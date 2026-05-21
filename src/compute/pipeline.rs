use std::borrow::Cow;

use bevy::{
    ecs::system::SystemParam,
    prelude::*,
    render::{
        render_asset::RenderAssets,
        render_graph,
        render_resource::{
            binding_types::{texture_2d, texture_storage_2d, uniform_buffer_sized},
            *,
        },
        renderer::{RenderContext, RenderDevice, RenderQueue},
        texture::GpuImage,
    },
    shader::PipelineCacheError,
};
use bytemuck::Zeroable;

use super::{CameraUniform, DiskConfigUniform, GeodesicImage, ObjectsUniform, SkyboxImage};
use crate::simulation::{SAGA_RS, kerr_horizon_radius, kerr_isco_radius};

// ── GPU-layout structs (repr C, bytemuck) ───────────────────────────────────

/// Matches the Camera uniform in geodesic.wgsl (std140, 96 bytes).
#[repr(C)]
#[derive(Clone, Copy, bytemuck::Pod, bytemuck::Zeroable)]
struct GpuCameraUniform {
    pos: [f32; 3],
    _pad0: f32,
    right: [f32; 3],
    _pad1: f32,
    up: [f32; 3],
    _pad2: f32,
    forward: [f32; 3],
    _pad3: f32,
    tan_half_fov: f32,
    aspect: f32,
    moving: u32,
    jitter_x: f32,
    jitter_y: f32,
    _pad5: f32,
    _pad6: f32,
    _pad7: f32,
}

/// Matches the Disk uniform in geodesic.wgsl (std140, 32 bytes).
#[repr(C)]
#[derive(Clone, Copy, bytemuck::Pod, bytemuck::Zeroable)]
struct GpuDiskUniform {
    r1: f32,
    r2: f32,
    num: f32,
    thickness: f32,
    spin: f32,
    horizon_r: f32,
    isco_r: f32,
    _pad0: f32,
}

/// Matches the Objects uniform in geodesic.wgsl.
/// std140 pads f32 array elements to 16 bytes → use [f32;4].
#[repr(C)]
#[derive(Clone, Copy, bytemuck::Pod, bytemuck::Zeroable)]
struct GpuObjectsUniform {
    num_objects: i32,
    _pad: [f32; 3],
    pos_radius: [[f32; 4]; 16],
    color: [[f32; 4]; 16],
    mass: [[f32; 4]; 16],
}

// ── Pipeline resource ────────────────────────────────────────────────────────

#[derive(Resource)]
pub struct GeodesicPipeline {
    layout: BindGroupLayoutDescriptor,
    pipeline_id: CachedComputePipelineId,
    camera_buf: Buffer,
    disk_buf: Buffer,
    objects_buf: Buffer,
}

pub fn init_geodesic_pipeline(
    mut commands: Commands,
    device: Res<RenderDevice>,
    asset_server: Res<AssetServer>,
    pipeline_cache: Res<PipelineCache>,
) {
    let layout = BindGroupLayoutDescriptor::new(
        "geodesic_layout",
        &BindGroupLayoutEntries::sequential(
            ShaderStages::COMPUTE,
            (
                // binding 0 – output storage texture (write-only RGBA8)
                texture_storage_2d(TextureFormat::Rgba8Unorm, StorageTextureAccess::WriteOnly),
                // binding 1 – camera uniform (80 bytes)
                uniform_buffer_sized(false, Some(GpuCameraUniform::SIZE)),
                // binding 2 – disk/Kerr uniform
                uniform_buffer_sized(false, Some(GpuDiskUniform::SIZE)),
                // binding 3 – objects uniform
                uniform_buffer_sized(false, Some(GpuObjectsUniform::SIZE)),
                // binding 4 – skybox HDR (sampled via textureLoad, no filtering)
                texture_2d(TextureSampleType::Float { filterable: false }),
            ),
        ),
    );

    let camera_buf = device.create_buffer(&BufferDescriptor {
        label: Some("camera_buf"),
        size: GpuCameraUniform::SIZE.get(),
        usage: BufferUsages::UNIFORM | BufferUsages::COPY_DST,
        mapped_at_creation: false,
    });

    let disk_buf = device.create_buffer(&BufferDescriptor {
        label: Some("disk_buf"),
        size: GpuDiskUniform::SIZE.get(),
        usage: BufferUsages::UNIFORM | BufferUsages::COPY_DST,
        mapped_at_creation: false,
    });

    let objects_buf = device.create_buffer(&BufferDescriptor {
        label: Some("objects_buf"),
        size: GpuObjectsUniform::SIZE.get(),
        usage: BufferUsages::UNIFORM | BufferUsages::COPY_DST,
        mapped_at_creation: false,
    });

    let pipeline_id = pipeline_cache.queue_compute_pipeline(ComputePipelineDescriptor {
        label: Some(Cow::Borrowed("geodesic_pipeline")),
        layout: vec![layout.clone()],
        push_constant_ranges: vec![],
        shader: asset_server.load("shaders/geodesic.wgsl"),
        shader_defs: vec![],
        entry_point: Some(Cow::Borrowed("main")),
        zero_initialize_workgroup_memory: false,
    });

    commands.insert_resource(GeodesicPipeline {
        layout,
        pipeline_id,
        camera_buf,
        disk_buf,
        objects_buf,
    });
}

/// Build a GPU disk uniform from runtime parameters.
fn build_disk_uniform(spin: f32, r_outer_rs: f32) -> GpuDiskUniform {
    let isco_r = kerr_isco_radius(spin);
    GpuDiskUniform {
        r1: isco_r,
        r2: SAGA_RS * r_outer_rs,
        num: 2.0,
        thickness: 1e9,
        spin,
        horizon_r: kerr_horizon_radius(spin),
        isco_r,
        _pad0: 0.0,
    }
}

// ── Bind group size helpers ──────────────────────────────────────────────────

trait GpuSize {
    const SIZE: std::num::NonZeroU64;
}

impl GpuSize for GpuCameraUniform {
    const SIZE: std::num::NonZeroU64 =
        std::num::NonZeroU64::new(std::mem::size_of::<Self>() as u64).unwrap();
}

impl GpuSize for GpuDiskUniform {
    const SIZE: std::num::NonZeroU64 =
        std::num::NonZeroU64::new(std::mem::size_of::<Self>() as u64).unwrap();
}

impl GpuSize for GpuObjectsUniform {
    const SIZE: std::num::NonZeroU64 =
        std::num::NonZeroU64::new(std::mem::size_of::<Self>() as u64).unwrap();
}

// ── Bind group (recreated every frame) ──────────────────────────────────────

#[derive(Resource)]
pub struct GeodesicBindGroup(pub BindGroup);

#[derive(SystemParam)]
pub struct GeodesicSources<'w> {
    pipeline: Option<Res<'w, GeodesicPipeline>>,
    geodesic_image: Option<Res<'w, GeodesicImage>>,
    camera_uniform: Option<Res<'w, CameraUniform>>,
    objects_uniform: Option<Res<'w, ObjectsUniform>>,
    disk_config: Option<Res<'w, DiskConfigUniform>>,
    skybox: Option<Res<'w, SkyboxImage>>,
}

#[derive(SystemParam)]
pub struct RenderGpu<'w> {
    gpu_images: Res<'w, RenderAssets<GpuImage>>,
    device: Res<'w, RenderDevice>,
    queue: Res<'w, RenderQueue>,
    pipeline_cache: Res<'w, PipelineCache>,
}

pub fn prepare_bind_group(
    mut commands: Commands,
    sources: GeodesicSources,
    gpu: RenderGpu,
) {
    let (
        Some(pipeline),
        Some(geodesic_image),
        Some(camera_uniform),
        Some(objects_uniform),
        Some(disk_config),
        Some(skybox),
    ) = (
        sources.pipeline,
        sources.geodesic_image,
        sources.camera_uniform,
        sources.objects_uniform,
        sources.disk_config,
        sources.skybox,
    )
    else {
        return;
    };
    let (Some(gpu_image), Some(skybox_gpu)) =
        (gpu.gpu_images.get(&geodesic_image.0), gpu.gpu_images.get(&skybox.0))
    else {
        return;
    };

    // Write camera data
    let gpu_cam = GpuCameraUniform {
        pos: camera_uniform.pos.into(),
        _pad0: 0.0,
        right: camera_uniform.right.into(),
        _pad1: 0.0,
        up: camera_uniform.up.into(),
        _pad2: 0.0,
        forward: camera_uniform.forward.into(),
        _pad3: 0.0,
        tan_half_fov: camera_uniform.tan_half_fov,
        aspect: camera_uniform.aspect,
        moving: camera_uniform.moving,
        jitter_x: camera_uniform.jitter_x,
        jitter_y: camera_uniform.jitter_y,
        _pad5: 0.0,
        _pad6: 0.0,
        _pad7: 0.0,
    };
    gpu.queue
        .write_buffer(&pipeline.camera_buf, 0, bytemuck::bytes_of(&gpu_cam));

    // Write objects data
    let mut gpu_objs = GpuObjectsUniform::zeroed();
    gpu_objs.num_objects = objects_uniform.num_objects;
    gpu_objs.pos_radius = objects_uniform.pos_radius;
    gpu_objs.color = objects_uniform.color;
    gpu_objs.mass = objects_uniform.mass;
    gpu.queue
        .write_buffer(&pipeline.objects_buf, 0, bytemuck::bytes_of(&gpu_objs));

    // Write disk/Kerr data (dynamic: spin and outer radius adjustable at runtime).
    let gpu_disk = build_disk_uniform(disk_config.spin, disk_config.r_outer_rs);
    gpu.queue
        .write_buffer(&pipeline.disk_buf, 0, bytemuck::bytes_of(&gpu_disk));

    let layout = gpu.pipeline_cache.get_bind_group_layout(&pipeline.layout);
    let bind_group = gpu.device.create_bind_group(
        None,
        &layout,
        &BindGroupEntries::sequential((
            &gpu_image.texture_view,
            pipeline.camera_buf.as_entire_binding(),
            pipeline.disk_buf.as_entire_binding(),
            pipeline.objects_buf.as_entire_binding(),
            &skybox_gpu.texture_view,
        )),
    );

    commands.insert_resource(GeodesicBindGroup(bind_group));
}

// ── Render graph node ────────────────────────────────────────────────────────

enum NodeState {
    Loading,
    Ready,
}

pub struct GeodesicNode {
    state: NodeState,
}

impl Default for GeodesicNode {
    fn default() -> Self {
        Self {
            state: NodeState::Loading,
        }
    }
}

impl render_graph::Node for GeodesicNode {
    fn update(&mut self, world: &mut World) {
        let Some(pipeline) = world.get_resource::<GeodesicPipeline>() else {
            return;
        };
        let cache = world.resource::<PipelineCache>();

        if let NodeState::Loading = self.state {
            match cache.get_compute_pipeline_state(pipeline.pipeline_id) {
                CachedPipelineState::Ok(_) => self.state = NodeState::Ready,
                CachedPipelineState::Err(PipelineCacheError::ShaderNotLoaded(_)) => {}
                CachedPipelineState::Err(err) => panic!("geodesic shader error: {err}"),
                _ => {}
            }
        }
    }

    fn run(
        &self,
        _graph: &mut render_graph::RenderGraphContext,
        render_context: &mut RenderContext,
        world: &World,
    ) -> Result<(), render_graph::NodeRunError> {
        if matches!(self.state, NodeState::Loading) {
            return Ok(());
        }

        let (Some(bind_group), Some(pipeline_res)) = (
            world.get_resource::<GeodesicBindGroup>(),
            world.get_resource::<GeodesicPipeline>(),
        ) else {
            return Ok(());
        };

        let cache = world.resource::<PipelineCache>();
        let Some(pipeline) = cache.get_compute_pipeline(pipeline_res.pipeline_id) else {
            return Ok(());
        };

        let (dispatch_x, dispatch_y) = world
            .get_resource::<GeodesicImage>()
            .and_then(|gi| world.resource::<RenderAssets<GpuImage>>().get(&gi.0))
            .map(|img| (img.size.width.div_ceil(16), img.size.height.div_ceil(16)))
            .unwrap_or((1, 1));

        let mut pass = render_context
            .command_encoder()
            .begin_compute_pass(&ComputePassDescriptor::default());

        pass.set_bind_group(0, &bind_group.0, &[]);
        pass.set_pipeline(pipeline);
        pass.dispatch_workgroups(dispatch_x, dispatch_y, 1);

        Ok(())
    }
}
