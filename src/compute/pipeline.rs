use std::borrow::Cow;

use bevy::{
    ecs::system::SystemParam,
    prelude::*,
    render::{
        render_asset::RenderAssets,
        render_resource::{
            binding_types::{texture_2d, texture_storage_2d, uniform_buffer_sized},
            *,
        },
        renderer::{RenderContext, RenderDevice, RenderQueue},
        texture::GpuImage,
    },
    shader::ShaderCacheError,
};
use bytemuck::Zeroable;

use super::{CameraUniform, DiskConfigUniform, GeodesicImage, ObjectsUniform, SkyboxImage};
use crate::simulation::{
    BINARY_DISK_INNER_RS, SCHWARZSCHILD_RADIUS, kerr_horizon_radius, kerr_isco_radius,
};

// ── GPU-layout structs (repr C, bytemuck) ───────────────────────────────────

/// Matches the Camera uniform in geodesic.wgsl (std140, 112 bytes).
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
    debug_heatmap: u32,
    max_iter: u32,
    polarization_view: u32,
    frequency_ghz: f32,
    faraday_depth: f32,
    conversion_depth: f32,
    _pad7: f32,
}

/// Matches the Disk uniform in geodesic.wgsl (std140, 64 bytes).
#[repr(C)]
#[derive(Clone, Copy, PartialEq, bytemuck::Pod, bytemuck::Zeroable)]
struct GpuDiskUniform {
    r1: f32,     // inner emitting radius (r_g)
    r2: f32,     // outer radius (r_g)
    h_thin: f32, // H/R for thin disk component
    h_hot: f32,  // H/R for hot / thick inner component
    spin: f32,
    horizon_r: f32,
    isco_r: f32,
    r_trunc: f32,   // truncation or puff radius (r_g)
    tilt_deg: f32,  // outer disk tilt (degrees)
    r_bp: f32,      // Bardeen-Petterson alignment radius (r_g)
    twist_deg: f32, // twist per ln(r/r_bp) (degrees)
    model: u32,     // 0=ThinNT 1=TruncHot 2=Slim 3=Warped
    binary_enabled: u32,
    _pad0: f32,
    _pad1: f32,
    _pad2: f32,
}

/// Matches the Objects uniform in geodesic.wgsl.
/// std140 pads f32 array elements to 16 bytes → use [f32;4].
#[repr(C)]
#[derive(Clone, Copy, PartialEq, bytemuck::Pod, bytemuck::Zeroable)]
struct GpuObjectsUniform {
    num_objects: i32,
    _pad: [f32; 3],
    pos_radius: [[f32; 4]; 16],
    color: [[f32; 4]; 16],
    mass: [[f32; 4]; 16],
    spin: [[f32; 4]; 16],
}

// ── Pipeline resource ────────────────────────────────────────────────────────

#[derive(Resource)]
pub struct GeodesicPipeline {
    layout: BindGroupLayoutDescriptor,
    pipeline_id: CachedComputePipelineId,
    camera_buf: Buffer,
    disk_buf: Buffer,
    objects_buf: Buffer,
    /// Handles of textures currently bound in the active GeodesicBindGroup.
    /// `None` until the first bind group is successfully created.
    bound_geo_handle: Option<Handle<Image>>,
    bound_sky_handle: Option<Handle<Image>>,
    /// Last values written to the GPU buffers; skip write when unchanged.
    last_objects: Option<GpuObjectsUniform>,
    last_disk: Option<GpuDiskUniform>,
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
                // binding 1 – camera uniform (112 bytes)
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
        immediate_size: 0,
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
        bound_geo_handle: None,
        bound_sky_handle: None,
        last_objects: None,
        last_disk: None,
    });
}

/// Build a GPU disk uniform from runtime parameters.
fn build_disk_uniform(cfg: &DiskConfigUniform) -> GpuDiskUniform {
    let isco_r = kerr_isco_radius(cfg.spin);
    let horizon_r = kerr_horizon_radius(cfg.spin);
    let inner_r = if cfg.binary_enabled {
        (SCHWARZSCHILD_RADIUS * BINARY_DISK_INNER_RS).max(isco_r)
    } else {
        isco_r
    };
    GpuDiskUniform {
        r1: inner_r,
        r2: SCHWARZSCHILD_RADIUS * cfg.r_outer_rs,
        h_thin: cfg.h_thin,
        h_hot: cfg.h_hot,
        spin: cfg.spin,
        horizon_r,
        isco_r,
        r_trunc: SCHWARZSCHILD_RADIUS * cfg.r_trunc_rs,
        tilt_deg: cfg.tilt_deg,
        r_bp: SCHWARZSCHILD_RADIUS * cfg.r_bp_rs,
        twist_deg: cfg.twist_deg,
        model: cfg.model,
        binary_enabled: cfg.binary_enabled as u32,
        _pad0: 0.0,
        _pad1: 0.0,
        _pad2: 0.0,
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

// ── Bind group ───────────────────────────────────────────────────────────────

#[derive(Resource)]
pub struct GeodesicBindGroup(pub BindGroup);

#[derive(SystemParam)]
pub struct GeodesicSources<'w> {
    pipeline: Option<ResMut<'w, GeodesicPipeline>>,
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

pub fn prepare_bind_group(mut commands: Commands, sources: GeodesicSources, gpu: RenderGpu) {
    let (
        Some(mut pipeline),
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

    // Camera changes every still frame (jitter) — always write.
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
        debug_heatmap: camera_uniform.debug_heatmap,
        max_iter: camera_uniform.max_iter,
        polarization_view: camera_uniform.polarization_view,
        frequency_ghz: camera_uniform.frequency_ghz,
        faraday_depth: camera_uniform.faraday_depth,
        conversion_depth: camera_uniform.conversion_depth,
        _pad7: 0.0,
    };
    gpu.queue
        .write_buffer(&pipeline.camera_buf, 0, bytemuck::bytes_of(&gpu_cam));

    // Objects buffer — write only when data actually changed.
    let mut gpu_objs = GpuObjectsUniform::zeroed();
    gpu_objs.num_objects = objects_uniform.num_objects;
    gpu_objs.pos_radius = objects_uniform.pos_radius;
    gpu_objs.color = objects_uniform.color;
    gpu_objs.mass = objects_uniform.mass;
    gpu_objs.spin = objects_uniform.spin;
    if pipeline.last_objects != Some(gpu_objs) {
        gpu.queue
            .write_buffer(&pipeline.objects_buf, 0, bytemuck::bytes_of(&gpu_objs));
        pipeline.last_objects = Some(gpu_objs);
    }

    // Disk/Kerr buffer — write only when any disk parameter changed.
    let gpu_disk = build_disk_uniform(&disk_config);
    if pipeline.last_disk != Some(gpu_disk) {
        gpu.queue
            .write_buffer(&pipeline.disk_buf, 0, bytemuck::bytes_of(&gpu_disk));
        pipeline.last_disk = Some(gpu_disk);
    }

    // Bind group — recreate only when output texture or skybox handle changes.
    let geo_changed = pipeline.bound_geo_handle.as_ref() != Some(&geodesic_image.0);
    let sky_changed = pipeline.bound_sky_handle.as_ref() != Some(&skybox.0);
    if !geo_changed && !sky_changed {
        return;
    }

    let (Some(gpu_image), Some(skybox_gpu)) = (
        gpu.gpu_images.get(&geodesic_image.0),
        gpu.gpu_images.get(&skybox.0),
    ) else {
        return; // GPU textures not yet uploaded; retry next frame.
    };

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
    pipeline.bound_geo_handle = Some(geodesic_image.0.clone());
    pipeline.bound_sky_handle = Some(skybox.0.clone());
}

// ── Render graph node ────────────────────────────────────────────────────────

pub fn dispatch_geodesic(
    mut render_context: RenderContext,
    pipeline: Option<Res<GeodesicPipeline>>,
    group: Option<Res<GeodesicBindGroup>>,
    image: Option<Res<GeodesicImage>>,
    images: Res<RenderAssets<GpuImage>>,
    cache: Res<PipelineCache>,
) {
    let (Some(pipeline), Some(group), Some(image)) = (pipeline, group, image) else {
        return;
    };
    if let CachedPipelineState::Err(err) = cache.get_compute_pipeline_state(pipeline.pipeline_id)
        && !matches!(err, ShaderCacheError::ShaderNotLoaded(_))
    {
        panic!("geodesic shader error: {err}");
    }
    let (Some(compute), Some(image)) = (
        cache.get_compute_pipeline(pipeline.pipeline_id),
        images.get(&image.0),
    ) else {
        return;
    };
    let mut pass = render_context
        .command_encoder()
        .begin_compute_pass(&ComputePassDescriptor::default());
    pass.set_bind_group(0, &group.0, &[]);
    pass.set_pipeline(compute);
    pass.dispatch_workgroups(
        image.texture_descriptor.size.width.div_ceil(16),
        image.texture_descriptor.size.height.div_ceil(16),
        1,
    );
}

#[cfg(test)]
pub(super) fn check_relativity(device: &RenderDevice, queue: &RenderQueue) {
    let source = format!(
        "{}\n{}",
        include_str!("../../assets/shaders/geodesic.wgsl"),
        include_str!("../../tests/relativity.wgsl")
    );
    let shader = device.create_and_validate_shader_module(ShaderModuleDescriptor {
        label: Some("physics checks"),
        source: ShaderSource::Wgsl(source.into()),
    });
    let pipeline = device.create_compute_pipeline(&RawComputePipelineDescriptor {
        label: Some("physics checks"),
        layout: None,
        module: &shader,
        entry_point: Some("check_physics"),
        compilation_options: default(),
        cache: None,
    });
    let camera = GpuCameraUniform {
        right: [1.0, 0.0, 0.0],
        up: [0.0, 1.0, 0.0],
        forward: [0.0, 0.0, -1.0],
        ..GpuCameraUniform::zeroed()
    };
    let mut objects = GpuObjectsUniform::zeroed();
    objects.num_objects = 1;
    objects.mass[0][0] = 1.0;
    let camera_buf = device.create_buffer_with_data(&BufferInitDescriptor {
        label: None,
        contents: bytemuck::bytes_of(&camera),
        usage: BufferUsages::UNIFORM,
    });
    let objects_buf = device.create_buffer_with_data(&BufferInitDescriptor {
        label: None,
        contents: bytemuck::bytes_of(&objects),
        usage: BufferUsages::UNIFORM,
    });
    let uniform_group = device.create_bind_group(
        None,
        &pipeline.get_bind_group_layout(0).into(),
        &[
            BindGroupEntry {
                binding: 1,
                resource: camera_buf.as_entire_binding(),
            },
            BindGroupEntry {
                binding: 3,
                resource: objects_buf.as_entire_binding(),
            },
        ],
    );
    let results = device.create_buffer(&BufferDescriptor {
        label: None,
        size: 112,
        usage: BufferUsages::STORAGE | BufferUsages::COPY_SRC,
        mapped_at_creation: false,
    });
    let readback = device.create_buffer(&BufferDescriptor {
        label: None,
        size: 112,
        usage: BufferUsages::MAP_READ | BufferUsages::COPY_DST,
        mapped_at_creation: false,
    });
    let result_group = device.create_bind_group(
        None,
        &pipeline.get_bind_group_layout(1).into(),
        &BindGroupEntries::single(results.as_entire_binding()),
    );
    let mut encoder = device.create_command_encoder(&CommandEncoderDescriptor::default());
    {
        let mut pass = encoder.begin_compute_pass(&ComputePassDescriptor::default());
        pass.set_pipeline(&pipeline);
        pass.set_bind_group(0, &uniform_group, &[]);
        pass.set_bind_group(1, &result_group, &[]);
        pass.dispatch_workgroups(1, 1, 1);
    }
    encoder.copy_buffer_to_buffer(&results, 0, &readback, 0, 112);
    queue.submit([encoder.finish()]);
    let (sender, receiver) = std::sync::mpsc::channel();
    readback
        .slice(..)
        .map_async(MapMode::Read, move |result| sender.send(result).unwrap());
    device
        .poll(PollType::Wait {
            submission_index: None,
            timeout: Some(std::time::Duration::from_secs(30)),
        })
        .unwrap();
    receiver
        .recv_timeout(std::time::Duration::from_secs(30))
        .unwrap()
        .unwrap();
    let data = readback.slice(..).get_mapped_range();
    for (i, value) in bytemuck::cast_slice::<u8, f32>(&data)
        .iter()
        .take(20)
        .enumerate()
    {
        assert_eq!(
            *value,
            1.0,
            "WGSL physics check {i} failed (tests/relativity.wgsl); capture/escape diagnostics: {:?}",
            &bytemuck::cast_slice::<u8, f32>(&data)[20..]
        );
    }
}
