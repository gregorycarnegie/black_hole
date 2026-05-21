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

use super::{AccumA, AccumB, DisplayImage, FrameParity, GeodesicImage, RenderFrameCount};

// ── Blend uniform (matches BlendParams in accumulate.wgsl) ──────────────────

#[repr(C)]
#[derive(Clone, Copy, bytemuck::Pod, bytemuck::Zeroable)]
struct BlendUniform {
    frame_count: u32,
    _pad: [u32; 3],
}

const BLEND_UNIFORM_SIZE: u64 = std::mem::size_of::<BlendUniform>() as u64;

// ── Pipeline resource ────────────────────────────────────────────────────────

#[derive(Resource)]
pub struct AccumulatePipeline {
    layout: BindGroupLayoutDescriptor,
    pipeline_id: CachedComputePipelineId,
    blend_buf: Buffer,
    /// Handles of textures currently bound in the active AccumulateBindGroups.
    /// `None` until the first bind groups are successfully created.
    bound_geo: Option<Handle<Image>>,
    bound_a: Option<Handle<Image>>,
    bound_b: Option<Handle<Image>>,
    bound_disp: Option<Handle<Image>>,
}

pub fn init_accumulate_pipeline(
    mut commands: Commands,
    device: Res<RenderDevice>,
    asset_server: Res<AssetServer>,
    pipeline_cache: Res<PipelineCache>,
) {
    let blend_size = std::num::NonZeroU64::new(BLEND_UNIFORM_SIZE).unwrap();

    let layout = BindGroupLayoutDescriptor::new(
        "accumulate_layout",
        &BindGroupLayoutEntries::sequential(
            ShaderStages::COMPUTE,
            (
                // 0 – display output (rgba8unorm, write)
                texture_storage_2d(TextureFormat::Rgba8Unorm, StorageTextureAccess::WriteOnly),
                // 1 – new_frame (read via textureLoad)
                texture_2d(TextureSampleType::Float { filterable: false }),
                // 2 – prev_accum (read via textureLoad)
                texture_2d(TextureSampleType::Float { filterable: false }),
                // 3 – curr_accum (rgba32float, write)
                texture_storage_2d(TextureFormat::Rgba32Float, StorageTextureAccess::WriteOnly),
                // 4 – blend params uniform
                uniform_buffer_sized(false, Some(blend_size)),
            ),
        ),
    );

    let blend_buf = device.create_buffer(&BufferDescriptor {
        label: Some("blend_buf"),
        size: BLEND_UNIFORM_SIZE,
        usage: BufferUsages::UNIFORM | BufferUsages::COPY_DST,
        mapped_at_creation: false,
    });

    let pipeline_id = pipeline_cache.queue_compute_pipeline(ComputePipelineDescriptor {
        label: Some(Cow::Borrowed("accumulate_pipeline")),
        layout: vec![layout.clone()],
        push_constant_ranges: vec![],
        shader: asset_server.load("shaders/accumulate.wgsl"),
        shader_defs: vec![],
        entry_point: Some(Cow::Borrowed("main")),
        zero_initialize_workgroup_memory: false,
    });

    commands.insert_resource(AccumulatePipeline {
        layout,
        pipeline_id,
        blend_buf,
        bound_geo: None,
        bound_a: None,
        bound_b: None,
        bound_disp: None,
    });
}

// ── Bind groups (ping-pong) ──────────────────────────────────────────────────

/// Two bind groups for ping-pong accumulation.
/// - `a_prev`: reads AccumA as history, writes into AccumB
/// - `b_prev`: reads AccumB as history, writes into AccumA
#[derive(Resource)]
pub struct AccumulateBindGroups {
    pub a_prev: BindGroup,
    pub b_prev: BindGroup,
}

#[derive(SystemParam)]
pub struct AccumulateSources<'w> {
    pipeline: Option<ResMut<'w, AccumulatePipeline>>,
    geodesic: Option<Res<'w, GeodesicImage>>,
    accum_a: Option<Res<'w, AccumA>>,
    accum_b: Option<Res<'w, AccumB>>,
    display: Option<Res<'w, DisplayImage>>,
    frame_count: Option<Res<'w, RenderFrameCount>>,
}

#[derive(SystemParam)]
pub struct RenderGpu<'w> {
    gpu_images: Res<'w, RenderAssets<GpuImage>>,
    device: Res<'w, RenderDevice>,
    queue: Res<'w, RenderQueue>,
    pipeline_cache: Res<'w, PipelineCache>,
}

pub fn prepare_accumulate_bind_group(
    mut commands: Commands,
    sources: AccumulateSources,
    gpu: RenderGpu,
) {
    let (Some(mut pipeline), Some(geo), Some(a), Some(b), Some(disp), Some(fc)) = (
        sources.pipeline,
        sources.geodesic,
        sources.accum_a,
        sources.accum_b,
        sources.display,
        sources.frame_count,
    ) else {
        return;
    };

    // Blend uniform changes every still frame — always write.
    let blend = BlendUniform {
        frame_count: fc.0,
        _pad: [0; 3],
    };
    gpu.queue
        .write_buffer(&pipeline.blend_buf, 0, bytemuck::bytes_of(&blend));

    // Bind groups — recreate only when any texture handle changes.
    let needs_rebuild = pipeline.bound_geo.as_ref() != Some(&geo.0)
        || pipeline.bound_a.as_ref() != Some(&a.0)
        || pipeline.bound_b.as_ref() != Some(&b.0)
        || pipeline.bound_disp.as_ref() != Some(&disp.0);

    if !needs_rebuild {
        return;
    }

    let (Some(geo_gpu), Some(a_gpu), Some(b_gpu), Some(disp_gpu)) = (
        gpu.gpu_images.get(&geo.0),
        gpu.gpu_images.get(&a.0),
        gpu.gpu_images.get(&b.0),
        gpu.gpu_images.get(&disp.0),
    ) else {
        return; // GPU textures not yet uploaded; retry next frame.
    };

    let layout = gpu.pipeline_cache.get_bind_group_layout(&pipeline.layout);

    // a_prev: prev = AccumA, curr = AccumB
    let a_prev = gpu.device.create_bind_group(
        None,
        &layout,
        &BindGroupEntries::sequential((
            &disp_gpu.texture_view,
            &geo_gpu.texture_view,
            &a_gpu.texture_view,
            &b_gpu.texture_view,
            pipeline.blend_buf.as_entire_binding(),
        )),
    );

    // b_prev: prev = AccumB, curr = AccumA
    let b_prev = gpu.device.create_bind_group(
        None,
        &layout,
        &BindGroupEntries::sequential((
            &disp_gpu.texture_view,
            &geo_gpu.texture_view,
            &b_gpu.texture_view,
            &a_gpu.texture_view,
            pipeline.blend_buf.as_entire_binding(),
        )),
    );

    commands.insert_resource(AccumulateBindGroups { a_prev, b_prev });
    pipeline.bound_geo = Some(geo.0.clone());
    pipeline.bound_a = Some(a.0.clone());
    pipeline.bound_b = Some(b.0.clone());
    pipeline.bound_disp = Some(disp.0.clone());
}

// ── Render graph node ────────────────────────────────────────────────────────

enum NodeState {
    Loading,
    Ready,
}

pub struct AccumulateNode {
    state: NodeState,
}

impl Default for AccumulateNode {
    fn default() -> Self {
        Self {
            state: NodeState::Loading,
        }
    }
}

impl render_graph::Node for AccumulateNode {
    fn update(&mut self, world: &mut World) {
        let Some(pipeline) = world.get_resource::<AccumulatePipeline>() else {
            return;
        };
        let cache = world.resource::<PipelineCache>();
        if let NodeState::Loading = self.state {
            match cache.get_compute_pipeline_state(pipeline.pipeline_id) {
                CachedPipelineState::Ok(_) => self.state = NodeState::Ready,
                CachedPipelineState::Err(PipelineCacheError::ShaderNotLoaded(_)) => {}
                CachedPipelineState::Err(e) => panic!("accumulate shader error: {e}"),
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

        let (Some(groups), Some(pipeline_res), Some(parity), Some(display)) = (
            world.get_resource::<AccumulateBindGroups>(),
            world.get_resource::<AccumulatePipeline>(),
            world.get_resource::<FrameParity>(),
            world.get_resource::<DisplayImage>(),
        ) else {
            return Ok(());
        };

        let cache = world.resource::<PipelineCache>();
        let Some(pipeline) = cache.get_compute_pipeline(pipeline_res.pipeline_id) else {
            return Ok(());
        };

        let gpu_images = world.resource::<RenderAssets<GpuImage>>();
        let Some(disp_gpu) = gpu_images.get(&display.0) else {
            return Ok(());
        };

        let (dispatch_x, dispatch_y) = (
            disp_gpu.size.width.div_ceil(16),
            disp_gpu.size.height.div_ceil(16),
        );

        // frame_count even → parity=true → prev=B, curr=A → use b_prev
        // frame_count odd  → parity=false → prev=A, curr=B → use a_prev
        let bind_group = if parity.0 {
            &groups.b_prev
        } else {
            &groups.a_prev
        };

        let mut pass = render_context
            .command_encoder()
            .begin_compute_pass(&ComputePassDescriptor::default());

        pass.set_bind_group(0, bind_group, &[]);
        pass.set_pipeline(pipeline);
        pass.dispatch_workgroups(dispatch_x, dispatch_y, 1);

        Ok(())
    }
}
