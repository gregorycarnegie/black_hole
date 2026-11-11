use bevy::{
    ecs::system::SystemParam,
    prelude::*,
    render::{
        render_asset::RenderAssets,
        render_resource::{Extent3d, TexelCopyBufferLayout},
        renderer::{RenderContext, RenderQueue},
        texture::GpuImage,
    },
};
use cudarc::driver::{CudaSlice, LaunchConfig, PushKernelArg};

use super::{
    AccumA, AccumB, DisplayImage, FrameParity, RenderFrameCount, cuda::shared_cuda,
    pipeline::GeodesicPipeline,
};

// ── Pipeline resource ────────────────────────────────────────────────────────

#[derive(Resource)]
pub struct AccumulatePipeline {
    accum_a: CudaSlice<f32>,
    accum_b: CudaSlice<f32>,
    display_buf: CudaSlice<u32>,
    host_rgba: Vec<u8>,
    width: u32,
    height: u32,
    frame_count: u32,
    bound_a: Option<Handle<Image>>,
    bound_b: Option<Handle<Image>>,
    bound_disp: Option<Handle<Image>>,
}

pub fn init_accumulate_pipeline(mut commands: Commands) {
    let cuda = shared_cuda();
    commands.insert_resource(AccumulatePipeline {
        accum_a: cuda.alloc_zeros::<f32>(4),
        accum_b: cuda.alloc_zeros::<f32>(4),
        display_buf: cuda.alloc_zeros::<u32>(1),
        host_rgba: Vec::new(),
        width: 0,
        height: 0,
        frame_count: 0,
        bound_a: None,
        bound_b: None,
        bound_disp: None,
    });
}

#[derive(SystemParam)]
pub struct AccumulateSources<'w> {
    pipeline: Option<ResMut<'w, AccumulatePipeline>>,
    accum_a: Option<Res<'w, AccumA>>,
    accum_b: Option<Res<'w, AccumB>>,
    display: Option<Res<'w, DisplayImage>>,
    frame_count: Option<Res<'w, RenderFrameCount>>,
}

pub fn prepare_accumulate_bind_group(
    sources: AccumulateSources,
    gpu_images: Res<RenderAssets<GpuImage>>,
) {
    let (Some(mut pipeline), Some(a), Some(b), Some(disp), Some(fc)) = (
        sources.pipeline,
        sources.accum_a,
        sources.accum_b,
        sources.display,
        sources.frame_count,
    ) else {
        return;
    };

    pipeline.frame_count = fc.0;

    let Some(disp_gpu) = gpu_images.get(&disp.0) else {
        return;
    };
    let w = disp_gpu.texture_descriptor.size.width;
    let h = disp_gpu.texture_descriptor.size.height;

    let needs_rebuild = pipeline.bound_a.as_ref() != Some(&a.0)
        || pipeline.bound_b.as_ref() != Some(&b.0)
        || pipeline.bound_disp.as_ref() != Some(&disp.0)
        || pipeline.width != w
        || pipeline.height != h;

    if !needs_rebuild {
        return;
    }

    let cuda = shared_cuda();
    let pixels = (w as usize) * (h as usize);
    pipeline.accum_a = cuda.alloc_zeros::<f32>(pixels * 4);
    pipeline.accum_b = cuda.alloc_zeros::<f32>(pixels * 4);
    pipeline.display_buf = cuda.alloc_zeros::<u32>(pixels);
    pipeline.host_rgba.resize(pixels * 4, 0);
    pipeline.width = w;
    pipeline.height = h;
    pipeline.bound_a = Some(a.0.clone());
    pipeline.bound_b = Some(b.0.clone());
    pipeline.bound_disp = Some(disp.0.clone());
}

// ── Render graph node ────────────────────────────────────────────────────────

pub fn dispatch_accumulate(
    mut render_context: RenderContext,
    pipeline: Option<ResMut<AccumulatePipeline>>,
    geo_pipeline: Option<Res<GeodesicPipeline>>,
    parity: Option<Res<FrameParity>>,
    display: Option<Res<DisplayImage>>,
    images: Res<RenderAssets<GpuImage>>,
    queue: Res<RenderQueue>,
) {
    let (Some(mut pipeline), Some(geo_pipeline), Some(parity), Some(display)) =
        (pipeline, geo_pipeline, parity, display)
    else {
        return;
    };
    let Some(disp_gpu) = images.get(&display.0) else {
        return;
    };
    if pipeline.width == 0
        || pipeline.height == 0
        || geo_pipeline.width != pipeline.width
        || geo_pipeline.height != pipeline.height
    {
        return;
    }

    let cuda = shared_cuda();
    cuda.bind_to_thread();

    let AccumulatePipeline {
        ref mut accum_a,
        ref mut accum_b,
        ref mut display_buf,
        ref mut host_rgba,
        width,
        height,
        frame_count,
        ..
    } = *pipeline;

    let (prev_accum, curr_accum) = if parity.0 {
        (&*accum_b, accum_a)
    } else {
        (&*accum_a, accum_b)
    };

    let cfg = LaunchConfig {
        grid_dim: (width.div_ceil(16), height.div_ceil(16), 1),
        block_dim: (16, 16, 1),
        shared_mem_bytes: 0,
    };
    let mut builder = cuda.stream.launch_builder(&cuda.accumulate);
    builder.arg(&mut *display_buf);
    builder.arg(&geo_pipeline.geodesic_buf);
    builder.arg(prev_accum);
    builder.arg(curr_accum);
    builder.arg(&width);
    builder.arg(&height);
    builder.arg(&frame_count);
    unsafe {
        builder
            .launch(cfg)
            .expect("CUDA bh_accumulate kernel launch failed");
    }
    drop(builder);

    cuda.memcpy_dtoh(display_buf, bytemuck::cast_slice_mut::<u8, u32>(host_rgba));

    let _ = render_context.command_encoder();
    queue.write_texture(
        disp_gpu.texture.as_image_copy(),
        host_rgba,
        TexelCopyBufferLayout {
            offset: 0,
            bytes_per_row: Some(width * 4),
            rows_per_image: Some(height),
        },
        Extent3d {
            width,
            height,
            depth_or_array_layers: 1,
        },
    );
}
