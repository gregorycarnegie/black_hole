use bevy::{
    ecs::system::SystemParam,
    prelude::*,
    render::{render_asset::RenderAssets, texture::GpuImage},
};
use bytemuck::Zeroable;
use cudarc::driver::{CudaSlice, LaunchConfig, PushKernelArg};

use super::{
    CameraUniform, DiskConfigUniform, GeodesicImage, ObjectsUniform, SkyboxData, cuda::shared_cuda,
};
use crate::simulation::{
    BINARY_DISK_INNER_RS, SCHWARZSCHILD_RADIUS, kerr_horizon_radius, kerr_isco_radius,
};

// ── GPU-layout structs (repr C, bytemuck) ───────────────────────────────────

/// Matches `GpuCameraUniform` in `tools/cuda/kernels.rs` (112 bytes).
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

/// Matches `GpuDiskUniform` in `tools/cuda/kernels.rs` (64 bytes).
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

/// Matches `GpuObjectsUniform` in `tools/cuda/kernels.rs`.
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
    camera_buf: CudaSlice<u8>,
    disk_buf: CudaSlice<u8>,
    objects_buf: CudaSlice<u8>,
    pub(super) geodesic_buf: CudaSlice<f32>,
    skybox_buf: CudaSlice<u8>,
    pub(super) width: u32,
    pub(super) height: u32,
    sky_width: u32,
    sky_height: u32,
    bound_geo_handle: Option<Handle<Image>>,
    bound_sky_handle: Option<Handle<Image>>,
    last_objects: Option<GpuObjectsUniform>,
    last_disk: Option<GpuDiskUniform>,
}

pub fn init_geodesic_pipeline(mut commands: Commands) {
    let cuda = shared_cuda();
    let camera_buf = cuda.alloc_zeros::<u8>(std::mem::size_of::<GpuCameraUniform>());
    let disk_buf = cuda.alloc_zeros::<u8>(std::mem::size_of::<GpuDiskUniform>());
    let objects_buf = cuda.alloc_zeros::<u8>(std::mem::size_of::<GpuObjectsUniform>());
    let geodesic_buf = cuda.alloc_zeros::<f32>(4);
    let skybox_buf = cuda.alloc_zeros::<u8>(16);

    commands.insert_resource(GeodesicPipeline {
        camera_buf,
        disk_buf,
        objects_buf,
        geodesic_buf,
        skybox_buf,
        width: 0,
        height: 0,
        sky_width: 0,
        sky_height: 0,
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

#[derive(SystemParam)]
pub struct GeodesicSources<'w> {
    pipeline: Option<ResMut<'w, GeodesicPipeline>>,
    geodesic_image: Option<Res<'w, GeodesicImage>>,
    camera_uniform: Option<Res<'w, CameraUniform>>,
    objects_uniform: Option<Res<'w, ObjectsUniform>>,
    disk_config: Option<Res<'w, DiskConfigUniform>>,
    skybox_data: Option<Res<'w, SkyboxData>>,
}

pub fn prepare_bind_group(sources: GeodesicSources, gpu_images: Res<RenderAssets<GpuImage>>) {
    let (
        Some(mut pipeline),
        Some(geodesic_image),
        Some(camera_uniform),
        Some(objects_uniform),
        Some(disk_config),
        Some(skybox_data),
    ) = (
        sources.pipeline,
        sources.geodesic_image,
        sources.camera_uniform,
        sources.objects_uniform,
        sources.disk_config,
        sources.skybox_data,
    )
    else {
        return;
    };

    let cuda = shared_cuda();

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
    cuda.memcpy_htod(bytemuck::bytes_of(&gpu_cam), &mut pipeline.camera_buf);

    // Objects buffer — write only when data actually changed.
    let mut gpu_objs = GpuObjectsUniform::zeroed();
    gpu_objs.num_objects = objects_uniform.num_objects;
    gpu_objs.pos_radius = objects_uniform.pos_radius;
    gpu_objs.color = objects_uniform.color;
    gpu_objs.mass = objects_uniform.mass;
    gpu_objs.spin = objects_uniform.spin;
    if pipeline.last_objects != Some(gpu_objs) {
        cuda.memcpy_htod(bytemuck::bytes_of(&gpu_objs), &mut pipeline.objects_buf);
        pipeline.last_objects = Some(gpu_objs);
    }

    // Disk/Kerr buffer — write only when any disk parameter changed.
    let gpu_disk = build_disk_uniform(&disk_config);
    if pipeline.last_disk != Some(gpu_disk) {
        cuda.memcpy_htod(bytemuck::bytes_of(&gpu_disk), &mut pipeline.disk_buf);
        pipeline.last_disk = Some(gpu_disk);
    }

    // Output geodesic buffer — reallocate when handle or resolution changes.
    if let Some(gpu_image) = gpu_images.get(&geodesic_image.0) {
        let w = gpu_image.texture_descriptor.size.width;
        let h = gpu_image.texture_descriptor.size.height;
        if pipeline.bound_geo_handle.as_ref() != Some(&geodesic_image.0)
            || pipeline.width != w
            || pipeline.height != h
        {
            pipeline.geodesic_buf = cuda.alloc_zeros::<f32>((w as usize) * (h as usize) * 4);
            pipeline.width = w;
            pipeline.height = h;
            pipeline.bound_geo_handle = Some(geodesic_image.0.clone());
        }
    }

    // Skybox buffer — upload when active skybox data is ready and changed.
    if pipeline.bound_sky_handle != skybox_data.handle
        && skybox_data.width > 0
        && skybox_data.height > 0
        && !skybox_data.bytes.is_empty()
    {
        pipeline.skybox_buf = cuda.clone_htod(&skybox_data.bytes);
        pipeline.sky_width = skybox_data.width;
        pipeline.sky_height = skybox_data.height;
        pipeline.bound_sky_handle = skybox_data.handle.clone();
    }
}

// ── Render graph node ────────────────────────────────────────────────────────

pub fn dispatch_geodesic(pipeline: Option<ResMut<GeodesicPipeline>>) {
    let Some(mut pipeline) = pipeline else {
        return;
    };
    if pipeline.width == 0
        || pipeline.height == 0
        || pipeline.sky_width == 0
        || pipeline.sky_height == 0
    {
        return;
    }

    let cuda = shared_cuda();
    cuda.bind_to_thread();

    let GeodesicPipeline {
        ref camera_buf,
        ref disk_buf,
        ref objects_buf,
        ref mut geodesic_buf,
        ref skybox_buf,
        width,
        height,
        sky_width,
        sky_height,
        ..
    } = *pipeline;

    let cfg = LaunchConfig {
        grid_dim: (width.div_ceil(16), height.div_ceil(16), 1),
        block_dim: (16, 16, 1),
        shared_mem_bytes: 0,
    };
    let mut builder = cuda.stream.launch_builder(&cuda.geodesic);
    builder.arg(geodesic_buf);
    builder.arg(camera_buf);
    builder.arg(disk_buf);
    builder.arg(objects_buf);
    builder.arg(skybox_buf);
    builder.arg(&width);
    builder.arg(&height);
    builder.arg(&sky_width);
    builder.arg(&sky_height);
    unsafe {
        builder
            .launch(cfg)
            .expect("CUDA bh_geodesic kernel launch failed");
    }
}

#[cfg(test)]
#[test]
#[ignore = "requires a CUDA GPU; run with -- --ignored --nocapture"]
fn binary_render_stops_stagnating_rays() {
    let cuda = shared_cuda();
    let cam = crate::camera::OrbitalCamera::default();
    let camera = GpuCameraUniform {
        pos: cam.position().into(),
        right: cam.right().into(),
        up: cam.up().into(),
        forward: cam.forward().into(),
        tan_half_fov: cam.tan_half_fov(),
        aspect: 4.0 / 3.0,
        debug_heatmap: 1,
        max_iter: cam.max_iter,
        frequency_ghz: cam.frequency_ghz,
        faraday_depth: cam.faraday_depth,
        conversion_depth: cam.conversion_depth,
        ..GpuCameraUniform::zeroed()
    };
    let scene = crate::simulation::SimObjects::default();
    let mut objects = GpuObjectsUniform::zeroed();
    objects.num_objects = scene.0.len() as i32;
    for (i, object) in scene.0.iter().enumerate() {
        objects.pos_radius[i] = object.position.extend(object.radius).into();
        objects.color[i] = object.color.into();
        objects.mass[i][0] = object.mass;
        objects.spin[i] = object.spin.extend(0.0).into();
    }
    let disk = build_disk_uniform(&DiskConfigUniform::default());
    let d_camera = cuda.clone_htod(bytemuck::bytes_of(&camera));
    let d_disk = cuda.clone_htod(bytemuck::bytes_of(&disk));
    let d_objects = cuda.clone_htod(bytemuck::bytes_of(&objects));
    let d_skybox = cuda.clone_htod(&[1.0_f32; 4]);
    let (width, height) = (64u32, 48u32);
    let mut output = cuda.alloc_zeros::<f32>((width * height * 4) as usize);
    cuda.stream.synchronize().unwrap();
    let start = std::time::Instant::now();
    let mut builder = cuda.stream.launch_builder(&cuda.geodesic);
    builder.arg(&mut output);
    builder.arg(&d_camera);
    builder.arg(&d_disk);
    builder.arg(&d_objects);
    builder.arg(&d_skybox);
    builder.arg(&width);
    builder.arg(&height);
    builder.arg(&1u32);
    builder.arg(&1u32);
    unsafe {
        builder
            .launch(LaunchConfig {
                grid_dim: (width.div_ceil(16), height.div_ceil(16), 1),
                block_dim: (16, 16, 1),
                shared_mem_bytes: 0,
            })
            .unwrap();
    }
    drop(builder);
    let pixels = cuda.clone_dtoh(&output);
    assert!(pixels.iter().all(|value| value.is_finite()));
    // The heatmap's RGB sum is 3 * iterations / max_iter.
    let max_iterations = pixels
        .as_chunks::<4>()
        .0
        .iter()
        .map(|pixel| (pixel[0] + pixel[1] + pixel[2]) * camera.max_iter as f32 / 3.0)
        .fold(0.0_f32, f32::max);
    eprintln!(
        "binary render: {:?}, max {max_iterations:.0} iterations",
        start.elapsed()
    );
    assert!(max_iterations > 0.0 && max_iterations < 2_000.0);
}

#[cfg(test)]
pub(super) fn check_relativity() {
    let cuda = shared_cuda();
    cuda.bind_to_thread();

    let camera = GpuCameraUniform {
        right: [1.0, 0.0, 0.0],
        up: [0.0, 1.0, 0.0],
        forward: [0.0, 0.0, -1.0],
        ..GpuCameraUniform::zeroed()
    };
    let mut objects = GpuObjectsUniform::zeroed();
    objects.num_objects = 1;
    objects.mass[0][0] = 1.0;

    let d_cam = cuda.clone_htod(bytemuck::bytes_of(&camera));
    let d_obj = cuda.clone_htod(bytemuck::bytes_of(&objects));
    let mut d_results = cuda.alloc_zeros::<f32>(124);

    let cfg = LaunchConfig {
        grid_dim: (1, 1, 1),
        block_dim: (64, 1, 1),
        shared_mem_bytes: 0,
    };
    let mut builder = cuda.stream.launch_builder(&cuda.check_relativity);
    builder.arg(&d_cam);
    builder.arg(&d_obj);
    builder.arg(&mut d_results);
    unsafe {
        builder
            .launch(cfg)
            .expect("CUDA bh_check_relativity kernel launch failed");
    }

    let data = cuda.clone_dtoh(&d_results);
    for (i, value) in data.iter().take(24).enumerate() {
        assert_eq!(
            *value,
            1.0,
            "CUDA physics check {i} failed (tools/cuda/kernels.rs); capture/escape diagnostics: {:?}",
            &data[24..40]
        );
    }
    for (i, value) in data[100..106].iter().enumerate() {
        assert_eq!(
            *value,
            1.0,
            "adaptive CUDA physics check {i} failed; statuses: {:?}; trajectory: {:?}",
            &data[100..106],
            &data[112..124]
        );
    }
    assert_eq!(
        data[106], 1.0,
        "intensity fast path changed the disk RGB, energy or opacity"
    );
    super::verification::check_convergence(&data);
}
