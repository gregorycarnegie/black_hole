use bevy::{
    ecs::system::SystemParam,
    prelude::*,
    render::{render_asset::RenderAssets, texture::GpuImage},
};
use bytemuck::Zeroable;
use cudarc::driver::{CudaSlice, LaunchConfig, PushKernelArg};

use super::{
    CameraUniform, DiskConfigUniform, GeodesicImage, ObjectsUniform, OtherSkyboxData,
    RayExperiments, SkyboxData,
    cuda::shared_cuda,
    profile::{RAY_FIELDS, RayProfile, write_ray_profile},
};
use crate::{
    simulation::{
        BINARY_DISK_INNER_RS, SCHWARZSCHILD_RADIUS, kerr_horizon_radius, kerr_isco_radius,
    },
    swarm::{GpuSwarmBody, SLICES, Swarm, swarm_belt, swarm_bodies, swarm_bvh},
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
    wormhole_radius: f32,
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
    other_skybox_buf: CudaSlice<u8>,
    pub(super) width: u32,
    pub(super) height: u32,
    sky_width: u32,
    sky_height: u32,
    other_sky_width: u32,
    other_sky_height: u32,
    bound_geo_handle: Option<Handle<Image>>,
    bound_sky_handle: Option<Handle<Image>>,
    bound_other_sky_handle: Option<Handle<Image>>,
    last_objects: Option<GpuObjectsUniform>,
    last_disk: Option<GpuDiskUniform>,
    swarm: SwarmDevice,
    /// RT-core swarm queries: None until RTX is first switched on, then the started
    /// renderer, or None inside if OptiX could not start.
    #[cfg(feature = "optix")]
    optix: Option<Option<super::optix::OptixRender>>,
    /// This frame's bodies when the swarm renders through OptiX; empty otherwise.
    #[cfg(feature = "optix")]
    optix_bodies: Vec<GpuSwarmBody>,
}

impl GeodesicPipeline {
    /// Whether the swarm renders through OptiX this frame, starting it on first use.
    fn use_optix(&mut self, rtx: bool) -> bool {
        #[cfg(feature = "optix")]
        return rtx
            && self
                .optix
                .get_or_insert_with(|| {
                    super::optix::OptixRender::new()
                        .inspect_err(|e| warn!("OptiX unavailable, using the software BVH: {e}"))
                        .ok()
                })
                .is_some();
        #[cfg(not(feature = "optix"))]
        {
            let _ = rtx;
            false
        }
    }
}

/// Swarm bodies and their per-slice BVHs on the device.
pub(super) struct SwarmDevice {
    bodies: CudaSlice<u8>,
    nodes: CudaSlice<u8>,
    items: CudaSlice<u8>,
    roots: CudaSlice<u8>,
    count: u32,
    /// 0 selects the brute-force path.
    slices: u32,
    /// From `swarm_belt`.
    belt: (f32, f32, f32),
}

impl SwarmDevice {
    fn new() -> Self {
        let cuda = shared_cuda();
        Self {
            bodies: cuda.alloc_zeros::<u8>(16),
            nodes: cuda.alloc_zeros::<u8>(16),
            items: cuda.alloc_zeros::<u8>(16),
            roots: cuda.alloc_zeros::<u8>(16),
            count: 0,
            slices: 0,
            belt: (0.0, 0.0, 0.0),
        }
    }

    /// Uploads `bodies`, with their BVHs unless `brute_force`.
    fn upload(&mut self, bodies: &[GpuSwarmBody], brute_force: bool) {
        fn write(buffer: &mut CudaSlice<u8>, bytes: &[u8]) {
            let cuda = shared_cuda();
            if buffer.len() == bytes.len() {
                cuda.memcpy_htod(bytes, buffer);
            } else {
                *buffer = cuda.clone_htod(bytes);
            }
        }
        write(&mut self.bodies, bytemuck::cast_slice(bodies));
        self.count = bodies.len() as u32;
        self.slices = 0;
        self.belt = swarm_belt(bodies);
        if !brute_force && !bodies.is_empty() {
            let bvh = swarm_bvh(bodies);
            write(&mut self.nodes, bytemuck::cast_slice(&bvh.nodes));
            write(&mut self.items, bytemuck::cast_slice(&bvh.items));
            write(&mut self.roots, bytemuck::cast_slice(&bvh.roots));
            self.slices = SLICES;
        }
    }

    fn launch(
        &self,
        output: &mut CudaSlice<f32>,
        args: (
            &CudaSlice<u8>,
            &CudaSlice<u8>,
            &CudaSlice<u8>,
            &CudaSlice<u8>,
        ),
        size: (u32, u32, u32, u32),
        experiments: u32,
        cfg: LaunchConfig,
    ) {
        let cuda = shared_cuda();
        let mut builder = cuda.stream.launch_builder(&cuda.geodesic_swarm);
        builder.arg(output);
        builder.arg(args.0);
        builder.arg(args.1);
        builder.arg(args.2);
        builder.arg(args.3);
        builder.arg(&size.0);
        builder.arg(&size.1);
        builder.arg(&size.2);
        builder.arg(&size.3);
        builder.arg(&self.bodies);
        builder.arg(&self.count);
        builder.arg(&self.nodes);
        builder.arg(&self.items);
        builder.arg(&self.roots);
        builder.arg(&self.slices);
        builder.arg(&self.belt.0);
        builder.arg(&self.belt.1);
        builder.arg(&self.belt.2);
        builder.arg(&experiments);
        unsafe {
            builder
                .launch(cfg)
                .expect("CUDA bh_geodesic_swarm kernel launch failed");
        }
    }
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
        other_skybox_buf: cuda.alloc_zeros::<u8>(16),
        width: 0,
        height: 0,
        sky_width: 0,
        sky_height: 0,
        other_sky_width: 0,
        other_sky_height: 0,
        bound_geo_handle: None,
        bound_sky_handle: None,
        bound_other_sky_handle: None,
        last_objects: None,
        last_disk: None,
        swarm: SwarmDevice::new(),
        // Started on demand: OptiX reserves a 512 MB queue.
        #[cfg(feature = "optix")]
        optix: None,
        #[cfg(feature = "optix")]
        optix_bodies: Vec::new(),
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
    other_skybox_data: Option<Res<'w, OtherSkyboxData>>,
    swarm: Option<Res<'w, Swarm>>,
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
        wormhole_radius: camera_uniform.wormhole_radius,
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

    // Swarm phases move every frame, so upload them whenever bodies are shown.
    pipeline.swarm.count = 0;
    #[cfg(feature = "optix")]
    pipeline.optix_bodies.clear();
    if let Some(swarm) = sources.swarm.filter(|swarm| swarm.count > 0) {
        let bodies = swarm_bodies(swarm.count, disk_config.spin, swarm.time);
        // OptiX builds its own motion GAS, so skip the software BVH then.
        let optix = pipeline.use_optix(swarm.rtx);
        pipeline.swarm.upload(&bodies, optix);
        #[cfg(feature = "optix")]
        if optix {
            pipeline.optix_bodies = bodies;
        }
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
    if let Some(data) = sources.other_skybox_data {
        let data = &data.0;
        if pipeline.bound_other_sky_handle != data.handle
            && data.width > 0
            && data.height > 0
            && !data.bytes.is_empty()
        {
            pipeline.other_skybox_buf = cuda.clone_htod(&data.bytes);
            pipeline.other_sky_width = data.width;
            pipeline.other_sky_height = data.height;
            pipeline.bound_other_sky_handle = data.handle.clone();
        }
    }
}

// ── Render graph node ────────────────────────────────────────────────────────

#[cfg(test)]
#[test]
#[ignore = "requires a CUDA GPU; checks transmission in the production image kernel"]
fn wormhole_image_selects_the_proved_critical_impact_sky() {
    let cuda = shared_cuda();
    let orbit = crate::camera::OrbitalCamera {
        radius: 12.0,
        ..default()
    };
    let camera = GpuCameraUniform {
        pos: orbit.position().into(),
        right: orbit.right().into(),
        up: orbit.up().into(),
        forward: orbit.forward().into(),
        aspect: 4.0 / 3.0,
        tan_half_fov: orbit.tan_half_fov(),
        wormhole_radius: black_hole::ellis::THROAT_RADIUS,
        max_iter: 10_000,
        ..GpuCameraUniform::zeroed()
    };
    let cam = cuda.clone_htod(bytemuck::bytes_of(&camera));
    let near = cuda.clone_htod(&[[4.0_f32, 0.0, 0.0, 1.0]]);
    let far = cuda.clone_htod(&[[0.0_f32, 0.0, 4.0, 1.0]]);
    let (width, height) = (128_u32, 96_u32);
    let mut output = cuda.alloc_zeros::<f32>((width * height * 4) as usize);
    let mut launch = cuda.stream.launch_builder(&cuda.wormhole);
    launch.arg(&mut output);
    launch.arg(&cam);
    launch.arg(&near);
    launch.arg(&far);
    launch.arg(&width);
    launch.arg(&height);
    launch.arg(&1_u32);
    launch.arg(&1_u32);
    launch.arg(&1_u32);
    launch.arg(&1_u32);
    launch.arg(&0.0_f32);
    launch.arg(&0_u32);
    unsafe {
        launch
            .launch(LaunchConfig {
                grid_dim: (8, 6, 1),
                block_dim: (16, 16, 1),
                shared_mem_bytes: 0,
            })
            .unwrap();
    }
    let pixels = cuda.clone_dtoh(&output);
    let normal = orbit.position().normalize();
    for y in 0..height {
        for x in 0..width {
            let u =
                (2.0 * (x as f32 + 0.5) / width as f32 - 1.0) * camera.aspect * camera.tan_half_fov;
            let v = (1.0 - 2.0 * (y as f32 + 0.5) / height as f32) * camera.tan_half_fov;
            let sight = (u * orbit.right() - v * orbit.up() + orbit.forward()).normalize();
            let transverse = sight - sight.dot(normal) * normal;
            let impact = (12.0_f32 * 12.0 + 16.0).sqrt() * transverse.length();
            let color = &pixels[((y * width + x) * 4) as usize..][..4];
            assert!(color.iter().all(|c| c.is_finite()));
            if (impact - 4.0).abs() > 4e-4 {
                if impact < 4.0 {
                    assert!(
                        color[2] > 0.9 && color[0] == 0.0,
                        "transmitted pixel ({x},{y})={color:?}"
                    );
                } else {
                    assert!(
                        color[0] > 0.9 && color[2] == 0.0,
                        "reflected pixel ({x},{y})={color:?}"
                    );
                }
            }
        }
    }
}

pub fn dispatch_geodesic(
    pipeline: Option<ResMut<GeodesicPipeline>>,
    camera: Option<Res<CameraUniform>>,
    view: Option<Res<crate::bridge::BridgeView>>,
    experiments: Option<Res<RayExperiments>>,
) {
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

    let wormhole = camera.is_some_and(|camera| camera.wormhole_radius > 0.0);
    let single_source = pipeline
        .last_objects
        .as_ref()
        .is_some_and(|objects| objects.num_objects == 1);
    #[cfg(feature = "optix")]
    if !wormhole && !pipeline.optix_bodies.is_empty() {
        let experiments = active_experiments(single_source, experiments.as_deref());
        let cfg = ray_launch_config(pipeline.width, pipeline.height, single_source);
        render_swarm_with_optix(&mut pipeline, experiments, cfg);
        return;
    }
    let GeodesicPipeline {
        ref camera_buf,
        ref disk_buf,
        ref objects_buf,
        ref mut geodesic_buf,
        ref skybox_buf,
        ref other_skybox_buf,
        ref swarm,
        width,
        height,
        sky_width,
        sky_height,
        other_sky_width,
        other_sky_height,
        ..
    } = *pipeline;

    let cfg = ray_launch_config(width, height, !wormhole && single_source);
    if wormhole {
        // Reuse the near sky until the second asynchronous asset has loaded.
        let (far_sky, far_w, far_h) = if other_sky_width > 0 && other_sky_height > 0 {
            (other_skybox_buf, other_sky_width, other_sky_height)
        } else {
            (skybox_buf, sky_width, sky_height)
        };
        let mut builder = cuda.stream.launch_builder(&cuda.wormhole);
        builder.arg(geodesic_buf);
        builder.arg(camera_buf);
        builder.arg(skybox_buf);
        builder.arg(far_sky);
        builder.arg(&width);
        builder.arg(&height);
        builder.arg(&sky_width);
        builder.arg(&sky_height);
        builder.arg(&far_w);
        builder.arg(&far_h);
        let (matter_time, matter_enabled) = view.map_or((0.0_f32, 0_u32), |view| {
            (view.matter_time as f32, u32::from(view.matter_enabled))
        });
        builder.arg(&matter_time);
        builder.arg(&matter_enabled);
        unsafe {
            builder
                .launch(cfg)
                .expect("CUDA bh_wormhole kernel launch failed");
        }
        return;
    }
    let enabled = active_experiments(single_source, experiments.as_deref());
    if swarm.count > 0 {
        swarm.launch(
            geodesic_buf,
            (camera_buf, disk_buf, objects_buf, skybox_buf),
            (width, height, sky_width, sky_height),
            enabled,
            cfg,
        );
        return;
    }
    let kernel = match enabled {
        0 => &cuda.geodesic,
        1 => &cuda.geodesic_full_trace,
        _ => &cuda.geodesic_experiments,
    };
    let mut builder = cuda.stream.launch_builder(kernel);
    builder.arg(geodesic_buf);
    builder.arg(camera_buf);
    builder.arg(disk_buf);
    builder.arg(objects_buf);
    builder.arg(skybox_buf);
    builder.arg(&width);
    builder.arg(&height);
    builder.arg(&sky_width);
    builder.arg(&sky_height);
    if enabled > 1 {
        builder.arg(&enabled);
    }
    unsafe {
        builder
            .launch(cfg)
            .expect("CUDA bh_geodesic kernel launch failed");
    }
}

#[cfg(feature = "optix")]
fn render_swarm_with_optix(pipeline: &mut GeodesicPipeline, experiments: u32, cfg: LaunchConfig) {
    use cudarc::driver::DevicePtr;
    let stream = &shared_cuda().stream;
    let p = pipeline;
    let (out_image, _out) = p.geodesic_buf.device_ptr(stream);
    let (cam, _cam) = p.camera_buf.device_ptr(stream);
    let (disk, _disk) = p.disk_buf.device_ptr(stream);
    let (objects, _objects) = p.objects_buf.device_ptr(stream);
    let (skybox, _skybox) = p.skybox_buf.device_ptr(stream);
    let inputs = super::optix::RenderInputs {
        out_image,
        cam,
        disk,
        objects,
        skybox,
        size: (p.width, p.height, p.sky_width, p.sky_height),
        experiments,
        cfg,
    };
    if let Some(Some(optix)) = p.optix.as_mut() {
        optix.render(&inputs, &p.optix_bodies);
    }
}

fn active_experiments(single_source: bool, experiments: Option<&RayExperiments>) -> u32 {
    let Some(experiments) = experiments else {
        return 0;
    };
    // Far field assumes a single source. Early capture is on by default and its kernel
    // guard rejects other scenes; bit 0 asks for the full trace.
    let single = if single_source {
        u32::from(experiments.full_trace) | (u32::from(experiments.far_field) << 1)
    } else {
        0
    };
    single | (u32::from(experiments.rk4) << 2)
}

fn ray_launch_config(width: u32, height: u32, single_source_kerr: bool) -> LaunchConfig {
    // Keep each warp on one scanline for the single-source Kerr kernel.
    let (block_width, block_height) = if single_source_kerr {
        (32, 4)
    } else {
        (16, 16)
    };
    LaunchConfig {
        grid_dim: (
            width.div_ceil(block_width),
            height.div_ceil(block_height),
            1,
        ),
        block_dim: (block_width, block_height, 1),
        shared_mem_bytes: 0,
    }
}

pub(super) fn capture_ray_profile(
    request: Res<RayProfile>,
    pipeline: Res<GeodesicPipeline>,
    experiments: Option<Res<RayExperiments>>,
) {
    if !request.requested() || pipeline.width == 0 || pipeline.sky_width == 0 {
        return;
    }
    let cuda = shared_cuda();
    cuda.bind_to_thread();
    let pixels = pipeline.width as usize * pipeline.height as usize;
    let mut image = cuda.alloc_zeros::<f32>(pixels * 4);
    let mut diagnostics = cuda.alloc_zeros::<u32>(pixels * RAY_FIELDS);
    let kernel = cuda
        .module
        .load_function("bh_geodesic_diagnostics")
        .expect("load ray diagnostic kernel");
    let single_source = pipeline
        .last_objects
        .as_ref()
        .is_some_and(|objects| objects.num_objects == 1);
    let cfg = ray_launch_config(pipeline.width, pipeline.height, single_source);
    let enabled = active_experiments(single_source, experiments.as_deref());
    let mut launch = cuda.stream.launch_builder(&kernel);
    launch.arg(&mut image);
    launch.arg(&pipeline.camera_buf);
    launch.arg(&pipeline.disk_buf);
    launch.arg(&pipeline.objects_buf);
    launch.arg(&pipeline.skybox_buf);
    launch.arg(&pipeline.width);
    launch.arg(&pipeline.height);
    launch.arg(&pipeline.sky_width);
    launch.arg(&pipeline.sky_height);
    launch.arg(&mut diagnostics);
    launch.arg(&enabled);
    unsafe { launch.launch(cfg).expect("launch ray diagnostic kernel") };
    let data = cuda.clone_dtoh(&diagnostics);
    write_ray_profile(pipeline.width, pipeline.height, &data, enabled)
        .expect("write ray diagnostic CSV");

    let reference = cuda.clone_dtoh(&pipeline.geodesic_buf);
    let diagnostic_image = cuda.clone_dtoh(&image);
    let largest_delta = reference
        .iter()
        .zip(diagnostic_image)
        .map(|(normal, diagnostic)| (normal - diagnostic).abs())
        .fold(0.0_f32, f32::max);
    println!("Diagnostic image maximum channel difference {largest_delta:.3e}");
    request.complete();
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

#[cfg(test)]
mod swarm_gpu {
    use super::*;
    use crate::{
        simulation::{KERR_SPIN, default_binary_spins, scene_objects},
        swarm::GpuSwarmBody,
    };

    const SPIN: f32 = KERR_SPIN;
    const WIDTH: u32 = 400;
    const HEIGHT: u32 = 300;

    struct Scene {
        camera: CudaSlice<u8>,
        disk: CudaSlice<u8>,
        objects: CudaSlice<u8>,
        sky: CudaSlice<u8>,
    }

    /// The default single-hole view.
    fn single_hole() -> Scene {
        let cuda = shared_cuda();
        let cam = crate::camera::OrbitalCamera::default();
        let camera = GpuCameraUniform {
            pos: cam.position().into(),
            right: cam.right().into(),
            up: cam.up().into(),
            forward: cam.forward().into(),
            tan_half_fov: cam.tan_half_fov(),
            aspect: 4.0 / 3.0,
            max_iter: cam.max_iter,
            frequency_ghz: cam.frequency_ghz,
            faraday_depth: cam.faraday_depth,
            conversion_depth: cam.conversion_depth,
            ..GpuCameraUniform::zeroed()
        };
        let mut objects = GpuObjectsUniform::zeroed();
        let scene = scene_objects(SPIN, false, false, 0.0, default_binary_spins());
        objects.num_objects = scene.len() as i32;
        for (i, object) in scene.iter().enumerate() {
            objects.pos_radius[i] = object.position.extend(object.radius).into();
            objects.color[i] = object.color.into();
            objects.mass[i][0] = object.mass;
            objects.spin[i] = object.spin.extend(0.0).into();
        }
        let disk = build_disk_uniform(&DiskConfigUniform {
            spin: SPIN,
            binary_enabled: false,
            ..DiskConfigUniform::default()
        });
        Scene {
            camera: cuda.clone_htod(bytemuck::bytes_of(&camera)),
            disk: cuda.clone_htod(bytemuck::bytes_of(&disk)),
            objects: cuda.clone_htod(bytemuck::bytes_of(&objects)),
            // A 2×1 sky, so the escape direction shows up in the image.
            sky: cuda.clone_htod(bytemuck::cast_slice(&[0.2_f32, 0.3, 0.9, 1.0, 0.9, 0.5, 0.2, 1.0])),
        }
    }

    /// Renders with `bh_geodesic`, or with `bh_geodesic_swarm` when bodies are given.
    fn render(scene: &Scene, swarm: Option<&SwarmDevice>) -> (Vec<f32>, f64) {
        render_with(scene, swarm, 0)
    }

    /// As `render`, with the experiment bits; without bodies, nonzero bits select
    /// `bh_geodesic_experiments`.
    fn render_with(
        scene: &Scene,
        swarm: Option<&SwarmDevice>,
        experiments: u32,
    ) -> (Vec<f32>, f64) {
        let cuda = shared_cuda();
        let mut output = cuda.alloc_zeros::<f32>((WIDTH * HEIGHT * 4) as usize);
        let cfg = ray_launch_config(WIDTH, HEIGHT, true);
        let args = (&scene.camera, &scene.disk, &scene.objects, &scene.sky);
        cuda.stream.synchronize().unwrap();
        let start = std::time::Instant::now();
        if let Some(swarm) = swarm {
            swarm.launch(&mut output, args, (WIDTH, HEIGHT, 2, 1), experiments, cfg);
        } else {
            let kernel = if experiments == 0 {
                &cuda.geodesic
            } else {
                &cuda.geodesic_experiments
            };
            let mut builder = cuda.stream.launch_builder(kernel);
            builder.arg(&mut output);
            builder.arg(args.0);
            builder.arg(args.1);
            builder.arg(args.2);
            builder.arg(args.3);
            builder.arg(&WIDTH);
            builder.arg(&HEIGHT);
            builder.arg(&2u32);
            builder.arg(&1u32);
            if experiments != 0 {
                builder.arg(&experiments);
            }
            unsafe { builder.launch(cfg).unwrap() };
        }
        cuda.stream.synchronize().unwrap();
        let elapsed = start.elapsed().as_secs_f64() * 1000.0;
        (cuda.clone_dtoh(&output), elapsed)
    }

    fn device(bodies: &[GpuSwarmBody], brute_force: bool) -> SwarmDevice {
        let mut device = SwarmDevice::new();
        device.upload(bodies, brute_force);
        device
    }

    fn upload(bodies: &[GpuSwarmBody]) -> CudaSlice<u8> {
        shared_cuda().clone_htod(bytemuck::cast_slice(bodies))
    }

    #[test]
    #[ignore = "requires a CUDA GPU"]
    fn an_empty_swarm_renders_the_ordinary_image() {
        let scene = single_hole();
        let (ordinary, _) = render(&scene, None);
        let (swarm, _) = render(&scene, Some(&device(&[], true)));
        assert!(
            ordinary
                .iter()
                .map(|v| v.to_bits())
                .eq(swarm.iter().map(|v| v.to_bits()))
        );
    }

    #[test]
    #[ignore = "requires a CUDA GPU"]
    fn swarm_hits_match_exact_circular_orbits() {
        let cuda = shared_cuda();
        let bodies = swarm_bodies(4096, SPIN, 1234.5);
        let d_bodies = upload(&bodies);
        // Deterministic segments: half start next to a body, half anywhere in the belt.
        let mut seed = 0x2545_f491_u64;
        let mut uniform = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            (seed >> 11) as f64 / (1u64 << 53) as f64
        };
        let mut cases = Vec::new();
        for i in 0..4000 {
            let t0 = -400.0 * uniform();
            let start: [f64; 3] = if i % 2 == 0 {
                let c = bodies[(uniform() * 4096.0) as usize].center(t0);
                std::array::from_fn(|k| c[k] + 1.2 * (uniform() - 0.5))
            } else {
                [
                    90.0 * (uniform() - 0.5),
                    16.0 * (uniform() - 0.5),
                    90.0 * (uniform() - 0.5),
                ]
            };
            let dir: [f64; 3] = std::array::from_fn(|_| uniform() - 0.5);
            let norm = dir.iter().map(|v| v * v).sum::<f64>().sqrt();
            let length = 0.5 + 5.5 * uniform();
            // Light moves backward in time at unit speed in the flat limit.
            let end: [f64; 3] = std::array::from_fn(|k| start[k] + length * dir[k] / norm);
            cases.push((start, end, t0, t0 - length));
        }
        let packed: Vec<[f32; 4]> = cases
            .iter()
            .flat_map(|(s, e, t0, t1)| {
                [
                    [s[0] as f32, s[1] as f32, s[2] as f32, *t0 as f32],
                    [e[0] as f32, e[1] as f32, e[2] as f32, *t1 as f32],
                ]
            })
            .collect();
        let d_cases = cuda.clone_htod(&packed);
        let count = cases.len() as u32;
        let mut d_results = cuda.alloc_zeros::<f32>(cases.len() * 4);
        let function = cuda.module.load_function("bh_test_swarm_segment").unwrap();
        let mut builder = cuda.stream.launch_builder(&function);
        builder.arg(&d_cases);
        builder.arg(&d_bodies);
        builder.arg(&4096u32);
        builder.arg(&mut d_results);
        builder.arg(&count);
        unsafe { builder.launch(LaunchConfig::for_num_elems(count)).unwrap() };
        drop(builder);
        let results = cuda.clone_dtoh(&d_results);

        let (mut hits, mut misses, mut ambiguous, mut wrong) = (0, 0, 0, Vec::new());
        for (case, gpu) in cases.iter().zip(results.as_chunks::<4>().0) {
            let (start, end, t0, t1) = *case;
            let gpu_hit = gpu[3] > 0.0;
            // Exact motion, sampled finely enough that the minimum is within 2e-3.
            let mut certain_hit = false;
            let mut near = false;
            for body in &bodies {
                let c = body.center(t0);
                let mid = (0..3)
                    .map(|k| (0.5 * (start[k] + end[k]) - c[k]).powi(2))
                    .sum::<f64>()
                    .sqrt();
                if mid > 12.0 {
                    continue;
                }
                let radius = f64::from(body.axis_b[3]);
                let turn = f64::from(body.orbit[1]) * (t1 - t0);
                let pad = 0.125 * f64::from(body.axis_a[3]) * turn * turn;
                let gap = (0..=4096)
                    .map(|j| {
                        let s = j as f64 / 4096.0;
                        let c = body.center(t0 + s * (t1 - t0));
                        (0..3)
                            .map(|k| (start[k] + s * (end[k] - start[k]) - c[k]).powi(2))
                            .sum::<f64>()
                            .sqrt()
                            - radius
                    })
                    .fold(f64::INFINITY, f64::min);
                certain_hit |= gap < -0.01;
                near |= (-0.01..=pad + 0.01).contains(&gap);
            }
            if certain_hit {
                hits += 1;
                if !gpu_hit {
                    wrong.push(("missed", start, t0));
                }
            } else if near {
                ambiguous += 1;
            } else {
                misses += 1;
                if gpu_hit {
                    wrong.push(("false hit", start, t0));
                }
            }
        }
        println!(
            "{hits} hits, {misses} misses, {ambiguous} within the padding; {} wrong",
            wrong.len()
        );
        assert!(hits > 300 && misses > 500, "too few decisive cases");
        assert!(wrong.is_empty(), "{:?}", &wrong[..wrong.len().min(5)]);
    }

    /// Renders through OptiX with RT-core swarm queries; returns the image, the
    /// host GAS build time and the launch time.
    #[cfg(feature = "optix")]
    fn render_optix(
        optix: &mut crate::compute::optix::OptixRender,
        scene: &Scene,
        bodies: &[GpuSwarmBody],
        experiments: u32,
    ) -> (Vec<f32>, f64, crate::compute::optix::RenderStats) {
        use cudarc::driver::DevicePtr;
        let cuda = shared_cuda();
        let output = cuda.alloc_zeros::<f32>((WIDTH * HEIGHT * 4) as usize);
        let stream = &cuda.stream;
        cuda.stream.synchronize().unwrap();
        let start = std::time::Instant::now();
        let stats = {
            let (out_image, _a) = output.device_ptr(stream);
            let (cam, _b) = scene.camera.device_ptr(stream);
            let (disk, _c) = scene.disk.device_ptr(stream);
            let (objects, _d) = scene.objects.device_ptr(stream);
            let (skybox, _e) = scene.sky.device_ptr(stream);
            optix.render(
                &crate::compute::optix::RenderInputs {
                    out_image,
                    cam,
                    disk,
                    objects,
                    skybox,
                    size: (WIDTH, HEIGHT, 2, 1),
                    experiments,
                    cfg: ray_launch_config(WIDTH, HEIGHT, true),
                },
                bodies,
            )
        };
        let elapsed = start.elapsed().as_secs_f64() * 1000.0;
        (cuda.clone_dtoh(&output), elapsed, stats)
    }

    /// RT cores must pick exactly the hits brute force picks, in the full renderer.
    #[cfg(feature = "optix")]
    #[test]
    #[ignore = "requires an NVIDIA RTX driver and OPTIX_ROOT; run with --release -- --ignored --nocapture"]
    fn optix_renders_the_brute_force_image() {
        let scene = single_hole();
        let mut optix = crate::compute::optix::OptixRender::new().unwrap();
        render(&scene, None);
        let mut plain: Vec<f64> = (0..5).map(|_| render(&scene, None).1).collect();
        plain.sort_by(f64::total_cmp);
        println!("without a swarm: {:.1} ms", plain[2]);
        // The app only takes the OptiX path with bodies to trace.
        for count in crate::swarm::SWARM_COUNTS.into_iter().skip(1).chain([16384]) {
            let bodies = swarm_bodies(count.max(1), SPIN, 1000.0);
            let bodies = &bodies[..count as usize];
            let bvh = device(bodies, false);
            render(&scene, Some(&bvh));
            let mut bvh_times: Vec<f64> = (0..5).map(|_| render(&scene, Some(&bvh)).1).collect();
            bvh_times.sort_by(f64::total_cmp);
            // The first frame sizes the queue.
            render_optix(&mut optix, &scene, bodies, 0);
            let mut runs: Vec<(f64, f64, u32)> = (0..5)
                .map(|_| {
                    let (_, total, stats) = render_optix(&mut optix, &scene, bodies, 0);
                    (total, stats.build_ms, stats.queued)
                })
                .collect();
            runs.sort_by(|a, b| a.0.total_cmp(&b.0));
            let (image, _, _) = render_optix(&mut optix, &scene, bodies, 0);
            let differing = if count <= 1024 {
                let (brute, _) = render(&scene, Some(&device(bodies, true)));
                brute
                    .iter()
                    .zip(&image)
                    .filter(|(a, b)| a.to_bits() != b.to_bits())
                    .count()
            } else {
                0
            };
            println!(
                "{count:>6} bodies: BVH {:7.1} ms, OptiX {:7.1} ms (of which host GAS build {:.1} ms, {} steps queued); {differing} channels differ from brute force",
                bvh_times[2], runs[2].0, runs[2].1, runs[2].2
            );
            assert_eq!(differing, 0);
        }
    }

    /// The BVH must pick exactly the hits brute force picks.
    #[test]
    #[ignore = "requires a CUDA GPU"]
    fn the_bvh_renders_the_brute_force_image() {
        let scene = single_hole();
        let bodies = swarm_bodies(1024, SPIN, 1000.0);
        let (brute, _) = render(&scene, Some(&device(&bodies, true)));
        let (bvh, _) = render(&scene, Some(&device(&bodies, false)));
        let differing = brute
            .iter()
            .zip(&bvh)
            .filter(|(a, b)| a.to_bits() != b.to_bits())
            .count();
        assert_eq!(differing, 0, "{differing} channels differ");
    }

    /// Early capture (checklist P0.3) must not change swarm images: bodies orbit
    /// outside the capture radius. Brute force, the BVH and, with `--features optix`,
    /// OptiX against the full trace (bit 1).
    #[test]
    #[ignore = "requires a CUDA GPU"]
    fn swarm_early_capture_matches_the_full_trace() {
        let scene = single_hole();
        #[cfg(feature = "optix")]
        let mut optix = crate::compute::optix::OptixRender::new().unwrap();
        let same = |a: &[f32], b: &[f32]| a.iter().zip(b).all(|(x, y)| x.to_bits() == y.to_bits());
        for count in [256, 1024, 4096] {
            let bodies = swarm_bodies(count, SPIN, 1000.0);
            for brute_force in [true, false] {
                let swarm = device(&bodies, brute_force);
                let early = render_with(&scene, Some(&swarm), 0).0;
                let full = render_with(&scene, Some(&swarm), 1).0;
                assert!(same(&early, &full), "{count} bodies, brute force {brute_force}");
            }
            #[cfg(feature = "optix")]
            {
                render_optix(&mut optix, &scene, &bodies, 0);
                let early = render_optix(&mut optix, &scene, &bodies, 0).0;
                let full = render_optix(&mut optix, &scene, &bodies, 1).0;
                assert!(same(&early, &full), "{count} bodies, OptiX");
            }
        }
    }

    /// The swarm with the legacy RK4 controller (bit 2) and the default Dormand–Prince
    /// one, BVH and, with `--features optix`, OptiX; alternating launches, medians of
    /// five. The accelerated images must still match brute force under DP45.
    #[test]
    #[ignore = "requires a CUDA GPU; benchmark, run with --release -- --ignored --nocapture"]
    fn swarm_dp45_timing() {
        let scene = single_hole();
        #[cfg(feature = "optix")]
        let mut optix = crate::compute::optix::OptixRender::new().unwrap();
        let median = |mut v: Vec<f64>| {
            v.sort_by(f64::total_cmp);
            v[v.len() / 2]
        };
        for count in crate::swarm::SWARM_COUNTS.into_iter().chain([16384]) {
            let bodies = swarm_bodies(count, SPIN, 1000.0);
            let bvh = (count > 0).then(|| device(&bodies, false));
            let mut times = [Vec::new(), Vec::new()];
            for sample in 0..6 {
                for (variant, experiments) in [4, 0].into_iter().enumerate() {
                    let ms = render_with(&scene, bvh.as_ref(), experiments).1;
                    if sample > 0 {
                        times[variant].push(ms);
                    }
                }
            }
            let [rk4, dp45] = times.map(median);
            #[cfg_attr(not(feature = "optix"), allow(unused_mut))]
            let mut row = format!("{count:>6} bodies: BVH rk4 {rk4:6.1} ms, dp45 {dp45:6.1} ms");
            if (1..=1024).contains(&count) {
                let brute = render_with(&scene, Some(&device(&bodies, true)), 0).0;
                let fast = render_with(&scene, bvh.as_ref(), 0).0;
                assert!(brute.iter().zip(&fast).all(|(a, b)| a.to_bits() == b.to_bits()));
            }
            #[cfg(feature = "optix")]
            if count > 0 {
                let mut times = [Vec::new(), Vec::new()];
                for sample in 0..6 {
                    for (variant, experiments) in [4, 0].into_iter().enumerate() {
                        let ms = render_optix(&mut optix, &scene, &bodies, experiments).1;
                        if sample > 0 {
                            times[variant].push(ms);
                        }
                    }
                }
                let [rk4, dp45] = times.map(median);
                row += &format!("; OptiX rk4 {rk4:6.1} ms, dp45 {dp45:6.1} ms");
                if count <= 1024 {
                    let brute = render_with(&scene, Some(&device(&bodies, true)), 0).0;
                    let image = render_optix(&mut optix, &scene, &bodies, 0).0;
                    assert!(brute.iter().zip(&image).all(|(a, b)| a.to_bits() == b.to_bits()));
                }
            }
            println!("{row}");
        }
    }

    /// Brute force against the space-time BVH, including the host build and upload.
    #[test]
    #[ignore = "requires a CUDA GPU; benchmark, run with --release -- --ignored --nocapture"]
    fn swarm_bvh_against_brute_force() {
        let scene = single_hole();
        for count in crate::swarm::SWARM_COUNTS.into_iter().chain([16384]) {
            let bodies = swarm_bodies(count, SPIN, 1000.0);
            let mut row = format!("{count:>6} bodies:");
            for brute_force in [true, false] {
                if brute_force && count > 4096 {
                    row += "  brute force skipped";
                    continue;
                }
                let start = std::time::Instant::now();
                let swarm = device(&bodies, brute_force);
                let build = start.elapsed().as_secs_f64() * 1000.0;
                render(&scene, Some(&swarm));
                let mut times: Vec<f64> = (0..5).map(|_| render(&scene, Some(&swarm)).1).collect();
                times.sort_by(f64::total_cmp);
                let name = if brute_force { "brute force" } else { "BVH" };
                row += &format!("  {name} {:7.1} ms (upload {build:.1} ms)", times[2]);
                if !brute_force && count == 1024 {
                    let (image, _) = render(&scene, Some(&swarm));
                    std::fs::write("target/swarm-1024.rgba32f", bytemuck::cast_slice(&image))
                        .unwrap();
                }
            }
            println!("{row}");
        }
    }
}

/// Times the legacy RK4 controller (`bh_geodesic_experiments` with bit 2) against
/// the default Dormand–Prince `bh_geodesic`, alternating launches, and compares
/// their images.
#[cfg(test)]
#[test]
#[ignore = "requires a CUDA GPU; run with --release -- --ignored --nocapture"]
fn dp45_controller_benchmark() {
    use crate::simulation::{KERR_SPIN, default_binary_spins, scene_objects};
    let cuda = shared_cuda();
    cuda.bind_to_thread();
    for (name, f) in [
        ("bh_geodesic", &cuda.geodesic),
        ("bh_geodesic_experiments", &cuda.geodesic_experiments),
    ] {
        println!(
            "{name}: {} registers, {} local bytes per thread",
            f.num_regs().unwrap(),
            f.local_size_bytes().unwrap()
        );
    }
    let cam = crate::camera::OrbitalCamera::default();
    let sky: CudaSlice<u8> = cuda.clone_htod(bytemuck::cast_slice(&[
        0.2_f32, 0.3, 0.9, 1.0, 0.9, 0.5, 0.2, 1.0,
    ]));
    for binary in [false, true] {
        let scene = scene_objects(KERR_SPIN, false, binary, 0.0, default_binary_spins());
        let mut objects = GpuObjectsUniform::zeroed();
        objects.num_objects = scene.len() as i32;
        for (i, object) in scene.iter().enumerate() {
            objects.pos_radius[i] = object.position.extend(object.radius).into();
            objects.color[i] = object.color.into();
            objects.mass[i][0] = object.mass;
            objects.spin[i] = object.spin.extend(0.0).into();
        }
        let disk = build_disk_uniform(&DiskConfigUniform {
            spin: KERR_SPIN,
            binary_enabled: binary,
            ..DiskConfigUniform::default()
        });
        let d_objects = cuda.clone_htod(bytemuck::bytes_of(&objects));
        let d_disk = cuda.clone_htod(bytemuck::bytes_of(&disk));
        for (width, height) in [(400u32, 300u32), (960, 540)] {
            let camera = GpuCameraUniform {
                pos: cam.position().into(),
                right: cam.right().into(),
                up: cam.up().into(),
                forward: cam.forward().into(),
                tan_half_fov: cam.tan_half_fov(),
                aspect: width as f32 / height as f32,
                max_iter: cam.max_iter,
                frequency_ghz: cam.frequency_ghz,
                faraday_depth: cam.faraday_depth,
                conversion_depth: cam.conversion_depth,
                ..GpuCameraUniform::zeroed()
            };
            let d_camera = cuda.clone_htod(bytemuck::bytes_of(&camera));
            let cfg = ray_launch_config(width, height, !binary);
            let mut outputs =
                [0, 1].map(|_| cuda.alloc_zeros::<f32>((width * height * 4) as usize));
            let mut times = [Vec::new(), Vec::new()];
            let timing = Some(cudarc::driver::sys::CUevent_flags::CU_EVENT_DEFAULT);
            for sample in 0..23 {
                for (variant, output) in outputs.iter_mut().enumerate() {
                    let kernel = [&cuda.geodesic_experiments, &cuda.geodesic][variant];
                    let start = cuda.stream.record_event(timing).unwrap();
                    let mut builder = cuda.stream.launch_builder(kernel);
                    builder.arg(output);
                    builder.arg(&d_camera);
                    builder.arg(&d_disk);
                    builder.arg(&d_objects);
                    builder.arg(&sky);
                    builder.arg(&width);
                    builder.arg(&height);
                    builder.arg(&2u32);
                    builder.arg(&1u32);
                    if variant == 0 {
                        builder.arg(&4u32);
                    }
                    unsafe { builder.launch(cfg).unwrap() };
                    drop(builder);
                    let end = cuda.stream.record_event(timing).unwrap();
                    end.synchronize().unwrap();
                    // Three warm-up launches per variant.
                    if sample >= 3 {
                        times[variant].push(start.elapsed_ms(&end).unwrap());
                    }
                }
            }
            let [rk4, dp45] = outputs.map(|output| cuda.clone_dtoh(&output));
            assert!(dp45.iter().all(|v| v.is_finite()));
            let differing = rk4
                .as_chunks::<4>()
                .0
                .iter()
                .zip(dp45.as_chunks::<4>().0)
                .filter(|(a, b)| a.iter().zip(*b).any(|(x, y)| (x - y).abs() > 1.0 / 255.0))
                .count();
            let largest = rk4
                .iter()
                .zip(&dp45)
                .map(|(a, b)| (a - b).abs())
                .fold(0.0_f32, f32::max);
            let [rk4_t, dp45_t] = times.map(|mut t| {
                t.sort_unstable_by(f32::total_cmp);
                (t[t.len() / 2], t[(t.len() * 95).div_ceil(100) - 1])
            });
            println!(
                "{} {width}×{height}: rk4 median {:.1} / p95 {:.1} ms, dp45 median {:.1} / p95 {:.1} ms; \
                 {differing} pixels differ by more than 1/255, largest channel difference {largest:.3}",
                if binary { "binary" } else { "single" },
                rk4_t.0,
                rk4_t.1,
                dp45_t.0,
                dp45_t.1,
            );
        }
    }
}

/// Escape directions of the pixels where the RK4 and Dormand–Prince controllers
/// disagree most in the `--profile-renderer` close-up, against a binary64 RK4
/// reference of the CPU Kerr field (`certified::Kerr`) started from the GPU's own
/// initial state. Diagnostic: prints which controller is closer.
#[cfg(test)]
#[test]
#[ignore = "requires a CUDA GPU; run with --release -- --ignored --nocapture"]
fn dp45_disagreements_against_a_binary64_reference() {
    use crate::simulation::{
        DiskConfig, DiskModel, KERR_SPIN, default_binary_spins, scene_objects,
    };
    let cuda = shared_cuda();
    cuda.bind_to_thread();
    let (width, height) = (400u32, 300u32);
    // The profile runner's close-up pose, without jitter.
    let cam = crate::camera::OrbitalCamera {
        radius: 24.0,
        elevation: std::f64::consts::FRAC_PI_2 - 0.1,
        azimuth: 0.0,
        ..Default::default()
    };
    let camera = GpuCameraUniform {
        pos: cam.position().into(),
        right: cam.right().into(),
        up: cam.up().into(),
        forward: cam.forward().into(),
        tan_half_fov: cam.tan_half_fov(),
        aspect: width as f32 / height as f32,
        max_iter: cam.max_iter,
        polarization_view: 2,
        frequency_ghz: cam.frequency_ghz,
        faraday_depth: cam.faraday_depth,
        conversion_depth: cam.conversion_depth,
        ..GpuCameraUniform::zeroed()
    };
    let config = DiskConfig::for_model(DiskModel::TruncatedHotFlow, KERR_SPIN);
    let disk = build_disk_uniform(&DiskConfigUniform {
        spin: config.spin,
        r_outer_rs: config.r_outer_rs,
        model: config.model.as_u32(),
        h_thin: config.h_thin,
        h_hot: config.h_hot,
        r_trunc_rs: config.r_trunc_rs,
        tilt_deg: config.tilt_deg,
        r_bp_rs: config.r_bp_rs,
        twist_deg: config.twist_deg,
        binary_enabled: false,
    });
    let scene = scene_objects(KERR_SPIN, false, false, 0.0, default_binary_spins());
    assert_eq!(scene.len(), 1);
    let mut objects = GpuObjectsUniform::zeroed();
    objects.num_objects = 1;
    objects.pos_radius[0] = scene[0].position.extend(scene[0].radius).into();
    objects.color[0] = scene[0].color.into();
    objects.mass[0][0] = scene[0].mass;
    objects.spin[0] = scene[0].spin.extend(0.0).into();
    let d_camera = cuda.clone_htod(bytemuck::bytes_of(&camera));
    let d_disk = cuda.clone_htod(bytemuck::bytes_of(&disk));
    let d_objects = cuda.clone_htod(bytemuck::bytes_of(&objects));
    let sky: CudaSlice<u8> =
        cuda.clone_htod(bytemuck::cast_slice(&[0.2_f32, 0.3, 0.9, 1.0, 0.9, 0.5, 0.2, 1.0]));

    // Escape direction per pixel, or None, for the RK4 (4) and default DP45 (0) controllers.
    let diagnostics_kernel = cuda.module.load_function("bh_geodesic_diagnostics").unwrap();
    let directions = [4u32, 0].map(|experiments| {
        let pixels = (width * height) as usize;
        let mut image = cuda.alloc_zeros::<f32>(pixels * 4);
        let mut diagnostics = cuda.alloc_zeros::<u32>(pixels * RAY_FIELDS);
        let mut launch = cuda.stream.launch_builder(&diagnostics_kernel);
        launch.arg(&mut image);
        launch.arg(&d_camera);
        launch.arg(&d_disk);
        launch.arg(&d_objects);
        launch.arg(&sky);
        launch.arg(&width);
        launch.arg(&height);
        launch.arg(&2u32);
        launch.arg(&1u32);
        launch.arg(&mut diagnostics);
        launch.arg(&experiments);
        unsafe { launch.launch(ray_launch_config(width, height, true)).unwrap() };
        drop(launch);
        let data = cuda.clone_dtoh(&diagnostics);
        // RayDiagnostics: exit at field 7 (7 = escaped), sky direction at 9..12.
        data.as_chunks::<RAY_FIELDS>()
            .0
            .iter()
            .map(|d| (d[7] == 7).then(|| [9, 10, 11].map(|i| f64::from(f32::from_bits(d[i])))))
            .collect::<Vec<_>>()
    });
    let angle = |a: [f64; 3], b: [f64; 3]| {
        let dot: f64 = (0..3).map(|i| a[i] * b[i]).sum();
        let norm = |v: [f64; 3]| v.iter().map(|x| x * x).sum::<f64>().sqrt();
        (dot / (norm(a) * norm(b))).clamp(-1.0, 1.0).acos()
    };
    let mut disagreements: Vec<(f64, u32)> = (0..width * height)
        .filter_map(|i| match (directions[0][i as usize], directions[1][i as usize]) {
            (Some(a), Some(b)) => Some((angle(a, b), i)),
            _ => None,
        })
        .collect();
    disagreements.sort_by(|a, b| b.0.total_cmp(&a.0));
    // The 16 largest disagreements, then four ordinary pixels as a set-up check.
    let mut chosen: Vec<u32> = disagreements.iter().take(16).map(|d| d.1).collect();
    let n = disagreements.len();
    chosen.extend([n / 5, 2 * n / 5, 3 * n / 5, 4 * n / 5].map(|k| disagreements[k].1));

    let pixel_input: Vec<f32> = chosen
        .iter()
        .flat_map(|&i| [(i % width) as f32, (i / width) as f32, width as f32, height as f32])
        .collect();
    let d_pixels = cuda.clone_htod(&pixel_input);
    let mut d_states = cuda.alloc_zeros::<f32>(chosen.len() * 12);
    let pixel_kernel = cuda.module.load_function("bh_test_pixel_ray").unwrap();
    let mut launch = cuda.stream.launch_builder(&pixel_kernel);
    launch.arg(&d_camera);
    launch.arg(&d_objects);
    launch.arg(&d_pixels);
    launch.arg(&mut d_states);
    let count = chosen.len() as u32;
    launch.arg(&count);
    unsafe {
        launch
            .launch(LaunchConfig {
                grid_dim: (count, 1, 1),
                block_dim: (1, 1, 1),
                shared_mem_bytes: 0,
            })
            .unwrap()
    };
    drop(launch);
    let states = cuda.clone_dtoh(&d_states);

    let spin = scene[0].spin.as_dvec3().to_array();
    let kerr = black_hole::certified::Kerr::new(spin).unwrap();
    let horizon = 1.0 + (1.0 - spin.iter().map(|a| a * a).sum::<f64>()).sqrt();
    let reference = |start, factor| binary64_reference(&kerr, horizon, start, factor);
    let (mut rk4_closer, mut dp45_closer) = (0, 0);
    for (n, &i) in chosen.iter().enumerate() {
        let v: Vec<f64> = states[12 * n..12 * n + 12].iter().map(|&x| f64::from(x)).collect();
        let start = [v[0], v[1], v[2], v[4], v[5], v[6], v[7], v[8], v[9], v[10], v[11]];
        let (rk4, dp45) = (directions[0][i as usize].unwrap(), directions[1][i as usize].unwrap());
        let (x, y) = (i % width, i / width);
        let (Some(coarse), Some(fine)) = (reference(start, 0.004), reference(start, 0.002)) else {
            println!("({x}, {y}): reference reached the horizon");
            continue;
        };
        let converged = angle(coarse, fine);
        let (e_rk4, e_dp45) = (angle(rk4, fine), angle(dp45, fine));
        println!(
            "({x:3}, {y:3}): controllers differ {:.2e} rad; error rk4 {e_rk4:.2e}, \
             dp45 {e_dp45:.2e}; reference step-halving change {converged:.1e}",
            angle(rk4, dp45)
        );
        assert!(converged < 1.0e-6, "reference not converged at ({x}, {y})");
        if n < 16 {
            if e_dp45 < e_rk4 {
                dp45_closer += 1;
            } else {
                rk4_closer += 1;
            }
        } else {
            // Ordinary pixels: both controllers agree with the reference.
            assert!(e_rk4.max(e_dp45) < 1.0e-3, "set-up mismatch at ({x}, {y})");
        }
    }
    println!("largest disagreements: dp45 closer at {dp45_closer}, rk4 closer at {rk4_closer}");
}

/// Binary64 RK4 on the CPU Kerr field with steps of `factor` times horizon clearance
/// over speed, until the coordinate radius passes 1600 as in the renderer. Returns the
/// escape direction, or None if the ray nears the horizon.
#[cfg(test)]
fn binary64_reference(
    kerr: &black_hole::certified::Kerr,
    horizon: f64,
    start: [f64; 11],
    factor: f64,
) -> Option<[f64; 3]> {
    let mut s = start;
    let add = |s: [f64; 11], d: [f64; 11], h: f64| std::array::from_fn(|i| s[i] + h * d[i]);
    for _ in 0..50_000_000 {
        let k1 = kerr.phase_rhs(s);
        if s[..3].iter().map(|x| x * x).sum::<f64>().sqrt() > 1600.0 {
            return Some([k1[0], k1[1], k1[2]]);
        }
        let clearance = kerr.radius([s[0], s[1], s[2]]) - horizon;
        if clearance < 1.0e-3 {
            return None;
        }
        let speed = k1[..3].iter().map(|x| x * x).sum::<f64>().sqrt();
        let h = factor * clearance / speed;
        let k2 = kerr.phase_rhs(add(s, k1, 0.5 * h));
        let k3 = kerr.phase_rhs(add(s, k2, 0.5 * h));
        let k4 = kerr.phase_rhs(add(s, k3, h));
        s = std::array::from_fn(|i| s[i] + h / 6.0 * (k1[i] + 2.0 * k2[i] + 2.0 * k3[i] + k4[i]));
    }
    None
}

/// Guarded early capture (checklist P0.3) must not change the image. Renders each
/// scene with the default kernel options and with the full trace (bit 0) through the
/// diagnostics kernel and requires bit-identical output, across spins up to the
/// |a| <= 0.995 guard edge and the 0.999 fallback, every disk model, intensity, EVPA
/// and circular-polarization views, cameras near the pole and just above and below
/// the disk, and the binary fallback. A sample of early-captured pixels is also traced
/// from the GPU's initial state in binary64 on the CPU Kerr field; none may escape.
#[cfg(test)]
#[test]
#[ignore = "requires a CUDA GPU; run with --release -- --ignored --nocapture"]
fn early_capture_matches_the_full_trace() {
    use crate::simulation::{DiskConfig, DiskModel, default_binary_spins, scene_objects};
    const EARLY_CAPTURE: u32 = 9;
    let cuda = shared_cuda();
    cuda.bind_to_thread();
    let (width, height) = (160u32, 120u32);
    let pixels = (width * height) as usize;
    let sky: CudaSlice<u8> =
        cuda.clone_htod(bytemuck::cast_slice(&[0.2_f32, 0.3, 0.9, 1.0, 0.9, 0.5, 0.2, 1.0]));
    let diagnostics_kernel = cuda.module.load_function("bh_geodesic_diagnostics").unwrap();
    let pixel_kernel = cuda.module.load_function("bh_test_pixel_ray").unwrap();
    let models = [
        DiskModel::ThinNt,
        DiskModel::TruncatedHotFlow,
        DiskModel::SlimFunnel,
        DiskModel::WarpedThin,
    ];
    let elevations = [
        0.15,
        std::f64::consts::FRAC_PI_2 - 0.1,
        std::f64::consts::FRAC_PI_2 + 0.5,
    ];
    let mut checked = 0;
    for spin in [0.0_f32, 0.82, -0.82, 0.99, -0.99, 0.995, -0.995, 0.999] {
        let mut early_total = 0;
        for binary in [false, true] {
            if binary && spin != 0.82 {
                continue;
            }
            let scene = scene_objects(spin, false, binary, 0.0, default_binary_spins());
            let mut objects = GpuObjectsUniform::zeroed();
            objects.num_objects = scene.len() as i32;
            for (i, object) in scene.iter().enumerate() {
                objects.pos_radius[i] = object.position.extend(object.radius).into();
                objects.color[i] = object.color.into();
                objects.mass[i][0] = object.mass;
                objects.spin[i] = object.spin.extend(0.0).into();
            }
            let d_objects = cuda.clone_htod(bytemuck::bytes_of(&objects));
            let mut binary_early = 0;
            for model in &models {
                let config = DiskConfig::for_model(model.clone(), spin);
                let disk = build_disk_uniform(&DiskConfigUniform {
                    spin: config.spin,
                    r_outer_rs: config.r_outer_rs,
                    model: config.model.as_u32(),
                    h_thin: config.h_thin,
                    h_hot: config.h_hot,
                    r_trunc_rs: config.r_trunc_rs,
                    tilt_deg: config.tilt_deg,
                    r_bp_rs: config.r_bp_rs,
                    twist_deg: config.twist_deg,
                    binary_enabled: binary,
                });
                let d_disk = cuda.clone_htod(bytemuck::bytes_of(&disk));
                for elevation in elevations {
                    for polarization_view in [0u32, 2, 5] {
                        let cam = crate::camera::OrbitalCamera {
                            radius: 24.0,
                            elevation,
                            azimuth: 0.7,
                            ..Default::default()
                        };
                        let camera = GpuCameraUniform {
                            pos: cam.position().into(),
                            right: cam.right().into(),
                            up: cam.up().into(),
                            forward: cam.forward().into(),
                            tan_half_fov: cam.tan_half_fov(),
                            aspect: width as f32 / height as f32,
                            max_iter: cam.max_iter,
                            polarization_view,
                            frequency_ghz: cam.frequency_ghz,
                            faraday_depth: cam.faraday_depth,
                            conversion_depth: cam.conversion_depth,
                            ..GpuCameraUniform::zeroed()
                        };
                        let d_camera = cuda.clone_htod(bytemuck::bytes_of(&camera));
                        let [(early_image, early_rays), (full_image, _)] =
                            [0u32, 1].map(|experiments| {
                                let mut image = cuda.alloc_zeros::<f32>(pixels * 4);
                                let mut diagnostics =
                                    cuda.alloc_zeros::<u32>(pixels * RAY_FIELDS);
                                let mut launch = cuda.stream.launch_builder(&diagnostics_kernel);
                                launch.arg(&mut image);
                                launch.arg(&d_camera);
                                launch.arg(&d_disk);
                                launch.arg(&d_objects);
                                launch.arg(&sky);
                                launch.arg(&width);
                                launch.arg(&height);
                                launch.arg(&2u32);
                                launch.arg(&1u32);
                                launch.arg(&mut diagnostics);
                                launch.arg(&experiments);
                                let cfg = ray_launch_config(width, height, !binary);
                                unsafe { launch.launch(cfg).unwrap() };
                                drop(launch);
                                (cuda.clone_dtoh(&image), cuda.clone_dtoh(&diagnostics))
                            });
                        let differing = early_image
                            .iter()
                            .zip(&full_image)
                            .filter(|(a, b)| a.to_bits() != b.to_bits())
                            .count();
                        assert_eq!(
                            differing, 0,
                            "spin {spin}, binary {binary}, {model:?}, elevation {elevation}, view {polarization_view}"
                        );
                        let early: Vec<usize> = early_rays
                            .as_chunks::<RAY_FIELDS>()
                            .0
                            .iter()
                            .enumerate()
                            .filter(|(_, d)| d[7] == EARLY_CAPTURE)
                            .map(|(i, _)| i)
                            .collect();
                        if binary {
                            binary_early += early.len();
                            continue;
                        }
                        early_total += early.len();
                        if early.is_empty() || polarization_view != 0 {
                            continue;
                        }
                        // Independent check of four early-captured pixels.
                        let chosen: Vec<u32> =
                            (0..4).map(|k| early[k * early.len() / 4] as u32).collect();
                        let input: Vec<f32> = chosen
                            .iter()
                            .flat_map(|&i| {
                                [(i % width) as f32, (i / width) as f32, width as f32, height as f32]
                            })
                            .collect();
                        let d_pixels = cuda.clone_htod(&input);
                        let mut d_states = cuda.alloc_zeros::<f32>(chosen.len() * 12);
                        let count = chosen.len() as u32;
                        let mut launch = cuda.stream.launch_builder(&pixel_kernel);
                        launch.arg(&d_camera);
                        launch.arg(&d_objects);
                        launch.arg(&d_pixels);
                        launch.arg(&mut d_states);
                        launch.arg(&count);
                        let one_thread_each = LaunchConfig {
                            grid_dim: (count, 1, 1),
                            block_dim: (1, 1, 1),
                            shared_mem_bytes: 0,
                        };
                        unsafe { launch.launch(one_thread_each).unwrap() };
                        drop(launch);
                        let states = cuda.clone_dtoh(&d_states);
                        let kerr =
                            black_hole::certified::Kerr::new(scene[0].spin.as_dvec3().to_array())
                                .unwrap();
                        let a = f64::from(spin);
                        let horizon = 1.0 + (1.0 - a * a).sqrt();
                        for (n, &i) in chosen.iter().enumerate() {
                            let v: Vec<f64> =
                                states[12 * n..12 * n + 12].iter().map(|&x| f64::from(x)).collect();
                            let start =
                                [v[0], v[1], v[2], v[4], v[5], v[6], v[7], v[8], v[9], v[10], v[11]];
                            assert!(
                                binary64_reference(&kerr, horizon, start, 0.004).is_none(),
                                "early-captured pixel {i} escapes in binary64 at spin {spin}, {model:?}, elevation {elevation}"
                            );
                            checked += 1;
                        }
                    }
                }
            }
            assert_eq!(binary_early, 0, "the binary must keep the full trace");
        }
        println!("spin {spin}: {early_total} early captures; every image identical");
        if spin.abs() > 0.995 {
            assert_eq!(early_total, 0, "spin {spin} is outside the guard");
        } else {
            assert!(early_total > 0, "no early captures at spin {spin}");
        }
    }
    println!("{checked} early-captured pixels confirmed captured in binary64");
}
