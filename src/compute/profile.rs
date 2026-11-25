use std::{
    fs::{File, create_dir_all},
    io::{self, BufWriter, Write},
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
    time::Instant,
};

use bevy::{
    prelude::*,
    render::{
        RenderApp,
        extract_resource::{ExtractResource, ExtractResourcePlugin},
        renderer::RenderGraph,
    },
    winit::WinitSettings,
};

use crate::{
    camera::{OrbitalCamera, update_orbital_camera},
    simulation::{
        BinaryBlackHoles, DiskConfig, DiskModel, KERR_SPIN, SimObjects, default_binary_spins,
        scene_objects,
    },
};

use super::{accumulate::dispatch_accumulate, pipeline::capture_ray_profile};

const SAMPLES: usize = 60;
const WARMUP: usize = 12;
const PHASE_FRAMES: usize = SAMPLES + WARMUP;
pub(super) const RAY_FIELDS: usize = 18;
/// Exit names in the order of RayExit in the CUDA kernel.
pub(super) const RAY_EXITS: [&str; 11] = [
    "iteration_limit",
    "invalid_camera",
    "invalid_metric",
    "horizon",
    "step_rejected",
    "affine_stagnation",
    "object_hit",
    "escaped",
    "opaque",
    "early_capture",
    "near_critical",
];

#[derive(Clone, Default, ExtractResource, Resource)]
#[extract_app(RenderApp)]
pub(super) struct RayProfile {
    requested: bool,
    complete: Arc<AtomicBool>,
}

impl RayProfile {
    pub fn requested(&self) -> bool {
        self.requested && !self.complete.load(Ordering::Acquire)
    }

    pub fn complete(&self) {
        self.complete.store(true, Ordering::Release);
    }
}

#[derive(Default)]
struct Run {
    frame: usize,
    previous: Option<Instant>,
    samples: Vec<f64>,
}

pub(crate) fn install(app: &mut App) {
    app.init_resource::<RayProfile>()
        .insert_resource(WinitSettings::continuous())
        .add_plugins(ExtractResourcePlugin::<RayProfile>::default())
        .add_systems(PreUpdate, profile_frame.after(update_orbital_camera));

    app.sub_app_mut(RenderApp).add_systems(
        RenderGraph,
        capture_ray_profile
            .after(super::dispatch_geodesic)
            .before(dispatch_accumulate),
    );
}

fn profile_frame(
    mut run: Local<Run>,
    mut cam: ResMut<OrbitalCamera>,
    mut disk: ResMut<DiskConfig>,
    mut binary: ResMut<BinaryBlackHoles>,
    mut objects: ResMut<SimObjects>,
    mut request: ResMut<RayProfile>,
    mut exit: MessageWriter<AppExit>,
) {
    let frame = run.frame;
    let now = Instant::now();
    let previous = run.previous.replace(now);

    if frame == 0 {
        cam.radius = 24.0;
        cam.elevation = std::f64::consts::FRAC_PI_2 - 0.1;
        cam.polarization_view = 2;
        *disk = DiskConfig::for_model(DiskModel::TruncatedHotFlow, KERR_SPIN);
        binary.enabled = false;
        objects.0 = scene_objects(KERR_SPIN, false, false, 0.0, default_binary_spins());
    }

    // Each entry measures the preceding frame, including the window and render loop.
    if let Some(previous) = previous.filter(|_| (1..=2 * PHASE_FRAMES).contains(&frame)) {
        let rendered_frame = frame - 1;
        if rendered_frame % PHASE_FRAMES >= WARMUP {
            run.samples.push((now - previous).as_secs_f64() * 1000.0);
        }
        if frame.is_multiple_of(PHASE_FRAMES) {
            run.samples.sort_unstable_by(f64::total_cmp);
            let median = (run.samples[SAMPLES / 2 - 1] + run.samples[SAMPLES / 2]) * 0.5;
            let p95 = run.samples[(SAMPLES * 95).div_ceil(100) - 1];
            let phase = if frame == PHASE_FRAMES {
                "still"
            } else {
                "orbit"
            };
            println!("{phase}: {SAMPLES} frames, median {median:.2} ms, p95 {p95:.2} ms");
            run.samples.clear();
        }
    }

    if frame >= 2 * PHASE_FRAMES {
        cam.azimuth = 0.0;
        cam.is_moving = true; // Render the diagnostic at the initial pose without jitter.
        if frame == 2 * PHASE_FRAMES {
            request.requested = true;
        } else if request.complete.load(Ordering::Acquire) {
            exit.write(AppExit::Success);
        }
    } else if frame >= PHASE_FRAMES {
        cam.azimuth = (frame - PHASE_FRAMES + 1) as f64 * 0.01;
        cam.is_moving = true;
    }
    run.frame += 1;
}

pub(super) fn write_ray_profile(
    width: u32,
    height: u32,
    data: &[u32],
    experiments: u32,
) -> io::Result<()> {
    // Field order matches RayDiagnostics in the CUDA kernel.
    create_dir_all("target")?;
    let mut path = String::from("target/renderer-rays");
    for (bit, name) in [
        (1, "-full-trace"),
        (2, "-no-far-field"),
        (4, "-rk4"),
        (256, "-no-analytic-escape"),
    ] {
        if experiments & bit != 0 {
            path.push_str(name);
        }
    }
    path.push_str(".csv");
    let mut file = BufWriter::new(File::create(&path)?);
    writeln!(
        file,
        "x,y,iterations,steps,rejected_attempts,near_horizon_steps,far_field_steps,disk_limited_steps,controller_limited_steps,exit,wide_steps,sky_x,sky_y,sky_z,plasma_steps,vacuum_disk_steps,stokes_i,stokes_q,stokes_u,stokes_v"
    )?;
    let (rays, remainder) = data.as_chunks::<RAY_FIELDS>();
    assert!(remainder.is_empty() && rays.len() == width as usize * height as usize);
    for (
        pixel,
        &[
            iterations,
            steps,
            rejected,
            near,
            far,
            disk,
            controller,
            exit,
            wide,
            sky_x,
            sky_y,
            sky_z,
            plasma_steps,
            vacuum_disk_steps,
            stokes_i,
            stokes_q,
            stokes_u,
            stokes_v,
        ],
    ) in rays.iter().enumerate()
    {
        let x = pixel % width as usize;
        let y = pixel / width as usize;
        let reason = RAY_EXITS[exit as usize];
        let [sky_x, sky_y, sky_z] = [sky_x, sky_y, sky_z].map(f32::from_bits);
        let [stokes_i, stokes_q, stokes_u, stokes_v] =
            [stokes_i, stokes_q, stokes_u, stokes_v].map(f32::from_bits);
        writeln!(
            file,
            "{x},{y},{iterations},{steps},{rejected},{near},{far},{disk},{controller},{reason},{wide},{sky_x},{sky_y},{sky_z},{plasma_steps},{vacuum_disk_steps},{stokes_i},{stokes_q},{stokes_u},{stokes_v}"
        )?;
    }
    file.flush()?;
    println!("Wrote {width}×{height} ray diagnostics to {path}");
    Ok(())
}
