//! Fluid-frame photon energies in the production renderer (obligation P1).
//!
//! `sample_plasma` clamps the redshift `1/E` to [0.01, 20], which is inactive
//! exactly when the fluid-frame energy `E` (camera Eulerian energy 1) lies in
//! [0.05, 100]. This sweep traces admitted scenes with the renderer's rules and
//! reports the extreme energies of every disk sample.

use bevy::render::render_resource::BufferUsages;
use black_hole::physics::{kerr_horizon_radius_rg, kerr_isco_radius_rg};
use googletest::prelude::*;
use rstest::rstest;

/// Disk presets as (model, h_thin, h_hot, r_outer, r_trunc): thin, truncated hot flow, slim.
const DISKS: [(u32, f32, f32, f32, f32); 3] = [
    (0, 0.03, 0.5, 30.0, 20.0),
    (1, 0.02, 0.5, 40.0, 20.0),
    (2, 0.05, 0.45, 24.0, 6.0),
];

fn words(values: &[f32]) -> Vec<u8> {
    values.iter().flat_map(|v| v.to_le_bytes()).collect()
}

/// Traces one admitted scene on the GPU; returns (min E, max E, disk samples).
fn disk_energies(
    spin: f32,
    (model, h_thin, h_hot, r_outer, r_trunc): (u32, f32, f32, f32, f32),
    radius: f32,
    elevation: f32,
) -> (f32, f32, f32) {
    let el = elevation.to_radians();
    let pos = [radius * el.cos(), radius * el.sin(), 0.0];
    let forward = [-el.cos(), -el.sin(), 0.0];
    let right = [0.0, 0.0, 1.0];
    let up = [
        right[1] * forward[2] - right[2] * forward[1],
        right[2] * forward[0] - right[0] * forward[2],
        right[0] * forward[1] - right[1] * forward[0],
    ];
    let mut camera = Vec::new();
    for v in [pos, right, up, forward] {
        camera.extend_from_slice(&v);
        camera.push(0.0);
    }
    let tan_half_fov = 30.0_f32.to_radians().tan();
    camera.extend_from_slice(&[tan_half_fov, 1.0]);
    let mut cam = words(&camera);
    cam.extend_from_slice(&0u32.to_le_bytes()); // moving
    cam.extend(words(&[0.0, 0.0])); // jitter
    cam.extend_from_slice(&0u32.to_le_bytes()); // heatmap
    cam.extend_from_slice(&10_000u32.to_le_bytes()); // max_iter
    cam.extend_from_slice(&0u32.to_le_bytes()); // polarization view
    cam.extend(words(&[230.0, 0.0, 0.0, 0.0]));
    assert_eq!(cam.len(), 112);
    let isco = kerr_isco_radius_rg(spin);
    let mut dsk = words(&[
        isco,
        r_outer,
        h_thin,
        h_hot,
        spin,
        kerr_horizon_radius_rg(spin),
        isco,
        r_trunc,
        0.0,
        10.0,
        0.0,
    ]);
    dsk.extend_from_slice(&model.to_le_bytes());
    dsk.extend_from_slice(&0u32.to_le_bytes());
    dsk.extend(words(&[0.0, 0.0, 0.0]));
    assert_eq!(dsk.len(), 64);
    let mut objects = vec![0u8; 1040];
    objects[..4].copy_from_slice(&1i32.to_le_bytes());
    objects[528..532].copy_from_slice(&1f32.to_le_bytes());
    objects[788..792].copy_from_slice(&spin.to_le_bytes());
    let data = crate::gpu::run_groups(
        include_str!("../energy.wesl"),
        "energies",
        &[
            &[
                (1, &cam, BufferUsages::UNIFORM),
                (2, &dsk, BufferUsages::UNIFORM),
                (3, &objects, BufferUsages::UNIFORM),
            ],
            &[],
        ],
        32 * 32 * 16,
        4,
    );
    let values: &[f32] = bytemuck::cast_slice(&data);
    // Each pixel reports (min E, max E, disk sample count, _).
    values.chunks(4).filter(|px| px[2] > 0.0).fold(
        (f32::INFINITY, f32::NEG_INFINITY, 0.0),
        |(lo, hi, n), px| (lo.min(px[0]), hi.max(px[1]), n + px[2]),
    )
}

/// Records the counterexample: an admitted scene drives E above 100, so the
/// clamp replaces the redshift 1/E by 0.01 and the cubed boost is too large.
#[rstest]
#[case::spin_0_999_hot_flow_r8_el10(0.999, DISKS[1], 8.0, 10.0)]
// Within 0.1% of the hot flow here; which of the two tops the sweep depends on the GPU.
#[case::spin_0_999_slim_r8_el10(0.999, DISKS[2], 8.0, 10.0)]
#[ignore = "requires a GPU (lavapipe works); run with --release -- --ignored"]
fn admitted_scene_activates_the_redshift_clamp(
    #[case] spin: f32,
    #[case] disk: (u32, f32, f32, f32, f32),
    #[case] radius: f32,
    #[case] elevation: f32,
) {
    let (_, high, samples) = disk_energies(spin, disk, radius, elevation);
    assert_that!(samples, gt(0.0));
    assert_that!(high, gt(100.0));
}

/// Reproduces the sweep statistics quoted in verification/OBLIGATIONS.md (P1).
#[test]
#[ignore = "requires a GPU (lavapipe works); run with --release -- --ignored"]
fn fluid_energy_extremes() {
    let mut low = (f32::INFINITY, String::new());
    let mut high = (f32::NEG_INFINITY, String::new());
    let mut total = 0.0;
    for spin in [0.999_f32, -0.999, 0.82] {
        for disk in DISKS {
            for radius in [1.6_f32, 3.0, 8.0, 40.0, 160.0] {
                for elevation in [10.0_f32, 60.0] {
                    let (lo, hi, samples) = disk_energies(spin, disk, radius, elevation);
                    let label = format!(
                        "spin {spin}, model {}, camera r {radius}, el {elevation}",
                        disk.0
                    );
                    total += samples;
                    if lo < low.0 {
                        low = (lo, label.clone());
                    }
                    if hi > high.0 {
                        high = (hi, label);
                    }
                }
            }
        }
    }
    println!(
        "{total} disk samples; min E {} ({}); max E {} ({})",
        low.0, low.1, high.0, high.1
    );
    assert_that!(
        high.0,
        gt(100.0),
        "no admitted disk sample activated the redshift clamp"
    );
}
