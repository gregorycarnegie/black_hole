//! Fluid-frame photon energies in the production renderer (obligation P1).
//!
//! `sample_plasma` clamps the redshift `1/E` to [0.01, 20], which is inactive
//! exactly when the fluid-frame energy `E` (camera Eulerian energy 1) lies in
//! [0.05, 100]. This sweep traces admitted scenes with the renderer's rules and
//! reports the extreme energies of every disk sample.

use bevy::render::render_resource::BufferUsages;
use black_hole::physics::{kerr_horizon_radius_rg, kerr_isco_radius_rg};

fn words(values: &[f32]) -> Vec<u8> {
    values.iter().flat_map(|v| v.to_le_bytes()).collect()
}

#[test]
#[ignore = "requires a GPU (lavapipe works); run with --release -- --ignored"]
fn fluid_energy_extremes() {
    let mut low = (f32::INFINITY, String::new());
    let mut high = (f32::NEG_INFINITY, String::new());
    let mut total = 0.0;
    for &spin in &[0.999_f32, -0.999, 0.82] {
        for &(model, h_thin, h_hot, r_outer, r_trunc) in
            &[(0u32, 0.03_f32, 0.5_f32, 30.0_f32, 20.0_f32), (1, 0.02, 0.5, 40.0, 20.0), (2, 0.05, 0.45, 24.0, 6.0)]
        {
            for &radius in &[1.6_f32, 3.0, 8.0, 40.0, 160.0] {
                for &elevation in &[10.0_f32, 60.0] {
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
                    let label = format!("spin {spin}, model {model}, camera r {radius}, el {elevation}");
                    for px in values.chunks(4) {
                        if px[2] > 0.0 {
                            total += px[2];
                            if px[0] < low.0 {
                                low = (px[0], label.clone());
                            }
                            if px[1] > high.0 {
                                high = (px[1], label.clone());
                            }
                        }
                    }
                }
            }
        }
    }
    println!("{total} disk samples; min E {} ({}); max E {} ({})", low.0, low.1, high.0, high.1);
    // Records the counterexample: an admitted scene drives E above 100, so the
    // clamp replaces the redshift 1/E by 0.01 and the cubed boost is too large.
    assert!(high.0 > 100.0, "no admitted disk sample activated the redshift clamp");
}
