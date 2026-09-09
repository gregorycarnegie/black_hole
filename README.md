[![Rust](https://img.shields.io/badge/Rust-2024-f74c00?logo=rust&logoColor=white)](https://www.rust-lang.org/)
[![Bevy](https://img.shields.io/badge/Bevy-0.19.1-232326?logo=bevy&logoColor=white)](https://bevyengine.org/)
![WGSL](https://img.shields.io/badge/WGSL-compute%20shader-005a9c)
![Status](https://img.shields.io/badge/status-experimental-yellow)

# **black**_**hole**

Real-time black hole visualization using GPU ray-tracing in Bevy (Rust).

Current version: **0.3.0**. See the [changelog](CHANGELOG.md) for release notes.

Simulates null geodesics (light paths) in Kerr spacetime in mass-independent gravitational units, with a default binary black-hole scene, an accretion disk, and a deformed spacetime grid.

## Features

1. **GPU ray-tracing** — compute shader integrates null geodesics using RK4 in spin-aligned Kerr coordinates
2. **Accretion disk** — four switchable geometry presets (thin NT, truncated thin + hot flow, slim/super-Eddington, warped Bardeen-Petterson) with Kerr ISCO, frame dragging, Doppler beaming, and gravitational redshift
3. **Spacetime grid** — wireframe grid deformed by the Schwarzschild metric of each massive object
4. **Binary black holes** — equal-mass spinning black holes orbit a shared barycentre, with per-hole spin vectors and local Lense-Thirring frame-dragging in the binary ray marcher
5. **N-body gravity** — optional Newtonian gravity simulation using a fixed timestep, independent of rendering framerate
6. **Skyboxes** — a procedural checker grid plus bilinearly filtered equirectangular HDR space backgrounds sampled along each ray's lensed escape direction
7. **Filmic lighting** — an ACES curve approximation applied after combining disk and background lighting

## Controls

### Keyboard / Mouse

| Input           | Action                                         |
|-----------------|------------------------------------------------|
| Left mouse drag | Orbit camera                                   |
| Scroll wheel    | Zoom in/out                                    |
| `[` / `]`       | Decrease / increase FOV                        |
| `-` / `=`       | Decrease / increase render scale (25 – 100 %)  |
| Q / E           | Decrease / increase Kerr spin, or selected binary-hole spin magnitude (±0.05) |
| 1 / 2           | Select binary black hole A / B for spin editing |
| Z / X           | Decrease / increase outer disk radius (±1 r_s) |
| M               | Cycle disk geometry preset                     |
| F               | Toggle spacetime grid                          |
| N               | Toggle binary black holes                      |
| G               | Toggle n-body gravity                          |
| O               | Toggle debug bodies                            |
| B               | Cycle HDR skybox                               |
| `,` / `.`       | Decrease / increase max geodesic iterations    |
| H               | Toggle iteration-count heatmap                 |

### Xbox Controller

| Input            | Action                                      |
|------------------|---------------------------------------------|
| Left stick       | Orbit camera                                |
| RT / LT          | Zoom in / out                               |
| A                | Cycle skybox                                |
| B                | Toggle binary black holes                   |
| X                | Toggle spacetime grid                       |
| Y                | Toggle iteration-count heatmap              |
| Select           | Toggle n-body gravity                       |
| Start            | Toggle debug bodies                         |
| D-pad left/right | Select binary black hole A / B              |
| D-pad up/down    | Increase / decrease selected-hole spin a*   |
| Right stick      | Adjust selected-hole spin-axis X / Y        |
| RB / LB          | Increase / decrease selected-hole spin-axis Z |

## Building

Requires [Rust](https://rustup.rs/) (stable).

```bash
git clone https://github.com/gregorycarnegie/black_hole.git
cd black_hole
cargo run --release
```

## How it works

`src/compute/pipeline.rs` sets up a Bevy render graph node that dispatches `assets/shaders/geodesic.wgsl` — a WGSL compute shader — every frame. The shader receives the camera position, Kerr/accretion disk parameters, and scene objects via uniform buffers, then traces each pixel through curved spacetime, writing the result to a storage texture that is displayed as a fullscreen sprite.

Single-hole mode uses the Kerr geodesic integrator with accretion-disk shading. Binary mode switches to a two-source ray marcher: mass curvature is accumulated from both black holes, and each hole contributes a local gravitomagnetic / Lense-Thirring frame-dragging term from its spin vector.

In binary mode, the on-screen `BH` selector chooses which black hole is being edited. `Spin a*` changes that hole's spin magnitude, and the `Axis X/Y/Z` rows rotate its spin axis independently of the other hole.

The spacetime grid is drawn each frame using Bevy's `Gizmos` API, with vertex Y-positions displaced by `2 * sqrt(r_s * (r - r_s))` (the Schwarzschild embedding).

## Units and timing

Camera, objects, grid, Kerr radii, and GPU ray tracing use `G = c = M = 1`: distances are in gravitational radii `r_g = GM/c²`, and object masses are fractions of the total black-hole mass. The Schwarzschild radius is `2 r_g`; the UI continues to express disk radii in `r_s`. The same scene therefore represents a stellar-mass or supermassive black hole without changing shader constants.

To interpret a scene in SI units for any chosen mass `M`, multiply distances by `GM/c²`, velocities by `c`, and simulation times by `GM/c³`. Newtonian gravity advances one gravitational time unit per elapsed application second, using Bevy's fixed 64 Hz timestep. This is a visualization clock, not real-time SI playback. Binary motion remains a prescribed 18-second visual orbit and uses approximate lensing, rather than an evolved relativistic binary solution.

The library exposes `kerr_horizon_radius_rg` and `kerr_isco_radius_rg` for arbitrary mass scales. The existing `kerr_horizon_radius` and `kerr_isco_radius` functions retain their Sagittarius A* metre-based results for compatibility.

The [ACES curve fit](https://knarkowicz.wordpress.com/2016/01/06/aces-filmic-tone-mapping-curve/) is a compact approximation, not a full ACES colour-management transform. Skybox filtering wraps longitude across the seam and clamps latitude at the poles before tone mapping.

Run `cargo test` for physics and camera invariants, gravity timing checks at 30/60/120 rendering FPS, and WGSL parsing/validation.
