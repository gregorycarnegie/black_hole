# **black**_**hole**

[![Rust](https://img.shields.io/badge/Rust-2024-f74c00?logo=rust&logoColor=white)](https://www.rust-lang.org/)
[![Bevy](https://img.shields.io/badge/Bevy-0.18.1-232326?logo=bevy&logoColor=white)](https://bevyengine.org/)
![WGSL](https://img.shields.io/badge/WGSL-compute%20shader-005a9c)
![Status](https://img.shields.io/badge/status-experimental-yellow)

Real-time black hole visualization using GPU ray-tracing in Bevy (Rust).

Simulates null geodesics (light paths) in Schwarzschild spacetime around Sagittarius A*, with an accretion disk and a deformed spacetime grid.

## Features

1. **GPU ray-tracing** — compute shader integrates null geodesics using RK4 in Schwarzschild coordinates
2. **Accretion disk** — rays that cross the equatorial plane within the disk radius render as an orange glow
3. **Spacetime grid** — wireframe grid deformed by the Schwarzschild metric of each massive object
4. **N-body gravity** — optional Newtonian gravity simulation between scene objects

## Controls

| Input           | Action                |
|-----------------|-----------------------|
| Left mouse drag | Orbit camera          |
| Scroll wheel    | Zoom in/out           |
| G               | Toggle n-body gravity |

## Building

Requires [Rust](https://rustup.rs/) (stable).

```bash
git clone https://github.com/kavan010/black_hole.git
cd black_hole
cargo run --release
```

## How it works

`src/compute/pipeline.rs` sets up a Bevy render graph node that dispatches `assets/shaders/geodesic.wgsl` — a WGSL compute shader — every frame. The shader receives the camera position, accretion disk parameters, and scene objects via uniform buffers, then traces each pixel as a null geodesic through curved spacetime, writing the result to a storage texture that is displayed as a fullscreen sprite.

The spacetime grid is drawn each frame using Bevy's `Gizmos` API, with vertex Y-positions displaced by `2 * sqrt(r_s * (r - r_s))` (the Schwarzschild embedding).
