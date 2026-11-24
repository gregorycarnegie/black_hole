[![Rust](https://img.shields.io/badge/Rust-2024-f74c00?logo=rust&logoColor=white)](https://www.rust-lang.org/)
[![Bevy](https://img.shields.io/badge/Bevy-0.20.1-232326?logo=bevy&logoColor=white)](https://bevyengine.org/)
![CUDA](https://img.shields.io/badge/CUDA-PTX%20kernels-76b900?logo=nvidia&logoColor=white)
[![CI](https://github.com/gregorycarnegie/black_hole/actions/workflows/ci.yml/badge.svg?branch=main&event=push)](https://github.com/gregorycarnegie/black_hole/actions/workflows/ci.yml)
[![Lean verification](https://github.com/gregorycarnegie/black_hole/actions/workflows/verification.yml/badge.svg?branch=main&event=push)](https://github.com/gregorycarnegie/black_hole/actions/workflows/verification.yml)
[![Version tag](https://img.shields.io/github/v/tag/gregorycarnegie/black_hole?sort=semver&label=version)](https://github.com/gregorycarnegie/black_hole/tags)
![Status](https://img.shields.io/badge/status-experimental-yellow)

# **black**_**hole**

Real-time black hole visualization using GPU ray-tracing in Bevy (Rust).

Current version: **0.5.0**. See the [changelog](CHANGELOG.md) for release notes.

Simulates null geodesics (light paths) in Kerr spacetime in mass-independent gravitational units, with a default binary black-hole scene, an accretion disk, and a deformed spacetime grid.

## Features

1. **GPU ray-tracing** — one Cartesian Kerr–Schild Hamiltonian RK4 solver traces both single-hole and binary scenes, with analytic metric derivatives and a null-constraint check
2. **Accretion disk** — four switchable geometry presets (thin NT, truncated thin + hot flow, slim/super-Eddington, warped Bardeen-Petterson) with Kerr ISCO, frame dragging, Doppler beaming, and gravitational redshift
3. **Spacetime grid** — wireframe grid deformed by the Schwarzschild metric of each massive object
4. **Binary black holes** — equal-mass spinning black holes orbit a shared barycentre, with per-hole spin vectors in a frozen superposed Kerr–Schild metric and a circumbinary disk
5. **N-body gravity** — optional Newtonian gravity simulation using a fixed timestep, independent of rendering framerate
6. **Skyboxes** — a procedural checker grid plus bilinearly filtered equirectangular HDR space backgrounds sampled along each ray's lensed escape direction
7. **Polarized transfer** — transported polarization basis, Stokes I/Q/U/V, power-law synchrotron emission, scalar absorption, Faraday rotation and conversion, and selectable diagnostic views
8. **Filmic lighting** — an ACES curve approximation applied after combining disk and background lighting
9. **Wormholes** — CUDA ray tracing through an Ellis throat between two skies, plus an evolving Einstein–Rosen spatial embedding. Both have Lean-checked equations; the Einstein–Rosen bridge is nontraversable.

## Controls

Most settings are also buttons in the on-screen **CONTROLS** panel; the polarization settings are in the panel on the left.

### Keyboard / Mouse

| Input           | Action                                         |
|-----------------|------------------------------------------------|
| Left mouse drag | Orbit camera                                   |
| Scroll wheel    | Zoom in/out                                    |
| W               | Cycle black holes / ray-traced Ellis wormhole / Einstein–Rosen diagram |
| Left / Right    | In the Einstein–Rosen diagram: step Kruskal time by 0.05; pause |
| Space / R       | In wormhole modes: play/pause / reset dust time or Einstein–Rosen v to 0 |
| D               | Toggle the evolving test-dust emission in the Ellis wormhole |
| `[` / `]`       | Decrease / increase FOV                        |
| `-` / `=`       | Decrease / increase render scale (25 – 100 %)  |
| Q / E           | Decrease / increase Kerr spin, or selected binary-hole spin magnitude (±0.05) |
| 1 / 2           | Select binary black hole A / B for spin editing |
| Z / X           | Decrease / increase outer disk radius (±1 r_s) |
| M               | Cycle disk geometry preset                     |
| F               | Toggle spacetime grid                          |
| N               | Toggle binary black holes                      |
| G               | Toggle Newtonian n-body motion (moves the debug bodies; light bending is always on) |
| O               | Toggle debug bodies                            |
| B               | Cycle HDR skybox                               |
| `,` / `.`       | Decrease / increase max geodesic iterations    |
| H               | Toggle iteration-count heatmap                 |
| K               | Cycle the orbiting-body swarm: off, 256, 1024, 4096 bodies |
| P               | Cycle intensity, linear polarization fraction, EVPA, Q/I, U/I, V/I |

### Xbox Controller

| Input            | Action                                      |
|------------------|---------------------------------------------|
| Left stick       | Orbit camera                                |
| RT / LT          | Zoom in / out                               |
| A                | Cycle skybox                                |
| B                | Toggle binary black holes                   |
| X                | Toggle spacetime grid                       |
| Y                | Toggle iteration-count heatmap              |
| Select           | Toggle Newtonian n-body motion              |
| Start            | Toggle debug bodies                         |
| D-pad left/right | Select binary black hole A / B              |
| D-pad up/down    | Increase / decrease selected-hole spin a*   |
| Right stick      | Adjust selected-hole spin-axis X / Y        |
| RB / LB          | Increase / decrease selected-hole spin-axis Z |

## Running

### Requirements

- **An NVIDIA GPU with compute capability 8.0 or newer**, such as a GeForce RTX 30-series or later. The renderer runs CUDA kernels shipped as PTX compiled for `sm_80`. Older NVIDIA GPUs (RTX 20-series and earlier) and other vendors' GPUs cannot run the simulation; it stops at startup with `failed to initialize CUDA runtime`.
- **An NVIDIA driver with CUDA 12 support**, version 525 or newer. The driver loads the PTX directly, so you do not need the CUDA toolkit.
- **[Rust](https://rustup.rs/) 1.85 or newer** (stable), for the 2024 edition.
- Windows or Linux.

### Start the simulation

```bash
git clone https://github.com/gregorycarnegie/black_hole.git
cd black_hole
cargo run --release
```

Always use `--release`. Debug builds are too slow to ray-trace in real time. The first build takes a few minutes.

Run the simulation through `cargo run`, which tells Bevy where the `assets/` folder is. To launch the built binary (`target/release/black_hole`) yourself, first set `BEVY_ASSET_ROOT` to the repository folder. Otherwise the HDR skyboxes fail to load.

The window opens on a single Kerr black hole with a thin accretion disk. Drag with the left mouse button to orbit, and scroll to zoom. The **CONTROLS** panel on the right has a button for every setting; the keyboard and controller shortcuts are listed under [Controls](#controls). If the frame rate is low, lower **Render %** (`-`) or **Iterations** (`,`).

### Command-line options

Pass options after `--`, for example `cargo run --release -- --experiment-far-field`.

| Option | Effect |
|---|---|
| `--experiment-early-capture` | Single hole only: ends rays early once a proved Kerr test shows they will fall into the horizon. Faster, with the same exit classification. |
| `--experiment-far-field` | Single hole only: takes larger steps far from the hole and disk. |
| `--profile-renderer` | Runs a fixed benchmark and writes per-ray diagnostics to `target/renderer-rays*.csv`, then exits. |
| `--optix` | In an RTX build (below), starts with the RTX button on. |

[`RENDERING_PERFORMANCE.md`](RENDERING_PERFORMANCE.md) has the measurements behind the experiments.

### Optional: RTX (OptiX) build

The orbiting-body swarm (`K`, or the **Swarm** row) can also be traced with RT cores through NVIDIA OptiX. The normal build traces it with a software space-time BVH. That is just as fast in this scene, so the OptiX build is only needed for experimenting. It needs:

- the [OptiX 9.1 SDK headers](https://github.com/NVIDIA/optix-dev), with `OPTIX_ROOT` set to the folder that contains `include/optix.h`;
- [LLVM](https://releases.llvm.org/) for `libclang`, with `LIBCLANG_PATH` set to the folder that contains `libclang.dll` (Windows) or `libclang.so` (Linux).

```powershell
# PowerShell; on Linux use `export OPTIX_ROOT=...` instead.
$env:OPTIX_ROOT = "C:\path\to\optix-dev-9.1.0"
$env:LIBCLANG_PATH = "C:\Program Files\LLVM\bin"
cargo run --release --features optix
```

This build adds an **RTX** button to the panel, which switches the swarm between OptiX and the BVH while the simulation runs. OptiX starts the first time it is needed and reserves about 512 MB of GPU memory. If it cannot start, the simulation logs a warning and keeps using the BVH. The OptiX licence does not allow redistributing its headers, so they are not in this repository.

## Building and testing

See [CONTRIBUTING.md](CONTRIBUTING.md) for the checks a change must pass, the GPU tests, and how to regenerate the CUDA and OptiX PTX.

CI runs Rust lint and CPU tests on Linux and Windows and the Python verification tests on Linux. Lean proof changes trigger a separate build, axiom audit, and kernel replay. Pushing a `vX.Y.Z` tag that matches `Cargo.toml` publishes a GitHub source release after the Rust and Python checks pass.

## How it works

The renderer runs on CUDA. The kernels are written in Rust in `tools/cuda/kernels.rs` and compiled ahead of time to PTX (`src/compute/kernels.ptx`) by [cuda-oxide](https://github.com/NVIDIA/cuda-rust). At startup the app loads that PTX through the NVIDIA driver with [cudarc](https://github.com/coreylowman/cudarc). Each frame, `src/compute/pipeline.rs` uploads the camera, the Kerr and accretion-disk parameters and the scene objects. It then launches a kernel with one thread per pixel, which traces that pixel's ray through curved spacetime. `bh_accumulate` (`src/compute/accumulate.rs`) blends successive frames of a still camera, each jittered by a fraction of a pixel, for anti-aliasing and converts the result to 8-bit colour. The frame is then uploaded to the texture that Bevy shows as a fullscreen sprite.

Both modes use the same past-directed null geodesic solver in Cartesian ingoing Kerr–Schild coordinates. The covariant metric is `g = η + Σᵢ 2 Hᵢ lᵢ ⊗ lᵢ`; sequential rank-one inversion retains the cross terms of the combined metric. Each RK4 step evolves position, covariant momentum, and a parallel-transported screen vector using analytic spatial metric derivatives. Geometry and disk thickness limit the step; RK4 step doubling estimates position, momentum and screen errors; invalid stages or failed error/null checks trigger step halving. Horizon excision replaces the old enlarged shadow spheres. Rays that exhaust their iteration budget or fail numerical checks are dark, rather than incorrectly sampling the sky.

A single isolated term is the Kerr metric. Multiple terms are an **approximate frozen spacetime**, not an exact double-Kerr vacuum solution: positions and spins are held fixed during each ray trace, and boosts, retarded time, radiation, and relativistic orbital evolution are absent. The construction is suited to separated visual binaries; it is not validated for merger or overlapping strong fields. The Majumdar–Papapetrou alternative describes charged, nonrotating extremal holes and would not preserve this app's spinning neutral-hole scene.

The disk uses the same transfer path in both modes, with an inner cavity in binary mode. Select **Truncated** with `M` to expose its polarized hot flow. The left panel controls the Stokes view, observing frequency (30–1000 GHz), signed Faraday normalization, and conversion normalization. Thermal emission remains unpolarized. The hot component assumes an ordered toroidal field and power-law electrons with index `p = 3` (75% intrinsic linear polarization). Emission is shifted by the fluid-frame photon energy; Stokes intensities use the same frequency-cubed redshift factor. Exact constant-cell emission/absorption/rotation solutions compose in foreground-to-background order, so Faraday depth can depolarize emission and conversion can produce Stokes V.

These are **illustrative plasma coefficients in arbitrary units**. The temperature profile, density, magnetic field, and false-color spectrum are prescribed; scalar absorption omits dichroism, scattering, calibrated thermal synchrotron coefficients, and GRMHD input. The controls demonstrate frequency-dependent transfer, not a calibrated radio observation or an EHT research-grade model. RGB intensity remains a false-color image; polarization views show band-specific, pre-tone-map Stokes ratios. Linear fraction is grayscale (black 0%, white 100%); EVPA hue encodes the polarization angle modulo 180° and brightness the linear fraction. Q/I, U/I, and V/I use red for positive and blue for negative, with brightness equal to the absolute fraction. Unpolarized sky/background contributes to I and dilutes those fractions.

References: [Skylight's Kerr–Schild formulation and ray-tracing tests](https://academic.oup.com/mnras/article/515/1/1316/6631564), [Combi et al.'s more complete boosted binary metric](https://arxiv.org/abs/2103.15707), and [ipole's covariant polarized-transfer framework](https://arxiv.org/abs/1712.03057). This implementation is simpler than those research codes and has not been cross-validated against them.

In binary mode, the on-screen `BH` selector chooses which black hole is being edited. `Spin a*` changes that hole's spin magnitude, and the `Axis X/Y/Z` rows rotate its spin axis independently of the other hole.

The spacetime grid is drawn each frame using Bevy's `Gizmos` API, with vertex Y-positions displaced by `2 * sqrt(r_s * (r - r_s))` (the Schwarzschild embedding).

## Units and timing

The ray-traced Ellis view uses the metric and camera-to-sky construction in [James et al., *Visualizing Interstellar's Wormhole*](https://arxiv.org/abs/1502.03809), Eqs. (1), (2), (13), and (16). `W` enters this mode; drag to orbit, scroll to approach the throat, use `[` / `]` for field of view, and `B` to cycle pairs of skies. The first sky is the current background and the second is the next background in the list. Rays may cross the throat or turn back to their starting side. The CUDA renderer uses the existing temporal accumulation and tone mapping. Magenta identifies unresolved rays, including a narrow band around the critical photon orbit.

The Ellis throat radius is fixed at 4 scene-length units. These are arbitrary length units for this massless metric, rather than a gravitational radius defined by its mass. A pressureless test-dust pulse flows through the throat with coordinate speed -0.5c. Its density is an exact time-dependent solution of the relativistic continuity equation. The renderer samples its optically thin emission at retarded time, including the fluid-frame Doppler factor. Space pauses/resumes the flow, R rewinds it, and D hides/shows the matter. Geometry remains prescribed: supporting exotic matter, gravitational backreaction, pressure, magnetic fields, and stability are not evolved. [Ellis equations, proof coverage, and numerical tests](verification/ellis.md) document the implementation.

The bridge view follows [Collas & Klein, *Embeddings and time evolution of the Schwarzschild wormhole*](https://arxiv.org/abs/1107.4871), Eqs. (3), (5), (21), (22), and (24). Its two colors distinguish the two signed spatial sheets. Embedding height is an auxiliary Euclidean coordinate, not a physical travel direction. The original [Einstein & Rosen paper (1935)](https://doi.org/10.1103/PhysRev.48.73) motivates the two-sheet construction; this view uses the modern Schwarzschild/Kruskal extension. [Fuller & Wheeler (1962)](https://doi.org/10.1103/PhysRev.128.919) analyze its causal obstruction.

Bridge playback advances Kruskal coordinate time by 0.2 per application second and stops at v = 0.95. The finite display domain is |u| <= 32, |v| <= 0.95; the singular pinch at |v| = 1 and separated slices are excluded. The camera remains an external diagram viewer. See [the equations, proofs, and numerical checks](verification/einstein-rosen.md) for coverage and limitations.

Camera, objects, grid, Kerr radii, and GPU ray tracing use `G = c = M = 1`: distances are in gravitational radii `r_g = GM/c²`, and object masses are fractions of the total black-hole mass. The Schwarzschild radius is `2 r_g`; the UI continues to express disk radii in `r_s`. The same scene therefore represents a stellar-mass or supermassive black hole without changing shader constants.

To interpret a scene in SI units for any chosen mass `M`, multiply distances by `GM/c²`, velocities by `c`, and simulation times by `GM/c³`. Newtonian gravity advances one gravitational time unit per elapsed application second, using Bevy's fixed 64 Hz timestep. This is a visualization clock, not real-time SI playback. Binary motion remains a prescribed 18-second visual orbit and uses a frozen approximate binary metric, rather than an evolved relativistic binary solution.

The library exposes `kerr_horizon_radius_rg` and `kerr_isco_radius_rg` for arbitrary mass scales. The existing `kerr_horizon_radius` and `kerr_isco_radius` functions retain their Sagittarius A* metre-based results for compatibility.

The [ACES curve fit](https://knarkowicz.wordpress.com/2016/01/06/aces-filmic-tone-mapping-curve/) is a compact approximation, not a full ACES colour-management transform. Skybox filtering wraps longitude across the seam and clamps latitude at the poles before tone mapping.

Run `cargo test` for unit, `rstest` case and `proptest` property tests (physics, camera, simulation, uniforms and UI), and gravity timing checks at 30/60/120 rendering FPS. Certified arithmetic properties use exact rational oracles; GoogleTest matchers report interval bounds, error variants and enclosure tolerances without changing the numerical thresholds. Run `cargo mutants -j6` for mutation testing; exclusions are documented in `.cargo/mutants.toml`. Run `cargo clippy --all-targets -- -D warnings` for lint checks.

The [Lean 4 verification package](verification/README.md) checks Kerr metric derivatives, ISCO algebra and radial stability, camera frame identities, continuous transport, polarized cell transfer and error bounds, disk profiles, nine shared binary32 horizon executions, and selected RK4 error calculations. Run `lake build` inside `verification/`. The [results](verification/RESULTS.md) include GPU step-refinement measurements and counterexamples to exact binary vacuum curvature and Newtonian integrator energy conservation. The [remaining obligations](verification/OBLIGATIONS.md) distinguish proved formulas from source correspondence, numerical error bounds and physical calibration still required.

Run `cargo test headless_render -- --ignored --nocapture` on a machine with a supported NVIDIA GPU to run numerical checks **in the production CUDA kernels** (metric inverse/derivatives, spin reversal, null initialization, Schwarzschild capture/escape, screen transport, and analytic Stokes/Faraday solutions), then render single/binary intensity and polarization scenes. Preview PNGs are saved under `target/render-smoke-*.png`. This small-resolution regression does not establish production-resolution performance or scientific accuracy.
