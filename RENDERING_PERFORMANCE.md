# Rendering performance experiments

The first optimization reuses metrics and the initial derivative inside RK4. Consider RT hardware if geometry queries become a measurable part of frame time.

## What the renderer does today

- **CUDA compute.** The renderer loads PTX and launches one thread per pixel. The Kerr kernel traces a backward null geodesic, integrates emission and absorption along it, and samples the background sky on escape. There are no RT-core calls or BVHs in this path. [CUDA module](src/compute/cuda.rs#L62) · [Kerr render kernel](tools/cuda/kernels.rs#L2091)
- **Direct geometry checks.** Each accepted step tests the straight segment between its endpoints against the object spheres in array order. The usual scenes contain one or two black holes, with optional debug bodies and a GPU limit of 16 bodies. The disk uses radial and vertical bounds to reject samples outside the plasma. The metric and its derivatives still sum contributions from every positive-mass source at each evaluation. A geometry bound gives no error bound for dropping a source's gravitational contribution. [Scene construction](src/simulation.rs#L283) · [Object limit](src/compute/mod.rs#L478) · [Sphere tests](tools/cuda/kernels.rs#L1686) · [Disk bounds](tools/cuda/kernels.rs#L1891) · [Metric evaluation](tools/cuda/kernels.rs#L1281)
- **Existing optimizations.** The step controller grows steps away from the holes and limits them near the disk. The loop stops on capture, failed or stagnant integration, escape, or low transmission. Thermal intensity has a fast path that skips magnetic-field and polarization calculations in plasma sampling. The previous CUDA optimization measured roughly **88 → 43 ms at 400×300** and **198 → 98 ms at 960×540** for disk tracing on an RTX 4090. [Step and termination logic](tools/cuda/kernels.rs#L2131) · [Thermal fast path](tools/cuda/kernels.rs#L1920) · [Recorded timings](https://github.com/gregorycarnegie/black_hole/commit/8f38a9f36e6e0d59334559dcff8e8339168ba365)

## RK4 measurements

RTX 4090, driver 621.01, checked-in CUDA PTX, and 16×16 blocks. Each row is the median of 30 CUDA-event measurements after three warm-up launches. The fixed camera used a 60° vertical field of view and spin 0.82. The standard view used a camera radius of 48 gravitational radii and an elevation of 0.35 radians. The close heatmap used a radius of 24 and an elevation of 0.1, with the hot-flow disk and EVPA shading underneath.

| Scene | Size | Before (ms) | Reuse endpoints (ms) | Reuse endpoints and initial derivative (ms) |
|---|---:|---:|---:|---:|
| Single hole, thin disk intensity | 400×300 | 183.1 | 165.2 | 159.0 |
| Binary, thin disk intensity | 400×300 | 41.3 | 35.3 | 35.2 |
| Binary, thin disk intensity | 960×540 | 99.6 | 85.2 | 91.2 |
| Single hole, hot flow EVPA | 400×300 | 181.6 | 164.8 | 152.8 |
| Single hole, close heatmap | 400×300 | 253.2 | 229.6 | 221.1 |

CUDA accumulation medians were 0.008–0.026 ms in the baseline. Copying the RGBA8 buffer to the host after CUDA completion took 0.088–0.232 ms. The windowed profile below measures total frame intervals. In the close heatmap, the median ray used 130 outer iterations, the 99th percentile used 4,847, and the longest reached the 10,000 cap. The baseline and optimized heatmaps matched exactly.

All tested images had identical RGBA8 output after quantization, including a close-up with a patterned sky. The final variant changed 14 and 29 pixels before quantization in two EVPA images. The largest channel difference was 5.96 × 10⁻⁸. The initial derivative reuse was faster in the expensive single-hole views. The larger binary view favored endpoint reuse alone in this run, and a later run with the shared derivative measured 83.7 ms.

### CUDA block shape

A second sweep used the optimized kernel with several two-dimensional launch shapes. At 400×300, 32×4 reduced the median trace time from 159.0 to 125.7 ms for single-hole thin-disk intensity and from 159.4 to 123.1 ms for single-hole hot-flow EVPA. The 960×540 binary case favored 16×16 in the repeat run. The renderer now selects 32×4 only for single-source Kerr scenes. A warp traces neighboring pixels along one row in that configuration. [Launch configuration](src/compute/pipeline.rs#L356)

The final comparison ran 20 timed samples per scene after three warm-ups and used the production launch shape for each variant. All four RGBA8 buffers from the production accumulation kernel matched byte for byte.

| Scene | Size | Before median / p95 (ms) | After median / p95 (ms) | Median reduction |
|---|---:|---:|---:|---:|
| Single hole, thin disk intensity | 400×300 | 183.7 / 186.7 | 122.8 / 141.3 | 33% |
| Binary, thin disk intensity | 400×300 | 41.5 / 44.3 | 34.7 / 36.6 | 17% |
| Binary, thin disk intensity | 960×540 | 99.5 / 100.3 | 82.9 / 83.7 | 17% |
| Single hole, close hot-flow EVPA with patterned sky | 400×300 | 252.8 / 256.6 | 185.7 / 202.2 | 27% |

The CUDA driver reported 255 registers per thread for both builds. Local memory per thread increased from 456 to 704 bytes. The headless Bevy render and the CUDA regressions passed, including all 256 near-critical classification cases. `lake build BlackHole.CudaGeodesic` also passed.

The separate EHT snapshot benchmark reused the accepted endpoint metric for screen transport and its null diagnostic. Its 25,600-ray output buffer matched the baseline bit for bit, with 990 captured and 24,610 escaped. Median CUDA kernel time went from 626.1 to 546.2 ms across five timed launches after warm-up. [Snapshot benchmark](tests/common/image.rs#L5)

## Slow-ray profile

Run `cargo run --offline -- --profile-renderer` to repeat the windowed test. It opens an 800×600 window with the default 50% render scale, requests presentation without vsync, and uses one Kerr hole at spin 0.82 with a hot-flow disk and EVPA view. The camera is 24 gravitational radii out and 0.1 radians above the equator. The two phases each discard 12 warm-up frames and time 60 intervals between application frames. The orbit advances by 0.01 radians per frame. After timing, the one-shot diagnostic re-traces the initial pose without jitter, writes `target/renderer-rays.csv`, and closes the window. These results are from the optimized dev build on the RTX 4090. [Profile runner](src/compute/profile.rs#L60)

| Camera | Median windowed frame interval | p95 |
|---|---:|---:|
| Still | 193.75 ms | 227.36 ms |
| Orbiting | 188.95 ms | 220.73 ms |

The trace covered 120,000 rays. All diagnostic image channels matched the ordinary kernel in this view. The median ray took 130 outer iterations, p95 took 2,892, and p99 took 4,842. Eighteen hit the 10,000-iteration cap.

- The slowest 5% accounted for **56.8% of all accepted steps**. They spent **98.8% of their steps within one gravitational radius of the horizon**, with zero far-field steps. Disk and controller limits together set the proposed step on just 1.2% of their accepted steps. The geometric step limit set the rest.
- **7,524 rays ended at affine stagnation**, when adding the accepted step no longer changed the binary32 affine sum. Those rays accounted for 65.3% of all accepted steps. In the slowest 1%, 1,182 rays stagnated and the other 18 reached the cap. Of all rays, 112,278 escaped, 151 reached the current horizon cutoff, and 29 stopped on opacity.
- Across the frame, 28.1 million of 42.9 million accepted steps began within one gravitational radius of the horizon. Far-field steps, starting at least 64 gravitational radii from the origin, accounted for 14.3%. The controller rejected 80,317 proposals, about 0.19 rejections per 100 accepted steps. Step counts show where the work accumulates. Per-step costs and GPU scheduling determine the corresponding time.

Affine stagnation alone gives no capture verdict. The experiment below checks the Kerr radial potential and the plasma support before ending a ray. [Near-critical GPU checks](tests/common/controller.rs#L150)

## Single-Kerr early capture (default)

**Default since 2026-11-25 (checklist P0.3).** Every render kernel tries early capture, and the kernel guard decides per scene. `--full-trace` (experiment bit 0) turns it off; with `--profile-renderer` it saves `target/renderer-rays-full-trace.csv`. On the windowed close-up with Dormand–Prince, the still and orbit medians are 19.5 / 17.6 ms (two runs: 19.52 and 19.46, 17.59 and 17.58), against 91.3 / 91.7 ms with `--full-trace`. These runs predate the finite-precision certificate described below, which brings them to about 20 / 18 ms. Still-camera p95 varied between 27 and 49 ms across the two runs; orbit p95 was 18.1–18.7 ms.

The re-profiled close-up: accepted steps fall from 42.80M to 15.04M, near-horizon steps from 28.13M to 0.37M, and disk-limited steps stay at 6.39M. Iterations per ray: median 121, p95 160, p99 199, maximum 1,393 (full trace: 129, 2,888, 4,844, 10,000). The slowest 5% now account for **7.8% of accepted steps** (56.9% with the full trace). 18.0% of their steps are near the horizon and 36.0% are disk- or controller-limited; 5,390 of those 6,000 rays escape. Disk-limited plasma steps are now the largest remaining workload. Exits: 112,271 escaped in both modes. The full trace's 7,524 affine stagnations, 152 horizon cutoffs and 17 iteration caps become 7,692 early captures and one extra `near_critical` (8 against 7); both give a black pixel, and the images match bit for bit.

`early_capture_matches_the_full_trace` (`src/compute/pipeline.rs`) renders 160×120 images with and without bit 0 at spins 0, ±0.82, ±0.99, ±0.995 and 0.999. Each spin runs every disk model (thin, truncated hot flow, slim funnel, warped), cameras near the pole and 0.1 rad above and 0.5 rad below the disk plane, and intensity, EVPA and circular-polarization views. It also renders the binary. Every pair is bit-identical. Spins 0 to ±0.995 each early-capture about 39,000–46,000 rays across their views; 0.999 and the binary early-capture none. For four early-captured pixels per intensity view, it traces the GPU's initial state in binary64 RK4 on the CPU Kerr field; none of the 336 escapes. `swarm_early_capture_matches_the_full_trace` requires the same identity for brute force, the BVH and OptiX at 256, 1,024 and 4,096 bodies. Swarm bodies orbit at 12 gravitational radii or more, outside the largest ISCO (9), so the swarm never lies inside the capture radius. The equatorial potential test now includes spins ±0.995 (438 of 801 rays early-captured, none with an exterior turning point).

The sections below describe the guard and the measurements from when it was the opt-in `--experiment-early-capture` with RK4. The guard applies to an origin-centered, unit-mass Kerr source with an aligned disk, a black surface, and absolute spin at most 0.995. [Kernel guard](tools/cuda/kernels.rs#L2037)

The guard tests the inward radial tangent and the energy-normalized potential `R(s) = P(s)² − Δ(s)K`, where `P(s) = s² + a² − aλ`, `λ = L/E`, and `K = Q/E² + (λ − a)²`. Over the interval from the outer horizon `h` to the current radius `r`, `P(s)` and `Δ(s)` are increasing. When `P(h)` is positive, `P(h)² − Δ(r)K` is a lower bound for `R(s)`. The GPU checks this bound with an explicit margin in binary64 and checks the local radial equation against the integrated tangent. If a check fails, it tries again once the clearance has halved. A ray must also be below the disk's inner radius by a guard margin. The projected disk radius stays below the Kerr radius, so a monotonically inward exact ray adds zero prescribed emission or absorption. Lean proves the real-arithmetic inequalities.

**Finite precision (2026-11-25).** The round-to-nearest binary64 guard is now only a filter. A ray it accepts must also pass `kerr_capture_certified`, which re-evaluates the hypotheses in interval binary64. Each operation uses an explicit `_rn` intrinsic, so nothing is contracted into an FMA, and then steps one ulp outward. Every decision therefore holds for the exact real values of the stored binary32 state: r is strictly between the horizon and the disk's inner radius, P(h) > 0, and P(h)² − Δ(r)K > 0. The inward tangent is now computed from the state's own momentum, Σ dr/dλ through g⁻¹ = η − 2h ℓ♯ℓ♯ᵀ, which is exact for the null ℓ, instead of from the binary32 velocity. The certificate runs once per captured ray. Inlining the guard into the render loop cost about 0.8 ms per frame, so it is kept out of line. In alternating windowed runs, the still/orbit medians are 19.9–20.2 / 18.2 ms against 19.6–19.7 / 17.8–18.1 ms without the certificate, about 2%. Every capture decision, step count and image is unchanged.

`black_hole::certified::capture_certified` evaluates the same hypotheses on the CPU with the exact-dyadic-checked `Interval`. `the_capture_guard_is_certified_on_the_cpu` runs the full GPU guard on 20,000 random null states per spin, at spins 0, ±0.5, ±0.9 and ±0.995. The states have random Kerr radii up to 3.9, polar angles with sine above 0.12, and inward-biased momenta. All 20,129 GPU captures are certified on the CPU, and 545–743 more states per spin are certified only on the CPU, where the GPU's margins reject them. The equatorial potential test also certifies its 3,241 GPU captures on the CPU.

What remains outside proof: the stored binary32 state differs from the exact ray by the integration error, as for every other exit. IEEE 754 round-to-nearest is assumed. The identity linking the Kerr-Schild Cartesian state to λ, K and R(r) is a standard Carter separation, but it is not in Lean. It is checked numerically by the guard's consistency test (Σṙ)² ≈ R and by the equatorial analytic test. [Separated Kerr null geodesics](https://arxiv.org/abs/1910.12881) · [Lean bounds](verification/BlackHole/KerrCapture.lean)

The first version checked the bound once. It reduced accepted steps from 42.9 million to 24.1 million in the fixed polarized close-up, while kernel time stayed around 185 ms. The 18 rays that reached the original step cap still did so. Retrying the same bound at tighter radial intervals reduced the workload to **15.1 million steps** and the ray kernel from **190.2 ms to 30.9 ms** in the repeated 400×300 test with a patterned sky. All **112,278** escaping pixels kept the same exit classification. All 7,693 early exits replaced a horizon cutoff, affine stagnation, or iteration cap. The floating-point image and the packed RGBA8 output both matched exactly in that case.

The windowed A/B used the same RTX 4090, close-up, 400×300 internal render, and 60 timed frames per phase. The diagnostic image matched its respective normal kernel exactly in both runs.

| Camera | Full trace median / p95 | Early capture median / p95 |
|---|---:|---:|
| Still | 191.14 / 229.04 ms | 38.56 / 54.88 ms |
| Orbiting | 195.36 / 224.61 ms | 36.32 / 37.84 ms |

All seven fixed-camera image pairs matched in both floating-point and RGBA8 output. These included spins ±0.82 and 0.99, thin-disk intensity, hot-flow EVPA, warped-disk circular polarization, and the binary and spin-0.999 fallback cases. The GPU regression also exercised 4,005 equatorial Kerr rays at five spins, checked early captures against the exterior minimum of the analytic equatorial potential, and checked 256 near-critical Schwarzschild rays with each mode. [GPU trajectory tests](tests/common/controller.rs#L150)

## Experimental far-field steps

`cargo run --offline -- --experiment-far-field` enables far-field steps on top of the default early capture. For the benchmark, add `--profile-renderer` and run once with and once without `--experiment-far-field`. Compare `target/renderer-rays-far-field.csv` and `target/renderer-rays.csv`. (The measurements below predate the default and used `--experiment-early-capture`.) Each per-pixel row now includes the number of enlarged steps and the direction used to sample the sky on an escape.

The larger steps start outside a padded sphere enclosing the disk's radial and vertical support and the central object. The ray must point outward with radial cosine above 0.95. The proposal is capped at 28% of the current radius and 192 gravitational radii, with the ordinary cap restored near the 1,600-gravitational-radius sky sampling sphere. The existing RK4 checks still control acceptance. If the proposal fails or its accepted chord heads inward, the renderer retries with the ordinary proposal. Lean proves that an exact chord with a nonnegative radial dot product remains outside its starting sphere. [CUDA guard](tools/cuda/kernels.rs#L2037) · [Outward-chord proof](verification/BlackHole/KerrCapture.lean)

In the 400×300 polarized close-up, accepted steps went from **15.14 million to 11.23 million** and far-field steps went from **6.12 million to 2.22 million**. All 120,000 exit classifications matched. The sampled sky direction shifted by at most 0.39 microradians in the windowed comparison, relative to the ordinary trace. The fixed-camera patterned-sky EVPA output matched at RGBA8 precision.

Several 30-sample CUDA repeats put the close-up ray kernel near 30 ms for early capture alone and for early capture with widened steps. Skipping the disk and object checks on the verified vacuum chords and raising the cap again to 384 gravitational radii also timed near 30 ms. That version changed 21 RGBA8 channels by one byte in the close-up. The retained version keeps the ordinary disk and object checks.

In the windowed close-up, four back-to-back runs measured wide, ordinary, ordinary, then wide. Each run timed 60 frames per camera phase after warm-up. The ranges below show the two median measurements per mode.

| Camera | Early capture alone | Early capture and far-field steps |
|---|---:|---:|
| Still | 39.48–39.74 ms | 38.91–39.71 ms |
| Orbiting | 36.10–36.28 ms | 35.94–36.24 ms |

The distant warped-disk view at camera radius 160 improved from about **11.6 ms to 10.2 ms** in the ray kernel at 400×300. The spin-0.99 close-up ran at 167.7–168.6 ms with early capture alone and 171.5 ms with wider steps in the fixed-camera sweep. Across four fixed-camera views, the maximum direction shift was 0.72 microradians and every exit classification matched. The thin-disk and distant warped-disk images each had a few RGBA8 channels change by one level. Both fixed-camera EVPA images matched at RGBA8 precision. These comparisons measure the change against the existing renderer's sampled direction. The project's absolute error target still calls for an independent reference. [Accuracy targets](verification/TARGETS.md#L24)

The standard polarized close-up still executes 6.31 million disk-limited steps. Those are 56% of the remaining accepted steps with both experiments enabled.

### Cheaper plasma samples

About 5 million of those disk-limited steps sample plasma. A trial that merged two geodesic steps inside the disk while keeping two transfer samples cut accepted steps by about 13%. It ran slower, and some near-critical rays sampled noticeably different parts of the sky, so it was dropped.

The retained change keeps every step and removes work inside each sample. The plasma sampler and the RK4 endpoint validity check only read the metric, its inverse, the clearance, and the validity flag. They now call a metric evaluation that skips the three derivative matrices. The controller also hands the accepted endpoint metric back to the renderer instead of recomputing it. These quantities are computed outside the derivative branch, so their values are unchanged. [Metric without derivatives](tools/cuda/kernels.rs#L1293) · [Plasma sample](tools/cuda/kernels.rs#L1941)

The 400×300 polarized close-up ray kernel went from about 30.5 ms to 28–29 ms with both experiments enabled. Every exit, sky direction, Stokes value, and RGBA8 pixel matched bit for bit. The floating-point and RGBA8 buffers also matched for disk models 0, 1, and 3, polarization views 0, 2, and 5, and the binary thin-disk scene.

The windowed A/B swapped the checked-in PTX between runs in new, old, old, new order, with the same close-up and 60 timed frames per phase. The ranges show the two median measurements per kernel.

| Mode | Camera | Before | After |
|---|---|---:|---:|
| Default | Still | 176.59–180.44 ms | 176.52–177.89 ms |
| Default | Orbiting | 175.62–176.15 ms | 177.03–177.60 ms |
| Both experiments | Still | 34.51–34.73 ms | 31.68–32.34 ms |
| Both experiments | Orbiting | 31.63–31.68 ms | 28.54–28.76 ms |

With both experiments enabled, the change saves about 3 ms per frame. The default renderer shows no difference beyond run-to-run noise, because its close-up frame is dominated by near-horizon steps rather than plasma samples. Codex's earlier experiment timings of 36–40 ms came from a separate session, so they overstate the gain when compared with these results.

## Dormand–Prince controller (default)

**Default since 2026-11-25 (checklist P1.1b).** Every render kernel uses it, including binaries, the swarm, OptiX and diagnostics. `--rk4-controller` restores the step-doubling RK4 controller for one release. RK4 now runs in `bh_geodesic_experiments` (1,128 local bytes), so it is slower than it was as the default. On the windowed close-up (`--profile-renderer`, two alternating runs each) the still and orbit medians are 92.0 / 91.7 ms and 92.5 / 91.7 ms by default, against 194.4 / 193.4 ms and 194.2 / 197.3 ms with `--rk4-controller`. The p95 values are 101–103 ms and 231–232 ms. The default `bh_geodesic` needs 255 registers and 328 local bytes. In `dp45_controller_benchmark` it takes 66.6, 77.0, 17.9 and 39.4 ms for the four scenes, about half of the old RK4 `bh_geodesic` (125.1, 148.0, 32.5 and 77.6 ms). The EHT snapshot test now writes the default image to `image-gpu.f32` and the RK4 one to `image-gpu-rk4.f32`.

The measurements below were taken while DP45 was still the opt-in `--experiment-dp45`, so "none" in their tables means RK4. The controller replaces the step-doubling RK4 controller with an embedded Dormand–Prince 5(4) step that advances the fifth-order solution. The stages form the error estimate directly, so binary32 rounding of the two end states does not hide it. A step accepted on the first try costs 6 `scene_metric` evaluations inside the controller instead of 11. It does not reuse the last stage as the next step's first stage, because the renderer rewrites the screen vector between steps and the endpoint metric is already reused. Validity, null-constraint, stagnation and retry rules are unchanged, as is `STEP_TOLERANCE`. [Controller](tools/cuda/kernels.rs#L1653) · [Tableau proof](verification/BlackHole/DormandPrince.lean)

Measured on 2026-11-24 with `--profile-renderer`, release build, RTX 4090, alternating runs:

| Flags | Still median / p95 (ms) | Orbit median / p95 (ms) |
|---|---:|---:|
| none | 174.8 / 206.2, 177.2 / 205.6 | 179.9 / 209.0, 173.3 / 196.2 |
| `--experiment-dp45` | 118.2 / 134.4, 118.4 / 129.9 | 117.2 / 134.4, 117.8 / 135.0 |
| `--experiment-early-capture` | 33.1 / 39.5 | 30.3 / 31.9 |
| early capture + DP45 | 23.9 / 30.7 | 22.1 / 23.9 |

Accepted steps fell by only 0.2% (42.90M to 42.80M), and rejected attempts by 6%. The gain comes from cheaper steps, not longer ones. The geometric step limit, not the error tolerance, sets most steps. Across the 120,000 diagnostic rays, two changed their exit class: one went from affine stagnation to horizon, and one from the iteration limit to affine stagnation. No ray moved between escape and any other class. For rays that escaped both times, the sky-direction difference had a median of 1.7e-7 rad, a 99th percentile of 3.8e-6 rad, and a maximum of 0.075 rad. Stokes I differs by 0.38% in relative L2. Seven pixels differ by more than 0.1% of peak intensity, and two by more than 10%. Those two are grazing rays at (183, 112) and (196, 103). Without an independent reference, that comparison cannot say which controller is right.

In the binary64 Schwarzschild trajectory test, DP45 cut the near-critical errors about threefold. At impact 5.3 the position error went from 1.646e-3 to 5.70e-4 and the momentum error from 1.500e-5 to 5.12e-6. At 5.25 the position error went from 1.584e-3 to 5.62e-4. Both still miss the target. Impact 10 rose from 1.87e-5 to 4.16e-5 and stays within its 9.88e-5 target. Impact 30 was unchanged. [Trajectory test](tests/common/controller.rs#L85)

`dp45_controller_benchmark` times `bh_geodesic` against `bh_geodesic_experiments` with only DP45 enabled. It uses CUDA events, alternates launches, and takes 20 samples after three warm-ups. It uses the default camera, a 2×1 sky and thermal intensity. Run it with `cargo test --release --bin black_hole -- --ignored dp45_controller_benchmark --nocapture`. [Benchmark](src/compute/pipeline.rs#L1295)

| Scene | RK4 median / p95 (ms) | DP45 median / p95 (ms) | Pixels differing by more than 1/255 | Largest channel difference |
|---|---:|---:|---:|---:|
| Single hole 400×300 | 124.6 / 152.4 | 83.6 / 90.8 | 0 | 0.002 |
| Single hole 960×540 | 154.2 / 172.8 | 102.3 / 111.3 | 0 | 0.004 |
| Binary 400×300 | 33.3 / 33.5 | 23.4 / 23.7 | 1 | 0.008 |
| Binary 960×540 | 80.3 / 81.2 | 53.0 / 53.8 | 3 | 0.019 |

The driver reports 255 registers for both kernels. Local memory is 704 bytes per thread for `bh_geodesic` and 1,128 bytes for `bh_geodesic_experiments`. That kernel also carries the early-capture and far-field code. A build of `bh_geodesic` with DP45 alone (not kept) needs 255 registers and 320 bytes of local memory, under half the RK4 kernel's 704. On the same run it took 62.6, 76.3, 17.6 and 38.9 ms for the four scenes in the table, against 125.1, 148.0, 32.5 and 77.6 ms for RK4 and 80.5, 102.2, 22.8 and 51.5 ms for DP45 in the experiments kernel. Its images matched the experiments kernel's DP45 images exactly. So a DP45 default would halve the frame time, and the stage sums need no restructuring for local memory.

The EHT snapshot test traces its gauged path with both controllers. At the time it wrote `image-gpu.f32` (RK4) and `image-gpu-dp45.f32`. Compare each with `check_image.py compare --image <file>`. Both resolve every ray (990 captured, 24,610 escaped). Against the refined Zig reference, Stokes I L2 error is 0.719% for RK4 and 0.704% for DP45. The worst I error is 2.75% and 2.87% of the reference peak. The worst relative I error above the floor is 24.27% for both. The maximum null residual is 4.06e-5 and 2.37e-5. The Q, U and V L2 errors are within 0.0001 of each other. Path error does not dominate this image's error. A single launch of each took 711 ms (RK4, run first) and 431 ms (DP45). That is not a controlled timing. The recorded RK4 median is 546 ms.

`dp45_disagreements_against_a_binary64_reference` traces the 16 close-up pixels where the controllers' escape directions differ most. It uses binary64 RK4 on the CPU Kerr field (`certified::Kerr`), starting from the GPU's own initial state. Halving the reference step changed directions by at most 9e-8 rad. The two image outliers top that list. At (196, 103) the error against the reference is 9.1e-2 rad for RK4 and 1.6e-2 for DP45; at (183, 112) it is 2.1e-2 and 4.1e-3. DP45 is closer at 13 of the 16 pixels. Four ordinary pixels agree with the reference to 3e-7 rad under both controllers.

The near-critical classification regression (256 consecutive binary32 impacts around the Schwarzschild critical value, run twice) blocks a default switch as written. RK4 gives zero wrong resolved answers, and DP45 gives 2 per run, all within 1.2e-7 of the critical margin. RK4's zero is not robust, though. Changing the geometric step factor from 0.12 to 0.11 or 0.13 gave RK4 5 and 9 wrong answers per run, against 1 and 2 for DP45. Tightening the DP45 tolerance to 1e-8 or 2e-9 did not help: more steps meant more binary32 rounding, and impact 5.25 rose to 2.9e-3 position error at 2e-9. Neither controller reliably ended near-critical rays as unresolved, so DP45 stayed opt-in until an unresolved band (checklist P1.6) could cover both.

### Unresolved band

A ray that ends captured or escaped after sweeping more than `UNRESOLVED_WINDING` = 14 rad around the origin now ends unresolved. It gets no sky, as at the iteration limit, and the diagnostic exit `near_critical`. Close to the photon sphere the swept angle grows like −ln|margin|: in the test, escapes sweep about 3.3 − ln|margin| and captures about 2.0 − ln|margin|. So the band is about |margin| < 6e-5 for escapes and 1.5e-5 for captures. Unlike a margin computed from conserved quantities, the swept angle is measured on the computed path itself. A wrong answer means that path's effective margin crossed zero, so the ray must have wound a long way. Before the band, every wrong answer from either controller at step factors 0.11–0.13 had swept at least 16.1 rad, about a factor of 8 in margin inside the band. [Band](tools/cuda/kernels.rs) · [Test](tests/common/controller.rs)

The classification test now runs both controllers at step factors 0.11, 0.12 and 0.13, with and without the disk inner edge (early capture), on the 256 binary32 impacts around the critical value plus 256 impacts from 4 to 6.5. It requires zero wrong definitive answers and resolution of every ray with |margin| > 1e-4. Both pass. Each run leaves 147–163 of the 512 rays in the band, depending on controller, step factor and disk edge, and the closest definitive answers have |margin| between 4.2e-6 and 7.2e-6. In the `--profile-renderer` close-up the band takes 7 of 120,000 pixels for both controllers, including both earlier outliers, (196, 103) and (183, 112). Frame times and local memory are unchanged. The band is calibrated on the single hole at the origin. In a binary the winding is still measured about the origin, so it is not calibrated there.

`swarm_dp45_timing` times the swarm with and without DP45. It uses the default 400×300 view, alternating launches, and the median of five after one warm-up. OptiX frames include the host GAS build. With DP45, the BVH and OptiX images still match brute force bit for bit at 256 and 1,024 bodies. Run it with `cargo test --release --features optix --bin black_hole -- --ignored swarm_dp45_timing --nocapture`; without the feature it times the BVH only. [Benchmark](src/compute/pipeline.rs#L1208)

| Bodies | BVH RK4 | BVH DP45 | OptiX RK4 | OptiX DP45 |
|---:|---:|---:|---:|---:|
| 0 | 119.1 ms | 78.9 ms | — | — |
| 256 | 131.8 ms | 86.3 ms | 164.1 ms | 110.5 ms |
| 1,024 | 140.4 ms | 90.4 ms | 171.9 ms | 102.8 ms |
| 4,096 | 155.2 ms | 86.7 ms | 171.0 ms | 121.2 ms |
| 16,384 | 144.8 ms | 93.9 ms | 211.6 ms | 161.0 ms |

DP45 saves 34–44% with the BVH and 24–40% with OptiX. The BVH times leave out its host rebuild, which the table above puts at up to 75 ms.

## Structured metric contractions (default)

**Default since 2026-11-25 (checklist P1.3).** `Metric` now holds only g, g⁻¹, the clearance and a validity flag. The three 4×4 derivative matrices are gone. `geodesic_rhs` builds each Kerr–Schild source's contributions to k·∂ᵢg·k and to the screen transport directly from h, ℓ, ∂h and the derivatives of ℓ along k and f (`source_terms`). The sum over sources is the derivative of the superposed metric, and g⁻¹ stays the generic Sherman–Morrison update, so binaries are handled exactly as before. With one or two holes, `metric_and_rhs` computes each source once and uses it for both the metric and the right-hand side. Its metric has the same bits as `scene_metric`. The DP45 step no longer evaluates the endpoint metric twice. The matrix form survives as `geodesic_rhs_matrix`, behind `MetricJet`, for the diagnostics and the proved fixture. [RHS](tools/cuda/kernels.rs) · [Identity](verification/BlackHole/CudaStructuredRhs.lean)

How it was built matters for the timings. The first version recomputed every source inside `geodesic_rhs` and inlined it into every stage. It was 30% slower (close-up 26.0 / 24.2 ms), even though it had fewer registers and no local memory. Moving the right-hand side back behind a device call recovered most of that. Computing each source once per stage made it faster than the matrix form.

Close-up, `--profile-renderer`, two alternating runs each, still / orbit medians: 19.9 / 18.2 and 20.2 / 18.3 ms before, 18.3 / 16.8 and 18.6 / 16.9 ms after (about 8%). `dp45_controller_benchmark`:

| Scene | DP45 before (ms) | DP45 after (ms) | RK4 before (ms) | RK4 after (ms) |
|---|---:|---:|---:|---:|
| Single hole 400×300 | 14.4 | 13.0 | 30.3 | 27.1 |
| Single hole 960×540 | 26.9 | 23.8 | 59.8 | 49.0 |
| Binary 400×300 | 17.6 | 16.2 | 35.1 | 35.1 |
| Binary 960×540 | 38.7 | 34.5 | 84.1 | 76.8 |

`bh_geodesic` local memory falls from 344 to 184 bytes per thread at 255 registers, and `bh_geodesic_experiments` from 1,128 to 464. Images: every GPU image and controller test passes unchanged, including bit-identical early capture, swarm BVH and OptiX against brute force, the EHT snapshot and the controller classification.

`structured_geodesic_rhs_matches_the_matrix_form` compares, for 4,096 random states each on a spinning single hole (a = 0.9) and a tilted-spin binary, the structured and fused forms with the matrix form. Each output group is scaled by the size of its terms, as `absEval` is for the proved bound. The worst difference is 3.1e-7 (single) and 2.1e-7 (binary), against a limit of 1e-5. On the single hole, all three forms meet the binary64 `certified::Kerr` right-hand side to 8.0e-7 (matrix), 9.2e-7 (structured) and 8.6e-7 (fused), against 1e-4. `CudaStructuredRhs.lean` proves over ℝ that one source's structured terms equal its matrix contractions; both are linear in ∂g. The structured form's binary32 rounding has no proved bound. The proved 3e-4 bound (`CudaGeodesic.geodesic_rhs_exact_inputs`) now covers only `geodesic_rhs_matrix`.

## Experiment order

1. **Measure the interactive frame.** Fix the camera, spin, disk preset, pixel dimensions, and render mode for each comparison. Start with single-hole thermal intensity, then compare polarized or synchrotron-heavy rendering and the binary scene. Include a view with a prominent photon ring and measure the Ellis kernel separately if the wormhole view is slow. Record median and 95th-percentile frame times after warm-up. Time the geodesic and accumulation kernels with CUDA events. Measure the host wait/readback, Bevy texture upload, and total frame time separately. Use the `H` heatmap to locate long rays and count rejected attempts separately from outer iterations. If a few long-running rays dominate, check warp divergence, register pressure, and spills before changing block size or splitting up the ray work. [Existing CUDA-event example](tests/common/gpu.rs#L229) · [Kernel dispatch](src/compute/pipeline.rs#L356) · [Display path](src/compute/accumulate.rs#L156)
2. **Reuse RK4 work.** The controller takes one coarse RK4 step and two half-steps. Reusing the first half-step and fine endpoint metrics cuts the source-level `scene_metric` count from **15 to 12** for an interactive step accepted on the first try, excluding the incoming metric and any plasma sample. The coarse step, first half-step, and every retry share one initial right-hand-side evaluation. The validity checks, error limits, and retry budget are the same. [RK4 step](tools/cuda/kernels.rs#L1414) · [Adaptive controller](tools/cuda/kernels.rs#L1472) · [Renderer](tools/cuda/kernels.rs#L2148)
3. **Measure the CUDA-to-Bevy handoff.** The finished RGBA8 image travels from CUDA device memory to a host buffer, then back to a Bevy texture. If profiling shows this handoff is significant, compare an overlapped or buffered copy with sharing GPU memory through the active graphics backend. Measure input-to-display latency as well as throughput when buffering frames. [Readback and upload](src/compute/accumulate.rs#L171) · [CUDA graphics interoperability](https://docs.nvidia.com/cuda/archive/13.2.2/cuda-programming-guide/04-special-topics/graphics-interop.html)
4. **Reduce rays during interaction.** The `-` and `=` keys select 25%, 50%, 75%, and 100% render scale. Moving from the default 50% to 25% sends one quarter as many pixels to the ray kernel. Use these presets to measure work scaling before trying automatic resolution changes. An interactive mode could trace at a lower scale during camera motion, then restore the selected scale and resume temporal accumulation. Account for texture reallocations and accumulation resets when evaluating it. [Render scale](src/compute/mod.rs#L185) · [Scale controls and resizing](src/compute/mod.rs#L568) · [Accumulation reset logic](src/compute/mod.rs#L423)
5. **Explore fewer integration steps after work reuse.** Escaping rays currently march to a radius of 1,600 gravitational radii before sampling the sky. A bounded far-field handoff could terminate outward rays earlier when they are clear of the scene and the remaining bending is below an explicit sky-direction error budget. Keep the existing integrator available for inbound, grazing, or ambiguous cases. A separate single-hole experiment could use Kerr's separable geodesics to compute escape directions and disk crossings. That still leaves volumetric transfer and screen transport to evaluate where the image needs them. [Current escape check](tools/cuda/kernels.rs#L2188) · [Explicit Kerr null geodesics](https://arxiv.org/abs/1910.12881)

## Where a BVH or RT cores could help

### Swarm scene: the brute-force baseline

Press K (or use the Swarm panel row) to add 256–4096 small bodies on circular orbits 12–40 r_g out. The kernel tracks coordinate time along each ray and places every body where it was when the light passed it. Inner bodies move several r_g during one crossing of the belt, so straight 3D bounds are not enough. Each ray step tests every body. It skips bodies whose orbit sphere or orbital plane the segment cannot reach, and only then solves linearized relative motion, with the radius padded by the arc's sagitta. [Swarm intersection](tools/cuda/kernels.rs) · [Body generator](src/swarm.rs)

### Space-time BVH

Camera-relative time is cut into 40 slices, each 8 r_g/c wide. For each slice, the host builds a binary BVH over every body's swept box, with median splits and up to four bodies per leaf. Each box holds the body throughout the slice plus 6 r_g/c on either side, padded by the arc's sagitta and by the kernel's own per-step padding. A ray step therefore traverses only the slice its midpoint time falls in, provided the step spans at most 12 r_g/c. A step first has to pass a check against the radial shell that holds every orbit: `beyond_belt`, from `swarm_belt` in `src/swarm.rs`. The check widens the shell by the largest arc sagitta for the step's duration, so it holds for steps of any length. Steps that pass but span more than 12 r_g/c, or start more than 320 r_g/c before the camera time, fall back to brute force. Brute force itself skips the shell check, so it remains an unfiltered reference. The leaves run the same per-body test as brute force, so the hits are the same. Bodies move every frame, so the trees are rebuilt and uploaded every frame. [Traversal](tools/cuda/kernels.rs) · [Builder](src/swarm.rs)

`cargo test --release --bin black_hole -- --ignored swarm_bvh_against_brute_force --nocapture` times the default single-hole view at 400×300 on the RTX 4090. Each kernel time is the median of five launches. The build column is the host build plus upload.

| Bodies | Brute force | BVH | BVH build and upload |
|---:|---:|---:|---:|
| 0 | 127 ms | 130 ms | — |
| 256 | 259 ms | 120 ms | 1 ms |
| 1,024 | 836 ms | 129 ms | 4 ms |
| 4,096 | 4,339 ms | 125 ms | 17 ms |
| 16,384 | about 16 s | 126 ms | 75 ms |

Before the shell check, the BVH took 159, 213, 384 and 890 ms at these body counts. Most of that time went to long far-field steps, which were sent to brute force even though they never came near the belt. Now the swarm costs the kernel almost nothing, and at 16,384 bodies the host rebuild is the larger cost.

At 1,024 bodies the BVH image matches brute force bit for bit (`the_bvh_renders_the_brute_force_image`). `swarm_hits_match_exact_circular_orbits` checks the shared per-body test against exact orbits. Possible next steps include refitting instead of rebuilding, building on the GPU, and choosing slice widths from the measured step spans.

### OptiX RT-core queries (`--features optix`)

In a build with the `optix` cargo feature, which needs the OptiX 9.1 headers (`OPTIX_ROOT`) and libclang (`LIBCLANG_PATH`), the RTX button in the controls panel renders the swarm through OptiX; `--optix` starts with it on. OptiX starts the first time it is needed, and the BVH is used if it cannot start. The OptiX programs are Rust built by cuda-oxide (`tools/optix/programs.rs`, `cargo oxide build --arch sm_80`). The host builds a motion GAS each frame: built-in spheres over 53 keys spanning 412 r_g/c, each padded for half a step's motion, the step's own sagitta padding and the gap between the orbit and OptiX's linear interpolation between keys. One ray per step, at the step's mid time, finds candidates. An any-hit program runs the exact per-body test on each candidate and keeps the earliest hit.

The first attempt traced from inside the render loop, with one `optixTrace` per step near the belt. The image matched brute force, but frames took 0.9–11 s, 5–20 times slower than the BVH. OptiX saves and restores the integrator's whole live state around every trace, and this kernel already needs 255 registers.

The renderer now works in batches, one band of rows at a time:

1. `bh_geodesic_swarm_record` renders the band without swarm hits. Each step that can reach the belt goes into a queue with the pixel's state before that step: colour, transmission, Stokes vector and iteration. The belt check is a radial shell bound that widens with the square of the step's duration, so it is valid for steps of any length. Steps outside the GAS time window are tested by brute force in place, as the BVH does, and so are steps past the queue's capacity.
2. One OptiX launch tests the whole queue.
3. `bh_swarm_first_hit` keeps each pixel's earliest hit with an atomic max. `bh_swarm_apply` then finishes that pixel as the render loop would have finished it at that step.

Each band's queue is limited to 512 MB (5.6 million entries of 96 bytes). Band heights come from the previous frame's densest band. `optix_renders_the_brute_force_image` times the same 400×300 view; the frame is the median of five and includes the host GAS build.

| Bodies | BVH kernel + host build | OptiX frame | of which host GAS build | Steps queued |
|---:|---:|---:|---:|---:|
| 256 | 121 + 1 ms | 145 ms | 2 ms | 8.55 M |
| 1,024 | 125 + 4 ms | 144 ms | 4 ms | 8.56 M |
| 4,096 | 124 + 17 ms | 159 ms | 8 ms | 8.57 M |
| 16,384 | 128 + 75 ms | 199 ms | 24 ms | 8.58 M |

The OptiX launch answers the 8.6 M queries in 0.2 ms at 256 bodies and 31 ms at 16,384, and the first pass costs about as much as a render without the swarm. The BVH uses the same shell check, though, and its traversal is just as cheap. OptiX pays for its queue writes, the band launches and the fix-up passes. It ties the BVH only at 16,384 bodies, where the BVH's single-threaded host rebuild dominates. In this scene RT cores give no gain over the BVH, so OptiX stays opt-in. At up to 1,024 bodies the OptiX image matches brute force bit for bit.

The current binary renderer freezes positions and spins for each trace, so 3D bounds suffice for those geometry queries. RT cores accelerate conventional straight-ray traversal and triangle intersections. A mesh-heavy scene could use a 3D BVH to find candidates along short geodesic segments, with the integrator still computing the trajectory. If accuracy is defined against the curved trajectory, the broad phase needs a conservative bound on the curve's departure from each segment, followed by a refined test for candidate hits. Measure the traversal overhead against the direct loop before adopting it. [Frozen metric](README.md#L91) · [NVIDIA RT cores](https://developer.nvidia.com/blog/?p=11872) · [OptiX ray API](https://raytracing-docs.nvidia.com/optix8/api/group__optix__device__api.html)

Any future RT-core backend must have an on/off switch and fall back to the existing CUDA path when RT hardware is unavailable. Test both settings and the fallback before enabling it by default.

Spacetime bounds become relevant if the scene gains many surfaces that move appreciably during a photon's flight. An OptiX query takes one motion-time value, so moving-surface intersections along a ray whose coordinate time changes still need a time-aware test. Ellis dust already evaluates its analytic density directly at the retarded time along the ray. [OptiX ray time](https://raytracing-docs.nvidia.com/optix8/api/group__optix__device__api.html) · [Ellis dust sampling](src/ellis.rs#L97)

## Verification for each experiment

- **For work reuse**, compare ray outcomes and fixed-camera images before and after, starting with exact output comparisons. Check single and binary scenes, grazing disk rays, near-critical capture and escape, intensity, and polarization. Run the existing Lean-backed CUDA arithmetic fixtures and GPU regressions. Investigate any image or trajectory differences before accepting the change. [CUDA proof and fixture coverage](verification/README.md#L77) · [GPU controller tests](tests/common/controller.rs#L83)
- **For approximations or controller changes**, track captured, escaped, and unresolved rays, plus escape direction, redshift, and image differences where applicable. Check rays on both sides of the critical boundary and keep unresolved cases visible in diagnostics. The existing controller audit records trajectories that miss accuracy targets, and the Lean arithmetic results cover selected formulas under stated hypotheses. Keep tolerances and iteration limits fixed during the work-reuse experiment so the comparisons isolate the optimization. [Accuracy audit](verification/accuracy-performance.md) · [Certified single-hole ray checks](verification/n2-certificates.md)
- **For performance comparisons**, record the GPU, build mode, scene, render dimensions, frame-time distribution, and numerical or image differences together. The EHT snapshot benchmark uses a separate transfer path, so report its timing independently from the live renderer. [Timing and accuracy audit](verification/accuracy-performance.md#L31)
