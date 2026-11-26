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

The guard tests the inward radial tangent and the energy-normalized potential `R(s) = P(s)² − Δ(s)K`, where `P(s) = s² + a² − aλ`, `λ = L/E`, and `K = Q/E² + (λ − a)²`. Over the interval from the outer horizon `h` to the current radius `r`, `P(s)` and `Δ(s)` are increasing. When `P(h)` is positive, `P(h)² − Δ(r)K` is a lower bound for `R(s)`. Since 2026-11-26 the guard uses a piecewise bound instead (below). The GPU checks the bound with an explicit margin in binary64 and checks the local radial equation against the integrated tangent. If a check fails, it tries again once the clearance has halved. A ray must also be below the disk's inner radius by a guard margin. The projected disk radius stays below the Kerr radius, so a monotonically inward exact ray adds zero prescribed emission or absorption. Lean proves the real-arithmetic inequalities.

**Finite precision (2026-11-25).** The round-to-nearest binary64 guard is now only a filter. A ray it accepts must also pass `kerr_capture_certified`, which re-evaluates the hypotheses in interval binary64. Each operation uses an explicit `_rn` intrinsic, so nothing is contracted into an FMA, and then steps one ulp outward. Every decision therefore holds for the exact real values of the stored binary32 state: r is strictly between the horizon and the disk's inner radius, and R > 0 on [h, r] (originally from P(h) > 0 and P(h)² − Δ(r)K > 0; now from the piecewise bound below). The inward tangent is now computed from the state's own momentum, Σ dr/dλ through g⁻¹ = η − 2h ℓ♯ℓ♯ᵀ, which is exact for the null ℓ, instead of from the binary32 velocity. The certificate runs once per captured ray. Inlining the guard into the render loop cost about 0.8 ms per frame, so it is kept out of line. In alternating windowed runs, the still/orbit medians are 19.9–20.2 / 18.2 ms against 19.6–19.7 / 17.8–18.1 ms without the certificate, about 2%. Every capture decision, step count and image is unchanged.

`black_hole::certified::capture_certified` evaluates the same hypotheses on the CPU with the exact-dyadic-checked `Interval`. `the_capture_guard_is_certified_on_the_cpu` runs the full GPU guard on 20,000 random null states per spin, at spins 0, ±0.5, ±0.9 and ±0.995. The states have random Kerr radii up to 3.9, polar angles with sine above 0.12, and inward-biased momenta. All 20,129 GPU captures are certified on the CPU, and 545–743 more states per spin are certified only on the CPU, where the GPU's margins reject them. The equatorial potential test also certifies its 3,241 GPU captures on the CPU.

What remains outside proof: the stored binary32 state differs from the exact ray by the integration error, as for every other exit. IEEE 754 round-to-nearest is assumed. The identity linking the Kerr-Schild Cartesian state to λ, K and R(r) is a standard Carter separation, but it is not in Lean. It is checked numerically by the guard's consistency test (Σṙ)² ≈ R and by the equatorial analytic test. [Separated Kerr null geodesics](https://arxiv.org/abs/1910.12881) · [Lean bounds](verification/BlackHole/KerrCapture.lean)

**Piecewise bound (2026-11-26).** The single bound `P(h)² − Δ(r)K` takes P at its smallest and Δ at its largest, so it fails well before R itself gets small. In the default 400×300 thin-disk view, the slowest rays were captured rays that skim the prograde photon orbit (r ≈ 1.75–1.8 at spin 0.82) for about 1,200 steps before falling in. `near_critical_capture_margin` evaluates R from each ray's initial state. For the 8 slowest rays (1,101–1,248 iterations), R stays above 0.079–0.205 between the horizon and the guard's entry radius r1 − 0.05 = 2.75, which is 4–13% of P² at the minimum, while the old bound is about −16 to −17 there. 232 of the 379 rays past 128 iterations have R > 0 below r1 − 0.05; the other 147 turn and are not captures.

R is a quartic in s, so its Taylor expansion about a point c is exact: `R(c + t) = R₀ + R₁t + Ht² + 4ct³ + t⁴`, with `R₀ = R(c)`, `R₁ = 4cP(c) − (2c − 2)K` and `H = 6c² + 2(a² − aλ) − K`. On `|t| ≤ w` with c ≥ 0, R is positive if either `R₀ − |R₁|w + min(H, 0)w² − 4cw³ > 0` or `H > 0` and `4H(R₀ − 4cw³) − R₁² > 0` (the quadratic part's minimum over all t, written without division). `null_radial_positive_near` in `verification/BlackHole/KerrCapture.lean` proves this. The guard splits [h, r] into 1, 2, 4 and then 8 equal pieces and stops at the first split on which every piece passes, so rays far from a turning point pay for one piece. The binary64 filter demands a margin of 10⁻³ of its existing scale on each piece and checks the inward tangent first. `kerr_capture_certified` evaluates the same bounds in interval binary64 on pieces whose shared knots cover [h.lo, r.hi], and `certified::capture_certified` repeats them on the CPU. The first try now comes as soon as the ray is within 0.05 of the disk's inner edge (clearance r1 − 0.05 − h, 1.18 at spin 0.82), not at clearance 0.5; later tries still wait for the clearance to halve.

The slowest ray in the default view drops from 1,248 iterations to 641. The rays left at the top are the ones with a real turning point: three `near_critical` exits with 544–641 iterations, then escapes with 286–360. Medians of `long_tail_time` (30 launches) over three alternating rounds against the previous PTX (3a820b9), in ms:

| Scene | Previous | Piecewise bound | Change |
|---|---:|---:|---:|
| 400×300 thin disk | 9.85 | 6.50 | −34% |
| 400×300 thin disk, view 2 | 13.59 | 8.50 | −37% |
| 400×300 hot flow, view 5 | 14.75 | 10.11 | −31% |
| 400×300 thin disk, elevation 0.2 | 6.26 | 5.77 | −8% |
| 960×540 thin disk | 12.70 | 7.78 | −39% |
| 960×540 thin disk, view 2 | 16.56 | 10.02 | −39% |
| 960×540 hot flow, view 5 | 21.84 | 16.29 | −25% |
| 960×540 thin disk, elevation 0.2 | 10.10 | 10.14 | +0.4% |

The windowed close-up (`--profile-renderer`) goes from 22.1 / 20.7 ms (still / orbit medians) to 16.2–16.5 / 15.4–15.6 ms over two runs. A first version always used 8 pieces: in the elevation 0.2 views, where most captured rays fall straight in and the old bound already caught them, the extra interval work made frames 4.5–8.5% slower. Trying one piece first removed that. Costliest-tiles-first ordering (P1.5) still pays with the shorter tail: `costliest_tiles_first` gives −9% to −18% at 640×480 and −5% to −20% at 960×540, while 400×300 stays mixed (−3.5% to +4.4%), so the 8-wave threshold is unchanged.

Images are unchanged: `early_capture_matches_the_full_trace` is bit-identical at every spin, disk model, view and camera, with 39,696–45,756 early captures per spin. The swarm, controller and classification tests pass, including zero wrong definitive answers in the near-critical classification. `gpu_escapes_match_the_separated_solution` finds no capture/escape disagreements, with the same escape-direction errors as before. `the_capture_guard_is_certified_on_the_cpu` certifies every GPU capture on the CPU: 12,853–15,154 of 20,000 random states per spin, against 20,129 over all seven spins with the single bound; 142–319 more per spin are certified only on the CPU. A proptest checks that a certified piece has R > 0 at 257 points for random spins, λ, K and pieces, and that an interval of width 2 above the horizon with a turning point is never certified.

The first version checked the bound once. It reduced accepted steps from 42.9 million to 24.1 million in the fixed polarized close-up, while kernel time stayed around 185 ms. The 18 rays that reached the original step cap still did so. Retrying the same bound at tighter radial intervals reduced the workload to **15.1 million steps** and the ray kernel from **190.2 ms to 30.9 ms** in the repeated 400×300 test with a patterned sky. All **112,278** escaping pixels kept the same exit classification. All 7,693 early exits replaced a horizon cutoff, affine stagnation, or iteration cap. The floating-point image and the packed RGBA8 output both matched exactly in that case.

The windowed A/B used the same RTX 4090, close-up, 400×300 internal render, and 60 timed frames per phase. The diagnostic image matched its respective normal kernel exactly in both runs.

| Camera | Full trace median / p95 | Early capture median / p95 |
|---|---:|---:|
| Still | 191.14 / 229.04 ms | 38.56 / 54.88 ms |
| Orbiting | 195.36 / 224.61 ms | 36.32 / 37.84 ms |

All seven fixed-camera image pairs matched in both floating-point and RGBA8 output. These included spins ±0.82 and 0.99, thin-disk intensity, hot-flow EVPA, warped-disk circular polarization, and the binary and spin-0.999 fallback cases. The GPU regression also exercised 4,005 equatorial Kerr rays at five spins, checked early captures against the exterior minimum of the analytic equatorial potential, and checked 256 near-critical Schwarzschild rays with each mode. [GPU trajectory tests](tests/common/controller.rs#L150)

## Far-field steps (first experiment)

Far-field steps are now the default; see "Far-field steps by default (checklist P1.8)" below. `--no-far-field` turns them off. For the benchmark, run `--profile-renderer` once with and once without `--no-far-field` and compare `target/renderer-rays.csv` with `target/renderer-rays-no-far-field.csv`. (The measurements in this section predate both defaults and used `--experiment-early-capture` and `--experiment-far-field`.) Each per-pixel row now includes the number of enlarged steps and the direction used to sample the sky on an escape.

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

## Register caps, carveout and launch shape (checklist P1.4)

`launch_tuning_sweep` times `bh_geodesic` (DP45, early capture) under `.maxnreg` register caps and an L1-preferring carveout, each loaded as its own module from the shipped PTX, at several launch shapes. Configurations are interleaved within each of 15 timed rounds. All 90 configurations of the first sweep rendered images bit-identical to the shipped configuration. Run it with `cargo test --release --bin black_hole -- --ignored launch_tuning_sweep --nocapture`. [Sweep](src/compute/pipeline.rs)

- **Register caps lose.** The kernel needs 255 registers and spills 184 bytes. Capping registers trades occupancy for spills: 232 registers spill 280 bytes, 200 spill 440, 168 spill 568 and 128 spill 792. The time rises by 1–3% at 232, 6–9% at 200, 3–49% at 168, and 2.4–3.7× at 128. This kernel is limited by its live state, not by occupancy. Fewer registers would mean less live state, which is P1.2's specialised paths, not a cap.
- **Target architecture is already native.** The driver JIT-compiles the `sm_80` PTX to `sm_89` SASS (`binary_version` 89), so changing the PTX target would do nothing.
- **The L1 carveout makes no difference.** Setting `PREFERRED_SHARED_MEMORY_CARVEOUT` to 0 (maximum L1) changes no time by more than 0.1 ms. The driver already prefers L1 for a kernel with no shared memory.
- **Launch shape.** For the single hole, 32×4, 16×8 and 8×8 are within ±1% (13.05 / 13.18 / 13.10 ms at 400×300; 23.76 / 23.52 / 23.58 ms at 960×540), so 32×4 stays. For the binary, 8×8 beats the old 16×16 by 6.7% at 400×300 (15.00 against 16.07 ms) and 2.5% at 960×540 (33.64 against 34.50 ms), in both sweeps and for every kernel variant. Non-single geodesic launches now use 8×8. The wormhole kernel keeps 16×16, because it was not measured.

After the change, `dp45_controller_benchmark` gives 15.0 and 33.6 ms for the binary at the two sizes, against 16.2 and 34.5 ms. Single-hole times and the close-up are unchanged.

## Specialised single-hole kernels (checklist P1.2)

Single-hole scenes run their own builds of the production renderer, chosen on the host. `render_geodesic` takes the path as a const parameter.

- **`bh_geodesic_single`** (any single-source scene with default options). It calls `metric_and_rhs_one`, which does the operations of `metric_and_rhs`'s two-slot path with the second slot empty, so the second source's state is never live. It needs 234 registers and no local memory, against 255 registers and 184 spilled bytes for `bh_geodesic`. Images are bit-identical.
- **`bh_geodesic_scalar`** (single source, polarization view off, disk model other than the hot flow). This is `sample_plasma`'s own thermal shortcut condition, under which the screen vector is never read. The kernel does not transport the screen vector, its step error omits the screen term, and it skips `screen_frame` after each step. It needs 222 registers and no local memory. On the 400×300 thin-disk frame it takes 16,826,671 accepted steps and 174,324 rejected attempts, against 16,827,795 and 176,118 for `bh_geodesic`. The screen term almost never limited the step, so the time saved is work per step, not coarser steps. Images are not bit-identical. The largest channel difference from `bh_geodesic` is 0.0021 on the benchmark frames and 0.00203 in the match test, under half of 1/255.

`specialised_kernel_benchmark` (thin disk, default camera, launches interleaved, 17 timed rounds):

| Kernel | Registers / local bytes | 400×300 | 960×540 |
|---|---|---|---|
| `bh_geodesic` | 255 / 184 | 13.07 ms | 23.66 ms |
| `bh_geodesic_single` | 234 / 0 | 11.35 ms | 20.56 ms |
| `bh_geodesic_scalar` | 222 / 0 | 9.33 ms | 16.67 ms |

The close-up (`--profile-renderer`) uses polarization view 2 and the hot flow, so it runs `bh_geodesic_single`. Two rounds each, alternating, still / orbit medians: 18.35 / 16.92 and 18.25 / 16.98 ms with `bh_geodesic`, against 16.47 / 15.01 and 16.22 / 15.09 ms with `bh_geodesic_single` (about 11%).

`specialised_kernels_match_bh_geodesic` renders 4 spins (0, 0.82, -0.99, 0.999), all 4 disk models, polarization views 0, 2 and 5, and 2 camera elevations. It requires `bh_geodesic_single` to match `bh_geodesic` bit for bit everywhere, and `bh_geodesic_scalar` to stay within 1/255 in every channel in each thermal-only mode. Binaries, the swarm, the wormhole, diagnostics and the `--full-trace`, `--no-far-field`, `--no-analytic-legs`, `--band-legs` and `--rk4-controller` options still use the generic kernels.

## Far-field steps by default (checklist P1.8)

P1.8 asks for an analytic vacuum propagator. Before building one, a step census measured how much there is to gain. With capped steps, steps starting at r ≥ 64 were 52–59% of all steps in the tested single-hole frames: an escaping ray took about 55 of its roughly 92 steps there, crossing empty space to the sky sphere at r = 1600. An oracle that ended escaping rays at r = 64 for free, as a perfect analytic escape would, cut the kernel time by 18–33% at 960×540 and 4.5–11% at 400×300. (It sampled the sky at the wrong place, so it bounds the gain and says nothing about accuracy.)

The far-field steps from the first experiment already take much of that gain, so they are now the default for single-hole scenes. Against the separated reference (`gpu_escapes_match_the_separated_solution`, 4 spins and 2 elevations), they leave the escape-direction error unchanged: the median stays 1.2–1.7e-7 rad, the 99th percentile 2.5–4.1e-6 rad, and no ray changes classification.

Same-process A/B against the previous PTX, 30 alternating samples after warm-up, medians:

| Kernel | Scene | 400×300 | 960×540 |
|---|---|---:|---:|
| `bh_geodesic` | thin disk | 13.12 → 13.03 ms | 20.55 → 18.20 ms (−11.4%) |
| `bh_geodesic` | thin disk, view 2 | 14.46 → 14.45 ms | 22.15 → 19.89 ms (−10.2%) |
| `bh_geodesic` | hot flow, view 5 | 8.89 → 8.48 ms | 22.21 → 17.55 ms (−21.0%) |
| `bh_geodesic` | thin disk, elevation 0.2 | 8.00 → 7.80 ms | 17.71 → 15.27 ms (−13.8%) |
| `bh_geodesic_single` | thin disk | 11.01 → 11.14 ms | 17.54 → 15.66 ms (−10.7%) |
| `bh_geodesic_single` | thin disk, view 2 | 12.39 → 12.47 ms | 18.81 → 17.12 ms (−9.0%) |
| `bh_geodesic_single` | hot flow, view 5 | 7.61 → 7.44 ms | 18.51 → 15.06 ms (−18.6%) |
| `bh_geodesic_single` | thin disk, elevation 0.2 | 6.85 → 6.90 ms | 15.02 → 13.05 ms (−13.1%) |
| `bh_geodesic_scalar` | thin disk | 9.08 → 9.31 ms | 14.19 → 12.99 ms (−8.4%) |
| `bh_geodesic_scalar` | thin disk, elevation 0.2 | 5.69 → 5.66 ms | 11.90 → 10.55 ms (−11.4%) |

At 400×300 the changes run from −4.6% to +2.5%, close to the noise. The gain is larger at 960×540, where more rays escape to the sky and the per-ray saving outweighs the frame's tail.

Shift check over six views (thin disk at two elevations, warped disk at spin −0.9, the hot-flow close-up, the warped disk from radius 160, and the thin disk at spin 0.99), 400×300: steps fell by 34–42% (for example 11.19M → 6.96M on the thin disk, 8.98M → 5.25M from radius 160). No ray changed its exit and Stokes I was unchanged bit for bit. The sampled sky direction moved by at most 5.8e-7 rad and the largest image change was 2.7e-7.

So a full analytic escape can add at most the difference between the oracle and the far-field default: about 5–13 points at 960×540, minus its own cost. The next section measures it.

## Analytic escape (checklist P1.8)

The next section generalises this leg; the names below are those of this first version.

An escaping single-hole ray now leaves the numerical loop once it is outside the sphere enclosing the disk and the hole (radius at least 16) and moving outward within 18 degrees of radial, the far-field guard. From there `analytic_escape` in `tools/cuda/kernels.rs` carries it to Kerr–Schild radius 1600 with the separated solution and samples the sky. Swarm scenes keep the numerical trace, because the leg would skip their per-step intersection tests. `--no-analytic-escape` (experiment bit 8) turns the leg off; `--no-far-field` turns off both.

**Method.** Beyond r = 4 an outgoing ray has no radial turning point left, so the elliptic case analysis of P1.7 is not needed:
- *Radial integrals.* With u = 1/r, R(r) = r⁴ f(u) and f(u) = 1 + (a² − η − λ²)u² + 2(η + (λ − a)²)u³ − a²η u⁴. Under the guard f stays near the squared radial cosine (above 0.5 is required), so Mino time ∫du/√f, the Boyer–Lindquist azimuth term and the Kerr–Schild shift ∫a du/(1 − 2u + a²u²) are smooth on [1/1600, 1/r]. An 8-node Gauss–Legendre sum evaluates them.
- *Polar motion.* In Mino time the polar direction n = (sin θ cos ψ, sin θ sin ψ, cos θ) moves on the unit sphere under the potential −a² n_z²/2, with ψ the polar part of the azimuth: n'' = −|n'|² n + a² n_z (ẑ − n_z n). This equation is regular at the pole, unlike ∫dτ/sin²θ: a first version that integrated cos θ and ∫dτ/sin²θ had errors up to 2.7e-6 rad near the pole and had to reject 9% of rays. Eight RK4 steps integrate n; the azimuth comes from its final direction.
- *Precision.* The conserved quantities, the start point and the rebuild of the Cartesian state run in binary64, where they cancel. The Gauss–Legendre sums and the RK4 stages run in binary32 (64 times faster on this GPU), with the polar state accumulated in binary64. Only `sqrt` and a hand-written binary64 `sin_cos` are needed.
- *Divergence.* The first device version called the leg inside the loop, so a warp ran it once for each escaping lane, one lane at a time. It was 3–15% slower than the far-field default. Lanes now leave the loop and run the leg together after it, once per warp. If a guard fails (not seen in testing), the ray resumes the numerical trace.

**Accuracy.** `separated::far_escape` is the leg's CPU twin, line for line. `far_escape_matches_the_separated_solution` checks it against the binary64 quadrature reference on random outgoing rays from r = 12 to 800 at spins up to ±0.99, including rays over the pole, and requires 2e-7 rad. Over 20,000 rays per radius band the error has median 4–8e-9 rad, 99th percentile 3–6e-8 rad and maximum 1.3e-7 rad (at r = 12–16; 7e-8 rad from r = 24). On the GPU, `gpu_escapes_match_the_separated_solution` is unchanged: median 1.3–1.7e-7 rad, 99th percentile 2.5–4.0e-6 rad, and no pixel changes classification.

**Steps.** In the 400×300 thin-disk view, accepted steps fall from 6.96 million to 4.84 million, and steps starting at r ≥ 64 from 2.23 million to 0.22 million. Every exit is unchanged (117,840 escapes in both).

**Time.** Same-process A/B against the far-field default PTX, 30 alternating samples after warm-up, medians:

| Kernel | Scene | 400×300 | 960×540 |
|---|---|---:|---:|
| `bh_geodesic` | thin disk | 13.20 → 13.23 ms | 18.50 → 17.60 ms (−4.9%) |
| `bh_geodesic` | thin disk, view 2 | 14.46 → 14.64 ms | 20.15 → 19.35 ms (−4.0%) |
| `bh_geodesic` | hot flow, view 5 | 8.58 → 8.60 ms | 17.77 → 16.40 ms (−7.7%) |
| `bh_geodesic` | thin disk, elevation 0.2 | 7.91 → 7.91 ms | 15.48 → 14.60 ms (−5.7%) |
| `bh_geodesic_single` | thin disk | 11.26 → 11.21 ms | 15.83 → 14.97 ms (−5.4%) |
| `bh_geodesic_single` | thin disk, view 2 | 12.64 → 12.61 ms | 17.30 → 16.51 ms (−4.6%) |
| `bh_geodesic_single` | hot flow, view 5 | 7.49 → 7.27 ms | 15.24 → 13.79 ms (−9.5%) |
| `bh_geodesic_single` | thin disk, elevation 0.2 | 6.71 → 6.51 ms | 12.90 → 12.00 ms (−7.0%) |
| `bh_geodesic_scalar` | thin disk | 9.28 → 9.41 ms | 12.80 → 12.68 ms (−0.9%) |
| `bh_geodesic_scalar` | thin disk, elevation 0.2 | 5.62 → 5.63 ms | 10.48 → 9.96 ms (−4.9%) |

No image channel changed by more than 4e-4, and none by 1/255. Against a stub that moves the ray to r = 1600 for free, the leg costs 0–4% (mostly 1–3%), so most of the remaining gap to the oracle is not its arithmetic. Repeat runs moved individual rows by about ±1.5 points.

**Not covered.** Only the escape leg is analytic. Vacuum intervals between disk crossings and inward legs to the horizon (where early capture already ends most rays) still use the numerical trace.

## Vacuum legs (default, checklist P1.8)

The escape leg above is now one case of a general vacuum leg. Outside the sphere enclosing the disk and the hole, every single-hole ray is carried analytically. An outward ray goes to the sky sphere, as before but without the 18-degree cone. An inward ray goes either back to the sphere or through its radial turning point and out to the sky. Inside the sphere the numerical trace runs as before. `analytic_vacuum_leg` in `tools/cuda/kernels.rs` is the device leg and `separated::vacuum_leg` its CPU twin. The trigger now sits at the top of the step loop, so rays leave the camera, which is outside the sphere in the default view, on a leg. `--no-analytic-legs` (experiment bit 8, which replaces `--no-analytic-escape`) turns the legs off.

**Method.** The radial and polar parts are as in the escape leg, with three changes:
- *Turning points.* With r ≥ 12, f(u) is either close to 1 or decreasing and concave in u, so a leg meets at most one radial root u₁, and it is simple. An inward ray turns before the sphere exactly when f(1/r_sphere) ≤ 0. Newton's method finds u₁ (8 binary32 iterations from 1/b, then 2 binary64). Synthetic division gives f = (u − u₁) q(u), and the substitution u = u₁ − t² makes ∫du/√f = ∫2 dt/√(−q), which is smooth. The same substitution covers rays that pass the sphere nearly tangentially, where f(u) < 1/2 at the deep end.
- *Polar motion.* A turning leg sweeps up to about π, against 0.3 rad for the escape cone. With |n'|² taken from energy conservation, n'' = −ω²n + F(n) with F = a²(n_z ẑ − (2n_z² − n_z0²) n) and ω = |n'(0)|. The great circle n = A cos ωτ + B sin ωτ/ω is exact for a = 0. Sixteen binary32 RK4 steps integrate only the corrections to A and B (variation of constants), and F/ω² ≤ a²/b² is small for every leg that sweeps far.
- *Winding.* The leg adds ωτ, the angle swept by the polar direction, to the near-critical winding count.

**Accuracy.** Three proptests check `separated::vacuum_leg` against the binary64 quadrature reference at spins up to ±0.99. They cover outgoing rays tilted up to 89 degrees from radial, from r = 13 to 800. They also cover inward rays, which either turn outside a sphere of radius 12–40 or reach it; for those, the reference runs backward from the leg's end and must return to the start. Over 20,000 rays each, the direction error has median 1–7e-8 rad, 99th percentile 1.1–2.7e-7 rad and maximum 4.6e-7 rad. The binary32 radial sums set this error: in binary64 it falls to about 1e-8. The tests require 1e-6 rad, well below the numerical trace's own 99th percentile against the reference (2.5–4.0e-6 rad). On the GPU, `gpu_escapes_match_the_separated_solution` finds no classification change, median 1.3–1.8e-7 rad and 99th percentile 2.5–4.0e-6 rad, as before.

**Steps.** 400×300, per frame:

| View | Escape leg | Vacuum legs | Band legs (experiment) |
|---|---:|---:|---:|
| thin disk | 4.84 M | 2.86 M | 1.29 M |
| thin disk, elevation 0.2 | 4.66 M | 2.69 M | 1.02 M |
| hot flow, view 5 | 4.68 M | 4.65 M | 4.65 M |

Every exit is unchanged. In the hot flow the enclosing sphere (radius about 90) contains the camera, so only escapes beyond it use a leg.

**Time.** Same-process A/B against the escape-leg PTX (HEAD), 30 alternating samples after warm-up, medians:

| Kernel | Scene | 400×300 | 960×540 |
|---|---|---:|---:|
| `bh_geodesic` | thin disk | 14.93 → 14.07 ms (−5.7%) | 19.74 → 17.00 ms (−13.9%) |
| `bh_geodesic` | thin disk, view 2 | 16.77 → 15.41 ms (−8.1%) | 21.53 → 19.24 ms (−10.6%) |
| `bh_geodesic` | hot flow, view 5 | 9.50 → 9.34 ms (−1.6%) | 18.60 → 18.15 ms (−2.4%) |
| `bh_geodesic` | thin disk, elevation 0.2 | 8.92 → 8.69 ms (−2.7%) | 17.10 → 14.72 ms (−13.9%) |
| `bh_geodesic_single` | thin disk | 13.41 → 12.94 ms (−3.5%) | 17.16 → 15.63 ms (−8.9%) |
| `bh_geodesic_single` | thin disk, view 2 | 14.40 → 14.32 ms (−0.5%) | 18.56 → 17.00 ms (−8.4%) |
| `bh_geodesic_single` | hot flow, view 5 | 8.39 → 8.38 ms (−0.2%) | 15.89 → 16.40 ms (+3.2%) |
| `bh_geodesic_single` | thin disk, elevation 0.2 | 7.86 → 8.14 ms (+3.5%) | 14.94 → 13.33 ms (−10.8%) |
| `bh_geodesic_scalar` | thin disk | 11.66 → 11.50 ms (−1.4%) | 16.14 → 13.94 ms (−13.7%) |
| `bh_geodesic_scalar` | thin disk, elevation 0.2 | 7.48 → 7.14 ms (−4.5%) | 13.94 → 12.78 ms (−8.3%) |

This run's absolute times are about 8% above the escape-leg table's, on the same GPU; compare within a row.

Two pixels per 960×540 frame change by up to 0.01 in one channel. Both sit on the photon ring, with 240–300 steps and sky directions that differ by 1e-3–1.5 rad: chaotic rays where a 1e-7 difference at the start of the trace grows exponentially. Of the other pixels, 99.99% change by less than 1e-4. Repeat runs moved rows by about ±2 points.

**Band legs inside the sphere (experiment, bit 9, `--band-legs`).** After the outside legs, 78% of the remaining thin-disk steps (2.06 M of 2.65 M for escaping rays) are vacuum steps inside the sphere but outside the emitting slab, 1.43 M of them at r ≥ 12. The thin disk's emission |y| < 4H, H = h r_disk, lies inside the polar band |cos θ| < k/√(1 + k²), k = 4h. So a leg from r > 12 with |cos θ| clear of that band can run until the first of three events: the band, r = 12 going in, or the sky. The polar Mino time to the band is a Gauss–Legendre sum in t = √(μ₊ − |cos θ|), with a turning point at μ₊ when the ray first moves away from the equator. A proptest checks it against a binary64 march of the polar motion to 1e-5. Vortical rays (η < 0) count as never reaching the band if μ₋ lies outside it, and are rejected otherwise. When the band comes first, Newton's method on the partial radial sums finds r at that Mino time. A fourth proptest checks band legs against the reference, forward or backward according to the end's radial direction. The same error statistics give median 1–3e-8 rad and maximum 4.0e-7 rad.

On the GPU the band legs remove another 55–62% of the steps in thin-disk views. No pixel changes classification, and the reference errors are median 1.2–1.9e-7 rad and 99th percentile 1.7–6.4e-6 rad (up from 4.0e-6 in edge-on views). They are not faster. Against the outside legs alone, the band legs with a start margin of 2 (|cos θ| > 2× the band) measured −4.5% to +2.6% in thin-disk views, within noise. The same legs with a 1.02 margin, applied to the hot flow (band ±0.89), were 3–9% slower. Each leg costs about 300 binary64 operations, roughly as much as 20 Dormand–Prince steps on this GPU. A ray takes one to three band legs, at different iterations from its warp neighbours, so the warp runs each leg separately and the slowest lanes still set the time. So they stay an experiment: `render_geodesic`'s `BAND` parameter compiles them only into the experiment and diagnostics kernels. When compiled in, the dormant band branch alone cost the production kernels 1–10%. Thick flows (H/R > 0.1) and the warped disk take no band legs.

**Not covered.** Inside r = 12 and inside the band the trace stays numerical, as do inward legs to the horizon. Early capture already ends most of those with a proved Kerr test. Cheaper band legs would need the binary64 setup and rebuild cut down, or warp-synchronous scheduling of the legs; the step counts above bound the possible gain.

## Long-tail scheduling (checklist P1.5)

A few rays take far longer than the rest, so the checklist proposed a hybrid scheduler: a first pass of N iterations per ray, then a compacted resume pass for the rays still running. The measurements below show that the long tail is the latency of a few hundred rays, not idle lanes. The hybrid scheduler is therefore slower at every N tested, and was removed. What helps is starting the costliest tiles first, which is now the default when the grid needs at least 8 waves of blocks.

```
cargo test --release --bin black_hole long_tail -- --ignored --nocapture
cargo test --release --bin black_hole costliest_tiles_first -- --ignored --nocapture
```

**Setup.** RTX 4090, the production single-hole kernels (`bh_geodesic_scalar` for thermal views, `bh_geodesic_single` for polarized views and the hot flow), 32×4 blocks, the default camera and two-texel test sky. Each kernel fits 2 blocks of 128 threads per SM, so 256 blocks are resident at once and a 400×300 frame (975 tiles) runs in about 4 waves. Medians of 30 launches after 5 warm-up rounds, variants alternating.

**Lanes are not the problem.** `long_tail_model` takes each ray's attempts (accepted steps plus rejected tries) from the diagnostics kernel. The median ray takes 15–36 attempts, the 99th percentile 89–108, and the slowest 707–1,335. Warp lane efficiency is 70–87%. Suppose capping every ray at N attempts and packing the survivors into full warps cost nothing. One resume pass would then save at most 4–12% of warp work, and repeated passes at N = 32 (up to 42 of them) 7–19%.

**Time is.** `long_tail_time` cuts the iteration limit instead. The table gives frame times in ms; the survivors are the rays still running at each limit.

| Scene | 10,000 (default) | 512 | 256 | 128 | 64 |
|---|---:|---:|---:|---:|---:|
| 400×300 thin disk | 8.98 | 5.17 | 3.84 | 2.81 | 1.76 |
| 400×300 hot flow, view 5 | 13.48 | 8.44 | 6.90 | 5.28 | 3.70 |
| 960×540 thin disk | 11.49 | 7.49 | 5.99 | 5.10 | 4.15 |
| 960×540 hot flow, view 5 | 19.85 | 15.47 | 13.77 | 13.33 | 12.34 |

At 400×300, 0.35% of the rays run past 128 iterations and take 69% of the thin-disk frame. The 29 rays past 512 alone add 3.8 ms. Once the other blocks have finished, a lone warp takes about 5 µs per step, so a ray of 1,250 steps sets the frame time by itself.

**The slowest rays.** `long_tail_rays` lists them. At 400×300 they form a short vertical line of pixels at x = 183, 17 pixels left of the image centre, in the thin disk and the hot flow alike. Nearly all end in early capture after winding less than the 14-rad unresolved band: they are near-critical rays that skim the hole before falling in. About 1,200 of their 1,250 steps are within clearance 1 of the horizon, where the step is limited to 0.12 × clearance; the Dormand–Prince controller limits at most 31 of them. Early capture ends a ray only once its binary64 test rules out a turning point.

**Suspend and resume: slower.** The hybrid scheduler was built and measured. The first pass suspended each ray still running after N iterations into a structure-of-arrays queue: 35 words of ray state, and an atomic slot per ray. If the queue was full, the ray finished in place. A resume pass then ran the survivors to completion, one thread per slot. It recomputed each ray's metric the same way the last step had, so images were bit-identical to the single pass. The pair of kernels was slower than the single pass at every cap:

| Scene | N = 64 | N = 128 | N = 256 | N = 512 |
|---|---:|---:|---:|---:|
| 400×300, four scenes | +7% to +12% | +21% to +32% | +21% to +31% | +12% to +26% |
| 960×540, four scenes | +28% to +32% | +39% to +43% | +35% to +41% | +20% to +29% |

Suspending a ray only moves its remaining steps after the first pass, so the frame waits for the first pass and then for the slowest ray's full latency. The kernels were removed: unused, the four of them and the ordering experiment's two kernels added 13 s (46%) to the driver's first, uncached PTX compilation (28.9 s to 42.2 s). A full wavefront scheduler was not tried, because the checklist makes it conditional on the hybrid one winning.

**Costliest tiles first (default).** `bh_geodesic_single` and `bh_geodesic_scalar` take a tile `order` and a `costs` buffer. Block b renders tile `order[b]`. Each warp raises its tile's cost to its most iterations, using shuffles and one `red.max`. After the frame, `bh_tile_histogram` and `bh_tile_order` sort the tiles costliest first into half-octave buckets of iterations, all on the GPU. The next frame starts with the tiles that were costliest in this one, so the slowest rays overlap their latency with the rest of the frame. Ordering cannot change a pixel. `costliest_tiles_first` checks that each image is bit-identical and that the order is a permutation of the tiles, sorted by bucket. Times include the two ordering kernels:

| Size (waves) | Thin disk | Thin disk, view 2 | Hot flow, view 5 | Thin disk, elevation 0.2 |
|---|---:|---:|---:|---:|
| 400×300 (3.8) | +3.9% to +5.9% | +8.5% to +9.8% | +3.7% to +4.9% | −0.8% to +1.6% |
| 640×480 (9.4) | −3.0% to −1.1% | −2.3% to +0.7% | −9.7% to −8.5% | −7.0% to −4.9% |
| 960×540 (15.8) | −8.7% to −7.7% | −9.3% to −7.5% | −24.3% to −22.5% | −9.3% to −6.4% |
| 1280×720 (28.1) | −18.3% to −18.1% | −18.7% to −17.3% | −13.7% to −12.6% | −22.2% to −21.0% |
| 1920×1080 (63.3) | −18.5% to −16.3% | −14.8% to −14.2% | −0.5% to +1.0% | −0.6% to +1.6% |

Ranges are over three runs. The two 1920×1080 scenes that do not gain spend their time on throughput, not on the slowest rays. At 400×300 the slowest rays' own latency is longer than the rest of the frame, so starting them early cannot shorten it. Starting them together slows them. Strict sorting, sorting by summed iterations, moving only the 64 or 256 costliest tiles forward, and moving only tiles above 4 or 16 times the median cost all timed within noise of each other, with the same 400×300 loss. `dispatch_geodesic` therefore orders the tiles only when the grid has at least 8 times as many tiles as there are resident blocks (`ORDER_MIN_WAVES`), and passes null pointers otherwise. With null pointers the kernels render in row order. They are 0.7% slower on average than before the change, within the run-to-run spread (−1.9% to +2.6%), and the images are bit-identical.

**Not covered.**
- **The default view does not change.** (Since addressed: the piecewise capture bound, in "Single-Kerr early capture", ends most of these rays at the disk's inner edge and makes the default view 34% faster.) The app's 800×600 window at render scale 0.5 renders 400×300, below the threshold. That frame is set by about 30 near-critical rays. Only fewer steps for them would shorten it: for example a step limit that lets the controller lead near the photon orbit, or analytic legs inside the disk's inner edge. Both change trajectories, so they need the separated reference checks (P1.6, P1.8).
- **The binary, swarm and experiment kernels** still render in row order. The binary's 8×8 blocks do not fit the one-row-per-warp cost recording.
- **A moving camera.** The order comes from the previous frame. In a still frame it is exact, but it was not timed while the camera orbits.
- **Other GPUs.** The 8-wave threshold comes from one RTX 4090.

## Separated Kerr reference (checklist P1.7)

`black_hole::separated` solves a single-hole null geodesic in binary64 from E, L and Q. It finds the radial roots with Ferrari's resolvent and Newton polishing, classifies the ray as captured, escaped or unresolved, and returns the state where the ray first reaches a target radius going outward. Unresolved covers critical double roots (relative root gap below 1e-7), bound orbits, rays exactly on the spin axis, and escaping rays with Q <= 0. The state at the target radius is computed two independent ways:
- **Elliptic:** Gralla–Lupsasca closed forms, using Carlson R_F/R_J and AGM Jacobi functions written for this module.
- **Quadrature:** tanh–sinh quadrature of the same Mino-time integrals, with the polar motion inverted by bisection.

On a ray grid from equatorial and polar cameras at 4 spins, every ray resolves and the two methods agree to 1e-9 rad. Both match a binary64 RK4 integration of the Cartesian Kerr–Schild geodesic to 1e-8 rad. 1 - u₊ is computed from its own quadratic, so rays that pass within 1e-7 rad of the axis keep their azimuth.

`gpu_escapes_match_the_separated_solution` traces every pixel of a 160×120 thin-disk frame from the GPU's own initial state. It runs 4 spins (0, 0.5, -0.9, 0.99) and 2 camera elevations (1.47 and 0.40 rad). Results:
- **Classification:** no pixel escapes on the GPU but is captured in the reference, or the reverse. The exceptions are the GPU's near-critical band (up to 26 pixels per frame) and rays the opaque disk stops (675–942 per near-equatorial frame).
- **Escape direction:** median error 1.4–2.3e-7 rad, 99th percentile 2.5–7.9e-6 rad, and maximum 1.6e-4 to 6.1e-3 rad. Between 483 and 1,299 of each frame's 17,000–18,000 escapes miss the P0.2 target of 1e-6 rad.
- **Gates:** zero classification disagreements, median below 1e-6 rad and 99th percentile below 2e-5 rad.

Not covered:
- Closed forms for outgoing rays with no turning point outside the horizon. The quadrature covers them, and no GPU camera ray in these frames needed them.
- Escaping vortical rays (Q <= 0).
- A Carlson-integral formulation separate from the elliptic one. The second method is quadrature instead.

## Decoupled transfer (checklist P1.9, default)

Before this change, the renderer took one midpoint plasma sample per geodesic step. Near the disk it limited the step to a quarter of the disk scale height H, so the plasma's resolution set the trajectory's step: 56% of accepted steps in the polarized close-up were disk-limited. Now the step's transfer is split into its own constant cells, and the geodesic step is limited only by the controller and by a cap of 8 cells:
- **Dense output:** each cell samples the plasma at its midpoint on a cubic Hermite interpolant of the accepted Dormand–Prince step. The interpolant uses the stage rates k1 and k7, which the controller already computes, for position, momentum and screen vector.
- **Cell length:** min(H/4, 0.05 r). The H/4 term is the old limit. The 0.05 r term resolves emissivity and Doppler variation along the orbit, which the thick hot flow's H/4 (0.125 r) did not.
- **Which steps are split:** only steps that can reach the emitting slab (|z| < 4H). As in the coupled scheme, a chord shorter than half the vertical distance to the slab is taken in one cell.
- **Cap of 8 cells per step:** at 32 cells the longer steps left the thin-disk Stokes error at twice the coupled value. At 8 cells it matches, for 3% more steps.
- **Fallback:** `--coupled-transfer` (experiment bit 3) restores the old scheme for one release. The legacy RK4 controller has no stage rates, so it always uses the coupled scheme.

**Fixed-path check.** `transfer_paths_match_the_constant_coefficient_solution` composites 8-cell paths of random constant coefficients through the renderer's own cell routine (`bh_test_transfer_path`). It compares them with a binary64 RK4 solution of dS/dl = j − αS + (0, ρ × S_pol). Over 32,768 paths the colour and transmission errors stay below 2.4e-7. The Stokes error relative to the path's unattenuated intensity stays below 1.3e-6. About 5 paths in 32,768 miss the 1e-6 target. Each of those rotates through tens of radians of Faraday angle, which binary32 holds only to 2^-24 of the angle, and each stays inside that floor. The named edge cases (`transfer_path_edge_cases`) meet 1e-6. One finding was fixed: `polarized_cell` skipped the rotation inside the cell when w·ds < 1e-5, which dropped up to w·ds/2 of the polarized emission (measured 2.2e-6). The cutoff is now 1e-7.

**Image check.** `decoupled_transfer_against_a_refined_reference` renders 160×120 frames with the diagnostics kernel. The reference is the coupled scheme with cells 16 times shorter. A coupled run with cells 8 times shorter, and a decoupled run at the reference's refinement, agree with it to a p99 of 1.3e-6 to 4.8e-6. Errors are relative to the reference's peak intensity:

| Scene | Coupled steps | Decoupled steps | Coupled p99 / max | Decoupled p99 / max |
|---|---:|---:|---:|---:|
| Thin disk, polarized, elevation 1.22 | 2.69M | 1.79M | 4.8e-6 / 9.6e-5 | 5.0e-6 / 1.1e-4 |
| Thin disk, elevation 0.20 | 2.39M | 1.76M | 1.3e-5 / 2.8e-4 | 1.1e-5 / 6.7e-5 |
| Hot flow (spin 0.5), circular polarization | 2.49M | 1.72M | 2.8e-4 / 8.0e-4 | 3.7e-5 / 4.4e-4 |
| Warped disk (spin −0.9), elevation 0.40 | 2.31M | 1.76M | 2.1e-5 / 5.2e-5 | 2.0e-5 / 5.9e-5 |

The p99 relative intensity error above 1e-3 of peak is 1.3e-5 to 8.9e-5 decoupled, against 1.5e-5 to 7.1e-4 coupled. Only the decoupled scheme meets the 1e-4 relative target at p99 in every scene. Neither meets it at the maximum: the worst decoupled pixel is 1.8e-3, and the refined runs disagree with each other by up to 1e-3 at the same pixels. Neither meets the 1e-6 Stokes target. No exit classification changes, and no pixel changes by more than 1/255.

**Vacuum check.** Fewer, longer steps also make escape directions more accurate. Against the separated solution (`gpu_escapes_match_the_separated_solution`, which now runs both schemes), the near-pole frames' p99 direction error falls from 6.7–7.9e-6 rad to 3.0–4.1e-6 rad. The escapes that miss 1e-6 rad fall from 1,101–1,299 to 473–576 per frame. The near-equatorial frames change little: p99 2.5–3.5e-6 rad coupled, 2.5–3.2e-6 rad decoupled. Every escape/capture classification is the same.

**Time.** A same-process A/B against the previous PTX, in the production kernels (17 timed launches each, medians):

| Scene | Size | `bh_geodesic` | `bh_geodesic_single` | `bh_geodesic_scalar` |
|---|---|---:|---:|---:|
| Thin disk, elevation 1.22 | 400×300 | 14.75 → 14.46 ms (−2.0%) | 11.95 → 11.88 ms (−0.6%) | 10.31 → 10.10 ms (−2.1%) |
| | 960×540 | 25.37 → 21.86 ms (−13.9%) | 22.54 → 19.30 ms (−14.4%) | 18.22 → 15.68 ms (−13.9%) |
| Thin disk, polarized, elevation 1.22 | 400×300 | 15.00 → 15.51 ms (+3.4%) | 13.47 → 13.77 ms (+2.3%) | — |
| | 960×540 | 26.72 → 24.11 ms (−9.8%) | 23.32 → 20.64 ms (−11.5%) | — |
| Hot flow (spin 0.5), circular polarization | 400×300 | 8.24 → 9.55 ms (+16.0%) | 7.32 → 8.55 ms (+16.8%) | — |
| | 960×540 | 25.47 → 24.25 ms (−4.8%) | 22.16 → 19.85 ms (−10.4%) | — |
| Thin disk, elevation 0.20 | 400×300 | 8.55 → 8.66 ms (+1.3%) | 7.62 → 7.52 ms (−1.3%) | 6.63 → 6.50 ms (−2.1%) |
| | 960×540 | 20.50 → 19.24 ms (−6.2%) | 17.84 → 16.52 ms (−7.4%) | 14.68 → 13.60 ms (−7.4%) |

Registers: `bh_geodesic` 255 with 192 local bytes (was 184), `bh_geodesic_single` 240 with no spills (was 234), `bh_geodesic_scalar` 218 (was 222). The hot flow at 400×300 is slower because its cells are 2.5 times shorter. It buys an 8-fold smaller p99 error. At 960×540 the hot flow is still faster. The largest channel change is 0.0055, in the scalar kernel's edge-on 960×540 frame. Every other change in these frames is at most 0.002.

Not covered:
- **Error-controlled quadrature:** cells are sized from local scales (H and r), not from an error estimate.
- **The |z| = 4H truncation:** the density jumps from exp(−8) of its midplane value to zero there, and that jump is not resolved.
- **The EHT snapshot path:** it keeps its own transfer loop (`transfer_cell` and `grid_step`). Its status counts are unchanged (990 captured, 24,610 escaped), and it was not decoupled.

## Baseline profile (checklist P0.1)

`baseline_profile` times the production kernels on a fixed scene set, with the kernel and launch shape `dispatch_geodesic` picks for each scene. In the same rounds it times `bh_geodesic` from the checklist's pinned revision (e9ce1b95), loaded from `PINNED_PTX`. That kernel was the pinned app's default: the RK4 controller, full trace, 16×16 blocks for the binary. The camera, disk, frame index and sub-pixel sample are fixed, and the sky is a two-texel test texture. Each launch is timed with CUDA events: 10 warm-up rounds, then 30 timed rounds. Within a round the scenes run in turn, and the current and pinned kernels alternate which goes first. Per-launch times go to `target/baseline-profile.csv`. Step and exit counts come from a separate pass of the diagnostics kernel, so timing runs without instrumentation.

```
PINNED_PTX=<git show e9ce1b95:src/compute/kernels.ptx> cargo test --release --bin black_hole baseline_profile -- --ignored --nocapture
```

**Setup.** RTX 4090, driver 621.01, Windows 11. PTX source SHA256 eee2004e…, cuda-oxide e027ac32, LLVM NVPTX `sm_80` PTX 7.0. Under load the GPU held P2 at 2,820 MHz SM and 10,251 MHz memory, 44–54 °C, 180–297 W. Kernel resources: `bh_geodesic` 255 registers and 192 local bytes, `bh_geodesic_single` 236 and none, `bh_geodesic_scalar` 218 and none, pinned `bh_geodesic` 255 and 704 local bytes. Each fits 2 blocks of 128 threads per SM.

**Time.** Medians and p95 in ms. Two runs in separate processes; their medians agree within 1.5%.

| Scene | Kernel | 400×300 median (run 1 / 2) | p95 | Pinned median | 960×540 median (run 1 / 2) | p95 | Pinned median |
|---|---|---:|---:|---:|---:|---:|---:|
| Thin disk, elevation 1.22 | scalar | 9.81 / 9.96 | 10.58 | 130.9 (−92.5%) | 15.48 / 15.52 | 15.83 | 158.6 (−90.2%) |
| Thin disk, elevation 0.20 | scalar | 6.32 / 6.29 | 6.65 | 75.0 (−91.6%) | 13.03 / 12.94 | 13.59 | 98.9 (−86.8%) |
| Warped disk, spin −0.9, polarized, elevation 0.40 | single | 11.50 / 11.36 | 12.32 | 92.2 (−87.5%) | 18.22 / 18.28 | 19.14 | 126.4 (−85.6%) |
| Hot flow close-up, polarized | single | 16.19 / 16.18 | 17.59 | 190.8 (−91.5%) | 28.54 / 28.44 | 29.52 | 242.7 (−88.2%) |
| Binary | generic | 15.75 / 15.59 | 16.07 | 35.1 (−55.1%) | 29.56 / 29.77 | 30.37 | 83.9 (−64.8%) |

p95 is run 1's. The pinned kernel's p95 is 3–24% above its median, against 2–9% for the current kernels.

**Ray cost.** From the diagnostics pass at 960×540. An attempt is an accepted step or a rejected one. Warp lane efficiency is the attempts made divided by the attempts each warp's lanes would make if every lane ran as long as the warp's costliest ray, in the launch's own block shape.

| Scene | Accepted steps | Rejected | Attempts per ray p50 / p90 / p99 / max | Costliest 1% of rays | Warp lane efficiency | Exits other than escape |
|---|---:|---:|---|---:|---:|---|
| Thin disk, elevation 1.22 | 46.2M | 1.28% | 86 / 110 / 149 / 1,337 | 2.1% | 93.8% | early capture 6,811, opaque 183, near-critical 4 |
| Thin disk, elevation 0.20 | 45.5M | 1.82% | 86 / 107 / 146 / 1,089 | 2.0% | 95.0% | early capture 6,565, horizon 9, near-critical 4 |
| Warped disk, spin −0.9 | 45.6M | 1.81% | 87 / 106 / 148 / 1,171 | 2.0% | 94.6% | early capture 6,448, near-critical 12, horizon 3, stagnation 1 |
| Hot flow close-up | 49.0M | 1.95% | 90 / 114 / 168 / 1,564 | 2.8% | 90.5% | early capture 24,929, opaque 93, near-critical 26 |
| Binary | 48.9M | 1.05% | 87 / 116 / 235 / 935 | 4.1% | 96.4% | stagnation 5,123, opaque 56 |

At 400×300 the shares are similar: the costliest 1% of rays make 2.0–4.2% of the attempts, and warp lane efficiency is 83.9–94.1% (lowest for the hot flow close-up).

What this says about the next steps:
- **Long tails are small.** No scene loses more than about 10% of its lanes to waiting on slower rays in the same warp (16% for the 400×300 close-up). That bounds what the long-tail scheduler (P1.5) can recover by regrouping rays, before its own compaction and relaunch costs. "Long-tail scheduling" below found that the tail is the slowest rays' latency instead.
- **Time goes into each step.** The scenes take 86–90 attempts per median ray, yet the polarized hot flow takes 1.8 times as long as the thermal thin disk at 960×540. The difference is per-step work: polarized transport and plasma sampling.
- **The binary stagnates.** 5,123 binary rays (1.0%) end in affine stagnation, against at most 1 per single-hole frame.

**Nsight Systems timeline.** Nsight Systems 2026.6.1 traced CUDA and D3D12 in the real app on the `--profile-renderer` close-up (`bh_geodesic_single`):

```
nsys profile --trace=cuda,dx12 --sample=none --cpuctxsw=none -o target/nsys/profile-renderer target/release/black_hole.exe --profile-renderer
```

After the first 12 frames, the geodesic kernel takes 15.06 ms at the median (p95 17.80 ms). Kernels start 17.66 ms apart (p95 21.80 ms). Between one geodesic kernel ending and the next starting, CUDA is idle for 2.60 ms at the median (p95 3.97 ms). Accumulation takes 2 µs per frame and the device-to-host copy 20 µs; the 15 ms that the readback call spends is the host waiting for the kernel. So the geodesic kernel is 85% of the frame. Overlapping or sharing the display handoff (P2.6) could recover at most the 2.6 ms idle gap, about 15% of this frame.

**Nsight Compute.** Nsight Compute 2026.4 profiled one launch at 960×540 with `--set full`, after warm-up (round 10 of `baseline_profile`). Each kernel was replayed 47 times, so its duration is a little longer than in the timed runs.

| Metric | Thin disk (`scalar`) | Hot flow close-up (`single`) | Binary (`bh_geodesic`) |
|---|---:|---:|---:|
| Duration | 16.57 ms | 29.12 ms | 29.75 ms |
| Registers per thread | 218 | 236 | 255 |
| Theoretical / achieved occupancy | 16.7% / 16.1% | 16.7% / 16.1% | 16.7% / 15.4% |
| Active / eligible warps per scheduler | 1.95 / 0.61 | 1.95 / 0.63 | 1.90 / 0.72 |
| Cycles with no eligible warp | 54.8% | 53.6% | 50.1% |
| Warp cycles per issued instruction | 4.31 | 4.20 | 3.80 |
| Compute (SM) throughput | 34.5% | 40.3% | 43.9% |
| FP32 share of peak | 13% | 16% | 20% |
| FP32 fused / unfused instructions | 2.08G / 1.62G | 5.10G / 3.78G | 5.64G / 4.73G |
| DRAM throughput | 1.2% | 1.3% | 1.3% |
| L1 / L2 hit rate | 99.2% / 83.9% | 99.8% / 90.7% | 99.2% / 98.8% |
| Local-memory (spill) requests | 0 | 0 | 325M (85% of L1 sectors) |
| Branch efficiency | 99.7% | 99.6% | 99.9% |
| Active threads per warp | 28.9 | 27.2 | 30.1 |
| SM workload imbalance (busiest SM above mean) | 22.5% | 11.8% | 9.1% |

What it shows:
- **The kernels are latency-bound by register-limited occupancy.** Registers allow 2 warps per scheduler out of 12. On average only 0.6–0.7 of them are ready to issue, so a scheduler issues on fewer than half its cycles. The largest named stall is waiting on fixed-latency results (1.1–1.5 of the 3.8–4.3 cycles per instruction). Memory bandwidth is not a factor: DRAM runs at about 1% and L1 serves over 99% of loads.
- **Divergence is small.** Branch efficiency is above 99.6% and 27–30 of 32 threads are active per warp. This agrees with the 84–96% warp lane efficiency from the diagnostics pass.
- **43–46% of FP32 instructions are unfused multiplies and adds.** Rust code does not contract `a * b + c` into an FMA. Nsight estimates that fusing the pairs would raise FP32 throughput by up to 21–23%, a 4–6% kernel speedup. It would change results in the last bit, so it needs the same image and reference checks as any numerical change.
- **SMs finish unevenly.** The busiest SM runs 9–22% longer than the average SM. This is the frame's tail: the last blocks to start hold the GPU while other SMs sit idle. It is the one long-tail cost these measurements show. It points to finer-grained work distribution at the end of the frame, rather than to regrouping rays within warps (P1.5).
- **The binary spills.** `bh_geodesic` at 255 registers puts 85% of its L1 traffic into local memory. The traffic stays in L1 (99.2% hit rate), but the spill instructions still have to be issued.
- **No source-line attribution.** cuda-oxide emits no line information, so Nsight cannot map stalls to source lines.

The reports are in `target/ncu/*.ncu-repz`. Profiling counters on Windows need administrator rights, so `ncu` was run elevated.

Not covered:
- **The rest of the benchmark matrix** (acceptance checklist): spins ±0.99 and ±0.999, Schwarzschild, the distant view at radius 160, and near-horizon views.
- **The EHT snapshot**, which is timed separately and is not part of this harness.
- **The app's sky texture.** The test sky has two texels, so sky lookups are cheaper than in the app. The Nsight Systems timeline does use the app's sky.

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
