# Changelog

## Unreleased

### Added

- `black_hole::separated`, a binary64 reference for null geodesics around an isolated Kerr hole, solved from E, L and Q. It computes each ray two independent ways, elliptic closed forms and quadrature, which agree with each other and with a binary64 integration. `gpu_escapes_match_the_separated_solution` checks every pixel of single-hole frames against it. There are no classification disagreements outside the near-critical band and the opaque disk. The median escape-direction error is 2e-7 rad and the 99th percentile is below 8e-6 rad (`RENDERING_PERFORMANCE.md`).
- `--profile-renderer` runs a windowed close-up benchmark and reports the median and 95th-percentile frame intervals for a still and an orbiting camera. It then writes per-ray diagnostics (steps, rejections, exit reason, sky direction, Stokes values) to `target/renderer-rays*.csv` and checks that the diagnostic image matches the normal kernel.
- Single-hole early capture ends inward rays once a binary64 check of the Kerr radial potential rules out a turning point before the horizon. The Lean lemmas in `verification/BlackHole/KerrCapture.lean` prove that check in exact arithmetic. It is on by default (see Changed); `--full-trace` turns it off. Far-field steps take larger outward steps outside a sphere enclosing the disk and the hole; they are on by default (see Changed). `RENDERING_PERFORMANCE.md` records the measurements.
- GPU regressions for early capture against the analytic equatorial Kerr potential at seven spins up to the ±0.995 guard edge, and for near-critical Schwarzschild classification with a disk inner edge.

- A swarm of up to 4096 small bodies on prescribed circular orbits (K, or the Swarm panel row), drawn where each was when the light reaching the camera passed it. A space-time BVH over 40 time slices renders the same image as brute force bit for bit. Together with a radial check that drops steps which cannot reach the belt, it cuts the 4096-body frame from 4.3 s to 0.13 s on an RTX 4090, the same as a frame without the swarm. GPU tests check the intersection against exact orbits and show that an empty swarm leaves the image unchanged bit for bit.
- Experimental RT-core swarm queries, switched with the RTX panel button (or `--optix` at startup) in builds with the `optix` cargo feature, which needs the OptiX 9.1 SDK headers at `OPTIX_ROOT`. The render pass queues each step that can reach the belt, one OptiX launch over a motion GAS tests them all, and a fix-up pass applies each pixel's earliest hit. The image matches brute force bit for bit. It is no faster than the BVH (145–199 ms per frame against 122–203 ms, from 256 to 16,384 bodies), so the BVH stays the default. Details are in `RENDERING_PERFORMANCE.md`.

### Changed

- Early capture now bounds the Kerr radial potential piecewise, from its exact Taylor expansion on 1, 2, 4 or 8 pieces between the horizon and the ray, instead of with one bound that held P at its smallest and Δ at its largest. Captured rays that skim the photon orbit were taking over 1,000 steps before the old bound could rule out a turning point; they now end as soon as they pass within 0.05 of the disk's inner edge. Frames are 31–37% faster in the default 400×300 views and 25–39% at 960×540, the windowed close-up drops from 22.1 to about 16.3 ms, and edge-on views are within noise or 8% faster. Images are bit-identical to the full trace. `null_radial_positive_near` in `verification/BlackHole/KerrCapture.lean` proves the bound, and the GPU certificate and its CPU twin check it in interval binary64.
- Large single-hole frames now render the tiles that were costliest in the previous frame first (checklist P1.5). The frame's tail is the latency of a few hundred near-critical rays of over 1,000 steps each, and starting them first overlaps that latency with the rest of the frame. The kernels record each tile's most iterations, and two small kernels sort the tiles on the GPU. This applies when the grid has at least 8 waves of resident blocks: on an RTX 4090, 640×480 and up. Frames are up to 10% faster at 640×480 (one of four scenes within noise), 6–24% faster at 960×540 and 13–22% at 1280×720; images are bit-identical. The default 400×300 view keeps row order: starting the slowest rays early made it up to 10% slower. A hybrid scheduler that suspended rays after N iterations and resumed the survivors in a second kernel was 7–43% slower at every N from 64 to 512, and was removed.
- Single-hole rays now travel analytically outside the disk's enclosing sphere (at least r = 16; checklist P1.8). The separated Kerr solution carries each ray from the camera back to that sphere or, through its radial turning point, to the sky sphere, and carries every ray that leaves the sphere to the sky. It uses Gauss–Legendre sums in 1/r, a t² substitution at radial turning points, and an exact great-circle polar motion with an RK4 spin correction, all with only square roots. Steps fall by 41–42% in thin-disk views. Production kernels are 8–14% faster at 960×540 and within −8.1% to +3.5% at 400×300, and the hot flow is within ±3.2%. Two photon-ring pixels per frame change by up to 0.01; 99.99% of the others change by less than 1e-4. The CPU twin `separated::vacuum_leg` is within 4.6e-7 rad of the binary64 reference, and on the GPU the reference errors and classification are unchanged. `--no-analytic-legs` (replacing `--no-analytic-escape`) restores the numerical trace for one release. Experimental `--band-legs` also runs legs inside the sphere until the band around a thin disk: steps fall by another 55–62%, but the frame is no faster, because each binary64 leg costs about as much as 20 steps.
- Single-hole rays now take far-field steps by default (checklist P1.8). Outside a sphere enclosing the disk and the hole, an outward ray's step may grow to 28% of its radius, up to 192 gravitational radii. Steps fall by 34–42% across six views. No ray changes its exit, disk emission is unchanged bit for bit, and sky directions move by at most 5.8e-7 rad; the error against the separated reference is unchanged. Production kernels are 8–21% faster at 960×540 and within −4.6% to +2.5% at 400×300. `--no-far-field` replaces `--experiment-far-field` and restores the capped steps for one release.
- Disk transfer no longer sets the geodesic step. Each step's plasma is split into constant cells of min(H/4, 0.05 r), up to 8 per step, and each cell samples a cubic Hermite interpolant of the Dormand–Prince step. Before, the disk limited the step itself to H/4 and each step took one midpoint sample. Accepted steps fall by 24–35%. Production kernels are 5–16% faster at 960×540 in a same-process A/B and within ±4.4% at 400×300. The exception is the hot flow at 400×300, which is 13–17% slower because its cells are now shorter. In exchange its p99 intensity error is 8 times smaller. Against a reference with cells 16 times shorter, the thin-disk Stokes errors match the coupled scheme. The p99 relative intensity error now meets the 1e-4 target in every tested scene, with no exit change and no pixel change above 1/255. Escape directions also improve: near the pole the p99 error against the separated solution halves. `--coupled-transfer` restores the old scheme for one release. Fixed-path tests check the renderer's cell compositing against a binary64 solution. They found and fixed a cutoff that skipped Faraday rotation inside cells with w·ds < 1e-5. Details are in `RENDERING_PERFORMANCE.md` (checklist P1.9).

- Single-hole scenes now render with specialised kernels. `bh_geodesic_single` computes only one source and has no register spills. It renders the same image bit for bit and makes the windowed close-up about 11% faster (18.3 / 16.9 to 16.3 / 15.0 ms, still / orbit). When neither the polarization view nor the hot flow is on, `bh_geodesic_scalar` also skips screen-vector transport, which thermal intensity never reads. Its ray kernel is 29–30% faster than the generic one on the thin-disk benchmark, with pixel values within 1/255 of it and the same step count to 0.01%. `specialised_kernels_match_bh_geodesic` checks both across spins, disk models, polarization views and elevations (`RENDERING_PERFORMANCE.md`).

- Binary-scene ray launches use 8×8 blocks instead of 16×16. That is 2.5–6.7% faster, and images are bit-identical. `launch_tuning_sweep` also shows that register caps, a maximum-L1 carveout and a different PTX target do not help the ray kernel (`RENDERING_PERFORMANCE.md`).

- The geodesic right-hand side now contracts each Kerr–Schild source's metric derivatives with the ray directly, without building three 4×4 derivative matrices. With one or two holes, each source is computed once per stage for both the metric and the right-hand side. The Dormand–Prince kernel is 8–12% faster in `dp45_controller_benchmark`, and the windowed close-up drops from about 20.0 / 18.3 ms to 18.4 / 16.8 ms (still / orbit) on an RTX 4090. Images are unchanged in every GPU image test. `structured_geodesic_rhs_matches_the_matrix_form` checks the new form against the matrix form and a binary64 reference. `verification/BlackHole/CudaStructuredRhs.lean` proves the two forms equal in exact arithmetic. The proved binary32 bound now covers only the matrix reference form.

- Guarded early capture is now the default in every render kernel. With Dormand–Prince, the windowed close-up drops from about 91 ms to 20 ms per frame on an RTX 4090, and the slowest 5% of rays fall from 56.9% to 7.8% of accepted steps. The guard still falls back to the full trace for binaries, |a| > 0.995, shifted or non-black holes and tilted spins. `--full-trace` replaces `--experiment-early-capture`. GPU tests require bit-identical images with and without it across 8 spins, all disk models, three camera elevations, three polarization views, the binary, and the swarm (brute force, BVH and OptiX at 256–4,096 bodies), and trace sampled early-captured pixels in binary64 on the CPU to confirm capture. Each capture must also pass an outward-rounded interval certificate of the guard's hypotheses for the exact stored state, with the inward direction taken from the state's momentum. `black_hole::certified::capture_certified` checks the same hypotheses on the CPU and confirms every GPU capture in the tests. The certificate costs about 2% of frame time.

- The ray controller is now an embedded Dormand–Prince 5(4) step in every scene, instead of step-doubling RK4. It needs 6 metric evaluations per accepted step instead of 11, and the windowed close-up benchmark drops from about 175 ms to 92 ms per frame on an RTX 4090. Near-critical Schwarzschild trajectory errors fall about threefold, and EHT snapshot Stokes I L2 error goes from 0.719% to 0.704%. `--rk4-controller` restores RK4 for one release. `verification/BlackHole/DormandPrince.lean` proves the tableau's order conditions, and `tests/dormand_prince_tableau.rs` checks the kernel's coefficients against it. `RENDERING_PERFORMANCE.md` records the image differences and the swarm timings. The EHT snapshot test writes `image-gpu.f32` with the new controller and `image-gpu-rk4.f32` with RK4.

- Near-critical rays now end unresolved, with no sky and diagnostic exit `near_critical`, once they have swept more than 14 rad around the hole, instead of being guessed captured or escaped. The Schwarzschild classification regression now checks RK4 and Dormand–Prince at step factors 0.11, 0.12 and 0.13. It requires zero wrong definitive answers, and it requires every ray with |margin| > 1e-4 to resolve. In the close-up benchmark 7 of 120,000 pixels fall in the band.

- The RK4 controller shares the initial derivative between the coarse step, the first half-step and every retry. It also returns the accepted endpoint metric to the renderer instead of recomputing it. Plasma samples and endpoint validity checks skip the metric derivatives they never read. Output is unchanged bit for bit.
- Single-source Kerr scenes launch with 32×4 CUDA blocks, so that each warp traces one scanline. With the RK4 reuse, the single-hole thin-disk ray kernel dropped from 184 to 123 ms at 400×300.
- Updated rstest to 0.29.0.
- The swarm's slice BVHs are now cached on a grid of absolute coordinate time, 2 r_g/c apart, instead of rebuilt every frame. Each tree spans 22 r_g/c instead of 20, so it holds every slice that ends in its last grid step. A frame builds and uploads only the trees new to it (about one every 6 frames at 60 fps) into fixed device slots, and builds several at once on Bevy's compute pool. The host cost of a 4096-body frame falls from 17.7 ms to 0.25 ms on average (0.8 ms on frames that build a tree). Turning the swarm on, or changing the body count or spin, builds all 40 trees in about 4 ms. The GPU render is within noise (10.7 ms against 10.1–10.5 ms) and still matches brute force bit for bit.
- CI checks formatting with `cargo fmt --check` and `rustfmt --check` on the tool crates (except `tools/cuda/kernels.rs`, whose hash pins the checked-in PTX). The Python verification job installs its dependencies with uv.

### Fixed

- The Mino time to the disk's band (`--band-legs`, and its CPU twin `separated::escape::band_time`) came from one 8-point Gauss–Legendre sum, which missed the near pole of the polar potential for nearly polar rays with small η by up to 5e-3 relative. It is now the closed form F(φ, k) / √D through Carlson's R_F in binary32, with the addition theorem for rays heading to the equator. Over 200,000 sampled rays the largest error against a binary64 reference falls to 3.2e-7, for disks down to H/R = 5e-4. `gpu_escapes_match_the_separated_solution` now also runs with band legs: no classification disagreements, median direction error 1.2–1.9e-7 rad and p99 at most 6.4e-6 rad. Default rendering does not use band legs and is unchanged.
- `bridge_scene_renders_and_switches_back` failed because its app had the UI but not the swarm resource it reads.
- The 2D background camera also drew the gizmos, in pixels, as a tiny copy of the spacetime grid at the screen centre; gizmos now draw only in the 3D camera.
- The FPS counter refreshes twice a second instead of every frame, so it can be read.

## 0.5.0 - 2026-11-08

### Added

- Wormhole views, cycled with W: a CUDA ray-traced Ellis wormhole between two skies with an evolving pressureless test-dust pulse, and an Einstein–Rosen bridge embedding diagram stepped in Kruskal time. Lean proofs cover the Ellis ray equations, the dust continuity solution, and the bridge embedding and its nontraversability; `verification/ellis.md` and `verification/einstein-rosen.md` list coverage and limits.
- Exact-rational property tests for certified arithmetic, table-driven certification cases, and GPU regression cases for redshift clamping in the truncated hot flow and slim disk.
- The translation-validation test also checks naga's SPIR-V backend for every compared kernel, by reading the written SPIR-V back with naga's SPIR-V front end. A GPU test checks the proved `geodesic_rhs` error bound on the driver, with exact values taken from the Lean fixture.
- Unconditional WGSL error bounds for `heatmap_color` (every input) and `tonemap` (input error at most 1/10): their safety conditions are now proved instead of assumed. A matching lower bound shows that near a branch threshold no all-input error bound can be smaller than half the branch jump.
- A checked interval evaluator in Lean decides the WGSL safety conditions on input boxes. It proves closed-form domains for `polarization_color`, `spin_scale` and `spatial_unit`, and neighbourhoods of a Kerr configuration for every output of `add_kerr`, `screen_frame` and all four `sample_plasma` models. These hold for every association of the sums, and of the products and quotients with each factor kept in its role, which WGSL lets an implementation choose.
- Translation validation of the naga front end for `geodesic_rhs`, `atan_poly`, `tonemap`, `heatmap_color`, the polarization hue, `spatial_unit`, `screen_frame`, `sample_plasma` (all disk models), `atan2_arith`, `kerr_radius`, `sincos` and `transfer_phi` (linked to their hand-proved bounds), `faraday_rotation`, `polarized_cell` and `add_kerr`: a Rust test symbolically executes naga's IR, including branches and loops, and compares it with fixtures that Lean proves equal to the modeled kernels. It corrected two models: `geodesic_rhs` had `-0.5*(m.inv*x)` where the shader computes `(-0.5*m.inv)*x`, `heatmap_color` channel 0 subtracted zero, and `add_kerr` associated `2h·ell_i·ell_j` differently from `outer`.
- Skybox, polarization hue and warped-disk shading no longer call `atan2`, `acos` or `cos`, whose WGSL accuracy is unspecified on inputs these paths reach. The skybox uses an arithmetic `atan2_arith` with a proved 128u bound and a GPU accuracy test.
- Certified Kerr rays: `verification/` proves (`RayCertificate.certified_ray`) that an accepted certificate fixes the exact ray from a camera. It covers physical initial data, existence and uniqueness over the certified interval, the capture/escape verdict, a final-state enclosure, and binary32 direction and redshift within 10⁻⁶. `lake exe certify` runs the proved checker as compiled Lean and reports uncertifiable rays as unresolved.
- WGSL error frameworks for polynomial and general programs (division, roots, floors, clamps, branches, `exp`/`log`/`pow`/`tanh` and inherited builtins), applied to `geodesic_rhs`, the RK4 arithmetic, `add_kerr`, `screen_frame`, `sample_plasma` and the display kernels. Most bounds hold under explicit safety hypotheses. Counterexamples show that the unspecified `atan2`/`acos` accuracy cases leave the unchanged skybox, polarization-hue and warped-disk paths without a useful bound.
- Uniform nonlinear Kerr RK4 defect bounds, automatic stage containment, finite-time continuation in compact nonsingular phase regions, and fixed/variable-step trajectory certificates that derive numerical-region containment from the error budget. Numerical constants and production roundoff certification remain open.
- Uniform higher-derivative and Lipschitz existence proofs on compact Kerr exterior phase regions; full-field and continuous screen-growth bounds; nonlinear RK4 stage-containment, perturbation-growth and accumulated-error proofs with explicit truncation/roundoff hypotheses. Production global accuracy remains open.
- Lean 4 verification package, pinned Mathlib dependencies, axiom audit, independent kernel replay, and a GitHub Actions proof workflow. Exact-real results cover single-source Kerr vacuum curvature, metric derivatives, ISCO properties, camera frames, continuous transport, selected transfer models, and numerical bounds. Checked counterexamples document limits of binary superposition and exact discrete conservation.
- Reproducible EHT snapshot acquisition/validation and pinned ipole reference workflows, with input hashes, physical conventions, measured results, and an explicit ledger of remaining proof obligations.
- Optional WESL kernels for MKS snapshot interpolation, thermal synchrotron coefficients, polarized absorption/Faraday transfer, and a full 160x160 hybrid CPU/GPU image benchmark. Binary64 outer-ray transport is checked independently before handing off to the GPU.
- Expanded numerical and shader regressions, including Schwarzschild trajectory refinement, adaptive-step rejection, local snapshot/transfer comparisons, and full-image diagnostics. Validation now includes 370 default Rust tests, seven Python tests, and separately enabled GPU checks.

- Lean proofs for binary32 horizon/ISCO error bounds, unit and timing consistency, the energy-drift counterexample, equatorial radial stability, the full polarized matrix-exponential cell, a reassociation-independent WGSL summation bound, the WGSL `kerr_radius` error bound, the stable Faraday-cell series, and fourth-order local consistency of RK4 for the full nonlinear Kerr geodesic/screen field. Exhaustive all-input binary32 tests for the horizon, ISCO and `cbrtf`. GPU tests (lavapipe-compatible) showing the adaptive controller misses the trajectory targets and misclassifies near-critical captured rays.
- WGSL floating-point bounds for `transfer_cell`'s matrix exponential (`polarized_transfer.wesl`). For every cell the shader accepts, the 12-term loop's exponential is within 16u + 10⁻²⁰ of exp(−h·k) and its source within 16u·h‖j‖ plus a flush-to-zero term. Running bounds cover the squarings and the returned Stokes vector.
- The Lean kernel now checks that naga's own expression trees, recorded before any normalization from the WGSL front end and from the SPIR-V round trip, are reassociations of the models for every translation-validated kernel (`NagaFixture`, with a checker proved sound). The domain theorems that hold for every reassociation therefore apply to the trees naga builds; the comparison's normalizing store is no longer trusted for that statement.

### Fixed

- Serialized the memory-heavy naga fixture proof builds alongside the curvature proofs to reduce swap pressure behind the Lean CI timeout.
- The WGSL safety conditions required both sides of a branch to be safe. Every `sample_plasma` error bound was therefore vacuous: `disk_radius`'s untaken branch divides by a floor that its own error exceeds everywhere on the disk. Only the branch taken is now required, which is all the error proof uses.
- `kerr_isco_radius_rg` lost up to 4731 binary32 units of relative accuracy near zero spin (about 2.8e-4 at |a| = 5e-4). It now uses a cancellation-free form of the Bardeen formula (maximum 17 units over all inputs).
- `polarized_cell` cancelled catastrophically for small optical depth with Faraday rotation (e.g. sin-component integral 1.3e-3 instead of 5.0e-6). Both cell integrals and `absorption_integral` now use one complex `(1 - exp(-z))/z` with a series branch.
- CI proof builds ran out of runner memory; the workflow now adds swap, logs memory, caches the project build and queues concurrent pushes.

### Changed

- Added GoogleTest matchers for clearer numerical assertion failures and documented GPU-dependent rounding differences in the fluid-energy sweep.
- Migrated production and test shaders from WGSL source files to WESL, updated Bevy asset paths, and added shared WESL compilation/validation helpers. Pinned verification files and WESL sources to LF endings for WSL scripts and stable provenance hashes.
- Replaced null-residual-only step acceptance with RK4 step doubling over position, momentum, and transported screen, retaining null checks and rejecting invalid intermediate stages.
- Updated Bevy to 0.20.1, proptest to 1.12.0, and rstest to 0.28.0; added WESL 0.6.0 for shader tests. Refreshed README shader references and the Bevy badge.

### Verification limits

- All 25,600 benchmark rays resolve, and the finest run's integrated intensity differs from the refined ipole reference by 0.077%. Its intensity image L2 error is 0.688%; the requested pixel-accuracy targets remain unmet, and refinement has not established convergence. The image comparison reports this failure explicitly.
- The interactive renderer still uses prescribed plasma. Exact-real theorems and sampled GPU comparisons do not establish all-input floating-point correctness, compiler equivalence, global numerical error bounds, or an evolved relativistic binary solution.

## 0.4.0 - 2026-10-10

### Added

- Screen-basis parallel transport, illustrative synchrotron Stokes emission, scalar absorption, and exact constant-cell Faraday rotation/conversion. Added `P` and panel controls for polarization views, observing frequency, and transfer strengths.
- GPU numerical regressions using the actual shader functions, plus intensity/polarization render smoke checks. Documented scientific limits and references in README.
- Test suite expanded from 34 to 273 tests, using `rstest` case tables and `proptest` properties (for example momentum conservation, binary orbit geometry, spin clamping, Halton jitter, and UI parameter bounds). Covers simulation input, uniform packing, accumulation resets, camera and gamepad input, and every panel button.
- cargo-mutants configuration (`.cargo/mutants.toml`); every surviving mutant is either equivalent or only changes log output.

### Changed

- Replaced separate Kerr and weak-field binary ray marchers with a shared Cartesian Kerr-Schild Hamiltonian RK4 solver, analytic metric derivatives, null-residual rejection, and physical horizon excision.
- Binary mode now uses a frozen, unboosted superposed metric and renders the circumbinary disk. This is an approximate separated-binary model, not a relativistic merger solution.
- Updated Bevy to 0.20.0: `ExtractResource` types declare `#[extract_app(RenderApp)]`, compute pipelines set `constants`, and panel buttons use `ui_widgets::Button` with `Hovered`/`Pressed` instead of the removed `Interaction` button.
- Orbital camera input now runs in `PreUpdate` and GPU uniform syncing in `PostUpdate`.

### Fixed

- Accumulation resets requested by the iteration, heatmap, skybox, disk and panel controls could be lost. The camera cleared `is_moving` in the same unordered `Update` set where those systems set it, so old frames could blend into the new view.
- Fixed both reported collapsible-if Clippy warnings and the current toolchain's array-chunk lints in the GPU smoke test.

## 0.3.0 - 2026-09-09

### Added

- Mass-independent `kerr_horizon_radius_rg` and `kerr_isco_radius_rg` library functions.
- Gravity timing regression checks at 30, 60, and 120 rendering FPS, WGSL validation, and an optional headless GPU test for single-hole and binary scenes.

### Changed

- Camera, scene objects, spacetime grid, and GPU ray tracing now use gravitational units (`G = c = M = 1`). Distances are in `r_g`; object masses are fractions of the total black-hole mass. Disk controls still use Schwarzschild radii (`r_s = 2 r_g`).
- Newtonian gravity advances one gravitational time unit per application second using Bevy's fixed 64 Hz timestep. Convert simulation time to physical seconds using `GM/c³`; binary motion retains its prescribed 18-second visual orbit.
- Replaced Reinhard tone mapping with an ACES filmic curve approximation, applied after combining disk and background lighting.
- Added bilinear HDR skybox filtering with longitude wrapping and pole clamping.
- Updated Bevy to 0.19.1 and adapted compute rendering and text sizes to its APIs. Updated bytemuck to 1.25.2 and added Naga 30.0.1 for shader validation.

### Fixed

- Newtonian gravity no longer depends on rendering framerate.
- Removed the mass multiplication that overflowed in the previous SI gravity calculation; massless test particles can also accelerate correctly.
- Corrected the documented extremal retrograde ISCO limit to `9 M = 4.5 r_s`.

### Compatibility

- Existing `kerr_horizon_radius` and `kerr_isco_radius` functions retain their Sagittarius A* metre-based results.
- Scene coordinates and simulation timing have changed. Code using internal scene values must use the new gravitational units.
