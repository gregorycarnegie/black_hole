# Changelog

## 0.5.0 - 2026-11-08

### Added

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
