# Changelog

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
