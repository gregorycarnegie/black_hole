# Black Hole Simulator — Road to 10/10

## Physics Accuracy
- [x] Fix geodesic integrator: replace mislabeled "RK4" (currently Euler) with true 4th-order Runge-Kutta
- [x] Add adaptive step size to geodesic integration (smaller steps near event horizon, larger far away)
- [ ] Fix multi-object physics inconsistency: light bending currently only uses Sag A* metric; other massive objects affect Newtonian gravity but not ray paths
- [x] Fix `orbital_beta_kerr` retrograde denominator: formula uses `rho^(3/2) + |a|` for all spins; retrograde (spin < 0) needs `rho^(3/2) - |a|` (latent bug, no effect at KERR_SPIN = 0.82)
- [x] Simplify near-horizon step size: `near_horizon_scale` floor of 0.1 is always overridden by the `clamp` minimum of 0.25 — dead code in `geodesic.wgsl` main loop

## Relativistic Effects
- [x] Kinematic Doppler shift (fully relativistic: transverse Doppler via γ term)
- [x] Gravitational redshift: sqrt(1 − r_s/r) applied at disk emission point
- [x] Relativistic beaming: D³ brightness scaling
- [x] Fix orbital velocity formula: using sqrt(r_s/2r), correct is sqrt(r_s/(2r−2r_s))
- [x] Fix inner disk edge: r1 = 2.2 r_s is inside ISCO; should be 3 r_s for Schwarzschild
- [x] Fix Doppler ray direction: use actual photon direction at emission, not straight line to camera
- [x] Multiple disk images / photon ring: currently break on first equatorial crossing; secondary images from photons that orbit the BH are missing
- [x] Temperature-based disk color: Novikov-Thorne T(r) ∝ r^(−3/4) blackbody spectrum instead of heuristic gradient
- [x] Kerr metric (frame dragging): Schwarzschild assumes zero spin; Kerr moves ISCO inward, asymmetric light bending, ergosphere

## Rendering Quality
- [x] Increase native compute shader resolution (200×150 → at least 800×600), or make it configurable at runtime
- [x] Add temporal anti-aliasing / accumulation buffer for smoother output

## Robustness
- [x] Add NaN/infinity guards in geodesic shader (divide-by-zero risk when sin(θ) ≈ 0 near poles)
- [x] Guard against log(0) in spacetime grid displacement calculation

## Configurability
- [x] Remove hardcoded aspect ratio (800/600 in `src/camera.rs:75`) — derive from window size
- [x] Remove hardcoded FOV (60° in `src/camera.rs:72`) — expose as runtime parameter
- [x] Remove hardcoded resolution in compute pipeline — derive or expose via config

## Performance
- [x] Cache spacetime grid vertices; only recompute when object positions change
- [x] Consider adaptive LOD for grid density based on camera distance
- [x] Accumulate bind groups recreated every frame: `AccumulateBindGroups { a_prev, b_prev }` is rebuilt and `insert_resource`d each frame; create once after textures are available, then only swap which group is dispatched (`src/compute/accumulate.rs:156-181`)
- [x] Geodesic bind group recreated every frame even though buffers/textures are usually stable; create once and recreate only when output texture or skybox changes (`src/compute/pipeline.rs:274-286`)
- [x] Unconditional uniform buffer writes: `objects_buf` and `disk_buf` are written every frame; first gate `sync_objects_uniform` / `sync_disk_config_uniform` on source changes, then write GPU buffers only when extracted values actually change (`src/compute/mod.rs:323-334`, `src/compute/pipeline.rs:260-271`)
- [x] Add a render-scale setting/preset; compute cost scales directly with traced pixel count, so this is likely the highest-impact runtime performance knob — press `[` / `]` to cycle 25 % → 50 % → 75 % → 100 %
- [x] Handle window resize for compute/accum/display textures and recreate affected bind groups only when texture handles change (`sync_compute_textures` in `src/compute/mod.rs`)
- [x] Add profiling/debug views before shader-limit tuning: on-screen FPS counter (`main.rs`) + GPU iteration-count heatmap toggle with H key (`geodesic.wgsl`, `src/camera.rs`)
- [x] Geodesic loop runs up to 10,000 iterations; profile with the iteration heatmap before lowering or making it configurable, since this affects photon-ring / multiple-image fidelity (`geodesic.wgsl:540`)
- [x] Micro-optimise Kerr helper paths: eliminate duplicate `metric_rho` calls in `orbital_kerr` and the redundant `kerr_lapse` / `spin_clamped` recomputation in `shade_disk` by returning an `OrbitalResult` struct (`geodesic.wgsl:437-446`)
- [x] Investigate filterable skybox sampling or a preprocessed skybox format; escaped rays currently do four `textureLoad`s for manual bilinear sampling (`geodesic.wgsl:476-509`)

## Visual Fidelity
- [x] Improve accretion disk: add thickness / 3D volume instead of infinitesimally thin equatorial plane
- [x] Add Doppler shift / blueshift coloring to accretion disk based on orbit velocity

## Test Coverage
- [x] Extract pure Kerr physics into `src/physics.rs` (no Bevy dep) to enable doc tests
- [x] Add doc tests to `kerr_horizon_radius` and `kerr_isco_radius`
- [x] Add unit tests: Schwarzschild limits, monotonicity, ISCO/horizon ordering at known spins
- [x] Add proptest invariants: horizon bounded by r_s, ISCO outside horizon, monotonicity over all valid spins
- [x] Add unit + proptest tests for `OrbitalCamera` (position radius, orthonormal frame, tan_half_fov)

## Precision
- [x] Use f64 for camera position accumulation on CPU; convert to f32 only when writing the GPU uniform

## Configurability
- [x] Expose KERR_SPIN and disk geometry (r1, r2) as runtime parameters (Q/E for spin, Z/X for outer radius)
