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
- [ ] Consider adaptive LOD for grid density based on camera distance

## Visual Fidelity
- [ ] Improve accretion disk: add thickness / 3D volume instead of infinitesimally thin equatorial plane
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
