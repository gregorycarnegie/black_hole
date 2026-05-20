# Black Hole Simulator — Road to 10/10

## Physics Accuracy
- [x] Fix geodesic integrator: replace mislabeled "RK4" (currently Euler) with true 4th-order Runge-Kutta
- [x] Add adaptive step size to geodesic integration (smaller steps near event horizon, larger far away)
- [ ] Fix multi-object physics inconsistency: light bending currently only uses Sag A* metric; other massive objects affect Newtonian gravity but not ray paths

## Relativistic Effects
- [x] Kinematic Doppler shift (fully relativistic: transverse Doppler via γ term)
- [x] Gravitational redshift: sqrt(1 − r_s/r) applied at disk emission point
- [x] Relativistic beaming: D³ brightness scaling
- [x] Fix orbital velocity formula: using sqrt(r_s/2r), correct is sqrt(r_s/(2r−2r_s))
- [x] Fix inner disk edge: r1 = 2.2 r_s is inside ISCO; should be 3 r_s for Schwarzschild
- [x] Fix Doppler ray direction: use actual photon direction at emission, not straight line to camera
- [x] Multiple disk images / photon ring: currently break on first equatorial crossing; secondary images from photons that orbit the BH are missing
- [x] Temperature-based disk color: Novikov-Thorne T(r) ∝ r^(−3/4) blackbody spectrum instead of heuristic gradient
- [ ] Kerr metric (frame dragging): Schwarzschild assumes zero spin; Kerr moves ISCO inward, asymmetric light bending, ergosphere

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
