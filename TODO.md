# Black Hole Simulator — Road to 10/10

## Physics Accuracy
- [ ] Fix geodesic integrator: replace mislabeled "RK4" (currently Euler) with true 4th-order Runge-Kutta
- [ ] Add adaptive step size to geodesic integration (smaller steps near event horizon, larger far away)
- [ ] Fix multi-object physics inconsistency: light bending currently only uses Sag A* metric; other massive objects affect Newtonian gravity but not ray paths

## Rendering Quality
- [ ] Increase native compute shader resolution (200×150 → at least 800×600), or make it configurable at runtime
- [ ] Add temporal anti-aliasing / accumulation buffer for smoother output

## Robustness
- [ ] Add NaN/infinity guards in geodesic shader (divide-by-zero risk when sin(θ) ≈ 0 near poles)
- [ ] Guard against log(0) in spacetime grid displacement calculation

## Configurability
- [ ] Remove hardcoded aspect ratio (800/600 in `src/camera.rs:75`) — derive from window size
- [ ] Remove hardcoded FOV (60° in `src/camera.rs:72`) — expose as runtime parameter
- [ ] Remove hardcoded resolution in compute pipeline — derive or expose via config

## Performance
- [ ] Cache spacetime grid vertices; only recompute when object positions change
- [ ] Consider adaptive LOD for grid density based on camera distance

## Visual Fidelity
- [ ] Improve accretion disk: add thickness / 3D volume instead of infinitesimally thin equatorial plane
- [ ] Add Doppler shift / blueshift coloring to accretion disk based on orbit velocity
