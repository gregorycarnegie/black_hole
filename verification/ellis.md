# Ray-traced Ellis wormhole

The optical mode implements the static Ellis metric, with a fixed throat radius a = 4 in arbitrary scene-length units. An evolving pressureless test-dust pulse passes through it. The geometry is prescribed and hypothetical, distinct from the nontraversable Einstein–Rosen bridge. Supporting exotic matter, gravitational backreaction, pressure, magnetic fields, stability, and polarization transport are not evolved.

The primary implementation reference is James, von Tunzelmann, Franklin & Thorne (2015), [Visualizing Interstellar's Wormhole](https://arxiv.org/abs/1502.03809): the Ellis metric in Eqs. (1)–(2), Hamiltonian in Eq. (13), and ray equations in Eq. (16). See also Ohgami & Sakai (2017), [Wormhole Shadows](https://arxiv.org/abs/1704.07065), for the Ellis metric and photon trajectories. This implements the Ellis example, rather than the movie's adjustable Dneg metric.

## Equations and implementation

Spherical symmetry puts each ray in a plane. With proper radial distance l, orbital angle φ, radial momentum p, and conserved angular momentum b, normalize the photon energy to 1:

```
ds² = -dt² + dl² + (l² + a²) dΩ²
H = (p² + b²/(l²+a²) - 1) / 2
dl/dλ = p
dp/dλ = b² l / (l²+a²)²
dφ/dλ = b / (l²+a²)
```

`src/ellis.rs` supplies the RHS and RK4 integration verbatim to both Rust and CUDA. Each pixel in `bh_wormhole` initializes p from the local radial sight component and b from the transverse component times sqrt(l²+a²), using the orthonormal orbital camera frame. The camera starts at l = 12 on the positive side; scrolling approaches the throat but does not move the camera through it. Rays themselves cross freely.

The solver advances with h = 0.025 (|l| + a), until it reaches |l| >= 400a on an outgoing leg. It projects the outgoing Cartesian velocity, including its remaining transverse component, onto the sky. Negative l selects the second sky; positive l selects the first. The render pipeline reuses its output textures, tone mapping, and temporal accumulation. B selects consecutive backgrounds from the existing skybox list. While the second asset loads, it temporarily uses the first sky on both ends.

The renderer checks the null-energy residual after every step, rejecting nonfinite states or absolute drift above 1e-4. Exhausted rays and inputs within relative distance 1e-5 of b = a are unresolved and shown in magenta. These checks are numerical diagnostics, not trajectory certificates. The unresolved critical band avoids claiming reliable classification arbitrarily close to the unstable photon orbit. Black-hole simulation and inputs pause in the other modes, allowing the wormhole image to accumulate while the camera is still.

## Matter evolution and radiation

The pressureless limit of Ohgami & Sakai's Eqs. (3.9)–(3.10) admits constant radial velocity. With A(l) = l²+a², v = -1/2 and gamma = 1/sqrt(1-v²), particle conservation becomes

```
∂t n + v ∂l n + 2lv n/A = 0
∂t(A n) + v ∂l(A n) = 0
n(l,t) = a² / [ A(l) (1 + ((l-vt-2a)/a)²)² ]
```

This is an exact characteristic solution: the weighted density A n translates at constant v without numerical diffusion or mass creation. The finite-mass pulse begins centered at l = 2a, has width scale a, and has no artificial spatial cutoff. Its coordinate center reaches the throat at t = 4a = 16, and later moves into the opposite exterior. The total particle number is proportional to gamma times the integral of A n over l. The absolute density and luminosity have arbitrary normalization, with no physical mass scale or calibrated emission spectrum assigned.

Time advances by one scene-time unit per elapsed application second while the Ellis view, matter, and playback are active. Space pauses/resumes; R rewinds to t = 0; D disables/enables the dust. The matter clock pauses in other views. Frozen matter images can accumulate temporally; changing density or visibility clears history so moving emission does not leave trails.

The ray tracer carries the past-directed affine time and samples density at t_emit = t_observer - λ. With backwards spatial radial tangent p, the future photon has k^l = -p, so its fluid-frame energy is nu_emit = gamma (1+v p). The dust four-velocity is timelike. Following the paper's nonabsorbing, flat-spectrum model, the observed contribution is proportional to the integral of n/nu_emit along the ray. A midpoint sample using an RK4 half-step is added over each full ray step. The fixed RGB spectral weights (1, 0.45, 0.12), multiplied by 0.2, are illustrative and added before tone mapping. There is no absorption, scattering, radiative cooling, or radiation feedback on the dust.

Light-travel delay is visible: from the default camera at l = 12, a radial view sees the throat crossing near observer time 28, although the coordinate-time center crosses at 16. The field is defined for all real emission times, including before the display clock's reset origin. This is ordinary test dust on the given metric; it does not supply or evolve the exotic stress-energy that supports the wormhole.

## Lean coverage

`BlackHole/Ellis.lean` proves over exact reals:

- The spatial angular coefficient l²+a² is positive for a > 0, with its minimum at the throat.
- The radial, radial-momentum, and angular equations are Hamilton's equations for H.
- The null-energy expression has zero derivative along a differentiable solution of the radial ODE.
- Unit local camera components initialize a null ray with b = r times its transverse component.
- Subcritical null rays (b² < a²) cannot turn radially; their radial speed has a positive lower bound. Turning points satisfy l² = b² - a².
- The throat supports the critical circular photon orbit b = a. Radial null geodesics with b = 0 cross the throat regularly. The radial force respects reflection symmetry.
- Eight exact rational RHS cases in `fixtures/ellis-rhs.csv` equal the specified equations. A strict macro parses literal rationals, and Lean's kernel checks the resulting equality. The rational force and angular rate are also proved to agree with the real formulas.

These proofs do not establish existence or stability of a physical wormhole, derive its supporting stress-energy, certify the full CUDA compiler, or bound the complete binary32 trajectory, finite sky cutoff, pixel filtering, or tone mapping. A small null residual alone does not certify angular accuracy. The ODE and fixture are manually related to the paper; the shared source and fixture tests reduce, but do not eliminate, that correspondence boundary.

`BlackHole/EllisDust.lean` additionally checks the normalized timelike four-velocity, the constant radial proper-time velocity in the pressureless Euler equation, the advected profile along characteristics, and the local relativistic continuity equation. It proves differentiability/nonnegativity of the pulse, its passage through the throat, positive Doppler-energy bounds, and the flat-spectrum n/nu emission identity. Eight rational density, weighted-density, and squared-Doppler-energy cases are kernel-checked in `fixtures/ellis-dust.csv`; the rational density specification is proved equal to the real formula. Global particle-number constancy is checked numerically; no formal improper-integral evaluation, backreaction theorem, or floating-point transfer error certificate is claimed.

## Executed checks

Host tests compare transmitted and returning ray angles to an independent double-precision orbit quadrature, including b/a = 0.999 and 1.001, with a 0.001-radian regression tolerance. They check both radial crossing directions, invalid inputs, critical rays, and step exhaustion. These sampled checks are not a uniform error bound.

GPU tests evaluate the kernel-checked RHS cases, compare classifications and trajectories to the host implementation, and exercise the production image kernel with different solid-color skies. Image pixels away from the critical band must select the sky predicted by the impact threshold. The complete offscreen scene test renders the sky textures and UI, exercises the three simulation modes, and writes `target/wormhole-smoke.png` and `target/bridge-smoke.png`. Mode changes and asynchronous sky loads reset temporal accumulation.

Dust tests compare total particle number at five times against its analytic integral, including after throat passage. A separate double-precision radial quadrature checks retarded emission with the Doppler factor. Clock tests run at 30/60/120 FPS and check pause, reset, visibility, and inactive modes. CUDA tests check the dust fixture and integrated intensities against the host solver. The offscreen test also compares scene pixels at observer times 0 and 28 and writes `target/wormhole-matter-throat.png`.

```sh
python tools/cuda/build.py
cargo test --locked --all-targets
cargo test wormhole -- --ignored --nocapture
cargo test --bin black_hole bridge_scene_renders_and_switches_back -- --ignored --nocapture
cd verification
lake build BlackHole.Ellis
lake env leanchecker BlackHole.Ellis
lake build BlackHole.EllisDust
lake env leanchecker BlackHole.EllisDust
```

The shared solver participates in the PTX source hash. The fixture is an explicit Lake input, and `BlackHole.lean` imports this module for the existing complete build, axiom audit, and kernel replay.
