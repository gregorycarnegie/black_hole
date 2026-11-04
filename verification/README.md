# Lean 4 verification

The full [proof-obligation list](OBLIGATIONS.md) tracks the remaining work,
counterexamples, specification dependencies and external trust boundaries.
The chosen reference systems, finite domains and error requirements are in
[TARGETS.md](TARGETS.md). The exact EHT comparison snapshot has been obtained;
[benchmark-data.md](benchmark-data.md) records its verified identity and the
independent reference-solver workflow.

This package checks exact-real identities, concrete binary32 executions, RK4
error calculations, and an exact binary-metric counterexample. Read
[verification results](RESULTS.md) for the findings: the frozen binary model
fails the vacuum field equations in a supported nonspinning configuration.
This is not a proof of the entire renderer's physical accuracy. Specifications
are manually transcribed from Rust/WESL; source changes require reviewing their
correspondence. Shared bit fixtures connect the horizon specification to Rust
execution at nine inputs.

## Run

Install [Elan](https://lean-lang.org/install/manual/) and put its `bin` directory
on `PATH`. From the repository root:

```sh
cd verification
lake exe cache get
python check.py
```

On Windows, if Elan is not on `PATH`, first run
`$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"` in PowerShell.
`check.py` builds the large curvature modules one at a time, builds the complete
project, audits all project declarations' axiom dependencies and independently
replays the compiled proofs (`--build` and `--replay` run the two phases
separately; CI runs them as separate jobs). On a 16 GB hosted runner with swap,
`KerrVacuumTime` alone takes about 2.7 hours and the full build about 4 hours. It sets `LEAN_NUM_THREADS=1`; an earlier concurrent
replay failed to resolve a Mathlib import. A parallel curvature build also
exhausted a 64 GB workstation's free memory.
The toolchain and mathlib are pinned to v4.35.0; `lake-manifest.json` locks
transitive dependencies. The first cache download requires network access and
substantial disk space. Subsequent proof builds work offline.

`lake build` checks proofs and treats warnings, including unfinished proofs, as
errors. The package uses no `sorry`, `admit`, custom axioms, or `native_decide`.
`leanchecker` separately rechecks the compiled proof environment. Standard Lean
and mathlib foundations (including classical choice) are trusted. CI repeats the
checks with `check.py`, using [lean-action](https://github.com/leanprover/lean-action)
for toolchain and Mathlib-cache setup.

## Correspondence and coverage

All lengths below are in gravitational radii, with G = c = M = 1. Theorems state
their hypotheses explicitly; they do not establish that every runtime input
satisfies them.

| Implementation | Lean declarations | What is established |
| --- | --- | --- |
| `src/physics.rs`: `kerr_horizon_radius_rg` | `horizon_*` | At zero spin r+ = 2; spin reversal symmetry; 1 ≤ r+ ≤ 2 and Δ(r+) = 0 when a² ≤ 1; shrinking radius as nonnegative spin increases; positive-mass scaling bounds. The specification takes spin after the runtime clamp. |
| `src/physics.rs`: `kerr_isco_radius_rg` | `Orbits.lean`, `KerrGeodesics.lean`, `KerrRadialStability.lean`, `Binary32Bounds.lean`, `isco_outside_horizon` | The actual Bardeen formula satisfies r²−6r+8a√r−3a²=0, uniquely for r >= 1. Its radius lies in [1,9], strictly decreases with signed spin, and lies outside the horizon for subextremal spin. The equatorial Kerr radial model admits a marginal timelike circle there, and linearized radial motion about a circular orbit is bounded exactly outside it. The production code evaluates the cancellation-free form `isco_stable`; in the IEEE binary32 model its relative error is at most 2048 u prograde and 256 u retrograde (`isco_error`), and the exhaustive test measures 17.2 u. |
| `assets/shaders/geodesic.wesl`: `kerr_radius` | `radialSquared_*` | The nonnegative squared radius solves u² − q u − (a·x)² = 0. For q < 0, the rationalized expression equals the direct positive root. Numerical floors are excluded. |
| `add_kerr`: `numerator`, `ell` | `kerr_ell_numerator`, `kerr_ell_null` | For r ≠ 0 satisfying the radial equation, the shader's spatial ell has unit Euclidean norm for an arbitrary spin axis. Thus (1, ell) is null in the Minkowski metric with signature (−,+,+,+). Excision clamps are excluded. |
| `add_kerr`: inverse update | `sherman_morrison`, `KerrInverse.lean`, `KerrRankDerivative.lean` | The rank-one update has a right inverse when the previous inverse is correct and 1 + 2H ell·(B ell) ≠ 0. For one exact source with r>0, the explicit Kerr inverse and metric nonsingularity are proved without an inverse hypothesis. The null rank-one inverse derivative is also checked. Repeated updates retain cross terms; this does not establish binary vacuum. |
| `add_kerr`: spatial metric derivatives | `Calculus.lean`, `KerrCartesian.lean` | Lean differentiates the explicit radius, H and ell along each Cartesian coordinate and obtains all 16 implemented component derivatives. Nonsingular-domain hypotheses exclude numerical floors. |
| `add_kerr`: metric Hessian and curvature | `KerrSecond.lean`, `MetricInverse.lean`, `Curvature.lean`, `KerrCurvature.lean`, `KerrJetBridge.lean`, `KerrVacuum.lean` | Lean differentiates the metric twice and the inverse/Christoffel symbols, giving actual Riemann and Ricci tensors. The optical and Cartesian inverse/first/second jets agree. `KerrField.ricci_zero` and `ricci_matrix_zero` prove all 16 Ricci components vanish for arbitrary real mass and spin at every point with positive exact Kerr radius. |
| `add_kerr`: optical geometry and guards | `KerrOptical.lean`, `KerrOpticalSecond.lean` | The actual source's optical coordinate identities, affine geodesic principal direction, first/second optical jets and radial gradient bound are proved. Real radius, excision and derivative floors are inactive in the normalized subextremal exterior. Floating-point evaluation remains separate. |
| Kerr ODE domain and bounds | `KerrSmoothness.lean`, `KerrBounds.lean` | The actual continuous Hamiltonian/screen RHS is infinitely differentiable and locally Lipschitz for positive Kerr radius, and admits local solutions. For unit mass and r>=1, metric/inverse components are bounded by three and the spatial metric lies between one and three times the Euclidean form. Global duration, error-controller and rounding bounds remain open. |
| Disk radius / equatorial orbital coordinates | `KerrEquatorial.lean` | The actual Cartesian metric pulls back to the equatorial orbital metric; exterior logarithmic shifts and their derivatives, radial first integral and circular angular velocity are proved. Single-hole disk profiles use the equatorial Kerr radial label extended through height, matching the ISCO coordinate; the binary prescription uses cylindrical radius. Floating-point execution and full orbital ODE/stability correspondence remain separate. |
| Snapshot MKS/Cartesian chart and interpolation | `SnapshotChart.lean` | Full spherical chart radius and ell identities, polar derivative/lower bound/monotonicity/range, and weighted trilinear convexity/constant reproduction. CPU/GPU indexing, bisection and finite-precision execution remain separate. Independent local snapshot, thermal and full polarized-transfer checks are documented in [benchmark-data.md](benchmark-data.md). |
| Benchmark ray conditioning and composition | `RayConditioning.lean` | Exact tangent/force homogeneity, energy-ratio and affine/fluid-distance compensation, gauge-rate time cancellation/bivector invariance, and full-matrix foreground composition. Eight checked lemmas; numerical execution/global errors remain open. The full hybrid EHT image benchmark and failed accuracy targets are recorded in [benchmark-data.md](benchmark-data.md). |
| `src/camera.rs`, `init_ray` | `ADM.lean`, `KerrCamera.lean`, `CameraFrame.lean`, `CameraPinhole.lean`, `OrbitalCamera.lean` | The spherical camera with clamped elevation yields an orthonormal basis for any positive radius. Scaled Gram–Schmidt, Euclidean pinhole normalization and dot-product reconstruction yield a unit Kerr direction and first screen for all finite real pixels. The inverse column gives the future unit observer, past null tangent and unit measured energy. Floating-point/source execution remains separate. |
| `geodesic_rhs` | `inverse_metric_derivative`, `hamiltonian_constraint_rate` | The differentiated inverse identity gives K′ = −K G′ K; the positive 1/2 in the momentum equation cancels the corresponding inverse-metric term in the null-constraint rate. These are algebraic ingredients, not a proof of the ODE solver or global trajectories. |
| `geodesic_rhs`: continuous screen transport | `Transport.lean`, `Hamiltonian.lean`, `KerrPath.lean` | The inverse-raised Christoffel expression is metric compatible. Hamiltonian momentum evolution implies the tangent geodesic equation. The full Kerr derivative chain along arbitrary differentiable paths is proved, giving zero derivatives of null norm, screen norm and transversality for exact Hamiltonian/transport solutions. These quantities are constant on connected open solution domains; discrete integration and floating execution remain separate. |
| `screen_frame` | `screen_gauge`, `ScreenFrame.lean`, `ScreenGauge.lean` | The time-component gauge reset preserves the polarization bivector. Given exact null/unit/transverse inputs, source projection and scaled normalization preserve the first screen; the second screen is unit, orthogonal to both inputs and positively oriented. Discrete transport errors and floating-point/source execution remain separate. |
| `faraday_rotation` | `faraday_generator_preserves_norm`, `rodrigues_preserves_norm`, `faraday_rotation_preserves_norm` | The cross-product generator has zero norm derivative; the Rodrigues operator preserves Q²+U²+V² for any unit axis and angle. Emission and absorption are excluded from this invariant. |
| `absorption_integral`, `polarized_cell`, `transfer_phi` | `Transfer.lean`, `TransferBounds.lean`, `TransferPhi.lean` | The exact coefficients solve the full source/absorption/Faraday ODE, with zero-distance and zero-Faraday cases and uniqueness. Both integrals are now ds·φ(z), φ(z) = (1 − e⁻ᶻ)/z with z = (α − iw)ds; `phi_closed_form` shows this equals the former closed form exactly, and the 11-term series used for \|z\| < 1/2 is within 10⁻¹¹ (`phi_series_error`). The former evaluation cancelled at small optical depth (`check_transfer_cell.py`). Omitting Faraday changes each component by at most (ws²/2) times the sum of its absolute perpendicular/turned source components; ws ≤ 0.00001 implies ws²/2 ≤ s/200000. `Transfer.absorptionTaylor_*` concern the former 3-term branch. Floating-point evaluation is separate. |
| `polarized_cell`, foreground accumulation | `Composition.lean`, `Stokes.lean` | Exact cells compose, foreground order agrees with camera-outward linear-operator multiplication, and nonnegative-opacity cells preserve the physical Stokes cone for admissible sources. The proof includes scalar zero-Faraday transfer and induction over finite cell sequences. Numerical approximations/floors are excluded. |
| `sample_plasma`, `projected_evpa` | `Frames.fluid_*`, `Plasma.lean`, `PlasmaEmission.lean`, `PlasmaFluid.lean` | Both actual Kerr fluid branches give future unit timelike vectors for any spatial candidate; fluid-frame energy is positive for arbitrary past null rays under spatial ADM positivity. Field/screen projections are orthogonal under normalization/energy hypotheses. All blackbody-color branches, hot weight, density, frequency and thermal/synchrotron prescriptions have nonnegative exact-real emission/opacity. The corrected source lies in the Stokes cone for every model index and arbitrary real projected fields. Physical redshift conservation, calibration and floating-point/source execution remain separate. |
| `src/simulation.rs`: Newtonian update and units | `Dynamics.lean`, `NewtonianLoop.lean` | The full exact three-dimensional pair loop, including self-pairs and coincident positions, preserves total momentum for any finite number of objects and updates. The mass-weighted position advances by step times total momentum. Exact energy conservation is false: a two-body symplectic-Euler step has drift −9/896. The scalar gravitational unit conversion is consistent for c != 0. Floating-point/source execution, timing and error bounds remain open. |
| `src/grid.rs`: single-source deformation | `Models.embedding_*`, `Models.clamped_embedding_*` | The exterior height is the Flamm embedding of the Schwarzschild spatial radial metric. The interior clamp gives constant height; a multi-source sum remains a visualization prescription. |
| `nt_temp`, disk height and warp | `Models.diskTemperature_*`, `temperature_*`, `disk_*`, `slim_height_weight`, `warp_height_bound` | The actual nested-root temperature profile peaks at r/r_in = 49/36. Transition and height weights have the expected bounds; the real warp displacement is bounded by radius times absolute tilt in radians. Full runtime branch correspondence and physical calibration remain open. |
| `src/physics.rs`: binary32 horizon bound | `Binary32.horizon_error` | Every clamped binary32 input, in the IEEE round-to-nearest model, has absolute error at most 32 u (u = 2⁻²⁴); `tests/exhaustive_binary32.rs` measures 6.2 u over all 2³² inputs. |
| `src/simulation.rs`: units, fixed step, binary clock | `Units.lean`, `EnergyDrift.lean` | Exact gravitational units for positive scales, an exactly representable 1/64 fixed step, a 21.16 s Sagittarius A* time unit, a superluminal prescribed binary, and no uniform energy-drift bound for the production update. |
| `polarized_transfer.wesl`: matrix exponential | `MatrixTransfer.lean` | The augmented exponential solves the full polarized ODE; the loop's closed form, the 10⁻¹⁹ per-step truncation bound, exact squaring and the squaring error amplification are proved for exact reals. |
| `geodesic.wesl`: `blackbody_color` | `check_color.py` | Numerical check: no peak temperature makes the colour stops a Planck sequence under CIE 1931/sRGB. |
| `src/physics.rs`: horizon arithmetic | `Numerics.horizon_binary32_replay`, `Numerics.horizon_sample_residual_bound`, `Numerics.binary32_horizon_has_roundoff` | Kernel-reduced binary32 operations match nine shared bit fixtures. Their exact-rational horizon polynomial residual is ≤ 10⁻⁶. A nonzero computed residual at spin 0.999 demonstrates roundoff. `tests/numerical.rs` checks the same fixtures against the production Rust function. This is finite input coverage, not an exhaustive proof. |
| `advance_ray`: adaptive acceptance | `AdaptiveStep.lean`, `KerrDerivativeBounds.lean`, `RayGrowth.lean` | The 1/15 step-doubling factor, conditional remainder/global-budget and separated-event bounds are proved. Exact rational checks reject the former radial counterexample and verify its halved position/momentum target; even the refined step is not exactly null. Explicit first metric-derivative and momentum-force bounds cover unit mass, |a|²≤1 and r≥1. Higher derivatives, global error, floating-point and execution correspondence remain open. |
| `step_ray` RK4 weights/stages | `Numerics.rk4_*`, `Numerics.accumulated_error_bound` | Exact stages give the degree-four stability polynomial for y′=λy; z=−3 is unstable. The t⁵ test solution has a local defect h⁵/24. Stage and accumulated-error bounds hold under stated error/growth hypotheses, which are not established for every production geodesic. |
| `add_kerr` nonspinning binary superposition | `Schwarzschild.lean`, `BinaryCurvature.lean`, `Binary.lean` | Lean differentiates the nonspinning real source, proves its equality to the zero-spin Cartesian Kerr formula, and checks every first/second derivative value against the rational calculation. Actual connection derivatives then give R_tt = 4/3087 at the equal-mass midpoint (sources ±7, masses 1/2), versus zero for the one-source control. Production GPU finite differences independently reproduce these values. The Rust/WESL-to-Lean transcription and execution remain trust boundaries. |

## Numerical checks and remaining physics

Run these from the repository root as well:

```sh
cargo test
cargo test headless_render -- --ignored --nocapture
```

The GPU test appends `tests/relativity.wesl` to the **production** shader. It checks
metric inverse and derivatives, null initialization, capture/escape, screen
transport, and Stokes/Faraday solutions at sampled inputs. The headless app
disables gamepad discovery so unrelated Windows controller failures do not
prevent physics checks. It also measures production RK4 step refinement against
an independent binary64 Schwarzschild reference, checks small-radius cancellation,
and compares single/binary vacuum residuals with the exact Lean calculations.
These complement the finite binary32 proofs without establishing whole-program
IEEE-754 bounds or source-to-specification equivalence.

Still outside the formal coverage:

- Finite-precision/source correspondence for the complete single-hole vacuum
  theorem: all 16 exact-real Kerr Ricci components are proved zero. The binary
  superposition has a checked nonvacuum counterexample, and the prescribed
  18-second orbit is not an evolved relativistic two-body solution.
- Unconditional convergence/error bounds for the nonlinear geodesic solver,
  all-input floating-point guarantees, adaptive rejection, excision/capture
  boundaries, and long-run conservation. Conditional error theorems and sampled
  refinement checks do not establish these stronger claims.
- Complete source/coordinate correspondence for the orbit and continuous transport
  models, all runtime frame nondegeneracy conditions, and Newtonian long-time drift.
- Floating-point polarized-cell branch errors, full plasma/redshift derivation,
  and disk geometry, emissivity and color calibration.
  In particular, `nt_temp` implements the simplified profile
  T ∝ r^(−3/4)(1−sqrt(r_in/r))^(1/4), rather than the full relativistic flux
  treatment of [Page and Thorne (1974)](https://articles.adsabs.harvard.edu/pdf/1974ApJ...191..499P).

For further verification, extend these statements alongside the corresponding
source functions and production-shader regression cases. A theorem about a
transcribed formula alone cannot certify the renderer's physical fidelity.
