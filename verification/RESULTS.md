# Verification results

The additional checks establish useful numerical properties and expose a
physical limitation. The present frozen binary model cannot be certified as
an exact vacuum binary spacetime: a supported configuration has nonzero Ricci
curvature outside the sources.

## Additional exact-real results

The proof inventory is in [OBLIGATIONS.md](OBLIGATIONS.md); a claim about a
transcribed formula does not prove the compiler or all runtime preconditions.

- **Kerr geometry:** Lean differentiates the explicit Cartesian radial root,
  H, ell and every metric component twice for arbitrary spin, with numerical
  floors inactive. The explicit Kerr inverse and nonsingularity are proved for
  r>0; inverse differentiability follows. Optical coordinate identities,
  first/second jets, the affine geodesic principal direction and a radial
  gradient bound are checked. The normalized subextremal exterior has inactive
  real radius/excision/derivative guards. Actual Christoffel derivatives give
  the Riemann tensor and its Ricci contraction. `KerrJetBridge` proves equality
  of the optical and Cartesian inverse/first/second jets. `KerrField.ricci_zero`
  and `ricci_matrix_zero` establish all 16 Ricci components vanish for every
  real mass, arbitrary spin vector and every point with positive exact Kerr
  radius. The polynomial certificates, coordinate-permutation identities and
  Ricci symmetry are all kernel checked and tied to the actual derivatives.
- **ISCO:** the actual Bardeen formula satisfies the unsquared marginal
  equation, is the unique marginal root for r >= 1, lies in [1,9], strictly
  decreases with signed spin, and is exterior to the horizon for |a| < 1.
  The equatorial Boyer–Lindquist model verifies conserved charges, the timelike
  radial identity, circular constants and marginality. In its stated existence
  domain, the circular radial curvature is negative exactly above ISCO.
  `KerrEquatorial` proves the Cartesian source's equatorial metric pullback,
  the coordinate differential using explicit exterior logarithmic shifts,
  source radial first integral and circular angular velocity. A complete
  geodesic-ODE/stability transformation remains open. The reference is
  [Bardeen, Press and Teukolsky (1972)](https://adsabs.harvard.edu/pdf/1972ApJ...178..347B).
- **Frames and transport:** the implemented inverse-column lapse and shift
  give the ADM norm and initialize a null tangent under exact inverse/symmetry
  hypotheses. They also give a future unit timelike observer and unit measured
  photon energy. `KerrCamera` establishes these hypotheses from the actual
  source with nonnegative mass and r>0, and proves spatial metric positivity.
  `CameraFrame` proves Gram–Schmidt nondegeneracy and orthonormal axes from a
  Euclidean orthonormal camera basis. `CameraPinhole` proves unit directions
  and a nonzero first-screen projection for all finite real pixel coordinates.
  `OrbitalCamera` derives that basis from the actual spherical position,
  elevation clamp and normalized cross products for every positive radius.
  It connects Euclidean pinhole normalization and dot-product reconstruction
  to the scaled Kerr frame and proves unit ray/first-screen construction.
  `ScreenFrame` proves the actual Kerr second-screen cross product has squared
  norm at least one for orthonormal inputs; its production floor is inactive
  and normalization preserves unit norm and both orthogonalities.
  `ScreenGauge` proves invariance of the polarization bivector under the actual
  time-component gauge reset. For exact null/unit/transverse input vectors it
  proves that source projection and scaled normalization preserve the screen;
  the chosen second screen has strictly positive frame orientation.
  `PlasmaFluid` proves both production fluid branches are future unit timelike
  for the actual Kerr source and any spatial candidate. Its ADM energy-sign
  theorem covers every past null ray and future unit fluid.
  `Hamiltonian` proves that the momentum
  equations imply the Christoffel geodesic equation. `KerrPath` derives the
  source's derivative along any differentiable ray path and verifies zero
  derivatives of null norm, screen norm and transversality. Pairings are
  constant on connected open solution domains. These are continuous results.
- **Polarized transfer:** the exact constant-cell expression solves the full
  ODE uniquely, composes under subdivision and preserves the physical Stokes
  cone under admissible-source/nonnegative-opacity hypotheses. Foreground
  multiplication order and finite-sequence cone preservation are checked.
  These claims exclude floating-point and threshold approximations.
- **Polarization normalization:** the shader now divides the EVPA numerator
  by the unclipped projected-field norm. Clipping that denominator could
  amplify polarization when numerical frame error makes the norm exceed one.
  Lean proves the corrected thermal plus 3/4-synchrotron source stays in the
  Stokes cone for arbitrary real projected fields. `PlasmaEmission` additionally
  proves nonnegative emission and opacity from the blackbody-color branches,
  hot weight, density, frequency and thermal/synchrotron prescriptions, for
  every model index and arbitrary real scalar arguments.
  The GPU regression exercises an oversized projected field and its cell
  transfer. Floating-point roundoff remains a separate error obligation.
- **Spatial normalization:** the shader rescales by the largest absolute
  component before squaring. Previously `(1e-12,0,0)` acquired length 0.01
  because of the 1e-20 norm floor, and squaring `(1e20,0,0)` overflowed.
  The GPU regression failed with the old shader and passes with the fix for
  tiny, huge and zero vectors. `SpatialNormalization` proves that the revised
  exact-real expression gives the intended unit vector for every nonzero input
  when the spatial metric dominates the Euclidean metric, including Kerr with
  nonnegative mass and positive radius. Floating-point error bounds remain open.
- **Threshold error:** for 0 <= alpha*s <= 0.001 the real absorption polynomial
  error is <= s/19200000000. The omitted Faraday coefficients have error
  <= w*s²/2; each component's error has this factor times the sum of the
  absolute perpendicular and turned emission components. At w*s <= 0.00001,
  the factor is <= s/200000. The two approximation errors add separately.
- **Disk radial coordinate:** the equatorial chart proves cylindrical radius
  squared is Kerr radius squared plus spin squared. Comparing cylindrical radius
  directly with the Boyer–Lindquist ISCO therefore misplaced the spinning disk.
  Both plasma sampling and disk step heuristics now use the same equatorial Kerr
  radial label, extended through the prescribed disk height; the circumbinary
  prescription retains cylindrical radius. The GPU regression reproduced the
  old failure and checks both spin signs, the binary branch, height invariance
  and an empty rotation axis after the fix. This does not calibrate the plasma
  or turn its sub-Keplerian flow into an exact circular-geodesic solution.
- **Exterior bounds:** `KerrBounds` proves H<=mass/radius. For unit mass and
  radius>=1, metric and inverse components have magnitude <=3, the spatial
  quadratic form lies between one and three times the Euclidean norm squared,
  and momenta bounded componentwise by P give tangent components bounded by 12P.
  `KerrSmoothness` proves infinite differentiability of the actual metric,
  inverse, first derivatives and full Hamiltonian/parallel-screen ODE on the
  positive-radius domain, plus local Lipschitz continuity and local solution
  existence. Uniform derivative constants, truncation and accumulated trajectory
  bounds still remain.
- **Dynamics:** `NewtonianLoop` transcribes the three-dimensional gravity loop,
  including self-pairs, coincident positions and velocity-before-position order.
  Its pair forces cancel, and exact momentum is conserved for any finite number
  of objects and updates. The mass-weighted position moves by step times total
  momentum. Floating-point/source execution remains separate.
  Exact symplectic-Euler energy conservation is false: two masses 1/2 initially
  at +/-1 at rest, with step 1, have new velocities +/-1/8, positions +/-7/8,
  and energy drift -9/896. No long-time drift bound is established.
- **Visual models:** the single-source exterior grid has the Schwarzschild
  Flamm induced radial metric; the interior clamp is constant. The implemented
  Newtonian zero-torque temperature peaks at 49/36 times the inner radius.
  Disk transition/height and warp displacement bounds are proved. This does
  not calibrate the prescribed disk/plasma/color model against observations.

## Binary field equations: counterexample

[Binary.lean](BlackHole/Binary.lean) evaluates the stationary Kerr–Schild
superposition with two nonspinning sources of mass 1/2 at x = ±7, at their
midpoint. This is the project's separation and total-mass convention, with
spin set to zero. Both individual horizons are well away from the test point;
the shader's excision and radius floors are inactive there.

The metric and its inverse at this point are

```
g    = diag(-5/7, 9/7, 1, 1)
g^-1 = diag(-7/5, 7/9, 1, 1)
```

[Schwarzschild.lean](BlackHole/Schwarzschild.lean) now differentiates
2m/r, 2m x_i/r² and 2m x_i x_j/r³ in Lean, including every time/spatial index
and mixed-partial symmetry, and proves equality with the zero-spin Cartesian
Kerr formula away from r=0. It checks all resulting first/second derivative
values against the rational model. [BinaryCurvature.lean](BlackHole/BinaryCurvature.lean)
then differentiates the actual inverse and Christoffel symbols and identifies
their Ricci contraction with the exact rational result. Kernel evaluation checks
both inverse products and gives

```
R_tt(binary midpoint) = 4/3087 ≈ 0.0012957564 ≠ 0
R_tt(single source, r = 7, mass = 1) = 0
```

The production GPU check differentiates connections using the production
metric/derivative functions. The local run produced:

| Central-difference spacing | Single source R_tt | Binary R_tt |
| --- | ---: | ---: |
| 0.02 | −3.02 × 10⁻⁷ | 0.0012953032 |
| 0.01 | −3.87 × 10⁻⁷ | 0.0012952890 |

Both spacings must agree with the exact values within 2 × 10⁻⁶. The test
**passes by detecting the expected nonzero binary residual**. Zero Ricci is
required for a vacuum solution without a cosmological constant. Matrix
invertibility and good null-geodesic integration do not make this superposition
a vacuum solution.

The metric specification remains manually transcribed; Lean does not parse or
verify WGSL execution. The derivative formulas are now proved from that metric,
rather than supplied as unchecked analytic inputs. The GPU comparison is an
independent sampled check of source correspondence. This counterexample covers one valid nonspinning
configuration, not every spin, point, phase, or a spacetime with evolved sources.
An exact dynamical binary would require a different physical model and evolved
metric data; these verification changes do not supply that model.

## Floating-point execution: finite bit-exact coverage

[Numerics.lean](BlackHole/Numerics.lean) uses Lean's logical `Float32` model for
the horizon function, including clamping, multiplication, subtraction, square
root and addition. Kernel reduction proves the output bit patterns for all nine
rows of [the shared fixture](fixtures/horizon-binary32.csv). The rows exercise
zero, both signs, ordinary and near-extremal spin, and clamping beyond the limit.
[The Rust regression](../tests/numerical.rs) calls the actual library function
and requires those same output bits. No native evaluation axiom is used in the
proof. Fixture changes invalidate the Lean build through a Lake input target.

A separate rational decoder interprets finite binary32 bits, including signed
zero/subnormals and rejection of nonfinite encodings. For each fixture it proves
that the exact-real polynomial residual of the returned horizon satisfies
|r² − 2r + a²| ≤ 10⁻⁶, with a clamped to the binary32 spin limit. These are
bounds on the nine executions, not all representable inputs. A kernel-checked
example at spin 0.999 has a nonzero floating-point polynomial residual, so exact
real algebraic equalities cannot simply be asserted about floating execution.

The production shader also checks the cancellation-sensitive negative-q Kerr
radius branch at an axial radius of 10⁻⁴. That is a hardware regression, not a
portable bit-level proof. A CPU binary32 replay is insufficient for the whole
shader: [WGSL permits differing rounding, reassociation and fusion](https://www.w3.org/TR/WGSL/#floating-point-evaluation),
and specifies accuracy bounds for built-in functions. See also
[Lean's floating-point logical model](https://lean-lang.org/doc/reference/latest/Basic-Types/Floating-Point-Numbers/).
There is no verified translation from Rust/WGSL to Lean or proof of the GPU
driver/compiler/hardware implementation in this repository.

## Solver accuracy: exact error facts and measured refinement

The Lean checks establish:

- Classical RK4's actual stages give the stability polynomial
  1 + z + z²/2 + z³/6 + z⁴/24 for y′=λy, z=λh.
- At z=−3 its amplification is 11/8, so overly large steps can be unstable.
- For y′=5t⁴, y=t⁵, the local signed defect is h⁵/24, before any rounding.
- Exact RK4 does not conserve nullness even for an initially null radial
  Schwarzschild ray whose stages and endpoint remain outside the horizon.
  `RadialRK4` derives its two-variable RHS and constraint from the actual
  Cartesian metric inverse and Hamiltonian force, then checks the nonzero
  residual using rational arithmetic in Lean's kernel.
- Stage perturbations bounded by ε change the weighted update by at most
  |h|ε, excluding rounding of the final weighted sum/state addition.
- If a nonnegative growth factor bounds an error recurrence with zero initial
  error and per-step defect d, the accumulated bound is
  d times the corresponding finite geometric sum. The recurrence is a theorem
  hypothesis, not an established property of every geodesic.

The GPU regression integrates one nonradial Schwarzschild ray to affine time
40 at h=4,2,1,0.5. An independent binary64 reference integrates the spherical
equations r″=L²/r³−3L²/r⁴ and φ′=L/r², rather than the shader's Cartesian
Hamiltonian system. Doubling the reference resolution from 4096 to 8192 steps
must change the endpoint by less than 10⁻⁹ r_g. A separate radial-ray self-check
verifies the reference's affine solution when L=0.

| GPU affine step | Endpoint position error (r_g), local run |
| --- | ---: |
| 4 | 0.19442833 |
| 2 | 0.01765692 |
| 1 | 0.00121205 |
| 0.5 | 0.00009061 |

The first two refinements must each reduce error by a factor greater than four;
the finest error must be below 0.001 r_g. The finest null residual must satisfy
the production threshold, and p_t must remain bit-identical at all resolutions.
These thresholds test convergence without requiring exact hardware-specific
error ratios.

The user delegated numerical and physical targets; [TARGETS.md](TARGETS.md)
records the selected domain, duration, accuracy and reference suite. A further
exact-arithmetic counterexample checks the former null-only acceptance rule
against the selected position target. At r=4, p_t=1, p_r=-3, the analytic radial
solution has r(λ)=4-λ and p_r=-(r+2)/(r-2); Lean verifies that it solves the
metric-derived Hamiltonian ODE. With h=6/25, the production geometry limit
0.12*(4-2), every stage stays outside r=2. The step has normalized null residual
about 2.264×10⁻⁶, below the accepted 2×10⁻⁴, but position error about
7.036×10⁻⁶, above the target 3.76×10⁻⁶. The inequalities are proved exactly;
these decimals are explanatory approximations. This is an affine p_t=1
normalization; a full proof of camera/affine-rescaling and floating execution
correspondence remains separate. Choosing an error target does not establish
that the renderer meets it.

Lean and a GPU check also show why null residual alone cannot estimate the full
trajectory error: momenta pointing in orthogonal spatial directions can have
equal conserved energy and exactly zero null residual. Production now combines
this residual guard with position/momentum/screen step doubling; see the adaptive
controller results below. The fixed-step refinement experiment exercises
production `step_ray`, and additional regressions now exercise `advance_ray`.
Arbitrary-ray global error bounds, rejection and capture correctness, and
long-time conservation remain unproved.

## Reproduce

Baseline validation on 2026-11-03, before the adaptive-controller additions:
the complete build passed for 61 project modules
and 486 public theorems, with all targets subsequently confirmed up to date.
The axiom audit checked all 1004 project declarations; a separate explicit audit
checked all 486 public theorem names. Both found only `propext`, `Classical.choice`
and `Quot.sound`. No proof uses `sorry`, a custom axiom or native evaluation.

`python check.py` completed the full build/audit/independent replay at the
58-module, 439-theorem checkpoint. The three subsequently added modules,
`KerrEquatorial`, `KerrBounds` and `KerrSmoothness`, each passed a separate
independent replay, covering the 47 additional theorems. No earlier proof body
changed after that checkpoint. The replay uses `LEAN_NUM_THREADS=1`; CI runs
the complete current tree with `python check.py`.
Fresh Rust validation passed 275 tests, the separately enabled GPU regression,
formatting and Clippy. This includes the projected-polarization, tiny/huge/zero
spatial-normalization and corrected disk-coordinate regressions. The latter was
observed failing with the original cylindrical calculation before the fix.
Separate Bevy/proptest/rstest dependency updates appeared during the proof work;
they were preserved, and these Rust/GPU checks ran against the updated dependencies.

From `verification/`, run `python check.py` with Elan's `bin` directory on `PATH`.
From the repository root, run `cargo test` and
`cargo test headless_render -- --ignored --nocapture`. The latter prints the
trajectory errors and Ricci residuals; it needs a supported GPU.


## Adaptive controller and explicit first-derivative bounds

Production `advance_ray` compares a full RK4 step against two half steps in
position, covariant momentum and the transported screen. Each component uses
`max(1, abs(coarse), abs(fine))` scaling; the maximum difference divided by 15
must be at most 5×10⁻⁸. The existing normalized null guard is retained. All RK
stage and endpoint states must be finite within the implementation's numeric
limits, have a valid metric and positive horizon clearance. Twelve failed
halvings produce an unresolved step, and the renderer does not add escaped sky
for it. An accepted step uses the two-half-step result and carries a bounded
step-size suggestion forward. These extra evaluations increase GPU work.

`AdaptiveStep.lean` proves the leading-error factor, an estimator-to-error bound
with an explicit higher-order remainder, variable accumulated-error budgets,
and separated-event classification given a certified scalar enclosure. Kernel
rational evaluation proves that the new estimator rejects the former radial
counterexample at h=6/25 and that its first halving meets the analytic radial
position/momentum targets. The accepted refined result still has a nonzero
exact null residual. These are conditional theorems and finite examples;
they do not certify the full nonlinear controller or floating-point execution.

`KerrDerivativeBounds.lean` proves explicit bounds for unit mass, |a|²≤1 and
Kerr radius r≥1: each radius derivative is bounded by 2, cosine derivative by
3, ell derivative by 4, potential derivative by 10, and metric first derivative
by 36. If all covariant momentum components have magnitude at most P, each
continuous momentum-force component has magnitude at most 41472 P². These
conservative bounds apply to arbitrary spin orientation. Higher derivatives,
uniform RHS Lipschitz/truncation constants and the full global budget remain.

The production GPU regression checks the rejected radial example, invalid
intermediate stages, nonpositive steps, oversized screen inputs, repeated
radial stepping, and an adaptive Schwarzschild scattering trajectory. A local
run at affine length 40 measured position error 2.3535×10⁻⁵ r_g against the
independent, refined binary64 spherical reference, and maximum screen
norm/transversality residual 2.3842×10⁻⁷. The stationary p_t bits were unchanged.
The scattering regression limit is 10⁻⁴ r_g; it does not assert that the stricter
TARGETS.md global accuracy has been met. The six existing single/binary
intensity and polarization smoke scenes also passed at 128×96 resolution.

Current adaptive-controller validation on 2026-11-03: `python check.py` completed
the full current build, the axiom audit of 1024 project declarations (only
standard axioms), and independent kernel replay of all 63 project modules,
including the 16 new public theorems. Rust validation passed all 276 default
tests, the separately enabled headless GPU regression, formatting and Clippy.


## Extended ray growth bounds and benchmark acquisition

`RayGrowth.lean` adds explicit bounds of 5184 on inverse-metric derivative
components and 2592 K on contracted-connection components for a tangent bound
K. The actual `phaseRhs` screen derivative is bounded by 124416 P F for
momentum-component bound P and screen-component bound F. These use unit mass,
|a|²≤1 and Kerr radius r≥1, as in the first-derivative bounds. The new module
passed the normal build and independent kernel replay; the updated whole-tree
axiom audit checked 1027 project declarations with only standard axioms. The
previous 63-module replay remains the checkpoint for unchanged proof bodies.
There are now 19 new public theorems across the three additions.

The exact EHT comparison snapshot was found in Harvard Dataverse, downloaded
and verified against its published MD5 and a recorded SHA-256. Its finite
primitives and positive density/internal energy passed inspection. The actual
header time differs from the nominal paper time, and its simulation diagnostic
flags are retained explicitly. [benchmark-data.md](benchmark-data.md) records
identity, acquisition, validation and the pinned independent ipole workflow.
This removes the missing-input dependency of P3; physical renderer calibration
and source correspondence are still open.

The pinned independent ipole run generated the polarized 160×160 reference
with integrated (I,Q,U,V) = (0.47976118576344184, -0.006700681644500638,
-0.002915943556236394, 0.00310100947421721) Jy and unpolarized flux
0.5046674123064179 Jy. The recorded HDF5 camera/physical headers match the
saved parameter file. Its Stokes pixels were finite with positive intensity
and satisfied the cone check. This is a regenerated independent reference;
there has not yet been a calibrated comparison with the production WESL.

A repeat through the saved reference build/run scripts reproduced every
Stokes pixel bit-for-bit on this machine. This verifies this workflow; it
is not a portable bit-exactness claim about other compilers or hardware.

## Snapshot and polarized local kernels (2026-11-04)

`SnapshotChart.lean` adds 12 public theorems for the full spherical
Kerr-Schild position, radius and ell direction, the MKS polar map's derivative,
lower derivative bound, strict monotonicity and range, and trilinear weighted
form, convex bounds and constant reproduction. The whole project build and
axiom audit passed with 1051 project declarations and only standard axioms.
The new module was independently replayed; the earlier full-tree replay remains
the checkpoint for unchanged proof bodies. This is exact-real coverage; it
does not prove the sampled CPU/GPU execution or the inverse bisection.

`eht_snapshot.py` and `snapshot.wesl` implement native-grid interpolation,
reference ghost conventions, primitive-to-four-vector reconstruction, physical
scalars/cuts and the +Y-spin Cartesian mapping. A C probe queries the pinned,
unmodified ipole model independently. All 274 CPU queries agreed to maximum
scaled component error 8.8911e-14. The GPU maximum scaled errors were
2.0266e-6 for velocity, 8.1584e-7 for magnetic vector, 1.2161e-5 for physical
scalars, and 2.9803e-7 for native coordinates. Invalid queries were rejected.

`thermal.wesl` matches the pinned thermal fits and benchmark physical units.
The 292 direct ipole comparisons measured maximum family-scaled GPU errors
6.3172e-6 (emission), 9.9344e-6 (absorption), and 2.9016e-6 (Faraday).
The table, cold branch, polarization cap and normalized CGS arithmetic avoid
underflow in relevant coefficients; this is not an all-input accuracy proof.

`polarized_transfer.wesl` includes polarized absorption in the full affine
four-Stokes system. Its 128 GPU cases agreed with an independent binary64 ODE
reference to maximum scaled error 6.3795e-6. Refining the reference from 4096
to 8192 steps changed results by at most 1.6087e-10. Exact zero-opacity,
pure-Faraday and thermal-equilibrium checks validate the reference separately.
Nonfinite, nonpassive, negative-length and oversized inputs are rejected.
The full matrix solver still needs formal truncation/roundoff bounds.

[benchmark-data.md](benchmark-data.md) documents regeneration commands, units,
error normalizations and supported domains. The optional local kernels have
not yet been connected into a snapshot image renderer. The interactive shader
continues to use its prescribed plasma, and no calibrated WESL/ipole image
agreement is claimed.

The final incremental checks passed 279 default Rust tests, all 15 rendering
checks including the three optional GPU suites, six Python regressions,
formatting and Clippy with warnings denied. Recorded source hashes, query
counts and local measurements are in
[fixtures/eht-component-checks.json](fixtures/eht-component-checks.json).
The unchanged interactive six-scene GPU smoke test retains its earlier
checkpoint; it was not rerun for these optional benchmark additions.

## End-to-end snapshot images (2026-11-04)

The optional benchmark now connects the local kernels into full 160x160 images.
All 25600 camera rays/tetrad vectors were checked against ipole. A binary64
emission-free outer segment hands off at 120 r_g; its independent probe and
refinement results are in [benchmark-data.md](benchmark-data.md). The GPU uses
screen-gauged transport, momentum rescaling with compensated frequency/path
length, and radial horizon-clearance steps. The original production transport
mode and six-scene GPU smoke test passed again.

`RayConditioning.lean` adds eight exact-real scaling, gauge-rate and full-matrix
foreground-composition theorems. The complete build and axiom audit passed
1061 project declarations with only standard axioms; the new module passed
independent kernel replay. These conditional algebraic results do not certify
the complete hybrid numerical execution or its roundoff.

The reference was refined from ipole eps=0.01 to eps=0.0025. Integrated I
changed from 0.4797611858 to 0.4771235045 Jy; the image I L2 change was 5.98%.
Three full GPU runs (cell fractions 0.25/0.125/0.0625) each resolved 990 captured
and 24610 escaped rays without failures. The finest run gave total I
0.4767574909 Jy (0.077% difference), with component image L2 errors over the
reference I L2 norm of 0.688%, 0.216%, 0.285% and 0.0666% for I/Q/U/V.

The requested numerical targets are still **not met**. Maximum I pixel error
is 2.64% of a fixed reference peak, and relative error in faint pixels can be
about 44%. GPU refinement changes do not decrease monotonically and the null
residual increases at smaller steps. Reference refinement and separation of
geometry/transfer/roundoff errors remain necessary. `check_image.py compare`
writes the measured report and exits unsuccessfully until the targets pass.
The image regression checks finiteness/resolved rays, not target accuracy.

[fixtures/eht-image-checks.json](fixtures/eht-image-checks.json) records the
reference provenance, all three runs and refinement differences. The default
Rust checks passed 280 tests, the Python suite passed seven, all optional local
GPU suites and the full image runs passed their stated checks, and formatting
and Clippy passed. The interactive renderer's plasma prescriptions are unchanged.

## Certified rays and WGSL kernel bounds (2026-11-06)

**Certified rays (N2, F3).** `RayCertificate.certified_ray` states what an
accepted certificate means for the exact Kerr ray from a camera: physical
initial data, existence over the certified affine interval, uniqueness among
solutions that stay where the equations are defined, the capture/escape
verdict, and 10⁻⁶ bounds on an escaping ray's direction and redshift. Each
step's residual is checked with interval jets, its Jacobian over the tube
gives a Lipschitz bound, and a Grönwall end radius keeps errors growing
linearly. `lake exe certify` runs this exact checker as compiled Lean. A ray
from radius 1500 with spin (0.2, −0.7, 0.3) certifies as escaping in 14 steps
and 27 s. A full escape from radius 100 with the same spin certifies in 1159
steps (21 minutes of search plus a 14-minute trusted replay). At radius about
1600 its final position is enclosed within ±2.1·10⁻⁵, which is 1.3·10⁻⁸
relative, and its momentum within ±1.4·10⁻⁸.

**WGSL kernels (F2).** `WgslPoly` and `WgslExpr` prove error bounds for every
input and every admissible rounding under the WGSL accuracy table. They are
applied to `geodesic_rhs`, the RK4 arithmetic, `add_kerr`, `screen_frame`,
`sample_plasma` (disk models 0–2) and the display kernels. Most of
these bounds hold under explicit `Safe` hypotheses and are running
expressions rather than domain-wide constants. Two consequences of the
specification limit what can be proved for the code as written:

- WGSL does not specify `atan2(y, x)` accuracy for `y = 0` or
  `|x| < 2⁻¹²⁶`. A conforming implementation may return binary32 angles at
  least 2 away there, and `acos(0)` at least 1.4 from `π/2` with every
  inherited intermediate accurate (`WgslCounterexamples`). The unchanged
  skybox, polarization hue and warped-disk paths therefore have no useful
  bound on every conforming implementation; explicit handling of these inputs
  would fix this.
- `sqrt(x)` is inherited from `1.0/inverseSqrt(x)`, and `inverseSqrt(0)` is
  infinite, which WGSL turns into an indeterminate value. A shader `sqrt(0)`
  therefore has no defined result. The running bounds require square-root
  arguments to stay positive by more than their error, which is exactly this
  boundary.
