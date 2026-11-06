# N2: certified Kerr rays

N2 asked for geodesic-specific smoothness, growth and defect bounds feeding
an accumulated-error theorem, at the accuracy fixed in [TARGETS.md](TARGETS.md).
An a priori bound cannot meet those targets: `RayGrowth` gives exact screen
growth up to exp(124416·P·t), and with momentum P and affine length t up to
10⁴ this is astronomically large. The project therefore certifies each ray a
posteriori. The step bounds are computed for that ray and checked exactly.
Every claim is a Lean theorem about the exact Kerr ray, and a ray the checker
cannot certify is reported as unresolved.

## What is proved

`RayCertificate.certified_ray` is the end-to-end statement. If
`RayCertificate.certify` accepts a camera (spin, position, view direction,
screen hint) and a list of proposed steps, then:

1. **Camera.** The exact camera state is a null covector with Eulerian energy
   one and a future observer, and its screen is a unit spacelike vector
   transverse to the ray (`CameraPhysics.camera_physics`, using
   `KerrField.camera_initialization`). Checked evaluation encloses this state
   (`RayObserve.cameraBoxes_sound`).
2. **Existence.** A solution of all eleven Kerr equations exists from that
   state over the whole certified affine interval. It stays where the Kerr
   radius is positive (`TraceCheck.steps_exist`, `StepField.lift`).
3. **Uniqueness.** Every solution of the full equations from that state that
   stays where they are defined satisfies the facts below. The time momentum
   is conserved (`reduce_solution`), and the reduced solution is unique
   because the field is locally Lipschitz on that open set
   (`TraceCheck.solution_unique`, `steps_unique`).
4. **Classification.** For the verdict `running`, the ray keeps horizon
   clearance above 1/500 and Euclidean radius below 1600 for the whole
   interval. For `captured`, it stays inside radius 1600 and ends within 1/500
   of the horizon. For `escaped`, it keeps clearance above 1/500 and ends
   outside radius 1600 (`RayEvents.trace_sound`). Ambiguous steps are not
   classified.
5. **Observables.** For an escape, the angle between the exact direction of
   the contravariant spatial momentum and the reported binary32 direction is
   at most 10⁻⁶ rad (via `DirectionError.angle_le_twice_chord`). The
   static-observer redshift is positive and the reported binary32 value is
   within 10⁻⁶ relative error. The screen norm and transversality residuals
   are at most 10⁻⁶ (`RayObserve.observe_sound`).
6. **Final state.** The exact state at the end of the interval lies in the
   last reported box, whose half-widths are the position, momentum and screen
   errors compared with TARGETS.md. The search keeps the weighted end radius
   below 10⁻⁷ relative to max(1, |component|). That budget is a search policy;
   the box is the certified result.

The full build and `Audit.lean` show these theorems use only `propext`,
`Classical.choice` and `Quot.sound`.

## How a step is certified

`StepCheck.check` takes a proposed step: a dyadic length h, quartic
coefficients for the ten reduced components (position, spatial covariant
momentum, screen), weights and a tube radius ρ. It then:

- runs the complete Kerr right-hand side (`KerrProgram`, memoized as
  `KerrProgramFast`) on proof-carrying interval jets (`CheckedFunction`).
  This happens once at t = 0 and once over [0, h], to bound the residual
  P′ − f(P) (`CheckedData.kerr_residual`);
- encloses the Jacobian over the whole tube from ten directional order-1
  runs (`StepCheck.jacobian_sound`) and derives a weighted row-sum Lipschitz
  constant K;
- checks Picard inclusion e₀ + h(δ + Kρ) ≤ ρ (`StepField.certified_step`,
  through `ValidatedStep.exists_solution_in_tube`);
- applies Grönwall inside the tube to get the end radius
  (e₀ + hδ)/(1 − hK) (`StepField.certified_step` with Mathlib's
  `dist_le_of_approx_trajectories_ODE_of_mem`). Errors therefore grow
  linearly with the defect rather than doubling per step.

`check_sound` covers every initial point and every conserved time momentum in
the input boxes. `CheckedData.erase_execute` shows the data-only evaluation
that the executable runs computes exactly the erased certificates, so the
proofs never depend on the floating-point accuracy of a proposal.

## Execution: the checked code is the proved code

`lake exe certify ray ax ay az  x y z  dx dy dz  hx hy hz  limit` runs
[Certify.lean](Certify.lean). Its search is untrusted: it proposes step
lengths, Taylor coefficients, weights, tube radii and rounded observables.
The verdict comes only from `RayCertificate.certify`, the definition that
`certified_ray` is about, compiled by Lean. Inputs are rounded once to
multiples of 2⁻⁶⁴, and the certificate is about those exact dyadic values.
This closes the source-correspondence question (F3) for this path. What
remains trusted is the Lean compiler, the C toolchain and the hardware, the
same boundary as F4.

Practical notes:

- Evaluation is in exact dyadic arithmetic with outward rounding at 2⁻⁹⁶. A
  checked step takes about 0.3 s.
- The quartic Taylor remainder near radius r forces h ≈ 10⁻³ r at the default
  defect heuristic of 10⁻¹¹ per unit time. The escape from r = 100 with spin
  (0.2, −0.7, 0.3) takes 1159 steps: 21 minutes of search and a 14-minute
  trusted replay. Its final position is enclosed within ±2.1·10⁻⁵ at
  r ≈ 1600, and its direction and redshift meet 10⁻⁶.
- The direction check bounds the squared chord. Its enclosure contains 0 for
  an accurate direction, so a checked square root of it would fail.
- A compiled table must be built inside a definition that returns a
  structure, `Option` or `Vector`. Lean gives a definition the arity of a
  function-typed result, so a table built there is rebuilt at every lookup.
  `RoundedProposals`, `KerrProgramFast` and `StepCheck.collect` follow this
  rule.

## Relation to the renderer

The GPU renderer keeps its binary32 RK4 step-doubling controller. That
controller is shown to miss the trajectory targets (N3) and to misclassify
near-critical rays (N4). Nothing here certifies a GPU pixel. The Rust
prototype in `src/certified` is superseded as a trust base by the
Lean-compiled checker; it remains a faster, unverified proposer.
