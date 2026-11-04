module

public import BlackHole.KerrInverse
import Mathlib.Tactic.FinCases

@[expose] public section
noncomputable section

namespace BlackHole.RadialRK4

variable {R : Type*} [Field R]

/-- Past-directed radial Schwarzschild Hamilton equations with p_t=1. -/
def rhs (s : R × R) : R × R :=
  ((1-2/s.1)*s.2+2/s.1, -(s.2-1)^2/s.1^2)
def add (s d : R × R) (h : R) : R × R := (s.1+h*d.1, s.2+h*d.2)
def stages (s : R × R) (h : R) : (R × R) × (R × R) × (R × R) :=
  let s2 := add s (rhs s) (h/2)
  let s3 := add s (rhs s2) (h/2)
  let s4 := add s (rhs s3) h
  (s2,s3,s4)
def step (s : R × R) (h : R) : R × R :=
  let (s2,s3,s4) := stages s h
  let a := rhs s
  let b := rhs s2
  let c := rhs s3
  let d := rhs s4
  (s.1+h/6*(a.1+2*b.1+2*c.1+d.1), s.2+h/6*(a.2+2*b.2+2*c.2+d.2))
def constraint (s : R × R) : R := s.2^2-1-(2/s.1)*(s.2-1)^2

theorem initial_null : constraint ((4,-3) : ℚ × ℚ) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem stages_outside_horizon :
    let (a,b,c) := stages ((4,-3) : ℚ × ℚ) (1/2)
    2 < a.1 ∧ 2 < b.1 ∧ 2 < c.1 ∧ 2 < (step ((4,-3) : ℚ × ℚ) (1/2)).1 := by
  decide +kernel

/- Classical RK4 fails exact null conservation before rounding, even on
    an initially null ray with all stage positions outside the horizon. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem rk4_not_exactly_null : constraint (step ((4,-3) : ℚ × ℚ) (1/2)) ≠ 0 := by
  decide +kernel

def exactRay (t : ℝ) : ℝ × ℝ := (4-t, -((4-t)+2)/((4-t)-2))

theorem exactRay_initial : exactRay 0 = (4,-3) := by norm_num [exactRay]

theorem exactRay_solves (t : ℝ) (ht : t < 2) :
    HasDerivAt (fun s => (exactRay s).1) (rhs (exactRay t)).1 t ∧
      HasDerivAt (fun s => (exactRay s).2) (rhs (exactRay t)).2 t := by
  have hr : 4-t ≠ 0 := by linarith
  have hd : 4-t-2 ≠ 0 := by linarith
  have hnum := ((hasDerivAt_id' t).const_sub 4).add_const 2
  have hden := ((hasDerivAt_id' t).const_sub 4).sub_const 2
  constructor
  · convert (hasDerivAt_id' t).const_sub 4 using 1
    · rfl
    · unfold rhs exactRay
      dsimp only [Prod.fst, Prod.snd]
      field_simp
      ring
  · have h := (hnum.div hden hd).neg
    simp only [Pi.div_def, Pi.neg_def] at h
    convert h using 1
    · funext s
      simp only [exactRay, neg_div]
    · unfold rhs exactRay
      dsimp only [Prod.fst, Prod.snd]
      field_simp
      ring

/- At r=4, the production geometry limit is 0.12*(4-2)=6/25.
    Its normalized null acceptance test permits an error above TARGETS.md. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem accepted_step_exceeds_position_target :
    let s := step ((4,-3) : ℚ × ℚ) (6/25)
    let (a,b,c) := stages ((4,-3) : ℚ × ℚ) (6/25)
    |constraint s|/(1+s.2^2) < (2/10000 : ℚ) ∧
      (4-6/25 : ℚ)/1000000 < |s.1-(4-6/25)| ∧
      2 < s.1 ∧ 2 < a.1 ∧ 2 < b.1 ∧ 2 < c.1 := by
  decide +kernel

def momentum (p : ℝ) : Fin 4 → ℝ := ![1,p,0,0]
def tangent (r p : ℝ) : Fin 4 → ℝ := ![-1-2/r+2*p/r, (1-2/r)*p+2/r, 0, 0]

theorem radius_axis (r : ℝ) (hr : 0 < r) : Cartesian.radius 0 (Schwarzschild.axis r) = r := by
  rw [Schwarzschild.radius_eq_kerr, Schwarzschild.radius_axis, abs_of_pos hr]

theorem spatialEll_axis (r : ℝ) (hr : 0 < r) :
    Cartesian.spatialEll 0 (Schwarzschild.axis r) = ![1,0,0] := by
  have hr0 := ne_of_gt hr
  ext i
  simp only [Cartesian.spatialEll, radius_axis r hr]
  fin_cases i <;> simp [Cartesian.b, Schwarzschild.axis, map_zero, hr0, ← pow_two]

theorem ell_axis (r : ℝ) (hr : 0 < r) :
    Cartesian.ell 0 (Schwarzschild.axis r) = ![1,1,0,0] := by
  change Fin.cases 1 (Cartesian.spatialEll 0 (Schwarzschild.axis r)) = ![1,1,0,0]
  rw [spatialEll_axis r hr]
  rfl

theorem potential_axis (r : ℝ) (hr : 0 < r) :
    Cartesian.potential 1 0 (Schwarzschild.axis r) = 1/r := by
  have hr0 := ne_of_gt hr
  simp only [Cartesian.potential, Calculus.kerrH, radius_axis r hr, Cartesian.b,
    zero_dotProduct, zero_pow (by decide : 2 ≠ 0), add_zero, one_mul]
  field_simp

theorem tangent_from_metric (r p : ℝ) (hr : 0 < r) :
    (KerrField.metric 1 0 (Schwarzschild.axis r))⁻¹.mulVec (momentum p) = tangent r p := by
  rw [KerrField.inverse_eq_explicit 1 0 (Schwarzschild.axis r)
    (by rw [radius_axis r hr]; exact hr)]
  ext i
  fin_cases i <;>
    simp [KerrField.explicitInverse, KerrField.minkowski, KerrField.raisedEll, KerrField.signature,
      Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Fin.sum_univ_succ,
      potential_axis r hr, ell_axis r hr, momentum, tangent] <;>
    ring

theorem constraint_from_metric (r p : ℝ) (hr : 0 < r) :
    dotProduct (momentum p) ((KerrField.metric 1 0 (Schwarzschild.axis r))⁻¹.mulVec (momentum p)) =
      constraint (r,p) := by
  rw [tangent_from_metric r p hr]
  simp [dotProduct, Fin.sum_univ_succ, momentum, tangent, constraint]
  ring

theorem radial_radiusD (r : ℝ) (hr : 0 < r) (e : Fin 3) :
    Cartesian.radiusD 0 (Schwarzschild.axis r) e = if e = 0 then 1 else 0 := by
  have hr0 := ne_of_gt hr
  simp only [Cartesian.radiusD, radius_axis r hr]
  fin_cases e <;>
    simp [Cartesian.q, Cartesian.b, Schwarzschild.axis, dotProduct, Fin.sum_univ_succ,
      ← pow_two]
  field_simp
  ring

theorem radial_potentialD (r : ℝ) (hr : 0 < r) (e : Fin 3) :
    Cartesian.potentialD 1 0 (Schwarzschild.axis r) e = if e = 0 then -1/r^2 else 0 := by
  have hr0 := ne_of_gt hr
  simp only [Cartesian.potentialD, radius_axis r hr, potential_axis r hr, radial_radiusD r hr]
  fin_cases e <;> simp [Cartesian.b]
  field_simp
  ring

theorem radial_ellD_first (r : ℝ) (hr : 0 < r) (e : Fin 3) :
    Cartesian.ellD 0 (Schwarzschild.axis r) e 1 = 0 := by
  have hr0 := ne_of_gt hr
  change Cartesian.spatialEllD 0 (Schwarzschild.axis r) e 0 = 0
  simp only [Cartesian.spatialEllD, radius_axis r hr, radial_radiusD r hr, spatialEll_axis r hr]
  fin_cases e <;> simp [Cartesian.b, Cartesian.basis, Schwarzschild.axis, map_zero, hr0]
  field_simp
  ring

theorem momentum_rhs_from_metric (r p : ℝ) (hr : 0 < r) (e : Fin 3) :
    (1/2 : ℝ)*dotProduct (tangent r p)
      ((KerrField.metricD 1 0 (Schwarzschild.axis r) e.succ).mulVec (tangent r p)) =
      if e = 0 then -(p-1)^2/r^2 else 0 := by
  have hzero : Cartesian.ellD 0 (Schwarzschild.axis r) e 0 = 0 := rfl
  simp only [KerrField.metricD, Fin.cases_succ, Matrix.of_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Cartesian.metricD, radial_potentialD r hr, potential_axis r hr,
    ell_axis r hr, hzero, tangent]
  fin_cases e <;> simp [radial_ellD_first r hr]
  ring

/-- The two-dimensional counterexample uses the actual metric inverse and
    momentum equation; transverse coordinates and momenta have zero RHS. -/
theorem hamiltonian_rhs (r p : ℝ) (hr : 0 < r) :
    let k := (KerrField.metric 1 0 (Schwarzschild.axis r))⁻¹.mulVec (momentum p)
    (k 1, (1/2 : ℝ)*dotProduct k ((KerrField.metricD 1 0 (Schwarzschild.axis r) 1).mulVec k)) =
      rhs (r,p) := by
  dsimp only
  rw [tangent_from_metric r p hr]
  change ((1-2/r)*p+2/r, _) = _
  rw [show (1 : Fin 4) = (0 : Fin 3).succ from rfl, momentum_rhs_from_metric r p hr 0]
  rfl

theorem transverse_momentum_rhs (r p : ℝ) (hr : 0 < r) :
    (1/2 : ℝ)*dotProduct (tangent r p)
      ((KerrField.metricD 1 0 (Schwarzschild.axis r) 2).mulVec (tangent r p)) = 0 ∧
    (1/2 : ℝ)*dotProduct (tangent r p)
      ((KerrField.metricD 1 0 (Schwarzschild.axis r) 3).mulVec (tangent r p)) = 0 := by
  exact ⟨momentum_rhs_from_metric r p hr 1, momentum_rhs_from_metric r p hr 2⟩

end BlackHole.RadialRK4
