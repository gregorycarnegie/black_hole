module

public import BlackHole.Orbits
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section

namespace BlackHole.Kerr

def delta (a r : ℝ) : ℝ := r^2-2*r+a^2
def timeVelocity (E L a r : ℝ) : ℝ := ((r^2+a^2+2*a^2/r)*E-(2*a/r)*L)/delta a r
def phiVelocity (E L a r : ℝ) : ℝ := ((2*a/r)*E+(1-2/r)*L)/delta a r
def equatorialNorm (a r ut up ur : ℝ) : ℝ :=
  -(1-2/r)*ut^2-(4*a/r)*ut*up+(r^2+a^2+2*a^2/r)*up^2+r^2/delta a r*ur^2
def radial (E L a r : ℝ) : ℝ :=
  (E*(r^2+a^2)-a*L)^2-delta a r*(r^2+(L-a*E)^2)
def radialSlope (E L a r : ℝ) : ℝ :=
  4*(E^2-1)*r^3+6*r^2+2*(a^2*(E^2-1)-L^2)*r+2*(L-a*E)^2
def radialCurvature (E L a r : ℝ) : ℝ :=
  12*(E^2-1)*r^2+12*r+2*(a^2*(E^2-1)-L^2)

theorem conserved_charges (E L a r : ℝ) (hr : r ≠ 0) (hd : delta a r ≠ 0) :
    (1-2/r)*timeVelocity E L a r+(2*a/r)*phiVelocity E L a r = E ∧
    -(2*a/r)*timeVelocity E L a r+(r^2+a^2+2*a^2/r)*phiVelocity E L a r = L := by
  unfold timeVelocity phiVelocity
  constructor <;> field_simp <;> unfold delta <;> ring

/-- The equatorial Kerr metric normalization gives the radial first integral;
    no circular-orbit or ISCO equation is assumed in this identity. -/
theorem normalization_radial_identity (E L a r ur : ℝ)
    (hr : r ≠ 0) (hd : delta a r ≠ 0) :
    equatorialNorm a r (timeVelocity E L a r) (phiVelocity E L a r) ur+1 =
      (r^4*ur^2-radial E L a r)/(r^2*delta a r) := by
  unfold equatorialNorm timeVelocity phiVelocity radial
  field_simp
  unfold delta
  ring

theorem radial_expanded (E L a r : ℝ) :
    radial E L a r = (E^2-1)*r^4+2*r^3+(a^2*(E^2-1)-L^2)*r^2+2*(L-a*E)^2*r := by
  unfold radial delta
  ring

theorem radial_derivative (E L a r : ℝ) :
    HasDerivAt (radial E L a) (radialSlope E L a r) r := by
  have hi := hasDerivAt_id' r
  have h := ((((hi.pow 4).const_mul (E^2-1)).add ((hi.pow 3).const_mul 2)).add
    ((hi.pow 2).const_mul (a^2*(E^2-1)-L^2))).add (hi.const_mul (2*(L-a*E)^2))
  have heq : radial E L a = fun x =>
      (E^2-1)*x^4+2*x^3+(a^2*(E^2-1)-L^2)*x^2+2*(L-a*E)^2*x := by
    funext x
    exact radial_expanded E L a x
  rw [heq]
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub] at h
  convert h using 1
  unfold radialSlope
  ring

theorem radialSlope_derivative (E L a r : ℝ) :
    HasDerivAt (radialSlope E L a) (radialCurvature E L a r) r := by
  have hi := hasDerivAt_id' r
  have h := ((((hi.pow 3).const_mul (4*(E^2-1))).add ((hi.pow 2).const_mul 6)).add
    (hi.const_mul (2*(a^2*(E^2-1)-L^2)))).add_const (2*(L-a*E)^2)
  simp only [Pi.add_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one] at h
  change HasDerivAt (fun x => 4*(E^2-1)*x^3+6*x^2+2*(a^2*(E^2-1)-L^2)*x+2*(L-a*E)^2)
    (radialCurvature E L a r) r
  convert h using 1
  unfold radialCurvature
  ring

def circularDenominator (a u : ℝ) : ℝ := u^3*(u^3-3*u+2*a)
def circularEnergy (a u : ℝ) : ℝ := (u^3-2*u+a)/Real.sqrt (circularDenominator a u)
def circularMomentum (a u : ℝ) : ℝ := (u^4-2*a*u+a^2)/Real.sqrt (circularDenominator a u)

theorem circular_radial_zero (a u : ℝ) (hd : 0 < circularDenominator a u) :
    radial (circularEnergy a u) (circularMomentum a u) a (u^2) = 0 := by
  have hs := Real.sq_sqrt (le_of_lt hd)
  have hn := ne_of_gt (Real.sqrt_pos.mpr hd)
  unfold circularEnergy circularMomentum radial
  field_simp [hs]
  rw [hs]
  unfold circularDenominator delta
  ring

theorem circular_radialSlope_zero (a u : ℝ) (hd : 0 < circularDenominator a u) :
    radialSlope (circularEnergy a u) (circularMomentum a u) a (u^2) = 0 := by
  have hs := Real.sq_sqrt (le_of_lt hd)
  have hn := ne_of_gt (Real.sqrt_pos.mpr hd)
  unfold circularEnergy circularMomentum radialSlope
  field_simp [hs]
  rw [hs]
  unfold circularDenominator
  ring

theorem circular_radialCurvature (a u : ℝ) (hd : 0 < circularDenominator a u) :
    radialCurvature (circularEnergy a u) (circularMomentum a u) a (u^2) =
      -2*u^4*(u^4-6*u^2+8*a*u-3*a^2)/circularDenominator a u := by
  have hs := Real.sq_sqrt (le_of_lt hd)
  have hn := ne_of_gt (Real.sqrt_pos.mpr hd)
  unfold circularEnergy circularMomentum radialCurvature
  field_simp [hs]
  rw [hs]
  unfold circularDenominator
  ring

theorem isco_circularDenominator_pos (a : ℝ) (ha : |a| < 1) :
    0 < circularDenominator a (Real.sqrt (isco a)) := by
  have hr := isco_strictAnti a 1 (le_of_lt ha) (by norm_num)
    (lt_of_le_of_lt (le_abs_self a) ha)
  rw [isco_extremal_prograde] at hr
  let u := Real.sqrt (isco a)
  let v := Real.sqrt (3*u^2-2)
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u^2 = isco a := Real.sq_sqrt (by linarith)
  have hu1 : 1 < u := by nlinarith
  have hv2 : v^2 = 3*u^2-2 := Real.sq_sqrt (by nlinarith)
  have hv1 : 1 < v := by nlinarith [Real.sqrt_nonneg (3*u^2-2)]
  have haCurve : a = u*(4-v)/3 := by
    simpa only [iscoSpinCurve, u, v, hu2] using isco_spin_curve a (le_of_lt ha)
  have hid : u^3-3*u+2*a = u/3*(v-1)^2 := by
    calc
      _ = u/3*((3*u^2-2)+1-2*v) := by rw [haCurve]; ring
      _ = u/3*(v-1)^2 := by rw [← hv2]; ring
  change 0 < u^3*(u^3-3*u+2*a)
  rw [hid]
  exact mul_pos (pow_pos (by linarith) 3)
    (mul_pos (div_pos (by linarith) (by norm_num)) (sq_pos_of_pos (by linarith)))

/-- The implemented Bardeen radius admits timelike circular constants and is
    marginal in the equatorial Kerr radial potential, for every subextremal spin. -/
theorem isco_is_marginal_timelike_circle (a : ℝ) (ha : |a| < 1) :
    let u := Real.sqrt (isco a)
    let E := circularEnergy a u
    let L := circularMomentum a u
    radial E L a (isco a) = 0 ∧ radialSlope E L a (isco a) = 0 ∧
      radialCurvature E L a (isco a) = 0 := by
  let u := Real.sqrt (isco a)
  have hd := isco_circularDenominator_pos a ha
  have hr := isco_bounds a (le_of_lt ha)
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u^2 = isco a := Real.sq_sqrt (by linarith)
  have hp := isco_marginal_stability a (le_of_lt ha)
  rw [← hu2, Real.sqrt_sq hu0] at hp
  have hp' : u^4-6*u^2+8*a*u-3*a^2 = 0 := by nlinarith
  change radial (circularEnergy a u) (circularMomentum a u) a (isco a) = 0 ∧
    radialSlope (circularEnergy a u) (circularMomentum a u) a (isco a) = 0 ∧
    radialCurvature (circularEnergy a u) (circularMomentum a u) a (isco a) = 0
  rw [← hu2]
  refine ⟨circular_radial_zero a u hd, circular_radialSlope_zero a u hd, ?_⟩
  rw [circular_radialCurvature a u hd, hp']
  ring

/-- Negative curvature of R is radial linear stability at a circular orbit
    of the fixed-(E,L) radial first integral. The positive denominator is the
    timelike circular-orbit existence condition. -/
theorem circular_radially_stable_iff (a u : ℝ) (ha : |a| ≤ 1) (hu : 1 ≤ u)
    (hd : 0 < circularDenominator a u) :
    radialCurvature (circularEnergy a u) (circularMomentum a u) a (u^2) < 0 ↔
      isco a < u^2 := by
  rw [circular_radialCurvature a u hd, div_lt_iff₀ hd, zero_mul]
  have hp : 0 < u^4 := pow_pos (by linarith) 4
  have heq : -2*u^4*(u^4-6*u^2+8*a*u-3*a^2) < 0 ↔
      0 < u^4-6*u^2+8*a*u-3*a^2 := by
    constructor <;> intro h <;> nlinarith
  rw [heq]
  exact stability_polynomial_positive_iff a u ha hu

end BlackHole.Kerr
