module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

@[expose] public section
noncomputable section

namespace BlackHole.Models

def timelikePotential (angularSquared r : ℝ) : ℝ := (1-2/r)*(1+angularSquared/r^2)
def potentialSlope (l r : ℝ) : ℝ := 2/r^2-2*l/r^3+6*l/r^4
def potentialCurvature (l r : ℝ) : ℝ := -4/r^3+6*l/r^4-24*l/r^5

theorem timelikePotential_derivative (l r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (timelikePotential l) (potentialSlope l r) r := by
  have hi := hasDerivAt_id' r
  have ha := (hasDerivAt_const r (1 : ℝ)).sub ((hasDerivAt_const r (2 : ℝ)).div hi hr)
  have hb := (hasDerivAt_const r (1 : ℝ)).add
    ((hasDerivAt_const r l).div (hi.pow 2) (pow_ne_zero 2 hr))
  have h := ha.mul hb
  simp only [Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply,
    Nat.cast_ofNat, Nat.reduceSub, pow_one] at h
  change HasDerivAt (fun x => (1-2/x)*(1+l/x^2)) (potentialSlope l r) r
  convert h using 1
  unfold potentialSlope
  field_simp
  ring

theorem potentialSlope_derivative (l r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (potentialSlope l) (potentialCurvature l r) r := by
  have hi := hasDerivAt_id' r
  have h := (((hasDerivAt_const r (2 : ℝ)).div (hi.pow 2) (pow_ne_zero 2 hr)).sub
    ((hasDerivAt_const r (2*l)).div (hi.pow 3) (pow_ne_zero 3 hr))).add
    ((hasDerivAt_const r (6*l)).div (hi.pow 4) (pow_ne_zero 4 hr))
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one] at h
  change HasDerivAt (fun x => 2/x^2-2*l/x^3+6*l/x^4) (potentialCurvature l r) r
  convert h using 1
  unfold potentialCurvature
  field_simp
  ring

theorem schwarzschild_circular_orbit (r : ℝ) (hr : 3 < r) :
    potentialSlope (r^2/(r-3)) r = 0 := by
  have hr0 : r ≠ 0 := by linarith
  have hr3 : r-3 ≠ 0 := by linarith
  unfold potentialSlope
  field_simp
  ring

theorem schwarzschild_circular_curvature (r : ℝ) (hr : 3 < r) :
    potentialCurvature (r^2/(r-3)) r = 2*(r-6)/(r^3*(r-3)) := by
  have hr0 : r ≠ 0 := by linarith
  have hr3 : r-3 ≠ 0 := by linarith
  unfold potentialCurvature
  field_simp
  ring

/-- The stable exterior Schwarzschild circular-orbit branch starts at 6M. -/
theorem schwarzschild_circular_stable_iff (r : ℝ) (hr : 3 < r) :
    0 < potentialCurvature (r^2/(r-3)) r ↔ 6 < r := by
  rw [schwarzschild_circular_curvature r hr]
  have hd : 0 < r^3*(r-3) := mul_pos (pow_pos (by linarith) 3) (by linarith)
  rw [div_pos_iff_of_pos_right hd]
  constructor <;> intro h <;> linarith

def embedding (rs r : ℝ) : ℝ := 2*Real.sqrt (rs*(r-rs))

theorem embedding_derivative (rs r : ℝ) (hrs : 0 < rs) (hr : rs < r) :
    HasDerivAt (embedding rs) (rs/Real.sqrt (rs*(r-rs))) r := by
  have hp : 0 < rs*(r-rs) := mul_pos hrs (by linarith)
  have h := ((((hasDerivAt_id' r).sub_const rs).const_mul rs).sqrt (ne_of_gt hp)).const_mul 2
  change HasDerivAt (fun x => 2*Real.sqrt (rs*(x-rs))) _ r
  convert h using 1
  field_simp

theorem embedding_induced_metric (rs r : ℝ) (hrs : 0 < rs) (hr : rs < r) :
    1+(rs/Real.sqrt (rs*(r-rs)))^2 = 1/(1-rs/r) := by
  have hp : 0 < rs*(r-rs) := mul_pos hrs (by linarith)
  have hsq := Real.sq_sqrt (le_of_lt hp)
  have hn := ne_of_gt (Real.sqrt_pos.mpr hp)
  have hr0 : r ≠ 0 := by linarith
  have hgap : r-rs ≠ 0 := by linarith
  rw [div_pow, hsq]
  field_simp
  ring

theorem clamped_embedding_interior (rs r : ℝ) (hr : r ≤ rs) :
    2*Real.sqrt (rs*max (r-rs) 0)-(24/5 : ℝ) = -24/5 := by
  rw [max_eq_right (by linarith)]
  norm_num

theorem clamped_embedding_exterior (rs r : ℝ) (hr : rs ≤ r) :
    2*Real.sqrt (rs*max (r-rs) 0)-(24/5 : ℝ) = embedding rs r-24/5 := by
  rw [max_eq_left (by linarith)]
  rfl

theorem disk_transition_weight (x : ℝ) : 0 ≤ (1+Real.tanh x)/2 ∧ (1+Real.tanh x)/2 ≤ 1 := by
  have hl := Real.neg_one_lt_tanh x
  have hu := Real.tanh_lt_one x
  constructor <;> linarith

theorem disk_height_blend_bounds (thin hot weight : ℝ) (hh : thin ≤ hot)
    (hw0 : 0 ≤ weight) (hw1 : weight ≤ 1) :
    thin ≤ weight*thin+(1-weight)*hot ∧ weight*thin+(1-weight)*hot ≤ hot := by
  constructor <;> nlinarith [mul_nonneg hw0 (sub_nonneg.mpr hh),
    mul_nonneg (sub_nonneg.mpr hw1) (sub_nonneg.mpr hh)]

theorem slim_height_weight (ratio : ℝ) : 0 < 1/(1+ratio^2) ∧ 1/(1+ratio^2) ≤ 1 := by
  have hd : 0 < 1+ratio^2 := by positivity
  constructor
  · exact one_div_pos.mpr hd
  · rw [div_le_iff₀ hd]
    nlinarith [sq_nonneg ratio]

theorem warp_height_bound (r tilt weight phase : ℝ) (hr : 0 ≤ r)
    (hw0 : 0 ≤ weight) (hw1 : weight ≤ 1) :
    |r*Real.sin (tilt*weight)*Real.sin phase| ≤ r*|tilt| := by
  have hb : |Real.sin (tilt*weight)| ≤ |tilt| := by
    calc
      _ ≤ |tilt*weight| := Real.abs_sin_le_abs
      _ = |tilt| * weight := by rw [abs_mul, abs_of_nonneg hw0]
      _ ≤ |tilt| := by nlinarith [abs_nonneg tilt]
  rw [abs_mul, abs_mul, abs_of_nonneg hr]
  calc
    _ ≤ (r*|Real.sin (tilt*weight)|)*1 :=
      mul_le_mul_of_nonneg_left (Real.abs_sin_le_one phase) (mul_nonneg hr (abs_nonneg _))
    _ ≤ r*|tilt| := by simpa using mul_le_mul_of_nonneg_left hb hr

def temperatureFourthPower (u : ℝ) : ℝ := u^6*(1-u)

theorem temperatureFourthPower_derivative (u : ℝ) :
    HasDerivAt temperatureFourthPower (u^5*(6-7*u)) u := by
  have h := ((hasDerivAt_id' u).pow 6).mul ((hasDerivAt_id' u).const_sub 1)
  simp only [Pi.pow_apply] at h
  change HasDerivAt (fun x => x^6*(1-x)) _ u
  convert h using 1
  ring

theorem temperature_peak : IsMaxOn temperatureFourthPower (Set.Icc 0 1) (6/7) := by
  apply isMaxOn_Icc_of_deriv
  · exact (temperatureFourthPower_derivative 0).continuousAt
  · exact (temperatureFourthPower_derivative (6/7)).continuousAt
  · exact (temperatureFourthPower_derivative 1).continuousAt
  · exact fun u _ => (temperatureFourthPower_derivative u).differentiableAt.differentiableWithinAt
  · exact fun u _ => (temperatureFourthPower_derivative u).differentiableAt.differentiableWithinAt
  · intro u hu
    rw [(temperatureFourthPower_derivative u).deriv]
    exact mul_nonneg (pow_nonneg (le_of_lt hu.1) 5) (by linarith [hu.2])
  · intro u hu
    rw [(temperatureFourthPower_derivative u).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (by linarith [hu.1]) 5) (by linarith [hu.1])

theorem temperature_peak_radius_ratio : (1/(6/7 : ℝ))^2 = 49/36 := by norm_num

def diskTemperature (u : ℝ) : ℝ :=
  u*Real.sqrt u*Real.sqrt (Real.sqrt (max (1-u) 0))

theorem diskTemperature_fourth_power (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    diskTemperature u^4 = temperatureFourthPower u := by
  have hgap : 0 ≤ 1-u := by linarith
  have hsq := Real.sq_sqrt hu
  have hsq2 := Real.sq_sqrt hgap
  have hsq3 := Real.sq_sqrt (Real.sqrt_nonneg (1-u))
  have hfour : (Real.sqrt u)^4 = u^2 := by
    calc
      _ = ((Real.sqrt u)^2)^2 := by ring
      _ = u^2 := by rw [hsq]
  have hfour2 : (Real.sqrt (Real.sqrt (1-u)))^4 = 1-u := by
    calc
      _ = ((Real.sqrt (Real.sqrt (1-u)))^2)^2 := by ring
      _ = (Real.sqrt (1-u))^2 := by rw [hsq3]
      _ = 1-u := hsq2
  unfold diskTemperature temperatureFourthPower
  rw [max_eq_left hgap, mul_pow, mul_pow, hfour, hfour2]
  ring

theorem diskTemperature_peak (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    diskTemperature u ≤ diskTemperature (6/7) := by
  apply le_of_pow_le_pow_left₀ (n := 4) (by decide) (by unfold diskTemperature; positivity)
  rw [diskTemperature_fourth_power u hu hu1,
    diskTemperature_fourth_power (6/7) (by norm_num) (by norm_num)]
  exact temperature_peak ⟨hu, hu1⟩

end BlackHole.Models
