module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section

namespace BlackHole

def iscoZ1 (a : ℝ) : ℝ :=
  1+(1-|a| * |a|)^(1/3 : ℝ)*((1+|a|)^(1/3 : ℝ)+(1-|a|)^(1/3 : ℝ))
def iscoZ2 (a : ℝ) : ℝ := Real.sqrt (3 * |a| * |a|+iscoZ1 a^2)
def isco (a : ℝ) : ℝ := 3+iscoZ2 a+(if 0 ≤ a then -1 else 1)*
  Real.sqrt ((3-iscoZ1 a)*(3+iscoZ1 a+2*iscoZ2 a))

theorem isco_zero : isco 0 = 6 := by norm_num [isco, iscoZ1, iscoZ2]
theorem isco_extremal_prograde : isco 1 = 1 := by
  norm_num [isco, iscoZ1, iscoZ2, Real.zero_rpow]
theorem isco_extremal_retrograde : isco (-1) = 9 := by
  norm_num [isco, iscoZ1, iscoZ2, Real.zero_rpow]

theorem cubeRoot_cube (x : ℝ) (hx : 0 ≤ x) : (x^(1/3 : ℝ))^3 = x := by
  rw [← Real.rpow_mul_natCast hx]
  norm_num

theorem iscoZ1_cubic (a : ℝ) (ha : |a| ≤ 1) :
    iscoZ1 a^3-3*iscoZ1 a^2+3*a^2*iscoZ1 a-a^2 = 0 := by
  have hm : 0 ≤ 1-|a| := by linarith
  have hp : 0 ≤ 1+|a| := by positivity
  have ha2 : 0 ≤ 1-|a| * |a| := by nlinarith [abs_nonneg a]
  let p := (1+|a|)^(1/3 : ℝ)
  let q := (1-|a|)^(1/3 : ℝ)
  let w := (1-|a| * |a|)^(1/3 : ℝ)
  have hp3 : p^3 = 1+|a| := cubeRoot_cube _ hp
  have hq3 : q^3 = 1-|a| := cubeRoot_cube _ hm
  have hw3 : w^3 = 1-a^2 := by
    simpa [w, sq_abs, ← sq] using cubeRoot_cube (1-|a| * |a|) ha2
  have hpq : p*q = w := by
    dsimp [p, q, w]
    rw [← Real.mul_rpow hp hm]
    congr 1
    ring
  have hsum : (p+q)^3 = 2+3*w*(p+q) := by
    calc
      _ = p^3+q^3+3*(p*q)*(p+q) := by ring
      _ = 2+3*w*(p+q) := by rw [hp3, hq3, hpq]; ring
  have hu : (w*(p+q))^3 = (1-a^2)*(2+3*(w*(p+q))) := by
    rw [mul_pow, hw3, hsum]
    ring
  change (1+w*(p+q))^3-3*(1+w*(p+q))^2+3*a^2*(1+w*(p+q))-a^2 = 0
  linear_combination hu

theorem iscoZ1_bounds (a : ℝ) (ha : |a| ≤ 1) : 1 ≤ iscoZ1 a ∧ iscoZ1 a ≤ 3 := by
  have hm : 0 ≤ 1-|a| := by linarith
  have hp : 0 ≤ 1+|a| := by positivity
  have ha2 : 0 ≤ 1-|a| * |a| := by nlinarith [abs_nonneg a]
  have hl : 1 ≤ iscoZ1 a := by
    unfold iscoZ1
    exact le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg ha2 _) (add_nonneg
      (Real.rpow_nonneg hp _) (Real.rpow_nonneg hm _)))
  refine ⟨hl, ?_⟩
  by_contra h
  have hz : 3 < iscoZ1 a := lt_of_not_ge h
  have hpos : 0 < (iscoZ1 a)^2*(iscoZ1 a-3) :=
    mul_pos (sq_pos_of_pos (by linarith)) (by linarith)
  have han : 0 ≤ a^2*(3*iscoZ1 a-1) := mul_nonneg (sq_nonneg a) (by linarith)
  nlinarith [iscoZ1_cubic a ha]

theorem iscoZ2_square (a : ℝ) : iscoZ2 a^2 = 3*a^2+iscoZ1 a^2 := by
  unfold iscoZ2
  have h : 3 * |a| * |a| = 3*a^2 := by nlinarith [sq_abs a]
  rw [h, Real.sq_sqrt (by positivity)]

theorem isco_auxiliary_relation (a : ℝ) (ha : |a| ≤ 1) :
    (3-iscoZ1 a)*iscoZ2 a^2 = 8*a^2 := by
  linear_combination (3-iscoZ1 a)*(iscoZ2_square a)-iscoZ1_cubic a ha

theorem iscoZ2_bounds (a : ℝ) (ha : |a| ≤ 1) : 2 ≤ iscoZ2 a ∧ iscoZ2 a ≤ 3 := by
  obtain ⟨hz1, hz3⟩ := iscoZ1_bounds a ha
  have hz0 : 0 ≤ iscoZ2 a := Real.sqrt_nonneg _
  have hrel : (3*iscoZ1 a-1)*iscoZ2 a^2 = 8*iscoZ1 a^2 := by
    linear_combination 8*(iscoZ2_square a)-3*(isco_auxiliary_relation a ha)
  constructor
  · by_contra h
    have hlt : iscoZ2 a < 2 := lt_of_not_ge h
    have hpos : 0 < (3*iscoZ1 a-1)*(4-iscoZ2 a^2) := mul_pos (by linarith) (by nlinarith)
    have hnonneg := mul_nonneg (show 0 ≤ 2*iscoZ1 a-1 by linarith) (show 0 ≤ iscoZ1 a-1 by linarith)
    nlinarith
  · by_contra h
    have hlt : 3 < iscoZ2 a := lt_of_not_ge h
    have hpos : 0 < (3*iscoZ1 a-1)*(iscoZ2 a^2-9) := mul_pos (by linarith) (by nlinarith)
    have hnonpos := mul_nonpos_of_nonpos_of_nonneg (show iscoZ1 a-3 ≤ 0 by linarith)
      (show 0 ≤ 8*iscoZ1 a-3 by linarith)
    nlinarith

theorem isco_radical_square (a : ℝ) (ha : |a| ≤ 1) :
    ((if 0 ≤ a then (-1 : ℝ) else 1)*
      Real.sqrt ((3-iscoZ1 a)*(3+iscoZ1 a+2*iscoZ2 a)))^2 =
      (3-iscoZ1 a)*(3+iscoZ1 a+2*iscoZ2 a) := by
  obtain ⟨hz1, hz3⟩ := iscoZ1_bounds a ha
  obtain ⟨hw2, hw3⟩ := iscoZ2_bounds a ha
  have hn : 0 ≤ (3-iscoZ1 a)*(3+iscoZ1 a+2*iscoZ2 a) := mul_nonneg (by linarith) (by linarith)
  split <;> simp [Real.sq_sqrt hn]

theorem isco_squared_stability (a : ℝ) (ha : |a| ≤ 1) :
    (isco a^2-6*isco a-3*a^2)^2 = 64*a^2*isco a := by
  let z := iscoZ1 a
  let w := iscoZ2 a
  let d := (if 0 ≤ a then (-1 : ℝ) else 1)*Real.sqrt ((3-z)*(3+z+2*w))
  have hd : d^2 = (3-z)*(3+z+2*w) := isco_radical_square a ha
  have hx : (3+w+d)^2-6*(3+w+d)-3*a^2 = 2*w*(3-z+d) := by
    nlinarith [iscoZ2_square a]
  have hquad : (3-z+d)^2 = 2*(3-z)*(3+w+d) := by nlinarith [hd]
  change ((3+w+d)^2-6*(3+w+d)-3*a^2)^2 = 64*a^2*(3+w+d)
  rw [hx]
  calc
    _ = 4*w^2*(3-z+d)^2 := by ring
    _ = 8*((3-z)*w^2)*(3+w+d) := by rw [hquad]; ring
    _ = 64*a^2*(3+w+d) := by rw [isco_auxiliary_relation a ha]; ring

theorem isco_bounds (a : ℝ) (ha : |a| ≤ 1) : 1 ≤ isco a ∧ isco a ≤ 9 := by
  obtain ⟨hz1, hz3⟩ := iscoZ1_bounds a ha
  obtain ⟨hw2, hw3⟩ := iscoZ2_bounds a ha
  have hd := isco_radical_square a ha
  let d := (if 0 ≤ a then (-1 : ℝ) else 1)*
    Real.sqrt ((3-iscoZ1 a)*(3+iscoZ1 a+2*iscoZ2 a))
  have hprod := mul_nonneg (show 0 ≤ iscoZ1 a-1 by linarith)
    (show 0 ≤ iscoZ1 a+1+2*iscoZ2 a by linarith)
  have hsq : d^2 ≤ (2+iscoZ2 a)^2 := by dsimp [d]; nlinarith
  have habs := (sq_le_sq).mp hsq
  rw [abs_of_nonneg (show 0 ≤ 2+iscoZ2 a by linarith)] at habs
  have hl : 1 ≤ isco a := by
    have hdlo := (abs_le.mp habs).1
    change 1 ≤ 3+iscoZ2 a+d
    linarith
  refine ⟨hl, ?_⟩
  by_contra h
  have hr : 9 < isco a := lt_of_not_ge h
  have ha2 : a^2 ≤ 1 := by nlinarith [sq_abs a, abs_nonneg a]
  have hpos : 0 < (isco a-1)^3*(isco a-9) := mul_pos (pow_pos (by linarith) 3) (by linarith)
  have hnonneg := mul_nonneg (show 0 ≤ 1-a^2 by linarith)
    (show 0 ≤ 6*isco a^2+28*isco a+9*a^2+9 by positivity)
  nlinarith [isco_squared_stability a ha]

theorem isco_stability_expression (a : ℝ) (ha : |a| ≤ 1) :
    isco a^2-6*isco a-3*a^2 = 2*iscoZ2 a*(3-iscoZ1 a+
      (if 0 ≤ a then (-1 : ℝ) else 1)*Real.sqrt ((3-iscoZ1 a)*(3+iscoZ1 a+2*iscoZ2 a))) := by
  have hd := isco_radical_square a ha
  have hz := iscoZ2_square a
  unfold isco
  nlinarith

/-- The unsquared marginal-stability equation, including the sign selecting
    prograde versus retrograde orbits in the actual Bardeen formula. -/
theorem isco_marginal_stability (a : ℝ) (ha : |a| ≤ 1) :
    isco a^2-6*isco a+8*a*Real.sqrt (isco a)-3*a^2 = 0 := by
  obtain ⟨hr1, hr9⟩ := isco_bounds a ha
  obtain ⟨hz1, hz3⟩ := iscoZ1_bounds a ha
  obtain ⟨hw2, hw3⟩ := iscoZ2_bounds a ha
  let root := Real.sqrt ((3-iscoZ1 a)*(3+iscoZ1 a+2*iscoZ2 a))
  have harg : 0 ≤ (3-iscoZ1 a)*(3+iscoZ1 a+2*iscoZ2 a) :=
    mul_nonneg (by linarith) (by linarith)
  have hroot : 3-iscoZ1 a ≤ root := by
    apply (sq_le_sq₀ (by linarith) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt harg]
    have hp := mul_nonneg (show 0 ≤ 3-iscoZ1 a by linarith)
      (show 0 ≤ iscoZ1 a+iscoZ2 a by linarith)
    nlinarith
  have hs : (isco a^2-6*isco a-3*a^2)^2 = (8*a*Real.sqrt (isco a))^2 := by
    rw [isco_squared_stability a ha]
    have hr := Real.sq_sqrt (show 0 ≤ isco a by linarith)
    calc
      _ = 64*a^2*(Real.sqrt (isco a))^2 := by rw [hr]
      _ = (8*a*Real.sqrt (isco a))^2 := by ring
  by_cases hapos : 0 ≤ a
  · have hx : isco a^2-6*isco a-3*a^2 ≤ 0 := by
      rw [isco_stability_expression a ha, ite_eq_left hapos]
      apply mul_nonpos_of_nonneg_of_nonpos (by linarith)
      dsimp [root] at hroot
      linarith
    have hy : 0 ≤ 8*a*Real.sqrt (isco a) := by positivity
    have heq := (sq_eq_sq₀ (neg_nonneg.mpr hx) hy).mp (by simpa only [neg_sq] using hs)
    linarith
  · have hx : 0 ≤ isco a^2-6*isco a-3*a^2 := by
      rw [isco_stability_expression a ha, ite_eq_right hapos]
      positivity
    have hy : 0 ≤ -(8*a*Real.sqrt (isco a)) := by
      have hn : a < 0 := lt_of_not_ge hapos
      nlinarith [Real.sqrt_nonneg (isco a)]
    have heq := (sq_eq_sq₀ hx hy).mp (by simpa only [neg_sq] using hs)
    linarith

def iscoSpinCurve (u : ℝ) : ℝ := u*(4-Real.sqrt (3*u^2-2))/3

theorem iscoSpinCurve_derivative (u : ℝ) (hu : 1 ≤ u) :
    HasDerivAt iscoSpinCurve
      (-2*(Real.sqrt (3*u^2-2)-1)^2/(3*Real.sqrt (3*u^2-2))) u := by
  have hp : 0 < 3*u^2-2 := by nlinarith
  have hroot := (((hasDerivAt_id' u).pow 2).const_mul 3).sub_const 2
  have hs := (hroot.sqrt (ne_of_gt hp)).const_sub 4
  have h := ((hasDerivAt_id' u).mul hs).div_const 3
  have hsq := Real.sq_sqrt (le_of_lt hp)
  have hn := ne_of_gt (Real.sqrt_pos.mpr hp)
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] at h
  change HasDerivAt (fun x => x*(4-Real.sqrt (3*x^2-2))/3) _ u
  convert h using 1
  field_simp
  nlinarith

theorem iscoSpinCurve_strictAnti : StrictAntiOn iscoSpinCurve (Set.Ici 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 1)
  · exact fun u hu => (iscoSpinCurve_derivative u hu).continuousAt.continuousWithinAt
  · intro u hu
    rw [interior_Ici] at hu
    have hu1 : 1 < u := hu
    rw [(iscoSpinCurve_derivative u (le_of_lt hu1)).deriv]
    have hsq := Real.sq_sqrt (show 0 ≤ 3*u^2-2 by nlinarith)
    have hroot : 1 < Real.sqrt (3*u^2-2) := by nlinarith [Real.sqrt_nonneg (3*u^2-2)]
    apply div_neg_of_neg_of_pos
    · nlinarith [sq_pos_of_pos (show 0 < Real.sqrt (3*u^2-2)-1 by linarith)]
    · linarith

theorem isco_spin_curve (a : ℝ) (ha : |a| ≤ 1) :
    a = iscoSpinCurve (Real.sqrt (isco a)) := by
  obtain ⟨hr1, hr9⟩ := isco_bounds a ha
  let u := Real.sqrt (isco a)
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u^2 = isco a := Real.sq_sqrt (by linarith)
  have hu1 : 1 ≤ u := by nlinarith
  have ha1 : a ≤ 1 := le_trans (le_abs_self a) ha
  have hmargin := isco_marginal_stability a ha
  have hpoly : (3*a-4*u)^2 = u^2*(3*u^2-2) := by
    rw [← hu2, Real.sqrt_sq hu0] at hmargin
    linear_combination -3*hmargin
  have hroot := Real.sq_sqrt (show 0 ≤ 3*u^2-2 by nlinarith)
  have hneg : 0 ≤ -(3*a-4*u) := by linarith
  have hpos : 0 ≤ u*Real.sqrt (3*u^2-2) := mul_nonneg hu0 (Real.sqrt_nonneg _)
  have hsquares : (-(3*a-4*u))^2 = (u*Real.sqrt (3*u^2-2))^2 := by
    rw [neg_sq, mul_pow, hroot]
    exact hpoly
  have heq := (sq_eq_sq₀ hneg hpos).mp hsquares
  change a = u*(4-Real.sqrt (3*u^2-2))/3
  linarith

theorem isco_strictAnti (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hab : a < b) :
    isco b < isco a := by
  have hra := isco_bounds a ha
  have hrb := isco_bounds b hb
  have ha2 := Real.sq_sqrt (show 0 ≤ isco a by linarith)
  have hb2 := Real.sq_sqrt (show 0 ≤ isco b by linarith)
  have hua : 1 ≤ Real.sqrt (isco a) := by nlinarith [Real.sqrt_nonneg (isco a)]
  have hub : 1 ≤ Real.sqrt (isco b) := by nlinarith [Real.sqrt_nonneg (isco b)]
  have hlt : Real.sqrt (isco b) < Real.sqrt (isco a) := by
    apply (iscoSpinCurve_strictAnti.lt_iff_gt hua hub).mp
    simpa only [← isco_spin_curve a ha, ← isco_spin_curve b hb] using hab
  nlinarith [Real.sqrt_nonneg (isco b)]

theorem isco_delta (a : ℝ) (ha : |a| ≤ 1) :
    isco a^2-2*isco a+a^2 =
      (4/9)*isco a*(Real.sqrt (3*isco a-2)-1)^2 := by
  have hr := isco_bounds a ha
  let u := Real.sqrt (isco a)
  let v := Real.sqrt (3*u^2-2)
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u^2 = isco a := Real.sq_sqrt (by linarith)
  have hv2 : v^2 = 3*u^2-2 := Real.sq_sqrt (by nlinarith)
  have haCurve : a = u*(4-v)/3 := by
    have h := isco_spin_curve a ha
    simpa only [iscoSpinCurve, u, v, hu2] using h
  rw [← hu2, haCurve]
  change (u^2)^2-2*u^2+(u*(4-v)/3)^2 = (4/9)*u^2*(v-1)^2
  field_simp
  linear_combination -27*u^2*hv2

theorem stability_polynomial_factor (a u : ℝ) (hu : 1 ≤ u) :
    u^4-6*u^2+8*a*u-3*a^2 =
      (a-iscoSpinCurve u)*(u*(4+Real.sqrt (3*u^2-2))-3*a) := by
  have hs := Real.sq_sqrt (show 0 ≤ 3*u^2-2 by nlinarith)
  unfold iscoSpinCurve
  linear_combination -u^2/3*hs

theorem stability_other_factor_pos (a u : ℝ) (ha : a ≤ 1) (hu : 1 ≤ u) :
    0 < u*(4+Real.sqrt (3*u^2-2))-3*a := by
  have hs := Real.sqrt_nonneg (3*u^2-2)
  have hp := mul_nonneg (show 0 ≤ u by linarith) hs
  nlinarith

/-- The marginal polynomial has a unique root in r >= 1 for each admitted
    spin, so the closed form cannot select a different exterior branch. -/
theorem isco_unique_marginal_root (a u : ℝ) (ha : |a| ≤ 1) (hu : 1 ≤ u)
    (hzero : u^4-6*u^2+8*a*u-3*a^2 = 0) : u^2 = isco a := by
  rw [stability_polynomial_factor a u hu] at hzero
  have hfac := stability_other_factor_pos a u (le_trans (le_abs_self a) ha) hu
  have heq := (mul_eq_zero.mp hzero).resolve_right (ne_of_gt hfac)
  have hcurve : iscoSpinCurve u = iscoSpinCurve (Real.sqrt (isco a)) := by
    rw [← isco_spin_curve a ha]
    linarith
  have hr := isco_bounds a ha
  have hs := Real.sq_sqrt (show 0 ≤ isco a by linarith)
  have hu0 : 1 ≤ Real.sqrt (isco a) := by nlinarith [Real.sqrt_nonneg (isco a)]
  have hroot := iscoSpinCurve_strictAnti.injOn hu hu0 hcurve
  rw [hroot, hs]

theorem stability_polynomial_positive_iff (a u : ℝ) (ha : |a| ≤ 1) (hu : 1 ≤ u) :
    0 < u^4-6*u^2+8*a*u-3*a^2 ↔ isco a < u^2 := by
  have hr := isco_bounds a ha
  have hs := Real.sq_sqrt (show 0 ≤ isco a by linarith)
  have hu0 : 1 ≤ Real.sqrt (isco a) := by nlinarith [Real.sqrt_nonneg (isco a)]
  rw [stability_polynomial_factor a u hu,
    mul_pos_iff_of_pos_right (stability_other_factor_pos a u (le_trans (le_abs_self a) ha) hu),
    sub_pos]
  have hlt : iscoSpinCurve u < a ↔ Real.sqrt (isco a) < u := by
    conv_lhs => rw [isco_spin_curve a ha]
    exact iscoSpinCurve_strictAnti.lt_iff_gt hu hu0
  rw [hlt]
  constructor <;> intro h <;> nlinarith

end BlackHole
