module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section

namespace BlackHole

/- kerr_radius solves u² - q*u - (a·x)² = 0, where u = r². -/
def radialSquared (q ax : ℝ) : ℝ :=
  (q + Real.sqrt (q * q + 4 * ax * ax)) / 2

theorem radialSquared_solves (q ax : ℝ) :
    radialSquared q ax ^ 2 - q * radialSquared q ax - ax * ax = 0 := by
  have hs := Real.sq_sqrt (by nlinarith [sq_nonneg q, sq_nonneg ax] :
    0 ≤ q * q + 4 * ax * ax)
  unfold radialSquared
  nlinarith

theorem radialSquared_nonneg (q ax : ℝ) : 0 ≤ radialSquared q ax := by
  have hs := Real.sqrt_nonneg (q * q + 4 * ax * ax)
  have hsq := Real.sq_sqrt (by nlinarith [sq_nonneg q, sq_nonneg ax] :
    0 ≤ q * q + 4 * ax * ax)
  unfold radialSquared
  nlinarith [sq_nonneg ax]

/-- The shader's negative-q branch is algebraically the same positive root.
    Its denominator floor and the final radius floor are numerical guards. -/
theorem radialSquared_rationalized (q ax : ℝ) (hq : q < 0) :
    radialSquared q ax = 2 * ax * ax / (Real.sqrt (q * q + 4 * ax * ax) - q) := by
  have hs := Real.sqrt_nonneg (q * q + 4 * ax * ax)
  have hsq := Real.sq_sqrt (by nlinarith [sq_nonneg q, sq_nonneg ax] :
    0 ≤ q * q + 4 * ax * ax)
  have hd : Real.sqrt (q * q + 4 * ax * ax) - q ≠ 0 := by linarith
  apply (eq_div_iff hd).2
  unfold radialSquared
  nlinarith

/-- Numerator of ell's spatial part in add_kerr. The radial equation is the
    only geometric hypothesis; no axis alignment is assumed. -/
theorem kerr_ell_numerator (x a : Fin 3 → ℝ) (r : ℝ) (hr : r ≠ 0)
    (hradial : r^4 - (dotProduct x x - dotProduct a a) * r^2 -
      (dotProduct a x)^2 = 0) :
    let v := r • x - crossProduct a x + (dotProduct a x / r) • a
    dotProduct v v = (r^2 + dotProduct a a)^2 := by
  dsimp
  simp only [dotProduct_add, add_dotProduct, dotProduct_sub, sub_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  simp only [dot_self_cross, dot_cross_self, cross_dot_cross,
    dotProduct_comm x a, dotProduct_comm (crossProduct a x) x,
    dotProduct_comm (crossProduct a x) a, dot_self_cross, dot_cross_self]
  field_simp
  linear_combination -(r^2 + dotProduct a a) * hradial

theorem kerr_ell_null (x a : Fin 3 → ℝ) (r : ℝ) (hr : r ≠ 0)
    (hradial : r^4 - (dotProduct x x - dotProduct a a) * r^2 -
      (dotProduct a x)^2 = 0) :
    let ell := (1 / (r^2 + dotProduct a a)) •
      (r • x - crossProduct a x + (dotProduct a x / r) • a)
    (-1 : ℝ) + dotProduct ell ell = 0 := by
  have haa : 0 ≤ dotProduct a a := Finset.sum_nonneg (fun i _ => mul_self_nonneg (a i))
  have hd : r^2 + dotProduct a a ≠ 0 := by nlinarith [sq_pos_of_ne_zero hr]
  dsimp
  rw [smul_dotProduct, dotProduct_smul, kerr_ell_numerator x a r hr hradial]
  simp only [smul_eq_mul]
  field_simp
  norm_num

end BlackHole
