module

public import BlackHole.KerrAlgebra
public import BlackHole.KerrCurvature

@[expose] public section
noncomputable section

namespace BlackHole.KerrField

open Cartesian (Space)

def signature (i : Fin 4) : ℝ := if i = 0 then -1 else 1
def minkowski : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal signature
def raisedEll (a x : Space) (i : Fin 4) : ℝ := signature i*Cartesian.ell a x i
def explicitInverse (mass : ℝ) (a x : Space) : Matrix (Fin 4) (Fin 4) ℝ :=
  minkowski-(2*Cartesian.potential mass a x) • Matrix.vecMulVec (raisedEll a x) (raisedEll a x)

theorem signature_square (i : Fin 4) : signature i*signature i = 1 := by
  by_cases h : i = 0 <;> simp [signature, h]

theorem minkowski_square : minkowski*minkowski = 1 := by
  simp only [minkowski, Matrix.diagonal_mul_diagonal, signature_square]
  rfl

theorem null_rank_one_inverse (l : Fin 4 → ℝ) (c : ℝ)
    (hl : dotProduct l (fun i => signature i*l i) = 0) :
    (minkowski+c • Matrix.vecMulVec l l)*
      (minkowski-c • Matrix.vecMulVec (fun i => signature i*l i) (fun i => signature i*l i)) = 1 := by
  let v := fun i => signature i*l i
  have hlv : dotProduct l v = 0 := hl
  have hleft : minkowski.mulVec v = l := by
    ext i
    simp only [minkowski, Matrix.mulVec_diagonal, v, ← mul_assoc, signature_square, one_mul]
  have hright : Matrix.vecMul l minkowski = v := by
    ext i
    simp only [minkowski, Matrix.vecMul_diagonal, v]
    ring
  change (minkowski+c • Matrix.vecMulVec l l)*(minkowski-c • Matrix.vecMulVec v v) = 1
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul]
  rw [Matrix.vecMulVec_mul_vecMulVec]
  simp only [minkowski_square, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hleft, hright, hlv, zero_smul,
    Matrix.vecMulVec_zero, smul_zero]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul]
  ring

theorem radius_squared (a x : Space) :
    Cartesian.radius a x^2 = radialSquared (Cartesian.q a x) (Cartesian.b a x) := by
  have heq : (Cartesian.q a x+Real.sqrt (Cartesian.q a x^2+4*Cartesian.b a x^2))/2 =
      radialSquared (Cartesian.q a x) (Cartesian.b a x) := by
    unfold radialSquared
    congr 3
    ring
  unfold Cartesian.radius Calculus.kerrRadius
  rw [heq]
  exact Real.sq_sqrt (radialSquared_nonneg _ _)

theorem radial_relation (a x : Space) :
    Cartesian.radius a x^4-Cartesian.q a x*Cartesian.radius a x^2-Cartesian.b a x^2 = 0 := by
  have h := radialSquared_solves (Cartesian.q a x) (Cartesian.b a x)
  rw [← radius_squared a x] at h
  nlinarith

theorem spatialEll_unit (a x : Space) (hr : 0 < Cartesian.radius a x) :
    -1+dotProduct (Cartesian.spatialEll a x) (Cartesian.spatialEll a x) = 0 := by
  have hradial := radial_relation a x
  unfold Cartesian.q Cartesian.b at hradial
  have h := kerr_ell_null x a (Cartesian.radius a x) (ne_of_gt hr) hradial
  dsimp at h
  have heq : (1/(Cartesian.radius a x^2+dotProduct a a)) •
      (Cartesian.radius a x • x-crossProduct a x+(dotProduct a x/Cartesian.radius a x) • a) =
      Cartesian.spatialEll a x := by
    ext i
    simp only [Cartesian.spatialEll, Cartesian.b, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [heq] at h
  exact h

theorem ell_null (a x : Space) (hr : 0 < Cartesian.radius a x) :
    dotProduct (Cartesian.ell a x) (raisedEll a x) = 0 := by
  rw [dotProduct, Fin.sum_univ_succ]
  simp only [Cartesian.ell, raisedEll, signature, Fin.cases_zero, Fin.cases_succ,
    Fin.succ_ne_zero, ite_true, ite_false, mul_one, one_mul]
  exact spatialEll_unit a x hr

theorem metric_rank_one (mass : ℝ) (a x : Space) :
    metric mass a x = minkowski+(2*Cartesian.potential mass a x) •
      Matrix.vecMulVec (Cartesian.ell a x) (Cartesian.ell a x) := by
  ext i j
  simp only [metric, Matrix.of_apply, Cartesian.metric, minkowski, Matrix.add_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, Matrix.diagonal_apply, signature,
    Cartesian.eta]
  ring

theorem metric_mul_explicitInverse (mass : ℝ) (a x : Space) (hr : 0 < Cartesian.radius a x) :
    metric mass a x*explicitInverse mass a x = 1 := by
  rw [metric_rank_one]
  exact null_rank_one_inverse (Cartesian.ell a x) (2*Cartesian.potential mass a x) (ell_null a x hr)

theorem inverse_eq_explicit (mass : ℝ) (a x : Space) (hr : 0 < Cartesian.radius a x) :
    (metric mass a x)⁻¹ = explicitInverse mass a x :=
  Matrix.inv_eq_right_inv (metric_mul_explicitInverse mass a x hr)

theorem metric_nonsingular (mass : ℝ) (a x : Space) (hr : 0 < Cartesian.radius a x) :
    (metric mass a x).det ≠ 0 :=
  Matrix.det_ne_zero_of_right_inverse (metric_mul_explicitInverse mass a x hr)

theorem metric_symmetric (mass : ℝ) (a x : Space) (i j : Fin 4) :
    metric mass a x i j = metric mass a x j i := by
  simp only [metric, Matrix.of_apply, Cartesian.metric, Cartesian.eta]
  by_cases h : i = j
  · subst j
    rfl
  · simp only [ite_eq_right h, ite_eq_right (Ne.symm h)]
    ring

theorem potential_nonnegative (mass : ℝ) (a x : Space) (hm : 0 ≤ mass)
    (hr : 0 < Cartesian.radius a x) : 0 ≤ Cartesian.potential mass a x := by
  unfold Cartesian.potential Calculus.kerrH
  positivity

theorem inverse_time_negative (mass : ℝ) (a x : Space) (hm : 0 ≤ mass)
    (hr : 0 < Cartesian.radius a x) : (metric mass a x)⁻¹ 0 0 < 0 := by
  rw [inverse_eq_explicit mass a x hr]
  simp only [explicitInverse, minkowski, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.diagonal_apply_eq, signature, ite_true, Matrix.vecMulVec_apply, raisedEll,
    Cartesian.ell, Fin.cases_zero, mul_one, smul_eq_mul]
  linarith [potential_nonnegative mass a x hm hr]

end BlackHole.KerrField
