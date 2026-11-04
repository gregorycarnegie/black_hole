module

public import BlackHole.SpatialNormalization
public import Mathlib.LinearAlgebra.CrossProduct

@[expose] public section
noncomputable section

namespace BlackHole.Frames

def rankSpatial (coefficient : ℝ) (l v : Cartesian.Space) : Cartesian.Space :=
  v+(coefficient*dotProduct l v) • l

theorem rankSpatial_selfAdjoint (coefficient : ℝ) (l n v : Cartesian.Space) :
    dotProduct n (rankSpatial coefficient l v) = dotProduct (rankSpatial coefficient l n) v := by
  simp only [rankSpatial, dotProduct_add, dotProduct_smul, add_dotProduct, smul_dotProduct,
    smul_eq_mul]
  rw [dotProduct_comm n l]
  ring

def rankScreenCross (coefficient : ℝ) (l n e : Cartesian.Space) : Cartesian.Space :=
  crossProduct (rankSpatial coefficient l n) (rankSpatial coefficient l e)

theorem rankScreenCross_orthogonal (coefficient : ℝ) (l n e : Cartesian.Space) :
    let v := rankScreenCross coefficient l n e
    dotProduct n (rankSpatial coefficient l v) = 0 ∧
      dotProduct e (rankSpatial coefficient l v) = 0 := by
  dsimp only
  constructor
  · rw [rankSpatial_selfAdjoint]
    exact dot_self_cross _ _
  · rw [rankSpatial_selfAdjoint]
    exact dot_cross_self _ _

set_option maxHeartbeats 2000000 in
theorem rankScreenCross_norm (coefficient : ℝ) (l n e : Cartesian.Space) :
    let g := rankSpatial coefficient l
    let v := rankScreenCross coefficient l n e
    dotProduct v (g v) = (1+coefficient*dotProduct l l)*
      (dotProduct n (g n)*dotProduct e (g e)-(dotProduct n (g e))^2) := by
  simp [rankScreenCross, rankSpatial, dotProduct, Fin.sum_univ_succ, cross_apply]
  ring

theorem rankScreenCross_norm_ge_one (coefficient : ℝ) (l n e : Cartesian.Space)
    (hc : 0 ≤ coefficient)
    (hn : dotProduct n (rankSpatial coefficient l n) = 1)
    (he : dotProduct e (rankSpatial coefficient l e) = 1)
    (hne : dotProduct n (rankSpatial coefficient l e) = 0) :
    1 ≤ dotProduct (rankScreenCross coefficient l n e)
      (rankSpatial coefficient l (rankScreenCross coefficient l n e)) := by
  rw [rankScreenCross_norm, hn, he, hne]
  have hl : 0 ≤ dotProduct l l := Finset.sum_nonneg (fun i _ => mul_self_nonneg (l i))
  nlinarith [mul_nonneg hc hl]

end BlackHole.Frames

namespace BlackHole.ADM

theorem spatial_smul_left (g : Matrix (Fin 4) (Fin 4) ℝ) (a : ℝ) (v w : Fin 3 → ℝ) :
    spatial g (a • v) w = a*spatial g v w := by
  simp only [spatial, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem spatial_smul_right (g : Matrix (Fin 4) (Fin 4) ℝ) (a : ℝ) (v w : Fin 3 → ℝ) :
    spatial g v (a • w) = a*spatial g v w := by
  simp only [spatial, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end BlackHole.ADM

namespace BlackHole.KerrField

def spatialMatrix (mass : ℝ) (a x : Cartesian.Space) : Matrix (Fin 3) (Fin 3) ℝ :=
  (metric mass a x).submatrix Fin.succ Fin.succ

theorem spatialMatrix_action (mass : ℝ) (a x v : Cartesian.Space) :
    (spatialMatrix mass a x).mulVec v =
      Frames.rankSpatial (2*Cartesian.potential mass a x) (Cartesian.spatialEll a x) v := by
  ext i
  simp only [spatialMatrix, Matrix.mulVec, dotProduct, Matrix.submatrix_apply,
    metric, Matrix.of_apply, Cartesian.metric, Cartesian.ell, Fin.cases_succ]
  fin_cases i <;> simp [Cartesian.eta, Frames.rankSpatial, dotProduct, Fin.sum_univ_succ]
  all_goals ring

theorem spatialMatrix_pairing (mass : ℝ) (a x v w : Cartesian.Space) :
    dotProduct v ((spatialMatrix mass a x).mulVec w) = ADM.spatial (metric mass a x) v w := by
  simp [spatialMatrix, Matrix.mulVec, dotProduct, ADM.spatial, Fin.sum_univ_succ]
  ring

/-- The source's metric-weighted cross product has squared spatial norm at
    least one for an orthonormal direction and first screen vector. -/
theorem second_screen_norm_ge_one (mass : ℝ) (a x n e : Cartesian.Space)
    (hm : 0 ≤ mass) (hr : 0 < Cartesian.radius a x)
    (hn : ADM.spatial (metric mass a x) n n = 1)
    (he : ADM.spatial (metric mass a x) e e = 1)
    (hne : ADM.spatial (metric mass a x) n e = 0) :
    let gamma := spatialMatrix mass a x
    let v := crossProduct (gamma.mulVec n) (gamma.mulVec e)
    1 ≤ ADM.spatial (metric mass a x) v v := by
  simp only [← spatialMatrix_pairing] at hn he hne ⊢
  simp only [spatialMatrix_action] at hn he hne ⊢
  exact Frames.rankScreenCross_norm_ge_one _ _ _ _
    (mul_nonneg (by norm_num) (potential_nonnegative mass a x hm hr)) hn he hne

theorem second_screen_orthogonal (mass : ℝ) (a x n e : Cartesian.Space) :
    let gamma := spatialMatrix mass a x
    let v := crossProduct (gamma.mulVec n) (gamma.mulVec e)
    ADM.spatial (metric mass a x) n v = 0 ∧ ADM.spatial (metric mass a x) e v = 0 := by
  simp only [← spatialMatrix_pairing, spatialMatrix_action]
  exact Frames.rankScreenCross_orthogonal _ _ _ _

def secondScreen (mass : ℝ) (a x n e : Cartesian.Space) : Cartesian.Space :=
  let gamma := spatialMatrix mass a x
  let v := crossProduct (gamma.mulVec n) (gamma.mulVec e)
  (1/Real.sqrt (max (ADM.spatial (metric mass a x) v v) Frames.spatialFloor)) • v

/-- The normalization and floor in the production second-screen construction
    preserve its unit norm and both orthogonalities for orthonormal inputs. -/
theorem second_screen_orthonormal (mass : ℝ) (a x n e : Cartesian.Space)
    (hm : 0 ≤ mass) (hr : 0 < Cartesian.radius a x)
    (hn : ADM.spatial (metric mass a x) n n = 1)
    (he : ADM.spatial (metric mass a x) e e = 1)
    (hne : ADM.spatial (metric mass a x) n e = 0) :
    let g := metric mass a x
    let e2 := secondScreen mass a x n e
    ADM.spatial g n e2 = 0 ∧ ADM.spatial g e e2 = 0 ∧ ADM.spatial g e2 e2 = 1 := by
  let g := metric mass a x
  let gamma := spatialMatrix mass a x
  let v := crossProduct (gamma.mulVec n) (gamma.mulVec e)
  have hv : 1 ≤ ADM.spatial g v v := second_screen_norm_ge_one mass a x n e hm hr hn he hne
  have hp : 0 < ADM.spatial g v v := by linarith
  have hmax : max (ADM.spatial g v v) Frames.spatialFloor = ADM.spatial g v v :=
    max_eq_left (le_trans Frames.spatialFloor_bounds.2 hv)
  have ho : ADM.spatial g n v = 0 ∧ ADM.spatial g e v = 0 :=
    second_screen_orthogonal mass a x n e
  change ADM.spatial g n ((1/Real.sqrt (max (ADM.spatial g v v) Frames.spatialFloor)) • v) = 0 ∧
    ADM.spatial g e ((1/Real.sqrt (max (ADM.spatial g v v) Frames.spatialFloor)) • v) = 0 ∧
    ADM.spatial g ((1/Real.sqrt (max (ADM.spatial g v v) Frames.spatialFloor)) • v)
      ((1/Real.sqrt (max (ADM.spatial g v v) Frames.spatialFloor)) • v) = 1
  simp only [hmax]
  refine ⟨?_, ?_, ?_⟩
  · rw [ADM.spatial_smul_right, ho.1, mul_zero]
  · rw [ADM.spatial_smul_right, ho.2, mul_zero]
  · rw [ADM.spatial_smul_left, ADM.spatial_smul_right]
    have hs := Real.sq_sqrt (le_of_lt hp)
    have hs0 := ne_of_gt (Real.sqrt_pos.mpr hp)
    field_simp
    nlinarith

end BlackHole.KerrField
