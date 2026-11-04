module

public import BlackHole.ScreenFrame
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

@[expose] public section
noncomputable section

namespace BlackHole.Frames

theorem unit_component_norm_bound (v e : Cartesian.Space)
    (he : dotProduct e e = 1) (hev : dotProduct e v = 1) : 1 ≤ dotProduct v v := by
  have hp : 0 ≤ dotProduct (v-e) (v-e) :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg ((v-e) i))
  simp only [sub_dotProduct, dotProduct_sub] at hp
  rw [dotProduct_comm v e, hev, he] at hp
  linarith

/-- Gram–Schmidt of a Euclidean orthonormal camera basis is nondegenerate
    in any symmetric spatial metric that dominates the Euclidean metric. -/
theorem camera_gram_schmidt (g : Cartesian.Space →ₗ[ℝ] Cartesian.Space →ₗ[ℝ] ℝ)
    (hsym : ∀ v w, g v w = g w v) (hdom : ∀ v, dotProduct v v ≤ g v v)
    (f r u : Cartesian.Space)
    (hff : dotProduct f f = 1) (hrr : dotProduct r r = 1) (huu : dotProduct u u = 1)
    (hfr : dotProduct f r = 0) (hfu : dotProduct f u = 0) (hru : dotProduct r u = 0) :
    let F := spatialUnit g f
    let R0 := r-(g F r) • F
    let R := spatialUnit g R0
    let U0 := u-(g F u) • F-(g R u) • R
    let U := spatialUnit g U0
    1 ≤ g f f ∧ 1 ≤ g R0 R0 ∧ 1 ≤ g U0 U0 ∧
      g F F = 1 ∧ g R R = 1 ∧ g U U = 1 ∧ g F R = 0 ∧ g F U = 0 ∧ g R U = 0 := by
  let F := spatialUnit g f
  let R0 := r-(g F r) • F
  let R := spatialUnit g R0
  let U0 := u-(g F u) • F-(g R u) • R
  let U := spatialUnit g U0
  have hf : 1 ≤ g f f := by simpa only [hff] using hdom f
  have hF : g F F = 1 := spatialUnit_unit g f (by linarith)
  have hrF : dotProduct r F = 0 := by
    simp only [F, spatialUnit, dotProduct_smul]
    rw [dotProduct_comm r f, hfr, smul_zero]
  have hrR0 : dotProduct r R0 = 1 := by
    simp [R0, dotProduct_sub, dotProduct_smul, hrF, hrr]
  have hR0 : 1 ≤ g R0 R0 := le_trans (unit_component_norm_bound R0 r hrr hrR0) (hdom R0)
  have hR : g R R = 1 := spatialUnit_unit g R0 (by linarith)
  have hFR : g F R = 0 := normalization_preserves_orthogonality g F R0
    (projection_orthogonal g F r hF)
  have hRF : g R F = 0 := by rw [hsym]; exact hFR
  have huF : dotProduct u F = 0 := by
    simp only [F, spatialUnit, dotProduct_smul]
    rw [dotProduct_comm u f, hfu, smul_zero]
  have huR : dotProduct u R = 0 := by
    simp only [R, spatialUnit, dotProduct_smul]
    simp [R0, dotProduct_sub, dotProduct_smul, huF, dotProduct_comm u r, hru]
  have huU0 : dotProduct u U0 = 1 := by
    simp [U0, dotProduct_sub, dotProduct_smul, huF, huR, huu]
  have hU0 : 1 ≤ g U0 U0 := le_trans (unit_component_norm_bound U0 u huu huU0) (hdom U0)
  have hU : g U U = 1 := spatialUnit_unit g U0 (by linarith)
  have ho := two_projections_orthogonal g F R u hF hR hFR hRF
  have hFU : g F U = 0 := normalization_preserves_orthogonality g F U0 ho.1
  have hRU : g R U = 0 := normalization_preserves_orthogonality g R U0 ho.2
  exact ⟨hf,hR0,hU0,hF,hR,hU,hFR,hFU,hRU⟩

theorem camera_gram_schmidt_scaled (g : Cartesian.Space →ₗ[ℝ] Cartesian.Space →ₗ[ℝ] ℝ)
    (hsym : ∀ v w, g v w = g w v) (hdom : ∀ v, dotProduct v v ≤ g v v)
    (f r u : Cartesian.Space)
    (hff : dotProduct f f = 1) (hrr : dotProduct r r = 1) (huu : dotProduct u u = 1)
    (hfr : dotProduct f r = 0) (hfu : dotProduct f u = 0) (hru : dotProduct r u = 0) :
    let F := spatialUnitScaled g f
    let R := spatialUnitScaled g (r-(g F r) • F)
    let U := spatialUnitScaled g (u-(g F u) • F-(g R u) • R)
    g F F = 1 ∧ g R R = 1 ∧ g U U = 1 ∧ g F R = 0 ∧ g F U = 0 ∧ g R U = 0 := by
  let F := spatialUnit g f
  let R0 := r-(g F r) • F
  let R := spatialUnit g R0
  let U0 := u-(g F u) • F-(g R u) • R
  let U := spatialUnit g U0
  obtain ⟨hf,hR0,hU0,hF,hR,hU,hFR,hFU,hRU⟩ :=
    camera_gram_schmidt g hsym hdom f r u hff hrr huu hfr hfu hru
  have hne (v : Cartesian.Space) (hv : 1 ≤ g v v) : v ≠ 0 := by
    intro hz
    simp [hz] at hv
    linarith
  have heF : spatialUnitScaled g f = F := spatialUnitScaled_eq g hdom f (hne f hf)
  have heR : spatialUnitScaled g R0 = R := spatialUnitScaled_eq g hdom R0 (hne R0 hR0)
  have heU : spatialUnitScaled g U0 = U := spatialUnitScaled_eq g hdom U0 (hne U0 hU0)
  dsimp only
  rw [heF, heR, heU]
  exact ⟨hF,hR,hU,hFR,hFU,hRU⟩

end BlackHole.Frames

namespace BlackHole.KerrField

def spatialBilinear (mass : ℝ) (a x : Cartesian.Space) :
    Cartesian.Space →ₗ[ℝ] Cartesian.Space →ₗ[ℝ] ℝ :=
  Matrix.toBilin' (spatialMatrix mass a x)

theorem spatialBilinear_apply (mass : ℝ) (a x v w : Cartesian.Space) :
    spatialBilinear mass a x v w = ADM.spatial (metric mass a x) v w := by
  simp only [spatialBilinear, Matrix.toBilin'_apply', spatialMatrix_pairing]

theorem spatialBilinear_symmetric (mass : ℝ) (a x v w : Cartesian.Space) :
    spatialBilinear mass a x v w = spatialBilinear mass a x w v := by
  simp only [spatialBilinear_apply, ← spatialMatrix_pairing, spatialMatrix_action]
  exact (Frames.rankSpatial_selfAdjoint _ _ v w).trans (dotProduct_comm _ _)

theorem spatialBilinear_dominates_euclidean (mass : ℝ) (a x : Cartesian.Space)
    (hm : 0 ≤ mass) (hr : 0 < Cartesian.radius a x) (v : Cartesian.Space) :
    dotProduct v v ≤ spatialBilinear mass a x v v := by
  rw [spatialBilinear_apply, spatial_metric_form]
  have hH := potential_nonnegative mass a x hm hr
  nlinarith [sq_nonneg (dotProduct (Cartesian.spatialEll a x) v)]

/-- Actual Kerr camera Gram–Schmidt inputs have squared norm at least one;
    all three normalized axes are orthonormal. -/
theorem camera_gram_schmidt_defined (mass : ℝ) (a x f r u : Cartesian.Space)
    (hm : 0 ≤ mass) (hr : 0 < Cartesian.radius a x)
    (hff : dotProduct f f = 1) (hrr : dotProduct r r = 1) (huu : dotProduct u u = 1)
    (hfr : dotProduct f r = 0) (hfu : dotProduct f u = 0) (hru : dotProduct r u = 0) :
    let g := spatialBilinear mass a x
    let F := Frames.spatialUnit g f
    let R0 := r-(g F r) • F
    let R := Frames.spatialUnit g R0
    let U0 := u-(g F u) • F-(g R u) • R
    let U := Frames.spatialUnit g U0
    1 ≤ g f f ∧ 1 ≤ g R0 R0 ∧ 1 ≤ g U0 U0 ∧
      g F F = 1 ∧ g R R = 1 ∧ g U U = 1 ∧ g F R = 0 ∧ g F U = 0 ∧ g R U = 0 := by
  exact Frames.camera_gram_schmidt _ (spatialBilinear_symmetric mass a x)
    (spatialBilinear_dominates_euclidean mass a x hm hr) f r u hff hrr huu hfr hfu hru

theorem spatial_unit_scaled_correct (mass : ℝ) (a x v : Cartesian.Space)
    (hm : 0 ≤ mass) (hr : 0 < Cartesian.radius a x) (hv : v ≠ 0) :
    let g := spatialBilinear mass a x
    Frames.spatialUnitScaled g v = Frames.spatialUnit g v ∧
      ADM.spatial (metric mass a x) (Frames.spatialUnitScaled g v) (Frames.spatialUnitScaled g v) = 1 := by
  refine ⟨Frames.spatialUnitScaled_eq _ (spatialBilinear_dominates_euclidean mass a x hm hr) v hv, ?_⟩
  rw [← spatialBilinear_apply]
  exact Frames.spatialUnitScaled_unit _ (spatialBilinear_dominates_euclidean mass a x hm hr) v hv

theorem second_screen_scaled_eq (mass : ℝ) (a x n e : Cartesian.Space)
    (hm : 0 ≤ mass) (hr : 0 < Cartesian.radius a x)
    (hn : ADM.spatial (metric mass a x) n n = 1)
    (he : ADM.spatial (metric mass a x) e e = 1)
    (hne : ADM.spatial (metric mass a x) n e = 0) :
    let gamma := spatialMatrix mass a x
    let v := crossProduct (gamma.mulVec n) (gamma.mulVec e)
    Frames.spatialUnitScaled (spatialBilinear mass a x) v = secondScreen mass a x n e := by
  let v := crossProduct ((spatialMatrix mass a x).mulVec n) ((spatialMatrix mass a x).mulVec e)
  have hv : 1 ≤ ADM.spatial (metric mass a x) v v :=
    second_screen_norm_ge_one mass a x n e hm hr hn he hne
  have hv0 : v ≠ 0 := by
    intro hz
    simp [hz, ADM.spatial] at hv
    linarith
  change Frames.spatialUnitScaled (spatialBilinear mass a x) v = secondScreen mass a x n e
  rw [Frames.spatialUnitScaled_eq _ (spatialBilinear_dominates_euclidean mass a x hm hr) v hv0]
  dsimp only [Frames.spatialUnit, secondScreen]
  rw [spatialBilinear_apply, max_eq_left (le_trans Frames.spatialFloor_bounds.2 hv)]

end BlackHole.KerrField
