module

public import BlackHole.KerrCamera

@[expose] public section
noncomputable section

namespace BlackHole.Frames

def spatialFloor : ℝ := 1/(10 : ℝ)^(20 : ℕ)

theorem spatialFloor_bounds : 0 < spatialFloor ∧ spatialFloor ≤ 1 := by
  norm_num [spatialFloor]

def maxAbs (v : Cartesian.Space) : ℝ := max (max |v 0| |v 1|) |v 2|

theorem maxAbs_pos (v : Cartesian.Space) (hv : v ≠ 0) : 0 < maxAbs v := by
  have h0 : |v 0| ≤ maxAbs v := le_trans (le_max_left _ _) (le_max_left _ _)
  have h1 : |v 1| ≤ maxAbs v := le_trans (le_max_right _ _) (le_max_left _ _)
  have h2 : |v 2| ≤ maxAbs v := le_max_right _ _
  by_contra hnot
  have hs : maxAbs v ≤ 0 := le_of_not_gt hnot
  apply hv
  ext i
  fin_cases i
  · exact abs_eq_zero.mp (le_antisymm (le_trans h0 hs) (abs_nonneg _))
  · exact abs_eq_zero.mp (le_antisymm (le_trans h1 hs) (abs_nonneg _))
  · exact abs_eq_zero.mp (le_antisymm (le_trans h2 hs) (abs_nonneg _))

theorem maxAbs_sq_le (v : Cartesian.Space) : (maxAbs v)^2 ≤ dotProduct v v := by
  unfold maxAbs
  by_cases h01 : |v 0| ≤ |v 1|
  · rw [max_eq_right h01]
    by_cases h12 : |v 1| ≤ |v 2|
    · rw [max_eq_right h12, sq_abs]
      simp [dotProduct, Fin.sum_univ_succ]
      nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    · rw [max_eq_left (lt_of_not_ge h12).le, sq_abs]
      simp [dotProduct, Fin.sum_univ_succ]
      nlinarith [sq_nonneg (v 0), sq_nonneg (v 2)]
  · rw [max_eq_left (lt_of_not_ge h01).le]
    by_cases h02 : |v 0| ≤ |v 2|
    · rw [max_eq_right h02, sq_abs]
      simp [dotProduct, Fin.sum_univ_succ]
      nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    · rw [max_eq_left (lt_of_not_ge h02).le, sq_abs]
      simp [dotProduct, Fin.sum_univ_succ]
      nlinarith [sq_nonneg (v 1), sq_nonneg (v 2)]

theorem spatialUnit_rescale (g : Cartesian.Space →ₗ[ℝ] Cartesian.Space →ₗ[ℝ] ℝ)
    (v : Cartesian.Space) (a : ℝ) (ha : 0 < a) (hv : 0 < g v v) :
    spatialUnit g (a • v) = spatialUnit g v := by
  have hnorm : g (a • v) (a • v) = a^2*g v v := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have ha0 := ne_of_gt ha
  have hs0 := ne_of_gt (Real.sqrt_pos.mpr hv)
  unfold spatialUnit
  rw [hnorm, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs, abs_of_pos ha, smul_smul]
  congr 1
  field_simp

def spatialUnitScaled (g : Cartesian.Space →ₗ[ℝ] Cartesian.Space →ₗ[ℝ] ℝ)
    (v : Cartesian.Space) : Cartesian.Space :=
  let scale := maxAbs v
  if scale = 0 then v else
    let w := (1/scale) • v
    (1/Real.sqrt (max (g w w) spatialFloor)) • w

theorem spatialUnitScaled_zero (g : Cartesian.Space →ₗ[ℝ] Cartesian.Space →ₗ[ℝ] ℝ) :
    spatialUnitScaled g 0 = 0 := by
  simp [spatialUnitScaled, maxAbs]

theorem scaled_input_norm_bound (g : Cartesian.Space →ₗ[ℝ] Cartesian.Space →ₗ[ℝ] ℝ)
    (hdom : ∀ v, dotProduct v v ≤ g v v) (v : Cartesian.Space) (hv : v ≠ 0) :
    1 ≤ g ((1/maxAbs v) • v) ((1/maxAbs v) • v) := by
  have hs := maxAbs_pos v hv
  have hs0 := ne_of_gt hs
  have hid : g ((1/maxAbs v) • v) ((1/maxAbs v) • v) = g v v/(maxAbs v)^2 := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    field_simp
  rw [hid]
  exact (le_div_iff₀ (sq_pos_of_pos hs)).2 (by
    simpa only [one_mul] using le_trans (maxAbs_sq_le v) (hdom v))

/-- Rescaling makes the shader's floor inactive for every nonzero input in
    a metric that dominates the Euclidean metric. -/
theorem spatialUnitScaled_eq (g : Cartesian.Space →ₗ[ℝ] Cartesian.Space →ₗ[ℝ] ℝ)
    (hdom : ∀ v, dotProduct v v ≤ g v v) (v : Cartesian.Space) (hv : v ≠ 0) :
    spatialUnitScaled g v = spatialUnit g v := by
  have hs := maxAbs_pos v hv
  have hs0 := ne_of_gt hs
  have hw := scaled_input_norm_bound g hdom v hv
  have hfloor : spatialFloor ≤ g ((1/maxAbs v) • v) ((1/maxAbs v) • v) :=
    le_trans spatialFloor_bounds.2 hw
  have hpos : 0 < g v v := lt_of_lt_of_le (sq_pos_of_pos hs)
    (le_trans (maxAbs_sq_le v) (hdom v))
  simp only [spatialUnitScaled, hs0]
  rw [normalization_floor_inactive g _ _ hfloor]
  exact spatialUnit_rescale g v _ (one_div_pos.mpr hs) hpos

theorem spatialUnitScaled_unit (g : Cartesian.Space →ₗ[ℝ] Cartesian.Space →ₗ[ℝ] ℝ)
    (hdom : ∀ v, dotProduct v v ≤ g v v) (v : Cartesian.Space) (hv : v ≠ 0) :
    g (spatialUnitScaled g v) (spatialUnitScaled g v) = 1 := by
  rw [spatialUnitScaled_eq g hdom v hv]
  have hs := maxAbs_pos v hv
  exact spatialUnit_unit g v (lt_of_lt_of_le (sq_pos_of_pos hs)
    (le_trans (maxAbs_sq_le v) (hdom v)))

theorem spatialUnitScaled_orthogonal (g : Cartesian.Space →ₗ[ℝ] Cartesian.Space →ₗ[ℝ] ℝ)
    (hdom : ∀ v, dotProduct v v ≤ g v v) (u v : Cartesian.Space) (hv : v ≠ 0)
    (huv : g u v = 0) : g u (spatialUnitScaled g v) = 0 := by
  rw [spatialUnitScaled_eq g hdom v hv]
  exact normalization_preserves_orthogonality g u v huv

end BlackHole.Frames
