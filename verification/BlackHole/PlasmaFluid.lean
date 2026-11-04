module

public import BlackHole.KerrCamera

@[expose] public section
noncomputable section

namespace BlackHole.Plasma

/-- The shader normalizes a timelike circular candidate, otherwise using
    the Eulerian observer. The spatial velocity may be arbitrary. -/
def fluidVelocity (g inv : Matrix (Fin 4) (Fin 4) ℝ) (space : Cartesian.Space) : Fin 4 → ℝ :=
  let candidate : Fin 4 → ℝ := Fin.cases 1 space
  if dotProduct candidate (g.mulVec candidate) < -(1/10000) then
    (1/Real.sqrt (-dotProduct candidate (g.mulVec candidate))) • candidate
  else ADM.observer inv

theorem fluidVelocity_unit_future (g inv : Matrix (Fin 4) (Fin 4) ℝ)
    (space : Cartesian.Space) (hinv : g*inv = 1) (h00 : inv 0 0 < 0) :
    dotProduct (fluidVelocity g inv space) (g.mulVec (fluidVelocity g inv space)) = -1 ∧
      0 < fluidVelocity g inv space 0 := by
  dsimp only [fluidVelocity]
  split_ifs with hcandidate
  · have hc : dotProduct (Fin.cases 1 space) (g.mulVec (Fin.cases 1 space)) < 0 := by linarith
    have hsq := Real.sq_sqrt (le_of_lt (neg_pos.mpr hc))
    have hn := ne_of_gt (Real.sqrt_pos.mpr (neg_pos.mpr hc))
    constructor
    · simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      field_simp
      nlinarith
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.cases_zero, mul_one]
      exact one_div_pos.mpr (Real.sqrt_pos.mpr (neg_pos.mpr hc))
  · exact ⟨ADM.observer_unit_timelike g inv hinv h00, ADM.observer_future inv h00⟩

end BlackHole.Plasma

namespace BlackHole.Frames

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem past_null_fluid_energy_positive (gamma : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsym : ∀ v w, gamma v w = gamma w v) (hpositive : ∀ v, 0 ≤ gamma v v)
    (alpha rayTime fluidTime : ℝ) (beta raySpace fluidSpace : V)
    (ha : 0 < alpha) (hk : rayTime < 0) (hu : 0 < fluidTime)
    (hnull : admNorm gamma alpha rayTime beta raySpace = 0)
    (hfluid : admNorm gamma alpha fluidTime beta fluidSpace = -1) :
    0 < -(alpha^2*rayTime*fluidTime)+
      gamma (raySpace+rayTime • beta) (fluidSpace+fluidTime • beta) := by
  let A := -(alpha*rayTime)
  let K := raySpace+rayTime • beta
  let n := (1/A) • K
  have hA : 0 < A := neg_pos.mpr (mul_neg_of_pos_of_neg ha hk)
  have hA0 := ne_of_gt hA
  have hnK : gamma K K = A^2 := by
    change -(alpha^2*rayTime^2)+gamma K K = 0 at hnull
    dsimp only [A]
    nlinarith
  have hn : gamma n n = 1 := by
    simp only [n, map_smul, LinearMap.smul_apply, smul_eq_mul, hnK]
    field_simp
  have hp := mul_pos hA
    (fluid_photon_energy_positive gamma hsym hpositive alpha fluidTime beta fluidSpace n ha hu hn hfluid)
  have heq : -(alpha^2*rayTime*fluidTime)+gamma K (fluidSpace+fluidTime • beta) =
      A*(alpha*fluidTime+gamma n (fluidSpace+fluidTime • beta)) := by
    simp only [n, map_smul, LinearMap.smul_apply, smul_eq_mul]
    field_simp
    dsimp only [A]
    ring
  rw [heq]
  exact hp

end BlackHole.Frames

namespace BlackHole.KerrField

theorem plasma_fluid_unit_future (mass : ℝ) (a x space : Cartesian.Space)
    (hm : 0 ≤ mass) (hr : 0 < Cartesian.radius a x) :
    let g := metric mass a x
    let fluid := Plasma.fluidVelocity g g⁻¹ space
    dotProduct fluid (g.mulVec fluid) = -1 ∧ 0 < fluid 0 := by
  exact Plasma.fluidVelocity_unit_future _ _ space
    (Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (metric_nonsingular mass a x hr)))
    (inverse_time_negative mass a x hm hr)

end BlackHole.KerrField
