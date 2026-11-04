module
public import BlackHole.Hamiltonian
public import BlackHole.ScreenGauge

@[expose] public section
noncomputable section
namespace BlackHole.RayConditioning

theorem tangent_rescale (inv : Matrix (Fin 4) (Fin 4) ℝ) (p : Fin 4 → ℝ) (c : ℝ) :
    inv.mulVec (c • p) = c • inv.mulVec p := by
  exact Matrix.mulVec_smul inv c p

theorem force_rescale (dg : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ)
    (k : Fin 4 → ℝ) (c : ℝ) (a : Fin 4) :
    Transport.momentumForce dg (c • k) a = c^2*Transport.momentumForce dg k a := by
  simp only [Transport.momentumForce,Pi.smul_apply,smul_eq_mul]
  rw [← mul_div_assoc]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem energy_ratio_rescale (p u : Fin 4 → ℝ) (c : ℝ) (hc : c ≠ 0) :
    dotProduct (c • p) u / (c • p) 0 = dotProduct p u / p 0 := by
  simp only [smul_dotProduct,Pi.smul_apply,smul_eq_mul]
  exact mul_div_mul_left _ _ hc

theorem affine_increment_rescale (h pt camera c : ℝ) (hc : c ≠ 0) :
    (c*h)*(pt/c)/camera = h*pt/camera := by
  field_simp

theorem fluid_distance_rescale (energy h c : ℝ) (hc : c ≠ 0) :
    (energy/c)*(c*h) = energy*h := by
  field_simp

def gaugeRate (k df : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => df i-k i*(df 0/k 0)

theorem gauge_rate_time_zero (k df : Fin 4 → ℝ) (hk : k 0 ≠ 0) :
    gaugeRate k df 0 = 0 := by
  unfold gaugeRate
  field_simp
  ring

theorem gauge_rate_bivector (k df : Fin 4 → ℝ) (i j : Fin 4) :
    k i*gaugeRate k df j-k j*gaugeRate k df i = k i*df j-k j*df i := by
  unfold gaugeRate
  ring

theorem foreground_composition (a b : Matrix (Fin 4) (Fin 4) ℝ)
    (sourceA sourceB incident : Fin 4 → ℝ) :
    a.mulVec (b.mulVec incident+sourceB)+sourceA =
      (a*b).mulVec incident+(a.mulVec sourceB+sourceA) := by
  rw [Matrix.mulVec_add,Matrix.mulVec_mulVec]
  exact add_assoc _ _ _

end BlackHole.RayConditioning
