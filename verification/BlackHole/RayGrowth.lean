module

public import BlackHole.KerrDerivativeBounds
public import BlackHole.KerrSmoothness
public import Mathlib.Analysis.ODE.Gronwall

@[expose] public section
noncomputable section
namespace BlackHole.KerrField

open Set

private theorem product_bound (a b A B : ℝ) (ha : |a| ≤ A) (hb : |b| ≤ B)
    (hA : 0 ≤ A) : |a*b| ≤ A*B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg b) hA

private theorem sum_bound (f : Fin 4 → ℝ) (B : ℝ) (hf : ∀ i, |f i| ≤ B) :
    |∑ i, f i| ≤ 4*B := by
  calc
    _ ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 4, B := Finset.sum_le_sum (fun i _ => hf i)
    _ = 4*B := by simp

/-- Explicit derivative bound for the inverse used by the Hamiltonian RHS. -/
theorem inverseD_component_bound (a x : Cartesian.Space) (ha : dotProduct a a ≤ 1)
    (hr : 1 ≤ Cartesian.radius a x) (e i j : Fin 4) :
    |Curvature.inverseD (metric 1 a x)⁻¹ (metricD 1 a x) e i j| ≤ 5184 := by
  unfold Curvature.inverseD
  rw [abs_neg]
  have hi := inverse_component_bound a x hr
  have hd := metricD_field_component_bound a x ha hr e
  have ht (b c : Fin 4) : |(metric 1 a x)⁻¹ i b*metricD 1 a x e b c*(metric 1 a x)⁻¹ c j| ≤ 324 := by
    have h := product_bound _ _ _ _ (product_bound _ _ _ _ (hi i b) (hd b c) (by norm_num)) (hi c j) (by norm_num)
    norm_num at h
    simpa only [abs_mul] using h
  have h := sum_bound _ (4*324) (fun b => sum_bound _ 324 (ht b))
  norm_num at h
  exact h

/-- The contracted connection is linear in the tangent, with an explicit bound. -/
theorem contracted_connection_bound (a x : Cartesian.Space) (k : Fin 4 → ℝ)
    (K : ℝ) (ha : dotProduct a a ≤ 1) (hr : 1 ≤ Cartesian.radius a x)
    (hk : ∀ j, |k j| ≤ K) (i c : Fin 4) :
    |Transport.contractedConnection (metric 1 a x)⁻¹ (metricD 1 a x) k i c| ≤ 2592*K := by
  have hK : 0 ≤ K := le_trans (abs_nonneg (k 0)) (hk 0)
  have hd := metricD_field_component_bound a x ha hr
  have hl (d b : Fin 4) : |Transport.loweredConnection (metricD 1 a x) d b c| ≤ 54 := by
    unfold Transport.loweredConnection
    rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ)<2)).2
    have h1 := abs_add_le (metricD 1 a x b d c) (metricD 1 a x c d b)
    have h2 := abs_add_le (metricD 1 a x b d c+metricD 1 a x c d b) (-metricD 1 a x d b c)
    simp only [abs_neg, ← sub_eq_add_neg] at h2
    linarith [hd b d c,hd c d b,hd d b c]
  have hb (d : Fin 4) : |∑ b, Transport.loweredConnection (metricD 1 a x) d b c*k b| ≤ 216*K := by
    have h := sum_bound _ (54*K) (fun b => product_bound _ _ _ _ (hl d b) (hk b) (by norm_num))
    nlinarith
  unfold Transport.contractedConnection
  simp only [Matrix.mulVec,dotProduct]
  have h := sum_bound _ (3*(216*K)) (fun d =>
    product_bound _ _ _ _ (inverse_component_bound a x hr i d) (hb d) (by norm_num))
  nlinarith

/-- Explicit growth bound for the actual parallel-screen component of phaseRhs. -/
theorem phase_rhs_screen_component_bound (a x : Cartesian.Space) (p screen : Fin 4 → ℝ)
    (P F : ℝ) (ha : dotProduct a a ≤ 1) (hr : 1 ≤ Cartesian.radius a x)
    (hp : ∀ j, |p j| ≤ P) (hf : ∀ j, |screen j| ≤ F) (i : Fin 4) :
    |(phaseRhs 1 a (x,p,screen)).2.2 i| ≤ 124416*P*F := by
  have hP : 0 ≤ P := le_trans (abs_nonneg (p 0)) (hp 0)
  let k := ((metric 1 a x)⁻¹).mulVec p
  have hk := hamiltonian_tangent_component_bound a x p P hr hp
  have hc (c : Fin 4) : |Transport.contractedConnection (metric 1 a x)⁻¹ (metricD 1 a x) k i c| ≤ 31104*P := by
    have h := contracted_connection_bound a x k (12*P) ha hr hk i c
    nlinarith
  change |-(∑ c, Transport.contractedConnection (metric 1 a x)⁻¹ (metricD 1 a x) k i c*screen c)| ≤ _
  rw [abs_neg]
  have h := sum_bound _ ((31104*P)*F) (fun c => product_bound _ _ _ _ (hc c) (hf c) (by positivity))
  nlinarith

/-- Explicit maximum-norm growth bound for the complete phase field, suitable
for checking clearance of all RK4 stages before taking a step. -/
theorem phase_rhs_norm_bound (a x : Cartesian.Space) (p screen : Fin 4 → ℝ)
    (P F : ℝ) (ha : dotProduct a a ≤ 1) (hr : 1 ≤ Cartesian.radius a x)
    (hp : ∀ j, |p j| ≤ P) (hf : ∀ j, |screen j| ≤ F) :
    ‖phaseRhs 1 a (x,p,screen)‖ ≤ max (12*P) (max (41472*P^2) (124416*P*F)) := by
  rw [Prod.norm_def, Prod.norm_def]
  apply max_le_max
  · apply (pi_norm_le_iff_of_nonempty _).mpr
    intro i
    exact hamiltonian_tangent_component_bound a x p P hr hp i.succ
  · apply max_le_max
    · apply (pi_norm_le_iff_of_nonempty _).mpr
      intro i
      exact momentum_force_component_bound a x p P ha hr hp i
    · apply (pi_norm_le_iff_of_nonempty _).mpr
      intro i
      exact phase_rhs_screen_component_bound a x p screen P F ha hr hp hf i

/-- Exact parallel-screen transport grows at most exponentially while the ray
stays in the normalized exterior and its momentum components stay bounded.
This supplies a finite screen bound on each finite solution interval. -/
theorem screen_growth_bound (a : Cartesian.Space) (curve : ℝ → Phase) (P t₀ T : ℝ)
    (ha : dotProduct a a ≤ 1)
    (hsol : ∀ t ∈ Icc t₀ T, HasDerivAt curve (phaseRhs 1 a (curve t)) t)
    (hr : ∀ t ∈ Icc t₀ T, 1 ≤ Cartesian.radius a (curve t).1)
    (hp : ∀ t ∈ Icc t₀ T, ∀ j, |(curve t).2.1 j| ≤ P) :
    ∀ t ∈ Icc t₀ T, ‖(curve t).2.2‖ ≤
      ‖(curve t₀).2.2‖*Real.exp ((124416*P)*(t-t₀)) := by
  let screen : Phase →L[ℝ] (Fin 4 → ℝ) :=
    (ContinuousLinearMap.snd ℝ (Fin 4 → ℝ) (Fin 4 → ℝ)).comp
      (ContinuousLinearMap.snd ℝ Cartesian.Space ((Fin 4 → ℝ) × (Fin 4 → ℝ)))
  have hs : ∀ t ∈ Icc t₀ T, HasDerivAt (fun u => (curve u).2.2)
      (phaseRhs 1 a (curve t)).2.2 t :=
    fun t ht => screen.hasFDerivAt.comp_hasDerivAt t (hsol t ht)
  have hc : ContinuousOn (fun t => (curve t).2.2) (Icc t₀ T) :=
    fun t ht => (hs t ht).continuousAt.continuousWithinAt
  have hd : ∀ t ∈ Ico t₀ T, HasDerivWithinAt (fun u => (curve u).2.2)
      (phaseRhs 1 a (curve t)).2.2 (Ici t) t :=
    fun t ht => (hs t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt
  have hb : ∀ t ∈ Ico t₀ T, ‖(phaseRhs 1 a (curve t)).2.2‖ ≤
      (124416*P)*‖(curve t).2.2‖+0 := by
    intro t ht
    rw [add_zero]
    apply (pi_norm_le_iff_of_nonempty _).mpr
    intro i
    have hf (j : Fin 4) : |(curve t).2.2 j| ≤ ‖(curve t).2.2‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (curve t).2.2 j
    exact phase_rhs_screen_component_bound a (curve t).1 (curve t).2.1 (curve t).2.2
      P ‖(curve t).2.2‖ ha (hr t ⟨ht.1, ht.2.le⟩) (hp t ⟨ht.1, ht.2.le⟩) hf i
  simpa only [gronwallBound_ε0] using
    norm_le_gronwallBound_of_norm_deriv_right_le hc hd le_rfl hb

end BlackHole.KerrField
