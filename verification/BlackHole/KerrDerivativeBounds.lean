module

public import BlackHole.KerrBounds
public import BlackHole.KerrOptical
public import BlackHole.Hamiltonian
import Mathlib.Tactic.GCongr

@[expose] public section
noncomputable section
namespace BlackHole.KerrField

private theorem abs_sub_bound (a b : Real) : |a-b| <= |a|+|b| := by
  simpa only [sub_eq_add_neg,abs_neg] using abs_add_le a (-b)

private theorem component_abs_le_one (v : Cartesian.Space) (hv : dotProduct v v ≤ 1)
    (i : Fin 3) : |v i| ≤ 1 := by
  have hi : (v i)^2 ≤ dotProduct v v := by
    simpa only [dotProduct, ← pow_two] using
      (Finset.single_le_sum (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ i))
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

theorem radiusD_abs_le_two (a x : Cartesian.Space) (ha : dotProduct a a ≤ 1)
    (hr : 1 ≤ Cartesian.radius a x) (e : Fin 3) : |Cartesian.radiusD a x e| ≤ 2 := by
  have hr0 : 0 < Cartesian.radius a x := by linarith
  have h := Cartesian.radius_gradient_bound a x hr0 (by nlinarith)
  have hi : (Cartesian.radiusD a x e)^2 ≤ dotProduct (Cartesian.radiusD a x) (Cartesian.radiusD a x) := by
    simpa only [dotProduct, ← pow_two] using
      (Finset.single_le_sum (fun j _ => mul_self_nonneg (Cartesian.radiusD a x j)) (Finset.mem_univ e))
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

theorem cosine_abs_le_one (a x : Cartesian.Space) (ha : dotProduct a a ≤ 1)
    (hr : 1 ≤ Cartesian.radius a x) : |Cartesian.cosine a x| ≤ 1 := by
  have h := Cartesian.cosine_bound a x (show 0 < Cartesian.radius a x by linarith)
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

theorem cosineD_abs_le_three (a x : Cartesian.Space) (ha : dotProduct a a ≤ 1)
    (hr : 1 ≤ Cartesian.radius a x) (e : Fin 3) : |Cartesian.cosineD a x e| ≤ 3 := by
  rw [Cartesian.cosineD, abs_div, abs_of_pos (show 0 < Cartesian.radius a x by linarith)]
  apply (div_le_iff₀ (show 0 < Cartesian.radius a x by linarith)).2
  have hc := cosine_abs_le_one a x ha hr
  have hd := radiusD_abs_le_two a x ha hr e
  have hp : |Cartesian.cosine a x*Cartesian.radiusD a x e| ≤ 2 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (Cartesian.cosine a x), abs_nonneg (Cartesian.radiusD a x e)]
  have h := abs_sub_bound (a e) (Cartesian.cosine a x*Cartesian.radiusD a x e)
  have he := component_abs_le_one a ha e
  linarith

private theorem basis_abs_le_one (e i : Fin 3) : |Cartesian.basis e i| ≤ 1 := by
  unfold Cartesian.basis
  split_ifs <;> norm_num

private theorem cross_basis_abs_le_two (v : Cartesian.Space) (hv : ∀ i, |v i| ≤ 1)
    (e i : Fin 3) : |crossProduct v (Cartesian.basis e) i| ≤ 2 := by
  have hb := basis_abs_le_one e
  have hprod (j k : Fin 3) : |v j*Cartesian.basis e k| ≤ 1 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (v j), abs_nonneg (Cartesian.basis e k), hv j, hb k]
  fin_cases i <;> simp [cross_apply] <;>
    linarith [abs_sub_bound (v 1*Cartesian.basis e 2) (v 2*Cartesian.basis e 1),
      abs_sub_bound (v 2*Cartesian.basis e 0) (v 0*Cartesian.basis e 2),
      abs_sub_bound (v 0*Cartesian.basis e 1) (v 1*Cartesian.basis e 0),
      hprod 1 2, hprod 2 1, hprod 2 0, hprod 0 2, hprod 0 1, hprod 1 0]

theorem spatialEllD_abs_le_four (a x : Cartesian.Space) (ha : dotProduct a a ≤ 1)
    (hr : 1 ≤ Cartesian.radius a x) (e i : Fin 3) : |Cartesian.spatialEllD a x e i| ≤ 4 := by
  have hr0 : 0 < Cartesian.radius a x := by linarith
  have hl (j : Fin 3) : |Cartesian.spatialEll a x j| ≤ 1 :=
    ell_component_abs_le_one a x hr0 j.succ
  have hp : |Cartesian.spatialEll a x i*Cartesian.spatialEll a x e| ≤ 1 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (Cartesian.spatialEll a x i), abs_nonneg (Cartesian.spatialEll a x e), hl i, hl e]
  have hfirst : |Cartesian.basis e i-Cartesian.spatialEll a x i*Cartesian.spatialEll a x e| ≤ 2 := by
    linarith [abs_sub_bound (Cartesian.basis e i) (Cartesian.spatialEll a x i*Cartesian.spatialEll a x e), basis_abs_le_one e i]
  have hc := cosine_abs_le_one a x ha hr
  have hcross := cross_basis_abs_le_two (Cartesian.spatialEll a x) hl e i
  have hsecond : |Cartesian.cosine a x*crossProduct (Cartesian.spatialEll a x) (Cartesian.basis e) i| ≤ 2 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (Cartesian.cosine a x), abs_nonneg (crossProduct (Cartesian.spatialEll a x) (Cartesian.basis e) i)]
  rw [Cartesian.spatialEllD_optical a x hr0, abs_div, abs_of_pos (Cartesian.sigma_positive a x hr0)]
  apply (div_le_iff₀ (Cartesian.sigma_positive a x hr0)).2
  have hterm : |Cartesian.radius a x*(Cartesian.basis e i-Cartesian.spatialEll a x i*Cartesian.spatialEll a x e)| ≤ 2*Cartesian.radius a x := by
    rw [abs_mul, abs_of_pos hr0]
    nlinarith
  have h := abs_sub_bound
    (Cartesian.radius a x*(Cartesian.basis e i-Cartesian.spatialEll a x i*Cartesian.spatialEll a x e))
    (Cartesian.cosine a x*crossProduct (Cartesian.spatialEll a x) (Cartesian.basis e) i)
  unfold Cartesian.sigma
  nlinarith [sq_nonneg (Cartesian.cosine a x)]

theorem potentialD_optical (a x : Cartesian.Space) (hr : 0 < Cartesian.radius a x) (e : Fin 3) :
    Cartesian.potentialD 1 a x e =
      ((Cartesian.cosine a x^2-Cartesian.radius a x^2)*Cartesian.radiusD a x e-
        2*Cartesian.radius a x*Cartesian.cosine a x*Cartesian.cosineD a x e)/Cartesian.sigma a x^2 := by
  have hr0 := ne_of_gt hr
  have hs0 := ne_of_gt (Cartesian.sigma_positive a x hr)
  have hd : Cartesian.radius a x^4+Cartesian.b a x^2 ≠ 0 := by positivity
  rw [Cartesian.potentialD, Cartesian.potential_optical 1 a x hr]
  simp only [Cartesian.cosineD,Cartesian.sigma,Cartesian.cosine]
  field_simp
  ring

theorem potentialD_abs_le_ten (a x : Cartesian.Space) (ha : dotProduct a a ≤ 1)
    (hr : 1 ≤ Cartesian.radius a x) (e : Fin 3) : |Cartesian.potentialD 1 a x e| ≤ 10 := by
  have hr0 : 0 < Cartesian.radius a x := by linarith
  have hc := cosine_abs_le_one a x ha hr
  have hd := radiusD_abs_le_two a x ha hr e
  have hcd := cosineD_abs_le_three a x ha hr e
  have hsub : |Cartesian.cosine a x^2-Cartesian.radius a x^2| ≤ 1+Cartesian.radius a x^2 := by
    have h := abs_sub_bound (Cartesian.cosine a x^2) (Cartesian.radius a x^2)
    rw [abs_of_nonneg (sq_nonneg (Cartesian.cosine a x)),
      abs_of_nonneg (sq_nonneg (Cartesian.radius a x))] at h
    have hh := abs_le.mp hc
    nlinarith
  have hfirst : |(Cartesian.cosine a x^2-Cartesian.radius a x^2)*Cartesian.radiusD a x e| ≤ 2*(1+Cartesian.radius a x^2) := by
    rw [abs_mul]
    nlinarith [abs_nonneg (Cartesian.cosine a x^2-Cartesian.radius a x^2), abs_nonneg (Cartesian.radiusD a x e)]
  have hprod : |Cartesian.cosine a x*Cartesian.cosineD a x e| ≤ 3 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (Cartesian.cosine a x),abs_nonneg (Cartesian.cosineD a x e)]
  have hsecond : |2*Cartesian.radius a x*Cartesian.cosine a x*Cartesian.cosineD a x e| ≤ 6*Cartesian.radius a x := by
    have heq : 2*Cartesian.radius a x*Cartesian.cosine a x*Cartesian.cosineD a x e =
        (2*Cartesian.radius a x)*(Cartesian.cosine a x*Cartesian.cosineD a x e) := by ring
    rw [heq,abs_mul,abs_of_pos (by positivity : 0 < 2*Cartesian.radius a x)]
    nlinarith
  rw [potentialD_optical a x hr0 e,abs_div,abs_of_pos (sq_pos_of_pos (Cartesian.sigma_positive a x hr0))]
  apply (div_le_iff₀ (sq_pos_of_pos (Cartesian.sigma_positive a x hr0))).2
  have h := abs_sub_bound
    ((Cartesian.cosine a x^2-Cartesian.radius a x^2)*Cartesian.radiusD a x e)
    (2*Cartesian.radius a x*Cartesian.cosine a x*Cartesian.cosineD a x e)
  have hs : 1 ≤ Cartesian.sigma a x := by unfold Cartesian.sigma; nlinarith [sq_nonneg (Cartesian.cosine a x)]
  have hsr : Cartesian.radius a x^2 ≤ Cartesian.sigma a x := by unfold Cartesian.sigma; nlinarith [sq_nonneg (Cartesian.cosine a x)]
  nlinarith [sq_nonneg (Cartesian.radius a x-1)]

theorem metricD_component_bound (a x : Cartesian.Space) (ha : dotProduct a a ≤ 1)
    (hr : 1 ≤ Cartesian.radius a x) (e : Fin 3) (i j : Fin 4) :
    |Cartesian.metricD 1 a x e i j| ≤ 36 := by
  have hr0 : 0 < Cartesian.radius a x := by linarith
  have hl := ell_component_abs_le_one a x hr0
  have hdl (k : Fin 4) : |Cartesian.ellD a x e k| ≤ 4 := by
    cases k using Fin.cases with
    | zero => simp [Cartesian.ellD]
    | succ k => exact spatialEllD_abs_le_four a x ha hr e k
  have hH := unit_mass_potential_bounds a x hr
  have hHD := potentialD_abs_le_ten a x ha hr e
  have hprod (u v U V : ℝ) (hu : |u| ≤ U) (hv : |v| ≤ V) (hU : 0 ≤ U) : |u*v| ≤ U*V := by
    rw [abs_mul]
    exact mul_le_mul hu hv (abs_nonneg v) hU
  have ht := hprod _ _ _ _ (hprod _ _ _ _ hHD (hl i) (by norm_num)) (hl j) (by norm_num)
  have hleft := hprod _ _ _ _ (hdl i) (hl j) (by norm_num)
  have hright := hprod _ _ _ _ (hl i) (hdl j) (by norm_num)
  have hsum : |Cartesian.ellD a x e i*Cartesian.ell a x j+Cartesian.ell a x i*Cartesian.ellD a x e j| ≤ 8 := by
    linarith [abs_add_le (Cartesian.ellD a x e i*Cartesian.ell a x j) (Cartesian.ell a x i*Cartesian.ellD a x e j)]
  have hh : |Cartesian.potential 1 a x| ≤ 1 := by rw [abs_of_nonneg hH.1]; exact hH.2
  have hb := hprod _ _ _ _ hh hsum (by norm_num)
  unfold Cartesian.metricD
  have heq : 2*Cartesian.potentialD 1 a x e*Cartesian.ell a x i*Cartesian.ell a x j =
      2*(Cartesian.potentialD 1 a x e*Cartesian.ell a x i*Cartesian.ell a x j) := by ring
  rw [heq]
  have h := abs_add_le
    (2*(Cartesian.potentialD 1 a x e*Cartesian.ell a x i*Cartesian.ell a x j))
    (2*Cartesian.potential 1 a x*(Cartesian.ellD a x e i*Cartesian.ell a x j+Cartesian.ell a x i*Cartesian.ellD a x e j))
  simp only [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)] at ht hb h
  nlinarith

theorem metricD_field_component_bound (a x : Cartesian.Space) (ha : dotProduct a a ≤ 1)
    (hr : 1 ≤ Cartesian.radius a x) (e i j : Fin 4) :
    |metricD 1 a x e i j| ≤ 36 := by
  cases e using Fin.cases with
  | zero => simp [metricD]
  | succ e => exact metricD_component_bound a x ha hr e i j

/-- An explicit continuous momentum-growth bound on the normalized exterior.
    Higher derivatives and accumulated trajectory error still need separate bounds. -/
theorem momentum_force_component_bound (a x : Cartesian.Space) (p : Fin 4 → ℝ)
    (P : ℝ) (ha : dotProduct a a ≤ 1) (hr : 1 ≤ Cartesian.radius a x)
    (hp : ∀ j, |p j| ≤ P) (e : Fin 4) :
    |Transport.momentumForce (metricD 1 a x) (((metric 1 a x)⁻¹).mulVec p) e| ≤ 41472*P^2 := by
  have hP : 0 ≤ P := le_trans (abs_nonneg (p 0)) (hp 0)
  have hk := hamiltonian_tangent_component_bound a x p P hr hp
  let k := ((metric 1 a x)⁻¹).mulVec p
  have ht (i j : Fin 4) : |metricD 1 a x e i j*k i*k j| ≤ 36*(12*P)*(12*P) := by
    rw [abs_mul,abs_mul]
    apply mul_le_mul _ (hk j) (abs_nonneg _) (by positivity)
    exact mul_le_mul (metricD_field_component_bound a x ha hr e i j) (hk i)
      (abs_nonneg _) (by norm_num)
  unfold Transport.momentumForce
  rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ)<2)).2
  calc
    _ ≤ ∑ i : Fin 4, |∑ j : Fin 4, metricD 1 a x e i j*k i*k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 4, ∑ j : Fin 4, |metricD 1 a x e i j*k i*k j| := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 4, ∑ _j : Fin 4, 36*(12*P)*(12*P) := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum (fun j _ => ht i j)
    _ = 41472*P^2*2 := by simp; ring

end BlackHole.KerrField
