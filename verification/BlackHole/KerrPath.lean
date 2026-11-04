module

public import BlackHole.KerrOptical
public import BlackHole.Hamiltonian

@[expose] public section
noncomputable section

namespace BlackHole.Cartesian

theorem q_path_derivative (a : Space) (x : ℝ → Space) (v : Space) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun s => x s i) (v i) t) :
    HasDerivAt (fun s => q a (x s)) (2*dotProduct (x t) v) t := by
  have h := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hx i).pow 2)).sub_const (dotProduct a a)
  simp only [Pi.pow_apply] at h
  convert h using 1
  · simp only [q, dotProduct, ← pow_two]
  · simp [dotProduct, Fin.sum_univ_succ]
    ring

theorem b_path_derivative (a : Space) (x : ℝ → Space) (v : Space) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun s => x s i) (v i) t) :
    HasDerivAt (fun s => b a (x s)) (dotProduct a v) t := by
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hx i).const_mul (a i))

theorem cross_path_derivative (a : Space) (x : ℝ → Space) (v : Space) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun s => x s i) (v i) t) (i : Fin 3) :
    HasDerivAt (fun s => crossProduct a (x s) i) (crossProduct a v i) t := by
  fin_cases i
  · simpa [cross_apply, Pi.sub_def] using ((hx 2).const_mul (a 1)).sub ((hx 1).const_mul (a 2))
  · simpa [cross_apply, Pi.sub_def] using ((hx 0).const_mul (a 2)).sub ((hx 2).const_mul (a 0))
  · simpa [cross_apply, Pi.sub_def] using ((hx 1).const_mul (a 0)).sub ((hx 0).const_mul (a 1))

theorem radius_path_derivative (a : Space) (x : ℝ → Space) (v : Space) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun s => x s i) (v i) t) (hr : 0 < radius a (x t)) :
    HasDerivAt (fun s => radius a (x s)) (∑ e, radiusD a (x t) e*v e) t := by
  obtain ⟨hdisc,hroot⟩ := positive_radius_domain a (x t) hr
  have h := Calculus.kerrRadius_derivative (fun s => q a (x s)) (fun s => b a (x s))
    t (dotProduct (x t) v) (dotProduct a v) (q_path_derivative a x v t hx)
    (b_path_derivative a x v t hx) hdisc hroot
  convert h using 1
  · rfl
  · simp [radiusD, dotProduct, Fin.sum_univ_succ, radius]
    ring

theorem potential_path_derivative (mass : ℝ) (a : Space) (x : ℝ → Space) (v : Space) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun s => x s i) (v i) t) (hr : 0 < radius a (x t)) :
    HasDerivAt (fun s => potential mass a (x s)) (∑ e, potentialD mass a (x t) e*v e) t := by
  have hr0 := ne_of_gt hr
  have hd : radius a (x t)^4+b a (x t)^2 ≠ 0 := by positivity
  have h := Calculus.kerrH_derivative (fun s => radius a (x s)) (fun s => b a (x s)) mass t
    (∑ e, radiusD a (x t) e*v e) (dotProduct a v)
    (radius_path_derivative a x v t hx hr) (b_path_derivative a x v t hx) hr0 hd
  convert h using 1
  · rfl
  · simp [potentialD, potential, dotProduct, Fin.sum_univ_succ]
    ring

theorem spatialEll_path_derivative (a : Space) (x : ℝ → Space) (v : Space) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun s => x s i) (v i) t) (hr : 0 < radius a (x t)) (i : Fin 3) :
    HasDerivAt (fun s => spatialEll a (x s) i) (∑ e, spatialEllD a (x t) e i*v e) t := by
  have hr0 := ne_of_gt hr
  have haa : 0 ≤ dotProduct a a := Finset.sum_nonneg (fun j _ => mul_self_nonneg (a j))
  have hd : radius a (x t)^2+dotProduct a a ≠ 0 := by positivity
  have h := Calculus.ell_component_derivative (fun s => radius a (x s)) (fun s => x s i)
    (fun s => b a (x s)) (fun s => crossProduct a (x s) i) (a i) (dotProduct a a) t
    (∑ e, radiusD a (x t) e*v e) (v i) (dotProduct a v) (crossProduct a v i)
    (radius_path_derivative a x v t hx hr) (hx i) (b_path_derivative a x v t hx)
    (cross_path_derivative a x v t hx i) hr0 hd
  convert h using 1
  · rfl
  · fin_cases i <;> simp [spatialEllD, spatialEll, dotProduct, Fin.sum_univ_succ, basis, cross_apply] <;> ring

theorem ell_path_derivative (a : Space) (x : ℝ → Space) (v : Space) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun s => x s i) (v i) t) (hr : 0 < radius a (x t)) (i : Fin 4) :
    HasDerivAt (fun s => ell a (x s) i) (∑ e, ellD a (x t) e i*v e) t := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simpa only [ell, ellD, Fin.cases_zero, zero_mul, Finset.sum_const_zero] using hasDerivAt_const t (1 : ℝ)
  · exact spatialEll_path_derivative a x v t hx hr i

theorem metric_path_derivative (mass : ℝ) (a : Space) (x : ℝ → Space) (v : Space) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun s => x s i) (v i) t) (hr : 0 < radius a (x t)) (i j : Fin 4) :
    HasDerivAt (fun s => metric mass a (x s) i j) (∑ e, metricD mass a (x t) e i j*v e) t := by
  have h := (Calculus.metric_component_derivative (fun s => potential mass a (x s))
    (fun s => ell a (x s) i) (fun s => ell a (x s) j) t
    (∑ e, potentialD mass a (x t) e*v e) (∑ e, ellD a (x t) e i*v e)
    (∑ e, ellD a (x t) e j*v e) (potential_path_derivative mass a x v t hx hr)
    (ell_path_derivative a x v t hx hr i) (ell_path_derivative a x v t hx hr j)).const_add (eta i j)
  convert h using 1
  · rfl
  · simp [metricD, Fin.sum_univ_succ]
    ring

end BlackHole.Cartesian

namespace BlackHole.KerrField

theorem metric_path_derivative (mass : ℝ) (a : Cartesian.Space) (x : ℝ → Cartesian.Space)
    (k : Fin 4 → ℝ) (t : ℝ) (hx : ∀ i, HasDerivAt (fun s => x s i) (k i.succ) t)
    (hr : 0 < Cartesian.radius a (x t)) (i j : Fin 4) :
    HasDerivAt (fun s => metric mass a (x s) i j)
      (Transport.metricRate (metricD mass a (x t)) k i j) t := by
  have h := Cartesian.metric_path_derivative mass a x (fun e => k e.succ) t hx hr i j
  simpa only [metric, Matrix.of_apply, Transport.metricRate, metricD, Fin.sum_univ_succ,
    Fin.cases_zero, Fin.cases_succ, Matrix.zero_apply, zero_mul, zero_add] using h

theorem metricD_symmetric (mass : ℝ) (a x : Cartesian.Space) (e i j : Fin 4) :
    metricD mass a x e i j = metricD mass a x e j i := by
  cases e using Fin.cases with
  | zero => rfl
  | succ e =>
    simp only [metricD, Fin.cases_succ, Matrix.of_apply, Cartesian.metricD]
    ring

theorem tangent_path_derivative (mass : ℝ) (a : Cartesian.Space)
    (x : ℝ → Cartesian.Space) (p : ℝ → Fin 4 → ℝ) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun s => x s i) (((metric mass a (x t))⁻¹).mulVec (p t) i.succ) t)
    (hp : ∀ i, HasDerivAt (fun s => p s i)
      (Transport.momentumForce (metricD mass a (x t)) ((metric mass a (x t))⁻¹.mulVec (p t)) i) t)
    (hr : 0 < Cartesian.radius a (x t)) (i : Fin 4) :
    HasDerivAt (fun s => (metric mass a (x s))⁻¹.mulVec (p s) i)
      (-(∑ c, Transport.contractedConnection (metric mass a (x t))⁻¹ (metricD mass a (x t))
        ((metric mass a (x t))⁻¹.mulVec (p t)) i c*((metric mass a (x t))⁻¹.mulVec (p t)) c)) t := by
  exact Transport.hamiltonian_tangent_derivative (fun s => metric mass a (x s)) p
    (metricD mass a (x t)) t (metric_nonsingular mass a (x t) hr)
    (metric_path_derivative mass a x _ t hx hr) hp i

/-- These are the actual Cartesian Kerr field and Hamiltonian equations,
    with the derivative chain along the ray proved above. -/
theorem pairings_path_derivatives (mass : ℝ) (a : Cartesian.Space)
    (x : ℝ → Cartesian.Space) (p screen : ℝ → Fin 4 → ℝ) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun s => x s i) (((metric mass a (x t))⁻¹).mulVec (p t) i.succ) t)
    (hp : ∀ i, HasDerivAt (fun s => p s i)
      (Transport.momentumForce (metricD mass a (x t)) ((metric mass a (x t))⁻¹.mulVec (p t)) i) t)
    (hscreen : ∀ i, HasDerivAt (fun s => screen s i)
      (-(∑ c, Transport.contractedConnection (metric mass a (x t))⁻¹ (metricD mass a (x t))
        ((metric mass a (x t))⁻¹.mulVec (p t)) i c*screen t c)) t)
    (hr : 0 < Cartesian.radius a (x t)) :
    let k := fun s => (metric mass a (x s))⁻¹.mulVec (p s)
    let g := fun s => metric mass a (x s)
    HasDerivAt (fun s => Transport.pairing (g s) (k s) (k s)) 0 t ∧
      HasDerivAt (fun s => Transport.pairing (g s) (k s) (screen s)) 0 t ∧
      HasDerivAt (fun s => Transport.pairing (g s) (screen s) (screen s)) 0 t := by
  let k := fun s => (metric mass a (x s))⁻¹.mulVec (p s)
  let g := fun s => metric mass a (x s)
  let C := fun s => Matrix.of (Transport.contractedConnection (g s)⁻¹ (metricD mass a (x s)) (k s))
  have hmetric (i j : Fin 4) : HasDerivAt (fun s => g s i j)
      (∑ c, (C t c i*g t c j+g t i c*C t c j)) t := by
    have hcompat := Transport.contracted_metric_compatible (g t) (g t)⁻¹
      (Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (metric_nonsingular mass a (x t) hr)))
      (metric_symmetric mass a (x t)) (metricD mass a (x t)) (metricD_symmetric mass a (x t)) (k t) i j
    dsimp only [C, Matrix.of_apply]
    rw [hcompat]
    exact metric_path_derivative mass a x (k t) t hx hr i j
  have hk := tangent_path_derivative mass a x p t hx hp hr
  exact ⟨Transport.transported_pairing_derivative g C k k t hmetric hk hk,
    Transport.transported_pairing_derivative g C k screen t hmetric hk hscreen,
    Transport.transported_pairing_derivative g C screen screen t hmetric hscreen hscreen⟩

end BlackHole.KerrField
