module

public import BlackHole.Curvature
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section
noncomputable section

namespace BlackHole

theorem inverse_metric_derivative {n : Type*} [Fintype n] [DecidableEq n]
    (G K dG dK : Matrix n n ℝ) (hGK : G * K = 1)
    (hproduct : dK * G + K * dG = 0) : dK = -(K * dG * K) := by
  have h := congrArg (fun M => M * K) hproduct
  simp only [Matrix.add_mul, Matrix.mul_assoc, hGK, Matrix.mul_one, Matrix.zero_mul] at h
  simpa only [Matrix.mul_assoc] using eq_neg_of_add_eq_zero_left h

namespace Curvature

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem determinant_differentiableAt (g : ℝ → Matrix n n ℝ) (t : ℝ)
    (hg : ∀ i j, DifferentiableAt ℝ (fun s => g s i j) t) :
    DifferentiableAt ℝ (fun s => (g s).det) t := by
  classical
  simp only [Matrix.det_apply']
  exact DifferentiableAt.fun_sum (u := Finset.univ) (fun p _ =>
    (DifferentiableAt.fun_finsetProd (u := Finset.univ) (fun i _ => hg (p i) i)).const_mul _)

theorem adjugate_differentiableAt (g : ℝ → Matrix n n ℝ) (t : ℝ)
    (hg : ∀ i j, DifferentiableAt ℝ (fun s => g s i j) t) (i j : n) :
    DifferentiableAt ℝ (fun s => (g s).adjugate i j) t := by
  simp only [Matrix.adjugate_apply]
  apply determinant_differentiableAt
  intro a b
  by_cases h : a = j
  · subst a
    simp only [Matrix.updateRow_self]
    exact differentiableAt_const _
  · simpa only [Matrix.updateRow_ne h] using hg a b

theorem inverse_differentiableAt (g : ℝ → Matrix n n ℝ) (t : ℝ)
    (hg : ∀ i j, DifferentiableAt ℝ (fun s => g s i j) t) (hdet : (g t).det ≠ 0) (i j : n) :
    DifferentiableAt ℝ (fun s => (g s)⁻¹ i j) t := by
  have h := ((determinant_differentiableAt g t hg).inv hdet).mul
    (adjugate_differentiableAt g t hg i j)
  simpa only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv,
    Pi.inv_def, Pi.mul_def] using h

/-- Inversion is differentiated here, including existence of its derivative;
    the inverse-product derivative is not supplied as a theorem hypothesis. -/
theorem inverse_derivative (g : ℝ → Matrix n n ℝ) (dg : Matrix n n ℝ) (t : ℝ)
    (hg : ∀ i j, HasDerivAt (fun s => g s i j) (dg i j) t) (hdet : (g t).det ≠ 0) (i j : n) :
    HasDerivAt (fun s => (g s)⁻¹ i j)
      (-(∑ a, ∑ b, (g t)⁻¹ i a*dg a b*(g t)⁻¹ b j)) t := by
  let dk : Matrix n n ℝ := fun i j => deriv (fun s => (g s)⁻¹ i j) t
  have hk (i j : n) : HasDerivAt (fun s => (g s)⁻¹ i j) (dk i j) t :=
    (inverse_differentiableAt g t (fun i j => (hg i j).differentiableAt) hdet i j).hasDerivAt
  have hevent : ∀ᶠ s in nhds t, (g s).det ≠ 0 :=
    (determinant_differentiableAt g t (fun i j => (hg i j).differentiableAt)).continuousAt.eventually_ne hdet
  have hz (i j : n) : (∑ k, (dk i k*g t k j+(g t)⁻¹ i k*dg k j)) = 0 := by
    have hp := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => (hk i k).mul (hg k j))
    have heq : (fun s => ∑ k, (g s)⁻¹ i k*g s k j) =ᶠ[nhds t]
        (fun _ => (1 : Matrix n n ℝ) i j) := by
      filter_upwards [hevent] with s hs
      exact congrArg (fun m : Matrix n n ℝ => m i j)
        (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hs))
    have hc := (hasDerivAt_const t ((1 : Matrix n n ℝ) i j)).congr_of_eventuallyEq heq
    simp only [Pi.mul_apply] at hp
    exact hp.unique hc
  have hproduct : dk*g t+(g t)⁻¹*dg = 0 := by
    ext i j
    simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      ← Finset.sum_add_distrib] using hz i j
  have hdk := inverse_metric_derivative (g t) (g t)⁻¹ dg dk
    (Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)) hproduct
  have heq : dk i j = -(∑ a, ∑ b, (g t)⁻¹ i a*dg a b*(g t)⁻¹ b j) := by
    rw [hdk]
    simp only [Matrix.neg_apply, Matrix.mul_apply, Finset.sum_mul]
    congr 1
    exact Finset.sum_comm
  rw [← heq]
  exact hk i j

end Curvature
end BlackHole
