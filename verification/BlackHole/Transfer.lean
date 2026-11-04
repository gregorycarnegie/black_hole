module

public import BlackHole.Calculus
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

@[expose] public section
noncomputable section

namespace BlackHole

def absorption (alpha ds : ℝ) : ℝ :=
  if alpha = 0 then ds else (1 - Real.exp (-alpha * ds)) / alpha

theorem absorption_zero_opacity (ds : ℝ) : absorption 0 ds = ds := by
  simp [absorption]

theorem absorption_nonneg (alpha ds : ℝ) (ha : 0 < alpha) (hs : 0 ≤ ds) :
    0 ≤ absorption alpha ds := by
  simp only [absorption, ite_eq_right (ne_of_gt ha)]
  apply div_nonneg _ (le_of_lt ha)
  have h := Real.exp_le_one_iff.mpr (show -alpha * ds ≤ 0 by nlinarith)
  linarith

theorem absorption_zero_distance (alpha : ℝ) : absorption alpha 0 = 0 := by
  simp [absorption]

theorem absorption_nonneg_of_nonneg (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s) :
    0 ≤ absorption alpha s := by
  rcases ha.eq_or_lt with hz | hp
  · rw [← hz, absorption_zero_opacity]
    exact hs
  · exact absorption_nonneg alpha s hp hs

theorem absorption_derivative (alpha ds : ℝ) (ha : alpha ≠ 0) :
    HasDerivAt (absorption alpha) (Real.exp (-alpha * ds)) ds := by
  have h := (((hasDerivAt_id ds).const_mul (-alpha)).exp.const_sub 1).div_const alpha
  unfold absorption
  simp only [ite_eq_right ha]
  change HasDerivAt (fun x => (1 - Real.exp (-alpha * x)) / alpha) _ ds
  simp only [id_eq, mul_one] at h
  convert h using 1
  field_simp

theorem absorption_composes (alpha x y : ℝ) :
    absorption alpha (x + y) = absorption alpha x +
      Real.exp (-alpha * x) * absorption alpha y := by
  by_cases ha : alpha = 0
  · simp [absorption, ha]
  simp only [absorption, ite_eq_right ha]
  rw [mul_add, Real.exp_add]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem absorption_derivative_all (alpha ds : ℝ) :
    HasDerivAt (absorption alpha) (Real.exp (-alpha*ds)) ds := by
  by_cases ha : alpha = 0
  · subst alpha
    unfold absorption
    simpa using hasDerivAt_id' ds
  exact absorption_derivative alpha ds ha

theorem absorption_coefficient_ode (alpha s : ℝ) :
    Real.exp (-alpha*s) = 1-alpha*absorption alpha s := by
  by_cases ha : alpha = 0
  · simp [ha]
  simp only [absorption, ite_eq_right ha]
  field_simp
  ring

def cellPolarization (axis j : Fin 3 → ℝ) (alpha w s : ℝ) : Fin 3 → ℝ :=
  let parallel := dotProduct axis j • axis
  let perpendicular := j-parallel
  absorption alpha s • parallel + Calculus.cosineIntegral alpha w s • perpendicular +
    Calculus.sineIntegral alpha w s • crossProduct axis perpendicular

theorem cellPolarization_zero (axis j : Fin 3 → ℝ) (alpha w : ℝ) :
    cellPolarization axis j alpha w 0 = 0 := by
  simp [cellPolarization, absorption_zero_distance, (Calculus.polarized_coefficients_zero alpha w).1,
    (Calculus.polarized_coefficients_zero alpha w).2]

/-- The full vector source/absorption/Faraday formula in polarized_cell solves
    dP/ds = w axis×P - alpha P + j, with the separate zero-frequency limit.
    This concerns the exact coefficients, before the shader's thresholds. -/
theorem cellPolarization_solves_transfer (axis j : Fin 3 → ℝ) (alpha w s : ℝ)
    (haxis : dotProduct axis axis = 1) (hd : alpha^2+w^2 ≠ 0) (i : Fin 3) :
    HasDerivAt (fun t => cellPolarization axis j alpha w t i)
      ((w • crossProduct axis (cellPolarization axis j alpha w s) -
        alpha • cellPolarization axis j alpha w s + j) i) s := by
  let parallel := dotProduct axis j • axis
  let perpendicular := j-parallel
  let turn := crossProduct axis perpendicular
  have hp : dotProduct axis perpendicular = 0 := by
    simp [perpendicular, parallel, dotProduct_sub, dotProduct_smul, haxis]
  have hpar : crossProduct axis parallel = 0 := by
    simp [parallel, map_smul, cross_self]
  have hturn : crossProduct axis turn = -perpendicular := by
    simp [turn, cross_cross_eq_smul_sub_smul', hp, haxis]
  have hj (k : Fin 3) : j k = parallel k+perpendicular k := by
    dsimp [perpendicular]
    ring
  have hvector : w • crossProduct axis (cellPolarization axis j alpha w s) -
      alpha • cellPolarization axis j alpha w s+j =
      Real.exp (-alpha*s) • parallel +
        (Real.exp (-alpha*s)*Real.cos (w*s)) • perpendicular +
        (Real.exp (-alpha*s)*Real.sin (w*s)) • turn := by
    change w • crossProduct axis (absorption alpha s • parallel +
      Calculus.cosineIntegral alpha w s • perpendicular + Calculus.sineIntegral alpha w s • turn) -
      alpha • (absorption alpha s • parallel + Calculus.cosineIntegral alpha w s • perpendicular +
      Calculus.sineIntegral alpha w s • turn) + j = _
    simp only [map_add, map_smul, hpar, hturn, smul_zero]
    ext k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, Pi.neg_apply, smul_eq_mul]
    rw [hj k, (Calculus.polarized_coefficients_ode alpha w s hd).1,
      (Calculus.polarized_coefficients_ode alpha w s hd).2, absorption_coefficient_ode]
    dsimp only [turn]
    ring
  rw [hvector]
  change HasDerivAt (fun t => absorption alpha t*parallel i +
    Calculus.cosineIntegral alpha w t*perpendicular i + Calculus.sineIntegral alpha w t*turn i)
    (Real.exp (-alpha*s)*parallel i + (Real.exp (-alpha*s)*Real.cos (w*s))*perpendicular i +
      (Real.exp (-alpha*s)*Real.sin (w*s))*turn i) s
  exact (((absorption_derivative_all alpha s).mul_const (parallel i)).add
    ((Calculus.cosineIntegral_derivative alpha w s hd).mul_const (perpendicular i))).add
    ((Calculus.sineIntegral_derivative alpha w s hd).mul_const (turn i))

theorem zeroFaraday_solves_transfer (j alpha s : ℝ) :
    HasDerivAt (fun t => j*absorption alpha t) (j-alpha*(j*absorption alpha s)) s := by
  have h := (absorption_derivative_all alpha s).const_mul j
  rw [absorption_coefficient_ode] at h
  convert h using 1
  ring

def absorptionTaylor (alpha s : ℝ) : ℝ := s*(1-alpha*s/2+(alpha*s)^2/6)

theorem absorptionTaylor_zero_opacity (s : ℝ) : absorptionTaylor 0 s = absorption 0 s := by
  simp [absorptionTaylor, absorption]

/-- Explicit real truncation bound for the shader's small-optical-depth
    absorption branch. Floating-point evaluation error is separate. -/
theorem absorptionTaylor_error (alpha s : ℝ) (ha : 0 < alpha) (hs : 0 ≤ s)
    (ht : alpha*s ≤ 1) :
    |absorption alpha s-absorptionTaylor alpha s| ≤ (5/96)*s*(alpha*s)^3 := by
  have hnonneg : 0 ≤ alpha*s := mul_nonneg (le_of_lt ha) hs
  have h := Real.exp_bound (x := -(alpha*s))
    (by rw [abs_neg, abs_of_nonneg hnonneg]; exact ht) (n := 4) (by decide)
  norm_num [Finset.sum_range_succ, abs_neg, abs_of_nonneg hnonneg] at h
  have heq : absorption alpha s-absorptionTaylor alpha s =
      -(Real.exp (-(alpha*s))-(1-alpha*s+(alpha*s)^2/2-(alpha*s)^3/6))/alpha := by
    simp only [absorption, ite_eq_right (ne_of_gt ha), absorptionTaylor]
    rw [neg_mul]
    field_simp
    ring
  rw [heq, abs_div, abs_neg, abs_of_pos ha]
  calc
    _ ≤ ((5/96)*(alpha*s)^4)/alpha := by
      apply div_le_div_of_nonneg_right _ (le_of_lt ha)
      convert h using 1
      · congr 1
        ring
      · ring
    _ = (5/96)*s*(alpha*s)^3 := by field_simp

theorem absorptionTaylor_cutoff_error (alpha s : ℝ) (ha : 0 < alpha) (hs : 0 ≤ s)
    (ht : alpha*s ≤ (1/1000 : ℝ)) :
    |absorption alpha s-absorptionTaylor alpha s| ≤ s/19200000000 := by
  have hp := pow_le_pow_left₀ (mul_nonneg (le_of_lt ha) hs) ht 3
  have hscaled := mul_le_mul_of_nonneg_left hp (show 0 ≤ (5/96 : ℝ)*s by positivity)
  calc
    _ ≤ (5/96)*s*(alpha*s)^3 := absorptionTaylor_error alpha s ha hs (by linarith)
    _ ≤ (5/96)*s*(1/1000 : ℝ)^3 := hscaled
    _ = s/19200000000 := by ring

def polarizationNormSquared (p : Fin 3 → ℝ) : ℝ := (p 0)^2+(p 1)^2+(p 2)^2

theorem homogeneous_polarization_norm_derivative (p : ℝ → Fin 3 → ℝ)
    (rho : Fin 3 → ℝ) (alpha s : ℝ)
    (hp : ∀ i, HasDerivAt (fun t => p t i) (crossProduct rho (p s) i-alpha*p s i) s) :
    HasDerivAt (fun t => polarizationNormSquared (p t))
      (-2*alpha*polarizationNormSquared (p s)) s := by
  have h := (((hp 0).pow 2).add ((hp 1).pow 2)).add ((hp 2).pow 2)
  change HasDerivAt (fun t => (p t 0)^2+(p t 1)^2+(p t 2)^2)
    (-2*alpha*((p s 0)^2+(p s 1)^2+(p s 2)^2)) s
  convert h using 1
  simp [cross_apply]
  ring

/-- Uniqueness of the full constant-coefficient polarized transfer ODE follows
    from the weighted squared norm of the difference of two solutions. -/
theorem polarized_transfer_unique (p q : ℝ → Fin 3 → ℝ)
    (rho j : Fin 3 → ℝ) (alpha : ℝ)
    (hp : ∀ t i, HasDerivAt (fun s => p s i) (crossProduct rho (p t) i-alpha*p t i+j i) t)
    (hq : ∀ t i, HasDerivAt (fun s => q s i) (crossProduct rho (q t) i-alpha*q t i+j i) t)
    (hzero : p 0 = q 0) : ∀ t, p t = q t := by
  let d := fun t => p t-q t
  have hd (t : ℝ) (i : Fin 3) :
      HasDerivAt (fun s => d s i) (crossProduct rho (d t) i-alpha*d t i) t := by
    have h := (hp t i).sub (hq t i)
    convert h using 1
    dsimp [d]
    simp only [map_sub, Pi.sub_apply]
    ring
  have hw (t : ℝ) : HasDerivAt
      (fun s => Real.exp (2*alpha*s)*polarizationNormSquared (d s)) 0 t := by
    have h := (((hasDerivAt_id' t).const_mul (2*alpha)).exp).mul
      (homogeneous_polarization_norm_derivative d rho alpha t (hd t))
    convert h using 1
    simp only [mul_one]
    ring
  have hz : polarizationNormSquared (d 0) = 0 := by
    simp [d, hzero, polarizationNormSquared]
  intro t
  have hc := is_const_of_deriv_eq_zero (fun s => (hw s).differentiableAt)
    (fun s => (hw s).deriv) t 0
  have hn : polarizationNormSquared (d t) = 0 := by
    simp only [hz, mul_zero] at hc
    exact (mul_eq_zero.mp hc).resolve_left (Real.exp_ne_zero _)
  have h0 := sq_nonneg (d t 0)
  have h1 := sq_nonneg (d t 1)
  have h2 := sq_nonneg (d t 2)
  unfold polarizationNormSquared at hn
  ext i
  fin_cases i <;> dsimp [d] at * <;> nlinarith

end BlackHole
