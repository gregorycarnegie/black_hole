module

public import BlackHole.Transfer
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp

@[expose] public section
noncomputable section

namespace BlackHole

open intervalIntegral

theorem cosineIntegral_as_integral (alpha w s : ℝ) (hd : alpha^2+w^2 ≠ 0) :
    Calculus.cosineIntegral alpha w s =
      ∫ t in 0..s, Real.exp (-alpha*t)*Real.cos (w*t) := by
  have h := integral_eq_sub_of_hasDerivAt
    (fun t _ => Calculus.cosineIntegral_derivative alpha w t hd)
    (show IntervalIntegrable (fun t => Real.exp (-alpha*t)*Real.cos (w*t))
      MeasureTheory.volume 0 s from Continuous.intervalIntegrable (by fun_prop) _ _)
  simpa [(Calculus.polarized_coefficients_zero alpha w).1] using h.symm

theorem sineIntegral_as_integral (alpha w s : ℝ) (hd : alpha^2+w^2 ≠ 0) :
    Calculus.sineIntegral alpha w s =
      ∫ t in 0..s, Real.exp (-alpha*t)*Real.sin (w*t) := by
  have h := integral_eq_sub_of_hasDerivAt
    (fun t _ => Calculus.sineIntegral_derivative alpha w t hd)
    (show IntervalIntegrable (fun t => Real.exp (-alpha*t)*Real.sin (w*t))
      MeasureTheory.volume 0 s from Continuous.intervalIntegrable (by fun_prop) _ _)
  simpa [(Calculus.polarized_coefficients_zero alpha w).2] using h.symm

theorem absorption_as_integral (alpha s : ℝ) :
    absorption alpha s = ∫ t in 0..s, Real.exp (-alpha*t) := by
  have h := integral_eq_sub_of_hasDerivAt (fun t _ => absorption_derivative_all alpha t)
    (show IntervalIntegrable (fun t => Real.exp (-alpha*t)) MeasureTheory.volume 0 s
      from Continuous.intervalIntegrable (by fun_prop) _ _)
  simpa [absorption_zero_distance] using h.symm

private theorem weighted_trig_bound (alpha w t : ℝ) (ha : 0 ≤ alpha)
    (hw : 0 ≤ w) (ht : 0 ≤ t) :
    |Real.exp (-alpha*t)*Real.sin (w*t)| ≤ w*t ∧
    |Real.exp (-alpha*t)*(Real.cos (w*t)-1)| ≤ w*t := by
  have he : Real.exp (-alpha*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have he0 := le_of_lt (Real.exp_pos (-alpha*t))
  have hs : |Real.sin (w*t)| ≤ w*t := by
    simpa [abs_of_nonneg (mul_nonneg hw ht)] using Real.abs_sin_le_abs (x := w*t)
  have hc : |Real.cos (w*t)-1| ≤ w*t := by
    simpa [abs_of_nonneg (mul_nonneg hw ht)] using Real.abs_cos_sub_cos_le (w*t) 0
  constructor
  · rw [abs_mul, abs_of_nonneg he0]
    exact (mul_le_mul_of_nonneg_left hs he0).trans
      (by simpa using mul_le_mul_of_nonneg_right he (mul_nonneg hw ht))
  · rw [abs_mul, abs_of_nonneg he0]
    exact (mul_le_mul_of_nonneg_left hc he0).trans
      (by simpa using mul_le_mul_of_nonneg_right he (mul_nonneg hw ht))

/-- Bounds both coefficients discarded by the small-Faraday-depth branch.
    This is real arithmetic; threshold rounding and the absorption polynomial
    contribute separate errors. -/
theorem omitted_faraday_coefficients (alpha w s : ℝ)
    (ha : 0 ≤ alpha) (hw : 0 ≤ w) (hs : 0 ≤ s) (hd : alpha^2+w^2 ≠ 0) :
    |Calculus.cosineIntegral alpha w s-absorption alpha s| ≤ w*s^2/2 ∧
    |Calculus.sineIntegral alpha w s| ≤ w*s^2/2 := by
  have hbound : IntervalIntegrable (fun t => w*t) MeasureTheory.volume 0 s :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hi : (∫ t in 0..s, w*t) = w*s^2/2 := by
    rw [integral_const_mul, integral_id]
    ring
  have hsin := norm_integral_le_of_norm_le (f := fun t => Real.exp (-alpha*t)*Real.sin (w*t)) hs
    (Filter.Eventually.of_forall (fun t ht => by
      simpa [Real.norm_eq_abs] using (weighted_trig_bound alpha w t ha hw (le_of_lt ht.1)).1))
    hbound
  have hcos := norm_integral_le_of_norm_le
    (f := fun t => Real.exp (-alpha*t)*(Real.cos (w*t)-1)) hs
    (Filter.Eventually.of_forall (fun t ht => by
      simpa [Real.norm_eq_abs] using (weighted_trig_bound alpha w t ha hw (le_of_lt ht.1)).2))
    hbound
  rw [hi, Real.norm_eq_abs] at hsin hcos
  constructor
  · rw [cosineIntegral_as_integral alpha w s hd, absorption_as_integral]
    rw [← integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    convert hcos using 1
    congr 1
    apply integral_congr
    intro t _
    ring
  · simpa [sineIntegral_as_integral alpha w s hd] using hsin

theorem omitted_faraday_component (axis j : Fin 3 → ℝ) (alpha w s : ℝ)
    (ha : 0 ≤ alpha) (hw : 0 ≤ w) (hs : 0 ≤ s) (hd : alpha^2+w^2 ≠ 0) (i : Fin 3) :
    |cellPolarization axis j alpha w s i-absorption alpha s*j i| ≤
      (w*s^2/2)*(|j i-dotProduct axis j*axis i|+
        |crossProduct axis (j-dotProduct axis j • axis) i|) := by
  obtain ⟨hc, ht⟩ := omitted_faraday_coefficients alpha w s ha hw hs hd
  have heq : cellPolarization axis j alpha w s i-absorption alpha s*j i =
      (Calculus.cosineIntegral alpha w s-absorption alpha s)*(j i-dotProduct axis j*axis i)+
      Calculus.sineIntegral alpha w s*crossProduct axis (j-dotProduct axis j • axis) i := by
    simp only [cellPolarization, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [heq]
  calc
    _ ≤ |(Calculus.cosineIntegral alpha w s-absorption alpha s)*
        (j i-dotProduct axis j*axis i)|+
        |Calculus.sineIntegral alpha w s*crossProduct axis (j-dotProduct axis j • axis) i| :=
      abs_add_le _ _
    _ ≤ (w*s^2/2)*|j i-dotProduct axis j*axis i|+
        (w*s^2/2)*|crossProduct axis (j-dotProduct axis j • axis) i| := by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_right hc (abs_nonneg _))
        (mul_le_mul_of_nonneg_right ht (abs_nonneg _))
    _ = _ := by ring

theorem omitted_faraday_cutoff (w s : ℝ) (hs : 0 ≤ s)
    (hcut : w*s ≤ (1/100000 : ℝ)) : w*s^2/2 ≤ s/200000 := by
  nlinarith [mul_le_mul_of_nonneg_right hcut hs]

end BlackHole
