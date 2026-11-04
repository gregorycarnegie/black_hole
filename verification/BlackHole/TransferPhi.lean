module

public import BlackHole.MatrixTransfer
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Stable Faraday-cell integrals (obligations T2, T3 and F2).

The former `polarized_cell` evaluated
`ic = (α(1 - e cos θ) + w e sin θ)/(α² + w²)` and
`is = (w(1 - e cos θ) - α e sin θ)/(α² + w²)` with `e = exp(-α ds)`,
`θ = w ds`. For small optical depth both numerators cancel: with every
operation correctly rounded, α = 10⁻⁶, w = 10⁻⁵, ds = 1 gives `is` = 1.3·10⁻³
instead of 5.0·10⁻⁶ (`verification/check_transfer_cell.py`).

The shader now evaluates `ic + i·is = ds·φ(z)` with `z = (α - iw) ds` and
`φ(z) = (1 - e^{-z})/z`, using an 11-term Horner series when `|z| < 1/2`.

* `phi_closed_form`: `ds·φ(z)` has exactly the former `ic`, `is` as real and
  imaginary parts, so the existing exact-real transfer theorems apply.
* `horner_eq`: the shader's Horner recurrence is `Σ_{k<11} (-z)^k/(k+1)!`.
* `phi_series_error`: that sum is within `10⁻¹¹` of `φ(z)` for `0 < |z| ≤ 1/2`. -/

@[expose] public section
noncomputable section

open Finset

namespace BlackHole.TransferPhi

/-- φ(z) = (1 - e^{-z})/z. -/
def phi (z : ℂ) : ℂ := (1-Complex.exp (-z))/z

/-- The shader's truncated series. -/
def series (z : ℂ) : ℂ := ∑ k ∈ range 11, (-z)^k/((k+1).factorial : ℂ)

/-- The new evaluation has the former closed form as real and imaginary parts. -/
theorem phi_closed_form (α w ds : ℝ) (hds : ds ≠ 0) (hz : α^2+w^2 ≠ 0) :
    let z : ℂ := ⟨α*ds, -(w*ds)⟩
    let e := Real.exp (-(α*ds))
    let θ := w*ds
    (ds*phi z).re = (α*(1-e*Real.cos θ)+w*e*Real.sin θ)/(α^2+w^2) ∧
      (ds*phi z).im = (w*(1-e*Real.cos θ)-α*e*Real.sin θ)/(α^2+w^2) := by
  intro z e θ
  have hexp_re : (Complex.exp (-z)).re = e*Real.cos θ := by
    rw [Complex.exp_re]; simp [z, e, θ]
  have hexp_im : (Complex.exp (-z)).im = e*Real.sin θ := by
    rw [Complex.exp_im]; simp [z, e, θ]
  have hnorm : z.re*z.re+z.im*z.im = (α^2+w^2)*ds^2 := by simp [z]; ring
  have hnz : z.re*z.re+z.im*z.im ≠ 0 := by rw [hnorm]; exact mul_ne_zero hz (pow_ne_zero 2 hds)
  unfold phi
  constructor
  · rw [Complex.mul_re, Complex.div_re, Complex.div_im, Complex.normSq_apply]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, hexp_re, hexp_im, zero_mul, sub_zero]
    simp only [z]
    field_simp
    ring
  · rw [Complex.mul_im, Complex.div_re, Complex.div_im, Complex.normSq_apply]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, hexp_re, hexp_im, zero_mul, add_zero]
    simp only [z]
    field_simp
    ring

/-- The shader's Horner loop, `acc ← c[k] - z·acc` from `c[10]` down to `c[0]`. -/
theorem horner_eq (z : ℂ) :
    let c : ℕ → ℂ := fun k => 1/((k+1).factorial : ℂ)
    c 0-z*(c 1-z*(c 2-z*(c 3-z*(c 4-z*(c 5-z*(c 6-z*(c 7-z*(c 8-z*(c 9-z*c 10))))))))) =
      series z := by
  intro c
  simp only [series, c, sum_range_succ, sum_range_zero]
  ring

/-- Truncation error of the 11-term series. -/
theorem phi_series_error (z : ℂ) (hz0 : z ≠ 0) (hz : ‖z‖ ≤ 1/2) :
    ‖phi z-series z‖ ≤ 1/10^11 := by
  -- φ(z) - S(z) = -(e^{-z} - Σ_{n<12} (-z)^n/n!)/z.
  have hpartial : ∑ n ∈ range 12, ((n.factorial : ℝ)⁻¹) • (-z)^n = 1-z*series z := by
    simp only [series, sum_range_succ, sum_range_zero, Complex.real_smul]
    push_cast
    field_simp
    ring
  have hdiff : phi z-series z =
      -(NormedSpace.exp (-z)-∑ n ∈ range 12, ((n.factorial : ℝ)⁻¹) • (-z)^n)/z := by
    rw [hpartial, phi, ← Complex.exp_eq_exp_ℂ]
    field_simp
    ring
  have htail := MatrixTransfer.taylor_tail_le (-z) 12
  rw [norm_neg] at htail
  have hreal := Real.exp_bound (x := ‖z‖) (by rw [abs_of_nonneg (norm_nonneg z)]; linarith)
    (n := 12) (by norm_num)
  rw [abs_of_nonneg (norm_nonneg z)] at hreal
  have habs := le_abs_self (Real.exp ‖z‖-∑ m ∈ range 12, ‖z‖^m/m.factorial)
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  rw [hdiff, norm_div, norm_neg, div_le_iff₀ hnz]
  have h1 : ‖NormedSpace.exp (-z)-∑ n ∈ range 12, ((n.factorial : ℝ)⁻¹) • (-z)^n‖ ≤
      ‖z‖^12*((Nat.succ 12 : ℝ)/((Nat.factorial 12 : ℝ)*12)) := by
    have := le_trans htail (le_trans habs hreal)
    push_cast at this ⊢
    exact this
  have h2 : ‖z‖^12 = ‖z‖^11*‖z‖ := by ring
  have h3 : ‖z‖^11 ≤ (1/2)^11 := pow_le_pow_left₀ (norm_nonneg _) hz 11
  have h4 : (1/2:ℝ)^11*((Nat.succ 12 : ℝ)/((Nat.factorial 12 : ℝ)*12)) ≤ 1/10^11 := by
    norm_num [Nat.factorial]
  calc _ ≤ ‖z‖^12*((Nat.succ 12 : ℝ)/((Nat.factorial 12 : ℝ)*12)) := h1
    _ = (‖z‖^11*((Nat.succ 12 : ℝ)/((Nat.factorial 12 : ℝ)*12)))*‖z‖ := by rw [h2]; ring
    _ ≤ ((1/2:ℝ)^11*((Nat.succ 12 : ℝ)/((Nat.factorial 12 : ℝ)*12)))*‖z‖ := by
        gcongr
    _ ≤ 1/10^11*‖z‖ := by gcongr

end BlackHole.TransferPhi
