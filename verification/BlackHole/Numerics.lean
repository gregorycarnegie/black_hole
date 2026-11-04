module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace BlackHole.Numerics

/-- Rust's finite-input horizon computation, including the spin clamp.
    Core Float32 arithmetic and sqrt reduce in Lean's kernel. -/
def horizon32 (spin : Float32) : Float32 :=
  let a := if spin.abs ≤ 0.999 then spin.abs else 0.999
  1 + (1 - a * a).sqrt

private meta def fixtureText : String := include_str ".."/"fixtures"/"horizon-binary32.csv"

/-- Parsing generates a literal list; each floating-point calculation on that
    list is subsequently checked by the kernel, not by native_decide. -/
macro "horizon_fixture_cases" : term => do
  let rows := fixtureText.trimAscii.toString.splitOn "\n"
  let cases ← rows.toArray.mapM fun row => do
    let [input, output] := row.trimAscii.toString.splitOn ","
      | Lean.Macro.throwError "expected input_bits,output_bits"
    let some a := input.toNat? | Lean.Macro.throwError "invalid input bits"
    let some b := output.toNat? | Lean.Macro.throwError "invalid output bits"
    unless a < 2^32 ∧ b < 2^32 do Lean.Macro.throwError "binary32 bits out of range"
    `((($(Lean.quote a) : UInt32), ($(Lean.quote b) : UInt32)))
  `([$[$cases],*])

def horizonCases : List (UInt32 × UInt32) := horizon_fixture_cases

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem horizon_binary32_replay :
    horizonCases.length = 9 ∧
      horizonCases.all (fun (a, b) => (horizon32 (Float32.ofBits a)).toBits == b) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem binary32_horizon_has_roundoff :
    let a := Float32.ofBits 1065336439 -- the Rust literal 0.999_f32
    let r := horizon32 a
    let residual := (r*r - 2*r + a*a).toBits
    residual ≠ 0 ∧ residual ≠ 2147483648 := by
  decide +kernel

/-- IEEE-754 finite binary32 interpretation, including signed zero and
    subnormals. Nonfinite encodings have no rational interpretation. -/
def binary32Value (bits : UInt32) : Option ℚ :=
  let exponent : ℕ := bits.toNat / 2^23 % 256
  let fraction : ℕ := bits.toNat % 2^23
  let sign : ℚ := if bits.toNat / 2^31 = 0 then 1 else -1
  if exponent = 255 then none else
    let significand := if exponent = 0 then fraction else fraction + 2^23
    let power : ℤ := if exponent = 0 then -149 else (exponent : ℤ) - 150
    some (sign * (significand : ℚ) * (2 : ℚ)^power)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem horizon_sample_residual_bound :
    horizonCases.all (fun (input, output) =>
      match binary32Value input, binary32Value output, binary32Value 1065336439 with
      | some a, some r, some limit =>
        let clamped := min |a| limit
        decide (|r*r - 2*r + clamped*clamped| ≤ (1/1000000 : ℚ))
      | _, _, _ => false) = true := by
  decide +kernel

noncomputable def flatNullConstraint (p : Fin 4 → ℝ) : ℝ :=
  -(p 0)^2 + (p 1)^2 + (p 2)^2 + (p 3)^2

/-- Equal energy and zero null residual do not fix the propagation direction. -/
theorem null_residual_not_an_error_estimator :
    ∃ p q : Fin 4 → ℝ, p 0 = q 0 ∧ flatNullConstraint p = 0 ∧
      flatNullConstraint q = 0 ∧
      (p 1 - q 1)^2 + (p 2 - q 2)^2 + (p 3 - q 3)^2 = 2 := by
  refine ⟨(fun i => if i = 0 ∨ i = 1 then 1 else 0),
    (fun i => if i = 0 ∨ i = 2 then 1 else 0), ?_⟩
  norm_num [flatNullConstraint]

noncomputable section

/-- The exact-real classical RK4 stages used by step_ray, specialized to y'=λy. -/
def rk4Linear (lambda h y : ℝ) : ℝ :=
  let k1 := lambda * y
  let k2 := lambda * (y + h / 2 * k1)
  let k3 := lambda * (y + h / 2 * k2)
  let k4 := lambda * (y + h * k3)
  y + h / 6 * (k1 + 2*k2 + 2*k3 + k4)

def rk4Polynomial (z : ℝ) : ℝ := 1 + z + z^2/2 + z^3/6 + z^4/24

theorem rk4_linear_stages (lambda h y : ℝ) :
    rk4Linear lambda h y = y * rk4Polynomial (lambda * h) := by
  unfold rk4Linear rk4Polynomial
  ring

theorem rk4_large_step_is_unstable : rk4Polynomial (-3) = 11/8 := by
  norm_num [rk4Polynomial]

/-- Exact local defect on a fifth-degree solution: y'=5t^4, y=t^5.
    This is a nonzero truncation error even before floating-point rounding. -/
theorem rk4_quartic_forcing_defect (t h : ℝ) :
    t^5 + h/6 * (5*t^4 + 4*(5*(t+h/2)^4) + 5*(t+h)^4) - (t+h)^5 = h^5/24 := by
  ring

/-- Stage perturbations of size ε change the weighted RK4 update by at most
    |h| ε, before rounding the weighted sum and state update themselves. -/
theorem rk4_stage_error_bound (h e1 e2 e3 e4 eps : ℝ)
    (h1 : |e1| ≤ eps) (h2 : |e2| ≤ eps) (h3 : |e3| ≤ eps) (h4 : |e4| ≤ eps) :
    |h/6 * (e1 + 2*e2 + 2*e3 + e4)| ≤ |h| * eps := by
  rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  have hsum : |e1 + 2*e2 + 2*e3 + e4| ≤ 6*eps := by
    have h12 := abs_add_le e1 (2*e2)
    have h123 := abs_add_le (e1+2*e2) (2*e3)
    have h1234 := abs_add_le (e1+2*e2+2*e3) e4
    simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at *
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hsum (abs_nonneg h)]

/-- A conditional accumulated-error bound. The recurrence must be established
    for the chosen ODE/domain; a null-residual test does not establish it. -/
theorem accumulated_error_bound (error : ℕ → ℝ) (growth defect : ℝ)
    (hgrowth : 0 ≤ growth) (hzero : error 0 = 0)
    (hstep : ∀ n, error (n+1) ≤ growth * error n + defect) :
    ∀ n, error n ≤ defect * ∑ i ∈ Finset.range n, growth^i := by
  have hsum (n : ℕ) : growth * (∑ i ∈ Finset.range n, growth^i) + 1 =
        ∑ i ∈ Finset.range (n+1), growth^i := by
    induction n with
    | zero => simp
    | succ n ihn =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, ← ihn, pow_succ]
      ring
  intro n
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
    have h := mul_le_mul_of_nonneg_left ih hgrowth
    nlinarith [hstep n, congrArg (fun x => defect*x) (hsum n)]

end
end BlackHole.Numerics
