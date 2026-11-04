module

public import BlackHole.MatrixTransfer
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Fourth-order consistency of classical RK4 (obligation N1, partial).

* `order_conditions`: the RK4 Butcher tableau satisfies all eight order
  conditions for order four, and `not_order_five` shows the quadrature
  condition `Σ bᵢcᵢ⁴ = 1/5` fails, so the classical order is exactly four.
* `linear_step`: for a linear system `Y' = A Y` in any Banach algebra the RK4
  step is the degree-four Taylor polynomial of `exp(hA)` applied to `Y`.
* `linear_consistency`: the local error is at most `‖Y‖ ‖hA‖⁵ · 6/(5!·5)`
  whenever `‖hA‖ ≤ 1`, i.e. fourth-order consistency for every linear field
  (including transport along a fixed path).

The general nonlinear statement, needed for the full geodesic/screen field,
requires the multivariate Taylor expansion of the stages and remains open. -/

@[expose] public section
noncomputable section

open Finset NormedSpace

namespace BlackHole.RK4Order

/-- RK4 nodes, weights and stage matrix. -/
def c : Fin 4 → ℚ := ![0, 1/2, 1/2, 1]
def b : Fin 4 → ℚ := ![1/6, 1/3, 1/3, 1/6]
def a : Fin 4 → Fin 4 → ℚ := ![![0,0,0,0], ![1/2,0,0,0], ![0,1/2,0,0], ![0,0,1,0]]

/-- All eight rooted-tree order conditions up to order four. -/
theorem order_conditions :
    (∑ i, b i) = 1 ∧
    (∑ i, b i*c i) = 1/2 ∧
    (∑ i, b i*c i^2) = 1/3 ∧
    (∑ i, ∑ j, b i*a i j*c j) = 1/6 ∧
    (∑ i, b i*c i^3) = 1/4 ∧
    (∑ i, ∑ j, b i*c i*a i j*c j) = 1/8 ∧
    (∑ i, ∑ j, b i*a i j*c j^2) = 1/12 ∧
    (∑ i, ∑ j, ∑ k, b i*a i j*a j k*c k) = 1/24 ∧
    -- Row sums: cᵢ = Σⱼ aᵢⱼ.
    (∀ i, c i = ∑ j, a i j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (simp [Fin.sum_univ_four, b, c, a]; norm_num; done)
  intro i
  fin_cases i <;> simp [Fin.sum_univ_four, c, a]

/-- The fifth-order quadrature condition fails, so the order is exactly four. -/
theorem not_order_five : (∑ i, b i*c i^4) ≠ 1/5 := by
  simp [Fin.sum_univ_four, b, c]; norm_num

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- One RK4 step for `Y' = A Y`. -/
def step (A Y : 𝔸) (h : ℝ) : 𝔸 :=
  let k1 := A*Y
  let k2 := A*(Y+(h/2)•k1)
  let k3 := A*(Y+(h/2)•k2)
  let k4 := A*(Y+h•k3)
  Y+(h/6)•(k1+2•k2+2•k3+k4)

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
/-- For a linear field the step is the degree-four Taylor polynomial of `exp(hA)`. -/
theorem linear_step (A Y : 𝔸) (h : ℝ) :
    step A Y h = (∑ n ∈ range 5, ((n.factorial : ℝ)⁻¹) • (h • A)^n)*Y := by
  simp only [step, sum_range_succ, sum_range_zero, Nat.factorial, Nat.cast_one, inv_one,
    one_smul, pow_zero, pow_one, zero_add, smul_pow]
  simp only [add_mul, smul_mul_assoc, mul_add, mul_smul_comm, one_mul, pow_succ, pow_zero,
    one_mul, mul_assoc, two_smul, smul_add, smul_smul]
  push_cast
  module

omit [NormOneClass 𝔸] in
/-- The exact solution `exp(sA) Y` of `Y' = A Y`. -/
theorem exact_solves (A Y : 𝔸) (s : ℝ) :
    HasDerivAt (fun t : ℝ => exp (t • A)*Y) (A*(exp (s • A)*Y)) s := by
  have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A s).mul_const Y
  simpa [mul_assoc] using h

/-- Fourth-order local consistency for every linear field. -/
theorem linear_consistency (A Y : 𝔸) (h : ℝ) (hA : ‖h • A‖ ≤ 1) :
    ‖step A Y h-exp (h • A)*Y‖ ≤ ‖h • A‖^5*(6/(Nat.factorial 5*5))*‖Y‖ := by
  rw [linear_step, ← sub_mul]
  refine le_trans (norm_mul_le _ _) ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [norm_sub_rev]
  have htail := MatrixTransfer.taylor_tail_le (h • A) 5
  have hreal := Real.exp_bound (x := ‖h • A‖) (by rwa [abs_of_nonneg (norm_nonneg _)])
    (n := 5) (by norm_num)
  rw [abs_of_nonneg (norm_nonneg _)] at hreal
  have habs := le_abs_self (Real.exp ‖h • A‖-∑ m ∈ range 5, ‖h • A‖^m/m.factorial)
  push_cast at hreal ⊢
  linarith

end BlackHole.RK4Order
