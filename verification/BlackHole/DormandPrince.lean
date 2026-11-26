module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! The Dormand–Prince 5(4) tableau of the opt-in CUDA controller
(`advance_ray_dp45`, checklist P1.1/P1.1b).

* `order_five`: the propagated weights `b` satisfy all seventeen rooted-tree
  order conditions up to order five; `not_order_six` shows the order is exactly five.
* `embedded_order_four`: the embedded weights `bhat` satisfy the eight conditions
  up to order four, and `embedded_not_order_five` shows they stop there.
* `fsal`: the last stage row equals `b`, so the seventh stage is the derivative at
  the new point. The kernel evaluates it there, so the error estimate needs no
  extra metric evaluation.
* `error_weights`: `e = b - bhat`, the coefficients the kernel applies to the
  stages to form the error estimate directly.

`tests/dormand_prince_tableau.rs` checks that the `DP_A`, `DP_B` and `DP_E`
literals in `tools/cuda/kernels.rs` are these rationals. This file covers the
exact-real tableau only; the controller's binary32 execution and acceptance rule
are not certified (obligation N3 and the P1.6 unresolved band). -/

@[expose] public section

open Finset

namespace BlackHole.DormandPrince

/-- Stage nodes, stage matrix, fifth-order weights, fourth-order weights. -/
def c : Fin 7 → ℚ := ![0, 1/5, 3/10, 4/5, 8/9, 1, 1]
def a : Fin 7 → Fin 7 → ℚ := ![
  ![0, 0, 0, 0, 0, 0, 0],
  ![1/5, 0, 0, 0, 0, 0, 0],
  ![3/40, 9/40, 0, 0, 0, 0, 0],
  ![44/45, -56/15, 32/9, 0, 0, 0, 0],
  ![19372/6561, -25360/2187, 64448/6561, -212/729, 0, 0, 0],
  ![9017/3168, -355/33, 46732/5247, 49/176, -5103/18656, 0, 0],
  ![35/384, 0, 500/1113, 125/192, -2187/6784, 11/84, 0]]
def b : Fin 7 → ℚ := ![35/384, 0, 500/1113, 125/192, -2187/6784, 11/84, 0]
def bhat : Fin 7 → ℚ :=
  ![5179/57600, 0, 7571/16695, 393/640, -92097/339200, 187/2100, 1/40]
/-- Error weights as the kernel writes them. -/
def e : Fin 7 → ℚ := ![71/57600, 0, -71/16695, 71/1920, -17253/339200, 22/525, -1/40]

/-- `(A v)ᵢ = Σⱼ aᵢⱼ vⱼ`. -/
def av (v : Fin 7 → ℚ) (i : Fin 7) : ℚ := ∑ j, a i j * v j

/-- `cᵏ` componentwise. -/
def cp (k : ℕ) (i : Fin 7) : ℚ := c i ^ k

/-- The quadrature conditions and the order conditions of trees with a single branch
point at the root, in terms of weights `w`. -/
def order_four_conditions (w : Fin 7 → ℚ) : Prop :=
  (∑ i, w i) = 1 ∧
  (∑ i, w i * c i) = 1/2 ∧
  (∑ i, w i * cp 2 i) = 1/3 ∧
  (∑ i, w i * av c i) = 1/6 ∧
  (∑ i, w i * cp 3 i) = 1/4 ∧
  (∑ i, w i * c i * av c i) = 1/8 ∧
  (∑ i, w i * av (cp 2) i) = 1/12 ∧
  (∑ i, w i * av (av c) i) = 1/24

theorem row_sums : ∀ i, c i = ∑ j, a i j := by
  intro i
  fin_cases i <;> simp [Fin.sum_univ_seven, c, a] <;> norm_num

theorem fsal : a 6 = b := by
  funext j
  fin_cases j <;> rfl

theorem error_weights : e = b - bhat := by
  funext i
  fin_cases i <;> simp [e, b, bhat] <;> norm_num

theorem order_five :
    order_four_conditions b ∧
    (∑ i, b i * cp 4 i) = 1/5 ∧
    (∑ i, b i * cp 2 i * av c i) = 1/10 ∧
    (∑ i, b i * c i * av (cp 2) i) = 1/15 ∧
    (∑ i, b i * c i * av (av c) i) = 1/30 ∧
    (∑ i, b i * av c i ^ 2) = 1/20 ∧
    (∑ i, b i * av (cp 3) i) = 1/20 ∧
    (∑ i, b i * av (fun j => c j * av c j) i) = 1/40 ∧
    (∑ i, b i * av (av (cp 2)) i) = 1/60 ∧
    (∑ i, b i * av (av (av c)) i) = 1/120 := by
  simp only [order_four_conditions, av, cp, Fin.sum_univ_seven, a, b, c]
  norm_num

/-- The order-six quadrature condition fails. -/
theorem not_order_six : (∑ i, b i * cp 5 i) ≠ 1/6 := by
  simp only [cp, Fin.sum_univ_seven, b, c]
  norm_num

theorem embedded_order_four : order_four_conditions bhat := by
  simp only [order_four_conditions, av, cp, Fin.sum_univ_seven, a, bhat, c]
  norm_num

theorem embedded_not_order_five : (∑ i, bhat i * cp 4 i) ≠ 1/5 := by
  simp only [cp, Fin.sum_univ_seven, bhat, c]
  norm_num

end BlackHole.DormandPrince
