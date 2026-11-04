module

public import BlackHole.RadialRK4
public import BlackHole.Numerics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section

namespace BlackHole.AdaptiveStep

/-- The production controller compares the full step with two half steps.
    This is an estimator, not a certified enclosure of the exact solution. -/
def estimate (coarse fine : ℝ) : ℝ := |fine-coarse|/15

/-- The factor 15 is exact when halving scales the leading RK4 error by 1/16. -/
theorem leading_error_identity (exact defect : ℝ) :
    ((exact+defect)-(exact+16*defect))/15 = -defect := by ring

/-- Higher-order defects must be bounded separately from the measured difference. -/
theorem fine_error_bound (coarse fine exact remainder : ℝ)
    (hdefect : |(fine-exact)-(coarse-exact)/16| ≤ remainder) :
    |fine-exact| ≤ estimate coarse fine + (16/15 : ℝ)*remainder := by
  have hid : fine-exact = (coarse-fine)/15 +
      (16/15 : ℝ)*((fine-exact)-(coarse-exact)/16) := by ring
  calc
    _ = |(coarse-fine)/15+(16/15 : ℝ)*((fine-exact)-(coarse-exact)/16)| := congrArg abs hid
    _ ≤ |(coarse-fine)/15| + |(16/15 : ℝ)*((fine-exact)-(coarse-exact)/16)| := abs_add_le _ _
    _ ≤ estimate coarse fine+(16/15 : ℝ)*remainder := by
      rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ)<15),abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ)<16/15),abs_sub_comm coarse fine]
      have hb := mul_le_mul_of_nonneg_left hdefect (show (0 : Real) <= 16/15 by norm_num)
      unfold estimate
      linarith

/-- Variable step sizes, rounding and local defects enter the same error budget.
    This theorem does not assume the estimator bounds any of these terms. -/
theorem variable_error_budget (error growth defect budget : ℕ → ℝ)
    (hzero : error 0 ≤ budget 0) (hgrowth : ∀ n, 0 ≤ growth n)
    (hstep : ∀ n, error (n+1) ≤ growth n*error n+defect n)
    (hbudget : ∀ n, growth n*budget n+defect n ≤ budget (n+1)) :
    ∀ n, error n ≤ budget n := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
    have h := mul_le_mul_of_nonneg_left ih (hgrowth n)
    linarith [hstep n, hbudget n]

/-- A signed event is classified only when the complete certified enclosure is
    strictly on one side; a sampled step endpoint cannot supply this hypothesis. -/
theorem separated_event (exact approx radius boundary : ℝ)
    (henclosure : |exact-approx| ≤ radius) :
    (approx+radius < boundary → exact < boundary) ∧
      (boundary < approx-radius → boundary < exact) := by
  obtain ⟨hl,hu⟩ := abs_le.mp henclosure
  constructor <;> intro h <;> linarith

end BlackHole.AdaptiveStep

namespace BlackHole.RadialRK4

def doubledStep (s : ℚ × ℚ) (h : ℚ) : ℚ × ℚ := step (step s (h/2)) (h/2)

def scaledDifference (coarse fine : ℚ × ℚ) : ℚ :=
  max (|fine.1-coarse.1| / max 1 (max |coarse.1| |fine.1|))
    (|fine.2-coarse.2| / max 1 (max |coarse.2| |fine.2|)) / 15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The new position/momentum estimator rejects the old residual-only counterexample. -/
theorem doubling_rejects_old_step :
    (1/20000000 : ℚ) < scaledDifference (step (4,-3) (6/25)) (doubledStep (4,-3) (6/25)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Its first halving meets the estimator and exact analytic endpoint targets
    for this radial example; this is finite coverage, not a general error theorem. -/
theorem halved_step_meets_radial_target :
    let fine := doubledStep (4,-3) (3/25)
    let exact_r : ℚ := 4-3/25
    let exact_p : ℚ := -(exact_r+2)/(exact_r-2)
    scaledDifference (step (4,-3) (3/25)) fine ≤ (1/20000000 : ℚ) ∧
      |fine.1-exact_r| ≤ exact_r/1000000 ∧
      |fine.2-exact_p| ≤ |exact_p|/1000000 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Even the accepted refined step needs a nonzero null-error budget. -/
theorem doubled_step_not_exactly_null :
    constraint (doubledStep (4,-3) (3/25)) ≠ 0 := by
  decide +kernel

end BlackHole.RadialRK4
