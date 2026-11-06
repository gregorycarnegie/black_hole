module

public import BlackHole.WgslPlasma

/-! Domains on which the `Safe` conditions of WGSL kernel bounds hold
(obligation F2).

`heatmap_color` has no division, root or branch, so its bound holds for every
input and error allowance (`heatmap_safe`). `tonemap` divides by
`x(2.43x+0.59)+0.14` with `x` clamped to `[0, 10⁴]`; that denominator is at
least `0.14`, and its running bound stays below it whenever the input error is
at most `1/10` (`tonemap_safe`). Kernels that branch on computed values
(`polarization_color`, `sample_plasma`, `spatial_unit`) cannot satisfy `Safe`
near their thresholds, where an arbitrarily small error can change the branch
and so the result. -/

@[expose] public section
noncomputable section

namespace BlackHole.WgslSafe
open Wgsl WgslExpr GExpr WgslPlasma

theorem heatmap_safe (i : Fin 3) (v E : ℕ → ℝ) : (heatmap i).Safe v E := by
  fin_cases i <;> simp [heatmap,clamp,Safe,c]

/-- `heatmap_color` is within its running bound for every input. -/
theorem heatmap_error_all (i : Fin 3) (v w E : ℕ → ℝ) (hw : ∀ k, |w k-v k| ≤ E k) (y : ℝ)
    (hy : (heatmap i).Computes w y) : |y-(heatmap i).exact v| ≤ (heatmap i).bound v E :=
  heatmap_error i v w E hw y (heatmap_safe i v E) hy

theorem tonemap_safe (v E : ℕ → ℝ) (hE0 : 0 ≤ E 0) (hE : E 0 ≤ 1/10) : tonemap.Safe v E := by
  simp only [tonemap,clamp,Safe,bound,exact,c,true_and,and_true,zero_mul,mul_zero,
    add_zero,max_eq_left hE0]
  push_cast
  have hX0 : 0 ≤ min (max (v 0) 0) 10000 := le_min (le_max_right _ _) (by norm_num)
  have hX1 : min (max (v 0) 0) 10000 ≤ 10000 := min_le_right _ _
  generalize min (max (v 0) 0) 10000 = X at hX0 hX1 ⊢
  generalize E 0 = e at hE0 hE ⊢
  have hU : WgslPoly.U = 5/2^24 := by unfold WgslPoly.U u; norm_num
  have hη : η = 1/2^126 := rfl
  rw [hU,hη]
  rw [abs_of_nonneg hX0,abs_of_nonneg (by positivity : (0:ℝ) ≤ 10192159/4194304*X),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ 10192159/4194304*X+9898557/16777216),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ X*(10192159/4194304*X+9898557/16777216)+9395241/67108864)]
  norm_num
  have hs : |10192159/4194304*X+9898557/16777216| = 10192159/4194304*X+9898557/16777216 :=
    abs_of_nonneg (by positivity)
  rw [abs_of_nonneg hX0,hs]
  have hXX := mul_nonneg hX0 hX0
  have hXe := mul_nonneg hX0 hE0
  have hee := mul_nonneg hE0 hE0
  have hXXe := mul_nonneg hXX hE0
  have hXee := mul_nonneg hXe hE0
  refine ⟨?_,?_,?_⟩ <;> nlinarith [mul_le_mul_of_nonneg_left hE hX0, mul_le_mul_of_nonneg_left hE hXX,
    mul_le_mul_of_nonneg_left hX1 hX0, mul_le_mul_of_nonneg_left hX1 hXX,
    mul_le_mul_of_nonneg_left hE hE0, mul_le_mul_of_nonneg_left hX1 hXe]

/-- `tonemap` is within its running bound for every input whose error is at
most `1/10`. -/
theorem tonemap_error_all (v w E : ℕ → ℝ) (hw : ∀ k, |w k-v k| ≤ E k) (hE : E 0 ≤ 1/10) (y : ℝ)
    (hy : tonemap.Computes w y) : |y-tonemap.exact v| ≤ tonemap.bound v E :=
  tonemap_error v w E hw y (tonemap_safe v E ((abs_nonneg _).trans (hw 0)) hE) hy

end BlackHole.WgslSafe
