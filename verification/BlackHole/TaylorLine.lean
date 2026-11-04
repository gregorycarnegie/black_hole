module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Multivariate Taylor expansion along a segment (groundwork for N1).

For `f : E → F` of class `C⁴`, `taylor_line` bounds
`f(y + w) - Σ_{k<4} Dᵏf(y)(w,…,w)/k!` by `M‖w‖⁴/6` when `‖D⁴f‖ ≤ M` on the
segment. It reduces to the one-variable Taylor theorem for
`t ↦ f(y + t•w)`, whose derivatives `line_iteratedDeriv` identifies. The RK4
consistency proof expands each stage with this lemma. -/

@[expose] public section
noncomputable section

open Set Finset Nat

namespace BlackHole.TaylorLine

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Derivatives of `f` along the line `t ↦ y + t•w`. -/
theorem line_iteratedDeriv {n : ℕ} {f : E → F} (hf : ContDiff ℝ n f) (y w : E) {k : ℕ}
    (hk : k ≤ n) (t : ℝ) :
    iteratedDeriv k (fun s : ℝ => f (y+s • w)) t =
      iteratedFDeriv ℝ k f (y+t • w) (fun _ => w) := by
  set L : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) w
  have hL : ∀ s : ℝ, L s = s • w := fun s => by simp [L]
  have hshift : ContDiff ℝ n (fun z : E => f (y+z)) :=
    hf.comp (by fun_prop)
  have hcomp : (fun s : ℝ => f (y+s • w)) = (fun z : E => f (y+z)) ∘ L := by
    funext s; simp [hL]
  rw [hcomp, iteratedDeriv_eq_iteratedFDeriv,
    ContinuousLinearMap.iteratedFDeriv_comp_right L hshift t (by exact_mod_cast hk)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hL, one_smul]
  rw [iteratedFDeriv_comp_add_left]

/-- Taylor's theorem along a segment, to third order with a fourth-derivative
    remainder. -/
theorem taylor_line {f : E → F} (hf : ContDiff ℝ 4 f) (y w : E) (M : ℝ)
    (hM : ∀ t ∈ Icc (0:ℝ) 1, ‖iteratedFDeriv ℝ 4 f (y+t • w)‖ ≤ M) :
    ‖f (y+w)-∑ k ∈ range 4, ((k ! : ℝ)⁻¹) • iteratedFDeriv ℝ k f y (fun _ => w)‖ ≤
      M*‖w‖^4/6 := by
  set g : ℝ → F := fun s => f (y+s • w)
  have hg : ContDiff ℝ 4 g :=
    hf.comp (by fun_prop)
  have huniq : UniqueDiffOn ℝ (Icc (0:ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have hderiv : ∀ k ≤ 4, ∀ t ∈ Icc (0:ℝ) 1,
      iteratedDerivWithin k g (Icc 0 1) t = iteratedFDeriv ℝ k f (y+t • w) (fun _ => w) := by
    intro k hk t ht
    rw [iteratedDerivWithin_eq_iteratedDeriv huniq
      ((hg.of_le (by exact_mod_cast hk)).contDiffAt) ht]
    exact line_iteratedDeriv hf y w hk t
  have hbound : ∀ t ∈ Icc (0:ℝ) 1, ‖iteratedDerivWithin (3+1) g (Icc 0 1) t‖ ≤ M*‖w‖^4 := by
    intro t ht
    rw [hderiv 4 le_rfl t ht]
    calc ‖iteratedFDeriv ℝ 4 f (y+t • w) (fun _ => w)‖
        ≤ ‖iteratedFDeriv ℝ 4 f (y+t • w)‖*∏ _i : Fin 4, ‖w‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ M*‖w‖^4 := by
          rw [prod_const, Finset.card_univ, Fintype.card_fin]
          exact mul_le_mul_of_nonneg_right (hM t ht) (by positivity)
  have h := taylor_mean_remainder_bound (f := g) (n := 3) (a := 0) (b := 1) (x := 1)
    zero_le_one hg.contDiffOn (right_mem_Icc.mpr zero_le_one) hbound
  rw [taylor_within_apply] at h
  have hsum : ∑ k ∈ range (3+1), ((k ! : ℝ)⁻¹*(1-0)^k) • iteratedDerivWithin k g (Icc 0 1) 0 =
      ∑ k ∈ range 4, ((k ! : ℝ)⁻¹) • iteratedFDeriv ℝ k f y (fun _ => w) := by
    apply sum_congr rfl
    intro k hk
    have hk4 : k ≤ 4 := by simp at hk; omega
    rw [hderiv k hk4 0 (left_mem_Icc.mpr zero_le_one)]
    simp
  rw [hsum] at h
  have hg1 : g 1 = f (y+w) := by simp [g]
  rw [hg1] at h
  calc _ ≤ M*‖w‖^4*(1-0)^(3+1)/3 ! := h
    _ = M*‖w‖^4/6 := by norm_num [Nat.factorial]

end BlackHole.TaylorLine
