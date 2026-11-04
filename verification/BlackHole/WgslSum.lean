module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Reassociation-independent summation error (obligation F2).

WGSL permits an implementation to reassociate floating-point expressions
(`(a + b) + c` may become `a + (b + c)`), to fuse operations when at least as
accurate, and to flush subnormal inputs and outputs to zero. A `dot` product
inherits its accuracy from the sum of its componentwise products, so a WGSL
sum of `n` rounded terms may be evaluated as any binary tree over its terms.

`SumTree.error` bounds every such tree at once: if each leaf approximates its
exact term with error `≤ u|t| + η`, and each internal addition is rounded with
the same model, the total error is at most `((1+u)^n - 1)·Σ|t| + (2n-1)(1+u)^n η`,
where `n` is the number of leaves. The bound depends only on `n` and `Σ|t|`,
not on the tree. -/

@[expose] public section
noncomputable section

namespace BlackHole.Wgsl

/-- A binary summation tree; leaves carry their exact term. -/
inductive SumTree
  | leaf (t : ℝ)
  | node (l r : SumTree)

namespace SumTree

def exact : SumTree → ℝ
  | leaf t => t
  | node l r => exact l+exact r

def absSum : SumTree → ℝ
  | leaf t => |t|
  | node l r => absSum l+absSum r

def leaves : SumTree → ℕ
  | leaf _ => 1
  | node l r => leaves l+leaves r

lemma leaves_pos : ∀ T : SumTree, 1 ≤ T.leaves
  | leaf _ => le_rfl
  | node l _ => le_trans (leaves_pos l) (Nat.le_add_right _ _)

lemma absSum_nonneg : ∀ T : SumTree, 0 ≤ T.absSum
  | leaf t => abs_nonneg t
  | node l r => add_nonneg (absSum_nonneg l) (absSum_nonneg r)

lemma abs_exact_le : ∀ T : SumTree, |T.exact| ≤ T.absSum
  | leaf _ => le_rfl
  | node l r => le_trans (abs_add_le _ _) (add_le_add (abs_exact_le l) (abs_exact_le r))

/-- `T.Computes u η y`: some floating-point evaluation of `T` returns `y`. -/
def Computes (u η : ℝ) : SumTree → ℝ → Prop
  | leaf t, y => |y-t| ≤ u*|t|+η
  | node l r, y => ∃ yl yr, Computes u η l yl ∧ Computes u η r yr ∧
      |y-(yl+yr)| ≤ u*|yl+yr|+η

theorem error (u η : ℝ) (hu : 0 ≤ u) (hη : 0 ≤ η) :
    ∀ (T : SumTree) (y : ℝ), T.Computes u η y →
      |y-T.exact| ≤ ((1+u)^T.leaves-1)*T.absSum+(2*(T.leaves : ℝ)-1)*(1+u)^T.leaves*η
  | leaf t, y, h => by
    simp only [Computes, exact, absSum, leaves] at *
    simp only [pow_one, Nat.cast_one]
    nlinarith
  | node l r, y, h => by
    obtain ⟨yl, yr, hl, hr, hy⟩ := h
    have el := error u η hu hη l yl hl
    have er := error u η hu hη r yr hr
    simp only [exact, absSum, leaves] at *
    set nl := l.leaves
    set nr := r.leaves
    set Al := l.absSum
    set Ar := r.absSum
    have hAl := absSum_nonneg l
    have hAr := absSum_nonneg r
    have hnl : 1 ≤ nl := leaves_pos l
    have hnr : 1 ≤ nr := leaves_pos r
    have hgl : 1 ≤ (1+u)^nl := one_le_pow₀ (by linarith)
    have hgr : 1 ≤ (1+u)^nr := one_le_pow₀ (by linarith)
    -- Growth factors: (1+u)^nl·(1+u) ≤ (1+u)^(nl+nr), and similarly for nr.
    have hsplit : (1+u)^(nl+nr) = (1+u)^nl*(1+u)^nr := pow_add _ _ _
    have hl1 : (1+u)^nl*(1+u) ≤ (1+u)^(nl+nr) := by
      rw [hsplit]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc 1+u = (1+u)^1 := (pow_one _).symm
        _ ≤ (1+u)^nr := pow_le_pow_right₀ (by linarith) hnr
    have hr1 : (1+u)^nr*(1+u) ≤ (1+u)^(nl+nr) := by
      rw [hsplit, mul_comm ((1+u)^nl)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc 1+u = (1+u)^1 := (pow_one _).symm
        _ ≤ (1+u)^nl := pow_le_pow_right₀ (by linarith) hnl
    have hle : (1+u)^nl ≤ (1+u)^(nl+nr) := pow_le_pow_right₀ (by linarith) (by omega)
    have hre : (1+u)^nr ≤ (1+u)^(nl+nr) := pow_le_pow_right₀ (by linarith) (by omega)
    set El := ((1+u)^nl-1)*Al+(2*(nl : ℝ)-1)*(1+u)^nl*η
    set Er := ((1+u)^nr-1)*Ar+(2*(nr : ℝ)-1)*(1+u)^nr*η
    have hsum : |yl+yr| ≤ Al+Ar+El+Er := by
      have h1 := abs_exact_le l
      have h2 := abs_exact_le r
      have h3 : |yl| ≤ |l.exact|+El := by
        have := abs_sub_abs_le_abs_sub yl l.exact; linarith
      have h4 : |yr| ≤ |r.exact|+Er := by
        have := abs_sub_abs_le_abs_sub yr r.exact; linarith
      linarith [abs_add_le yl yr]
    have htri : |y-(l.exact+r.exact)| ≤ |y-(yl+yr)|+|yl-l.exact|+|yr-r.exact| := by
      calc |y-(l.exact+r.exact)| = |(y-(yl+yr))+(yl-l.exact)+(yr-r.exact)| := by ring_nf
        _ ≤ _ := abs_add_three _ _ _
    -- Collect: u·|yl+yr| + η + El + Er ≤ target.
    have hmain : u*(Al+Ar+El+Er)+η+El+Er ≤
        ((1+u)^(nl+nr)-1)*(Al+Ar)+(2*((nl+nr : ℕ) : ℝ)-1)*(1+u)^(nl+nr)*η := by
      have e1 : u*(Al+Ar+El+Er)+El+Er = (1+u)*(El+Er)+u*(Al+Ar) := by ring
      have hnl' : (1:ℝ) ≤ nl := by exact_mod_cast hnl
      have hnr' : (1:ℝ) ≤ nr := by exact_mod_cast hnr
      have e2 : (1+u)*El ≤ ((1+u)^(nl+nr)-(1+u))*Al+(2*(nl : ℝ)-1)*(1+u)^(nl+nr)*η := by
        have : (1+u)*El = ((1+u)^nl*(1+u)-(1+u))*Al+(2*(nl : ℝ)-1)*((1+u)^nl*(1+u))*η := by
          ring
        rw [this]
        have h1 : ((1+u)^nl*(1+u)-(1+u))*Al ≤ ((1+u)^(nl+nr)-(1+u))*Al :=
          mul_le_mul_of_nonneg_right (by linarith) hAl
        have h2 : (2*(nl : ℝ)-1)*((1+u)^nl*(1+u))*η ≤ (2*(nl : ℝ)-1)*(1+u)^(nl+nr)*η :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl1 (by linarith)) hη
        linarith
      have e3 : (1+u)*Er ≤ ((1+u)^(nl+nr)-(1+u))*Ar+(2*(nr : ℝ)-1)*(1+u)^(nl+nr)*η := by
        have : (1+u)*Er = ((1+u)^nr*(1+u)-(1+u))*Ar+(2*(nr : ℝ)-1)*((1+u)^nr*(1+u))*η := by
          ring
        rw [this]
        have h1 : ((1+u)^nr*(1+u)-(1+u))*Ar ≤ ((1+u)^(nl+nr)-(1+u))*Ar :=
          mul_le_mul_of_nonneg_right (by linarith) hAr
        have h2 : (2*(nr : ℝ)-1)*((1+u)^nr*(1+u))*η ≤ (2*(nr : ℝ)-1)*(1+u)^(nl+nr)*η :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr1 (by linarith)) hη
        linarith
      have e4 : η ≤ (1+u)^(nl+nr)*η := by
        have : 1 ≤ (1+u)^(nl+nr) := one_le_pow₀ (by linarith)
        nlinarith
      push_cast
      have e6 : (2*((nl : ℝ)+nr)-1)*(1+u)^(nl+nr)*η =
          (2*(nl : ℝ)-1)*(1+u)^(nl+nr)*η+(2*(nr : ℝ)-1)*(1+u)^(nl+nr)*η+(1+u)^(nl+nr)*η := by
        ring
      rw [e6]
      linarith [e1, e2, e3, e4]
    calc |y-(l.exact+r.exact)| ≤ |y-(yl+yr)|+|yl-l.exact|+|yr-r.exact| := htri
      _ ≤ (u*|yl+yr|+η)+El+Er := by linarith
      _ ≤ u*(Al+Ar+El+Er)+η+El+Er := by nlinarith
      _ ≤ _ := hmain

end SumTree

end BlackHole.Wgsl
