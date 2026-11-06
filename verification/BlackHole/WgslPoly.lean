module

public import BlackHole.WgslKerrRadius
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! All-input error bounds for WGSL polynomial programs (obligation F2).

A program built from inputs, exact constants, `+ - *`, negation and division
by an exact nonzero constant is evaluated under the WGSL f32 model: every
operation has relative error at most `U` (here `U = 5u`, which covers the
2.5 ULP division and the correctly rounded `+ - *`) and an absolute
flush-to-zero term `η`. Inputs may themselves carry errors from earlier
kernels, described by a magnitude bound `α i ≥ |v i|` and an operation count
`k i`.

`error` proves `|y - exact| ≤ ((1+U)^N - 1)·A` for every input and every
admissible rounding, where `N` counts operations and `A` is the absolute
evaluation with `η/U` added at each rounded node. Both `N` and `A` are
unchanged by the reassociation of sums and products that WGSL permits, and
fusion is covered because a fused result satisfies the same per-operation
model. -/

@[expose] public section
noncomputable section

namespace BlackHole.WgslPoly
open Wgsl

/-- Per-operation relative error bound covering every arithmetic case. -/
def U : ℝ := 5*u

lemma U_pos : 0 < U := by unfold U; have := u_pos; positivity

def Γ (n : ℕ) : ℝ := (1+U)^n-1

lemma Γ_nonneg (n : ℕ) : 0 ≤ Γ n := by
  unfold Γ; have := U_pos; have : 1 ≤ (1+U)^n := one_le_pow₀ (by linarith); linarith

lemma Γ_succ (n : ℕ) : Γ (n+1) = (1+U)*Γ n+U := by unfold Γ; ring

lemma Γ_mono {m n : ℕ} (h : m ≤ n) : Γ m ≤ Γ n := by
  unfold Γ; have := U_pos
  have := pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ 1+U) h
  linarith

lemma Γ_add (m n : ℕ) : (1+Γ m)*(1+Γ n) = 1+Γ (m+n) := by unfold Γ; ring

/-- `(1+U)^n - 1 ≤ nU/(1-nU)` while `nU < 1`. -/
lemma Γ_le (n : ℕ) (h : (n:ℝ)*U < 1) : Γ n ≤ (n*U)/(1-n*U) := by
  have hU := U_pos
  have h1 : (1+U)^n ≤ Real.exp (n*U) := by
    calc (1+U)^n ≤ (Real.exp U)^n :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp U]) n
      _ = Real.exp (n*U) := by rw [← Real.exp_nat_mul]
  have h2 : Real.exp (n*U)*(1-n*U) ≤ 1 := by
    have e1 := Real.add_one_le_exp (-(n*U))
    have e2 : Real.exp (n*U)*Real.exp (-(n*U)) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (n*U)]
  have hd : 0 < 1-n*U := by linarith
  unfold Γ
  rw [le_div_iff₀ hd]
  nlinarith [mul_le_mul_of_nonneg_right h1 hd.le]

inductive PExpr
  | input (i : ℕ)
  | const (c : ℝ)
  | add (a b : PExpr)
  | sub (a b : PExpr)
  | mul (a b : PExpr)
  | neg (a : PExpr)
  | divc (a : PExpr) (c : ℝ)

namespace PExpr

def exact (v : ℕ → ℝ) : PExpr → ℝ
  | input i => v i
  | const c => c
  | add a b => exact v a+exact v b
  | sub a b => exact v a-exact v b
  | mul a b => exact v a*exact v b
  | neg a => -exact v a
  | divc a c => exact v a/c

/-- Operation count, including the operations behind each input. -/
def ops (k : ℕ → ℕ) : PExpr → ℕ
  | input i => k i
  | const _ => 0
  | add a b => ops k a+ops k b+1
  | sub a b => ops k a+ops k b+1
  | mul a b => ops k a+ops k b+1
  | neg a => ops k a
  | divc a _ => ops k a+1

/-- Absolute evaluation, with the flush allowance `η/U` per rounded node. -/
def absEval (α : ℕ → ℝ) : PExpr → ℝ
  | input i => α i
  | const c => |c|
  | add a b => absEval α a+absEval α b+η/U
  | sub a b => absEval α a+absEval α b+η/U
  | mul a b => absEval α a*absEval α b+η/U
  | neg a => absEval α a
  | divc a c => absEval α a/|c|+η/U

/-- Some WGSL evaluation of the program, from computed inputs `w`, returns `y`. -/
def Computes (w : ℕ → ℝ) : PExpr → ℝ → Prop
  | input i, y => y = w i
  | const c, y => y = c
  | add a b, y => ∃ ya yb, Computes w a ya ∧ Computes w b yb ∧ Rnd (ya+yb) y
  | sub a b, y => ∃ ya yb, Computes w a ya ∧ Computes w b yb ∧ Rnd (ya-yb) y
  | mul a b, y => ∃ ya yb, Computes w a ya ∧ Computes w b yb ∧ Rnd (ya*yb) y
  | neg a, y => ∃ ya, Computes w a ya ∧ y = -ya
  | divc a c, y => ∃ ya, Computes w a ya ∧ DivSpec ya c y

/-- Every constant divisor lies in WGSL's specified division range. -/
def DivcOk : PExpr → Prop
  | input _ => True
  | const _ => True
  | add a b => DivcOk a ∧ DivcOk b
  | sub a b => DivcOk a ∧ DivcOk b
  | mul a b => DivcOk a ∧ DivcOk b
  | neg a => DivcOk a
  | divc a c => DivcOk a ∧ 1/2^126 ≤ |c| ∧ |c| ≤ 2^126

lemma ηU_nonneg : 0 ≤ η/U := div_nonneg η_pos.le U_pos.le

lemma rnd_le {x y : ℝ} (h : Rnd x y) : |y-x| ≤ U*|x|+η := by
  unfold Rnd at h; unfold U; have := u_pos; nlinarith [abs_nonneg x]

theorem error (v w α : ℕ → ℝ) (k : ℕ → ℕ)
    (hα : ∀ i, |v i| ≤ α i) (hw : ∀ i, |w i-v i| ≤ Γ (k i)*α i) :
    ∀ (e : PExpr) (y : ℝ), DivcOk e → Computes w e y →
      |exact v e| ≤ absEval α e ∧ |y-exact v e| ≤ Γ (ops k e)*absEval α e
  | input i, y, hc, h => by
    simp only [Computes] at h; subst h
    exact ⟨hα i,hw i⟩
  | const c, y, hc, h => by
    simp only [Computes] at h; subst h
    simp [exact,absEval,ops,Γ]
  | add a b, y, hc, h => by
    obtain ⟨ya,yb,ha,hb,hy⟩ := h
    obtain ⟨ea,ra⟩ := error v w α k hα hw a ya hc.1 ha
    obtain ⟨eb,rb⟩ := error v w α k hα hw b yb hc.2 hb
    simp only [exact,absEval,ops]
    have hU := U_pos; have hη := η_pos
    set Aa := absEval α a; set Ab := absEval α b
    set n := ops k a+ops k b
    have hga : Γ (ops k a) ≤ Γ n := Γ_mono (Nat.le_add_right _ _)
    have hgb : Γ (ops k b) ≤ Γ n := Γ_mono (Nat.le_add_left _ _)
    have hAa : 0 ≤ Aa := (abs_nonneg _).trans ea
    have hAb : 0 ≤ Ab := (abs_nonneg _).trans eb
    have hra : |ya-exact v a| ≤ Γ n*Aa := ra.trans (mul_le_mul_of_nonneg_right hga hAa)
    have hrb : |yb-exact v b| ≤ Γ n*Ab := rb.trans (mul_le_mul_of_nonneg_right hgb hAb)
    have hgn := Γ_nonneg n
    have hηU : U*(η/U) = η := by field_simp
    refine ⟨(abs_add_le _ _).trans (by linarith [ηU_nonneg]),?_⟩
    have hsum : |ya+yb| ≤ (1+Γ n)*(Aa+Ab) := by
      have := abs_add_le ya yb
      have h1 := abs_sub_abs_le_abs_sub ya (exact v a)
      have h2 := abs_sub_abs_le_abs_sub yb (exact v b)
      nlinarith
    have hy' := rnd_le hy
    rw [Γ_succ]
    calc |y-(exact v a+exact v b)| ≤ |y-(ya+yb)|+|ya-exact v a|+|yb-exact v b| := by
          have := abs_sub_le y (ya+yb) (exact v a+exact v b)
          have := abs_add_le (ya-exact v a) (yb-exact v b)
          rw [show ya+yb-(exact v a+exact v b) = (ya-exact v a)+(yb-exact v b) by ring] at *
          linarith
      _ ≤ ((1+U)*Γ n+U)*(Aa+Ab+η/U) := by nlinarith [ηU_nonneg]
  | sub a b, y, hc, h => by
    obtain ⟨ya,yb,ha,hb,hy⟩ := h
    obtain ⟨ea,ra⟩ := error v w α k hα hw a ya hc.1 ha
    obtain ⟨eb,rb⟩ := error v w α k hα hw b yb hc.2 hb
    simp only [exact,absEval,ops]
    have hU := U_pos; have hη := η_pos
    set Aa := absEval α a; set Ab := absEval α b
    set n := ops k a+ops k b
    have hga : Γ (ops k a) ≤ Γ n := Γ_mono (Nat.le_add_right _ _)
    have hgb : Γ (ops k b) ≤ Γ n := Γ_mono (Nat.le_add_left _ _)
    have hAa : 0 ≤ Aa := (abs_nonneg _).trans ea
    have hAb : 0 ≤ Ab := (abs_nonneg _).trans eb
    have hra : |ya-exact v a| ≤ Γ n*Aa := ra.trans (mul_le_mul_of_nonneg_right hga hAa)
    have hrb : |yb-exact v b| ≤ Γ n*Ab := rb.trans (mul_le_mul_of_nonneg_right hgb hAb)
    have hgn := Γ_nonneg n
    have hηU : U*(η/U) = η := by field_simp
    refine ⟨(abs_sub _ _).trans (by linarith [ηU_nonneg]),?_⟩
    have hsum : |ya-yb| ≤ (1+Γ n)*(Aa+Ab) := by
      have := abs_sub ya yb
      have h1 := abs_sub_abs_le_abs_sub ya (exact v a)
      have h2 := abs_sub_abs_le_abs_sub yb (exact v b)
      nlinarith
    have hy' := rnd_le hy
    rw [Γ_succ]
    calc |y-(exact v a-exact v b)| ≤ |y-(ya-yb)|+|ya-exact v a|+|yb-exact v b| := by
          have := abs_sub_le y (ya-yb) (exact v a-exact v b)
          have := abs_sub (ya-exact v a) (yb-exact v b)
          rw [show ya-yb-(exact v a-exact v b) = (ya-exact v a)-(yb-exact v b) by ring] at *
          linarith
      _ ≤ ((1+U)*Γ n+U)*(Aa+Ab+η/U) := by nlinarith [ηU_nonneg]
  | mul a b, y, hc, h => by
    obtain ⟨ya,yb,ha,hb,hy⟩ := h
    obtain ⟨ea,ra⟩ := error v w α k hα hw a ya hc.1 ha
    obtain ⟨eb,rb⟩ := error v w α k hα hw b yb hc.2 hb
    simp only [exact,absEval,ops]
    have hU := U_pos; have hη := η_pos
    set Aa := absEval α a; set Ab := absEval α b
    set ga := Γ (ops k a); set gb := Γ (ops k b)
    have hAa : 0 ≤ Aa := (abs_nonneg _).trans ea
    have hAb : 0 ≤ Ab := (abs_nonneg _).trans eb
    have hga := Γ_nonneg (ops k a); have hgb := Γ_nonneg (ops k b)
    have hηU : U*(η/U) = η := by field_simp
    refine ⟨by rw [abs_mul]; nlinarith [abs_nonneg (exact v a),abs_nonneg (exact v b),ηU_nonneg],?_⟩
    have hya : |ya| ≤ (1+ga)*Aa := by
      have := abs_sub_abs_le_abs_sub ya (exact v a); nlinarith
    have hyb : |yb| ≤ (1+gb)*Ab := by
      have := abs_sub_abs_le_abs_sub yb (exact v b); nlinarith
    have hprod : |ya*yb-exact v a*exact v b| ≤ ((1+ga)*(1+gb)-1)*(Aa*Ab) := by
      rw [show ya*yb-exact v a*exact v b = (ya-exact v a)*yb+exact v a*(yb-exact v b) by ring]
      have h1 : |(ya-exact v a)*yb| ≤ ga*Aa*((1+gb)*Ab) := by
        rw [abs_mul]; exact mul_le_mul ra hyb (abs_nonneg _) (by positivity)
      have h2 : |exact v a*(yb-exact v b)| ≤ Aa*(gb*Ab) := by
        rw [abs_mul]; exact mul_le_mul ea rb (abs_nonneg _) hAa
      have := abs_add_le ((ya-exact v a)*yb) (exact v a*(yb-exact v b))
      nlinarith
    have hy' := rnd_le hy
    have hyy : |ya*yb| ≤ (1+ga)*(1+gb)*(Aa*Ab) := by
      rw [abs_mul]; nlinarith [abs_nonneg ya,abs_nonneg yb]
    have hcomb := Γ_add (ops k a) (ops k b)
    rw [Γ_succ]
    set n := ops k a+ops k b
    have hgn := Γ_nonneg n
    calc |y-exact v a*exact v b| ≤ |y-ya*yb|+|ya*yb-exact v a*exact v b| := abs_sub_le _ _ _
      _ ≤ ((1+U)*Γ n+U)*(Aa*Ab+η/U) := by
          have hAA : 0 ≤ Aa*Ab := mul_nonneg hAa hAb
          rw [show (1+ga)*(1+gb) = 1+Γ n from hcomb] at hprod hyy
          nlinarith [ηU_nonneg]
  | neg a, y, hc, h => by
    obtain ⟨ya,ha,rfl⟩ := h
    obtain ⟨ea,ra⟩ := error v w α k hα hw a ya hc ha
    simp only [exact,absEval,ops,abs_neg]
    refine ⟨ea,?_⟩
    rw [show -ya- -exact v a = -(ya-exact v a) by ring,abs_neg]
    exact ra
  | divc a c, y, hc, h => by
    obtain ⟨ya,ha,hy⟩ := h
    obtain ⟨ea,ra⟩ := error v w α k hα hw a ya hc.1 ha
    simp only [exact,absEval,ops]
    have hU := U_pos; have hη := η_pos
    set Aa := absEval α a
    set ga := Γ (ops k a)
    have hAa : 0 ≤ Aa := (abs_nonneg _).trans ea
    have hga := Γ_nonneg (ops k a)
    have hηU : U*(η/U) = η := by field_simp
    have hc0 : 0 < |c| := lt_of_lt_of_le (by norm_num) hc.2.1
    have hy := hy hc.2
    refine ⟨?_,?_⟩
    · rw [abs_div]
      have := div_le_div_of_nonneg_right ea hc0.le
      linarith [ηU_nonneg]
    · unfold Wgsl.Div at hy
      have hq : |ya/c-exact v a/c| ≤ ga*Aa/|c| := by
        rw [← sub_div,abs_div]; exact div_le_div_of_nonneg_right ra hc0.le
      have hyq : |ya/c| ≤ (1+ga)*Aa/|c| := by
        rw [abs_div]
        have := abs_sub_abs_le_abs_sub ya (exact v a)
        exact div_le_div_of_nonneg_right (by nlinarith) hc0.le
      have hdiv : 5*u = U := rfl
      rw [hdiv] at hy
      rw [Γ_succ]
      have hAc : 0 ≤ Aa/|c| := div_nonneg hAa hc0.le
      calc |y-exact v a/c| ≤ |y-ya/c|+|ya/c-exact v a/c| := abs_sub_le _ _ _
        _ ≤ ((1+U)*ga+U)*(Aa/|c|+η/U) := by
            rw [mul_div_assoc] at hq hyq
            nlinarith [ηU_nonneg]

end PExpr

end BlackHole.WgslPoly
