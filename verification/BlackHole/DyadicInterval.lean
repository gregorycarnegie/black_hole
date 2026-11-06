module
public import Mathlib.Data.Dyadic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith

/-! Checked finite interval arithmetic. Floating endpoints are only proposals:
the checker compares exact dyadic sums, products and squares. These theorems
do not require an error bound for a floating arithmetic operation or builtin. -/

@[expose] public section
namespace BlackHole.DyadicInterval
open Set

@[simp] theorem real_zero : (0:Dyadic).toReal = 0 := by norm_num [Dyadic.toReal]
@[simp] theorem real_one : (1:Dyadic).toReal = 1 := by
  change ((1:Dyadic).toRat:ℝ) = 1
  rw [show (1:Dyadic).toRat = (1:ℚ) by decide]
  norm_num

@[simp] theorem real_neg (a : Dyadic) : (-a).toReal = -a.toReal := by simp [Dyadic.toReal]

structure Bounds where
  lo : Dyadic
  hi : Dyadic

def Contains (b : Bounds) (x : ℝ) : Prop := x ∈ Icc b.lo.toReal b.hi.toReal

def negate (b : Bounds) : Bounds := ⟨-b.hi,-b.lo⟩

def addCheck (a b c : Bounds) : Bool :=
  decide (c.lo ≤ a.lo+b.lo ∧ a.hi+b.hi ≤ c.hi)

def mulCheck (a b c : Bounds) : Bool := decide (
  c.lo ≤ a.lo*b.lo ∧ a.lo*b.lo ≤ c.hi ∧
  c.lo ≤ a.lo*b.hi ∧ a.lo*b.hi ≤ c.hi ∧
  c.lo ≤ a.hi*b.lo ∧ a.hi*b.lo ≤ c.hi ∧
  c.lo ≤ a.hi*b.hi ∧ a.hi*b.hi ≤ c.hi)

def reciprocalCheck (a b : Bounds) : Bool := decide (
  (0 < a.lo ∧ b.lo*a.hi ≤ 1 ∧ 1 ≤ b.hi*a.lo) ∨
  (a.hi < 0 ∧ 1 ≤ b.lo*a.hi ∧ b.hi*a.lo ≤ 1))

def sqrtCheck (a b : Bounds) : Bool := decide (
  0 ≤ a.lo ∧ 0 ≤ b.lo ∧ b.lo ≤ b.hi ∧ b.lo*b.lo ≤ a.lo ∧ a.hi ≤ b.hi*b.hi)

def squareCheck (a b : Bounds) : Bool := decide (
  (0 ≤ a.lo ∧ b.lo ≤ a.lo*a.lo ∧ a.hi*a.hi ≤ b.hi) ∨
  (a.hi ≤ 0 ∧ b.lo ≤ a.hi*a.hi ∧ a.lo*a.lo ≤ b.hi) ∨
  (a.lo ≤ 0 ∧ 0 ≤ a.hi ∧ b.lo ≤ 0 ∧ a.lo*a.lo ≤ b.hi ∧ a.hi*a.hi ≤ b.hi))

def zeroCheck (a : Bounds) : Bool := decide (a.lo ≤ 0 ∧ 0 ≤ a.hi)

theorem zero_sound {a : Bounds} (h : zeroCheck a = true) : Contains a 0 := by
  have h' := of_decide_eq_true h
  exact ⟨by simpa using Dyadic.toReal_le_toReal.mpr h'.1,
    by simpa using Dyadic.toReal_le_toReal.mpr h'.2⟩

theorem add_sound {a b c : Bounds} {x y : ℝ}
    (hc : addCheck a b c = true) (hx : Contains a x) (hy : Contains b y) :
    Contains c (x+y) := by
  have h := of_decide_eq_true hc
  have hl := Dyadic.toReal_le_toReal.mpr h.1
  have hu := Dyadic.toReal_le_toReal.mpr h.2
  simp only [Dyadic.toReal_add] at hl hu
  exact ⟨hl.trans (add_le_add hx.1 hy.1), (add_le_add hx.2 hy.2).trans hu⟩

theorem neg_sound {b : Bounds} {x : ℝ} (hx : Contains b x) : Contains (negate b) (-x) := by
  exact ⟨by simpa [negate] using neg_le_neg hx.2, by simpa [negate] using neg_le_neg hx.1⟩

theorem sub_sound {a b c : Bounds} {x y : ℝ}
    (hc : addCheck a (negate b) c = true) (hx : Contains a x) (hy : Contains b y) :
    Contains c (x-y) := by simpa [sub_eq_add_neg] using add_sound hc hx (neg_sound hy)

/-- The accumulation loop used for sums and coefficient convolutions. -/
theorem sum_sound (term accum : ℕ → Bounds) (value : ℕ → ℝ) (N : ℕ)
    (hzero : Contains (accum 0) 0)
    (hstep : ∀ k < N, addCheck (accum k) (term k) (accum (k+1)) = true)
    (hterm : ∀ k < N, Contains (term k) (value k)) :
    Contains (accum N) (∑ k ∈ Finset.range N, value k) := by
  induction N with
  | zero => simpa using hzero
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact add_sound (hstep n (Nat.lt_succ_self n))
      (ih (fun k hk => hstep k (Nat.lt_succ_of_lt hk))
        (fun k hk => hterm k (Nat.lt_succ_of_lt hk))) (hterm n (Nat.lt_succ_self n))

private theorem linear_mem {a b x k l u : ℝ} (hx : x ∈ Icc a b)
    (ha : k*a ∈ Icc l u) (hb : k*b ∈ Icc l u) : k*x ∈ Icc l u := by
  by_cases hk : 0 ≤ k
  · exact ⟨ha.1.trans (mul_le_mul_of_nonneg_left hx.1 hk),
      (mul_le_mul_of_nonneg_left hx.2 hk).trans hb.2⟩
  · have hk' := le_of_not_ge hk
    exact ⟨hb.1.trans (mul_le_mul_of_nonpos_left hx.2 hk'),
      (mul_le_mul_of_nonpos_left hx.1 hk').trans ha.2⟩

theorem mul_sound {a b c : Bounds} {x y : ℝ}
    (hc : mulCheck a b c = true) (hx : Contains a x) (hy : Contains b y) :
    Contains c (x*y) := by
  have h := of_decide_eq_true hc
  have pair {u v : Dyadic} (hl : c.lo ≤ u*v) (hu : u*v ≤ c.hi) :
      u.toReal*v.toReal ∈ Icc c.lo.toReal c.hi.toReal := by
    exact ⟨by simpa using Dyadic.toReal_le_toReal.mpr hl,
      by simpa using Dyadic.toReal_le_toReal.mpr hu⟩
  have hlo := linear_mem hy (pair h.1 h.2.1) (pair h.2.2.1 h.2.2.2.1)
  have hhi := linear_mem hy (pair h.2.2.2.2.1 h.2.2.2.2.2.1)
    (pair h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2)
  simpa [Contains,mul_comm] using linear_mem hx (by simpa [mul_comm] using hlo)
    (by simpa [mul_comm] using hhi)

theorem reciprocal_sound {a b : Bounds} {x : ℝ}
    (hc : reciprocalCheck a b = true) (hx : Contains a x) : Contains b (1/x) := by
  rcases of_decide_eq_true hc with hp | hn
  · have ha : 0 < a.lo.toReal := by simpa using Dyadic.toReal_lt_toReal.mpr hp.1
    have hx0 : 0 < x := ha.trans_le hx.1
    have hb : 0 < a.hi.toReal := hx0.trans_le hx.2
    have hl : b.lo.toReal*a.hi.toReal ≤ 1 := by simpa using Dyadic.toReal_le_toReal.mpr hp.2.1
    have hu : 1 ≤ b.hi.toReal*a.lo.toReal := by simpa using Dyadic.toReal_le_toReal.mpr hp.2.2
    exact ⟨((le_div_iff₀ hb).mpr hl).trans (one_div_le_one_div_of_le hx0 hx.2),
      (one_div_le_one_div_of_le ha hx.1).trans ((div_le_iff₀ ha).mpr hu)⟩
  · have hb : a.hi.toReal < 0 := by simpa using Dyadic.toReal_lt_toReal.mpr hn.1
    have hx0 : x < 0 := hx.2.trans_lt hb
    have ha : a.lo.toReal < 0 := hx.1.trans_lt hx0
    have hl : 1 ≤ b.lo.toReal*a.hi.toReal := by simpa using Dyadic.toReal_le_toReal.mpr hn.2.1
    have hu : b.hi.toReal*a.lo.toReal ≤ 1 := by simpa using Dyadic.toReal_le_toReal.mpr hn.2.2
    exact ⟨((le_div_iff_of_neg hb).mpr hl).trans (one_div_le_one_div_of_neg_of_le hb hx.2),
      (one_div_le_one_div_of_neg_of_le hx0 hx.1).trans ((div_le_iff_of_neg ha).mpr hu)⟩

theorem reciprocal_nonzero {a b : Bounds} {x : ℝ}
    (hc : reciprocalCheck a b = true) (hx : Contains a x) : x ≠ 0 := by
  rcases of_decide_eq_true hc with hp | hn
  · have ha : 0 < a.lo.toReal := by simpa using Dyadic.toReal_lt_toReal.mpr hp.1
    exact ne_of_gt (ha.trans_le hx.1)
  · have ha : a.hi.toReal < 0 := by simpa using Dyadic.toReal_lt_toReal.mpr hn.1
    exact ne_of_lt (hx.2.trans_lt ha)

theorem sqrt_sound {a b : Bounds} {x : ℝ}
    (hc : sqrtCheck a b = true) (hx : Contains a x) : Contains b (Real.sqrt x) := by
  have h := of_decide_eq_true hc
  have ha : 0 ≤ a.lo.toReal := by simpa using Dyadic.toReal_le_toReal.mpr h.1
  have hb : 0 ≤ b.lo.toReal := by simpa using Dyadic.toReal_le_toReal.mpr h.2.1
  have horder := Dyadic.toReal_le_toReal.mpr h.2.2.1
  have hl : b.lo.toReal*b.lo.toReal ≤ a.lo.toReal := by
    simpa using Dyadic.toReal_le_toReal.mpr h.2.2.2.1
  have hu : a.hi.toReal ≤ b.hi.toReal*b.hi.toReal := by
    simpa using Dyadic.toReal_le_toReal.mpr h.2.2.2.2
  have hs := Real.sq_sqrt (ha.trans hx.1)
  have hp := Real.sqrt_nonneg x
  rcases hx with ⟨hxlo,hxhi⟩
  constructor <;> nlinarith

theorem square_sound {a b : Bounds} {x : ℝ}
    (hc : squareCheck a b = true) (hx : Contains a x) : Contains b (x*x) := by
  rcases hx with ⟨hxlo,hxhi⟩
  rcases of_decide_eq_true hc with hp | hn | hz
  · have h0 : 0 ≤ a.lo.toReal := by simpa using Dyadic.toReal_le_toReal.mpr hp.1
    have hl : b.lo.toReal ≤ a.lo.toReal*a.lo.toReal := by
      simpa using Dyadic.toReal_le_toReal.mpr hp.2.1
    have hu : a.hi.toReal*a.hi.toReal ≤ b.hi.toReal := by
      simpa using Dyadic.toReal_le_toReal.mpr hp.2.2
    constructor <;> nlinarith
  · have h0 : a.hi.toReal ≤ 0 := by simpa using Dyadic.toReal_le_toReal.mpr hn.1
    have hl : b.lo.toReal ≤ a.hi.toReal*a.hi.toReal := by
      simpa using Dyadic.toReal_le_toReal.mpr hn.2.1
    have hu : a.lo.toReal*a.lo.toReal ≤ b.hi.toReal := by
      simpa using Dyadic.toReal_le_toReal.mpr hn.2.2
    constructor <;> nlinarith
  · have hlo : a.lo.toReal ≤ 0 := by simpa using Dyadic.toReal_le_toReal.mpr hz.1
    have hhi : 0 ≤ a.hi.toReal := by simpa using Dyadic.toReal_le_toReal.mpr hz.2.1
    have hl : b.lo.toReal ≤ 0 := by simpa using Dyadic.toReal_le_toReal.mpr hz.2.2.1
    have hul : a.lo.toReal*a.lo.toReal ≤ b.hi.toReal := by
      simpa using Dyadic.toReal_le_toReal.mpr hz.2.2.2.1
    have huh : a.hi.toReal*a.hi.toReal ≤ b.hi.toReal := by
      simpa using Dyadic.toReal_le_toReal.mpr hz.2.2.2.2
    refine ⟨hl.trans (mul_self_nonneg x),?_⟩
    by_cases hx : 0 ≤ x <;> nlinarith

theorem refine_nonnegative {b : Bounds} {x : ℝ} (hx : Contains b x) (h0 : 0 ≤ x) :
    Contains ⟨max 0 b.lo,b.hi⟩ x := by
  by_cases hl : (0:Dyadic) ≤ b.lo
  · simpa [max_eq_right hl] using hx
  · have hl' : b.lo ≤ 0 := le_of_not_ge hl
    simpa [Contains,max_eq_left hl'] using And.intro h0 hx.2

end BlackHole.DyadicInterval
