module

public import BlackHole.WgslKerrRadius
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-! WGSL error bound for the production `sincos` (obligation F2).

WGSL bounds builtin f32 `sin`/`cos` only to an absolute error of 2⁻¹¹ and
only on [-π, π]. `geodesic.wesl` therefore evaluates them with correctly
rounded `+ - *` alone:

```
let k = round(x*TWO_OVER_PI);
let r = clamp((x-k*PIO2_HI)-k*PIO2_LO,-1.0,1.0);
let r2 = r*r;
let s = r*(1 + r2*(-1/3! + r2*(... + r2*(1/13!))));
let c = 1 + r2*(-1/2! + r2*(... + r2*(-1/14!)));
```

followed by the quadrant selection on `k mod 4`.

* `sin_poly_error`, `cos_poly_error`: the polynomials are within 10⁻¹² of
  `sin`, `cos` on `|r| ≤ 1`.
* `quadrant`: the selection is exact.
* `horner_error`: any WGSL evaluation of a Horner chain is within `10u` per
  coefficient, in the rounding model of `WgslKerrRadius` (which covers fusion).
* `sincos_error`: for every binary32 `|x| ≤ 2¹⁸` the result is within
  `128 u (1 + |x|)` of `(sin x, cos x)`, for any association of the reduction
  sum. -/

@[expose] public section
noncomputable section

open Finset

namespace BlackHole.Wgsl

/-! ### Horner chains -/

/-- Exact Horner evaluation `a₀ + y(a₁ + y(a₂ + …))`. -/
def hornerL : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: as, y => a+y*hornerL as y

/-- A WGSL evaluation of a Horner chain with binary32 coefficients `b`. -/
def HornerComp : List ℝ → ℝ → ℝ → Prop
  | [], _, _ => False
  | [b], _, h => h = b
  | b :: b' :: bs, y, h => ∃ t m, HornerComp (b' :: bs) y t ∧ Rnd (y*t) m ∧ Rnd (b+m) h

def absSum : List ℝ → ℝ
  | [] => 0
  | a :: as => |a|+absSum as

lemma absSum_nonneg : ∀ L : List ℝ, 0 ≤ absSum L
  | [] => le_rfl
  | a :: as => add_nonneg (abs_nonneg a) (absSum_nonneg as)

lemma hornerL_bound (y : ℝ) (hy : |y| ≤ 1001/1000) :
    ∀ L : List ℝ, |hornerL L y| ≤ absSum L*(1001/1000)^L.length
  | [] => by simp [hornerL, absSum]
  | a :: as => by
    have ih := hornerL_bound y hy as
    simp only [hornerL, absSum, List.length_cons, pow_succ]
    have h1 : 1 ≤ (1001/1000:ℝ)^as.length := one_le_pow₀ (by norm_num)
    have hA := absSum_nonneg as
    calc |a+y*hornerL as y| ≤ |a|+|y| *|hornerL as y| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |a| *((1001/1000)^as.length*(1001/1000))+
          (1001/1000)*(absSum as*(1001/1000)^as.length) := by
          gcongr
          · nlinarith [abs_nonneg a]
      _ = _ := by ring

/-- Error of a computed Horner chain. Coefficients satisfy `|a| ≤ 1`, their
    binary32 constants are rounded, the coefficient sum is at most 1.9 and
    the chain has at most ten terms. -/
theorem horner_error (y : ℝ) (hy : |y| ≤ 1001/1000) :
    ∀ (L B : List ℝ) (h : ℝ), List.Forall₂ (fun a b => Rnd a b ∧ |a| ≤ 1) L B →
      absSum L ≤ 19/10 → L.length ≤ 10 → HornerComp B y h →
      |h-hornerL L y| ≤ 10*u*L.length
  | [], _, _, hf, _, _, hc => by cases hf; simp [HornerComp] at hc
  | [a], B, h, hf, _, _, hc => by
    cases hf with
    | cons hab hrest =>
      cases hrest
      simp only [HornerComp] at hc
      subst hc
      unfold Rnd at hab
      simp only [hornerL, mul_zero, add_zero, List.length_singleton, Nat.cast_one, mul_one]
      have := η_pos; have := u_pos
      have : η ≤ u := by norm_num [u, η]
      nlinarith [hab.2, abs_nonneg a]
  | a :: a' :: as, B, h, hf, hsum, hlen, hc => by
    cases hf with
    | cons hab hrest =>
      rename_i b B'
      cases hrest with
      | cons hab' hrest' =>
        rename_i b' B''
        obtain ⟨t, m, ht, hm, hh⟩ := hc
        have hu := u_pos
        have hη := η_pos
        have hsum' : absSum (a' :: as) ≤ 19/10 := by
          simp only [absSum] at hsum ⊢; linarith [abs_nonneg a]
        have hlen' : (a' :: as).length ≤ 10 := by simp at hlen ⊢; omega
        have ih := horner_error y hy (a' :: as) (b' :: B'') t (List.Forall₂.cons hab' hrest')
          hsum' hlen' ht
        set H := hornerL (a' :: as) y
        set n := (a' :: as).length
        have hn : (n : ℝ) ≤ 9 := by
          have : n ≤ 9 := by simp [n] at hlen ⊢; omega
          exact_mod_cast this
        -- |H| ≤ 2 and |t| ≤ 3.
        have hH : |H| ≤ 2 := by
          have h1 := hornerL_bound y hy (a' :: as)
          have h2 : (1001/1000:ℝ)^n ≤ (1001/1000)^10 :=
            pow_le_pow_right₀ (by norm_num) (by simp [n] at hlen ⊢; omega)
          have h3 : absSum (a' :: as)*(1001/1000)^n ≤ 19/10*(1001/1000)^10 :=
            mul_le_mul hsum' h2 (by positivity) (by norm_num)
          have : (19/10:ℝ)*(1001/1000)^10 ≤ 2 := by norm_num
          linarith
        have he : 10*u*n ≤ 1/1000 := by
          have : 10*u*n ≤ 10*u*9 := by nlinarith
          have : 10*u*9 ≤ 1/1000 := by norm_num [u]
          linarith
        have ht3 : |t| ≤ 3 := by
          have := abs_sub_abs_le_abs_sub t H; linarith
        unfold Rnd at hab hm hh
        -- Error of the product, the constant and the sum.
        have hyt : |y*t| ≤ 1001/1000*3 := by
          rw [abs_mul]; exact mul_le_mul hy ht3 (abs_nonneg _) (by norm_num)
        have hp : |m-y*H| ≤ u*(1001/1000*3)+η+1001/1000*(10*u*n) := by
          have h1 : |y*t-y*H| ≤ 1001/1000*(10*u*n) := by
            rw [← mul_sub, abs_mul]; exact mul_le_mul hy ih (abs_nonneg _) (by norm_num)
          have h2 : u*|y*t| ≤ u*(1001/1000*3) := mul_le_mul_of_nonneg_left hyt hu.le
          calc |m-y*H| = |(m-y*t)+(y*t-y*H)| := by ring_nf
            _ ≤ _ := abs_add_le _ _
            _ ≤ _ := by linarith
        have hs : |b+m-(a+y*H)| ≤ (u*|a|+η)+(u*(1001/1000*3)+η+1001/1000*(10*u*n)) := by
          calc |b+m-(a+y*H)| = |(b-a)+(m-y*H)| := by ring_nf
            _ ≤ _ := abs_add_le _ _
            _ ≤ _ := by linarith [hab.1]
        have hexact : |a+y*H| ≤ 1+1001/1000*2 := by
          have : |y*H| ≤ 1001/1000*2 := by
            rw [abs_mul]; exact mul_le_mul hy hH (abs_nonneg _) (by norm_num)
          linarith [abs_add_le a (y*H), hab.2]
        have hbm : |b+m| ≤ 1+1001/1000*2+1/100 := by
          have := abs_sub_abs_le_abs_sub (b+m) (a+y*H)
          have : (u*|a|+η)+(u*(1001/1000*3)+η+1001/1000*(10*u*n)) ≤ 1/100 := by
            have : u*|a| ≤ u := by nlinarith [hab.2]
            have : η ≤ u := by norm_num [u, η]
            have : 6*u ≤ 1/1000 := by norm_num [u]
            nlinarith
          linarith
        have hfinal : |h-(a+y*H)| ≤ u*(1+1001/1000*2+1/100)+η+
            ((u*|a|+η)+(u*(1001/1000*3)+η+1001/1000*(10*u*n))) := by
          have : u*|b+m| ≤ u*(1+1001/1000*2+1/100) := mul_le_mul_of_nonneg_left hbm hu.le
          calc |h-(a+y*H)| = |(h-(b+m))+(b+m-(a+y*H))| := by ring_nf
            _ ≤ _ := abs_add_le _ _
            _ ≤ _ := by linarith
        simp only [hornerL, List.length_cons] at hfinal ⊢
        change |h-(a+y*H)| ≤ 10*u*((n+1 : ℕ) : ℝ)
        push_cast
        have : u*|a| ≤ u := by nlinarith [hab.2]
        have : η ≤ u/1000 := by norm_num [u, η]
        have : 1001/1000*(10*u*n) ≤ 10*u*n+u/10 := by
          have : (1/1000)*(10*u*n) ≤ u/10 := by nlinarith
          linarith
        nlinarith

/-! ### Taylor polynomials -/

def sinCoeffs : List ℝ :=
  [1, -1/6, 1/120, -1/5040, 1/362880, -1/39916800, 1/6227020800]
def cosCoeffs : List ℝ :=
  [1, -1/2, 1/24, -1/720, 1/40320, -1/3628800, 1/479001600, -1/87178291200]

/-- Real and imaginary parts of the degree-15 exponential partial sum at `r i`. -/
lemma exp_partial (r : ℝ) :
    ∑ m ∈ range 16, ((r : ℂ)*Complex.I)^m/(m.factorial : ℂ) =
      ⟨hornerL cosCoeffs (r^2), r*hornerL sinCoeffs (r^2)-r^15/1307674368000⟩ := by
  simp only [sum_range_succ, sum_range_zero, mul_pow, Complex.I_sq]
  apply Complex.ext <;>
    simp [hornerL, cosCoeffs, sinCoeffs, Nat.factorial, pow_succ, Complex.I_mul_I] <;> ring

lemma poly_bound (r : ℝ) (hr : |r| ≤ 1) :
    ‖Complex.exp ((r : ℂ)*Complex.I)-
      ⟨hornerL cosCoeffs (r^2), r*hornerL sinCoeffs (r^2)-r^15/1307674368000⟩‖ ≤ 1/10^13 := by
  rw [← exp_partial]
  have hn : ‖(r : ℂ)*Complex.I‖ = |r| := by simp
  have h := Complex.exp_bound (x := (r : ℂ)*Complex.I) (by rw [hn]; exact hr) (n := 16)
    (by norm_num)
  rw [hn] at h
  refine le_trans h ?_
  have : |r|^16 ≤ 1 := pow_le_one₀ (abs_nonneg _) hr
  have : (Nat.succ 16 : ℝ)/((Nat.factorial 16 : ℝ)*16) ≤ 1/10^13 := by norm_num [Nat.factorial]
  push_cast at *
  nlinarith [pow_nonneg (abs_nonneg r) 16]

theorem cos_poly_error (r : ℝ) (hr : |r| ≤ 1) :
    |Real.cos r-hornerL cosCoeffs (r^2)| ≤ 1/10^12 := by
  have h := poly_bound r hr
  have hre := Complex.abs_re_le_norm (Complex.exp ((r : ℂ)*Complex.I)-
      ⟨hornerL cosCoeffs (r^2), r*hornerL sinCoeffs (r^2)-r^15/1307674368000⟩)
  rw [Complex.sub_re, Complex.exp_ofReal_mul_I_re] at hre
  simp only at hre
  linarith

theorem sin_poly_error (r : ℝ) (hr : |r| ≤ 1) :
    |Real.sin r-r*hornerL sinCoeffs (r^2)| ≤ 1/10^12 := by
  have h := poly_bound r hr
  have him := Complex.abs_im_le_norm (Complex.exp ((r : ℂ)*Complex.I)-
      ⟨hornerL cosCoeffs (r^2), r*hornerL sinCoeffs (r^2)-r^15/1307674368000⟩)
  rw [Complex.sub_im, Complex.exp_ofReal_mul_I_im] at him
  simp only at him
  have h15 : |r^15/1307674368000| ≤ 1/10^12-1/10^13 := by
    rw [abs_div, abs_pow, abs_of_pos (by norm_num : (0:ℝ) < 1307674368000)]
    have : |r|^15 ≤ 1 := pow_le_one₀ (abs_nonneg _) hr
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  calc |Real.sin r-r*hornerL sinCoeffs (r^2)| =
      |(Real.sin r-(r*hornerL sinCoeffs (r^2)-r^15/1307674368000))-r^15/1307674368000| := by
        ring_nf
    _ ≤ _ := abs_sub _ _
    _ ≤ _ := by linarith

/-! ### Quadrants -/

/-- The shader's quadrant selection from `q = k mod 4`. -/
def quadSel (q : ℤ) (s c : ℝ) : ℝ × ℝ :=
  if q = 0 then (s, c) else if q = 1 then (c, -s) else if q = 2 then (-s, -c) else (-c, s)

theorem quadrant (r : ℝ) (k : ℤ) :
    (Real.sin (r+k*(Real.pi/2)), Real.cos (r+k*(Real.pi/2))) =
      quadSel (k % 4) (Real.sin r) (Real.cos r) := by
  have hk : (k : ℝ) = ((k % 4 : ℤ) : ℝ)+4*((k/4 : ℤ) : ℝ) := by
    have h := Int.emod_add_mul_ediv k 4
    have : ((k % 4+4*(k/4) : ℤ) : ℝ) = (k : ℝ) := by rw [h]
    push_cast at this
    linarith
  have hshift : r+k*(Real.pi/2) = (r+((k % 4 : ℤ) : ℝ)*(Real.pi/2))+((k/4 : ℤ) : ℝ)*(2*Real.pi) := by
    rw [hk]; ring
  rw [hshift, Real.sin_add_int_mul_two_pi, Real.cos_add_int_mul_two_pi]
  rcases (by omega : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3) with h | h | h | h <;>
    rw [h] <;> simp only [quadSel] <;> norm_num
  · rw [Real.sin_add_pi_div_two, Real.cos_add_pi_div_two]; exact ⟨rfl, rfl⟩
  · rw [show r+2*(Real.pi/2) = r+Real.pi by ring, Real.sin_add_pi, Real.cos_add_pi]
    exact ⟨rfl, rfl⟩
  · rw [show r+3*(Real.pi/2) = (r+Real.pi)+Real.pi/2 by ring, Real.sin_add_pi_div_two,
      Real.cos_add_pi_div_two, Real.sin_add_pi, Real.cos_add_pi]
    simp

/-! ### Composition -/

lemma hornerL_lipschitz (y z : ℝ) (hy : |y| ≤ 1001/1000) (hz : |z| ≤ 1001/1000) :
    ∀ L : List ℝ, absSum L ≤ 19/10 → L.length ≤ 10 →
      |hornerL L y-hornerL L z| ≤ 3*L.length*|y-z|
  | [], _, _ => by simp [hornerL]
  | a :: as, hsum, hlen => by
    have hsum' : absSum as ≤ 19/10 := by simp only [absSum] at hsum; linarith [abs_nonneg a]
    have hlen' : as.length ≤ 10 := by simp at hlen; omega
    have ih := hornerL_lipschitz y z hy hz as hsum' hlen'
    have hH : |hornerL as y| ≤ 2 := by
      have h1 := hornerL_bound y hy as
      have h2 : (1001/1000:ℝ)^as.length ≤ (1001/1000)^10 := pow_le_pow_right₀ (by norm_num) hlen'
      have h3 : absSum as*(1001/1000)^as.length ≤ 19/10*(1001/1000)^10 :=
        mul_le_mul hsum' h2 (by positivity) (by norm_num)
      have : (19/10:ℝ)*(1001/1000)^10 ≤ 2 := by norm_num
      linarith
    have hn : (as.length : ℝ) ≤ 9 := by
      have : as.length ≤ 9 := by simp at hlen; omega
      exact_mod_cast this
    simp only [hornerL, List.length_cons]
    push_cast
    have e : a+y*hornerL as y-(a+z*hornerL as z) =
        (y-z)*hornerL as y+z*(hornerL as y-hornerL as z) := by ring
    rw [e]
    have hd := abs_nonneg (y-z)
    calc |(y-z)*hornerL as y+z*(hornerL as y-hornerL as z)|
        ≤ |y-z| *2+1001/1000*(3*as.length*|y-z|) := by
          refine le_trans (abs_add_le _ _) ?_
          rw [abs_mul, abs_mul]
          gcongr
      _ ≤ 3*(as.length+1)*|y-z| := by nlinarith

set_option maxHeartbeats 8000000 in
/-- WGSL error bound for `sincos`. `k` is the computed quadrant index
    (`round(fl(x·TWO_OVER_PI))`, exact in binary32), `hred` is the
    reassociation-independent bound for the reduction sum from
    `SumTree.error`, and the coefficient lists are the binary32 constants of
    the exact Taylor coefficients. -/
theorem sincos_error (x : ℝ) (hx : |x| ≤ 2^18) (t : ℝ) (k : ℤ)
    (ht : Rnd (x*(10680707/16777216)) t) (hk : |(k : ℝ)-t| ≤ 1/2)
    (r0 : ℝ)
    (hred : |r0-(x-k*(13176795/8388608)-k*(-6151831/140737488355328))| ≤
      ((1+u)^3-1)*(|x|+|(k : ℝ)*(13176795/8388608)|+|(k : ℝ)*(-6151831/140737488355328)|)+
        5*(1+u)^3*η)
    (r : ℝ) (hr : r = max (-1) (min 1 r0)) (y : ℝ) (hy : Rnd (r*r) y)
    (Bs Bc : List ℝ) (hBs : List.Forall₂ (fun a b => Rnd a b ∧ |a| ≤ 1) sinCoeffs Bs)
    (hBc : List.Forall₂ (fun a b => Rnd a b ∧ |a| ≤ 1) cosCoeffs Bc)
    (hS : ℝ) (hhS : HornerComp Bs y hS) (s : ℝ) (hs : Rnd (r*hS) s)
    (c : ℝ) (hc : HornerComp Bc y c) :
    |(quadSel (k % 4) s c).1-Real.sin x| ≤ 128*u*(1+|x|) ∧
      |(quadSel (k % 4) s c).2-Real.cos x| ≤ 128*u*(1+|x|) := by
  have hu := u_pos
  have hη := η_pos
  have hpi1 := Real.pi_gt_d20
  have hpi2 := Real.pi_lt_d20
  have hpi0 : 0 < Real.pi := Real.pi_pos
  set HI : ℝ := 13176795/8388608
  set LO : ℝ := -6151831/140737488355328
  set TW : ℝ := 10680707/16777216
  -- The constants.
  have hHILO : |HI+LO-Real.pi/2| ≤ 1/10^14 := by
    rw [abs_le]; constructor <;> norm_num [HI, LO] <;> linarith
  have hTW : |TW-2/Real.pi| ≤ 3/10^8 := by
    have h2 : 2/Real.pi ≤ 2/3.14159265358979323846 := div_le_div_of_nonneg_left (by norm_num)
      (by norm_num) hpi1.le
    have h3 : 2/3.14159265358979323847 ≤ 2/Real.pi := div_le_div_of_nonneg_left (by norm_num)
      hpi0 hpi2.le
    rw [abs_le]; constructor <;> norm_num [TW] at h2 h3 ⊢ <;> linarith
  -- The exact reduced argument.
  set re := x-k*(Real.pi/2) with hre
  have hηu : η ≤ u/10^20 := by norm_num [u, η]
  have hkx : |(k : ℝ)-x*(2/Real.pi)| ≤ 1/2+1/10^19+7/10^8*|x| := by
    unfold Rnd at ht
    have h1 : |x*TW| ≤ 637/1000*|x| := by
      rw [abs_mul, abs_of_pos (by norm_num [TW] : (0:ℝ) < TW), mul_comm]
      exact mul_le_mul_of_nonneg_right (by norm_num [TW]) (abs_nonneg _)
    have h2 : |x*TW-x*(2/Real.pi)| ≤ |x| *(3/10^8) := by
      rw [← mul_sub, abs_mul]; exact mul_le_mul_of_nonneg_left hTW (abs_nonneg _)
    have h3 : u*|x*TW| ≤ u*(637/1000*|x|) := mul_le_mul_of_nonneg_left h1 hu.le
    have h4 : u*(637/1000) ≤ 4/10^8 := by norm_num [u]
    have h5 : u*(637/1000*|x|) ≤ 4/10^8*|x| := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h4 (abs_nonneg _)
    have h6 : η ≤ 1/10^19 := by norm_num [η]
    calc |(k : ℝ)-x*(2/Real.pi)| = |((k : ℝ)-t)+(t-x*TW)+(x*TW-x*(2/Real.pi))| := by ring_nf
      _ ≤ |(k : ℝ)-t|+|t-x*TW|+|x*TW-x*(2/Real.pi)| := abs_add_three _ _ _
      _ ≤ 1/2+(u*|x*TW|+η)+|x| *(3/10^8) := by gcongr
      _ ≤ _ := by linarith
  have hre_abs : |re| ≤ 8/10+2/10^7*|x| := by
    have : re = -(Real.pi/2)*((k : ℝ)-x*(2/Real.pi)) := by rw [hre]; field_simp; ring
    rw [this, abs_mul, abs_neg, abs_of_pos (by positivity)]
    have : Real.pi/2 ≤ 15708/10000 := by linarith
    calc Real.pi/2*|(k : ℝ)-x*(2/Real.pi)| ≤ 15708/10000*(1/2+1/10^19+7/10^8*|x|) :=
          mul_le_mul this hkx (abs_nonneg _) (by norm_num)
      _ ≤ _ := by nlinarith [abs_nonneg x]
  have hkabs : |(k : ℝ)| ≤ 64/100*|x|+51/100 := by
    have h1 : |x*(2/Real.pi)| ≤ 6367/10000*|x| := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2/Real.pi), mul_comm]
      have : 2/Real.pi ≤ 6367/10000 := by rw [div_le_iff₀ hpi0]; linarith
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    have := abs_sub_abs_le_abs_sub (k : ℝ) (x*(2/Real.pi))
    have : 7/10^8*|x| ≤ 33/10000*|x| := by nlinarith [abs_nonneg x]
    have : (1:ℝ)/10^19 ≤ 1/100 := by norm_num
    linarith
  -- Reduction error.
  have hred' : |r0-re| ≤ 8*u*(1+|x|) := by
    have hγ : (1+u)^3-1 ≤ 3*u+u/1000 := by norm_num [u]
    have hg : (1+u)^3 ≤ 2 := by norm_num [u]
    have hsum : |x|+|k*HI|+|k*LO| ≤ 21/10*|x|+9/10 := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num [HI] : (0:ℝ) < HI),
        abs_of_neg (by norm_num [LO] : LO < 0)]
      have e1 : |(k : ℝ)| *HI ≤ (64/100*|x|+51/100)*(15708/10000) :=
        mul_le_mul hkabs (by norm_num [HI]) (by norm_num [HI]) (by positivity)
      have e2 : |(k : ℝ)| *(-LO) ≤ (64/100*|x|+51/100)*(1/10^7) :=
        mul_le_mul hkabs (by norm_num [LO]) (by norm_num [LO]) (by positivity)
      nlinarith [abs_nonneg x]
    have h1 : ((1+u)^3-1)*(|x|+|k*HI|+|k*LO|) ≤ (3*u+u/1000)*(21/10*|x|+9/10) :=
      mul_le_mul hγ hsum (by positivity) (by positivity)
    have hk1 : |(k : ℝ)| ≤ |x|+1 := by linarith [abs_nonneg x]
    have h2 : |(x-k*HI-k*LO)-re| ≤ (|x|+1)*(1/10^14) := by
      rw [show (x-k*HI-k*LO)-re = -(k*(HI+LO-Real.pi/2)) by rw [hre]; ring, abs_neg, abs_mul]
      exact mul_le_mul hk1 hHILO (abs_nonneg _) (by positivity)
    have h3 : 5*(1+u)^3*η ≤ 10*η := by nlinarith
    have h4 : (1:ℝ)/10^14 ≤ u/10^6 := by norm_num [u]
    have h5 : (|x|+1)*(1/10^14) ≤ (|x|+1)*(u/10^6) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    have h6 : (3*u+u/1000)*(21/10*|x|+9/10) = (3*u+u/1000)*(21/10)*|x|+(3*u+u/1000)*(9/10) := by
      ring
    have h7 : (3*u+u/1000)*(21/10)*|x| ≤ 7*u*|x| := by
      have : (3*u+u/1000)*(21/10) ≤ 7*u := by norm_num [u]
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    have h8 : (3*u+u/1000)*(9/10)+10*η+(|x|+1)*(u/10^6) ≤ 7*u+u/10^6*|x| := by
      have : (3*u+u/1000)*(9/10)+10*η+u/10^6 ≤ 7*u := by norm_num [u, η]
      nlinarith [abs_nonneg x]
    have h9 : u/10^6*|x| ≤ u*|x|/10^6 := by rw [div_mul_eq_mul_div]
    calc |r0-re| = |(r0-(x-k*HI-k*LO))+((x-k*HI-k*LO)-re)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ (((1+u)^3-1)*(|x|+|(k : ℝ)*HI|+|(k : ℝ)*LO|)+5*(1+u)^3*η)+(|x|+1)*(1/10^14) :=
          add_le_add hred h2
      _ ≤ ((3*u+u/1000)*(21/10*|x|+9/10)+10*η)+(|x|+1)*(u/10^6) :=
          add_le_add (add_le_add h1 h3) h5
      _ = (3*u+u/1000)*(21/10)*|x|+((3*u+u/1000)*(9/10)+10*η+(|x|+1)*(u/10^6)) := by
          rw [h6]; ring
      _ ≤ 7*u*|x|+(7*u+u/10^6*|x|) := add_le_add h7 h8
      _ ≤ 7*u*|x|+7*u+u*|x|/10^6 := by linarith [h9]
      _ ≤ 7*u*(1+|x|)+u*|x|/10^6 := by linarith
      _ ≤ _ := by
        have : u*|x|/10^6 ≤ u*(1+|x|) := by
          have : u*|x| ≤ u*(1+|x|) := mul_le_mul_of_nonneg_left (by linarith) hu.le
          have : 0 ≤ u*|x| := by positivity
          linarith [div_le_self this (by norm_num : (1:ℝ) ≤ 10^6)]
        linarith
  -- Domain: the clamp is inactive.
  have hr0 : |r0| ≤ 99/100 := by
    have h1 : 8*u*(1+|x|) ≤ 8*u*(1+2^18) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : 8*u*(1+2^18) ≤ 13/100 := by norm_num [u]
    have h3 : 2/10^7*|x| ≤ 2/10^7*2^18 := mul_le_mul_of_nonneg_left hx (by norm_num)
    have h4 : (2:ℝ)/10^7*2^18 ≤ 6/100 := by norm_num
    have h5 := abs_sub_abs_le_abs_sub r0 re
    linarith
  have hrr : r = r0 := by
    rw [hr, abs_le] at *
    rw [min_eq_right (by linarith), max_eq_right (by linarith)]
  rw [← hrr] at hred' hr0
  have hr1 : |r| ≤ 1 := by linarith
  -- Horner arguments.
  unfold Rnd at hy hs
  have hrr2 : |r*r| ≤ 1 := by rw [abs_mul]; nlinarith [abs_nonneg r]
  have hyb : |y| ≤ 1001/1000 := by
    have := abs_sub_abs_le_abs_sub y (r*r)
    have : u*|r*r| ≤ u := by nlinarith
    have : u+η ≤ 1/1000 := by norm_num [u, η]
    linarith
  have hy2 : |y-r^2| ≤ u+η := by
    rw [sq]; have : u*|r*r| ≤ u := by nlinarith
    linarith
  have hr2b : |r^2| ≤ 1001/1000 := by rw [sq]; linarith
  have hsinS : absSum sinCoeffs ≤ 19/10 := by norm_num [absSum, sinCoeffs, abs_of_pos, abs_of_neg]
  have hcosS : absSum cosCoeffs ≤ 19/10 := by norm_num [absSum, cosCoeffs, abs_of_pos, abs_of_neg]
  have hSe := horner_error y hyb sinCoeffs Bs hS hBs hsinS (by simp [sinCoeffs]) hhS
  have hCe := horner_error y hyb cosCoeffs Bc c hBc hcosS (by simp [cosCoeffs]) hc
  have hSl := hornerL_lipschitz y (r^2) hyb hr2b sinCoeffs hsinS (by simp [sinCoeffs])
  have hCl := hornerL_lipschitz y (r^2) hyb hr2b cosCoeffs hcosS (by simp [cosCoeffs])
  simp only [show sinCoeffs.length = 7 by rfl, show cosCoeffs.length = 8 by rfl] at hSe hCe hSl hCl
  push_cast at hSe hCe hSl hCl
  have hSb : |hornerL sinCoeffs (r^2)| ≤ 2 := by
    have h1 := hornerL_bound (r^2) hr2b sinCoeffs
    have : absSum sinCoeffs*(1001/1000)^sinCoeffs.length ≤ 2 := by
      norm_num [absSum, sinCoeffs, abs_of_pos, abs_of_neg]
    linarith
  -- Cosine.
  have hcos : |c-Real.cos re| ≤ 128*u*(1+|x|) := by
    have h1 := cos_poly_error r hr1
    have h2 := Real.abs_cos_sub_cos_le r re
    have hyd : 3*8*|y-r^2| ≤ 3*8*(u+η) := by gcongr
    calc |c-Real.cos re| = |(c-hornerL cosCoeffs y)+(hornerL cosCoeffs y-hornerL cosCoeffs (r^2))
          -(Real.cos r-hornerL cosCoeffs (r^2))+(Real.cos r-Real.cos re)| := by ring_nf
      _ ≤ |c-hornerL cosCoeffs y|+|hornerL cosCoeffs y-hornerL cosCoeffs (r^2)|
          +|Real.cos r-hornerL cosCoeffs (r^2)|+|Real.cos r-Real.cos re| := by
          refine le_trans (abs_add_le _ _) ?_
          refine add_le_add (le_trans (abs_sub _ _) (add_le_add (abs_add_le _ _) le_rfl)) le_rfl
      _ ≤ 10*u*8+3*8*(u+η)+1/10^12+8*u*(1+|x|) := by linarith
      _ ≤ _ := by
        have : (1:ℝ)/10^12 ≤ u/1000 := by norm_num [u]
        nlinarith [abs_nonneg x]
  -- Sine.
  have hsin : |s-Real.sin re| ≤ 128*u*(1+|x|) := by
    have h1 := sin_poly_error r hr1
    have h2 := Real.abs_sin_sub_sin_le r re
    have hS3 : |hS| ≤ 3 := by
      have := abs_sub_abs_le_abs_sub hS (hornerL sinCoeffs (r^2))
      have : 10*u*7+3*7*(u+η) ≤ 1/2 := by norm_num [u, η]
      have := abs_sub_abs_le_abs_sub hS (hornerL sinCoeffs y)
      linarith [abs_sub_le hS (hornerL sinCoeffs y) (hornerL sinCoeffs (r^2))]
    have hrh : |r*hS-r*hornerL sinCoeffs (r^2)| ≤ 10*u*7+3*7*(u+η) := by
      rw [← mul_sub, abs_mul]
      have : |hS-hornerL sinCoeffs (r^2)| ≤ 10*u*7+3*7*(u+η) := by
        have := abs_sub_le hS (hornerL sinCoeffs y) (hornerL sinCoeffs (r^2))
        have : 3*7*|y-r^2| ≤ 3*7*(u+η) := by gcongr
        linarith
      calc |r| *|hS-hornerL sinCoeffs (r^2)| ≤ 1*(10*u*7+3*7*(u+η)) :=
            mul_le_mul hr1 this (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    have hrs : u*|r*hS| ≤ 3*u := by
      rw [abs_mul]
      have := mul_le_mul hr1 hS3 (abs_nonneg _) zero_le_one
      nlinarith
    calc |s-Real.sin re| = |(s-r*hS)+(r*hS-r*hornerL sinCoeffs (r^2))
          -(Real.sin r-r*hornerL sinCoeffs (r^2))+(Real.sin r-Real.sin re)| := by ring_nf
      _ ≤ |s-r*hS|+|r*hS-r*hornerL sinCoeffs (r^2)|
          +|Real.sin r-r*hornerL sinCoeffs (r^2)|+|Real.sin r-Real.sin re| := by
          refine le_trans (abs_add_le _ _) ?_
          refine add_le_add (le_trans (abs_sub _ _) (add_le_add (abs_add_le _ _) le_rfl)) le_rfl
      _ ≤ (3*u+η)+(10*u*7+3*7*(u+η))+1/10^12+8*u*(1+|x|) := by linarith
      _ ≤ _ := by
        have : (1:ℝ)/10^12 ≤ u/1000 := by norm_num [u]
        nlinarith [abs_nonneg x]
  -- Quadrants.
  have hq := quadrant re k
  have hx : re+k*(Real.pi/2) = x := by rw [hre]; ring
  rw [hx] at hq
  have hsx : Real.sin x = (quadSel (k % 4) (Real.sin re) (Real.cos re)).1 := by rw [← hq]
  have hcx : Real.cos x = (quadSel (k % 4) (Real.sin re) (Real.cos re)).2 := by rw [← hq]
  rw [hsx, hcx]
  unfold quadSel
  split_ifs <;> simp only [] <;>
    first
    | exact ⟨hsin, hcos⟩
    | exact ⟨hcos, by rw [show -s-(-Real.sin re) = -(s-Real.sin re) by ring, abs_neg]; exact hsin⟩
    | exact ⟨by rw [show -s-(-Real.sin re) = -(s-Real.sin re) by ring, abs_neg]; exact hsin,
             by rw [show -c-(-Real.cos re) = -(c-Real.cos re) by ring, abs_neg]; exact hcos⟩
    | exact ⟨by rw [show -c-(-Real.cos re) = -(c-Real.cos re) by ring, abs_neg]; exact hcos, hsin⟩

end BlackHole.Wgsl
