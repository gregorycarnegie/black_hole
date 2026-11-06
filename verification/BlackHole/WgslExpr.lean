module

public import BlackHole.WgslPoly
public import BlackHole.WgslSinCos
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Calculus.MeanValue

/-! Running WGSL error bounds for programs with division, square roots,
floors, clamps and branches (obligation F2).

`GExpr` extends the polynomial programs of `WgslPoly` with division by a
computed value, `sqrt` (inherited from `1/inverseSqrt`, within `10u`), exact
`max`/`min` (floors and clamps), and a branch on the sign of a computed value
against an exact threshold. `bound v E e` is the forward error recursion
evaluated at the exact inputs `v` with input errors `E`. `Safe` collects the
only conditions under which a finite bound can hold in general: each
denominator's exact magnitude exceeds its own error bound, each square-root
argument stays nonnegative after its error, and each branch value is farther
from its threshold than its error so both evaluations take the same side.
Floors and clamps need no condition because `max` and `min` are 1-Lipschitz.

`error` proves `|y - exact| ≤ bound` for every input and every admissible
rounding whenever `Safe` holds. -/

@[expose] public section
noncomputable section

namespace BlackHole.WgslExpr
open Wgsl WgslPoly

inductive GExpr
  | input (i : ℕ)
  | const (c : ℝ)
  | add (a b : GExpr)
  | sub (a b : GExpr)
  | mul (a b : GExpr)
  | neg (a : GExpr)
  | div (a b : GExpr)
  | sqrt (a : GExpr)
  | max (a b : GExpr)
  | min (a b : GExpr)
  /-- `if c < t { a } else { b }` for an exact threshold `t`. -/
  | lt (c : GExpr) (t : ℝ) (a b : GExpr)
  | abs (a : GExpr)
  /-- `inverseSqrt`, 2 ULP. -/
  | invsqrt (a : GExpr)
  /-- `exp` and `exp2`, `3 + 2|x|` ULP. -/
  | exp (a : GExpr)
  | exp2 (a : GExpr)
  /-- `log` and `log2`: `2⁻²¹` absolute on `[0.5, 2]`, `3` ULP elsewhere. -/
  | log (a : GExpr)
  | log2 (a : GExpr)
  /-- A builtin whose accuracy is inherited from the program `f`, applied to the
  value of `a` (`f` reads it as input 0). -/
  | inh (f a : GExpr)
  /-- `tanh`: the worse of `10⁻⁵` absolute and inheritance from `f`. -/
  | tanh (f a : GExpr)
  /-- `if a < b { x } else { y }`; WGSL compares the computed operands exactly. -/
  | lt2 (a b x y : GExpr)
  /-- `sincos(a).x` and `sincos(a).y` of the shader's arithmetic `sincos`. -/
  | sinS (a : GExpr)
  | cosS (a : GExpr)

def exp2R (x : ℝ) : ℝ := Real.exp (x*Real.log 2)

/-- Some WGSL evaluation of the shader's arithmetic `sincos(x)` (geodesic.wesl)
returns `out`: rounded reduction by `π/2` with `round`, clamped remainder,
Horner polynomials with binary32 coefficients, quadrant from `k mod 4`. -/
def SinCosComputes (x : ℝ) (out : ℝ × ℝ) : Prop :=
  ∃ (t : ℝ) (k : ℤ) (r0 r yy : ℝ) (Bs Bc : List ℝ) (hS s c : ℝ),
    Rnd (x*(10680707/16777216)) t ∧ |(k : ℝ)-t| ≤ 1/2 ∧
    |r0-(x-k*(13176795/8388608)-k*(-6151831/140737488355328))| ≤
      ((1+u)^3-1)*(|x|+|(k : ℝ)*(13176795/8388608)|+|(k : ℝ)*(-6151831/140737488355328)|)+
        5*(1+u)^3*η ∧
    r = Max.max (-1) (Min.min 1 r0) ∧ Rnd (r*r) yy ∧
    List.Forall₂ (fun a b => Rnd a b ∧ |a| ≤ 1) sinCoeffs Bs ∧
    List.Forall₂ (fun a b => Rnd a b ∧ |a| ≤ 1) cosCoeffs Bc ∧
    HornerComp Bs yy hS ∧ Rnd (r*hS) s ∧ HornerComp Bc yy c ∧ out = quadSel (k % 4) s c

theorem sincos_spec {x : ℝ} {out : ℝ × ℝ} (h : SinCosComputes x out) (hx : |x| ≤ 2^18) :
    |out.1-Real.sin x| ≤ 128*u*(1+|x|) ∧ |out.2-Real.cos x| ≤ 128*u*(1+|x|) := by
  obtain ⟨t,k,r0,r,yy,Bs,Bc,hS,s,c,ht,hk,hred,hr,hy,hBs,hBc,hhS,hs,hc,rfl⟩ := h
  exact sincos_error x hx t k ht hk r0 hred r hr yy hy Bs Bc hBs hBc hS hhS s hs c hc
def log2R (x : ℝ) : ℝ := Real.log x/Real.log 2

/-- One ULP of a binary32 value `z`, including subnormals, is at most this. -/
def ulp (z : ℝ) : ℝ := 2*u*|z|+η

namespace GExpr

def exact (v : ℕ → ℝ) : GExpr → ℝ
  | input i => v i
  | const c => c
  | add a b => exact v a+exact v b
  | sub a b => exact v a-exact v b
  | mul a b => exact v a*exact v b
  | neg a => -exact v a
  | div a b => exact v a/exact v b
  | sqrt a => Real.sqrt (exact v a)
  | max a b => Max.max (exact v a) (exact v b)
  | min a b => Min.min (exact v a) (exact v b)
  | lt c t a b => if exact v c < t then exact v a else exact v b
  | abs a => |exact v a|
  | invsqrt a => 1/Real.sqrt (exact v a)
  | exp a => Real.exp (exact v a)
  | exp2 a => exp2R (exact v a)
  | log a => Real.log (exact v a)
  | log2 a => log2R (exact v a)
  | inh f a => exact (fun _ => exact v a) f
  | tanh _ a => Real.tanh (exact v a)
  | lt2 a b x y => if exact v a < exact v b then exact v x else exact v y
  | sinS a => Real.sin (exact v a)
  | cosS a => Real.cos (exact v a)

/-- The running forward error bound at exact inputs `v` with input errors `E`. -/
def bound (v E : ℕ → ℝ) : GExpr → ℝ
  | input i => E i
  | const _ => 0
  | add a b => bound v E a+bound v E b+U*(|exact v a|+|exact v b|+bound v E a+bound v E b)+η
  | sub a b => bound v E a+bound v E b+U*(|exact v a|+|exact v b|+bound v E a+bound v E b)+η
  | mul a b => |exact v a| *bound v E b+|exact v b| *bound v E a+bound v E a*bound v E b+
      U*((|exact v a|+bound v E a)*(|exact v b|+bound v E b))+η
  | neg a => bound v E a
  | div a b => (bound v E a+|exact v a/exact v b| *bound v E b)/(|exact v b|-bound v E b)+
      U*((|exact v a|+bound v E a)/(|exact v b|-bound v E b))+η
  | sqrt a => bound v E a/Real.sqrt (exact v a)+10*u*Real.sqrt (exact v a+bound v E a)+η
  | max a b => Max.max (bound v E a) (bound v E b)
  | min a b => Max.max (bound v E a) (bound v E b)
  | lt c t a b => if exact v c < t then bound v E a else bound v E b
  | abs a => bound v E a
  | invsqrt a => bound v E a/(Real.sqrt (exact v a-bound v E a)*Real.sqrt (exact v a)*
      (Real.sqrt (exact v a-bound v E a)+Real.sqrt (exact v a)))+
      4*u/Real.sqrt (exact v a-bound v E a)
  | exp a => Real.exp (exact v a)*(Real.exp (bound v E a)-1)+
      (3+2*(|exact v a|+bound v E a))*(2*u*Real.exp (exact v a+bound v E a)+η)
  | exp2 a => exp2R (exact v a)*(exp2R (bound v E a)-1)+
      (3+2*(|exact v a|+bound v E a))*(2*u*exp2R (exact v a+bound v E a)+η)
  | log a => bound v E a/(exact v a-bound v E a)+1/2^21+
      3*(2*u*(|Real.log (exact v a)|+bound v E a/(exact v a-bound v E a))+η)
  | log2 a => bound v E a/((exact v a-bound v E a)*Real.log 2)+1/2^21+
      3*(2*u*(|log2R (exact v a)|+bound v E a/((exact v a-bound v E a)*Real.log 2))+η)
  | inh f a => bound (fun _ => exact v a) (fun _ => bound v E a) f
  | tanh f a => Max.max (bound v E a+1/10^5) (bound (fun _ => exact v a) (fun _ => bound v E a) f)
  | lt2 a b x y => if exact v a < exact v b then bound v E x else bound v E y
  | sinS a => bound v E a+128*u*(1+(|exact v a|+bound v E a))
  | cosS a => bound v E a+128*u*(1+(|exact v a|+bound v E a))

/-- Conditions under which the running bound is valid. -/
def Safe (v E : ℕ → ℝ) : GExpr → Prop
  | input _ => True
  | const _ => True
  | add a b => Safe v E a ∧ Safe v E b
  | sub a b => Safe v E a ∧ Safe v E b
  | mul a b => Safe v E a ∧ Safe v E b
  | neg a => Safe v E a
  | div a b => Safe v E a ∧ Safe v E b ∧ bound v E b < |exact v b| ∧
      1/2^126 ≤ |exact v b|-bound v E b ∧ |exact v b|+bound v E b ≤ 2^126
  | sqrt a => Safe v E a ∧ 0 < exact v a ∧ bound v E a ≤ exact v a
  | max a b => Safe v E a ∧ Safe v E b
  | min a b => Safe v E a ∧ Safe v E b
  | lt c t a b => Safe v E c ∧ Safe v E a ∧ Safe v E b ∧ bound v E c < |exact v c-t|
  | abs a => Safe v E a
  | invsqrt a => Safe v E a ∧ bound v E a < exact v a
  | exp a => Safe v E a
  | exp2 a => Safe v E a
  | log a => Safe v E a ∧ bound v E a < exact v a
  | log2 a => Safe v E a ∧ bound v E a < exact v a
  | inh f a => Safe v E a ∧ Safe (fun _ => exact v a) (fun _ => bound v E a) f
  | tanh f a => Safe v E a ∧ Safe (fun _ => exact v a) (fun _ => bound v E a) f ∧
      ∀ t, exact (fun _ => t) f = Real.tanh t
  | lt2 a b x y => Safe v E a ∧ Safe v E b ∧ Safe v E x ∧ Safe v E y ∧
      bound v E a+bound v E b < |exact v a-exact v b|
  | sinS a => Safe v E a ∧ |exact v a|+bound v E a ≤ 2^18
  | cosS a => Safe v E a ∧ |exact v a|+bound v E a ≤ 2^18

/-- Some WGSL evaluation of the program from computed inputs `w` returns `y`. -/
def Computes (w : ℕ → ℝ) : GExpr → ℝ → Prop
  | input i, y => y = w i
  | const c, y => y = c
  | add a b, y => ∃ ya yb, Computes w a ya ∧ Computes w b yb ∧ Rnd (ya+yb) y
  | sub a b, y => ∃ ya yb, Computes w a ya ∧ Computes w b yb ∧ Rnd (ya-yb) y
  | mul a b, y => ∃ ya yb, Computes w a ya ∧ Computes w b yb ∧ Rnd (ya*yb) y
  | neg a, y => ∃ ya, Computes w a ya ∧ y = -ya
  | div a b, y => ∃ ya yb, Computes w a ya ∧ Computes w b yb ∧ DivSpec ya yb y
  | sqrt a, y => ∃ ya, Computes w a ya ∧ |y-Real.sqrt ya| ≤ 10*u*Real.sqrt ya+η
  | max a b, y => ∃ ya yb, Computes w a ya ∧ Computes w b yb ∧ y = Max.max ya yb
  | min a b, y => ∃ ya yb, Computes w a ya ∧ Computes w b yb ∧ y = Min.min ya yb
  | lt c t a b, y => ∃ yc, Computes w c yc ∧
      ((yc < t ∧ Computes w a y) ∨ (¬ yc < t ∧ Computes w b y))
  | abs a, y => ∃ ya, Computes w a ya ∧ y = |ya|
  | invsqrt a, y => ∃ ya, Computes w a ya ∧ InvSqrt ya y
  | exp a, y => ∃ ya, Computes w a ya ∧ |y-Real.exp ya| ≤ (3+2*|ya|)*ulp (Real.exp ya)
  | exp2 a, y => ∃ ya, Computes w a ya ∧ |y-exp2R ya| ≤ (3+2*|ya|)*ulp (exp2R ya)
  | log a, y => ∃ ya, Computes w a ya ∧ |y-Real.log ya| ≤ 1/2^21+3*ulp (Real.log ya)
  | log2 a, y => ∃ ya, Computes w a ya ∧ |y-log2R ya| ≤ 1/2^21+3*ulp (log2R ya)
  | inh f a, y => ∃ ya, Computes w a ya ∧ Computes (fun _ => ya) f y
  | tanh f a, y => ∃ ya, Computes w a ya ∧
      (|y-Real.tanh ya| ≤ 1/10^5 ∨ Computes (fun _ => ya) f y)
  | lt2 a b x y, r => ∃ ya yb, Computes w a ya ∧ Computes w b yb ∧
      ((ya < yb ∧ Computes w x r) ∨ (¬ ya < yb ∧ Computes w y r))
  | sinS a, y => ∃ ya out, Computes w a ya ∧ SinCosComputes ya out ∧ y = out.1
  | cosS a, y => ∃ ya out, Computes w a ya ∧ SinCosComputes ya out ∧ y = out.2

lemma max_lip (a b c d : ℝ) : |Max.max a b-Max.max c d| ≤ Max.max |a-c| |b-d| := by
  rcases le_total a b with h1 | h1 <;> rcases le_total c d with h2 | h2 <;>
    simp only [max_eq_right,max_eq_left,h1,h2] <;>
    (rw [abs_le]; constructor <;>
      (first
        | linarith [le_max_left |a-c| |b-d|,le_max_right |a-c| |b-d|,le_abs_self (a-c),
            neg_abs_le (a-c),le_abs_self (b-d),neg_abs_le (b-d)]))

lemma min_lip (a b c d : ℝ) : |Min.min a b-Min.min c d| ≤ Max.max |a-c| |b-d| := by
  rcases le_total a b with h1 | h1 <;> rcases le_total c d with h2 | h2 <;>
    simp only [min_eq_right,min_eq_left,h1,h2] <;>
    (rw [abs_le]; constructor <;>
      (first
        | linarith [le_max_left |a-c| |b-d|,le_max_right |a-c| |b-d|,le_abs_self (a-c),
            neg_abs_le (a-c),le_abs_self (b-d),neg_abs_le (b-d)]))

lemma sqrt_lip {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    |Real.sqrt x-Real.sqrt y| ≤ |x-y|/Real.sqrt y := by
  have hsy := Real.sqrt_pos.mpr hy
  have hsx := Real.sqrt_nonneg x
  rw [le_div_iff₀ hsy]
  have hprod : (Real.sqrt x-Real.sqrt y)*(Real.sqrt x+Real.sqrt y) = x-y := by
    rw [show (Real.sqrt x-Real.sqrt y)*(Real.sqrt x+Real.sqrt y) =
      Real.sqrt x^2-Real.sqrt y^2 by ring,Real.sq_sqrt hx,Real.sq_sqrt hy.le]
  calc |Real.sqrt x-Real.sqrt y| *Real.sqrt y ≤
        |Real.sqrt x-Real.sqrt y| *(Real.sqrt x+Real.sqrt y) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    _ = |x-y| := by rw [← hprod,abs_mul,abs_of_nonneg (by linarith : 0 ≤ Real.sqrt x+Real.sqrt y)]

lemma exp_lip (x a : ℝ) : |Real.exp x-Real.exp a| ≤ Real.exp a*(Real.exp |x-a|-1) := by
  have hx : Real.exp x = Real.exp a*Real.exp (x-a) := by rw [← Real.exp_add]; ring_nf
  have ha := Real.exp_pos a
  rw [hx,show Real.exp a*Real.exp (x-a)-Real.exp a = Real.exp a*(Real.exp (x-a)-1) by ring,
    abs_mul,abs_of_pos ha]
  apply mul_le_mul_of_nonneg_left _ ha.le
  have e1 := Real.add_one_le_exp (a-x)
  have e2 := Real.add_one_le_exp (x-a)
  rcases le_total a x with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h),abs_of_nonneg (by linarith)]
  · rw [abs_of_nonpos (sub_nonpos.mpr h),neg_sub]
    have e3 : Real.exp (x-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [abs_of_nonpos (by linarith)]
    linarith

lemma log_lip {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    |Real.log x-Real.log a| ≤ |x-a|/Min.min x a := by
  have hm : 0 < Min.min x a := lt_min hx ha
  rw [le_div_iff₀ hm]
  rcases le_total x a with h | h
  · rw [min_eq_left h]
    have := Real.log_le_sub_one_of_pos (div_pos ha hx)
    rw [Real.log_div ha.ne' hx.ne'] at this
    have hle : Real.log x ≤ Real.log a := Real.log_le_log hx h
    rw [abs_of_nonpos (by linarith),abs_of_nonpos (by linarith)]
    have : (a/x-1)*x = a-x := by field_simp
    nlinarith
  · rw [min_eq_right h]
    have := Real.log_le_sub_one_of_pos (div_pos hx ha)
    rw [Real.log_div hx.ne' ha.ne'] at this
    have hle : Real.log a ≤ Real.log x := Real.log_le_log ha h
    rw [abs_of_nonneg (by linarith),abs_of_nonneg (by linarith)]
    have : (x/a-1)*a = x-a := by field_simp
    nlinarith

lemma invsqrt_eq {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    |1/Real.sqrt x-1/Real.sqrt a| =
      |x-a|/(Real.sqrt x*Real.sqrt a*(Real.sqrt x+Real.sqrt a)) := by
  have sx := Real.sqrt_pos.mpr hx; have sa := Real.sqrt_pos.mpr ha
  have hxx := Real.sq_sqrt hx.le; have haa := Real.sq_sqrt ha.le
  have hd : 0 < Real.sqrt x*Real.sqrt a*(Real.sqrt x+Real.sqrt a) := by positivity
  have heq : 1/Real.sqrt x-1/Real.sqrt a =
      -(x-a)/(Real.sqrt x*Real.sqrt a*(Real.sqrt x+Real.sqrt a)) := by
    rw [eq_div_iff hd.ne']
    field_simp
    nlinarith
  rw [heq,abs_div,abs_neg,abs_of_pos hd]

lemma tanh_lip (x y : ℝ) : |Real.tanh x-Real.tanh y| ≤ |x-y| := by
  have heq : Real.tanh = fun t => Real.sinh t/Real.cosh t := by
    funext t; exact Real.tanh_eq_sinh_div_cosh t
  have hd (t : ℝ) : HasDerivAt Real.tanh (1/Real.cosh t^2) t := by
    have hc := Real.cosh_pos t
    have h := (Real.hasDerivAt_sinh t).div (Real.hasDerivAt_cosh t) hc.ne'
    rw [heq]
    convert h using 1
    field_simp
    nlinarith [Real.cosh_sq t]
  have hb (t : ℝ) : ‖1/Real.cosh t^2‖ ≤ 1 := by
    have hc := Real.cosh_pos t
    rw [Real.norm_eq_abs,abs_of_pos (by positivity),div_le_one (by positivity)]
    nlinarith [Real.one_le_cosh t]
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := Real.tanh)
    (fun t _ => (hd t).hasDerivWithinAt) (fun t _ => hb t) (convex_univ : Convex ℝ (Set.univ : Set ℝ))
    (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using this

theorem error : ∀ (e : GExpr) (v w E : ℕ → ℝ), (∀ i, |w i-v i| ≤ E i) →
    ∀ (y : ℝ), Safe v E e → Computes w e y → |y-exact v e| ≤ bound v E e
  | input i, v, w, E, hw, y, _, h => by simp only [Computes] at h; subst h; exact hw i
  | const c, v, w, E, hw, y, _, h => by simp only [Computes] at h; subst h; simp [exact,bound]
  | add a b, v, w, E, hw, y, hs, h => by
    obtain ⟨ya,yb,ha,hb,hy⟩ := h
    have ea := error a v w E hw ya hs.1 ha
    have eb := error b v w E hw yb hs.2 hb
    have hr := PExpr.rnd_le hy
    simp only [exact,bound]
    have h1 : |ya+yb| ≤ |exact v a|+|exact v b|+bound v E a+bound v E b := by
      have := abs_add_le ya yb
      have := abs_sub_abs_le_abs_sub ya (exact v a)
      have := abs_sub_abs_le_abs_sub yb (exact v b)
      linarith
    have hU := U_pos
    calc |y-(exact v a+exact v b)| ≤ |y-(ya+yb)|+(|ya-exact v a|+|yb-exact v b|) := by
          have := abs_sub_le y (ya+yb) (exact v a+exact v b)
          have := abs_add_le (ya-exact v a) (yb-exact v b)
          rw [show ya+yb-(exact v a+exact v b) = (ya-exact v a)+(yb-exact v b) by ring] at *
          linarith
      _ ≤ _ := by nlinarith
  | sub a b, v, w, E, hw, y, hs, h => by
    obtain ⟨ya,yb,ha,hb,hy⟩ := h
    have ea := error a v w E hw ya hs.1 ha
    have eb := error b v w E hw yb hs.2 hb
    have hr := PExpr.rnd_le hy
    simp only [exact,bound]
    have h1 : |ya-yb| ≤ |exact v a|+|exact v b|+bound v E a+bound v E b := by
      have := abs_sub ya yb
      have := abs_sub_abs_le_abs_sub ya (exact v a)
      have := abs_sub_abs_le_abs_sub yb (exact v b)
      linarith
    have hU := U_pos
    calc |y-(exact v a-exact v b)| ≤ |y-(ya-yb)|+(|ya-exact v a|+|yb-exact v b|) := by
          have := abs_sub_le y (ya-yb) (exact v a-exact v b)
          have := abs_sub (ya-exact v a) (yb-exact v b)
          rw [show ya-yb-(exact v a-exact v b) = (ya-exact v a)-(yb-exact v b) by ring] at *
          linarith
      _ ≤ _ := by nlinarith
  | mul a b, v, w, E, hw, y, hs, h => by
    obtain ⟨ya,yb,ha,hb,hy⟩ := h
    have ea := error a v w E hw ya hs.1 ha
    have eb := error b v w E hw yb hs.2 hb
    have hr := PExpr.rnd_le hy
    simp only [exact,bound]
    set A := exact v a; set B := exact v b; set Ba := bound v E a; set Bb := bound v E b
    have hBa : 0 ≤ Ba := (abs_nonneg _).trans ea
    have hBb : 0 ≤ Bb := (abs_nonneg _).trans eb
    have hya : |ya| ≤ |A|+Ba := by have := abs_sub_abs_le_abs_sub ya A; linarith
    have hyb : |yb| ≤ |B|+Bb := by have := abs_sub_abs_le_abs_sub yb B; linarith
    have hp : |ya*yb-A*B| ≤ |A| *Bb+|B| *Ba+Ba*Bb := by
      rw [show ya*yb-A*B = (ya-A)*(yb-B)+A*(yb-B)+B*(ya-A) by ring]
      calc _ ≤ |(ya-A)*(yb-B)|+|A*(yb-B)|+|B*(ya-A)| := abs_add_three _ _ _
        _ = |ya-A| *|yb-B|+|A| *|yb-B|+|B| *|ya-A| := by rw [abs_mul,abs_mul,abs_mul]
        _ ≤ Ba*Bb+|A| *Bb+|B| *Ba := by gcongr
        _ = _ := by ring
    have hyy : |ya*yb| ≤ (|A|+Ba)*(|B|+Bb) := by
      rw [abs_mul]; exact mul_le_mul hya hyb (abs_nonneg _) (by positivity)
    have hU := U_pos
    calc |y-A*B| ≤ |y-ya*yb|+|ya*yb-A*B| := abs_sub_le _ _ _
      _ ≤ _ := by nlinarith
  | neg a, v, w, E, hw, y, hs, h => by
    obtain ⟨ya,ha,rfl⟩ := h
    have ea := error a v w E hw ya hs ha
    simp only [exact,bound]
    rw [show -ya- -exact v a = -(ya-exact v a) by ring,abs_neg]; exact ea
  | div a b, v, w, E, hw, y, hs, h => by
    obtain ⟨ya,yb,ha,hb,hy⟩ := h
    obtain ⟨sa,sb,hden,hlo,hhi⟩ := hs
    have ea := error a v w E hw ya sa ha
    have eb := error b v w E hw yb sb hb
    have hy := hy ⟨by have := abs_sub_abs_le_abs_sub (exact v b) yb; rw [abs_sub_comm] at this; linarith,
      by have := abs_sub_abs_le_abs_sub yb (exact v b); linarith⟩
    simp only [exact,bound]
    set A := exact v a; set B := exact v b; set Ba := bound v E a; set Bb := bound v E b
    have hBb : 0 ≤ Bb := (abs_nonneg _).trans eb
    have hBa : 0 ≤ Ba := (abs_nonneg _).trans ea
    have hd : 0 < |B|-Bb := by linarith
    have hyb : |B|-Bb ≤ |yb| := by have := abs_sub_abs_le_abs_sub B yb; rw [abs_sub_comm] at eb; linarith
    have hyb0 : 0 < |yb| := lt_of_lt_of_le hd hyb
    have hB0 : 0 < |B| := by linarith
    have hyb' : yb ≠ 0 := abs_pos.mp hyb0
    have hB' : B ≠ 0 := abs_pos.mp hB0
    have hq : |ya/yb-A/B| ≤ (Ba+|A/B| *Bb)/(|B|-Bb) := by
      rw [show ya/yb-A/B = ((ya-A)-(A/B)*(yb-B))/yb by field_simp; ring,abs_div,
        div_le_div_iff₀ hyb0 hd]
      have h1 := abs_sub ((ya-A)) ((A/B)*(yb-B))
      rw [abs_mul] at h1
      have h2 : |ya-A|+|A/B| *|yb-B| ≤ Ba+|A/B| *Bb := by nlinarith [abs_nonneg (A/B)]
      have h3 : 0 ≤ Ba+|A/B| *Bb := by positivity
      nlinarith
    have hyq : |ya/yb| ≤ (|A|+Ba)/(|B|-Bb) := by
      rw [abs_div]
      have := abs_sub_abs_le_abs_sub ya A
      exact div_le_div₀ (by positivity) (by linarith) hd hyb
    unfold Wgsl.Div at hy
    have hU : 5*u = U := rfl
    rw [hU] at hy
    have hU0 := U_pos
    calc |y-A/B| ≤ |y-ya/yb|+|ya/yb-A/B| := abs_sub_le _ _ _
      _ ≤ _ := by nlinarith [abs_nonneg (ya/yb)]
  | sqrt a, v, w, E, hw, y, hs, h => by
    obtain ⟨ya,ha,hy⟩ := h
    obtain ⟨sa,hpos,hle⟩ := hs
    have ea := error a v w E hw ya sa ha
    simp only [exact,bound]
    set A := exact v a; set Ba := bound v E a
    have hya : 0 ≤ ya := by have := (abs_le.mp ea).1; linarith
    have hl := sqrt_lip hya hpos
    have hs1 : Real.sqrt ya ≤ Real.sqrt (A+Ba) := Real.sqrt_le_sqrt (by have := (abs_le.mp ea).2; linarith)
    have hq : |ya-A|/Real.sqrt A ≤ Ba/Real.sqrt A :=
      div_le_div_of_nonneg_right ea (Real.sqrt_nonneg _)
    have hu := u_pos
    calc |y-Real.sqrt A| ≤ |y-Real.sqrt ya|+|Real.sqrt ya-Real.sqrt A| := abs_sub_le _ _ _
      _ ≤ _ := by nlinarith
  | max a b, v, w, E, hw, y, hs, h => by
    obtain ⟨ya,yb,ha,hb,rfl⟩ := h
    have ea := error a v w E hw ya hs.1 ha
    have eb := error b v w E hw yb hs.2 hb
    simp only [exact,bound]
    exact (max_lip _ _ _ _).trans (max_le_max ea eb)
  | min a b, v, w, E, hw, y, hs, h => by
    obtain ⟨ya,yb,ha,hb,rfl⟩ := h
    have ea := error a v w E hw ya hs.1 ha
    have eb := error b v w E hw yb hs.2 hb
    simp only [exact,bound]
    exact (min_lip _ _ _ _).trans (max_le_max ea eb)
  | lt c t a b, v, w, E, hw, y, hs, h => by
    obtain ⟨sc,sa,sb,hsep⟩ := hs
    obtain ⟨yc,hc,hbr⟩ := h
    have ec := error c v w E hw yc sc hc
    simp only [exact,bound]
    by_cases hct : exact v c < t
    · have hyc : yc < t := by
        have := (abs_le.mp ec).2
        rw [abs_of_neg (by linarith)] at hsep
        linarith
      rcases hbr with ⟨-,hy⟩ | ⟨hn,-⟩
      · simp only [hct,↓reduceIte]; exact error a v w E hw y sa hy
      · exact absurd hyc hn
    · have hyc : ¬ yc < t := by
        have := (abs_le.mp ec).1
        rw [abs_of_nonneg (by linarith)] at hsep
        intro h'; linarith
      rcases hbr with ⟨h',-⟩ | ⟨-,hy⟩
      · exact absurd h' hyc
      · simp only [hct,↓reduceIte]; exact error b v w E hw y sb hy

  | abs a, v, w, E, hw, y, hs, h => by
    obtain ⟨ya,ha,rfl⟩ := h
    have ea := error a v w E hw ya hs ha
    simp only [exact,bound]
    exact (abs_abs_sub_abs_le_abs_sub ya (exact v a)).trans ea
  | invsqrt a, v, w, E, hw, y, hs, h => by
    obtain ⟨ya,ha,hy⟩ := h
    obtain ⟨sa,hlt⟩ := hs
    have ea := error a v w E hw ya sa ha
    simp only [exact,bound]
    set A := exact v a; set Ba := bound v E a
    have hBa : 0 ≤ Ba := (abs_nonneg _).trans ea
    have hlo : A-Ba ≤ ya := by have := (abs_le.mp ea).1; linarith
    have hpos : 0 < A-Ba := by linarith
    have hya : 0 < ya := lt_of_lt_of_le hpos hlo
    have hA : 0 < A := by linarith
    have s1 : Real.sqrt (A-Ba) ≤ Real.sqrt ya := Real.sqrt_le_sqrt hlo
    have s0 := Real.sqrt_pos.mpr hpos
    have sA := Real.sqrt_pos.mpr hA
    have hl := invsqrt_eq hya hA
    unfold InvSqrt at hy
    have t1 : 4*u*(1/Real.sqrt ya) ≤ 4*u/Real.sqrt (A-Ba) := by
      rw [mul_one_div]; exact div_le_div_of_nonneg_left (by have := u_pos; positivity) s0 s1
    have t2 : |1/Real.sqrt ya-1/Real.sqrt A| ≤
        Ba/(Real.sqrt (A-Ba)*Real.sqrt A*(Real.sqrt (A-Ba)+Real.sqrt A)) := by
      rw [hl]
      exact div_le_div₀ hBa ea (by positivity) (by gcongr)
    calc |y-1/Real.sqrt A| ≤ |y-1/Real.sqrt ya|+|1/Real.sqrt ya-1/Real.sqrt A| := abs_sub_le _ _ _
      _ ≤ _ := by linarith
  | exp a, v, w, E, hw, y, hs, h => by
    obtain ⟨ya,ha,hy⟩ := h
    have ea := error a v w E hw ya hs ha
    simp only [exact,bound]
    set A := exact v a; set Ba := bound v E a
    have hya : |ya| ≤ |A|+Ba := by have := abs_sub_abs_le_abs_sub ya A; linarith
    have hle : ya ≤ A+Ba := by have := (abs_le.mp ea).2; linarith
    have e1 : Real.exp ya ≤ Real.exp (A+Ba) := Real.exp_le_exp.mpr hle
    have hl := exp_lip ya A
    have e2 : Real.exp |ya-A| ≤ Real.exp Ba := Real.exp_le_exp.mpr ea
    unfold ulp at hy
    rw [abs_of_pos (Real.exp_pos ya)] at hy
    have hu := u_pos; have hη := η_pos
    have hBa : 0 ≤ Ba := (abs_nonneg _).trans ea
    have t1 : (3+2*|ya|)*(2*u*Real.exp ya+η) ≤ (3+2*(|A|+Ba))*(2*u*Real.exp (A+Ba)+η) :=
      mul_le_mul (by linarith) (by nlinarith) (by positivity) (by positivity)
    have t2 : Real.exp A*(Real.exp |ya-A|-1) ≤ Real.exp A*(Real.exp Ba-1) := by
      gcongr
    calc |y-Real.exp A| ≤ |y-Real.exp ya|+|Real.exp ya-Real.exp A| := abs_sub_le _ _ _
      _ ≤ _ := by linarith
  | exp2 a, v, w, E, hw, y, hs, h => by
    obtain ⟨ya,ha,hy⟩ := h
    have ea := error a v w E hw ya hs ha
    simp only [exact,bound]
    set A := exact v a; set Ba := bound v E a
    have hl2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
    have hya : |ya| ≤ |A|+Ba := by have := abs_sub_abs_le_abs_sub ya A; linarith
    have hle : ya ≤ A+Ba := by have := (abs_le.mp ea).2; linarith
    have e1 : exp2R ya ≤ exp2R (A+Ba) := Real.exp_le_exp.mpr (by nlinarith)
    have hl : |exp2R ya-exp2R A| ≤ exp2R A*(exp2R |ya-A|-1) := by
      have := exp_lip (ya*Real.log 2) (A*Real.log 2)
      rw [show ya*Real.log 2-A*Real.log 2 = (ya-A)*Real.log 2 by ring,abs_mul,
        abs_of_pos hl2] at this
      exact this
    have e2 : exp2R |ya-A| ≤ exp2R Ba := Real.exp_le_exp.mpr (by nlinarith)
    unfold ulp at hy
    rw [abs_of_pos (show 0 < exp2R ya from Real.exp_pos _)] at hy
    have hu := u_pos; have hη := η_pos
    have hBa : 0 ≤ Ba := (abs_nonneg _).trans ea
    have h2pos : 0 < exp2R ya := Real.exp_pos _
    have t1 : (3+2*|ya|)*(2*u*exp2R ya+η) ≤ (3+2*(|A|+Ba))*(2*u*exp2R (A+Ba)+η) :=
      mul_le_mul (by linarith) (by nlinarith) (by positivity) (by positivity)
    have t2 : exp2R A*(exp2R |ya-A|-1) ≤ exp2R A*(exp2R Ba-1) := by
      have := Real.exp_pos (A*Real.log 2)
      have := e2
      unfold exp2R at *
      gcongr
    calc |y-exp2R A| ≤ |y-exp2R ya|+|exp2R ya-exp2R A| := abs_sub_le _ _ _
      _ ≤ _ := by linarith
  | log a, v, w, E, hw, y, hs, h => by
    obtain ⟨ya,ha,hy⟩ := h
    obtain ⟨sa,hlt⟩ := hs
    have ea := error a v w E hw ya sa ha
    simp only [exact,bound]
    set A := exact v a; set Ba := bound v E a
    have hBa : 0 ≤ Ba := (abs_nonneg _).trans ea
    have hlo : A-Ba ≤ ya := by have := (abs_le.mp ea).1; linarith
    have hpos : 0 < A-Ba := by linarith
    have hya : 0 < ya := lt_of_lt_of_le hpos hlo
    have hA : 0 < A := by linarith
    have hm : A-Ba ≤ Min.min ya A := le_min hlo (by linarith)
    have hl : |Real.log ya-Real.log A| ≤ Ba/(A-Ba) :=
      (log_lip hya hA).trans (div_le_div₀ hBa ea hpos hm)
    have hlog : |Real.log ya| ≤ |Real.log A|+Ba/(A-Ba) := by
      have := abs_sub_abs_le_abs_sub (Real.log ya) (Real.log A); linarith
    unfold ulp at hy
    have hu := u_pos; have hη := η_pos
    calc |y-Real.log A| ≤ |y-Real.log ya|+|Real.log ya-Real.log A| := abs_sub_le _ _ _
      _ ≤ _ := by nlinarith
  | log2 a, v, w, E, hw, y, hs, h => by
    obtain ⟨ya,ha,hy⟩ := h
    obtain ⟨sa,hlt⟩ := hs
    have ea := error a v w E hw ya sa ha
    simp only [exact,bound]
    set A := exact v a; set Ba := bound v E a
    have hl2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
    have hBa : 0 ≤ Ba := (abs_nonneg _).trans ea
    have hlo : A-Ba ≤ ya := by have := (abs_le.mp ea).1; linarith
    have hpos : 0 < A-Ba := by linarith
    have hya : 0 < ya := lt_of_lt_of_le hpos hlo
    have hA : 0 < A := by linarith
    have hm : A-Ba ≤ Min.min ya A := le_min hlo (by linarith)
    have hl0 : |Real.log ya-Real.log A| ≤ Ba/(A-Ba) :=
      (log_lip hya hA).trans (div_le_div₀ hBa ea hpos hm)
    have hl : |log2R ya-log2R A| ≤ Ba/((A-Ba)*Real.log 2) := by
      unfold log2R
      rw [← sub_div,abs_div,abs_of_pos hl2,div_le_div_iff₀ hl2 (by positivity)]
      have := (le_div_iff₀ hpos).mp hl0
      nlinarith
    have hlog : |log2R ya| ≤ |log2R A|+Ba/((A-Ba)*Real.log 2) := by
      have := abs_sub_abs_le_abs_sub (log2R ya) (log2R A); linarith
    unfold ulp at hy
    have hu := u_pos; have hη := η_pos
    calc |y-log2R A| ≤ |y-log2R ya|+|log2R ya-log2R A| := abs_sub_le _ _ _
      _ ≤ _ := by nlinarith
  | inh f a, v, w, E, hw, y, hs, h => by
    obtain ⟨ya,ha,hy⟩ := h
    obtain ⟨sa,sf⟩ := hs
    have ea := error a v w E hw ya sa ha
    simp only [exact,bound]
    exact error f (fun _ => exact v a) (fun _ => ya) (fun _ => bound v E a) (fun _ => ea) y sf hy
  | tanh f a, v, w, E, hw, y, hs, h => by
    obtain ⟨ya,ha,hy⟩ := h
    obtain ⟨sa,sf,hid⟩ := hs
    have ea := error a v w E hw ya sa ha
    simp only [exact,bound]
    rcases hy with hy | hy
    · have := tanh_lip ya (exact v a)
      calc |y-Real.tanh (exact v a)| ≤ |y-Real.tanh ya|+|Real.tanh ya-Real.tanh (exact v a)| :=
            abs_sub_le _ _ _
        _ ≤ bound v E a+1/10^5 := by linarith
        _ ≤ _ := le_max_left _ _
    · have hf := error f (fun _ => exact v a) (fun _ => ya) (fun _ => bound v E a) (fun _ => ea) y sf hy
      rw [hid] at hf
      exact hf.trans (le_max_right _ _)

  | lt2 a b x y, v, w, E, hw, r, hs, h => by
    obtain ⟨sa,sb,sx,sy,hsep⟩ := hs
    obtain ⟨ya,yb,ha,hb,hbr⟩ := h
    have ea := error a v w E hw ya sa ha
    have eb := error b v w E hw yb sb hb
    have ha' := abs_le.mp ea
    have hb' := abs_le.mp eb
    simp only [exact,bound]
    by_cases hab : exact v a < exact v b
    · have hy : ya < yb := by
        rw [abs_of_neg (by linarith)] at hsep
        linarith
      rcases hbr with ⟨-,hr⟩ | ⟨hn,-⟩
      · simp only [hab,↓reduceIte]; exact error x v w E hw r sx hr
      · exact absurd hy hn
    · have hy : ¬ ya < yb := by
        rw [abs_of_nonneg (by linarith)] at hsep
        intro h'; linarith
      rcases hbr with ⟨h',-⟩ | ⟨-,hr⟩
      · exact absurd h' hy
      · simp only [hab,↓reduceIte]; exact error y v w E hw r sy hr

  | sinS a, v, w, E, hw, y, hs, h => by
    obtain ⟨ya,out,ha,hsc,rfl⟩ := h
    obtain ⟨sa,hrange⟩ := hs
    have ea := error a v w E hw ya sa ha
    simp only [exact,bound]
    have hya : |ya| ≤ |exact v a|+bound v E a := by
      have := abs_sub_abs_le_abs_sub ya (exact v a); linarith
    have hspec := (sincos_spec hsc (hya.trans hrange)).1
    have hlip : |Real.sin ya-Real.sin (exact v a)| ≤ |ya-exact v a| := Real.abs_sin_sub_sin_le _ _
    have hu := u_pos
    have : 128*u*(1+|ya|) ≤ 128*u*(1+(|exact v a|+bound v E a)) := by gcongr
    calc |out.1-Real.sin (exact v a)| ≤ |out.1-Real.sin ya|+|Real.sin ya-Real.sin (exact v a)| :=
          abs_sub_le _ _ _
      _ ≤ _ := by linarith
  | cosS a, v, w, E, hw, y, hs, h => by
    obtain ⟨ya,out,ha,hsc,rfl⟩ := h
    obtain ⟨sa,hrange⟩ := hs
    have ea := error a v w E hw ya sa ha
    simp only [exact,bound]
    have hya : |ya| ≤ |exact v a|+bound v E a := by
      have := abs_sub_abs_le_abs_sub ya (exact v a); linarith
    have hspec := (sincos_spec hsc (hya.trans hrange)).2
    have hlip : |Real.cos ya-Real.cos (exact v a)| ≤ |ya-exact v a| := Real.abs_cos_sub_cos_le _ _
    have hu := u_pos
    have : 128*u*(1+|ya|) ≤ 128*u*(1+(|exact v a|+bound v E a)) := by gcongr
    calc |out.2-Real.cos (exact v a)| ≤ |out.2-Real.cos ya|+|Real.cos ya-Real.cos (exact v a)| :=
          abs_sub_le _ _ _
      _ ≤ _ := by linarith

end GExpr

end BlackHole.WgslExpr
