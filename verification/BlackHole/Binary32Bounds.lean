module

public import BlackHole.Orbits
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! All-input binary32 error bounds for `src/physics.rs`.

Rounding is the IEEE 754 standard model for round-to-nearest binary32 without
overflow: every `+`, `-`, `*`, `/` and `sqrt` result `y` of an exact operation
on computed operands `x` satisfies `|y - x| ≤ u|x| + η`, with `u = 2⁻²⁴` and
`η = 2⁻¹⁴⁹` covering gradual underflow. Rust guarantees correctly rounded
`f32` arithmetic and `sqrt` and does not contract them into fused operations.
Rust does not specify `cbrt`; its result is modelled by a separate relative
error `cbrtError = 2⁻²³` (one unit in the last place), which
`tests/exhaustive_binary32.rs` checks for every input the ISCO uses.

The clamp limit is the binary32 value nearest 0.999, `16760439 / 2²⁴`. NaN and
infinite spins are handled exhaustively in Rust; after `abs`/`min`/`clamp`
every finite result lies in the domains below. -/

@[expose] public section
noncomputable section

namespace BlackHole.Binary32

/-- Unit roundoff of binary32 round-to-nearest. -/
def u : ℝ := 1/2^24
/-- Absolute rounding allowance covering subnormal results. -/
def η : ℝ := 1/2^149
/-- Relative error admitted for the platform `cbrtf`. -/
def cbrtError : ℝ := 1/2^23
/-- `0.999_f32`, the production spin limit, as an exact rational. -/
def spinLimit : ℝ := 16760439/2^24

/-- One correctly rounded operation whose exact result, on computed operands, is `x`. -/
def Rounded (x y : ℝ) : Prop := |y - x| ≤ u*|x|+η

/-- A platform cube root of a positive computed value. -/
def CubeRooted (x y : ℝ) : Prop := |y - x^(1/3 : ℝ)| ≤ cbrtError*x^(1/3 : ℝ)

/-- `y` approximates the nonnegative exact value `x` with relative error `e`
    and absolute error `d`. -/
def Approx (y x e d : ℝ) : Prop := |y - x| ≤ e*x+d

lemma u_pos : 0 < u := by norm_num [u]
lemma η_pos : 0 < η := by norm_num [η]

namespace Approx

lemma exact (x : ℝ) : Approx x x 0 0 := by simp [Approx]

lemma mono {y x e d e' d' : ℝ} (h : Approx y x e d) (hx : 0 ≤ x)
    (he : e ≤ e') (hd : d ≤ d') : Approx y x e' d' := by
  unfold Approx at *
  nlinarith

/-- Fold the absolute error into the relative error above a positive floor. -/
lemma fold {y x e d m : ℝ} (h : Approx y x e d) (hm : 0 < m) (hmx : m ≤ x)
    (hd : 0 ≤ d) : Approx y x (e+d/m) 0 := by
  unfold Approx at *
  have : d ≤ d/m*x := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hm]
    nlinarith
  nlinarith

lemma round {z x y e d : ℝ} (h : Approx z x e d) (hx : 0 ≤ x) (_he : 0 ≤ e)
    (_hd : 0 ≤ d) (hr : Rounded z y) : Approx y x (e+u+u*e) (d*(1+u)+η) := by
  unfold Approx Rounded at *
  have hu := u_pos
  have hz : |z| ≤ x+e*x+d := by
    have := abs_sub_abs_le_abs_sub z x
    rw [abs_of_nonneg hx] at this
    linarith
  have hyz := abs_sub_le y z x
  nlinarith [abs_nonneg z, mul_le_mul_of_nonneg_left hz hu.le]

lemma add {y₁ x₁ e₁ d₁ y₂ x₂ e₂ d₂ e : ℝ} (h₁ : Approx y₁ x₁ e₁ d₁)
    (h₂ : Approx y₂ x₂ e₂ d₂) (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂)
    (he₁ : e₁ ≤ e) (he₂ : e₂ ≤ e) : Approx (y₁+y₂) (x₁+x₂) e (d₁+d₂) := by
  unfold Approx at *
  have := abs_add_le (y₁-x₁) (y₂-x₂)
  rw [show y₁+y₂-(x₁+x₂) = (y₁-x₁)+(y₂-x₂) by ring]
  nlinarith

lemma mul {y₁ x₁ e₁ d₁ y₂ x₂ e₂ d₂ X Y : ℝ} (h₁ : Approx y₁ x₁ e₁ d₁)
    (h₂ : Approx y₂ x₂ e₂ d₂) (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂)
    (hX : x₁ ≤ X) (hY : x₂ ≤ Y) (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂)
    (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) :
    Approx (y₁*y₂) (x₁*x₂) (e₁+e₂+e₁*e₂) (e₁*X*d₂+d₁*Y*(1+e₂)+d₁*d₂+X*d₂) := by
  unfold Approx at *
  have hy₂ : |y₂| ≤ x₂*(1+e₂)+d₂ := by
    have := abs_sub_abs_le_abs_sub y₂ x₂
    rw [abs_of_nonneg hx₂] at this
    linarith
  have key : |y₁*y₂-x₁*x₂| ≤ |y₁-x₁| *|y₂|+x₁*|y₂-x₂| := by
    rw [show y₁*y₂-x₁*x₂ = (y₁-x₁)*y₂+x₁*(y₂-x₂) by ring]
    calc _ ≤ |(y₁-x₁)*y₂|+|x₁*(y₂-x₂)| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg hx₁]
  have t₁ : |y₁-x₁| *|y₂| ≤ (e₁*x₁+d₁)*(x₂*(1+e₂)+d₂) :=
    mul_le_mul h₁ hy₂ (abs_nonneg _) (by positivity)
  have t₂ : x₁*|y₂-x₂| ≤ x₁*(e₂*x₂+d₂) := mul_le_mul_of_nonneg_left h₂ hx₁
  have b₁ : e₁*x₁*d₂ ≤ e₁*X*d₂ := by
    have := mul_le_mul_of_nonneg_left hX he₁
    nlinarith
  have b₂ : d₁*x₂*(1+e₂) ≤ d₁*Y*(1+e₂) := by
    have := mul_le_mul_of_nonneg_left hY hd₁
    nlinarith
  have b₃ : x₁*d₂ ≤ X*d₂ := mul_le_mul_of_nonneg_right hX hd₂
  nlinarith

lemma div {y₁ x₁ e₁ d₁ y₂ x₂ e₂ d₂ X m : ℝ} (h₁ : Approx y₁ x₁ e₁ d₁)
    (h₂ : Approx y₂ x₂ e₂ d₂) (hx₁ : 0 ≤ x₁) (hX : x₁ ≤ X) (hm : 0 < m)
    (hmx : m ≤ x₂) (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂)
    (hk : 0 < 1-e₂-d₂/m) :
    Approx (y₁/y₂) (x₁/x₂) ((e₁+e₂)/(1-e₂-d₂/m))
      (d₁/((1-e₂-d₂/m)*m)+X*d₂/((1-e₂-d₂/m)*m^2)) := by
  unfold Approx at *
  set k := 1-e₂-d₂/m with hkdef
  have hx₂ : 0 < x₂ := lt_of_lt_of_le hm hmx
  have hdm : d₂ ≤ d₂/m*x₂ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hm]
    nlinarith
  have hy₂ : k*x₂ ≤ y₂ := by
    have := neg_abs_le (y₂-x₂)
    have : k*x₂ = x₂-e₂*x₂-d₂/m*x₂ := by rw [hkdef]; ring
    nlinarith
  have hy₂pos : 0 < y₂ := lt_of_lt_of_le (by positivity) hy₂
  have hden : k*x₂^2 ≤ y₂*x₂ := by nlinarith
  have hnum : |y₁*x₂-x₁*y₂| ≤ (e₁+e₂)*x₁*x₂+d₁*x₂+x₁*d₂ := by
    rw [show y₁*x₂-x₁*y₂ = (y₁-x₁)*x₂-x₁*(y₂-x₂) by ring]
    calc _ ≤ |(y₁-x₁)*x₂|+|x₁*(y₂-x₂)| := abs_sub _ _
      _ = |y₁-x₁| *x₂+x₁*|y₂-x₂| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hx₁, abs_of_pos hx₂]
      _ ≤ (e₁*x₁+d₁)*x₂+x₁*(e₂*x₂+d₂) := by
        gcongr
      _ = _ := by ring
  have hq : y₁/y₂-x₁/x₂ = (y₁*x₂-x₁*y₂)/(y₂*x₂) := by
    field_simp
  rw [hq, abs_div, abs_of_pos (mul_pos hy₂pos hx₂), div_le_iff₀ (mul_pos hy₂pos hx₂)]
  -- Bound each term of the numerator by the corresponding term of the target.
  have hxm : x₁/x₂ ≤ X/m := by
    apply div_le_div₀ (by linarith) hX hm hmx
  have t₁ : (e₁+e₂)*x₁*x₂ ≤ (e₁+e₂)/k*(x₁/x₂)*(y₂*x₂) := by
    have : (e₁+e₂)/k*(x₁/x₂)*(k*x₂^2) = (e₁+e₂)*x₁*x₂ := by
      field_simp
    rw [← this]
    apply mul_le_mul_of_nonneg_left hden
    positivity
  have t₂ : d₁*x₂ ≤ d₁/(k*m)*(y₂*x₂) := by
    have : d₁/(k*m)*(k*x₂*x₂) = d₁*x₂*(x₂/m) := by
      field_simp
    have h1 : d₁*x₂ ≤ d₁*x₂*(x₂/m) := by
      have : 1 ≤ x₂/m := by rw [le_div_iff₀ hm]; linarith
      nlinarith [mul_nonneg hd₁ hx₂.le]
    have h2 : d₁/(k*m)*(k*x₂*x₂) ≤ d₁/(k*m)*(y₂*x₂) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    linarith
  have t₃ : x₁*d₂ ≤ X*d₂/(k*m^2)*(y₂*x₂) := by
    have h1 : X*d₂/(k*m^2)*(k*x₂^2) = X*d₂*(x₂/m)^2 := by
      field_simp
    have h2 : x₁*d₂ ≤ X*d₂*(x₂/m)^2 := by
      have h1m : 1 ≤ x₂/m := by rw [le_div_iff₀ hm]; linarith
      have hq1 : 1 ≤ (x₂/m)^2 := one_le_pow₀ h1m
      have hX0 : 0 ≤ X := le_trans hx₁ hX
      have : X ≤ X*(x₂/m)^2 := le_mul_of_one_le_right hX0 hq1
      have : x₁ ≤ X*(x₂/m)^2 := le_trans hX this
      calc x₁*d₂ ≤ X*(x₂/m)^2*d₂ := mul_le_mul_of_nonneg_right this hd₂
        _ = _ := by ring
    have h3 : X*d₂/(k*m^2)*(k*x₂^2) ≤ X*d₂/(k*m^2)*(y₂*x₂) := by
      apply mul_le_mul_of_nonneg_left hden
      have : 0 ≤ X := le_trans hx₁ hX
      positivity
    linarith
  nlinarith

/-- Square-root perturbation for a purely relative error; the relative error
    roughly halves. -/
lemma sqrt_rel {y x e : ℝ} (h : Approx y x e 0) (hx : 0 ≤ x) (he : 0 ≤ e) (he1 : e < 1) :
    Approx (Real.sqrt y) (Real.sqrt x) (e/(2-e)) 0 := by
  unfold Approx at *
  rw [add_zero] at *
  have hyx : (1-e)*x ≤ y := by
    have := neg_abs_le (y-x)
    nlinarith
  have hy : 0 ≤ y := le_trans (by nlinarith) hyx
  rcases eq_or_lt_of_le hx with hx0 | hxpos
  · subst hx0
    have : y = 0 := by
      have h0 : |y-0| ≤ 0 := by simpa using h
      simpa using abs_nonpos_iff.mp h0
    simp [this]
  have hsx := Real.sqrt_pos.mpr hxpos
  have hsy := Real.sqrt_nonneg y
  -- √y ≥ (1-e)√x.
  have hlow : (1-e)*Real.sqrt x ≤ Real.sqrt y := by
    have h1 : ((1-e)*Real.sqrt x)^2 ≤ y := by
      rw [mul_pow, Real.sq_sqrt hx]
      nlinarith
    calc (1-e)*Real.sqrt x = Real.sqrt (((1-e)*Real.sqrt x)^2) := by
          rw [Real.sqrt_sq (by nlinarith)]
      _ ≤ _ := Real.sqrt_le_sqrt h1
  have hprod : (Real.sqrt y-Real.sqrt x)*(Real.sqrt y+Real.sqrt x) = y-x := by
    nlinarith [Real.sq_sqrt hy, Real.sq_sqrt hx]
  have hsum : (2-e)*Real.sqrt x ≤ Real.sqrt y+Real.sqrt x := by linarith
  have hpos : 0 < (2-e)*Real.sqrt x := by
    apply mul_pos (by linarith) hsx
  have habs : |Real.sqrt y-Real.sqrt x| *(Real.sqrt y+Real.sqrt x) = |y-x| := by
    rw [← hprod, abs_mul, abs_of_pos (by linarith : 0 < Real.sqrt y+Real.sqrt x)]
  have key : |Real.sqrt y-Real.sqrt x| *((2-e)*Real.sqrt x) ≤ e*x := by
    calc _ ≤ |Real.sqrt y-Real.sqrt x| *(Real.sqrt y+Real.sqrt x) :=
          mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
      _ = |y-x| := habs
      _ ≤ e*x := h
  have : e*x = e/(2-e)*Real.sqrt x*((2-e)*Real.sqrt x) := by
    have : (2-e) ≠ 0 := by linarith
    field_simp
    rw [Real.sq_sqrt hx]
  rw [this] at key
  exact le_of_mul_le_mul_right key hpos

/-- Square-root perturbation with an absolute part: the result's absolute error
    is at most `D` whenever `2d ≤ D²`. -/
lemma sqrt_abs {y x e d D : ℝ} (h : Approx y x e d) (hx : 0 ≤ x) (he : 0 ≤ e)
    (he1 : 2*e < 1) (_hd : 0 ≤ d) (hD : 0 ≤ D) (hdD : 2*d ≤ D^2) :
    Approx (Real.sqrt y) (Real.sqrt x) (e/(1-e)) D := by
  by_cases hcase : d ≤ e*x
  · have h' : Approx y x (2*e) 0 := by unfold Approx at *; linarith
    have := sqrt_rel h' hx (by linarith) he1
    have hfrac : 2*e/(2-2*e) = e/(1-e) := by
      rw [show 2-2*e = 2*(1-e) by ring, mul_div_mul_left _ _ (by norm_num : (2:ℝ) ≠ 0)]
    rw [hfrac] at this
    exact mono this (Real.sqrt_nonneg _) le_rfl hD
  · push Not at hcase
    unfold Approx at *
    have hδ : |y-x| ≤ D^2 := by linarith
    -- (√y - √x)² ≤ |y - x|.
    have hsq : (Real.sqrt y-Real.sqrt x)^2 ≤ |y-x| := by
      rcases le_or_gt 0 y with hy | hy
      · have hprod : (Real.sqrt y-Real.sqrt x)*(Real.sqrt y+Real.sqrt x) = y-x := by
          nlinarith [Real.sq_sqrt hy, Real.sq_sqrt hx]
        have h1 : (Real.sqrt y-Real.sqrt x)^2 ≤
            |Real.sqrt y-Real.sqrt x| *(Real.sqrt y+Real.sqrt x) := by
          rw [sq, ← abs_mul_abs_self]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          rw [abs_le]
          constructor <;> nlinarith [Real.sqrt_nonneg y, Real.sqrt_nonneg x]
        calc _ ≤ _ := h1
          _ = |(Real.sqrt y-Real.sqrt x)*(Real.sqrt y+Real.sqrt x)| := by
            rw [abs_mul, abs_of_nonneg (by positivity :
              0 ≤ Real.sqrt y+Real.sqrt x)]
          _ = _ := by rw [hprod]
      · rw [Real.sqrt_eq_zero'.mpr hy.le]
        have : |y-x| = x-y := by rw [abs_of_neg (by linarith)]; ring
        rw [this]
        nlinarith [Real.sq_sqrt hx]
    have : |Real.sqrt y-Real.sqrt x| ≤ D := by
      rw [← Real.sqrt_sq hD, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by linarith)
    have : 0 ≤ e/(1-e)*Real.sqrt x := by
      apply mul_nonneg (div_nonneg he (by linarith)) (Real.sqrt_nonneg _)
    linarith

/-- Cube-root perturbation followed by the platform cube root. -/
lemma cbrt {y x z e : ℝ} (h : Approx y x e 0) (hx : 0 < x) (he : 0 ≤ e) (he1 : e < 1)
    (hc : CubeRooted y z) :
    Approx z (x^(1/3 : ℝ)) (e+cbrtError+cbrtError*e) 0 := by
  unfold Approx CubeRooted at *
  have hy : 0 < y := by
    have := neg_abs_le (y-x)
    nlinarith
  set a := x^(1/3 : ℝ) with ha
  set b := y^(1/3 : ℝ) with hb
  have ha0 : 0 < a := Real.rpow_pos_of_pos hx _
  have hb0 : 0 < b := Real.rpow_pos_of_pos hy _
  have ha3 : a^3 = x := cubeRoot_cube x hx.le
  have hb3 : b^3 = y := cubeRoot_cube y hy.le
  have hfac : (b-a)*(b^2+b*a+a^2) = y-x := by rw [← ha3, ← hb3]; ring
  have hpos : 0 < b^2+b*a+a^2 := by positivity
  have hba : |b-a| ≤ e*a := by
    have h1 : |b-a| *(b^2+b*a+a^2) ≤ e*a*(b^2+b*a+a^2) := by
      rw [← abs_of_pos hpos, ← abs_mul, hfac, abs_of_pos hpos]
      calc |y-x| ≤ e*x+0 := h
        _ = e*a*a^2 := by rw [← ha3]; ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith [mul_pos hb0 ha0]
    exact le_of_mul_le_mul_right h1 hpos
  have hb_le : b ≤ (1+e)*a := by
    have := le_abs_self (b-a)
    nlinarith
  have hz := abs_sub_le z b a
  have : cbrtError*b ≤ cbrtError*((1+e)*a) :=
    mul_le_mul_of_nonneg_left hb_le (by norm_num [cbrtError])
  nlinarith

/-- The subtraction `3 - w` is well conditioned when `w ≤ 2`. -/
lemma three_sub {y x e d : ℝ} (h : Approx y x e d) (_hx : 0 ≤ x) (hx2 : x ≤ 2)
    (he : 0 ≤ e) : Approx (3-y) (3-x) (2*e) d := by
  unfold Approx at *
  rw [show 3-y-(3-x) = -(y-x) by ring, abs_neg]
  nlinarith

/-- Round, then fold the absolute error into the relative error above `m`. -/
lemma roundFold {z x y e d m : ℝ} (h : Approx z x e d) (hm : 0 < m) (hmx : m ≤ x)
    (he : 0 ≤ e) (hd : 0 ≤ d) (hr : Rounded z y) :
    Approx y x (e+u+u*e+(d*(1+u)+η)/m) 0 := by
  have hx : 0 ≤ x := le_trans hm.le hmx
  have h1 := round h hx he hd hr
  have h2 := fold h1 hm hmx (by have := u_pos; have := η_pos; positivity)
  exact mono h2 hx (by linarith) le_rfl

end Approx

/-! ### Horizon -/

/-- `|√m - √t| ≤ |m - t| / √t` for positive `t`, including negative `m`. -/
lemma sqrt_sub_le (m t : ℝ) (ht : 0 < t) :
    |Real.sqrt m-Real.sqrt t| ≤ |m-t|/Real.sqrt t := by
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  rw [le_div_iff₀ hst]
  rcases le_or_gt 0 m with hm0 | hm0
  · have hprod : (Real.sqrt m-Real.sqrt t)*(Real.sqrt m+Real.sqrt t) = m-t := by
      nlinarith [Real.sq_sqrt hm0, Real.sq_sqrt ht.le]
    have : |Real.sqrt m-Real.sqrt t| *(Real.sqrt m+Real.sqrt t) = |m-t| := by
      rw [← hprod, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt m+Real.sqrt t)]
    nlinarith [abs_nonneg (Real.sqrt m-Real.sqrt t), Real.sqrt_nonneg m]
  · rw [Real.sqrt_eq_zero'.mpr hm0.le, zero_sub, abs_neg, abs_of_pos hst,
      ← sq, Real.sq_sqrt ht.le]
    have := le_abs_self (t-m)
    rw [abs_sub_comm] at this
    linarith

/-- `kerr_horizon_radius_rg`: `1 + sqrt(1 - a*a)` with every operation rounded.
    For every clamped binary32 input the absolute error, and hence the relative
    error since `r₊ ≥ 1`, is at most 32 units of roundoff (`1.9·10⁻⁶`). -/
theorem horizon_error (a p m s h : ℝ) (ha : 0 ≤ a) (haA : a ≤ spinLimit)
    (hp : Rounded (a*a) p) (hm : Rounded (1-p) m) (hs : Rounded (Real.sqrt m) s)
    (hh : Rounded (1+s) h) :
    |h-(1+Real.sqrt (1-a*a))| ≤ 32*u := by
  unfold Rounded at hp hm hs hh
  have hu := u_pos
  have hη := η_pos
  have haa : 0 ≤ a*a := mul_self_nonneg a
  have haa1 : a*a ≤ 500/501 := by
    have h1 : spinLimit*spinLimit ≤ 500/501 := by norm_num [spinLimit]
    have h2 : a*a ≤ spinLimit*spinLimit := mul_le_mul haA haA ha (le_trans ha haA)
    linarith
  set t := 1-a*a with ht
  have htmin : 1/501 ≤ t := by linarith
  have htpos : 0 < t := by linarith
  rw [abs_of_nonneg haa] at hp
  have hp1 : |1-p| ≤ t+u*(a*a)+η := by
    have : |1-p| ≤ |t|+|p-a*a| := by
      calc |1-p| = |t-(p-a*a)| := by rw [ht]; ring_nf
        _ ≤ |t|+|p-a*a| := abs_sub _ _
    rw [abs_of_nonneg htpos.le] at this
    linarith
  have hmt : |m-t| ≤ (101/100)*u := by
    have e1 : |m-t| ≤ |m-(1-p)|+|p-a*a| := by
      calc |m-t| = |(m-(1-p))-(p-a*a)| := by rw [ht]; ring_nf
        _ ≤ _ := abs_sub _ _
    have e2 : u*|1-p| ≤ u*(t+u*(a*a)+η) := mul_le_mul_of_nonneg_left hp1 hu.le
    have e3 : u*(t+u*(a*a)+η) = u*t+u*u*(a*a)+u*η := by ring
    have e4 : u*t+u*(a*a) = u := by rw [ht]; ring
    have e5 : u*u*(a*a) ≤ u*u := by
      have : u*u*(a*a) ≤ u*u*1 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have e6 : u*u+u*η+2*η ≤ u/100 := by norm_num [u, η]
    linarith
  have hroot : |Real.sqrt m-Real.sqrt t| ≤ (101/100)*u*23 := by
    have h1 := sqrt_sub_le m t htpos
    have h2 : (1:ℝ)/23 ≤ Real.sqrt t := by
      rw [show (1:ℝ)/23 = Real.sqrt ((1/23)^2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    have h3 : |m-t|/Real.sqrt t ≤ (101/100)*u/(1/23) := by
      apply div_le_div₀ (by positivity) hmt (by norm_num) h2
    have : (101/100)*u/(1/23) = (101/100)*u*23 := by ring
    linarith
  have hst1 : Real.sqrt t ≤ 1 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsm : Real.sqrt m ≤ 1+1/1000 := by
    have := le_abs_self (Real.sqrt m-Real.sqrt t)
    have : (101/100)*u*23 ≤ 1/1000 := by norm_num [u]
    linarith
  have hsr : |s-Real.sqrt m| ≤ (1+1/1000)*u+η := by
    rw [abs_of_nonneg (Real.sqrt_nonneg m)] at hs
    nlinarith
  have hs1 : |1+s| ≤ 2+1/100 := by
    have h1 := abs_sub_abs_le_abs_sub s (Real.sqrt m)
    rw [abs_of_nonneg (Real.sqrt_nonneg m)] at h1
    have h2 := abs_add_le (1:ℝ) s
    have : (1+1/1000)*u+η ≤ 1/1000 := by norm_num [u, η]
    simp only [abs_one] at h2
    linarith
  have hhr : |h-(1+s)| ≤ (2+1/100)*u+η := by nlinarith
  calc |h-(1+Real.sqrt t)| = |(h-(1+s))+(s-Real.sqrt m)+(Real.sqrt m-Real.sqrt t)| := by
        ring_nf
    _ ≤ |h-(1+s)|+|s-Real.sqrt m|+|Real.sqrt m-Real.sqrt t| := abs_add_three _ _ _
    _ ≤ ((2+1/100)*u+η)+((1+1/1000)*u+η)+(101/100)*u*23 := by linarith
    _ ≤ 32*u := by norm_num [u, η]

/-! ### ISCO -/

/-- The cancellation-free form used by `kerr_isco_radius_rg`: with
    `q = ∛(1+a)`, `r = ∛(1-a)`, the Bardeen `3 - z₁` equals
    `(q+r)(2a/(q²+qr+r²))²`. -/
theorem iscoZ1_stable (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    let q := (1+a)^(1/3 : ℝ)
    let r := (1-a)^(1/3 : ℝ)
    let gap := 2*a/(q*q+q*r+r*r)
    iscoZ1 a = 3-(q+r)*gap*gap := by
  intro q r gap
  have hp : 0 ≤ 1+a := by linarith
  have hm : 0 ≤ 1-a := by linarith
  have hq3 : q^3 = 1+a := cubeRoot_cube _ hp
  have hr3 : r^3 = 1-a := cubeRoot_cube _ hm
  have hq0 : 0 ≤ q := Real.rpow_nonneg hp _
  have hr0 : 0 ≤ r := Real.rpow_nonneg hm _
  have hq1 : 1 ≤ q := by
    by_contra hc
    push Not at hc
    have : q^3 < 1 := by
      have := pow_lt_pow_left₀ hc hq0 (by norm_num : (3:ℕ) ≠ 0)
      simpa using this
    linarith
  have hS : 0 < q*q+q*r+r*r := by nlinarith [mul_nonneg hq0 hr0]
  have hgap : gap = q-r := by
    show 2*a/(q*q+q*r+r*r) = q-r
    rw [div_eq_iff hS.ne']
    linear_combination hr3-hq3
  have hprod : (1-|a| *|a|)^(1/3 : ℝ) = q*r := by
    rw [abs_of_nonneg ha, show 1-a*a = (1+a)*(1-a) by ring, Real.mul_rpow hp hm]
  unfold iscoZ1
  rw [hprod, hgap, abs_of_nonneg ha]
  linear_combination hq3+hr3

/-- The production evaluation order of the exact ISCO formula. -/
theorem isco_stable (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    let q := (1+a)^(1/3 : ℝ)
    let r := (1-a)^(1/3 : ℝ)
    let gap := 2*a/(q*q+q*r+r*r)
    let w := (q+r)*gap*gap
    let z1 := 3-w
    let z2 := Real.sqrt (3*a*a+z1*z1)
    isco a = 3+z2-Real.sqrt (w*(3+z1+2*z2)) ∧
      (0 < a → isco (-a) = 3+z2+Real.sqrt (w*(3+z1+2*z2))) := by
  intro q r gap w z1 z2
  have hz1 : iscoZ1 a = z1 := iscoZ1_stable a ha ha1
  have hz1n : iscoZ1 (-a) = z1 := by
    rw [← hz1]; unfold iscoZ1; rw [abs_neg]
  have hw : 3-iscoZ1 a = w := by rw [hz1]; ring
  have hz2 : iscoZ2 a = z2 := by
    unfold iscoZ2; rw [hz1, abs_of_nonneg ha, sq]
  have hz2n : iscoZ2 (-a) = z2 := by
    rw [← hz2]; unfold iscoZ2; rw [abs_neg, hz1n, hz1]
  constructor
  · unfold isco
    have hif : (if 0 ≤ a then (-1:ℝ) else 1) = -1 := by simp [ha]
    rw [hif, hz2, hw, hz1]
    ring
  · intro hpos
    unfold isco
    have hif : (if 0 ≤ -a then (-1:ℝ) else 1) = 1 := by
      simp only [ite_eq_right_iff]; intro h; linarith
    rw [hif, hz2n, hz1n, show 3-z1 = w by ring]
    ring

set_option maxHeartbeats 8000000 in
/-- `kerr_isco_radius_rg` evaluated in binary32 for the clamped magnitude
    `a = |spin|`. Each hypothesis is one Rust operation in source order;
    multiplication by the ±1 direction is exact. The prograde result
    (`spin = a ≥ 0`) has relative error at most `2048 u ≈ 1.2·10⁻⁴`; the
    retrograde result (`spin = -a < 0`) at most `256 u ≈ 1.5·10⁻⁵`. These are
    worst-case analytic bounds; the exhaustive platform check measures 18 u. -/
theorem isco_error (a : ℝ) (ha : 0 ≤ a) (haA : a ≤ spinLimit)
    (P M q r qq qr rr s1 s n g qp t w z1 a3 aa zz zi z2 u1 z22 u2 v sq b : ℝ)
    (hP : Rounded (1+a) P) (hM : Rounded (1-a) M)
    (hq : CubeRooted P q) (hr : CubeRooted M r)
    (hqq : Rounded (q*q) qq) (hqr : Rounded (q*r) qr) (hrr : Rounded (r*r) rr)
    (hs1 : Rounded (qq+qr) s1) (hs : Rounded (s1+rr) s)
    (hn : Rounded (2*a) n) (hg : Rounded (n/s) g)
    (hqp : Rounded (q+r) qp) (ht : Rounded (qp*g) t) (hw : Rounded (t*g) w)
    (hz1 : Rounded (3-w) z1) (ha3 : Rounded (3*a) a3) (haa : Rounded (a3*a) aa)
    (hzz : Rounded (z1*z1) zz) (hzi : Rounded (aa+zz) zi)
    (hz2 : Rounded (Real.sqrt zi) z2) (hu1 : Rounded (3+z1) u1)
    (hz22 : Rounded (2*z2) z22) (hu2 : Rounded (u1+z22) u2)
    (hv : Rounded (w*u2) v) (hsq : Rounded (Real.sqrt v) sq) (hb : Rounded (3+z2) b) :
    (∀ res, Rounded (b-sq) res → |res-isco a| ≤ 2048*u*isco a) ∧
      (0 < a → ∀ res, Rounded (b+sq) res → |res-isco (-a)| ≤ 256*u*isco (-a)) := by
  have hu := u_pos
  have hη := η_pos
  have ha1 : a ≤ 1 := le_trans haA (by norm_num [spinLimit])
  have hma : 1/1001 ≤ 1-a := by
    have : spinLimit ≤ 1000/1001 := by norm_num [spinLimit]
    linarith
  -- Exact intermediate values and their ranges.
  set Q := (1+a)^(1/3 : ℝ) with hQ
  set R := (1-a)^(1/3 : ℝ) with hR
  have hQ3 : Q^3 = 1+a := cubeRoot_cube _ (by linarith)
  have hR3 : R^3 = 1-a := cubeRoot_cube _ (by linarith)
  have hQ0 : 0 ≤ Q := Real.rpow_nonneg (by linarith) _
  have hR0 : 0 ≤ R := Real.rpow_nonneg (by linarith) _
  have hQ1 : 1 ≤ Q := by nlinarith [sq_nonneg (Q-1), sq_nonneg Q]
  have hQ2 : Q ≤ 63/50 := by nlinarith [sq_nonneg (Q-63/50), sq_nonneg Q]
  have hR1 : R ≤ 1 := by nlinarith [sq_nonneg (R-1), sq_nonneg R]
  have hR11 : 1/11 ≤ R := by nlinarith [sq_nonneg (R-1/11), sq_nonneg R]
  set S := Q*Q+Q*R+R*R with hS
  have hS1 : 1 ≤ S := by nlinarith [mul_nonneg hQ0 hR0]
  set G := 2*a/S with hG
  have hG0 : 0 ≤ G := div_nonneg (by linarith) (by linarith)
  have hG2 : G ≤ 2 := by
    rw [hG, div_le_iff₀ (by linarith)]
    nlinarith
  set W := (Q+R)*G*G with hW
  set Z1 := 3-W with hZ1
  have hZ1eq : iscoZ1 a = Z1 := iscoZ1_stable a ha ha1
  have hZ1b := iscoZ1_bounds a (by rw [abs_of_nonneg ha]; exact ha1)
  rw [hZ1eq] at hZ1b
  have hW0 : 0 ≤ W := by positivity
  have hW2 : W ≤ 2 := by linarith [hZ1b.1]
  set ZIN := 3*a*a+Z1*Z1 with hZIN
  set Z2 := Real.sqrt ZIN with hZ2
  have hZ2eq : iscoZ2 a = Z2 := by
    unfold iscoZ2; rw [hZ1eq, abs_of_nonneg ha, pow_two]
  have hZ2b := iscoZ2_bounds a (by rw [abs_of_nonneg ha]; exact ha1)
  rw [hZ2eq] at hZ2b
  have hZIN1 : 1 ≤ ZIN := by nlinarith [hZ1b.1]
  set U2 := 3+Z1+2*Z2 with hU2
  set V := W*U2 with hV
  set SQ := Real.sqrt V with hSQ
  set B := 3+Z2 with hB
  obtain ⟨hpro, hret⟩ := isco_stable a ha ha1
  have hpro' : isco a = B-SQ := hpro
  have hiso := isco_bounds a (by rw [abs_of_nonneg ha]; exact ha1)
  have hSQ0 : 0 ≤ SQ := Real.sqrt_nonneg _
  have hSQ5 : SQ ≤ 5 := by linarith [hZ2b.2]
  -- Error propagation, one Rust operation at a time.
  open Approx in
  have eP : Approx P (1+a) (2*u) 0 :=
    mono (roundFold (exact _) one_pos (by linarith) le_rfl le_rfl hP) (by linarith)
      (by norm_num [u, η]) le_rfl
  open Approx in
  have eM : Approx M (1-a) (2*u) 0 :=
    mono (roundFold (exact _) (by norm_num) hma le_rfl le_rfl hM) (by linarith)
      (by norm_num [u, η]) le_rfl
  open Approx in
  have eq : Approx q Q (5*u) 0 :=
    mono (cbrt eP (by linarith) (by positivity) (by norm_num [u]) hq) hQ0
      (by norm_num [u, cbrtError]) le_rfl
  open Approx in
  have er : Approx r R (5*u) 0 :=
    mono (cbrt eM (by linarith) (by positivity) (by norm_num [u]) hr) hR0
      (by norm_num [u, cbrtError]) le_rfl
  open Approx in
  have eqq : Approx qq (Q*Q) (13*u) 0 :=
    mono (roundFold (mul eq eq hQ0 hQ0 hQ2 hQ2 (by positivity) (by positivity) le_rfl le_rfl)
      one_pos (by nlinarith) (by positivity) (by norm_num) hqq) (by positivity)
      (by norm_num [u, η]) le_rfl
  open Approx in
  have eqr : Approx qr (Q*R) (13*u) 0 :=
    mono (roundFold (mul eq er hQ0 hR0 hQ2 hR1 (by positivity) (by positivity) le_rfl le_rfl)
      (by norm_num : (0:ℝ) < 1/11) (by nlinarith) (by positivity) (by norm_num) hqr)
      (by positivity) (by norm_num [u, η]) le_rfl
  open Approx in
  have err : Approx rr (R*R) (13*u) 0 :=
    mono (roundFold (mul er er hR0 hR0 hR1 hR1 (by positivity) (by positivity) le_rfl le_rfl)
      (by norm_num : (0:ℝ) < 1/121) (by nlinarith) (by positivity) (by norm_num) hrr)
      (by positivity) (by norm_num [u, η]) le_rfl
  open Approx in
  have es1 : Approx s1 (Q*Q+Q*R) (15*u) 0 :=
    mono (roundFold (add eqq eqr (by positivity) (by positivity) le_rfl le_rfl)
      one_pos (by nlinarith [mul_nonneg hQ0 hR0]) (by positivity) (by norm_num) hs1)
      (by positivity) (by norm_num [u, η]) le_rfl
  open Approx in
  have es : Approx s S (17*u) 0 :=
    mono (roundFold (add es1 err (by positivity) (by positivity) le_rfl
      (by linarith)) one_pos hS1 (by positivity) (by norm_num) hs)
      (by positivity) (by norm_num [u, η]) le_rfl
  open Approx in
  have en : Approx n (2*a) u η :=
    mono (round (exact _) (by linarith) le_rfl le_rfl hn) (by linarith)
      (by norm_num) (by norm_num)
  open Approx in
  have eg : Approx g G (21*u) (4*η) :=
    mono (round (div en es (by linarith) (by linarith : 2*a ≤ 2) one_pos hS1
      hu.le (by positivity) hη.le le_rfl (by norm_num [u])) hG0
      (by apply div_nonneg <;> norm_num [u]) (by apply add_nonneg <;> apply div_nonneg <;>
        norm_num [u, η]) hg)
      hG0 (by norm_num [u]) (by norm_num [u, η])
  open Approx in
  have eqp : Approx qp (Q+R) (7*u) 0 :=
    mono (roundFold (add eq er hQ0 hR0 le_rfl le_rfl) one_pos (by linarith)
      (by positivity) (by norm_num) hqp) (by positivity) (by norm_num [u, η]) le_rfl
  open Approx in
  have et : Approx t ((Q+R)*G) (31*u) (15*η) :=
    mono (round (mul eqp eg (by positivity) hG0 (by linarith : Q+R ≤ 3) hG2
      (by positivity) (by positivity) le_rfl (by positivity)) (by positivity)
      (by positivity) (by positivity) ht) (by positivity) (by norm_num [u]) (by norm_num [u, η])
  open Approx in
  have ew : Approx w W (55*u) (57*η) :=
    mono (round (mul et eg (by positivity) hG0 (by nlinarith : (Q+R)*G ≤ 6) hG2
      (by positivity) (by positivity) (by positivity) (by positivity)) hW0
      (by positivity) (by positivity) hw) hW0 (by norm_num [u]) (by norm_num [u, η])
  open Approx in
  have ez1 : Approx z1 Z1 (112*u) 0 :=
    mono (roundFold (three_sub ew hW0 hW2 (by positivity)) one_pos hZ1b.1 (by positivity)
      (by positivity) hz1) (by linarith [hZ1b.1]) (by norm_num [u, η]) le_rfl
  open Approx in
  have ea3 : Approx a3 (3*a) u η :=
    mono (round (exact _) (by linarith) le_rfl le_rfl ha3) (by linarith)
      (by norm_num) (by norm_num)
  open Approx in
  have eaa : Approx aa (3*a*a) (3*u) (3*η) :=
    mono (round (mul ea3 (exact a) (by linarith) ha (by linarith : 3*a ≤ 3) ha1
      hu.le le_rfl hη.le le_rfl) (by positivity) (by positivity) (by positivity) haa)
      (by positivity) (by norm_num [u]) (by norm_num [u, η])
  open Approx in
  have ezz : Approx zz (Z1*Z1) (226*u) 0 :=
    mono (roundFold (mul ez1 ez1 (by linarith [hZ1b.1]) (by linarith [hZ1b.1]) hZ1b.2 hZ1b.2
      (by positivity) (by positivity) le_rfl le_rfl) one_pos (by nlinarith [hZ1b.1])
      (by positivity) (by norm_num) hzz) (by nlinarith [hZ1b.1]) (by norm_num [u, η]) le_rfl
  open Approx in
  have ezi : Approx zi ZIN (228*u) 0 :=
    mono (roundFold (add eaa ezz (by positivity) (by nlinarith [hZ1b.1])
      (by norm_num [u]) le_rfl) one_pos hZIN1 (by positivity) (by positivity) hzi)
      (by linarith) (by norm_num [u, η]) le_rfl
  have hZ21 : 1 ≤ Z2 := by linarith [hZ2b.1]
  open Approx in
  have ez2 : Approx z2 Z2 (116*u) 0 :=
    mono (roundFold (sqrt_rel ezi (by linarith) (by positivity) (by norm_num [u]))
      one_pos hZ21 (by apply div_nonneg (by positivity); norm_num [u]) le_rfl hz2)
      (by linarith) (by norm_num [u, η]) le_rfl
  open Approx in
  have eu1 : Approx u1 (3+Z1) (114*u) 0 :=
    mono (roundFold (add (exact 3) ez1 (by norm_num) (by linarith [hZ1b.1]) (by positivity)
      le_rfl) (by norm_num : (0:ℝ) < 4) (by linarith [hZ1b.1]) (by positivity) (by norm_num) hu1)
      (by linarith [hZ1b.1]) (by norm_num [u, η]) le_rfl
  open Approx in
  have ez22 : Approx z22 (2*Z2) (118*u) 0 :=
    mono (roundFold (mul (exact 2) ez2 (by norm_num) (by linarith) le_rfl hZ2b.2
      le_rfl (by positivity) le_rfl le_rfl) (by norm_num : (0:ℝ) < 2) (by linarith)
      (by positivity) (by norm_num) hz22) (by linarith) (by norm_num [u, η]) le_rfl
  open Approx in
  have eu2 : Approx u2 U2 (120*u) 0 :=
    mono (roundFold (add eu1 ez22 (by linarith [hZ1b.1]) (by linarith) (by norm_num [u])
      le_rfl) (by norm_num : (0:ℝ) < 4) (by linarith [hZ1b.1]) (by positivity) (by norm_num) hu2)
      (by linarith [hZ1b.1]) (by norm_num [u, η]) le_rfl
  have hU2 : U2 ≤ 12 := by linarith [hZ1b.2, hZ2b.2]
  have hV0 : 0 ≤ V := mul_nonneg hW0 (by linarith [hZ1b.1, hZ2b.1])
  open Approx in
  have ev : Approx v V (178*u) (700*η) :=
    mono (round (mul ew eu2 hW0 (by linarith [hZ1b.1]) hW2 hU2 (by positivity)
      (by positivity) (by positivity) le_rfl)
      (mul_nonneg hW0 (by linarith [hZ1b.1, hZ2b.1])) (by positivity)
      (by positivity) hv) (mul_nonneg hW0 (by linarith [hZ1b.1, hZ2b.1]))
      (by norm_num [u]) (by norm_num [u, η])
  open Approx in
  have esq : Approx sq SQ (180*u) (1/2^68) :=
    mono (round (sqrt_abs ev hV0 (by positivity) (by norm_num [u])
      (by positivity) (by norm_num : (0:ℝ) ≤ 1/2^69) (by norm_num [η]))
      hSQ0 (by apply div_nonneg (by positivity); norm_num [u]) (by norm_num) hsq)
      hSQ0 (by norm_num [u]) (by norm_num [u, η])
  open Approx in
  have eb : Approx b B (118*u) 0 :=
    mono (roundFold (add (exact 3) ez2 (by norm_num) (by linarith) (by positivity) le_rfl)
      (by norm_num : (0:ℝ) < 5) (by linarith [hZ2b.1]) (by positivity) (by norm_num) hb)
      (by linarith) (by norm_num [u, η]) le_rfl
  unfold Approx at eb esq
  have hB6 : B ≤ 6 := by linarith [hZ2b.2]
  have hB0 : 0 ≤ B := by linarith [hZ2b.1]
  have hB5 : 5 ≤ B := by linarith [hZ2b.1]
  have hBS : 1 ≤ B-SQ := by rw [← hpro']; exact hiso.1
  constructor
  · intro res hres
    unfold Rounded at hres
    rw [hpro']
    have hdiff : |(b-sq)-(B-SQ)| ≤ 118*u*B+(180*u*SQ+1/2^68) := by
      calc |(b-sq)-(B-SQ)| = |(b-B)-(sq-SQ)| := by ring_nf
        _ ≤ |b-B|+|sq-SQ| := abs_sub _ _
        _ ≤ _ := by linarith
    have hdiff' : |(b-sq)-(B-SQ)| ≤ 1609*u := by
      have : 118*u*B ≤ 118*u*6 := by nlinarith
      have : 180*u*SQ ≤ 180*u*5 := by nlinarith
      have : (1:ℝ)/2^68 ≤ u := by norm_num [u]
      linarith
    have hbs : |b-sq| ≤ (B-SQ)+1609*u := by
      have := abs_sub_abs_le_abs_sub (b-sq) (B-SQ)
      rw [abs_of_nonneg (show (0:ℝ) ≤ B-SQ by linarith)] at this
      linarith
    have hround : |res-(b-sq)| ≤ u*((B-SQ)+1609*u)+η := by nlinarith
    calc |res-(B-SQ)| = |(res-(b-sq))+((b-sq)-(B-SQ))| := by ring_nf
      _ ≤ |res-(b-sq)|+|(b-sq)-(B-SQ)| := abs_add_le _ _
      _ ≤ u*((B-SQ)+1609*u)+η+1609*u := by linarith
      _ ≤ 2048*u*(B-SQ) := by
        have : u*(1609*u)+η ≤ u := by norm_num [u, η]
        nlinarith [hiso.1, hpro']
  · intro hpos res hres
    unfold Rounded at hres
    have hret' : isco (-a) = B+SQ := hret hpos
    rw [hret']
    have hsum1 : 1 ≤ B+SQ := by linarith
    have hdiff : |(b+sq)-(B+SQ)| ≤ 180*u*(B+SQ)+1/2^68 := by
      calc |(b+sq)-(B+SQ)| = |(b-B)+(sq-SQ)| := by ring_nf
        _ ≤ |b-B|+|sq-SQ| := abs_add_le _ _
        _ ≤ _ := by nlinarith
    have hbs : |b+sq| ≤ (B+SQ)*(1+180*u)+1/2^68 := by
      have := abs_sub_abs_le_abs_sub (b+sq) (B+SQ)
      rw [abs_of_nonneg (show (0:ℝ) ≤ B+SQ by linarith)] at this
      linarith
    have hround : |res-(b+sq)| ≤ u*((B+SQ)*(1+180*u)+1/2^68)+η := by nlinarith
    calc |res-(B+SQ)| = |(res-(b+sq))+((b+sq)-(B+SQ))| := by ring_nf
      _ ≤ |res-(b+sq)|+|(b+sq)-(B+SQ)| := abs_add_le _ _
      _ ≤ u*((B+SQ)*(1+180*u)+1/2^68)+η+(180*u*(B+SQ)+1/2^68) := by linarith
      _ ≤ 256*u*(B+SQ) := by
        have h1 : u*(1/2^68)+η+1/2^68 ≤ u := by norm_num [u, η]
        have h2 : u*((B+SQ)*(1+180*u)) = u*(B+SQ)+180*u*u*(B+SQ) := by ring
        have h3 : 180*u*u*(B+SQ) ≤ u*(B+SQ) := by
          have : 180*u*u ≤ u := by norm_num [u]
          nlinarith
        nlinarith

end BlackHole.Binary32
