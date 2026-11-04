module

public import BlackHole.WgslSinCos
public import BlackHole.TransferPhi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! WGSL error bounds for `transfer_phi` (obligations F2, T2, T3).

```
var acc = vec2<f32>(c[10],0.0);
for (var k=9; k>=0; k--) {
    acc = vec2<f32>(c[k]-(z.x*acc.x-z.y*acc.y), -(z.x*acc.y+z.y*acc.x));
}
```

* Series branch: `cmul_error` bounds one computed complex product,
  `horner_step` one loop iteration (the propagated error contracts by `|z|`),
  `chorner_error` the whole loop, and `transfer_phi_series_error` gives
  `‖computed - (1 - e^{-z})/z‖ ≤ 33u + 10⁻¹¹` for `0 < |z| ≤ 0.5001`.
* Direct branch (`|z| ≥ 0.4999`, `Re z ≥ 0`): `direct_numerator` bounds
  `1 - e^{-z}` from WGSL `exp` (`3 + 2x` ULP) and the proved `sincos` error σ,
  and `direct_component` bounds each component of the quotient by `1200u`,
  using `σ/|z| ≤ 385u` (the `sincos` error grows with `|Im z|`, the quotient
  divides by `|z|`).
* `branch_domains`: the computed test `dot(z,z) < 0.25` selects exactly these
  two domains, so every input with `Re z ≥ 0` and `|Im z| ≤ 2¹⁸` is covered. -/

@[expose] public section
noncomputable section

namespace BlackHole.Wgsl

lemma norm_le_re_im (w : ℂ) : ‖w‖ ≤ |w.re|+|w.im| := Complex.norm_le_abs_re_add_abs_im w

lemma cs2 (x1 x2 y1 y2 : ℝ) :
    |x1*y1|+|x2*y2| ≤ Real.sqrt (x1*x1+x2*x2)*Real.sqrt (y1*y1+y2*y2) := by
  have h0 : 0 ≤ x1*x1+x2*x2 := add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  have h1 : 0 ≤ y1*y1+y2*y2 := add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  rw [← Real.sqrt_mul h0, Real.le_sqrt (by positivity) (mul_nonneg h0 h1), abs_mul, abs_mul]
  nlinarith [sq_nonneg (|x1| *|y2|-|x2| *|y1|), sq_abs x1, sq_abs x2, sq_abs y1, sq_abs y2,
    abs_mul_abs_self x1, abs_mul_abs_self x2, abs_mul_abs_self y1, abs_mul_abs_self y2]

lemma cauchy_re_im (a b : ℂ) : |a.re*b.re|+|a.im*b.im| ≤ ‖a‖*‖b‖ := by
  rw [Complex.norm_def, Complex.norm_def, Complex.normSq_apply, Complex.normSq_apply]
  exact cs2 _ _ _ _

lemma cauchy_re_im' (a b : ℂ) : |a.re*b.im|+|a.im*b.re| ≤ ‖a‖*‖b‖ := by
  rw [Complex.norm_def, Complex.norm_def, Complex.normSq_apply, Complex.normSq_apply,
    show b.re*b.re+b.im*b.im = b.im*b.im+b.re*b.re by ring]
  exact cs2 _ _ _ _

/-- One computed complex product `(a.re b.re - a.im b.im, a.re b.im + a.im b.re)`. -/
theorem cmul_error (a b : ℂ) (p q t1 r s t2 : ℝ) (hp : Rnd (a.re*b.re) p)
    (hq : Rnd (a.im*b.im) q) (ht1 : Rnd (p-q) t1) (hr : Rnd (a.re*b.im) r)
    (hs : Rnd (a.im*b.re) s) (ht2 : Rnd (r+s) t2) :
    |t1-(a*b).re| ≤ 3*u*(‖a‖*‖b‖)+4*η ∧ |t2-(a*b).im| ≤ 3*u*(‖a‖*‖b‖)+4*η := by
  unfold Rnd at *
  have hu := u_pos
  have hη := η_pos
  have hc1 := cauchy_re_im a b
  have hc2 := cauchy_re_im' a b
  have hN : 0 ≤ ‖a‖*‖b‖ := by positivity
  have hsmall : u*(u*(‖a‖*‖b‖)+2*η) ≤ u*(‖a‖*‖b‖)/2+η := by
    have a1 : u*u ≤ u/2 := by norm_num [u]
    have a2 : 2*u*η ≤ η := by
      have : 2*u ≤ 1 := by norm_num [u]
      nlinarith
    have a3 : u*u*(‖a‖*‖b‖) ≤ u/2*(‖a‖*‖b‖) := mul_le_mul_of_nonneg_right a1 hN
    have e : u*(u*(‖a‖*‖b‖)+2*η) = u*u*(‖a‖*‖b‖)+2*u*η := by ring
    rw [e]; linarith
  constructor
  · simp only [Complex.mul_re]
    have h1 : |p-q-(a.re*b.re-a.im*b.im)| ≤ u*(‖a‖*‖b‖)+2*η := by
      calc |p-q-(a.re*b.re-a.im*b.im)| = |(p-a.re*b.re)-(q-a.im*b.im)| := by ring_nf
        _ ≤ _ := abs_sub _ _
        _ ≤ (u*|a.re*b.re|+η)+(u*|a.im*b.im|+η) := add_le_add hp hq
        _ ≤ _ := by nlinarith
    have h2 : |p-q| ≤ ‖a‖*‖b‖+(u*(‖a‖*‖b‖)+2*η) := by
      have := abs_sub_abs_le_abs_sub (p-q) (a.re*b.re-a.im*b.im)
      have : |a.re*b.re-a.im*b.im| ≤ ‖a‖*‖b‖ := le_trans (abs_sub _ _) hc1
      linarith
    calc |t1-(a.re*b.re-a.im*b.im)| = |(t1-(p-q))+(p-q-(a.re*b.re-a.im*b.im))| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ (u*|p-q|+η)+(u*(‖a‖*‖b‖)+2*η) := add_le_add ht1 h1
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left h2 hu.le
        have e : u*(‖a‖*‖b‖+(u*(‖a‖*‖b‖)+2*η)) = u*(‖a‖*‖b‖)+u*(u*(‖a‖*‖b‖)+2*η) := by ring
        nlinarith
  · simp only [Complex.mul_im]
    have h1 : |r+s-(a.re*b.im+a.im*b.re)| ≤ u*(‖a‖*‖b‖)+2*η := by
      calc |r+s-(a.re*b.im+a.im*b.re)| = |(r-a.re*b.im)+(s-a.im*b.re)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
        _ ≤ (u*|a.re*b.im|+η)+(u*|a.im*b.re|+η) := add_le_add hr hs
        _ ≤ _ := by nlinarith
    have h2 : |r+s| ≤ ‖a‖*‖b‖+(u*(‖a‖*‖b‖)+2*η) := by
      have := abs_sub_abs_le_abs_sub (r+s) (a.re*b.im+a.im*b.re)
      have : |a.re*b.im+a.im*b.re| ≤ ‖a‖*‖b‖ := le_trans (abs_add_le _ _) hc2
      linarith
    calc |t2-(a.re*b.im+a.im*b.re)| = |(t2-(r+s))+(r+s-(a.re*b.im+a.im*b.re))| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ (u*|r+s|+η)+(u*(‖a‖*‖b‖)+2*η) := add_le_add ht2 h1
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left h2 hu.le
        have e : u*(‖a‖*‖b‖+(u*(‖a‖*‖b‖)+2*η)) = u*(‖a‖*‖b‖)+u*(u*(‖a‖*‖b‖)+2*η) := by ring
        nlinarith

/-- One loop iteration: `acc ← c - z·acc` with `c` a rounded real constant.
    The propagated error contracts by `|z|`; each iteration adds at most `16u`. -/
theorem horner_step (z acc accT : ℂ) (c cT : ℝ) (E : ℝ) (hz : ‖z‖ ≤ 5001/10000)
    (hacc : ‖acc‖ ≤ 2) (hE : ‖accT-acc‖ ≤ E) (hE1 : E ≤ 1/100) (hc : Rnd c cT) (hc1 : |c| ≤ 1)
    (p q t1 r s t2 re : ℝ) (hp : Rnd (z.re*accT.re) p) (hq : Rnd (z.im*accT.im) q)
    (ht1 : Rnd (p-q) t1) (hr : Rnd (z.re*accT.im) r) (hs : Rnd (z.im*accT.re) s)
    (ht2 : Rnd (r+s) t2) (hre : Rnd (cT-t1) re) :
    ‖(⟨re, -t2⟩ : ℂ)-((c : ℂ)-z*acc)‖ ≤ 5001/10000*E+16*u := by
  have hu := u_pos
  have hη := η_pos
  have haccT : ‖accT‖ ≤ 2+1/100 := by
    have := norm_sub_norm_le accT acc; linarith
  have hzT : ‖z‖*‖accT‖ ≤ 11/10 := by
    calc ‖z‖*‖accT‖ ≤ 5001/10000*(2+1/100) := mul_le_mul hz haccT (norm_nonneg _) (by norm_num)
      _ ≤ 11/10 := by norm_num
  obtain ⟨e1, e2⟩ := cmul_error z accT p q t1 r s t2 hp hq ht1 hr hs ht2
  have hηu : η ≤ u/10^20 := by norm_num [u, η]
  have h3 : 3*u*(‖z‖*‖accT‖) ≤ 33/10*u := by nlinarith
  unfold Rnd at hc hre
  -- Split into fresh rounding T and the propagated part z·(acc - accT).
  set T : ℂ := (⟨re, -t2⟩ : ℂ)-((c : ℂ)-z*accT) with hT
  have hsplit : (⟨re, -t2⟩ : ℂ)-((c : ℂ)-z*acc) = T+z*(acc-accT) := by rw [hT]; ring
  have hprop : ‖z*(acc-accT)‖ ≤ 5001/10000*E := by
    rw [norm_mul, norm_sub_rev]; exact mul_le_mul hz hE (norm_nonneg _) (by norm_num)
  have hzre : |(z*accT).re| ≤ 11/10 := by
    calc |(z*accT).re| ≤ ‖z*accT‖ := Complex.abs_re_le_norm _
      _ = ‖z‖*‖accT‖ := norm_mul _ _
      _ ≤ 11/10 := hzT
  have ht1b : |t1| ≤ 12/10 := by
    have := abs_sub_abs_le_abs_sub t1 (z*accT).re
    have : 33/10*u+4*η ≤ 1/100 := by norm_num [u, η]
    linarith
  have hcTb : |cT| ≤ 11/10 := by
    have := abs_sub_abs_le_abs_sub cT c
    have : u*|c| ≤ u := by nlinarith
    have : u+η ≤ 1/100 := by norm_num [u, η]
    linarith
  have hsub : |cT-t1| ≤ 23/10 := by
    have := abs_sub cT t1; linarith
  have hTre : |T.re| ≤ 3*u*(23/10)+(u+η)+(33/10*u+4*η)+η := by
    have : T.re = (re-(cT-t1))+(cT-c)-(t1-(z*accT).re) := by
      simp [hT, Complex.sub_re]; ring
    rw [this]
    have hr1 : |re-(cT-t1)| ≤ u*(23/10)+η := by
      have : u*|cT-t1| ≤ u*(23/10) := mul_le_mul_of_nonneg_left hsub hu.le
      linarith
    have hr2 : |cT-c| ≤ u+η := by
      have : u*|c| ≤ u := by nlinarith
      linarith
    calc |(re-(cT-t1))+(cT-c)-(t1-(z*accT).re)| ≤
        |re-(cT-t1)|+|cT-c|+|t1-(z*accT).re| := by
          refine le_trans (abs_sub _ _) (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ (u*(23/10)+η)+(u+η)+(33/10*u+4*η) := by linarith
      _ ≤ _ := by nlinarith
  have hTim : |T.im| ≤ 33/10*u+4*η := by
    have : T.im = -(t2-(z*accT).im) := by simp [hT, Complex.sub_im]; ring
    rw [this, abs_neg]; linarith
  have hTn : ‖T‖ ≤ 16*u := by
    have := norm_le_re_im T
    have : (3*u*(23/10)+(u+η)+(33/10*u+4*η)+η)+(33/10*u+4*η) ≤ 16*u := by norm_num [u, η]
    linarith
  rw [hsplit]
  calc ‖T+z*(acc-accT)‖ ≤ ‖T‖+‖z*(acc-accT)‖ := norm_add_le _ _
    _ ≤ 16*u+5001/10000*E := add_le_add hTn hprop
    _ = _ := by ring

/-! ### The whole loop -/

/-- Exact complex Horner chain `c₀ - z(c₁ - z(… - z c₁₀))`. -/
def chorner (z : ℂ) : List ℝ → ℂ
  | [] => 0
  | [c] => c
  | c :: c' :: cs => (c : ℂ)-z*chorner z (c' :: cs)

/-- A WGSL evaluation of the chain with binary32 coefficients. -/
def CHornerComp (z : ℂ) : List ℝ → ℂ → Prop
  | [], _ => False
  | [cT], res => res = (cT : ℂ)
  | cT :: cT' :: cTs, res => ∃ accT : ℂ, CHornerComp z (cT' :: cTs) accT ∧
      ∃ p q t1 r s t2 re : ℝ, Rnd (z.re*accT.re) p ∧ Rnd (z.im*accT.im) q ∧ Rnd (p-q) t1 ∧
        Rnd (z.re*accT.im) r ∧ Rnd (z.im*accT.re) s ∧ Rnd (r+s) t2 ∧ Rnd (cT-t1) re ∧
        res = ⟨re, -t2⟩

lemma chorner_bound (z : ℂ) (hz : ‖z‖ ≤ 1) : ∀ L : List ℝ, ‖chorner z L‖ ≤ absSum L
  | [] => by simp [chorner, absSum]
  | [c] => by simp [chorner, absSum]
  | c :: c' :: cs => by
    have ih := chorner_bound z hz (c' :: cs)
    simp only [chorner, absSum] at ih ⊢
    calc ‖(c : ℂ)-z*chorner z (c' :: cs)‖ ≤ ‖(c : ℂ)‖+‖z‖*‖chorner z (c' :: cs)‖ := by
          rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ |c|+1*(|c'|+absSum cs) := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          gcongr
      _ = _ := by ring

theorem chorner_error (z : ℂ) (hz : ‖z‖ ≤ 5001/10000) :
    ∀ (L B : List ℝ) (res : ℂ), List.Forall₂ (fun c cT => Rnd c cT ∧ |c| ≤ 1) L B →
      absSum L ≤ 2 → CHornerComp z B res → ‖res-chorner z L‖ ≤ 33*u
  | [], _, _, hf, _, hc => by cases hf; simp [CHornerComp] at hc
  | [c], B, res, hf, _, hc => by
    cases hf with
    | cons hcb hrest =>
      cases hrest
      simp only [CHornerComp] at hc
      subst hc
      simp only [chorner]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have := hcb.1; unfold Rnd at this
      have hu := u_pos
      have : η ≤ u := by norm_num [u, η]
      nlinarith [hcb.2]
  | c :: c' :: cs, B, res, hf, hsum, hc => by
    cases hf with
    | cons hcb hrest =>
      rename_i cT B'
      cases hrest with
      | cons hcb' hrest' =>
        rename_i cT' B''
        obtain ⟨accT, hacc, p, q, t1, r, s, t2, re, hp, hq, ht1, hr, hs, ht2, hre, hres⟩ := hc
        have hsum' : absSum (c' :: cs) ≤ 2 := by
          simp only [absSum] at hsum ⊢; linarith [abs_nonneg c]
        have ih := chorner_error z hz (c' :: cs) (cT' :: B'') accT
          (List.Forall₂.cons hcb' hrest') hsum' hacc
        have hb := chorner_bound z (by linarith) (c' :: cs)
        have hE1 : 33*u ≤ 1/100 := by norm_num [u]
        have hstep := horner_step z (chorner z (c' :: cs)) accT c cT (33*u) hz
          (le_trans hb hsum') ih hE1 hcb.1 hcb.2 p q t1 r s t2 re hp hq ht1 hr hs ht2 hre
        rw [hres]
        simp only [chorner]
        have hu := u_pos
        calc _ ≤ 5001/10000*(33*u)+16*u := hstep
          _ ≤ 33*u := by nlinarith

/-- The eleven series coefficients `1/(k+1)!`. -/
def phiCoeffs : List ℝ := [1, 1/2, 1/6, 1/24, 1/120, 1/720, 1/5040, 1/40320, 1/362880,
  1/3628800, 1/39916800]

lemma chorner_phiCoeffs (z : ℂ) : chorner z phiCoeffs = TransferPhi.series z := by
  simp only [chorner, phiCoeffs, TransferPhi.series, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.factorial]
  push_cast
  ring

/-- WGSL error bound for the series branch of `transfer_phi`: for
    `0 < |z| ≤ 0.5001` the computed value is within `33u + 10⁻¹¹` of
    `(1 - e^{-z})/z`. -/
theorem transfer_phi_series_error (z : ℂ) (hz0 : z ≠ 0) (hz : ‖z‖ ≤ 5001/10000)
    (B : List ℝ) (hB : List.Forall₂ (fun c cT => Rnd c cT ∧ |c| ≤ 1) phiCoeffs B)
    (res : ℂ) (hres : CHornerComp z B res) :
    ‖res-TransferPhi.phi z‖ ≤ 33*u+1/10^11 := by
  have hsum : absSum phiCoeffs ≤ 2 := by norm_num [absSum, phiCoeffs, abs_of_pos]
  have h1 := chorner_error z hz phiCoeffs B res hB hsum hres
  rw [chorner_phiCoeffs] at h1
  have h2 := TransferPhi.phi_series_error z hz0 hz
  calc ‖res-TransferPhi.phi z‖ = ‖(res-TransferPhi.series z)-(TransferPhi.phi z-TransferPhi.series z)‖ := by
        ring_nf
    _ ≤ ‖res-TransferPhi.series z‖+‖TransferPhi.phi z-TransferPhi.series z‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add h1 h2

/-! ### Direct branch -/

/-- WGSL `exp(-x)` for `x ≥ 0`: within `(3 + 2x)` ULP. -/
def ExpW (x e : ℝ) : Prop := |e-Real.exp (-x)| ≤ 2*u*(3+2*x)*Real.exp (-x)+η

lemma exp_error_le (x e : ℝ) (hx : 0 ≤ x) (he : ExpW x e) : |e-Real.exp (-x)| ≤ 6*u+η := by
  unfold ExpW at he
  have hu := u_pos
  have h1 : (3+2*x)*Real.exp (-x) ≤ 3 := by
    have h := Real.add_one_le_exp x
    have hpos := Real.exp_pos x
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hpos]
    linarith
  nlinarith

set_option maxHeartbeats 8000000 in
/-- WGSL error bound for one component of the direct branch of `transfer_phi`
    (`|z| ≥ 0.4999`): numerator component `num = n₁ a + n₂ b` with
    `(a, b) = (x, y)` for the real part and `(n₁, n₂) = (nx, ny)`, `(ny, -nx)`
    for the real and imaginary parts. `σ` is the `sincos` error. -/
theorem direct_component (x y : ℝ) (hR : (4999/10000)^2 ≤ x^2+y^2)
    (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ : σ ≤ 128*u*(1+|y|)) (hy : |y| ≤ 2^18)
    (N1 N2 n1 n2 a b : ℝ) (hab : (a = x ∧ b = y) ∨ (a = y ∧ b = -x))
    (hN1 : |N1| ≤ 2) (hN2 : |N2| ≤ 2) (hn1 : |n1-N1| ≤ σ+34*u) (hn2 : |n2-N2| ≤ σ+34*u)
    (xx yy d p1 p2 num q : ℝ) (hxx : Rnd (x*x) xx) (hyy : Rnd (y*y) yy) (hd : Rnd (xx+yy) d)
    (hp1 : Rnd (n1*a) p1) (hp2 : Rnd (n2*b) p2) (hnum : Rnd (p1+p2) num) (hq : Div num d q) :
    |q-(N1*a+N2*b)/(x^2+y^2)| ≤ 1200*u := by
  have hu := u_pos
  have hη := η_pos
  set D := x^2+y^2 with hD
  set R := Real.sqrt D with hRdef
  have hD0 : 0 < D := lt_of_lt_of_le (by norm_num) hR
  have hRsq : R^2 = D := Real.sq_sqrt hD0.le
  have hR0 : 4999/10000 ≤ R := by
    rw [hRdef, show (4999/10000:ℝ) = Real.sqrt ((4999/10000)^2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hR
  have hRpos : 0 < R := by linarith
  have hxR : |x| ≤ R := by
    rw [hRdef, ← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg y])
  have hyR : |y| ≤ R := by
    rw [hRdef, ← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])
  have haR : |a| ≤ R ∧ |b| ≤ R := by
    rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb]; exact ⟨hxR, hyR⟩
    · rw [ha, hb, abs_neg]; exact ⟨hyR, hxR⟩
  have hηu : η ≤ u/10^20 := by norm_num [u, η]
  -- σ is at most 3 on the domain, and σ/R at most 385u.
  have hσ3 : σ ≤ 3 := by
    have : 128*u*(1+|y|) ≤ 128*u*(1+2^18) := by nlinarith [abs_nonneg y]
    have : 128*u*(1+2^18) ≤ 3 := by norm_num [u]
    linarith
  have hσR : σ ≤ 385*u*R := by
    have : 128*u*(1+|y|) ≤ 128*u*(2001/1000*R+R) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : (1:ℝ) ≤ 2001/1000*R := by linarith
      linarith
    nlinarith
  -- Denominator.
  unfold Rnd at hxx hyy hd hp1 hp2 hnum
  unfold Div at hq
  have hxxe : |xx-x*x| ≤ u*(x*x)+η := by rw [abs_of_nonneg (mul_self_nonneg x)] at hxx; exact hxx
  have hyye : |yy-y*y| ≤ u*(y*y)+η := by rw [abs_of_nonneg (mul_self_nonneg y)] at hyy; exact hyy
  have hDe : |d-D| ≤ 3*u*D := by
    have h1 : |xx+yy-D| ≤ u*D+2*η := by
      calc |xx+yy-D| = |(xx-x*x)+(yy-y*y)| := by rw [hD]; ring_nf
        _ ≤ _ := abs_add_le _ _
        _ ≤ (u*(x*x)+η)+(u*(y*y)+η) := add_le_add hxxe hyye
        _ = u*D+2*η := by rw [hD]; ring
    have h2 : |xx+yy| ≤ D+u*D+2*η := by
      have := abs_sub_abs_le_abs_sub (xx+yy) D
      rw [abs_of_pos hD0] at this; linarith
    have h3 : u*(u*D+2*η) ≤ u*D/10 := by
      have : u*u ≤ u/10^7 := by norm_num [u]
      have : 2*u*η ≤ u*D/20 := by
        have : (1:ℝ)/5 ≤ D := le_trans (by norm_num) hR
        have : 2*η ≤ D/20 := by
          have : η ≤ 1/10^30 := by norm_num [η]
          linarith
        nlinarith
      nlinarith
    have h4 : 3*η ≤ u*D/10 := by
      have : (1:ℝ)/5 ≤ D := le_trans (by norm_num) hR
      have : η ≤ u/10^20 := hηu
      nlinarith
    calc |d-D| = |(d-(xx+yy))+(xx+yy-D)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ (u*|xx+yy|+η)+(u*D+2*η) := add_le_add hd h1
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left h2 hu.le
        nlinarith
  have hdlow : D*(1-3*u) ≤ d := by
    have := neg_abs_le (d-D); nlinarith
  have hdpos : 0 < d := lt_of_lt_of_le (by nlinarith [show 3*u < 1 by norm_num [u]]) hdlow
  -- Numerator.
  obtain ⟨ha, hb⟩ := haR
  have hn1b : |n1| ≤ 6 := by
    have := abs_sub_abs_le_abs_sub n1 N1
    have : 34*u ≤ 1/100 := by norm_num [u]
    linarith
  have hn2b : |n2| ≤ 6 := by
    have := abs_sub_abs_le_abs_sub n2 N2
    have : 34*u ≤ 1/100 := by norm_num [u]
    linarith
  set A := N1*a+N2*b with hA
  have hAb : |A| ≤ 4*R := by
    have h1 : |N1*a| ≤ 2*R := by rw [abs_mul]; exact mul_le_mul hN1 ha (abs_nonneg _) (by norm_num)
    have h2 : |N2*b| ≤ 2*R := by rw [abs_mul]; exact mul_le_mul hN2 hb (abs_nonneg _) (by norm_num)
    linarith [abs_add_le (N1*a) (N2*b)]
  have hp1b : |n1*a| ≤ 6*R := by rw [abs_mul]; exact mul_le_mul hn1b ha (abs_nonneg _) (by norm_num)
  have hp2b : |n2*b| ≤ 6*R := by rw [abs_mul]; exact mul_le_mul hn2b hb (abs_nonneg _) (by norm_num)
  have hlin : |n1*a+n2*b-A| ≤ 2*(σ+34*u)*R := by
    have h1 : |n1*a-N1*a| ≤ (σ+34*u)*R := by
      rw [← sub_mul, abs_mul]; exact mul_le_mul hn1 ha (abs_nonneg _) (by positivity)
    have h2 : |n2*b-N2*b| ≤ (σ+34*u)*R := by
      rw [← sub_mul, abs_mul]; exact mul_le_mul hn2 hb (abs_nonneg _) (by positivity)
    calc |n1*a+n2*b-A| = |(n1*a-N1*a)+(n2*b-N2*b)| := by rw [hA]; ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := by linarith
  have hnume : |num-A| ≤ 2*(σ+34*u)*R+26*u*R := by
    have h1 : |p1+p2-(n1*a+n2*b)| ≤ 12*u*R+2*η := by
      calc |p1+p2-(n1*a+n2*b)| = |(p1-n1*a)+(p2-n2*b)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
        _ ≤ (u*|n1*a|+η)+(u*|n2*b|+η) := add_le_add hp1 hp2
        _ ≤ _ := by nlinarith
    have h2 : |p1+p2| ≤ 13*R := by
      have := abs_sub_abs_le_abs_sub (p1+p2) (n1*a+n2*b)
      have : |n1*a+n2*b| ≤ 12*R := by linarith [abs_add_le (n1*a) (n2*b)]
      have : 12*u*R+2*η ≤ R := by
        have : 12*u ≤ 1/2 := by norm_num [u]
        have : 2*η ≤ R/2 := by
          have : η ≤ 1/10^30 := by norm_num [η]
          linarith
        nlinarith
      linarith
    have h3 : u*|p1+p2| ≤ 13*u*R := by nlinarith
    have h4 : 3*η ≤ u*R := by nlinarith
    calc |num-A| = |(num-(p1+p2))+(p1+p2-(n1*a+n2*b))+(n1*a+n2*b-A)| := by ring_nf
      _ ≤ _ := abs_add_three _ _ _
      _ ≤ (u*|p1+p2|+η)+(12*u*R+2*η)+2*(σ+34*u)*R := by gcongr
      _ ≤ _ := by linarith
  -- Quotient.
  have hnumb : |num| ≤ 12*R := by
    have := abs_sub_abs_le_abs_sub num A
    have : 2*(σ+34*u)*R+26*u*R ≤ 8*R := by
      have : 2*(σ+34*u)+26*u ≤ 8 := by
        have : 94*u ≤ 1 := by norm_num [u]
        linarith
      nlinarith
    linarith
  have hquot : |num/d-A/D| ≤ (2*(σ+34*u)*R+26*u*R)/(D*(1-3*u))+4*R*(3*u*D)/((D*(1-3*u))*D) := by
    have e : num/d-A/D = (num-A)/d+A*(D-d)/(d*D) := by field_simp; ring
    rw [e]
    have hdD : 0 < D*(1-3*u) := by nlinarith [show 3*u < 1 by norm_num [u]]
    calc |(num-A)/d+A*(D-d)/(d*D)| ≤ |(num-A)/d|+|A*(D-d)/(d*D)| := abs_add_le _ _
      _ = |num-A|/d+|A| *|D-d|/(d*D) := by
          rw [abs_div, abs_of_pos hdpos, abs_div, abs_mul, abs_of_pos (mul_pos hdpos hD0)]
      _ ≤ _ := by
          have hdD : D*(1-3*u) ≤ d := hdlow
          have hpos1 : 0 < D*(1-3*u) := by nlinarith [show 3*u < 1 by norm_num [u]]
          apply add_le_add
          · exact div_le_div₀ (by positivity) hnume hpos1 hdD
          · apply div_le_div₀ (by positivity) _ (mul_pos hpos1 hD0)
              (mul_le_mul_of_nonneg_right hdD hD0.le)
            rw [abs_sub_comm]
            exact mul_le_mul hAb hDe (abs_nonneg _) (by positivity)
  have hR2 : D = R*R := by rw [← hRsq]; ring
  have hfinal1 : (2*(σ+34*u)*R+26*u*R)/(D*(1-3*u)) ≤ (2*σ+94*u)/R*(1+4*u) := by
    rw [div_le_iff₀ (by nlinarith [show 3*u < 1 by norm_num [u]])]
    have hk : (1+4*u)*(1-3*u) ≥ 1 := by nlinarith [show u ≤ 1/10^7 by norm_num [u]]
    calc 2*(σ+34*u)*R+26*u*R = (2*σ+94*u)/R*(R*R)*1 := by field_simp; ring
      _ ≤ (2*σ+94*u)/R*(R*R)*((1+4*u)*(1-3*u)) := by
          apply mul_le_mul_of_nonneg_left hk; positivity
      _ = _ := by rw [hR2]; ring
  have hfinal2 : 4*R*(3*u*D)/((D*(1-3*u))*D) ≤ 12*u/R*(1+4*u) := by
    rw [div_le_iff₀ (mul_pos (mul_pos hD0 (by norm_num [u] : (0:ℝ) < 1-3*u)) hD0)]
    have hk : (1+4*u)*(1-3*u) ≥ 1 := by nlinarith [show u ≤ 1/10^7 by norm_num [u]]
    have : 12*u/R*(1+4*u)*((D*(1-3*u))*D) = 12*u*R*D*((1+4*u)*(1-3*u)) := by
      rw [hR2]; field_simp
    rw [this]
    have : 4*R*(3*u*D) = 12*u*R*D*1 := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_left hk; positivity
  have hRinv : 1/R ≤ 2001/1000 := by
    rw [div_le_iff₀ hRpos]; linarith
  have hq1 : |num/d| ≤ 26 := by
    rw [abs_div, abs_of_pos hdpos, div_le_iff₀ hdpos]
    have : 12*R ≤ 26*(D*(1-3*u)) := by
      rw [hR2]
      have : 3*u ≤ 1/1000 := by norm_num [u]
      nlinarith
    linarith
  have hdiv : |q-num/d| ≤ 5*u*26+η := by
    have := mul_le_mul_of_nonneg_left hq1 (show 0 ≤ 5*u by positivity); linarith
  calc |q-A/D| = |(q-num/d)+(num/d-A/D)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ (5*u*26+η)+((2*σ+94*u)/R*(1+4*u)+12*u/R*(1+4*u)) := by
        refine add_le_add hdiv (le_trans hquot (add_le_add hfinal1 hfinal2))
    _ ≤ 1200*u := by
        have h1 : (2*σ+94*u)/R ≤ (2*(385*u)+94*u*(2001/1000)) := by
          have e : (2*σ+94*u)/R = 2*(σ/R)+94*u*(1/R) := by field_simp
          have hs : σ/R ≤ 385*u := by rw [div_le_iff₀ hRpos]; linarith
          rw [e]
          have := mul_le_mul_of_nonneg_left hRinv (show 0 ≤ 94*u by positivity)
          linarith
        have h2 : 12*u/R ≤ 12*u*(2001/1000) := by
          rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hRinv (by positivity)
        have h3 : (2*σ+94*u)/R*(1+4*u) ≤ (2*(385*u)+94*u*(2001/1000))*(1+4*u) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
        have h4 : 12*u/R*(1+4*u) ≤ 12*u*(2001/1000)*(1+4*u) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
        have : 5*u*26+η+((2*(385*u)+94*u*(2001/1000))*(1+4*u)+12*u*(2001/1000)*(1+4*u)) ≤
            1200*u := by norm_num [u, η]
        linarith

/-- The direct branch's numerator `1 - exp(-z)` from WGSL `exp` and `sincos`. -/
theorem direct_numerator (x y : ℝ) (hx : 0 ≤ x) (e c s ec nx ny σ : ℝ) (he : ExpW x e)
    (hσ0 : 0 ≤ σ) (hσ3 : σ ≤ 3) (hc : |c-Real.cos y| ≤ σ) (hs : |s-Real.sin y| ≤ σ)
    (hec : Rnd (e*c) ec) (hnx : Rnd (1-ec) nx) (hny : Rnd (e*s) ny) :
    |nx-(1-Real.exp (-x)*Real.cos y)| ≤ σ+34*u ∧ |ny-Real.exp (-x)*Real.sin y| ≤ σ+34*u := by
  have hu := u_pos
  have hη := η_pos
  have hηu : η ≤ u/10^20 := by norm_num [u, η]
  have hde := exp_error_le x e hx he
  set E := Real.exp (-x) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := by rw [hE]; exact Real.exp_le_one_iff.mpr (by linarith)
  have hcos := Real.abs_cos_le_one y
  have hsin := Real.abs_sin_le_one y
  have hcb : |c| ≤ 1+σ := by have := abs_sub_abs_le_abs_sub c (Real.cos y); linarith
  have hsb : |s| ≤ 1+σ := by have := abs_sub_abs_le_abs_sub s (Real.sin y); linarith
  have heb : |e| ≤ 1+6*u+η := by
    have := abs_sub_abs_le_abs_sub e E; rw [abs_of_pos hE0] at this; linarith
  unfold Rnd at hec hnx hny
  -- |e c - E cos y| ≤ (6u+η)(1+σ) + σ.
  have hprod : ∀ t T : ℝ, |t-T| ≤ σ → |t| ≤ 1+σ → |e*t-E*T| ≤ (6*u+η)*(1+σ)+σ := by
    intro t T ht htb
    calc |e*t-E*T| = |(e-E)*t+E*(t-T)| := by ring_nf
      _ ≤ |(e-E)*t|+|E*(t-T)| := abs_add_le _ _
      _ = |e-E| *|t|+E*|t-T| := by rw [abs_mul, abs_mul, abs_of_pos hE0]
      _ ≤ (6*u+η)*(1+σ)+1*σ := by
          gcongr
      _ = _ := by ring
  have hbig : (6*u+η)*(1+σ) ≤ 24*u+u/1000 := by nlinarith
  have hetb : ∀ t : ℝ, |t| ≤ 1+σ → u*|e*t| ≤ 4*u+u/1000 := by
    intro t ht
    have : |e*t| ≤ (1+6*u+η)*(1+σ) := by rw [abs_mul]; exact mul_le_mul heb ht (abs_nonneg _) (by positivity)
    have : (1+6*u+η)*(1+σ) ≤ 4+1/1000 := by nlinarith [show 6*u+η ≤ 1/10^6 by norm_num [u, η]]
    nlinarith
  have h1 := hprod c (Real.cos y) hc hcb
  have h2 := hprod s (Real.sin y) hs hsb
  have h3 := hetb c hcb
  have h4 := hetb s hsb
  constructor
  · have hec' : |ec-E*Real.cos y| ≤ σ+28*u+u/100 := by
      calc |ec-E*Real.cos y| = |(ec-e*c)+(e*c-E*Real.cos y)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
        _ ≤ _ := by linarith
    have h1ec : |1-ec| ≤ 5+1/10 := by
      have := abs_sub_abs_le_abs_sub ec (E*Real.cos y)
      have : |E*Real.cos y| ≤ 1 := by
        rw [abs_mul, abs_of_pos hE0]; nlinarith
      have : σ+28*u+u/100 ≤ 31/10 := by nlinarith [show 29*u ≤ 1/100 by norm_num [u]]
      linarith [abs_sub (1:ℝ) ec, (abs_one : |(1:ℝ)| = 1)]
    calc |nx-(1-E*Real.cos y)| = |(nx-(1-ec))-(ec-E*Real.cos y)| := by ring_nf
      _ ≤ _ := abs_sub _ _
      _ ≤ (u*|1-ec|+η)+(σ+28*u+u/100) := by linarith
      _ ≤ _ := by nlinarith
  · calc |ny-E*Real.sin y| = |(ny-e*s)+(e*s-E*Real.sin y)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := by linarith

/-- The computed branch test `dot(z,z) < 0.25` selects `|z| ≤ 0.5001`;
    its negation selects `|z|² ≥ 0.4999²`. -/
theorem branch_domains (x y xx yy d : ℝ) (hxx : Rnd (x*x) xx) (hyy : Rnd (y*y) yy)
    (hd : Rnd (xx+yy) d) :
    (d < 1/4 → x^2+y^2 ≤ (5001/10000)^2) ∧ (1/4 ≤ d → (4999/10000)^2 ≤ x^2+y^2) := by
  have hu := u_pos
  have hη := η_pos
  unfold Rnd at *
  rw [abs_of_nonneg (mul_self_nonneg x)] at hxx
  rw [abs_of_nonneg (mul_self_nonneg y)] at hyy
  set D := x^2+y^2 with hD
  have hD0 : 0 ≤ D := by positivity
  have h1 : |xx+yy-D| ≤ u*D+2*η := by
    calc |xx+yy-D| = |(xx-x*x)+(yy-y*y)| := by rw [hD]; ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ (u*(x*x)+η)+(u*(y*y)+η) := add_le_add hxx hyy
      _ = u*D+2*η := by rw [hD]; ring
  have h2 : |xx+yy| ≤ D+u*D+2*η := by
    have := abs_sub_abs_le_abs_sub (xx+yy) D
    rw [abs_of_nonneg hD0] at this; linarith
  have h3 : |d-D| ≤ u*(D+u*D+2*η)+η+(u*D+2*η) := by
    calc |d-D| = |(d-(xx+yy))+(xx+yy-D)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ (u*|xx+yy|+η)+(u*D+2*η) := add_le_add hd h1
      _ ≤ _ := by have := mul_le_mul_of_nonneg_left h2 hu.le; linarith
  have hsmall : u ≤ 1/10^7 := by norm_num [u]
  have hηs : η ≤ 1/10^30 := by norm_num [η]
  have hηu : 2*u*η ≤ η := by
    have : 2*u ≤ 1 := by norm_num [u]
    nlinarith
  have huD : u*D ≤ 1/10^7*D := mul_le_mul_of_nonneg_right hsmall hD0
  have huuD : u*(u*D) ≤ 1/10^7*(u*D) := mul_le_mul_of_nonneg_right hsmall (by positivity)
  have e1 : u*(D+u*D+2*η) = u*D+u*(u*D)+2*u*η := by ring
  have h3' : |d-D| ≤ 3*u*D+4*η := by nlinarith
  have h4 : 3*u*D ≤ 3/10^7*D := by linarith
  constructor
  · intro hdl
    by_contra hc
    push Not at hc
    have := neg_abs_le (d-D)
    have : (5001/10000:ℝ)^2 = 25010001/100000000 := by norm_num
    linarith
  · intro hdg
    by_contra hc
    push Not at hc
    have := le_abs_self (d-D)
    have : (4999/10000:ℝ)^2 = 24990001/100000000 := by norm_num
    linarith

end BlackHole.Wgsl
