module

public import BlackHole.WgslSinCos
public import BlackHole.TransferPhi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! WGSL error bound for the series branch of `transfer_phi` (obligations
F2, T2, T3).

```
var acc = vec2<f32>(c[10],0.0);
for (var k=9; k>=0; k--) {
    acc = vec2<f32>(c[k]-(z.x*acc.x-z.y*acc.y), -(z.x*acc.y+z.y*acc.x));
}
```

`cmul_error` bounds one computed complex product, `horner_step` one loop
iteration, and `series_error` the whole loop: for `|z| ≤ 0.5001` the computed
value is within `16u` of `TransferPhi.series z`, hence (with
`TransferPhi.phi_series_error`) within `16u + 10⁻¹¹` of `(1 - e^{-z})/z`. -/

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

end BlackHole.Wgsl
