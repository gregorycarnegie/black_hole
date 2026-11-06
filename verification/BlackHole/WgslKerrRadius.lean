module

public import BlackHole.WgslSum
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! WGSL error bound for `kerr_radius` in `geodesic.wesl` (obligation F2).

```
let q = dot(x,x) - dot(a,a);
let ax = dot(a,x);
let root = sqrt(q*q + 4.0*ax*ax);
var r2 = 0.5 * (q + root);
if q < 0.0 { r2 = 2.0*ax*ax / max(root-q, 1.0e-20); }
return sqrt(max(r2, 1.0e-12));
```

The arithmetic model is the WGSL specification's f32 accuracy table:
`+ - *` are correctly rounded, `x / y` is within 2.5 ULP, `inverseSqrt` within
2 ULP and `sqrt` inherits from `1.0 / inverseSqrt(x)`. One ULP of a binary32
value is at most `2⁻²³|x| = 2u|x|`. Subnormal inputs and outputs may be flushed
to zero, covered by an absolute term `η = 2⁻¹²⁶` per operation. Reassociation
is allowed: `WgslSum.SumTree.error` bounds every evaluation order of the
`dot` sums, which is exactly the form of the `hq` and `hp` hypotheses below.
Fusion is covered because an exact intermediate satisfies the rounding model.

`kerr_radius_error` proves a relative error of at most `160 u ≈ 9.5·10⁻⁶`
for every input whose exact Kerr radius `r` satisfies `|a| ≤ r` and
`r² ≥ 2⁻³⁶`, whichever branch the computed sign of `q` selects, with both
floors inactive. Every point outside the horizon of a source with `|a| ≤ M`
satisfies `|a| ≤ M ≤ r₊ ≤ r`. -/

@[expose] public section
noncomputable section

namespace BlackHole.Wgsl

/-- Unit roundoff of binary32. -/
def u : ℝ := 1/2^24
/-- Flush-to-zero allowance. -/
def η : ℝ := 1/2^126

/-- A correctly rounded WGSL operation (or an exact one, e.g. after fusion). -/
def Rnd (x y : ℝ) : Prop := |y-x| ≤ u*|x|+η
/-- Two successive roundings of one product chain, in any association. -/
def Rnd2 (x y : ℝ) : Prop := |y-x| ≤ (2*u+u^2)*|x|+3*η
/-- WGSL division, 2.5 ULP. -/
def Div (n d y : ℝ) : Prop := |y-n/d| ≤ 5*u*|n/d|+η
/-- WGSL specifies the 2.5 ULP division only for `|d| ∈ [2⁻¹²⁶, 2¹²⁶]`; outside
that range the result is unconstrained. -/
def DivSpec (n d y : ℝ) : Prop := (1/2^126 ≤ |d| ∧ |d| ≤ 2^126) → Div n d y
/-- WGSL `inverseSqrt`, 2 ULP. -/
def InvSqrt (x y : ℝ) : Prop := |y-1/Real.sqrt x| ≤ 4*u*(1/Real.sqrt x)

lemma u_pos : 0 < u := by norm_num [u]
lemma η_pos : 0 < η := by norm_num [η]

/-- `sqrt(x)` inherited from `1.0 / inverseSqrt(x)` is within `10u` relative. -/
theorem sqrt_inherited (x i y : ℝ) (hx : 0 < x) (hi : InvSqrt x i) (hy : Div 1 i y) :
    |y-Real.sqrt x| ≤ 10*u*Real.sqrt x+η := by
  unfold InvSqrt Div at *
  have hu := u_pos
  set s := Real.sqrt x with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hx
  have hu1 : u ≤ 1/2^24 := le_rfl
  -- i = (1/s)(1+δ), |δ| ≤ 4u.
  have hi0 : (1-4*u)*(1/s) ≤ i := by
    have := neg_abs_le (i-1/s); nlinarith
  have hi1 : i ≤ (1+4*u)*(1/s) := by
    have := le_abs_self (i-1/s); nlinarith
  have hipos : 0 < i := by
    have h1 : 0 < 1/s := by positivity
    have h2 : 0 < 1-4*u := by norm_num [u]
    nlinarith [mul_pos h2 h1]
  -- 1/i is within 4u/(1-4u) of s.
  have hrec : |1/i-s| ≤ 4*u/(1-4*u)*s := by
    have hk : 0 < 1-4*u := by norm_num [u]
    rw [show 1/i-s = (1-s*i)/i by field_simp]
    rw [abs_div, abs_of_pos hipos, div_le_iff₀ hipos]
    have h1 : |1-s*i| ≤ 4*u := by
      have : 1-s*i = -(s*(i-1/s)) := by field_simp; ring
      rw [this, abs_neg, abs_mul, abs_of_pos hs0]
      calc s*|i-1/s| ≤ s*(4*u*(1/s)) := mul_le_mul_of_nonneg_left hi hs0.le
        _ = 4*u := by field_simp
    have h2 : 4*u ≤ 4*u/(1-4*u)*s*i := by
      have : 4*u/(1-4*u)*s*i ≥ 4*u/(1-4*u)*s*((1-4*u)*(1/s)) := by
        apply mul_le_mul_of_nonneg_left hi0; positivity
      have h3 : 4*u/(1-4*u)*s*((1-4*u)*(1/s)) = 4*u := by field_simp
      linarith
    linarith
  have hrabs : |1/i| ≤ (1+4*u/(1-4*u))*s := by
    have := abs_sub_abs_le_abs_sub (1/i) s
    rw [abs_of_pos hs0] at this
    nlinarith
  have hc : 4*u/(1-4*u) ≤ 4*u+u/10 := by
    rw [div_le_iff₀ (by norm_num [u])]; norm_num [u]
  have hy' : |y-1/i| ≤ 5*u*((1+4*u/(1-4*u))*s)+η := by
    have : 5*u*|1/i| ≤ 5*u*((1+4*u/(1-4*u))*s) := mul_le_mul_of_nonneg_left hrabs (by positivity)
    simp only [one_div] at hy this ⊢
    linarith
  calc |y-s| = |(y-1/i)+(1/i-s)| := by ring_nf
    _ ≤ |y-1/i|+|1/i-s| := abs_add_le _ _
    _ ≤ 5*u*((1+4*u/(1-4*u))*s)+η+4*u/(1-4*u)*s := by linarith
    _ ≤ 10*u*s+η := by
      have : 5*u*((1+4*u/(1-4*u))*s)+4*u/(1-4*u)*s ≤ 10*u*s := by
        have e : 5*u*((1+4*u/(1-4*u))*s)+4*u/(1-4*u)*s = (5*u+(5*u+1)*(4*u/(1-4*u)))*s := by ring
        rw [e]
        apply mul_le_mul_of_nonneg_right _ hs0.le
        have : (5*u+1)*(4*u/(1-4*u)) ≤ (5*u+1)*(4*u+u/10) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
        nlinarith [show u*u ≤ u/2^24 by norm_num [u]]
      linarith

/-- Square-root perturbation: `|√m - √t| ≤ |m - t| / √t`. -/
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

set_option maxHeartbeats 20000000 in
/-- The WGSL error bound for `kerr_radius`. `X = |x|²`, `A = |a|²`, `P = a·x`
    and `S = Σ|aᵢxᵢ|`; `T` is the exact squared Kerr radius. `hq` and `hp` are
    the reassociation-independent `dot` bounds from `SumTree.error` with six and
    three rounded product leaves. -/
theorem kerr_radius_error (X A P S T : ℝ) (hX : 0 ≤ X) (hA : 0 ≤ A)
    (hCS : P^2 ≤ X*A) (hPS : |P| ≤ S) (hS : S ≤ (X+A)/2)
    (hT : T = ((X-A)+Real.sqrt ((X-A)^2+4*P^2))/2) (haT : A ≤ T) (hTmin : 1/2^36 ≤ T)
    (hTmax : T ≤ 2^120)
    (q p qq fp s root : ℝ)
    (hq : |q-(X-A)| ≤ ((1+u)^6-1)*(X+A)+11*(1+u)^6*η)
    (hp : |p-P| ≤ ((1+u)^3-1)*S+5*(1+u)^3*η)
    (hqq : Rnd (q*q) qq) (hfp : Rnd2 (4*p*p) fp) (hs : Rnd (qq+fp) s)
    (hroot : |root-Real.sqrt s| ≤ 10*u*Real.sqrt s+η)
    (r2 r : ℝ)
    (hbranch : (0 ≤ q ∧ ∃ sA, Rnd (q+root) sA ∧ Rnd (sA/2) r2) ∨
      (q < 0 ∧ ∃ num den, Rnd2 (2*p*p) num ∧ Rnd (root-q) den ∧ DivSpec num (max den (1547425/154742504910672534362390528:ℝ)) r2))
    (hr : |r-Real.sqrt (max r2 (2305843/2305843009213693952:ℝ))| ≤ 10*u*Real.sqrt (max r2 (2305843/2305843009213693952:ℝ))+η) :
    |r-Real.sqrt T| ≤ 160*u*Real.sqrt T := by
  have hu := u_pos
  have hη := η_pos
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hTmin
  have hηT : η ≤ u*T/2^60 := by
    have : η*2^60 ≤ u*(1/2^36) := by norm_num [u, η]
    nlinarith
  set Q := X-A with hQ
  set D := Real.sqrt (Q^2+4*P^2) with hD
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hDsq : D^2 = Q^2+4*P^2 := Real.sq_sqrt (by positivity)
  -- Kerr radial identity and ranges in units of T.
  have hrad : T^2-Q*T-P^2 = 0 := by rw [hT]; nlinarith [hDsq]
  have hQT : Q ≤ T := by nlinarith [sq_nonneg P]
  have hQlow : -T ≤ Q := by linarith
  have hDT : D = 2*T-Q := by rw [hT]; ring
  have hX2 : X ≤ 2*T := by linarith
  have hP2 : P^2 ≤ 2*T^2 := by nlinarith
  have hS2 : S ≤ 3*T/2 := by linarith
  have hPabs : |P| ≤ 3*T/2 := by linarith
  -- Sum errors.
  have hγ6 : (1+u)^6-1 ≤ 6*u+u/1000 := by norm_num [u]
  have hγ3 : (1+u)^3-1 ≤ 3*u+u/1000 := by norm_num [u]
  have hg6 : (1+u)^6 ≤ 2 := by norm_num [u]
  have hg3 : (1+u)^3 ≤ 2 := by norm_num [u]
  have eq : |q-Q| ≤ 19*u*T := by
    have h1 : ((1+u)^6-1)*(X+A) ≤ (6*u+u/1000)*(3*T) :=
      mul_le_mul hγ6 (by linarith) (by positivity) (by positivity)
    have h2 : 11*(1+u)^6*η ≤ 22*η := by nlinarith
    nlinarith
  have ep : |p-P| ≤ 5*u*T := by
    have h1 : ((1+u)^3-1)*S ≤ (3*u+u/1000)*(3*T/2) :=
      mul_le_mul hγ3 hS2 (le_trans (abs_nonneg _) hPS) (by positivity)
    have h2 : 5*(1+u)^3*η ≤ 10*η := by nlinarith
    nlinarith
  have hqabs : |q| ≤ 2*T+19*u*T := by
    have := abs_sub_abs_le_abs_sub q Q
    have : |Q| ≤ 2*T := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have hpabs : |p| ≤ 3*T/2+5*u*T := by
    have := abs_sub_abs_le_abs_sub p P; linarith
  have huT : u*T ≤ T/2^24 := by rw [u]; linarith
  -- q*q
  have eqq : |qq-Q^2| ≤ 82*u*T^2 := by
    unfold Rnd at hqq
    have hqQ : |q+Q| ≤ 4*T+19*u*T := by
      have : |Q| ≤ 2*T := abs_le.mpr ⟨by linarith, by linarith⟩
      have := abs_add_le q Q
      linarith
    have h1 : |q*q-Q^2| ≤ 19*u*T*(4*T+19*u*T) := by
      rw [show q*q-Q^2 = (q-Q)*(q+Q) by ring, abs_mul]
      exact mul_le_mul eq hqQ (abs_nonneg _) (by positivity)
    have h2 : |q*q| ≤ (2*T+19*u*T)^2 := by
      rw [abs_mul, sq]
      exact mul_le_mul hqabs hqabs (abs_nonneg _) (by positivity)
    have h3 : |qq-Q^2| ≤ |qq-q*q|+|q*q-Q^2| := by
      calc |qq-Q^2| = |(qq-q*q)+(q*q-Q^2)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have : u*u*T^2 ≤ u*T^2/2^24 := by
      have : u*u ≤ u/2^24 := by norm_num [u]
      nlinarith [sq_nonneg T]
    have : u*u*u*T^2 ≤ u*T^2/2^48 := by
      have : u*u*u ≤ u/2^48 := by norm_num [u]
      nlinarith [sq_nonneg T]
    have : η ≤ u*T^2/2^20 := by
      have : u*T/2^60 ≤ u*T^2/2^20 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_pos hu hT0]
      linarith
    nlinarith
  -- Simple magnitude bounds.
  have huT' : 19*u*T ≤ T/1000 := by rw [u]; linarith
  have hq1 : |q| ≤ 2001*T/1000 := by linarith
  have hp1 : |p| ≤ 1501*T/1000 := by linarith
  have hQabs : |Q| ≤ 2*T := abs_le.mpr ⟨by linarith, by linarith⟩
  have hηT2 : η ≤ u*T^2/2^20 := by
    have : u*T/2^60 ≤ u*T^2/2^20 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hu hT0]
    linarith
  -- 4*p*p
  have efp : |fp-4*P^2| ≤ 80*u*T^2 := by
    unfold Rnd2 at hfp
    have hpP : |p+P| ≤ 3002*T/1000 := by have := abs_add_le p P; linarith
    have h1 : |4*p*p-4*P^2| ≤ 4*(5*u*T)*(3002*T/1000) := by
      rw [show 4*p*p-4*P^2 = 4*((p-P)*(p+P)) by ring, abs_mul, abs_mul,
        abs_of_pos (by norm_num : (0:ℝ) < 4)]
      have := mul_le_mul ep hpP (abs_nonneg _) (by positivity)
      nlinarith
    have h2 : |4*p*p| ≤ 4*(1501*T/1000)^2 := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4)]
      have := mul_le_mul hp1 hp1 (abs_nonneg _) (by positivity)
      nlinarith
    have hu2 : (2*u+u^2) ≤ 2*u+u/2^24 := by norm_num [u]
    have h4 : (2*u+u^2)*|4*p*p| ≤ (2*u+u/2^24)*(4*(1501*T/1000)^2) :=
      mul_le_mul hu2 h2 (abs_nonneg _) (by positivity)
    have h3 : |fp-4*P^2| ≤ |fp-4*p*p|+|4*p*p-4*P^2| := by
      calc |fp-4*P^2| = |(fp-4*p*p)+(4*p*p-4*P^2)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have h5 : (2*u+u/2^24)*(4*(1501*T/1000)^2)+4*(5*u*T)*(3002*T/1000)+3*η ≤ 80*u*T^2 := by
      have : (2*u+u/2^24)*(4*(1501*T/1000)^2)+4*(5*u*T)*(3002*T/1000) =
          (2+1/2^24)*(4*(1501/1000)^2)*(u*T^2)+4*5*(3002/1000)*(u*T^2) := by ring
      rw [this]
      nlinarith [mul_pos hu (pow_pos hT0 2)]
    linarith
  -- The radicand q*q + 4*ax*ax.
  have hsq : Q^2+4*P^2 ≤ 9*T^2 := by nlinarith [hDsq, hDT]
  have es : |s-(Q^2+4*P^2)| ≤ 172*u*T^2 := by
    unfold Rnd at hs
    have h1 : |qq+fp-(Q^2+4*P^2)| ≤ 162*u*T^2 := by
      calc |qq+fp-(Q^2+4*P^2)| = |(qq-Q^2)+(fp-4*P^2)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
        _ ≤ _ := by linarith
    have h2 : |qq+fp| ≤ 9*T^2+162*u*T^2 := by
      have := abs_sub_abs_le_abs_sub (qq+fp) (Q^2+4*P^2)
      rw [abs_of_nonneg (show (0:ℝ) ≤ Q^2+4*P^2 by positivity)] at this
      linarith
    have h3 : u*|qq+fp| ≤ u*(9*T^2+162*u*T^2) := mul_le_mul_of_nonneg_left h2 hu.le
    have h4 : u*(9*T^2+162*u*T^2)+η ≤ 9*u*T^2+u*T^2/100 := by
      have : u*(162*u*T^2) ≤ u*T^2/1000 := by
        have : 162*u ≤ 1/1000 := by norm_num [u]
        nlinarith [mul_pos hu (pow_pos hT0 2)]
      nlinarith
    calc |s-(Q^2+4*P^2)| = |(s-(qq+fp))+(qq+fp-(Q^2+4*P^2))| := by ring_nf
      _ ≤ |s-(qq+fp)|+|qq+fp-(Q^2+4*P^2)| := abs_add_le _ _
      _ ≤ _ := by linarith [hs, h3, h4, h1]
  -- The root.
  have hDge : T ≤ D := by linarith
  have eroot : |root-D| ≤ 203*u*T := by
    have h1 : |Real.sqrt s-D| ≤ 172*u*T := by
      have := sqrt_sub_le s (Q^2+4*P^2) (by nlinarith)
      rw [← hD] at this
      calc |Real.sqrt s-D| ≤ |s-(Q^2+4*P^2)|/D := this
        _ ≤ 172*u*T^2/T := div_le_div₀ (by positivity) es hT0 hDge
        _ = 172*u*T := by field_simp
    have h2 : Real.sqrt s ≤ 3*T+172*u*T := by
      have := le_abs_self (Real.sqrt s-D); linarith
    have h3 : 10*u*Real.sqrt s+η ≤ 31*u*T := by
      have h4 : 10*u*Real.sqrt s ≤ 10*u*(3*T+172*u*T) := mul_le_mul_of_nonneg_left h2 (by positivity)
      have h5 : 10*u*(172*u*T) ≤ u*T/2 := by
        have : 1720*u ≤ 1/2 := by norm_num [u]
        nlinarith [mul_pos hu hT0]
      have h6 : 10*u*(3*T+172*u*T) = 30*(u*T)+10*u*(172*u*T) := by ring
      linarith
    calc |root-D| = |(root-Real.sqrt s)+(Real.sqrt s-D)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := by linarith
  -- Both branches give r2 within 140 u T of T.
  have er2 : |r2-T| ≤ 140*u*T := by
    rcases hbranch with ⟨_, sA, hsA, hr2⟩ | ⟨hneg, num, den, hnum, hden, hdiv⟩
    · unfold Rnd at hsA hr2
      have h1 : |q+root-(Q+D)| ≤ 222*u*T := by
        calc |q+root-(Q+D)| = |(q-Q)+(root-D)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
          _ ≤ _ := by linarith
      have hQD : Q+D = 2*T := by linarith
      have h2 : |q+root| ≤ 2*T+222*u*T := by
        have := abs_sub_abs_le_abs_sub (q+root) (Q+D)
        rw [abs_of_pos (show (0:ℝ) < Q+D by linarith)] at this; linarith
      have hsA' : |sA-2*T| ≤ 225*u*T := by
        have h3 : u*|q+root| ≤ u*(2*T+222*u*T) := mul_le_mul_of_nonneg_left h2 hu.le
        have h4 : u*(222*u*T) ≤ u*T/1000 := by
          have : 222*u ≤ 1/1000 := by norm_num [u]
          nlinarith [mul_pos hu hT0]
        have h5 : u*(2*T+222*u*T) = 2*(u*T)+u*(222*u*T) := by ring
        have h6 : η ≤ u*T/2^60 := hηT
        calc |sA-2*T| = |(sA-(q+root))+(q+root-(Q+D))| := by rw [hQD]; ring_nf
          _ ≤ _ := abs_add_le _ _
          _ ≤ _ := by linarith
      have h4 : |sA/2| ≤ T+113*u*T := by
        have := abs_sub_abs_le_abs_sub (sA/2) T
        rw [abs_of_pos hT0] at this
        have : |sA/2-T| = |sA-2*T|/2 := by
          rw [show sA/2-T = (sA-2*T)/2 by ring, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        linarith
      have h5 : u*|sA/2| ≤ u*(T+113*u*T) := mul_le_mul_of_nonneg_left h4 hu.le
      have h6 : u*(113*u*T) ≤ u*T/1000 := by
        have : 113*u ≤ 1/1000 := by norm_num [u]
        nlinarith [mul_pos hu hT0]
      have h7 : u*(T+113*u*T) = u*T+u*(113*u*T) := by ring
      calc |r2-T| = |(r2-sA/2)+(sA-2*T)/2| := by ring_nf
        _ ≤ |r2-sA/2|+|(sA-2*T)/2| := abs_add_le _ _
        _ = |r2-sA/2|+|sA-2*T|/2 := by
          rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        _ ≤ _ := by linarith
    · unfold Rnd2 at hnum
      unfold Rnd at hden
      -- q < 0 forces Q < 19uT, hence P² ≥ T(T - 19uT).
      have hQs : Q ≤ 19*u*T := by
        have := le_abs_self (q-Q); have := neg_abs_le (q-Q); linarith
      have hP2low : T*(T-19*u*T) ≤ P^2 := by nlinarith
      have hDQ : D-Q = 2*(T-Q) := by linarith
      have hDQlow : 2*(T-19*u*T) ≤ D-Q := by linarith
      have hDQup : D-Q ≤ 4*T := by linarith
      -- Numerator 2*p*p.
      have enum : |num-2*P^2| ≤ 40*u*T^2 := by
        have hpP : |p+P| ≤ 3002*T/1000 := by have := abs_add_le p P; linarith
        have h1 : |2*p*p-2*P^2| ≤ 2*(5*u*T)*(3002*T/1000) := by
          rw [show 2*p*p-2*P^2 = 2*((p-P)*(p+P)) by ring, abs_mul, abs_mul,
            abs_of_pos (by norm_num : (0:ℝ) < 2)]
          have := mul_le_mul ep hpP (abs_nonneg _) (by positivity)
          nlinarith
        have h2 : |2*p*p| ≤ 2*(1501*T/1000)^2 := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
          have := mul_le_mul hp1 hp1 (abs_nonneg _) (by positivity)
          nlinarith
        have hu2 : (2*u+u^2) ≤ 2*u+u/2^24 := by norm_num [u]
        have h4 : (2*u+u^2)*|2*p*p| ≤ (2*u+u/2^24)*(2*(1501*T/1000)^2) :=
          mul_le_mul hu2 h2 (abs_nonneg _) (by positivity)
        have h5 : (2*u+u/2^24)*(2*(1501*T/1000)^2)+2*(5*u*T)*(3002*T/1000)+3*η ≤ 40*u*T^2 := by
          have : (2*u+u/2^24)*(2*(1501*T/1000)^2)+2*(5*u*T)*(3002*T/1000) =
              (2+1/2^24)*(2*(1501/1000)^2)*(u*T^2)+2*5*(3002/1000)*(u*T^2) := by ring
          rw [this]
          linarith [hηT2, mul_pos hu (pow_pos hT0 2)]
        calc |num-2*P^2| = |(num-2*p*p)+(2*p*p-2*P^2)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
          _ ≤ _ := by linarith
      -- Denominator root - q.
      have eden : |den-(D-Q)| ≤ 227*u*T := by
        have h1 : |root-q-(D-Q)| ≤ 222*u*T := by
          calc |root-q-(D-Q)| = |(root-D)-(q-Q)| := by ring_nf
            _ ≤ _ := abs_sub _ _
            _ ≤ _ := by linarith
        have h2 : |root-q| ≤ 4*T+222*u*T := by
          have := abs_sub_abs_le_abs_sub (root-q) (D-Q)
          rw [abs_of_pos (show (0:ℝ) < D-Q by linarith)] at this; linarith
        have h3 : u*|root-q| ≤ u*(4*T+222*u*T) := mul_le_mul_of_nonneg_left h2 hu.le
        have h4 : u*(222*u*T) ≤ u*T/1000 := by
          have : 222*u ≤ 1/1000 := by norm_num [u]
          nlinarith [mul_pos hu hT0]
        have h5 : u*(4*T+222*u*T) = 4*(u*T)+u*(222*u*T) := by ring
        have h6 : η ≤ u*T/2^60 := hηT
        calc |den-(D-Q)| = |(den-(root-q))+(root-q-(D-Q))| := by ring_nf
          _ ≤ _ := abs_add_le _ _
          _ ≤ _ := by linarith
      have hden_pos : (1547425/154742504910672534362390528:ℝ) ≤ den := by
        have := neg_abs_le (den-(D-Q))
        have : 2*(T-19*u*T)-227*u*T ≥ T := by linarith [huT]
        have : (1547425/154742504910672534362390528:ℝ) ≤ T := le_trans (by norm_num) hTmin
        linarith
      rw [max_eq_left hden_pos] at hdiv
      have hden_low : T ≤ den := by
        have := neg_abs_le (den-(D-Q)); linarith [huT]
      have hden_hi : den ≤ 2^126 := by
        have := le_abs_self (den-(D-Q))
        have : D-Q ≤ 4*T := by linarith
        linarith [huT]
      have hdiv := hdiv ⟨by rw [abs_of_pos (lt_of_lt_of_le hT0 hden_low)]; linarith,
        by rw [abs_of_pos (lt_of_lt_of_le hT0 hden_low)]; exact hden_hi⟩
      unfold Div at hdiv
      -- Exact T = 2P²/(D-Q).
      have hTexact : T = 2*P^2/(D-Q) := by
        rw [eq_div_iff (by linarith), hDQ]; nlinarith
      have hdenpos : 0 < den := lt_of_lt_of_le hT0 hden_low
      have hDQpos : 0 < D-Q := by linarith
      -- |num/den - T| ≤ (|num - 2P²| + T|den - (D-Q)|)/den.
      have hratio : |num/den-T| ≤ (40*u*T^2+T*(227*u*T))/den := by
        rw [show num/den-T = ((num-2*P^2)-T*(den-(D-Q)))/den by
          rw [hTexact]; field_simp; ring]
        rw [abs_div, abs_of_pos hdenpos]
        apply div_le_div_of_nonneg_right _ hdenpos.le
        calc |(num-2*P^2)-T*(den-(D-Q))| ≤ |num-2*P^2|+|T*(den-(D-Q))| := abs_sub _ _
          _ = |num-2*P^2|+T*|den-(D-Q)| := by rw [abs_mul, abs_of_pos hT0]
          _ ≤ _ := by gcongr
      have hratio' : |num/den-T| ≤ 134*u*T := by
        refine le_trans hratio ?_
        rw [div_le_iff₀ hdenpos]
        have h1 : 2*(T-19*u*T)-227*u*T ≤ den := by
          have := neg_abs_le (den-(D-Q)); linarith
        have h2 : 134*u*T*(2*(T-19*u*T)-227*u*T) ≤ 134*u*T*den :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        have h3 : (u*T)*(u*T) ≤ (u*T)*T/2^24 := by
          have : u*T ≤ T/2^24 := huT
          have : 0 ≤ u*T := by positivity
          nlinarith
        have h4 : 134*u*T*(2*(T-19*u*T)-227*u*T) = 268*(u*T*T)-134*265*((u*T)*(u*T)) := by ring
        have h5 : 40*u*T^2+T*(227*u*T) = 267*(u*T*T) := by ring
        have h6 : (u*T)*T/2^24*(134*265) ≤ u*T*T := by
          have : 0 ≤ u*T*T := by positivity
          nlinarith
        nlinarith
      have hnd : |num/den| ≤ T+134*u*T := by
        have := abs_sub_abs_le_abs_sub (num/den) T
        rw [abs_of_pos hT0] at this; linarith
      have h1 : 5*u*|num/den| ≤ 5*u*(T+134*u*T) := mul_le_mul_of_nonneg_left hnd (by positivity)
      have h2 : 5*u*(134*u*T) ≤ u*T/1000 := by
        have : 670*u ≤ 1/1000 := by norm_num [u]
        nlinarith [mul_pos hu hT0]
      have h3 : 5*u*(T+134*u*T) = 5*(u*T)+5*u*(134*u*T) := by ring
      have h4 : η ≤ u*T/2^60 := hηT
      calc |r2-T| = |(r2-num/den)+(num/den-T)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
        _ ≤ _ := by linarith
  -- The floor is inactive and the final square root.
  have hr2low : (2305843/2305843009213693952:ℝ) ≤ r2 := by
    have := neg_abs_le (r2-T)
    have : 140*u*T ≤ T/1000 := by rw [u]; linarith
    have : (2305843/2305843009213693952:ℝ) ≤ T*(999/1000) := by
      have : (2305843/2305843009213693952:ℝ) ≤ 1/2^36*(999/1000) := by norm_num
      nlinarith
    linarith
  rw [max_eq_left hr2low] at hr
  have hsr : |Real.sqrt r2-Real.sqrt T| ≤ 140*u*Real.sqrt T := by
    have hst : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
    calc |Real.sqrt r2-Real.sqrt T| ≤ |r2-T|/Real.sqrt T := sqrt_sub_le r2 T hT0
      _ ≤ 140*u*T/Real.sqrt T := div_le_div_of_nonneg_right er2 hst.le
      _ = 140*u*Real.sqrt T := by
        rw [div_eq_iff hst.ne', mul_assoc (140*u) (Real.sqrt T), Real.mul_self_sqrt hT0.le]
  have hsT : Real.sqrt r2 ≤ Real.sqrt T+140*u*Real.sqrt T := by
    have := le_abs_self (Real.sqrt r2-Real.sqrt T); linarith
  have hst0 : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
  have hηs : η ≤ u*Real.sqrt T/1000 := by
    have : (1:ℝ)/2^18 ≤ Real.sqrt T := by
      rw [show (1:ℝ)/2^18 = Real.sqrt ((1/2^18)^2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num; linarith)
    have : η*1000 ≤ u*(1/2^18) := by norm_num [u, η]
    nlinarith
  have : 10*u*Real.sqrt r2 ≤ 10*u*(Real.sqrt T+140*u*Real.sqrt T) :=
    mul_le_mul_of_nonneg_left hsT (by positivity)
  have : 10*u*(140*u*Real.sqrt T) ≤ u*Real.sqrt T/1000 := by
    have : 1400*u ≤ 1/1000 := by norm_num [u]
    nlinarith [mul_pos hu hst0]
  calc |r-Real.sqrt T| = |(r-Real.sqrt r2)+(Real.sqrt r2-Real.sqrt T)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := by nlinarith

end BlackHole.Wgsl
