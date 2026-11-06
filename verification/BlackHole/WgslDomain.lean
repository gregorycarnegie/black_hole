module

public import BlackHole.WgslPlasma
public import BlackHole.WgslReassocBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! A checked interval evaluator for the `Safe` conditions of `WgslExpr`
(obligation F2).

`ev env e` evaluates a program over input boxes: `env i` gives an interval
containing the exact input `v i` and an upper bound on its error `E i`. If it
returns `some A`, then for every input in those boxes `Safe v E e` holds, the
exact value lies in `[A.lo, A.hi]` and the running bound is at most `A.b`
(`ev_sound`). It returns `none` when it cannot decide, so a domain theorem is
proved by evaluating it once per box of a cover, in the kernel.

At a sum the bound is also raised to cover every association of its chain
(`WgslReassoc.sum_bound`), and at a product or quotient every association that
keeps each factor in its role (`WgslReassoc.prod_bound`); the chains' factor
data is carried across `let` slots. Success therefore also implies `Safe` for
every such reassociation (`ev_robust`, `evLets_robust`), which WGSL permits.

Arithmetic is exact rational arithmetic, with endpoints rounded outward to
`2⁻¹⁶⁰` after each step. `sqrt`, `exp` and `log` use proved enclosures:
checked square-root candidates, Taylor series with Mathlib's remainder bounds
after range reduction, and `log 2` within `10⁻¹⁰`. -/

@[expose] public section

namespace BlackHole.WgslDomain
open Wgsl WgslExpr GExpr

/-! ### Outward rounding -/

/-- Rounding down and up to `p` fractional bits. -/
def rdn (p : ℕ) (q : ℚ) : ℚ := (⌊q*((2^p : ℕ) : ℚ)⌋ : ℚ)/((2^p : ℕ) : ℚ)
def rup (p : ℕ) (q : ℚ) : ℚ := (⌈q*((2^p : ℕ) : ℚ)⌉ : ℚ)/((2^p : ℕ) : ℚ)

lemma rdn_le (p : ℕ) (q : ℚ) : rdn p q ≤ q := by
  unfold rdn
  rw [div_le_iff₀ (by positivity)]; exact Int.floor_le _

lemma le_rup (p : ℕ) (q : ℚ) : q ≤ rup p q := by
  unfold rup
  rw [le_div_iff₀ (by positivity)]; exact Int.le_ceil _

lemma rdn_nonneg (p : ℕ) {q : ℚ} (hq : 0 ≤ q) : 0 ≤ rdn p q := by
  unfold rdn
  have : (0:ℚ) ≤ ⌊q*((2^p : ℕ) : ℚ)⌋ := by exact_mod_cast Int.floor_nonneg.mpr (by positivity)
  positivity

lemma rdn_le_real (p : ℕ) (q : ℚ) : ((rdn p q : ℚ) : ℝ) ≤ q := by exact_mod_cast rdn_le p q
lemma le_rup_real (p : ℕ) (q : ℚ) : (q : ℝ) ≤ ((rup p q : ℚ) : ℝ) := by exact_mod_cast le_rup p q

/-- `2^e` for an integer `e`. -/
def pow2 (e : ℤ) : ℚ := if 0 ≤ e then ((2^e.toNat : ℕ) : ℚ) else 1/((2^(-e).toNat : ℕ) : ℚ)

lemma pow2_eq (e : ℤ) : ((pow2 e : ℚ) : ℝ) = (2:ℝ)^e := by
  unfold pow2
  split_ifs with h
  · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp
  · obtain ⟨n,hn⟩ := Int.exists_eq_neg_ofNat (le_of_lt (not_le.mp h))
    subst hn
    simp [zpow_neg]

lemma pow2_pos (e : ℤ) : 0 < pow2 e := by
  unfold pow2; split_ifs <;> positivity

/-! ### Square roots -/

def newton (q : ℚ) : ℕ → ℚ → ℚ
  | 0, g => g
  | n+1, g => newton q n (rup 160 ((g+q/g)/2))

/-- A square-root candidate; only its checked bounds below are used. -/
def sqrtCand (q : ℚ) : ℚ :=
  newton q 10 (pow2 (((Nat.log2 q.num.natAbs : ℤ)-Nat.log2 q.den)/2))

def sqLo (q : ℚ) : ℚ :=
  let l := rdn 160 (sqrtCand q)*(1-1/1073741824)
  if 0 ≤ l ∧ l*l ≤ q then l else 0

def sqHi (q : ℚ) : ℚ :=
  let h := rup 160 (sqrtCand q)*(1+1/1073741824)
  if 0 ≤ h ∧ q ≤ h*h then h else Max.max q 1

lemma sqLo_nonneg (q : ℚ) : 0 ≤ sqLo q := by
  unfold sqLo; dsimp only; split_ifs with h
  · exact h.1
  · exact le_rfl

lemma sqLo_le (q : ℚ) : ((sqLo q : ℚ) : ℝ) ≤ Real.sqrt q := by
  unfold sqLo; dsimp only
  set l := rdn 160 (sqrtCand q)*(1-1/1073741824)
  split_ifs with h
  · apply Real.le_sqrt_of_sq_le
    have : ((l*l : ℚ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast h.2
    push_cast at this; nlinarith
  · simp [Real.sqrt_nonneg]

lemma le_sqHi (q : ℚ) : Real.sqrt q ≤ ((sqHi q : ℚ) : ℝ) := by
  unfold sqHi; dsimp only
  set l := rup 160 (sqrtCand q)*(1+1/1073741824)
  split_ifs with h
  · have h1 : (0:ℝ) ≤ ((l : ℚ) : ℝ) := by exact_mod_cast h.1
    have h2 : (q:ℝ) ≤ ((l : ℚ) : ℝ)^2 := by
      have : (q:ℝ) ≤ ((l*l : ℚ) : ℝ) := by exact_mod_cast h.2
      push_cast at this; nlinarith
    exact Real.sqrt_le_iff.mpr ⟨h1,h2⟩
  · push_cast
    rcases le_total (q:ℝ) 1 with h1 | h1
    · exact (Real.sqrt_le_one.mpr h1).trans (le_max_right _ _)
    · exact (Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩).trans (le_max_left _ _)

lemma sqHi_pos {q : ℚ} (hq : 0 < q) : 0 < ((sqHi q : ℚ) : ℝ) :=
  (Real.sqrt_pos.mpr (by exact_mod_cast hq)).trans_le (le_sqHi q)

/-! ### Exponentials -/

def expSum (y : ℚ) : ℕ → ℚ
  | 0 => 0
  | n+1 => expSum y n+y^n/(n.factorial : ℚ)

lemma expSum_eq (y : ℚ) (n : ℕ) :
    ((expSum y n : ℚ) : ℝ) = ∑ m ∈ Finset.range n, (y:ℝ)^m/m.factorial := by
  induction n with
  | zero => simp [expSum]
  | succ n ih => rw [Finset.sum_range_succ,← ih]; simp [expSum]

/-- The Taylor remainder bound for 12 terms at `|y| ≤ 1`. -/
def expRem (y : ℚ) : ℚ := |y|^12*(13/((Nat.factorial 12 : ℚ)*12))

def sqIter : ℕ → ℚ × ℚ → ℚ × ℚ
  | 0, p => p
  | k+1, p => sqIter k (rdn 160 (p.1*p.1), rup 160 (p.2*p.2))

/-- Bounds on `exp q`: `exp (q/2^k)` by its Taylor polynomial, squared `k` times. -/
def expBnd (q : ℚ) : ℚ × ℚ :=
  let k := Nat.log2 (⌈|q|⌉.toNat)+1
  let y := q/((2^k : ℕ) : ℚ)
  sqIter k (Max.max (expSum y 12-expRem y) 0, expSum y 12+expRem y)

lemma sqIter_sound : ∀ (k : ℕ) (p : ℚ × ℚ) (z : ℝ), 0 ≤ p.1 → (p.1 : ℝ) ≤ Real.exp z →
    Real.exp z ≤ p.2 → 0 ≤ (sqIter k p).1 ∧ ((sqIter k p).1 : ℝ) ≤ Real.exp (2^k*z) ∧
      Real.exp (2^k*z) ≤ (sqIter k p).2
  | 0, p, z, h0, h1, h2 => by simp [sqIter]; exact ⟨h0,h1,h2⟩
  | k+1, p, z, h0, h1, h2 => by
    have e : Real.exp (2^(k+1)*z) = Real.exp (2^k*(2*z)) := by ring_nf
    rw [e]
    have hz : Real.exp (2*z) = Real.exp z*Real.exp z := by rw [← Real.exp_add]; ring_nf
    apply sqIter_sound k _ (2*z) (rdn_nonneg _ (mul_nonneg h0 h0))
    · rw [hz]
      refine (rdn_le_real _ _).trans ?_
      push_cast
      have : (0:ℝ) ≤ p.1 := by exact_mod_cast h0
      exact mul_le_mul h1 h1 this (Real.exp_pos _).le
    · rw [hz]
      refine le_trans ?_ (le_rup_real _ _)
      push_cast
      exact mul_le_mul h2 h2 (Real.exp_pos _).le ((Real.exp_pos _).le.trans h2)

lemma expBnd_sound (q : ℚ) : 0 ≤ (expBnd q).1 ∧ ((expBnd q).1 : ℝ) ≤ Real.exp q ∧
    Real.exp q ≤ (expBnd q).2 := by
  unfold expBnd; dsimp only
  set k := Nat.log2 (⌈|q|⌉.toNat)+1
  set y := q/((2^k : ℕ) : ℚ)
  have hk : (0:ℚ) < ((2^k : ℕ) : ℚ) := by positivity
  have hy : |(y:ℝ)| ≤ 1 := by
    have h1 : |q| ≤ ((⌈|q|⌉.toNat : ℕ) : ℚ) := by
      have := Int.le_ceil |q|
      have h2 : ((⌈|q|⌉.toNat : ℕ) : ℤ) = ⌈|q|⌉ := Int.toNat_of_nonneg (Int.ceil_nonneg (abs_nonneg q))
      have h3 : (((⌈|q|⌉.toNat : ℕ) : ℤ) : ℚ) = ((⌈|q|⌉ : ℤ) : ℚ) := by rw [h2]
      push_cast at h3
      linarith
    have h3 : ((⌈|q|⌉.toNat : ℕ) : ℚ) ≤ ((2^k : ℕ) : ℚ) := by
      exact_mod_cast (Nat.lt_log2_self).le
    have : |y| ≤ 1 := by
      rw [abs_div, abs_of_pos hk, div_le_one hk]; linarith
    exact_mod_cast this
  have hb := Real.exp_bound hy (n := 12) (by norm_num)
  rw [← expSum_eq] at hb
  have hb' : |Real.exp y-((expSum y 12 : ℚ) : ℝ)| ≤ ((expRem y : ℚ) : ℝ) := by
    refine hb.trans (le_of_eq ?_); simp [expRem]
  have hab := abs_le.mp hb'
  have hq : (q:ℝ) = 2^k*(y:ℝ) := by
    simp only [y]; push_cast; field_simp
  rw [hq]
  apply sqIter_sound k _ y (le_max_right _ _)
  · push_cast; exact max_le (by linarith) (Real.exp_pos _).le
  · push_cast; linarith

def expLo (q : ℚ) : ℚ := (expBnd (rdn 40 q)).1
def expHi (q : ℚ) : ℚ := (expBnd (rup 40 q)).2

lemma expLo_le (q : ℚ) : ((expLo q : ℚ) : ℝ) ≤ Real.exp q :=
  (expBnd_sound _).2.1.trans (Real.exp_le_exp.mpr (rdn_le_real _ _))

lemma le_expHi (q : ℚ) : Real.exp q ≤ ((expHi q : ℚ) : ℝ) :=
  (Real.exp_le_exp.mpr (le_rup_real _ _)).trans (expBnd_sound _).2.2

/-! ### Logarithms -/

def logSum (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | n+1 => logSum x n+x^(n+1)/(n+1)

lemma logSum_eq (x : ℚ) (n : ℕ) :
    ((logSum x n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, (x:ℝ)^(i+1)/(i+1) := by
  induction n with
  | zero => simp [logSum]
  | succ n ih => rw [Finset.sum_range_succ,← ih]; simp [logSum]

def logRem (x : ℚ) : ℚ := |x|^17/(1-|x|)

/-- Bounds on `log m` for `m > 0`, from `log m = log (1+z) - log (1-z)` with
`z = (m-1)/(m+1)`. -/
def logMBnd (m : ℚ) : ℚ × ℚ :=
  let z := (m-1)/(m+1)
  let s := logSum z 16-logSum (-z) 16
  (s-2*logRem z, s+2*logRem z)

lemma logMBnd_sound {m : ℚ} (hm : 0 < m) :
    ((logMBnd m).1 : ℝ) ≤ Real.log m ∧ Real.log m ≤ (logMBnd m).2 := by
  unfold logMBnd
  set z := (m-1)/(m+1)
  have hm1 : (0:ℚ) < m+1 := by linarith
  have hz : |z| < 1 := by
    rw [abs_div, abs_of_pos hm1, div_lt_one hm1, abs_lt]; constructor <;> linarith
  have hzr : |(z:ℝ)| < 1 := by exact_mod_cast hz
  have hzr' : |(-(z:ℝ))| < 1 := by rwa [abs_neg]
  have h1 := Real.abs_log_sub_add_sum_range_le hzr 16
  have h2 := Real.abs_log_sub_add_sum_range_le hzr' 16
  rw [abs_neg] at h2
  have hrem : |(z:ℝ)|^(16+1)/(1-|(z:ℝ)|) = ((logRem z : ℚ) : ℝ) := by simp [logRem]
  rw [hrem] at h1 h2
  rw [← logSum_eq] at h1
  have e2 : ∑ i ∈ Finset.range 16, (-(z:ℝ))^(i+1)/(i+1) = ((logSum (-z) 16 : ℚ) : ℝ) := by
    rw [logSum_eq]; push_cast; rfl
  rw [e2] at h2
  have hlog : Real.log m = Real.log (1-(-(z:ℝ)))-Real.log (1-(z:ℝ)) := by
    rw [← Real.log_div]
    · congr 1
      simp only [z]; push_cast
      have : (m:ℝ)+1 ≠ 0 := by exact_mod_cast hm1.ne'
      field_simp; ring
    · have := (abs_lt.mp hzr).1; linarith
    · have := (abs_lt.mp hzr).2; linarith
  rw [hlog]
  have a1 := abs_le.mp h1
  have a2 := abs_le.mp h2
  push_cast
  constructor <;> linarith

/-- `log 2` within `10⁻¹⁰` (`Real.log_two_near_10`). -/
def L2lo : ℚ := 287209/414355-1/10000000000
def L2hi : ℚ := 287209/414355+1/10000000000

lemma L2_sound : (L2lo : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ L2hi := by
  have h := abs_le.mp Real.log_two_near_10
  simp only [L2lo, L2hi]; push_cast
  constructor <;> linarith [h.1, h.2]

lemma L2lo_pos : (0:ℚ) < L2lo := by norm_num [L2lo]

/-- The binary exponent used to reduce `q` near `1`. -/
def logExp (q : ℚ) : ℤ := (Nat.log2 q.num.natAbs : ℤ)-Nat.log2 q.den

def logLo0 (q : ℚ) : ℚ :=
  let k := logExp q
  let m := q/pow2 k
  let ml := if 0 < rdn 60 m then rdn 60 m else m
  k*(if 0 ≤ k then L2lo else L2hi)+(logMBnd ml).1

def logHi0 (q : ℚ) : ℚ :=
  let k := logExp q
  let m := q/pow2 k
  k*(if 0 ≤ k then L2hi else L2lo)+(logMBnd (rup 60 m)).2

lemma log_split {q : ℚ} (hq : 0 < q) (k : ℤ) :
    Real.log q = k*Real.log 2+Real.log ((q/pow2 k : ℚ) : ℝ) := by
  have hp := pow2_pos k
  push_cast
  rw [pow2_eq, Real.log_div (by exact_mod_cast hq.ne') (by positivity), Real.log_zpow]
  ring

lemma int_mul_log2_lo (k : ℤ) : ((k*(if 0 ≤ k then L2lo else L2hi) : ℚ) : ℝ) ≤ k*Real.log 2 := by
  have h := L2_sound
  split_ifs with hk
  · push_cast; exact mul_le_mul_of_nonneg_left h.1 (by exact_mod_cast hk)
  · push_cast; exact mul_le_mul_of_nonpos_left h.2 (by exact_mod_cast (not_le.mp hk).le)

lemma int_mul_log2_hi (k : ℤ) : (k:ℝ)*Real.log 2 ≤ ((k*(if 0 ≤ k then L2hi else L2lo) : ℚ) : ℝ) := by
  have h := L2_sound
  split_ifs with hk
  · push_cast; exact mul_le_mul_of_nonneg_left h.2 (by exact_mod_cast hk)
  · push_cast; exact mul_le_mul_of_nonpos_left h.1 (by exact_mod_cast (not_le.mp hk).le)

lemma logLo0_le {q : ℚ} (hq : 0 < q) : ((logLo0 q : ℚ) : ℝ) ≤ Real.log q := by
  unfold logLo0
  set k := logExp q
  set m := q/pow2 k
  have hm : 0 < m := div_pos hq (pow2_pos k)
  set ml := if 0 < rdn 60 m then rdn 60 m else m
  have hml : 0 < ml ∧ ml ≤ m := by
    simp only [ml]; split_ifs with h
    · exact ⟨h, rdn_le _ _⟩
    · exact ⟨hm, le_rfl⟩
  rw [log_split hq k, Rat.cast_add]
  have a := int_mul_log2_lo k
  have b := (logMBnd_sound hml.1).1
  have c := Real.log_le_log (by exact_mod_cast hml.1) (show (ml:ℝ) ≤ m by exact_mod_cast hml.2)
  linarith

lemma le_logHi0 {q : ℚ} (hq : 0 < q) : Real.log q ≤ ((logHi0 q : ℚ) : ℝ) := by
  unfold logHi0
  set k := logExp q
  set m := q/pow2 k
  have hm : 0 < m := div_pos hq (pow2_pos k)
  have hmu : m ≤ rup 60 m := le_rup _ _
  rw [log_split hq k, Rat.cast_add]
  have a := int_mul_log2_hi k
  have b := (logMBnd_sound (hm.trans_le hmu)).2
  have c := Real.log_le_log (by exact_mod_cast hm) (show (m:ℝ) ≤ rup 60 m by exact_mod_cast hmu)
  linarith

def logLo (q : ℚ) : ℚ := rdn 160 (logLo0 q)
def logHi (q : ℚ) : ℚ := rup 160 (logHi0 q)

lemma logLo_le {q : ℚ} (hq : 0 < q) : ((logLo q : ℚ) : ℝ) ≤ Real.log q :=
  (rdn_le_real _ _).trans (logLo0_le hq)

lemma le_logHi {q : ℚ} (hq : 0 < q) : Real.log q ≤ ((logHi q : ℚ) : ℝ) :=
  (le_logHi0 hq).trans (le_rup_real _ _)

/-! ### Abstract values -/

/-- Data on a list of divisors: their number, a lower bound on the product of
their magnitudes, upper bounds on the products of `1 + B/|t|`, of
`max(1, |t|)` and of `max(1, 1/|t|)`, and a lower bound on the product of
`min(1, |t|)`. -/
structure DD where
  m : ℕ
  T : ℚ
  P : ℚ
  mn : ℚ
  mx : ℚ
  im : ℚ

def DD.one : DD := ⟨0, 1, 1, 1, 1, 1⟩

/-- Data on a product chain: its number of factors, upper bounds on the
numerators' `Π(|t|+B)` and `Π max(1, |t|+B)`, a lower bound on their `Π|t|`
at the same magnitudes, and its divisors. -/
structure PD where
  n : ℕ
  ψ : ℚ
  M : ℚ
  T : ℚ
  d : DD

def PD.one : PD := ⟨1, 0, 1, 0, DD.one⟩

/-- An interval `[lo, hi]` for an exact value and an upper bound `b` on its
running error bound. -/
structure Av where
  lo : ℚ
  hi : ℚ
  b : ℚ
  /-- Whether the value is a sum chain (`WgslReassoc`), with its number of
  leaves and upper bounds on the sums of the leaf magnitudes and leaf bounds;
  used to bound every reassociation of the chain. -/
  sc : Bool
  sn : ℕ
  sm : ℚ
  sb : ℚ
  /-- Whether the value is a product chain, with its data. -/
  pc : Bool
  pd : PD
  /-- Whether the value is a product `*`, with the data of its factors as
  divisors. -/
  mc : Bool
  md : DD

/-- A value that is not a chain. -/
abbrev Av.mk3 (lo hi b : ℚ) : Av := ⟨lo, hi, b, false, 1, 0, 0, false, PD.one, false, DD.one⟩

def Av.H (A : Av) (x B : ℝ) : Prop := (A.lo : ℝ) ≤ x ∧ x ≤ A.hi ∧ 0 ≤ B ∧ B ≤ A.b

def mag (A : Av) : ℚ := Max.max |A.lo| |A.hi|

lemma abs_le_mag {A : Av} {x B : ℝ} (h : A.H x B) : |x| ≤ ((mag A : ℚ) : ℝ) := by
  obtain ⟨h1,h2,-,-⟩ := h
  unfold mag; push_cast
  refine abs_le.mpr ⟨?_,?_⟩
  · have := neg_abs_le (A.lo:ℝ); have := le_max_left |(A.lo:ℝ)| |(A.hi:ℝ)|; linarith
  · have := le_abs_self (A.hi:ℝ); have := le_max_right |(A.lo:ℝ)| |(A.hi:ℝ)|; linarith

lemma mag_nonneg (A : Av) : 0 ≤ mag A := le_max_of_le_left (abs_nonneg _)

/-- A lower bound on `|x|` over the interval. -/
def mig (A : Av) : ℚ := if 0 < A.lo then A.lo else if A.hi < 0 then -A.hi else 0

lemma mig_le_abs {A : Av} {x B : ℝ} (h : A.H x B) : ((mig A : ℚ) : ℝ) ≤ |x| := by
  obtain ⟨h1,h2,-,-⟩ := h
  unfold mig
  split_ifs with p q
  · have : (0:ℝ) < A.lo := by exact_mod_cast p
    rw [abs_of_pos (by linarith)]; exact h1
  · have : (A.hi:ℝ) < 0 := by exact_mod_cast q
    rw [abs_of_neg (by linarith)]; push_cast; linarith
  · simp

lemma mig_sign {A : Av} (h : 0 < mig A) : 0 < A.lo ∨ A.hi < 0 := by
  unfold mig at h
  split_ifs at h with p q
  · exact Or.inl p
  · exact Or.inr q
  · exact absurd h (lt_irrefl 0)

def nrm (A : Av) : Av := Av.mk3 (rdn 160 A.lo) (rup 160 A.hi) (rup 160 A.b)

lemma Av.H.nrm {A : Av} {x B : ℝ} (h : A.H x B) : (nrm A).H x B :=
  ⟨(rdn_le_real _ _).trans h.1, h.2.1.trans (le_rup_real _ _), h.2.2.1,
    h.2.2.2.trans (le_rup_real _ _)⟩

/-- The same interval and bound, not a sum chain. -/
abbrev Av.leaf (A : Av) : Av := Av.mk3 A.lo A.hi A.b

def join (A B : Av) : Av := Av.mk3 (Min.min A.lo B.lo) (Max.max A.hi B.hi) (Max.max A.b B.b)

lemma Av.H.join_l {A : Av} {x B : ℝ} (h : A.H x B) (C : Av) : (join A C).H x B := by
  obtain ⟨h1,h2,h3,h4⟩ := h
  refine ⟨?_,?_,h3,?_⟩ <;> simp only [join] <;> push_cast
  · exact (min_le_left _ _).trans h1
  · exact h2.trans (le_max_left _ _)
  · exact h4.trans (le_max_left _ _)

lemma Av.H.join_r {A : Av} {x B : ℝ} (h : A.H x B) (C : Av) : (join C A).H x B := by
  obtain ⟨h1,h2,h3,h4⟩ := h
  refine ⟨?_,?_,h3,?_⟩ <;> simp only [join] <;> push_cast
  · exact (min_le_right _ _).trans h1
  · exact h2.trans (le_max_right _ _)
  · exact h4.trans (le_max_right _ _)

/-! ### Constants -/

def qu : ℚ := 1/16777216
def qU : ℚ := 5/16777216
def qη : ℚ := 1/85070591730234615865843651857942052864
def q2p126 : ℚ := 85070591730234615865843651857942052864

lemma qu_eq : (qu : ℝ) = u := by simp [qu, u]; norm_num
lemma qU_eq : (qU : ℝ) = WgslPoly.U := by simp [qU, WgslPoly.U, u]; norm_num
lemma qη_eq : (qη : ℝ) = η := by simp [qη, η]; norm_num
lemma q2p126_eq : (q2p126 : ℝ) = 2^126 := by simp [q2p126]; norm_num

/-! A value's sum-chain data: its own leaves if it is a chain, else itself as
the only leaf. -/
def sdn (A : Av) : ℕ := if A.sc then A.sn else 1
def sdm (A : Av) : ℚ := if A.sc then A.sm else mag A
def sdb (A : Av) : ℚ := if A.sc then A.sb else A.b

/-- The bound `((1+U)ⁿ⁻¹ - 1) Σ|tᵢ| + (1+U)ⁿ⁻¹ Σ Bᵢ + (n-1)(1+U)ⁿ⁻¹ η` of every
association of a chain (`WgslReassoc.sum_bound`). -/
def chainB (n : ℕ) (sm sb : ℚ) : ℚ := ((1+qU)^(n-1)-1)*sm+(1+qU)^(n-1)*sb+(n-1)*(1+qU)^(n-1)*qη

/-- A sum chain: `R`'s interval, its bound raised to cover every association. -/
def chainAv (R : Av) (n : ℕ) (sm sb : ℚ) : Av :=
  ⟨R.lo, R.hi, rup 160 (Max.max R.b (chainB n sm sb)), true, n, sm, sb, false, PD.one, false, DD.one⟩

/-! A value's product-chain data: its own factors if it is a product chain,
else itself as the only numerator; and its factors as divisors. -/
def DD.mul (x y : DD) : DD :=
  ⟨x.m+y.m, rdn 160 (x.T*y.T), rup 160 (x.P*y.P), rdn 160 (x.mn*y.mn), rup 160 (x.mx*y.mx),
    rup 160 (x.im*y.im)⟩
def DD.leaf (A : Av) : DD :=
  ⟨1, mig A, rup 160 (1+A.b/mig A), Min.min 1 (mig A), Max.max 1 (mag A), rup 160 (Max.max 1 (1/mig A))⟩
def PD.leaf (A : Av) : PD := ⟨1, mag A+A.b, Max.max 1 (mag A+A.b), mag A, DD.one⟩
def PD.mul (p q : PD) : PD :=
  ⟨p.n+q.n, rup 160 (p.ψ*q.ψ), rup 160 (p.M*q.M), rdn 160 (p.T*q.T), p.d.mul q.d⟩
def PD.div (p : PD) (m : DD) : PD := ⟨p.n+m.m, p.ψ, p.M, p.T, p.d.mul m⟩
def pdOf (A : Av) : PD := if A.pc then A.pd else PD.leaf A
def mdOf (A : Av) : DD := if A.mc then A.md else DD.leaf A

/-- `U'` and `2⁻¹⁰⁰` as rationals. -/
def qU' : ℚ := 5/16777216+1/67108864
def q2m100 : ℚ := 1/1267650600228229401496703205376

/-- The bound of every role-preserving association of a product chain
(`WgslReassoc.prod_bound`), if its margins hold. -/
def chainPB (p : PD) : Option ℚ :=
  -- `Xq` and `Kq` bound `P (1+U')ᵐ⁻¹` and `(1+U)ⁿ⁻¹` by `(1+x)ᵏ ≤ 1/(1-kx)`,
  -- and `Mq` bounds `M im/cᵐ`.
  let Xq := p.d.P/(1-((p.d.m-1 : ℕ) : ℚ)*qU')
  let Kq := 1/(1-((p.n-1 : ℕ) : ℚ)*qU)
  let Mq := p.M*p.d.im/(2-Xq)^p.d.m
  if 0 < p.d.T ∧ p.n ≤ 64 ∧ Xq < 2 ∧ q2m100 ≤ p.d.mn ∧
      qη ≤ p.d.mn*(2-Xq) ∧ p.d.mx*Xq ≤ q2p126 ∧ Mq ≤ 1237940039285380274899124224
  then some ((Kq/(2-Xq)*p.ψ-p.T)/p.d.T+2*((p.n:ℚ)-1)*Kq*qη*Mq)
  else none

/-- A product chain: `R`'s interval, its bound raised to cover every
role-preserving association. -/
def prodAv (R : Av) (cb : ℚ) (p : PD) (mc : Bool) (md : DD) : Av :=
  ⟨R.lo, R.hi, rup 160 (Max.max R.b cb), false, 1, 0, 0, true, p, mc, md⟩

lemma Av.H.prod {R : Av} {x B : ℝ} (h : R.H x B) (cb : ℚ) (p : PD) (mc : Bool) (md : DD) :
    (prodAv R cb p mc md).H x B :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans (by
    simp only [prodAv]; exact (show ((R.b:ℚ):ℝ) ≤ ((Max.max R.b cb : ℚ) : ℝ) by
      exact_mod_cast le_max_left _ _).trans (le_rup_real _ _))⟩

lemma Av.H.chain {R : Av} {x B : ℝ} (h : R.H x B) (n : ℕ) (sm sb : ℚ) : (chainAv R n sm sb).H x B :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans (by
    simp only [chainAv]; exact (show ((R.b:ℚ):ℝ) ≤ ((Max.max R.b (chainB n sm sb) : ℚ) : ℝ) by
      exact_mod_cast le_max_left _ _).trans (le_rup_real _ _))⟩

/-! ### Interval products -/

def mulLo (a b c d : ℚ) : ℚ := Min.min (Min.min (a*c) (a*d)) (Min.min (b*c) (b*d))
def mulHi (a b c d : ℚ) : ℚ := Max.max (Max.max (a*c) (a*d)) (Max.max (b*c) (b*d))

lemma lin_lo {a b x y : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) : Min.min (a*y) (b*y) ≤ x*y := by
  rcases le_total 0 y with hy | hy
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right h1 hy)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right h2 hy)

lemma lin_hi {a b x y : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) : x*y ≤ Max.max (a*y) (b*y) := by
  rcases le_total 0 y with hy | hy
  · exact (mul_le_mul_of_nonneg_right h2 hy).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_right h1 hy).trans (le_max_left _ _)

lemma mul_mem {a b c d : ℚ} {x y : ℝ} (h1 : (a:ℝ) ≤ x) (h2 : x ≤ b) (h3 : (c:ℝ) ≤ y)
    (h4 : y ≤ d) : ((mulLo a b c d : ℚ) : ℝ) ≤ x*y ∧ x*y ≤ ((mulHi a b c d : ℚ) : ℝ) := by
  unfold mulLo mulHi; push_cast
  have l1 : Min.min ((a:ℝ)*c) ((a:ℝ)*d) ≤ (a:ℝ)*y := by
    have := lin_lo (y := (a:ℝ)) h3 h4; rwa [mul_comm (c:ℝ), mul_comm (d:ℝ), mul_comm y] at this
  have l2 : Min.min ((b:ℝ)*c) ((b:ℝ)*d) ≤ (b:ℝ)*y := by
    have := lin_lo (y := (b:ℝ)) h3 h4; rwa [mul_comm (c:ℝ), mul_comm (d:ℝ), mul_comm y] at this
  have u1 : (a:ℝ)*y ≤ Max.max ((a:ℝ)*c) ((a:ℝ)*d) := by
    have := lin_hi (y := (a:ℝ)) h3 h4; rwa [mul_comm (c:ℝ), mul_comm (d:ℝ), mul_comm y] at this
  have u2 : (b:ℝ)*y ≤ Max.max ((b:ℝ)*c) ((b:ℝ)*d) := by
    have := lin_hi (y := (b:ℝ)) h3 h4; rwa [mul_comm (c:ℝ), mul_comm (d:ℝ), mul_comm y] at this
  exact ⟨(min_le_min l1 l2).trans (lin_lo h1 h2), (lin_hi h1 h2).trans (max_le_max u1 u2)⟩

/-! ### Operations -/

def addAv (A B : Av) : Av :=
  Av.mk3 (A.lo+B.lo) (A.hi+B.hi) (A.b+B.b+qU*(mag A+mag B+A.b+B.b)+qη)
def subAv (A B : Av) : Av :=
  Av.mk3 (A.lo-B.hi) (A.hi-B.lo) (A.b+B.b+qU*(mag A+mag B+A.b+B.b)+qη)
def mulB (A B : Av) : ℚ := mag A*B.b+mag B*A.b+A.b*B.b+qU*((mag A+A.b)*(mag B+B.b))+qη
def mulAv (A B : Av) : Av := Av.mk3 (mulLo A.lo A.hi B.lo B.hi) (mulHi A.lo A.hi B.lo B.hi) (mulB A B)
def sqAv (A : Av) : Av :=
  Av.mk3 (if 0 ≤ A.lo then A.lo*A.lo else if A.hi ≤ 0 then A.hi*A.hi else 0) (Max.max (A.lo*A.lo) (A.hi*A.hi)) (mulB A A)
def divOk (B : Av) : Prop := B.b < mig B ∧ qη ≤ mig B-B.b ∧ mag B+B.b ≤ q2p126
instance (B : Av) : Decidable (divOk B) := by unfold divOk; infer_instance
def divAv (A B : Av) : Av :=
  Av.mk3 (mulLo A.lo A.hi (1/B.hi) (1/B.lo)) (mulHi A.lo A.hi (1/B.hi) (1/B.lo)) ((A.b+mag A/mig B*B.b)/(mig B-B.b)+qU*((mag A+A.b)/(mig B-B.b))+qη)
def sqrtOk (A : Av) : Prop := 0 < A.lo ∧ A.b ≤ A.lo ∧ 0 < sqLo A.lo
instance (A : Av) : Decidable (sqrtOk A) := by unfold sqrtOk; infer_instance
def sqrtAv (A : Av) : Av :=
  Av.mk3 (sqLo A.lo) (sqHi A.hi) (A.b/sqLo A.lo+10*qu*sqHi (A.hi+A.b)+qη)
def invOk (A : Av) : Prop := A.b < A.lo ∧ 0 < sqLo (A.lo-A.b) ∧ 0 < sqLo A.lo
instance (A : Av) : Decidable (invOk A) := by unfold invOk; infer_instance
def invAv (A : Av) : Av :=
  Av.mk3 (1/sqHi A.hi) (1/sqLo A.lo) (A.b/(sqLo (A.lo-A.b)*sqLo A.lo*(sqLo (A.lo-A.b)+sqLo A.lo))+4*qu/sqLo (A.lo-A.b))
def absAv (A : Av) : Av :=
  Av.mk3 (if 0 ≤ A.lo then A.lo else if A.hi ≤ 0 then -A.hi else 0) (mag A) A.b
/-- `exp` arguments are kept moderate so that the enclosures stay small. -/
def expOk (A : Av) : Prop := -256 ≤ A.lo ∧ A.hi+A.b ≤ 256 ∧ A.b ≤ 256
instance (A : Av) : Decidable (expOk A) := by unfold expOk; infer_instance
def expAv (A : Av) : Av :=
  Av.mk3 (expLo A.lo) (expHi A.hi) (expHi A.hi*(expHi A.b-1)+(3+2*(mag A+A.b))*(2*qu*expHi (A.hi+A.b)+qη))
def exp2Av (A : Av) : Av :=
  Av.mk3 (expLo (mulLo A.lo A.hi L2lo L2hi)) (expHi (mulHi A.lo A.hi L2lo L2hi)) (expHi (mulHi A.lo A.hi L2lo L2hi)*(expHi (A.b*L2hi)-1)+ (3+2*(mag A+A.b))*(2*qu*expHi (mulHi A.lo (A.hi+A.b) L2lo L2hi)+qη))
def logAv (A : Av) : Av :=
  Av.mk3 (logLo A.lo) (logHi A.hi) (A.b/(A.lo-A.b)+1/2097152+ 3*(2*qu*(Max.max |logLo A.lo| |logHi A.hi|+A.b/(A.lo-A.b))+qη))
def log2Lo (A : Av) : ℚ := Min.min (logLo A.lo/L2lo) (logLo A.lo/L2hi)
def log2Hi (A : Av) : ℚ := Max.max (logHi A.hi/L2lo) (logHi A.hi/L2hi)
def log2Av (A : Av) : Av :=
  Av.mk3 (log2Lo A) (log2Hi A) (A.b/((A.lo-A.b)*L2lo)+1/2097152+ 3*(2*qu*(Max.max |log2Lo A| |log2Hi A|+A.b/((A.lo-A.b)*L2lo))+qη))
def trigAv (lo hi : ℚ) (A : Av) : Av := Av.mk3 lo hi (A.b+128*qu*(1+(mag A+A.b)))
/-- `sin` on `[-1, 1]`, where it is increasing, from its Taylor bound. -/
def sinLo (A : Av) : ℚ := if -1 ≤ A.lo ∧ A.hi ≤ 1 then A.lo-A.lo^3/6-|A.lo|^5/100 else -1
def sinHi (A : Av) : ℚ := if -1 ≤ A.lo ∧ A.hi ≤ 1 then A.hi-A.hi^3/6+|A.hi|^5/100 else 1
def cosLo (A : Av) : ℚ := Max.max (-1) (1-mag A^2/2)
/-- `tanh x = 1 - 2/(exp (2x) + 1)`, increasing. -/
def tanhLo (x : ℚ) : ℚ := if -128 ≤ x ∧ x ≤ 128 then 1-2/(expLo (2*x)+1) else -1
def tanhHi (x : ℚ) : ℚ := if -128 ≤ x ∧ x ≤ 128 then 1-2/(expHi (2*x)+1) else 1
def scaleAv (k : ℤ) (A : Av) : Av := Av.mk3 (pow2 k*A.lo) (pow2 k*A.hi) (pow2 k*A.b+qη)

/-- Evaluates `g` on `2^n` equal pieces of `A`'s interval and joins the results. -/
def bisect (g : Av → Option Av) : ℕ → Av → Option Av
  | 0, A => g A
  | n+1, A =>
    (bisect g n (Av.mk3 A.lo (rdn 160 ((A.lo+A.hi)/2)) A.b)).bind fun L =>
      (bisect g n (Av.mk3 (rdn 160 ((A.lo+A.hi)/2)) A.hi A.b)).bind fun R => some (join L R)

/-- The interval evaluator; the arguments of `inh` and `tanh` builtins are
split into `2^d` pieces. -/
def ev (d : ℕ) (env : ℕ → Option Av) : GExpr → Option Av
  | .input i => if i < WgslLets.letBase then (env i).map Av.leaf else env i
  | .const c => some (Av.mk3 c c 0)
  | .add a b => (ev d env a).bind fun A => (ev d env b).bind fun B =>
      some (chainAv (nrm (addAv A B)) (sdn A+sdn B) (sdm A+sdm B) (sdb A+sdb B))
  | .sub a b => (ev d env a).bind fun A => (ev d env b).bind fun B =>
      some (chainAv (nrm (subAv A B)) (sdn A+sdn B) (sdm A+sdm B) (sdb A+sdb B))
  | .mul a b => (ev d env a).bind fun A => (if a = b then some A else ev d env b).bind fun B =>
      (chainPB ((pdOf A).mul (pdOf B))).map fun cb =>
        prodAv (nrm (if a = b then sqAv A else mulAv A B)) cb ((pdOf A).mul (pdOf B)) true
          ((mdOf A).mul (mdOf B))
  | .neg a => (ev d env a).bind fun A =>
      some (chainAv (Av.mk3 (-A.hi) (-A.lo) A.b) (sdn A) (sdm A) (sdb A))
  | .div a b => (ev d env a).bind fun A => (ev d env b).bind fun B =>
      if divOk B then (chainPB ((pdOf A).div (mdOf B))).map fun cb =>
        prodAv (nrm (divAv A B)) cb ((pdOf A).div (mdOf B)) false DD.one else none
  | .sqrt a => (ev d env a).bind fun A => if sqrtOk A then some (nrm (sqrtAv A)) else none
  | .max a b => (ev d env a).bind fun A => (ev d env b).bind fun B =>
      some (Av.mk3 (Max.max A.lo B.lo) (Max.max A.hi B.hi) (Max.max A.b B.b))
  | .min a b => (ev d env a).bind fun A => (ev d env b).bind fun B =>
      some (Av.mk3 (Min.min A.lo B.lo) (Min.min A.hi B.hi) (Max.max A.b B.b))
  | .lt c t a b => (ev d env c).bind fun C =>
      if C.hi+C.b < t then (ev d env a).map Av.leaf
      else if t < C.lo-C.b then (ev d env b).map Av.leaf else none
  | .abs a => (ev d env a).bind fun A => some (absAv A)
  | .invsqrt a => (ev d env a).bind fun A => if invOk A then some (nrm (invAv A)) else none
  | .exp a => (ev d env a).bind fun A => if expOk A then some (nrm (expAv A)) else none
  | .exp2 a => (ev d env a).bind fun A => if expOk A then some (nrm (exp2Av A)) else none
  | .log a => (ev d env a).bind fun A => if A.b < A.lo then some (nrm (logAv A)) else none
  | .log2 a => (ev d env a).bind fun A => if A.b < A.lo then some (nrm (log2Av A)) else none
  | .inh f a => (ev d env a).bind fun A =>
      (bisect (fun A' => ev d (fun _ => some A'.leaf) f) d A).map Av.leaf
  | .tanh f a => if f = WgslPlasma.tanhInh then (ev d env a).bind fun A =>
      (bisect (fun A' => ev d (fun _ => some A'.leaf) f) d A).bind fun R =>
        some (nrm (Av.mk3 (tanhLo A.lo) (tanhHi A.hi) (Max.max (A.b+1/100000) R.b))) else none
  | .lt2 a b x y => (ev d env a).bind fun A => (ev d env b).bind fun B =>
      if A.hi-B.lo+(A.b+B.b) < 0 then (ev d env x).map Av.leaf
      else if B.hi-A.lo+(A.b+B.b) < 0 then (ev d env y).map Av.leaf else none
  | .sinS a => (ev d env a).bind fun A =>
      if mag A+A.b ≤ 262144 then some (nrm (trigAv (sinLo A) (sinHi A) A)) else none
  | .cosS a => (ev d env a).bind fun A =>
      if mag A+A.b ≤ 262144 then some (nrm (trigAv (cosLo A) 1 A)) else none
  | .scale k a => (ev d env a).bind fun A => some (nrm (scaleAv k A))
  | .round _ => none
  | .qsel _ _ _ _ => none

/-! ### Soundness of the operations -/

section Ops
variable {A B : Av} {x y X Y : ℝ}

lemma Av.H.b_nonneg (h : A.H x X) : (0:ℝ) ≤ A.b := h.2.2.1.trans h.2.2.2

lemma add_H (hA : A.H x X) (hB : B.H y Y) :
    (addAv A B).H (x+y) (X+Y+WgslPoly.U*(|x|+|y|+X+Y)+η) := by
  have ma := abs_le_mag hA; have mb := abs_le_mag hB
  obtain ⟨a1,a2,a3,a4⟩ := hA; obtain ⟨b1,b2,b3,b4⟩ := hB
  have hU := WgslPoly.U_pos; have hη := η_pos
  simp only [Av.H, addAv]; push_cast; rw [qU_eq, qη_eq]
  refine ⟨by linarith, by linarith, by positivity, by gcongr⟩

lemma sub_H (hA : A.H x X) (hB : B.H y Y) :
    (subAv A B).H (x-y) (X+Y+WgslPoly.U*(|x|+|y|+X+Y)+η) := by
  have ma := abs_le_mag hA; have mb := abs_le_mag hB
  obtain ⟨a1,a2,a3,a4⟩ := hA; obtain ⟨b1,b2,b3,b4⟩ := hB
  have hU := WgslPoly.U_pos; have hη := η_pos
  simp only [Av.H, subAv]; push_cast; rw [qU_eq, qη_eq]
  refine ⟨by linarith, by linarith, by positivity, by gcongr⟩

lemma mulB_le (hA : A.H x X) (hB : B.H y Y) :
    |x| *Y+|y| *X+X*Y+WgslPoly.U*((|x|+X)*(|y|+Y))+η ≤ ((mulB A B : ℚ) : ℝ) := by
  have ma := abs_le_mag hA; have mb := abs_le_mag hB
  obtain ⟨a1,a2,a3,a4⟩ := hA; obtain ⟨b1,b2,b3,b4⟩ := hB
  have hU := WgslPoly.U_pos
  simp only [mulB]; push_cast; rw [qU_eq, qη_eq]
  have e1 : |x| *Y ≤ (mag A:ℝ)*B.b := mul_le_mul ma b4 b3 ((abs_nonneg _).trans ma)
  have e2 : |y| *X ≤ (mag B:ℝ)*A.b := mul_le_mul mb a4 a3 ((abs_nonneg _).trans mb)
  have e3 : X*Y ≤ (A.b:ℝ)*B.b := mul_le_mul a4 b4 b3 (a3.trans a4)
  have e4 : (|x|+X)*(|y|+Y) ≤ ((mag A:ℝ)+A.b)*((mag B:ℝ)+B.b) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith [abs_nonneg x])
  have := mul_le_mul_of_nonneg_left e4 hU.le
  linarith

lemma mulB_nonneg (hA : A.H x X) (hB : B.H y Y) :
    0 ≤ |x| *Y+|y| *X+X*Y+WgslPoly.U*((|x|+X)*(|y|+Y))+η := by
  have := hA.2.2.1; have := hB.2.2.1; have := WgslPoly.U_pos; have := η_pos; positivity

lemma mul_H (hA : A.H x X) (hB : B.H y Y) :
    (mulAv A B).H (x*y) (|x| *Y+|y| *X+X*Y+WgslPoly.U*((|x|+X)*(|y|+Y))+η) := by
  have m := mul_mem hA.1 hA.2.1 hB.1 hB.2.1
  exact ⟨m.1, m.2, mulB_nonneg hA hB, mulB_le hA hB⟩

lemma sq_H (hA : A.H x X) :
    (sqAv A).H (x*x) (|x| *X+|x| *X+X*X+WgslPoly.U*((|x|+X)*(|x|+X))+η) := by
  refine ⟨?_,?_,mulB_nonneg hA hA,mulB_le hA hA⟩
  · obtain ⟨a1,a2,-,-⟩ := hA
    simp only [sqAv]
    split_ifs with p q
    · have : (0:ℝ) ≤ A.lo := by exact_mod_cast p
      push_cast; nlinarith
    · have : (A.hi:ℝ) ≤ 0 := by exact_mod_cast q
      push_cast; nlinarith
    · push_cast; nlinarith
  · have ma := abs_le_mag hA
    simp only [sqAv]; push_cast
    have h1 : x*x ≤ (mag A:ℝ)*(mag A) := by
      rw [← abs_mul_abs_self x]; exact mul_le_mul ma ma (abs_nonneg _) ((abs_nonneg _).trans ma)
    have h2 : ((mag A : ℚ):ℝ)*(mag A) = Max.max ((A.lo:ℝ)*A.lo) ((A.hi:ℝ)*A.hi) := by
      unfold mag; push_cast
      rcases le_total |(A.lo:ℝ)| |(A.hi:ℝ)| with h | h
      · rw [max_eq_right h, max_eq_right, abs_mul_abs_self]
        rw [← abs_mul_abs_self (A.lo:ℝ), ← abs_mul_abs_self (A.hi:ℝ)]
        exact mul_le_mul h h (abs_nonneg _) ((abs_nonneg _).trans h)
      · rw [max_eq_left h, max_eq_left, abs_mul_abs_self]
        rw [← abs_mul_abs_self (A.lo:ℝ), ← abs_mul_abs_self (A.hi:ℝ)]
        exact mul_le_mul h h (abs_nonneg _) ((abs_nonneg _).trans h)
    linarith

lemma neg_H (hA : A.H x X) : (Av.mk3 (-A.hi) (-A.lo) A.b).H (-x) X := by
  obtain ⟨a1,a2,a3,a4⟩ := hA
  refine ⟨?_,?_,a3,a4⟩ <;> push_cast <;> linarith

lemma inv_mem (hB : B.H y Y) (h : 0 < B.lo ∨ B.hi < 0) :
    ((1/B.hi : ℚ) : ℝ) ≤ 1/y ∧ 1/y ≤ ((1/B.lo : ℚ) : ℝ) := by
  obtain ⟨b1,b2,-,-⟩ := hB
  push_cast
  rcases h with h | h
  · have : (0:ℝ) < B.lo := by exact_mod_cast h
    exact ⟨one_div_le_one_div_of_le (by linarith) b2, one_div_le_one_div_of_le this b1⟩
  · have : (B.hi:ℝ) < 0 := by exact_mod_cast h
    exact ⟨one_div_le_one_div_of_neg_of_le this b2, one_div_le_one_div_of_neg_of_le (by linarith) b1⟩

lemma div_H (hA : A.H x X) (hB : B.H y Y) (ok : divOk B) :
    (divAv A B).H (x/y) ((X+|x/y| *Y)/(|y|-Y)+WgslPoly.U*((|x|+X)/(|y|-Y))+η) ∧
      Y < |y| ∧ 1/2^126 ≤ |y|-Y ∧ |y|+Y ≤ 2^126 := by
  obtain ⟨o1,o2,o3⟩ := ok
  have ma := abs_le_mag hA; have mb := abs_le_mag hB; have mi := mig_le_abs hB
  have hBb := hB.b_nonneg
  have o1' : (B.b:ℝ) < mig B := by exact_mod_cast o1
  have o2' : (qη:ℝ) ≤ (mig B:ℝ)-B.b := by exact_mod_cast o2
  have o3' : (mag B:ℝ)+B.b ≤ q2p126 := by exact_mod_cast o3
  rw [qη_eq] at o2'; rw [q2p126_eq] at o3'
  obtain ⟨a1,a2,a3,a4⟩ := hA
  have b3 := hB.2.2.1; have b4 := hB.2.2.2
  have hmig : (0:ℚ) < mig B := by
    have : (0:ℝ) < mig B := by linarith
    exact_mod_cast this
  have hy : 0 < |y| := by linarith
  have hd : (0:ℝ) < (mig B:ℝ)-B.b := by linarith
  have hd' : (mig B:ℝ)-B.b ≤ |y|-Y := by linarith
  have hU := WgslPoly.U_pos; have hη := η_pos
  refine ⟨⟨?_,?_,?_,?_⟩,by linarith,?_,by linarith⟩
  · have := inv_mem hB (mig_sign hmig)
    have m := mul_mem a1 a2 this.1 this.2
    rw [← div_eq_mul_one_div] at m; exact m.1
  · have := inv_mem hB (mig_sign hmig)
    have m := mul_mem a1 a2 this.1 this.2
    rw [← div_eq_mul_one_div] at m; exact m.2
  · have : 0 < |y|-Y := by linarith
    positivity
  · simp only [divAv]; push_cast; rw [qU_eq, qη_eq]
    have hq : |x/y| ≤ (mag A:ℝ)/mig B := by
      rw [abs_div]; exact div_le_div₀ ((abs_nonneg _).trans ma) ma (by linarith) mi
    have n1 : X+|x/y| *Y ≤ (A.b:ℝ)+(mag A:ℝ)/mig B*B.b :=
      add_le_add a4 (mul_le_mul hq b4 b3 (div_nonneg ((abs_nonneg _).trans ma) (by linarith)))
    have t1 := div_le_div₀ (by linarith [abs_nonneg (x/y), mul_nonneg (abs_nonneg (x/y)) b3])
      n1 hd hd'
    have t2 := div_le_div₀ (by linarith [abs_nonneg x]) (show |x|+X ≤ (mag A:ℝ)+A.b by linarith)
      hd hd'
    have := mul_le_mul_of_nonneg_left t2 hU.le
    linarith
  · have : η = 1/2^126 := rfl
    linarith

lemma sqrt_H (hA : A.H x X) (ok : sqrtOk A) :
    (sqrtAv A).H (Real.sqrt x) (X/Real.sqrt x+10*u*Real.sqrt (x+X)+η) ∧ 0 < x ∧ X ≤ x := by
  obtain ⟨o1,o2,o3⟩ := ok
  obtain ⟨a1,a2,a3,a4⟩ := hA
  have o1' : (0:ℝ) < A.lo := by exact_mod_cast o1
  have o2' : (A.b:ℝ) ≤ A.lo := by exact_mod_cast o2
  have o3' : (0:ℝ) < sqLo A.lo := by exact_mod_cast o3
  have hx : 0 < x := by linarith
  have s1 : (sqLo A.lo:ℝ) ≤ Real.sqrt x :=
    (sqLo_le _).trans (Real.sqrt_le_sqrt a1)
  have hu := u_pos; have hη := η_pos
  refine ⟨⟨s1,?_,by positivity,?_⟩,hx,by linarith⟩
  · exact (Real.sqrt_le_sqrt a2).trans (le_sqHi _)
  · simp only [sqrtAv]; push_cast; rw [qu_eq, qη_eq]
    have t1 : X/Real.sqrt x ≤ (A.b:ℝ)/sqLo A.lo := div_le_div₀ (by linarith) a4 o3' s1
    have t2 : Real.sqrt (x+X) ≤ (sqHi (A.hi+A.b) : ℝ) := by
      refine (Real.sqrt_le_sqrt (by push_cast; linarith : x+X ≤ ((A.hi+A.b : ℚ) : ℝ))).trans ?_
      exact le_sqHi _
    have := mul_le_mul_of_nonneg_left t2 (by positivity : (0:ℝ) ≤ 10*u)
    linarith

lemma inv_H (hA : A.H x X) (ok : invOk A) :
    (invAv A).H (1/Real.sqrt x) (X/(Real.sqrt (x-X)*Real.sqrt x*(Real.sqrt (x-X)+Real.sqrt x))+
      4*u/Real.sqrt (x-X)) ∧ X < x := by
  obtain ⟨o1,o2,o3⟩ := ok
  obtain ⟨a1,a2,a3,a4⟩ := hA
  have o1' : (A.b:ℝ) < A.lo := by exact_mod_cast o1
  have o2' : (0:ℝ) < sqLo (A.lo-A.b) := by exact_mod_cast o2
  have o3' : (0:ℝ) < sqLo A.lo := by exact_mod_cast o3
  have hx : 0 < x := by linarith
  have s1 : (sqLo (A.lo-A.b):ℝ) ≤ Real.sqrt (x-X) :=
    (sqLo_le _).trans (Real.sqrt_le_sqrt (by push_cast; linarith))
  have s2 : (sqLo A.lo:ℝ) ≤ Real.sqrt x := (sqLo_le _).trans (Real.sqrt_le_sqrt a1)
  have hu := u_pos
  have sx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  refine ⟨⟨?_,?_,?_,?_⟩,by linarith⟩
  · simp only [invAv]; push_cast
    have hhi : (0:ℚ) < A.hi := by exact_mod_cast (show (0:ℝ) < A.hi by linarith)
    exact one_div_le_one_div_of_le sx ((Real.sqrt_le_sqrt a2).trans (le_sqHi _))
  · simp only [invAv]; push_cast; exact one_div_le_one_div_of_le o3' s2
  · have : 0 < Real.sqrt (x-X) := o2'.trans_le s1
    positivity
  · simp only [invAv]; push_cast; rw [qu_eq]
    have d1 : (0:ℝ) < (sqLo (A.lo-A.b):ℝ)*sqLo A.lo*(sqLo (A.lo-A.b)+sqLo A.lo) := by positivity
    have d2 : (sqLo (A.lo-A.b):ℝ)*sqLo A.lo*(sqLo (A.lo-A.b)+sqLo A.lo) ≤
        Real.sqrt (x-X)*Real.sqrt x*(Real.sqrt (x-X)+Real.sqrt x) := by
      gcongr
    have t1 := div_le_div₀ (by linarith) a4 d1 d2
    have t2 : 4*u/Real.sqrt (x-X) ≤ 4*u/(sqLo (A.lo-A.b):ℝ) :=
      div_le_div_of_nonneg_left (by positivity) o2' s1
    linarith

lemma abs_H (hA : A.H x X) : (absAv A).H |x| X := by
  have ma := abs_le_mag hA
  obtain ⟨a1,a2,a3,a4⟩ := hA
  refine ⟨?_,ma,a3,a4⟩
  simp only [absAv]
  split_ifs with p q
  · have : (0:ℝ) ≤ A.lo := by exact_mod_cast p
    rw [abs_of_nonneg (by linarith)]; exact a1
  · have : (A.hi:ℝ) ≤ 0 := by exact_mod_cast q
    rw [abs_of_nonpos (by linarith)]; push_cast; linarith
  · simp

lemma max_H (hA : A.H x X) (hB : B.H y Y) :
    (Av.mk3 (Max.max A.lo B.lo) (Max.max A.hi B.hi) (Max.max A.b B.b)).H (Max.max x y) (Max.max X Y) := by
  obtain ⟨a1,a2,a3,a4⟩ := hA; obtain ⟨b1,b2,b3,b4⟩ := hB
  refine ⟨?_,?_,le_max_of_le_left a3,?_⟩ <;> push_cast
  · exact max_le_max a1 b1
  · exact max_le_max a2 b2
  · exact max_le_max a4 b4

lemma min_H (hA : A.H x X) (hB : B.H y Y) :
    (Av.mk3 (Min.min A.lo B.lo) (Min.min A.hi B.hi) (Max.max A.b B.b)).H (Min.min x y) (Max.max X Y) := by
  obtain ⟨a1,a2,a3,a4⟩ := hA; obtain ⟨b1,b2,b3,b4⟩ := hB
  refine ⟨?_,?_,le_max_of_le_left a3,?_⟩ <;> push_cast
  · exact min_le_min a1 b1
  · exact min_le_min a2 b2
  · exact max_le_max a4 b4

lemma exp_H (hA : A.H x X) :
    (expAv A).H (Real.exp x) (Real.exp x*(Real.exp X-1)+(3+2*(|x|+X))*(2*u*Real.exp (x+X)+η)) := by
  have ma := abs_le_mag hA
  obtain ⟨a1,a2,a3,a4⟩ := hA
  have hu := u_pos; have hη := η_pos
  have hX1 : 0 ≤ Real.exp X-1 := by linarith [Real.add_one_le_exp X]
  refine ⟨(expLo_le _).trans (Real.exp_le_exp.mpr a1),
    (Real.exp_le_exp.mpr a2).trans (le_expHi _),by positivity,?_⟩
  simp only [expAv]; push_cast; rw [qu_eq, qη_eq]
  have e1 : Real.exp x ≤ (expHi A.hi : ℝ) := (Real.exp_le_exp.mpr a2).trans (le_expHi _)
  have e2 : Real.exp X-1 ≤ (expHi A.b : ℝ)-1 := by
    linarith [(Real.exp_le_exp.mpr a4).trans (le_expHi A.b)]
  have e3 : Real.exp (x+X) ≤ (expHi (A.hi+A.b) : ℝ) :=
    (Real.exp_le_exp.mpr (by push_cast; linarith)).trans (le_expHi _)
  have t1 := mul_le_mul e1 e2 hX1 ((Real.exp_pos _).le.trans e1)
  have t2 : (3+2*(|x|+X))*(2*u*Real.exp (x+X)+η) ≤
      (3+2*((mag A:ℝ)+A.b))*(2*u*(expHi (A.hi+A.b):ℝ)+η) := by
    apply mul_le_mul (by linarith) (by gcongr) (by positivity) (by linarith [abs_nonneg x])
  linarith

lemma exp2_H (hA : A.H x X) :
    (exp2Av A).H (exp2R x) (exp2R x*(exp2R X-1)+(3+2*(|x|+X))*(2*u*exp2R (x+X)+η)) := by
  have ma := abs_le_mag hA
  have hL := L2_sound
  have l0 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨a1,a2,a3,a4⟩ := hA
  have hu := u_pos; have hη := η_pos
  have m1 := mul_mem a1 a2 hL.1 hL.2
  have m2 := mul_mem (show (A.lo:ℝ) ≤ x+X by linarith) (show x+X ≤ ((A.hi+A.b : ℚ) : ℝ) by push_cast; linarith) hL.1 hL.2
  unfold exp2R
  have hX1 : 0 ≤ Real.exp (X*Real.log 2)-1 := by
    linarith [Real.add_one_le_exp (X*Real.log 2), mul_nonneg a3 l0.le]
  have e1 : Real.exp (x*Real.log 2) ≤ (expHi (mulHi A.lo A.hi L2lo L2hi) : ℝ) :=
    (Real.exp_le_exp.mpr m1.2).trans (le_expHi _)
  refine ⟨(expLo_le _).trans (Real.exp_le_exp.mpr m1.1), e1, by positivity, ?_⟩
  simp only [exp2Av]; push_cast; rw [qu_eq, qη_eq]
  have e2 : Real.exp (X*Real.log 2)-1 ≤ (expHi (A.b*L2hi) : ℝ)-1 := by
    have : X*Real.log 2 ≤ ((A.b*L2hi : ℚ) : ℝ) := by
      push_cast; exact mul_le_mul a4 hL.2 l0.le (a3.trans a4)
    linarith [(Real.exp_le_exp.mpr this).trans (le_expHi (A.b*L2hi))]
  have e3 : Real.exp ((x+X)*Real.log 2) ≤ (expHi (mulHi A.lo (A.hi+A.b) L2lo L2hi) : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith [m2.2])).trans (le_expHi _)
  have t1 := mul_le_mul e1 e2 hX1 ((Real.exp_pos _).le.trans e1)
  have t2 : (3+2*(|x|+X))*(2*u*Real.exp ((x+X)*Real.log 2)+η) ≤
      (3+2*((mag A:ℝ)+A.b))*(2*u*(expHi (mulHi A.lo (A.hi+A.b) L2lo L2hi):ℝ)+η) := by
    apply mul_le_mul (by linarith) (by gcongr) (by positivity) (by linarith [abs_nonneg x])
  linarith

lemma log_H (hA : A.H x X) (ok : A.b < A.lo) :
    (logAv A).H (Real.log x) (X/(x-X)+1/2^21+3*(2*u*(|Real.log x|+X/(x-X))+η)) ∧ X < x := by
  obtain ⟨a1,a2,a3,a4⟩ := hA
  have ok' : (A.b:ℝ) < A.lo := by exact_mod_cast ok
  have hlo : (0:ℚ) < A.lo := by exact_mod_cast (show (0:ℝ) < A.lo by linarith)
  have hhi : (0:ℚ) < A.hi := by exact_mod_cast (show (0:ℝ) < A.hi by linarith)
  have hx : 0 < x := by linarith
  have hu := u_pos; have hη := η_pos
  have l1 : (logLo A.lo:ℝ) ≤ Real.log x := (logLo_le hlo).trans (Real.log_le_log (by linarith) a1)
  have l2 : Real.log x ≤ (logHi A.hi:ℝ) := (Real.log_le_log hx a2).trans (le_logHi hhi)
  refine ⟨⟨l1,l2,?_,?_⟩,by linarith⟩
  · have : 0 < x-X := by linarith
    positivity
  · simp only [logAv]; push_cast; rw [qu_eq, qη_eq]
    have hd : (0:ℝ) < A.lo-A.b := by linarith
    have t1 : X/(x-X) ≤ (A.b:ℝ)/(A.lo-A.b) := div_le_div₀ (by linarith) a4 hd (by linarith)
    have t2 : |Real.log x| ≤ Max.max |(logLo A.lo:ℝ)| |(logHi A.hi:ℝ)| := by
      rw [abs_le]; constructor
      · have := neg_abs_le (logLo A.lo:ℝ); have := le_max_left |(logLo A.lo:ℝ)| |(logHi A.hi:ℝ)|
        linarith
      · have := le_abs_self (logHi A.hi:ℝ); have := le_max_right |(logLo A.lo:ℝ)| |(logHi A.hi:ℝ)|
        linarith
    norm_num
    nlinarith

lemma log2_H (hA : A.H x X) (ok : A.b < A.lo) :
    (log2Av A).H (log2R x) (X/((x-X)*Real.log 2)+1/2^21+
      3*(2*u*(|log2R x|+X/((x-X)*Real.log 2))+η)) ∧ X < x := by
  obtain ⟨a1,a2,a3,a4⟩ := hA
  have ok' : (A.b:ℝ) < A.lo := by exact_mod_cast ok
  have hlo : (0:ℚ) < A.lo := by exact_mod_cast (show (0:ℝ) < A.lo by linarith)
  have hhi : (0:ℚ) < A.hi := by exact_mod_cast (show (0:ℝ) < A.hi by linarith)
  have hx : 0 < x := by linarith
  have hu := u_pos; have hη := η_pos
  have hL := L2_sound
  have L0 : (0:ℝ) < L2lo := by exact_mod_cast L2lo_pos
  have l0 : (0:ℝ) < Real.log 2 := L0.trans_le hL.1
  have l1 : (logLo A.lo:ℝ) ≤ Real.log x := (logLo_le hlo).trans (Real.log_le_log (by linarith) a1)
  have l2 : Real.log x ≤ (logHi A.hi:ℝ) := (Real.log_le_log hx a2).trans (le_logHi hhi)
  have q1 : (log2Lo A:ℝ) ≤ log2R x := by
    unfold log2Lo log2R; push_cast
    rcases le_total 0 (logLo A.lo:ℝ) with h | h
    · refine (min_le_right _ _).trans ?_
      exact (div_le_div_of_nonneg_left h l0 hL.2).trans (div_le_div_of_nonneg_right l1 l0.le)
    · have : (logLo A.lo:ℝ)/L2lo ≤ (logLo A.lo:ℝ)/Real.log 2 := by
        rw [div_le_div_iff₀ L0 l0]; nlinarith [hL.1]
      exact (min_le_left _ _).trans (this.trans (div_le_div_of_nonneg_right l1 l0.le))
  have q2 : log2R x ≤ (log2Hi A:ℝ) := by
    unfold log2Hi log2R; push_cast
    rcases le_total 0 (logHi A.hi:ℝ) with h | h
    · refine le_trans ?_ (le_max_left _ _)
      exact (div_le_div_of_nonneg_right l2 l0.le).trans (div_le_div_of_nonneg_left h L0 hL.1)
    · refine le_trans ?_ (le_max_right _ _)
      have : (logHi A.hi:ℝ)/Real.log 2 ≤ (logHi A.hi:ℝ)/L2hi := by
        rw [div_le_div_iff₀ l0 (l0.trans_le hL.2)]; nlinarith [hL.2]
      exact (div_le_div_of_nonneg_right l2 l0.le).trans this
  refine ⟨⟨q1,q2,?_,?_⟩,by linarith⟩
  · have : 0 < (x-X)*Real.log 2 := mul_pos (by linarith) l0
    positivity
  · simp only [log2Av]; push_cast; rw [qu_eq, qη_eq]
    have hd : (0:ℝ) < (A.lo-A.b)*L2lo := mul_pos (by linarith) L0
    have hd' : ((A.lo:ℝ)-A.b)*L2lo ≤ (x-X)*Real.log 2 :=
      mul_le_mul (by linarith) hL.1 L0.le (by linarith)
    have t1 : X/((x-X)*Real.log 2) ≤ (A.b:ℝ)/((A.lo-A.b)*L2lo) := div_le_div₀ (by linarith) a4 hd hd'
    have t2 : |log2R x| ≤ Max.max |(log2Lo A:ℝ)| |(log2Hi A:ℝ)| := by
      rw [abs_le]; constructor
      · have := neg_abs_le (log2Lo A:ℝ); have := le_max_left |(log2Lo A:ℝ)| |(log2Hi A:ℝ)|
        linarith
      · have := le_abs_self (log2Hi A:ℝ); have := le_max_right |(log2Lo A:ℝ)| |(log2Hi A:ℝ)|
        linarith
    norm_num
    nlinarith

lemma trig_H {lo hi : ℚ} (hA : A.H x X) (ok : mag A+A.b ≤ 262144) (s : ℝ) (hs1 : (lo:ℝ) ≤ s)
    (hs2 : s ≤ hi) : (trigAv lo hi A).H s (X+128*u*(1+(|x|+X))) ∧ |x|+X ≤ 2^18 := by
  have ma := abs_le_mag hA
  obtain ⟨a1,a2,a3,a4⟩ := hA
  have ok' : (mag A:ℝ)+A.b ≤ 262144 := by exact_mod_cast ok
  have hu := u_pos
  refine ⟨⟨by simpa [trigAv] using hs1,by simpa [trigAv] using hs2,by positivity,?_⟩,
    by norm_num; linarith⟩
  simp only [trigAv]; push_cast; rw [qu_eq]
  have := mul_le_mul_of_nonneg_left (show 1+(|x|+X) ≤ 1+((mag A:ℝ)+A.b) by linarith)
    (by positivity : (0:ℝ) ≤ 128*u)
  linarith

lemma sinLo_le (hA : A.H x X) : ((sinLo A : ℚ) : ℝ) ≤ Real.sin x := by
  obtain ⟨a1,a2,-,-⟩ := hA
  unfold sinLo
  split_ifs with h
  · have l1 : (-1:ℝ) ≤ A.lo := by exact_mod_cast h.1
    have l2 : (A.hi:ℝ) ≤ 1 := by exact_mod_cast h.2
    have hpi := Real.pi_gt_three
    have hb := abs_le.mp (Real.sin_bound (x := (A.lo:ℝ)) (abs_le.mpr ⟨l1, by linarith⟩))
    have hm := Real.sin_le_sin_of_le_of_le_pi_div_two (x := (A.lo:ℝ)) (y := x) (by linarith)
      (by linarith) a1
    push_cast; linarith
  · simpa using Real.neg_one_le_sin x

lemma le_sinHi (hA : A.H x X) : Real.sin x ≤ ((sinHi A : ℚ) : ℝ) := by
  obtain ⟨a1,a2,-,-⟩ := hA
  unfold sinHi
  split_ifs with h
  · have l1 : (-1:ℝ) ≤ A.lo := by exact_mod_cast h.1
    have l2 : (A.hi:ℝ) ≤ 1 := by exact_mod_cast h.2
    have hpi := Real.pi_gt_three
    have hb := abs_le.mp (Real.sin_bound (x := (A.hi:ℝ)) (abs_le.mpr ⟨by linarith, l2⟩))
    have hm := Real.sin_le_sin_of_le_of_le_pi_div_two (x := x) (y := (A.hi:ℝ)) (by linarith)
      (by linarith) a2
    push_cast; linarith
  · simpa using Real.sin_le_one x

lemma cosLo_le (hA : A.H x X) : ((cosLo A : ℚ) : ℝ) ≤ Real.cos x := by
  have ma := abs_le_mag hA
  unfold cosLo; push_cast
  refine max_le (Real.neg_one_le_cos x) ?_
  have h1 := Real.one_sub_sq_div_two_le_cos (x := x)
  have h2 : x^2 ≤ (mag A:ℝ)^2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ma 2
  linarith

lemma tanh_eq_exp (x : ℝ) : Real.tanh x = 1-2/(Real.exp (2*x)+1) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have h1 : Real.exp (2*x) = Real.exp x*Real.exp x := by rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp (-x) = 1/Real.exp x := by rw [Real.exp_neg]; ring
  have hx := Real.exp_pos x
  rw [h1, h2]
  field_simp
  ring

lemma expLo_nonneg (q : ℚ) : 0 ≤ expLo q := (expBnd_sound _).1

lemma tanhLo_le {lo : ℚ} {x : ℝ} (h : (lo:ℝ) ≤ x) : ((tanhLo lo : ℚ) : ℝ) ≤ Real.tanh x := by
  unfold tanhLo
  split_ifs with hc
  · rw [tanh_eq_exp]; push_cast
    have e0 : (0:ℝ) ≤ expLo (2*lo) := by exact_mod_cast expLo_nonneg _
    have e1 : (expLo (2*lo) : ℝ) ≤ Real.exp (2*x) :=
      (expLo_le _).trans (Real.exp_le_exp.mpr (by push_cast; linarith))
    have := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2) (by linarith) (by linarith : (expLo (2*lo):ℝ)+1 ≤ Real.exp (2*x)+1)
    linarith
  · simpa using (Real.neg_one_lt_tanh x).le

lemma le_tanhHi {hi : ℚ} {x : ℝ} (h : x ≤ hi) : Real.tanh x ≤ ((tanhHi hi : ℚ) : ℝ) := by
  unfold tanhHi
  split_ifs with hc
  · rw [tanh_eq_exp]; push_cast
    have e1 : Real.exp (2*x) ≤ (expHi (2*hi) : ℝ) :=
      (Real.exp_le_exp.mpr (by push_cast; linarith)).trans (le_expHi _)
    have := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2) (by have := Real.exp_pos (2*x); linarith) (by linarith : Real.exp (2*x)+1 ≤ (expHi (2*hi):ℝ)+1)
    linarith
  · simpa using (Real.tanh_lt_one x).le

lemma scale_H (k : ℤ) (hA : A.H x X) : (scaleAv k A).H ((2:ℝ)^k*x) ((2:ℝ)^k*X+η) := by
  obtain ⟨a1,a2,a3,a4⟩ := hA
  have hk : (0:ℝ) < (2:ℝ)^k := by positivity
  have hη := η_pos
  simp only [Av.H, scaleAv]; push_cast; rw [pow2_eq, qη_eq]
  exact ⟨mul_le_mul_of_nonneg_left a1 hk.le, mul_le_mul_of_nonneg_left a2 hk.le, by positivity,
    by linarith [mul_le_mul_of_nonneg_left a4 hk.le]⟩

end Ops

/-! ### Soundness of the evaluator -/

lemma bisect_sound (g : Av → Option Av) (x X y Y : ℝ) (S : Prop)
    (hg : ∀ A R, A.H x X → g A = some R → R.H y Y ∧ S) :
    ∀ (n : ℕ) (A R : Av), A.H x X → bisect g n A = some R → R.H y Y ∧ S
  | 0, A, R, hA, h => hg A R hA h
  | n+1, A, R, hA, h => by
    simp only [bisect, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨L, hL, R', hR, rfl⟩ := h
    obtain ⟨a1,a2,a3,a4⟩ := hA
    rcases le_total x ((rdn 160 ((A.lo+A.hi)/2) : ℚ) : ℝ) with hm | hm
    · obtain ⟨h1,h2⟩ := bisect_sound g x X y Y S hg n (Av.mk3 A.lo (rdn 160 ((A.lo+A.hi)/2)) A.b) L ⟨a1,hm,a3,a4⟩ hL
      exact ⟨h1.join_l R',h2⟩
    · obtain ⟨h1,h2⟩ := bisect_sound g x X y Y S hg n (Av.mk3 (rdn 160 ((A.lo+A.hi)/2)) A.hi A.b) R' ⟨hm,a2,a3,a4⟩ hR
      exact ⟨h1.join_r L,h2⟩

/-- Every input box contains its input and bounds its error. -/
def EnvH (env : ℕ → Option Av) (v E : ℕ → ℝ) : Prop := ∀ i A, env i = some A → A.H (v i) (E i)

/-- If the evaluator succeeds, `Safe` holds for every input in the boxes, and
the exact value and running bound lie within the result. -/
theorem ev_sound (d : ℕ) (e : GExpr) : ∀ (env : ℕ → Option Av) (v E : ℕ → ℝ) (R : Av),
    EnvH env v E → ev d env e = some R → R.H (e.exact v) (e.bound v E) ∧ e.Safe v E := by
  induction e with
  | input i =>
    intro env v E R henv h
    simp only [ev] at h
    split_ifs at h
    · obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨henv i A hA,trivial⟩
    · exact ⟨henv i R h,trivial⟩
  | const c =>
    intro env v E R henv h
    simp only [ev, Option.some.injEq] at h; subst h
    exact ⟨⟨le_rfl,le_rfl,le_rfl,by simp [bound]⟩,trivial⟩
  | add a b iha ihb =>
    intro env v E R henv h
    simp only [ev, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨A, ha, B, hb, rfl⟩ := h
    obtain ⟨hA, sa⟩ := iha env v E A henv ha
    obtain ⟨hB, sb⟩ := ihb env v E B henv hb
    exact ⟨(add_H hA hB).nrm.chain _ _ _,sa,sb⟩
  | sub a b iha ihb =>
    intro env v E R henv h
    simp only [ev, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨A, ha, B, hb, rfl⟩ := h
    obtain ⟨hA, sa⟩ := iha env v E A henv ha
    obtain ⟨hB, sb⟩ := ihb env v E B henv hb
    exact ⟨(sub_H hA hB).nrm.chain _ _ _,sa,sb⟩
  | mul a b iha ihb =>
    intro env v E R henv h
    simp only [ev, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨A, ha, B, hb, cb, -, rfl⟩ := h
    have hb' : ev d env b = some B := by
      split_ifs at hb with hab
      · subst hab; rw [ha]; exact hb
      · exact hb
    obtain ⟨hA, sa⟩ := iha env v E A henv ha
    obtain ⟨hB, sb⟩ := ihb env v E B henv hb'
    refine ⟨?_,sa,sb⟩
    apply Av.H.prod
    split_ifs with hab
    · subst hab
      obtain rfl : B = A := by rw [ha] at hb'; exact (Option.some.inj hb').symm
      exact (sq_H hA).nrm
    · exact (mul_H hA hB).nrm
  | neg a iha =>
    intro env v E R henv h
    simp only [ev, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨A, ha, rfl⟩ := h
    obtain ⟨hA, sa⟩ := iha env v E A henv ha
    exact ⟨(neg_H hA).chain _ _ _,sa⟩
  | div a b iha ihb =>
    intro env v E R henv h
    simp only [ev, Option.bind_eq_some_iff] at h
    obtain ⟨A, ha, B, hb, h⟩ := h
    split_ifs at h with ok
    obtain ⟨cb, -, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hA, sa⟩ := iha env v E A henv ha
    obtain ⟨hB, sb⟩ := ihb env v E B henv hb
    obtain ⟨hR, s1, s2, s3⟩ := div_H hA hB ok
    exact ⟨hR.nrm.prod _ _ _ _,sa,sb,s1,s2,s3⟩
  | sqrt a iha =>
    intro env v E R henv h
    simp only [ev, Option.bind_eq_some_iff] at h
    obtain ⟨A, ha, h⟩ := h
    split_ifs at h with ok
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hA, sa⟩ := iha env v E A henv ha
    obtain ⟨hR, s1, s2⟩ := sqrt_H hA ok
    exact ⟨hR.nrm,sa,s1,s2⟩
  | max a b iha ihb =>
    intro env v E R henv h
    simp only [ev, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨A, ha, B, hb, rfl⟩ := h
    obtain ⟨hA, sa⟩ := iha env v E A henv ha
    obtain ⟨hB, sb⟩ := ihb env v E B henv hb
    exact ⟨max_H hA hB,sa,sb⟩
  | min a b iha ihb =>
    intro env v E R henv h
    simp only [ev, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨A, ha, B, hb, rfl⟩ := h
    obtain ⟨hA, sa⟩ := iha env v E A henv ha
    obtain ⟨hB, sb⟩ := ihb env v E B henv hb
    exact ⟨min_H hA hB,sa,sb⟩
  | lt c t a b ihc iha ihb =>
    intro env v E R henv h
    simp only [ev, Option.bind_eq_some_iff] at h
    obtain ⟨C, hc, h⟩ := h
    obtain ⟨hC, sc⟩ := ihc env v E C henv hc
    obtain ⟨c1,c2,c3,c4⟩ := hC
    split_ifs at h with p q
    · obtain ⟨R', h', rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hA, sa⟩ := iha env v E R' henv h'
      have p' : (C.hi:ℝ)+C.b < t := by exact_mod_cast p
      have hlt : exact v c < (t:ℝ) := by linarith
      simp only [exact, bound, Safe, hlt, ↓reduceIte]
      exact ⟨hA,sc,sa,by rw [abs_of_neg (by linarith)]; linarith⟩
    · obtain ⟨R', h', rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hB, sb⟩ := ihb env v E R' henv h'
      have q' : (t:ℝ) < C.lo-C.b := by exact_mod_cast q
      have hlt : ¬ exact v c < (t:ℝ) := by linarith
      simp only [exact, bound, Safe, hlt, ↓reduceIte]
      exact ⟨hB,sc,sb,by rw [abs_of_pos (by linarith)]; linarith⟩
  | abs a iha =>
    intro env v E R henv h
    simp only [ev, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨A, ha, rfl⟩ := h
    obtain ⟨hA, sa⟩ := iha env v E A henv ha
    exact ⟨abs_H hA,sa⟩
  | invsqrt a iha =>
    intro env v E R henv h
    simp only [ev, Option.bind_eq_some_iff] at h
    obtain ⟨A, ha, h⟩ := h
    split_ifs at h with ok
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hA, sa⟩ := iha env v E A henv ha
    obtain ⟨hR, s1⟩ := inv_H hA ok
    exact ⟨hR.nrm,sa,s1⟩
  | exp a iha =>
    intro env v E R henv h
    simp only [ev, Option.bind_eq_some_iff] at h
    obtain ⟨A, ha, h⟩ := h
    split_ifs at h with ok
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hA, sa⟩ := iha env v E A henv ha
    exact ⟨(exp_H hA).nrm,sa⟩
  | exp2 a iha =>
    intro env v E R henv h
    simp only [ev, Option.bind_eq_some_iff] at h
    obtain ⟨A, ha, h⟩ := h
    split_ifs at h with ok
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hA, sa⟩ := iha env v E A henv ha
    exact ⟨(exp2_H hA).nrm,sa⟩
  | log a iha =>
    intro env v E R henv h
    simp only [ev, Option.bind_eq_some_iff] at h
    obtain ⟨A, ha, h⟩ := h
    split_ifs at h with ok
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hA, sa⟩ := iha env v E A henv ha
    obtain ⟨hR, s1⟩ := log_H hA ok
    exact ⟨hR.nrm,sa,s1⟩
  | log2 a iha =>
    intro env v E R henv h
    simp only [ev, Option.bind_eq_some_iff] at h
    obtain ⟨A, ha, h⟩ := h
    split_ifs at h with ok
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hA, sa⟩ := iha env v E A henv ha
    obtain ⟨hR, s1⟩ := log2_H hA ok
    exact ⟨hR.nrm,sa,s1⟩
  | inh f a ihf iha =>
    intro env v E R henv h
    simp only [ev, Option.bind_eq_some_iff] at h
    obtain ⟨A, ha, h⟩ := h
    obtain ⟨R', hb, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hA, sa⟩ := iha env v E A henv ha
    obtain ⟨hR, sf⟩ := bisect_sound _ _ _ _ _ _ (fun A' R' hA' h' =>
      ihf (fun _ => some A'.leaf) (fun _ => exact v a) (fun _ => bound v E a) R'
        (fun _ A'' h'' => by simp only [Option.some.injEq] at h''; subst h''; exact hA') h') d A R' hA hb
    exact ⟨hR,sa,sf⟩
  | tanh f a ihf iha =>
    intro env v E R henv h
    simp only [ev] at h
    split_ifs at h with hf
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨A, ha, R', hR', rfl⟩ := h
    obtain ⟨hA, sa⟩ := iha env v E A henv ha
    obtain ⟨hR, sf⟩ := bisect_sound _ _ _ _ _ _ (fun A' R'' hA' h' =>
      ihf (fun _ => some A'.leaf) (fun _ => exact v a) (fun _ => bound v E a) R''
        (fun _ A'' h'' => by simp only [Option.some.injEq] at h''; subst h''; exact hA') h') d A R' hA hR'
    refine ⟨Av.H.nrm ⟨?_,?_,?_,?_⟩,sa,sf,by rw [hf]; exact WgslPlasma.tanhInh_exact⟩
    · exact tanhLo_le hA.1
    · exact le_tanhHi hA.2.1
    · exact le_max_of_le_left (by have := hA.2.2.1; positivity)
    · simp only [bound]; push_cast
      exact max_le_max (by have := hA.2.2.2; norm_num; linarith) hR.2.2.2
  | lt2 a b x y iha ihb ihx ihy =>
    intro env v E R henv h
    simp only [ev, Option.bind_eq_some_iff] at h
    obtain ⟨A, ha, B, hb, h⟩ := h
    obtain ⟨hA, sa⟩ := iha env v E A henv ha
    obtain ⟨hB, sb⟩ := ihb env v E B henv hb
    obtain ⟨a1,a2,a3,a4⟩ := hA
    obtain ⟨b1,b2,b3,b4⟩ := hB
    split_ifs at h with p q
    · obtain ⟨R', h', rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hX, sx⟩ := ihx env v E R' henv h'
      have p' : (A.hi:ℝ)-B.lo+(A.b+B.b) < 0 := by exact_mod_cast p
      have hlt : exact v a < exact v b := by linarith
      simp only [exact, bound, Safe, hlt, ↓reduceIte]
      exact ⟨hX,sa,sb,sx,by rw [abs_of_neg (by linarith)]; linarith⟩
    · obtain ⟨R', h', rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hY, sy⟩ := ihy env v E R' henv h'
      have q' : (B.hi:ℝ)-A.lo+(A.b+B.b) < 0 := by exact_mod_cast q
      have hlt : ¬ exact v a < exact v b := by linarith
      simp only [exact, bound, Safe, hlt, ↓reduceIte]
      exact ⟨hY,sa,sb,sy,by rw [abs_of_pos (by linarith)]; linarith⟩
  | sinS a iha =>
    intro env v E R henv h
    simp only [ev, Option.bind_eq_some_iff] at h
    obtain ⟨A, ha, h⟩ := h
    split_ifs at h with ok
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hA, sa⟩ := iha env v E A henv ha
    obtain ⟨hR, s1⟩ := trig_H hA ok _ (sinLo_le hA) (le_sinHi hA)
    exact ⟨hR.nrm,sa,s1⟩
  | cosS a iha =>
    intro env v E R henv h
    simp only [ev, Option.bind_eq_some_iff] at h
    obtain ⟨A, ha, h⟩ := h
    split_ifs at h with ok
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hA, sa⟩ := iha env v E A henv ha
    obtain ⟨hR, s1⟩ := trig_H (hi := 1) hA ok _ (cosLo_le hA) (by simpa using Real.cos_le_one (exact v a))
    exact ⟨hR.nrm,sa,s1⟩
  | scale k a iha =>
    intro env v E R henv h
    simp only [ev, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨A, ha, rfl⟩ := h
    obtain ⟨hA, sa⟩ := iha env v E A henv ha
    exact ⟨(scale_H k hA).nrm,sa⟩
  | round a _ => intro env v E R henv h; simp [ev] at h
  | qsel j k s c _ _ _ => intro env v E R henv h; simp [ev] at h

/-! ### `let` slots

A slot program (`WgslLets`) is evaluated slot by slot, each slot once, with
later slots reading the earlier results. This is sound for the expanded tree
`withLets`, whose exact value, running bound and `Safe` conditions at a
substituted input depend only on the exact value, bound and `Safe` of what
is substituted. -/

section Lets
open WgslLets

lemma exact_subst (σ : ℕ → GExpr) (v : ℕ → ℝ) :
    ∀ e : GExpr, (subst σ e).exact v = e.exact (fun i => (σ i).exact v) := by
  intro e
  induction e <;> simp_all [subst, exact]

lemma bound_subst (σ : ℕ → GExpr) (v E : ℕ → ℝ) :
    ∀ e : GExpr, (subst σ e).bound v E =
      e.bound (fun i => (σ i).exact v) (fun i => (σ i).bound v E) := by
  intro e
  induction e <;> simp_all [subst, bound, exact_subst]

lemma safe_subst (σ : ℕ → GExpr) (v E : ℕ → ℝ) (hσ : ∀ i, (σ i).Safe v E) :
    ∀ e : GExpr, e.Safe (fun i => (σ i).exact v) (fun i => (σ i).bound v E) →
      (subst σ e).Safe v E := by
  intro e
  induction e <;> simp_all [subst, Safe, exact_subst, bound_subst]
  all_goals intros; split_ifs at * <;> simp_all

/-- Kernel input boxes, then the results of the slots evaluated so far. -/
def slotEnv (env : ℕ → Option Av) (vals : List Av) (i : ℕ) : Option Av :=
  if letBase ≤ i then vals[i-letBase]? else env i

def evSlots (d : ℕ) (env : ℕ → Option Av) : List GExpr → List Av → Option (List Av)
  | [], done => some done
  | e :: es, done => (ev d (slotEnv env done) e).bind fun A => evSlots d env es (done ++ [A])

/-- An output of a slot program, evaluated over its slots. -/
def evLets (d : ℕ) (env : ℕ → Option Av) (slots : List GExpr) (e : GExpr) : Option Av :=
  (evSlots d env slots []).bind fun vals => ev d (slotEnv env vals) e

/-- The evaluated slots enclose the expanded slots, which are `Safe`. -/
def SlotsH (v E : ℕ → ℝ) (vals : List Av) (X : List GExpr) : Prop :=
  vals.length = X.length ∧ ∀ j (hv : j < vals.length) (hX : j < X.length),
    vals[j].H (X[j].exact v) (X[j].bound v E) ∧ X[j].Safe v E

lemma lookup_safe {v E : ℕ → ℝ} {vals : List Av} {X : List GExpr} (h : SlotsH v E vals X) (i : ℕ) :
    (lookup X i).Safe v E := by
  unfold lookup
  split_ifs with hi
  · rw [List.getD_eq_getElem?_getD]
    cases hx : X[i-letBase]? with
    | none => exact trivial
    | some x =>
      obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hx
      exact (h.2 _ (h.1 ▸ hlt) hlt).2
  · exact trivial

lemma slotEnv_H {env : ℕ → Option Av} {v E : ℕ → ℝ} (henv : EnvH env v E) {vals : List Av}
    {X : List GExpr} (h : SlotsH v E vals X) :
    EnvH (slotEnv env vals) (fun i => (lookup X i).exact v) (fun i => (lookup X i).bound v E) := by
  intro i A hA
  unfold slotEnv at hA
  unfold lookup
  dsimp only
  split_ifs at hA ⊢ with hi
  · obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hA
    have hX : i-letBase < X.length := h.1 ▸ hlt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hX, Option.getD_some]
    exact (h.2 _ hlt hX).1
  · exact henv i A hA

lemma evSlots_sound (d : ℕ) {env : ℕ → Option Av} {v E : ℕ → ℝ} (henv : EnvH env v E) :
    ∀ (es : List GExpr) (done : List Av) (X : List GExpr) (vals : List Av), SlotsH v E done X →
      evSlots d env es done = some vals → SlotsH v E vals (expand X es)
  | [], done, X, vals, h, hs => by
    simp only [evSlots, Option.some.injEq] at hs; subst hs; exact h
  | e :: es, done, X, vals, h, hs => by
    simp only [evSlots, Option.bind_eq_some_iff] at hs
    obtain ⟨A, hA, hs⟩ := hs
    apply evSlots_sound d henv es _ _ vals _ hs
    obtain ⟨hR, hS⟩ := ev_sound d e _ _ _ A (slotEnv_H henv h) hA
    refine ⟨by simp [h.1], fun j hv hX => ?_⟩
    rcases Nat.lt_or_ge j done.length with hj | hj
    · have hjX : j < X.length := h.1 ▸ hj
      rw [List.getElem_append_left hj, List.getElem_append_left hjX]
      exact h.2 j hj hjX
    · have e1 : j = done.length := by simp at hv; omega
      subst e1
      rw [List.getElem_append_right le_rfl, List.getElem_append_right (h.1 ▸ le_rfl)]
      simp only [Nat.sub_self, List.getElem_cons_zero, h.1]
      rw [exact_subst, bound_subst]
      exact ⟨hR, safe_subst _ _ _ (lookup_safe h) e hS⟩

/-- If the slot evaluation succeeds, the expanded output `withLets slots e`
is `Safe` on the boxes, with its exact value and bound enclosed. -/
theorem evLets_sound (d : ℕ) (env : ℕ → Option Av) (slots : List GExpr) (e : GExpr)
    (v E : ℕ → ℝ) (R : Av) (henv : EnvH env v E) (h : evLets d env slots e = some R) :
    R.H ((withLets slots e).exact v) ((withLets slots e).bound v E) ∧ (withLets slots e).Safe v E := by
  simp only [evLets, Option.bind_eq_some_iff] at h
  obtain ⟨vals, hv, hR⟩ := h
  have hS := evSlots_sound d henv slots [] [] vals ⟨rfl, fun j hv _ => absurd hv (by simp)⟩ hv
  obtain ⟨hR', hS'⟩ := ev_sound d e _ _ _ R (slotEnv_H henv hS) hR
  unfold withLets
  rw [exact_subst, bound_subst]
  exact ⟨hR', safe_subst _ _ _ (lookup_safe hS) e hS'⟩

end Lets

/-- Every output of a slot program over one slot evaluation. -/
def evLetsAll (d : ℕ) (env : ℕ → Option Av) (slots outs : List GExpr) : Bool :=
  match evSlots d env slots [] with
  | some vals => outs.all fun e => (ev d (slotEnv env vals) e).isSome
  | none => false

theorem evLetsAll_sound (d : ℕ) (env : ℕ → Option Av) (slots outs : List GExpr)
    (h : evLetsAll d env slots outs = true) (v E : ℕ → ℝ) (henv : EnvH env v E) :
    ∀ e ∈ outs, (WgslLets.withLets slots e).Safe v E := by
  intro e he
  unfold evLetsAll at h
  cases hs : evSlots d env slots [] with
  | none => rw [hs] at h; exact absurd h (by simp)
  | some vals =>
    rw [hs, List.all_eq_true] at h
    obtain ⟨R, hR⟩ := Option.isSome_iff_exists.mp (h e he)
    exact (evLets_sound d env slots e v E R henv (by simp [evLets, hs, hR])).2

/-! ### Boxes around a reference input -/

/-- Input `i` within `w (1 + |ref i|)` of `ref i`, with error at most that. -/
def nearEnv (ref : List ℚ) (w : ℚ) (i : ℕ) : Option Av :=
  ref[i]?.map fun r => Av.mk3 (r-w*(1+|r|)) (r+w*(1+|r|)) (w*(1+|r|))

/-- Inputs and errors within the box `nearEnv ref w`. -/
def Near (ref : List ℚ) (w : ℚ) (v E : ℕ → ℝ) : Prop :=
  ∀ i (hi : i < ref.length), |v i-ref[i]| ≤ w*(1+|(ref[i] : ℝ)|) ∧ 0 ≤ E i ∧
    E i ≤ w*(1+|(ref[i] : ℝ)|)

lemma nearEnv_H {ref : List ℚ} {w : ℚ} {v E : ℕ → ℝ} (h : Near ref w v E) :
    EnvH (nearEnv ref w) v E := by
  intro i A hA
  unfold nearEnv at hA
  cases hr : ref[i]? with
  | none => rw [hr] at hA; exact absurd hA (by simp)
  | some r =>
    rw [hr] at hA
    simp only [Option.map_some, Option.some.injEq] at hA; subst hA
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hr
    obtain ⟨h1, h2, h3⟩ := h i hi
    have := abs_le.mp h1
    exact ⟨by push_cast; linarith, by push_cast; linarith, h2, by push_cast; linarith⟩

/-! ### Product-chain invariants -/

section ProdInv
open WgslReassoc

/-- A factor of a product chain with `λ ≤ |t| ≤ μ`, every reassociation of
which is `Safe` with bound in `[0, β]`; the data is `(λ, μ, β)`. -/
def FacP (v E : ℕ → ℝ) (p : Bool × GExpr) (q : ℝ × ℝ × ℝ) : Prop :=
  0 ≤ q.1 ∧ q.1 ≤ |p.2.exact v| ∧ |p.2.exact v| ≤ q.2.1 ∧ 0 ≤ q.2.2 ∧
    ∀ x', RA p.2 x' → x'.Safe v E ∧ 0 ≤ x'.bound v E ∧ x'.bound v E ≤ q.2.2

/-- Products over the numerators, and over the divisors, of a chain. -/
def zN (L : List (Bool × GExpr)) (Q : List (ℝ × ℝ × ℝ)) (f : ℝ × ℝ × ℝ → ℝ) : ℝ :=
  ((L.zip Q).map fun z => if z.1.1 then 1 else f z.2).prod
def zD (L : List (Bool × GExpr)) (Q : List (ℝ × ℝ × ℝ)) (f : ℝ × ℝ × ℝ → ℝ) : ℝ :=
  ((L.zip Q).map fun z => if z.1.1 then f z.2 else 1).prod

lemma zN_append {L₁ L₂ : List (Bool × GExpr)} {Q₁ Q₂ : List (ℝ × ℝ × ℝ)} (h : L₁.length = Q₁.length)
    (f : ℝ × ℝ × ℝ → ℝ) : zN (L₁ ++ L₂) (Q₁ ++ Q₂) f = zN L₁ Q₁ f*zN L₂ Q₂ f := by
  simp [zN, List.zip_append h]

lemma zD_append {L₁ L₂ : List (Bool × GExpr)} {Q₁ Q₂ : List (ℝ × ℝ × ℝ)} (h : L₁.length = Q₁.length)
    (f : ℝ × ℝ × ℝ → ℝ) : zD (L₁ ++ L₂) (Q₁ ++ Q₂) f = zD L₁ Q₁ f*zD L₂ Q₂ f := by
  simp [zD, List.zip_append h]

lemma zN_divs (L : List GExpr) (Q : List (ℝ × ℝ × ℝ)) (f : ℝ × ℝ × ℝ → ℝ) :
    zN (L.map fun x => (true, x)) Q f = 1 := by
  unfold zN; rw [List.prod_eq_one]; intro y hy
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
  obtain ⟨x, -, hx⟩ := List.mem_map.mp (List.of_mem_zip hz).1
  simp [← hx]

lemma zD_divs {L : List GExpr} {Q : List (ℝ × ℝ × ℝ)} (h : L.length = Q.length) (f : ℝ × ℝ × ℝ → ℝ) :
    zD (L.map fun x => (true, x)) Q f = (Q.map f).prod := by
  induction L generalizing Q with
  | nil => cases Q <;> simp_all [zD]
  | cons x L ih =>
    cases Q with
    | nil => simp at h
    | cons q Q =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      have := ih h
      simp only [zD, List.map_cons, List.zip_cons_cons, List.prod_cons, ↓reduceIte] at this ⊢
      rw [this]

/-- Data on a list of divisors bounds the true divisor quantities. -/
def DDH (d : DD) (Q : List (ℝ × ℝ × ℝ)) : Prop :=
  Q.length = d.m ∧ 0 ≤ (d.T:ℝ) ∧ (d.T:ℝ) ≤ (Q.map (·.1)).prod ∧
    (Q.map fun q => 1+q.2.2/q.1).prod ≤ (d.P:ℝ) ∧ 0 ≤ (d.mn:ℝ) ∧
    (d.mn:ℝ) ≤ (Q.map fun q => Min.min 1 q.1).prod ∧ (Q.map fun q => Max.max 1 q.2.1).prod ≤ (d.mx:ℝ) ∧
    (Q.map fun q => Max.max 1 (1/q.1)).prod ≤ (d.im:ℝ)

/-- `d` bounds the factors of the product `x` as divisors. -/
def MH (v E : ℕ → ℝ) (d : DD) (x : GExpr) : Prop :=
  ∃ Q : List (ℝ × ℝ × ℝ), List.Forall₂ (fun ℓ q => FacP v E (true, ℓ) q) (mulLeaves x) Q ∧ DDH d Q

/-- `p` bounds the factors of the product chain `x`. -/
def PH (v E : ℕ → ℝ) (p : PD) (x : GExpr) : Prop :=
  (prodLeaves x).length = p.n ∧ ∃ Q : List (ℝ × ℝ × ℝ), List.Forall₂ (FacP v E) (prodLeaves x) Q ∧
    zN (prodLeaves x) Q (fun q => q.2.1+q.2.2) ≤ (p.ψ:ℝ) ∧
    zN (prodLeaves x) Q (fun q => Max.max 1 (q.2.1+q.2.2)) ≤ (p.M:ℝ) ∧
    0 ≤ (p.T:ℝ) ∧ (p.T:ℝ) ≤ zN (prodLeaves x) Q (·.2.1) ∧ nd (prodLeaves x) = p.d.m ∧
    0 ≤ (p.d.T:ℝ) ∧ (p.d.T:ℝ) ≤ zD (prodLeaves x) Q (·.1) ∧
    zD (prodLeaves x) Q (fun q => 1+q.2.2/q.1) ≤ (p.d.P:ℝ) ∧
    0 ≤ (p.d.mn:ℝ) ∧ (p.d.mn:ℝ) ≤ zD (prodLeaves x) Q (fun q => Min.min 1 q.1) ∧
    zD (prodLeaves x) Q (fun q => Max.max 1 q.2.1) ≤ (p.d.mx:ℝ) ∧
    zD (prodLeaves x) Q (fun q => Max.max 1 (1/q.1)) ≤ (p.d.im:ℝ)

end ProdInv


section ProdComb
open WgslReassoc

lemma mig_nonneg (A : Av) : 0 ≤ mig A := by
  unfold mig; split_ifs with p q
  · exact p.le
  · linarith
  · exact le_rfl

lemma zN_nonneg {L : List (Bool × GExpr)} {Q : List (ℝ × ℝ × ℝ)} {f : ℝ × ℝ × ℝ → ℝ}
    (h : ∀ q ∈ Q, 0 ≤ f q) : 0 ≤ zN L Q f :=
  List.prod_nonneg fun y hy => by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    split_ifs
    · exact zero_le_one
    · exact h _ (List.of_mem_zip hz).2

lemma zD_nonneg {L : List (Bool × GExpr)} {Q : List (ℝ × ℝ × ℝ)} {f : ℝ × ℝ × ℝ → ℝ}
    (h : ∀ q ∈ Q, 0 ≤ f q) : 0 ≤ zD L Q f :=
  List.prod_nonneg fun y hy => by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    split_ifs
    · exact h _ (List.of_mem_zip hz).2
    · exact zero_le_one

lemma prod_map_nonneg {Q : List (ℝ × ℝ × ℝ)} {f : ℝ × ℝ × ℝ → ℝ} (h : ∀ q ∈ Q, 0 ≤ f q) :
    0 ≤ (Q.map f).prod :=
  List.prod_nonneg fun y hy => by obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy; exact h q hq

/-- The nonnegative quantities of the factors. -/
lemma FacP.nn {v E : ℕ → ℝ} {p : Bool × GExpr} {q : ℝ × ℝ × ℝ} (h : FacP v E p q) :
    0 ≤ q.1 ∧ 0 ≤ q.2.1 ∧ 0 ≤ q.2.2 :=
  ⟨h.1, (abs_nonneg _).trans h.2.2.1, h.2.2.2.1⟩

lemma forall₂_mem {α β : Type*} {R : α → β → Prop} {L : List α} {Q : List β}
    (h : List.Forall₂ R L Q) : ∀ q ∈ Q, ∃ p ∈ L, R p q := by
  induction h with
  | nil => simp
  | cons hr _ ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨_, List.mem_cons_self .., hr⟩
    · obtain ⟨p, hp, hpq⟩ := ih q hq; exact ⟨p, List.mem_cons_of_mem _ hp, hpq⟩

lemma up_mul {a b A B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : a ≤ A) (hB : b ≤ B) : a*b ≤ A*B :=
  mul_le_mul hA hB hb (ha.trans hA)

lemma rup_mul (x y : ℚ) : (x:ℝ)*y ≤ ((rup 160 (x*y) : ℚ) : ℝ) := by
  have := le_rup_real 160 (x*y); push_cast at this; exact this

lemma rdn_mul (x y : ℚ) : ((rdn 160 (x*y) : ℚ) : ℝ) ≤ (x:ℝ)*y := by
  have := rdn_le_real 160 (x*y); push_cast at this; exact this

lemma rdn_mul_nonneg {x y : ℚ} (hx : 0 ≤ (x:ℝ)) (hy : 0 ≤ (y:ℝ)) : 0 ≤ ((rdn 160 (x*y) : ℚ) : ℝ) := by
  have : (0:ℚ) ≤ x*y := by exact_mod_cast mul_nonneg hx hy
  exact_mod_cast rdn_nonneg 160 this

/-- A value that is not a product chain is its chain's only numerator. -/
lemma PH_leaf {v E : ℕ → ℝ} {A : Av} {x : GExpr} (hx : ¬ IsProd x)
    (h : ∀ x', RA x x' → x'.Safe v E ∧ A.H (x'.exact v) (x'.bound v E)) : PH v E (PD.leaf A) x := by
  obtain ⟨-, hH⟩ := h x (RA.refl x)
  have hm := abs_le_mag hH
  have hb : (0:ℝ) ≤ A.b := hH.b_nonneg
  have fac : FacP v E (false, x) (0, mag A, A.b) :=
    ⟨le_rfl, abs_nonneg _, hm, hb, fun x' hx' => by
      obtain ⟨s', h'⟩ := h x' hx'; exact ⟨s', h'.2.2.1, h'.2.2.2⟩⟩
  refine ⟨by simp [prodLeaves_of_not hx, PD.leaf], [(0, mag A, A.b)],
    by rw [prodLeaves_of_not hx]; exact List.Forall₂.cons fac List.Forall₂.nil, ?_⟩
  simp only [prodLeaves_of_not hx, zN, zD, PD.leaf, DD.one, List.zip_cons_cons, List.zip_nil_left,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Bool.false_eq_true, ↓reduceIte,
    mul_one, nd, List.countP_cons, List.countP_nil]
  push_cast
  refine ⟨le_rfl, le_rfl, by linarith [abs_nonneg (exact v x)], le_rfl, trivial, by norm_num, le_rfl,
    le_rfl, by norm_num, le_rfl, le_rfl, le_rfl⟩

/-- A value that is not a product is its own only factor as a divisor. -/
lemma MH_leaf {v E : ℕ → ℝ} {A : Av} {x : GExpr} (hx : ¬ IsMul x)
    (h : ∀ x', RA x x' → x'.Safe v E ∧ A.H (x'.exact v) (x'.bound v E)) : MH v E (DD.leaf A) x := by
  obtain ⟨-, hH⟩ := h x (RA.refl x)
  have hm := abs_le_mag hH
  have hl := mig_le_abs hH
  have hb : (0:ℝ) ≤ A.b := hH.b_nonneg
  have h0 : (0:ℝ) ≤ mig A := by exact_mod_cast mig_nonneg A
  have fac : FacP v E (true, x) (mig A, mag A, A.b) :=
    ⟨h0, hl, hm, hb, fun x' hx' => by
      obtain ⟨s', h'⟩ := h x' hx'; exact ⟨s', h'.2.2.1, h'.2.2.2⟩⟩
  refine ⟨[(mig A, mag A, A.b)], by rw [mulLeaves_of_not hx]; exact List.Forall₂.cons fac List.Forall₂.nil, ?_⟩
  simp only [DDH, DD.leaf, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    List.length_singleton]
  refine ⟨trivial, h0, le_rfl, ?_, by push_cast; exact le_min zero_le_one h0, ?_, ?_, ?_⟩
  · have := le_rup_real 160 (1+A.b/mig A); push_cast at this; exact this
  · push_cast; exact le_rfl
  · push_cast; exact le_rfl
  · have := le_rup_real 160 (Max.max 1 (1/mig A)); push_cast at this; exact this

end ProdComb


section ProdComb2
open WgslReassoc

/-- The nonnegativity of the factor quantities in a chain. -/
lemma Q_nn {v E : ℕ → ℝ} {L : List (Bool × GExpr)} {Q : List (ℝ × ℝ × ℝ)}
    (h : List.Forall₂ (FacP v E) L Q) : ∀ q ∈ Q, 0 ≤ q.1 ∧ 0 ≤ q.2.1 ∧ 0 ≤ q.2.2 := fun q hq => by
  obtain ⟨p, -, hpq⟩ := forall₂_mem h q hq; exact hpq.nn

lemma Qd_nn {v E : ℕ → ℝ} {L : List GExpr} {Q : List (ℝ × ℝ × ℝ)}
    (h : List.Forall₂ (fun ℓ q => FacP v E (true, ℓ) q) L Q) : ∀ q ∈ Q, 0 ≤ q.1 ∧ 0 ≤ q.2.1 ∧ 0 ≤ q.2.2 :=
  fun q hq => by obtain ⟨p, -, hpq⟩ := forall₂_mem h q hq; exact hpq.nn

lemma DDH_mul {d e : DD} {Q R : List (ℝ × ℝ × ℝ)} (hQ : ∀ q ∈ Q, 0 ≤ q.1 ∧ 0 ≤ q.2.1 ∧ 0 ≤ q.2.2)
    (hR : ∀ q ∈ R, 0 ≤ q.1 ∧ 0 ≤ q.2.1 ∧ 0 ≤ q.2.2) (hd : DDH d Q) (he : DDH e R) :
    DDH (d.mul e) (Q ++ R) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := hd
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := he
  have n1 := fun q hq => (hQ q hq).1
  have m1 := fun q hq => (hR q hq).1
  simp only [DDH, DD.mul, List.map_append, List.prod_append, List.length_append]
  refine ⟨by rw [d1, e1], rdn_mul_nonneg d2 e2, (rdn_mul _ _).trans (up_mul d2 e2 d3 e3),
    le_trans (up_mul (prod_map_nonneg fun q hq => add_nonneg zero_le_one (div_nonneg (hQ q hq).2.2 (n1 q hq)))
      (prod_map_nonneg fun q hq => add_nonneg zero_le_one (div_nonneg (hR q hq).2.2 (m1 q hq))) d4 e4)
      (rup_mul _ _),
    rdn_mul_nonneg d5 e5, (rdn_mul _ _).trans (up_mul d5 e5 d6 e6),
    le_trans (up_mul (prod_map_nonneg fun q _ => le_max_of_le_left zero_le_one)
      (prod_map_nonneg fun q _ => le_max_of_le_left zero_le_one) d7 e7) (rup_mul _ _),
    le_trans (up_mul (prod_map_nonneg fun q _ => le_max_of_le_left zero_le_one)
      (prod_map_nonneg fun q _ => le_max_of_le_left zero_le_one) d8 e8) (rup_mul _ _)⟩

lemma MH_mul {v E : ℕ → ℝ} {d e : DD} {a b : GExpr} (ha : MH v E d a) (hb : MH v E e b) :
    MH v E (d.mul e) (.mul a b) := by
  obtain ⟨Q, fQ, hQ⟩ := ha
  obtain ⟨R, fR, hR⟩ := hb
  exact ⟨Q ++ R, by simp only [mulLeaves]; exact List.rel_append fQ fR, DDH_mul (Qd_nn fQ) (Qd_nn fR) hQ hR⟩

end ProdComb2


section ProdComb3
open WgslReassoc

lemma PH_mul {v E : ℕ → ℝ} {p q : PD} {a b : GExpr} (ha : PH v E p a) (hb : PH v E q b) :
    PH v E (p.mul q) (.mul a b) := by
  obtain ⟨na, Qa, fa, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := ha
  obtain ⟨nb, Qb, fb, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := hb
  have la := fa.length_eq
  have qa := Q_nn fa; have qb := Q_nn fb
  have eL : prodLeaves (.mul a b) = prodLeaves a ++ prodLeaves b := rfl
  refine ⟨by rw [eL, List.length_append, na, nb]; rfl, Qa ++ Qb, by rw [eL]; exact List.rel_append fa fb, ?_⟩
  simp only [eL, zN_append la, zD_append la, PD.mul, DD.mul, nd_append, a5, b5]
  have zNn := fun (f : ℝ × ℝ × ℝ → ℝ) (L : List (Bool × GExpr)) (Q : List (ℝ × ℝ × ℝ))
    (h : ∀ q ∈ Q, 0 ≤ f q) => zN_nonneg (L := L) h
  have zDn := fun (f : ℝ × ℝ × ℝ → ℝ) (L : List (Bool × GExpr)) (Q : List (ℝ × ℝ × ℝ))
    (h : ∀ q ∈ Q, 0 ≤ f q) => zD_nonneg (L := L) h
  refine ⟨le_trans (up_mul (zNn _ _ _ fun q hq => add_nonneg (qa q hq).2.1 (qa q hq).2.2)
      (zNn _ _ _ fun q hq => add_nonneg (qb q hq).2.1 (qb q hq).2.2) a1 b1) (rup_mul _ _),
    le_trans (up_mul (zNn _ _ _ fun q _ => le_max_of_le_left zero_le_one) (zNn _ _ _ fun q _ => le_max_of_le_left zero_le_one) a2 b2) (rup_mul _ _),
    rdn_mul_nonneg a3 b3, (rdn_mul _ _).trans (up_mul a3 b3 a4 b4), trivial,
    rdn_mul_nonneg a6 b6, (rdn_mul _ _).trans (up_mul a6 b6 a7 b7),
    le_trans (up_mul (zDn _ _ _ fun q hq => add_nonneg zero_le_one (div_nonneg (qa q hq).2.2 (qa q hq).1))
      (zDn _ _ _ fun q hq => add_nonneg zero_le_one (div_nonneg (qb q hq).2.2 (qb q hq).1)) a8 b8)
      (rup_mul _ _),
    rdn_mul_nonneg a9 b9, (rdn_mul _ _).trans (up_mul a9 b9 a10 b10),
    le_trans (up_mul (zDn _ _ _ fun q _ => le_max_of_le_left zero_le_one)
      (zDn _ _ _ fun q _ => le_max_of_le_left zero_le_one) a11 b11) (rup_mul _ _),
    le_trans (up_mul (zDn _ _ _ fun q _ => le_max_of_le_left zero_le_one)
      (zDn _ _ _ fun q _ => le_max_of_le_left zero_le_one) a12 b12) (rup_mul _ _)⟩

lemma PH_div {v E : ℕ → ℝ} {p : PD} {d : DD} {a b : GExpr} (ha : PH v E p a) (hb : MH v E d b) :
    PH v E (p.div d) (.div a b) := by
  obtain ⟨na, Qa, fa, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := ha
  obtain ⟨Qb, fb, b1, b2, b3, b4, b5, b6, b7, b8⟩ := hb
  have la := fa.length_eq
  have lb := fb.length_eq
  have qa := Q_nn fa; have qb := Qd_nn fb
  have eL : prodLeaves (.div a b) = prodLeaves a ++ (mulLeaves b).map fun x => (true, x) := rfl
  refine ⟨by rw [eL, List.length_append, List.length_map, na, lb, b1]; rfl, Qa ++ Qb,
    by rw [eL]; exact List.rel_append fa (List.forall₂_map_left_iff.mpr fb), ?_⟩
  simp only [eL, zN_append la, zD_append la, zN_divs, zD_divs lb, PD.div, DD.mul, nd_append, nd_divs,
    a5, mul_one]
  refine ⟨a1, a2, a3, a4, by rw [lb, b1], rdn_mul_nonneg a6 b2, (rdn_mul _ _).trans (up_mul a6 b2 a7 b3),
    le_trans (up_mul (zD_nonneg fun q hq => add_nonneg zero_le_one (div_nonneg (qa q hq).2.2 (qa q hq).1))
      (prod_map_nonneg fun q hq => add_nonneg zero_le_one (div_nonneg (qb q hq).2.2 (qb q hq).1)) a8 b4)
      (rup_mul _ _),
    rdn_mul_nonneg a9 b5, (rdn_mul _ _).trans (up_mul a9 b5 a10 b6),
    le_trans (up_mul (zD_nonneg fun q _ => le_max_of_le_left zero_le_one)
      (prod_map_nonneg fun q _ => le_max_of_le_left zero_le_one) a11 b7) (rup_mul _ _),
    le_trans (up_mul (zD_nonneg fun q _ => le_max_of_le_left zero_le_one)
      (prod_map_nonneg fun q _ => le_max_of_le_left zero_le_one) a12 b8) (rup_mul _ _)⟩

end ProdComb3


section ProdChain
open WgslReassoc

lemma lp_perm {L L' : List (Bool × GExpr)} (σ : Fin L.length ≃ Fin L'.length) (f : Bool × GExpr → ℝ) :
    lp L' f = ∏ i : Fin L.length, f L'[σ i] := by
  unfold lp; rw [← List.ofFn_getElem_eq_map, List.prod_ofFn]
  exact (Equiv.prod_comp σ (fun j => f L'[(j : ℕ)])).symm

lemma zip_prod {L : List (Bool × GExpr)} {Q : List (ℝ × ℝ × ℝ)} (h : L.length = Q.length)
    (g : (Bool × GExpr) × (ℝ × ℝ × ℝ) → ℝ) :
    ((L.zip Q).map g).prod = ∏ i : Fin L.length, g (L[i], Q[(i : ℕ)]'(h ▸ i.2)) := by
  have hl : (L.zip Q).length = L.length := by simp [List.length_zip, h]
  rw [← List.ofFn_getElem_eq_map, List.prod_ofFn]
  refine Fintype.prod_equiv (finCongr hl) _ _ fun i => ?_
  simp [List.getElem_zip]

/-- The factor data of a chain, at index `i`. -/
lemma Q_get {v E : ℕ → ℝ} {L : List (Bool × GExpr)} {Q : List (ℝ × ℝ × ℝ)}
    (hQ : List.Forall₂ (FacP v E) L Q) (i : Fin L.length) :
    FacP v E L[i] (Q[(i : ℕ)]'(hQ.length_eq ▸ i.2)) :=
  (List.forall₂_iff_get.mp hQ).2 i i.2 (hQ.length_eq ▸ i.2)

lemma qU'_eq : (qU' : ℝ) = U' := by simp [qU', U', WgslPoly.U, u]; norm_num

lemma nd_fin (L : List (Bool × GExpr)) :
    (nd L : ℝ) = ∑ i : Fin L.length, (if L[i].1 then (1:ℝ) else 0) := by
  have : (nd L : ℝ) = (L.map fun p => if p.1 then (1:ℝ) else 0).sum := by
    induction L with
    | nil => simp [nd]
    | cons p L ih =>
      simp only [nd, List.countP_cons, List.map_cons, List.sum_cons] at ih ⊢
      push_cast; rw [ih]; split_ifs <;> ring
  rw [this, list_sum_fin]

lemma nd_perm {L L' : List (Bool × GExpr)} (σ : Fin L.length ≃ Fin L'.length)
    (hs : ∀ i, (L'[σ i]).1 = (L[i]).1) : nd L' = nd L := by
  have h : (nd L' : ℝ) = nd L := by
    rw [nd_fin, nd_fin, ← Equiv.sum_comp σ]
    exact Finset.sum_congr rfl fun i _ => by rw [hs i]
  exact_mod_cast h

/-- Products over a permuted chain compare factor by factor. -/
lemma perm_le {L L' : List (Bool × GExpr)} {Q : List (ℝ × ℝ × ℝ)} (σ : Fin L.length ≃ Fin L'.length)
    (hlQ : L.length = Q.length) (f : Bool × GExpr → ℝ) (g : (Bool × GExpr) × (ℝ × ℝ × ℝ) → ℝ)
    (h0 : ∀ i : Fin L.length, 0 ≤ f L'[σ i]) (h : ∀ i : Fin L.length, f L'[σ i] ≤ g (L[i], Q[(i : ℕ)]'(hlQ ▸ i.2))) :
    lp L' f ≤ ((L.zip Q).map g).prod := by
  rw [lp_perm σ, zip_prod hlQ]
  exact Finset.prod_le_prod₀ (fun i _ => h0 i) (fun i _ => h i)

lemma perm_ge {L L' : List (Bool × GExpr)} {Q : List (ℝ × ℝ × ℝ)} (σ : Fin L.length ≃ Fin L'.length)
    (hlQ : L.length = Q.length) (f : Bool × GExpr → ℝ) (g : (Bool × GExpr) × (ℝ × ℝ × ℝ) → ℝ)
    (h0 : ∀ i : Fin L.length, 0 ≤ g (L[i], Q[(i : ℕ)]'(hlQ ▸ i.2)))
    (h : ∀ i : Fin L.length, g (L[i], Q[(i : ℕ)]'(hlQ ▸ i.2)) ≤ f L'[σ i]) :
    ((L.zip Q).map g).prod ≤ lp L' f := by
  rw [lp_perm σ, zip_prod hlQ]
  exact Finset.prod_le_prod₀ (fun i _ => h0 i) (fun i _ => h i)


/-- `(1+x)ᵏ ≤ 1/(1 - kx)` for `0 ≤ x` and `kx < 1`. -/
lemma pow_le_inv {x : ℝ} (hx : 0 ≤ x) {k : ℕ} (hk : (k:ℝ)*x < 1) : (1+x)^k ≤ 1/(1-(k:ℝ)*x) := by
  have h1 : (1+x)^k ≤ Real.exp x^k :=
    pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) k
  rw [← Real.exp_nat_mul] at h1
  have h2 : 1-(k:ℝ)*x ≤ Real.exp (-((k:ℝ)*x)) := by linarith [Real.add_one_le_exp (-((k:ℝ)*x))]
  have h3 : Real.exp ((k:ℝ)*x) = 1/Real.exp (-((k:ℝ)*x)) := by rw [Real.exp_neg, one_div, inv_inv]
  rw [h3] at h1
  exact h1.trans (one_div_le_one_div_of_le (by linarith) h2)

/-- `prod_gap_mono` for families indexed by `Fin n`. -/
lemma fin_gap {n : ℕ} (f1 f2 f3 f4 : Fin n → ℝ)
    (h : ∀ i, 0 ≤ f1 i ∧ f1 i ≤ f2 i ∧ f1 i ≤ f3 i ∧ f3 i ≤ f4 i ∧ f2 i-f1 i ≤ f4 i-f3 i) :
    0 ≤ ∏ i, f1 i ∧ ∏ i, f1 i ≤ ∏ i, f2 i ∧ ∏ i, f2 i ≤ ∏ i, f4 i ∧
      ∏ i, f2 i-∏ i, f1 i ≤ ∏ i, f4 i-∏ i, f3 i := by
  have := prod_gap_mono ((List.finRange n).map fun i => (f1 i, f2 i, f3 i, f4 i)) (by
    intro q hq; obtain ⟨i, -, rfl⟩ := List.mem_map.mp hq; exact h i)
  simp only [List.map_map, Function.comp_def] at this
  simp only [Fin.prod_univ_def]
  exact this

set_option maxHeartbeats 4000000 in
/-- The product-chain bound covers every role-preserving reassociation. -/
lemma chainP_all {v E : ℕ → ℝ} {R : Av} {x : GExpr} (hx : IsProd x) {p : PD} (hp : PH v E p x)
    {cb : ℚ} (hcb : chainPB p = some cb) (hlo : (R.lo : ℝ) ≤ x.exact v) (hhi : x.exact v ≤ R.hi)
    (mc : Bool) (md : DD) :
    ∀ x', RA x x' → x'.Safe v E ∧ (prodAv R cb p mc md).H (x'.exact v) (x'.bound v E) := by
  intro x' hx'
  obtain ⟨hx'', σ, hsg, hl⟩ := hx'.prod_inv hx
  obtain ⟨hn, Q, hQ, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hp
  simp only [chainPB] at hcb
  split_ifs at hcb with hc
  obtain ⟨c1, cn, c2, c3, c4, c5, c6⟩ := hc
  simp only [Option.some.injEq] at hcb
  subst hcb
  have hlQ : (prodLeaves x).length = Q.length := hQ.length_eq
  have hlen : (prodLeaves x').length = (prodLeaves x).length := by
    rw [← Fintype.card_fin (prodLeaves x').length, ← Fintype.card_congr σ, Fintype.card_fin]
  have fac := Q_get hQ
  have ex : ∀ i : Fin (prodLeaves x).length, ((prodLeaves x')[σ i]).2.exact v = ((prodLeaves x)[i]).2.exact v := fun i => exact_RA v (hl i)
  have bd : ∀ i : Fin (prodLeaves x).length, ((prodLeaves x')[σ i]).2.Safe v E ∧ 0 ≤ ((prodLeaves x')[σ i]).2.bound v E ∧
      ((prodLeaves x')[σ i]).2.bound v E ≤ (Q[(i : ℕ)]'(hlQ ▸ i.2)).2.2 := fun i => (fac i).2.2.2.2 _ (hl i)
  have hU := WgslPoly.U_pos; have hη := η_pos; have hU' := U'_pos
  have hU1 : (1:ℝ) ≤ 1+WgslPoly.U := by linarith
  -- the closed-form bounds of `chainPB`
  have cn64 : (p.n:ℝ) ≤ 64 := by exact_mod_cast cn
  have hUv : WgslPoly.U = 5/2^24 := by simp [WgslPoly.U, u]; norm_num
  have hU'v : U' = 5/2^24+1/2^26 := by simp [U', hUv]
  have cn' : (p.n:ℝ)*WgslPoly.U < 1/2 := by rw [hUv]; nlinarith
  have cm' : (p.d.m:ℝ)*U' < 1/2 := by
    have : (p.d.m:ℝ) ≤ p.n := by rw [← a5, ← hn]; exact_mod_cast nd_le _
    rw [hU'v]; nlinarith
  have P0 : (0:ℝ) ≤ p.d.P := le_trans (zD_nonneg fun q hq => add_nonneg zero_le_one
    (div_nonneg (Q_nn hQ q hq).2.2 (Q_nn hQ q hq).1)) a8
  have hm1 : ((p.d.m-1 : ℕ) : ℝ)*U' < 1 := by
    have : ((p.d.m-1 : ℕ) : ℝ) ≤ p.d.m := by exact_mod_cast Nat.sub_le _ _
    nlinarith
  set Xr : ℝ := (p.d.P:ℝ)/(1-((p.d.m-1 : ℕ) : ℝ)*U')
  have cX : ((p.d.P/(1-((p.d.m-1 : ℕ) : ℚ)*qU') : ℚ) : ℝ) = Xr := by push_cast; rw [qU'_eq]
  set XU := (p.d.P:ℝ)*(1+U')^(p.d.m-1)
  have XUr : XU ≤ Xr := by
    have := pow_le_inv hU'.le hm1
    calc XU ≤ (p.d.P:ℝ)*(1/(1-((p.d.m-1 : ℕ) : ℝ)*U')) := mul_le_mul_of_nonneg_left this P0
      _ = Xr := by simp only [Xr]; ring
  have c1' : (0:ℝ) < p.d.T := by exact_mod_cast c1
  have Xr2 : Xr < 2 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr c2
    rw [cX] at h; norm_num at h ⊢; linarith
  have c2' : XU < 2 := by linarith
  have c3' : (1:ℝ)/2^100 ≤ p.d.mn := by
    have h1 : ((q2m100 : ℚ) : ℝ) ≤ p.d.mn := by exact_mod_cast c3
    have h2 : ((q2m100 : ℚ) : ℝ) = 1/2^100 := by norm_num [q2m100]
    linarith
  have c4' : (1:ℝ)/2^126 ≤ p.d.mn*(2-XU) := by
    have : ((qη : ℚ) : ℝ) ≤ ((p.d.mn*(2-p.d.P/(1-((p.d.m-1 : ℕ) : ℚ)*qU')) : ℚ) : ℝ) := by exact_mod_cast c4
    rw [qη_eq] at this; push_cast at this; rw [qU'_eq] at this
    exact this.trans (mul_le_mul_of_nonneg_left (by linarith) a9)
  have mx0 : (0:ℝ) ≤ p.d.mx := le_trans (zD_nonneg fun q _ => le_max_of_le_left zero_le_one) a11
  have c5' : (p.d.mx:ℝ)*XU ≤ 2^126 := by
    have : ((p.d.mx*(p.d.P/(1-((p.d.m-1 : ℕ) : ℚ)*qU')) : ℚ) : ℝ) ≤ ((q2p126 : ℚ) : ℝ) := by exact_mod_cast c5
    rw [q2p126_eq] at this; push_cast at this; rw [qU'_eq] at this
    exact (mul_le_mul_of_nonneg_left XUr mx0).trans this
  set cU := 2-XU
  have cU0 : 0 < cU := by simp only [cU]; linarith
  have cXr : 0 < 2-Xr := by linarith
  have cUr : 2-Xr ≤ cU := by simp only [cU]; linarith
  set MU := (p.M:ℝ)*p.d.im/cU^p.d.m
  set Mr : ℝ := (p.M:ℝ)*p.d.im/(2-Xr)^p.d.m
  have M0 : (0:ℝ) ≤ (p.M:ℝ)*p.d.im := mul_nonneg
    (le_trans (zN_nonneg fun q _ => le_max_of_le_left zero_le_one) a2)
    (le_trans (zD_nonneg fun q _ => le_max_of_le_left zero_le_one) a12)
  have MUr : MU ≤ Mr := by
    exact div_le_div_of_nonneg_left M0 (pow_pos cXr _) (pow_le_pow_left₀ cXr.le cUr _)
  have Kn : (1+WgslPoly.U)^p.n ≤ 1/(1-(p.n:ℝ)*WgslPoly.U) := pow_le_inv hU.le (by linarith)
  have c6' : 4*(p.n:ℝ)^2*η*(1+WgslPoly.U)^p.n*MU ≤ 1 := by
    have hM90 : Mr ≤ 2^90 := by
      have : ((p.M*p.d.im/(2-p.d.P/(1-((p.d.m-1 : ℕ) : ℚ)*qU'))^p.d.m : ℚ) : ℝ) ≤
          ((1237940039285380274899124224 : ℚ) : ℝ) := by exact_mod_cast c6
      simp only [Mr, Xr]; push_cast at this ⊢; rw [qU'_eq] at this; norm_num at this ⊢; linarith
    have hK2 : (1+WgslPoly.U)^p.n ≤ 2 := Kn.trans (by
      rw [div_le_iff₀ (by linarith)]; linarith)
    have MU0 : 0 ≤ MU := div_nonneg M0 (pow_pos cU0 _).le
    have hη' : η = 1/2^126 := rfl
    have n2 : (p.n:ℝ)^2 ≤ 64^2 := pow_le_pow_left₀ (by positivity) cn64 2
    calc 4*(p.n:ℝ)^2*η*(1+WgslPoly.U)^p.n*MU ≤ 4*64^2*η*2*2^90 := by
          gcongr
          exact MUr.trans hM90
      _ ≤ 1 := by rw [hη']; norm_num
  -- divisors are nonzero
  have lam : ∀ i : Fin (prodLeaves x).length, ((prodLeaves x)[i]).1 = true → 0 < (Q[(i : ℕ)]'(hlQ ▸ i.2)).1 := by
    intro i hi
    have hpos : 0 < zD (prodLeaves x) Q (·.1) := c1'.trans_le a7
    rw [zD, zip_prod hlQ] at hpos
    have hne := (Finset.prod_ne_zero_iff.mp hpos.ne') i (Finset.mem_univ _)
    simp only [hi, ↓reduceIte] at hne
    exact lt_of_le_of_ne (fac i).1 (Ne.symm hne)
  have tpos : ∀ i : Fin (prodLeaves x).length, ((prodLeaves x)[i]).1 = true → 0 < |((prodLeaves x')[σ i]).2.exact v| := fun i hi => by
    rw [ex]; exact (lam i hi).trans_le (fac i).2.1
  have memL' : ∀ r ∈ (prodLeaves x'), ∃ i : Fin (prodLeaves x).length, r = (prodLeaves x')[σ i] := fun r hr => by
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hr
    exact ⟨σ.symm ⟨j, hj⟩, by simp⟩
  have H1 : LeafOK v E (prodLeaves x') := ⟨fun r hr => by
      obtain ⟨i, rfl⟩ := memL' r hr; exact ⟨(bd i).1, (bd i).2.1⟩,
    fun r hr hs => by obtain ⟨i, rfl⟩ := memL' r hr; rw [hsg] at hs; exact tpos i hs⟩
  have ndL : nd (prodLeaves x') = p.d.m := by rw [nd_perm σ hsg, a5]
  -- the divisor margins
  have dPle : lp (prodLeaves x') (dP v E) ≤ (p.d.P:ℝ) := by
    refine le_trans (perm_le σ hlQ _ (fun z => if z.1.1 then 1+z.2.2.2/z.2.1 else 1) ?_ ?_) a8
    · intro i; unfold WgslReassoc.dP; split_ifs
      · exact add_nonneg zero_le_one (div_nonneg (bd i).2.1 (abs_nonneg _))
      · exact zero_le_one
    · intro i; simp only [WgslReassoc.dP, hsg i]; split_ifs with hf
      · rw [ex i]
        have hl0 := lam i hf
        have h1 := div_le_div_of_nonneg_right (bd i).2.2 (abs_nonneg ((prodLeaves x)[i].2.exact v))
        have h2 := div_le_div_of_nonneg_left (fac i).2.2.2.1 hl0 (fac i).2.1
        linarith
      · exact le_rfl
  have XDle : XD v E (prodLeaves x') ≤ XU := by
    unfold XD; rw [ndL]; exact mul_le_mul_of_nonneg_right dPle (by positivity)
  have H2 : XD v E (prodLeaves x') < 2 := XDle.trans_lt c2'
  have dminge : (p.d.mn:ℝ) ≤ lp (prodLeaves x') (dmin v) := by
    refine a10.trans (perm_ge σ hlQ _ (fun z => if z.1.1 then Min.min 1 z.2.1 else 1) ?_ ?_)
    · intro i; dsimp only; split_ifs
      · exact le_min zero_le_one (fac i).1
      · exact zero_le_one
    · intro i; simp only [WgslReassoc.dmin, hsg i]; split_ifs with hf
      · rw [ex i]; exact min_le_min le_rfl (fac i).2.1
      · exact le_rfl
  have H3 : 1/2^100 ≤ lp (prodLeaves x') (dmin v) := c3'.trans dminge
  have cDge : cU ≤ cD v E (prodLeaves x') := by unfold cD; simp only [cU]; linarith
  have H4 : 1/2^126 ≤ lp (prodLeaves x') (dmin v)*cD v E (prodLeaves x') :=
    c4'.trans (mul_le_mul dminge cDge cU0.le (a9.trans dminge))
  have dmaxle : lp (prodLeaves x') (dmax v) ≤ (p.d.mx:ℝ) := by
    refine le_trans (perm_le σ hlQ _ (fun z => if z.1.1 then Max.max 1 z.2.2.1 else 1) ?_ ?_) a11
    · intro i; exact zero_le_one.trans (one_le_dmax _)
    · intro i; simp only [WgslReassoc.dmax, hsg i]; split_ifs with hf
      · rw [ex i]; exact max_le_max le_rfl (fac i).2.2.1
      · exact le_rfl
  have xd1 := one_le_XD H1
  have dm1 : 1 ≤ lp (prodLeaves x') (dmax v) := lp_one_le fun r _ => one_le_dmax r
  have H5 : lp (prodLeaves x') (dmax v)*XD v E (prodLeaves x') ≤ 2^126 :=
    (mul_le_mul dmaxle XDle (by linarith) (by linarith)).trans c5'
  -- the `η` weight
  have nMle : lp (prodLeaves x') (nM v E) ≤ (p.M:ℝ) := by
    refine le_trans (perm_le σ hlQ _ (fun z => if z.1.1 then 1 else Max.max 1 (z.2.2.1+z.2.2.2)) ?_ ?_) a2
    · intro i; exact zero_le_one.trans (one_le_nM _)
    · intro i; simp only [WgslReassoc.nM, hsg i]; split_ifs with hf
      · exact le_rfl
      · rw [ex i]; exact max_le_max le_rfl (add_le_add (fac i).2.2.1 (bd i).2.2)
  have dIMle : lp (prodLeaves x') (dIM v) ≤ (p.d.im:ℝ) := by
    refine le_trans (perm_le σ hlQ _ (fun z => if z.1.1 then Max.max 1 (1/z.2.1) else 1) ?_ ?_) a12
    · intro i; exact zero_le_one.trans (one_le_dIM _)
    · intro i; simp only [WgslReassoc.dIM, hsg i]; split_ifs with hf
      · rw [ex i]; exact max_le_max le_rfl (one_div_le_one_div_of_le (lam i hf) (fac i).2.1)
      · exact le_rfl
  have nM1 : 1 ≤ lp (prodLeaves x') (nM v E) := lp_one_le fun r _ => one_le_nM r
  have dI1 : 1 ≤ lp (prodLeaves x') (dIM v) := lp_one_le fun r _ => one_le_dIM r
  have cD0 : 0 < cD v E (prodLeaves x') := cU0.trans_le cDge
  have Mfle : Mf v E (prodLeaves x') ≤ MU := by
    unfold Mf; rw [ndL]
    exact div_le_div₀ (mul_nonneg (by linarith) (by linarith)) (mul_le_mul nMle dIMle (by linarith) (by linarith))
      (pow_pos cU0 _) (pow_le_pow_left₀ cU0.le cDge _)
  have hn' : (prodLeaves x').length = p.n := by rw [hlen, hn]
  have H6 : 4*((prodLeaves x').length:ℝ)^2*η*(1+WgslPoly.U)^(prodLeaves x').length*
      Mf v E (prodLeaves x') ≤ 1 := by
    rw [hn']; exact le_trans (mul_le_mul_of_nonneg_left Mfle (by positivity)) c6'
  obtain ⟨s', b0, hb⟩ := prod_bound v E x' H1 H2 H3 H4 H5 H6
  have hex := exact_RA v hx'
  refine ⟨s', by rw [hex]; exact hlo, by rw [hex]; exact hhi, b0, ?_⟩
  simp only [prodAv]
  refine le_trans ?_ (le_rup_real _ _)
  set Kr : ℝ := 1/(1-((p.n-1 : ℕ) : ℝ)*WgslPoly.U)
  have ecb : ((((1/(1-((p.n-1 : ℕ) : ℚ)*qU))/(2-p.d.P/(1-((p.d.m-1 : ℕ) : ℚ)*qU'))*p.ψ-p.T)/p.d.T+
      2*((p.n:ℚ)-1)*(1/(1-((p.n-1 : ℕ) : ℚ)*qU))*qη*(p.M*p.d.im/(2-p.d.P/(1-((p.d.m-1 : ℕ) : ℚ)*qU'))^p.d.m) : ℚ) : ℝ) =
      (Kr/(2-Xr)*p.ψ-p.T)/p.d.T+2*((p.n:ℝ)-1)*Kr*η*Mr := by
    simp only [Kr, Xr, Mr]; push_cast; rw [qU_eq, qη_eq, qU'_eq]
  refine le_trans ?_ ((Rat.cast_le (K := ℝ)).mpr (le_max_right R.b _))
  rw [ecb]
  rw [hn'] at hb
  -- magnitudes of the reassociated chain
  have dTge : (p.d.T:ℝ) ≤ lp (prodLeaves x') (dT v) := by
    refine a7.trans (perm_ge σ hlQ _ (fun z => if z.1.1 then z.2.1 else 1) ?_ ?_)
    · intro i; dsimp only; split_ifs
      · exact (fac i).1
      · exact zero_le_one
    · intro i; simp only [WgslReassoc.dT, hsg i]; split_ifs with hf
      · rw [ex i]; exact (fac i).2.1
      · exact le_rfl
  have dT0 : 0 < lp (prodLeaves x') (dT v) := c1'.trans_le dTge
  have gap := fin_gap (fun i => nT v (prodLeaves x')[σ i]) (fun i => nψ v E (prodLeaves x')[σ i])
    (fun i => if ((prodLeaves x)[i]).1 then 1 else (Q[(i : ℕ)]'(hlQ ▸ i.2)).2.1)
    (fun i => if ((prodLeaves x)[i]).1 then 1 else (Q[(i : ℕ)]'(hlQ ▸ i.2)).2.1+(Q[(i : ℕ)]'(hlQ ▸ i.2)).2.2)
    (fun i => by
      simp only [WgslReassoc.nT, WgslReassoc.nψ, hsg i]
      split_ifs with hf
      · norm_num
      · rw [ex i]
        have := (fac i).2.2.1; have := (bd i).2.1; have := (bd i).2.2; have := (fac i).2.2.2.1
        refine ⟨abs_nonneg _, by linarith, by linarith, by linarith, by linarith⟩)
  rw [← lp_perm σ, ← lp_perm σ] at gap
  have eTU : (∏ i : Fin (prodLeaves x).length,
      (if ((prodLeaves x)[i]).1 then 1 else (Q[(i : ℕ)]'(hlQ ▸ i.2)).2.1)) = zN (prodLeaves x) Q (·.2.1) := by
    rw [zN, zip_prod hlQ]
  have ePU : (∏ i : Fin (prodLeaves x).length, (if ((prodLeaves x)[i]).1 then 1 else
      (Q[(i : ℕ)]'(hlQ ▸ i.2)).2.1+(Q[(i : ℕ)]'(hlQ ▸ i.2)).2.2)) =
      zN (prodLeaves x) Q (fun q => q.2.1+q.2.2) := by
    rw [zN, zip_prod hlQ]
  rw [eTU, ePU] at gap
  obtain ⟨g0, g1, g2, g3⟩ := gap
  set Ts := lp (prodLeaves x') (nT v); set Ps := lp (prodLeaves x') (nψ v E)
  set TU := zN (prodLeaves x) Q (·.2.1); set PU := zN (prodLeaves x) Q (fun q => q.2.1+q.2.2)
  set K := (1+WgslPoly.U)^(p.n-1)
  have K1 : 1 ≤ K := one_le_pow₀ hU1
  set cD' := cD v E (prodLeaves x')
  have cD1 : cD' ≤ 1 := by simp only [cD', cD]; linarith
  have A'1 : 1 ≤ K/cD' := by rw [le_div_iff₀ cD0]; nlinarith
  have A'A : K/cD' ≤ K/cU := div_le_div_of_nonneg_left (by linarith) cU0 cDge
  have hX0 : 0 ≤ K/cD'*Ps-Ts := by nlinarith
  have hXY : K/cD'*Ps-Ts ≤ K/cU*p.ψ-p.T := by
    have e1 : (K/cD'-1)*Ps ≤ (K/cU-1)*PU := mul_le_mul (by linarith) g2 (by linarith) (by linarith)
    have e2 : K/cU*PU ≤ K/cU*p.ψ := mul_le_mul_of_nonneg_left a1 (by linarith)
    nlinarith
  have hexact : |x'.exact v| = Ts/lp (prodLeaves x') (dT v) := abs_prod_exact v x'
  have hRf : Rf v E (prodLeaves x') = Ps/(lp (prodLeaves x') (dT v)*cD') := rfl
  have hn1 : (0:ℝ) ≤ (p.n:ℝ)-1 := by
    have : 1 ≤ p.n := by rw [← hn]; exact prodLeaves_length_pos x
    have : (1:ℝ) ≤ p.n := by exact_mod_cast this
    linarith
  have hM : 2*((p.n:ℝ)-1)*η*Mf v E (prodLeaves x') ≤ 2*((p.n:ℝ)-1)*η*MU :=
    mul_le_mul_of_nonneg_left Mfle (by positivity)
  rw [hexact, hRf] at hb
  have hsplit : K*(Ps/(lp (prodLeaves x') (dT v)*cD')) = K/cD'*Ps/lp (prodLeaves x') (dT v) := by
    field_simp
  have hX1 : (K/cD'*Ps-Ts)/lp (prodLeaves x') (dT v) ≤ (K/cU*p.ψ-p.T)/p.d.T :=
    (div_le_div_of_nonneg_left hX0 c1' dTge).trans (div_le_div_of_nonneg_right hXY c1'.le)
  have : x'.bound v E ≤ (K/cD'*Ps-Ts)/lp (prodLeaves x') (dT v)+K*(2*((p.n:ℝ)-1)*η*Mf v E (prodLeaves x')) := by
    rw [sub_div]; nlinarith
  have hKM := mul_le_mul_of_nonneg_left hM (by linarith : (0:ℝ) ≤ K)
  -- the closed-form bounds of `chainPB` only enlarge the bound
  have hn1' : ((p.n-1 : ℕ) : ℝ)*WgslPoly.U < 1 := by
    have : ((p.n-1 : ℕ) : ℝ) ≤ p.n := by exact_mod_cast Nat.sub_le _ _
    nlinarith
  have KKr : K ≤ Kr := pow_le_inv hU.le hn1'
  have Kr0 : 0 ≤ Kr := le_trans (by linarith) KKr
  have ψ0 : (0:ℝ) ≤ p.ψ := le_trans (zN_nonneg fun q hq => add_nonneg (Q_nn hQ q hq).2.1 (Q_nn hQ q hq).2.2) a1
  have e1 : K/cU ≤ Kr/(2-Xr) := div_le_div₀ Kr0 KKr cXr (by simp only [cU]; linarith)
  have e2 : (K/cU*p.ψ-p.T)/p.d.T ≤ (Kr/(2-Xr)*p.ψ-p.T)/p.d.T :=
    div_le_div_of_nonneg_right (by nlinarith) c1'.le
  have e3 : K*(2*((p.n:ℝ)-1)*η*MU) ≤ 2*((p.n:ℝ)-1)*Kr*η*Mr := by
    have := mul_le_mul KKr (mul_le_mul_of_nonneg_left MUr (by positivity : (0:ℝ) ≤ 2*((p.n:ℝ)-1)*η))
      (by have := div_nonneg M0 (pow_pos cU0 p.d.m).le; positivity) Kr0
    linarith
  linarith

end ProdChain


/-! ### Every reassociation

WGSL may evaluate each sum chain in any association (`WgslReassoc.RA`). The
evaluator's bounds cover all of them: at a sum it takes the larger of the
running bound and the chain bound of `WgslReassoc.sum_bound`, and it carries
each chain's leaf data across `let` slots, where a chain may continue. -/

section Robust
open WgslReassoc WgslLets

/-- `A` encloses every reassociation of `x`, which is `Safe`, and records
`x`'s sum chain. -/
structure RH (v E : ℕ → ℝ) (A : Av) (x : GExpr) : Prop where
  all : ∀ x', RA x x' → x'.Safe v E ∧ A.H (x'.exact v) (x'.bound v E)
  sflag : A.sc = true ↔ IsSum x
  sdata : A.sc = true → (sumLeaves x).length = A.sn ∧ lmag v (sumLeaves x) ≤ A.sm ∧
    ∃ bs : List ℝ, List.Forall₂ (fun p β => ∀ x', RA p.2 x' →
      x'.Safe v E ∧ 0 ≤ x'.bound v E ∧ x'.bound v E ≤ β) (sumLeaves x) bs ∧ bs.sum ≤ A.sb
  pflag : A.pc = true ↔ IsProd x
  pdata : A.pc = true → PH v E A.pd x
  mflag : A.mc = true ↔ IsMul x
  mdata : A.mc = true → MH v E A.md x

/-- The leaf condition of a chain. -/
abbrev LeafP (v E : ℕ → ℝ) (p : Bool × GExpr) (β : ℝ) : Prop :=
  ∀ x', RA p.2 x' → x'.Safe v E ∧ 0 ≤ x'.bound v E ∧ x'.bound v E ≤ β

lemma RH.self {v E : ℕ → ℝ} {A : Av} {x : GExpr} (h : RH v E A x) :
    x.Safe v E ∧ A.H (x.exact v) (x.bound v E) := h.all x (RA.refl x)

/-- A value's chain data, whether or not it is a chain. -/
lemma RH.sd {v E : ℕ → ℝ} {A : Av} {x : GExpr} (h : RH v E A x) :
    (sumLeaves x).length = sdn A ∧ lmag v (sumLeaves x) ≤ sdm A ∧
      ∃ bs : List ℝ, List.Forall₂ (LeafP v E) (sumLeaves x) bs ∧ bs.sum ≤ sdb A := by
  by_cases hs : A.sc = true
  · obtain ⟨h1, h2, h3⟩ := h.sdata hs
    simp only [sdn, sdm, sdb, hs, ↓reduceIte]
    exact ⟨h1, h2, h3⟩
  · have hns : ¬ IsSum x := fun hx => hs (h.sflag.mpr hx)
    simp only [sdn, sdm, sdb, hs, Bool.false_eq_true, ↓reduceIte, sumLeaves_of_not hns]
    obtain ⟨-, hH⟩ := h.self
    refine ⟨rfl, ?_, [A.b], List.Forall₂.cons ?_ List.Forall₂.nil, by simp⟩
    · simp only [lmag, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      exact abs_le_mag hH
    · intro x' hx'
      obtain ⟨s', h1, h2, h3, h4⟩ := h.all x' hx'
      exact ⟨s', h3, h4⟩

/-- The leaf bounds of a chain bound the leaf bounds of every reassociation. -/
lemma chain_RH {v E : ℕ → ℝ} {R : Av} {x : GExpr} (hx : IsSum x) {n : ℕ} {sm sb : ℚ}
    (hn : (sumLeaves x).length = n) (hm : lmag v (sumLeaves x) ≤ sm) {bs : List ℝ}
    (hb : List.Forall₂ (LeafP v E) (sumLeaves x) bs) (hs : bs.sum ≤ sb)
    (hlo : (R.lo : ℝ) ≤ x.exact v) (hhi : x.exact v ≤ R.hi) :
    RH v E (chainAv R n sm sb) x := by
  have hU := WgslPoly.U_pos; have hη := η_pos
  have hnp : ¬ IsProd x := by cases x <;> simp_all [IsSum, IsProd]
  have hnm : ¬ IsMul x := by cases x <;> simp_all [IsSum, IsMul]
  refine ⟨fun x' hx' => ?_, by simp [chainAv, hx], fun _ => ⟨hn, hm, bs, hb, hs⟩,
    by simp [chainAv, hnp], fun h => by simp [chainAv] at h, by simp [chainAv, hnm],
    fun h => by simp [chainAv] at h⟩
  obtain ⟨hx'', σ, hsg, hl⟩ := hx'.sum_inv hx
  obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.mp hb
  -- each leaf of `x'` is a reassociation of a leaf of `x`
  have leaf : ∀ j : Fin (sumLeaves x').length, ((sumLeaves x')[j]).2.Safe v E ∧
      0 ≤ ((sumLeaves x')[j]).2.bound v E ∧
      ((sumLeaves x')[j]).2.bound v E ≤ bs[(σ.symm j : ℕ)]'(hlen ▸ (σ.symm j).2) := by
    intro j
    have := hget (σ.symm j) (σ.symm j).2 (hlen ▸ (σ.symm j).2) _ (by simpa using hl (σ.symm j))
    exact this
  obtain ⟨s', b0, hbd⟩ := sum_bound v E x' fun p hp => by
    obtain ⟨j, rfl⟩ := List.get_of_mem hp
    exact ⟨(leaf j).1, (leaf j).2.1⟩
  have hn' : (sumLeaves x').length = n := by rw [← hn, ← Fintype.card_fin (sumLeaves x').length,
    ← Fintype.card_congr σ, Fintype.card_fin]
  have hmag : lmag v (sumLeaves x') = lmag v (sumLeaves x) := by
    simp only [lmag, list_sum_fin]
    rw [← Equiv.sum_comp σ]
    congr 1; ext i; rw [exact_RA v (hl i)]
  have hbnd : lbnd v E (sumLeaves x') ≤ sb := by
    simp only [lbnd, list_sum_fin]
    rw [← Equiv.sum_comp σ]
    calc ∑ i, ((sumLeaves x')[σ i]).2.bound v E
        ≤ ∑ i : Fin (sumLeaves x).length, bs[(i : ℕ)]'(hlen ▸ i.2) := by
          apply Finset.sum_le_sum; intro i _
          have := (leaf (σ i)).2.2; simpa using this
      _ = ∑ j : Fin bs.length, bs[(j : ℕ)] := Fintype.sum_equiv (finCongr hlen) _ _ (fun i => rfl)
      _ = bs.sum := by simp
      _ ≤ sb := hs
  rw [hn'] at hbd
  rw [hmag] at hbd
  have hP : (1:ℝ) ≤ (1+WgslPoly.U)^(n-1) := one_le_pow₀ (by linarith)
  have hM := lmag_nonneg v (sumLeaves x)
  refine ⟨s', ?_, ?_, b0, ?_⟩
  · rw [exact_RA v hx']; exact hlo
  · rw [exact_RA v hx']; exact hhi
  · simp only [chainAv]
    refine le_trans ?_ (le_rup_real _ _)
    push_cast
    refine le_trans ?_ (le_max_right _ _)
    simp only [chainB]; push_cast; rw [qU_eq, qη_eq]
    have hsb : (lbnd v E (sumLeaves x') : ℝ) ≤ sb := hbnd
    have hsm : lmag v (sumLeaves x) ≤ sm := hm
    have e1 := mul_le_mul_of_nonneg_left hsb (by linarith : (0:ℝ) ≤ (1+WgslPoly.U)^(n-1))
    have e2 := mul_le_mul_of_nonneg_left hsm (by linarith : (0:ℝ) ≤ (1+WgslPoly.U)^(n-1)-1)
    nlinarith

/-- Kernel inputs are boxes; inputs from `letBase` on are evaluated slots. -/
def EnvR (env : ℕ → Option Av) (σ : ℕ → GExpr) (v E : ℕ → ℝ) : Prop :=
  ∀ i A, env i = some A → (i < letBase → σ i = .input i ∧ A.H (v i) (E i)) ∧
    (letBase ≤ i → RH v E A (σ i))

lemma RH_leaf_input {v E : ℕ → ℝ} {A : Av} {i : ℕ} (h : A.H (v i) (E i)) :
    RH v E A.leaf (.input i) := by
  refine ⟨fun x' hx' => ?_, by simp [IsSum], fun h => by simp at h, by simp [IsProd],
    fun h => by simp at h, by simp [IsMul], fun h => by simp at h⟩
  cases hx' with
  | sum he => exact absurd he (by simp [IsSum])
  | prod he => exact absurd he (by simp [IsProd])
  | input => exact ⟨trivial, h⟩

lemma subst_input : ∀ e : GExpr, subst GExpr.input e = e := by
  intro e; induction e <;> simp_all [subst]

/-- Programs whose root is not a sum chain: every reassociation keeps the root. -/
lemma RH_of_root {v E : ℕ → ℝ} {R : Av} {x : GExpr} (hx : ¬ IsSum x ∧ ¬ IsProd x)
    (hR : R.sc = false ∧ R.pc = false ∧ R.mc = false)
    (h : ∀ x', RA x x' → x'.Safe v E ∧ R.H (x'.exact v) (x'.bound v E)) : RH v E R x := by
  have hm : ¬ IsMul x := by cases x <;> simp_all [IsProd, IsMul]
  exact ⟨h, by simp [hR.1, hx.1], fun h' => by simp [hR.1] at h', by simp [hR.2.1, hx.2],
    fun h' => by simp [hR.2.1] at h', by simp [hR.2.2, hm], fun h' => by simp [hR.2.2] at h'⟩

lemma sq_H' {A : Av} {x y X Y : ℝ} (hA : A.H x X) (hB : A.H y Y) (hxy : x = y) :
    (sqAv A).H (x*y) (|x| * Y+|y| * X+X*Y+WgslPoly.U*((|x|+X)*(|y|+Y))+η) := by
  subst hxy
  have h := sq_H hA
  exact ⟨h.1, h.2.1, mulB_nonneg hA hB, mulB_le hA hB⟩

end Robust

lemma RH.pd {v E : ℕ → ℝ} {A : Av} {x : GExpr} (h : RH v E A x) : PH v E (pdOf A) x := by
  unfold pdOf; split_ifs with hp
  · exact h.pdata hp
  · exact PH_leaf (fun hx => hp (h.pflag.mpr hx)) h.all

lemma RH.md {v E : ℕ → ℝ} {A : Av} {x : GExpr} (h : RH v E A x) : MH v E (mdOf A) x := by
  unfold mdOf; split_ifs with hm
  · exact h.mdata hm
  · exact MH_leaf (fun hx => hm (h.mflag.mpr hx)) h.all

section Robust2
open WgslReassoc WgslLets

/-- Unpacks a non-chain node: every reassociation keeps the node. -/
macro "root_tac" : tactic => `(tactic| (refine RH_of_root (by simp [IsSum, IsProd, subst]) ⟨rfl, rfl, rfl⟩ ?_))

/-- If the evaluator succeeds, every reassociation of the evaluated program
(with slots substituted by `σ`) is `Safe` and enclosed by the result. -/
theorem ev_robust (d : ℕ) (e : GExpr) : ∀ (env : ℕ → Option Av) (σ : ℕ → GExpr) (v E : ℕ → ℝ)
    (R : Av), EnvR env σ v E → ev d env e = some R → RH v E R (subst σ e) := by
  induction e with
  | input i =>
    intro env σ v E R henv h
    simp only [ev] at h
    simp only [subst]
    split_ifs at h with hi
    · obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hσ, hH⟩ := (henv i A hA).1 hi
      rw [hσ]; exact RH_leaf_input hH
    · exact (henv i R h).2 (by omega)
  | const c =>
    intro env σ v E R henv h
    simp only [ev, Option.some.injEq] at h; subst h
    root_tac
    intro x' hx'; simp only [subst] at hx'
    cases hx' with
    | sum he => exact absurd he (by simp [IsSum])
    | prod he => exact absurd he (by simp [IsProd])
    | const => exact ⟨trivial, le_rfl, le_rfl, by simp [bound], by simp [bound]⟩
  | add a b iha ihb =>
    intro env σ v E R henv h
    simp only [ev, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨A, ha, B, hb, rfl⟩ := h
    have rA := iha env σ v E A henv ha
    have rB := ihb env σ v E B henv hb
    obtain ⟨na, ma, bsa, fa, sa⟩ := rA.sd
    obtain ⟨nb, mb, bsb, fb, sb⟩ := rB.sd
    have hR := (add_H rA.self.2 rB.self.2).nrm
    refine chain_RH (by simp [IsSum, subst]) ?_ ?_ (List.rel_append fa fb) ?_ hR.1 hR.2.1
    · simp [subst, sumLeaves, na, nb]
    · simp only [subst, sumLeaves, lmag, List.map_append, List.sum_append] at ma mb ⊢
      push_cast; linarith
    · simp only [List.sum_append]; push_cast; linarith
  | sub a b iha ihb =>
    intro env σ v E R henv h
    simp only [ev, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨A, ha, B, hb, rfl⟩ := h
    have rA := iha env σ v E A henv ha
    have rB := ihb env σ v E B henv hb
    obtain ⟨na, ma, bsa, fa, sa⟩ := rA.sd
    obtain ⟨nb, mb, bsb, fb, sb⟩ := rB.sd
    have hR := (sub_H rA.self.2 rB.self.2).nrm
    refine chain_RH (by simp [IsSum, subst]) ?_ ?_ (List.rel_append fa (List.forall₂_map_left_iff.mpr fb)) ?_ hR.1 hR.2.1
    · simp [subst, sumLeaves, na, nb]
    · simp only [subst, sumLeaves]
      rw [show lmag v (sumLeaves (subst σ a) ++ (sumLeaves (subst σ b)).map fun p => (!p.1, p.2)) =
        lmag v (sumLeaves (subst σ a))+lmag v (sumLeaves (subst σ b)) by
          simp [lmag, Function.comp_def]]
      push_cast; linarith
    · simp only [List.sum_append]; push_cast; linarith
  | neg a iha =>
    intro env σ v E R henv h
    simp only [ev, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨A, ha, rfl⟩ := h
    have rA := iha env σ v E A henv ha
    obtain ⟨na, ma, bsa, fa, sa⟩ := rA.sd
    have hR := neg_H rA.self.2
    refine chain_RH (by simp [IsSum, subst]) ?_ ?_ (List.forall₂_map_left_iff.mpr fa) sa hR.1 hR.2.1
    · simp [subst, sumLeaves, na]
    · simp only [subst, sumLeaves, lmag_flip]; exact ma
  | mul a b iha ihb =>
    intro env σ v E R henv h
    simp only [ev, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨A, ha, B, hb, cb, hcb, rfl⟩ := h
    have hb' : ev d env b = some B := by
      split_ifs at hb with hab
      · subst hab; rw [ha]; exact hb
      · exact hb
    have rA := iha env σ v E A henv ha
    have rB := ihb env σ v E B henv hb'
    have hx : IsProd (subst σ (.mul a b)) := by simp [subst, IsProd]
    have hPH : PH v E ((pdOf A).mul (pdOf B)) (subst σ (.mul a b)) := PH_mul rA.pd rB.pd
    have hR : (nrm (if a = b then sqAv A else mulAv A B)).H ((subst σ (.mul a b)).exact v)
        ((subst σ (.mul a b)).bound v E) := by
      split_ifs with hab
      · subst hab
        obtain rfl : B = A := by rw [ha] at hb'; exact (Option.some.inj hb').symm
        exact (sq_H' rA.self.2 rB.self.2 rfl).nrm
      · exact (mul_H rA.self.2 rB.self.2).nrm
    exact ⟨chainP_all hx hPH hcb hR.1 hR.2.1 true _, by simp [prodAv, IsSum, subst],
      fun h => by simp [prodAv] at h, by simp [prodAv, hx], fun _ => hPH,
      by simp [prodAv, IsMul, subst], fun _ => MH_mul rA.md rB.md⟩
  | div a b iha ihb =>
    intro env σ v E R henv h
    simp only [ev, Option.bind_eq_some_iff] at h
    obtain ⟨A, ha, B, hb, h⟩ := h
    split_ifs at h with ok
    obtain ⟨cb, hcb, rfl⟩ := Option.map_eq_some_iff.mp h
    have rA := iha env σ v E A henv ha
    have rB := ihb env σ v E B henv hb
    have hx : IsProd (subst σ (.div a b)) := by simp [subst, IsProd]
    have hPH : PH v E ((pdOf A).div (mdOf B)) (subst σ (.div a b)) := PH_div rA.pd rB.md
    have hR := (div_H rA.self.2 rB.self.2 ok).1.nrm
    exact ⟨chainP_all hx hPH hcb hR.1 hR.2.1 false _, by simp [prodAv, IsSum, subst],
      fun h => by simp [prodAv] at h, by simp [prodAv, hx], fun _ => hPH,
      by simp [prodAv, IsMul, subst], fun h => by simp [prodAv] at h⟩
  | sqrt a iha =>
    intro env σ v E R henv h
    simp only [ev, Option.bind_eq_some_iff] at h
    obtain ⟨A, ha, h⟩ := h
    split_ifs at h with ok
    simp only [Option.some.injEq] at h; subst h
    have rA := iha env σ v E A henv ha
    root_tac
    intro x' hx'; simp only [subst] at hx'
    cases hx' with
    | sum he => exact absurd he (by simp [IsSum])
    | prod he => exact absurd he (by simp [IsProd])
    | sqrt ha' =>
      obtain ⟨s1, h1⟩ := rA.all _ ha'
      obtain ⟨hR, c1, c2⟩ := sqrt_H h1 ok
      exact ⟨⟨s1, c1, c2⟩, hR.nrm⟩
  | max a b iha ihb =>
    intro env σ v E R henv h
    simp only [ev, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨A, ha, B, hb, rfl⟩ := h
    have rA := iha env σ v E A henv ha
    have rB := ihb env σ v E B henv hb
    root_tac
    intro x' hx'; simp only [subst] at hx'
    cases hx' with
    | sum he => exact absurd he (by simp [IsSum])
    | prod he => exact absurd he (by simp [IsProd])
    | max ha' hb' =>
      obtain ⟨s1, h1⟩ := rA.all _ ha'
      obtain ⟨s2, h2⟩ := rB.all _ hb'
      exact ⟨⟨s1, s2⟩, max_H h1 h2⟩
  | min a b iha ihb =>
    intro env σ v E R henv h
    simp only [ev, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨A, ha, B, hb, rfl⟩ := h
    have rA := iha env σ v E A henv ha
    have rB := ihb env σ v E B henv hb
    root_tac
    intro x' hx'; simp only [subst] at hx'
    cases hx' with
    | sum he => exact absurd he (by simp [IsSum])
    | prod he => exact absurd he (by simp [IsProd])
    | min ha' hb' =>
      obtain ⟨s1, h1⟩ := rA.all _ ha'
      obtain ⟨s2, h2⟩ := rB.all _ hb'
      exact ⟨⟨s1, s2⟩, min_H h1 h2⟩
  | lt c t a b ihc iha ihb =>
    intro env σ v E R henv h
    simp only [ev, Option.bind_eq_some_iff] at h
    obtain ⟨C, hc, h⟩ := h
    have rC := ihc env σ v E C henv hc
    split_ifs at h with p q
    · obtain ⟨A, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      have rA := iha env σ v E A henv ha
      have p' : (C.hi:ℝ)+C.b < t := by exact_mod_cast p
      root_tac
      intro x' hx'; simp only [subst] at hx'
      cases hx' with
      | sum he => exact absurd he (by simp [IsSum])
      | prod he => exact absurd he (by simp [IsProd])
      | lt t hc' ha' hb' =>
        rename_i c' a' b'
        obtain ⟨sc, c1, c2, c3, c4⟩ := rC.all _ hc'
        obtain ⟨sa, hA⟩ := rA.all _ ha'
        have hlt : exact v c' < (t:ℝ) := by linarith
        simp only [exact, bound, Safe, hlt, ↓reduceIte]
        exact ⟨⟨sc, sa, by rw [abs_of_neg (by linarith)]; linarith⟩, hA⟩
    · obtain ⟨B, hb, rfl⟩ := Option.map_eq_some_iff.mp h
      have rB := ihb env σ v E B henv hb
      have q' : (t:ℝ) < C.lo-C.b := by exact_mod_cast q
      root_tac
      intro x' hx'; simp only [subst] at hx'
      cases hx' with
      | sum he => exact absurd he (by simp [IsSum])
      | prod he => exact absurd he (by simp [IsProd])
      | lt t hc' ha' hb' =>
        rename_i c' a' b'
        obtain ⟨sc, c1, c2, c3, c4⟩ := rC.all _ hc'
        obtain ⟨sb, hB⟩ := rB.all _ hb'
        have hlt : ¬ exact v c' < (t:ℝ) := by linarith
        simp only [exact, bound, Safe, hlt, ↓reduceIte]
        exact ⟨⟨sc, sb, by rw [abs_of_pos (by linarith)]; linarith⟩, hB⟩
  | abs a iha =>
    intro env σ v E R henv h
    simp only [ev, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨A, ha, rfl⟩ := h
    have rA := iha env σ v E A henv ha
    root_tac
    intro x' hx'; simp only [subst] at hx'
    cases hx' with
    | sum he => exact absurd he (by simp [IsSum])
    | prod he => exact absurd he (by simp [IsProd])
    | abs ha' =>
      obtain ⟨s1, h1⟩ := rA.all _ ha'
      exact ⟨s1, abs_H h1⟩
  | invsqrt a iha =>
    intro env σ v E R henv h
    simp only [ev, Option.bind_eq_some_iff] at h
    obtain ⟨A, ha, h⟩ := h
    split_ifs at h with ok
    simp only [Option.some.injEq] at h; subst h
    have rA := iha env σ v E A henv ha
    root_tac
    intro x' hx'; simp only [subst] at hx'
    cases hx' with
    | sum he => exact absurd he (by simp [IsSum])
    | prod he => exact absurd he (by simp [IsProd])
    | invsqrt ha' =>
      obtain ⟨s1, h1⟩ := rA.all _ ha'
      obtain ⟨hR, c1⟩ := inv_H h1 ok
      exact ⟨⟨s1, c1⟩, hR.nrm⟩
  | exp a iha =>
    intro env σ v E R henv h
    simp only [ev, Option.bind_eq_some_iff] at h
    obtain ⟨A, ha, h⟩ := h
    split_ifs at h with ok
    simp only [Option.some.injEq] at h; subst h
    have rA := iha env σ v E A henv ha
    root_tac
    intro x' hx'; simp only [subst] at hx'
    cases hx' with
    | sum he => exact absurd he (by simp [IsSum])
    | prod he => exact absurd he (by simp [IsProd])
    | exp ha' =>
      obtain ⟨s1, h1⟩ := rA.all _ ha'
      exact ⟨s1, (exp_H h1).nrm⟩
  | exp2 a iha =>
    intro env σ v E R henv h
    simp only [ev, Option.bind_eq_some_iff] at h
    obtain ⟨A, ha, h⟩ := h
    split_ifs at h with ok
    simp only [Option.some.injEq] at h; subst h
    have rA := iha env σ v E A henv ha
    root_tac
    intro x' hx'; simp only [subst] at hx'
    cases hx' with
    | sum he => exact absurd he (by simp [IsSum])
    | prod he => exact absurd he (by simp [IsProd])
    | exp2 ha' =>
      obtain ⟨s1, h1⟩ := rA.all _ ha'
      exact ⟨s1, (exp2_H h1).nrm⟩
  | log a iha =>
    intro env σ v E R henv h
    simp only [ev, Option.bind_eq_some_iff] at h
    obtain ⟨A, ha, h⟩ := h
    split_ifs at h with ok
    simp only [Option.some.injEq] at h; subst h
    have rA := iha env σ v E A henv ha
    root_tac
    intro x' hx'; simp only [subst] at hx'
    cases hx' with
    | sum he => exact absurd he (by simp [IsSum])
    | prod he => exact absurd he (by simp [IsProd])
    | log ha' =>
      obtain ⟨s1, h1⟩ := rA.all _ ha'
      obtain ⟨hR, c1⟩ := log_H h1 ok
      exact ⟨⟨s1, c1⟩, hR.nrm⟩
  | log2 a iha =>
    intro env σ v E R henv h
    simp only [ev, Option.bind_eq_some_iff] at h
    obtain ⟨A, ha, h⟩ := h
    split_ifs at h with ok
    simp only [Option.some.injEq] at h; subst h
    have rA := iha env σ v E A henv ha
    root_tac
    intro x' hx'; simp only [subst] at hx'
    cases hx' with
    | sum he => exact absurd he (by simp [IsSum])
    | prod he => exact absurd he (by simp [IsProd])
    | log2 ha' =>
      obtain ⟨s1, h1⟩ := rA.all _ ha'
      obtain ⟨hR, c1⟩ := log2_H h1 ok
      exact ⟨⟨s1, c1⟩, hR.nrm⟩
  | inh f a ihf iha =>
    intro env σ v E R henv h
    simp only [ev, Option.bind_eq_some_iff] at h
    obtain ⟨A, ha, h⟩ := h
    obtain ⟨R', hb, rfl⟩ := Option.map_eq_some_iff.mp h
    have rA := iha env σ v E A henv ha
    root_tac
    intro x' hx'; simp only [subst] at hx'
    cases hx' with
    | sum he => exact absurd he (by simp [IsSum])
    | prod he => exact absurd he (by simp [IsProd])
    | inh f ha' =>
      rename_i a'
      obtain ⟨s1, h1⟩ := rA.all _ ha'
      obtain ⟨hR, sf⟩ := bisect_sound _ _ _ _ _ _ (fun A' R'' hA' h' => by
        have := ihf (fun _ => some A'.leaf) GExpr.input (fun _ => exact v a') (fun _ => bound v E a') R''
          (fun i A'' h'' => by
            simp only [Option.some.injEq] at h''; subst h''
            exact ⟨fun _ => ⟨rfl, hA'⟩, fun _ => RH_leaf_input hA'⟩) h'
        rw [subst_input] at this
        exact ⟨this.self.2, this.self.1⟩) d A R' h1 hb
      exact ⟨⟨s1, sf⟩, hR⟩
  | tanh f a ihf iha =>
    intro env σ v E R henv h
    simp only [ev] at h
    split_ifs at h with hf
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨A, ha, R', hR', rfl⟩ := h
    have rA := iha env σ v E A henv ha
    root_tac
    intro x' hx'; simp only [subst] at hx'
    cases hx' with
    | sum he => exact absurd he (by simp [IsSum])
    | prod he => exact absurd he (by simp [IsProd])
    | tanh f ha' =>
      rename_i a'
      obtain ⟨s1, h1⟩ := rA.all _ ha'
      obtain ⟨hR, sf⟩ := bisect_sound _ _ _ _ _ _ (fun A' R'' hA' h' => by
        have := ihf (fun _ => some A'.leaf) GExpr.input (fun _ => exact v a') (fun _ => bound v E a') R''
          (fun i A'' h'' => by
            simp only [Option.some.injEq] at h''; subst h''
            exact ⟨fun _ => ⟨rfl, hA'⟩, fun _ => RH_leaf_input hA'⟩) h'
        rw [subst_input] at this
        exact ⟨this.self.2, this.self.1⟩) d A R' h1 hR'
      refine ⟨⟨s1, sf, by rw [hf]; exact WgslPlasma.tanhInh_exact⟩, Av.H.nrm ⟨?_,?_,?_,?_⟩⟩
      · exact tanhLo_le h1.1
      · exact le_tanhHi h1.2.1
      · exact le_max_of_le_left (by have := h1.2.2.1; positivity)
      · simp only [bound]; push_cast
        exact max_le_max (by have := h1.2.2.2; norm_num; linarith) hR.2.2.2
  | lt2 a b x y iha ihb ihx ihy =>
    intro env σ v E R henv h
    simp only [ev, Option.bind_eq_some_iff] at h
    obtain ⟨A, ha, B, hb, h⟩ := h
    have rA := iha env σ v E A henv ha
    have rB := ihb env σ v E B henv hb
    split_ifs at h with p q
    · obtain ⟨X, hx, rfl⟩ := Option.map_eq_some_iff.mp h
      have rX := ihx env σ v E X henv hx
      have p' : (A.hi:ℝ)-B.lo+(A.b+B.b) < 0 := by exact_mod_cast p
      root_tac
      intro x' hx'; simp only [subst] at hx'
      cases hx' with
      | sum he => exact absurd he (by simp [IsSum])
      | prod he => exact absurd he (by simp [IsProd])
      | lt2 ha' hb' hx' hy' =>
        rename_i a' b' x'' y''
        obtain ⟨sa, a1, a2, a3, a4⟩ := rA.all _ ha'
        obtain ⟨sb, b1, b2, b3, b4⟩ := rB.all _ hb'
        obtain ⟨sx, hX⟩ := rX.all _ hx'
        have hlt : exact v a' < exact v b' := by linarith
        simp only [exact, bound, Safe, hlt, ↓reduceIte]
        exact ⟨⟨sa, sb, sx, by rw [abs_of_neg (by linarith)]; linarith⟩, hX⟩
    · obtain ⟨Y, hy, rfl⟩ := Option.map_eq_some_iff.mp h
      have rY := ihy env σ v E Y henv hy
      have q' : (B.hi:ℝ)-A.lo+(A.b+B.b) < 0 := by exact_mod_cast q
      root_tac
      intro x' hx'; simp only [subst] at hx'
      cases hx' with
      | sum he => exact absurd he (by simp [IsSum])
      | prod he => exact absurd he (by simp [IsProd])
      | lt2 ha' hb' hx' hy' =>
        rename_i a' b' x'' y''
        obtain ⟨sa, a1, a2, a3, a4⟩ := rA.all _ ha'
        obtain ⟨sb, b1, b2, b3, b4⟩ := rB.all _ hb'
        obtain ⟨sy, hY⟩ := rY.all _ hy'
        have hlt : ¬ exact v a' < exact v b' := by linarith
        simp only [exact, bound, Safe, hlt, ↓reduceIte]
        exact ⟨⟨sa, sb, sy, by rw [abs_of_pos (by linarith)]; linarith⟩, hY⟩
  | sinS a iha =>
    intro env σ v E R henv h
    simp only [ev, Option.bind_eq_some_iff] at h
    obtain ⟨A, ha, h⟩ := h
    split_ifs at h with ok
    simp only [Option.some.injEq] at h; subst h
    have rA := iha env σ v E A henv ha
    root_tac
    intro x' hx'; simp only [subst] at hx'
    cases hx' with
    | sum he => exact absurd he (by simp [IsSum])
    | prod he => exact absurd he (by simp [IsProd])
    | sinS ha' =>
      obtain ⟨s1, h1⟩ := rA.all _ ha'
      obtain ⟨hR, c1⟩ := trig_H h1 ok _ (sinLo_le h1) (le_sinHi h1)
      exact ⟨⟨s1, c1⟩, hR.nrm⟩
  | cosS a iha =>
    intro env σ v E R henv h
    simp only [ev, Option.bind_eq_some_iff] at h
    obtain ⟨A, ha, h⟩ := h
    split_ifs at h with ok
    simp only [Option.some.injEq] at h; subst h
    have rA := iha env σ v E A henv ha
    root_tac
    intro x' hx'; simp only [subst] at hx'
    cases hx' with
    | sum he => exact absurd he (by simp [IsSum])
    | prod he => exact absurd he (by simp [IsProd])
    | cosS ha' =>
      obtain ⟨s1, h1⟩ := rA.all _ ha'
      obtain ⟨hR, c1⟩ := trig_H (hi := 1) h1 ok _ (cosLo_le h1)
        (by simpa using Real.cos_le_one _)
      exact ⟨⟨s1, c1⟩, hR.nrm⟩
  | scale k a iha =>
    intro env σ v E R henv h
    simp only [ev, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨A, ha, rfl⟩ := h
    have rA := iha env σ v E A henv ha
    root_tac
    intro x' hx'; simp only [subst] at hx'
    cases hx' with
    | sum he => exact absurd he (by simp [IsSum])
    | prod he => exact absurd he (by simp [IsProd])
    | scale k ha' =>
      obtain ⟨s1, h1⟩ := rA.all _ ha'
      exact ⟨s1, (scale_H k h1).nrm⟩
  | round a _ => intro env σ v E R henv h; simp [ev] at h
  | qsel j k s c _ _ _ => intro env σ v E R henv h; simp [ev] at h

end Robust2

section Robust3
open WgslReassoc WgslLets

/-- Kernel boxes only: no entries from `letBase` on. -/
def EnvLow (env : ℕ → Option Av) : Prop := ∀ i, letBase ≤ i → env i = none

/-- For a box environment, every reassociation of a program on which the
evaluator succeeds is `Safe` and enclosed. -/
theorem ev_robust_box (d : ℕ) (env : ℕ → Option Av) (e : GExpr) (v E : ℕ → ℝ) (R : Av)
    (henv : EnvH env v E) (hlow : EnvLow env) (h : ev d env e = some R) :
    ∀ x', RA e x' → x'.Safe v E ∧ R.H (x'.exact v) (x'.bound v E) := by
  have := ev_robust d e env GExpr.input v E R (fun i A hA =>
    ⟨fun _ => ⟨rfl, henv i A hA⟩, fun hi => by rw [hlow i hi] at hA; exact absurd hA (by simp)⟩) h
  rw [subst_input] at this
  exact this.1

/-- Evaluated slots enclose every reassociation of the expanded slots. -/
def SlotsR (v E : ℕ → ℝ) (vals : List Av) (X : List GExpr) : Prop :=
  vals.length = X.length ∧ ∀ j (hv : j < vals.length) (hX : j < X.length), RH v E vals[j] X[j]

lemma slotEnv_R {env : ℕ → Option Av} {v E : ℕ → ℝ} (henv : EnvH env v E) {vals : List Av}
    {X : List GExpr} (h : SlotsR v E vals X) : EnvR (slotEnv env vals) (lookup X) v E := by
  intro i A hA
  unfold slotEnv at hA
  constructor
  · intro hi
    simp only [show ¬ letBase ≤ i by omega, ↓reduceIte] at hA
    exact ⟨by simp [lookup, show ¬ letBase ≤ i by omega], henv i A hA⟩
  · intro hi
    simp only [hi, ↓reduceIte] at hA
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hA
    have hX : i-letBase < X.length := h.1 ▸ hlt
    simp only [lookup, hi, ↓reduceIte]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hX, Option.getD_some]
    exact h.2 _ hlt hX

lemma evSlots_robust (d : ℕ) {env : ℕ → Option Av} {v E : ℕ → ℝ} (henv : EnvH env v E) :
    ∀ (es : List GExpr) (done : List Av) (X : List GExpr) (vals : List Av), SlotsR v E done X →
      evSlots d env es done = some vals → SlotsR v E vals (expand X es)
  | [], done, X, vals, h, hs => by
    simp only [evSlots, Option.some.injEq] at hs; subst hs; exact h
  | e :: es, done, X, vals, h, hs => by
    simp only [evSlots, Option.bind_eq_some_iff] at hs
    obtain ⟨A, hA, hs⟩ := hs
    apply evSlots_robust d henv es _ _ vals _ hs
    have hR := ev_robust d e _ _ v E A (slotEnv_R henv h) hA
    refine ⟨by simp [h.1], fun j hv hX => ?_⟩
    rcases Nat.lt_or_ge j done.length with hj | hj
    · have hjX : j < X.length := h.1 ▸ hj
      rw [List.getElem_append_left hj, List.getElem_append_left hjX]
      exact h.2 j hj hjX
    · have e1 : j = done.length := by simp at hv; omega
      subst e1
      rw [List.getElem_append_right le_rfl, List.getElem_append_right (h.1 ▸ le_rfl)]
      simp only [Nat.sub_self, List.getElem_cons_zero, h.1]
      exact hR

/-- If the slot evaluation succeeds, every reassociation of the expanded
output, including chains that continue across `let` slots, is `Safe` and
enclosed. -/
theorem evLets_robust (d : ℕ) (env : ℕ → Option Av) (slots : List GExpr) (e : GExpr)
    (v E : ℕ → ℝ) (R : Av) (henv : EnvH env v E) (h : evLets d env slots e = some R) :
    ∀ x', RA (withLets slots e) x' → x'.Safe v E ∧ R.H (x'.exact v) (x'.bound v E) := by
  simp only [evLets, Option.bind_eq_some_iff] at h
  obtain ⟨vals, hv, hR⟩ := h
  have hS := evSlots_robust d henv slots [] [] vals ⟨rfl, fun j hv _ => absurd hv (by simp)⟩ hv
  exact (ev_robust d e _ _ v E R (slotEnv_R henv hS) hR).1

theorem evLetsAll_robust (d : ℕ) (env : ℕ → Option Av) (slots outs : List GExpr)
    (h : evLetsAll d env slots outs = true) (v E : ℕ → ℝ) (henv : EnvH env v E) :
    ∀ e ∈ outs, ∀ x', RA (withLets slots e) x' → x'.Safe v E := by
  intro e he
  unfold evLetsAll at h
  cases hs : evSlots d env slots [] with
  | none => rw [hs] at h; exact absurd h (by simp)
  | some vals =>
    rw [hs, List.all_eq_true] at h
    obtain ⟨R, hR⟩ := Option.isSome_iff_exists.mp (h e he)
    exact fun x' hx' => (evLets_robust d env slots e v E R henv (by simp [evLets, hs, hR]) x' hx').1

end Robust3

end BlackHole.WgslDomain
