module

public import BlackHole.WgslPlasma
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

/-- An interval `[lo, hi]` for an exact value and an upper bound `b` on its
running error bound. -/
structure Av where
  lo : ℚ
  hi : ℚ
  b : ℚ

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

def nrm (A : Av) : Av := ⟨rdn 160 A.lo, rup 160 A.hi, rup 160 A.b⟩

lemma Av.H.nrm {A : Av} {x B : ℝ} (h : A.H x B) : (nrm A).H x B :=
  ⟨(rdn_le_real _ _).trans h.1, h.2.1.trans (le_rup_real _ _), h.2.2.1,
    h.2.2.2.trans (le_rup_real _ _)⟩

def join (A B : Av) : Av := ⟨Min.min A.lo B.lo, Max.max A.hi B.hi, Max.max A.b B.b⟩

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
  ⟨A.lo+B.lo, A.hi+B.hi, A.b+B.b+qU*(mag A+mag B+A.b+B.b)+qη⟩
def subAv (A B : Av) : Av :=
  ⟨A.lo-B.hi, A.hi-B.lo, A.b+B.b+qU*(mag A+mag B+A.b+B.b)+qη⟩
def mulB (A B : Av) : ℚ := mag A*B.b+mag B*A.b+A.b*B.b+qU*((mag A+A.b)*(mag B+B.b))+qη
def mulAv (A B : Av) : Av := ⟨mulLo A.lo A.hi B.lo B.hi, mulHi A.lo A.hi B.lo B.hi, mulB A B⟩
def sqAv (A : Av) : Av :=
  ⟨if 0 ≤ A.lo then A.lo*A.lo else if A.hi ≤ 0 then A.hi*A.hi else 0,
    Max.max (A.lo*A.lo) (A.hi*A.hi), mulB A A⟩
def divOk (B : Av) : Prop := B.b < mig B ∧ qη ≤ mig B-B.b ∧ mag B+B.b ≤ q2p126
instance (B : Av) : Decidable (divOk B) := by unfold divOk; infer_instance
def divAv (A B : Av) : Av :=
  ⟨mulLo A.lo A.hi (1/B.hi) (1/B.lo), mulHi A.lo A.hi (1/B.hi) (1/B.lo),
    (A.b+mag A/mig B*B.b)/(mig B-B.b)+qU*((mag A+A.b)/(mig B-B.b))+qη⟩
def sqrtOk (A : Av) : Prop := 0 < A.lo ∧ A.b ≤ A.lo ∧ 0 < sqLo A.lo
instance (A : Av) : Decidable (sqrtOk A) := by unfold sqrtOk; infer_instance
def sqrtAv (A : Av) : Av :=
  ⟨sqLo A.lo, sqHi A.hi, A.b/sqLo A.lo+10*qu*sqHi (A.hi+A.b)+qη⟩
def invOk (A : Av) : Prop := A.b < A.lo ∧ 0 < sqLo (A.lo-A.b) ∧ 0 < sqLo A.lo
instance (A : Av) : Decidable (invOk A) := by unfold invOk; infer_instance
def invAv (A : Av) : Av :=
  ⟨1/sqHi A.hi, 1/sqLo A.lo,
    A.b/(sqLo (A.lo-A.b)*sqLo A.lo*(sqLo (A.lo-A.b)+sqLo A.lo))+4*qu/sqLo (A.lo-A.b)⟩
def absAv (A : Av) : Av :=
  ⟨if 0 ≤ A.lo then A.lo else if A.hi ≤ 0 then -A.hi else 0, mag A, A.b⟩
/-- `exp` arguments are kept moderate so that the enclosures stay small. -/
def expOk (A : Av) : Prop := -256 ≤ A.lo ∧ A.hi+A.b ≤ 256 ∧ A.b ≤ 256
instance (A : Av) : Decidable (expOk A) := by unfold expOk; infer_instance
def expAv (A : Av) : Av :=
  ⟨expLo A.lo, expHi A.hi,
    expHi A.hi*(expHi A.b-1)+(3+2*(mag A+A.b))*(2*qu*expHi (A.hi+A.b)+qη)⟩
def exp2Av (A : Av) : Av :=
  ⟨expLo (mulLo A.lo A.hi L2lo L2hi), expHi (mulHi A.lo A.hi L2lo L2hi),
    expHi (mulHi A.lo A.hi L2lo L2hi)*(expHi (A.b*L2hi)-1)+
      (3+2*(mag A+A.b))*(2*qu*expHi (mulHi A.lo (A.hi+A.b) L2lo L2hi)+qη)⟩
def logAv (A : Av) : Av :=
  ⟨logLo A.lo, logHi A.hi, A.b/(A.lo-A.b)+1/2097152+
    3*(2*qu*(Max.max |logLo A.lo| |logHi A.hi|+A.b/(A.lo-A.b))+qη)⟩
def log2Lo (A : Av) : ℚ := Min.min (logLo A.lo/L2lo) (logLo A.lo/L2hi)
def log2Hi (A : Av) : ℚ := Max.max (logHi A.hi/L2lo) (logHi A.hi/L2hi)
def log2Av (A : Av) : Av :=
  ⟨log2Lo A, log2Hi A, A.b/((A.lo-A.b)*L2lo)+1/2097152+
    3*(2*qu*(Max.max |log2Lo A| |log2Hi A|+A.b/((A.lo-A.b)*L2lo))+qη)⟩
def trigAv (lo hi : ℚ) (A : Av) : Av := ⟨lo, hi, A.b+128*qu*(1+(mag A+A.b))⟩
/-- `sin` on `[-1, 1]`, where it is increasing, from its Taylor bound. -/
def sinLo (A : Av) : ℚ := if -1 ≤ A.lo ∧ A.hi ≤ 1 then A.lo-A.lo^3/6-|A.lo|^5/100 else -1
def sinHi (A : Av) : ℚ := if -1 ≤ A.lo ∧ A.hi ≤ 1 then A.hi-A.hi^3/6+|A.hi|^5/100 else 1
def cosLo (A : Av) : ℚ := Max.max (-1) (1-mag A^2/2)
/-- `tanh x = 1 - 2/(exp (2x) + 1)`, increasing. -/
def tanhLo (x : ℚ) : ℚ := if -128 ≤ x ∧ x ≤ 128 then 1-2/(expLo (2*x)+1) else -1
def tanhHi (x : ℚ) : ℚ := if -128 ≤ x ∧ x ≤ 128 then 1-2/(expHi (2*x)+1) else 1
def scaleAv (k : ℤ) (A : Av) : Av := ⟨pow2 k*A.lo, pow2 k*A.hi, pow2 k*A.b+qη⟩

/-- Evaluates `g` on `2^n` equal pieces of `A`'s interval and joins the results. -/
def bisect (g : Av → Option Av) : ℕ → Av → Option Av
  | 0, A => g A
  | n+1, A =>
    (bisect g n ⟨A.lo, rdn 160 ((A.lo+A.hi)/2), A.b⟩).bind fun L =>
      (bisect g n ⟨rdn 160 ((A.lo+A.hi)/2), A.hi, A.b⟩).bind fun R => some (join L R)

/-- The interval evaluator; the arguments of `inh` and `tanh` builtins are
split into `2^d` pieces. -/
def ev (d : ℕ) (env : ℕ → Option Av) : GExpr → Option Av
  | .input i => env i
  | .const c => some ⟨c, c, 0⟩
  | .add a b => (ev d env a).bind fun A => (ev d env b).bind fun B => some (nrm (addAv A B))
  | .sub a b => (ev d env a).bind fun A => (ev d env b).bind fun B => some (nrm (subAv A B))
  | .mul a b => (ev d env a).bind fun A => (ev d env b).bind fun B =>
      some (nrm (if a = b then sqAv A else mulAv A B))
  | .neg a => (ev d env a).bind fun A => some ⟨-A.hi, -A.lo, A.b⟩
  | .div a b => (ev d env a).bind fun A => (ev d env b).bind fun B =>
      if divOk B then some (nrm (divAv A B)) else none
  | .sqrt a => (ev d env a).bind fun A => if sqrtOk A then some (nrm (sqrtAv A)) else none
  | .max a b => (ev d env a).bind fun A => (ev d env b).bind fun B =>
      some ⟨Max.max A.lo B.lo, Max.max A.hi B.hi, Max.max A.b B.b⟩
  | .min a b => (ev d env a).bind fun A => (ev d env b).bind fun B =>
      some ⟨Min.min A.lo B.lo, Min.min A.hi B.hi, Max.max A.b B.b⟩
  | .lt c t a b => (ev d env c).bind fun C =>
      if C.hi+C.b < t then ev d env a else if t < C.lo-C.b then ev d env b else none
  | .abs a => (ev d env a).bind fun A => some (absAv A)
  | .invsqrt a => (ev d env a).bind fun A => if invOk A then some (nrm (invAv A)) else none
  | .exp a => (ev d env a).bind fun A => if expOk A then some (nrm (expAv A)) else none
  | .exp2 a => (ev d env a).bind fun A => if expOk A then some (nrm (exp2Av A)) else none
  | .log a => (ev d env a).bind fun A => if A.b < A.lo then some (nrm (logAv A)) else none
  | .log2 a => (ev d env a).bind fun A => if A.b < A.lo then some (nrm (log2Av A)) else none
  | .inh f a => (ev d env a).bind fun A => bisect (fun A' => ev d (fun _ => some A') f) d A
  | .tanh f a => if f = WgslPlasma.tanhInh then (ev d env a).bind fun A =>
      (bisect (fun A' => ev d (fun _ => some A') f) d A).bind fun R =>
        some (nrm ⟨tanhLo A.lo, tanhHi A.hi, Max.max (A.b+1/100000) R.b⟩) else none
  | .lt2 a b x y => (ev d env a).bind fun A => (ev d env b).bind fun B =>
      if A.hi-B.lo+(A.b+B.b) < 0 then ev d env x
      else if B.hi-A.lo+(A.b+B.b) < 0 then ev d env y else none
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

lemma neg_H (hA : A.H x X) : (⟨-A.hi, -A.lo, A.b⟩ : Av).H (-x) X := by
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
    (⟨Max.max A.lo B.lo, Max.max A.hi B.hi, Max.max A.b B.b⟩ : Av).H (Max.max x y) (Max.max X Y) := by
  obtain ⟨a1,a2,a3,a4⟩ := hA; obtain ⟨b1,b2,b3,b4⟩ := hB
  refine ⟨?_,?_,le_max_of_le_left a3,?_⟩ <;> push_cast
  · exact max_le_max a1 b1
  · exact max_le_max a2 b2
  · exact max_le_max a4 b4

lemma min_H (hA : A.H x X) (hB : B.H y Y) :
    (⟨Min.min A.lo B.lo, Min.min A.hi B.hi, Max.max A.b B.b⟩ : Av).H (Min.min x y) (Max.max X Y) := by
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
    · obtain ⟨h1,h2⟩ := bisect_sound g x X y Y S hg n ⟨A.lo, rdn 160 ((A.lo+A.hi)/2), A.b⟩ L ⟨a1,hm,a3,a4⟩ hL
      exact ⟨h1.join_l R',h2⟩
    · obtain ⟨h1,h2⟩ := bisect_sound g x X y Y S hg n ⟨rdn 160 ((A.lo+A.hi)/2), A.hi, A.b⟩ R' ⟨hm,a2,a3,a4⟩ hR
      exact ⟨h1.join_r L,h2⟩

/-- Every input box contains its input and bounds its error. -/
def EnvH (env : ℕ → Option Av) (v E : ℕ → ℝ) : Prop := ∀ i A, env i = some A → A.H (v i) (E i)

/-- If the evaluator succeeds, `Safe` holds for every input in the boxes, and
the exact value and running bound lie within the result. -/
theorem ev_sound (d : ℕ) (e : GExpr) : ∀ (env : ℕ → Option Av) (v E : ℕ → ℝ) (R : Av),
    EnvH env v E → ev d env e = some R → R.H (e.exact v) (e.bound v E) ∧ e.Safe v E := by
  induction e with
  | input i => intro env v E R henv h; exact ⟨henv i R h,trivial⟩
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
    exact ⟨(add_H hA hB).nrm,sa,sb⟩
  | sub a b iha ihb =>
    intro env v E R henv h
    simp only [ev, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨A, ha, B, hb, rfl⟩ := h
    obtain ⟨hA, sa⟩ := iha env v E A henv ha
    obtain ⟨hB, sb⟩ := ihb env v E B henv hb
    exact ⟨(sub_H hA hB).nrm,sa,sb⟩
  | mul a b iha ihb =>
    intro env v E R henv h
    simp only [ev, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨A, ha, B, hb, rfl⟩ := h
    obtain ⟨hA, sa⟩ := iha env v E A henv ha
    obtain ⟨hB, sb⟩ := ihb env v E B henv hb
    refine ⟨?_,sa,sb⟩
    split_ifs with hab
    · subst hab
      exact (sq_H hA).nrm
    · exact (mul_H hA hB).nrm
  | neg a iha =>
    intro env v E R henv h
    simp only [ev, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨A, ha, rfl⟩ := h
    obtain ⟨hA, sa⟩ := iha env v E A henv ha
    exact ⟨neg_H hA,sa⟩
  | div a b iha ihb =>
    intro env v E R henv h
    simp only [ev, Option.bind_eq_some_iff] at h
    obtain ⟨A, ha, B, hb, h⟩ := h
    split_ifs at h with ok
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hA, sa⟩ := iha env v E A henv ha
    obtain ⟨hB, sb⟩ := ihb env v E B henv hb
    obtain ⟨hR, s1, s2, s3⟩ := div_H hA hB ok
    exact ⟨hR.nrm,sa,sb,s1,s2,s3⟩
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
    · obtain ⟨hA, sa⟩ := iha env v E R henv h
      have p' : (C.hi:ℝ)+C.b < t := by exact_mod_cast p
      have hlt : exact v c < (t:ℝ) := by linarith
      simp only [exact, bound, Safe, hlt, ↓reduceIte]
      exact ⟨hA,sc,sa,by rw [abs_of_neg (by linarith)]; linarith⟩
    · obtain ⟨hB, sb⟩ := ihb env v E R henv h
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
    obtain ⟨hA, sa⟩ := iha env v E A henv ha
    obtain ⟨hR, sf⟩ := bisect_sound _ _ _ _ _ _ (fun A' R' hA' h' =>
      ihf (fun _ => some A') (fun _ => exact v a) (fun _ => bound v E a) R'
        (fun _ A'' h'' => by simp only [Option.some.injEq] at h''; subst h''; exact hA') h') d A R hA h
    exact ⟨hR,sa,sf⟩
  | tanh f a ihf iha =>
    intro env v E R henv h
    simp only [ev] at h
    split_ifs at h with hf
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨A, ha, R', hR', rfl⟩ := h
    obtain ⟨hA, sa⟩ := iha env v E A henv ha
    obtain ⟨hR, sf⟩ := bisect_sound _ _ _ _ _ _ (fun A' R'' hA' h' =>
      ihf (fun _ => some A') (fun _ => exact v a) (fun _ => bound v E a) R''
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
    · obtain ⟨hX, sx⟩ := ihx env v E R henv h
      have p' : (A.hi:ℝ)-B.lo+(A.b+B.b) < 0 := by exact_mod_cast p
      have hlt : exact v a < exact v b := by linarith
      simp only [exact, bound, Safe, hlt, ↓reduceIte]
      exact ⟨hX,sa,sb,sx,by rw [abs_of_neg (by linarith)]; linarith⟩
    · obtain ⟨hY, sy⟩ := ihy env v E R henv h
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
  ref[i]?.map fun r => ⟨r-w*(1+|r|), r+w*(1+|r|), w*(1+|r|)⟩

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

end BlackHole.WgslDomain
