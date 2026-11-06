module

public import BlackHole.WgslDomain
public import BlackHole.WgslSafe
public import BlackHole.WgslAddKerr
public import Mathlib.Data.Int.Log

/-! Closed-form domains on which the `Safe` conditions of the branching WGSL
kernels hold (obligation F2).

Each theorem covers its domain by finitely many boxes, runs the checked
interval evaluator `WgslDomain.ev` on every box in the kernel, and applies
`ev_sound`. The domains stay a fixed distance from the branch thresholds and
singular points, where no all-input bound exists (`WgslSafe.bound_ge_half_variation`). -/

@[expose] public section

namespace BlackHole.WgslSafeDomains
open Wgsl WgslExpr GExpr WgslPlasma WgslDomain

/-- Every positive real lies in a binary octave `[2^k, 2^(k+1))`. -/
lemma octave {r : ℝ} (hr : 0 < r) : ∃ k : ℤ, (2:ℝ)^k ≤ r ∧ r < (2:ℝ)^(k+1) :=
  ⟨Int.log 2 r, by exact_mod_cast Int.zpow_log_le_self (b := 2) (by norm_num) hr,
    by exact_mod_cast Int.lt_zpow_succ_log_self (b := 2) (by norm_num) r⟩

lemma octave_range {r : ℝ} {k lo hi : ℤ} (h1 : (2:ℝ)^k ≤ r) (h2 : r < (2:ℝ)^(k+1))
    (hl : (2:ℝ)^lo ≤ r) (hh : r ≤ (2:ℝ)^hi) : lo ≤ k ∧ k ≤ hi := by
  constructor
  · by_contra h
    have : (2:ℝ)^(k+1) ≤ (2:ℝ)^lo := zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith
  · by_contra h
    have : (2:ℝ)^(hi+1) ≤ (2:ℝ)^k := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have : (2:ℝ)^hi < (2:ℝ)^(hi+1) := zpow_lt_zpow_right₀ (by norm_num) (by omega)
    linarith

lemma all_range {p : ℕ → Bool} {n : ℕ} (h : (List.range n).all p = true) {k : ℕ} (hk : k < n) :
    p k = true :=
  List.all_eq_true.mp h k (List.mem_range.mpr hk)

/-! ### `polarization_color` -/

/-- Octave `k` of the intensity `I`; slab `s` puts `Q` (`s = 0, 1`) or `U`
(`s = 2, 3`) at least `7/640` of `2^k` away from zero, positive or negative. -/
def polBox (k : ℤ) (s : ℕ) : ℕ → Option Av :=
  let a := pow2 k
  let e := 2*a/1048576
  let wide : Av := Av.mk3 (-2*a) (2*a) e
  let pos : Av := Av.mk3 (7/640*a) (2*a) e
  let neg : Av := Av.mk3 (-2*a) (-(7/640*a)) e
  fun i => match i with
    | 0 => some (Av.mk3 a (2*a) e)
    | 1 => some (if s = 0 then pos else if s = 1 then neg else wide)
    | 2 => some (if s = 2 then pos else if s = 3 then neg else wide)
    | _ => none

set_option maxRecDepth 100000 in
theorem polBox_ok : ((List.range 53).all fun k => (List.range 4).all fun s =>
    ([0,1,2] : List (Fin 3)).all fun j =>
      (ev 0 (polBox ((k:ℤ)-26) s) (polarizationHue j)).isSome) = true := by
  decide +kernel

/-- Every reassociation of `polarization_color`'s hue view (`WgslReassoc.RA`)
satisfies `Safe`, so its running bound holds, for every intensity in
`[2⁻²⁶, 2²⁶]` (above the `10⁻⁸` cutoff), every `|Q|, |U| ≤ I` with linear
polarization fraction at least `1/64`, and input errors up to `2⁻²⁰ I`. -/
theorem polarization_safe (j : Fin 3) (v E : ℕ → ℝ) (hI : (2:ℝ)^(-26:ℤ) ≤ v 0)
    (hI' : v 0 ≤ (2:ℝ)^(26:ℤ)) (hQ : |v 1| ≤ v 0) (hU : |v 2| ≤ v 0)
    (hpol : (v 0/64)^2 ≤ v 1^2+v 2^2) (hE : ∀ i, i < 3 → 0 ≤ E i ∧ E i ≤ v 0/2^20) :
    ∀ x', WgslReassoc.RA (polarizationHue j) x' → x'.Safe v E := by
  have hI0 : 0 < v 0 := lt_of_lt_of_le (by positivity) hI
  obtain ⟨k, hk1, hk2⟩ := octave hI0
  obtain ⟨kl, kh⟩ := octave_range hk1 hk2 hI hI'
  set a : ℝ := (2:ℝ)^k with ha
  have ha0 : 0 < a := by positivity
  have h2a : v 0 < 2*a := by rw [zpow_add_one₀ (by norm_num)] at hk2; rw [ha]; linarith
  have hslab : 7/640*a ≤ |v 1| ∨ 7/640*a ≤ |v 2| := by
    by_contra h
    simp only [not_or, not_le] at h
    have h1 : v 1^2 < (7/640*a)^2 := by
      rw [← sq_abs]; exact pow_lt_pow_left₀ h.1 (abs_nonneg _) (by norm_num)
    have h2 : v 2^2 < (7/640*a)^2 := by
      rw [← sq_abs]; exact pow_lt_pow_left₀ h.2 (abs_nonneg _) (by norm_num)
    have h3 : (a/64)^2 ≤ (v 0/64)^2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    nlinarith
  obtain ⟨s, hs, hsl⟩ : ∃ s < 4, (s = 0 → 7/640*a ≤ v 1) ∧ (s = 1 → v 1 ≤ -(7/640*a)) ∧
      (s = 2 → 7/640*a ≤ v 2) ∧ (s = 3 → v 2 ≤ -(7/640*a)) := by
    rcases hslab with h | h
    · rcases le_total 0 (v 1) with h0 | h0
      · exact ⟨0, by norm_num, by simp; rwa [abs_of_nonneg h0] at h⟩
      · exact ⟨1, by norm_num, by simp; rw [abs_of_nonpos h0] at h; linarith⟩
    · rcases le_total 0 (v 2) with h0 | h0
      · exact ⟨2, by norm_num, by simp; rwa [abs_of_nonneg h0] at h⟩
      · exact ⟨3, by norm_num, by simp; rw [abs_of_nonpos h0] at h; linarith⟩
  have hok := all_range polBox_ok (k := (k+26).toNat) (by omega)
  have hok' := all_range hok hs
  rw [List.all_eq_true] at hok'
  have hj := hok' j (by fin_cases j <;> simp)
  rw [show (((k+26).toNat : ℕ) : ℤ)-26 = k by omega] at hj
  obtain ⟨R, hR⟩ := Option.isSome_iff_exists.mp hj
  intro x' hx'
  refine (ev_robust_box 0 _ _ v E R ?_ ?_ hR x' hx').1
  rotate_left
  · intro i hi
    obtain ⟨n, rfl⟩ : ∃ n, i = n+3 := ⟨i-3, by simp only [WgslLets.letBase] at hi; omega⟩
    rfl
  have hpa : ((pow2 k : ℚ) : ℝ) = a := pow2_eq k
  have hb : ∀ i, i < 3 → 0 ≤ E i ∧ E i ≤ ((2*pow2 k/1048576 : ℚ) : ℝ) := by
    intro i hi
    obtain ⟨e0, e1⟩ := hE i hi
    refine ⟨e0, e1.trans ?_⟩
    push_cast; rw [hpa]; linarith
  have q1 : -(2*a) ≤ v 1 ∧ v 1 ≤ 2*a := by
    have := abs_le.mp hQ; constructor <;> linarith
  have q2 : -(2*a) ≤ v 2 ∧ v 2 ≤ 2*a := by
    have := abs_le.mp hU; constructor <;> linarith
  intro i A hA
  match i with
  | 0 =>
    simp only [polBox, Option.some.injEq] at hA; subst hA
    exact ⟨by push_cast; rw [hpa]; exact hk1, by push_cast; rw [hpa]; exact h2a.le,
      (hb 0 (by norm_num)).1, (hb 0 (by norm_num)).2⟩
  | 1 =>
    simp only [polBox, Option.some.injEq] at hA; subst hA
    refine ⟨?_,?_,(hb 1 (by norm_num)).1,?_⟩
    · split_ifs with p q <;> push_cast <;> rw [hpa]
      · exact hsl.1 p
      · linarith
      · linarith
    · split_ifs with p q <;> push_cast <;> rw [hpa]
      · linarith
      · exact hsl.2.1 q
      · linarith
    · split_ifs <;> exact (hb 1 (by norm_num)).2
  | 2 =>
    simp only [polBox, Option.some.injEq] at hA; subst hA
    refine ⟨?_,?_,(hb 2 (by norm_num)).1,?_⟩
    · split_ifs with p q <;> push_cast <;> rw [hpa]
      · exact hsl.2.2.1 p
      · linarith
      · linarith
    · split_ifs with p q <;> push_cast <;> rw [hpa]
      · linarith
      · exact hsl.2.2.2 q
      · linarith
    · split_ifs <;> exact (hb 2 (by norm_num)).2
  | n+3 => simp [polBox] at hA

/-- On the domain of `polarization_safe`, a WGSL evaluation of
`polarization_color`'s hue view in any association `x'` of its sums is within
the running bound of that association. -/
theorem polarization_error_all (j : Fin 3) (v w E : ℕ → ℝ) (hw : ∀ i, |w i-v i| ≤ E i)
    (hI : (2:ℝ)^(-26:ℤ) ≤ v 0) (hI' : v 0 ≤ (2:ℝ)^(26:ℤ)) (hQ : |v 1| ≤ v 0) (hU : |v 2| ≤ v 0)
    (hpol : (v 0/64)^2 ≤ v 1^2+v 2^2) (hE : ∀ i, i < 3 → E i ≤ v 0/2^20) (x' : GExpr)
    (hx' : WgslReassoc.RA (polarizationHue j) x') (y : ℝ) (hy : x'.Computes w y) :
    |y-(polarizationHue j).exact v| ≤ x'.bound v E := by
  rw [← WgslReassoc.exact_RA v hx']
  exact error x' v w E hw y (polarization_safe j v E hI hI' hQ hU hpol
    (fun i hi => ⟨(abs_nonneg _).trans (hw i), hE i hi⟩) x' hx') hy

/-! ### Vectors by octave and slab -/

/-- Coordinate `j` of a vector whose largest coordinate lies in octave `k`:
slab `2j` (`2j+1`) holds coordinate `j` in `[2^k, 2^(k+1)]`
(`[-2^(k+1), -2^k]`); other slabs only bound it by `2^(k+1)`. -/
def slabAv (k : ℤ) (s j : ℕ) (e : ℚ) : Av :=
  if s = 2*j then Av.mk3 (pow2 k) (2*pow2 k) e
  else if s = 2*j+1 then Av.mk3 (-(2*pow2 k)) (-pow2 k) e else Av.mk3 (-(2*pow2 k)) (2*pow2 k) e

/-- The largest absolute coordinate. -/
def vmax (x : ℕ → ℝ) (o : ℕ) : ℝ := Max.max (Max.max |x o| |x (o+1)|) |x (o+2)|

/-- The slab conditions on coordinate `j` of `x`, offset `o`. -/
def InSlab (x : ℕ → ℝ) (o : ℕ) (a : ℝ) (s : ℕ) : Prop :=
  ∀ j, j < 3 → (s = 2*j → a ≤ x (o+j)) ∧ (s = 2*j+1 → x (o+j) ≤ -a)

lemma vec_slab (x : ℕ → ℝ) (o : ℕ) {a : ℝ} (ha : a ≤ vmax x o) : ∃ s < 6, InSlab x o a s := by
  have pick : ∀ j, j < 3 → a ≤ |x (o+j)| → ∃ s < 6, InSlab x o a s := by
    intro j hj h
    rcases le_total 0 (x (o+j)) with h0 | h0
    · refine ⟨2*j, by omega, fun j' _ => ⟨fun e => ?_, fun e => by omega⟩⟩
      obtain rfl : j' = j := by omega
      rwa [abs_of_nonneg h0] at h
    · refine ⟨2*j+1, by omega, fun j' _ => ⟨fun e => by omega, fun e => ?_⟩⟩
      obtain rfl : j' = j := by omega
      rw [abs_of_nonpos h0] at h; linarith
  unfold vmax at ha
  rcases le_total (Max.max |x o| |x (o+1)|) |x (o+2)| with h2 | h2
  · rw [max_eq_right h2] at ha; exact pick 2 (by norm_num) ha
  · rw [max_eq_left h2] at ha
    rcases le_total |x o| |x (o+1)| with h1 | h1
    · rw [max_eq_right h1] at ha; exact pick 1 (by norm_num) ha
    · rw [max_eq_left h1] at ha; exact pick 0 (by norm_num) (by simpa using ha)

lemma slabAv_H {k : ℤ} {s j : ℕ} {e : ℚ} {x E : ℝ} (hx : |x| ≤ 2*(2:ℝ)^k)
    (hp : s = 2*j → (2:ℝ)^k ≤ x) (hn : s = 2*j+1 → x ≤ -(2:ℝ)^k) (hE : 0 ≤ E) (he : E ≤ e) :
    (slabAv k s j e).H x E := by
  have hpa := pow2_eq k
  have hb := abs_le.mp hx
  unfold slabAv
  split_ifs with p q
  · exact ⟨by rw [hpa]; exact hp p, by push_cast; rw [hpa]; linarith, hE, he⟩
  · exact ⟨by push_cast; rw [hpa]; linarith, by push_cast; rw [hpa]; exact hn q, hE, he⟩
  · exact ⟨by push_cast; rw [hpa]; linarith, by push_cast; rw [hpa]; linarith, hE, he⟩

/-- A vector with `2^lo ≤ vmax ≤ 2^hi` lies in some octave `k` and slab `s`. -/
lemma vec_cover (x : ℕ → ℝ) (o : ℕ) {lo hi : ℤ} (h1 : (2:ℝ)^lo ≤ vmax x o)
    (h2 : vmax x o ≤ (2:ℝ)^hi) : ∃ k s, lo ≤ k ∧ k ≤ hi ∧ s < 6 ∧
      InSlab x o ((2:ℝ)^k) s ∧ ∀ j, j < 3 → |x (o+j)| ≤ 2*(2:ℝ)^k ∧ vmax x o ≤ 2*(2:ℝ)^k := by
  obtain ⟨k, hk1, hk2⟩ := octave (lt_of_lt_of_le (by positivity) h1)
  obtain ⟨kl, kh⟩ := octave_range hk1 hk2 h1 h2
  obtain ⟨s, hs, hsl⟩ := vec_slab x o hk1
  have h2k : vmax x o ≤ 2*(2:ℝ)^k := by
    rw [zpow_add_one₀ (by norm_num)] at hk2; linarith
  refine ⟨k, s, kl, kh, hs, hsl, fun j hj => ⟨?_, h2k⟩⟩
  refine le_trans ?_ h2k
  unfold vmax
  obtain _|_|_|j := j
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact le_max_right _ _
  · omega

/-! ### `spin_scale` -/

/-- Spin in octave `k` and slab `s` with errors up to `2⁻²⁰` of `2^(k+1)`;
any mass and mass error up to `2⁶⁴`. -/
def spinEnv (k : ℤ) (s : ℕ) : ℕ → Option Av := fun i =>
  if i < 3 then some (slabAv k s i (2*pow2 k/1048576))
  else if i = 3 then some (Av.mk3 (-18446744073709551616) 18446744073709551616 18446744073709551616)
  else none

set_option maxRecDepth 100000 in
theorem spinEnv_ok : ((List.range 41).all fun k => (List.range 6).all fun s =>
      (ev 0 (spinEnv ((k:ℤ)-20) s) (WgslAddKerr.spinScale 0)).isSome) = true := by
  decide +kernel

/-- Every reassociation of `add_kerr`'s spin scaling
`mass*spin/max(1, length(spin)/0.999)` satisfies `Safe` for every spin with `2⁻²⁰ ≤ max |spinᵢ| ≤ 2²⁰` and component errors up
to `2⁻²⁰ max |spinᵢ|`, and every mass and mass error up to `2⁶⁴`. A zero spin
is excluded: WGSL leaves `sqrt(0) = 1/inverseSqrt(0)` unspecified. -/
theorem spin_scale_safe (j : Fin 3) (v E : ℕ → ℝ) (h1 : (2:ℝ)^(-20:ℤ) ≤ vmax v 0)
    (h2 : vmax v 0 ≤ (2:ℝ)^(20:ℤ)) (hE : ∀ i, i < 3 → 0 ≤ E i ∧ E i ≤ vmax v 0/2^20)
    (hm : |v 3| ≤ 2^64) (hEm : 0 ≤ E 3 ∧ E 3 ≤ 2^64) :
    ∀ x', WgslReassoc.RA (WgslAddKerr.spinScale j) x' → x'.Safe v E := by
  obtain ⟨k, s, kl, kh, hs, hsl, hb⟩ := vec_cover v 0 h1 h2
  have hj := all_range (all_range spinEnv_ok (k := (k+20).toNat) (by omega)) hs
  rw [show (((k+20).toNat : ℕ) : ℤ)-20 = k by omega] at hj
  obtain ⟨R, hR⟩ := Option.isSome_iff_exists.mp hj
  -- Only the divisor carries conditions, and it does not depend on `j`.
  suffices h : ∀ x', WgslReassoc.RA (WgslAddKerr.spinScale 0) x' → x'.Safe v E by
    intro x' hx'
    simp only [WgslAddKerr.spinScale] at hx'
    cases hx' with
    | sum he => exact absurd he (by simp [WgslReassoc.IsSum])
    | div hN hD =>
      obtain ⟨-, sD, cD⟩ := h _ (WgslReassoc.RA.div (WgslReassoc.RA.refl _) hD)
      refine ⟨?_, sD, cD⟩
      cases hN with
      | sum he => exact absurd he (by simp [WgslReassoc.IsSum])
      | mul h3 hi => rw [h3.input_inv, hi.input_inv]; exact ⟨trivial, trivial⟩
  intro x' hx'
  refine (ev_robust_box 0 _ _ v E R ?_ ?_ hR x' hx').1
  rotate_left
  · intro i hi; simp only [spinEnv]
    split_ifs
    all_goals first | rfl | (exfalso; simp only [WgslLets.letBase] at hi; omega)
  intro i A hA
  unfold spinEnv at hA
  split_ifs at hA with p q <;> simp only [Option.some.injEq] at hA <;> subst hA
  · obtain ⟨hx, hv⟩ := hb i p
    obtain ⟨e0, e1⟩ := hE i p
    refine slabAv_H (by simpa using hx) (fun e => by simpa using (hsl i p).1 e)
      (fun e => by simpa using (hsl i p).2 e) e0 (e1.trans ?_)
    push_cast; rw [pow2_eq]; linarith
  · subst q
    have := abs_le.mp hm
    exact ⟨by push_cast; linarith, by push_cast; linarith, hEm.1, by push_cast; linarith⟩

/-! ### `spatial_unit` -/

/-- `spatial_unit` applied to inputs 100–102 (as in the translation fixture),
with the spatial metric `gamma` read from inputs 5–7, 9–11, 13–15. -/
def suVec (j : Fin 3) : GExpr := input (100+j)
def suScale : GExpr := max (max (abs (suVec 0)) (abs (suVec 1))) (abs (suVec 2))
def suScaled (j : Fin 3) : GExpr := div (suVec j) suScale
def suQ : GExpr := WgslScreen.dot3 suScaled (WgslScreen.gammaMul suScaled)
/-- The branch test and the scaled component, without the final
`inverseSqrt`, whose condition is proved from positive definiteness. -/
def suPre (i : Fin 3) : GExpr := lt (neg suScale) 0 (suScaled i) (suVec i)

def gIdx : List ℕ := [5,6,7,9,10,11,13,14,15]

/-- The vector in octave `k` and slab `s`; metric entries in `[-64, 64]` with
errors up to `2⁻¹⁴`. -/
def suEnv (k : ℤ) (s : ℕ) : ℕ → Option Av := fun i =>
  if 100 ≤ i ∧ i < 103 then some (slabAv k s (i-100) (2*pow2 k/1048576))
  else if i ∈ gIdx then some (Av.mk3 (-64) 64 (1/16384)) else none

def qOk : Option Av → Bool
  | some A => decide (A.b < 1/32)
  | none => false

set_option maxRecDepth 100000 in
theorem suEnv_ok : ((List.range 41).all fun k => (List.range 6).all fun s =>
    qOk (ev 0 (suEnv ((k:ℤ)-20) s) suQ) && (ev 0 (suEnv ((k:ℤ)-20) s) (suPre 0)).isSome) = true := by
  decide +kernel

lemma suQ_exact (v : ℕ → ℝ) : suQ.exact v = (∑ i : Fin 3, v (100+i)*
    ∑ j : Fin 3, v (4*(i.succ : ℕ)+j.succ)*v (100+j))/(vmax v 100)^2 := by
  have hm : suScale.exact v = vmax v 100 := rfl
  simp only [suQ, WgslScreen.dot3, WgslScreen.gammaMul, WgslScreen.sum3, WgslScreen.gamma,
    WgslScreen.g, suScaled, exact, hm, suVec, Fin.sum_univ_three]
  simp
  ring

/-- Every reassociation of `spatial_unit` satisfies `Safe`, so its running
bound holds, for every
vector with `2⁻²⁰ ≤ max |vᵢ| ≤ 2²⁰` and component errors up to
`2⁻²⁰ max |vᵢ|`, and every spatial metric with entries in `[-64, 64]`,
entry errors up to `2⁻¹⁴`, and quadratic form at least `max |vᵢ|²/32` at the
vector (for instance, smallest eigenvalue at least `1/32`). -/
theorem spatial_unit_safe (i : Fin 3) (v E : ℕ → ℝ) (h1 : (2:ℝ)^(-20:ℤ) ≤ vmax v 100)
    (h2 : vmax v 100 ≤ (2:ℝ)^(20:ℤ)) (hE : ∀ j, j < 3 → 0 ≤ E (100+j) ∧ E (100+j) ≤ vmax v 100/2^20)
    (hg : ∀ n ∈ gIdx, |v n| ≤ 64 ∧ 0 ≤ E n ∧ E n ≤ 1/16384)
    (hpd : (vmax v 100)^2/32 ≤ ∑ i : Fin 3, v (100+i)*∑ j : Fin 3, v (4*(i.succ : ℕ)+j.succ)*v (100+j)) :
    ∀ x', WgslReassoc.RA (WgslScreen.spatialUnit suVec i) x' → x'.Safe v E := by
  obtain ⟨k, s, kl, kh, hs, hsl, hb⟩ := vec_cover v 100 h1 h2
  have hok := all_range (all_range suEnv_ok (k := (k+20).toNat) (by omega)) hs
  rw [show (((k+20).toNat : ℕ) : ℤ)-20 = k by omega, Bool.and_eq_true] at hok
  obtain ⟨hq, hpre⟩ := hok
  have henv : EnvH (suEnv k s) v E := by
    intro n A hA
    unfold suEnv at hA
    split_ifs at hA with p q <;> simp only [Option.some.injEq] at hA <;> subst hA
    · obtain ⟨j, rfl⟩ : ∃ j, n = 100+j := ⟨n-100, by omega⟩
      have hj : j < 3 := by omega
      obtain ⟨hx, hv⟩ := hb j hj
      obtain ⟨e0, e1⟩ := hE j hj
      rw [show 100+j-100 = j by omega]
      refine slabAv_H hx (hsl j hj).1 (hsl j hj).2 e0 (e1.trans ?_)
      push_cast; rw [pow2_eq]; linarith
    · obtain ⟨hv, e0, e1⟩ := hg n q
      have := abs_le.mp hv
      exact ⟨by push_cast; linarith, by push_cast; linarith, e0, by push_cast; linarith⟩
  have hlow : EnvLow (suEnv k s) := by
    intro n hn; simp only [suEnv]
    split_ifs with p q
    all_goals first | rfl | (exfalso; simp_all [gIdx, WgslLets.letBase]; omega)
  obtain ⟨R, hR⟩ := Option.isSome_iff_exists.mp hpre
  have pre := ev_robust_box 0 _ _ v E R henv hlow hR
  have hm0 : 0 < vmax v 100 := lt_of_lt_of_le (by positivity) h1
  cases hQ : ev 0 (suEnv k s) suQ with
  | none => rw [hQ] at hq; simp [qOk] at hq
  | some A =>
    rw [hQ] at hq
    have hAb : (A.b : ℝ) < 1/32 := by
      have h' : A.b < 1/32 := of_decide_eq_true hq
      have := (Rat.cast_lt (K := ℝ)).mpr h'; push_cast at this; linarith
    have qR := ev_robust_box 0 _ _ v E A henv hlow hQ
    have hqe : 1/32 ≤ suQ.exact v := by
      rw [suQ_exact, le_div_iff₀ (by positivity)]; linarith
    intro x' hx'
    simp only [WgslScreen.spatialUnit] at hx'
    cases hx' with
    | sum he => exact absurd he (by simp [WgslReassoc.IsSum])
    | lt t hc' ha' hb' =>
      rename_i c' a' b'
      -- The test and the scaled components' conditions come from `suPre 0`:
      -- they are those of `scale`, the same for every `i`.
      have hpre' := fun s' (hs' : WgslReassoc.RA (suScaled 0) s') =>
        (pre _ (WgslReassoc.RA.lt 0 hc' hs' (WgslReassoc.RA.refl (suVec 0)))).1
      obtain ⟨p1, -, p4⟩ := hpre' _ (WgslReassoc.RA.refl _)
      have hneg : c'.exact v < ((0:ℚ):ℝ) := by
        rw [WgslReassoc.exact_RA v hc']; show -vmax v 100 < _; push_cast; linarith
      refine ⟨p1, ?_, p4⟩
      simp only [hneg, ↓reduceIte]
      cases ha' with
      | sum he => exact absurd he (by simp [WgslReassoc.IsSum])
      | mul hs hinv =>
        cases hs with
        | sum he => exact absurd he (by simp [WgslReassoc.IsSum])
        | div hv hsc =>
          have h2 := (hpre' _ (WgslReassoc.RA.div (WgslReassoc.RA.refl (suVec 0)) hsc)).2.1
          simp only [hneg, ↓reduceIte] at h2
          obtain ⟨-, s2, c2⟩ := h2
          refine ⟨⟨by rw [hv.input_inv]; trivial, s2, c2⟩, ?_⟩
          cases hinv with
          | sum he => exact absurd he (by simp [WgslReassoc.IsSum])
          | invsqrt hm =>
            cases hm with
            | sum he => exact absurd he (by simp [WgslReassoc.IsSum])
            | max hq' hc'' =>
              rename_i q' cc
              change WgslReassoc.RA suQ q' at hq'
              rw [hc''.const_inv]
              obtain ⟨sq, -, -, qb0, qb⟩ := qR _ hq'
              refine ⟨⟨sq, trivial⟩, ?_⟩
              show max (bound v E q') 0 < max (q'.exact v) _
              rw [max_eq_left qb0, WgslReassoc.exact_RA v hq']
              exact lt_of_lt_of_le (by linarith) (le_max_left _ _)

end BlackHole.WgslSafeDomains
