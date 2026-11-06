module

public import BlackHole.WgslDomain
public import BlackHole.WgslSafe
public import BlackHole.WgslAddKerr
public import Mathlib.Data.Int.Log

/-! Box covers for the closed-form domains on which the `Safe` conditions of
the branching WGSL kernels hold (obligation F2): binary octaves and slabs of
vectors.

Each domain theorem (`WgslSafeDomains`, `WgslSafeSpin`, `WgslSafeSpatial`)
covers its domain by finitely many boxes, runs the checked interval evaluator
`WgslDomain.ev` on every box in the kernel, and applies its soundness theorem
for every reassociation (`WgslDomain.ev_robust`). The domains stay a fixed
distance from the branch thresholds and singular points, where no all-input
bound exists (`WgslSafe.bound_ge_half_variation`). -/

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

end BlackHole.WgslSafeDomains
