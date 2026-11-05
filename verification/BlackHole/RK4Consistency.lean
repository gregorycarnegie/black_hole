module

public import BlackHole.TaylorLine
public import BlackHole.KerrSmoothness
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Fourth-order local consistency of classical RK4 for nonlinear fields (N1).

`Small k F` says `‖F h‖ ≤ C |h|^k` for all small `h`. The proof expands each
RK4 stage with the local Taylor theorem and compares the step with the
explicit polynomial `y + q(h)`; the exact flow is compared with the same
polynomial by Gronwall's inequality. -/

@[expose] public section
noncomputable section

set_option linter.unusedSectionVars false

open Set Finset Nat

namespace BlackHole.RK4Consistency

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Orders of smallness -/

/-- `F h = O(h^k)` as `h → 0`, with explicit constants. -/
def Small (k : ℕ) {G : Type*} [NormedAddCommGroup G] (F : ℝ → G) : Prop :=
  ∃ C δ : ℝ, 0 < δ ∧ ∀ h, |h| ≤ δ → ‖F h‖ ≤ C*|h|^k

section Small

variable {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H]
  [NormedSpace ℝ H]

lemma Small.congr {k : ℕ} {F F' : ℝ → G} (hF : Small k F) (h : ∀ x, F x = F' x) : Small k F' := by
  obtain ⟨C, δ, hδ, hb⟩ := hF
  exact ⟨C, δ, hδ, fun x hx => by rw [← h x]; exact hb x hx⟩

lemma small_zero (k : ℕ) : Small k (fun _ : ℝ => (0 : G)) :=
  ⟨0, 1, one_pos, fun h _ => by simp⟩

lemma Small.add {k : ℕ} {F F' : ℝ → G} (hF : Small k F) (hF' : Small k F') :
    Small k (fun h => F h+F' h) := by
  obtain ⟨C, δ, hδ, hb⟩ := hF
  obtain ⟨C', δ', hδ', hb'⟩ := hF'
  refine ⟨C+C', min δ δ', lt_min hδ hδ', fun h hh => ?_⟩
  have h1 := hb h (le_trans hh (min_le_left _ _))
  have h2 := hb' h (le_trans hh (min_le_right _ _))
  calc ‖F h+F' h‖ ≤ ‖F h‖+‖F' h‖ := norm_add_le _ _
    _ ≤ C*|h|^k+C'*|h|^k := add_le_add h1 h2
    _ = _ := by ring

lemma Small.neg {k : ℕ} {F : ℝ → G} (hF : Small k F) : Small k (fun h => -F h) := by
  obtain ⟨C, δ, hδ, hb⟩ := hF
  exact ⟨C, δ, hδ, fun h hh => by rw [norm_neg]; exact hb h hh⟩

lemma Small.sub {k : ℕ} {F F' : ℝ → G} (hF : Small k F) (hF' : Small k F') :
    Small k (fun h => F h-F' h) :=
  (hF.add hF'.neg).congr (fun h => by abel)

lemma Small.mono {j k : ℕ} {F : ℝ → G} (hF : Small k F) (hjk : j ≤ k) : Small j F := by
  obtain ⟨C, δ, hδ, hb⟩ := hF
  refine ⟨max C 0, min δ 1, lt_min hδ one_pos, fun h hh => ?_⟩
  have h1 : |h| ≤ 1 := le_trans hh (min_le_right _ _)
  have h2 : |h|^k ≤ |h|^j := pow_le_pow_of_le_one (abs_nonneg _) h1 hjk
  calc ‖F h‖ ≤ C*|h|^k := hb h (le_trans hh (min_le_left _ _))
    _ ≤ max C 0*|h|^k := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0*|h|^j := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)

lemma Small.smul {j k : ℕ} {p : ℝ → ℝ} {F : ℝ → G} (hp : Small j p) (hF : Small k F) :
    Small (j+k) (fun h => p h • F h) := by
  obtain ⟨C, δ, hδ, hb⟩ := hp
  obtain ⟨C', δ', hδ', hb'⟩ := hF
  refine ⟨C*C', min δ δ', lt_min hδ hδ', fun h hh => ?_⟩
  have h1 := hb h (le_trans hh (min_le_left _ _))
  have h2 := hb' h (le_trans hh (min_le_right _ _))
  rw [norm_smul, pow_add]
  have hC : 0 ≤ C := by
    have := le_trans (norm_nonneg _) (hb 0 (by simp [hδ.le]))
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj; simpa using this
    · have : ‖p δ‖ ≤ C*|δ|^j := hb δ (by rw [abs_of_pos hδ])
      have hpos : 0 < |δ|^j := by positivity
      by_contra hneg; push Not at hneg
      have : C*|δ|^j < 0 := mul_neg_of_neg_of_pos hneg hpos
      linarith [norm_nonneg (p δ)]
  calc ‖p h‖*‖F h‖ ≤ (C*|h|^j)*(C'*|h|^k) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Scalar monomials. -/
lemma small_monomial (a : ℝ) (j : ℕ) : Small j (fun h : ℝ => a*h^j) :=
  ⟨|a|, 1, one_pos, fun h _ => by rw [Real.norm_eq_abs, abs_mul, abs_pow]⟩

lemma small_const (c : G) : Small 0 (fun _ : ℝ => c) :=
  ⟨‖c‖, 1, one_pos, fun h _ => by simp⟩

lemma Small.clm {k : ℕ} {F : ℝ → G} (L : G →L[ℝ] H) (hF : Small k F) :
    Small k (fun h => L (F h)) := by
  obtain ⟨C, δ, hδ, hb⟩ := hF
  refine ⟨‖L‖*C, δ, hδ, fun h hh => ?_⟩
  calc ‖L (F h)‖ ≤ ‖L‖*‖F h‖ := L.le_opNorm _
    _ ≤ ‖L‖*(C*|h|^k) := mul_le_mul_of_nonneg_left (hb h hh) (norm_nonneg _)
    _ = _ := by ring

lemma Small.bilin {j k : ℕ} {F F' : ℝ → G} (B : G →L[ℝ] G →L[ℝ] H) (hF : Small j F)
    (hF' : Small k F') : Small (j+k) (fun h => B (F h) (F' h)) := by
  obtain ⟨C, δ, hδ, hb⟩ := hF
  obtain ⟨C', δ', hδ', hb'⟩ := hF'
  refine ⟨‖B‖*(max C 0*max C' 0), min δ δ', lt_min hδ hδ', fun h hh => ?_⟩
  have h1 := le_trans (hb h (le_trans hh (min_le_left _ _)))
    (mul_le_mul_of_nonneg_right (le_max_left C 0) (by positivity))
  have h2 := le_trans (hb' h (le_trans hh (min_le_right _ _)))
    (mul_le_mul_of_nonneg_right (le_max_left C' 0) (by positivity))
  calc ‖B (F h) (F' h)‖ ≤ ‖B‖*‖F h‖*‖F' h‖ := B.le_opNorm₂ _ _
    _ ≤ ‖B‖*(max C 0*|h|^j)*(max C' 0*|h|^k) := by gcongr
    _ = _ := by rw [pow_add]; ring

/-- A map Lipschitz near `c`, evaluated along `c + d h` with `d h = O(h)`. -/
lemma Small.lipschitz {Φ : G → H} {c : G} {K : NNReal} {s : Set G} (hs : s ∈ nhds c)
    (hΦ : LipschitzOnWith K Φ s) {d : ℝ → G} (hd : Small 1 d) :
    Small 1 (fun h => Φ (c+d h)-Φ c) := by
  obtain ⟨C, δ, hδ, hb⟩ := hd
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  set C₀ := max C 1
  refine ⟨K*C₀, min δ (ε/(2*C₀)), lt_min hδ (by positivity), fun h hh => ?_⟩
  have hhδ := le_trans hh (min_le_left _ _)
  have hdh : ‖d h‖ ≤ C₀*|h| := le_trans (by simpa using hb h hhδ)
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  have hmem : c+d h ∈ s := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    have : C₀*|h| ≤ ε/2 := by
      have h1 := le_trans hh (min_le_right _ _)
      have hC₀ : 0 < C₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
      calc C₀*|h| ≤ C₀*(ε/(2*C₀)) := mul_le_mul_of_nonneg_left h1 hC₀.le
        _ = ε/2 := by field_simp
    linarith
  have hc : c ∈ s := mem_of_mem_nhds hs
  calc ‖Φ (c+d h)-Φ c‖ ≤ K*‖c+d h-c‖ := hΦ.norm_sub_le hmem hc
    _ = K*‖d h‖ := by rw [add_sub_cancel_left]
    _ ≤ K*(C₀*|h|) := mul_le_mul_of_nonneg_left hdh (by positivity)
    _ = _ := by ring

end Small

/-! ### Local Taylor expansion -/

/-- Derivatives along a line inside an open set where `f` is smooth. -/
theorem line_iteratedDeriv_on {n : ℕ} {f : E → E} {B : Set E} (hB : IsOpen B)
    (hf : ContDiffOn ℝ n f B) (y w : E) {k : ℕ} (hk : k ≤ n) (t : ℝ) (ht : y+t • w ∈ B) :
    iteratedDeriv k (fun s : ℝ => f (y+s • w)) t =
      iteratedFDeriv ℝ k f (y+t • w) (fun _ => w) := by
  set L : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) w
  have hL : ∀ s : ℝ, L s = s • w := fun s => by simp [L]
  set B' : Set E := (fun z => y+z) ⁻¹' B
  have hB' : IsOpen B' := hB.preimage (by fun_prop)
  have hf' : ContDiffOn ℝ n (fun z : E => f (y+z)) B' :=
    hf.comp (by fun_prop) (fun z hz => hz)
  set S : Set ℝ := L ⁻¹' B'
  have hS : IsOpen S := hB'.preimage L.continuous
  have htS : t ∈ S := by simp [S, B', hL, ht]
  have hcomp : (fun s : ℝ => f (y+s • w)) = (fun z : E => f (y+z)) ∘ L := by
    funext s; simp [hL]
  rw [hcomp, iteratedDeriv_eq_iteratedFDeriv, ← iteratedFDerivWithin_of_isOpen k hS htS,
    ContinuousLinearMap.iteratedFDerivWithin_comp_right L hf' hB'.uniqueDiffOn hS.uniqueDiffOn
      htS (by exact_mod_cast hk),
    iteratedFDerivWithin_of_isOpen k hB' htS]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hL, one_smul]
  rw [iteratedFDeriv_comp_add_left]

/-- Taylor's theorem along a segment inside an open set. -/
theorem taylor_line_on {f : E → E} {B : Set E} (hB : IsOpen B) (hf : ContDiffOn ℝ 4 f B)
    (y w : E) (hseg : ∀ t ∈ Icc (0:ℝ) 1, y+t • w ∈ B) (M : ℝ)
    (hM : ∀ t ∈ Icc (0:ℝ) 1, ‖iteratedFDeriv ℝ 4 f (y+t • w)‖ ≤ M) :
    ‖f (y+w)-∑ k ∈ range 4, ((k ! : ℝ)⁻¹) • iteratedFDeriv ℝ k f y (fun _ => w)‖ ≤
      M*‖w‖^4/6 := by
  set g : ℝ → E := fun s => f (y+s • w)
  have hcont : Continuous (fun s : ℝ => y+s • w) := by fun_prop
  have hg : ContDiffOn ℝ 4 g (Icc 0 1) := hf.comp (by fun_prop) (fun t ht => hseg t ht)
  have huniq : UniqueDiffOn ℝ (Icc (0:ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have hgat : ∀ t ∈ Icc (0:ℝ) 1, ContDiffAt ℝ 4 g t := by
    intro t ht
    have h1 : ContDiffAt ℝ 4 f (y+t • w) := hf.contDiffAt (hB.mem_nhds (hseg t ht))
    exact h1.comp t (by fun_prop)
  have hderiv : ∀ k ≤ 4, ∀ t ∈ Icc (0:ℝ) 1,
      iteratedDerivWithin k g (Icc 0 1) t = iteratedFDeriv ℝ k f (y+t • w) (fun _ => w) := by
    intro k hk t ht
    rw [iteratedDerivWithin_eq_iteratedDeriv huniq ((hgat t ht).of_le (by exact_mod_cast hk)) ht]
    exact line_iteratedDeriv_on hB hf y w hk t (hseg t ht)
  have hbound : ∀ t ∈ Icc (0:ℝ) 1, ‖iteratedDerivWithin (3+1) g (Icc 0 1) t‖ ≤ M*‖w‖^4 := by
    intro t ht
    rw [hderiv 4 le_rfl t ht]
    calc ‖iteratedFDeriv ℝ 4 f (y+t • w) (fun _ => w)‖
        ≤ ‖iteratedFDeriv ℝ 4 f (y+t • w)‖*∏ _i : Fin 4, ‖w‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ M*‖w‖^4 := by
          rw [prod_const, Finset.card_univ, Fintype.card_fin]
          exact mul_le_mul_of_nonneg_right (hM t ht) (by positivity)
  have h := taylor_mean_remainder_bound (f := g) (n := 3) (a := 0) (b := 1) (x := 1)
    zero_le_one hg (right_mem_Icc.mpr zero_le_one) hbound
  rw [taylor_within_apply] at h
  have hsum : ∑ k ∈ range (3+1), ((k ! : ℝ)⁻¹*(1-0)^k) • iteratedDerivWithin k g (Icc 0 1) 0 =
      ∑ k ∈ range 4, ((k ! : ℝ)⁻¹) • iteratedFDeriv ℝ k f y (fun _ => w) := by
    apply sum_congr rfl
    intro k hk
    have hk4 : k ≤ 4 := by simp at hk; omega
    rw [hderiv k hk4 0 (left_mem_Icc.mpr zero_le_one)]
    simp
  rw [hsum] at h
  have hg1 : g 1 = f (y+w) := by simp [g]
  rw [hg1] at h
  calc _ ≤ M*‖w‖^4*(1-0)^(3+1)/3 ! := h
    _ = M*‖w‖^4/6 := by norm_num [Nat.factorial]

/-! ### The cubic Taylor polynomial and the stage lemma -/

section Jet

variable (f : E → E) (y : E)

/-- `f(y)`, `Df(y)`, `D²f(y)` and the cubic `w ↦ D³f(y)(w,w,w)`. -/
def f0 : E := f y
def L1 : E →L[ℝ] E := fderiv ℝ f y
def D2 : E →L[ℝ] E →L[ℝ] E := fderiv ℝ (fderiv ℝ f) y
def T3 (w : E) : E := iteratedFDeriv ℝ 3 f y (fun _ => w)

/-- The cubic Taylor polynomial of `f` at `y`. -/
def P (w : E) : E := f0 f y+L1 f y w+(1/2:ℝ) • D2 f y w w+(1/6:ℝ) • T3 f y w

lemma taylor_sum_eq (w : E) :
    ∑ k ∈ range 4, ((k ! : ℝ)⁻¹) • iteratedFDeriv ℝ k f y (fun _ => w) = P f y w := by
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.factorial, Nat.cast_one, inv_one,
    one_smul, iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply, iteratedFDeriv_two_apply, P,
    f0, L1, D2, T3]
  push_cast
  norm_num

lemma T3_smul (c : ℝ) (w : E) : T3 f y (c • w) = c^3 • T3 f y w := by
  unfold T3
  have := (iteratedFDeriv ℝ 3 f y).map_smul_univ (fun _ => c) (fun _ => w)
  simp only [prod_const, Finset.card_univ, Fintype.card_fin] at this
  exact this

lemma T3_contDiff : ContDiff ℝ 1 (T3 f y) := by
  unfold T3
  exact (iteratedFDeriv ℝ 3 f y).contDiff.comp (contDiff_pi.mpr fun _ => contDiff_id)

/-- The local Taylor theorem: `f(y + a h) - P(a h) = O(h⁴)` when `a h = O(h)`. -/
theorem taylor_small {U : Set E} (hU : IsOpen U) (hyU : y ∈ U) (hf : ContDiffOn ℝ 4 f U)
    {a : ℝ → E} (ha : Small 1 a) : Small 4 (fun h => f (y+a h)-P f y (a h)) := by
  -- Continuity of the fourth derivative bounds it near y.
  have hcont : ContinuousOn (iteratedFDeriv ℝ 4 f) U := by
    have h1 := hf.continuousOn_iteratedFDerivWithin (m := 4) le_rfl hU.uniqueDiffOn
    exact h1.congr (fun x hx => (iteratedFDerivWithin_of_isOpen 4 hU hx).symm)
  have hcy : ContinuousAt (iteratedFDeriv ℝ 4 f) y := hcont.continuousAt (hU.mem_nhds hyU)
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp hU y hyU
  obtain ⟨σ, hσ, hσb⟩ := Metric.continuousAt_iff.mp hcy 1 one_pos
  set r := min ρ σ
  have hr : 0 < r := lt_min hρ hσ
  set M := ‖iteratedFDeriv ℝ 4 f y‖+1
  obtain ⟨C, δ, hδ, hb⟩ := ha
  set C₀ := max C 1
  have hC₀ : 0 < C₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨M/6*C₀^4, min δ (r/(2*C₀)), lt_min hδ (by positivity), fun h hh => ?_⟩
  have hah : ‖a h‖ ≤ C₀*|h| := le_trans (by simpa using hb h (le_trans hh (min_le_left _ _)))
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  have hsmall : ‖a h‖ < r := by
    have : C₀*|h| ≤ r/2 := by
      calc C₀*|h| ≤ C₀*(r/(2*C₀)) := mul_le_mul_of_nonneg_left (le_trans hh (min_le_right _ _)) hC₀.le
        _ = r/2 := by field_simp
    linarith
  have hseg : ∀ t ∈ Icc (0:ℝ) 1, dist (y+t • a h) y < r := by
    intro t ht
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    calc t*‖a h‖ ≤ 1*‖a h‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
      _ < r := by rw [one_mul]; exact hsmall
  have hT := taylor_line_on hU hf y (a h)
    (fun t ht => hρU (lt_of_lt_of_le (hseg t ht) (min_le_left _ _))) M
    (fun t ht => by
      have h1 := hσb (lt_of_lt_of_le (hseg t ht) (min_le_right _ _))
      rw [dist_eq_norm] at h1
      have := norm_sub_norm_le (iteratedFDeriv ℝ 4 f (y+t • a h)) (iteratedFDeriv ℝ 4 f y)
      simp only [M]; linarith)
  rw [taylor_sum_eq] at hT
  calc ‖f (y+a h)-P f y (a h)‖ ≤ M*‖a h‖^4/6 := hT
    _ ≤ M*(C₀*|h|)^4/6 := by gcongr
    _ = M/6*C₀^4*|h|^4 := by ring

/-- One RK4 stage. If `v h = c + h e + h² g + O(h³)` then
    `f(y + αh v h)` has the explicit expansion below up to `O(h⁴)`. -/
theorem stage {U : Set E} (hU : IsOpen U) (hyU : y ∈ U) (hf : ContDiffOn ℝ 4 f U)
    (α : ℝ) (v : ℝ → E) (c e g : E) (hv : Small 3 (fun h => v h-(c+h • e+h^2 • g))) :
    Small 4 (fun h => f (y+(α*h) • v h)-(f0 f y+(α*h) • L1 f y c+
      h^2 • (α • L1 f y e+(α^2/2) • D2 f y c c)+
      h^3 • (α • L1 f y g+(α^2/2) • (D2 f y c e+D2 f y e c)+(α^3/6) • T3 f y c))) := by
  -- v = c + d with d = O(h), and r = d - h e = O(h²).
  have hd : Small 1 (fun h => v h-c) := by
    have h1 : Small 1 (fun h => h • e+h^2 • g) :=
      ((small_monomial 1 1).smul (small_const e)).add
        (((small_monomial 1 2).smul (small_const g)).mono (by norm_num)) |>.congr
          (fun h => by simp)
    exact ((hv.mono (by norm_num)).add h1).congr (fun h => by abel)
  have hr : Small 2 (fun h => v h-c-h • e) := by
    have h1 : Small 2 (fun h => h^2 • g) :=
      ((small_monomial 1 2).smul (small_const g)).congr (fun h => by simp)
    exact ((hv.mono (by norm_num)).add h1).congr (fun h => by abel)
  have hv0 : Small 0 v := ((hd.mono (by norm_num)).add (small_const c)).congr (fun h => by abel)
  have ha : Small 1 (fun h => (α*h) • v h) :=
    ((small_monomial α 1).smul hv0).congr (fun h => by simp)
  have hT := taylor_small f y hU hyU hf ha
  -- The three polynomial pieces.
  have hLin : Small 4 (fun h => (α*h) • (L1 f y (v h-(c+h • e+h^2 • g)))) :=
    ((small_monomial α 1).smul (hv.clm (L1 f y))).congr (fun h => by simp)
  have hQuad : Small 4 (fun h => (α^2/2*h^2) •
      (D2 f y (v h-c) (v h-c)+D2 f y c (v h-c-h • e)+D2 f y (v h-c-h • e) c)) := by
    have h1 : Small 2 (fun h => D2 f y (v h-c) (v h-c)) := hd.bilin (D2 f y) hd
    have h2 : Small 2 (fun h => D2 f y c (v h-c-h • e)) :=
      ((small_const c).bilin (D2 f y) hr).congr (fun h => rfl)
    have h3 : Small 2 (fun h => D2 f y (v h-c-h • e) c) :=
      (hr.bilin (D2 f y) (small_const c)).congr (fun h => rfl)
    exact ((small_monomial (α^2/2) 2).smul ((h1.add h2).add h3)).congr (fun h => rfl)
  have hCub : Small 4 (fun h => (α^3/6*h^3) • (T3 f y (v h)-T3 f y c)) := by
    obtain ⟨K, s, hs, hlip⟩ := ((T3_contDiff f y).contDiffAt (x := c)).exists_lipschitzOnWith
    have h1 : Small 1 (fun h => T3 f y (c+(v h-c))-T3 f y c) := Small.lipschitz hs hlip hd
    exact ((small_monomial (α^3/6) 3).smul h1).congr (fun h => by simp)
  refine (((hT.add hLin).add hQuad).add hCub).congr (fun h => ?_)
  -- Algebra: P(αh v) minus the target equals the three pieces.
  simp only [P, map_add, map_sub, map_smul, sub_apply, FunLike.coe_smul, Pi.smul_apply, T3_smul]
  module

/-- `stage` with the argument and the coefficients given by name. -/
theorem stage' {U : Set E} (hU : IsOpen U) (hyU : y ∈ U) (hf : ContDiffOn ℝ 4 f U)
    (α : ℝ) (v : ℝ → E) (c e g : E) (hv : Small 3 (fun h => v h-(c+h • e+h^2 • g)))
    {k : ℝ → E} (hk : ∀ h, k h = f (y+(α*h) • v h)) :
    Small 4 (fun h => k h-(f0 f y+h • (α • L1 f y c)+
      h^2 • (α • L1 f y e+(α^2/2) • D2 f y c c)+
      h^3 • (α • L1 f y g+(α^2/2) • (D2 f y c e+D2 f y e c)+(α^3/6) • T3 f y c))) :=
  (stage f y hU hyU hf α v c e g hv).congr (fun h => by rw [hk]; module)

end Jet

/-- Dropping the cubic term of an `O(h⁴)` expansion. -/
lemma drop_cubic {k : ℝ → E} {c e g r : E}
    (hk : Small 4 (fun h => k h-(c+h • e+h^2 • g+h^3 • r))) :
    Small 3 (fun h => k h-(c+h • e+h^2 • g)) :=
  ((hk.mono (by norm_num)).add ((small_monomial 1 3).smul (small_const r))).congr
    (fun h => by simp only [one_mul]; abel)

/-! ### The RK4 step -/

section RK4

variable (f : E → E) (y : E)

def k2 (h : ℝ) : E := f (y+(h/2) • f y)
def k3 (h : ℝ) : E := f (y+(h/2) • k2 f y h)
def k4 (h : ℝ) : E := f (y+h • k3 f y h)

/-- One classical RK4 step of size `h` for `y' = f(y)`. -/
def rk4Step (h : ℝ) : E :=
  y+(h/6) • (f y+(2:ℝ) • k2 f y h+(2:ℝ) • k3 f y h+k4 f y h)

/-- Coefficients of the exact flow, `y(h) = y + h F + h² q₂ + h³ q₃ + h⁴ q₄ + O(h⁵)`. -/
def q2 : E := (1/2:ℝ) • L1 f y (f0 f y)
def q3 : E := (1/3:ℝ) • (L1 f y (q2 f y)+(1/2:ℝ) • D2 f y (f0 f y) (f0 f y))
def q4 : E := (1/4:ℝ) • (L1 f y (q3 f y)+
  (1/2:ℝ) • (D2 f y (f0 f y) (q2 f y)+D2 f y (q2 f y) (f0 f y))+(1/6:ℝ) • T3 f y (f0 f y))

/-- `(y(h) - y)/h` to `O(h⁴)`. -/
def vq (h : ℝ) : E := f0 f y+h • q2 f y+h^2 • q3 f y+h^3 • q4 f y

/-- The RK4 step agrees with the quartic `y + h vq(h)` to `O(h⁵)`. -/
theorem rk4_expansion {U : Set E} (hU : IsOpen U) (hyU : y ∈ U) (hf : ContDiffOn ℝ 4 f U) :
    Small 5 (fun h => rk4Step f y h-(y+h • vq f y h)) := by
  have hK2 := stage' f y hU hyU hf (1/2) (fun _ => f0 f y) (f0 f y) 0 0
    ((small_zero 3).congr (fun h => by simp)) (k := k2 f y)
    (fun h => by rw [k2, f0, show h/2 = 1/2*h by ring])
  have hK3 := stage' f y hU hyU hf (1/2) (k2 f y) _ _ _ (drop_cubic hK2) (k := k3 f y)
    (fun h => by rw [k3, show h/2 = 1/2*h by ring])
  have hK4 := stage' f y hU hyU hf 1 (k3 f y) _ _ _ (drop_cubic hK3) (k := k4 f y)
    (fun h => by rw [k4, one_mul])
  refine ((small_monomial (1/6) 1).smul
    ((((small_const (2:ℝ)).smul hK2).add ((small_const (2:ℝ)).smul hK3)).add hK4)).congr
    (fun h => ?_)
  simp only [rk4Step, vq, q2, q3, q4, f0, map_add, map_smul, map_zero, FunLike.coe_smul,
    Pi.smul_apply, zero_apply, smul_zero, add_zero, zero_add]
  module

/-- The quartic nearly solves the ODE: its derivative misses `f` by `O(t⁴)`. -/
theorem flow_residual {U : Set E} (hU : IsOpen U) (hyU : y ∈ U) (hf : ContDiffOn ℝ 4 f U) :
    Small 4 (fun t => f (y+t • vq f y t)-
      (f0 f y+(2*t) • q2 f y+(3*t^2) • q3 f y+(4*t^3) • q4 f y)) := by
  have hv : Small 3 (fun t => vq f y t-(f0 f y+t • q2 f y+t^2 • q3 f y)) :=
    ((small_monomial 1 3).smul (small_const (q4 f y))).congr
      (fun t => by simp only [vq, one_mul]; abel)
  refine (stage' f y hU hyU hf 1 (vq f y) _ _ _ hv (k := fun t => f (y+t • vq f y t))
    (fun t => by rw [one_mul])).congr (fun t => ?_)
  simp only [q2, q3, q4, map_add, map_smul, FunLike.coe_smul, Pi.smul_apply]
  module

/-! ### The exact flow -/

lemma gronwallBound_le {K ε x : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    gronwallBound 0 K ε x ≤ ε*x*Real.exp (K*x) := by
  by_cases hK0 : K = 0
  · subst hK0; simp [gronwallBound_K0]
  · have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hK0)
    rw [gronwallBound_of_K_ne_0 hK0]
    simp only [zero_mul, zero_add]
    have hE := Real.exp_pos (K*x)
    have h1 := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-(K*x))) hE.le
    have h2 : Real.exp (K*x)*Real.exp (-(K*x)) = 1 := by rw [← Real.exp_add]; simp
    have h3 : Real.exp (K*x)-1 ≤ K*x*Real.exp (K*x) := by nlinarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hKpos]
    nlinarith [mul_le_mul_of_nonneg_left h3 hε]

/-- The exact solution agrees with the same quartic to `O(h⁵)` (Gronwall). -/
theorem flow_close {U : Set E} (hU : IsOpen U) (hyU : y ∈ U) (hf : ContDiffOn ℝ 4 f U)
    {sol : ℝ → E} {ε : ℝ} (hε : 0 < ε) (h0 : sol 0 = y)
    (hsol : ∀ t ∈ Ioo (-ε) ε, HasDerivAt sol (f (sol t)) t) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ h ∈ Icc 0 δ, ‖sol h-(y+h • vq f y h)‖ ≤ C*h^5 := by
  have hfy : ContDiffAt ℝ 1 f y := (hf.contDiffAt (hU.mem_nhds hyU)).of_le (by norm_num)
  obtain ⟨K, s, hs, hlip⟩ := hfy.exists_lipschitzOnWith
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨C, δ1, hδ1, hb⟩ := flow_residual f y hU hyU hf
  let g : ℝ → E := fun t => y+t • vq f y t
  let g' : ℝ → E := fun t => f0 f y+(2*t) • q2 f y+(3*t^2) • q3 f y+(4*t^3) • q4 f y
  have hg_eq : g = fun t => y+t • f0 f y+t^2 • q2 f y+t^3 • q3 f y+t^4 • q4 f y := by
    funext t; simp only [g, vq]; module
  have hgd : ∀ t, HasDerivAt g (g' t) t := by
    intro t
    rw [hg_eq]
    have := (((((hasDerivAt_id t).smul_const (f0 f y)).const_add y).add
      ((hasDerivAt_pow 2 t).smul_const (q2 f y))).add
      ((hasDerivAt_pow 3 t).smul_const (q3 f y))).add
      ((hasDerivAt_pow 4 t).smul_const (q4 f y))
    convert this using 1
    · funext x; simp only [Pi.add_apply, id]
    · simp only [g', Nat.cast_ofNat, one_smul, show (2:ℕ)-1 = 1 from rfl,
        show (3:ℕ)-1 = 2 from rfl, show (4:ℕ)-1 = 3 from rfl, pow_one]
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun t => (hgd t).continuousAt
  have hsc : ContinuousAt sol 0 := (hsol 0 ⟨by linarith, hε⟩).continuousAt
  obtain ⟨η1, hη1, hsb⟩ := Metric.continuousAt_iff.mp hsc ρ hρ
  obtain ⟨η2, hη2, hgb⟩ := Metric.continuousAt_iff.mp hgc.continuousAt ρ hρ
  have hg0 : g 0 = y := by simp [g]
  set δ := min (min (min δ1 (η1/2)) (min (η2/2) (ε/2))) 1 with hδdef
  have hδ : 0 < δ := by positivity
  refine ⟨max C 0*Real.exp K, δ, hδ, fun h hh => ?_⟩
  have hδ1' : δ ≤ δ1 :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδη1 : δ ≤ η1/2 :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδη2 : δ ≤ η2/2 :=
    le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδε : δ ≤ ε/2 :=
    le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hδ1le : δ ≤ 1 := min_le_right _ _
  have hIco : ∀ t ∈ Ico 0 h, 0 ≤ t ∧ t ≤ δ := fun t ht => ⟨ht.1, le_trans ht.2.le hh.2⟩
  have hmain := dist_le_of_approx_trajectories_ODE_of_mem (v := fun _ => f)
    (s := fun _ => Metric.ball y ρ) (K := K) (f := sol) (g := g) (f' := fun t => f (sol t))
    (g' := g') (a := 0) (b := h) (εf := 0) (εg := max C 0*h^4) (δ := 0)
    (fun _ _ => hlip.mono hball)
    (fun t ht => (hsol t ⟨by linarith [ht.1], by linarith [ht.2, hh.2]⟩).continuousAt.continuousWithinAt)
    (fun t ht => (hsol t ⟨by linarith [ht.1], by linarith [ht.2, hh.2]⟩).hasDerivWithinAt)
    (fun _ _ => by simp)
    (fun t ht => by
      obtain ⟨h1, h2⟩ := hIco t ht
      have := hsb (x := t) (by rw [Real.dist_eq, sub_zero, abs_of_nonneg h1]; linarith)
      rwa [h0] at this)
    hgc.continuousOn
    (fun t _ => (hgd t).hasDerivWithinAt)
    (fun t ht => by
      obtain ⟨h1, h2⟩ := hIco t ht
      have hbt := hb t (by rw [abs_of_nonneg h1]; linarith)
      rw [abs_of_nonneg h1] at hbt
      rw [dist_comm, dist_eq_norm]
      calc ‖f (g t)-g' t‖ ≤ C*t^4 := hbt
        _ ≤ max C 0*t^4 := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ max C 0*h^4 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h1 ht.2.le 4) (le_max_right _ _))
    (fun t ht => by
      obtain ⟨h1, h2⟩ := hIco t ht
      have := hgb (x := t) (by rw [Real.dist_eq, sub_zero, abs_of_nonneg h1]; linarith)
      rwa [hg0] at this)
    (by rw [h0, hg0, dist_self])
    h ⟨hh.1, le_rfl⟩
  rw [dist_eq_norm, sub_zero, zero_add] at hmain
  have hgb' := gronwallBound_le (x := h) K.2 (by positivity : 0 ≤ max C 0*h^4)
  have hexp : Real.exp (K*h) ≤ Real.exp K :=
    Real.exp_le_exp.mpr (mul_le_of_le_one_right K.2 (le_trans hh.2 hδ1le))
  calc ‖sol h-(y+h • vq f y h)‖ ≤ max C 0*h^4*h*Real.exp (K*h) := le_trans hmain hgb'
    _ ≤ max C 0*h^4*h*Real.exp K :=
        mul_le_mul_of_nonneg_left hexp (by have := hh.1; positivity)
    _ = max C 0*Real.exp K*h^5 := by ring

/-- **N1.** Fourth-order local consistency of classical RK4 for any field that is
    `C⁴` near the initial point: the step and the exact solution through `y` differ
    by `O(h⁵)`. -/
theorem rk4_local_error (hf : ContDiffAt ℝ 4 f y) {sol : ℝ → E} {ε : ℝ} (hε : 0 < ε)
    (h0 : sol 0 = y) (hsol : ∀ t ∈ Ioo (-ε) ε, HasDerivAt sol (f (sol t)) t) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ h ∈ Icc 0 δ, ‖rk4Step f y h-sol h‖ ≤ C*h^5 := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨U, hUu, hU, hyU⟩ := mem_nhds_iff.mp hu
  have hfU := hfu.mono hUu
  obtain ⟨C1, δ1, hδ1, hb1⟩ := rk4_expansion f y hU hyU hfU
  obtain ⟨C2, δ2, hδ2, hb2⟩ := flow_close f y hU hyU hfU hε h0 hsol
  refine ⟨C1+C2, min δ1 δ2, lt_min hδ1 hδ2, fun h hh => ?_⟩
  have hb1' := hb1 h (by rw [abs_of_nonneg hh.1]; exact le_trans hh.2 (min_le_left _ _))
  rw [abs_of_nonneg hh.1] at hb1'
  have hb2' := hb2 h ⟨hh.1, le_trans hh.2 (min_le_right _ _)⟩
  calc ‖rk4Step f y h-sol h‖ =
        ‖(rk4Step f y h-(y+h • vq f y h))-(sol h-(y+h • vq f y h))‖ := by congr 1; abel
    _ ≤ ‖rk4Step f y h-(y+h • vq f y h)‖+‖sol h-(y+h • vq f y h)‖ := norm_sub_le _ _
    _ ≤ C1*h^5+C2*h^5 := add_le_add hb1' hb2'
    _ = (C1+C2)*h^5 := by ring

end RK4

/-- N1 for the renderer's field: from any nonsingular Kerr phase point, the local
    solution exists and one RK4 step of the full geodesic/parallel-screen system
    is within `C h⁵` of it. -/
theorem kerr_rk4_local_error (mass : ℝ) (a : Cartesian.Space) (state : KerrField.Phase)
    (hr : 0 < Cartesian.radius a state.1) :
    ∃ curve : ℝ → KerrField.Phase, curve 0 = state ∧ ∃ C δ : ℝ, 0 < δ ∧
      ∀ h ∈ Icc 0 δ, ‖rk4Step (KerrField.phaseRhs mass a) state h-curve h‖ ≤ C*h^5 := by
  obtain ⟨curve, h0, ε, hε, hsol⟩ := KerrField.local_phase_solution mass a state 0 hr
  have hsol' : ∀ t ∈ Ioo (-ε) ε, HasDerivAt curve (KerrField.phaseRhs mass a (curve t)) t :=
    fun t ht => hsol t (by simpa using ht)
  have hf : ContDiffAt ℝ 4 (KerrField.phaseRhs mass a) state :=
    (KerrField.phase_rhs_smooth mass a state hr).of_le (by simp)
  exact ⟨curve, h0, rk4_local_error _ _ hf hε h0 hsol'⟩

end BlackHole.RK4Consistency
