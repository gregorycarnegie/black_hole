module
public import BlackHole.RK4Consistency
public import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Tactic.FunProp

/-! A smooth family of pointwise Taylor remainders has uniform constants over
a compact parameter set. Pointwise asymptotic order is not assumed uniform:
`small_derivatives_zero` first proves the vanishing Taylor coefficients, then
`uniform_small` bounds the next joint derivative on a compact time slab. -/

@[expose] public section
noncomputable section
open Set Finset Filter
open scoped Topology
set_option linter.unusedSectionVars false
namespace BlackHole.UniformRemainder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def RightSmall (k : ℕ) (f : ℝ → E) : Prop :=
  ∃ C δ : ℝ, 0 < δ ∧ ∀ h ∈ Icc 0 δ, ‖f h‖ ≤ C*h^k

lemma rightSmall_of_small {k : ℕ} {f : ℝ → E} (hf : RK4Consistency.Small k f) :
    RightSmall k f := by
  obtain ⟨C, δ, hδ, hb⟩ := hf
  refine ⟨C, δ, hδ, fun h hh => ?_⟩
  simpa only [abs_of_nonneg hh.1] using hb h (by rw [abs_of_nonneg hh.1]; exact hh.2)

lemma RightSmall.sub {k : ℕ} {f g : ℝ → E} (hf : RightSmall k f) (hg : RightSmall k g) :
    RightSmall k (fun h => f h-g h) := by
  obtain ⟨C, δ, hδ, hb⟩ := hf
  obtain ⟨D, ε, hε, hd⟩ := hg
  refine ⟨C+D, min δ ε, lt_min hδ hε, fun h hh => ?_⟩
  calc _ ≤ ‖f h‖+‖g h‖ := norm_sub_le _ _
    _ ≤ C*h^k+D*h^k := add_le_add (hb h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩)
      (hd h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩)
    _ = _ := by ring

lemma RightSmall.congr {k : ℕ} {f g : ℝ → E} (hf : RightSmall k f)
    (hfg : ∀ h, f h = g h) : RightSmall k g := by
  obtain ⟨C, δ, hδ, hb⟩ := hf
  exact ⟨C, δ, hδ, fun h hh => by rw [← hfg h]; exact hb h hh⟩

lemma RightSmall.unscale {k : ℕ} {f : ℝ → E}
    (hf : RightSmall (k+1) (fun h => h • f h)) (hc : ContinuousAt f 0) : RightSmall k f := by
  obtain ⟨C, δ, hδ, hb⟩ := hf
  have hb' (h : ℝ) (hh : 0 < h) (hd : h ≤ δ) : ‖f h‖ ≤ C*h^k := by
    apply (mul_le_mul_iff_right₀ hh).mp
    calc h*‖f h‖ = ‖h • f h‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
      _ ≤ C*h^(k+1) := hb h ⟨hh.le, hd⟩
      _ = h*(C*h^k) := by ring
  have hev : ∀ᶠ h in 𝓝[>] (0:ℝ), ‖f h‖ ≤ C*h^k := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with h hh hd
    exact hb' h hh hd.le
  have hlim : ‖f 0‖ ≤ C*(0:ℝ)^k :=
    le_of_tendsto_of_tendsto (hc.norm.mono_left nhdsWithin_le_nhds)
      ((show ContinuousAt (fun h : ℝ => C*h^k) 0 by fun_prop).mono_left nhdsWithin_le_nhds) hev
  refine ⟨C, δ, hδ, fun h hh => ?_⟩
  obtain rfl | hh' := eq_or_lt_of_le hh.1
  · exact hlim
  · exact hb' h hh' hh.2

def poly (c : ℕ → E) (n : ℕ) (h : ℝ) : E := ∑ i ∈ range n, h^i • c i

lemma poly_continuous (c : ℕ → E) (n : ℕ) : Continuous (poly c n) := by
  unfold poly
  fun_prop

lemma poly_unique (c : ℕ → E) (n : ℕ) (hp : RightSmall n (poly c n)) :
    ∀ i < n, c i = 0 := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    have hzero : c 0 = 0 := by
      obtain ⟨C, δ, hδ, hb⟩ := hp
      have h := hb 0 ⟨le_rfl, hδ.le⟩
      simpa [poly, sum_range_succ', zero_pow (Nat.succ_ne_zero n)] using h
    have hfactor (h : ℝ) : poly c (n+1) h = h • poly (fun i => c (i+1)) n h := by
      simp only [poly, sum_range_succ', pow_zero, one_smul, hzero, add_zero, smul_sum]
      apply sum_congr rfl
      intro i _
      rw [pow_succ, mul_smul]
      module
    have htail := (hp.congr hfactor).unscale ((poly_continuous _ _).continuousAt)
    intro i hi
    cases i with
    | zero => exact hzero
    | succ i => exact ih _ htail i (by omega)

lemma taylor_small {g : ℝ → E} {n : ℕ} (hg : ContDiffAt ℝ (n+1) g 0) :
    RightSmall (n+1) (fun h => g h-poly (fun i => ((i.factorial : ℝ)⁻¹) • iteratedDeriv i g 0) (n+1) h) := by
  obtain ⟨U, hU, h0U, hgu⟩ := hg.contDiffOn' le_rfl (by simp)
  simp only [Set.insert_eq_of_mem (Set.mem_univ (0:ℝ)), Set.univ_inter] at hgu
  obtain ⟨δ, hδ, hb⟩ := Metric.isOpen_iff.mp hU 0 h0U
  have hsub : Icc (0:ℝ) (δ/2) ⊆ U := by
    intro t ht
    apply hb
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    linarith [ht.2]
  have hcont : ContDiffOn ℝ (n+1) g (Icc 0 (δ/2)) := hgu.mono hsub
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound (show (0:ℝ) ≤ δ/2 by positivity) hcont
  refine ⟨C, δ/2, by positivity, fun h hh => ?_⟩
  have heq : taylorWithinEval g n (Icc 0 (δ/2)) 0 h =
      poly (fun i => ((i.factorial : ℝ)⁻¹) • iteratedDeriv i g 0) (n+1) h := by
    rw [taylor_within_apply]
    apply sum_congr rfl
    intro i hi
    rw [iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc (by positivity)) (hg.of_le (by exact_mod_cast (show i ≤ n+1 by simp at hi; omega)))
      (by constructor <;> positivity)]
    simp only [sub_zero, smul_smul]
    rw [mul_comm]
  simpa only [heq, sub_zero] using hC h hh

lemma small_derivatives_zero {g : ℝ → E} {n : ℕ}
    (hg : ContDiffAt ℝ (n+1) g 0) (hb : RightSmall (n+1) g) :
    ∀ i ≤ n, iteratedDeriv i g 0 = 0 := by
  have hp : RightSmall (n+1)
      (poly (fun i => ((i.factorial : ℝ)⁻¹) • iteratedDeriv i g 0) (n+1)) :=
    (hb.sub (taylor_small hg)).congr (fun h => by abel)
  have hz := poly_unique (fun i => ((i.factorial : ℝ)⁻¹) • iteratedDeriv i g 0) (n+1) hp
  intro i hi
  have h := hz i (by omega)
  exact (smul_eq_zero.mp h).resolve_left (inv_ne_zero (by positivity))

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- A common time slab for a continuous family starting in an open set. -/
theorem uniform_mem {B : Type*} [TopologicalSpace B] {F : A × ℝ → B}
    {s : Set A} (hs : IsCompact s) {V : Set B} (hV : IsOpen V)
    (hc : ∀ y ∈ s, ContinuousAt F (y,0)) (h0 : ∀ y ∈ s, F (y,0) ∈ V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ s, ∀ h ∈ Icc 0 δ, F (y,h) ∈ V := by
  let U := interior (F ⁻¹' V)
  let s₀ := (fun y : A => (y,(0:ℝ))) '' s
  have hs₀ : IsCompact s₀ := hs.image (by fun_prop)
  have hsU : s₀ ⊆ U := by
    rintro _ ⟨y,hy,rfl⟩
    exact mem_interior_iff_mem_nhds.mpr ((hc y hy).preimage_mem_nhds (hV.mem_nhds (h0 y hy)))
  obtain ⟨δ,hδ,hd⟩ := hs₀.exists_cthickening_subset_open isOpen_interior hsU
  refine ⟨δ,hδ,fun y hy h hh => ?_⟩
  apply interior_subset (hd ?_)
  apply Metric.mem_cthickening_of_dist_le (y,h) (y,0) δ s₀ (mem_image_of_mem _ hy)
  simpa [Prod.dist_eq, Real.dist_eq, abs_of_nonneg hh.1] using
    (show max 0 h ≤ δ from max_le hδ.le hh.2)

theorem uniform_small {F : A × ℝ → E} {s : Set A} (hs : IsCompact s) (n : ℕ)
    (hF : ∀ y ∈ s, ContDiffAt ℝ (n+1) F (y,0))
    (hb : ∀ y ∈ s, RightSmall (n+1) (fun h => F (y,h))) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ y ∈ s, ∀ h ∈ Icc 0 δ,
      ‖F (y,h)‖ ≤ C*h^(n+1) := by
  let U : Set (A × ℝ) := {p | ContDiffAt ℝ (n+1) F p}
  have hU : IsOpen U := isOpen_iff_mem_nhds.mpr fun p hp =>
    (show ContDiffAt ℝ (n+1) F p from hp).eventually (by simp)
  have hfU : ContDiffOn ℝ (n+1) F U := fun p hp =>
    (show ContDiffAt ℝ (n+1) F p from hp).contDiffWithinAt
  let s₀ := (fun y : A => (y,(0:ℝ))) '' s
  have hs₀ : IsCompact s₀ := hs.image (by fun_prop)
  have hsU : s₀ ⊆ U := by rintro _ ⟨y, hy, rfl⟩; exact hF y hy
  obtain ⟨δ, hδ, hδU⟩ := hs₀.exists_cthickening_subset_open hU hsU
  have hmem (y : A) (hy : y ∈ s) (t : ℝ) (ht : t ∈ Icc 0 δ) :
      ContDiffAt ℝ (n+1) F (y,t) := by
    change (y,t) ∈ U
    apply hδU
    apply Metric.mem_cthickening_of_dist_le (y,t) (y,0) δ s₀ (mem_image_of_mem _ hy)
    simpa [Prod.dist_eq, Real.dist_eq, abs_of_nonneg ht.1] using
      (show max 0 t ≤ δ from max_le hδ.le ht.2)
  have hcompact : IsCompact (s ×ˢ Icc (0:ℝ) δ) := hs.prod isCompact_Icc
  have hc : ContinuousOn (iteratedFDeriv ℝ (n+1) F) (s ×ˢ Icc (0:ℝ) δ) := by
    intro p hp
    exact ((hmem p.1 hp.1 p.2 hp.2).continuousAt_iteratedFDeriv (by norm_cast)).continuousWithinAt
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hc
  let B := max M 0
  have hB : 0 ≤ B := le_max_right _ _
  refine ⟨B/(n.factorial:ℝ), δ, by positivity, hδ, fun y hy h hh => ?_⟩
  have hgy : ∀ t ∈ Icc (0:ℝ) δ, ContDiffAt ℝ (n+1) (fun u => F (y,u)) t := by
    intro t ht
    exact (hmem y hy t ht).comp t (by fun_prop)
  have hzero := small_derivatives_zero (hgy 0 ⟨le_rfl, hδ.le⟩) (hb y hy)
  have hderiv (t : ℝ) (ht : t ∈ Icc (0:ℝ) δ) :
      iteratedDeriv (n+1) (fun u => F (y,u)) t =
        iteratedFDeriv ℝ (n+1) F (y,t) (fun _ => (0, (1:ℝ))) := by
    have hline := RK4Consistency.line_iteratedDeriv_on hU hfU (y,0) (0,(1:ℝ))
      (k := n+1) le_rfl t (by simpa [U] using hmem y hy t ht)
    simpa using hline
  have hbound (t : ℝ) (ht : t ∈ Icc (0:ℝ) δ) :
      ‖iteratedDerivWithin (n+1) (fun u => F (y,u)) (Icc 0 δ) t‖ ≤ B := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hδ) (hgy t ht) ht, hderiv t ht]
    calc _ ≤ ‖iteratedFDeriv ℝ (n+1) F (y,t)‖ * ∏ _i : Fin (n+1), ‖((0,(1:ℝ)) : A × ℝ)‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ (n+1) F (y,t)‖ := by simp [Prod.norm_def]
      _ ≤ B := (hM (y,t) ⟨hy, ht⟩).trans (le_max_left _ _)
  have htaylor : taylorWithinEval (fun u => F (y,u)) n (Icc 0 δ) 0 h = 0 := by
    rw [taylor_within_apply]
    apply sum_eq_zero
    intro i hi
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hδ)
      ((hgy 0 ⟨le_rfl,hδ.le⟩).of_le (by exact_mod_cast (show i ≤ n+1 by simp at hi; omega)))
      (by constructor <;> linarith), hzero i (by simp at hi; omega), smul_zero]
  have h := taylor_mean_remainder_bound hδ.le (fun t ht => (hgy t ht).contDiffWithinAt) hh hbound
  rw [htaylor, sub_zero, sub_zero] at h
  simpa [div_mul_eq_mul_div] using h

end BlackHole.UniformRemainder
