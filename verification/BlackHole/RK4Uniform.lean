module
public import BlackHole.UniformRemainder
public import BlackHole.KerrCompact
public import BlackHole.RK4Stability
import Mathlib.Tactic.FunProp

/-! Uniform local RK4 defects for the nonlinear Kerr field. Compact exterior
starting regions acquire a common nonsingular stage neighbourhood, a common
step threshold, and one `C h⁵` defect bound for every exact solution segment
inside that neighbourhood. The constants are derived from source smoothness;
they are existential and do not certify production binary32 error budgets. -/

@[expose] public section
noncomputable section
open Set
open scoped ContDiff Topology
open scoped NNReal
namespace BlackHole.RK4Consistency
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem multilinear_smooth {n : ℕ} {F : E → E [×n]→L[ℝ] E}
    {v : Fin n → E → E} {y : E} (hF : ContDiffAt ℝ ∞ F y)
    (hv : ∀ i, ContDiffAt ℝ ∞ (v i) y) :
    ContDiffAt ℝ ∞ (fun x => F x (fun i => v i x)) y := by
  induction n with
  | zero =>
    have h := (continuousMultilinearCurryFin0 ℝ E E).contDiff.contDiffAt.comp y hF
    apply h.congr_of_eventuallyEq
    filter_upwards [] with x
    change F x (fun i => v i x) = F x 0
    congr 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    let curry := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) E
    have hc := (curry.contDiff.contDiffAt.comp y hF).clm_apply (hv 0)
    have h := ih hc (fun i => hv i.succ)
    apply h.congr_of_eventuallyEq
    filter_upwards [] with x
    change F x (fun i => v i x) = F x (Fin.cons (v 0 x) (fun i => v i.succ x))
    congr 1
    funext i
    cases i using Fin.cases <;> rfl

theorem q2_smooth {f : E → E} {y : E} (hf : ContDiffAt ℝ ∞ f y) :
    ContDiffAt ℝ ∞ (q2 f) y := by
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ f) y := hf.fderiv_right (by simp)
  unfold q2 L1 f0
  fun_prop


theorem q3_smooth {f : E → E} {y : E} (hf : ContDiffAt ℝ ∞ f y) :
    ContDiffAt ℝ ∞ (q3 f) y := by
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ f) y := hf.fderiv_right (by simp)
  have hdd : ContDiffAt ℝ ∞ (fderiv ℝ (fderiv ℝ f)) y := hd.fderiv_right (by simp)
  have hq2 := q2_smooth hf
  unfold q3 L1 D2 f0
  fun_prop

theorem q4_smooth {f : E → E} {y : E} (hf : ContDiffAt ℝ ∞ f y) :
    ContDiffAt ℝ ∞ (q4 f) y := by
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ f) y := hf.fderiv_right (by simp)
  have hdd : ContDiffAt ℝ ∞ (fderiv ℝ (fderiv ℝ f)) y := hd.fderiv_right (by simp)
  have hddd : ContDiffAt ℝ ∞ (iteratedFDeriv ℝ 3 f) y := hf.iteratedFDeriv_right (by simp)
  have hq2 := q2_smooth hf
  have hq3 := q3_smooth hf
  have ht := multilinear_smooth hddd (fun _ : Fin 3 => hf)
  have hl := hd.clm_apply hq3
  have hqe := (hdd.clm_apply hf).clm_apply hq2
  have heq := (hdd.clm_apply hq2).clm_apply hf
  unfold q4 L1 D2 T3 f0
  fun_prop

def quartic (f : E → E) (p : E × ℝ) : E := p.1+p.2 • vq f p.1 p.2
def quarticRate (f : E → E) (p : E × ℝ) : E :=
  f p.1+(2*p.2) • q2 f p.1+(3*p.2^2) • q3 f p.1+(4*p.2^3) • q4 f p.1
def stepRemainder (f : E → E) (p : E × ℝ) : E := rk4Step f p.1 p.2-quartic f p
def flowResidual (f : E → E) (p : E × ℝ) : E := f (quartic f p)-quarticRate f p

theorem quartic_smooth {f : E → E} {y : E} (hf : ContDiffAt ℝ ∞ f y) :
    ContDiffAt ℝ ∞ (quartic f) (y,0) ∧ ContDiffAt ℝ ∞ (quarticRate f) (y,0) := by
  have h0 : ContDiffAt ℝ ∞ (fun p : E × ℝ => f p.1) (y,0) := hf.comp _ contDiffAt_fst
  have h2 : ContDiffAt ℝ ∞ (fun p : E × ℝ => q2 f p.1) (y,0) :=
    ContDiffAt.comp (g := q2 f) (f := Prod.fst) (y,0) (q2_smooth hf) contDiffAt_fst
  have h3 : ContDiffAt ℝ ∞ (fun p : E × ℝ => q3 f p.1) (y,0) :=
    ContDiffAt.comp (g := q3 f) (f := Prod.fst) (y,0) (q3_smooth hf) contDiffAt_fst
  have h4 : ContDiffAt ℝ ∞ (fun p : E × ℝ => q4 f p.1) (y,0) :=
    ContDiffAt.comp (g := q4 f) (f := Prod.fst) (y,0) (q4_smooth hf) contDiffAt_fst
  constructor
  · unfold quartic vq f0
    fun_prop
  · unfold quarticRate
    fun_prop

theorem rk4_joint_smooth {f : E → E} {y : E} (hf : ContDiffAt ℝ ∞ f y) :
    ContDiffAt ℝ ∞ (fun p : E × ℝ => rk4Step f p.1 p.2) (y,0) := by
  have h1 : ContDiffAt ℝ ∞ (fun p : E × ℝ => f p.1) (y,0) := hf.comp _ contDiffAt_fst
  have h2 : ContDiffAt ℝ ∞ (fun p : E × ℝ => k2 f p.1 p.2) (y,0) := by
    unfold k2
    apply ContDiffAt.comp _ (by simpa using hf)
    fun_prop
  have h3 : ContDiffAt ℝ ∞ (fun p : E × ℝ => k3 f p.1 p.2) (y,0) := by
    unfold k3
    apply ContDiffAt.comp _ (by simpa using hf)
    fun_prop
  have h4 : ContDiffAt ℝ ∞ (fun p : E × ℝ => k4 f p.1 p.2) (y,0) := by
    unfold k4
    apply ContDiffAt.comp _ (by simpa using hf)
    fun_prop
  unfold rk4Step
  fun_prop

theorem uniform_remainders {f : E → E} {s : Set E} (hs : IsCompact s)
    (hf : ∀ y ∈ s, ContDiffAt ℝ ∞ f y) :
    (∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ y ∈ s, ∀ h ∈ Icc 0 δ,
      ‖stepRemainder f (y,h)‖ ≤ C*h^5) ∧
    (∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ y ∈ s, ∀ h ∈ Icc 0 δ,
      ‖flowResidual f (y,h)‖ ≤ C*h^4) := by
  have hstep (y : E) (hy : y ∈ s) : ContDiffAt ℝ 5 (stepRemainder f) (y,0) :=
    ((rk4_joint_smooth (hf y hy)).sub (quartic_smooth (hf y hy)).1).of_le (by simp)
  have hres (y : E) (hy : y ∈ s) : ContDiffAt ℝ 4 (flowResidual f) (y,0) := by
    have hfy : ContDiffAt ℝ ∞ f (quartic f (y,0)) := by simpa [quartic] using hf y hy
    have hcomp : ContDiffAt ℝ ∞ (fun p => f (quartic f p)) (y,0) :=
      hfy.comp _ (quartic_smooth (hf y hy)).1
    exact (hcomp.sub (quartic_smooth (hf y hy)).2).of_le (by simp)
  have hlocal (y : E) (hy : y ∈ s) : ∃ U, IsOpen U ∧ y ∈ U ∧ ContDiffOn ℝ 4 f U := by
    obtain ⟨U, hU, hyU, hfu⟩ := ((hf y hy).of_le (show (4:ℕ∞ω) ≤ ∞ by simp)).contDiffOn' le_rfl (by simp)
    exact ⟨U,hU,hyU,by simpa only [Set.insert_eq_of_mem (Set.mem_univ y), Set.univ_inter] using hfu⟩
  constructor
  · apply UniformRemainder.uniform_small hs 4 hstep
    intro y hy
    obtain ⟨U,hU,hyU,hfu⟩ := hlocal y hy
    exact UniformRemainder.rightSmall_of_small (rk4_expansion f y hU hyU hfu)
  · apply UniformRemainder.uniform_small hs 3 hres
    intro y hy
    obtain ⟨U,hU,hyU,hfu⟩ := hlocal y hy
    exact UniformRemainder.rightSmall_of_small (flow_residual f y hU hyU hfu)

theorem quartic_hasDerivAt (f : E → E) (y : E) (t : ℝ) :
    HasDerivAt (fun u => quartic f (y,u)) (quarticRate f (y,t)) t := by
  have heq : (fun u => quartic f (y,u)) =
      fun u => y+u • f0 f y+u^2 • q2 f y+u^3 • q3 f y+u^4 • q4 f y := by
    funext u
    simp only [quartic, vq]
    module
  rw [heq]
  have hd := (((((hasDerivAt_id t).smul_const (f0 f y)).const_add y).add
    ((hasDerivAt_pow 2 t).smul_const (q2 f y))).add
    ((hasDerivAt_pow 3 t).smul_const (q3 f y))).add
    ((hasDerivAt_pow 4 t).smul_const (q4 f y))
  convert hd using 1
  · funext u; simp only [Pi.add_apply, id]
  · simp only [quarticRate, f0, Nat.cast_ofNat, one_smul, pow_one,
      show (2:ℕ)-1=1 from rfl, show (3:ℕ)-1=2 from rfl, show (4:ℕ)-1=3 from rfl]

theorem uniform_local_error {f : E → E} {s U : Set E} {K : ℝ≥0} (hs : IsCompact s)
    (hf : ∀ y ∈ s, ContDiffAt ℝ ∞ f y) (hsU : s ⊆ interior U)
    (hlip : LipschitzOnWith K f U) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ y ∈ s, ∀ h ∈ Icc 0 δ, ∀ sol : ℝ → E,
      sol 0 = y → (∀ t ∈ Icc 0 h, HasDerivAt sol (f (sol t)) t) →
      (∀ t ∈ Icc 0 h, sol t ∈ U) → ‖rk4Step f y h-sol h‖ ≤ C*h^5 := by
  obtain ⟨⟨C1,δ1,hC1,hδ1,h1⟩,⟨C2,δ2,hC2,hδ2,h2⟩⟩ := uniform_remainders hs hf
  obtain ⟨δ3,hδ3,h3⟩ := UniformRemainder.uniform_mem hs isOpen_interior
    (fun y hy => (quartic_smooth (hf y hy)).1.continuousAt)
    (fun y hy => by simpa [quartic] using hsU hy)
  let δ := min (min δ1 δ2) (min δ3 1)
  have hδ : 0 < δ := by positivity
  refine ⟨C1+C2*Real.exp K, δ, by positivity, hδ, fun y hy h hh sol h0 hsol hmem => ?_⟩
  have hh1 : h ≤ δ1 := hh.2.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hh2 : h ≤ δ2 := hh.2.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hh3 : h ≤ δ3 := hh.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hh4 : h ≤ 1 := hh.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc : ContinuousOn (fun t => quartic f (y,t)) (Icc 0 h) :=
    fun t _ => (quartic_hasDerivAt f y t).continuousAt.continuousWithinAt
  have hmain := dist_le_of_approx_trajectories_ODE_of_mem (v := fun _ => f)
    (s := fun _ => U) (K := K) (f := sol) (g := fun t => quartic f (y,t))
    (f' := fun t => f (sol t)) (g' := fun t => quarticRate f (y,t))
    (a := 0) (b := h) (εf := 0) (εg := C2*h^4) (δ := 0)
    (fun _ _ => hlip)
    (fun t ht => (hsol t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hsol t ⟨ht.1,ht.2.le⟩).hasDerivWithinAt)
    (fun _ _ => by simp)
    (fun t ht => hmem t ⟨ht.1,ht.2.le⟩)
    hc (fun t _ => (quartic_hasDerivAt f y t).hasDerivWithinAt)
    (fun t ht => by
      rw [dist_comm, dist_eq_norm]
      calc _ ≤ C2*t^4 := h2 y hy t ⟨ht.1,ht.2.le.trans hh2⟩
        _ ≤ C2*h^4 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.1 ht.2.le 4) hC2)
    (fun t ht => interior_subset (h3 y hy t ⟨ht.1,ht.2.le.trans hh3⟩))
    (by simp [quartic, h0]) h ⟨hh.1,le_rfl⟩
  rw [dist_eq_norm, sub_zero, zero_add] at hmain
  have hg := gronwallBound_le (x := h) K.2 (mul_nonneg hC2 (by positivity : 0 ≤ h^4))
  have hexp : Real.exp (K*h) ≤ Real.exp K :=
    Real.exp_le_exp.mpr (mul_le_of_le_one_right K.2 hh4)
  have hflow : ‖sol h-quartic f (y,h)‖ ≤ C2*Real.exp K*h^5 := by
    calc _ ≤ C2*h^4*h*Real.exp (K*h) := hmain.trans hg
      _ ≤ C2*h^4*h*Real.exp K := mul_le_mul_of_nonneg_left hexp (by have := hh.1; positivity)
      _ = _ := by ring
  calc _ ≤ ‖rk4Step f y h-quartic f (y,h)‖+‖sol h-quartic f (y,h)‖ :=
        (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans_eq (by rw [norm_sub_rev (quartic f (y,h)) (sol h)])
    _ ≤ C1*h^5+C2*Real.exp K*h^5 := add_le_add (h1 y hy h ⟨hh.1,hh1⟩) hflow
    _ = _ := by ring

theorem kerr_uniform_step_bounds (mass : ℝ) (a : Cartesian.Space) {s : Set KerrField.Phase}
    (hs : IsCompact s) (hr : ∀ y ∈ s, 0 < Cartesian.radius a y.1) :
    ∃ U : Set KerrField.Phase, ∃ K : ℝ≥0, ∃ C δ : ℝ,
      IsCompact U ∧ s ⊆ interior U ∧ (∀ y ∈ U, 0 < Cartesian.radius a y.1) ∧
      LipschitzOnWith K (KerrField.phaseRhs mass a) U ∧ 0 ≤ C ∧ 0 < δ ∧
      (∀ y ∈ s, ∀ h ∈ Icc 0 δ, StagesIn (KerrField.phaseRhs mass a) U y h) ∧
      ∀ y ∈ s, ∀ h ∈ Icc 0 δ, ∀ sol : ℝ → KerrField.Phase,
        sol 0 = y → (∀ t ∈ Icc 0 h, HasDerivAt sol (KerrField.phaseRhs mass a (sol t)) t) →
        (∀ t ∈ Icc 0 h, sol t ∈ U) →
        ‖rk4Step (KerrField.phaseRhs mass a) y h-sol h‖ ≤ C*h^5 := by
  let D : Set KerrField.Phase := {y | 0 < Cartesian.radius a y.1}
  have hD : IsOpen D := KerrField.positive_phase_domain_open a
  obtain ⟨r,hrpos,hrD⟩ := hs.exists_cthickening_subset_open hD hr
  let U := Metric.cthickening r s
  have hU : IsCompact U := hs.cthickening
  have hsU : s ⊆ interior U :=
    (Metric.self_subset_thickening hrpos s).trans (Metric.thickening_subset_interior_cthickening r s)
  have hrad : ∀ y ∈ U, 0 < Cartesian.radius a y.1 := fun _ hy => hrD hy
  obtain ⟨K,hlip⟩ := KerrField.phase_rhs_compact_lipschitz mass a hU hrad
  obtain ⟨C,δ0,hC,hδ0,hlocal⟩ := uniform_local_error hs
    (fun y hy => KerrField.phase_rhs_smooth mass a y (hr y hy)) hsU hlip
  obtain ⟨M,hM,hbound⟩ := KerrField.phase_rhs_derivatives_bounded mass a hU hrad 0
  have hnorm : ∀ y ∈ U, ‖KerrField.phaseRhs mass a y‖ ≤ M :=
    fun y hy => by simpa only [norm_iteratedFDeriv_zero] using hbound y hy
  let δ := min δ0 (r/(M+1))
  have hδ : 0 < δ := lt_min hδ0 (by positivity)
  refine ⟨U,K,C,δ,hU,hsU,hrad,hlip,hC,hδ,?_,?_
    ⟩
  · intro y hy h hh
    apply stagesIn_of_ball (KerrField.phaseRhs mass a) y h M hM hnorm
    intro z hz
    apply Metric.mem_cthickening_of_dist_le z y r s hy
    have hhlim : h ≤ r/(M+1) := hh.2.trans (min_le_right _ _)
    have hprod : h*(M+1) ≤ r := (le_div_iff₀ (by positivity : 0 < M+1)).mp hhlim
    have hd := Metric.mem_closedBall.mp hz
    rw [abs_of_nonneg hh.1] at hd
    nlinarith [hh.1]
  · intro y hy h hh sol h0 hsol hmem
    exact hlocal y hy h ⟨hh.1,hh.2.trans (min_le_left _ _)⟩ sol h0 hsol hmem

/-- The source supplies the uniform stage and local-defect hypotheses for
finite-horizon accumulation. Roundoff is an explicit execution-error budget;
no infinite-time existence or global region invariance is assumed. -/
theorem kerr_uniform_global_error (mass : ℝ) (a : Cartesian.Space) {s : Set KerrField.Phase}
    (hs : IsCompact s) (hr : ∀ y ∈ s, 0 < Cartesian.radius a y.1) :
    ∃ K : ℝ≥0, ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ (N : ℕ) (h roundoff initial : ℝ) (approx : ℕ → KerrField.Phase)
        (sol : ℝ → KerrField.Phase), h ∈ Icc 0 δ → 0 ≤ roundoff → 0 ≤ initial →
        (∀ n < N, approx n ∈ s) → (∀ t ∈ Icc 0 ((N:ℝ)*h), sol t ∈ s) →
        (∀ t ∈ Icc 0 ((N:ℝ)*h), HasDerivAt sol (KerrField.phaseRhs mass a (sol t)) t) →
        ‖approx 0-sol 0‖ ≤ initial →
        (∀ n < N, ‖approx (n+1)-rk4Step (KerrField.phaseRhs mass a) (approx n) h‖ ≤ roundoff) →
        ∀ n ≤ N, ‖approx n-sol ((n:ℝ)*h)‖ ≤
          (initial+(n:ℝ)*(C*h^5+roundoff))*Real.exp (K*((n:ℝ)*h)) := by
  obtain ⟨U,K,C,δ,_hU,hsU,_hrU,hlip,hC,hδ,hstage,hlocal⟩ := kerr_uniform_step_bounds mass a hs hr
  refine ⟨K,C,δ,hC,hδ,fun N h roundoff initial approx sol hh hroundoff hinitial
    ha hmem hsol hzero hround => ?_⟩
  have hsample (n : ℕ) (hn : n ≤ N) : (n:ℝ)*h ∈ Icc 0 ((N:ℝ)*h) :=
    ⟨mul_nonneg (Nat.cast_nonneg _) hh.1, mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) hh.1⟩
  have htime (n : ℕ) (hn : n < N) (t : ℝ) (ht : t ∈ Icc 0 h) :
      (n:ℝ)*h+t ∈ Icc 0 ((N:ℝ)*h) := by
    refine ⟨add_nonneg (mul_nonneg (Nat.cast_nonneg _) hh.1) ht.1, ?_⟩
    have hb := mul_le_mul_of_nonneg_right
      (show ((n+1:ℕ):ℝ) ≤ (N:ℝ) from Nat.cast_le.mpr (Nat.succ_le_of_lt hn)) hh.1
    push_cast at hb
    linarith [ht.2]
  apply rk4_fixed_error_bound_upto (KerrField.phaseRhs mass a) hlip approx
    (fun n => sol ((n:ℝ)*h)) N h C roundoff initial hh.1 hC hroundoff hinitial
  · intro n hn
    exact hstage (approx n) (ha n hn) h hh
  · intro n hn
    exact hstage (sol ((n:ℝ)*h)) (hmem _ (hsample n hn.le)) h hh
  · simpa using hzero
  · exact hround
  · intro n hn
    have hshift (t : ℝ) (ht : t ∈ Icc 0 h) :
        HasDerivAt (fun u => sol ((n:ℝ)*h+u))
          (KerrField.phaseRhs mass a (sol ((n:ℝ)*h+t))) t := by
      simpa only [Function.comp_def, one_smul] using
        (hsol _ (htime n hn t ht)).scomp t ((hasDerivAt_id t).const_add ((n:ℝ)*h))
    have heq : (n:ℝ)*h+h = ((n+1:ℕ):ℝ)*h := by push_cast; ring
    simpa only [heq] using hlocal (sol ((n:ℝ)*h)) (hmem _ (hsample n hn.le)) h hh
      (fun t => sol ((n:ℝ)*h+t)) (by simp) hshift
      (fun t ht => interior_subset (hsU (hmem _ (htime n hn t ht))))

/-- A checked accumulated budget below the neighbourhood radius also proves
numerical-region containment, rather than assuming it at every step. -/
theorem kerr_certified_global_error (mass : ℝ) (a : Cartesian.Space) {s : Set KerrField.Phase}
    (hs : IsCompact s) (hr : ∀ y ∈ s, 0 < Cartesian.radius a y.1) :
    ∃ r : ℝ, 0 < r ∧ ∃ K : ℝ≥0, ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ (N : ℕ) (h roundoff initial : ℝ) (approx : ℕ → KerrField.Phase)
        (sol : ℝ → KerrField.Phase), h ∈ Icc 0 δ → 0 ≤ roundoff → 0 ≤ initial →
        (∀ t ∈ Icc 0 ((N:ℝ)*h), sol t ∈ s) →
        (∀ t ∈ Icc 0 ((N:ℝ)*h), HasDerivAt sol (KerrField.phaseRhs mass a (sol t)) t) →
        ‖approx 0-sol 0‖ ≤ initial →
        (∀ n < N, ‖approx (n+1)-rk4Step (KerrField.phaseRhs mass a) (approx n) h‖ ≤ roundoff) →
        (∀ n ≤ N, (initial+(n:ℝ)*(C*h^5+roundoff))*Real.exp (K*((n:ℝ)*h)) ≤ r) →
        ∀ n ≤ N, ‖approx n-sol ((n:ℝ)*h)‖ ≤
          (initial+(n:ℝ)*(C*h^5+roundoff))*Real.exp (K*((n:ℝ)*h)) := by
  obtain ⟨r,hrpos,hrD⟩ := hs.exists_cthickening_subset_open
    (KerrField.positive_phase_domain_open a) hr
  let S := Metric.cthickening r s
  have hS : IsCompact S := hs.cthickening
  have hrad : ∀ y ∈ S, 0 < Cartesian.radius a y.1 := fun _ hy => hrD hy
  have hsS : s ⊆ S := Metric.self_subset_cthickening s
  obtain ⟨K,C,δ,hC,hδ,hglobal⟩ := kerr_uniform_global_error mass a hS hrad
  refine ⟨r,hrpos,K,C,δ,hC,hδ,fun N h roundoff initial approx sol hh hroundoff hinitial
    hmem hsol hzero hround hbudget => ?_⟩
  have htime (m : ℕ) (hm : m ≤ N) : Icc (0:ℝ) ((m:ℝ)*h) ⊆ Icc 0 ((N:ℝ)*h) :=
    Icc_subset_Icc_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hm) hh.1)
  have hproof : ∀ n ≤ N, ‖approx n-sol ((n:ℝ)*h)‖ ≤
      (initial+(n:ℝ)*(C*h^5+roundoff))*Real.exp (K*((n:ℝ)*h)) ∧ approx n ∈ S := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      have he : ‖approx n-sol ((n:ℝ)*h)‖ ≤
          (initial+(n:ℝ)*(C*h^5+roundoff))*Real.exp (K*((n:ℝ)*h)) := by
        cases n with
        | zero => simpa using hzero
        | succ m =>
          exact hglobal (m+1) h roundoff initial approx sol hh hroundoff hinitial
            (fun i hi => (ih i hi (hi.le.trans hn)).2)
            (fun t ht => hsS (hmem t (htime _ hn ht)))
            (fun t ht => hsol t (htime _ hn ht)) hzero
            (fun i hi => hround i (hi.trans_le hn)) (m+1) le_rfl
      refine ⟨he,?_⟩
      apply Metric.mem_cthickening_of_dist_le (approx n) (sol ((n:ℝ)*h)) r s
        (hmem _ ⟨mul_nonneg (Nat.cast_nonneg _) hh.1,
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) hh.1⟩)
      simpa only [dist_eq_norm] using he.trans (hbudget n hn)
  exact fun n hn => (hproof n hn).1

/-- Variable-step certification for the actual Kerr field. A verified step
perturbation and a budget that stays below the neighbourhood radius imply
both the trajectory enclosure and every required numerical stage condition. -/
theorem kerr_certified_variable_error (mass : ℝ) (a : Cartesian.Space) {s : Set KerrField.Phase}
    (hs : IsCompact s) (hr : ∀ y ∈ s, 0 < Cartesian.radius a y.1) :
    ∃ r : ℝ, 0 < r ∧ ∃ K : ℝ≥0, ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ (N : ℕ) (T : ℝ) (time step roundoff budget : ℕ → ℝ)
        (approx : ℕ → KerrField.Phase) (sol : ℝ → KerrField.Phase),
        time 0 = 0 → (∀ n ≤ N, time n ∈ Icc 0 T) →
        (∀ n < N, step n ∈ Icc 0 δ) → (∀ n < N, time (n+1) = time n+step n) →
        (∀ t ∈ Icc 0 T, sol t ∈ s) →
        (∀ t ∈ Icc 0 T, HasDerivAt sol (KerrField.phaseRhs mass a (sol t)) t) →
        ‖approx 0-sol 0‖ ≤ budget 0 →
        (∀ n < N, ‖approx (n+1)-rk4Step (KerrField.phaseRhs mass a) (approx n) (step n)‖ ≤ roundoff n) →
        (∀ n < N, Numerics.rk4Polynomial (K*step n)*budget n+C*(step n)^5+roundoff n ≤ budget (n+1)) →
        (∀ n ≤ N, budget n ≤ r) → ∀ n ≤ N, ‖approx n-sol (time n)‖ ≤ budget n := by
  obtain ⟨r,hrpos,hrD⟩ := hs.exists_cthickening_subset_open
    (KerrField.positive_phase_domain_open a) hr
  let S := Metric.cthickening r s
  have hS : IsCompact S := hs.cthickening
  have hrad : ∀ y ∈ S, 0 < Cartesian.radius a y.1 := fun _ hy => hrD hy
  have hsS : s ⊆ S := Metric.self_subset_cthickening s
  obtain ⟨U,K,C,δ,_hU,hSU,_hUr,hlip,hC,hδ,hstage,hlocal⟩ :=
    kerr_uniform_step_bounds mass a hS hrad
  refine ⟨r,hrpos,K,C,δ,hC,hδ,fun N T time step roundoff budget approx sol ht0 htime
    hstep hclock hmem hsol hzero hround hbudget hclear => ?_⟩
  have hsegment (n : ℕ) (hn : n < N) (t : ℝ) (ht : t ∈ Icc 0 (step n)) :
      time n+t ∈ Icc 0 T := by
    refine ⟨add_nonneg (htime n hn.le).1 ht.1, ?_⟩
    have hb := (htime (n+1) (Nat.succ_le_of_lt hn)).2
    rw [hclock n hn] at hb
    linarith [ht.2]
  have hproof : ∀ n ≤ N, ‖approx n-sol (time n)‖ ≤ budget n ∧ approx n ∈ S := by
    intro n
    induction n with
    | zero =>
      intro hn
      have he : ‖approx 0-sol (time 0)‖ ≤ budget 0 := by simpa only [ht0] using hzero
      refine ⟨he,?_⟩
      apply Metric.mem_cthickening_of_dist_le (approx 0) (sol (time 0)) r s (hmem _ (htime 0 hn))
      simpa only [dist_eq_norm] using he.trans (hclear 0 hn)
    | succ n ih =>
      intro hn
      have hnN : n < N := Nat.lt_of_succ_le hn
      have prev := ih hnN.le
      have hexact : sol (time n) ∈ S := hsS (hmem _ (htime n hnN.le))
      have hshift (t : ℝ) (ht : t ∈ Icc 0 (step n)) :
          HasDerivAt (fun u => sol (time n+u)) (KerrField.phaseRhs mass a (sol (time n+t))) t := by
        simpa only [Function.comp_def,one_smul] using
          (hsol _ (hsegment n hnN t ht)).scomp t ((hasDerivAt_id t).const_add (time n))
      have htrunc : ‖rk4Step (KerrField.phaseRhs mass a) (sol (time n)) (step n)-sol (time (n+1))‖ ≤
          C*(step n)^5 := by
        simpa only [hclock n hnN] using hlocal (sol (time n)) hexact (step n) (hstep n hnN)
          (fun t => sol (time n+t)) (by simp) hshift
          (fun t ht => interior_subset (hSU (hsS (hmem _ (hsegment n hnN t ht)))))
      have hrec := rk4_error_recurrence (KerrField.phaseRhs mass a) hlip (approx n) (sol (time n))
        (approx (n+1)) (sol (time (n+1))) (step n) (C*(step n)^5) (roundoff n)
        (hstage (approx n) prev.2 (step n) (hstep n hnN))
        (hstage (sol (time n)) hexact (step n) (hstep n hnN)) (hround n hnN) htrunc
      have hg : 0 ≤ Numerics.rk4Polynomial (K*step n) := by
        have hp := (hstep n hnN).1
        unfold Numerics.rk4Polynomial
        positivity
      have he : ‖approx (n+1)-sol (time (n+1))‖ ≤ budget (n+1) := by
        rw [abs_of_nonneg (hstep n hnN).1] at hrec
        exact hrec.trans ((add_le_add (add_le_add (mul_le_mul_of_nonneg_left prev.1 hg) le_rfl) le_rfl).trans
          (hbudget n hnN))
      refine ⟨he,?_⟩
      apply Metric.mem_cthickening_of_dist_le (approx (n+1)) (sol (time (n+1))) r s
        (hmem _ (htime (n+1) hn))
      simpa only [dist_eq_norm] using he.trans (hclear (n+1) hn)
  exact fun n hn => (hproof n hn).1

end BlackHole.RK4Consistency
