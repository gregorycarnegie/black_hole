module
public import BlackHole.KerrProgram
public import BlackHole.ValidatedStep
public import Mathlib.Analysis.ODE.Gronwall

/-! The ten-component system integrated by a certified step: position,
spatial covariant momentum and the transported screen. The conserved time
momentum `pt` is a fixed parameter. `lift` recovers a solution of all eleven
original Kerr equations, and `certified_step` is the weighted tube theorem
whose hypotheses the numerical checker discharges. -/

@[expose] public section
noncomputable section
open Set Metric
open scoped ContDiff NNReal
namespace BlackHole.StepField
open KerrProgram

abbrev Reduced := Fin 10 → ℝ

def assemble {S : Type*} (pt : S) (y : Fin 10 → S) : State S :=
  ⟨fun i => y ⟨i,by omega⟩,Fin.cases pt (fun i => y ⟨3+i,by omega⟩),fun i => y ⟨6+i,by omega⟩⟩

def component (i : Fin 10) : Component :=
  if h : i.val < 3 then .position ⟨i,h⟩
  else if h' : i.val < 6 then .momentum ⟨i-2,by omega⟩
  else .screen ⟨i-6,by omega⟩

theorem map_assemble {S T : Type*} (eval : S → T) (pt : S) (y : Fin 10 → S) :
    mapState eval (assemble pt y) = assemble (eval pt) (fun i => eval (y i)) := by
  simp only [mapState,assemble,State.mk.injEq,true_and,and_true]
  funext i
  cases i using Fin.cases <;> rfl

theorem get_assemble {S : Type*} (pt : S) (y : Fin 10 → S) (i : Fin 10) :
    (assemble pt y).get (component i) = y i := by
  fin_cases i <;> rfl

def full (pt : ℝ) (y : Reduced) : KerrField.Phase := toPhase (assemble pt y)

def field (a : Cartesian.Space) (pt : ℝ) (y : Reduced) : Reduced :=
  fun i => phaseGet (KerrField.phaseRhs 1 a (full pt y)) (component i)

theorem phaseGet_smooth (c : Component) : ContDiff ℝ ∞ (fun s : KerrField.Phase => phaseGet s c) := by
  cases c <;> simp only [phaseGet] <;> fun_prop

theorem full_smooth (pt : ℝ) : ContDiff ℝ ∞ (full pt) := by
  unfold full toPhase assemble
  refine ContDiff.prodMk ?_ (ContDiff.prodMk ?_ ?_)
  · exact contDiff_pi.mpr fun i => by fun_prop
  · refine contDiff_pi.mpr fun i => ?_
    cases i using Fin.cases with
    | zero => exact contDiff_const
    | succ i => simp only [Fin.cases_succ]; fun_prop
  · exact contDiff_pi.mpr fun i => by fun_prop

theorem field_smooth (a : Cartesian.Space) (pt : ℝ) (y : Reduced)
    (hr : 0 < Cartesian.radius a (full pt y).1) : ContDiffAt ℝ ∞ (field a pt) y := by
  refine contDiffAt_pi.mpr fun i => ?_
  exact (phaseGet_smooth (component i)).contDiffAt.comp y
    ((KerrField.phase_rhs_smooth 1 a (full pt y) hr).comp y (full_smooth pt).contDiffAt)

/-- A reduced solution with the parameter held fixed solves all eleven Kerr
equations, because the exact time-momentum equation is stationary. -/
theorem lift (a : Cartesian.Space) (pt : ℝ) (y : ℝ → Reduced) (s : Set ℝ) (t : ℝ)
    (hy : HasDerivWithinAt y (field a pt (y t)) s t) :
    HasDerivWithinAt (fun u => full pt (y u)) (KerrField.phaseRhs 1 a (full pt (y t))) s t := by
  have hc (i : Fin 10) : HasDerivWithinAt (fun u => y u i) (field a pt (y t) i) s t :=
    hasDerivWithinAt_pi.mp hy i
  set R := KerrField.phaseRhs 1 a (full pt (y t))
  have hx : HasDerivWithinAt (fun u => (full pt (y u)).1) R.1 s t := by
    refine hasDerivWithinAt_pi.mpr fun i => ?_
    fin_cases i <;> exact hc _
  have hp : HasDerivWithinAt (fun u => (full pt (y u)).2.1) R.2.1 s t := by
    refine hasDerivWithinAt_pi.mpr fun i => ?_
    cases i using Fin.cases with
    | zero =>
      have h0 : R.2.1 0 = 0 := KerrField.phase_rhs_stationary 1 a _
      rw [h0]
      exact hasDerivWithinAt_const t s pt
    | succ i => fin_cases i <;> exact hc _
  have hf : HasDerivWithinAt (fun u => (full pt (y u)).2.2) R.2.2 s t := by
    refine hasDerivWithinAt_pi.mpr fun i => ?_
    fin_cases i <;> exact hc _
  exact hx.prodMk (hp.prodMk hf)

/-- Diagonal weights as continuous linear maps. -/
def scale (w : Reduced) : Reduced →L[ℝ] Reduced :=
  ContinuousLinearMap.pi fun i => w i • ContinuousLinearMap.proj i

@[simp] theorem scale_apply (w v : Reduced) (i : Fin 10) : scale w v i = w i*v i := by
  simp [scale]

def inv (w : Reduced) : Reduced := fun i => (w i)⁻¹

def scaled (a : Cartesian.Space) (pt : ℝ) (w : Reduced) (z : Reduced) : Reduced :=
  scale (inv w) (field a pt (scale w z))

theorem scale_inv {w : Reduced} (hw : ∀ i, 0 < w i) (v : Reduced) : scale w (scale (inv w) v) = v := by
  funext i
  simp only [scale_apply,inv]
  field_simp [(hw i).ne']

theorem pi_norm_le {v : Reduced} {r : ℝ} (hr : 0 ≤ r) : ‖v‖ ≤ r ↔ ∀ i, |v i| ≤ r := by
  simp [pi_norm_le_iff_of_nonneg hr,Real.norm_eq_abs]

theorem weighted_ball {w : Reduced} (hw : ∀ i, 0 < w i) {ρ : ℝ} (hρ : 0 ≤ ρ) (c z : Reduced)
    (hz : ‖z-scale (inv w) c‖ ≤ ρ) (i : Fin 10) : |scale w z i-c i| ≤ ρ*w i := by
  have hzi := (pi_norm_le hρ).mp hz i
  simp only [Pi.sub_apply,scale_apply,inv] at hzi ⊢
  have : w i*z i-c i = w i*(z i-(w i)⁻¹*c i) := by field_simp [(hw i).ne']
  rw [this,abs_mul,abs_of_pos (hw i),mul_comm ρ]
  exact mul_le_mul_of_nonneg_left hzi (hw i).le

theorem weighted_norm {w : Reduced} (hw : ∀ i, 0 < w i) {r : ℝ} (hr : 0 ≤ r) (u v : Reduced)
    (h : ∀ i, |u i-v i| ≤ r*w i) : ‖scale (inv w) u-scale (inv w) v‖ ≤ r := by
  refine (pi_norm_le hr).mpr fun i => ?_
  have hi := inv_pos.mpr (hw i)
  simp only [Pi.sub_apply,scale_apply,inv]
  rw [← mul_sub,abs_mul,abs_of_pos hi]
  calc (w i)⁻¹*|u i-v i| ≤ (w i)⁻¹*(r*w i) := mul_le_mul_of_nonneg_left (h i) hi.le
    _ = r := by field_simp [(hw i).ne']

/-- The weighted tube theorem. Every hypothesis is a bound the numerical
checker establishes over enclosing boxes; no exact trajectory is assumed. -/
theorem certified_step (a : Cartesian.Space) (pt : ℝ) (w : Reduced) (hw : ∀ i, 0 < w i)
    (h : ℝ) (hh : 0 ≤ h) (P P' : ℝ → Reduced)
    (hP : ∀ t ∈ Icc 0 h, HasDerivWithinAt P (P' t) (Icc 0 h) t)
    (hP' : ContinuousOn P' (Icc 0 h))
    (ρ e0 δ K : ℝ) (hρ : 0 ≤ ρ) (he0 : 0 ≤ e0) (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (hdomain : ∀ t ∈ Icc 0 h, ∀ y : Reduced, (∀ i, |y i-P t i| ≤ ρ*w i) →
      0 < Cartesian.radius a (full pt y).1)
    (hjac : ∀ t ∈ Icc 0 h, ∀ y : Reduced, (∀ i, |y i-P t i| ≤ ρ*w i) → ∀ i,
      ∑ j, |fderiv ℝ (field a pt) y (Pi.single j 1) i| * w j ≤ K*w i)
    (hres : ∀ t ∈ Icc 0 h, ∀ i, |field a pt (P t) i-P' t i| ≤ δ*w i)
    (x : Reduced) (hx : ∀ i, |x i-P 0 i| ≤ e0*w i)
    (hinc : e0+h*(δ+K*ρ) ≤ ρ) :
    ∃ y : ℝ → Reduced, y 0 = x ∧
      (∀ t ∈ Icc 0 h, HasDerivWithinAt y (field a pt (y t)) (Icc 0 h) t) ∧
      (∀ t ∈ Icc 0 h, ∀ i, |y t i-P t i| ≤ ρ*w i) ∧
      ∀ t ∈ Icc 0 h, ∀ i, |y t i-P t i| ≤ gronwallBound e0 K δ t*w i := by
  have hw' (i : Fin 10) : 0 < (w i)⁻¹ := inv_pos.mpr (hw i)
  have hball (t : ℝ) (z : Reduced) (hz : z ∈ closedBall (scale (inv w) (P t)) ρ) (i : Fin 10) :
      |scale w z i-P t i| ≤ ρ*w i :=
    weighted_ball hw hρ (P t) z (by simpa [mem_closedBall,dist_eq_norm] using hz) i
  have hG (z : Reduced) (hz : 0 < Cartesian.radius a (full pt (scale w z)).1) :
      HasFDerivAt (scaled a pt w)
        ((scale (inv w)).comp ((fderiv ℝ (field a pt) (scale w z)).comp (scale w))) z := by
    have hf := ((field_smooth a pt _ hz).differentiableAt (by simp)).hasFDerivAt
    exact (scale (inv w)).hasFDerivAt.comp z (hf.comp z (scale w).hasFDerivAt)
  have hpath : ContinuousOn (fun z : ℝ × Reduced => scale (inv w) (P z.1)+z.2)
      ((Icc 0 h) ×ˢ closedBall 0 ρ) :=
    ((scale (inv w)).continuous.comp_continuousOn ((HasDerivWithinAt.continuousOn hP).comp
      continuousOn_fst (fun _ hz => hz.1))).add continuousOn_snd
  have hmaps : MapsTo (fun z : ℝ × Reduced => scale (inv w) (P z.1)+z.2)
      ((Icc 0 h) ×ˢ closedBall 0 ρ) {z | 0 < Cartesian.radius a (full pt (scale w z)).1} := by
    intro z hz
    apply hdomain z.1 hz.1
    apply hball z.1
    simpa [mem_closedBall,dist_eq_norm] using hz.2
  have hGc : ContinuousOn (scaled a pt w) {z | 0 < Cartesian.radius a (full pt (scale w z)).1} :=
    fun z hz => (hG z hz).continuousAt.continuousWithinAt
  have hlip : ∀ t ∈ Icc 0 h, LipschitzOnWith (⟨K,hK⟩ : ℝ≥0) (scaled a pt w)
      (closedBall (scale (inv w) (P t)) (⟨ρ,hρ⟩ : ℝ≥0)) := by
    intro t ht
    have hd (z : Reduced) (hz : z ∈ closedBall (scale (inv w) (P t)) ρ) :
        0 < Cartesian.radius a (full pt (scale w z)).1 := hdomain t ht _ (hball t z hz)
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun z hz => (hG z (hd z hz)).differentiableAt) (fun z hz => ?_) (convex_closedBall _ _)
    rw [(hG z (hd z hz)).fderiv]
    set L := fderiv ℝ (field a pt) (scale w z)
    have hreal : ‖(scale (inv w)).comp (L.comp (scale w))‖ ≤ K := by
      apply ValidatedStep.jacobian_norm_bound _ (fun i j => L (Pi.single j 1) i*w j*(w i)⁻¹) _ K hK
      · intro i
        have hj := hjac t ht _ (hball t z hz) i
        calc (∑ j, |L (Pi.single j 1) i*w j*(w i)⁻¹|)
            = (∑ j, |L (Pi.single j 1) i| * w j)*(w i)⁻¹ := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [abs_mul,abs_mul,abs_of_pos (hw j),abs_of_pos (hw' i)]
          _ ≤ K*w i*(w i)⁻¹ := mul_le_mul_of_nonneg_right hj (hw' i).le
          _ = K := by field_simp [(hw i).ne']
      · intro v i
        simp only [ContinuousLinearMap.comp_apply,scale_apply,inv]
        rw [ValidatedStep.linear_map_matrix_apply L (scale w v) i,Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [scale_apply]
        ring
    exact NNReal.coe_le_coe.mp hreal
  have hdef : ∀ t ∈ Icc 0 h, ‖scaled a pt w (scale (inv w) (P t))-scale (inv w) (P' t)‖ ≤ δ := by
    intro t ht
    have := weighted_norm hw hδ (field a pt (P t)) (P' t) (hres t ht)
    simpa [scaled,scale_inv hw,map_sub] using this
  have hx0 : ‖scale (inv w) x-scale (inv w) (P 0)‖ ≤ e0 := by
    simpa [map_sub] using weighted_norm hw he0 x (P 0) hx
  have hQ : ∀ t ∈ Icc 0 h, HasDerivWithinAt (fun t => scale (inv w) (P t)) (scale (inv w) (P' t))
      (Icc 0 h) t := fun t ht => (scale (inv w)).hasFDerivAt.comp_hasDerivWithinAt t (hP t ht)
  obtain ⟨sol,hsol0,hsol,hbound⟩ := ValidatedStep.exists_solution_in_tube (scaled a pt w)
    (fun t => scale (inv w) (P t)) (fun t => scale (inv w) (P' t)) (scale (inv w) x) h hh
    ⟨e0,he0⟩ ⟨ρ,hρ⟩ ⟨δ,hδ⟩ ⟨K,hK⟩ hQ
    ((hGc.comp hpath hmaps).sub ((scale (inv w)).continuous.comp_continuousOn
        (hP'.comp continuousOn_fst (fun _ hz => hz.1))))
    hlip (fun t ht => show _ ≤ δ from hdef t ht) (show _ ≤ e0 from hx0) hinc
  -- Inside the tube the field is K-Lipschitz, so Grönwall bounds the actual error.
  have hright {f f' : ℝ → Reduced} (hf : ∀ t ∈ Icc 0 h, HasDerivWithinAt f (f' t) (Icc 0 h) t)
      (t : ℝ) (ht : t ∈ Ico 0 h) : HasDerivWithinAt f (f' t) (Ici t) t :=
    (hf t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  have hgron := dist_le_of_approx_trajectories_ODE_of_mem (v := fun _ => scaled a pt w)
    (s := fun t => closedBall (scale (inv w) (P t)) ρ) (K := ⟨K,hK⟩) (εf := 0) (εg := δ) (δ := e0)
    (fun t ht => hlip t (Ico_subset_Icc_self ht)) (HasDerivWithinAt.continuousOn hsol)
    (hright hsol) (fun t _ => by simp)
    (fun t ht => by simpa [mem_closedBall,dist_eq_norm] using (show _ ≤ ρ from hbound t (Ico_subset_Icc_self ht)))
    (HasDerivWithinAt.continuousOn hQ) (hright hQ)
    (fun t ht => by rw [dist_comm,dist_eq_norm]; exact hdef t (Ico_subset_Icc_self ht))
    (fun t ht => mem_closedBall_self hρ)
    (by rw [hsol0,dist_eq_norm]; exact hx0)
  refine ⟨fun t => scale w (sol t),?_,?_,?_,?_⟩
  · simp [hsol0,scale_inv hw]
  · intro t ht
    have hd := (scale w).hasFDerivAt.comp_hasDerivWithinAt t (hsol t ht)
    simpa [scaled,scale_inv hw,Function.comp_def] using hd
  · intro t ht i
    exact hball t (sol t) (by simpa [mem_closedBall,dist_eq_norm] using (show _ ≤ ρ from hbound t ht)) i
  · intro t ht i
    have hg := hgron t ht
    simp only [sub_zero,zero_add] at hg
    exact weighted_ball hw (dist_nonneg.trans hg) (P t) (sol t) (by rwa [dist_eq_norm] at hg) i

end BlackHole.StepField
