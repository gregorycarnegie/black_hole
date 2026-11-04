module

public import BlackHole.KerrPath
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic.FunProp

@[expose] public section
noncomputable section
open scoped ContDiff Topology NNReal
namespace BlackHole.Cartesian

theorem q_smooth (a x : Space) : ContDiffAt ℝ ∞ (q a) x := by
  unfold q dotProduct
  fun_prop

theorem b_smooth (a x : Space) : ContDiffAt ℝ ∞ (b a) x := by
  unfold b dotProduct
  fun_prop

theorem radius_smooth (a x : Space) (hr : 0 < radius a x) :
    ContDiffAt ℝ ∞ (radius a) x := by
  obtain ⟨hdisc,hroot⟩ := positive_radius_domain a x hr
  have hq := q_smooth a x
  have hb := b_smooth a x
  have hc (c : ℝ) : ContDiffAt ℝ ∞ (fun _ : Space => c) x := contDiffAt_const
  have hd := ((hq.pow 2).add ((hc 4).mul (hb.pow 2))).sqrt (ne_of_gt hdisc)
  exact ((hq.add hd).div (hc 2) (by norm_num)).sqrt (ne_of_gt hroot)

theorem potential_smooth (mass : ℝ) (a x : Space) (hr : 0 < radius a x) :
    ContDiffAt ℝ ∞ (potential mass a) x := by
  have hrad := radius_smooth a x hr
  have hb := b_smooth a x
  have hd : radius a x^4+b a x^2 ≠ 0 := ne_of_gt (by positivity)
  have hm : ContDiffAt ℝ ∞ (fun _ : Space => mass) x := contDiffAt_const
  exact (hm.mul (hrad.pow 3)).div ((hrad.pow 4).add (hb.pow 2)) hd

theorem spatialEll_smooth (a x : Space) (hr : 0 < radius a x) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => spatialEll a y i) x := by
  have hrad := radius_smooth a x hr
  have hb := b_smooth a x
  have hc : ContDiffAt ℝ ∞ (fun y : Space => y i) x := by fun_prop
  have hcross : ContDiffAt ℝ ∞ (fun y : Space => crossProduct a y i) x := by
    fin_cases i <;> simp [cross_apply] <;> fun_prop
  have haa : 0 ≤ dotProduct a a := Finset.sum_nonneg (fun j _ => mul_self_nonneg (a j))
  have hd : radius a x^2+dotProduct a a ≠ 0 := ne_of_gt (by positivity)
  have hconst (c : ℝ) : ContDiffAt ℝ ∞ (fun _ : Space => c) x := contDiffAt_const
  exact (((hrad.mul hc).sub hcross).add ((hb.div hrad (ne_of_gt hr)).mul (hconst (a i)))).div
    ((hrad.pow 2).add (hconst (dotProduct a a))) hd

theorem ell_smooth (a x : Space) (hr : 0 < radius a x) (i : Fin 4) :
    ContDiffAt ℝ ∞ (fun y => ell a y i) x := by
  cases i using Fin.cases with
  | zero => simpa only [ell,Fin.cases_zero] using (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Space => (1 : ℝ)) x)
  | succ i => exact spatialEll_smooth a x hr i

theorem metric_smooth (mass : ℝ) (a x : Space) (hr : 0 < radius a x) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun y => metric mass a y i j) x := by
  have hconst (c : ℝ) : ContDiffAt ℝ ∞ (fun _ : Space => c) x := contDiffAt_const
  exact (hconst (eta i j)).add
    ((((hconst 2).mul (potential_smooth mass a x hr)).mul (ell_smooth a x hr i)).mul
      (ell_smooth a x hr j))

theorem radiusD_smooth (a x : Space) (hr : 0 < radius a x) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => radiusD a y i) x := by
  have hrad := radius_smooth a x hr
  have hb := b_smooth a x
  have hq := q_smooth a x
  have hr0 := ne_of_gt hr
  have hd : 2*radius a x^2-q a x ≠ 0 := by
    rw [radial_den_optical a x hr]
    exact ne_of_gt (sigma_positive a x hr)
  unfold radiusD
  fun_prop (disch := assumption)

theorem potentialD_smooth (mass : ℝ) (a x : Space) (hr : 0 < radius a x) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => potentialD mass a y i) x := by
  have hrad := radius_smooth a x hr
  have hb := b_smooth a x
  have hH := potential_smooth mass a x hr
  have hdr := radiusD_smooth a x hr i
  have hr0 := ne_of_gt hr
  have hd : radius a x^4+b a x^2 ≠ 0 := ne_of_gt (by positivity)
  unfold potentialD
  fun_prop (disch := assumption)

theorem spatialEllD_smooth (a x : Space) (hr : 0 < radius a x) (e i : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => spatialEllD a y e i) x := by
  have hrad := radius_smooth a x hr
  have hb := b_smooth a x
  have hdr := radiusD_smooth a x hr e
  have hl := spatialEll_smooth a x hr i
  have hr0 := ne_of_gt hr
  have hr2 : radius a x^2 ≠ 0 := pow_ne_zero 2 hr0
  have haa : 0 ≤ dotProduct a a := Finset.sum_nonneg (fun j _ => mul_self_nonneg (a j))
  have hd : radius a x^2+dotProduct a a ≠ 0 := ne_of_gt (by positivity)
  unfold spatialEllD
  fun_prop (disch := assumption)

theorem ellD_smooth (a x : Space) (hr : 0 < radius a x) (e : Fin 3) (i : Fin 4) :
    ContDiffAt ℝ ∞ (fun y => ellD a y e i) x := by
  cases i using Fin.cases with
  | zero => simpa only [ellD,Fin.cases_zero] using (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Space => (0 : ℝ)) x)
  | succ i => exact spatialEllD_smooth a x hr e i

theorem metricD_smooth (mass : ℝ) (a x : Space) (hr : 0 < radius a x) (e : Fin 3) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun y => metricD mass a y e i j) x := by
  have hH := potential_smooth mass a x hr
  have hHD := potentialD_smooth mass a x hr e
  have hi := ell_smooth a x hr i
  have hj := ell_smooth a x hr j
  have hdi := ellD_smooth a x hr e i
  have hdj := ellD_smooth a x hr e j
  unfold metricD
  fun_prop

end BlackHole.Cartesian

namespace BlackHole.KerrField

theorem explicitInverse_smooth (mass : ℝ) (a x : Cartesian.Space)
    (hr : 0 < Cartesian.radius a x) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun y => explicitInverse mass a y i j) x := by
  have hH := Cartesian.potential_smooth mass a x hr
  have hi := Cartesian.ell_smooth a x hr i
  have hj := Cartesian.ell_smooth a x hr j
  simp only [explicitInverse,Matrix.sub_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,
    smul_eq_mul,raisedEll]
  fun_prop

theorem inverse_smooth (mass : ℝ) (a x : Cartesian.Space)
    (hr : 0 < Cartesian.radius a x) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun y => (metric mass a y)⁻¹ i j) x := by
  have hnear := (Cartesian.radius_smooth a x hr).continuousAt.eventually (eventually_gt_nhds hr)
  apply (explicitInverse_smooth mass a x hr i j).congr_of_eventuallyEq
  filter_upwards [hnear] with y hy
  exact congrArg (fun m : Matrix (Fin 4) (Fin 4) ℝ => m i j) (inverse_eq_explicit mass a y hy)

abbrev Phase := Cartesian.Space × (Fin 4 → ℝ) × (Fin 4 → ℝ)

def phaseRhs (mass : ℝ) (a : Cartesian.Space) (state : Phase) : Phase :=
  let x := state.1
  let p := state.2.1
  let screen := state.2.2
  let inv := (metric mass a x)⁻¹
  let dg := metricD mass a x
  let k := inv.mulVec p
  ((fun i => k i.succ), Transport.momentumForce dg k,
    fun i => -(∑ c, Transport.contractedConnection inv dg k i c*screen c))

set_option maxHeartbeats 2000000 in
/-- The actual continuous Hamiltonian and parallel-screen RHS is infinitely
    differentiable at every nonsingular Kerr phase point. -/
theorem phase_rhs_smooth (mass : ℝ) (a : Cartesian.Space) (state : Phase)
    (hr : 0 < Cartesian.radius a state.1) :
    ContDiffAt ℝ ∞ (phaseRhs mass a) state := by
  have hi (i j : Fin 4) : ContDiffAt ℝ ∞ (fun s : Phase => (metric mass a s.1)⁻¹ i j) state :=
    (inverse_smooth mass a state.1 hr i j).comp state contDiffAt_fst
  have hd (e i j : Fin 4) : ContDiffAt ℝ ∞ (fun s : Phase => metricD mass a s.1 e i j) state := by
    cases e using Fin.cases with
    | zero => simp only [metricD,Fin.cases_zero,Matrix.zero_apply]; fun_prop
    | succ e =>
      simpa only [metricD,Fin.cases_succ,Matrix.of_apply,Function.comp_def] using
        (Cartesian.metricD_smooth mass a state.1 hr e i j).comp state contDiffAt_fst
  have hk (i : Fin 4) : ContDiffAt ℝ ∞
      (fun s : Phase => ((metric mass a s.1)⁻¹).mulVec s.2.1 i) state := by
    have hp (j : Fin 4) : ContDiffAt ℝ ∞ (fun s : Phase => s.2.1 j) state := by fun_prop
    simpa only [Matrix.mulVec,dotProduct] using
      ContDiffAt.sum (s := Finset.univ) (fun j _ => (hi i j).mul (hp j))
  have hc (c : ℝ) : ContDiffAt ℝ ∞ (fun _ : Phase => c) state := contDiffAt_const
  have hl (d b c : Fin 4) : ContDiffAt ℝ ∞
      (fun s : Phase => Transport.loweredConnection (metricD mass a s.1) d b c) state :=
    (((hd b d c).add (hd c d b)).sub (hd d b c)).div (hc 2) (by norm_num)
  have hconnection (i c : Fin 4) : ContDiffAt ℝ ∞
      (fun s : Phase => Transport.contractedConnection (metric mass a s.1)⁻¹ (metricD mass a s.1)
        (((metric mass a s.1)⁻¹).mulVec s.2.1) i c) state := by
    simpa only [Transport.contractedConnection,Matrix.mulVec,dotProduct] using
      ContDiffAt.sum (s := Finset.univ) (fun d _ => (hi i d).mul
        (ContDiffAt.sum (s := Finset.univ) (fun b _ => (hl d b c).mul (hk b))))
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro i
    exact hk i.succ
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro i
    exact (ContDiffAt.sum (s := Finset.univ) (fun j _ =>
      ContDiffAt.sum (s := Finset.univ) (fun k _ =>
        ((hd i j k).mul (hk j)).mul (hk k)))).div (hc 2) (by norm_num)
  · apply contDiffAt_pi.mpr
    intro i
    have hs (c : Fin 4) : ContDiffAt ℝ ∞ (fun s : Phase => s.2.2 c) state := by fun_prop
    exact (ContDiffAt.sum (s := Finset.univ) (fun c _ =>
      (hconnection i c).mul (hs c))).neg

theorem phase_rhs_locally_lipschitz (mass : ℝ) (a : Cartesian.Space) (state : Phase)
    (hr : 0 < Cartesian.radius a state.1) :
    ∃ K : ℝ≥0, ∃ s ∈ 𝓝 state, LipschitzOnWith K (phaseRhs mass a) s := by
  have h1 : ContDiffAt ℝ 1 (phaseRhs mass a) state := (phase_rhs_smooth mass a state hr).of_le (by simp)
  exact h1.exists_lipschitzOnWith

theorem local_phase_solution (mass : ℝ) (a : Cartesian.Space) (state : Phase) (t0 : ℝ)
    (hr : 0 < Cartesian.radius a state.1) :
    ∃ curve : ℝ → Phase, curve t0 = state ∧ ∃ epsilon > (0 : ℝ),
      ∀ t ∈ Set.Ioo (t0-epsilon) (t0+epsilon),
        HasDerivAt curve (phaseRhs mass a (curve t)) t := by
  have h1 : ContDiffAt ℝ 1 (phaseRhs mass a) state := (phase_rhs_smooth mass a state hr).of_le (by simp)
  exact h1.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t0

end BlackHole.KerrField
