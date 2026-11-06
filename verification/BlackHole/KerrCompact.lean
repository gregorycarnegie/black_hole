module

public import BlackHole.KerrSmoothness
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Tactic.FunProp

/-! Uniform bounds for the full Kerr geodesic/screen field on compact exterior
phase regions (N2). These bounds exist; their numerical values and invariance
of the region under the production solver are separate obligations. -/

@[expose] public section
noncomputable section

open Set Metric
open scoped NNReal

namespace BlackHole.KerrField

theorem positive_phase_domain_open (a : Cartesian.Space) :
    IsOpen {y : Phase | 0 < Cartesian.radius a y.1} := by
  apply isOpen_iff_mem_nhds.mpr
  intro y hy
  have hc : ContinuousAt (fun z : Phase => Cartesian.radius a z.1) y :=
    (Cartesian.radius_smooth a y.1 hy).continuousAt.comp continuousAt_fst
  exact hc.eventually (eventually_gt_nhds hy)

/-- Every derivative order of the actual field is uniformly bounded on any
compact set of nonsingular phase points. No convexity assumption is needed. -/
theorem phase_rhs_derivatives_bounded (mass : ℝ) (a : Cartesian.Space)
    {s : Set Phase} (hs : IsCompact s)
    (hr : ∀ state ∈ s, 0 < Cartesian.radius a state.1) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ state ∈ s,
      ‖iteratedFDeriv ℝ n (phaseRhs mass a) state‖ ≤ M := by
  have hc : ContinuousOn (iteratedFDeriv ℝ n (phaseRhs mass a)) s :=
    fun state hstate => ((phase_rhs_smooth mass a state (hr state hstate)).continuousAt_iteratedFDeriv
      (by simp)).continuousWithinAt
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuousOn hc
  exact ⟨max M 0, le_max_right _ _, fun state hstate =>
    (hM state hstate).trans (le_max_left _ _)⟩

/-- Local smoothness yields a single Lipschitz constant on a compact exterior
set, including sets that are not convex around the excised black hole. -/
theorem phase_rhs_compact_lipschitz (mass : ℝ) (a : Cartesian.Space)
    {s : Set Phase} (hs : IsCompact s)
    (hr : ∀ state ∈ s, 0 < Cartesian.radius a state.1) :
    ∃ K : ℝ≥0, LipschitzOnWith K (phaseRhs mass a) s := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hs
  intro state hstate
  obtain ⟨K, t, ht, hlip⟩ := phase_rhs_locally_lipschitz mass a state (hr state hstate)
  exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hlip⟩

/-- Bounded position, momentum and screen, separated from the Kerr singularity.
The norm on each finite vector is the maximum component norm. -/
def phaseRegion (a : Cartesian.Space) (ρ R P F : ℝ) : Set Phase :=
  (closedBall 0 R ×ˢ (closedBall 0 P ×ˢ closedBall 0 F)) ∩
    {state | ρ ≤ Cartesian.radius a state.1}

theorem phaseRegion_compact (a : Cartesian.Space) (ρ R P F : ℝ) :
    IsCompact (phaseRegion a ρ R P F) := by
  have hc : Continuous (fun state : Phase => Cartesian.radius a state.1) := by
    unfold Cartesian.radius Cartesian.q Cartesian.b Calculus.kerrRadius dotProduct
    fun_prop
  exact ((isCompact_closedBall 0 R).prod
    ((isCompact_closedBall 0 P).prod (isCompact_closedBall 0 F))).inter_right
      (isClosed_le continuous_const hc)

/-- The bounded exterior region has uniform derivative and Lipschitz bounds
for the complete nonlinear Hamiltonian/parallel-screen system. -/
theorem phaseRegion_bounds (mass : ℝ) (a : Cartesian.Space) (ρ R P F : ℝ)
    (hρ : 0 < ρ) :
    (∀ n : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ state ∈ phaseRegion a ρ R P F,
      ‖iteratedFDeriv ℝ n (phaseRhs mass a) state‖ ≤ M) ∧
    ∃ K : ℝ≥0, LipschitzOnWith K (phaseRhs mass a) (phaseRegion a ρ R P F) := by
  have hs := phaseRegion_compact a ρ R P F
  have hr : ∀ state ∈ phaseRegion a ρ R P F, 0 < Cartesian.radius a state.1 :=
    fun _ hstate => hρ.trans_le hstate.2
  exact ⟨fun n => phase_rhs_derivatives_bounded mass a hs hr n,
    phase_rhs_compact_lipschitz mass a hs hr⟩

end BlackHole.KerrField
