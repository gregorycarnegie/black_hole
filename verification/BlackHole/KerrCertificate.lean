module
public import BlackHole.KerrArithmetic
public import BlackHole.ValidatedStep
public import BlackHole.NormalizedJet

@[expose] public section
noncomputable section
open Set Metric
open scoped ContDiff NNReal
namespace BlackHole.KerrField

/-- A segment certificate for the actual Kerr equations. The local Jacobian
and residual bounds are numerical inputs; tube inclusion supplies exact
existence and containment, including the previously unknown trajectory. -/
theorem certified_segment (mass : ℝ) (a : Cartesian.Space)
    (proposal rate : ℝ → Phase) (x : Phase) (h : ℝ) (hh : 0 ≤ h)
    (initial radius defect K : ℝ≥0)
    (hproposal : ∀ t ∈ Icc 0 h, HasDerivWithinAt proposal (rate t) (Icc 0 h) t)
    (hrate : ContinuousOn rate (Icc 0 h))
    (hdomain : ∀ t ∈ Icc 0 h, ∀ y ∈ closedBall (proposal t) radius,
      0 < Cartesian.radius a y.1)
    (hjacobian : ∀ t ∈ Icc 0 h, ∀ y ∈ closedBall (proposal t) radius,
      ‖fderiv ℝ (phaseRhs mass a) y‖ ≤ K)
    (hdefect : ∀ t ∈ Icc 0 h, ‖phaseRhs mass a (proposal t)-rate t‖ ≤ defect)
    (hx : ‖x-proposal 0‖ ≤ initial)
    (hinclude : initial+h*(defect+K*radius) ≤ radius) :
    ∃ sol : ℝ → Phase, sol 0 = x ∧
      (∀ t ∈ Icc 0 h, HasDerivWithinAt sol (phaseRhs mass a (sol t)) (Icc 0 h) t) ∧
      ∀ t ∈ Icc 0 h, ‖sol t-proposal t‖ ≤ radius := by
  apply ValidatedStep.exists_solution_in_tube (phaseRhs mass a) proposal rate x h hh
    initial radius defect K hproposal _ _ hdefect hx hinclude
  · have hp : ContinuousOn proposal (Icc 0 h) := HasDerivWithinAt.continuousOn hproposal
    have hpath : ContinuousOn (fun z : ℝ × Phase => proposal z.1+z.2)
        ((Icc 0 h) ×ˢ closedBall 0 (radius:ℝ)) :=
      (hp.comp continuousOn_fst (fun _ hz => hz.1)).add continuousOn_snd
    have hf : ContinuousOn (phaseRhs mass a) {y | 0 < Cartesian.radius a y.1} :=
      fun y hy => (phase_rhs_smooth mass a y hy).continuousAt.continuousWithinAt
    apply (hf.comp hpath _).sub (hrate.comp continuousOn_fst (fun _ hz => hz.1))
    intro z hz
    apply hdomain z.1 hz.1
    simpa [mem_closedBall,dist_eq_norm] using hz.2
  · intro t ht
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun y hy => (phase_rhs_smooth mass a y (hdomain t ht y hy)).differentiableAt (by simp))
      (fun y hy => ?_) (convex_closedBall (proposal t) (radius:ℝ))
    exact_mod_cast hjacobian t ht y hy

end BlackHole.KerrField
