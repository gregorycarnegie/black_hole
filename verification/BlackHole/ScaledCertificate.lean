module
public import BlackHole.ValidatedStep
public import Mathlib.Topology.Algebra.Module.Equiv.Prod

@[expose] public section
noncomputable section
open Set Metric
open scoped NNReal
namespace BlackHole.ValidatedStep

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def scaledField (S : E ≃L[ℝ] E) (f : E → E) (z : E) : E := S (f (S.symm z))

omit [CompleteSpace E] in
theorem unscale_solution (S : E ≃L[ℝ] E) (f : E → E) (curve : ℝ → E)
    (s : Set ℝ) (t : ℝ)
    (hcurve : HasDerivWithinAt curve (scaledField S f (curve t)) s t) :
    HasDerivWithinAt (fun u => S.symm (curve u)) (f (S.symm (curve t))) s t := by
  have h := S.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t hcurve
  simpa [scaledField,Function.comp_def] using h

/-- The conserved parameter's uncertainty enters as a fixed forcing term.
It is never multiplied into a fictitious evolving parameter error. Scaling
may be any invertible continuous linear map, including the runtime weights. -/
theorem parameterized_segment (f : ℝ → E → E) (S : E ≃L[ℝ] E)
    (nominal parameter : ℝ) (proposal rate : ℝ → E) (x : E)
    (h : ℝ) (hh : 0 ≤ h) (initial radius defect forcing K : ℝ≥0)
    (hproposal : ∀ t ∈ Icc 0 h, HasDerivWithinAt proposal (rate t) (Icc 0 h) t)
    (hcontinuous : ContinuousOn
      (fun z : ℝ × E => scaledField S (f parameter) (proposal z.1+z.2)-rate z.1)
      ((Icc 0 h) ×ˢ closedBall 0 radius))
    (hlip : ∀ t ∈ Icc 0 h,
      LipschitzOnWith K (scaledField S (f parameter)) (closedBall (proposal t) radius))
    (hdefect : ∀ t ∈ Icc 0 h,
      ‖scaledField S (f nominal) (proposal t)-rate t‖ ≤ defect)
    (hparameter : ∀ t ∈ Icc 0 h,
      ‖S (f parameter (S.symm (proposal t))-f nominal (S.symm (proposal t)))‖ ≤ forcing)
    (hx : ‖S x-proposal 0‖ ≤ initial)
    (hinclude : initial+h*(defect+forcing+K*radius) ≤ radius) :
    ∃ sol : ℝ → E, sol 0 = x ∧
      (∀ t ∈ Icc 0 h, HasDerivWithinAt sol (f parameter (sol t)) (Icc 0 h) t) ∧
      ∀ t ∈ Icc 0 h, ‖S (sol t)-proposal t‖ ≤ radius := by
  have hr (t : ℝ) (ht : t ∈ Icc 0 h) :
      ‖scaledField S (f parameter) (proposal t)-rate t‖ ≤ (defect+forcing:ℝ≥0) := by
    calc
      _ ≤ ‖scaledField S (f parameter) (proposal t)-scaledField S (f nominal) (proposal t)‖+
          ‖scaledField S (f nominal) (proposal t)-rate t‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (forcing:ℝ)+defect := by
        apply add_le_add _ (hdefect t ht)
        simpa [scaledField,map_sub] using hparameter t ht
      _ = _ := by simp [add_comm]
  obtain ⟨curve,hzero,hsol,hbound⟩ := exists_solution_in_tube
    (scaledField S (f parameter)) proposal rate (S x) h hh initial radius (defect+forcing) K
      hproposal hcontinuous hlip hr hx (by simpa using hinclude)
  refine ⟨fun t => S.symm (curve t), ?_, ?_, ?_⟩
  · simp [hzero]
  · intro t ht
    exact unscale_solution S (f parameter) curve _ t (hsol t ht)
  · intro t ht
    simpa using hbound t ht

end BlackHole.ValidatedStep
