module

public import BlackHole.KerrInverse
public import BlackHole.ADM
import Mathlib.LinearAlgebra.Matrix.DotProduct

@[expose] public section
noncomputable section

namespace BlackHole.KerrField

theorem spatial_metric_form (mass : ℝ) (a x v : Cartesian.Space) :
    ADM.spatial (metric mass a x) v v = dotProduct v v+
      2*Cartesian.potential mass a x*(dotProduct (Cartesian.spatialEll a x) v)^2 := by
  simp [ADM.spatial, metric, Cartesian.metric, Cartesian.eta, Cartesian.ell,
    dotProduct, Fin.sum_univ_succ]
  ring

theorem spatial_metric_positive (mass : ℝ) (a x v : Cartesian.Space)
    (hm : 0 ≤ mass) (hr : 0 < Cartesian.radius a x) (hv : v ≠ 0) :
    0 < ADM.spatial (metric mass a x) v v := by
  have hne : dotProduct v v ≠ 0 := fun hz => hv (dotProduct_self_eq_zero.mp hz)
  have hpos : 0 < dotProduct v v := lt_of_le_of_ne
    (Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))) (Ne.symm hne)
  rw [spatial_metric_form]
  have hH := potential_nonnegative mass a x hm hr
  nlinarith [sq_nonneg (dotProduct (Cartesian.spatialEll a x) v)]

/-- The camera's unit observer, past null initialization and unit energy
    hold for the actual exact Kerr source with nonnegative mass and r>0. -/
theorem camera_initialization (mass : ℝ) (a x direction : Cartesian.Space)
    (hm : 0 ≤ mass) (hr : 0 < Cartesian.radius a x)
    (hdir : ADM.spatial (metric mass a x) direction direction = 1) :
    let g := metric mass a x
    let inv := g⁻¹
    0 < ADM.observer inv 0 ∧
      dotProduct (ADM.observer inv) (g.mulVec (ADM.observer inv)) = -1 ∧
      dotProduct (g.mulVec (ADM.pastTangent inv direction)) (ADM.observer inv) = 1 ∧
      ADM.norm g (-1/ADM.lapse inv) (direction+(1/ADM.lapse inv) • ADM.shift inv) = 0 := by
  let g := metric mass a x
  have hinv : g*g⁻¹ = 1 := Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (metric_nonsingular mass a x hr))
  have h00 := inverse_time_negative mass a x hm hr
  exact ⟨ADM.observer_future g⁻¹ h00, ADM.observer_unit_timelike g g⁻¹ hinv h00,
    ADM.initialized_energy g g⁻¹ hinv (metric_symmetric mass a x) h00 direction,
    ADM.initialized_null g g⁻¹ hinv (metric_symmetric mass a x) h00 direction hdir⟩

end BlackHole.KerrField
