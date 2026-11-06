module
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

@[expose] public section
noncomputable section
namespace BlackHole.DirectionError
open Real InnerProductGeometry

/-- A chord enclosure also certifies the angular error, without a rounded
inverse trigonometric builtin in the acceptance test. -/
theorem angle_le_twice_chord {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x y : V) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : angle x y ≤ 2*‖x-y‖ := by
  let θ := angle x y
  let c := ‖x-y‖
  have ht0 : 0 ≤ θ := angle_nonneg x y
  have hc0 : 0 ≤ c := norm_nonneg _
  have htpi : θ ≤ π := angle_le_pi x y
  have hcos := cos_le_one_sub_mul_cos_sq (x := θ) (by rwa [abs_of_nonneg ht0])
  have hp2 : 0 < π^2 := by positivity
  have hm := mul_le_mul_of_nonneg_right hcos hp2.le
  have hsimp : (1-2/π^2*θ^2)*π^2 = π^2-2*θ^2 := by field_simp
  rw [hsimp] at hm
  have hnorm : c^2 = 2-2*cos θ := by
    dsimp [c,θ]
    rw [norm_sub_pow_two_real,hx,hy,inner_eq_cos_angle_of_norm_eq_one hx hy]
    ring
  have hnormmul := congrArg (fun z : ℝ => π^2*z) hnorm
  have hpi : π^2 ≤ 16 := by nlinarith [pi_lt_four,pi_pos]
  have hlarge := mul_le_mul_of_nonneg_right hpi (sq_nonneg c)
  nlinarith

end BlackHole.DirectionError
