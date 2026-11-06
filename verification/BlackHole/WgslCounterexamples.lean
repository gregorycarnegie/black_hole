module

public import BlackHole.WgslExpr
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Kernels with no all-input error bound under the WGSL specification
(obligation F2).

WGSL bounds `atan2(y, x)` to 4096 ULP only "for `|x|` in the range
`[2⁻¹²⁶, 2¹²⁶]`, and `y` is finite and normal", and states that accuracy is
undefined outside a specified range. `acos(x)` is "the worse of absolute
error `6.77·10⁻⁵`" and inheritance from `atan2(sqrt(1.0 - x * x), x)`.
`sqrt` is inherited from `1.0 / inverseSqrt(x)`, and `inverseSqrt(0)` is
infinite, which the Finite Math Assumption makes an indeterminate value.

So for `y = 0`, or `|x| < 2⁻¹²⁶`, every real number is an admissible
`atan2` result, and `acos(0)` may return anything. In `geodesic.wesl`:

* `sample_skybox` uses `atan2(dir.z, dir.x)` and `acos(clamp(dir.y,-1,1))`;
  every ray with `dir.z = 0` or `dir.y = 0` may sample any texel.
* `sample_plasma`'s warped disk (model 3) uses `atan2(pos.z, pos.x)`; at
  `pos.z = 0` the midplane twist angle, hence the disk height and density, is
  unconstrained.
* `polarization_color` uses `atan2(pol.y, pol.x)`; at `pol.y = 0` the hue is
  unconstrained.

These are display paths (skybox, polarization view) and the warped-disk
prescription. Guarding the arguments, or an arithmetic angle as `sincos`
did for sine and cosine, would be needed to give them any bound. -/

@[expose] public section
noncomputable section

namespace BlackHole.WgslCounterexamples
open Wgsl WgslExpr

/-- Finite, normal binary32 magnitude. -/
def Normal32 (y : ℝ) : Prop := 1/2^126 ≤ |y| ∧ |y| ≤ 2^128

/-- The WGSL accuracy requirement on a computed `atan2(y, x)`. -/
def Atan2Acc (y x r : ℝ) : Prop :=
  (1/2^126 ≤ |x| ∧ |x| ≤ 2^126 ∧ Normal32 y) →
    |r-Complex.arg ⟨x,y⟩| ≤ 4096*ulp (Complex.arg ⟨x,y⟩)

/-- The WGSL accuracy requirement on a computed `acos(x)`: within `6.77·10⁻⁵`,
or any result of the inherited `atan2(sqrt(1-x²), x)` from some admissible
`sqrt` value `s` (unconstrained when `1-x²` is zero). -/
def AcosAcc (x r : ℝ) : Prop :=
  |r-Real.arccos x| ≤ 677/10^7 ∨ ∃ s, Atan2Acc s x r

theorem atan2_zero_y (x r : ℝ) : Atan2Acc 0 x r := by
  intro ⟨_,_,hn,_⟩
  norm_num at hn

theorem atan2_tiny_x (y x r : ℝ) (hx : |x| < 1/2^126) : Atan2Acc y x r := by
  intro ⟨h,_⟩
  linarith

/-- Every real number is an admissible WGSL `acos(0)`. -/
theorem acos_zero (r : ℝ) : AcosAcc 0 r := Or.inr ⟨1,atan2_tiny_x 1 0 r (by norm_num)⟩

/-- No bound on the skybox longitude `atan2(dir.z, dir.x)/(2π)+0.5` holds for
rays in the plane `dir.z = 0`: each admissible `atan2` result, and hence every
longitude, is possible. -/
theorem skybox_longitude_unbounded (dirx : ℝ) (B : ℝ) :
    ∃ r, Atan2Acc 0 dirx r ∧ B < |r/(2*Real.pi)+1/2-(Complex.arg ⟨dirx,0⟩/(2*Real.pi)+1/2)| := by
  refine ⟨Complex.arg ⟨dirx,0⟩+2*Real.pi*(|B|+1),atan2_zero_y _ _,?_⟩
  have hpi := Real.pi_pos
  rw [show (Complex.arg ⟨dirx,0⟩+2*Real.pi*(|B|+1))/(2*Real.pi)+1/2-
      (Complex.arg ⟨dirx,0⟩/(2*Real.pi)+1/2) = |B|+1 by field_simp; ring]
  rw [abs_of_pos (by positivity)]
  linarith [le_abs_self B]

end BlackHole.WgslCounterexamples
