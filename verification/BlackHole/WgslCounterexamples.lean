module

public import BlackHole.WgslExpr
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.Real.Pi.Bounds

/-! Accuracy gaps in the WGSL specification reached by the unchanged shaders
(obligation F2).

WGSL bounds `atan2(y, x)` to 4096 ULP only "for `|x|` in the range
`[2⁻¹²⁶, 2¹²⁶]`, and `y` is finite and normal", and leaves accuracy undefined
outside a specified range. `acos(x)` is "the worse of absolute error
`6.77·10⁻⁵`" and inheritance from `atan2(sqrt(1.0 - x * x), x)`, where the
inner `x * x`, `1.0 - ·` and `sqrt` follow their own accuracy rules.

The theorems below show that on such inputs a conforming implementation may
return binary32 values far from the exact angle:

* `atan2(0, x)` may return `0` or `4` for every `x`, so its error can be at
  least 2 (`atan2_zero_y_far`), and the skybox longitude
  `atan2(dir.z, dir.x)/(2π)+0.5` can be off by at least `1/π` for rays with
  `dir.z = 0` (`skybox_longitude_gap`).
* `acos(0)` may return `0` or `3`, both at least `1.4` from `π/2`
  (`acos_zero_far`). The inner `sqrt(1 - 0*0)` is required to be accurate;
  the gap comes from `atan2` at `x = 0`.

So the former `sample_skybox` (`dir.z = 0` or `dir.y = 0`), `polarization_color`
view 2 (`pol.y = 0`) and warped-disk plasma (`pos.z = 0`) had no useful bound
on every conforming implementation. The shader now avoids these gaps: the
skybox uses the arithmetic `atan2_arith` (`WgslAtan2`: within `128u`, with
texture-coordinate bounds `skybox_longitude_error` and
`skybox_latitude_error`), and the polarization hue and warped midplane use
exact trigonometric identities with no angle (`WgslPlasma`). -/

@[expose] public section
noncomputable section

namespace BlackHole.WgslCounterexamples
open Wgsl WgslExpr

/-- Values representable in binary32 that the counterexamples use. -/
def Binary32 (r : ℝ) : Prop := ∃ m e : ℤ, |m| < 2^24 ∧ r = m*2^e

/-- Finite, normal binary32 magnitude. -/
def Normal32 (y : ℝ) : Prop := 1/2^126 ≤ |y| ∧ |y| ≤ 2^128

/-- The WGSL accuracy requirement on a computed `atan2(y, x)`. -/
def Atan2Acc (y x r : ℝ) : Prop :=
  (1/2^126 ≤ |x| ∧ |x| ≤ 2^126 ∧ Normal32 y) →
    |r-Complex.arg ⟨x,y⟩| ≤ 4096*ulp (Complex.arg ⟨x,y⟩)

/-- The WGSL accuracy requirement on a computed `sqrt(t)` for positive `t`,
inherited from `1.0 / inverseSqrt(t)` (`Wgsl.sqrt_inherited`). -/
def SqrtAcc (t s : ℝ) : Prop := 0 < t ∧ |s-Real.sqrt t| ≤ 10*u*Real.sqrt t+η

/-- The WGSL accuracy requirement on a computed `acos(x)`: within `6.77·10⁻⁵`,
or a result of the inherited `atan2(sqrt(1.0 - x * x), x)` whose
intermediate values each satisfy their own accuracy rule. -/
def AcosAcc (x r : ℝ) : Prop :=
  |r-Real.arccos x| ≤ 677/10^7 ∨
    ∃ xx t s, Rnd (x*x) xx ∧ Rnd (1-xx) t ∧ SqrtAcc t s ∧ Atan2Acc s x r

theorem atan2_zero_y (x r : ℝ) : Atan2Acc 0 x r := by
  intro ⟨_,_,hn,_⟩
  norm_num at hn

theorem atan2_tiny_x (y x r : ℝ) (hx : |x| < 1/2^126) : Atan2Acc y x r := by
  intro ⟨h,_⟩
  linarith

theorem binary32_zero : Binary32 0 := ⟨0,0,by norm_num,by norm_num⟩
theorem binary32_small (n : ℕ) (hn : n < 2^24) : Binary32 n :=
  ⟨n,0,by rw [abs_of_nonneg (by positivity)]; exact_mod_cast hn,by simp⟩

/-- Both `0` and `4` are admissible binary32 results of `atan2(0, x)`, so the
error can be at least 2 for every `x`. -/
theorem atan2_zero_y_far (x : ℝ) :
    ∃ r, Binary32 r ∧ Atan2Acc 0 x r ∧ 2 ≤ |r-Complex.arg ⟨x,0⟩| := by
  by_cases h : 2 ≤ |0-Complex.arg ⟨x,0⟩|
  · exact ⟨0,binary32_zero,atan2_zero_y _ _,h⟩
  · refine ⟨4,by exact_mod_cast binary32_small 4 (by norm_num),atan2_zero_y _ _,?_⟩
    have := abs_sub_abs_le_abs_sub (4:ℝ) (Complex.arg ⟨x,0⟩)
    norm_num at this h ⊢
    linarith

/-- For rays with `dir.z = 0`, some conforming result makes the skybox
longitude `atan2(dir.z, dir.x)/(2π)+0.5` wrong by at least `1/π`. -/
theorem skybox_longitude_gap (dirx : ℝ) :
    ∃ r, Binary32 r ∧ Atan2Acc 0 dirx r ∧
      1/Real.pi ≤ |r/(2*Real.pi)+1/2-(Complex.arg ⟨dirx,0⟩/(2*Real.pi)+1/2)| := by
  obtain ⟨r,hb,ha,hd⟩ := atan2_zero_y_far dirx
  refine ⟨r,hb,ha,?_⟩
  have hpi := Real.pi_pos
  have h2 : 0 < 2*Real.pi := by linarith
  rw [show r/(2*Real.pi)+1/2-(Complex.arg ⟨dirx,0⟩/(2*Real.pi)+1/2) =
    (r-Complex.arg ⟨dirx,0⟩)/(2*Real.pi) by ring,abs_div,abs_of_pos h2]
  calc 1/Real.pi = 2/(2*Real.pi) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hd h2.le

/-- Both `0` and `3` are admissible binary32 results of `acos(0)`, with every
intermediate of the inherited expression accurate; each is at least `1.4`
from the exact `π/2`. -/
theorem acos_zero_far :
    AcosAcc 0 0 ∧ AcosAcc 0 3 ∧ 14/10 ≤ |0-Real.arccos 0| ∧ 14/10 ≤ |3-Real.arccos 0| := by
  have hinner (r : ℝ) : AcosAcc 0 r := by
    refine Or.inr ⟨0,1,1,?_,?_,⟨by norm_num,?_⟩,atan2_tiny_x 1 0 r (by norm_num)⟩
    · unfold Rnd; have := η_pos; simp; positivity
    · unfold Rnd; have := η_pos; have := u_pos; norm_num; positivity
    · have := η_pos; have := u_pos; simp; positivity
  refine ⟨hinner 0,hinner 3,?_,?_⟩ <;> rw [Real.arccos_zero]
  · rw [zero_sub,abs_neg,abs_of_pos (by linarith [Real.pi_pos])]; linarith [Real.pi_gt_three]
  · rw [abs_of_pos (by linarith [Real.pi_lt_d2])]; linarith [Real.pi_lt_d2]

/-- The model is not vacuous: on an input inside the specified range,
`acos(1/2)` may not return `3`. -/
theorem acos_half_constrained : ¬ AcosAcc (1/2) 3 := by
  have hu := u_pos; have hη := η_pos
  have hu' : u = 1/2^24 := rfl; have hη' : η = 1/2^126 := rfl
  rintro (h | ⟨xx,t,s,hxx,ht,⟨ht0,hs⟩,ha⟩)
  · have h1 : Real.arccos (1/2) ≤ Real.pi/2 := by
      rw [Real.arccos]; linarith [Real.arcsin_nonneg.mpr (by norm_num : (0:ℝ) ≤ 1/2)]
    have := (abs_le.mp h).2
    linarith [Real.pi_lt_d2]
  · unfold Rnd at hxx ht
    have hxx' := abs_le.mp hxx
    have ht' := abs_le.mp ht
    rw [hu',hη'] at hxx' ht' hs
    norm_num at hxx'
    have hx1 : |1-xx| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have htt : |t-(1-xx)| ≤ 1/2^24+1/2^126 := by
      have := mul_le_mul_of_nonneg_left hx1 (by norm_num : (0:ℝ) ≤ 1/2^24)
      have h0 : |t-(1-xx)| ≤ 1/2^24*|1-xx|+1/2^126 := by rw [← hu',← hη']; exact ht
      linarith
    have htt' := abs_le.mp htt
    have htl : 7/10 ≤ t := by linarith
    have htu : t ≤ 8/10 := by linarith
    have hst : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
    have hsl : 8/10 ≤ Real.sqrt t := by
      rw [show (8/10:ℝ) = Real.sqrt ((8/10)^2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hs' := abs_le.mp hs
    have hsl' : 1/2 ≤ s := by nlinarith
    have hsu : s ≤ 2 := by nlinarith
    have hnorm : Normal32 s := ⟨by rw [abs_of_pos (by linarith)]; norm_num; linarith,
      by rw [abs_of_pos (by linarith)]; norm_num; linarith⟩
    have hacc := ha ⟨by norm_num,by norm_num,hnorm⟩
    have harg : |Complex.arg ⟨1/2,s⟩| ≤ Real.pi/2 :=
      Complex.abs_arg_le_pi_div_two_iff.mpr (by norm_num)
    unfold ulp at hacc
    rw [hu',hη'] at hacc
    have h1 := abs_le.mp harg
    have h2 := abs_le.mp hacc
    nlinarith [Real.pi_lt_d2,Real.pi_pos]

end BlackHole.WgslCounterexamples
