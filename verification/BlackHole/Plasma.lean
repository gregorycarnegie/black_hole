module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section

namespace BlackHole.Plasma

theorem evpa_numerator_norm (bx by_ : ℝ) :
    (by_^2-bx^2)^2+(-2*bx*by_)^2 = (bx^2+by_^2)^2 := by ring

/-- The production source has synchrotron polarization fraction 3/4 and
    unpolarized thermal emission. Normalize its direction before clipping
    the perpendicular emissivity, so frame error cannot amplify polarization. -/
theorem emission_stokes_cone (bx by_ thermal synch eps : ℝ)
    (hthermal : 0 ≤ thermal) (hsynch : 0 ≤ synch) (heps : 0 < eps) :
    let den := max (bx^2+by_^2) eps
    let q := (3/4)*synch*(by_^2-bx^2)/den
    let u := (3/4)*synch*(-2*bx*by_)/den
    0 ≤ thermal+synch ∧ q^2+u^2 ≤ (thermal+synch)^2 := by
  dsimp
  let den := max (bx^2+by_^2) eps
  have hd : 0 < den := lt_of_lt_of_le heps (le_max_right _ _)
  have hn : (bx^2+by_^2)^2 ≤ den^2 := by
    have hl : bx^2+by_^2 ≤ den := le_max_left _ _
    nlinarith
  have hsmall : ((3/4 : ℝ)*synch)^2 ≤ (thermal+synch)^2 := by
    nlinarith [sq_nonneg thermal, mul_nonneg hthermal hsynch, sq_nonneg synch]
  constructor
  · linarith
  · change ((3/4)*synch*(by_^2-bx^2)/den)^2 +
      ((3/4)*synch*(-2*bx*by_)/den)^2 ≤ _
    have hid : ((3/4)*synch*(by_^2-bx^2)/den)^2 +
        ((3/4)*synch*(-2*bx*by_)/den)^2 =
        ((3/4)*synch)^2*(bx^2+by_^2)^2/den^2 := by
      field_simp
      ring
    rw [hid]
    apply (div_le_iff₀ (sq_pos_of_pos hd)).2
    calc
      _ ≤ (thermal+synch)^2*(bx^2+by_^2)^2 :=
        mul_le_mul_of_nonneg_right hsmall (sq_nonneg _)
      _ ≤ (thermal+synch)^2*den^2 := mul_le_mul_of_nonneg_left hn (sq_nonneg _)

theorem redshift_boost_positive (redshift : ℝ) (h : 0 < redshift) : 0 < redshift^3 :=
  pow_pos h 3

def clampedRedshift (energy : ℝ) : ℝ :=
  min (max (1/max energy (1/100000)) (1/100)) 20

theorem clamped_redshift_bounds (energy : ℝ) :
    (1/100 : ℝ) ≤ clampedRedshift energy ∧ clampedRedshift energy ≤ 20 := by
  constructor
  · exact le_min (le_max_right _ _) (by norm_num)
  · exact min_le_right _ _

theorem clamped_redshift_inactive (energy : ℝ) (hlo : 1/20 ≤ energy) (hhi : energy ≤ 100) :
    clampedRedshift energy = 1/energy := by
  have he : 0 < energy := by linarith
  have hfloor : (1/100000 : ℝ) ≤ energy := by linarith
  have hlo' : (1/100 : ℝ) ≤ 1/energy := (le_div_iff₀ he).2 (by nlinarith)
  have hhi' : 1/energy ≤ (20 : ℝ) := (div_le_iff₀ he).2 (by nlinarith)
  simp only [clampedRedshift, max_eq_left hfloor, max_eq_left hlo', min_eq_left hhi']

/-- The cubic intensity law follows algebraically from invariant I_nu/nu^3.
    Conservation of that invariant is a separate physical transport premise. -/
theorem invariant_intensity_redshift (observed emitted nuObserved nuEmitted : ℝ)
    (ho : nuObserved ≠ 0) (he : nuEmitted ≠ 0)
    (hinvariant : observed/nuObserved^3 = emitted/nuEmitted^3) :
    observed = (nuObserved/nuEmitted)^3*emitted := by
  have h := (div_eq_div_iff (pow_ne_zero 3 ho) (pow_ne_zero 3 he)).mp hinvariant
  rw [div_pow, div_mul_eq_mul_div]
  apply (eq_div_iff (pow_ne_zero 3 he)).2
  simpa only [mul_comm] using h

theorem emissivity_luminance_nonneg (r g b : ℝ) (hr : 0 ≤ r) (hg : 0 ≤ g) (hb : 0 ≤ b) :
    0 ≤ (2126/10000 : ℝ)*r+(7152/10000)*g+(722/10000)*b := by positivity

end BlackHole.Plasma
