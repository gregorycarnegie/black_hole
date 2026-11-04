module

public import BlackHole.KerrInverse
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

@[expose] public section
noncomputable section

namespace BlackHole.Cartesian

def cosine (a x : Space) : ℝ := b a x/radius a x
def sigma (a x : Space) : ℝ := radius a x^2+cosine a x^2
def cosineD (a x : Space) (e : Fin 3) : ℝ :=
  (a e-cosine a x*radiusD a x e)/radius a x

theorem ell_spin_dot (a x : Space) (hr : 0 < radius a x) :
    dotProduct a (spatialEll a x) = cosine a x := by
  have hr0 := ne_of_gt hr
  have haa : 0 ≤ dotProduct a a := Finset.sum_nonneg (fun i _ => mul_self_nonneg (a i))
  have hd : radius a x^2+dotProduct a a ≠ 0 := by positivity
  simp only [dotProduct, Fin.sum_univ_succ] at hd
  simp [dotProduct, Fin.sum_univ_succ, spatialEll, cosine, b, cross_apply]
  field_simp
  ring

theorem ell_coordinates (a x : Space) (hr : 0 < radius a x) :
    radius a x • spatialEll a x+crossProduct a (spatialEll a x) = x := by
  have hr0 := ne_of_gt hr
  have haa : 0 ≤ dotProduct a a := Finset.sum_nonneg (fun i _ => mul_self_nonneg (a i))
  have hd : radius a x^2+dotProduct a a ≠ 0 := by positivity
  simp only [dotProduct, Fin.sum_univ_succ] at hd
  ext i
  fin_cases i <;>
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, spatialEll, b, cross_apply,
      dotProduct, Fin.sum_univ_succ] <;>
    field_simp <;> ring

theorem q_optical (a x : Space) (hr : 0 < radius a x) :
    q a x = radius a x^2-cosine a x^2 := by
  have hr0 := ne_of_gt hr
  have h := KerrField.radial_relation a x
  unfold cosine
  field_simp
  nlinarith

theorem radial_den_optical (a x : Space) (hr : 0 < radius a x) :
    2*radius a x^2-q a x = sigma a x := by
  rw [q_optical a x hr]
  unfold sigma
  ring

theorem sigma_positive (a x : Space) (hr : 0 < radius a x) : 0 < sigma a x := by
  unfold sigma
  positivity

theorem positive_radius_domain (a x : Space) (hr : 0 < radius a x) :
    0 < q a x^2+4*b a x^2 ∧
      0 < (q a x+Real.sqrt (q a x^2+4*b a x^2))/2 := by
  have hs := KerrField.radius_squared a x
  unfold BlackHole.radialSquared at hs
  simp only [mul_assoc, ← pow_two] at hs
  have hroot : 0 < (q a x+Real.sqrt (q a x^2+4*b a x^2))/2 := by
    nlinarith [sq_pos_of_pos hr]
  have heq : Real.sqrt (q a x^2+4*b a x^2) = sigma a x := by
    rw [← radial_den_optical a x hr]
    nlinarith
  exact ⟨Real.sqrt_pos.mp (by rw [heq]; exact sigma_positive a x hr), hroot⟩

theorem cosine_derivative (a x : Space) (e : Fin 3)
    (hdisc : 0 < q a x^2+4*b a x^2)
    (hroot : 0 < (q a x+Real.sqrt (q a x^2+4*b a x^2))/2) :
    HasDerivAt (fun t => cosine a (line x e t)) (cosineD a x e) 0 := by
  have hr := radius_derivative a x e hdisc hroot
  have hb := b_derivative a x e
  have hr0 : radius a x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hroot)
  have h := hb.div hr (by simpa only [line_zero] using hr0)
  simp only [Pi.div_def, line_zero] at h
  convert h using 1
  · rfl
  · unfold cosineD cosine
    field_simp

theorem radial_complex_real (a x : Space) (hr : 0 < radius a x) (e : Fin 3) :
    radius a x*radiusD a x e-cosine a x*cosineD a x e = x e := by
  have hr0 := ne_of_gt hr
  have hs0 := ne_of_gt (sigma_positive a x hr)
  simp only [radiusD, radial_den_optical a x hr]
  unfold cosineD radiusD
  rw [radial_den_optical a x hr]
  unfold sigma cosine
  field_simp
  ring

theorem radial_complex_imag (a x : Space) (hr : 0 < radius a x) (e : Fin 3) :
    cosine a x*radiusD a x e+radius a x*cosineD a x e = a e := by
  unfold cosineD
  have hr0 := ne_of_gt hr
  field_simp
  ring

set_option maxHeartbeats 2000000 in
theorem spatialEllD_optical (a x : Space) (hr : 0 < radius a x) (e i : Fin 3) :
    spatialEllD a x e i =
      (radius a x*(basis e i-spatialEll a x i*spatialEll a x e)-
        cosine a x*crossProduct (spatialEll a x) (basis e) i)/sigma a x := by
  have hr0 := ne_of_gt hr
  have haa : 0 ≤ dotProduct a a := Finset.sum_nonneg (fun j _ => mul_self_nonneg (a j))
  have hd : radius a x^2+dotProduct a a ≠ 0 := by positivity
  have hH : radius a x^4+b a x^2 ≠ 0 := by positivity
  have hidentity :
      spatialEllD a x e i-
        (radius a x*(basis e i-spatialEll a x i*spatialEll a x e)-
          cosine a x*crossProduct (spatialEll a x) (basis e) i)/sigma a x =
      (radius a x^4-q a x*radius a x^2-b a x^2)*radius a x*
        (a e*a i-dotProduct a a*basis e i-radius a x*crossProduct a (basis e) i)/
        ((radius a x^2+dotProduct a a)^2*(radius a x^4+b a x^2)) := by
    simp only [spatialEllD, radiusD, radial_den_optical a x hr]
    simp only [dotProduct, Fin.sum_univ_succ] at hd
    simp only [b, dotProduct, Fin.sum_univ_succ] at hH
    fin_cases e <;> fin_cases i <;>
      simp [spatialEll, sigma, cosine, q, b, basis, cross_apply, dotProduct, Fin.sum_univ_succ] <;>
      field_simp <;> ring
  simp only [KerrField.radial_relation a x, zero_mul, zero_div] at hidentity
  exact sub_eq_zero.mp hidentity

theorem potential_optical (mass : ℝ) (a x : Space) (hr : 0 < radius a x) :
    potential mass a x = mass*radius a x/sigma a x := by
  have hr0 := ne_of_gt hr
  have hH : radius a x^4+b a x^2 ≠ 0 := by positivity
  unfold potential Calculus.kerrH sigma cosine
  field_simp

theorem ell_affine_geodesic (a x : Space) (hr : 0 < radius a x) (i : Fin 3) :
    (∑ e, spatialEll a x e*spatialEllD a x e i) = 0 := by
  have hu := KerrField.spatialEll_unit a x hr
  have hsum : (∑ e, spatialEll a x e*
      (radius a x*(basis e i-spatialEll a x i*spatialEll a x e)-
        cosine a x*crossProduct (spatialEll a x) (basis e) i)) =
      radius a x*spatialEll a x i*(1-dotProduct (spatialEll a x) (spatialEll a x)) := by
    fin_cases i <;> simp [Fin.sum_univ_succ, dotProduct, basis, cross_apply] <;> ring
  simp only [spatialEllD_optical a x hr, ← mul_div_assoc, ← Finset.sum_div]
  rw [hsum]
  have hz : 1-dotProduct (spatialEll a x) (spatialEll a x) = 0 := by linarith
  rw [hz, mul_zero, zero_div]

theorem radius_gradient_norm (a x : Space) (hr : 0 < radius a x) :
    dotProduct (radiusD a x) (radiusD a x) = (radius a x^2+dotProduct a a)/sigma a x := by
  have hr0 := ne_of_gt hr
  have hH : radius a x^4+b a x^2 ≠ 0 := by positivity
  have hidentity : dotProduct (radiusD a x) (radiusD a x)-
      (radius a x^2+dotProduct a a)/sigma a x =
      -(radius a x^4-q a x*radius a x^2-b a x^2)*radius a x^4/(radius a x^4+b a x^2)^2 := by
    simp only [dotProduct, Fin.sum_univ_succ]
    simp only [radiusD, radial_den_optical a x hr]
    simp only [b, dotProduct, Fin.sum_univ_succ] at hH
    simp [sigma, cosine, q, b, dotProduct, Fin.sum_univ_succ]
    field_simp
    ring
  simp only [KerrField.radial_relation a x, neg_zero, zero_mul, zero_div] at hidentity
  exact sub_eq_zero.mp hidentity

theorem principal_radiusD (a x : Space) (hr : 0 < radius a x) :
    dotProduct (spatialEll a x) (radiusD a x) = 1 := by
  have hr0 := ne_of_gt hr
  have haa : 0 ≤ dotProduct a a := Finset.sum_nonneg (fun j _ => mul_self_nonneg (a j))
  have hd : radius a x^2+dotProduct a a ≠ 0 := by positivity
  have hH : radius a x^4+b a x^2 ≠ 0 := by positivity
  have hidentity : dotProduct (spatialEll a x) (radiusD a x)-1 =
      -(radius a x^4-q a x*radius a x^2-b a x^2)*radius a x^2/
        ((radius a x^2+dotProduct a a)*(radius a x^4+b a x^2)) := by
    simp only [dotProduct, Fin.sum_univ_succ]
    simp only [radiusD, radial_den_optical a x hr]
    simp only [dotProduct, Fin.sum_univ_succ] at hd
    simp only [b, dotProduct, Fin.sum_univ_succ] at hH
    simp [spatialEll, sigma, cosine, q, b, cross_apply,
      dotProduct, Fin.sum_univ_succ]
    field_simp
    ring
  simp only [KerrField.radial_relation a x, neg_zero, zero_mul, zero_div] at hidentity
  exact sub_eq_zero.mp hidentity

theorem cosineD_cross (a x : Space) (hr : 0 < radius a x) :
    crossProduct (spatialEll a x) (radiusD a x) = cosineD a x := by
  have hr0 := ne_of_gt hr
  have haa : 0 ≤ dotProduct a a := Finset.sum_nonneg (fun j _ => mul_self_nonneg (a j))
  have hd : radius a x^2+dotProduct a a ≠ 0 := by positivity
  have hH : radius a x^4+b a x^2 ≠ 0 := by positivity
  ext i
  have hidentity : crossProduct (spatialEll a x) (radiusD a x) i-cosineD a x i =
      -(radius a x^4-q a x*radius a x^2-b a x^2)*a i*radius a x/
        ((radius a x^2+dotProduct a a)*(radius a x^4+b a x^2)) := by
    simp only [cosineD, radiusD, radial_den_optical a x hr]
    simp only [dotProduct, Fin.sum_univ_succ] at hd
    simp only [b, dotProduct, Fin.sum_univ_succ] at hH
    fin_cases i <;> simp [cross_apply] <;>
      simp only [radiusD, radial_den_optical a x hr] <;>
      simp [spatialEll, sigma, cosine, q, b, cross_apply,
        dotProduct, Fin.sum_univ_succ] <;>
      field_simp <;> ring
  simp only [KerrField.radial_relation a x, neg_zero, zero_mul, zero_div] at hidentity
  exact sub_eq_zero.mp hidentity

def opticalParameter (a x : Space) : Space :=
  crossProduct (radiusD a x-spatialEll a x) (spatialEll a x)

theorem opticalParameter_represents_gradient (a x : Space) (hr : 0 < radius a x) :
    crossProduct (spatialEll a x) (opticalParameter a x) = radiusD a x-spatialEll a x := by
  have hu : dotProduct (spatialEll a x) (spatialEll a x) = 1 := by
    linarith [KerrField.spatialEll_unit a x hr]
  simp only [opticalParameter, cross_cross_eq_smul_sub_smul', hu, sub_dotProduct,
    dotProduct_comm (radiusD a x) (spatialEll a x), principal_radiusD a x hr,
    sub_self, one_smul, zero_smul, sub_zero]

theorem radius_gradient_bound (a x : Space) (hr : 0 < radius a x)
    (ha : dotProduct a a ≤ radius a x^2) :
    dotProduct (radiusD a x) (radiusD a x) ≤ 2 := by
  rw [radius_gradient_norm a x hr]
  apply (div_le_iff₀ (sigma_positive a x hr)).2
  unfold sigma
  nlinarith [sq_nonneg (cosine a x)]

theorem cosine_bound (a x : Space) (hr : 0 < radius a x) : cosine a x^2 ≤ dotProduct a a := by
  have hu : dotProduct (spatialEll a x) (spatialEll a x) = 1 := by
    linarith [KerrField.spatialEll_unit a x hr]
  have hcross : 0 ≤ dotProduct (crossProduct a (spatialEll a x))
      (crossProduct a (spatialEll a x)) := Finset.sum_nonneg (fun j _ => mul_self_nonneg _)
  rw [cross_dot_cross, hu, ell_spin_dot a x hr,
    dotProduct_comm (spatialEll a x) a, ell_spin_dot a x hr] at hcross
  nlinarith

theorem normalized_exterior_guards (a x : Space) (ha : dotProduct a a ≤ 1)
    (hr : 1+Real.sqrt (1-dotProduct a a) < radius a x) :
    0 < q a x ∧ max (radius a x^2) (1/1000000000000 : ℝ) = radius a x^2 ∧
      max (radius a x) ((4/5 : ℝ)*(1+Real.sqrt (1-dotProduct a a))) = radius a x ∧
      max (2*radius a x^2-q a x) (1/1000000000000 : ℝ) = 2*radius a x^2-q a x := by
  have hs := Real.sqrt_nonneg (1-dotProduct a a)
  have hr1 : 1 < radius a x := by linarith
  have hr0 : 0 < radius a x := by linarith
  have hc := cosine_bound a x hr0
  have hq : 0 < q a x := by rw [q_optical a x hr0]; nlinarith
  refine ⟨hq, max_eq_left (by nlinarith), max_eq_left (by linarith), max_eq_left ?_⟩
  rw [radial_den_optical a x hr0]
  unfold sigma
  nlinarith [sq_nonneg (cosine a x)]

end BlackHole.Cartesian
