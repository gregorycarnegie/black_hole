module

public import BlackHole.Calculus
public import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section

namespace BlackHole.Cartesian

abbrev Space := Fin 3 → ℝ

def basis (j : Fin 3) : Space := fun i => if i = j then 1 else 0
def line (x : Space) (j : Fin 3) (t : ℝ) : Space := fun i => x i+t*basis j i
def q (a x : Space) : ℝ := dotProduct x x-dotProduct a a
def b (a x : Space) : ℝ := dotProduct a x
def radius (a x : Space) : ℝ := Calculus.kerrRadius (q a x) (b a x)
def radiusD (a x : Space) (j : Fin 3) : ℝ :=
  (radius a x*x j+(b a x/radius a x)*a j)/(2*radius a x^2-q a x)
def potential (mass : ℝ) (a x : Space) : ℝ := Calculus.kerrH mass (radius a x) (b a x)
def potentialD (mass : ℝ) (a x : Space) (j : Fin 3) : ℝ :=
  potential mass a x*(3*radiusD a x j/radius a x-
    (4*radius a x^3*radiusD a x j+2*b a x*a j)/(radius a x^4+b a x^2))
def spatialEll (a x : Space) (i : Fin 3) : ℝ :=
  (radius a x*x i-crossProduct a x i+(b a x/radius a x)*a i)/(radius a x^2+dotProduct a a)
def spatialEllD (a x : Space) (j i : Fin 3) : ℝ :=
  (radiusD a x j*x i+radius a x*basis j i-crossProduct a (basis j) i+
    (a j/radius a x-b a x*radiusD a x j/radius a x^2)*a i-
    spatialEll a x i*2*radius a x*radiusD a x j)/(radius a x^2+dotProduct a a)
def ell (a x : Space) : Fin 4 → ℝ := Fin.cases 1 (spatialEll a x)
def ellD (a x : Space) (j : Fin 3) : Fin 4 → ℝ := Fin.cases 0 (spatialEllD a x j)
def eta (i k : Fin 4) : ℝ := if i = k then (if i = 0 then -1 else 1) else 0
def metric (mass : ℝ) (a x : Space) (i k : Fin 4) : ℝ :=
  eta i k+2*potential mass a x*ell a x i*ell a x k
def metricD (mass : ℝ) (a x : Space) (j : Fin 3) (i k : Fin 4) : ℝ :=
  2*potentialD mass a x j*ell a x i*ell a x k+
    2*potential mass a x*(ellD a x j i*ell a x k+ell a x i*ellD a x j k)

theorem line_zero (x : Space) (j : Fin 3) : line x j 0 = x := by
  funext i
  simp [line]

theorem line_component_derivative (x : Space) (j i : Fin 3) :
    HasDerivAt (fun t => line x j t i) (basis j i) 0 := by
  simpa only [line, one_mul] using ((hasDerivAt_id' (0 : ℝ)).mul_const (basis j i)).const_add (x i)

theorem q_derivative (a x : Space) (j : Fin 3) :
    HasDerivAt (fun t => q a (line x j t)) (2*x j) 0 := by
  have h := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (line_component_derivative x j i).pow 2)).sub_const (dotProduct a a)
  convert h using 1
  · funext t
    simp [q, dotProduct, pow_two]
  · simp [line, basis, mul_ite]

theorem b_derivative (a x : Space) (j : Fin 3) :
    HasDerivAt (fun t => b a (line x j t)) (a j) 0 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (line_component_derivative x j i).const_mul (a i))
  convert h using 1
  · rfl
  · simp [basis, mul_ite]

theorem cross_derivative (a x : Space) (j i : Fin 3) :
    HasDerivAt (fun t => crossProduct a (line x j t) i) (crossProduct a (basis j) i) 0 := by
  fin_cases i
  · simpa [cross_apply, Pi.sub_def] using
      ((line_component_derivative x j 2).const_mul (a 1)).sub
        ((line_component_derivative x j 1).const_mul (a 2))
  · simpa [cross_apply, Pi.sub_def] using
      ((line_component_derivative x j 0).const_mul (a 2)).sub
        ((line_component_derivative x j 2).const_mul (a 0))
  · simpa [cross_apply, Pi.sub_def] using
      ((line_component_derivative x j 1).const_mul (a 0)).sub
        ((line_component_derivative x j 0).const_mul (a 1))

theorem radius_derivative (a x : Space) (j : Fin 3)
    (hdisc : 0 < q a x^2+4*b a x^2)
    (hroot : 0 < (q a x+Real.sqrt (q a x^2+4*b a x^2))/2) :
    HasDerivAt (fun t => radius a (line x j t)) (radiusD a x j) 0 := by
  have h := Calculus.kerrRadius_derivative (fun t => q a (line x j t))
    (fun t => b a (line x j t)) 0 (x j) (a j) (q_derivative a x j) (b_derivative a x j)
    (by simpa only [line_zero] using hdisc) (by simpa only [line_zero] using hroot)
  simpa only [radius, radiusD, line_zero] using h

theorem potential_derivative (mass : ℝ) (a x : Space) (j : Fin 3)
    (hdisc : 0 < q a x^2+4*b a x^2)
    (hroot : 0 < (q a x+Real.sqrt (q a x^2+4*b a x^2))/2) :
    HasDerivAt (fun t => potential mass a (line x j t)) (potentialD mass a x j) 0 := by
  have hr := radius_derivative a x j hdisc hroot
  have hb := b_derivative a x j
  have hpos : 0 < radius a x := Real.sqrt_pos.mpr hroot
  have hr0 : radius a x ≠ 0 := ne_of_gt hpos
  have hd : radius a x^4+b a x^2 ≠ 0 := by positivity
  have h := Calculus.kerrH_derivative (fun t => radius a (line x j t))
    (fun t => b a (line x j t)) mass 0 (radiusD a x j) (a j) hr hb
    (by simpa only [line_zero] using hr0) (by simpa only [line_zero] using hd)
  simpa only [potential, potentialD, line_zero] using h

theorem spatialEll_derivative (a x : Space) (j l : Fin 3)
    (hdisc : 0 < q a x^2+4*b a x^2)
    (hroot : 0 < (q a x+Real.sqrt (q a x^2+4*b a x^2))/2) :
    HasDerivAt (fun t => spatialEll a (line x j t) l) (spatialEllD a x j l) 0 := by
  have hr := radius_derivative a x j hdisc hroot
  have hb := b_derivative a x j
  have hpos : 0 < radius a x := Real.sqrt_pos.mpr hroot
  have hr0 : radius a x ≠ 0 := ne_of_gt hpos
  have haa : 0 ≤ dotProduct a a := Finset.sum_nonneg (fun l _ => mul_self_nonneg (a l))
  have he : radius a x^2+dotProduct a a ≠ 0 := by positivity
  have h := Calculus.ell_component_derivative (fun t => radius a (line x j t))
    (fun t => line x j t l) (fun t => b a (line x j t))
    (fun t => crossProduct a (line x j t) l) (a l) (dotProduct a a) 0
    (radiusD a x j) (basis j l) (a j) (crossProduct a (basis j) l)
    hr (line_component_derivative x j l) hb (cross_derivative a x j l)
    (by simpa only [line_zero] using hr0) (by simpa only [line_zero] using he)
  simpa only [spatialEll, spatialEllD, line_zero] using h

theorem ell_derivative (a x : Space) (j : Fin 3) (l : Fin 4)
    (hdisc : 0 < q a x^2+4*b a x^2)
    (hroot : 0 < (q a x+Real.sqrt (q a x^2+4*b a x^2))/2) :
    HasDerivAt (fun t => ell a (line x j t) l) (ellD a x j l) 0 := by
  exact Fin.cases (hasDerivAt_const 0 1)
    (fun n => spatialEll_derivative a x j n hdisc hroot) l

/-- All sixteen component derivatives in add_kerr, for every Cartesian
    direction, when the explicit radius/denominator floors are inactive. -/
theorem metric_derivative (mass : ℝ) (a x : Space) (j : Fin 3) (i k : Fin 4)
    (hdisc : 0 < q a x^2+4*b a x^2)
    (hroot : 0 < (q a x+Real.sqrt (q a x^2+4*b a x^2))/2) :
    HasDerivAt (fun t => metric mass a (line x j t) i k) (metricD mass a x j i k) 0 := by
  have h := (Calculus.metric_component_derivative (fun t => potential mass a (line x j t))
    (fun t => ell a (line x j t) i) (fun t => ell a (line x j t) k) 0
    (potentialD mass a x j) (ellD a x j i) (ellD a x j k)
    (potential_derivative mass a x j hdisc hroot) (ell_derivative a x j i hdisc hroot)
    (ell_derivative a x j k hdisc hroot)).const_add (eta i k)
  simpa only [metric, metricD, line_zero] using h

end BlackHole.Cartesian
