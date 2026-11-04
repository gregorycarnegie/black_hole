module

public import BlackHole.Schwarzschild
public import BlackHole.MetricInverse
import Mathlib.Tactic.Push

@[expose] public section
noncomputable section

namespace BlackHole.BinaryField

open Cartesian (Space)
open Schwarzschild (axis line4)

def shifted (x : Space) (s : ℝ) : Space := x+axis s

theorem shifted_line (x : Space) (s : ℝ) (e : Fin 4) (t : ℝ) :
    shifted (line4 x e t) s = line4 (shifted x s) e t := by
  refine Fin.cases ?_ (fun e => ?_) e
  · rfl
  · ext i
    simp only [shifted, line4, Fin.cases_succ, Cartesian.line, Pi.add_apply]
    ring

def metric (binary : Bool) (x : Space) : Matrix (Fin 4) (Fin 4) ℝ := fun i j =>
  Cartesian.eta i j+if binary then
    Schwarzschild.source ((1/2 : ℚ) : ℝ) (shifted x ((7 : ℚ) : ℝ)) i j+
    Schwarzschild.source ((1/2 : ℚ) : ℝ) (shifted x ((-7 : ℚ) : ℝ)) i j
  else Schwarzschild.source 1 (shifted x ((7 : ℚ) : ℝ)) i j

def metricD (binary : Bool) (x : Space) : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ := fun e i j =>
  if binary then
    Schwarzschild.sourceD ((1/2 : ℚ) : ℝ) (shifted x ((7 : ℚ) : ℝ)) e i j+
    Schwarzschild.sourceD ((1/2 : ℚ) : ℝ) (shifted x ((-7 : ℚ) : ℝ)) e i j
  else Schwarzschild.sourceD 1 (shifted x ((7 : ℚ) : ℝ)) e i j

def metricDD (binary : Bool) (x : Space) : Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℝ := fun e f i j =>
  if binary then
    Schwarzschild.sourceDD ((1/2 : ℚ) : ℝ) (shifted x ((7 : ℚ) : ℝ)) e f i j+
    Schwarzschild.sourceDD ((1/2 : ℚ) : ℝ) (shifted x ((-7 : ℚ) : ℝ)) e f i j
  else Schwarzschild.sourceDD 1 (shifted x ((7 : ℚ) : ℝ)) e f i j

theorem metric_derivative (binary : Bool) (x : Space) (e i j : Fin 4)
    (hp : 0 < Schwarzschild.radius (shifted x ((7 : ℚ) : ℝ)))
    (hm : 0 < Schwarzschild.radius (shifted x ((-7 : ℚ) : ℝ))) :
    HasDerivAt (fun t => metric binary (line4 x e t) i j) (metricD binary x e i j) 0 := by
  cases binary
  · have h := (Schwarzschild.source_derivative 1 (shifted x ((7 : ℚ) : ℝ)) e i j hp).const_add
      (Cartesian.eta i j)
    simpa [metric, metricD, shifted_line] using h
  · have h := ((Schwarzschild.source_derivative ((1/2 : ℚ) : ℝ)
      (shifted x ((7 : ℚ) : ℝ)) e i j hp).add
      (Schwarzschild.source_derivative ((1/2 : ℚ) : ℝ)
        (shifted x ((-7 : ℚ) : ℝ)) e i j hm)).const_add (Cartesian.eta i j)
    simp only [Pi.add_def] at h
    simpa [metric, metricD, shifted_line] using h

theorem metric_second_derivative (binary : Bool) (x : Space) (e f i j : Fin 4)
    (hp : 0 < Schwarzschild.radius (shifted x ((7 : ℚ) : ℝ)))
    (hm : 0 < Schwarzschild.radius (shifted x ((-7 : ℚ) : ℝ))) :
    HasDerivAt (fun t => metricD binary (line4 x e t) f i j) (metricDD binary x e f i j) 0 := by
  have h (m : ℝ) (s : ℝ) (hr : 0 < Schwarzschild.radius (shifted x s)) :=
    Schwarzschild.source_second_derivative m (shifted x s) f e i j hr
  simp_rw [Schwarzschild.sourceDD_symmetric _ _ f e] at h
  cases binary
  · simpa [metricD, metricDD, shifted_line] using h 1 ((7 : ℚ) : ℝ) hp
  · have hd := (h ((1/2 : ℚ) : ℝ) ((7 : ℚ) : ℝ) hp).add
      (h ((1/2 : ℚ) : ℝ) ((-7 : ℚ) : ℝ) hm)
    simp only [Pi.add_def] at hd
    simpa [metricD, metricDD, shifted_line] using hd

theorem metric_at_zero (binary : Bool) (i j : Fin 4) :
    metric binary 0 i j = (Binary.metric binary i j : ℝ) := by
  have heta : Cartesian.eta i j = (Binary.eta i j : ℝ) := by
    unfold Cartesian.eta Binary.eta
    split_ifs <;> norm_num
  have h0 := Schwarzschild.source_cast 1 7 i j
  have hp := Schwarzschild.source_cast (1/2) 7 i j
  have hm := Schwarzschild.source_cast (1/2) (-7) i j
  norm_num at h0 hp hm
  simp only [one_div] at hp hm
  cases binary <;> simp [metric, shifted, heta, h0, hp, hm, Binary.metric]

theorem metricD_at_zero (binary : Bool) (e i j : Fin 4) :
    metricD binary 0 e i j = (Binary.metricD binary e i j : ℝ) := by
  have h0 := Schwarzschild.sourceD_cast 1 7 e i j
  have hp := Schwarzschild.sourceD_cast (1/2) 7 e i j
  have hm := Schwarzschild.sourceD_cast (1/2) (-7) e i j
  norm_num at h0 hp hm
  simp only [one_div] at hp hm
  cases binary <;> simp [metricD, shifted, h0, hp, hm, Binary.metricD]

theorem metricDD_at_zero (binary : Bool) (e f i j : Fin 4) :
    metricDD binary 0 e f i j = (Binary.metricDD binary e f i j : ℝ) := by
  have h0 := Schwarzschild.sourceDD_cast 1 7 e f i j
  have hp := Schwarzschild.sourceDD_cast (1/2) 7 e f i j
  have hm := Schwarzschild.sourceDD_cast (1/2) (-7) e f i j
  norm_num at h0 hp hm
  simp only [one_div] at hp hm
  cases binary <;> simp [metricDD, shifted, h0, hp, hm, Binary.metricDD]

def pointInverse (binary : Bool) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of (fun i j => (Binary.inverse binary i j : ℝ))

theorem inverse_product_at_zero (binary : Bool) :
    metric binary 0*pointInverse binary = 1 := by
  have hq : ∀ i j, (∑ k, Binary.metric binary i k*Binary.inverse binary k j) = Binary.delta i j := by
    cases binary
    · exact Binary.inverse_checked.2
    · exact Binary.inverse_checked.1
  ext i j
  have hc := congrArg (fun q : ℚ => (q : ℝ)) (hq i j)
  push_cast at hc
  by_cases hij : i = j
  · simpa [Matrix.mul_apply, metric_at_zero, Matrix.one_apply, Binary.delta, pointInverse, hij] using hc
  · simpa [Matrix.mul_apply, metric_at_zero, Matrix.one_apply, Binary.delta, pointInverse, hij] using hc

theorem inverse_at_zero (binary : Bool) :
    (metric binary 0)⁻¹ = pointInverse binary :=
  Matrix.inv_eq_right_inv (inverse_product_at_zero binary)

theorem determinant_at_zero_ne (binary : Bool) : (metric binary 0).det ≠ 0 :=
  Matrix.det_ne_zero_of_right_inverse (inverse_product_at_zero binary)

theorem midpoint_radius (s : ℚ) (hs : s ≠ 0) : 0 < Schwarzschild.radius (shifted 0 (s : ℝ)) := by
  simpa only [shifted, zero_add, Schwarzschild.radius_axis] using
    abs_pos.mpr (show (s : ℝ) ≠ 0 by exact_mod_cast hs)

def connection (binary : Bool) (x : Space) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  Curvature.christoffel (metric binary x)⁻¹ (metricD binary x)

theorem connection_derivative (binary : Bool) (e a b c : Fin 4) :
    HasDerivAt (fun t => connection binary (line4 0 e t) a b c)
      (Curvature.christoffelD (metric binary 0)⁻¹ (metricD binary 0) (metricDD binary 0) e a b c) 0 := by
  have hp := midpoint_radius 7 (by norm_num)
  have hm := midpoint_radius (-7) (by norm_num)
  have hg := fun i j => metric_derivative binary 0 e i j hp hm
  have hi := fun i j => Curvature.inverse_derivative (fun t => metric binary (line4 0 e t))
    (metricD binary 0 e) 0 hg (by simpa only [Schwarzschild.line4_zero]
      using determinant_at_zero_ne binary) i j
  have hd := fun d i j => metric_second_derivative binary 0 e d i j hp hm
  have h := Curvature.christoffel_derivative
    (fun t => (metric binary (line4 0 e t))⁻¹) (fun t => metricD binary (line4 0 e t))
    (metricDD binary 0) 0 e a b c
  simp only [Schwarzschild.line4_zero] at hi h
  apply h
  · intro i j
    simpa only [Curvature.inverseD] using hi i j
  · exact hd

def ricciAtZero (binary : Bool) : Fin 4 → Fin 4 → ℝ :=
  Curvature.ricci (metric binary 0)⁻¹ (metricD binary 0) (metricDD binary 0)

theorem ricci_from_connection (binary : Bool) (b c : Fin 4) :
    ricciAtZero binary b c =
      ∑ a, (deriv (fun t => connection binary (line4 0 a t) a b c) 0-
        deriv (fun t => connection binary (line4 0 c t) a b a) 0+
        ∑ d, (connection binary 0 a a d*connection binary 0 d b c-
          connection binary 0 a c d*connection binary 0 d b a)) := by
  unfold ricciAtZero Curvature.ricci
  apply Finset.sum_congr rfl
  intro a _
  rw [(connection_derivative binary a a b c).deriv,
    (connection_derivative binary c a b a).deriv]
  rfl

theorem ricci_cast (binary : Bool) (b c : Fin 4) :
    ricciAtZero binary b c = (Binary.ricci binary b c : ℝ) := by
  simp only [ricciAtZero, inverse_at_zero]
  have hd : metricD binary 0 = fun e i j => (Binary.metricD binary e i j : ℝ) :=
    funext (fun e => funext (fun i => funext (metricD_at_zero binary e i)))
  have hdd : metricDD binary 0 = fun e f i j => (Binary.metricDD binary e f i j : ℝ) :=
    funext (fun e => funext (fun f => funext (fun i => funext (metricDD_at_zero binary e f i))))
  rw [hd, hdd]
  exact (Curvature.ricci_map (Rat.castHom ℝ) (Binary.inverse binary)
    (Binary.metricD binary) (Binary.metricDD binary) b c).symm

theorem binary_ricci_tt : ricciAtZero true 0 0 = 4/3087 := by
  rw [ricci_cast, Binary.binary_ricci_tt]
  norm_num

theorem binary_not_vacuum : ricciAtZero true 0 0 ≠ 0 := by
  rw [binary_ricci_tt]
  norm_num

theorem single_ricci_tt : ricciAtZero false 0 0 = 0 := by
  rw [ricci_cast, Binary.single_ricci_tt]
  norm_num

end BlackHole.BinaryField
