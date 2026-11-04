module

public import BlackHole.KerrSecond
public import BlackHole.Schwarzschild
public import BlackHole.MetricInverse

@[expose] public section
noncomputable section

namespace BlackHole.KerrField

open Cartesian (Space)
open Schwarzschild (line4 line4_zero)

def metric (mass : ℝ) (a x : Space) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of (Cartesian.metric mass a x)

def metricD (mass : ℝ) (a x : Space) (e : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  Fin.cases 0 (fun e => Matrix.of (Cartesian.metricD mass a x e)) e

/-- The first direction is the outer derivative, matching christoffelD. -/
def metricDD (mass : ℝ) (a x : Space) (e f : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  Fin.cases 0 (fun e => Fin.cases 0 (fun f => Matrix.of (Cartesian.metricDD mass a x f e)) f) e

theorem metric_derivative (mass : ℝ) (a x : Space) (e i j : Fin 4)
    (hdisc : 0 < Cartesian.q a x^2+4*Cartesian.b a x^2)
    (hroot : 0 < (Cartesian.q a x+Real.sqrt (Cartesian.q a x^2+4*Cartesian.b a x^2))/2) :
    HasDerivAt (fun t => metric mass a (line4 x e t) i j) (metricD mass a x e i j) 0 := by
  exact Fin.cases (hasDerivAt_const (0 : ℝ) (metric mass a x i j))
    (fun e => Cartesian.metric_derivative mass a x e i j hdisc hroot) e

theorem metric_second_derivative (mass : ℝ) (a x : Space) (e f i j : Fin 4)
    (hdisc : 0 < Cartesian.q a x^2+4*Cartesian.b a x^2)
    (hroot : 0 < (Cartesian.q a x+Real.sqrt (Cartesian.q a x^2+4*Cartesian.b a x^2))/2) :
    HasDerivAt (fun t => metricD mass a (line4 x e t) f i j) (metricDD mass a x e f i j) 0 := by
  refine Fin.cases ?_ (fun e => ?_) e
  · exact hasDerivAt_const (0 : ℝ) (metricD mass a x f i j)
  · refine Fin.cases ?_ (fun f => ?_) f
    · exact hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · exact Cartesian.metricD_derivative mass a x f e i j hdisc hroot

def connection (mass : ℝ) (a x : Space) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  Curvature.christoffel (metric mass a x)⁻¹ (metricD mass a x)

theorem connection_derivative (mass : ℝ) (a x : Space) (e i j k : Fin 4)
    (hdisc : 0 < Cartesian.q a x^2+4*Cartesian.b a x^2)
    (hroot : 0 < (Cartesian.q a x+Real.sqrt (Cartesian.q a x^2+4*Cartesian.b a x^2))/2)
    (hdet : (metric mass a x).det ≠ 0) :
    HasDerivAt (fun t => connection mass a (line4 x e t) i j k)
      (Curvature.christoffelD (metric mass a x)⁻¹ (metricD mass a x) (metricDD mass a x) e i j k) 0 := by
  have hg := fun i j => metric_derivative mass a x e i j hdisc hroot
  have hi := fun i j => Curvature.inverse_derivative (fun t => metric mass a (line4 x e t))
    (metricD mass a x e) 0 hg (by simpa only [line4_zero] using hdet) i j
  have hd := fun f i j => metric_second_derivative mass a x e f i j hdisc hroot
  have h := Curvature.christoffel_derivative
    (fun t => (metric mass a (line4 x e t))⁻¹) (fun t => metricD mass a (line4 x e t))
    (metricDD mass a x) 0 e i j k
  simp only [line4_zero] at hi h
  apply h
  · intro i j
    simpa only [Curvature.inverseD] using hi i j
  · exact hd

def riemann (mass : ℝ) (a x : Space) : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  Curvature.riemann (metric mass a x)⁻¹ (metricD mass a x) (metricDD mass a x)

def ricci (mass : ℝ) (a x : Space) : Fin 4 → Fin 4 → ℝ :=
  Curvature.ricci (metric mass a x)⁻¹ (metricD mass a x) (metricDD mass a x)

theorem riemann_from_connection (mass : ℝ) (a x : Space) (i j k l : Fin 4)
    (hdisc : 0 < Cartesian.q a x^2+4*Cartesian.b a x^2)
    (hroot : 0 < (Cartesian.q a x+Real.sqrt (Cartesian.q a x^2+4*Cartesian.b a x^2))/2)
    (hdet : (metric mass a x).det ≠ 0) :
    riemann mass a x i j k l =
      deriv (fun t => connection mass a (line4 x k t) i j l) 0-
      deriv (fun t => connection mass a (line4 x l t) i j k) 0+
      ∑ d, (connection mass a x i k d*connection mass a x d j l-
        connection mass a x i l d*connection mass a x d j k) := by
  rw [(connection_derivative mass a x k i j l hdisc hroot hdet).deriv,
    (connection_derivative mass a x l i j k hdisc hroot hdet).deriv]
  rfl

theorem ricci_is_contracted_curvature (mass : ℝ) (a x : Space) (i j : Fin 4) :
    ricci mass a x i j = ∑ k, riemann mass a x k i k j :=
  Curvature.ricci_eq_riemann_contraction _ _ _ i j

end BlackHole.KerrField
