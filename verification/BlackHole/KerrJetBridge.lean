module

public import BlackHole.KerrVacuumJet
public import BlackHole.KerrOpticalSecond

@[expose] public section
noncomputable section

namespace BlackHole.KerrField

open Cartesian (Space)

theorem radiusD_eq_optical_jet (a x : Space) (hr : 0 < Cartesian.radius a x) :
    Cartesian.radiusD a x =
      KerrVacuumJet.radiusD (Cartesian.spatialEll a x) (Cartesian.opticalParameter a x) := by
  unfold KerrVacuumJet.radiusD KerrVacuumJet.twist
  rw [Cartesian.opticalParameter_represents_gradient a x hr]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem cosineD_eq_optical_jet (a x : Space) (hr : 0 < Cartesian.radius a x) :
    Cartesian.cosineD a x =
      KerrVacuumJet.cosineD (Cartesian.spatialEll a x) (Cartesian.opticalParameter a x) := by
  unfold KerrVacuumJet.cosineD KerrVacuumJet.twist
  rw [Cartesian.opticalParameter_represents_gradient a x hr, map_sub, cross_self, sub_zero,
    Cartesian.cosineD_cross a x hr]

theorem spatialEllD_eq_optical_jet (a x : Space) (hr : 0 < Cartesian.radius a x) (e : Fin 3) :
    Cartesian.spatialEllD a x e = KerrVacuumJet.ellD (Cartesian.sigma a x)
      (Cartesian.radius a x) (Cartesian.cosine a x) (Cartesian.spatialEll a x) e := by
  ext i
  exact Cartesian.spatialEllD_optical a x hr e i

theorem potentialD_eq_optical_jet (mass : ℝ) (a x : Space) (hr : 0 < Cartesian.radius a x) (e : Fin 3) :
    Cartesian.potentialD mass a x e = KerrVacuumJet.HD (Cartesian.sigma a x)
      (Cartesian.radius a x) (Cartesian.cosine a x) mass (Cartesian.spatialEll a x)
      (Cartesian.opticalParameter a x) e := by
  rw [Cartesian.potentialD_optical mass a x hr,
    radiusD_eq_optical_jet a x hr, cosineD_eq_optical_jet a x hr]
  rfl

theorem spatialEllDD_eq_optical_jet (a x : Space) (hr : 0 < Cartesian.radius a x) (e f i : Fin 3) :
    Cartesian.spatialEllDD a x e f i = KerrVacuumJet.ellDD (Cartesian.sigma a x)
      (Cartesian.radius a x) (Cartesian.cosine a x) (Cartesian.spatialEll a x)
      (Cartesian.opticalParameter a x) f e i := by
  rw [Cartesian.spatialEllDD_optical a x hr]
  simp only [Cartesian.ellHessian, radiusD_eq_optical_jet a x hr, cosineD_eq_optical_jet a x hr,
    spatialEllD_eq_optical_jet a x hr]
  rfl

theorem potentialDD_eq_optical_jet (mass : ℝ) (a x : Space) (hr : 0 < Cartesian.radius a x) (e f : Fin 3) :
    Cartesian.potentialDD mass a x e f = KerrVacuumJet.HDD (Cartesian.sigma a x)
      (Cartesian.radius a x) (Cartesian.cosine a x) mass (Cartesian.spatialEll a x)
      (Cartesian.opticalParameter a x) f e := by
  rw [Cartesian.potentialDD_optical mass a x hr]
  simp only [Cartesian.potentialHessian, Cartesian.radialHessian, Cartesian.cosineHessian,
    radiusD_eq_optical_jet a x hr, cosineD_eq_optical_jet a x hr,
    KerrVacuumJet.HDD, KerrVacuumJet.rDD, KerrVacuumJet.cDD]
  ring

theorem inverse_eq_optical_jet (mass : ℝ) (a x : Space) (hr : 0 < Cartesian.radius a x) :
    (metric mass a x)⁻¹ = KerrVacuumJet.inv (Cartesian.sigma a x)
      (Cartesian.radius a x) mass (Cartesian.spatialEll a x) := by
  rw [inverse_eq_explicit mass a x hr]
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [explicitInverse, minkowski, Matrix.diagonal_apply, raisedEll, signature,
      Cartesian.potential_optical mass a x hr, Cartesian.ell, Cartesian.eta,
      KerrVacuumJet.inv, KerrVacuumJet.H, KerrVacuumJet.raised, Matrix.vecMulVec_apply, eq_comm]
  ring

theorem metricD_eq_optical_jet (mass : ℝ) (a x : Space) (hr : 0 < Cartesian.radius a x) :
    metricD mass a x = KerrVacuumJet.dg (Cartesian.sigma a x)
      (Cartesian.radius a x) (Cartesian.cosine a x) mass (Cartesian.spatialEll a x)
      (Cartesian.opticalParameter a x) := by
  ext e i j
  cases e using Fin.cases with
  | zero => simp [metricD, KerrVacuumJet.dg, KerrVacuumJet.h4, KerrVacuumJet.dell4]
  | succ e =>
    simp only [metricD, Fin.cases_succ, Matrix.of_apply, Cartesian.metricD,
      potentialD_eq_optical_jet mass a x hr e, Cartesian.potential_optical mass a x hr]
    have hellD : Cartesian.ellD a x e = Fin.cases 0 (KerrVacuumJet.ellD (Cartesian.sigma a x)
        (Cartesian.radius a x) (Cartesian.cosine a x) (Cartesian.spatialEll a x) e) := by
      unfold Cartesian.ellD
      rw [spatialEllD_eq_optical_jet a x hr e]
    simp only [hellD, Cartesian.ell, KerrVacuumJet.dg, Matrix.of_apply, KerrVacuumJet.h4,
      KerrVacuumJet.dell4, KerrVacuumJet.ell4, KerrVacuumJet.H, Fin.cases_succ]

theorem metricDD_eq_optical_jet (mass : ℝ) (a x : Space) (hr : 0 < Cartesian.radius a x) :
    metricDD mass a x = KerrVacuumJet.ddg (Cartesian.sigma a x)
      (Cartesian.radius a x) (Cartesian.cosine a x) mass (Cartesian.spatialEll a x)
      (Cartesian.opticalParameter a x) := by
  ext e f i j
  cases e using Fin.cases with
  | zero => simp [metricDD, KerrVacuumJet.ddg, KerrVacuumJet.hh4, KerrVacuumJet.h4,
      KerrVacuumJet.dell4, KerrVacuumJet.ddell4]
  | succ e =>
    cases f using Fin.cases with
    | zero => simp [metricDD, KerrVacuumJet.ddg, KerrVacuumJet.hh4, KerrVacuumJet.h4,
        KerrVacuumJet.dell4, KerrVacuumJet.ddell4]
    | succ f =>
      have hellD (d : Fin 3) : Cartesian.ellD a x d = Fin.cases 0 (KerrVacuumJet.ellD (Cartesian.sigma a x)
          (Cartesian.radius a x) (Cartesian.cosine a x) (Cartesian.spatialEll a x) d) := by
        unfold Cartesian.ellD
        rw [spatialEllD_eq_optical_jet a x hr d]
      have hellDD : Cartesian.ellDD a x f e = Fin.cases 0
          (KerrVacuumJet.ellDD (Cartesian.sigma a x) (Cartesian.radius a x) (Cartesian.cosine a x)
            (Cartesian.spatialEll a x) (Cartesian.opticalParameter a x) e f) := by
        unfold Cartesian.ellDD
        ext k
        cases k using Fin.cases with
        | zero => rfl
        | succ k => exact spatialEllDD_eq_optical_jet a x hr f e k
      simp only [metricDD, Fin.cases_succ, Matrix.of_apply, Cartesian.metricDD,
        potentialDD_eq_optical_jet mass a x hr, potentialD_eq_optical_jet mass a x hr,
        Cartesian.potential_optical mass a x hr, Cartesian.ell, hellD, hellDD,
        KerrVacuumJet.ddg, Matrix.of_apply, KerrVacuumJet.hh4, KerrVacuumJet.h4,
        KerrVacuumJet.dell4, KerrVacuumJet.ddell4, KerrVacuumJet.ell4, KerrVacuumJet.H,
        Fin.cases_succ]
      ring

theorem ricci_eq_optical_jet (mass : ℝ) (a x : Space) (hr : 0 < Cartesian.radius a x) (i j : Fin 4) :
    ricci mass a x i j = Curvature.ricci
      (KerrVacuumJet.inv (Cartesian.sigma a x) (Cartesian.radius a x) mass (Cartesian.spatialEll a x))
      (KerrVacuumJet.dg (Cartesian.sigma a x) (Cartesian.radius a x) (Cartesian.cosine a x) mass
        (Cartesian.spatialEll a x) (Cartesian.opticalParameter a x))
      (KerrVacuumJet.ddg (Cartesian.sigma a x) (Cartesian.radius a x) (Cartesian.cosine a x) mass
        (Cartesian.spatialEll a x) (Cartesian.opticalParameter a x)) i j := by
  simp only [ricci, inverse_eq_optical_jet mass a x hr,
    metricD_eq_optical_jet mass a x hr, metricDD_eq_optical_jet mass a x hr]

end BlackHole.KerrField
