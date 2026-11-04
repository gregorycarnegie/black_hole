module
public import BlackHole.KerrVacuumSpatialCertificate
import Mathlib.Tactic.FinCases

@[expose] public section
noncomputable section
namespace BlackHole.KerrVacuumJet

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem ricci_space_13_zero (S r c m : ℝ) (l v : Cartesian.Space)
    (hunit : l 0^2+l 1^2+l 2^2 = 1) (hS : S ≠ 0)
    (hsigma : S = r^2+c^2) :
    Curvature.ricci (inv S r m l) (dg S r c m l v) (ddg S r c m l v) 1 3 = 0 := by
  have hid : Curvature.ricci (inv S r m l) (dg S r c m l v) (ddg S r c m l v) 1 3 =
      ((l 0^2+l 1^2+l 2^2-1)*(spatialResidual S r c m l v (0 : Fin 3) (2 : Fin 3))+2*S^3*m*r*(Cartesian.basis (0 : Fin 3) (2 : Fin 3)-l (0 : Fin 3)*l (2 : Fin 3)-l (0 : Fin 3)*twist l v (2 : Fin 3)-
        twist l v (0 : Fin 3)*l (2 : Fin 3))*(S-r^2-c^2))/S^6 := by
    dsimp only [spatialResidual]
    simp only [Curvature.ricci, Curvature.christoffelD, inverseD_closed S r c m l v hunit]
    simp only [Curvature.christoffel, Fin.sum_univ_succ]
    simp only [di, KerrField.rankDerivative, inv, dg, ddg, Matrix.of_apply,
      Matrix.vecMulVec_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    simp [KerrField.signature, Cartesian.eta, hh4, h4, dell4, ddell4, ell4, raised]
    simp [H, HD, HDD, ellD, ellDD, radiusD, cosineD, twist, rDD, cDD,
      cross_apply, Cartesian.basis, dotProduct, Fin.sum_univ_succ]
    field_simp
    ring
  rw [hid]
  rw [hunit, sub_self, zero_mul, hsigma]
  ring

end BlackHole.KerrVacuumJet
