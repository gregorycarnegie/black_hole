module
public import BlackHole.KerrJetBridge
import Mathlib.Tactic.FinCases

@[expose] public section
noncomputable section
namespace BlackHole.KerrVacuumJet

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem ricci_time_space_first_zero (S r c m : ℝ) (l v : Cartesian.Space)
    (hunit : l 0^2+l 1^2+l 2^2 = 1) (hS : S ≠ 0)
    (hsigma : S = r^2+c^2) :
    Curvature.ricci (inv S r m l) (dg S r c m l v) (ddg S r c m l v) 0 1 = 0 := by
  /- Explicit polynomial certificate; ring checks it against the metric jets. -/
  let N : ℝ := l 0^2+l 1^2+l 2^2
  let U : ℝ := dotProduct (twist l v) (twist l v)
  let A : ℝ := -m*(8*N^2*S*U*c^2*m^2*r^3 + 4*N^2*c^4*m^3*r^2 - 16*N^2*c^2*m^3*r^4 + 12*N^2*m^3*r^6 -
    4*N*S^2*U*c^2*m*r^2 + 2*N*S*U*c^4*m^2*r - 12*N*S*U*c^2*m^2*r^3 + 2*N*S*U*m^2*r^5 -
    6*N*S*c^4*m^2*r + 20*N*S*c^2*m^2*r^3 - 14*N*S*m^2*r^5 - 4*N*c^4*m^3*r^2 + 16*N*c^2*m^3*r^4 -
    12*N*m^3*r^6 + 9*S^3*U*c^2*r - 3*S^3*U*r^3 - S^2*U*c^4*m + 2*S^2*U*c^2*m*r^2 - S^2*U*m*r^4 +
    10*S^2*c^2*m*r^2 - 6*S^2*m*r^4 - 2*S*U*c^4*m^2*r + 4*S*U*c^2*m^2*r^3 - 2*S*U*m^2*r^5 -
    4*S*c^2*m^2*r^3 + 4*S*m^2*r^5)
  let B : ℝ := m*(4*N^3*c^4*m^3*r^2 - 16*N^3*c^2*m^3*r^4 + 12*N^3*m^3*r^6 - 4*N^2*S*c^4*m^2*r +
    16*N^2*S*c^2*m^2*r^3 - 12*N^2*S*m^2*r^5 - 8*N^2*c^4*m^3*r^2 + 32*N^2*c^2*m^3*r^4 -
    24*N^2*m^3*r^6 - N*S^2*c^4*m + 24*N*S^2*c^2*m*r^2 - 11*N*S^2*m*r^4 + 4*N*S*c^4*m^2*r -
    20*N*S*c^2*m^2*r^3 + 16*N*S*m^2*r^5 + 4*N*c^4*m^3*r^2 - 16*N*c^2*m^3*r^4 + 12*N*m^3*r^6 -
    2*S^4*r + 4*S^3*r^3 - 4*S^2*c^2*m*r^2 + 4*S^2*m*r^4 + 4*S*c^2*m^2*r^3 - 4*S*m^2*r^5)
  let C : ℝ := c*m*(-8*N^3*c^2*m^3*r^3 + 24*N^3*m^3*r^5 + 8*N^2*S*c^2*m^2*r^2 - 24*N^2*S*m^2*r^4 +
    16*N^2*c^2*m^3*r^3 - 48*N^2*m^3*r^5 + 8*N*S^2*c^2*m*r - 28*N*S^2*m*r^3 - 8*N*S*c^2*m^2*r^2 +
    32*N*S*m^2*r^4 - 8*N*c^2*m^3*r^3 + 24*N*m^3*r^5 - 3*S^3*c^2 + 11*S^3*r^2 + 8*S^2*m*r^3 -
    8*S*m^2*r^4)
  have hid : Curvature.ricci (inv S r m l) (dg S r c m l v) (ddg S r c m l v) 0 1 =
      ((N-1)*(A*l (0 : Fin 3)+B*twist l v (0 : Fin 3)+C*cosineD l v (0 : Fin 3))-
        2*S^3*m*r*twist l v (0 : Fin 3)*(S-r^2-c^2))/S^6 := by
    dsimp only [N, U, A, B, C]
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
  have hN : N = 1 := hunit
  rw [hN, sub_self, zero_mul, hsigma]
  ring

end BlackHole.KerrVacuumJet
