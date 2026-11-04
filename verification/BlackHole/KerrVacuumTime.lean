module

public import BlackHole.KerrJetBridge

@[expose] public section
noncomputable section

namespace BlackHole.KerrVacuumJet

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem ricci_time_time_zero (S r c m : ℝ) (l v : Cartesian.Space)
    (hunit : l 0^2+l 1^2+l 2^2 = 1) (hS : S ≠ 0) :
    Curvature.ricci (inv S r m l) (dg S r c m l v) (ddg S r c m l v) 0 0 = 0 := by
  simp only [Curvature.ricci, Curvature.christoffelD, inverseD_closed S r c m l v hunit]
  simp only [Curvature.christoffel, Fin.sum_univ_succ]
  simp only [di, KerrField.rankDerivative, inv, dg, ddg, Matrix.of_apply,
    Matrix.vecMulVec_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  simp [KerrField.signature, Cartesian.eta, hh4, h4, dell4, ddell4, ell4, raised]
  simp [H, HD, HDD, ellD, radiusD, cosineD, twist, rDD, cDD,
    cross_apply, Cartesian.basis]
  field_simp
  grobner (ringSteps := 2000000)

end BlackHole.KerrVacuumJet

namespace BlackHole.KerrField

/-- All spins and positions with positive exact Kerr radius, not an axial
    sample. The other fifteen Ricci components are separate obligations. -/
theorem ricci_time_time_zero (mass : ℝ) (a x : Cartesian.Space) (hr : 0 < Cartesian.radius a x) :
    ricci mass a x 0 0 = 0 := by
  have hu := spatialEll_unit a x hr
  simp [dotProduct, Fin.sum_univ_succ] at hu
  have hunit : Cartesian.spatialEll a x 0^2+Cartesian.spatialEll a x 1^2+
      Cartesian.spatialEll a x 2^2 = 1 := by nlinarith
  rw [ricci_eq_optical_jet mass a x hr 0 0]
  exact KerrVacuumJet.ricci_time_time_zero _ _ _ _ _ _ hunit
    (ne_of_gt (Cartesian.sigma_positive a x hr))

end BlackHole.KerrField
