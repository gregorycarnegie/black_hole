module
public import BlackHole.KerrVacuumSpatial11
public import BlackHole.KerrJetCycle

@[expose] public section
noncomputable section
namespace BlackHole.KerrVacuumJet

theorem ricci_space_22_zero (S r c m : ℝ) (l v : Cartesian.Space)
    (hunit : l 0^2+l 1^2+l 2^2 = 1) (hS : S ≠ 0) (hsigma : S = r^2+c^2) :
    Curvature.ricci (inv S r m l) (dg S r c m l v) (ddg S r c m l v) 2 2 = 0 := by
  have h := ricci_space_11_zero S r c m (cycleSpace l) (cycleSpace v)
    (unit_cycle l hunit) hS hsigma
  simpa only [ricci_cycle, cycle4_one] using h

end BlackHole.KerrVacuumJet
