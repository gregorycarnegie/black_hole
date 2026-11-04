module
public import BlackHole.KerrVacuumMixedFirst
public import BlackHole.KerrJetCycle
import Mathlib.Tactic.FinCases

@[expose] public section
noncomputable section
namespace BlackHole.KerrVacuumJet

theorem ricci_time_space_zero (S r c m : ℝ) (l v : Cartesian.Space)
    (hunit : l 0^2+l 1^2+l 2^2 = 1) (hS : S ≠ 0)
    (hsigma : S = r^2+c^2) (i : Fin 3) :
    Curvature.ricci (inv S r m l) (dg S r c m l v) (ddg S r c m l v) 0 i.succ = 0 := by
  have h0 := ricci_time_space_first_zero S r c m l v hunit hS hsigma
  have h1 := ricci_time_space_first_zero S r c m (cycleSpace l) (cycleSpace v)
    (unit_cycle l hunit) hS hsigma
  have h2 := ricci_time_space_first_zero S r c m (cycleSpace (cycleSpace l)) (cycleSpace (cycleSpace v))
    (unit_cycle _ (unit_cycle l hunit)) hS hsigma
  fin_cases i
  · exact h0
  · change Curvature.ricci (inv S r m l) (dg S r c m l v) (ddg S r c m l v) 0 2 = 0
    simpa only [ricci_cycle, cycle4_zero, cycle4_one] using h1
  · change Curvature.ricci (inv S r m l) (dg S r c m l v) (ddg S r c m l v) 0 3 = 0
    simpa only [ricci_cycle, cycle4_zero, cycle4_one, cycle4_two] using h2

end BlackHole.KerrVacuumJet
