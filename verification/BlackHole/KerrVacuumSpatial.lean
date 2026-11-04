module
public import BlackHole.KerrVacuumSpatial11
public import BlackHole.KerrVacuumSpatial12
public import BlackHole.KerrVacuumSpatial13
public import BlackHole.KerrVacuumSpatial22
public import BlackHole.KerrVacuumSpatial23
public import BlackHole.KerrVacuumSpatial33
import Mathlib.Tactic.FinCases

@[expose] public section
noncomputable section
namespace BlackHole.KerrVacuumJet

theorem ricci_space_space_zero (S r c m : ℝ) (l v : Cartesian.Space)
    (hunit : l 0^2+l 1^2+l 2^2 = 1) (hS : S ≠ 0)
    (hsigma : S = r^2+c^2) (i j : Fin 3) (hij : i ≤ j) :
    Curvature.ricci (inv S r m l) (dg S r c m l v) (ddg S r c m l v) i.succ j.succ = 0 := by
  fin_cases i <;> fin_cases j
  all_goals norm_num at hij
  all_goals first
    | exact ricci_space_11_zero S r c m l v hunit hS hsigma
    | exact ricci_space_12_zero S r c m l v hunit hS hsigma
    | exact ricci_space_13_zero S r c m l v hunit hS hsigma
    | exact ricci_space_22_zero S r c m l v hunit hS hsigma
    | exact ricci_space_23_zero S r c m l v hunit hS hsigma
    | exact ricci_space_33_zero S r c m l v hunit hS hsigma

end BlackHole.KerrVacuumJet
