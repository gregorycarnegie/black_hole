module

public import BlackHole.KerrVacuumTime
public import BlackHole.KerrVacuumMixed
public import BlackHole.KerrVacuumSpatial
public import BlackHole.KerrConnectionTrace

@[expose] public section
noncomputable section

namespace BlackHole.KerrField

theorem ricci_time_space_zero (mass : ℝ) (a x : Cartesian.Space)
    (hr : 0 < Cartesian.radius a x) (i : Fin 3) : ricci mass a x 0 i.succ = 0 := by
  have hu := spatialEll_unit a x hr
  simp [dotProduct, Fin.sum_univ_succ] at hu
  have hunit : Cartesian.spatialEll a x 0^2+Cartesian.spatialEll a x 1^2+
      Cartesian.spatialEll a x 2^2 = 1 := by nlinarith
  rw [ricci_eq_optical_jet mass a x hr]
  exact KerrVacuumJet.ricci_time_space_zero _ _ _ _ _ _ hunit
    (ne_of_gt (Cartesian.sigma_positive a x hr)) rfl i

theorem ricci_space_space_zero (mass : ℝ) (a x : Cartesian.Space)
    (hr : 0 < Cartesian.radius a x) (i j : Fin 3) : ricci mass a x i.succ j.succ = 0 := by
  have hu := spatialEll_unit a x hr
  simp [dotProduct, Fin.sum_univ_succ] at hu
  have hunit : Cartesian.spatialEll a x 0^2+Cartesian.spatialEll a x 1^2+
      Cartesian.spatialEll a x 2^2 = 1 := by nlinarith
  by_cases hij : i ≤ j
  · rw [ricci_eq_optical_jet mass a x hr]
    exact KerrVacuumJet.ricci_space_space_zero _ _ _ _ _ _ hunit
      (ne_of_gt (Cartesian.sigma_positive a x hr)) rfl i j hij
  · rw [ricci_symmetric mass a x hr, ricci_eq_optical_jet mass a x hr]
    exact KerrVacuumJet.ricci_space_space_zero _ _ _ _ _ _ hunit
      (ne_of_gt (Cartesian.sigma_positive a x hr)) rfl j i (le_of_lt (lt_of_not_ge hij))

/-- The complete exact Cartesian Kerr metric is Ricci-flat for every spin
    vector and mass at every position with positive Kerr radius. -/
theorem ricci_zero (mass : ℝ) (a x : Cartesian.Space)
    (hr : 0 < Cartesian.radius a x) (i j : Fin 4) : ricci mass a x i j = 0 := by
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact ricci_time_time_zero mass a x hr
    | succ j => exact ricci_time_space_zero mass a x hr j
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      rw [ricci_symmetric mass a x hr]
      exact ricci_time_space_zero mass a x hr i
    | succ j => exact ricci_space_space_zero mass a x hr i j

theorem ricci_matrix_zero (mass : ℝ) (a x : Cartesian.Space)
    (hr : 0 < Cartesian.radius a x) :
    (fun i j => ricci mass a x i j) = (0 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  exact ricci_zero mass a x hr i j

end BlackHole.KerrField
