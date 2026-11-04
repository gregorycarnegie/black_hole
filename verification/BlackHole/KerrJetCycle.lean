module

public import BlackHole.KerrJetBridge
public import BlackHole.CurvaturePermutation
import Mathlib.Tactic.FinCases

@[expose] public section
noncomputable section
namespace BlackHole.KerrVacuumJet

def cycle3 : Fin 3 ≃ Fin 3 where
  toFun := ![1,2,0]
  invFun := ![2,0,1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def cycle4 : Fin 4 ≃ Fin 4 where
  toFun := ![0,2,3,1]
  invFun := ![0,3,1,2]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

@[simp] theorem cycle4_zero : cycle4 (0 : Fin 4) = 0 := rfl
@[simp] theorem cycle4_one : cycle4 (1 : Fin 4) = 2 := rfl
@[simp] theorem cycle4_two : cycle4 (2 : Fin 4) = 3 := rfl
@[simp] theorem cycle4_three : cycle4 (3 : Fin 4) = 1 := rfl

def cycleSpace (l : Cartesian.Space) : Cartesian.Space := fun i => l (cycle3 i)

theorem unit_cycle (l : Cartesian.Space) (hunit : l 0^2+l 1^2+l 2^2 = 1) :
    cycleSpace l 0^2+cycleSpace l 1^2+cycleSpace l 2^2 = 1 := by
  change l 1^2+l 2^2+l 0^2 = 1
  nlinarith

theorem inv_cycle (S r m : ℝ) (l : Cartesian.Space) :
    inv S r m (cycleSpace l) = fun i j => inv S r m l (cycle4 i) (cycle4 j) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem dg_cycle (S r c m : ℝ) (l v : Cartesian.Space) :
    dg S r c m (cycleSpace l) (cycleSpace v) =
      fun e i j => dg S r c m l v (cycle4 e) (cycle4 i) (cycle4 j) := by
  ext e i j
  fin_cases e <;> fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem ddg_cycle (S r c m : ℝ) (l v : Cartesian.Space) :
    ddg S r c m (cycleSpace l) (cycleSpace v) =
      fun e f i j => ddg S r c m l v (cycle4 e) (cycle4 f) (cycle4 i) (cycle4 j) := by
  ext e f i j
  fin_cases e <;> fin_cases f <;> fin_cases i <;> fin_cases j <;> rfl

theorem ricci_cycle (S r c m : ℝ) (l v : Cartesian.Space) (i j : Fin 4) :
    Curvature.ricci (inv S r m (cycleSpace l)) (dg S r c m (cycleSpace l) (cycleSpace v))
      (ddg S r c m (cycleSpace l) (cycleSpace v)) i j =
      Curvature.ricci (inv S r m l) (dg S r c m l v) (ddg S r c m l v) (cycle4 i) (cycle4 j) := by
  rw [inv_cycle, dg_cycle, ddg_cycle]
  exact Curvature.ricci_reindex cycle4 _ _ _ i j

end BlackHole.KerrVacuumJet
