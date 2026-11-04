module

public import BlackHole.Dynamics
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section
noncomputable section
namespace BlackHole.Dynamics

abbrev Vector := Fin 3 → ℝ

def pairDistance (x y : Vector) : ℝ := Real.sqrt (dotProduct (y-x) (y-x))

theorem pairDistance_symmetric (x y : Vector) : pairDistance x y = pairDistance y x := by
  unfold pairDistance
  have he : y-x = -(x-y) := by ext i; simp
  rw [he, neg_dotProduct, dotProduct_neg, neg_neg]

def pairAcceleration {n : Type*} [DecidableEq n] (mass : n → ℝ) (position : n → Vector)
    (i j : n) : Vector :=
  if i = j then 0 else
    let diff := position j-position i
    let dist := pairDistance (position i) (position j)
    if 0 < dist then (mass j/(dist*dist)) • ((1/dist) • diff) else 0

theorem loop_pair_force_antisymmetric {n : Type*} [DecidableEq n]
    (mass : n → ℝ) (position : n → Vector) (i j : n) :
    mass i • pairAcceleration mass position i j =
      -(mass j • pairAcceleration mass position j i) := by
  by_cases hij : i = j
  · subst j
    simp [pairAcceleration]
  have hji : j ≠ i := Ne.symm hij
  simp only [pairAcceleration, hij, hji, ite_false]
  rw [pairDistance_symmetric (position j) (position i)]
  split_ifs
  · ext c
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
    ring
  · simp

def loopAcceleration {n : Type*} [Fintype n] [DecidableEq n]
    (mass : n → ℝ) (position : n → Vector) (i : n) : Vector :=
  ∑ j, pairAcceleration mass position i j

theorem loop_total_force_zero {n : Type*} [Fintype n] [DecidableEq n]
    (mass : n → ℝ) (position : n → Vector) :
    (∑ i, mass i • loopAcceleration mass position i) = 0 := by
  ext c
  simp only [loopAcceleration, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    Pi.zero_apply]
  apply antisymmetric_forces_sum_zero
  intro i j
  exact congrFun (loop_pair_force_antisymmetric mass position i j) c

def loopVelocity {n : Type*} [Fintype n] [DecidableEq n]
    (mass : n → ℝ) (position velocity : n → Vector) (h : ℝ) (i : n) : Vector :=
  velocity i+h • loopAcceleration mass position i

def loopPosition {n : Type*} [Fintype n] [DecidableEq n]
    (mass : n → ℝ) (position velocity : n → Vector) (h : ℝ) (i : n) : Vector :=
  position i+h • loopVelocity mass position velocity h i

theorem loop_preserves_momentum {n : Type*} [Fintype n] [DecidableEq n]
    (mass : n → ℝ) (position velocity : n → Vector) (h : ℝ) :
    (∑ i, mass i • loopVelocity mass position velocity h i) = ∑ i, mass i • velocity i := by
  ext c
  have hf := congrFun (loop_total_force_zero mass position) c
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hf
  simp only [loopVelocity, Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  exact velocity_update_preserves_momentum mass (fun i => velocity i c)
    (fun i => loopAcceleration mass position i c) h hf

theorem loop_mass_position_drift {n : Type*} [Fintype n] [DecidableEq n]
    (mass : n → ℝ) (position velocity : n → Vector) (h : ℝ) :
    (∑ i, mass i • loopPosition mass position velocity h i) =
      (∑ i, mass i • position i)+h • (∑ i, mass i • velocity i) := by
  simp only [loopPosition, smul_add, smul_smul, Finset.sum_add_distrib]
  have hcomm : (∑ i, (mass i*h) • loopVelocity mass position velocity h i) =
      h • (∑ i, mass i • loopVelocity mass position velocity h i) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul, mul_comm]
  rw [hcomm, loop_preserves_momentum]

def loopStep {n : Type*} [Fintype n] [DecidableEq n] (mass : n → ℝ) (h : ℝ)
    (state : (n → Vector) × (n → Vector)) : (n → Vector) × (n → Vector) :=
  (loopPosition mass state.1 state.2 h, loopVelocity mass state.1 state.2 h)

theorem iterated_loop_preserves_momentum {n : Type*} [Fintype n] [DecidableEq n]
    (mass : n → ℝ) (h : ℝ) (state : (n → Vector) × (n → Vector)) (steps : ℕ) :
    (∑ i, mass i • ((loopStep mass h)^[steps] state).2 i) = ∑ i, mass i • state.2 i := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    rw [Function.iterate_succ_apply']
    exact (loop_preserves_momentum mass _ _ h).trans ih

end BlackHole.Dynamics
