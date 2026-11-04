module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

@[expose] public section
noncomputable section

namespace BlackHole.Dynamics

/-- One Cartesian component of the Newtonian pair force in gravity_system.
    r is the shared pair distance; the coincident-point branch sets both forces
    to zero and also satisfies the antisymmetry used below. -/
theorem pair_force_antisymmetric (m1 m2 x1 x2 r : ℝ) :
    m1*(m2*(x2-x1)/r^3) = -(m2*(m1*(x1-x2)/r^3)) := by ring

theorem antisymmetric_forces_sum_zero {n : Type*} [Fintype n]
    (force : n → n → ℝ) (hforce : ∀ i j, force i j = -force j i) :
    (∑ i, ∑ j, force i j) = 0 := by
  have hneg : (∑ i, ∑ j, force i j) = -(∑ i, ∑ j, force i j) := by
    calc
      _ = ∑ i, ∑ j, -force j i := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact hforce i j
      _ = -(∑ i, ∑ j, force j i) := by simp only [Finset.sum_neg_distrib]
      _ = -(∑ i, ∑ j, force i j) := by rw [Finset.sum_comm]
  linarith

theorem velocity_update_preserves_momentum {n : Type*} [Fintype n]
    (mass velocity acceleration : n → ℝ) (h : ℝ)
    (hforce : (∑ i, mass i*acceleration i) = 0) :
    (∑ i, mass i*(velocity i+h*acceleration i)) = ∑ i, mass i*velocity i := by
  simp_rw [mul_add, mul_left_comm (mass _ ) h]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hforce]
  ring

/-- Exact-real symplectic Euler is not exactly energy conserving, even for a
    two-body Newtonian scene. Equal masses 1/2 at x=±1, v=0, h=1 produce
    velocities ±1/8 and positions ±7/8 under the production update order. -/
theorem symplectic_euler_energy_drift :
    let mass : ℝ := 1/2
    let velocity := mass/2^2
    let radius := 1-velocity
    let initialEnergy := -(mass*mass)/2
    let finalEnergy := mass*velocity^2-(mass*mass)/(2*radius)
    finalEnergy-initialEnergy = -9/896 := by norm_num

theorem unit_conversion_consistency (G mass c : ℝ) (hc : c ≠ 0) :
    (G*mass/c^2)/(G*mass/c^3) = c ∨ G*mass = 0 := by
  by_cases hm : G*mass = 0
  · exact Or.inr hm
  left
  field_simp [hm]
  exact div_self hm

end BlackHole.Dynamics
