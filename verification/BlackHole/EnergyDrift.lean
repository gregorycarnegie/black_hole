module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Energy drift of the production Newtonian update (obligation D2).

`gravity_system` performs symplectic Euler with Bevy's fixed step
`h = 1/64` (`Units.fixed_step_exact`): velocities are updated from the
pairwise accelerations `m_j / |x_j - x_i|²`, then positions from the new
velocities. `Dynamics.symplectic_euler_energy_drift` showed the energy is not
conserved exactly. This file shows that no bound on the drift holds uniformly
over admissible initial states, even for one step, so a long-time bound needs
additional hypotheses (for example a minimum separation over the run). -/

@[expose] public section
noncomputable section

namespace BlackHole.EnergyDrift

/-- Production fixed step. -/
def step : ℝ := 1/64

/-- Two masses ½ at rest at `±x` on a line. After one production update each
    moves inward with speed `v = h·½/(2x)²`, and the separation becomes
    `2x - 2hv`. The drift is the new total energy minus the old one. -/
def drift (x : ℝ) : ℝ :=
  let v := step*(1/2)/(2*x)^2
  let d := 2*x-2*step*v
  (2*((1/2)*(1/2)*v^2)-(1/2)*(1/2)/d)-(-(1/2)*(1/2)/(2*x))

/-- The separation after the step vanishes at `x = 1/32`. -/
theorem collapse_point : 2*(1/32:ℝ)-2*step*(step*(1/2)/(2*(1/32))^2) = 0 := by
  norm_num [step]

/-- For every bound `B` some initial separation makes the one-step energy
    drift fall below `-B`. Hence the production integrator admits no uniform
    energy-drift bound, over one step or over long times. -/
theorem drift_unbounded (B : ℝ) : ∃ x > 0, drift x < -B := by
  set t : ℝ := 1/(24*(|B|+7)) with ht
  have hB := abs_nonneg B
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1/168 := by
    rw [ht, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine ⟨1/32+t, by positivity, ?_⟩
  set x := 1/32+t with hx
  have hx0 : 0 < x := by positivity
  have hx32 : 1/32 ≤ x := by linarith
  unfold drift step
  simp only
  set v := (1/64:ℝ)*(1/2)/(2*x)^2 with hv
  set d := 2*x-2*(1/64)*v with hd
  -- The kinetic term stays below 2.
  have hv0 : 0 ≤ v := by positivity
  have hv2 : v ≤ 2 := by
    rw [hv, div_le_iff₀ (by positivity)]
    nlinarith
  have hkin : 2*((1/2:ℝ)*(1/2)*v^2) ≤ 2 := by nlinarith
  -- The initial potential term is at most 4 in magnitude.
  have hpot0 : -(-(1/2:ℝ)*(1/2)/(2*x)) ≤ 4 := by
    rw [neg_mul, neg_div, neg_neg, div_le_iff₀ (by positivity)]
    nlinarith
  -- The new separation is positive and at most 6t.
  have hdx : d = 2*x-1/(2^14*x^2) := by
    rw [hd, hv]
    field_simp
    ring
  have hdpos : 0 < d := by
    rw [hdx, sub_pos, div_lt_iff₀ (by positivity)]
    nlinarith [mul_pos hx0 hx0]
  have hd6 : d ≤ 6*t := by
    rw [hdx]
    have key : (1/16-4*t)*x^2 ≤ 1/2^14 := by
      rw [hx]
      nlinarith [sq_nonneg t, mul_pos ht0 (mul_pos ht0 ht0)]
    have : 1/16-4*t ≤ 1/(2^14*x^2) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    linarith
  -- So the new potential term is below -(|B|+7).
  have hpot1 : (1/2:ℝ)*(1/2)/d ≥ |B|+7 := by
    rw [ge_iff_le, le_div_iff₀ hdpos]
    have : 6*t*(|B|+7) = 1/4 := by
      rw [ht]
      field_simp
      ring
    nlinarith
  have hBle : -B ≥ -|B| := by linarith [le_abs_self B]
  linarith

end BlackHole.EnergyDrift
