module

public import BlackHole.Numerics
public import BlackHole.Binary
public import BlackHole.Schwarzschild
public import BlackHole.MetricInverse
public import BlackHole.BinaryCurvature
public import BlackHole.Calculus
public import BlackHole.Transfer
public import BlackHole.TransferBounds
public import BlackHole.Composition
public import BlackHole.Stokes
public import BlackHole.Dynamics
public import BlackHole.NewtonianLoop
public import BlackHole.Frames
public import BlackHole.ADM
public import BlackHole.Models
public import BlackHole.Plasma
public import BlackHole.PlasmaEmission
public import BlackHole.PlasmaFluid
public import BlackHole.Orbits
public import BlackHole.KerrGeodesics
public import BlackHole.KerrEquatorial
public import BlackHole.SnapshotChart
public import BlackHole.RayConditioning
public import BlackHole.KerrAlgebra
public import BlackHole.KerrCartesian
public import BlackHole.KerrSecond
public import BlackHole.KerrCurvature
public import BlackHole.CurvaturePermutation
public import BlackHole.KerrInverse
public import BlackHole.KerrOptical
public import BlackHole.KerrOpticalSecond
public import BlackHole.KerrRankDerivative
public import BlackHole.KerrPath
public import BlackHole.KerrSmoothness
public import BlackHole.KerrCamera
public import BlackHole.ScreenFrame
public import BlackHole.ScreenGauge
public import BlackHole.CameraFrame
public import BlackHole.RayGrowth
public import BlackHole.KerrDerivativeBounds
public import BlackHole.KerrBounds
public import BlackHole.CameraPinhole
public import BlackHole.OrbitalCamera
public import BlackHole.KerrVacuumJet
public import BlackHole.KerrJetBridge
public import BlackHole.KerrJetCycle
public import BlackHole.KerrConnectionTrace
public import BlackHole.KerrVacuumTime
public import BlackHole.KerrVacuum
public import BlackHole.AdaptiveStep
public import BlackHole.RadialRK4
public import BlackHole.Transport
public import BlackHole.Hamiltonian
public import BlackHole.Binary32Bounds
public import BlackHole.Units
public import BlackHole.EnergyDrift
public import BlackHole.KerrRadialStability
public import BlackHole.MatrixTransfer
public import BlackHole.WgslSum
public import BlackHole.WgslKerrRadius
public import BlackHole.TransferPhi
public import BlackHole.WgslSinCos
public import BlackHole.RK4Consistency
public import BlackHole.RK4Stability
public import BlackHole.RK4Uniform
public import BlackHole.KerrContinuation
public import BlackHole.KerrArithmetic
public import BlackHole.KerrCertificate
public import BlackHole.KerrReduced
public import BlackHole.ScaledCertificate
public import BlackHole.DyadicInterval
public import BlackHole.IntervalJet
public import BlackHole.DirectionError
public import BlackHole.CheckedData
public import BlackHole.RayCertificate
public import BlackHole.RK4Order
public import BlackHole.TaylorLine
public import BlackHole.WgslTransferPhi
public import BlackHole.WgslGeodesic
public import BlackHole.WgslAddKerr
public import BlackHole.WgslPlasma
public import BlackHole.WgslCounterexamples
public import BlackHole.WgslAtan2
public import BlackHole.KernelFixture
public import BlackHole.WgslSafe
public import BlackHole.WgslSafeDomains
public import BlackHole.WgslSafeNear
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Ring

/-! Exact-real specifications of selected simulation equations.
These are manually transcribed models, not verification of Rust/WESL execution. -/

public section
noncomputable section

namespace BlackHole

def horizon (a : ℝ) : ℝ := 1 + Real.sqrt (1 - a * a)

theorem horizon_zero : horizon 0 = 2 := by norm_num [horizon]

theorem horizon_even (a : ℝ) : horizon (-a) = horizon a := by
  simp [horizon]

theorem horizon_bounds (a : ℝ) (ha : a * a ≤ 1) :
    1 ≤ horizon a ∧ horizon a ≤ 2 := by
  have hs := Real.sqrt_nonneg (1 - a * a)
  have hsq := Real.sq_sqrt (by linarith : 0 ≤ 1 - a * a)
  have haa := sq_nonneg a
  constructor <;> unfold horizon <;> nlinarith

theorem horizon_solves_delta (a : ℝ) (ha : a * a ≤ 1) :
    horizon a ^ 2 - 2 * horizon a + a * a = 0 := by
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1 - a * a)
  unfold horizon
  nlinarith

theorem horizon_antitone (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    : horizon b ≤ horizon a := by
  have hsq : a * a ≤ b * b := by nlinarith
  unfold horizon
  have h := Real.sqrt_le_sqrt (show 1 - b*b ≤ 1 - a*a by linarith)
  linarith

theorem horizon_mass_scaling (m a : ℝ) (hm : 0 < m) (ha : a * a ≤ 1) :
    m ≤ m * horizon a ∧ m * horizon a ≤ 2 * m := by
  obtain ⟨hl, hu⟩ := horizon_bounds a ha
  constructor <;> nlinarith

theorem isco_outside_horizon (a : ℝ) (ha : |a| < 1) : horizon a < isco a := by
  have ha_le := le_of_lt ha
  have hr := isco_strictAnti a 1 ha_le (by norm_num) (lt_of_le_of_lt (le_abs_self a) ha)
  rw [isco_extremal_prograde] at hr
  have hroot : 1 < Real.sqrt (3*isco a-2) := by
    have hs := Real.sq_sqrt (show 0 ≤ 3*isco a-2 by linarith)
    nlinarith [Real.sqrt_nonneg (3*isco a-2)]
  have hdelta : 0 < isco a^2-2*isco a+a^2 := by
    rw [isco_delta a ha_le]
    exact mul_pos (mul_pos (by norm_num) (by linarith))
      (sq_pos_of_pos (by linarith))
  have ha2 : 0 ≤ 1-a^2 := by nlinarith [sq_abs a, abs_nonneg a]
  have hs := Real.sq_sqrt ha2
  have hsq : (Real.sqrt (1-a^2))^2 < (isco a-1)^2 := by nlinarith
  have hlt := (sq_lt_sq₀ (Real.sqrt_nonneg (1-a^2)) (show 0 ≤ isco a-1 by linarith)).mp hsq
  unfold horizon
  have heq : a*a = a^2 := by ring
  rw [heq]
  linarith

/- Sherman-Morrison as a linear operator: A is the old metric, B its inverse,
   u is ell and c = 2H. No null-vector assumption is made for multiple sources. -/
section Inverse
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem sherman_morrison (A B : V →ₗ[ℝ] V) (L : V →ₗ[ℝ] ℝ)
    (u v : V) (c : ℝ) (hAB : ∀ x, A (B x) = x)
    (hd : 1 + c * L (B u) ≠ 0) :
    let w := B v - (c / (1 + c * L (B u)) * L (B v)) • B u
    A w + (c * L w) • u = v := by
  dsimp
  simp only [map_sub, map_smul, hAB, smul_eq_mul]
  have hc : -(c / (1 + c * L (B u)) * L (B v)) +
      c * (L (B v) - c / (1 + c * L (B u)) * L (B v) * L (B u)) = 0 := by
    field_simp; ring
  rw [sub_eq_add_neg, ← neg_smul, add_assoc, ← add_smul, hc, zero_smul, add_zero]

end Inverse

/- init_ray uses an Eulerian observer n with g(n,n) = -1 and a spatial unit
   direction s orthogonal to n. Its past-directed tangent is -n+s. -/
section NullRay
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem eulerian_null (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (n s : V)
    (hn : g n n = -1) (hs : g s s = 1)
    (hns : g n s = 0) (hsn : g s n = 0) :
    g (-n + s) (-n + s) = 0 := by
  simp [map_add, map_neg, hn, hs, hns, hsn]

/-- The gauge reset in screen_frame preserves screen norm and transversality. -/
theorem screen_gauge (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (k f : V) (c : ℝ)
    (hk : g k k = 0) (hkf : g k f = 0) (hfk : g f k = 0) :
    g k (f + c • k) = 0 ∧ g (f + c • k) (f + c • k) = g f f := by
  simp [map_add, map_smul, hk, hkf, hfk]

end NullRay

/-- The shader's positive 1/2 in dp_i/dλ cancels the inverse-metric term
    in d(p·Kp)/dλ. Index 0 may be included with dg[0] = 0 (stationarity). -/
theorem hamiltonian_constraint_rate {n : Type*} [Fintype n]
    (k : n → ℝ) (dg : n → Matrix n n ℝ) :
    2 * (∑ i, ((1 / 2 : ℝ) * dotProduct k ((dg i).mulVec k)) * k i) -
      (∑ i, k i * dotProduct k ((dg i).mulVec k)) = 0 := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro i _
  ring

end BlackHole
