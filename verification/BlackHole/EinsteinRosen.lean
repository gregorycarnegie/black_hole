module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/- Collas & Klein, arXiv:1107.4871, Eqs. (3), (5), (21), (22), (24).
   R = r/r_s, u = Kruskal space, v = Kruskal time. The Rust display uses
   r_s = 2, |v| <= 0.95. These are real equations, not float error bounds. -/
@[expose] public section
noncomputable section

namespace BlackHole.EinsteinRosen

def kruskal (R : ℝ) : ℝ := (R - 1) * Real.exp R
def radialDerivative (rs R u : ℝ) : ℝ := 2 * rs * u / (R * Real.exp R)
def heightDerivative (rs R v : ℝ) : ℝ :=
  2 * rs * Real.sqrt (Real.exp R - v^2) / (R * Real.exp R)

theorem kruskal_derivative (R : ℝ) :
    HasDerivAt kruskal (R * Real.exp R) R := by
  convert (((hasDerivAt_id R).sub_const 1).mul (Real.hasDerivAt_exp R)) using 1
  · funext x
    dsimp [kruskal]
  · simp only [id_eq]
    ring

/-- Positive derivative gives unique radius inversion on the physical domain. -/
theorem kruskal_strictMono : StrictMonoOn kruskal (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · exact fun R _ => (kruskal_derivative R).continuousAt.continuousWithinAt
  · intro R hR
    rw [interior_Ici] at hR
    rw [(kruskal_derivative R).deriv]
    exact mul_pos hR (Real.exp_pos R)

theorem unique_radius (R S u v : ℝ) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hr : kruskal R = u^2 - v^2) (hs : kruskal S = u^2 - v^2) : R = S :=
  kruskal_strictMono.injOn hR hS (hr.trans hs.symm)

theorem height_radicand_positive (R v : ℝ) (hR : 0 ≤ R) (hv : v^2 < 1) :
    0 < Real.exp R - v^2 := by
  have := Real.one_le_exp hR
  linarith

/-- The slopes implemented in Rust induce exactly the constant-v spatial metric. -/
theorem induced_metric (rs R u v : ℝ) (hR : 0 < R) (hv : v^2 < 1)
    (h : kruskal R = u^2 - v^2) :
    radialDerivative rs R u ^ 2 + heightDerivative rs R v ^ 2 =
      4 * rs^2 / (R * Real.exp R) := by
  have he := ne_of_gt (Real.exp_pos R)
  have hr := ne_of_gt hR
  have hs := Real.sq_sqrt (le_of_lt (height_radicand_positive R v hR.le hv))
  unfold radialDerivative heightDerivative
  simp only [div_pow, mul_pow, hs]
  unfold kruskal at h
  field_simp [hr, he]
  nlinarith [h]

/-- At maximum extent the throat is r_s; both signed sheets have r >= r_s. -/
theorem time_zero_throat (R : ℝ) (hR : 0 ≤ R) (h : kruskal R = 0) : R = 1 := by
  apply kruskal_strictMono.injOn hR (by norm_num : (1 : ℝ) ∈ Set.Ici 0)
  simpa [kruskal] using h

theorem time_zero_exterior (R u : ℝ) (h : kruskal R = u^2) : 1 ≤ R := by
  have he := Real.exp_pos R
  unfold kruskal at h
  nlinarith [sq_nonneg u]

/-- For equal u, increasing |v| strictly contracts the areal radius. -/
theorem throat_contracts (R S v w : ℝ) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hv : kruskal R = -v^2) (hw : kruskal S = -w^2) (ht : v^2 < w^2) : S < R := by
  by_contra hn
  have hle := kruskal_strictMono.monotoneOn hR hS (le_of_not_gt hn)
  linarith

/-- Necessary endpoint cone inequality forbids future travel from exterior I to III. -/
theorem no_exterior_causal_segment (u₀ v₀ u₁ v₁ : ℝ)
    (hstart : |v₀| < u₀) (hend : u₁ < -|v₁|)
    (hcausal : |u₁ - u₀| ≤ v₁ - v₀) : False := by
  have h₀ := neg_abs_le v₀
  have h₁ := le_abs_self v₁
  have hΔ := neg_abs_le (u₁ - u₀)
  linarith

/-- Eq. (5) with nonpositive spacetime norm and future dv gives the cone condition. -/
theorem cone_from_metric (C angular du dv : ℝ) (hC : 0 < C) (ha : 0 ≤ angular)
    (hf : 0 ≤ dv) (hc : C * (du^2 - dv^2) + angular ≤ 0) : |du| ≤ dv := by
  have hsq : du^2 ≤ dv^2 := by nlinarith
  apply (sq_le_sq₀ (abs_nonneg du) hf).mp
  simpa only [sq_abs] using hsq

/-- A differentiable future causal curve has monotone u+v, so it cannot join
    the two exteriors. The cone condition is supplied by cone_from_metric. -/
theorem future_curve_cannot_cross (u v du dv : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hu : ∀ s ∈ Set.Icc a b, HasDerivAt u (du s) s)
    (hv : ∀ s ∈ Set.Icc a b, HasDerivAt v (dv s) s)
    (hcone : ∀ s ∈ Set.Icc a b, |du s| ≤ dv s)
    (hstart : |v a| < u a) (hend : u b < -|v b|) : False := by
  have hsum (s : ℝ) (hs : s ∈ Set.Icc a b) := (hu s hs).add (hv s hs)
  have hm : MonotoneOn (fun s => u s + v s) (Set.Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · exact fun s hs => (hsum s hs).continuousAt.continuousWithinAt
    · exact fun s hs => (hsum s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      change 0 ≤ deriv (u + v) s
      rw [(hsum s (interior_subset hs)).deriv]
      have := hcone s (interior_subset hs)
      have := neg_abs_le (du s)
      linarith
  have hle := hm (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) hab
  have h₀ := neg_abs_le (v a)
  have h₁ := le_abs_self (v b)
  linarith

end BlackHole.EinsteinRosen
