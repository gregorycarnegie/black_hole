module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section

namespace BlackHole.Frames

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def spatialUnit (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (v : V) : V :=
  (1/Real.sqrt (g v v)) • v

theorem spatialUnit_unit (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (v : V) (hv : 0 < g v v) :
    g (spatialUnit g v) (spatialUnit g v) = 1 := by
  have h := Real.sq_sqrt (le_of_lt hv)
  have hn := ne_of_gt (Real.sqrt_pos.mpr hv)
  simp only [spatialUnit, map_smul, LinearMap.smul_apply, smul_eq_mul]
  field_simp
  nlinarith

theorem projection_orthogonal (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (u v : V)
    (hu : g u u = 1) : g u (v-(g u v) • u) = 0 := by
  simp [map_sub, map_smul, hu]

theorem projection_nonzero (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (u v : V)
    (h : ∀ c : ℝ, v ≠ c • u) : v-(g u v) • u ≠ 0 := by
  exact sub_ne_zero.mpr (h (g u v))

theorem two_projections_orthogonal (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (u v w : V)
    (hu : g u u = 1) (hv : g v v = 1) (huv : g u v = 0) (hvu : g v u = 0) :
    g u (w-(g u w) • u-(g v w) • v) = 0 ∧
      g v (w-(g u w) • u-(g v w) • v) = 0 := by
  simp [map_sub, map_smul, hu, hv, huv, hvu]

theorem normalization_preserves_orthogonality (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (u v : V)
    (huv : g u v = 0) : g u (spatialUnit g v) = 0 := by
  simp [spatialUnit, map_smul, huv]

theorem normalization_floor_inactive (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (v : V) (floor : ℝ)
    (hfloor : floor ≤ g v v) :
    (1/Real.sqrt (max (g v v) floor)) • v = spatialUnit g v := by
  simp [spatialUnit, max_eq_left hfloor]

theorem fluid_field_projection (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (fluid b : V)
    (hu : g fluid fluid = -1) : g (b+(g b fluid) • fluid) fluid = 0 := by
  simp [map_add, map_smul, LinearMap.smul_apply, hu]

theorem fluid_screen_projection (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (fluid e k : V)
    (energy : ℝ) (he : energy ≠ 0) (henergy : g k fluid = energy) :
    g (e-(g e fluid/energy) • k) fluid = 0 := by
  simp [map_sub, map_smul, henergy, he]

/-- ADM metric in lapse/shift form, signature (-,+,+,+). -/
def admNorm (gamma : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (alpha time : ℝ) (beta space : V) : ℝ :=
  -(alpha^2*time^2)+gamma (space+time • beta) (space+time • beta)

theorem past_null_initialization (gamma : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (alpha : ℝ) (beta direction : V) (ha : alpha ≠ 0)
    (hdir : gamma direction direction = 1) :
    admNorm gamma alpha (-1/alpha) beta (direction+(1/alpha) • beta) = 0 := by
  have hshift : direction+(1/alpha) • beta+(-1/alpha) • beta = direction := by
    rw [add_assoc, ← add_smul]
    have hz : 1/alpha+(-1)/alpha = 0 := by ring
    rw [hz, zero_smul, add_zero]
  unfold admNorm
  rw [hshift, hdir]
  field_simp
  norm_num

theorem past_direction (alpha : ℝ) (ha : 0 < alpha) : -1/alpha < 0 := by
  exact div_neg_of_neg_of_pos (by norm_num) ha

theorem screen_projection_unit (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (direction right : V)
    (hdir : g direction direction = 1)
    (hpos : 0 < g (right-(g direction right) • direction) (right-(g direction right) • direction)) :
    let screen := spatialUnit g (right-(g direction right) • direction)
    g direction screen = 0 ∧ g screen screen = 1 := by
  dsimp
  exact ⟨normalization_preserves_orthogonality g direction _ (projection_orthogonal g _ _ hdir),
    spatialUnit_unit g _ hpos⟩

def timelikeUnit (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (v : V) : V :=
  (1/Real.sqrt (-g v v)) • v

theorem timelikeUnit_normalized (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (v : V) (hv : g v v < 0) :
    g (timelikeUnit g v) (timelikeUnit g v) = -1 := by
  have hs := Real.sq_sqrt (le_of_lt (neg_pos.mpr hv))
  have hn := ne_of_gt (Real.sqrt_pos.mpr (neg_pos.mpr hv))
  simp only [timelikeUnit, map_smul, LinearMap.smul_apply, smul_eq_mul]
  field_simp
  nlinarith

/-- A past-directed unit-energy ray has positive energy in every normalized
    future timelike fluid frame, given the positive spatial ADM metric. -/
theorem fluid_photon_energy_positive (gamma : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsym : ∀ v w, gamma v w = gamma w v) (hpositive : ∀ v, 0 ≤ gamma v v)
    (alpha time : ℝ) (beta space direction : V) (ha : 0 < alpha) (ht : 0 < time)
    (hdir : gamma direction direction = 1)
    (hfluid : admNorm gamma alpha time beta space = -1) :
    0 < alpha*time+gamma direction (space+time • beta) := by
  let w := space+time • beta
  let d := gamma direction w
  have hcs := hpositive (w-d • direction)
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hdir,
    hsym w direction] at hcs
  change -(alpha^2*time^2)+gamma w w = -1 at hfluid
  have ha0 : 0 < alpha*time := mul_pos ha ht
  have hsq : d^2 < (alpha*time)^2 := by
    dsimp only [d] at *
    nlinarith
  have habs : |d| < alpha*time :=
    (sq_lt_sq₀ (abs_nonneg d) (le_of_lt ha0)).mp (by simpa only [sq_abs] using hsq)
  change 0 < alpha*time+d
  linarith [neg_abs_le d]

theorem projected_field_bound (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (fluid b e1 e2 : V)
    (hsym : ∀ v w, g v w = g w v)
    (hrest : ∀ v, g v fluid = 0 → 0 ≤ g v v)
    (hb : g b b = 1) (hbfluid : g b fluid = 0)
    (h1 : g e1 e1 = 1) (h2 : g e2 e2 = 1) (h12 : g e1 e2 = 0)
    (h1fluid : g e1 fluid = 0) (h2fluid : g e2 fluid = 0) :
    (g b e1)^2+(g b e2)^2 ≤ 1 := by
  let v := b-(g b e1) • e1-(g b e2) • e2
  have hv : g v fluid = 0 := by
    simp [v, map_sub, map_smul, hbfluid, h1fluid, h2fluid]
  have hp := hrest v hv
  simp only [v, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hb, h1, h2, h12,
    hsym e2 e1, hsym e1 b, hsym e2 b] at hp
  nlinarith

end BlackHole.Frames
