module

public import BlackHole.CameraFrame

@[expose] public section
noncomputable section
namespace BlackHole.Frames

def pinholeDirection (F R U : Cartesian.Space) (px py : ℝ) : Cartesian.Space :=
  (1/Real.sqrt (1+px^2+py^2)) • (F+px • R-py • U)

theorem pinhole_direction_unit (g : Cartesian.Space →ₗ[ℝ] Cartesian.Space →ₗ[ℝ] ℝ)
    (hsym : ∀ v w, g v w = g w v) (F R U : Cartesian.Space) (px py : ℝ)
    (hF : g F F = 1) (hR : g R R = 1) (hU : g U U = 1)
    (hFR : g F R = 0) (hFU : g F U = 0) (hRU : g R U = 0) :
    g (pinholeDirection F R U px py) (pinholeDirection F R U px py) = 1 := by
  have hs : 0 < 1+px^2+py^2 := by positivity
  have hr0 := ne_of_gt (Real.sqrt_pos.mpr hs)
  have hrsq := Real.sq_sqrt (le_of_lt hs)
  have hRF : g R F = 0 := by rw [hsym]; exact hFR
  have hUF : g U F = 0 := by rw [hsym]; exact hFU
  have hUR : g U R = 0 := by rw [hsym]; exact hRU
  simp only [pinholeDirection, map_smul, map_add, map_sub, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.sub_apply, smul_eq_mul, hF, hR, hU, hFR, hRF, hFU, hUF, hRU, hUR]
  field_simp
  nlinarith

theorem pinhole_screen_projection (g : Cartesian.Space →ₗ[ℝ] Cartesian.Space →ₗ[ℝ] ℝ)
    (hsym : ∀ v w, g v w = g w v) (hdom : ∀ v, dotProduct v v ≤ g v v)
    (F R U : Cartesian.Space) (px py : ℝ)
    (hF : g F F = 1) (hR : g R R = 1) (hU : g U U = 1)
    (hFR : g F R = 0) (hFU : g F U = 0) (hRU : g R U = 0) :
    let s := 1+px^2+py^2
    let n := pinholeDirection F R U px py
    let residual := R-(g n R) • n
    let screen := spatialUnitScaled g residual
    g n n = 1 ∧ spatialUnitScaled g n = n ∧ g residual residual = (1+py^2)/s ∧
      g n screen = 0 ∧ g screen screen = 1 := by
  let s : ℝ := 1+px^2+py^2
  let root := Real.sqrt s
  let n := (1/root) • (F+px • R-py • U)
  let residual := R-(g n R) • n
  have hs : 0 < s := by dsimp only [s]; positivity
  have hr : 0 < root := Real.sqrt_pos.mpr hs
  have hr0 := ne_of_gt hr
  have hrsq : root^2 = s := Real.sq_sqrt (le_of_lt hs)
  have hn : g n n = 1 := pinhole_direction_unit g hsym F R U px py hF hR hU hFR hFU hRU
  have hUR : g U R = 0 := by rw [hsym]; exact hRU
  have hnR : g n R = px/root := by
    simp only [n, map_smul, map_add, map_sub, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.sub_apply, smul_eq_mul, hFR, hR, hUR]
    ring
  have hRn : g R n = px/root := by rw [hsym]; exact hnR
  have hres : g residual residual = 1-(px/root)^2 := by
    simp only [residual, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, hn, hnR, hRn, hR]
    ring
  have hresEq : g residual residual = (1+py^2)/s := by
    rw [hres]
    calc
      _ = (root^2-px^2)/root^2 := by field_simp
      _ = (1+py^2)/s := by rw [hrsq]; congr 1; dsimp only [s]; ring
  have hresPos : 0 < g residual residual := by rw [hresEq]; positivity
  have hres0 : residual ≠ 0 := by
    intro hz
    simp [hz] at hresPos
  have hn0 : n ≠ 0 := by
    intro hz
    simp [hz] at hn
  have hnFixed : spatialUnitScaled g n = n := by
    rw [spatialUnitScaled_eq g hdom n hn0]
    simp [spatialUnit, hn]
  have hscreen := screen_projection_unit g n R hn hresPos
  change g n n = 1 ∧ spatialUnitScaled g n = n ∧ g residual residual = (1+py^2)/s ∧
    g n (spatialUnitScaled g residual) = 0 ∧
      g (spatialUnitScaled g residual) (spatialUnitScaled g residual) = 1
  simp only [spatialUnitScaled_eq g hdom residual hres0]
  exact ⟨hn, hnFixed, hresEq, hscreen⟩

end BlackHole.Frames

namespace BlackHole.KerrField

theorem camera_pinhole_initialization (mass : ℝ) (a x F R U : Cartesian.Space) (px py : ℝ)
    (hm : 0 ≤ mass) (hr : 0 < Cartesian.radius a x)
    (hF : ADM.spatial (metric mass a x) F F = 1)
    (hR : ADM.spatial (metric mass a x) R R = 1)
    (hU : ADM.spatial (metric mass a x) U U = 1)
    (hFR : ADM.spatial (metric mass a x) F R = 0)
    (hFU : ADM.spatial (metric mass a x) F U = 0)
    (hRU : ADM.spatial (metric mass a x) R U = 0) :
    let g := metric mass a x
    let inv := g⁻¹
    let direction := Frames.pinholeDirection F R U px py
    0 < ADM.observer inv 0 ∧
      dotProduct (ADM.observer inv) (g.mulVec (ADM.observer inv)) = -1 ∧
      dotProduct (g.mulVec (ADM.pastTangent inv direction)) (ADM.observer inv) = 1 ∧
      ADM.norm g (-1/ADM.lapse inv) (direction+(1/ADM.lapse inv) • ADM.shift inv) = 0 := by
  have hn := Frames.pinhole_direction_unit (spatialBilinear mass a x)
    (spatialBilinear_symmetric mass a x) F R U px py
  simp only [spatialBilinear_apply] at hn
  exact camera_initialization mass a x _ hm hr (hn hF hR hU hFR hFU hRU)

end BlackHole.KerrField
