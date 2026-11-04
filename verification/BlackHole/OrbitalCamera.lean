module

public import BlackHole.CameraPinhole
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section
noncomputable section
namespace BlackHole.Camera

def elevation (e : ℝ) : ℝ := min (max e (1/100)) (Real.pi-1/100)

theorem elevation_domain (e : ℝ) : 0 < elevation e ∧ elevation e < Real.pi := by
  have hp := Real.two_le_pi
  have hl : (1/100 : ℝ) ≤ elevation e :=
    le_min (le_max_right _ _) (by linarith)
  have hu : elevation e ≤ Real.pi-1/100 := min_le_right _ _
  constructor <;> linarith

def position (r theta phi : ℝ) : Cartesian.Space :=
  ![r*Real.sin theta*Real.cos phi, r*Real.cos theta, r*Real.sin theta*Real.sin phi]

def unit (v : Cartesian.Space) : Cartesian.Space := (1/Real.sqrt (dotProduct v v)) • v

def forward (r theta phi : ℝ) : Cartesian.Space := unit (-position r theta phi)

def right (r theta phi : ℝ) : Cartesian.Space :=
  unit (crossProduct (forward r theta phi) ![0,1,0])

def up (r theta phi : ℝ) : Cartesian.Space :=
  crossProduct (right r theta phi) (forward r theta phi)

theorem position_norm (r theta phi : ℝ) :
    dotProduct (position r theta phi) (position r theta phi) = r^2 := by
  have ht := Real.sin_sq_add_cos_sq theta
  have hp := Real.sin_sq_add_cos_sq phi
  simp [position, dotProduct, Fin.sum_univ_succ]
  linear_combination r^2*(Real.sin theta)^2*hp+r^2*ht

theorem forward_formula (r theta phi : ℝ) (hr : 0 < r) :
    forward r theta phi = ![-Real.sin theta*Real.cos phi,-Real.cos theta,
      -Real.sin theta*Real.sin phi] := by
  have hn : dotProduct (-position r theta phi) (-position r theta phi) = r^2 := by
    simpa only [neg_dotProduct, dotProduct_neg, neg_neg] using position_norm r theta phi
  simp only [forward, unit, hn, Real.sqrt_sq_eq_abs, abs_of_pos hr]
  ext i
  fin_cases i <;> simp [position] <;> field_simp

theorem right_formula (r theta phi : ℝ) (hr : 0 < r)
    (ht : 0 < theta) (htp : theta < Real.pi) :
    right r theta phi = ![Real.sin phi,0,-Real.cos phi] := by
  have hs := Real.sin_pos_of_pos_of_lt_pi ht htp
  have hc : crossProduct (forward r theta phi) ![0,1,0] =
      Real.sin theta • ![Real.sin phi,0,-Real.cos phi] := by
    rw [forward_formula r theta phi hr]
    ext i
    fin_cases i <;> simp [cross_apply]
  have hn : dotProduct (Real.sin theta • ![Real.sin phi,0,-Real.cos phi])
      (Real.sin theta • ![Real.sin phi,0,-Real.cos phi]) = (Real.sin theta)^2 := by
    simp [dotProduct, Fin.sum_univ_succ]
    nlinarith [Real.sin_sq_add_cos_sq phi]
  simp only [right, hc, unit, hn, Real.sqrt_sq_eq_abs, abs_of_pos hs, smul_smul]
  rw [one_div_mul_cancel (ne_of_gt hs), one_smul]

theorem basis_orthonormal (r theta phi : ℝ) (hr : 0 < r)
    (ht : 0 < theta) (htp : theta < Real.pi) :
    let f := forward r theta phi
    let q := right r theta phi
    let u := up r theta phi
    dotProduct f f = 1 ∧ dotProduct q q = 1 ∧ dotProduct u u = 1 ∧
      dotProduct f q = 0 ∧ dotProduct f u = 0 ∧ dotProduct q u = 0 := by
  have hf : dotProduct (forward r theta phi) (forward r theta phi) = 1 := by
    rw [forward_formula r theta phi hr]
    simp [dotProduct, Fin.sum_univ_succ]
    linear_combination (Real.sin theta)^2*(Real.sin_sq_add_cos_sq phi)+
      (Real.sin_sq_add_cos_sq theta)
  have hq : dotProduct (right r theta phi) (right r theta phi) = 1 := by
    rw [right_formula r theta phi hr ht htp]
    simp [dotProduct, Fin.sum_univ_succ]
    nlinarith [Real.sin_sq_add_cos_sq phi]
  have hfq : dotProduct (forward r theta phi) (right r theta phi) = 0 := by
    rw [forward_formula r theta phi hr, right_formula r theta phi hr ht htp]
    simp [dotProduct, Fin.sum_univ_succ]
    ring
  have hqf : dotProduct (right r theta phi) (forward r theta phi) = 0 := by
    rw [dotProduct_comm]; exact hfq
  refine ⟨hf,hq,?_,hfq,?_,?_⟩
  · simp only [up, cross_dot_cross, hf, hq, hfq, hqf]
    norm_num
  · exact dot_cross_self _ _
  · exact dot_self_cross _ _

theorem clamped_basis_orthonormal (r e phi : ℝ) (hr : 0 < r) :
    let f := forward r (elevation e) phi
    let q := right r (elevation e) phi
    let u := up r (elevation e) phi
    dotProduct f f = 1 ∧ dotProduct q q = 1 ∧ dotProduct u u = 1 ∧
      dotProduct f q = 0 ∧ dotProduct f u = 0 ∧ dotProduct q u = 0 := by
  exact basis_orthonormal r (elevation e) phi hr (elevation_domain e).1 (elevation_domain e).2

theorem pinhole_coordinates (f q u : Cartesian.Space) (px py : ℝ)
    (hf : dotProduct f f = 1) (hq : dotProduct q q = 1) (hu : dotProduct u u = 1)
    (hfq : dotProduct f q = 0) (hfu : dotProduct f u = 0) (hqu : dotProduct q u = 0) :
    let d := Frames.pinholeDirection f q u px py
    dotProduct d f = 1/Real.sqrt (1+px^2+py^2) ∧
      dotProduct d q = px/Real.sqrt (1+px^2+py^2) ∧
      dotProduct d u = -py/Real.sqrt (1+px^2+py^2) := by
  have hqf : dotProduct q f = 0 := by rw [dotProduct_comm]; exact hfq
  have huf : dotProduct u f = 0 := by rw [dotProduct_comm]; exact hfu
  have huq : dotProduct u q = 0 := by rw [dotProduct_comm]; exact hqu
  dsimp only
  simp only [Frames.pinholeDirection, smul_dotProduct, add_dotProduct, sub_dotProduct,
    smul_eq_mul, hf, hq, hu, hfq, hfu, hqu, hqf, huf, huq]
  constructor
  · ring
  constructor <;> ring

theorem pinhole_normalize (f q u : Cartesian.Space) (px py : ℝ)
    (hf : dotProduct f f = 1) (hq : dotProduct q q = 1) (hu : dotProduct u u = 1)
    (hfq : dotProduct f q = 0) (hfu : dotProduct f u = 0) (hqu : dotProduct q u = 0) :
    unit (f+px • q-py • u) = Frames.pinholeDirection f q u px py := by
  have hqf : dotProduct q f = 0 := by rw [dotProduct_comm]; exact hfq
  have huf : dotProduct u f = 0 := by rw [dotProduct_comm]; exact hfu
  have huq : dotProduct u q = 0 := by rw [dotProduct_comm]; exact hqu
  have hn : dotProduct (f+px • q-py • u) (f+px • q-py • u) = 1+px^2+py^2 := by
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_add, add_dotProduct,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hf, hq, hu, hfq, hfu, hqu, hqf, huf, huq]
    ring
  simp only [unit, hn, Frames.pinholeDirection]

theorem pinhole_reconstruction (f q u F R U : Cartesian.Space) (px py : ℝ)
    (hf : dotProduct f f = 1) (hq : dotProduct q q = 1) (hu : dotProduct u u = 1)
    (hfq : dotProduct f q = 0) (hfu : dotProduct f u = 0) (hqu : dotProduct q u = 0) :
    let d := unit (f+px • q-py • u)
    (dotProduct d f) • F+(dotProduct d q) • R+(dotProduct d u) • U =
      Frames.pinholeDirection F R U px py := by
  dsimp only
  rw [pinhole_normalize f q u px py hf hq hu hfq hfu hqu]
  obtain ⟨hf',hq',hu'⟩ := pinhole_coordinates f q u px py hf hq hu hfq hfu hqu
  rw [hf',hq',hu']
  ext i
  simp only [Frames.pinholeDirection, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem kerr_gram_schmidt (mass r e phi : ℝ) (a x : Cartesian.Space)
    (hm : 0 ≤ mass) (hr : 0 < r) (hx : 0 < Cartesian.radius a x) :
    let f := forward r (elevation e) phi
    let q := right r (elevation e) phi
    let u := up r (elevation e) phi
    let g := KerrField.spatialBilinear mass a x
    let F := Frames.spatialUnit g f
    let R0 := q-(g F q) • F
    let R := Frames.spatialUnit g R0
    let U0 := u-(g F u) • F-(g R u) • R
    let U := Frames.spatialUnit g U0
    1 ≤ g f f ∧ 1 ≤ g R0 R0 ∧ 1 ≤ g U0 U0 ∧
      g F F = 1 ∧ g R R = 1 ∧ g U U = 1 ∧ g F R = 0 ∧ g F U = 0 ∧ g R U = 0 := by
  obtain ⟨hf,hq,hu,hfq,hfu,hqu⟩ := clamped_basis_orthonormal r e phi hr
  exact KerrField.camera_gram_schmidt_defined mass a x _ _ _ hm hx hf hq hu hfq hfu hqu

theorem kerr_source_pinhole_frame (mass r e phi px py : ℝ) (a x : Cartesian.Space)
    (hm : 0 ≤ mass) (hr : 0 < r) (hx : 0 < Cartesian.radius a x) :
    let f := forward r (elevation e) phi
    let q := right r (elevation e) phi
    let u := up r (elevation e) phi
    let gamma := KerrField.spatialBilinear mass a x
    let F := Frames.spatialUnitScaled gamma f
    let R := Frames.spatialUnitScaled gamma (q-(gamma F q) • F)
    let U := Frames.spatialUnitScaled gamma (u-(gamma F u) • F-(gamma R u) • R)
    let dir := unit (f+px • q-py • u)
    let n := Frames.spatialUnitScaled gamma
      ((dotProduct dir f) • F+(dotProduct dir q) • R+(dotProduct dir u) • U)
    let screen := Frames.spatialUnitScaled gamma (R-(gamma n R) • n)
    gamma n n = 1 ∧ gamma n screen = 0 ∧ gamma screen screen = 1 := by
  let f := forward r (elevation e) phi
  let q := right r (elevation e) phi
  let u := up r (elevation e) phi
  let gamma := KerrField.spatialBilinear mass a x
  let F := Frames.spatialUnitScaled gamma f
  let R := Frames.spatialUnitScaled gamma (q-(gamma F q) • F)
  let U := Frames.spatialUnitScaled gamma (u-(gamma F u) • F-(gamma R u) • R)
  let dir := unit (f+px • q-py • u)
  let n0 := Frames.pinholeDirection F R U px py
  have hsym := KerrField.spatialBilinear_symmetric mass a x
  have hdom := KerrField.spatialBilinear_dominates_euclidean mass a x hm hx
  obtain ⟨hf,hq,hu,hfq,hfu,hqu⟩ := clamped_basis_orthonormal r e phi hr
  obtain ⟨hF,hR,hU,hFR,hFU,hRU⟩ :=
    Frames.camera_gram_schmidt_scaled gamma hsym hdom f q u hf hq hu hfq hfu hqu
  have hdir : (dotProduct dir f) • F+(dotProduct dir q) • R+(dotProduct dir u) • U = n0 :=
    pinhole_reconstruction f q u F R U px py hf hq hu hfq hfu hqu
  obtain ⟨hn,hfixed,_,hns,hss⟩ :=
    Frames.pinhole_screen_projection gamma hsym hdom F R U px py hF hR hU hFR hFU hRU
  change gamma (Frames.spatialUnitScaled gamma
      ((dotProduct dir f) • F+(dotProduct dir q) • R+(dotProduct dir u) • U))
      (Frames.spatialUnitScaled gamma
        ((dotProduct dir f) • F+(dotProduct dir q) • R+(dotProduct dir u) • U)) = 1 ∧ _
  rw [hdir, hfixed]
  exact ⟨hn,hns,hss⟩

end BlackHole.Camera
