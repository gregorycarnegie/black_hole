module

public import BlackHole.CameraFrame

@[expose] public section
noncomputable section
namespace BlackHole.Frames

def waveBivector {n : Type*} (k f : n → ℝ) (i j : n) : ℝ := k i*f j-k j*f i

/-- The geometric-optics polarization field k wedge f is gauge invariant. -/
theorem waveBivector_gauge {n : Type*} (k f : n → ℝ) (c : ℝ) (i j : n) :
    waveBivector k (f+c • k) i j = waveBivector k f i j := by
  simp only [waveBivector, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

def screenGauge (k f : Fin 4 → ℝ) : Fin 4 → ℝ :=
  f-(f 0/k 0) • k

theorem screenGauge_time_zero (k f : Fin 4 → ℝ) (hk : k 0 ≠ 0) :
    screenGauge k f 0 = 0 := by
  simp only [screenGauge, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem screenGauge_field (k f : Fin 4 → ℝ) (i j : Fin 4) :
    waveBivector k (screenGauge k f) i j = waveBivector k f i j := by
  simpa only [screenGauge, sub_eq_add_neg, neg_smul] using
    waveBivector_gauge k f (-(f 0/k 0)) i j

/-- ADM screen reset: the gauge-fixed spatial vector is already unit and
    transverse, so exact projection and positive normalization cannot rotate it. -/
theorem adm_screen_reset (gamma : Cartesian.Space →ₗ[ℝ] Cartesian.Space →ₗ[ℝ] ℝ)
    (hsym : ∀ v w, gamma v w = gamma w v)
    (alpha kt ft : ℝ) (beta ks fs : Cartesian.Space)
    (ha : 0 < alpha) (ht : kt ≠ 0)
    (hnull : -(alpha^2*kt^2)+gamma (ks+kt • beta) (ks+kt • beta) = 0)
    (horth : -(alpha^2*kt*ft)+gamma (ks+kt • beta) (fs+ft • beta) = 0)
    (hunit : -(alpha^2*ft^2)+gamma (fs+ft • beta) (fs+ft • beta) = 1) :
    let K := ks+kt • beta
    let e := fs-(ft/kt) • ks
    let n := spatialUnit gamma K
    gamma e e = 1 ∧ gamma n e = 0 ∧
      gamma n n = 1 ∧ spatialUnit gamma (e-(gamma n e) • n) = e := by
  let K := ks+kt • beta
  let E := fs+ft • beta
  let e := fs-(ft/kt) • ks
  have hKK : gamma K K = alpha^2*kt^2 := by linarith
  have hKE : gamma K E = alpha^2*kt*ft := by linarith
  have hEK : gamma E K = alpha^2*kt*ft := by rw [hsym]; exact hKE
  have hEE : gamma E E = 1+alpha^2*ft^2 := by linarith
  have heq : e = E-(ft/kt) • K := by
    ext i
    simp only [e,E,K,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    field_simp
    ring
  have he : gamma e e = 1 := by
    rw [heq]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, hKK, hKE, hEK, hEE]
    field_simp
    ring
  have hKe : gamma K e = 0 := by
    rw [heq]
    simp only [map_sub, map_smul, hKE, hKK, smul_eq_mul]
    field_simp
    ring
  have hn : gamma (spatialUnit gamma K) (spatialUnit gamma K) = 1 :=
    spatialUnit_unit gamma K (by rw [hKK]; positivity)
  have hne : gamma (spatialUnit gamma K) e = 0 := by
    simp only [spatialUnit, map_smul, LinearMap.smul_apply, smul_eq_mul, hKe, mul_zero]
  refine ⟨he,hne,hn,?_⟩
  change spatialUnit gamma (e-(gamma (spatialUnit gamma K) e) • spatialUnit gamma K) = e
  rw [hne, zero_smul, sub_zero]
  simp only [spatialUnit, he, Real.sqrt_one, div_one, one_smul]

end BlackHole.Frames

namespace BlackHole.ADM

theorem pairing_decomposition (g inv : Matrix Index Index ℝ)
    (hinv : g*inv = 1) (hsym : ∀ i j, g i j = g j i) (h00 : inv 0 0 < 0)
    (kt ft : ℝ) (ks fs : Cartesian.Space) :
    dotProduct (Fin.cases kt ks) (g.mulVec (Fin.cases ft fs)) =
      -(lapse inv)^2*kt*ft+spatial g (ks+kt • shift inv) (fs+ft • shift inv) := by
  have hp := metric_decomposition g inv hinv hsym h00 (kt+ft) (ks+fs)
  have hk := metric_decomposition g inv hinv hsym h00 kt ks
  have hf := metric_decomposition g inv hinv hsym h00 ft fs
  simp [norm, spatial, dotProduct, Matrix.mulVec, Fin.sum_univ_succ] at hp hk hf ⊢
  simp only [hsym 1 0, hsym 2 0, hsym 3 0, hsym 2 1, hsym 3 1, hsym 3 2] at hp hk hf ⊢
  linear_combination (hp-hk-hf)/2

end BlackHole.ADM

namespace BlackHole.KerrField

theorem second_screen_orientation (mass : ℝ) (a x n e : Cartesian.Space)
    (hm : 0 ≤ mass) (hr : 0 < Cartesian.radius a x)
    (hn : ADM.spatial (metric mass a x) n n = 1)
    (he : ADM.spatial (metric mass a x) e e = 1)
    (hne : ADM.spatial (metric mass a x) n e = 0) :
    0 < dotProduct (crossProduct n e) (secondScreen mass a x n e) := by
  have hc : dotProduct (crossProduct n e)
      (crossProduct ((spatialMatrix mass a x).mulVec n) ((spatialMatrix mass a x).mulVec e)) = 1 := by
    simp only [cross_dot_cross, spatialMatrix_pairing, hn, he, hne,
      one_mul, zero_mul, sub_zero]
  have hv := second_screen_norm_ge_one mass a x n e hm hr hn he hne
  dsimp only [secondScreen]
  rw [dotProduct_smul, hc, smul_eq_mul, mul_one]
  apply one_div_pos.mpr
  apply Real.sqrt_pos.mpr
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (le_trans hv (le_max_left _ _))

theorem screen_frame_first (mass : ℝ) (a x : Cartesian.Space) (k f : Fin 4 → ℝ)
    (hm : 0 ≤ mass) (hr : 0 < Cartesian.radius a x) (ht : k 0 ≠ 0)
    (hk : dotProduct k ((metric mass a x).mulVec k) = 0)
    (hkf : dotProduct k ((metric mass a x).mulVec f) = 0)
    (hf : dotProduct f ((metric mass a x).mulVec f) = 1) :
    let g := metric mass a x
    let gamma := spatialBilinear mass a x
    let K : Cartesian.Space := (fun i => k i.succ)+(k 0) • ADM.shift g⁻¹
    let n := Frames.spatialUnitScaled gamma K
    let raw : Cartesian.Space := (fun i => f i.succ)-(f 0/k 0) • (fun i => k i.succ)
    let e1 := Frames.spatialUnitScaled gamma (raw-(gamma n raw) • n)
    gamma n n = 1 ∧ gamma e1 e1 = 1 ∧ gamma n e1 = 0 ∧
      ∀ i j, Frames.waveBivector k (Fin.cases 0 e1) i j = Frames.waveBivector k f i j := by
  let g := metric mass a x
  let gamma := spatialBilinear mass a x
  let ks : Cartesian.Space := fun i => k i.succ
  let fs : Cartesian.Space := fun i => f i.succ
  let K := ks+(k 0) • ADM.shift g⁻¹
  let raw := fs-(f 0/k 0) • ks
  have heta (v : Fin 4 → ℝ) : Fin.cases (v 0) (fun i => v i.succ) = v := by
    ext i
    cases i using Fin.cases <;> rfl
  have hinv : g*g⁻¹ = 1 := Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (metric_nonsingular mass a x hr))
  have h00 := inverse_time_negative mass a x hm hr
  have hpair (v w : Fin 4 → ℝ) : dotProduct v (g.mulVec w) =
      -(ADM.lapse g⁻¹)^2*v 0*w 0+
        gamma ((fun i => v i.succ)+(v 0) • ADM.shift g⁻¹)
          ((fun i => w i.succ)+(w 0) • ADM.shift g⁻¹) := by
    dsimp only [gamma]
    rw [spatialBilinear_apply]
    simpa only [heta] using
      ADM.pairing_decomposition g g⁻¹ hinv (metric_symmetric mass a x) h00
        (v 0) (w 0) (fun i => v i.succ) (fun i => w i.succ)
  have hk' : -((ADM.lapse g⁻¹)^2*(k 0)^2)+gamma K K = 0 := by
    rw [hpair] at hk
    nlinarith [hk]
  have hf' : -((ADM.lapse g⁻¹)^2*(f 0)^2)+
      gamma (fs+(f 0) • ADM.shift g⁻¹) (fs+(f 0) • ADM.shift g⁻¹) = 1 := by
    rw [hpair] at hf
    nlinarith [hf]
  have hkf' : -((ADM.lapse g⁻¹)^2*(k 0)*(f 0))+
      gamma K (fs+(f 0) • ADM.shift g⁻¹) = 0 := by
    rw [hpair] at hkf
    nlinarith [hkf]
  obtain ⟨hraw,hne,hn,hreset⟩ := Frames.adm_screen_reset gamma
    (spatialBilinear_symmetric mass a x) (ADM.lapse g⁻¹) (k 0) (f 0)
    (ADM.shift g⁻¹) ks fs (ADM.lapse_identity g⁻¹ h00).1 ht hk' hkf' hf'
  change gamma raw raw = 1 at hraw
  change gamma (Frames.spatialUnit gamma K) raw = 0 at hne
  change gamma (Frames.spatialUnit gamma K) (Frames.spatialUnit gamma K) = 1 at hn
  have hdom := spatialBilinear_dominates_euclidean mass a x hm hr
  have hK0 : K ≠ 0 := by
    intro hz
    simp [hz, Frames.spatialUnit] at hn
  have hnEq : Frames.spatialUnitScaled gamma K = Frames.spatialUnit gamma K :=
    Frames.spatialUnitScaled_eq gamma hdom K hK0
  have hraw0 : raw ≠ 0 := by
    intro hz
    simp [hz] at hraw
  have hfixed : Frames.spatialUnitScaled gamma raw = raw := by
    rw [Frames.spatialUnitScaled_eq gamma hdom raw hraw0]
    simp only [Frames.spatialUnit, hraw, Real.sqrt_one, div_one, one_smul]
  have hrawEq : Fin.cases 0 raw = Frames.screenGauge k f := by
    ext i
    cases i using Fin.cases with
    | zero => exact (Frames.screenGauge_time_zero k f ht).symm
    | succ i => rfl
  change gamma (Frames.spatialUnitScaled gamma K) (Frames.spatialUnitScaled gamma K) = 1 ∧
    gamma (Frames.spatialUnitScaled gamma (raw-(gamma (Frames.spatialUnitScaled gamma K) raw) •
      Frames.spatialUnitScaled gamma K))
      (Frames.spatialUnitScaled gamma (raw-(gamma (Frames.spatialUnitScaled gamma K) raw) •
        Frames.spatialUnitScaled gamma K)) = 1 ∧
    gamma (Frames.spatialUnitScaled gamma K)
      (Frames.spatialUnitScaled gamma (raw-(gamma (Frames.spatialUnitScaled gamma K) raw) •
        Frames.spatialUnitScaled gamma K)) = 0 ∧ _
  rw [hnEq, hne, zero_smul, sub_zero, hfixed]
  refine ⟨hn,hraw,hne,?_⟩
  intro i j
  rw [hrawEq]
  exact Frames.screenGauge_field k f i j

end BlackHole.KerrField
