module
public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.MeanValue

/-! A computable residual certificate for a proposed ODE segment. The tube
condition supplies existence and containment, rather than assuming that the
unknown exact trajectory stays in the region used to bound the Jacobian. -/

@[expose] public section
noncomputable section
open Set Metric
open scoped NNReal
namespace BlackHole.ValidatedStep

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The derivative matrix is its action on the coordinate basis. -/
theorem linear_map_matrix_apply {n : ℕ}
    (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (v : Fin n → ℝ) (i : Fin n) :
    L v i = ∑ j, L (Pi.single j 1) i*v j := by
  have hsum : (∑ j : Fin n, v j • Pi.single j (1:ℝ)) = v := by
    funext k
    simp [Pi.single_apply]
  conv_lhs => rw [← hsum]
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Row sums certify the operator norm of a Jacobian in the sup norm. -/
theorem jacobian_norm_bound {n : ℕ}
    (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (A : Fin n → Fin n → ℝ)
    (happly : ∀ v i, L v i = ∑ j, A i j*v j)
    (K : ℝ) (hK : 0 ≤ K) (hrow : ∀ i, (∑ j, |A i j|) ≤ K) : ‖L‖ ≤ K := by
  apply L.opNorm_le_bound hK
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hK (norm_nonneg v))).mpr
  intro i
  rw [Real.norm_eq_abs,happly]
  calc
    |∑ j, A i j*v j| ≤ ∑ j, |A i j*v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |A i j| * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm v j) (abs_nonneg _)
    _ = (∑ j, |A i j|)*‖v‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ K*‖v‖ := mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg v)

omit [CompleteSpace E] in
/-- The fixed uncertainty of a scalar parameter is bounded by its Jacobian
column on the complete parameter interval. -/
theorem parameter_forcing (f derivative : ℝ → E) (nominal parameter uncertainty M : ℝ)
    (hr : 0 ≤ uncertainty) (hM : 0 ≤ M)
    (hp : parameter ∈ Icc (nominal-uncertainty) (nominal+uncertainty))
    (hf : ∀ p ∈ Icc (nominal-uncertainty) (nominal+uncertainty),
      HasDerivWithinAt f (derivative p) (Icc (nominal-uncertainty) (nominal+uncertainty)) p)
    (hb : ∀ p ∈ Icc (nominal-uncertainty) (nominal+uncertainty), ‖derivative p‖ ≤ M) :
    ‖f parameter-f nominal‖ ≤ M*uncertainty := by
  have hn : nominal ∈ Icc (nominal-uncertainty) (nominal+uncertainty) := by
    constructor <;> linarith
  have he := (convex_Icc (nominal-uncertainty) (nominal+uncertainty)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hf hb hn hp
  have hd : |parameter-nominal| ≤ uncertainty := by
    apply abs_le.mpr
    constructor <;> linarith [hp.1,hp.2]
  exact he.trans (by simpa only [Real.norm_eq_abs] using mul_le_mul_of_nonneg_left hd hM)

/-- The rational bound used by the interval controller implies Picard inclusion. -/
theorem rational_inclusion {h K initial defect radius : ℝ}
    (hK : h*K < 1)
    (hb : (initial+h*defect)/(1-h*K) ≤ radius) :
    initial+h*(defect+K*radius) ≤ radius := by
  have hd : 0 < 1-h*K := by linarith
  have := (div_le_iff₀ hd).mp hb
  nlinarith

/-- Construct an exact solution in a moving tube from a residual, a local
Lipschitz bound and a checked inclusion inequality. No exact flow is assumed. -/
theorem exists_solution_in_tube
    (f : E → E) (proposal rate : ℝ → E) (x : E)
    (h : ℝ) (hh : 0 ≤ h) (initial radius defect : ℝ≥0) (K : ℝ≥0)
    (hproposal : ∀ t ∈ Icc 0 h, HasDerivWithinAt proposal (rate t) (Icc 0 h) t)
    (hcontinuous : ContinuousOn (fun z : ℝ × E => f (proposal z.1+z.2)-rate z.1)
      ((Icc 0 h) ×ˢ closedBall 0 radius))
    (hlip : ∀ t ∈ Icc 0 h, LipschitzOnWith K f (closedBall (proposal t) radius))
    (hdefect : ∀ t ∈ Icc 0 h, ‖f (proposal t)-rate t‖ ≤ defect)
    (hx : ‖x-proposal 0‖ ≤ initial)
    (hinclude : initial+h*(defect+K*radius) ≤ radius) :
    ∃ sol : ℝ → E, sol 0 = x ∧
      (∀ t ∈ Icc 0 h, HasDerivWithinAt sol (f (sol t)) (Icc 0 h) t) ∧
      ∀ t ∈ Icc 0 h, ‖sol t-proposal t‖ ≤ radius := by
  let g : ℝ → E → E := fun t e => f (proposal t+e)-rate t
  let L : ℝ≥0 := defect+K*radius
  let t0 : Icc (0:ℝ) h := ⟨0, le_rfl, hh⟩
  have hball {e : E} (he : e ∈ closedBall 0 (radius:ℝ)) (t : ℝ) :
      proposal t+e ∈ closedBall (proposal t) (radius:ℝ) := by
    simpa [mem_closedBall, dist_eq_norm] using he
  have hsize : (L:ℝ)*h ≤ radius-initial := by
    dsimp [L]
    linarith
  have hpl : IsPicardLindelof g t0 (0:E) radius initial L K := by
    constructor
    · intro t ht
      apply LipschitzOnWith.of_dist_le_mul
      intro e he v hv
      simpa [g, dist_eq_norm] using (hlip t ht).dist_le_mul
        (proposal t+e) (hball he t) (proposal t+v) (hball hv t)
    · intro e he
      exact hcontinuous.comp (continuousOn_id.prodMk continuousOn_const) (fun t ht => ⟨ht,he⟩)
    · intro t ht e he
      calc
        ‖g t e‖ ≤ ‖f (proposal t+e)-f (proposal t)‖+‖f (proposal t)-rate t‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ K*‖e‖+defect := by
          apply add_le_add _ (hdefect t ht)
          simpa only [add_sub_cancel_left] using (hlip t ht).norm_sub_le
            (hball he t) (mem_closedBall_self (NNReal.coe_nonneg radius))
        _ ≤ L := by
          have he' : ‖e‖ ≤ (radius:ℝ) := by simpa [mem_closedBall,dist_eq_norm] using he
          change (K:ℝ)*‖e‖+defect ≤ (defect:ℝ)+(K:ℝ)*radius
          linarith [mul_le_mul_of_nonneg_left he' (NNReal.coe_nonneg K)]
    · simpa [t0, max_eq_left hh] using hsize
  have hxin : x-proposal 0 ∈ closedBall (0:E) (initial:ℝ) := by
    simpa [mem_closedBall, dist_eq_norm] using hx
  obtain ⟨α,hα⟩ := ODE.FunSpace.exists_isFixedPt_next hpl hxin
  let error : ℝ → E := α.compProj
  have herr (t : ℝ) : ‖error t‖ ≤ radius := by
    simpa [error, mem_closedBall, dist_eq_norm] using
      α.compProj_mem_closedBall hpl.mul_max_le (t := t)
  have hcont : ContinuousOn error (Icc 0 h) := α.continuous_compProj.continuousOn
  have hpic (t : ℝ) (ht : t ∈ Icc 0 h) :
      error t = ODE.picard g 0 (x-proposal 0) error t := by
    have hp := (ODE.FunSpace.isFixedPt_next_iff hpl hxin).mp hα ⟨t,ht⟩
    simpa [error, ODE.FunSpace.compProj_apply, projIcc_of_mem _ ht] using hp
  have hder (t : ℝ) (ht : t ∈ Icc 0 h) :
      HasDerivWithinAt error (g t (error t)) (Icc 0 h) t := by
    apply (ODE.hasDerivWithinAt_picard_Icc t0.2 hcontinuous hcont
      (fun u _ => by simpa [mem_closedBall,dist_eq_norm] using herr u) (x-proposal 0) ht).congr
    · intro u hu
      exact hpic u hu
    · exact hpic t ht
  refine ⟨fun t => proposal t+error t, ?_, ?_, ?_⟩
  · have hp := hpic 0 ⟨le_rfl,hh⟩
    simp only [ODE.picard_apply, intervalIntegral.integral_same, add_zero] at hp
    change proposal 0+error 0 = x
    rw [hp]
    abel
  · intro t ht
    have hd := (hproposal t ht).add (hder t ht)
    have hc : rate t+g t (error t) = f (proposal t+error t) := by dsimp [g]; abel
    rw [hc] at hd
    exact hd
  · intro t _
    simpa using herr t

end BlackHole.ValidatedStep
