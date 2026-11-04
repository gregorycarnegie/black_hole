module

public import BlackHole.TransferBounds
public import BlackHole.Composition
public import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.Push

@[expose] public section
noncomputable section

namespace BlackHole

open intervalIntegral

theorem polarized_coefficient_norm (alpha w s : ℝ) (hs : 0 ≤ s)
    (hd : alpha^2+w^2 ≠ 0) :
    Calculus.cosineIntegral alpha w s^2+Calculus.sineIntegral alpha w s^2 ≤
      absorption alpha s^2 := by
  let z := fun t => (Calculus.cosineIntegral alpha w t : ℂ)+
    (Calculus.sineIntegral alpha w t : ℂ)*Complex.I
  let f := fun t => (Real.exp (-alpha*t) : ℂ)*
    ((Real.cos (w*t) : ℂ)+(Real.sin (w*t) : ℂ)*Complex.I)
  have hz (t : ℝ) : HasDerivAt z (f t) t := by
    have h := (Calculus.cosineIntegral_derivative alpha w t hd).ofReal_comp.add
      ((Calculus.sineIntegral_derivative alpha w t hd).ofReal_comp.mul_const Complex.I)
    simp only [Pi.add_def] at h
    convert h using 1
    dsimp [f]
    push_cast
    ring
  have hnorm (t : ℝ) : ‖f t‖ = Real.exp (-alpha*t) := by
    have hunit : ‖(Real.cos (w*t) : ℂ)+(Real.sin (w*t) : ℂ)*Complex.I‖ = 1 := by
      have he : ‖(Real.cos (w*t) : ℂ)+(Real.sin (w*t) : ℂ)*Complex.I‖^2 = 1 := by
        rw [Complex.sq_norm]
        simpa only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
          Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          mul_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add, sq] using
            Real.cos_sq_add_sin_sq (w*t)
      nlinarith [norm_nonneg ((Real.cos (w*t) : ℂ)+(Real.sin (w*t) : ℂ)*Complex.I)]
    dsimp [f]
    rw [norm_mul, hunit, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hint := integral_eq_sub_of_hasDerivAt (fun t _ => hz t)
    (show IntervalIntegrable f MeasureTheory.volume 0 s from
      Continuous.intervalIntegrable (by dsimp [f]; fun_prop) _ _)
  have hzero : z 0 = 0 := by
    simp [z, (Calculus.polarized_coefficients_zero alpha w).1,
      (Calculus.polarized_coefficients_zero alpha w).2]
  rw [hzero, sub_zero] at hint
  have hb := norm_integral_le_integral_norm (μ := MeasureTheory.volume) (f := f) hs
  simp_rw [hnorm] at hb
  rw [hint, ← absorption_as_integral] at hb
  have he : ‖z s‖^2 = Calculus.cosineIntegral alpha w s^2+
      Calculus.sineIntegral alpha w s^2 := by
    rw [Complex.sq_norm]
    simp [z, Complex.normSq, sq]
  simpa only [he] using pow_le_pow_left₀ (norm_nonneg (z s)) hb 2

theorem cellPolarization_contraction (axis j : Fin 3 → ℝ) (alpha w s : ℝ)
    (haxis : dotProduct axis axis = 1) (hs : 0 ≤ s) (hd : alpha^2+w^2 ≠ 0) :
    dotProduct (cellPolarization axis j alpha w s) (cellPolarization axis j alpha w s) ≤
      absorption alpha s^2*dotProduct j j := by
  have hperp : 0 ≤ dotProduct j j-(dotProduct axis j)^2 := by
    have h : 0 ≤ dotProduct (j-dotProduct axis j • axis) (j-dotProduct axis j • axis) :=
      Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, haxis, dotProduct_comm j axis] at h
    nlinarith
  have hcross : crossProduct axis (j-dotProduct axis j • axis) = crossProduct axis j := by
    simp [map_sub, map_smul, cross_self]
  have heq : dotProduct (cellPolarization axis j alpha w s) (cellPolarization axis j alpha w s) =
      absorption alpha s^2*(dotProduct axis j)^2+
      (Calculus.cosineIntegral alpha w s^2+Calculus.sineIntegral alpha w s^2)*
        (dotProduct j j-(dotProduct axis j)^2) := by
    simp only [cellPolarization, hcross, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, dotProduct_sub, sub_dotProduct, smul_eq_mul,
      cross_dot_cross, dot_cross_self, dot_self_cross,
      dotProduct_comm j axis, dotProduct_comm (crossProduct axis j) j,
      dotProduct_comm (crossProduct axis j) axis, haxis]
    ring
  rw [heq]
  have h := mul_le_mul_of_nonneg_right (polarized_coefficient_norm alpha w s hs hd) hperp
  nlinarith

theorem cell_emission_stokes_cone (axis j : Fin 3 → ℝ) (intensity alpha w s : ℝ)
    (haxis : dotProduct axis axis = 1) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hd : alpha^2+w^2 ≠ 0)
    (hi : 0 ≤ intensity) (hj : dotProduct j j ≤ intensity^2) :
    0 ≤ intensity*absorption alpha s ∧
    dotProduct (cellPolarization axis j alpha w s) (cellPolarization axis j alpha w s) ≤
      (intensity*absorption alpha s)^2 := by
  constructor
  · exact mul_nonneg hi (absorption_nonneg_of_nonneg alpha s ha hs)
  · calc
      _ ≤ absorption alpha s^2*dotProduct j j := cellPolarization_contraction axis j alpha w s haxis hs hd
      _ ≤ absorption alpha s^2*intensity^2 := mul_le_mul_of_nonneg_left hj (sq_nonneg _)
      _ = _ := by ring

theorem stokes_cone_add (p q : Fin 3 → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : dotProduct p p ≤ a^2) (hq : dotProduct q q ≤ b^2) :
    dotProduct (p+q) (p+q) ≤ (a+b)^2 := by
  have hcs : (dotProduct p q)^2 ≤ dotProduct p p*dotProduct q q := by
    simpa only [dotProduct, pow_two] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ p q
  have hqq : 0 ≤ dotProduct q q := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hsq : (dotProduct p q)^2 ≤ (a*b)^2 := by
    calc
      _ ≤ dotProduct p p*dotProduct q q := hcs
      _ ≤ a^2*b^2 := mul_le_mul hp hq hqq (sq_nonneg a)
      _ = _ := by ring
  have hpq : dotProduct p q ≤ a*b := by
    by_cases h : dotProduct p q ≤ 0
    · exact h.trans (mul_nonneg ha hb)
    · exact (sq_le_sq₀ (le_of_lt (lt_of_not_ge h)) (mul_nonneg ha hb)).mp hsq
  simp only [dotProduct_add, add_dotProduct, dotProduct_comm q p]
  nlinarith

/-- Every exact cell preserves the physical Stokes cone. Induction therefore
    covers any finite sequence of cells, with independently varying axes and
    coefficients; zero-Faraday cells reduce to positive scalar transfer. -/
theorem transferCell_stokes_cone (axis j p : Fin 3 → ℝ) (intensity emission alpha w s : ℝ)
    (haxis : dotProduct axis axis = 1) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hd : alpha^2+w^2 ≠ 0) (hi : 0 ≤ intensity) (he : 0 ≤ emission)
    (hp : dotProduct p p ≤ intensity^2) (hj : dotProduct j j ≤ emission^2) :
    let newIntensity := Real.exp (-alpha*s)*intensity+emission*absorption alpha s
    0 ≤ newIntensity ∧
      dotProduct (transferCell axis j alpha w s p) (transferCell axis j alpha w s p) ≤ newIntensity^2 := by
  obtain ⟨hc0, hc⟩ := cell_emission_stokes_cone axis j emission alpha w s haxis ha hs hd he hj
  have hr := faraday_rotation_preserves_norm axis p (w*s) haxis
  have hh : dotProduct (homogeneous axis p alpha w s) (homogeneous axis p alpha w s) ≤
      (Real.exp (-alpha*s)*intensity)^2 := by
    simp only [homogeneous, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    change dotProduct (rotate axis (w*s) p) (rotate axis (w*s) p) = dotProduct p p at hr
    rw [hr]
    nlinarith [mul_le_mul_of_nonneg_left hp (sq_nonneg (Real.exp (-alpha*s)))]
  have hh0 := mul_nonneg (le_of_lt (Real.exp_pos (-alpha*s))) hi
  exact ⟨add_nonneg hh0 hc0, stokes_cone_add _ _ _ _ hh0 hc0 hh hc⟩

theorem scalar_transfer_stokes_cone (j p : Fin 3 → ℝ) (intensity emission alpha s : ℝ)
    (ha : 0 ≤ alpha) (hs : 0 ≤ s) (hi : 0 ≤ intensity) (he : 0 ≤ emission)
    (hp : dotProduct p p ≤ intensity^2) (hj : dotProduct j j ≤ emission^2) :
    let e := Real.exp (-alpha*s)
    let a := absorption alpha s
    0 ≤ e*intensity+a*emission ∧
      dotProduct (e • p+a • j) (e • p+a • j) ≤ (e*intensity+a*emission)^2 := by
  have he0 := le_of_lt (Real.exp_pos (-alpha*s))
  have ha0 := absorption_nonneg_of_nonneg alpha s ha hs
  have hp' : dotProduct (Real.exp (-alpha*s) • p) (Real.exp (-alpha*s) • p) ≤
      (Real.exp (-alpha*s)*intensity)^2 := by
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left hp (sq_nonneg (Real.exp (-alpha*s)))]
  have hj' : dotProduct (absorption alpha s • j) (absorption alpha s • j) ≤
      (absorption alpha s*emission)^2 := by
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left hj (sq_nonneg (absorption alpha s))]
  exact ⟨add_nonneg (mul_nonneg he0 hi) (mul_nonneg ha0 he),
    stokes_cone_add _ _ _ _ (mul_nonneg he0 hi) (mul_nonneg ha0 he) hp' hj'⟩

def physicalStokes (state : ℝ × (Fin 3 → ℝ)) : Prop :=
  0 ≤ state.1 ∧ dotProduct state.2 state.2 ≤ state.1^2

theorem finite_cells_preserve_stokes_cone
    (cells : List ((ℝ × (Fin 3 → ℝ)) → (ℝ × (Fin 3 → ℝ))))
    (hcells : ∀ cell ∈ cells, ∀ state, physicalStokes state → physicalStokes (cell state))
    (initial : ℝ × (Fin 3 → ℝ)) (hi : physicalStokes initial) :
    physicalStokes (cells.foldl (fun state cell => cell state) initial) := by
  induction cells generalizing initial with
  | nil => exact hi
  | cons cell rest ih =>
    apply ih (fun f hf => hcells f (List.mem_cons_of_mem cell hf))
    exact hcells cell (List.mem_cons_self) initial hi

end BlackHole
