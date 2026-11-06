module
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! Normalized time derivatives used by the interval Taylor evaluator. -/

@[expose] public section
noncomputable section
open Set Finset
open scoped Topology
namespace BlackHole.NormalizedJet

def coefficient (f : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  iteratedDeriv n f t/(n.factorial:ℝ)

@[simp] theorem coefficient_zero (f : ℝ → ℝ) (t : ℝ) : coefficient f 0 t = f t := by
  simp [coefficient]

/-- A first time jet along a coordinate direction is a Jacobian action. -/
theorem coefficient_direction_first {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x v : E) (hf : DifferentiableAt ℝ f x) :
    coefficient (fun t : ℝ => f (x+t • v)) 1 0 = fderiv ℝ f x v := by
  have hline : HasDerivAt (fun t : ℝ => x+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  have hd := hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  simpa [coefficient,Function.comp_def] using hd.deriv

theorem affine_coefficient (base direction : ℝ) (k : ℕ) :
    coefficient (fun t : ℝ => base+t*direction) k 0 =
      if k=0 then base else if k=1 then direction else 0 := by
  by_cases hk0 : k=0
  · subst k; simp
  · unfold coefficient
    rw [iteratedDeriv_const_add (Nat.pos_of_ne_zero hk0),iteratedDeriv_mul_const_field]
    by_cases hk1 : k=1
    · subst k; simp
    · simp [iteratedDeriv_fun_id,hk0,hk1]

theorem coefficient_add {f g : ℝ → ℝ} {n : ℕ} {t : ℝ}
    (hf : ContDiffAt ℝ n f t) (hg : ContDiffAt ℝ n g t) :
    coefficient (f+g) n t = coefficient f n t+coefficient g n t := by
  simp [coefficient,iteratedDeriv_add hf hg,add_div]

theorem coefficient_neg (f : ℝ → ℝ) (n : ℕ) (t : ℝ) :
    coefficient (-f) n t = -coefficient f n t := by simp [coefficient,neg_div]

private theorem choose_factor (n i : ℕ) (hi : i ≤ n) (a b : ℝ) :
    (n.choose i:ℝ)*a*b/(n.factorial:ℝ) = a/(i.factorial:ℝ)*(b/((n-i).factorial:ℝ)) := by
  have hn : (n.factorial:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hi0 : (i.factorial:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  have hni : ((n-i).factorial:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n-i))
  have hfact : (n.choose i:ℝ)*(i.factorial:ℝ)*((n-i).factorial:ℝ) = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  apply (div_eq_iff hn).mpr
  rw [← hfact]
  field_simp

theorem coefficient_mul {f g : ℝ → ℝ} {n : ℕ} {t : ℝ}
    (hf : ContDiffAt ℝ n f t) (hg : ContDiffAt ℝ n g t) :
    coefficient (f*g) n t = ∑ i ∈ range (n+1), coefficient f i t*coefficient g (n-i) t := by
  unfold coefficient
  rw [iteratedDeriv_mul hf hg]
  simp only [div_eq_mul_inv,Finset.sum_mul]
  apply sum_congr rfl
  intro i hi
  simpa only [div_eq_mul_inv] using choose_factor n i (Nat.le_of_lt_succ (mem_range.mp hi))
    (iteratedDeriv i f t) (iteratedDeriv (n-i) g t)

theorem coefficient_congr {f g : ℝ → ℝ} {n : ℕ} {t : ℝ} (h : f =ᶠ[𝓝 t] g) :
    coefficient f n t = coefficient g n t := by
  unfold coefficient
  rw [h.iteratedDeriv_eq n]

/-- Recursive division coefficients; only the constant denominator is inverted. -/
theorem quotient_recurrence {a b c : ℝ → ℝ} {n : ℕ} {t : ℝ}
    (hb : ContDiffAt ℝ n b t) (hc : ContDiffAt ℝ n c t)
    (heq : b*c =ᶠ[𝓝 t] a) (hb0 : b t ≠ 0) :
    coefficient c n t = (coefficient a n t-
      ∑ i ∈ range n, coefficient b (i+1) t*coefficient c (n-(i+1)) t)/b t := by
  have h := (coefficient_congr (n := n) heq).symm.trans (coefficient_mul hb hc)
  rw [sum_range_succ'] at h
  simp only [coefficient_zero,Nat.sub_zero] at h
  apply (eq_div_iff hb0).mpr
  nlinarith [h]

theorem coefficient_div {f g : ℝ → ℝ} {n : ℕ} {t : ℝ}
    (hf : ContDiffAt ℝ n f t) (hg : ContDiffAt ℝ n g t) (hg0 : g t ≠ 0) :
    coefficient (fun u => f u/g u) n t = (coefficient f n t-
      ∑ i ∈ range n, coefficient g (i+1) t*coefficient (fun u => f u/g u) (n-(i+1)) t)/g t := by
  apply quotient_recurrence hg (hf.div hg hg0) _ hg0
  filter_upwards [hg.continuousAt.eventually (eventually_ne_nhds hg0)] with u hu
  change g u*(f u/g u) = f u
  field_simp

/-- Recursive square-root coefficients, with both endpoint terms isolated. -/
theorem square_root_recurrence {f r : ℝ → ℝ} {n : ℕ} {t : ℝ}
    (hr : ContDiffAt ℝ (n+1) r t) (heq : r*r =ᶠ[𝓝 t] f) (hr0 : r t ≠ 0) :
    coefficient r (n+1) t = (coefficient f (n+1) t-
      ∑ i ∈ range n, coefficient r (i+1) t*coefficient r (n-i) t)/(2*r t) := by
  have h := (coefficient_congr (n := n+1) heq).symm.trans (coefficient_mul hr hr)
  rw [sum_range_succ',sum_range_succ] at h
  simp only [coefficient_zero,Nat.sub_zero,Nat.add_sub_add_right,Nat.sub_self] at h
  apply (eq_div_iff (mul_ne_zero (by norm_num) hr0)).mpr
  nlinarith [h]

theorem coefficient_sqrt {f : ℝ → ℝ} {n : ℕ} {t : ℝ}
    (hf : ContDiffAt ℝ (n+1) f t) (hpos : 0 < f t) :
    coefficient (fun u => Real.sqrt (f u)) (n+1) t = (coefficient f (n+1) t-
      ∑ i ∈ range n, coefficient (fun u => Real.sqrt (f u)) (i+1) t*
        coefficient (fun u => Real.sqrt (f u)) (n-i) t)/(2*Real.sqrt (f t)) := by
  apply square_root_recurrence (hf.sqrt (ne_of_gt hpos)) _ (ne_of_gt (Real.sqrt_pos.mpr hpos))
  filter_upwards [hf.continuousAt.eventually (eventually_gt_nhds hpos)] with u hu
  simpa [Pi.mul_apply] using Real.mul_self_sqrt hu.le

/-- Exact normalized derivatives of the stored quartic proposal, at any
point or interval time used by the interval evaluator. -/
theorem quartic_coefficient (a : Fin 5 → ℝ) (k : Fin 5) (t : ℝ) :
    coefficient (fun u : ℝ => ∑ j : Fin 5, a j*u^(j:ℕ)) k t =
      ∑ j : Fin 5, ((j:ℕ).choose k:ℝ)*a j*t^((j:ℕ)-(k:ℕ)) := by
  unfold coefficient
  rw [iteratedDeriv_fun_sum (fun j _ => by fun_prop)]
  simp only [div_eq_mul_inv,Finset.sum_mul]
  apply sum_congr rfl
  intro j _
  rw [iteratedDeriv_const_mul_field,iteratedDeriv_pow]
  fin_cases k <;> fin_cases j <;> norm_num [Nat.descFactorial,Nat.factorial,Nat.choose] <;> ring

/-- A fourth normalized derivative bound gives the residual allowance used by
the quartic proposal controller, uniformly over the complete time interval. -/
theorem cubic_residual_bound (g : ℝ → ℝ) (a : Fin 4 → ℝ) (h B : ℝ)
    (hh : 0 < h) (hB : 0 ≤ B)
    (hg : ∀ t ∈ Icc 0 h, ContDiffAt ℝ 4 g t)
    (hfour : ∀ t ∈ Icc 0 h, |coefficient g 4 t| ≤ B)
    (t : ℝ) (ht : t ∈ Icc 0 h) :
    |(∑ k : Fin 4, a k*t^(k:ℕ))-g t| ≤
      (∑ k : Fin 4, |a k-coefficient g k 0| * h^(k:ℕ))+4*B*h^4 := by
  have huniq := uniqueDiffOn_Icc hh
  have hd (k : ℕ) (hk : k ≤ 4) (u : ℝ) (hu : u ∈ Icc 0 h) :
      iteratedDerivWithin k g (Icc 0 h) u = iteratedDeriv k g u :=
    iteratedDerivWithin_eq_iteratedDeriv huniq ((hg u hu).of_le (by exact_mod_cast hk)) hu
  have hb (u : ℝ) (hu : u ∈ Icc 0 h) :
      ‖iteratedDerivWithin (3+1) g (Icc 0 h) u‖ ≤ 24*B := by
    rw [hd 4 le_rfl u hu,Real.norm_eq_abs]
    have hn := hfour u hu
    norm_num [coefficient,Nat.factorial,abs_div] at hn
    linarith
  have hr := taylor_mean_remainder_bound (f := g) (n := 3) (a := 0) (b := h) (x := t)
    hh.le (fun u hu => (hg u hu).contDiffWithinAt) ht hb
  rw [taylor_within_apply] at hr
  have hs : (∑ k ∈ range (3+1), ((k.factorial:ℝ)⁻¹*(t-0)^k)*
      iteratedDerivWithin k g (Icc 0 h) 0) = ∑ k : Fin 4, coefficient g k 0*t^(k:ℕ) := by
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => coefficient g k 0*t^k)]
    apply sum_congr rfl
    intro k hk
    rw [hd k (by have := mem_range.mp hk; omega) 0 ⟨le_rfl,hh.le⟩]
    simp [coefficient,div_eq_mul_inv]
    ring
  simp only [smul_eq_mul] at hr
  rw [hs] at hr
  norm_num [Nat.factorial,Real.norm_eq_abs] at hr
  have heq : (∑ k : Fin 4, a k*t^(k:ℕ))-g t =
      (∑ k : Fin 4, (a k-coefficient g k 0)*t^(k:ℕ))-
        (g t-∑ k : Fin 4, coefficient g k 0*t^(k:ℕ)) := by
    simp only [sub_mul,sum_sub_distrib]
    ring
  rw [heq]
  calc
    _ ≤ |∑ k : Fin 4, (a k-coefficient g k 0)*t^(k:ℕ)|+
        |g t-∑ k : Fin 4, coefficient g k 0*t^(k:ℕ)| := abs_sub _ _
    _ ≤ (∑ k : Fin 4, |(a k-coefficient g k 0)*t^(k:ℕ)|)+4*B*t^4 :=
      add_le_add (abs_sum_le_sum_abs _ _) (by nlinarith [hr])
    _ ≤ (∑ k : Fin 4, |a k-coefficient g k 0| * h^(k:ℕ))+4*B*h^4 := by
      apply add_le_add
      · apply sum_le_sum
        intro k _
        rw [abs_mul,abs_of_nonneg (pow_nonneg ht.1 _)]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.1 ht.2 _) (abs_nonneg _)
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.1 ht.2 4) (by positivity)

end BlackHole.NormalizedJet
