module

public import BlackHole.WgslPlasma

/-! Domains on which the `Safe` conditions of WGSL kernel bounds hold
(obligation F2).

`heatmap_color` has no division, root or branch, so its bound holds for every
input and error allowance (`heatmap_safe`). `tonemap` divides by
`x(2.43x+0.59)+0.14` with `x` clamped to `[0, 10⁴]`; that denominator is at
least `0.14`, and its running bound stays below it whenever the input error is
at most `1/10` (`tonemap_safe`). Kernels that branch on computed values
(`polarization_color`, `sample_plasma`, `spatial_unit`) cannot satisfy `Safe`
near their thresholds, where an arbitrarily small error can change the branch
and so the result. -/

@[expose] public section
noncomputable section

namespace BlackHole.WgslSafe
open Wgsl WgslExpr GExpr WgslPlasma

theorem heatmap_safe (i : Fin 3) (v E : ℕ → ℝ) : (heatmap i).Safe v E := by
  fin_cases i <;> simp [heatmap,clamp,Safe,c]

/-- `heatmap_color` is within its running bound for every input. -/
theorem heatmap_error_all (i : Fin 3) (v w E : ℕ → ℝ) (hw : ∀ k, |w k-v k| ≤ E k) (y : ℝ)
    (hy : (heatmap i).Computes w y) : |y-(heatmap i).exact v| ≤ (heatmap i).bound v E :=
  heatmap_error i v w E hw y (heatmap_safe i v E) hy

theorem tonemap_safe (v E : ℕ → ℝ) (hE0 : 0 ≤ E 0) (hE : E 0 ≤ 1/10) : tonemap.Safe v E := by
  simp only [tonemap,clamp,Safe,bound,exact,c,true_and,and_true,zero_mul,mul_zero,
    add_zero,max_eq_left hE0]
  push_cast
  have hX0 : 0 ≤ min (max (v 0) 0) 10000 := le_min (le_max_right _ _) (by norm_num)
  have hX1 : min (max (v 0) 0) 10000 ≤ 10000 := min_le_right _ _
  generalize min (max (v 0) 0) 10000 = X at hX0 hX1 ⊢
  generalize E 0 = e at hE0 hE ⊢
  have hU : WgslPoly.U = 5/2^24 := by unfold WgslPoly.U u; norm_num
  have hη : η = 1/2^126 := rfl
  rw [hU,hη]
  rw [abs_of_nonneg hX0,abs_of_nonneg (by positivity : (0:ℝ) ≤ 10192159/4194304*X),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ 10192159/4194304*X+9898557/16777216),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ X*(10192159/4194304*X+9898557/16777216)+9395241/67108864)]
  norm_num
  have hs : |10192159/4194304*X+9898557/16777216| = 10192159/4194304*X+9898557/16777216 :=
    abs_of_nonneg (by positivity)
  rw [abs_of_nonneg hX0,hs]
  have hXX := mul_nonneg hX0 hX0
  have hXe := mul_nonneg hX0 hE0
  have hee := mul_nonneg hE0 hE0
  have hXXe := mul_nonneg hXX hE0
  have hXee := mul_nonneg hXe hE0
  refine ⟨?_,?_,?_⟩ <;> nlinarith [mul_le_mul_of_nonneg_left hE hX0, mul_le_mul_of_nonneg_left hE hXX,
    mul_le_mul_of_nonneg_left hX1 hX0, mul_le_mul_of_nonneg_left hX1 hXX,
    mul_le_mul_of_nonneg_left hE hE0, mul_le_mul_of_nonneg_left hX1 hXe]

/-- `tonemap` is within its running bound for every input whose error is at
most `1/10`. -/
theorem tonemap_error_all (v w E : ℕ → ℝ) (hw : ∀ k, |w k-v k| ≤ E k) (hE : E 0 ≤ 1/10) (y : ℝ)
    (hy : tonemap.Computes w y) : |y-tonemap.exact v| ≤ tonemap.bound v E :=
  tonemap_error v w E hw y (tonemap_safe v E ((abs_nonneg _).trans (hw 0)) hE) hy

/-! ### Branch changes

Exact evaluation is itself an admissible WGSL computation (`computes_exact`),
so any bound that holds for every input within its error allowance is at
least half the variation of the exact kernel over that box
(`bound_ge_half_variation`). Near a branch threshold the variation includes
the jump between the branches: at `polarization_color`'s intensity threshold
no valid bound is smaller than half the hue it switches off
(`polarization_branch_change`). The `Safe` conditions exclude exactly such
neighbourhoods of thresholds, denominators and roots, and give the matching
bounds elsewhere. -/

/-- Programs without the hand-modeled `sincos` primitives or quadrant
selection, whose exact evaluation is admissible. -/
def Plain : GExpr → Prop
  | .input _ => True
  | .const _ => True
  | .add a b => Plain a ∧ Plain b
  | .sub a b => Plain a ∧ Plain b
  | .mul a b => Plain a ∧ Plain b
  | .div a b => Plain a ∧ Plain b
  | .max a b => Plain a ∧ Plain b
  | .min a b => Plain a ∧ Plain b
  | .neg a => Plain a
  | .sqrt a => Plain a
  | .abs a => Plain a
  | .invsqrt a => Plain a
  | .exp a => Plain a
  | .exp2 a => Plain a
  | .log a => Plain a
  | .log2 a => Plain a
  | .scale _ a => Plain a
  | .round a => Plain a
  | .inh f a => Plain f ∧ Plain a
  | .tanh _ a => Plain a
  | .lt c _ a b => Plain c ∧ Plain a ∧ Plain b
  | .lt2 a b x y => Plain a ∧ Plain b ∧ Plain x ∧ Plain y
  | .sinS _ => False
  | .cosS _ => False
  | .qsel _ _ _ _ => False

lemma rnd_self (x : ℝ) : Rnd x x := by
  unfold Rnd; have := η_pos; have := u_pos; simp; positivity

lemma ulp_nonneg (z : ℝ) : 0 ≤ ulp z := by unfold ulp; have := η_pos; have := u_pos; positivity

/-- Exact evaluation is an admissible WGSL computation. -/
theorem computes_exact (w : ℕ → ℝ) : ∀ e : GExpr, Plain e → e.Computes w (e.exact w)
  | .input _, _ => rfl
  | .const _, _ => rfl
  | .add a b, ⟨ha,hb⟩ => ⟨_,_,computes_exact w a ha,computes_exact w b hb,rnd_self _⟩
  | .sub a b, ⟨ha,hb⟩ => ⟨_,_,computes_exact w a ha,computes_exact w b hb,rnd_self _⟩
  | .mul a b, ⟨ha,hb⟩ => ⟨_,_,computes_exact w a ha,computes_exact w b hb,rnd_self _⟩
  | .div a b, ⟨ha,hb⟩ => ⟨_,_,computes_exact w a ha,computes_exact w b hb,fun _ => by
      unfold Wgsl.Div; have := η_pos; have := u_pos; simp only [exact,sub_self,abs_zero]; positivity⟩
  | .max a b, ⟨ha,hb⟩ => ⟨_,_,computes_exact w a ha,computes_exact w b hb,rfl⟩
  | .min a b, ⟨ha,hb⟩ => ⟨_,_,computes_exact w a ha,computes_exact w b hb,rfl⟩
  | .neg a, ha => ⟨_,computes_exact w a ha,rfl⟩
  | .sqrt a, ha => ⟨_,computes_exact w a ha,by
      have := η_pos; have := u_pos; simp only [exact,sub_self,abs_zero]; positivity⟩
  | .abs a, ha => ⟨_,computes_exact w a ha,rfl⟩
  | .invsqrt a, ha => ⟨_,computes_exact w a ha,by
      unfold InvSqrt; have := u_pos; simp only [exact,sub_self,abs_zero]; positivity⟩
  | .exp a, ha => ⟨_,computes_exact w a ha,by
      simp only [exact,sub_self,abs_zero]; have := ulp_nonneg (Real.exp (exact w a)); positivity⟩
  | .exp2 a, ha => ⟨_,computes_exact w a ha,by
      simp only [exact,sub_self,abs_zero]; have := ulp_nonneg (exp2R (exact w a)); positivity⟩
  | .log a, ha => ⟨_,computes_exact w a ha,by
      simp only [exact,sub_self,abs_zero]; have := ulp_nonneg (Real.log (exact w a)); positivity⟩
  | .log2 a, ha => ⟨_,computes_exact w a ha,by
      simp only [exact,sub_self,abs_zero]; have := ulp_nonneg (log2R (exact w a)); positivity⟩
  | .scale k a, ha => ⟨_,computes_exact w a ha,by
      have := η_pos; simp only [exact,sub_self,abs_zero]; positivity⟩
  | .round a, ha => ⟨_,computes_exact w a ha,⟨_,rfl⟩,by
      rw [abs_sub_comm]; exact abs_sub_round _⟩
  | .inh f a, ⟨hf,ha⟩ => ⟨_,computes_exact w a ha,computes_exact _ f hf⟩
  | .tanh f a, ha => ⟨_,computes_exact w a ha,Or.inl (by simp [exact])⟩
  | .lt c t a b, ⟨hc,ha,hb⟩ => by
    refine ⟨_,computes_exact w c hc,?_⟩
    by_cases h : exact w c < (t : ℝ)
    · exact Or.inl ⟨h,by simpa only [exact,h,↓reduceIte] using computes_exact w a ha⟩
    · exact Or.inr ⟨h,by simpa only [exact,h,↓reduceIte] using computes_exact w b hb⟩
  | .lt2 a b x y, ⟨ha,hb,hx,hy⟩ => by
    refine ⟨_,_,computes_exact w a ha,computes_exact w b hb,?_⟩
    by_cases h : exact w a < exact w b
    · exact Or.inl ⟨h,by simpa only [exact,h,↓reduceIte] using computes_exact w x hx⟩
    · exact Or.inr ⟨h,by simpa only [exact,h,↓reduceIte] using computes_exact w y hy⟩

/-- A bound valid for every input within its error allowance is at least half
the variation of the exact kernel between any two such inputs. -/
theorem bound_ge_half_variation (e : GExpr) (he : Plain e) (v E : ℕ → ℝ) (B : ℝ)
    (hB : ∀ w : ℕ → ℝ, (∀ i, |w i-v i| ≤ E i) → ∀ y, e.Computes w y → |y-e.exact v| ≤ B)
    (w₁ w₂ : ℕ → ℝ) (h₁ : ∀ i, |w₁ i-v i| ≤ E i) (h₂ : ∀ i, |w₂ i-v i| ≤ E i) :
    |e.exact w₁-e.exact w₂| ≤ 2*B := by
  have a := hB w₁ h₁ _ (computes_exact w₁ e he)
  have b := hB w₂ h₂ _ (computes_exact w₂ e he)
  have := abs_sub_le (e.exact w₁) (e.exact v) (e.exact w₂)
  rw [abs_sub_comm (e.exact v)] at this
  linarith

theorem polarization_plain (k : Fin 3) : Plain (polarizationHue k) := by
  fin_cases k <;> simp [Plain,polarizationHue,clamp,c]

/-- Near `polarization_color`'s intensity threshold `I = 10⁻⁸`, no bound valid
for every admissible input is smaller than half the hue at an intensity just
above the threshold: the hue view switches between that hue and zero. -/
theorem polarization_branch_change (k : Fin 3) (v E : ℕ → ℝ) (hE : ∀ i, 0 ≤ E i)
    (hnear : |v 0-(L1em8 : ℝ)| < E 0) (B : ℝ)
    (hB : ∀ w : ℕ → ℝ, (∀ i, |w i-v i| ≤ E i) → ∀ y, (polarizationHue k).Computes w y →
      |y-(polarizationHue k).exact v| ≤ B) :
    |(polarizationHue k).exact (Function.update v 0 (v 0+E 0))| ≤ 2*B := by
  have adm (d : ℝ) (hd : |d| ≤ E 0) : ∀ i, |Function.update v 0 (v 0+d) i-v i| ≤ E i := by
    intro i
    by_cases hi : i = 0
    · subst hi; simpa using hd
    · simp [Function.update_of_ne hi,hE i]
  have h0 := abs_lt.mp hnear
  have hE0 : 0 < E 0 := lt_of_le_of_lt (abs_nonneg _) hnear
  have hv := bound_ge_half_variation _ (polarization_plain k) v E B hB _ _
    (adm (E 0) (by rw [abs_of_pos hE0])) (adm (-E 0) (by rw [abs_neg,abs_of_pos hE0]))
  have hz : (polarizationHue k).exact (Function.update v 0 (v 0+-E 0)) = 0 := by
    have : ¬ -(v 0+-E 0) < -(L1em8 : ℝ) := by linarith
    simp only [polarizationHue,exact,Function.update_self]
    push_cast at this ⊢
    simp only [this,↓reduceIte]
    show ((0:ℚ):ℝ) = 0
    simp
  rwa [hz,sub_zero] at hv

end BlackHole.WgslSafe
