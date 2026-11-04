module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Full polarized constant-cell transfer (obligation T1), tied to
`assets/shaders/polarized_transfer.wesl`.

The cell equation is `dS/ds = j - K S` with the 4×4 Mueller generator `K`
built from absorption and Faraday coefficients. Augmenting with a constant
fifth component gives the homogeneous generator `A = [[-K, j], [0, 0]]`, so
`exp(sA) = [[e^{-sK}, source(s)], [0, 1]]`.

* `cell_solves`: the augmented exponential solves the transfer ODE exactly.
* `shaderLoop_closed`: the shader's 12-term loop computes the Taylor
  polynomial `Σ mⁱ/i!` (with `m = -hK`) and the source `Σ h mⁱ j/(i+1)!`.
* `taylor_tail`: the truncated series is within `‖x‖¹³·14/(13!·13)` of the
  exponential whenever `‖x‖ ≤ 1`.
* `squaring_error`: `squares` repeated squarings amplify an initial error `ε`
  at most to `(R+ε)^(2^k) - R^(2^k)`, and `exp_squaring` identifies the exact
  result with `exp(2^k h A)`, which is the cell over `ds = 2^k h`.

Norms are the L∞ operator (maximum absolute row sum) norm. Floating-point
evaluation of the loop is separate (F2). -/

@[expose] public section
noncomputable section

open NormedSpace Finset Matrix

namespace BlackHole.MatrixTransfer

/-! ### Banach-algebra lemmas -/

section Banach

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- The exponential series tail is dominated by the real exponential tail. -/
theorem taylor_tail_le (x : 𝔸) (N : ℕ) :
    ‖exp x-∑ n ∈ range N, ((n.factorial : ℝ)⁻¹) • x^n‖ ≤
      Real.exp ‖x‖-∑ n ∈ range N, ‖x‖^n/n.factorial := by
  set f : ℕ → 𝔸 := fun n => ((n.factorial : ℝ)⁻¹) • x^n with hf
  set g : ℕ → ℝ := fun n => ‖x‖^n/n.factorial with hg
  have hfs : HasSum f (exp x) := exp_series_hasSum_exp' (𝕂 := ℝ) x
  have hgs : HasSum g (Real.exp ‖x‖) := by
    rw [Real.exp_eq_exp_ℝ]
    exact expSeries_div_hasSum_exp ‖x‖
  have hfg : ∀ n, ‖f n‖ ≤ g n := by
    intro n
    simp only [hf, hg]
    rw [norm_smul, norm_inv, Real.norm_natCast, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (norm_pow_le x n) (by positivity)
  have hnorm : Summable fun n => ‖f n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hfg hgs.summable
  have hf_tail : exp x-∑ n ∈ range N, f n = ∑' n, f (n+N) := by
    rw [← hfs.tsum_eq, ← hfs.summable.sum_add_tsum_nat_add N]
    abel
  have hg_tail : Real.exp ‖x‖-∑ n ∈ range N, g n = ∑' n, g (n+N) := by
    rw [← hgs.tsum_eq, ← hgs.summable.sum_add_tsum_nat_add N]
    ring
  rw [hf_tail, hg_tail]
  calc ‖∑' n, f (n+N)‖ ≤ ∑' n, ‖f (n+N)‖ :=
        norm_tsum_le_tsum_norm ((summable_nat_add_iff N).mpr hnorm)
    _ ≤ ∑' n, g (n+N) :=
        Summable.tsum_le_tsum (fun n => hfg (n+N)) ((summable_nat_add_iff N).mpr hnorm)
          ((summable_nat_add_iff N).mpr hgs.summable)

/-- Truncation error of the shader's 13-term Taylor polynomial for `‖x‖ ≤ 1`. -/
theorem taylor_tail (x : 𝔸) (hx : ‖x‖ ≤ 1) :
    ‖exp x-∑ n ∈ range 13, ((n.factorial : ℝ)⁻¹) • x^n‖ ≤
      ‖x‖^13*(14/(Nat.factorial 13*13)) := by
  have h1 := taylor_tail_le x 13
  have h2 := Real.exp_bound (x := ‖x‖) (by rwa [abs_of_nonneg (norm_nonneg x)])
    (n := 13) (by norm_num)
  rw [abs_of_nonneg (norm_nonneg x)] at h2
  have h3 := le_abs_self (Real.exp ‖x‖-∑ m ∈ range 13, ‖x‖^m/m.factorial)
  push_cast at h2 ⊢
  linarith

omit [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] in
/-- Error amplification by repeated squaring. -/
theorem squaring_error (x y : 𝔸) (R ε : ℝ) (hR : ‖x‖ ≤ R) (hε : ‖y-x‖ ≤ ε) (k : ℕ) :
    ‖y^(2^k)-x^(2^k)‖ ≤ (R+ε)^(2^k)-R^(2^k) := by
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) hR
  have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) hε
  induction k with
  | zero => simpa using hε
  | succ k ih =>
    set X := x^(2^k)
    set Y := y^(2^k)
    have hX : ‖X‖ ≤ R^(2^k) := le_trans (norm_pow_le x _) (pow_le_pow_left₀ (norm_nonneg _) hR _)
    have hY : ‖Y‖ ≤ (R+ε)^(2^k) := by
      have := norm_sub_norm_le Y X
      linarith
    have hpow : ∀ z : 𝔸, z^(2^(k+1)) = z^(2^k)*z^(2^k) := by
      intro z; rw [pow_succ, pow_mul, sq]
    have hpowR : ∀ z : ℝ, z^(2^(k+1)) = z^(2^k)*z^(2^k) := by
      intro z; rw [pow_succ, pow_mul, sq]
    rw [hpow y, hpow x, hpowR (R+ε), hpowR R]
    have heq : Y*Y-X*X = Y*(Y-X)+(Y-X)*X := by noncomm_ring
    rw [heq]
    calc ‖Y*(Y-X)+(Y-X)*X‖ ≤ ‖Y‖*‖Y-X‖+‖Y-X‖*‖X‖ := by
          refine le_trans (norm_add_le _ _) (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ (R+ε)^(2^k)*((R+ε)^(2^k)-R^(2^k))+((R+ε)^(2^k)-R^(2^k))*R^(2^k) := by
          gcongr
          · have : R^(2^k) ≤ (R+ε)^(2^k) := pow_le_pow_left₀ hR0 (by linarith) _
            linarith
      _ = _ := by ring

end Banach

/-! ### The augmented cell -/

/-- Stokes vectors and 4×4 Mueller matrices. -/
abbrev Stokes := Fin 4 → ℝ
abbrev Mueller := Matrix (Fin 4) (Fin 4) ℝ
/-- Augmented index set: four Stokes components and one constant. -/
abbrev Aug := Matrix (Fin 4 ⊕ Unit) (Fin 4 ⊕ Unit) ℝ

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Homogeneous generator of `dS/ds = j - K S`. -/
def generator (K : Mueller) (j : Stokes) : Aug :=
  fromBlocks (-K) (replicateCol Unit j) 0 0

/-- Append the constant component. -/
def extend (S : Stokes) : Fin 4 ⊕ Unit → ℝ := Sum.elim S fun _ => 1

/-- The exact cell: Stokes part of `exp(sA)(S₀, 1)`. -/
def cell (K : Mueller) (j S₀ : Stokes) (s : ℝ) : Stokes :=
  fun i => (exp (s • generator K j) *ᵥ extend S₀) (Sum.inl i)

lemma generator_mulVec (K : Mueller) (j : Stokes) (v : Fin 4 ⊕ Unit → ℝ) :
    generator K j *ᵥ v = Sum.elim (-K *ᵥ (v ∘ Sum.inl)+v (Sum.inr ()) • j) 0 := by
  unfold generator
  rw [fromBlocks_mulVec]
  congr 1
  · funext i
    simp [replicateCol, mulVec, dotProduct, mul_comm]
  · funext i
    simp

/-- Evaluation of a vector component after multiplying by a matrix, as a
    continuous linear map on matrices. -/
def evalMul (v : Fin 4 ⊕ Unit → ℝ) (c : Fin 4 ⊕ Unit) : Aug →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (M *ᵥ v) c
      map_add' := fun M N => by simp [add_mulVec]
      map_smul' := fun r M => by simp [smul_mulVec] }

/-- The constant component stays one. -/
theorem cell_constant (K : Mueller) (j S₀ : Stokes) (s : ℝ) :
    (exp (s • generator K j) *ᵥ extend S₀) (Sum.inr ()) = 1 := by
  set A := generator K j
  have hd : ∀ t, HasDerivAt (fun u : ℝ => (exp (u • A) *ᵥ extend S₀) (Sum.inr ()))
      0 t := by
    intro t
    have h := HasFDerivAt.comp_hasDerivAt t (evalMul (extend S₀) (Sum.inr ())).hasFDerivAt
      (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t)
    have hfun : (fun u : ℝ => (exp (u • A) *ᵥ extend S₀) (Sum.inr ())) =
        (evalMul (extend S₀) (Sum.inr ())) ∘ fun u => exp (u • A) := by
      funext u; rfl
    rw [hfun]
    refine HasDerivAt.congr_deriv h ?_
    show ((A*exp (t • A)) *ᵥ extend S₀) (Sum.inr ()) = 0
    rw [← mulVec_mulVec, generator_mulVec]
    rfl
  have hc := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) s 0
  rw [hc]
  simp [exp_zero, extend]

/-- The exact cell solves the polarized transfer equation with initial value `S₀`. -/
theorem cell_solves (K : Mueller) (j S₀ : Stokes) (s : ℝ) :
    cell K j S₀ 0 = S₀ ∧ HasDerivAt (cell K j S₀) (j-K *ᵥ cell K j S₀ s) s := by
  set A := generator K j
  constructor
  · funext i; simp [cell, exp_zero, extend]
  rw [hasDerivAt_pi]
  intro i
  have h := HasFDerivAt.comp_hasDerivAt s (evalMul (extend S₀) (Sum.inl i)).hasFDerivAt
    (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A s)
  have hfun : (fun x => cell K j S₀ x i) =
      (evalMul (extend S₀) (Sum.inl i)) ∘ fun u => exp (u • A) := by
    funext u; rfl
  rw [hfun]
  refine HasDerivAt.congr_deriv h ?_
  symm
  show _ = ((A*exp (s • A)) *ᵥ extend S₀) (Sum.inl i)
  rw [← mulVec_mulVec, generator_mulVec, cell_constant]
  simp only [Sum.elim_inl, Pi.add_apply, Pi.sub_apply, one_smul, neg_mulVec]
  have : (exp (s • A) *ᵥ extend S₀) ∘ Sum.inl = cell K j S₀ s := rfl
  rw [this]
  simp only [Pi.neg_apply]
  ring

/-- Squaring the step-`h` cell gives the step-`2^k h` cell exactly. -/
theorem exp_squaring (K : Mueller) (j : Stokes) (h : ℝ) (k : ℕ) :
    exp ((2^k*h) • generator K j) = exp (h • generator K j)^(2^k) := by
  rw [← Matrix.exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  push_cast
  rfl

/-! ### The shader loop -/

/-- State of the shader loop after `i` iterations: exponential, current term,
    source. `m = -hK`. -/
def shaderLoop (m : Mueller) (h : ℝ) (j : Stokes) : ℕ → Mueller × Mueller × Stokes
  | 0 => (1, 1, h • j)
  | i+1 =>
    let (e, term, src) := shaderLoop m h j i
    let term' := (1/((i+1 : ℕ) : ℝ)) • (m*term)
    (e+term', term', src+(h/((i+2 : ℕ) : ℝ)) • (term' *ᵥ j))

/-- Closed form of the shader loop. -/
theorem shaderLoop_closed (m : Mueller) (h : ℝ) (j : Stokes) (i : ℕ) :
    shaderLoop m h j i =
      (∑ n ∈ range (i+1), ((n.factorial : ℝ)⁻¹) • m^n,
       ((i.factorial : ℝ)⁻¹) • m^i,
       ∑ n ∈ range (i+1), (h*((n+1).factorial : ℝ)⁻¹) • (m^n *ᵥ j)) := by
  induction i with
  | zero => simp [shaderLoop]
  | succ i ih =>
    simp only [shaderLoop, ih]
    have hterm : (1/((i+1 : ℕ) : ℝ)) • (m*(((i.factorial : ℝ)⁻¹) • m^i)) =
        (((i+1).factorial : ℝ)⁻¹) • m^(i+1) := by
      rw [mul_smul_comm, smul_smul, pow_succ', Nat.factorial_succ]
      congr 1
      push_cast
      field_simp
    rw [hterm]
    refine Prod.ext ?_ (Prod.ext rfl ?_)
    · simp [sum_range_succ _ (i+1)]
    · simp only [sum_range_succ _ (i+1)]
      congr 1
      rw [smul_mulVec, smul_smul]
      congr 1
      rw [Nat.factorial_succ (i+1)]
      push_cast
      field_simp
      ring

/-- Powers of the scaled generator. -/
theorem generator_pow (K : Mueller) (j : Stokes) (h : ℝ) (n : ℕ) :
    (h • generator K j)^(n+1) =
      fromBlocks ((-h • K)^(n+1)) (replicateCol Unit (h • ((-h • K)^n *ᵥ j))) 0 0 := by
  induction n with
  | zero =>
    simp only [zero_add, pow_one, pow_zero, one_mulVec, generator, fromBlocks_smul,
      smul_zero, neg_smul, smul_neg]
    congr 1
  | succ n ih =>
    rw [pow_succ, ih, generator, fromBlocks_smul, fromBlocks_multiply]
    congr 1 <;> simp [pow_succ, ← replicateCol_mulVec, Matrix.mul_smul, Matrix.mul_assoc]

/-! ### Shader matrix as a truncated exponential -/

/-- The 5×5 matrix the shader's loop represents: its exponential block and
    source column, with constant row `(0, 1)`. -/
def shaderMatrix (K : Mueller) (j : Stokes) (h : ℝ) : Aug :=
  fromBlocks (∑ n ∈ range 13, ((n.factorial : ℝ)⁻¹) • (-h • K)^n)
    (replicateCol Unit (∑ n ∈ range 13, (h*((n+1).factorial : ℝ)⁻¹) • ((-h • K)^n *ᵥ j)))
    0 1

lemma fromBlocks_sum (f : ℕ → Mueller) (g : ℕ → Matrix (Fin 4) Unit ℝ) (N : ℕ) :
    ∑ n ∈ range N, fromBlocks (f n) (g n) (0 : Matrix Unit (Fin 4) ℝ) (0 : Matrix Unit Unit ℝ) =
      fromBlocks (∑ n ∈ range N, f n) (∑ n ∈ range N, g n) 0 0 := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ, ih, fromBlocks_add, sum_range_succ, sum_range_succ]; simp

lemma replicateCol_sum (v : ℕ → Stokes) (N : ℕ) :
    ∑ n ∈ range N, replicateCol Unit (v n) = replicateCol Unit (∑ n ∈ range N, v n) := by
  ext i c
  simp [replicateCol, Matrix.sum_apply]

/-- The shader matrix is the degree-13 Taylor polynomial of `exp(hA)` with
    the top-left degree-13 term removed: the source column carries one more
    term than the exponential block. -/
theorem shaderMatrix_eq (K : Mueller) (j : Stokes) (h : ℝ) :
    shaderMatrix K j h =
      ∑ n ∈ range 14, ((n.factorial : ℝ)⁻¹) • (h • generator K j)^n -
        fromBlocks (((Nat.factorial 13 : ℝ)⁻¹) • (-h • K)^13) 0 0 0 := by
  rw [eq_sub_iff_add_eq, sum_range_succ']
  simp only [generator_pow, pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    fromBlocks_smul, smul_zero]
  rw [fromBlocks_sum, ← fromBlocks_one, fromBlocks_add, shaderMatrix, fromBlocks_add]
  congr 1
  · rw [← sum_range_succ (fun n => ((n.factorial : ℝ)⁻¹) • (-h • K)^n) 13,
      sum_range_succ' (fun n => ((n.factorial : ℝ)⁻¹) • (-h • K)^n) 13]
    simp
  · simp only [add_zero, ← replicateCol_smul, replicateCol_sum]
    congr 1
    apply sum_congr rfl
    intro n _
    rw [smul_smul, mul_comm]
  · simp

/-- Norm of a top-left block embedded in the augmented space. -/
lemma norm_fromBlocks_topLeft (X : Mueller) :
    ‖(fromBlocks X 0 0 0 : Aug)‖ ≤ ‖X‖ := by
  rw [Matrix.linfty_opNorm_def, Matrix.linfty_opNorm_def]
  norm_cast
  apply Finset.sup_le
  rintro (i | i) _
  · simp only [Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂, Matrix.zero_apply,
      nnnorm_zero, Finset.sum_const_zero, add_zero]
    exact Finset.le_sup (f := fun i => ∑ k, ‖X i k‖₊) (Finset.mem_univ i)
  · simp

/-- One scaled Taylor step of the shader is within `10⁻¹⁹` of the exact
    augmented cell whenever `‖hA‖ ≤ 1/4` and the shader's own check `‖hK‖ ≤ 1/8`
    hold. (The source column is linear in `j`, so any emission can be scaled
    into the first hypothesis; the shader's `bound` bounds every row sum of `K`.) -/
theorem shader_step_error (K : Mueller) (j : Stokes) (h : ℝ)
    (hA : ‖h • generator K j‖ ≤ 1/4) (hK : ‖-h • K‖ ≤ 1/8) :
    ‖shaderMatrix K j h-exp (h • generator K j)‖ ≤ 1/10^19 := by
  rw [shaderMatrix_eq]
  set x := h • generator K j
  have htail := taylor_tail_le x 14
  have hreal := Real.exp_bound (x := ‖x‖) (by rw [abs_of_nonneg (norm_nonneg x)]; linarith)
    (n := 14) (by norm_num)
  rw [abs_of_nonneg (norm_nonneg x)] at hreal
  have habs := le_abs_self (Real.exp ‖x‖-∑ m ∈ range 14, ‖x‖^m/m.factorial)
  have hpow : ‖x‖^14 ≤ (1/4)^14 := pow_le_pow_left₀ (norm_nonneg _) hA 14
  have hdrop : ‖(fromBlocks (((Nat.factorial 13 : ℝ)⁻¹) • (-h • K)^13) 0 0 0 : Aug)‖ ≤
      (Nat.factorial 13 : ℝ)⁻¹*(1/8)^13 := by
    refine le_trans (norm_fromBlocks_topLeft _) ?_
    rw [norm_smul, norm_inv, Real.norm_natCast]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact le_trans (norm_pow_le _ _) (pow_le_pow_left₀ (norm_nonneg _) hK 13)
  have hsplit : ‖∑ n ∈ range 14, ((n.factorial : ℝ)⁻¹) • x^n -
      fromBlocks (((Nat.factorial 13 : ℝ)⁻¹) • (-h • K)^13) 0 0 0 - exp x‖ ≤
      ‖exp x-∑ n ∈ range 14, ((n.factorial : ℝ)⁻¹) • x^n‖ +
      ‖(fromBlocks (((Nat.factorial 13 : ℝ)⁻¹) • (-h • K)^13) 0 0 0 : Aug)‖ := by
    rw [show ∑ n ∈ range 14, ((n.factorial : ℝ)⁻¹) • x^n -
        fromBlocks (((Nat.factorial 13 : ℝ)⁻¹) • (-h • K)^13) 0 0 0 - exp x =
        -(exp x-∑ n ∈ range 14, ((n.factorial : ℝ)⁻¹) • x^n) -
        fromBlocks (((Nat.factorial 13 : ℝ)⁻¹) • (-h • K)^13) 0 0 0 by abel]
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_neg]
  refine le_trans hsplit ?_
  set C : ℝ := ((Nat.succ 14 : ℕ) : ℝ)/(((Nat.factorial 14 : ℕ) : ℝ)*((14 : ℕ) : ℝ)) with hC
  have hreal' := le_trans habs hreal
  have hmono : ‖x‖^14*C ≤ (1/4)^14*C :=
    mul_le_mul_of_nonneg_right hpow (by rw [hC]; positivity)
  have hc1 : (Nat.factorial 13 : ℝ)⁻¹*(1/8)^13 ≤ 1/10^21 := by norm_num [Nat.factorial]
  have hc2 : (1/4:ℝ)^14*C ≤ 5/10^20 := by rw [hC]; norm_num [Nat.factorial]
  have : (1:ℝ)/10^21+5/10^20 ≤ 1/10^19 := by norm_num
  calc ‖exp x-∑ n ∈ range 14, ((n.factorial : ℝ)⁻¹) • x^n‖ +
        ‖(fromBlocks (((Nat.factorial 13 : ℝ)⁻¹) • (-h • K)^13) 0 0 0 : Aug)‖
      ≤ (1/4)^14*C+(Nat.factorial 13 : ℝ)⁻¹*(1/8)^13 := by
        gcongr
        exact le_trans htail (le_trans hreal' hmono)
    _ ≤ 5/10^20+1/10^21 := add_le_add hc2 hc1
    _ ≤ 1/10^19 := by norm_num

end BlackHole.MatrixTransfer
