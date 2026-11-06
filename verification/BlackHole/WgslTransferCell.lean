module

public import BlackHole.MatrixTransfer
public import BlackHole.WgslSum
public import BlackHole.WgslKerrRadius
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-! WGSL error bounds for `transfer_cell` (obligations F2, T1).

```
let m = -h*k;
var exponential = identity; var term = identity; var source = h*c.emission;
for (var i=1u; i<=12u; i++) {
    term = (1.0/f32(i))*(m*term);
    exponential += term;
    source += (h/f32(i+1u))*(term*c.emission);
}
for (var i=0u; i<squares; i++) {
    source = exponential*source+source;
    exponential = exponential*exponential;
}
result.stokes = exponential*initial+source;
```

The trace follows the source association. Every dot product (`m*term`,
`term*c.emission`, `exponential*exponential`) and every sum
`exponential*v+source` may be evaluated in any order (`dot_of_tree`,
`dot5_of_tree`, from `WgslSum`); `+` and scalar products are correctly
rounded and `1.0/f32(i)`, `h/f32(i+1)` are WGSL divisions (2.5 ULP).

* `taylor_error`: after the twelve-term loop, the computed exponential,
  term and source are within the explicit running bounds `exB`, `eB`, `σB`
  of the exact-real loop `MatrixTransfer.shaderLoop` with the computed `h`,
  in terms of any `ρ ≥ ‖-h·K‖` and the emission norm.
* `squaring_error`: each squaring adds the running bounds `eS`, `σS`, given
  any bounds `R k` on the norms of the exact-real powers; `squaring_exact`
  identifies those powers with `shaderMatrix^(2^k)`, which
  `MatrixTransfer.exp_squaring` and `shader_step_error` relate to the exact
  cell. `R k = R₀^(2^k)` is always valid (`sqExact_norm`); it is pessimistic
  when Faraday rotation dominates absorption, since the L∞ norm of a
  rotation exceeds one.
* `stokes_error`: the returned Stokes vector.
* `check_bound`: every cell that passes the shader's computed test
  `bound*h ≤ 0.125` has `‖-h·k‖ ≤ 1/8 + 10⁻⁶`. There `taylor_accepted` puts
  the computed exponential within `16u` of the exact Taylor polynomial and
  `16u + 10⁻²⁰` of `exp(-h·k)`, and `source_accepted` puts the computed
  source within `16u·h‖j‖ + 2⁻¹²¹(1+h)(1+‖j‖)` of the exact loop's.

Norms are the L∞ operator norm on matrices and the sup norm on vectors. The
data-dependent `while` loop that picks `squares` is not modeled: the bounds
hold for the computed `h` and any number of squarings. -/

@[expose] public section
noncomputable section

namespace BlackHole.WgslTransferCell
open Finset Matrix Wgsl MatrixTransfer

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-! ### Norms -/

lemma row_le (A : Mueller) (i : Fin 4) : ∑ j, |A i j| ≤ ‖A‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h := Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (mem_univ i)
  have h2 : ((∑ j, ‖A i j‖₊ : NNReal) : ℝ) ≤ ((univ.sup fun i => ∑ j, ‖A i j‖₊ : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr h
  simpa [NNReal.coe_sum, Real.norm_eq_abs] using h2

lemma norm_le_rows {A : Mueller} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, ∑ j, |A i j| ≤ c) : ‖A‖ ≤ c := by
  rw [Matrix.linfty_opNorm_def]
  have : (univ.sup fun i => ∑ j, ‖A i j‖₊) ≤ ⟨c, hc⟩ := Finset.sup_le fun i _ => by
    have : ((∑ j, ‖A i j‖₊ : NNReal) : ℝ) ≤ ((⟨c, hc⟩ : NNReal) : ℝ) := by
      simpa [NNReal.coe_sum, Real.norm_eq_abs] using h i
    exact NNReal.coe_le_coe.mp this
  exact NNReal.coe_le_coe.mpr this

lemma vec_le (v : Stokes) (i : Fin 4) : |v i| ≤ ‖v‖ := by
  simpa [Real.norm_eq_abs] using norm_le_pi_norm v i

lemma norm_le_vec {v : Stokes} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, |v i| ≤ c) : ‖v‖ ≤ c :=
  (pi_norm_le_iff_of_nonneg hc).mpr fun i => by simpa [Real.norm_eq_abs] using h i

lemma norm_one_le : ‖(1 : Mueller)‖ ≤ 1 :=
  norm_le_rows zero_le_one fun i => by
    simp [Matrix.one_apply, abs_ite, Finset.sum_ite_eq]

/-! ### The floating-point operations -/

/-- Growth factors of an `n`-term WGSL sum (`WgslSum.SumTree.error`). -/
def γ (n : ℕ) : ℝ := (1+u)^n-1
def ζ4 : ℝ := 7*(1+u)^4*η
def ζ5 : ℝ := 9*(1+u)^5*η

lemma γ_nonneg (n : ℕ) : 0 ≤ γ n := by
  unfold γ; have := u_pos; have : 1 ≤ (1+u)^n := one_le_pow₀ (by linarith); linarith

lemma ζ4_nonneg : 0 ≤ ζ4 := by unfold ζ4; have := u_pos; have := η_pos; positivity
lemma ζ5_nonneg : 0 ≤ ζ5 := by unfold ζ5; have := u_pos; have := η_pos; positivity

/-- A WGSL `dot` of two 4-vectors, in any order. -/
def DotB (a b : Fin 4 → ℝ) (y : ℝ) : Prop :=
  |y-∑ k, a k*b k| ≤ γ 4*∑ k, |a k| *|b k|+ζ4

/-- A WGSL `dot(a, b) + c`, the five terms in any order. -/
def Dot5B (a b : Fin 4 → ℝ) (c y : ℝ) : Prop :=
  |y-(∑ k, a k*b k+c)| ≤ γ 5*(∑ k, |a k| *|b k|+|c|)+ζ5

def MatMulB (A B C : Mueller) : Prop := ∀ i j, DotB (A i) (fun k => B k j) (C i j)
def MatVecB (A : Mueller) (v w : Stokes) : Prop := ∀ i, DotB (A i) v (w i)
def ScaleM (s : ℝ) (A C : Mueller) : Prop := ∀ i j, Rnd (s*A i j) (C i j)
def ScaleV (s : ℝ) (v w : Stokes) : Prop := ∀ i, Rnd (s*v i) (w i)
def AddM (A B C : Mueller) : Prop := ∀ i j, Rnd (A i j+B i j) (C i j)
def AddV (v w z : Stokes) : Prop := ∀ i, Rnd (v i+w i) (z i)

/-! #### Every summation order satisfies `DotB` and `Dot5B` -/

/-- The exact terms at the leaves of a summation tree. -/
def terms : SumTree → List ℝ
  | .leaf t => [t]
  | .node l r => terms l ++ terms r

lemma exact_terms : ∀ T : SumTree, T.exact = (terms T).sum
  | .leaf _ => by simp [terms, SumTree.exact]
  | .node l r => by simp [terms, SumTree.exact, exact_terms l, exact_terms r]

lemma absSum_terms : ∀ T : SumTree, T.absSum = ((terms T).map abs).sum
  | .leaf _ => by simp [terms, SumTree.absSum]
  | .node l r => by simp [terms, SumTree.absSum, absSum_terms l, absSum_terms r]

lemma leaves_terms : ∀ T : SumTree, T.leaves = (terms T).length
  | .leaf _ => by simp [terms, SumTree.leaves]
  | .node l r => by simp [terms, SumTree.leaves, leaves_terms l, leaves_terms r]

theorem dot_of_tree (a b : Fin 4 → ℝ) (T : SumTree)
    (hT : (terms T).Perm (List.ofFn fun k => a k*b k)) (y : ℝ) (hy : T.Computes u η y) :
    DotB a b y := by
  have h := SumTree.error u η u_pos.le η_pos.le T y hy
  rw [exact_terms, absSum_terms, leaves_terms, hT.sum_eq, (hT.map abs).sum_eq, hT.length_eq] at h
  simp only [List.sum_ofFn, List.map_ofFn, List.length_ofFn, Function.comp_def, abs_mul] at h
  unfold DotB γ ζ4
  convert h using 2; norm_num

theorem dot5_of_tree (a b : Fin 4 → ℝ) (c : ℝ) (T : SumTree)
    (hT : (terms T).Perm (List.ofFn (fun k => a k*b k) ++ [c])) (y : ℝ)
    (hy : T.Computes u η y) : Dot5B a b c y := by
  have h := SumTree.error u η u_pos.le η_pos.le T y hy
  rw [exact_terms, absSum_terms, leaves_terms, hT.sum_eq, (hT.map abs).sum_eq, hT.length_eq] at h
  simp only [List.sum_append, List.sum_ofFn, List.map_append, List.map_ofFn, List.length_append,
    List.length_ofFn, Function.comp_def, abs_mul, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, List.length_cons, List.length_nil] at h
  unfold Dot5B γ ζ5
  convert h using 2; norm_num

/-! #### Norm consequences -/

lemma matmul_err {A B C : Mueller} (h : MatMulB A B C) : ‖C-A*B‖ ≤ γ 4*‖A‖*‖B‖+4*ζ4 := by
  have hg := γ_nonneg 4
  refine norm_le_rows (by have := ζ4_nonneg; positivity) fun i => ?_
  calc ∑ j, |(C-A*B) i j| ≤ ∑ j, (γ 4*∑ k, |A i k| *|B k j|+ζ4) :=
        sum_le_sum fun j _ => by simpa [DotB, Matrix.mul_apply] using h i j
    _ = γ 4*∑ k, |A i k| *∑ j, |B k j|+4*ζ4 := by
        rw [sum_add_distrib, ← mul_sum, sum_comm]; simp [mul_sum]
    _ ≤ γ 4*∑ k, |A i k| *‖B‖+4*ζ4 := by
        gcongr with k; exact row_le B k
    _ ≤ γ 4*‖A‖*‖B‖+4*ζ4 := by
        rw [← sum_mul, mul_assoc]; gcongr; exact row_le A i

lemma matvec_err {A : Mueller} {v w : Stokes} (h : MatVecB A v w) :
    ‖w-A *ᵥ v‖ ≤ γ 4*‖A‖*‖v‖+ζ4 := by
  have hg := γ_nonneg 4
  refine norm_le_vec (by have := ζ4_nonneg; positivity) fun i => ?_
  calc |(w-A *ᵥ v) i| ≤ γ 4*∑ k, |A i k| *|v k|+ζ4 := by
        simpa [DotB, Dot5B, Matrix.mulVec, dotProduct] using h i
    _ ≤ γ 4*∑ k, |A i k| *‖v‖+ζ4 := by gcongr with k; exact vec_le v k
    _ ≤ γ 4*‖A‖*‖v‖+ζ4 := by rw [← sum_mul, mul_assoc]; gcongr; exact row_le A i

lemma dot5_err {A : Mueller} {v c w : Stokes} (h : ∀ i, Dot5B (A i) v (c i) (w i)) :
    ‖w-(A *ᵥ v+c)‖ ≤ γ 5*(‖A‖*‖v‖+‖c‖)+ζ5 := by
  have hg := γ_nonneg 5
  have := ζ5_nonneg; have := norm_nonneg A; have := norm_nonneg v; have := norm_nonneg c
  refine norm_le_vec (by positivity) fun i => ?_
  calc |(w-(A *ᵥ v+c)) i| ≤ γ 5*(∑ k, |A i k| *|v k|+|c i|)+ζ5 := by
        simpa [DotB, Dot5B, Matrix.mulVec, dotProduct] using h i
    _ ≤ γ 5*(∑ k, |A i k| *‖v‖+‖c‖)+ζ5 := by
        gcongr with k
        · exact vec_le v k
        · exact vec_le c i
    _ ≤ γ 5*(‖A‖*‖v‖+‖c‖)+ζ5 := by rw [← sum_mul]; gcongr; exact row_le A i

lemma scaleM_err {s : ℝ} {A C : Mueller} (h : ScaleM s A C) : ‖C-s • A‖ ≤ u*|s| *‖A‖+4*η := by
  have hu := u_pos; have hη := η_pos
  refine norm_le_rows (by positivity) fun i => ?_
  calc ∑ j, |(C-s • A) i j| ≤ ∑ j, (u*|s| *|A i j|+η) :=
        sum_le_sum fun j _ => by have := h i j; unfold Rnd at this; simpa [abs_mul, mul_assoc] using this
    _ = u*|s| *∑ j, |A i j|+4*η := by rw [sum_add_distrib, ← mul_sum]; simp
    _ ≤ u*|s| *‖A‖+4*η := by gcongr; exact row_le A i

lemma scaleV_err {s : ℝ} {v w : Stokes} (h : ScaleV s v w) : ‖w-s • v‖ ≤ u*|s| *‖v‖+η := by
  have hu := u_pos; have hη := η_pos
  refine norm_le_vec (by positivity) fun i => ?_
  have := h i; unfold Rnd at this
  calc |(w-s • v) i| ≤ u*|s| *|v i|+η := by simpa [abs_mul, mul_assoc] using this
    _ ≤ u*|s| *‖v‖+η := by gcongr; exact vec_le v i

lemma addM_err {A B C : Mueller} (h : AddM A B C) : ‖C-(A+B)‖ ≤ u*‖A+B‖+4*η := by
  have hu := u_pos; have hη := η_pos
  refine norm_le_rows (by positivity) fun i => ?_
  calc ∑ j, |(C-(A+B)) i j| ≤ ∑ j, (u*|(A+B) i j|+η) :=
        sum_le_sum fun j _ => by have := h i j; unfold Rnd at this; simpa using this
    _ = u*∑ j, |(A+B) i j|+4*η := by rw [sum_add_distrib, ← mul_sum]; simp
    _ ≤ u*‖A+B‖+4*η := by gcongr; exact row_le _ i

lemma addV_err {v w z : Stokes} (h : AddV v w z) : ‖z-(v+w)‖ ≤ u*‖v+w‖+η := by
  have hu := u_pos; have hη := η_pos
  refine norm_le_vec (by positivity) fun i => ?_
  have := h i; unfold Rnd at this
  calc |(z-(v+w)) i| ≤ u*|(v+w) i|+η := by simpa using this
    _ ≤ u*‖v+w‖+η := by gcongr; exact vec_le _ i

lemma div_err {n d y : ℝ} (hn : 0 ≤ n) (hd : 0 < d) (h : Wgsl.Div n d y) :
    |y-n/d| ≤ 5*u*(n/d)+η ∧ |y| ≤ (1+5*u)*(n/d)+η := by
  unfold Wgsl.Div at h
  rw [abs_of_nonneg (div_nonneg hn hd.le)] at h
  refine ⟨h, ?_⟩
  have := abs_sub_abs_le_abs_sub y (n/d)
  rw [abs_of_nonneg (div_nonneg hn hd.le)] at this
  linarith

/-! ### The twelve-term loop -/

/-- Iteration `i+1` of the loop, from `(X, T, S)` to `(X', T', S')`. -/
def TaylorStep (Mt : Mueller) (h : ℝ) (j : Stokes) (i : ℕ) (X T : Mueller) (S : Stokes)
    (X' T' : Mueller) (S' : Stokes) : Prop :=
  ∃ (P : Mueller) (c d : ℝ) (v w : Stokes), MatMulB Mt T P ∧ Wgsl.Div 1 ((i+1 : ℕ) : ℝ) c ∧
    ScaleM c P T' ∧ AddM X T' X' ∧ Wgsl.Div h ((i+2 : ℕ) : ℝ) d ∧ MatVecB T' j v ∧
    ScaleV d v w ∧ AddV S w S'

/-- A WGSL evaluation of the first `i` iterations, from the computed `m`
(`Mt`), `h` and emission `j`: exponential, term and source. -/
def TaylorTrace (Mt : Mueller) (h : ℝ) (j : Stokes) : ℕ → Mueller → Mueller → Stokes → Prop
  | 0, X, T, S => X = 1 ∧ T = 1 ∧ ScaleV h j S
  | i+1, X', T', S' => ∃ X T S, TaylorTrace Mt h j i X T S ∧ TaylorStep Mt h j i X T S X' T' S'

lemma shaderLoop_succ (m : Mueller) (h : ℝ) (j : Stokes) (i : ℕ) :
    shaderLoop m h j (i+1) =
      ((shaderLoop m h j i).1+(1/((i+1 : ℕ) : ℝ)) • (m*(shaderLoop m h j i).2.1),
        (1/((i+1 : ℕ) : ℝ)) • (m*(shaderLoop m h j i).2.1),
        (shaderLoop m h j i).2.2+
          (h/((i+2 : ℕ) : ℝ)) • (((1/((i+1 : ℕ) : ℝ)) • (m*(shaderLoop m h j i).2.1)) *ᵥ j)) := by
  rcases e : shaderLoop m h j i with ⟨E, T, S⟩
  simp [shaderLoop, e]

/-- The bound after one term update, from `‖T - T*‖ ≤ e`, `‖T*‖ ≤ t`. -/
def termF (ρ μ t e n : ℝ) : ℝ :=
  let p := γ 4*(ρ+μ)*(t+e)+4*ζ4+μ*(t+e)+ρ*e
  (u*((1+5*u)*(1/n)+η)+(5*u*(1/n)+η))*(ρ*t+p)+4*η+1/n*p

/-- The bound after one source update, with `t'`, `e'` the new term's. -/
def srcF (h J t' e' n s' σ : ℝ) : ℝ :=
  let q := (γ 4*(t'+e')+e')*J+ζ4
  let W := u*((1+5*u)*(h/n)+η)*(t'*J+q)+η+(5*u*(h/n)+η)*(t'*J+q)+h/n*q
  u*(s'+σ+W)+η+σ+W

/-- Bounds on the exact term `t`, exponential `x` and source `s`, and on the
computed term `e`, exponential `ex` and source `σ` errors. -/
def tB (ρ : ℝ) : ℕ → ℝ
  | 0 => 1
  | i+1 => 1/((i+1 : ℕ) : ℝ)*(ρ*tB ρ i)

def eB (ρ μ : ℝ) : ℕ → ℝ
  | 0 => 0
  | i+1 => termF ρ μ (tB ρ i) (eB ρ μ i) ((i+1 : ℕ) : ℝ)

def xB (ρ : ℝ) : ℕ → ℝ
  | 0 => 1
  | i+1 => xB ρ i+tB ρ (i+1)

def exB (ρ μ : ℝ) : ℕ → ℝ
  | 0 => 0
  | i+1 => u*(xB ρ (i+1)+(exB ρ μ i+eB ρ μ (i+1)))+4*η+(exB ρ μ i+eB ρ μ (i+1))

def sB (ρ h J : ℝ) : ℕ → ℝ
  | 0 => h*J
  | i+1 => sB ρ h J i+h/((i+2 : ℕ) : ℝ)*(tB ρ (i+1)*J)

def σB (ρ μ h J : ℝ) : ℕ → ℝ
  | 0 => u*h*J+η
  | i+1 => srcF h J (tB ρ (i+1)) (eB ρ μ (i+1)) ((i+2 : ℕ) : ℝ) (sB ρ h J (i+1)) (σB ρ μ h J i)

lemma tB_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) : ∀ i, 0 ≤ tB ρ i
  | 0 => zero_le_one
  | i+1 => by have := tB_nonneg hρ i; simp only [tB]; positivity

lemma termF_nonneg {ρ μ t e n : ℝ} (hρ : 0 ≤ ρ) (hμ : 0 ≤ μ) (ht : 0 ≤ t) (he : 0 ≤ e)
    (hn : 0 < n) : 0 ≤ termF ρ μ t e n := by
  have := γ_nonneg 4; have := ζ4_nonneg; have := u_pos; have := η_pos
  unfold termF; positivity

lemma eB_nonneg {ρ μ : ℝ} (hρ : 0 ≤ ρ) (hμ : 0 ≤ μ) : ∀ i, 0 ≤ eB ρ μ i
  | 0 => le_rfl
  | i+1 => termF_nonneg hρ hμ (tB_nonneg hρ i) (eB_nonneg hρ hμ i) (by positivity)

lemma term_step {m Mt T Ts P T' : Mueller} {ρ μ t e c n : ℝ} (hm : ‖m‖ ≤ ρ) (hμ : ‖Mt-m‖ ≤ μ)
    (hT : ‖T-Ts‖ ≤ e) (hTs : ‖Ts‖ ≤ t) (hn : 0 < n) (hP : MatMulB Mt T P)
    (hc : Wgsl.Div 1 n c) (hT' : ScaleM c P T') :
    ‖T'-(1/n) • (m*Ts)‖ ≤ termF ρ μ t e n := by
  have hu := u_pos; have hη := η_pos; have hg := γ_nonneg 4; have hζ := ζ4_nonneg
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans hm
  have hμ0 : 0 ≤ μ := (norm_nonneg _).trans hμ
  have he : 0 ≤ e := (norm_nonneg _).trans hT
  have ht : 0 ≤ t := (norm_nonneg _).trans hTs
  have nT : ‖T‖ ≤ t+e := by
    have := norm_le_insert' T Ts; linarith
  have nMt : ‖Mt‖ ≤ ρ+μ := by
    have := norm_le_insert' Mt m; linarith
  set p := γ 4*(ρ+μ)*(t+e)+4*ζ4+μ*(t+e)+ρ*e with hp
  have h1 := matmul_err hP
  have h2 : ‖Mt*T-m*Ts‖ ≤ μ*(t+e)+ρ*e := by
    rw [show Mt*T-m*Ts = (Mt-m)*T+m*(T-Ts) by noncomm_ring]
    refine (norm_add_le _ _).trans (add_le_add ((norm_mul_le _ _).trans ?_) ((norm_mul_le _ _).trans ?_))
    · exact mul_le_mul hμ nT (norm_nonneg _) hμ0
    · exact mul_le_mul hm hT (norm_nonneg _) hρ
  have hP' : ‖P-m*Ts‖ ≤ p := by
    have h3 : γ 4*‖Mt‖*‖T‖ ≤ γ 4*(ρ+μ)*(t+e) := by gcongr
    calc ‖P-m*Ts‖ = ‖(P-Mt*T)+(Mt*T-m*Ts)‖ := by rw [sub_add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ p := by rw [hp]; linarith
  have nP : ‖P‖ ≤ ρ*t+p := by
    have h4 : ‖m*Ts‖ ≤ ρ*t := (norm_mul_le _ _).trans (mul_le_mul hm hTs (norm_nonneg _) hρ)
    have := norm_le_insert' P (m*Ts); linarith
  obtain ⟨hc1, hc2⟩ := div_err zero_le_one hn hc
  have h5 := scaleM_err hT'
  have h6 : ‖c • P-(1/n) • (m*Ts)‖ ≤ |c-1/n| *‖P‖+1/n*p := by
    rw [show c • P-(1/n) • (m*Ts) = (c-1/n) • P+(1/n) • (P-m*Ts) by
      rw [sub_smul, smul_sub]; abel]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_left hP' (by positivity)
  have hcP : |c| *‖P‖ ≤ ((1+5*u)*(1/n)+η)*(ρ*t+p) :=
    mul_le_mul hc2 nP (norm_nonneg _) (by positivity)
  have hcP' : |c-1/n| *‖P‖ ≤ (5*u*(1/n)+η)*(ρ*t+p) :=
    mul_le_mul hc1 nP (norm_nonneg _) (by positivity)
  calc ‖T'-(1/n) • (m*Ts)‖ = ‖(T'-c • P)+(c • P-(1/n) • (m*Ts))‖ := by rw [sub_add_sub_cancel]
    _ ≤ _ := norm_add_le _ _
    _ ≤ (u*|c| *‖P‖+4*η)+(|c-1/n| *‖P‖+1/n*p) := add_le_add h5 h6
    _ ≤ termF ρ μ t e n := by
        unfold termF
        simp only [← hp]
        nlinarith [mul_le_mul_of_nonneg_left hcP hu.le]

lemma exp_step {X Xs T' Ts' X' : Mueller} {ex e' x' : ℝ} (hX : ‖X-Xs‖ ≤ ex) (hT : ‖T'-Ts'‖ ≤ e')
    (hx : ‖Xs+Ts'‖ ≤ x') (hX' : AddM X T' X') :
    ‖X'-(Xs+Ts')‖ ≤ u*(x'+(ex+e'))+4*η+(ex+e') := by
  have hu := u_pos
  have h1 := addM_err hX'
  have h2 : ‖X+T'-(Xs+Ts')‖ ≤ ex+e' := by
    rw [show X+T'-(Xs+Ts') = (X-Xs)+(T'-Ts') by abel]
    exact (norm_add_le _ _).trans (add_le_add hX hT)
  have h3 : ‖X+T'‖ ≤ x'+(ex+e') := by have := norm_le_insert' (X+T') (Xs+Ts'); linarith
  calc ‖X'-(Xs+Ts')‖ = ‖(X'-(X+T'))+(X+T'-(Xs+Ts'))‖ := by rw [sub_add_sub_cancel]
    _ ≤ _ := norm_add_le _ _
    _ ≤ (u*(x'+(ex+e'))+4*η)+(ex+e') := by
        gcongr
        exact h1.trans (by gcongr)

lemma src_step {T' Ts' : Mueller} {S Ss v w S' j : Stokes} {h J t' e' n s' σ d : ℝ}
    (hh : 0 ≤ h) (hJ : ‖j‖ ≤ J) (hT : ‖T'-Ts'‖ ≤ e') (hTs : ‖Ts'‖ ≤ t') (hS : ‖S-Ss‖ ≤ σ)
    (hs : ‖Ss+(h/n) • (Ts' *ᵥ j)‖ ≤ s') (hn : 0 < n) (hd : Wgsl.Div h n d)
    (hv : MatVecB T' j v) (hw : ScaleV d v w) (hS' : AddV S w S') :
    ‖S'-(Ss+(h/n) • (Ts' *ᵥ j))‖ ≤ srcF h J t' e' n s' σ := by
  have hu := u_pos; have hη := η_pos; have hg := γ_nonneg 4; have hζ := ζ4_nonneg
  have hJ0 : 0 ≤ J := (norm_nonneg _).trans hJ
  have he : 0 ≤ e' := (norm_nonneg _).trans hT
  have ht : 0 ≤ t' := (norm_nonneg _).trans hTs
  have hσ : 0 ≤ σ := (norm_nonneg _).trans hS
  have hhn : 0 ≤ h/n := div_nonneg hh hn.le
  set q := (γ 4*(t'+e')+e')*J+ζ4 with hq
  have nT : ‖T'‖ ≤ t'+e' := by have := norm_le_insert' T' Ts'; linarith
  have h1 := matvec_err hv
  have h2 : ‖T' *ᵥ j-Ts' *ᵥ j‖ ≤ e'*J := by
    rw [← sub_mulVec]
    exact (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul hT hJ (norm_nonneg _) he)
  have hvq : ‖v-Ts' *ᵥ j‖ ≤ q := by
    have h3 : γ 4*‖T'‖*‖j‖ ≤ γ 4*(t'+e')*J := by gcongr
    calc ‖v-Ts' *ᵥ j‖ = ‖(v-T' *ᵥ j)+(T' *ᵥ j-Ts' *ᵥ j)‖ := by rw [sub_add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ q := by rw [hq]; nlinarith
  have nv : ‖v‖ ≤ t'*J+q := by
    have h4 : ‖Ts' *ᵥ j‖ ≤ t'*J :=
      (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul hTs hJ (norm_nonneg _) ht)
    have := norm_le_insert' v (Ts' *ᵥ j); linarith
  obtain ⟨hd1, hd2⟩ := div_err hh hn hd
  have h5 := scaleV_err hw
  have h6 : ‖d • v-(h/n) • (Ts' *ᵥ j)‖ ≤ |d-h/n| *‖v‖+h/n*q := by
    rw [show d • v-(h/n) • (Ts' *ᵥ j) = (d-h/n) • v+(h/n) • (v-Ts' *ᵥ j) by
      rw [sub_smul, smul_sub]; abel]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hhn]
      exact mul_le_mul_of_nonneg_left hvq hhn
  set W := u*((1+5*u)*(h/n)+η)*(t'*J+q)+η+(5*u*(h/n)+η)*(t'*J+q)+h/n*q with hW
  have hwW : ‖w-(h/n) • (Ts' *ᵥ j)‖ ≤ W := by
    have hdv : |d| *‖v‖ ≤ ((1+5*u)*(h/n)+η)*(t'*J+q) :=
      mul_le_mul hd2 nv (norm_nonneg _) (by positivity)
    have hdv' : |d-h/n| *‖v‖ ≤ (5*u*(h/n)+η)*(t'*J+q) :=
      mul_le_mul hd1 nv (norm_nonneg _) (by positivity)
    calc ‖w-(h/n) • (Ts' *ᵥ j)‖ = ‖(w-d • v)+(d • v-(h/n) • (Ts' *ᵥ j))‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ (u*|d| *‖v‖+η)+(|d-h/n| *‖v‖+h/n*q) := add_le_add h5 h6
      _ ≤ W := by rw [hW]; nlinarith [mul_le_mul_of_nonneg_left hdv hu.le]
  have h7 := addV_err hS'
  have h8 : ‖S+w-(Ss+(h/n) • (Ts' *ᵥ j))‖ ≤ σ+W := by
    rw [show S+w-(Ss+(h/n) • (Ts' *ᵥ j)) = (S-Ss)+(w-(h/n) • (Ts' *ᵥ j)) by abel]
    exact (norm_add_le _ _).trans (add_le_add hS hwW)
  have h9 : ‖S+w‖ ≤ s'+(σ+W) := by
    have := norm_le_insert' (S+w) (Ss+(h/n) • (Ts' *ᵥ j)); linarith
  calc ‖S'-(Ss+(h/n) • (Ts' *ᵥ j))‖ = ‖(S'-(S+w))+(S+w-(Ss+(h/n) • (Ts' *ᵥ j)))‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ _ := norm_add_le _ _
    _ ≤ (u*(s'+(σ+W))+η)+(σ+W) := add_le_add (h7.trans (by gcongr)) h8
    _ = srcF h J t' e' n s' σ := by unfold srcF; simp only [← hq, ← hW]; ring

/-- The twelve-term loop: the computed exponential, term and source are
within the running bounds of the exact-real loop with the same `h`, for any
`ρ ≥ ‖m‖`, `μ ≥ ‖Mt - m‖` and `J ≥ ‖j‖`. -/
theorem taylor_error {m Mt : Mueller} {h ρ μ J : ℝ} {j : Stokes} (hh : 0 ≤ h) (hm : ‖m‖ ≤ ρ)
    (hμ : ‖Mt-m‖ ≤ μ) (hJ : ‖j‖ ≤ J) :
    ∀ i X T S, TaylorTrace Mt h j i X T S →
      ‖T-(shaderLoop m h j i).2.1‖ ≤ eB ρ μ i ∧ ‖(shaderLoop m h j i).2.1‖ ≤ tB ρ i ∧
      ‖X-(shaderLoop m h j i).1‖ ≤ exB ρ μ i ∧ ‖(shaderLoop m h j i).1‖ ≤ xB ρ i ∧
      ‖S-(shaderLoop m h j i).2.2‖ ≤ σB ρ μ h J i ∧ ‖(shaderLoop m h j i).2.2‖ ≤ sB ρ h J i
  | 0, X, T, S, ⟨hX, hT, hS⟩ => by
    subst hX hT
    have hJ0 : 0 ≤ J := (norm_nonneg _).trans hJ
    have hs := scaleV_err hS
    simp only [shaderLoop, sub_self, norm_zero, le_refl, true_and, eB, tB, exB, xB, σB, sB]
    refine ⟨norm_one_le, norm_one_le, ?_, ?_⟩
    · refine hs.trans ?_
      rw [abs_of_nonneg hh]
      have := mul_le_mul_of_nonneg_left hJ (mul_nonneg u_pos.le hh); linarith
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]; gcongr
  | i+1, X', T', S', ⟨X, T, S, htr, P, c, d, v, w, hP, hc, hT', hX', hd, hv, hw, hS'⟩ => by
    obtain ⟨eT, nT, eX, nX, eS, nS⟩ := taylor_error hh hm hμ hJ i X T S htr
    have hρ : 0 ≤ ρ := (norm_nonneg _).trans hm
    rw [shaderLoop_succ]
    set Ts := (shaderLoop m h j i).2.1
    have hn1 : (0:ℝ) < ((i+1 : ℕ) : ℝ) := by positivity
    have hn2 : (0:ℝ) < ((i+2 : ℕ) : ℝ) := by positivity
    have eT' := term_step hm hμ eT nT hn1 hP hc hT'
    have nT' : ‖(1/((i+1 : ℕ) : ℝ)) • (m*Ts)‖ ≤ tB ρ (i+1) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), tB]
      exact mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans
        (mul_le_mul hm nT (norm_nonneg _) hρ)) (by positivity)
    refine ⟨eT', nT', ?_, (norm_add_le _ _).trans (add_le_add nX nT'), ?_, ?_⟩
    · exact exp_step eX eT' ((norm_add_le _ _).trans (add_le_add nX nT')) hX'
    · have hJ0 : 0 ≤ J := (norm_nonneg _).trans hJ
      have hsn : ‖(shaderLoop m h j i).2.2+(h/((i+2 : ℕ) : ℝ)) •
          (((1/((i+1 : ℕ) : ℝ)) • (m*Ts)) *ᵥ j)‖ ≤ sB ρ h J (i+1) := by
        refine (norm_add_le _ _).trans (add_le_add nS ?_)
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hh hn2.le)]
        exact mul_le_mul_of_nonneg_left ((Matrix.linfty_opNorm_mulVec _ _).trans
          (mul_le_mul nT' hJ (norm_nonneg _) (tB_nonneg hρ _))) (div_nonneg hh hn2.le)
      exact src_step hh hJ eT' nT' eS hsn hn2 hd hv hw hS'
    · refine (norm_add_le _ _).trans (add_le_add nS ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hh hn2.le)]
      exact mul_le_mul_of_nonneg_left ((Matrix.linfty_opNorm_mulVec _ _).trans
        (mul_le_mul nT' hJ (norm_nonneg _) (tB_nonneg hρ _))) (div_nonneg hh hn2.le)

/-! ### The squarings -/

/-- `k` WGSL squarings from `(E, S)`. -/
def SqTrace (E : Mueller) (S : Stokes) : ℕ → Mueller → Stokes → Prop
  | 0, E', S' => E' = E ∧ S' = S
  | k+1, E', S' => ∃ E1 S1, SqTrace E S k E1 S1 ∧ (∀ i, Dot5B (E1 i) S1 (S1 i) (S' i)) ∧
      MatMulB E1 E1 E'

/-- The same squarings in exact arithmetic. -/
def sqExact (E : Mueller) (S : Stokes) : ℕ → Mueller × Stokes
  | 0 => (E, S)
  | k+1 => ((sqExact E S k).1*(sqExact E S k).1,
      (sqExact E S k).1 *ᵥ (sqExact E S k).2+(sqExact E S k).2)

/-- Running bounds through the squarings, from bounds `R k` and `Sg k` on the
exact exponential and source after `k` squarings. -/
def eS (R : ℕ → ℝ) (e0 : ℝ) : ℕ → ℝ
  | 0 => e0
  | k+1 => γ 4*(R k+eS R e0 k)^2+4*ζ4+(2*R k+eS R e0 k)*eS R e0 k

def σS (R Sg : ℕ → ℝ) (e0 σ0 : ℝ) : ℕ → ℝ
  | 0 => σ0
  | k+1 => γ 5*((R k+eS R e0 k)*(Sg k+σS R Sg e0 σ0 k)+(Sg k+σS R Sg e0 σ0 k))+ζ5+
      ((R k+eS R e0 k)*σS R Sg e0 σ0 k+eS R e0 k*Sg k)+σS R Sg e0 σ0 k

theorem squaring_error {E Es : Mueller} {S Ss : Stokes} {e0 σ0 : ℝ} (R Sg : ℕ → ℝ)
    (hE : ‖E-Es‖ ≤ e0) (hS : ‖S-Ss‖ ≤ σ0) (hR : ∀ k, ‖(sqExact Es Ss k).1‖ ≤ R k)
    (hSg : ∀ k, ‖(sqExact Es Ss k).2‖ ≤ Sg k) :
    ∀ k E' S', SqTrace E S k E' S' →
      ‖E'-(sqExact Es Ss k).1‖ ≤ eS R e0 k ∧ ‖S'-(sqExact Es Ss k).2‖ ≤ σS R Sg e0 σ0 k
  | 0, E', S', ⟨h1, h2⟩ => by subst h1 h2; exact ⟨hE, hS⟩
  | k+1, E', S', ⟨E1, S1, htr, hS', hE'⟩ => by
    obtain ⟨ek, σk⟩ := squaring_error R Sg hE hS hR hSg k E1 S1 htr
    set Ek := (sqExact Es Ss k).1
    set Sk := (sqExact Es Ss k).2
    have nE := hR k
    have nS := hSg k
    have hg4 := γ_nonneg 4; have hg5 := γ_nonneg 5
    have he : 0 ≤ eS R e0 k := (norm_nonneg _).trans ek
    have hσ : 0 ≤ σS R Sg e0 σ0 k := (norm_nonneg _).trans σk
    have hRk : 0 ≤ R k := (norm_nonneg _).trans nE
    have hSk : 0 ≤ Sg k := (norm_nonneg _).trans nS
    have nE1 : ‖E1‖ ≤ R k+eS R e0 k := by have := norm_le_insert' E1 Ek; linarith
    have nS1 : ‖S1‖ ≤ Sg k+σS R Sg e0 σ0 k := by have := norm_le_insert' S1 Sk; linarith
    simp only [sqExact]
    constructor
    · have h1 := matmul_err hE'
      have h2 : ‖E1*E1-Ek*Ek‖ ≤ (R k+eS R e0 k)*eS R e0 k+eS R e0 k*R k := by
        rw [show E1*E1-Ek*Ek = E1*(E1-Ek)+(E1-Ek)*Ek by noncomm_ring]
        refine (norm_add_le _ _).trans (add_le_add ((norm_mul_le _ _).trans ?_)
          ((norm_mul_le _ _).trans ?_))
        · exact mul_le_mul nE1 ek (norm_nonneg _) (by linarith)
        · exact mul_le_mul ek nE (norm_nonneg _) he
      have h3 : γ 4*‖E1‖*‖E1‖ ≤ γ 4*(R k+eS R e0 k)^2 := by
        rw [mul_assoc, sq]; gcongr
      calc ‖E'-Ek*Ek‖ = ‖(E'-E1*E1)+(E1*E1-Ek*Ek)‖ := by rw [sub_add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
        _ ≤ eS R e0 (k+1) := by simp only [eS]; nlinarith
    · have h1 := dot5_err hS'
      have h2 : ‖E1 *ᵥ S1+S1-(Ek *ᵥ Sk+Sk)‖ ≤
          (R k+eS R e0 k)*σS R Sg e0 σ0 k+eS R e0 k*Sg k+σS R Sg e0 σ0 k := by
        rw [show E1 *ᵥ S1+S1-(Ek *ᵥ Sk+Sk) = (E1 *ᵥ (S1-Sk)+(E1-Ek) *ᵥ Sk)+(S1-Sk) by
          rw [mulVec_sub, sub_mulVec]; abel]
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
          ((Matrix.linfty_opNorm_mulVec _ _).trans ?_) ((Matrix.linfty_opNorm_mulVec _ _).trans ?_))) σk)
        · exact mul_le_mul nE1 σk (norm_nonneg _) (by linarith)
        · exact mul_le_mul ek nS (norm_nonneg _) he
      have h3 : γ 5*(‖E1‖*‖S1‖+‖S1‖) ≤
          γ 5*((R k+eS R e0 k)*(Sg k+σS R Sg e0 σ0 k)+(Sg k+σS R Sg e0 σ0 k)) := by
        gcongr
      calc ‖S'-(Ek *ᵥ Sk+Sk)‖ = ‖(S'-(E1 *ᵥ S1+S1))+(E1 *ᵥ S1+S1-(Ek *ᵥ Sk+Sk))‖ := by
            rw [sub_add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
        _ ≤ σS R Sg e0 σ0 (k+1) := by simp only [σS]; linarith

/-- The returned Stokes vector `exponential*initial+source`. -/
theorem stokes_error {E Es : Mueller} {S Ss I0 out : Stokes} {e R σ Sg : ℝ}
    (hE : ‖E-Es‖ ≤ e) (hEs : ‖Es‖ ≤ R) (hS : ‖S-Ss‖ ≤ σ) (hSs : ‖Ss‖ ≤ Sg)
    (hout : ∀ i, Dot5B (E i) I0 (S i) (out i)) :
    ‖out-(Es *ᵥ I0+Ss)‖ ≤ γ 5*((R+e)*‖I0‖+(Sg+σ))+ζ5+(e*‖I0‖+σ) := by
  have hg5 := γ_nonneg 5
  have he : 0 ≤ e := (norm_nonneg _).trans hE
  have nE : ‖E‖ ≤ R+e := by have := norm_le_insert' E Es; linarith
  have nS : ‖S‖ ≤ Sg+σ := by have := norm_le_insert' S Ss; linarith
  have h1 := dot5_err hout
  have h2 : ‖E *ᵥ I0+S-(Es *ᵥ I0+Ss)‖ ≤ e*‖I0‖+σ := by
    rw [show E *ᵥ I0+S-(Es *ᵥ I0+Ss) = (E-Es) *ᵥ I0+(S-Ss) by rw [sub_mulVec]; abel]
    exact (norm_add_le _ _).trans (add_le_add ((Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul_of_nonneg_right hE (norm_nonneg _))) hS)
  have h3 : γ 5*(‖E‖*‖I0‖+‖S‖) ≤ γ 5*((R+e)*‖I0‖+(Sg+σ)) := by gcongr
  calc ‖out-(Es *ᵥ I0+Ss)‖ = ‖(out-(E *ᵥ I0+S))+(E *ᵥ I0+S-(Es *ᵥ I0+Ss))‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := by linarith

/-! ### The exact algorithm is a power of the shader matrix -/

lemma aug_sq (E : Mueller) (S : Stokes) :
    (fromBlocks E (replicateCol Unit S) 0 1 : Aug)*fromBlocks E (replicateCol Unit S) 0 1 =
      fromBlocks (E*E) (replicateCol Unit (E *ᵥ S+S)) 0 1 := by
  rw [fromBlocks_multiply]
  congr 1 <;> simp [replicateCol_mulVec, replicateCol_add]

lemma shaderMatrix_blocks (K : Mueller) (j : Stokes) (h : ℝ) :
    shaderMatrix K j h = fromBlocks (shaderLoop (-h • K) h j 12).1
      (replicateCol Unit (shaderLoop (-h • K) h j 12).2.2) 0 1 := by
  rw [shaderMatrix, shaderLoop_closed]

/-- After `k` squarings the exact algorithm holds the blocks of
`shaderMatrix^(2^k)`; `MatrixTransfer.exp_squaring` and `shader_step_error`
relate this to the exact cell `exp(2^k h A)`. -/
theorem squaring_exact (K : Mueller) (j : Stokes) (h : ℝ) (k : ℕ) :
    shaderMatrix K j h^(2^k) =
      fromBlocks (sqExact (shaderLoop (-h • K) h j 12).1 (shaderLoop (-h • K) h j 12).2.2 k).1
        (replicateCol Unit
          (sqExact (shaderLoop (-h • K) h j 12).1 (shaderLoop (-h • K) h j 12).2.2 k).2) 0 1 := by
  induction k with
  | zero => simpa [sqExact] using shaderMatrix_blocks K j h
  | succ k ih => rw [pow_succ, pow_mul, sq, ih, aug_sq]; rfl

/-- The plain L∞ bound on the exact powers. -/
lemma sqExact_norm {E : Mueller} {R0 : ℝ} (S : Stokes) (hR0 : ‖E‖ ≤ R0) :
    ∀ k, ‖(sqExact E S k).1‖ ≤ R0^(2^k)
  | 0 => by simpa [sqExact] using hR0
  | k+1 => by
    have ih := sqExact_norm S hR0 k
    simp only [sqExact]
    rw [pow_succ, pow_mul, sq]
    exact (norm_mul_le _ _).trans (mul_le_mul ih ih (norm_nonneg _) ((norm_nonneg _).trans ih))

/-- The matching bound on the exact sources. -/
def sgB (R0 s0 : ℝ) : ℕ → ℝ
  | 0 => s0
  | k+1 => (R0^(2^k)+1)*sgB R0 s0 k

lemma sqExact_source {E : Mueller} {S : Stokes} {R0 s0 : ℝ} (hR0 : ‖E‖ ≤ R0) (hs0 : ‖S‖ ≤ s0) :
    ∀ k, ‖(sqExact E S k).2‖ ≤ sgB R0 s0 k
  | 0 => by simpa [sqExact, sgB] using hs0
  | k+1 => by
    have ih := sqExact_source hR0 hs0 k
    have hR := sqExact_norm S hR0 k
    simp only [sqExact, sgB]
    calc ‖(sqExact E S k).1 *ᵥ (sqExact E S k).2+(sqExact E S k).2‖
        ≤ R0^(2^k)*sgB R0 s0 k+sgB R0 s0 k :=
          (norm_add_le _ _).trans (add_le_add ((Matrix.linfty_opNorm_mulVec _ _).trans
            (mul_le_mul hR ih (norm_nonneg _) ((norm_nonneg _).trans hR))) ih)
      _ = _ := by ring

/-! ### The whole cell -/

/-- `transfer_cell` for the computed `h` and `squares = k`: the returned
transmission and Stokes vector are within the running bounds of the exact
algorithm, whose result is `shaderMatrix^(2^k)` applied to `(initial, 1)`
(`squaring_exact`). `R`, `Sg` are any bounds on the exact powers'
exponential and source norms (`sqExact_norm`, `sqExact_source`). -/
theorem transfer_cell_error {K Mt X T E : Mueller} {S Sq I0 out j : Stokes} {h : ℝ} {k : ℕ}
    (R Sg : ℕ → ℝ) (hh : 0 ≤ h) (hm : ScaleM (-h) K Mt) (htay : TaylorTrace Mt h j 12 X T S)
    (hsq : SqTrace X S k E Sq) (hout : ∀ i, Dot5B (E i) I0 (Sq i) (out i))
    (hR : ∀ k, ‖(sqExact (shaderLoop (-h • K) h j 12).1 (shaderLoop (-h • K) h j 12).2.2 k).1‖ ≤ R k)
    (hSg : ∀ k, ‖(sqExact (shaderLoop (-h • K) h j 12).1 (shaderLoop (-h • K) h j 12).2.2 k).2‖ ≤
      Sg k) :
    let e0 := exB (h*‖K‖) (u*h*‖K‖+4*η) 12
    let σ0 := σB (h*‖K‖) (u*h*‖K‖+4*η) h ‖j‖ 12
    let ex := sqExact (shaderLoop (-h • K) h j 12).1 (shaderLoop (-h • K) h j 12).2.2 k
    ‖E-ex.1‖ ≤ eS R e0 k ∧
      ‖out-(ex.1 *ᵥ I0+ex.2)‖ ≤ γ 5*((R k+eS R e0 k)*‖I0‖+(Sg k+σS R Sg e0 σ0 k))+ζ5+
        (eS R e0 k*‖I0‖+σS R Sg e0 σ0 k) := by
  intro e0 σ0 ex
  have hρ : ‖-h • K‖ ≤ h*‖K‖ := by rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hh]
  have hμ : ‖Mt-(-h • K)‖ ≤ u*h*‖K‖+4*η := by
    have := scaleM_err hm
    rwa [abs_neg, abs_of_nonneg hh] at this
  obtain ⟨-, -, eX, -, eSrc, -⟩ := taylor_error hh hρ hμ le_rfl 12 X T S htay
  obtain ⟨hE, hS⟩ := squaring_error R Sg eX eSrc hR hSg k E Sq hsq
  exact ⟨hE, stokes_error hE (hR k) hS (hSg k) hout⟩

/-! ### Accepted cells

The shader rejects a cell unless its computed `bound*h ≤ 0.125`, where
`bound = abs(a.x)+dot(abs(a.yzw)+abs(r),vec3(1.0))` bounds every row sum of
`k`. `check_bound` turns the computed test into `‖-h·k‖ ≤ 1/8 + 10⁻⁶`, and
`taylor_accepted` evaluates the running bound of the exponential there. -/

/-- The absorption/Faraday matrix `k` of `transfer_cell` (rows). -/
def kMat (a : Fin 4 → ℝ) (r : Fin 3 → ℝ) : Mueller :=
  !![a 0, a 1, a 2, a 3; a 1, a 0, r 2, -r 1; a 2, -r 2, a 0, r 0; a 3, r 1, -r 0, a 0]

lemma kMat_norm (a : Fin 4 → ℝ) (r : Fin 3 → ℝ) :
    ‖kMat a r‖ ≤ |a 0|+((|a 1|+|r 0|)+(|a 2|+|r 1|)+(|a 3|+|r 2|)) := by
  have := abs_nonneg (a 0); have := abs_nonneg (a 1); have := abs_nonneg (a 2)
  have := abs_nonneg (a 3); have := abs_nonneg (r 0); have := abs_nonneg (r 1)
  have := abs_nonneg (r 2)
  refine norm_le_rows (by positivity) fun i => ?_
  fin_cases i <;> simp [kMat, Fin.sum_univ_four, abs_neg] <;> linarith

def ρ0 : ℝ := 1/8+1/10^6

lemma rnd_lo {x y : ℝ} (h : Rnd x y) : x-u*|x|-η ≤ y := by
  unfold Rnd at h; linarith [neg_abs_le (y-x)]
lemma rnd_hi {x y : ℝ} (h : Rnd x y) : y ≤ x+u*|x|+η := by
  unfold Rnd at h; linarith [le_abs_self (y-x)]

set_option maxHeartbeats 2000000 in
/-- A cell that passes the shader's computed test has `‖-h·k‖ ≤ 1/8 + 10⁻⁶`.
`q` is `abs(a.yzw)+abs(r)`, `ds` its `dot` with `vec3(1.0)` in any order,
`b` the computed `bound` and `c` the computed `bound*h`. -/
theorem check_bound (a : Fin 4 → ℝ) (r : Fin 3 → ℝ) {h : ℝ} (hh0 : 0 ≤ h) (hh : h ≤ 10^10)
    (q : Fin 3 → ℝ) (hq : ∀ i, Rnd (|a i.succ|+|r i|) (q i))
    (T : SumTree) (hT : (terms T).Perm [q 0, q 1, q 2]) (ds : ℝ) (hds : T.Computes u η ds)
    {b c : ℝ} (hb : Rnd (|a 0|+ds) b) (hc : Rnd (b*h) c) (hpass : c ≤ 1/8) :
    ‖-h • kMat a r‖ ≤ ρ0 := by
  have hu := u_pos; have hη := η_pos
  have hu1 : u ≤ 1/10^7 := by norm_num [u]
  have hη1 : η ≤ 1/10^37 := by norm_num [η]
  set B1 := |a 1|+|r 0|; set B2 := |a 2|+|r 1|; set B3 := |a 3|+|r 2|
  set B := |a 0|+(B1+B2+B3)
  have b1 : 0 ≤ B1 := by positivity
  have b2 : 0 ≤ B2 := by positivity
  have b3 : 0 ≤ B3 := by positivity
  have hB0 : 0 ≤ |a 0| := abs_nonneg _
  -- the three rounded sums
  have qb (i : Fin 3) (Bi : ℝ) (hBi : Bi = |a i.succ|+|r i|) (h0 : 0 ≤ Bi) :
      (1-u)*Bi-η ≤ q i ∧ |q i| ≤ (1+u)*Bi+η := by
    have h1 := hq i; rw [← hBi] at h1; unfold Rnd at h1
    rw [abs_of_nonneg h0] at h1
    constructor
    · linarith [neg_abs_le (q i-Bi)]
    · have := abs_sub_abs_le_abs_sub (q i) Bi; rw [abs_of_nonneg h0] at this; linarith
  obtain ⟨q0l, q0a⟩ := qb 0 B1 rfl b1
  obtain ⟨q1l, q1a⟩ := qb 1 B2 rfl b2
  obtain ⟨q2l, q2a⟩ := qb 2 B3 rfl b3
  -- the `dot`
  have hs := SumTree.error u η hu.le hη.le T ds hds
  rw [exact_terms, absSum_terms, leaves_terms, hT.sum_eq, (hT.map abs).sum_eq, hT.length_eq] at hs
  simp only [List.sum_cons, List.sum_nil, List.map_cons, List.map_nil, List.length_cons,
    List.length_nil, add_zero] at hs
  norm_num at hs
  set Bv := B1+B2+B3 with hBv
  have hBv0 : 0 ≤ Bv := by positivity
  have hBB : 0 ≤ B := by positivity
  have uu : u^2 ≤ u/10^7 := by nlinarith
  have m1 : u^2*Bv ≤ u*Bv/10^7 := by nlinarith [mul_le_mul_of_nonneg_right uu hBv0]
  have m1' : u^2*B ≤ u*B/10^7 := by nlinarith [mul_le_mul_of_nonneg_right uu hBB]
  have m2 : u*η ≤ η/10^7 := by nlinarith
  have uB : 0 ≤ u*Bv := by positivity
  have uB' : 0 ≤ u*|a 0| := by positivity
  have g3 : (1+u)^3-1 ≤ 4*u := by
    have : (1+u)^3-1 = 3*u+3*u^2+u^3 := by ring
    rw [this]; nlinarith
  have g3n : 0 ≤ (1+u)^3-1 := by
    have : 1 ≤ (1+u)^3 := one_le_pow₀ (by linarith); linarith
  have g3' : (1+u)^3 ≤ 2 := by linarith
  have qs : q 0+(q 1+q 2) ≤ (1+u)*Bv+3*η := by
    linarith [le_abs_self (q 0), le_abs_self (q 1), le_abs_self (q 2)]
  have qs' : (1-u)*Bv-3*η ≤ q 0+(q 1+q 2) := by linarith
  have hsa : |q 0|+(|q 1|+|q 2|) ≤ (1+u)*Bv+3*η := by linarith
  have e1 : ((1+u)^3-1)*(|q 0|+(|q 1|+|q 2|)) ≤ 4*(u*Bv)+4*(u^2*Bv)+12*(u*η) := by
    calc _ ≤ ((1+u)^3-1)*((1+u)*Bv+3*η) := mul_le_mul_of_nonneg_left hsa g3n
      _ ≤ 4*u*((1+u)*Bv+3*η) := mul_le_mul_of_nonneg_right g3 (by positivity)
      _ = _ := by ring
  have e2 : 5*(1+u)^3*η ≤ 10*η := by nlinarith
  have hds' := abs_le.mp (hs.trans (add_le_add e1 e2))
  have dlo : (1-6*u)*Bv-25*η ≤ ds := by nlinarith
  have dhi : ds ≤ (1+6*u)*Bv+25*η := by nlinarith
  -- `bound`
  have xlo : (1-6*u)*B-25*η ≤ |a 0|+ds := by nlinarith
  have xhi : |a 0|+ds ≤ (1+6*u)*B+25*η := by nlinarith
  have xabs : |(|a 0|+ds)| ≤ (1+6*u)*B+25*η := by
    have : 0 ≤ u*B := by positivity
    rw [abs_le]; constructor <;> linarith
  have ux := mul_le_mul_of_nonneg_left xabs hu.le
  have ux' : u*((1+6*u)*B+25*η) = u*B+6*(u^2*B)+25*(u*η) := by ring
  have blo : (1-8*u)*B-27*η ≤ b := by
    have := rnd_lo hb
    nlinarith
  have babs : |b| ≤ (1+8*u)*B+27*η := by
    have h1 := rnd_lo hb; have h2 := rnd_hi hb
    have : 0 ≤ u*B := by positivity
    rw [abs_le]; constructor <;> nlinarith
  -- the test
  have clo := rnd_lo hc
  rw [abs_mul, abs_of_nonneg hh0] at clo
  have p1 : ((1-8*u)*B-27*η)*h ≤ b*h := mul_le_mul_of_nonneg_right blo hh0
  have p2 : |b| *h ≤ ((1+8*u)*B+27*η)*h := mul_le_mul_of_nonneg_right babs hh0
  have key : h*B*(1-9*u-8*u^2) ≤ 1/8+η+27*η*h*(1+u) := by nlinarith
  have hηh : 27*η*h*(1+u) ≤ 28*10^10*η := by
    have : η*h ≤ η*10^10 := mul_le_mul_of_nonneg_left hh hη.le
    nlinarith
  have hBK := kMat_norm a r
  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hh0]
  have hk : h*‖kMat a r‖ ≤ h*B := mul_le_mul_of_nonneg_left hBK hh0
  have hc9 : 1-10*u ≤ 1-9*u-8*u^2 := by nlinarith
  have hPB : 0 ≤ h*B := by positivity
  have hm := mul_le_mul_of_nonneg_left hc9 hPB
  have : h*B*(1-10*u) ≤ 1/8+η+28*10^10*η := by linarith
  have hfin : (1/8+η+28*10^10*η) ≤ ρ0*(1-10*u) := by norm_num [ρ0, u, η]
  have h10 : 0 < 1-10*u := by linarith
  have : h*B ≤ ρ0 := by
    by_contra hcon; push Not at hcon
    have := mul_lt_mul_of_pos_right hcon h10
    linarith
  linarith

/-! #### The running bounds are monotone -/

lemma tB_mono {ρ ρ' : ℝ} (h0 : 0 ≤ ρ) (h : ρ ≤ ρ') : ∀ i, tB ρ i ≤ tB ρ' i
  | 0 => le_rfl
  | i+1 => by
    simp only [tB]
    have := tB_mono h0 h i
    have := tB_nonneg h0 i
    have := h0.trans h
    gcongr

lemma termF_mono {ρ μ t e ρ' μ' t' e' n : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ ≤ ρ') (hμ : 0 ≤ μ)
    (hμ' : μ ≤ μ') (ht : 0 ≤ t) (ht' : t ≤ t') (he : 0 ≤ e) (he' : e ≤ e') (hn : 0 < n) :
    termF ρ μ t e n ≤ termF ρ' μ' t' e' n := by
  have := γ_nonneg 4; have := ζ4_nonneg; have := u_pos; have := η_pos
  have := hρ.trans hρ'; have := hμ.trans hμ'
  unfold termF; dsimp only
  gcongr

lemma xB_mono {ρ ρ' : ℝ} (h0 : 0 ≤ ρ) (h : ρ ≤ ρ') : ∀ i, xB ρ i ≤ xB ρ' i
  | 0 => le_rfl
  | i+1 => by simp only [xB]; exact add_le_add (xB_mono h0 h i) (tB_mono h0 h (i+1))

lemma xB_nonneg {ρ : ℝ} (h0 : 0 ≤ ρ) : ∀ i, 0 ≤ xB ρ i
  | 0 => zero_le_one
  | i+1 => by simp only [xB]; exact add_nonneg (xB_nonneg h0 i) (tB_nonneg h0 (i+1))

lemma exB_nonneg {ρ μ : ℝ} (h0 : 0 ≤ ρ) (hμ : 0 ≤ μ) : ∀ i, 0 ≤ exB ρ μ i
  | 0 => le_rfl
  | i+1 => by
    have := exB_nonneg h0 hμ i; have := eB_nonneg h0 hμ (i+1); have := xB_nonneg h0 (i+1)
    have := u_pos; have := η_pos
    simp only [exB]; positivity

/-- Budgets for `eB` on accepted cells, in units of `u`. -/
def Eb : ℕ → ℝ
  | 0 => 0
  | 1 => 1377/1000*u
  | 2 => 861/5000*u
  | 3 => 1077/100000*u
  | 4 => 449/1000000*u
  | 5 => 351/25000000*u
  | 6 => 439/1250000000*u
  | 7 => 183/25000000000*u
  | 8 => 327/2500000000000*u
  | 9 => 409/200000000000000*u
  | 10 => 1421/50000000000000000*u
  | 11 => 1777/5000000000000000000*u
  | 12 => 4041/1000000000000000000000*u
  | _ => 0

/-- Budgets for `exB` on accepted cells. -/
def Xe : ℕ → ℝ
  | 0 => 0
  | 1 => 501/200*u
  | 2 => 1907/500*u
  | 3 => 4963/1000*u
  | 4 => 6103/1000*u
  | 5 => 1811/250*u
  | 6 => 4193/500*u
  | 7 => 9529/1000*u
  | 8 => 267/25*u
  | 9 => 1183/100*u
  | 10 => 649/50*u
  | 11 => 1413/100*u
  | 12 => 382/25*u
  | _ => 0

def μ0 : ℝ := u*ρ0+4*η

lemma eB_check : ∀ i < 12, termF ρ0 μ0 (tB ρ0 i) (Eb i) ((i+1 : ℕ) : ℝ) ≤ Eb (i+1) := by
  intro i hi
  interval_cases i <;> norm_num [termF, tB, ρ0, μ0, γ, ζ4, u, η, Eb]

lemma exB_check : ∀ i < 12,
    u*(xB ρ0 (i+1)+(Xe i+Eb (i+1)))+4*η+(Xe i+Eb (i+1)) ≤ Xe (i+1) := by
  intro i hi
  interval_cases i <;> norm_num [xB, tB, ρ0, u, η, Eb, Xe]

lemma eB_budget {ρ μ : ℝ} (hρ : 0 ≤ ρ) (hρ0 : ρ ≤ ρ0) (hμ : 0 ≤ μ) (hμ0 : μ ≤ μ0) :
    ∀ i ≤ 12, eB ρ μ i ≤ Eb i
  | 0, _ => by simp [eB, Eb]
  | i+1, hi => by
    have ih := eB_budget hρ hρ0 hμ hμ0 i (by omega)
    simp only [eB]
    exact (termF_mono hρ hρ0 hμ hμ0 (tB_nonneg hρ i) (tB_mono hρ hρ0 i) (eB_nonneg hρ hμ i) ih
      (by positivity)).trans (eB_check i (by omega))

lemma exB_budget {ρ μ : ℝ} (hρ : 0 ≤ ρ) (hρ0 : ρ ≤ ρ0) (hμ : 0 ≤ μ) (hμ0 : μ ≤ μ0) :
    ∀ i ≤ 12, exB ρ μ i ≤ Xe i
  | 0, _ => by simp [exB, Xe]
  | i+1, hi => by
    have ih := exB_budget hρ hρ0 hμ hμ0 i (by omega)
    have he := eB_budget hρ hρ0 hμ hμ0 (i+1) hi
    have hx := xB_mono hρ hρ0 (i+1)
    have := u_pos
    simp only [exB]
    refine le_trans ?_ (exB_check i (by omega))
    gcongr

/-- On every cell the shader accepts, the computed exponential after the
twelve-term loop is within `16u` of the exact Taylor polynomial and within
`16u + 10⁻²⁰` of `exp(-h·k)`. -/
theorem taylor_accepted {a : Fin 4 → ℝ} {r : Fin 3 → ℝ} {Mt X T : Mueller} {S j : Stokes} {h : ℝ}
    (hh : 0 ≤ h) (hacc : ‖-h • kMat a r‖ ≤ ρ0) (hm : ScaleM (-h) (kMat a r) Mt)
    (htay : TaylorTrace Mt h j 12 X T S) :
    ‖X-(shaderLoop (-h • kMat a r) h j 12).1‖ ≤ 16*u ∧
      ‖X-NormedSpace.exp (-h • kMat a r)‖ ≤ 16*u+1/10^20 := by
  have hu := u_pos; have hη := η_pos
  set ρ := ‖-h • kMat a r‖
  have eρ : ρ = h*‖kMat a r‖ := by simp [ρ, norm_smul, abs_of_nonneg hh]
  have hμ : ‖Mt-(-h • kMat a r)‖ ≤ u*ρ+4*η := by
    have := scaleM_err hm
    rw [abs_neg, abs_of_nonneg hh] at this
    rw [eρ]; linarith
  obtain ⟨-, -, eX, -, -, -⟩ := taylor_error hh le_rfl hμ le_rfl 12 X T S htay
  have hμ0 : u*ρ+4*η ≤ μ0 := by
    unfold μ0; have := mul_le_mul_of_nonneg_left hacc hu.le; linarith
  have hb := exB_budget (μ := u*ρ+4*η) (norm_nonneg _) hacc (by positivity) hμ0 12 le_rfl
  have hX12 : Xe 12 = 382/25*u := rfl
  have h1 : ‖X-(shaderLoop (-h • kMat a r) h j 12).1‖ ≤ 16*u := by
    have := eX.trans hb; rw [hX12] at this; linarith
  refine ⟨h1, ?_⟩
  have htail := taylor_tail (-h • kMat a r) (hacc.trans (by norm_num [ρ0]))
  have hcl : (shaderLoop (-h • kMat a r) h j 12).1 =
      ∑ n ∈ range 13, ((n.factorial : ℝ)⁻¹) • (-h • kMat a r)^n := by rw [shaderLoop_closed]
  rw [← hcl] at htail
  have h13 : ρ^13*(14/(Nat.factorial 13*13)) ≤ 1/10^20 := by
    have : ρ^13 ≤ ρ0^13 := pow_le_pow_left₀ (norm_nonneg _) hacc 13
    have h2 : ρ0^13*(14/(Nat.factorial 13*13)) ≤ (1:ℝ)/10^20 := by
      norm_num [ρ0, Nat.factorial]
    nlinarith [show (0:ℝ) < 14/(Nat.factorial 13*13) by positivity]
  calc ‖X-NormedSpace.exp (-h • kMat a r)‖ ≤ ‖X-(shaderLoop (-h • kMat a r) h j 12).1‖+
        ‖NormedSpace.exp (-h • kMat a r)-(shaderLoop (-h • kMat a r) h j 12).1‖ := by
        rw [← norm_neg (NormedSpace.exp _-_)]
        convert norm_add_le _ _ using 2; abel
    _ ≤ 16*u+1/10^20 := add_le_add h1 (htail.trans h13)

/-! #### The source after the loop -/

/-- The exact source factors as `h·J` times a function of `ρ`. -/
def sbc (ρ : ℝ) : ℕ → ℝ
  | 0 => 1
  | i+1 => sbc ρ i+1/((i+2 : ℕ) : ℝ)*tB ρ (i+1)

lemma sB_eq (ρ h J : ℝ) : ∀ i, sB ρ h J i = h*J*sbc ρ i
  | 0 => by simp [sB, sbc]
  | i+1 => by simp only [sB, sbc, sB_eq ρ h J i]; ring

lemma sbc_mono {ρ ρ' : ℝ} (h0 : 0 ≤ ρ) (h : ρ ≤ ρ') : ∀ i, sbc ρ i ≤ sbc ρ' i
  | 0 => le_rfl
  | i+1 => by
    simp only [sbc]
    have := tB_mono h0 h (i+1)
    gcongr
    exact sbc_mono h0 h i

/-- The coefficients of `srcF` as a polynomial in `h` and `J`. -/
def c1 (t e n S A D : ℝ) : ℝ :=
  (1+u)*(A+D+((u*(1+5*u)+5*u)*(t+(γ 4*(t+e)+e))+(γ 4*(t+e)+e))/n)+u*S
def c2 (n D : ℝ) : ℝ := (1+u)*(D+(u*(1+5*u)+5*u+1)*ζ4/n)
def c3 (t e D : ℝ) : ℝ := (1+u)*(D+η*(1+u)*(t+(γ 4*(t+e)+e)))
def c4 (D : ℝ) : ℝ := (1+u)*(D+η*(1+u)*ζ4+η)+η

lemma srcF_expand (h J t e n S A D : ℝ) :
    srcF h J t e n (S*(h*J)) (A*(h*J)+D*((1+h)*(1+J))) =
      c1 t e n S A D*(h*J)+c2 n D*h+c3 t e D*J+c4 D := by
  unfold srcF c1 c2 c3 c4; ring

lemma srcF_mono {h J t e n s σ t' e' s' σ' : ℝ} (hh : 0 ≤ h) (hJ : 0 ≤ J) (hn : 0 < n)
    (ht : 0 ≤ t) (ht' : t ≤ t') (he : 0 ≤ e) (he' : e ≤ e') (hs : s ≤ s') (hσ : σ ≤ σ') :
    srcF h J t e n s σ ≤ srcF h J t' e' n s' σ' := by
  have := γ_nonneg 4; have := ζ4_nonneg; have := u_pos; have := η_pos
  have := ht.trans ht'; have := he.trans he'
  unfold srcF; dsimp only
  gcongr

lemma poly_le {h J a b c d A D : ℝ} (hh : 0 ≤ h) (hJ : 0 ≤ J) (ha : a ≤ A+D) (hb : b ≤ D)
    (hc : c ≤ D) (hd : d ≤ D) : a*(h*J)+b*h+c*J+d ≤ A*(h*J)+D*((1+h)*(1+J)) := by
  have hhJ : 0 ≤ h*J := mul_nonneg hh hJ
  have := mul_le_mul_of_nonneg_right ha hhJ
  have := mul_le_mul_of_nonneg_right hb hh
  have := mul_le_mul_of_nonneg_right hc hJ
  have e : D*((1+h)*(1+J)) = D+D*h+D*J+D*(h*J) := by ring
  rw [e]; nlinarith

/-- Budgets for the exact source, in units of `h*J`. -/
def Sb : ℕ → ℝ
  | 0 => 1
  | 1 => 1063/1000
  | 2 => 533/500
  | 3 => 533/500
  | 4 => 533/500
  | 5 => 533/500
  | 6 => 533/500
  | 7 => 533/500
  | 8 => 533/500
  | 9 => 533/500
  | 10 => 533/500
  | 11 => 533/500
  | 12 => 533/500
  | _ => 0

/-- Budgets for the source error's `h*J` coefficient. -/
def Ab : ℕ → ℝ
  | 0 => 1*u
  | 1 => 169/50*u
  | 2 => 2267/500*u
  | 3 => 561/100*u
  | 4 => 6683/1000*u
  | 5 => 7757/1000*u
  | 6 => 1104/125*u
  | 7 => 2477/250*u
  | 8 => 1099/100*u
  | 9 => 1207/100*u
  | 10 => 263/20*u
  | 11 => 356/25*u
  | 12 => 1533/100*u
  | _ => 0

/-- Budgets for the source error's flush-to-zero coefficient. -/
def Db : ℕ → ℝ
  | 0 => η
  | 1 => 331/6250000000000000000000000000000000000000
  | 2 => 8047/100000000000000000000000000000000000000000
  | 3 => 1041/10000000000000000000000000000000000000000
  | 4 => 639/5000000000000000000000000000000000000000
  | 5 => 303/2000000000000000000000000000000000000000
  | 6 => 219/1250000000000000000000000000000000000000
  | 7 => 199/1000000000000000000000000000000000000000
  | 8 => 557/2500000000000000000000000000000000000000
  | 9 => 1233/5000000000000000000000000000000000000000
  | 10 => 169/625000000000000000000000000000000000000
  | 11 => 2943/10000000000000000000000000000000000000000
  | 12 => 1591/5000000000000000000000000000000000000000
  | _ => 0

lemma sbc_check : ∀ i ≤ 12, sbc ρ0 i ≤ Sb i := by
  intro i hi
  interval_cases i <;> norm_num [sbc, tB, ρ0, Sb]

lemma src_check : ∀ i < 12,
    c1 (tB ρ0 (i+1)) (Eb (i+1)) ((i+2 : ℕ) : ℝ) (Sb (i+1)) (Ab i) (Db i) ≤ Ab (i+1)+Db (i+1) ∧
    c2 ((i+2 : ℕ) : ℝ) (Db i) ≤ Db (i+1) ∧ c3 (tB ρ0 (i+1)) (Eb (i+1)) (Db i) ≤ Db (i+1) ∧
    c4 (Db i) ≤ Db (i+1) := by
  intro i hi
  interval_cases i <;> norm_num [c1, c2, c3, c4, tB, ρ0, γ, ζ4, u, η, Eb, Sb, Ab, Db]

lemma σB_budget {ρ μ h J : ℝ} (hρ : 0 ≤ ρ) (hρ0 : ρ ≤ ρ0) (hμ : 0 ≤ μ) (hμ0 : μ ≤ μ0)
    (hh : 0 ≤ h) (hJ : 0 ≤ J) :
    ∀ i ≤ 12, σB ρ μ h J i ≤ Ab i*(h*J)+Db i*((1+h)*(1+J))
  | 0, _ => by
    have := η_pos
    have : 1 ≤ (1+h)*(1+J) := by nlinarith
    simp only [σB, Ab, Db]
    nlinarith
  | i+1, hi => by
    have ih := σB_budget hρ hρ0 hμ hμ0 hh hJ i (by omega)
    have he := eB_budget hρ hρ0 hμ hμ0 (i+1) hi
    have hs : sB ρ h J (i+1) ≤ Sb (i+1)*(h*J) := by
      rw [sB_eq, mul_comm (Sb _)]
      exact mul_le_mul_of_nonneg_left ((sbc_mono hρ hρ0 (i+1)).trans (sbc_check (i+1) hi))
        (mul_nonneg hh hJ)
    obtain ⟨k1, k2, k3, k4⟩ := src_check i (by omega)
    simp only [σB]
    refine (srcF_mono hh hJ (by positivity) (tB_nonneg hρ _) (tB_mono hρ hρ0 _)
      (eB_nonneg hρ hμ _) he hs ih).trans ?_
    rw [srcF_expand]
    exact poly_le hh hJ k1 k2 k3 k4

/-- On every cell the shader accepts, the computed source after the
twelve-term loop is within `16u·h‖j‖ + 2⁻¹²¹(1+h)(1+‖j‖)` of the exact
loop's. -/
theorem source_accepted {a : Fin 4 → ℝ} {r : Fin 3 → ℝ} {Mt X T : Mueller} {S j : Stokes} {h : ℝ}
    (hh : 0 ≤ h) (hacc : ‖-h • kMat a r‖ ≤ ρ0) (hm : ScaleM (-h) (kMat a r) Mt)
    (htay : TaylorTrace Mt h j 12 X T S) :
    ‖S-(shaderLoop (-h • kMat a r) h j 12).2.2‖ ≤ 16*u*(h*‖j‖)+1/2^121*((1+h)*(1+‖j‖)) := by
  have hu := u_pos; have hη := η_pos
  set ρ := ‖-h • kMat a r‖
  have eρ : ρ = h*‖kMat a r‖ := by simp [ρ, norm_smul, abs_of_nonneg hh]
  have hμ : ‖Mt-(-h • kMat a r)‖ ≤ u*ρ+4*η := by
    have := scaleM_err hm
    rw [abs_neg, abs_of_nonneg hh] at this
    rw [eρ]; linarith
  obtain ⟨-, -, -, -, eS0, -⟩ := taylor_error hh le_rfl hμ le_rfl 12 X T S htay
  have hμ0 : u*ρ+4*η ≤ μ0 := by
    unfold μ0; have := mul_le_mul_of_nonneg_left hacc hu.le; linarith
  have hb := σB_budget (μ := u*ρ+4*η) (norm_nonneg _) hacc (by positivity) hμ0 hh
    (norm_nonneg j) 12 le_rfl
  have hA : Ab 12 = 1533/100*u := rfl
  have hD : Db 12 = 1591/5000000000000000000000000000000000000000 := rfl
  rw [hA, hD] at hb
  have hhJ : 0 ≤ h*‖j‖ := mul_nonneg hh (norm_nonneg _)
  have h1 : 0 ≤ (1+h)*(1+‖j‖) := by have := norm_nonneg j; positivity
  have h2 : (1591/5000000000000000000000000000000000000000 : ℝ) ≤ 1/2^121 := by norm_num
  nlinarith [mul_le_mul_of_nonneg_right h2 h1]

end BlackHole.WgslTransferCell
