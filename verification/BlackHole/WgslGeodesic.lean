module

public import BlackHole.WgslPoly

/-! All-input WGSL error bounds for `geodesic_rhs`, `rk_state` and the RK4
combination in `geodesic.wesl` (obligation F2).

```
fn geodesic_rhs(ray: Ray, m: Metric) -> Derivs {
    let k = m.inv*ray.p;
    let dg_k = k.y*m.dx + k.z*m.dy + k.w*m.dz;
    let dg_f = ray.screen.y*m.dx + ray.screen.z*m.dy + ray.screen.w*m.dz;
    let contracted = vec4<f32>(0.0, dot(k,m.dx*ray.screen),
        dot(k,m.dy*ray.screen),dot(k,m.dz*ray.screen));
    return Derivs(k.yzw,
        0.5*vec4<f32>(0.0,dot(k,m.dx*k),dot(k,m.dy*k),dot(k,m.dz*k)),
        -0.5*m.inv*(dg_k*ray.screen + dg_f*k - contracted));
}
fn rk_state(ray: Ray, d: Derivs, h: f32) -> Ray {
    return Ray(ray.pos+h*d.pos,ray.p+h*d.p,ray.screen+h*d.screen);
}
// next = rk_state(ray, k1 + 2 k2 + 2 k3 + k4, h/6)
```

The inputs are the metric arrays and ray actually passed to the kernel, so
these bounds measure the kernel's own arithmetic. Errors already present in
the metric (from `add_kerr`) enter through the input error allowances `k`,
`α` of `PExpr.error`. Matrix layout (row or column major) only relabels
inputs, and a shared subexpression such as `k` is covered because each copy
may round independently. -/

@[expose] public section
noncomputable section

namespace BlackHole.WgslGeodesic
open WgslPoly PExpr

/-! Input indices: `inv` 0–15, `dx` 16–31, `dy` 32–47, `dz` 48–63 (entry
`4 i + j`), momentum `p` 64–67 and screen 68–71. -/

def inv (i j : Fin 4) : PExpr := input (4*i+j)
def dmat (e : Fin 3) (i j : Fin 4) : PExpr := input (16+16*e+4*i+j)
def p (i : Fin 4) : PExpr := input (64+i)
def f (i : Fin 4) : PExpr := input (68+i)

def sum4 (t : Fin 4 → PExpr) : PExpr := add (add (add (t 0) (t 1)) (t 2)) (t 3)
def sum3 (t : Fin 3 → PExpr) : PExpr := add (add (t 0) (t 1)) (t 2)
def mv (M : Fin 4 → Fin 4 → PExpr) (v : Fin 4 → PExpr) (i : Fin 4) : PExpr :=
  sum4 fun j => mul (M i j) (v j)
def dot (a b : Fin 4 → PExpr) : PExpr := sum4 fun i => mul (a i) (b i)

def k : Fin 4 → PExpr := mv inv p
/-- `c.y*m.dx + c.z*m.dy + c.w*m.dz` for a vector `c`. -/
def comb (c : Fin 4 → PExpr) (i j : Fin 4) : PExpr := sum3 fun e => mul (c e.succ) (dmat e i j)

def contracted (i : Fin 4) : PExpr :=
  Fin.cases (const 0) (fun e => dot k (mv (dmat e) f)) i

def posRhs (i : Fin 3) : PExpr := k i.succ
def momRhs (i : Fin 4) : PExpr :=
  mul (const (1/2)) (Fin.cases (const 0) (fun e => dot k (mv (dmat e) k)) i)
def screenRhs (i : Fin 4) : PExpr :=
  mul (const (-1/2)) (mv inv (fun j => sub (add (mv (comb k) f j) (mv (comb f) k j)) (contracted j)) i)

/-- All eleven output components of `geodesic_rhs`. -/
def rhs (o : Fin 11) : PExpr :=
  if h : o.val < 3 then posRhs ⟨o,h⟩ else if h' : o.val < 7 then momRhs ⟨o-3,by omega⟩
  else screenRhs ⟨o-7,by omega⟩

theorem divcOk_sum4 {t : Fin 4 → PExpr} (h : ∀ i, (t i).DivcOk) : (sum4 t).DivcOk :=
  ⟨⟨⟨h 0,h 1⟩,h 2⟩,h 3⟩
theorem divcOk_sum3 {t : Fin 3 → PExpr} (h : ∀ i, (t i).DivcOk) : (sum3 t).DivcOk :=
  ⟨⟨h 0,h 1⟩,h 2⟩
theorem divcOk_mv {M : Fin 4 → Fin 4 → PExpr} {v : Fin 4 → PExpr} (hM : ∀ i j, (M i j).DivcOk)
    (hv : ∀ j, (v j).DivcOk) (i : Fin 4) : (mv M v i).DivcOk :=
  divcOk_sum4 fun j => ⟨hM i j,hv j⟩
theorem divcOk_dot {a b : Fin 4 → PExpr} (ha : ∀ i, (a i).DivcOk) (hb : ∀ i, (b i).DivcOk) :
    (dot a b).DivcOk := divcOk_sum4 fun i => ⟨ha i,hb i⟩

/-- `geodesic_rhs` has no division. -/
theorem rhs_divcOk (o : Fin 11) : (rhs o).DivcOk := by
  have hin (n : ℕ) : (input n).DivcOk := trivial
  have hk (i : Fin 4) : (k i).DivcOk := divcOk_mv (fun _ _ => hin _) (fun _ => hin _) i
  have hcomb (c : Fin 4 → PExpr) (hc : ∀ i, (c i).DivcOk) (i j : Fin 4) : (comb c i j).DivcOk :=
    divcOk_sum3 fun e => ⟨hc e.succ,hin _⟩
  have hcon (i : Fin 4) : (contracted i).DivcOk := by
    cases i using Fin.cases with
    | zero => trivial
    | succ e => exact divcOk_dot hk (divcOk_mv (fun _ _ => hin _) (fun _ => hin _))
  unfold rhs
  split_ifs
  · exact hk _
  · refine ⟨trivial,?_⟩
    generalize (⟨o-3,_⟩ : Fin 4) = i
    cases i using Fin.cases with
    | zero => trivial
    | succ e => exact divcOk_dot hk (divcOk_mv (fun _ _ => hin _) hk)
  · have hj (j : Fin 4) :
        (sub (add (mv (comb k) f j) (mv (comb f) k j)) (contracted j)).DivcOk :=
      ⟨⟨divcOk_mv (hcomb k hk) (fun _ => hin _) j,divcOk_mv (hcomb f (fun _ => hin _)) hk j⟩,hcon j⟩
    exact ⟨trivial,divcOk_mv (fun _ _ => hin _) hj _⟩

/-- The WGSL error of every `geodesic_rhs` output, for every input. `A` is
the absolute evaluation of that output's program. -/
theorem geodesic_rhs_error (v w α : ℕ → ℝ) (kk : ℕ → ℕ)
    (hα : ∀ i, |v i| ≤ α i) (hw : ∀ i, |w i-v i| ≤ Γ (kk i)*α i) (o : Fin 11) (y : ℝ)
    (hy : (rhs o).Computes w y) :
    |y-(rhs o).exact v| ≤ Γ ((rhs o).ops kk)*(rhs o).absEval α :=
  (error v w α kk hα hw (rhs o) y (rhs_divcOk o) hy).2

/-- Rounded operations per output: 7 for position, 176 for momentum and 869
for the screen, counting each use of the shared `k` separately. -/
theorem rhs_ops (o : Fin 11) : (rhs o).ops (fun _ => 0) ≤ 869 := by
  fin_cases o <;> decide

theorem Γ869_small : Γ 869 < 3/10000 := by
  have hn : ((869:ℕ):ℝ)*U < 1 := by unfold U Wgsl.u; norm_num
  refine (Γ_le 869 hn).trans_lt ?_
  unfold U Wgsl.u; norm_num

/-- With exact inputs every `geodesic_rhs` output is within `3·10⁻⁴` of the
exact value, relative to the absolute evaluation of its program. -/
theorem geodesic_rhs_exact_inputs (v : ℕ → ℝ) (o : Fin 11) (y : ℝ) (hy : (rhs o).Computes v y) :
    |y-(rhs o).exact v| ≤ 3/10000*(rhs o).absEval (fun i => |v i|) := by
  have hall := error v v (fun i => |v i|) (fun _ => 0) (fun _ => le_rfl) (fun i => by simp [Γ]) (rhs o) y
    (rhs_divcOk o) hy
  have hA : 0 ≤ (rhs o).absEval (fun i => |v i|) := (abs_nonneg _).trans hall.1
  refine hall.2.trans (mul_le_mul_of_nonneg_right ?_ hA)
  exact ((Γ_mono (rhs_ops o)).trans Γ869_small.le)

/-! RK4 arithmetic. Inputs: state component 0, step `h` 1, stage derivatives
2–5 (each carrying the error of its own `geodesic_rhs` evaluation). -/

def stage (c : ℝ) : PExpr := add (input 0) (mul (mul (const c) (input 1)) (input 2))
def combination : PExpr :=
  add (input 0) (mul (divc (input 1) 6)
    (add (add (add (input 2) (mul (const 2) (input 3))) (mul (const 2) (input 4))) (input 5)))

theorem combination_ops (kk : ℕ → ℕ) :
    combination.ops kk = kk 0+kk 1+kk 2+kk 3+kk 4+kk 5+8 := by
  simp only [combination,ops]; omega

/-- The RK4 update `ray + (h/6)(k1+2k2+2k3+k4)` for one component, with stage
derivative errors carried as input allowances. -/
theorem rk4_combination_error (v w α : ℕ → ℝ) (kk : ℕ → ℕ)
    (hα : ∀ i, |v i| ≤ α i) (hw : ∀ i, |w i-v i| ≤ Γ (kk i)*α i) (y : ℝ)
    (hy : combination.Computes w y) :
    |y-(v 0+v 1/6*(v 2+2*v 3+2*v 4+v 5))| ≤
      Γ (kk 0+kk 1+kk 2+kk 3+kk 4+kk 5+8)*combination.absEval α := by
  have h := (error v w α kk hα hw combination y
    (by simp only [combination,DivcOk]; norm_num) hy).2
  rw [combination_ops] at h
  simpa [combination,exact] using h

/-- A stage state `ray + (c h) d`, with `c = 1/2` or `1`. -/
theorem rk4_stage_error (c : ℝ) (v w α : ℕ → ℝ) (kk : ℕ → ℕ)
    (hα : ∀ i, |v i| ≤ α i) (hw : ∀ i, |w i-v i| ≤ Γ (kk i)*α i) (y : ℝ)
    (hy : (stage c).Computes w y) :
    |y-(v 0+c*v 1*v 2)| ≤ Γ (kk 0+kk 1+kk 2+3)*(stage c).absEval α := by
  have h := (error v w α kk hα hw (stage c) y (by simp [stage,DivcOk]) hy).2
  have hops : (stage c).ops kk = kk 0+kk 1+kk 2+3 := by simp only [stage,ops]; omega
  rw [hops] at h
  simpa [stage,exact] using h

end BlackHole.WgslGeodesic
