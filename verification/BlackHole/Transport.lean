module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section

namespace BlackHole.Transport

variable {n : Type*} [Fintype n]

def loweredConnection (dg : n → n → n → ℝ) (a b c : n) : ℝ :=
  (dg b a c+dg c a b-dg a b c)/2

omit [Fintype n] in
theorem connection_metric_compatible (dg : n → n → n → ℝ)
    (hsym : ∀ d i j, dg d i j = dg d j i) (a b c : n) :
    loweredConnection dg a b c+loweredConnection dg c b a = dg b a c := by
  unfold loweredConnection
  rw [hsym b c a, hsym a c b, hsym c b a]
  ring

theorem lower_raised_connection [DecidableEq n] (g inv : Matrix n n ℝ)
    (hinv : g*inv = 1) (dg : n → n → n → ℝ) (b c : n) :
    g.mulVec (inv.mulVec (fun a => loweredConnection dg a b c)) =
      fun a => loweredConnection dg a b c := by
  rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]

private theorem sum_reverse (f : n → n → n → ℝ) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ j, ∑ i, f i j k := by
  calc
    _ = ∑ j, ∑ i, ∑ k, f i j k := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, f i j k := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ k, ∑ j, ∑ i, f i j k := Finset.sum_comm

def contractedConnection (inv : Matrix n n ℝ) (dg : n → n → n → ℝ)
    (tangent : n → ℝ) (a c : n) : ℝ :=
  (inv.mulVec (fun d => ∑ b, loweredConnection dg d b c*tangent b)) a

theorem contracted_metric_compatible [DecidableEq n] (g inv : Matrix n n ℝ)
    (hinv : g*inv = 1) (hsym : ∀ i j, g i j = g j i)
    (dg : n → n → n → ℝ) (hdsym : ∀ d i j, dg d i j = dg d j i)
    (tangent : n → ℝ) (i j : n) :
    (∑ k, (contractedConnection inv dg tangent k i*g k j+
      g i k*contractedConnection inv dg tangent k j)) = ∑ b, dg b i j*tangent b := by
  have hcol (a c : n) : (∑ k, g a k*contractedConnection inv dg tangent k c) =
      ∑ b, loweredConnection dg a b c*tangent b := by
    change (g.mulVec (inv.mulVec _)) a = _
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hfirst : (∑ k, contractedConnection inv dg tangent k i*g k j) =
      ∑ b, loweredConnection dg j b i*tangent b := by
    convert hcol j i using 1
    apply Finset.sum_congr rfl
    intro k _
    rw [hsym k j]
    ring
  rw [Finset.sum_add_distrib, hfirst, hcol, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [← add_mul, add_comm, connection_metric_compatible dg hdsym]

theorem stationary_momentum_constant (p : ℝ → ℝ)
    (hp : ∀ t, HasDerivAt p 0 t) (a b : ℝ) : p a = p b := by
  exact is_const_of_deriv_eq_zero (fun t => (hp t).differentiableAt) (fun t => (hp t).deriv) a b

/-- Metric compatibility cancels every term in the derivative of g(u,v).
    C is the connection contracted with the path tangent. -/
theorem metric_pairing_rate_zero (g C : n → n → ℝ) (u v : n → ℝ) :
    (∑ i, ∑ j,
      ((∑ k, (C k i*g k j+g i k*C k j))*u i*v j+
      g i j*(-(∑ k, C i k*u k))*v j+g i j*u i*(-(∑ k, C j k*v k)))) = 0 := by
  have hU : (∑ i, ∑ j, ∑ k, g i j*(C i k*u k)*v j) =
      ∑ i, ∑ j, ∑ k, (C k i*g k j)*u i*v j := by
    rw [sum_reverse]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hV : (∑ i, ∑ j, ∑ k, g i j*u i*(C j k*v k)) =
      ∑ i, ∑ j, ∑ k, (g i k*C k j)*u i*v j := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp only [Finset.sum_add_distrib, add_mul, Finset.sum_mul, Finset.mul_sum,
    mul_neg, neg_mul, Finset.sum_neg_distrib]
  rw [hU, hV]
  ring

def pairing (g : Matrix n n ℝ) (u v : n → ℝ) : ℝ := ∑ i, ∑ j, g i j*u i*v j

/-- Continuous parallel transport preserves metric pairings. Setting u=v
    gives norm conservation, and taking u as the geodesic tangent gives
    polarization transversality. This is an exact ODE theorem, not an RK4 invariant. -/
theorem transported_pairing_derivative (g C : ℝ → Matrix n n ℝ)
    (u v : ℝ → n → ℝ) (t : ℝ)
    (hg : ∀ i j, HasDerivAt (fun s => g s i j)
      (∑ k, (C t k i*g t k j+g t i k*C t k j)) t)
    (hu : ∀ i, HasDerivAt (fun s => u s i) (-(∑ k, C t i k*u t k)) t)
    (hv : ∀ i, HasDerivAt (fun s => v s i) (-(∑ k, C t i k*v t k)) t) :
    HasDerivAt (fun s => pairing (g s) (u s) (v s)) 0 t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => ((hg i j).mul (hu i)).mul (hv j)))
  simp only [Pi.mul_apply] at h
  change HasDerivAt (fun s => ∑ i, ∑ j, g s i j*u s i*v s j) 0 t
  convert h using 1
  have hz := metric_pairing_rate_zero (g t) (C t) (u t) (v t)
  convert hz.symm using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem transported_pairing_constant (g C : ℝ → Matrix n n ℝ)
    (u v : ℝ → n → ℝ)
    (hg : ∀ t i j, HasDerivAt (fun s => g s i j)
      (∑ k, (C t k i*g t k j+g t i k*C t k j)) t)
    (hu : ∀ t i, HasDerivAt (fun s => u s i) (-(∑ k, C t i k*u t k)) t)
    (hv : ∀ t i, HasDerivAt (fun s => v s i) (-(∑ k, C t i k*v t k)) t)
    (a b : ℝ) : pairing (g a) (u a) (v a) = pairing (g b) (u b) (v b) := by
  have h := fun t => transported_pairing_derivative g C u v t (hg t) (hu t) (hv t)
  exact is_const_of_deriv_eq_zero (fun t => (h t).differentiableAt) (fun t => (h t).deriv) a b

end BlackHole.Transport
