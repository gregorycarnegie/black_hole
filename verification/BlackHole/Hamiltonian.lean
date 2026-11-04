module

public import BlackHole.Transport
public import BlackHole.MetricInverse
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.LinearCombination

@[expose] public section
noncomputable section

namespace BlackHole.Transport

variable {n : Type*} [Fintype n]

def metricRate (dg : n → Matrix n n ℝ) (k : n → ℝ) : Matrix n n ℝ :=
  Matrix.of (fun i j => ∑ e, dg e i j*k e)

def momentumForce (dg : n → Matrix n n ℝ) (k : n → ℝ) (a : n) : ℝ :=
  (∑ i, ∑ j, dg a i j*k i*k j)/2

theorem lowered_acceleration (dg : n → Matrix n n ℝ) (k : n → ℝ) (a : n) :
    (∑ c, ∑ b, loweredConnection dg a b c*k b*k c) =
      (metricRate dg k).mulVec k a-momentumForce dg k a := by
  have hswap : (∑ c, ∑ b, dg c a b*k b*k c) = ∑ c, ∑ b, dg b a c*k b*k c := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hrate : (metricRate dg k).mulVec k a = ∑ c, ∑ b, dg b a c*k b*k c := by
    simp only [metricRate, Matrix.mulVec, Matrix.of_apply, dotProduct, Finset.sum_mul]
  have hlast : (∑ c, ∑ b, dg a b c*k b*k c) = ∑ c, ∑ b, dg a c b*k c*k b :=
    Finset.sum_comm
  simp only [loweredConnection, div_mul_eq_mul_div, add_mul, sub_mul,
    ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib, hswap,
    hrate, momentumForce, hlast]
  ring

theorem hamiltonian_acceleration (inv : Matrix n n ℝ) (dg : n → Matrix n n ℝ)
    (k : n → ℝ) (a : n) :
    (inv.mulVec (momentumForce dg k-(metricRate dg k).mulVec k)) a =
      -(∑ c, contractedConnection inv dg k a c*k c) := by
  have hsum : (∑ c, contractedConnection inv dg k a c*k c) =
      (inv.mulVec (fun d => ∑ c, ∑ b, loweredConnection dg d b c*k b*k c)) a := by
    simp only [contractedConnection, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hsum]
  simp only [lowered_acceleration, Matrix.mulVec, dotProduct, Pi.sub_apply,
    mul_sub, Finset.sum_sub_distrib]
  ring

/-- Differentiating k=g⁻¹p in the Hamiltonian equations gives the
    Christoffel geodesic equation. The metric derivative is along the path. -/
theorem hamiltonian_tangent_derivative [DecidableEq n]
    (g : ℝ → Matrix n n ℝ) (p : ℝ → n → ℝ) (dg : n → Matrix n n ℝ) (t : ℝ)
    (hdet : (g t).det ≠ 0)
    (hg : ∀ i j, HasDerivAt (fun s => g s i j)
      (metricRate dg ((g t)⁻¹.mulVec (p t)) i j) t)
    (hp : ∀ i, HasDerivAt (fun s => p s i)
      (momentumForce dg ((g t)⁻¹.mulVec (p t)) i) t) (a : n) :
    HasDerivAt (fun s => (g s)⁻¹.mulVec (p s) a)
      (-(∑ c, contractedConnection (g t)⁻¹ dg ((g t)⁻¹.mulVec (p t)) a c*
        ((g t)⁻¹.mulVec (p t)) c)) t := by
  let k := (g t)⁻¹.mulVec (p t)
  let rate := metricRate dg k
  have hi := Curvature.inverse_derivative g rate t hg hdet
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun b _ => (hi a b).mul (hp b))
  simp only [Pi.mul_def] at h
  have hdk : (∑ b, ((-(∑ i, ∑ j, (g t)⁻¹ a i*rate i j*(g t)⁻¹ j b))*p t b+
      (g t)⁻¹ a b*momentumForce dg k b)) =
      ((g t)⁻¹.mulVec (momentumForce dg k-rate.mulVec k)) a := by
    have hfirst : (∑ b, (-(∑ i, ∑ j, (g t)⁻¹ a i*rate i j*(g t)⁻¹ j b))*p t b) =
        -((g t)⁻¹.mulVec (rate.mulVec k)) a := by
      simp only [neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
      rw [Finset.sum_comm]
      conv_lhs =>
        arg 1
        arg 2
        ext i
        rw [Finset.sum_comm]
      simp only [k, Matrix.mulVec, dotProduct, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro b _
      ring
    simp only [Matrix.mulVec_sub, Pi.sub_apply]
    simp only [Finset.sum_add_distrib]
    rw [hfirst]
    simp only [Matrix.mulVec, dotProduct]
    ring
  have hresult := hamiltonian_acceleration (g t)⁻¹ dg k a
  rw [hdk, hresult] at h
  exact h

theorem hamiltonian_pairings_constant [DecidableEq n]
    (g : ℝ → Matrix n n ℝ) (p screen : ℝ → n → ℝ)
    (dg : ℝ → n → Matrix n n ℝ)
    (hdet : ∀ t, (g t).det ≠ 0)
    (hsym : ∀ t i j, g t i j = g t j i)
    (hdsym : ∀ t e i j, dg t e i j = dg t e j i)
    (hg : ∀ t i j, HasDerivAt (fun s => g s i j)
      (metricRate (dg t) ((g t)⁻¹.mulVec (p t)) i j) t)
    (hp : ∀ t i, HasDerivAt (fun s => p s i)
      (momentumForce (dg t) ((g t)⁻¹.mulVec (p t)) i) t)
    (hscreen : ∀ t i, HasDerivAt (fun s => screen s i)
      (-(∑ c, contractedConnection (g t)⁻¹ (dg t) ((g t)⁻¹.mulVec (p t)) i c*screen t c)) t)
    (a b : ℝ) :
    let k := fun t => (g t)⁻¹.mulVec (p t)
    pairing (g a) (k a) (k a) = pairing (g b) (k b) (k b) ∧
      pairing (g a) (k a) (screen a) = pairing (g b) (k b) (screen b) := by
  let k := fun t => (g t)⁻¹.mulVec (p t)
  let C := fun t => Matrix.of (contractedConnection (g t)⁻¹ (dg t) (k t))
  have hk := fun t i => hamiltonian_tangent_derivative g p (dg t) t (hdet t) (hg t) (hp t) i
  have hmetric (t : ℝ) (i j : n) : HasDerivAt (fun s => g s i j)
      (∑ c, (C t c i*g t c j+g t i c*C t c j)) t := by
    have hcompat := contracted_metric_compatible (g t) (g t)⁻¹
      (Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hdet t))) (hsym t) (dg t) (hdsym t) (k t) i j
    dsimp only [C, Matrix.of_apply]
    rw [hcompat]
    exact hg t i j
  exact ⟨transported_pairing_constant g C k k hmetric hk hk a b,
    transported_pairing_constant g C k screen hmetric hk hscreen a b⟩

theorem hamiltonian_stationary_momentum (p : ℝ → n → ℝ)
    (dg : ℝ → n → Matrix n n ℝ) (k : ℝ → n → ℝ) (e : n)
    (hp : ∀ t, HasDerivAt (fun s => p s e) (momentumForce (dg t) (k t) e) t)
    (hstationary : ∀ t i j, dg t e i j = 0) (a b : ℝ) : p a e = p b e := by
  refine stationary_momentum_constant (fun s => p s e) ?_ a b
  intro t
  simpa only [momentumForce, hstationary, zero_mul, Finset.sum_const_zero, zero_div] using hp t

theorem zero_derivative_constant_on (f : ℝ → ℝ) (domain : Set ℝ)
    (hopen : IsOpen domain) (hconnected : IsPreconnected domain)
    (hf : ∀ t ∈ domain, HasDerivAt f 0 t) {a b : ℝ}
    (ha : a ∈ domain) (hb : b ∈ domain) : f a = f b := by
  apply hopen.is_const_of_deriv_eq_zero hconnected
    (fun t ht => (hf t ht).differentiableAt.differentiableWithinAt) _ ha hb
  intro t ht
  exact (hf t ht).deriv

end BlackHole.Transport
