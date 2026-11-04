module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

namespace BlackHole.Curvature

variable {n R S : Type*} [Fintype n] [Field R] [Field S]

def inverseD (inv : Matrix n n R) (dg : n → Matrix n n R) (e a b : n) : R :=
  -(∑ i, ∑ j, inv a i*dg e i j*inv j b)

def christoffel (inv : Matrix n n R) (dg : n → Matrix n n R) (a b c : n) : R :=
  (∑ d, inv a d*(dg b d c+dg c d b-dg d b c))/2

def christoffelD (inv : Matrix n n R) (dg : n → Matrix n n R)
    (ddg : n → n → Matrix n n R) (e a b c : n) : R :=
  (∑ d, (inverseD inv dg e a d*(dg b d c+dg c d b-dg d b c)+
    inv a d*(ddg e b d c+ddg e c d b-ddg e d b c)))/2

def ricci (inv : Matrix n n R) (dg : n → Matrix n n R)
    (ddg : n → n → Matrix n n R) (b c : n) : R :=
  ∑ a, (christoffelD inv dg ddg a a b c-christoffelD inv dg ddg c a b a+
    ∑ d, (christoffel inv dg a a d*christoffel inv dg d b c-
      christoffel inv dg a c d*christoffel inv dg d b a))

def riemann (inv : Matrix n n R) (dg : n → Matrix n n R)
    (ddg : n → n → Matrix n n R) (a b c d : n) : R :=
  christoffelD inv dg ddg c a b d-christoffelD inv dg ddg d a b c+
    ∑ e, (christoffel inv dg a c e*christoffel inv dg e b d-
      christoffel inv dg a d e*christoffel inv dg e b c)

theorem ricci_eq_riemann_contraction (inv : Matrix n n R) (dg : n → Matrix n n R)
    (ddg : n → n → Matrix n n R) (b c : n) :
    ricci inv dg ddg b c = ∑ a, riemann inv dg ddg a b a c := rfl

theorem riemann_skew (inv : Matrix n n R) (dg : n → Matrix n n R)
    (ddg : n → n → Matrix n n R) (a b c d : n) :
    riemann inv dg ddg a b c d = -riemann inv dg ddg a b d c := by
  simp only [riemann, Finset.sum_sub_distrib]
  ring

theorem inverseD_map (f : R →+* S) (inv : Matrix n n R) (dg : n → Matrix n n R) (e a b : n) :
    f (inverseD inv dg e a b) =
      inverseD (fun i j => f (inv i j)) (fun e i j => f (dg e i j)) e a b := by
  simp [inverseD]

theorem christoffel_map (f : R →+* S) (inv : Matrix n n R) (dg : n → Matrix n n R) (a b c : n) :
    f (christoffel inv dg a b c) =
      christoffel (fun i j => f (inv i j)) (fun e i j => f (dg e i j)) a b c := by
  simp [christoffel, map_ofNat]

theorem christoffelD_map (f : R →+* S) (inv : Matrix n n R) (dg : n → Matrix n n R)
    (ddg : n → n → Matrix n n R) (e a b c : n) :
    f (christoffelD inv dg ddg e a b c) =
      christoffelD (fun i j => f (inv i j)) (fun e i j => f (dg e i j))
        (fun e f_ i j => f (ddg e f_ i j)) e a b c := by
  simp [christoffelD, inverseD_map, map_ofNat]

theorem ricci_map (f : R →+* S) (inv : Matrix n n R) (dg : n → Matrix n n R)
    (ddg : n → n → Matrix n n R) (b c : n) :
    f (ricci inv dg ddg b c) =
      ricci (fun i j => f (inv i j)) (fun e i j => f (dg e i j))
        (fun e f_ i j => f (ddg e f_ i j)) b c := by
  simp [ricci, christoffel_map, christoffelD_map]

/-- The derivative used in the Ricci contraction is obtained by the product
    rule from the Christoffel formula and the metric's actual first/second jets. -/
theorem christoffel_derivative (inv : ℝ → Matrix n n ℝ) (dg : ℝ → n → Matrix n n ℝ)
    (ddg : n → n → Matrix n n ℝ) (t : ℝ) (e a b c : n)
    (hi : ∀ i j, HasDerivAt (fun s => inv s i j) (inverseD (inv t) (dg t) e i j) t)
    (hd : ∀ d i j, HasDerivAt (fun s => dg s d i j) (ddg e d i j) t) :
    HasDerivAt (fun s => christoffel (inv s) (dg s) a b c)
      (christoffelD (inv t) (dg t) ddg e a b c) t := by
  have h := (HasDerivAt.fun_sum (u := Finset.univ) (fun d _ =>
    (hi a d).mul (((hd b d c).add (hd c d b)).sub (hd d b c)))).div_const 2
  simp only [Pi.add_def, Pi.sub_def, Pi.mul_def] at h
  exact h

end BlackHole.Curvature
