module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! The CUDA renderer's structured geodesic right-hand side (checklist P1.3). Each
Kerr–Schild source adds `∂ᵢg = 2 ∂ᵢh ℓℓ + 2h (∂ᵢℓ ℓ + ℓ ∂ᵢℓ)` with covariant
`ℓ = (1, ℓ⃗)` and `∂ᵢℓ = (0, ∂ᵢℓ⃗)`. `geodesic_rhs` forms only the contractions of
these with `k = g⁻¹p` and the screen vector `f`; `force_eq` and `transport_eq` show they
equal the contractions of the matrices in `geodesic_rhs_matrix`, whose rounding
`CudaGeodesic` bounds. Both sides are linear in `∂g`, so the identities hold for a sum of
sources. The rounding of the structured program itself is not bounded here: the GPU test
`structured_geodesic_rhs_matches_the_matrix_form` compares it with the bounded form. -/

@[expose] public section

namespace BlackHole.CudaStructuredRhs

open Matrix

/-- One source's `∂ᵢg`, with `J i j = ∂ᵢ ℓⱼ`. -/
def dg (h : ℝ) (dh l : Fin 3 → ℝ) (J : Fin 3 → Fin 3 → ℝ) (i : Fin 3) (a b : Fin 4) : ℝ :=
  2 * dh i * vecCons 1 l a * vecCons 1 l b +
    2 * h * (vecCons 0 (J i) a * vecCons 1 l b + vecCons 1 l a * vecCons 0 (J i) b)

def mv (M : Fin 4 → Fin 4 → ℝ) (x : Fin 4 → ℝ) (a : Fin 4) : ℝ := ∑ b, M a b * x b
def dot4 (x y : Fin 4 → ℝ) : ℝ := ∑ a, x a * y a
def dot3 (x y : Fin 3 → ℝ) : ℝ := ∑ a, x a * y a
def spatial (x : Fin 4 → ℝ) (e : Fin 3) : ℝ := x e.succ

/-- `geodesic_rhs_matrix`'s `k · ∂ᵢg · k`. -/
def forceMatrix (M : Fin 3 → Fin 4 → Fin 4 → ℝ) (k : Fin 4 → ℝ) (i : Fin 3) : ℝ :=
  dot4 k (mv (M i) k)

/-- `geodesic_rhs_matrix`'s `Σᵢ (kⁱ ∂ᵢg f + fⁱ ∂ᵢg k) - (0, k · ∂ⱼg · f)`. -/
def transportMatrix (M : Fin 3 → Fin 4 → Fin 4 → ℝ) (k f : Fin 4 → ℝ) (a : Fin 4) : ℝ :=
  ∑ i, (k i.succ * mv (M i) f a + f i.succ * mv (M i) k a) -
    vecCons 0 (fun e => dot4 k (mv (M e) f)) a

/-- `along v = Σⱼ vⱼ ∂ⱼℓ⃗`. -/
def along (J : Fin 3 → Fin 3 → ℝ) (v : Fin 3 → ℝ) (e : Fin 3) : ℝ := ∑ j, v j * J j e

/-- `gradient v = ∇(ℓ⃗ · v)` at fixed `v`. -/
def gradient (J : Fin 3 → Fin 3 → ℝ) (v : Fin 3 → ℝ) (i : Fin 3) : ℝ := ∑ j, J i j * v j

/-- `geodesic_rhs`'s `force` term for one source. -/
def forceStructured (h : ℝ) (dh l : Fin 3 → ℝ) (J : Fin 3 → Fin 3 → ℝ) (k : Fin 4 → ℝ)
    (i : Fin 3) : ℝ :=
  let u := k 0 + dot3 l (spatial k)
  2 * u * u * dh i + 2 * (2 * h) * u * gradient J (spatial k) i

/-- `geodesic_rhs`'s `transport` term for one source. -/
def transportStructured (h : ℝ) (dh l : Fin 3 → ℝ) (J : Fin 3 → Fin 3 → ℝ)
    (k f : Fin 4 → ℝ) : Fin 4 → ℝ :=
  let ks := spatial k
  let fs := spatial f
  let u := k 0 + dot3 l ks
  let w := f 0 + dot3 l fs
  let onL := 2 * (w * dot3 dh ks + u * dot3 dh fs +
    h * (dot3 fs (along J ks) + dot3 ks (along J fs)))
  vecCons onL fun e => onL * l e + 2 * h * (w * along J ks e + u * along J fs e) -
    (2 * u * w * dh e + 2 * h * (w * gradient J ks e + u * gradient J fs e))

theorem force_eq (h : ℝ) (dh l : Fin 3 → ℝ) (J : Fin 3 → Fin 3 → ℝ) (k : Fin 4 → ℝ)
    (i : Fin 3) : forceMatrix (dg h dh l J) k i = forceStructured h dh l J k i := by
  simp only [forceMatrix, forceStructured, dg, mv, dot4, dot3, gradient, spatial,
    Fin.sum_univ_succ, Fin.sum_univ_zero, cons_val_zero, cons_val_succ]
  ring

theorem transport_eq (h : ℝ) (dh l : Fin 3 → ℝ) (J : Fin 3 → Fin 3 → ℝ) (k f : Fin 4 → ℝ)
    (a : Fin 4) :
    transportMatrix (dg h dh l J) k f a = transportStructured h dh l J k f a := by
  cases a using Fin.cases with
  | zero =>
    simp only [transportMatrix, transportStructured, dg, mv, dot4, dot3, along, spatial,
      Fin.sum_univ_succ, Fin.sum_univ_zero, cons_val_zero, cons_val_succ]
    ring
  | succ e =>
    simp only [transportMatrix, transportStructured, dg, mv, dot4, dot3, along, gradient,
      spatial, Fin.sum_univ_succ, Fin.sum_univ_zero, cons_val_zero, cons_val_succ]
    ring

end BlackHole.CudaStructuredRhs
