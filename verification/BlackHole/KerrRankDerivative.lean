module

public import BlackHole.KerrInverse

@[expose] public section
noncomputable section

namespace BlackHole.KerrField

def rankInverse (c : ℝ) (l : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  minkowski-c • Matrix.vecMulVec (fun i => signature i*l i) (fun i => signature i*l i)

def rankDerivative (c dc : ℝ) (l dl : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  dc • Matrix.vecMulVec l l+
    c • (Matrix.vecMulVec dl l+Matrix.vecMulVec l dl)

/-- The inverse derivative of a null Kerr–Schild rank-one field stays
    rank one/two; no expanded four-index inverse sum is needed. -/
theorem rank_inverse_derivative (c dc : ℝ) (l dl : Fin 4 → ℝ)
    (hnull : dotProduct l (fun i => signature i*l i) = 0)
    (horth : dotProduct dl (fun i => signature i*l i) = 0) :
    -(rankInverse c l*rankDerivative c dc l dl*rankInverse c l) =
      -rankDerivative c dc (fun i => signature i*l i) (fun i => signature i*dl i) := by
  let v := fun i => signature i*l i
  let w := fun i => signature i*dl i
  have hn : dotProduct l v = 0 := hnull
  have ho : dotProduct dl v = 0 := horth
  have hnl : dotProduct v l = 0 := by rw [dotProduct_comm]; exact hn
  have hol : dotProduct v dl = 0 := by rw [dotProduct_comm]; exact ho
  have hl : (rankInverse c l).mulVec l = v := by
    change (minkowski-c • Matrix.vecMulVec v v).mulVec l = v
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.vecMulVec_mulVec, hnl, MulOpposite.op_zero, zero_smul, smul_zero, sub_zero]
    ext i
    simp only [minkowski, Matrix.mulVec_diagonal, v]
  have hdl : (rankInverse c l).mulVec dl = w := by
    change (minkowski-c • Matrix.vecMulVec v v).mulVec dl = w
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.vecMulVec_mulVec, hol, MulOpposite.op_zero, zero_smul, smul_zero, sub_zero]
    ext i
    simp only [minkowski, Matrix.mulVec_diagonal, w]
  have hr : Matrix.vecMul l (rankInverse c l) = v := by
    change Matrix.vecMul l (minkowski-c • Matrix.vecMulVec v v) = v
    simp only [Matrix.vecMul_sub, Matrix.vecMul_smul,
      Matrix.vecMul_vecMulVec, hn, zero_smul, smul_zero, sub_zero]
    ext i
    simp only [minkowski, Matrix.vecMul_diagonal, v]
    ring
  have hdr : Matrix.vecMul dl (rankInverse c l) = w := by
    change Matrix.vecMul dl (minkowski-c • Matrix.vecMulVec v v) = w
    simp only [Matrix.vecMul_sub, Matrix.vecMul_smul,
      Matrix.vecMul_vecMulVec, ho, zero_smul, smul_zero, sub_zero]
    ext i
    simp only [minkowski, Matrix.vecMul_diagonal, w]
    ring
  simp only [rankDerivative, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hl, hdl, hr, hdr]
  rfl

end BlackHole.KerrField
