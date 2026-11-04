module

public import BlackHole.Frames
public import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FinCases

@[expose] public section
noncomputable section

namespace BlackHole.ADM

abbrev Spatial := Fin 3
abbrev Index := Fin 4

def shift (inv : Matrix Index Index ℝ) (i : Spatial) : ℝ := -inv i.succ 0/inv 0 0
def lapse (inv : Matrix Index Index ℝ) : ℝ := 1/Real.sqrt (-inv 0 0)
def spatial (g : Matrix Index Index ℝ) (v w : Spatial → ℝ) : ℝ :=
  ∑ i, ∑ j, g i.succ j.succ*v i*w j
def norm (g : Matrix Index Index ℝ) (t : ℝ) (v : Spatial → ℝ) : ℝ :=
  g 0 0*t^2+2*t*(∑ i, g 0 i.succ*v i)+spatial g v v

theorem shift_equations (g inv : Matrix Index Index ℝ) (hinv : g*inv = 1)
    (h00 : inv 0 0 ≠ 0) :
    (∀ i : Spatial, (∑ j : Spatial, g i.succ j.succ*shift inv j) = g i.succ 0) ∧
    g 0 0-(∑ j : Spatial, g 0 j.succ*shift inv j) = 1/inv 0 0 := by
  have h (i : Index) := congrArg (fun m : Matrix Index Index ℝ => m i 0) hinv
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] at h
  constructor
  · intro i
    have hi := h i.succ
    simp only [Fin.succ_ne_zero] at hi
    simp [Fin.sum_univ_succ] at hi ⊢
    unfold shift
    field_simp
    norm_num at hi ⊢
    linarith
  · have hi := h 0
    simp only [ite_eq_left] at hi
    simp [Fin.sum_univ_succ] at hi ⊢
    unfold shift
    field_simp
    norm_num at hi ⊢
    linarith

theorem lapse_identity (inv : Matrix Index Index ℝ) (h00 : inv 0 0 < 0) :
    0 < lapse inv ∧ lapse inv^2 = -1/inv 0 0 := by
  have hp : 0 < -inv 0 0 := neg_pos.mpr h00
  have hs := Real.sq_sqrt (le_of_lt hp)
  have hn := ne_of_gt (Real.sqrt_pos.mpr hp)
  constructor
  · exact div_pos (by norm_num) (Real.sqrt_pos.mpr hp)
  · unfold lapse
    rw [div_pow, one_pow, hs]
    ring

/-- The inverse-metric column used by init_ray really gives the ADM
    decomposition, assuming an exact inverse, symmetry and g^{00}<0. -/
theorem metric_decomposition (g inv : Matrix Index Index ℝ)
    (hinv : g*inv = 1) (hsym : ∀ i j, g i j = g j i) (h00 : inv 0 0 < 0)
    (t : ℝ) (v : Spatial → ℝ) :
    norm g t v = -(lapse inv)^2*t^2+
      spatial g (v+t • shift inv) (v+t • shift inv) := by
  obtain ⟨hshift, htime⟩ := shift_equations g inv hinv (ne_of_lt h00)
  have hlapse := (lapse_identity inv h00).2
  have hcross (v : Spatial → ℝ) : (∑ i, ∑ j, g i.succ j.succ*v i*shift inv j) =
      ∑ i, g 0 i.succ*v i := by
    apply Finset.sum_congr rfl
    intro i _
    simp_rw [mul_right_comm _ (v i), ← Finset.sum_mul, hshift i, hsym i.succ 0]
  have hcross' : (∑ i, ∑ j, g i.succ j.succ*shift inv i*v j) =
      ∑ i, g 0 i.succ*v i := by
    rw [Finset.sum_comm]
    convert hcross v using 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j.succ i.succ]
    ring
  have hbeta : spatial g (shift inv) (shift inv) = g 0 0+(lapse inv)^2 := by
    unfold spatial
    rw [hcross]
    linear_combination -htime-hlapse
  unfold norm spatial at *
  have hc := hcross v
  simp [Fin.sum_univ_succ] at *
  linear_combination -t^2*hbeta-t*hc-t*hcross'

theorem initialized_null (g inv : Matrix Index Index ℝ)
    (hinv : g*inv = 1) (hsym : ∀ i j, g i j = g j i) (h00 : inv 0 0 < 0)
    (direction : Spatial → ℝ) (hdir : spatial g direction direction = 1) :
    norm g (-1/lapse inv) (direction+(1/lapse inv) • shift inv) = 0 := by
  have ha := (lapse_identity inv h00).1
  rw [metric_decomposition g inv hinv hsym h00]
  have heq : direction+(1/lapse inv) • shift inv+(-1/lapse inv) • shift inv = direction := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq, hdir]
  field_simp
  norm_num

def observer (inv : Matrix Index Index ℝ) : Index → ℝ :=
  (-lapse inv) • (fun i => inv i 0)

def pastTangent (inv : Matrix Index Index ℝ) (direction : Spatial → ℝ) : Index → ℝ :=
  Fin.cases (-1/lapse inv) (fun i => direction i+shift inv i/lapse inv)

theorem observer_covector (g inv : Matrix Index Index ℝ) (hinv : g*inv = 1) :
    g.mulVec (observer inv) = (-lapse inv) • Pi.single 0 1 := by
  have hcol : g.mulVec (fun i => inv i 0) = Pi.single 0 1 := by
    ext i
    have h := congrArg (fun m : Matrix Index Index ℝ => m i 0) hinv
    by_cases hi : i = 0
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply, hi] using h
    · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply, hi] using h
  rw [observer, Matrix.mulVec_smul, hcol]

theorem observer_unit_timelike (g inv : Matrix Index Index ℝ)
    (hinv : g*inv = 1) (h00 : inv 0 0 < 0) :
    dotProduct (observer inv) (g.mulVec (observer inv)) = -1 := by
  have hl := (lapse_identity inv h00).2
  rw [observer_covector g inv hinv, dotProduct_smul, dotProduct_single]
  simp only [observer, Pi.smul_apply, smul_eq_mul, mul_one]
  have hn := ne_of_lt h00
  field_simp at hl ⊢
  nlinarith

theorem observer_future (inv : Matrix Index Index ℝ) (h00 : inv 0 0 < 0) :
    0 < observer inv 0 := by
  have hl := (lapse_identity inv h00).1
  change 0 < -lapse inv*inv 0 0
  exact mul_pos_of_neg_of_neg (by linarith) h00

theorem initialized_energy (g inv : Matrix Index Index ℝ)
    (hinv : g*inv = 1) (hsym : ∀ i j, g i j = g j i) (h00 : inv 0 0 < 0)
    (direction : Spatial → ℝ) :
    dotProduct (g.mulVec (pastTangent inv direction)) (observer inv) = 1 := by
  have htranspose : g.transpose = g := by
    ext i j
    exact hsym j i
  have hrow : Matrix.vecMul (observer inv) g = g.mulVec (observer inv) := by
    calc
      _ = Matrix.vecMul (observer inv) g.transpose := by rw [htranspose]
      _ = g.mulVec (observer inv) := Matrix.vecMul_transpose g (observer inv)
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, hrow, observer_covector g inv hinv,
    smul_dotProduct, dotProduct_comm, dotProduct_single]
  simp only [pastTangent, Fin.cases_zero, smul_eq_mul, mul_one]
  have hn := ne_of_gt (lapse_identity inv h00).1
  field_simp

end BlackHole.ADM
