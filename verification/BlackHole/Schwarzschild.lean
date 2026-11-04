module

public import BlackHole.KerrCartesian
public import BlackHole.Binary

@[expose] public section
noncomputable section

namespace BlackHole.Schwarzschild

open Cartesian (Space line basis line_zero line_component_derivative)

def radius (x : Space) : ℝ := Real.sqrt (dotProduct x x)
def inversePower (x : Space) (n : ℕ) : ℝ := 1/radius x^n

theorem radius_derivative (x : Space) (e : Fin 3) (hr : 0 < radius x) :
    HasDerivAt (fun t => radius (line x e t)) (x e/radius x) 0 := by
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (line_component_derivative x e i).pow 2)
  simp only [Pi.pow_apply] at hsum
  have hq : HasDerivAt (fun t => dotProduct (line x e t) (line x e t)) (2*x e) 0 := by
    convert hsum using 1
    · funext t
      simp only [dotProduct, pow_two]
    · simp [line, basis, mul_ite]
  have hpos : 0 < dotProduct x x := (Real.sqrt_pos).mp hr
  have h := hq.sqrt (by simpa only [line_zero] using ne_of_gt hpos)
  convert h using 1
  · rfl
  · simp only [line_zero]
    unfold radius
    field_simp

theorem inversePower_derivative (x : Space) (e : Fin 3) (n : ℕ) (hr : 0 < radius x) :
    HasDerivAt (fun t => inversePower (line x e t) (n+1))
      (-((n : ℝ)+1)*x e/radius x^(n+3)) 0 := by
  have hn : radius x^(n+1) ≠ 0 := pow_ne_zero _ (ne_of_gt hr)
  have h := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).div
    ((radius_derivative x e hr).pow (n+1)) (by simpa only [Pi.pow_apply, line_zero] using hn)
  simp only [Pi.div_def, Pi.pow_apply, line_zero, Nat.cast_add, Nat.cast_one,
    Nat.add_sub_cancel] at h
  convert h using 1
  · rfl
  · field_simp [pow_add, pow_succ]
    ring

def timeTime (m : ℝ) (x : Space) : ℝ := 2*m*inversePower x 1
def timeSpace (m : ℝ) (x : Space) (i : Fin 3) : ℝ := 2*m*x i*inversePower x 2
def spaceSpace (m : ℝ) (x : Space) (i j : Fin 3) : ℝ := 2*m*x i*x j*inversePower x 3

def timeTimeD (m : ℝ) (x : Space) (e : Fin 3) : ℝ :=
  -2*m*x e*inversePower x 3
def timeSpaceD (m : ℝ) (x : Space) (e i : Fin 3) : ℝ :=
  2*m*(basis e i*inversePower x 2-2*x i*x e*inversePower x 4)
def spaceSpaceD (m : ℝ) (x : Space) (e i j : Fin 3) : ℝ :=
  2*m*((basis e i*x j+basis e j*x i)*inversePower x 3-
    3*x i*x j*x e*inversePower x 5)

def timeTimeDD (m : ℝ) (x : Space) (e f : Fin 3) : ℝ :=
  2*m*(3*x e*x f*inversePower x 5-basis f e*inversePower x 3)
def timeSpaceDD (m : ℝ) (x : Space) (e f i : Fin 3) : ℝ :=
  2*m*(-2*(basis e i*x f+basis f i*x e+basis f e*x i)*inversePower x 4+
    8*x i*x e*x f*inversePower x 6)
def spaceSpaceDD (m : ℝ) (x : Space) (e f i j : Fin 3) : ℝ :=
  2*m*((basis e i*basis f j+basis f i*basis e j)*inversePower x 3-
    3*((basis e i*x j+basis e j*x i)*x f+
      (basis f i*x j+basis f j*x i)*x e+basis f e*x i*x j)*inversePower x 5+
    15*x i*x j*x e*x f*inversePower x 7)

theorem timeTime_derivative (m : ℝ) (x : Space) (e : Fin 3) (hr : 0 < radius x) :
    HasDerivAt (fun t => timeTime m (line x e t)) (timeTimeD m x e) 0 := by
  have h := (inversePower_derivative x e 0 hr).const_mul (2*m)
  convert h using 1
  · rfl
  · simp only [timeTimeD, inversePower]
    norm_num only
    ring

theorem timeSpace_derivative (m : ℝ) (x : Space) (e i : Fin 3) (hr : 0 < radius x) :
    HasDerivAt (fun t => timeSpace m (line x e t) i) (timeSpaceD m x e i) 0 := by
  have h := ((line_component_derivative x e i).mul
    (inversePower_derivative x e 1 hr)).const_mul (2*m)
  simp only [Pi.mul_def, line_zero] at h
  convert h using 1
  · funext t
    unfold timeSpace
    ring
  · simp only [timeSpaceD, inversePower]
    norm_num only
    ring

theorem spaceSpace_derivative (m : ℝ) (x : Space) (e i j : Fin 3) (hr : 0 < radius x) :
    HasDerivAt (fun t => spaceSpace m (line x e t) i j) (spaceSpaceD m x e i j) 0 := by
  have h := (((line_component_derivative x e i).mul (line_component_derivative x e j)).mul
    (inversePower_derivative x e 2 hr)).const_mul (2*m)
  simp only [Pi.mul_def, line_zero] at h
  convert h using 1
  · funext t
    unfold spaceSpace
    ring
  · simp only [spaceSpaceD, inversePower]
    norm_num only
    ring

theorem timeTime_second_derivative (m : ℝ) (x : Space) (e f : Fin 3) (hr : 0 < radius x) :
    HasDerivAt (fun t => timeTimeD m (line x f t) e) (timeTimeDD m x e f) 0 := by
  have h := ((line_component_derivative x f e).mul
    (inversePower_derivative x f 2 hr)).const_mul (-2*m)
  simp only [Pi.mul_def, line_zero] at h
  convert h using 1
  · funext t
    unfold timeTimeD
    ring
  · simp only [timeTimeDD, inversePower]
    norm_num only
    ring

theorem timeSpace_second_derivative (m : ℝ) (x : Space) (e f i : Fin 3)
    (hr : 0 < radius x) :
    HasDerivAt (fun t => timeSpaceD m (line x f t) e i) (timeSpaceDD m x e f i) 0 := by
  have h := (((inversePower_derivative x f 1 hr).const_mul (basis e i)).sub
    ((((line_component_derivative x f i).mul (line_component_derivative x f e)).mul
      (inversePower_derivative x f 3 hr)).const_mul 2)).const_mul (2*m)
  simp only [Pi.mul_def, Pi.sub_def, line_zero] at h
  convert h using 1
  · funext t
    unfold timeSpaceD
    ring
  · simp only [timeSpaceDD, inversePower]
    norm_num only
    ring

theorem spaceSpace_second_derivative (m : ℝ) (x : Space) (e f i j : Fin 3)
    (hr : 0 < radius x) :
    HasDerivAt (fun t => spaceSpaceD m (line x f t) e i j) (spaceSpaceDD m x e f i j) 0 := by
  have hn := ((line_component_derivative x f j).const_mul (basis e i)).add
    ((line_component_derivative x f i).const_mul (basis e j))
  have hc := (((line_component_derivative x f i).mul (line_component_derivative x f j)).mul
    (line_component_derivative x f e)).mul (inversePower_derivative x f 4 hr)
  have h := ((hn.mul (inversePower_derivative x f 2 hr)).sub (hc.const_mul 3)).const_mul (2*m)
  simp only [Pi.mul_def, Pi.sub_def, Pi.add_def, line_zero] at h
  convert h using 1
  · funext t
    unfold spaceSpaceD
    ring
  · simp only [spaceSpaceDD, inversePower]
    norm_num only
    ring

def lift (a : ℝ) (b : Fin 3 → ℝ) (c : Fin 3 → Fin 3 → ℝ) (i j : Fin 4) : ℝ :=
  Fin.cases (Fin.cases a b j) (fun i => Fin.cases (b i) (c i) j) i

theorem lift_derivative (a : ℝ → ℝ) (b : ℝ → Fin 3 → ℝ)
    (c : ℝ → Fin 3 → Fin 3 → ℝ) (da : ℝ) (db : Fin 3 → ℝ)
    (dc : Fin 3 → Fin 3 → ℝ) (t : ℝ)
    (ha : HasDerivAt a da t) (hb : ∀ i, HasDerivAt (fun s => b s i) (db i) t)
    (hc : ∀ i j, HasDerivAt (fun s => c s i j) (dc i j) t) (i j : Fin 4) :
    HasDerivAt (fun s => lift (a s) (b s) (c s) i j) (lift da db dc i j) t := by
  exact Fin.cases (Fin.cases ha hb j) (fun i => Fin.cases (hb i) (hc i) j) i

def source (m : ℝ) (x : Space) : Fin 4 → Fin 4 → ℝ :=
  lift (timeTime m x) (timeSpace m x) (spaceSpace m x)
def sourceD (m : ℝ) (x : Space) (e : Fin 4) : Fin 4 → Fin 4 → ℝ :=
  Fin.cases 0 (fun e => lift (timeTimeD m x e) (timeSpaceD m x e) (spaceSpaceD m x e)) e
def sourceDD (m : ℝ) (x : Space) (e f : Fin 4) : Fin 4 → Fin 4 → ℝ :=
  Fin.cases 0 (fun e => Fin.cases 0
    (fun f => lift (timeTimeDD m x e f) (timeSpaceDD m x e f) (spaceSpaceDD m x e f)) f) e
def line4 (x : Space) (e : Fin 4) (t : ℝ) : Space :=
  Fin.cases x (fun e => line x e t) e

theorem line4_zero (x : Space) (e : Fin 4) : line4 x e 0 = x := by
  exact Fin.cases rfl (fun e => line_zero x e) e

theorem basis_symmetric (e f : Fin 3) : basis e f = basis f e := by
  simp [basis, eq_comm]

theorem sourceDD_symmetric (m : ℝ) (x : Space) (e f i j : Fin 4) :
    sourceDD m x e f i j = sourceDD m x f e i j := by
  cases e using Fin.cases <;> cases f using Fin.cases <;>
    cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp only [sourceDD, lift, Fin.cases_zero, Fin.cases_succ, Pi.zero_apply] <;>
    simp only [timeTimeDD, timeSpaceDD, spaceSpaceDD, basis_symmetric] <;> ring

theorem source_derivative (m : ℝ) (x : Space) (e i j : Fin 4) (hr : 0 < radius x) :
    HasDerivAt (fun t => source m (line4 x e t) i j) (sourceD m x e i j) 0 := by
  refine Fin.cases ?_ (fun d => ?_) e
  · exact hasDerivAt_const (0 : ℝ) (source m x i j)
  · exact lift_derivative (fun t => timeTime m (line x d t))
      (fun t => timeSpace m (line x d t)) (fun t => spaceSpace m (line x d t))
      _ _ _ 0 (timeTime_derivative m x d hr) (fun i => timeSpace_derivative m x d i hr)
      (fun i j => spaceSpace_derivative m x d i j hr) i j

/-- All second partial derivatives, including time components, of the exact
    nonspinning Kerr-Schild field. The only excluded point is r=0. -/
theorem source_second_derivative (m : ℝ) (x : Space) (e f i j : Fin 4) (hr : 0 < radius x) :
    HasDerivAt (fun t => sourceD m (line4 x f t) e i j) (sourceDD m x e f i j) 0 := by
  refine Fin.cases ?_ (fun e => ?_) e
  · exact hasDerivAt_const 0 0
  · refine Fin.cases ?_ (fun f => ?_) f
    · exact hasDerivAt_const (0 : ℝ) (sourceD m x e.succ i j)
    · exact lift_derivative (fun t => timeTimeD m (line x f t) e)
        (fun t => timeSpaceD m (line x f t) e) (fun t => spaceSpaceD m (line x f t) e)
        _ _ _ 0 (timeTime_second_derivative m x e f hr)
        (fun i => timeSpace_second_derivative m x e f i hr)
        (fun i j => spaceSpace_second_derivative m x e f i j hr) i j

theorem radius_eq_kerr (x : Space) : Cartesian.radius 0 x = radius x := by
  have hxx : 0 ≤ dotProduct x x := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  simp only [Cartesian.radius, Calculus.kerrRadius, Cartesian.q, Cartesian.b,
    zero_dotProduct, dotProduct_zero, sub_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
    add_zero, Real.sqrt_sq hxx]
  congr 1
  ring

theorem source_eq_kerr (m : ℝ) (x : Space) (i j : Fin 4) (hr : 0 < radius x) :
    Cartesian.metric m 0 x i j = Cartesian.eta i j+source m x i j := by
  have hH : Cartesian.potential m 0 x = m/radius x := by
    simp only [Cartesian.potential, Calculus.kerrH, radius_eq_kerr, Cartesian.b,
      zero_dotProduct, zero_pow (by decide : 2 ≠ 0), add_zero]
    field_simp
  have hell (i : Fin 3) : Cartesian.spatialEll 0 x i = x i/radius x := by
    simp only [Cartesian.spatialEll, radius_eq_kerr, crossProduct, map_zero,
      LinearMap.zero_apply, Pi.zero_apply, sub_zero, Cartesian.b, zero_dotProduct,
      zero_div, zero_mul, add_zero, dotProduct_zero]
    field_simp
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Cartesian.metric, Cartesian.ell, source, lift, Fin.cases_zero,
        timeTime, inversePower, hH]
      ring
    · simp only [Cartesian.metric, Cartesian.ell, source, lift, Fin.cases_zero,
        Fin.cases_succ, hH, hell, timeSpace, inversePower]
      ring
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Cartesian.metric, Cartesian.ell, source, lift, Fin.cases_zero,
        Fin.cases_succ, hH, hell, timeSpace, inversePower]
      ring
    · simp only [Cartesian.metric, Cartesian.ell, source, lift, Fin.cases_succ,
        hH, hell, spaceSpace, inversePower]
      ring

def axis (s : ℝ) : Space := ![s, 0, 0]

theorem radius_axis (s : ℝ) : radius (axis s) = |s| := by
  simp [radius, axis, dotProduct, Fin.sum_univ_succ, ← pow_two]
  exact Real.sqrt_sq_eq_abs s

theorem source_cast (m s : ℚ) (i j : Fin 4) :
    source (m : ℝ) (axis (s : ℝ)) i j = (Binary.source m s i j : ℝ) := by
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp only [source, lift, Fin.cases_zero, Fin.cases_succ] <;>
    (repeat' (rename_i k; fin_cases k)) <;>
    simp [timeTime, timeSpace, spaceSpace, inversePower, radius, axis,
      dotProduct, Fin.sum_univ_succ, ← pow_two, Real.sqrt_sq_eq_abs,
      Binary.source, Binary.offset] <;>
    ring_nf

set_option maxHeartbeats 800000 in
theorem sourceD_cast (m s : ℚ) (e i j : Fin 4) :
    sourceD (m : ℝ) (axis (s : ℝ)) e i j = (Binary.sourceD m s e i j : ℝ) := by
  cases e using Fin.cases <;> cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp only [sourceD, lift, Fin.cases_zero, Fin.cases_succ] <;>
    (repeat' (rename_i k; fin_cases k)) <;>
    simp [timeTimeD, timeSpaceD, spaceSpaceD, inversePower, radius, axis,
      dotProduct, Fin.sum_univ_succ, ← pow_two, Real.sqrt_sq_eq_abs,
      basis, Binary.sourceD, Binary.offset, Binary.delta] <;>
    ring_nf <;> simp

set_option maxHeartbeats 2000000 in
theorem sourceDD_cast (m s : ℚ) (e f i j : Fin 4) :
    sourceDD (m : ℝ) (axis (s : ℝ)) e f i j = (Binary.sourceDD m s e f i j : ℝ) := by
  cases e using Fin.cases <;> cases f using Fin.cases <;>
    cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp only [sourceDD, lift, Fin.cases_zero, Fin.cases_succ] <;>
    (repeat' (rename_i k; fin_cases k)) <;>
    simp [timeTimeDD, timeSpaceDD, spaceSpaceDD, inversePower, radius, axis,
      dotProduct, Fin.sum_univ_succ, ← pow_two, Real.sqrt_sq_eq_abs,
      basis, Binary.sourceDD, Binary.offset, Binary.delta] <;>
    ring_nf <;> simp

end BlackHole.Schwarzschild
