module
public import BlackHole.KerrGeodesics
public import BlackHole.KerrCamera
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section
noncomputable section
namespace BlackHole.KerrChart

def spin (a : ℝ) : Cartesian.Space := ![0,a,0]

def equator (a r phi : ℝ) : Cartesian.Space :=
  ![r*Real.cos phi-a*Real.sin phi,0,-r*Real.sin phi-a*Real.cos phi]

theorem equator_q (a r phi : ℝ) : Cartesian.q (spin a) (equator a r phi) = r^2 := by
  simp [Cartesian.q,spin,equator,dotProduct,Fin.sum_univ_succ]
  linear_combination (r^2+a^2)*(Real.sin_sq_add_cos_sq phi)

theorem equator_b (a r phi : ℝ) : Cartesian.b (spin a) (equator a r phi) = 0 := by
  simp [Cartesian.b,spin,equator,dotProduct,Fin.sum_univ_succ]

theorem equator_radius (a r phi : ℝ) (hr : 0 < r) :
    Cartesian.radius (spin a) (equator a r phi) = r := by
  unfold Cartesian.radius Calculus.kerrRadius
  rw [equator_q,equator_b]
  have hr2 : 0 ≤ r^2 := sq_nonneg r
  simp only [zero_pow (by omega : 2 ≠ 0), mul_zero, add_zero,
    Real.sqrt_sq_eq_abs, abs_of_nonneg hr2]
  rw [add_self_div_two, Real.sqrt_sq_eq_abs, abs_of_pos hr]

theorem equator_potential (a r phi : ℝ) (hr : 0 < r) :
    Cartesian.potential 1 (spin a) (equator a r phi) = 1/r := by
  unfold Cartesian.potential
  rw [equator_radius a r phi hr,equator_b]
  unfold Calculus.kerrH
  field_simp
  ring

theorem equator_ell (a r phi : ℝ) (hr : 0 < r) :
    Cartesian.spatialEll (spin a) (equator a r phi) = ![Real.cos phi,0,-Real.sin phi] := by
  have hd : r^2+a^2 ≠ 0 := ne_of_gt (by positivity : 0 < r^2+a^2)
  ext i
  simp only [Cartesian.spatialEll,equator_radius a r phi hr,equator_b,zero_div,zero_mul]
  fin_cases i <;> simp [spin,equator,cross_apply,dotProduct,Fin.sum_univ_succ]
  all_goals field_simp
  all_goals ring

def ksVector (a r phi time omega ur : ℝ) : Fin 4 → ℝ :=
  ![time,
    Real.cos phi*ur+(-r*Real.sin phi-a*Real.cos phi)*omega,
    0,
    -Real.sin phi*ur+(-r*Real.cos phi+a*Real.sin phi)*omega]

def tangent (a r phi ut up ur : ℝ) : Fin 4 → ℝ :=
  ksVector a r phi (ut+2*r/Kerr.delta a r*ur) (up+a/Kerr.delta a r*ur) ur

theorem equator_norm (a r phi : ℝ) (hr : 0 < r) (v : Fin 4 → ℝ) :
    dotProduct v ((KerrField.metric 1 (spin a) (equator a r phi)).mulVec v) =
      -(v 0)^2+(v 1)^2+(v 2)^2+(v 3)^2+
        2/r*(v 0+Real.cos phi*v 1-Real.sin phi*v 3)^2 := by
  simp only [KerrField.metric]
  simp [Cartesian.metric,Cartesian.ell,equator_potential a r phi hr,
    equator_ell a r phi hr,Cartesian.eta,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

theorem ksVector_norm (a r phi time omega ur : ℝ) :
    let v := ksVector a r phi time omega ur;
    -(v 0)^2+(v 1)^2+(v 2)^2+(v 3)^2 =
      -time^2+ur^2-2*a*ur*omega+(r^2+a^2)*omega^2 := by
  simp [ksVector]
  linear_combination (ur^2-2*a*ur*omega+(r^2+a^2)*omega^2)*(Real.sin_sq_add_cos_sq phi)

theorem ksVector_ell (a r phi time omega ur : ℝ) :
    let v := ksVector a r phi time omega ur
    v 0+Real.cos phi*v 1-Real.sin phi*v 3 = time+ur-a*omega := by
  simp [ksVector]
  linear_combination (ur-a*omega)*(Real.sin_sq_add_cos_sq phi)

theorem equatorial_metric_pullback (a r phi ut up ur : ℝ)
    (hr : 0 < r) (hd : Kerr.delta a r ≠ 0) :
    let g := KerrField.metric 1 (spin a) (equator a r phi)
    let v := tangent a r phi ut up ur
    dotProduct v (g.mulVec v) = Kerr.equatorialNorm a r ut up ur := by
  dsimp only
  rw [equator_norm a r phi hr]
  unfold tangent
  rw [ksVector_norm,ksVector_ell]
  unfold Kerr.equatorialNorm
  field_simp
  unfold Kerr.delta
  ring

theorem equator_curve_derivative (a : ℝ) (R Phi : ℝ → ℝ) (t dr dp : ℝ)
    (hR : HasDerivAt R dr t) (hPhi : HasDerivAt Phi dp t) (i : Fin 3) :
    HasDerivAt (fun s => equator a (R s) (Phi s) i)
      (ksVector a (R t) (Phi t) 0 dp dr i.succ) t := by
  fin_cases i
  · convert ((hR.mul hPhi.cos).sub (hPhi.sin.const_mul a)) using 1
    · funext s
      simp [equator,Pi.sub_apply,Pi.mul_apply]
    · simp [ksVector]
      ring
  · simpa [equator,ksVector] using hasDerivAt_const t (0 : ℝ)
  · convert ((hR.mul hPhi.sin).neg.sub (hPhi.cos.const_mul a)) using 1
    · funext s
      simp [equator,Pi.sub_apply,Pi.mul_apply,Pi.neg_apply]
    · simp [ksVector]
      ring

def timeShift (a r : ℝ) : ℝ :=
  let s := Real.sqrt (1-a^2)
  (1+s)/s*Real.log (r-(1+s))-(1-s)/s*Real.log (r-(1-s))

def phiShift (a r : ℝ) : ℝ :=
  let s := Real.sqrt (1-a^2)
  a/(2*s)*(Real.log (r-(1+s))-Real.log (r-(1-s)))

theorem timeShift_derivative (a r : ℝ) (ha : |a| < 1)
    (hr : 1+Real.sqrt (1-a^2) < r) :
    HasDerivAt (timeShift a) (2*r/Kerr.delta a r) r := by
  let s := Real.sqrt (1-a^2)
  have hs : 0 < s := Real.sqrt_pos.mpr (by nlinarith [sq_abs a,abs_nonneg a])
  have hsq : s^2 = 1-a^2 := Real.sq_sqrt (by nlinarith [sq_abs a,abs_nonneg a])
  have h1 : r-(1+s) ≠ 0 := ne_of_gt (by linarith)
  have h2 : r-(1-s) ≠ 0 := ne_of_gt (by linarith)
  have hd : Kerr.delta a r = (r-(1+s))*(r-(1-s)) := by
    unfold Kerr.delta
    nlinarith
  have h := ((((hasDerivAt_id' r).sub_const (1+s)).log h1).const_mul ((1+s)/s)).sub
    ((((hasDerivAt_id' r).sub_const (1-s)).log h2).const_mul ((1-s)/s))
  convert h using 1
  · rfl
  · rw [hd]
    field_simp
    ring

theorem phiShift_derivative (a r : ℝ) (ha : |a| < 1)
    (hr : 1+Real.sqrt (1-a^2) < r) :
    HasDerivAt (phiShift a) (a/Kerr.delta a r) r := by
  let s := Real.sqrt (1-a^2)
  have hs : 0 < s := Real.sqrt_pos.mpr (by nlinarith [sq_abs a,abs_nonneg a])
  have hsq : s^2 = 1-a^2 := Real.sq_sqrt (by nlinarith [sq_abs a,abs_nonneg a])
  have h1 : r-(1+s) ≠ 0 := ne_of_gt (by linarith)
  have h2 : r-(1-s) ≠ 0 := ne_of_gt (by linarith)
  have hd : Kerr.delta a r = (r-(1+s))*(r-(1-s)) := by
    unfold Kerr.delta
    nlinarith
  have h := ((((hasDerivAt_id' r).sub_const (1+s)).log h1).sub
    (((hasDerivAt_id' r).sub_const (1-s)).log h2)).const_mul (a/(2*s))
  convert h using 1
  · rfl
  · rw [hd]
    field_simp
    ring

theorem cartesian_chart_derivative (a : ℝ) (T R Phi : ℝ → ℝ) (t ut up ur : ℝ)
    (ha : |a| < 1) (hr : 1+Real.sqrt (1-a^2) < R t)
    (hT : HasDerivAt T ut t) (hR : HasDerivAt R ur t) (hPhi : HasDerivAt Phi up t)
    (i : Fin 4) :
    HasDerivAt (fun s => Fin.cases (T s+timeShift a (R s))
      (equator a (R s) (Phi s+phiShift a (R s))) i)
      (tangent a (R t) (Phi t+phiShift a (R t)) ut up ur i) t := by
  have ht := hT.add ((timeShift_derivative a (R t) ha hr).comp t hR)
  have hp := hPhi.add ((phiShift_derivative a (R t) ha hr).comp t hR)
  cases i using Fin.cases with
  | zero =>
    simpa only [tangent,ksVector,Fin.cases_zero,Matrix.cons_val_zero,Pi.add_def,Function.comp_def] using ht
  | succ i =>
    change HasDerivAt (fun s => equator a (R s) (Phi s+phiShift a (R s)) i)
      (tangent a (R t) (Phi t+phiShift a (R t)) ut up ur i.succ) t
    have hcurve := equator_curve_derivative a R (fun s => Phi s+phiShift a (R s)) t ur
      (up+a/Kerr.delta a (R t)*ur) hR hp i
    fin_cases i <;> simpa [tangent,ksVector] using hcurve

theorem cylindrical_radius_sq (a r phi : ℝ) :
    (equator a r phi 0)^2+(equator a r phi 2)^2 = r^2+a^2 := by
  simp [equator]
  linear_combination (r^2+a^2)*(Real.sin_sq_add_cos_sq phi)

theorem cylindrical_radius_gt_kerr (a r phi : ℝ) (ha : a ≠ 0) (hr : 0 < r) :
    r < Real.sqrt ((equator a r phi 0)^2+(equator a r phi 2)^2) := by
  rw [cylindrical_radius_sq]
  have hs := Real.sq_sqrt (show 0 ≤ r^2+a^2 by positivity)
  have ha2 : 0 < a^2 := by simpa only [pow_two] using mul_self_pos.mpr ha
  nlinarith [Real.sqrt_nonneg (r^2+a^2)]

theorem source_radial_first_integral (a r phi E L ur : ℝ)
    (hr : 0 < r) (hd : Kerr.delta a r ≠ 0) :
    let g := KerrField.metric 1 (spin a) (equator a r phi)
    let v := tangent a r phi (Kerr.timeVelocity E L a r) (Kerr.phiVelocity E L a r) ur
    dotProduct v (g.mulVec v)+1 =
      (r^4*ur^2-Kerr.radial E L a r)/(r^2*Kerr.delta a r) := by
  dsimp only
  rw [equatorial_metric_pullback a r phi _ _ ur hr hd]
  exact Kerr.normalization_radial_identity E L a r ur (ne_of_gt hr) hd

theorem circular_coordinate_velocities (a u : ℝ) (hu : 0 < u)
    (hden : 0 < Kerr.circularDenominator a u) (hd : Kerr.delta a (u^2) ≠ 0) :
    Kerr.timeVelocity (Kerr.circularEnergy a u) (Kerr.circularMomentum a u) a (u^2) =
      (u^3+a)/Real.sqrt (Kerr.circularDenominator a u) ∧
    Kerr.phiVelocity (Kerr.circularEnergy a u) (Kerr.circularMomentum a u) a (u^2) =
      1/Real.sqrt (Kerr.circularDenominator a u) := by
  have hu0 := ne_of_gt hu
  have hs0 := ne_of_gt (Real.sqrt_pos.mpr hden)
  constructor <;> dsimp only [Kerr.timeVelocity,Kerr.phiVelocity,Kerr.circularEnergy,Kerr.circularMomentum]
  all_goals field_simp
  all_goals unfold Kerr.delta
  all_goals ring

theorem circular_angular_velocity (a u : ℝ) (hu : 0 < u)
    (hden : 0 < Kerr.circularDenominator a u) (hd : Kerr.delta a (u^2) ≠ 0)
    (ht : u^3+a ≠ 0) :
    Kerr.phiVelocity (Kerr.circularEnergy a u) (Kerr.circularMomentum a u) a (u^2) /
      Kerr.timeVelocity (Kerr.circularEnergy a u) (Kerr.circularMomentum a u) a (u^2) =
        1/(u^3+a) := by
  obtain ⟨hT,hP⟩ := circular_coordinate_velocities a u hu hden hd
  rw [hT,hP]
  have hs0 := ne_of_gt (Real.sqrt_pos.mpr hden)
  field_simp

def spinLimit (a : ℝ) : ℝ := max (-(999/1000)) (min (999/1000) a)

theorem spinLimit_eq (a : ℝ) (ha : |a| ≤ 999/1000) : spinLimit a = a := by
  obtain ⟨hl,hu⟩ := abs_le.mp ha
  simp only [spinLimit,min_eq_right hu,max_eq_right hl]

/-- Exact coordinate model; the shader's radius floor and arithmetic errors
    remain separate obligations on the exterior domain. -/
def diskRadius (pos : Cartesian.Space) (a : ℝ) (binary : Bool) : ℝ :=
  if binary then Real.sqrt ((pos 0)^2+(pos 2)^2)
  else Cartesian.radius (spin (spinLimit a)) ![pos 0,0,pos 2]

theorem diskRadius_single_equator (a r phi : ℝ) (ha : |a| ≤ 999/1000) (hr : 0 < r) :
    diskRadius (equator a r phi) a false = r := by
  simp only [diskRadius,Bool.false_eq_true,ite_false,spinLimit_eq a ha]
  have he : ![equator a r phi 0,0,equator a r phi 2] = equator a r phi := by
    ext i
    fin_cases i <;> simp [equator]
  rw [he]
  exact equator_radius a r phi hr

theorem diskRadius_height_invariant (pos : Cartesian.Space) (y a : ℝ) (binary : Bool) :
    diskRadius ![pos 0,y,pos 2] a binary = diskRadius pos a binary := by
  cases binary <;> simp [diskRadius]

theorem diskRadius_binary (pos : Cartesian.Space) (a : ℝ) :
    diskRadius pos a true = Real.sqrt ((pos 0)^2+(pos 2)^2) := by rfl

end BlackHole.KerrChart
