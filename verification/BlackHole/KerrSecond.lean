module

public import BlackHole.KerrCartesian

@[expose] public section
noncomputable section

namespace BlackHole.Cartesian

def radiusDD (a x : Space) (e f : Fin 3) : ℝ :=
  ((radiusD a x f*x e+radius a x*basis f e+
      (a f/radius a x-b a x*radiusD a x f/radius a x^2)*a e)*(2*radius a x^2-q a x)-
    (radius a x*x e+(b a x/radius a x)*a e)*(4*radius a x*radiusD a x f-2*x f))/
      (2*radius a x^2-q a x)^2

def hDen (a x : Space) : ℝ := radius a x^4+b a x^2
def hDenD (a x : Space) (e : Fin 3) : ℝ := 4*radius a x^3*radiusD a x e+2*b a x*a e
def hDenDD (a x : Space) (e f : Fin 3) : ℝ :=
  12*radius a x^2*radiusD a x e*radiusD a x f+4*radius a x^3*radiusDD a x e f+2*a e*a f
def hLogD (a x : Space) (e : Fin 3) : ℝ := 3*radiusD a x e/radius a x-hDenD a x e/hDen a x
def hLogDD (a x : Space) (e f : Fin 3) : ℝ :=
  3*(radiusDD a x e f/radius a x-radiusD a x e*radiusD a x f/radius a x^2)-
    hDenDD a x e f/hDen a x+hDenD a x e*hDenD a x f/hDen a x^2
def potentialDD (mass : ℝ) (a x : Space) (e f : Fin 3) : ℝ :=
  potentialD mass a x f*hLogD a x e+potential mass a x*hLogDD a x e f

theorem radiusD_derivative (a x : Space) (e f : Fin 3)
    (hdisc : 0 < q a x^2+4*b a x^2)
    (hroot : 0 < (q a x+Real.sqrt (q a x^2+4*b a x^2))/2) :
    HasDerivAt (fun t => radiusD a (line x f t) e) (radiusDD a x e f) 0 := by
  have hr := radius_derivative a x f hdisc hroot
  have hb := b_derivative a x f
  have hq := q_derivative a x f
  have hr0 : radius a x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hroot)
  have hs := Real.sq_sqrt (le_of_lt hroot)
  have hden : 2*radius a x^2-q a x = Real.sqrt (q a x^2+4*b a x^2) := by
    unfold radius Calculus.kerrRadius
    nlinarith
  have hd : 2*radius a x^2-q a x ≠ 0 := by
    rw [hden]
    exact ne_of_gt (Real.sqrt_pos.mpr hdisc)
  have hn := (hr.mul (line_component_derivative x f e)).add
    ((hb.div hr (by simpa only [line_zero] using hr0)).mul_const (a e))
  have h := hn.div (((hr.pow 2).const_mul 2).sub hq)
    (by simpa only [Pi.sub_apply, Pi.pow_apply, line_zero] using hd)
  simp only [Pi.add_def, Pi.sub_def, Pi.mul_def, Pi.div_def, Pi.pow_apply, line_zero,
    Nat.cast_ofNat, Nat.reduceSub, pow_one] at h
  convert h using 1
  · rfl
  · unfold radiusDD
    field_simp
    ring

theorem hDen_derivative (a x : Space) (f : Fin 3)
    (hdisc : 0 < q a x^2+4*b a x^2)
    (hroot : 0 < (q a x+Real.sqrt (q a x^2+4*b a x^2))/2) :
    HasDerivAt (fun t => hDen a (line x f t)) (hDenD a x f) 0 := by
  have h := ((radius_derivative a x f hdisc hroot).pow 4).add ((b_derivative a x f).pow 2)
  simp only [Pi.add_def, Pi.pow_apply, line_zero, Nat.cast_ofNat, Nat.reduceSub, pow_one] at h
  convert h using 1
  · rfl
  · unfold hDenD
    ring

theorem hDenD_derivative (a x : Space) (e f : Fin 3)
    (hdisc : 0 < q a x^2+4*b a x^2)
    (hroot : 0 < (q a x+Real.sqrt (q a x^2+4*b a x^2))/2) :
    HasDerivAt (fun t => hDenD a (line x f t) e) (hDenDD a x e f) 0 := by
  have h := ((((radius_derivative a x f hdisc hroot).pow 3).mul
    (radiusD_derivative a x e f hdisc hroot)).const_mul 4).add
      ((b_derivative a x f).mul_const (2*a e))
  simp only [Pi.add_def, Pi.mul_def, Pi.pow_apply, line_zero, Nat.cast_ofNat, Nat.reduceSub] at h
  convert h using 1
  · funext t
    unfold hDenD
    ring
  · unfold hDenDD
    ring

theorem hLogD_derivative (a x : Space) (e f : Fin 3)
    (hdisc : 0 < q a x^2+4*b a x^2)
    (hroot : 0 < (q a x+Real.sqrt (q a x^2+4*b a x^2))/2) :
    HasDerivAt (fun t => hLogD a (line x f t) e) (hLogDD a x e f) 0 := by
  have hr := radius_derivative a x f hdisc hroot
  have hr0 : radius a x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hroot)
  have hd : hDen a x ≠ 0 := by
    have hp : 0 < radius a x := Real.sqrt_pos.mpr hroot
    unfold hDen
    positivity
  have h := (((radiusD_derivative a x e f hdisc hroot).div hr
    (by simpa only [line_zero] using hr0)).const_mul 3).sub
      ((hDenD_derivative a x e f hdisc hroot).div (hDen_derivative a x f hdisc hroot)
        (by simpa only [line_zero] using hd))
  simp only [Pi.sub_def, Pi.div_def, line_zero] at h
  convert h using 1
  · funext t
    unfold hLogD
    ring
  · unfold hLogDD
    field_simp
    ring

theorem potentialD_derivative (mass : ℝ) (a x : Space) (e f : Fin 3)
    (hdisc : 0 < q a x^2+4*b a x^2)
    (hroot : 0 < (q a x+Real.sqrt (q a x^2+4*b a x^2))/2) :
    HasDerivAt (fun t => potentialD mass a (line x f t) e) (potentialDD mass a x e f) 0 := by
  have h := (potential_derivative mass a x f hdisc hroot).mul (hLogD_derivative a x e f hdisc hroot)
  simp only [Pi.mul_def, line_zero] at h
  exact h

def ellNumeratorD (a x : Space) (e i : Fin 3) : ℝ :=
  radiusD a x e*x i+radius a x*basis e i-crossProduct a (basis e) i+
    (a e/radius a x-b a x*radiusD a x e/radius a x^2)*a i
def ellNumeratorDD (a x : Space) (e f i : Fin 3) : ℝ :=
  radiusDD a x e f*x i+radiusD a x e*basis f i+radiusD a x f*basis e i+
    ((-a e*radiusD a x f-a f*radiusD a x e-b a x*radiusDD a x e f)/radius a x^2+
      2*b a x*radiusD a x e*radiusD a x f/radius a x^3)*a i
def ellDen (a x : Space) : ℝ := radius a x^2+dotProduct a a
def ellDenD (a x : Space) (e : Fin 3) : ℝ := 2*radius a x*radiusD a x e
def ellDenDD (a x : Space) (e f : Fin 3) : ℝ :=
  2*radiusD a x f*radiusD a x e+2*radius a x*radiusDD a x e f
def spatialEllDD (a x : Space) (e f i : Fin 3) : ℝ :=
  ((ellNumeratorDD a x e f i-spatialEllD a x f i*ellDenD a x e-
      spatialEll a x i*ellDenDD a x e f)*ellDen a x-
    (ellNumeratorD a x e i-spatialEll a x i*ellDenD a x e)*ellDenD a x f)/ellDen a x^2
def ellDD (a x : Space) (e f : Fin 3) : Fin 4 → ℝ := Fin.cases 0 (spatialEllDD a x e f)

theorem ellNumeratorD_derivative (a x : Space) (e f i : Fin 3)
    (hdisc : 0 < q a x^2+4*b a x^2)
    (hroot : 0 < (q a x+Real.sqrt (q a x^2+4*b a x^2))/2) :
    HasDerivAt (fun t => ellNumeratorD a (line x f t) e i) (ellNumeratorDD a x e f i) 0 := by
  have hr := radius_derivative a x f hdisc hroot
  have hb := b_derivative a x f
  have he := radiusD_derivative a x e f hdisc hroot
  have hr0 : radius a x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hroot)
  have hfirst := (hasDerivAt_const (0 : ℝ) (a e)).div hr (by simpa only [line_zero] using hr0)
  have hsecond := (hb.mul he).div (hr.pow 2)
    (by simpa only [Pi.pow_apply, line_zero] using pow_ne_zero 2 hr0)
  have h := (((he.mul (line_component_derivative x f i)).add (hr.mul_const (basis e i))).sub_const
    (crossProduct a (basis e) i)).add ((hfirst.sub hsecond).mul_const (a i))
  simp only [Pi.add_def, Pi.sub_def, Pi.mul_def, Pi.div_def, Pi.pow_apply, line_zero,
    Nat.cast_ofNat, Nat.reduceSub, pow_one] at h
  convert h using 1
  · rfl
  · unfold ellNumeratorDD
    field_simp
    ring

theorem spatialEllD_derivative (a x : Space) (e f i : Fin 3)
    (hdisc : 0 < q a x^2+4*b a x^2)
    (hroot : 0 < (q a x+Real.sqrt (q a x^2+4*b a x^2))/2) :
    HasDerivAt (fun t => spatialEllD a (line x f t) e i) (spatialEllDD a x e f i) 0 := by
  have hr := radius_derivative a x f hdisc hroot
  have he := radiusD_derivative a x e f hdisc hroot
  have hl := spatialEll_derivative a x f i hdisc hroot
  have hden : HasDerivAt (fun t => ellDen a (line x f t)) (ellDenD a x f) 0 := by
    have h := (hr.pow 2).add_const (dotProduct a a)
    simp only [Pi.pow_apply, line_zero, Nat.cast_ofNat, Nat.reduceSub, pow_one] at h
    convert h using 1
    · rfl
    · unfold ellDenD
      ring
  have hde : HasDerivAt (fun t => ellDenD a (line x f t) e) (ellDenDD a x e f) 0 := by
    have h := (hr.mul he).const_mul 2
    simp only [Pi.mul_def, line_zero] at h
    convert h using 1
    · funext t
      unfold ellDenD
      ring
    · unfold ellDenDD
      ring
  have hd : ellDen a x ≠ 0 := by
    have hp : 0 < radius a x := Real.sqrt_pos.mpr hroot
    have haa : 0 ≤ dotProduct a a := Finset.sum_nonneg (fun k _ => mul_self_nonneg _)
    unfold ellDen
    positivity
  have h := ((ellNumeratorD_derivative a x e f i hdisc hroot).sub (hl.mul hde)).div hden
    (by simpa only [line_zero] using hd)
  simp only [Pi.sub_def, Pi.mul_def, Pi.div_def, line_zero] at h
  convert h using 1
  · funext t
    unfold spatialEllD ellNumeratorD ellDenD ellDen
    ring
  · unfold spatialEllDD
    ring

theorem ellD_derivative (a x : Space) (e f : Fin 3) (i : Fin 4)
    (hdisc : 0 < q a x^2+4*b a x^2)
    (hroot : 0 < (q a x+Real.sqrt (q a x^2+4*b a x^2))/2) :
    HasDerivAt (fun t => ellD a (line x f t) e i) (ellDD a x e f i) 0 := by
  exact Fin.cases (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    (fun i => spatialEllD_derivative a x e f i hdisc hroot) i

def metricDD (mass : ℝ) (a x : Space) (e f : Fin 3) (i j : Fin 4) : ℝ :=
  2*potentialDD mass a x e f*ell a x i*ell a x j+
    2*potentialD mass a x e*(ellD a x f i*ell a x j+ell a x i*ellD a x f j)+
    2*potentialD mass a x f*(ellD a x e i*ell a x j+ell a x i*ellD a x e j)+
    2*potential mass a x*(ellDD a x e f i*ell a x j+ellD a x e i*ellD a x f j+
      ellD a x f i*ellD a x e j+ell a x i*ellDD a x e f j)

/-- All spatial second derivatives of all sixteen Kerr-Schild components,
    for arbitrary spin vectors on the nonsingular, unclamped radial domain. -/
theorem metricD_derivative (mass : ℝ) (a x : Space) (e f : Fin 3) (i j : Fin 4)
    (hdisc : 0 < q a x^2+4*b a x^2)
    (hroot : 0 < (q a x+Real.sqrt (q a x^2+4*b a x^2))/2) :
    HasDerivAt (fun t => metricD mass a (line x f t) e i j) (metricDD mass a x e f i j) 0 := by
  have hH := potential_derivative mass a x f hdisc hroot
  have hHe := potentialD_derivative mass a x e f hdisc hroot
  have hli := ell_derivative a x f i hdisc hroot
  have hlj := ell_derivative a x f j hdisc hroot
  have hlei := ellD_derivative a x e f i hdisc hroot
  have hlej := ellD_derivative a x e f j hdisc hroot
  have hfirst := ((hHe.const_mul 2).mul hli).mul hlj
  have hsecond := (hH.const_mul 2).mul ((hlei.mul hlj).add (hli.mul hlej))
  have h := hfirst.add hsecond
  simp only [Pi.add_def, Pi.mul_def, line_zero] at h
  convert h using 1
  · rfl
  · unfold metricDD
    ring

end BlackHole.Cartesian
