module

public import BlackHole.KerrPath

@[expose] public section
noncomputable section

namespace BlackHole.Cartesian

def radialHessian (a x : Space) (e f : Fin 3) : ℝ :=
  (radius a x*(basis f e-radiusD a x e*radiusD a x f+cosineD a x e*cosineD a x f)-
    cosine a x*(radiusD a x e*cosineD a x f+cosineD a x e*radiusD a x f))/sigma a x

def cosineHessian (a x : Space) (e f : Fin 3) : ℝ :=
  (-radius a x*(radiusD a x e*cosineD a x f+cosineD a x e*radiusD a x f)-
    cosine a x*(basis f e-radiusD a x e*radiusD a x f+cosineD a x e*cosineD a x f))/sigma a x

theorem b_optical (a x : Space) (hr : 0 < radius a x) : b a x = radius a x*cosine a x := by
  have hr0 := ne_of_gt hr
  unfold cosine
  field_simp

theorem radiusDD_optical (a x : Space) (hr : 0 < radius a x) (e f : Fin 3) :
    radiusDD a x e f = radialHessian a x e f := by
  have hr0 := ne_of_gt hr
  have hs0 := ne_of_gt (sigma_positive a x hr)
  simp only [radiusDD, radial_den_optical a x hr, b_optical a x hr]
  rw [← radial_complex_real a x hr e, ← radial_complex_real a x hr f,
    ← radial_complex_imag a x hr e, ← radial_complex_imag a x hr f]
  unfold radialHessian sigma
  field_simp
  ring

theorem cosineD_derivative (a x : Space) (hr : 0 < radius a x) (e f : Fin 3) :
    HasDerivAt (fun t => cosineD a (line x f t) e) (cosineHessian a x e f) 0 := by
  obtain ⟨hdisc,hroot⟩ := positive_radius_domain a x hr
  have hr0 := ne_of_gt hr
  have hs0 := ne_of_gt (sigma_positive a x hr)
  have hc := cosine_derivative a x f hdisc hroot
  have hRe := radiusD_derivative a x e f hdisc hroot
  have h := ((hc.mul hRe).const_sub (a e)).div (radius_derivative a x f hdisc hroot)
    (by simpa only [line_zero] using hr0)
  simp only [Pi.mul_def, Pi.div_def, line_zero] at h
  convert h using 1
  · rfl
  · rw [radiusDD_optical a x hr e f, ← radial_complex_imag a x hr e]
    unfold radialHessian cosineHessian sigma
    field_simp
    ring

theorem potentialD_optical (mass : ℝ) (a x : Space) (hr : 0 < radius a x) (e : Fin 3) :
    potentialD mass a x e = mass*(cosine a x^2-radius a x^2)/sigma a x^2*radiusD a x e-
      2*mass*radius a x*cosine a x/sigma a x^2*cosineD a x e := by
  have hr0 := ne_of_gt hr
  have hs0 := ne_of_gt (sigma_positive a x hr)
  simp only [potentialD, potential_optical mass a x hr, b_optical a x hr]
  rw [← radial_complex_imag a x hr e]
  unfold sigma
  field_simp
  ring

def potentialHessian (mass : ℝ) (a x : Space) (e f : Fin 3) : ℝ :=
  2*mass*radius a x*(radius a x^2-3*cosine a x^2)/sigma a x^3*radiusD a x e*radiusD a x f+
    2*mass*cosine a x*(3*radius a x^2-cosine a x^2)/sigma a x^3*
      (radiusD a x e*cosineD a x f+cosineD a x e*radiusD a x f)-
    2*mass*radius a x*(radius a x^2-3*cosine a x^2)/sigma a x^3*cosineD a x e*cosineD a x f+
    mass*(cosine a x^2-radius a x^2)/sigma a x^2*radialHessian a x e f-
    2*mass*radius a x*cosine a x/sigma a x^2*cosineHessian a x e f

set_option maxHeartbeats 1000000 in
theorem potentialDD_optical (mass : ℝ) (a x : Space) (hr : 0 < radius a x) (e f : Fin 3) :
    potentialDD mass a x e f = potentialHessian mass a x e f := by
  have hr0 := ne_of_gt hr
  have hs0 := ne_of_gt (sigma_positive a x hr)
  simp only [potentialDD, hLogDD, hLogD, hDenDD, hDenD, hDen,
    potentialD_optical mass a x hr, potential_optical mass a x hr, radiusDD_optical a x hr,
    b_optical a x hr]
  rw [← radial_complex_imag a x hr e, ← radial_complex_imag a x hr f]
  unfold potentialHessian radialHessian cosineHessian sigma
  field_simp
  ring

def ellHessian (a x : Space) (e f i : Fin 3) : ℝ :=
  (radiusD a x f*(basis e i-spatialEll a x i*spatialEll a x e)-
    radius a x*(spatialEllD a x f i*spatialEll a x e+spatialEll a x i*spatialEllD a x f e)-
    cosineD a x f*crossProduct (spatialEll a x) (basis e) i-
    cosine a x*crossProduct (spatialEllD a x f) (basis e) i-
    spatialEllD a x e i*(2*radius a x*radiusD a x f+2*cosine a x*cosineD a x f))/sigma a x

theorem spatialEllDD_optical (a x : Space) (hrpos : 0 < radius a x) (e f i : Fin 3) :
    spatialEllDD a x e f i = ellHessian a x e f i := by
  obtain ⟨hdisc,hroot⟩ := positive_radius_domain a x hrpos
  have hr := radius_derivative a x f hdisc hroot
  have hc := cosine_derivative a x f hdisc hroot
  have hL := fun j => spatialEll_derivative a x f j hdisc hroot
  have hcross : HasDerivAt (fun t => crossProduct (spatialEll a (line x f t)) (basis e) i)
      (crossProduct (spatialEllD a x f) (basis e) i) 0 := by
    fin_cases i
    · simpa [cross_apply, Pi.sub_def] using ((hL 1).mul_const (basis e 2)).sub ((hL 2).mul_const (basis e 1))
    · simpa [cross_apply, Pi.sub_def] using ((hL 2).mul_const (basis e 0)).sub ((hL 0).mul_const (basis e 2))
    · simpa [cross_apply, Pi.sub_def] using ((hL 0).mul_const (basis e 1)).sub ((hL 1).mul_const (basis e 0))
  have hsigma := (hr.pow 2).add (hc.pow 2)
  have hn := (hr.mul (((hL i).mul (hL e)).const_sub (basis e i))).sub (hc.mul hcross)
  have hd : radius a (line x f 0)^2+cosine a (line x f 0)^2 ≠ 0 := by
    simpa only [line_zero, sigma] using ne_of_gt (sigma_positive a x hrpos)
  have h := hn.div hsigma hd
  simp only [Pi.add_def, Pi.sub_def, Pi.mul_def, Pi.div_def, Pi.pow_apply, line_zero,
    Nat.cast_ofNat, Nat.reduceSub, pow_one] at h
  have hevent : ∀ᶠ t in nhds (0 : ℝ), 0 < radius a (line x f t) :=
    hr.continuousAt.eventually (lt_mem_nhds (by simpa only [line_zero] using hrpos))
  have heq : (fun t => spatialEllD a (line x f t) e i) =ᶠ[nhds (0 : ℝ)]
      (fun t => (radius a (line x f t)*(basis e i-spatialEll a (line x f t) i*spatialEll a (line x f t) e)-
        cosine a (line x f t)*crossProduct (spatialEll a (line x f t)) (basis e) i)/
        (radius a (line x f t)^2+cosine a (line x f t)^2)) := by
    filter_upwards [hevent] with t ht
    exact spatialEllD_optical a (line x f t) ht e i
  have hactual := h.congr_of_eventuallyEq heq
  rw [(spatialEllD_derivative a x e f i hdisc hroot).unique hactual]
  unfold ellHessian
  rw [spatialEllD_optical a x hrpos e i]
  unfold sigma
  have hs0 := ne_of_gt (sigma_positive a x hrpos)
  field_simp
  ring

end BlackHole.Cartesian
