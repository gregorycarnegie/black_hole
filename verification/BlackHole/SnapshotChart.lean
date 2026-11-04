module
public import BlackHole.KerrEquatorial
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section
noncomputable section
namespace BlackHole.SnapshotChart

def position (a r th phi : ℝ) : Cartesian.Space :=
  ![(r*Real.cos phi-a*Real.sin phi)*Real.sin th,
    r*Real.cos th, -(r*Real.sin phi+a*Real.cos phi)*Real.sin th]

theorem position_q (a r th phi : ℝ) :
    Cartesian.q (KerrChart.spin a) (position a r th phi) =
      r^2-a^2*(Real.cos th)^2 := by
  simp [Cartesian.q,KerrChart.spin,position,dotProduct,Fin.sum_univ_succ]
  linear_combination
    (r^2+a^2)*(Real.sin th)^2*(Real.sin_sq_add_cos_sq phi) +
    (r^2+a^2)*(Real.sin_sq_add_cos_sq th)

theorem position_b (a r th phi : ℝ) :
    Cartesian.b (KerrChart.spin a) (position a r th phi) = a*r*Real.cos th := by
  simp [Cartesian.b,KerrChart.spin,position,dotProduct,Fin.sum_univ_succ]
  ring

theorem position_radius (a r th phi : ℝ) (hr : 0 < r) :
    Cartesian.radius (KerrChart.spin a) (position a r th phi) = r := by
  unfold Cartesian.radius Calculus.kerrRadius
  rw [position_q,position_b]
  have hid : (r^2-a^2*(Real.cos th)^2)^2+4*(a*r*Real.cos th)^2 =
      (r^2+a^2*(Real.cos th)^2)^2 := by ring
  rw [hid,Real.sqrt_sq_eq_abs,abs_of_nonneg (by positivity)]
  have hs : (r^2-a^2*(Real.cos th)^2+(r^2+a^2*(Real.cos th)^2))/2 = r^2 := by ring
  rw [hs,Real.sqrt_sq_eq_abs,abs_of_pos hr]

theorem position_ell (a r th phi : ℝ) (hr : 0 < r) :
    Cartesian.spatialEll (KerrChart.spin a) (position a r th phi) =
      ![Real.sin th*Real.cos phi,Real.cos th,-Real.sin th*Real.sin phi] := by
  have hd : r^2+a^2 ≠ 0 := ne_of_gt (by positivity : 0 < r^2+a^2)
  ext i
  simp only [Cartesian.spatialEll,position_radius a r th phi hr,position_b]
  fin_cases i <;> simp [KerrChart.spin,position,cross_apply,dotProduct,Fin.sum_univ_succ]
  all_goals field_simp
  all_goals ring

def theta (h x : ℝ) : ℝ := Real.pi*x+(1-h)/2*Real.sin (2*Real.pi*x)
def thetaD (h x : ℝ) : ℝ := Real.pi*(1+(1-h)*Real.cos (2*Real.pi*x))

theorem theta_derivative (h x : ℝ) : HasDerivAt (theta h) (thetaD h x) x := by
  unfold theta thetaD
  convert (((hasDerivAt_id x).const_mul Real.pi).add
    (((hasDerivAt_id x).const_mul (2*Real.pi)).sin.const_mul ((1-h)/2))) using 1
  · funext y
    rfl
  · dsimp
    ring

theorem theta_derivative_lower (h x : ℝ) (hh : h ≤ 1) :
    Real.pi*h ≤ thetaD h x := by
  have hc := Real.neg_one_le_cos (2*Real.pi*x)
  have hp := Real.pi_pos
  unfold thetaD
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1-h) (by linarith : 0 ≤ 1+Real.cos (2*Real.pi*x))]

theorem theta_strictMono (h : ℝ) (hpos : 0 < h) (hh : h ≤ 1) : StrictMono (theta h) := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(theta_derivative h x).deriv]
  exact lt_of_lt_of_le (mul_pos Real.pi_pos hpos) (theta_derivative_lower h x hh)

theorem theta_range (h x : ℝ) (hpos : 0 < h) (hh : h ≤ 1)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : theta h x ∈ Set.Icc (0 : ℝ) Real.pi := by
  have hm := (theta_strictMono h hpos hh).monotone
  have h0 := hm hx.1
  have h1 := hm hx.2
  simpa [theta,Real.sin_two_pi] using And.intro h0 h1

def lerp (t a b : ℝ) : ℝ := (1-t)*a+t*b

theorem lerp_bounds (t a b lo hi : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ha : a ∈ Set.Icc lo hi) (hb : b ∈ Set.Icc lo hi) :
    lerp t a b ∈ Set.Icc lo hi := by
  constructor <;> unfold lerp
  · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ha.1),
      mul_nonneg ht.1 (sub_nonneg.mpr hb.1)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ha.2),
      mul_nonneg ht.1 (sub_nonneg.mpr hb.2)]

def trilinear (d : Fin 3 → ℝ) (v : Fin 2 → Fin 2 → Fin 2 → ℝ) : ℝ :=
  lerp (d 2)
    (lerp (d 1) (lerp (d 0) (v 0 0 0) (v 1 0 0)) (lerp (d 0) (v 0 1 0) (v 1 1 0)))
    (lerp (d 1) (lerp (d 0) (v 0 0 1) (v 1 0 1)) (lerp (d 0) (v 0 1 1) (v 1 1 1)))

theorem trilinear_weighted (d : Fin 3 → ℝ) (v : Fin 2 → Fin 2 → Fin 2 → ℝ) :
    trilinear d v =
      (1-d 2)*((1-d 0)*(1-d 1)*v 0 0 0+(1-d 0)*d 1*v 0 1 0+
        d 0*(1-d 1)*v 1 0 0+d 0*d 1*v 1 1 0)+
      d 2*((1-d 0)*(1-d 1)*v 0 0 1+(1-d 0)*d 1*v 0 1 1+
        d 0*(1-d 1)*v 1 0 1+d 0*d 1*v 1 1 1) := by
  simp only [trilinear,lerp]
  ring

theorem trilinear_bounds (d : Fin 3 → ℝ) (v : Fin 2 → Fin 2 → Fin 2 → ℝ)
    (lo hi : ℝ) (hd : ∀ i, d i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ i j k, v i j k ∈ Set.Icc lo hi) :
    trilinear d v ∈ Set.Icc lo hi := by
  exact lerp_bounds _ _ _ _ _ (hd 2)
    (lerp_bounds _ _ _ _ _ (hd 1)
      (lerp_bounds _ _ _ _ _ (hd 0) (hv 0 0 0) (hv 1 0 0))
      (lerp_bounds _ _ _ _ _ (hd 0) (hv 0 1 0) (hv 1 1 0)))
    (lerp_bounds _ _ _ _ _ (hd 1)
      (lerp_bounds _ _ _ _ _ (hd 0) (hv 0 0 1) (hv 1 0 1))
      (lerp_bounds _ _ _ _ _ (hd 0) (hv 0 1 1) (hv 1 1 1)))

theorem trilinear_constant (d : Fin 3 → ℝ) (c : ℝ) :
    trilinear d (fun _ _ _ => c) = c := by
  simp only [trilinear,lerp]
  ring

end BlackHole.SnapshotChart
