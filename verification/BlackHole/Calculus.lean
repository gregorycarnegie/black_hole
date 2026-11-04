module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section

namespace BlackHole.Calculus

def kerrRadius (q b : ℝ) : ℝ := Real.sqrt ((q + Real.sqrt (q^2 + 4*b^2))/2)

/-- Derivative of the explicit positive Kerr root, matching dr in add_kerr.
    q' = 2x_j and b' = a_j for a Cartesian partial derivative. Both strict
    inequalities exclude the singular disk and numerical floor branches. -/
theorem kerrRadius_derivative (q b : ℝ → ℝ) (t xj aj : ℝ)
    (hq : HasDerivAt q (2*xj) t) (hb : HasDerivAt b aj t)
    (hd : 0 < q t ^ 2 + 4*b t ^ 2)
    (hr : 0 < (q t + Real.sqrt (q t ^ 2 + 4*b t ^ 2))/2) :
    HasDerivAt (fun s => kerrRadius (q s) (b s))
      ((kerrRadius (q t) (b t)*xj + (b t/kerrRadius (q t) (b t))*aj) /
        (2*kerrRadius (q t) (b t)^2-q t)) t := by
  have hdisc := ((hq.pow 2).add ((hb.pow 2).const_mul 4)).sqrt (ne_of_gt hd)
  have h := ((hq.add hdisc).div_const 2).sqrt (ne_of_gt hr)
  simp only [Pi.add_apply, Pi.pow_apply, Nat.cast_ofNat,
    Nat.reduceSub, pow_one] at h
  have hs := Real.sq_sqrt (le_of_lt hr)
  have hspos := Real.sqrt_pos.mpr hr
  have hdpos := Real.sqrt_pos.mpr hd
  have hden : 2*kerrRadius (q t) (b t)^2-q t = Real.sqrt (q t^2+4*b t^2) := by
    unfold kerrRadius
    nlinarith
  convert h using 1
  · rfl
  · rw [hden]
    unfold kerrRadius
    field_simp
    linear_combination 4*xj*hs

def kerrH (mass r b : ℝ) : ℝ := mass*r^3/(r^4+b^2)

theorem kerrH_derivative (r b : ℝ → ℝ) (mass t dr db : ℝ)
    (hr : HasDerivAt r dr t) (hb : HasDerivAt b db t)
    (hr0 : r t ≠ 0) (hd : r t^4+b t^2 ≠ 0) :
    HasDerivAt (fun s => kerrH mass (r s) (b s))
      (kerrH mass (r t) (b t) *
        (3*dr/r t - (4*r t^3*dr+2*b t*db)/(r t^4+b t^2))) t := by
  have h := ((hr.pow 3).const_mul mass).div ((hr.pow 4).add (hb.pow 2)) hd
  simp only [Pi.add_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one] at h
  convert h using 1
  · rfl
  · unfold kerrH
    field_simp

theorem ell_component_derivative (r x b c : ℝ → ℝ) (a a2 t dr dx db dc : ℝ)
    (hr : HasDerivAt r dr t) (hx : HasDerivAt x dx t)
    (hb : HasDerivAt b db t) (hc : HasDerivAt c dc t)
    (hr0 : r t ≠ 0) (hd : r t^2+a2 ≠ 0) :
    let ell := fun s => (r s*x s-c s+(b s/r s)*a)/(r s^2+a2)
    HasDerivAt ell
      ((dr*x t+r t*dx-dc+(db/r t-b t*dr/r t^2)*a-ell t*2*r t*dr)/(r t^2+a2)) t := by
  dsimp
  have h := (((hr.mul hx).sub hc).add ((hb.div hr hr0).mul_const a)).div
    ((hr.pow 2).add_const a2) hd
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply,
    Nat.cast_ofNat, Nat.reduceSub, pow_one] at h
  convert h using 1
  field_simp

theorem metric_component_derivative (h l u : ℝ → ℝ) (t dh dl du : ℝ)
    (hh : HasDerivAt h dh t) (hl : HasDerivAt l dl t) (hu : HasDerivAt u du t) :
    HasDerivAt (fun s => 2*h s*l s*u s)
      (2*dh*l t*u t+2*h t*(dl*u t+l t*du)) t := by
  convert ((hh.const_mul 2).mul hl).mul hu using 1
  simp only [Pi.mul_apply]
  ring

def cosineIntegral (alpha w s : ℝ) : ℝ :=
  (alpha*(1-Real.exp (-alpha*s)*Real.cos (w*s)) +
    w*Real.exp (-alpha*s)*Real.sin (w*s))/(alpha^2+w^2)

def sineIntegral (alpha w s : ℝ) : ℝ :=
  (w*(1-Real.exp (-alpha*s)*Real.cos (w*s)) -
    alpha*Real.exp (-alpha*s)*Real.sin (w*s))/(alpha^2+w^2)

theorem cosineIntegral_derivative (alpha w s : ℝ) (hd : alpha^2+w^2 ≠ 0) :
    HasDerivAt (cosineIntegral alpha w) (Real.exp (-alpha*s)*Real.cos (w*s)) s := by
  have he := ((hasDerivAt_id s).const_mul (-alpha)).exp
  have hc := ((hasDerivAt_id s).const_mul w).cos
  have hs := ((hasDerivAt_id s).const_mul w).sin
  have h := ((((he.mul hc).const_sub 1).const_mul alpha).add
    (((he.mul hs).const_mul w))).div_const (alpha^2+w^2)
  change HasDerivAt (fun x => (alpha*(1-Real.exp (-alpha*x)*Real.cos (w*x)) +
    w*Real.exp (-alpha*x)*Real.sin (w*x))/(alpha^2+w^2)) _ s
  convert h using 1
  · funext x
    simp only [Pi.add_apply, Pi.mul_apply, id_eq]
    ring
  · simp only [id_eq, mul_one]
    field_simp
    ring

theorem sineIntegral_derivative (alpha w s : ℝ) (hd : alpha^2+w^2 ≠ 0) :
    HasDerivAt (sineIntegral alpha w) (Real.exp (-alpha*s)*Real.sin (w*s)) s := by
  have he := ((hasDerivAt_id s).const_mul (-alpha)).exp
  have hc := ((hasDerivAt_id s).const_mul w).cos
  have hs := ((hasDerivAt_id s).const_mul w).sin
  have h := ((((he.mul hc).const_sub 1).const_mul w).sub
    (((he.mul hs).const_mul alpha))).div_const (alpha^2+w^2)
  change HasDerivAt (fun x => (w*(1-Real.exp (-alpha*x)*Real.cos (w*x)) -
    alpha*Real.exp (-alpha*x)*Real.sin (w*x))/(alpha^2+w^2)) _ s
  convert h using 1
  · funext x
    simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
    ring
  · simp only [id_eq, mul_one]
    field_simp
    ring

theorem polarized_coefficients_ode (alpha w s : ℝ) (hd : alpha^2+w^2 ≠ 0) :
    Real.exp (-alpha*s)*Real.cos (w*s) =
      1-alpha*cosineIntegral alpha w s-w*sineIntegral alpha w s ∧
    Real.exp (-alpha*s)*Real.sin (w*s) =
      w*cosineIntegral alpha w s-alpha*sineIntegral alpha w s := by
  unfold cosineIntegral sineIntegral
  constructor <;> field_simp <;> ring

theorem polarized_coefficients_zero (alpha w : ℝ) :
    cosineIntegral alpha w 0 = 0 ∧ sineIntegral alpha w 0 = 0 := by
  simp [cosineIntegral, sineIntegral]

end BlackHole.Calculus
