module

public import BlackHole.KerrGeodesics
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Radial equation of motion and linear stability of equatorial circular
orbits (obligation I3).

`KerrEquatorial.source_radial_first_integral` pulls the production Cartesian
metric back to the equatorial chart and turns its timelike normalization into
`r⁴ ṙ² = R(r)`, with `R = Kerr.radial E L a`. Along a geodesic E and L are
conserved (`Hamiltonian`: the metric does not depend on t or φ). This file
differentiates that first integral into the radial equation of motion,
computes its linearization about a circular orbit, and proves that the
linearized radial motion is bounded exactly outside the ISCO. -/

@[expose] public section
noncomputable section

namespace BlackHole.Kerr

/-- Effective radial potential: `ṙ² = V(r)`. -/
def potential (E L a r : ℝ) : ℝ := radial E L a r/r^4

def potentialSlope (E L a r : ℝ) : ℝ :=
  radialSlope E L a r/r^4-4*radial E L a r/r^5

def potentialCurvature (E L a r : ℝ) : ℝ :=
  radialCurvature E L a r/r^4-8*radialSlope E L a r/r^5+20*radial E L a r/r^6

theorem potential_derivative (E L a r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (potential E L a) (potentialSlope E L a r) r := by
  have h := HasDerivAt.div (radial_derivative E L a r) ((hasDerivAt_id' r).pow 4) (pow_ne_zero 4 hr)
  have heq : potential E L a = fun x => radial E L a x/x^4 := rfl
  rw [heq]
  convert h using 1
  simp only [Pi.pow_apply, Nat.cast_ofNat]
  unfold potentialSlope
  field_simp
  ring

theorem potentialSlope_derivative (E L a r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (potentialSlope E L a) (potentialCurvature E L a r) r := by
  have h1 := HasDerivAt.div (radialSlope_derivative E L a r) ((hasDerivAt_id' r).pow 4)
    (pow_ne_zero 4 hr)
  have h2 := HasDerivAt.div ((radial_derivative E L a r).const_mul 4) ((hasDerivAt_id' r).pow 5)
    (pow_ne_zero 5 hr)
  have h := h1.sub h2
  have heq : potentialSlope E L a = fun x =>
      radialSlope E L a x/x^4-4*radial E L a x/x^5 := by
    funext x; rfl
  rw [heq]
  convert h using 1
  simp only [Pi.pow_apply, Nat.cast_ofNat]
  unfold potentialCurvature
  field_simp
  ring

/-- The radial equation of motion: differentiating `ṙ² = V(r)` along a
    non-turning point gives `r̈ = V'(r)/2`. -/
theorem radial_equation_of_motion (E L a : ℝ) (r rdot : ℝ → ℝ) (τ rddot : ℝ)
    (hr : ∀ s, HasDerivAt r (rdot s) s) (hrdot : HasDerivAt rdot rddot τ)
    (hfirst : ∀ s, rdot s^2 = potential E L a (r s)) (hpos : r τ ≠ 0)
    (hturn : rdot τ ≠ 0) :
    rddot = potentialSlope E L a (r τ)/2 := by
  have hl : HasDerivAt (fun s => rdot s^2) (2*rdot τ*rddot) τ := by
    have := hrdot.pow 2
    convert this using 1
    simp
  have hr' : HasDerivAt (fun s => potential E L a (r s))
      (potentialSlope E L a (r τ)*rdot τ) τ :=
    (potential_derivative E L a (r τ) hpos).comp τ (hr τ)
  have hfun : (fun s => rdot s^2) = fun s => potential E L a (r s) := funext hfirst
  rw [hfun] at hl
  have := hl.unique hr'
  field_simp
  have h2 : 2*rdot τ*rddot = potentialSlope E L a (r τ)*rdot τ := this
  have : rdot τ*(2*rddot-potentialSlope E L a (r τ)) = 0 := by linear_combination h2
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hturn
  · linarith

/-- At a circular orbit (`R = R' = 0`) the linearization coefficient of the
    radial equation is `V''/2 = R''/(2r⁴)`. -/
theorem circular_linearization (E L a r : ℝ) (hR : radial E L a r = 0)
    (hR' : radialSlope E L a r = 0) :
    potentialSlope E L a r = 0 ∧
      potentialCurvature E L a r = radialCurvature E L a r/r^4 := by
  unfold potentialSlope potentialCurvature
  rw [hR, hR']
  constructor <;> ring

/-- Solutions of `δ'' = κ δ` are bounded for `κ < 0`: the quantity
    `δ'² - κ δ²` is conserved. -/
theorem linear_bounded (κ : ℝ) (hκ : κ < 0) (δ δ' : ℝ → ℝ)
    (hδ : ∀ τ, HasDerivAt δ (δ' τ) τ) (hδ' : ∀ τ, HasDerivAt δ' (κ*δ τ) τ) :
    ∃ C, ∀ τ, |δ τ| ≤ C := by
  set f := fun τ => δ' τ^2-κ*δ τ^2 with hf
  have hderiv : ∀ τ, HasDerivAt f 0 τ := by
    intro τ
    have h := ((hδ' τ).pow 2).sub (((hδ τ).pow 2).const_mul κ)
    convert h using 1
    simp only [Nat.cast_ofNat]
    ring
  have hconst : ∀ τ, f τ = f 0 := by
    intro τ
    exact is_const_of_deriv_eq_zero
      (fun x => (hderiv x).differentiableAt) (fun x => (hderiv x).deriv) τ 0
  refine ⟨Real.sqrt (f 0/(-κ)), fun τ => ?_⟩
  have hsq : δ τ^2 ≤ f 0/(-κ) := by
    rw [le_div_iff₀ (by linarith), ← hconst τ, hf]
    nlinarith [sq_nonneg (δ' τ)]
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hsq

/-- For `κ ≥ 0` the linearized equation has an unbounded solution. -/
theorem linear_unbounded (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ δ δ' : ℝ → ℝ, (∀ τ, HasDerivAt δ (δ' τ) τ) ∧
      (∀ τ, HasDerivAt δ' (κ*δ τ) τ) ∧ ∀ C, ∃ τ, C < |δ τ| := by
  rcases eq_or_lt_of_le hκ with h0 | hpos
  · subst h0
    refine ⟨fun τ => τ, fun _ => 1, fun τ => hasDerivAt_id' τ, ?_, ?_⟩
    · intro τ; simpa using hasDerivAt_const τ (1:ℝ)
    · intro C; exact ⟨|C|+1, by rw [abs_of_nonneg (by positivity)]; linarith [le_abs_self C]⟩
  · set w := Real.sqrt κ with hw
    have hw0 : 0 < w := Real.sqrt_pos.mpr hpos
    have hww : w*w = κ := Real.mul_self_sqrt hκ
    refine ⟨fun τ => Real.exp (w*τ), fun τ => w*Real.exp (w*τ), ?_, ?_, ?_⟩
    · intro τ
      have := ((hasDerivAt_id' τ).const_mul w).exp
      simpa [mul_comm] using this
    · intro τ
      have := (((hasDerivAt_id' τ).const_mul w).exp).const_mul w
      convert this using 1
      rw [← hww]; ring
    · intro C
      refine ⟨|C|/w, ?_⟩
      rw [abs_of_pos (Real.exp_pos _), mul_div_cancel₀ _ hw0.ne']
      have := Real.add_one_le_exp |C|
      linarith [le_abs_self C]

/-- Radial stability interpretation of the ISCO: for the timelike circular
    orbit at `r = u²` with its conserved charges, the linearized radial
    equation `δ'' = (V''/2) δ` has only bounded solutions exactly when the
    orbit lies outside the Bardeen ISCO; otherwise an unbounded solution exists. -/
theorem circular_orbit_linear_stability (a u : ℝ) (ha : |a| ≤ 1) (hu : 1 ≤ u)
    (hd : 0 < circularDenominator a u) :
    let E := circularEnergy a u
    let L := circularMomentum a u
    let κ := potentialCurvature E L a (u^2)/2
    (isco a < u^2 →
      ∀ δ δ' : ℝ → ℝ, (∀ τ, HasDerivAt δ (δ' τ) τ) → (∀ τ, HasDerivAt δ' (κ*δ τ) τ) →
        ∃ C, ∀ τ, |δ τ| ≤ C) ∧
    (u^2 ≤ isco a →
      ∃ δ δ' : ℝ → ℝ, (∀ τ, HasDerivAt δ (δ' τ) τ) ∧
        (∀ τ, HasDerivAt δ' (κ*δ τ) τ) ∧ ∀ C, ∃ τ, C < |δ τ|) := by
  intro E L κ
  have hR := circular_radial_zero a u hd
  have hR' := circular_radialSlope_zero a u hd
  have hκ : κ = radialCurvature E L a (u^2)/(u^2)^4/2 := by
    show potentialCurvature E L a (u^2)/2 = _
    rw [(circular_linearization E L a (u^2) hR hR').2]
  have hp : 0 < (u^2)^4 := by positivity
  have hstab := circular_radially_stable_iff a u ha hu hd
  constructor
  · intro hout δ δ' hδ hδ'
    have hneg : radialCurvature E L a (u^2) < 0 := hstab.mpr hout
    have : κ < 0 := by
      rw [hκ]
      apply div_neg_of_neg_of_pos (div_neg_of_neg_of_pos hneg hp) (by norm_num)
    exact linear_bounded κ this δ δ' hδ hδ'
  · intro hin
    have hnn : 0 ≤ radialCurvature E L a (u^2) := by
      by_contra h
      push Not at h
      have := hstab.mp h
      linarith
    have : 0 ≤ κ := by rw [hκ]; positivity
    exact linear_unbounded κ this

end BlackHole.Kerr
