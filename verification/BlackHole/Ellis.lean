module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean

/- James et al., arXiv:1502.03809, Eqs. (1), (2), (13), (16).
   Equatorial reduction by spherical symmetry; photon energy normalized to 1.
   This proves real equations, not floating-point trajectory enclosures. -/
@[expose] public section
noncomputable section

namespace BlackHole.Ellis

def radiusSquared (a l : ℝ) : ℝ := l^2 + a^2
def radialForce (a l b : ℝ) : ℝ := b^2 * l / radiusSquared a l ^ 2
def angularRate (a l b : ℝ) : ℝ := b / radiusSquared a l
def energy (a l p b : ℝ) : ℝ := p^2 + b^2 / radiusSquared a l
def hamiltonian (a l p b : ℝ) : ℝ := (energy a l p b - 1) / 2

theorem radiusSquared_pos (a l : ℝ) (ha : 0 < a) : 0 < radiusSquared a l := by
  unfold radiusSquared
  nlinarith [sq_nonneg l]

theorem throat_minimum (a l : ℝ) : a^2 ≤ radiusSquared a l := by
  unfold radiusSquared
  nlinarith [sq_nonneg l]

theorem hamiltonian_radial_derivative (a l p b : ℝ) (ha : 0 < a) :
    HasDerivAt (fun x => hamiltonian a x p b) (-radialForce a l b) l := by
  have hr := ((hasDerivAt_id l).pow 2).add_const (a^2)
  have hn := ne_of_gt (radiusSquared_pos a l ha)
  have h := ((((hasDerivAt_const l (b^2)).div hr hn).add_const (p^2)).sub_const 1).div_const 2
  convert h using 1
  · funext x
    dsimp [hamiltonian, energy, radiusSquared]
    ring
  · dsimp [radialForce, radiusSquared] at *
    field_simp
    ring

theorem hamiltonian_momentum_derivative (a l p b : ℝ) :
    HasDerivAt (fun x => hamiltonian a l x b) p p := by
  have h := ((((hasDerivAt_id p).pow 2).add_const (b^2 / radiusSquared a l)).sub_const 1).div_const 2
  convert h using 1 <;> simp [hamiltonian, energy]

theorem hamiltonian_angular_derivative (a l p b : ℝ) :
    HasDerivAt (fun x => hamiltonian a l p x) (angularRate a l b) b := by
  have h := (((((hasDerivAt_id b).pow 2).div_const (radiusSquared a l)).add_const (p^2)).sub_const 1).div_const 2
  convert h using 1
  · funext x
    dsimp [hamiltonian, energy]
    ring
  · dsimp [angularRate]
    ring

/-- The actual Hamiltonian ODE preserves the null constraint along a differentiable ray. -/
theorem energy_rate_zero (a b : ℝ) (ha : 0 < a) (l p : ℝ → ℝ) (t : ℝ)
    (hl : HasDerivAt l (p t) t)
    (hp : HasDerivAt p (radialForce a (l t) b) t) :
    HasDerivAt (fun s => energy a (l s) (p s) b) 0 t := by
  have hr := (hl.pow 2).add_const (a^2)
  have hn := ne_of_gt (radiusSquared_pos a (l t) ha)
  have h := (hp.pow 2).add ((hasDerivAt_const t (b^2)).div hr hn)
  convert h using 1
  · rfl
  · dsimp [radialForce, radiusSquared] at *
    field_simp
    ring

/-- Orthonormal camera components, with b = r times transverse component, initialize a null ray. -/
theorem camera_null (a l p s : ℝ) (ha : 0 < a) (hunit : p^2 + s^2 = 1) :
    energy a l p (Real.sqrt (radiusSquared a l) * s) = 1 := by
  have hr := radiusSquared_pos a l ha
  unfold energy
  rw [mul_pow, Real.sq_sqrt hr.le]
  field_simp
  nlinarith [hunit]

theorem subcritical_no_turning (a l p b : ℝ) (ha : 0 < a)
    (hb : b^2 < a^2) (hnull : energy a l p b = 1) : p ≠ 0 := by
  intro hp
  have hr := radiusSquared_pos a l ha
  simp only [energy, hp, zero_pow (by decide : 2 ≠ 0), zero_add] at hnull
  have he := (div_eq_one_iff_eq (ne_of_gt hr)).mp hnull
  have := throat_minimum a l
  linarith

/-- Subcritical null rays have a strictly positive lower bound on radial speed. -/
theorem subcritical_speed_bound (a l p b : ℝ) (ha : 0 < a)
    (hb : b^2 < a^2) (hnull : energy a l p b = 1) :
    0 < 1 - b^2/a^2 ∧ 1 - b^2/a^2 ≤ p^2 := by
  have ha2 : 0 < a^2 := sq_pos_of_pos ha
  have hratio := div_le_div_of_nonneg_left (sq_nonneg b) ha2 (throat_minimum a l)
  have hlt : b^2/a^2 < 1 := (div_lt_one ha2).mpr hb
  dsimp [energy] at hnull
  constructor <;> linarith

theorem turning_radius (a l b : ℝ) (ha : 0 < a)
    (hnull : energy a l 0 b = 1) : l^2 = b^2 - a^2 := by
  have hr := radiusSquared_pos a l ha
  simp only [energy, zero_pow (by decide : 2 ≠ 0), zero_add] at hnull
  have he := (div_eq_one_iff_eq (ne_of_gt hr)).mp hnull
  dsimp [radiusSquared] at he
  linarith

/-- The critical b=a ray is a circular null orbit at the throat. -/
theorem throat_photon_orbit (a : ℝ) (ha : 0 < a) :
    radialForce a 0 a = 0 ∧ energy a 0 0 a = 1 ∧ angularRate a 0 a = 1/a := by
  have hn := ne_of_gt ha
  simp [radialForce, energy, angularRate, radiusSquared, hn, pow_two]

/-- l = l₀ - λ is a regular radial null geodesic through l=0, with b=0. -/
theorem radial_crossing (a l₀ t : ℝ) (ha : 0 < a) :
    HasDerivAt (fun s : ℝ => l₀ - s) (-1) t ∧
    0 < radiusSquared a (l₀-t) ∧
    radialForce a (l₀-t) 0 = 0 ∧ energy a (l₀-t) (-1) 0 = 1 := by
  constructor
  · exact (hasDerivAt_id t).const_sub l₀
  · exact ⟨radiusSquared_pos a (l₀-t) ha, by simp [radialForce, energy]⟩

theorem reflection_symmetry (a l b : ℝ) : radialForce a (-l) b = -radialForce a l b := by
  simp [radialForce, radiusSquared, neg_div]

-- Rational fixtures are kernel-checked, then evaluated by the shared Rust/CUDA RHS tests.
def fixtureCases : List (ℚ × ℚ × ℚ × ℚ) :=
  [(0,-1,0,4), (12,-1,2,4), (4,0,4,4), (-4,1,2,4),
   (0,0,4,4), (3,4/5,5,4), (1/2,-3/5,7/2,2), (8,-1,0,2)]

def rationalRhs (l p b a : ℚ) : List ℚ :=
  [p, b*b*l/((l*l+a*a)*(l*l+a*a)), b/(l*l+a*a)]

theorem rational_force_correspondence (l b a : ℚ) :
    ((b*b*l/((l*l+a*a)*(l*l+a*a)) : ℚ) : ℝ) = radialForce a l b := by
  simp [radialForce, radiusSquared, pow_two]

theorem rational_angle_correspondence (l b a : ℚ) :
    ((b/(l*l+a*a) : ℚ) : ℝ) = angularRate a l b := by
  simp [angularRate, radiusSquared, pow_two]

private meta def fixtureText : String := include_str "../fixtures/ellis-rhs.csv"

meta def parseRationalFixture (contents : String) : Lean.MacroM Lean.Term := do
  let rows ← contents.trimAscii.toString.splitOn "\n" |>.toArray.mapM fun row => do
    let columns := row.splitOn ","
    unless columns.length == 7 do Lean.Macro.throwError "expected seven rational columns"
    let values ← columns.toArray.mapM fun number => do
      let [n,d] := number.splitOn "/" | Lean.Macro.throwError "expected numerator/denominator"
      let some n := n.toInt? | Lean.Macro.throwError "invalid numerator"
      let some d := d.toNat? | Lean.Macro.throwError "invalid denominator"
      if d == 0 then Lean.Macro.throwError "zero denominator"
      let magnitude := n.natAbs
      if n < 0 then `((-($(Lean.quote magnitude) : ℚ) / ($(Lean.quote d) : ℚ)))
      else `((($(Lean.quote magnitude) : ℚ) / ($(Lean.quote d) : ℚ)))
    `([$[$values],*])
  `([$[$rows],*])

macro "ellis_fixture" : term => parseRationalFixture fixtureText

def fixture : List (List ℚ) := ellis_fixture

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem fixture_checked : fixture = fixtureCases.map (fun (l,p,b,a) =>
    [l,p,b,a] ++ rationalRhs l p b a) := by
  decide +kernel

end BlackHole.Ellis
