module

public import BlackHole.Ellis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/- Ohgami & Sakai, arXiv:1704.07065, Eqs. (3.9), (3.10), (5.4)-(5.7).
   Time-dependent pressureless test dust on the fixed ultrastatic Ellis metric.
   The pulse is an exact characteristic solution, not a backreaction model. -/
@[expose] public section
noncomputable section

namespace BlackHole.EllisDust
open Ellis (radiusSquared radiusSquared_pos)

def speed : ℝ := -1/2
def gamma : ℝ := 1 / Real.sqrt (1-speed^2)
def pulse (a x : ℝ) : ℝ := a^2 / (1+((x-2*a)/a)^2)^2
def advected (a v : ℝ) (F : ℝ → ℝ) (t l : ℝ) : ℝ := F (l-v*t) / radiusSquared a l
def density (a t l : ℝ) : ℝ := advected a speed (pulse a) t l
def photonEnergy (p : ℝ) : ℝ := gamma * (1+speed*p)

theorem gamma_pos : 0 < gamma := by
  unfold gamma speed
  positivity

theorem timelike_flow : -gamma^2 + (gamma*speed)^2 = -1 := by
  have hs : 0 < 1-speed^2 := by norm_num [speed]
  have hroot := Real.sq_sqrt hs.le
  unfold gamma
  field_simp
  nlinarith [hroot]

theorem gamma_squared : gamma^2 = 4/3 := by
  have h := timelike_flow
  norm_num [speed] at h
  nlinarith

theorem photon_energy_squared (p : ℝ) : photonEnergy p^2 = (1-p/2)^2/(3/4) := by
  unfold photonEnergy
  rw [mul_pow, gamma_squared]
  unfold speed
  ring

theorem weighted_characteristic (a v t x : ℝ) (F : ℝ → ℝ) (ha : 0 < a) :
    radiusSquared a (x+v*t) * advected a v F t (x+v*t) = F x := by
  have hn := ne_of_gt (radiusSquared_pos a (x+v*t) ha)
  simp only [advected, add_sub_cancel_right]
  field_simp

theorem advected_derivatives (a v t l d : ℝ) (F : ℝ → ℝ) (ha : 0 < a)
    (hF : HasDerivAt F d (l-v*t)) :
    HasDerivAt (fun s => advected a v F s l) (-v*d/radiusSquared a l) t ∧
    HasDerivAt (fun x => advected a v F t x)
      (d/radiusSquared a l - 2*l*F (l-v*t)/radiusSquared a l^2) l := by
  have ht : HasDerivAt (fun s : ℝ => l-v*s) (-v) t := by
    convert ((hasDerivAt_id t).const_mul v).const_sub l using 1 <;> simp
  have hl : HasDerivAt (fun x : ℝ => x-v*t) 1 l := (hasDerivAt_id l).sub_const _
  have hr := ((hasDerivAt_id l).pow 2).add_const (a^2)
  have hn := ne_of_gt (radiusSquared_pos a l ha)
  constructor
  · convert (hF.comp t ht).div_const (radiusSquared a l) using 1
    · rfl
    · ring
  · convert (hF.comp l hl).div hr hn using 1
    · rfl
    · dsimp [radiusSquared] at *
      field_simp

/-- Relativistic number continuity after cancelling the constant positive gamma. -/
theorem number_continuity (a v t l d : ℝ) (F : ℝ → ℝ) (ha : 0 < a)
    (hF : HasDerivAt F d (l-v*t)) :
    deriv (fun s => advected a v F s l) t +
      v * deriv (fun x => advected a v F t x) l +
      2*l*v*advected a v F t l/radiusSquared a l = 0 := by
  have h := advected_derivatives a v t l d F ha hF
  rw [h.1.deriv, h.2.deriv]
  unfold advected
  ring

theorem pulse_differentiable (a : ℝ) : Differentiable ℝ (pulse a) := by
  intro x
  have hq := ((hasDerivAt_id x).sub_const (2*a)).div_const a
  have hd := ((hq.pow 2).const_add 1).pow 2
  have hn : (1+((x-2*a)/a)^2)^2 ≠ 0 := by positivity
  exact ((hasDerivAt_const x (a^2)).div hd hn).differentiableAt

theorem pulse_nonnegative (a x : ℝ) : 0 ≤ pulse a x :=
  div_nonneg (sq_nonneg a) (sq_nonneg _)

theorem density_nonnegative (a t l : ℝ) (ha : 0 < a) : 0 ≤ density a t l :=
  div_nonneg (pulse_nonnegative _ _) (radiusSquared_pos a l ha).le

theorem pulse_conserves_number (a t l : ℝ) (ha : 0 < a) :
    deriv (fun s => density a s l) t + speed * deriv (fun x => density a t x) l +
      2*l*speed*density a t l/radiusSquared a l = 0 :=
  number_continuity a speed t l _ (pulse a) ha (pulse_differentiable a _).hasDerivAt

theorem throat_passage (a : ℝ) (ha : 0 < a) : density a (4*a) 0 = 1 := by
  have hn := ne_of_gt ha
  have hz : -(speed*(4*a))-2*a = 0 := by unfold speed; ring
  simp [density, advected, pulse, radiusSquared, hz, hn]

/-- The dust's radial proper-time velocity is constant: the pressureless Euler equation. -/
theorem radial_euler (t : ℝ) : HasDerivAt (fun _ : ℝ => gamma*speed) 0 t :=
  hasDerivAt_const _ _

theorem photon_energy_bounds (p : ℝ) (hp : |p| ≤ 1) :
    gamma/2 ≤ photonEnergy p ∧ photonEnergy p ≤ 3*gamma/2 := by
  have habs := abs_le.mp hp
  have hg := gamma_pos
  unfold photonEnergy speed
  constructor <;> nlinarith

/-- The optically thin flat-spectrum transfer from Eq. (5.4) is n/nu_em for E_obs=1. -/
theorem flat_spectrum_transfer (n nu : ℝ) (hnu : 0 < nu) :
    (n*nu)/nu^2 = n/nu := by
  field_simp

def fixtureCases : List (ℚ × ℚ × ℚ × ℚ) :=
  [(8,0,-1,4), (0,16,-1,4), (-8,32,1,4), (0,0,0,4),
   (4,8,1/2,4), (8,8,-1/2,4), (0,8,1,2), (2,0,0,2)]

def rationalDensity (l t a : ℚ) : ℚ :=
  let q := (l+t/2-2*a)/a
  a*a / ((l*l+a*a)*(1+q*q)*(1+q*q))

theorem rational_density_correspondence (l t a : ℚ) :
    ((rationalDensity l t a : ℚ) : ℝ) = density a t l := by
  unfold rationalDensity
  push_cast
  unfold density advected pulse speed radiusSquared
  rw [div_div]
  congr 1 <;> ring

private meta def fixtureText : String := include_str "../fixtures/ellis-dust.csv"
macro "dust_fixture" : term => Ellis.parseRationalFixture fixtureText
def fixture : List (List ℚ) := dust_fixture

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem fixture_checked : fixture = fixtureCases.map (fun (l,t,p,a) =>
    [l,t,p,a, rationalDensity l t a, (l*l+a*a)*rationalDensity l t a,
     (1-p/2)^2/(3/4)]) := by decide +kernel

end BlackHole.EllisDust
