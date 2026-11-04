module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Unit conversion and timing (obligation D3), tied to `src/simulation.rs`
and `src/physics.rs`.

The source works in gravitational units G = c = M = 1: lengths are
`r_g = GM/c²`, times `t_g = GM/c³`, and `SimObject::velocity` is stated in
`r_g` per time unit with c = 1. Bevy advances `Time<Fixed>` by its default
15 625 µs step and `Time` by wall-clock seconds; the source uses either
`delta_secs()` directly as the gravitational time step. -/

@[expose] public section
noncomputable section

namespace BlackHole.Units

/-- Gravitational length and time units for nonzero, finite real scales. Every
    real number is finite, so the only precondition is that `c` and `GM` are
    nonzero; the length/time ratio is then `c`, and both units are positive
    when the scales are. -/
theorem gravitational_units (G mass c : ℝ) (hG : 0 < G) (hm : 0 < mass) (hc : 0 < c) :
    0 < G*mass/c^2 ∧ 0 < G*mass/c^3 ∧ (G*mass/c^2)/(G*mass/c^3) = c := by
  refine ⟨by positivity, by positivity, ?_⟩
  have : G*mass ≠ 0 := by positivity
  field_simp

/-- A zero mass or zero G makes both units vanish, so the ratio is undefined
    rather than c: the conversion needs a strictly positive GM. -/
theorem zero_scale_degenerate (c : ℝ) : (0:ℝ)/c^2 = 0 ∧ (0:ℝ)/c^3 = 0 := by simp

/-- Bevy's default fixed step, 15 625 µs, is exactly 2⁻⁶ s, so `delta_secs()`
    returns it without binary32 rounding and the gravity update uses
    `dt = 1/64` time units exactly. -/
theorem fixed_step_exact : (15625:ℝ)/1000000 = 1/2^6 := by norm_num

/-- `kerr_horizon_radius` scales the dimensionless radius by `SAGA_RS / 2`, so
    its metre value at spin zero is `SAGA_RS`, i.e. the factor is `r_g` in metres. -/
theorem horizon_metres_scale (rg : ℝ) (h : rg = 2) : 1/2*((1269:ℝ)*10^7)*rg = 1269*10^7 := by
  subst h; norm_num

/-- Speed of light in m/s and the Sagittarius A* time unit `t_g = r_g / c`
    implied by `SAGA_RS = 1.269e10 m`: 21.16 s < t_g < 21.17 s. The renderer
    treats one second of simulation time as one `t_g`, so it plays the
    Sagittarius A* system about 21 times faster than real time. -/
theorem sgra_time_unit :
    let tg := ((1269:ℝ)*10^7/2)/299792458
    2116/100 < tg ∧ tg < 2117/100 := by
  intro tg
  constructor <;> (simp only [tg]; norm_num)

/-! ### Prescribed binary timing

`binary_black_holes` places each hole at `orbital_radius = ½·7·2 = 7 r_g` and
advances the phase by `2π / 18` per time unit. -/

/-- Orbital radius of each hole, in `r_g`. -/
def binaryOrbitRadius : ℝ := 1/2*7*2
/-- Prescribed angular velocity, radians per time unit. -/
def binaryAngularVelocity : ℝ := 2*Real.pi/18

/-- The prescribed speed of each hole exceeds the speed of light (c = 1) by more
    than a factor of two. -/
theorem binary_speed_superluminal :
    2 < binaryOrbitRadius*binaryAngularVelocity := by
  unfold binaryOrbitRadius binaryAngularVelocity
  have := Real.pi_gt_three
  nlinarith

/-- The Newtonian circular angular velocity of two masses ½ at separation 14
    is `√(M/d³) = 1/√2744`. The prescribed angular velocity is more than 18
    times larger, so the 18-second period is not the gravitational period of
    the modelled binary in the declared units (Kepler gives `2π√2744 ≈ 329`). -/
theorem binary_faster_than_kepler :
    18*(1/Real.sqrt 2744) < binaryAngularVelocity := by
  unfold binaryAngularVelocity
  have hpi := Real.pi_gt_d2
  have hs : (52:ℝ) < Real.sqrt 2744 := by
    rw [show (52:ℝ) = Real.sqrt (52^2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hpos : (0:ℝ) < Real.sqrt 2744 := by positivity
  rw [mul_one_div, div_lt_iff₀ hpos]
  nlinarith

/-- The resulting consistency statement for D3: the unit conversion is exact
    for positive scales, the fixed step is exactly representable, and the
    prescribed binary clock is inconsistent with both relativity (speed > c)
    and Newtonian gravity (period ≠ Kepler period) in those same units. -/
theorem timing_resolution :
    (15625:ℝ)/1000000 = 1/2^6 ∧ 2 < binaryOrbitRadius*binaryAngularVelocity ∧
      18*(1/Real.sqrt 2744) < binaryAngularVelocity :=
  ⟨fixed_step_exact, binary_speed_superluminal, binary_faster_than_kepler⟩

end BlackHole.Units
