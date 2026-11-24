module

public import BlackHole.KerrGeodesics
import Mathlib.Tactic.Linarith

@[expose] public section
noncomputable section

namespace BlackHole.Kerr

/-- For unit mass, the lower bound used by the capture experiment excludes a
radial turning point on `[h, r]` for the exact separated null equation. -/
theorem null_radial_positive_below {a l k h r s : ℝ}
    (hh : 1 ≤ h) (hhs : h ≤ s) (hsr : s ≤ r) (hk : 0 ≤ k)
    (hp : 0 ≤ h^2 + a^2 - a*l)
    (hb : 0 < (h^2 + a^2 - a*l)^2 - delta a r*k) :
    0 < (s^2 + a^2 - a*l)^2 - delta a s*k := by
  have hs : h^2 ≤ s^2 := pow_le_pow_left₀ (by linarith) hhs 2
  have hps : h^2 + a^2 - a*l ≤ s^2 + a^2 - a*l := by linarith
  have hdelta : delta a s ≤ delta a r := by
    unfold delta
    nlinarith [mul_nonneg (sub_nonneg.mpr hsr) (show 0 ≤ r+s-2 by linarith)]
  exact lt_of_lt_of_le hb
    (sub_le_sub (pow_le_pow_left₀ hp hps 2) (mul_le_mul_of_nonneg_right hdelta hk))

/-- The squared equatorial radius used by the prescribed disk is bounded by
the squared Kerr radius when the disk is aligned with the source. -/
theorem projected_disk_radius_sq_le (r a sinSq : ℝ) (hs : sinSq ≤ 1) :
    max 0 ((r^2 + a^2)*sinSq - a^2) ≤ r^2 := by
  apply max_le (sq_nonneg r)
  have h := mul_le_mul_of_nonneg_left hs (show 0 ≤ r^2 + a^2 by positivity)
  linarith

/-- An outward chord cannot enter a sphere centered at the ray-tracing origin. -/
theorem outward_chord_radius_sq_le (x y z dx dy dz t : ℝ)
    (ht : 0 ≤ t) (hout : 0 ≤ x*dx + y*dy + z*dz) :
    x^2 + y^2 + z^2 ≤ (x+t*dx)^2 + (y+t*dy)^2 + (z+t*dz)^2 := by
  have hlin := mul_nonneg ht hout
  have hquad := mul_nonneg (sq_nonneg t) (show 0 ≤ dx^2 + dy^2 + dz^2 by positivity)
  nlinarith

end BlackHole.Kerr
