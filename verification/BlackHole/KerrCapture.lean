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

/-- The unit-mass null radial potential is a quartic in `s`; its Taylor expansion
about `c` is exact. -/
theorem null_radial_expand (a l k c t : ℝ) :
    ((c+t)^2 + a^2 - a*l)^2 - delta a (c+t) * k
      = ((c^2 + a^2 - a*l)^2 - delta a c * k)
        + (4*c*(c^2 + a^2 - a*l) - (2*c - 2)*k) * t
        + (6*c^2 + 2*(a^2 - a*l) - k) * t^2 + 4*c*t^3 + t^4 := by
  unfold delta; ring

/-- The piecewise capture bound: on `|s - c| ≤ w` with `c ≥ 0`, either lower bound
of the expansion excludes a radial turning point. The first takes each term at its
worst; the second takes the quadratic part's minimum over all `t` (written without
division). Both drop `t^4 ≥ 0` and bound `4 c t^3` below by `-4 c w^3`. -/
theorem null_radial_positive_near {a l k c w t : ℝ} (hc : 0 ≤ c) (ht : |t| ≤ w)
    (hb : 0 < ((c^2 + a^2 - a*l)^2 - delta a c * k)
            - |4*c*(c^2 + a^2 - a*l) - (2*c - 2)*k| * w
            + min (6*c^2 + 2*(a^2 - a*l) - k) 0 * w^2 - 4*c*w^3
        ∨ (0 < 6*c^2 + 2*(a^2 - a*l) - k ∧
           0 < 4*(6*c^2 + 2*(a^2 - a*l) - k)
                 * (((c^2 + a^2 - a*l)^2 - delta a c * k) - 4*c*w^3)
               - (4*c*(c^2 + a^2 - a*l) - (2*c - 2)*k)^2)) :
    0 < ((c+t)^2 + a^2 - a*l)^2 - delta a (c+t) * k := by
  rw [null_radial_expand]
  set R0 := (c^2 + a^2 - a*l)^2 - delta a c * k
  set R1 := 4*c*(c^2 + a^2 - a*l) - (2*c - 2)*k
  set H := 6*c^2 + 2*(a^2 - a*l) - k
  obtain ⟨htl, htu⟩ := abs_le.mp ht
  have hw : 0 ≤ w := le_trans (abs_nonneg t) ht
  have hquad : 0 ≤ t^2 - t*w + w^2 := by nlinarith [sq_nonneg (t - w/2), sq_nonneg w]
  have hcube : -(w^3) ≤ t^3 := by
    nlinarith [mul_nonneg (show 0 ≤ t + w by linarith) hquad]
  have hcubic : -(4*c*w^3) ≤ 4*c*t^3 + t^4 := by
    nlinarith [mul_le_mul_of_nonneg_left hcube (show 0 ≤ 4*c by linarith), sq_nonneg (t^2)]
  rcases hb with hb | ⟨hH, hv⟩
  · have h1 : -(|R1| * w) ≤ R1 * t := by
      calc -(|R1| * w) ≤ -(|R1| * |t|) := neg_le_neg (mul_le_mul_of_nonneg_left ht (abs_nonneg R1))
        _ = -|R1 * t| := by rw [abs_mul]
        _ ≤ R1 * t := neg_abs_le _
    have ht2 : t^2 ≤ w^2 := by
      rw [← sq_abs t]; exact pow_le_pow_left₀ (abs_nonneg t) ht 2
    have h2 : min H 0 * w^2 ≤ H * t^2 := by
      rcases le_total H 0 with h | h
      · rw [min_eq_left h]; nlinarith
      · rw [min_eq_right h]; nlinarith [sq_nonneg t]
    linarith
  · have hsq : 4*H*R0 - R1^2 ≤ 4*H*(R0 + R1*t + H*t^2) := by
      nlinarith [sq_nonneg (2*H*t + R1)]
    have hpos : 0 < 4*H*(R0 + R1*t + H*t^2 + 4*c*t^3 + t^4) := by
      nlinarith [mul_le_mul_of_nonneg_left hcubic (show 0 ≤ 4*H by linarith)]
    by_contra hneg
    replace hneg := not_lt.mp hneg
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 4*H by linarith) hneg]

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
