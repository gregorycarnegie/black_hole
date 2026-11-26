//! CPU certificate for the GPU early-capture guard (`inward_kerr_capture` in
//! `tools/cuda/kernels.rs`), evaluated with exact-dyadic-checked intervals.

use super::interval::Interval;

/// Most pieces of `[horizon, r]` on which the radial potential is bounded; as on the
/// GPU, 1, 2, 4 and then 8 equal pieces are tried.
pub const CAPTURE_PIECES: u32 = 8;

/// Whether the exact real values of a stored binary32 Kerr-Schild state satisfy the
/// hypotheses of `null_radial_positive_near` (`verification/BlackHole/KerrCapture.lean`)
/// on every piece of `[horizon, r]`, with `r` below `disk_inner` and an inward radial
/// tangent. Unit
/// mass at the origin, spin `spin` along +y; `p` is `(p_t, p_x, p_y, p_z)`. Only the
/// soundness conditions are checked, not the GPU's margins, so every GPU capture must
/// pass. False when an enclosure cannot decide.
pub fn capture_certified(spin: f32, disk_inner: f32, pos: [f32; 3], p: [f32; 4]) -> bool {
    let point = |v: f32| Interval::point(f64::from(v));
    let constant = Interval::point;
    let one = Interval::ONE;
    let a = point(spin);
    let a2 = a.square();
    let horizon = one + (one - a2).sqrt();
    let [x, y, z] = pos.map(point);
    let rho2 = x.square() + z.square();
    let y2 = y.square();
    let q = rho2 + y2 - a2;
    let r2 = (q + (q.square() + constant(4.0) * a2 * y2).sqrt()) * constant(0.5);
    let r = r2.sqrt();
    let r2a2 = r2 + a2;
    let sine = (rho2 / r2a2).sqrt();
    let pt = point(p[0]);
    let energy = -pt;
    let [px, py, pz] = [p[1], p[2], p[3]].map(point);
    let lambda = (z * px - x * pz) / energy;
    let polar = ((y / r) / sine * (x * px + z * pz) - r * sine * py) / energy;
    let azimuthal = lambda / sine - a * sine;
    let carter = polar.square() + azimuthal.square();
    let aa = a2 - a * lambda;
    // Pieces that cover [horizon.lo, r.hi] contain [horizon, r].
    let covered = horizon.valid()
        && r.valid()
        && [1, 2, 4, CAPTURE_PIECES]
            .into_iter()
            .any(|n| radial_pieces_certified(horizon.lo, r.hi, n, aa, carter, a2));
    let h = r * r2 / (r2.square() + (a * y).square());
    let lx = (r * x - a * z) / r2a2;
    let ly = y / r;
    let lz = (r * z + a * x) / r2a2;
    let k = constant(2.0) * h * (lx * px + ly * py + lz * pz - pt);
    let (vx, vy, vz) = (px - k * lx, py - k * ly, pz - k * lz);
    let sigma_dr = r * (x * vx + (one + a2 / r2) * y * vy + z * vz) / pt;
    // NaN endpoints of a failed enclosure make every comparison false.
    p[0] > 0.0
        && r.lo > horizon.hi
        && r.hi < f64::from(disk_inner)
        && sine.lo > 0.0
        && covered
        && sigma_dr.hi < 0.0
}

/// Whether `radial_piece_certified` holds on each of `n` pieces of `[lo, hi]` that share
/// their knots, so that they cover it.
fn radial_pieces_certified(
    lo: f64,
    hi: f64,
    n: u32,
    aa: Interval,
    k: Interval,
    a2: Interval,
) -> bool {
    let knot = |j: u32| {
        if j == n {
            hi
        } else {
            lo + (hi - lo) * (f64::from(j) / f64::from(n))
        }
    };
    (1..=n).all(|j| radial_piece_certified(knot(j - 1), knot(j), aa, k, a2))
}

/// Whether either lower bound of `null_radial_positive_near` is positive on `[s0, s1]`,
/// expanding `R(s) = (s^2 + A)^2 - Delta(s) K` about the midpoint; `A = a^2 - a lambda`.
fn radial_piece_certified(s0: f64, s1: f64, aa: Interval, k: Interval, a2: Interval) -> bool {
    let constant = Interval::point;
    let abs = |x: Interval| {
        if x.lo >= 0.0 {
            x
        } else if x.hi <= 0.0 {
            -x
        } else {
            Interval::new(0.0, x.magnitude())
        }
    };
    let c = (constant(s0) + constant(s1)) * constant(0.5);
    let w = (constant(s1) - constant(s0)) * constant(0.5);
    let c2 = c.square();
    let p = c2 + aa;
    let r0 = p.square() - (c2 - constant(2.0) * c + a2) * k;
    let r1 = constant(4.0) * c * p - (constant(2.0) * c - constant(2.0)) * k;
    let h = constant(6.0) * c2 + constant(2.0) * aa - k;
    let w2 = w.square();
    let low = r0 - constant(4.0) * c * (w2 * w);
    let min_zero = Interval::new(h.lo.min(0.0), h.hi.min(0.0));
    let linear = low - abs(r1) * w + min_zero * w2;
    // NaN endpoints of a failed enclosure make every comparison false.
    linear.lo > 0.0 || (h.lo > 0.0 && (constant(4.0) * h * low - r1.square()).lo > 0.0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

    // Spin 0 at (3, 0, 0): l# = (-1, 1, 0, 0) and h = 1/3, so the null roots are
    // p_x = p_t (outgoing, dr/dlambda = 1) and p_x = -5 p_t (ingoing, dr/dlambda = -1,
    // where (Sigma dr/dlambda)^2 = 81 = R(3)).
    #[rstest]
    #[case::ingoing([1.0, -5.0, 0.0, 0.0], 6.0, true)]
    #[case::outgoing([1.0, 1.0, 0.0, 0.0], 6.0, false)]
    #[case::inside_the_disk_edge([1.0, -5.0, 0.0, 0.0], 3.0, false)]
    #[case::forward_ray([-1.0, 5.0, 0.0, 0.0], 6.0, false)]
    fn radial_rays(#[case] p: [f32; 4], #[case] disk_inner: f32, #[case] certified: bool) {
        assert_eq!(
            capture_certified(0.0, disk_inner, [3.0, 0.0, 0.0], p),
            certified
        );
    }

    fn radial(a: f64, lambda: f64, k: f64, s: f64) -> f64 {
        let p = s * s + a * a - a * lambda;
        p * p - (s * s - 2.0 * s + a * a) * k
    }

    fn pieces_certified(a: f64, lambda: f64, k: f64, lo: f64, hi: f64) -> bool {
        let point = Interval::point;
        let aa = point(a) * point(a) - point(a) * point(lambda);
        radial_pieces_certified(lo, hi, CAPTURE_PIECES, aa, point(k), point(a) * point(a))
    }

    // The slowest ray of the default 400x300 view (pixel 183, 153; 1,248 iterations): a
    // captured ray with R >= 0.079 below the guard's entry radius r1 - 0.05 = 2.75. The
    // former single bound P(h)^2 - Delta(r) K was -17 there.
    #[test]
    fn near_critical_capture_is_certified_at_entry() {
        let (a, lambda, k) = (0.82_f64, 3.01153, 6.41101);
        let horizon = 1.0 + (1.0 - a * a).sqrt();
        assert!(pieces_certified(a, lambda, k, horizon, 2.75));
        let p = horizon * horizon + a * a - a * lambda;
        assert!(p * p - (2.75 * 2.75 - 5.5 + a * a) * k < -17.0);
    }

    proptest::proptest! {
        /// Soundness: a certified piece has R > 0 at every sampled point.
        #[test]
        fn certified_pieces_have_no_turning_point(
            a in -0.999..0.999_f64,
            lambda in -8.0..8.0_f64,
            k in 0.0..80.0_f64,
            s0 in 1.0..6.0_f64,
            width in 1.0e-3..3.0_f64,
        ) {
            let point = Interval::point;
            let aa = point(a) * point(a) - point(a) * point(lambda);
            if radial_piece_certified(s0, s0 + width, aa, point(k), point(a) * point(a)) {
                for i in 0..=256 {
                    let s = s0 + width * f64::from(i) / 256.0;
                    proptest::prop_assert!(radial(a, lambda, k, s) > 0.0, "R({s}) <= 0");
                }
            }
        }

        /// Near the double root of a critical orbit, R_min is the margin; pieces certify
        /// once it is a little above the cubic remainder 4 c w^3.
        #[test]
        fn pieces_reject_a_turning_point(
            a in -0.99..0.99_f64,
            lambda in -6.0..6.0_f64,
            k in 1.0..60.0_f64,
        ) {
            let horizon = 1.0 + (1.0 - a * a).sqrt();
            let hi = horizon + 2.0;
            let turns = (0..=4096).any(|i| radial(a, lambda, k, horizon + 2.0 * f64::from(i) / 4096.0) <= 0.0);
            if turns {
                proptest::prop_assert!(!pieces_certified(a, lambda, k, horizon, hi));
            }
        }
    }

    #[test]
    fn spin_beyond_extremal_is_undecided() {
        assert!(!capture_certified(
            1.5,
            6.0,
            [3.0, 0.0, 0.0],
            [1.0, -5.0, 0.0, 0.0]
        ));
    }
}
