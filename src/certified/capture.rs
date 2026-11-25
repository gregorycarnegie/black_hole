//! CPU certificate for the GPU early-capture guard (`inward_kerr_capture` in
//! `tools/cuda/kernels.rs`), evaluated with exact-dyadic-checked intervals.

use super::interval::Interval;

/// Whether the exact real values of a stored binary32 Kerr-Schild state satisfy the
/// hypotheses of `null_radial_positive_below` (`verification/BlackHole/KerrCapture.lean`)
/// on `[horizon, r]`, with `r` below `disk_inner` and an inward radial tangent. Unit
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
    let horizon_p = horizon.square() + a2 - a * lambda;
    let barrier = (r - horizon) * (r + horizon - constant(2.0)) * carter;
    let bound = horizon_p.square() - barrier;
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
        && horizon_p.lo > 0.0
        && bound.lo > 0.0
        && sigma_dr.hi < 0.0
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
        assert_eq!(capture_certified(0.0, disk_inner, [3.0, 0.0, 0.0], p), certified);
    }

    #[test]
    fn spin_beyond_extremal_is_undecided() {
        assert!(!capture_certified(1.5, 6.0, [3.0, 0.0, 0.0], [1.0, -5.0, 0.0, 0.0]));
    }
}
