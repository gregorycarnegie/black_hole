/// Schwarzschild radius of Sagittarius A* in metres (2GM/c²).
pub const SAGA_RS: f32 = 1.269e10;

const KERR_SPIN_LIMIT: f32 = 0.999;

/// Kerr event-horizon radius r₊ = M(1 + √(1 − a²)) in metres.
///
/// At zero spin this equals the full Schwarzschild radius (r_s = 2M = `SAGA_RS`).
/// Increasing |a| shrinks the horizon; at the extremal limit (a → 1) it
/// approaches M = `SAGA_RS / 2`.
///
/// The spin is silently clamped to the range (−0.999, 0.999) to avoid the
/// coordinate singularity at a = ±1.
///
/// # Examples
///
/// ```
/// use black_hole::physics::{kerr_horizon_radius, SAGA_RS};
///
/// // Schwarzschild limit: horizon equals the full Schwarzschild radius.
/// let r_h = kerr_horizon_radius(0.0);
/// assert!((r_h / SAGA_RS - 1.0).abs() < 1e-5);
/// ```
///
/// ```
/// use black_hole::physics::{kerr_horizon_radius, SAGA_RS};
///
/// // Near-extremal spin: horizon shrinks but stays positive.
/// let r_h = kerr_horizon_radius(0.999);
/// assert!(r_h > 0.0 && r_h < SAGA_RS);
/// ```
///
/// ```
/// use black_hole::physics::kerr_horizon_radius;
///
/// // Horizon radius depends only on |a| — prograde and retrograde are symmetric.
/// assert!((kerr_horizon_radius(0.7) - kerr_horizon_radius(-0.7)).abs() < 1.0);
/// ```
pub fn kerr_horizon_radius(spin: f32) -> f32 {
    let a = spin.abs().min(KERR_SPIN_LIMIT);
    0.5 * SAGA_RS * (1.0 + (1.0 - a * a).sqrt())
}

/// Kerr ISCO radius using the Bardeen-Press-Teukolsky formula, in metres.
///
/// For prograde orbits (spin > 0) the ISCO lies inside the Schwarzschild value
/// of 3 r_s (= 6M); for retrograde orbits (spin < 0) it moves outward, up to
/// 9 r_s at the extremal limit. The ISCO is always outside the event horizon.
///
/// The spin is clamped to (−0.999, 0.999).
///
/// # Examples
///
/// ```
/// use black_hole::physics::{kerr_isco_radius, SAGA_RS};
///
/// // Schwarzschild limit: ISCO = 3 r_s = 6M.
/// let r_isco = kerr_isco_radius(0.0);
/// assert!((r_isco / (3.0 * SAGA_RS) - 1.0).abs() < 1e-4);
/// ```
///
/// ```
/// use black_hole::physics::{kerr_isco_radius, kerr_horizon_radius};
///
/// // ISCO is always outside the event horizon.
/// for &a in &[-0.9_f32, -0.5, 0.0, 0.5, 0.9] {
///     assert!(kerr_isco_radius(a) > kerr_horizon_radius(a),
///         "ISCO inside horizon at a={a}");
/// }
/// ```
///
/// ```
/// use black_hole::physics::{kerr_isco_radius, SAGA_RS};
///
/// // Prograde spin moves ISCO inward; retrograde moves it outward.
/// assert!(kerr_isco_radius(0.9) < 3.0 * SAGA_RS);
/// assert!(kerr_isco_radius(-0.9) > 3.0 * SAGA_RS);
/// ```
pub fn kerr_isco_radius(spin: f32) -> f32 {
    let a = spin.clamp(-KERR_SPIN_LIMIT, KERR_SPIN_LIMIT);
    let abs_a = a.abs();
    let z1 = 1.0
        + (1.0 - abs_a * abs_a).powf(1.0 / 3.0)
            * ((1.0 + abs_a).powf(1.0 / 3.0) + (1.0 - abs_a).powf(1.0 / 3.0));
    let z2 = (3.0 * abs_a * abs_a + z1 * z1).sqrt();
    let direction = if a >= 0.0 { -1.0 } else { 1.0 };
    let r_over_m = 3.0 + z2 + direction * ((3.0 - z1) * (3.0 + z1 + 2.0 * z2)).sqrt();
    0.5 * SAGA_RS * r_over_m
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    // ── Unit tests ───────────────────────────────────────────────────────────

    #[test]
    fn horizon_equals_schwarzschild_at_zero_spin() {
        let r_h = kerr_horizon_radius(0.0);
        assert!(
            (r_h / SAGA_RS - 1.0).abs() < 1e-5,
            "expected r_h ≈ SAGA_RS ({SAGA_RS}), got {r_h}"
        );
    }

    #[test]
    fn horizon_shrinks_monotonically_with_spin() {
        let r0 = kerr_horizon_radius(0.0);
        let r5 = kerr_horizon_radius(0.5);
        let r9 = kerr_horizon_radius(0.9);
        assert!(r0 > r5, "r_h(0)={r0} should be > r_h(0.5)={r5}");
        assert!(r5 > r9, "r_h(0.5)={r5} should be > r_h(0.9)={r9}");
    }

    #[test]
    fn horizon_symmetric_in_spin_sign() {
        for &a in &[0.1_f32, 0.5, 0.8, 0.999] {
            let rp = kerr_horizon_radius(a);
            let rm = kerr_horizon_radius(-a);
            assert!(
                (rp - rm).abs() < 1.0,
                "horizon should be symmetric: r_h({a})={rp}, r_h(-{a})={rm}"
            );
        }
    }

    #[test]
    fn horizon_always_positive() {
        for &a in &[-0.999_f32, -0.5, 0.0, 0.5, 0.999] {
            assert!(
                kerr_horizon_radius(a) > 0.0,
                "horizon non-positive at a={a}"
            );
        }
    }

    #[test]
    fn isco_equals_three_rs_at_zero_spin() {
        let r_isco = kerr_isco_radius(0.0);
        let expected = 3.0 * SAGA_RS;
        assert!(
            (r_isco / expected - 1.0).abs() < 1e-4,
            "expected r_isco ≈ {expected}, got {r_isco}"
        );
    }

    #[test]
    fn prograde_spin_moves_isco_inward() {
        let r_schw = 3.0 * SAGA_RS;
        for &a in &[0.1_f32, 0.5, 0.82, 0.999] {
            let r = kerr_isco_radius(a);
            assert!(
                r < r_schw,
                "prograde a={a}: r_isco={r} should be < {r_schw}"
            );
        }
    }

    #[test]
    fn retrograde_spin_moves_isco_outward() {
        let r_schw = 3.0 * SAGA_RS;
        for &a in &[-0.1_f32, -0.5, -0.82, -0.999] {
            let r = kerr_isco_radius(a);
            assert!(
                r > r_schw,
                "retrograde a={a}: r_isco={r} should be > {r_schw}"
            );
        }
    }

    #[test]
    fn isco_outside_horizon_at_known_spins() {
        for &a in &[-0.999_f32, -0.5, 0.0, 0.5, 0.82, 0.999] {
            let r_h = kerr_horizon_radius(a);
            let r_isco = kerr_isco_radius(a);
            assert!(
                r_isco > r_h,
                "ISCO must be outside horizon at a={a}: r_isco={r_isco}, r_h={r_h}"
            );
        }
    }

    // ── Proptest ─────────────────────────────────────────────────────────────

    proptest! {
        #[test]
        fn horizon_positive_and_bounded_by_schwarzschild(a in -0.999_f32..=0.999_f32) {
            let r_h = kerr_horizon_radius(a);
            prop_assert!(r_h > 0.0, "horizon non-positive at a={a}: {r_h}");
            // r_+ ≤ r_s with tiny float tolerance
            prop_assert!(
                r_h <= SAGA_RS * 1.000_01,
                "horizon exceeds Schwarzschild radius at a={a}: r_h={r_h}, SAGA_RS={SAGA_RS}"
            );
        }

        #[test]
        fn isco_always_outside_horizon(a in -0.999_f32..=0.999_f32) {
            let r_h = kerr_horizon_radius(a);
            let r_isco = kerr_isco_radius(a);
            prop_assert!(
                r_isco > r_h,
                "ISCO inside horizon at a={a}: r_isco={r_isco}, r_h={r_h}"
            );
        }

        #[test]
        fn prograde_isco_below_schwarzschild(a in 0.001_f32..=0.999_f32) {
            let r_isco = kerr_isco_radius(a);
            prop_assert!(
                r_isco < 3.0 * SAGA_RS,
                "prograde a={a}: r_isco={r_isco} should be < 3 r_s"
            );
        }

        #[test]
        fn retrograde_isco_above_schwarzschild(a in -0.999_f32..=-0.001_f32) {
            let r_isco = kerr_isco_radius(a);
            prop_assert!(
                r_isco > 3.0 * SAGA_RS,
                "retrograde a={a}: r_isco={r_isco} should be > 3 r_s"
            );
        }

        // Test strict monotonicity: a₁ < a₂  ⟹  r_isco(a₁) ≥ r_isco(a₂).
        // We construct a₂ = a₁ + δ with a guaranteed positive gap to avoid
        // degenerate a₁ == a₂ cases from f32 rounding.
        #[test]
        fn isco_monotone_decreasing_with_spin(
            a1 in -0.998_f32..=0.997_f32,
            delta in 0.001_f32..=0.05_f32,
        ) {
            let a2 = (a1 + delta).min(0.999);
            let r1 = kerr_isco_radius(a1);
            let r2 = kerr_isco_radius(a2);
            // 1 m tolerance for f32 rounding near the minimum
            prop_assert!(
                r1 >= r2 - 1.0,
                "ISCO not monotone: a1={a1} r1={r1}, a2={a2} r2={r2}"
            );
        }

        #[test]
        fn horizon_monotone_shrinks_with_spin(
            a1 in 0.0_f32..=0.998_f32,
            delta in 0.001_f32..=0.05_f32,
        ) {
            let a2 = (a1 + delta).min(0.999);
            let r1 = kerr_horizon_radius(a1);
            let r2 = kerr_horizon_radius(a2);
            prop_assert!(
                r1 >= r2 - 1.0,
                "horizon not monotone: a1={a1} r1={r1}, a2={a2} r2={r2}"
            );
        }

        #[test]
        fn horizon_symmetric_prograde_retrograde(a in 0.001_f32..=0.999_f32) {
            let rp = kerr_horizon_radius(a);
            let rm = kerr_horizon_radius(-a);
            prop_assert!(
                (rp - rm).abs() < 1.0,
                "horizon not symmetric: r_h({a})={rp}, r_h(-{a})={rm}"
            );
        }
    }
}
