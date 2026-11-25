//! The analytic escape leg (checklist P1.8): from an outgoing state far from the hole
//! to Kerr–Schild radius `target`, with only `sqrt` and a hand-written `sin_cos`, so
//! the CUDA kernel can repeat it line for line (`analytic_escape` in
//! `tools/cuda/kernels.rs`).
//!
//! Past the last radial turning point R(r) = r⁴ f(1/r) with f bounded away from zero,
//! so the radial Mino-time integrals are smooth in u = 1/r and a short Gauss–Legendre
//! sum suffices. The polar motion c = cos θ obeys the turning-point-free ODE
//! c'' = -(η + λ² - a²) c - 2a² c³, integrated with classical RK4 together with
//! ∫ dτ / (1 - c²). Rays that come near the pole, or whose radial factor is small, are
//! left to the numerical integrator.

/// Gauss–Legendre nodes and weights on [-1, 1], positive half.
const GL_NODES: [f64; 4] = [
    0.183_434_642_495_649_8,
    0.525_532_409_916_329,
    0.796_666_477_413_626_7,
    0.960_289_856_497_536_3,
];
const GL_WEIGHTS: [f64; 4] = [
    0.362_683_783_378_362,
    0.313_706_645_877_887_3,
    0.222_381_034_453_374_5,
    0.101_228_536_290_376_3,
];

/// RK4 steps of the polar motion.
pub const POLAR_STEPS: usize = 8;
/// Smallest f(u) = R / r⁴ accepted on the path (1 at infinity, cos² of the radial
/// angle in flat space).
pub const RADIAL_FLOOR: f64 = 0.5;
/// Smallest sin²θ accepted at either end, where the azimuth and p_θ are formed.
pub const POLAR_FLOOR: f64 = 1.0e-6;

/// sin x and cos x for |x| up to about 1e9, from Taylor polynomials on [-π/4, π/4].
pub fn sin_cos(x: f64) -> (f64, f64) {
    const PIO2_LO: f64 = 6.123_233_995_736_766e-17;
    let k = (x * std::f64::consts::FRAC_2_PI + if x >= 0.0 { 0.5 } else { -0.5 }) as i64;
    let kf = k as f64;
    let r = (x - kf * std::f64::consts::FRAC_PI_2) - kf * PIO2_LO;
    let r2 = r * r;
    // Horner forms of the series to r¹⁷ and r¹⁶; the next terms are below 2e-17.
    let s = r
        * (1.0
            + r2 * (-1.0 / 6.0
                + r2 * (1.0 / 120.0
                    + r2 * (-1.0 / 5040.0
                        + r2 * (1.0 / 362_880.0
                            + r2 * (-1.0 / 39_916_800.0
                                + r2 * (1.0 / 6_227_020_800.0
                                    + r2 * (-1.0 / 1_307_674_368_000.0
                                        + r2 / 355_687_428_096_000.0))))))));
    let c = 1.0
        + r2 * (-0.5
            + r2 * (1.0 / 24.0
                + r2 * (-1.0 / 720.0
                    + r2 * (1.0 / 40_320.0
                        + r2 * (-1.0 / 3_628_800.0
                            + r2 * (1.0 / 479_001_600.0
                                + r2 * (-1.0 / 87_178_291_200.0 + r2 / 20_922_789_888_000.0)))))));
    match k & 3 {
        0 => (s, c),
        1 => (c, -s),
        2 => (-s, -c),
        _ => (-c, s),
    }
}

/// The state at Kerr–Schild radius `target` of the ray at `pos` with covariant
/// momentum `p` (conventions of [`super::propagate`]), or `None` when the ray is not
/// outgoing past its turning points or the guards above reject it.
#[allow(
    clippy::neg_cmp_op_on_partial_ord,
    reason = "NaN must fail every guard"
)]
pub fn far_escape(
    spin: f64,
    pos: [f64; 3],
    p: [f64; 4],
    target: f64,
) -> Option<([f64; 3], [f64; 4])> {
    let a = spin;
    let a2 = a * a;
    let [x, y, z] = pos;
    // Spin axis Z: (X, Y, Z) = (z, x, y).
    let (big_x, big_y, big_z) = (z, x, y);
    let (p_x, p_y, p_z) = (p[3], p[1], p[2]);
    let rho2 = big_x * big_x + big_y * big_y;
    let q = rho2 + big_z * big_z - a2;
    let r2 = 0.5 * (q + (q * q + 4.0 * a2 * big_z * big_z).sqrt());
    let r = r2.sqrt();
    let cos = big_z / r;
    let sin2 = rho2 / (r2 + a2);
    // NaN-safe: every guard is written so that NaN fails it.
    if !(r < target && sin2 > POLAR_FLOOR && a2 < 1.0) {
        return None;
    }
    let sin = sin2.sqrt();
    // e^{iφ} = (X + iY)(r - ia) / ((r² + a²) sin θ).
    let norm = 1.0 / ((r2 + a2) * sin);
    let (cp, sp) = (
        (big_x * r + big_y * a) * norm,
        (big_y * r - big_x * a) * norm,
    );
    let p_r = sin * (cp * p_x + sp * p_y) + cos * p_z;
    let p_theta = cos / sin * (big_x * p_x + big_y * p_y) - r * sin * p_z;
    let energy = -p[0];
    let angular = z * p[1] - x * p[3];
    let carter = p_theta * p_theta + cos * cos * (angular * angular / sin2 - a2 * energy * energy);
    let lambda = angular / energy;
    let eta = carter / (energy * energy);
    let e_abs = energy.abs();
    let delta = r2 - 2.0 * r + a2;
    // Boyer–Lindquist p_r is positive going out.
    if !(p_r - (2.0 * r * energy - a * angular) / delta > 0.0) {
        return None;
    }

    // Radial integrals over u in [1/target, 1/r]: Mino time, the Boyer–Lindquist
    // azimuth term ∫ a(2r - aλ)/Δ dτ and the Kerr–Schild shift ∫ a dr/Δ.
    let (fa, fb, fc) = (
        a2 - eta - lambda * lambda,
        2.0 * (eta + (lambda - a) * (lambda - a)),
        -a2 * eta,
    );
    let f = |u: f64| {
        let u2 = u * u;
        1.0 + u2 * (fa + u * (fb + u * fc))
    };
    let (u_end, u_start) = (1.0 / target, 1.0 / r);
    let (mid, half) = (0.5 * (u_start + u_end), 0.5 * (u_start - u_end));
    let mut floor = f(u_start).min(f(u_end));
    // The sums and the polar stages run in binary32, which is 64 times faster on consumer
    // GPUs: each contributes a small increment, so its relative error stays below 1e-7
    // of a quantity that is itself small. The conserved quantities, the start and the
    // rebuild need binary64, where they cancel.
    let (fa32, fb32, fc32, a32, lambda32) =
        (fa as f32, fb as f32, fc as f32, a as f32, lambda as f32);
    let (mid32, half32) = (mid as f32, half as f32);
    let (mut mino, mut phi_radial, mut ks_shift) = (0.0_f32, 0.0_f32, 0.0_f32);
    for i in 0..4 {
        for side in [-1.0_f32, 1.0] {
            let u = mid32 + side * half32 * GL_NODES[i] as f32;
            let fu = 1.0 + u * u * (fa32 + u * (fb32 + u * fc32));
            floor = floor.min(f64::from(fu));
            let weight = GL_WEIGHTS[i] as f32;
            let w = weight / fu.sqrt();
            let delta_u = 1.0 - 2.0 * u + a32 * a32 * u * u;
            mino += w;
            phi_radial += w * a32 * u * (2.0 - a32 * lambda32 * u) / delta_u;
            ks_shift += weight * a32 / delta_u;
        }
    }
    if !(floor > RADIAL_FLOOR) {
        return None;
    }
    let (mino, phi_radial, ks_shift) = (
        f64::from(mino) * half,
        f64::from(phi_radial) * half,
        f64::from(ks_shift) * half,
    );

    // Polar motion over Mino time `mino`, as a unit vector n = (sin θ cos ψ, sin θ sin ψ,
    // cos θ) with ψ the polar part of the azimuth, dψ/dτ = L / (|E| sin²θ). It moves on the
    // sphere under the potential -a² n_z² / 2, so n'' = -|n'|² n + a² n_z (ẑ - n_z n),
    // which stays regular through the pole. The state accumulates in binary64.
    let theta_rate = p_theta / e_abs;
    let mut n = [sin, 0.0, cos];
    let mut dn = [cos * theta_rate, angular / (e_abs * sin), -sin * theta_rate];
    let a2_32 = a2 as f32;
    let accel = |n: [f32; 3], dn: [f32; 3]| {
        let speed2 = dn[0] * dn[0] + dn[1] * dn[1] + dn[2] * dn[2];
        let pull = a2_32 * n[2];
        let radial = speed2 + pull * n[2];
        [-radial * n[0], -radial * n[1], pull - radial * n[2]]
    };
    let h = (mino / POLAR_STEPS as f64) as f32;
    for _ in 0..POLAR_STEPS {
        let n1 = n.map(|v| v as f32);
        let d1 = dn.map(|v| v as f32);
        let k1 = accel(n1, d1);
        let n2: [f32; 3] = std::array::from_fn(|i| n1[i] + 0.5 * h * d1[i]);
        let d2: [f32; 3] = std::array::from_fn(|i| d1[i] + 0.5 * h * k1[i]);
        let k2 = accel(n2, d2);
        let n3: [f32; 3] = std::array::from_fn(|i| n1[i] + 0.5 * h * d2[i]);
        let d3: [f32; 3] = std::array::from_fn(|i| d1[i] + 0.5 * h * k2[i]);
        let k3 = accel(n3, d3);
        let n4: [f32; 3] = std::array::from_fn(|i| n1[i] + h * d3[i]);
        let d4: [f32; 3] = std::array::from_fn(|i| d1[i] + h * k3[i]);
        let k4 = accel(n4, d4);
        for i in 0..3 {
            n[i] += f64::from(h / 6.0 * (d1[i] + 2.0 * d2[i] + 2.0 * d3[i] + d4[i]));
            dn[i] += f64::from(h / 6.0 * (k1[i] + 2.0 * k2[i] + 2.0 * k3[i] + k4[i]));
        }
    }
    let length = (n[0] * n[0] + n[1] * n[1] + n[2] * n[2]).sqrt();
    let c = n[2] / length;
    let rho = (n[0] * n[0] + n[1] * n[1]).sqrt();
    let sin = rho / length;
    if !(sin * sin > POLAR_FLOOR) {
        return None;
    }
    let sign_e = if energy < 0.0 { -1.0 } else { 1.0 };
    let (sd, cd) = sin_cos(sign_e * phi_radial + ks_shift);
    // Rotate by the radial azimuth, then by ψ.
    let (cp, sp) = (cp * cd - sp * sd, sp * cd + cp * sd);
    let (cpsi, spsi) = (n[0] / rho, n[1] / rho);
    let (cp, sp) = (cp * cpsi - sp * spsi, sp * cpsi + cp * spsi);

    // Rebuild the Cartesian state at `target`, as `super::rebuild`.
    let r = target;
    let v = dn[2] / length;
    let delta = r * r - 2.0 * r + a2;
    let radial = r * r * r * r * f(u_end);
    let p_theta = -e_abs * v / sin;
    let p_r = (e_abs * radial.sqrt() + 2.0 * r * energy - a * angular) / delta;
    let big_x = (r * cp - a * sp) * sin;
    let big_y = (r * sp + a * cp) * sin;
    let big_z = r * c;
    let j = [
        [cp * sin, sp * sin, c],
        [(r * cp - a * sp) * c, (r * sp + a * cp) * c, -r * sin],
        [-(r * sp + a * cp) * sin, (r * cp - a * sp) * sin, 0.0],
    ];
    let rhs = [p_r, p_theta, angular];
    let det3 = |m: [[f64; 3]; 3]| {
        m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
            - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
            + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0])
    };
    let inv_det = 1.0 / det3(j);
    let solve = |col: usize| {
        let mut m = j;
        for row in 0..3 {
            m[row][col] = rhs[row];
        }
        det3(m) * inv_det
    };
    let (p_x, p_y, p_z) = (solve(0), solve(1), solve(2));
    Some(([big_y, big_z, big_x], [-energy, p_y, p_z, p_x]))
}

#[cfg(test)]
mod tests {
    use super::super::tests::{angle, camera_ray};
    use super::super::{Method, Outcome, direction, propagate};
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn sin_cos_matches_the_standard_library(x in -1.0e4f64..1.0e4) {
            let (s, c) = sin_cos(x);
            let (rs, rc) = x.sin_cos();
            prop_assert!((s - rs).abs() < 4.0e-16 * x.abs().max(1.0) && (c - rc).abs() < 4.0e-16 * x.abs().max(1.0));
        }

        #[test]
        fn far_escape_matches_the_separated_solution(
            spin in -0.99f64..0.99,
            radius in 12.0f64..800.0,
            at in (0.05f64..3.09, -3.1f64..3.1),
            (tilt, turn) in (0.0f64..0.32, -3.1f64..3.1),
            backward in any::<bool>(),
        ) {
            // Outward, tilted by up to 0.32 rad from radial.
            let (pos, p) = camera_ray(spin, radius, at, (std::f64::consts::PI - tilt, turn), backward);
            let reference = propagate(spin, pos, p, 1600.0, Method::Quadrature);
            match (far_escape(spin, pos, p, 1600.0), reference) {
                (Some((position, momentum)), Ok(Outcome::Arrived { position: x, momentum: px })) => {
                    let gap = (0..3).map(|i| (position[i] - x[i]).abs()).fold(0.0, f64::max);
                    let turn = angle(direction(spin, position, momentum), direction(spin, x, px));
                    prop_assert!(gap < 1.0e-7 * 1600.0 && turn < 2.0e-7, "gap {gap}, turn {turn}");
                }
                // The reference leaves vortical and near-polar rays unresolved.
                (Some(_), Err(_)) => {}
                (None, _) => prop_assert!(false, "rejected"),
                (Some(_), other) => prop_assert!(false, "reference {other:?}"),
            }
        }
    }
}
