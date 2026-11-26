//! Legendre and Jacobi elliptic functions in binary64, from Carlson's symmetric
//! integrals (Carlson 1995, "Numerical computation of real or complex elliptic
//! integrals") and the arithmetic–geometric mean (Abramowitz & Stegun 16.4). The
//! parameter `m` may be negative; amplitudes may be any real number.

use std::f64::consts::PI;

/// Relative truncation target of the duplication series.
const TOLERANCE: f64 = 1.0e-16;

/// Carlson's R_F(x, y, z) for nonnegative arguments, at most one zero.
pub fn rf(x: f64, y: f64, z: f64) -> f64 {
    let (mut x, mut y, mut z) = (x, y, z);
    let a0 = (x + y + z) / 3.0;
    let q =
        (3.0 * TOLERANCE).powf(-1.0 / 6.0) * (a0 - x).abs().max((a0 - y).abs()).max((a0 - z).abs());
    let (x0, y0) = (x, y);
    let mut a = a0;
    let mut scale = 1.0;
    while scale * q >= a.abs() {
        let (sx, sy, sz) = (x.sqrt(), y.sqrt(), z.sqrt());
        let lambda = sx * sy + sy * sz + sz * sx;
        a = 0.25 * (a + lambda);
        x = 0.25 * (x + lambda);
        y = 0.25 * (y + lambda);
        z = 0.25 * (z + lambda);
        scale *= 0.25;
    }
    let dx = (a0 - x0) * scale / a;
    let dy = (a0 - y0) * scale / a;
    let dz = -dx - dy;
    let e2 = dx * dy - dz * dz;
    let e3 = dx * dy * dz;
    (1.0 - e2 / 10.0 + e3 / 14.0 + e2 * e2 / 24.0 - 3.0 * e2 * e3 / 44.0) / a.sqrt()
}

/// R_C(1, 1 + e) for e > -1.
fn rc_one(e: f64) -> f64 {
    if e > 1.0e-8 {
        e.sqrt().atan() / e.sqrt()
    } else if e < -1.0e-8 {
        (-e).sqrt().atanh() / (-e).sqrt()
    } else {
        1.0 - e / 3.0 + e * e / 5.0
    }
}

/// Carlson's R_J(x, y, z, p) for nonnegative x, y, z (at most one zero) and p > 0.
pub fn rj(x: f64, y: f64, z: f64, p: f64) -> f64 {
    let (mut x, mut y, mut z, mut p) = (x, y, z, p);
    let a0 = (x + y + z + 2.0 * p) / 5.0;
    let delta = (p - x) * (p - y) * (p - z);
    let q = (0.25 * TOLERANCE).powf(-1.0 / 6.0)
        * (a0 - x)
            .abs()
            .max((a0 - y).abs())
            .max((a0 - z).abs())
            .max((a0 - p).abs());
    let (x0, y0, z0) = (x, y, z);
    let mut a = a0;
    let mut scale = 1.0;
    let mut sum = 0.0;
    while scale * q >= a.abs() {
        let (sx, sy, sz, sp) = (x.sqrt(), y.sqrt(), z.sqrt(), p.sqrt());
        let lambda = sx * sy + sy * sz + sz * sx;
        let d = (sp + sx) * (sp + sy) * (sp + sz);
        let e = scale * scale * scale * delta / (d * d);
        sum += scale * rc_one(e) / d;
        a = 0.25 * (a + lambda);
        x = 0.25 * (x + lambda);
        y = 0.25 * (y + lambda);
        z = 0.25 * (z + lambda);
        p = 0.25 * (p + lambda);
        scale *= 0.25;
    }
    let dx = (a0 - x0) * scale / a;
    let dy = (a0 - y0) * scale / a;
    let dz = (a0 - z0) * scale / a;
    let dp = -0.5 * (dx + dy + dz);
    let e2 = dx * dy + dx * dz + dy * dz - 3.0 * dp * dp;
    let e3 = dx * dy * dz + 2.0 * e2 * dp + 4.0 * dp * dp * dp;
    let e4 = (2.0 * dx * dy * dz + e2 * dp + 3.0 * dp * dp * dp) * dp;
    let e5 = dx * dy * dz * dp * dp;
    let series = 1.0 - 3.0 * e2 / 14.0 + e3 / 6.0 + 9.0 * e2 * e2 / 88.0
        - 3.0 * e4 / 22.0
        - 9.0 * e2 * e3 / 52.0
        + 3.0 * e5 / 26.0;
    scale * series / (a * a.sqrt()) + 6.0 * sum
}

/// Splits an amplitude into `j` half-periods and a remainder in [-π/2, π/2].
fn reduce(phi: f64) -> (f64, f64) {
    let j = (phi / PI).round();
    (j, phi - j * PI)
}

/// Complete integral of the first kind K(m), m < 1.
pub fn complete_f(m: f64) -> f64 {
    rf(0.0, 1.0 - m, 1.0)
}

/// Legendre F(φ | m) for any real φ and m < 1.
pub fn legendre_f(phi: f64, m: f64) -> f64 {
    let (j, phi) = reduce(phi);
    let (s, c) = phi.sin_cos();
    let part = s * rf(c * c, 1.0 - m * s * s, 1.0);
    if j == 0.0 {
        part
    } else {
        2.0 * j * complete_f(m) + part
    }
}

/// Legendre Π(n; φ | m) = ∫₀^φ dθ / ((1 - n sin²θ) √(1 - m sin²θ)), for m < 1 and
/// 1 - n sin²θ > 0 along the path. Amplitudes past ±π/2 need n < 1.
pub fn legendre_pi(n: f64, phi: f64, m: f64) -> f64 {
    legendre_pi_near_one(n, 1.0 - n, phi, m)
}

/// `legendre_pi` with 1 - n supplied, so n close to 1 keeps its precision.
pub fn legendre_pi_near_one(n: f64, one_minus_n: f64, phi: f64, m: f64) -> f64 {
    let (j, phi) = reduce(phi);
    let (s, c) = phi.sin_cos();
    let (s2, c2) = (s * s, c * c);
    // 1 - n sin²φ = cos²φ + (1 - n) sin²φ.
    let part = s * rf(c2, 1.0 - m * s2, 1.0)
        + n / 3.0 * s * s2 * rj(c2, 1.0 - m * s2, 1.0, c2 + one_minus_n * s2);
    if j == 0.0 {
        part
    } else {
        let complete = rf(0.0, 1.0 - m, 1.0) + n / 3.0 * rj(0.0, 1.0 - m, 1.0, one_minus_n);
        2.0 * j * complete + part
    }
}

/// Jacobi amplitude am(u | m) for any real u and m < 1, by the descending AGM.
pub fn amplitude(u: f64, m: f64) -> f64 {
    if m == 0.0 {
        return u;
    }
    let mut a = [0.0_f64; 32];
    let mut c = [0.0_f64; 32];
    a[0] = 1.0;
    let mut b = (1.0 - m).sqrt();
    let mut n = 0;
    while n < 31 {
        let next = 0.5 * (a[n] + b);
        c[n + 1] = 0.5 * (a[n] - b);
        b = (a[n] * b).sqrt();
        a[n + 1] = next;
        n += 1;
        if c[n].abs() <= 1.0e-17 * a[n] {
            break;
        }
    }
    let mut phi = (1u64 << n) as f64 * a[n] * u;
    for i in (1..=n).rev() {
        phi = 0.5 * (phi + (c[i] / a[i] * phi.sin()).asin());
    }
    phi
}

#[cfg(test)]
mod tests {
    use super::super::quadrature::tanh_sinh;
    use super::*;
    use proptest::prelude::*;
    use rstest::rstest;

    fn close(a: f64, b: f64, tolerance: f64) -> bool {
        (a - b).abs() <= tolerance * b.abs().max(1.0)
    }

    #[rstest]
    #[case::circle(0.0, std::f64::consts::FRAC_PI_2)]
    #[case::half(0.5, 1.854_074_677_301_371_9)]
    #[case::negative(-1.0, 1.311_028_777_146_059_9)]
    #[case::near_one(0.99, 3.695_637_362_989_874_8)]
    fn complete_first_kind_matches_tabulated_values(#[case] m: f64, #[case] k: f64) {
        assert!(
            close(complete_f(m), k, 1.0e-15),
            "{} against {k}",
            complete_f(m)
        );
    }

    proptest! {
        #[test]
        fn legendre_f_matches_quadrature(phi in -7.0f64..7.0, m in -20.0f64..0.999) {
            let direct = tanh_sinh(|t, _, _| 1.0 / (1.0 - m * t.sin().powi(2)).sqrt(), 0.0, phi);
            prop_assert!(close(legendre_f(phi, m), direct, 1.0e-13));
        }

        #[test]
        fn legendre_pi_matches_quadrature(
            phi in -7.0f64..7.0, m in -20.0f64..0.99, n in -5.0f64..0.99,
        ) {
            let direct = tanh_sinh(
                |t, _, _| {
                    let s2 = t.sin().powi(2);
                    1.0 / ((1.0 - n * s2) * (1.0 - m * s2).sqrt())
                },
                0.0,
                phi,
            );
            prop_assert!(close(legendre_pi(n, phi, m), direct, 1.0e-12));
        }

        #[test]
        fn amplitude_inverts_legendre_f(phi in -20.0f64..20.0, m in -30.0f64..0.999) {
            let back = amplitude(legendre_f(phi, m), m);
            prop_assert!((back - phi).abs() <= 1.0e-11 * phi.abs().max(1.0), "{back} against {phi}");
        }
    }
}
