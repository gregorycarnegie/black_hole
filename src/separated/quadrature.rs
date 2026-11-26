//! Tanh–sinh (double-exponential) quadrature, accurate for integrands with
//! square-root singularities at the endpoints.

use std::f64::consts::FRAC_PI_2;

/// ∫ₐᵇ f. The integrand receives the point and its exact distances from `a` and `b`,
/// so it can form factors like (x - a) without cancellation near an endpoint.
pub fn tanh_sinh(f: impl Fn(f64, f64, f64) -> f64, a: f64, b: f64) -> f64 {
    if a == b {
        return 0.0;
    }
    let (lo, hi, sign) = if a < b { (a, b, 1.0) } else { (b, a, -1.0) };
    let half = 0.5 * (hi - lo);
    // The integrand sees distances from a and from b, whichever way round they lie.
    let eval = |t: f64| {
        let u = FRAC_PI_2 * t.sinh();
        let d_lo = 2.0 * half / (1.0 + (-2.0 * u).exp());
        let d_hi = 2.0 * half / (1.0 + (2.0 * u).exp());
        if d_lo == 0.0 || d_hi == 0.0 {
            return 0.0;
        }
        let x = if t < 0.0 { lo + d_lo } else { hi - d_hi };
        let weight = half * FRAC_PI_2 * t.cosh() / u.cosh().powi(2);
        let value = if sign > 0.0 {
            f(x, d_lo, d_hi)
        } else {
            f(x, d_hi, d_lo)
        };
        weight * value
    };
    const T_MAX: f64 = 4.0;
    let mut h = 1.0;
    let mut sum = eval(0.0);
    let mut k = 1.0;
    while k * h <= T_MAX {
        sum += eval(k * h) + eval(-k * h);
        k += 1.0;
    }
    let mut estimate = sum * h;
    for level in 1..14 {
        h *= 0.5;
        let mut k = 1.0;
        while k * h <= T_MAX {
            sum += eval(k * h) + eval(-k * h);
            k += 2.0;
        }
        let next = sum * h;
        let converged = (next - estimate).abs() <= 1.0e-15 * next.abs();
        estimate = next;
        if level >= 3 && converged {
            break;
        }
    }
    sign * estimate
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

    #[rstest]
    #[case::polynomial(|x: f64, _, _| x * x, 0.0, 3.0, 9.0)]
    #[case::reversed(|x: f64, _, _| x * x, 3.0, 0.0, -9.0)]
    // ∫₋₁¹ dx / √(1 - x²) = π, with the factors from the exact endpoint distances.
    #[case::arcsine(|_, da: f64, db: f64| 1.0 / (da * db).sqrt(), -1.0, 1.0, std::f64::consts::PI)]
    #[case::arcsine_reversed(|_, da: f64, db: f64| 1.0 / (da * db).sqrt(), 1.0, -1.0, -std::f64::consts::PI)]
    fn integrates_known_cases(
        #[case] f: fn(f64, f64, f64) -> f64,
        #[case] a: f64,
        #[case] b: f64,
        #[case] expected: f64,
    ) {
        let value = tanh_sinh(f, a, b);
        assert!(
            (value - expected).abs() < 1.0e-14 * expected.abs(),
            "{value}"
        );
    }
}
