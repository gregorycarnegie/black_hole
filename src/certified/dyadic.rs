use num_bigint::BigInt;
use std::cmp::Ordering;

// Exact finite-f64 values, including subnormals. No floating arithmetic enters comparisons.
#[derive(Clone, Copy)]
struct Dyadic {
    mantissa: i128,
    exponent: i32,
}

impl Dyadic {
    fn decode(x: f64) -> Self {
        debug_assert!(x.is_finite());
        let bits = x.to_bits();
        let exponent = ((bits >> 52) & 0x7ff) as i32;
        let fraction = bits & ((1u64 << 52) - 1);
        let mantissa = if exponent == 0 {
            fraction
        } else {
            fraction | (1u64 << 52)
        };
        Self {
            mantissa: if bits >> 63 == 0 {
                i128::from(mantissa)
            } else {
                -i128::from(mantissa)
            },
            exponent: if exponent == 0 {
                -1074
            } else {
                exponent - 1075
            },
        }
    }

    fn neg(self) -> Self {
        Self {
            mantissa: -self.mantissa,
            ..self
        }
    }

    fn mul(self, rhs: Self) -> Self {
        // The product of two finite-f64 significands has at most 106 bits.
        Self {
            mantissa: self.mantissa * rhs.mantissa,
            exponent: self.exponent + rhs.exponent,
        }
    }
}

fn sign<const N: usize>(terms: [Dyadic; N]) -> Ordering {
    let exponent = terms
        .iter()
        .filter(|t| t.mantissa != 0)
        .map(|t| t.exponent)
        .min()
        .unwrap_or(0);
    let small = terms.iter().try_fold(0i128, |sum, t| {
        if t.mantissa == 0 {
            return Some(sum);
        }
        let shift = u32::try_from(t.exponent - exponent).ok()?;
        let power = 1i128.checked_shl(shift).filter(|p| *p > 0)?;
        sum.checked_add(t.mantissa.checked_mul(power)?)
    });
    if let Some(sum) = small {
        return sum.cmp(&0);
    }
    let sum = terms
        .into_iter()
        .filter(|t| t.mantissa != 0)
        .fold(BigInt::from(0), |sum, t| {
            sum + (BigInt::from(t.mantissa) << ((t.exponent - exponent) as usize))
        });
    sum.cmp(&BigInt::from(0))
}

pub(super) fn sum_lower(a: f64, b: f64, lower: f64) -> bool {
    sign([
        Dyadic::decode(a),
        Dyadic::decode(b),
        Dyadic::decode(lower).neg(),
    ]) != Ordering::Less
}

pub(super) fn sum_upper(a: f64, b: f64, upper: f64) -> bool {
    sign([
        Dyadic::decode(a),
        Dyadic::decode(b),
        Dyadic::decode(upper).neg(),
    ]) != Ordering::Greater
}

pub(super) fn product_lower(a: f64, b: f64, lower: f64) -> bool {
    sign([
        Dyadic::decode(a).mul(Dyadic::decode(b)),
        Dyadic::decode(lower).neg(),
    ]) != Ordering::Less
}

pub(super) fn product_upper(a: f64, b: f64, upper: f64) -> bool {
    sign([
        Dyadic::decode(a).mul(Dyadic::decode(b)),
        Dyadic::decode(upper).neg(),
    ]) != Ordering::Greater
}

pub(super) fn reciprocal_lower(a: f64, lower: f64) -> bool {
    if a > 0.0 {
        product_upper(lower, a, 1.0)
    } else {
        product_lower(lower, a, 1.0)
    }
}

pub(super) fn reciprocal_upper(a: f64, upper: f64) -> bool {
    if a > 0.0 {
        product_lower(upper, a, 1.0)
    } else {
        product_upper(upper, a, 1.0)
    }
}

pub(super) fn scaled_integer(value: f64, denominator: u64, numerator: u64) -> bool {
    value.is_finite()
        && sign([
            Dyadic::decode(value).mul(Dyadic {
                mantissa: i128::from(denominator),
                exponent: 0,
            }),
            Dyadic {
                mantissa: -i128::from(numerator),
                exponent: 0,
            },
        ]) == Ordering::Equal
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_rational::BigRational as R;

    #[test]
    fn rejects_an_endpoint_on_the_wrong_side_of_the_exact_result() {
        let tiny = f64::from_bits(1);
        assert!(!sum_upper(1.0, tiny, 1.0));
        assert!(!sum_lower(1.0, tiny, 1.0f64.next_up()));
        assert!(!product_upper(
            1.0f64.next_up(),
            1.0f64.next_up(),
            1.0f64.next_up()
        ));
        assert!(scaled_integer(0.125, 1 << 30, 1 << 27));
        assert!(!scaled_integer(0.125f64.next_up(), 1 << 30, 1 << 27));
    }

    #[test]
    fn exact_comparisons_cover_extreme_exponents_and_cancellation() {
        let values = [
            0.0,
            -0.0,
            f64::from_bits(1),
            -f64::from_bits(1),
            f64::MIN_POSITIVE,
            -f64::MIN_POSITIVE,
            1.0,
            -1.0,
            1.0f64.next_up(),
            f64::MAX,
            -f64::MAX,
        ];
        for a in values {
            for b in values {
                for bound in values {
                    let ra = R::from_float(a).unwrap();
                    let rb = R::from_float(b).unwrap();
                    let rbound = R::from_float(bound).unwrap();
                    assert_eq!(sum_lower(a, b, bound), &ra + &rb >= rbound);
                    assert_eq!(sum_upper(a, b, bound), &ra + &rb <= rbound);
                    assert_eq!(product_lower(a, b, bound), &ra * &rb >= rbound);
                    assert_eq!(product_upper(a, b, bound), &ra * &rb <= rbound);
                }
            }
        }
    }
}
