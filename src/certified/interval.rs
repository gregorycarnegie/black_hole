use super::dyadic;
use std::ops::{Add, Div, Mul, Neg, Sub};

/// Closed binary64 enclosure, with NaN endpoints representing a failed operation.
/// Floating proposals are checked against exact dyadic arithmetic before use.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) struct Interval {
    pub lo: f64,
    pub hi: f64,
}

impl Interval {
    pub const ZERO: Self = Self { lo: 0.0, hi: 0.0 };
    pub const ONE: Self = Self { lo: 1.0, hi: 1.0 };
    const INVALID: Self = Self {
        lo: f64::NAN,
        hi: f64::NAN,
    };

    pub fn new(lo: f64, hi: f64) -> Self {
        if lo.is_finite() && hi.is_finite() && lo <= hi {
            Self { lo, hi }
        } else {
            Self::INVALID
        }
    }

    pub fn point(x: f64) -> Self {
        Self::new(x, x)
    }

    pub fn valid(self) -> bool {
        self.lo.is_finite() && self.hi.is_finite() && self.lo <= self.hi
    }

    pub fn sqrt(self) -> Self {
        if !self.valid() || self.lo < 0.0 {
            return Self::INVALID;
        }
        if self == Self::ZERO {
            return self;
        }
        let result = Self::new(
            self.lo.sqrt().next_down().max(0.0),
            self.hi.sqrt().next_up(),
        );
        if result.valid()
            && dyadic::product_upper(result.lo, result.lo, self.lo)
            && dyadic::product_lower(result.hi, result.hi, self.hi)
        {
            result
        } else {
            Self::INVALID
        }
    }

    pub fn square(self) -> Self {
        if !self.valid() {
            return Self::INVALID;
        }
        if self == Self::ZERO || self == Self::ONE {
            return self;
        }
        let a = self.lo * self.lo;
        let b = self.hi * self.hi;
        let lo = if self.lo <= 0.0 && self.hi >= 0.0 {
            0.0
        } else {
            a.min(b).next_down().max(0.0)
        };
        let result = Self::new(lo, a.max(b).next_up());
        if result.valid()
            && dyadic::product_upper(self.lo, self.lo, result.hi)
            && dyadic::product_upper(self.hi, self.hi, result.hi)
            && (lo == 0.0
                || (dyadic::product_lower(self.lo, self.lo, lo)
                    && dyadic::product_lower(self.hi, self.hi, lo)))
        {
            result
        } else {
            Self::INVALID
        }
    }

    pub fn sum_squares<const N: usize>(values: [Self; N]) -> Self {
        let sum = values
            .into_iter()
            .fold(Self::ZERO, |sum, x| sum + x.square());
        if sum.valid() {
            Self::new(sum.lo.max(0.0), sum.hi)
        } else {
            Self::INVALID
        }
    }

    pub fn reciprocal(self) -> Self {
        if !self.valid() || (self.lo <= 0.0 && 0.0 <= self.hi) {
            Self::INVALID
        } else if self == Self::ONE {
            self
        } else {
            let result = Self::new((1.0 / self.hi).next_down(), (1.0 / self.lo).next_up());
            if result.valid()
                && dyadic::reciprocal_lower(self.hi, result.lo)
                && dyadic::reciprocal_upper(self.lo, result.hi)
            {
                result
            } else {
                Self::INVALID
            }
        }
    }

    pub fn magnitude(self) -> f64 {
        if self.valid() {
            self.lo.abs().max(self.hi.abs())
        } else {
            f64::INFINITY
        }
    }

    pub fn midpoint(self) -> f64 {
        // Halving first also works when the sum of finite endpoints overflows.
        if self.valid() {
            (0.5 * self.lo + 0.5 * self.hi).clamp(self.lo, self.hi)
        } else {
            f64::NAN
        }
    }
}

impl Neg for Interval {
    type Output = Self;

    fn neg(self) -> Self {
        Self {
            lo: -self.hi,
            hi: -self.lo,
        }
    }
}

impl Add for Interval {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        if !self.valid() || !rhs.valid() {
            Self::INVALID
        } else if self == Self::ZERO {
            rhs
        } else if rhs == Self::ZERO {
            self
        } else {
            let result = Self::new((self.lo + rhs.lo).next_down(), (self.hi + rhs.hi).next_up());
            if result.valid()
                && dyadic::sum_lower(self.lo, rhs.lo, result.lo)
                && dyadic::sum_upper(self.hi, rhs.hi, result.hi)
            {
                result
            } else {
                Self::INVALID
            }
        }
    }
}

impl Sub for Interval {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        self + -rhs
    }
}

impl Mul for Interval {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        if !self.valid() || !rhs.valid() {
            return Self::INVALID;
        }
        if self == Self::ZERO || rhs == Self::ZERO {
            return Self::ZERO;
        }
        if self == Self::ONE {
            return rhs;
        }
        if rhs == Self::ONE {
            return self;
        }
        let p = [
            self.lo * rhs.lo,
            self.lo * rhs.hi,
            self.hi * rhs.lo,
            self.hi * rhs.hi,
        ];
        if p.iter().any(|p| !p.is_finite()) {
            return Self::INVALID;
        }
        let lo = p.into_iter().fold(f64::INFINITY, f64::min).next_down();
        let hi = p.into_iter().fold(f64::NEG_INFINITY, f64::max).next_up();
        let result = Self::new(lo, hi);
        if result.valid()
            && [self.lo, self.hi].into_iter().all(|a| {
                [rhs.lo, rhs.hi]
                    .into_iter()
                    .all(|b| dyadic::product_lower(a, b, lo) && dyadic::product_upper(a, b, hi))
            })
        {
            result
        } else {
            Self::INVALID
        }
    }
}

#[allow(
    clippy::suspicious_arithmetic_impl,
    reason = "Interval division multiplies by an enclosed reciprocal"
)]
impl Div for Interval {
    type Output = Self;

    fn div(self, rhs: Self) -> Self {
        self * rhs.reciprocal()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_rational::BigRational;
    use proptest::prelude::*;
    use rstest::rstest;

    fn rat(x: f64) -> BigRational {
        BigRational::from_float(x).unwrap()
    }

    fn encloses(i: Interval, x: BigRational) -> bool {
        !i.valid() || (rat(i.lo) <= x && x <= rat(i.hi))
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(512))]

        #[test]
        fn rounded_operations_enclose_exact_rationals(a in any::<u64>(), b in any::<u64>()) {
            let a = f64::from_bits(a);
            let b = f64::from_bits(b);
            prop_assume!(a.is_finite() && b.is_finite());
            let (ia, ib) = (Interval::point(a), Interval::point(b));
            prop_assert!(encloses(ia + ib, rat(a) + rat(b)));
            prop_assert!(encloses(ia - ib, rat(a) - rat(b)));
            prop_assert!(encloses(ia * ib, rat(a) * rat(b)));
            if b != 0.0 {
                prop_assert!(encloses(ia / ib, rat(a) / rat(b)));
            }
        }

        #[test]
        fn sqrt_bounds_are_verified_by_exact_squares(bits in any::<u64>()) {
            let x = f64::from_bits(bits & !(1 << 63));
            prop_assume!(x.is_finite());
            let r = Interval::point(x).sqrt();
            prop_assert!(r.valid());
            prop_assert!(r.lo >= 0.0);
            prop_assert!(rat(r.lo) * rat(r.lo) <= rat(x));
            prop_assert!(rat(x) <= rat(r.hi) * rat(r.hi));
        }
    }

    proptest! {
        #[test]
        fn interval_corners_are_enclosed(a in -100.0f64..100.0, b in -100.0f64..100.0,
            c in -100.0f64..100.0, d in -100.0f64..100.0) {
            let x = Interval::new(a.min(b), a.max(b));
            let y = Interval::new(c.min(d), c.max(d));
            prop_assert!((x + y).valid() && (x - y).valid() && (x * y).valid());
            prop_assert!(x.square().valid());
            for u in [x.lo,x.hi,0.5*x.lo+0.5*x.hi] {
                prop_assert!(encloses(x.square(),rat(u)*rat(u)));
            }
            if x.lo<=0.0 && x.hi>=0.0 {
                prop_assert!(x.square().lo==0.0);
            }
            for u in [x.lo, x.hi] {
                for v in [y.lo, y.hi] {
                    prop_assert!(encloses(x + y, rat(u) + rat(v)));
                    prop_assert!(encloses(x - y, rat(u) - rat(v)));
                    prop_assert!(encloses(x * y, rat(u) * rat(v)));
                    if y.lo > 1e-10 || y.hi < -1e-10 {
                        prop_assert!((x / y).valid());
                        prop_assert!(encloses(x / y, rat(u) / rat(v)));
                    }
                }
            }
        }
    }

    #[rstest]
    #[case::division_through_zero(Interval::ONE / Interval::new(-1.0, 1.0))]
    #[case::negative_sqrt(Interval::new(-1.0, 4.0).sqrt())]
    #[case::overflow(Interval::point(f64::MAX) * Interval::point(2.0))]
    #[case::nan_product(Interval::ZERO * Interval::point(f64::NAN))]
    #[case::reversed_endpoints(Interval::new(2.0, 1.0))]
    fn invalid_domains_never_become_certificates(#[case] result: Interval) {
        assert!(!result.valid(), "{result:?}");
    }

    #[rstest]
    #[case::sqrt_of_zero(Interval::ZERO.sqrt(), Interval::ZERO)]
    #[case::one_times_max(Interval::ONE * Interval::point(f64::MAX), Interval::point(f64::MAX))]
    fn exact_identities_preserve_boundary_values(
        #[case] actual: Interval,
        #[case] expected: Interval,
    ) {
        assert_eq!(actual, expected);
    }
}
