use super::interval::Interval;
use std::ops::{Add, Div, Mul, Neg, Sub};

/// One source expression is evaluated at points, intervals and derivative jets.
pub(crate) trait Scalar:
    Copy
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Div<Output = Self>
    + Neg<Output = Self>
{
    fn constant(x: f64) -> Self;
    fn sqrt(self) -> Self;
}

impl Scalar for f64 {
    fn constant(x: f64) -> Self {
        x
    }
    fn sqrt(self) -> Self {
        f64::sqrt(self)
    }
}

impl Scalar for Interval {
    fn constant(x: f64) -> Self {
        Self::point(x)
    }
    fn sqrt(self) -> Self {
        self.sqrt()
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct Dual<const N: usize> {
    pub value: Interval,
    pub derivative: [Interval; N],
}

impl<const N: usize> Dual<N> {
    pub fn variable(value: Interval, axis: usize) -> Self {
        Self {
            value,
            derivative: std::array::from_fn(|i| {
                if i == axis {
                    Interval::ONE
                } else {
                    Interval::ZERO
                }
            }),
        }
    }
}

impl<const N: usize> Scalar for Dual<N> {
    fn constant(x: f64) -> Self {
        Self {
            value: Interval::point(x),
            derivative: [Interval::ZERO; N],
        }
    }
    fn sqrt(self) -> Self {
        let root = self.value.sqrt();
        Self {
            value: root,
            derivative: self.derivative.map(|d| d / (Interval::point(2.0) * root)),
        }
    }
}

impl<const N: usize> Add for Dual<N> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self {
            value: self.value + rhs.value,
            derivative: std::array::from_fn(|i| self.derivative[i] + rhs.derivative[i]),
        }
    }
}
impl<const N: usize> Neg for Dual<N> {
    type Output = Self;
    fn neg(self) -> Self {
        Self {
            value: -self.value,
            derivative: self.derivative.map(Neg::neg),
        }
    }
}
impl<const N: usize> Sub for Dual<N> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        self + -rhs
    }
}
#[allow(
    clippy::suspicious_arithmetic_impl,
    reason = "The product rule adds both derivative terms"
)]
impl<const N: usize> Mul for Dual<N> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        Self {
            value: self.value * rhs.value,
            derivative: std::array::from_fn(|i| {
                self.derivative[i] * rhs.value + self.value * rhs.derivative[i]
            }),
        }
    }
}
#[allow(
    clippy::suspicious_arithmetic_impl,
    reason = "The quotient rule subtracts the denominator derivative"
)]
impl<const N: usize> Div for Dual<N> {
    type Output = Self;
    fn div(self, rhs: Self) -> Self {
        let value = self.value / rhs.value;
        Self {
            value,
            derivative: std::array::from_fn(|i| {
                (self.derivative[i] - value * rhs.derivative[i]) / rhs.value
            }),
        }
    }
}

/// Coefficient k encloses the k-th derivative divided by k!.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Jet<const N: usize>(pub [Interval; N]);

impl<const N: usize> Scalar for Jet<N> {
    fn constant(x: f64) -> Self {
        let mut c = [Interval::ZERO; N];
        c[0] = Interval::point(x);
        Self(c)
    }
    fn sqrt(self) -> Self {
        let mut c = [Interval::ZERO; N];
        c[0] = self.0[0].sqrt();
        for k in 1..N {
            let mut cross = Interval::ZERO;
            for i in 1..k {
                cross = cross + c[i] * c[k - i];
            }
            c[k] = (self.0[k] - cross) / (Interval::point(2.0) * c[0]);
        }
        Self(c)
    }
}
impl<const N: usize> Add for Jet<N> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self(std::array::from_fn(|i| self.0[i] + rhs.0[i]))
    }
}
impl<const N: usize> Neg for Jet<N> {
    type Output = Self;
    fn neg(self) -> Self {
        Self(self.0.map(Neg::neg))
    }
}
impl<const N: usize> Sub for Jet<N> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        self + -rhs
    }
}
impl<const N: usize> Mul for Jet<N> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        Self(std::array::from_fn(|k| {
            let mut sum = Interval::ZERO;
            for i in 0..=k {
                sum = sum + self.0[i] * rhs.0[k - i];
            }
            sum
        }))
    }
}
impl<const N: usize> Div for Jet<N> {
    type Output = Self;
    fn div(self, rhs: Self) -> Self {
        let mut c = [Interval::ZERO; N];
        for k in 0..N {
            let mut cross = Interval::ZERO;
            for i in 1..=k {
                cross = cross + rhs.0[i] * c[k - i];
            }
            c[k] = (self.0[k] - cross) / rhs.0[0];
        }
        Self(c)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use googletest::prelude::*;
    use rstest::rstest;

    #[rstest]
    #[case::constant(0, 1.0, 1.0)]
    #[case::linear(1, 0.5, -1.0)]
    #[case::quadratic(2, -0.125, 1.0)]
    #[case::cubic(3, 0.0625, -1.0)]
    #[case::quartic(4, -5.0 / 128.0, 1.0)]
    fn jets_enclose_known_analytic_coefficients(
        #[case] i: usize,
        #[case] root_coefficient: f64,
        #[case] inverse_coefficient: f64,
    ) {
        let x = Jet([
            Interval::ONE,
            Interval::ONE,
            Interval::ZERO,
            Interval::ZERO,
            Interval::ZERO,
        ]);
        let root = x.sqrt();
        let inverse = Jet::constant(1.0) / x;
        assert!(root.0[i].valid() && inverse.0[i].valid());
        assert_that!(
            root.0[i],
            pat!(Interval {
                lo: le(root_coefficient),
                hi: ge(root_coefficient)
            })
        );
        assert_that!(
            inverse.0[i],
            pat!(Interval {
                lo: le(inverse_coefficient),
                hi: ge(inverse_coefficient)
            })
        );
    }

    #[test]
    fn duals_enclose_chain_rule() {
        let x = Dual::<2>::variable(Interval::point(4.0), 0);
        let y = Dual::<2>::variable(Interval::point(2.0), 1);
        let z = (x / y).sqrt();
        let encloses = |x: f64| {
            pat!(Interval {
                lo: le(x),
                hi: ge(x)
            })
        };
        assert!(z.value.valid() && z.derivative.iter().all(|d| d.valid()));
        assert_that!(z.value, encloses(2.0f64.sqrt()));
        assert_that!(z.derivative[0], encloses(1.0 / (4.0 * 2.0f64.sqrt())));
        assert_that!(z.derivative[1], encloses(-1.0 / (2.0 * 2.0f64.sqrt())));
    }
}
