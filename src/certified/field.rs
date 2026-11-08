use super::{interval::Interval, scalar::Scalar};

pub type Phase = [f64; 11];

/// Isolated Kerr source in G=c=M=1 units, with arbitrary spin orientation.
#[derive(Clone, Copy, Debug)]
pub struct Kerr {
    pub(crate) spin: [f64; 3],
}

pub(crate) struct Geometry<S> {
    pub radius: S,
    pub g: [[S; 4]; 4],
    pub inv: [[S; 4]; 4],
    pub dg: [[[S; 4]; 4]; 3],
}

impl Kerr {
    pub fn new(spin: [f64; 3]) -> Option<Self> {
        let norm = spin
            .map(Interval::point)
            .into_iter()
            .fold(Interval::ZERO, |s, a| s + a * a);
        (norm.valid() && norm.hi < 1.0).then_some(Self { spin })
    }

    pub(crate) fn geometry<S: Scalar>(&self, x: [S; 3]) -> Geometry<S> {
        let c = S::constant;
        let a = self.spin.map(c);
        let zero = c(0.0);
        let dot = |u: [S; 3], v: [S; 3]| (0..3).fold(zero, |s, i| s + u[i] * v[i]);
        let aa = dot(a, a);
        let ax = dot(a, x);
        let q = dot(x, x) - aa;
        let r = ((q + (q * q + c(4.0) * ax * ax).sqrt()) / c(2.0)).sqrt();
        let r2 = r * r;
        let r3 = r2 * r;
        let den = r2 * r2 + ax * ax;
        let h = r3 / den;
        let cross = [
            a[1] * x[2] - a[2] * x[1],
            a[2] * x[0] - a[0] * x[2],
            a[0] * x[1] - a[1] * x[0],
        ];
        let dr: [S; 3] = std::array::from_fn(|i| (r * x[i] + (ax / r) * a[i]) / (c(2.0) * r2 - q));
        let ell: [S; 4] = std::array::from_fn(|i| {
            if i == 0 {
                c(1.0)
            } else {
                let j = i - 1;
                (r * x[j] - cross[j] + (ax / r) * a[j]) / (r2 + aa)
            }
        });
        let dell: [[S; 4]; 3] = std::array::from_fn(|e| {
            let basis: [S; 3] = std::array::from_fn(|i| c(if i == e { 1.0 } else { 0.0 }));
            let dcross = [
                a[1] * basis[2] - a[2] * basis[1],
                a[2] * basis[0] - a[0] * basis[2],
                a[0] * basis[1] - a[1] * basis[0],
            ];
            std::array::from_fn(|i| {
                if i == 0 {
                    zero
                } else {
                    let j = i - 1;
                    (dr[e] * x[j] + r * basis[j] - dcross[j] + (a[e] / r - ax * dr[e] / r2) * a[j]
                        - ell[i] * c(2.0) * r * dr[e])
                        / (r2 + aa)
                }
            })
        });
        let dh: [S; 3] = std::array::from_fn(|e| {
            h * (c(3.0) * dr[e] / r - (c(4.0) * r3 * dr[e] + c(2.0) * ax * a[e]) / den)
        });
        let sign = |i| c(if i == 0 { -1.0 } else { 1.0 });
        let eta = |i, j| if i == j { sign(i) } else { zero };
        Geometry {
            radius: r,
            g: std::array::from_fn(|i| {
                std::array::from_fn(|j| eta(i, j) + c(2.0) * h * ell[i] * ell[j])
            }),
            inv: std::array::from_fn(|i| {
                std::array::from_fn(|j| {
                    eta(i, j) - c(2.0) * h * sign(i) * ell[i] * sign(j) * ell[j]
                })
            }),
            dg: std::array::from_fn(|e| {
                std::array::from_fn(|i| {
                    std::array::from_fn(|j| {
                        c(2.0) * dh[e] * ell[i] * ell[j]
                            + c(2.0) * h * (dell[e][i] * ell[j] + ell[i] * dell[e][j])
                    })
                })
            }),
        }
    }

    pub(crate) fn rhs<S: Scalar>(&self, state: [S; 11]) -> [S; 11] {
        let c = S::constant;
        let zero = c(0.0);
        let m = self.geometry([state[0], state[1], state[2]]);
        let p: [S; 4] = std::array::from_fn(|i| state[3 + i]);
        let f: [S; 4] = std::array::from_fn(|i| state[7 + i]);
        let mul = |matrix: [[S; 4]; 4], vector: [S; 4]| -> [S; 4] {
            std::array::from_fn(|i| (0..4).fold(zero, |s, j| s + matrix[i][j] * vector[j]))
        };
        let dot = |u: [S; 4], v: [S; 4]| (0..4).fold(zero, |s, i| s + u[i] * v[i]);
        let k = mul(m.inv, p);
        let force: [S; 3] = std::array::from_fn(|i| c(0.5) * dot(k, mul(m.dg[i], k)));
        let cov: [S; 4] = std::array::from_fn(|i| {
            let dgkf = (0..3).fold(zero, |s, e| s + k[e + 1] * mul(m.dg[e], f)[i]);
            let dgfk = (0..3).fold(zero, |s, e| s + f[e + 1] * mul(m.dg[e], k)[i]);
            let contraction = if i == 0 {
                zero
            } else {
                dot(k, mul(m.dg[i - 1], f))
            };
            dgkf + dgfk - contraction
        });
        let df = mul(m.inv, cov).map(|v| -c(0.5) * v);
        [
            k[1], k[2], k[3], zero, force[0], force[1], force[2], df[0], df[1], df[2], df[3],
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::certified::scalar::Dual;
    use googletest::prelude::*;
    use rstest::rstest;

    #[rstest]
    #[case::radial_velocity_position(0, 0, -0.5)]
    #[case::radial_velocity_momentum(0, 4, 0.5)]
    #[case::radial_force_position(4, 0, 0.5)]
    #[case::radial_force_momentum(4, 4, 0.5)]
    fn source_and_jacobian_match_the_exact_radial_reduction(
        #[case] i: usize,
        #[case] j: usize,
        #[case] value: f64,
    ) {
        let kerr = Kerr::new([0.0; 3]).unwrap();
        let state = [4.0, 0.0, 0.0, 1.0, -3.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0];
        assert_eq!(
            kerr.rhs(state),
            [-1.0, 0.0, 0.0, 0.0, -1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]
        );
        let jac = kerr.rhs(std::array::from_fn(|i| {
            Dual::<11>::variable(Interval::point(state[i]), i)
        }));
        let d = jac[i].derivative[j];
        assert!(d.valid());
        assert_that!(
            d,
            pat!(Interval {
                lo: le(value),
                hi: ge(value)
            })
        );
    }
}
