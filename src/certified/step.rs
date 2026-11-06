use super::{
    field::{Kerr, Phase},
    interval::Interval as I,
    scalar::{Dual, Jet},
};

// All affine times are integer multiples of 2^-30, below 2^44 ticks.
pub const TICKS_PER_UNIT: u64 = 1 << 30;
pub(crate) const MAX_TICKS: u64 = 10_000 * TICKS_PER_UNIT;
const MAX_STEP_TICKS: u64 = 32 * TICKS_PER_UNIT;
const BUDGET: f64 = 1e-7;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Unresolved {
    InvalidInput,
    OutsideDomain,
    Arithmetic,
    AccuracyBudget,
    StepLimit,
    EventBoundary,
}

#[derive(Clone, Copy, Debug)]
pub struct State {
    pub phase: Phase,
    pub error: Phase,
    pub ticks: u64,
}

impl State {
    /// Exact initial data for an ODE trace; physical camera normalization is separate.
    pub fn exact(phase: Phase) -> Option<Self> {
        phase.iter().all(|x| x.is_finite()).then_some(Self {
            phase,
            error: [0.0; 11],
            ticks: 0,
        })
    }

    pub fn affine(self) -> f64 {
        self.ticks as f64 / TICKS_PER_UNIT as f64
    }

    pub(crate) fn enclosure(self) -> [I; 11] {
        std::array::from_fn(|i| I::point(self.phase[i]) + I::new(-self.error[i], self.error[i]))
    }
}

/// Inspectable quantities used by the step inclusion test.
#[derive(Clone, Debug)]
pub struct EnclosedStep {
    pub end: State,
    pub ticks: u64,
    pub polynomial: [Phase; 5],
    pub tube: [[f64; 2]; 11],
    pub residual: Phase,
    pub lipschitz: f64,
}

const BINOMIAL: [[f64; 5]; 5] = [
    [1.0, 0.0, 0.0, 0.0, 0.0],
    [1.0, 1.0, 0.0, 0.0, 0.0],
    [1.0, 2.0, 1.0, 0.0, 0.0],
    [1.0, 3.0, 3.0, 1.0, 0.0],
    [1.0, 4.0, 6.0, 4.0, 1.0],
];

fn polynomial_jet<const N: usize>(a: &[Phase; 5], time: I) -> [Jet<N>; 11] {
    let mut powers = [I::ONE; 5];
    for i in 1..5 {
        powers[i] = powers[i - 1] * time;
    }
    std::array::from_fn(|component| {
        Jet(std::array::from_fn(|k| {
            let mut sum = I::ZERO;
            for j in k..5 {
                sum = sum + I::point(BINOMIAL[j][k]) * I::point(a[j][component]) * powers[j - k];
            }
            sum
        }))
    })
}

fn next_coefficient<const N: usize>(kerr: &Kerr, a: &[Phase; 5]) -> Phase {
    let input = std::array::from_fn(|i| Jet::<N>(std::array::from_fn(|j| I::point(a[j][i]))));
    kerr.rhs(input)
        .map(|j| (j.0[N - 1] / I::point(N as f64)).midpoint())
}

fn norm_scale(phase: Phase) -> Phase {
    let x = phase[..3].iter().fold(1.0f64, |m, x| m.max(x.abs()));
    let p = phase[3..7].iter().fold(1.0f64, |m, x| m.max(x.abs()));
    let f = phase[7..].iter().fold(1.0f64, |m, x| m.max(x.abs()));
    std::array::from_fn(|i| {
        if i < 3 {
            x
        } else if i < 7 {
            p
        } else {
            f
        }
    })
}

fn norm_bound(error: Phase, scale: Phase) -> f64 {
    (0..11)
        .filter(|&i| i != 3)
        .map(|i| {
            let quotient = I::point(error[i]) / I::point(scale[i]);
            if quotient.valid() {
                quotient.hi
            } else {
                f64::INFINITY
            }
        })
        .fold(0.0, f64::max)
}

impl Kerr {
    pub(crate) fn horizon(&self) -> I {
        let a2 = self
            .spin
            .map(I::point)
            .into_iter()
            .fold(I::ZERO, |s, a| s + a.square());
        I::ONE + (I::ONE - a2).sqrt()
    }

    pub(crate) fn domain(&self, box_: [I; 11]) -> bool {
        if box_.iter().any(|x| !x.valid()) || box_[3..7].iter().any(|p| p.magnitude() > 10_000.0) {
            return false;
        }
        let norm2 = box_[..3].iter().fold(I::ZERO, |s, x| s + x.square());
        if !norm2.valid() || norm2.hi > 1632.0 * 1632.0 {
            return false;
        }
        let radius = self.geometry([box_[0], box_[1], box_[2]]).radius;
        radius.valid() && radius.lo > self.horizon().hi
    }

    /// A quartic Taylor proposal is accepted only with a residual/Jacobian enclosure.
    pub fn try_step(&self, state: State, ticks: u64) -> Result<EnclosedStep, Unresolved> {
        if !ticks.is_power_of_two()
            || ticks > MAX_STEP_TICKS
            || state.ticks > MAX_TICKS
            || state.ticks.checked_add(ticks).is_none_or(|t| t > MAX_TICKS)
            || state.phase.iter().any(|x| !x.is_finite())
            || state.error.iter().any(|x| !x.is_finite() || *x < 0.0)
        {
            return Err(Unresolved::InvalidInput);
        }
        if !self.domain(state.enclosure()) {
            return Err(Unresolved::OutsideDomain);
        }
        let h = I::point(ticks as f64 / TICKS_PER_UNIT as f64);
        if !super::dyadic::scaled_integer(h.hi, TICKS_PER_UNIT, ticks) {
            return Err(Unresolved::Arithmetic);
        }
        let mut a = [[0.0; 11]; 5];
        a[0] = state.phase;
        a[1] = next_coefficient::<1>(self, &a);
        a[2] = next_coefficient::<2>(self, &a);
        a[3] = next_coefficient::<3>(self, &a);
        a[4] = next_coefficient::<4>(self, &a);
        if a.iter().flatten().any(|x| !x.is_finite()) {
            return Err(Unresolved::Arithmetic);
        }

        let at_zero = polynomial_jet::<5>(&a, I::ZERO);
        let along = polynomial_jet::<5>(&a, I::new(0.0, h.hi));
        let rhs_zero = self.rhs(at_zero);
        let rhs_along = self.rhs(along);
        let mut hp = [I::ONE; 5];
        for k in 1..5 {
            hp[k] = hp[k - 1] * h;
        }
        let residual: Phase = std::array::from_fn(|i| {
            let mut bound = I::ZERO;
            for (k, power) in hp.iter().enumerate().take(4) {
                let coefficient = I::point((k + 1) as f64) * at_zero[i].0[k + 1] - rhs_zero[i].0[k];
                bound = bound + I::point(coefficient.magnitude()) * *power;
            }
            // Taylor's fourth-derivative remainder bound is 4 times the normalized coefficient.
            bound = bound + I::point(4.0) * I::point(rhs_along[i].0[4].magnitude()) * hp[4];
            if bound.valid() {
                bound.hi.max(0.0)
            } else {
                f64::INFINITY
            }
        });
        if residual.iter().any(|r| !r.is_finite()) {
            return Err(Unresolved::Arithmetic);
        }
        let scale = norm_scale(state.phase);
        let e0 = norm_bound(state.error, scale);
        let defect = norm_bound(residual, scale);
        // Reserve the global allowance for propagation instead of spending it on one proposal.
        if defect > 1e-12 {
            return Err(Unresolved::AccuracyBudget);
        }
        let mut trial = (I::point(2.0) * (I::point(e0) + h * I::point(defect)))
            .hi
            .max(1e-30);
        for _ in 0..8 {
            if !trial.is_finite() || trial > BUDGET * 4.0 {
                return Err(Unresolved::AccuracyBudget);
            }
            let tube: [I; 11] = std::array::from_fn(|i| {
                let r = if i == 3 {
                    I::point(state.error[3])
                } else {
                    I::point(trial) * I::point(scale[i])
                };
                along[i].0[0] + I::new(-r.hi, r.hi)
            });
            if !self.domain(tube) {
                return Err(Unresolved::OutsideDomain);
            }
            let jac = self.rhs(std::array::from_fn(|i| Dual::<11>::variable(tube[i], i)));
            if jac
                .iter()
                .any(|j| !j.value.valid() || j.derivative.iter().any(|d| !d.valid()))
            {
                return Err(Unresolved::Arithmetic);
            }
            let mut k = 0.0f64;
            let mut forcing = 0.0f64;
            for i in (0..11).filter(|&i| i != 3) {
                let mut row = I::ZERO;
                for j in (0..11).filter(|&j| j != 3) {
                    row = row
                        + I::point(jac[i].derivative[j].magnitude()) * I::point(scale[j])
                            / I::point(scale[i]);
                }
                if !row.valid() {
                    return Err(Unresolved::Arithmetic);
                }
                k = k.max(row.hi);
                let q = I::point(jac[i].derivative[3].magnitude()) * I::point(state.error[3])
                    / I::point(scale[i]);
                if !q.valid() {
                    return Err(Unresolved::Arithmetic);
                }
                forcing = forcing.max(q.hi);
            }
            let kh = I::point(k) * h;
            if !kh.valid() || kh.hi >= 0.125 {
                return Err(Unresolved::AccuracyBudget);
            }
            let e = (I::point(e0) + h * (I::point(defect) + I::point(forcing))) / (I::ONE - kh);
            if !e.valid() {
                return Err(Unresolved::Arithmetic);
            }
            if e.hi > trial {
                trial = (I::point(2.0) * I::point(e.hi)).hi;
                continue;
            }
            let end_poly = polynomial_jet::<1>(&a, h);
            let phase = end_poly.map(|j| j.0[0].midpoint());
            let error: Phase = std::array::from_fn(|i| {
                if i == 3 {
                    return state.error[3];
                }
                let evaluation = (end_poly[i].0[0] - I::point(phase[i])).magnitude();
                (I::point(scale[i]) * I::point(e.hi) + I::point(evaluation)).hi
            });
            if error.iter().any(|e| !e.is_finite()) || norm_bound(error, norm_scale(phase)) > BUDGET
            {
                return Err(Unresolved::AccuracyBudget);
            }
            return Ok(EnclosedStep {
                end: State {
                    phase,
                    error,
                    ticks: state.ticks + ticks,
                },
                ticks,
                polynomial: a,
                tube: tube.map(|i| [i.lo, i.hi]),
                residual,
                lipschitz: k,
            });
        }
        Err(Unresolved::AccuracyBudget)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn step_encloses_the_exact_radial_schwarzschild_ray() {
        let kerr = Kerr::new([0.0; 3]).unwrap();
        let start = State::exact([4.0, 0.0, 0.0, 1.0, -3.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0]).unwrap();
        let step = kerr.try_step(start, TICKS_PER_UNIT / 1024).unwrap();
        let t = step.end.affine();
        let r = 4.0 - t;
        let p = -(r + 2.0) / (r - 2.0);
        assert!((step.end.phase[0] - r).abs() <= step.end.error[0]);
        assert!((step.end.phase[4] - p).abs() <= step.end.error[4]);
        assert!(step.end.error[0] > 0.0 && step.end.error[0] < 1e-6);
        assert_eq!(step.end.error[3], 0.0);
        assert_eq!(step.end.phase[3], 1.0);
    }

    #[test]
    fn rejects_invalid_inputs_and_exhausted_accuracy() {
        let kerr = Kerr::new([0.0; 3]).unwrap();
        let mut start =
            State::exact([4.0, 0.0, 0.0, 1.0, -3.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0]).unwrap();
        assert!(matches!(
            kerr.try_step(start, 3),
            Err(Unresolved::InvalidInput)
        ));
        start.error[0] = 1.0;
        assert!(kerr.try_step(start, TICKS_PER_UNIT / 1024).is_err());
        start.error[0] = f64::NAN;
        assert!(matches!(
            kerr.try_step(start, 1),
            Err(Unresolved::InvalidInput)
        ));
    }
}
