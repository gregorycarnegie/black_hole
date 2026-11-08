use super::{
    Kerr, Observation, State, Unresolved,
    interval::Interval as I,
    step::{MAX_TICKS, TICKS_PER_UNIT},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Outcome {
    Captured,
    Escaped,
    AffineLimit,
    Unresolved(Unresolved),
}

#[derive(Clone, Copy, Debug)]
pub struct Trace {
    pub state: State,
    pub outcome: Outcome,
    pub accepted: usize,
    pub rejected: usize,
    pub observation: Option<Observation>,
}

impl Kerr {
    fn events(&self, enclosure: [I; 11]) -> (I, I) {
        let x = [enclosure[0], enclosure[1], enclosure[2]];
        let clearance = self.geometry(x).radius - self.horizon();
        let radius2 = x.into_iter().fold(I::ZERO, |s, x| s + x.square());
        (clearance, radius2)
    }

    /// Stop at a separated event or affine limit; ambiguous or exhausted traces stay unresolved.
    pub fn trace(&self, initial: State, until: u64) -> Trace {
        let mut trace = Trace {
            state: initial,
            outcome: Outcome::Unresolved(Unresolved::InvalidInput),
            accepted: 0,
            rejected: 0,
            observation: None,
        };
        if until > MAX_TICKS
            || until < initial.ticks
            || !self.domain(initial.enclosure())
            || initial.error.iter().any(|e| !e.is_finite() || *e < 0.0)
        {
            return trace;
        }
        // 1/500 is enclosed rather than rounded to a single binary64 threshold.
        let guard = I::ONE / I::point(500.0);
        let (clearance, radius2) = self.events(initial.enclosure());
        if clearance.lo < guard.hi || radius2.hi >= 1600.0 * 1600.0 {
            trace.outcome = Outcome::Unresolved(Unresolved::EventBoundary);
            return trace;
        }
        let mut ticks = 32 * TICKS_PER_UNIT;
        while trace.accepted < 10_000 {
            let remaining = until - trace.state.ticks;
            if remaining == 0 {
                trace.outcome = Outcome::AffineLimit;
                return trace;
            }
            ticks = ticks.min(1u64 << (63 - remaining.leading_zeros()));
            loop {
                let failure = match self.try_step(trace.state, ticks) {
                    Ok(step) => {
                        let (end_clearance, end_radius2) = self.events(step.end.enclosure());
                        let (tube_clearance, tube_radius2) =
                            self.events(step.tube.map(|x| I::new(x[0], x[1])));
                        let captured =
                            end_clearance.hi < guard.lo && tube_radius2.hi < 1600.0 * 1600.0;
                        let escaped =
                            end_radius2.lo > 1600.0 * 1600.0 && tube_clearance.lo > guard.hi;
                        let no_event =
                            tube_clearance.lo > guard.hi && tube_radius2.hi < 1600.0 * 1600.0;
                        if captured || escaped || no_event {
                            let output = if escaped {
                                self.observe(step.end, [0.0; 3]).map(Some)
                            } else {
                                Ok(None)
                            };
                            match output {
                                Ok(observation) => {
                                    trace.state = step.end;
                                    trace.accepted += 1;
                                    trace.observation = observation;
                                    if captured || escaped {
                                        trace.outcome = if captured {
                                            Outcome::Captured
                                        } else {
                                            Outcome::Escaped
                                        };
                                        return trace;
                                    }
                                    ticks = (ticks * 2).min(32 * TICKS_PER_UNIT);
                                    break;
                                }
                                Err(reason) => reason,
                            }
                        } else {
                            Unresolved::EventBoundary
                        }
                    }
                    Err(reason) => reason,
                };
                trace.rejected += 1;
                if ticks == 1 {
                    trace.outcome = Outcome::Unresolved(failure);
                    return trace;
                }
                ticks /= 2;
            }
        }
        trace.outcome = Outcome::Unresolved(Unresolved::StepLimit);
        trace
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use googletest::prelude::*;
    use rstest::rstest;

    #[test]
    fn multiple_steps_enclose_the_radial_solution() {
        let kerr = Kerr::new([0.0; 3]).unwrap();
        let initial =
            State::exact([4.0, 0.0, 0.0, 1.0, -3.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0]).unwrap();
        let trace = kerr.trace(initial, TICKS_PER_UNIT / 4);
        assert_that!(trace.outcome, eq(Outcome::AffineLimit), "{trace:?}");
        assert_that!(trace.accepted, gt(1));
        assert_that!(trace.rejected, gt(0));
        let r = 4.0 - trace.state.affine();
        assert_that!(trace.state.phase[0], near(r, trace.state.error[0]));
        let p = -(r + 2.0) / (r - 2.0);
        assert_that!(trace.state.phase[4], near(p, trace.state.error[4]));
    }

    #[test]
    fn classifies_an_outgoing_radial_ray() {
        let kerr = Kerr::new([0.0; 3]).unwrap();
        // This exact null ray has r'=1, p_t=1, p_r=1.
        let initial =
            State::exact([1599.0, 0.0, 0.0, 1.0, 1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0]).unwrap();
        let trace = kerr.trace(initial, 4 * TICKS_PER_UNIT);
        assert_that!(trace.outcome, eq(Outcome::Escaped), "{trace:?}");
        let r = 1599.0 + trace.state.affine();
        assert_that!(trace.state.phase[0], near(r, trace.state.error[0]));
        assert_that!(trace.state.phase[0] - trace.state.error[0], gt(1600.0));
    }

    #[rstest]
    #[case::schwarzschild([0.0; 3], [100.0, 0.0, 0.0], [1.0, 0.0, 0.0])]
    #[case::arbitrary_spin([0.2, -0.7, 0.3], [100.0, 10.0, -20.0], [1.0, 0.4, 0.2])]
    fn admitted_cameras_escape_with_checked_observables(
        #[case] spin: [f64; 3],
        #[case] position: [f64; 3],
        #[case] direction: [f64; 3],
    ) {
        let kerr = Kerr::new(spin).unwrap();
        let initial = kerr
            .initialize(position, direction, [0.0, 1.0, 0.0])
            .unwrap();
        let trace = kerr.trace(initial, 2000 * TICKS_PER_UNIT);
        assert_that!(trace.outcome, eq(Outcome::Escaped), "{trace:?}");
        let observation = trace.observation.unwrap();
        assert_that!(observation.direction_error_radians, le(1e-6));
        assert_that!(observation.redshift_relative_error, le(1e-6));
    }

    #[test]
    fn capture_trace_remains_sound_when_the_budget_runs_out() {
        let kerr = Kerr::new([0.0; 3]).unwrap();
        let initial = kerr
            .initialize([3.0, 0.0, 0.0], [-1.0, 0.0, 0.0], [0.0, 1.0, 0.0])
            .unwrap();
        let trace = kerr.trace(initial, 4 * TICKS_PER_UNIT);
        assert_that!(
            trace.outcome,
            any![
                eq(Outcome::Captured),
                matches_pattern!(Outcome::Unresolved(_))
            ],
            "{trace:?}"
        );
        assert_that!(trace.accepted, gt(0));
        let r = 3.0 - initial.phase[3] * trace.state.affine();
        let p = -initial.phase[3] * (r + 2.0) / (r - 2.0);
        assert_that!(trace.state.phase[0], near(r, trace.state.error[0]));
        assert_that!(trace.state.phase[4], near(p, trace.state.error[4]));
        if trace.outcome == Outcome::Captured {
            assert_that!(r, lt(2.002));
        }
    }
}
