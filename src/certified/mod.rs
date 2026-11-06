//! Validated single-hole Kerr trajectories. An unsuccessful enclosure is unresolved.
//! This N2 workbench's remaining proof and integration gaps are in verification/n2-certificates.md.

mod camera;
mod dyadic;
mod field;
mod interval;
mod observe;
mod scalar;
mod step;
mod trace;
pub use field::{Kerr, Phase};
pub use observe::Observation;
pub use step::{EnclosedStep, State, TICKS_PER_UNIT, Unresolved};
pub use trace::{Outcome, Trace};
