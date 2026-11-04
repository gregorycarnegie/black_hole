//! Exhaustive binary32 checks for the Kerr horizon and ISCO functions.
//!
//! Every one of the 2³² `f32` bit patterns is evaluated, including both
//! zeros, subnormals, infinities and every NaN payload. Run with
//!
//! ```sh
//! cargo test --release --test exhaustive_binary32 -- --ignored
//! ```
//!
//! The binary64 references use the same cancellation-free formulas. The
//! Lean theorems in `verification/BlackHole/Binary32Bounds.lean` bound their
//! own rounding error below 10⁻¹³ relative, far inside the margins used here.
//! The asserted limits are the measured maxima on x86_64 with Rust's libm
//! `cbrtf`, rounded up; the Lean bounds are the platform-independent ones.

use black_hole::physics::{kerr_horizon_radius_rg, kerr_isco_radius_rg};
use std::thread;

const UNIT: f64 = 1.0 / 16_777_216.0; // 2⁻²⁴
const SPIN_LIMIT: f32 = 0.999;

fn horizon_reference(a: f64) -> f64 {
    1.0 + (1.0 - a * a).sqrt()
}

fn isco_reference(spin: f64) -> f64 {
    let a = spin.abs();
    let q = (1.0 + a).cbrt();
    let r = (1.0 - a).cbrt();
    let gap = 2.0 * a / (q * q + q * r + r * r);
    let w = (q + r) * gap * gap;
    let z1 = 3.0 - w;
    let z2 = (3.0 * a * a + z1 * z1).sqrt();
    let direction = if spin >= 0.0 { -1.0 } else { 1.0 };
    3.0 + z2 + direction * (w * (3.0 + z1 + 2.0 * z2)).sqrt()
}

#[derive(Default)]
struct Worst {
    horizon: f64,
    isco: f64,
    nonfinite_horizon: u64,
    nan_isco: u64,
    other_nonfinite_isco: u64,
}

fn scan(start: u64, stride: u64) -> Worst {
    let mut worst = Worst::default();
    let mut index = start;
    while index < 1 << 32 {
        let spin = f32::from_bits(index as u32);
        index += stride;

        // `f32::min` returns the non-NaN operand, so NaN and ±∞ select the limit.
        let horizon = kerr_horizon_radius_rg(spin);
        if horizon.is_finite() {
            let exact = horizon_reference(spin.abs().min(SPIN_LIMIT) as f64);
            worst.horizon = worst.horizon.max(((horizon as f64 - exact) / exact).abs());
        } else {
            worst.nonfinite_horizon += 1;
        }

        // `f32::clamp` propagates NaN; ±∞ clamp to ∓/± the limit.
        let isco = kerr_isco_radius_rg(spin);
        if spin.is_nan() {
            worst.nan_isco += u64::from(isco.is_nan());
        } else if isco.is_finite() {
            let exact = isco_reference(spin.clamp(-SPIN_LIMIT, SPIN_LIMIT) as f64);
            worst.isco = worst.isco.max(((isco as f64 - exact) / exact).abs());
        } else {
            worst.other_nonfinite_isco += 1;
        }
    }
    worst
}

/// The Lean model admits a platform `cbrtf` with relative error at most 2⁻²³.
/// The ISCO only takes cube roots of `fl(1 + a)` and `fl(1 - a)` for
/// `0 ≤ a ≤ 0.999`, which lie in `[1 - 0.999_f32, 2]`; check every one.
#[test]
#[ignore = "evaluates every binary32 cube-root input; run with --release -- --ignored"]
fn cbrt_meets_the_lean_hypothesis() {
    let low = (1.0_f32 - SPIN_LIMIT).to_bits();
    let high = 2.0_f32.to_bits();
    let mut worst = 0.0_f64;
    for bits in low..=high {
        let x = f32::from_bits(bits);
        let exact = (x as f64).cbrt();
        worst = worst.max(((x.cbrt() as f64 - exact) / exact).abs());
    }
    println!("cbrtf {:.3} u", worst / UNIT);
    // 2⁻²³ = 2 u, less a margin for the binary64 reference.
    assert!(worst <= 2.0 * UNIT * (1.0 - 1e-9), "cbrtf error {} u", worst / UNIT);
}

#[test]
#[ignore = "evaluates all 2^32 inputs; run with --release -- --ignored"]
fn every_binary32_spin() {
    let threads = thread::available_parallelism().map_or(4, |n| n.get()) as u64;
    let parts: Vec<_> = (0..threads)
        .map(|start| thread::spawn(move || scan(start, threads)))
        .collect();
    let mut total = Worst::default();
    for part in parts {
        let part = part.join().unwrap();
        total.horizon = total.horizon.max(part.horizon);
        total.isco = total.isco.max(part.isco);
        total.nonfinite_horizon += part.nonfinite_horizon;
        total.nan_isco += part.nan_isco;
        total.other_nonfinite_isco += part.other_nonfinite_isco;
    }
    println!(
        "horizon {:.2} u, isco {:.2} u",
        total.horizon / UNIT,
        total.isco / UNIT
    );
    let nan_patterns = (1u64 << 24) - 2;
    assert_eq!(total.nonfinite_horizon, 0, "horizon must be finite for every input");
    assert_eq!(total.nan_isco, nan_patterns, "every NaN spin propagates to the ISCO");
    assert_eq!(total.other_nonfinite_isco, 0, "non-NaN spins give finite ISCO");
    assert!(total.horizon <= 7.0 * UNIT, "horizon error {} u", total.horizon / UNIT);
    assert!(total.isco <= 18.0 * UNIT, "isco error {} u", total.isco / UNIT);
}
