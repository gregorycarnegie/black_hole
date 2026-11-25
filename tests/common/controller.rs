//! Production adaptive stepping against the trajectory targets (obligation N3).
//!
//! The `bh_test_controller_trace` CUDA kernel traces Schwarzschild rays with the legacy RK4 controller (and, with `cases.z`
//! set, the production Dormand–Prince controller of checklist P1.1b) and the
//! renderer's step-size rule up to a fixed affine parameter. Two independent
//! measures of the error at the end point are compared with TARGETS.md:
//!
//! * a binary64 Kerr–Schild Hamiltonian reference started from the GPU's own
//!   binary32 initial state, integrated with RK4 at two step counts whose
//!   difference must be below 10⁻³ of the smallest target;
//! * the drift of the axial angular momentum `L = z p_x - x p_z`, which the
//!   exact flow conserves. It is printed as a diagnostic only: the drift the
//!   targets allow (`2 εx |p|∞ + 2 |x|∞ εp + 2 εx εp`) is too large for it to
//!   certify a failure on these rays.

const MASS: f64 = 1.0;

/// Inverse Kerr–Schild Schwarzschild metric `η - (2M/r) l l` with
/// `l^μ = (-1, x/r)`, and its spatial derivatives.
fn inverse_and_derivative(x: [f64; 3]) -> ([[f64; 4]; 4], [[[f64; 4]; 4]; 3]) {
    let r = (x[0] * x[0] + x[1] * x[1] + x[2] * x[2]).sqrt();
    let f = 2.0 * MASS / r;
    let l = [-1.0, x[0] / r, x[1] / r, x[2] / r];
    let mut inv = [[0.0; 4]; 4];
    let eta = [-1.0, 1.0, 1.0, 1.0];
    for a in 0..4 {
        for b in 0..4 {
            inv[a][b] = if a == b { eta[a] } else { 0.0 } - f * l[a] * l[b];
        }
    }
    let mut d = [[[0.0; 4]; 4]; 3];
    for i in 0..3 {
        let df = -2.0 * MASS * x[i] / r.powi(3);
        let mut dl = [0.0; 4];
        for j in 0..3 {
            dl[j + 1] = if i == j { 1.0 / r } else { 0.0 } - x[i] * x[j] / r.powi(3);
        }
        for a in 0..4 {
            for b in 0..4 {
                d[i][a][b] = -(df * l[a] * l[b] + f * (dl[a] * l[b] + l[a] * dl[b]));
            }
        }
    }
    (inv, d)
}

/// Hamiltonian flow of `H = ½ g^{μν} p_μ p_ν`; state is `(x, p)`.
fn rhs(s: [f64; 7]) -> [f64; 7] {
    let (inv, d) = inverse_and_derivative([s[0], s[1], s[2]]);
    let p = [s[3], s[4], s[5], s[6]];
    let mut out = [0.0; 7];
    for i in 0..3 {
        out[i] = (0..4).map(|b| inv[i + 1][b] * p[b]).sum();
        let mut force = 0.0;
        for a in 0..4 {
            for b in 0..4 {
                force += d[i][a][b] * p[a] * p[b];
            }
        }
        out[i + 4] = -0.5 * force;
    }
    out
}

fn reference(start: [f64; 7], span: f64, steps: usize) -> [f64; 7] {
    let h = span / steps as f64;
    let mut s = start;
    let add = |s: [f64; 7], d: [f64; 7], h: f64| std::array::from_fn(|i| s[i] + h * d[i]);
    for _ in 0..steps {
        let a = rhs(s);
        let b = rhs(add(s, a, 0.5 * h));
        let c = rhs(add(s, b, 0.5 * h));
        let e = rhs(add(s, c, h));
        s = std::array::from_fn(|i| s[i] + h / 6.0 * (a[i] + 2.0 * b[i] + 2.0 * c[i] + e[i]));
    }
    s
}

fn max_abs(v: &[f64]) -> f64 {
    v.iter().fold(0.0, |m, x| m.max(x.abs()))
}

#[test]
#[ignore = "requires a GPU; run with --release -- --ignored"]
fn adaptive_controller_misses_trajectory_targets() {
    // (impact parameter, affine span): a wide deflection, two near-critical
    // passes around the photon sphere, and a direct long ray.
    let cases: [(f32, f32); 4] = [(10.0, 220.0), (5.3, 220.0), (5.25, 260.0), (30.0, 400.0)];
    // Each case runs with the legacy RK4 controller, then with the production
    // Dormand–Prince one; both are held to the counterexample.
    let mut input = Vec::new();
    for dormand_prince in [0.0, 1.0] {
        for (impact, span) in cases {
            for value in [impact, span, dormand_prince, 0.0] {
                input.extend_from_slice(&value.to_le_bytes());
            }
        }
    }
    let mut objects = vec![0u8; 1040];
    objects[..4].copy_from_slice(&1i32.to_le_bytes());
    objects[528..532].copy_from_slice(&1f32.to_le_bytes());
    let values = crate::gpu::controller_trace(&objects, &input, 2 * cases.len() as u32);
    let mut failures = [0; 2];
    for (n, (impact, _)) in cases.iter().cycle().take(2 * cases.len()).enumerate() {
        let (label, evaluations) = if n < cases.len() { ("rk4", 11.0) } else { ("dp45", 6.0) };
        let v: Vec<f64> = values[20 * n..20 * n + 20].iter().map(|&x| f64::from(x)).collect();
        assert_eq!(v[3], 1.0, "ray {impact} did not reach its affine span: status {}", v[3]);
        let span = v[11];
        let start = [v[0], v[1], v[2], v[4], v[5], v[6], v[7]];
        let coarse = reference(start, span, 200_000);
        let fine = reference(start, span, 400_000);
        let agreement = max_abs(&std::array::from_fn::<f64, 7, _>(|i| coarse[i] - fine[i]));
        let gpu_pos = [v[8], v[9], v[10]];
        let gpu_p = [v[4], v[12], v[13], v[14]];
        let pos_error = max_abs(&std::array::from_fn::<f64, 3, _>(|i| gpu_pos[i] - fine[i]));
        let p_error = max_abs(&std::array::from_fn::<f64, 4, _>(|i| gpu_p[i] - fine[i + 3]));
        let pos_target = 1e-6 * max_abs(&gpu_pos).max(1.0);
        let p_target = 1e-6 * max_abs(&gpu_p).max(1.0);
        assert!(
            agreement < 1e-3 * pos_target.min(p_target),
            "reference not converged: {agreement}"
        );
        let angular = |x: [f64; 3], p: [f64; 4]| x[2] * p[1] - x[0] * p[3];
        let drift = (angular(gpu_pos, gpu_p) - angular([v[0], v[1], v[2]], [v[4], v[5], v[6], v[7]]))
            .abs();
        let allowed = 2.0 * pos_target * max_abs(&gpu_p)
            + 2.0 * max_abs(&gpu_pos) * p_target
            + 2.0 * pos_target * p_target;
        println!(
            "{label} impact {impact}: affine {span}, {} accepted steps, {} rejected \
             (at most {} metric evaluations); position error {pos_error:.3e} \
             (target {pos_target:.3e}), momentum error {p_error:.3e} (target {p_target:.3e}), \
             |ΔL| {drift:.3e} (targets allow {allowed:.3e}); reference agreement {agreement:.1e}",
            v[15],
            v[16],
            (v[15] + v[16]) * evaluations
        );
        if pos_error > pos_target || p_error > p_target {
            failures[n / cases.len()] += 1;
        }
    }
    // Records the counterexample: for each controller, at least one accepted trajectory
    // exceeds the TARGETS.md position or momentum error. Remove this assertion once
    // the controller is certified.
    assert!(failures.iter().all(|&f| f > 0), "a controller met every trajectory target: {failures:?}");
}

/// Schwarzschild classification (obligation N4). A geodesic with conserved
/// `E = |p_t|`, `L = z p_x - x p_z` and `m² = -g^{μν} p_μ p_ν` obeys
/// `ṙ² = E² - V(r)` with `V = (1 - 2M/r)(L²/r² + m²)`. An ingoing ray from
/// r ≈ 100 is captured iff `E²` exceeds the maximum of `V` outside the
/// horizon, and otherwise turns and escapes. All three charges are evaluated
/// in binary64 from the GPU's own binary32 initial state, so the binary32
/// null residual is accounted for exactly (for a null ray this reduces to
/// `b = |L|/E` versus `3√3 M`). The renderer's rules must never return the
/// opposite class; critical rays may only end unresolved, which the unresolved
/// band (`UNRESOLVED_WINDING`, checklist P1.6) does for rays that wound around the
/// photon sphere. Both controllers run at geometric step factors 0.11, 0.12 and
/// 0.13, so a pass cannot hinge on one factor's rounding.
#[test]
#[ignore = "requires a GPU; run with --release -- --ignored --nocapture"]
fn classification_against_the_critical_impact_parameter() {
    let critical = 27.0_f64.sqrt() * MASS;
    // (b, status, steps, margin, winding) per ray. Status: 1 captured, 2 escaped,
    // 4 early capture, 5 unresolved band, 0 or 3 unresolved otherwise.
    let run = |impacts: &[f32], disk_inner: f32, dormand_prince: f32, step_factor: f32| {
        let mut input = Vec::new();
        for &impact in impacts {
            for value in [impact, disk_inner, dormand_prince, step_factor] {
                input.extend_from_slice(&value.to_le_bytes());
            }
        }
        let mut objects = vec![0u8; 1040];
        objects[..4].copy_from_slice(&1i32.to_le_bytes());
        objects[528..532].copy_from_slice(&1f32.to_le_bytes());
        let values: Vec<f64> = crate::gpu::controller_classify(&objects, &input, impacts.len() as u32)
            .iter()
            .map(|&x| f64::from(x))
            .collect();
        (0..impacts.len())
            .map(|n| {
                let v = &values[16 * n..16 * n + 16];
                let angular = v[2] * v[4 + 1] - v[0] * v[4 + 3];
                // Past-directed rays: p_t > 0, energy is |p_t|.
                let energy = v[4].abs();
                let b = angular.abs() / energy;
                let p = [v[4], v[5], v[6], v[7]];
                let (inv, _) = inverse_and_derivative([v[0], v[1], v[2]]);
                let mut norm = 0.0;
                for a in 0..4 {
                    for c in 0..4 {
                        norm += inv[a][c] * p[a] * p[c];
                    }
                }
                let mass2 = -norm;
                let potential = |r: f64| (1.0 - 2.0 * MASS / r) * (angular * angular / (r * r) + mass2);
                // V is unimodal on (2M, 100]; golden-section search for its peak.
                let (mut lo, mut hi) = (2.5 * MASS, 4.0 * MASS);
                for _ in 0..200 {
                    let a = lo + 0.381_966_011_250_105 * (hi - lo);
                    let c = hi - 0.381_966_011_250_105 * (hi - lo);
                    if potential(a) < potential(c) { lo = a } else { hi = c }
                }
                let margin = (energy * energy - potential(0.5 * (lo + hi))) / (energy * energy);
                (b, v[3] as u32, v[11] as u32, margin, v[15])
            })
            .collect::<Vec<_>>()
    };
    // Coarse pass to locate the critical impact, then every binary32 impact in a
    // window around it, and a wide sweep for rays safely away from it.
    let coarse: Vec<f32> = (0..64).map(|i| 5.0 + 0.4 * i as f32 / 63.0).collect();
    let rays = run(&coarse, 0.0, 0.0, 0.0);
    let index = rays.iter().position(|r| r.3 < 0.0).unwrap();
    let centre = coarse[index - 1] + (coarse[index] - coarse[index - 1])
        * (rays[index - 1].3 / (rays[index - 1].3 - rays[index].3)) as f32;
    let mut impacts = Vec::new();
    let mut impact = f32::from_bits(centre.to_bits() - 128);
    for _ in 0..256 {
        impacts.push(impact);
        impact = f32::from_bits(impact.to_bits() + 1);
    }
    impacts.extend((0..256).map(|i| 4.0 + 2.5 * i as f32 / 255.0));
    // Rays at least this far from the critical margin must resolve.
    const SAFE_MARGIN: f64 = 1.0e-4;

    let mut wrong = Vec::new();
    let mut unresolved_safe = Vec::new();
    for dormand_prince in [0.0, 1.0] {
        let name = if dormand_prince != 0.0 { "dp45" } else { "rk4" };
        for step_factor in [0.11, 0.12, 0.13] {
            for disk_inner in [0.0, 4.0] {
                let mut counts = [0; 6];
                // Smallest |margin| among definitive answers.
                let mut closest = f64::INFINITY;
                for (impact, (b, status, steps, margin, winding)) in
                    impacts.iter().zip(run(&impacts, disk_inner, dormand_prince, step_factor))
                {
                    counts[status as usize] += 1;
                    // Positive margin: E² exceeds the potential barrier, so the ray is captured.
                    let exact = if margin > 0.0 { 1 } else { 2 };
                    let result = if status == 4 { 1 } else { status };
                    if result == 1 || result == 2 {
                        closest = closest.min(margin.abs());
                        if result != exact {
                            wrong.push((name, step_factor, *impact, b - critical, margin, status, steps, winding));
                        }
                    } else if margin.abs() > SAFE_MARGIN {
                        unresolved_safe.push((name, step_factor, *impact, margin, status, winding));
                    }
                }
                println!(
                    "{name} step factor {step_factor} disk inner {disk_inner}: captured/escaped/early/band/other unresolved {}/{}/{}/{}/{}; closest definitive |margin| {closest:.2e}",
                    counts[1], counts[2], counts[4], counts[5], counts[0] + counts[3]
                );
            }
        }
    }
    for (name, factor, impact, offset, margin, status, steps, winding) in wrong.iter().take(8) {
        println!(
            "{name} {factor}: misclassified impact {impact}: b - b_c = {offset:.3e}, (E² - V_max)/E² = {margin:.3e}, status {status}, {steps} steps, winding {winding:.2} rad"
        );
    }
    assert!(wrong.is_empty(), "{} definitive answers contradict the reference", wrong.len());
    assert!(unresolved_safe.is_empty(), "rays away from the critical margin left unresolved: {unresolved_safe:?}");
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn kerr_early_capture_matches_the_equatorial_radial_potential() {
    const CASES: usize = 801;
    // ±0.995 is the guard's edge.
    for spin in [-0.995_f32, -0.99, -0.82, 0.0, 0.82, 0.99, 0.995] {
        let a = f64::from(spin);
        let horizon = 1.0 + (1.0 - a * a).sqrt();
        let mut objects = vec![0u8; 1040];
        objects[..4].copy_from_slice(&1i32.to_le_bytes());
        objects[528..532].copy_from_slice(&1f32.to_le_bytes());
        objects[788..792].copy_from_slice(&spin.to_le_bytes());
        let run = |disk_inner: f32| {
            let cases: Vec<f32> = (0..CASES)
                .flat_map(|i| [-8.0 + 0.02 * i as f32, disk_inner, 0.0, 0.0])
                .collect();
            crate::gpu::controller_classify(&objects, bytemuck::cast_slice(&cases), CASES as u32)
        };
        let baseline = run(0.0);
        if spin == 0.82 {
            assert_eq!(
                run(1.0),
                baseline,
                "a disk extending to the horizon must keep the full trace"
            );
        }
        let optimized = run(4.0);
        let mut early = 0;
        let mut saved_steps = 0;
        for (old, new) in baseline.as_chunks::<16>().0.iter().zip(optimized.as_chunks::<16>().0) {
            let [x, z, pt, px, pz] = [new[0], new[2], new[4], new[5], new[7]].map(f64::from);
            let lambda = (z * px - x * pz) / -pt;
            // For equatorial null rays R(r)/r is a cubic with at most one exterior minimum.
            let min_r = ((lambda * lambda - a * a).max(0.0) / 3.0)
                .sqrt()
                .max(horizon);
            let minimum = min_r * (min_r * min_r + a * a - lambda * lambda)
                + 2.0 * (lambda - a).powi(2);
            if old[3] == 2.0 {
                assert_eq!(new[3], 2.0, "baseline escape changed at spin {a}, λ {lambda}");
            }
            if new[3] == 4.0 {
                assert!(
                    minimum > 0.0,
                    "early capture with an exterior radial turn at spin {a}, λ {lambda}, minimum {minimum}"
                );
                // The capture state: position, conserved p_t and spatial momentum.
                assert!(
                    black_hole::certified::capture_certified(
                        spin,
                        4.0,
                        [new[8], new[9], new[10]],
                        [new[4], new[12], new[13], new[14]],
                    ),
                    "GPU early capture not certified on the CPU at spin {a}, λ {lambda}"
                );
                early += 1;
                saved_steps += old[11] as u32 - new[11] as u32;
            }
        }
        println!("spin {spin} early-captured {early}/{CASES}, saved {saved_steps} steps");
        assert!(early > 0 && saved_steps > 0);
    }
}

