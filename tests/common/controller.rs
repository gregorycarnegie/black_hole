//! Production adaptive stepping against the trajectory targets (obligation N3).
//!
//! `tests/controller.wesl` traces Schwarzschild rays with `advance_ray` and the
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

use bevy::render::render_resource::BufferUsages;

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
#[ignore = "requires a GPU (lavapipe works); run with --release -- --ignored"]
fn adaptive_controller_misses_trajectory_targets() {
    // (impact parameter, affine span): a wide deflection, two near-critical
    // passes around the photon sphere, and a direct long ray.
    let cases: [(f32, f32); 4] = [(10.0, 220.0), (5.3, 220.0), (5.25, 260.0), (30.0, 400.0)];
    let mut input = Vec::new();
    for (impact, span) in cases {
        for value in [impact, span, 0.0, 0.0] {
            input.extend_from_slice(&value.to_le_bytes());
        }
    }
    let mut objects = vec![0u8; 1040];
    objects[..4].copy_from_slice(&1i32.to_le_bytes());
    objects[528..532].copy_from_slice(&1f32.to_le_bytes());
    let data = crate::gpu::run_groups(
        include_str!("../controller.wesl"),
        "trace",
        &[
            &[(3, &objects, BufferUsages::UNIFORM)],
            &[(0, &input, BufferUsages::STORAGE)],
        ],
        (cases.len() * 64) as u64,
        cases.len() as u32,
    );
    let values: &[f32] = bytemuck::cast_slice(&data);
    let mut failures = 0;
    for (n, (impact, _)) in cases.iter().enumerate() {
        let v: Vec<f64> = values[16 * n..16 * n + 16].iter().map(|&x| f64::from(x)).collect();
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
            "impact {impact}: affine {span}, {} accepted steps; position error {pos_error:.3e} \
             (target {pos_target:.3e}), momentum error {p_error:.3e} (target {p_target:.3e}), \
             |ΔL| {drift:.3e} (targets allow {allowed:.3e}); reference agreement {agreement:.1e}",
            v[15]
        );
        if pos_error > pos_target || p_error > p_target {
            failures += 1;
        }
    }
    // Records the counterexample: at least one accepted trajectory exceeds the
    // TARGETS.md position or momentum error. Remove this assertion once the
    // controller is certified.
    assert!(failures > 0, "every traced ray met the trajectory targets");
}
