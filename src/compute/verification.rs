// An independent Schwarzschild reference in spherical coordinates. Unlike the
// shader, it integrates r''=L²/r³-3L²/r⁴ and phi'=L/r² in binary64.
// shortcut: Schwarzschild only; add an independent Kerr reference before claiming spinning-ray convergence.
fn schwarzschild_reference(initial: &[f32], steps: usize) -> [f64; 2] {
    let x = f64::from(initial[0]);
    let z = f64::from(initial[2]);
    let r = x.hypot(z);
    let angular = x * f64::from(initial[7]) - z * f64::from(initial[5]);
    let radial = (x * f64::from(initial[8]) + z * f64::from(initial[10])) / r;
    let mut state = [r, radial, z.atan2(x)];
    let rhs = |s: [f64; 3]| {
        [
            s[1],
            angular.powi(2) / s[0].powi(3) - 3.0 * angular.powi(2) / s[0].powi(4),
            angular / s[0].powi(2),
        ]
    };
    let add = |s: [f64; 3], d: [f64; 3], h: f64| std::array::from_fn(|i| s[i] + h * d[i]);
    let h = 40.0 / steps as f64;
    for _ in 0..steps {
        let a = rhs(state);
        let b = rhs(add(state, a, h * 0.5));
        let c = rhs(add(state, b, h * 0.5));
        let d = rhs(add(state, c, h));
        state =
            std::array::from_fn(|i| state[i] + h / 6.0 * (a[i] + 2.0 * b[i] + 2.0 * c[i] + d[i]));
        assert!(state.iter().all(|x| x.is_finite()) && state[0] > 2.0);
    }
    [state[0] * state[2].cos(), state[0] * state[2].sin()]
}

pub(super) fn check_convergence(values: &[f32]) {
    let initial = &values[40..52];
    let reference = schwarzschild_reference(initial, 4096);
    let refined = schwarzschild_reference(initial, 8192);
    assert!((reference[0] - refined[0]).hypot(reference[1] - refined[1]) < 1e-9);
    let errors: Vec<_> = (1..=4)
        .map(|sample| {
            let state = &values[40 + sample * 12..52 + sample * 12];
            assert!(state.iter().all(|x| x.is_finite()));
            assert_eq!(state[3], 1.0, "RK4 stage left the valid domain");
            assert_eq!(
                state[4].to_bits(),
                initial[4].to_bits(),
                "stationary p_t changed"
            );
            (f64::from(state[0]) - refined[0]).hypot(f64::from(state[2]) - refined[1])
        })
        .collect();
    let adaptive = &values[112..124];
    let adaptive_error =
        (f64::from(adaptive[0]) - refined[0]).hypot(f64::from(adaptive[2]) - refined[1]);
    eprintln!(
        "Adaptive Schwarzschild position error at affine time 40: {adaptive_error}, screen residual: {}",
        adaptive[3]
    );
    assert!(adaptive.iter().all(|x| x.is_finite()));
    assert!(
        adaptive_error < 0.0001,
        "adaptive trajectory error: {adaptive_error}"
    );
    assert!(
        adaptive[3] < 0.00001,
        "adaptive screen residual: {}",
        adaptive[3]
    );
    assert_eq!(
        adaptive[4].to_bits(),
        initial[4].to_bits(),
        "adaptive p_t changed"
    );
    assert_eq!(adaptive[11], 40.0);
    eprintln!("Schwarzschild position errors at affine time 40, h=4/2/1/0.5: {errors:?}");
    eprintln!(
        "Ricci_tt single/binary, difference steps 0.02/0.01: {:?}",
        &values[32..36]
    );
    assert!(
        errors[1] < errors[0] / 4.0 && errors[2] < errors[1] / 4.0,
        "RK4 refinement failed: {errors:?}"
    );
    assert!(
        errors[3] < 0.001,
        "finest trajectory error exceeds 0.001 r_g: {errors:?}"
    );
    assert!(
        values[99] < 2e-4,
        "finest trajectory null residual exceeds production tolerance"
    );
}

#[test]
fn schwarzschild_radial_reference_is_affine() {
    // Zero angular momentum has r''=0 and constant phi.
    let mut initial = [0.0; 12];
    initial[0] = 20.0;
    initial[8] = 0.5;
    let final_position = schwarzschild_reference(&initial, 80);
    googletest::assert_that!(final_position[0], googletest::matchers::near(40.0, 1e-12));
    assert_eq!(final_position[1], 0.0);
}
