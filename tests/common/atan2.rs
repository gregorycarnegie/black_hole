//! Production `atan2_arith` against binary64 (obligation F2). The Lean bound
//! (`WgslAtan2.atan2_arith_error`) is 128 u absolute against `Complex.arg`
//! under the WGSL accuracy model, for `max(|x|, |y|)` in `[2^-126, 2^126]`.

#[test]
#[ignore = "requires a GPU; run with --release -- --ignored"]
fn atan2_arith_meets_the_wgsl_bound() {
    const UNIT: f64 = 1.0 / 16_777_216.0;
    let mut points: Vec<[f32; 2]> = Vec::new();
    // Dense angles, every octant boundary and its neighbours, the tan(pi/8)
    // branch point, the axes (where builtin atan2 is unspecified), and scales.
    for i in 0..8192 {
        let a = -std::f64::consts::PI + std::f64::consts::TAU * f64::from(i) / 8192.0;
        for r in [1.0e-30_f64, 1.0e-6, 1.0, 1.0e6, 1.0e30] {
            points.push([(r * a.sin()) as f32, (r * a.cos()) as f32]);
        }
    }
    for k in 0..16 {
        let a = f64::from(k) * std::f64::consts::FRAC_PI_8;
        let (y, x) = (a.sin() as f32, a.cos() as f32);
        for (dy, dx) in [(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)] {
            let nudge = |v: f32, d: i32| f32::from_bits((v.to_bits() as i32 + d) as u32);
            points.push([nudge(y, dy), nudge(x, dx)]);
        }
    }
    for v in [1.0_f32, -1.0, 2.0e-38, -3.0e38] {
        points.extend([[0.0, v], [v, 0.0], [v, v], [v, -v]]);
    }
    let values = crate::gpu::atan2(&points);
    let mut worst = 0.0_f64;
    for (n, &[y, x]) in points.iter().enumerate() {
        let (y, x) = (f64::from(y), f64::from(x));
        // WGSL specifies division only for divisors in [2^-126, 2^126].
        let hi = x.abs().max(y.abs());
        if !(2.0_f64.powi(-126)..=2.0_f64.powi(126)).contains(&hi) {
            continue;
        }
        // Complex.arg takes the imaginary part as +0 for both zeros.
        let exact = (if y == 0.0 { 0.0 } else { y }).atan2(x);
        worst = worst.max((f64::from(values[n]) - exact).abs() / UNIT);
    }
    println!("atan2_arith: {} points, worst error {worst:.3} u", points.len());
    assert!(worst <= 128.0, "atan2_arith error {worst} u");
}
