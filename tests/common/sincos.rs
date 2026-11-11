//! Production `sincos` against binary64 (obligation F2). The Lean bound
//! (`WgslSinCos.sincos_error`) is 128 u (1 + |x|) for |x| ≤ 2^18 under the
//! WGSL accuracy model; every finite input stays within [-1.01, 1.01].

#[test]
#[ignore = "requires a GPU; run with --release -- --ignored"]
fn sincos_meets_the_wgsl_bound() {
    const UNIT: f64 = 1.0 / 16_777_216.0;
    let mut angles: Vec<f32> = Vec::new();
    // Dense near zero and the quadrant boundaries, then geometric out to 2^18
    // and beyond, both signs, plus extreme finite values.
    for i in 0..4096 {
        angles.push(-4.0 + 8.0 * i as f32 / 4095.0);
    }
    let mut x = 1.0e-6_f32;
    while x < 3.0e38 {
        angles.push(x);
        angles.push(-x);
        x *= 1.013;
    }
    for k in 1..2000 {
        let edge = k as f32 * std::f32::consts::FRAC_PI_4;
        angles.extend([edge, f32::from_bits(edge.to_bits() + 1), f32::from_bits(edge.to_bits() - 1)]);
    }
    angles.extend([f32::MAX, -f32::MAX, f32::MIN_POSITIVE, 0.0, -0.0]);
    let values = crate::gpu::sincos(&angles);
    let mut worst = 0.0_f64;
    for (n, &a) in angles.iter().enumerate() {
        let [s_f32, c_f32] = values[n];
        let (s, c) = (f64::from(s_f32), f64::from(c_f32));
        assert!(s.abs() <= 1.01 && c.abs() <= 1.01, "unbounded sincos({a}) = ({s}, {c})");
        let x = f64::from(a);
        if x.abs() <= 262_144.0 {
            let error = (s - x.sin()).abs().max((c - x.cos()).abs()) / (UNIT * (1.0 + x.abs()));
            worst = worst.max(error);
        }
    }
    println!("sincos: {} angles, worst error {worst:.3} u (1 + |x|) for |x| <= 2^18", angles.len());
    assert!(worst <= 128.0, "sincos error {worst} u (1 + |x|)");
}
