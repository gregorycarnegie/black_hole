//! Production `geodesic_rhs` on the GPU against the proved bound
//! `CudaGeodesic.geodesic_rhs_exact_inputs`: every output is within
//! `3·10⁻⁴` of the exact value, relative to the absolute evaluation of its
//! program. The exact value and absolute evaluation come from the Lean
//! fixture (`verification/fixtures/cuda-geodesic.sexp`), not a transcription. This
//! exercises the driver and hardware, which no proof here covers (F4).

/// Unit roundoff `u` and flush-to-zero `η` of the WGSL model; `U = 5u`.
const U: f64 = 5.0 / 16_777_216.0;
const ETA: f64 = 1.0 / 85_070_591_730_234_615_865_843_651_857_942_052_864.0;

/// `(exact, absEval)` of a fixture expression with inputs `v`.
fn eval(tokens: &[&str], pos: &mut usize, v: &[f64]) -> (f64, f64) {
    let mut next = || {
        *pos += 1;
        tokens[*pos - 1]
    };
    assert_eq!(next(), "(");
    let op = next();
    let rational = |n: &str, d: &str| n.parse::<f64>().unwrap() / d.parse::<f64>().unwrap();
    let r = match op {
        "in" => {
            let x = v[next().parse::<usize>().unwrap()];
            (x, x.abs())
        }
        "c" => {
            let c = rational(next(), next());
            (c, c.abs())
        }
        "neg" => {
            let (x, a) = eval(tokens, pos, v);
            (-x, a)
        }
        "divc" => {
            let (x, a) = eval(tokens, pos, v);
            let c = rational(tokens[*pos], tokens[*pos + 1]);
            *pos += 2;
            (x / c, a / c.abs() + ETA / U)
        }
        _ => {
            let (x, a) = eval(tokens, pos, v);
            let (y, b) = eval(tokens, pos, v);
            match op {
                "add" => (x + y, a + b + ETA / U),
                "sub" => (x - y, a + b + ETA / U),
                "mul" => (x * y, a * b + ETA / U),
                _ => panic!("unknown operation {op}"),
            }
        }
    };
    assert_eq!(tokens[*pos], ")");
    *pos += 1;
    r
}

#[test]
#[ignore = "requires a GPU; run with --release -- --ignored"]
fn geodesic_rhs_meets_the_proved_bound() {
    let fixture = include_str!("../../verification/fixtures/cuda-geodesic.sexp");
    let lines: Vec<String> = fixture
        .lines()
        .filter(|l| l.starts_with("geodesic_rhs "))
        .map(|l| l.replace('(', " ( ").replace(')', " ) "))
        .collect();
    let programs: Vec<Vec<&str>> = lines
        .iter()
        .map(|l| l.split_whitespace().skip(1).collect())
        .collect();
    assert_eq!(programs.len(), 11);
    // Deterministic inputs over several magnitudes, signs and cancellations.
    let mut state = 0x9e37_79b9_7f4a_7c15_u64;
    let mut random = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        let mantissa = (state >> 40) as f64 / f64::from(1u32 << 24) * 2.0 - 1.0;
        let scale = [1.0e-3, 1.0, 1.0e2, 1.0e4][(state & 3) as usize];
        (mantissa * scale) as f32
    };
    let cases = 4096;
    let inputs: Vec<f32> = (0..cases * 72).map(|_| random()).collect();
    let values = crate::gpu::geodesic_rhs(&inputs, cases);
    let mut worst = 0.0_f64;
    for case in 0..cases {
        let v: Vec<f64> = inputs[case * 72..(case + 1) * 72]
            .iter()
            .map(|&x| f64::from(x))
            .collect();
        for (o, program) in programs.iter().enumerate() {
            let (exact, abs_eval) = eval(program, &mut 0, &v);
            let error = (f64::from(values[case * 11 + o]) - exact).abs();
            // binary64 evaluation of the exact value errs by far less than this slack.
            let allowed = 3.0e-4 * abs_eval + 1.0e-12 * abs_eval;
            worst = worst.max(error / abs_eval.max(f64::MIN_POSITIVE));
            assert!(
                error <= allowed,
                "case {case} output {o}: error {error}, bound {allowed}"
            );
        }
    }
    println!("geodesic_rhs: {cases} cases, worst error {worst:.3e} of absEval (bound 3e-4)");
}

/// The structured `geodesic_rhs` (checklist P1.3) and its fused one- and two-hole form
/// against the matrix form above, on a spinning single hole and a tilted-spin binary.
/// They are the same algebra in a different order (`CudaStructuredRhs.lean`), so they
/// agree to binary32 rounding. On the single hole all three also meet the binary64
/// `certified::Kerr` right-hand side.
#[test]
#[ignore = "requires a GPU; run with --release -- --ignored"]
fn structured_geodesic_rhs_matches_the_matrix_form() {
    // `Objects`: count, then 16-entry Vec4 arrays pos_radius, color, mass, spin.
    let scene = |holes: &[([f32; 3], f32, [f32; 3])]| {
        let mut objects = vec![0u8; 1040];
        objects[..4].copy_from_slice(&i32::try_from(holes.len()).unwrap().to_le_bytes());
        for (i, (pos, mass, spin)) in holes.iter().enumerate() {
            let put = |o: &mut Vec<u8>, at: usize, v: &[f32]| {
                o[at..at + 4 * v.len()].copy_from_slice(bytemuck::cast_slice(v));
            };
            put(&mut objects, 16 + 16 * i, pos);
            put(&mut objects, 528 + 16 * i, &[*mass]);
            put(&mut objects, 784 + 16 * i, spin);
        }
        objects
    };
    let single = [([0.0; 3], 1.0, [0.0, 0.9, 0.0])];
    let binary = [
        ([7.0, 0.0, 0.0], 0.5, [0.0, 0.6, 0.0]),
        ([-7.0, 0.0, 0.0], 0.5, [0.3, 0.0, 0.4]),
    ];
    let mut state = 0x2545_f491_4f6c_dd1d_u64;
    let mut random = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        (state >> 40) as f32 / (1u32 << 24) as f32 * 2.0 - 1.0
    };
    let cases = 4096;
    let kerr = black_hole::certified::Kerr::new([0.0, 0.9, 0.0]).unwrap();
    for (name, holes) in [("single", &single[..]), ("binary", &binary[..])] {
        // Positions from 2.5 to 30 from the origin, so most states are outside both horizons.
        let inputs: Vec<f32> = (0..cases)
            .flat_map(|_| {
                let dir = [random(), random(), random()];
                let n = dir.iter().map(|d| d * d).sum::<f32>().sqrt().max(1.0e-3);
                let r = 2.5 + 27.5 * (0.5 + 0.5 * random());
                let mut v = vec![r * dir[0] / n, r * dir[1] / n, r * dir[2] / n, 0.0];
                v.extend((0..8).map(|_| random()));
                v
            })
            .collect();
        let values = crate::gpu::rhs_forms(&scene(holes), &inputs);
        // Random p is not null, so outputs can cancel far below their terms. Each group is
        // scaled by its terms' size instead, as `absEval` does for the proved bound: |p| for
        // k, |p|²/d² for the force and |p| |f| / d² for transport, d the nearest hole.
        let scales = |x: &[f32]| {
            let d2 = holes
                .iter()
                .map(|(c, _, _)| (0..3).map(|i| (x[i] - c[i]).powi(2)).sum::<f32>())
                .fold(f32::MAX, f32::min);
            let p: f32 = x[4..8].iter().map(|v| v.abs()).sum();
            let f: f32 = x[8..12].iter().map(|v| v.abs()).sum();
            [(0, 3, p), (3, 7, p * p / d2), (7, 11, p * f / d2)]
        };
        let (mut worst, mut worst_exact, mut checked) = (0.0_f32, [0.0_f64; 3], 0);
        for case in 0..cases {
            let v = &values[case * 34..(case + 1) * 34];
            if v[33] < 0.0 {
                continue;
            }
            assert_eq!(
                v[33], 1.0,
                "{name} case {case}: fused metric differs from scene_metric"
            );
            checked += 1;
            let x = &inputs[case * 12..(case + 1) * 12];
            let exact = (name == "single").then(|| {
                kerr.phase_rhs(std::array::from_fn(|i| {
                    f64::from(x[if i < 3 { i } else { i + 1 }])
                }))
            });
            for (lo, hi, scale) in scales(x) {
                for i in lo..hi {
                    for form in 1..3 {
                        let error = (v[11 * form + i] - v[i]).abs() / scale;
                        worst = worst.max(error);
                        assert!(
                            error <= 1.0e-5,
                            "{name} case {case} form {form} output {i}: {} against {}",
                            v[11 * form + i],
                            v[i]
                        );
                    }
                    let Some(exact) = exact else { continue };
                    for (form, w) in worst_exact.iter_mut().enumerate() {
                        let error =
                            (f64::from(v[11 * form + i]) - exact[i]).abs() / f64::from(scale);
                        *w = w.max(error);
                        assert!(
                            error <= 1.0e-4,
                            "binary64 case {case} form {form} output {i}: {} against {}",
                            v[11 * form + i],
                            exact[i]
                        );
                    }
                }
            }
        }
        assert!(checked > cases / 2, "{name}: only {checked} valid states");
        println!("{name}: {checked} states, worst difference from the matrix form {worst:.3e}");
        if name == "single" {
            println!(
                "single against binary64: worst error matrix {:.3e}, structured {:.3e}, fused {:.3e}",
                worst_exact[0], worst_exact[1], worst_exact[2]
            );
        }
    }
}
