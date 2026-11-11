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
