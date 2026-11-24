//! The Dormand–Prince literals in `tools/cuda/kernels.rs` must be the rationals whose
//! order conditions `verification/BlackHole/DormandPrince.lean` proves.

const KERNELS: &str = include_str!("../tools/cuda/kernels.rs");
const LEAN: &str = include_str!("../verification/BlackHole/DormandPrince.lean");

/// A reduced fraction.
type Rational = (i64, i64);

fn rational(text: &str) -> Rational {
    let integer = |s: &str| -> i64 {
        let s = s.trim();
        s.strip_suffix(".0")
            .unwrap_or(s)
            .parse()
            .unwrap_or_else(|_| panic!("not an integer: {s:?}"))
    };
    let (n, d) = text
        .split_once('/')
        .map_or_else(|| (integer(text), 1), |(n, d)| (integer(n), integer(d)));
    let g = gcd(n.abs(), d);
    (n / g, d / g)
}

fn gcd(a: i64, b: i64) -> i64 {
    if b == 0 { a.max(1) } else { gcd(b, a % b) }
}

/// The comma-separated entries between `start` and the next `end`, brackets removed.
fn entries(source: &str, start: &str, end: &str) -> Vec<Rational> {
    let from = source
        .find(start)
        .unwrap_or_else(|| panic!("{start:?} not found"))
        + start.len();
    let body = &source[from..from + source[from..].find(end).unwrap()];
    body.replace(['[', ']', '!'], "")
        .split(',')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(rational)
        .collect()
}

#[test]
fn kernel_tableau_matches_the_lean_tableau() {
    let a = entries(LEAN, "def a : Fin 7 → Fin 7 → ℚ := ", "\ndef");
    let b = entries(LEAN, "def b : Fin 7 → ℚ := ", "\n");
    let e = entries(LEAN, "def e : Fin 7 → ℚ := ", "\n");
    assert_eq!((a.len(), b.len(), e.len()), (49, 7, 7));

    let kernel_a = entries(KERNELS, "const DP_A: [[f32; 5]; 5] = ", ";");
    let kernel_b = entries(KERNELS, "const DP_B: [f32; 6] = ", ";");
    let kernel_e = entries(KERNELS, "const DP_E: [f32; 7] = ", ";");
    assert_eq!((kernel_a.len(), kernel_b.len(), kernel_e.len()), (25, 6, 7));

    // DP_A row r is Lean row r + 1 (stage r + 2), truncated to five columns; the
    // Lean entries past those columns are zero.
    for r in 0..5 {
        let lean_row = &a[7 * (r + 1)..7 * (r + 2)];
        assert_eq!(kernel_a[5 * r..5 * r + 5], lean_row[..5], "DP_A row {r}");
        assert!(lean_row[5..].iter().all(|&x| x == (0, 1)));
    }
    // The solution never uses the seventh stage.
    assert_eq!(kernel_b[..], b[..6]);
    assert_eq!(b[6], (0, 1));
    assert_eq!(kernel_e, e);
}
