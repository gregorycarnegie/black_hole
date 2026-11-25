use std::path::Path;

#[test]
#[ignore = "requires GPU and generated transfer references; see verification/benchmark-data.md"]
fn headless_polarized_transfer() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("target/eht-benchmark");
    let mut cases = std::fs::read(root.join("transfer-cases.f32"))
        .expect("Run verification/check_transfer.py first");
    let expected = std::fs::read(root.join("transfer-expected.f32")).unwrap();
    assert!(!cases.is_empty() && cases.len().is_multiple_of(64));
    let samples = cases.len() / 64;
    assert_eq!(expected.len(), samples * 16);
    for (alpha, faraday, ds) in [
        ([1.0, 2.0, 0.0, 0.0], [0.0; 3], 1.0),
        ([1.0e-23, 2.0e-23, 0.0, 0.0], [0.0; 3], 1.0),
        ([0.0; 4], [0.0; 3], -1.0),
        ([0.0; 4], [f32::NAN, 0.0, 0.0], 1.0),
        ([0.0; 4], [1.0e6, 0.0, 0.0], 1.0),
    ] {
        let mut invalid = [0.0_f32; 16];
        invalid[4..8].copy_from_slice(&alpha);
        invalid[8..11].copy_from_slice(&faraday);
        invalid[11] = ds;
        cases.extend_from_slice(bytemuck::bytes_of(&invalid));
    }
    let count = cases.len() / 64;
    let data = crate::gpu::transfer(&cases, count as u32);
    let actual: &[f32] = bytemuck::cast_slice(&data);
    let expected: Vec<_> = expected
        .as_chunks::<4>()
        .0
        .iter()
        .map(|v| f32::from_le_bytes(*v))
        .collect();
    let mut maximum = 0.0_f32;
    for (i, row) in actual.as_chunks::<8>().0.iter().enumerate() {
        if i >= samples {
            assert_eq!(row, &[0.0; 8], "invalid transfer cell accepted");
            continue;
        }
        assert_eq!(row[4], 1.0, "transfer cell {i} rejected");
        for component in 0..4 {
            let reference = expected[4 * i + component];
            let error = (row[component] - reference).abs() / reference.abs().max(1.0);
            maximum = maximum.max(error);
            assert!(
                row[component].is_finite() && error < 0.0002,
                "transfer case {i}, component {component}: {} vs {reference}",
                row[component]
            );
        }
        let polarized = (row[1] * row[1] + row[2] * row[2] + row[3] * row[3]).sqrt();
        assert!(
            polarized <= row[0] + 0.0002 * row[0].abs().max(1.0),
            "Stokes cone at case {i}"
        );
    }
    std::fs::write(root.join("transfer-gpu.f32"), &data).unwrap();
    eprintln!("{samples} full polarized GPU cells: maximum scaled error = {maximum}");
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn subnormal_opacity_remains_passive() {
    let mut cases = Vec::new();
    // Squaring 0.99 * 3e-23 rounds upward past the passive bound.
    for scale in [1e-30_f32, 3e-23, 1e-20, 1.0] {
        let mut row = [0.0_f32; 16];
        row[4..8].copy_from_slice(&[scale, 0.99 * scale, 0.0, 0.0]);
        row[11] = 1.0;
        row[12..16].copy_from_slice(&[1.0, 0.0, 0.0, 0.0]);
        cases.extend_from_slice(bytemuck::bytes_of(&row));
    }
    let data = crate::gpu::transfer(&cases, 4);
    let actual: &[f32] = bytemuck::cast_slice(&data);
    for row in actual.as_chunks::<8>().0 {
        assert_eq!(row[4], 1.0, "valid passive opacity rejected");
        assert!(row[..4].iter().all(|v| v.is_finite()));
    }
}

/// One constant-coefficient cell: Stokes emissivity j, absorption alpha, rotation rho,
/// length ds and scalar (colour) emissivity e.
#[derive(Clone, Copy, Debug)]
struct Cell {
    j: [f32; 4],
    alpha: f32,
    rho: [f32; 3],
    ds: f32,
    e: f32,
}

const PATH_CELLS: usize = 8;
type CellPath = [Cell; PATH_CELLS];

/// Binary64 RK4 of dS/dl = j - alpha S + (0, rho x S_pol) and dI/dl = e - alpha I along
/// the photon direction, from the far end of the path (last cell) to the camera.
fn path_reference(path: &CellPath) -> ([f64; 4], f64, f64) {
    let mut s = [0.0_f64; 5];
    for c in path.iter().rev() {
        let j = c.j.map(f64::from);
        let (alpha, rho) = (f64::from(c.alpha), c.rho.map(f64::from));
        let e = f64::from(c.e);
        let rate = |s: [f64; 5]| {
            [
                j[0] - alpha * s[0],
                j[1] - alpha * s[1] + rho[1] * s[3] - rho[2] * s[2],
                j[2] - alpha * s[2] + rho[2] * s[1] - rho[0] * s[3],
                j[3] - alpha * s[3] + rho[0] * s[2] - rho[1] * s[1],
                e - alpha * s[4],
            ]
        };
        let stiffness = alpha + rho.iter().map(|r| r.abs()).sum::<f64>();
        let n = (200.0 * stiffness * f64::from(c.ds)).ceil().max(64.0);
        let h = f64::from(c.ds) / n;
        let add = |s: [f64; 5], k: [f64; 5], w: f64| std::array::from_fn(|i| s[i] + w * k[i]);
        for _ in 0..n as usize {
            let k1 = rate(s);
            let k2 = rate(add(s, k1, 0.5 * h));
            let k3 = rate(add(s, k2, 0.5 * h));
            let k4 = rate(add(s, k3, h));
            s = std::array::from_fn(|i| {
                s[i] + h / 6.0 * (k1[i] + 2.0 * k2[i] + 2.0 * k3[i] + k4[i])
            });
        }
    }
    let depth: f64 = path
        .iter()
        .map(|c| f64::from(c.alpha) * f64::from(c.ds))
        .sum();
    ([s[0], s[1], s[2], s[3]], s[4], (-depth).exp())
}

/// Runs the paths through `bh_test_transfer_path` and asserts each against the accuracy
/// targets. Returns the largest Stokes error relative to the path's unattenuated
/// intensity, the largest relative colour and transmission errors, and how many paths
/// miss the 1e-6 Stokes target.
fn check_paths(paths: &[CellPath]) -> (f64, f64, f64, usize) {
    let cuda = black_hole::cuda::shared_cuda();
    let kernel = cuda.module.load_function("bh_test_transfer_path").unwrap();
    let inputs: Vec<[[f32; 4]; 3 * PATH_CELLS]> = paths
        .iter()
        .map(|path| {
            let mut row = [[0.0; 4]; 3 * PATH_CELLS];
            for (i, c) in path.iter().enumerate() {
                row[3 * i] = c.j;
                row[3 * i + 1] = [c.alpha, c.rho[0], c.rho[1], c.rho[2]];
                row[3 * i + 2] = [c.ds, c.e, 0.0, 0.0];
            }
            row
        })
        .collect();
    let outputs: Vec<[[f32; 4]; 2]> = cuda.run_1d(&kernel, &inputs, 64);
    let mut worst = (0.0_f64, 0.0_f64, 0.0_f64, 0);
    for (path, [stokes, rest]) in paths.iter().zip(&outputs) {
        let (reference, colour, transmission) = path_reference(path);
        // Fixed reference intensities: no path value can exceed its unattenuated sum.
        let scale: f64 = path
            .iter()
            .map(|c| f64::from(c.j[0]) * f64::from(c.ds))
            .sum();
        let colour_scale: f64 = path.iter().map(|c| f64::from(c.e) * f64::from(c.ds)).sum();
        let error = (0..4)
            .map(|i| (f64::from(stokes[i]) - reference[i]).abs())
            .fold(0.0, f64::max)
            / scale;
        let colour = (f64::from(rest[0]) - colour).abs() / colour_scale;
        let transmission = (f64::from(rest[1]) - transmission).abs();
        // A binary32 rotation angle of size theta is only held to about 2^-24 theta.
        let theta: f64 = path
            .iter()
            .map(|c| {
                c.rho
                    .iter()
                    .map(|&r| f64::from(r).powi(2))
                    .sum::<f64>()
                    .sqrt()
                    * f64::from(c.ds)
            })
            .sum();
        let floor = f64::from(f32::EPSILON) * theta;
        assert!(
            error <= 1.0e-6 + floor && colour <= 1.0e-6 && transmission <= 1.0e-6,
            "{path:?}: GPU {stokes:?} {rest:?}, reference {reference:?}; \
             errors {error:e} {colour:e} {transmission:e}"
        );
        worst = (
            worst.0.max(error),
            worst.1.max(colour),
            worst.2.max(transmission),
            worst.3 + usize::from(error > 1.0e-6),
        );
    }
    worst
}

const EMITTER: Cell = Cell {
    j: [1.0, 0.5, -0.3, 0.2],
    alpha: 0.0,
    rho: [0.0; 3],
    ds: 0.125,
    e: 1.0,
};

/// Checklist P1.9: the interactive renderer's cell compositing against an independent
/// constant-coefficient solution, at its branch points and limits.
#[rstest::rstest]
#[case::transparent(EMITTER)]
#[case::full_faraday_turn(Cell { rho: [0.0, 0.0, std::f32::consts::TAU], ..EMITTER })]
#[case::rotation_below_series_switch(Cell { rho: [0.0, 0.0, 0.9e-7 / 0.125], ..EMITTER })]
#[case::rotation_above_series_switch(Cell { rho: [0.0, 0.0, 1.1e-7 / 0.125], ..EMITTER })]
#[case::conversion(Cell { rho: [3.0, -2.0, 0.0], ..EMITTER })]
#[case::subnormal_opacity(Cell { alpha: 1.0e-23, ..EMITTER })]
#[case::optically_thick(Cell { alpha: 400.0, rho: [5.0, 1.0, -7.0], ..EMITTER })]
#[case::absorbing_and_rotating(Cell { alpha: 2.0, rho: [-4.0, 6.0, 15.0], ..EMITTER })]
#[ignore = "requires a CUDA GPU"]
fn transfer_path_edge_cases(#[case] cell: Cell) {
    let errors = check_paths(&[[cell; PATH_CELLS]]);
    eprintln!("errors {:.2e} {:.2e} {:.2e}", errors.0, errors.1, errors.2);
    assert_eq!(errors.3, 0, "Stokes target missed");
}

fn cell() -> impl proptest::strategy::Strategy<Value = Cell> {
    use proptest::prelude::*;
    let alpha = prop_oneof![Just(0.0_f32), (-4.0_f32..1.5).prop_map(|x| 10f32.powf(x))];
    let rho = prop_oneof![
        Just([0.0_f32; 3]),
        [-20.0_f32..20.0, -20.0_f32..20.0, -20.0_f32..20.0]
    ];
    (
        -3.0_f32..1.0,
        [-0.5_f32..0.5, -0.5_f32..0.5, -0.5_f32..0.5],
        alpha,
        rho,
        1.0e-3_f32..1.0,
        -3.0_f32..1.0,
    )
        .prop_map(|(intensity, polarized, alpha, rho, ds, e)| {
            let i = 10f32.powf(intensity);
            Cell {
                j: [i, i * polarized[0], i * polarized[1], i * polarized[2]],
                alpha,
                rho,
                ds,
                e: 10f32.powf(e),
            }
        })
}

proptest::proptest! {
    #![proptest_config(proptest::prelude::ProptestConfig::with_cases(64))]

    /// Checklist P1.9: random fixed paths of constant cells.
    #[test]
    #[ignore = "requires a CUDA GPU"]
    fn transfer_paths_match_the_constant_coefficient_solution(
        paths in proptest::collection::vec(proptest::array::uniform8(cell()), 512)
    ) {
        let errors = check_paths(&paths);
        eprintln!(
            "512 paths: largest Stokes, colour, transmission errors {:.2e} {:.2e} {:.2e}; {} miss the Stokes target",
            errors.0, errors.1, errors.2, errors.3
        );
    }
}
