use std::path::Path;

#[test]
#[ignore = "requires GPU and pinned thermal references; see verification/benchmark-data.md"]
fn headless_thermal_coefficients() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("target/eht-benchmark");
    let mut cases = std::fs::read(root.join("thermal-cases.f32"))
        .expect("Run check_thermal.py and sample_ipole.sh thermal first");
    let expected = std::fs::read(root.join("thermal-expected.f32")).unwrap();
    let table = std::fs::read(root.join("thermal-bessel.f32")).unwrap();
    assert_eq!(table.len(), (8193 + 2) * 8);
    assert!(!cases.is_empty() && cases.len().is_multiple_of(32));
    let samples = cases.len() / 32;
    assert_eq!(expected.len(), samples * 48);
    for invalid in [
        [-1.0, 1.0, 1.0, 0.0, 230e9, 0.0, 0.0, 0.0],
        [1.0, 1001.0, 1.0, 0.0, 230e9, 0.0, 0.0, 0.0],
        [1.0, 1.0, 1.0, 0.0, 230e9, 1.1, 0.0, 0.0],
        [1.0, 1.0, 1.0, 0.0, f32::NAN, 0.0, 0.0, 0.0],
    ] {
        cases.extend_from_slice(bytemuck::bytes_of(&invalid));
    }
    let count = cases.len() / 32;
    let data = crate::gpu::thermal(&table, &cases, count as u32);
    let actual: &[f32] = bytemuck::cast_slice(&data);
    let expected: Vec<_> = expected
        .as_chunks::<4>()
        .0
        .iter()
        .map(|v| f32::from_le_bytes(*v))
        .collect();
    let mut maxima = [0.0_f32; 3];
    for row in actual[samples * 12..].as_chunks::<12>().0.iter() {
        assert_eq!(row, &[0.0; 12], "invalid thermal query accepted");
    }
    for (i, (row, reference)) in actual
        .as_chunks::<12>()
        .0
        .iter()
        .zip(expected.as_chunks::<12>().0.iter())
        .enumerate()
    {
        assert_eq!(row[11], 1.0, "thermal coefficient query {i} rejected");
        let opacity = &row[4..8];
        let scale = opacity.iter().map(|v| v.abs()).fold(0.0_f32, f32::max);
        if scale > 0.0 {
            let polarized = opacity[1..]
                .iter()
                .map(|v| (v / scale).powi(2))
                .sum::<f32>()
                .sqrt();
            assert!(
                polarized <= 0.99001 * opacity[0] / scale,
                "nonpassive thermal query {i}"
            );
        }
        for (family, maximum) in maxima.iter_mut().enumerate() {
            let length = if family == 2 { 3 } else { 4 };
            let start = family * 4;
            // Tiny coefficients below 1e-20 in the stated physical units have an absolute floor.
            let scale = reference[start..start + length]
                .iter()
                .map(|x| x.abs())
                .fold(1e-20_f32, f32::max);
            for component in start..start + length {
                let error = (row[component] - reference[component]).abs() / scale;
                *maximum = maximum.max(error);
                assert!(
                    row[component].is_finite() && error < 0.0003,
                    "thermal query {i}, component {component}: {} vs {}, scaled error {error}",
                    row[component],
                    reference[component]
                );
            }
        }
    }
    std::fs::write(root.join("thermal-gpu.f32"), &data).unwrap();
    eprintln!(
        "{samples} thermal GPU queries: max family-scaled errors (j, alpha, rho) = {maxima:?}"
    );
}
