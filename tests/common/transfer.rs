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
