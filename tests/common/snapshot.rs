use bevy::render::render_resource::BufferUsages;
use std::path::Path;

#[test]
#[ignore = "requires GPU and exported EHT snapshot; see verification/benchmark-data.md"]
fn headless_snapshot_sampling() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("target/eht-benchmark");
    let read = |name: &str| {
        std::fs::read(root.join(format!("sample-{name}.f32")))
            .expect("Run verification/check_sampling.py and sample_ipole.sh first")
    };
    let header = read("header");
    assert_eq!(header.len(), 80);
    let h: Vec<f32> = header
        .as_chunks::<4>()
        .0
        .iter()
        .map(|v| f32::from_le_bytes(*v))
        .collect();
    assert!(h.iter().all(|v| v.is_finite()));
    assert_eq!(&h[8..11], &[288.0, 128.0, 128.0]);
    assert_eq!(&h[12..16], &[0.9375, 0.3, 1.0, 100.0]);
    let mut positions = read("positions");
    let expected_bytes = read("expected");
    assert!(!positions.is_empty() && positions.len().is_multiple_of(16));
    let samples = positions.len() / 16;
    assert_eq!(expected_bytes.len(), samples * 64);
    for pos in [
        [0.0_f32; 4],
        [f32::NAN, 0.0, 0.0, 0.0],
        [11000.0, 0.0, 0.0, 0.0],
        [1.0, 0.0, 0.0, 0.0],
        [0.0, 1001.0, 0.0, 0.0],
    ] {
        positions.extend_from_slice(bytemuck::bytes_of(&pos));
    }
    let count = positions.len() / 16;

    let grids: Vec<_> = ["primitives0", "primitives1", "physical"]
        .map(read)
        .into_iter()
        .collect();
    for data in &grids {
        assert_eq!(data.len(), 290 * 130 * 130 * 16);
        assert!(data.len() <= 128 * 1024 * 1024);
    }
    let data = crate::gpu::run_groups(
        include_str!("../snapshot.wesl"),
        "check_snapshot",
        &[
            &[],
            &[
                (0, &header, BufferUsages::UNIFORM),
                (1, &grids[0], BufferUsages::STORAGE),
                (2, &grids[1], BufferUsages::STORAGE),
                (3, &grids[2], BufferUsages::STORAGE),
                (4, &positions, BufferUsages::STORAGE),
            ],
        ],
        (count * 64) as u64,
        (count as u32).div_ceil(64),
    );
    let values: &[f32] = bytemuck::cast_slice(&data);
    let expected: Vec<_> = expected_bytes
        .as_chunks::<4>()
        .0
        .iter()
        .map(|v| f32::from_le_bytes(*v))
        .collect();
    let mut errors = [0.0_f32; 4];
    for (i, (&actual, &reference)) in values.iter().zip(&expected).enumerate() {
        assert!(actual.is_finite(), "nonfinite GPU sample {i}");
        let component = i % 16;
        if component == 15 {
            assert_eq!(actual, reference, "emission mask at sample {}", i / 16);
        } else {
            // Phi is periodic: the two seam representatives describe the same point.
            let mut difference = (actual - reference).abs();
            if component == 14 {
                difference = difference.min((difference - std::f32::consts::TAU).abs());
            }
            let error = difference / reference.abs().max(1.0);
            errors[component / 4] = errors[component / 4].max(error);
            assert!(
                error < 0.0004,
                "GPU sample {}, component {component}: {actual} vs {reference}, scaled error {error}",
                i / 16
            );
        }
    }
    for invalid in values[samples * 16..].as_chunks::<16>().0 {
        assert_eq!(&invalid[..15], &[0.0; 15]);
        assert_eq!(invalid[15], -1.0);
    }
    std::fs::write(root.join("sampling-gpu.f32"), &*data).unwrap();
    eprintln!(
        "{samples} GPU snapshot samples: maximum scaled errors (u, b, physical, native) = {errors:?}"
    );
}
