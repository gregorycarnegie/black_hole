use std::path::Path;

#[test]
#[ignore = "requires EHT snapshot/camera/reference files and GPU; see verification/benchmark-data.md"]
fn headless_snapshot_image() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("target/eht-benchmark");
    let read =
        |name: &str| std::fs::read(root.join(name)).expect("Run check_image.py prepare first");
    let header = read("sample-header.f32");
    let grids = [
        read("sample-primitives0.f32"),
        read("sample-primitives1.f32"),
        read("sample-physical.f32"),
    ];
    assert_eq!(header.len(), 80);
    for grid in &grids {
        assert_eq!(grid.len(), 290 * 130 * 130 * 16);
    }
    let table = read("thermal-bessel.f32");
    assert_eq!(table.len(), 8195 * 8);
    let seeds = read("image-seeds.f32");
    assert!(!seeds.is_empty() && seeds.len().is_multiple_of(64));
    let count = seeds.len() / 64;
    let settings = read("image-settings.f32");
    assert_eq!(settings.len(), 16);
    assert_eq!(
        f32::from_le_bytes(settings[8..12].try_into().unwrap()),
        count as f32
    );
    let mut objects = vec![0u8; 1040];
    objects[..4].copy_from_slice(&1i32.to_le_bytes());
    objects[528..532].copy_from_slice(&1f32.to_le_bytes());
    objects[788..792].copy_from_slice(&0.9375f32.to_le_bytes());
    // The production RK4 controller, then the Dormand–Prince experiment (checklist P1.1).
    // Compare each with `python verification/check_image.py compare --image <file>`.
    for (dormand_prince, file) in [(false, "image-gpu.f32"), (true, "image-gpu-dp45.f32")] {
        let data = crate::gpu::image(
            &objects,
            &header,
            &grids[0],
            &grids[1],
            &grids[2],
            &table,
            &seeds,
            &settings,
            count as u32,
            dormand_prince,
        );
        std::fs::write(root.join(file), &data).unwrap();
        let values: &[f32] = bytemuck::cast_slice(&data);
        assert!(
            values.iter().all(|v| v.is_finite()),
            "Nonfinite snapshot image"
        );
        let mut statuses = [0usize; 7];
        for row in values.as_chunks::<16>().0 {
            let status = row[5] as usize;
            assert!(status < 7);
            statuses[status] += 1;
        }
        eprintln!(
            "{file}: {count} snapshot image rays; statuses [unused,captured,escaped,exhausted,step failure,sampling failure,thermal failure] = {statuses:?}"
        );
        assert_eq!(
            statuses[1] + statuses[2],
            count,
            "Unresolved rays; inspect saved image output"
        );
    }
}
