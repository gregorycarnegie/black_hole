use black_hole::physics::kerr_horizon_radius_rg;

#[test]
fn rust_horizon_matches_lean_binary32_fixtures() {
    let fixtures = include_str!("../verification/fixtures/horizon-binary32.csv");
    let mut count = 0;
    for line in fixtures.lines() {
        let (input, output) = line.trim().split_once(',').unwrap();
        let input: u32 = input.parse().unwrap();
        let expected: u32 = output.parse().unwrap();
        let spin = f32::from_bits(input);
        assert_eq!(
            kerr_horizon_radius_rg(spin).to_bits(),
            expected,
            "spin={spin}"
        );
        count += 1;
    }
    assert_eq!(count, 9);
}
