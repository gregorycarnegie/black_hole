use black_hole::physics::*;
use rstest::rstest;

/// geodesic.wgsl is validated together with the relativity checks that call into it.
const GEODESIC_WITH_CHECKS: &str = concat!(
    include_str!("../assets/shaders/geodesic.wgsl"),
    "\n",
    include_str!("relativity.wgsl")
);

#[rstest]
#[case::geodesic(GEODESIC_WITH_CHECKS)]
#[case::accumulate(include_str!("../assets/shaders/accumulate.wgsl"))]
fn shader_validates(#[case] source: &str) {
    let module = naga::front::wgsl::parse_str(source)
        .unwrap_or_else(|err| panic!("{}", err.emit_to_string(source)));
    naga::valid::Validator::new(
        naga::valid::ValidationFlags::all(),
        naga::valid::Capabilities::all(),
    )
    .validate(&module)
    .unwrap();
}

#[test]
fn gravitational_units_match_schwarzschild_at_zero_spin() {
    assert_eq!(kerr_horizon_radius_rg(0.0), SCHWARZSCHILD_RADIUS);
    assert_eq!(kerr_isco_radius_rg(0.0), 6.0);
}

#[rstest]
fn gravitational_units_preserve_kerr_radii(#[values(-0.999, -0.5, 0.0, 0.5, 0.999)] spin: f32) {
    let horizon = kerr_horizon_radius_rg(spin);
    let isco = kerr_isco_radius_rg(spin);
    assert!(horizon > 0.0 && isco > horizon);
    assert!((kerr_horizon_radius(spin) / (SAGA_RS * 0.5) - horizon).abs() < 1e-6);
    assert!((kerr_isco_radius(spin) / (SAGA_RS * 0.5) - isco).abs() < 1e-6);
}
