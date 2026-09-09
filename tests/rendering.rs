use black_hole::physics::*;

#[test]
fn shaders_validate() {
    for source in [
        include_str!("../assets/shaders/geodesic.wgsl"),
        include_str!("../assets/shaders/accumulate.wgsl"),
    ] {
        let module = naga::front::wgsl::parse_str(source)
            .unwrap_or_else(|err| panic!("{}", err.emit_to_string(source)));
        naga::valid::Validator::new(
            naga::valid::ValidationFlags::all(),
            naga::valid::Capabilities::all(),
        )
        .validate(&module)
        .unwrap();
    }
}

#[test]
fn gravitational_units_preserve_kerr_radii() {
    assert_eq!(kerr_horizon_radius_rg(0.0), SCHWARZSCHILD_RADIUS);
    assert_eq!(kerr_isco_radius_rg(0.0), 6.0);
    for spin in [-0.999, -0.5, 0.0, 0.5, 0.999] {
        let horizon = kerr_horizon_radius_rg(spin);
        let isco = kerr_isco_radius_rg(spin);
        assert!(horizon > 0.0 && isco > horizon);
        assert!((kerr_horizon_radius(spin) / (SAGA_RS * 0.5) - horizon).abs() < 1e-6);
        assert!((kerr_isco_radius(spin) / (SAGA_RS * 0.5) - isco).abs() < 1e-6);
    }
}
