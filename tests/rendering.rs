use black_hole::physics::*;
use rstest::rstest;

mod common;

#[path = "common/gpu.rs"]
mod gpu;

#[path = "common/snapshot.rs"]
mod snapshot;

#[path = "common/transfer.rs"]
mod transfer;

#[path = "common/thermal.rs"]
mod thermal;

#[path = "common/image.rs"]
mod image;

#[path = "common/controller.rs"]
mod controller;

#[path = "common/sincos.rs"]
mod sincos;

#[path = "common/energy.rs"]
mod energy;

#[rstest]
#[case::geodesic(include_str!("../assets/shaders/geodesic.wesl"))]
#[case::relativity(common::GEODESIC_WITH_CHECKS)]
#[case::accumulate(include_str!("../assets/shaders/accumulate.wesl"))]
#[case::snapshot(include_str!("snapshot.wesl"))]
#[case::transfer(include_str!("transfer.wesl"))]
#[case::thermal(include_str!("thermal.wesl"))]
#[case::image(include_str!("image.wesl"))]
#[case::controller(include_str!("controller.wesl"))]
#[case::sincos(include_str!("sincos.wesl"))]
#[case::energy(include_str!("energy.wesl"))]
fn shader_validates(#[case] source: &str) {
    let source = common::compile_wesl(source);
    let module = naga::front::wgsl::parse_str(&source)
        .unwrap_or_else(|err| panic!("{}", err.emit_to_string(&source)));
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
