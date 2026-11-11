use black_hole::{
    cuda::{KERNEL_NAMES, PTX, kernels_source_sha256, ptx_recorded_sha256, shared_cuda},
    physics::*,
};
use googletest::{assert_that, matchers::near};
use rstest::rstest;

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

#[path = "common/atan2.rs"]
mod atan2;
#[path = "common/geodesic_gpu.rs"]
mod geodesic_gpu;
#[path = "common/sincos.rs"]
mod sincos;

#[path = "common/energy.rs"]
mod energy;

#[test]
fn ptx_matches_cuda_oxide_kernel_sources() {
    assert_eq!(
        ptx_recorded_sha256(),
        Some(kernels_source_sha256().as_str()),
        "src/compute/kernels.ptx is out of date with tools/cuda/kernels.rs; run `python tools/cuda/build.py`"
    );
    assert!(
        !PTX.contains(".extern .func"),
        "PTX must be self-contained without unresolved .extern .func symbols"
    );
    for kernel in KERNEL_NAMES {
        let marker = format!(".visible .entry {kernel}(");
        assert!(
            PTX.contains(&marker),
            "missing CUDA kernel entry `{kernel}` in src/compute/kernels.ptx"
        );
    }
}

#[test]
#[ignore = "requires a CUDA GPU; run with -- --ignored"]
fn cuda_module_loads_all_kernels() {
    let cuda = shared_cuda();
    for kernel in KERNEL_NAMES {
        cuda.module
            .load_function(kernel)
            .unwrap_or_else(|err| panic!("failed to load `{kernel}`: {err}"));
    }
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
    assert_that!(
        kerr_horizon_radius(spin) / (SAGA_RS * 0.5),
        near(horizon, 1e-6)
    );
    assert_that!(kerr_isco_radius(spin) / (SAGA_RS * 0.5), near(isco, 1e-6));
}
