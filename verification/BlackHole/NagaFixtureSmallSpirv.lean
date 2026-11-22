module

public import BlackHole.NagaFixture

/-! naga's trees for every `small` kernel, from the SPIR-V round trip, are
reassociations of the models (`NagaFixture`). Each kernel is a separate
kernel check to bound kernel-reduction memory. -/

@[expose] public section

namespace BlackHole.NagaFixture
open KernelFixture

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem naga_small_spirv_geodesic_rhs :
    check nagaSpirvFixture "geodesic_rhs" "geodesic_rhs" = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem naga_small_spirv_atan_poly :
    check nagaSpirvFixture "atan_poly" "atan_poly" = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem naga_small_spirv_tonemap :
    check nagaSpirvFixture "tonemap" "tonemap" = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem naga_small_spirv_heatmap_color :
    check nagaSpirvFixture "heatmap_color" "heatmap_color" = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem naga_small_spirv_polarization_color :
    check nagaSpirvFixture "polarization_color" "polarization_color" = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem naga_small_spirv_spatial_unit :
    check nagaSpirvFixture "spatial_unit" "spatial_unit" = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem naga_small_spirv_screen_frame :
    check nagaSpirvFixture "screen_frame" "screen_frame" = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem naga_small_spirv_atan2_arith :
    check nagaSpirvFixture "atan2_arith" "atan2_arith" = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem naga_small_spirv_kerr_radius :
    check nagaSpirvFixture "kerr_radius" "kerr_radius" = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem naga_small_spirv_sincos :
    check nagaSpirvFixture "sincos" "sincos" = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem naga_small_spirv_transfer_phi :
    check nagaSpirvFixture "transfer_phi" "transfer_phi" = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem naga_small_spirv_faraday_rotation :
    check nagaSpirvFixture "faraday_rotation" "faraday_rotation" = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem naga_small_spirv_polarized_cell :
    check nagaSpirvFixture "polarized_cell" "polarized_cell" = true := by
  decide +kernel

theorem naga_small_spirv : small.all (fun n => check nagaSpirvFixture n n) = true := by
  simp only [small, List.all_cons, List.all_nil,
    naga_small_spirv_geodesic_rhs, naga_small_spirv_atan_poly, naga_small_spirv_tonemap,
    naga_small_spirv_heatmap_color, naga_small_spirv_polarization_color,
    naga_small_spirv_spatial_unit,
    naga_small_spirv_screen_frame, naga_small_spirv_atan2_arith, naga_small_spirv_kerr_radius,
    naga_small_spirv_sincos, naga_small_spirv_transfer_phi, naga_small_spirv_faraday_rotation,
    naga_small_spirv_polarized_cell]
  rfl

end BlackHole.NagaFixture
