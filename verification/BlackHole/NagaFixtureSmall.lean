module

public import BlackHole.NagaFixture

/-! naga's trees for every `small` kernel, from naga's WGSL front end, are
reassociations of the models (`NagaFixture`). Each kernel is a separate
kernel check to bound kernel-reduction memory. -/

@[expose] public section

namespace BlackHole.NagaFixture
open KernelFixture

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem naga_small_geodesic_rhs :
    check nagaFixture "geodesic_rhs" "geodesic_rhs" = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem naga_small_atan_poly :
    check nagaFixture "atan_poly" "atan_poly" = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem naga_small_tonemap :
    check nagaFixture "tonemap" "tonemap" = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem naga_small_heatmap_color :
    check nagaFixture "heatmap_color" "heatmap_color" = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem naga_small_polarization_color :
    check nagaFixture "polarization_color" "polarization_color" = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem naga_small_spatial_unit :
    check nagaFixture "spatial_unit" "spatial_unit" = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem naga_small_screen_frame :
    check nagaFixture "screen_frame" "screen_frame" = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem naga_small_atan2_arith :
    check nagaFixture "atan2_arith" "atan2_arith" = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem naga_small_kerr_radius :
    check nagaFixture "kerr_radius" "kerr_radius" = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem naga_small_sincos :
    check nagaFixture "sincos" "sincos" = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem naga_small_transfer_phi :
    check nagaFixture "transfer_phi" "transfer_phi" = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem naga_small_faraday_rotation :
    check nagaFixture "faraday_rotation" "faraday_rotation" = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem naga_small_polarized_cell :
    check nagaFixture "polarized_cell" "polarized_cell" = true := by
  decide +kernel

theorem naga_small : small.all (fun n => check nagaFixture n n) = true := by
  simp only [small, List.all_cons, List.all_nil,
    naga_small_geodesic_rhs, naga_small_atan_poly, naga_small_tonemap,
    naga_small_heatmap_color, naga_small_polarization_color, naga_small_spatial_unit,
    naga_small_screen_frame, naga_small_atan2_arith, naga_small_kerr_radius,
    naga_small_sincos, naga_small_transfer_phi, naga_small_faraday_rotation,
    naga_small_polarized_cell]
  rfl

end BlackHole.NagaFixture
