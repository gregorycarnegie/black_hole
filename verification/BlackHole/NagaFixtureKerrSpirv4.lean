module

public import BlackHole.NagaFixture

/-! Check `add_kerr`'s z derivative outputs (64–79) four at a time (`checkPart` with `k = 4`),
in a separate process to bound kernel-reduction memory. -/

@[expose] public section

namespace BlackHole.NagaFixture
open WgslExpr KernelFixture

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem naga_add_kerr_spirv_16 :
    checkPart nagaSpirvFixture "add_kerr" "add_kerr" GExpr.input 4 16 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem naga_add_kerr_spirv_17 :
    checkPart nagaSpirvFixture "add_kerr" "add_kerr" GExpr.input 4 17 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem naga_add_kerr_spirv_18 :
    checkPart nagaSpirvFixture "add_kerr" "add_kerr" GExpr.input 4 18 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem naga_add_kerr_spirv_19 :
    checkPart nagaSpirvFixture "add_kerr" "add_kerr" GExpr.input 4 19 = true := by
  decide +kernel

end BlackHole.NagaFixture
