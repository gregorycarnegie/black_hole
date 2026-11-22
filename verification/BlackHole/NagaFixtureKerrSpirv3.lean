module

public import BlackHole.NagaFixture

/-! Check `add_kerr`'s y derivative outputs (48–63) in a separate process to bound
kernel-reduction memory. -/

@[expose] public section

namespace BlackHole.NagaFixture
open WgslExpr KernelFixture

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem naga_add_kerr_spirv_3 :
    checkPart nagaSpirvFixture "add_kerr" "add_kerr" GExpr.input 16 3 = true := by
  decide +kernel

end BlackHole.NagaFixture
