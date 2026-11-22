module

public import BlackHole.NagaFixture

/-! Check `add_kerr`'s metric outputs (0–15) in a separate process to bound
kernel-reduction memory. -/

@[expose] public section

namespace BlackHole.NagaFixture
open WgslExpr KernelFixture

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem naga_add_kerr_spirv_0 :
    checkPart nagaSpirvFixture "add_kerr" "add_kerr" GExpr.input 16 0 = true := by
  decide +kernel

end BlackHole.NagaFixture
