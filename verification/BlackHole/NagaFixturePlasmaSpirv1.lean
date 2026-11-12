module

public import BlackHole.NagaFixture

/-! Check one plasma model in a separate process to bound kernel-reduction memory. -/

@[expose] public section

namespace BlackHole.NagaFixture
open KernelFixture

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem naga_sample_plasma_spirv_1 :
    check nagaSpirvFixture "sample_plasma.1" "sample_plasma.1" = true := by
  decide +kernel

end BlackHole.NagaFixture
