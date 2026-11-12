module

public import BlackHole.NagaFixture

/-! Check one plasma model in a separate process to bound kernel-reduction memory. -/

@[expose] public section

namespace BlackHole.NagaFixture
open KernelFixture

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem naga_sample_plasma_3 :
    check nagaFixture "sample_plasma.3" "sample_plasma.3" = true := by
  decide +kernel

end BlackHole.NagaFixture
