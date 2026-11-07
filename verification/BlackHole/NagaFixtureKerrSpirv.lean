module

public import BlackHole.NagaFixtureKerr

/-! The trees read back from the SPIR-V naga writes for `add_kerr` and its
spin scaling are reassociations of the models (`NagaFixture`). -/

@[expose] public section

namespace BlackHole.NagaFixture
open KernelFixture

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem naga_add_kerr_spirv : check nagaSpirvFixture "add_kerr" "add_kerr" = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem naga_add_kerr_spin_spirv :
    check nagaSpirvFixture "spin_scale" "add_kerr.let0" spinInputs = true := by
  decide +kernel

end BlackHole.NagaFixture
