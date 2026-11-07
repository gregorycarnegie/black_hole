module

public import BlackHole.NagaFixture

/-! naga's trees for `sample_plasma`, all four disk models, are
reassociations of the models (`NagaFixture`), for the WGSL front end and the
SPIR-V round trip. -/

@[expose] public section

namespace BlackHole.NagaFixture
open KernelFixture

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem naga_sample_plasma :
    ["sample_plasma.0", "sample_plasma.1", "sample_plasma.2", "sample_plasma.3"].all
      (fun n => check nagaFixture n n) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem naga_sample_plasma_spirv :
    ["sample_plasma.0", "sample_plasma.1", "sample_plasma.2", "sample_plasma.3"].all
      (fun n => check nagaSpirvFixture n n) = true := by decide +kernel

end BlackHole.NagaFixture
