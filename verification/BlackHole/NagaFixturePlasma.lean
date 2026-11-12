module

public import BlackHole.NagaFixturePlasma0
public import BlackHole.NagaFixturePlasma1
public import BlackHole.NagaFixturePlasma2
public import BlackHole.NagaFixturePlasma3
public import BlackHole.NagaFixturePlasmaSpirv0
public import BlackHole.NagaFixturePlasmaSpirv1
public import BlackHole.NagaFixturePlasmaSpirv2
public import BlackHole.NagaFixturePlasmaSpirv3

/-! naga's trees for `sample_plasma`, all four disk models, are
reassociations of the models (`NagaFixture`), for the WGSL front end and the
SPIR-V round trip. -/

@[expose] public section

namespace BlackHole.NagaFixture
open KernelFixture

theorem naga_sample_plasma :
    ["sample_plasma.0", "sample_plasma.1", "sample_plasma.2", "sample_plasma.3"].all
      (fun n => check nagaFixture n n) = true := by
  simp only [List.all_cons, List.all_nil, naga_sample_plasma_0, naga_sample_plasma_1,
    naga_sample_plasma_2, naga_sample_plasma_3]
  rfl

theorem naga_sample_plasma_spirv :
    ["sample_plasma.0", "sample_plasma.1", "sample_plasma.2", "sample_plasma.3"].all
      (fun n => check nagaSpirvFixture n n) = true := by
  simp only [List.all_cons, List.all_nil, naga_sample_plasma_spirv_0, naga_sample_plasma_spirv_1,
    naga_sample_plasma_spirv_2, naga_sample_plasma_spirv_3]
  rfl

end BlackHole.NagaFixture
