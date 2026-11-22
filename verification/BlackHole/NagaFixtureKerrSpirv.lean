module

public import BlackHole.NagaFixtureKerr
public import BlackHole.NagaFixtureKerrSpirv0
public import BlackHole.NagaFixtureKerrSpirv1
public import BlackHole.NagaFixtureKerrSpirv2
public import BlackHole.NagaFixtureKerrSpirv3
public import BlackHole.NagaFixtureKerrSpirv4
public import BlackHole.NagaFixtureKerrSpirv5

/-! The trees read back from the SPIR-V naga writes for `add_kerr` and its
spin scaling are reassociations of the models (`NagaFixture`), checked in 21
parts like `NagaFixtureKerr`. -/

@[expose] public section

namespace BlackHole.NagaFixture
open WgslExpr WgslLets KernelFixture

set_option maxRecDepth 100000 in
theorem naga_add_kerr_spirv :
    (modelOuts "add_kerr" GExpr.input).length = (nagaOuts nagaSpirvFixture "add_kerr").length ∧
      ∀ i (h1 : i < (modelOuts "add_kerr" GExpr.input).length)
        (h2 : i < (nagaOuts nagaSpirvFixture "add_kerr").length),
        WgslReassoc.RA (withLets (modelSlots "add_kerr") (modelOuts "add_kerr" GExpr.input)[i])
          (withLets (nagaSlots nagaSpirvFixture "add_kerr")
            (nagaOuts nagaSpirvFixture "add_kerr")[i]) :=
  checkParts_sound (k := 4) (c := 21) (by decide +kernel) (by decide +kernel) fun j hj =>
    match j, hj with
    | 0, _ => naga_add_kerr_spirv_0
    | 1, _ => naga_add_kerr_spirv_1
    | 2, _ => naga_add_kerr_spirv_2
    | 3, _ => naga_add_kerr_spirv_3
    | 4, _ => naga_add_kerr_spirv_4
    | 5, _ => naga_add_kerr_spirv_5
    | 6, _ => naga_add_kerr_spirv_6
    | 7, _ => naga_add_kerr_spirv_7
    | 8, _ => naga_add_kerr_spirv_8
    | 9, _ => naga_add_kerr_spirv_9
    | 10, _ => naga_add_kerr_spirv_10
    | 11, _ => naga_add_kerr_spirv_11
    | 12, _ => naga_add_kerr_spirv_12
    | 13, _ => naga_add_kerr_spirv_13
    | 14, _ => naga_add_kerr_spirv_14
    | 15, _ => naga_add_kerr_spirv_15
    | 16, _ => naga_add_kerr_spirv_16
    | 17, _ => naga_add_kerr_spirv_17
    | 18, _ => naga_add_kerr_spirv_18
    | 19, _ => naga_add_kerr_spirv_19
    | 20, _ => naga_add_kerr_spirv_20
    | _+21, h => absurd h (by omega)

set_option maxRecDepth 100000 in
theorem naga_add_kerr_spin_spirv :
    check nagaSpirvFixture "spin_scale" "add_kerr.let0" spinInputs = true := by
  decide +kernel

end BlackHole.NagaFixture
