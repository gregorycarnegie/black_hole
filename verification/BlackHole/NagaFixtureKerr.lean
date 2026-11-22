module

public import BlackHole.NagaFixtureKerr0
public import BlackHole.NagaFixtureKerr1
public import BlackHole.NagaFixtureKerr2
public import BlackHole.NagaFixtureKerr3
public import BlackHole.NagaFixtureKerr4
public import BlackHole.NagaFixtureKerr5

/-! naga's trees for `add_kerr` and its spin scaling are reassociations of the
models (`NagaFixture`). The spin scaling reads `spin` as inputs 200–202 and
`mass` as input 6, as `tests/translation.rs` renames it. The 81 outputs are
checked four at a time in 21 kernel checks across `NagaFixtureKerr0`–`5`; one
check of all of them exceeds a 16 GB runner's memory. -/

@[expose] public section

namespace BlackHole.NagaFixture
open WgslExpr WgslLets KernelFixture

/-- `spinScale`'s inputs as `add_kerr` passes them. -/
def spinInputs (i : ℕ) : GExpr := .input (if i < 3 then 200+i else 6)

set_option maxRecDepth 100000 in
/-- `check_sound`'s conclusion for `add_kerr`, from the 21 checked parts. -/
theorem naga_add_kerr :
    (modelOuts "add_kerr" GExpr.input).length = (nagaOuts nagaFixture "add_kerr").length ∧
      ∀ i (h1 : i < (modelOuts "add_kerr" GExpr.input).length)
        (h2 : i < (nagaOuts nagaFixture "add_kerr").length),
        WgslReassoc.RA (withLets (modelSlots "add_kerr") (modelOuts "add_kerr" GExpr.input)[i])
          (withLets (nagaSlots nagaFixture "add_kerr") (nagaOuts nagaFixture "add_kerr")[i]) :=
  checkParts_sound (k := 4) (c := 21) (by decide +kernel) (by decide +kernel) fun j hj =>
    match j, hj with
    | 0, _ => naga_add_kerr_0
    | 1, _ => naga_add_kerr_1
    | 2, _ => naga_add_kerr_2
    | 3, _ => naga_add_kerr_3
    | 4, _ => naga_add_kerr_4
    | 5, _ => naga_add_kerr_5
    | 6, _ => naga_add_kerr_6
    | 7, _ => naga_add_kerr_7
    | 8, _ => naga_add_kerr_8
    | 9, _ => naga_add_kerr_9
    | 10, _ => naga_add_kerr_10
    | 11, _ => naga_add_kerr_11
    | 12, _ => naga_add_kerr_12
    | 13, _ => naga_add_kerr_13
    | 14, _ => naga_add_kerr_14
    | 15, _ => naga_add_kerr_15
    | 16, _ => naga_add_kerr_16
    | 17, _ => naga_add_kerr_17
    | 18, _ => naga_add_kerr_18
    | 19, _ => naga_add_kerr_19
    | 20, _ => naga_add_kerr_20
    | _+21, h => absurd h (by omega)

set_option maxRecDepth 100000 in
theorem naga_add_kerr_spin :
    check nagaFixture "spin_scale" "add_kerr.let0" spinInputs = true := by
  decide +kernel

end BlackHole.NagaFixture
