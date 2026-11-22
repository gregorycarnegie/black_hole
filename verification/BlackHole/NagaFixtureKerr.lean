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
checked in six parts (`NagaFixtureKerr0`–`5`); one kernel check of all of them
exceeds a 16 GB runner's memory. -/

@[expose] public section

namespace BlackHole.NagaFixture
open WgslExpr WgslLets KernelFixture

/-- `spinScale`'s inputs as `add_kerr` passes them. -/
def spinInputs (i : ℕ) : GExpr := .input (if i < 3 then 200+i else 6)

/-- `check_sound`'s conclusion for `add_kerr`, from the six checked parts. -/
set_option maxRecDepth 100000 in
theorem naga_add_kerr :
    (modelOuts "add_kerr" GExpr.input).length = (nagaOuts nagaFixture "add_kerr").length ∧
      ∀ i (h1 : i < (modelOuts "add_kerr" GExpr.input).length)
        (h2 : i < (nagaOuts nagaFixture "add_kerr").length),
        WgslReassoc.RA (withLets (modelSlots "add_kerr") (modelOuts "add_kerr" GExpr.input)[i])
          (withLets (nagaSlots nagaFixture "add_kerr") (nagaOuts nagaFixture "add_kerr")[i]) :=
  checkParts_sound (k := 16) (c := 6) (by decide +kernel) (by decide +kernel) fun j hj =>
    match j, hj with
    | 0, _ => naga_add_kerr_0
    | 1, _ => naga_add_kerr_1
    | 2, _ => naga_add_kerr_2
    | 3, _ => naga_add_kerr_3
    | 4, _ => naga_add_kerr_4
    | 5, _ => naga_add_kerr_5
    | _+6, h => absurd h (by omega)

set_option maxRecDepth 100000 in
theorem naga_add_kerr_spin :
    check nagaFixture "spin_scale" "add_kerr.let0" spinInputs = true := by
  decide +kernel

end BlackHole.NagaFixture
