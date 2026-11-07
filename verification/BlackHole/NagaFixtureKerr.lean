module

public import BlackHole.NagaFixture

/-! naga's trees for `add_kerr` and its spin scaling are reassociations of the
models (`NagaFixture`). The spin scaling reads `spin` as inputs 200–202 and
`mass` as input 6, as `tests/translation.rs` renames it. -/

@[expose] public section

namespace BlackHole.NagaFixture
open WgslExpr

/-- `spinScale`'s inputs as `add_kerr` passes them. -/
def spinInputs (i : ℕ) : GExpr := .input (if i < 3 then 200+i else 6)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem naga_add_kerr : check "add_kerr" "add_kerr" = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem naga_add_kerr_spin : check "spin_scale" "add_kerr.let0" spinInputs = true := by
  decide +kernel

end BlackHole.NagaFixture
