module

public import BlackHole.NagaFixture

/-! Check `add_kerr`'s inverse outputs (16–31) four at a time (`checkPart` with `k = 4`),
in a separate process to bound kernel-reduction memory. -/

@[expose] public section

namespace BlackHole.NagaFixture
open WgslExpr KernelFixture

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem naga_add_kerr_4 :
    checkPart nagaFixture "add_kerr" "add_kerr" GExpr.input 4 4 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem naga_add_kerr_5 :
    checkPart nagaFixture "add_kerr" "add_kerr" GExpr.input 4 5 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem naga_add_kerr_6 :
    checkPart nagaFixture "add_kerr" "add_kerr" GExpr.input 4 6 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem naga_add_kerr_7 :
    checkPart nagaFixture "add_kerr" "add_kerr" GExpr.input 4 7 = true := by
  decide +kernel

end BlackHole.NagaFixture
