module

public import BlackHole.NagaFixture

/-! Check `add_kerr`'s y derivative outputs (48–63) four at a time (`checkPart` with `k = 4`),
in a separate process to bound kernel-reduction memory. -/

@[expose] public section

namespace BlackHole.NagaFixture
open WgslExpr KernelFixture

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem naga_add_kerr_12 :
    checkPart nagaFixture "add_kerr" "add_kerr" GExpr.input 4 12 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem naga_add_kerr_13 :
    checkPart nagaFixture "add_kerr" "add_kerr" GExpr.input 4 13 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem naga_add_kerr_14 :
    checkPart nagaFixture "add_kerr" "add_kerr" GExpr.input 4 14 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem naga_add_kerr_15 :
    checkPart nagaFixture "add_kerr" "add_kerr" GExpr.input 4 15 = true := by
  decide +kernel

end BlackHole.NagaFixture
