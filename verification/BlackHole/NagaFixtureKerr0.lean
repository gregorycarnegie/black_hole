module

public import BlackHole.NagaFixture

/-! Check `add_kerr`'s metric outputs (0–15) four at a time (`checkPart` with `k = 4`),
in a separate process to bound kernel-reduction memory. -/

@[expose] public section

namespace BlackHole.NagaFixture
open WgslExpr KernelFixture

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem naga_add_kerr_0 :
    checkPart nagaFixture "add_kerr" "add_kerr" GExpr.input 4 0 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem naga_add_kerr_1 :
    checkPart nagaFixture "add_kerr" "add_kerr" GExpr.input 4 1 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem naga_add_kerr_2 :
    checkPart nagaFixture "add_kerr" "add_kerr" GExpr.input 4 2 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem naga_add_kerr_3 :
    checkPart nagaFixture "add_kerr" "add_kerr" GExpr.input 4 3 = true := by
  decide +kernel

end BlackHole.NagaFixture
