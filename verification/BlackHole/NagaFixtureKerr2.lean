module

public import BlackHole.NagaFixture

/-! Check `add_kerr`'s x derivative outputs (32–47) four at a time (`checkPart` with `k = 4`),
in a separate process to bound kernel-reduction memory. -/

@[expose] public section

namespace BlackHole.NagaFixture
open WgslExpr KernelFixture

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem naga_add_kerr_8 :
    checkPart nagaFixture "add_kerr" "add_kerr" GExpr.input 4 8 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem naga_add_kerr_9 :
    checkPart nagaFixture "add_kerr" "add_kerr" GExpr.input 4 9 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem naga_add_kerr_10 :
    checkPart nagaFixture "add_kerr" "add_kerr" GExpr.input 4 10 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem naga_add_kerr_11 :
    checkPart nagaFixture "add_kerr" "add_kerr" GExpr.input 4 11 = true := by
  decide +kernel

end BlackHole.NagaFixture
