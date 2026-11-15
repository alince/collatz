/-
  CollatzFormal/HenselBridge93_00.lean — R2 bands chunk 0 for (93, 1).
-/

import CollatzFormal.HenselBridgeCore

namespace CollatzFormal

set_option exponentiation.threshold 2048

set_option maxRecDepth 20000 in
theorem m93_u1_r2_p0 :
    verifyRangeR2 b1M93U1 b2M93U1 exemptM93U1 (mkBoundsS1 uMMM93U1 denM93U1 b1M93U1) 1 12 = true := by decide

set_option maxRecDepth 20000 in
theorem m93_u1_r2_p1 :
    verifyRangeR2 b1M93U1 b2M93U1 exemptM93U1 (mkBoundsS1 uMMM93U1 denM93U1 b1M93U1) 13 2 = true := by decide

set_option maxRecDepth 20000 in
theorem m93_u1_r2_p2 :
    verifyRangeR2 b1M93U1 b2M93U1 exemptM93U1 (mkBoundsS1 uMMM93U1 denM93U1 b1M93U1) 15 1 = true := by decide

end CollatzFormal
