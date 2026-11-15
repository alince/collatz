/-
  CollatzFormal/HenselBridge93_14.lean — R2 bands chunk 14 for (93, 1).
-/

import CollatzFormal.HenselBridgeCore

namespace CollatzFormal

set_option exponentiation.threshold 2048

set_option maxRecDepth 20000 in
theorem m93_u1_r2_p34 :
    verifyRangeR2 b1M93U1 b2M93U1 exemptM93U1 (mkBoundsS1 uMMM93U1 denM93U1 b1M93U1) 48 2 = true := by decide

set_option maxRecDepth 20000 in
theorem m93_u1_r2_p35 :
    verifyRangeR2 b1M93U1 b2M93U1 exemptM93U1 (mkBoundsS1 uMMM93U1 denM93U1 b1M93U1) 50 4 = true := by decide

end CollatzFormal
