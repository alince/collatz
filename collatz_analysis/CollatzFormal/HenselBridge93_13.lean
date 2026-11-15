/-
  CollatzFormal/HenselBridge93_13.lean — R2 bands chunk 13 for (93, 1).
-/

import CollatzFormal.HenselBridgeCore

namespace CollatzFormal

set_option exponentiation.threshold 2048

set_option maxRecDepth 20000 in
theorem m93_u1_r2_p31 :
    verifyRangeR2 b1M93U1 b2M93U1 exemptM93U1 (mkBoundsS1 uMMM93U1 denM93U1 b1M93U1) 44 1 = true := by decide

set_option maxRecDepth 20000 in
theorem m93_u1_r2_p32 :
    verifyRangeR2 b1M93U1 b2M93U1 exemptM93U1 (mkBoundsS1 uMMM93U1 denM93U1 b1M93U1) 45 1 = true := by decide

set_option maxRecDepth 20000 in
theorem m93_u1_r2_p33 :
    verifyRangeR2 b1M93U1 b2M93U1 exemptM93U1 (mkBoundsS1 uMMM93U1 denM93U1 b1M93U1) 46 2 = true := by decide

end CollatzFormal
