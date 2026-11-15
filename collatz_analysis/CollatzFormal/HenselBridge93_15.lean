/-
  CollatzFormal/HenselBridge93_15.lean — R2 bands chunk 15 for (93, 1).
-/

import CollatzFormal.HenselBridgeCore

namespace CollatzFormal

set_option exponentiation.threshold 2048

set_option maxRecDepth 20000 in
theorem m93_u1_r2_p36a :
    verifyRangeR2 b1M93U1 b2M93U1 exemptM93U1 (mkBoundsS1 uMMM93U1 denM93U1 b1M93U1) 54 4 = true := by decide

set_option maxRecDepth 20000 in
theorem m93_u1_r2_p36b :
    verifyRangeR2 b1M93U1 b2M93U1 exemptM93U1 (mkBoundsS1 uMMM93U1 denM93U1 b1M93U1) 58 20 = true := by decide

theorem m93_u1_r2_p36 :
    verifyRangeR2 b1M93U1 b2M93U1 exemptM93U1 (mkBoundsS1 uMMM93U1 denM93U1 b1M93U1) 54 24 = true :=
  verifyRangeR2_append 54 4 20 m93_u1_r2_p36a m93_u1_r2_p36b

end CollatzFormal
