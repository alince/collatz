/-
  CollatzFormal/HenselBridge96_00.lean — R2 bands chunk 0 for (96, 4).
-/

import CollatzFormal.HenselBridgeCore

namespace CollatzFormal

set_option exponentiation.threshold 2048

set_option maxRecDepth 20000 in
theorem m96_u4_r2_p0 :
    verifyRangeR2 b1M96U4 b2M96U4 exemptM96U4 (mkBoundsS1 uMMM96U4 denM96U4 b1M96U4) 1 17 = true := by decide

set_option maxRecDepth 20000 in
theorem m96_u4_r2_p1 :
    verifyRangeR2 b1M96U4 b2M96U4 exemptM96U4 (mkBoundsS1 uMMM96U4 denM96U4 b1M96U4) 18 2 = true := by decide

set_option maxRecDepth 20000 in
theorem m96_u4_r2_p2 :
    verifyRangeR2 b1M96U4 b2M96U4 exemptM96U4 (mkBoundsS1 uMMM96U4 denM96U4 b1M96U4) 20 2 = true := by decide

end CollatzFormal
