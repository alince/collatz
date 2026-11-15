/-
  CollatzFormal/HenselBridge96_03.lean — R2 bands chunk 3 for (96, 4).
-/

import CollatzFormal.HenselBridgeCore

namespace CollatzFormal

set_option exponentiation.threshold 2048

set_option maxRecDepth 20000 in
theorem m96_u4_r2_p10 :
    verifyRangeR2 b1M96U4 b2M96U4 exemptM96U4 (mkBoundsS1 uMMM96U4 denM96U4 b1M96U4) 30 1 = true := by decide

set_option maxRecDepth 20000 in
theorem m96_u4_r2_p11 :
    verifyRangeR2 b1M96U4 b2M96U4 exemptM96U4 (mkBoundsS1 uMMM96U4 denM96U4 b1M96U4) 31 1 = true := by decide

set_option maxRecDepth 20000 in
theorem m96_u4_r2_p12 :
    verifyRangeR2 b1M96U4 b2M96U4 exemptM96U4 (mkBoundsS1 uMMM96U4 denM96U4 b1M96U4) 32 1 = true := by decide

set_option maxRecDepth 20000 in
theorem m96_u4_r2_p13 :
    verifyRangeR2 b1M96U4 b2M96U4 exemptM96U4 (mkBoundsS1 uMMM96U4 denM96U4 b1M96U4) 33 1 = true := by decide

end CollatzFormal
