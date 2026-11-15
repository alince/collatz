/-
  CollatzFormal/HenselBridge96_04.lean — R2 bands chunk 4 for (96, 4).
-/

import CollatzFormal.HenselBridgeCore

namespace CollatzFormal

set_option exponentiation.threshold 2048

set_option maxRecDepth 20000 in
theorem m96_u4_r2_p14 :
    verifyRangeR2 b1M96U4 b2M96U4 exemptM96U4 (mkBoundsS1 uMMM96U4 denM96U4 b1M96U4) 34 1 = true := by decide

set_option maxRecDepth 20000 in
theorem m96_u4_r2_p15 :
    verifyRangeR2 b1M96U4 b2M96U4 exemptM96U4 (mkBoundsS1 uMMM96U4 denM96U4 b1M96U4) 35 1 = true := by decide

set_option maxRecDepth 20000 in
theorem m96_u4_r2_p16 :
    verifyRangeR2 b1M96U4 b2M96U4 exemptM96U4 (mkBoundsS1 uMMM96U4 denM96U4 b1M96U4) 36 1 = true := by decide

set_option maxRecDepth 20000 in
theorem m96_u4_r2_p17 :
    verifyRangeR2 b1M96U4 b2M96U4 exemptM96U4 (mkBoundsS1 uMMM96U4 denM96U4 b1M96U4) 37 1 = true := by decide

end CollatzFormal
