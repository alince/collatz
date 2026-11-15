/-
  CollatzFormal/HenselBridge96_02.lean — R2 bands chunk 2 for (96, 4).
-/

import CollatzFormal.HenselBridgeCore

namespace CollatzFormal

set_option exponentiation.threshold 2048

set_option maxRecDepth 20000 in
theorem m96_u4_r2_p6 :
    verifyRangeR2 b1M96U4 b2M96U4 exemptM96U4 (mkBoundsS1 uMMM96U4 denM96U4 b1M96U4) 26 1 = true := by decide

set_option maxRecDepth 20000 in
theorem m96_u4_r2_p7 :
    verifyRangeR2 b1M96U4 b2M96U4 exemptM96U4 (mkBoundsS1 uMMM96U4 denM96U4 b1M96U4) 27 1 = true := by decide

set_option maxRecDepth 20000 in
theorem m96_u4_r2_p8 :
    verifyRangeR2 b1M96U4 b2M96U4 exemptM96U4 (mkBoundsS1 uMMM96U4 denM96U4 b1M96U4) 28 1 = true := by decide

set_option maxRecDepth 20000 in
theorem m96_u4_r2_p9 :
    verifyRangeR2 b1M96U4 b2M96U4 exemptM96U4 (mkBoundsS1 uMMM96U4 denM96U4 b1M96U4) 29 1 = true := by decide

end CollatzFormal
