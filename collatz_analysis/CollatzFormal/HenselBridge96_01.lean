/-
  CollatzFormal/HenselBridge96_01.lean — R2 bands chunk 1 for (96, 4).
-/

import CollatzFormal.HenselBridgeCore

namespace CollatzFormal

set_option exponentiation.threshold 2048

set_option maxRecDepth 20000 in
theorem m96_u4_r2_p3 :
    verifyRangeR2 b1M96U4 b2M96U4 exemptM96U4 (mkBoundsS1 uMMM96U4 denM96U4 b1M96U4) 22 2 = true := by decide

set_option maxRecDepth 20000 in
theorem m96_u4_r2_p4 :
    verifyRangeR2 b1M96U4 b2M96U4 exemptM96U4 (mkBoundsS1 uMMM96U4 denM96U4 b1M96U4) 24 1 = true := by decide

set_option maxRecDepth 20000 in
theorem m96_u4_r2_p5 :
    verifyRangeR2 b1M96U4 b2M96U4 exemptM96U4 (mkBoundsS1 uMMM96U4 denM96U4 b1M96U4) 25 1 = true := by decide

end CollatzFormal
