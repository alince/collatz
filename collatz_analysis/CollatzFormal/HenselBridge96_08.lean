/-
  CollatzFormal/HenselBridge96_08.lean — R2 bands chunk 8 for (96, 4).
-/

import CollatzFormal.HenselBridgeCore

namespace CollatzFormal

set_option exponentiation.threshold 2048

set_option maxRecDepth 20000 in
theorem m96_u4_r2_p23a :
    verifyRangeR2 b1M96U4 b2M96U4 exemptM96U4 (mkBoundsS1 uMMM96U4 denM96U4 b1M96U4) 56 6 = true := by decide

set_option maxRecDepth 20000 in
theorem m96_u4_r2_p23b :
    verifyRangeR2 b1M96U4 b2M96U4 exemptM96U4 (mkBoundsS1 uMMM96U4 denM96U4 b1M96U4) 62 16 = true := by decide

theorem m96_u4_r2_p23 :
    verifyRangeR2 b1M96U4 b2M96U4 exemptM96U4 (mkBoundsS1 uMMM96U4 denM96U4 b1M96U4) 56 22 = true :=
  verifyRangeR2_append 56 6 16 m96_u4_r2_p23a m96_u4_r2_p23b

end CollatzFormal
