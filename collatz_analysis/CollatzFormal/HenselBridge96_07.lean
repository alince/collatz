/-
  CollatzFormal/HenselBridge96_07.lean — R2 bands chunk 7 for (96, 4).
-/

import CollatzFormal.HenselBridgeCore

namespace CollatzFormal

set_option exponentiation.threshold 2048

set_option maxRecDepth 20000 in
theorem m96_u4_r2_p22a :
    verifyRangeR2 b1M96U4 b2M96U4 exemptM96U4 (mkBoundsS1 uMMM96U4 denM96U4 b1M96U4) 47 4 = true := by decide

set_option maxRecDepth 20000 in
theorem m96_u4_r2_p22b :
    verifyRangeR2 b1M96U4 b2M96U4 exemptM96U4 (mkBoundsS1 uMMM96U4 denM96U4 b1M96U4) 51 5 = true := by decide

theorem m96_u4_r2_p22 :
    verifyRangeR2 b1M96U4 b2M96U4 exemptM96U4 (mkBoundsS1 uMMM96U4 denM96U4 b1M96U4) 47 9 = true :=
  verifyRangeR2_append 47 4 5 m96_u4_r2_p22a m96_u4_r2_p22b

end CollatzFormal
