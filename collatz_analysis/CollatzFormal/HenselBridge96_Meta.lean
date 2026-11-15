/-
  CollatzFormal/HenselBridge96_Meta.lean — Slab & R1 certs for (96, 4).
-/

import CollatzFormal.HenselBridgeCore

namespace CollatzFormal

set_option exponentiation.threshold 2048

set_option maxRecDepth 20000 in
theorem m96_u4_counts_ok :
    checkSlabEliminated 112 84 256 96 (4 * q43Val) barinaXMin (2 * 2 ^ 256) [2 ^ 71, 2 ^ 71, b1M96U4, b2M96U4, b3M96U4, 2 ^ 256] = true := by decide

set_option maxRecDepth 20000 in
theorem m96_u4_s0_ok :
    checkSlabEliminated 112 84 256 96 (4 * q43Val) (b1M96U4 + 1)
      (evalPow2Pow3Aux 256 (4 * p43Val) (4 * q43Val) 96).1 bsS0M96U4 = true := by decide

set_option maxRecDepth 20000 in
theorem m96_u4_aux_ok :
    checkSubcaseAux 2 96 4 78 b1M96U4 b2M96U4 b3M96U4 uMMM96U4 denM96U4 = true := by decide

set_option maxRecDepth 20000 in
theorem m96_u4_r1_ok :
    verifyRangeR1 b1M96U4 b2M96U4 exemptM96U4 (mkBoundsU uMMM96U4 b1M96U4) 1 77 = true := by decide

end CollatzFormal
