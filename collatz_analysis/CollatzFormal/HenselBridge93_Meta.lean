/-
  CollatzFormal/HenselBridge93_Meta.lean — Slab & R1 certs for (93, 1).
-/

import CollatzFormal.HenselBridgeCore

namespace CollatzFormal

set_option exponentiation.threshold 2048

set_option maxRecDepth 20000 in
theorem m93_u1_counts_ok :
    checkSlabEliminated 112 84 256 93 (1 * q43Val) barinaXMin (2 * 2 ^ 256) [2 ^ 71, 2 ^ 71, b1M93U1, b2M93U1, b3M93U1, 2 ^ 256] = true := by decide

set_option maxRecDepth 20000 in
theorem m93_u1_s0_ok :
    checkSlabEliminated 112 84 256 93 (1 * q43Val) (b1M93U1 + 1)
      (evalPow2Pow3Aux 256 (1 * p43Val) (1 * q43Val) 96).1 bsS0M93U1 = true := by decide

set_option maxRecDepth 20000 in
theorem m93_u1_aux_ok :
    checkSubcaseAux 2 93 1 78 b1M93U1 b2M93U1 b3M93U1 uMMM93U1 denM93U1 = true := by decide

set_option maxRecDepth 20000 in
theorem m93_u1_r1_ok :
    verifyRangeR1 b1M93U1 b2M93U1 exemptM93U1 (mkBoundsU uMMM93U1 b1M93U1) 1 77 = true := by decide

end CollatzFormal
