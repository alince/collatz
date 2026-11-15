/-
  CollatzFormal/HenselBridge93_U2.lean — Kernel elimination of (93, 2).
-/

import CollatzFormal.HenselBridgeCore

namespace CollatzFormal

set_option exponentiation.threshold 2048

set_option maxRecDepth 20000 in
theorem m93_u2_counts_ok :
    checkSlabEliminated 112 84 256 93 (2 * q43Val) barinaXMin (2 * 2 ^ 256) [2 ^ 71, b1M93U2, b2M93U2, b3M93U2, 2 ^ 256] = true := by decide

set_option maxRecDepth 20000 in
theorem m93_u2_s0_ok :
    checkSlabEliminated 112 84 256 93 (2 * q43Val) (b1M93U2 + 1)
      (evalPow2Pow3Aux 256 (2 * p43Val) (2 * q43Val) 96).1 bsS0M93U2 = true := by decide

set_option maxRecDepth 20000 in
theorem m93_u2_aux_ok :
    checkSubcaseAux 1 93 2 98 b1M93U2 b2M93U2 b3M93U2 uMMM93U2 denM93U2 = true := by decide

set_option maxRecDepth 20000 in
theorem m93_u2_r1_ok :
    verifyRangeR1 b1M93U2 b2M93U2 exemptM93U2 (mkBoundsS1 uMMM93U2 denM93U2 b1M93U2) 1 97 = true := by decide

theorem no_spiral_cycle_m93_u2 {steps : List SpiralStepData}
    (hbar : BarinaThreshold (2 ^ 71))
    (hcyc : IsNontrivialSpiralCycle steps)
    (hm_eq : steps.length = 93)
    (hK_eq : spiralChainTotalK steps = 2 * p43Val)
    (hW_eq : spiralChainTotalW steps = 2 * q43Val) : False :=
  no_spiral_cycle_c1_core hbar hcyc hm_eq (by omega) hK_eq hW_eq (by decide) (by decide)
    m93_u2_counts_ok m93_u2_s0_ok m93_u2_aux_ok m93_u2_r1_ok (by decide)

end CollatzFormal
