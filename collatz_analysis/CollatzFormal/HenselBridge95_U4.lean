/-
  CollatzFormal/HenselBridge95_U4.lean — Kernel elimination of (95, 4).
-/

import CollatzFormal.HenselBridgeCore

namespace CollatzFormal

set_option exponentiation.threshold 2048

set_option maxRecDepth 20000 in
theorem m95_u4_counts_ok :
    checkSlabEliminated 112 84 256 95 (4 * q43Val) barinaXMin (2 * 2 ^ 256) [2 ^ 71, b1M95U4, b2M95U4, b3M95U4, 2 ^ 256] = true := by decide

set_option maxRecDepth 20000 in
theorem m95_u4_s0_ok :
    checkSlabEliminated 112 84 256 95 (4 * q43Val) (b1M95U4 + 1)
      (evalPow2Pow3Aux 256 (4 * p43Val) (4 * q43Val) 96).1 bsS0M95U4 = true := by decide

set_option maxRecDepth 20000 in
theorem m95_u4_aux_ok :
    checkSubcaseAux 1 95 4 78 b1M95U4 b2M95U4 b3M95U4 uMMM95U4 denM95U4 = true := by decide

set_option maxRecDepth 20000 in
theorem m95_u4_r1_ok :
    verifyRangeR1 b1M95U4 b2M95U4 exemptM95U4 (mkBoundsS1 uMMM95U4 denM95U4 b1M95U4) 1 77 = true := by decide

theorem no_spiral_cycle_m95_u4 {steps : List SpiralStepData}
    (hbar : BarinaThreshold (2 ^ 71))
    (hcyc : IsNontrivialSpiralCycle steps)
    (hm_eq : steps.length = 95)
    (hK_eq : spiralChainTotalK steps = 4 * p43Val)
    (hW_eq : spiralChainTotalW steps = 4 * q43Val) : False :=
  no_spiral_cycle_c1_core hbar hcyc hm_eq (by omega) hK_eq hW_eq (by decide) (by decide)
    m95_u4_counts_ok m95_u4_s0_ok m95_u4_aux_ok m95_u4_r1_ok (by decide)

end CollatzFormal
