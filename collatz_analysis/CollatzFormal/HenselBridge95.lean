/-
  CollatzFormal/HenselBridge95.lean — Kernel elimination of (95, 3).
-/

import CollatzFormal.HenselBridgeCore

namespace CollatzFormal

set_option exponentiation.threshold 2048

set_option maxRecDepth 20000 in
theorem m95_u3_counts_ok :
    checkSlabEliminated 112 84 256 95 (3 * q43Val) barinaXMin (2 * 2 ^ 256) [2 ^ 71, 2 ^ 71, b1M95U3, b2M95U3, b3M95U3, 2 ^ 256] = true := by decide

set_option maxRecDepth 20000 in
theorem m95_u3_s0_ok :
    checkSlabEliminated 112 84 256 95 (3 * q43Val) (b1M95U3 + 1)
      (evalPow2Pow3Aux 256 (3 * p43Val) (3 * q43Val) 96).1 bsS0M95U3 = true := by decide

set_option maxRecDepth 20000 in
theorem m95_u3_aux_ok :
    checkSubcaseAux 2 95 3 92 b1M95U3 b2M95U3 b3M95U3 uMMM95U3 denM95U3 = true := by decide

set_option maxRecDepth 20000 in
theorem m95_u3_r1_ok :
    verifyRangeR1 b1M95U3 b2M95U3 exemptM95U3 (mkBoundsU uMMM95U3 b1M95U3) 1 91 = true := by decide

set_option maxRecDepth 20000 in
theorem m95_u3_r2_p0 :
    verifyRangeR2 b1M95U3 b2M95U3 exemptM95U3 (mkBoundsS1 uMMM95U3 denM95U3 b1M95U3) 1 35 = true := by decide

set_option maxRecDepth 20000 in
theorem m95_u3_r2_p1 :
    verifyRangeR2 b1M95U3 b2M95U3 exemptM95U3 (mkBoundsS1 uMMM95U3 denM95U3 b1M95U3) 36 25 = true := by decide

set_option maxRecDepth 20000 in
theorem m95_u3_r2_p2 :
    verifyRangeR2 b1M95U3 b2M95U3 exemptM95U3 (mkBoundsS1 uMMM95U3 denM95U3 b1M95U3) 61 31 = true := by decide

theorem m95_u3_r2_ok :
    verifyRangeR2 b1M95U3 b2M95U3 exemptM95U3 (mkBoundsS1 uMMM95U3 denM95U3 b1M95U3) 1 91 = true := by
  have h01 := verifyRangeR2_append 1 35 25 m95_u3_r2_p0 m95_u3_r2_p1
  exact verifyRangeR2_append 1 60 31 h01 m95_u3_r2_p2

theorem no_spiral_cycle_m95_u3 {steps : List SpiralStepData}
    (hbar : BarinaThreshold (2 ^ 71))
    (hcyc : IsNontrivialSpiralCycle steps)
    (hm_eq : steps.length = 95)
    (hK_eq : spiralChainTotalK steps = 3 * p43Val)
    (hW_eq : spiralChainTotalW steps = 3 * q43Val) : False :=
  no_spiral_cycle_c2_core hbar hcyc hm_eq (by omega) hK_eq hW_eq (by decide) (by decide)
    m95_u3_counts_ok m95_u3_s0_ok m95_u3_aux_ok m95_u3_r1_ok m95_u3_r2_ok (by decide)

end CollatzFormal
