/-
  CollatzFormal/HenselBridge96_U5.lean — Kernel elimination of (96, 5).
-/

import CollatzFormal.HenselBridgeCore

namespace CollatzFormal

set_option exponentiation.threshold 2048

set_option maxRecDepth 20000 in
theorem m96_u5_counts_ok :
    checkSlabEliminated 112 84 256 96 (5 * q43Val) barinaXMin (2 * 2 ^ 256) [2 ^ 71, 2 ^ 71, b1M96U5, b2M96U5, b3M96U5, 2 ^ 256] = true := by decide

set_option maxRecDepth 20000 in
theorem m96_u5_s0_ok :
    checkSlabEliminated 112 84 256 96 (5 * q43Val) (b1M96U5 + 1)
      (evalPow2Pow3Aux 256 (5 * p43Val) (5 * q43Val) 96).1 bsS0M96U5 = true := by decide

set_option maxRecDepth 20000 in
theorem m96_u5_aux_ok :
    checkSubcaseAux 2 96 5 97 b1M96U5 b2M96U5 b3M96U5 uMMM96U5 denM96U5 = true := by decide

set_option maxRecDepth 20000 in
theorem m96_u5_r1_ok :
    verifyRangeR1 b1M96U5 b2M96U5 exemptM96U5 (mkBoundsU uMMM96U5 b1M96U5) 1 96 = true := by decide

set_option maxRecDepth 20000 in
theorem m96_u5_r2_p0 :
    verifyRangeR2 b1M96U5 b2M96U5 exemptM96U5 (mkBoundsS1 uMMM96U5 denM96U5 b1M96U5) 1 35 = true := by decide

set_option maxRecDepth 20000 in
theorem m96_u5_r2_p1 :
    verifyRangeR2 b1M96U5 b2M96U5 exemptM96U5 (mkBoundsS1 uMMM96U5 denM96U5 b1M96U5) 36 30 = true := by decide

set_option maxRecDepth 20000 in
theorem m96_u5_r2_p2 :
    verifyRangeR2 b1M96U5 b2M96U5 exemptM96U5 (mkBoundsS1 uMMM96U5 denM96U5 b1M96U5) 66 31 = true := by decide

theorem m96_u5_r2_ok :
    verifyRangeR2 b1M96U5 b2M96U5 exemptM96U5 (mkBoundsS1 uMMM96U5 denM96U5 b1M96U5) 1 96 = true := by
  have h01 := verifyRangeR2_append 1 35 30 m96_u5_r2_p0 m96_u5_r2_p1
  exact verifyRangeR2_append 1 65 31 h01 m96_u5_r2_p2

theorem no_spiral_cycle_m96_u5 {steps : List SpiralStepData}
    (hbar : BarinaThreshold (2 ^ 71))
    (hcyc : IsNontrivialSpiralCycle steps)
    (hm_eq : steps.length = 96)
    (hK_eq : spiralChainTotalK steps = 5 * p43Val)
    (hW_eq : spiralChainTotalW steps = 5 * q43Val) : False :=
  no_spiral_cycle_c2_core hbar hcyc hm_eq (by omega) hK_eq hW_eq (by decide) (by decide)
    m96_u5_counts_ok m96_u5_s0_ok m96_u5_aux_ok m96_u5_r1_ok m96_u5_r2_ok (by decide)

end CollatzFormal
