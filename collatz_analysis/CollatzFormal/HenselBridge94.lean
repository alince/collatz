/-
  CollatzFormal/HenselBridge94.lean — Kernel elimination of (94, 3) & (94, 2).
-/

import CollatzFormal.HenselBridgeCore

namespace CollatzFormal

set_option exponentiation.threshold 2048

set_option maxRecDepth 20000 in
theorem m94_u3_counts_ok :
    checkSlabEliminated 112 84 256 94 (3 * q43Val) barinaXMin (2 * 2 ^ 256) [2 ^ 71, b1M94U3, b2M94U3, b3M94U3, 2 ^ 256] = true := by decide

set_option maxRecDepth 20000 in
theorem m94_u3_s0_ok :
    checkSlabEliminated 112 84 256 94 (3 * q43Val) (b1M94U3 + 1)
      (evalPow2Pow3Aux 256 (3 * p43Val) (3 * q43Val) 96).1 bsS0M94U3 = true := by decide

set_option maxRecDepth 20000 in
theorem m94_u3_aux_ok :
    checkSubcaseAux 1 94 3 92 b1M94U3 b2M94U3 b3M94U3 uMMM94U3 denM94U3 = true := by decide

set_option maxRecDepth 20000 in
theorem m94_u3_r1_ok :
    verifyRangeR1 b1M94U3 b2M94U3 exemptM94U3 (mkBoundsS1 uMMM94U3 denM94U3 b1M94U3) 1 91 = true := by decide

theorem no_spiral_cycle_m94_u3 {steps : List SpiralStepData}
    (hbar : BarinaThreshold (2 ^ 71))
    (hcyc : IsNontrivialSpiralCycle steps)
    (hm_eq : steps.length = 94)
    (hK_eq : spiralChainTotalK steps = 3 * p43Val)
    (hW_eq : spiralChainTotalW steps = 3 * q43Val) : False :=
  no_spiral_cycle_c1_core hbar hcyc hm_eq (by omega) hK_eq hW_eq (by decide) (by decide)
    m94_u3_counts_ok m94_u3_s0_ok m94_u3_aux_ok m94_u3_r1_ok (by decide)

set_option maxRecDepth 20000 in
theorem m94_u2_counts_ok :
    checkSlabEliminated 112 84 256 94 (2 * q43Val) barinaXMin (2 * 2 ^ 256) [2 ^ 71, 2 ^ 71, b1M94U2, b2M94U2, b3M94U2, 2 ^ 256] = true := by decide

set_option maxRecDepth 20000 in
theorem m94_u2_s0_ok :
    checkSlabEliminated 112 84 256 94 (2 * q43Val) (b1M94U2 + 1)
      (evalPow2Pow3Aux 256 (2 * p43Val) (2 * q43Val) 96).1 bsS0M94U2 = true := by decide

set_option maxRecDepth 20000 in
theorem m94_u2_aux_ok :
    checkSubcaseAux 2 94 2 98 b1M94U2 b2M94U2 b3M94U2 uMMM94U2 denM94U2 = true := by decide

set_option maxRecDepth 20000 in
theorem m94_u2_r1_ok :
    verifyRangeR1 b1M94U2 b2M94U2 exemptM94U2 (mkBoundsU uMMM94U2 b1M94U2) 1 97 = true := by decide

set_option maxRecDepth 20000 in
theorem m94_u2_r2_ok :
    verifyRangeR2 b1M94U2 b2M94U2 exemptM94U2 (mkBoundsS1 uMMM94U2 denM94U2 b1M94U2) 1 97 = true := by decide

theorem no_spiral_cycle_m94_u2 {steps : List SpiralStepData}
    (hbar : BarinaThreshold (2 ^ 71))
    (hcyc : IsNontrivialSpiralCycle steps)
    (hm_eq : steps.length = 94)
    (hK_eq : spiralChainTotalK steps = 2 * p43Val)
    (hW_eq : spiralChainTotalW steps = 2 * q43Val) : False :=
  no_spiral_cycle_c2_core hbar hcyc hm_eq (by omega) hK_eq hW_eq (by decide) (by decide)
    m94_u2_counts_ok m94_u2_s0_ok m94_u2_aux_ok m94_u2_r1_ok m94_u2_r2_ok (by decide)

end CollatzFormal
