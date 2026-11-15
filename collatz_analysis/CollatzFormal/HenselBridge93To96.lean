/-
  CollatzFormal/HenselBridge93To96.lean — Master Zero-Trust-Gap Kernel Eliminations for m = 93..96.
-/

import CollatzFormal.HenselBridgeCore
import CollatzFormal.HenselBridge93_U2
import CollatzFormal.HenselBridge94
import CollatzFormal.HenselBridge95_U4
import CollatzFormal.HenselBridge95
import CollatzFormal.HenselBridge96_U5
import CollatzFormal.HenselBridge93_Meta
import CollatzFormal.HenselBridge93_00
import CollatzFormal.HenselBridge93_01
import CollatzFormal.HenselBridge93_02
import CollatzFormal.HenselBridge93_03
import CollatzFormal.HenselBridge93_04
import CollatzFormal.HenselBridge93_05
import CollatzFormal.HenselBridge93_06
import CollatzFormal.HenselBridge93_07
import CollatzFormal.HenselBridge93_08
import CollatzFormal.HenselBridge93_09
import CollatzFormal.HenselBridge93_10
import CollatzFormal.HenselBridge93_11
import CollatzFormal.HenselBridge93_12
import CollatzFormal.HenselBridge93_13
import CollatzFormal.HenselBridge93_14
import CollatzFormal.HenselBridge93_15
import CollatzFormal.HenselBridge96_Meta
import CollatzFormal.HenselBridge96_00
import CollatzFormal.HenselBridge96_01
import CollatzFormal.HenselBridge96_02
import CollatzFormal.HenselBridge96_03
import CollatzFormal.HenselBridge96_04
import CollatzFormal.HenselBridge96_05
import CollatzFormal.HenselBridge96_06
import CollatzFormal.HenselBridge96_07
import CollatzFormal.HenselBridge96_08

namespace CollatzFormal

set_option exponentiation.threshold 2048

theorem m93_u1_r2_ok :
    verifyRangeR2 b1M93U1 b2M93U1 exemptM93U1 (mkBoundsS1 uMMM93U1 denM93U1 b1M93U1) 1 77 = true := by
  have hacc := m93_u1_r2_p0
  have hacc := verifyRangeR2_append 1 12 2 hacc m93_u1_r2_p1
  have hacc := verifyRangeR2_append 1 14 1 hacc m93_u1_r2_p2
  have hacc := verifyRangeR2_append 1 15 1 hacc m93_u1_r2_p3
  have hacc := verifyRangeR2_append 1 16 1 hacc m93_u1_r2_p4
  have hacc := verifyRangeR2_append 1 17 1 hacc m93_u1_r2_p5
  have hacc := verifyRangeR2_append 1 18 1 hacc m93_u1_r2_p6
  have hacc := verifyRangeR2_append 1 19 1 hacc m93_u1_r2_p7
  have hacc := verifyRangeR2_append 1 20 1 hacc m93_u1_r2_p8
  have hacc := verifyRangeR2_append 1 21 1 hacc m93_u1_r2_p9
  have hacc := verifyRangeR2_append 1 22 1 hacc m93_u1_r2_p10
  have hacc := verifyRangeR2_append 1 23 1 hacc m93_u1_r2_p11
  have hacc := verifyRangeR2_append 1 24 1 hacc m93_u1_r2_p12
  have hacc := verifyRangeR2_append 1 25 1 hacc m93_u1_r2_p13
  have hacc := verifyRangeR2_append 1 26 1 hacc m93_u1_r2_p14
  have hacc := verifyRangeR2_append 1 27 1 hacc m93_u1_r2_p15
  have hacc := verifyRangeR2_append 1 28 1 hacc m93_u1_r2_p16
  have hacc := verifyRangeR2_append 1 29 1 hacc m93_u1_r2_p17
  have hacc := verifyRangeR2_append 1 30 1 hacc m93_u1_r2_p18
  have hacc := verifyRangeR2_append 1 31 1 hacc m93_u1_r2_p19
  have hacc := verifyRangeR2_append 1 32 1 hacc m93_u1_r2_p20
  have hacc := verifyRangeR2_append 1 33 1 hacc m93_u1_r2_p21
  have hacc := verifyRangeR2_append 1 34 1 hacc m93_u1_r2_p22
  have hacc := verifyRangeR2_append 1 35 1 hacc m93_u1_r2_p23
  have hacc := verifyRangeR2_append 1 36 1 hacc m93_u1_r2_p24
  have hacc := verifyRangeR2_append 1 37 1 hacc m93_u1_r2_p25
  have hacc := verifyRangeR2_append 1 38 1 hacc m93_u1_r2_p26
  have hacc := verifyRangeR2_append 1 39 1 hacc m93_u1_r2_p27
  have hacc := verifyRangeR2_append 1 40 1 hacc m93_u1_r2_p28
  have hacc := verifyRangeR2_append 1 41 1 hacc m93_u1_r2_p29
  have hacc := verifyRangeR2_append 1 42 1 hacc m93_u1_r2_p30
  have hacc := verifyRangeR2_append 1 43 1 hacc m93_u1_r2_p31
  have hacc := verifyRangeR2_append 1 44 1 hacc m93_u1_r2_p32
  have hacc := verifyRangeR2_append 1 45 2 hacc m93_u1_r2_p33
  have hacc := verifyRangeR2_append 1 47 2 hacc m93_u1_r2_p34
  have hacc := verifyRangeR2_append 1 49 4 hacc m93_u1_r2_p35
  have hacc := verifyRangeR2_append 1 53 24 hacc m93_u1_r2_p36
  exact hacc

theorem no_spiral_cycle_m93_u1 {steps : List SpiralStepData}
    (hbar : BarinaThreshold (2 ^ 71))
    (hcyc : IsNontrivialSpiralCycle steps)
    (hm_eq : steps.length = 93)
    (hK_eq : spiralChainTotalK steps = 1 * p43Val)
    (hW_eq : spiralChainTotalW steps = 1 * q43Val) : False :=
  no_spiral_cycle_c2_core hbar hcyc hm_eq (by omega) hK_eq hW_eq (by decide) (by decide)
    m93_u1_counts_ok m93_u1_s0_ok m93_u1_aux_ok m93_u1_r1_ok m93_u1_r2_ok (by decide)

theorem m96_u4_r2_ok :
    verifyRangeR2 b1M96U4 b2M96U4 exemptM96U4 (mkBoundsS1 uMMM96U4 denM96U4 b1M96U4) 1 77 = true := by
  have hacc := m96_u4_r2_p0
  have hacc := verifyRangeR2_append 1 17 2 hacc m96_u4_r2_p1
  have hacc := verifyRangeR2_append 1 19 2 hacc m96_u4_r2_p2
  have hacc := verifyRangeR2_append 1 21 2 hacc m96_u4_r2_p3
  have hacc := verifyRangeR2_append 1 23 1 hacc m96_u4_r2_p4
  have hacc := verifyRangeR2_append 1 24 1 hacc m96_u4_r2_p5
  have hacc := verifyRangeR2_append 1 25 1 hacc m96_u4_r2_p6
  have hacc := verifyRangeR2_append 1 26 1 hacc m96_u4_r2_p7
  have hacc := verifyRangeR2_append 1 27 1 hacc m96_u4_r2_p8
  have hacc := verifyRangeR2_append 1 28 1 hacc m96_u4_r2_p9
  have hacc := verifyRangeR2_append 1 29 1 hacc m96_u4_r2_p10
  have hacc := verifyRangeR2_append 1 30 1 hacc m96_u4_r2_p11
  have hacc := verifyRangeR2_append 1 31 1 hacc m96_u4_r2_p12
  have hacc := verifyRangeR2_append 1 32 1 hacc m96_u4_r2_p13
  have hacc := verifyRangeR2_append 1 33 1 hacc m96_u4_r2_p14
  have hacc := verifyRangeR2_append 1 34 1 hacc m96_u4_r2_p15
  have hacc := verifyRangeR2_append 1 35 1 hacc m96_u4_r2_p16
  have hacc := verifyRangeR2_append 1 36 1 hacc m96_u4_r2_p17
  have hacc := verifyRangeR2_append 1 37 2 hacc m96_u4_r2_p18
  have hacc := verifyRangeR2_append 1 39 2 hacc m96_u4_r2_p19
  have hacc := verifyRangeR2_append 1 41 2 hacc m96_u4_r2_p20
  have hacc := verifyRangeR2_append 1 43 3 hacc m96_u4_r2_p21
  have hacc := verifyRangeR2_append 1 46 9 hacc m96_u4_r2_p22
  have hacc := verifyRangeR2_append 1 55 22 hacc m96_u4_r2_p23
  exact hacc

theorem no_spiral_cycle_m96_u4 {steps : List SpiralStepData}
    (hbar : BarinaThreshold (2 ^ 71))
    (hcyc : IsNontrivialSpiralCycle steps)
    (hm_eq : steps.length = 96)
    (hK_eq : spiralChainTotalK steps = 4 * p43Val)
    (hW_eq : spiralChainTotalW steps = 4 * q43Val) : False :=
  no_spiral_cycle_c2_core hbar hcyc hm_eq (by omega) hK_eq hW_eq (by decide) (by decide)
    m96_u4_counts_ok m96_u4_s0_ok m96_u4_aux_ok m96_u4_r1_ok m96_u4_r2_ok (by decide)

/--
  Master Theorem 26B (Zero-Trust-Gap End-to-End Cycle Elimination Through `1 <= m <= 93`):
  Assuming ONLY `BarinaThreshold (2^71)` and `BakerLMNPowerBound`, NO non-trivial positive
  spiral cycle of block count `1 <= m <= 93` exists — verified 100% inside the Lean 4 kernel!
-/
theorem no_nontrivial_spiral_cycles_1_to_93
    {steps : List SpiralStepData}
    (hbar : BarinaThreshold (2 ^ 71))
    (hbaker : BakerLMNPowerBound)
    (hcyc : IsNontrivialSpiralCycle steps)
    (hm_le : steps.length ≤ 93) :
    False := by
  by_cases hm92 : steps.length ≤ 92
  · exact no_nontrivial_spiral_cycles_1_to_92 hbar hbaker hcyc hm92
  · have hm93 : steps.length = 93 := by omega
    rcases q43_confinement_le_96 hbar hbaker hcyc (by omega) with ⟨u, _hu1, hK, hW⟩
    by_cases hu_eq1 : u = 1
    · subst hu_eq1; exact no_spiral_cycle_m93_u1 hbar hcyc hm93 hK hW
    · by_cases hu_eq2 : u = 2
      · subst hu_eq2; exact no_spiral_cycle_m93_u2 hbar hcyc hm93 hK hW
      · exact eliminate_q43_multiple_tail hbar hcyc (by omega) (by decide) (by decide)
          slab_utail_m93_u3_ok (by omega) hK hW

/-- Zero-trust-gap kernel elimination of all `u >= 2` (`W >= 2 * q43`) cycles at `m = 94`. -/
theorem no_nontrivial_spiral_cycles_m94_u_ge_2
    {steps : List SpiralStepData} {u : Nat}
    (hbar : BarinaThreshold (2 ^ 71))
    (hcyc : IsNontrivialSpiralCycle steps)
    (hm_eq : steps.length = 94)
    (hu_ge2 : u ≥ 2)
    (hK : spiralChainTotalK steps = u * p43Val)
    (hW : spiralChainTotalW steps = u * q43Val) :
    False := by
  by_cases hu2 : u = 2
  · subst hu2; exact no_spiral_cycle_m94_u2 hbar hcyc hm_eq hK hW
  · by_cases hu3 : u = 3
    · subst hu3; exact no_spiral_cycle_m94_u3 hbar hcyc hm_eq hK hW
    · exact eliminate_q43_multiple_tail hbar hcyc (by omega) (by decide) (by decide)
        slab_utail_m94_u4_ok (by omega) hK hW

/-- Zero-trust-gap kernel elimination of all `u >= 3` (`W >= 3 * q43`) cycles at `m = 95`. -/
theorem no_nontrivial_spiral_cycles_m95_u_ge_3
    {steps : List SpiralStepData} {u : Nat}
    (hbar : BarinaThreshold (2 ^ 71))
    (hcyc : IsNontrivialSpiralCycle steps)
    (hm_eq : steps.length = 95)
    (hu_ge3 : u ≥ 3)
    (hK : spiralChainTotalK steps = u * p43Val)
    (hW : spiralChainTotalW steps = u * q43Val) :
    False := by
  by_cases hu3 : u = 3
  · subst hu3; exact no_spiral_cycle_m95_u3 hbar hcyc hm_eq hK hW
  · by_cases hu4 : u = 4
    · subst hu4; exact no_spiral_cycle_m95_u4 hbar hcyc hm_eq hK hW
    · exact eliminate_q43_multiple_tail hbar hcyc (by omega) (by decide) (by decide)
        slab_utail_m95_u5_ok (by omega) hK hW

/-- Zero-trust-gap kernel elimination of all `u >= 4` (`W >= 4 * q43`) cycles at `m = 96`. -/
theorem no_nontrivial_spiral_cycles_m96_u_ge_4
    {steps : List SpiralStepData} {u : Nat}
    (hbar : BarinaThreshold (2 ^ 71))
    (hcyc : IsNontrivialSpiralCycle steps)
    (hm_eq : steps.length = 96)
    (hu_ge4 : u ≥ 4)
    (hK : spiralChainTotalK steps = u * p43Val)
    (hW : spiralChainTotalW steps = u * q43Val) :
    False := by
  by_cases hu4 : u = 4
  · subst hu4; exact no_spiral_cycle_m96_u4 hbar hcyc hm_eq hK hW
  · by_cases hu5 : u = 5
    · subst hu5; exact no_spiral_cycle_m96_u5 hbar hcyc hm_eq hK hW
    · exact eliminate_q43_multiple_tail hbar hcyc (by omega) (by decide) (by decide)
        slab_utail_m96_u6_ok (by omega) hK hW

end CollatzFormal
