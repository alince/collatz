/-
  CollatzFormal/Wave11WholeSpace.lean
  Wave 11 Whole-Space Mathematical & CS Proof Loop:
  1. Front A — Left-Anchored / Reachable Arts–Giesl Dependency Pair (`DP2`) Chain Reduction
     (`WellFounded leftAnchoredDP2Step -> CollatzConjectureStandard` + Infinite `L`-Anchored
     `DP2` Recurrence Modulo `all11OmitR2List`, Separating `Z^+` Reachable Words from Unanchored
     `M2 = -1` `R8` Loops), `TwoSided(2 × 3)` / `TwoSided(2 × 6)` Rule-Removal & Positive-Syzygy
     Certificates (`60 -> 39`, `66 -> 64`, `120 -> 78`, `132 -> 126`), Exact Higher `K ∈ {4, 8}`,
     `M ∈ {6, 12, 18}` Left/Right Semantic Carriers, Fixed-Point-Free Period-`2` `deltaL_flip2`
     Certificate (`[]` axioms), & Universal `∀ K, M ≥ 1` Finite-Carrier Mersenne `B1/T2` Spine Lock (Branch P4.3)
  2. Front B — Complete Mod-`24` `2`-Adic Reciprocity Classification (`{7, 19, 23}` Universal Odd-`gcd`,
     Quartic `q ≡ 5` `6^((q-1)/4)` Biconditional, Octic `q ≡ 17` `8 ∣ ord_q(3/2)` Lock), Universal
     `ℓ`-Sylow (`ℓ = 2, 3, 5`; `mod 72, 96, 240`) Order-Lock + All-`m` (`∀ m ≥ 1`) Shared-Mersenne
     `m`-Block Obstructions + 1-Block Companion-Prime Quotient Cascades (`15 ∣ q0`, `255 ∣ q0`, `31 ∣ q0`,
     `511 ∣ q0`) + `(123, 195)` / `(205, 325)` / `(328, 520)` 2-Block Floors, Universal `∀ T ≥ 1`
     `(T + 1) × (T + 1)` Single-Base Closed Form (`W^(T*(T-1)/2) * (2^u - 1)^T`, Including `8 × 8`
     `W^21 * (2^u - 1)^7`) + Upgraded `2^u (2^u - 1)^(2T)` & `2^(3u) (2^u - 1)^9` Extrapolation +
     Column-Majorant Laplace Bound, & Rank-2 Vandermonde `6 × 6` `(T = 3, U = 2)` Closed Form / Cone
     Positivity + `8 × 8` Two-Base `(T = 4, U = 2)` Congruence / Divisibility / Cone Sign-Flip (Branches P3.4 & P3.3)
  3. Front C — Unconditional Closure of ALL `∀ Q ≥ 1` Stateful MSB, LSB, & Joint `MSB + LSB`
     Zero-Testing `1`-Counter Pushdown (`OCN`) Preimage Weights (Dual Unary `1`-Run Semilinear
     Dichotomy, Observable-Mode `(q, c == 0)` Impossibility, Constructive Mod-`9` Backward Collatz
     Branch-Descent Refuting ALL Polynomial-`binBitLength` Denominator & ALL Unrestricted Raw-Counter
     `NatPoly2` / `NatPoly3` `OCN` Weights with Zero Sign or Slope Assumptions, Asymmetric-Slope
     `Q = 2` Mersenne-Bypass Certificate, & Multi-Symbol Context-Free `PDA` Stack-Mode Periodicity),
     plus 8th Solvable Cousin `T_diamond8` (`ω^6` 6-Tier Cascade, `Q_(6)^+` Avoidance, & Separation)
     (Branches P1.2 & P5.10)
  4. Front D — Exact Static First-Hit `IsFirstHitOnePair u 0 ↔ canonicalSuffixShift u 1 ≥ 3` &
     All-Ones `3^(w - 1)` Law, Complete Mod-`162` (`2 * 3^4`) Markov Bijection & 5-Ones `81 mod 162`
     Lock, Universal Super-Critical `L > M + w + 1` Dyadic-Window Shift-Multiplicity Law, & Coupled
     `dyadicWindowSurvivingQ0Leaves` Mod-`162` Confinement + `3^(w - 5)` Fiber Equidistribution (Branches P2.2 & P5.3)

  Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

import CollatzFormal.Wave10WholeSpace
import CollatzFormal.Wave11WholeSpaceCore

namespace CollatzFormal

-- ============================================================================
-- SECTION 3: Front C (Branches P1.2 & P5.10) — Closing ALL General Mixed-Sign
--            `∀ Q ≥ 1` Zero-Testing 1-Counter Pushdown (`OCN`) Preimage Weights
--            + 8th Solvable `(3x + 1)`-Cousin `T_diamond8` (`ω^6` 6-Tier Cascade)
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Section 3A: General Mixed-Sign `∀ Q ≥ 1` MSB + LSB `OCN` Preimage Impossibility (`P1.2`)
-- ----------------------------------------------------------------------------

/-- Fuel-stabilized LSB-to-MSB `Q`-state zero-testing `1`-counter pushdown automaton runner. -/
def runLSBOneCounterOCNAux {Q : Nat}
    (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp) :
    Nat -> Nat -> (Fin Q × Nat) -> (Fin Q × Nat)
  | 0, _, cfg => cfg
  | fuel + 1, n, cfg =>
    if n = 0 then cfg
    else runLSBOneCounterOCNAux deltaZero deltaPos fuel (n / 2)
           (stepOCN deltaZero deltaPos cfg (n % 2 == 1))

def runLSBFromOCN {Q : Nat}
    (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp)
    (n : Nat) (cfg : Fin Q × Nat) : Fin Q × Nat :=
  runLSBOneCounterOCNAux deltaZero deltaPos n n cfg

def runLSBOneCounterOCN (Q : Nat)
    (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp)
    (q0 : Fin Q) (n : Nat) : Fin Q × Nat :=
  runLSBFromOCN deltaZero deltaPos n (q0, 0)

/-- Observable control mode `(q, c == 0)` of a zero-testing `1`-counter configuration. -/
def ocnObservableMode {Q : Nat} (cfg : Fin Q × Nat) : Fin Q × Bool :=
  (cfg.1, cfg.2 == 0)

/-- Bit-complemented transition table mapping `iterOCN1` directly to `iterOCN0`. -/
def flipOCNTable {Q : Nat}
    (d : Fin Q -> Bool -> Fin Q × CounterOp) : Fin Q -> Bool -> Fin Q × CounterOp :=
  fun q b => d q (!b)

theorem iterOCN1_eq_iterOCN0_flip {Q : Nat}
    (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp) :
    ∀ (k : Nat) (cfg : Fin Q × Nat),
      iterOCN1 deltaZero deltaPos k cfg =
        iterOCN0 (flipOCNTable deltaZero) (flipOCNTable deltaPos) k cfg
  | 0, _ => rfl
  | k + 1, cfg => by
    simp only [iterOCN1, iterOCN0, iterOCN1_eq_iterOCN0_flip deltaZero deltaPos k cfg]
    rfl

theorem runLSBOneCounterOCNAux_eq_of_ge {Q : Nat}
    (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp) :
    ∀ (f1 f2 n : Nat) (cfg : Fin Q × Nat),
      n ≤ f1 -> n ≤ f2 ->
      runLSBOneCounterOCNAux deltaZero deltaPos f1 n cfg =
        runLSBOneCounterOCNAux deltaZero deltaPos f2 n cfg
  | 0, 0, _, _, _, _ => rfl
  | 0, _ + 1, n, _, h1, _ => by rw [show n = 0 by omega]; simp [runLSBOneCounterOCNAux]
  | _ + 1, 0, n, _, _, h2 => by rw [show n = 0 by omega]; simp [runLSBOneCounterOCNAux]
  | f1 + 1, f2 + 1, n, cfg, h1, h2 => by
    simp only [runLSBOneCounterOCNAux]
    by_cases hn0 : n = 0
    · simp [hn0]
    · simp only [hn0, ite_false]
      exact runLSBOneCounterOCNAux_eq_of_ge deltaZero deltaPos f1 f2 (n / 2)
        (stepOCN deltaZero deltaPos cfg (n % 2 == 1)) (by omega) (by omega)

theorem runLSBFromOCN_step_pos {Q : Nat}
    (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp)
    (n : Nat) (hn : n ≥ 1) (cfg : Fin Q × Nat) :
    runLSBFromOCN deltaZero deltaPos n cfg =
      runLSBFromOCN deltaZero deltaPos (n / 2)
        (stepOCN deltaZero deltaPos cfg (n % 2 == 1)) := by
  unfold runLSBFromOCN
  cases n with
  | zero => omega
  | succ m =>
    simp only [runLSBOneCounterOCNAux, Nat.succ_ne_zero, ite_false]
    exact runLSBOneCounterOCNAux_eq_of_ge deltaZero deltaPos m ((m + 1) / 2) ((m + 1) / 2)
      _ (by omega) (Nat.le_refl _)

theorem runLSBFromOCN_mul_pow2 {Q : Nat}
    (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp)
    (H : Nat) (hH : H ≥ 1) :
    ∀ (k : Nat) (cfg : Fin Q × Nat),
      runLSBFromOCN deltaZero deltaPos (2 ^ k * H) cfg =
        runLSBFromOCN deltaZero deltaPos H (iterOCN0 deltaZero deltaPos k cfg)
  | 0, cfg => by simp [iterOCN0]
  | k + 1, cfg => by
    have hmul : 2 ^ (k + 1) * H = 2 * (2 ^ k * H) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
    have hpos : 2 ^ k * H ≥ 1 := Nat.mul_le_mul (pow2_pos_nat k) hH
    have hm2 : ((2 * (2 ^ k * H)) % 2 == 1) = false := by rw [Nat.mul_mod_right]; rfl
    rw [hmul, runLSBFromOCN_step_pos deltaZero deltaPos _ (by omega) cfg,
        hm2, show (2 * (2 ^ k * H)) / 2 = 2 ^ k * H by omega,
        runLSBFromOCN_mul_pow2 deltaZero deltaPos H hH k]
    have h1k : iterOCN0 deltaZero deltaPos k (stepOCN deltaZero deltaPos cfg false) =
        iterOCN0 deltaZero deltaPos (k + 1) cfg :=
      (iterOCN0_add deltaZero deltaPos k 1 cfg).symm
    rw [h1k]

theorem stepOCN_mode_eq_of_pos {Q : Nat}
    (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp)
    (q : Fin Q) (c1 c2 : Nat) (b : Bool) (hc1 : c1 ≥ 2) (hc2 : c2 ≥ 2) :
    ocnObservableMode (stepOCN deltaZero deltaPos (q, c1) b) =
      ocnObservableMode (stepOCN deltaZero deltaPos (q, c2) b) := by
  have hnz1 : ¬ (c1 = 0) := by omega
  have hnz2 : ¬ (c2 = 0) := by omega
  unfold ocnObservableMode stepOCN
  rw [ite_false_of_w10 hnz1, ite_false_of_w10 hnz2]
  dsimp only
  cases (deltaPos q b).2 <;> simp only [applyCounterOp]
  · have h1 : ((c1 - 1) == 0) = false := decide_eq_false (by omega)
    have h2 : ((c2 - 1) == 0) = false := decide_eq_false (by omega)
    rw [h1, h2]
  · have h1 : (c1 == 0) = false := decide_eq_false (by omega)
    have h2 : (c2 == 0) = false := decide_eq_false (by omega)
    rw [h1, h2]
  · have h1 : ((c1 + 1) == 0) = false := decide_eq_false (by omega)
    have h2 : ((c2 + 1) == 0) = false := decide_eq_false (by omega)
    rw [h1, h2]

theorem stepOCN_counter_ge_pred {Q : Nat}
    (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp)
    (cfg : Fin Q × Nat) (b : Bool) :
    (stepOCN deltaZero deltaPos cfg b).2 + 1 ≥ cfg.2 := by
  unfold stepOCN
  by_cases hc0 : cfg.2 = 0
  · simp only [hc0, ite_true]; omega
  · simp only [hc0, ite_false]
    cases (deltaPos cfg.1 b).2 <;> simp only [applyCounterOp] <;> omega

theorem alternating_odd_zero_and_len :
    ∀ r : Nat,
      4 ^ (r + 1) ≥ 4 ∧
      (4 ^ (r + 1) - 1) % 3 = 0 ∧
      zeroBitCount ((4 ^ (r + 1) - 1) / 3) = r ∧
      binBitLength ((4 ^ (r + 1) - 1) / 3) = 2 * r + 1
  | 0 => ⟨by decide, by decide, by decide, by decide⟩
  | r + 1 => by
    rcases alternating_odd_zero_and_len r with ⟨hp4, hm3, hz, hl⟩
    let prev := (4 ^ (r + 1) - 1) / 3
    have hprev_eq : 3 * prev = 4 ^ (r + 1) - 1 := by dsimp [prev]; omega
    have hprev_pos : prev ≥ 1 := by omega
    have hp4_next : 4 ^ (r + 2) = 4 * 4 ^ (r + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    have hcur_eq : (4 ^ (r + 2) - 1) / 3 = 2 * (2 * prev) + 1 := by rw [hp4_next]; omega
    refine ⟨by omega, by rw [hp4_next]; omega, ?_, ?_⟩
    · rw [hcur_eq]
      have hs1 := (window_step_pos 1 (2 * (2 * prev) + 1) (by omega)).2
      have hm1 : (2 * (2 * prev) + 1) % (2 ^ 1) = 1 := by
        rw [Nat.pow_one, Nat.add_comm, Nat.add_mul_mod_self_left]
      have hd1 : (2 * (2 * prev) + 1) / 2 = 2 * prev := by omega
      rw [hm1, hd1] at hs1; simp only [Nat.one_ne_zero, ite_false, Nat.zero_add] at hs1
      have hs2 := (window_step_pos 1 (2 * prev) (by omega)).2
      have hm2 : (2 * prev) % (2 ^ 1) = 0 := by rw [Nat.pow_one, Nat.mul_mod_right]
      have hd2 : (2 * prev) / 2 = prev := by omega
      rw [hm2, hd2] at hs2; simp only [ite_true] at hs2
      unfold zeroBitCount at hz ⊢
      rw [hs1, hs2, hz]; omega
    · rw [hcur_eq,
          binBitLength_step_pos (2 * (2 * prev) + 1) (by omega),
          show (2 * (2 * prev) + 1) / 2 = 2 * prev by omega,
          binBitLength_step_pos (2 * prev) (by omega),
          show (2 * prev) / 2 = prev by omega,
          hl]
      omega

/-- Finite sum of `g μL μM` across all `4 * Q_L * Q_M` observable modes (giving a constructive upper bound). -/
def sumModesAuxM {Q_M : Nat} (f : (Fin Q_M × Bool) -> Nat) : (k : Nat) -> k ≤ Q_M -> Nat
  | 0, _ => 0
  | k + 1, hk =>
    f (⟨k, hk⟩, false) + f (⟨k, hk⟩, true) + sumModesAuxM f k (Nat.le_of_lt hk)

theorem le_sumModesAuxM {Q_M : Nat} (f : (Fin Q_M × Bool) -> Nat) :
    ∀ (k : Nat) (hk : k ≤ Q_M) (μM : Fin Q_M × Bool),
      μM.1.val < k -> f μM ≤ sumModesAuxM f k hk
  | 0, _, _, hlt => by omega
  | k + 1, hk, (qM, bM), hlt => by
    simp only [sumModesAuxM]
    by_cases hqk : qM.val = k
    · have hqf : qM = ⟨k, hk⟩ := Fin.ext hqk
      subst hqf
      cases bM <;> omega
    · change qM.val < k + 1 at hlt
      have ih := le_sumModesAuxM f k (Nat.le_of_lt hk) (qM, bM) (by change qM.val < k; omega)
      omega

def sumAllJointModes (Q_L Q_M : Nat)
    (g : (Fin Q_L × Bool) -> (Fin Q_M × Bool) -> Nat) : (k : Nat) -> k ≤ Q_L -> Nat
  | 0, _ => 0
  | k + 1, hk =>
    sumModesAuxM (g (⟨k, hk⟩, false)) Q_M (Nat.le_refl Q_M) +
    sumModesAuxM (g (⟨k, hk⟩, true)) Q_M (Nat.le_refl Q_M) +
    sumAllJointModes Q_L Q_M g k (Nat.le_of_lt hk)

theorem le_sumAllJointModes (Q_L Q_M : Nat)
    (g : (Fin Q_L × Bool) -> (Fin Q_M × Bool) -> Nat) :
    ∀ (k : Nat) (hk : k ≤ Q_L) (μL : Fin Q_L × Bool) (μM : Fin Q_M × Bool),
      μL.1.val < k -> g μL μM ≤ sumAllJointModes Q_L Q_M g k hk
  | 0, _, _, _, hlt => by omega
  | k + 1, hk, (qL, bL), μM, hlt => by
    simp only [sumAllJointModes]
    by_cases hqk : qL.val = k
    · have hqf : qL = ⟨k, hk⟩ := Fin.ext hqk
      subst hqf
      cases bL
      · have hm := le_sumModesAuxM (g (⟨k, hk⟩, false)) Q_M (Nat.le_refl Q_M) μM μM.1.isLt
        omega
      · have hm := le_sumModesAuxM (g (⟨k, hk⟩, true)) Q_M (Nat.le_refl Q_M) μM μM.1.isLt
        omega
    · change qL.val < k + 1 at hlt
      have ih := le_sumAllJointModes Q_L Q_M g k (Nat.le_of_lt hk) (qL, bL) μM (by change qL.val < k; omega)
      omega

/-- Concrete `Q = 2` mixed-sign zero-testing `OCN` witness (`ZPOS_MIXED_SIGN_Q2_OCN_PREIMAGE_COLLAPSE`). -/
def mixedSignQ2Zero : Fin 2 -> Bool -> Fin 2 × CounterOp :=
  fun q b =>
    if q.val = 0 then
      if b then (⟨0, by decide⟩, .inc) else (⟨1, by decide⟩, .stay)
    else
      if b then (⟨1, by decide⟩, .inc) else (⟨0, by decide⟩, .stay)

def mixedSignQ2Pos : Fin 2 -> Bool -> Fin 2 × CounterOp :=
  fun q b =>
    if q.val = 0 then
      if b then (⟨0, by decide⟩, .inc) else (⟨1, by decide⟩, .stay)
    else
      if b then (⟨1, by decide⟩, .dec) else (⟨0, by decide⟩, .dec)

private theorem runMSBOneCounterOCN_eq_log_fuel {Q : Nat}
    (dz dp : Fin Q -> Bool -> Fin Q × CounterOp) (q0 : Fin Q) :
    ∀ (fuel n : Nat), n < 2 ^ fuel ->
      runMSBOneCounterOCN Q dz dp q0 n = runMSBOneCounterOCNAux dz dp q0 fuel n
  | 0, n, hn => by
    have hn0 : n = 0 := by omega
    subst hn0; rfl
  | fuel + 1, n, hn => by
    by_cases hn0 : n = 0
    · subst hn0; rfl
    · rw [runMSBOneCounterOCN_step_pos dz dp q0 n (by omega)]
      simp only [runMSBOneCounterOCNAux, hn0, ite_false]
      rw [runMSBOneCounterOCN_eq_log_fuel dz dp q0 fuel (n / 2)
        (by rw [Nat.pow_succ] at hn; omega)]

private theorem w11_ocn_q2_witness_cert :
    collatzStep 8277 = 12416 ∧ 12416 % 3 = 2 ∧ (2 * 12416 - 1) / 3 = 8277 ∧
    (runMSBOneCounterOCN 2 mixedSignQ2Zero mixedSignQ2Pos ⟨0, by decide⟩ 56).2 = 2 ∧
    (runMSBOneCounterOCN 2 mixedSignQ2Zero mixedSignQ2Pos ⟨0, by decide⟩ 224).2 = 1 ∧
    runMSBOneCounterOCN 2 mixedSignQ2Zero mixedSignQ2Pos ⟨0, by decide⟩ 12416 = (⟨1, by decide⟩, 0) ∧
    runMSBOneCounterOCN 2 mixedSignQ2Zero mixedSignQ2Pos ⟨0, by decide⟩ 49664 = (⟨1, by decide⟩, 0) := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
  · rw [runMSBOneCounterOCN_eq_log_fuel mixedSignQ2Zero mixedSignQ2Pos ⟨0, by decide⟩ 6 56 (by decide)]
    decide
  · rw [runMSBOneCounterOCN_eq_log_fuel mixedSignQ2Zero mixedSignQ2Pos ⟨0, by decide⟩ 8 224 (by decide)]
    decide
  · rw [runMSBOneCounterOCN_eq_log_fuel mixedSignQ2Zero mixedSignQ2Pos ⟨0, by decide⟩ 14 12416 (by decide)]
    decide
  · rw [runMSBOneCounterOCN_eq_log_fuel mixedSignQ2Zero mixedSignQ2Pos ⟨0, by decide⟩ 16 49664 (by decide)]
    decide

private theorem w11_ocn_part1_dual :
    ∀ (Q : Nat), Q ≥ 1 ->
      ∀ (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp)
        (B : Nat) (cfg0 : Fin Q × Nat),
        cfg0.2 ≤ B ->
        let M_box := Q * (B + Q + 1)
        let P_ocn := natFact M_box
        ∃ slope1 : Nat,
          ((∀ t : Nat, t ≤ M_box -> (iterOCN1 deltaZero deltaPos t cfg0).2 < B + Q + 1) -> slope1 = 0) ∧
          (∀ (m k : Nat), k ≥ M_box ->
            (iterOCN1 deltaZero deltaPos (k + P_ocn * m) cfg0).1 =
              (iterOCN1 deltaZero deltaPos k cfg0).1 ∧
            (iterOCN1 deltaZero deltaPos (k + P_ocn * m) cfg0).2 =
              m * slope1 + (iterOCN1 deltaZero deltaPos k cfg0).2) := by
    intro Q hQ dz dp B cfg0 hB
    dsimp only
    rcases ocn_unary_zero_run_semilinear_dichotomy hQ (flipOCNTable dz) (flipOCNTable dp) B cfg0 hB with
      ⟨slope1, hzero, hsemi⟩
    refine ⟨slope1, ?_, ?_⟩
    · intro hall
      apply hzero
      intro t ht
      rw [← iterOCN1_eq_iterOCN0_flip dz dp t cfg0]
      exact hall t ht
    · intro m k hk
      rw [iterOCN1_eq_iterOCN0_flip dz dp (k + natFact (Q * (B + Q + 1)) * m) cfg0,
          iterOCN1_eq_iterOCN0_flip dz dp k cfg0]
      exact hsemi m k hk

set_option maxHeartbeats 400000 in
private theorem w11_ocn_part3_joint_mode :
    ∀ (Q_L Q_M : Nat), Q_L ≥ 1 -> Q_M ≥ 1 ->
      ∀ (dzL dpL : Fin Q_L -> Bool -> Fin Q_L × CounterOp)
        (dzM dpM : Fin Q_M -> Bool -> Fin Q_M × CounterOp)
        (q0L : Fin Q_L) (q0M : Fin Q_M)
        (fNum fDen : (Fin Q_L × Bool) -> (Fin Q_M × Bool) -> Nat)
        (pTerms qTerms : NatPoly2) (pTheta qTheta : Nat),
        ¬ IsPositiveRationalPreimageWeight
          (fun n =>
            fNum (ocnObservableMode (runLSBOneCounterOCN Q_L dzL dpL q0L n))
                 (ocnObservableMode (runMSBOneCounterOCN Q_M dzM dpM q0M n)) *
            evalNatPoly2 pTerms (zeroBitCount n) (binBitLength n))
          (fun n =>
            fDen (ocnObservableMode (runLSBOneCounterOCN Q_L dzL dpL q0L n))
                 (ocnObservableMode (runMSBOneCounterOCN Q_M dzM dpM q0M n)) *
            evalNatPoly2 qTerms (zeroBitCount n) (binBitLength n))
          pTheta qTheta := by
    intro Q_L Q_M hQL hQM dzL dpL dzM dpM q0L q0M fNum fDen pTerms qTerms pTheta qTheta hw
    let M_L := Q_L * (1 + Q_L + 1)
    let M_M := Q_M * (1 + Q_M + 1)
    let P_L := natFact M_L
    let P_M := natFact M_M
    let P_joint := P_L * P_M
    have hPL_pos : P_L ≥ 1 := natFact_pos M_L
    have hPM_pos : P_M ≥ 1 := natFact_pos M_M
    have hPj_pos : P_joint ≥ 1 := Nat.mul_le_mul hPL_pos hPM_pos
    let r0 := M_L + M_M + 2
    let k0 := 2 * r0 + 1
    have hk0_ge_L : k0 ≥ M_L := by dsimp only [k0, r0]; omega
    have hk0_ge_M : k0 ≥ M_M := by dsimp only [k0, r0]; omega
    have hk0_pos : k0 ≥ 3 := by dsimp only [k0, r0]; omega
    -- Apply `0`-run semilinear dichotomy to LSB `(q0L, 0)` and MSB `runMSB 1` (`c ≤ 1`):
    have hcfgL_le : ((q0L, (0 : Nat))).2 ≤ 1 := Nat.zero_le 1
    let cfgM1 := runMSBOneCounterOCN Q_M dzM dpM q0M 1
    have hcfgM_le : cfgM1.2 ≤ 1 := by
      dsimp only [cfgM1]
      rw [runMSBOneCounterOCN_step_pos dzM dpM q0M 1 (by decide)]
      have h0 : runMSBOneCounterOCN Q_M dzM dpM q0M 0 = (q0M, 0) := rfl
      rw [h0]
      have hs := stepOCN_counter_le_succ dzM dpM (q0M, 0) true
      omega
    rcases ocn_unary_zero_run_semilinear_dichotomy hQL dzL dpL 1 (q0L, 0) hcfgL_le with
      ⟨slopeL, _, hsemiL⟩
    rcases ocn_unary_zero_run_semilinear_dichotomy hQM dzM dpM 1 cfgM1 hcfgM_le with
      ⟨slopeM, _, hsemiM⟩
    -- Prove that for ALL `u ≥ 2`, `2 ^ (k0 + P_joint * u)` has identical `(modeL, modeM)` to `u = 2`:
    have hmode_pow2 : ∀ u : Nat, u ≥ 2 ->
        ocnObservableMode (runLSBOneCounterOCN Q_L dzL dpL q0L (2 ^ (k0 + P_joint * u))) =
          ocnObservableMode (runLSBOneCounterOCN Q_L dzL dpL q0L (2 ^ (k0 + P_joint * 2))) ∧
        ocnObservableMode (runMSBOneCounterOCN Q_M dzM dpM q0M (2 ^ (k0 + P_joint * u))) =
          ocnObservableMode (runMSBOneCounterOCN Q_M dzM dpM q0M (2 ^ (k0 + P_joint * 2))) := by
      intro u hu2
      have hlsb_k : ∀ k : Nat,
          runLSBOneCounterOCN Q_L dzL dpL q0L (2 ^ k) =
            stepOCN dzL dpL (iterOCN0 dzL dpL k (q0L, 0)) true := by
        intro k
        unfold runLSBOneCounterOCN
        have h1 : 2 ^ k = 2 ^ k * 1 := (Nat.mul_one _).symm
        rw [h1, runLSBFromOCN_mul_pow2 dzL dpL 1 (by decide) k (q0L, 0),
            runLSBFromOCN_step_pos dzL dpL 1 (by decide)]
        rfl
      have hmsb_k : ∀ k : Nat,
          runMSBOneCounterOCN Q_M dzM dpM q0M (2 ^ k) =
            iterOCN0 dzM dpM k cfgM1 := by
        intro k
        have h1 : 2 ^ k = 2 ^ k * 1 := (Nat.mul_one _).symm
        rw [h1]; exact runMSBOneCounterOCN_mul_pow2 dzM dpM q0M 1 (by decide) k
      have hPL_mul : ∀ v : Nat, P_joint * v = P_L * (P_M * v) :=
        fun v => Nat.mul_assoc P_L P_M v
      have hPM_mul : ∀ v : Nat, P_joint * v = P_M * (P_L * v) := by
        intro v; dsimp only [P_joint]; rw [Nat.mul_comm P_L P_M, Nat.mul_assoc]
      refine ⟨?_, ?_⟩
      · rw [hlsb_k, hlsb_k, hPL_mul u, hPL_mul 2]
        rcases hsemiL (P_M * u) k0 hk0_ge_L with ⟨hq_u, hc_u⟩
        rcases hsemiL (P_M * 2) k0 hk0_ge_L with ⟨hq_2, hc_2⟩
        let q_ex := (iterOCN0 dzL dpL k0 (q0L, 0)).1
        let c_ex := (iterOCN0 dzL dpL k0 (q0L, 0)).2
        have hcfg_u : iterOCN0 dzL dpL (k0 + P_L * (P_M * u)) (q0L, 0) =
            (q_ex, (P_M * u) * slopeL + c_ex) := Prod.ext hq_u hc_u
        have hcfg_2 : iterOCN0 dzL dpL (k0 + P_L * (P_M * 2)) (q0L, 0) =
            (q_ex, (P_M * 2) * slopeL + c_ex) := Prod.ext hq_2 hc_2
        rw [hcfg_u, hcfg_2]
        cases slopeL with
        | zero => simp
        | succ sl' =>
          have hge_u : (P_M * u) * (sl' + 1) + c_ex ≥ 2 := by
            have hm1 : 2 ≤ P_M * u := by
              simpa using Nat.mul_le_mul hPM_pos hu2
            have hm2 : 2 * 1 ≤ (P_M * u) * (sl' + 1) := Nat.mul_le_mul hm1 (by omega)
            omega
          have hge_2 : (P_M * 2) * (sl' + 1) + c_ex ≥ 2 := by
            have hm1 : 2 ≤ P_M * 2 := by
              simpa using Nat.mul_le_mul hPM_pos (Nat.le_refl 2)
            have hm2 : 2 * 1 ≤ (P_M * 2) * (sl' + 1) := Nat.mul_le_mul hm1 (by omega)
            omega
          exact stepOCN_mode_eq_of_pos dzL dpL q_ex _ _ true hge_u hge_2
      · rw [hmsb_k, hmsb_k, hPM_mul u, hPM_mul 2]
        rcases hsemiM (P_L * u) k0 hk0_ge_M with ⟨hq_u, hc_u⟩
        rcases hsemiM (P_L * 2) k0 hk0_ge_M with ⟨hq_2, hc_2⟩
        let q_ex := (iterOCN0 dzM dpM k0 cfgM1).1
        let c_ex := (iterOCN0 dzM dpM k0 cfgM1).2
        have hcfg_u : iterOCN0 dzM dpM (k0 + P_M * (P_L * u)) cfgM1 =
            (q_ex, (P_L * u) * slopeM + c_ex) := Prod.ext hq_u hc_u
        have hcfg_2 : iterOCN0 dzM dpM (k0 + P_M * (P_L * 2)) cfgM1 =
            (q_ex, (P_L * 2) * slopeM + c_ex) := Prod.ext hq_2 hc_2
        rw [hcfg_u, hcfg_2]
        cases slopeM with
        | zero => simp
        | succ sm' =>
          have hge_u : (P_L * u) * (sm' + 1) + c_ex ≥ 2 := by
            have hm1 : 2 ≤ P_L * u := by simpa using Nat.mul_le_mul hPL_pos hu2
            have hm2 : 2 * 1 ≤ (P_L * u) * (sm' + 1) := Nat.mul_le_mul hm1 (by omega)
            omega
          have hge_2 : (P_L * 2) * (sm' + 1) + c_ex ≥ 2 := by
            have hm1 : 2 ≤ P_L * 2 := by simpa using Nat.mul_le_mul hPL_pos (Nat.le_refl 2)
            have hm2 : 2 * 1 ≤ (P_L * 2) * (sm' + 1) := Nat.mul_le_mul hm1 (by omega)
            omega
          unfold ocnObservableMode
          dsimp only
          have h1 : (((P_L * u) * (sm' + 1) + c_ex) == 0) = false := decide_eq_false (by omega)
          have h2 : (((P_L * 2) * (sm' + 1) + c_ex) == 0) = false := decide_eq_false (by omega)
          rw [h1, h2]
    -- Reference point `u = 2`:
    let m_ref := 2 ^ (k0 + P_joint * 2)
    have hm_ref_ge3 : m_ref ≥ 3 := by
      dsimp only [m_ref]
      exact Nat.le_trans (by decide : 3 ≤ 2 ^ 3) (pow2_mono_nat (by omega))
    let μL_E := ocnObservableMode (runLSBOneCounterOCN Q_L dzL dpL q0L m_ref)
    let μM_E := ocnObservableMode (runMSBOneCounterOCN Q_M dzM dpM q0M m_ref)
    let aE := fNum μL_E μM_E
    let bE := fDen μL_E μM_E
    have hpos_fac : ∀ x y : Nat, x * y > 0 -> x ≥ 1 ∧ y ≥ 1 := by
      intro x y h
      cases x with
      | zero => simp at h
      | succ _ =>
        cases y with
        | zero => simp at h
        | succ _ => exact ⟨by omega, by omega⟩
    rcases hw.2.2.1 m_ref hm_ref_ge3 with ⟨hnum_ref, hden_ref⟩
    dsimp only at hnum_ref hden_ref
    have haE_pos : aE ≥ 1 := (hpos_fac _ _ hnum_ref).1
    have hbE_pos : bE ≥ 1 := (hpos_fac _ _ hden_ref).1
    let F_den := 1 + sumAllJointModes Q_L Q_M fDen Q_L (Nat.le_refl Q_L)
    have hF_pos : F_den ≥ 1 := by dsimp only [F_den]; omega
    let dP := maxDegNatPoly2 pTerms
    let dQ := maxDegNatPoly2 qTerms
    let D := dP + dQ
    let C := 2 * r0 + 2 * P_joint + 4
    have hC_pos : C ≥ 1 := by dsimp only [C]; omega
    let M_hi : Nat := 4 + C
    have hMhi_ge1 : M_hi ≥ 1 := by dsimp only [M_hi]; omega
    let B_mode := aE * F_den
    have hBmode_pos : B_mode ≥ 1 := Nat.mul_le_mul haE_pos hF_pos
    let B_eff := B_mode * M_hi ^ D
    have hBeff_pos : B_eff ≥ 1 := Nat.mul_le_mul hBmode_pos (nat_pow_pos_of_pos M_hi hMhi_ge1 D)
    let s_idx := (B_eff + bE + 1) * (D * C + 1) + 2
    have hs_ge2 : s_idx ≥ 2 := by dsimp only [s_idx]; omega
    let r := r0 + P_joint * s_idx
    have hr_ge : r ≥ (B_eff + bE + 1) * (D * C + 1) := by
      have hm : 1 * s_idx ≤ P_joint * s_idx := Nat.mul_le_mul_right s_idx hPj_pos
      dsimp only [r, s_idx] at hm ⊢; omega
    have hr_pos : r ≥ 2 := by dsimp only [r, r0]; omega
    let ms := 2 ^ (2 * r + 1)
    let evs := 2 ^ (2 * P_joint) * ms
    let ns := (2 * ms - 1) / 3
    have h2r1_eq : 2 * r + 1 = k0 + P_joint * (2 * s_idx) := by
      dsimp only [r, k0]; rw [Nat.mul_add 2 r0 (P_joint * s_idx),
        ← Nat.mul_assoc 2 P_joint s_idx, Nat.mul_comm 2 P_joint, Nat.mul_assoc]; omega
    have hevs_pow : evs = 2 ^ (k0 + P_joint * (2 * s_idx + 2)) := by
      dsimp only [evs, ms]
      rw [← Nat.pow_add 2 (2 * P_joint) (2 * r + 1), h2r1_eq,
          Nat.mul_add P_joint (2 * s_idx) 2, Nat.mul_comm 2 P_joint]
      apply congrArg (2 ^ ·); omega
    have hms_pow : ms = 2 ^ (k0 + P_joint * (2 * s_idx)) := by dsimp only [ms]; rw [h2r1_eq]
    have hms_ge3 : ms ≥ 3 := by
      dsimp only [ms]; exact Nat.le_trans (by decide : 3 ≤ 2 ^ 3) (pow2_mono_nat (by omega))
    have hms_m3 : ms % 3 = 2 := by
      dsimp only [ms]; rw [Nat.pow_succ, ← pow4_eq_pow2_even r]
      have h4_1 : ∀ t : Nat, 4 ^ t % 3 = 1 := by
        intro t; induction t with
        | zero => rfl
        | succ t' ih => rw [Nat.pow_succ, Nat.mul_mod, ih]
      rw [Nat.mul_mod, h4_1 r]
    have hns_alt : ns = (4 ^ (r + 1) - 1) / 3 := by
      dsimp only [ns, ms]
      have h2m : 2 * 2 ^ (2 * r + 1) = 4 ^ (r + 1) := by
        rw [Nat.mul_comm 2 (2 ^ (2 * r + 1)), ← Nat.pow_succ 2 (2 * r + 1),
            show (2 * r + 1).succ = 2 * (r + 1) by omega,
            ← pow4_eq_pow2_even (r + 1)]
      rw [h2m]
    rcases alternating_odd_zero_and_len r with ⟨_, _, hz_alt, hl_alt⟩
    have hns_ge3 : ns ≥ 3 := by
      rw [hns_alt]
      have h4_ge16 : 4 ^ (r + 1) ≥ 16 := by
        simpa using nat_pow_mono_exp_pos 4 2 (r + 1) (by decide) (by omega)
      omega
    -- Mode equalities on `ms` and `evs`:
    rcases hmode_pow2 (2 * s_idx) (by omega) with ⟨hL_ms, hM_ms⟩
    rcases hmode_pow2 (2 * s_idx + 2) (by omega) with ⟨hL_ev, hM_ev⟩
    rw [← hms_pow] at hL_ms hM_ms
    rw [← hevs_pow] at hL_ev hM_ev
    -- Multi-step even preimage inequality at `(ms, d = 2 * P_joint)`:
    have hineq := preimage_multistep_even_branch_ineq _ _ pTheta qTheta ms (2 * P_joint)
      hw hms_ge3 hms_m3 (by omega)
    dsimp only at hineq
    change ((fNum _ _ * evalNatPoly2 pTerms (zeroBitCount evs) (binBitLength evs)) *
              (fDen _ _ * evalNatPoly2 qTerms (zeroBitCount ns) (binBitLength ns)) +
            (fNum _ _ * evalNatPoly2 pTerms (zeroBitCount ns) (binBitLength ns)) *
              (fDen _ _ * evalNatPoly2 qTerms (zeroBitCount evs) (binBitLength evs))) *
            (fDen _ _ * evalNatPoly2 qTerms (zeroBitCount ms) (binBitLength ms)) ≤
          (fNum _ _ * evalNatPoly2 pTerms (zeroBitCount ms) (binBitLength ms)) *
            ((fDen _ _ * evalNatPoly2 qTerms (zeroBitCount evs) (binBitLength evs)) *
              (fDen _ _ * evalNatPoly2 qTerms (zeroBitCount ns) (binBitLength ns))) at hineq
    rw [hL_ms, hM_ms, hL_ev, hM_ev] at hineq
    let aO := fNum (ocnObservableMode (runLSBOneCounterOCN Q_L dzL dpL q0L ns))
                   (ocnObservableMode (runMSBOneCounterOCN Q_M dzM dpM q0M ns))
    let bO := fDen (ocnObservableMode (runLSBOneCounterOCN Q_L dzL dpL q0L ns))
                   (ocnObservableMode (runMSBOneCounterOCN Q_M dzM dpM q0M ns))
    let P_m := evalNatPoly2 pTerms (zeroBitCount ms) (binBitLength ms)
    let Q_m := evalNatPoly2 qTerms (zeroBitCount ms) (binBitLength ms)
    let P_ev := evalNatPoly2 pTerms (zeroBitCount evs) (binBitLength evs)
    let Q_ev := evalNatPoly2 qTerms (zeroBitCount evs) (binBitLength evs)
    let P_n := evalNatPoly2 pTerms (zeroBitCount ns) (binBitLength ns)
    let Q_n := evalNatPoly2 qTerms (zeroBitCount ns) (binBitLength ns)
    change ((aE * P_ev) * (bO * Q_n) + (aO * P_n) * (bE * Q_ev)) * (bE * Q_m) ≤
      (aE * P_m) * ((bE * Q_ev) * (bO * Q_n)) at hineq
    rcases hw.2.2.1 ms hms_ge3 with ⟨hnum_ms, hden_ms⟩
    rcases hw.2.2.1 evs (by dsimp only [evs]; have hm := Nat.mul_le_mul (pow2_pos_nat (2 * P_joint)) hms_ge3; omega) with
      ⟨_, hden_ev⟩
    rcases hw.2.2.1 ns hns_ge3 with ⟨hnum_ns, hden_ns⟩
    dsimp only at hnum_ms hden_ms hden_ev hnum_ns hden_ns
    have haO_pos : aO ≥ 1 := (hpos_fac _ _ hnum_ns).1
    have hbO_pos : bO ≥ 1 := (hpos_fac _ _ hden_ns).1
    have hbO_le : bO ≤ F_den := by
      dsimp only [bO, F_den]
      have hm := le_sumAllJointModes Q_L Q_M fDen Q_L (Nat.le_refl Q_L)
        (ocnObservableMode (runLSBOneCounterOCN Q_L dzL dpL q0L ns))
        (ocnObservableMode (runMSBOneCounterOCN Q_M dzM dpM q0M ns))
        (ocnObservableMode (runLSBOneCounterOCN Q_L dzL dpL q0L ns)).1.isLt
      omega
    have hPm_pos : P_m ≥ 1 := (hpos_fac _ _ hnum_ms).2
    have hQev_pos : Q_ev ≥ 1 := (hpos_fac _ _ hden_ev).2
    have hQn_pos : Q_n ≥ 1 := (hpos_fac _ _ hden_ns).2
    -- Simplify `hineq` by cancelling `bE ≥ 1` and using `aO ≥ 1`, `aE * bO ≤ B_mode`:
    have hineq_simp : aE * bO * ((P_ev * Q_n) * Q_m) + bE * ((P_n * Q_ev) * Q_m) ≤
        aE * bO * (P_m * (Q_ev * Q_n)) := by
      have hl1 : ((aE * P_ev) * (bO * Q_n) + (aO * P_n) * (bE * Q_ev)) * (bE * Q_m) =
          bE * (aE * bO * ((P_ev * Q_n) * Q_m) + aO * bE * ((P_n * Q_ev) * Q_m)) := by
        generalize P_ev = pe, Q_n = qn, P_n = pn, Q_ev = qe, Q_m = qm
        calc
          ((aE * pe) * (bO * qn) + (aO * pn) * (bE * qe)) * (bE * qm)
              = ((aE * pe) * (bO * qn)) * (bE * qm) + ((aO * pn) * (bE * qe)) * (bE * qm) :=
                Nat.add_mul _ _ _
          _ = bE * (aE * bO * ((pe * qn) * qm)) + bE * (aO * bE * ((pn * qe) * qm)) := by
                congr 1
                · rw [← Nat.mul_assoc (aE * pe) bO qn, Nat.mul_assoc aE pe bO,
                      Nat.mul_comm pe bO, ← Nat.mul_assoc aE bO pe,
                      Nat.mul_assoc (aE * bO) pe qn,
                      ← Nat.mul_assoc (aE * bO * (pe * qn)) bE qm,
                      Nat.mul_comm (aE * bO * (pe * qn)) bE, Nat.mul_assoc bE,
                      Nat.mul_assoc (aE * bO) (pe * qn) qm]
                · rw [← Nat.mul_assoc (aO * pn) bE qe, Nat.mul_assoc aO pn bE,
                      Nat.mul_comm pn bE, ← Nat.mul_assoc aO bE pn,
                      Nat.mul_assoc (aO * bE) pn qe,
                      ← Nat.mul_assoc (aO * bE * (pn * qe)) bE qm,
                      Nat.mul_comm (aO * bE * (pn * qe)) bE, Nat.mul_assoc bE,
                      Nat.mul_assoc (aO * bE) (pn * qe) qm]
          _ = bE * (aE * bO * ((pe * qn) * qm) + aO * bE * ((pn * qe) * qm)) :=
                (Nat.mul_add bE _ _).symm
      have hr1 : (aE * P_m) * ((bE * Q_ev) * (bO * Q_n)) =
          bE * (aE * bO * (P_m * (Q_ev * Q_n))) := by
        generalize P_m = pm, Q_ev = qe, Q_n = qn
        rw [← Nat.mul_assoc (bE * qe) bO qn, Nat.mul_assoc bE qe bO,
            Nat.mul_comm qe bO, ← Nat.mul_assoc bE bO qe, Nat.mul_assoc (bE * bO) qe qn,
            ← Nat.mul_assoc (aE * pm) (bE * bO) (qe * qn),
            Nat.mul_assoc aE pm (bE * bO), Nat.mul_comm pm (bE * bO),
            ← Nat.mul_assoc aE (bE * bO) pm,
            ← Nat.mul_assoc aE bE bO, Nat.mul_comm aE bE, Nat.mul_assoc bE aE bO,
            Nat.mul_assoc (bE * (aE * bO)) pm (qe * qn),
            Nat.mul_assoc bE (aE * bO) (pm * (qe * qn))]
      rw [hl1, hr1] at hineq
      have hcanc_bE := nat_mul_le_cancel_left_w5 bE _ _ hbE_pos hineq
      have haO_ge : 1 * bE * ((P_n * Q_ev) * Q_m) ≤ aO * bE * ((P_n * Q_ev) * Q_m) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right bE haO_pos)
      rw [Nat.one_mul] at haO_ge
      omega
    -- Exact `zeroBitCount` and `binBitLength` formulas on `ms`, `evs`, `ns`:
    have hz0 : zeroBitCount 1 = 0 := by decide
    have hl0 : binBitLength 1 = 1 := by decide
    have hz_ms : zeroBitCount ms = r * 2 + 1 := by
      dsimp only [ms]
      have h := (zeroBitCount_and_len_mul_pow2 1 (by decide) (2 * r + 1)).1
      rw [Nat.mul_one, hz0, Nat.add_zero] at h; rw [h]; omega
    have hbl_ms : binBitLength ms = r * 2 + 2 := by
      dsimp only [ms]
      have h := (zeroBitCount_and_len_mul_pow2 1 (by decide) (2 * r + 1)).2
      rw [Nat.mul_one, hl0] at h; rw [h]; omega
    have hz_evs : zeroBitCount evs = r * 2 + (2 * P_joint + 1) := by
      dsimp only [evs]
      rw [(zeroBitCount_and_len_mul_pow2 ms (by omega) (2 * P_joint)).1, hz_ms]; omega
    have hbl_evs : binBitLength evs = r * 2 + (2 * P_joint + 2) := by
      dsimp only [evs]
      rw [(zeroBitCount_and_len_mul_pow2 ms (by omega) (2 * P_joint)).2, hbl_ms]; omega
    have hz_ns : zeroBitCount ns = r * 1 + 0 := by rw [hns_alt, hz_alt]; omega
    have hbl_ns : binBitLength ns = r * 2 + 1 := by rw [hns_alt, hl_alt, Nat.mul_comm 2 r]
    -- Apply cross-ratio polynomial bounds:
    have hsame1 : ∀ (k c1 c2 : Nat), k ≥ 1 -> c1 ≤ C ->
        r * (r * k + c1) ≤ (r + C) * (r * k + c2) := by
      intro k c1 c2 hk hc1
      have hkc : c1 ≤ k * C := Nat.le_trans hc1 (by simpa using Nat.mul_le_mul_right C hk)
      calc
        r * (r * k + c1) = r * (r * k) + r * c1 := Nat.mul_add _ _ _
        _ ≤ r * (r * k) + C * (r * k) := by
              apply Nat.add_le_add_left
              have hm := Nat.mul_le_mul_left r hkc
              have hr : r * (k * C) = C * (r * k) := by
                rw [← Nat.mul_assoc r k C, Nat.mul_comm (r * k) C]
              rwa [hr] at hm
        _ = (r + C) * (r * k) := (Nat.add_mul r C (r * k)).symm
        _ ≤ (r + C) * (r * k + c2) := Nat.mul_le_mul_left (r + C) (by omega)
    have hdiff1 : ∀ (k1 c1 k2 c2 : Nat),
        k2 ≥ 1 -> k1 + C ≤ M_hi -> c1 ≤ C ->
        1 * (r * k1 + c1) ≤ M_hi * (r * k2 + c2) := by
      intro k1 c1 k2 c2 hk2 hk_hi hc1
      rw [Nat.one_mul]
      have hlo : r ≤ r * k2 + c2 := by
        have hm : r * 1 ≤ r * k2 := Nat.mul_le_mul_left r hk2; omega
      have hhi : r * k1 + c1 ≤ M_hi * r := by
        have hc_r : c1 ≤ C * r :=
          Nat.le_trans hc1 (by simpa using Nat.mul_le_mul_left C (by omega : 1 ≤ r))
        calc
          r * k1 + c1 ≤ k1 * r + C * r := by rw [Nat.mul_comm r k1]; exact Nat.add_le_add_left hc_r _
          _ = (k1 + C) * r := (Nat.add_mul k1 C r).symm
          _ ≤ M_hi * r := Nat.mul_le_mul_right r hk_hi
      exact Nat.le_trans hhi (Nat.mul_le_mul_left M_hi hlo)
    have hpoly2_cr : ∀ (F : NatPoly2) (a b x1 y1 x2 y2 : Nat),
        a ≤ b -> a * x1 ≤ b * x2 -> a * y1 ≤ b * y2 ->
        a ^ (maxDegNatPoly2 F) * evalNatPoly2 F x1 y1 ≤
          b ^ (maxDegNatPoly2 F) * evalNatPoly2 F x2 y2 := by
      intro F a b x1 y1 x2 y2 hab hx hy
      rcases evalNatPoly2_to_3_eq F x1 y1 with ⟨he1, hd1⟩
      rcases evalNatPoly2_to_3_eq F x2 y2 with ⟨he2, _⟩
      rw [he1, he2, hd1]
      exact evalNatPoly3_cross_ratio_bound _ a b x1 y1 1 x2 y2 1 hab hx hy (by omega)
    have hPm_Pev : r ^ dP * P_m ≤ (r + C) ^ dP * P_ev :=
      hpoly2_cr pTerms r (r + C) _ _ _ _ (by omega)
        (by rw [hz_ms, hz_evs]; exact hsame1 2 1 (2 * P_joint + 1) (by decide) (by dsimp only [C]; omega))
        (by rw [hbl_ms, hbl_evs]; exact hsame1 2 2 (2 * P_joint + 2) (by decide) (by dsimp only [C]; omega))
    have hQev_Qm : r ^ dQ * Q_ev ≤ (r + C) ^ dQ * Q_m :=
      hpoly2_cr qTerms r (r + C) _ _ _ _ (by omega)
        (by rw [hz_evs, hz_ms]; exact hsame1 2 (2 * P_joint + 1) 1 (by decide) (by dsimp only [C]; omega))
        (by rw [hbl_evs, hbl_ms]; exact hsame1 2 (2 * P_joint + 2) 2 (by decide) (by dsimp only [C]; omega))
    have hPm_Pn : P_m ≤ M_hi ^ dP * P_n := by
      simpa using hpoly2_cr pTerms 1 M_hi
        (zeroBitCount ms) (binBitLength ms) (zeroBitCount ns) (binBitLength ns) hMhi_ge1
        (by rw [hz_ms, hz_ns]; exact hdiff1 2 1 1 0 (by decide) (by dsimp only [M_hi]; omega) (by dsimp only [C]; omega))
        (by rw [hbl_ms, hbl_ns]; exact hdiff1 2 2 2 1 (by decide) (by dsimp only [M_hi]; omega) (by dsimp only [C]; omega))
    have hQn_Qm : Q_n ≤ M_hi ^ dQ * Q_m := by
      simpa using hpoly2_cr qTerms 1 M_hi
        (zeroBitCount ns) (binBitLength ns) (zeroBitCount ms) (binBitLength ms) hMhi_ge1
        (by rw [hz_ns, hz_ms]; exact hdiff1 1 0 2 1 (by decide) (by dsimp only [M_hi]; omega) (by dsimp only [C]; omega))
        (by rw [hbl_ns, hbl_ms]; exact hdiff1 2 1 2 2 (by decide) (by dsimp only [M_hi]; omega) (by dsimp only [C]; omega))
    let K_den := P_m * (Q_ev * Q_n)
    have hK_pos : K_den ≥ 1 := Nat.mul_le_mul hPm_pos (Nat.mul_le_mul hQev_pos hQn_pos)
    have hrD_le : r ^ D ≤ (r + C) ^ D := by
      have hm : ∀ k : Nat, r ^ k ≤ (r + C) ^ k := by
        intro k; induction k with
        | zero => exact Nat.le_refl 1
        | succ k' ih => rw [Nat.pow_succ, Nat.pow_succ]; exact Nat.mul_le_mul ih (by omega)
      exact hm D
    have hbr_ev : r ^ D * K_den ≤ (r + C) ^ D * ((P_ev * Q_n) * Q_m) := by
      have hm := Nat.mul_le_mul_right Q_n (Nat.mul_le_mul hPm_Pev hQev_Qm)
      have hl : (r ^ dP * P_m * (r ^ dQ * Q_ev)) * Q_n = r ^ D * K_den := by
        dsimp only [D, K_den]
        rw [Nat.pow_add r dP dQ, ← Nat.mul_assoc (r ^ dP * P_m),
            Nat.mul_assoc (r ^ dP) P_m (r ^ dQ), Nat.mul_comm P_m (r ^ dQ),
            ← Nat.mul_assoc (r ^ dP) (r ^ dQ) P_m,
            Nat.mul_assoc (r ^ dP * r ^ dQ) P_m Q_ev,
            Nat.mul_assoc (r ^ dP * r ^ dQ), Nat.mul_assoc P_m Q_ev Q_n]
      have hr_eq : ((r + C) ^ dP * P_ev * ((r + C) ^ dQ * Q_m)) * Q_n =
          (r + C) ^ D * ((P_ev * Q_n) * Q_m) := by
        dsimp only [D]
        rw [Nat.pow_add (r + C) dP dQ, ← Nat.mul_assoc ((r + C) ^ dP * P_ev),
            Nat.mul_assoc ((r + C) ^ dP) P_ev ((r + C) ^ dQ),
            Nat.mul_comm P_ev ((r + C) ^ dQ),
            ← Nat.mul_assoc ((r + C) ^ dP) ((r + C) ^ dQ) P_ev,
            Nat.mul_assoc ((r + C) ^ dP * (r + C) ^ dQ) P_ev Q_m,
            Nat.mul_assoc ((r + C) ^ dP * (r + C) ^ dQ),
            Nat.mul_assoc P_ev Q_m Q_n, Nat.mul_comm Q_m Q_n, ← Nat.mul_assoc P_ev Q_n Q_m]
      rwa [hl, hr_eq] at hm
    have hbr_n : K_den ≤ M_hi ^ D * ((P_n * Q_ev) * Q_m) := by
      have hm := Nat.mul_le_mul_right Q_ev (Nat.mul_le_mul hPm_Pn hQn_Qm)
      have hl : (P_m * Q_n) * Q_ev = K_den := by
        dsimp only [K_den]; rw [Nat.mul_assoc P_m Q_n Q_ev, Nat.mul_comm Q_n Q_ev]
      have hr_eq : ((M_hi ^ dP * P_n) * (M_hi ^ dQ * Q_m)) * Q_ev =
          M_hi ^ D * ((P_n * Q_ev) * Q_m) := by
        dsimp only [D]
        rw [Nat.pow_add M_hi dP dQ, ← Nat.mul_assoc (M_hi ^ dP * P_n),
            Nat.mul_assoc (M_hi ^ dP) P_n (M_hi ^ dQ),
            Nat.mul_comm P_n (M_hi ^ dQ),
            ← Nat.mul_assoc (M_hi ^ dP) (M_hi ^ dQ) P_n,
            Nat.mul_assoc (M_hi ^ dP * M_hi ^ dQ) P_n Q_m,
            Nat.mul_assoc (M_hi ^ dP * M_hi ^ dQ),
            Nat.mul_assoc P_n Q_m Q_ev, Nat.mul_comm Q_m Q_ev, ← Nat.mul_assoc P_n Q_ev Q_m]
      rwa [hl, hr_eq] at hm
    let B_actual := aE * bO * M_hi ^ D
    have hBact_pos : B_actual ≥ 1 :=
      Nat.mul_le_mul (Nat.mul_le_mul haE_pos hbO_pos) (nat_pow_pos_of_pos M_hi hMhi_ge1 D)
    have hBact_le : B_actual ≤ B_eff := by
      dsimp only [B_actual, B_eff, B_mode]
      exact Nat.mul_le_mul_right (M_hi ^ D) (Nat.mul_le_mul_left aE hbO_le)
    have hr_ge_act : r ≥ (B_actual + bE + 1) * (D * C + 1) :=
      Nat.le_trans (Nat.mul_le_mul_right (D * C + 1) (by omega)) hr_ge
    have ht1 : B_actual * r ^ D * K_den ≤
        (M_hi ^ D * (r + C) ^ D) * (aE * bO * ((P_ev * Q_n) * Q_m)) := by
      have hm := Nat.mul_le_mul_left B_actual hbr_ev
      dsimp only [B_actual] at hm ⊢
      calc
        aE * bO * M_hi ^ D * r ^ D * K_den
            = aE * bO * M_hi ^ D * (r ^ D * K_den) := Nat.mul_assoc _ _ _
        _ ≤ aE * bO * M_hi ^ D * ((r + C) ^ D * ((P_ev * Q_n) * Q_m)) := hm
        _ = (M_hi ^ D * (r + C) ^ D) * (aE * bO * ((P_ev * Q_n) * Q_m)) := by
              generalize aE * bO = AB, M_hi ^ D = MH, (r + C) ^ D = RC, (P_ev * Q_n) * Q_m = X1
              rw [← Nat.mul_assoc (AB * MH) RC X1, Nat.mul_assoc AB MH RC,
                  Nat.mul_comm AB (MH * RC), Nat.mul_assoc (MH * RC) AB X1]
    have ht2 : bE * r ^ D * K_den ≤
        (M_hi ^ D * (r + C) ^ D) * (bE * ((P_n * Q_ev) * Q_m)) := by
      calc
        bE * r ^ D * K_den
            ≤ bE * (r + C) ^ D * K_den :=
              Nat.mul_le_mul_right K_den (Nat.mul_le_mul_left bE hrD_le)
        _ ≤ bE * (r + C) ^ D * (M_hi ^ D * ((P_n * Q_ev) * Q_m)) :=
              Nat.mul_le_mul_left (bE * (r + C) ^ D) hbr_n
        _ = (M_hi ^ D * (r + C) ^ D) * (bE * ((P_n * Q_ev) * Q_m)) := by
              generalize (r + C) ^ D = RC, M_hi ^ D = MH, (P_n * Q_ev) * Q_m = X2
              rw [← Nat.mul_assoc (bE * RC) MH X2, Nat.mul_assoc bE RC MH,
                  Nat.mul_comm RC MH, ← Nat.mul_assoc bE MH RC,
                  Nat.mul_comm bE MH, Nat.mul_assoc MH bE RC,
                  Nat.mul_comm bE RC, ← Nat.mul_assoc MH RC bE,
                  Nat.mul_assoc (MH * RC) bE X2]
    have hsum := Nat.add_le_add ht1 ht2
    rw [← Nat.add_mul (B_actual * r ^ D) (bE * r ^ D) K_den,
        ← Nat.add_mul B_actual bE (r ^ D),
        ← Nat.mul_add (M_hi ^ D * (r + C) ^ D)] at hsum
    have htot : ((B_actual + bE) * r ^ D) * K_den ≤ (B_actual * (r + C) ^ D) * K_den := by
      have hm := Nat.le_trans hsum (Nat.mul_le_mul_left (M_hi ^ D * (r + C) ^ D) hineq_simp)
      have hr_eq : (M_hi ^ D * (r + C) ^ D) * (aE * bO * K_den) =
          (B_actual * (r + C) ^ D) * K_den := by
        dsimp only [B_actual]
        generalize aE * bO = AB, M_hi ^ D = MH, (r + C) ^ D = RC
        rw [← Nat.mul_assoc (MH * RC) AB K_den, Nat.mul_comm (MH * RC) AB,
            ← Nat.mul_assoc AB MH RC]
      rwa [hr_eq] at hm
    have hle_b := nat_mul_le_cancel_right_w5 K_den _ _ hK_pos htot
    have hlt_b := bernoulli_nat_ratio_lt bE B_actual D C r hbE_pos hBact_pos hC_pos hr_ge_act
    omega

-- ----------------------------------------------------------------------------
-- Unconditional Closure of ALL `∀ Q ≥ 1` Stateful MSB, LSB, & Joint Raw-Counter
-- `OCN` `NatPoly2` / `NatPoly3` & Polynomial-`binBitLength` Preimage Weights
-- via Constructive Mod-`9` Synchronized Backward Collatz Branch-Descent
-- ----------------------------------------------------------------------------

/-- Canonical `Q = 2` asymmetric-slope zero-testing `OCN` (`ZPOS_ASYMMETRIC_SLOPE_Q2_OCN_MERSENNE_BYPASS`). -/
def asymSlopeQ2Zero : Fin 2 -> Bool -> Fin 2 × CounterOp :=
  fun q b =>
    match q.val, b with
    | 0, false => (⟨0, Nat.zero_lt_succ 1⟩, .stay)
    | 0, true => (⟨1, Nat.succ_lt_succ Nat.zero_lt_one⟩, .stay)
    | _, false => (⟨0, Nat.zero_lt_succ 1⟩, .inc)
    | _, true => (⟨1, Nat.succ_lt_succ Nat.zero_lt_one⟩, .stay)

def asymSlopeQ2Pos : Fin 2 -> Bool -> Fin 2 × CounterOp :=
  fun q b =>
    match q.val, b with
    | 0, false => (⟨0, Nat.zero_lt_succ 1⟩, .stay)
    | 0, true => (⟨0, Nat.zero_lt_succ 1⟩, .inc)
    | _, _ => (⟨1, Nat.succ_lt_succ Nat.zero_lt_one⟩, .stay)

private theorem add_succ_lt_axfree (a : Nat) : ∀ k : Nat, a < a + (k + 1)
  | 0 => Nat.lt_succ_self a
  | k + 1 => Nat.lt_trans (add_succ_lt_axfree a k) (Nat.lt_succ_self (a + (k + 1)))

/--
  Theorem W11.3a''' (`asymSlopeQ2_mersenne_bypass_and_zpos_refutation_cert`, `[]` axioms):
  Pure-Kernel Certificate for Asymmetric-Slope `Q = 2` `OCN` (`ZPOS_ASYMMETRIC_SLOPE_Q2_OCN_MERSENNE_BYPASS`):
  On `asymSlopeQ2` (`q0 = 0`), `w(n) = (c_MSB(n) + 1) / (binBitLength n)^2` strictly satisfies the
  cleared-denominator preimage inequality at Mersenne `k = 4` (`m = 47`, `2m = 94`, `nOdd = 31`:
  `7164 < 7350`, i.e., `199 / 1225 < 1 / 6`), demonstrating why single-family Mersenne arguments
  cannot refute asymmetric `(sl1 = 0, sl2 ≥ 1)` `OCN` weights — yet strictly violates preimage
  superharmonicity on `Z^+` at `m = 5` (`2m = 10`, `nOdd = 3`: `252 > 192`, i.e., `7 / 16 > 1 / 3`)!
-/
theorem asymSlopeQ2_mersenne_bypass_and_zpos_refutation_cert :
    let q0 : Fin 2 := ⟨0, Nat.zero_lt_succ 1⟩
    (runMSBOneCounterOCNAux asymSlopeQ2Zero asymSlopeQ2Pos q0 7 3).2 = 0 ∧
    (runMSBOneCounterOCNAux asymSlopeQ2Zero asymSlopeQ2Pos q0 7 5).2 = 2 ∧
    (runMSBOneCounterOCNAux asymSlopeQ2Zero asymSlopeQ2Pos q0 7 10).2 = 2 ∧
    (runMSBOneCounterOCNAux asymSlopeQ2Zero asymSlopeQ2Pos q0 7 31).2 = 0 ∧
    (runMSBOneCounterOCNAux asymSlopeQ2Zero asymSlopeQ2Pos q0 7 47).2 = 5 ∧
    (runMSBOneCounterOCNAux asymSlopeQ2Zero asymSlopeQ2Pos q0 7 94).2 = 5 ∧
    ((5 + 1) * 25 + (0 + 1) * 49) * 36 < (5 + 1) * (49 * 25) ∧
    (2 + 1) * (16 * 4) < ((2 + 1) * 4 + (0 + 1) * 16) * 9 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, add_succ_lt_axfree 7164 185, add_succ_lt_axfree 192 59⟩

theorem runMSBOneCounterOCN_counter_le_bitLength {Q : Nat}
    (dz dp : Fin Q -> Bool -> Fin Q × CounterOp) (q0 : Fin Q) (n : Nat) :
    (runMSBOneCounterOCN Q dz dp q0 n).2 ≤ binBitLength n := by
  have haux : ∀ (bd m : Nat), m ≤ bd ->
      (runMSBOneCounterOCN Q dz dp q0 m).2 ≤ binBitLength m := by
    intro bd; induction bd with
    | zero =>
      intro m hm
      have hm0 : m = 0 := by omega
      subst hm0; exact Nat.zero_le 0
    | succ bd' ih =>
      intro m hm
      by_cases hm0 : m = 0
      · subst hm0; exact Nat.zero_le 0
      · rw [runMSBOneCounterOCN_step_pos dz dp q0 m (by omega),
            binBitLength_step_pos m (by omega)]
        have hstep := stepOCN_counter_le_succ dz dp
          (runMSBOneCounterOCN Q dz dp q0 (m / 2)) (m % 2 == 1)
        have hih := ih (m / 2) (by omega)
        omega
  exact haux n n (Nat.le_refl n)

theorem runLSBOneCounterOCN_counter_le_bitLength {Q : Nat}
    (dz dp : Fin Q -> Bool -> Fin Q × CounterOp) (q0 : Fin Q) (n : Nat) :
    (runLSBOneCounterOCN Q dz dp q0 n).2 ≤ binBitLength n := by
  have haux : ∀ (bd m : Nat) (cfg : Fin Q × Nat), m ≤ bd ->
      (runLSBFromOCN dz dp m cfg).2 ≤ cfg.2 + binBitLength m := by
    intro bd; induction bd with
    | zero =>
      intro m cfg hm
      have hm0 : m = 0 := by omega
      subst hm0
      have hz0 : runLSBFromOCN dz dp 0 cfg = cfg := rfl
      have hbl0 : binBitLength 0 = 0 := rfl
      rw [hz0, hbl0]; omega
    | succ bd' ih =>
      intro m cfg hm
      by_cases hm0 : m = 0
      · subst hm0
        have hz0 : runLSBFromOCN dz dp 0 cfg = cfg := rfl
        have hbl0 : binBitLength 0 = 0 := rfl
        rw [hz0, hbl0]; omega
      · rw [runLSBFromOCN_step_pos dz dp m (by omega) cfg,
            binBitLength_step_pos m (by omega)]
        have hstep := stepOCN_counter_le_succ dz dp cfg (m % 2 == 1)
        have hih := ih (m / 2) (stepOCN dz dp cfg (m % 2 == 1)) (by omega)
        omega
  unfold runLSBOneCounterOCN
  simpa using haux n n (q0, 0) (Nat.le_refl n)

/-- Constructive shift `r ∈ {1..6}` mapping any `x` with `x % 3 ≠ 0` to `(2 ^ r * x) % 9 = 8`. -/
def mod9ShiftTo8 (x : Nat) : Nat :=
  match x % 9 with
  | 4 => 1
  | 2 => 2
  | 1 => 3
  | 5 => 4
  | 7 => 5
  | _ => 6

theorem mod9ShiftTo8_spec (x : Nat) (hx3 : x % 3 ≠ 0) :
    1 ≤ mod9ShiftTo8 x ∧ mod9ShiftTo8 x ≤ 6 ∧ (2 ^ (mod9ShiftTo8 x) * x) % 9 = 8 := by
  unfold mod9ShiftTo8
  have hr_lt : x % 9 < 9 := Nat.mod_lt x (by decide)
  have hr_m3 : (x % 9) % 3 ≠ 0 := by omega
  generalize hr_eq : x % 9 = r9 at hr_lt hr_m3
  rcases (show r9 = 1 ∨ r9 = 2 ∨ r9 = 4 ∨ r9 = 5 ∨ r9 = 7 ∨ r9 = 8 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, by decide, by rw [Nat.mul_mod, hr_eq]; decide⟩

/-- Constructive single-path backward Collatz branch step choosing the lighter preimage of `2 ^ r * x`. -/
def preimageBranchNext (wNum wDen : Nat -> Nat) (x : Nat) : Nat :=
  let r := mod9ShiftTo8 x
  let m := 2 ^ r * x
  let y0 := 2 * m
  let y1 := (2 * m - 1) / 3
  if 2 * wNum y0 * wDen m ≤ wNum m * wDen y0 then y0 else y1

def preimageBranchIter (wNum wDen : Nat -> Nat) : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => preimageBranchNext wNum wDen (preimageBranchIter wNum wDen k x)

private theorem preimageBranchNext_spec
    (wNum wDen : Nat -> Nat) (pTheta qTheta x : Nat)
    (hw : IsPositiveRationalPreimageWeight wNum wDen pTheta qTheta)
    (hx5 : x ≥ 5) (hx3 : x % 3 ≠ 0) :
    let x' := preimageBranchNext wNum wDen x
    x' ≥ 5 ∧ x' % 3 ≠ 0 ∧ x' ≤ 128 * x ∧ 2 * wNum x' * wDen x ≤ wNum x * wDen x' := by
  dsimp only
  rcases mod9ShiftTo8_spec x hx3 with ⟨hr1, hr6, hm9⟩
  let r := mod9ShiftTo8 x
  let m := 2 ^ r * x
  change m % 9 = 8 at hm9
  let y0 := 2 * m
  let y1 := (2 * m - 1) / 3
  have hp_lo : 2 ≤ 2 ^ r := by simpa using pow2_mono_nat hr1
  have hp_hi : 2 ^ r ≤ 64 := by simpa using pow2_mono_nat hr6
  have hm_ge10 : m ≥ 10 := by
    dsimp only [m]; have hm := Nat.mul_le_mul hp_lo hx5; omega
  have hm_le : m ≤ 64 * x := by
    dsimp only [m]; exact Nat.mul_le_mul_right x hp_hi
  have hm_m3 : m % 3 = 2 := by omega
  have hy0_ge5 : y0 ≥ 5 := by dsimp only [y0]; omega
  have hy0_m3 : y0 % 3 ≠ 0 := by dsimp only [y0]; omega
  have hy0_le : y0 ≤ 128 * x := by dsimp only [y0]; omega
  have hy1_eq : y1 = 6 * (m / 9) + 5 := by dsimp only [y1]; omega
  have hy1_ge5 : y1 ≥ 5 := by rw [hy1_eq]; omega
  have hy1_m3 : y1 % 3 ≠ 0 := by rw [hy1_eq]; omega
  have hy1_le : y1 ≤ 128 * x := by dsimp only [y1]; omega
  -- Even-halving chain `wNum (2 ^ r * x) * wDen x ≤ wNum x * wDen (2 ^ r * x)`:
  have hpow2_le : ∀ d : Nat,
      wNum (2 ^ d * x) * wDen x ≤ wNum x * wDen (2 ^ d * x) := by
    intro d; induction d with
    | zero => simp
    | succ d' ih =>
      have hpos_d : 2 ^ d' * x ≥ 3 := by
        have hm1 := Nat.mul_le_mul (pow2_pos_nat d') hx5; omega
      have hmul : 2 ^ (d' + 1) * x = 2 * (2 ^ d' * x) := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ d') 2, Nat.mul_assoc]
      have hs := preimage_rational_forward_step_laws wNum wDen pTheta qTheta
        (2 * (2 ^ d' * x)) hw (by omega)
        (by rw [collatzStep_double_pos (2 ^ d' * x)]; omega)
      have h12 : wNum (2 * (2 ^ d' * x)) * wDen (2 ^ d' * x) ≤
          wNum (2 ^ d' * x) * wDen (2 * (2 ^ d' * x)) := by
        simpa [collatzStep_double_pos (2 ^ d' * x)] using hs.2.1
      rw [hmul]
      exact rat_le_trans_pos_w5 _ _ (wNum (2 ^ d' * x)) (wDen (2 ^ d' * x)) _ _
        (hw.2.2.1 (2 ^ d' * x) hpos_d).2 h12 ih
  have hm_le_x : wNum m * wDen x ≤ wNum x * wDen m := hpow2_le r
  -- Branching inequality at `m`:
  have hpre := hw.2.2.2.2 m (by omega) hm_m3
  dsimp only at hpre
  have hbr : (wNum y0 * wDen y1 + wNum y1 * wDen y0) * wDen m ≤
      wNum m * (wDen y0 * wDen y1) :=
    nat_mul_le_cancel_left_w5 qTheta _ _
      (Nat.lt_of_lt_of_le hw.1 hw.2.1)
      (Nat.le_trans hpre (Nat.mul_le_mul_right _ hw.2.1))
  have hbm_pos : wDen m > 0 := (hw.2.2.1 m (by omega)).2
  have hb0_pos : wDen y0 > 0 := (hw.2.2.1 y0 (by omega)).2
  have hb1_pos : wDen y1 > 0 := (hw.2.2.1 y1 (by omega)).2
  -- Pigeonhole selection between `y0` and `y1`:
  have hchoice :
      let x' := preimageBranchNext wNum wDen x
      x' ≥ 5 ∧ x' % 3 ≠ 0 ∧ x' ≤ 128 * x ∧ 2 * wNum x' * wDen m ≤ wNum m * wDen x' := by
    unfold preimageBranchNext
    dsimp only
    change (if 2 * wNum y0 * wDen m ≤ wNum m * wDen y0 then y0 else y1) ≥ 5 ∧ _
    by_cases hcond : 2 * wNum y0 * wDen m ≤ wNum m * wDen y0
    · rw [ite_true_of_w10 hcond]
      exact ⟨hy0_ge5, hy0_m3, hy0_le, hcond⟩
    · rw [ite_false_of_w10 hcond]
      refine ⟨hy1_ge5, hy1_m3, hy1_le, ?_⟩
      by_cases hc1 : 2 * wNum y1 * wDen m ≤ wNum m * wDen y1
      · exact hc1
      · exfalso
        have hlt0 : wNum m * wDen y0 < 2 * wNum y0 * wDen m := by omega
        have hlt1 : wNum m * wDen y1 < 2 * wNum y1 * wDen m := by omega
        have hm0 := Nat.mul_lt_mul_of_pos_right hlt0 hb1_pos
        have hm1 := Nat.mul_lt_mul_of_pos_right hlt1 hb0_pos
        have hl0 : (wNum m * wDen y0) * wDen y1 = wNum m * (wDen y0 * wDen y1) :=
          Nat.mul_assoc _ _ _
        have hl1 : (wNum m * wDen y1) * wDen y0 = wNum m * (wDen y0 * wDen y1) := by
          rw [Nat.mul_assoc, Nat.mul_comm (wDen y1) (wDen y0)]
        have hr0 : (2 * wNum y0 * wDen m) * wDen y1 = 2 * ((wNum y0 * wDen y1) * wDen m) := by
          rw [Nat.mul_assoc 2 (wNum y0) (wDen m), Nat.mul_assoc 2,
              Nat.mul_assoc (wNum y0) (wDen m) (wDen y1),
              Nat.mul_comm (wDen m) (wDen y1), ← Nat.mul_assoc (wNum y0)]
        have hr1 : (2 * wNum y1 * wDen m) * wDen y0 = 2 * ((wNum y1 * wDen y0) * wDen m) := by
          rw [Nat.mul_assoc 2 (wNum y1) (wDen m), Nat.mul_assoc 2,
              Nat.mul_assoc (wNum y1) (wDen m) (wDen y0),
              Nat.mul_comm (wDen m) (wDen y0), ← Nat.mul_assoc (wNum y1)]
        rw [hl0, hr0] at hm0
        rw [hl1, hr1] at hm1
        rw [Nat.add_mul (wNum y0 * wDen y1) (wNum y1 * wDen y0) (wDen m)] at hbr
        omega
  rcases hchoice with ⟨hx'_ge5, hx'_m3, hx'_le, hstep_m⟩
  refine ⟨hx'_ge5, hx'_m3, hx'_le, ?_⟩
  exact rat_le_trans_pos_w5 (2 * wNum (preimageBranchNext wNum wDen x))
    (wDen (preimageBranchNext wNum wDen x)) (wNum m) (wDen m) (wNum x) (wDen x)
    hbm_pos hstep_m hm_le_x

private theorem preimageBranchIter_spec
    (wNum wDen : Nat -> Nat) (pTheta qTheta : Nat)
    (hw : IsPositiveRationalPreimageWeight wNum wDen pTheta qTheta) :
    ∀ k : Nat,
      let xk := preimageBranchIter wNum wDen k 5
      xk ≥ 5 ∧ xk % 3 ≠ 0 ∧ xk < 2 ^ (7 * k + 3) ∧
      2 ^ k * wNum xk * wDen 5 ≤ wNum 5 * wDen xk
  | 0 => by
    simp only [preimageBranchIter, Nat.pow_zero, Nat.one_mul]
    exact ⟨by decide, by decide, by decide, Nat.le_refl _⟩
  | k + 1 => by
    rcases preimageBranchIter_spec wNum wDen pTheta qTheta hw k with
      ⟨hxk5, hxk3, hxk_lt, hxk_rat⟩
    let xk := preimageBranchIter wNum wDen k 5
    change xk ≥ 5 at hxk5
    change xk % 3 ≠ 0 at hxk3
    change xk < 2 ^ (7 * k + 3) at hxk_lt
    change 2 ^ k * wNum xk * wDen 5 ≤ wNum 5 * wDen xk at hxk_rat
    rcases preimageBranchNext_spec wNum wDen pTheta qTheta xk hw hxk5 hxk3 with
      ⟨hn5, hn3, hn_le, hn_rat⟩
    let xn := preimageBranchNext wNum wDen xk
    have hxn_lt : xn < 2 ^ (7 * (k + 1) + 3) := by
      have hp7 : 2 ^ (7 * (k + 1) + 3) = 128 * 2 ^ (7 * k + 3) := by
        rw [show 7 * (k + 1) + 3 = (7 * k + 3) + 7 by omega,
            Nat.pow_add 2 (7 * k + 3) 7, Nat.mul_comm _ (2 ^ 7)]
      rw [hp7]; omega
    have hbxk_pos : wDen xk > 0 := (hw.2.2.1 xk (by omega)).2
    have hstep_scaled : (2 ^ (k + 1) * wNum xn) * wDen xk ≤ (2 ^ k * wNum xk) * wDen xn := by
      have hm := Nat.mul_le_mul_left (2 ^ k) hn_rat
      have hl : 2 ^ k * (2 * wNum xn * wDen xk) = (2 ^ (k + 1) * wNum xn) * wDen xk := by
        rw [Nat.pow_succ 2 k, Nat.mul_assoc (2 ^ k) 2 (wNum xn),
            Nat.mul_assoc (2 ^ k) (2 * wNum xn) (wDen xk)]
      have hr : 2 ^ k * (wNum xk * wDen xn) = (2 ^ k * wNum xk) * wDen xn :=
        (Nat.mul_assoc _ _ _).symm
      rwa [hl, hr] at hm
    have htot := rat_le_trans_pos_w5 (2 ^ (k + 1) * wNum xn) (wDen xn)
      (2 ^ k * wNum xk) (wDen xk) (wNum 5) (wDen 5) hbxk_pos hstep_scaled hxk_rat
    exact ⟨hn5, hn3, hxn_lt, htot⟩

private theorem id_lt_pow2_w11 : ∀ n : Nat, n < 2 ^ n
  | 0 => by decide
  | n + 1 => by
    have ih := id_lt_pow2_w11 n
    have hp := pow2_pos_nat n
    rw [Nat.pow_succ]
    omega

private theorem pow_mono_base_w11 (a b : Nat) (hab : a ≤ b) : ∀ e : Nat, a ^ e ≤ b ^ e
  | 0 => Nat.le_refl 1
  | e + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ]
    exact Nat.mul_le_mul (pow_mono_base_w11 a b hab e) hab

private theorem exists_pow2_gt_const_mul_bitlen_pow (C D : Nat) :
    ∃ k : Nat, C * (7 * k + 3) ^ D < 2 ^ k := by
  let m := C + 3 * D + 5
  let t := m + m
  let k := 2 ^ t
  refine ⟨k, ?_⟩
  have hm_ge5 : m ≥ 5 := by dsimp only [m]; omega
  have hk_pos : k ≥ 1 := pow2_pos_nat t
  have hlin_lt : 7 * k + 3 < 2 ^ (t + 4) := by
    have hp4 : 2 ^ (t + 4) = k * 16 := by rw [Nat.pow_add 2 t 4]
    rw [hp4]; omega
  have hpow_le : (7 * k + 3) ^ D ≤ 2 ^ ((t + 4) * D) := by
    have hm1 := pow_mono_base_w11 (7 * k + 3) (2 ^ (t + 4)) (Nat.le_of_lt hlin_lt) D
    rwa [← Nat.pow_mul 2 (t + 4) D] at hm1
  have hC_lt : C + 1 ≤ 2 ^ C := id_lt_pow2_w11 C
  have hbase_pos : (7 * k + 3) ^ D ≥ 1 := nat_pow_pos_of_pos (7 * k + 3) (by omega) D
  have hprod_lt : C * (7 * k + 3) ^ D < 2 ^ (C + (t + 4) * D) := by
    have h1 : C * (7 * k + 3) ^ D < (C + 1) * (7 * k + 3) ^ D := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    have h2 : (C + 1) * (7 * k + 3) ^ D ≤ 2 ^ C * 2 ^ ((t + 4) * D) :=
      Nat.mul_le_mul hC_lt hpow_le
    rw [← Nat.pow_add 2 C ((t + 4) * D)] at h2
    exact Nat.lt_of_lt_of_le h1 h2
  have hexp_le : C + (t + 4) * D ≤ k := by
    have ht4 : t + 4 ≤ 3 * m := by dsimp only [t]; omega
    have hmD : (t + 4) * D ≤ m * (3 * D) := by
      have hm1 := Nat.mul_le_mul_right D ht4
      rwa [Nat.mul_comm 3 m, Nat.mul_assoc m 3 D] at hm1
    have hC_m : C ≤ m * 1 := by dsimp only [m]; omega
    have hsum_mm : C + (t + 4) * D ≤ m * m := by
      have h1 : C + (t + 4) * D ≤ m * (1 + 3 * D) := by
        rw [Nat.mul_add m 1 (3 * D)]; omega
      have h2 : m * (1 + 3 * D) ≤ m * m :=
        Nat.mul_le_mul_left m (by dsimp only [m]; omega)
      exact Nat.le_trans h1 h2
    have hm_pow : m ≤ 2 ^ m := Nat.le_of_lt (id_lt_pow2_w11 m)
    have hmm_k : m * m ≤ k := by
      have hm2 := Nat.mul_le_mul hm_pow hm_pow
      rwa [← Nat.pow_add 2 m m] at hm2
    exact Nat.le_trans hsum_mm hmm_k
  exact Nat.lt_of_lt_of_le hprod_lt (pow2_mono_nat hexp_le)

/--
  Theorem W11.3a'''' (`poly_bitlength_denominator_preimage_impossibility`, choice-free `zero custom axioms`):
  Universal Polynomial-`binBitLength` Denominator Preimage Barrier (`Branch P1.2`):
  For ANY `wNum, wDen : Nat -> Nat` and ANY `C_den, D_den : Nat`, if `wDen n ≤ C_den * (binBitLength n) ^ D_den`
  for all `n ≥ 5`, then NO `(pTheta, qTheta)` can make `(wNum, wDen)` satisfy `IsPositiveRationalPreimageWeight`!
-/
theorem poly_bitlength_denominator_preimage_impossibility
    (wNum wDen : Nat -> Nat) (C_den D_den pTheta qTheta : Nat)
    (hden_bound : ∀ n : Nat, n ≥ 5 -> wDen n ≤ C_den * (binBitLength n) ^ D_den) :
    ¬ IsPositiveRationalPreimageWeight wNum wDen pTheta qTheta := by
  intro hw
  rcases exists_pow2_gt_const_mul_bitlen_pow (wNum 5 * C_den) D_den with ⟨k, hgt⟩
  rcases preimageBranchIter_spec wNum wDen pTheta qTheta hw k with
    ⟨hxk5, _, hxk_lt, hxk_rat⟩
  let xk := preimageBranchIter wNum wDen k 5
  change xk ≥ 5 at hxk5
  change xk < 2 ^ (7 * k + 3) at hxk_lt
  change 2 ^ k * wNum xk * wDen 5 ≤ wNum 5 * wDen xk at hxk_rat
  have hwn_pos : wNum xk ≥ 1 := (hw.2.2.1 xk (by omega)).1
  have hwd5_pos : wDen 5 ≥ 1 := (hw.2.2.1 5 (by decide)).2
  have hlhs_ge : 2 ^ k ≤ 2 ^ k * wNum xk * wDen 5 := by
    have hm1 : 2 ^ k * 1 ≤ 2 ^ k * wNum xk := Nat.mul_le_mul_left (2 ^ k) hwn_pos
    have hm2 : (2 ^ k * wNum xk) * 1 ≤ (2 ^ k * wNum xk) * wDen 5 :=
      Nat.mul_le_mul_left (2 ^ k * wNum xk) hwd5_pos
    omega
  have hbl_xk : binBitLength xk ≤ 7 * k + 3 := by
    have hpred := (binBitLength_pow2_and_pred (7 * k + 2)).2
    have hmono := binBitLength_mono xk (2 ^ ((7 * k + 2) + 1) - 1)
      (by rw [show (7 * k + 2) + 1 = 7 * k + 3 by omega]; omega)
    omega
  have hden_xk : wDen xk ≤ C_den * (7 * k + 3) ^ D_den :=
    Nat.le_trans (hden_bound xk hxk5)
      (Nat.mul_le_mul_left C_den (pow_mono_base_w11 _ _ hbl_xk D_den))
  have hrhs_le : wNum 5 * wDen xk ≤ (wNum 5 * C_den) * (7 * k + 3) ^ D_den := by
    have hm := Nat.mul_le_mul_left (wNum 5) hden_xk
    rwa [← Nat.mul_assoc (wNum 5) C_den] at hm
  omega

private theorem asymSlopeQ2_all_mersenne_bypass :
    let q0 : Fin 2 := ⟨0, Nat.zero_lt_succ 1⟩
    ∀ k : Nat, k ≥ 4 ->
      let ms1 := 3 * 2 ^ k - 1
      let evs1 := 2 * ms1
      let ns1 := 2 ^ (k + 1) - 1
      let cm := (runMSBOneCounterOCN 2 asymSlopeQ2Zero asymSlopeQ2Pos q0 ms1).2
      let cev := (runMSBOneCounterOCN 2 asymSlopeQ2Zero asymSlopeQ2Pos q0 evs1).2
      let cn := (runMSBOneCounterOCN 2 asymSlopeQ2Zero asymSlopeQ2Pos q0 ns1).2
      cn = 0 ∧ cm = k + 1 ∧ cev = k + 1 ∧
      ((cev + 1) * (binBitLength ns1) ^ 2 + (cn + 1) * (binBitLength evs1) ^ 2) *
        (binBitLength ms1) ^ 2 <
        (cm + 1) * ((binBitLength evs1) ^ 2 * (binBitLength ns1) ^ 2) := by
  dsimp only
  let q0 : Fin 2 := ⟨0, Nat.zero_lt_succ 1⟩
  let q1 : Fin 2 := ⟨1, Nat.succ_lt_succ Nat.zero_lt_one⟩
  have hrun1 : runMSBOneCounterOCN 2 asymSlopeQ2Zero asymSlopeQ2Pos q0 1 = (q1, 0) := by
    rw [runMSBOneCounterOCN_eq_log_fuel asymSlopeQ2Zero asymSlopeQ2Pos q0 1 1 (by decide)]
    rfl
  have hrun2 : runMSBOneCounterOCN 2 asymSlopeQ2Zero asymSlopeQ2Pos q0 2 = (q0, 1) := by
    rw [runMSBOneCounterOCN_eq_log_fuel asymSlopeQ2Zero asymSlopeQ2Pos q0 2 2 (by decide)]
    rfl
  have hiter_q1 : ∀ t : Nat, iterOCN1 asymSlopeQ2Zero asymSlopeQ2Pos t (q1, 0) = (q1, 0) := by
    intro t; induction t with
    | zero => rfl
    | succ t' ih => simp only [iterOCN1, ih]; rfl
  have hiter_q0 : ∀ t : Nat, iterOCN1 asymSlopeQ2Zero asymSlopeQ2Pos t (q0, 1) = (q0, t + 1) := by
    intro t; induction t with
    | zero => rfl
    | succ t' ih =>
      simp only [iterOCN1, ih]
      unfold stepOCN asymSlopeQ2Pos applyCounterOp
      have hnz : ¬ (t' + 1 = 0) := by omega
      rw [ite_false_of_w10 hnz]; rfl
  intro k hk4
  let ms1 := 3 * 2 ^ k - 1
  let evs1 := 2 * ms1
  let ns1 := 2 ^ (k + 1) - 1
  have hp2k_ge4 : 2 ^ k ≥ 4 := by simpa using pow2_mono_nat (by omega : 2 ≤ k)
  rcases ripple_carry_alternating_cascade_and_mersenne_triples.2.2 (k + 1) (by omega) with
    ⟨_, _, _, _, _, hbl_n, hbl_m, hbl_ev⟩
  have hm_simp : 3 * 2 ^ (k + 1 - 1) - 1 = ms1 := by rw [Nat.add_sub_cancel]
  rw [hm_simp] at hbl_m hbl_ev
  have hms1_dec : ms1 = 2 ^ k * 2 + (2 ^ k - 1) := by
    change 3 * 2 ^ k - 1 = 2 ^ k * 2 + (2 ^ k - 1)
    have hp := pow2_pos_nat k; generalize 2 ^ k = p2 at hp ⊢; omega
  have hns1_dec : ns1 = 2 ^ k * 1 + (2 ^ k - 1) := by
    change 2 ^ (k + 1) - 1 = 2 ^ k * 1 + (2 ^ k - 1)
    rw [Nat.pow_succ 2 k]; have hp := pow2_pos_nat k; generalize 2 ^ k = p2 at hp ⊢; omega
  have hcfg_ms1 : runMSBOneCounterOCN 2 asymSlopeQ2Zero asymSlopeQ2Pos q0 ms1 = (q0, k + 1) := by
    rw [hms1_dec, runMSBOneCounterOCN_mersenne_tail asymSlopeQ2Zero asymSlopeQ2Pos q0 2 (by decide) k,
        hrun2, hiter_q0 k]
  have hcfg_ns1 : runMSBOneCounterOCN 2 asymSlopeQ2Zero asymSlopeQ2Pos q0 ns1 = (q1, 0) := by
    rw [hns1_dec, runMSBOneCounterOCN_mersenne_tail asymSlopeQ2Zero asymSlopeQ2Pos q0 1 (by decide) k,
        hrun1, hiter_q1 k]
  have hcfg_evs1 : runMSBOneCounterOCN 2 asymSlopeQ2Zero asymSlopeQ2Pos q0 evs1 = (q0, k + 1) := by
    dsimp only [evs1]
    rw [runMSBOneCounterOCN_step_pos asymSlopeQ2Zero asymSlopeQ2Pos q0 (2 * ms1) (by omega),
        show ((2 * ms1) % 2 == 1) = false by rw [Nat.mul_mod_right]; rfl,
        show (2 * ms1) / 2 = ms1 by omega,
        hcfg_ms1]
    unfold stepOCN asymSlopeQ2Pos applyCounterOp
    have hnz : ¬ (k + 1 = 0) := by omega
    rw [ite_false_of_w10 hnz]; rfl
  change (runMSBOneCounterOCN 2 asymSlopeQ2Zero asymSlopeQ2Pos q0 ns1).2 = 0 ∧ _
  rw [hcfg_ns1, hcfg_ms1, hcfg_evs1, hbl_n, hbl_m, hbl_ev]
  dsimp only
  refine ⟨rfl, rfl, rfl, ?_⟩
  let u := k + 1
  have hu5 : u ≥ 5 := by dsimp only [u]; omega
  change ((u + 1) * u ^ 2 + 1 * (u + 2) ^ 2) * (u + 1) ^ 2 <
    (u + 1) * ((u + 2) ^ 2 * u ^ 2)
  have hsq : ∀ z : Nat, z ^ 2 = z * z := fun z => by rw [Nat.pow_succ, Nat.pow_one]
  rw [hsq u, hsq (u + 2), hsq (u + 1), Nat.one_mul]
  let A := u * (u + 2)
  have hA_ge35 : A ≥ 35 := by
    dsimp only [A]
    have hm : 5 * 7 ≤ u * (u + 2) := Nat.mul_le_mul hu5 (by omega)
    omega
  have hu1_sq : (u + 1) * (u + 1) = A + 1 := by
    dsimp only [A]
    rw [Nat.add_mul u 1 (u + 1), Nat.one_mul, Nat.mul_add u u 1,
        Nat.mul_add u u 2, Nat.mul_one]
    omega
  have hinner_lhs : (u + 1) * (u * u) + (u + 2) * (u + 2) = u * A + 4 * (u + 1) := by
    dsimp only [A]
    rw [Nat.add_mul u 1 (u * u), Nat.one_mul,
        Nat.add_mul u 2 (u + 2), Nat.mul_add u u 2, Nat.mul_add 2 u 2,
        Nat.mul_add u (u * u) (u * 2), Nat.mul_comm 2 u, ← Nat.mul_assoc u u 2,
        Nat.mul_add 4 u 1]
    generalize u * (u * u) = U3, u * u = U2
    omega
  have hlhs_core : ((u + 1) * (u * u) + (u + 2) * (u + 2)) * (u + 1) =
      u * (u + 1) * A + (4 * A + 4) := by
    rw [hinner_lhs, Nat.add_mul (u * A) (4 * (u + 1)) (u + 1),
        Nat.mul_assoc u A (u + 1), Nat.mul_comm A (u + 1), ← Nat.mul_assoc u (u + 1) A,
        Nat.mul_assoc 4 (u + 1) (u + 1), hu1_sq, Nat.mul_add 4 A 1]
  have hrhs_core : ((u + 2) * (u + 2)) * (u * u) = u * (u + 1) * A + u * A := by
    have hsq_A : ((u + 2) * (u + 2)) * (u * u) = A * A := by
      dsimp only [A]
      calc
        ((u + 2) * (u + 2)) * (u * u)
            = (u + 2) * ((u + 2) * (u * u)) := Nat.mul_assoc _ _ _
        _ = (u + 2) * (((u + 2) * u) * u) := by rw [Nat.mul_assoc (u + 2) u u]
        _ = (u + 2) * ((u * (u + 2)) * u) := by rw [Nat.mul_comm (u + 2) u]
        _ = (u + 2) * (u * (u * (u + 2))) := by rw [Nat.mul_comm (u * (u + 2)) u]
        _ = ((u + 2) * u) * (u * (u + 2)) := (Nat.mul_assoc _ _ _).symm
        _ = (u * (u + 2)) * (u * (u + 2)) := by rw [Nat.mul_comm (u + 2) u]
    have hA_split : A = u * (u + 1) + u := by
      dsimp only [A]; rw [Nat.mul_add u u 2, Nat.mul_add u u 1, Nat.mul_one]; omega
    rw [hsq_A]
    conv => lhs; rw [hA_split]
    exact Nat.add_mul (u * (u + 1)) u A
  have h5A_le : 5 * A ≤ u * A := Nat.mul_le_mul_right A hu5
  have hcore_lt : ((u + 1) * (u * u) + (u + 2) * (u + 2)) * (u + 1) <
      ((u + 2) * (u + 2)) * (u * u) := by
    rw [hlhs_core, hrhs_core]; omega
  have hmul_u1 := Nat.mul_lt_mul_of_pos_right hcore_lt (by omega : u + 1 > 0)
  rwa [Nat.mul_assoc ((u + 1) * (u * u) + (u + 2) * (u + 2)) (u + 1) (u + 1),
       Nat.mul_comm (((u + 2) * (u + 2)) * (u * u)) (u + 1)] at hmul_u1

/--
  Theorem W11.3a''''' (`unconditional_all_ocn_raw_counter_and_poly_bitlength_preimage_impossibility`,
  choice-free `zero custom axioms`):
  Complete Unconditional Closure of ALL `∀ Q ≥ 1` Stateful MSB, LSB, & Joint `MSB + LSB` Zero-Testing
  `1`-Counter Pushdown (`OCN`) `NatPoly2` / `NatPoly3` & Polynomial-`binBitLength` Preimage Weights
  (Zero `_hinc0`/`_hinc1` Sign-Uniformity AND Zero Slope-Positivity or Slope-Equality Hypotheses!
  `Branch P1.2`, `W11_H1`, `ZPOS_ASYMMETRIC_SLOPE_Q2_OCN_MERSENNE_BYPASS`):
  1. **Universal Polynomial-`binBitLength` Denominator Preimage Barrier**:
     NO positive rational weight `wNum(n) / wDen(n)` (`θ ≤ 1`) satisfying `wDen n ≤ C_den * (binBitLength n) ^ D_den`
     (`∀ n ≥ 5`) can exist on `Z^+`!
  2. **Unconditional All-`Q` (`∀ Q ≥ 1`) Stateful MSB `1`-Counter `OCN` Raw-Counter `NatPoly2` Impossibility**:
     Closes ALL asymmetric zero-vs-positive slope (`sl = 0` vs `sl ≥ 1`), bounded, and mixed-sign MSB
     `OCN` `NatPoly2((runMSBOneCounterOCN Q dz dp q0 n).2, binBitLength n)` preimage weights unconditionally!
  3. **Unconditional All-`Q` (`∀ Q ≥ 1`) Stateful LSB `1`-Counter `OCN` Raw-Counter `NatPoly2` Impossibility**:
     Closes ALL unequal-slope, zero-slope, bounded, and mixed-sign LSB `OCN`
     `NatPoly2((runLSBOneCounterOCN Q dz dp q0 n).2, binBitLength n)` preimage weights unconditionally!
  4. **Unconditional All-`Q_L, Q_M` (`∀ Q_L, Q_M ≥ 1`) Joint Mode-Weighted + Dual-Raw-Counter `NatPoly3` Impossibility**:
     Closes ALL joint `fNum(modeL, modeM) * evalNatPoly3 pTerms3 c_LSB(n) c_MSB(n) (binBitLength n) /
     (fDen(modeL, modeM) * evalNatPoly3 qTerms3 c_LSB(n) c_MSB(n) (binBitLength n))` preimage weights!
  5. **Universal `∀ k ≥ 4` Mersenne-Family Bypass on Asymmetric-Slope `Q = 2` `asymSlopeQ2`**:
     Proves `c_MSB(2^(k+1) - 1) = 0` (`sl1 = 0`) and `c_MSB(3*2^k - 1) = c_MSB(6*2^k - 2) = k + 1`
     (`sl2 ≥ 1`), so `w(n) = (c_MSB(n) + 1) / (binBitLength n)^2` strictly satisfies `w(2*ms1) + w(ns1) < w(ms1)`
     across EVERY `k ≥ 4` Mersenne triple — proving why constructive Mod-`9` synchronized backward
     branch-descent (`2^k` vs `(7k + 3)^D`) is essential to close asymmetric-slope raw-counter `OCN` weights!
-/
theorem unconditional_all_ocn_raw_counter_and_poly_bitlength_preimage_impossibility :
    -- 1. Universal polynomial-in-`binBitLength` denominator barrier:
    (∀ (wNum wDen : Nat -> Nat) (C_den D_den pTheta qTheta : Nat),
      (∀ n : Nat, n ≥ 5 -> wDen n ≤ C_den * (binBitLength n) ^ D_den) ->
      ¬ IsPositiveRationalPreimageWeight wNum wDen pTheta qTheta) ∧
    -- 2. Unconditional `∀ Q ≥ 1` stateful MSB raw-counter `OCN` `NatPoly2` impossibility:
    (∀ (Q : Nat) (_hQ : Q ≥ 1)
       (dz dp : Fin Q -> Bool -> Fin Q × CounterOp) (q0 : Fin Q)
       (pTerms qTerms : NatPoly2) (pTheta qTheta : Nat),
      ¬ IsPositiveRationalPreimageWeight
          (fun n => evalNatPoly2 pTerms (runMSBOneCounterOCN Q dz dp q0 n).2 (binBitLength n))
          (fun n => evalNatPoly2 qTerms (runMSBOneCounterOCN Q dz dp q0 n).2 (binBitLength n))
          pTheta qTheta) ∧
    -- 3. Unconditional `∀ Q ≥ 1` stateful LSB raw-counter `OCN` `NatPoly2` impossibility:
    (∀ (Q : Nat) (_hQ : Q ≥ 1)
       (dz dp : Fin Q -> Bool -> Fin Q × CounterOp) (q0 : Fin Q)
       (pTerms qTerms : NatPoly2) (pTheta qTheta : Nat),
      ¬ IsPositiveRationalPreimageWeight
          (fun n => evalNatPoly2 pTerms (runLSBOneCounterOCN Q dz dp q0 n).2 (binBitLength n))
          (fun n => evalNatPoly2 qTerms (runLSBOneCounterOCN Q dz dp q0 n).2 (binBitLength n))
          pTheta qTheta) ∧
    -- 4. Unconditional `∀ Q_L, Q_M ≥ 1` joint mode-weighted + dual-raw-counter `NatPoly3` impossibility:
    (∀ (Q_L Q_M : Nat) (_hQL : Q_L ≥ 1) (_hQM : Q_M ≥ 1)
       (dzL dpL : Fin Q_L -> Bool -> Fin Q_L × CounterOp)
       (dzM dpM : Fin Q_M -> Bool -> Fin Q_M × CounterOp)
       (q0L : Fin Q_L) (q0M : Fin Q_M)
       (fNum fDen : (Fin Q_L × Bool) -> (Fin Q_M × Bool) -> Nat)
       (pTerms3 qTerms3 : NatPoly3) (pTheta qTheta : Nat),
      ¬ IsPositiveRationalPreimageWeight
          (fun n =>
            fNum (ocnObservableMode (runLSBOneCounterOCN Q_L dzL dpL q0L n))
                 (ocnObservableMode (runMSBOneCounterOCN Q_M dzM dpM q0M n)) *
            evalNatPoly3 pTerms3
              (runLSBOneCounterOCN Q_L dzL dpL q0L n).2
              (runMSBOneCounterOCN Q_M dzM dpM q0M n).2
              (binBitLength n))
          (fun n =>
            fDen (ocnObservableMode (runLSBOneCounterOCN Q_L dzL dpL q0L n))
                 (ocnObservableMode (runMSBOneCounterOCN Q_M dzM dpM q0M n)) *
            evalNatPoly3 qTerms3
              (runLSBOneCounterOCN Q_L dzL dpL q0L n).2
              (runMSBOneCounterOCN Q_M dzM dpM q0M n).2
              (binBitLength n))
          pTheta qTheta) ∧
    -- 5. Universal `∀ k ≥ 4` Mersenne-family bypass on asymmetric-slope `Q = 2` `asymSlopeQ2`:
    (let q0 : Fin 2 := ⟨0, Nat.zero_lt_succ 1⟩
     ∀ k : Nat, k ≥ 4 ->
       let ms1 := 3 * 2 ^ k - 1
       let evs1 := 2 * ms1
       let ns1 := 2 ^ (k + 1) - 1
       let cm := (runMSBOneCounterOCN 2 asymSlopeQ2Zero asymSlopeQ2Pos q0 ms1).2
       let cev := (runMSBOneCounterOCN 2 asymSlopeQ2Zero asymSlopeQ2Pos q0 evs1).2
       let cn := (runMSBOneCounterOCN 2 asymSlopeQ2Zero asymSlopeQ2Pos q0 ns1).2
       cn = 0 ∧ cm = k + 1 ∧ cev = k + 1 ∧
       ((cev + 1) * (binBitLength ns1) ^ 2 + (cn + 1) * (binBitLength evs1) ^ 2) *
         (binBitLength ms1) ^ 2 <
         (cm + 1) * ((binBitLength evs1) ^ 2 * (binBitLength ns1) ^ 2)) := by
  have hpoly3_ub : ∀ (F : NatPoly3) (x y z L : Nat),
      L ≥ 1 -> x ≤ L -> y ≤ L -> z ≤ L ->
      evalNatPoly3 F x y z ≤ evalNatPoly3 F 1 1 1 * L ^ (maxDegNatPoly3 F) := by
    intro F x y z L hL hx hy hz
    have hcr := evalNatPoly3_cross_ratio_bound F 1 L x y z 1 1 1 hL
      (by omega) (by omega) (by omega)
    rw [Nat.one_pow, Nat.one_mul, Nat.mul_comm (L ^ maxDegNatPoly3 F)] at hcr
    exact hcr
  have hpoly2_ub : ∀ (F : NatPoly2) (x L : Nat),
      L ≥ 1 -> x ≤ L ->
      evalNatPoly2 F x L ≤ evalNatPoly2 F 1 1 * L ^ (maxDegNatPoly2 F) := by
    intro F x L hL hx
    rcases evalNatPoly2_to_3_eq F x L with ⟨he1, hd1⟩
    rcases evalNatPoly2_to_3_eq F 1 1 with ⟨he2, _⟩
    rw [he1, he2, hd1]
    exact hpoly3_ub _ x L 1 L hL hx (Nat.le_refl L) hL
  have hbl_pos5 : ∀ n : Nat, n ≥ 5 -> binBitLength n ≥ 1 := by
    intro n hn5
    have h1 : binBitLength 1 = 1 := rfl
    have hm := binBitLength_mono 1 n (by omega)
    omega
  refine ⟨poly_bitlength_denominator_preimage_impossibility, ?_, ?_, ?_, asymSlopeQ2_all_mersenne_bypass⟩
  · -- Part 2: Unconditional MSB raw-counter `OCN` `NatPoly2`:
    intro Q _hQ dz dp q0 pTerms qTerms pTheta qTheta
    apply poly_bitlength_denominator_preimage_impossibility _ _
      (evalNatPoly2 qTerms 1 1) (maxDegNatPoly2 qTerms) pTheta qTheta
    intro n hn5
    exact hpoly2_ub qTerms _ (binBitLength n) (hbl_pos5 n hn5)
      (runMSBOneCounterOCN_counter_le_bitLength dz dp q0 n)
  · -- Part 3: Unconditional LSB raw-counter `OCN` `NatPoly2`:
    intro Q _hQ dz dp q0 pTerms qTerms pTheta qTheta
    apply poly_bitlength_denominator_preimage_impossibility _ _
      (evalNatPoly2 qTerms 1 1) (maxDegNatPoly2 qTerms) pTheta qTheta
    intro n hn5
    exact hpoly2_ub qTerms _ (binBitLength n) (hbl_pos5 n hn5)
      (runLSBOneCounterOCN_counter_le_bitLength dz dp q0 n)
  · -- Part 4: Unconditional joint mode-weighted + dual-raw-counter `NatPoly3`:
    intro Q_L Q_M _hQL _hQM dzL dpL dzM dpM q0L q0M fNum fDen pTerms3 qTerms3 pTheta qTheta
    let F_den := sumAllJointModes Q_L Q_M fDen Q_L (Nat.le_refl Q_L)
    apply poly_bitlength_denominator_preimage_impossibility _ _
      (F_den * evalNatPoly3 qTerms3 1 1 1) (maxDegNatPoly3 qTerms3) pTheta qTheta
    intro n hn5
    have hf_le : fDen (ocnObservableMode (runLSBOneCounterOCN Q_L dzL dpL q0L n))
                      (ocnObservableMode (runMSBOneCounterOCN Q_M dzM dpM q0M n)) ≤ F_den :=
      le_sumAllJointModes Q_L Q_M fDen Q_L (Nat.le_refl Q_L) _ _
        (ocnObservableMode (runLSBOneCounterOCN Q_L dzL dpL q0L n)).1.isLt
    have hp_le := hpoly3_ub qTerms3
      (runLSBOneCounterOCN Q_L dzL dpL q0L n).2
      (runMSBOneCounterOCN Q_M dzM dpM q0M n).2
      (binBitLength n) (binBitLength n) (hbl_pos5 n hn5)
      (runLSBOneCounterOCN_counter_le_bitLength dzL dpL q0L n)
      (runMSBOneCounterOCN_counter_le_bitLength dzM dpM q0M n)
      (Nat.le_refl _)
    have hm := Nat.mul_le_mul hf_le hp_le
    rwa [← Nat.mul_assoc F_den (evalNatPoly3 qTerms3 1 1 1)] at hm

private theorem w11_ocn_part4_raw_msb :
    ∀ (Q : Nat), Q ≥ 1 ->
      ∀ (dz dp : Fin Q -> Bool -> Fin Q × CounterOp) (q0 : Fin Q)
        (sl2 sl1 : Nat),
        sl2 ≥ 1 -> sl1 ≥ 1 ->
        let M1 := Q * (2 + Q + 1)
        let P1 := natFact M1
        let cfg_two := runMSBOneCounterOCN Q dz dp q0 2
        let cfg_one := runMSBOneCounterOCN Q dz dp q0 1
        (∀ m : Nat,
          (iterOCN1 dz dp (M1 + P1 * m) cfg_two).2 =
            m * sl2 + (iterOCN1 dz dp M1 cfg_two).2) ->
        (∀ m : Nat,
          (iterOCN1 dz dp (M1 + P1 * m) cfg_one).2 =
            m * sl1 + (iterOCN1 dz dp M1 cfg_one).2) ->
        ∀ (pTerms qTerms : NatPoly2) (pTheta qTheta : Nat),
          ¬ IsPositiveRationalPreimageWeight
            (fun n => evalNatPoly2 pTerms (runMSBOneCounterOCN Q dz dp q0 n).2 (binBitLength n))
            (fun n => evalNatPoly2 qTerms (runMSBOneCounterOCN Q dz dp q0 n).2 (binBitLength n))
            pTheta qTheta := by
  intro Q hQ dz dp q0 _sl2 _sl1 _hsl2 _hsl1
  dsimp only
  intro _hgrow2 _hgrow1 pTerms qTerms pTheta qTheta
  exact unconditional_all_ocn_raw_counter_and_poly_bitlength_preimage_impossibility.2.1
    Q hQ dz dp q0 pTerms qTerms pTheta qTheta

/--
  Theorem W11.3a (`general_mixed_sign_ocn_preimage_impossibility`, choice-free `zero custom axioms`):
  Closing ALL General Mixed-Sign `∀ Q ≥ 1` Zero-Testing `1`-Counter Pushdown (`OCN`) Preimage Weights
  (Zero `_hinc0` or `_hinc1` Sign-Uniformity Assumptions, `Branch P1.2`, `W11_H1`):
  1. **Universal Dual Unary `1`-Run Semilinear Dichotomy (`∀ Q ≥ 1`, Arbitrary Mixed-Sign Tables)**:
     For ANY `Q ≥ 1`, ANY `(deltaZero, deltaPos)` mixing `.inc`, `.dec`, and `.stay`, ANY `B : Nat`,
     and ANY `cfg0` with `cfg0.2 ≤ B`, setting `M_box := Q * (B + Q + 1)` and `P_ocn := natFact M_box`,
     there exists `slope1 : Nat` (`slope1 = 0` when bounded `< B + Q + 1` on `[0, M_box]`) such that
     for ALL `k ≥ M_box` and `m : Nat`:
       `(iterOCN1 deltaZero deltaPos (k + P_ocn * m) cfg0).1 = (iterOCN1 deltaZero deltaPos k cfg0).1 ∧
        (iterOCN1 deltaZero deltaPos (k + P_ocn * m) cfg0).2 = m * slope1 + (iterOCN1 deltaZero deltaPos k cfg0).2`!
  2. **Concrete `Q = 2` Mixed-Sign Witness (`ZPOS_MIXED_SIGN_Q2_OCN_PREIMAGE_COLLAPSE`)**:
     On `mixedSignQ2`, single-step `56` (`c = 2`) vs `224 = 4 * 56` (`c = 1`) separates `2`-step even
     padding, YET `8277 -> 12416` (`12416 % 3 = 2`, `(2 * 12416 - 1) / 3 = 8277`) collides identically
     with `4 * 12416 = 49664` at `(1, 0)`!
  3. **Unconditional Joint `MSB + LSB` Mixed-Sign Observable-Mode `NatPoly2` Impossibility (`∀ Q_L, Q_M ≥ 1`)**:
     For ALL state counts `Q_L ≥ 1, Q_M ≥ 1`, ALL mixed-sign LSB and MSB `OCN` transition tables
     `(dzL, dpL)` and `(dzM, dpM)` (with ZERO sign-uniformity assumptions!), ALL initial states
     `q0L, q0M`, ALL rational mode-weight tables `fNum, fDen`, ALL `pTerms, qTerms : NatPoly2`,
     and ALL `pTheta, qTheta : Nat`, NO weight
       `w(n) = (fNum (ocnObservableMode (runLSBOneCounterOCN Q_L dzL dpL q0L n))
                     (ocnObservableMode (runMSBOneCounterOCN Q_M dzM dpM q0M n)) *
                evalNatPoly2 pTerms (zeroBitCount n) (binBitLength n)) /
               (fDen (...) (...) * evalNatPoly2 qTerms (zeroBitCount n) (binBitLength n))`
     can satisfy `IsPositiveRationalPreimageWeight`!
  4. **Mixed-Sign Raw-Counter `NatPoly2(c(n), binBitLength n)` Impossibility Corollary (`∀ Q ≥ 1`)**:
     Direct corollary of `Theorem W11.3a'''''` (`unconditional_all_ocn_raw_counter_and_poly_bitlength_preimage_impossibility`),
     which refutes ALL `∀ Q ≥ 1` stateful MSB and LSB raw-counter `NatPoly2` weights unconditionally
     with ZERO slope-positivity or slope-equality hypotheses!
-/
theorem general_mixed_sign_ocn_preimage_impossibility :
    (∀ (Q : Nat), Q ≥ 1 ->
      ∀ (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp)
        (B : Nat) (cfg0 : Fin Q × Nat),
        cfg0.2 ≤ B ->
        let M_box := Q * (B + Q + 1)
        let P_ocn := natFact M_box
        ∃ slope1 : Nat,
          ((∀ t : Nat, t ≤ M_box -> (iterOCN1 deltaZero deltaPos t cfg0).2 < B + Q + 1) -> slope1 = 0) ∧
          (∀ (m k : Nat), k ≥ M_box ->
            (iterOCN1 deltaZero deltaPos (k + P_ocn * m) cfg0).1 =
              (iterOCN1 deltaZero deltaPos k cfg0).1 ∧
            (iterOCN1 deltaZero deltaPos (k + P_ocn * m) cfg0).2 =
              m * slope1 + (iterOCN1 deltaZero deltaPos k cfg0).2)) ∧
    (collatzStep 8277 = 12416 ∧ 12416 % 3 = 2 ∧ (2 * 12416 - 1) / 3 = 8277 ∧
     (runMSBOneCounterOCN 2 mixedSignQ2Zero mixedSignQ2Pos ⟨0, by decide⟩ 56).2 = 2 ∧
     (runMSBOneCounterOCN 2 mixedSignQ2Zero mixedSignQ2Pos ⟨0, by decide⟩ 224).2 = 1 ∧
     runMSBOneCounterOCN 2 mixedSignQ2Zero mixedSignQ2Pos ⟨0, by decide⟩ 12416 = (⟨1, by decide⟩, 0) ∧
     runMSBOneCounterOCN 2 mixedSignQ2Zero mixedSignQ2Pos ⟨0, by decide⟩ 49664 = (⟨1, by decide⟩, 0)) ∧
    (∀ (Q_L Q_M : Nat), Q_L ≥ 1 -> Q_M ≥ 1 ->
      ∀ (dzL dpL : Fin Q_L -> Bool -> Fin Q_L × CounterOp)
        (dzM dpM : Fin Q_M -> Bool -> Fin Q_M × CounterOp)
        (q0L : Fin Q_L) (q0M : Fin Q_M)
        (fNum fDen : (Fin Q_L × Bool) -> (Fin Q_M × Bool) -> Nat)
        (pTerms qTerms : NatPoly2) (pTheta qTheta : Nat),
        ¬ IsPositiveRationalPreimageWeight
          (fun n =>
            fNum (ocnObservableMode (runLSBOneCounterOCN Q_L dzL dpL q0L n))
                 (ocnObservableMode (runMSBOneCounterOCN Q_M dzM dpM q0M n)) *
            evalNatPoly2 pTerms (zeroBitCount n) (binBitLength n))
          (fun n =>
            fDen (ocnObservableMode (runLSBOneCounterOCN Q_L dzL dpL q0L n))
                 (ocnObservableMode (runMSBOneCounterOCN Q_M dzM dpM q0M n)) *
            evalNatPoly2 qTerms (zeroBitCount n) (binBitLength n))
          pTheta qTheta) ∧
    (∀ (Q : Nat), Q ≥ 1 ->
      ∀ (dz dp : Fin Q -> Bool -> Fin Q × CounterOp) (q0 : Fin Q)
        (sl2 sl1 : Nat),
        sl2 ≥ 1 -> sl1 ≥ 1 ->
        let M1 := Q * (2 + Q + 1)
        let P1 := natFact M1
        let cfg_two := runMSBOneCounterOCN Q dz dp q0 2
        let cfg_one := runMSBOneCounterOCN Q dz dp q0 1
        (∀ m : Nat,
          (iterOCN1 dz dp (M1 + P1 * m) cfg_two).2 =
            m * sl2 + (iterOCN1 dz dp M1 cfg_two).2) ->
        (∀ m : Nat,
          (iterOCN1 dz dp (M1 + P1 * m) cfg_one).2 =
            m * sl1 + (iterOCN1 dz dp M1 cfg_one).2) ->
        ∀ (pTerms qTerms : NatPoly2) (pTheta qTheta : Nat),
          ¬ IsPositiveRationalPreimageWeight
            (fun n => evalNatPoly2 pTerms (runMSBOneCounterOCN Q dz dp q0 n).2 (binBitLength n))
            (fun n => evalNatPoly2 qTerms (runMSBOneCounterOCN Q dz dp q0 n).2 (binBitLength n))
            pTheta qTheta) :=
  ⟨w11_ocn_part1_dual, w11_ocn_q2_witness_cert, w11_ocn_part3_joint_mode, w11_ocn_part4_raw_msb⟩

theorem runLSBFromOCN_mersenne_prefix {Q : Nat}
    (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp)
    (H : Nat) :
    ∀ (k : Nat) (cfg : Fin Q × Nat),
      runLSBFromOCN deltaZero deltaPos (2 ^ k * H + (2 ^ k - 1)) cfg =
        runLSBFromOCN deltaZero deltaPos H (iterOCN1 deltaZero deltaPos k cfg)
  | 0, cfg => by simp [iterOCN1]
  | k + 1, cfg => by
    have hp_pos : 2 ^ k ≥ 1 := pow2_pos_nat k
    have hval : 2 ^ (k + 1) * H + (2 ^ (k + 1) - 1) =
        2 * (2 ^ k * H + (2 ^ k - 1)) + 1 := by
      rw [Nat.pow_succ 2 k, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc 2 (2 ^ k) H]
      generalize 2 ^ k = P2 at hp_pos ⊢; omega
    let inner := 2 ^ k * H + (2 ^ k - 1)
    have hm2 : ((2 * inner + 1) % 2 == 1) = true := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left]; rfl
    have hdiv : (2 * inner + 1) / 2 = inner := by omega
    rw [hval, runLSBFromOCN_step_pos deltaZero deltaPos _ (by omega) cfg]
    change runLSBFromOCN deltaZero deltaPos ((2 * inner + 1) / 2)
      (stepOCN deltaZero deltaPos cfg ((2 * inner + 1) % 2 == 1)) = _
    rw [hm2, hdiv, runLSBFromOCN_mersenne_prefix deltaZero deltaPos H k]
    have h1k : iterOCN1 deltaZero deltaPos k (stepOCN deltaZero deltaPos cfg true) =
        iterOCN1 deltaZero deltaPos (k + 1) cfg := by
      rw [iterOCN1_eq_iterOCN0_flip, iterOCN1_eq_iterOCN0_flip]
      exact (iterOCN0_add (flipOCNTable deltaZero) (flipOCNTable deltaPos) k 1 cfg).symm
    rw [h1k]

/-- Canonical `Q = 2, |Γ| = 3` (`0 = Z_0, 1 = A, 2 = B`) multi-symbol context-free `PDA` step. -/
def stepPDAQ2G3 (cfg : Nat × List Nat) (b : Bool) : Nat × List Nat :=
  let q := cfg.1
  let stk := cfg.2
  let top := match stk with | g :: _ => g | [] => 0
  let q_flip := match q with | 0 => 1 | _ + 1 => 0
  match b with
  | true =>
    (q_flip, (match q with | 0 => 1 | _ + 1 => 2) :: stk)
  | false =>
    match top with
    | 0 => (q, 1 :: stk)
    | 1 => (q_flip, 2 :: stk.tail)
    | 2 => (q, match stk.tail with | [] => [0] | h :: t => h :: t)
    | _ + 3 => (q, 1 :: stk)

def runMSBPDAQ2G3Bits : List Bool -> (Nat × List Nat) -> (Nat × List Nat)
  | [], cfg => cfg
  | b :: bs, cfg => runMSBPDAQ2G3Bits bs (stepPDAQ2G3 cfg b)

/--
  Theorem W11.3a' (`canonical_pda_q2_g3_separates_and_collides_cert`, `[]` axioms):
  Pure-Kernel Certificate for Multi-Symbol Context-Free `PDA` (`Q = 2, |Γ| = 3`,
  `ZPOS_PDA_STACK_Q2_G3_COLLISION_8_VS_512`):
  Separates BOTH Wave 10's `56` vs `224` AND Wave 11's `12,416` vs `49,664` AND `8` vs `32`,
  yet unary `0`-run pushdown periodicity (`2^6 = 64`) locks the full configuration `(0, [1, 0])`
  identically on `8` (`[true, false, false, false]`) and `512` (`8 ++ [false]^6`)!
-/
theorem canonical_pda_q2_g3_separates_and_collides_cert :
    let b56 : List Bool := [true, true, true, false, false, false]
    let b224 : List Bool := b56 ++ [false, false]
    let b12416 : List Bool :=
      [true, true, false, false, false, false, true, false, false, false, false, false, false, false]
    let b49664 : List Bool := b12416 ++ [false, false]
    let b8 : List Bool := [true, false, false, false]
    let b32 : List Bool := b8 ++ [false, false]
    let b512 : List Bool := b8 ++ [false, false, false, false, false, false]
    runMSBPDAQ2G3Bits b56 (0, [0]) = (0, [1, 0]) ∧
    runMSBPDAQ2G3Bits b224 (0, [0]) = (1, [0]) ∧
    runMSBPDAQ2G3Bits b56 (0, [0]) ≠ runMSBPDAQ2G3Bits b224 (0, [0]) ∧
    runMSBPDAQ2G3Bits b12416 (0, [0]) = (0, [1, 0]) ∧
    runMSBPDAQ2G3Bits b49664 (0, [0]) = (1, [0]) ∧
    runMSBPDAQ2G3Bits b12416 (0, [0]) ≠ runMSBPDAQ2G3Bits b49664 (0, [0]) ∧
    runMSBPDAQ2G3Bits b8 (0, [0]) = (0, [1, 0]) ∧
    runMSBPDAQ2G3Bits b32 (0, [0]) = (1, [0]) ∧
    runMSBPDAQ2G3Bits b8 (0, [0]) = runMSBPDAQ2G3Bits b512 (0, [0]) :=
  ⟨rfl, rfl, fun h => nat_zero_ne_one_axfree (congrArg Prod.fst h),
   rfl, rfl, fun h => nat_zero_ne_one_axfree (congrArg Prod.fst h),
   rfl, rfl, rfl⟩

/--
  Theorem W11.3a'' (`lsb_mixed_sign_ocn_raw_counter_impossibility_and_bounded_pda_pumping`,
  `zero custom axioms`):
  1. **LSB Mixed-Sign Raw-Counter `OCN` `NatPoly2(c_LSB(n), binBitLength n)` Impossibility (`∀ Q ≥ 1`)**:
     Direct corollary of `unconditional_all_ocn_raw_counter_and_poly_bitlength_preimage_impossibility`
     (with ZERO `_hinc0` or `_hinc1` sign-uniformity assumptions).
  2. **General Bounded-Stack `PDA` / Bounded 2-Counter Unary `0`-Run Periodicity (`∀ S ≥ 1`)**:
     For EVERY finite configuration carrier `Fin S`, `P := natFact S` locks unary `0`-runs identically
     after `S` steps (`iterFin step0 (k + P) cfg = iterFin step0 k cfg` for all `k ≥ S`)!
-/
theorem lsb_mixed_sign_ocn_raw_counter_impossibility_and_bounded_pda_pumping :
    (∀ (Q : Nat) (_hQ : Q ≥ 1)
       (dz dp : Fin Q -> Bool -> Fin Q × CounterOp)
       (q0 : Fin Q) (sl1 : Nat),
      sl1 ≥ 1 ->
      let M1 := Q * (1 + Q + 1)
      let P1 := natFact M1
      let cfg_ev0 := stepOCN dz dp (q0, 0) false
      (∀ t : Nat,
        (iterOCN1 dz dp (M1 + P1 * t) (q0, 0)).2 =
          t * sl1 + (iterOCN1 dz dp M1 (q0, 0)).2) ->
      (∀ t : Nat,
        (iterOCN1 dz dp (M1 + P1 * t) cfg_ev0).2 =
          t * sl1 + (iterOCN1 dz dp M1 cfg_ev0).2) ->
      ∀ (pTerms qTerms : NatPoly2) (pTheta qTheta : Nat),
        ¬ IsPositiveRationalPreimageWeight
            (fun n => evalNatPoly2 pTerms (runLSBOneCounterOCN Q dz dp q0 n).2 (binBitLength n))
            (fun n => evalNatPoly2 qTerms (runLSBOneCounterOCN Q dz dp q0 n).2 (binBitLength n))
            pTheta qTheta) ∧
    (∀ (S : Nat) (_hS : S ≥ 1) (step0 : Fin S -> Fin S) (cfg : Fin S) (k : Nat),
      k ≥ S ->
      iterFin step0 (k + natFact S) cfg = iterFin step0 k cfg) := by
  refine ⟨?_, ?_⟩
  · intro Q hQ dz dp q0 _sl1 _hsl1
    dsimp only
    intro _hgrow0 _hgrow_ev pTerms qTerms pTheta qTheta
    exact unconditional_all_ocn_raw_counter_and_poly_bitlength_preimage_impossibility.2.2.1
      Q hQ dz dp q0 pTerms qTerms pTheta qTheta
  · intro S hS step0 cfg k hk
    simpa using fin_unary_iter_factorial_period hS step0 cfg 1 k hk

/--
  Eventual Berg–Meinardus rational preimage superharmonicity above an arbitrary threshold `M_0 : Nat`
  (exempting all small integers `< M_0`, e.g. exempting `m = 5` on `asymSlopeQ2`).
-/
def IsEventualPositiveRationalPreimageWeight
    (M_0 : Nat) (wNum wDen : Nat -> Nat) (pTheta qTheta : Nat) : Prop :=
  0 < pTheta ∧ pTheta ≤ qTheta ∧
  (∀ n : Nat, n ≥ M_0 -> wNum n > 0 ∧ wDen n > 0) ∧
  (∀ m : Nat, m ≥ M_0 -> m % 3 ≠ 2 ->
    qTheta * (wNum (2 * m) * wDen m) ≤ pTheta * (wNum m * wDen (2 * m))) ∧
  (∀ m : Nat, m ≥ M_0 -> m % 3 = 2 ->
    let nOdd := (2 * m - 1) / 3
    qTheta * ((wNum (2 * m) * wDen nOdd + wNum nOdd * wDen (2 * m)) * wDen m) ≤
      pTheta * (wNum m * (wDen (2 * m) * wDen nOdd)))

private theorem mul_pow_w11 (a b : Nat) : ∀ e : Nat, (a * b) ^ e = a ^ e * b ^ e
  | 0 => rfl
  | e + 1 => by
    rw [Nat.pow_succ (a * b) e, Nat.pow_succ a e, Nat.pow_succ b e, mul_pow_w11 a b e,
        Nat.mul_assoc (a ^ e) (b ^ e) (a * b),
        ← Nat.mul_assoc (b ^ e) a b, Nat.mul_comm (b ^ e) a,
        Nat.mul_assoc a (b ^ e) b, ← Nat.mul_assoc (a ^ e) a]

private theorem preimageBranchNext_eventual_spec
    (M_0 : Nat) (hM0 : M_0 ≥ 3)
    (wNum wDen : Nat -> Nat) (pTheta qTheta x : Nat)
    (hw : IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta)
    (hx_2M0 : x ≥ 2 * M_0) (hx3 : x % 3 ≠ 0) :
    let x' := preimageBranchNext wNum wDen x
    x < x' ∧ x' % 3 ≠ 0 ∧ x' ≤ 128 * x ∧ 2 * wNum x' * wDen x ≤ wNum x * wDen x' := by
  dsimp only
  have hq_pos : qTheta > 0 := Nat.lt_of_lt_of_le hw.1 hw.2.1
  rcases mod9ShiftTo8_spec x hx3 with ⟨hr1, hr6, hm9⟩
  let r := mod9ShiftTo8 x
  let m := 2 ^ r * x
  change m % 9 = 8 at hm9
  let y0 := 2 * m
  let y1 := (2 * m - 1) / 3
  have hp_lo : 2 ≤ 2 ^ r := by simpa using pow2_mono_nat hr1
  have hp_hi : 2 ^ r ≤ 64 := by simpa using pow2_mono_nat hr6
  have hm_ge2x : m ≥ 2 * x := by dsimp only [m]; exact Nat.mul_le_mul_right x hp_lo
  have hm_le : m ≤ 64 * x := by dsimp only [m]; exact Nat.mul_le_mul_right x hp_hi
  have hm_m3 : m % 3 = 2 := by omega
  have hy0_gt : x < y0 := by dsimp only [y0]; omega
  have hy0_m3 : y0 % 3 ≠ 0 := by dsimp only [y0]; omega
  have hy0_le : y0 ≤ 128 * x := by dsimp only [y0]; omega
  have hy1_eq : y1 = 6 * (m / 9) + 5 := by dsimp only [y1]; omega
  have hy1_gt : x < y1 := by dsimp only [y1]; omega
  have hy1_m3 : y1 % 3 ≠ 0 := by rw [hy1_eq]; omega
  have hy1_le : y1 ≤ 128 * x := by dsimp only [y1]; omega
  have heven_step : ∀ z : Nat, z ≥ 2 * M_0 -> wNum (2 * z) * wDen z ≤ wNum z * wDen (2 * z) := by
    intro z hz
    by_cases hz2 : z % 3 = 2
    · let nOdd := (2 * z - 1) / 3
      have hnOdd_ge : nOdd ≥ M_0 := by dsimp only [nOdd]; omega
      have hdn_pos : wDen nOdd > 0 := (hw.2.2.1 nOdd hnOdd_ge).2
      have hpre_z := hw.2.2.2.2 z (by omega) hz2
      dsimp only at hpre_z
      have hbr_z : (wNum (2 * z) * wDen nOdd + wNum nOdd * wDen (2 * z)) * wDen z ≤
          wNum z * (wDen (2 * z) * wDen nOdd) :=
        nat_mul_le_cancel_left_w5 qTheta _ _ hq_pos
          (Nat.le_trans hpre_z (Nat.mul_le_mul_right _ hw.2.1))
      have hdrop : (wNum (2 * z) * wDen z) * wDen nOdd ≤ (wNum z * wDen (2 * z)) * wDen nOdd := by
        have hl : (wNum (2 * z) * wDen z) * wDen nOdd = (wNum (2 * z) * wDen nOdd) * wDen z := by
          rw [Nat.mul_assoc, Nat.mul_comm (wDen z) (wDen nOdd), ← Nat.mul_assoc]
        have hr : (wNum z * wDen (2 * z)) * wDen nOdd = wNum z * (wDen (2 * z) * wDen nOdd) :=
          Nat.mul_assoc _ _ _
        rw [hl, hr]
        rw [Nat.add_mul] at hbr_z
        omega
      exact nat_mul_le_cancel_right_w5 (wDen nOdd) _ _ hdn_pos hdrop
    · have hpre_z := hw.2.2.2.1 z (by omega) hz2
      exact nat_mul_le_cancel_left_w5 qTheta _ _ hq_pos
        (Nat.le_trans hpre_z (Nat.mul_le_mul_right _ hw.2.1))
  have hpow2_le : ∀ d : Nat,
      wNum (2 ^ d * x) * wDen x ≤ wNum x * wDen (2 ^ d * x) := by
    intro d; induction d with
    | zero => simp
    | succ d' ih =>
      have hzd : 2 ^ d' * x ≥ 2 * M_0 := by
        have hm1 := Nat.mul_le_mul (pow2_pos_nat d') hx_2M0; omega
      have hmul : 2 ^ (d' + 1) * x = 2 * (2 ^ d' * x) := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ d') 2, Nat.mul_assoc]
      rw [hmul]
      exact rat_le_trans_pos_w5 _ _ (wNum (2 ^ d' * x)) (wDen (2 ^ d' * x)) _ _
        (hw.2.2.1 (2 ^ d' * x) (by omega)).2 (heven_step (2 ^ d' * x) hzd) ih
  have hm_le_x : wNum m * wDen x ≤ wNum x * wDen m := hpow2_le r
  have hpre := hw.2.2.2.2 m (by omega) hm_m3
  dsimp only at hpre
  have hbr : (wNum y0 * wDen y1 + wNum y1 * wDen y0) * wDen m ≤
      wNum m * (wDen y0 * wDen y1) :=
    nat_mul_le_cancel_left_w5 qTheta _ _ hq_pos
      (Nat.le_trans hpre (Nat.mul_le_mul_right _ hw.2.1))
  have hbm_pos : wDen m > 0 := (hw.2.2.1 m (by omega)).2
  have hb0_pos : wDen y0 > 0 := (hw.2.2.1 y0 (by omega)).2
  have hb1_pos : wDen y1 > 0 := (hw.2.2.1 y1 (by omega)).2
  have hchoice :
      let x' := preimageBranchNext wNum wDen x
      x < x' ∧ x' % 3 ≠ 0 ∧ x' ≤ 128 * x ∧ 2 * wNum x' * wDen m ≤ wNum m * wDen x' := by
    unfold preimageBranchNext
    dsimp only
    change x < (if 2 * wNum y0 * wDen m ≤ wNum m * wDen y0 then y0 else y1) ∧ _
    by_cases hcond : 2 * wNum y0 * wDen m ≤ wNum m * wDen y0
    · rw [ite_true_of_w10 hcond]
      exact ⟨hy0_gt, hy0_m3, hy0_le, hcond⟩
    · rw [ite_false_of_w10 hcond]
      refine ⟨hy1_gt, hy1_m3, hy1_le, ?_⟩
      by_cases hc1 : 2 * wNum y1 * wDen m ≤ wNum m * wDen y1
      · exact hc1
      · exfalso
        have hlt0 : wNum m * wDen y0 < 2 * wNum y0 * wDen m := by omega
        have hlt1 : wNum m * wDen y1 < 2 * wNum y1 * wDen m := by omega
        have hm0 := Nat.mul_lt_mul_of_pos_right hlt0 hb1_pos
        have hm1 := Nat.mul_lt_mul_of_pos_right hlt1 hb0_pos
        have hl0 : (wNum m * wDen y0) * wDen y1 = wNum m * (wDen y0 * wDen y1) :=
          Nat.mul_assoc _ _ _
        have hl1 : (wNum m * wDen y1) * wDen y0 = wNum m * (wDen y0 * wDen y1) := by
          rw [Nat.mul_assoc, Nat.mul_comm (wDen y1) (wDen y0)]
        have hr0 : (2 * wNum y0 * wDen m) * wDen y1 = 2 * ((wNum y0 * wDen y1) * wDen m) := by
          rw [Nat.mul_assoc 2 (wNum y0) (wDen m), Nat.mul_assoc 2,
              Nat.mul_assoc (wNum y0) (wDen m) (wDen y1),
              Nat.mul_comm (wDen m) (wDen y1), ← Nat.mul_assoc (wNum y0)]
        have hr1 : (2 * wNum y1 * wDen m) * wDen y0 = 2 * ((wNum y1 * wDen y0) * wDen m) := by
          rw [Nat.mul_assoc 2 (wNum y1) (wDen m), Nat.mul_assoc 2,
              Nat.mul_assoc (wNum y1) (wDen m) (wDen y0),
              Nat.mul_comm (wDen m) (wDen y0), ← Nat.mul_assoc (wNum y1)]
        rw [hl0, hr0] at hm0
        rw [hl1, hr1] at hm1
        rw [Nat.add_mul (wNum y0 * wDen y1) (wNum y1 * wDen y0) (wDen m)] at hbr
        omega
  rcases hchoice with ⟨hx'_gt, hx'_m3, hx'_le, hstep_m⟩
  refine ⟨hx'_gt, hx'_m3, hx'_le, ?_⟩
  exact rat_le_trans_pos_w5 (2 * wNum (preimageBranchNext wNum wDen x))
    (wDen (preimageBranchNext wNum wDen x)) (wNum m) (wDen m) (wNum x) (wDen x)
    hbm_pos hstep_m hm_le_x

private theorem preimageBranchIter_eventual_spec
    (M_0 : Nat) (hM0 : M_0 ≥ 3)
    (wNum wDen : Nat -> Nat) (pTheta qTheta : Nat)
    (hw : IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta) :
    let x0 := 6 * M_0 + 5
    ∀ k : Nat,
      let xk := preimageBranchIter wNum wDen k x0
      xk ≥ x0 + k ∧ xk % 3 ≠ 0 ∧ xk < 2 ^ (7 * k + x0) ∧
      2 ^ k * wNum xk * wDen x0 ≤ wNum x0 * wDen xk := by
  dsimp only
  let x0 := 6 * M_0 + 5
  intro k; induction k with
  | zero =>
    simp only [preimageBranchIter, Nat.add_zero, Nat.mul_zero, Nat.zero_add,
               Nat.pow_zero, Nat.one_mul]
    exact ⟨Nat.le_refl x0, by omega, id_lt_pow2_w11 x0, Nat.le_refl _⟩
  | succ k' ih =>
    rcases ih with ⟨hxk_ge, hxk_m3, hxk_lt, hxk_rat⟩
    let xk := preimageBranchIter wNum wDen k' x0
    change xk ≥ x0 + k' at hxk_ge
    change xk % 3 ≠ 0 at hxk_m3
    change xk < 2 ^ (7 * k' + x0) at hxk_lt
    change 2 ^ k' * wNum xk * wDen x0 ≤ wNum x0 * wDen xk at hxk_rat
    have hxk_2M0 : xk ≥ 2 * M_0 := by omega
    rcases preimageBranchNext_eventual_spec M_0 hM0 wNum wDen pTheta qTheta xk hw hxk_2M0 hxk_m3 with
      ⟨hn_gt, hn_m3, hn_le, hn_rat⟩
    let xn := preimageBranchNext wNum wDen xk
    have hxn_lt : xn < 2 ^ (7 * (k' + 1) + x0) := by
      have hp7 : 2 ^ (7 * (k' + 1) + x0) = 128 * 2 ^ (7 * k' + x0) := by
        rw [show 7 * (k' + 1) + x0 = (7 * k' + x0) + 7 by omega,
            Nat.pow_add 2 (7 * k' + x0) 7, Nat.mul_comm _ (2 ^ 7)]
      rw [hp7]; omega
    have hbxk_pos : wDen xk > 0 := (hw.2.2.1 xk (by omega)).2
    have hstep_scaled : (2 ^ (k' + 1) * wNum xn) * wDen xk ≤ (2 ^ k' * wNum xk) * wDen xn := by
      have hm := Nat.mul_le_mul_left (2 ^ k') hn_rat
      have hl : 2 ^ k' * (2 * wNum xn * wDen xk) = (2 ^ (k' + 1) * wNum xn) * wDen xk := by
        rw [Nat.pow_succ 2 k', Nat.mul_assoc (2 ^ k') 2 (wNum xn),
            Nat.mul_assoc (2 ^ k') (2 * wNum xn) (wDen xk)]
      have hr : 2 ^ k' * (wNum xk * wDen xn) = (2 ^ k' * wNum xk) * wDen xn :=
        (Nat.mul_assoc _ _ _).symm
      rwa [hl, hr] at hm
    have htot := rat_le_trans_pos_w5 (2 ^ (k' + 1) * wNum xn) (wDen xn)
      (2 ^ k' * wNum xk) (wDen xk) (wNum x0) (wDen x0) hbxk_pos hstep_scaled hxk_rat
    change xn ≥ x0 + (k' + 1) ∧ xn % 3 ≠ 0 ∧ xn < 2 ^ (7 * (k' + 1) + x0) ∧
      2 ^ (k' + 1) * wNum xn * wDen x0 ≤ wNum x0 * wDen xn
    exact ⟨by omega, hn_m3, hxn_lt, htot⟩

/--
  Theorem W11.3a'''''' (`eventual_poly_bitlength_denominator_preimage_impossibility`,
  choice-free `zero custom axioms`):
  Eventual-Threshold (`∀ M_0 ≥ 3`) Polynomial-`binBitLength` Denominator Preimage Barrier (`Branch P1.2`):
  1. `preimageBranchNext` strictly increases `x < preimageBranchNext wNum wDen x` across all `x ≥ 5, x % 3 ≠ 0`.
  2. Even if ALL finitely many small integers `< M_0` (`∀ M_0 ≥ 3`, e.g. `m = 5` on `asymSlopeQ2`) are
     exempted, NO positive rational weight satisfying `wDen n ≤ C_den * (binBitLength n) ^ D_den` (`∀ n ≥ M_0`)
     can satisfy `IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta`!
-/
theorem eventual_poly_bitlength_denominator_preimage_impossibility :
    (∀ (wNum wDen : Nat -> Nat) (x : Nat),
      x ≥ 5 -> x % 3 ≠ 0 -> x < preimageBranchNext wNum wDen x) ∧
    (∀ (M_0 : Nat), M_0 ≥ 3 ->
      ∀ (wNum wDen : Nat -> Nat) (C_den D_den pTheta qTheta : Nat),
        (∀ n : Nat, n ≥ M_0 -> wDen n ≤ C_den * (binBitLength n) ^ D_den) ->
        ¬ IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta) := by
  refine ⟨?_, ?_⟩
  · intro wNum wDen x hx5 hx3
    rcases mod9ShiftTo8_spec x hx3 with ⟨hr1, _, _⟩
    have hp_lo : 2 ≤ 2 ^ (mod9ShiftTo8 x) := by simpa using pow2_mono_nat hr1
    have hm_ge2x : 2 ^ (mod9ShiftTo8 x) * x ≥ 2 * x := Nat.mul_le_mul_right x hp_lo
    unfold preimageBranchNext
    dsimp only
    by_cases hcond : 2 * wNum (2 * (2 ^ mod9ShiftTo8 x * x)) * wDen (2 ^ mod9ShiftTo8 x * x) ≤
        wNum (2 ^ mod9ShiftTo8 x * x) * wDen (2 * (2 ^ mod9ShiftTo8 x * x))
    · rw [ite_true_of_w10 hcond]; omega
    · rw [ite_false_of_w10 hcond]; omega
  · intro M_0 hM0 wNum wDen C_den D_den pTheta qTheta hden_bound hw
    let x0 := 6 * M_0 + 5
    have hx0_pos : x0 ≥ 1 := by omega
    rcases exists_pow2_gt_const_mul_bitlen_pow (wNum x0 * C_den * x0 ^ D_den) D_den with ⟨k, hgt⟩
    rcases preimageBranchIter_eventual_spec M_0 hM0 wNum wDen pTheta qTheta hw k with
      ⟨hxk_ge, _, hxk_lt, hxk_rat⟩
    let xk := preimageBranchIter wNum wDen k x0
    change xk ≥ x0 + k at hxk_ge
    change xk < 2 ^ (7 * k + x0) at hxk_lt
    change 2 ^ k * wNum xk * wDen x0 ≤ wNum x0 * wDen xk at hxk_rat
    have hxk_M0 : xk ≥ M_0 := by omega
    have hx0_M0 : x0 ≥ M_0 := by omega
    have hwn_pos : wNum xk ≥ 1 := (hw.2.2.1 xk hxk_M0).1
    have hwd0_pos : wDen x0 ≥ 1 := (hw.2.2.1 x0 hx0_M0).2
    have hlhs_ge : 2 ^ k ≤ 2 ^ k * wNum xk * wDen x0 := by
      have hm1 : 2 ^ k * 1 ≤ 2 ^ k * wNum xk := Nat.mul_le_mul_left (2 ^ k) hwn_pos
      have hm2 : (2 ^ k * wNum xk) * 1 ≤ (2 ^ k * wNum xk) * wDen x0 :=
        Nat.mul_le_mul_left (2 ^ k * wNum xk) hwd0_pos
      omega
    have hbl_xk : binBitLength xk ≤ x0 * (7 * k + 3) := by
      have hpred := (binBitLength_pow2_and_pred (7 * k + x0 - 1)).2
      have hmono := binBitLength_mono xk (2 ^ ((7 * k + x0 - 1) + 1) - 1)
        (by rw [show (7 * k + x0 - 1) + 1 = 7 * k + x0 by omega]; omega)
      have h1 : binBitLength xk ≤ 7 * k + x0 := by omega
      have h2 : 7 * k + x0 ≤ x0 * (7 * k + 3) := by
        rw [Nat.mul_add x0 (7 * k) 3]
        have hm1 : 1 * (7 * k) ≤ x0 * (7 * k) := Nat.mul_le_mul_right (7 * k) hx0_pos
        omega
      exact Nat.le_trans h1 h2
    have hpow_xk : (binBitLength xk) ^ D_den ≤ x0 ^ D_den * (7 * k + 3) ^ D_den := by
      have hm := pow_mono_base_w11 _ _ hbl_xk D_den
      rwa [mul_pow_w11 x0 (7 * k + 3) D_den] at hm
    have hden_xk : wDen xk ≤ (C_den * x0 ^ D_den) * (7 * k + 3) ^ D_den := by
      have hm := Nat.le_trans (hden_bound xk hxk_M0) (Nat.mul_le_mul_left C_den hpow_xk)
      rwa [← Nat.mul_assoc C_den (x0 ^ D_den)] at hm
    have hrhs_le : wNum x0 * wDen xk ≤ (wNum x0 * C_den * x0 ^ D_den) * (7 * k + 3) ^ D_den := by
      have hm := Nat.mul_le_mul_left (wNum x0) hden_xk
      rwa [← Nat.mul_assoc (wNum x0) (C_den * x0 ^ D_den),
           ← Nat.mul_assoc (wNum x0) C_den (x0 ^ D_den)] at hm
    omega

/-- Single real-time step of a general `Q`-state, `G`-symbol context-free pushdown automaton (`PDA`). -/
def stepGeneralPDA {Q G : Nat}
    (delta : Fin Q -> Option (Fin G) -> Bool -> Fin Q × List (Fin G))
    (cfg : Fin Q × List (Fin G)) (b : Bool) : Fin Q × List (Fin G) :=
  match cfg.2 with
  | [] =>
    let res := delta cfg.1 none b
    (res.1, res.2)
  | top :: rest =>
    let res := delta cfg.1 (some top) b
    (res.1, res.2 ++ rest)

/-- Observable top-of-stack mode `(q, head? stk)` of a general context-free `PDA`. -/
def pdaObservableMode {Q G : Nat} (cfg : Fin Q × List (Fin G)) : Fin Q × Option (Fin G) :=
  (cfg.1, cfg.2.head?)

def runMSBGeneralPDAAux {Q G : Nat}
    (delta : Fin Q -> Option (Fin G) -> Bool -> Fin Q × List (Fin G))
    (initCfg : Fin Q × List (Fin G)) : Nat -> Nat -> Fin Q × List (Fin G)
  | 0, _ => initCfg
  | fuel + 1, n =>
    if n = 0 then initCfg
    else stepGeneralPDA delta (runMSBGeneralPDAAux delta initCfg fuel (n / 2)) (n % 2 == 1)

def runMSBGeneralPDA (Q G : Nat)
    (delta : Fin Q -> Option (Fin G) -> Bool -> Fin Q × List (Fin G))
    (initCfg : Fin Q × List (Fin G)) (n : Nat) : Fin Q × List (Fin G) :=
  runMSBGeneralPDAAux delta initCfg n n

def runLSBGeneralPDAAux {Q G : Nat}
    (delta : Fin Q -> Option (Fin G) -> Bool -> Fin Q × List (Fin G)) :
    Nat -> Nat -> (Fin Q × List (Fin G)) -> (Fin Q × List (Fin G))
  | 0, _, cfg => cfg
  | fuel + 1, n, cfg =>
    if n = 0 then cfg
    else runLSBGeneralPDAAux delta fuel (n / 2) (stepGeneralPDA delta cfg (n % 2 == 1))

def runLSBGeneralPDA (Q G : Nat)
    (delta : Fin Q -> Option (Fin G) -> Bool -> Fin Q × List (Fin G))
    (initCfg : Fin Q × List (Fin G)) (n : Nat) : Fin Q × List (Fin G) :=
  runLSBGeneralPDAAux delta n n initCfg

/-- Arbitrary-initial-counter MSB `1`-counter `OCN` runner (dual to `runLSBFromOCN`). -/
def runMSBFromOCNAux {Q : Nat}
    (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp)
    (initCfg : Fin Q × Nat) : Nat -> Nat -> Fin Q × Nat
  | 0, _ => initCfg
  | fuel + 1, n =>
    if n = 0 then initCfg
    else stepOCN deltaZero deltaPos
           (runMSBFromOCNAux deltaZero deltaPos initCfg fuel (n / 2)) (n % 2 == 1)

def runMSBFromOCN {Q : Nat}
    (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp)
    (n : Nat) (initCfg : Fin Q × Nat) : Fin Q × Nat :=
  runMSBFromOCNAux deltaZero deltaPos initCfg n n

private def sumOverFinW11 {N : Nat} (f : Fin N -> Nat) : ∀ k : Nat, k ≤ N -> Nat
  | 0, _ => 0
  | k + 1, hk => f ⟨k, hk⟩ + sumOverFinW11 f k (Nat.le_of_lt hk)

private theorem le_sumOverFinW11 {N : Nat} (f : Fin N -> Nat) :
    ∀ (k : Nat) (hk : k ≤ N) (x : Fin N), x.val < k -> f x ≤ sumOverFinW11 f k hk
  | 0, _, _, hlt => by omega
  | k + 1, hk, x, hlt => by
    simp only [sumOverFinW11]
    by_cases hxk : x.val = k
    · have hxf : x = ⟨k, hk⟩ := Fin.ext hxk
      subst hxf; omega
    · have ih := le_sumOverFinW11 f k (Nat.le_of_lt hk) x (by omega)
      omega

private def sumOverOptFinW11 {G : Nat} (f : Option (Fin G) -> Nat) : Nat :=
  f none + sumOverFinW11 (fun g => f (some g)) G (Nat.le_refl G)

private theorem le_sumOverOptFinW11 {G : Nat} (f : Option (Fin G) -> Nat) (o : Option (Fin G)) :
    f o ≤ sumOverOptFinW11 f := by
  unfold sumOverOptFinW11
  cases o with
  | none => omega
  | some g =>
    have hm := le_sumOverFinW11 (fun g' => f (some g')) G (Nat.le_refl G) g g.isLt
    omega

private theorem stepGeneralPDA_length_le {Q G : Nat}
    (delta : Fin Q -> Option (Fin G) -> Bool -> Fin Q × List (Fin G))
    (K_push : Nat)
    (hK : ∀ (q : Fin Q) (o : Option (Fin G)) (b : Bool), (delta q o b).2.length ≤ K_push)
    (cfg : Fin Q × List (Fin G)) (b : Bool) :
    (stepGeneralPDA delta cfg b).2.length ≤ cfg.2.length + K_push := by
  rcases cfg with ⟨q, stk⟩
  cases stk with
  | nil =>
    simp only [stepGeneralPDA, List.length_nil, Nat.zero_add]
    exact hK q none b
  | cons top rest =>
    simp only [stepGeneralPDA, List.length_append, List.length_cons]
    have hm := hK q (some top) b
    omega

/--
  Theorem W11.3a''''''' (`unconditional_general_pda_stack_height_and_arbitrary_init_ocn_impossibility`,
  choice-free `zero custom axioms`):
  Unconditional Closure of ALL `∀ Q, G ≥ 1` Real-Time Context-Free `PDA` (`MSB` & `LSB`, Arbitrary
  Finite Push-Word Transitions) Stack-Height `NatPoly3` AND Arbitrary-Initial-Counter `(q0, c0)` `OCN`
  Preimage Weights (Even Eventually Above ANY Cutoff `∀ M_0 ≥ 3`, `Branch P1.2`, `W11_H1`):
  1. **General `∀ Q_L, G_L, Q_M, G_M ≥ 1` Context-Free `PDA` Mode + Dual-Stack-Height `NatPoly3` Impossibility**:
     With ZERO push-length or sign-uniformity hypotheses, NO rational weight combining `LSB` & `MSB`
     observable top-of-stack modes `(q, head? stk)` with `NatPoly3(h_LSB(n), h_MSB(n), binBitLength n)`
     (subsuming single `MSB`/`LSB` `NatPoly2(h(n), binBitLength n)` AND coordinate-swapped
     `NatPoly2(binBitLength n, h(n))`!) can satisfy `IsEventualPositiveRationalPreimageWeight M_0` (`∀ M_0 ≥ 3`)!
  2. **Arbitrary-Initial-Counter `(q0L, c0L), (q0M, c0M)` Joint `OCN` `NatPoly3` Eventual Impossibility**:
     Closes ALL `∀ Q_L, Q_M ≥ 1`, `∀ M_0 ≥ 3` joint `MSB + LSB` `OCN` mode-weighted + dual-raw-counter
     `NatPoly3` weights starting from arbitrary initial counters `(q0L, c0L)` and `(q0M, c0M)`!
-/
theorem unconditional_general_pda_stack_height_and_arbitrary_init_ocn_impossibility :
    -- 1. General `∀ Q_L, G_L, Q_M, G_M ≥ 1` context-free `PDA` stack-height + mode `NatPoly3` impossibility:
    (∀ (M_0 : Nat), M_0 ≥ 3 ->
      ∀ (Q_L G_L Q_M G_M : Nat) (_hQL : Q_L ≥ 1) (_hGL : G_L ≥ 1) (_hQM : Q_M ≥ 1) (_hGM : G_M ≥ 1)
        (deltaL : Fin Q_L -> Option (Fin G_L) -> Bool -> Fin Q_L × List (Fin G_L))
        (deltaM : Fin Q_M -> Option (Fin G_M) -> Bool -> Fin Q_M × List (Fin G_M))
        (initL : Fin Q_L × List (Fin G_L)) (initM : Fin Q_M × List (Fin G_M))
        (fNum fDen : (Fin Q_L × Option (Fin G_L)) -> (Fin Q_M × Option (Fin G_M)) -> Nat)
        (pTerms3 qTerms3 : NatPoly3) (pTheta qTheta : Nat),
        ¬ IsEventualPositiveRationalPreimageWeight M_0
            (fun n =>
              fNum (pdaObservableMode (runLSBGeneralPDA Q_L G_L deltaL initL n))
                   (pdaObservableMode (runMSBGeneralPDA Q_M G_M deltaM initM n)) *
              evalNatPoly3 pTerms3
                (runLSBGeneralPDA Q_L G_L deltaL initL n).2.length
                (runMSBGeneralPDA Q_M G_M deltaM initM n).2.length
                (binBitLength n))
            (fun n =>
              fDen (pdaObservableMode (runLSBGeneralPDA Q_L G_L deltaL initL n))
                   (pdaObservableMode (runMSBGeneralPDA Q_M G_M deltaM initM n)) *
              evalNatPoly3 qTerms3
                (runLSBGeneralPDA Q_L G_L deltaL initL n).2.length
                (runMSBGeneralPDA Q_M G_M deltaM initM n).2.length
                (binBitLength n))
            pTheta qTheta) ∧
    -- 2. Arbitrary-initial-counter `(q0L, c0L), (q0M, c0M)` joint `OCN` `NatPoly3` eventual impossibility:
    (∀ (M_0 : Nat), M_0 ≥ 3 ->
      ∀ (Q_L Q_M : Nat) (_hQL : Q_L ≥ 1) (_hQM : Q_M ≥ 1)
        (dzL dpL : Fin Q_L -> Bool -> Fin Q_L × CounterOp)
        (dzM dpM : Fin Q_M -> Bool -> Fin Q_M × CounterOp)
        (initL : Fin Q_L × Nat) (initM : Fin Q_M × Nat)
        (fNum fDen : (Fin Q_L × Bool) -> (Fin Q_M × Bool) -> Nat)
        (pTerms3 qTerms3 : NatPoly3) (pTheta qTheta : Nat),
        ¬ IsEventualPositiveRationalPreimageWeight M_0
            (fun n =>
              fNum (ocnObservableMode (runLSBFromOCN dzL dpL n initL))
                   (ocnObservableMode (runMSBFromOCN dzM dpM n initM)) *
              evalNatPoly3 pTerms3
                (runLSBFromOCN dzL dpL n initL).2
                (runMSBFromOCN dzM dpM n initM).2
                (binBitLength n))
            (fun n =>
              fDen (ocnObservableMode (runLSBFromOCN dzL dpL n initL))
                   (ocnObservableMode (runMSBFromOCN dzM dpM n initM)) *
              evalNatPoly3 qTerms3
                (runLSBFromOCN dzL dpL n initL).2
                (runMSBFromOCN dzM dpM n initM).2
                (binBitLength n))
            pTheta qTheta) := by
  have hpoly3_scaled_ub : ∀ (F : NatPoly3) (S x y z L : Nat),
      S ≥ 1 -> L ≥ 1 -> x ≤ S * L -> y ≤ S * L -> z ≤ S * L ->
      evalNatPoly3 F x y z ≤ (evalNatPoly3 F 1 1 1 * S ^ maxDegNatPoly3 F) * L ^ maxDegNatPoly3 F := by
    intro F S x y z L hS hL hx hy hz
    have hSL : 1 ≤ S * L := Nat.mul_le_mul hS hL
    have hcr := evalNatPoly3_cross_ratio_bound F 1 (S * L) x y z 1 1 1 hSL
      (by omega) (by omega) (by omega)
    rw [Nat.one_pow, Nat.one_mul, mul_pow_w11 S L (maxDegNatPoly3 F),
        Nat.mul_comm (S ^ maxDegNatPoly3 F * L ^ maxDegNatPoly3 F),
        ← Nat.mul_assoc (evalNatPoly3 F 1 1 1)] at hcr
    exact hcr
  have hbl_pos3 : ∀ n : Nat, n ≥ 3 -> binBitLength n ≥ 1 := by
    intro n hn3
    have h1 : binBitLength 1 = 1 := rfl
    have hm := binBitLength_mono 1 n (by omega)
    omega
  refine ⟨?_, ?_⟩
  · -- Part 1: General `∀ Q, G ≥ 1` `PDA` mode + stack-height `NatPoly3`:
    intro M_0 hM0 Q_L G_L Q_M G_M _hQL _hGL _hQM _hGM deltaL deltaM initL initM fNum fDen pTerms3 qTerms3 pTheta qTheta
    let KL := sumOverFinW11 (fun q => sumOverOptFinW11 (fun o =>
      (deltaL q o false).2.length + (deltaL q o true).2.length)) Q_L (Nat.le_refl Q_L)
    let KM := sumOverFinW11 (fun q => sumOverOptFinW11 (fun o =>
      (deltaM q o false).2.length + (deltaM q o true).2.length)) Q_M (Nat.le_refl Q_M)
    have hKL : ∀ q o b, (deltaL q o b).2.length ≤ KL := by
      intro q o b
      have h1 := le_sumOverOptFinW11 (fun o' => (deltaL q o' false).2.length + (deltaL q o' true).2.length) o
      have h2 := le_sumOverFinW11 (fun q' => sumOverOptFinW11 (fun o' =>
        (deltaL q' o' false).2.length + (deltaL q' o' true).2.length)) Q_L (Nat.le_refl Q_L) q q.isLt
      cases b <;> omega
    have hKM : ∀ q o b, (deltaM q o b).2.length ≤ KM := by
      intro q o b
      have h1 := le_sumOverOptFinW11 (fun o' => (deltaM q o' false).2.length + (deltaM q o' true).2.length) o
      have h2 := le_sumOverFinW11 (fun q' => sumOverOptFinW11 (fun o' =>
        (deltaM q' o' false).2.length + (deltaM q' o' true).2.length)) Q_M (Nat.le_refl Q_M) q q.isLt
      cases b <;> omega
    have hlsb_len : ∀ (fuel m : Nat) (cfg : Fin Q_L × List (Fin G_L)),
        (runLSBGeneralPDAAux deltaL fuel m cfg).2.length ≤ cfg.2.length + KL * binBitLength m := by
      intro fuel; induction fuel with
      | zero => intro m cfg; simp [runLSBGeneralPDAAux]
      | succ fuel' ih =>
        intro m cfg
        simp only [runLSBGeneralPDAAux]
        by_cases hm0 : m = 0
        · subst hm0; simp
        · simp only [hm0, ite_false]
          rw [binBitLength_step_pos m (by omega), Nat.mul_add KL 1 _, Nat.mul_one]
          have hst := stepGeneralPDA_length_le deltaL KL hKL cfg (m % 2 == 1)
          have hih := ih (m / 2) (stepGeneralPDA deltaL cfg (m % 2 == 1))
          omega
    have hmsb_len : ∀ (fuel m : Nat),
        (runMSBGeneralPDAAux deltaM initM fuel m).2.length ≤ initM.2.length + KM * binBitLength m := by
      intro fuel; induction fuel with
      | zero => intro m; simp [runMSBGeneralPDAAux]
      | succ fuel' ih =>
        intro m
        simp only [runMSBGeneralPDAAux]
        by_cases hm0 : m = 0
        · subst hm0; simp
        · simp only [hm0, ite_false]
          rw [binBitLength_step_pos m (by omega), Nat.mul_add KM 1 _, Nat.mul_one]
          have hst := stepGeneralPDA_length_le deltaM KM hKM
            (runMSBGeneralPDAAux deltaM initM fuel' (m / 2)) (m % 2 == 1)
          have hih := ih (m / 2)
          omega
    let F_pda := sumOverFinW11 (fun qL => sumOverOptFinW11 (fun oL =>
      sumOverFinW11 (fun qM => sumOverOptFinW11 (fun oM => fDen (qL, oL) (qM, oM)))
        Q_M (Nat.le_refl Q_M))) Q_L (Nat.le_refl Q_L)
    have hf_le : ∀ (μL : Fin Q_L × Option (Fin G_L)) (μM : Fin Q_M × Option (Fin G_M)),
        fDen μL μM ≤ F_pda := by
      intro ⟨qL, oL⟩ ⟨qM, oM⟩
      have h1 := le_sumOverOptFinW11 (fun oM' => fDen (qL, oL) (qM, oM')) oM
      have h2 := le_sumOverFinW11 (fun qM' => sumOverOptFinW11 (fun oM' => fDen (qL, oL) (qM', oM')))
        Q_M (Nat.le_refl Q_M) qM qM.isLt
      have h3 := le_sumOverOptFinW11 (fun oL' => sumOverFinW11 (fun qM' =>
        sumOverOptFinW11 (fun oM' => fDen (qL, oL') (qM', oM'))) Q_M (Nat.le_refl Q_M)) oL
      have h4 := le_sumOverFinW11 (fun qL' => sumOverOptFinW11 (fun oL' =>
        sumOverFinW11 (fun qM' => sumOverOptFinW11 (fun oM' => fDen (qL', oL') (qM', oM')))
          Q_M (Nat.le_refl Q_M))) Q_L (Nat.le_refl Q_L) qL qL.isLt
      omega
    let S := initL.2.length + KL + initM.2.length + KM + 1
    let d := maxDegNatPoly3 qTerms3
    apply eventual_poly_bitlength_denominator_preimage_impossibility.2 M_0 hM0 _ _
      (F_pda * (evalNatPoly3 qTerms3 1 1 1 * S ^ d)) d pTheta qTheta
    intro n hnM0
    have hL_pos : binBitLength n ≥ 1 := hbl_pos3 n (by omega)
    have hS_pos : S ≥ 1 := by omega
    have hl_ub : (runLSBGeneralPDA Q_L G_L deltaL initL n).2.length ≤ S * binBitLength n := by
      have hb := hlsb_len n n initL
      have h1 : initL.2.length + KL * binBitLength n ≤ (initL.2.length + KL) * binBitLength n := by
        rw [Nat.add_mul]
        have hm := Nat.mul_le_mul_left initL.2.length hL_pos
        omega
      have h2 : (initL.2.length + KL) * binBitLength n ≤ S * binBitLength n :=
        Nat.mul_le_mul_right (binBitLength n) (by omega)
      exact Nat.le_trans hb (Nat.le_trans h1 h2)
    have hm_ub : (runMSBGeneralPDA Q_M G_M deltaM initM n).2.length ≤ S * binBitLength n := by
      have hb := hmsb_len n n
      have h1 : initM.2.length + KM * binBitLength n ≤ (initM.2.length + KM) * binBitLength n := by
        rw [Nat.add_mul]
        have hm := Nat.mul_le_mul_left initM.2.length hL_pos
        omega
      have h2 : (initM.2.length + KM) * binBitLength n ≤ S * binBitLength n :=
        Nat.mul_le_mul_right (binBitLength n) (by omega)
      exact Nat.le_trans hb (Nat.le_trans h1 h2)
    have hz_ub : binBitLength n ≤ S * binBitLength n := by
      simpa using Nat.mul_le_mul_right (binBitLength n) hS_pos
    have hp_ub := hpoly3_scaled_ub qTerms3 S _ _ (binBitLength n) (binBitLength n)
      hS_pos hL_pos hl_ub hm_ub hz_ub
    have hf_inst := hf_le (pdaObservableMode (runLSBGeneralPDA Q_L G_L deltaL initL n))
                          (pdaObservableMode (runMSBGeneralPDA Q_M G_M deltaM initM n))
    have hm := Nat.mul_le_mul hf_inst hp_ub
    rwa [← Nat.mul_assoc F_pda (evalNatPoly3 qTerms3 1 1 1 * S ^ d)] at hm
  · -- Part 2: Arbitrary-initial-counter `(q0L, c0L), (q0M, c0M)` joint `OCN` `NatPoly3`:
    intro M_0 hM0 Q_L Q_M _hQL _hQM dzL dpL dzM dpM initL initM fNum fDen pTerms3 qTerms3 pTheta qTheta
    have hlsb_c : ∀ (fuel m : Nat) (cfg : Fin Q_L × Nat),
        (runLSBOneCounterOCNAux dzL dpL fuel m cfg).2 ≤ cfg.2 + binBitLength m := by
      intro fuel; induction fuel with
      | zero => intro m cfg; simp [runLSBOneCounterOCNAux]
      | succ fuel' ih =>
        intro m cfg
        simp only [runLSBOneCounterOCNAux]
        by_cases hm0 : m = 0
        · subst hm0; simp
        · simp only [hm0, ite_false]
          rw [binBitLength_step_pos m (by omega)]
          have hst := stepOCN_counter_le_succ dzL dpL cfg (m % 2 == 1)
          have hih := ih (m / 2) (stepOCN dzL dpL cfg (m % 2 == 1))
          omega
    have hmsb_c : ∀ (fuel m : Nat),
        (runMSBFromOCNAux dzM dpM initM fuel m).2 ≤ initM.2 + binBitLength m := by
      intro fuel; induction fuel with
      | zero => intro m; simp [runMSBFromOCNAux]
      | succ fuel' ih =>
        intro m
        simp only [runMSBFromOCNAux]
        by_cases hm0 : m = 0
        · subst hm0; simp
        · simp only [hm0, ite_false]
          rw [binBitLength_step_pos m (by omega)]
          have hst := stepOCN_counter_le_succ dzM dpM
            (runMSBFromOCNAux dzM dpM initM fuel' (m / 2)) (m % 2 == 1)
          have hih := ih (m / 2)
          omega
    let F_den := sumAllJointModes Q_L Q_M fDen Q_L (Nat.le_refl Q_L)
    let S := initL.2 + initM.2 + 1
    let d := maxDegNatPoly3 qTerms3
    apply eventual_poly_bitlength_denominator_preimage_impossibility.2 M_0 hM0 _ _
      (F_den * (evalNatPoly3 qTerms3 1 1 1 * S ^ d)) d pTheta qTheta
    intro n hnM0
    have hL_pos : binBitLength n ≥ 1 := hbl_pos3 n (by omega)
    have hS_pos : S ≥ 1 := by omega
    have hf_le : fDen (ocnObservableMode (runLSBFromOCN dzL dpL n initL))
                      (ocnObservableMode (runMSBFromOCN dzM dpM n initM)) ≤ F_den :=
      le_sumAllJointModes Q_L Q_M fDen Q_L (Nat.le_refl Q_L) _ _
        (ocnObservableMode (runLSBFromOCN dzL dpL n initL)).1.isLt
    have hl_ub : (runLSBFromOCN dzL dpL n initL).2 ≤ S * binBitLength n := by
      unfold runLSBFromOCN
      have hb := hlsb_c n n initL
      rw [Nat.add_mul (initL.2 + initM.2) 1 (binBitLength n), Nat.one_mul, Nat.add_mul]
      have hm := Nat.mul_le_mul_left initL.2 hL_pos
      omega
    have hm_ub : (runMSBFromOCN dzM dpM n initM).2 ≤ S * binBitLength n := by
      unfold runMSBFromOCN
      have hb := hmsb_c n n
      rw [Nat.add_mul (initL.2 + initM.2) 1 (binBitLength n), Nat.one_mul, Nat.add_mul]
      have hm := Nat.mul_le_mul_left initM.2 hL_pos
      omega
    have hz_ub : binBitLength n ≤ S * binBitLength n := by
      simpa using Nat.mul_le_mul_right (binBitLength n) hS_pos
    have hp_ub := hpoly3_scaled_ub qTerms3 S _ _ (binBitLength n) (binBitLength n)
      hS_pos hL_pos hl_ub hm_ub hz_ub
    have hm := Nat.mul_le_mul hf_le hp_ub
    rwa [← Nat.mul_assoc F_den (evalNatPoly3 qTerms3 1 1 1 * S ^ d)] at hm

-- ----------------------------------------------------------------------------
-- Section 3B: 8th Solvable Mixed-(2, 3) Cousin `T_diamond8` (`ω^6` Cascade, `Branch P5.10`)
-- ----------------------------------------------------------------------------

/-- Cone 9 of `T_diamond8`: `92275 + x = 2 ^ u * 3 ^ v` with `u ≥ 25, v ≥ 1` (starting at `x = 100571021`). -/
def isDiamond8Cone9 (x : Nat) : Prop :=
  x ≥ 100571021 ∧ x % 33554432 = 33462157 ∧ x % 3 = 2 ∧ coprime23Core (92275 + x) = 1

instance (x : Nat) : Decidable (isDiamond8Cone9 x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/--
  8th solvable mixed-(2, 3) Collatz cousin `T_diamond8` on `Nat`:
  Extends `T_diamond7` by adding Cone 9 (`isDiamond8Cone9 x -> (3 * x + 1) / 8`, a genuine
  `v_2(3x + 1) = 3` Syracuse jump that steps `2 ^ u * 3 ^ v - 92275 -> 2 ^ (u - 3) * 3 ^ (v + 1) - 34603`
  directly into Cone 8 -> Cone 7 -> Cone 6 -> Cone 5's `r`-block spiral climb, e.g.
  `100571021 -> 37714133 -> 883925 -> 20717 -> 7769 -> ... -> 1` in `16` steps,
  exhibiting a genuine 6-tier `ω^6` cascade defeating 5-tier `ω^5` rankings)!
-/
def cousinDiamond8Step (x : Nat) : Nat :=
  if isDiamond8Cone9 x then (3 * x + 1) / 8 else cousinDiamond7Step x

def cousinDiamond8Iter : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamond8Iter k (cousinDiamond8Step x)

theorem cousinDiamond8Iter_add : ∀ (a b x : Nat),
    cousinDiamond8Iter (a + b) x = cousinDiamond8Iter b (cousinDiamond8Iter a x)
  | 0, _, _ => by simp [cousinDiamond8Iter]
  | a + 1, b, x => by
    rw [Nat.succ_add]
    exact cousinDiamond8Iter_add a b (cousinDiamond8Step x)

/-- Signed extension of `T_diamond8` (`q = 3`) to `Int` for `M2 = Z^-` separation. -/
def cousinDiamond8StepInt (x : Int) : Int :=
  if x ≥ 100571021 ∧ x % 33554432 = 33462157 ∧ x % 3 = 2 ∧ coprime23Core (92275 + x.toNat) = 1
  then (3 * x + 1) / 8
  else cousinDiamond7StepInt x

def cousinDiamond8IterInt : Nat -> Int -> Int
  | 0, x => x
  | k + 1, x => cousinDiamond8IterInt k (cousinDiamond8StepInt x)

/-- Hensel lift of `invMod4194304Odd` (`2^22`) to `mod 33554432` (`2^25`, since `22 * 2 = 44 ≥ 25`). -/
def invMod33554432Odd (d : Nat) : Nat :=
  let i4m := invMod4194304Odd d
  (i4m * (67108866 - ((d % 33554432) * i4m) % 33554432)) % 33554432

/-- Canonical reduced-pair extension of `T_diamond8` (`q = 3`) to positive `Q_(6)^+`. -/
def cousinDiamond8StepQ6 (p : Nat × Nat) : Nat × Nat :=
  let num := p.1
  let den := p.2
  let r33m := (num * invMod33554432Odd den) % 33554432
  let r3 := (num * (den % 3)) % 3
  if num ≥ 100571021 * den ∧ r33m = 33462157 ∧ r3 = 2 ∧ core3 (core2 (92275 * den + num)) = den
  then reduceRatPair (3 * num + den) (8 * den)
  else cousinDiamond7StepQ6 p

def cousinDiamond8IterQ6 : Nat -> (Nat × Nat) -> (Nat × Nat)
  | 0, p => p
  | k + 1, p => cousinDiamond8IterQ6 k (cousinDiamond8StepQ6 p)

/-- Generalized odd-multiplier `q` step of `T_diamond8` on `Nat` for `M3` (`q = 7`) separation. -/
def cousinDiamond8StepParam (q x : Nat) : Nat :=
  if isDiamond8Cone9 x then (q * x + 1) / 8 else cousinDiamond7StepParam q x

def cousinDiamond8IterParam (q : Nat) : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamond8IterParam q k (cousinDiamond8StepParam q x)

/--
  Theorem W11.3b (`cousinDiamond8StepInt_ofNat_eq`, `zero custom axioms`):
  Exact `Nat`/`Int` step agreement for `T_diamond8` (`∀ x : Nat`).
-/
theorem cousinDiamond8StepInt_ofNat_eq (x : Nat) :
    cousinDiamond8StepInt (x : Int) = (cousinDiamond8Step x : Int) := by
  have h1 : ((x : Int) ≥ 100571021) ↔ (x ≥ 100571021) := by omega
  have h2 : ((x : Int) % 33554432 = 33462157) ↔ (x % 33554432 = 33462157) :=
    ⟨Int.ofNat.inj, congrArg Int.ofNat⟩
  have h3 : ((x : Int) % 3 = 2) ↔ (x % 3 = 2) :=
    ⟨Int.ofNat.inj, congrArg Int.ofNat⟩
  have hdiv : ((3 * (x : Int) + 1) / 8) = (((3 * x + 1) / 8 : Nat) : Int) := by omega
  have htoNat : (x : Int).toNat = x := rfl
  unfold cousinDiamond8StepInt cousinDiamond8Step isDiamond8Cone9
  rw [htoNat]
  simp only [h1, h2, h3]
  by_cases hc9 : x ≥ 100571021 ∧ x % 33554432 = 33462157 ∧ x % 3 = 2 ∧ coprime23Core (92275 + x) = 1
  · simp only [hc9, and_self, ite_true, hdiv]
  · simp only [hc9, ite_false]
    exact cousinDiamond7StepInt_ofNat_eq x

theorem cousinDiamond8Step_pos (x : Nat) (hx : x > 0) : cousinDiamond8Step x > 0 := by
  unfold cousinDiamond8Step
  by_cases hc9 : isDiamond8Cone9 x
  · simp only [hc9, ite_true]
    have hge : x ≥ 100571021 := hc9.1
    clear hc9
    have hle : (3 * 100571021 + 1) / 8 ≤ (3 * x + 1) / 8 :=
      Nat.div_le_div_right (by omega)
    exact Nat.lt_of_lt_of_le (by decide : 0 < (3 * 100571021 + 1) / 8) hle
  · simp only [hc9, ite_false]; exact cousinDiamond7Step_pos x hx

theorem cousinDiamond8Step_eq_d7_of_not_cone9 (x : Nat) (hnc9 : ¬ isDiamond8Cone9 x) :
    cousinDiamond8Step x = cousinDiamond7Step x := by
  unfold cousinDiamond8Step; simp [hnc9]

/--
  Theorem W11.3c (`cousin_diamond8_outside_cones4to9_strict_descent`, `zero custom axioms`):
  Outside Cones 4, 5, 6, 7, 8, and 9, EVERY `x > 2` strictly decreases `cousinDiamond2Phi` in 1 step!
-/
theorem cousin_diamond8_outside_cones4to9_strict_descent
    (x : Nat) (hx : x > 2)
    (hnc4 : ¬ isDiamond3Cone4 x) (hnc5 : ¬ isDiamond4Cone5 x)
    (hnc6 : ¬ isDiamond5Cone6 x) (hnc7 : ¬ isDiamond6Cone7 x)
    (hnc8 : ¬ isDiamond7Cone8 x) (hnc9 : ¬ isDiamond8Cone9 x) :
    cousinDiamond2Phi (cousinDiamond8Step x) < cousinDiamond2Phi x := by
  rw [cousinDiamond8Step_eq_d7_of_not_cone9 x hnc9]
  exact cousin_diamond7_outside_cones45678_strict_descent x hx hnc4 hnc5 hnc6 hnc7 hnc8

-- Modular Cone-9 avoidance helpers (`33462157 % 256 = 141, % 32 = 13, % 16 = 13, % 8 = 5, % 4 = 1, % 2 = 1`):

theorem mod256_of_cone9 (z : Nat) (hc9 : isDiamond8Cone9 z) : z % 256 = 141 := by
  have h := congrArg (· % 256) hc9.2.1
  rwa [Nat.mod_mod_of_dvd z (by decide : 256 ∣ 33554432)] at h

theorem mod32_of_cone9 (z : Nat) (hc9 : isDiamond8Cone9 z) : z % 32 = 13 := by
  have h := congrArg (· % 32) (mod256_of_cone9 z hc9)
  rwa [Nat.mod_mod_of_dvd z (by decide : 32 ∣ 256)] at h

theorem not_cone9_of_even (z : Nat) (hev : z % 2 = 0) : ¬ isDiamond8Cone9 z := by
  intro hc9
  have h := congrArg (· % 2) (mod32_of_cone9 z hc9)
  rw [Nat.mod_mod_of_dvd z (by decide : 2 ∣ 32), hev] at h
  cases h

theorem not_cone9_of_mod4_eq_3 (z : Nat) (hm4 : z % 4 = 3) : ¬ isDiamond8Cone9 z := by
  intro hc9
  have h := congrArg (· % 4) (mod32_of_cone9 z hc9)
  rw [Nat.mod_mod_of_dvd z (by decide : 4 ∣ 32), hm4] at h
  cases h

theorem not_cone9_of_mod8_ne_5 (z : Nat) (hm8 : z % 8 ≠ 5) : ¬ isDiamond8Cone9 z := by
  intro hc9
  have h := congrArg (· % 8) (mod32_of_cone9 z hc9)
  rw [Nat.mod_mod_of_dvd z (by decide : 8 ∣ 32)] at h
  exact hm8 h

theorem not_cone9_of_mod16_ne_13 (z : Nat) (hm16 : z % 16 ≠ 13) : ¬ isDiamond8Cone9 z := by
  intro hc9
  have h := congrArg (· % 16) (mod32_of_cone9 z hc9)
  rw [Nat.mod_mod_of_dvd z (by decide : 16 ∣ 32)] at h
  exact hm16 h

theorem not_cone9_of_mod32_ne_13 (z : Nat) (hm32 : z % 32 ≠ 13) : ¬ isDiamond8Cone9 z :=
  fun hc9 => hm32 (mod32_of_cone9 z hc9)

theorem not_cone9_of_mod256_ne_141 (z : Nat) (hm256 : z % 256 ≠ 141) : ¬ isDiamond8Cone9 z :=
  fun hc9 => hm256 (mod256_of_cone9 z hc9)

theorem not_cone9_of_mod3_ne_2 (z : Nat) (hm3 : z % 3 ≠ 2) : ¬ isDiamond8Cone9 z := by
  rintro ⟨_, _, h3, _⟩; exact hm3 h3

theorem not_cone9_six_mul_pow9_sub1 (m : Nat) :
    ¬ isDiamond8Cone9 (6 * 9 ^ m - 1) := by
  apply not_cone9_of_mod16_ne_13
  have h9_16 : ∀ r : Nat, 9 ^ r % 16 = 1 ∨ 9 ^ r % 16 = 9 := by
    intro r; induction r with
    | zero => left; rfl
    | succ r' ih =>
      rw [Nat.pow_succ, Nat.mul_mod]
      rcases ih with h1 | h9
      · right; rw [h1]
      · left; rw [h9]
  have hp9 := nat_pow_pos_of_pos 9 (by decide) m
  have hdm := (Nat.div_add_mod (9 ^ m) 16).symm
  rcases h9_16 m with h1 | h9 <;> omega

theorem isDiamond7Cone8_of_pow2_pow3 (u v : Nat) (hu : u ≥ 22) (hv : v ≥ 1) :
    isDiamond7Cone8 (2 ^ u * 3 ^ v - 34603) := by
  have hc : (2 : Nat) ^ 22 = 4194304 := by decide
  have hp2_ge : 2 ^ u ≥ 4194304 := by
    rw [← hc]; exact pow2_mono_nat hu
  have hp3_ge : 3 ^ v ≥ 3 := by
    simpa using nat_pow_mono_exp_pos 3 1 v (by decide) hv
  have hprod_ge : 2 ^ u * 3 ^ v ≥ 12582912 := by
    simpa using Nat.mul_le_mul hp2_ge hp3_ge
  have hp4m : 4194304 ∣ 2 ^ u * 3 ^ v := by
    have hsp : u = 22 + (u - 22) := by omega
    rw [hsp, Nat.pow_add 2 22 (u - 22), hc, Nat.mul_assoc]
    exact ⟨2 ^ (u - 22) * 3 ^ v, rfl⟩
  have hp3_div : 3 ∣ 2 ^ u * 3 ^ v := by
    have hsp : v = 1 + (v - 1) := by omega
    rw [hsp, Nat.pow_add 3 1 (v - 1), Nat.pow_one,
        ← Nat.mul_assoc (2 ^ u) 3, Nat.mul_comm (2 ^ u) 3, Nat.mul_assoc]
    exact ⟨2 ^ u * 3 ^ (v - 1), rfl⟩
  refine ⟨by clear hc hp2_ge hp3_ge hp4m hp3_div; generalize 2 ^ u * 3 ^ v = P at hprod_ge ⊢; omega,
          ?_, ?_, ?_⟩
  · rcases hp4m with ⟨q, hq⟩
    clear hc hp2_ge hp3_ge hp3_div
    generalize 2 ^ u * 3 ^ v = P at hprod_ge hq ⊢
    have hq_ge : q ≥ 3 := by omega
    rw [hq, show q = (q - 1) + 1 by omega, Nat.mul_add 4194304 (q - 1) 1, Nat.mul_one]
    generalize q - 1 = q'
    have hsub : 4194304 * q' + 4194304 - 34603 = 4159701 + 4194304 * q' := by omega
    rw [hsub, Nat.add_mul_mod_self_left]
  · rcases hp3_div with ⟨q3, hq3⟩
    clear hc hp2_ge hp3_ge hp4m
    generalize 2 ^ u * 3 ^ v = P at hprod_ge hq3 ⊢
    omega
  · have hadd : 34603 + (2 ^ u * 3 ^ v - 34603) = 2 ^ u * 3 ^ v := by
      clear hc hp2_ge hp3_ge hp4m hp3_div
      generalize 2 ^ u * 3 ^ v = P at hprod_ge ⊢
      omega
    rw [hadd]
    exact coprime23Core_pow2_pow3 u v

theorem cousin_diamond8_mersenne_scaled :
    ∀ (k a q : Nat), k + 1 ≤ a -> q ≥ 1 ->
      cousinDiamond8Iter k (2 ^ a * q - 1) = 3 ^ k * 2 ^ (a - k) * q - 1
  | 0, _, _, _, _ => by simp [cousinDiamond8Iter]
  | k + 1, a, q, hka, hq => by
    have hp4 : 2 ^ a * q = 4 * (2 ^ (a - 2) * q) := by
      conv => lhs; rw [show a = (a - 2) + 2 by omega]
      rw [Nat.pow_add 2 (a - 2) 2, show (2 : Nat) ^ 2 = 4 from rfl,
          Nat.mul_comm (2 ^ (a - 2)) 4, Nat.mul_assoc]
    have hm_pos : 2 ^ (a - 2) * q ≥ 1 := Nat.mul_le_mul (pow2_pos_nat (a - 2)) hq
    have hz4 : (2 ^ a * q - 1) % 4 = 3 := by omega
    simp only [cousinDiamond8Iter]
    rw [cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_mod4_eq_3 _ hz4)]
    have hd7 := cousin_diamond7_mersenne_scaled 1 a q (by omega) hq
    simp only [cousinDiamond7Iter, Nat.pow_one] at hd7
    have hstep_eq : cousinDiamond7Step (2 ^ a * q - 1) = 2 ^ (a - 1) * (3 * q) - 1 := by
      rw [hd7]
      apply congrArg (· - 1)
      rw [Nat.mul_comm 3 (2 ^ (a - 1)), Nat.mul_assoc]
    rw [hstep_eq, cousin_diamond8_mersenne_scaled k (a - 1) (3 * q) (by omega) (by omega),
        show a - 1 - k = a - (k + 1) by omega, Nat.pow_succ 3 k]
    apply congrArg (· - 1)
    calc
      3 ^ k * 2 ^ (a - (k + 1)) * (3 * q)
          = 3 ^ k * (2 ^ (a - (k + 1)) * 3) * q := by rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
      _ = 3 ^ k * (3 * 2 ^ (a - (k + 1))) * q := by rw [Nat.mul_comm (2 ^ (a - (k + 1))) 3]
      _ = 3 ^ k * 3 * 2 ^ (a - (k + 1)) * q := by rw [← Nat.mul_assoc (3 ^ k) 3]

theorem cousin_diamond8_even9_spine_drain :
    ∀ k : Nat, cousinDiamond8Iter k ((9 ^ (k + 1) - 1) / 4) = 2
  | 0 => rfl
  | k + 1 => by
    let j := k + 1
    have hp9j_ge9 : 9 ^ j ≥ 9 := by
      dsimp [j]; rw [Nat.pow_succ]; have hp := nat_pow_pos_of_pos 9 (by decide) k; omega
    have hp9j_m8 : 9 ^ j % 8 = 1 := pow9_mod8_eq_one_w5 j
    let q := (9 ^ j - 1) / 8
    have hp9j_eq : 9 ^ j = 8 * q + 1 := by dsimp [q]; omega
    have he_j1 : (9 ^ (j + 1) - 1) / 4 = 18 * q + 2 := by rw [Nat.pow_succ 9 j, hp9j_eq]; omega
    simp only [cousinDiamond8Iter]
    change cousinDiamond8Iter k (cousinDiamond8Step ((9 ^ (j + 1) - 1) / 4)) = 2
    have hnc9 : ¬ isDiamond8Cone9 ((9 ^ (j + 1) - 1) / 4) := by
      rw [he_j1]; exact not_cone9_of_even _ (by omega)
    rw [cousinDiamond8Step_eq_d7_of_not_cone9 _ hnc9]
    have hd7 : cousinDiamond7Step ((9 ^ (j + 1) - 1) / 4) = (9 ^ j - 1) / 4 := by
      have he_j : (9 ^ j - 1) / 4 = 2 * q := by rw [hp9j_eq]; omega
      rw [he_j1, he_j,
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (18 * q + 2) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]; unfold cousinDiamond3Step
      have hq_pos : q ≥ 1 := by dsimp [q]; omega
      have hodd_f : ¬ ((18 * q + 2) % 2 = 1) := by omega
      have h18_t : 18 * q + 2 ≥ 20 ∧ (18 * q + 2) % 18 = 2 := ⟨by omega, by omega⟩
      simp only [hodd_f, h18_t, and_self, ite_true, ite_false]; omega
    rw [hd7]
    exact cousin_diamond8_even9_spine_drain k

theorem cousin_diamond8_pow3_sub1_drain :
    ∀ k : Nat, cousinDiamond8Iter k (3 ^ (k + 1) - 1) = 2
  | 0 => rfl
  | k + 1 => by
    let j := k + 1
    have hp3_ge3 : 3 ^ j ≥ 3 := by dsimp [j]; rw [Nat.pow_succ]; have hp := pow3_pos_nat k; omega
    have ho_j1 := pow3_odd_nat_sec8 (j + 1)
    have hp_j1 := pow3_pos_nat (j + 1)
    simp only [cousinDiamond8Iter]
    change cousinDiamond8Iter k (cousinDiamond8Step (3 ^ (j + 1) - 1)) = 2
    rw [cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
        cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
        cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
        cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
    have hd4 : cousinDiamond4Step (3 ^ (j + 1) - 1) = 3 ^ j - 1 := by
      have hev : ¬ ((3 ^ (j + 1) - 1) % 2 = 1) := by omega
      have hnc5 : ¬ isDiamond4Cone5 (3 ^ (j + 1) - 1) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h3j1 : 3 ^ (j + 1) = 3 * 3 ^ j := by rw [Nat.pow_succ, Nat.mul_comm]
      have hn18 : ¬ (3 ^ (j + 1) - 1 ≥ 20 ∧ (3 ^ (j + 1) - 1) % 18 = 2) := by
        rintro ⟨h20, hm18⟩
        cases k with
        | zero => simp [j] at h20
        | succ k' =>
          have h9 : 3 ^ (j + 1) = 9 * (3 * 3 ^ k') := by
            dsimp [j]; rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]; omega
          have ho' := pow3_odd_nat_sec8 k'; omega
      have hm6 : 3 ^ (j + 1) - 1 > 2 ∧ (3 ^ (j + 1) - 1) % 6 = 2 := by rw [h3j1]; omega
      unfold cousinDiamond3Step
      simp only [hev, hn18, hm6, and_self, ite_true, ite_false]
      rw [h3j1]; omega
    rw [hd4]
    exact cousin_diamond8_pow3_sub1_drain k

theorem cousin_diamond8_cone5_two_step_climb :
    ∀ (q_c a b : Nat), 3 * q_c + 2 ≤ a -> b ≥ 1 ->
      cousinDiamond8Iter (2 * q_c) (2 ^ a * 3 ^ b - 7) =
        2 ^ (a - 3 * q_c) * 3 ^ (b + 2 * q_c) - 7
  | 0, _, _, _, _ => by simp [cousinDiamond8Iter]
  | q_c + 1, a, b, ha, hb => by
    have ha5 : a ≥ 5 := by omega
    have hc5 := isDiamond4Cone5_of_pow2_pow3 a b ha5 hb
    have hnc9_0 : ¬ isDiamond8Cone9 (2 ^ a * 3 ^ b - 7) :=
      not_cone9_of_mod32_ne_13 _ (by have h := hc5.2.1; omega)
    let mid := 2 ^ (a - 2) * 3 ^ (b + 1) - 5
    have hmid_4 : mid % 4 = 3 := by
      dsimp [mid]
      have hp8 : 2 ^ (a - 2) = 8 * 2 ^ (a - 5) := by
        conv => lhs; rw [show a - 2 = 3 + (a - 5) by omega]; rw [Nat.pow_add]
      rw [hp8, Nat.mul_assoc 8]
      have hp_pos : 2 ^ (a - 5) * 3 ^ (b + 1) ≥ 1 :=
        Nat.mul_le_mul (pow2_pos_nat _) (pow3_pos_nat _)
      omega
    have hnc9_1 : ¬ isDiamond8Cone9 mid := not_cone9_of_mod4_eq_3 mid hmid_4
    have hd7_2 := cousin_diamond7_cone5_two_step_climb 1 a b (by omega) hb
    simp only [Nat.mul_one, cousinDiamond7Iter] at hd7_2
    have hd7_s1 : cousinDiamond7Step (2 ^ a * 3 ^ b - 7) = mid := by
      rw [cousinDiamond7Step_eq_d6_of_not_cone8 _
            (not_cone8_of_mod32_ne_21 _ (by have h := hc5.2.1; omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _
            (not_cone7_of_mod32_ne_21 _ (by have h := hc5.2.1; omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _
            (not_cone6_of_mod32_ne_13 _ (by have h := hc5.2.1; omega))]
      unfold cousinDiamond4Step; simp only [hc5, ite_true]
      dsimp [mid]
      have hp4 : 2 ^ a = 4 * 2 ^ (a - 2) := by
        conv => lhs; rw [show a = 2 + (a - 2) by omega]; rw [Nat.pow_add]
      have hp_pos : 2 ^ (a - 2) * 3 ^ b ≥ 8 * 3 := by
        have h1 : 8 ≤ 2 ^ (a - 2) := by
          have hc : (2 : Nat) ^ 3 = 8 := by decide
          rw [← hc]; exact pow2_mono_nat (by omega)
        have h2 : 3 ≤ 3 ^ b := by simpa using nat_pow_mono_exp_pos 3 1 b (by decide) hb
        simpa using Nat.mul_le_mul h1 h2
      have h3_eq : 2 ^ (a - 2) * 3 ^ (b + 1) = 3 * (2 ^ (a - 2) * 3 ^ b) := by
        rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm _ 3]
      rw [hp4, Nat.mul_assoc 4, h3_eq]
      generalize 2 ^ (a - 2) * 3 ^ b = A at hp_pos ⊢
      omega
    rw [hd7_s1] at hd7_2
    have hs1 : cousinDiamond8Step (2 ^ a * 3 ^ b - 7) = mid := by
      rw [cousinDiamond8Step_eq_d7_of_not_cone9 _ hnc9_0]; exact hd7_s1
    have hs2 : cousinDiamond8Step mid = 2 ^ (a - 3) * 3 ^ (b + 2) - 7 := by
      rw [cousinDiamond8Step_eq_d7_of_not_cone9 _ hnc9_1]; exact hd7_2
    rw [Nat.mul_succ 2 q_c, Nat.add_comm (2 * q_c) 2,
        cousinDiamond8Iter_add 2 (2 * q_c)]
    have hi2 : cousinDiamond8Iter 2 (2 ^ a * 3 ^ b - 7) = 2 ^ (a - 3) * 3 ^ (b + 2) - 7 := by
      simp only [cousinDiamond8Iter, hs1, hs2]
    rw [hi2, cousin_diamond8_cone5_two_step_climb q_c (a - 3) (b + 2) (by omega) (by omega)]
    apply congrArg (· - 7)
    congr 1
    · apply congrArg (2 ^ ·); omega
    · apply congrArg (3 ^ ·); omega

theorem cousin_diamond8_a0_3_drain (b0 : Nat) (hb0 : b0 ≥ 3) :
    cousinDiamond8Step (8 * 3 ^ b0 - 7) = 12 * 3 ^ b0 - 10 ∧
    cousinDiamond8Step (12 * 3 ^ b0 - 10) = 4 * 3 ^ b0 - 4 ∧
    cousinDiamond8Step (4 * 3 ^ b0 - 4) = 4 * 3 ^ (b0 - 1) - 2 ∧
    cousinDiamond8Iter ((b0 - 1) / 2 + 7) (8 * 3 ^ b0 - 7) = 1 := by
  rcases cousin_diamond7_a0_3_drain b0 hb0 with ⟨hd7_1, hd7_2, hd7_3, _⟩
  have hp3_ge27 : 3 ^ b0 ≥ 27 := by
    simpa using nat_pow_mono_exp_pos 3 3 b0 (by decide) hb0
  have hp3_b1_ge9 : 3 ^ (b0 - 1) ≥ 9 := by
    simpa using nat_pow_mono_exp_pos 3 2 (b0 - 1) (by decide) (by omega)
  have hp3_b2_ge3 : 3 ^ (b0 - 2) ≥ 3 := by
    simpa using nat_pow_mono_exp_pos 3 1 (b0 - 2) (by decide) (by omega)
  have hnc9_1 : ¬ isDiamond8Cone9 (8 * 3 ^ b0 - 7) := by
    apply not_cone9_of_mod32_ne_13
    have ho := pow3_odd_nat_sec8 b0
    omega
  have hs1 : cousinDiamond8Step (8 * 3 ^ b0 - 7) = 12 * 3 ^ b0 - 10 := by
    rw [cousinDiamond8Step_eq_d7_of_not_cone9 _ hnc9_1]; exact hd7_1
  have hs2 : cousinDiamond8Step (12 * 3 ^ b0 - 10) = 4 * 3 ^ b0 - 4 := by
    rw [cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega))]; exact hd7_2
  have hs3 : cousinDiamond8Step (4 * 3 ^ b0 - 4) = 4 * 3 ^ (b0 - 1) - 2 := by
    rw [cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega))]; exact hd7_3
  refine ⟨hs1, hs2, hs3, ?_⟩
  by_cases hev_b1 : (b0 - 1) % 2 = 0
  · -- `b0 - 1 = 2 * m` (`m ≥ 1`): `4 * 3^(b0 - 1) - 2` steps to `2 * 9^m - 1`:
    let m := (b0 - 1) / 2
    have hm1 : m ≥ 1 := by dsimp [m]; omega
    have hb1_eq : b0 - 1 = 2 * m := by dsimp [m]; omega
    have hp9_ge9 : 9 ^ m ≥ 9 := by rw [pow9_eq_pow3_double m, ← hb1_eq]; exact hp3_b1_ge9
    have hp9_m8 : 9 ^ m % 8 = 1 := pow9_mod8_eq_one_w5 m
    have h4_eq : 4 * 3 ^ (b0 - 1) - 2 = 4 * 9 ^ m - 2 := by
      rw [hb1_eq, ← pow9_eq_pow3_double m]
    let zr := 2 * 9 ^ m - 1
    let yr := (3 * 9 ^ m - 1) / 2
    have hs4 : cousinDiamond8Step (4 * 9 ^ m - 2) = zr := by
      rw [cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (4 * 9 ^ m - 2) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have hn18 : ¬ (4 * 9 ^ m - 2 ≥ 20 ∧ (4 * 9 ^ m - 2) % 18 = 2) := by
        have h9m9 : 9 ^ m % 9 = 0 := by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
        omega
      have hn6 : ¬ (4 * 9 ^ m - 2 > 2 ∧ (4 * 9 ^ m - 2) % 6 = 2) := by
        have h9m3 : 9 ^ m % 3 = 0 := by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
        omega
      have hn8 : ¬ (4 * 9 ^ m - 2 > 2 ∧ (4 * 9 ^ m - 2) % 8 = 6) := by omega
      rw [cousinDiamond3Step_even_plain_half_w8 _ (by omega) hn18 hn6 hn8]
      dsimp [zr]; omega
    have hsz : cousinDiamond8Step zr = yr := by
      rw [cousinDiamond8Step_eq_d7_of_not_cone9 zr (not_cone9_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 zr (not_cone8_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 zr (not_cone7_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 zr (not_cone6_of_mod16_ne_13 zr (by dsimp [zr]; omega))]
      have hnc5 : ¬ isDiamond4Cone5 zr := by rintro ⟨_, h32, _, _⟩; dsimp [zr] at h32; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 zr hnc5]
      have hc3 : core3 (zr + 1) = 2 := by
        rw [show zr + 1 = 2 * 9 ^ m by dsimp [zr]; omega,
            core3_mul2 (9 ^ m) (by omega), (pow9_eq_v3Pow_w5 m).2]
      rw [cousinDiamond3Step_of_core3_succ_two_w8 zr (by dsimp [zr]; omega) (by dsimp [zr]; omega) hc3]
      dsimp [zr, yr]; omega
    have hsy : cousinDiamond8Step yr = (9 ^ (m + 1) - 1) / 4 := by
      have hyr_m3 : yr % 3 = 1 := by
        have hm3 : 9 ^ m % 3 = 0 := by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
        dsimp [yr]; omega
      rw [cousinDiamond8Step_eq_d7_of_not_cone9 yr (not_cone9_of_mod3_ne_2 yr (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 yr (not_cone8_of_mod3_ne_2 yr (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 yr (not_cone7_of_mod9_ne_8 yr (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 yr (not_cone6_of_mod9_ne_8 yr (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 yr := by rintro ⟨_, _, hm3, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 yr hnc5]
      have hc3_2 : core3 (2 * yr + 1) = 1 := by
        rw [show 2 * yr + 1 = 3 * 9 ^ m by dsimp [yr]; omega,
            core3_mul3 (9 ^ m) (by omega), (pow9_eq_v3Pow_w5 m).2]
      have hc3_1 : core3 (yr + 1) ≠ 2 := by
        have hnd3 : (yr + 1) % 3 ≠ 0 := by
          clear hd7_1 hd7_2 hd7_3 hs1 hs2 hs3 h4_eq hs4 hsz hnc5 hc3_2
          omega
        rw [core3_not_div3 (yr + 1) hnd3]
        clear hd7_1 hd7_2 hd7_3 hs1 hs2 hs3 h4_eq hs4 hsz hnc5 hc3_2
        dsimp [yr]; omega
      have hnc4 : ¬ isDiamond3Cone4 yr := by
        rintro ⟨hge169, _, hc2⟩
        by_cases hm_eq1 : m = 1
        · clear hd7_1 hd7_2 hd7_3 hs1 hs2 hs3 h4_eq hs4 hsz hnc5 hc3_2 hc3_1 hc2
          dsimp only [yr] at hge169
          rw [hm_eq1] at hge169
          omega
        · have hm2 : m ≥ 2 := by
            clear hd7_1 hd7_2 hd7_3 hs1 hs2 hs3 h4_eq hs4 hsz hnc5 hc3_2 hc3_1 hge169 hc2
            omega
          rcases eq_pow2_of_core2_eq_one (3 * yr + 5)
            (by clear hd7_1 hd7_2 hd7_3 hs1 hs2 hs3 h4_eq hs4 hsz hnc5 hc3_2 hc3_1; dsimp [yr]; omega) hc2 with
            ⟨M0, hM0⟩
          have h9_eq : 9 ^ (m + 1) + 7 = 2 ^ (M0 + 1) := by
            have h2mul : 2 * (3 * yr + 5) = 9 ^ (m + 1) + 7 := by
              clear hd7_1 hd7_2 hd7_3 hs1 hs2 hs3 h4_eq hs4 hsz hnc5 hc3_2 hc3_1 hc2 hM0
              rw [Nat.pow_succ 9 m, Nat.mul_comm (9 ^ m) 9]; dsimp [yr]; omega
            rw [← h2mul, hM0, Nat.pow_succ 2 M0, Nat.mul_comm]
          exact pow9_succ_add_seven_ne_pow2 m (M0 + 1) hm2 h9_eq
      rw [cousinDiamond3Step_odd_half_w8 yr (by dsimp [yr]; omega) hnc4 hc3_2 hc3_1]
      dsimp [yr]; rw [Nat.pow_succ 9 m]; omega
    change cousinDiamond8Iter (m + 7) (8 * 3 ^ b0 - 7) = 1
    rw [show m + 7 = 4 + 1 + 1 + m + 1 by omega,
        cousinDiamond8Iter_add (4 + 1 + 1 + m) 1,
        cousinDiamond8Iter_add (4 + 1 + 1) m,
        cousinDiamond8Iter_add (4 + 1) 1,
        cousinDiamond8Iter_add 4 1]
    have hi4 : cousinDiamond8Iter 4 (8 * 3 ^ b0 - 7) = zr := by
      simp only [cousinDiamond8Iter, hs1, hs2, hs3, h4_eq, hs4]
    rw [hi4]
    have hiz : cousinDiamond8Iter 1 zr = yr := hsz
    rw [hiz]
    have hiy : cousinDiamond8Iter 1 yr = (9 ^ (m + 1) - 1) / 4 := hsy
    rw [hiy, cousin_diamond8_even9_spine_drain m]
    decide
  · -- `b0 - 1 = 2 * m + 1` (`m ≥ 1`): `4 * 3^(b0 - 1) - 2 = 12 * 9^m - 2 -> 6 * 9^m - 1`:
    let m := (b0 - 1) / 2
    have hm1 : m ≥ 1 := by dsimp [m]; omega
    have hb1_eq : b0 - 1 = 2 * m + 1 := by dsimp [m]; omega
    have hp9_ge9 : 9 ^ m ≥ 9 := by
      rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]
      have hp := nat_pow_pos_of_pos 9 (by decide) (m - 1); omega
    have hp9_m8 : 9 ^ m % 8 = 1 := pow9_mod8_eq_one_w5 m
    let ur := 6 * 9 ^ m - 1
    let wr := (9 ^ (m + 1) - 1) / 2
    have hu_eq : 4 * 3 ^ (b0 - 1) - 2 = 12 * 9 ^ m - 2 := by
      rw [hb1_eq, Nat.pow_succ 3 (2 * m), ← pow9_eq_pow3_double m]; omega
    have hs4 : cousinDiamond8Step (12 * 9 ^ m - 2) = ur := by
      rw [cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (12 * 9 ^ m - 2) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h9m9 : 9 ^ m % 9 = 0 := by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
      rw [cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) (by omega)]
      dsimp [ur]; omega
    have hsu : cousinDiamond8Step ur = wr := by
      rw [cousinDiamond8Step_eq_d7_of_not_cone9 ur (not_cone9_six_mul_pow9_sub1 m),
          cousinDiamond7Step_eq_d6_of_not_cone8 ur (not_cone8_six_mul_pow9_sub1 m),
          cousinDiamond6Step_eq_d5_of_not_cone7 ur (not_cone7_six_mul_pow9_sub1 m),
          cousinDiamond5Step_eq_d4_of_not_cone6 ur (not_cone6_of_mod16_ne_13 ur (by dsimp [ur]; omega))]
      have hnc5 : ¬ isDiamond4Cone5 ur := by rintro ⟨_, h32, _, _⟩; dsimp [ur] at h32; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 ur hnc5]
      have hc3 : core3 (ur + 1) = 2 := by
        rw [show ur + 1 = 2 * (3 * 9 ^ m) by dsimp [ur]; omega,
            core3_mul2 (3 * 9 ^ m) (by omega),
            core3_mul3 (9 ^ m) (by omega), (pow9_eq_v3Pow_w5 m).2]
      rw [cousinDiamond3Step_of_core3_succ_two_w8 ur (by dsimp [ur]; omega) (by dsimp [ur]; omega) hc3]
      dsimp [ur, wr]; rw [Nat.pow_succ 9 m]; omega
    have hsw : cousinDiamond8Step wr = (9 ^ (m + 1) - 1) / 4 := by
      let q := (9 ^ m - 1) / 8
      have hq_pos : q ≥ 1 := by dsimp [q]; omega
      have hp9_eq : 9 ^ m = 8 * q + 1 := by dsimp [q]; omega
      have hwr_eq : wr = 36 * q + 4 := by dsimp [wr]; rw [Nat.pow_succ 9 m, hp9_eq]; omega
      have hnext_eq : (9 ^ (m + 1) - 1) / 4 = 18 * q + 2 := by rw [Nat.pow_succ 9 m, hp9_eq]; omega
      rw [hwr_eq, hnext_eq,
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (36 * q + 4) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5,
          cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) (by omega)]
      omega
    change cousinDiamond8Iter (m + 7) (8 * 3 ^ b0 - 7) = 1
    rw [show m + 7 = 4 + 1 + 1 + m + 1 by omega,
        cousinDiamond8Iter_add (4 + 1 + 1 + m) 1,
        cousinDiamond8Iter_add (4 + 1 + 1) m,
        cousinDiamond8Iter_add (4 + 1) 1,
        cousinDiamond8Iter_add 4 1]
    have hi4 : cousinDiamond8Iter 4 (8 * 3 ^ b0 - 7) = ur := by
      simp only [cousinDiamond8Iter, hs1, hs2, hs3, hu_eq, hs4]
    rw [hi4]
    have hiu : cousinDiamond8Iter 1 ur = wr := hsu
    rw [hiu]
    have hiw : cousinDiamond8Iter 1 wr = (9 ^ (m + 1) - 1) / 4 := hsw
    rw [hiw, cousin_diamond8_even9_spine_drain m]
    decide

theorem cousin_diamond8_a0_2_and_4_drain (b0 : Nat) (hb0 : b0 ≥ 3) :
    cousinDiamond8Iter (b0 + 3) (4 * 3 ^ b0 - 7) = 1 ∧
    cousinDiamond8Iter ((b0 - 1) / 2 + 8) (16 * 3 ^ b0 - 7) = 1 := by
  have hp3_ge27 : 3 ^ b0 ≥ 27 := by
    simpa using nat_pow_mono_exp_pos 3 3 b0 (by decide) hb0
  have hp3_b1_ge9 : 3 ^ (b0 - 1) ≥ 9 := by
    simpa using nat_pow_mono_exp_pos 3 2 (b0 - 1) (by decide) (by omega)
  have hp3_b2_ge3 : 3 ^ (b0 - 2) ≥ 3 := by
    simpa using nat_pow_mono_exp_pos 3 1 (b0 - 2) (by decide) (by omega)
  have h3b0_sp : 3 ^ b0 = 3 * 3 ^ (b0 - 1) := by
    conv => lhs; rw [show b0 = 1 + (b0 - 1) by omega]; rw [Nat.pow_add, Nat.pow_one]
  have h3b1_sp : 3 ^ (b0 - 1) = 3 * 3 ^ (b0 - 2) := by
    conv => lhs; rw [show b0 - 1 = 1 + (b0 - 2) by omega]; rw [Nat.pow_add, Nat.pow_one]
  have h3b0_m9 : 3 ^ b0 % 9 = 0 := by rw [h3b0_sp, h3b1_sp]; omega
  have h3b0_m8 : 3 ^ b0 % 8 = 1 ∨ 3 ^ b0 % 8 = 3 := by
    by_cases hev : b0 % 2 = 0
    · left
      rw [show b0 = 2 * (b0 / 2) by omega, ← pow9_eq_pow3_double]
      exact pow9_mod8_eq_one_w5 _
    · right
      rw [show b0 = 2 * (b0 / 2) + 1 by omega, Nat.pow_succ, ← pow9_eq_pow3_double,
          Nat.mul_mod, pow9_mod8_eq_one_w5]
  have hnc9_4 : ¬ isDiamond8Cone9 (4 * 3 ^ b0 - 7) := by
    apply not_cone9_of_mod32_ne_13
    have hdm := (Nat.div_add_mod (3 ^ b0) 8).symm
    rcases h3b0_m8 with h1 | h3 <;> omega
  have hnc9_16 : ¬ isDiamond8Cone9 (16 * 3 ^ b0 - 7) := by
    apply not_cone9_of_mod32_ne_13
    have ho := pow3_odd_nat_sec8 b0
    omega
  have hnc8_4 : ¬ isDiamond7Cone8 (4 * 3 ^ b0 - 7) := by
    apply not_cone8_of_mod32_ne_21
    have hdm := (Nat.div_add_mod (3 ^ b0) 8).symm
    rcases h3b0_m8 with h1 | h3 <;> omega
  have hnc8_16 : ¬ isDiamond7Cone8 (16 * 3 ^ b0 - 7) := by
    apply not_cone8_of_mod32_ne_21
    have ho := pow3_odd_nat_sec8 b0
    omega
  have hnc7_c : ∀ c : Nat, c ≥ 1 -> ¬ isDiamond6Cone7 (c * 3 ^ b0 - 7) := by
    intro c hc1
    apply not_cone7_of_mod9_ne_8
    have hm : c * 3 ^ b0 ≥ 27 := by simpa using Nat.mul_le_mul hc1 hp3_ge27
    have hm9 : (c * 3 ^ b0) % 9 = 0 := by rw [Nat.mul_mod, h3b0_m9, Nat.mul_zero, Nat.zero_mod]
    omega
  have hnc6_c : ∀ c : Nat, c ≥ 1 -> ¬ isDiamond5Cone6 (c * 3 ^ b0 - 7) := by
    intro c hc1
    apply not_cone6_of_mod9_ne_8
    have hm : c * 3 ^ b0 ≥ 27 := by simpa using Nat.mul_le_mul hc1 hp3_ge27
    have hm9 : (c * 3 ^ b0) % 9 = 0 := by rw [Nat.mul_mod, h3b0_m9, Nat.mul_zero, Nat.zero_mod]
    omega
  refine ⟨?_, ?_⟩
  · have hs1 : cousinDiamond8Step (4 * 3 ^ b0 - 7) = 6 * 3 ^ b0 - 10 := by
      rw [cousinDiamond8Step_eq_d7_of_not_cone9 _ hnc9_4,
          cousinDiamond7Step_eq_d6_of_not_cone8 _ hnc8_4,
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (hnc7_c 4 (by decide)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (hnc6_c 4 (by decide))]
      exact cousin_diamond4_exit_step_general_odd 4 b0 (Or.inl rfl) hb0
    have hs2 : cousinDiamond8Step (6 * 3 ^ b0 - 10) = 2 * 3 ^ b0 - 4 := by
      rw [cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (6 * 3 ^ b0 - 10) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 6 * 3 ^ b0 = 18 * 3 ^ (b0 - 1) := by rw [h3b0_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    have hs3 : cousinDiamond8Step (2 * 3 ^ b0 - 4) = 2 * 3 ^ (b0 - 1) - 2 := by
      rw [cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (2 * 3 ^ b0 - 4) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 2 * 3 ^ b0 = 18 * 3 ^ (b0 - 2) := by rw [h3b0_sp, h3b1_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    have hs4 : cousinDiamond8Step (2 * 3 ^ (b0 - 1) - 2) = 3 ^ (b0 - 1) - 1 := by
      rw [cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (2 * 3 ^ (b0 - 1) - 2) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 2 * 3 ^ (b0 - 1) = 18 * 3 ^ (b0 - 3) := by
        conv => lhs; rhs; rw [show b0 - 1 = 2 + (b0 - 3) by omega]
        rw [Nat.pow_add]; omega
      have hp3_b3 := pow3_pos_nat (b0 - 3)
      have hn8 : ¬ (2 * 3 ^ (b0 - 1) - 2 > 2 ∧ (2 * 3 ^ (b0 - 1) - 2) % 8 = 6) := by
        by_cases hev_b : (b0 - 1) % 2 = 0
        · have h9 : 3 ^ (b0 - 1) % 8 = 1 := by
            rw [show b0 - 1 = 2 * ((b0 - 1) / 2) by omega, ← pow9_eq_pow3_double]
            exact pow9_mod8_eq_one_w5 _
          omega
        · have h9 : 3 ^ (b0 - 1) % 8 = 3 := by
            rw [show b0 - 1 = 2 * ((b0 - 1) / 2) + 1 by omega, Nat.pow_succ,
                ← pow9_eq_pow3_double, Nat.mul_mod, pow9_mod8_eq_one_w5]
          omega
      rw [cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) hn8]
      omega
    rw [show b0 + 3 = 4 + (b0 - 2) + 1 by omega,
        cousinDiamond8Iter_add (4 + (b0 - 2)) 1,
        cousinDiamond8Iter_add 4 (b0 - 2)]
    have hi4 : cousinDiamond8Iter 4 (4 * 3 ^ b0 - 7) = 3 ^ ((b0 - 2) + 1) - 1 := by
      simp only [cousinDiamond8Iter, hs1, hs2, hs3, hs4]
      rw [show b0 - 1 = (b0 - 2) + 1 by omega]
    rw [hi4, cousin_diamond8_pow3_sub1_drain (b0 - 2)]
    decide
  · rcases cousin_diamond8_a0_3_drain b0 hb0 with ⟨ha3_s1, ha3_s2, ha3_s3, ha3⟩
    have hs1 : cousinDiamond8Step (16 * 3 ^ b0 - 7) = 24 * 3 ^ b0 - 10 := by
      rw [cousinDiamond8Step_eq_d7_of_not_cone9 _ hnc9_16,
          cousinDiamond7Step_eq_d6_of_not_cone8 _ hnc8_16,
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (hnc7_c 16 (by decide)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (hnc6_c 16 (by decide))]
      exact cousin_diamond4_exit_step_general_odd 16 b0 (Or.inr (Or.inr rfl)) hb0
    have hs2 : cousinDiamond8Step (24 * 3 ^ b0 - 10) = 8 * 3 ^ b0 - 4 := by
      rw [cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (24 * 3 ^ b0 - 10) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 24 * 3 ^ b0 = 18 * (4 * 3 ^ (b0 - 1)) := by rw [h3b0_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    have hs3 : cousinDiamond8Step (8 * 3 ^ b0 - 4) = 8 * 3 ^ (b0 - 1) - 2 := by
      rw [cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (8 * 3 ^ b0 - 4) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 8 * 3 ^ b0 = 18 * (4 * 3 ^ (b0 - 2)) := by rw [h3b0_sp, h3b1_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    have hs4 : cousinDiamond8Step (8 * 3 ^ (b0 - 1) - 2) = 4 * 3 ^ (b0 - 1) - 2 := by
      rw [cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (8 * 3 ^ (b0 - 1) - 2) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 8 * 3 ^ (b0 - 1) = 18 * (4 * 3 ^ (b0 - 3)) := by
        conv => lhs; rhs; rw [show b0 - 1 = 2 + (b0 - 3) by omega]
        rw [Nat.pow_add]; omega
      have hp3_b3 := pow3_pos_nat (b0 - 3)
      rw [cousinDiamond3Step_even_mod8_eq6_w8 _ (by omega) (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    rw [show (b0 - 1) / 2 + 7 = 3 + ((b0 - 1) / 2 + 4) by omega,
        cousinDiamond8Iter_add 3 ((b0 - 1) / 2 + 4)] at ha3
    have hi3 : cousinDiamond8Iter 3 (8 * 3 ^ b0 - 7) = 4 * 3 ^ (b0 - 1) - 2 := by
      simp only [cousinDiamond8Iter, ha3_s1, ha3_s2, ha3_s3]
    rw [hi3] at ha3
    rw [show (b0 - 1) / 2 + 8 = 4 + ((b0 - 1) / 2 + 4) by omega,
        cousinDiamond8Iter_add 4 ((b0 - 1) / 2 + 4)]
    have hi4 : cousinDiamond8Iter 4 (16 * 3 ^ b0 - 7) = 4 * 3 ^ (b0 - 1) - 2 := by
      simp only [cousinDiamond8Iter, hs1, hs2, hs3, hs4]
    rw [hi4]
    exact ha3

theorem cousin_diamond8_cone4_return_aux (x : Nat) (hc4 : isDiamond3Cone4 x) :
    ∃ k : Nat, k ≤ cousinDiamond2Phi x ∧ cousinDiamond8Iter k x = 1 := by
  rcases cousin_diamond3_cone4_reaches_one_exact x hc4 with ⟨r, hr_ge3, hE, _, hphi_ge⟩
  refine ⟨3 * r + 4, hphi_ge, ?_⟩
  have hnc9_x : ¬ isDiamond8Cone9 x := not_cone9_of_mod8_ne_5 x (by have h8 := hc4.2.1; omega)
  have hnc8_x : ¬ isDiamond7Cone8 x := not_cone8_of_mod8_ne_5 x (by have h8 := hc4.2.1; omega)
  have hnc7_x : ¬ isDiamond6Cone7 x := not_cone7_of_mod8_ne_5 x (by have h8 := hc4.2.1; omega)
  have hnc6_x : ¬ isDiamond5Cone6 x := by rintro ⟨_, h256, _, _⟩; have h8 := hc4.2.1; omega
  have hx_odd : x % 2 = 1 := by have h8 := hc4.2.1; omega
  have hs1 : cousinDiamond8Step x = 2 ^ (2 * r + 1) - 1 := by
    rw [cousinDiamond8Step_eq_d7_of_not_cone9 x hnc9_x,
        cousinDiamond7Step_eq_d6_of_not_cone8 x hnc8_x,
        cousinDiamond6Step_eq_d5_of_not_cone7 x hnc7_x,
        cousinDiamond5Step_eq_d4_of_not_cone6 x hnc6_x]
    unfold cousinDiamond4Step
    have hp4 : 2 ^ (2 * r + 3) = 4 * 2 ^ (2 * r + 1) := by
      rw [show 2 * r + 3 = 2 + (2 * r + 1) by omega, Nat.pow_add]
    have hp_pos := pow2_pos_nat (2 * r + 1)
    by_cases hc5 : isDiamond4Cone5 x
    · simp only [hc5, ite_true]; omega
    · simp only [hc5, ite_false]
      rw [cousinDiamond3Step_of_cone4_w8 x hx_odd hc4]; omega
  let zr := 2 * 9 ^ r - 1
  let yr := (3 * 9 ^ r - 1) / 2
  have hglide : cousinDiamond8Iter (2 * r) (2 ^ (2 * r + 1) - 1) = zr := by
    have hf := cousin_diamond8_mersenne_scaled (2 * r) (2 * r + 1) 1 (by omega) (by decide)
    simp only [Nat.mul_one, show 2 * r + 1 - 2 * r = 1 by omega, Nat.pow_one] at hf
    rw [hf, ← pow9_eq_pow3_double r, Nat.mul_comm]
  have hp9_ge729 : 9 ^ r ≥ 729 := by
    simpa using nat_pow_mono_exp_pos 9 3 r (by decide) hr_ge3
  have hp9_m8 : 9 ^ r % 8 = 1 := pow9_mod8_eq_one_w5 r
  have hsz : cousinDiamond8Step zr = yr := by
    rw [cousinDiamond8Step_eq_d7_of_not_cone9 zr (not_cone9_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
        cousinDiamond7Step_eq_d6_of_not_cone8 zr (not_cone8_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
        cousinDiamond6Step_eq_d5_of_not_cone7 zr (not_cone7_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
        cousinDiamond5Step_eq_d4_of_not_cone6 zr (not_cone6_of_mod16_ne_13 zr (by dsimp [zr]; omega))]
    have hnc5 : ¬ isDiamond4Cone5 zr := by rintro ⟨_, h32, _, _⟩; dsimp [zr] at h32; omega
    rw [cousinDiamond4Step_eq_d3_of_not_cone5 zr hnc5]
    have hc3 : core3 (zr + 1) = 2 := by
      rw [show zr + 1 = 2 * 9 ^ r by dsimp [zr]; omega,
          core3_mul2 (9 ^ r) (by omega), (pow9_eq_v3Pow_w5 r).2]
    rw [cousinDiamond3Step_of_core3_succ_two_w8 zr (by dsimp [zr]; omega) (by dsimp [zr]; omega) hc3]
    dsimp [zr, yr]; omega
  have hsy : cousinDiamond8Step yr = (9 ^ (r + 1) - 1) / 4 := by
    have hyr_m3 : yr % 3 = 1 := by
      have hm3 : 9 ^ r % 3 = 0 := by rw [show r = (r - 1) + 1 by omega, Nat.pow_succ]; omega
      dsimp [yr]; omega
    rw [cousinDiamond8Step_eq_d7_of_not_cone9 yr (not_cone9_of_mod3_ne_2 yr (by omega)),
        cousinDiamond7Step_eq_d6_of_not_cone8 yr (not_cone8_of_mod3_ne_2 yr (by omega)),
        cousinDiamond6Step_eq_d5_of_not_cone7 yr (not_cone7_of_mod9_ne_8 yr (by omega)),
        cousinDiamond5Step_eq_d4_of_not_cone6 yr (not_cone6_of_mod9_ne_8 yr (by omega))]
    have hnc5 : ¬ isDiamond4Cone5 yr := by rintro ⟨_, _, hm3, _⟩; omega
    rw [cousinDiamond4Step_eq_d3_of_not_cone5 yr hnc5]
    have hc3_2 : core3 (2 * yr + 1) = 1 := by
      rw [show 2 * yr + 1 = 3 * 9 ^ r by dsimp [yr]; omega,
          core3_mul3 (9 ^ r) (by omega), (pow9_eq_v3Pow_w5 r).2]
    have hc3_1 : core3 (yr + 1) ≠ 2 := by
      rw [core3_not_div3 (yr + 1) (by omega)]; dsimp [yr]; omega
    have hnc4 : ¬ isDiamond3Cone4 yr := by
      rintro ⟨_, _, hc2⟩
      rcases eq_pow2_of_core2_eq_one (3 * yr + 5) (by dsimp [yr]; omega) hc2 with ⟨M0, hM0⟩
      have h9_eq : 9 ^ (r + 1) + 7 = 2 ^ (M0 + 1) := by
        have h2mul : 2 * (3 * yr + 5) = 9 ^ (r + 1) + 7 := by
          rw [Nat.pow_succ 9 r, Nat.mul_comm (9 ^ r) 9]; dsimp [yr]; omega
        rw [← h2mul, hM0, Nat.pow_succ 2 M0, Nat.mul_comm]
      exact pow9_succ_add_seven_ne_pow2 r (M0 + 1) (by omega) h9_eq
    rw [cousinDiamond3Step_odd_half_w8 yr (by dsimp [yr]; omega) hnc4 hc3_2 hc3_1]
    dsimp [yr]; rw [Nat.pow_succ 9 r]; omega
  rw [show 3 * r + 4 = 1 + 2 * r + 1 + 1 + r + 1 by omega,
      cousinDiamond8Iter_add (1 + 2 * r + 1 + 1 + r) 1,
      cousinDiamond8Iter_add (1 + 2 * r + 1 + 1) r,
      cousinDiamond8Iter_add (1 + 2 * r + 1) 1,
      cousinDiamond8Iter_add (1 + 2 * r) 1,
      cousinDiamond8Iter_add 1 (2 * r)]
  have hi1 : cousinDiamond8Iter 1 x = 2 ^ (2 * r + 1) - 1 := hs1
  rw [hi1, hglide]
  have hiz : cousinDiamond8Iter 1 zr = yr := hsz
  rw [hiz]
  have hiy : cousinDiamond8Iter 1 yr = (9 ^ (r + 1) - 1) / 4 := hsy
  rw [hiy, cousin_diamond8_even9_spine_drain r]
  decide

theorem cousin_diamond8_cone5_return_aux (x : Nat) (hc5 : isDiamond4Cone5 x) :
    ∃ (a b k : Nat),
      a ≥ 5 ∧ b ≥ 1 ∧ x + 7 = 2 ^ a * 3 ^ b ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond8Iter k x = 1 := by
  rcases hc5 with ⟨hx89, hx32, hx3, hg1⟩
  rcases decomp_2_3_exact (x + 7) (by omega) with ⟨_, _, _, _, _, hmul⟩
  rw [hg1, Nat.mul_one] at hmul
  rcases eq_pow2_of_v2Pow_aux (x + 7) (x + 7) (by omega) (Nat.le_refl _) with ⟨a, ha⟩
  rcases eq_pow3_of_v3Pow_aux (x + 7) (x + 7) (by omega) (Nat.le_refl _) with ⟨b, hb⟩
  rw [ha, hb] at hmul
  have ha5 : a ≥ 5 := by
    by_cases hlt : a < 5
    · have hp3_o := pow3_odd_nat_sec8 b
      rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4) with rfl | rfl | rfl | rfl | rfl <;>
        omega
    · omega
  have hb1 : b ≥ 1 := by
    cases b with
    | zero => rw [Nat.pow_zero, Nat.mul_one] at hmul; have hm3 := pow2_mod3_nonzero_w5 a; omega
    | succ _ => omega
  have hx_eq : x = 2 ^ a * 3 ^ b - 7 := by omega
  let q_c := (a - 2) / 3
  let a0 := a - 3 * q_c
  let b0 := b + 2 * q_c
  have hb0_ge3 : b0 ≥ 3 := by dsimp [b0, q_c]; omega
  have ha0_234 : a0 = 2 ∨ a0 = 3 ∨ a0 = 4 := by dsimp [a0, q_c]; omega
  have hclimb := cousin_diamond8_cone5_two_step_climb q_c a b (by dsimp [q_c]; omega) hb1
  rw [← hx_eq] at hclimb
  change cousinDiamond8Iter (2 * q_c) x = 2 ^ a0 * 3 ^ b0 - 7 at hclimb
  have hbound_x : ∀ ex : Nat, ex ≤ b0 + 8 -> 2 * q_c + ex ≤ x := by
    intro ex hex
    have hm1 := pow2_ge_six_mul_ge5 a ha5
    have hm2 := pow3_ge_add_two_ge1 b hb1
    have hprod := Nat.mul_le_mul hm1 hm2
    rw [hmul] at hprod
    have hab : 6 * b ≤ 6 * a * b := by
      rw [Nat.mul_comm (6 * a) b, ← Nat.mul_assoc, Nat.mul_comm b 6]
      simpa using Nat.mul_le_mul_left (6 * b) (by omega : 1 ≤ a)
    have hexp : (6 * a) * (b + 2) = 6 * a * b + 12 * a := by rw [Nat.mul_add]; omega
    rw [hexp] at hprod
    dsimp [q_c, b0] at hex ⊢
    omega
  have hd_3 := (cousin_diamond8_a0_3_drain b0 hb0_ge3).2.2.2
  rcases cousin_diamond8_a0_2_and_4_drain b0 hb0_ge3 with ⟨hd_2, hd_4⟩
  rcases ha0_234 with ha2 | ha3 | ha4
  · have hkx := hbound_x (b0 + 3) (by omega)
    refine ⟨a, b, 2 * q_c + (b0 + 3), ha5, hb1, hmul.symm, hkx,
      Nat.le_trans (by omega : 2 * q_c + (b0 + 3) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond8Iter_add (2 * q_c) (b0 + 3) x, hclimb, ha2]; exact hd_2
  · have hkx := hbound_x ((b0 - 1) / 2 + 7) (by omega)
    refine ⟨a, b, 2 * q_c + ((b0 - 1) / 2 + 7), ha5, hb1, hmul.symm, hkx,
      Nat.le_trans (by omega : 2 * q_c + ((b0 - 1) / 2 + 7) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond8Iter_add (2 * q_c) ((b0 - 1) / 2 + 7) x, hclimb, ha3]; exact hd_3
  · have hkx := hbound_x ((b0 - 1) / 2 + 8) (by omega)
    refine ⟨a, b, 2 * q_c + ((b0 - 1) / 2 + 8), ha5, hb1, hmul.symm, hkx,
      Nat.le_trans (by omega : 2 * q_c + ((b0 - 1) / 2 + 8) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond8Iter_add (2 * q_c) ((b0 - 1) / 2 + 8) x, hclimb, ha4]; exact hd_4

theorem cousin_diamond8_cone6_return_aux (x : Nat) (hc6 : isDiamond5Cone6 x) :
    ∃ (e f k : Nat),
      e ≥ 8 ∧ f ≥ 2 ∧ x + 19 = 2 ^ e * 3 ^ f ∧
      cousinDiamond8Step x = 2 ^ (e - 3) * 3 ^ (f + 1) - 7 ∧
      isDiamond4Cone5 (cousinDiamond8Step x) ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond8Iter k x = 1 := by
  have hnc9_x : ¬ isDiamond8Cone9 x :=
    not_cone9_of_mod256_ne_141 x (by rw [hc6.2.1]; decide)
  have hx_ge : x ≥ 2285 := hc6.1
  rcases (cousin_diamond7_cones45678_exact_return.2.2.1 x hc6) with
    ⟨e, f, _, he8, hf2, hmul, hd7_x, _, _, _, _⟩
  let y := 2 ^ (e - 3) * 3 ^ (f + 1) - 7
  have hstep_x : cousinDiamond8Step x = y := by
    rw [cousinDiamond8Step_eq_d7_of_not_cone9 x hnc9_x]; exact hd7_x
  have hnc8_x : ¬ isDiamond7Cone8 x :=
    not_cone8_of_mod256_ne_213 x (by rw [hc6.2.1]; decide)
  have hnc7_x : ¬ isDiamond6Cone7 x :=
    not_cone7_of_mod256_ne_213 x (by rw [hc6.2.1]; decide)
  have hy_step : y = (3 * x + 1) / 8 :=
    hd7_x.symm.trans (by
      rw [cousinDiamond7Step_eq_d6_of_not_cone8 x hnc8_x,
          cousinDiamond6Step_eq_d5_of_not_cone7 x hnc7_x]
      unfold cousinDiamond5Step; simp [hc6])
  clear hc6 hnc9_x hnc8_x hnc7_x hd7_x
  have hc5_y : isDiamond4Cone5 y :=
    isDiamond4Cone5_of_pow2_pow3 (e - 3) (f + 1) (by omega) (by omega)
  rcases cousin_diamond8_cone5_return_aux y hc5_y with ⟨_, _, ky, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hdiv : y * 8 ≤ 3 * x + 1 := by rw [hy_step]; exact Nat.div_mul_le_self (3 * x + 1) 8
    clear hy_step hmul hstep_x hc5_y hky_1
    omega
  have h1ky_x : 1 + ky ≤ x := by clear hy_step hmul hstep_x hc5_y hky_1; omega
  have h1ky_phi : 1 + ky ≤ cousinDiamond2Phi x :=
    Nat.le_trans (by clear hy_step hmul hstep_x hc5_y hky_1; omega : 1 + ky ≤ x + 1) (cousinDiamond2Phi_ge_succ x)
  refine ⟨e, f, 1 + ky, he8, hf2, hmul, hstep_x, ?_, h1ky_x, h1ky_phi, ?_⟩
  · rw [hstep_x]; exact hc5_y
  · rw [cousinDiamond8Iter_add 1 ky x]
    have hi1 : cousinDiamond8Iter 1 x = y := hstep_x
    rw [hi1]; exact hky_1

theorem cousin_diamond8_cone7_return_aux (x : Nat) (hc7 : isDiamond6Cone7 x) :
    ∃ (g h k : Nat),
      g ≥ 15 ∧ h ≥ 2 ∧ x + 811 = 2 ^ g * 3 ^ h ∧
      cousinDiamond8Step x = 2 ^ (g - 7) * 3 ^ (h + 1) - 19 ∧
      isDiamond5Cone6 (cousinDiamond8Step x) ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond8Iter k x = 1 := by
  have hnc9_x : ¬ isDiamond8Cone9 x := by
    apply not_cone9_of_mod32_ne_13
    have h32 : x % 32 = 31957 % 32 := by
      have h := congrArg (· % 32) hc7.2.1
      rwa [Nat.mod_mod_of_dvd x (by decide : 32 ∣ 32768)] at h
    rw [h32]; decide
  have hnc8_x : ¬ isDiamond7Cone8 x :=
    not_cone8_of_mod32768_ne_30933 x (by rw [hc7.2.1]; decide)
  have hx_ge : x ≥ 294101 := hc7.1
  rcases (cousin_diamond7_cones45678_exact_return.2.2.2.1 x hc7) with
    ⟨g, h, _, hg15, hh2, hmul, hd7_x, _, _, _, _⟩
  let y := 2 ^ (g - 7) * 3 ^ (h + 1) - 19
  have hstep_x : cousinDiamond8Step x = y := by
    rw [cousinDiamond8Step_eq_d7_of_not_cone9 x hnc9_x]; exact hd7_x
  have hy_step : y = (3 * x + 1) / 128 :=
    hd7_x.symm.trans (by
      rw [cousinDiamond7Step_eq_d6_of_not_cone8 x hnc8_x]
      unfold cousinDiamond6Step; simp [hc7])
  clear hc7 hnc9_x hnc8_x hd7_x
  have hc6_y : isDiamond5Cone6 y :=
    isDiamond5Cone6_of_pow2_pow3 (g - 7) (h + 1) (by omega) (by omega)
  rcases cousin_diamond8_cone6_return_aux y hc6_y with ⟨_, _, ky, _, _, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hdiv : y * 128 ≤ 3 * x + 1 := by rw [hy_step]; exact Nat.div_mul_le_self (3 * x + 1) 128
    clear hy_step hmul hstep_x hc6_y hky_1
    omega
  have h1ky_x : 1 + ky ≤ x := by clear hy_step hmul hstep_x hc6_y hky_1; omega
  have h1ky_phi : 1 + ky ≤ cousinDiamond2Phi x :=
    Nat.le_trans (by clear hy_step hmul hstep_x hc6_y hky_1; omega : 1 + ky ≤ x + 1) (cousinDiamond2Phi_ge_succ x)
  refine ⟨g, h, 1 + ky, hg15, hh2, hmul, hstep_x, ?_, h1ky_x, h1ky_phi, ?_⟩
  · rw [hstep_x]; exact hc6_y
  · rw [cousinDiamond8Iter_add 1 ky x]
    have hi1 : cousinDiamond8Iter 1 x = y := hstep_x
    rw [hi1]; exact hky_1

theorem cousin_diamond8_cone8_return_aux (x : Nat) (hc8 : isDiamond7Cone8 x) :
    ∃ (u v k : Nat),
      u ≥ 22 ∧ v ≥ 1 ∧ x + 34603 = 2 ^ u * 3 ^ v ∧
      cousinDiamond8Step x = 2 ^ (u - 7) * 3 ^ (v + 1) - 811 ∧
      isDiamond6Cone7 (cousinDiamond8Step x) ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond8Iter k x = 1 := by
  have hnc9_x : ¬ isDiamond8Cone9 x :=
    not_cone9_of_mod32_ne_13 x (by have h := mod32_of_cone8 x hc8; omega)
  have hx_ge : x ≥ 12548309 := hc8.1
  rcases (cousin_diamond7_cones45678_exact_return.2.2.2.2 x hc8) with
    ⟨u, v, _, hu22, hv1, hmul, hd7_x, _, _, _, _⟩
  let y := 2 ^ (u - 7) * 3 ^ (v + 1) - 811
  have hstep_x : cousinDiamond8Step x = y := by
    rw [cousinDiamond8Step_eq_d7_of_not_cone9 x hnc9_x]; exact hd7_x
  have hy_step : y = (3 * x + 1) / 128 :=
    hd7_x.symm.trans (by unfold cousinDiamond7Step; simp [hc8])
  clear hc8 hnc9_x hd7_x
  have hc7_y : isDiamond6Cone7 y :=
    isDiamond6Cone7_of_pow2_pow3 (u - 7) (v + 1) (by omega) (by omega)
  rcases cousin_diamond8_cone7_return_aux y hc7_y with ⟨_, _, ky, _, _, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hdiv : y * 128 ≤ 3 * x + 1 := by rw [hy_step]; exact Nat.div_mul_le_self (3 * x + 1) 128
    clear hy_step hmul hstep_x hc7_y hky_1
    omega
  have h1ky_x : 1 + ky ≤ x := by clear hy_step hmul hstep_x hc7_y hky_1; omega
  have h1ky_phi : 1 + ky ≤ cousinDiamond2Phi x :=
    Nat.le_trans (by clear hy_step hmul hstep_x hc7_y hky_1; omega : 1 + ky ≤ x + 1) (cousinDiamond2Phi_ge_succ x)
  refine ⟨u, v, 1 + ky, hu22, hv1, hmul, hstep_x, ?_, h1ky_x, h1ky_phi, ?_⟩
  · rw [hstep_x]; exact hc7_y
  · rw [cousinDiamond8Iter_add 1 ky x]
    have hi1 : cousinDiamond8Iter 1 x = y := hstep_x
    rw [hi1]; exact hky_1

/--
  Theorem W11.3d (`cousin_diamond8_cones4to9_exact_return`, `zero custom axioms`):
  Exact 6-Tier `ω^6` Multi-Block Return Across Cones 4, 5, 6, 7, 8, AND 9 of `T_diamond8`:
  1–5. Every `x` in Cone 4, 5, 6, 7, or 8 reaches `1` in `k ≤ cousinDiamond2Phi x` steps!
  6. Every `x` in Cone 9 (`isDiamond8Cone9 x`) has `x + 92275 = 2 ^ w * 3 ^ z` (`w ≥ 25, z ≥ 1`),
     steps in 1 genuine `v_2(3x + 1) = 3` jump `(3 * x + 1) / 8` directly into the Cone-8 state
     `y = 2 ^ (w - 3) * 3 ^ (z + 1) - 34603`, and reaches `1` in `1 + k_y ≤ x` (`≤ cousinDiamond2Phi x`) steps!
-/
theorem cousin_diamond8_cones4to9_exact_return :
    (∀ x : Nat, isDiamond3Cone4 x ->
      ∃ k : Nat, k ≤ cousinDiamond2Phi x ∧ cousinDiamond8Iter k x = 1) ∧
    (∀ x : Nat, isDiamond4Cone5 x ->
      ∃ (a b k : Nat),
        a ≥ 5 ∧ b ≥ 1 ∧ x + 7 = 2 ^ a * 3 ^ b ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond8Iter k x = 1) ∧
    (∀ x : Nat, isDiamond5Cone6 x ->
      ∃ (e f k : Nat),
        e ≥ 8 ∧ f ≥ 2 ∧ x + 19 = 2 ^ e * 3 ^ f ∧
        cousinDiamond8Step x = 2 ^ (e - 3) * 3 ^ (f + 1) - 7 ∧
        isDiamond4Cone5 (cousinDiamond8Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond8Iter k x = 1) ∧
    (∀ x : Nat, isDiamond6Cone7 x ->
      ∃ (g h k : Nat),
        g ≥ 15 ∧ h ≥ 2 ∧ x + 811 = 2 ^ g * 3 ^ h ∧
        cousinDiamond8Step x = 2 ^ (g - 7) * 3 ^ (h + 1) - 19 ∧
        isDiamond5Cone6 (cousinDiamond8Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond8Iter k x = 1) ∧
    (∀ x : Nat, isDiamond7Cone8 x ->
      ∃ (u v k : Nat),
        u ≥ 22 ∧ v ≥ 1 ∧ x + 34603 = 2 ^ u * 3 ^ v ∧
        cousinDiamond8Step x = 2 ^ (u - 7) * 3 ^ (v + 1) - 811 ∧
        isDiamond6Cone7 (cousinDiamond8Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond8Iter k x = 1) ∧
    (∀ x : Nat, isDiamond8Cone9 x ->
      ∃ (w z k : Nat),
        w ≥ 25 ∧ z ≥ 1 ∧ x + 92275 = 2 ^ w * 3 ^ z ∧
        cousinDiamond8Step x = 2 ^ (w - 3) * 3 ^ (z + 1) - 34603 ∧
        isDiamond7Cone8 (cousinDiamond8Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond8Iter k x = 1) := by
  refine ⟨cousin_diamond8_cone4_return_aux,
          cousin_diamond8_cone5_return_aux,
          cousin_diamond8_cone6_return_aux,
          cousin_diamond8_cone7_return_aux,
          cousin_diamond8_cone8_return_aux, ?_⟩
  intro x hc9
  have hraw_step : cousinDiamond8Step x = (3 * x + 1) / 8 := by
    unfold cousinDiamond8Step; simp only [hc9, ite_true]
  rcases hc9 with ⟨hx_ge, hx33m, hx3, hg1⟩
  have hdvd33m : 33554432 ∣ (x + 92275) :=
    Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, hx33m])
  clear hx33m
  rcases (⟨92275 + x, rfl⟩ : ∃ N : Nat, N = 92275 + x) with ⟨N, hN_def⟩
  rw [← hN_def] at hg1
  have hN_pos : N > 0 := by clear hraw_step hdvd33m hx3 hg1; omega
  rcases decomp_2_3_exact N hN_pos with ⟨_, _, _, _, _, hmul⟩
  rw [hg1, Nat.mul_one] at hmul
  rcases eq_pow2_of_v2Pow_aux N N hN_pos (Nat.le_refl _) with ⟨w, hw⟩
  rcases eq_pow3_of_v3Pow_aux N N hN_pos (Nat.le_refl _) with ⟨z, hz⟩
  rw [hw, hz] at hmul
  have hmul_comm : x + 92275 = 2 ^ w * 3 ^ z := by
    rw [Nat.add_comm x 92275, ← hN_def, ← hmul]
  clear hg1 hw hz hN_def hmul hN_pos
  have hw25 : w ≥ 25 := by
    by_cases hlt : w < 25
    · exfalso
      have h33m_sp : 33554432 = 2 ^ (w + 1) * 2 ^ (24 - w) := by
        have hsum25 : w + 1 + (24 - w) = 25 := by clear hraw_step hx_ge hx3 hdvd33m hmul_comm; omega
        rw [← Nat.pow_add 2 (w + 1) (24 - w), hsum25]
      rcases hdvd33m with ⟨q, hq⟩
      rw [hmul_comm, h33m_sp, Nat.mul_assoc (2 ^ (w + 1)),
          Nat.pow_succ 2 w, Nat.mul_assoc (2 ^ w) 2] at hq
      have h3z_ev : 3 ^ z = 2 * (2 ^ (24 - w) * q) :=
        nat_mul_left_cancel_pos (2 ^ w) _ _ (pow2_pos_nat w) hq
      have ho := pow3_odd_nat_sec8 z
      rw [h3z_ev, Nat.mul_mod_right] at ho
      cases ho
    · clear hraw_step hx_ge hx3 hdvd33m hmul_comm; omega
  clear hdvd33m
  have hz1 : z ≥ 1 := by
    cases z with
    | zero =>
      rw [Nat.pow_zero, Nat.mul_one] at hmul_comm
      exact False.elim (pow2_mod3_nonzero_w5 w (by rw [← hmul_comm, Nat.add_mod, hx3]))
    | succ _ => clear hraw_step hx_ge hx3 hmul_comm hw25; omega
  clear hx3
  let y := 2 ^ (w - 3) * 3 ^ (z + 1) - 34603
  have hstep_x : cousinDiamond8Step x = y := by
    rw [hraw_step]
    dsimp [y]
    have hp8 : 2 ^ w = 8 * 2 ^ (w - 3) := by
      have hw_sp : w = 3 + (w - 3) := by clear hraw_step hx_ge hmul_comm hz1; omega
      conv => lhs; rw [hw_sp]; rw [Nat.pow_add]
    have hprod_pos : 2 ^ (w - 3) * 3 ^ z ≥ 4194304 * 3 := by
      have h1 : 4194304 ≤ 2 ^ (w - 3) := by
        have hc : (2 : Nat) ^ 22 = 4194304 := by decide
        have h22 : 22 ≤ w - 3 := by clear hraw_step hx_ge hmul_comm hz1 hp8; omega
        rw [← hc]; exact pow2_mono_nat h22
      have h2 : 3 ≤ 3 ^ z := by simpa using nat_pow_mono_exp_pos 3 1 z (by decide) hz1
      simpa using Nat.mul_le_mul h1 h2
    have h3_eq : 2 ^ (w - 3) * 3 ^ (z + 1) = 3 * (2 ^ (w - 3) * 3 ^ z) := by
      rw [Nat.pow_succ 3 z, ← Nat.mul_assoc, Nat.mul_comm _ 3]
    rw [h3_eq]
    have hx8 : x + 92275 = 8 * (2 ^ (w - 3) * 3 ^ z) := by
      rw [hmul_comm, hp8, Nat.mul_assoc]
    have h3x1 : 3 * x + 1 = (3 * (2 ^ (w - 3) * 3 ^ z) - 34603) * 8 := by
      clear hraw_step hw25 hz1 hp8 h3_eq hmul_comm
      generalize 2 ^ (w - 3) * 3 ^ z = A at hprod_pos hx8 ⊢
      omega
    rw [h3x1]
    exact Nat.mul_div_left _ (by decide : 0 < 8)
  have hc8_y : isDiamond7Cone8 y :=
    isDiamond7Cone8_of_pow2_pow3 (w - 3) (z + 1)
      (by clear hraw_step hx_ge hmul_comm hstep_x; omega)
      (by clear hraw_step hx_ge hmul_comm hstep_x; omega)
  rcases cousin_diamond8_cone8_return_aux y hc8_y with ⟨_, _, ky, _, _, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hstep_eq : y = (3 * x + 1) / 8 := hstep_x.symm.trans hraw_step
    have hdiv : y * 8 ≤ 3 * x + 1 := by rw [hstep_eq]; exact Nat.div_mul_le_self (3 * x + 1) 8
    clear hraw_step hmul_comm hstep_x hc8_y hky_1 hstep_eq
    omega
  have h1ky_x : 1 + ky ≤ x := by clear hraw_step hmul_comm hstep_x hc8_y hky_1; omega
  have h1ky_phi : 1 + ky ≤ cousinDiamond2Phi x :=
    Nat.le_trans (by clear hraw_step hmul_comm hstep_x hc8_y hky_1; omega : 1 + ky ≤ x + 1)
      (cousinDiamond2Phi_ge_succ x)
  refine ⟨w, z, 1 + ky, hw25, hz1, hmul_comm, hstep_x, ?_, h1ky_x, h1ky_phi, ?_⟩
  · rw [hstep_x]; exact hc8_y
  · rw [cousinDiamond8Iter_add 1 ky x]
    have hi1 : cousinDiamond8Iter 1 x = y := hstep_x
    rw [hi1]; exact hky_1

theorem cousin_diamond8_reaches_one_within_phi :
    ∀ (B x : Nat), x > 0 -> cousinDiamond2Phi x ≤ B ->
      ∃ k : Nat, k ≤ B ∧ cousinDiamond8Iter k x = 1
  | 0, x, _, hB => by have hge := cousinDiamond2Phi_ge_succ x; omega
  | B + 1, x, hx, hB => by
    by_cases hx1 : x = 1
    · subst hx1; exact ⟨0, by omega, rfl⟩
    · by_cases hx2 : x = 2
      · subst hx2
        have hphi2 : cousinDiamond2Phi 2 = 28 := by decide
        rw [hphi2] at hB
        exact ⟨1, by omega, by decide⟩
      · by_cases hc4 : isDiamond3Cone4 x
        · rcases cousin_diamond8_cones4to9_exact_return.1 x hc4 with ⟨k, hle_phi, hk1⟩
          exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
        · by_cases hc5 : isDiamond4Cone5 x
          · rcases cousin_diamond8_cones4to9_exact_return.2.1 x hc5 with
              ⟨_, _, k, _, _, _, _, hle_phi, hk1⟩
            exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
          · by_cases hc6 : isDiamond5Cone6 x
            · rcases cousin_diamond8_cones4to9_exact_return.2.2.1 x hc6 with
                ⟨_, _, k, _, _, _, _, _, _, hle_phi, hk1⟩
              exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
            · by_cases hc7 : isDiamond6Cone7 x
              · rcases cousin_diamond8_cones4to9_exact_return.2.2.2.1 x hc7 with
                  ⟨_, _, k, _, _, _, _, _, _, hle_phi, hk1⟩
                exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
              · by_cases hc8 : isDiamond7Cone8 x
                · rcases cousin_diamond8_cones4to9_exact_return.2.2.2.2.1 x hc8 with
                    ⟨_, _, k, _, _, _, _, _, _, hle_phi, hk1⟩
                  exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
                · by_cases hc9 : isDiamond8Cone9 x
                  · rcases cousin_diamond8_cones4to9_exact_return.2.2.2.2.2 x hc9 with
                      ⟨_, _, k, _, _, _, _, _, _, hle_phi, hk1⟩
                    exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
                  · have hdesc := cousin_diamond8_outside_cones4to9_strict_descent x
                      (by omega) hc4 hc5 hc6 hc7 hc8 hc9
                    have hpos := cousinDiamond8Step_pos x hx
                    rcases cousin_diamond8_reaches_one_within_phi B (cousinDiamond8Step x) hpos (by omega) with
                      ⟨k, hk_le, hk_eq⟩
                    exact ⟨k + 1, by omega, hk_eq⟩

/--
  Theorem W11.3e (`cousin_diamond8_global_convergence`, `zero custom axioms`):
  Unconditional Global Convergence & Degree-5 Polynomial Stopping Bound for `T_diamond8`:
  For EVERY `x > 0`, `cousinDiamond8Iter` reaches `1` within `k ≤ (x + 1) ^ 3 + (x + 1) ^ 5` steps!
-/
theorem cousin_diamond8_global_convergence (x : Nat) (hx : x > 0) :
    ∃ k : Nat, k ≤ (x + 1) ^ 3 + (x + 1) ^ 5 ∧ cousinDiamond8Iter k x = 1 := by
  rcases cousin_diamond8_reaches_one_within_phi (cousinDiamond2Phi x) x hx (Nat.le_refl _) with
    ⟨k, hk_phi, hk1⟩
  exact ⟨k, Nat.le_trans hk_phi (cousinDiamond2Phi_upper_poly_bound x), hk1⟩

theorem exists_non_desc_along_diamond8_iter_clean :
    ∀ (terms : List LaurentTerm) (A0 B0 C0 N z : Nat),
      N ≥ 1 ->
      (∀ i : Nat, i < N ->
        cousinDiamond8Iter i z ≥ 3 ∧
        (cousinDiamond8Iter i z) % 2 = 1 ∧
        cousinDiamond8Step (cousinDiamond8Iter i z) ≥ 3) ->
      ¬ laurentDescProp terms A0 B0 C0 z (cousinDiamond8Iter N z) ->
      ∃ x : Nat,
        x ≥ 3 ∧ x % 2 = 1 ∧ cousinDiamond8Step x ≥ 3 ∧
        ¬ laurentDescProp terms A0 B0 C0 x (cousinDiamond8Step x)
  | _, _, _, _, 0, _, hN, _, _ => by omega
  | terms, A0, B0, C0, 1, z, _, hall, hnd => by
    rcases hall 0 (by decide) with ⟨hz3, hzo, hsz3⟩
    exact ⟨z, hz3, hzo, hsz3, hnd⟩
  | terms, A0, B0, C0, m + 2, z, _, hall, hnd => by
    if h0 : laurentDescProp terms A0 B0 C0 z (cousinDiamond8Step z) then
      have hnd_next : ¬ laurentDescProp terms A0 B0 C0 (cousinDiamond8Step z)
          (cousinDiamond8Iter (m + 1) (cousinDiamond8Step z)) :=
        fun hrest => hnd (laurentDescProp_trans terms A0 B0 C0 z (cousinDiamond8Step z) _ h0 hrest)
      exact exists_non_desc_along_diamond8_iter_clean terms A0 B0 C0 (m + 1) (cousinDiamond8Step z)
        (by omega) (fun i hi => hall (i + 1) (by omega)) hnd_next
    else
      rcases hall 0 (by omega) with ⟨hz3, hzo, hsz3⟩
      exact ⟨z, hz3, hzo, hsz3, h0⟩

/--
  Theorem W11.3f (`cousin_diamond8_r_block_spiral_climb_and_laurent_impossibility`, `zero custom axioms`):
  1. Cone-9 -> Cone-8 -> Cone-7 -> Cone-6 -> Cone-5 6-Tier Cascade & Unbounded `r`-Block Spiral Climb (`∀ r ≥ 1`):
     `100571021 -> 37714133 -> 883925 -> 20717 -> 7769` AND
     `cousinDiamond8Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5` for ALL `j ≤ r`!
  2. Universal `∀ L ≥ 1` Multi-Term Laurent Valuation Impossibility on `cousinDiamond8Step`!
-/
theorem cousin_diamond8_r_block_spiral_climb_and_laurent_impossibility :
    cousinDiamond8Step 100571021 = 37714133 ∧
    cousinDiamond8Step 37714133 = 883925 ∧
    cousinDiamond8Step 883925 = 20717 ∧
    cousinDiamond8Step 20717 = 7769 ∧
    (∀ (r j : Nat), r ≥ 1 -> j ≤ r ->
      cousinDiamond8Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5) ∧
    (∀ (terms : List LaurentTerm) (A0 B0 C0 : Nat),
      (∃ t ∈ terms, t.coeff > 0) ->
      ∃ x : Nat,
        x ≥ 3 ∧ x % 2 = 1 ∧ cousinDiamond8Step x ≥ 3 ∧
        ¬ (evalLaurentSumNum terms (cousinDiamond8Step x) * laurentValDen A0 B0 C0 x <
            evalLaurentSumNum terms x * laurentValDen A0 B0 C0 (cousinDiamond8Step x))) := by
  have hspiral : ∀ (r j : Nat), r ≥ 1 -> j ≤ r ->
      cousinDiamond8Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5 := by
    intro r j hr hj
    cases j with
    | zero => simp [cousinDiamond8Iter]
    | succ j' =>
      have hp16_ge16 : 16 ^ r ≥ 16 := by
        rw [show r = (r - 1) + 1 by omega, Nat.pow_succ]
        have hp := nat_pow_pos_of_pos 16 (by decide) (r - 1); omega
      let x0 := 4 * 16 ^ r - 5
      have hx0_m4 : x0 % 4 = 3 := by dsimp [x0]; omega
      have hx0_pow : 4 * 16 ^ r = 2 ^ (4 * r + 2) := by
        have h16 : 16 ^ r = 2 ^ (4 * r) := by
          rw [show (16 : Nat) = 2 ^ 4 from rfl, pow_pow_eq_mul_w5 2 4 r]
        rw [h16, show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add 2 2 (4 * r), Nat.add_comm 2 (4 * r)]
      have hs_first : cousinDiamond8Step x0 = 2 ^ (4 * r + 1) * 3 ^ 1 - 7 := by
        rw [cousinDiamond8Step_eq_d7_of_not_cone9 x0 (not_cone9_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond7Step_eq_d6_of_not_cone8 x0 (not_cone8_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond6Step_eq_d5_of_not_cone7 x0 (not_cone7_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond5Step_eq_d4_of_not_cone6 x0 (not_cone6_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond4Step_mod4_eq_3 x0 hx0_m4]
        dsimp [x0]
        rw [hx0_pow, show 4 * r + 2 = (4 * r + 1) + 1 by omega, Nat.pow_succ 2 (4 * r + 1)]
        have hp := pow2_pos_nat (4 * r + 1); omega
      have hclimb := cousin_diamond8_cone5_two_step_climb j' (4 * r + 1) 1 (by omega) (by decide)
      let y_end := 2 ^ (4 * r + 1 - 3 * j') * 3 ^ (1 + 2 * j') - 7
      have hy_c5 : isDiamond4Cone5 y_end :=
        isDiamond4Cone5_of_pow2_pow3 (4 * r + 1 - 3 * j') (1 + 2 * j') (by omega) (by omega)
      have hy_nc9 : ¬ isDiamond8Cone9 y_end :=
        not_cone9_of_mod32_ne_13 y_end (by have h := hy_c5.2.1; omega)
      have hy_nc8 : ¬ isDiamond7Cone8 y_end :=
        not_cone8_of_mod32_ne_21 y_end (by have h := hy_c5.2.1; omega)
      have hy_nc7 : ¬ isDiamond6Cone7 y_end :=
        not_cone7_of_mod32_ne_21 y_end (by have h := hy_c5.2.1; omega)
      have hy_nc6 : ¬ isDiamond5Cone6 y_end :=
        not_cone6_of_mod32_ne_13 y_end (by have h := hy_c5.2.1; omega)
      have hs_last : cousinDiamond8Step y_end = 4 * 16 ^ (r - (j' + 1)) * 18 ^ (j' + 1) - 5 := by
        rw [cousinDiamond8Step_eq_d7_of_not_cone9 y_end hy_nc9,
            cousinDiamond7Step_eq_d6_of_not_cone8 y_end hy_nc8,
            cousinDiamond6Step_eq_d5_of_not_cone7 y_end hy_nc7,
            cousinDiamond5Step_eq_d4_of_not_cone6 y_end hy_nc6]
        unfold cousinDiamond4Step; simp only [hy_c5, ite_true]
        dsimp [y_end]
        have ha_sp : 4 * r + 1 - 3 * j' = 2 + (4 * (r - (j' + 1)) + (j' + 1) + 2) := by omega
        have hp2_sp : 2 ^ (4 * r + 1 - 3 * j') = 4 * (4 * 2 ^ (4 * (r - (j' + 1))) * 2 ^ (j' + 1)) := by
          rw [ha_sp, Nat.pow_add 2 2, Nat.pow_add 2 (4 * (r - (j' + 1)) + (j' + 1)) 2,
              Nat.pow_add 2 (4 * (r - (j' + 1))) (j' + 1)]
          change 4 * (2 ^ (4 * (r - (j' + 1))) * 2 ^ (j' + 1) * 4) = _
          rw [Nat.mul_comm (2 ^ (4 * (r - (j' + 1))) * 2 ^ (j' + 1)) 4,
              ← Nat.mul_assoc 4 (2 ^ (4 * (r - (j' + 1)))) (2 ^ (j' + 1))]
        have h16_rj : 2 ^ (4 * (r - (j' + 1))) = 16 ^ (r - (j' + 1)) := by
          rw [show (16 : Nat) = 2 ^ 4 from rfl, pow_pow_eq_mul_w5 2 4]
        have h18_j : 2 ^ (j' + 1) * 3 ^ (2 * (j' + 1)) = 18 ^ (j' + 1) := by
          rw [← pow9_eq_pow3_double (j' + 1), ← mul_pow_local 2 9 (j' + 1)]
        have hp3_sp : 3 * 3 ^ (1 + 2 * j') = 3 ^ (2 * (j' + 1)) := by
          rw [show 2 * (j' + 1) = (1 + 2 * j') + 1 by omega, Nat.pow_succ, Nat.mul_comm]
        have hprod_eq : 3 * (2 ^ (4 * r + 1 - 3 * j') * 3 ^ (1 + 2 * j')) =
            4 * (4 * 16 ^ (r - (j' + 1)) * 18 ^ (j' + 1)) := by
          calc
            3 * (2 ^ (4 * r + 1 - 3 * j') * 3 ^ (1 + 2 * j'))
                = 2 ^ (4 * r + 1 - 3 * j') * (3 * 3 ^ (1 + 2 * j')) := by
                  rw [← Nat.mul_assoc 3, Nat.mul_comm 3 (2 ^ (4 * r + 1 - 3 * j')), Nat.mul_assoc]
            _ = 4 * (4 * 16 ^ (r - (j' + 1)) * 2 ^ (j' + 1)) * 3 ^ (2 * (j' + 1)) := by
                  rw [hp2_sp, h16_rj, hp3_sp]
            _ = 4 * (4 * 16 ^ (r - (j' + 1)) * 18 ^ (j' + 1)) := by
                  rw [Nat.mul_assoc 4, Nat.mul_assoc (4 * 16 ^ (r - (j' + 1))), h18_j]
        have hpos_ge : 4 * 16 ^ (r - (j' + 1)) * 18 ^ (j' + 1) ≥ 72 := by
          have h1 : 1 ≤ 16 ^ (r - (j' + 1)) := nat_pow_pos_of_pos 16 (by decide) _
          have h2 : 18 ≤ 18 ^ (j' + 1) := by
            rw [Nat.pow_succ]; have hp := nat_pow_pos_of_pos 18 (by decide) j'; omega
          simpa using Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl 4) h1) h2
        omega
      rw [show 2 * (j' + 1) = 1 + 2 * j' + 1 by omega,
          cousinDiamond8Iter_add (1 + 2 * j') 1,
          cousinDiamond8Iter_add 1 (2 * j')]
      have hi1 : cousinDiamond8Iter 1 x0 = 2 ^ (4 * r + 1) * 3 ^ 1 - 7 := hs_first
      rw [hi1, hclimb]
      exact hs_last
  refine ⟨by decide, by decide, by decide, by decide, hspiral, ?_⟩
  intro terms A0 B0 C0 hnonempty
  rcases three_family_multiterm_laurent_obstruction terms A0 B0 C0 hnonempty with
    h97 | ⟨j2, hj2⟩ | ⟨r, hr_pos, hr3⟩
  · have hs97 : cousinDiamond8Step 97 = 73 := by decide
    refine ⟨97, by decide, by decide, by rw [hs97]; decide, ?_⟩
    rw [hs97]; exact h97
  · let zj := geomSpineEntry j2
    let Mj := 4 ^ (3 * j2 + 3)
    rcases geomSpineEntry_valuations_constant j2 with ⟨h3zj1, hzj_ge, _, _, _, _⟩
    change 3 * zj + 1 = 4 ^ (3 * j2 + 4) at h3zj1
    change zj ≥ 85 at hzj_ge
    have hMj_ge64 : Mj ≥ 64 := by
      dsimp [Mj]; rw [Nat.pow_add 4 (3 * j2) 3]
      simpa using Nat.mul_le_mul_right 64 (nat_pow_pos_of_pos 4 (by decide) (3 * j2))
    have h3zj1_M : 3 * zj + 1 = 4 * Mj := by
      rw [h3zj1]; dsimp [Mj]
      rw [show 3 * j2 + 4 = (3 * j2 + 3) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    let xj2 := 2 * zj - 1
    let yj2 := 2 * Mj - 1
    have hxj2_odd : xj2 % 2 = 1 := by dsimp [xj2]; omega
    have hc4_xj2 : isDiamond3Cone4 xj2 := by
      refine ⟨by dsimp [xj2]; omega, ?_, ?_⟩
      · have hzj_m4 : zj % 4 = 1 := by omega
        dsimp [xj2]; omega
      · have hpow2 : 3 * xj2 + 5 = 2 ^ (6 * j2 + 9) * 1 := by
          rw [Nat.mul_one, show 6 * j2 + 9 = 2 * (3 * j2 + 4) + 1 by omega,
              Nat.pow_succ, ← pow4_eq_pow2_even (3 * j2 + 4), Nat.mul_comm]
          dsimp [xj2]; omega
        rw [hpow2]
        exact core2_pow2_mul (6 * j2 + 9) 1 (by decide) (by decide)
    have hnc9_xj2 : ¬ isDiamond8Cone9 xj2 :=
      not_cone9_of_mod8_ne_5 xj2 (by have h := hc4_xj2.2.1; omega)
    have hnc8_xj2 : ¬ isDiamond7Cone8 xj2 :=
      not_cone8_of_mod8_ne_5 xj2 (by have h := hc4_xj2.2.1; omega)
    have hnc7_xj2 : ¬ isDiamond6Cone7 xj2 :=
      not_cone7_of_mod8_ne_5 xj2 (by have h := hc4_xj2.2.1; omega)
    have hnc6_xj2 : ¬ isDiamond5Cone6 xj2 := by
      rintro ⟨_, h256, _, _⟩; have h := hc4_xj2.2.1; omega
    have hstep_xj2 : cousinDiamond8Step xj2 = yj2 := by
      rw [cousinDiamond8Step_eq_d7_of_not_cone9 xj2 hnc9_xj2,
          cousinDiamond7Step_eq_d6_of_not_cone8 xj2 hnc8_xj2,
          cousinDiamond6Step_eq_d5_of_not_cone7 xj2 hnc7_xj2,
          cousinDiamond5Step_eq_d4_of_not_cone6 xj2 hnc6_xj2]
      unfold cousinDiamond4Step
      by_cases hc5 : isDiamond4Cone5 xj2
      · simp only [hc5, ite_true]; dsimp [xj2, yj2]; omega
      · simp only [hc5, ite_false]
        rw [cousinDiamond3Step_of_cone4_w8 xj2 hxj2_odd hc4_xj2]
        dsimp [xj2, yj2]; omega
    refine ⟨xj2, by dsimp [xj2]; omega, hxj2_odd, by rw [hstep_xj2]; dsimp [yj2]; omega, ?_⟩
    rw [hstep_xj2]; exact hj2
  · let xr3 := 2 * 4 ^ r - 1
    let zr := 2 * 9 ^ r - 1
    let yr3 := (3 * 9 ^ r - 1) / 2
    have hp9_ge9 : 9 ^ r ≥ 9 := by
      rw [show r = (r - 1) + 1 by omega, Nat.pow_succ]
      have hp := nat_pow_pos_of_pos 9 (by decide) (r - 1); omega
    have hp9_m8 : 9 ^ r % 8 = 1 := pow9_mod8_eq_one_w5 r
    have hxr3_pow : xr3 = 2 ^ (2 * r + 1) * 1 - 1 := by
      dsimp [xr3]; rw [Nat.mul_one, pow4_eq_pow2_even r, Nat.pow_succ, Nat.mul_comm]
    have hglide_i : ∀ i : Nat, i ≤ 2 * r ->
        cousinDiamond8Iter i xr3 = 3 ^ i * 2 ^ (2 * r + 1 - i) - 1 ∧
        cousinDiamond8Iter i xr3 ≥ 7 ∧
        (cousinDiamond8Iter i xr3) % 2 = 1 := by
      intro i hi
      have hf := cousin_diamond8_mersenne_scaled i (2 * r + 1) 1 (by omega) (by decide)
      rw [← hxr3_pow, Nat.mul_one] at hf
      have hprod_ge8 : 3 ^ i * 2 ^ (2 * r + 1 - i) ≥ 8 := by
        have h1 : 2 ^ i * 2 ^ (2 * r + 1 - i) ≤ 3 ^ i * 2 ^ (2 * r + 1 - i) :=
          Nat.mul_le_mul_right _ (pow2_le_pow3 i)
        rw [← Nat.pow_add, show i + (2 * r + 1 - i) = 2 * r + 1 by omega] at h1
        exact Nat.le_trans (pow2_mono_nat (by omega : 3 ≤ 2 * r + 1)) h1
      have hprod_ev : (3 ^ i * 2 ^ (2 * r + 1 - i)) % 2 = 0 := by
        rw [show 2 * r + 1 - i = (2 * r - i) + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc]; omega
      exact ⟨hf, by rw [hf]; omega, by rw [hf]; omega⟩
    have hiter_2r : cousinDiamond8Iter (2 * r) xr3 = zr := by
      have hf := (hglide_i (2 * r) (Nat.le_refl _)).1
      rw [hf, show 2 * r + 1 - 2 * r = 1 by omega, Nat.pow_one,
          ← pow9_eq_pow3_double r, Nat.mul_comm]
    have hstep_zr : cousinDiamond8Step zr = yr3 := by
      rw [cousinDiamond8Step_eq_d7_of_not_cone9 zr (not_cone9_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 zr (not_cone8_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 zr (not_cone7_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 zr (not_cone6_of_mod16_ne_13 zr (by dsimp [zr]; omega))]
      have hnc5 : ¬ isDiamond4Cone5 zr := by rintro ⟨_, h32, _, _⟩; dsimp [zr] at h32; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 zr hnc5]
      have hc3 : core3 (zr + 1) = 2 := by
        rw [show zr + 1 = 2 * 9 ^ r by dsimp [zr]; omega,
            core3_mul2 (9 ^ r) (by omega), (pow9_eq_v3Pow_w5 r).2]
      rw [cousinDiamond3Step_of_core3_succ_two_w8 zr (by dsimp [zr]; omega) (by dsimp [zr]; omega) hc3]
      dsimp [zr, yr3]; omega
    have hiter_2r1 : cousinDiamond8Iter (2 * r + 1) xr3 = yr3 := by
      rw [cousinDiamond8Iter_add (2 * r) 1 xr3, hiter_2r]; exact hstep_zr
    have hall : ∀ i : Nat, i < 2 * r + 1 ->
        cousinDiamond8Iter i xr3 ≥ 3 ∧
        (cousinDiamond8Iter i xr3) % 2 = 1 ∧
        cousinDiamond8Step (cousinDiamond8Iter i xr3) ≥ 3 := by
      intro i hi
      by_cases hlt : i < 2 * r
      · rcases hglide_i i (by omega) with ⟨_, hge7, hodd_i⟩
        have hnext : cousinDiamond8Step (cousinDiamond8Iter i xr3) =
            cousinDiamond8Iter (i + 1) xr3 :=
          (cousinDiamond8Iter_add i 1 xr3).symm
        rcases hglide_i (i + 1) (by omega) with ⟨_, hge7_n, _⟩
        exact ⟨by omega, hodd_i, by rw [hnext]; omega⟩
      · have hi_eq : i = 2 * r := by omega
        rw [hi_eq, hiter_2r, hstep_zr]
        exact ⟨by dsimp [zr]; omega, by dsimp [zr]; omega, by dsimp [yr3]; omega⟩
    change ¬ laurentDescProp terms A0 B0 C0 xr3 yr3 at hr3
    rw [← hiter_2r1] at hr3
    exact exists_non_desc_along_diamond8_iter_clean terms A0 B0 C0 (2 * r + 1) xr3 (by omega) hall hr3

/--
  Theorem W11.3g (`cousin_diamond8_q6_noninteger_avoids_cone9`, choice-free `zero custom axioms`):
  Universal Non-Integer Rational Exclusion from Cone 9 on `M1 = Q_(6)^+`:
  For EVERY reduced non-integer rational `(num, den)` (`Nat.gcd num den = 1` and `den > 1`),
  `core3 (core2 (92275 * den + num)) ≠ den`, so `cousinDiamond8StepQ6 (num, den)` NEVER enters
  Cone 9 and agrees identically with `cousinDiamond7StepQ6 (num, den)`!
-/
theorem cousin_diamond8_q6_noninteger_avoids_cone9 (num den : Nat)
    (hgcd : Nat.gcd num den = 1) (hden : den > 1) :
    core3 (core2 (92275 * den + num)) ≠ den ∧
    cousinDiamond8StepQ6 (num, den) = cousinDiamond7StepQ6 (num, den) := by
  have hne : core3 (core2 (92275 * den + num)) ≠ den := by
    intro heq
    have hdvd_sum : den ∣ (92275 * den + num) := by
      have hc_dvd : core3 (core2 (92275 * den + num)) ∣ (92275 * den + num) :=
        Nat.dvd_trans (core3Aux_dvd_w8 _ _) (core2Aux_dvd_w8 _ _)
      rwa [heq] at hc_dvd
    rcases hdvd_sum with ⟨k, hk⟩
    have hdvd_num : den ∣ num := ⟨k - 92275, by
      have hge : k ≥ 92275 := by
        by_cases hlt : k < 92275
        · have hm := Nat.mul_le_mul_left den (show k ≤ 92274 by omega); omega
        · omega
      rw [Nat.mul_sub_left_distrib]; omega⟩
    have hdvd_gcd : den ∣ Nat.gcd num den := Nat.dvd_gcd hdvd_num (Nat.dvd_refl den)
    rw [hgcd] at hdvd_gcd
    rcases hdvd_gcd with ⟨c, hc⟩
    cases c with
    | zero => omega
    | succ c' =>
      have hle : den * 1 ≤ den * (c' + 1) := Nat.mul_le_mul_left den (by omega)
      omega
  refine ⟨hne, ?_⟩
  unfold cousinDiamond8StepQ6
  have hcond : ¬ (num ≥ 100571021 * den ∧ (num * invMod33554432Odd den) % 33554432 = 33462157 ∧
      (num * (den % 3)) % 3 = 2 ∧ core3 (core2 (92275 * den + num)) = den) :=
    fun ⟨_, _, _, hc⟩ => hne hc
  simp only [hcond, ite_false]

set_option maxRecDepth 16384 in
/--
  Theorem W11.3h (`cousin_diamond8_counter_model_separation`, `[]` axioms):
  `T_diamond8` rejects ALL three Counter-Models (`M1 = Q_(6)^+` 5-cycle `(1, 7) -> ... -> (1, 7)`
  plus non-integer `(100571021, 7)` bypassing Cone 9 by `W11.3g`, `M2 = Z^-` cycles `-1` and
  `-5 -> -7 -> -10 -> -5`, and `M3` supercritical `q = 7` 5-cycle at `5`), AND at the genuine
  `v_2(3x + 1) = 3` Cone-9 jump `100571021 -> 37714133 -> 883925 -> 20717 -> 7769`
  (`ZPOS_COUSIN_DIAMOND8_CONE9_100571021_JUMP`, `16` steps to `1`) strictly increases
  `cousinDiamond2Phi` (`cousinDiamond2Phi 100571021 < cousinDiamond2Phi 37714133`) directly
  into `Cone 8 -> Cone 7 -> Cone 6 -> Cone 5`!
-/
theorem cousin_diamond8_counter_model_separation :
    cousinDiamond8StepInt (-1) = -1 ∧
    cousinDiamond8IterInt 3 (-5) = -5 ∧
    cousinDiamond8IterParam 7 5 5 = 5 ∧
    cousinDiamond8StepQ6 (1, 7) = (5, 7) ∧
    cousinDiamond8IterQ6 5 (1, 7) = (1, 7) ∧
    cousinDiamond8StepQ6 (100571021, 7) = cousinDiamond7StepQ6 (100571021, 7) ∧
    isDiamond8Cone9 100571021 ∧
    cousinDiamond8Step 100571021 = 37714133 ∧
    cousinDiamond8StepInt 100571021 = 37714133 ∧
    cousinDiamond8StepQ6 (100571021, 1) = (37714133, 1) ∧
    isDiamond7Cone8 37714133 ∧
    isDiamond6Cone7 883925 ∧
    isDiamond5Cone6 20717 ∧
    isDiamond4Cone5 7769 ∧
    cousinDiamond2Phi 100571021 < cousinDiamond2Phi 37714133 ∧
    cousinDiamond8Iter 16 100571021 = 1 := by
  decide

-- ============================================================================
-- SECTION 4: Front D (Branches P2.2 & P5.3) — Exact `q = 0` First-Hit Shift
--            Criterion (`canonicalSuffixShift u 1 ≥ 3`), Universal `1^w ↦ 3^(w-1)`
--            Law, Complete Mod-`162` (`2 * 3^4`) Markov Bijection, & Super-Critical
--            `L > M + w + 1` Dyadic-Window Shift-Multiplicity Ceiling
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Section 4A: Universal `1^w ↦ 3^(w-1)` Law & Exact `q = 0` First-Hit Criterion
-- ----------------------------------------------------------------------------

theorem pow2_pow3_succ_dvd_pow3 :
    ∀ k : Nat, ∃ q : Nat, q ≥ 1 ∧ 2 ^ (3 ^ k) + 1 = 3 ^ (k + 1) * q
  | 0 => ⟨1, by decide, by decide⟩
  | k + 1 => by
    rcases pow2_pow3_succ_dvd_pow3 k with ⟨q, hq1, hxk⟩
    let x := 2 ^ (3 ^ k)
    let M := 3 ^ (k + 1)
    change x + 1 = M * q at hxk
    have hx3_eq : 2 ^ (3 ^ (k + 1)) = x * x * x := by
      dsimp [x]
      rw [Nat.pow_succ 3 k, ← pow_pow_eq_mul_w5 2 (3 ^ k) 3,
          Nat.pow_succ _ 2, Nat.pow_two]
    rw [hx3_eq]
    have hcube : (x * x * x + 1) + 3 * x * (x + 1) = (x + 1) * (x + 1) * (x + 1) := by
      have hsq : (x + 1) * (x + 1) = x * x + 2 * x + 1 := by
        rw [Nat.mul_add (x + 1) x 1, Nat.add_mul x 1 x, Nat.one_mul, Nat.mul_one]; omega
      have hcu : (x + 1) * (x + 1) * (x + 1) = x * x * x + 3 * (x * x) + 3 * x + 1 := by
        rw [hsq, Nat.mul_add (x * x + 2 * x + 1) x 1, Nat.mul_one,
            Nat.add_mul (x * x + 2 * x) 1 x, Nat.add_mul (x * x) (2 * x) x,
            Nat.one_mul, Nat.mul_assoc 2 x x]
        generalize x * x * x = xxx, x * x = xx
        omega
      have hmid : 3 * x * (x + 1) = 3 * (x * x) + 3 * x := by
        rw [Nat.mul_add (3 * x) x 1, Nat.mul_one, Nat.mul_assoc 3 x x]
      rw [hcu, hmid]
      generalize x * x * x = xxx, x * x = xx
      omega
    have hM_split : M = 3 * 3 ^ k := by dsimp [M]; rw [Nat.pow_succ, Nat.mul_comm]
    have hM3_eq : (M * q) * (M * q) * (M * q) = 3 ^ (k + 2) * (3 ^ k * M * (q * q * q)) := by
      have h3k2 : 3 ^ (k + 2) = M * 3 := by rw [Nat.pow_succ 3 (k + 1)]
      rw [h3k2]
      calc
        (M * q) * (M * q) * (M * q)
            = M * (M * (M * (q * q * q))) := by ac_rfl
        _ = M * (3 * (3 ^ k * (M * (q * q * q)))) := by
              conv => lhs; rhs; lhs; rw [hM_split]
              rw [Nat.mul_assoc 3 (3 ^ k)]
        _ = (M * 3) * (3 ^ k * M * (q * q * q)) := by
              rw [← Nat.mul_assoc M 3, Nat.mul_assoc (3 ^ k) M]
    have hmid_eq : 3 * x * (M * q) = 3 ^ (k + 2) * (x * q) := by
      have h3k2 : 3 ^ (k + 2) = 3 * M := by rw [Nat.pow_succ 3 (k + 1), Nat.mul_comm]
      rw [h3k2, ← Nat.mul_assoc (3 * x) M q, Nat.mul_assoc 3 x M,
          Nat.mul_comm x M, ← Nat.mul_assoc 3 M x, Nat.mul_assoc (3 * M) x q]
    rw [hxk, hM3_eq, hmid_eq] at hcube
    let Q_hi := 3 ^ k * M * (q * q * q)
    let Q_lo := x * q
    change x * x * x + 1 + 3 ^ (k + 2) * Q_lo = 3 ^ (k + 2) * Q_hi at hcube
    have hpos3k2 : 3 ^ (k + 2) ≥ 1 := pow3_pos_nat (k + 2)
    have hle_Q : Q_lo ≤ Q_hi := by
      apply nat_mul_le_cancel_left_w5 (3 ^ (k + 2)) Q_lo Q_hi hpos3k2
      omega
    have hdiff : x * x * x + 1 = 3 ^ (k + 2) * (Q_hi - Q_lo) := by
      rw [Nat.mul_sub_left_distrib]
      omega
    have hQ_pos : Q_hi - Q_lo ≥ 1 := by
      cases hd : Q_hi - Q_lo with
      | zero => rw [hd, Nat.mul_zero] at hdiff; omega
      | succ _ => omega
    exact ⟨Q_hi - Q_lo, hQ_pos, hdiff⟩

theorem pow2_pow3_mod_pow3_succ (k : Nat) :
    2 ^ (3 ^ k) % 3 ^ (k + 1) = 3 ^ (k + 1) - 1 := by
  rcases pow2_pow3_succ_dvd_pow3 k with ⟨q, hq1, hq_eq⟩
  have hp3 : 3 ^ (k + 1) ≥ 3 := by
    simpa using nat_pow_mono_exp_pos 3 1 (k + 1) (by decide) (by omega)
  have hsp : 2 ^ (3 ^ k) = (3 ^ (k + 1) - 1) + 3 ^ (k + 1) * (q - 1) := by
    have hqm : 3 ^ (k + 1) * q = 3 ^ (k + 1) * (q - 1) + 3 ^ (k + 1) := by
      conv => lhs; rhs; rw [show q = (q - 1) + 1 by omega]
      rw [Nat.mul_add, Nat.mul_one]
    omega
  rw [hsp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem affineCarry_replicate_true :
    ∀ w : Nat,
      (List.replicate w true).length = w ∧
      parityWeight (List.replicate w true) = w ∧
      affineCarry (List.replicate w true) + 2 ^ w = 3 ^ w
  | 0 => ⟨rfl, rfl, by decide⟩
  | w + 1 => by
    rcases affineCarry_replicate_true w with ⟨hlen, hwt, hcar⟩
    have hcons : List.replicate (w + 1) true = [true] ++ List.replicate w true := rfl
    have hcar_step : affineCarry (List.replicate (w + 1) true) =
        3 ^ w + 2 * affineCarry (List.replicate w true) := by
      rw [hcons, affineCarry_append, hwt]
      have hc1 : affineCarry [true] = 1 := rfl
      have hl1 : [true].length = 1 := rfl
      rw [hc1, hl1, Nat.mul_one]
    refine ⟨List.length_replicate, ?_, ?_⟩
    · simp only [List.replicate_succ, parityWeight, hwt]; omega
    · rw [hcar_step, Nat.pow_succ 2 w, Nat.pow_succ 3 w,
          Nat.mul_comm (2 ^ w) 2, Nat.add_assoc, ← Nat.mul_add 2, hcar]
      omega

/--
  Theorem W11.4a (`first_hit_q0_iff_shift_ge_three_and_pow3_ones`, `zero custom axioms`):
  1. **Universal All-Ones `1^w ↦ 3^(w - 1)` Canonical Shift Law (`∀ w ≥ 1`)**:
       `canonicalSuffixShift (List.replicate w true) 1 = 3 ^ (w - 1)`.
  2. **Universal `∀ k ≥ 1` Unrestricted-Prefix All-Ones Suffix Lock**:
     For EVERY `k ≥ 1` and EVERY unrestricted prefix `pref : List Bool`:
       `canonicalSuffixShift (pref ++ List.replicate k true) 1 % (2 * 3 ^ (k - 1)) = 3 ^ (k - 1)`
     (simultaneously yielding `9 mod 18` at `k = 3`, `27 mod 54` at `k = 4`, `81 mod 162` at `k = 5`, etc.!).
  3. **Exact `q = 0` First-Hit Characterization (`∀ u`, `IsCoreParityWord u`)**:
       `IsFirstHitOnePair u 0 ↔ canonicalSuffixShift u 1 ≥ 3`
     (hence `u = [true]` is the unique non-first-hit all-ones core word, while `List.replicate w true`
     for every `w ≥ 2` is a surviving `q = 0` first-hit word with shift `3 ^ (w - 1) ≥ 3`!).
-/
theorem first_hit_q0_iff_shift_ge_three_and_pow3_ones :
    (∀ w : Nat, w ≥ 1 ->
      canonicalSuffixShift (List.replicate w true) 1 = 3 ^ (w - 1)) ∧
    (∀ (k : Nat) (pref : List Bool), k ≥ 1 ->
      canonicalSuffixShift (pref ++ List.replicate k true) 1 % (2 * 3 ^ (k - 1)) = 3 ^ (k - 1)) ∧
    (∀ u : List Bool, IsCoreParityWord u ->
      (IsFirstHitOnePair u 0 ↔ canonicalSuffixShift u 1 ≥ 3)) := by
  have hones : ∀ w : Nat, w ≥ 1 ->
      canonicalSuffixShift (List.replicate w true) 1 = 3 ^ (w - 1) := by
    intro w hw1
    rcases affineCarry_replicate_true w with ⟨hlen, hwt, hcar_sum⟩
    rcases canonicalSuffixShift_spec_unique (List.replicate w true) 1
      (by rw [hwt]; exact hw1) (by decide) with ⟨_, _, huniq⟩
    symm
    apply huniq (3 ^ (w - 1))
    · rw [hwt]
      have hp := pow3_pos_nat (w - 1)
      omega
    · rw [Nat.mul_one, hlen, hwt]
      have hp_lt := pow2_lt_pow3_pos w hw1
      have hp2_pos := pow2_pos_nat w
      have hcar_eq : affineCarry (List.replicate w true) = 3 ^ w - 2 ^ w := by omega
      have hcar_mod : affineCarry (List.replicate w true) % 3 ^ w = 3 ^ w - 2 ^ w := by
        rw [hcar_eq]; exact Nat.mod_eq_of_lt (by omega)
      have hw_sp : (w - 1) + 1 = w := by omega
      have hp_mod := pow2_pow3_mod_pow3_succ (w - 1)
      rw [hw_sp] at hp_mod
      have hlhs : 2 ^ (w + 3 ^ (w - 1)) % 3 ^ w = (2 ^ w * (3 ^ w - 1)) % 3 ^ w := by
        rw [Nat.pow_add 2 w (3 ^ (w - 1)), Nat.mul_mod, hp_mod,
            Nat.mul_mod (2 ^ w) (3 ^ w - 1) (3 ^ w),
            Nat.mod_eq_of_lt (by omega : 3 ^ w - 1 < 3 ^ w)]
      have hmul_mod : (2 ^ w * (3 ^ w - 1)) % 3 ^ w = 3 ^ w - 2 ^ w := by
        have hdecomp : 2 ^ w * (3 ^ w - 1) = (3 ^ w - 2 ^ w) + 3 ^ w * (2 ^ w - 1) := by
          rw [Nat.mul_sub_left_distrib (2 ^ w), Nat.mul_sub_left_distrib (3 ^ w),
              Nat.mul_one, Nat.mul_one, Nat.mul_comm (2 ^ w) (3 ^ w)]
          generalize 2 ^ w = P2, 3 ^ w = P3 at hp_lt hp2_pos ⊢
          have hm : P3 ≤ P3 * P2 := by simpa using Nat.mul_le_mul_left P3 hp2_pos
          omega
        rw [hdecomp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      rw [hlhs, hmul_mod, hcar_mod]
  have hpref_ones : ∀ (k : Nat) (pref : List Bool), k ≥ 1 ->
      canonicalSuffixShift (pref ++ List.replicate k true) 1 % (2 * 3 ^ (k - 1)) = 3 ^ (k - 1) := by
    intro k pref hk1
    rcases affineCarry_replicate_true k with ⟨_, hwt_k, _⟩
    have hann := canonicalSuffixShift_mod18_and_pow3_memory_annihilation.1 pref
      (List.replicate k true) (by rw [hwt_k]; exact hk1)
    rw [hwt_k, hones k hk1] at hann
    have hlt : 3 ^ (k - 1) < 2 * 3 ^ (k - 1) := by have hp := pow3_pos_nat (k - 1); omega
    rw [Nat.mod_eq_of_lt hlt] at hann
    exact hann
  refine ⟨hones, hpref_ones, ?_⟩
  intro u hu
  constructor
  · -- `IsFirstHitOnePair u 0 -> canonicalSuffixShift u 1 ≥ 3`:
    intro hfh
    by_cases hge3 : canonicalSuffixShift u 1 ≥ 3
    · exact hge3
    · exfalso
      have hm6 := core_word_canonicalSuffixShift_mod6_1_or_3 u hu
      have hsh1 : canonicalSuffixShift u 1 = 1 := by rcases hm6 with h | h <;> omega
      rcases list_eq_append_true_of_reverse_head u hu.2 with ⟨v, rfl⟩
      let y := exactBackwardQuotient 1 (v ++ [true]) 0
      let L := backwardOneTotalSteps (v ++ [true]) 0
      have hL_eq : L = v.length + 2 := by
        dsimp [L]; unfold backwardOneTotalSteps
        rw [hsh1, Nat.zero_mul, Nat.add_zero, List.length_append]
        simp
      rcases one_generator_pos_odd_and_reaches_one (v ++ [true]) 0 hu with ⟨_, _, heq, hiterL⟩
      change 2 ^ L = 3 ^ parityWeight (v ++ [true]) * y + affineCarry (v ++ [true]) at heq
      change collatzIter L y = 1 at hiterL
      let w_full := (v ++ [true]) ++ [false]
      have hw_len : w_full.length = L := by
        dsimp [w_full]; rw [List.length_append, List.length_append, hL_eq]; simp
      rcases affineCarry_append_replicate_false (v ++ [true]) 1 with ⟨hwt_w, hcar_w⟩
      have hw_aff : 2 ^ w_full.length * 1 = 3 ^ parityWeight w_full * y + affineCarry w_full := by
        rw [Nat.mul_one, hw_len]; dsimp [w_full]
        have hr1 : List.replicate 1 false = [false] := rfl
        rw [← hr1, hwt_w, hcar_w]; exact heq
      have hw_par := eq_parityOfIter_of_nat_affine w_full y 1 hw_aff
      rw [hw_len] at hw_par
      have hpar_sp : parityOfIter L y = parityOfIter v.length y ++ parityOfIter 2 (collatzIter v.length y) := by
        rw [hL_eq]; exact parityOfIter_append_split v.length 2 y
      have hw_sp2 : w_full = v ++ [true, false] := by
        dsimp [w_full]; rw [List.append_assoc]; rfl
      rw [hw_sp2, hpar_sp] at hw_par
      have hsuf2 := list_append_right_eq_of_eq_len_w5 v (parityOfIter v.length y)
        [true, false] (parityOfIter 2 (collatzIter v.length y))
        (parityOfIter_length v.length y).symm hw_par
      let z := collatzIter v.length y
      have hz_iter2 : collatzIter 2 z = 1 := by
        dsimp [z]; rw [← collatzIter_add v.length 2 y, ← hL_eq]; exact hiterL
      -- From `parityOfIter 2 z = [true, false]` and `collatzIter 2 z = 1`, deduce `z = 1`:
      change [true, false] = parityOfIter 2 z at hsuf2
      have hb0 : (if z % 2 == 0 then false else true) = true := by
        have h := congrArg List.head? hsuf2
        exact Option.some.inj h.symm
      have hz_odd : z % 2 = 1 := by
        by_cases he : z % 2 = 0
        · have ht : (z % 2 == 0) = true := decide_eq_true he
          rw [ht] at hb0; cases hb0
        · omega
      have hstep_z : collatzStep z = (3 * z + 1) / 2 := by
        have hf : (z % 2 == 0) = false := decide_eq_false (by omega)
        simp [collatzStep, hf]
      let z1 := collatzStep z
      have hb1 : (if z1 % 2 == 0 then false else true) = false := by
        have h := congrArg (fun l => List.head? (List.tail l)) hsuf2
        exact Option.some.inj h.symm
      have hz1_ev : z1 % 2 = 0 := by
        by_cases he1 : z1 % 2 = 0
        · exact he1
        · have hf1 : (z1 % 2 == 0) = false := decide_eq_false he1
          rw [hf1] at hb1; cases hb1
      have hstep_z1 : collatzStep z1 = z1 / 2 := by
        have ht : (z1 % 2 == 0) = true := decide_eq_true hz1_ev
        simp [collatzStep, ht]
      change collatzStep (collatzStep z) = 1 at hz_iter2
      change collatzStep z1 = 1 at hz_iter2
      rw [hstep_z1] at hz_iter2
      have hz1_eq2 : z1 = 2 := by omega
      dsimp [z1] at hz1_eq2
      rw [hstep_z] at hz1_eq2
      have hz_eq1 : z = 1 := by omega
      exact hfh.2 v.length (by change v.length < L; rw [hL_eq]; omega) hz_eq1
  · -- `canonicalSuffixShift u 1 ≥ 3 -> IsFirstHitOnePair u 0`:
    intro hsh_ge3
    refine ⟨hu, ?_⟩
    let shift := canonicalSuffixShift u 1
    let y := exactBackwardQuotient 1 u 0
    let L := backwardOneTotalSteps u 0
    have hL_sh : L = u.length + shift := by
      dsimp [L, shift]; unfold backwardOneTotalSteps; simp
    have hu_len : u.length ≥ 1 := by
      cases u with
      | nil => have hh := hu.1; simp at hh
      | cons _ _ => simp
    have hL_ge4 : L ≥ 4 := by omega
    rcases one_generator_pos_odd_and_reaches_one u 0 hu with ⟨_, _, heq, hiterL⟩
    change 2 ^ L = 3 ^ parityWeight u * y + affineCarry u at heq
    change collatzIter L y = 1 at hiterL
    let v := u ++ List.replicate shift false
    have hv_len : v.length = L := by
      dsimp [v]; rw [List.length_append, List.length_replicate, hL_sh]
    rcases affineCarry_append_replicate_false u shift with ⟨hwt_v, hcar_v⟩
    have hv_aff : 2 ^ v.length * 1 = 3 ^ parityWeight v * y + affineCarry v := by
      rw [Nat.mul_one, hv_len, hwt_v, hcar_v]; exact heq
    have hv_par := eq_parityOfIter_of_nat_affine v y 1 hv_aff
    rw [hv_len] at hv_par
    intro j hj hj1
    by_cases hj_last : j = L - 1
    · have hL_split : L = j + 1 := by omega
      rw [hL_split, collatzIter_add j 1 y, hj1] at hiterL
      have hs1 : collatzIter 1 1 = 2 := by decide
      rw [hs1] at hiterL; omega
    · have hsplit_j : L - 2 = j + (L - 2 - j) := by omega
      have htriv : collatzIter (L - 2) y = 1 ∨ collatzIter (L - 2) y = 2 := by
        rw [hsplit_j, collatzIter_add]
        exact collatzIter_triv_one_two_w5 (L - 2 - j) (collatzIter j y) (Or.inl hj1)
      rcases htriv with h_eq1 | h_eq2
      · have hpar_split : parityOfIter L y = parityOfIter (L - 2) y ++ [true, false] := by
          have hLs : L = (L - 2) + 2 := by omega
          conv => lhs; rw [hLs]
          rw [parityOfIter_append_split (L - 2) 2 y, h_eq1]; rfl
        have hv_split : v = (u ++ List.replicate (shift - 2) false) ++ [false, false] := by
          dsimp [v]
          have hs2 : shift = (shift - 2) + 2 := by omega
          conv => lhs; rhs; rw [hs2]
          rw [replicate_false_split_w5 (shift - 2) 2, ← List.append_assoc]; rfl
        rw [hv_split, hpar_split] at hv_par
        have hlen_pre : (u ++ List.replicate (shift - 2) false).length =
            (parityOfIter (L - 2) y).length := by
          rw [List.length_append, List.length_replicate, parityOfIter_length]; omega
        have hsuf := list_append_right_eq_of_eq_len_w5 _ _ [false, false] [true, false]
          hlen_pre hv_par
        simp at hsuf
      · have hLs : L = (L - 2) + 2 := by omega
        rw [hLs, collatzIter_add (L - 2) 2 y, h_eq2] at hiterL
        have hs2 : collatzIter 2 2 = 2 := by decide
        rw [hs2] at hiterL; omega

-- ----------------------------------------------------------------------------
-- Section 4B: Complete Mod-`162` (`2 * 3^4`) Markov Bijection & `81 mod 162` Lock (`P5.3`)
-- ----------------------------------------------------------------------------

def survivingMod162List : List Nat :=
  [1, 3, 7, 9, 13, 15, 19, 21, 25, 27, 31, 33, 37, 39, 43, 45, 49, 51,
   55, 57, 61, 63, 67, 69, 73, 75, 79, 81, 85, 87, 91, 93, 97, 99, 103, 105,
   109, 111, 115, 117, 121, 123, 127, 129, 133, 135, 139, 141, 145, 147, 151, 153, 157, 159]

def markovShiftTrue4Mod162Table (x : Fin 54) : Nat :=
  match x.val with
  | 0  => 1   | 1  => 69  | 2  => 7   | 3  => 45  | 4  => 139 | 5  => 57
  | 6  => 127 | 7  => 51  | 8  => 25  | 9  => 135 | 10 => 49  | 11 => 93
  | 12 => 91  | 13 => 33  | 14 => 43  | 15 => 63  | 16 => 121 | 17 => 129
  | 18 => 55  | 19 => 15  | 20 => 61  | 21 => 153 | 22 => 31  | 23 => 3
  | 24 => 19  | 25 => 159 | 26 => 79  | 27 => 81  | 28 => 103 | 29 => 39
  | 30 => 145 | 31 => 141 | 32 => 97  | 33 => 9   | 34 => 13  | 35 => 75
  | 36 => 109 | 37 => 123 | 38 => 115 | 39 => 99  | 40 => 85  | 41 => 111
  | 42 => 73  | 43 => 105 | 44 => 133 | 45 => 27  | 46 => 157 | 47 => 147
  | 48 => 37  | 49 => 87  | 50 => 151 | 51 => 117 | 52 => 67  | _  => 21

private theorem markovShiftTrue4_eq_table :
    ∀ x : Fin 54, markovShiftTrue 4 x.val % 162 = markovShiftTrue4Mod162Table x := by
  decide

private theorem markovShiftTrue4_table_inj :
    ∀ x1 x2 : Fin 54, markovShiftTrue4Mod162Table x1 = markovShiftTrue4Mod162Table x2 -> x1 = x2 := by
  decide

private theorem markovShiftTrue4_table_mem :
    ∀ x : Fin 54, markovShiftTrue4Mod162Table x ∈ survivingMod162List := by
  decide

/--
  Theorem W11.4b (`markovShift_mod162_bijection_and_five_ones_81_lock`, `zero custom axioms`):
  Complete Mod-`162` (`2 * 3^4`) Markov Image Bijection, `108 / 162 = 2 / 3` Forbidden-Residue
  Confinement on `w(u) ≥ 5`, & Universal `5`-Ones `81 mod 162` Suffix Lock (`Branch P5.3`):
  1. **Exact Mod-`162` Contraction & Bijection onto `54` Odd Non-`5 mod 6` Classes (`∀ w ≥ 4`)**:
     For EVERY weight `w ≥ 4` and `a < 2 * 3 ^ (w - 1)`,
       `markovShiftTrue w a % 162 = markovShiftTrue 4 (a % 54) % 162`,
     and `r ↦ markovShiftTrue 4 r.val % 162` is strictly injective on `Fin 54`, mapping `[0, 54)`
     bijectively onto the `54`-element `survivingMod162List`!
  2. **Universal `108 / 162` Core-Word Confinement (`∀ u`, `IsCoreParityWord u`, `parityWeight u ≥ 5`)**:
       `canonicalSuffixShift u 1 % 162 ∈ survivingMod162List`!
  3. **Exact Mod-`162` Suffix Locks Across Unrestricted Prefixes**:
     - For EVERY `pref : List Bool` with `parityWeight pref ≥ 1`:
       `canonicalSuffixShift (pref ++ [true, true, true, true]) 1 % 162 = 81 ∨
        canonicalSuffixShift (pref ++ [true, true, true, true]) 1 % 162 = 135`;
     - For EVERY completely unrestricted `pref : List Bool` (including `pref = []`):
       `canonicalSuffixShift (pref ++ [true, true, true, true, true]) 1 % 162 = 81` AND
       `canonicalSuffixShift (pref ++ [true, false, true, true, true, true]) 1 % 162 = 135`!
-/
theorem markovShift_mod162_bijection_and_five_ones_81_lock :
    ((∀ (w a : Nat), w ≥ 4 -> a < 2 * 3 ^ (w - 1) ->
        markovShiftTrue w a % 162 = markovShiftTrue 4 (a % 54) % 162) ∧
     survivingMod162List.length = 54 ∧
     (∀ x1 x2 : Fin 54,
        markovShiftTrue 4 x1.val % 162 = markovShiftTrue 4 x2.val % 162 -> x1 = x2) ∧
     (∀ x : Fin 54,
        markovShiftTrue 4 x.val % 162 ∈ survivingMod162List)) ∧
    (∀ u : List Bool, IsCoreParityWord u -> parityWeight u ≥ 5 ->
      canonicalSuffixShift u 1 % 162 ∈ survivingMod162List) ∧
    ((∀ pref : List Bool, parityWeight pref ≥ 1 ->
        canonicalSuffixShift (pref ++ [true, true, true, true]) 1 % 162 = 81 ∨
        canonicalSuffixShift (pref ++ [true, true, true, true]) 1 % 162 = 135) ∧
     (∀ pref : List Bool,
        canonicalSuffixShift (pref ++ [true, true, true, true, true]) 1 % 162 = 81 ∧
        canonicalSuffixShift (pref ++ [true, false, true, true, true, true]) 1 % 162 = 135)) := by
  have hcongr162 : ∀ (w a : Nat), w ≥ 4 -> a < 2 * 3 ^ (w - 1) ->
      markovShiftTrue w a % 162 = markovShiftTrue 4 (a % 54) % 162 := by
    intro w a hw4 ha_lt
    have hr_lt : a % 54 < 2 * 3 ^ (4 - 1) := Nat.mod_lt a (by decide)
    exact markovShiftTrue_contraction_mod_pow3 3 w 4 a (a % 54)
      (by omega) (by decide) ha_lt hr_lt (by simp)
  have hinj54 : ∀ x1 x2 : Fin 54,
      markovShiftTrue 4 x1.val % 162 = markovShiftTrue 4 x2.val % 162 -> x1 = x2 := by
    intro x1 x2 heq
    rw [markovShiftTrue4_eq_table x1, markovShiftTrue4_eq_table x2] at heq
    exact markovShiftTrue4_table_inj x1 x2 heq
  have hmem54 : ∀ x : Fin 54, markovShiftTrue 4 x.val % 162 ∈ survivingMod162List := by
    intro x
    rw [markovShiftTrue4_eq_table x]
    exact markovShiftTrue4_table_mem x
  refine ⟨⟨hcongr162, rfl, hinj54, hmem54⟩, ?_, ⟨?_, ?_⟩⟩
  · -- Core-word mod-`162` confinement on `w(u) ≥ 5`:
    intro u hu hw5
    rcases list_eq_append_true_of_reverse_head u hu.2 with ⟨v, rfl⟩
    have hw_v : parityWeight v ≥ 4 := by
      rw [parityWeight_append] at hw5
      have h1 : parityWeight [true] = 1 := rfl
      rw [h1] at hw5; omega
    have hrec : canonicalSuffixShift (v ++ [true]) 1 =
        markovShiftTrue (parityWeight v) (canonicalSuffixShift v 1) :=
      (canonicalSuffixShift_append_markov_recurrence.2.2 v (by omega)).2.2.1
    have ha_lt := (canonicalSuffixShift_spec_unique v 1 (by omega) (by decide)).1
    rw [hrec, hcongr162 (parityWeight v) (canonicalSuffixShift v 1) hw_v ha_lt]
    exact hmem54 ⟨canonicalSuffixShift v 1 % 54, Nat.mod_lt _ (by decide)⟩
  · -- `pref ++ [true, true, true, true]` (`parityWeight pref ≥ 1`) mod `162 ∈ {81, 135}`:
    intro pref hwp
    have hap1 := iterMarkovShift_append_canonical [true, true, true, true] pref hwp
    have ha_lt := (canonicalSuffixShift_spec_unique pref 1 hwp (by decide)).1
    by_cases hpar : canonicalSuffixShift pref 1 % 2 = 0
    · right
      have hbase0 : canonicalSuffixShift [true, false] 1 % 2 = 0 := by decide
      have hap0 := iterMarkovShift_append_canonical [true, true, true, true] [true, false] (by decide)
      change canonicalSuffixShift ([true, false] ++ [true, true, true, true]) 1 =
        iterMarkovShift [true, true, true, true] 1 (canonicalSuffixShift [true, false] 1) at hap0
      have hc := iterMarkovShift_congr_mod_pow3 [true, true, true, true] 0 (parityWeight pref) 1
        (canonicalSuffixShift pref 1) (canonicalSuffixShift [true, false] 1)
        hwp (by decide) ha_lt (by decide)
        (by simp only [Nat.pow_zero, Nat.mul_one]; exact hpar.trans hbase0.symm)
      rw [← hap1, ← hap0] at hc
      have hv : canonicalSuffixShift ([true, false] ++ [true, true, true, true]) 1 % 162 = 135 := by decide
      exact hc.trans hv
    · left
      have hodd : canonicalSuffixShift pref 1 % 2 = 1 := by omega
      have hbase1 : canonicalSuffixShift [true] 1 % 2 = 1 := by decide
      have hap1' := iterMarkovShift_append_canonical [true, true, true, true] [true] (by decide)
      change canonicalSuffixShift ([true] ++ [true, true, true, true]) 1 =
        iterMarkovShift [true, true, true, true] 1 (canonicalSuffixShift [true] 1) at hap1'
      have hc := iterMarkovShift_congr_mod_pow3 [true, true, true, true] 0 (parityWeight pref) 1
        (canonicalSuffixShift pref 1) (canonicalSuffixShift [true] 1)
        hwp (by decide) ha_lt (by decide)
        (by simp only [Nat.pow_zero, Nat.mul_one]; exact hodd.trans hbase1.symm)
      rw [← hap1, ← hap1'] at hc
      have hv : canonicalSuffixShift ([true] ++ [true, true, true, true]) 1 % 162 = 81 := by decide
      exact hc.trans hv
  · -- Unrestricted `pref ++ [true, true, true, true, true]` and `pref ++ [true, false, true, true, true, true]`:
    intro pref
    have ha1 := first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.1 5 pref (by decide)
    have ha2 := canonicalSuffixShift_mod18_and_pow3_memory_annihilation.2.1 4 pref
      [true, false, true, true, true, true] (by decide)
    have hv2 : canonicalSuffixShift [true, false, true, true, true, true] 1 % 162 = 135 := by decide
    exact ⟨by simpa using ha1, by simpa using ha2.trans hv2⟩

-- ----------------------------------------------------------------------------
-- Section 4C: Super-Critical `L > M + w + 1` Dyadic-Window Shift-Multiplicity Law (`P2.2`)
-- ----------------------------------------------------------------------------

/--
  Theorem W11.4c (`dyadic_window_supercritical_shift_multiplicity`, `zero custom axioms`):
  Universal All-Length (`∀ L ≥ 1`, Including Super-Critical `L > M + w + 1`) Dyadic-Window
  Shift-Spread Ceiling, First-Layer `≤ 2`-Shift / `3 mod 6` Pinning, & Length-Split Sharpness (`Branch P2.2`):
  1. **Exact Coupled Exponential Shift-Gap Inequality Across ALL Lengths `L ≥ 1`**:
     For ANY two core words `u1, u2` in `[2 ^ M, 2 ^ (M + 1))` with `u1.length = u2.length`,
     `parityWeight u1 = parityWeight u2`, and `canonicalSuffixShift u1 1 ≤ canonicalSuffixShift u2 1`:
       `2 ^ (canonicalSuffixShift u2 1 - canonicalSuffixShift u1 1 + M + parityWeight u1) <
          2 ^ (M + parityWeight u1 + 1) + 2 ^ u1.length`!
  2. **Universal All-Length Shift-Spread Ceiling (`∀ L ≥ 1`, Recovering Sub-Critical Uniqueness at `E = 0`)**:
       `canonicalSuffixShift u2 1 - canonicalSuffixShift u1 1 ≤
          (u1.length - (M + parityWeight u1 + 1)) + 1`!
     (When `u1.length ≤ M + parityWeight u1 + 1`, the RHS is `1`, and parity of shifts immediately forces
     `canonicalSuffixShift u2 1 = canonicalSuffixShift u1 1`!)
  3. **First Super-Critical Layer (`u1.length = M + parityWeight u1 + 2`, `E = 1`)**:
     - `canonicalSuffixShift u2 1 = canonicalSuffixShift u1 1 ∨
        canonicalSuffixShift u2 1 = canonicalSuffixShift u1 1 + 2` (at most `2` shifts!), AND
     - Whenever `canonicalSuffixShift u1 1 % 6 = 3`, `canonicalSuffixShift u2 1 = canonicalSuffixShift u1 1`
       (uniquely pinned even in the super-critical regime because `(a1 + 2) % 6 = 5` is forbidden!)!
  4. **Concrete Length-Conditioning & Super-Critical Witnesses (`ZPOS_DYADIC_WINDOW_M6_W3_LENGTH_SPLIT_69_VS_75`, `W11_H4`)**:
     Inside `[2 ^ 6, 2 ^ 7) = [64, 128)`:
     - `u69 = [true, false, false, false, true, false, false, true]` (`y = 69, L = 8, w = 3, a = 3`) and
       `u75 = [true, true, false, true]` (`y = 75, L = 4, w = 3, a = 7`) share `(M, w) = (6, 3)` yet `3 ≠ 7`,
       refuting length-blind `(M, w)` shift-pinning!
     - `u99` (`y = 99`, `L = 15 = 6 + 7 + 2`, `w = 7`, `a = 3`, `E = 1`) and `u111` (`y = 111`,
       `L = 42 = 6 + 24 + 1 + 11`, `w = 24`, `a = 3`, `E = 11`) are genuine surviving `q = 0` first-hit
       leaves inside the super-critical regime `L > M + w + 1`!
-/
theorem dyadic_window_supercritical_shift_multiplicity :
    (∀ (u1 u2 : List Bool) (M : Nat),
      IsCoreParityWord u1 -> IsCoreParityWord u2 ->
      u1.length = u2.length ->
      parityWeight u1 = parityWeight u2 ->
      canonicalSuffixShift u1 1 ≤ canonicalSuffixShift u2 1 ->
      2 ^ M ≤ exactBackwardQuotient 1 u1 0 -> exactBackwardQuotient 1 u1 0 < 2 ^ (M + 1) ->
      2 ^ M ≤ exactBackwardQuotient 1 u2 0 -> exactBackwardQuotient 1 u2 0 < 2 ^ (M + 1) ->
      2 ^ (canonicalSuffixShift u2 1 - canonicalSuffixShift u1 1 + M + parityWeight u1) <
        2 ^ (M + parityWeight u1 + 1) + 2 ^ u1.length ∧
      canonicalSuffixShift u2 1 - canonicalSuffixShift u1 1 ≤
        (u1.length - (M + parityWeight u1 + 1)) + 1) ∧
    (∀ (u1 u2 : List Bool) (M : Nat),
      IsCoreParityWord u1 -> IsCoreParityWord u2 ->
      u1.length = u2.length ->
      parityWeight u1 = parityWeight u2 ->
      u1.length = M + parityWeight u1 + 2 ->
      canonicalSuffixShift u1 1 ≤ canonicalSuffixShift u2 1 ->
      2 ^ M ≤ exactBackwardQuotient 1 u1 0 -> exactBackwardQuotient 1 u1 0 < 2 ^ (M + 1) ->
      2 ^ M ≤ exactBackwardQuotient 1 u2 0 -> exactBackwardQuotient 1 u2 0 < 2 ^ (M + 1) ->
      (canonicalSuffixShift u2 1 = canonicalSuffixShift u1 1 ∨
       canonicalSuffixShift u2 1 = canonicalSuffixShift u1 1 + 2) ∧
      (canonicalSuffixShift u1 1 % 6 = 3 ->
        canonicalSuffixShift u2 1 = canonicalSuffixShift u1 1)) ∧
    (let u69 : List Bool := [true, false, false, false, true, false, false, true]
     let u75 : List Bool := [true, true, false, true]
     let u99 : List Bool :=
       [true, true, false, false, false, false, false, true, true, true, false, true, false, false, true]
     let u111 : List Bool :=
       [true, true, true, true, false, true, true, false, true, true, true, true, true, true,
        false, false, true, true, true, true, false, false, false, true, false, true, false, true,
        false, false, false, true, false, false, true, true, true, false, false, false, false, true]
     IsFirstHitOnePair u69 0 ∧ IsFirstHitOnePair u75 0 ∧
     IsFirstHitOnePair u99 0 ∧ IsFirstHitOnePair u111 0 ∧
     u69.length = 8 ∧ u75.length = 4 ∧ parityWeight u69 = 3 ∧ parityWeight u75 = 3 ∧
     exactBackwardQuotient 1 u69 0 = 69 ∧ exactBackwardQuotient 1 u75 0 = 75 ∧
     canonicalSuffixShift u69 1 = 3 ∧ canonicalSuffixShift u75 1 = 7 ∧
     exactBackwardQuotient 1 u99 0 = 99 ∧ canonicalSuffixShift u99 1 = 3 ∧
     u99.length = 6 + parityWeight u99 + 2 ∧
     u111.length = 42 ∧ parityWeight u111 = 24 ∧
     exactBackwardQuotient 1 u111 0 = 111 ∧
     canonicalSuffixShift u111 1 = 3 ∧
     2 ^ 6 ≤ 111 ∧ 111 < 2 ^ 7 ∧ u111.length - (6 + parityWeight u111 + 1) = 11) := by
  have hmain : ∀ (u1 u2 : List Bool) (M : Nat),
      IsCoreParityWord u1 -> IsCoreParityWord u2 ->
      u1.length = u2.length ->
      parityWeight u1 = parityWeight u2 ->
      canonicalSuffixShift u1 1 ≤ canonicalSuffixShift u2 1 ->
      2 ^ M ≤ exactBackwardQuotient 1 u1 0 -> exactBackwardQuotient 1 u1 0 < 2 ^ (M + 1) ->
      2 ^ M ≤ exactBackwardQuotient 1 u2 0 -> exactBackwardQuotient 1 u2 0 < 2 ^ (M + 1) ->
      2 ^ (canonicalSuffixShift u2 1 - canonicalSuffixShift u1 1 + M + parityWeight u1) <
        2 ^ (M + parityWeight u1 + 1) + 2 ^ u1.length ∧
      canonicalSuffixShift u2 1 - canonicalSuffixShift u1 1 ≤
        (u1.length - (M + parityWeight u1 + 1)) + 1 := by
    intro u1 u2 M hu1 hu2 hL hw ha_le hlo1 hhi1 hlo2 hhi2
    rcases dyadic_window_unique_shift_pinning_and_l2_energy.1 u1 M hu1 hlo1 hhi1 with
      ⟨hgt1, _, _, _⟩
    rcases dyadic_window_unique_shift_pinning_and_l2_energy.1 u2 M hu2 hlo2 hhi2 with
      ⟨_, hlt2, _, _⟩
    rw [← hL, ← hw] at hlt2
    let L := u1.length
    let w := parityWeight u1
    let a1 := canonicalSuffixShift u1 1
    let a2 := canonicalSuffixShift u2 1
    have hw_le_L : w ≤ L := parityWeight_le_length u1
    change 3 ^ w * 2 ^ M < 2 ^ (L + a1) at hgt1
    change 2 ^ (L + a2) < 3 ^ w * (2 ^ (M + 1) + 2 ^ (L - w)) at hlt2
    change a1 ≤ a2 at ha_le
    -- Multiply `hlt2` by `2 ^ w` to clear `L - w`:
    have hlt2_w : 2 ^ (L + a2 + w) < 3 ^ w * (2 ^ (M + w + 1) + 2 ^ L) := by
      have hm := Nat.mul_lt_mul_of_pos_right hlt2 (pow2_pos_nat w)
      rw [← Nat.pow_add 2 (L + a2) w, Nat.mul_assoc (3 ^ w),
          Nat.add_mul (2 ^ (M + 1)) (2 ^ (L - w)) (2 ^ w),
          ← Nat.pow_add 2 (M + 1) w, ← Nat.pow_add 2 (L - w) w,
          show (M + 1) + w = M + w + 1 by omega,
          show (L - w) + w = L by omega] at hm
      exact hm
    -- Multiply `3^w * 2^M < 2^(L + a1)` and `2^(L + a2 + w) < 3^w * (...)`:
    have hprod_lt : 2 ^ (L + a2 + w) * (3 ^ w * 2 ^ M) <
        2 ^ (L + a1) * (3 ^ w * (2 ^ (M + w + 1) + 2 ^ L)) := by
      have h1 : 2 ^ (L + a2 + w) * (3 ^ w * 2 ^ M) < 2 ^ (L + a2 + w) * 2 ^ (L + a1) :=
        Nat.mul_lt_mul_of_pos_left hgt1 (pow2_pos_nat _)
      have h2 : 2 ^ (L + a2 + w) * 2 ^ (L + a1) ≤
          (3 ^ w * (2 ^ (M + w + 1) + 2 ^ L)) * 2 ^ (L + a1) :=
        Nat.mul_le_mul_right _ (Nat.le_of_lt hlt2_w)
      have hr := Nat.lt_of_lt_of_le h1 h2
      rwa [Nat.mul_comm _ (2 ^ (L + a1))] at hr
    -- Factor out `(2 ^ (L + a1) * 3 ^ w)` on both sides:
    have hlhs_fac : 2 ^ (L + a2 + w) * (3 ^ w * 2 ^ M) =
        (2 ^ (L + a1) * 3 ^ w) * 2 ^ (a2 - a1 + M + w) := by
      have hexp : (L + a2 + w) + M = (L + a1) + (a2 - a1 + M + w) := by omega
      calc
        2 ^ (L + a2 + w) * (3 ^ w * 2 ^ M)
            = 3 ^ w * (2 ^ (L + a2 + w) * 2 ^ M) := by
              rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ (L + a2 + w)) (3 ^ w), Nat.mul_assoc]
        _ = 3 ^ w * 2 ^ ((L + a2 + w) + M) := by rw [← Nat.pow_add]
        _ = 3 ^ w * (2 ^ (L + a1) * 2 ^ (a2 - a1 + M + w)) := by rw [hexp, Nat.pow_add]
        _ = (2 ^ (L + a1) * 3 ^ w) * 2 ^ (a2 - a1 + M + w) := by
              rw [← Nat.mul_assoc (3 ^ w), Nat.mul_comm (3 ^ w) (2 ^ (L + a1))]
    have hrhs_fac : 2 ^ (L + a1) * (3 ^ w * (2 ^ (M + w + 1) + 2 ^ L)) =
        (2 ^ (L + a1) * 3 ^ w) * (2 ^ (M + w + 1) + 2 ^ L) :=
      (Nat.mul_assoc _ _ _).symm
    rw [hlhs_fac, hrhs_fac] at hprod_lt
    have hfac_pos : 2 ^ (L + a1) * 3 ^ w ≥ 1 :=
      Nat.mul_le_mul (pow2_pos_nat _) (pow3_pos_nat _)
    have hexp_gap : 2 ^ (a2 - a1 + M + w) < 2 ^ (M + w + 1) + 2 ^ L := by
      by_cases hlt : 2 ^ (a2 - a1 + M + w) < 2 ^ (M + w + 1) + 2 ^ L
      · exact hlt
      · exfalso
        have hge : 2 ^ (M + w + 1) + 2 ^ L ≤ 2 ^ (a2 - a1 + M + w) := Nat.not_lt.mp hlt
        exact Nat.not_le_of_gt hprod_lt (Nat.mul_le_mul_left (2 ^ (L + a1) * 3 ^ w) hge)
    refine ⟨hexp_gap, ?_⟩
    -- Bound `2 ^ (M + w + 1) + 2 ^ L ≤ 2 ^ (M + w + 2 + E)` where `E := L - (M + w + 1)`:
    let E := L - (M + w + 1)
    have h1_le : 2 ^ (M + w + 1) ≤ 2 ^ (M + w + 1 + E) := pow2_mono_nat (by omega)
    have h2_le : 2 ^ L ≤ 2 ^ (M + w + 1 + E) := pow2_mono_nat (by dsimp [E]; omega)
    have hsum_le : 2 ^ (M + w + 1) + 2 ^ L ≤ 2 ^ (M + w + E + 2) := by
      have hm := Nat.add_le_add h1_le h2_le
      have hp2 : 2 ^ (M + w + 1 + E) + 2 ^ (M + w + 1 + E) = 2 ^ (M + w + E + 2) := by
        rw [show M + w + E + 2 = (M + w + 1 + E) + 1 by omega, Nat.pow_succ]
        omega
      rwa [hp2] at hm
    have hp_lt := Nat.lt_of_lt_of_le hexp_gap hsum_le
    change a2 - a1 ≤ E + 1
    by_cases hle : a2 - a1 ≤ E + 1
    · exact hle
    · have hm := pow2_mono_nat (by omega : M + w + E + 2 ≤ a2 - a1 + M + w)
      omega
  refine ⟨hmain, ?_, ?_⟩
  · -- Part 2: First super-critical layer `L = M + w + 2` (`E = 1`):
    intro u1 u2 M hu1 hu2 hL hw hL_sc ha_le hlo1 hhi1 hlo2 hhi2
    rcases hmain u1 u2 M hu1 hu2 hL hw ha_le hlo1 hhi1 hlo2 hhi2 with ⟨_, hspread⟩
    have hm6_1 := core_word_canonicalSuffixShift_mod6_1_or_3 u1 hu1
    have hm6_2 := core_word_canonicalSuffixShift_mod6_1_or_3 u2 hu2
    have hsp_le2 : canonicalSuffixShift u2 1 - canonicalSuffixShift u1 1 ≤ 2 := by
      rw [hL_sc] at hspread; omega
    have ha1_odd : canonicalSuffixShift u1 1 % 2 = 1 := by rcases hm6_1 with h | h <;> omega
    have ha2_odd : canonicalSuffixShift u2 1 % 2 = 1 := by rcases hm6_2 with h | h <;> omega
    have hor : canonicalSuffixShift u2 1 = canonicalSuffixShift u1 1 ∨
        canonicalSuffixShift u2 1 = canonicalSuffixShift u1 1 + 2 := by omega
    refine ⟨hor, ?_⟩
    intro hm6_eq3
    rcases hor with heq | hplus2
    · exact heq
    · exfalso
      rw [hplus2] at hm6_2
      rcases hm6_2 with h1 | h3 <;> omega
  · -- Part 3: Concrete witnesses `u69`, `u75`, `u99`, `u111` in `[64, 128)`:
    dsimp only
    let u69 : List Bool := [true, false, false, false, true, false, false, true]
    let u75 : List Bool := [true, true, false, true]
    let u99 : List Bool :=
      [true, true, false, false, false, false, false, true, true, true, false, true, false, false, true]
    let u111 : List Bool :=
      [true, true, true, true, false, true, true, false, true, true, true, true, true, true,
       false, false, true, true, true, true, false, false, false, true, false, true, false, true,
       false, false, false, true, false, false, true, true, true, false, false, false, false, true]
    have ha99 : canonicalSuffixShift u99 1 = 3 :=
      ((canonicalSuffixShift_spec_unique u99 1 (by decide) (by decide)).2.2
        3 (by decide) (by decide)).symm
    have hq99 : exactBackwardQuotient 1 u99 0 = 99 := by
      unfold exactBackwardQuotient; dsimp only; rw [ha99]; decide
    have ha111 : canonicalSuffixShift u111 1 = 3 :=
      ((canonicalSuffixShift_spec_unique u111 1 (by decide) (by decide)).2.2
        3 (by decide) (by decide)).symm
    have hq111 : exactBackwardQuotient 1 u111 0 = 111 := by
      unfold exactBackwardQuotient; dsimp only; rw [ha111]; decide
    have hfh69 : IsFirstHitOnePair u69 0 :=
      (first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.2 u69 ⟨rfl, rfl⟩).mpr (by decide)
    have hfh75 : IsFirstHitOnePair u75 0 :=
      (first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.2 u75 ⟨rfl, rfl⟩).mpr (by decide)
    have hfh99 : IsFirstHitOnePair u99 0 :=
      (first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.2 u99 ⟨rfl, rfl⟩).mpr
        (by rw [ha99]; decide)
    have hfh111 : IsFirstHitOnePair u111 0 :=
      (first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.2 u111 ⟨rfl, rfl⟩).mpr
        (by rw [ha111]; decide)
    exact ⟨hfh69, hfh75, hfh99, hfh111,
           rfl, rfl, by decide, by decide,
           by decide, by decide, by decide, by decide,
           hq99, ha99, by decide,
           rfl, by decide, hq111, ha111,
           by decide, by decide, by decide⟩

theorem isSurvivingMod373248Bool_imp_class (n : Nat)
    (hb : isSurvivingMod373248Bool n = true) :
    IsSurvivingMod373248Class n := by
  unfold isSurvivingMod373248Bool isSurvivingMod512Bool isSurvivingMod64Bool isSurvivingMod729Bool at hb
  unfold IsSurvivingMod373248Class IsSurvivingMod512Residue IsSurvivingMod64Residue IsSurvivingMod729Residue
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
             beq_iff_eq, beq_eq_false_iff_ne, decide_eq_true_eq] at hb
  rcases hb with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h512_lt, h64⟩, h128_7⟩, h128_59⟩, h128_95⟩,
                                h256_39⟩, h256_63⟩, h256_123⟩, h256_175⟩, h256_199⟩,
                              h256_219⟩, h287⟩, h367⟩, h383⟩, h411⟩, h487⟩,
                  ⟨⟨⟨⟨⟨⟨⟨⟨⟨h729_lt, h3⟩, h9⟩, h81_10⟩, h81_60⟩, h45⟩, h159⟩, h330⟩, h433⟩, h604⟩⟩
  exact ⟨⟨h512_lt, by omega, h128_7, h128_59, h128_95, h256_39, h256_63, h256_123,
          h256_175, h256_199, h256_219, h287, h367, h383, h411, h487⟩,
         ⟨h729_lt, h3, h9, h81_10, h81_60, h45, h159, h330, h433, h604⟩⟩

/--
  Theorem W11.4d (`dyadic_window_surviving_leaves_mod162_fiber_and_cell_occupancy`, `zero custom axioms`):
  Coupled Surviving Dyadic-Window Leaves (`dyadicWindowSurvivingQ0Leaves L_max M`), Automatic
  `w ≥ 6` / `|u| ≥ 8` Mod-`162` (`54/162`) Confinement, `3^(w - 5)` Fiber Equidistribution, &
  Per-Cell Shift-Multiplicity / Occupancy Bounds (`Branches P2.2 & P5.3`):
  1. **Universal Surviving-Window Leaf Decomposition & Automatic `54/162` Confinement (`∀ L_max, M`)**:
     Every `y ∈ dyadicWindowSurvivingQ0Leaves L_max M` is realized by a UNIQUE core parity word `u`
     (`IsFirstHitOnePair u 0 ∧ u.length ≤ L_max`) satisfying:
     - `IsSurvivingMod373248Class y ∧ y ≥ 27 ∧ 2 ^ M ≤ y ∧ y < 2 ^ (M + 1)`,
     - **`parityWeight u ≥ 6` AND `u.length ≥ 8`** (eliminating all low-weight sectors `w ≤ 5`), AND
     - **`canonicalSuffixShift u 1 ≥ 3` AND `canonicalSuffixShift u 1 % 162 ∈ survivingMod162List`**
       (`54 / 162` surviving classes across 100% of `dyadicWindowSurvivingQ0Leaves L_max M`)!
  2. **Mod-`162` (`j = 4`) Multi-Step `3 ^ (w - 5)` Fiber Equidistribution (`∀ tail, ∀ w ≥ 5, ∀ r0 < 162`)**:
     Along any suffix `tail : List Bool` from coarse weight `w ≥ 5`, `iterMarkovShift tail w` maps
     the `3 ^ (w - 5)`-element mod-`162` fiber `{r0 + 162 * t | t < 3 ^ (w - 5)}` bijectively and
     uniformly onto `{base + (2 * 3 ^ (4 + parityWeight tail)) * q | q < 3 ^ (w - 5)}`!
  3. **Coupled Per-Cell Shift-Multiplicity & Dyadic-Window Occupancy Bounds (`∀ L_max, M`)**:
     For ANY two surviving leaves `y1, y2 ∈ dyadicWindowSurvivingQ0Leaves L_max M` realized by `u1, u2`
     in the same `(M, L, w)` cell (`u1.length = u2.length`, `parityWeight u1 = parityWeight u2`,
     `canonicalSuffixShift u1 1 ≤ canonicalSuffixShift u2 1`):
     - `canonicalSuffixShift u1 1 % 162 ∈ survivingMod162List ∧ canonicalSuffixShift u2 1 % 162 ∈ survivingMod162List`,
     - `canonicalSuffixShift u2 1 - canonicalSuffixShift u1 1 ≤ (u1.length - (M + parityWeight u1 + 1)) + 1`,
     - `(u1.length ≤ M + parityWeight u1 + 1 -> canonicalSuffixShift u2 1 = canonicalSuffixShift u1 1)`,
     - `(u1.length = M + parityWeight u1 + 2 -> canonicalSuffixShift u1 1 % 6 = 3 ->
         canonicalSuffixShift u2 1 = canonicalSuffixShift u1 1)`, AND
     - When `M ≥ 1`: `NoDupNat (dyadicWindowSurvivingQ0Leaves L_max M)`, `l2CollisionEnergy = length`,
       and `(dyadicWindowSurvivingQ0Leaves L_max M).length ≤ 2 ^ (M - 1)`!
-/
theorem dyadic_window_surviving_leaves_mod162_fiber_and_cell_occupancy :
    -- Part 1: Universal surviving-leaf unique first-hit decomposition & mod-`162` confinement:
    (∀ (L_max M y : Nat),
      y ∈ dyadicWindowSurvivingQ0Leaves L_max M ->
      ∃ u : List Bool,
        IsFirstHitOnePair u 0 ∧
        u.length ≤ L_max ∧
        exactBackwardQuotient 1 u 0 = y ∧
        IsSurvivingMod373248Class y ∧
        y ≥ 27 ∧
        2 ^ M ≤ y ∧ y < 2 ^ (M + 1) ∧
        parityWeight u ≥ 6 ∧
        u.length ≥ 8 ∧
        canonicalSuffixShift u 1 ≥ 3 ∧
        canonicalSuffixShift u 1 % 162 ∈ survivingMod162List ∧
        (∀ u' : List Bool,
          IsFirstHitOnePair u' 0 -> exactBackwardQuotient 1 u' 0 = y -> u' = u)) ∧
    -- Part 2: Mod-`162` (`j = 4`) multi-step `3 ^ (w - 5)` fiber equidistribution:
    (∀ (tail : List Bool) (w r0 : Nat),
      w ≥ 5 -> r0 < 162 ->
      let Mk := 2 * 3 ^ (4 + parityWeight tail)
      let N := 3 ^ (w - 5)
      let base := iterMarkovShift tail w r0 % Mk
      (∀ t : Nat, t < N ->
        ∃ q : Nat, q < N ∧ iterMarkovShift tail w (r0 + 162 * t) = base + Mk * q) ∧
      (∀ q : Nat, q < N ->
        ∃ t : Nat, t < N ∧
          iterMarkovShift tail w (r0 + 162 * t) = base + Mk * q ∧
          ∀ t' : Nat, t' < N ->
            iterMarkovShift tail w (r0 + 162 * t') = base + Mk * q -> t' = t)) ∧
    -- Part 3: Per-cell shift-multiplicity + sub-critical / first-layer pinning + occupancy bounds:
    ((∀ (L_max M : Nat) (u1 u2 : List Bool),
        IsFirstHitOnePair u1 0 -> IsFirstHitOnePair u2 0 ->
        exactBackwardQuotient 1 u1 0 ∈ dyadicWindowSurvivingQ0Leaves L_max M ->
        exactBackwardQuotient 1 u2 0 ∈ dyadicWindowSurvivingQ0Leaves L_max M ->
        u1.length = u2.length ->
        parityWeight u1 = parityWeight u2 ->
        canonicalSuffixShift u1 1 ≤ canonicalSuffixShift u2 1 ->
        canonicalSuffixShift u1 1 % 162 ∈ survivingMod162List ∧
        canonicalSuffixShift u2 1 % 162 ∈ survivingMod162List ∧
        canonicalSuffixShift u2 1 - canonicalSuffixShift u1 1 ≤
          (u1.length - (M + parityWeight u1 + 1)) + 1 ∧
        (u1.length ≤ M + parityWeight u1 + 1 ->
          canonicalSuffixShift u2 1 = canonicalSuffixShift u1 1) ∧
        (u1.length = M + parityWeight u1 + 2 ->
          canonicalSuffixShift u1 1 % 6 = 3 ->
          canonicalSuffixShift u2 1 = canonicalSuffixShift u1 1)) ∧
     (∀ (L_max M : Nat), M ≥ 1 ->
        let win := dyadicWindowSurvivingQ0Leaves L_max M
        NoDupNat win ∧
        (∀ n : Nat, countEqInList n win ≤ 1) ∧
        l2CollisionEnergy win = win.length ∧
        win.length ≤ 2 ^ (M - 1))) := by
  have hleaf : ∀ (L_max M y : Nat),
      y ∈ dyadicWindowSurvivingQ0Leaves L_max M ->
      ∃ u : List Bool,
        IsFirstHitOnePair u 0 ∧
        u.length ≤ L_max ∧
        exactBackwardQuotient 1 u 0 = y ∧
        IsSurvivingMod373248Class y ∧
        y ≥ 27 ∧
        2 ^ M ≤ y ∧ y < 2 ^ (M + 1) ∧
        parityWeight u ≥ 6 ∧
        u.length ≥ 8 ∧
        canonicalSuffixShift u 1 ≥ 3 ∧
        canonicalSuffixShift u 1 % 162 ∈ survivingMod162List ∧
        (∀ u' : List Bool,
          IsFirstHitOnePair u' 0 -> exactBackwardQuotient 1 u' 0 = y -> u' = u) := by
    intro L_max M y hy
    unfold dyadicWindowSurvivingQ0Leaves at hy
    rcases mem_filter_w10 _ (firstHitSurvivingQ0LeavesUpToLen L_max) y hy with ⟨hy_surv, hy_dec⟩
    rcases of_decide_eq_true hy_dec with ⟨hlo, hhi⟩
    rcases (multiscale_first_hit_surviving_q0_leaves_nodup L_max).2.2 y |>.mp hy_surv with
      ⟨u, hfh, hlen_max, hsurv_b, hy_eq⟩
    have hcls : IsSurvivingMod373248Class y := isSurvivingMod373248Bool_imp_class y hsurv_b
    have hy_ge27 : y ≥ 27 := survivingMod373248_ge_27 y hcls
    have hw_ge6 : parityWeight u ≥ 6 := by
      by_cases hle5 : parityWeight u ≤ 5
      · exact False.elim (one_generator_weight_le_five_never_surviving_mod373248 u 0 hfh.1 hle5 (hy_eq ▸ hcls))
      · omega
    have hlen_ge8 : u.length ≥ 8 := by
      by_cases hle7 : u.length ≤ 7
      · exact False.elim (one_generator_length_le_seven_never_surviving_mod373248 u 0 hfh.1 hle7 (hy_eq ▸ hcls))
      · omega
    have hsh_ge3 : canonicalSuffixShift u 1 ≥ 3 :=
      (first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.2 u hfh.1).mp hfh
    have hsh_162 : canonicalSuffixShift u 1 % 162 ∈ survivingMod162List :=
      markovShift_mod162_bijection_and_five_ones_81_lock.2.1 u hfh.1 (by omega)
    refine ⟨u, hfh, hlen_max, hy_eq, hcls, hy_ge27, hlo, hhi, hw_ge6, hlen_ge8, hsh_ge3, hsh_162, ?_⟩
    intro u' hfh' hy_eq'
    exact (first_hit_one_pair_sound_and_injective u' u 0 0 hfh' hfh).2.2.2 (hy_eq'.trans hy_eq.symm) |>.1
  refine ⟨hleaf, ?_, ⟨?_, dyadic_window_unique_shift_pinning_and_l2_energy.2.2.2⟩⟩
  · -- Part 2: Mod-`162` (`j = 4`) `3 ^ (w - 5)` fiber equidistribution:
    intro tail w r0 hw5 hr0
    have hm162 : (2 : Nat) * 3 ^ 4 = 162 := by decide
    have hw_sub : w - 1 - 4 = w - 5 := by omega
    have heq := markovShift_mod18_bijection_and_multistep_fiber_equidistribution.2.2
      tail 4 w r0 (by omega) (by rw [hm162]; exact hr0)
    dsimp only at heq ⊢
    rwa [hm162, hw_sub] at heq
  · -- Part 3: Per-cell shift-multiplicity, sub-critical uniqueness, & `E = 1` `3 mod 6` pinning:
    intro L_max M u1 u2 hfh1 hfh2 hm1 hm2 hL hw ha_le
    rcases hleaf L_max M (exactBackwardQuotient 1 u1 0) hm1 with
      ⟨w1_c, hfh1_c, _, heq1_c, _, _, hlo1, hhi1, _, _, _, h162_c1, huniq1⟩
    rcases hleaf L_max M (exactBackwardQuotient 1 u2 0) hm2 with
      ⟨w2_c, hfh2_c, _, heq2_c, _, _, hlo2, hhi2, _, _, _, h162_c2, huniq2⟩
    have hu1_eq : u1 = w1_c := huniq1 u1 hfh1 rfl
    have hu2_eq : u2 = w2_c := huniq2 u2 hfh2 rfl
    subst hu1_eq; subst hu2_eq
    rcases dyadic_window_supercritical_shift_multiplicity.1
      u1 u2 M hfh1.1 hfh2.1 hL hw ha_le hlo1 hhi1 hlo2 hhi2 with ⟨_, hspread⟩
    refine ⟨h162_c1, h162_c2, hspread, ?_, ?_⟩
    · intro hsub
      exact (dyadic_window_unique_shift_pinning_and_l2_energy.2.1
        u1 u2 M hfh1.1 hfh2.1 hL hw hsub hlo1 hhi1 hlo2 hhi2).symm
    · intro hL_sc hm6_3
      exact (dyadic_window_supercritical_shift_multiplicity.2.1
        u1 u2 M hfh1.1 hfh2.1 hL hw hL_sc ha_le hlo1 hhi1 hlo2 hhi2).2 hm6_3

end CollatzFormal
