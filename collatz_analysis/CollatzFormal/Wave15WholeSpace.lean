/-
  CollatzFormal/Wave15WholeSpace.lean
  Wave 15 Whole-Space Mathematical & CS Proof Loop (Synthesis — Fronts C & D):
  1. Front C (Branches P1.2 & P5.14):
     - Equal-Bitlength Single-Step Popcount Drop (`nOdd(s) = (8^s - 1) / 7 <- m(s) = (3 * nOdd(s) + 1) / 2`,
       `L = 3s - 2 = 3s - 2`, `P: 2s - 1 -> s`, `878 -> 585`) Closing ALL Popcount-Penalizing (`1 ≤ p_P < q_P`)
       Arbitrary-Base (`∀ p_L, q_L ≥ 1`, Including Super-Critical `B_L ≥ 2^(1/3)`) Joint `(binBitLength, binaryPopcount)`
       Preimage Weights & Complete 100% `(0, ∞)^2` All-Bases Two-Sided Joint `(binBitLength, binaryPopcount)`
       Exponential Impossibility (`∀ M_0 ≥ 3, ∀ p_L, q_L, p_P, q_P ≥ 1`),
     - Exact `binaryAltTransitions` Laws (`2^k - 1 -> 0`, `2^k -> 1`, `4^s + 1 -> (2 * 4^s + 1) / 3` Jump `2 -> 2s - 2`,
       & `(4^(3s + 2) - 1) / 3 -> (2 * 4^(3s + 2) - 5) / 9` Drop `6s + 2 -> 2s`) & Complete 100% `(0, ∞)^2` All-Bases
       Two-Sided Joint `(binBitLength, binaryAltTransitions)` Exponential Impossibility (`∀ M_0 ≥ 3, ∀ p_L, q_L, p_T, q_T ≥ 1`),
     - End-to-End Global Convergence (`k ≤ (x + 1)^3 + (x + 1)^5`), Genuine 10-Tier `ω^10` Syracuse Cascade
       (`Cone 13 -> Cone 12 -> ... -> Cone 5 -> Φ_diamond2`, `9895585985333 -> 927711186125` in `22` steps to `1`,
       `+16.22x` `Φ_2` jump), `mod 2^37` & `mod 2^39` Newton–Hensel Odd-Inverse & `Nat`/`Int`/`Q_(6)^+`
       Agreement + Choice-Free Non-Integer Rational Cone-13 Avoidance, `mod 63` Post-Climb Non-Reentry, & `[]`-Axiom `M1/M2/M3`
       Counter-Model Separation for the 12th Solvable `(3x + 1)`-Cousin `T_diamond12`.
  2. Front D (Branches P2.2 & P5.3):
     - Complete Mod-`13122` (`2 * 3^8`, `4374/13122` Surviving Classes on `w ≥ 9`) Markov Shift Bijection,
       Universal `9`-Ones `6561 mod 13122` & `[true, false] ++ 8`-Ones `10935 mod 13122` Locks, Exact `8 + 14 + 5 = 27`
       Surviving Mod-`512` Prefix-Weight-`9` Trichotomy (`8` weight-`≥ 8` prefixes force `w(u) ≥ 9` vs `14` weight-`7`
       escape witness), & `3^(w - 9)` (`j = 8`) Multi-Step Fiber Equidistribution,
     - Constructive Arbitrary-Degree `(d + 1)`-Zero-Run Family `uWinPoly d R M idx` Proving Unconditional
       Arbitrary-Degree Polynomial Surviving-Leaf Dyadic-Window Occupancy
       `(dyadicWindowSurvivingQ0Leaves L_max M).length ≥ R ^ d` at Linear Horizon `L_max ≥ M` (`C_0(d) = 0`)
       Across `∀ d ≥ 1, ∀ R ≥ 1`.

  Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

import CollatzFormal.Wave15WholeSpaceCore

namespace CollatzFormal

-- ============================================================================
-- SECTION 1: Front C Part 1 (Branch P1.2) — Complete 100% `(0, ∞)^2` Joint
--            `(binBitLength, binaryPopcount)` & `(binBitLength, binaryAltTransitions)`
--            Two-Sided Exponential Preimage Barriers (`W15_H3`)
-- ============================================================================

private theorem mul_pow_w15s (a b : Nat) : ∀ n : Nat, (a * b) ^ n = a ^ n * b ^ n
  | 0 => rfl
  | n + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, mul_pow_w15s a b n]
    ac_rfl

private theorem pow_mono_base_w15s (a b : Nat) (hle : a ≤ b) : ∀ n : Nat, a ^ n ≤ b ^ n
  | 0 => Nat.le_refl 1
  | n + 1 => Nat.mul_le_mul (pow_mono_base_w15s a b hle n) hle

private theorem id_lt_pow2_w15s : ∀ n : Nat, n < 2 ^ n
  | 0 => by decide
  | n + 1 => by
    have ih := id_lt_pow2_w15s n
    have hp := pow2_pos_nat n
    rw [Nat.pow_succ]
    omega

private theorem ite_true_dec_w15s {p : Prop} [inst : Decidable p] {α : Type} {a b : α} (hp : p) :
    (if p then a else b) = a := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hnp => exact False.elim (hnp hp)

private theorem ite_false_dec_w15s {p : Prop} [inst : Decidable p] {α : Type} {a b : α} (hnp : ¬ p) :
    (if p then a else b) = b := by
  cases inst with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

private theorem bernoulli_nat_mul_w15s (A : Nat) :
    ∀ n : Nat, A ^ (n + 1) + n * A ^ n ≤ A * (A + 1) ^ n
  | 0 => by simp
  | n + 1 => by
    have ih := bernoulli_nat_mul_w15s A n
    have hm := Nat.mul_le_mul_right (A + 1) ih
    rw [show (A * (A + 1) ^ n) * (A + 1) = A * (A + 1) ^ (n + 1) by
          rw [Nat.mul_assoc, ← Nat.pow_succ]] at hm
    have heq : (A ^ (n + 1) + n * A ^ n) * (A + 1) =
        (A ^ (n + 2) + (n + 1) * A ^ (n + 1)) + n * A ^ n := by
      rw [show n + 2 = (n + 1) + 1 from rfl, Nat.pow_succ A (n + 1),
          Nat.add_mul n 1 (A ^ (n + 1)), Nat.one_mul, Nat.pow_succ A n,
          Nat.add_mul (A ^ n * A) (n * A ^ n) (A + 1),
          Nat.mul_add (A ^ n * A) A 1, Nat.mul_one,
          Nat.mul_add (n * A ^ n) A 1, Nat.mul_one]
      ac_rfl
    exact Nat.le_trans (by rw [heq]; exact Nat.le_add_right _ _) hm

private theorem pow_gt_const_mul_pow_of_lt_w15s (A B K_0 : Nat) (hA : A ≥ 1) (hAB : A < B) :
    let k := K_0 * A
    K_0 * A ^ k < B ^ k := by
  dsimp only
  let k := K_0 * A
  have hbern := bernoulli_nat_mul_w15s A k
  have hb_mono : A * (A + 1) ^ k ≤ A * B ^ k :=
    Nat.mul_le_mul_left A (pow_mono_base_w15s (A + 1) B (by omega) k)
  have hle_AB : A ^ (k + 1) + k * A ^ k ≤ A * B ^ k := Nat.le_trans hbern hb_mono
  have hfac : A ^ (k + 1) + k * A ^ k = A * ((K_0 + 1) * A ^ k) := by
    dsimp only [k]
    rw [Nat.pow_succ A (K_0 * A), Nat.mul_comm (A ^ (K_0 * A)) A,
        Nat.add_mul K_0 1 (A ^ (K_0 * A)), Nat.one_mul, Nat.mul_add A]
    ac_rfl
  rw [hfac] at hle_AB
  have hle_B : (K_0 + 1) * A ^ k ≤ B ^ k :=
    nat_mul_le_cancel_left_w5 A _ _ (by omega) hle_AB
  have hAk_pos : A ^ k ≥ 1 := nat_pow_pos_of_pos A (by omega) k
  rw [Nat.add_mul K_0 1 (A ^ k), Nat.one_mul] at hle_B
  dsimp only [k] at hle_B hAk_pos ⊢
  omega

private theorem eventual_pure_bitlength_twosided_ratio_impossibility_w15
    (M_0 : Nat) (hM0 : M_0 ≥ 3)
    (wNum wDen : Nat -> Nat) (c_0 C_hi p_L q_L pTheta qTheta : Nat)
    (hc0 : c_0 ≥ 1) (hpL : p_L ≥ 1) (hqL : q_L ≥ 1)
    (hsand : ∀ n : Nat, n ≥ M_0 ->
      c_0 * q_L ^ binBitLength n * wDen n ≤ p_L ^ binBitLength n * wNum n ∧
      p_L ^ binBitLength n * wNum n ≤ C_hi * q_L ^ binBitLength n * wDen n) :
    ¬ IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta := by
  intro hw
  have hq_pos : qTheta > 0 := Nat.lt_of_lt_of_le hw.1 hw.2.1
  rcases eventual_equal_order_exp_ratio_all_bases_impossibility.1.2.1 q_L 1 p_L 1 hqL (by decide) hpL (by decide) with
    hsub | hsup
  · simp only [Nat.mul_one, Nat.one_mul] at hsub
    have hcMod9_bd : ∀ z : Nat, 1 ≤ cMod9 z ∧ cMod9 z ≤ 4 := by
      intro z; unfold cMod9
      have hr : z % 9 < 9 := Nat.mod_lt z (by decide)
      rcases (by omega :
        z % 9 = 0 ∨ z % 9 = 1 ∨ z % 9 = 2 ∨ z % 9 = 3 ∨ z % 9 = 4 ∨
        z % 9 = 5 ∨ z % 9 = 6 ∨ z % 9 = 7 ∨ z % 9 = 8) with
        h | h | h | h | h | h | h | h | h <;> simp [h]
    have hstep1 : ∀ z : Nat, z ≥ 2 * M_0 -> z % 3 ≠ 0 ->
        let z' := cubeRootTwoBranchNext wNum wDen z
        z < z' ∧ z' % 3 ≠ 0 ∧ cMod9 z' * z' ≤ 8 * (cMod9 z * z) ∧
        2 * wNum z' * wDen z ≤ wNum z * wDen z' := by
      intro z hz_2M0 hz3; dsimp only
      have hpot := eventual_exp_bitlength_cube_root_two_impossibility.1.1 wNum wDen z (by omega) hz3
      let r := optShiftMod9 z
      have hr_bd : 1 ≤ r ∧ r ≤ 4 ∧ (2 ^ r * z) % 3 = 2 := by
        dsimp [r]; unfold optShiftMod9
        have hr9 : z % 9 < 9 := Nat.mod_lt z (by decide)
        rcases (by omega : z % 9 = 1 ∨ z % 9 = 2 ∨ z % 9 = 4 ∨ z % 9 = 5 ∨ z % 9 = 7 ∨ z % 9 = 8) with
          h | h | h | h | h | h <;> (simp only [h]; omega)
      let m := 2 ^ r * z
      let y0 := 2 * m
      let y1 := (2 * m - 1) / 3
      have hm_ge2z : m ≥ 2 * z := Nat.mul_le_mul_right z (by simpa using pow2_mono_nat hr_bd.1)
      have hy0_3 : y0 % 3 ≠ 0 := by dsimp [y0]; have := hr_bd.2.2; omega
      have hy1_3 : y1 % 3 ≠ 0 := by
        dsimp [y1, m, r]; unfold optShiftMod9
        have hr9 : z % 9 < 9 := Nat.mod_lt z (by decide)
        rcases (by omega : z % 9 = 1 ∨ z % 9 = 2 ∨ z % 9 = 4 ∨ z % 9 = 5 ∨ z % 9 = 7 ∨ z % 9 = 8) with
          h | h | h | h | h | h <;> simp only [h]
        · rw [show 2 * (2 ^ 1 * z) = 4 * z by omega]; omega
        · rw [show 2 * (2 ^ 2 * z) = 8 * z by omega]; omega
        · rw [show 2 * (2 ^ 1 * z) = 4 * z by omega]; omega
        · rw [show 2 * (2 ^ 2 * z) = 8 * z by omega]; omega
        · rw [show 2 * (2 ^ 3 * z) = 16 * z by omega]; omega
        · rw [show 2 * (2 ^ 4 * z) = 32 * z by omega]; omega
      have heven_st : ∀ u : Nat, u ≥ 2 * M_0 -> wNum (2 * u) * wDen u ≤ wNum u * wDen (2 * u) := by
        intro u hu
        if hu2 : u % 3 = 2 then
          let nO := (2 * u - 1) / 3
          have hdn_pos : wDen nO > 0 := (hw.2.2.1 nO (by dsimp [nO]; omega)).2
          have hpre_u := hw.2.2.2.2 u (by omega) hu2
          dsimp only at hpre_u
          have hbr_u : (wNum (2 * u) * wDen nO + wNum nO * wDen (2 * u)) * wDen u ≤
              wNum u * (wDen (2 * u) * wDen nO) :=
            nat_mul_le_cancel_left_w5 qTheta _ _ hq_pos
              (Nat.le_trans hpre_u (Nat.mul_le_mul_right _ hw.2.1))
          exact nat_mul_le_cancel_right_w5 (wDen nO) _ _ hdn_pos (by
            rw [show (wNum (2 * u) * wDen u) * wDen nO = (wNum (2 * u) * wDen nO) * wDen u by ac_rfl,
                show (wNum u * wDen (2 * u)) * wDen nO = wNum u * (wDen (2 * u) * wDen nO) by ac_rfl]
            rw [Nat.add_mul] at hbr_u; omega)
        else
          exact nat_mul_le_cancel_left_w5 qTheta _ _ hq_pos
            (Nat.le_trans (hw.2.2.2.1 u (by omega) hu2) (Nat.mul_le_mul_right _ hw.2.1))
      have hpow2_le : ∀ d : Nat, wNum (2 ^ d * z) * wDen z ≤ wNum z * wDen (2 ^ d * z) := by
        intro d; induction d with
        | zero => simp
        | succ d' ih =>
          have hzd : 2 ^ d' * z ≥ 2 * M_0 := by
            have := Nat.mul_le_mul (pow2_pos_nat d') hz_2M0; omega
          rw [Nat.pow_succ, Nat.mul_comm (2 ^ d') 2, Nat.mul_assoc]
          exact rat_le_trans_pos_w5 _ _ (wNum (2 ^ d' * z)) (wDen (2 ^ d' * z)) _ _
            (hw.2.2.1 (2 ^ d' * z) (by omega)).2 (heven_st (2 ^ d' * z) hzd) ih
      have hm_le_z := hpow2_le r
      have hpre := hw.2.2.2.2 m (by omega) hr_bd.2.2
      dsimp only at hpre
      have hbr : (wNum y0 * wDen y1 + wNum y1 * wDen y0) * wDen m ≤ wNum m * (wDen y0 * wDen y1) :=
        nat_mul_le_cancel_left_w5 qTheta _ _ hq_pos (Nat.le_trans hpre (Nat.mul_le_mul_right _ hw.2.1))
      have hbm_pos : wDen m > 0 := (hw.2.2.1 m (by omega)).2
      have hb0_pos : wDen y0 > 0 := (hw.2.2.1 y0 (by dsimp [y0]; omega)).2
      have hb1_pos : wDen y1 > 0 := (hw.2.2.1 y1 (by dsimp [y1]; omega)).2
      refine ⟨?_, ?_, hpot, ?_⟩
      · unfold cubeRootTwoBranchNext; dsimp only
        if hc : 2 * wNum y0 * wDen m ≤ wNum m * wDen y0 then
          change z < (if 2 * wNum y0 * wDen m ≤ wNum m * wDen y0 then y0 else y1)
          rw [ite_true_dec_w15s hc]; dsimp [y0]; omega
        else
          change z < (if 2 * wNum y0 * wDen m ≤ wNum m * wDen y0 then y0 else y1)
          rw [ite_false_dec_w15s hc]; dsimp [y1]; omega
      · unfold cubeRootTwoBranchNext; dsimp only
        if hc : 2 * wNum y0 * wDen m ≤ wNum m * wDen y0 then
          change (if 2 * wNum y0 * wDen m ≤ wNum m * wDen y0 then y0 else y1) % 3 ≠ 0
          rw [ite_true_dec_w15s hc]; exact hy0_3
        else
          change (if 2 * wNum y0 * wDen m ≤ wNum m * wDen y0 then y0 else y1) % 3 ≠ 0
          rw [ite_false_dec_w15s hc]; exact hy1_3
      · unfold cubeRootTwoBranchNext; dsimp only
        change 2 * wNum (if 2 * wNum y0 * wDen m ≤ wNum m * wDen y0 then y0 else y1) * wDen z ≤
          wNum z * wDen (if 2 * wNum y0 * wDen m ≤ wNum m * wDen y0 then y0 else y1)
        if hc : 2 * wNum y0 * wDen m ≤ wNum m * wDen y0 then
          rw [ite_true_dec_w15s hc]
          exact rat_le_trans_pos_w5 _ _ _ _ _ _ hbm_pos hc hm_le_z
        else
          rw [ite_false_dec_w15s hc]
          have hc1 : 2 * wNum y1 * wDen m ≤ wNum m * wDen y1 := by
            if hc' : 2 * wNum y1 * wDen m ≤ wNum m * wDen y1 then exact hc'
            else
              exfalso
              have hm0 := Nat.mul_lt_mul_of_pos_right (by omega : wNum m * wDen y0 < 2 * wNum y0 * wDen m) hb1_pos
              have hm1 := Nat.mul_lt_mul_of_pos_right (by omega : wNum m * wDen y1 < 2 * wNum y1 * wDen m) hb0_pos
              rw [show (wNum m * wDen y0) * wDen y1 = wNum m * (wDen y0 * wDen y1) by ac_rfl,
                  show (2 * wNum y0 * wDen m) * wDen y1 = 2 * ((wNum y0 * wDen y1) * wDen m) by ac_rfl] at hm0
              rw [show (wNum m * wDen y1) * wDen y0 = wNum m * (wDen y0 * wDen y1) by ac_rfl,
                  show (2 * wNum y1 * wDen m) * wDen y0 = 2 * ((wNum y1 * wDen y0) * wDen m) by ac_rfl] at hm1
              rw [Nat.add_mul] at hbr; omega
          exact rat_le_trans_pos_w5 _ _ _ _ _ _ hbm_pos hc1 hm_le_z
    let x0 := 6 * M_0 + 5
    have hx0_2M0 : x0 ≥ 2 * M_0 := by dsimp [x0]; omega
    have hx0_3 : x0 % 3 ≠ 0 := by dsimp [x0]; omega
    have hiter : ∀ (k z : Nat), z ≥ 2 * M_0 -> z % 3 ≠ 0 ->
        let zk := cubeRootTwoBranchIter wNum wDen k z
        zk ≥ z ∧ zk % 3 ≠ 0 ∧ cMod9 zk * zk ≤ 8 ^ k * (cMod9 z * z) ∧
        2 ^ k * wNum zk * wDen z ≤ wNum z * wDen zk := by
      intro k; induction k with
      | zero => intro z _ hz3; simp [cubeRootTwoBranchIter, hz3]
      | succ k' ih =>
        intro z hz hz3
        rcases hstep1 z hz hz3 with ⟨hlt1, hz1_3, hpot1, hrat1⟩
        let z1 := cubeRootTwoBranchNext wNum wDen z
        rcases ih z1 (by dsimp [z1]; omega) hz1_3 with ⟨hge_k, hzk_3, hpot_k, hrat_k⟩
        let zk := cubeRootTwoBranchIter wNum wDen k' z1
        have hdz1_pos : wDen z1 > 0 := (hw.2.2.1 z1 (by dsimp [z1]; omega)).2
        refine ⟨Nat.le_trans (Nat.le_of_lt hlt1) hge_k, hzk_3, ?_, ?_⟩
        · calc cMod9 zk * zk ≤ 8 ^ k' * (cMod9 z1 * z1) := hpot_k
            _ ≤ 8 ^ k' * (8 * (cMod9 z * z)) := Nat.mul_le_mul_left _ hpot1
            _ = 8 ^ (k' + 1) * (cMod9 z * z) := by rw [Nat.pow_succ]; ac_rfl
        · exact nat_mul_le_cancel_right_w5 (wDen z1) _ _ hdz1_pos (by
            calc (2 ^ (k' + 1) * wNum zk * wDen z) * wDen z1
                = (2 * wDen z) * (2 ^ k' * wNum zk * wDen z1) := by rw [Nat.pow_succ]; ac_rfl
              _ ≤ (2 * wDen z) * (wNum z1 * wDen zk) := Nat.mul_le_mul_left _ hrat_k
              _ = wDen zk * (2 * wNum z1 * wDen z) := by ac_rfl
              _ ≤ wDen zk * (wNum z * wDen z1) := Nat.mul_le_mul_left _ hrat1
              _ = (wNum z * wDen zk) * wDen z1 := by ac_rfl)
    have hstep_canc : ∀ k : Nat,
        let xk := cubeRootTwoBranchIter wNum wDen k x0
        let Lk := binBitLength xk
        Lk ≤ 3 * k + (3 + x0) ∧ 2 ^ k * q_L ^ Lk ≤ wNum x0 * p_L ^ Lk := by
      intro k; dsimp only
      rcases hiter k x0 hx0_2M0 hx0_3 with ⟨hxk_ge, _, hpot_k, hrat_k⟩
      let xk := cubeRootTwoBranchIter wNum wDen k x0
      let Lk := binBitLength xk
      have hxk_M0 : xk ≥ M_0 := by dsimp [xk]; omega
      have hbl_k : Lk ≤ 3 * k + (3 + x0) := by
        have hc1 : 1 * xk ≤ cMod9 xk * xk := Nat.mul_le_mul_right xk (hcMod9_bd xk).1
        rw [Nat.one_mul] at hc1
        have hc0_lt : cMod9 x0 * x0 < 2 ^ (2 + x0) := by
          have h1 : cMod9 x0 * x0 ≤ 4 * x0 := Nat.mul_le_mul_right x0 (hcMod9_bd x0).2
          have h2 : 4 * x0 < 4 * 2 ^ x0 := Nat.mul_lt_mul_of_pos_left (id_lt_pow2_w15s x0) (by decide)
          rw [show 4 * 2 ^ x0 = 2 ^ (2 + x0) by rw [Nat.pow_add 2 2 x0]] at h2
          exact Nat.lt_of_le_of_lt h1 h2
        have h8k : 8 ^ k = 2 ^ (3 * k) := by rw [show (8 : Nat) = 2 ^ 3 from rfl, pow_pow_eq_mul_w5 2 3 k]
        have hxk_lt : xk < 2 ^ (3 * k + (2 + x0)) := by
          have hm := Nat.mul_lt_mul_of_pos_left hc0_lt (pow2_pos_nat (3 * k))
          rw [← h8k] at hm
          have hlt := Nat.lt_of_le_of_lt (Nat.le_trans hc1 hpot_k) hm
          rwa [h8k, ← Nat.pow_add 2 (3 * k) (2 + x0)] at hlt
        have hle := binBitLength_mono xk (2 ^ ((3 * k + 1 + x0) + 1) - 1)
          (by rw [show (3 * k + 1 + x0) + 1 = 3 * k + (2 + x0) by omega]; omega)
        rw [(binBitLength_pow2_and_pred (3 * k + 1 + x0)).2] at hle
        dsimp [Lk]; omega
      have hwn_pos : wNum xk > 0 := (hw.2.2.1 xk hxk_M0).1
      have hwd0_pos : wDen x0 ≥ 1 := (hw.2.2.1 x0 (by omega)).2
      have hlo := (hsand xk hxk_M0).1
      change c_0 * q_L ^ Lk * wDen xk ≤ p_L ^ Lk * wNum xk at hlo
      have hc0_wd0 : 1 ≤ c_0 * wDen x0 := Nat.mul_le_mul hc0 hwd0_pos
      have hm_comb : (2 ^ k * q_L ^ Lk) * wNum xk ≤ (wNum x0 * p_L ^ Lk) * wNum xk := by
        calc (2 ^ k * q_L ^ Lk) * wNum xk
            = 1 * ((2 ^ k * q_L ^ Lk) * wNum xk) := (Nat.one_mul _).symm
          _ ≤ (c_0 * wDen x0) * ((2 ^ k * q_L ^ Lk) * wNum xk) := Nat.mul_le_mul_right _ hc0_wd0
          _ = c_0 * q_L ^ Lk * (2 ^ k * wNum xk * wDen x0) := by ac_rfl
          _ ≤ c_0 * q_L ^ Lk * (wNum x0 * wDen xk) := Nat.mul_le_mul_left _ hrat_k
          _ = wNum x0 * (c_0 * q_L ^ Lk * wDen xk) := by ac_rfl
          _ ≤ wNum x0 * (p_L ^ Lk * wNum xk) := Nat.mul_le_mul_left _ hlo
          _ = (wNum x0 * p_L ^ Lk) * wNum xk := by ac_rfl
      exact ⟨hbl_k, nat_mul_le_cancel_right_w5 (wNum xk) _ _ hwn_pos hm_comb⟩
    if hpq : p_L ≤ q_L then
      let k := wNum x0 + 1
      rcases hstep_canc k with ⟨_, hineq⟩
      let Lk := binBitLength (cubeRootTwoBranchIter wNum wDen k x0)
      change 2 ^ k * q_L ^ Lk ≤ wNum x0 * p_L ^ Lk at hineq
      have h2 := Nat.le_trans hineq (Nat.mul_le_mul_left _ (pow_mono_base_w15s p_L q_L hpq Lk))
      have h2k_le := nat_mul_le_cancel_right_w5 (q_L ^ Lk) _ _ (nat_pow_pos_of_pos q_L hqL Lk) h2
      have hgt := id_lt_pow2_w15s k
      dsimp [k] at h2k_le hgt; omega
    else
      have hqp : q_L ≤ p_L := by omega
      let E0 := 3 + x0
      let K_0 := wNum x0 * p_L ^ E0 + 1
      let k := K_0 * p_L ^ 3
      rcases hstep_canc k with ⟨hLk_le, hineq⟩
      let Lk := binBitLength (cubeRootTwoBranchIter wNum wDen k x0)
      change Lk ≤ 3 * k + E0 at hLk_le
      change 2 ^ k * q_L ^ Lk ≤ wNum x0 * p_L ^ Lk at hineq
      let D_ex := (3 * k + E0) - Lk
      have hsp : Lk + D_ex = 3 * k + E0 := by dsimp [D_ex]; omega
      have hup : 2 ^ k * q_L ^ (3 * k + E0) ≤ (wNum x0 * p_L ^ E0) * (p_L ^ 3) ^ k := by
        calc 2 ^ k * q_L ^ (3 * k + E0)
            = (2 ^ k * q_L ^ Lk) * q_L ^ D_ex := by rw [← hsp, Nat.pow_add q_L Lk D_ex]; ac_rfl
          _ ≤ (wNum x0 * p_L ^ Lk) * p_L ^ D_ex := Nat.mul_le_mul hineq (pow_mono_base_w15s q_L p_L hqp D_ex)
          _ = wNum x0 * p_L ^ (3 * k + E0) := by rw [Nat.mul_assoc, ← Nat.pow_add, hsp]
          _ = (wNum x0 * p_L ^ E0) * (p_L ^ 3) ^ k := by
                rw [Nat.pow_add p_L (3 * k) E0, ← pow_pow_eq_mul_w5 p_L 3 k]; ac_rfl
      rw [show 2 ^ k * q_L ^ (3 * k + E0) = q_L ^ E0 * (2 * q_L ^ 3) ^ k by
            rw [Nat.pow_add q_L (3 * k) E0, ← pow_pow_eq_mul_w5 q_L 3 k, mul_pow_w15s 2 (q_L ^ 3) k]; ac_rfl] at hup
      have h1 : 1 * (2 * q_L ^ 3) ^ k ≤ q_L ^ E0 * (2 * q_L ^ 3) ^ k :=
        Nat.mul_le_mul_right _ (nat_pow_pos_of_pos q_L hqL E0)
      rw [Nat.one_mul] at h1
      have hle_pow : (2 * q_L ^ 3) ^ k ≤ K_0 * (p_L ^ 3) ^ k :=
        Nat.le_trans (Nat.le_trans h1 hup) (Nat.mul_le_mul_right _ (by dsimp [K_0]; omega))
      have hgt_pow := pow_gt_const_mul_pow_of_lt_w15s (p_L ^ 3) (2 * q_L ^ 3) K_0
        (nat_pow_pos_of_pos p_L hpL 3) hsub
      dsimp only [k] at hle_pow hgt_pow; omega
  · simp only [Nat.mul_one, Nat.one_mul] at hsup
    -- Super-unit arm (`q_L < p_L`) along `revSyracuseNode (2 * s)`:
    rcases eventual_poly_num_any_exp_base_bitlength_impossibility.1 with ⟨hchain, hbits⟩
    let C_tot := C_hi + M_0 + 1
    let s := C_tot * q_L
    have hs1 : s ≥ 1 := by
      dsimp [s, C_tot]; simpa using Nat.mul_le_mul (by omega : 1 ≤ C_hi + M_0 + 1) hqL
    let m := 2 * s
    have hnode_ge : ∀ t : Nat, t ≤ 2 * m -> revSyracuseNode m t ≥ M_0 := by
      intro t ht; unfold revSyracuseNode
      have h1 : 2 ^ (t + 1) * 3 ^ (2 * m - t) ≥ 2 ^ (t + 1) * 2 ^ (2 * m - t) :=
        Nat.mul_le_mul_left _ (pow2_le_pow3 _)
      rw [← Nat.pow_add, show (t + 1) + (2 * m - t) = 2 * m + 1 by omega] at h1
      have h2 := id_lt_pow2_w15s (2 * m + 1)
      have hs_M0 : s ≥ M_0 := by
        have hm1 : C_tot * 1 ≤ C_tot * q_L := Nat.mul_le_mul_left C_tot hqL
        dsimp [s, C_tot] at hm1 ⊢; omega
      dsimp [m] at h1 h2 ⊢; omega
    have hstep_rs : ∀ t : Nat, t < 2 * m ->
        wNum (revSyracuseNode m (t + 1)) * wDen (revSyracuseNode m t) ≤
          wNum (revSyracuseNode m t) * wDen (revSyracuseNode m (t + 1)) := by
      intro t ht
      let xt := revSyracuseNode m t
      let xn := revSyracuseNode m (t + 1)
      rcases (hchain m).2.2 t ht with ⟨hxt_m3, hnOdd_eq⟩
      have hpre := hw.2.2.2.2 xt (hnode_ge t (Nat.le_of_lt ht)) hxt_m3
      dsimp only at hpre; rw [hnOdd_eq] at hpre
      have hbr : (wNum (2 * xt) * wDen xn + wNum xn * wDen (2 * xt)) * wDen xt ≤
          wNum xt * (wDen (2 * xt) * wDen xn) :=
        nat_mul_le_cancel_left_w5 qTheta _ _ hq_pos (Nat.le_trans hpre (Nat.mul_le_mul_right _ hw.2.1))
      exact nat_mul_le_cancel_right_w5 (wDen (2 * xt)) _ _ (hw.2.2.1 (2 * xt) (by have := hnode_ge t (Nat.le_of_lt ht); omega)).2 (by
        rw [show (wNum xn * wDen xt) * wDen (2 * xt) = (wNum xn * wDen (2 * xt)) * wDen xt by ac_rfl,
            show (wNum xt * wDen xn) * wDen (2 * xt) = wNum xt * (wDen (2 * xt) * wDen xn) by ac_rfl]
        rw [Nat.add_mul] at hbr; omega)
    have htele : ∀ r : Nat, r ≤ 2 * m ->
        wNum (revSyracuseNode m r) * wDen (revSyracuseNode m 0) ≤
          wNum (revSyracuseNode m 0) * wDen (revSyracuseNode m r) := by
      intro r hr; induction r with
      | zero => exact Nat.le_refl _
      | succ r' ih =>
        exact rat_le_trans_pos_w5 _ _ (wNum (revSyracuseNode m r')) (wDen (revSyracuseNode m r')) _ _
          (hw.2.2.1 _ (hnode_ge r' (Nat.le_of_lt hr))).2 (hstep_rs r' hr) (ih (Nat.le_of_lt hr))
    let x0 := revSyracuseNode m 0
    let xe := revSyracuseNode m (2 * m)
    have hrat_end := htele (2 * m) (Nat.le_refl _)
    rcases hbits s hs1 with ⟨hbl_end, hbl_lo0, _⟩
    rw [show revSyracuseNode (2 * s) (4 * s) = xe by dsimp [xe, m]; rw [show 2 * (2 * s) = 4 * s by omega]] at hbl_end
    let L0 := binBitLength x0
    let Le := binBitLength xe
    let D_L := L0 - Le
    have hDL_ge : s ≤ D_L := by
      change Le = 4 * s + 1 at hbl_end; change 6 * s + 2 ≤ L0 at hbl_lo0; dsimp [D_L]; omega
    have hL0_sp : Le + D_L = L0 := by dsimp [D_L]; omega
    have hlo_e := (hsand xe (hnode_ge (2 * m) (Nat.le_refl _))).1
    have hhi_0 := (hsand x0 (hnode_ge 0 (Nat.zero_le _))).2
    change c_0 * q_L ^ Le * wDen xe ≤ p_L ^ Le * wNum xe at hlo_e
    change p_L ^ L0 * wNum x0 ≤ C_hi * q_L ^ L0 * wDen x0 at hhi_0
    let F_c := (q_L ^ Le * p_L ^ Le) * (wDen x0 * wDen xe)
    have hF_pos : F_c > 0 := Nat.mul_le_mul
      (Nat.mul_le_mul (nat_pow_pos_of_pos q_L hqL Le) (nat_pow_pos_of_pos p_L hpL Le))
      (Nat.mul_le_mul (hw.2.2.1 x0 (hnode_ge 0 (Nat.zero_le _))).2
                      (hw.2.2.1 xe (hnode_ge (2 * m) (Nat.le_refl _))).2)
    have hcomb : F_c * (c_0 * p_L ^ D_L) ≤ F_c * (C_hi * q_L ^ D_L) := by
      have hl : F_c * (c_0 * p_L ^ D_L) = (p_L ^ L0 * wDen x0) * (c_0 * q_L ^ Le * wDen xe) := by
        dsimp [F_c]; rw [← hL0_sp, Nat.pow_add p_L Le D_L]; ac_rfl
      have hr : F_c * (C_hi * q_L ^ D_L) = (p_L ^ Le * wDen xe) * (C_hi * q_L ^ L0 * wDen x0) := by
        dsimp [F_c]; rw [← hL0_sp, Nat.pow_add q_L Le D_L]; ac_rfl
      rw [hl, hr]
      calc (p_L ^ L0 * wDen x0) * (c_0 * q_L ^ Le * wDen xe)
          ≤ (p_L ^ L0 * wDen x0) * (p_L ^ Le * wNum xe) := Nat.mul_le_mul_left _ hlo_e
        _ = (p_L ^ Le * p_L ^ L0) * (wNum xe * wDen x0) := by ac_rfl
        _ ≤ (p_L ^ Le * p_L ^ L0) * (wNum x0 * wDen xe) := Nat.mul_le_mul_left _ hrat_end
        _ = (p_L ^ Le * wDen xe) * (p_L ^ L0 * wNum x0) := by ac_rfl
        _ ≤ (p_L ^ Le * wDen xe) * (C_hi * q_L ^ L0 * wDen x0) := Nat.mul_le_mul_left _ hhi_0
    have hDL_ineq : p_L ^ D_L ≤ C_tot * q_L ^ D_L := by
      have hc := nat_mul_le_cancel_left_w5 F_c _ _ hF_pos hcomb
      have h1 : 1 * p_L ^ D_L ≤ c_0 * p_L ^ D_L := Nat.mul_le_mul_right _ hc0
      rw [Nat.one_mul] at h1
      exact Nat.le_trans (Nat.le_trans h1 hc) (Nat.mul_le_mul_right _ (by dsimp [C_tot]; omega))
    let E_ex := D_L - s
    have hs_sp : s + E_ex = D_L := by dsimp [E_ex]; omega
    have hs_ineq : p_L ^ s ≤ C_tot * q_L ^ s := by
      have hm1 : q_L ^ E_ex * p_L ^ s ≤ q_L ^ E_ex * (C_tot * q_L ^ s) := by
        calc q_L ^ E_ex * p_L ^ s
            ≤ p_L ^ E_ex * p_L ^ s := Nat.mul_le_mul_right _ (pow_mono_base_w15s q_L p_L (Nat.le_of_lt hsup) E_ex)
          _ = p_L ^ D_L := by rw [← hs_sp, Nat.pow_add p_L s E_ex, Nat.mul_comm]
          _ ≤ C_tot * q_L ^ D_L := hDL_ineq
          _ = q_L ^ E_ex * (C_tot * q_L ^ s) := by rw [← hs_sp, Nat.pow_add q_L s E_ex]; ac_rfl
      exact nat_mul_le_cancel_left_w5 (q_L ^ E_ex) _ _ (nat_pow_pos_of_pos q_L hqL E_ex) hm1
    have hgt := pow_gt_const_mul_pow_of_lt_w15s q_L p_L C_tot hqL hsup
    dsimp only [s] at hs_ineq hgt; omega

-- ----------------------------------------------------------------------------
-- Section 1A: Equal-Bitlength Popcount Drop (`(8^s - 1)/7 <- (3*nOdd + 1)/2`) &
--             Complete 100% `(0, ∞)^2` Joint `(binBitLength, binaryPopcount)`
--             Two-Sided Exponential Impossibility (`W15_H3`)
-- ----------------------------------------------------------------------------

private theorem binPopcount_double_w15 : ∀ n : Nat,
    binPopcount (2 * n) = binPopcount n
  | 0 => rfl
  | n + 1 => by
    rw [binPopcount_step_pos (2 * (n + 1)) (by omega), Nat.mul_mod_right, Nat.zero_add,
        Nat.mul_div_right (n + 1) (by decide : 0 < 2)]

private theorem binPopcount_double_add_one_w15 (n : Nat) :
    binPopcount (2 * n + 1) = binPopcount n + 1 := by
  rw [binPopcount_step_pos (2 * n + 1) (by omega)]
  have hm : (2 * n + 1) % 2 = 1 := by omega
  have hd : (2 * n + 1) / 2 = n := by omega
  rw [hm, hd]; omega

private theorem equal_bitlength_popcount_drop_family :
    ∀ s : Nat, s ≥ 2 ->
      let nOdd := (8 ^ s - 1) / 7
      let m := (3 * nOdd + 1) / 2
      m % 3 = 2 ∧
      (2 * m - 1) / 3 = nOdd ∧
      binBitLength m = 3 * s - 2 ∧
      binBitLength nOdd = 3 * s - 2 ∧
      binaryPopcount m = 2 * s - 1 ∧
      binaryPopcount nOdd = s := by
  have hm7 : ∀ k : Nat, 8 ^ k % 7 = 1 := by
    intro k; induction k with
    | zero => rfl
    | succ k' ih => rw [Nat.pow_succ, Nat.mul_mod, ih]
  have hrec_n : ∀ k : Nat, (8 ^ (k + 1) - 1) / 7 = 8 * ((8 ^ k - 1) / 7) + 1 := by
    intro k
    have h7 := hm7 k
    have hp := nat_pow_pos_of_pos 8 (by decide) k
    rw [Nat.pow_succ 8 k]; omega
  have hpop_n : ∀ k : Nat, binPopcount ((8 ^ k - 1) / 7) = k := by
    intro k; induction k with
    | zero => rfl
    | succ k' ih =>
      rw [hrec_n k', show 8 * ((8 ^ k' - 1) / 7) + 1 = 2 * (2 * (2 * ((8 ^ k' - 1) / 7))) + 1 by omega,
          binPopcount_double_add_one_w15, binPopcount_double_w15, binPopcount_double_w15, ih]
  have hn_mod4 : ∀ k : Nat, k ≥ 1 -> ((8 ^ k - 1) / 7) % 4 = 1 := by
    intro k hk; cases k with
    | zero => omega
    | succ k' =>
      cases k' with
      | zero => rfl
      | succ k'' => rw [hrec_n (k'' + 1)]; omega
  have hpop_u : ∀ k : Nat, k ≥ 1 ->
      binPopcount ((3 * ((8 ^ k - 1) / 7) + 1) / 4) = 2 * k - 1 := by
    intro k hk; induction k with
    | zero => omega
    | succ k' ih =>
      cases k' with
      | zero => decide
      | succ k'' =>
        let n0 := (8 ^ (k'' + 1) - 1) / 7
        have hm4 := hn_mod4 (k'' + 1) (by omega)
        change (n0 % 4 = 1) at hm4
        let u0 := (3 * n0 + 1) / 4
        have hu0_eq : 4 * u0 = 3 * n0 + 1 := by dsimp [u0]; omega
        have hu1_eq : (3 * ((8 ^ (k'' + 2) - 1) / 7) + 1) / 4 = 8 * u0 - 1 := by
          rw [hrec_n (k'' + 1)]; change (3 * (8 * n0 + 1) + 1) / 4 = 8 * u0 - 1; omega
        have hu0_odd : u0 % 2 = 1 := by
          have hn0_8 : n0 % 8 = 1 := by
            dsimp [n0]; rw [hrec_n k'']; omega
          omega
        let q := u0 / 2
        have hu0_sp : u0 = 2 * q + 1 := by dsimp [q]; omega
        have h8u : 8 * u0 - 1 = 2 * (2 * (2 * (2 * q) + 1) + 1) + 1 := by rw [hu0_sp]; omega
        have hp_u0 : binPopcount u0 = binPopcount q + 1 := by
          rw [hu0_sp, binPopcount_double_add_one_w15]
        have hp_ih := ih (by omega)
        change binPopcount u0 = 2 * (k'' + 1) - 1 at hp_ih
        rw [hu1_eq, h8u, binPopcount_double_add_one_w15, binPopcount_double_add_one_w15,
            binPopcount_double_add_one_w15, binPopcount_double_w15]
        omega
  intro s hs2; dsimp only
  let nOdd := (8 ^ s - 1) / 7
  let m := (3 * nOdd + 1) / 2
  have hm4_n : nOdd % 4 = 1 := hn_mod4 s (by omega)
  let u := (3 * nOdd + 1) / 4
  have hm_2u : m = 2 * u := by dsimp [m, u]; omega
  have h2m_eq : 2 * m = 3 * nOdd + 1 := by dsimp [m]; omega
  have h8_pow2 : 8 ^ s = 8 * 2 ^ (3 * s - 3) := by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, pow_pow_eq_mul_w5 2 3 s]
    conv => lhs; rw [show 3 * s = 3 + (3 * s - 3) by omega, Nat.pow_add]
  have hp_ge8 : 2 ^ (3 * s - 3) ≥ 8 := by
    have hc : (2 : Nat) ^ 3 = 8 := rfl
    rw [← hc]; exact pow2_mono_nat (by omega)
  have h7n : 7 * nOdd + 1 = 8 * 2 ^ (3 * s - 3) := by
    dsimp [nOdd]; have h7 := hm7 s; rw [← h8_pow2]; omega
  have hbl_n : binBitLength nOdd = 3 * s - 2 := by
    have hlo : 2 ^ (3 * s - 3) ≤ nOdd := by omega
    have hhi : nOdd < 2 ^ ((3 * s - 3) + 1) := by rw [Nat.pow_succ]; omega
    rw [binBitLength_of_pow2_sandwich (3 * s - 3) nOdd hlo hhi]; omega
  have hbl_m : binBitLength m = 3 * s - 2 := by
    have hlo : 2 ^ (3 * s - 3) ≤ m := by omega
    have hhi : m < 2 ^ ((3 * s - 3) + 1) := by rw [Nat.pow_succ]; omega
    rw [binBitLength_of_pow2_sandwich (3 * s - 3) m hlo hhi]; omega
  refine ⟨by omega, by omega, hbl_m, hbl_n, ?_, hpop_n s⟩
  change binPopcount m = 2 * s - 1
  rw [hm_2u, binPopcount_double_w15]
  exact hpop_u s (by omega)

/--
  Theorem W15.3a (`eventual_popcount_penalizing_all_bases_joint_exp_impossibility`,
  `zero custom axioms`):
  Equal-Bitlength High-Density `1`-Run Single-Step Popcount Drop (`(8^s - 1)/7 <- (3 * nOdd + 1)/2`,
  `878 -> 585` & `7022 -> 4681`), Universal Popcount-Penalizing (`1 ≤ p_P < q_P`) Arbitrary-Base
  (`∀ p_L, q_L ≥ 1`, Including Super-Critical `B_L ≥ 2^(1/3)`) Impossibility, & Complete 100%
  `(0, ∞)^2` All-Bases Two-Sided Joint `(binBitLength, binaryPopcount)` Exponential Impossibility
  (`Branch P1.2`, witness `ZPOS_POPCOUNT_DROP_4681_TO_7022_AND_ALT_TRANSITIONS`, `W15_H3`).
-/
theorem eventual_popcount_penalizing_all_bases_joint_exp_impossibility :
    ((∀ s : Nat, s ≥ 2 ->
        let nOdd := (8 ^ s - 1) / 7
        let m := (3 * nOdd + 1) / 2
        m % 3 = 2 ∧
        (2 * m - 1) / 3 = nOdd ∧
        binBitLength m = 3 * s - 2 ∧
        binBitLength nOdd = 3 * s - 2 ∧
        binaryPopcount m = 2 * s - 1 ∧
        binaryPopcount nOdd = s) ∧
     (binBitLength 878 = 10 ∧ binBitLength 585 = 10 ∧
      binaryPopcount 878 = 7 ∧ binaryPopcount 585 = 4 ∧
      binBitLength 7022 = 13 ∧ binBitLength 4681 = 13 ∧
      binaryPopcount 7022 = 9 ∧ binaryPopcount 4681 = 5)) ∧
    (∀ (M_0 : Nat), M_0 ≥ 3 ->
      ∀ (wNum wDen : Nat -> Nat) (c_0 C_hi p_L q_L p_P q_P pTheta qTheta : Nat),
        c_0 ≥ 1 -> p_L ≥ 1 -> q_L ≥ 1 -> p_P ≥ 1 -> p_P < q_P ->
        (∀ n : Nat, n ≥ M_0 ->
          c_0 * (q_L ^ binBitLength n * p_P ^ binaryPopcount n) * wDen n ≤
            (p_L ^ binBitLength n * q_P ^ binaryPopcount n) * wNum n ∧
          (p_L ^ binBitLength n * q_P ^ binaryPopcount n) * wNum n ≤
            C_hi * (q_L ^ binBitLength n * p_P ^ binaryPopcount n) * wDen n) ->
        ¬ IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta) ∧
    (∀ (M_0 : Nat), M_0 ≥ 3 ->
      ∀ (wNum wDen : Nat -> Nat) (c_0 C_hi p_L q_L p_P q_P pTheta qTheta : Nat),
        c_0 ≥ 1 -> p_L ≥ 1 -> q_L ≥ 1 -> p_P ≥ 1 -> q_P ≥ 1 ->
        (∀ n : Nat, n ≥ M_0 ->
          c_0 * (q_L ^ binBitLength n * p_P ^ binaryPopcount n) * wDen n ≤
            (p_L ^ binBitLength n * q_P ^ binaryPopcount n) * wNum n ∧
          (p_L ^ binBitLength n * q_P ^ binaryPopcount n) * wNum n ≤
            C_hi * (q_L ^ binBitLength n * p_P ^ binaryPopcount n) * wDen n) ->
        ¬ IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta) := by
  have hpen : ∀ (M_0 : Nat), M_0 ≥ 3 ->
      ∀ (wNum wDen : Nat -> Nat) (c_0 C_hi p_L q_L p_P q_P pTheta qTheta : Nat),
        c_0 ≥ 1 -> p_L ≥ 1 -> q_L ≥ 1 -> p_P ≥ 1 -> p_P < q_P ->
        (∀ n : Nat, n ≥ M_0 ->
          c_0 * (q_L ^ binBitLength n * p_P ^ binaryPopcount n) * wDen n ≤
            (p_L ^ binBitLength n * q_P ^ binaryPopcount n) * wNum n ∧
          (p_L ^ binBitLength n * q_P ^ binaryPopcount n) * wNum n ≤
            C_hi * (q_L ^ binBitLength n * p_P ^ binaryPopcount n) * wDen n) ->
        ¬ IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta := by
    intro M_0 hM0 wNum wDen c_0 C_hi p_L q_L p_P q_P pTheta qTheta
      hc0 hpL hqL hpP hpq_lt hsand hw
    have hq_pos : qTheta > 0 := Nat.lt_of_lt_of_le hw.1 hw.2.1
    let K_0 := C_hi + M_0 + 2
    let e := K_0 * p_P
    let s := e + 1
    have hs2 : s ≥ 2 := by
      have hm1 : 2 * 1 ≤ K_0 * p_P := Nat.mul_le_mul (by dsimp [K_0]; omega) hpP
      dsimp [s, e]; omega
    rcases equal_bitlength_popcount_drop_family s hs2 with
      ⟨hm_3, hnOdd_eq, hbl_m, hbl_o, hpop_m, hpop_o⟩
    let nOdd := (8 ^ s - 1) / 7
    let m := (3 * nOdd + 1) / 2
    have hnOdd_M0 : nOdd ≥ M_0 := by
      have hs_M0 : 3 * s - 3 ≥ M_0 := by
        have hm1 : K_0 * 1 ≤ K_0 * p_P := Nat.mul_le_mul_left K_0 hpP
        dsimp [s, e, K_0] at hm1 ⊢; omega
      have hlt := id_lt_pow2_w15s (3 * s - 3)
      have h8_sp : 8 ^ s = 8 * 2 ^ (3 * s - 3) := by
        rw [show (8 : Nat) = 2 ^ 3 from rfl, pow_pow_eq_mul_w5 2 3 s]
        conv => lhs; rw [show 3 * s = 3 + (3 * s - 3) by omega, Nat.pow_add]
      dsimp [nOdd]; rw [h8_sp]; omega
    have hm_M0 : m ≥ M_0 := by dsimp [m]; omega
    have hpre := hw.2.2.2.2 m hm_M0 hm_3
    dsimp only at hpre; rw [hnOdd_eq] at hpre
    have hbr : (wNum (2 * m) * wDen nOdd + wNum nOdd * wDen (2 * m)) * wDen m ≤
        wNum m * (wDen (2 * m) * wDen nOdd) :=
      nat_mul_le_cancel_left_w5 qTheta _ _ hq_pos
        (Nat.le_trans hpre (Nat.mul_le_mul_right _ hw.2.1))
    have hdrop : wNum nOdd * wDen m ≤ wNum m * wDen nOdd :=
      nat_mul_le_cancel_right_w5 (wDen (2 * m)) _ _ (hw.2.2.1 (2 * m) (by omega)).2 (by
        rw [show (wNum nOdd * wDen m) * wDen (2 * m) = (wNum nOdd * wDen (2 * m)) * wDen m by ac_rfl,
            show (wNum m * wDen nOdd) * wDen (2 * m) = wNum m * (wDen (2 * m) * wDen nOdd) by ac_rfl]
        rw [Nat.add_mul] at hbr; omega)
    let L := 3 * s - 2
    have hlo_o := (hsand nOdd hnOdd_M0).1
    have hhi_m := (hsand m hm_M0).2
    rw [hbl_o, hpop_o] at hlo_o
    rw [hbl_m, hpop_m] at hhi_m
    change c_0 * (q_L ^ L * p_P ^ s) * wDen nOdd ≤ (p_L ^ L * q_P ^ s) * wNum nOdd at hlo_o
    change (p_L ^ L * q_P ^ (2 * s - 1)) * wNum m ≤ C_hi * (q_L ^ L * p_P ^ (2 * s - 1)) * wDen m at hhi_m
    let F_c := (p_L ^ L * q_L ^ L * p_P ^ s * q_P ^ s) * (wDen m * wDen nOdd)
    have hF_pos : F_c > 0 := Nat.mul_le_mul
      (Nat.mul_le_mul
        (Nat.mul_le_mul
          (Nat.mul_le_mul (nat_pow_pos_of_pos p_L hpL L) (nat_pow_pos_of_pos q_L hqL L))
          (nat_pow_pos_of_pos p_P hpP s))
        (nat_pow_pos_of_pos q_P (by omega) s))
      (Nat.mul_le_mul (hw.2.2.1 m hm_M0).2 (hw.2.2.1 nOdd hnOdd_M0).2)
    have h2s_sp : 2 * s - 1 = s + e := by dsimp [s]; omega
    have hcomb : F_c * (c_0 * q_P ^ e) ≤ F_c * (C_hi * p_P ^ e) := by
      have hl : F_c * (c_0 * q_P ^ e) =
          ((p_L ^ L * q_P ^ (2 * s - 1)) * wDen m) * (c_0 * (q_L ^ L * p_P ^ s) * wDen nOdd) := by
        dsimp [F_c]; rw [h2s_sp, Nat.pow_add q_P s e]; ac_rfl
      have hr : F_c * (C_hi * p_P ^ e) =
          (p_L ^ L * q_P ^ s) * ((C_hi * (q_L ^ L * p_P ^ (2 * s - 1)) * wDen m) * wDen nOdd) := by
        dsimp [F_c]; rw [h2s_sp, Nat.pow_add p_P s e]; ac_rfl
      rw [hl, hr]
      calc ((p_L ^ L * q_P ^ (2 * s - 1)) * wDen m) * (c_0 * (q_L ^ L * p_P ^ s) * wDen nOdd)
          ≤ ((p_L ^ L * q_P ^ (2 * s - 1)) * wDen m) * ((p_L ^ L * q_P ^ s) * wNum nOdd) :=
            Nat.mul_le_mul_left _ hlo_o
        _ = (p_L ^ L * q_P ^ s) * ((p_L ^ L * q_P ^ (2 * s - 1)) * (wNum nOdd * wDen m)) := by ac_rfl
        _ ≤ (p_L ^ L * q_P ^ s) * ((p_L ^ L * q_P ^ (2 * s - 1)) * (wNum m * wDen nOdd)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hdrop)
        _ = (p_L ^ L * q_P ^ s) * (((p_L ^ L * q_P ^ (2 * s - 1)) * wNum m) * wDen nOdd) := by ac_rfl
        _ ≤ (p_L ^ L * q_P ^ s) * ((C_hi * (q_L ^ L * p_P ^ (2 * s - 1)) * wDen m) * wDen nOdd) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hhi_m)
    have hcanc := nat_mul_le_cancel_left_w5 F_c _ _ hF_pos hcomb
    have h1 : 1 * q_P ^ e ≤ c_0 * q_P ^ e := Nat.mul_le_mul_right _ hc0
    rw [Nat.one_mul] at h1
    have hqP_le : q_P ^ e ≤ K_0 * p_P ^ e :=
      Nat.le_trans (Nat.le_trans h1 hcanc) (Nat.mul_le_mul_right _ (by dsimp [K_0]; omega))
    have hgt_pow := pow_gt_const_mul_pow_of_lt_w15s p_P q_P K_0 hpP hpq_lt
    dsimp only [e] at hqP_le hgt_pow; omega
  refine ⟨⟨equal_bitlength_popcount_drop_family,
           by decide, by decide, by decide, by decide,
           by decide, by decide, by decide, by decide⟩,
          hpen, ?_⟩
  intro M_0 hM0 wNum wDen c_0 C_hi p_L q_L p_P q_P pTheta qTheta
    hc0 hpL hqL hpP hqP hsand
  rcases (by omega : p_P < q_P ∨ q_P < p_P ∨ p_P = q_P) with hlt | hgt | heq
  · exact hpen M_0 hM0 wNum wDen c_0 C_hi p_L q_L p_P q_P pTheta qTheta hc0 hpL hqL hpP hlt hsand
  · exact eventual_joint_bitlength_popcount_exp_impossibility.2.2.1 M_0 hM0
      wNum wDen c_0 C_hi p_L q_L p_P q_P pTheta qTheta hc0 hpL hqL hqP hgt hsand
  · subst heq
    apply eventual_pure_bitlength_twosided_ratio_impossibility_w15 M_0 hM0
      wNum wDen c_0 C_hi p_L q_L pTheta qTheta hc0 hpL hqL
    intro n hn
    rcases hsand n hn with ⟨hlo, hhi⟩
    let P := binaryPopcount n
    have hp_pos : p_P ^ P > 0 := nat_pow_pos_of_pos p_P hpP P
    refine ⟨nat_mul_le_cancel_right_w5 (p_P ^ P) _ _ hp_pos ?_,
            nat_mul_le_cancel_right_w5 (p_P ^ P) _ _ hp_pos ?_⟩
    · calc (c_0 * q_L ^ binBitLength n * wDen n) * p_P ^ P
          = c_0 * (q_L ^ binBitLength n * p_P ^ P) * wDen n := by ac_rfl
        _ ≤ (p_L ^ binBitLength n * p_P ^ P) * wNum n := hlo
        _ = (p_L ^ binBitLength n * wNum n) * p_P ^ P := by ac_rfl
    · calc (p_L ^ binBitLength n * wNum n) * p_P ^ P
          = (p_L ^ binBitLength n * p_P ^ P) * wNum n := by ac_rfl
        _ ≤ C_hi * (q_L ^ binBitLength n * p_P ^ P) * wDen n := hhi
        _ = (C_hi * q_L ^ binBitLength n * wDen n) * p_P ^ P := by ac_rfl

-- ----------------------------------------------------------------------------
-- Section 1B: Digit-Transition Count `binaryAltTransitions` Exact Laws &
--             Complete 100% `(0, ∞)^2` Joint `(binBitLength, binaryAltTransitions)`
--             Two-Sided Exponential Impossibility (`W15_H3`)
-- ----------------------------------------------------------------------------

/-- Fuel-structural helper for `binaryAltTransitions` (pure kernel `rfl`-reducible). -/
def binaryAltTransitionsAux : Nat -> Nat -> Nat
  | 0, _ => 0
  | _ + 1, 0 => 0
  | _ + 1, 1 => 0
  | fuel + 1, n =>
    (if n % 2 != (n / 2) % 2 then 1 else 0) + binaryAltTransitionsAux fuel (n / 2)

/-- Number of adjacent distinct-bit transitions in the standard MSB-to-LSB binary
    expansion of `n` (`0` for `n < 2`, `2^k - 1 -> 0`, `2^k -> 1` for `k ≥ 1`). -/
def binaryAltTransitions (n : Nat) : Nat :=
  binaryAltTransitionsAux n n

private theorem binaryAltTransitionsAux_eq_binAltTransAux :
    ∀ (fuel n : Nat), binaryAltTransitionsAux fuel n = binAltTransAux fuel n
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | _ + 1, 1 => rfl
  | fuel + 1, n + 2 => by
    have hle : ¬ (n + 2 ≤ 1) := by omega
    simp only [binaryAltTransitionsAux, binAltTransAux, hle, ite_false]
    rw [binaryAltTransitionsAux_eq_binAltTransAux fuel ((n + 2) / 2)]
    generalize (n + 2) % 2 = r1, ((n + 2) / 2) % 2 = r2
    by_cases he : r1 = r2
    · subst he; simp
    · have hb : (r1 != r2) = true := bne_iff_ne.mpr he
      rw [hb, ite_true_dec_w15s he]; rfl

private theorem binaryAltTransitions_eq_binAltTransitions (n : Nat) :
    binaryAltTransitions n = binAltTransitions n :=
  binaryAltTransitionsAux_eq_binAltTransAux n n

private theorem binaryAltTransitionsAux_eq_of_le :
    ∀ (f1 f2 n : Nat), n ≤ f1 -> n ≤ f2 ->
      binaryAltTransitionsAux f1 n = binaryAltTransitionsAux f2 n
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, n, h1, _ => by rw [show n = 0 by omega]; rfl
  | _ + 1, 0, n, _, h2 => by rw [show n = 0 by omega]; rfl
  | _ + 1, _ + 1, 0, _, _ => rfl
  | _ + 1, _ + 1, 1, _, _ => rfl
  | f1 + 1, f2 + 1, n + 2, h1, h2 => by
    simp only [binaryAltTransitionsAux]
    rw [binaryAltTransitionsAux_eq_of_le f1 f2 ((n + 2) / 2) (by omega) (by omega)]

private theorem binaryAltTransitions_step_ge2 (m : Nat) (hm : m ≥ 2) :
    binaryAltTransitions m =
      (if m % 2 != (m / 2) % 2 then 1 else 0) + binaryAltTransitions (m / 2) := by
  rcases (⟨m - 2, by omega⟩ : ∃ k : Nat, m = k + 2) with ⟨k, rfl⟩
  unfold binaryAltTransitions
  simp only [binaryAltTransitionsAux]
  rw [binaryAltTransitionsAux_eq_of_le (k + 1) ((k + 2) / 2) ((k + 2) / 2) (by omega) (Nat.le_refl _)]

private theorem binaryAltTransitions_double_even (m : Nat) (hm : m ≥ 1) :
    binaryAltTransitions (2 * (2 * m)) = binaryAltTransitions (2 * m) := by
  rw [binaryAltTransitions_step_ge2 (2 * (2 * m)) (by omega)]
  have h1 : (2 * (2 * m)) % 2 = 0 := by omega
  have h2 : (2 * (2 * m)) / 2 = 2 * m := by omega
  have h3 : (2 * m) % 2 = 0 := by omega
  rw [h1, h2, h3]; simp

private theorem binaryAltTransitions_double_odd (m : Nat) :
    binaryAltTransitions (2 * (2 * m + 1)) = 1 + binaryAltTransitions (2 * m + 1) := by
  rw [binaryAltTransitions_step_ge2 (2 * (2 * m + 1)) (by omega)]
  have h1 : (2 * (2 * m + 1)) % 2 = 0 := by omega
  have h2 : (2 * (2 * m + 1)) / 2 = 2 * m + 1 := by omega
  have h3 : (2 * m + 1) % 2 = 1 := by omega
  rw [h1, h2, h3]; rfl

private theorem binaryAltTransitions_succ_double_even (m : Nat) (hm : m ≥ 1) :
    binaryAltTransitions (2 * (2 * m) + 1) = 1 + binaryAltTransitions (2 * m) := by
  rw [binaryAltTransitions_step_ge2 (2 * (2 * m) + 1) (by omega)]
  have h1 : (2 * (2 * m) + 1) % 2 = 1 := by omega
  have h2 : (2 * (2 * m) + 1) / 2 = 2 * m := by omega
  have h3 : (2 * m) % 2 = 0 := by omega
  rw [h1, h2, h3]; rfl

private theorem binaryAltTransitions_succ_double_odd (m : Nat) :
    binaryAltTransitions (2 * (2 * m + 1) + 1) = binaryAltTransitions (2 * m + 1) := by
  rw [binaryAltTransitions_step_ge2 (2 * (2 * m + 1) + 1) (by omega)]
  have h1 : (2 * (2 * m + 1) + 1) % 2 = 1 := by omega
  have h2 : (2 * (2 * m + 1) + 1) / 2 = 2 * m + 1 := by omega
  have h3 : (2 * m + 1) % 2 = 1 := by omega
  rw [h1, h2, h3]; simp

private theorem binaryAltTransitions_mersenne :
    ∀ k : Nat, binaryAltTransitions (2 ^ k - 1) = 0
  | 0 => rfl
  | 1 => rfl
  | k + 2 => by
    have hp := pow2_pos_nat k
    have heq : 2 ^ (k + 2) - 1 = 2 * (2 * (2 ^ k - 1) + 1) + 1 := by
      rw [Nat.pow_succ, Nat.pow_succ]; omega
    rw [heq, binaryAltTransitions_succ_double_odd,
        show 2 * (2 ^ k - 1) + 1 = 2 ^ (k + 1) - 1 by rw [Nat.pow_succ]; omega]
    exact binaryAltTransitions_mersenne (k + 1)

private theorem binaryAltTransitions_pow2 :
    ∀ k : Nat, k ≥ 1 -> binaryAltTransitions (2 ^ k) = 1
  | 0, hk => by omega
  | 1, _ => rfl
  | k + 2, _ => by
    have hp := pow2_pos_nat k
    have heq : 2 ^ (k + 2) = 2 * (2 * 2 ^ k) := by rw [Nat.pow_succ, Nat.pow_succ]; omega
    rw [heq, binaryAltTransitions_double_even (2 ^ k) hp,
        show 2 * 2 ^ k = 2 ^ (k + 1) by rw [Nat.pow_succ]; omega]
    exact binaryAltTransitions_pow2 (k + 1) (by omega)

private theorem binaryAltTransitions_alt_geom :
    ∀ k : Nat, k ≥ 1 ->
      ((4 ^ k - 1) / 3) % 2 = 1 ∧ binaryAltTransitions ((4 ^ k - 1) / 3) = 2 * k - 2
  | 0, hk => by omega
  | 1, _ => ⟨rfl, rfl⟩
  | k + 2, _ => by
    rcases binaryAltTransitions_alt_geom (k + 1) (by omega) with ⟨hodd, htr⟩
    have hm3 : ∀ m : Nat, 4 ^ m % 3 = 1 := by
      intro m; induction m with
      | zero => rfl
      | succ m' ih => rw [Nat.pow_succ, Nat.mul_mod, ih]
    let a := (4 ^ (k + 1) - 1) / 3
    change a % 2 = 1 at hodd
    change binaryAltTransitions a = 2 * (k + 1) - 2 at htr
    have ha_pos : a ≥ 1 := by
      dsimp [a]; have hp := nat_pow_pos_of_pos 4 (by decide) k; rw [Nat.pow_succ]; omega
    have hrec : (4 ^ (k + 2) - 1) / 3 = 2 * (2 * a) + 1 := by
      dsimp [a]; have h3 := hm3 (k + 1); rw [Nat.pow_succ 4 (k + 1)]; omega
    let q := a / 2
    have ha_sp : a = 2 * q + 1 := by dsimp [q]; omega
    refine ⟨by rw [hrec]; omega, ?_⟩
    rw [hrec, binaryAltTransitions_succ_double_even a ha_pos, ha_sp,
        binaryAltTransitions_double_odd q, ← ha_sp, htr]
    omega

private def vAltDropAuxW15 : Nat -> Nat
  | 0 => 0
  | k + 1 => 64 * vAltDropAuxW15 k + 7

private theorem binaryAltTransitions_jump_and_drop_families :
    (∀ s : Nat, s ≥ 2 ->
      let m := 4 ^ s + 1
      let nOdd := (2 * m - 1) / 3
      m % 3 = 2 ∧
      binBitLength m = 2 * s + 1 ∧
      binBitLength nOdd = 2 * s ∧
      binaryAltTransitions m = 2 ∧
      binaryAltTransitions nOdd = 2 * s - 2) ∧
    (∀ s : Nat, s ≥ 1 ->
      let m := (4 ^ (3 * s + 2) - 1) / 3
      let nOdd := (2 * m - 1) / 3
      m % 3 = 2 ∧
      binBitLength m = 6 * s + 3 ∧
      binBitLength nOdd = 6 * s + 2 ∧
      binaryAltTransitions m = 6 * s + 2 ∧
      binaryAltTransitions nOdd = 2 * s) := by
  refine ⟨?_, ?_⟩
  · intro s hs2; dsimp only
    rcases eventual_joint_bitlength_popcount_exp_impossibility.1.2.1 s hs2 with
      ⟨hm3, hbl_m, hbl_o, _, _, _⟩
    have hm_eq : 4 ^ s + 1 = 2 * (2 * 2 ^ (2 * s - 2)) + 1 := by
      rw [pow4_eq_pow2_even s]
      conv => lhs; lhs; rw [show 2 * s = (2 * s - 2) + 2 by omega, Nat.pow_add]
      omega
    have htr_m : binaryAltTransitions (4 ^ s + 1) = 2 := by
      have hp_sp : 2 * 2 ^ (2 * s - 2) = 2 ^ (2 * s - 1) := by
        calc 2 * 2 ^ (2 * s - 2)
            = 2 ^ (2 * s - 2) * 2 := Nat.mul_comm _ _
          _ = 2 ^ ((2 * s - 2) + 1) := (Nat.pow_succ 2 _).symm
          _ = 2 ^ (2 * s - 1) := by congr 1; omega
      rw [hm_eq, binaryAltTransitions_succ_double_even (2 ^ (2 * s - 2)) (pow2_pos_nat _),
          hp_sp, binaryAltTransitions_pow2 (2 * s - 1) (by omega)]
    rcases binaryAltTransitions_alt_geom s (by omega) with ⟨ha_odd, ha_tr⟩
    let a := (4 ^ s - 1) / 3
    change a % 2 = 1 at ha_odd
    change binaryAltTransitions a = 2 * s - 2 at ha_tr
    have hn_eq : (2 * (4 ^ s + 1) - 1) / 3 = 2 * (2 * (a / 2) + 1) + 1 := by
      have ha_sp : a = 2 * (a / 2) + 1 := by omega
      dsimp [a] at ha_sp ⊢; omega
    have htr_o : binaryAltTransitions ((2 * (4 ^ s + 1) - 1) / 3) = 2 * s - 2 := by
      rw [hn_eq, binaryAltTransitions_succ_double_odd,
          show 2 * (a / 2) + 1 = a by omega, ha_tr]
    exact ⟨hm3, hbl_m, hbl_o, htr_m, htr_o⟩
  · have hv_spec : ∀ k : Nat,
        9 * (32 * vAltDropAuxW15 k + 3) + 5 = 2 * 4 ^ (3 * k + 2) ∧
        (k ≥ 1 -> vAltDropAuxW15 k ≥ 7 ∧ vAltDropAuxW15 k % 2 = 1 ∧
          binaryAltTransitions (vAltDropAuxW15 k) = 2 * k - 2) := by
      intro k; induction k with
      | zero => exact ⟨by decide, fun hk => by omega⟩
      | succ k' ih =>
        rcases ih with ⟨h9, ih_ge⟩
        have h9_next : 9 * (32 * vAltDropAuxW15 (k' + 1) + 3) + 5 = 2 * 4 ^ (3 * (k' + 1) + 2) := by
          simp only [vAltDropAuxW15]
          have hpow : 4 ^ (3 * (k' + 1) + 2) = 64 * 4 ^ (3 * k' + 2) := by
            rw [show 3 * (k' + 1) + 2 = (3 * k' + 2) + 3 by omega, Nat.pow_add 4 _ 3]
            change _ = 64 * _; ac_rfl
          rw [hpow]; omega
        refine ⟨h9_next, fun _ => ?_⟩
        cases k' with
        | zero => exact ⟨by decide, by decide, by decide⟩
        | succ k'' =>
          rcases ih_ge (by omega) with ⟨hv_ge, hv_odd, hv_tr⟩
          let v0 := vAltDropAuxW15 (k'' + 1)
          change v0 ≥ 7 at hv_ge; change v0 % 2 = 1 at hv_odd
          change binaryAltTransitions v0 = 2 * (k'' + 1) - 2 at hv_tr
          have hsp_v0 : v0 = 2 * (v0 / 2) + 1 := by omega
          have h64 : vAltDropAuxW15 (k'' + 2) = 2 * (2 * (2 * (8 * v0) + 1) + 1) + 1 := by
            simp only [vAltDropAuxW15]; change 64 * v0 + 7 = _; omega
          have h16 : 2 * (8 * v0) + 1 = 2 * (2 * (4 * v0)) + 1 := by omega
          have h8 : 2 * (4 * v0) = 2 * (2 * (2 * v0)) := by omega
          refine ⟨by simp only [vAltDropAuxW15]; change 64 * v0 + 7 ≥ 7; omega,
                  by simp only [vAltDropAuxW15]; change (64 * v0 + 7) % 2 = 1; omega, ?_⟩
          rw [h64, binaryAltTransitions_succ_double_odd, binaryAltTransitions_succ_double_odd,
              h16, binaryAltTransitions_succ_double_even (4 * v0) (by omega),
              h8, binaryAltTransitions_double_even (2 * v0) (by omega),
              binaryAltTransitions_double_even v0 (by omega),
              hsp_v0, binaryAltTransitions_double_odd (v0 / 2), ← hsp_v0, hv_tr]
          omega
    intro s hs1; dsimp only
    rcases hv_spec s with ⟨h9_eq, hv_s⟩
    rcases hv_s hs1 with ⟨hv_ge, hv_odd, hv_tr⟩
    let v := vAltDropAuxW15 s
    change 9 * (32 * v + 3) + 5 = 2 * 4 ^ (3 * s + 2) at h9_eq
    let m := (4 ^ (3 * s + 2) - 1) / 3
    have h4_eq : 4 ^ (3 * s + 2) = 3 * m + 1 := by dsimp [m]; omega
    have hm_3 : m % 3 = 2 := by omega
    have hnOdd_eq : (2 * m - 1) / 3 = 32 * v + 3 := by omega
    have htr_m : binaryAltTransitions m = 6 * s + 2 := by
      have h := (binaryAltTransitions_alt_geom (3 * s + 2) (by omega)).2
      dsimp [m]; omega
    have htr_o : binaryAltTransitions ((2 * m - 1) / 3) = 2 * s := by
      rw [hnOdd_eq]
      have hsp_v : v = 2 * (v / 2) + 1 := by dsimp [v]; omega
      have h32 : 32 * v + 3 = 2 * (2 * (8 * v) + 1) + 1 := by omega
      have h16 : 2 * (2 * (8 * v) + 1) + 1 = 2 * (2 * (8 * v) + 1) + 1 := rfl
      rw [h32, binaryAltTransitions_succ_double_odd,
          show 2 * (8 * v) + 1 = 2 * (2 * (4 * v)) + 1 by omega,
          binaryAltTransitions_succ_double_even (4 * v) (by dsimp [v]; omega),
          show 2 * (4 * v) = 2 * (2 * (2 * v)) by omega,
          binaryAltTransitions_double_even (2 * v) (by dsimp [v]; omega),
          binaryAltTransitions_double_even v (by dsimp [v]; omega),
          hsp_v, binaryAltTransitions_double_odd (v / 2), ← hsp_v]
      dsimp [v]; omega
    have h4_pow2 : 4 ^ (3 * s + 2) = 2 ^ (6 * s + 4) := by
      rw [pow4_eq_pow2_even (3 * s + 2), show 2 * (3 * s + 2) = 6 * s + 4 by omega]
    have hp_pos : 2 ^ (6 * s + 1) ≥ 128 := by
      have hc : (2 : Nat) ^ 7 = 128 := by decide
      rw [← hc]; exact pow2_mono_nat (by omega)
    have hp_rel : 2 ^ (6 * s + 4) = 8 * 2 ^ (6 * s + 1) := by
      rw [show 6 * s + 4 = (6 * s + 1) + 3 by omega, Nat.pow_add]; ac_rfl
    have hbl_m : binBitLength m = 6 * s + 3 := by
      have hlo : 2 ^ (6 * s + 2) ≤ m := by
        rw [show 6 * s + 2 = (6 * s + 1) + 1 by omega, Nat.pow_succ]; omega
      have hhi : m < 2 ^ ((6 * s + 2) + 1) := by
        rw [show (6 * s + 2) + 1 = (6 * s + 1) + 2 by omega, Nat.pow_add]; omega
      exact binBitLength_of_pow2_sandwich (6 * s + 2) m hlo hhi
    have hbl_o : binBitLength ((2 * m - 1) / 3) = 6 * s + 2 := by
      have hlo : 2 ^ (6 * s + 1) ≤ (2 * m - 1) / 3 := by omega
      have hhi : (2 * m - 1) / 3 < 2 ^ ((6 * s + 1) + 1) := by rw [Nat.pow_succ]; omega
      exact binBitLength_of_pow2_sandwich (6 * s + 1) ((2 * m - 1) / 3) hlo hhi
    exact ⟨hm_3, hbl_m, hbl_o, htr_m, htr_o⟩

/--
  Theorem W15.3b (`eventual_joint_bitlength_alt_transitions_exp_impossibility`,
  `zero custom axioms`):
  Exact Digit-Transition (`binaryAltTransitions`) Preimage Jump (`4^s + 1 -> (2*4^s + 1)/3`,
  `2 -> 2s - 2`) & Drop (`(4^(3s+2) - 1)/3 -> (2*4^(3s+2) - 5)/9`, `6s + 2 -> 2s`; `21845 -> 14563`,
  `14 -> 4`) Laws, & Complete 100% `(0, ∞)^2` All-Bases Two-Sided Joint
  `(binBitLength, binaryAltTransitions)` Exponential Impossibility Across ALL
  `∀ M_0 ≥ 3, ∀ p_L, q_L, p_T, q_T ≥ 1` (`Branch P1.2`, `W15_H3`).
-/
theorem eventual_joint_bitlength_alt_transitions_exp_impossibility :
    ((∀ n : Nat, binaryAltTransitions n = binAltTransitions n) ∧
     (∀ k : Nat, binaryAltTransitions (2 ^ k - 1) = 0) ∧
     (∀ k : Nat, k ≥ 1 -> binaryAltTransitions (2 ^ k) = 1) ∧
     (∀ s : Nat, s ≥ 2 ->
        let m := 4 ^ s + 1
        let nOdd := (2 * m - 1) / 3
        m % 3 = 2 ∧
        binBitLength m = 2 * s + 1 ∧
        binBitLength nOdd = 2 * s ∧
        binaryAltTransitions m = 2 ∧
        binaryAltTransitions nOdd = 2 * s - 2) ∧
     (∀ s : Nat, s ≥ 1 ->
        let m := (4 ^ (3 * s + 2) - 1) / 3
        let nOdd := (2 * m - 1) / 3
        m % 3 = 2 ∧
        binBitLength m = 6 * s + 3 ∧
        binBitLength nOdd = 6 * s + 2 ∧
        binaryAltTransitions m = 6 * s + 2 ∧
        binaryAltTransitions nOdd = 2 * s) ∧
     (binaryAltTransitions 257 = 2 ∧ binaryAltTransitions 171 = 6 ∧
      binaryAltTransitions 21845 = 14 ∧ binaryAltTransitions 14563 = 4)) ∧
    (∀ (M_0 : Nat), M_0 ≥ 3 ->
      ∀ (wNum wDen : Nat -> Nat) (c_0 C_hi p_L q_L p_T q_T pTheta qTheta : Nat),
        c_0 ≥ 1 -> p_L ≥ 1 -> q_L ≥ 1 -> p_T ≥ 1 -> q_T ≥ 1 ->
        (∀ n : Nat, n ≥ M_0 ->
          c_0 * (q_L ^ binBitLength n * p_T ^ binaryAltTransitions n) * wDen n ≤
            (p_L ^ binBitLength n * q_T ^ binaryAltTransitions n) * wNum n ∧
          (p_L ^ binBitLength n * q_T ^ binaryAltTransitions n) * wNum n ≤
            C_hi * (q_L ^ binBitLength n * p_T ^ binaryAltTransitions n) * wDen n) ->
        ¬ IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta) := by
  rcases binaryAltTransitions_jump_and_drop_families with ⟨hjump, hdrop_fam⟩
  refine ⟨⟨binaryAltTransitions_eq_binAltTransitions,
           binaryAltTransitions_mersenne, binaryAltTransitions_pow2, hjump, hdrop_fam,
           by decide, by decide, by decide, by decide⟩, ?_⟩
  intro M_0 hM0 wNum wDen c_0 C_hi p_L q_L p_T q_T pTheta qTheta
    hc0 hpL hqL hpT hqT hsand
  rcases (by omega : q_T < p_T ∨ p_T < q_T ∨ p_T = q_T) with hrew | hpen | heq
  · -- Case 1 (`q_T < p_T`, transition-rewarding): killed in 1 step by `4^s + 1 -> (2*4^s + 1)/3`!
    intro hw
    have hq_pos : qTheta > 0 := Nat.lt_of_lt_of_le hw.1 hw.2.1
    let K_0 := C_hi * q_L + M_0 + 2
    let e := K_0 * q_T
    let s := e + 2
    rcases hjump s (by dsimp [s]; omega) with ⟨hm3, hbl_m, hbl_o, htr_m, htr_o⟩
    let m := 4 ^ s + 1
    let nOdd := (2 * m - 1) / 3
    have hnOdd_M0 : nOdd ≥ M_0 := by
      have hs_M0 : 2 * s - 1 ≥ M_0 := by
        have hm1 : K_0 * 1 ≤ K_0 * q_T := Nat.mul_le_mul_left K_0 hqT
        dsimp [s, e, K_0] at hm1 ⊢; omega
      have hlt := id_lt_pow2_w15s (2 * s - 1)
      have h4_sp : 4 ^ s = 2 * 2 ^ (2 * s - 1) := by
        rw [pow4_eq_pow2_even s]
        conv => lhs; rw [show 2 * s = (2 * s - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
      dsimp [nOdd, m]; rw [h4_sp]; omega
    have hm_M0 : m ≥ M_0 := by dsimp [nOdd] at hnOdd_M0; omega
    have hpre := hw.2.2.2.2 m hm_M0 hm3
    dsimp only at hpre
    have hbr : (wNum (2 * m) * wDen nOdd + wNum nOdd * wDen (2 * m)) * wDen m ≤
        wNum m * (wDen (2 * m) * wDen nOdd) :=
      nat_mul_le_cancel_left_w5 qTheta _ _ hq_pos (Nat.le_trans hpre (Nat.mul_le_mul_right _ hw.2.1))
    have hd_step : wNum nOdd * wDen m ≤ wNum m * wDen nOdd :=
      nat_mul_le_cancel_right_w5 (wDen (2 * m)) _ _ (hw.2.2.1 (2 * m) (by omega)).2 (by
        rw [show (wNum nOdd * wDen m) * wDen (2 * m) = (wNum nOdd * wDen (2 * m)) * wDen m by ac_rfl,
            show (wNum m * wDen nOdd) * wDen (2 * m) = wNum m * (wDen (2 * m) * wDen nOdd) by ac_rfl]
        rw [Nat.add_mul] at hbr; omega)
    have hlo_o := (hsand nOdd hnOdd_M0).1
    have hhi_m := (hsand m hm_M0).2
    rw [hbl_o, htr_o] at hlo_o; rw [hbl_m, htr_m] at hhi_m
    let D_e := 2 * e
    have h2s2 : 2 * s - 2 = 2 + D_e := by dsimp [s, D_e]; omega
    let F_c := (p_L ^ (2 * s) * q_L ^ (2 * s) * p_T ^ 2 * q_T ^ 2) * (wDen m * wDen nOdd)
    have hF_pos : F_c > 0 := Nat.mul_le_mul
      (Nat.mul_le_mul
        (Nat.mul_le_mul
          (Nat.mul_le_mul (nat_pow_pos_of_pos p_L hpL _) (nat_pow_pos_of_pos q_L hqL _))
          (nat_pow_pos_of_pos p_T hpT 2))
        (nat_pow_pos_of_pos q_T hqT 2))
      (Nat.mul_le_mul (hw.2.2.1 m hm_M0).2 (hw.2.2.1 nOdd hnOdd_M0).2)
    have hcomb : F_c * (c_0 * p_L * p_T ^ D_e) ≤ F_c * ((C_hi * q_L) * q_T ^ D_e) := by
      have hl : F_c * (c_0 * p_L * p_T ^ D_e) =
          ((p_L ^ (2 * s + 1) * q_T ^ 2) * wDen m) *
            (c_0 * (q_L ^ (2 * s) * p_T ^ (2 * s - 2)) * wDen nOdd) := by
        dsimp [F_c]; rw [h2s2, Nat.pow_add p_T 2 D_e, Nat.pow_succ p_L (2 * s)]; ac_rfl
      have hr : F_c * ((C_hi * q_L) * q_T ^ D_e) =
          (p_L ^ (2 * s) * q_T ^ (2 * s - 2)) *
            ((C_hi * (q_L ^ (2 * s + 1) * p_T ^ 2) * wDen m) * wDen nOdd) := by
        dsimp [F_c]; rw [h2s2, Nat.pow_add q_T 2 D_e, Nat.pow_succ q_L (2 * s)]; ac_rfl
      rw [hl, hr]
      calc ((p_L ^ (2 * s + 1) * q_T ^ 2) * wDen m) *
            (c_0 * (q_L ^ (2 * s) * p_T ^ (2 * s - 2)) * wDen nOdd)
          ≤ ((p_L ^ (2 * s + 1) * q_T ^ 2) * wDen m) *
              ((p_L ^ (2 * s) * q_T ^ (2 * s - 2)) * wNum nOdd) := Nat.mul_le_mul_left _ hlo_o
        _ = (p_L ^ (2 * s) * q_T ^ (2 * s - 2)) *
              ((p_L ^ (2 * s + 1) * q_T ^ 2) * (wNum nOdd * wDen m)) := by ac_rfl
        _ ≤ (p_L ^ (2 * s) * q_T ^ (2 * s - 2)) *
              ((p_L ^ (2 * s + 1) * q_T ^ 2) * (wNum m * wDen nOdd)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hd_step)
        _ = (p_L ^ (2 * s) * q_T ^ (2 * s - 2)) *
              (((p_L ^ (2 * s + 1) * q_T ^ 2) * wNum m) * wDen nOdd) := by ac_rfl
        _ ≤ (p_L ^ (2 * s) * q_T ^ (2 * s - 2)) *
              ((C_hi * (q_L ^ (2 * s + 1) * p_T ^ 2) * wDen m) * wDen nOdd) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hhi_m)
    have hcanc := nat_mul_le_cancel_left_w5 F_c _ _ hF_pos hcomb
    have h1 : 1 * p_T ^ D_e ≤ (c_0 * p_L) * p_T ^ D_e := Nat.mul_le_mul_right _ (Nat.mul_le_mul hc0 hpL)
    rw [Nat.one_mul] at h1
    have hp_De : p_T ^ D_e ≤ K_0 * q_T ^ D_e :=
      Nat.le_trans (Nat.le_trans h1 hcanc) (Nat.mul_le_mul_right _ (by dsimp [K_0]; omega))
    have hp_e : p_T ^ e ≤ K_0 * q_T ^ e := by
      have hm1 : q_T ^ e * p_T ^ e ≤ q_T ^ e * (K_0 * q_T ^ e) := by
        calc q_T ^ e * p_T ^ e
            ≤ p_T ^ e * p_T ^ e := Nat.mul_le_mul_right _ (pow_mono_base_w15s q_T p_T (Nat.le_of_lt hrew) e)
          _ = p_T ^ D_e := by dsimp [D_e]; rw [show 2 * e = e + e by omega, Nat.pow_add]
          _ ≤ K_0 * q_T ^ D_e := hp_De
          _ = q_T ^ e * (K_0 * q_T ^ e) := by dsimp [D_e]; rw [show 2 * e = e + e by omega, Nat.pow_add]; ac_rfl
      exact nat_mul_le_cancel_left_w5 (q_T ^ e) _ _ (nat_pow_pos_of_pos q_T hqT e) hm1
    have hgt_pow := pow_gt_const_mul_pow_of_lt_w15s q_T p_T K_0 hqT hrew
    dsimp only [e] at hp_e hgt_pow; omega
  · -- Case 2 (`p_T < q_T`, transition-penalizing): killed in 1 step by `(4^(3s+2) - 1)/3 -> (2*m - 1)/3`!
    intro hw
    have hq_pos : qTheta > 0 := Nat.lt_of_lt_of_le hw.1 hw.2.1
    let K_0 := C_hi * q_L + M_0 + 2
    let e := K_0 * p_T
    let s := e + 1
    rcases hdrop_fam s (by dsimp [s]; omega) with ⟨hm3, hbl_m, hbl_o, htr_m, htr_o⟩
    let m := (4 ^ (3 * s + 2) - 1) / 3
    let nOdd := (2 * m - 1) / 3
    have hnOdd_M0 : nOdd ≥ M_0 := by
      have hs_M0 : 6 * s + 1 ≥ M_0 := by
        have hm1 : K_0 * 1 ≤ K_0 * p_T := Nat.mul_le_mul_left K_0 hpT
        dsimp [s, e, K_0] at hm1 ⊢; omega
      have hlt := id_lt_pow2_w15s (6 * s + 1)
      have h4_sp : 4 ^ (3 * s + 2) = 8 * 2 ^ (6 * s + 1) := by
        rw [pow4_eq_pow2_even (3 * s + 2), show 2 * (3 * s + 2) = 3 + (6 * s + 1) by omega, Nat.pow_add]
      dsimp [nOdd, m]; rw [h4_sp]; omega
    have hm_M0 : m ≥ M_0 := by dsimp [nOdd] at hnOdd_M0; omega
    have hpre := hw.2.2.2.2 m hm_M0 hm3
    dsimp only at hpre
    have hbr : (wNum (2 * m) * wDen nOdd + wNum nOdd * wDen (2 * m)) * wDen m ≤
        wNum m * (wDen (2 * m) * wDen nOdd) :=
      nat_mul_le_cancel_left_w5 qTheta _ _ hq_pos (Nat.le_trans hpre (Nat.mul_le_mul_right _ hw.2.1))
    have hd_step : wNum nOdd * wDen m ≤ wNum m * wDen nOdd :=
      nat_mul_le_cancel_right_w5 (wDen (2 * m)) _ _ (hw.2.2.1 (2 * m) (by omega)).2 (by
        rw [show (wNum nOdd * wDen m) * wDen (2 * m) = (wNum nOdd * wDen (2 * m)) * wDen m by ac_rfl,
            show (wNum m * wDen nOdd) * wDen (2 * m) = wNum m * (wDen (2 * m) * wDen nOdd) by ac_rfl]
        rw [Nat.add_mul] at hbr; omega)
    have hlo_o := (hsand nOdd hnOdd_M0).1
    have hhi_m := (hsand m hm_M0).2
    rw [hbl_o, htr_o] at hlo_o; rw [hbl_m, htr_m] at hhi_m
    let D_e := 4 * s + 2
    have h6s2 : 6 * s + 2 = 2 * s + D_e := by dsimp [D_e]; omega
    let F_c := (p_L ^ (6 * s + 2) * q_L ^ (6 * s + 2) * p_T ^ (2 * s) * q_T ^ (2 * s)) * (wDen m * wDen nOdd)
    have hF_pos : F_c > 0 := Nat.mul_le_mul
      (Nat.mul_le_mul
        (Nat.mul_le_mul
          (Nat.mul_le_mul (nat_pow_pos_of_pos p_L hpL _) (nat_pow_pos_of_pos q_L hqL _))
          (nat_pow_pos_of_pos p_T hpT _))
        (nat_pow_pos_of_pos q_T hqT _))
      (Nat.mul_le_mul (hw.2.2.1 m hm_M0).2 (hw.2.2.1 nOdd hnOdd_M0).2)
    have hcomb : F_c * (c_0 * p_L * q_T ^ D_e) ≤ F_c * ((C_hi * q_L) * p_T ^ D_e) := by
      have hl : F_c * (c_0 * p_L * q_T ^ D_e) =
          ((p_L ^ (6 * s + 3) * q_T ^ (6 * s + 2)) * wDen m) *
            (c_0 * (q_L ^ (6 * s + 2) * p_T ^ (2 * s)) * wDen nOdd) := by
        dsimp [F_c]
        rw [show 6 * s + 3 = (6 * s + 2) + 1 by omega, Nat.pow_succ p_L (6 * s + 2),
            h6s2, Nat.pow_add q_T (2 * s) D_e]; ac_rfl
      have hr : F_c * ((C_hi * q_L) * p_T ^ D_e) =
          (p_L ^ (6 * s + 2) * q_T ^ (2 * s)) *
            ((C_hi * (q_L ^ (6 * s + 3) * p_T ^ (6 * s + 2)) * wDen m) * wDen nOdd) := by
        dsimp [F_c]
        rw [show 6 * s + 3 = (6 * s + 2) + 1 by omega, Nat.pow_succ q_L (6 * s + 2),
            h6s2, Nat.pow_add p_T (2 * s) D_e]; ac_rfl
      rw [hl, hr]
      calc ((p_L ^ (6 * s + 3) * q_T ^ (6 * s + 2)) * wDen m) *
            (c_0 * (q_L ^ (6 * s + 2) * p_T ^ (2 * s)) * wDen nOdd)
          ≤ ((p_L ^ (6 * s + 3) * q_T ^ (6 * s + 2)) * wDen m) *
              ((p_L ^ (6 * s + 2) * q_T ^ (2 * s)) * wNum nOdd) := Nat.mul_le_mul_left _ hlo_o
        _ = (p_L ^ (6 * s + 2) * q_T ^ (2 * s)) *
              ((p_L ^ (6 * s + 3) * q_T ^ (6 * s + 2)) * (wNum nOdd * wDen m)) := by ac_rfl
        _ ≤ (p_L ^ (6 * s + 2) * q_T ^ (2 * s)) *
              ((p_L ^ (6 * s + 3) * q_T ^ (6 * s + 2)) * (wNum m * wDen nOdd)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hd_step)
        _ = (p_L ^ (6 * s + 2) * q_T ^ (2 * s)) *
              (((p_L ^ (6 * s + 3) * q_T ^ (6 * s + 2)) * wNum m) * wDen nOdd) := by ac_rfl
        _ ≤ (p_L ^ (6 * s + 2) * q_T ^ (2 * s)) *
              ((C_hi * (q_L ^ (6 * s + 3) * p_T ^ (6 * s + 2)) * wDen m) * wDen nOdd) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hhi_m)
    have hcanc := nat_mul_le_cancel_left_w5 F_c _ _ hF_pos hcomb
    have h1 : 1 * q_T ^ D_e ≤ (c_0 * p_L) * q_T ^ D_e := Nat.mul_le_mul_right _ (Nat.mul_le_mul hc0 hpL)
    rw [Nat.one_mul] at h1
    have hq_De : q_T ^ D_e ≤ K_0 * p_T ^ D_e :=
      Nat.le_trans (Nat.le_trans h1 hcanc) (Nat.mul_le_mul_right _ (by dsimp [K_0]; omega))
    let E_ex := D_e - e
    have he_sp : e + E_ex = D_e := by dsimp [E_ex, D_e, s]; omega
    have hq_e : q_T ^ e ≤ K_0 * p_T ^ e := by
      have hm1 : p_T ^ E_ex * q_T ^ e ≤ p_T ^ E_ex * (K_0 * p_T ^ e) := by
        calc p_T ^ E_ex * q_T ^ e
            ≤ q_T ^ E_ex * q_T ^ e := Nat.mul_le_mul_right _ (pow_mono_base_w15s p_T q_T (Nat.le_of_lt hpen) E_ex)
          _ = q_T ^ D_e := by rw [← he_sp, Nat.pow_add q_T e E_ex, Nat.mul_comm]
          _ ≤ K_0 * p_T ^ D_e := hq_De
          _ = p_T ^ E_ex * (K_0 * p_T ^ e) := by rw [← he_sp, Nat.pow_add p_T e E_ex]; ac_rfl
      exact nat_mul_le_cancel_left_w5 (p_T ^ E_ex) _ _ (nat_pow_pos_of_pos p_T hpT E_ex) hm1
    have hgt_pow := pow_gt_const_mul_pow_of_lt_w15s p_T q_T K_0 hpT hpen
    dsimp only [e] at hq_e hgt_pow; omega
  · -- Case 3 (`p_T = q_T`): reduces to pure-bitlength two-sided ratio pincer!
    subst heq
    apply eventual_pure_bitlength_twosided_ratio_impossibility_w15 M_0 hM0
      wNum wDen c_0 C_hi p_L q_L pTheta qTheta hc0 hpL hqL
    intro n hn
    rcases hsand n hn with ⟨hlo, hhi⟩
    let T := binaryAltTransitions n
    have hp_pos : p_T ^ T > 0 := nat_pow_pos_of_pos p_T hpT T
    refine ⟨nat_mul_le_cancel_right_w5 (p_T ^ T) _ _ hp_pos ?_,
            nat_mul_le_cancel_right_w5 (p_T ^ T) _ _ hp_pos ?_⟩
    · calc (c_0 * q_L ^ binBitLength n * wDen n) * p_T ^ T
          = c_0 * (q_L ^ binBitLength n * p_T ^ T) * wDen n := by ac_rfl
        _ ≤ (p_L ^ binBitLength n * p_T ^ T) * wNum n := hlo
        _ = (p_L ^ binBitLength n * wNum n) * p_T ^ T := by ac_rfl
    · calc (p_L ^ binBitLength n * wNum n) * p_T ^ T
          = (p_L ^ binBitLength n * p_T ^ T) * wNum n := by ac_rfl
        _ ≤ C_hi * (q_L ^ binBitLength n * p_T ^ T) * wDen n := hhi
        _ = (C_hi * q_L ^ binBitLength n * wDen n) * p_T ^ T := by ac_rfl

-- ============================================================================
-- SECTION 2: Front C Part 2 (Branch P5.14) — 12th Solvable `(3x + 1)`-Cousin
--            `T_diamond12` with Genuine 10-Tier `ω^10` Cascade
--            (`Cone 13 -> Cone 12 -> ... -> Cone 5 -> Φ_diamond2`, `W15_H3`)
-- ============================================================================

/-- Cone 13 of `T_diamond12`: `18664651 + x = 2 ^ a * 3 ^ b` with `a ≥ 39, b ≥ 1`
    (starting at `x = 2 ^ 39 * 3 - 18664651 = 1649248777013`). -/
def isDiamond12Cone13 (x : Nat) : Prop :=
  x ≥ 1649248777013 ∧ x % 549755813888 = 549737149237 ∧ x % 3 = 2 ∧ coprime23Core (18664651 + x) = 1

instance (x : Nat) : Decidable (isDiamond12Cone13 x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/--
  12th solvable mixed-(2, 3) Collatz cousin `T_diamond12` on `Nat`:
  Extends `T_diamond11` by adding Cone 13 (`isDiamond12Cone13 x -> (3 * x + 1) / 32`, a genuine
  `v_2(3x + 1) = 5` Syracuse jump that steps `2 ^ a * 3 ^ b - 18664651 -> 2 ^ (a - 5) * 3 ^ (b + 1) - 1749811`
  directly into Cone 12 -> Cone 11 -> ... -> Cone 5 -> `Φ_diamond2`, e.g. `9895585985333 -> 927711186125`
  in `22` steps to `1`, jumping `cousinDiamond2Phi` upward `+16.22x` and defeating 9-tier `ω^9` rankings)!
-/
def cousinDiamond12Step (x : Nat) : Nat :=
  if isDiamond12Cone13 x then (3 * x + 1) / 32 else cousinDiamond11Step x

def cousinDiamond12Iter : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamond12Iter k (cousinDiamond12Step x)

private theorem cousinDiamond12Iter_add : ∀ (a b x : Nat),
    cousinDiamond12Iter (a + b) x = cousinDiamond12Iter b (cousinDiamond12Iter a x)
  | 0, _, _ => by simp [cousinDiamond12Iter]
  | a + 1, b, x => by
    rw [Nat.succ_add]
    exact cousinDiamond12Iter_add a b (cousinDiamond12Step x)

/-- Signed extension of `T_diamond12` (`q = 3`) to `Int` for `M2 = Z^-` separation. -/
def cousinDiamond12StepInt (x : Int) : Int :=
  if x ≥ 1649248777013 ∧ x % 549755813888 = 549737149237 ∧ x % 3 = 2 ∧ coprime23Core (18664651 + x.toNat) = 1
  then (3 * x + 1) / 32
  else cousinDiamond11StepInt x

def cousinDiamond12IterInt : Nat -> Int -> Int
  | 0, x => x
  | k + 1, x => cousinDiamond12IterInt k (cousinDiamond12StepInt x)

/-- Hensel lift of `invMod17179869184Odd` (`2^34`) to `mod 137438953472` (`2^37`, `34 * 2 = 68 ≥ 37`). -/
def invMod137438953472Odd (d : Nat) : Nat :=
  let i17 := invMod17179869184Odd d
  (i17 * (274877906946 - ((d % 137438953472) * i17) % 137438953472)) % 137438953472

/-- Hensel lift of `invMod17179869184Odd` (`2^34`) to `mod 549755813888` (`2^39`, `34 * 2 = 68 ≥ 39`). -/
def invMod549755813888Odd (d : Nat) : Nat :=
  let i17 := invMod17179869184Odd d
  (i17 * (1099511627778 - ((d % 549755813888) * i17) % 549755813888)) % 549755813888

/-- Canonical reduced-pair extension of `T_diamond12` (`q = 3`) to positive `Q_(6)^+`. -/
def cousinDiamond12StepQ6 (p : Nat × Nat) : Nat × Nat :=
  let num := p.1
  let den := p.2
  let r549b := (num * invMod549755813888Odd den) % 549755813888
  let r3 := (num * (den % 3)) % 3
  if num ≥ 1649248777013 * den ∧ r549b = 549737149237 ∧ r3 = 2 ∧ core3 (core2 (18664651 * den + num)) = den
  then reduceRatPair (3 * num + den) (32 * den)
  else cousinDiamond11StepQ6 p

def cousinDiamond12IterQ6 : Nat -> (Nat × Nat) -> (Nat × Nat)
  | 0, p => p
  | k + 1, p => cousinDiamond12IterQ6 k (cousinDiamond12StepQ6 p)

/-- Generalized odd-multiplier `q` step of `T_diamond12` on `Nat` for `M3` (`q = 7`) separation. -/
def cousinDiamond12StepParam (q x : Nat) : Nat :=
  if isDiamond12Cone13 x then (q * x + 1) / 32 else cousinDiamond11StepParam q x

def cousinDiamond12IterParam (q : Nat) : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamond12IterParam q k (cousinDiamond12StepParam q x)

private theorem hensel_inv_lift_w15 (M1 M2 S C d i1 : Nat)
    (hM2 : M2 ≥ 2) (hsq : M1 * M1 = M2 * S) (hC : C = 2 * M2 + 2)
    (h1 : (d * i1) % M1 = 1) :
    (d * ((i1 * (C - ((d % M2) * i1) % M2)) % M2)) % M2 = 1 := by
  let x := d * i1
  let r := ((d % M2) * i1) % M2
  have hr_lt : r < M2 := Nat.mod_lt _ (by omega)
  let K := (d / M2) * i1 + ((d % M2) * i1) / M2
  have hx_M2 : x = M2 * K + r := by
    have hd_div : d = M2 * (d / M2) + d % M2 := (Nat.div_add_mod d M2).symm
    have hdr_div : (d % M2) * i1 = M2 * (((d % M2) * i1) / M2) + r :=
      (Nat.div_add_mod ((d % M2) * i1) M2).symm
    calc x = (M2 * (d / M2) + d % M2) * i1 := by dsimp [x]; rw [← hd_div]
      _ = M2 * ((d / M2) * i1) + (M2 * (((d % M2) * i1) / M2) + r) := by
            rw [Nat.add_mul, Nat.mul_assoc, ← hdr_div]
      _ = M2 * K + r := by dsimp [K]; rw [Nat.mul_add]; omega
  let q1 := x / M1
  have hx_M1 : x = M1 * q1 + 1 := by
    have hdm := (Nat.div_add_mod x M1).symm
    dsimp [x] at hdm ⊢; rw [h1] at hdm; exact hdm
  have hsq_x : (M1 * q1) * (M1 * q1) + 2 * x = x * x + 1 := by
    rw [hx_M1]
    calc (M1 * q1) * (M1 * q1) + 2 * (M1 * q1 + 1)
        = (M1 * q1) * (M1 * q1) + (M1 * q1) + (M1 * q1 + 1) + 1 := by omega
      _ = (M1 * q1 + 1) * (M1 * q1 + 1) + 1 := by
            rw [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  have hmain : x * (C - r) + M2 * (S * (q1 * q1)) = M2 * (x * (2 + K)) + 1 := by
    have hlhs1 : (M1 * q1) * (M1 * q1) = M2 * (S * (q1 * q1)) := by
      calc (M1 * q1) * (M1 * q1) = (M1 * M1) * (q1 * q1) := by ac_rfl
        _ = (M2 * S) * (q1 * q1) := by rw [hsq]
        _ = M2 * (S * (q1 * q1)) := by ac_rfl
    have hsplit_c : C - r = (2 * M2 - r) + 2 := by omega
    calc x * (C - r) + M2 * (S * (q1 * q1))
        = x * (2 * M2 - r) + (x * 2 + (M1 * q1) * (M1 * q1)) := by
            rw [hsplit_c, Nat.mul_add, ← hlhs1, Nat.add_assoc]
      _ = x * (2 * M2 - r) + (x * x + 1) := by rw [Nat.mul_comm x 2, Nat.add_comm (2 * x), hsq_x]
      _ = x * ((2 * M2 - r) + (M2 * K + r)) + 1 := by
            conv => lhs; rhs; lhs; rhs; rw [hx_M2]
            rw [← Nat.add_assoc, ← Nat.mul_add]
      _ = x * (M2 * (2 + K)) + 1 := by
            rw [show (2 * M2 - r) + (M2 * K + r) = 2 * M2 + M2 * K by omega,
                Nat.mul_add M2 2 K, Nat.mul_comm M2 2]
      _ = M2 * (x * (2 + K)) + 1 := by ac_rfl
  have hle_q : S * (q1 * q1) ≤ x * (2 + K) := by
    by_cases hle : S * (q1 * q1) ≤ x * (2 + K)
    · exact hle
    · exfalso
      have hm := Nat.mul_le_mul_left M2 (by omega : x * (2 + K) + 1 ≤ S * (q1 * q1))
      rw [Nat.mul_add, Nat.mul_one] at hm; omega
  have hx_mod : (x * (C - r)) % M2 = 1 := by
    have hm_sub : M2 * (x * (2 + K) - S * (q1 * q1)) + M2 * (S * (q1 * q1)) = M2 * (x * (2 + K)) := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hle_q]
    have heq : x * (C - r) = M2 * (x * (2 + K) - S * (q1 * q1)) + 1 := by
      generalize x * (C - r) = A, M2 * (S * (q1 * q1)) = B,
        M2 * (x * (2 + K)) = E, M2 * (x * (2 + K) - S * (q1 * q1)) = F at hmain hm_sub ⊢
      omega
    rw [heq, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hM2]
  let Y := i1 * (C - r)
  have hdY_mod : (d * Y) % M2 = (d * (Y % M2)) % M2 := by
    have hdY : d * Y = M2 * (d * (Y / M2)) + d * (Y % M2) := by
      conv => lhs; rhs; rw [(Nat.div_add_mod Y M2).symm]
      rw [Nat.mul_add, ← Nat.mul_assoc d M2, Nat.mul_comm d M2, Nat.mul_assoc M2 d]
    rw [hdY, Nat.add_comm (M2 * (d * (Y / M2))), Nat.add_mul_mod_self_left]
  have hdY_eq : d * Y = x * (C - r) := by dsimp [x, Y]; ac_rfl
  dsimp only [Y] at hdY_mod
  rw [← hdY_mod, hdY_eq, hx_mod]

private theorem core3_core2_eq_coprime23Core_w15 :
    ∀ (fuel n : Nat), n > 0 -> n ≤ fuel -> core3 (core2 n) = coprime23Core n
  | 0, _, hn, hle => by omega
  | fuel + 1, n, hn, hle => by
    by_cases hev : n % 2 = 0
    · let k := n / 2
      have hk_pos : k > 0 := by dsimp [k]; omega
      rw [show n = 2 * k by dsimp [k]; omega, core2_mul2 k hk_pos, coprime23Core_mul2 k hk_pos]
      exact core3_core2_eq_coprime23Core_w15 fuel k hk_pos (by dsimp [k]; omega)
    · have hodd : n % 2 = 1 := by omega
      rcases core3_decomp n hn with ⟨_, _, _, _, hmul⟩
      have hc3_odd : core3 n % 2 = 1 := by
        by_cases hc3_ev : core3 n % 2 = 0
        · have hm0 : (v3Pow n * core3 n) % 2 = 0 := by rw [Nat.mul_mod, hc3_ev, Nat.mul_zero]
          rw [hmul] at hm0; omega
        · omega
      unfold coprime23Core
      rw [core2_of_odd n hodd, core2_of_odd (core3 n) hc3_odd]

private theorem reduceRatPair_div_exact_w15 (a m : Nat) (hm : m > 0) (hdvd : m ∣ a) :
    reduceRatPair a m = (a / m, 1) := by
  rcases hdvd with ⟨q, rfl⟩
  unfold reduceRatPair
  have hgcd : Nat.gcd (m * q) m = m :=
    Nat.dvd_antisymm (Nat.gcd_dvd_right (m * q) m) (Nat.dvd_gcd ⟨q, rfl⟩ (Nat.dvd_refl m))
  dsimp only
  rw [hgcd, Nat.div_self hm]

private theorem dvd_three_mul_add_one_of_mod_w15 (x M D Qm Qr R Qt : Nat)
    (hM : M = D * Qm) (hmod : x % M = D * Qr + R) (h3 : 3 * R + 1 = D * Qt) :
    D ∣ (3 * x + 1) := by
  refine ⟨3 * (Qm * (x / M) + Qr) + Qt, ?_⟩
  have hdiv : M * (x / M) + x % M = x := Nat.div_add_mod x M
  calc 3 * x + 1 = 3 * (M * (x / M) + x % M) + 1 := by rw [hdiv]
    _ = 3 * ((D * Qm) * (x / M) + (D * Qr + R)) + 1 := by rw [← hM, ← hmod]
    _ = D * (3 * (Qm * (x / M) + Qr)) + (3 * R + 1) := by
          rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add]; ac_rfl
    _ = D * (3 * (Qm * (x / M) + Qr) + Qt) := by rw [h3, ← Nat.mul_add]

/--
  Theorem W15.3i (`cousin_diamond12_q6_noninteger_avoids_cone13`,
  choice-free `zero custom axioms`):
  Universal Non-Integer Rational Exclusion from Cone 13 on `M1 = Q_(6)^+`:
  For EVERY reduced non-integer rational `(num, den)` (`Nat.gcd num den = 1` and `den > 1`),
  `core3 (core2 (18664651 * den + num)) ≠ den`, so `cousinDiamond12StepQ6 (num, den)` NEVER enters
  Cone 13 and agrees identically with `cousinDiamond11StepQ6 (num, den)` (`Branch P5.14`, `W15_H3`).
-/
theorem cousin_diamond12_q6_noninteger_avoids_cone13 (num den : Nat)
    (hgcd : Nat.gcd num den = 1) (hden : den > 1) :
    core3 (core2 (18664651 * den + num)) ≠ den ∧
    cousinDiamond12StepQ6 (num, den) = cousinDiamond11StepQ6 (num, den) := by
  have hne : core3 (core2 (18664651 * den + num)) ≠ den := by
    intro heq
    have hdvd_sum : den ∣ (18664651 * den + num) := by
      have hc_dvd : core3 (core2 (18664651 * den + num)) ∣ (18664651 * den + num) :=
        Nat.dvd_trans (core3Aux_dvd_w8 _ _) (core2Aux_dvd_w8 _ _)
      rwa [heq] at hc_dvd
    rcases hdvd_sum with ⟨k, hk⟩
    have hdvd_num : den ∣ num := ⟨k - 18664651, by
      have hge : k ≥ 18664651 := by
        by_cases hlt : k < 18664651
        · have hm := Nat.mul_le_mul_left den (show k ≤ 18664650 by omega); omega
        · omega
      rw [Nat.mul_sub_left_distrib]; omega⟩
    have hdvd_gcd : den ∣ Nat.gcd num den := Nat.dvd_gcd hdvd_num (Nat.dvd_refl den)
    rw [hgcd] at hdvd_gcd
    rcases hdvd_gcd with ⟨c, hc⟩
    cases c with
    | zero => omega
    | succ c' =>
      have hle := Nat.mul_le_mul_left den (show 1 ≤ c' + 1 by omega); omega
  refine ⟨hne, ?_⟩
  unfold cousinDiamond12StepQ6
  have hcond : ¬ (num ≥ 1649248777013 * den ∧ (num * invMod549755813888Odd den) % 549755813888 = 549737149237 ∧
      (num * (den % 3)) % 3 = 2 ∧ core3 (core2 (18664651 * den + num)) = den) :=
    fun ⟨_, _, _, hc⟩ => hne hc
  simp only [hcond, ite_false]

/--
  Theorem W15.3c (`cousin_diamond12_hensel_inv_and_nat_int_q6_agreement`,
  `zero custom axioms`):
  Universal Newton–Hensel `mod 2^37` & `mod 2^39` Odd-Inverse Correctness, Exact `Nat`/`Int`/`Q_(6)^+`
  Step Agreement, & Universal Non-Integer Rational Exclusion from Cone 13 on `M1 = Q_(6)^+`
  (`Branch P5.14`, `W15_H3`).
-/
theorem cousin_diamond12_hensel_inv_and_nat_int_q6_agreement :
    (∀ d : Nat, d % 2 = 1 -> (d * invMod137438953472Odd d) % 137438953472 = 1) ∧
    (∀ d : Nat, d % 2 = 1 -> (d * invMod549755813888Odd d) % 549755813888 = 1) ∧
    (∀ x : Nat, cousinDiamond12StepInt (x : Int) = (cousinDiamond12Step x : Int)) ∧
    (∀ x : Nat, cousinDiamond12StepQ6 (x, 1) = (cousinDiamond12Step x, 1)) ∧
    (∀ num den : Nat, Nat.gcd num den = 1 -> den > 1 ->
      core3 (core2 (18664651 * den + num)) ≠ den ∧
      cousinDiamond12StepQ6 (num, den) = cousinDiamond11StepQ6 (num, den)) := by
  rcases invMod17179869184Odd_mul_and_q6_nat_agreement with ⟨hinv17, hd11_q6⟩
  have hinv37 : ∀ d : Nat, d % 2 = 1 -> (d * invMod137438953472Odd d) % 137438953472 = 1 := by
    intro d hodd
    exact hensel_inv_lift_w15 17179869184 137438953472 2147483648 274877906946 d (invMod17179869184Odd d)
      (by decide) (by decide) (by decide) (hinv17 d hodd)
  have hinv39 : ∀ d : Nat, d % 2 = 1 -> (d * invMod549755813888Odd d) % 549755813888 = 1 := by
    intro d hodd
    exact hensel_inv_lift_w15 17179869184 549755813888 536870912 1099511627778 d (invMod17179869184Odd d)
      (by decide) (by decide) (by decide) (hinv17 d hodd)
  refine ⟨hinv37, hinv39, ?_, ?_, cousin_diamond12_q6_noninteger_avoids_cone13⟩
  · intro x
    have h1 : ((x : Int) ≥ 1649248777013) ↔ (x ≥ 1649248777013) := by omega
    have h2 : ((x : Int) % 549755813888 = 549737149237) ↔ (x % 549755813888 = 549737149237) :=
      ⟨Int.ofNat.inj, congrArg Int.ofNat⟩
    have h3 : ((x : Int) % 3 = 2) ↔ (x % 3 = 2) := ⟨Int.ofNat.inj, congrArg Int.ofNat⟩
    have hdiv : ((3 * (x : Int) + 1) / 32) = (((3 * x + 1) / 32 : Nat) : Int) := by omega
    have htoNat : (x : Int).toNat = x := rfl
    unfold cousinDiamond12StepInt cousinDiamond12Step isDiamond12Cone13
    rw [htoNat]; simp only [h1, h2, h3]
    by_cases hc13 : x ≥ 1649248777013 ∧ x % 549755813888 = 549737149237 ∧ x % 3 = 2 ∧ coprime23Core (18664651 + x) = 1
    · simp only [hc13, and_self, ite_true, hdiv]
    · simp only [hc13, ite_false]; exact cousinDiamond11StepInt_ofNat_eq x
  · have hi39 : invMod549755813888Odd 1 = 1 := by decide
    have hm3_1 : (1 : Nat) % 3 = 1 := by decide
    intro x
    have hcc : core3 (core2 (18664651 + x)) = coprime23Core (18664651 + x) :=
      core3_core2_eq_coprime23Core_w15 (18664651 + x) (18664651 + x) (by omega) (Nat.le_refl _)
    unfold cousinDiamond12StepQ6 cousinDiamond12Step isDiamond12Cone13
    simp only [hi39, hm3_1, Nat.mul_one, hcc]
    by_cases hc13 : x ≥ 1649248777013 ∧ x % 549755813888 = 549737149237 ∧ x % 3 = 2 ∧ coprime23Core (18664651 + x) = 1
    · simp only [hc13, and_self, ite_true]
      exact reduceRatPair_div_exact_w15 (3 * x + 1) 32 (by decide)
        (dvd_three_mul_add_one_of_mod_w15 x 549755813888 32 17179869184 17179285913 21 2
          (by decide) hc13.2.1 (by decide))
    · simp only [hc13, ite_false]; exact hd11_q6 x

private theorem cousinDiamond12Step_pos (x : Nat) (hx : x > 0) : cousinDiamond12Step x > 0 := by
  unfold cousinDiamond12Step
  by_cases hc13 : isDiamond12Cone13 x
  · simp only [hc13, ite_true]
    have hge : x ≥ 1649248777013 := hc13.1
    clear hc13
    exact Nat.lt_of_lt_of_le (by decide : 0 < (3 * 1649248777013 + 1) / 32)
      (Nat.div_le_div_right (by omega))
  · simp only [hc13, ite_false]; exact cousinDiamond11Step_pos x hx

private theorem d12_eq_d11_of_not_cone13 (x : Nat) (hnc13 : ¬ isDiamond12Cone13 x) :
    cousinDiamond12Step x = cousinDiamond11Step x := by
  unfold cousinDiamond12Step; simp [hnc13]

-- Modular Cone-13 avoidance helpers (`549737149237 % 64 = 53, % 32 = 21, % 8 = 5, % 4 = 1`):

private theorem mod64_of_cone13 (z : Nat) (hc13 : isDiamond12Cone13 z) : z % 64 = 53 := by
  have h := congrArg (· % 64) hc13.2.1
  rw [Nat.mod_mod_of_dvd z (by decide : 64 ∣ 549755813888),
      show 549737149237 % 64 = 53 by decide] at h
  exact h

private theorem mod32_of_cone13 (z : Nat) (hc13 : isDiamond12Cone13 z) : z % 32 = 21 := by
  have h := congrArg (· % 32) (mod64_of_cone13 z hc13)
  rw [Nat.mod_mod_of_dvd z (by decide : 32 ∣ 64), show 53 % 32 = 21 by decide] at h
  exact h

private theorem not_cone13_of_even (z : Nat) (hev : z % 2 = 0) : ¬ isDiamond12Cone13 z := by
  intro hc13
  have h := congrArg (· % 2) (mod32_of_cone13 z hc13)
  rw [Nat.mod_mod_of_dvd z (by decide : 2 ∣ 32), hev] at h
  cases h

private theorem not_cone13_of_mod4_eq_3 (z : Nat) (hm4 : z % 4 = 3) : ¬ isDiamond12Cone13 z := by
  intro hc13
  have h := congrArg (· % 4) (mod32_of_cone13 z hc13)
  rw [Nat.mod_mod_of_dvd z (by decide : 4 ∣ 32), hm4] at h
  cases h

private theorem not_cone13_of_mod8_ne_5 (z : Nat) (hm8 : z % 8 ≠ 5) : ¬ isDiamond12Cone13 z := by
  intro hc13
  have h := congrArg (· % 8) (mod32_of_cone13 z hc13)
  rw [Nat.mod_mod_of_dvd z (by decide : 8 ∣ 32)] at h
  exact hm8 h

private theorem not_cone13_of_mod32_ne_21 (z : Nat) (hm32 : z % 32 ≠ 21) : ¬ isDiamond12Cone13 z :=
  fun hc13 => hm32 (mod32_of_cone13 z hc13)

private theorem not_cone13_of_mod64_ne_53 (z : Nat) (hm64 : z % 64 ≠ 53) : ¬ isDiamond12Cone13 z :=
  fun hc13 => hm64 (mod64_of_cone13 z hc13)

private theorem not_cone13_of_mod3_ne_2 (z : Nat) (hm3 : z % 3 ≠ 2) : ¬ isDiamond12Cone13 z :=
  fun ⟨_, _, h3, _⟩ => hm3 h3

private theorem not_cone13_six_mul_pow9_sub1_w15 (m : Nat) :
    ¬ isDiamond12Cone13 (6 * 9 ^ m - 1) := by
  cases m with
  | zero => rintro ⟨hge, _, _, _⟩; simp at hge
  | succ m1 =>
    cases m1 with
    | zero => rintro ⟨hge, _, _, _⟩; simp at hge
    | succ n =>
      have h9_63 : ∀ t : Nat, 9 ^ (t + 1) % 63 = 9 ∨ 9 ^ (t + 1) % 63 = 18 ∨ 9 ^ (t + 1) % 63 = 36 := by
        intro t; induction t with
        | zero => exact Or.inl rfl
        | succ t' ih =>
          rw [Nat.pow_succ 9 (t' + 1), Nat.mul_mod]
          rcases ih with h | h | h <;> (rw [h]; decide)
      have h2_63 : ∀ t : Nat,
          2 ^ t % 63 = 1 ∨ 2 ^ t % 63 = 2 ∨ 2 ^ t % 63 = 4 ∨
          2 ^ t % 63 = 8 ∨ 2 ^ t % 63 = 16 ∨ 2 ^ t % 63 = 32 := by
        intro t; induction t with
        | zero => exact Or.inl rfl
        | succ t' ih =>
          rw [Nat.pow_succ 2 t', Nat.mul_mod]
          rcases ih with h | h | h | h | h | h <;> (rw [h]; decide)
      rcases (⟨9 ^ (n + 1), rfl⟩ : ∃ p9 : Nat, p9 = 9 ^ (n + 1)) with ⟨P9, hP9_def⟩
      have hp9_pos : P9 ≥ 1 := by rw [hP9_def]; exact nat_pow_pos_of_pos 9 (by decide) (n + 1)
      have hp9_next : 6 * 9 ^ (n + 2) = 54 * P9 := by
        rw [Nat.pow_succ 9 (n + 1), ← hP9_def]; omega
      rcases (⟨6 * P9 + 2073850, rfl⟩ : ∃ a0 : Nat, a0 = 6 * P9 + 2073850) with ⟨A, hA_def⟩
      have hsum_eq : 18664651 + (6 * 9 ^ (n + 2) - 1) = 9 * A := by
        rw [hp9_next, hA_def]; omega
      have hN_pos : 9 * A > 0 := by rw [hA_def]; omega
      have hA_m3 : A % 3 = 1 := by rw [hA_def]; omega
      have hA_63 : A % 63 = 7 ∨ A % 63 = 43 ∨ A % 63 = 61 := by
        rw [hA_def, hP9_def]
        have hdm := (Nat.div_add_mod (9 ^ (n + 1)) 63).symm
        rcases h9_63 n with h | h | h <;> clear h9_63 h2_63 hp9_next hsum_eq hN_pos hA_m3 <;> omega
      rintro ⟨hc_ge, hc_39, hc_3, hcop⟩
      clear hc_ge hc_39 hc_3
      rw [hsum_eq] at hcop
      rcases decomp_2_3_exact (9 * A) hN_pos with ⟨hd1, hd2, hd3, hd4, hd5, hmul⟩
      clear hd1 hd2 hd3 hd4 hd5
      rw [hcop, Nat.mul_one] at hmul
      rcases eq_pow2_of_v2Pow_aux (9 * A) (9 * A) hN_pos (Nat.le_refl _) with ⟨k, hk⟩
      rcases eq_pow3_of_v3Pow_aux (9 * A) (9 * A) hN_pos (Nat.le_refl _) with ⟨r, hr⟩
      rw [hk, hr] at hmul
      clear hcop hsum_eq hp9_next hk hr hA_def hP9_def hp9_pos hN_pos h9_63
      have hr2 : r = 2 := by
        by_cases hlt : r < 2
        · exfalso
          have hm9 := pow2_mod3_nonzero_w5 k
          rcases (by clear h2_63 hA_63 hmul hm9; omega : r = 0 ∨ r = 1) with rfl | rfl
          · rw [Nat.pow_zero, Nat.mul_one] at hmul
            exact hm9 (by clear h2_63 hA_63 hm9; omega)
          · rw [Nat.pow_one] at hmul
            have h3A : 2 ^ k = 3 * A := by clear h2_63 hA_63 hm9; omega
            exact hm9 (by rw [h3A]; clear h2_63 hA_63 hmul h3A hm9; omega)
        · by_cases hgt : r > 2
          · exfalso
            have hr_sp : 3 ^ r = 9 * (3 * 3 ^ (r - 3)) := by
              calc 3 ^ r = 3 ^ (3 + (r - 3)) := by congr 1; clear h2_63 hA_63 hmul; omega
                _ = 3 ^ 3 * 3 ^ (r - 3) := Nat.pow_add 3 3 (r - 3)
                _ = 9 * (3 * 3 ^ (r - 3)) := by clear h2_63 hA_63 hmul; omega
            have h9_pull : 2 ^ k * (9 * (3 * 3 ^ (r - 3))) = 9 * (3 * (2 ^ k * 3 ^ (r - 3))) := by ac_rfl
            rw [hr_sp, h9_pull] at hmul
            have hA_div3 : A = 3 * (2 ^ k * 3 ^ (r - 3)) :=
              Nat.eq_of_mul_eq_mul_left (by decide : 0 < 9) hmul.symm
            rw [hA_div3, Nat.mul_mod_right] at hA_m3
            cases hA_m3
          · clear h2_63 hA_63 hmul; omega
      rw [hr2] at hmul
      have hA_pow2 : A = 2 ^ k := by clear h2_63 hA_63 hr2; omega
      rw [hA_pow2] at hA_63
      rcases h2_63 k with h | h | h | h | h | h <;> clear h2_63 hmul hA_pow2 hr2 <;> omega

/--
  Theorem W15.3d (`cousin_diamond12_outside_cones4to13_descent_and_mod63_nonreentry`,
  `zero custom axioms`):
  Strict `cousinDiamond2Phi` Descent Outside Cones 4..13 & Universal `mod 63` Post-Climb
  Non-Reentry into Cone 13 (`∀ m : Nat, ¬ isDiamond12Cone13 (6 * 9 ^ m - 1)`,
  `Branch P5.14`, `W15_H3`).
-/
theorem cousin_diamond12_outside_cones4to13_descent_and_mod63_nonreentry :
    (∀ x : Nat, x > 2 ->
      ¬ isDiamond3Cone4 x -> ¬ isDiamond4Cone5 x ->
      ¬ isDiamond5Cone6 x -> ¬ isDiamond6Cone7 x ->
      ¬ isDiamond7Cone8 x -> ¬ isDiamond8Cone9 x ->
      ¬ isDiamond9Cone10 x -> ¬ isDiamond10Cone11 x ->
      ¬ isDiamond11Cone12 x -> ¬ isDiamond12Cone13 x ->
      cousinDiamond2Phi (cousinDiamond12Step x) < cousinDiamond2Phi x) ∧
    (∀ m : Nat, ¬ isDiamond12Cone13 (6 * 9 ^ m - 1)) := by
  refine ⟨?_, not_cone13_six_mul_pow9_sub1_w15⟩
  intro x hx hnc4 hnc5 hnc6 hnc7 hnc8 hnc9 hnc10 hnc11 hnc12 hnc13
  rw [d12_eq_d11_of_not_cone13 x hnc13]
  exact cousin_diamond11_outside_cones4to12_strict_descent x hx
    hnc4 hnc5 hnc6 hnc7 hnc8 hnc9 hnc10 hnc11 hnc12

private theorem isDiamond11Cone12_of_pow2_pow3_w15 (m n : Nat) (hm : m ≥ 34) (hn : n ≥ 1) :
    isDiamond11Cone12 (2 ^ m * 3 ^ n - 1749811) := by
  have hc : (2 : Nat) ^ 34 = 17179869184 := by decide
  have hp2_ge : 2 ^ m ≥ 17179869184 := by rw [← hc]; exact pow2_mono_nat hm
  have hp3_ge : 3 ^ n ≥ 3 := by simpa using nat_pow_mono_exp_pos 3 1 n (by decide) hn
  have hprod_ge : 2 ^ m * 3 ^ n ≥ 51539607552 := by simpa using Nat.mul_le_mul hp2_ge hp3_ge
  have hp17b : 17179869184 ∣ 2 ^ m * 3 ^ n := by
    rw [show m = 34 + (m - 34) by omega, Nat.pow_add 2 34 (m - 34), hc, Nat.mul_assoc]
    exact ⟨2 ^ (m - 34) * 3 ^ n, rfl⟩
  have hp3_div : 3 ∣ 2 ^ m * 3 ^ n := by
    rw [show n = 1 + (n - 1) by omega, Nat.pow_add 3 1 (n - 1), Nat.pow_one,
        ← Nat.mul_assoc (2 ^ m) 3, Nat.mul_comm (2 ^ m) 3, Nat.mul_assoc]
    exact ⟨2 ^ m * 3 ^ (n - 1), rfl⟩
  refine ⟨by clear hc hp2_ge hp3_ge hp17b hp3_div; generalize 2 ^ m * 3 ^ n = P at hprod_ge ⊢; omega,
          ?_, ?_, ?_⟩
  · rcases hp17b with ⟨k, hk⟩
    clear hc hp2_ge hp3_ge hp3_div
    generalize 2 ^ m * 3 ^ n = P at hprod_ge hk ⊢
    rw [hk, show k = (k - 1) + 1 by omega, Nat.mul_add 17179869184 (k - 1) 1, Nat.mul_one]
    generalize k - 1 = k'
    rw [show 17179869184 * k' + 17179869184 - 1749811 = 17178119373 + 17179869184 * k' by omega,
        Nat.add_mul_mod_self_left]
  · rcases hp3_div with ⟨k3, hk3⟩
    clear hc hp2_ge hp3_ge hp17b
    generalize 2 ^ m * 3 ^ n = P at hprod_ge hk3 ⊢; omega
  · rw [show 1749811 + (2 ^ m * 3 ^ n - 1749811) = 2 ^ m * 3 ^ n by
          clear hc hp2_ge hp3_ge hp17b hp3_div; generalize 2 ^ m * 3 ^ n = P at hprod_ge ⊢; omega]
    exact coprime23Core_pow2_pow3 m n

private theorem cousin_diamond12_mersenne_scaled :
    ∀ (k a q : Nat), k + 1 ≤ a -> q ≥ 1 ->
      cousinDiamond12Iter k (2 ^ a * q - 1) = 3 ^ k * 2 ^ (a - k) * q - 1
  | 0, _, _, _, _ => by simp [cousinDiamond12Iter]
  | k + 1, a, q, hka, hq => by
    have hp4 : 2 ^ a * q = 4 * (2 ^ (a - 2) * q) := by
      conv => lhs; rw [show a = (a - 2) + 2 by omega]
      rw [Nat.pow_add 2 (a - 2) 2, show (2 : Nat) ^ 2 = 4 from rfl,
          Nat.mul_comm (2 ^ (a - 2)) 4, Nat.mul_assoc]
    have hm_pos : 2 ^ (a - 2) * q ≥ 1 := Nat.mul_le_mul (pow2_pos_nat (a - 2)) hq
    simp only [cousinDiamond12Iter]
    rw [d12_eq_d11_of_not_cone13 _ (not_cone13_of_mod4_eq_3 _ (by omega))]
    have hd11 := cousin_diamond11_mersenne_scaled 1 a q (by omega) hq
    simp only [cousinDiamond11Iter, Nat.pow_one] at hd11
    rw [show cousinDiamond11Step (2 ^ a * q - 1) = 2 ^ (a - 1) * (3 * q) - 1 by
          rw [hd11]; apply congrArg (· - 1); ac_rfl,
        cousin_diamond12_mersenne_scaled k (a - 1) (3 * q) (by omega) (by omega),
        show a - 1 - k = a - (k + 1) by omega, Nat.pow_succ 3 k]
    apply congrArg (· - 1); ac_rfl

private theorem cousin_diamond12_even9_spine_drain :
    ∀ k : Nat, cousinDiamond12Iter k ((9 ^ (k + 1) - 1) / 4) = 2
  | 0 => rfl
  | k + 1 => by
    let j := k + 1
    have hp9j_ge9 : 9 ^ j ≥ 9 := by
      dsimp [j]; rw [Nat.pow_succ]; have hp := nat_pow_pos_of_pos 9 (by decide) k; omega
    have hp9j_m8 := pow9_mod8_eq_one_w5 j
    let q := (9 ^ j - 1) / 8
    have hp9j_eq : 9 ^ j = 8 * q + 1 := by dsimp [q]; omega
    have he_j1 : (9 ^ (j + 1) - 1) / 4 = 18 * q + 2 := by rw [Nat.pow_succ 9 j, hp9j_eq]; omega
    simp only [cousinDiamond12Iter]
    change cousinDiamond12Iter k (cousinDiamond12Step ((9 ^ (j + 1) - 1) / 4)) = 2
    rw [d12_eq_d11_of_not_cone13 _ (by rw [he_j1]; exact not_cone13_of_even _ (by omega))]
    -- Step `(9^(j+1)-1)/4 -> (9^j-1)/4` under `d11`:
    have hd11 : cousinDiamond11Step ((9 ^ (j + 1) - 1) / 4) = (9 ^ j - 1) / 4 := by
      have he_j : (9 ^ j - 1) / 4 = 2 * q := by rw [hp9j_eq]; omega
      rw [he_j1, he_j,
          cousinDiamond11Step_eq_d10_of_not_cone12 _ (not_cone12_of_even _ (by omega)),
          cousinDiamond10Step_eq_d9_of_not_cone11 _ (not_cone11_of_even _ (by omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (18 * q + 2) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]; unfold cousinDiamond3Step
      have hq_pos : q ≥ 1 := by dsimp [q]; omega
      have hodd_f : ¬ ((18 * q + 2) % 2 = 1) := by omega
      have h18_t : 18 * q + 2 ≥ 20 ∧ (18 * q + 2) % 18 = 2 := ⟨by omega, by omega⟩
      simp only [hodd_f, h18_t, and_self, ite_true, ite_false]; omega
    rw [hd11]
    exact cousin_diamond12_even9_spine_drain k

private theorem cousin_diamond12_pow3_sub1_drain :
    ∀ k : Nat, cousinDiamond12Iter k (3 ^ (k + 1) - 1) = 2
  | 0 => rfl
  | k + 1 => by
    let j := k + 1
    have hp3_ge3 : 3 ^ j ≥ 3 := by dsimp [j]; rw [Nat.pow_succ]; have := pow3_pos_nat k; omega
    have ho_j1 := pow3_odd_nat_sec8 (j + 1)
    have hp_j1 := pow3_pos_nat (j + 1)
    simp only [cousinDiamond12Iter]
    change cousinDiamond12Iter k (cousinDiamond12Step (3 ^ (j + 1) - 1)) = 2
    rw [d12_eq_d11_of_not_cone13 _ (not_cone13_of_even _ (by omega)),
        cousinDiamond11Step_eq_d10_of_not_cone12 _ (not_cone12_of_even _ (by omega)),
        cousinDiamond10Step_eq_d9_of_not_cone11 _ (not_cone11_of_even _ (by omega)),
        cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
        cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
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
      unfold cousinDiamond3Step; simp only [hev, hn18, hm6, and_self, ite_true, ite_false]
      rw [h3j1]; omega
    rw [hd4]
    exact cousin_diamond12_pow3_sub1_drain k

private theorem cousin_diamond12_cone5_two_step_climb :
    ∀ (q_c a b : Nat), 3 * q_c + 2 ≤ a -> b ≥ 1 ->
      cousinDiamond12Iter (2 * q_c) (2 ^ a * 3 ^ b - 7) =
        2 ^ (a - 3 * q_c) * 3 ^ (b + 2 * q_c) - 7
  | 0, _, _, _, _ => by simp [cousinDiamond12Iter]
  | q_c + 1, a, b, ha, hb => by
    have hc5 := isDiamond4Cone5_of_pow2_pow3 a b (by omega) hb
    let mid := 2 ^ (a - 2) * 3 ^ (b + 1) - 5
    have hmid_4 : mid % 4 = 3 := by
      dsimp [mid]
      have hp8 : 2 ^ (a - 2) = 8 * 2 ^ (a - 5) := by
        conv => lhs; rw [show a - 2 = 3 + (a - 5) by omega]; rw [Nat.pow_add]
      rw [hp8, Nat.mul_assoc 8]
      have := Nat.mul_le_mul (pow2_pos_nat (a - 5)) (pow3_pos_nat (b + 1)); omega
    have hd11_2 := cousin_diamond11_cone5_two_step_climb 1 a b (by omega) hb
    simp only [Nat.mul_one, cousinDiamond11Iter] at hd11_2
    have hd11_s1 : cousinDiamond11Step (2 ^ a * 3 ^ b - 7) = mid := by
      rw [cousinDiamond11Step_eq_d10_of_not_cone12 _ (not_cone12_of_mod32_ne_13 _ (by have := hc5.2.1; omega)),
          cousinDiamond10Step_eq_d9_of_not_cone11 _ (not_cone11_of_mod32_ne_13 _ (by have := hc5.2.1; omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_mod32_ne_13 _ (by have := hc5.2.1; omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_mod32_ne_13 _ (by have := hc5.2.1; omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_mod32_ne_21 _ (by have := hc5.2.1; omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_mod32_ne_21 _ (by have := hc5.2.1; omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_mod32_ne_13 _ (by have := hc5.2.1; omega))]
      unfold cousinDiamond4Step; simp only [hc5, ite_true]; dsimp [mid]
      have hp4 : 2 ^ a = 4 * 2 ^ (a - 2) := by
        conv => lhs; rw [show a = 2 + (a - 2) by omega]; rw [Nat.pow_add]
      have hp_pos : 2 ^ (a - 2) * 3 ^ b ≥ 24 := by
        have h1 : 8 ≤ 2 ^ (a - 2) := by rw [show (8 : Nat) = 2 ^ 3 from rfl]; exact pow2_mono_nat (by omega)
        have h2 : 3 ≤ 3 ^ b := by simpa using nat_pow_mono_exp_pos 3 1 b (by decide) hb
        simpa using Nat.mul_le_mul h1 h2
      rw [hp4, Nat.mul_assoc 4, show 2 ^ (a - 2) * 3 ^ (b + 1) = 3 * (2 ^ (a - 2) * 3 ^ b) by
            rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm _ 3]]
      generalize 2 ^ (a - 2) * 3 ^ b = A at hp_pos ⊢; omega
    rw [hd11_s1] at hd11_2
    have hs1 : cousinDiamond12Step (2 ^ a * 3 ^ b - 7) = mid := by
      rw [d12_eq_d11_of_not_cone13 _ (not_cone13_of_mod32_ne_21 _ (by have := hc5.2.1; omega))]
      exact hd11_s1
    have hs2 : cousinDiamond12Step mid = 2 ^ (a - 3) * 3 ^ (b + 2) - 7 := by
      rw [d12_eq_d11_of_not_cone13 _ (not_cone13_of_mod4_eq_3 _ hmid_4)]; exact hd11_2
    rw [Nat.mul_succ 2 q_c, Nat.add_comm (2 * q_c) 2, cousinDiamond12Iter_add 2 (2 * q_c)]
    have hi2 : cousinDiamond12Iter 2 (2 ^ a * 3 ^ b - 7) = 2 ^ (a - 3) * 3 ^ (b + 2) - 7 := by
      simp only [cousinDiamond12Iter, hs1, hs2]
    rw [hi2, cousin_diamond12_cone5_two_step_climb q_c (a - 3) (b + 2) (by omega) (by omega)]
    apply congrArg (· - 7); congr 1
    · apply congrArg (2 ^ ·); omega
    · apply congrArg (3 ^ ·); omega

private theorem cousin_diamond12_a0_3_drain (b0 : Nat) (hb0 : b0 ≥ 3) :
    cousinDiamond12Step (8 * 3 ^ b0 - 7) = 12 * 3 ^ b0 - 10 ∧
    cousinDiamond12Step (12 * 3 ^ b0 - 10) = 4 * 3 ^ b0 - 4 ∧
    cousinDiamond12Step (4 * 3 ^ b0 - 4) = 4 * 3 ^ (b0 - 1) - 2 ∧
    cousinDiamond12Iter ((b0 - 1) / 2 + 7) (8 * 3 ^ b0 - 7) = 1 := by
  rcases cousin_diamond11_a0_3_drain b0 hb0 with ⟨hd11_1, hd11_2, hd11_3, _⟩
  have hp3_ge27 : 3 ^ b0 ≥ 27 := by simpa using nat_pow_mono_exp_pos 3 3 b0 (by decide) hb0
  have hp3_b1_ge9 : 3 ^ (b0 - 1) ≥ 9 := by simpa using nat_pow_mono_exp_pos 3 2 (b0 - 1) (by decide) (by omega)
  have hs1 : cousinDiamond12Step (8 * 3 ^ b0 - 7) = 12 * 3 ^ b0 - 10 := by
    rw [d12_eq_d11_of_not_cone13 _ (not_cone13_of_mod32_ne_21 _ (by
          have ho := pow3_odd_nat_sec8 b0
          have hdm := (Nat.div_add_mod (3 ^ b0) 4).symm
          omega))]
    exact hd11_1
  have hs2 : cousinDiamond12Step (12 * 3 ^ b0 - 10) = 4 * 3 ^ b0 - 4 := by
    rw [d12_eq_d11_of_not_cone13 _ (not_cone13_of_even _ (by omega))]; exact hd11_2
  have hs3 : cousinDiamond12Step (4 * 3 ^ b0 - 4) = 4 * 3 ^ (b0 - 1) - 2 := by
    rw [d12_eq_d11_of_not_cone13 _ (not_cone13_of_even _ (by omega))]; exact hd11_3
  refine ⟨hs1, hs2, hs3, ?_⟩
  -- Helper: for any `z` not in Cones 5..13, `cousinDiamond12Step z = cousinDiamond3Step z`!
  have hd3_of_even : ∀ z : Nat, z % 2 = 0 -> cousinDiamond12Step z = cousinDiamond3Step z := by
    intro z hev
    rw [d12_eq_d11_of_not_cone13 z (not_cone13_of_even z hev),
        cousinDiamond11Step_eq_d10_of_not_cone12 z (not_cone12_of_even z hev),
        cousinDiamond10Step_eq_d9_of_not_cone11 z (not_cone11_of_even z hev),
        cousinDiamond9Step_eq_d8_of_not_cone10 z (not_cone10_of_even z hev),
        cousinDiamond8Step_eq_d7_of_not_cone9 z (not_cone9_of_even z hev),
        cousinDiamond7Step_eq_d6_of_not_cone8 z (not_cone8_of_even z hev),
        cousinDiamond6Step_eq_d5_of_not_cone7 z (not_cone7_of_even z hev),
        cousinDiamond5Step_eq_d4_of_not_cone6 z (not_cone6_of_even z hev),
        cousinDiamond4Step_eq_d3_of_not_cone5 z (by rintro ⟨_, h32, _, _⟩; omega)]
  by_cases hev_b1 : (b0 - 1) % 2 = 0
  · let m := (b0 - 1) / 2
    have hm1 : m ≥ 1 := by dsimp [m]; omega
    have hb1_eq : b0 - 1 = 2 * m := by dsimp [m]; omega
    have hp9_ge9 : 9 ^ m ≥ 9 := by rw [pow9_eq_pow3_double m, ← hb1_eq]; exact hp3_b1_ge9
    have hp9_m8 := pow9_mod8_eq_one_w5 m
    have h4_eq : 4 * 3 ^ (b0 - 1) - 2 = 4 * 9 ^ m - 2 := by rw [hb1_eq, ← pow9_eq_pow3_double m]
    let zr := 2 * 9 ^ m - 1
    let yr := (3 * 9 ^ m - 1) / 2
    have hs4 : cousinDiamond12Step (4 * 9 ^ m - 2) = zr := by
      rw [hd3_of_even _ (by omega)]
      have h9m9 : 9 ^ m % 9 = 0 := by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
      rw [cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) (by omega)]
      dsimp [zr]; omega
    have hsz : cousinDiamond12Step zr = yr := by
      rw [d12_eq_d11_of_not_cone13 zr (not_cone13_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          cousinDiamond11Step_eq_d10_of_not_cone12 zr (not_cone12_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          cousinDiamond10Step_eq_d9_of_not_cone11 zr (not_cone11_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 zr (not_cone10_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 zr (not_cone9_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 zr (not_cone8_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 zr (not_cone7_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 zr (not_cone6_of_mod16_ne_13 zr (by dsimp [zr]; omega)),
          cousinDiamond4Step_eq_d3_of_not_cone5 zr (by rintro ⟨_, h32, _, _⟩; dsimp [zr] at h32; omega)]
      have hc3 : core3 (zr + 1) = 2 := by
        rw [show zr + 1 = 2 * 9 ^ m by dsimp [zr]; omega, core3_mul2 (9 ^ m) (by omega), (pow9_eq_v3Pow_w5 m).2]
      rw [cousinDiamond3Step_of_core3_succ_two_w8 zr (by dsimp [zr]; omega) (by dsimp [zr]; omega) hc3]
      dsimp [zr, yr]; omega
    have hsy : cousinDiamond12Step yr = (9 ^ (m + 1) - 1) / 4 := by
      have hyr_m3 : yr % 3 = 1 := by
        have hm3 : 9 ^ m % 3 = 0 := by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
        dsimp [yr]; omega
      rw [d12_eq_d11_of_not_cone13 yr (not_cone13_of_mod3_ne_2 yr (by omega)),
          cousinDiamond11Step_eq_d10_of_not_cone12 yr (not_cone12_of_mod3_ne_2 yr (by omega)),
          cousinDiamond10Step_eq_d9_of_not_cone11 yr (not_cone11_of_mod3_ne_2 yr (by omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 yr (not_cone10_of_mod3_ne_2 yr (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 yr (not_cone9_of_mod3_ne_2 yr (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 yr (not_cone8_of_mod3_ne_2 yr (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 yr (not_cone7_of_mod9_ne_8 yr (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 yr (not_cone6_of_mod9_ne_8 yr (by omega)),
          cousinDiamond4Step_eq_d3_of_not_cone5 yr (by rintro ⟨_, _, hm3, _⟩; omega)]
      have hc3_2 : core3 (2 * yr + 1) = 1 := by
        rw [show 2 * yr + 1 = 3 * 9 ^ m by dsimp [yr]; omega, core3_mul3 (9 ^ m) (by omega), (pow9_eq_v3Pow_w5 m).2]
      have hc3_1 : core3 (yr + 1) ≠ 2 := by
        rw [core3_not_div3 (yr + 1) (by clear hd11_1 hd11_2 hd11_3 hs1 hs2 hs3 h4_eq hs4 hsz hc3_2 hd3_of_even; omega)]
        clear hd11_1 hd11_2 hd11_3 hs1 hs2 hs3 h4_eq hs4 hsz hc3_2 hd3_of_even; dsimp [yr]; omega
      have hnc4 : ¬ isDiamond3Cone4 yr := by
        rintro ⟨hge169, _, hc2⟩
        by_cases hm_eq1 : m = 1
        · clear hd11_1 hd11_2 hd11_3 hs1 hs2 hs3 h4_eq hs4 hsz hc3_2 hc3_1 hc2 hd3_of_even
          dsimp [yr] at hge169; rw [hm_eq1] at hge169; omega
        · rcases eq_pow2_of_core2_eq_one (3 * yr + 5)
            (by clear hd11_1 hd11_2 hd11_3 hs1 hs2 hs3 h4_eq hs4 hsz hc3_2 hc3_1 hd3_of_even; dsimp [yr]; omega) hc2 with
            ⟨M0, hM0⟩
          have h9_eq : 9 ^ (m + 1) + 7 = 2 ^ (M0 + 1) := by
            have h2mul : 2 * (3 * yr + 5) = 9 ^ (m + 1) + 7 := by
              clear hd11_1 hd11_2 hd11_3 hs1 hs2 hs3 h4_eq hs4 hsz hc3_2 hc3_1 hc2 hM0 hd3_of_even
              rw [Nat.pow_succ 9 m, Nat.mul_comm (9 ^ m) 9]; dsimp [yr]; omega
            rw [← h2mul, hM0, Nat.pow_succ 2 M0, Nat.mul_comm]
          exact pow9_succ_add_seven_ne_pow2 m (M0 + 1)
            (by clear hd11_1 hd11_2 hd11_3 hs1 hs2 hs3 h4_eq hs4 hsz hc3_2 hc3_1 hge169 hc2 hM0 h9_eq hd3_of_even; omega) h9_eq
      rw [cousinDiamond3Step_odd_half_w8 yr (by dsimp [yr]; omega) hnc4 hc3_2 hc3_1]
      dsimp [yr]; rw [Nat.pow_succ 9 m]; omega
    change cousinDiamond12Iter (m + 7) (8 * 3 ^ b0 - 7) = 1
    rw [show m + 7 = 4 + 1 + 1 + m + 1 by omega,
        cousinDiamond12Iter_add (4 + 1 + 1 + m) 1,
        cousinDiamond12Iter_add (4 + 1 + 1) m,
        cousinDiamond12Iter_add (4 + 1) 1,
        cousinDiamond12Iter_add 4 1]
    have hi4 : cousinDiamond12Iter 4 (8 * 3 ^ b0 - 7) = zr := by
      simp only [cousinDiamond12Iter, hs1, hs2, hs3, h4_eq, hs4]
    rw [hi4, show cousinDiamond12Iter 1 zr = yr from hsz,
        show cousinDiamond12Iter 1 yr = (9 ^ (m + 1) - 1) / 4 from hsy,
        cousin_diamond12_even9_spine_drain m]
    decide
  · let m := (b0 - 1) / 2
    have hm1 : m ≥ 1 := by dsimp [m]; omega
    have hb1_eq : b0 - 1 = 2 * m + 1 := by dsimp [m]; omega
    have hp9_ge9 : 9 ^ m ≥ 9 := by
      rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]
      have := nat_pow_pos_of_pos 9 (by decide) (m - 1); omega
    have hp9_m8 := pow9_mod8_eq_one_w5 m
    let ur := 6 * 9 ^ m - 1
    let wr := (9 ^ (m + 1) - 1) / 2
    have hu_eq : 4 * 3 ^ (b0 - 1) - 2 = 12 * 9 ^ m - 2 := by
      rw [hb1_eq, Nat.pow_succ 3 (2 * m), ← pow9_eq_pow3_double m]; omega
    have hs4 : cousinDiamond12Step (12 * 9 ^ m - 2) = ur := by
      rw [hd3_of_even _ (by omega)]
      have h9m9 : 9 ^ m % 9 = 0 := by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
      rw [cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) (by omega)]
      dsimp [ur]; omega
    have hsu : cousinDiamond12Step ur = wr := by
      rw [d12_eq_d11_of_not_cone13 ur (not_cone13_six_mul_pow9_sub1_w15 m),
          cousinDiamond11Step_eq_d10_of_not_cone12 ur (not_cone12_six_mul_pow9_sub1 m),
          cousinDiamond10Step_eq_d9_of_not_cone11 ur (not_cone11_six_mul_pow9_sub1 m),
          cousinDiamond9Step_eq_d8_of_not_cone10 ur (not_cone10_six_mul_pow9_sub1 m),
          cousinDiamond8Step_eq_d7_of_not_cone9 ur (not_cone9_six_mul_pow9_sub1 m),
          cousinDiamond7Step_eq_d6_of_not_cone8 ur (not_cone8_six_mul_pow9_sub1 m),
          cousinDiamond6Step_eq_d5_of_not_cone7 ur (not_cone7_six_mul_pow9_sub1 m),
          cousinDiamond5Step_eq_d4_of_not_cone6 ur (not_cone6_of_mod16_ne_13 ur (by dsimp [ur]; omega)),
          cousinDiamond4Step_eq_d3_of_not_cone5 ur (by rintro ⟨_, h32, _, _⟩; dsimp [ur] at h32; omega)]
      have hc3 : core3 (ur + 1) = 2 := by
        rw [show ur + 1 = 2 * (3 * 9 ^ m) by dsimp [ur]; omega,
            core3_mul2 (3 * 9 ^ m) (by omega), core3_mul3 (9 ^ m) (by omega), (pow9_eq_v3Pow_w5 m).2]
      rw [cousinDiamond3Step_of_core3_succ_two_w8 ur (by dsimp [ur]; omega) (by dsimp [ur]; omega) hc3]
      dsimp [ur, wr]; rw [Nat.pow_succ 9 m]; omega
    have hsw : cousinDiamond12Step wr = (9 ^ (m + 1) - 1) / 4 := by
      let q := (9 ^ m - 1) / 8
      have hq_pos : q ≥ 1 := by dsimp [q]; omega
      have hp9_eq : 9 ^ m = 8 * q + 1 := by dsimp [q]; omega
      have hwr_eq : wr = 36 * q + 4 := by dsimp [wr]; rw [Nat.pow_succ 9 m, hp9_eq]; omega
      have hnext_eq : (9 ^ (m + 1) - 1) / 4 = 18 * q + 2 := by rw [Nat.pow_succ 9 m, hp9_eq]; omega
      rw [hwr_eq, hnext_eq, hd3_of_even _ (by omega),
          cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) (by omega)]
      omega
    change cousinDiamond12Iter (m + 7) (8 * 3 ^ b0 - 7) = 1
    rw [show m + 7 = 4 + 1 + 1 + m + 1 by omega,
        cousinDiamond12Iter_add (4 + 1 + 1 + m) 1,
        cousinDiamond12Iter_add (4 + 1 + 1) m,
        cousinDiamond12Iter_add (4 + 1) 1,
        cousinDiamond12Iter_add 4 1]
    have hi4 : cousinDiamond12Iter 4 (8 * 3 ^ b0 - 7) = ur := by
      simp only [cousinDiamond12Iter, hs1, hs2, hs3, hu_eq, hs4]
    rw [hi4, show cousinDiamond12Iter 1 ur = wr from hsu,
        show cousinDiamond12Iter 1 wr = (9 ^ (m + 1) - 1) / 4 from hsw,
        cousin_diamond12_even9_spine_drain m]
    decide

private theorem cousin_diamond12_a0_2_and_4_drain (b0 : Nat) (hb0 : b0 ≥ 3) :
    cousinDiamond12Iter (b0 + 3) (4 * 3 ^ b0 - 7) = 1 ∧
    cousinDiamond12Iter ((b0 - 1) / 2 + 8) (16 * 3 ^ b0 - 7) = 1 := by
  have hp3_ge27 : 3 ^ b0 ≥ 27 := by simpa using nat_pow_mono_exp_pos 3 3 b0 (by decide) hb0
  have hp3_b1_ge9 : 3 ^ (b0 - 1) ≥ 9 := by simpa using nat_pow_mono_exp_pos 3 2 (b0 - 1) (by decide) (by omega)
  have hp3_b2_ge3 : 3 ^ (b0 - 2) ≥ 3 := by simpa using nat_pow_mono_exp_pos 3 1 (b0 - 2) (by decide) (by omega)
  have h3b0_sp : 3 ^ b0 = 3 * 3 ^ (b0 - 1) := by
    conv => lhs; rw [show b0 = 1 + (b0 - 1) by omega]; rw [Nat.pow_add, Nat.pow_one]
  have h3b1_sp : 3 ^ (b0 - 1) = 3 * 3 ^ (b0 - 2) := by
    conv => lhs; rw [show b0 - 1 = 1 + (b0 - 2) by omega]; rw [Nat.pow_add, Nat.pow_one]
  have h3b0_m9 : 3 ^ b0 % 9 = 0 := by rw [h3b0_sp, h3b1_sp]; omega
  have h3b0_m8 : 3 ^ b0 % 8 = 1 ∨ 3 ^ b0 % 8 = 3 := by
    by_cases hev : b0 % 2 = 0
    · left; rw [show b0 = 2 * (b0 / 2) by omega, ← pow9_eq_pow3_double]; exact pow9_mod8_eq_one_w5 _
    · right; rw [show b0 = 2 * (b0 / 2) + 1 by omega, Nat.pow_succ, ← pow9_eq_pow3_double, Nat.mul_mod, pow9_mod8_eq_one_w5]
  have hd3_of_even : ∀ z : Nat, z % 2 = 0 -> cousinDiamond12Step z = cousinDiamond3Step z := by
    intro z hev
    rw [d12_eq_d11_of_not_cone13 z (not_cone13_of_even z hev),
        cousinDiamond11Step_eq_d10_of_not_cone12 z (not_cone12_of_even z hev),
        cousinDiamond10Step_eq_d9_of_not_cone11 z (not_cone11_of_even z hev),
        cousinDiamond9Step_eq_d8_of_not_cone10 z (not_cone10_of_even z hev),
        cousinDiamond8Step_eq_d7_of_not_cone9 z (not_cone9_of_even z hev),
        cousinDiamond7Step_eq_d6_of_not_cone8 z (not_cone8_of_even z hev),
        cousinDiamond6Step_eq_d5_of_not_cone7 z (not_cone7_of_even z hev),
        cousinDiamond5Step_eq_d4_of_not_cone6 z (not_cone6_of_even z hev),
        cousinDiamond4Step_eq_d3_of_not_cone5 z (by rintro ⟨_, h32, _, _⟩; omega)]
  have hnc7_c : ∀ c : Nat, c ≥ 1 -> ¬ isDiamond6Cone7 (c * 3 ^ b0 - 7) := by
    intro c hc1; apply not_cone7_of_mod9_ne_8
    have hm : c * 3 ^ b0 ≥ 27 := by simpa using Nat.mul_le_mul hc1 hp3_ge27
    have hm9 : (c * 3 ^ b0) % 9 = 0 := by rw [Nat.mul_mod, h3b0_m9, Nat.mul_zero, Nat.zero_mod]
    omega
  have hnc6_c : ∀ c : Nat, c ≥ 1 -> ¬ isDiamond5Cone6 (c * 3 ^ b0 - 7) := by
    intro c hc1; apply not_cone6_of_mod9_ne_8
    have hm : c * 3 ^ b0 ≥ 27 := by simpa using Nat.mul_le_mul hc1 hp3_ge27
    have hm9 : (c * 3 ^ b0) % 9 = 0 := by rw [Nat.mul_mod, h3b0_m9, Nat.mul_zero, Nat.zero_mod]
    omega
  refine ⟨?_, ?_⟩
  · have hs1 : cousinDiamond12Step (4 * 3 ^ b0 - 7) = 6 * 3 ^ b0 - 10 := by
      have hdm := (Nat.div_add_mod (3 ^ b0) 8).symm
      rw [d12_eq_d11_of_not_cone13 _ (not_cone13_of_mod32_ne_21 _ (by rcases h3b0_m8 with h1 | h3 <;> omega)),
          cousinDiamond11Step_eq_d10_of_not_cone12 _ (not_cone12_of_mod32_ne_13 _ (by rcases h3b0_m8 with h1 | h3 <;> omega)),
          cousinDiamond10Step_eq_d9_of_not_cone11 _ (not_cone11_of_mod32_ne_13 _ (by rcases h3b0_m8 with h1 | h3 <;> omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_mod32_ne_13 _ (by rcases h3b0_m8 with h1 | h3 <;> omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_mod32_ne_13 _ (by rcases h3b0_m8 with h1 | h3 <;> omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_mod32_ne_21 _ (by rcases h3b0_m8 with h1 | h3 <;> omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (hnc7_c 4 (by decide)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (hnc6_c 4 (by decide))]
      exact cousin_diamond4_exit_step_general_odd 4 b0 (Or.inl rfl) hb0
    have hs2 : cousinDiamond12Step (6 * 3 ^ b0 - 10) = 2 * 3 ^ b0 - 4 := by
      rw [hd3_of_even _ (by omega)]
      have h18 : 6 * 3 ^ b0 = 18 * 3 ^ (b0 - 1) := by rw [h3b0_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]; omega
    have hs3 : cousinDiamond12Step (2 * 3 ^ b0 - 4) = 2 * 3 ^ (b0 - 1) - 2 := by
      rw [hd3_of_even _ (by omega)]
      have h18 : 2 * 3 ^ b0 = 18 * 3 ^ (b0 - 2) := by rw [h3b0_sp, h3b1_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]; omega
    have hs4 : cousinDiamond12Step (2 * 3 ^ (b0 - 1) - 2) = 3 ^ (b0 - 1) - 1 := by
      rw [hd3_of_even _ (by omega)]
      have h18 : 2 * 3 ^ (b0 - 1) = 18 * 3 ^ (b0 - 3) := by
        calc 2 * 3 ^ (b0 - 1) = 2 * 3 ^ (2 + (b0 - 3)) := by congr 2; omega
          _ = 2 * (3 ^ 2 * 3 ^ (b0 - 3)) := by rw [Nat.pow_add]
          _ = 18 * 3 ^ (b0 - 3) := by omega
      have hp3_b3 := pow3_pos_nat (b0 - 3)
      have hn8 : ¬ (2 * 3 ^ (b0 - 1) - 2 > 2 ∧ (2 * 3 ^ (b0 - 1) - 2) % 8 = 6) := by
        by_cases hev_b : (b0 - 1) % 2 = 0
        · have h9 : 3 ^ (b0 - 1) % 8 = 1 := by
            rw [show b0 - 1 = 2 * ((b0 - 1) / 2) by omega, ← pow9_eq_pow3_double]; exact pow9_mod8_eq_one_w5 _
          omega
        · have h9 : 3 ^ (b0 - 1) % 8 = 3 := by
            rw [show b0 - 1 = 2 * ((b0 - 1) / 2) + 1 by omega, Nat.pow_succ, ← pow9_eq_pow3_double, Nat.mul_mod, pow9_mod8_eq_one_w5]
          omega
      rw [cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) hn8]; omega
    rw [show b0 + 3 = 4 + (b0 - 2) + 1 by omega,
        cousinDiamond12Iter_add (4 + (b0 - 2)) 1,
        cousinDiamond12Iter_add 4 (b0 - 2)]
    have hi4 : cousinDiamond12Iter 4 (4 * 3 ^ b0 - 7) = 3 ^ ((b0 - 2) + 1) - 1 := by
      simp only [cousinDiamond12Iter, hs1, hs2, hs3, hs4]; rw [show b0 - 1 = (b0 - 2) + 1 by omega]
    rw [hi4, cousin_diamond12_pow3_sub1_drain (b0 - 2)]; decide
  · rcases cousin_diamond12_a0_3_drain b0 hb0 with ⟨ha3_s1, ha3_s2, ha3_s3, ha3⟩
    have ho := pow3_odd_nat_sec8 b0
    have hs1 : cousinDiamond12Step (16 * 3 ^ b0 - 7) = 24 * 3 ^ b0 - 10 := by
      rw [d12_eq_d11_of_not_cone13 _ (not_cone13_of_mod32_ne_21 _ (by omega)),
          cousinDiamond11Step_eq_d10_of_not_cone12 _ (not_cone12_of_mod32_ne_13 _ (by omega)),
          cousinDiamond10Step_eq_d9_of_not_cone11 _ (not_cone11_of_mod32_ne_13 _ (by omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_mod32_ne_13 _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_mod32_ne_13 _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_mod32_ne_21 _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (hnc7_c 16 (by decide)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (hnc6_c 16 (by decide))]
      exact cousin_diamond4_exit_step_general_odd 16 b0 (Or.inr (Or.inr rfl)) hb0
    have hs2 : cousinDiamond12Step (24 * 3 ^ b0 - 10) = 8 * 3 ^ b0 - 4 := by
      rw [hd3_of_even _ (by omega)]
      have h18 : 24 * 3 ^ b0 = 18 * (4 * 3 ^ (b0 - 1)) := by rw [h3b0_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]; omega
    have hs3 : cousinDiamond12Step (8 * 3 ^ b0 - 4) = 8 * 3 ^ (b0 - 1) - 2 := by
      rw [hd3_of_even _ (by omega)]
      have h18 : 8 * 3 ^ b0 = 18 * (4 * 3 ^ (b0 - 2)) := by rw [h3b0_sp, h3b1_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]; omega
    have hs4 : cousinDiamond12Step (8 * 3 ^ (b0 - 1) - 2) = 4 * 3 ^ (b0 - 1) - 2 := by
      rw [hd3_of_even _ (by omega)]
      have h18 : 8 * 3 ^ (b0 - 1) = 18 * (4 * 3 ^ (b0 - 3)) := by
        calc 8 * 3 ^ (b0 - 1) = 8 * 3 ^ (2 + (b0 - 3)) := by congr 2; omega
          _ = 8 * (3 ^ 2 * 3 ^ (b0 - 3)) := by rw [Nat.pow_add]
          _ = 18 * (4 * 3 ^ (b0 - 3)) := by omega
      have hp3_b3 := pow3_pos_nat (b0 - 3)
      rw [cousinDiamond3Step_even_mod8_eq6_w8 _ (by omega) (by omega) (by omega) ⟨by omega, by omega⟩]; omega
    rw [show (b0 - 1) / 2 + 7 = 3 + ((b0 - 1) / 2 + 4) by omega,
        cousinDiamond12Iter_add 3 ((b0 - 1) / 2 + 4)] at ha3
    have hi3 : cousinDiamond12Iter 3 (8 * 3 ^ b0 - 7) = 4 * 3 ^ (b0 - 1) - 2 := by
      simp only [cousinDiamond12Iter, ha3_s1, ha3_s2, ha3_s3]
    rw [hi3] at ha3
    rw [show (b0 - 1) / 2 + 8 = 4 + ((b0 - 1) / 2 + 4) by omega,
        cousinDiamond12Iter_add 4 ((b0 - 1) / 2 + 4)]
    have hi4 : cousinDiamond12Iter 4 (16 * 3 ^ b0 - 7) = 4 * 3 ^ (b0 - 1) - 2 := by
      simp only [cousinDiamond12Iter, hs1, hs2, hs3, hs4]
    rw [hi4]; exact ha3

private theorem cousin_diamond12_cone4_return_aux (x : Nat) (hc4 : isDiamond3Cone4 x) :
    ∃ k : Nat, k ≤ cousinDiamond2Phi x ∧ cousinDiamond12Iter k x = 1 := by
  rcases cousin_diamond3_cone4_reaches_one_exact x hc4 with ⟨r, hr_ge3, hE, _, hphi_ge⟩
  refine ⟨3 * r + 4, hphi_ge, ?_⟩
  have hx_odd : x % 2 = 1 := by have := hc4.2.1; omega
  have hs1 : cousinDiamond12Step x = 2 ^ (2 * r + 1) - 1 := by
    rw [d12_eq_d11_of_not_cone13 x (not_cone13_of_mod8_ne_5 x (by have := hc4.2.1; omega)),
        cousinDiamond11Step_eq_d10_of_not_cone12 x (not_cone12_of_mod8_ne_5 x (by have := hc4.2.1; omega)),
        cousinDiamond10Step_eq_d9_of_not_cone11 x (not_cone11_of_mod8_ne_5 x (by have := hc4.2.1; omega)),
        cousinDiamond9Step_eq_d8_of_not_cone10 x (not_cone10_of_mod8_ne_5 x (by have := hc4.2.1; omega)),
        cousinDiamond8Step_eq_d7_of_not_cone9 x (not_cone9_of_mod8_ne_5 x (by have := hc4.2.1; omega)),
        cousinDiamond7Step_eq_d6_of_not_cone8 x (not_cone8_of_mod8_ne_5 x (by have := hc4.2.1; omega)),
        cousinDiamond6Step_eq_d5_of_not_cone7 x (not_cone7_of_mod8_ne_5 x (by have := hc4.2.1; omega)),
        cousinDiamond5Step_eq_d4_of_not_cone6 x (by rintro ⟨_, h256, _, _⟩; have := hc4.2.1; omega)]
    unfold cousinDiamond4Step
    have hp4 : 2 ^ (2 * r + 3) = 4 * 2 ^ (2 * r + 1) := by
      rw [show 2 * r + 3 = 2 + (2 * r + 1) by omega, Nat.pow_add]
    have hp_pos := pow2_pos_nat (2 * r + 1)
    by_cases hc5 : isDiamond4Cone5 x
    · simp only [hc5, ite_true]; omega
    · simp only [hc5, ite_false]; rw [cousinDiamond3Step_of_cone4_w8 x hx_odd hc4]; omega
  let zr := 2 * 9 ^ r - 1
  let yr := (3 * 9 ^ r - 1) / 2
  have hglide : cousinDiamond12Iter (2 * r) (2 ^ (2 * r + 1) - 1) = zr := by
    have hf := cousin_diamond12_mersenne_scaled (2 * r) (2 * r + 1) 1 (by omega) (by decide)
    simp only [Nat.mul_one, show 2 * r + 1 - 2 * r = 1 by omega, Nat.pow_one] at hf
    rw [hf, ← pow9_eq_pow3_double r, Nat.mul_comm]
  have hp9_ge729 : 9 ^ r ≥ 729 := by simpa using nat_pow_mono_exp_pos 9 3 r (by decide) hr_ge3
  have hp9_m8 := pow9_mod8_eq_one_w5 r
  have hsz : cousinDiamond12Step zr = yr := by
    rw [d12_eq_d11_of_not_cone13 zr (not_cone13_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
        cousinDiamond11Step_eq_d10_of_not_cone12 zr (not_cone12_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
        cousinDiamond10Step_eq_d9_of_not_cone11 zr (not_cone11_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
        cousinDiamond9Step_eq_d8_of_not_cone10 zr (not_cone10_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
        cousinDiamond8Step_eq_d7_of_not_cone9 zr (not_cone9_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
        cousinDiamond7Step_eq_d6_of_not_cone8 zr (not_cone8_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
        cousinDiamond6Step_eq_d5_of_not_cone7 zr (not_cone7_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
        cousinDiamond5Step_eq_d4_of_not_cone6 zr (not_cone6_of_mod16_ne_13 zr (by dsimp [zr]; omega)),
        cousinDiamond4Step_eq_d3_of_not_cone5 zr (by rintro ⟨_, h32, _, _⟩; dsimp [zr] at h32; omega)]
    have hc3 : core3 (zr + 1) = 2 := by
      rw [show zr + 1 = 2 * 9 ^ r by dsimp [zr]; omega, core3_mul2 (9 ^ r) (by omega), (pow9_eq_v3Pow_w5 r).2]
    rw [cousinDiamond3Step_of_core3_succ_two_w8 zr (by dsimp [zr]; omega) (by dsimp [zr]; omega) hc3]
    dsimp [zr, yr]; omega
  have hsy : cousinDiamond12Step yr = (9 ^ (r + 1) - 1) / 4 := by
    have hyr_m3 : yr % 3 = 1 := by
      have hm3 : 9 ^ r % 3 = 0 := by rw [show r = (r - 1) + 1 by omega, Nat.pow_succ]; omega
      dsimp [yr]; omega
    rw [d12_eq_d11_of_not_cone13 yr (not_cone13_of_mod3_ne_2 yr (by omega)),
        cousinDiamond11Step_eq_d10_of_not_cone12 yr (not_cone12_of_mod3_ne_2 yr (by omega)),
        cousinDiamond10Step_eq_d9_of_not_cone11 yr (not_cone11_of_mod3_ne_2 yr (by omega)),
        cousinDiamond9Step_eq_d8_of_not_cone10 yr (not_cone10_of_mod3_ne_2 yr (by omega)),
        cousinDiamond8Step_eq_d7_of_not_cone9 yr (not_cone9_of_mod3_ne_2 yr (by omega)),
        cousinDiamond7Step_eq_d6_of_not_cone8 yr (not_cone8_of_mod3_ne_2 yr (by omega)),
        cousinDiamond6Step_eq_d5_of_not_cone7 yr (not_cone7_of_mod9_ne_8 yr (by omega)),
        cousinDiamond5Step_eq_d4_of_not_cone6 yr (not_cone6_of_mod9_ne_8 yr (by omega)),
        cousinDiamond4Step_eq_d3_of_not_cone5 yr (by rintro ⟨_, _, hm3, _⟩; omega)]
    have hc3_2 : core3 (2 * yr + 1) = 1 := by
      rw [show 2 * yr + 1 = 3 * 9 ^ r by dsimp [yr]; omega, core3_mul3 (9 ^ r) (by omega), (pow9_eq_v3Pow_w5 r).2]
    have hc3_1 : core3 (yr + 1) ≠ 2 := by rw [core3_not_div3 (yr + 1) (by omega)]; dsimp [yr]; omega
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
      cousinDiamond12Iter_add (1 + 2 * r + 1 + 1 + r) 1,
      cousinDiamond12Iter_add (1 + 2 * r + 1 + 1) r,
      cousinDiamond12Iter_add (1 + 2 * r + 1) 1,
      cousinDiamond12Iter_add (1 + 2 * r) 1,
      cousinDiamond12Iter_add 1 (2 * r)]
  rw [show cousinDiamond12Iter 1 x = 2 ^ (2 * r + 1) - 1 from hs1, hglide,
      show cousinDiamond12Iter 1 zr = yr from hsz,
      show cousinDiamond12Iter 1 yr = (9 ^ (r + 1) - 1) / 4 from hsy,
      cousin_diamond12_even9_spine_drain r]
  decide

private theorem cousin_diamond12_cone5_return_aux (x : Nat) (hc5 : isDiamond4Cone5 x) :
    ∃ (a b k : Nat),
      a ≥ 5 ∧ b ≥ 1 ∧ x + 7 = 2 ^ a * 3 ^ b ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond12Iter k x = 1 := by
  rcases cousin_diamond11_cones4to12_exact_return.2.1 x hc5 with ⟨a, b, _, ha5, hb1, hmul, _, _, _⟩
  have hx_eq : x = 2 ^ a * 3 ^ b - 7 := by omega
  let q_c := (a - 2) / 3
  let a0 := a - 3 * q_c
  let b0 := b + 2 * q_c
  have hb0_ge3 : b0 ≥ 3 := by dsimp [b0, q_c]; omega
  have ha0_234 : a0 = 2 ∨ a0 = 3 ∨ a0 = 4 := by dsimp [a0, q_c]; omega
  have hclimb := cousin_diamond12_cone5_two_step_climb q_c a b (by dsimp [q_c]; omega) hb1
  rw [← hx_eq] at hclimb
  change cousinDiamond12Iter (2 * q_c) x = 2 ^ a0 * 3 ^ b0 - 7 at hclimb
  have hbound_x : ∀ ex : Nat, ex ≤ b0 + 8 -> 2 * q_c + ex ≤ x := by
    intro ex hex
    have hprod := Nat.mul_le_mul (pow2_ge_six_mul_ge5 a ha5) (pow3_ge_add_two_ge1 b hb1)
    rw [hmul.symm] at hprod
    have hab : 6 * b ≤ 6 * a * b := by
      rw [Nat.mul_comm (6 * a) b, ← Nat.mul_assoc, Nat.mul_comm b 6]
      simpa using Nat.mul_le_mul_left (6 * b) (by omega : 1 ≤ a)
    rw [show (6 * a) * (b + 2) = 6 * a * b + 12 * a by rw [Nat.mul_add]; omega] at hprod
    dsimp [q_c, b0] at hex ⊢; omega
  have hd_3 := (cousin_diamond12_a0_3_drain b0 hb0_ge3).2.2.2
  rcases cousin_diamond12_a0_2_and_4_drain b0 hb0_ge3 with ⟨hd_2, hd_4⟩
  rcases ha0_234 with ha2 | ha3 | ha4
  · have hkx := hbound_x (b0 + 3) (by omega)
    refine ⟨a, b, 2 * q_c + (b0 + 3), ha5, hb1, hmul, hkx,
      Nat.le_trans (by omega : 2 * q_c + (b0 + 3) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond12Iter_add (2 * q_c) (b0 + 3) x, hclimb, ha2]; exact hd_2
  · have hkx := hbound_x ((b0 - 1) / 2 + 7) (by omega)
    refine ⟨a, b, 2 * q_c + ((b0 - 1) / 2 + 7), ha5, hb1, hmul, hkx,
      Nat.le_trans (by omega : 2 * q_c + ((b0 - 1) / 2 + 7) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond12Iter_add (2 * q_c) ((b0 - 1) / 2 + 7) x, hclimb, ha3]; exact hd_3
  · have hkx := hbound_x ((b0 - 1) / 2 + 8) (by omega)
    refine ⟨a, b, 2 * q_c + ((b0 - 1) / 2 + 8), ha5, hb1, hmul, hkx,
      Nat.le_trans (by omega : 2 * q_c + ((b0 - 1) / 2 + 8) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond12Iter_add (2 * q_c) ((b0 - 1) / 2 + 8) x, hclimb, ha4]; exact hd_4

private theorem lift_cone_step_to_d12 (x y D : Nat) (hD8 : D ≥ 8) (hx_ge : x ≥ 2000)
    (hnc13 : ¬ isDiamond12Cone13 x)
    (hd11 : cousinDiamond11Step x = y)
    (hy_div : y = (3 * x + 1) / D)
    (hret_y : ∃ ky : Nat, ky ≤ y ∧ cousinDiamond12Iter ky y = 1) :
    ∃ k : Nat, k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond12Step x = y ∧ cousinDiamond12Iter k x = 1 := by
  rcases hret_y with ⟨ky, hky_y, hky_1⟩
  have hstep : cousinDiamond12Step x = y := (d12_eq_d11_of_not_cone13 x hnc13).trans hd11
  have hy_lt : y + 1 ≤ x := by
    have hdiv : y * D ≤ 3 * x + 1 := by rw [hy_div]; exact Nat.div_mul_le_self (3 * x + 1) D
    have h8 : y * 8 ≤ y * D := Nat.mul_le_mul_left y hD8
    omega
  refine ⟨1 + ky, by omega, Nat.le_trans (by omega : 1 + ky ≤ x + 1) (cousinDiamond2Phi_ge_succ x), hstep, ?_⟩
  rw [cousinDiamond12Iter_add 1 ky x, show cousinDiamond12Iter 1 x = y from hstep]; exact hky_1

/--
  Theorem W15.3e (`cousin_diamond12_cones4to13_exact_return`, `zero custom axioms`):
  Exact 10-Tier `ω^10` Multi-Block Return Across Cones 4, 5, 6, 7, 8, 9, 10, 11, 12, AND 13
  of `T_diamond12` (`Branch P5.14`, `W15_H3`).
-/
theorem cousin_diamond12_cones4to13_exact_return :
    (∀ x : Nat, isDiamond3Cone4 x ->
      ∃ k : Nat, k ≤ cousinDiamond2Phi x ∧ cousinDiamond12Iter k x = 1) ∧
    (∀ x : Nat, isDiamond4Cone5 x ->
      ∃ (a b k : Nat),
        a ≥ 5 ∧ b ≥ 1 ∧ x + 7 = 2 ^ a * 3 ^ b ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond12Iter k x = 1) ∧
    (∀ x : Nat, isDiamond5Cone6 x ->
      ∃ (e f k : Nat),
        e ≥ 8 ∧ f ≥ 2 ∧ x + 19 = 2 ^ e * 3 ^ f ∧
        cousinDiamond12Step x = 2 ^ (e - 3) * 3 ^ (f + 1) - 7 ∧
        isDiamond4Cone5 (cousinDiamond12Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond12Iter k x = 1) ∧
    (∀ x : Nat, isDiamond6Cone7 x ->
      ∃ (g h k : Nat),
        g ≥ 15 ∧ h ≥ 2 ∧ x + 811 = 2 ^ g * 3 ^ h ∧
        cousinDiamond12Step x = 2 ^ (g - 7) * 3 ^ (h + 1) - 19 ∧
        isDiamond5Cone6 (cousinDiamond12Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond12Iter k x = 1) ∧
    (∀ x : Nat, isDiamond7Cone8 x ->
      ∃ (u v k : Nat),
        u ≥ 22 ∧ v ≥ 1 ∧ x + 34603 = 2 ^ u * 3 ^ v ∧
        cousinDiamond12Step x = 2 ^ (u - 7) * 3 ^ (v + 1) - 811 ∧
        isDiamond6Cone7 (cousinDiamond12Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond12Iter k x = 1) ∧
    (∀ x : Nat, isDiamond8Cone9 x ->
      ∃ (w z k : Nat),
        w ≥ 25 ∧ z ≥ 1 ∧ x + 92275 = 2 ^ w * 3 ^ z ∧
        cousinDiamond12Step x = 2 ^ (w - 3) * 3 ^ (z + 1) - 34603 ∧
        isDiamond7Cone8 (cousinDiamond12Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond12Iter k x = 1) ∧
    (∀ x : Nat, isDiamond9Cone10 x ->
      ∃ (p q k : Nat),
        p ≥ 28 ∧ q ≥ 1 ∧ x + 246067 = 2 ^ p * 3 ^ q ∧
        cousinDiamond12Step x = 2 ^ (p - 3) * 3 ^ (q + 1) - 92275 ∧
        isDiamond8Cone9 (cousinDiamond12Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond12Iter k x = 1) ∧
    (∀ x : Nat, isDiamond10Cone11 x ->
      ∃ (r s k : Nat),
        r ≥ 31 ∧ s ≥ 1 ∧ x + 656179 = 2 ^ r * 3 ^ s ∧
        cousinDiamond12Step x = 2 ^ (r - 3) * 3 ^ (s + 1) - 246067 ∧
        isDiamond9Cone10 (cousinDiamond12Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond12Iter k x = 1) ∧
    (∀ x : Nat, isDiamond11Cone12 x ->
      ∃ (m n k : Nat),
        m ≥ 34 ∧ n ≥ 1 ∧ x + 1749811 = 2 ^ m * 3 ^ n ∧
        cousinDiamond12Step x = 2 ^ (m - 3) * 3 ^ (n + 1) - 656179 ∧
        isDiamond10Cone11 (cousinDiamond12Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond12Iter k x = 1) ∧
    (∀ x : Nat, isDiamond12Cone13 x ->
      ∃ (a b k : Nat),
        a ≥ 39 ∧ b ≥ 1 ∧ x + 18664651 = 2 ^ a * 3 ^ b ∧
        cousinDiamond12Step x = 2 ^ (a - 5) * 3 ^ (b + 1) - 1749811 ∧
        isDiamond11Cone12 (cousinDiamond12Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond12Iter k x = 1) := by
  have hc6_ret : ∀ x : Nat, isDiamond5Cone6 x ->
      ∃ (e f k : Nat), e ≥ 8 ∧ f ≥ 2 ∧ x + 19 = 2 ^ e * 3 ^ f ∧
        cousinDiamond12Step x = 2 ^ (e - 3) * 3 ^ (f + 1) - 7 ∧
        isDiamond4Cone5 (cousinDiamond12Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond12Iter k x = 1 := by
    intro x hc6
    rcases cousin_diamond11_cones4to12_exact_return.2.2.1 x hc6 with ⟨e, f, _, he8, hf2, hmul, hd11, hc5_y, _, _, _⟩
    rw [hd11] at hc5_y
    rcases cousin_diamond12_cone5_return_aux _ hc5_y with ⟨_, _, ky, _, _, _, hky_y, _, hky_1⟩
    have hnc13 : ¬ isDiamond12Cone13 x := not_cone13_of_mod32_ne_21 x (by
      have h := congrArg (· % 32) hc6.2.1; rw [Nat.mod_mod_of_dvd x (by decide : 32 ∣ 256)] at h; omega)
    have hy_div : 2 ^ (e - 3) * 3 ^ (f + 1) - 7 = (3 * x + 1) / 8 := by
      have hp2 : 2 ^ e = 8 * 2 ^ (e - 3) := by
        conv => lhs; rw [show e = 3 + (e - 3) by omega, Nat.pow_add]
      have h3x : 3 * (x + 19) = 8 * (2 ^ (e - 3) * 3 ^ (f + 1)) := by
        rw [hmul, hp2, Nat.pow_succ 3 f]; ac_rfl
      have hge := hc6.1; omega
    rcases lift_cone_step_to_d12 x _ 8 (by decide) (by have := hc6.1; omega) hnc13 hd11 hy_div ⟨ky, hky_y, hky_1⟩ with
      ⟨k, hkx, hkphi, hst, hk1⟩
    exact ⟨e, f, k, he8, hf2, hmul, hst, by rw [hst]; exact hc5_y, hkx, hkphi, hk1⟩
  have hc7_ret : ∀ x : Nat, isDiamond6Cone7 x ->
      ∃ (g h k : Nat), g ≥ 15 ∧ h ≥ 2 ∧ x + 811 = 2 ^ g * 3 ^ h ∧
        cousinDiamond12Step x = 2 ^ (g - 7) * 3 ^ (h + 1) - 19 ∧
        isDiamond5Cone6 (cousinDiamond12Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond12Iter k x = 1 := by
    intro x hc7
    rcases cousin_diamond11_cones4to12_exact_return.2.2.2.1 x hc7 with ⟨g, h, _, hg15, hh2, hmul, hd11, hc6_y, _, _, _⟩
    rw [hd11] at hc6_y
    rcases hc6_ret _ hc6_y with ⟨_, _, ky, _, _, _, _, _, hky_y, _, hky_1⟩
    have hnc13 : ¬ isDiamond12Cone13 x := not_cone13_of_mod64_ne_53 x (by
      have h64 := congrArg (· % 64) hc7.2.1; rw [Nat.mod_mod_of_dvd x (by decide : 64 ∣ 32768)] at h64; omega)
    have hy_div : 2 ^ (g - 7) * 3 ^ (h + 1) - 19 = (3 * x + 1) / 128 := by
      have hp2 : 2 ^ g = 128 * 2 ^ (g - 7) := by
        conv => lhs; rw [show g = 7 + (g - 7) by omega, Nat.pow_add]
      have h3x : 3 * (x + 811) = 128 * (2 ^ (g - 7) * 3 ^ (h + 1)) := by
        rw [hmul, hp2, Nat.pow_succ 3 h]; ac_rfl
      have hge := hc7.1; omega
    rcases lift_cone_step_to_d12 x _ 128 (by decide) (by have := hc7.1; omega) hnc13 hd11 hy_div ⟨ky, hky_y, hky_1⟩ with
      ⟨k, hkx, hkphi, hst, hk1⟩
    exact ⟨g, h, k, hg15, hh2, hmul, hst, by rw [hst]; exact hc6_y, hkx, hkphi, hk1⟩
  have hc8_ret : ∀ x : Nat, isDiamond7Cone8 x ->
      ∃ (u v k : Nat), u ≥ 22 ∧ v ≥ 1 ∧ x + 34603 = 2 ^ u * 3 ^ v ∧
        cousinDiamond12Step x = 2 ^ (u - 7) * 3 ^ (v + 1) - 811 ∧
        isDiamond6Cone7 (cousinDiamond12Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond12Iter k x = 1 := by
    intro x hc8
    rcases cousin_diamond11_cones4to12_exact_return.2.2.2.2.1 x hc8 with ⟨u, v, _, hu22, hv1, hmul, hd11, hc7_y, _, _, _⟩
    rw [hd11] at hc7_y
    rcases hc7_ret _ hc7_y with ⟨_, _, ky, _, _, _, _, _, hky_y, _, hky_1⟩
    have hnc13 : ¬ isDiamond12Cone13 x := not_cone13_of_mod64_ne_53 x (by
      have h32k : x % 32768 = 30933 := by
        have hm := congrArg (· % 32768) hc8.2.1
        rw [Nat.mod_mod_of_dvd x (by decide : 32768 ∣ 4194304),
            show 4159701 % 32768 = 30933 by decide] at hm
        exact hm
      have h64 := congrArg (· % 64) h32k; rw [Nat.mod_mod_of_dvd x (by decide : 64 ∣ 32768)] at h64; omega)
    have hy_div : 2 ^ (u - 7) * 3 ^ (v + 1) - 811 = (3 * x + 1) / 128 := by
      have hp2 : 2 ^ u = 128 * 2 ^ (u - 7) := by
        conv => lhs; rw [show u = 7 + (u - 7) by omega, Nat.pow_add]
      have h3x : 3 * (x + 34603) = 128 * (2 ^ (u - 7) * 3 ^ (v + 1)) := by
        rw [hmul, hp2, Nat.pow_succ 3 v]; ac_rfl
      have hge := hc8.1; omega
    rcases lift_cone_step_to_d12 x _ 128 (by decide) (by have := hc8.1; omega) hnc13 hd11 hy_div ⟨ky, hky_y, hky_1⟩ with
      ⟨k, hkx, hkphi, hst, hk1⟩
    exact ⟨u, v, k, hu22, hv1, hmul, hst, by rw [hst]; exact hc7_y, hkx, hkphi, hk1⟩
  have hc9_ret : ∀ x : Nat, isDiamond8Cone9 x ->
      ∃ (w z k : Nat), w ≥ 25 ∧ z ≥ 1 ∧ x + 92275 = 2 ^ w * 3 ^ z ∧
        cousinDiamond12Step x = 2 ^ (w - 3) * 3 ^ (z + 1) - 34603 ∧
        isDiamond7Cone8 (cousinDiamond12Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond12Iter k x = 1 := by
    intro x hc9
    rcases cousin_diamond11_cones4to12_exact_return.2.2.2.2.2.1 x hc9 with ⟨w, z, _, hw25, hz1, hmul, hd11, hc8_y, _, _, _⟩
    rw [hd11] at hc8_y
    rcases hc8_ret _ hc8_y with ⟨_, _, ky, _, _, _, _, _, hky_y, _, hky_1⟩
    have hnc13 : ¬ isDiamond12Cone13 x := not_cone13_of_mod32_ne_21 x (by rw [mod32_of_cone9 x hc9]; decide)
    have hy_div : 2 ^ (w - 3) * 3 ^ (z + 1) - 34603 = (3 * x + 1) / 8 := by
      have hp2 : 2 ^ w = 8 * 2 ^ (w - 3) := by
        conv => lhs; rw [show w = 3 + (w - 3) by omega, Nat.pow_add]
      have h3x : 3 * (x + 92275) = 8 * (2 ^ (w - 3) * 3 ^ (z + 1)) := by
        rw [hmul, hp2, Nat.pow_succ 3 z]; ac_rfl
      have hge := hc9.1; omega
    rcases lift_cone_step_to_d12 x _ 8 (by decide) (by have := hc9.1; omega) hnc13 hd11 hy_div ⟨ky, hky_y, hky_1⟩ with
      ⟨k, hkx, hkphi, hst, hk1⟩
    exact ⟨w, z, k, hw25, hz1, hmul, hst, by rw [hst]; exact hc8_y, hkx, hkphi, hk1⟩
  have hc10_ret : ∀ x : Nat, isDiamond9Cone10 x ->
      ∃ (p q k : Nat), p ≥ 28 ∧ q ≥ 1 ∧ x + 246067 = 2 ^ p * 3 ^ q ∧
        cousinDiamond12Step x = 2 ^ (p - 3) * 3 ^ (q + 1) - 92275 ∧
        isDiamond8Cone9 (cousinDiamond12Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond12Iter k x = 1 := by
    intro x hc10
    rcases cousin_diamond11_cones4to12_exact_return.2.2.2.2.2.2.1 x hc10 with ⟨p, q, _, hp28, hq1, hmul, hd11, hc9_y, _, _, _⟩
    rw [hd11] at hc9_y
    rcases hc9_ret _ hc9_y with ⟨_, _, ky, _, _, _, _, _, hky_y, _, hky_1⟩
    have hnc13 : ¬ isDiamond12Cone13 x := not_cone13_of_mod32_ne_21 x (by
      have h := congrArg (· % 32) hc10.2.1
      rw [Nat.mod_mod_of_dvd x (by decide : 32 ∣ 268435456),
          show 268189389 % 32 = 13 by decide] at h
      omega)
    have hy_div : 2 ^ (p - 3) * 3 ^ (q + 1) - 92275 = (3 * x + 1) / 8 := by
      have hp2 : 2 ^ p = 8 * 2 ^ (p - 3) := by
        conv => lhs; rw [show p = 3 + (p - 3) by omega, Nat.pow_add]
      have h3x : 3 * (x + 246067) = 8 * (2 ^ (p - 3) * 3 ^ (q + 1)) := by
        rw [hmul, hp2, Nat.pow_succ 3 q]; ac_rfl
      have hge := hc10.1; omega
    rcases lift_cone_step_to_d12 x _ 8 (by decide) (by have := hc10.1; omega) hnc13 hd11 hy_div ⟨ky, hky_y, hky_1⟩ with
      ⟨k, hkx, hkphi, hst, hk1⟩
    exact ⟨p, q, k, hp28, hq1, hmul, hst, by rw [hst]; exact hc9_y, hkx, hkphi, hk1⟩
  have hc11_ret : ∀ x : Nat, isDiamond10Cone11 x ->
      ∃ (r s k : Nat), r ≥ 31 ∧ s ≥ 1 ∧ x + 656179 = 2 ^ r * 3 ^ s ∧
        cousinDiamond12Step x = 2 ^ (r - 3) * 3 ^ (s + 1) - 246067 ∧
        isDiamond9Cone10 (cousinDiamond12Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond12Iter k x = 1 := by
    intro x hc11
    rcases cousin_diamond11_cones4to12_exact_return.2.2.2.2.2.2.2.1 x hc11 with ⟨r, s, _, hr31, hs1, hmul, hd11, hc10_y, _, _, _⟩
    rw [hd11] at hc10_y
    rcases hc10_ret _ hc10_y with ⟨_, _, ky, _, _, _, _, _, hky_y, _, hky_1⟩
    have hnc13 : ¬ isDiamond12Cone13 x := not_cone13_of_mod32_ne_21 x (by rw [mod32_of_cone11 x hc11]; decide)
    have hy_div : 2 ^ (r - 3) * 3 ^ (s + 1) - 246067 = (3 * x + 1) / 8 := by
      have hp2 : 2 ^ r = 8 * 2 ^ (r - 3) := by
        conv => lhs; rw [show r = 3 + (r - 3) by omega, Nat.pow_add]
      have h3x : 3 * (x + 656179) = 8 * (2 ^ (r - 3) * 3 ^ (s + 1)) := by
        rw [hmul, hp2, Nat.pow_succ 3 s]; ac_rfl
      have hge := hc11.1; omega
    rcases lift_cone_step_to_d12 x _ 8 (by decide) (by have := hc11.1; omega) hnc13 hd11 hy_div ⟨ky, hky_y, hky_1⟩ with
      ⟨k, hkx, hkphi, hst, hk1⟩
    exact ⟨r, s, k, hr31, hs1, hmul, hst, by rw [hst]; exact hc10_y, hkx, hkphi, hk1⟩
  have hc12_ret : ∀ x : Nat, isDiamond11Cone12 x ->
      ∃ (m n k : Nat), m ≥ 34 ∧ n ≥ 1 ∧ x + 1749811 = 2 ^ m * 3 ^ n ∧
        cousinDiamond12Step x = 2 ^ (m - 3) * 3 ^ (n + 1) - 656179 ∧
        isDiamond10Cone11 (cousinDiamond12Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond12Iter k x = 1 := by
    intro x hc12
    rcases cousin_diamond11_cones4to12_exact_return.2.2.2.2.2.2.2.2 x hc12 with ⟨m, n, _, hm34, hn1, hmul, hd11, hc11_y, _, _, _⟩
    rw [hd11] at hc11_y
    rcases hc11_ret _ hc11_y with ⟨_, _, ky, _, _, _, _, _, hky_y, _, hky_1⟩
    have hnc13 : ¬ isDiamond12Cone13 x := not_cone13_of_mod32_ne_21 x (by rw [mod32_of_cone12 x hc12]; decide)
    have hy_div : 2 ^ (m - 3) * 3 ^ (n + 1) - 656179 = (3 * x + 1) / 8 := by
      have hp2 : 2 ^ m = 8 * 2 ^ (m - 3) := by
        conv => lhs; rw [show m = 3 + (m - 3) by omega, Nat.pow_add]
      have h3x : 3 * (x + 1749811) = 8 * (2 ^ (m - 3) * 3 ^ (n + 1)) := by
        rw [hmul, hp2, Nat.pow_succ 3 n]; ac_rfl
      have hge := hc12.1; omega
    rcases lift_cone_step_to_d12 x _ 8 (by decide) (by have := hc12.1; omega) hnc13 hd11 hy_div ⟨ky, hky_y, hky_1⟩ with
      ⟨k, hkx, hkphi, hst, hk1⟩
    exact ⟨m, n, k, hm34, hn1, hmul, hst, by rw [hst]; exact hc11_y, hkx, hkphi, hk1⟩
  refine ⟨cousin_diamond12_cone4_return_aux, cousin_diamond12_cone5_return_aux,
          hc6_ret, hc7_ret, hc8_ret, hc9_ret, hc10_ret, hc11_ret, hc12_ret, ?_⟩
  intro x hc13
  have hraw_step : cousinDiamond12Step x = (3 * x + 1) / 32 := by
    unfold cousinDiamond12Step; simp only [hc13, ite_true]
  rcases hc13 with ⟨hx_ge, hx39, hx3, hg1⟩
  have hdvd39 : 549755813888 ∣ (x + 18664651) :=
    Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, hx39])
  clear hx39
  rcases (⟨18664651 + x, rfl⟩ : ∃ N : Nat, N = 18664651 + x) with ⟨N, hN_def⟩
  rw [← hN_def] at hg1
  have hN_pos : N > 0 := by clear hraw_step hdvd39 hx3 hg1; omega
  rcases decomp_2_3_exact N hN_pos with ⟨_, _, _, _, _, hmul⟩
  rw [hg1, Nat.mul_one] at hmul
  rcases eq_pow2_of_v2Pow_aux N N hN_pos (Nat.le_refl _) with ⟨a, ha⟩
  rcases eq_pow3_of_v3Pow_aux N N hN_pos (Nat.le_refl _) with ⟨b, hb⟩
  rw [ha, hb] at hmul
  have hmul_comm : x + 18664651 = 2 ^ a * 3 ^ b := by
    rw [Nat.add_comm x 18664651, ← hN_def, ← hmul]
  clear hg1 ha hb hN_def hmul hN_pos
  have ha39 : a ≥ 39 := by
    by_cases hlt : a < 39
    · exfalso
      have h39_sp : 549755813888 = 2 ^ (a + 1) * 2 ^ (38 - a) := by
        rw [← Nat.pow_add 2 (a + 1) (38 - a), show a + 1 + (38 - a) = 39 by clear hraw_step hx_ge hx3 hdvd39 hmul_comm; omega]
      rcases hdvd39 with ⟨c, hc⟩
      rw [hmul_comm, h39_sp, Nat.mul_assoc (2 ^ (a + 1)), Nat.pow_succ 2 a, Nat.mul_assoc (2 ^ a) 2] at hc
      have h3b_ev : 3 ^ b = 2 * (2 ^ (38 - a) * c) :=
        nat_mul_left_cancel_pos (2 ^ a) _ _ (pow2_pos_nat a) hc
      have ho := pow3_odd_nat_sec8 b
      rw [h3b_ev, Nat.mul_mod_right] at ho; cases ho
    · clear hraw_step hx_ge hx3 hdvd39 hmul_comm; omega
  clear hdvd39
  have hb1 : b ≥ 1 := by
    cases b with
    | zero =>
      rw [Nat.pow_zero, Nat.mul_one] at hmul_comm
      exact False.elim (pow2_mod3_nonzero_w5 a (by rw [← hmul_comm, Nat.add_mod, hx3]))
    | succ _ => clear hraw_step hx_ge hx3 hmul_comm ha39; omega
  clear hx3
  let y := 2 ^ (a - 5) * 3 ^ (b + 1) - 1749811
  have hstep_x : cousinDiamond12Step x = y := by
    rw [hraw_step]; dsimp only [y]
    have hp32 : 2 ^ a = 32 * 2 ^ (a - 5) := by
      conv => lhs; rw [show a = 5 + (a - 5) by clear hraw_step hx_ge hmul_comm hb1; omega, Nat.pow_add]
    have hprod_pos : 2 ^ (a - 5) * 3 ^ b ≥ 17179869184 * 3 := by
      have h1 : 17179869184 ≤ 2 ^ (a - 5) := by
        rw [show (17179869184 : Nat) = 2 ^ 34 from rfl]
        exact pow2_mono_nat (by clear hraw_step hx_ge hmul_comm hb1 hp32; omega)
      have h2 : 3 ≤ 3 ^ b := by simpa using nat_pow_mono_exp_pos 3 1 b (by decide) hb1
      simpa using Nat.mul_le_mul h1 h2
    have h3_eq : 2 ^ (a - 5) * 3 ^ (b + 1) = 3 * (2 ^ (a - 5) * 3 ^ b) := by
      rw [Nat.pow_succ 3 b, ← Nat.mul_assoc, Nat.mul_comm _ 3]
    rw [h3_eq]
    have hx32 : x + 18664651 = 32 * (2 ^ (a - 5) * 3 ^ b) := by rw [hmul_comm, hp32, Nat.mul_assoc]
    have h3x1 : 3 * x + 1 = (3 * (2 ^ (a - 5) * 3 ^ b) - 1749811) * 32 := by
      clear hraw_step ha39 hb1 hp32 h3_eq hmul_comm
      generalize 2 ^ (a - 5) * 3 ^ b = A at hprod_pos hx32 ⊢; omega
    rw [h3x1]; exact Nat.mul_div_left _ (by decide : 0 < 32)
  have hc12_y : isDiamond11Cone12 y :=
    isDiamond11Cone12_of_pow2_pow3_w15 (a - 5) (b + 1)
      (by clear hraw_step hx_ge hmul_comm hstep_x; omega)
      (by clear hraw_step hx_ge hmul_comm hstep_x; omega)
  rcases hc12_ret y hc12_y with ⟨_, _, ky, _, _, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hstep_eq : y = (3 * x + 1) / 32 := hstep_x.symm.trans hraw_step
    have hdiv : y * 32 ≤ 3 * x + 1 := by rw [hstep_eq]; exact Nat.div_mul_le_self (3 * x + 1) 32
    clear hraw_step hmul_comm hstep_x hc12_y hky_1 hstep_eq; omega
  refine ⟨a, b, 1 + ky, ha39, hb1, hmul_comm, hstep_x, by rw [hstep_x]; exact hc12_y,
          by clear hraw_step hmul_comm hstep_x hc12_y hky_1; omega,
          Nat.le_trans (by clear hraw_step hmul_comm hstep_x hc12_y hky_1; omega : 1 + ky ≤ x + 1)
            (cousinDiamond2Phi_ge_succ x), ?_⟩
  rw [cousinDiamond12Iter_add 1 ky x, show cousinDiamond12Iter 1 x = y from hstep_x]; exact hky_1

private theorem cousin_diamond12_reaches_one_within_phi :
    ∀ (B x : Nat), x > 0 -> cousinDiamond2Phi x ≤ B ->
      ∃ k : Nat, k ≤ B ∧ cousinDiamond12Iter k x = 1
  | 0, x, _, hB => by have := cousinDiamond2Phi_ge_succ x; omega
  | B + 1, x, hx, hB => by
    by_cases hx1 : x = 1
    · subst hx1; exact ⟨0, by omega, rfl⟩
    · by_cases hx2 : x = 2
      · subst hx2
        have hphi2 : cousinDiamond2Phi 2 = 28 := by decide
        rw [hphi2] at hB; exact ⟨1, by omega, by decide⟩
      · by_cases hc4 : isDiamond3Cone4 x
        · rcases cousin_diamond12_cones4to13_exact_return.1 x hc4 with ⟨k, hle, hk1⟩
          exact ⟨k, Nat.le_trans hle hB, hk1⟩
        · by_cases hc5 : isDiamond4Cone5 x
          · rcases cousin_diamond12_cones4to13_exact_return.2.1 x hc5 with ⟨_, _, k, _, _, _, _, hle, hk1⟩
            exact ⟨k, Nat.le_trans hle hB, hk1⟩
          · by_cases hc6 : isDiamond5Cone6 x
            · rcases cousin_diamond12_cones4to13_exact_return.2.2.1 x hc6 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
              exact ⟨k, Nat.le_trans hle hB, hk1⟩
            · by_cases hc7 : isDiamond6Cone7 x
              · rcases cousin_diamond12_cones4to13_exact_return.2.2.2.1 x hc7 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                exact ⟨k, Nat.le_trans hle hB, hk1⟩
              · by_cases hc8 : isDiamond7Cone8 x
                · rcases cousin_diamond12_cones4to13_exact_return.2.2.2.2.1 x hc8 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                  exact ⟨k, Nat.le_trans hle hB, hk1⟩
                · by_cases hc9 : isDiamond8Cone9 x
                  · rcases cousin_diamond12_cones4to13_exact_return.2.2.2.2.2.1 x hc9 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                    exact ⟨k, Nat.le_trans hle hB, hk1⟩
                  · by_cases hc10 : isDiamond9Cone10 x
                    · rcases cousin_diamond12_cones4to13_exact_return.2.2.2.2.2.2.1 x hc10 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                      exact ⟨k, Nat.le_trans hle hB, hk1⟩
                    · by_cases hc11 : isDiamond10Cone11 x
                      · rcases cousin_diamond12_cones4to13_exact_return.2.2.2.2.2.2.2.1 x hc11 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                        exact ⟨k, Nat.le_trans hle hB, hk1⟩
                      · by_cases hc12 : isDiamond11Cone12 x
                        · rcases cousin_diamond12_cones4to13_exact_return.2.2.2.2.2.2.2.2.1 x hc12 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                          exact ⟨k, Nat.le_trans hle hB, hk1⟩
                        · by_cases hc13 : isDiamond12Cone13 x
                          · rcases cousin_diamond12_cones4to13_exact_return.2.2.2.2.2.2.2.2.2 x hc13 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                            exact ⟨k, Nat.le_trans hle hB, hk1⟩
                          · have hdesc := cousin_diamond12_outside_cones4to13_descent_and_mod63_nonreentry.1 x
                              (by omega) hc4 hc5 hc6 hc7 hc8 hc9 hc10 hc11 hc12 hc13
                            rcases cousin_diamond12_reaches_one_within_phi B (cousinDiamond12Step x)
                              (cousinDiamond12Step_pos x hx) (by omega) with ⟨k, hk_le, hk_eq⟩
                            exact ⟨k + 1, by omega, hk_eq⟩

/--
  Theorem W15.3f (`cousin_diamond12_global_convergence`, `zero custom axioms`):
  Unconditional Global Convergence & Degree-5 Polynomial Stopping Bound for `T_diamond12`:
  For EVERY `x > 0`, `cousinDiamond12Iter` reaches `1` within `k ≤ (x + 1) ^ 3 + (x + 1) ^ 5` steps!
-/
theorem cousin_diamond12_global_convergence (x : Nat) (hx : x > 0) :
    ∃ k : Nat, k ≤ (x + 1) ^ 3 + (x + 1) ^ 5 ∧ cousinDiamond12Iter k x = 1 := by
  rcases cousin_diamond12_reaches_one_within_phi (cousinDiamond2Phi x) x hx (Nat.le_refl _) with
    ⟨k, hk_phi, hk1⟩
  exact ⟨k, Nat.le_trans hk_phi (cousinDiamond2Phi_upper_poly_bound x), hk1⟩

private theorem exists_non_desc_along_diamond12_iter_w15 :
    ∀ (terms : List LaurentTerm) (A0 B0 C0 N z : Nat),
      N ≥ 1 ->
      (∀ i : Nat, i < N ->
        cousinDiamond12Iter i z ≥ 3 ∧
        (cousinDiamond12Iter i z) % 2 = 1 ∧
        cousinDiamond12Step (cousinDiamond12Iter i z) ≥ 3) ->
      ¬ laurentDescProp terms A0 B0 C0 z (cousinDiamond12Iter N z) ->
      ∃ x : Nat,
        x ≥ 3 ∧ x % 2 = 1 ∧ cousinDiamond12Step x ≥ 3 ∧
        ¬ laurentDescProp terms A0 B0 C0 x (cousinDiamond12Step x)
  | _, _, _, _, 0, _, hN, _, _ => by omega
  | _, _, _, _, 1, z, _, hall, hnd => by
    rcases hall 0 (by decide) with ⟨hz3, hzo, hsz3⟩
    exact ⟨z, hz3, hzo, hsz3, hnd⟩
  | terms, A0, B0, C0, m + 2, z, _, hall, hnd => by
    if h0 : laurentDescProp terms A0 B0 C0 z (cousinDiamond12Step z) then
      have hnd_next : ¬ laurentDescProp terms A0 B0 C0 (cousinDiamond12Step z)
          (cousinDiamond12Iter (m + 1) (cousinDiamond12Step z)) :=
        fun hrest => hnd (laurentDescProp_trans terms A0 B0 C0 z (cousinDiamond12Step z) _ h0 hrest)
      exact exists_non_desc_along_diamond12_iter_w15 terms A0 B0 C0 (m + 1) (cousinDiamond12Step z)
        (by omega) (fun i hi => hall (i + 1) (by omega)) hnd_next
    else
      rcases hall 0 (by omega) with ⟨hz3, hzo, hsz3⟩
      exact ⟨z, hz3, hzo, hsz3, h0⟩

/--
  Theorem W15.3g (`cousin_diamond12_ten_tier_cascade_and_laurent_impossibility`,
  `zero custom axioms`):
  1. Genuine 10-Tier `Cone 13 -> Cone 12 -> ... -> Cone 5` Cascade
     `9895585985333 -> 927711186125 -> 347891694797 -> 130459385549 -> 48922269581 ->
      18345851093 -> 429980885 -> 10077677 -> 3779129` & Unbounded `r`-Block Spiral Climb
     `cousinDiamond12Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5`!
  2. Universal `∀ L ≥ 1` Multi-Term Laurent Valuation Impossibility on `cousinDiamond12Step`!
-/
theorem cousin_diamond12_ten_tier_cascade_and_laurent_impossibility :
    cousinDiamond12Step 9895585985333 = 927711186125 ∧
    cousinDiamond12Step 927711186125 = 347891694797 ∧
    cousinDiamond12Step 347891694797 = 130459385549 ∧
    cousinDiamond12Step 130459385549 = 48922269581 ∧
    cousinDiamond12Step 48922269581 = 18345851093 ∧
    cousinDiamond12Step 18345851093 = 429980885 ∧
    cousinDiamond12Step 429980885 = 10077677 ∧
    cousinDiamond12Step 10077677 = 3779129 ∧
    (∀ (r j : Nat), r ≥ 1 -> j ≤ r ->
      cousinDiamond12Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5) ∧
    (∀ (terms : List LaurentTerm) (A0 B0 C0 : Nat),
      (∃ t ∈ terms, t.coeff > 0) ->
      ∃ x : Nat,
        x ≥ 3 ∧ x % 2 = 1 ∧ cousinDiamond12Step x ≥ 3 ∧
        ¬ (evalLaurentSumNum terms (cousinDiamond12Step x) * laurentValDen A0 B0 C0 x <
            evalLaurentSumNum terms x * laurentValDen A0 B0 C0 (cousinDiamond12Step x))) := by
  have hspiral : ∀ (r j : Nat), r ≥ 1 -> j ≤ r ->
      cousinDiamond12Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5 := by
    intro r j hr hj
    cases j with
    | zero => simp [cousinDiamond12Iter]
    | succ j' =>
      have hp16_ge16 : 16 ^ r ≥ 16 := by
        rw [show r = (r - 1) + 1 by omega, Nat.pow_succ]
        have := nat_pow_pos_of_pos 16 (by decide) (r - 1); omega
      let x0 := 4 * 16 ^ r - 5
      have hx0_m4 : x0 % 4 = 3 := by dsimp [x0]; omega
      have hx0_pow : 4 * 16 ^ r = 2 ^ (4 * r + 2) := by
        rw [show (16 : Nat) = 2 ^ 4 from rfl, pow_pow_eq_mul_w5 2 4 r,
            show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add 2 2 (4 * r), Nat.add_comm 2 (4 * r)]
      have hs_first : cousinDiamond12Step x0 = 2 ^ (4 * r + 1) * 3 ^ 1 - 7 := by
        rw [d12_eq_d11_of_not_cone13 x0 (not_cone13_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond11Step_eq_d10_of_not_cone12 x0 (not_cone12_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond10Step_eq_d9_of_not_cone11 x0 (not_cone11_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond9Step_eq_d8_of_not_cone10 x0 (not_cone10_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond8Step_eq_d7_of_not_cone9 x0 (not_cone9_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond7Step_eq_d6_of_not_cone8 x0 (not_cone8_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond6Step_eq_d5_of_not_cone7 x0 (not_cone7_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond5Step_eq_d4_of_not_cone6 x0 (not_cone6_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond4Step_mod4_eq_3 x0 hx0_m4]
        dsimp [x0]; rw [hx0_pow, show 4 * r + 2 = (4 * r + 1) + 1 by omega, Nat.pow_succ 2 (4 * r + 1)]
        have := pow2_pos_nat (4 * r + 1); omega
      have hclimb := cousin_diamond12_cone5_two_step_climb j' (4 * r + 1) 1 (by omega) (by decide)
      let y_end := 2 ^ (4 * r + 1 - 3 * j') * 3 ^ (1 + 2 * j') - 7
      have hy_c5 := isDiamond4Cone5_of_pow2_pow3 (4 * r + 1 - 3 * j') (1 + 2 * j') (by omega) (by omega)
      have hs_last : cousinDiamond12Step y_end = 4 * 16 ^ (r - (j' + 1)) * 18 ^ (j' + 1) - 5 := by
        rw [d12_eq_d11_of_not_cone13 y_end (not_cone13_of_mod32_ne_21 y_end (by have := hy_c5.2.1; omega)),
            cousinDiamond11Step_eq_d10_of_not_cone12 y_end (not_cone12_of_mod32_ne_13 y_end (by have := hy_c5.2.1; omega)),
            cousinDiamond10Step_eq_d9_of_not_cone11 y_end (not_cone11_of_mod32_ne_13 y_end (by have := hy_c5.2.1; omega)),
            cousinDiamond9Step_eq_d8_of_not_cone10 y_end (not_cone10_of_mod32_ne_13 y_end (by have := hy_c5.2.1; omega)),
            cousinDiamond8Step_eq_d7_of_not_cone9 y_end (not_cone9_of_mod32_ne_13 y_end (by have := hy_c5.2.1; omega)),
            cousinDiamond7Step_eq_d6_of_not_cone8 y_end (not_cone8_of_mod32_ne_21 y_end (by have := hy_c5.2.1; omega)),
            cousinDiamond6Step_eq_d5_of_not_cone7 y_end (not_cone7_of_mod32_ne_21 y_end (by have := hy_c5.2.1; omega)),
            cousinDiamond5Step_eq_d4_of_not_cone6 y_end (not_cone6_of_mod32_ne_13 y_end (by have := hy_c5.2.1; omega))]
        unfold cousinDiamond4Step; dsimp only [y_end]; simp only [hy_c5, ite_true]
        have hp2_sp : 2 ^ (4 * r + 1 - 3 * j') = 4 * (4 * 2 ^ (4 * (r - (j' + 1))) * 2 ^ (j' + 1)) := by
          rw [show 4 * r + 1 - 3 * j' = 2 + (4 * (r - (j' + 1)) + (j' + 1) + 2) by omega,
              Nat.pow_add 2 2, Nat.pow_add 2 (4 * (r - (j' + 1)) + (j' + 1)) 2,
              Nat.pow_add 2 (4 * (r - (j' + 1))) (j' + 1)]
          change 4 * (2 ^ (4 * (r - (j' + 1))) * 2 ^ (j' + 1) * 4) = _; ac_rfl
        have h16_rj : 2 ^ (4 * (r - (j' + 1))) = 16 ^ (r - (j' + 1)) := by
          rw [show (16 : Nat) = 2 ^ 4 from rfl, pow_pow_eq_mul_w5 2 4]
        have h18_j : 2 ^ (j' + 1) * 3 ^ (2 * (j' + 1)) = 18 ^ (j' + 1) := by
          rw [← pow9_eq_pow3_double (j' + 1), ← mul_pow_w15s 2 9 (j' + 1)]
        have hp3_sp : 3 * 3 ^ (1 + 2 * j') = 3 ^ (2 * (j' + 1)) := by
          rw [show 2 * (j' + 1) = (1 + 2 * j') + 1 by omega, Nat.pow_succ, Nat.mul_comm]
        have hprod_eq : 3 * (2 ^ (4 * r + 1 - 3 * j') * 3 ^ (1 + 2 * j')) =
            4 * (4 * 16 ^ (r - (j' + 1)) * 18 ^ (j' + 1)) := by
          calc 3 * (2 ^ (4 * r + 1 - 3 * j') * 3 ^ (1 + 2 * j'))
              = 2 ^ (4 * r + 1 - 3 * j') * (3 * 3 ^ (1 + 2 * j')) := by ac_rfl
            _ = 4 * (4 * 16 ^ (r - (j' + 1)) * 2 ^ (j' + 1)) * 3 ^ (2 * (j' + 1)) := by rw [hp2_sp, h16_rj, hp3_sp]
            _ = 4 * (4 * 16 ^ (r - (j' + 1)) * 18 ^ (j' + 1)) := by rw [Nat.mul_assoc 4, Nat.mul_assoc (4 * 16 ^ _), h18_j]
        have hpos_ge : 4 * 16 ^ (r - (j' + 1)) * 18 ^ (j' + 1) ≥ 72 := by
          have h1 := nat_pow_pos_of_pos 16 (by decide) (r - (j' + 1))
          have h2 : 18 ≤ 18 ^ (j' + 1) := by rw [Nat.pow_succ]; have := nat_pow_pos_of_pos 18 (by decide) j'; omega
          simpa using Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl 4) h1) h2
        omega
      rw [show 2 * (j' + 1) = 1 + 2 * j' + 1 by omega,
          cousinDiamond12Iter_add (1 + 2 * j') 1,
          cousinDiamond12Iter_add 1 (2 * j'),
          show cousinDiamond12Iter 1 x0 = 2 ^ (4 * r + 1) * 3 ^ 1 - 7 from hs_first, hclimb]
      exact hs_last
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, hspiral, ?_⟩
  intro terms A0 B0 C0 hnonempty
  rcases cousin_diamond11_r_block_spiral_climb_and_laurent_impossibility.2.2.2.2.2.2.2.2
    terms A0 B0 C0 hnonempty with ⟨x_bad, hx3, hxo, hs3, hnot⟩
  -- Note: instead of lifting `x_bad` (which might be in Cone 13), apply `three_family_multiterm_laurent_obstruction` directly!
  clear x_bad hx3 hxo hs3 hnot
  rcases three_family_multiterm_laurent_obstruction terms A0 B0 C0 hnonempty with
    h97 | ⟨j2, hj2⟩ | ⟨r, hr_pos, hr3⟩
  · have hs97 : cousinDiamond12Step 97 = 73 := by decide
    exact ⟨97, by decide, by decide, by rw [hs97]; decide, by rwa [hs97]⟩
  · let zj := geomSpineEntry j2
    let Mj := 4 ^ (3 * j2 + 3)
    rcases geomSpineEntry_valuations_constant j2 with ⟨h3zj1, hzj_ge, _, _, _, _⟩
    change 3 * zj + 1 = 4 ^ (3 * j2 + 4) at h3zj1
    change zj ≥ 85 at hzj_ge
    have hMj_ge64 : Mj ≥ 64 := by
      dsimp [Mj]; rw [Nat.pow_add 4 (3 * j2) 3]
      simpa using Nat.mul_le_mul_right 64 (nat_pow_pos_of_pos 4 (by decide) (3 * j2))
    have h3zj1_M : 3 * zj + 1 = 4 * Mj := by
      rw [h3zj1]; dsimp [Mj]; rw [show 3 * j2 + 4 = (3 * j2 + 3) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    let xj2 := 2 * zj - 1
    let yj2 := 2 * Mj - 1
    have hxj2_odd : xj2 % 2 = 1 := by dsimp [xj2]; omega
    have hc4_xj2 : isDiamond3Cone4 xj2 := by
      refine ⟨by dsimp [xj2]; omega, by dsimp [xj2]; omega, ?_⟩
      rw [show 3 * xj2 + 5 = 2 ^ (6 * j2 + 9) * 1 by
            rw [Nat.mul_one, show 6 * j2 + 9 = 2 * (3 * j2 + 4) + 1 by omega,
                Nat.pow_succ, ← pow4_eq_pow2_even (3 * j2 + 4), Nat.mul_comm]; dsimp [xj2]; omega]
      exact core2_pow2_mul (6 * j2 + 9) 1 (by decide) (by decide)
    have hstep_xj2 : cousinDiamond12Step xj2 = yj2 := by
      rw [d12_eq_d11_of_not_cone13 xj2 (not_cone13_of_mod8_ne_5 xj2 (by have := hc4_xj2.2.1; omega)),
          cousinDiamond11Step_eq_d10_of_not_cone12 xj2 (not_cone12_of_mod8_ne_5 xj2 (by have := hc4_xj2.2.1; omega)),
          cousinDiamond10Step_eq_d9_of_not_cone11 xj2 (not_cone11_of_mod8_ne_5 xj2 (by have := hc4_xj2.2.1; omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 xj2 (not_cone10_of_mod8_ne_5 xj2 (by have := hc4_xj2.2.1; omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 xj2 (not_cone9_of_mod8_ne_5 xj2 (by have := hc4_xj2.2.1; omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 xj2 (not_cone8_of_mod8_ne_5 xj2 (by have := hc4_xj2.2.1; omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 xj2 (not_cone7_of_mod8_ne_5 xj2 (by have := hc4_xj2.2.1; omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 xj2 (by rintro ⟨_, h256, _, _⟩; have := hc4_xj2.2.1; omega)]
      unfold cousinDiamond4Step
      by_cases hc5 : isDiamond4Cone5 xj2
      · simp only [hc5, ite_true]; dsimp [xj2, yj2]; omega
      · simp only [hc5, ite_false]; rw [cousinDiamond3Step_of_cone4_w8 xj2 hxj2_odd hc4_xj2]; dsimp [xj2, yj2]; omega
    exact ⟨xj2, by dsimp [xj2]; omega, hxj2_odd, by rw [hstep_xj2]; dsimp [yj2]; omega, by rwa [hstep_xj2]⟩
  · let xr3 := 2 * 4 ^ r - 1
    let zr := 2 * 9 ^ r - 1
    let yr3 := (3 * 9 ^ r - 1) / 2
    have hp9_ge9 : 9 ^ r ≥ 9 := by
      rw [show r = (r - 1) + 1 by omega, Nat.pow_succ]; have := nat_pow_pos_of_pos 9 (by decide) (r - 1); omega
    have hp9_m8 := pow9_mod8_eq_one_w5 r
    have hxr3_pow : xr3 = 2 ^ (2 * r + 1) * 1 - 1 := by
      dsimp [xr3]; rw [Nat.mul_one, pow4_eq_pow2_even r, Nat.pow_succ, Nat.mul_comm]
    have hglide_i : ∀ i : Nat, i ≤ 2 * r ->
        cousinDiamond12Iter i xr3 = 3 ^ i * 2 ^ (2 * r + 1 - i) - 1 ∧
        cousinDiamond12Iter i xr3 ≥ 7 ∧ (cousinDiamond12Iter i xr3) % 2 = 1 := by
      intro i hi
      have hf := cousin_diamond12_mersenne_scaled i (2 * r + 1) 1 (by omega) (by decide)
      rw [← hxr3_pow, Nat.mul_one] at hf
      have hprod_ge8 : 3 ^ i * 2 ^ (2 * r + 1 - i) ≥ 8 := by
        have h1 : 2 ^ i * 2 ^ (2 * r + 1 - i) ≤ 3 ^ i * 2 ^ (2 * r + 1 - i) :=
          Nat.mul_le_mul_right _ (pow2_le_pow3 i)
        rw [← Nat.pow_add, show i + (2 * r + 1 - i) = 2 * r + 1 by omega] at h1
        exact Nat.le_trans (pow2_mono_nat (by omega : 3 ≤ 2 * r + 1)) h1
      have hprod_ev : (3 ^ i * 2 ^ (2 * r + 1 - i)) % 2 = 0 := by
        rw [show 2 * r + 1 - i = (2 * r - i) + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc]; omega
      exact ⟨hf, by rw [hf]; omega, by rw [hf]; omega⟩
    have hiter_2r : cousinDiamond12Iter (2 * r) xr3 = zr := by
      have hf := (hglide_i (2 * r) (Nat.le_refl _)).1
      rw [hf, show 2 * r + 1 - 2 * r = 1 by omega, Nat.pow_one, ← pow9_eq_pow3_double r, Nat.mul_comm]
    have hstep_zr : cousinDiamond12Step zr = yr3 := by
      rw [d12_eq_d11_of_not_cone13 zr (not_cone13_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          cousinDiamond11Step_eq_d10_of_not_cone12 zr (not_cone12_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          cousinDiamond10Step_eq_d9_of_not_cone11 zr (not_cone11_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 zr (not_cone10_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 zr (not_cone9_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 zr (not_cone8_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 zr (not_cone7_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 zr (not_cone6_of_mod16_ne_13 zr (by dsimp [zr]; omega)),
          cousinDiamond4Step_eq_d3_of_not_cone5 zr (by rintro ⟨_, h32, _, _⟩; dsimp [zr] at h32; omega)]
      have hc3 : core3 (zr + 1) = 2 := by
        rw [show zr + 1 = 2 * 9 ^ r by dsimp [zr]; omega, core3_mul2 (9 ^ r) (by omega), (pow9_eq_v3Pow_w5 r).2]
      rw [cousinDiamond3Step_of_core3_succ_two_w8 zr (by dsimp [zr]; omega) (by dsimp [zr]; omega) hc3]
      dsimp [zr, yr3]; omega
    have hiter_2r1 : cousinDiamond12Iter (2 * r + 1) xr3 = yr3 := by
      rw [cousinDiamond12Iter_add (2 * r) 1 xr3, hiter_2r]; exact hstep_zr
    have hall : ∀ i : Nat, i < 2 * r + 1 ->
        cousinDiamond12Iter i xr3 ≥ 3 ∧ (cousinDiamond12Iter i xr3) % 2 = 1 ∧
        cousinDiamond12Step (cousinDiamond12Iter i xr3) ≥ 3 := by
      intro i hi
      by_cases hlt : i < 2 * r
      · rcases hglide_i i (by omega) with ⟨_, hge7, hodd_i⟩
        rcases hglide_i (i + 1) (by omega) with ⟨_, hge7_n, _⟩
        refine ⟨by omega, hodd_i, ?_⟩
        change cousinDiamond12Iter 1 (cousinDiamond12Iter i xr3) ≥ 3
        rw [← cousinDiamond12Iter_add i 1 xr3]; omega
      · rw [show i = 2 * r by omega, hiter_2r, hstep_zr]
        exact ⟨by dsimp [zr]; omega, by dsimp [zr]; omega, by dsimp [yr3]; omega⟩
    change ¬ laurentDescProp terms A0 B0 C0 xr3 yr3 at hr3
    rw [← hiter_2r1] at hr3
    exact exists_non_desc_along_diamond12_iter_w15 terms A0 B0 C0 (2 * r + 1) xr3 (by omega) hall hr3

set_option maxRecDepth 16384 in
/--
  Theorem W15.3h (`cousin_diamond12_counter_model_separation`, `[]` axioms):
  `T_diamond12` rejects ALL three Counter-Models (`M1 = Q_(6)^+` 5-cycle `(1, 7) -> ... -> (1, 7)`
  plus non-integers `(1649248777013, 7)` and `(9895585985333, 7)` bypassing Cone 13 by `W15.3c`,
  `M2 = Z^-` cycles `-1` and `-5 -> -7 -> -10 -> -5`, and `M3` supercritical `q = 7` 5-cycle at `5`),
  AND at the genuine `v_2(3x + 1) = 5` Cone-13 jumps `1649248777013 -> 154617072845` (`24` steps to `1`)
  and `9895585985333 -> 927711186125 -> 347891694797 -> 130459385549 -> 48922269581 -> 18345851093 ->
  429980885 -> 10077677 -> 3779129` (`ZPOS_COUSIN_DIAMOND12_CONE13_9895585985333_JUMP`, `22` steps to `1`)
  strictly increases `cousinDiamond2Phi` (`+16.22x`) directly into `Cone 12 -> Cone 11 -> ... -> Cone 5`!
-/
theorem cousin_diamond12_counter_model_separation :
    cousinDiamond12StepInt (-1) = -1 ∧
    cousinDiamond12IterInt 3 (-5) = -5 ∧
    cousinDiamond12IterParam 7 5 5 = 5 ∧
    cousinDiamond12StepQ6 (1, 7) = (5, 7) ∧
    cousinDiamond12IterQ6 5 (1, 7) = (1, 7) ∧
    cousinDiamond12StepQ6 (1649248777013, 7) = cousinDiamond11StepQ6 (1649248777013, 7) ∧
    cousinDiamond12StepQ6 (9895585985333, 7) = cousinDiamond11StepQ6 (9895585985333, 7) ∧
    isDiamond12Cone13 1649248777013 ∧
    cousinDiamond12Step 1649248777013 = 154617072845 ∧
    cousinDiamond12Iter 24 1649248777013 = 1 ∧
    isDiamond12Cone13 9895585985333 ∧
    cousinDiamond12Step 9895585985333 = 927711186125 ∧
    cousinDiamond12StepInt 9895585985333 = 927711186125 ∧
    cousinDiamond12StepQ6 (9895585985333, 1) = (927711186125, 1) ∧
    isDiamond11Cone12 927711186125 ∧
    isDiamond10Cone11 347891694797 ∧
    isDiamond9Cone10 130459385549 ∧
    isDiamond8Cone9 48922269581 ∧
    isDiamond7Cone8 18345851093 ∧
    isDiamond6Cone7 429980885 ∧
    isDiamond5Cone6 10077677 ∧
    isDiamond4Cone5 3779129 ∧
    cousinDiamond2Phi 9895585985333 < cousinDiamond2Phi 927711186125 ∧
    cousinDiamond12Iter 22 9895585985333 = 1 := by
  decide


-- ============================================================================
-- SECTION 3: Front D (Branches P2.2 & P5.3) — Complete Mod-`13122` (`2 * 3^8`,
--            `w ≥ 9`) Markov Shift Bijection, Exact `8 + 14 + 5 = 27` Prefix
--            Weight-`9` Trichotomy, & Constructive Arbitrary-Degree `∀ d ≥ 1`
--            (`≥ R^d`) Polynomial Dyadic-Window Occupancy (`W15_H4`)
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Section 3A: Complete Mod-`13122` (`2 * 3^8`) Markov Bijection (`4374 / 13122`
--             Surviving Classes on `w ≥ 9`), Prefix-Weight-`9` `8 + 14 + 5 = 27`
--             Trichotomy, & `3 ^ (w - 9)` (`j = 8`) Fiber Equidistribution
-- ----------------------------------------------------------------------------

/-- Canonical ordered list of the `4374` (`= 2 * 3^7`) surviving mod-`13122` (`= 2 * 3^8`)
    suffix-shift classes `{r < 13122 | r % 6 = 1 ∨ r % 6 = 3}` on `w ≥ 9`. -/
def survivingMod13122List : List Nat :=
  (List.range 13122).filter (fun r => r % 6 == 1 || r % 6 == 3)

private theorem mem_survivingMod13122List_iff_w15 (r : Nat) :
    r ∈ survivingMod13122List ↔ (r < 13122 ∧ (r % 6 = 1 ∨ r % 6 = 3)) := by
  unfold survivingMod13122List
  rw [List.mem_filter, List.mem_range]
  simp only [Bool.or_eq_true, beq_iff_eq]

private theorem range_six_mul_surviving_len_w15 :
    ∀ n : Nat, ((List.range (6 * n)).filter (fun r => r % 6 == 1 || r % 6 == 3)).length = 2 * n
  | 0 => rfl
  | n + 1 => by
    let p : Nat -> Bool := fun r => r % 6 == 1 || r % 6 == 3
    change ((List.range (6 * (n + 1))).filter p).length = 2 * (n + 1)
    have h6 : 6 * (n + 1) = 6 * n + 6 := by omega
    rw [h6,
        show 6 * n + 6 = (6 * n + 5) + 1 by omega, List.range_succ,
        show 6 * n + 5 = (6 * n + 4) + 1 by omega, List.range_succ,
        show 6 * n + 4 = (6 * n + 3) + 1 by omega, List.range_succ,
        show 6 * n + 3 = (6 * n + 2) + 1 by omega, List.range_succ,
        show 6 * n + 2 = (6 * n + 1) + 1 by omega, List.range_succ,
        List.range_succ]
    simp only [List.filter_append, List.length_append, List.filter]
    have m0 : p (6 * n) = false := by dsimp [p]; simp [show (6 * n) % 6 = 0 by omega]
    have m1 : p (6 * n + 1) = true := by dsimp [p]; simp [show (6 * n + 1) % 6 = 1 by omega]
    have m2 : p (6 * n + 2) = false := by dsimp [p]; simp [show (6 * n + 2) % 6 = 2 by omega]
    have m3 : p (6 * n + 3) = true := by dsimp [p]; simp [show (6 * n + 3) % 6 = 3 by omega]
    have m4 : p (6 * n + 4) = false := by dsimp [p]; simp [show (6 * n + 4) % 6 = 4 by omega]
    have m5 : p (6 * n + 5) = false := by dsimp [p]; simp [show (6 * n + 5) % 6 = 5 by omega]
    rw [m0, m1, m2, m3, m4, m5]
    simp only [List.length]
    have ih := range_six_mul_surviving_len_w15 n
    change ((List.range (6 * n)).filter p).length = 2 * n at ih
    omega

/-- Exact `8 + 14 + 5 = 27` surviving mod-`512` prefix weight-`9` predicates:
    - `isHighWeight8SurvivingMod512Bool`: `w(pref_9) ≥ 8` (`8 / 27` classes, forcing `w(u) ≥ 9` at `|u| ≥ 10`),
    - `isMedWeight7SurvivingMod512Bool`: `w(pref_9) = 7` (`14 / 27` classes, escaping at `w(u) = 8`),
    - `isLowWeight6SurvivingMod512Bool`: `w(pref_9) = 6` (`5 / 27` classes, escaping at `w(u) = 7`). -/
def isHighWeight8SurvivingMod512Bool (y : Nat) : Bool :=
  isSurvivingMod512Bool (y % 512) && decide (parityWeight (parityOfIter 9 (y % 512)) ≥ 8)

def isMedWeight7SurvivingMod512Bool (y : Nat) : Bool :=
  isSurvivingMod512Bool (y % 512) && decide (parityWeight (parityOfIter 9 (y % 512)) = 7)

def highWeight8Mod512Residues8 : List Nat :=
  survivingMod512Residues27.filter isHighWeight8SurvivingMod512Bool

def medWeight7Mod512Residues14 : List Nat :=
  survivingMod512Residues27.filter isMedWeight7SurvivingMod512Bool

private theorem take_drop_split_eq_w15 :
    ∀ (k : Nat) (xs : List Bool), xs.take k ++ xs.drop k = xs
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, x :: xs => by
    simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append,
               take_drop_split_eq_w15 k xs]

private theorem take_len_of_ge_w15 :
    ∀ (k : Nat) (xs : List Bool), k ≤ xs.length -> (xs.take k).length = k
  | 0, _, _ => rfl
  | _ + 1, [], h => by simp at h
  | k + 1, _ :: xs, h => by
    simp only [List.length_cons] at h
    simp only [List.take_succ_cons, List.length_cons, take_len_of_ge_w15 k xs (by omega)]

private theorem len10_core_mod512_prefix9_w15
    (p9 freeBits : List Bool) (q : Nat)
    (hp9_len : p9.length = 9)
    (hu : IsCoreParityWord (p9 ++ freeBits ++ [true])) :
    parityOfIter 9 (exactBackwardQuotient 1 (p9 ++ freeBits ++ [true]) q % 512) = p9 := by
  let u := p9 ++ freeBits ++ [true]
  let y := exactBackwardQuotient 1 u q
  let K := backwardOneTotalSteps u q
  let shift := canonicalSuffixShift u 1 + q * (2 * 3 ^ (parityWeight u - 1))
  have hu_len : u.length = 9 + (freeBits.length + 1) := by
    dsimp [u]; rw [List.length_append, List.length_append, hp9_len, List.length_singleton]
    omega
  have hK_ge10 : K ≥ 10 := by unfold K backwardOneTotalSteps; omega
  let v := u ++ List.replicate shift false
  have hv_len : v.length = K := by
    dsimp [v]; rw [List.length_append, List.length_replicate]; rfl
  rcases one_generator_pos_odd_and_reaches_one u q hu with ⟨_, _, heq, _⟩
  change 2 ^ K = 3 ^ parityWeight u * y + affineCarry u at heq
  rcases affineCarry_append_replicate_false u shift with ⟨hwt_v, hcar_v⟩
  have hv_aff : 2 ^ v.length * 1 = 3 ^ parityWeight v * y + affineCarry v := by
    rw [Nat.mul_one, hv_len, hwt_v, hcar_v]; exact heq
  have hv_par := eq_parityOfIter_of_nat_affine v y 1 hv_aff
  rw [hv_len] at hv_par
  have hKs9 : K = 9 + (K - 9) := by omega
  have hpar_sp := parityOfIter_append_split 9 (K - 9) y
  rw [← hKs9, ← hv_par] at hpar_sp
  have hv_p9 : v = p9 ++ (freeBits ++ [true] ++ List.replicate shift false) := by
    dsimp [v, u]
    rw [List.append_assoc p9 freeBits [true],
        List.append_assoc p9 (freeBits ++ [true]) (List.replicate shift false)]
  rw [hv_p9] at hpar_sp
  have hlen9 : p9.length = (parityOfIter 9 y).length := by
    rw [hp9_len, parityOfIter_length]
  have hp9_eq : parityOfIter 9 y = p9 :=
    (list_append_inj_left_eq_len _ _ _ _ hlen9 hpar_sp).1.symm
  have hy_div9 : y = y % 512 + 2 ^ 9 * (y / 512) := by
    have hdm := (Nat.div_add_mod y 512).symm
    rw [show (2 : Nat) ^ 9 = 512 from rfl]; omega
  have hpar9_mod : parityOfIter 9 y = parityOfIter 9 (y % 512) := by
    conv => lhs; rw [hy_div9]
    exact parityOfIter_mod_pow2_shift 9 (y % 512) (y / 512)
  rw [← hpar9_mod, hp9_eq]

private theorem pow_mod_eq_pow_mod_w15 (b m : Nat) :
    ∀ e : Nat, (b ^ e) % m = ((b % m) ^ e) % m
  | 0 => rfl
  | e + 1 => by
    rw [Nat.pow_succ b e, Nat.pow_succ (b % m) e, Nat.mul_mod (b ^ e) b m,
        pow_mod_eq_pow_mod_w15 b m e, Nat.mul_mod ((b % m) ^ e % m) (b % m) m,
        Nat.mod_mod, ← Nat.mul_mod ((b % m) ^ e) (b % m) m]

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 131072 in
/--
  Theorem W15.4a (`markovShift_mod13122_bijection_and_prefix8_weight9_dichotomy`,
  `zero custom axioms`):
  Complete Mod-`13122` (`2 * 3^8`) Markov Bijection onto `4374` Surviving Classes (`w ≥ 9`),
  Exact `8 + 14 + 5 = 27` Mod-`512` Prefix-Weight-`9` Trichotomy (`8` High-Weight Prefixes Force
  `w(u) ≥ 9` vs `14` Medium-Weight Escape `ZPOS_DYADIC_LEN16_WEIGHT8_MED_PREFIX_ESCAPE` at `1340663463`),
  Mod-`13122` Suffix Locks (`6561`, `10935`, & `{2187, 6561, 10935}`), & `3 ^ (w - 9)` (`j = 8`)
  Multi-Step Fiber Equidistribution (`Branch P5.3`, `W15_H4`).
-/
theorem markovShift_mod13122_bijection_and_prefix8_weight9_dichotomy :
    ((∀ (w a : Nat), w ≥ 8 -> a < 2 * 3 ^ (w - 1) ->
        markovShiftTrue w a % 13122 = markovShiftTrue 8 (a % 4374) % 13122) ∧
     survivingMod13122List.length = 4374 ∧
     (∀ x1 x2 : Fin 4374,
        markovShiftTrue 8 x1.val % 13122 = markovShiftTrue 8 x2.val % 13122 -> x1 = x2) ∧
     (∀ x : Fin 4374,
        markovShiftTrue 8 x.val % 13122 ∈ survivingMod13122List) ∧
     (∀ r ∈ survivingMod13122List,
        ∃ x : Fin 4374, markovShiftTrue 8 x.val % 13122 = r)) ∧
    (highWeight8Mod512Residues8.length = 8 ∧
     medWeight7Mod512Residues14.length = 14 ∧
     lowWeight6Mod512Residues5.length = 5 ∧
     (∀ r : Fin 512, isSurvivingMod512Bool r.val = true ->
        (isHighWeight8SurvivingMod512Bool r.val = true ∧
         isMedWeight7SurvivingMod512Bool r.val = false ∧
         isLowWeight6SurvivingMod512Bool r.val = false) ∨
        (isMedWeight7SurvivingMod512Bool r.val = true ∧
         isHighWeight8SurvivingMod512Bool r.val = false ∧
         isLowWeight6SurvivingMod512Bool r.val = false) ∨
        (isLowWeight6SurvivingMod512Bool r.val = true ∧
         isHighWeight8SurvivingMod512Bool r.val = false ∧
         isMedWeight7SurvivingMod512Bool r.val = false)) ∧
     (∀ u : List Bool, IsCoreParityWord u -> parityWeight u ≥ 9 ->
        canonicalSuffixShift u 1 % 13122 ∈ survivingMod13122List) ∧
     (∀ (u : List Bool) (q : Nat),
        IsCoreParityWord u -> u.length ≥ 10 ->
        isHighWeight8SurvivingMod512Bool (exactBackwardQuotient 1 u q) = true ->
        parityWeight u ≥ 9 ∧ canonicalSuffixShift u 1 % 13122 ∈ survivingMod13122List) ∧
     (let u_esc8 : List Bool :=
        [true, true, true, false, true, true, false, true, true,
         false, false, false, false, false, false, true]
      u_esc8.length = 16 ∧
      parityWeight u_esc8 = 8 ∧
      IsFirstHitOnePair u_esc8 0 ∧
      exactBackwardQuotient 1 u_esc8 0 = 1340663463 ∧
      IsSurvivingMod373248Class (exactBackwardQuotient 1 u_esc8 0) ∧
      isMedWeight7SurvivingMod512Bool (exactBackwardQuotient 1 u_esc8 0) = true)) ∧
    ((∀ pref : List Bool,
        canonicalSuffixShift (pref ++ List.replicate 8 true) 1 % 13122 = 2187 ∨
        canonicalSuffixShift (pref ++ List.replicate 8 true) 1 % 13122 = 6561 ∨
        canonicalSuffixShift (pref ++ List.replicate 8 true) 1 % 13122 = 10935) ∧
     (∀ pref : List Bool,
        canonicalSuffixShift (pref ++ List.replicate 9 true) 1 % 13122 = 6561 ∧
        canonicalSuffixShift (pref ++ ([true, false] ++ List.replicate 8 true)) 1 % 13122 = 10935)) ∧
    (∀ (tail : List Bool) (w r0 : Nat),
      w ≥ 9 -> r0 < 13122 ->
      let Mk := 2 * 3 ^ (8 + parityWeight tail)
      let N := 3 ^ (w - 9)
      let base := iterMarkovShift tail w r0 % Mk
      (∀ t : Nat, t < N ->
        ∃ q : Nat, q < N ∧ iterMarkovShift tail w (r0 + 13122 * t) = base + Mk * q) ∧
      (∀ q : Nat, q < N ->
        ∃ t : Nat, t < N ∧
          iterMarkovShift tail w (r0 + 13122 * t) = base + Mk * q ∧
          ∀ t' : Nat, t' < N ->
            iterMarkovShift tail w (r0 + 13122 * t') = base + Mk * q -> t' = t)) := by
  have h4374_eq : (2 : Nat) * 3 ^ (8 - 1) = 4374 := by decide
  have h13122_eq : (2 : Nat) * 3 ^ 8 = 13122 := by decide
  have hcongr13122 : ∀ (w a : Nat), w ≥ 8 -> a < 2 * 3 ^ (w - 1) ->
      markovShiftTrue w a % 13122 = markovShiftTrue 8 (a % 4374) % 13122 := by
    intro w a hw8 ha_lt
    have hr_lt : a % 4374 < 2 * 3 ^ (8 - 1) := by rw [h4374_eq]; exact Nat.mod_lt a (by decide)
    exact markovShiftTrue_contraction_mod_pow3 7 w 8 a (a % 4374)
      (by omega) (by decide) ha_lt hr_lt (by simp)
  have hlen13122 : survivingMod13122List.length = 4374 := by
    unfold survivingMod13122List
    have h := range_six_mul_surviving_len_w15 2187
    simpa using h
  have hinj4374 : ∀ x1 x2 : Fin 4374,
      markovShiftTrue 8 x1.val % 13122 = markovShiftTrue 8 x2.val % 13122 -> x1 = x2 := by
    intro x1 x2 heq
    have hx1 : x1.val < 2 * 3 ^ (8 - 1) := by rw [h4374_eq]; exact x1.isLt
    have hx2 : x2.val < 2 * 3 ^ (8 - 1) := by rw [h4374_eq]; exact x2.isLt
    have hm1_lt : markovShiftTrue 8 x1.val < 13122 := by
      rw [← h13122_eq]
      exact (canonicalSuffixShift_markov_bijection_and_mod6_lock.2.1 8 x1.val (by decide) hx1).1
    have hm2_lt : markovShiftTrue 8 x2.val < 13122 := by
      rw [← h13122_eq]
      exact (canonicalSuffixShift_markov_bijection_and_mod6_lock.2.1 8 x2.val (by decide) hx2).1
    rw [Nat.mod_eq_of_lt hm1_lt, Nat.mod_eq_of_lt hm2_lt] at heq
    exact Fin.ext (canonicalSuffixShift_markov_bijection_and_mod6_lock.2.2.1 8 x1.val x2.val
      (by decide) hx1 hx2 heq)
  have hmem4374 : ∀ x : Fin 4374, markovShiftTrue 8 x.val % 13122 ∈ survivingMod13122List := by
    intro x
    have hx : x.val < 2 * 3 ^ (8 - 1) := by rw [h4374_eq]; exact x.isLt
    rcases canonicalSuffixShift_markov_bijection_and_mod6_lock.2.1 8 x.val (by decide) hx with
      ⟨hlt, hm6⟩
    rw [h13122_eq] at hlt
    rw [Nat.mod_eq_of_lt hlt]
    exact (mem_survivingMod13122List_iff_w15 _).mpr ⟨hlt, hm6⟩
  have hsurj4374 : ∀ r ∈ survivingMod13122List,
      ∃ x : Fin 4374, markovShiftTrue 8 x.val % 13122 = r := by
    intro r hr
    rcases (mem_survivingMod13122List_iff_w15 r).mp hr with ⟨hr_lt, hr_m6⟩
    rcases canonicalSuffixShift_markov_bijection_and_mod6_lock.2.2.2.1 8 r (by decide)
      (by rw [h13122_eq]; exact hr_lt) hr_m6 with ⟨a, ha_lt, ha_eq⟩
    rw [h4374_eq] at ha_lt
    refine ⟨⟨a, ha_lt⟩, ?_⟩
    dsimp only
    rw [ha_eq, Nat.mod_eq_of_lt hr_lt]
  have hconf9 : ∀ u : List Bool, IsCoreParityWord u -> parityWeight u ≥ 9 ->
      canonicalSuffixShift u 1 % 13122 ∈ survivingMod13122List := by
    intro u hu hw9
    rcases list_eq_append_true_of_reverse_head u hu.2 with ⟨v, rfl⟩
    have hw_v : parityWeight v ≥ 8 := by
      rw [parityWeight_append] at hw9
      have h1 : parityWeight [true] = 1 := rfl
      rw [h1] at hw9; omega
    have hrec : canonicalSuffixShift (v ++ [true]) 1 =
        markovShiftTrue (parityWeight v) (canonicalSuffixShift v 1) :=
      (canonicalSuffixShift_append_markov_recurrence.2.2 v (by omega)).2.2.1
    have ha_lt := (canonicalSuffixShift_spec_unique v 1 (by omega) (by decide)).1
    rw [hrec, hcongr13122 (parityWeight v) (canonicalSuffixShift v 1) hw_v ha_lt]
    exact hmem4374 ⟨canonicalSuffixShift v 1 % 4374, Nat.mod_lt _ (by decide)⟩
  have h512_trich : ∀ r : Fin 512, isSurvivingMod512Bool r.val = true ->
      (isHighWeight8SurvivingMod512Bool r.val = true ∧
       isMedWeight7SurvivingMod512Bool r.val = false ∧
       isLowWeight6SurvivingMod512Bool r.val = false) ∨
      (isMedWeight7SurvivingMod512Bool r.val = true ∧
       isHighWeight8SurvivingMod512Bool r.val = false ∧
       isLowWeight6SurvivingMod512Bool r.val = false) ∨
      (isLowWeight6SurvivingMod512Bool r.val = true ∧
       isHighWeight8SurvivingMod512Bool r.val = false ∧
       isMedWeight7SurvivingMod512Bool r.val = false) := by
    have hgrid : ∀ (hi : Fin 8) (lo : Fin 64),
        let rv := 64 * hi.val + lo.val
        isSurvivingMod512Bool rv = true ->
        (isHighWeight8SurvivingMod512Bool rv = true ∧
         isMedWeight7SurvivingMod512Bool rv = false ∧
         isLowWeight6SurvivingMod512Bool rv = false) ∨
        (isMedWeight7SurvivingMod512Bool rv = true ∧
         isHighWeight8SurvivingMod512Bool rv = false ∧
         isLowWeight6SurvivingMod512Bool rv = false) ∨
        (isLowWeight6SurvivingMod512Bool rv = true ∧
         isHighWeight8SurvivingMod512Bool rv = false ∧
         isMedWeight7SurvivingMod512Bool rv = false) := by
      decide
    intro r hr
    have hhi : r.val / 64 < 8 := by have := r.isLt; omega
    have hlo : r.val % 64 < 64 := Nat.mod_lt r.val (by decide)
    have hg := hgrid ⟨r.val / 64, hhi⟩ ⟨r.val % 64, hlo⟩
    dsimp only at hg
    rw [Nat.div_add_mod r.val 64] at hg
    exact hg hr
  have hlen10_high8 : ∀ (u : List Bool) (q : Nat),
      IsCoreParityWord u -> u.length ≥ 10 ->
      isHighWeight8SurvivingMod512Bool (exactBackwardQuotient 1 u q) = true ->
      parityWeight u ≥ 9 ∧ canonicalSuffixShift u 1 % 13122 ∈ survivingMod13122List := by
    intro u q hu hlen10 hhigh
    rcases list_eq_append_true_of_reverse_head u hu.2 with ⟨pre, rfl⟩
    have hpre_ge9 : pre.length ≥ 9 := by
      rw [List.length_append, List.length_singleton] at hlen10; omega
    let p9 := pre.take 9
    let fb := pre.drop 9
    have hp9_len : p9.length = 9 := take_len_of_ge_w15 9 pre hpre_ge9
    have hpre_sp : p9 ++ fb = pre := take_drop_split_eq_w15 9 pre
    have hu' : IsCoreParityWord (p9 ++ fb ++ [true]) := by rwa [hpre_sp]
    have hp9_eq : parityOfIter 9 (exactBackwardQuotient 1 (p9 ++ fb ++ [true]) q % 512) = p9 :=
      len10_core_mod512_prefix9_w15 p9 fb q hp9_len hu'
    rw [hpre_sp] at hp9_eq
    unfold isHighWeight8SurvivingMod512Bool at hhigh
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hhigh
    have hhigh2 := hhigh.2
    have hw_p9 : parityWeight p9 ≥ 8 := by rwa [hp9_eq] at hhigh2
    have hw9 : parityWeight (pre ++ [true]) ≥ 9 := by
      rw [← hpre_sp, parityWeight_append, parityWeight_append]
      have h1 : parityWeight [true] = 1 := rfl
      rw [h1]; omega
    exact ⟨hw9, hconf9 (pre ++ [true]) hu hw9⟩
  have hesc8_cert :
      let u_esc8 : List Bool :=
        [true, true, true, false, true, true, false, true, true,
         false, false, false, false, false, false, true]
      u_esc8.length = 16 ∧
      parityWeight u_esc8 = 8 ∧
      IsFirstHitOnePair u_esc8 0 ∧
      exactBackwardQuotient 1 u_esc8 0 = 1340663463 ∧
      IsSurvivingMod373248Class (exactBackwardQuotient 1 u_esc8 0) ∧
      isMedWeight7SurvivingMod512Bool (exactBackwardQuotient 1 u_esc8 0) = true := by
    dsimp only
    let u_esc8 : List Bool :=
      [true, true, true, false, true, true, false, true, true,
       false, false, false, false, false, false, true]
    have hfh_esc : IsFirstHitOnePair u_esc8 0 :=
      (first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.2 u_esc8 ⟨rfl, rfl⟩).mpr (by decide)
    have hq_val : exactBackwardQuotient 1 u_esc8 0 = 1340663463 := by decide
    have hb_surv : isSurvivingMod373248Bool 1340663463 = true := by decide
    have hmed_b : isMedWeight7SurvivingMod512Bool 1340663463 = true := by decide
    rw [hq_val]
    exact ⟨rfl, rfl, hfh_esc, rfl, isSurvivingMod373248Bool_imp_class _ hb_surv, hmed_b⟩
  refine ⟨⟨hcongr13122, hlen13122, hinj4374, hmem4374, hsurj4374⟩,
          ⟨rfl, rfl, rfl, h512_trich, hconf9, hlen10_high8, hesc8_cert⟩, ⟨?_, ?_⟩, ?_⟩
  · intro pref
    have hm4374 := first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.1 8 pref (by decide)
    change canonicalSuffixShift (pref ++ List.replicate 8 true) 1 % 4374 = 2187 at hm4374
    let A := canonicalSuffixShift (pref ++ List.replicate 8 true) 1 % 13122
    have hA_lt : A < 13122 := Nat.mod_lt _ (by decide)
    have hA_m4374 : A % 4374 = 2187 := by
      dsimp only [A]
      rw [Nat.mod_mod_of_dvd _ ⟨3, by decide⟩]
      exact hm4374
    have hdm := (Nat.div_add_mod A 4374).symm
    change canonicalSuffixShift (pref ++ List.replicate 8 true) 1 % 13122 = 2187 ∨
      canonicalSuffixShift (pref ++ List.replicate 8 true) 1 % 13122 = 6561 ∨
      canonicalSuffixShift (pref ++ List.replicate 8 true) 1 % 13122 = 10935
    change A = 2187 ∨ A = 6561 ∨ A = 10935
    omega
  · intro pref
    have ha1 := first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.1 9 pref (by decide)
    let u10 : List Bool := [true, false] ++ List.replicate 8 true
    have ha2 := canonicalSuffixShift_mod18_and_pow3_memory_annihilation.2.1 8 pref u10 (by decide)
    have hu10_sh : canonicalSuffixShift u10 1 = 10935 := by
      rcases canonicalSuffixShift_spec_unique u10 1 (by decide) (by decide) with ⟨_, _, huniq⟩
      symm
      apply huniq 10935 (by decide)
      have hlen10 : u10.length = 10 := rfl
      have hwt9 : parityWeight u10 = 9 := rfl
      rw [Nat.mul_one, hlen10, hwt9, show (3 : Nat) ^ 9 = 19683 from rfl,
          show 10 + 10935 = 10 + 243 * 45 from rfl, Nat.pow_add 2 10 (243 * 45),
          ← pow_pow_eq_mul_w5 2 243 45, Nat.mul_mod, pow_mod_eq_pow_mod_w15 (2 ^ 243) 19683 45]
      decide
    have hv2 : canonicalSuffixShift u10 1 % 13122 = 10935 := by rw [hu10_sh]
    exact ⟨by simpa using ha1, by simpa [u10] using ha2.trans hv2⟩
  · intro tail w r0 hw9 hr0
    have hm13122 : (2 : Nat) * 3 ^ 8 = 13122 := by decide
    have hw_sub : w - 1 - 8 = w - 9 := by omega
    have heq := markovShift_mod18_bijection_and_multistep_fiber_equidistribution.2.2
      tail 8 w r0 (by omega) (by rw [hm13122]; exact hr0)
    dsimp only at heq ⊢
    rwa [hm13122, hw_sub] at heq

-- ----------------------------------------------------------------------------
-- Section 3B: Constructive `(d + 1)`-Zero-Run Family `uWinPoly d R M idx` &
--             Unconditional Arbitrary-Degree Polynomial (`≥ R ^ d`) Surviving-Leaf
--             Dyadic-Window Occupancy at Linear Horizon `L_max ≥ M` (`W15_H4`)
-- ----------------------------------------------------------------------------

/-- Shift adjustment `delta ∈ {0, 1, 2, 3}` ensuring `(b0 + 1 + delta) % 6 ∈ {2, 4}`,
    so `q3 := (2 ^ (b0 + 1 + delta) - 1) / 3` satisfies `3 * q3 + 1 = 2 ^ (b0 + 1 + delta)`
    AND `q3 % 3 ≠ 0` simultaneously across all bit-lengths `b0`. -/
def dyadicPolyShiftDelta (b0 : Nat) : Nat :=
  let r6 := (b0 + 1) % 6
  if r6 = 0 then 2 else if r6 = 5 then 3 else (b0 + 1) % 2

/-- Extract `m` base-`R` digits of `v` scaled by `2` (`[2 * d_0, 2 * d_1, ..., 2 * d_{m-1}]`). -/
def baseREvenDigits : Nat -> Nat -> Nat -> List Nat
  | 0, _, _ => []
  | m + 1, R, v => (2 * (v % R)) :: baseREvenDigits m R (v / R)

/-- Encode a list of zero-run lengths `[k_1, ..., k_r]` as `0^{k_1} ++ [1] ++ ... ++ 0^{k_r} ++ [1]`. -/
def zeroRunsSuffix : List Nat -> List Bool
  | [] => []
  | k :: ks => List.replicate k false ++ (true :: zeroRunsSuffix ks)

/-- Minimum dyadic window scale `M_min(d, R) = 2 * R * (2 * 3 ^ (d + 12)) + 2 * d * R + 30`
    above which `[2^M, 2^(M+1))` contains at least `R ^ d` surviving `Mod373248` first-hit leaves. -/
def dyadicPolyWindowMinM (d R : Nat) : Nat :=
  2 * R * (2 * 3 ^ (d + 12)) + 2 * d * R + 30

/-- Zero-run length list `[k_1, ..., k_d, k_{d+1}]` for `uWinPoly d R M idx`. -/
def uWinPolyRuns (d R M idx : Nat) : List Nat :=
  let w := d + 10
  let b0 := binBitLength (3 ^ w)
  let delta := dyadicPolyShiftDelta b0
  let a := b0 + delta
  let q3 := (2 ^ (a + 1) - 1) / 3
  let period := 2 * 3 ^ (d + 12)
  let L := M - delta
  let ks := baseREvenDigits (d - 1) R (idx / R)
  let u_pref := List.replicate 9 true ++ zeroRunsSuffix ks
  let A_num := q3 * 2 ^ (L - 1) - (3 * affineCarry u_pref + 3 ^ (w - 1))
  let t_base := dlog2ModPow3 (w + 3) (A_num % 3 ^ (w + 3))
  let t_pos := t_base + (R + idx % R) * period
  let kd := t_pos - u_pref.length
  let kd1 := (L - 2) - t_pos
  ks ++ [kd, kd1]

/-- Constructive `(d + 1)`-zero-run 2-adic/3-adic carry-decoded surviving `Mod373248` first-hit
    `q = 0` family `uWinPoly d R M idx` inside `[2^M, 2^(M+1))` at linear length `L = M - delta ≤ M`
    and parity weight `w = d + 10` (`∀ d ≥ 1, ∀ R ≥ 1, ∀ idx < R ^ d`). -/
def uWinPoly (d R M idx : Nat) : List Bool :=
  List.replicate 9 true ++ zeroRunsSuffix (uWinPolyRuns d R M idx)

private def natSumListW15 : List Nat -> Nat
  | [] => 0
  | x :: xs => x + natSumListW15 xs

private theorem baseREvenDigits_spec :
    ∀ (m R : Nat), R ≥ 1 ->
      (∀ v : Nat,
        (baseREvenDigits m R v).length = m ∧
        natSumListW15 (baseREvenDigits m R v) ≤ 2 * m * R) ∧
      (∀ v1 v2 : Nat, v1 < R ^ m -> v2 < R ^ m ->
        baseREvenDigits m R v1 = baseREvenDigits m R v2 -> v1 = v2)
  | 0, R, _ => by
    refine ⟨fun _ => ⟨rfl, by simp [baseREvenDigits, natSumListW15]⟩, ?_⟩
    intro v1 v2 h1 h2 _
    rw [Nat.pow_zero] at h1 h2; omega
  | m + 1, R, hR => by
    rcases baseREvenDigits_spec m R hR with ⟨hb_len, hb_inj⟩
    refine ⟨?_, ?_⟩
    · intro v
      rcases hb_len (v / R) with ⟨hl, hs⟩
      dsimp only [baseREvenDigits, List.length_cons, natSumListW15]
      rw [hl]
      have hmod : v % R < R := Nat.mod_lt v (by omega)
      have hexp : 2 * (m + 1) * R = 2 * R + 2 * m * R := by
        rw [Nat.mul_add 2 m 1, Nat.mul_one, Nat.add_mul, Nat.add_comm]
      exact ⟨rfl, by omega⟩
    · intro v1 v2 hv1 hv2 heq
      simp only [baseREvenDigits, List.cons.injEq] at heq
      rcases heq with ⟨hm_eq, htl_eq⟩
      have hr_eq : v1 % R = v2 % R := by omega
      have hdiv_lt : ∀ v : Nat, v < R ^ (m + 1) -> v / R < R ^ m := by
        intro v hv
        rw [Nat.pow_succ] at hv
        by_cases hlt : v / R < R ^ m
        · exact hlt
        · exfalso
          have hge : R ^ m ≤ v / R := by omega
          have hmul := Nat.mul_le_mul_left R hge
          rw [Nat.mul_comm R (R ^ m)] at hmul
          have hdm := (Nat.div_add_mod v R).symm
          omega
      have hq_eq : v1 / R = v2 / R :=
        hb_inj (v1 / R) (v2 / R) (hdiv_lt v1 hv1) (hdiv_lt v2 hv2) htl_eq
      have hdm1 := (Nat.div_add_mod v1 R).symm
      have hdm2 := (Nat.div_add_mod v2 R).symm
      rw [hq_eq, hr_eq] at hdm1
      omega

private theorem replicate_false_cons_true_inj_w15 :
    ∀ (a b : Nat) (xs ys : List Bool),
      List.replicate a false ++ (true :: xs) = List.replicate b false ++ (true :: ys) ->
      a = b ∧ xs = ys
  | 0, 0, xs, ys, h => ⟨rfl, by simpa using h⟩
  | 0, _ + 1, _, _, h => by simp [List.replicate_succ] at h
  | _ + 1, 0, _, _, h => by simp [List.replicate_succ] at h
  | a + 1, b + 1, xs, ys, h => by
    simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
    rcases replicate_false_cons_true_inj_w15 a b xs ys h with ⟨hab, hxy⟩
    exact ⟨congrArg Nat.succ hab, hxy⟩

private theorem zeroRunsSuffix_append_and_inj :
    (∀ xs ys : List Nat, zeroRunsSuffix (xs ++ ys) = zeroRunsSuffix xs ++ zeroRunsSuffix ys) ∧
    (∀ xs ys : List Nat, zeroRunsSuffix xs = zeroRunsSuffix ys -> xs = ys) := by
  have happ : ∀ xs ys : List Nat, zeroRunsSuffix (xs ++ ys) = zeroRunsSuffix xs ++ zeroRunsSuffix ys := by
    intro xs; induction xs with
    | nil => intro ys; rfl
    | cons k tl ih =>
      intro ys
      simp only [List.cons_append, zeroRunsSuffix, ih ys, List.append_assoc]
  have hinj : ∀ xs ys : List Nat, zeroRunsSuffix xs = zeroRunsSuffix ys -> xs = ys := by
    intro xs; induction xs with
    | nil =>
      intro ys h
      cases ys with
      | nil => rfl
      | cons k tl =>
        exfalso
        have hlen := congrArg List.length h
        simp [zeroRunsSuffix] at hlen
    | cons k1 tl1 ih =>
      intro ys h
      cases ys with
      | nil =>
        exfalso
        have hlen := congrArg List.length h
        simp [zeroRunsSuffix] at hlen
      | cons k2 tl2 =>
        simp only [zeroRunsSuffix] at h
        rcases replicate_false_cons_true_inj_w15 k1 k2 _ _ h with ⟨hk, htl⟩
        rw [hk, ih tl2 htl]
  exact ⟨happ, hinj⟩

private theorem zeroRunsSuffix_len_wt_carry_bound :
    ∀ (ks : List Nat) (acc : List Bool),
      affineCarry acc < 4 ^ parityWeight acc * 2 ^ acc.length ->
      let w := acc ++ zeroRunsSuffix ks
      w.length = acc.length + ks.length + natSumListW15 ks ∧
      parityWeight w = parityWeight acc + ks.length ∧
      affineCarry w < 4 ^ parityWeight w * 2 ^ w.length
  | [], acc, hbd => by
    dsimp only
    rw [zeroRunsSuffix, List.append_nil]
    exact ⟨by simp [natSumListW15], by simp, hbd⟩
  | k :: tl, acc, hbd => by
    dsimp only
    let acc1 := acc ++ List.replicate k false ++ [true]
    have hstep_eq : acc ++ zeroRunsSuffix (k :: tl) = acc1 ++ zeroRunsSuffix tl := by
      dsimp only [acc1, zeroRunsSuffix]
      simp [List.append_assoc]
    rcases affineCarry_append_replicate_false acc k with ⟨hwt0, hcar0⟩
    have hlen0 : (acc ++ List.replicate k false).length = acc.length + k := by
      rw [List.length_append, List.length_replicate]
    have hlen1 : acc1.length = acc.length + k + 1 := by
      dsimp [acc1]; rw [List.length_append, hlen0, List.length_singleton]
    have hwt1 : parityWeight acc1 = parityWeight acc + 1 := by
      dsimp [acc1]; rw [parityWeight_append, hwt0]; rfl
    have hcar1 : affineCarry acc1 = 3 * affineCarry acc + 2 ^ (acc.length + k) := by
      dsimp [acc1]
      rw [affineCarry_append, hcar0, hlen0]
      have hc1 : affineCarry [true] = 1 := rfl
      have hw1 : parityWeight [true] = 1 := rfl
      rw [hc1, hw1]; omega
    have hbd1 : affineCarry acc1 < 4 ^ parityWeight acc1 * 2 ^ acc1.length := by
      rw [hcar1, hwt1, hlen1]
      have hm_k : 2 ^ acc.length ≤ 2 ^ (acc.length + k) := pow2_mono_nat (by omega)
      have h4_pos : 1 ≤ 4 ^ parityWeight acc := nat_pow_pos_of_pos 4 (by decide) _
      have ht1 : 3 * affineCarry acc < 3 * (4 ^ parityWeight acc * 2 ^ (acc.length + k)) := by
        calc 3 * affineCarry acc
            < 3 * (4 ^ parityWeight acc * 2 ^ acc.length) :=
              Nat.mul_lt_mul_of_pos_left hbd (by decide)
          _ ≤ 3 * (4 ^ parityWeight acc * 2 ^ (acc.length + k)) :=
              Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left _ hm_k)
      have ht2 : 2 ^ (acc.length + k) ≤ 4 ^ parityWeight acc * 2 ^ (acc.length + k) := by
        simpa using Nat.mul_le_mul_right (2 ^ (acc.length + k)) h4_pos
      calc 3 * affineCarry acc + 2 ^ (acc.length + k)
          < 3 * (4 ^ parityWeight acc * 2 ^ (acc.length + k)) +
              4 ^ parityWeight acc * 2 ^ (acc.length + k) := Nat.add_lt_add_of_lt_of_le ht1 ht2
        _ = 4 ^ (parityWeight acc + 1) * 2 ^ (acc.length + k) := by
              rw [Nat.pow_succ 4 (parityWeight acc), Nat.mul_comm (4 ^ parityWeight acc) 4, Nat.mul_assoc 4]
              generalize 4 ^ parityWeight acc * 2 ^ (acc.length + k) = X; omega
        _ ≤ 4 ^ (parityWeight acc + 1) * 2 ^ (acc.length + k + 1) :=
              Nat.mul_le_mul_left _ (pow2_mono_nat (by omega))
    rcases zeroRunsSuffix_len_wt_carry_bound tl acc1 hbd1 with ⟨ih_len, ih_wt, ih_bd⟩
    rw [hstep_eq]
    refine ⟨?_, ?_, ih_bd⟩
    · rw [ih_len, hlen1]; simp only [List.length_cons, natSumListW15]; omega
    · rw [ih_wt, hwt1]; simp only [List.length_cons]; omega

private theorem binBitLength_pow2_sandwich_w15 :
    ∀ (fuel n : Nat), n ≥ 1 -> n ≤ fuel ->
      binBitLength n ≥ 1 ∧ 2 ^ (binBitLength n - 1) ≤ n ∧ n < 2 ^ binBitLength n
  | 0, _, hn, hle => by omega
  | fuel + 1, n, hn, hle => by
    by_cases hn1 : n = 1
    · subst hn1; decide
    · let k := n / 2
      have hk_pos : k ≥ 1 := by dsimp [k]; omega
      have hbl_n : binBitLength n = 1 + binBitLength k := binBitLength_step_pos n hn
      rcases binBitLength_pow2_sandwich_w15 fuel k hk_pos (by dsimp [k]; omega) with
        ⟨hbl_k, hk_lo, hk_hi⟩
      rw [hbl_n]
      have hsub : 1 + binBitLength k - 1 = (binBitLength k - 1) + 1 := by omega
      refine ⟨by omega, ?_, ?_⟩
      · rw [hsub, Nat.pow_succ]
        have hm := Nat.mul_le_mul_right 2 hk_lo
        dsimp [k] at hm; omega
      · rw [Nat.add_comm 1 (binBitLength k), Nat.pow_succ]
        have hm := Nat.mul_lt_mul_of_pos_right hk_hi (by decide : 0 < 2)
        dsimp [k] at hm; omega

private theorem pow3_bitlength_strict_bounds_w15 (w : Nat) (hw : w ≥ 11) :
    let b0 := binBitLength (3 ^ w)
    b0 ≥ 18 ∧ b0 ≤ 2 * w ∧ 3 ^ w + 1 ≤ 2 ^ b0 ∧ 2 ^ b0 < 2 * 3 ^ w := by
  dsimp only
  let b0 := binBitLength (3 ^ w)
  have hp3_ge11 : 3 ^ w ≥ 177147 := by
    have h := nat_pow_mono_exp_pos 3 11 w (by decide) hw
    simpa using h
  have hb0_ge18 : b0 ≥ 18 := by
    have h17 : (2 : Nat) ^ 17 ≤ 3 ^ w := by omega
    have hm := binBitLength_mono (2 ^ 17) (3 ^ w) h17
    rw [(binBitLength_pow2_and_pred 17).1] at hm
    exact hm
  have hp3_le4 : 3 ^ w ≤ 2 ^ (2 * w) - 1 := by
    have hlt : 3 ^ w < 4 ^ w := by
      have hst : ∀ m : Nat, m ≥ 1 -> 3 ^ m < 4 ^ m := by
        intro m hm; induction m with
        | zero => omega
        | succ m' ihm =>
          cases m' with
          | zero => decide
          | succ m'' =>
            rw [Nat.pow_succ 3, Nat.pow_succ 4]
            exact Nat.lt_of_lt_of_le
              (Nat.mul_lt_mul_of_pos_right (ihm (by omega)) (by decide))
              (Nat.mul_le_mul_left _ (by decide))
      exact hst w (by omega)
    rw [pow4_eq_pow2_even w] at hlt; omega
  have hb0_le2w : b0 ≤ 2 * w := by
    have hm := binBitLength_mono (3 ^ w) (2 ^ ((2 * w - 1) + 1) - 1)
      (by rw [show (2 * w - 1) + 1 = 2 * w by omega]; exact hp3_le4)
    rw [(binBitLength_pow2_and_pred (2 * w - 1)).2, show (2 * w - 1) + 1 = 2 * w by omega] at hm
    exact hm
  rcases binBitLength_pow2_sandwich_w15 (3 ^ w) (3 ^ w) (by omega) (Nat.le_refl _) with
    ⟨_, hlo, hhi⟩
  change 2 ^ (b0 - 1) ≤ 3 ^ w at hlo
  change 3 ^ w < 2 ^ b0 at hhi
  have hne_pow2 : 2 ^ (b0 - 1) ≠ 3 ^ w := by
    intro heq
    have hev : 2 ^ (b0 - 1) % 2 = 0 := by
      rw [show b0 - 1 = (b0 - 2) + 1 by omega, Nat.pow_succ]; omega
    have hodd := pow3_odd_nat_sec8 w
    rw [← heq] at hodd; omega
  have hlt_lo : 2 ^ (b0 - 1) < 3 ^ w := Nat.lt_of_le_of_ne hlo hne_pow2
  have h2b0_lt : 2 ^ b0 < 2 * 3 ^ w := by
    rw [show b0 = (b0 - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    exact Nat.mul_lt_mul_of_pos_left hlt_lo (by decide)
  exact ⟨hb0_ge18, hb0_le2w, Nat.succ_le_of_lt hhi, h2b0_lt⟩

private theorem dyadicPolyShiftDelta_spec_w15 (b0 : Nat) :
    let delta := dyadicPolyShiftDelta b0
    let a := b0 + delta
    let q3 := (2 ^ (a + 1) - 1) / 3
    delta ≤ 3 ∧ 3 * q3 + 1 = 2 ^ (a + 1) ∧ q3 % 3 ≠ 0 ∧ q3 ≥ 1 := by
  dsimp only
  let delta := dyadicPolyShiftDelta b0
  have hd_mod6 : delta ≤ 3 ∧ ((b0 + 1 + delta) % 6 = 2 ∨ (b0 + 1 + delta) % 6 = 4) := by
    dsimp [delta]; unfold dyadicPolyShiftDelta
    have hr6 : (b0 + 1) % 6 < 6 := Nat.mod_lt (b0 + 1) (by decide)
    have hdm := (Nat.div_add_mod (b0 + 1) 6).symm
    rcases (by omega :
      (b0 + 1) % 6 = 0 ∨ (b0 + 1) % 6 = 1 ∨ (b0 + 1) % 6 = 2 ∨
      (b0 + 1) % 6 = 3 ∨ (b0 + 1) % 6 = 4 ∨ (b0 + 1) % 6 = 5) with
      h | h | h | h | h | h <;> (simp [h]; omega)
  let E := b0 + 1 + delta
  have hE_eq : b0 + delta + 1 = E := by dsimp [E]; omega
  have hp64_m9 : ∀ k : Nat, 2 ^ (6 * k) % 9 = 1 := by
    intro k; induction k with
    | zero => rfl
    | succ k' ih =>
      rw [Nat.mul_succ 6 k', Nat.pow_add 2 (6 * k') 6, Nat.mul_mod, ih]
  have hpE_m9 : 2 ^ E % 9 = 4 ∨ 2 ^ E % 9 = 7 := by
    have hdm := (Nat.div_add_mod E 6).symm
    rcases hd_mod6.2 with h2 | h4
    · left
      rw [h2] at hdm
      rw [hdm, Nat.pow_add 2 (6 * (E / 6)) 2, Nat.mul_mod, hp64_m9 (E / 6)]
    · right
      rw [h4] at hdm
      rw [hdm, Nat.pow_add 2 (6 * (E / 6)) 4, Nat.mul_mod, hp64_m9 (E / 6)]
  have hpE_ge4 : 2 ^ E ≥ 4 := by
    have hE2 : E ≥ 2 := by have := hd_mod6.2; omega
    simpa using pow2_mono_nat hE2
  rw [hE_eq]
  have hdm9 := (Nat.div_add_mod (2 ^ E) 9).symm
  refine ⟨hd_mod6.1, ?_, ?_, ?_⟩
  · rcases hpE_m9 with h4 | h7 <;> omega
  · rcases hpE_m9 with h4 | h7 <;> omega
  · omega

private theorem pow2_euler_pow3_mod_one_w15 :
    ∀ n : Nat, 3 ^ (n + 1) ∣ (2 ^ (2 * 3 ^ n) - 1)
  | 0 => ⟨1, by decide⟩
  | n + 1 => by
    rcases pow2_euler_pow3_mod_one_w15 n with ⟨q, hq⟩
    let X := 2 ^ (2 * 3 ^ n)
    have hX_pos : X ≥ 1 := pow2_pos_nat _
    have hX_eq : X = 3 ^ (n + 1) * q + 1 := by dsimp [X]; omega
    have hpow3 : 2 ^ (2 * 3 ^ (n + 1)) = X * X * X := by
      rw [Nat.pow_succ 3 n, ← Nat.mul_assoc 2 (3 ^ n) 3,
          ← pow_pow_eq_mul_w5 2 (2 * 3 ^ n) 3,
          Nat.pow_succ X 2, Nat.pow_succ X 1, Nat.pow_one]
    rw [hpow3]
    let M := 3 ^ (n + 1)
    change 3 ^ (n + 2) ∣ (X * X * X - 1)
    have hM3 : 3 ^ (n + 2) = 3 * M := by dsimp [M]; rw [Nat.pow_succ, Nat.mul_comm]
    have hM_sp : M = 3 * 3 ^ n := by dsimp [M]; rw [Nat.pow_succ, Nat.mul_comm]
    rw [hM3, hX_eq]
    refine ⟨q * (3 ^ n * M * q * q + M * q + 1), ?_⟩
    have hexp : (M * q + 1) * (M * q + 1) * (M * q + 1) =
        (3 * M) * (q * (3 ^ n * M * q * q + M * q + 1)) + 1 := by
      have hc : ∀ (p0 m0 q0 : Nat),
          ((3 * p0) * q0 + 1) * ((3 * p0) * q0 + 1) * ((3 * p0) * q0 + 1) =
            (3 * (3 * p0)) * (q0 * (p0 * (3 * p0) * q0 * q0 + (3 * p0) * q0 + 1)) + 1 := by
        intro p0 m0 q0
        have ht : ∀ Z : Nat, (Z + 1) * (Z + 1) * (Z + 1) = Z * Z * Z + 3 * (Z * Z) + 3 * Z + 1 := by
          intro Z
          simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
          generalize Z * Z * Z = A; generalize Z * Z = B; omega
        rw [ht ((3 * p0) * q0)]
        have h1 : ((3 * p0) * q0) * ((3 * p0) * q0) * ((3 * p0) * q0) =
            (3 * (3 * p0)) * (q0 * (p0 * (3 * p0) * q0 * q0)) := by ac_rfl
        have h2 : 3 * (((3 * p0) * q0) * ((3 * p0) * q0)) =
            (3 * (3 * p0)) * (q0 * ((3 * p0) * q0)) := by ac_rfl
        have h3 : 3 * ((3 * p0) * q0) = (3 * (3 * p0)) * (q0 * 1) := by ac_rfl
        rw [h1, h2, h3, ← Nat.mul_add (3 * (3 * p0)), ← Nat.mul_add (3 * (3 * p0)),
            ← Nat.mul_add q0, ← Nat.mul_add q0]
      rw [hM_sp]
      exact hc (3 ^ n) M q
    rw [hexp]; omega

private theorem pow2_add_period_mod_pow3_w15 (n t k : Nat) :
    2 ^ (t + k * (2 * 3 ^ n)) % 3 ^ (n + 1) = 2 ^ t % 3 ^ (n + 1) := by
  let P := 2 * 3 ^ n
  let M := 3 ^ (n + 1)
  have hM_ge3 : M ≥ 3 := by
    dsimp [M]; rw [Nat.pow_succ]; have := pow3_pos_nat n; omega
  have hp_one : 2 ^ P % M = 1 := by
    rcases pow2_euler_pow3_mod_one_w15 n with ⟨q, hq⟩
    have hp_pos := pow2_pos_nat (2 * 3 ^ n)
    have heq : 2 ^ P = 1 + M * q := by dsimp [P, M] at hq ⊢; omega
    rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hkp : 2 ^ (k * P) % M = 1 := by
    rw [Nat.mul_comm k P, ← pow_pow_eq_mul_w5 2 P k, pow_mod_eq_pow_mod_w15 (2 ^ P) M k,
        hp_one, Nat.one_pow, Nat.mod_eq_of_lt (by omega)]
  rw [Nat.pow_add 2 t (k * P), Nat.mul_mod, hkp, Nat.mul_one, Nat.mod_mod]

private theorem isSurvivingMod373248_of_511_and_1_w15 (y : Nat)
    (h512 : y % 512 = 511) (h81 : y % 81 = 1) :
    isSurvivingMod373248Bool y = true ∧ IsSurvivingMod373248Class y := by
  let r729 := y % 729
  have hr_lt : r729 < 729 := Nat.mod_lt y (by decide)
  have hr_m81 : r729 % 81 = 1 := by
    dsimp only [r729]
    rw [Nat.mod_mod_of_dvd y ⟨9, by decide⟩, h81]
  have hb729 : isSurvivingMod729Bool (y % 729) = true := by
    change isSurvivingMod729Bool r729 = true
    unfold isSurvivingMod729Bool
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, decide_eq_true_eq]
    omega
  have hb512 : isSurvivingMod512Bool (y % 512) = true := by rw [h512]; decide
  have hb373 : isSurvivingMod373248Bool y = true := by
    unfold isSurvivingMod373248Bool; rw [hb512, hb729]; rfl
  exact ⟨hb373, isSurvivingMod373248Bool_imp_class y hb373⟩

private def eraseAllNatW15 (b : Nat) : List Nat -> List Nat
  | [] => []
  | x :: xs => if x = b then eraseAllNatW15 b xs else x :: eraseAllNatW15 b xs

private theorem mem_eraseAllNatW15_iff (b : Nat) :
    ∀ (xs : List Nat) (v : Nat), v ∈ eraseAllNatW15 b xs ↔ (v ∈ xs ∧ v ≠ b)
  | [], _ => by simp [eraseAllNatW15]
  | x :: xs, v => by
    simp only [eraseAllNatW15]
    by_cases hxb : x = b
    · simp only [hxb, ite_true, mem_eraseAllNatW15_iff b xs v, List.mem_cons]
      exact ⟨fun ⟨hm, hne⟩ => ⟨Or.inr hm, hne⟩,
             fun ⟨h, hne⟩ => ⟨by rcases h with rfl | hm; { exact False.elim (hne rfl) }; exact hm, hne⟩⟩
    · simp only [hxb, ite_false, List.mem_cons, mem_eraseAllNatW15_iff b xs v]
      exact ⟨fun h => by rcases h with rfl | ⟨hm, hne⟩; { exact ⟨Or.inl rfl, hxb⟩ }; exact ⟨Or.inr hm, hne⟩,
             fun ⟨h, hne⟩ => by rcases h with rfl | hm; { exact Or.inl rfl }; exact Or.inr ⟨hm, hne⟩⟩

private theorem eraseAllNatW15_of_not_mem (b : Nat) :
    ∀ (xs : List Nat), b ∉ xs -> eraseAllNatW15 b xs = xs
  | [], _ => rfl
  | x :: xs, hnm => by
    have hxb : x ≠ b := fun h => hnm (h ▸ List.Mem.head _)
    have hnm_xs : b ∉ xs := fun hm => hnm (List.mem_cons_of_mem _ hm)
    simp only [eraseAllNatW15, hxb, ite_false, eraseAllNatW15_of_not_mem b xs hnm_xs]

private theorem nodup_eraseAllNatW15_and_len (b : Nat) :
    ∀ (xs : List Nat),
      NoDupNat xs -> NoDupNat (eraseAllNatW15 b xs) ∧ xs.length ≤ (eraseAllNatW15 b xs).length + 1
  | [], _ => ⟨NoDupNat.nil, by simp [eraseAllNatW15]⟩
  | x :: xs, NoDupNat.cons _ _ hnx hnd => by
    by_cases hxb : x = b
    · subst hxb
      simp only [eraseAllNatW15, ite_true, eraseAllNatW15_of_not_mem x xs hnx, List.length_cons]
      exact ⟨hnd, Nat.le_refl _⟩
    · rcases nodup_eraseAllNatW15_and_len b xs hnd with ⟨hnd_er, hlen_er⟩
      simp only [eraseAllNatW15, hxb, ite_false, List.length_cons]
      have hnx_er : x ∉ eraseAllNatW15 b xs :=
        fun hm => hnx ((mem_eraseAllNatW15_iff b xs x).mp hm).1
      exact ⟨NoDupNat.cons x _ hnx_er hnd_er, by omega⟩

private theorem noDupNat_length_le_of_subset_w15 :
    ∀ (cands xs : List Nat),
      NoDupNat xs -> (∀ y ∈ xs, y ∈ cands) -> xs.length ≤ cands.length
  | [], [], _, _ => Nat.le_refl 0
  | [], x :: _, _, hsub => by cases hsub x (List.Mem.head _)
  | b :: bs, xs, hnd, hsub => by
    rcases nodup_eraseAllNatW15_and_len b xs hnd with ⟨hnd', hlen'⟩
    have hsub' : ∀ y ∈ eraseAllNatW15 b xs, y ∈ bs := by
      intro y hy
      rcases (mem_eraseAllNatW15_iff b xs y).mp hy with ⟨hy_xs, hne⟩
      rcases List.mem_cons.mp (hsub y hy_xs) with rfl | hbs
      · exact False.elim (hne rfl)
      · exact hbs
    have ih := noDupNat_length_le_of_subset_w15 bs (eraseAllNatW15 b xs) hnd' hsub'
    simp only [List.length_cons]; omega

private def descIdxListW15 : Nat -> List Nat
  | 0 => []
  | r + 1 => r :: descIdxListW15 r

private theorem descIdxListW15_spec :
    ∀ r : Nat,
      (descIdxListW15 r).length = r ∧
      NoDupNat (descIdxListW15 r) ∧
      (∀ j ∈ descIdxListW15 r, j < r)
  | 0 => ⟨rfl, NoDupNat.nil, fun _ hm => by cases hm⟩
  | r + 1 => by
    rcases descIdxListW15_spec r with ⟨hlen, hnd, hlt⟩
    have hnot_mem : r ∉ descIdxListW15 r := fun hm => Nat.lt_irrefl r (hlt r hm)
    refine ⟨by simp [descIdxListW15, hlen], NoDupNat.cons r _ hnot_mem hnd, ?_⟩
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hm
    · omega
    · have := hlt j hm; omega

private theorem noDupNat_map_inj_on_w15 (f : Nat -> Nat) :
    ∀ (js : List Nat),
      NoDupNat js ->
      (∀ a ∈ js, ∀ b ∈ js, f a = f b -> a = b) ->
      NoDupNat (js.map f)
  | [], _, _ => NoDupNat.nil
  | j :: js, NoDupNat.cons _ _ hnj hnd, hinj => by
    refine NoDupNat.cons (f j) (js.map f) ?_
      (noDupNat_map_inj_on_w15 f js hnd (fun a ha b hb =>
        hinj a (List.mem_cons_of_mem j ha) b (List.mem_cons_of_mem j hb)))
    intro hm
    rcases List.mem_map.mp hm with ⟨j', hj', heq⟩
    have hj_eq := hinj j' (List.mem_cons_of_mem j hj') j (List.Mem.head _) heq
    exact hnj (hj_eq ▸ hj')

private theorem pow3_gt_two_mul_w15 : ∀ n : Nat, 3 ^ n > 2 * n
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by have ih := pow3_gt_two_mul_w15 (n + 1); rw [Nat.pow_succ]; omega

private theorem uWinPoly_per_idx_core_and_key_w15
    (d R M idx : Nat) (hd : d ≥ 1) (hR : R ≥ 1) (hM : M ≥ dyadicPolyWindowMinM d R)
    (_hidx : idx < R ^ d) :
    let w := d + 10
    let b0 := binBitLength (3 ^ w)
    let delta := dyadicPolyShiftDelta b0
    let a := b0 + delta
    let u_p := uWinPoly d R M idx
    IsCoreParityWord u_p ∧
    u_p.length = M - delta ∧
    parityWeight u_p = w ∧
    canonicalSuffixShift u_p 1 = a ∧
    IsFirstHitOnePair u_p 0 ∧
    affineCarry u_p ≥ 1 ∧
    affineCarry u_p < 2 ^ M ∧
    (∃ mid : List Bool, u_p = List.replicate 9 true ++ mid ++ [true]) ∧
    (∃ m : Nat, 2 ^ (u_p.length + a) = 3 ^ w * (81 * m + 1) + affineCarry u_p) := by
  dsimp only
  let w := d + 10
  let b0 := binBitLength (3 ^ w)
  let delta := dyadicPolyShiftDelta b0
  let a := b0 + delta
  let q3 := (2 ^ (a + 1) - 1) / 3
  let period := 2 * 3 ^ (d + 12)
  let L := M - delta
  have hw_eq : w = d + 10 := rfl
  have ha_eq : a = b0 + delta := rfl
  have hper_eq_def : period = 2 * 3 ^ (d + 12) := rfl
  have hL_eq : L = M - delta := rfl
  have hw_ge11 : w ≥ 11 := by rw [hw_eq]; omega
  rcases pow3_bitlength_strict_bounds_w15 w hw_ge11 with ⟨hb0_ge18, hb0_le2w, h3w_lo, _⟩
  change b0 ≥ 18 at hb0_ge18
  change b0 ≤ 2 * w at hb0_le2w
  change 3 ^ w + 1 ≤ 2 ^ b0 at h3w_lo
  rcases dyadicPolyShiftDelta_spec_w15 b0 with ⟨hdelta_le3, h3q3, hq3_n3, hq3_pos⟩
  change delta ≤ 3 at hdelta_le3
  change 3 * q3 + 1 = 2 ^ (a + 1) at h3q3
  change q3 % 3 ≠ 0 at hq3_n3
  change q3 ≥ 1 at hq3_pos
  have hper_gt : period > 4 * d + 48 := by
    rw [hper_eq_def]; have h := pow3_gt_two_mul_w15 (d + 12); omega
  have hRper_lin : R * period ≥ 2 * d * R + 2 * d + 48 := by
    have hm1 : R * (4 * d + 48) ≤ R * period := Nat.mul_le_mul_left R (Nat.le_of_lt hper_gt)
    have hm2 : 2 * d * 1 ≤ 2 * d * R := Nat.mul_le_mul_left (2 * d) hR
    have hm3 : 48 * 1 ≤ 48 * R := Nat.mul_le_mul_left 48 hR
    have h4d : R * (4 * d) = 2 * d * R + 2 * d * R := by
      rw [show (4 : Nat) = 2 + 2 from rfl, Nat.add_mul, Nat.mul_add]; ac_rfl
    rw [Nat.mul_add R (4 * d) 48, h4d, Nat.mul_comm R 48] at hm1
    omega
  have hM_def : M ≥ 2 * R * period + 2 * d * R + 30 := hM
  have hL_ge : L ≥ 2 * R * period + 2 * d * R + 27 := by
    rw [hL_eq]; rw [Nat.mul_assoc 2 R period] at hM_def ⊢; omega
  have ha_lt_P : a < 2 * 3 ^ (w - 1) := by
    have hb0_2d : b0 ≤ 2 * (d + 10) := by rw [← hw_eq]; exact hb0_le2w
    have ha_le : a ≤ 2 * d + 23 := by rw [ha_eq]; omega
    have hw1_gt : 3 ^ (w - 1) > 2 * (d + 9) := by
      have hw_sub : w - 1 = d + 9 := by rw [hw_eq]; omega
      rw [hw_sub]; exact pow3_gt_two_mul_w15 (d + 9)
    omega
  have hp9_bd : affineCarry (List.replicate 9 true) <
      4 ^ parityWeight (List.replicate 9 true) * 2 ^ (List.replicate 9 true).length := by decide
  let ks := baseREvenDigits (d - 1) R (idx / R)
  rcases (baseREvenDigits_spec (d - 1) R hR).1 (idx / R) with ⟨hks_len, hks_sum⟩
  change ks.length = d - 1 at hks_len
  change natSumListW15 ks ≤ 2 * (d - 1) * R at hks_sum
  let u_pref := List.replicate 9 true ++ zeroRunsSuffix ks
  have hupref_eq_def : u_pref = List.replicate 9 true ++ zeroRunsSuffix ks := rfl
  rcases zeroRunsSuffix_len_wt_carry_bound ks (List.replicate 9 true) hp9_bd with
    ⟨hpref_len, hpref_wt, hpref_bd⟩
  change u_pref.length = 9 + ks.length + natSumListW15 ks at hpref_len
  change parityWeight u_pref = 9 + ks.length at hpref_wt
  change affineCarry u_pref < 4 ^ parityWeight u_pref * 2 ^ u_pref.length at hpref_bd
  rw [hks_len] at hpref_len hpref_wt
  have hks_sum_le : natSumListW15 ks ≤ 2 * d * R :=
    Nat.le_trans hks_sum (Nat.mul_le_mul_right R (by omega))
  have hpref_len_ub : u_pref.length ≤ d + 8 + 2 * d * R := by omega
  have hpref_exp_ub : 2 * parityWeight u_pref + u_pref.length ≤ L - 27 := by
    rw [Nat.mul_assoc 2 R period] at hL_ge; omega
  have hcar_pref_ub : affineCarry u_pref < 2 ^ (L - 27) := by
    rw [pow4_eq_pow2_even (parityWeight u_pref), ← Nat.pow_add] at hpref_bd
    exact Nat.lt_of_lt_of_le hpref_bd (pow2_mono_nat hpref_exp_ub)
  have h3w1_ub : 3 ^ (w - 1) < 2 ^ (L - 27) := by
    have h1 : 3 ^ (w - 1) < 3 ^ w := by
      have hsp : 3 ^ w = 3 ^ (w - 1) * 3 := by
        conv => lhs; rw [show w = (w - 1) + 1 by omega, Nat.pow_succ]
      rw [hsp]; have hp := pow3_pos_nat (w - 1); omega
    have h2 : b0 ≤ L - 27 := by
      have hb0_2d : b0 ≤ 2 * (d + 10) := by rw [← hw_eq]; exact hb0_le2w
      rw [Nat.mul_assoc 2 R period] at hL_ge; omega
    exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h1 (Nat.le_of_succ_le h3w_lo)) (pow2_mono_nat h2)
  let sub_p := 3 * affineCarry u_pref + 3 ^ (w - 1)
  have hsub_eq_def : sub_p = 3 * affineCarry u_pref + 3 ^ (w - 1) := rfl
  have hsub_ub : sub_p < 2 ^ (L - 25) := by
    rw [hsub_eq_def, show L - 25 = 2 + (L - 27) by
          rw [Nat.mul_assoc 2 R period] at hL_ge; omega, Nat.pow_add 2 2 (L - 27)]
    change 3 * affineCarry u_pref + 3 ^ (w - 1) < 4 * 2 ^ (L - 27); omega
  have hsub_lt_q3 : sub_p < q3 * 2 ^ (L - 1) := by
    have h1 : 2 ^ (L - 25) ≤ 1 * 2 ^ (L - 1) := by
      rw [Nat.one_mul]; apply pow2_mono_nat
      rw [Nat.mul_assoc 2 R period] at hL_ge; omega
    exact Nat.lt_of_lt_of_le hsub_ub (Nat.le_trans h1 (Nat.mul_le_mul_right _ hq3_pos))
  let A_num := q3 * 2 ^ (L - 1) - sub_p
  have hA_eq_def : A_num = q3 * 2 ^ (L - 1) - sub_p := rfl
  have hA_m3 : (A_num % 3 ^ (w + 3)) % 3 ≠ 0 := by
    have hAn3 : A_num % 3 ≠ 0 := by
      have hsub3 : sub_p = 3 * (affineCarry u_pref + 3 ^ (w - 2)) := by
        rw [hsub_eq_def, show w - 1 = 1 + (w - 2) by omega, Nat.pow_add, Nat.pow_one, Nat.mul_add]
      have hrew : q3 * 2 ^ (L - 1) = A_num + 3 * (affineCarry u_pref + 3 ^ (w - 2)) := by
        rw [hA_eq_def, ← hsub3, Nat.sub_add_cancel (Nat.le_of_lt hsub_lt_q3)]
      intro h0
      have hm0 : (q3 * 2 ^ (L - 1)) % 3 = 0 := by rw [hrew, Nat.add_mul_mod_self_left, h0]
      rw [Nat.mul_mod] at hm0
      have hp2_n3 := pow2_mod3_nonzero_w5 (L - 1)
      have hq3_lt3 : q3 % 3 < 3 := Nat.mod_lt q3 (by decide)
      have hp2_lt3 : 2 ^ (L - 1) % 3 < 3 := Nat.mod_lt _ (by decide)
      rcases (by omega : q3 % 3 = 1 ∨ q3 % 3 = 2) with hq | hq <;>
      rcases (by omega : 2 ^ (L - 1) % 3 = 1 ∨ 2 ^ (L - 1) % 3 = 2) with hp | hp <;>
      (rw [hq, hp] at hm0; cases hm0)
    have hdvd3 : 3 ∣ 3 ^ (w + 3) := by
      rw [show w + 3 = 1 + (w + 2) by omega, Nat.pow_add, Nat.pow_one]
      exact ⟨3 ^ (w + 2), rfl⟩
    rwa [Nat.mod_mod_of_dvd A_num hdvd3]
  rcases dlog2ModPow3_spec (w + 3) (A_num % 3 ^ (w + 3)) (by omega) hA_m3 with
    ⟨htb_lt_raw, htb_mod_raw⟩
  let t_base := dlog2ModPow3 (w + 3) (A_num % 3 ^ (w + 3))
  change t_base < 2 * 3 ^ ((w + 3) - 1) at htb_lt_raw
  change 2 ^ t_base % 3 ^ (w + 3) = (A_num % 3 ^ (w + 3)) % 3 ^ (w + 3) at htb_mod_raw
  have hper_eq_w : 2 * 3 ^ ((w + 3) - 1) = period := by
    rw [hper_eq_def, hw_eq]; congr 2
  have htb_lt : t_base < period := by rwa [hper_eq_w] at htb_lt_raw
  let t_pos := t_base + (R + idx % R) * period
  have htpos_eq_def : t_pos = t_base + (R + idx % R) * period := rfl
  have hmod_tpos : 2 ^ t_pos % 3 ^ (w + 3) = A_num % 3 ^ (w + 3) := by
    have hp_per : 2 ^ t_pos % 3 ^ ((d + 12) + 1) = 2 ^ t_base % 3 ^ ((d + 12) + 1) := by
      rw [htpos_eq_def, hper_eq_def]
      exact pow2_add_period_mod_pow3_w15 (d + 12) t_base (R + idx % R)
    have hw3_eq : (d + 12) + 1 = w + 3 := by rw [hw_eq]
    rw [hw3_eq] at hp_per
    rw [hp_per]
    rw [Nat.mod_mod] at htb_mod_raw
    exact htb_mod_raw
  have hj0_lt : idx % R < R := Nat.mod_lt idx (by omega)
  have htpos_ge : t_pos ≥ R * period :=
    Nat.le_trans
      (Nat.mul_le_mul_right period (Nat.le_add_right R (idx % R)))
      (Nat.le_add_left _ t_base)
  have htpos_lt : t_pos < 2 * R * period := by
    have h1 : R + idx % R + 1 ≤ 2 * R := by omega
    have h2 := Nat.mul_le_mul_right period h1
    have h3 : t_pos < (R + idx % R + 1) * period := by
      rw [htpos_eq_def, Nat.add_mul (R + idx % R) 1 period, Nat.one_mul, Nat.add_comm t_base]
      exact Nat.add_lt_add_left htb_lt _
    exact Nat.lt_of_lt_of_le h3 h2
  have hpref_le_tpos : u_pref.length ≤ t_pos := by omega
  have htpos_le_L27 : t_pos ≤ L - 28 := by
    rw [Nat.mul_assoc 2 R period] at htpos_lt hL_ge; omega
  let kd := t_pos - u_pref.length
  let kd1 := (L - 2) - t_pos
  have hkd_eq_def : kd = t_pos - u_pref.length := rfl
  have hkd1_eq_def : kd1 = (L - 2) - t_pos := rfl
  rcases (⟨uWinPoly d R M idx, rfl⟩ : ∃ u0 : List Bool, u0 = uWinPoly d R M idx) with
    ⟨u_p, hup_def⟩
  have hruns_def : uWinPolyRuns d R M idx = ks ++ [kd, kd1] := rfl
  have hu_split_tail : u_p = u_pref ++ List.replicate kd false ++ [true] ++
      List.replicate kd1 false ++ [true] := by
    rw [hup_def]; unfold uWinPoly
    rw [hruns_def, zeroRunsSuffix_append_and_inj.1 ks [kd, kd1], hupref_eq_def]
    dsimp only [zeroRunsSuffix]
    simp [List.append_assoc]
  rcases affineCarry_append_replicate_false u_pref kd with ⟨hw_s1, hc_s1⟩
  let s1 := u_pref ++ List.replicate kd false
  let s2 := s1 ++ [true]
  let s3 := s2 ++ List.replicate kd1 false
  have hs1_eq_def : s1 = u_pref ++ List.replicate kd false := rfl
  have hs2_eq_def : s2 = s1 ++ [true] := rfl
  have hs3_eq_def : s3 = s2 ++ List.replicate kd1 false := rfl
  change parityWeight s1 = parityWeight u_pref at hw_s1
  change affineCarry s1 = affineCarry u_pref at hc_s1
  have hlen_s1 : s1.length = t_pos := by
    rw [hs1_eq_def, List.length_append, List.length_replicate, hkd_eq_def]; omega
  have hwt_s2 : parityWeight s2 = w - 1 := by
    rw [hs2_eq_def, parityWeight_append, hw_s1, hpref_wt, hw_eq]
    have hw1 : parityWeight [true] = 1 := rfl
    rw [hw1]; omega
  have hlen_s2 : s2.length = t_pos + 1 := by
    rw [hs2_eq_def, List.length_append, hlen_s1, List.length_singleton]
  have hcar_s2 : affineCarry s2 = 3 * affineCarry u_pref + 2 ^ t_pos := by
    rw [hs2_eq_def, affineCarry_append, hc_s1, hlen_s1]
    have hc1 : affineCarry [true] = 1 := rfl
    have hw1 : parityWeight [true] = 1 := rfl
    rw [hc1, hw1]; omega
  rcases affineCarry_append_replicate_false s2 kd1 with ⟨hw_s3, hc_s3⟩
  change parityWeight s3 = parityWeight s2 at hw_s3
  change affineCarry s3 = affineCarry s2 at hc_s3
  have hlen_s3 : s3.length = L - 1 := by
    rw [hs3_eq_def, List.length_append, hlen_s2, List.length_replicate, hkd1_eq_def]; omega
  have hu_s3 : u_p = s3 ++ [true] := hu_split_tail
  have hcore_u : IsCoreParityWord u_p := by
    refine ⟨?_, ?_⟩
    · rw [hup_def]; unfold uWinPoly; rfl
    · rw [hu_s3, List.reverse_append]; rfl
  have hlen_u : u_p.length = L := by
    rw [hu_s3, List.length_append, hlen_s3, List.length_singleton]
    rw [Nat.mul_assoc 2 R period] at hL_ge; omega
  have hwt_u : parityWeight u_p = w := by
    rw [hu_s3, parityWeight_append]
    change parityWeight s3 + 1 = w
    rw [hw_s3, hwt_s2]; omega
  have hcar_u : affineCarry u_p = 9 * affineCarry u_pref + 3 * 2 ^ t_pos + 2 ^ (L - 1) := by
    rw [hu_s3, affineCarry_append]
    change 3 ^ parityWeight [true] * affineCarry s3 + 2 ^ s3.length * affineCarry [true] = _
    have hc1 : affineCarry [true] = 1 := rfl
    have hw1 : parityWeight [true] = 1 := rfl
    rw [hc1, hw1, hc_s3, hlen_s3, hcar_s2]; omega
  have h2t_lt_A : 2 ^ t_pos < A_num := by
    have ht_ub : 2 ^ t_pos ≤ 2 ^ (L - 28) := pow2_mono_nat htpos_le_L27
    have hsum_ub : 2 ^ (L - 28) + 2 ^ (L - 25) < 1 * 2 ^ (L - 1) := by
      rw [Nat.one_mul, show L - 1 = 27 + (L - 28) by
            rw [Nat.mul_assoc 2 R period] at hL_ge; omega,
          show L - 25 = 3 + (L - 28) by
            rw [Nat.mul_assoc 2 R period] at hL_ge; omega,
          Nat.pow_add 2 27 (L - 28), Nat.pow_add 2 3 (L - 28)]
      have hp := pow2_pos_nat (L - 28)
      change 2 ^ (L - 28) + 8 * 2 ^ (L - 28) < 134217728 * 2 ^ (L - 28)
      omega
    have hlt_q : 2 ^ t_pos + sub_p < q3 * 2 ^ (L - 1) :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_of_le_of_lt ht_ub hsub_ub)
        (Nat.le_trans (Nat.le_of_lt hsum_ub) (Nat.mul_le_mul_right _ hq3_pos))
    rw [hA_eq_def]; omega
  have hdiff_mod : (A_num - 2 ^ t_pos) % 3 ^ (w + 3) = 0 := by
    let P3 := 3 ^ (w + 3)
    change (A_num - 2 ^ t_pos) % P3 = 0
    change 2 ^ t_pos % P3 = A_num % P3 at hmod_tpos
    have hdmA := (Nat.div_add_mod A_num P3).symm
    have hdmB := (Nat.div_add_mod (2 ^ t_pos) P3).symm
    rw [hmod_tpos] at hdmB
    have hsub_eq : A_num - 2 ^ t_pos = P3 * (A_num / P3 - (2 ^ t_pos) / P3) := by
      rw [Nat.mul_sub_left_distrib]
      generalize P3 * (A_num / P3) = QA, P3 * ((2 ^ t_pos) / P3) = QB,
        A_num % P3 = rem, A_num = AN, 2 ^ t_pos = BN at hdmA hdmB h2t_lt_A ⊢
      omega
    rw [hsub_eq, Nat.mul_mod_right]
  rcases Nat.dvd_of_mod_eq_zero hdiff_mod with ⟨m, hm_eq⟩
  have hA_rec : A_num = 3 ^ (w + 3) * m + 2 ^ t_pos := by
    rw [← hm_eq, Nat.sub_add_cancel (Nat.le_of_lt h2t_lt_A)]
  have hkey_eq : 2 ^ (u_p.length + a) = 3 ^ w * (81 * m + 1) + affineCarry u_p := by
    rw [hlen_u, hcar_u]
    have hlhs_sp : 2 ^ (L + a) = 3 * (q3 * 2 ^ (L - 1)) + 2 ^ (L - 1) := by
      rw [show L + a = (a + 1) + (L - 1) by
            rw [Nat.mul_assoc 2 R period] at hL_ge; omega,
          Nat.pow_add 2 (a + 1) (L - 1), ← h3q3, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
    have hq3_rec : q3 * 2 ^ (L - 1) = A_num + (3 * affineCarry u_pref + 3 ^ (w - 1)) := by
      rw [← hsub_eq_def, hA_eq_def]
      exact (Nat.sub_add_cancel (Nat.le_of_lt hsub_lt_q3)).symm
    have h3_w3_aux : ∀ (pw m0 : Nat), 3 * (pw * 27 * m0) = pw * (81 * m0) := by
      intro pw m0
      calc 3 * (pw * 27 * m0)
          = pw * ((3 * 27) * m0) := by
            rw [Nat.mul_assoc pw 27 m0, ← Nat.mul_assoc 3 pw (27 * m0),
                Nat.mul_comm 3 pw, Nat.mul_assoc pw 3 (27 * m0), Nat.mul_assoc 3 27 m0]
        _ = pw * (81 * m0) := rfl
    have h3_w3 : 3 * (3 ^ (w + 3) * m) = 3 ^ w * (81 * m) := by
      rw [Nat.pow_add 3 w 3, show (3 : Nat) ^ 3 = 27 from rfl]
      exact h3_w3_aux (3 ^ w) m
    have h3_w1 : 3 * 3 ^ (w - 1) = 3 ^ w := by
      conv => rhs; rw [show w = 1 + (w - 1) by omega]
      rw [Nat.pow_add, Nat.pow_one]
    have hreassoc_key : ∀ (pw m0 c0 t0 pl0 : Nat),
        (pw * (81 * m0) + 3 * t0 + (9 * c0 + pw)) + pl0 =
          pw * (81 * m0 + 1) + (9 * c0 + 3 * t0 + pl0) := by
      intro pw m0 c0 t0 pl0
      rw [Nat.mul_add pw (81 * m0) 1, Nat.mul_one]
      omega
    rw [hlhs_sp, hq3_rec, hA_rec,
        Nat.mul_add 3 (3 ^ (w + 3) * m + 2 ^ t_pos),
        Nat.mul_add 3 (3 ^ (w + 3) * m) (2 ^ t_pos),
        Nat.mul_add 3 (3 * affineCarry u_pref) (3 ^ (w - 1)),
        h3_w3, h3_w1, ← Nat.mul_assoc 3 3 (affineCarry u_pref),
        show 3 * 3 = 9 from rfl]
    exact hreassoc_key (3 ^ w) m (affineCarry u_pref) (2 ^ t_pos) (2 ^ (L - 1))
  have hsh_a : canonicalSuffixShift u_p 1 = a := by
    rcases canonicalSuffixShift_spec_unique u_p 1 (by rw [hwt_u]; omega) (by decide) with
      ⟨_, _, huniq⟩
    symm
    apply huniq a (by rw [hwt_u]; exact ha_lt_P)
    rw [Nat.mul_one, hwt_u, hkey_eq, Nat.add_comm]
    exact Nat.add_mul_mod_self_left _ _ _
  have hfh : IsFirstHitOnePair u_p 0 :=
    (first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.2 u_p hcore_u).mpr
      (by rw [hsh_a, ha_eq]; omega)
  have hcar_lt_PM : affineCarry u_p < 2 ^ M := by
    rw [hcar_u]
    have ht_ub : 2 ^ t_pos ≤ 2 ^ (L - 28) := pow2_mono_nat htpos_le_L27
    have hlt_L : 9 * affineCarry u_pref + 3 * 2 ^ t_pos + 2 ^ (L - 1) < 2 ^ L := by
      have h1 : 9 * affineCarry u_pref < 9 * 2 ^ (L - 27) :=
        Nat.mul_lt_mul_of_pos_left hcar_pref_ub (by decide)
      have h2 : 3 * 2 ^ t_pos ≤ 3 * 2 ^ (L - 28) := Nat.mul_le_mul_left 3 ht_ub
      rw [show L - 27 = 1 + (L - 28) by
            rw [Nat.mul_assoc 2 R period] at hL_ge; omega,
          Nat.pow_add 2 1 (L - 28)] at h1
      have hsum_lo : 9 * (2 ^ 1 * 2 ^ (L - 28)) + 3 * 2 ^ (L - 28) < 2 ^ (L - 1) := by
        rw [show L - 1 = 27 + (L - 28) by
              rw [Nat.mul_assoc 2 R period] at hL_ge; omega,
            Nat.pow_add 2 27 (L - 28)]
        have hp := pow2_pos_nat (L - 28)
        change 9 * (2 * 2 ^ (L - 28)) + 3 * 2 ^ (L - 28) < 134217728 * 2 ^ (L - 28)
        omega
      have h2L : 2 ^ L = 2 ^ (L - 1) + 2 ^ (L - 1) := by
        conv => lhs; rw [show L = (L - 1) + 1 by
          rw [Nat.mul_assoc 2 R period] at hL_ge; omega]
        rw [Nat.pow_succ, Nat.mul_two]
      rw [h2L]; omega
    exact Nat.lt_of_lt_of_le hlt_L (pow2_mono_nat (by rw [hL_eq]; omega))
  have hcar_pos : affineCarry u_p ≥ 1 := by
    rw [hcar_u]; have := pow2_pos_nat (L - 1); omega
  have hmid_ex : ∃ mid : List Bool, u_p = List.replicate 9 true ++ mid ++ [true] := by
    have happ5 : ∀ (p a1 b1 c1 d1 e1 : List Bool),
        (((p ++ a1) ++ b1 ++ c1) ++ d1) ++ e1 = p ++ (a1 ++ b1 ++ c1 ++ d1) ++ e1 := by
      intro p a1 b1 c1 d1 e1; simp only [List.append_assoc]
    refine ⟨zeroRunsSuffix ks ++ List.replicate kd false ++ [true] ++ List.replicate kd1 false, ?_⟩
    rw [hu_split_tail, hupref_eq_def]
    exact happ5 (List.replicate 9 true) (zeroRunsSuffix ks)
      (List.replicate kd false) [true] (List.replicate kd1 false) [true]
  subst hup_def
  exact ⟨hcore_u, hlen_u, hwt_u, hsh_a, hfh, hcar_pos, hcar_lt_PM, hmid_ex, ⟨m, hkey_eq⟩⟩

private theorem uWinPoly_per_idx_leaf_spec_w15
    (d R M idx : Nat) (hd : d ≥ 1) (hR : R ≥ 1) (hM : M ≥ dyadicPolyWindowMinM d R)
    (hidx : idx < R ^ d) :
    let w := d + 10
    let b0 := binBitLength (3 ^ w)
    let delta := dyadicPolyShiftDelta b0
    let u := uWinPoly d R M idx
    let y := exactBackwardQuotient 1 u 0
    IsFirstHitOnePair u 0 ∧
    u.length = M - delta ∧
    u.length ≤ M ∧
    parityWeight u = w ∧
    canonicalSuffixShift u 1 = b0 + delta ∧
    y % 512 = 511 ∧
    y % 81 = 1 ∧
    isSurvivingMod373248Bool y = true ∧
    IsSurvivingMod373248Class y ∧
    2 ^ M ≤ y ∧ y < 2 ^ (M + 1) ∧
    (∀ L_max : Nat, L_max ≥ M -> y ∈ dyadicWindowSurvivingQ0Leaves L_max M) := by
  dsimp only
  let w := d + 10
  let b0 := binBitLength (3 ^ w)
  let delta := dyadicPolyShiftDelta b0
  let a := b0 + delta
  have hw_eq : w = d + 10 := rfl
  have ha_eq : a = b0 + delta := rfl
  have hw_ge11 : w ≥ 11 := by rw [hw_eq]; omega
  rcases pow3_bitlength_strict_bounds_w15 w hw_ge11 with ⟨_, _, h3w_lo, h2b0_hi⟩
  change 3 ^ w + 1 ≤ 2 ^ b0 at h3w_lo
  change 2 ^ b0 < 2 * 3 ^ w at h2b0_hi
  rcases dyadicPolyShiftDelta_spec_w15 b0 with ⟨hdelta_le3, _, _, _⟩
  change delta ≤ 3 at hdelta_le3
  have hM_ge30 : M ≥ 30 := by
    have hm : dyadicPolyWindowMinM d R ≥ 30 := by unfold dyadicPolyWindowMinM; omega
    omega
  rcases uWinPoly_per_idx_core_and_key_w15 d R M idx hd hR hM hidx with
    ⟨hcore_r, hlen_r, hwt_r, hsh_r, hfh_r, hcar_pos_r, hcar_lt_r, ⟨mid, hu_mid_r⟩, ⟨m, hkey_r⟩⟩
  rcases (⟨uWinPoly d R M idx, rfl⟩ : ∃ u0 : List Bool, u0 = uWinPoly d R M idx) with ⟨u_p, hup_def⟩
  rw [← hup_def] at hcore_r hlen_r hwt_r hsh_r hfh_r hcar_pos_r hcar_lt_r hu_mid_r hkey_r
  change u_p.length = M - delta at hlen_r
  change parityWeight u_p = w at hwt_r
  change canonicalSuffixShift u_p 1 = a at hsh_r
  change 2 ^ (u_p.length + a) = 3 ^ w * (81 * m + 1) + affineCarry u_p at hkey_r
  rcases (⟨exactBackwardQuotient 1 u_p 0, rfl⟩ :
      ∃ y0 : Nat, y0 = exactBackwardQuotient 1 u_p 0) with ⟨y, hy_def⟩
  have hy_81m1 : y = 81 * m + 1 := by
    rcases one_generator_pos_odd_and_reaches_one u_p 0 hcore_r with ⟨_, _, heq_bw, _⟩
    have hbw_steps : backwardOneTotalSteps u_p 0 = u_p.length + a := by
      unfold backwardOneTotalSteps; rw [hsh_r]; omega
    rw [hbw_steps, hwt_r, ← hy_def] at heq_bw
    have hcomb : 3 ^ w * y = 3 ^ w * (81 * m + 1) :=
      Nat.add_right_cancel (heq_bw.symm.trans hkey_r)
    exact Nat.eq_of_mul_eq_mul_left (pow3_pos_nat w) hcomb
  have hy_m81 : y % 81 = 1 := by rw [hy_81m1]; omega
  have hy_m512 : y % 512 = 511 := by
    have hp9_511 : parityOfIter 9 511 = List.replicate 9 true := by decide
    have hu_511 : u_p = parityOfIter 9 511 ++ mid ++ [true] := by rw [hp9_511]; exact hu_mid_r
    have hm := (surviving_mod512_nine_prefix_auto_weight_and_characterization.1 511
      (by decide) (by decide)).2.2.2 mid 0 |>.2.2.1
    rwa [← hu_511, ← hy_def] at hm
  rcases isSurvivingMod373248_of_511_and_1_w15 y hy_m512 hy_m81 with ⟨hb_surv, hcls_surv⟩
  have hy_win : 2 ^ M ≤ y ∧ y < 2 ^ (M + 1) := by
    have hLa_eq : u_p.length + a = b0 + M := by
      rw [hlen_r, ha_eq]; omega
    have heq_y : 3 ^ w * y + affineCarry u_p = 2 ^ b0 * 2 ^ M := by
      have hk := hkey_r.symm
      rwa [← hy_81m1, hLa_eq, Nat.pow_add 2 b0 M] at hk
    have hPM_pos := pow2_pos_nat M
    refine ⟨?_, ?_⟩
    · by_cases hge : 2 ^ M ≤ y
      · exact hge
      · exfalso
        have hy_le : y ≤ 2 ^ M - 1 := by clear hu_mid_r hcore_r hfh_r hb_surv hcls_surv; omega
        have h1 : 3 ^ w * y + affineCarry u_p < (3 ^ w + 1) * 2 ^ M := by
          calc 3 ^ w * y + affineCarry u_p
              ≤ 3 ^ w * (2 ^ M - 1) + (2 ^ M - 1) :=
                Nat.add_le_add (Nat.mul_le_mul_left _ hy_le)
                  (by clear hu_mid_r hcore_r hfh_r hb_surv hcls_surv; omega)
            _ = (3 ^ w + 1) * (2 ^ M - 1) := by rw [Nat.add_mul, Nat.one_mul]
            _ < (3 ^ w + 1) * 2 ^ M :=
                Nat.mul_lt_mul_of_pos_left
                  (by clear hu_mid_r hcore_r hfh_r hb_surv hcls_surv; omega)
                  (by have := pow3_pos_nat w; clear hu_mid_r hcore_r hfh_r hb_surv hcls_surv; omega)
        have h2 : (3 ^ w + 1) * 2 ^ M ≤ 2 ^ b0 * 2 ^ M := Nat.mul_le_mul_right _ h3w_lo
        clear hu_mid_r hcore_r hfh_r hb_surv hcls_surv; omega
    · rw [Nat.pow_succ, Nat.mul_comm (2 ^ M) 2]
      by_cases hlt : y < 2 * 2 ^ M
      · exact hlt
      · exfalso
        have hy_ge : 2 * 2 ^ M ≤ y := by clear hu_mid_r hcore_r hfh_r hb_surv hcls_surv; omega
        have h1 : (2 * 3 ^ w) * 2 ^ M < 3 ^ w * y + affineCarry u_p := by
          calc (2 * 3 ^ w) * 2 ^ M
              = 3 ^ w * (2 * 2 ^ M) :=
                (Nat.mul_assoc 2 (3 ^ w) (2 ^ M)).trans (Nat.mul_left_comm 2 (3 ^ w) (2 ^ M))
            _ ≤ 3 ^ w * y := Nat.mul_le_mul_left _ hy_ge
            _ < 3 ^ w * y + affineCarry u_p := by
                clear hu_mid_r hcore_r hfh_r hb_surv hcls_surv; omega
        have h2 : 2 ^ b0 * 2 ^ M < (2 * 3 ^ w) * 2 ^ M :=
          Nat.mul_lt_mul_of_pos_right h2b0_hi hPM_pos
        clear hu_mid_r hcore_r hfh_r hb_surv hcls_surv; omega
  have hlen_le_M : u_p.length ≤ M := by rw [hlen_r]; omega
  have hy_mem_win : ∀ L_max : Nat, L_max ≥ M -> y ∈ dyadicWindowSurvivingQ0Leaves L_max M := by
    intro L_max hL_max
    have hy_mem_fh : y ∈ firstHitSurvivingQ0LeavesUpToLen L_max :=
      (multiscale_first_hit_surviving_q0_leaves_nodup L_max).2.2 y |>.mpr
        ⟨u_p, hfh_r, Nat.le_trans hlen_le_M hL_max, hb_surv, hy_def.symm⟩
    unfold dyadicWindowSurvivingQ0Leaves
    exact List.mem_filter.mpr ⟨hy_mem_fh, decide_eq_true hy_win⟩
  subst hup_def
  rw [← hy_def]
  exact ⟨hfh_r, hlen_r, hlen_le_M, hwt_r, hsh_r,
         hy_m512, hy_m81, hb_surv, hcls_surv, hy_win.1, hy_win.2, hy_mem_win⟩

private theorem uWinPoly_inj_idx_w15
    (d R M idx1 idx2 : Nat) (hd : d ≥ 1) (hR : R ≥ 1) (hM : M ≥ dyadicPolyWindowMinM d R)
    (h1 : idx1 < R ^ d) (h2 : idx2 < R ^ d)
    (hy_eq : exactBackwardQuotient 1 (uWinPoly d R M idx1) 0 =
      exactBackwardQuotient 1 (uWinPoly d R M idx2) 0) :
    idx1 = idx2 := by
  let w := d + 10
  let b0 := binBitLength (3 ^ w)
  let delta := dyadicPolyShiftDelta b0
  let a := b0 + delta
  let q3 := (2 ^ (a + 1) - 1) / 3
  let period := 2 * 3 ^ (d + 12)
  let L := M - delta
  have hper_eq_def : period = 2 * 3 ^ (d + 12) := rfl
  have hper_gt : period > 4 * d + 48 := by
    rw [hper_eq_def]; have h := pow3_gt_two_mul_w15 (d + 12); omega
  have hRper_lin : R * period ≥ 2 * d * R + 2 * d + 48 := by
    have hm1 : R * (4 * d + 48) ≤ R * period := Nat.mul_le_mul_left R (Nat.le_of_lt hper_gt)
    have hm2 : 2 * d * 1 ≤ 2 * d * R := Nat.mul_le_mul_left (2 * d) hR
    have hm3 : 48 * 1 ≤ 48 * R := Nat.mul_le_mul_left 48 hR
    have h4d : R * (4 * d) = 2 * d * R + 2 * d * R := by
      rw [show (4 : Nat) = 2 + 2 from rfl, Nat.add_mul, Nat.mul_add]; ac_rfl
    rw [Nat.mul_add R (4 * d) 48, h4d, Nat.mul_comm R 48] at hm1
    omega
  have hp9_bd : affineCarry (List.replicate 9 true) <
      4 ^ parityWeight (List.replicate 9 true) * 2 ^ (List.replicate 9 true).length := by decide
  have hfh1 := (uWinPoly_per_idx_core_and_key_w15 d R M idx1 hd hR hM h1).2.2.2.2.1
  have hfh2 := (uWinPoly_per_idx_core_and_key_w15 d R M idx2 hd hR hM h2).2.2.2.2.1
  have hu_eq : uWinPoly d R M idx1 = uWinPoly d R M idx2 :=
    (first_hit_one_pair_sound_and_injective _ _ 0 0 hfh1 hfh2).2.2.2 hy_eq |>.1
  clear hfh1 hfh2 hy_eq hM
  unfold uWinPoly at hu_eq
  have hzs_eq := (list_append_inj_left_eq_len _ _ _ _ rfl hu_eq).2
  have hruns_eq := zeroRunsSuffix_append_and_inj.2 _ _ hzs_eq
  clear hu_eq hzs_eq
  let ks1 := baseREvenDigits (d - 1) R (idx1 / R)
  let ks2 := baseREvenDigits (d - 1) R (idx2 / R)
  let up1 := List.replicate 9 true ++ zeroRunsSuffix ks1
  let up2 := List.replicate 9 true ++ zeroRunsSuffix ks2
  let A1 := q3 * 2 ^ (L - 1) - (3 * affineCarry up1 + 3 ^ (w - 1))
  let A2 := q3 * 2 ^ (L - 1) - (3 * affineCarry up2 + 3 ^ (w - 1))
  let tb1 := dlog2ModPow3 (w + 3) (A1 % 3 ^ (w + 3))
  let tb2 := dlog2ModPow3 (w + 3) (A2 % 3 ^ (w + 3))
  let tp1 := tb1 + (R + idx1 % R) * period
  let tp2 := tb2 + (R + idx2 % R) * period
  have hr1 : uWinPolyRuns d R M idx1 = ks1 ++ [tp1 - up1.length, (L - 2) - tp1] := rfl
  have hr2 : uWinPolyRuns d R M idx2 = ks2 ++ [tp2 - up2.length, (L - 2) - tp2] := rfl
  rw [hr1, hr2] at hruns_eq
  clear hr1 hr2
  rcases (baseREvenDigits_spec (d - 1) R hR).1 (idx1 / R) with ⟨hlen_k1, _⟩
  rcases (baseREvenDigits_spec (d - 1) R hR).1 (idx2 / R) with ⟨hlen_k2, hsum_k2⟩
  change ks1.length = d - 1 at hlen_k1
  change ks2.length = d - 1 at hlen_k2
  change natSumListW15 ks2 ≤ 2 * (d - 1) * R at hsum_k2
  rcases list_append_inj_left_eq_len _ _ _ _ (hlen_k1.trans hlen_k2.symm) hruns_eq with
    ⟨hks_eq, hpair_eq⟩
  clear hruns_eq
  have hdiv_lt : ∀ idx : Nat, idx < R ^ d -> idx / R < R ^ (d - 1) := by
    intro idx hidx
    rw [show d = (d - 1) + 1 by omega, Nat.pow_succ] at hidx
    by_cases hlt : idx / R < R ^ (d - 1)
    · exact hlt
    · exfalso
      have hge : R ^ (d - 1) ≤ idx / R := by omega
      have hm := Nat.mul_le_mul_left R hge
      rw [Nat.mul_comm R (R ^ (d - 1))] at hm
      have hdm := (Nat.div_add_mod idx R).symm
      omega
  have hq_eq : idx1 / R = idx2 / R :=
    (baseREvenDigits_spec (d - 1) R hR).2 (idx1 / R) (idx2 / R)
      (hdiv_lt idx1 h1) (hdiv_lt idx2 h2) hks_eq
  have hkd_eq : tp1 - up1.length = tp2 - up2.length := (List.cons.inj hpair_eq).1
  clear hpair_eq hdiv_lt
  have hks12 : ks1 = ks2 := by
    have hk1 : ks1 = baseREvenDigits (d - 1) R (idx1 / R) := rfl
    have hk2 : ks2 = baseREvenDigits (d - 1) R (idx2 / R) := rfl
    rw [hk1, hk2, hq_eq]
  have hup12 : up1 = up2 := by
    have hu1 : up1 = List.replicate 9 true ++ zeroRunsSuffix ks1 := rfl
    have hu2 : up2 = List.replicate 9 true ++ zeroRunsSuffix ks2 := rfl
    rw [hu1, hu2, hks12]
  have hA12 : A1 = A2 := by
    have ha1 : A1 = q3 * 2 ^ (L - 1) - (3 * affineCarry up1 + 3 ^ (w - 1)) := rfl
    have ha2 : A2 = q3 * 2 ^ (L - 1) - (3 * affineCarry up2 + 3 ^ (w - 1)) := rfl
    rw [ha1, ha2, hup12]
  have htb12 : tb1 = tb2 := by
    have ht1 : tb1 = dlog2ModPow3 (w + 3) (A1 % 3 ^ (w + 3)) := rfl
    have ht2 : tb2 = dlog2ModPow3 (w + 3) (A2 % 3 ^ (w + 3)) := rfl
    rw [ht1, ht2, hA12]
  have htp1_eq : tp1 = tb2 + (R + idx1 % R) * period := by
    have htp1_d : tp1 = tb1 + (R + idx1 % R) * period := rfl
    rw [htp1_d, htb12]
  have htp2_eq : tp2 = tb2 + (R + idx2 % R) * period := rfl
  rw [htp1_eq, htp2_eq, hup12] at hkd_eq
  rcases zeroRunsSuffix_len_wt_carry_bound ks2 (List.replicate 9 true) hp9_bd with
    ⟨hplen_c, _, _⟩
  change up2.length = 9 + ks2.length + natSumListW15 ks2 at hplen_c
  have hsum_le_c : natSumListW15 ks2 ≤ 2 * d * R :=
    Nat.le_trans hsum_k2 (Nat.mul_le_mul_right R (by omega))
  have hplen_le_per : up2.length ≤ R * period := by omega
  have hle1 : up2.length ≤ tb2 + (R + idx1 % R) * period :=
    Nat.le_trans hplen_le_per
      (Nat.le_trans (Nat.mul_le_mul_right period (Nat.le_add_right R _)) (Nat.le_add_left _ tb2))
  have hle2 : up2.length ≤ tb2 + (R + idx2 % R) * period :=
    Nat.le_trans hplen_le_per
      (Nat.le_trans (Nat.mul_le_mul_right period (Nat.le_add_right R _)) (Nat.le_add_left _ tb2))
  have htpos_eq : tb2 + (R + idx1 % R) * period = tb2 + (R + idx2 % R) * period := by
    have h := congrArg (· + up2.length) hkd_eq
    rwa [Nat.sub_add_cancel hle1, Nat.sub_add_cancel hle2] at h
  have hper_pos : 0 < period := by rw [hper_eq_def]; have := pow3_pos_nat (d + 12); omega
  have hmul_eq : R + idx1 % R = R + idx2 % R :=
    Nat.eq_of_mul_eq_mul_right hper_pos (Nat.add_left_cancel htpos_eq)
  have hr_eq : idx1 % R = idx2 % R := by omega
  have hdm1 := (Nat.div_add_mod idx1 R).symm
  have hdm2 := (Nat.div_add_mod idx2 R).symm
  rw [hq_eq, hr_eq] at hdm1
  omega

/--
  Theorem W15.4b (`dyadic_window_arbitrary_degree_polynomial_occupancy`, `zero custom axioms`):
  Constructive `(d + 1)`-Zero-Run Family `uWinPoly d R M idx` & Unconditional Arbitrary-Degree
  Polynomial Surviving-Leaf Dyadic-Window Occupancy (`≥ R ^ d` at Linear Horizon `L_max ≥ M`,
  `C_0(d) = 0`, `Branches P2.2 & P5.3`, `W15_H4`):
  For EVERY degree `d ≥ 1`, EVERY target base `R ≥ 1`, and EVERY dyadic window scale
  `M ≥ dyadicPolyWindowMinM d R` (`= 2 * R * (2 * 3 ^ (d + 12)) + 2 * d * R + 30`):
  1. **Explicit `R ^ d` Surviving First-Hit Family (`∀ idx < R ^ d`)**:
     Each word `u := uWinPoly d R M idx` satisfies:
     - `IsFirstHitOnePair u 0`, `u.length = M - dyadicPolyShiftDelta (binBitLength (3 ^ (d + 10))) ≤ M`,
       `parityWeight u = d + 10`, `canonicalSuffixShift u 1 ≥ 18`, AND
     - `y := exactBackwardQuotient 1 u 0` satisfies `y % 512 = 511`, `y % 81 = 1`,
       `IsSurvivingMod373248Class y`, `2 ^ M ≤ y ∧ y < 2 ^ (M + 1)`,
       `y ∈ dyadicWindowSurvivingQ0Leaves M M`, and
       `∀ L_max ≥ M, y ∈ dyadicWindowSurvivingQ0Leaves L_max M`!
  2. **Pairwise Leaf Injectivity Across All `idx1, idx2 < R ^ d`**:
     `exactBackwardQuotient 1 (uWinPoly d R M idx1) 0 = exactBackwardQuotient 1 (uWinPoly d R M idx2) 0 -> idx1 = idx2`!
  3. **Unconditional Arbitrary-Degree Polynomial Window Occupancy (`∀ L_max ≥ M`)**:
       `(dyadicWindowSurvivingQ0Leaves M M).length ≥ R ^ d` AND
       `∀ L_max ≥ M, (dyadicWindowSurvivingQ0Leaves L_max M).length ≥ R ^ d`!
-/
theorem dyadic_window_arbitrary_degree_polynomial_occupancy
    (d R M : Nat) (hd : d ≥ 1) (hR : R ≥ 1) (hM : M ≥ dyadicPolyWindowMinM d R) :
    let w := d + 10
    let b0 := binBitLength (3 ^ w)
    let delta := dyadicPolyShiftDelta b0
    (∀ idx : Nat, idx < R ^ d ->
      let u := uWinPoly d R M idx
      let y := exactBackwardQuotient 1 u 0
      IsFirstHitOnePair u 0 ∧
      u.length = M - delta ∧
      u.length ≤ M ∧
      parityWeight u = w ∧
      canonicalSuffixShift u 1 = b0 + delta ∧
      y % 512 = 511 ∧
      y % 81 = 1 ∧
      IsSurvivingMod373248Class y ∧
      2 ^ M ≤ y ∧ y < 2 ^ (M + 1) ∧
      y ∈ dyadicWindowSurvivingQ0Leaves M M ∧
      (∀ L_max : Nat, L_max ≥ M -> y ∈ dyadicWindowSurvivingQ0Leaves L_max M)) ∧
    (∀ idx1 idx2 : Nat, idx1 < R ^ d -> idx2 < R ^ d ->
      exactBackwardQuotient 1 (uWinPoly d R M idx1) 0 =
        exactBackwardQuotient 1 (uWinPoly d R M idx2) 0 ->
      idx1 = idx2) ∧
    ((dyadicWindowSurvivingQ0Leaves M M).length ≥ R ^ d ∧
     ∀ L_max : Nat, L_max ≥ M ->
       (dyadicWindowSurvivingQ0Leaves L_max M).length ≥ R ^ d) := by
  dsimp only
  refine ⟨?_, fun idx1 idx2 h1 h2 heq => uWinPoly_inj_idx_w15 d R M idx1 idx2 hd hR hM h1 h2 heq, ?_⟩
  · intro idx hidx
    rcases uWinPoly_per_idx_leaf_spec_w15 d R M idx hd hR hM hidx with
      ⟨hfh, hlen, hle_M, hwt, hsh, h512, h81, _, hcls, hlo, hhi, hmem⟩
    exact ⟨hfh, hlen, hle_M, hwt, hsh, h512, h81, hcls, hlo, hhi, hmem M (Nat.le_refl M), hmem⟩
  · rcases descIdxListW15_spec (R ^ d) with ⟨hd_len, hd_nd, hd_lt⟩
    let fnLeaf : Nat -> Nat := fun idx => exactBackwardQuotient 1 (uWinPoly d R M idx) 0
    let leavesRd := (descIdxListW15 (R ^ d)).map fnLeaf
    have hnd_Rd : NoDupNat leavesRd :=
      noDupNat_map_inj_on_w15 fnLeaf (descIdxListW15 (R ^ d)) hd_nd
        (fun a ha b hb heq => uWinPoly_inj_idx_w15 d R M a b hd hR hM (hd_lt a ha) (hd_lt b hb) heq)
    have hlen_Rd : leavesRd.length = R ^ d := by
      dsimp only [leavesRd]; rw [List.length_map, hd_len]
    have hall_L : ∀ L_max : Nat, L_max ≥ M ->
        (dyadicWindowSurvivingQ0Leaves L_max M).length ≥ R ^ d := by
      intro L_max hL_max
      have hsub_Rd : ∀ y ∈ leavesRd, y ∈ dyadicWindowSurvivingQ0Leaves L_max M := by
        intro y hy
        rcases List.mem_map.mp hy with ⟨idx, hidx, rfl⟩
        exact (uWinPoly_per_idx_leaf_spec_w15 d R M idx hd hR hM (hd_lt idx hidx)).2.2.2.2.2.2.2.2.2.2.2 L_max hL_max
      have hle := noDupNat_length_le_of_subset_w15
        (dyadicWindowSurvivingQ0Leaves L_max M) leavesRd hnd_Rd hsub_Rd
      omega
    exact ⟨hall_L M (Nat.le_refl M), hall_L⟩

end CollatzFormal
