/-
  CollatzFormal/Wave16WholeSpace.lean
  Wave 16 Whole-Space Mathematical & CS Proof Loop (Synthesis — Fronts C & D):
  1. Front C (Branches P1.2 & P5.15):
     - Three Coupled 3-Variable `(binBitLength, binaryPopcount, binaryAltTransitions)` Preimage Domino
       Laws (`4^s + 1 -> (2*4^s + 1)/3`, `(8^s - 1)/7 <- (3*nOdd + 1)/2`, & Popcount-Invariant
       `(4^(3s + 2) - 1)/3 -> (2*m - 1)/3` with `ΔP = 0, ΔT = -(4s + 2)`, `341 -> 227`) & Complete 100%
       `(0, ∞)^3` All-Bases Two-Sided 3-Variable Exponential Impossibility (`∀ M_0 ≥ 3, ∀ p_L, q_L, p_P, q_P, p_T, q_T ≥ 1`),
     - End-to-End Global Convergence (`k ≤ (x + 1)^3 + (x + 1)^5`), Genuine 11-Tier `ω^11` Syracuse Cascade
       (`Cone 14 -> Cone 13 -> ... -> Cone 5 -> Φ_diamond2`, `844424133773525 -> 19791190635317` in `24` steps to `1`,
       `+6.84x` `Φ_2` jump), `mod 2^46` Newton–Hensel Odd-Inverse & `Nat`/`Int`/`Q_(6)^+` Agreement +
       Choice-Free Non-Integer Rational Cone-14 Avoidance, `mod 33` Post-Climb Non-Reentry, & `[]`-Axiom `M1/M2/M3`
       Counter-Model Separation for the 13th Solvable `(3x + 1)`-Cousin `T_diamond13`.
  2. Front D (Branches P2.2 & P5.3):
     - Complete Mod-`39366` (`2 * 3^9`, `13122/39366` Surviving Classes on `w ≥ 10`) Markov Shift Bijection,
       Universal `10`-Ones `19683 mod 39366` & `[true, false] ++ 9`-Ones `6561 mod 39366` Locks, Exact
       `1 + 7 + 14 + 5 = 27` Surviving Mod-`512` Prefix-Weight-`9` Quadripartition (`1` all-ones prefix `511`
       forces `w(u) ≥ 10` vs `7` exact-weight-`8` escape witness `ZPOS_DYADIC_LEN11_WEIGHT9_HIGH_PREFIX_ESCAPE`),
       & `3^(w - 10)` (`j = 9`) Multi-Step Fiber Equidistribution,
     - Constructive Digit-by-Digit Mod-`9` Ternary-Carry-Lifted Family `uWinExp B M mask` Compressing
       Window Thresholds to Linear `M ≥ 6377332 + 8 * B` & Proving Unconditional True Exponential
       Surviving-Leaf Dyadic-Window Occupancy `(dyadicWindowSurvivingQ0Leaves L_max M).length ≥ 2 ^ B`
       (`≥ 2 ^ ((M - 6377332) / 8)`) at Linear Horizon `L_max ≥ M` Across `∀ B ≥ 1`.

  Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

import CollatzFormal.Wave16WholeSpaceCore

namespace CollatzFormal

-- ============================================================================
-- SECTION 1: Front C Part 1 (Branch P1.2) — Complete 100% `(0, ∞)^3` 3-Variable
--            `(binBitLength, binaryPopcount, binaryAltTransitions)` Two-Sided
--            Exponential Preimage Impossibility (`W16_H3`)
-- ============================================================================

private theorem mul_pow_w16s (a b : Nat) : ∀ n : Nat, (a * b) ^ n = a ^ n * b ^ n
  | 0 => rfl
  | n + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, mul_pow_w16s a b n]
    ac_rfl

private theorem pow_mono_base_w16s (a b : Nat) (hle : a ≤ b) : ∀ n : Nat, a ^ n ≤ b ^ n
  | 0 => Nat.le_refl 1
  | n + 1 => Nat.mul_le_mul (pow_mono_base_w16s a b hle n) hle

private theorem id_lt_pow2_w16s : ∀ n : Nat, n < 2 ^ n
  | 0 => by decide
  | n + 1 => by
    have ih := id_lt_pow2_w16s n
    have hp := pow2_pos_nat n
    rw [Nat.pow_succ]
    omega

private theorem ite_false_dec_w16s {p : Prop} [inst : Decidable p] {α : Type} {a b : α} (hnp : ¬ p) :
    (if p then a else b) = b := by
  cases inst with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

private theorem bernoulli_nat_mul_w16s (A : Nat) :
    ∀ n : Nat, A ^ (n + 1) + n * A ^ n ≤ A * (A + 1) ^ n
  | 0 => by simp
  | n + 1 => by
    have ih := bernoulli_nat_mul_w16s A n
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

private theorem pow_gt_const_mul_pow_of_lt_w16s (A B K_0 : Nat) (hA : A ≥ 1) (hAB : A < B) :
    let k := K_0 * A
    K_0 * A ^ k < B ^ k := by
  dsimp only
  let k := K_0 * A
  have hbern := bernoulli_nat_mul_w16s A k
  have hb_mono : A * (A + 1) ^ k ≤ A * B ^ k :=
    Nat.mul_le_mul_left A (pow_mono_base_w16s (A + 1) B (by omega) k)
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

private theorem binPopcount_double_w16 : ∀ n : Nat,
    binPopcount (2 * n) = binPopcount n
  | 0 => rfl
  | n + 1 => by
    rw [binPopcount_step_pos (2 * (n + 1)) (by omega), Nat.mul_mod_right, Nat.zero_add,
        Nat.mul_div_right (n + 1) (by decide : 0 < 2)]

private theorem binPopcount_double_add_one_w16 (n : Nat) :
    binPopcount (2 * n + 1) = binPopcount n + 1 := by
  rw [binPopcount_step_pos (2 * n + 1) (by omega)]
  have hm : (2 * n + 1) % 2 = 1 := by omega
  have hd : (2 * n + 1) / 2 = n := by omega
  rw [hm, hd]; omega

private theorem binaryAltTransitionsAux_eq_of_le_w16 :
    ∀ (f1 f2 n : Nat), n ≤ f1 -> n ≤ f2 ->
      binaryAltTransitionsAux f1 n = binaryAltTransitionsAux f2 n
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, n, h1, _ => by rw [show n = 0 by omega]; rfl
  | _ + 1, 0, n, _, h2 => by rw [show n = 0 by omega]; rfl
  | _ + 1, _ + 1, 0, _, _ => rfl
  | _ + 1, _ + 1, 1, _, _ => rfl
  | f1 + 1, f2 + 1, n + 2, h1, h2 => by
    simp only [binaryAltTransitionsAux]
    rw [binaryAltTransitionsAux_eq_of_le_w16 f1 f2 ((n + 2) / 2) (by omega) (by omega)]

private theorem binaryAltTransitions_step_ge2_w16 (m : Nat) (hm : m ≥ 2) :
    binaryAltTransitions m =
      (if m % 2 != (m / 2) % 2 then 1 else 0) + binaryAltTransitions (m / 2) := by
  rcases (⟨m - 2, by omega⟩ : ∃ k : Nat, m = k + 2) with ⟨k, rfl⟩
  unfold binaryAltTransitions
  simp only [binaryAltTransitionsAux]
  rw [binaryAltTransitionsAux_eq_of_le_w16 (k + 1) ((k + 2) / 2) ((k + 2) / 2) (by omega) (Nat.le_refl _)]

private theorem binaryAltTransitions_double_even_w16 (m : Nat) (hm : m ≥ 1) :
    binaryAltTransitions (2 * (2 * m)) = binaryAltTransitions (2 * m) := by
  rw [binaryAltTransitions_step_ge2_w16 (2 * (2 * m)) (by omega)]
  have h1 : (2 * (2 * m)) % 2 = 0 := by omega
  have h2 : (2 * (2 * m)) / 2 = 2 * m := by omega
  have h3 : (2 * m) % 2 = 0 := by omega
  rw [h1, h2, h3]; simp

private theorem binaryAltTransitions_double_odd_w16 (m : Nat) :
    binaryAltTransitions (2 * (2 * m + 1)) = 1 + binaryAltTransitions (2 * m + 1) := by
  rw [binaryAltTransitions_step_ge2_w16 (2 * (2 * m + 1)) (by omega)]
  have h1 : (2 * (2 * m + 1)) % 2 = 0 := by omega
  have h2 : (2 * (2 * m + 1)) / 2 = 2 * m + 1 := by omega
  have h3 : (2 * m + 1) % 2 = 1 := by omega
  rw [h1, h2, h3]; rfl

private theorem binaryAltTransitions_succ_double_even_w16 (m : Nat) (hm : m ≥ 1) :
    binaryAltTransitions (2 * (2 * m) + 1) = 1 + binaryAltTransitions (2 * m) := by
  rw [binaryAltTransitions_step_ge2_w16 (2 * (2 * m) + 1) (by omega)]
  have h1 : (2 * (2 * m) + 1) % 2 = 1 := by omega
  have h2 : (2 * (2 * m) + 1) / 2 = 2 * m := by omega
  have h3 : (2 * m) % 2 = 0 := by omega
  rw [h1, h2, h3]; rfl

private theorem binaryAltTransitions_succ_double_odd_w16 (m : Nat) :
    binaryAltTransitions (2 * (2 * m + 1) + 1) = binaryAltTransitions (2 * m + 1) := by
  rw [binaryAltTransitions_step_ge2_w16 (2 * (2 * m + 1) + 1) (by omega)]
  have h1 : (2 * (2 * m + 1) + 1) % 2 = 1 := by omega
  have h2 : (2 * (2 * m + 1) + 1) / 2 = 2 * m + 1 := by omega
  have h3 : (2 * m + 1) % 2 = 1 := by omega
  rw [h1, h2, h3]; simp

private def vAltDropAuxW16 : Nat -> Nat
  | 0 => 0
  | k + 1 => 64 * vAltDropAuxW16 k + 7

private theorem three_var_domino_families_w16 :
    (∀ s : Nat, s ≥ 2 ->
      let m := 4 ^ s + 1
      let nOdd := (2 * m - 1) / 3
      m % 3 = 2 ∧
      binBitLength m = 2 * s + 1 ∧
      binBitLength nOdd = 2 * s ∧
      binaryPopcount m = 2 ∧
      binaryPopcount nOdd = s + 1 ∧
      binaryAltTransitions m = 2 ∧
      binaryAltTransitions nOdd = 2 * s - 2) ∧
    (∀ s : Nat, s ≥ 2 ->
      let nOdd := (8 ^ s - 1) / 7
      let m := (3 * nOdd + 1) / 2
      m % 3 = 2 ∧
      (2 * m - 1) / 3 = nOdd ∧
      binBitLength m = 3 * s - 2 ∧
      binBitLength nOdd = 3 * s - 2 ∧
      binaryPopcount m = 2 * s - 1 ∧
      binaryPopcount nOdd = s ∧
      binaryAltTransitions m = 2 * s - 3 ∧
      binaryAltTransitions nOdd = 2 * s - 2) ∧
    (∀ s : Nat, s ≥ 1 ->
      let m := (4 ^ (3 * s + 2) - 1) / 3
      let nOdd := (2 * m - 1) / 3
      m % 3 = 2 ∧
      binBitLength m = 6 * s + 3 ∧
      binBitLength nOdd = 6 * s + 2 ∧
      binaryPopcount m = 3 * s + 2 ∧
      binaryPopcount nOdd = 3 * s + 2 ∧
      binaryAltTransitions m = 6 * s + 2 ∧
      binaryAltTransitions nOdd = 2 * s) := by
  refine ⟨?_, ?_, ?_⟩
  · -- F1: `4^s + 1 -> (2*4^s + 1)/3`
    intro s hs2; dsimp only
    rcases eventual_joint_bitlength_popcount_exp_impossibility.1.2.1 s hs2 with
      ⟨hm3, hbl_m, hbl_o, hpop_m, _, hpop_o⟩
    rcases eventual_joint_bitlength_alt_transitions_exp_impossibility.1.2.2.2.1 s hs2 with
      ⟨_, _, _, htr_m, htr_o⟩
    exact ⟨hm3, hbl_m, hbl_o, hpop_m, hpop_o, htr_m, htr_o⟩
  · -- F2: `(8^s - 1)/7 <- (3 * nOdd + 1)/2` (`ΔL = 0, ΔP = -(s - 1), ΔT = +1`)
    have hm7 : ∀ k : Nat, 8 ^ k % 7 = 1 := by
      intro k; induction k with
      | zero => rfl
      | succ k' ih => rw [Nat.pow_succ, Nat.mul_mod, ih]
    have hrec_n : ∀ k : Nat, (8 ^ (k + 1) - 1) / 7 = 8 * ((8 ^ k - 1) / 7) + 1 := by
      intro k; have h7 := hm7 k; have hp := nat_pow_pos_of_pos 8 (by decide) k
      rw [Nat.pow_succ 8 k]; omega
    have hn_tr : ∀ k : Nat, k ≥ 1 ->
        let n0 := (8 ^ k - 1) / 7
        n0 ≥ 1 ∧ n0 % 4 = 1 ∧ binaryAltTransitions n0 = 2 * k - 2 := by
      intro k hk; induction k with
      | zero => omega
      | succ k' ih =>
        cases k' with
        | zero => exact ⟨by decide, by decide, by decide⟩
        | succ k'' =>
          rcases ih (by omega) with ⟨hge, hm4, htr⟩
          let n0 := (8 ^ (k'' + 1) - 1) / 7
          change n0 ≥ 1 at hge; change n0 % 4 = 1 at hm4
          change binaryAltTransitions n0 = 2 * (k'' + 1) - 2 at htr
          have hn_sp : n0 = 2 * (n0 / 2) + 1 := by omega
          have h8n : (8 ^ (k'' + 2) - 1) / 7 = 2 * (2 * (2 * n0)) + 1 := by
            rw [hrec_n (k'' + 1)]; change 8 * n0 + 1 = _; omega
          refine ⟨by rw [h8n]; omega, by rw [h8n]; omega, ?_⟩
          rw [h8n, binaryAltTransitions_succ_double_even_w16 (2 * n0) (by omega),
              binaryAltTransitions_double_even_w16 n0 hge,
              hn_sp, binaryAltTransitions_double_odd_w16 (n0 / 2), ← hn_sp, htr]
          omega
    have hu_tr : ∀ k : Nat, k ≥ 2 ->
        let u0 := (3 * ((8 ^ k - 1) / 7) + 1) / 4
        u0 ≥ 7 ∧ u0 % 4 = 3 ∧ binaryAltTransitions u0 = 2 * k - 4 := by
      intro k hk; induction k with
      | zero => omega
      | succ k' ih =>
        cases k' with
        | zero => omega
        | succ k'' =>
          cases k'' with
          | zero => exact ⟨by decide, by decide, by decide⟩
          | succ k3 =>
            rcases ih (by omega) with ⟨hu_ge, hu_m4, hu_t⟩
            let n0 := (8 ^ (k3 + 2) - 1) / 7
            let u0 := (3 * n0 + 1) / 4
            change u0 ≥ 7 at hu_ge; change u0 % 4 = 3 at hu_m4
            change binaryAltTransitions u0 = 2 * (k3 + 2) - 4 at hu_t
            have hn0_m4 := (hn_tr (k3 + 2) (by omega)).2.1
            change n0 % 4 = 1 at hn0_m4
            have h4u0 : 4 * u0 = 3 * n0 + 1 := by dsimp [u0]; omega
            have hu1_eq : (3 * ((8 ^ (k3 + 3) - 1) / 7) + 1) / 4 = 8 * u0 - 1 := by
              rw [hrec_n (k3 + 2)]; change (3 * (8 * n0 + 1) + 1) / 4 = 8 * u0 - 1; omega
            let r := u0 / 4
            have hu0_sp : u0 = 2 * (2 * r + 1) + 1 := by dsimp [r]; omega
            have htr_u0_r : binaryAltTransitions u0 = binaryAltTransitions (2 * r + 1) := by
              conv => lhs; rw [hu0_sp]
              exact binaryAltTransitions_succ_double_odd_w16 r
            have h8u : 8 * u0 - 1 = 2 * (2 * (2 * (4 * r + 2) + 1) + 1) + 1 := by
              rw [hu0_sp]; omega
            refine ⟨by rw [hu1_eq]; omega, by rw [hu1_eq]; omega, ?_⟩
            rw [hu1_eq, h8u,
                binaryAltTransitions_succ_double_odd_w16 (2 * (4 * r + 2) + 1),
                binaryAltTransitions_succ_double_odd_w16 (4 * r + 2),
                show 2 * (4 * r + 2) + 1 = 2 * (2 * (2 * r + 1)) + 1 by omega,
                binaryAltTransitions_succ_double_even_w16 (2 * r + 1) (by omega),
                binaryAltTransitions_double_odd_w16 r,
                ← htr_u0_r, hu_t]
            omega
    intro s hs2; dsimp only
    rcases eventual_popcount_penalizing_all_bases_joint_exp_impossibility.1.1 s hs2 with
      ⟨hm3, hn_eq, hbl_m, hbl_o, hpop_m, hpop_o⟩
    rcases hn_tr s (by omega) with ⟨_, hm4_n, htr_n⟩
    rcases hu_tr s hs2 with ⟨_, hm4_u, htr_u⟩
    let nOdd := (8 ^ s - 1) / 7
    let u := (3 * nOdd + 1) / 4
    change nOdd % 4 = 1 at hm4_n
    change u % 4 = 3 at hm4_u
    change binaryAltTransitions u = 2 * s - 4 at htr_u
    have hm_eq_2u : (3 * nOdd + 1) / 2 = 2 * (2 * (u / 2) + 1) := by omega
    have hu_sp : 2 * (u / 2) + 1 = u := by omega
    have htr_m : binaryAltTransitions ((3 * nOdd + 1) / 2) = 2 * s - 3 := by
      rw [hm_eq_2u, binaryAltTransitions_double_odd_w16 (u / 2), hu_sp, htr_u]
      omega
    exact ⟨hm3, hn_eq, hbl_m, hbl_o, hpop_m, hpop_o, htr_m, htr_n⟩
  · -- F3: `(4^(3s + 2) - 1)/3 -> (2*m - 1)/3` (`ΔL = -1, ΔP = 0, ΔT = -(4s + 2)`)
    have hm3_4 : ∀ k : Nat, 4 ^ k % 3 = 1 := by
      intro k; induction k with
      | zero => rfl
      | succ k' ih => rw [Nat.pow_succ, Nat.mul_mod, ih]
    have hpop_alt4 : ∀ k : Nat, binPopcount ((4 ^ k - 1) / 3) = k := by
      intro k; induction k with
      | zero => rfl
      | succ k' ih =>
        have h3 := hm3_4 k'
        have hp := nat_pow_pos_of_pos 4 (by decide) k'
        have hrec : (4 ^ (k' + 1) - 1) / 3 = 2 * (2 * ((4 ^ k' - 1) / 3)) + 1 := by
          rw [Nat.pow_succ 4 k']; omega
        rw [hrec, binPopcount_double_add_one_w16, binPopcount_double_w16, ih]
    have hv_pop : ∀ k : Nat,
        9 * (32 * vAltDropAuxW16 k + 3) + 5 = 2 * 4 ^ (3 * k + 2) ∧
        binPopcount (vAltDropAuxW16 k) = 3 * k := by
      intro k; induction k with
      | zero => exact ⟨by decide, rfl⟩
      | succ k' ih =>
        rcases ih with ⟨h9, hp_v⟩
        have h9_next : 9 * (32 * vAltDropAuxW16 (k' + 1) + 3) + 5 = 2 * 4 ^ (3 * (k' + 1) + 2) := by
          simp only [vAltDropAuxW16]
          have hpow : 4 ^ (3 * (k' + 1) + 2) = 64 * 4 ^ (3 * k' + 2) := by
            rw [show 3 * (k' + 1) + 2 = (3 * k' + 2) + 3 by omega, Nat.pow_add 4 _ 3]
            change _ = 64 * _; ac_rfl
          rw [hpow]; omega
        let v0 := vAltDropAuxW16 k'
        have h64 : vAltDropAuxW16 (k' + 1) =
            2 * (2 * (2 * (2 * (2 * (2 * v0))) + 1) + 1) + 1 := by
          simp only [vAltDropAuxW16]; change 64 * v0 + 7 = _; omega
        refine ⟨h9_next, ?_⟩
        rw [h64, binPopcount_double_add_one_w16, binPopcount_double_add_one_w16,
            binPopcount_double_add_one_w16, binPopcount_double_w16,
            binPopcount_double_w16, binPopcount_double_w16]
        dsimp [v0]; omega
    intro s hs1; dsimp only
    rcases eventual_joint_bitlength_alt_transitions_exp_impossibility.1.2.2.2.2.1 s hs1 with
      ⟨hm3, hbl_m, hbl_o, htr_m, htr_o⟩
    rcases hv_pop s with ⟨h9_eq, hp_v⟩
    let v := vAltDropAuxW16 s
    let m := (4 ^ (3 * s + 2) - 1) / 3
    have h4_eq : 4 ^ (3 * s + 2) = 3 * m + 1 := by dsimp [m]; have := hm3_4 (3 * s + 2); omega
    have hn_eq : (2 * m - 1) / 3 = 2 * (2 * (2 * (2 * (2 * v))) + 1) + 1 := by
      dsimp [v]; omega
    have hp_o : binaryPopcount ((2 * m - 1) / 3) = 3 * s + 2 := by
      change binPopcount ((2 * m - 1) / 3) = 3 * s + 2
      rw [hn_eq, binPopcount_double_add_one_w16, binPopcount_double_add_one_w16,
          binPopcount_double_w16, binPopcount_double_w16, binPopcount_double_w16]
      dsimp [v]; omega
    exact ⟨hm3, hbl_m, hbl_o, hpop_alt4 (3 * s + 2), hp_o, htr_m, htr_o⟩

/--
  Theorem W16.3a (`eventual_three_var_bitlength_popcount_alt_exp_impossibility`,
  `zero custom axioms`):
  Three Coupled `(binBitLength, binaryPopcount, binaryAltTransitions)` Preimage Domino Laws
  (including Popcount-Invariant Transition Drop `(4^(3s+2) - 1)/3 -> (2*m - 1)/3` with `ΔP = 0,
  ΔT = -(4s + 2)`, `341 -> 227`, & Constant-`ΔT = +1` Popcount Drop `(8^s - 1)/7 <- (3*nOdd + 1)/2`)
  & Complete 100% `(0, ∞)^3` All-Bases Two-Sided 3-Variable Exponential Preimage Impossibility
  Across ALL `∀ M_0 ≥ 3, ∀ p_L, q_L, p_P, q_P, p_T, q_T ≥ 1` (`Branch P1.2`, witness
  `ZPOS_PREIMAGE_3VAR_POPCOUNT_INVARIANT_ALT_DROP_341_TO_227`, `W16_H3`).
-/
theorem eventual_three_var_bitlength_popcount_alt_exp_impossibility :
    ((∀ s : Nat, s ≥ 2 ->
        let m := 4 ^ s + 1
        let nOdd := (2 * m - 1) / 3
        m % 3 = 2 ∧
        binBitLength m = 2 * s + 1 ∧
        binBitLength nOdd = 2 * s ∧
        binaryPopcount m = 2 ∧
        binaryPopcount nOdd = s + 1 ∧
        binaryAltTransitions m = 2 ∧
        binaryAltTransitions nOdd = 2 * s - 2) ∧
     (∀ s : Nat, s ≥ 2 ->
        let nOdd := (8 ^ s - 1) / 7
        let m := (3 * nOdd + 1) / 2
        m % 3 = 2 ∧
        (2 * m - 1) / 3 = nOdd ∧
        binBitLength m = 3 * s - 2 ∧
        binBitLength nOdd = 3 * s - 2 ∧
        binaryPopcount m = 2 * s - 1 ∧
        binaryPopcount nOdd = s ∧
        binaryAltTransitions m = 2 * s - 3 ∧
        binaryAltTransitions nOdd = 2 * s - 2) ∧
     (∀ s : Nat, s ≥ 1 ->
        let m := (4 ^ (3 * s + 2) - 1) / 3
        let nOdd := (2 * m - 1) / 3
        m % 3 = 2 ∧
        binBitLength m = 6 * s + 3 ∧
        binBitLength nOdd = 6 * s + 2 ∧
        binaryPopcount m = 3 * s + 2 ∧
        binaryPopcount nOdd = 3 * s + 2 ∧
        binaryAltTransitions m = 6 * s + 2 ∧
        binaryAltTransitions nOdd = 2 * s) ∧
     (binBitLength 341 = 9 ∧ binBitLength 227 = 8 ∧
      binaryPopcount 341 = 5 ∧ binaryPopcount 227 = 5 ∧
      binaryAltTransitions 341 = 8 ∧ binaryAltTransitions 227 = 2)) ∧
    (∀ (M_0 : Nat), M_0 ≥ 3 ->
      ∀ (wNum wDen : Nat -> Nat) (c_0 C_hi p_L q_L p_P q_P p_T q_T pTheta qTheta : Nat),
        c_0 ≥ 1 -> p_L ≥ 1 -> q_L ≥ 1 -> p_P ≥ 1 -> q_P ≥ 1 -> p_T ≥ 1 -> q_T ≥ 1 ->
        (∀ n : Nat, n ≥ M_0 ->
          c_0 * (q_L ^ binBitLength n * p_P ^ binaryPopcount n * p_T ^ binaryAltTransitions n) * wDen n ≤
            (p_L ^ binBitLength n * q_P ^ binaryPopcount n * q_T ^ binaryAltTransitions n) * wNum n ∧
          (p_L ^ binBitLength n * q_P ^ binaryPopcount n * q_T ^ binaryAltTransitions n) * wNum n ≤
            C_hi * (q_L ^ binBitLength n * p_P ^ binaryPopcount n * p_T ^ binaryAltTransitions n) * wDen n) ->
        ¬ IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta) := by
  rcases three_var_domino_families_w16 with ⟨hf1, hf2, hf3⟩
  refine ⟨⟨hf1, hf2, hf3, by decide, by decide, by decide, by decide, by decide, by decide⟩, ?_⟩
  intro M_0 hM0 wNum wDen c_0 C_hi p_L q_L p_P q_P p_T q_T pTheta qTheta
    hc0 hpL hqL hpP hqP hpT hqT hsand
  -- Partition `(p_P, q_P, p_T, q_T) ≥ 1` into 4 exhaustive regimes:
  by_cases hpP_lt : p_P < q_P
  · -- Regime 1 (`p_P < q_P`, arbitrary `p_L, q_L, p_T, q_T ≥ 1`): killed in 1 step by F2 (`ΔL = 0, ΔP = -(s - 1), ΔT = +1`)!
    intro hw
    have hq_pos : qTheta > 0 := Nat.lt_of_lt_of_le hw.1 hw.2.1
    let K_0 := C_hi * q_T + M_0 + 2
    let e := K_0 * p_P
    let s := e + 1
    have hs2 : s ≥ 2 := by
      have hm1 : 2 * 1 ≤ K_0 * p_P := Nat.mul_le_mul (by dsimp [K_0]; omega) hpP
      dsimp [s, e]; omega
    rcases hf2 s hs2 with ⟨hm3, hn_eq, hbl_m, hbl_o, hpop_m, hpop_o, htr_m, htr_o⟩
    let nOdd := (8 ^ s - 1) / 7
    let m := (3 * nOdd + 1) / 2
    have hnOdd_M0 : nOdd ≥ M_0 := by
      have hs_M0 : 3 * s - 3 ≥ M_0 := by
        have hm1 : K_0 * 1 ≤ K_0 * p_P := Nat.mul_le_mul_left K_0 hpP
        dsimp [s, e, K_0] at hm1 ⊢; omega
      have hlt := id_lt_pow2_w16s (3 * s - 3)
      have h8_sp : 8 ^ s = 8 * 2 ^ (3 * s - 3) := by
        rw [show (8 : Nat) = 2 ^ 3 from rfl, pow_pow_eq_mul_w5 2 3 s]
        conv => lhs; rw [show 3 * s = 3 + (3 * s - 3) by omega, Nat.pow_add]
      dsimp [nOdd]; rw [h8_sp]; omega
    have hm_M0 : m ≥ M_0 := by dsimp [m]; omega
    have hpre := hw.2.2.2.2 m hm_M0 hm3
    dsimp only at hpre; rw [hn_eq] at hpre
    have hbr : (wNum (2 * m) * wDen nOdd + wNum nOdd * wDen (2 * m)) * wDen m ≤
        wNum m * (wDen (2 * m) * wDen nOdd) :=
      nat_mul_le_cancel_left_w5 qTheta _ _ hq_pos
        (Nat.le_trans hpre (Nat.mul_le_mul_right _ hw.2.1))
    have hd_step : wNum nOdd * wDen m ≤ wNum m * wDen nOdd :=
      nat_mul_le_cancel_right_w5 (wDen (2 * m)) _ _ (hw.2.2.1 (2 * m) (by omega)).2 (by
        rw [show (wNum nOdd * wDen m) * wDen (2 * m) = (wNum nOdd * wDen (2 * m)) * wDen m by ac_rfl,
            show (wNum m * wDen nOdd) * wDen (2 * m) = wNum m * (wDen (2 * m) * wDen nOdd) by ac_rfl]
        rw [Nat.add_mul] at hbr; omega)
    let L := 3 * s - 2
    let T0 := 2 * s - 3
    have hlo_o := (hsand nOdd hnOdd_M0).1
    have hhi_m := (hsand m hm_M0).2
    rw [hbl_o, hpop_o, htr_o] at hlo_o
    rw [hbl_m, hpop_m, htr_m] at hhi_m
    have htr_sp : 2 * s - 2 = T0 + 1 := by dsimp [T0]; omega
    have hpop_sp : 2 * s - 1 = s + e := by dsimp [s]; omega
    rw [htr_sp] at hlo_o; rw [hpop_sp] at hhi_m
    change c_0 * (q_L ^ L * p_P ^ s * p_T ^ (T0 + 1)) * wDen nOdd ≤
      (p_L ^ L * q_P ^ s * q_T ^ (T0 + 1)) * wNum nOdd at hlo_o
    change (p_L ^ L * q_P ^ (s + e) * q_T ^ T0) * wNum m ≤
      C_hi * (q_L ^ L * p_P ^ (s + e) * p_T ^ T0) * wDen m at hhi_m
    let F_c := (p_L ^ L * q_L ^ L * p_P ^ s * q_P ^ s * p_T ^ T0 * q_T ^ T0) * (wDen m * wDen nOdd)
    have hF_pos : F_c > 0 := Nat.mul_le_mul
      (Nat.mul_le_mul
        (Nat.mul_le_mul
          (Nat.mul_le_mul
            (Nat.mul_le_mul
              (Nat.mul_le_mul (nat_pow_pos_of_pos p_L hpL L) (nat_pow_pos_of_pos q_L hqL L))
              (nat_pow_pos_of_pos p_P hpP s))
            (nat_pow_pos_of_pos q_P hqP s))
          (nat_pow_pos_of_pos p_T hpT T0))
        (nat_pow_pos_of_pos q_T hqT T0))
      (Nat.mul_le_mul (hw.2.2.1 m hm_M0).2 (hw.2.2.1 nOdd hnOdd_M0).2)
    have hcomb : F_c * (c_0 * p_T * q_P ^ e) ≤ F_c * ((C_hi * q_T) * p_P ^ e) := by
      have hl : F_c * (c_0 * p_T * q_P ^ e) =
          ((p_L ^ L * q_P ^ (s + e) * q_T ^ T0) * wDen m) *
            (c_0 * (q_L ^ L * p_P ^ s * p_T ^ (T0 + 1)) * wDen nOdd) := by
        dsimp [F_c]; rw [Nat.pow_add q_P s e, Nat.pow_succ p_T T0]; ac_rfl
      have hr : F_c * ((C_hi * q_T) * p_P ^ e) =
          (p_L ^ L * q_P ^ s * q_T ^ (T0 + 1)) *
            ((C_hi * (q_L ^ L * p_P ^ (s + e) * p_T ^ T0) * wDen m) * wDen nOdd) := by
        dsimp [F_c]; rw [Nat.pow_add p_P s e, Nat.pow_succ q_T T0]; ac_rfl
      rw [hl, hr]
      calc ((p_L ^ L * q_P ^ (s + e) * q_T ^ T0) * wDen m) *
            (c_0 * (q_L ^ L * p_P ^ s * p_T ^ (T0 + 1)) * wDen nOdd)
          ≤ ((p_L ^ L * q_P ^ (s + e) * q_T ^ T0) * wDen m) *
              ((p_L ^ L * q_P ^ s * q_T ^ (T0 + 1)) * wNum nOdd) := Nat.mul_le_mul_left _ hlo_o
        _ = (p_L ^ L * q_P ^ s * q_T ^ (T0 + 1)) *
              ((p_L ^ L * q_P ^ (s + e) * q_T ^ T0) * (wNum nOdd * wDen m)) := by ac_rfl
        _ ≤ (p_L ^ L * q_P ^ s * q_T ^ (T0 + 1)) *
              ((p_L ^ L * q_P ^ (s + e) * q_T ^ T0) * (wNum m * wDen nOdd)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hd_step)
        _ = (p_L ^ L * q_P ^ s * q_T ^ (T0 + 1)) *
              (((p_L ^ L * q_P ^ (s + e) * q_T ^ T0) * wNum m) * wDen nOdd) := by ac_rfl
        _ ≤ (p_L ^ L * q_P ^ s * q_T ^ (T0 + 1)) *
              ((C_hi * (q_L ^ L * p_P ^ (s + e) * p_T ^ T0) * wDen m) * wDen nOdd) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hhi_m)
    have hcanc := nat_mul_le_cancel_left_w5 F_c _ _ hF_pos hcomb
    have h1 : 1 * q_P ^ e ≤ (c_0 * p_T) * q_P ^ e := Nat.mul_le_mul_right _ (Nat.mul_le_mul hc0 hpT)
    rw [Nat.one_mul] at h1
    have hqP_le : q_P ^ e ≤ K_0 * p_P ^ e :=
      Nat.le_trans (Nat.le_trans h1 hcanc) (Nat.mul_le_mul_right _ (by dsimp [K_0]; omega))
    have hgt_pow := pow_gt_const_mul_pow_of_lt_w16s p_P q_P K_0 hpP hpP_lt
    dsimp only [e] at hqP_le hgt_pow; omega
  · by_cases hpT_lt : p_T < q_T
    · -- Regime 2 (`p_T < q_T`, arbitrary `p_L, q_L, p_P, q_P ≥ 1`): killed in 1 step by F3 (`ΔP = 0, ΔT = -(4s + 2)`)!
      intro hw
      have hq_pos : qTheta > 0 := Nat.lt_of_lt_of_le hw.1 hw.2.1
      let K_0 := C_hi * q_L + M_0 + 2
      let e := K_0 * p_T
      let s := e + 1
      rcases hf3 s (by dsimp [s]; omega) with ⟨hm3, hbl_m, hbl_o, hpop_m, hpop_o, htr_m, htr_o⟩
      let m := (4 ^ (3 * s + 2) - 1) / 3
      let nOdd := (2 * m - 1) / 3
      have hnOdd_M0 : nOdd ≥ M_0 := by
        have hs_M0 : 6 * s + 1 ≥ M_0 := by
          have hm1 : K_0 * 1 ≤ K_0 * p_T := Nat.mul_le_mul_left K_0 hpT
          dsimp [s, e, K_0] at hm1 ⊢; omega
        have hlt := id_lt_pow2_w16s (6 * s + 1)
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
      let P0 := 3 * s + 2
      let D_e := 4 * s + 2
      have hlo_o := (hsand nOdd hnOdd_M0).1
      have hhi_m := (hsand m hm_M0).2
      rw [hbl_o, hpop_o, htr_o] at hlo_o
      rw [hbl_m, hpop_m, htr_m] at hhi_m
      have h6s2 : 6 * s + 2 = 2 * s + D_e := by dsimp [D_e]; omega
      change c_0 * (q_L ^ (6 * s + 2) * p_P ^ P0 * p_T ^ (2 * s)) * wDen nOdd ≤
        (p_L ^ (6 * s + 2) * q_P ^ P0 * q_T ^ (2 * s)) * wNum nOdd at hlo_o
      change (p_L ^ (6 * s + 3) * q_P ^ P0 * q_T ^ (6 * s + 2)) * wNum m ≤
        C_hi * (q_L ^ (6 * s + 3) * p_P ^ P0 * p_T ^ (6 * s + 2)) * wDen m at hhi_m
      let F_c := (p_L ^ (6 * s + 2) * q_L ^ (6 * s + 2) * p_P ^ P0 * q_P ^ P0 * p_T ^ (2 * s) * q_T ^ (2 * s)) *
        (wDen m * wDen nOdd)
      have hF_pos : F_c > 0 := Nat.mul_le_mul
        (Nat.mul_le_mul
          (Nat.mul_le_mul
            (Nat.mul_le_mul
              (Nat.mul_le_mul
                (Nat.mul_le_mul (nat_pow_pos_of_pos p_L hpL _) (nat_pow_pos_of_pos q_L hqL _))
                (nat_pow_pos_of_pos p_P hpP P0))
              (nat_pow_pos_of_pos q_P hqP P0))
            (nat_pow_pos_of_pos p_T hpT _))
          (nat_pow_pos_of_pos q_T hqT _))
        (Nat.mul_le_mul (hw.2.2.1 m hm_M0).2 (hw.2.2.1 nOdd hnOdd_M0).2)
      have hcomb : F_c * (c_0 * p_L * q_T ^ D_e) ≤ F_c * ((C_hi * q_L) * p_T ^ D_e) := by
        have hl : F_c * (c_0 * p_L * q_T ^ D_e) =
            ((p_L ^ (6 * s + 3) * q_P ^ P0 * q_T ^ (6 * s + 2)) * wDen m) *
              (c_0 * (q_L ^ (6 * s + 2) * p_P ^ P0 * p_T ^ (2 * s)) * wDen nOdd) := by
          dsimp [F_c]
          rw [show 6 * s + 3 = (6 * s + 2) + 1 by omega, Nat.pow_succ p_L (6 * s + 2),
              h6s2, Nat.pow_add q_T (2 * s) D_e]; ac_rfl
        have hr : F_c * ((C_hi * q_L) * p_T ^ D_e) =
            (p_L ^ (6 * s + 2) * q_P ^ P0 * q_T ^ (2 * s)) *
              ((C_hi * (q_L ^ (6 * s + 3) * p_P ^ P0 * p_T ^ (6 * s + 2)) * wDen m) * wDen nOdd) := by
          dsimp [F_c]
          rw [show 6 * s + 3 = (6 * s + 2) + 1 by omega, Nat.pow_succ q_L (6 * s + 2),
              h6s2, Nat.pow_add p_T (2 * s) D_e]; ac_rfl
        rw [hl, hr]
        calc ((p_L ^ (6 * s + 3) * q_P ^ P0 * q_T ^ (6 * s + 2)) * wDen m) *
              (c_0 * (q_L ^ (6 * s + 2) * p_P ^ P0 * p_T ^ (2 * s)) * wDen nOdd)
            ≤ ((p_L ^ (6 * s + 3) * q_P ^ P0 * q_T ^ (6 * s + 2)) * wDen m) *
                ((p_L ^ (6 * s + 2) * q_P ^ P0 * q_T ^ (2 * s)) * wNum nOdd) := Nat.mul_le_mul_left _ hlo_o
          _ = (p_L ^ (6 * s + 2) * q_P ^ P0 * q_T ^ (2 * s)) *
                ((p_L ^ (6 * s + 3) * q_P ^ P0 * q_T ^ (6 * s + 2)) * (wNum nOdd * wDen m)) := by ac_rfl
          _ ≤ (p_L ^ (6 * s + 2) * q_P ^ P0 * q_T ^ (2 * s)) *
                ((p_L ^ (6 * s + 3) * q_P ^ P0 * q_T ^ (6 * s + 2)) * (wNum m * wDen nOdd)) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hd_step)
          _ = (p_L ^ (6 * s + 2) * q_P ^ P0 * q_T ^ (2 * s)) *
                (((p_L ^ (6 * s + 3) * q_P ^ P0 * q_T ^ (6 * s + 2)) * wNum m) * wDen nOdd) := by ac_rfl
          _ ≤ (p_L ^ (6 * s + 2) * q_P ^ P0 * q_T ^ (2 * s)) *
                ((C_hi * (q_L ^ (6 * s + 3) * p_P ^ P0 * p_T ^ (6 * s + 2)) * wDen m) * wDen nOdd) :=
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
              ≤ q_T ^ E_ex * q_T ^ e := Nat.mul_le_mul_right _ (pow_mono_base_w16s p_T q_T (Nat.le_of_lt hpT_lt) E_ex)
            _ = q_T ^ D_e := by rw [← he_sp, Nat.pow_add q_T e E_ex, Nat.mul_comm]
            _ ≤ K_0 * p_T ^ D_e := hq_De
            _ = p_T ^ E_ex * (K_0 * p_T ^ e) := by rw [← he_sp, Nat.pow_add p_T e E_ex]; ac_rfl
        exact nat_mul_le_cancel_left_w5 (p_T ^ E_ex) _ _ (nat_pow_pos_of_pos p_T hpT E_ex) hm1
      have hgt_pow := pow_gt_const_mul_pow_of_lt_w16s p_T q_T K_0 hpT hpT_lt
      dsimp only [e] at hq_e hgt_pow; omega
    · -- Now `q_P ≤ p_P` and `q_T ≤ p_T`:
      have hqP_le_pP : q_P ≤ p_P := by omega
      have hqT_le_pT : q_T ≤ p_T := by omega
      by_cases hstrict : q_P < p_P ∨ q_T < p_T
      · -- Regime 3 (`q_P ≤ p_P ∧ q_T ≤ p_T ∧ (q_P < p_P ∨ q_T < p_T)`): killed in 1 step by F1 (`4^s + 1 -> (2*4^s + 1)/3`)!
        intro hw
        have hq_pos : qTheta > 0 := Nat.lt_of_lt_of_le hw.1 hw.2.1
        let A_c := q_P * (q_T * q_T)
        let B_c := p_P * (p_T * p_T)
        have hAc_pos : A_c ≥ 1 :=
          Nat.mul_le_mul hqP (Nat.mul_le_mul hqT hqT)
        have hAB_lt : A_c < B_c := by
          dsimp [A_c, B_c]
          rcases hstrict with hltP | hltT
          · exact Nat.lt_of_lt_of_le
              (Nat.mul_lt_mul_of_pos_right hltP (Nat.mul_le_mul hqT hqT))
              (Nat.mul_le_mul_left p_P (Nat.mul_le_mul hqT_le_pT hqT_le_pT))
          · have hsq_lt : q_T * q_T < p_T * p_T :=
              Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hltT hqT)
                (Nat.mul_le_mul_right p_T hqT_le_pT)
            exact Nat.lt_of_lt_of_le
              (Nat.mul_lt_mul_of_pos_left hsq_lt hqP)
              (Nat.mul_le_mul_right (p_T * p_T) hqP_le_pP)
        let K_0 := C_hi * q_L + M_0 + 2
        let e := K_0 * A_c
        let s := e + 2
        rcases hf1 s (by dsimp [s]; omega) with ⟨hm3, hbl_m, hbl_o, hpop_m, hpop_o, htr_m, htr_o⟩
        let m := 4 ^ s + 1
        let nOdd := (2 * m - 1) / 3
        have hnOdd_M0 : nOdd ≥ M_0 := by
          have hs_M0 : 2 * s - 1 ≥ M_0 := by
            have hm1 : K_0 * 1 ≤ K_0 * A_c := Nat.mul_le_mul_left K_0 hAc_pos
            dsimp [s, e, K_0] at hm1 ⊢; omega
          have hlt := id_lt_pow2_w16s (2 * s - 1)
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
        rw [hbl_o, hpop_o, htr_o] at hlo_o
        rw [hbl_m, hpop_m, htr_m] at hhi_m
        have hp_sp : s + 1 = 2 + (e + 1) := by dsimp [s]; omega
        have ht_sp : 2 * s - 2 = 2 + 2 * e := by dsimp [s]; omega
        rw [hp_sp, ht_sp] at hlo_o
        let F_c := (p_L ^ (2 * s) * q_L ^ (2 * s) * p_P ^ 2 * q_P ^ 2 * p_T ^ 2 * q_T ^ 2) *
          (wDen m * wDen nOdd)
        have hF_pos : F_c > 0 := Nat.mul_le_mul
          (Nat.mul_le_mul
            (Nat.mul_le_mul
              (Nat.mul_le_mul
                (Nat.mul_le_mul
                  (Nat.mul_le_mul (nat_pow_pos_of_pos p_L hpL _) (nat_pow_pos_of_pos q_L hqL _))
                  (nat_pow_pos_of_pos p_P hpP 2))
                (nat_pow_pos_of_pos q_P hqP 2))
              (nat_pow_pos_of_pos p_T hpT 2))
            (nat_pow_pos_of_pos q_T hqT 2))
          (Nat.mul_le_mul (hw.2.2.1 m hm_M0).2 (hw.2.2.1 nOdd hnOdd_M0).2)
        have hB_pow : p_P ^ (e + 1) * p_T ^ (2 * e) = p_P * B_c ^ e := by
          dsimp [B_c]
          rw [Nat.pow_succ p_P e, ← pow_pow_eq_mul_w5 p_T 2 e,
              show p_T ^ 2 = p_T * p_T by rw [Nat.pow_succ, Nat.pow_one],
              mul_pow_w16s p_P (p_T * p_T) e]
          ac_rfl
        have hA_pow : q_P ^ (e + 1) * q_T ^ (2 * e) = q_P * A_c ^ e := by
          dsimp [A_c]
          rw [Nat.pow_succ q_P e, ← pow_pow_eq_mul_w5 q_T 2 e,
              show q_T ^ 2 = q_T * q_T by rw [Nat.pow_succ, Nat.pow_one],
              mul_pow_w16s q_P (q_T * q_T) e]
          ac_rfl
        have hcomb : F_c * (p_P * (c_0 * p_L * B_c ^ e)) ≤ F_c * (q_P * ((C_hi * q_L) * A_c ^ e)) := by
          have hl : F_c * (p_P * (c_0 * p_L * B_c ^ e)) =
              ((p_L ^ (2 * s + 1) * q_P ^ 2 * q_T ^ 2) * wDen m) *
                (c_0 * (q_L ^ (2 * s) * p_P ^ (2 + (e + 1)) * p_T ^ (2 + 2 * e)) * wDen nOdd) := by
            dsimp [F_c]
            rw [Nat.pow_succ p_L (2 * s), Nat.pow_add p_P 2 (e + 1), Nat.pow_add p_T 2 (2 * e)]
            have heq_b : p_P * (c_0 * p_L * B_c ^ e) = c_0 * p_L * (p_P ^ (e + 1) * p_T ^ (2 * e)) := by
              rw [hB_pow]; ac_rfl
            rw [heq_b]; ac_rfl
          have hr : F_c * (q_P * ((C_hi * q_L) * A_c ^ e)) =
              (p_L ^ (2 * s) * q_P ^ (2 + (e + 1)) * q_T ^ (2 + 2 * e)) *
                ((C_hi * (q_L ^ (2 * s + 1) * p_P ^ 2 * p_T ^ 2) * wDen m) * wDen nOdd) := by
            dsimp [F_c]
            rw [Nat.pow_succ q_L (2 * s), Nat.pow_add q_P 2 (e + 1), Nat.pow_add q_T 2 (2 * e)]
            have heq_a : q_P * ((C_hi * q_L) * A_c ^ e) = (C_hi * q_L) * (q_P ^ (e + 1) * q_T ^ (2 * e)) := by
              rw [hA_pow]; ac_rfl
            rw [heq_a]; ac_rfl
          rw [hl, hr]
          calc ((p_L ^ (2 * s + 1) * q_P ^ 2 * q_T ^ 2) * wDen m) *
                (c_0 * (q_L ^ (2 * s) * p_P ^ (2 + (e + 1)) * p_T ^ (2 + 2 * e)) * wDen nOdd)
              ≤ ((p_L ^ (2 * s + 1) * q_P ^ 2 * q_T ^ 2) * wDen m) *
                  ((p_L ^ (2 * s) * q_P ^ (2 + (e + 1)) * q_T ^ (2 + 2 * e)) * wNum nOdd) :=
                Nat.mul_le_mul_left _ hlo_o
            _ = (p_L ^ (2 * s) * q_P ^ (2 + (e + 1)) * q_T ^ (2 + 2 * e)) *
                  ((p_L ^ (2 * s + 1) * q_P ^ 2 * q_T ^ 2) * (wNum nOdd * wDen m)) := by ac_rfl
            _ ≤ (p_L ^ (2 * s) * q_P ^ (2 + (e + 1)) * q_T ^ (2 + 2 * e)) *
                  ((p_L ^ (2 * s + 1) * q_P ^ 2 * q_T ^ 2) * (wNum m * wDen nOdd)) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hd_step)
            _ = (p_L ^ (2 * s) * q_P ^ (2 + (e + 1)) * q_T ^ (2 + 2 * e)) *
                  (((p_L ^ (2 * s + 1) * q_P ^ 2 * q_T ^ 2) * wNum m) * wDen nOdd) := by ac_rfl
            _ ≤ (p_L ^ (2 * s) * q_P ^ (2 + (e + 1)) * q_T ^ (2 + 2 * e)) *
                  ((C_hi * (q_L ^ (2 * s + 1) * p_P ^ 2 * p_T ^ 2) * wDen m) * wDen nOdd) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hhi_m)
        have hc1 := nat_mul_le_cancel_left_w5 F_c _ _ hF_pos hcomb
        have hc2 : p_P * (c_0 * p_L * B_c ^ e) ≤ p_P * ((C_hi * q_L) * A_c ^ e) :=
          Nat.le_trans hc1 (Nat.mul_le_mul_right _ hqP_le_pP)
        have hc3 := nat_mul_le_cancel_left_w5 p_P _ _ hpP hc2
        have h1 : 1 * B_c ^ e ≤ (c_0 * p_L) * B_c ^ e := Nat.mul_le_mul_right _ (Nat.mul_le_mul hc0 hpL)
        rw [Nat.one_mul] at h1
        have hB_le : B_c ^ e ≤ K_0 * A_c ^ e :=
          Nat.le_trans (Nat.le_trans h1 hc3) (Nat.mul_le_mul_right _ (by dsimp [K_0]; omega))
        have hgt_pow := pow_gt_const_mul_pow_of_lt_w16s A_c B_c K_0 hAc_pos hAB_lt
        dsimp only [e] at hB_le hgt_pow; omega
      · -- Regime 4 (`p_P = q_P ∧ p_T = q_T`): both `P` and `T` cancel identically!
        have heqP : p_P = q_P := by omega
        have heqT : p_T = q_T := by omega
        subst heqP; subst heqT
        apply eventual_popcount_penalizing_all_bases_joint_exp_impossibility.2.2 M_0 hM0
          wNum wDen c_0 C_hi p_L q_L 1 1 pTheta qTheta hc0 hpL hqL (by decide) (by decide)
        intro n hn
        rcases hsand n hn with ⟨hlo, hhi⟩
        let PT := p_P ^ binaryPopcount n * p_T ^ binaryAltTransitions n
        have hPT_pos : PT > 0 :=
          Nat.mul_le_mul (nat_pow_pos_of_pos p_P hpP _) (nat_pow_pos_of_pos p_T hpT _)
        simp only [Nat.one_pow, Nat.mul_one]
        refine ⟨nat_mul_le_cancel_right_w5 PT _ _ hPT_pos ?_,
                nat_mul_le_cancel_right_w5 PT _ _ hPT_pos ?_⟩
        · calc (c_0 * q_L ^ binBitLength n * wDen n) * PT
              = c_0 * (q_L ^ binBitLength n * p_P ^ binaryPopcount n * p_T ^ binaryAltTransitions n) * wDen n := by
                  dsimp [PT]; ac_rfl
            _ ≤ (p_L ^ binBitLength n * p_P ^ binaryPopcount n * p_T ^ binaryAltTransitions n) * wNum n := hlo
            _ = (p_L ^ binBitLength n * wNum n) * PT := by dsimp [PT]; ac_rfl
        · calc (p_L ^ binBitLength n * wNum n) * PT
              = (p_L ^ binBitLength n * p_P ^ binaryPopcount n * p_T ^ binaryAltTransitions n) * wNum n := by
                  dsimp [PT]; ac_rfl
            _ ≤ C_hi * (q_L ^ binBitLength n * p_P ^ binaryPopcount n * p_T ^ binaryAltTransitions n) * wDen n := hhi
            _ = (C_hi * q_L ^ binBitLength n * wDen n) * PT := by dsimp [PT]; ac_rfl


-- ============================================================================
-- SECTION 2: Front C Part 2 (Branch P5.15) — 13th Solvable `(3x + 1)`-Cousin
--            `T_diamond13` with Genuine 11-Tier `ω^11` Cascade
--            (`Cone 14 -> Cone 13 -> ... -> Cone 5 -> Φ_diamond2`, `W16_H3`)
-- ============================================================================

/-- Cone 14 of `T_diamond13`: `796358443 + x = 2 ^ k * 3 ^ m` with `k ≥ 46, m ≥ 1`
    (starting at `x = 2 ^ 46 * 3 - 796358443 = 211105436174549`). -/
def isDiamond13Cone14 (x : Nat) : Prop :=
  x ≥ 211105436174549 ∧ x % 70368744177664 = 70367947819221 ∧ x % 3 = 2 ∧ coprime23Core (796358443 + x) = 1

instance (x : Nat) : Decidable (isDiamond13Cone14 x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/--
  13th solvable mixed-(2, 3) Collatz cousin `T_diamond13` on `Nat`:
  Extends `T_diamond12` by adding Cone 14 (`isDiamond13Cone14 x -> (3 * x + 1) / 128`, a genuine
  `v_2(3x + 1) = 7` Syracuse jump that steps `2 ^ k * 3 ^ m - 796358443 -> 2 ^ (k - 7) * 3 ^ (m + 1) - 18664651`
  directly into `Cone 13 -> Cone 12 -> ... -> Cone 5 -> Φ_diamond2`, e.g. `844424133773525 -> 19791190635317`
  in `24` steps to `1`, jumping `cousinDiamond2Phi` upward `+6.84x` and defeating 10-tier `ω^10` rankings)!
-/
def cousinDiamond13Step (x : Nat) : Nat :=
  if isDiamond13Cone14 x then (3 * x + 1) / 128 else cousinDiamond12Step x

def cousinDiamond13Iter : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamond13Iter k (cousinDiamond13Step x)

private theorem cousinDiamond13Iter_add : ∀ (a b x : Nat),
    cousinDiamond13Iter (a + b) x = cousinDiamond13Iter b (cousinDiamond13Iter a x)
  | 0, _, _ => by simp [cousinDiamond13Iter]
  | a + 1, b, x => by
    rw [Nat.succ_add]
    exact cousinDiamond13Iter_add a b (cousinDiamond13Step x)

/-- Signed extension of `T_diamond13` (`q = 3`) to `Int` for `M2 = Z^-` separation. -/
def cousinDiamond13StepInt (x : Int) : Int :=
  if x ≥ 211105436174549 ∧ x % 70368744177664 = 70367947819221 ∧ x % 3 = 2 ∧ coprime23Core (796358443 + x.toNat) = 1
  then (3 * x + 1) / 128
  else cousinDiamond12StepInt x

def cousinDiamond13IterInt : Nat -> Int -> Int
  | 0, x => x
  | k + 1, x => cousinDiamond13IterInt k (cousinDiamond13StepInt x)

/-- Hensel lift of `invMod17179869184Odd` (`2^34`) to `mod 70368744177664` (`2^46`, `34 * 2 = 68 ≥ 46`). -/
def invMod70368744177664Odd (d : Nat) : Nat :=
  let i17 := invMod17179869184Odd d
  (i17 * (140737488355330 - ((d % 70368744177664) * i17) % 70368744177664)) % 70368744177664

/-- Canonical reduced-pair extension of `T_diamond13` (`q = 3`) to positive `Q_(6)^+`. -/
def cousinDiamond13StepQ6 (p : Nat × Nat) : Nat × Nat :=
  let num := p.1
  let den := p.2
  let r70t := (num * invMod70368744177664Odd den) % 70368744177664
  let r3 := (num * (den % 3)) % 3
  if num ≥ 211105436174549 * den ∧ r70t = 70367947819221 ∧ r3 = 2 ∧ core3 (core2 (796358443 * den + num)) = den
  then reduceRatPair (3 * num + den) (128 * den)
  else cousinDiamond12StepQ6 p

def cousinDiamond13IterQ6 : Nat -> (Nat × Nat) -> (Nat × Nat)
  | 0, p => p
  | k + 1, p => cousinDiamond13IterQ6 k (cousinDiamond13StepQ6 p)

/-- Generalized odd-multiplier `q` step of `T_diamond13` on `Nat` for `M3` (`q = 7`) separation. -/
def cousinDiamond13StepParam (q x : Nat) : Nat :=
  if isDiamond13Cone14 x then (q * x + 1) / 128 else cousinDiamond12StepParam q x

def cousinDiamond13IterParam (q : Nat) : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamond13IterParam q k (cousinDiamond13StepParam q x)

private theorem hensel_inv_lift_w16 (M1 M2 S C d i1 : Nat)
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

private theorem core3_core2_eq_coprime23Core_w16 :
    ∀ (fuel n : Nat), n > 0 -> n ≤ fuel -> core3 (core2 n) = coprime23Core n
  | 0, _, hn, hle => by omega
  | fuel + 1, n, hn, hle => by
    by_cases hev : n % 2 = 0
    · let k := n / 2
      have hk_pos : k > 0 := by dsimp [k]; omega
      rw [show n = 2 * k by dsimp [k]; omega, core2_mul2 k hk_pos, coprime23Core_mul2 k hk_pos]
      exact core3_core2_eq_coprime23Core_w16 fuel k hk_pos (by dsimp [k]; omega)
    · have hodd : n % 2 = 1 := by omega
      rcases core3_decomp n hn with ⟨_, _, _, _, hmul⟩
      have hc3_odd : core3 n % 2 = 1 := by
        by_cases hc3_ev : core3 n % 2 = 0
        · have hm0 : (v3Pow n * core3 n) % 2 = 0 := by rw [Nat.mul_mod, hc3_ev, Nat.mul_zero]
          rw [hmul] at hm0; omega
        · omega
      unfold coprime23Core
      rw [core2_of_odd n hodd, core2_of_odd (core3 n) hc3_odd]

private theorem reduceRatPair_div_exact_w16 (a m : Nat) (hm : m > 0) (hdvd : m ∣ a) :
    reduceRatPair a m = (a / m, 1) := by
  rcases hdvd with ⟨q, rfl⟩
  unfold reduceRatPair
  have hgcd : Nat.gcd (m * q) m = m :=
    Nat.dvd_antisymm (Nat.gcd_dvd_right (m * q) m) (Nat.dvd_gcd ⟨q, rfl⟩ (Nat.dvd_refl m))
  dsimp only
  rw [hgcd, Nat.div_self hm]

private theorem dvd_three_mul_add_one_of_mod_w16 (x M D Qm Qr R Qt : Nat)
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
  Theorem W16.3b (`cousin_diamond13_q6_noninteger_avoids_cone14`,
  choice-free `zero custom axioms`):
  Universal Non-Integer Rational Exclusion from Cone 14 on `M1 = Q_(6)^+`:
  For EVERY reduced non-integer rational `(num, den)` (`Nat.gcd num den = 1` and `den > 1`),
  `core3 (core2 (796358443 * den + num)) ≠ den`, so `cousinDiamond13StepQ6 (num, den)` NEVER enters
  Cone 14 and agrees identically with `cousinDiamond12StepQ6 (num, den)` (`Branch P5.15`, `W16_H3`).
-/
theorem cousin_diamond13_q6_noninteger_avoids_cone14 (num den : Nat)
    (hgcd : Nat.gcd num den = 1) (hden : den > 1) :
    core3 (core2 (796358443 * den + num)) ≠ den ∧
    cousinDiamond13StepQ6 (num, den) = cousinDiamond12StepQ6 (num, den) := by
  have hne : core3 (core2 (796358443 * den + num)) ≠ den := by
    intro heq
    have hdvd_sum : den ∣ (796358443 * den + num) := by
      have hc_dvd : core3 (core2 (796358443 * den + num)) ∣ (796358443 * den + num) :=
        Nat.dvd_trans (core3Aux_dvd_w8 _ _) (core2Aux_dvd_w8 _ _)
      rwa [heq] at hc_dvd
    rcases hdvd_sum with ⟨k, hk⟩
    have hdvd_num : den ∣ num := ⟨k - 796358443, by
      rcases Nat.lt_or_ge k 796358443 with hlt | hge
      · exfalso
        have hm := Nat.mul_le_mul_left den (show k ≤ 796358442 by omega)
        omega
      · rw [Nat.mul_sub_left_distrib]; omega⟩
    have hdvd_gcd : den ∣ Nat.gcd num den := Nat.dvd_gcd hdvd_num (Nat.dvd_refl den)
    rw [hgcd] at hdvd_gcd
    rcases hdvd_gcd with ⟨c, hc⟩
    cases c with
    | zero => omega
    | succ c' =>
      have hle := Nat.mul_le_mul_left den (show 1 ≤ c' + 1 by omega); omega
  refine ⟨hne, ?_⟩
  unfold cousinDiamond13StepQ6
  dsimp only
  exact ite_false_dec_w16s (fun ⟨_, _, _, hc⟩ => hne hc)

/--
  Theorem W16.3c (`cousin_diamond13_hensel_inv_and_nat_int_q6_agreement`,
  `zero custom axioms`):
  Universal Newton–Hensel `mod 2^46` (`70368744177664`) Odd-Inverse Correctness, Exact
  `Nat`/`Int`/`Q_(6)^+` Step Agreement, & Universal Non-Integer Rational Exclusion from Cone 14
  on `M1 = Q_(6)^+` (`Branch P5.15`, `W16_H3`).
-/
theorem cousin_diamond13_hensel_inv_and_nat_int_q6_agreement :
    (∀ d : Nat, d % 2 = 1 -> (d * invMod70368744177664Odd d) % 70368744177664 = 1) ∧
    (∀ x : Nat, cousinDiamond13StepInt (x : Int) = (cousinDiamond13Step x : Int)) ∧
    (∀ x : Nat, cousinDiamond13StepQ6 (x, 1) = (cousinDiamond13Step x, 1)) ∧
    (∀ num den : Nat, Nat.gcd num den = 1 -> den > 1 ->
      core3 (core2 (796358443 * den + num)) ≠ den ∧
      cousinDiamond13StepQ6 (num, den) = cousinDiamond12StepQ6 (num, den)) := by
  rcases invMod17179869184Odd_mul_and_q6_nat_agreement with ⟨hinv17, _⟩
  have hinv46 : ∀ d : Nat, d % 2 = 1 -> (d * invMod70368744177664Odd d) % 70368744177664 = 1 := by
    intro d hodd
    exact hensel_inv_lift_w16 17179869184 70368744177664 4194304 140737488355330 d (invMod17179869184Odd d)
      (by decide) (by decide) (by decide) (hinv17 d hodd)
  refine ⟨hinv46, ?_, ?_, cousin_diamond13_q6_noninteger_avoids_cone14⟩
  · intro x
    have h1 : ((x : Int) ≥ 211105436174549) ↔ (x ≥ 211105436174549) := by omega
    have h2 : ((x : Int) % 70368744177664 = 70367947819221) ↔ (x % 70368744177664 = 70367947819221) :=
      ⟨Int.ofNat.inj, congrArg Int.ofNat⟩
    have h3 : ((x : Int) % 3 = 2) ↔ (x % 3 = 2) := ⟨Int.ofNat.inj, congrArg Int.ofNat⟩
    have hdiv : ((3 * (x : Int) + 1) / 128) = (((3 * x + 1) / 128 : Nat) : Int) := by omega
    have htoNat : (x : Int).toNat = x := rfl
    unfold cousinDiamond13StepInt cousinDiamond13Step isDiamond13Cone14
    rw [htoNat]; simp only [h1, h2, h3]
    by_cases hc14 : x ≥ 211105436174549 ∧ x % 70368744177664 = 70367947819221 ∧ x % 3 = 2 ∧ coprime23Core (796358443 + x) = 1
    · simp only [hc14, and_self, ite_true, hdiv]
    · simp only [hc14, ite_false]
      exact cousin_diamond12_hensel_inv_and_nat_int_q6_agreement.2.2.1 x
  · have hi46 : invMod70368744177664Odd 1 = 1 := by decide
    have hm3_1 : (1 : Nat) % 3 = 1 := by decide
    intro x
    have hcc : core3 (core2 (796358443 + x)) = coprime23Core (796358443 + x) :=
      core3_core2_eq_coprime23Core_w16 (796358443 + x) (796358443 + x) (by omega) (Nat.le_refl _)
    unfold cousinDiamond13StepQ6 cousinDiamond13Step isDiamond13Cone14
    simp only [hi46, hm3_1, Nat.mul_one, hcc]
    by_cases hc14 : x ≥ 211105436174549 ∧ x % 70368744177664 = 70367947819221 ∧ x % 3 = 2 ∧ coprime23Core (796358443 + x) = 1
    · simp only [hc14, and_self, ite_true]
      exact reduceRatPair_div_exact_w16 (3 * x + 1) 128 (by decide)
        (dvd_three_mul_add_one_of_mod_w16 x 70368744177664 128 549755813888 549749592337 85 2
          (by decide) hc14.2.1 (by decide))
    · simp only [hc14, ite_false]
      exact cousin_diamond12_hensel_inv_and_nat_int_q6_agreement.2.2.2.1 x

private theorem cousinDiamond13Step_pos (x : Nat) (hx : x > 0) : cousinDiamond13Step x > 0 := by
  unfold cousinDiamond13Step
  by_cases hc14 : isDiamond13Cone14 x
  · simp only [hc14, ite_true]
    have hge : x ≥ 211105436174549 := hc14.1
    clear hc14
    exact Nat.lt_of_lt_of_le (by decide : 0 < (3 * 211105436174549 + 1) / 128)
      (Nat.div_le_div_right (by omega))
  · simp only [hc14, ite_false]
    have hd12_pos : cousinDiamond12Step x > 0 := by
      unfold cousinDiamond12Step
      by_cases hc13 : isDiamond12Cone13 x
      · simp only [hc13, ite_true]
        have hge : x ≥ 1649248777013 := hc13.1
        clear hc13 hc14
        exact Nat.lt_of_lt_of_le (by decide : 0 < (3 * 1649248777013 + 1) / 32)
          (Nat.div_le_div_right (by omega))
      · simp only [hc13, ite_false]; exact cousinDiamond11Step_pos x hx
    exact hd12_pos

private theorem d13_eq_d12_of_not_cone14 (x : Nat) (hnc14 : ¬ isDiamond13Cone14 x) :
    cousinDiamond13Step x = cousinDiamond12Step x := by
  unfold cousinDiamond13Step; simp [hnc14]

-- Modular Cone-14 avoidance helpers (`70367947819221 % 8192 = 2261, % 2048 = 213, % 64 = 21, % 32 = 21, % 8 = 5`):

private theorem mod8192_of_cone14 (z : Nat) (hc14 : isDiamond13Cone14 z) : z % 8192 = 2261 := by
  have h := congrArg (· % 8192) hc14.2.1
  rw [Nat.mod_mod_of_dvd z (by decide : 8192 ∣ 70368744177664),
      show 70367947819221 % 8192 = 2261 by decide] at h
  exact h

private theorem mod2048_of_cone14 (z : Nat) (hc14 : isDiamond13Cone14 z) : z % 2048 = 213 := by
  have h := congrArg (· % 2048) (mod8192_of_cone14 z hc14)
  rw [Nat.mod_mod_of_dvd z (by decide : 2048 ∣ 8192), show 2261 % 2048 = 213 by decide] at h
  exact h

private theorem mod64_of_cone14 (z : Nat) (hc14 : isDiamond13Cone14 z) : z % 64 = 21 := by
  have h := congrArg (· % 64) (mod2048_of_cone14 z hc14)
  rw [Nat.mod_mod_of_dvd z (by decide : 64 ∣ 2048), show 213 % 64 = 21 by decide] at h
  exact h

private theorem mod32_of_cone14 (z : Nat) (hc14 : isDiamond13Cone14 z) : z % 32 = 21 := by
  have h := congrArg (· % 32) (mod64_of_cone14 z hc14)
  rw [Nat.mod_mod_of_dvd z (by decide : 32 ∣ 64), show 21 % 32 = 21 by decide] at h
  exact h

private theorem not_cone14_of_even (z : Nat) (hev : z % 2 = 0) : ¬ isDiamond13Cone14 z := by
  intro hc14
  have h := congrArg (· % 2) (mod32_of_cone14 z hc14)
  rw [Nat.mod_mod_of_dvd z (by decide : 2 ∣ 32), hev] at h
  cases h

private theorem not_cone14_of_mod4_eq_3 (z : Nat) (hm4 : z % 4 = 3) : ¬ isDiamond13Cone14 z := by
  intro hc14
  have h := congrArg (· % 4) (mod32_of_cone14 z hc14)
  rw [Nat.mod_mod_of_dvd z (by decide : 4 ∣ 32), hm4] at h
  cases h

private theorem not_cone14_of_mod8_ne_5 (z : Nat) (hm8 : z % 8 ≠ 5) : ¬ isDiamond13Cone14 z := by
  intro hc14
  have h := congrArg (· % 8) (mod32_of_cone14 z hc14)
  rw [Nat.mod_mod_of_dvd z (by decide : 8 ∣ 32)] at h
  exact hm8 h

private theorem not_cone14_of_mod32_ne_21 (z : Nat) (hm32 : z % 32 ≠ 21) : ¬ isDiamond13Cone14 z :=
  fun hc14 => hm32 (mod32_of_cone14 z hc14)

private theorem not_cone14_of_mod64_ne_21 (z : Nat) (hm64 : z % 64 ≠ 21) : ¬ isDiamond13Cone14 z :=
  fun hc14 => hm64 (mod64_of_cone14 z hc14)

private theorem not_cone14_of_mod2048_ne_213 (z : Nat) (hm2k : z % 2048 ≠ 213) : ¬ isDiamond13Cone14 z :=
  fun hc14 => hm2k (mod2048_of_cone14 z hc14)

private theorem not_cone14_of_mod8192_ne_2261 (z : Nat) (hm8k : z % 8192 ≠ 2261) : ¬ isDiamond13Cone14 z :=
  fun hc14 => hm8k (mod8192_of_cone14 z hc14)

private theorem not_cone14_of_mod3_ne_2 (z : Nat) (hm3 : z % 3 ≠ 2) : ¬ isDiamond13Cone14 z :=
  fun ⟨_, _, h3, _⟩ => hm3 h3

private theorem not_cone14_six_mul_pow9_sub1_w16 (m : Nat) :
    ¬ isDiamond13Cone14 (6 * 9 ^ m - 1) := by
  cases m with
  | zero => rintro ⟨hge, _, _, _⟩; simp at hge
  | succ n =>
    have h9_33 : ∀ t : Nat,
        9 ^ (t + 1) % 33 = 9 ∨ 9 ^ (t + 1) % 33 = 15 ∨ 9 ^ (t + 1) % 33 = 3 ∨
        9 ^ (t + 1) % 33 = 27 ∨ 9 ^ (t + 1) % 33 = 12 := by
      intro t; induction t with
      | zero => exact Or.inl rfl
      | succ t' ih =>
        rw [Nat.pow_succ 9 (t' + 1), Nat.mul_mod]
        rcases ih with h | h | h | h | h <;> (rw [h]; decide)
    have h2_33 : ∀ t : Nat,
        2 ^ t % 33 = 1 ∨ 2 ^ t % 33 = 2 ∨ 2 ^ t % 33 = 4 ∨ 2 ^ t % 33 = 8 ∨ 2 ^ t % 33 = 16 ∨
        2 ^ t % 33 = 32 ∨ 2 ^ t % 33 = 31 ∨ 2 ^ t % 33 = 29 ∨ 2 ^ t % 33 = 25 ∨ 2 ^ t % 33 = 17 := by
      intro t; induction t with
      | zero => exact Or.inl rfl
      | succ t' ih =>
        rw [Nat.pow_succ 2 t', Nat.mul_mod]
        rcases ih with h | h | h | h | h | h | h | h | h | h <;> (rw [h]; decide)
    rcases (⟨9 ^ (n + 1), rfl⟩ : ∃ p9 : Nat, p9 = 9 ^ (n + 1)) with ⟨P9, hP9_def⟩
    have hp9_pos : P9 ≥ 1 := by rw [hP9_def]; exact nat_pow_pos_of_pos 9 (by decide) (n + 1)
    rcases (⟨2 * P9 + 265452814, rfl⟩ : ∃ a0 : Nat, a0 = 2 * P9 + 265452814) with ⟨A, hA_def⟩
    have hsum_eq : 796358443 + (6 * 9 ^ (n + 1) - 1) = 3 * A := by
      rw [← hP9_def, hA_def]; omega
    have hN_pos : 3 * A > 0 := by rw [hA_def]; omega
    have hA_m3 : A % 3 = 1 := by
      have hp9_3 : P9 % 3 = 0 := by rw [hP9_def, Nat.pow_succ 9 n]; omega
      rw [hA_def]; omega
    have hA_33 : A % 33 = 7 ∨ A % 33 = 19 ∨ A % 33 = 28 ∨ A % 33 = 10 ∨ A % 33 = 13 := by
      rw [hA_def, hP9_def]
      have hdm := (Nat.div_add_mod (9 ^ (n + 1)) 33).symm
      rcases h9_33 n with h | h | h | h | h <;> clear h9_33 h2_33 hsum_eq hN_pos hA_m3 <;> omega
    rintro ⟨hc_ge, hc_46, hc_3, hcop⟩
    clear hc_ge hc_46 hc_3
    rw [hsum_eq] at hcop
    rcases decomp_2_3_exact (3 * A) hN_pos with ⟨hd1, hd2, hd3, hd4, hd5, hmul⟩
    clear hd1 hd2 hd3 hd4 hd5
    rw [hcop, Nat.mul_one] at hmul
    rcases eq_pow2_of_v2Pow_aux (3 * A) (3 * A) hN_pos (Nat.le_refl _) with ⟨k, hk⟩
    rcases eq_pow3_of_v3Pow_aux (3 * A) (3 * A) hN_pos (Nat.le_refl _) with ⟨r, hr⟩
    rw [hk, hr] at hmul
    clear hcop hsum_eq hk hr hA_def hP9_def hp9_pos hN_pos h9_33
    have hr1 : r = 1 := by
      cases r with
      | zero =>
        rw [Nat.pow_zero, Nat.mul_one] at hmul
        exact False.elim (pow2_mod3_nonzero_w5 k (by clear h2_33 hA_33; omega))
      | succ r' =>
        cases r' with
        | zero => rfl
        | succ r'' =>
          exfalso
          have hr_sp : 3 ^ (r'' + 2) = 3 * (3 * 3 ^ r'') := by
            rw [Nat.pow_succ, Nat.pow_succ]; ac_rfl
          have h3_pull : 2 ^ k * (3 * (3 * 3 ^ r'')) = 3 * (3 * (2 ^ k * 3 ^ r'')) := by ac_rfl
          rw [hr_sp, h3_pull] at hmul
          have hA_div3 : A = 3 * (2 ^ k * 3 ^ r'') :=
            Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3) hmul.symm
          rw [hA_div3, Nat.mul_mod_right] at hA_m3
          cases hA_m3
    rw [hr1, Nat.pow_one] at hmul
    have hA_pow2 : A = 2 ^ k := by clear h2_33 hA_33 hr1; omega
    rw [hA_pow2] at hA_33
    rcases h2_33 k with h | h | h | h | h | h | h | h | h | h <;>
      clear h2_33 hmul hA_pow2 hr1 <;> omega

/--
  Theorem W16.3d (`cousin_diamond13_outside_cones4to14_descent_and_mod33_nonreentry`,
  `zero custom axioms`):
  Strict `cousinDiamond2Phi` Descent Outside Cones 4..14 & Universal `mod 33` Post-Climb
  Non-Reentry into Cone 14 (`∀ m : Nat, ¬ isDiamond13Cone14 (6 * 9 ^ m - 1)`,
  `Branch P5.15`, `W16_H3`).
-/
theorem cousin_diamond13_outside_cones4to14_descent_and_mod33_nonreentry :
    (∀ x : Nat, x > 2 ->
      ¬ isDiamond3Cone4 x -> ¬ isDiamond4Cone5 x ->
      ¬ isDiamond5Cone6 x -> ¬ isDiamond6Cone7 x ->
      ¬ isDiamond7Cone8 x -> ¬ isDiamond8Cone9 x ->
      ¬ isDiamond9Cone10 x -> ¬ isDiamond10Cone11 x ->
      ¬ isDiamond11Cone12 x -> ¬ isDiamond12Cone13 x ->
      ¬ isDiamond13Cone14 x ->
      cousinDiamond2Phi (cousinDiamond13Step x) < cousinDiamond2Phi x) ∧
    (∀ m : Nat, ¬ isDiamond13Cone14 (6 * 9 ^ m - 1)) := by
  refine ⟨?_, not_cone14_six_mul_pow9_sub1_w16⟩
  intro x hx hnc4 hnc5 hnc6 hnc7 hnc8 hnc9 hnc10 hnc11 hnc12 hnc13 hnc14
  rw [d13_eq_d12_of_not_cone14 x hnc14]
  exact cousin_diamond12_outside_cones4to13_descent_and_mod63_nonreentry.1 x hx
    hnc4 hnc5 hnc6 hnc7 hnc8 hnc9 hnc10 hnc11 hnc12 hnc13

private theorem isDiamond12Cone13_of_pow2_pow3_w16 (a b : Nat) (ha : a ≥ 39) (hb : b ≥ 1) :
    isDiamond12Cone13 (2 ^ a * 3 ^ b - 18664651) := by
  have hc : (2 : Nat) ^ 39 = 549755813888 := by decide
  have hp2_ge : 2 ^ a ≥ 549755813888 := by rw [← hc]; exact pow2_mono_nat ha
  have hp3_ge : 3 ^ b ≥ 3 := by simpa using nat_pow_mono_exp_pos 3 1 b (by decide) hb
  have hprod_ge : 2 ^ a * 3 ^ b ≥ 1649267441664 := by simpa using Nat.mul_le_mul hp2_ge hp3_ge
  have hp549 : 549755813888 ∣ 2 ^ a * 3 ^ b := by
    rw [show a = 39 + (a - 39) by omega, Nat.pow_add 2 39 (a - 39), hc, Nat.mul_assoc]
    exact ⟨2 ^ (a - 39) * 3 ^ b, rfl⟩
  have hp3_div : 3 ∣ 2 ^ a * 3 ^ b := by
    rw [show b = 1 + (b - 1) by omega, Nat.pow_add 3 1 (b - 1), Nat.pow_one,
        ← Nat.mul_assoc (2 ^ a) 3, Nat.mul_comm (2 ^ a) 3, Nat.mul_assoc]
    exact ⟨2 ^ a * 3 ^ (b - 1), rfl⟩
  refine ⟨by clear hc hp2_ge hp3_ge hp549 hp3_div; generalize 2 ^ a * 3 ^ b = P at hprod_ge ⊢; omega,
          ?_, ?_, ?_⟩
  · rcases hp549 with ⟨k, hk⟩
    clear hc hp2_ge hp3_ge hp3_div
    generalize 2 ^ a * 3 ^ b = P at hprod_ge hk ⊢
    rw [hk, show k = (k - 1) + 1 by omega, Nat.mul_add 549755813888 (k - 1) 1, Nat.mul_one]
    generalize k - 1 = k'
    rw [show 549755813888 * k' + 549755813888 - 18664651 = 549737149237 + 549755813888 * k' by omega,
        Nat.add_mul_mod_self_left]
  · rcases hp3_div with ⟨k3, hk3⟩
    clear hc hp2_ge hp3_ge hp549
    generalize 2 ^ a * 3 ^ b = P at hprod_ge hk3 ⊢; omega
  · rw [show 18664651 + (2 ^ a * 3 ^ b - 18664651) = 2 ^ a * 3 ^ b by
          clear hc hp2_ge hp3_ge hp549 hp3_div; generalize 2 ^ a * 3 ^ b = P at hprod_ge ⊢; omega]
    exact coprime23Core_pow2_pow3 a b

private theorem d13_eq_d3_of_even_w16 (z : Nat) (hev : z % 2 = 0) :
    cousinDiamond13Step z = cousinDiamond3Step z := by
  rw [d13_eq_d12_of_not_cone14 z (not_cone14_of_even z hev)]
  unfold cousinDiamond12Step
  have hnc13 : ¬ isDiamond12Cone13 z := by
    rintro ⟨_, h39, _, _⟩
    have h2 := congrArg (· % 2) h39
    rw [Nat.mod_mod_of_dvd z (by decide : 2 ∣ 549755813888), hev] at h2
    cases h2
  rw [ite_false_dec_w16s hnc13,
      cousinDiamond11Step_eq_d10_of_not_cone12 z (not_cone12_of_even z hev),
      cousinDiamond10Step_eq_d9_of_not_cone11 z (not_cone11_of_even z hev),
      cousinDiamond9Step_eq_d8_of_not_cone10 z (not_cone10_of_even z hev),
      cousinDiamond8Step_eq_d7_of_not_cone9 z (not_cone9_of_even z hev),
      cousinDiamond7Step_eq_d6_of_not_cone8 z (not_cone8_of_even z hev),
      cousinDiamond6Step_eq_d5_of_not_cone7 z (not_cone7_of_even z hev),
      cousinDiamond5Step_eq_d4_of_not_cone6 z (not_cone6_of_even z hev),
      cousinDiamond4Step_eq_d3_of_not_cone5 z (by rintro ⟨_, h32, _, _⟩; omega)]

private theorem not_cone13_of_mod32_ne_21_w16 (z : Nat) (hm32 : z % 32 ≠ 21) : ¬ isDiamond12Cone13 z := by
  rintro ⟨_, h39, _, _⟩
  have h := congrArg (· % 32) h39
  rw [Nat.mod_mod_of_dvd z (by decide : 32 ∣ 549755813888),
      show 549737149237 % 32 = 21 by decide] at h
  exact hm32 h

private theorem d12_eq_d11_of_not_cone13_w16 (x : Nat) (hnc13 : ¬ isDiamond12Cone13 x) :
    cousinDiamond12Step x = cousinDiamond11Step x := by
  unfold cousinDiamond12Step; exact ite_false_dec_w16s hnc13

private theorem cousin_diamond13_mersenne_scaled :
    ∀ (k a q : Nat), k + 1 ≤ a -> q ≥ 1 ->
      cousinDiamond13Iter k (2 ^ a * q - 1) = 3 ^ k * 2 ^ (a - k) * q - 1
  | 0, _, _, _, _ => by simp [cousinDiamond13Iter]
  | k + 1, a, q, hka, hq => by
    have hp4 : 2 ^ a * q = 4 * (2 ^ (a - 2) * q) := by
      conv => lhs; rw [show a = (a - 2) + 2 by omega]
      rw [Nat.pow_add 2 (a - 2) 2, show (2 : Nat) ^ 2 = 4 from rfl,
          Nat.mul_comm (2 ^ (a - 2)) 4, Nat.mul_assoc]
    have hm_pos : 2 ^ (a - 2) * q ≥ 1 := Nat.mul_le_mul (pow2_pos_nat (a - 2)) hq
    simp only [cousinDiamond13Iter]
    rw [d13_eq_d12_of_not_cone14 _ (not_cone14_of_mod4_eq_3 _ (by omega)),
        d12_eq_d11_of_not_cone13_w16 _ (not_cone13_of_mod32_ne_21_w16 _ (by omega))]
    have hd11 := cousin_diamond11_mersenne_scaled 1 a q (by omega) hq
    simp only [cousinDiamond11Iter, Nat.pow_one] at hd11
    rw [show cousinDiamond11Step (2 ^ a * q - 1) = 2 ^ (a - 1) * (3 * q) - 1 by
          rw [hd11]; apply congrArg (· - 1); ac_rfl,
        cousin_diamond13_mersenne_scaled k (a - 1) (3 * q) (by omega) (by omega),
        show a - 1 - k = a - (k + 1) by omega, Nat.pow_succ 3 k]
    apply congrArg (· - 1); ac_rfl

private theorem cousin_diamond13_even9_spine_drain :
    ∀ k : Nat, cousinDiamond13Iter k ((9 ^ (k + 1) - 1) / 4) = 2
  | 0 => rfl
  | k + 1 => by
    let j := k + 1
    have hp9j_ge9 : 9 ^ j ≥ 9 := by
      dsimp [j]; rw [Nat.pow_succ]; have hp := nat_pow_pos_of_pos 9 (by decide) k; omega
    have hp9j_m8 := pow9_mod8_eq_one_w5 j
    let q := (9 ^ j - 1) / 8
    have hp9j_eq : 9 ^ j = 8 * q + 1 := by dsimp [q]; omega
    have he_j1 : (9 ^ (j + 1) - 1) / 4 = 18 * q + 2 := by rw [Nat.pow_succ 9 j, hp9j_eq]; omega
    have he_j : (9 ^ j - 1) / 4 = 2 * q := by rw [hp9j_eq]; omega
    simp only [cousinDiamond13Iter]
    change cousinDiamond13Iter k (cousinDiamond13Step ((9 ^ (j + 1) - 1) / 4)) = 2
    rw [he_j1, d13_eq_d3_of_even_w16 _ (by omega)]
    have hd3 : cousinDiamond3Step (18 * q + 2) = (9 ^ j - 1) / 4 := by
      rw [he_j]; unfold cousinDiamond3Step
      have hq_pos : q ≥ 1 := by dsimp [q]; omega
      have hodd_f : ¬ ((18 * q + 2) % 2 = 1) := by omega
      have h18_t : 18 * q + 2 ≥ 20 ∧ (18 * q + 2) % 18 = 2 := ⟨by omega, by omega⟩
      simp only [hodd_f, h18_t, and_self, ite_true, ite_false]; omega
    rw [hd3]
    exact cousin_diamond13_even9_spine_drain k

private theorem cousin_diamond13_pow3_sub1_drain :
    ∀ k : Nat, cousinDiamond13Iter k (3 ^ (k + 1) - 1) = 2
  | 0 => rfl
  | k + 1 => by
    let j := k + 1
    have hp3_ge3 : 3 ^ j ≥ 3 := by dsimp [j]; rw [Nat.pow_succ]; have := pow3_pos_nat k; omega
    have ho_j1 := pow3_odd_nat_sec8 (j + 1)
    have hp_j1 := pow3_pos_nat (j + 1)
    simp only [cousinDiamond13Iter]
    change cousinDiamond13Iter k (cousinDiamond13Step (3 ^ (j + 1) - 1)) = 2
    rw [d13_eq_d3_of_even_w16 _ (by omega)]
    have hd3 : cousinDiamond3Step (3 ^ (j + 1) - 1) = 3 ^ j - 1 := by
      have hev : ¬ ((3 ^ (j + 1) - 1) % 2 = 1) := by omega
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
    rw [hd3]
    exact cousin_diamond13_pow3_sub1_drain k

private theorem cousin_diamond13_cone5_two_step_climb :
    ∀ (q_c a b : Nat), 3 * q_c + 2 ≤ a -> b ≥ 1 ->
      cousinDiamond13Iter (2 * q_c) (2 ^ a * 3 ^ b - 7) =
        2 ^ (a - 3 * q_c) * 3 ^ (b + 2 * q_c) - 7
  | 0, _, _, _, _ => by simp [cousinDiamond13Iter]
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
    have hs1 : cousinDiamond13Step (2 ^ a * 3 ^ b - 7) = mid := by
      rw [d13_eq_d12_of_not_cone14 _ (not_cone14_of_mod32_ne_21 _ (by have := hc5.2.1; omega)),
          d12_eq_d11_of_not_cone13_w16 _ (not_cone13_of_mod32_ne_21_w16 _ (by have := hc5.2.1; omega))]
      exact hd11_s1
    have hs2 : cousinDiamond13Step mid = 2 ^ (a - 3) * 3 ^ (b + 2) - 7 := by
      rw [d13_eq_d12_of_not_cone14 _ (not_cone14_of_mod4_eq_3 _ hmid_4),
          d12_eq_d11_of_not_cone13_w16 _ (not_cone13_of_mod32_ne_21_w16 _ (by omega))]
      exact hd11_2
    rw [Nat.mul_succ 2 q_c, Nat.add_comm (2 * q_c) 2, cousinDiamond13Iter_add 2 (2 * q_c)]
    have hi2 : cousinDiamond13Iter 2 (2 ^ a * 3 ^ b - 7) = 2 ^ (a - 3) * 3 ^ (b + 2) - 7 := by
      simp only [cousinDiamond13Iter, hs1, hs2]
    rw [hi2, cousin_diamond13_cone5_two_step_climb q_c (a - 3) (b + 2) (by omega) (by omega)]
    apply congrArg (· - 7); congr 1
    · apply congrArg (2 ^ ·); omega
    · apply congrArg (3 ^ ·); omega

private theorem not_cone13_of_mod3_ne_2_w16 (x : Nat) (h : x % 3 ≠ 2) : ¬ isDiamond12Cone13 x := by
  intro hc; exact h hc.2.2.1

private theorem not_cone5_of_mod3_ne_2_w16 (x : Nat) (h : x % 3 ≠ 2) : ¬ isDiamond4Cone5 x := by
  intro hc; exact h hc.2.2.1

private theorem ne8_mod9_of_mod3_eq1_w16 (x : Nat) (h : x % 3 = 1) : x % 9 ≠ 8 := by
  omega

private theorem d12_eq_d3_of_not_cones5to13_w16 (z : Nat)
    (h13 : ¬ isDiamond12Cone13 z) (h12 : ¬ isDiamond11Cone12 z) (h11 : ¬ isDiamond10Cone11 z)
    (h10 : ¬ isDiamond9Cone10 z) (h9 : ¬ isDiamond8Cone9 z) (h8 : ¬ isDiamond7Cone8 z)
    (h7 : ¬ isDiamond6Cone7 z) (h6 : ¬ isDiamond5Cone6 z) (h5 : ¬ isDiamond4Cone5 z) :
    cousinDiamond12Step z = cousinDiamond3Step z := by
  rw [d12_eq_d11_of_not_cone13_w16 z h13,
      cousinDiamond11Step_eq_d10_of_not_cone12 z h12,
      cousinDiamond10Step_eq_d9_of_not_cone11 z h11,
      cousinDiamond9Step_eq_d8_of_not_cone10 z h10,
      cousinDiamond8Step_eq_d7_of_not_cone9 z h9,
      cousinDiamond7Step_eq_d6_of_not_cone8 z h8,
      cousinDiamond6Step_eq_d5_of_not_cone7 z h7,
      cousinDiamond5Step_eq_d4_of_not_cone6 z h6,
      cousinDiamond4Step_eq_d3_of_not_cone5 z h5]

private theorem cousin_diamond13_a0_3_drain (b0 : Nat) (hb0 : b0 ≥ 3) :
    cousinDiamond13Step (8 * 3 ^ b0 - 7) = 12 * 3 ^ b0 - 10 ∧
    cousinDiamond13Step (12 * 3 ^ b0 - 10) = 4 * 3 ^ b0 - 4 ∧
    cousinDiamond13Step (4 * 3 ^ b0 - 4) = 4 * 3 ^ (b0 - 1) - 2 ∧
    cousinDiamond13Iter ((b0 - 1) / 2 + 7) (8 * 3 ^ b0 - 7) = 1 := by
  rcases cousin_diamond11_a0_3_drain b0 hb0 with ⟨hd11_1, hd11_2, hd11_3, _⟩
  have hp3_ge27 : 3 ^ b0 ≥ 27 := by simpa using nat_pow_mono_exp_pos 3 3 b0 (by decide) hb0
  have hp3_b1_ge9 : 3 ^ (b0 - 1) ≥ 9 := by simpa using nat_pow_mono_exp_pos 3 2 (b0 - 1) (by decide) (by omega)
  have hs1 : cousinDiamond13Step (8 * 3 ^ b0 - 7) = 12 * 3 ^ b0 - 10 := by
    have ho := pow3_odd_nat_sec8 b0
    rw [d13_eq_d12_of_not_cone14 _ (not_cone14_of_mod8_ne_5 _ (by omega)),
        d12_eq_d11_of_not_cone13_w16 _ (not_cone13_of_mod32_ne_21_w16 _ (by omega))]
    exact hd11_1
  have hs2 : cousinDiamond13Step (12 * 3 ^ b0 - 10) = 4 * 3 ^ b0 - 4 := by
    rw [d13_eq_d12_of_not_cone14 _ (not_cone14_of_even _ (by omega)),
        d12_eq_d11_of_not_cone13_w16 _ (not_cone13_of_mod32_ne_21_w16 _ (by omega))]
    exact hd11_2
  have hs3 : cousinDiamond13Step (4 * 3 ^ b0 - 4) = 4 * 3 ^ (b0 - 1) - 2 := by
    rw [d13_eq_d12_of_not_cone14 _ (not_cone14_of_even _ (by omega)),
        d12_eq_d11_of_not_cone13_w16 _ (not_cone13_of_mod32_ne_21_w16 _ (by omega))]
    exact hd11_3
  refine ⟨hs1, hs2, hs3, ?_⟩
  by_cases hev_b1 : (b0 - 1) % 2 = 0
  · let m := (b0 - 1) / 2
    have hm1 : m ≥ 1 := by dsimp [m]; omega
    have hb1_eq : b0 - 1 = 2 * m := by dsimp [m]; omega
    have hp9_ge9 : 9 ^ m ≥ 9 := by rw [pow9_eq_pow3_double m, ← hb1_eq]; exact hp3_b1_ge9
    have hp9_m8 := pow9_mod8_eq_one_w5 m
    have h4_eq : 4 * 3 ^ (b0 - 1) - 2 = 4 * 9 ^ m - 2 := by rw [hb1_eq, ← pow9_eq_pow3_double m]
    let zr := 2 * 9 ^ m - 1
    let yr := (3 * 9 ^ m - 1) / 2
    have hs4 : cousinDiamond13Step (4 * 9 ^ m - 2) = zr := by
      rw [d13_eq_d3_of_even_w16 _ (by omega)]
      have h9m9 : 9 ^ m % 9 = 0 := by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
      rw [cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) (by omega)]
      dsimp [zr]; omega
    have hsz : cousinDiamond13Step zr = yr := by
      rw [d13_eq_d12_of_not_cone14 zr (not_cone14_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          d12_eq_d3_of_not_cones5to13_w16 zr
            (not_cone13_of_mod32_ne_21_w16 zr (by dsimp [zr]; omega))
            (not_cone12_of_mod8_ne_5 zr (by dsimp [zr]; omega))
            (not_cone11_of_mod8_ne_5 zr (by dsimp [zr]; omega))
            (not_cone10_of_mod8_ne_5 zr (by dsimp [zr]; omega))
            (not_cone9_of_mod8_ne_5 zr (by dsimp [zr]; omega))
            (not_cone8_of_mod8_ne_5 zr (by dsimp [zr]; omega))
            (not_cone7_of_mod8_ne_5 zr (by dsimp [zr]; omega))
            (not_cone6_of_mod16_ne_13 zr (by dsimp [zr]; omega))
            (by rintro ⟨_, h32, _, _⟩; dsimp [zr] at h32; omega)]
      have hc3 : core3 (zr + 1) = 2 := by
        rw [show zr + 1 = 2 * 9 ^ m by dsimp [zr]; omega, core3_mul2 (9 ^ m) (by omega), (pow9_eq_v3Pow_w5 m).2]
      rw [cousinDiamond3Step_of_core3_succ_two_w8 zr (by dsimp [zr]; omega) (by dsimp [zr]; omega) hc3]
      dsimp [zr, yr]; omega
    have hsy : cousinDiamond13Step yr = (9 ^ (m + 1) - 1) / 4 := by
      have hyr_m3 : yr % 3 = 1 := by
        clear hd11_1 hd11_2 hd11_3 hs1 hs2 hs3 h4_eq hs4 hsz
        have hm3 : 9 ^ m % 3 = 0 := by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
        dsimp [yr]; omega
      have hyr_ne2 : yr % 3 ≠ 2 := by rw [hyr_m3]; decide
      have hyr_ne8 : yr % 9 ≠ 8 := ne8_mod9_of_mod3_eq1_w16 yr hyr_m3
      rw [d13_eq_d12_of_not_cone14 yr (not_cone14_of_mod3_ne_2 yr hyr_ne2),
          d12_eq_d3_of_not_cones5to13_w16 yr
            (not_cone13_of_mod3_ne_2_w16 yr hyr_ne2)
            (not_cone12_of_mod3_ne_2 yr hyr_ne2)
            (not_cone11_of_mod3_ne_2 yr hyr_ne2)
            (not_cone10_of_mod3_ne_2 yr hyr_ne2)
            (not_cone9_of_mod3_ne_2 yr hyr_ne2)
            (not_cone8_of_mod3_ne_2 yr hyr_ne2)
            (not_cone7_of_mod9_ne_8 yr hyr_ne8)
            (not_cone6_of_mod9_ne_8 yr hyr_ne8)
            (not_cone5_of_mod3_ne_2_w16 yr hyr_ne2)]
      have hc3_2 : core3 (2 * yr + 1) = 1 := by
        rw [show 2 * yr + 1 = 3 * 9 ^ m by dsimp [yr]; omega, core3_mul3 (9 ^ m) (by omega), (pow9_eq_v3Pow_w5 m).2]
      have hc3_1 : core3 (yr + 1) ≠ 2 := by
        rw [core3_not_div3 (yr + 1) (by clear hd11_1 hd11_2 hd11_3 hs1 hs2 hs3 h4_eq hs4 hsz hc3_2; omega)]
        clear hd11_1 hd11_2 hd11_3 hs1 hs2 hs3 h4_eq hs4 hsz hc3_2; dsimp [yr]; omega
      have hnc4 : ¬ isDiamond3Cone4 yr := by
        rintro ⟨hge169, _, hc2⟩
        by_cases hm_eq1 : m = 1
        · clear hd11_1 hd11_2 hd11_3 hs1 hs2 hs3 h4_eq hs4 hsz hc3_2 hc3_1 hc2
          dsimp [yr] at hge169; rw [hm_eq1] at hge169; omega
        · rcases eq_pow2_of_core2_eq_one (3 * yr + 5)
            (by clear hd11_1 hd11_2 hd11_3 hs1 hs2 hs3 h4_eq hs4 hsz hc3_2 hc3_1; dsimp [yr]; omega) hc2 with
            ⟨M0, hM0⟩
          have h9_eq : 9 ^ (m + 1) + 7 = 2 ^ (M0 + 1) := by
            have h2mul : 2 * (3 * yr + 5) = 9 ^ (m + 1) + 7 := by
              clear hd11_1 hd11_2 hd11_3 hs1 hs2 hs3 h4_eq hs4 hsz hc3_2 hc3_1 hc2 hM0
              rw [Nat.pow_succ 9 m, Nat.mul_comm (9 ^ m) 9]; dsimp [yr]; omega
            rw [← h2mul, hM0, Nat.pow_succ 2 M0, Nat.mul_comm]
          exact pow9_succ_add_seven_ne_pow2 m (M0 + 1)
            (by clear hd11_1 hd11_2 hd11_3 hs1 hs2 hs3 h4_eq hs4 hsz hc3_2 hc3_1 hge169 hc2 hM0 h9_eq; omega) h9_eq
      rw [cousinDiamond3Step_odd_half_w8 yr (by dsimp [yr]; omega) hnc4 hc3_2 hc3_1]
      dsimp [yr]; rw [Nat.pow_succ 9 m]; omega
    change cousinDiamond13Iter (m + 7) (8 * 3 ^ b0 - 7) = 1
    rw [show m + 7 = 4 + 1 + 1 + m + 1 by omega,
        cousinDiamond13Iter_add (4 + 1 + 1 + m) 1,
        cousinDiamond13Iter_add (4 + 1 + 1) m,
        cousinDiamond13Iter_add (4 + 1) 1,
        cousinDiamond13Iter_add 4 1]
    have hi4 : cousinDiamond13Iter 4 (8 * 3 ^ b0 - 7) = zr := by
      simp only [cousinDiamond13Iter, hs1, hs2, hs3, h4_eq, hs4]
    rw [hi4, show cousinDiamond13Iter 1 zr = yr from hsz,
        show cousinDiamond13Iter 1 yr = (9 ^ (m + 1) - 1) / 4 from hsy,
        cousin_diamond13_even9_spine_drain m]
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
    have hs4 : cousinDiamond13Step (12 * 9 ^ m - 2) = ur := by
      rw [d13_eq_d3_of_even_w16 _ (by omega)]
      have h9m9 : 9 ^ m % 9 = 0 := by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
      rw [cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) (by omega)]
      dsimp [ur]; omega
    have hsu : cousinDiamond13Step ur = wr := by
      rw [d13_eq_d12_of_not_cone14 ur (not_cone14_six_mul_pow9_sub1_w16 m),
          d12_eq_d3_of_not_cones5to13_w16 ur
            (cousin_diamond12_outside_cones4to13_descent_and_mod63_nonreentry.2 m)
            (not_cone12_six_mul_pow9_sub1 m)
            (not_cone11_six_mul_pow9_sub1 m)
            (not_cone10_six_mul_pow9_sub1 m)
            (not_cone9_six_mul_pow9_sub1 m)
            (not_cone8_six_mul_pow9_sub1 m)
            (not_cone7_six_mul_pow9_sub1 m)
            (not_cone6_of_mod16_ne_13 ur (by dsimp [ur]; omega))
            (by rintro ⟨_, h32, _, _⟩; dsimp [ur] at h32; omega)]
      have hc3 : core3 (ur + 1) = 2 := by
        rw [show ur + 1 = 2 * (3 * 9 ^ m) by dsimp [ur]; omega,
            core3_mul2 (3 * 9 ^ m) (by omega), core3_mul3 (9 ^ m) (by omega), (pow9_eq_v3Pow_w5 m).2]
      rw [cousinDiamond3Step_of_core3_succ_two_w8 ur (by dsimp [ur]; omega) (by dsimp [ur]; omega) hc3]
      dsimp [ur, wr]; rw [Nat.pow_succ 9 m]; omega
    have hsw : cousinDiamond13Step wr = (9 ^ (m + 1) - 1) / 4 := by
      let q := (9 ^ m - 1) / 8
      have hq_pos : q ≥ 1 := by dsimp [q]; omega
      have hp9_eq : 9 ^ m = 8 * q + 1 := by dsimp [q]; omega
      have hwr_eq : wr = 36 * q + 4 := by dsimp [wr]; rw [Nat.pow_succ 9 m, hp9_eq]; omega
      have hnext_eq : (9 ^ (m + 1) - 1) / 4 = 18 * q + 2 := by rw [Nat.pow_succ 9 m, hp9_eq]; omega
      rw [hwr_eq, hnext_eq, d13_eq_d3_of_even_w16 _ (by omega),
          cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) (by omega)]
      omega
    change cousinDiamond13Iter (m + 7) (8 * 3 ^ b0 - 7) = 1
    rw [show m + 7 = 4 + 1 + 1 + m + 1 by omega,
        cousinDiamond13Iter_add (4 + 1 + 1 + m) 1,
        cousinDiamond13Iter_add (4 + 1 + 1) m,
        cousinDiamond13Iter_add (4 + 1) 1,
        cousinDiamond13Iter_add 4 1]
    have hi4 : cousinDiamond13Iter 4 (8 * 3 ^ b0 - 7) = ur := by
      simp only [cousinDiamond13Iter, hs1, hs2, hs3, hu_eq, hs4]
    rw [hi4, show cousinDiamond13Iter 1 ur = wr from hsu,
        show cousinDiamond13Iter 1 wr = (9 ^ (m + 1) - 1) / 4 from hsw,
        cousin_diamond13_even9_spine_drain m]
    decide

private theorem cousin_diamond13_a0_2_and_4_drain (b0 : Nat) (hb0 : b0 ≥ 3) :
    cousinDiamond13Iter (b0 + 3) (4 * 3 ^ b0 - 7) = 1 ∧
    cousinDiamond13Iter ((b0 - 1) / 2 + 8) (16 * 3 ^ b0 - 7) = 1 := by
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
  · have hs1 : cousinDiamond13Step (4 * 3 ^ b0 - 7) = 6 * 3 ^ b0 - 10 := by
      have hdm := (Nat.div_add_mod (3 ^ b0) 8).symm
      rw [d13_eq_d12_of_not_cone14 _ (not_cone14_of_mod32_ne_21 _ (by rcases h3b0_m8 with h1 | h3 <;> omega)),
          d12_eq_d11_of_not_cone13_w16 _ (not_cone13_of_mod32_ne_21_w16 _ (by rcases h3b0_m8 with h1 | h3 <;> omega)),
          cousinDiamond11Step_eq_d10_of_not_cone12 _ (not_cone12_of_mod32_ne_13 _ (by rcases h3b0_m8 with h1 | h3 <;> omega)),
          cousinDiamond10Step_eq_d9_of_not_cone11 _ (not_cone11_of_mod32_ne_13 _ (by rcases h3b0_m8 with h1 | h3 <;> omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_mod32_ne_13 _ (by rcases h3b0_m8 with h1 | h3 <;> omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_mod32_ne_13 _ (by rcases h3b0_m8 with h1 | h3 <;> omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_mod32_ne_21 _ (by rcases h3b0_m8 with h1 | h3 <;> omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (hnc7_c 4 (by decide)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (hnc6_c 4 (by decide))]
      exact cousin_diamond4_exit_step_general_odd 4 b0 (Or.inl rfl) hb0
    have hs2 : cousinDiamond13Step (6 * 3 ^ b0 - 10) = 2 * 3 ^ b0 - 4 := by
      rw [d13_eq_d3_of_even_w16 _ (by omega)]
      have h18 : 6 * 3 ^ b0 = 18 * 3 ^ (b0 - 1) := by rw [h3b0_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]; omega
    have hs3 : cousinDiamond13Step (2 * 3 ^ b0 - 4) = 2 * 3 ^ (b0 - 1) - 2 := by
      rw [d13_eq_d3_of_even_w16 _ (by omega)]
      have h18 : 2 * 3 ^ b0 = 18 * 3 ^ (b0 - 2) := by rw [h3b0_sp, h3b1_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]; omega
    have hs4 : cousinDiamond13Step (2 * 3 ^ (b0 - 1) - 2) = 3 ^ (b0 - 1) - 1 := by
      rw [d13_eq_d3_of_even_w16 _ (by omega)]
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
        cousinDiamond13Iter_add (4 + (b0 - 2)) 1,
        cousinDiamond13Iter_add 4 (b0 - 2)]
    have hi4 : cousinDiamond13Iter 4 (4 * 3 ^ b0 - 7) = 3 ^ ((b0 - 2) + 1) - 1 := by
      simp only [cousinDiamond13Iter, hs1, hs2, hs3, hs4]; rw [show b0 - 1 = (b0 - 2) + 1 by omega]
    rw [hi4, cousin_diamond13_pow3_sub1_drain (b0 - 2)]; decide
  · rcases cousin_diamond13_a0_3_drain b0 hb0 with ⟨ha3_s1, ha3_s2, ha3_s3, ha3⟩
    have ho := pow3_odd_nat_sec8 b0
    have hs1 : cousinDiamond13Step (16 * 3 ^ b0 - 7) = 24 * 3 ^ b0 - 10 := by
      rw [d13_eq_d12_of_not_cone14 _ (not_cone14_of_mod8_ne_5 _ (by omega)),
          d12_eq_d11_of_not_cone13_w16 _ (not_cone13_of_mod32_ne_21_w16 _ (by omega)),
          cousinDiamond11Step_eq_d10_of_not_cone12 _ (not_cone12_of_mod32_ne_13 _ (by omega)),
          cousinDiamond10Step_eq_d9_of_not_cone11 _ (not_cone11_of_mod32_ne_13 _ (by omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_mod32_ne_13 _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_mod32_ne_13 _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_mod32_ne_21 _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (hnc7_c 16 (by decide)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (hnc6_c 16 (by decide))]
      exact cousin_diamond4_exit_step_general_odd 16 b0 (Or.inr (Or.inr rfl)) hb0
    have hs2 : cousinDiamond13Step (24 * 3 ^ b0 - 10) = 8 * 3 ^ b0 - 4 := by
      rw [d13_eq_d3_of_even_w16 _ (by omega)]
      have h18 : 24 * 3 ^ b0 = 18 * (4 * 3 ^ (b0 - 1)) := by rw [h3b0_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]; omega
    have hs3 : cousinDiamond13Step (8 * 3 ^ b0 - 4) = 8 * 3 ^ (b0 - 1) - 2 := by
      rw [d13_eq_d3_of_even_w16 _ (by omega)]
      have h18 : 8 * 3 ^ b0 = 18 * (4 * 3 ^ (b0 - 2)) := by rw [h3b0_sp, h3b1_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]; omega
    have hs4 : cousinDiamond13Step (8 * 3 ^ (b0 - 1) - 2) = 4 * 3 ^ (b0 - 1) - 2 := by
      rw [d13_eq_d3_of_even_w16 _ (by omega)]
      have h18 : 8 * 3 ^ (b0 - 1) = 18 * (4 * 3 ^ (b0 - 3)) := by
        calc 8 * 3 ^ (b0 - 1) = 8 * 3 ^ (2 + (b0 - 3)) := by congr 2; omega
          _ = 8 * (3 ^ 2 * 3 ^ (b0 - 3)) := by rw [Nat.pow_add]
          _ = 18 * (4 * 3 ^ (b0 - 3)) := by omega
      have hp3_b3 := pow3_pos_nat (b0 - 3)
      rw [cousinDiamond3Step_even_mod8_eq6_w8 _ (by omega) (by omega) (by omega) ⟨by omega, by omega⟩]; omega
    rw [show (b0 - 1) / 2 + 7 = 3 + ((b0 - 1) / 2 + 4) by omega,
        cousinDiamond13Iter_add 3 ((b0 - 1) / 2 + 4)] at ha3
    have hi3 : cousinDiamond13Iter 3 (8 * 3 ^ b0 - 7) = 4 * 3 ^ (b0 - 1) - 2 := by
      simp only [cousinDiamond13Iter, ha3_s1, ha3_s2, ha3_s3]
    rw [hi3] at ha3
    rw [show (b0 - 1) / 2 + 8 = 4 + ((b0 - 1) / 2 + 4) by omega,
        cousinDiamond13Iter_add 4 ((b0 - 1) / 2 + 4)]
    have hi4 : cousinDiamond13Iter 4 (16 * 3 ^ b0 - 7) = 4 * 3 ^ (b0 - 1) - 2 := by
      simp only [cousinDiamond13Iter, hs1, hs2, hs3, hs4]
    rw [hi4]; exact ha3

private theorem cousin_diamond13_cone4_return_aux (x : Nat) (hc4 : isDiamond3Cone4 x) :
    ∃ k : Nat, k ≤ cousinDiamond2Phi x ∧ cousinDiamond13Iter k x = 1 := by
  rcases cousin_diamond3_cone4_reaches_one_exact x hc4 with ⟨r, hr_ge3, hE, _, hphi_ge⟩
  refine ⟨3 * r + 4, hphi_ge, ?_⟩
  have hx_odd : x % 2 = 1 := by have := hc4.2.1; omega
  have hs1 : cousinDiamond13Step x = 2 ^ (2 * r + 1) - 1 := by
    rw [d13_eq_d12_of_not_cone14 x (not_cone14_of_mod8_ne_5 x (by have := hc4.2.1; omega)),
        d12_eq_d11_of_not_cone13_w16 x (not_cone13_of_mod32_ne_21_w16 x (by have := hc4.2.1; omega)),
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
  have hglide : cousinDiamond13Iter (2 * r) (2 ^ (2 * r + 1) - 1) = zr := by
    have hf := cousin_diamond13_mersenne_scaled (2 * r) (2 * r + 1) 1 (by omega) (by decide)
    simp only [Nat.mul_one, show 2 * r + 1 - 2 * r = 1 by omega, Nat.pow_one] at hf
    rw [hf, ← pow9_eq_pow3_double r, Nat.mul_comm]
  have hp9_ge729 : 9 ^ r ≥ 729 := by simpa using nat_pow_mono_exp_pos 9 3 r (by decide) hr_ge3
  have hp9_m8 := pow9_mod8_eq_one_w5 r
  have hsz : cousinDiamond13Step zr = yr := by
    rw [d13_eq_d12_of_not_cone14 zr (not_cone14_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
        d12_eq_d3_of_not_cones5to13_w16 zr
          (not_cone13_of_mod32_ne_21_w16 zr (by dsimp [zr]; omega))
          (not_cone12_of_mod8_ne_5 zr (by dsimp [zr]; omega))
          (not_cone11_of_mod8_ne_5 zr (by dsimp [zr]; omega))
          (not_cone10_of_mod8_ne_5 zr (by dsimp [zr]; omega))
          (not_cone9_of_mod8_ne_5 zr (by dsimp [zr]; omega))
          (not_cone8_of_mod8_ne_5 zr (by dsimp [zr]; omega))
          (not_cone7_of_mod8_ne_5 zr (by dsimp [zr]; omega))
          (not_cone6_of_mod16_ne_13 zr (by dsimp [zr]; omega))
          (by rintro ⟨_, h32, _, _⟩; dsimp [zr] at h32; omega)]
    have hc3 : core3 (zr + 1) = 2 := by
      rw [show zr + 1 = 2 * 9 ^ r by dsimp [zr]; omega, core3_mul2 (9 ^ r) (by omega), (pow9_eq_v3Pow_w5 r).2]
    rw [cousinDiamond3Step_of_core3_succ_two_w8 zr (by dsimp [zr]; omega) (by dsimp [zr]; omega) hc3]
    dsimp [zr, yr]; omega
  have hsy : cousinDiamond13Step yr = (9 ^ (r + 1) - 1) / 4 := by
    have hyr_m3 : yr % 3 = 1 := by
      clear hs1 hglide hsz
      have hm3 : 9 ^ r % 3 = 0 := by rw [show r = (r - 1) + 1 by omega, Nat.pow_succ]; omega
      dsimp [yr]; omega
    have hyr_ne2 : yr % 3 ≠ 2 := by rw [hyr_m3]; decide
    have hyr_ne8 : yr % 9 ≠ 8 := ne8_mod9_of_mod3_eq1_w16 yr hyr_m3
    rw [d13_eq_d12_of_not_cone14 yr (not_cone14_of_mod3_ne_2 yr hyr_ne2),
        d12_eq_d3_of_not_cones5to13_w16 yr
          (not_cone13_of_mod3_ne_2_w16 yr hyr_ne2)
          (not_cone12_of_mod3_ne_2 yr hyr_ne2)
          (not_cone11_of_mod3_ne_2 yr hyr_ne2)
          (not_cone10_of_mod3_ne_2 yr hyr_ne2)
          (not_cone9_of_mod3_ne_2 yr hyr_ne2)
          (not_cone8_of_mod3_ne_2 yr hyr_ne2)
          (not_cone7_of_mod9_ne_8 yr hyr_ne8)
          (not_cone6_of_mod9_ne_8 yr hyr_ne8)
          (not_cone5_of_mod3_ne_2_w16 yr hyr_ne2)]
    have hc3_2 : core3 (2 * yr + 1) = 1 := by
      rw [show 2 * yr + 1 = 3 * 9 ^ r by clear hs1 hglide hsz; dsimp [yr]; omega,
          core3_mul3 (9 ^ r) (by clear hs1 hglide hsz; omega), (pow9_eq_v3Pow_w5 r).2]
    have hc3_1 : core3 (yr + 1) ≠ 2 := by
      rw [core3_not_div3 (yr + 1) (by clear hs1 hglide hsz hc3_2; omega)]
      clear hs1 hglide hsz hc3_2; dsimp [yr]; omega
    have hnc4 : ¬ isDiamond3Cone4 yr := by
      rintro ⟨_, _, hc2⟩
      rcases eq_pow2_of_core2_eq_one (3 * yr + 5) (by clear hs1 hglide hsz hc3_2 hc3_1; dsimp [yr]; omega) hc2 with ⟨M0, hM0⟩
      have h9_eq : 9 ^ (r + 1) + 7 = 2 ^ (M0 + 1) := by
        have h2mul : 2 * (3 * yr + 5) = 9 ^ (r + 1) + 7 := by
          clear hs1 hglide hsz hc3_2 hc3_1 hc2 hM0
          rw [Nat.pow_succ 9 r, Nat.mul_comm (9 ^ r) 9]; dsimp [yr]; omega
        rw [← h2mul, hM0, Nat.pow_succ 2 M0, Nat.mul_comm]
      exact pow9_succ_add_seven_ne_pow2 r (M0 + 1) (by clear hs1 hglide hsz hc3_2 hc3_1 hc2 hM0 h9_eq; omega) h9_eq
    rw [cousinDiamond3Step_odd_half_w8 yr (by clear hs1 hglide hsz hc3_2 hc3_1 hnc4; dsimp [yr]; omega) hnc4 hc3_2 hc3_1]
    clear hs1 hglide hsz hc3_2 hc3_1 hnc4
    dsimp [yr]; rw [Nat.pow_succ 9 r]; omega
  rw [show 3 * r + 4 = 1 + 2 * r + 1 + 1 + r + 1 by omega,
      cousinDiamond13Iter_add (1 + 2 * r + 1 + 1 + r) 1,
      cousinDiamond13Iter_add (1 + 2 * r + 1 + 1) r,
      cousinDiamond13Iter_add (1 + 2 * r + 1) 1,
      cousinDiamond13Iter_add (1 + 2 * r) 1,
      cousinDiamond13Iter_add 1 (2 * r)]
  rw [show cousinDiamond13Iter 1 x = 2 ^ (2 * r + 1) - 1 from hs1, hglide,
      show cousinDiamond13Iter 1 zr = yr from hsz,
      show cousinDiamond13Iter 1 yr = (9 ^ (r + 1) - 1) / 4 from hsy,
      cousin_diamond13_even9_spine_drain r]
  decide

private theorem cousin_diamond13_cone5_return_aux (x : Nat) (hc5 : isDiamond4Cone5 x) :
    ∃ (a b k : Nat),
      a ≥ 5 ∧ b ≥ 1 ∧ x + 7 = 2 ^ a * 3 ^ b ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond13Iter k x = 1 := by
  rcases cousin_diamond12_cones4to13_exact_return.2.1 x hc5 with ⟨a, b, _, ha5, hb1, hmul, _, _, _⟩
  have hx_eq : x = 2 ^ a * 3 ^ b - 7 := by omega
  let q_c := (a - 2) / 3
  let a0 := a - 3 * q_c
  let b0 := b + 2 * q_c
  have hb0_ge3 : b0 ≥ 3 := by dsimp [b0, q_c]; omega
  have ha0_234 : a0 = 2 ∨ a0 = 3 ∨ a0 = 4 := by dsimp [a0, q_c]; omega
  have hclimb := cousin_diamond13_cone5_two_step_climb q_c a b (by dsimp [q_c]; omega) hb1
  rw [← hx_eq] at hclimb
  change cousinDiamond13Iter (2 * q_c) x = 2 ^ a0 * 3 ^ b0 - 7 at hclimb
  have hbound_x : ∀ ex : Nat, ex ≤ b0 + 8 -> 2 * q_c + ex ≤ x := by
    intro ex hex
    have hprod := Nat.mul_le_mul (pow2_ge_six_mul_ge5 a ha5) (pow3_ge_add_two_ge1 b hb1)
    rw [hmul.symm] at hprod
    have hab : 6 * b ≤ 6 * a * b := by
      rw [Nat.mul_comm (6 * a) b, ← Nat.mul_assoc, Nat.mul_comm b 6]
      simpa using Nat.mul_le_mul_left (6 * b) (by omega : 1 ≤ a)
    rw [show (6 * a) * (b + 2) = 6 * a * b + 12 * a by rw [Nat.mul_add]; omega] at hprod
    dsimp [q_c, b0] at hex ⊢; omega
  have hd_3 := (cousin_diamond13_a0_3_drain b0 hb0_ge3).2.2.2
  rcases cousin_diamond13_a0_2_and_4_drain b0 hb0_ge3 with ⟨hd_2, hd_4⟩
  rcases ha0_234 with ha2 | ha3 | ha4
  · have hkx := hbound_x (b0 + 3) (by omega)
    refine ⟨a, b, 2 * q_c + (b0 + 3), ha5, hb1, hmul, hkx,
      Nat.le_trans (by omega : 2 * q_c + (b0 + 3) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond13Iter_add (2 * q_c) (b0 + 3) x, hclimb, ha2]; exact hd_2
  · have hkx := hbound_x ((b0 - 1) / 2 + 7) (by omega)
    refine ⟨a, b, 2 * q_c + ((b0 - 1) / 2 + 7), ha5, hb1, hmul, hkx,
      Nat.le_trans (by omega : 2 * q_c + ((b0 - 1) / 2 + 7) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond13Iter_add (2 * q_c) ((b0 - 1) / 2 + 7) x, hclimb, ha3]; exact hd_3
  · have hkx := hbound_x ((b0 - 1) / 2 + 8) (by omega)
    refine ⟨a, b, 2 * q_c + ((b0 - 1) / 2 + 8), ha5, hb1, hmul, hkx,
      Nat.le_trans (by omega : 2 * q_c + ((b0 - 1) / 2 + 8) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond13Iter_add (2 * q_c) ((b0 - 1) / 2 + 8) x, hclimb, ha4]; exact hd_4

private theorem lift_cone_step_to_d13 (x y D : Nat) (hD8 : D ≥ 8) (hx_ge : x ≥ 2000)
    (hnc14 : ¬ isDiamond13Cone14 x)
    (hd12 : cousinDiamond12Step x = y)
    (hy_div : y = (3 * x + 1) / D)
    (hret_y : ∃ ky : Nat, ky ≤ y ∧ cousinDiamond13Iter ky y = 1) :
    ∃ k : Nat, k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond13Step x = y ∧ cousinDiamond13Iter k x = 1 := by
  rcases hret_y with ⟨ky, hky_y, hky_1⟩
  have hstep : cousinDiamond13Step x = y := (d13_eq_d12_of_not_cone14 x hnc14).trans hd12
  have hy_lt : y + 1 ≤ x := by
    have hdiv : y * D ≤ 3 * x + 1 := by rw [hy_div]; exact Nat.div_mul_le_self (3 * x + 1) D
    have h8 : y * 8 ≤ y * D := Nat.mul_le_mul_left y hD8
    omega
  refine ⟨1 + ky, by omega, Nat.le_trans (by omega : 1 + ky ≤ x + 1) (cousinDiamond2Phi_ge_succ x), hstep, ?_⟩
  rw [cousinDiamond13Iter_add 1 ky x, show cousinDiamond13Iter 1 x = y from hstep]; exact hky_1

/--
  Theorem W16.3e (`cousin_diamond13_cones4to14_exact_return`, `zero custom axioms`):
  Exact 11-Tier `ω^11` Multi-Block Return Across Cones 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, AND 14
  of `T_diamond13` (`Branch P5.15`, `W16_H3`).
-/
theorem cousin_diamond13_cones4to14_exact_return :
    (∀ x : Nat, isDiamond3Cone4 x ->
      ∃ k : Nat, k ≤ cousinDiamond2Phi x ∧ cousinDiamond13Iter k x = 1) ∧
    (∀ x : Nat, isDiamond4Cone5 x ->
      ∃ (a b k : Nat),
        a ≥ 5 ∧ b ≥ 1 ∧ x + 7 = 2 ^ a * 3 ^ b ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond13Iter k x = 1) ∧
    (∀ x : Nat, isDiamond5Cone6 x ->
      ∃ (e f k : Nat),
        e ≥ 8 ∧ f ≥ 2 ∧ x + 19 = 2 ^ e * 3 ^ f ∧
        cousinDiamond13Step x = 2 ^ (e - 3) * 3 ^ (f + 1) - 7 ∧
        isDiamond4Cone5 (cousinDiamond13Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond13Iter k x = 1) ∧
    (∀ x : Nat, isDiamond6Cone7 x ->
      ∃ (g h k : Nat),
        g ≥ 15 ∧ h ≥ 2 ∧ x + 811 = 2 ^ g * 3 ^ h ∧
        cousinDiamond13Step x = 2 ^ (g - 7) * 3 ^ (h + 1) - 19 ∧
        isDiamond5Cone6 (cousinDiamond13Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond13Iter k x = 1) ∧
    (∀ x : Nat, isDiamond7Cone8 x ->
      ∃ (u v k : Nat),
        u ≥ 22 ∧ v ≥ 1 ∧ x + 34603 = 2 ^ u * 3 ^ v ∧
        cousinDiamond13Step x = 2 ^ (u - 7) * 3 ^ (v + 1) - 811 ∧
        isDiamond6Cone7 (cousinDiamond13Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond13Iter k x = 1) ∧
    (∀ x : Nat, isDiamond8Cone9 x ->
      ∃ (w z k : Nat),
        w ≥ 25 ∧ z ≥ 1 ∧ x + 92275 = 2 ^ w * 3 ^ z ∧
        cousinDiamond13Step x = 2 ^ (w - 3) * 3 ^ (z + 1) - 34603 ∧
        isDiamond7Cone8 (cousinDiamond13Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond13Iter k x = 1) ∧
    (∀ x : Nat, isDiamond9Cone10 x ->
      ∃ (p q k : Nat),
        p ≥ 28 ∧ q ≥ 1 ∧ x + 246067 = 2 ^ p * 3 ^ q ∧
        cousinDiamond13Step x = 2 ^ (p - 3) * 3 ^ (q + 1) - 92275 ∧
        isDiamond8Cone9 (cousinDiamond13Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond13Iter k x = 1) ∧
    (∀ x : Nat, isDiamond10Cone11 x ->
      ∃ (r s k : Nat),
        r ≥ 31 ∧ s ≥ 1 ∧ x + 656179 = 2 ^ r * 3 ^ s ∧
        cousinDiamond13Step x = 2 ^ (r - 3) * 3 ^ (s + 1) - 246067 ∧
        isDiamond9Cone10 (cousinDiamond13Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond13Iter k x = 1) ∧
    (∀ x : Nat, isDiamond11Cone12 x ->
      ∃ (m n k : Nat),
        m ≥ 34 ∧ n ≥ 1 ∧ x + 1749811 = 2 ^ m * 3 ^ n ∧
        cousinDiamond13Step x = 2 ^ (m - 3) * 3 ^ (n + 1) - 656179 ∧
        isDiamond10Cone11 (cousinDiamond13Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond13Iter k x = 1) ∧
    (∀ x : Nat, isDiamond12Cone13 x ->
      ∃ (a b k : Nat),
        a ≥ 39 ∧ b ≥ 1 ∧ x + 18664651 = 2 ^ a * 3 ^ b ∧
        cousinDiamond13Step x = 2 ^ (a - 5) * 3 ^ (b + 1) - 1749811 ∧
        isDiamond11Cone12 (cousinDiamond13Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond13Iter k x = 1) ∧
    (∀ x : Nat, isDiamond13Cone14 x ->
      ∃ (k_e m_e k : Nat),
        k_e ≥ 46 ∧ m_e ≥ 1 ∧ x + 796358443 = 2 ^ k_e * 3 ^ m_e ∧
        cousinDiamond13Step x = 2 ^ (k_e - 7) * 3 ^ (m_e + 1) - 18664651 ∧
        isDiamond12Cone13 (cousinDiamond13Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond13Iter k x = 1) := by
  have hw15 := cousin_diamond12_cones4to13_exact_return
  have hc6_ret : ∀ x : Nat, isDiamond5Cone6 x ->
      ∃ (e f k : Nat), e ≥ 8 ∧ f ≥ 2 ∧ x + 19 = 2 ^ e * 3 ^ f ∧
        cousinDiamond13Step x = 2 ^ (e - 3) * 3 ^ (f + 1) - 7 ∧
        isDiamond4Cone5 (cousinDiamond13Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond13Iter k x = 1 := by
    intro x hc6
    rcases hw15.2.2.1 x hc6 with ⟨e, f, _, he8, hf2, hmul, hd12, hc5_y, _, _, _⟩
    rw [hd12] at hc5_y
    rcases cousin_diamond13_cone5_return_aux _ hc5_y with ⟨_, _, ky, _, _, _, hky_y, _, hky_1⟩
    have hnc14 : ¬ isDiamond13Cone14 x := not_cone14_of_mod32_ne_21 x (by
      have h := congrArg (· % 32) hc6.2.1; rw [Nat.mod_mod_of_dvd x (by decide : 32 ∣ 256)] at h; omega)
    have hy_div : 2 ^ (e - 3) * 3 ^ (f + 1) - 7 = (3 * x + 1) / 8 := by
      have hp2 : 2 ^ e = 8 * 2 ^ (e - 3) := by
        conv => lhs; rw [show e = 3 + (e - 3) by omega, Nat.pow_add]
      have h3x : 3 * (x + 19) = 8 * (2 ^ (e - 3) * 3 ^ (f + 1)) := by
        rw [hmul, hp2, Nat.pow_succ 3 f]; ac_rfl
      have hge := hc6.1; omega
    rcases lift_cone_step_to_d13 x _ 8 (by decide) (by have := hc6.1; omega) hnc14 hd12 hy_div ⟨ky, hky_y, hky_1⟩ with
      ⟨k, hkx, hkphi, hst, hk1⟩
    exact ⟨e, f, k, he8, hf2, hmul, hst, by rw [hst]; exact hc5_y, hkx, hkphi, hk1⟩
  have hc7_ret : ∀ x : Nat, isDiamond6Cone7 x ->
      ∃ (g h k : Nat), g ≥ 15 ∧ h ≥ 2 ∧ x + 811 = 2 ^ g * 3 ^ h ∧
        cousinDiamond13Step x = 2 ^ (g - 7) * 3 ^ (h + 1) - 19 ∧
        isDiamond5Cone6 (cousinDiamond13Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond13Iter k x = 1 := by
    intro x hc7
    rcases hw15.2.2.2.1 x hc7 with ⟨g, h, _, hg15, hh2, hmul, hd12, hc6_y, _, _, _⟩
    rw [hd12] at hc6_y
    rcases hc6_ret _ hc6_y with ⟨_, _, ky, _, _, _, _, _, hky_y, _, hky_1⟩
    have hnc14 : ¬ isDiamond13Cone14 x := not_cone14_of_mod2048_ne_213 x (by
      have h2k := congrArg (· % 2048) hc7.2.1
      rw [Nat.mod_mod_of_dvd x (by decide : 2048 ∣ 32768),
          show 31957 % 2048 = 1237 by decide] at h2k
      omega)
    have hy_div : 2 ^ (g - 7) * 3 ^ (h + 1) - 19 = (3 * x + 1) / 128 := by
      have hp2 : 2 ^ g = 128 * 2 ^ (g - 7) := by
        conv => lhs; rw [show g = 7 + (g - 7) by omega, Nat.pow_add]
      have h3x : 3 * (x + 811) = 128 * (2 ^ (g - 7) * 3 ^ (h + 1)) := by
        rw [hmul, hp2, Nat.pow_succ 3 h]; ac_rfl
      have hge := hc7.1; omega
    rcases lift_cone_step_to_d13 x _ 128 (by decide) (by have := hc7.1; omega) hnc14 hd12 hy_div ⟨ky, hky_y, hky_1⟩ with
      ⟨k, hkx, hkphi, hst, hk1⟩
    exact ⟨g, h, k, hg15, hh2, hmul, hst, by rw [hst]; exact hc6_y, hkx, hkphi, hk1⟩
  have hc8_ret : ∀ x : Nat, isDiamond7Cone8 x ->
      ∃ (u v k : Nat), u ≥ 22 ∧ v ≥ 1 ∧ x + 34603 = 2 ^ u * 3 ^ v ∧
        cousinDiamond13Step x = 2 ^ (u - 7) * 3 ^ (v + 1) - 811 ∧
        isDiamond6Cone7 (cousinDiamond13Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond13Iter k x = 1 := by
    intro x hc8
    rcases hw15.2.2.2.2.1 x hc8 with ⟨u, v, _, hu22, hv1, hmul, hd12, hc7_y, _, _, _⟩
    rw [hd12] at hc7_y
    rcases hc7_ret _ hc7_y with ⟨_, _, ky, _, _, _, _, _, hky_y, _, hky_1⟩
    have hnc14 : ¬ isDiamond13Cone14 x := not_cone14_of_mod8192_ne_2261 x (by
      have h8k := congrArg (· % 8192) hc8.2.1
      rw [Nat.mod_mod_of_dvd x (by decide : 8192 ∣ 4194304),
          show 4159701 % 8192 = 6357 by decide] at h8k
      omega)
    have hy_div : 2 ^ (u - 7) * 3 ^ (v + 1) - 811 = (3 * x + 1) / 128 := by
      have hp2 : 2 ^ u = 128 * 2 ^ (u - 7) := by
        conv => lhs; rw [show u = 7 + (u - 7) by omega, Nat.pow_add]
      have h3x : 3 * (x + 34603) = 128 * (2 ^ (u - 7) * 3 ^ (v + 1)) := by
        rw [hmul, hp2, Nat.pow_succ 3 v]; ac_rfl
      have hge := hc8.1; omega
    rcases lift_cone_step_to_d13 x _ 128 (by decide) (by have := hc8.1; omega) hnc14 hd12 hy_div ⟨ky, hky_y, hky_1⟩ with
      ⟨k, hkx, hkphi, hst, hk1⟩
    exact ⟨u, v, k, hu22, hv1, hmul, hst, by rw [hst]; exact hc7_y, hkx, hkphi, hk1⟩
  have hc9_ret : ∀ x : Nat, isDiamond8Cone9 x ->
      ∃ (w z k : Nat), w ≥ 25 ∧ z ≥ 1 ∧ x + 92275 = 2 ^ w * 3 ^ z ∧
        cousinDiamond13Step x = 2 ^ (w - 3) * 3 ^ (z + 1) - 34603 ∧
        isDiamond7Cone8 (cousinDiamond13Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond13Iter k x = 1 := by
    intro x hc9
    rcases hw15.2.2.2.2.2.1 x hc9 with ⟨w, z, _, hw25, hz1, hmul, hd12, hc8_y, _, _, _⟩
    rw [hd12] at hc8_y
    rcases hc8_ret _ hc8_y with ⟨_, _, ky, _, _, _, _, _, hky_y, _, hky_1⟩
    have hnc14 : ¬ isDiamond13Cone14 x := not_cone14_of_mod32_ne_21 x (by
      have h := congrArg (· % 32) hc9.2.1
      rw [Nat.mod_mod_of_dvd x (by decide : 32 ∣ 33554432),
          show 33462157 % 32 = 13 by decide] at h; omega)
    have hy_div : 2 ^ (w - 3) * 3 ^ (z + 1) - 34603 = (3 * x + 1) / 8 := by
      have hp2 : 2 ^ w = 8 * 2 ^ (w - 3) := by
        conv => lhs; rw [show w = 3 + (w - 3) by omega, Nat.pow_add]
      have h3x : 3 * (x + 92275) = 8 * (2 ^ (w - 3) * 3 ^ (z + 1)) := by
        rw [hmul, hp2, Nat.pow_succ 3 z]; ac_rfl
      have hge := hc9.1; omega
    rcases lift_cone_step_to_d13 x _ 8 (by decide) (by have := hc9.1; omega) hnc14 hd12 hy_div ⟨ky, hky_y, hky_1⟩ with
      ⟨k, hkx, hkphi, hst, hk1⟩
    exact ⟨w, z, k, hw25, hz1, hmul, hst, by rw [hst]; exact hc8_y, hkx, hkphi, hk1⟩
  have hc10_ret : ∀ x : Nat, isDiamond9Cone10 x ->
      ∃ (p q k : Nat), p ≥ 28 ∧ q ≥ 1 ∧ x + 246067 = 2 ^ p * 3 ^ q ∧
        cousinDiamond13Step x = 2 ^ (p - 3) * 3 ^ (q + 1) - 92275 ∧
        isDiamond8Cone9 (cousinDiamond13Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond13Iter k x = 1 := by
    intro x hc10
    rcases hw15.2.2.2.2.2.2.1 x hc10 with ⟨p, q, _, hp28, hq1, hmul, hd12, hc9_y, _, _, _⟩
    rw [hd12] at hc9_y
    rcases hc9_ret _ hc9_y with ⟨_, _, ky, _, _, _, _, _, hky_y, _, hky_1⟩
    have hnc14 : ¬ isDiamond13Cone14 x := not_cone14_of_mod32_ne_21 x (by
      have h := congrArg (· % 32) hc10.2.1
      rw [Nat.mod_mod_of_dvd x (by decide : 32 ∣ 268435456),
          show 268189389 % 32 = 13 by decide] at h; omega)
    have hy_div : 2 ^ (p - 3) * 3 ^ (q + 1) - 92275 = (3 * x + 1) / 8 := by
      have hp2 : 2 ^ p = 8 * 2 ^ (p - 3) := by
        conv => lhs; rw [show p = 3 + (p - 3) by omega, Nat.pow_add]
      have h3x : 3 * (x + 246067) = 8 * (2 ^ (p - 3) * 3 ^ (q + 1)) := by
        rw [hmul, hp2, Nat.pow_succ 3 q]; ac_rfl
      have hge := hc10.1; omega
    rcases lift_cone_step_to_d13 x _ 8 (by decide) (by have := hc10.1; omega) hnc14 hd12 hy_div ⟨ky, hky_y, hky_1⟩ with
      ⟨k, hkx, hkphi, hst, hk1⟩
    exact ⟨p, q, k, hp28, hq1, hmul, hst, by rw [hst]; exact hc9_y, hkx, hkphi, hk1⟩
  have hc11_ret : ∀ x : Nat, isDiamond10Cone11 x ->
      ∃ (r s k : Nat), r ≥ 31 ∧ s ≥ 1 ∧ x + 656179 = 2 ^ r * 3 ^ s ∧
        cousinDiamond13Step x = 2 ^ (r - 3) * 3 ^ (s + 1) - 246067 ∧
        isDiamond9Cone10 (cousinDiamond13Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond13Iter k x = 1 := by
    intro x hc11
    rcases hw15.2.2.2.2.2.2.2.1 x hc11 with ⟨r, s, _, hr31, hs1, hmul, hd12, hc10_y, _, _, _⟩
    rw [hd12] at hc10_y
    rcases hc10_ret _ hc10_y with ⟨_, _, ky, _, _, _, _, _, hky_y, _, hky_1⟩
    have hnc14 : ¬ isDiamond13Cone14 x := not_cone14_of_mod32_ne_21 x (by rw [mod32_of_cone11 x hc11]; decide)
    have hy_div : 2 ^ (r - 3) * 3 ^ (s + 1) - 246067 = (3 * x + 1) / 8 := by
      have hp2 : 2 ^ r = 8 * 2 ^ (r - 3) := by
        conv => lhs; rw [show r = 3 + (r - 3) by omega, Nat.pow_add]
      have h3x : 3 * (x + 656179) = 8 * (2 ^ (r - 3) * 3 ^ (s + 1)) := by
        rw [hmul, hp2, Nat.pow_succ 3 s]; ac_rfl
      have hge := hc11.1; omega
    rcases lift_cone_step_to_d13 x _ 8 (by decide) (by have := hc11.1; omega) hnc14 hd12 hy_div ⟨ky, hky_y, hky_1⟩ with
      ⟨k, hkx, hkphi, hst, hk1⟩
    exact ⟨r, s, k, hr31, hs1, hmul, hst, by rw [hst]; exact hc10_y, hkx, hkphi, hk1⟩
  have hc12_ret : ∀ x : Nat, isDiamond11Cone12 x ->
      ∃ (m n k : Nat), m ≥ 34 ∧ n ≥ 1 ∧ x + 1749811 = 2 ^ m * 3 ^ n ∧
        cousinDiamond13Step x = 2 ^ (m - 3) * 3 ^ (n + 1) - 656179 ∧
        isDiamond10Cone11 (cousinDiamond13Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond13Iter k x = 1 := by
    intro x hc12
    rcases hw15.2.2.2.2.2.2.2.2.1 x hc12 with ⟨m, n, _, hm34, hn1, hmul, hd12, hc11_y, _, _, _⟩
    rw [hd12] at hc11_y
    rcases hc11_ret _ hc11_y with ⟨_, _, ky, _, _, _, _, _, hky_y, _, hky_1⟩
    have hnc14 : ¬ isDiamond13Cone14 x := not_cone14_of_mod32_ne_21 x (by rw [mod32_of_cone12 x hc12]; decide)
    have hy_div : 2 ^ (m - 3) * 3 ^ (n + 1) - 656179 = (3 * x + 1) / 8 := by
      have hp2 : 2 ^ m = 8 * 2 ^ (m - 3) := by
        conv => lhs; rw [show m = 3 + (m - 3) by omega, Nat.pow_add]
      have h3x : 3 * (x + 1749811) = 8 * (2 ^ (m - 3) * 3 ^ (n + 1)) := by
        rw [hmul, hp2, Nat.pow_succ 3 n]; ac_rfl
      have hge := hc12.1; omega
    rcases lift_cone_step_to_d13 x _ 8 (by decide) (by have := hc12.1; omega) hnc14 hd12 hy_div ⟨ky, hky_y, hky_1⟩ with
      ⟨k, hkx, hkphi, hst, hk1⟩
    exact ⟨m, n, k, hm34, hn1, hmul, hst, by rw [hst]; exact hc11_y, hkx, hkphi, hk1⟩
  have hc13_ret : ∀ x : Nat, isDiamond12Cone13 x ->
      ∃ (a b k : Nat), a ≥ 39 ∧ b ≥ 1 ∧ x + 18664651 = 2 ^ a * 3 ^ b ∧
        cousinDiamond13Step x = 2 ^ (a - 5) * 3 ^ (b + 1) - 1749811 ∧
        isDiamond11Cone12 (cousinDiamond13Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond13Iter k x = 1 := by
    intro x hc13
    rcases hw15.2.2.2.2.2.2.2.2.2 x hc13 with ⟨a, b, _, ha39, hb1, hmul, hd12, hc12_y, _, _, _⟩
    rw [hd12] at hc12_y
    rcases hc12_ret _ hc12_y with ⟨_, _, ky, _, _, _, _, _, hky_y, _, hky_1⟩
    have hnc14 : ¬ isDiamond13Cone14 x := not_cone14_of_mod64_ne_21 x (by
      have h := congrArg (· % 64) hc13.2.1
      rw [Nat.mod_mod_of_dvd x (by decide : 64 ∣ 549755813888),
          show 549737149237 % 64 = 53 by decide] at h; omega)
    have hy_div : 2 ^ (a - 5) * 3 ^ (b + 1) - 1749811 = (3 * x + 1) / 32 := by
      have hp2 : 2 ^ a = 32 * 2 ^ (a - 5) := by
        conv => lhs; rw [show a = 5 + (a - 5) by omega, Nat.pow_add]
      have h3x : 3 * (x + 18664651) = 32 * (2 ^ (a - 5) * 3 ^ (b + 1)) := by
        rw [hmul, hp2, Nat.pow_succ 3 b]; ac_rfl
      have hge := hc13.1; omega
    rcases lift_cone_step_to_d13 x _ 32 (by decide) (by have := hc13.1; omega) hnc14 hd12 hy_div ⟨ky, hky_y, hky_1⟩ with
      ⟨k, hkx, hkphi, hst, hk1⟩
    exact ⟨a, b, k, ha39, hb1, hmul, hst, by rw [hst]; exact hc12_y, hkx, hkphi, hk1⟩
  refine ⟨cousin_diamond13_cone4_return_aux, cousin_diamond13_cone5_return_aux,
          hc6_ret, hc7_ret, hc8_ret, hc9_ret, hc10_ret, hc11_ret, hc12_ret, hc13_ret, ?_⟩
  intro x hc14
  have hraw_step : cousinDiamond13Step x = (3 * x + 1) / 128 := by
    unfold cousinDiamond13Step; simp only [hc14, ite_true]
  rcases hc14 with ⟨hx_ge, hx46, hx3, hg1⟩
  have hdvd46 : 70368744177664 ∣ (x + 796358443) :=
    Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, hx46])
  clear hx46
  rcases (⟨796358443 + x, rfl⟩ : ∃ N : Nat, N = 796358443 + x) with ⟨N, hN_def⟩
  rw [← hN_def] at hg1
  have hN_pos : N > 0 := by clear hraw_step hdvd46 hx3 hg1; omega
  rcases decomp_2_3_exact N hN_pos with ⟨_, _, _, _, _, hmul⟩
  rw [hg1, Nat.mul_one] at hmul
  rcases eq_pow2_of_v2Pow_aux N N hN_pos (Nat.le_refl _) with ⟨k_e, hk_e⟩
  rcases eq_pow3_of_v3Pow_aux N N hN_pos (Nat.le_refl _) with ⟨m_e, hm_e⟩
  rw [hk_e, hm_e] at hmul
  have hmul_comm : x + 796358443 = 2 ^ k_e * 3 ^ m_e := by
    rw [Nat.add_comm x 796358443, ← hN_def, ← hmul]
  clear hg1 hk_e hm_e hN_def hmul hN_pos
  have hk46 : k_e ≥ 46 := by
    by_cases hlt : k_e < 46
    · exfalso
      have h46_sp : 70368744177664 = 2 ^ (k_e + 1) * 2 ^ (45 - k_e) := by
        rw [← Nat.pow_add 2 (k_e + 1) (45 - k_e),
            show k_e + 1 + (45 - k_e) = 46 by clear hraw_step hx_ge hx3 hdvd46 hmul_comm; omega]
      rcases hdvd46 with ⟨c, hc⟩
      rw [hmul_comm, h46_sp, Nat.mul_assoc (2 ^ (k_e + 1)), Nat.pow_succ 2 k_e, Nat.mul_assoc (2 ^ k_e) 2] at hc
      have h3m_ev : 3 ^ m_e = 2 * (2 ^ (45 - k_e) * c) :=
        nat_mul_left_cancel_pos (2 ^ k_e) _ _ (pow2_pos_nat k_e) hc
      have ho := pow3_odd_nat_sec8 m_e
      rw [h3m_ev, Nat.mul_mod_right] at ho; cases ho
    · clear hraw_step hx_ge hx3 hdvd46 hmul_comm; omega
  clear hdvd46
  have hm1 : m_e ≥ 1 := by
    cases m_e with
    | zero =>
      rw [Nat.pow_zero, Nat.mul_one] at hmul_comm
      exact False.elim (pow2_mod3_nonzero_w5 k_e (by rw [← hmul_comm, Nat.add_mod, hx3]))
    | succ _ => clear hraw_step hx_ge hx3 hmul_comm hk46; omega
  clear hx3
  let y := 2 ^ (k_e - 7) * 3 ^ (m_e + 1) - 18664651
  have hstep_x : cousinDiamond13Step x = y := by
    rw [hraw_step]; dsimp only [y]
    have hp128 : 2 ^ k_e = 128 * 2 ^ (k_e - 7) := by
      conv => lhs; rw [show k_e = 7 + (k_e - 7) by clear hraw_step hx_ge hmul_comm hm1; omega, Nat.pow_add]
    have hprod_pos : 2 ^ (k_e - 7) * 3 ^ m_e ≥ 549755813888 * 3 := by
      have h1 : 549755813888 ≤ 2 ^ (k_e - 7) := by
        rw [show (549755813888 : Nat) = 2 ^ 39 from rfl]
        exact pow2_mono_nat (by clear hraw_step hx_ge hmul_comm hm1 hp128; omega)
      have h2 : 3 ≤ 3 ^ m_e := by simpa using nat_pow_mono_exp_pos 3 1 m_e (by decide) hm1
      simpa using Nat.mul_le_mul h1 h2
    have h3_eq : 2 ^ (k_e - 7) * 3 ^ (m_e + 1) = 3 * (2 ^ (k_e - 7) * 3 ^ m_e) := by
      rw [Nat.pow_succ 3 m_e, ← Nat.mul_assoc, Nat.mul_comm _ 3]
    rw [h3_eq]
    have hx128 : x + 796358443 = 128 * (2 ^ (k_e - 7) * 3 ^ m_e) := by rw [hmul_comm, hp128, Nat.mul_assoc]
    have h3x1 : 3 * x + 1 = (3 * (2 ^ (k_e - 7) * 3 ^ m_e) - 18664651) * 128 := by
      clear hraw_step hk46 hm1 hp128 h3_eq hmul_comm
      generalize 2 ^ (k_e - 7) * 3 ^ m_e = A at hprod_pos hx128 ⊢; omega
    rw [h3x1]; exact Nat.mul_div_left _ (by decide : 0 < 128)
  have hc13_y : isDiamond12Cone13 y :=
    isDiamond12Cone13_of_pow2_pow3_w16 (k_e - 7) (m_e + 1)
      (by clear hraw_step hx_ge hmul_comm hstep_x; omega)
      (by clear hraw_step hx_ge hmul_comm hstep_x; omega)
  rcases hc13_ret y hc13_y with ⟨_, _, ky, _, _, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hstep_eq : y = (3 * x + 1) / 128 := hstep_x.symm.trans hraw_step
    have hdiv : y * 128 ≤ 3 * x + 1 := by rw [hstep_eq]; exact Nat.div_mul_le_self (3 * x + 1) 128
    clear hraw_step hmul_comm hstep_x hc13_y hky_1 hstep_eq; omega
  refine ⟨k_e, m_e, 1 + ky, hk46, hm1, hmul_comm, hstep_x, by rw [hstep_x]; exact hc13_y,
          by clear hraw_step hmul_comm hstep_x hc13_y hky_1; omega,
          Nat.le_trans (by clear hraw_step hmul_comm hstep_x hc13_y hky_1; omega : 1 + ky ≤ x + 1)
            (cousinDiamond2Phi_ge_succ x), ?_⟩
  rw [cousinDiamond13Iter_add 1 ky x, show cousinDiamond13Iter 1 x = y from hstep_x]; exact hky_1

private theorem cousin_diamond13_reaches_one_within_phi :
    ∀ (B x : Nat), x > 0 -> cousinDiamond2Phi x ≤ B ->
      ∃ k : Nat, k ≤ B ∧ cousinDiamond13Iter k x = 1
  | 0, x, _, hB => by have := cousinDiamond2Phi_ge_succ x; omega
  | B + 1, x, hx, hB => by
    by_cases hx1 : x = 1
    · subst hx1; exact ⟨0, by omega, rfl⟩
    · by_cases hx2 : x = 2
      · subst hx2
        have hphi2 : cousinDiamond2Phi 2 = 28 := by decide
        rw [hphi2] at hB; exact ⟨1, by omega, by decide⟩
      · by_cases hc4 : isDiamond3Cone4 x
        · rcases cousin_diamond13_cones4to14_exact_return.1 x hc4 with ⟨k, hle, hk1⟩
          exact ⟨k, Nat.le_trans hle hB, hk1⟩
        · by_cases hc5 : isDiamond4Cone5 x
          · rcases cousin_diamond13_cones4to14_exact_return.2.1 x hc5 with ⟨_, _, k, _, _, _, _, hle, hk1⟩
            exact ⟨k, Nat.le_trans hle hB, hk1⟩
          · by_cases hc6 : isDiamond5Cone6 x
            · rcases cousin_diamond13_cones4to14_exact_return.2.2.1 x hc6 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
              exact ⟨k, Nat.le_trans hle hB, hk1⟩
            · by_cases hc7 : isDiamond6Cone7 x
              · rcases cousin_diamond13_cones4to14_exact_return.2.2.2.1 x hc7 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                exact ⟨k, Nat.le_trans hle hB, hk1⟩
              · by_cases hc8 : isDiamond7Cone8 x
                · rcases cousin_diamond13_cones4to14_exact_return.2.2.2.2.1 x hc8 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                  exact ⟨k, Nat.le_trans hle hB, hk1⟩
                · by_cases hc9 : isDiamond8Cone9 x
                  · rcases cousin_diamond13_cones4to14_exact_return.2.2.2.2.2.1 x hc9 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                    exact ⟨k, Nat.le_trans hle hB, hk1⟩
                  · by_cases hc10 : isDiamond9Cone10 x
                    · rcases cousin_diamond13_cones4to14_exact_return.2.2.2.2.2.2.1 x hc10 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                      exact ⟨k, Nat.le_trans hle hB, hk1⟩
                    · by_cases hc11 : isDiamond10Cone11 x
                      · rcases cousin_diamond13_cones4to14_exact_return.2.2.2.2.2.2.2.1 x hc11 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                        exact ⟨k, Nat.le_trans hle hB, hk1⟩
                      · by_cases hc12 : isDiamond11Cone12 x
                        · rcases cousin_diamond13_cones4to14_exact_return.2.2.2.2.2.2.2.2.1 x hc12 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                          exact ⟨k, Nat.le_trans hle hB, hk1⟩
                        · by_cases hc13 : isDiamond12Cone13 x
                          · rcases cousin_diamond13_cones4to14_exact_return.2.2.2.2.2.2.2.2.2.1 x hc13 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                            exact ⟨k, Nat.le_trans hle hB, hk1⟩
                          · by_cases hc14 : isDiamond13Cone14 x
                            · rcases cousin_diamond13_cones4to14_exact_return.2.2.2.2.2.2.2.2.2.2 x hc14 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                              exact ⟨k, Nat.le_trans hle hB, hk1⟩
                            · have hdesc := cousin_diamond13_outside_cones4to14_descent_and_mod33_nonreentry.1 x
                                (by omega) hc4 hc5 hc6 hc7 hc8 hc9 hc10 hc11 hc12 hc13 hc14
                              rcases cousin_diamond13_reaches_one_within_phi B (cousinDiamond13Step x)
                                (cousinDiamond13Step_pos x hx) (by omega) with ⟨k, hk_le, hk_eq⟩
                              exact ⟨k + 1, by omega, hk_eq⟩

/--
  Theorem W16.3f (`cousin_diamond13_global_convergence`, `zero custom axioms`):
  Unconditional Global Convergence & Degree-5 Polynomial Stopping Bound for `T_diamond13`:
  For EVERY `x > 0`, `cousinDiamond13Iter` reaches `1` within `k ≤ (x + 1) ^ 3 + (x + 1) ^ 5` steps!
-/
theorem cousin_diamond13_global_convergence (x : Nat) (hx : x > 0) :
    ∃ k : Nat, k ≤ (x + 1) ^ 3 + (x + 1) ^ 5 ∧ cousinDiamond13Iter k x = 1 := by
  rcases cousin_diamond13_reaches_one_within_phi (cousinDiamond2Phi x) x hx (Nat.le_refl _) with
    ⟨k, hk_phi, hk1⟩
  exact ⟨k, Nat.le_trans hk_phi (cousinDiamond2Phi_upper_poly_bound x), hk1⟩

private theorem exists_non_desc_along_diamond13_iter_w16 :
    ∀ (terms : List LaurentTerm) (A0 B0 C0 N z : Nat),
      N ≥ 1 ->
      (∀ i : Nat, i < N ->
        cousinDiamond13Iter i z ≥ 3 ∧
        (cousinDiamond13Iter i z) % 2 = 1 ∧
        cousinDiamond13Step (cousinDiamond13Iter i z) ≥ 3) ->
      ¬ laurentDescProp terms A0 B0 C0 z (cousinDiamond13Iter N z) ->
      ∃ x : Nat,
        x ≥ 3 ∧ x % 2 = 1 ∧ cousinDiamond13Step x ≥ 3 ∧
        ¬ laurentDescProp terms A0 B0 C0 x (cousinDiamond13Step x)
  | _, _, _, _, 0, _, hN, _, _ => by omega
  | _, _, _, _, 1, z, _, hall, hnd => by
    rcases hall 0 (by decide) with ⟨hz3, hzo, hsz3⟩
    exact ⟨z, hz3, hzo, hsz3, hnd⟩
  | terms, A0, B0, C0, m + 2, z, _, hall, hnd => by
    if h0 : laurentDescProp terms A0 B0 C0 z (cousinDiamond13Step z) then
      have hnd_next : ¬ laurentDescProp terms A0 B0 C0 (cousinDiamond13Step z)
          (cousinDiamond13Iter (m + 1) (cousinDiamond13Step z)) :=
        fun hrest => hnd (laurentDescProp_trans terms A0 B0 C0 z (cousinDiamond13Step z) _ h0 hrest)
      exact exists_non_desc_along_diamond13_iter_w16 terms A0 B0 C0 (m + 1) (cousinDiamond13Step z)
        (by omega) (fun i hi => hall (i + 1) (by omega)) hnd_next
    else
      rcases hall 0 (by omega) with ⟨hz3, hzo, hsz3⟩
      exact ⟨z, hz3, hzo, hsz3, h0⟩

/--
  Theorem W16.3g (`cousin_diamond13_eleven_tier_cascade_and_laurent_impossibility`,
  `zero custom axioms`):
  1. Genuine 11-Tier `Cone 14 -> Cone 13 -> Cone 12 -> ... -> Cone 5` Cascade
     `844424133773525 -> 19791190635317 -> 1855424122061 -> 695784045773 -> 260919017165 ->
      97844631437 -> 36691736789 -> 859962581 -> 20155373 -> 7558265` & Unbounded `r`-Block Spiral
     Climb `cousinDiamond13Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5`!
  2. Universal `∀ L ≥ 1` Multi-Term Laurent Valuation Impossibility on `cousinDiamond13Step`!
-/
theorem cousin_diamond13_eleven_tier_cascade_and_laurent_impossibility :
    cousinDiamond13Step 844424133773525 = 19791190635317 ∧
    cousinDiamond13Step 19791190635317 = 1855424122061 ∧
    cousinDiamond13Step 1855424122061 = 695784045773 ∧
    cousinDiamond13Step 695784045773 = 260919017165 ∧
    cousinDiamond13Step 260919017165 = 97844631437 ∧
    cousinDiamond13Step 97844631437 = 36691736789 ∧
    cousinDiamond13Step 36691736789 = 859962581 ∧
    cousinDiamond13Step 859962581 = 20155373 ∧
    cousinDiamond13Step 20155373 = 7558265 ∧
    (∀ (r j : Nat), r ≥ 1 -> j ≤ r ->
      cousinDiamond13Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5) ∧
    (∀ (terms : List LaurentTerm) (A0 B0 C0 : Nat),
      (∃ t ∈ terms, t.coeff > 0) ->
      ∃ x : Nat,
        x ≥ 3 ∧ x % 2 = 1 ∧ cousinDiamond13Step x ≥ 3 ∧
        ¬ (evalLaurentSumNum terms (cousinDiamond13Step x) * laurentValDen A0 B0 C0 x <
            evalLaurentSumNum terms x * laurentValDen A0 B0 C0 (cousinDiamond13Step x))) := by
  have hspiral : ∀ (r j : Nat), r ≥ 1 -> j ≤ r ->
      cousinDiamond13Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5 := by
    intro r j hr hj
    cases j with
    | zero => simp [cousinDiamond13Iter]
    | succ j' =>
      have hp16_ge16 : 16 ^ r ≥ 16 := by
        rw [show r = (r - 1) + 1 by omega, Nat.pow_succ]
        have := nat_pow_pos_of_pos 16 (by decide) (r - 1); omega
      let x0 := 4 * 16 ^ r - 5
      have hx0_m4 : x0 % 4 = 3 := by dsimp [x0]; omega
      have hx0_pow : 4 * 16 ^ r = 2 ^ (4 * r + 2) := by
        rw [show (16 : Nat) = 2 ^ 4 from rfl, pow_pow_eq_mul_w5 2 4 r,
            show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add 2 2 (4 * r), Nat.add_comm 2 (4 * r)]
      have hs_first : cousinDiamond13Step x0 = 2 ^ (4 * r + 1) * 3 ^ 1 - 7 := by
        rw [d13_eq_d12_of_not_cone14 x0 (not_cone14_of_mod4_eq_3 x0 hx0_m4),
            d12_eq_d11_of_not_cone13_w16 x0 (not_cone13_of_mod32_ne_21_w16 x0 (by omega)),
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
      have hclimb := cousin_diamond13_cone5_two_step_climb j' (4 * r + 1) 1 (by omega) (by decide)
      let y_end := 2 ^ (4 * r + 1 - 3 * j') * 3 ^ (1 + 2 * j') - 7
      have hy_c5 := isDiamond4Cone5_of_pow2_pow3 (4 * r + 1 - 3 * j') (1 + 2 * j') (by omega) (by omega)
      have hs_last : cousinDiamond13Step y_end = 4 * 16 ^ (r - (j' + 1)) * 18 ^ (j' + 1) - 5 := by
        rw [d13_eq_d12_of_not_cone14 y_end (not_cone14_of_mod32_ne_21 y_end (by have := hy_c5.2.1; omega)),
            d12_eq_d11_of_not_cone13_w16 y_end (not_cone13_of_mod32_ne_21_w16 y_end (by have := hy_c5.2.1; omega)),
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
          rw [← pow9_eq_pow3_double (j' + 1), ← mul_pow_w16s 2 9 (j' + 1)]
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
          cousinDiamond13Iter_add (1 + 2 * j') 1,
          cousinDiamond13Iter_add 1 (2 * j'),
          show cousinDiamond13Iter 1 x0 = 2 ^ (4 * r + 1) * 3 ^ 1 - 7 from hs_first, hclimb]
      exact hs_last
  refine ⟨by decide, by decide, by decide, by decide, by decide,
          by decide, by decide, by decide, by decide, hspiral, ?_⟩
  intro terms A0 B0 C0 hnonempty
  rcases three_family_multiterm_laurent_obstruction terms A0 B0 C0 hnonempty with
    h97 | ⟨j2, hj2⟩ | ⟨r, hr_pos, hr3⟩
  · have hs97 : cousinDiamond13Step 97 = 73 := by decide
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
    have hstep_xj2 : cousinDiamond13Step xj2 = yj2 := by
      rw [d13_eq_d12_of_not_cone14 xj2 (not_cone14_of_mod8_ne_5 xj2 (by have := hc4_xj2.2.1; omega)),
          d12_eq_d11_of_not_cone13_w16 xj2 (not_cone13_of_mod32_ne_21_w16 xj2 (by have := hc4_xj2.2.1; omega)),
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
        cousinDiamond13Iter i xr3 = 3 ^ i * 2 ^ (2 * r + 1 - i) - 1 ∧
        cousinDiamond13Iter i xr3 ≥ 7 ∧ (cousinDiamond13Iter i xr3) % 2 = 1 := by
      intro i hi
      have hf := cousin_diamond13_mersenne_scaled i (2 * r + 1) 1 (by omega) (by decide)
      rw [← hxr3_pow, Nat.mul_one] at hf
      have hprod_ge8 : 3 ^ i * 2 ^ (2 * r + 1 - i) ≥ 8 := by
        have h1 : 2 ^ i * 2 ^ (2 * r + 1 - i) ≤ 3 ^ i * 2 ^ (2 * r + 1 - i) :=
          Nat.mul_le_mul_right _ (pow2_le_pow3 i)
        rw [← Nat.pow_add, show i + (2 * r + 1 - i) = 2 * r + 1 by omega] at h1
        exact Nat.le_trans (pow2_mono_nat (by omega : 3 ≤ 2 * r + 1)) h1
      have hprod_ev : (3 ^ i * 2 ^ (2 * r + 1 - i)) % 2 = 0 := by
        rw [show 2 * r + 1 - i = (2 * r - i) + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc]; omega
      exact ⟨hf, by rw [hf]; omega, by rw [hf]; omega⟩
    have hiter_2r : cousinDiamond13Iter (2 * r) xr3 = zr := by
      have hf := (hglide_i (2 * r) (Nat.le_refl _)).1
      rw [hf, show 2 * r + 1 - 2 * r = 1 by omega, Nat.pow_one, ← pow9_eq_pow3_double r, Nat.mul_comm]
    have hstep_zr : cousinDiamond13Step zr = yr3 := by
      rw [d13_eq_d12_of_not_cone14 zr (not_cone14_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          d12_eq_d3_of_not_cones5to13_w16 zr
            (not_cone13_of_mod32_ne_21_w16 zr (by dsimp [zr]; omega))
            (not_cone12_of_mod8_ne_5 zr (by dsimp [zr]; omega))
            (not_cone11_of_mod8_ne_5 zr (by dsimp [zr]; omega))
            (not_cone10_of_mod8_ne_5 zr (by dsimp [zr]; omega))
            (not_cone9_of_mod8_ne_5 zr (by dsimp [zr]; omega))
            (not_cone8_of_mod8_ne_5 zr (by dsimp [zr]; omega))
            (not_cone7_of_mod8_ne_5 zr (by dsimp [zr]; omega))
            (not_cone6_of_mod16_ne_13 zr (by dsimp [zr]; omega))
            (by rintro ⟨_, h32, _, _⟩; dsimp [zr] at h32; omega)]
      have hc3 : core3 (zr + 1) = 2 := by
        rw [show zr + 1 = 2 * 9 ^ r by dsimp [zr]; omega, core3_mul2 (9 ^ r) (by omega), (pow9_eq_v3Pow_w5 r).2]
      rw [cousinDiamond3Step_of_core3_succ_two_w8 zr (by dsimp [zr]; omega) (by dsimp [zr]; omega) hc3]
      dsimp [zr, yr3]; omega
    have hiter_2r1 : cousinDiamond13Iter (2 * r + 1) xr3 = yr3 := by
      rw [cousinDiamond13Iter_add (2 * r) 1 xr3, hiter_2r]; exact hstep_zr
    have hall : ∀ i : Nat, i < 2 * r + 1 ->
        cousinDiamond13Iter i xr3 ≥ 3 ∧ (cousinDiamond13Iter i xr3) % 2 = 1 ∧
        cousinDiamond13Step (cousinDiamond13Iter i xr3) ≥ 3 := by
      intro i hi
      by_cases hlt : i < 2 * r
      · rcases hglide_i i (by omega) with ⟨_, hge7, hodd_i⟩
        rcases hglide_i (i + 1) (by omega) with ⟨_, hge7_n, _⟩
        refine ⟨by omega, hodd_i, ?_⟩
        change cousinDiamond13Iter 1 (cousinDiamond13Iter i xr3) ≥ 3
        rw [← cousinDiamond13Iter_add i 1 xr3]; omega
      · rw [show i = 2 * r by omega, hiter_2r, hstep_zr]
        exact ⟨by dsimp [zr]; omega, by dsimp [zr]; omega, by dsimp [yr3]; omega⟩
    change ¬ laurentDescProp terms A0 B0 C0 xr3 yr3 at hr3
    rw [← hiter_2r1] at hr3
    exact exists_non_desc_along_diamond13_iter_w16 terms A0 B0 C0 (2 * r + 1) xr3 (by omega) hall hr3

set_option maxRecDepth 16384 in
/--
  Theorem W16.3h (`cousin_diamond13_counter_model_separation`, `[]` axioms):
  `T_diamond13` rejects ALL three Counter-Models (`M1 = Q_(6)^+` 5-cycle `(1, 7) -> ... -> (1, 7)`
  plus non-integers `(211105436174549, 7)` and `(844424133773525, 7)` bypassing Cone 14 by `W16.3b`,
  `M2 = Z^-` cycles `-1` and `-5 -> -7 -> -10 -> -5`, and `M3` supercritical `q = 7` 5-cycle at `5`),
  AND at the genuine `v_2(3x + 1) = 7` Cone-14 jumps `211105436174549 -> 4947783660341` (`26` steps to `1`)
  and `844424133773525 -> 19791190635317 -> 1855424122061 -> 695784045773 -> 260919017165 ->
  97844631437 -> 36691736789 -> 859962581 -> 20155373 -> 7558265` (`ZPOS_COUSIN_DIAMOND13_CONE14_844424133773525_JUMP`,
  `24` steps to `1`) strictly increases `cousinDiamond2Phi` (`+6.84x`) directly into
  `Cone 13 -> Cone 12 -> ... -> Cone 5`!
-/
theorem cousin_diamond13_counter_model_separation :
    cousinDiamond13StepInt (-1) = -1 ∧
    cousinDiamond13IterInt 3 (-5) = -5 ∧
    cousinDiamond13IterParam 7 5 5 = 5 ∧
    cousinDiamond13StepQ6 (1, 7) = (5, 7) ∧
    cousinDiamond13IterQ6 5 (1, 7) = (1, 7) ∧
    cousinDiamond13StepQ6 (211105436174549, 7) = cousinDiamond12StepQ6 (211105436174549, 7) ∧
    cousinDiamond13StepQ6 (844424133773525, 7) = cousinDiamond12StepQ6 (844424133773525, 7) ∧
    isDiamond13Cone14 211105436174549 ∧
    cousinDiamond13Step 211105436174549 = 4947783660341 ∧
    cousinDiamond13Iter 26 211105436174549 = 1 ∧
    isDiamond13Cone14 844424133773525 ∧
    cousinDiamond13Step 844424133773525 = 19791190635317 ∧
    cousinDiamond13StepInt 844424133773525 = 19791190635317 ∧
    cousinDiamond13StepQ6 (844424133773525, 1) = (19791190635317, 1) ∧
    isDiamond12Cone13 19791190635317 ∧
    isDiamond11Cone12 1855424122061 ∧
    isDiamond10Cone11 695784045773 ∧
    isDiamond9Cone10 260919017165 ∧
    isDiamond8Cone9 97844631437 ∧
    isDiamond7Cone8 36691736789 ∧
    isDiamond6Cone7 859962581 ∧
    isDiamond5Cone6 20155373 ∧
    isDiamond4Cone5 7558265 ∧
    cousinDiamond2Phi 844424133773525 < cousinDiamond2Phi 19791190635317 ∧
    cousinDiamond13Iter 24 844424133773525 = 1 := by
  decide


-- ============================================================================
-- SECTION 3: Front D (Branches P2.2 & P5.3) — Complete Mod-`39366` (`2 * 3^9`,
--            `w ≥ 10`) Markov Shift Bijection, Exact `1 + 7 + 14 + 5 = 27`
--            Prefix Quadripartition, & Constructive Compressed-Threshold True
--            Exponential (`≥ 2^B`) Dyadic-Window Occupancy (`W16_H4`)
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Section 3A: Complete Mod-`39366` (`2 * 3^9`) Markov Bijection (`13122 / 39366`
--             Surviving Classes on `w ≥ 10`), Prefix-Weight-`9` `1 + 7 + 14 + 5 = 27`
--             Quadripartition, & `3 ^ (w - 10)` (`j = 9`) Fiber Equidistribution
-- ----------------------------------------------------------------------------

/-- Canonical ordered list of the `13122` (`= 2 * 3^8`) surviving mod-`39366` (`= 2 * 3^9`)
    suffix-shift classes `{r < 39366 | r % 6 = 1 ∨ r % 6 = 3}` on `w ≥ 10`. -/
def survivingMod39366List : List Nat :=
  (List.range 39366).filter (fun r => r % 6 == 1 || r % 6 == 3)

private theorem mem_survivingMod39366List_iff_w16 (r : Nat) :
    r ∈ survivingMod39366List ↔ (r < 39366 ∧ (r % 6 = 1 ∨ r % 6 = 3)) := by
  unfold survivingMod39366List
  rw [List.mem_filter, List.mem_range]
  simp only [Bool.or_eq_true, beq_iff_eq]

private theorem range_six_mul_surviving_len_w16 :
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
    have ih := range_six_mul_surviving_len_w16 n
    change ((List.range (6 * n)).filter p).length = 2 * n at ih
    omega

/-- Exact `1 + 7 + 14 + 5 = 27` surviving mod-`512` prefix weight-`9` predicates:
    - `isTopWeight9SurvivingMod512Bool`: `w(pref_9) = 9` (`1 / 27` class `r = 511`, forcing `w(u) ≥ 10` at `|u| ≥ 10`),
    - `isExactWeight8SurvivingMod512Bool`: `w(pref_9) = 8` (`7 / 27` classes, escaping at `w(u) = 9`),
    - `isMedWeight7SurvivingMod512Bool`: `w(pref_9) = 7` (`14 / 27` classes),
    - `isLowWeight6SurvivingMod512Bool`: `w(pref_9) = 6` (`5 / 27` classes). -/
def isTopWeight9SurvivingMod512Bool (y : Nat) : Bool :=
  isSurvivingMod512Bool (y % 512) && decide (parityWeight (parityOfIter 9 (y % 512)) = 9)

def isExactWeight8SurvivingMod512Bool (y : Nat) : Bool :=
  isSurvivingMod512Bool (y % 512) && decide (parityWeight (parityOfIter 9 (y % 512)) = 8)

def topWeight9Mod512Residues1 : List Nat :=
  survivingMod512Residues27.filter isTopWeight9SurvivingMod512Bool

def exactWeight8Mod512Residues7 : List Nat :=
  survivingMod512Residues27.filter isExactWeight8SurvivingMod512Bool

private theorem take_drop_split_eq_w16 :
    ∀ (k : Nat) (xs : List Bool), xs.take k ++ xs.drop k = xs
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, x :: xs => by
    simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append,
               take_drop_split_eq_w16 k xs]

private theorem take_len_of_ge_w16 :
    ∀ (k : Nat) (xs : List Bool), k ≤ xs.length -> (xs.take k).length = k
  | 0, _, _ => rfl
  | _ + 1, [], h => by simp at h
  | k + 1, _ :: xs, h => by
    simp only [List.length_cons] at h
    simp only [List.take_succ_cons, List.length_cons, take_len_of_ge_w16 k xs (by omega)]

private theorem len10_core_mod512_prefix9_w16
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

private theorem pow_mod_eq_pow_mod_w16 (b m : Nat) :
    ∀ e : Nat, (b ^ e) % m = ((b % m) ^ e) % m
  | 0 => rfl
  | e + 1 => by
    rw [Nat.pow_succ b e, Nat.pow_succ (b % m) e, Nat.mul_mod (b ^ e) b m,
        pow_mod_eq_pow_mod_w16 b m e, Nat.mul_mod ((b % m) ^ e % m) (b % m) m,
        Nat.mod_mod, ← Nat.mul_mod ((b % m) ^ e) (b % m) m]

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 131072 in
/--
  Theorem W16.4a (`markovShift_mod39366_bijection_and_prefix1_weight10_quadripartition`,
  `zero custom axioms`):
  Complete Mod-`39366` (`2 * 3^9`) Markov Bijection onto `13122` Surviving Classes (`w ≥ 10`),
  Exact `1 + 7 + 14 + 5 = 27` Mod-`512` Prefix-Weight-`9` Quadripartition (`1` All-Ones Prefix `511`
  Forces `w(u) ≥ 10` vs `7` Exact-Weight-`8` Escape `ZPOS_DYADIC_LEN11_WEIGHT9_HIGH_PREFIX_ESCAPE`
  at `145023390002129744557057965701200958845287`), Mod-`39366` Suffix Locks (`19683`, `6561`, &
  `{6561, 19683, 32805}`), & `3 ^ (w - 10)` (`j = 9`) Multi-Step Fiber Equidistribution
  (`Branch P5.3`, `W16_H4`).
-/
theorem markovShift_mod39366_bijection_and_prefix1_weight10_quadripartition :
    ((∀ (w a : Nat), w ≥ 9 -> a < 2 * 3 ^ (w - 1) ->
        markovShiftTrue w a % 39366 = markovShiftTrue 9 (a % 13122) % 39366) ∧
     survivingMod39366List.length = 13122 ∧
     (∀ x1 x2 : Fin 13122,
        markovShiftTrue 9 x1.val % 39366 = markovShiftTrue 9 x2.val % 39366 -> x1 = x2) ∧
     (∀ x : Fin 13122,
        markovShiftTrue 9 x.val % 39366 ∈ survivingMod39366List) ∧
     (∀ r ∈ survivingMod39366List,
        ∃ x : Fin 13122, markovShiftTrue 9 x.val % 39366 = r)) ∧
    (topWeight9Mod512Residues1 = [511] ∧
     exactWeight8Mod512Residues7.length = 7 ∧
     medWeight7Mod512Residues14.length = 14 ∧
     lowWeight6Mod512Residues5.length = 5 ∧
     (∀ r : Fin 512, isSurvivingMod512Bool r.val = true ->
        (isTopWeight9SurvivingMod512Bool r.val = true ∧
         isExactWeight8SurvivingMod512Bool r.val = false ∧
         isMedWeight7SurvivingMod512Bool r.val = false ∧
         isLowWeight6SurvivingMod512Bool r.val = false) ∨
        (isExactWeight8SurvivingMod512Bool r.val = true ∧
         isTopWeight9SurvivingMod512Bool r.val = false ∧
         isMedWeight7SurvivingMod512Bool r.val = false ∧
         isLowWeight6SurvivingMod512Bool r.val = false) ∨
        (isMedWeight7SurvivingMod512Bool r.val = true ∧
         isTopWeight9SurvivingMod512Bool r.val = false ∧
         isExactWeight8SurvivingMod512Bool r.val = false ∧
         isLowWeight6SurvivingMod512Bool r.val = false) ∨
        (isLowWeight6SurvivingMod512Bool r.val = true ∧
         isTopWeight9SurvivingMod512Bool r.val = false ∧
         isExactWeight8SurvivingMod512Bool r.val = false ∧
         isMedWeight7SurvivingMod512Bool r.val = false)) ∧
     (∀ u : List Bool, IsCoreParityWord u -> parityWeight u ≥ 10 ->
        canonicalSuffixShift u 1 % 39366 ∈ survivingMod39366List) ∧
     (∀ (u : List Bool) (q : Nat),
        IsCoreParityWord u -> u.length ≥ 10 ->
        isTopWeight9SurvivingMod512Bool (exactBackwardQuotient 1 u q) = true ->
        parityWeight u ≥ 10 ∧ canonicalSuffixShift u 1 % 39366 ∈ survivingMod39366List) ∧
     (let u_esc9 : List Bool :=
        [true, true, true, false, true, true, true, true, true] ++
          List.replicate 42 false ++ [true]
      u_esc9.length = 52 ∧
      parityWeight u_esc9 = 9 ∧
      IsFirstHitOnePair u_esc9 0 ∧
      exactBackwardQuotient 1 u_esc9 0 = 145023390002129744557057965701200958845287 ∧
      IsSurvivingMod373248Class (exactBackwardQuotient 1 u_esc9 0) ∧
      isExactWeight8SurvivingMod512Bool (exactBackwardQuotient 1 u_esc9 0) = true)) ∧
    ((∀ pref : List Bool,
        canonicalSuffixShift (pref ++ List.replicate 9 true) 1 % 39366 = 6561 ∨
        canonicalSuffixShift (pref ++ List.replicate 9 true) 1 % 39366 = 19683 ∨
        canonicalSuffixShift (pref ++ List.replicate 9 true) 1 % 39366 = 32805) ∧
     (∀ pref : List Bool,
        canonicalSuffixShift (pref ++ List.replicate 10 true) 1 % 39366 = 19683 ∧
        canonicalSuffixShift (pref ++ ([true, false] ++ List.replicate 9 true)) 1 % 39366 = 6561)) ∧
    (∀ (tail : List Bool) (w r0 : Nat),
      w ≥ 10 -> r0 < 39366 ->
      let Mk := 2 * 3 ^ (9 + parityWeight tail)
      let N := 3 ^ (w - 10)
      let base := iterMarkovShift tail w r0 % Mk
      (∀ t : Nat, t < N ->
        ∃ q : Nat, q < N ∧ iterMarkovShift tail w (r0 + 39366 * t) = base + Mk * q) ∧
      (∀ q : Nat, q < N ->
        ∃ t : Nat, t < N ∧
          iterMarkovShift tail w (r0 + 39366 * t) = base + Mk * q ∧
          ∀ t' : Nat, t' < N ->
            iterMarkovShift tail w (r0 + 39366 * t') = base + Mk * q -> t' = t)) := by
  have h13122_eq : (2 : Nat) * 3 ^ (9 - 1) = 13122 := by decide
  have h39366_eq : (2 : Nat) * 3 ^ 9 = 39366 := by decide
  have hcongr39366 : ∀ (w a : Nat), w ≥ 9 -> a < 2 * 3 ^ (w - 1) ->
      markovShiftTrue w a % 39366 = markovShiftTrue 9 (a % 13122) % 39366 := by
    intro w a hw9 ha_lt
    have hr_lt : a % 13122 < 2 * 3 ^ (9 - 1) := by rw [h13122_eq]; exact Nat.mod_lt a (by decide)
    exact markovShiftTrue_contraction_mod_pow3 8 w 9 a (a % 13122)
      (by omega) (by decide) ha_lt hr_lt (by simp)
  have hlen39366 : survivingMod39366List.length = 13122 := by
    unfold survivingMod39366List
    have h := range_six_mul_surviving_len_w16 6561
    simpa using h
  have hinj13122 : ∀ x1 x2 : Fin 13122,
      markovShiftTrue 9 x1.val % 39366 = markovShiftTrue 9 x2.val % 39366 -> x1 = x2 := by
    intro x1 x2 heq
    have hx1 : x1.val < 2 * 3 ^ (9 - 1) := by rw [h13122_eq]; exact x1.isLt
    have hx2 : x2.val < 2 * 3 ^ (9 - 1) := by rw [h13122_eq]; exact x2.isLt
    have hm1_lt : markovShiftTrue 9 x1.val < 39366 := by
      rw [← h39366_eq]
      exact (canonicalSuffixShift_markov_bijection_and_mod6_lock.2.1 9 x1.val (by decide) hx1).1
    have hm2_lt : markovShiftTrue 9 x2.val < 39366 := by
      rw [← h39366_eq]
      exact (canonicalSuffixShift_markov_bijection_and_mod6_lock.2.1 9 x2.val (by decide) hx2).1
    rw [Nat.mod_eq_of_lt hm1_lt, Nat.mod_eq_of_lt hm2_lt] at heq
    exact Fin.ext (canonicalSuffixShift_markov_bijection_and_mod6_lock.2.2.1 9 x1.val x2.val
      (by decide) hx1 hx2 heq)
  have hmem13122 : ∀ x : Fin 13122, markovShiftTrue 9 x.val % 39366 ∈ survivingMod39366List := by
    intro x
    have hx : x.val < 2 * 3 ^ (9 - 1) := by rw [h13122_eq]; exact x.isLt
    rcases canonicalSuffixShift_markov_bijection_and_mod6_lock.2.1 9 x.val (by decide) hx with
      ⟨hlt, hm6⟩
    rw [h39366_eq] at hlt
    rw [Nat.mod_eq_of_lt hlt]
    exact (mem_survivingMod39366List_iff_w16 _).mpr ⟨hlt, hm6⟩
  have hsurj13122 : ∀ r ∈ survivingMod39366List,
      ∃ x : Fin 13122, markovShiftTrue 9 x.val % 39366 = r := by
    intro r hr
    rcases (mem_survivingMod39366List_iff_w16 r).mp hr with ⟨hr_lt, hr_m6⟩
    rcases canonicalSuffixShift_markov_bijection_and_mod6_lock.2.2.2.1 9 r (by decide)
      (by rw [h39366_eq]; exact hr_lt) hr_m6 with ⟨a, ha_lt, ha_eq⟩
    rw [h13122_eq] at ha_lt
    refine ⟨⟨a, ha_lt⟩, ?_⟩
    dsimp only
    rw [ha_eq, Nat.mod_eq_of_lt hr_lt]
  have hconf10 : ∀ u : List Bool, IsCoreParityWord u -> parityWeight u ≥ 10 ->
      canonicalSuffixShift u 1 % 39366 ∈ survivingMod39366List := by
    intro u hu hw10
    rcases list_eq_append_true_of_reverse_head u hu.2 with ⟨v, rfl⟩
    have hw_v : parityWeight v ≥ 9 := by
      rw [parityWeight_append] at hw10
      have h1 : parityWeight [true] = 1 := rfl
      rw [h1] at hw10; omega
    have hrec : canonicalSuffixShift (v ++ [true]) 1 =
        markovShiftTrue (parityWeight v) (canonicalSuffixShift v 1) :=
      (canonicalSuffixShift_append_markov_recurrence.2.2 v (by omega)).2.2.1
    have ha_lt := (canonicalSuffixShift_spec_unique v 1 (by omega) (by decide)).1
    rw [hrec, hcongr39366 (parityWeight v) (canonicalSuffixShift v 1) hw_v ha_lt]
    exact hmem13122 ⟨canonicalSuffixShift v 1 % 13122, Nat.mod_lt _ (by decide)⟩
  have h512_quad : ∀ r : Fin 512, isSurvivingMod512Bool r.val = true ->
      (isTopWeight9SurvivingMod512Bool r.val = true ∧
       isExactWeight8SurvivingMod512Bool r.val = false ∧
       isMedWeight7SurvivingMod512Bool r.val = false ∧
       isLowWeight6SurvivingMod512Bool r.val = false) ∨
      (isExactWeight8SurvivingMod512Bool r.val = true ∧
       isTopWeight9SurvivingMod512Bool r.val = false ∧
       isMedWeight7SurvivingMod512Bool r.val = false ∧
       isLowWeight6SurvivingMod512Bool r.val = false) ∨
      (isMedWeight7SurvivingMod512Bool r.val = true ∧
       isTopWeight9SurvivingMod512Bool r.val = false ∧
       isExactWeight8SurvivingMod512Bool r.val = false ∧
       isLowWeight6SurvivingMod512Bool r.val = false) ∨
      (isLowWeight6SurvivingMod512Bool r.val = true ∧
       isTopWeight9SurvivingMod512Bool r.val = false ∧
       isExactWeight8SurvivingMod512Bool r.val = false ∧
       isMedWeight7SurvivingMod512Bool r.val = false) := by
    have hgrid : ∀ (hi : Fin 8) (lo : Fin 64),
        let rv := 64 * hi.val + lo.val
        isSurvivingMod512Bool rv = true ->
        (isTopWeight9SurvivingMod512Bool rv = true ∧
         isExactWeight8SurvivingMod512Bool rv = false ∧
         isMedWeight7SurvivingMod512Bool rv = false ∧
         isLowWeight6SurvivingMod512Bool rv = false) ∨
        (isExactWeight8SurvivingMod512Bool rv = true ∧
         isTopWeight9SurvivingMod512Bool rv = false ∧
         isMedWeight7SurvivingMod512Bool rv = false ∧
         isLowWeight6SurvivingMod512Bool rv = false) ∨
        (isMedWeight7SurvivingMod512Bool rv = true ∧
         isTopWeight9SurvivingMod512Bool rv = false ∧
         isExactWeight8SurvivingMod512Bool rv = false ∧
         isLowWeight6SurvivingMod512Bool rv = false) ∨
        (isLowWeight6SurvivingMod512Bool rv = true ∧
         isTopWeight9SurvivingMod512Bool rv = false ∧
         isExactWeight8SurvivingMod512Bool rv = false ∧
         isMedWeight7SurvivingMod512Bool rv = false) := by
      decide
    intro r hr
    have hhi : r.val / 64 < 8 := by have := r.isLt; omega
    have hlo : r.val % 64 < 64 := Nat.mod_lt r.val (by decide)
    have hg := hgrid ⟨r.val / 64, hhi⟩ ⟨r.val % 64, hlo⟩
    dsimp only at hg
    rw [Nat.div_add_mod r.val 64] at hg
    exact hg hr
  have hlen10_top9 : ∀ (u : List Bool) (q : Nat),
      IsCoreParityWord u -> u.length ≥ 10 ->
      isTopWeight9SurvivingMod512Bool (exactBackwardQuotient 1 u q) = true ->
      parityWeight u ≥ 10 ∧ canonicalSuffixShift u 1 % 39366 ∈ survivingMod39366List := by
    intro u q hu hlen10 htop
    rcases list_eq_append_true_of_reverse_head u hu.2 with ⟨pre, rfl⟩
    have hpre_ge9 : pre.length ≥ 9 := by
      rw [List.length_append, List.length_singleton] at hlen10; omega
    let p9 := pre.take 9
    let fb := pre.drop 9
    have hp9_len : p9.length = 9 := take_len_of_ge_w16 9 pre hpre_ge9
    have hpre_sp : p9 ++ fb = pre := take_drop_split_eq_w16 9 pre
    have hu' : IsCoreParityWord (p9 ++ fb ++ [true]) := by rwa [hpre_sp]
    have hp9_eq : parityOfIter 9 (exactBackwardQuotient 1 (p9 ++ fb ++ [true]) q % 512) = p9 :=
      len10_core_mod512_prefix9_w16 p9 fb q hp9_len hu'
    rw [hpre_sp] at hp9_eq
    unfold isTopWeight9SurvivingMod512Bool at htop
    simp only [Bool.and_eq_true, decide_eq_true_eq] at htop
    have htop2 := htop.2
    have hw_p9 : parityWeight p9 = 9 := by rwa [hp9_eq] at htop2
    have hw10 : parityWeight (pre ++ [true]) ≥ 10 := by
      rw [← hpre_sp, parityWeight_append, parityWeight_append]
      have h1 : parityWeight [true] = 1 := rfl
      rw [h1]; omega
    exact ⟨hw10, hconf10 (pre ++ [true]) hu hw10⟩
  have hesc9_cert :
      let u_esc9 : List Bool :=
        [true, true, true, false, true, true, true, true, true] ++
          List.replicate 42 false ++ [true]
      u_esc9.length = 52 ∧
      parityWeight u_esc9 = 9 ∧
      IsFirstHitOnePair u_esc9 0 ∧
      exactBackwardQuotient 1 u_esc9 0 = 145023390002129744557057965701200958845287 ∧
      IsSurvivingMod373248Class (exactBackwardQuotient 1 u_esc9 0) ∧
      isExactWeight8SurvivingMod512Bool (exactBackwardQuotient 1 u_esc9 0) = true := by
    dsimp only
    let u_esc9 : List Bool :=
      [true, true, true, false, true, true, true, true, true] ++
        List.replicate 42 false ++ [true]
    have hsh99 : canonicalSuffixShift u_esc9 1 = 99 := by
      rcases canonicalSuffixShift_spec_unique u_esc9 1 (by decide) (by decide) with ⟨_, _, huniq⟩
      symm
      apply huniq 99 (by decide)
      decide
    have hfh_esc : IsFirstHitOnePair u_esc9 0 :=
      (first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.2 u_esc9 ⟨rfl, rfl⟩).mpr
        (by rw [hsh99]; decide)
    have hq_val : exactBackwardQuotient 1 u_esc9 0 = 145023390002129744557057965701200958845287 := by
      unfold exactBackwardQuotient
      dsimp only
      rw [hsh99]
      decide
    have hb_surv : isSurvivingMod373248Bool 145023390002129744557057965701200958845287 = true := by decide
    have hex8_b : isExactWeight8SurvivingMod512Bool 145023390002129744557057965701200958845287 = true := by decide
    rw [hq_val]
    exact ⟨rfl, rfl, hfh_esc, rfl, isSurvivingMod373248Bool_imp_class _ hb_surv, hex8_b⟩
  refine ⟨⟨hcongr39366, hlen39366, hinj13122, hmem13122, hsurj13122⟩,
          ⟨rfl, rfl, rfl, rfl, h512_quad, hconf10, hlen10_top9, hesc9_cert⟩, ⟨?_, ?_⟩, ?_⟩
  · intro pref
    have hm13122 := first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.1 9 pref (by decide)
    change canonicalSuffixShift (pref ++ List.replicate 9 true) 1 % 13122 = 6561 at hm13122
    let A := canonicalSuffixShift (pref ++ List.replicate 9 true) 1 % 39366
    have hA_lt : A < 39366 := Nat.mod_lt _ (by decide)
    have hA_m13122 : A % 13122 = 6561 := by
      dsimp only [A]
      rw [Nat.mod_mod_of_dvd _ ⟨3, by decide⟩]
      exact hm13122
    have hdm := (Nat.div_add_mod A 13122).symm
    change A = 6561 ∨ A = 19683 ∨ A = 32805
    omega
  · intro pref
    have ha1 := first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.1 10 pref (by decide)
    let u11 : List Bool := [true, false] ++ List.replicate 9 true
    have ha2 := canonicalSuffixShift_mod18_and_pow3_memory_annihilation.2.1 9 pref u11 (by decide)
    have hu11_sh : canonicalSuffixShift u11 1 = 6561 := by
      rcases canonicalSuffixShift_spec_unique u11 1 (by decide) (by decide) with ⟨_, _, huniq⟩
      symm
      apply huniq 6561 (by decide)
      have hlen11 : u11.length = 11 := rfl
      have hwt10 : parityWeight u11 = 10 := rfl
      rw [Nat.mul_one, hlen11, hwt10, show (3 : Nat) ^ 10 = 59049 from rfl,
          show 11 + 6561 = 11 + 81 * 81 from rfl, Nat.pow_add 2 11 (81 * 81),
          ← pow_pow_eq_mul_w5 2 81 81, Nat.mul_mod, pow_mod_eq_pow_mod_w16 (2 ^ 81) 59049 81]
      decide
    have hv2 : canonicalSuffixShift u11 1 % 39366 = 6561 := by rw [hu11_sh]
    exact ⟨by simpa using ha1, by simpa [u11] using ha2.trans hv2⟩
  · intro tail w r0 hw10 hr0
    have hm39366 : (2 : Nat) * 3 ^ 9 = 39366 := by decide
    have hw_sub : w - 1 - 9 = w - 10 := by omega
    have heq := markovShift_mod18_bijection_and_multistep_fiber_equidistribution.2.2
      tail 9 w r0 (by omega) (by rw [hm39366]; exact hr0)
    dsimp only at heq ⊢
    rwa [hm39366, hw_sub] at heq


-- ----------------------------------------------------------------------------
-- Section 3B: Constructive Digit-by-Digit Mod-`9` Ternary-Carry-Lifted Family
--             `uWinExp B M mask` & Unconditional True Exponential (`≥ 2 ^ B`,
--             `≥ 2 ^ ((M - 6377332) / 8)`) Surviving-Leaf Dyadic-Window Occupancy
--             at Linear Horizon `L_max ≥ M` (`W16_H4`)
-- ----------------------------------------------------------------------------

/-- Exact 1-step mod-9 ternary carry selector (`2^6 ≡ 1 (mod 9)`):
    Given `rem9` (`rem9 % 3 ≠ 0`), `exp6` (`< 6`), and `bit` (`0` or `1`), selects the unique
    shift `step ∈ {3, 4, 5, 6, 7, 8}` such that
    `(rem9 + 9 - (2 ^ ((exp6 + 12 - step) % 6)) % 9) % 9 = if bit % 2 = 0 then 3 else 6`. -/
def chooseTernaryCarryStep (rem9 exp6 bit : Nat) : Nat :=
  let tgt := if bit % 2 = 0 then 3 else 6
  if (rem9 + 9 - (2 ^ ((exp6 + 12 - 3) % 6)) % 9) % 9 = tgt then 3
  else if (rem9 + 9 - (2 ^ ((exp6 + 12 - 4) % 6)) % 9) % 9 = tgt then 4
  else if (rem9 + 9 - (2 ^ ((exp6 + 12 - 5) % 6)) % 9) % 9 = tgt then 5
  else if (rem9 + 9 - (2 ^ ((exp6 + 12 - 6) % 6)) % 9) % 9 = tgt then 6
  else if (rem9 + 9 - (2 ^ ((exp6 + 12 - 7) % 6)) % 9) % 9 = tgt then 7
  else 8

/-- Top-down `k`-step mod-9 ternary carry-lifting chain starting from `(e_cur, R_cur)` and `mask`:
    Returns `(e_final, R_final, gaps)` where `gaps = [st_{k-1} - 1, ..., st_0 - 1]`. -/
def ternaryCarryChain : Nat -> Nat -> Nat -> Nat -> (Nat × Nat × List Nat)
  | 0, e_cur, R_cur, _ => (e_cur, R_cur, [])
  | k + 1, e_cur, R_cur, mask =>
    let st := chooseTernaryCarryStep (R_cur % 9) (e_cur % 6) (mask % 2)
    let e_nxt := e_cur - st
    let R_nxt := (R_cur - 2 ^ e_nxt) / 3
    let sub := ternaryCarryChain k e_nxt R_nxt (mask / 2)
    (sub.1, sub.2.1, sub.2.2 ++ [st - 1])

/-- Compressed linear minimum dyadic window scale `M_min(B) = 6377332 + 8 * B`
    (`= 2 * (2 * 3 ^ 13) + 40 + 8 * B`) above which `[2^M, 2^(M+1))` contains at least `2 ^ B`
    surviving `Mod373248` first-hit `q = 0` leaves at linear horizon `L_max ≥ M`. -/
def dyadicExpWindowMinM (B : Nat) : Nat :=
  6377332 + 8 * B

/-- Zero-run length list `(p_last - 9) :: (e_B - (p_last + 1)) :: gaps` for `uWinExp B M mask`. -/
def uWinExpRuns (B M mask : Nat) : List Nat :=
  let w := B + 11
  let b0 := binBitLength (3 ^ w)
  let delta := dyadicPolyShiftDelta b0
  let a := b0 + delta
  let q3 := (2 ^ (a + 1) - 1) / 3
  let L := M - delta
  let chain := ternaryCarryChain B (L - 1) (q3 * 2 ^ (L - 1)) mask
  let e_fin := chain.1
  let R_fin := chain.2.1
  let gaps := chain.2.2
  let A_last := R_fin - (3 * 19171 + 3 ^ 10)
  let t_base := dlog2ModPow3 14 (A_last % 3 ^ 14)
  let p_last := 3188646 + t_base
  (p_last - 9) :: (e_fin - (p_last + 1)) :: gaps

/-- Constructive digit-by-digit mod-`9` ternary-carry-lifted surviving `Mod373248` first-hit
    `q = 0` family `uWinExp B M mask` inside `[2^M, 2^(M+1))` at linear length `L = M - delta ≤ M`
    and parity weight `w = B + 11` (`∀ B ≥ 1, ∀ mask < 2 ^ B`). -/
def uWinExp (B M mask : Nat) : List Bool :=
  List.replicate 9 true ++ zeroRunsSuffix (uWinExpRuns B M mask)

private theorem chooseTernaryCarryStep_fin_spec :
    ∀ (r : Fin 9), r.val % 3 ≠ 0 -> ∀ (e : Fin 6) (b : Fin 2),
      let st := chooseTernaryCarryStep r.val e.val b.val
      3 ≤ st ∧ st ≤ 8 ∧
      (r.val + 9 - (2 ^ ((e.val + 12 - st) % 6)) % 9) % 9 = (if b.val = 0 then 3 else 6) ∧
      chooseTernaryCarryStep r.val e.val 0 ≠ chooseTernaryCarryStep r.val e.val 1 := by
  decide

private theorem pow2_mod9_period6_w16 (n : Nat) :
    2 ^ n % 9 = 2 ^ (n % 6) % 9 := by
  have hp6 : ∀ q : Nat, 2 ^ (6 * q) % 9 = 1 := by
    intro q; induction q with
    | zero => rfl
    | succ q' ih => rw [Nat.mul_succ 6 q', Nat.pow_add 2 (6 * q') 6, Nat.mul_mod, ih]
  conv => lhs; rw [(Nat.div_add_mod n 6).symm]
  rw [Nat.pow_add 2 (6 * (n / 6)) (n % 6), Nat.mul_mod, hp6 (n / 6), Nat.one_mul, Nat.mod_mod]

private theorem sub_mod9_of_le_w16 (R U : Nat) (hUR : U ≤ R) :
    (R - U) % 9 = (R % 9 + 9 - U % 9) % 9 := by
  have hR := (Nat.div_add_mod R 9).symm
  have hU := (Nat.div_add_mod U 9).symm
  omega

private theorem chooseTernaryCarryStep_nat_step_w16 (R e bit : Nat)
    (hR3 : R % 3 ≠ 0) (he8 : e ≥ 8) (hpow_le : 2 ^ (e - chooseTernaryCarryStep (R % 9) (e % 6) (bit % 2)) ≤ R) :
    let st := chooseTernaryCarryStep (R % 9) (e % 6) (bit % 2)
    let e_nxt := e - st
    let R_nxt := (R - 2 ^ e_nxt) / 3
    3 ≤ st ∧ st ≤ 8 ∧
    3 * R_nxt + 2 ^ e_nxt = R ∧
    R_nxt % 3 ≠ 0 ∧
    (∀ b1 b2 : Nat, b1 < 2 -> b2 < 2 ->
      chooseTernaryCarryStep (R % 9) (e % 6) b1 = chooseTernaryCarryStep (R % 9) (e % 6) b2 ->
      b1 = b2) := by
  dsimp only
  have hr9_lt : R % 9 < 9 := Nat.mod_lt R (by decide)
  have hr9_3 : (R % 9) % 3 ≠ 0 := by rw [Nat.mod_mod_of_dvd R ⟨3, by decide⟩]; exact hR3
  have he6_lt : e % 6 < 6 := Nat.mod_lt e (by decide)
  have hb2_lt : bit % 2 < 2 := Nat.mod_lt bit (by decide)
  rcases chooseTernaryCarryStep_fin_spec ⟨R % 9, hr9_lt⟩ hr9_3 ⟨e % 6, he6_lt⟩ ⟨bit % 2, hb2_lt⟩ with
    ⟨hst3, hst8, hmod9_eq, hne01⟩
  dsimp only at hst3 hst8 hmod9_eq hne01
  let st := chooseTernaryCarryStep (R % 9) (e % 6) (bit % 2)
  change 3 ≤ st at hst3; change st ≤ 8 at hst8
  have hexp_m6 : (e - st) % 6 = (e % 6 + 12 - st) % 6 := by
    have he_dm := (Nat.div_add_mod e 6).symm
    omega
  have hu_m9 : 2 ^ (e - st) % 9 = 2 ^ ((e % 6 + 12 - st) % 6) % 9 := by
    rw [pow2_mod9_period6_w16 (e - st), hexp_m6]
  have hdiff_m9 : (R - 2 ^ (e - st)) % 9 = (if bit % 2 = 0 then 3 else 6) := by
    rw [sub_mod9_of_le_w16 R (2 ^ (e - st)) hpow_le, hu_m9]
    exact hmod9_eq
  have hd_dm := (Nat.div_add_mod (R - 2 ^ (e - st)) 9).symm
  change 2 ^ (e - st) ≤ R at hpow_le
  refine ⟨hst3, hst8, ?_, ?_, ?_⟩
  · change 3 * ((R - 2 ^ (e - st)) / 3) + 2 ^ (e - st) = R
    by_cases hb0 : bit % 2 = 0 <;>
    (simp only [hb0, ite_true, ite_false] at hdiff_m9;
     generalize 2 ^ (e - st) = U at hpow_le hdiff_m9 hd_dm ⊢; omega)
  · change ((R - 2 ^ (e - st)) / 3) % 3 ≠ 0
    by_cases hb0 : bit % 2 = 0 <;>
    (simp only [hb0, ite_true, ite_false] at hdiff_m9;
     generalize 2 ^ (e - st) = U at hpow_le hdiff_m9 hd_dm ⊢; omega)
  · intro b1 b2 hb1 hb2 heq
    rcases (by omega : b1 = 0 ∨ b1 = 1) with rfl | rfl <;>
    rcases (by omega : b2 = 0 ∨ b2 = 1) with rfl | rfl
    · rfl
    · exact False.elim (hne01 heq)
    · exact False.elim (hne01 heq.symm)
    · rfl

private theorem list_append_singleton_inj_w16 {α : Type} :
    ∀ (xs ys : List α) (a b : α), xs ++ [a] = ys ++ [b] -> xs = ys ∧ a = b
  | [], [], a, b, h => ⟨rfl, by simpa using h⟩
  | [], y :: ys, a, b, h => by
    exfalso; have hlen := congrArg List.length h; simp at hlen
  | x :: xs, [], a, b, h => by
    exfalso; have hlen := congrArg List.length h; simp at hlen
  | x :: xs, y :: ys, a, b, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    rcases list_append_singleton_inj_w16 xs ys a b h.2 with ⟨hxy, hab⟩
    exact ⟨by rw [h.1, hxy], hab⟩

private theorem replicate_false_cons_true_inj_w16 :
    ∀ (a b : Nat) (xs ys : List Bool),
      List.replicate a false ++ (true :: xs) = List.replicate b false ++ (true :: ys) ->
      a = b ∧ xs = ys
  | 0, 0, xs, ys, h => ⟨rfl, by simpa using h⟩
  | 0, _ + 1, _, _, h => by simp [List.replicate_succ] at h
  | _ + 1, 0, _, _, h => by simp [List.replicate_succ] at h
  | a + 1, b + 1, xs, ys, h => by
    simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
    rcases replicate_false_cons_true_inj_w16 a b xs ys h with ⟨hab, hxy⟩
    exact ⟨congrArg Nat.succ hab, hxy⟩

private theorem zeroRunsSuffix_append_and_inj_w16 :
    (∀ xs ys : List Nat, zeroRunsSuffix (xs ++ ys) = zeroRunsSuffix xs ++ zeroRunsSuffix ys) ∧
    (∀ xs ys : List Nat, zeroRunsSuffix xs = zeroRunsSuffix ys -> xs = ys) := by
  have happ : ∀ xs ys : List Nat, zeroRunsSuffix (xs ++ ys) = zeroRunsSuffix xs ++ zeroRunsSuffix ys := by
    intro xs; induction xs with
    | nil => intro ys; rfl
    | cons k tl ih =>
      intro ys; simp only [List.cons_append, zeroRunsSuffix, ih ys, List.append_assoc]
  have hinj : ∀ xs ys : List Nat, zeroRunsSuffix xs = zeroRunsSuffix ys -> xs = ys := by
    intro xs; induction xs with
    | nil =>
      intro ys h; cases ys with
      | nil => rfl
      | cons k tl => exfalso; have hlen := congrArg List.length h; simp [zeroRunsSuffix] at hlen
    | cons k1 tl1 ih =>
      intro ys h; cases ys with
      | nil => exfalso; have hlen := congrArg List.length h; simp [zeroRunsSuffix] at hlen
      | cons k2 tl2 =>
        simp only [zeroRunsSuffix] at h
        rcases replicate_false_cons_true_inj_w16 k1 k2 _ _ h with ⟨hk, htl⟩
        rw [hk, ih tl2 htl]
  exact ⟨happ, hinj⟩

private theorem zeroRunsSuffix_nonempty_eq_mid_true_w16 :
    ∀ (k : Nat) (ks : List Nat), ∃ mid : List Bool, zeroRunsSuffix (k :: ks) = mid ++ [true]
  | k, [] => ⟨List.replicate k false, by simp [zeroRunsSuffix]⟩
  | k, k2 :: tl => by
    rcases zeroRunsSuffix_nonempty_eq_mid_true_w16 k2 tl with ⟨mid_tl, htl⟩
    refine ⟨List.replicate k false ++ [true] ++ mid_tl, ?_⟩
    simp only [zeroRunsSuffix] at htl ⊢
    rw [htl]
    simp [List.append_assoc]

private theorem ternaryCarryChain_spec_and_inj_w16 :
    ∀ (k e_cur R_cur L1 : Nat),
      e_cur ≤ L1 ->
      e_cur ≥ 8 * k + 8 ->
      R_cur % 3 ≠ 0 ->
      R_cur ≥ (2 * 3 ^ (k + 10) - 1) * 2 ^ L1 ->
      (∀ mask : Nat,
        let ch := ternaryCarryChain k e_cur R_cur mask
        let e_fin := ch.1
        let R_fin := ch.2.1
        let gaps := ch.2.2
        e_cur - 8 * k ≤ e_fin ∧ e_fin ≤ e_cur ∧
        gaps.length = k ∧
        R_fin % 3 ≠ 0 ∧
        R_fin ≥ (2 * 3 ^ 10 - 1) * 2 ^ L1 ∧
        (∀ (acc : List Bool) (Q1 : Nat),
          acc.length = e_fin + 1 ->
          affineCarry acc < 2 ^ (e_fin + 1) ->
          3 * R_fin + 2 ^ e_fin = 3 * Q1 + affineCarry acc ->
          let w_out := acc ++ zeroRunsSuffix gaps
          w_out.length = e_cur + 1 ∧
          parityWeight w_out = parityWeight acc + k ∧
          affineCarry w_out < 2 ^ (e_cur + 1) ∧
          3 * R_cur + 2 ^ e_cur = 3 ^ (k + 1) * Q1 + affineCarry w_out)) ∧
      (∀ m1 m2 : Nat, m1 < 2 ^ k -> m2 < 2 ^ k ->
        (ternaryCarryChain k e_cur R_cur m1).2.2 = (ternaryCarryChain k e_cur R_cur m2).2.2 ->
        m1 = m2) := by
  intro k; induction k with
  | zero =>
    intro e_cur R_cur L1 _ _ hR3 hR_lo
    refine ⟨?_, ?_⟩
    · intro mask; dsimp only [ternaryCarryChain]
      refine ⟨by omega, Nat.le_refl _, rfl, hR3, by simpa using hR_lo, ?_⟩
      intro acc Q1 hlen hcar heq
      rw [zeroRunsSuffix, List.append_nil, Nat.pow_one]
      exact ⟨hlen, by omega, hcar, heq⟩
    · intro m1 m2 h1 h2 _
      rw [Nat.pow_zero] at h1 h2; omega
  | succ k' ih =>
    intro e_cur R_cur L1 he_L1 he_8k hR3 hR_lo
    have hpow_le_R : ∀ bit : Nat,
        2 ^ (e_cur - chooseTernaryCarryStep (R_cur % 9) (e_cur % 6) (bit % 2)) ≤ R_cur := by
      intro bit
      have h1 : 2 ^ (e_cur - chooseTernaryCarryStep (R_cur % 9) (e_cur % 6) (bit % 2)) ≤ 2 ^ L1 :=
        pow2_mono_nat (by omega)
      have h3_pos : 2 * 3 ^ ((k' + 1) + 10) - 1 ≥ 1 := by
        have hp := pow3_pos_nat ((k' + 1) + 10); omega
      have h2 : 1 * 2 ^ L1 ≤ (2 * 3 ^ ((k' + 1) + 10) - 1) * 2 ^ L1 :=
        Nat.mul_le_mul_right _ h3_pos
      rw [Nat.one_mul] at h2
      exact Nat.le_trans h1 (Nat.le_trans h2 hR_lo)
    refine ⟨?_, ?_⟩
    · intro mask
      rcases chooseTernaryCarryStep_nat_step_w16 R_cur e_cur (mask % 2)
        hR3 (by omega) (by rw [Nat.mod_mod]; exact hpow_le_R mask) with
        ⟨hst3, hst8, h3Rnxt, hRnxt_3, _⟩
      rw [Nat.mod_mod] at hst3 hst8 h3Rnxt hRnxt_3
      let st := chooseTernaryCarryStep (R_cur % 9) (e_cur % 6) (mask % 2)
      let e_nxt := e_cur - st
      let R_nxt := (R_cur - 2 ^ e_nxt) / 3
      change 3 ≤ st at hst3; change st ≤ 8 at hst8
      change 3 * R_nxt + 2 ^ e_nxt = R_cur at h3Rnxt
      change R_nxt % 3 ≠ 0 at hRnxt_3
      have hRnxt_lo : R_nxt ≥ (2 * 3 ^ (k' + 10) - 1) * 2 ^ L1 := by
        let P3 := 3 ^ (k' + 10)
        have hP3_pos : P3 ≥ 1 := pow3_pos_nat (k' + 10)
        have hp_sp : 3 ^ ((k' + 1) + 10) = 3 * P3 := by
          dsimp [P3]; rw [show (k' + 1) + 10 = (k' + 10) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
        have hR_sp : R_cur ≥ (6 * P3 - 1) * 2 ^ L1 := by
          rw [hp_sp, show 2 * (3 * P3) = 6 * P3 by omega] at hR_lo; exact hR_lo
        have h2e_le : 2 ^ e_nxt ≤ 2 ^ L1 := pow2_mono_nat (by dsimp [e_nxt]; omega)
        let B_lo := (2 * P3 - 1) * 2 ^ L1
        have h3Blo : 3 * B_lo + 2 ^ L1 ≤ 3 * R_nxt + 2 ^ L1 := by
          calc 3 * B_lo + 2 ^ L1
              = (3 * (2 * P3 - 1) + 1) * 2 ^ L1 := by
                  dsimp [B_lo]; rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
            _ = (6 * P3 - 2) * 2 ^ L1 := by rw [show 3 * (2 * P3 - 1) + 1 = 6 * P3 - 2 by omega]
            _ ≤ (6 * P3 - 1) * 2 ^ L1 := Nat.mul_le_mul_right _ (by omega)
            _ ≤ R_cur := hR_sp
            _ = 3 * R_nxt + 2 ^ e_nxt := h3Rnxt.symm
            _ ≤ 3 * R_nxt + 2 ^ L1 := Nat.add_le_add_left h2e_le _
        change B_lo ≤ R_nxt; omega
      rcases (ih e_nxt R_nxt L1 (by dsimp [e_nxt]; omega) (by dsimp [e_nxt]; omega)
        hRnxt_3 hRnxt_lo).1 (mask / 2) with
        ⟨he_lo, he_hi, hlen_sub, hRfin_3, hRfin_lo, hunwind_sub⟩
      let ch_sub := ternaryCarryChain k' e_nxt R_nxt (mask / 2)
      change e_nxt - 8 * k' ≤ ch_sub.1 at he_lo
      change ch_sub.1 ≤ e_nxt at he_hi
      change ch_sub.2.2.length = k' at hlen_sub
      simp only [ternaryCarryChain]
      change e_cur - 8 * (k' + 1) ≤ ch_sub.1 ∧ ch_sub.1 ≤ e_cur ∧
        (ch_sub.2.2 ++ [st - 1]).length = k' + 1 ∧
        ch_sub.2.1 % 3 ≠ 0 ∧ ch_sub.2.1 ≥ (2 * 3 ^ 10 - 1) * 2 ^ L1 ∧ _
      refine ⟨by dsimp [e_nxt] at he_lo; omega,
              by dsimp [e_nxt] at he_hi; omega,
              by rw [List.length_append, hlen_sub, List.length_singleton],
              hRfin_3, hRfin_lo, ?_⟩
      intro acc Q1 hacc_len hacc_car hacc_eq
      rcases hunwind_sub acc Q1 hacc_len hacc_car hacc_eq with
        ⟨hw_len, hw_wt, hw_car, hw_eq⟩
      let w_sub := acc ++ zeroRunsSuffix ch_sub.2.2
      change w_sub.length = e_nxt + 1 at hw_len
      change parityWeight w_sub = parityWeight acc + k' at hw_wt
      change affineCarry w_sub < 2 ^ (e_nxt + 1) at hw_car
      change 3 * R_nxt + 2 ^ e_nxt = 3 ^ (k' + 1) * Q1 + affineCarry w_sub at hw_eq
      rw [h3Rnxt] at hw_eq
      have hw_out_eq : acc ++ zeroRunsSuffix (ch_sub.2.2 ++ [st - 1]) =
          (w_sub ++ List.replicate (st - 1) false) ++ [true] := by
        rw [zeroRunsSuffix_append_and_inj_w16.1 ch_sub.2.2 [st - 1]]
        dsimp only [zeroRunsSuffix, w_sub]
        simp [List.append_assoc]
      rw [hw_out_eq]
      rcases affineCarry_append_replicate_false w_sub (st - 1) with ⟨hwt_z, hcar_z⟩
      have hlen_z : (w_sub ++ List.replicate (st - 1) false).length = e_cur := by
        rw [List.length_append, hw_len, List.length_replicate]; dsimp [e_nxt]; omega
      have hlen_out : ((w_sub ++ List.replicate (st - 1) false) ++ [true]).length = e_cur + 1 := by
        rw [List.length_append, hlen_z, List.length_singleton]
      have hwt_out : parityWeight ((w_sub ++ List.replicate (st - 1) false) ++ [true]) =
          parityWeight acc + (k' + 1) := by
        rw [parityWeight_append, hwt_z, hw_wt]
        have h1 : parityWeight [true] = 1 := rfl
        rw [h1]; omega
      have hcar_out : affineCarry ((w_sub ++ List.replicate (st - 1) false) ++ [true]) =
          3 * affineCarry w_sub + 2 ^ e_cur := by
        rw [affineCarry_append, hcar_z, hlen_z]
        have hc1 : affineCarry [true] = 1 := rfl
        have hw1 : parityWeight [true] = 1 := rfl
        rw [hc1, hw1]; omega
      have hcar_lt : affineCarry ((w_sub ++ List.replicate (st - 1) false) ++ [true]) <
          2 ^ (e_cur + 1) := by
        rw [hcar_out]
        have he_le : e_nxt + 1 ≤ e_cur - 2 := by dsimp [e_nxt]; omega
        have hc_le : affineCarry w_sub < 2 ^ (e_cur - 2) :=
          Nat.lt_of_lt_of_le hw_car (pow2_mono_nat he_le)
        have hp_e : 2 ^ e_cur = 4 * 2 ^ (e_cur - 2) := by
          conv => lhs; rw [show e_cur = 2 + (e_cur - 2) by omega, Nat.pow_add]
        have hp_e1 : 2 ^ (e_cur + 1) = 8 * 2 ^ (e_cur - 2) := by
          conv => lhs; rw [show e_cur + 1 = 3 + (e_cur - 2) by omega, Nat.pow_add]
        rw [hp_e, hp_e1]
        generalize 2 ^ (e_cur - 2) = Z at hc_le ⊢; omega
      have hkey_out : 3 * R_cur + 2 ^ e_cur =
          3 ^ (k' + 1 + 1) * Q1 + affineCarry ((w_sub ++ List.replicate (st - 1) false) ++ [true]) := by
        rw [hcar_out, hw_eq, Nat.mul_add 3 (3 ^ (k' + 1) * Q1) (affineCarry w_sub),
            ← Nat.mul_assoc 3 (3 ^ (k' + 1)) Q1,
            show 3 * 3 ^ (k' + 1) = 3 ^ (k' + 1 + 1) by rw [Nat.pow_succ 3 (k' + 1), Nat.mul_comm],
            Nat.add_assoc]
      exact ⟨hlen_out, hwt_out, hcar_lt, hkey_out⟩
    · intro m1 m2 hm1 hm2 hgaps_eq
      rcases chooseTernaryCarryStep_nat_step_w16 R_cur e_cur (m1 % 2)
        hR3 (by omega) (by rw [Nat.mod_mod]; exact hpow_le_R m1) with
        ⟨hst1_3, hst1_8, h3R1, hR1_3, hbit_inj⟩
      rcases chooseTernaryCarryStep_nat_step_w16 R_cur e_cur (m2 % 2)
        hR3 (by omega) (by rw [Nat.mod_mod]; exact hpow_le_R m2) with
        ⟨hst2_3, _, _, _, _⟩
      rw [Nat.mod_mod] at hst1_3 hst1_8 h3R1 hR1_3 hst2_3
      let st1 := chooseTernaryCarryStep (R_cur % 9) (e_cur % 6) (m1 % 2)
      let st2 := chooseTernaryCarryStep (R_cur % 9) (e_cur % 6) (m2 % 2)
      change 3 ≤ st1 at hst1_3; change st1 ≤ 8 at hst1_8; change 3 ≤ st2 at hst2_3
      simp only [ternaryCarryChain] at hgaps_eq
      rcases list_append_singleton_inj_w16 _ _ _ _ hgaps_eq with ⟨hsub_eq, hst_sub⟩
      have hst_eq : st1 = st2 := by
        change _ = _ at hst_sub
        have h : st1 - 1 = st2 - 1 := hst_sub
        omega
      have hmod2_eq : m1 % 2 = m2 % 2 :=
        hbit_inj (m1 % 2) (m2 % 2) (Nat.mod_lt m1 (by decide)) (Nat.mod_lt m2 (by decide)) hst_eq
      let e_nxt := e_cur - st1
      let R_nxt := (R_cur - 2 ^ e_nxt) / 3
      change 3 * R_nxt + 2 ^ e_nxt = R_cur at h3R1
      change R_nxt % 3 ≠ 0 at hR1_3
      -- Rewrite `st2` to `st1` inside `hsub_eq`:
      have hsub_same : (ternaryCarryChain k' e_nxt R_nxt (m1 / 2)).2.2 =
          (ternaryCarryChain k' e_nxt R_nxt (m2 / 2)).2.2 := by
        dsimp only [st1, st2] at hst_eq
        simpa [e_nxt, R_nxt, st1, hst_eq] using hsub_eq
      have hRnxt_lo : R_nxt ≥ (2 * 3 ^ (k' + 10) - 1) * 2 ^ L1 := by
        let P3 := 3 ^ (k' + 10)
        have hP3_pos : P3 ≥ 1 := pow3_pos_nat (k' + 10)
        have hp_sp : 3 ^ ((k' + 1) + 10) = 3 * P3 := by
          dsimp [P3]; rw [show (k' + 1) + 10 = (k' + 10) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
        have hR_sp : R_cur ≥ (6 * P3 - 1) * 2 ^ L1 := by
          rw [hp_sp, show 2 * (3 * P3) = 6 * P3 by omega] at hR_lo; exact hR_lo
        have h2e_le : 2 ^ e_nxt ≤ 2 ^ L1 := pow2_mono_nat (by dsimp [e_nxt]; omega)
        let B_lo := (2 * P3 - 1) * 2 ^ L1
        have h3Blo : 3 * B_lo + 2 ^ L1 ≤ 3 * R_nxt + 2 ^ L1 := by
          calc 3 * B_lo + 2 ^ L1
              = (3 * (2 * P3 - 1) + 1) * 2 ^ L1 := by
                  dsimp [B_lo]; rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
            _ = (6 * P3 - 2) * 2 ^ L1 := by rw [show 3 * (2 * P3 - 1) + 1 = 6 * P3 - 2 by omega]
            _ ≤ (6 * P3 - 1) * 2 ^ L1 := Nat.mul_le_mul_right _ (by omega)
            _ ≤ R_cur := hR_sp
            _ = 3 * R_nxt + 2 ^ e_nxt := h3R1.symm
            _ ≤ 3 * R_nxt + 2 ^ L1 := Nat.add_le_add_left h2e_le _
        change B_lo ≤ R_nxt; omega
      have hdiv_lt : ∀ m : Nat, m < 2 ^ (k' + 1) -> m / 2 < 2 ^ k' := by
        intro m hm; rw [Nat.pow_succ] at hm; omega
      have hdiv_eq : m1 / 2 = m2 / 2 :=
        (ih e_nxt R_nxt L1 (by dsimp [e_nxt]; omega) (by dsimp [e_nxt]; omega)
          hR1_3 hRnxt_lo).2 (m1 / 2) (m2 / 2) (hdiv_lt m1 hm1) (hdiv_lt m2 hm2) hsub_same
      have hdm1 := (Nat.div_add_mod m1 2).symm
      have hdm2 := (Nat.div_add_mod m2 2).symm
      rw [hdiv_eq, hmod2_eq] at hdm1
      omega

private theorem binBitLength_pow2_sandwich_w16 :
    ∀ (fuel n : Nat), n ≥ 1 -> n ≤ fuel ->
      binBitLength n ≥ 1 ∧ 2 ^ (binBitLength n - 1) ≤ n ∧ n < 2 ^ binBitLength n
  | 0, _, hn, hle => by omega
  | fuel + 1, n, hn, hle => by
    by_cases hn1 : n = 1
    · subst hn1; decide
    · let k := n / 2
      have hk_pos : k ≥ 1 := by dsimp [k]; omega
      have hbl_n : binBitLength n = 1 + binBitLength k := binBitLength_step_pos n hn
      rcases binBitLength_pow2_sandwich_w16 fuel k hk_pos (by dsimp [k]; omega) with
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

private theorem pow3_bitlength_strict_bounds_w16 (w : Nat) (hw : w ≥ 11) :
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
          | succ _ =>
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
  rcases binBitLength_pow2_sandwich_w16 (3 ^ w) (3 ^ w) (by omega) (Nat.le_refl _) with
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

private theorem dyadicPolyShiftDelta_spec_w16 (b0 : Nat) :
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
  have hpE_m9 : 2 ^ E % 9 = 4 ∨ 2 ^ E % 9 = 7 := by
    rw [pow2_mod9_period6_w16 E]
    rcases hd_mod6.2 with h2 | h4
    · left; rw [h2]
    · right; rw [h4]
  have hpE_ge4 : 2 ^ E ≥ 4 := by
    have hE2 : E ≥ 2 := by have := hd_mod6.2; omega
    simpa using pow2_mono_nat hE2
  rw [hE_eq]
  have hdm9 := (Nat.div_add_mod (2 ^ E) 9).symm
  refine ⟨hd_mod6.1, ?_, ?_, ?_⟩
  · rcases hpE_m9 with h4 | h7 <;> omega
  · rcases hpE_m9 with h4 | h7 <;> omega
  · omega

private theorem pow2_euler_pow3_mod_one_w16 :
    ∀ n : Nat, 3 ^ (n + 1) ∣ (2 ^ (2 * 3 ^ n) - 1)
  | 0 => ⟨1, by decide⟩
  | n + 1 => by
    rcases pow2_euler_pow3_mod_one_w16 n with ⟨q, hq⟩
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
      have hc : ∀ (p0 q0 : Nat),
          ((3 * p0) * q0 + 1) * ((3 * p0) * q0 + 1) * ((3 * p0) * q0 + 1) =
            (3 * (3 * p0)) * (q0 * (p0 * (3 * p0) * q0 * q0 + (3 * p0) * q0 + 1)) + 1 := by
        intro p0 q0
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
      exact hc (3 ^ n) q
    rw [hexp]; omega

private theorem pow2_add_period_mod_pow3_w16 (n t : Nat) :
    2 ^ (t + 2 * 3 ^ n) % 3 ^ (n + 1) = 2 ^ t % 3 ^ (n + 1) := by
  let P := 2 * 3 ^ n
  let M := 3 ^ (n + 1)
  have hM_ge3 : M ≥ 3 := by dsimp [M]; rw [Nat.pow_succ]; have := pow3_pos_nat n; omega
  have hp_one : 2 ^ P % M = 1 := by
    rcases pow2_euler_pow3_mod_one_w16 n with ⟨q, hq⟩
    have hp_pos := pow2_pos_nat (2 * 3 ^ n)
    have heq : 2 ^ P = 1 + M * q := by dsimp [P, M] at hq ⊢; omega
    rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  rw [Nat.pow_add 2 t P, Nat.mul_mod, hp_one, Nat.mul_one, Nat.mod_mod]

private theorem isSurvivingMod373248_of_511_and_1_w16 (y : Nat)
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

private def eraseAllNatW16 (b : Nat) : List Nat -> List Nat
  | [] => []
  | x :: xs => if x = b then eraseAllNatW16 b xs else x :: eraseAllNatW16 b xs

private theorem mem_eraseAllNatW16_iff (b : Nat) :
    ∀ (xs : List Nat) (v : Nat), v ∈ eraseAllNatW16 b xs ↔ (v ∈ xs ∧ v ≠ b)
  | [], _ => by simp [eraseAllNatW16]
  | x :: xs, v => by
    simp only [eraseAllNatW16]
    by_cases hxb : x = b
    · simp only [hxb, ite_true, mem_eraseAllNatW16_iff b xs v, List.mem_cons]
      exact ⟨fun ⟨hm, hne⟩ => ⟨Or.inr hm, hne⟩,
             fun ⟨h, hne⟩ => ⟨by rcases h with rfl | hm; { exact False.elim (hne rfl) }; exact hm, hne⟩⟩
    · simp only [hxb, ite_false, List.mem_cons, mem_eraseAllNatW16_iff b xs v]
      exact ⟨fun h => by rcases h with rfl | ⟨hm, hne⟩; { exact ⟨Or.inl rfl, hxb⟩ }; exact ⟨Or.inr hm, hne⟩,
             fun ⟨h, hne⟩ => by rcases h with rfl | hm; { exact Or.inl rfl }; exact Or.inr ⟨hm, hne⟩⟩

private theorem eraseAllNatW16_of_not_mem (b : Nat) :
    ∀ (xs : List Nat), b ∉ xs -> eraseAllNatW16 b xs = xs
  | [], _ => rfl
  | x :: xs, hnm => by
    have hxb : x ≠ b := fun h => hnm (h ▸ List.Mem.head _)
    have hnm_xs : b ∉ xs := fun hm => hnm (List.mem_cons_of_mem _ hm)
    simp only [eraseAllNatW16, hxb, ite_false, eraseAllNatW16_of_not_mem b xs hnm_xs]

private theorem nodup_eraseAllNatW16_and_len (b : Nat) :
    ∀ (xs : List Nat),
      NoDupNat xs -> NoDupNat (eraseAllNatW16 b xs) ∧ xs.length ≤ (eraseAllNatW16 b xs).length + 1
  | [], _ => ⟨NoDupNat.nil, by simp [eraseAllNatW16]⟩
  | x :: xs, NoDupNat.cons _ _ hnx hnd => by
    by_cases hxb : x = b
    · subst hxb
      simp only [eraseAllNatW16, ite_true, eraseAllNatW16_of_not_mem x xs hnx, List.length_cons]
      exact ⟨hnd, Nat.le_refl _⟩
    · rcases nodup_eraseAllNatW16_and_len b xs hnd with ⟨hnd_er, hlen_er⟩
      simp only [eraseAllNatW16, hxb, ite_false, List.length_cons]
      have hnx_er : x ∉ eraseAllNatW16 b xs :=
        fun hm => hnx ((mem_eraseAllNatW16_iff b xs x).mp hm).1
      exact ⟨NoDupNat.cons x _ hnx_er hnd_er, by omega⟩

private theorem noDupNat_length_le_of_subset_w16 :
    ∀ (cands xs : List Nat),
      NoDupNat xs -> (∀ y ∈ xs, y ∈ cands) -> xs.length ≤ cands.length
  | [], [], _, _ => Nat.le_refl 0
  | [], x :: _, _, hsub => by cases hsub x (List.Mem.head _)
  | b :: bs, xs, hnd, hsub => by
    rcases nodup_eraseAllNatW16_and_len b xs hnd with ⟨hnd', hlen'⟩
    have hsub' : ∀ y ∈ eraseAllNatW16 b xs, y ∈ bs := by
      intro y hy
      rcases (mem_eraseAllNatW16_iff b xs y).mp hy with ⟨hy_xs, hne⟩
      rcases List.mem_cons.mp (hsub y hy_xs) with rfl | hbs
      · exact False.elim (hne rfl)
      · exact hbs
    have ih := noDupNat_length_le_of_subset_w16 bs (eraseAllNatW16 b xs) hnd' hsub'
    simp only [List.length_cons]; omega

private def descIdxListW16 : Nat -> List Nat
  | 0 => []
  | r + 1 => r :: descIdxListW16 r

private theorem descIdxListW16_spec :
    ∀ r : Nat,
      (descIdxListW16 r).length = r ∧
      NoDupNat (descIdxListW16 r) ∧
      (∀ j ∈ descIdxListW16 r, j < r)
  | 0 => ⟨rfl, NoDupNat.nil, fun _ hm => by cases hm⟩
  | r + 1 => by
    rcases descIdxListW16_spec r with ⟨hlen, hnd, hlt⟩
    have hnot_mem : r ∉ descIdxListW16 r := fun hm => Nat.lt_irrefl r (hlt r hm)
    refine ⟨by simp [descIdxListW16, hlen], NoDupNat.cons r _ hnot_mem hnd, ?_⟩
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hm
    · omega
    · have := hlt j hm; omega

private theorem noDupNat_map_inj_on_w16 (f : Nat -> Nat) :
    ∀ (js : List Nat),
      NoDupNat js ->
      (∀ a ∈ js, ∀ b ∈ js, f a = f b -> a = b) ->
      NoDupNat (js.map f)
  | [], _, _ => NoDupNat.nil
  | j :: js, NoDupNat.cons _ _ hnj hnd, hinj => by
    refine NoDupNat.cons (f j) (js.map f) ?_
      (noDupNat_map_inj_on_w16 f js hnd (fun a ha b hb =>
        hinj a (List.mem_cons_of_mem j ha) b (List.mem_cons_of_mem j hb)))
    intro hm
    rcases List.mem_map.mp hm with ⟨j', hj', heq⟩
    have hj_eq := hinj j' (List.mem_cons_of_mem j hj') j (List.Mem.head _) heq
    exact hnj (hj_eq ▸ hj')

private theorem pow3_gt_two_mul_w16 : ∀ n : Nat, 3 ^ n > 2 * n
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by have ih := pow3_gt_two_mul_w16 (n + 1); rw [Nat.pow_succ]; omega

private theorem uWinExp_per_mask_core_and_key_w16
    (B M mask : Nat) (hB : B ≥ 1) (hM : M ≥ dyadicExpWindowMinM B)
    (_hmask : mask < 2 ^ B) :
    let w := B + 11
    let b0 := binBitLength (3 ^ w)
    let delta := dyadicPolyShiftDelta b0
    let a := b0 + delta
    let u_e := uWinExp B M mask
    IsCoreParityWord u_e ∧
    u_e.length = M - delta ∧
    parityWeight u_e = w ∧
    canonicalSuffixShift u_e 1 = a ∧
    IsFirstHitOnePair u_e 0 ∧
    affineCarry u_e ≥ 1 ∧
    affineCarry u_e < 2 ^ M ∧
    (∃ mid : List Bool, u_e = List.replicate 9 true ++ mid ++ [true]) ∧
    (∃ m : Nat, 2 ^ (u_e.length + a) = 3 ^ w * (81 * m + 1) + affineCarry u_e) := by
  dsimp only
  let w := B + 11
  let b0 := binBitLength (3 ^ w)
  let delta := dyadicPolyShiftDelta b0
  let a := b0 + delta
  let q3 := (2 ^ (a + 1) - 1) / 3
  let L := M - delta
  have hw_eq : w = B + 11 := rfl
  have ha_eq : a = b0 + delta := rfl
  have hL_eq : L = M - delta := rfl
  have hw_ge12 : w ≥ 12 := by rw [hw_eq]; omega
  rcases pow3_bitlength_strict_bounds_w16 w (by omega) with ⟨hb0_ge18, hb0_le2w, h3w_lo, _⟩
  change b0 ≥ 18 at hb0_ge18
  change b0 ≤ 2 * w at hb0_le2w
  change 3 ^ w + 1 ≤ 2 ^ b0 at h3w_lo
  rcases dyadicPolyShiftDelta_spec_w16 b0 with ⟨hdelta_le3, h3q3, hq3_n3, hq3_pos⟩
  change delta ≤ 3 at hdelta_le3
  change 3 * q3 + 1 = 2 ^ (a + 1) at h3q3
  change q3 % 3 ≠ 0 at hq3_n3
  change q3 ≥ 1 at hq3_pos
  have hM_def : M ≥ 6377332 + 8 * B := hM
  have hL_ge : L ≥ 6377329 + 8 * B := by rw [hL_eq]; omega
  have ha_lt_P : a < 2 * 3 ^ (w - 1) := by
    have hb0_2B : b0 ≤ 2 * (B + 11) := by rw [← hw_eq]; exact hb0_le2w
    have ha_le : a ≤ 2 * B + 25 := by rw [ha_eq]; omega
    have hw1_gt : 3 ^ (w - 1) > 2 * (B + 10) := by
      have hw_sub : w - 1 = B + 10 := by rw [hw_eq]; omega
      rw [hw_sub]; exact pow3_gt_two_mul_w16 (B + 10)
    omega
  -- Verify preconditions of `ternaryCarryChain B (L - 1) (q3 * 2 ^ (L - 1))`:
  let R0 := q3 * 2 ^ (L - 1)
  have hR0_n3 : R0 % 3 ≠ 0 := by
    intro h0
    dsimp [R0] at h0
    rw [Nat.mul_mod] at h0
    have hp2_n3 := pow2_mod3_nonzero_w5 (L - 1)
    have hq3_lt : q3 % 3 < 3 := Nat.mod_lt q3 (by decide)
    have hp2_lt : 2 ^ (L - 1) % 3 < 3 := Nat.mod_lt _ (by decide)
    rcases (by omega : q3 % 3 = 1 ∨ q3 % 3 = 2) with hq | hq <;>
    rcases (by omega : 2 ^ (L - 1) % 3 = 1 ∨ 2 ^ (L - 1) % 3 = 2) with hp | hp <;>
    (rw [hq, hp] at h0; cases h0)
  have hq3_ge_pow3 : q3 ≥ 2 * 3 ^ (B + 10) - 1 := by
    have ha1_ge : 2 ^ (a + 1) ≥ 2 * 2 ^ b0 := by
      have h : 2 ^ (b0 + 1) ≤ 2 ^ (a + 1) := pow2_mono_nat (by rw [ha_eq]; omega)
      rw [Nat.pow_succ, Nat.mul_comm] at h; exact h
    have h3w_sp : 3 ^ w = 3 * 3 ^ (B + 10) := by
      rw [hw_eq, show B + 11 = (B + 10) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    have hge6 : 3 * q3 + 1 ≥ 2 * (3 * 3 ^ (B + 10) + 1) := by
      rw [h3q3, ← h3w_sp]
      exact Nat.le_trans (Nat.mul_le_mul_left 2 h3w_lo) ha1_ge
    generalize 3 ^ (B + 10) = P3 at hge6 ⊢
    omega
  have hR0_lo : R0 ≥ (2 * 3 ^ (B + 10) - 1) * 2 ^ (L - 1) :=
    Nat.mul_le_mul_right _ hq3_ge_pow3
  rcases (ternaryCarryChain_spec_and_inj_w16 B (L - 1) R0 (L - 1)
    (Nat.le_refl _) (by omega) hR0_n3 hR0_lo).1 mask with
    ⟨he_lo, he_hi, hlen_gaps, hRfin_n3, hRfin_lo, hunwind⟩
  let ch := ternaryCarryChain B (L - 1) R0 mask
  let e_fin := ch.1
  let R_fin := ch.2.1
  let gaps := ch.2.2
  change (L - 1) - 8 * B ≤ e_fin at he_lo
  change e_fin ≤ L - 1 at he_hi
  change gaps.length = B at hlen_gaps
  change R_fin % 3 ≠ 0 at hRfin_n3
  change R_fin ≥ (2 * 3 ^ 10 - 1) * 2 ^ (L - 1) at hRfin_lo
  have he_fin_ge : e_fin ≥ 6377328 := by omega
  have h2L1_ge20 : 2 ^ (L - 1) ≥ 1048576 := by
    rw [show (1048576 : Nat) = 2 ^ 20 from rfl]; exact pow2_mono_nat (by omega)
  have hRfin_big : R_fin ≥ 118097 * 2 ^ (L - 1) := by
    simpa [show 2 * 3 ^ 10 - 1 = 118097 by decide] using hRfin_lo
  -- Final Hensel step at fixed modulus `3 ^ 14`:
  let sub_c := 3 * 19171 + 3 ^ 10
  have hsub_val : sub_c = 116562 := by decide
  let A_last := R_fin - sub_c
  have hA_eq_def : A_last = R_fin - sub_c := rfl
  have hsub_lt_Rfin : sub_c < R_fin := by omega
  have hA_n3 : (A_last % 3 ^ 14) % 3 ≠ 0 := by
    have hAn3 : A_last % 3 ≠ 0 := by
      have hrew : R_fin = A_last + 3 * 38854 := by rw [hA_eq_def, hsub_val]; omega
      intro h0
      have hm0 : R_fin % 3 = 0 := by rw [hrew, Nat.add_mul_mod_self_left, h0]
      exact hRfin_n3 hm0
    rwa [Nat.mod_mod_of_dvd A_last ⟨3 ^ 13, by decide⟩]
  rcases dlog2ModPow3_spec 14 (A_last % 3 ^ 14) (by decide) hA_n3 with
    ⟨htb_lt_raw, htb_mod_raw⟩
  let t_base := dlog2ModPow3 14 (A_last % 3 ^ 14)
  change t_base < 2 * 3 ^ (14 - 1) at htb_lt_raw
  change 2 ^ t_base % 3 ^ 14 = (A_last % 3 ^ 14) % 3 ^ 14 at htb_mod_raw
  have hper14_eq : 2 * 3 ^ (14 - 1) = 3188646 := by decide
  have htb_lt : t_base < 3188646 := by rwa [hper14_eq] at htb_lt_raw
  rcases (⟨3188646 + t_base, rfl⟩ : ∃ p : Nat, p = 3188646 + t_base) with ⟨p_last, hplast_def⟩
  have hplast_ge : p_last ≥ 3188646 := by rw [hplast_def]; omega
  have hplast_lt : p_last < 6377292 := by rw [hplast_def]; omega
  have hplast_efin : p_last + 3 ≤ e_fin := by omega
  have hmod_plast : 2 ^ p_last % 3 ^ 14 = A_last % 3 ^ 14 := by
    have hp_per : 2 ^ p_last % 3 ^ (13 + 1) = 2 ^ t_base % 3 ^ (13 + 1) := by
      rw [hplast_def, Nat.add_comm 3188646 t_base, show (3188646 : Nat) = 2 * 3 ^ 13 by decide]
      exact pow2_add_period_mod_pow3_w16 13 t_base
    change 2 ^ p_last % 3 ^ 14 = 2 ^ t_base % 3 ^ 14 at hp_per
    rw [hp_per]
    rw [Nat.mod_mod] at htb_mod_raw
    exact htb_mod_raw
  have h2p_lt_A : 2 ^ p_last < A_last := by
    have hle : 2 ^ p_last ≤ 2 ^ (L - 1) := pow2_mono_nat (by omega)
    omega
  have hdiff_mod : (A_last - 2 ^ p_last) % 3 ^ 14 = 0 := by
    let P14 := (3 : Nat) ^ 14
    change (A_last - 2 ^ p_last) % P14 = 0
    change 2 ^ p_last % P14 = A_last % P14 at hmod_plast
    have hdmA := (Nat.div_add_mod A_last P14).symm
    have hdmB := (Nat.div_add_mod (2 ^ p_last) P14).symm
    rw [hmod_plast] at hdmB
    have hsub_eq : A_last - 2 ^ p_last = P14 * (A_last / P14 - (2 ^ p_last) / P14) := by
      rw [Nat.mul_sub_left_distrib]
      generalize P14 * (A_last / P14) = QA, P14 * ((2 ^ p_last) / P14) = QB,
        A_last % P14 = rem, A_last = AN, 2 ^ p_last = BN at hdmA hdmB h2p_lt_A ⊢
      omega
    rw [hsub_eq, Nat.mul_mod_right]
  rcases Nat.dvd_of_mod_eq_zero hdiff_mod with ⟨m, hm_eq⟩
  have hA_rec : A_last = 3 ^ 14 * m + 2 ^ p_last := by
    rw [← hm_eq, Nat.sub_add_cancel (Nat.le_of_lt h2p_lt_A)]
  -- Build prefix words `u_0`, `u_1`, `u_2` up to `e_fin + 1`:
  let u0 := List.replicate 9 true
  let u1 := (u0 ++ List.replicate (p_last - 9) false) ++ [true]
  let u2 := (u1 ++ List.replicate (e_fin - (p_last + 1)) false) ++ [true]
  have hu0_car : affineCarry u0 = 19171 := by decide
  rcases affineCarry_append_replicate_false u0 (p_last - 9) with ⟨hwt_u0z, hcar_u0z⟩
  have hlen_u0z : (u0 ++ List.replicate (p_last - 9) false).length = p_last := by
    rw [List.length_append, show u0.length = 9 from rfl, List.length_replicate]; omega
  have hlen_u1 : u1.length = p_last + 1 := by
    dsimp [u1]; rw [List.length_append, hlen_u0z, List.length_singleton]
  have hwt_u1 : parityWeight u1 = 10 := by
    dsimp [u1]; rw [parityWeight_append, hwt_u0z]
    have h9 : parityWeight u0 = 9 := rfl
    have h1 : parityWeight [true] = 1 := rfl
    rw [h9, h1]
  have hcar_u1 : affineCarry u1 = 3 * 19171 + 2 ^ p_last := by
    dsimp [u1]; rw [affineCarry_append, hcar_u0z, hu0_car, hlen_u0z]
    have hc1 : affineCarry [true] = 1 := rfl
    have hw1 : parityWeight [true] = 1 := rfl
    rw [hc1, hw1]; omega
  have hcar_u1_lt : affineCarry u1 < 2 ^ (p_last + 1) := by
    rw [hcar_u1, Nat.pow_succ 2 p_last]
    have hp20 : 2 ^ p_last ≥ 1048576 := by
      rw [show (1048576 : Nat) = 2 ^ 20 from rfl]; exact pow2_mono_nat (by omega)
    generalize 2 ^ p_last = ZP at hp20 ⊢
    omega
  rcases affineCarry_append_replicate_false u1 (e_fin - (p_last + 1)) with ⟨hwt_u1z, hcar_u1z⟩
  have hlen_u1z : (u1 ++ List.replicate (e_fin - (p_last + 1)) false).length = e_fin := by
    rw [List.length_append, hlen_u1, List.length_replicate]; omega
  have hlen_u2 : u2.length = e_fin + 1 := by
    dsimp [u2]; rw [List.length_append, hlen_u1z, List.length_singleton]
  have hwt_u2 : parityWeight u2 = 11 := by
    dsimp [u2]; rw [parityWeight_append, hwt_u1z, hwt_u1]; rfl
  have hcar_u2 : affineCarry u2 = 3 * affineCarry u1 + 2 ^ e_fin := by
    dsimp [u2]; rw [affineCarry_append, hcar_u1z, hlen_u1z]
    have hc1 : affineCarry [true] = 1 := rfl
    have hw1 : parityWeight [true] = 1 := rfl
    rw [hc1, hw1]; omega
  have hcar_u2_lt : affineCarry u2 < 2 ^ (e_fin + 1) := by
    rw [hcar_u2]
    have hc_le : affineCarry u1 < 2 ^ (e_fin - 2) :=
      Nat.lt_of_lt_of_le hcar_u1_lt (pow2_mono_nat (by omega))
    have hp_e : 2 ^ e_fin = 4 * 2 ^ (e_fin - 2) := by
      conv => lhs; rw [show e_fin = 2 + (e_fin - 2) by omega, Nat.pow_add]
    have hp_e1 : 2 ^ (e_fin + 1) = 8 * 2 ^ (e_fin - 2) := by
      conv => lhs; rw [show e_fin + 1 = 3 + (e_fin - 2) by omega, Nat.pow_add]
    rw [hp_e, hp_e1]
    generalize 2 ^ (e_fin - 2) = Z at hc_le ⊢; omega
  let Q1 := 3 ^ 10 * (81 * m + 1)
  have hRfin_Q1 : R_fin = Q1 + affineCarry u1 := by
    have hR_sub : R_fin = A_last + sub_c := by
      rw [hA_eq_def, Nat.sub_add_cancel (Nat.le_of_lt hsub_lt_Rfin)]
    have hQ1_exp : Q1 = 3 ^ 14 * m + 3 ^ 10 := by
      dsimp [Q1]; rw [Nat.mul_add, Nat.mul_one, show 3 ^ 10 * (81 * m) = 3 ^ 14 * m by
        rw [← Nat.mul_assoc, show (3 : Nat) ^ 10 * 81 = 3 ^ 14 by decide]]
    rw [hR_sub, hA_rec, hQ1_exp, hcar_u1]; dsimp [sub_c]; omega
  have hu2_base_eq : 3 * R_fin + 2 ^ e_fin = 3 * Q1 + affineCarry u2 := by
    rw [hRfin_Q1, hcar_u2, Nat.mul_add, Nat.add_assoc]
  rcases hunwind u2 Q1 hlen_u2 hcar_u2_lt hu2_base_eq with
    ⟨hw_len, hw_wt, hw_car, hw_key⟩
  have hu_eq_wout : uWinExp B M mask = u2 ++ zeroRunsSuffix gaps := by
    unfold uWinExp uWinExpRuns
    have hr_split : (p_last - 9) :: (e_fin - (p_last + 1)) :: gaps =
        [p_last - 9, e_fin - (p_last + 1)] ++ gaps := rfl
    dsimp only
    change u0 ++ zeroRunsSuffix (((3188646 + t_base) - 9) :: (e_fin - ((3188646 + t_base) + 1)) :: gaps) = _
    rw [← hplast_def, hr_split, zeroRunsSuffix_append_and_inj_w16.1 [p_last - 9, e_fin - (p_last + 1)] gaps]
    dsimp only [zeroRunsSuffix, u2, u1]
    simp [List.append_assoc]
  rcases (⟨uWinExp B M mask, rfl⟩ : ∃ u_x : List Bool, u_x = uWinExp B M mask) with ⟨u_e, hue_def⟩
  have hue_wout : u_e = u2 ++ zeroRunsSuffix gaps := hue_def.trans hu_eq_wout
  rw [← hue_wout] at hw_len hw_wt hw_car hw_key
  have hlen_final : u_e.length = L := by rw [hw_len]; omega
  have hwt_final : parityWeight u_e = w := by rw [hw_wt, hwt_u2, hw_eq]; omega
  have hcar_lt_M : affineCarry u_e < 2 ^ M :=
    Nat.lt_of_lt_of_le (by rwa [show (L - 1) + 1 = L by omega] at hw_car)
      (pow2_mono_nat (by rw [hL_eq]; omega))
  have hkey_final : 2 ^ (u_e.length + a) = 3 ^ w * (81 * m + 1) + affineCarry u_e := by
    have hlhs : 2 ^ (L + a) = 3 * R0 + 2 ^ (L - 1) := by
      dsimp [R0]
      rw [show L + a = (a + 1) + (L - 1) by omega, Nat.pow_add 2 (a + 1) (L - 1),
          ← h3q3, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
    have hrhs : 3 ^ (B + 1) * Q1 = 3 ^ w * (81 * m + 1) := by
      dsimp [Q1]
      rw [← Nat.mul_assoc, ← Nat.pow_add 3 (B + 1) 10,
          show (B + 1) + 10 = w by rw [hw_eq]]
    rw [hlen_final, hlhs, hw_key, hrhs]
  have hmid_ex : ∃ mid : List Bool, u_e = List.replicate 9 true ++ mid ++ [true] := by
    rcases zeroRunsSuffix_nonempty_eq_mid_true_w16 (p_last - 9) ((e_fin - (p_last + 1)) :: gaps) with
      ⟨mid, hmid⟩
    refine ⟨mid, ?_⟩
    rw [hue_def]; unfold uWinExp uWinExpRuns
    dsimp only
    change List.replicate 9 true ++ zeroRunsSuffix (((3188646 + t_base) - 9) :: (e_fin - ((3188646 + t_base) + 1)) :: gaps) = _
    rw [← hplast_def, hmid, List.append_assoc]
  have hcore_u : IsCoreParityWord u_e := by
    rcases hmid_ex with ⟨mid, hmid⟩
    refine ⟨?_, ?_⟩
    · rw [hmid]; rfl
    · rw [hmid, List.reverse_append]; rfl
  have hsh_a : canonicalSuffixShift u_e 1 = a := by
    rcases canonicalSuffixShift_spec_unique u_e 1 (by rw [hwt_final]; omega) (by decide) with
      ⟨_, _, huniq⟩
    symm
    apply huniq a (by rw [hwt_final]; exact ha_lt_P)
    rw [Nat.mul_one, hwt_final, hkey_final, Nat.add_comm]
    exact Nat.add_mul_mod_self_left _ _ _
  have hfh : IsFirstHitOnePair u_e 0 :=
    (first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.2 u_e hcore_u).mpr
      (by rw [hsh_a, ha_eq]; omega)
  have hcar_pos : affineCarry u_e ≥ 1 := by
    rw [hue_wout]
    cases hg : gaps with
    | nil => rw [hg] at hlen_gaps; simp at hlen_gaps; omega
    | cons g0 gtl =>
      rcases zeroRunsSuffix_nonempty_eq_mid_true_w16 g0 gtl with ⟨m_g, hmg⟩
      rw [hmg, ← List.append_assoc u2 m_g [true], affineCarry_append]
      have hc1 : affineCarry [true] = 1 := rfl
      rw [hc1, Nat.mul_one]
      have hp := pow2_pos_nat (u2 ++ m_g).length
      omega
  subst hue_def
  exact ⟨hcore_u, hlen_final, hwt_final, hsh_a, hfh, hcar_pos, hcar_lt_M, hmid_ex, ⟨m, hkey_final⟩⟩

private theorem uWinExp_per_mask_leaf_spec_w16
    (B M mask : Nat) (hB : B ≥ 1) (hM : M ≥ dyadicExpWindowMinM B)
    (hmask : mask < 2 ^ B) :
    let w := B + 11
    let b0 := binBitLength (3 ^ w)
    let delta := dyadicPolyShiftDelta b0
    let u := uWinExp B M mask
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
  let w := B + 11
  let b0 := binBitLength (3 ^ w)
  let delta := dyadicPolyShiftDelta b0
  let a := b0 + delta
  have hw_eq : w = B + 11 := rfl
  have ha_eq : a = b0 + delta := rfl
  rcases pow3_bitlength_strict_bounds_w16 w (by rw [hw_eq]; omega) with ⟨_, _, h3w_lo, h2b0_hi⟩
  change 3 ^ w + 1 ≤ 2 ^ b0 at h3w_lo
  change 2 ^ b0 < 2 * 3 ^ w at h2b0_hi
  rcases dyadicPolyShiftDelta_spec_w16 b0 with ⟨hdelta_le3, _, _, _⟩
  change delta ≤ 3 at hdelta_le3
  have hM_ge30 : M ≥ 30 := by unfold dyadicExpWindowMinM at hM; omega
  rcases uWinExp_per_mask_core_and_key_w16 B M mask hB hM hmask with
    ⟨hcore_r, hlen_r, hwt_r, hsh_r, hfh_r, hcar_pos_r, hcar_lt_r, ⟨mid, hu_mid_r⟩, ⟨m, hkey_r⟩⟩
  rcases (⟨uWinExp B M mask, rfl⟩ : ∃ u0 : List Bool, u0 = uWinExp B M mask) with ⟨u_e, hue_def⟩
  rw [← hue_def] at hcore_r hlen_r hwt_r hsh_r hfh_r hcar_pos_r hcar_lt_r hu_mid_r hkey_r
  change u_e.length = M - delta at hlen_r
  change parityWeight u_e = w at hwt_r
  change canonicalSuffixShift u_e 1 = a at hsh_r
  change 2 ^ (u_e.length + a) = 3 ^ w * (81 * m + 1) + affineCarry u_e at hkey_r
  rcases (⟨exactBackwardQuotient 1 u_e 0, rfl⟩ :
      ∃ y0 : Nat, y0 = exactBackwardQuotient 1 u_e 0) with ⟨y, hy_def⟩
  have hy_81m1 : y = 81 * m + 1 := by
    rcases one_generator_pos_odd_and_reaches_one u_e 0 hcore_r with ⟨_, _, heq_bw, _⟩
    have hbw_steps : backwardOneTotalSteps u_e 0 = u_e.length + a := by
      unfold backwardOneTotalSteps; rw [hsh_r]; omega
    rw [hbw_steps, hwt_r, ← hy_def] at heq_bw
    have hcomb : 3 ^ w * y = 3 ^ w * (81 * m + 1) :=
      Nat.add_right_cancel (heq_bw.symm.trans hkey_r)
    exact Nat.eq_of_mul_eq_mul_left (pow3_pos_nat w) hcomb
  have hy_m81 : y % 81 = 1 := by rw [hy_81m1]; omega
  have hy_m512 : y % 512 = 511 := by
    have hp9_511 : parityOfIter 9 511 = List.replicate 9 true := by decide
    have hu_511 : u_e = parityOfIter 9 511 ++ mid ++ [true] := by rw [hp9_511]; exact hu_mid_r
    have hm := (surviving_mod512_nine_prefix_auto_weight_and_characterization.1 511
      (by decide) (by decide)).2.2.2 mid 0 |>.2.2.1
    rwa [← hu_511, ← hy_def] at hm
  rcases isSurvivingMod373248_of_511_and_1_w16 y hy_m512 hy_m81 with ⟨hb_surv, hcls_surv⟩
  have hy_win : 2 ^ M ≤ y ∧ y < 2 ^ (M + 1) := by
    have hLa_eq : u_e.length + a = b0 + M := by rw [hlen_r, ha_eq]; omega
    have heq_y : 3 ^ w * y + affineCarry u_e = 2 ^ b0 * 2 ^ M := by
      have hk := hkey_r.symm
      rwa [← hy_81m1, hLa_eq, Nat.pow_add 2 b0 M] at hk
    have hPM_pos := pow2_pos_nat M
    refine ⟨?_, ?_⟩
    · by_cases hge : 2 ^ M ≤ y
      · exact hge
      · exfalso
        have hy_le : y ≤ 2 ^ M - 1 := by clear hu_mid_r hcore_r hfh_r hb_surv hcls_surv; omega
        have h1 : 3 ^ w * y + affineCarry u_e < (3 ^ w + 1) * 2 ^ M := by
          calc 3 ^ w * y + affineCarry u_e
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
        have h1 : (2 * 3 ^ w) * 2 ^ M < 3 ^ w * y + affineCarry u_e := by
          calc (2 * 3 ^ w) * 2 ^ M
              = 3 ^ w * (2 * 2 ^ M) :=
                (Nat.mul_assoc 2 (3 ^ w) (2 ^ M)).trans (Nat.mul_left_comm 2 (3 ^ w) (2 ^ M))
            _ ≤ 3 ^ w * y := Nat.mul_le_mul_left _ hy_ge
            _ < 3 ^ w * y + affineCarry u_e := by
                clear hu_mid_r hcore_r hfh_r hb_surv hcls_surv; omega
        have h2 : 2 ^ b0 * 2 ^ M < (2 * 3 ^ w) * 2 ^ M :=
          Nat.mul_lt_mul_of_pos_right h2b0_hi hPM_pos
        clear hu_mid_r hcore_r hfh_r hb_surv hcls_surv; omega
  have hlen_le_M : u_e.length ≤ M := by rw [hlen_r]; omega
  have hy_mem_win : ∀ L_max : Nat, L_max ≥ M -> y ∈ dyadicWindowSurvivingQ0Leaves L_max M := by
    intro L_max hL_max
    have hy_mem_fh : y ∈ firstHitSurvivingQ0LeavesUpToLen L_max :=
      (multiscale_first_hit_surviving_q0_leaves_nodup L_max).2.2 y |>.mpr
        ⟨u_e, hfh_r, Nat.le_trans hlen_le_M hL_max, hb_surv, hy_def.symm⟩
    unfold dyadicWindowSurvivingQ0Leaves
    exact List.mem_filter.mpr ⟨hy_mem_fh, decide_eq_true hy_win⟩
  subst hue_def
  rw [← hy_def]
  exact ⟨hfh_r, hlen_r, hlen_le_M, hwt_r, hsh_r,
         hy_m512, hy_m81, hb_surv, hcls_surv, hy_win.1, hy_win.2, hy_mem_win⟩

private theorem uWinExp_inj_mask_w16
    (B M m1 m2 : Nat) (hB : B ≥ 1) (hM : M ≥ dyadicExpWindowMinM B)
    (hm1 : m1 < 2 ^ B) (hm2 : m2 < 2 ^ B)
    (hy_eq : exactBackwardQuotient 1 (uWinExp B M m1) 0 =
      exactBackwardQuotient 1 (uWinExp B M m2) 0) :
    m1 = m2 := by
  have hfh1 := (uWinExp_per_mask_core_and_key_w16 B M m1 hB hM hm1).2.2.2.2.1
  have hfh2 := (uWinExp_per_mask_core_and_key_w16 B M m2 hB hM hm2).2.2.2.2.1
  have hu_eq : uWinExp B M m1 = uWinExp B M m2 :=
    (first_hit_one_pair_sound_and_injective _ _ 0 0 hfh1 hfh2).2.2.2 hy_eq |>.1
  unfold uWinExp at hu_eq
  have hzs_eq := (list_append_inj_left_eq_len _ _ _ _ rfl hu_eq).2
  have hruns_eq := zeroRunsSuffix_append_and_inj_w16.2 _ _ hzs_eq
  unfold uWinExpRuns at hruns_eq
  dsimp only at hruns_eq
  have hgaps_eq := (List.cons.inj (List.cons.inj hruns_eq).2).2
  let w := B + 11
  let b0 := binBitLength (3 ^ w)
  let delta := dyadicPolyShiftDelta b0
  let a := b0 + delta
  let q3 := (2 ^ (a + 1) - 1) / 3
  let L := M - delta
  rcases pow3_bitlength_strict_bounds_w16 w (by dsimp [w]; omega) with ⟨_, _, h3w_lo, _⟩
  change 3 ^ w + 1 ≤ 2 ^ b0 at h3w_lo
  rcases dyadicPolyShiftDelta_spec_w16 b0 with ⟨hdelta_le3, h3q3, hq3_n3, _⟩
  change delta ≤ 3 at hdelta_le3
  change 3 * q3 + 1 = 2 ^ (a + 1) at h3q3
  change q3 % 3 ≠ 0 at hq3_n3
  have hL_ge : L ≥ 6377329 + 8 * B := by dsimp [L]; unfold dyadicExpWindowMinM at hM; omega
  have hR0_n3 : (q3 * 2 ^ (L - 1)) % 3 ≠ 0 := by
    intro h0; rw [Nat.mul_mod] at h0
    have hp2_n3 := pow2_mod3_nonzero_w5 (L - 1)
    have hq3_lt : q3 % 3 < 3 := Nat.mod_lt q3 (by decide)
    have hp2_lt : 2 ^ (L - 1) % 3 < 3 := Nat.mod_lt _ (by decide)
    rcases (by omega : q3 % 3 = 1 ∨ q3 % 3 = 2) with hq | hq <;>
    rcases (by omega : 2 ^ (L - 1) % 3 = 1 ∨ 2 ^ (L - 1) % 3 = 2) with hp | hp <;>
    (rw [hq, hp] at h0; cases h0)
  have hq3_ge : q3 ≥ 2 * 3 ^ (B + 10) - 1 := by
    have ha1_ge : 2 ^ (a + 1) ≥ 2 * 2 ^ b0 := by
      have h : 2 ^ (b0 + 1) ≤ 2 ^ (a + 1) := pow2_mono_nat (by dsimp [a]; omega)
      rw [Nat.pow_succ, Nat.mul_comm] at h; exact h
    have h3w_sp : 3 ^ w = 3 * 3 ^ (B + 10) := by
      dsimp [w]; rw [show B + 11 = (B + 10) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    have hge6 : 3 * q3 + 1 ≥ 2 * (3 * 3 ^ (B + 10) + 1) := by
      rw [h3q3, ← h3w_sp]; exact Nat.le_trans (Nat.mul_le_mul_left 2 h3w_lo) ha1_ge
    generalize 3 ^ (B + 10) = P3 at hge6 ⊢; omega
  exact (ternaryCarryChain_spec_and_inj_w16 B (L - 1) (q3 * 2 ^ (L - 1)) (L - 1)
    (Nat.le_refl _) (by omega) hR0_n3 (Nat.mul_le_mul_right _ hq3_ge)).2 m1 m2 hm1 hm2 hgaps_eq

/--
  Theorem W16.4b (`dyadic_window_compressed_exponential_occupancy`, `zero custom axioms`):
  Constructive Digit-by-Digit Mod-`9` Ternary-Carry-Lifted Family `uWinExp B M mask` &
  Unconditional True Exponential Surviving-Leaf Dyadic-Window Occupancy
  (`≥ 2 ^ B` at Linear Threshold `M ≥ 6377332 + 8 * B`, i.e. `≥ 2 ^ ((M - 6377332) / 8)` at
  Linear Horizon `L_max ≥ M`, `Branches P2.2 & P5.3`, `W16_H4`):
  1. **Explicit `2 ^ B` Surviving First-Hit Family (`∀ B ≥ 1, ∀ M ≥ dyadicExpWindowMinM B, ∀ mask < 2 ^ B`)**:
     Each word `u := uWinExp B M mask` satisfies `IsFirstHitOnePair u 0`, `u.length = M - delta ≤ M`,
     `parityWeight u = B + 11`, `canonicalSuffixShift u 1 = b0 + delta`, AND `y := exactBackwardQuotient 1 u 0`
     satisfies `y % 512 = 511`, `y % 81 = 1`, `IsSurvivingMod373248Class y`, `2 ^ M ≤ y ∧ y < 2 ^ (M + 1)`,
     and `∀ L_max ≥ M, y ∈ dyadicWindowSurvivingQ0Leaves L_max M`!
  2. **Pairwise Leaf Injectivity Across All `m1, m2 < 2 ^ B`**:
     `exactBackwardQuotient 1 (uWinExp B M m1) 0 = exactBackwardQuotient 1 (uWinExp B M m2) 0 -> m1 = m2`!
  3. **Unconditional True Exponential Window Occupancy (`∀ L_max ≥ M`)**:
     `(dyadicWindowSurvivingQ0Leaves M M).length ≥ 2 ^ B`,
     `∀ L_max ≥ M, (dyadicWindowSurvivingQ0Leaves L_max M).length ≥ 2 ^ B`, AND explicitly in `M` alone:
     `∀ M' L_max, M' ≥ 6377340 -> L_max ≥ M' -> (dyadicWindowSurvivingQ0Leaves L_max M').length ≥ 2 ^ ((M' - 6377332) / 8)`!
-/
theorem dyadic_window_compressed_exponential_occupancy :
    (∀ (B M : Nat), B ≥ 1 -> M ≥ dyadicExpWindowMinM B ->
      let w := B + 11
      let b0 := binBitLength (3 ^ w)
      let delta := dyadicPolyShiftDelta b0
      (∀ mask : Nat, mask < 2 ^ B ->
        let u := uWinExp B M mask
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
      (∀ m1 m2 : Nat, m1 < 2 ^ B -> m2 < 2 ^ B ->
        exactBackwardQuotient 1 (uWinExp B M m1) 0 =
          exactBackwardQuotient 1 (uWinExp B M m2) 0 ->
        m1 = m2) ∧
      ((dyadicWindowSurvivingQ0Leaves M M).length ≥ 2 ^ B ∧
       ∀ L_max : Nat, L_max ≥ M ->
         (dyadicWindowSurvivingQ0Leaves L_max M).length ≥ 2 ^ B)) ∧
    (∀ (M L_max : Nat), M ≥ 6377340 -> L_max ≥ M ->
      (dyadicWindowSurvivingQ0Leaves L_max M).length ≥ 2 ^ ((M - 6377332) / 8)) := by
  have hmain : ∀ (B M : Nat), B ≥ 1 -> M ≥ dyadicExpWindowMinM B ->
      let w := B + 11
      let b0 := binBitLength (3 ^ w)
      let delta := dyadicPolyShiftDelta b0
      (∀ mask : Nat, mask < 2 ^ B ->
        let u := uWinExp B M mask
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
      (∀ m1 m2 : Nat, m1 < 2 ^ B -> m2 < 2 ^ B ->
        exactBackwardQuotient 1 (uWinExp B M m1) 0 =
          exactBackwardQuotient 1 (uWinExp B M m2) 0 ->
        m1 = m2) ∧
      ((dyadicWindowSurvivingQ0Leaves M M).length ≥ 2 ^ B ∧
       ∀ L_max : Nat, L_max ≥ M ->
         (dyadicWindowSurvivingQ0Leaves L_max M).length ≥ 2 ^ B) := by
    intro B M hB hM; dsimp only
    refine ⟨?_, fun m1 m2 h1 h2 heq => uWinExp_inj_mask_w16 B M m1 m2 hB hM h1 h2 heq, ?_⟩
    · intro mask hmask
      rcases uWinExp_per_mask_leaf_spec_w16 B M mask hB hM hmask with
        ⟨hfh, hlen, hle_M, hwt, hsh, h512, h81, _, hcls, hlo, hhi, hmem⟩
      exact ⟨hfh, hlen, hle_M, hwt, hsh, h512, h81, hcls, hlo, hhi, hmem M (Nat.le_refl M), hmem⟩
    · rcases descIdxListW16_spec (2 ^ B) with ⟨hd_len, hd_nd, hd_lt⟩
      let fnLeaf : Nat -> Nat := fun mask => exactBackwardQuotient 1 (uWinExp B M mask) 0
      let leaves2B := (descIdxListW16 (2 ^ B)).map fnLeaf
      have hnd_2B : NoDupNat leaves2B :=
        noDupNat_map_inj_on_w16 fnLeaf (descIdxListW16 (2 ^ B)) hd_nd
          (fun a ha b hb heq => uWinExp_inj_mask_w16 B M a b hB hM (hd_lt a ha) (hd_lt b hb) heq)
      have hlen_2B : leaves2B.length = 2 ^ B := by
        dsimp only [leaves2B]; rw [List.length_map, hd_len]
      have hall_L : ∀ L_max : Nat, L_max ≥ M ->
          (dyadicWindowSurvivingQ0Leaves L_max M).length ≥ 2 ^ B := by
        intro L_max hL_max
        have hsub_2B : ∀ y ∈ leaves2B, y ∈ dyadicWindowSurvivingQ0Leaves L_max M := by
          intro y hy
          rcases List.mem_map.mp hy with ⟨mask, hmask, rfl⟩
          exact (uWinExp_per_mask_leaf_spec_w16 B M mask hB hM (hd_lt mask hmask)).2.2.2.2.2.2.2.2.2.2.2 L_max hL_max
        have hle := noDupNat_length_le_of_subset_w16
          (dyadicWindowSurvivingQ0Leaves L_max M) leaves2B hnd_2B hsub_2B
        omega
      exact ⟨hall_L M (Nat.le_refl M), hall_L⟩
  refine ⟨hmain, ?_⟩
  intro M L_max hM hL_max
  let B := (M - 6377332) / 8
  have hB1 : B ≥ 1 := by dsimp [B]; omega
  have hM_min : M ≥ dyadicExpWindowMinM B := by
    dsimp [B]; unfold dyadicExpWindowMinM; omega
  exact (hmain B M hB1 hM_min).2.2.2 L_max hL_max

end CollatzFormal
