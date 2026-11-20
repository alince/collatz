/-
  CollatzFormal/Wave12WholeSpace.lean
  Wave 12 Whole-Space Mathematical & CS Proof Loop (Synthesis — Fronts C & D):
  1. Front C (Branches P1.2 & P5.11):
     - Universal All-Base Pure Exponential `binBitLength` Collapse at `m = 8` (`5/32 > 1/16` at `B = 2`),
     - 2-Step Mod-`9` Backward Branch-Descent Lookahead (`x_{2k} < 2^(13*k + x0)`) & Eventual (`∀ M_0 ≥ 3`)
       Critical-Base Impossibility (`p_B ^ 13 < 4 * q_B ^ 13`, covering `(10, 9)` and `(11, 10)`),
     - Reverse Syracuse Odd-Branch Chains (`x_t = 2^(t+1) * 3^(2m-t) - 1`) & Eventual (`∀ M_0 ≥ 3`)
       Impossibility of ALL Polynomial-Numerator Two-Sided Exponential-`binBitLength` Preimage Weights
       Across ALL Rational Bases `p_B, q_B ≥ 1`,
     - End-to-End Global Convergence, 7-Tier `ω^7` Cascade (`Cone 10 -> Cone 9 -> ... -> Cone 5 -> Φ_2`),
       Choice-Free `Q_(6)^+` Cone-10 Avoidance, & `[]`-Axiom `M1/M2/M3` Counter-Model Separation for the
       9th Solvable `(3x + 1)`-Cousin `T_diamond9` (`1610366669 -> 603887501` in `17` steps to `1`).
  2. Front D (Branches P2.2 & P5.3):
     - Complete Mod-`486` (`2 * 3^5`) Markov Shift Bijection (`Fin 162` ↔ `162` surviving classes, matching
       the exact `w(u) ≥ 6` floor of `IsSurvivingMod373248Class`!) & Universal `6`-Ones `243 mod 486` Lock,
     - Universal Equal-Shift `(M, L, w, a)` Carry-Difference Law `3^w * (y2 - y1) = C(u1) - C(u2)`,
       Spread Ceiling `y2 - y1 < 2^(L - w)`, `L ≤ w + 1` Cell Uniqueness, `L ≤ w + 9` Mod-`512` Fiber
       Uniqueness, & Sub-Critical Multi-Leaf Split Certificate (`369` vs `373` at `(8, 12, 4)`),
     - Coupled `dyadicWindowSurvivingQ0Leaves L_max M` `162/486` Confinement, `3^(w - 6)` (`j = 5`)
       Multi-Step Fiber Equidistribution, & `11 + 16 = 27` Surviving `Mod 512` Prefix Decomposition
       Proving Summed Window Occupancy `≤ min (2^(M - 1)) (27 * 2^(L_max - 9))` (`∀ L_max ≥ 9, ∀ M ≥ 1`).

  Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

import CollatzFormal.Wave12WholeSpaceCore

namespace CollatzFormal

-- ============================================================================
-- SECTION 1: Front C Part 1 (Branch P1.2) — Exponential-in-`binBitLength`
--            Non-Radial Preimage Denominators vs 2-Step Mod-`9` Branch-Descent
--            & Reverse Syracuse Odd-Branch Chains (`W12_H1`)
-- ============================================================================

private theorem mul_pow_w12s (a b : Nat) : ∀ n : Nat, (a * b) ^ n = a ^ n * b ^ n
  | 0 => rfl
  | n + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, mul_pow_w12s a b n]
    ac_rfl

private theorem pow_mono_base_w12s (a b : Nat) (hle : a ≤ b) : ∀ n : Nat, a ^ n ≤ b ^ n
  | 0 => Nat.le_refl 1
  | n + 1 => Nat.mul_le_mul (pow_mono_base_w12s a b hle n) hle

private theorem id_lt_pow2_w12s : ∀ n : Nat, n < 2 ^ n
  | 0 => by decide
  | n + 1 => by
    have ih := id_lt_pow2_w12s n
    have hp := pow2_pos_nat n
    rw [Nat.pow_succ]
    omega

-- Constructive pure-`Nat` Bernoulli inequality: `A ^ (n + 1) + n * A ^ n ≤ A * (A + 1) ^ n`.
private theorem bernoulli_nat_mul (A : Nat) :
    ∀ n : Nat, A ^ (n + 1) + n * A ^ n ≤ A * (A + 1) ^ n
  | 0 => by simp
  | n + 1 => by
    have ih := bernoulli_nat_mul A n
    have hm := Nat.mul_le_mul_right (A + 1) ih
    have hr : (A * (A + 1) ^ n) * (A + 1) = A * (A + 1) ^ (n + 1) := by
      rw [Nat.mul_assoc, ← Nat.pow_succ]
    rw [hr] at hm
    have hl : A ^ (n + 2) + (n + 1) * A ^ (n + 1) ≤ (A ^ (n + 1) + n * A ^ n) * (A + 1) := by
      have heq : (A ^ (n + 1) + n * A ^ n) * (A + 1) =
          (A ^ (n + 2) + (n + 1) * A ^ (n + 1)) + n * A ^ n := by
        rw [show n + 2 = (n + 1) + 1 by rfl, Nat.pow_succ A (n + 1),
            Nat.add_mul n 1 (A ^ (n + 1)), Nat.one_mul,
            Nat.pow_succ A n,
            Nat.add_mul (A ^ n * A) (n * A ^ n) (A + 1),
            Nat.mul_add (A ^ n * A) A 1, Nat.mul_one,
            Nat.mul_add (n * A ^ n) A 1, Nat.mul_one]
        ac_rfl
      rw [heq]
      exact Nat.le_add_right _ _
    exact Nat.le_trans hl hm

-- Consequence 1: Whenever `1 ≤ A < B`, `K_0 * A ^ (K_0 * A) < B ^ (K_0 * A)`.
private theorem pow_gt_const_mul_pow_of_lt (A B K_0 : Nat) (hA : A ≥ 1) (hAB : A < B) :
    let k := K_0 * A
    K_0 * A ^ k < B ^ k := by
  dsimp only
  let k := K_0 * A
  have hbern := bernoulli_nat_mul A k
  have hb_mono : A * (A + 1) ^ k ≤ A * B ^ k :=
    Nat.mul_le_mul_left A (pow_mono_base_w12s (A + 1) B (by omega) k)
  have hle_AB : A ^ (k + 1) + k * A ^ k ≤ A * B ^ k := Nat.le_trans hbern hb_mono
  have hfac : A ^ (k + 1) + k * A ^ k = A * ((K_0 + 1) * A ^ k) := by
    dsimp [k]
    rw [Nat.pow_succ A (K_0 * A), Nat.mul_comm (A ^ (K_0 * A)) A,
        Nat.add_mul K_0 1 (A ^ (K_0 * A)), Nat.one_mul, Nat.mul_add A]
    ac_rfl
  rw [hfac] at hle_AB
  have hle_B : (K_0 + 1) * A ^ k ≤ B ^ k :=
    nat_mul_le_cancel_left_w5 A _ _ (by omega) hle_AB
  have hAk_pos : A ^ k ≥ 1 := nat_pow_pos_of_pos A (by omega) k
  rw [Nat.add_mul K_0 1 (A ^ k), Nat.one_mul] at hle_B
  dsimp [k] at hle_B hAk_pos ⊢
  omega

-- Consequence 2: For every `q ≥ 1`, `2 * q ^ q ≤ (q + 1) ^ q`.
private theorem two_mul_pow_self_le_succ_pow (q : Nat) (hq : q ≥ 1) :
    2 * q ^ q ≤ (q + 1) ^ q := by
  have hb := bernoulli_nat_mul q q
  have hfac : q ^ (q + 1) + q * q ^ q = q * (2 * q ^ q) := by
    rw [Nat.pow_succ q q, show 2 = 1 + 1 by rfl, Nat.add_mul 1 1 (q ^ q),
        Nat.one_mul, Nat.mul_add q]
    ac_rfl
  rw [hfac] at hb
  exact nat_mul_le_cancel_left_w5 q _ _ (by omega) hb

/--
  Theorem W12.3a (`pure_exp_bitlength_all_base_m8_collapse`, choice-free `zero custom axioms`):
  Universal All-Base Collapse of Pure Exponential `binBitLength` Preimage Weights at `m = 8` &
  Explicit `B = 2` / Reverse-Syracuse `m = 2` Certificate (`Branch P1.2`,
  witness `ZPOS_EXP_BITLENGTH_BASE2_COLLAPSE_8_AND_REVERSE_SYRACUSE`, `W12_H1`):
  1. At `m = 8` (`2 * m = 16`, `n_odd = 5`), `binBitLength 8 = 4`, `binBitLength 16 = 5`,
     `binBitLength 5 = 3`, so `2^(-binBitLength n)` yields `1/32 + 1/8 = 5/32 > 1/16`, AND at `m = 2`
     the reverse Syracuse chain `161 -> 107 -> 71 -> 47 -> 31` drops from `8` bits to `5` bits!
  2. For EVERY positive rational base `(p_B, q_B)` (`p_B ≥ 1, q_B ≥ 1`) and EVERY `(pTheta, qTheta)`,
     `wNum n = q_B ^ binBitLength n`, `wDen n = p_B ^ binBitLength n` strictly violates
     `IsPositiveRationalPreimageWeight` at `m = 8` (`q_B^2 + p_B^2 > q_B * p_B`)!
-/
theorem pure_exp_bitlength_all_base_m8_collapse :
    (binBitLength 8 = 4 ∧ binBitLength 16 = 5 ∧ binBitLength 5 = 3 ∧
     (1 * 8 + 1 * 32) * 16 > 1 * (32 * 8) ∧
     binBitLength 161 = 8 ∧ binBitLength 31 = 5 ∧
     161 % 3 = 2 ∧ (2 * 161 - 1) / 3 = 107 ∧
     107 % 3 = 2 ∧ (2 * 107 - 1) / 3 = 71 ∧
     71 % 3 = 2 ∧ (2 * 71 - 1) / 3 = 47 ∧
     47 % 3 = 2 ∧ (2 * 47 - 1) / 3 = 31) ∧
    (∀ (p_B q_B pTheta qTheta : Nat),
      p_B ≥ 1 -> q_B ≥ 1 ->
      ¬ IsPositiveRationalPreimageWeight
          (fun n => q_B ^ binBitLength n) (fun n => p_B ^ binBitLength n) pTheta qTheta) := by
  refine ⟨by decide, ?_⟩
  intro p_B q_B pTheta qTheta hpB hqB hw
  have hq_pos : qTheta > 0 := Nat.lt_of_lt_of_le hw.1 hw.2.1
  have hm8 := hw.2.2.2.2 8 (by decide) (by decide)
  dsimp only at hm8
  have hb8 : binBitLength 8 = 4 := by decide
  have hb16 : binBitLength (2 * 8) = 5 := by decide
  have hb5 : binBitLength ((2 * 8 - 1) / 3) = 3 := by decide
  rw [hb8, hb16, hb5] at hm8
  have hbr : (q_B ^ 5 * p_B ^ 3 + q_B ^ 3 * p_B ^ 5) * p_B ^ 4 ≤
      q_B ^ 4 * (p_B ^ 5 * p_B ^ 3) :=
    nat_mul_le_cancel_left_w5 qTheta _ _ hq_pos
      (Nat.le_trans hm8 (Nat.mul_le_mul_right _ hw.2.1))
  let P := q_B ^ 3 * p_B ^ 7
  have hP_pos : P > 0 := by
    have h1 := nat_pow_pos_of_pos q_B (by omega) 3
    have h2 := nat_pow_pos_of_pos p_B (by omega) 7
    have hm := Nat.mul_le_mul h1 h2
    dsimp [P]; omega
  have hlhs : (q_B ^ 5 * p_B ^ 3 + q_B ^ 3 * p_B ^ 5) * p_B ^ 4 = P * (q_B ^ 2 + p_B ^ 2) := by
    dsimp [P]
    have hq5 : q_B ^ 5 = q_B ^ 3 * q_B ^ 2 := Nat.pow_add q_B 3 2
    have hp7 : p_B ^ 3 * p_B ^ 4 = p_B ^ 7 := (Nat.pow_add p_B 3 4).symm
    have hp9 : p_B ^ 5 * p_B ^ 4 = p_B ^ 7 * p_B ^ 2 := by
      rw [← Nat.pow_add p_B 5 4, ← Nat.pow_add p_B 7 2]
    rw [Nat.add_mul, Nat.mul_add, hq5]
    calc
      q_B ^ 3 * q_B ^ 2 * p_B ^ 3 * p_B ^ 4 + q_B ^ 3 * p_B ^ 5 * p_B ^ 4
          = q_B ^ 3 * (p_B ^ 3 * p_B ^ 4) * q_B ^ 2 + q_B ^ 3 * (p_B ^ 5 * p_B ^ 4) := by ac_rfl
      _ = q_B ^ 3 * p_B ^ 7 * q_B ^ 2 + q_B ^ 3 * (p_B ^ 7 * p_B ^ 2) := by rw [hp7, hp9]
      _ = q_B ^ 3 * p_B ^ 7 * q_B ^ 2 + q_B ^ 3 * p_B ^ 7 * p_B ^ 2 := by ac_rfl
  have hrhs : q_B ^ 4 * (p_B ^ 5 * p_B ^ 3) = P * (q_B * p_B) := by
    dsimp [P]
    have hq4 : q_B ^ 4 = q_B ^ 3 * q_B := Nat.pow_succ q_B 3
    have hp8 : p_B ^ 5 * p_B ^ 3 = p_B ^ 7 * p_B := by
      rw [← Nat.pow_add p_B 5 3, ← Nat.pow_succ p_B 7]
    rw [hq4, hp8]
    ac_rfl
  rw [hlhs, hrhs] at hbr
  have hquad : q_B ^ 2 + p_B ^ 2 ≤ q_B * p_B :=
    nat_mul_le_cancel_left_w5 P _ _ hP_pos hbr
  by_cases hle : q_B ≤ p_B
  · have hm : q_B * p_B ≤ p_B ^ 2 := by rw [Nat.pow_two]; exact Nat.mul_le_mul_right p_B hle
    have hq2 : q_B ^ 2 ≥ 1 := nat_pow_pos_of_pos q_B (by omega) 2
    omega
  · have hm : q_B * p_B ≤ q_B ^ 2 := by rw [Nat.pow_two]; exact Nat.mul_le_mul_left q_B (by omega)
    have hp2 : p_B ^ 2 ≥ 1 := nat_pow_pos_of_pos p_B (by omega) 2
    omega

-- 2-step Mod-`9` lookahead helpers: `r = 6` ONLY occurs at `x % 9 = 8`, where `128 * x % 9 = 7` (`r = 5`).

private theorem mod9ShiftTo8_le5_of_ne8 (z : Nat) (hz3 : z % 3 ≠ 0) (hz8 : z % 9 ≠ 8) :
    mod9ShiftTo8 z ≤ 5 := by
  unfold mod9ShiftTo8
  have hr_lt : z % 9 < 9 := Nat.mod_lt z (by decide)
  rcases (show z % 9 = 1 ∨ z % 9 = 2 ∨ z % 9 = 4 ∨ z % 9 = 5 ∨ z % 9 = 7 by omega) with
    h | h | h | h | h <;> simp [h]

private theorem preimageBranchNext_le64_of_ne8 (wNum wDen : Nat -> Nat) (z : Nat)
    (hz3 : z % 3 ≠ 0) (hz8 : z % 9 ≠ 8) :
    preimageBranchNext wNum wDen z ≤ 64 * z := by
  have hr5 := mod9ShiftTo8_le5_of_ne8 z hz3 hz8
  have hp32 : 2 ^ mod9ShiftTo8 z ≤ 32 := by simpa using pow2_mono_nat hr5
  have hm32 : 2 ^ mod9ShiftTo8 z * z ≤ 32 * z := Nat.mul_le_mul_right z hp32
  unfold preimageBranchNext; dsimp only
  by_cases hc : 2 * wNum (2 * (2 ^ mod9ShiftTo8 z * z)) * wDen (2 ^ mod9ShiftTo8 z * z) ≤
      wNum (2 ^ mod9ShiftTo8 z * z) * wDen (2 * (2 ^ mod9ShiftTo8 z * z))
  · rw [ite_true_of_w10 hc]; omega
  · rw [ite_false_of_w10 hc]; omega

private theorem preimageBranchNext_eventual_step_w12
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
  have hm_ge2x : m ≥ 2 * x := Nat.mul_le_mul_right x hp_lo
  have hm_le : m ≤ 64 * x := Nat.mul_le_mul_right x hp_hi
  have hm_m3 : m % 3 = 2 := by omega
  have hy1_eq : y1 = 6 * (m / 9) + 5 := by dsimp [y1]; omega
  have heven_step : ∀ z : Nat, z ≥ 2 * M_0 -> wNum (2 * z) * wDen z ≤ wNum z * wDen (2 * z) := by
    intro z hz
    by_cases hz2 : z % 3 = 2
    · let nOdd := (2 * z - 1) / 3
      have hdn_pos : wDen nOdd > 0 := (hw.2.2.1 nOdd (by dsimp [nOdd]; omega)).2
      have hpre_z := hw.2.2.2.2 z (by omega) hz2
      dsimp only at hpre_z
      have hbr_z : (wNum (2 * z) * wDen nOdd + wNum nOdd * wDen (2 * z)) * wDen z ≤
          wNum z * (wDen (2 * z) * wDen nOdd) :=
        nat_mul_le_cancel_left_w5 qTheta _ _ hq_pos
          (Nat.le_trans hpre_z (Nat.mul_le_mul_right _ hw.2.1))
      have hdrop : (wNum (2 * z) * wDen z) * wDen nOdd ≤ (wNum z * wDen (2 * z)) * wDen nOdd := by
        have hl : (wNum (2 * z) * wDen z) * wDen nOdd = (wNum (2 * z) * wDen nOdd) * wDen z := by ac_rfl
        have hr : (wNum z * wDen (2 * z)) * wDen nOdd = wNum z * (wDen (2 * z) * wDen nOdd) := by ac_rfl
        rw [hl, hr]; rw [Nat.add_mul] at hbr_z; omega
      exact nat_mul_le_cancel_right_w5 (wDen nOdd) _ _ hdn_pos hdrop
    · exact nat_mul_le_cancel_left_w5 qTheta _ _ hq_pos
        (Nat.le_trans (hw.2.2.2.1 z (by omega) hz2) (Nat.mul_le_mul_right _ hw.2.1))
  have hpow2_le : ∀ d : Nat, wNum (2 ^ d * x) * wDen x ≤ wNum x * wDen (2 ^ d * x) := by
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
  have hb0_pos : wDen y0 > 0 := (hw.2.2.1 y0 (by dsimp [y0]; omega)).2
  have hb1_pos : wDen y1 > 0 := (hw.2.2.1 y1 (by rw [hy1_eq]; omega)).2
  unfold preimageBranchNext; dsimp only
  change x < (if 2 * wNum y0 * wDen m ≤ wNum m * wDen y0 then y0 else y1) ∧ _
  by_cases hcond : 2 * wNum y0 * wDen m ≤ wNum m * wDen y0
  · rw [ite_true_of_w10 hcond]
    exact ⟨by dsimp [y0]; omega, by dsimp [y0]; omega, by dsimp [y0]; omega,
           rat_le_trans_pos_w5 _ _ (wNum m) (wDen m) _ _ hbm_pos hcond hm_le_x⟩
  · rw [ite_false_of_w10 hcond]
    have hc1 : 2 * wNum y1 * wDen m ≤ wNum m * wDen y1 := by
      by_cases hc : 2 * wNum y1 * wDen m ≤ wNum m * wDen y1
      · exact hc
      · exfalso
        have hm0 := Nat.mul_lt_mul_of_pos_right (by omega : wNum m * wDen y0 < 2 * wNum y0 * wDen m) hb1_pos
        have hm1 := Nat.mul_lt_mul_of_pos_right (by omega : wNum m * wDen y1 < 2 * wNum y1 * wDen m) hb0_pos
        have hl0 : (wNum m * wDen y0) * wDen y1 = wNum m * (wDen y0 * wDen y1) := by ac_rfl
        have hl1 : (wNum m * wDen y1) * wDen y0 = wNum m * (wDen y0 * wDen y1) := by ac_rfl
        have hr0 : (2 * wNum y0 * wDen m) * wDen y1 = 2 * ((wNum y0 * wDen y1) * wDen m) := by ac_rfl
        have hr1 : (2 * wNum y1 * wDen m) * wDen y0 = 2 * ((wNum y1 * wDen y0) * wDen m) := by ac_rfl
        rw [hl0, hr0] at hm0; rw [hl1, hr1] at hm1; rw [Nat.add_mul] at hbr
        omega
    exact ⟨by dsimp [y1]; omega, by rw [hy1_eq]; omega, by dsimp [y1]; omega,
           rat_le_trans_pos_w5 _ _ (wNum m) (wDen m) _ _ hbm_pos hc1 hm_le_x⟩

private theorem preimageBranchNext_two_step_le_8192 (wNum wDen : Nat -> Nat) (x : Nat)
    (hx3 : x % 3 ≠ 0) :
    preimageBranchNext wNum wDen (preimageBranchNext wNum wDen x) ≤ 8192 * x := by
  have h128 : ∀ z : Nat, z % 3 ≠ 0 ->
      preimageBranchNext wNum wDen z ≤ 128 * z ∧ (preimageBranchNext wNum wDen z) % 3 ≠ 0 := by
    intro z hz3
    rcases mod9ShiftTo8_spec z hz3 with ⟨_, hr6, hm9⟩
    let m := 2 ^ mod9ShiftTo8 z * z
    change m % 9 = 8 at hm9
    have hm_le : m ≤ 64 * z := Nat.mul_le_mul_right z (by simpa using pow2_mono_nat hr6)
    have hy1_eq : (2 * m - 1) / 3 = 6 * (m / 9) + 5 := by omega
    unfold preimageBranchNext; dsimp only
    by_cases hc : 2 * wNum (2 * m) * wDen m ≤ wNum m * wDen (2 * m)
    · rw [ite_true_of_w10 hc]; exact ⟨by omega, by omega⟩
    · rw [ite_false_of_w10 hc]; exact ⟨by omega, by rw [hy1_eq]; omega⟩
  by_cases hx8 : x % 9 = 8
  · have hr_eq6 : mod9ShiftTo8 x = 6 := by unfold mod9ShiftTo8; simp [hx8]
    have hm_eq : 2 ^ mod9ShiftTo8 x * x = 64 * x := by rw [hr_eq6]
    have hstep1 : preimageBranchNext wNum wDen x =
        if 2 * wNum (128 * x) * wDen (64 * x) ≤ wNum (64 * x) * wDen (128 * x)
        then 128 * x else (128 * x - 1) / 3 := by
      unfold preimageBranchNext; dsimp only
      rw [hm_eq, show 2 * (64 * x) = 128 * x by omega]
    rw [hstep1]
    by_cases hc : 2 * wNum (128 * x) * wDen (64 * x) ≤ wNum (64 * x) * wDen (128 * x)
    · rw [ite_true_of_w10 hc]
      have hy0_9 : (128 * x) % 9 = 7 := by rw [Nat.mul_mod, hx8]
      have h2 := preimageBranchNext_le64_of_ne8 wNum wDen (128 * x) (by omega) (by omega)
      omega
    · rw [ite_false_of_w10 hc]
      let y1 := (128 * x - 1) / 3
      have hm64_9 : (64 * x) % 9 = 8 := by rw [Nat.mul_mod, hx8]
      have hy1_eq : y1 = 6 * ((64 * x) / 9) + 5 := by dsimp [y1]; omega
      have hy1_3 : y1 % 3 ≠ 0 := by rw [hy1_eq]; omega
      have h2 := (h128 y1 hy1_3).1
      dsimp [y1] at h2 ⊢; omega
  · have h1_le := preimageBranchNext_le64_of_ne8 wNum wDen x hx3 hx8
    have h1_3 := (h128 x hx3).2
    have h2_le := (h128 (preimageBranchNext wNum wDen x) h1_3).1
    omega

/--
  Theorem W12.3b (`eventual_exp_bitlength_critical_base_impossibility`,
  choice-free `zero custom axioms`):
  2-Step Mod-`9` Lookahead Bound & Eventual (`∀ M_0 ≥ 3`) Sub-Critical Exponential-`binBitLength`
  Denominator Impossibility (`Branch P1.2`, `W12_H1`):
  1. **Universal 2-Step Mod-`9` Lookahead Bound (`∀ x ≥ 5, x % 3 ≠ 0`)**:
     `preimageBranchNext wNum wDen (preimageBranchNext wNum wDen x) ≤ 8192 * x` (`= 2 ^ 13 * x`),
     and bases `(10, 9)` and `(11, 10)` both satisfy `10 ^ 13 < 4 * 9 ^ 13` and `11 ^ 13 < 4 * 10 ^ 13`!
  2. **Eventual Unrestricted-Numerator Impossibility (`∀ M_0 ≥ 3`, `p_B ^ 13 < 4 * q_B ^ 13`)**:
     For ANY threshold `M_0 ≥ 3`, ANY `wNum, wDen` (with ZERO upper bound on `wNum`!), and ANY
     `p_B, q_B ≥ 1` with `p_B ^ 13 < 4 * q_B ^ 13`: if
       `∀ n ≥ M_0, q_B ^ binBitLength n * wDen n ≤ C_den * p_B ^ binBitLength n`,
     then `¬ IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta`!
-/
theorem eventual_exp_bitlength_critical_base_impossibility :
    ((∀ (wNum wDen : Nat -> Nat) (x : Nat),
        x % 3 ≠ 0 ->
        preimageBranchNext wNum wDen (preimageBranchNext wNum wDen x) ≤ 8192 * x) ∧
     10 ^ 13 < 4 * 9 ^ 13 ∧
     11 ^ 13 < 4 * 10 ^ 13) ∧
    (∀ (M_0 : Nat), M_0 ≥ 3 ->
      ∀ (wNum wDen : Nat -> Nat) (C_den p_B q_B pTheta qTheta : Nat),
        p_B ≥ 1 -> q_B ≥ 1 -> p_B ^ 13 < 4 * q_B ^ 13 ->
        (∀ n : Nat, n ≥ M_0 -> q_B ^ binBitLength n * wDen n ≤ C_den * p_B ^ binBitLength n) ->
        ¬ IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta) := by
  refine ⟨⟨preimageBranchNext_two_step_le_8192, by decide, by decide⟩, ?_⟩
  intro M_0 hM0 wNum wDen C_den p_B q_B pTheta qTheta hpB hqB hcrit hden hw
  by_cases hle_pq : p_B ≤ q_B
  · -- When `p_B ≤ q_B`, `wDen n ≤ C_den = C_den * (binBitLength n)^0`:
    have hconst : ∀ n : Nat, n ≥ M_0 -> wDen n ≤ C_den * (binBitLength n) ^ 0 := by
      intro n hn
      rw [Nat.pow_zero, Nat.mul_one]
      have h1 := hden n hn
      have h2 : C_den * p_B ^ binBitLength n ≤ C_den * q_B ^ binBitLength n :=
        Nat.mul_le_mul_left C_den (pow_mono_base_w12s p_B q_B hle_pq (binBitLength n))
      have h3 : q_B ^ binBitLength n * wDen n ≤ q_B ^ binBitLength n * C_den := by
        rw [Nat.mul_comm (q_B ^ binBitLength n) C_den]; exact Nat.le_trans h1 h2
      exact nat_mul_le_cancel_left_w5 (q_B ^ binBitLength n) _ _
        (nat_pow_pos_of_pos q_B (by omega) _) h3
    exact eventual_poly_bitlength_denominator_preimage_impossibility.2 M_0 hM0
      wNum wDen C_den 0 pTheta qTheta hconst hw
  · -- When `q_B < p_B`, run 2-step `preimageBranchIter (2 * k) x0` (`x0 = 6 * M_0 + 5`):
    have hqp : q_B ≤ p_B := by omega
    let x0 := 6 * M_0 + 5
    have hiter2 : ∀ k : Nat,
        let x2k := preimageBranchIter wNum wDen (2 * k) x0
        x2k ≥ x0 + 2 * k ∧ x2k % 3 ≠ 0 ∧ x2k < 2 ^ (13 * k + x0) ∧
        4 ^ k * wNum x2k * wDen x0 ≤ wNum x0 * wDen x2k := by
      intro k; induction k with
      | zero =>
        simp only [Nat.mul_zero, preimageBranchIter, Nat.add_zero, Nat.zero_add,
                   Nat.pow_zero, Nat.one_mul]
        exact ⟨Nat.le_refl x0, by dsimp [x0]; omega, id_lt_pow2_w12s x0, Nat.le_refl _⟩
      | succ k' ih =>
        rcases ih with ⟨hge, hm3, hlt, hrat⟩
        let x2k := preimageBranchIter wNum wDen (2 * k') x0
        change x2k ≥ x0 + 2 * k' at hge
        change x2k % 3 ≠ 0 at hm3
        change x2k < 2 ^ (13 * k' + x0) at hlt
        change 4 ^ k' * wNum x2k * wDen x0 ≤ wNum x0 * wDen x2k at hrat
        rcases preimageBranchNext_eventual_step_w12 M_0 hM0 wNum wDen pTheta qTheta x2k
          hw (by dsimp [x0] at hge; omega) hm3 with ⟨hgt1, hm3_1, _, hrat1⟩
        let y1 := preimageBranchNext wNum wDen x2k
        rcases preimageBranchNext_eventual_step_w12 M_0 hM0 wNum wDen pTheta qTheta y1
          hw (by dsimp [x0] at hge; omega) hm3_1 with ⟨hgt2, hm3_2, _, hrat2⟩
        let y2 := preimageBranchNext wNum wDen y1
        have hy2_8192 : y2 ≤ 8192 * x2k := preimageBranchNext_two_step_le_8192 wNum wDen x2k hm3
        have hy2_lt : y2 < 2 ^ (13 * (k' + 1) + x0) := by
          have hp13 : 2 ^ (13 * (k' + 1) + x0) = 8192 * 2 ^ (13 * k' + x0) := by
            rw [show 13 * (k' + 1) + x0 = (13 * k' + x0) + 13 by omega,
                Nat.pow_add 2 (13 * k' + x0) 13, Nat.mul_comm _ (2 ^ 13)]
          rw [hp13]; omega
        have hstep4 : 4 * wNum y2 * wDen x2k ≤ wNum x2k * wDen y2 := by
          have hrat2_s : (4 * wNum y2) * wDen y1 ≤ (2 * wNum y1) * wDen y2 := by
            have hm := Nat.mul_le_mul_left 2 hrat2
            have hl : 2 * (2 * wNum y2 * wDen y1) = (4 * wNum y2) * wDen y1 := by ac_rfl
            have hr : 2 * (wNum y1 * wDen y2) = (2 * wNum y1) * wDen y2 := by ac_rfl
            rwa [hl, hr] at hm
          exact rat_le_trans_pos_w5 (4 * wNum y2) (wDen y2) (2 * wNum y1) (wDen y1)
            (wNum x2k) (wDen x2k) (hw.2.2.1 y1 (by dsimp [x0] at hge; omega)).2 hrat2_s hrat1
        have hstep4k : (4 ^ (k' + 1) * wNum y2) * wDen x2k ≤ (4 ^ k' * wNum x2k) * wDen y2 := by
          have hm := Nat.mul_le_mul_left (4 ^ k') hstep4
          have hl : 4 ^ k' * (4 * wNum y2 * wDen x2k) = (4 ^ (k' + 1) * wNum y2) * wDen x2k := by
            rw [Nat.pow_succ 4 k']; ac_rfl
          have hr : 4 ^ k' * (wNum x2k * wDen y2) = (4 ^ k' * wNum x2k) * wDen y2 := by ac_rfl
          rwa [hl, hr] at hm
        have htot := rat_le_trans_pos_w5 (4 ^ (k' + 1) * wNum y2) (wDen y2)
          (4 ^ k' * wNum x2k) (wDen x2k) (wNum x0) (wDen x0)
          (hw.2.2.1 x2k (by dsimp [x0] at hge; omega)).2 hstep4k hrat
        have hiter_eq : preimageBranchIter wNum wDen (2 * (k' + 1)) x0 = y2 := by
          rw [show 2 * (k' + 1) = (2 * k' + 1) + 1 by omega]
          rfl
        dsimp only; rw [hiter_eq]
        exact ⟨by omega, hm3_2, hy2_lt, htot⟩
    let A := p_B ^ 13
    let B := 4 * q_B ^ 13
    let K_0 := wNum x0 * C_den * p_B ^ x0
    have hA1 : A ≥ 1 := nat_pow_pos_of_pos p_B (by omega) 13
    let k := K_0 * A
    have hgt_pow : K_0 * A ^ k < B ^ k := pow_gt_const_mul_pow_of_lt A B K_0 hA1 hcrit
    rcases hiter2 k with ⟨hxge, _, hxlt, hxrat⟩
    let x2k := preimageBranchIter wNum wDen (2 * k) x0
    change x2k ≥ x0 + 2 * k at hxge
    change x2k < 2 ^ (13 * k + x0) at hxlt
    change 4 ^ k * wNum x2k * wDen x0 ≤ wNum x0 * wDen x2k at hxrat
    have hwn_pos : wNum x2k ≥ 1 := (hw.2.2.1 x2k (by dsimp [x0] at hxge; omega)).1
    have hwd0_pos : wDen x0 ≥ 1 := (hw.2.2.1 x0 (by dsimp [x0]; omega)).2
    have h4k_le : 4 ^ k ≤ wNum x0 * wDen x2k := by
      have hm1 := Nat.mul_le_mul_left (4 ^ k) hwn_pos
      have hm2 := Nat.mul_le_mul_left (4 ^ k * wNum x2k) hwd0_pos
      omega
    have hbl_le : binBitLength x2k ≤ 13 * k + x0 := by
      let m_bl := 13 * k + 6 * M_0 + 4
      have hm_eq : 13 * k + x0 = m_bl + 1 := by dsimp [x0, m_bl]; omega
      have hpred := (binBitLength_pow2_and_pred m_bl).2
      have hmono := binBitLength_mono x2k (2 ^ (m_bl + 1) - 1) (by rw [hm_eq] at hxlt; omega)
      rw [hpred] at hmono
      omega
    -- Lift `q_B ^ L * wDen x2k ≤ C_den * p_B ^ L` from `L := binBitLength x2k` to `N := 13 * k + x0`:
    let L := binBitLength x2k
    let N := 13 * k + x0
    let E := N - L
    have hLN : L + E = N := by dsimp [L, N, E]; omega
    have hden_N : q_B ^ N * wDen x2k ≤ C_den * p_B ^ N := by
      have hdL := hden x2k (by dsimp [x0] at hxge; omega)
      change q_B ^ L * wDen x2k ≤ C_den * p_B ^ L at hdL
      have hqE_pE : q_B ^ E ≤ p_B ^ E := pow_mono_base_w12s q_B p_B hqp E
      calc
        q_B ^ N * wDen x2k = q_B ^ E * (q_B ^ L * wDen x2k) := by
          rw [← hLN, Nat.pow_add q_B L E]; ac_rfl
        _ ≤ p_B ^ E * (C_den * p_B ^ L) := Nat.mul_le_mul hqE_pE hdL
        _ = C_den * p_B ^ N := by
          rw [← hLN, Nat.pow_add p_B L E]; ac_rfl
    -- Multiply `4^k ≤ wNum x0 * wDen x2k` by `q_B ^ N`:
    have hBk_le : B ^ k * q_B ^ x0 ≤ (K_0 * A ^ k) * 1 := by
      rw [Nat.mul_one]
      have hBk_eq : B ^ k * q_B ^ x0 = q_B ^ N * 4 ^ k := by
        dsimp [B, N]
        rw [mul_pow_w12s 4 (q_B ^ 13) k, ← Nat.pow_mul q_B 13 k, Nat.pow_add q_B (13 * k) x0]
        ac_rfl
      have hAk_eq : wNum x0 * (C_den * p_B ^ N) = K_0 * A ^ k := by
        dsimp [K_0, A, N]
        rw [Nat.pow_add p_B (13 * k) x0, Nat.pow_mul p_B 13 k]
        ac_rfl
      calc
        B ^ k * q_B ^ x0 = q_B ^ N * 4 ^ k := hBk_eq
        _ ≤ q_B ^ N * (wNum x0 * wDen x2k) := Nat.mul_le_mul_left (q_B ^ N) h4k_le
        _ = wNum x0 * (q_B ^ N * wDen x2k) := by ac_rfl
        _ ≤ wNum x0 * (C_den * p_B ^ N) := Nat.mul_le_mul_left (wNum x0) hden_N
        _ = K_0 * A ^ k := hAk_eq
    have hqx0_pos : q_B ^ x0 ≥ 1 := nat_pow_pos_of_pos q_B (by omega) x0
    have hBk_self : B ^ k ≤ B ^ k * q_B ^ x0 := by
      simpa using Nat.mul_le_mul_left (B ^ k) hqx0_pos
    omega

-- Reverse Syracuse odd-branch chain `x_t = 2^(t + 1) * 3^(2*m - t) - 1` (`0 ≤ t ≤ 2*m`).

def revSyracuseNode (m t : Nat) : Nat :=
  2 ^ (t + 1) * 3 ^ (2 * m - t) - 1

private theorem exists_pow2_gt_const_mul_bitlen_pow_ge (M_min C D : Nat) :
    ∃ k : Nat, k ≥ M_min ∧ C * (7 * k + 3) ^ D < 2 ^ k := by
  let m := C + M_min + 3 * D + 5
  let t := m + m
  let k := 2 ^ t
  refine ⟨k, ?_, ?_⟩
  · have hm_lt : m < 2 ^ m := id_lt_pow2_w12s m
    have ht_gt : t ≥ m := by dsimp [t]; omega
    exact Nat.le_trans (by dsimp [m]; omega : M_min ≤ m)
      (Nat.le_trans (Nat.le_of_lt hm_lt) (pow2_mono_nat ht_gt))
  · have hm_ge5 : m ≥ 5 := by dsimp [m]; omega
    have hk_pos : k ≥ 1 := pow2_pos_nat t
    have hlin_lt : 7 * k + 3 < 2 ^ (t + 4) := by
      rw [Nat.pow_add 2 t 4]; change 7 * k + 3 < k * 16; omega
    have hpow_le : (7 * k + 3) ^ D ≤ 2 ^ ((t + 4) * D) := by
      have hm1 := pow_mono_base_w12s (7 * k + 3) (2 ^ (t + 4)) (Nat.le_of_lt hlin_lt) D
      rwa [← Nat.pow_mul 2 (t + 4) D] at hm1
    have hC_lt : C + 1 ≤ 2 ^ C := id_lt_pow2_w12s C
    have hbase_pos : (7 * k + 3) ^ D ≥ 1 := nat_pow_pos_of_pos (7 * k + 3) (by omega) D
    have hprod_lt : C * (7 * k + 3) ^ D < 2 ^ (C + (t + 4) * D) := by
      have h1 : C * (7 * k + 3) ^ D < (C + 1) * (7 * k + 3) ^ D := by
        rw [Nat.add_mul, Nat.one_mul]; omega
      have h2 := Nat.mul_le_mul hC_lt hpow_le
      rw [← Nat.pow_add 2 C ((t + 4) * D)] at h2
      exact Nat.lt_of_lt_of_le h1 h2
    have hexp_le : C + (t + 4) * D ≤ k := by
      have ht4 : t + 4 ≤ 3 * m := by dsimp [t]; omega
      have hmD : (t + 4) * D ≤ m * (3 * D) := by
        have hm1 := Nat.mul_le_mul_right D ht4
        rwa [Nat.mul_comm 3 m, Nat.mul_assoc m 3 D] at hm1
      have hsum_mm : C + (t + 4) * D ≤ m * m := by
        have h1 : C + (t + 4) * D ≤ m * (1 + 3 * D) := by
          rw [Nat.mul_add m 1 (3 * D)]
          have hc_m : C ≤ m * 1 := by dsimp [m]; omega
          omega
        exact Nat.le_trans h1 (Nat.mul_le_mul_left m (by dsimp [m]; omega))
      have hm_pow : m ≤ 2 ^ m := Nat.le_of_lt (id_lt_pow2_w12s m)
      have hmm_k : m * m ≤ k := by
        have hm2 := Nat.mul_le_mul hm_pow hm_pow
        rwa [← Nat.pow_add 2 m m] at hm2
      exact Nat.le_trans hsum_mm hmm_k
    exact Nat.lt_of_lt_of_le hprod_lt (pow2_mono_nat hexp_le)

/--
  Theorem W12.3c (`eventual_poly_num_any_exp_base_bitlength_impossibility`,
  `zero custom axioms`):
  Reverse Syracuse Odd-Branch Chains (`x_t = 2^(t+1) * 3^(2m-t) - 1`) & Eventual (`∀ M_0 ≥ 3`)
  All-Base Impossibility of Polynomial-Numerator Exponential-`binBitLength` Preimage Weights
  (`Branch P1.2`, `W12_H1`):
  1. **Exact Reverse Syracuse Chain & Bit-Length Drop (`∀ m ≥ 1, ∀ s ≥ 1`)**:
     `revSyracuseNode m 0 = 2 * 9 ^ m - 1`, `revSyracuseNode m (2 * m) = 2 ^ (2 * m + 1) - 1`,
     `∀ t < 2 * m, revSyracuseNode m t % 3 = 2 ∧ (2 * revSyracuseNode m t - 1) / 3 = revSyracuseNode m (t + 1)`,
     and at `m = 2 * s`: `binBitLength (revSyracuseNode (2 * s) (4 * s)) = 4 * s + 1`,
     `6 * s + 2 ≤ binBitLength (revSyracuseNode (2 * s) 0) ≤ 7 * s + 1` (dropping `≥ 2 * s + 1` bits)!
  2. **Universal Eventual All-Base Impossibility (`∀ M_0 ≥ 3`, `∀ p_B, q_B ≥ 1`)**:
     For ANY `M_0 ≥ 3`, ANY `p_B ≥ 1, q_B ≥ 1`, ANY `c_1 ≥ 1`, and ANY `C_den, C_num, D_num, pTheta, qTheta`:
     if `∀ n ≥ M_0`:
       `wNum n ≤ C_num * (binBitLength n) ^ D_num` AND
       `c_1 * p_B ^ binBitLength n ≤ q_B ^ binBitLength n * wDen n` AND
       `q_B ^ binBitLength n * wDen n ≤ C_den * p_B ^ binBitLength n`,
     then `¬ IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta`!
     (Refuting ALL `OCN`, `PDA`, finite-automaton, Stern–Brocot, and digit-count numerators divided
     by ANY rational exponential base `(p_B / q_B)^binBitLength(n)`!)
-/
theorem eventual_poly_num_any_exp_base_bitlength_impossibility :
    ((∀ m : Nat,
        revSyracuseNode m 0 = 2 * 9 ^ m - 1 ∧
        revSyracuseNode m (2 * m) = 2 ^ (2 * m + 1) - 1 ∧
        (∀ t : Nat, t < 2 * m ->
          revSyracuseNode m t % 3 = 2 ∧
          (2 * revSyracuseNode m t - 1) / 3 = revSyracuseNode m (t + 1))) ∧
     (∀ s : Nat, s ≥ 1 ->
        binBitLength (revSyracuseNode (2 * s) (4 * s)) = 4 * s + 1 ∧
        6 * s + 2 ≤ binBitLength (revSyracuseNode (2 * s) 0) ∧
        binBitLength (revSyracuseNode (2 * s) 0) ≤ 7 * s + 1)) ∧
    (∀ (M_0 : Nat), M_0 ≥ 3 ->
      ∀ (wNum wDen : Nat -> Nat) (c_1 C_den C_num D_num p_B q_B pTheta qTheta : Nat),
        c_1 ≥ 1 -> p_B ≥ 1 -> q_B ≥ 1 ->
        (∀ n : Nat, n ≥ M_0 -> wNum n ≤ C_num * (binBitLength n) ^ D_num) ->
        (∀ n : Nat, n ≥ M_0 ->
          c_1 * p_B ^ binBitLength n ≤ q_B ^ binBitLength n * wDen n ∧
          q_B ^ binBitLength n * wDen n ≤ C_den * p_B ^ binBitLength n) ->
        ¬ IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta) := by
  have hchain : ∀ m : Nat,
      revSyracuseNode m 0 = 2 * 9 ^ m - 1 ∧
      revSyracuseNode m (2 * m) = 2 ^ (2 * m + 1) - 1 ∧
      (∀ t : Nat, t < 2 * m ->
        revSyracuseNode m t % 3 = 2 ∧
        (2 * revSyracuseNode m t - 1) / 3 = revSyracuseNode m (t + 1)) := by
    intro m
    refine ⟨?_, ?_, ?_⟩
    · unfold revSyracuseNode
      rw [Nat.sub_zero, ← pow9_eq_pow3_double m]
    · unfold revSyracuseNode
      rw [Nat.sub_self, Nat.pow_zero, Nat.mul_one]
    · intro t ht
      unfold revSyracuseNode
      have hsp : 2 * m - t = (2 * m - 1 - t) + 1 := by omega
      rw [hsp, Nat.pow_succ 3 (2 * m - 1 - t)]
      have hp2_ge2 : 2 ^ (t + 1) ≥ 2 := by simpa using pow2_mono_nat (by omega : 1 ≤ t + 1)
      have hp3_pos : 3 ^ (2 * m - 1 - t) ≥ 1 := pow3_pos_nat _
      have hprod_ge2 : 2 ^ (t + 1) * 3 ^ (2 * m - 1 - t) ≥ 2 :=
        Nat.le_trans hp2_ge2 (by simpa using Nat.mul_le_mul_left (2 ^ (t + 1)) hp3_pos)
      have hrew : 2 ^ (t + 1) * (3 ^ (2 * m - 1 - t) * 3) =
          3 * (2 ^ (t + 1) * 3 ^ (2 * m - 1 - t)) := by ac_rfl
      have h2t2 : 2 ^ (t + 1 + 1) * 3 ^ (2 * m - (t + 1)) =
          2 * (2 ^ (t + 1) * 3 ^ (2 * m - 1 - t)) := by
        rw [show 2 * m - (t + 1) = 2 * m - 1 - t by omega, Nat.pow_succ 2 (t + 1)]
        ac_rfl
      rw [hrew, h2t2]
      generalize 2 ^ (t + 1) * 3 ^ (2 * m - 1 - t) = P at hprod_ge2 ⊢
      omega
  have hbits : ∀ s : Nat, s ≥ 1 ->
      binBitLength (revSyracuseNode (2 * s) (4 * s)) = 4 * s + 1 ∧
      6 * s + 2 ≤ binBitLength (revSyracuseNode (2 * s) 0) ∧
      binBitLength (revSyracuseNode (2 * s) 0) ≤ 7 * s + 1 := by
    intro s hs1
    have hend : revSyracuseNode (2 * s) (4 * s) = 2 ^ ((4 * s) + 1) - 1 := by
      have h := (hchain (2 * s)).2.1
      rwa [show 2 * (2 * s) = 4 * s by omega] at h
    have h0_eq : revSyracuseNode (2 * s) 0 = 2 * 81 ^ s - 1 := by
      rw [(hchain (2 * s)).1, show (81 : Nat) = 9 ^ 2 from rfl, pow_pow_eq_mul_w5 9 2 s]
    have hbl_end : binBitLength (revSyracuseNode (2 * s) (4 * s)) = 4 * s + 1 := by
      rw [hend]; exact (binBitLength_pow2_and_pred (4 * s)).2
    -- `64 ^ s < 81 ^ s` for `s ≥ 1`:
    have h64_lt_81 : 64 ^ s < 81 ^ s := by
      have hst : ∀ n : Nat, 64 ^ (n + 1) < 81 ^ (n + 1) := by
        intro n; induction n with
        | zero => decide
        | succ n' ih =>
          rw [Nat.pow_succ 64 (n' + 1), Nat.pow_succ 81 (n' + 1)]
          have hp81 : 0 < 81 ^ (n' + 1) := nat_pow_pos_of_pos 81 (by decide) (n' + 1)
          exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 64 (Nat.le_of_lt ih))
            (Nat.mul_lt_mul_of_pos_left (by decide : 64 < 81) hp81)
      rw [show s = (s - 1) + 1 by omega]
      exact hst (s - 1)
    have h64_pow2 : 64 ^ s = 2 ^ (6 * s) := by
      rw [show (64 : Nat) = 2 ^ 6 from rfl, pow_pow_eq_mul_w5 2 6 s]
    have hlo_0 : 2 ^ (6 * s + 1) ≤ revSyracuseNode (2 * s) 0 := by
      rw [h0_eq, Nat.pow_succ 2 (6 * s), Nat.mul_comm (2 ^ (6 * s)) 2, ← h64_pow2]
      omega
    have hbl_lo : 6 * s + 2 ≤ binBitLength (revSyracuseNode (2 * s) 0) := by
      have hp := (binBitLength_pow2_and_pred (6 * s + 1)).1
      have hm := binBitLength_mono (2 ^ (6 * s + 1)) (revSyracuseNode (2 * s) 0) hlo_0
      omega
    have h81_le_128 : 81 ^ s ≤ 128 ^ s := pow_mono_base_w12s 81 128 (by decide) s
    have h128_pow2 : 128 ^ s = 2 ^ (7 * s) := by
      rw [show (128 : Nat) = 2 ^ 7 from rfl, pow_pow_eq_mul_w5 2 7 s]
    have hhi_0 : revSyracuseNode (2 * s) 0 ≤ 2 ^ ((7 * s) + 1) - 1 := by
      rw [h0_eq, Nat.pow_succ 2 (7 * s), Nat.mul_comm (2 ^ (7 * s)) 2, ← h128_pow2]
      omega
    have hbl_hi : binBitLength (revSyracuseNode (2 * s) 0) ≤ 7 * s + 1 := by
      have hp := (binBitLength_pow2_and_pred (7 * s)).2
      have hm := binBitLength_mono (revSyracuseNode (2 * s) 0) (2 ^ ((7 * s) + 1) - 1) hhi_0
      omega
    exact ⟨hbl_end, hbl_lo, hbl_hi⟩
  refine ⟨⟨hchain, hbits⟩, ?_⟩
  intro M_0 hM0 wNum wDen c_1 C_den C_num D_num p_B q_B pTheta qTheta hc1 hpB hqB hnum hden hw
  by_cases hle_pq : p_B ≤ q_B
  · have hcrit : p_B ^ 13 < 4 * q_B ^ 13 := by
      have h1 := pow_mono_base_w12s p_B q_B hle_pq 13
      have h2 := nat_pow_pos_of_pos q_B (by omega) 13
      omega
    exact eventual_exp_bitlength_critical_base_impossibility.2 M_0 hM0
      wNum wDen C_den p_B q_B pTheta qTheta hpB hqB hcrit (fun n hn => (hden n hn).2) hw
  · -- `p_B ≥ q_B + 1`:
    have hp_gt : q_B + 1 ≤ p_B := by omega
    have hq_pos : qTheta > 0 := Nat.lt_of_lt_of_le hw.1 hw.2.1
    let K_const := C_den * C_num * q_B ^ D_num
    rcases exists_pow2_gt_const_mul_bitlen_pow_ge M_0 K_const D_num with ⟨k, hk_M0, hk_gt⟩
    let s := q_B * k
    have hs_M0 : s ≥ M_0 := by
      have hm : 1 * k ≤ q_B * k := Nat.mul_le_mul_right k hqB
      dsimp [s]; omega
    let m := 2 * s
    -- Prove every node `revSyracuseNode m t` (`t ≤ 2 * m`) is `≥ M_0` and telescope `w(x_{2m}) ≤ w(x_0)`:
    have hnode_ge : ∀ t : Nat, t ≤ 2 * m -> revSyracuseNode m t ≥ M_0 := by
      intro t ht
      unfold revSyracuseNode
      have h1 : 2 ^ (t + 1) * 3 ^ (2 * m - t) ≥ 2 ^ (t + 1) * 2 ^ (2 * m - t) :=
        Nat.mul_le_mul_left _ (pow2_le_pow3 _)
      rw [← Nat.pow_add, show (t + 1) + (2 * m - t) = 2 * m + 1 by omega] at h1
      have h2 : 2 * m + 1 < 2 ^ (2 * m + 1) := id_lt_pow2_w12s (2 * m + 1)
      dsimp [m] at h1 h2 ⊢; omega
    have hstep_rs : ∀ t : Nat, t < 2 * m ->
        wNum (revSyracuseNode m (t + 1)) * wDen (revSyracuseNode m t) ≤
          wNum (revSyracuseNode m t) * wDen (revSyracuseNode m (t + 1)) := by
      intro t ht
      let xt := revSyracuseNode m t
      let xn := revSyracuseNode m (t + 1)
      rcases (hchain m).2.2 t ht with ⟨hxt_m3, hnOdd_eq⟩
      have hxt_M0 : xt ≥ M_0 := hnode_ge t (Nat.le_of_lt ht)
      have hpre := hw.2.2.2.2 xt hxt_M0 hxt_m3
      dsimp only at hpre
      rw [hnOdd_eq] at hpre
      have hbr : (wNum (2 * xt) * wDen xn + wNum xn * wDen (2 * xt)) * wDen xt ≤
          wNum xt * (wDen (2 * xt) * wDen xn) :=
        nat_mul_le_cancel_left_w5 qTheta _ _ hq_pos
          (Nat.le_trans hpre (Nat.mul_le_mul_right _ hw.2.1))
      have hd2_pos : wDen (2 * xt) > 0 := (hw.2.2.1 (2 * xt) (by omega)).2
      have hdrop : (wNum xn * wDen xt) * wDen (2 * xt) ≤ (wNum xt * wDen xn) * wDen (2 * xt) := by
        have hl : (wNum xn * wDen xt) * wDen (2 * xt) = (wNum xn * wDen (2 * xt)) * wDen xt := by ac_rfl
        have hr : (wNum xt * wDen xn) * wDen (2 * xt) = wNum xt * (wDen (2 * xt) * wDen xn) := by ac_rfl
        rw [hl, hr]; rw [Nat.add_mul] at hbr; omega
      exact nat_mul_le_cancel_right_w5 (wDen (2 * xt)) _ _ hd2_pos hdrop
    have htele : ∀ r : Nat, r ≤ 2 * m ->
        wNum (revSyracuseNode m r) * wDen (revSyracuseNode m 0) ≤
          wNum (revSyracuseNode m 0) * wDen (revSyracuseNode m r) := by
      intro r hr; induction r with
      | zero => exact Nat.le_refl _
      | succ r' ih =>
        have hs_r := hstep_rs r' hr
        have hdr_pos : wDen (revSyracuseNode m r') > 0 :=
          (hw.2.2.1 (revSyracuseNode m r') (hnode_ge r' (Nat.le_of_lt hr))).2
        exact rat_le_trans_pos_w5 _ _ (wNum (revSyracuseNode m r')) (wDen (revSyracuseNode m r')) _ _
          hdr_pos hs_r (ih (Nat.le_of_lt hr))
    let x0 := revSyracuseNode m 0
    let xend := revSyracuseNode m (2 * m)
    have hrat_end : wDen x0 ≤ wNum x0 * wDen xend := by
      have ht := htele (2 * m) (Nat.le_refl _)
      have hwn_end : wNum xend ≥ 1 := (hw.2.2.1 xend (hnode_ge (2 * m) (Nat.le_refl _))).1
      have hm1 : 1 * wDen x0 ≤ wNum xend * wDen x0 := Nat.mul_le_mul_right _ hwn_end
      rw [Nat.one_mul] at hm1
      exact Nat.le_trans hm1 ht
    rcases hbits s (by omega) with ⟨hbl_end, hbl_lo0, hbl_hi0⟩
    have hxend_rew : revSyracuseNode (2 * s) (4 * s) = xend := by
      dsimp [xend, m]; rw [show 2 * (2 * s) = 4 * s by omega]
    rw [hxend_rew] at hbl_end
    let L0 := binBitLength x0
    let Lend := binBitLength xend
    change Lend = 4 * s + 1 at hbl_end
    change 6 * s + 2 ≤ L0 at hbl_lo0
    change L0 ≤ 7 * s + 1 at hbl_hi0
    let D_drop := L0 - Lend
    have hD_ge_s : s ≤ D_drop := by dsimp [D_drop]; omega
    have hL0_sp : Lend + D_drop = L0 := by dsimp [D_drop]; omega
    have hlo_den0 := (hden x0 (hnode_ge 0 (Nat.zero_le _))).1
    have hhi_denE := (hden xend (hnode_ge (2 * m) (Nat.le_refl _))).2
    change c_1 * p_B ^ L0 ≤ q_B ^ L0 * wDen x0 at hlo_den0
    change q_B ^ Lend * wDen xend ≤ C_den * p_B ^ Lend at hhi_denE
    -- Combine `c_1 * p_B^L0 ≤ q_B^L0 * wDen x0`, `wDen x0 ≤ wNum x0 * wDen xend`, `q_B^Lend * wDen xend ≤ C_den * p_B^Lend`:
    have hcomb_L : (p_B ^ Lend * q_B ^ Lend) * (c_1 * p_B ^ D_drop) ≤
        (p_B ^ Lend * q_B ^ Lend) * (C_den * wNum x0 * q_B ^ D_drop) := by
      have hl : (p_B ^ Lend * q_B ^ Lend) * (c_1 * p_B ^ D_drop) =
          (c_1 * p_B ^ L0) * q_B ^ Lend := by
        rw [← hL0_sp, Nat.pow_add p_B Lend D_drop]; ac_rfl
      have hr : (p_B ^ Lend * q_B ^ Lend) * (C_den * wNum x0 * q_B ^ D_drop) =
          q_B ^ L0 * (wNum x0 * (C_den * p_B ^ Lend)) := by
        rw [← hL0_sp, Nat.pow_add q_B Lend D_drop]; ac_rfl
      rw [hl, hr]
      calc
        (c_1 * p_B ^ L0) * q_B ^ Lend ≤ (q_B ^ L0 * wDen x0) * q_B ^ Lend :=
          Nat.mul_le_mul_right _ hlo_den0
        _ ≤ (q_B ^ L0 * (wNum x0 * wDen xend)) * q_B ^ Lend :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hrat_end)
        _ = q_B ^ L0 * (wNum x0 * (q_B ^ Lend * wDen xend)) := by ac_rfl
        _ ≤ q_B ^ L0 * (wNum x0 * (C_den * p_B ^ Lend)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hhi_denE)
    have hPQ_pos : p_B ^ Lend * q_B ^ Lend > 0 := by
      have h1 := nat_pow_pos_of_pos p_B (by omega) Lend
      have h2 := nat_pow_pos_of_pos q_B (by omega) Lend
      have hm := Nat.mul_le_mul h1 h2; omega
    have hdrop_ineq : p_B ^ D_drop ≤ C_den * wNum x0 * q_B ^ D_drop := by
      have hc := nat_mul_le_cancel_left_w5 _ _ _ hPQ_pos hcomb_L
      have h1 : 1 * p_B ^ D_drop ≤ c_1 * p_B ^ D_drop := Nat.mul_le_mul_right _ hc1
      omega
    -- Step down from `D_drop ≥ s` to `s` using `q_B ≤ p_B`:
    let E_ex := D_drop - s
    have hsE : s + E_ex = D_drop := by dsimp [E_ex]; omega
    have hs_ineq : p_B ^ s ≤ C_den * wNum x0 * q_B ^ s := by
      have hqE_pE : q_B ^ E_ex ≤ p_B ^ E_ex := pow_mono_base_w12s q_B p_B (by omega) E_ex
      have hm : q_B ^ E_ex * p_B ^ s ≤ C_den * wNum x0 * (q_B ^ E_ex * q_B ^ s) := by
        calc
          q_B ^ E_ex * p_B ^ s ≤ p_B ^ E_ex * p_B ^ s := Nat.mul_le_mul_right _ hqE_pE
          _ = p_B ^ D_drop := by rw [← hsE, Nat.pow_add p_B s E_ex, Nat.mul_comm]
          _ ≤ C_den * wNum x0 * q_B ^ D_drop := hdrop_ineq
          _ = C_den * wNum x0 * (q_B ^ E_ex * q_B ^ s) := by
            rw [← hsE, Nat.pow_add q_B s E_ex, Nat.mul_comm (q_B ^ s) (q_B ^ E_ex)]
      have hm' : q_B ^ E_ex * p_B ^ s ≤ q_B ^ E_ex * (C_den * wNum x0 * q_B ^ s) := by
        calc
          q_B ^ E_ex * p_B ^ s ≤ C_den * wNum x0 * (q_B ^ E_ex * q_B ^ s) := hm
          _ = q_B ^ E_ex * (C_den * wNum x0 * q_B ^ s) := by ac_rfl
      exact nat_mul_le_cancel_left_w5 (q_B ^ E_ex) _ _
        (nat_pow_pos_of_pos q_B (by omega) E_ex) hm'
    -- Bound `C_den * wNum x0 ≤ K_const * (7 * k + 3) ^ D_num`:
    have hlin_s : L0 ≤ q_B * (7 * k + 3) := by
      have h1 : 7 * s + 1 ≤ q_B * (7 * k + 3) := by
        dsimp [s]
        rw [Nat.mul_add q_B (7 * k) 3]
        have hq3 : 1 * 3 ≤ q_B * 3 := Nat.mul_le_mul_right 3 hqB
        have h7 : 7 * (q_B * k) = q_B * (7 * k) := by ac_rfl
        omega
      exact Nat.le_trans hbl_hi0 h1
    have hnum_hi : C_den * wNum x0 ≤ K_const * (7 * k + 3) ^ D_num := by
      have hn0 := hnum x0 (hnode_ge 0 (Nat.zero_le _))
      change wNum x0 ≤ C_num * L0 ^ D_num at hn0
      have hpD : L0 ^ D_num ≤ q_B ^ D_num * (7 * k + 3) ^ D_num := by
        have hm := pow_mono_base_w12s L0 (q_B * (7 * k + 3)) hlin_s D_num
        rwa [mul_pow_w12s q_B (7 * k + 3) D_num] at hm
      calc
        C_den * wNum x0 ≤ C_den * (C_num * L0 ^ D_num) := Nat.mul_le_mul_left C_den hn0
        _ ≤ C_den * (C_num * (q_B ^ D_num * (7 * k + 3) ^ D_num)) :=
          Nat.mul_le_mul_left C_den (Nat.mul_le_mul_left C_num hpD)
        _ = K_const * (7 * k + 3) ^ D_num := by dsimp [K_const]; ac_rfl
    -- Lower bound `2 ^ k * q_B ^ s ≤ p_B ^ s` via `(2 * q_B^q_B)^k ≤ ((q_B + 1)^q_B)^k ≤ p_B^(q_B * k)`:
    have hp_lo : 2 ^ k * q_B ^ s ≤ p_B ^ s := by
      have hbase := Nat.le_trans (two_mul_pow_self_le_succ_pow q_B hqB)
        (pow_mono_base_w12s (q_B + 1) p_B hp_gt q_B)
      have hpowk := pow_mono_base_w12s (2 * q_B ^ q_B) (p_B ^ q_B) hbase k
      dsimp [s]
      rwa [mul_pow_w12s 2 (q_B ^ q_B) k, ← Nat.pow_mul q_B q_B k,
           ← Nat.pow_mul p_B q_B k] at hpowk
    have hq_s_pos : q_B ^ s > 0 := nat_pow_pos_of_pos q_B (by omega) s
    have hlt_q : (K_const * (7 * k + 3) ^ D_num) * q_B ^ s < 2 ^ k * q_B ^ s :=
      Nat.mul_lt_mul_of_pos_right hk_gt hq_s_pos
    have hle_q : p_B ^ s ≤ (K_const * (7 * k + 3) ^ D_num) * q_B ^ s :=
      Nat.le_trans hs_ineq (Nat.mul_le_mul_right (q_B ^ s) hnum_hi)
    omega

-- ============================================================================
-- SECTION 2: Front C Part 2 (Branch P5.11) — 9th Solvable Cousin `T_diamond9`
--            with Genuine 7-Tier `ω^7` Cascade (`Cone 10 -> Cone 9 -> ... -> Cone 5`)
-- ============================================================================

/-- Cone 10 of `T_diamond9`: `246067 + x = 2 ^ a * 3 ^ b` with `a ≥ 28, b ≥ 1` (starting at `x = 805060301`). -/
def isDiamond9Cone10 (x : Nat) : Prop :=
  x ≥ 805060301 ∧ x % 268435456 = 268189389 ∧ x % 3 = 2 ∧ coprime23Core (246067 + x) = 1

instance (x : Nat) : Decidable (isDiamond9Cone10 x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/--
  9th solvable mixed-(2, 3) Collatz cousin `T_diamond9` on `Nat`:
  Extends `T_diamond8` by adding Cone 10 (`isDiamond9Cone10 x -> (3 * x + 1) / 8`, a genuine
  `v_2(3x + 1) = 3` Syracuse jump that steps `2 ^ a * 3 ^ b - 246067 -> 2 ^ (a - 3) * 3 ^ (b + 1) - 92275`
  directly into Cone 9 -> Cone 8 -> Cone 7 -> Cone 6 -> Cone 5's `r`-block spiral climb, e.g.
  `1610366669 -> 603887501 -> 226457813 -> 5307605 -> 124397 -> 46649 -> ... -> 1` in `17` steps,
  jumping `cousinDiamond2Phi` upward `+1037.97x` and defeating 6-tier `ω^6` rankings)!
-/
def cousinDiamond9Step (x : Nat) : Nat :=
  if isDiamond9Cone10 x then (3 * x + 1) / 8 else cousinDiamond8Step x

def cousinDiamond9Iter : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamond9Iter k (cousinDiamond9Step x)

theorem cousinDiamond9Iter_add : ∀ (a b x : Nat),
    cousinDiamond9Iter (a + b) x = cousinDiamond9Iter b (cousinDiamond9Iter a x)
  | 0, _, _ => by simp [cousinDiamond9Iter]
  | a + 1, b, x => by
    rw [Nat.succ_add]
    exact cousinDiamond9Iter_add a b (cousinDiamond9Step x)

/-- Signed extension of `T_diamond9` (`q = 3`) to `Int` for `M2 = Z^-` separation. -/
def cousinDiamond9StepInt (x : Int) : Int :=
  if x ≥ 805060301 ∧ x % 268435456 = 268189389 ∧ x % 3 = 2 ∧ coprime23Core (246067 + x.toNat) = 1
  then (3 * x + 1) / 8
  else cousinDiamond8StepInt x

def cousinDiamond9IterInt : Nat -> Int -> Int
  | 0, x => x
  | k + 1, x => cousinDiamond9IterInt k (cousinDiamond9StepInt x)

/-- Hensel lift of `invMod33554432Odd` (`2^25`) to `mod 268435456` (`2^28`, since `25 * 2 = 50 ≥ 28`). -/
def invMod268435456Odd (d : Nat) : Nat :=
  let i33m := invMod33554432Odd d
  (i33m * (536870914 - ((d % 268435456) * i33m) % 268435456)) % 268435456

/-- Canonical reduced-pair extension of `T_diamond9` (`q = 3`) to positive `Q_(6)^+`. -/
def cousinDiamond9StepQ6 (p : Nat × Nat) : Nat × Nat :=
  let num := p.1
  let den := p.2
  let r268m := (num * invMod268435456Odd den) % 268435456
  let r3 := (num * (den % 3)) % 3
  if num ≥ 805060301 * den ∧ r268m = 268189389 ∧ r3 = 2 ∧ core3 (core2 (246067 * den + num)) = den
  then reduceRatPair (3 * num + den) (8 * den)
  else cousinDiamond8StepQ6 p

def cousinDiamond9IterQ6 : Nat -> (Nat × Nat) -> (Nat × Nat)
  | 0, p => p
  | k + 1, p => cousinDiamond9IterQ6 k (cousinDiamond9StepQ6 p)

/-- Generalized odd-multiplier `q` step of `T_diamond9` on `Nat` for `M3` (`q = 7`) separation. -/
def cousinDiamond9StepParam (q x : Nat) : Nat :=
  if isDiamond9Cone10 x then (q * x + 1) / 8 else cousinDiamond8StepParam q x

def cousinDiamond9IterParam (q : Nat) : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamond9IterParam q k (cousinDiamond9StepParam q x)

/--
  Theorem W12.3d (`cousinDiamond9StepInt_ofNat_eq`, `zero custom axioms`):
  Exact `Nat`/`Int` step agreement for `T_diamond9` (`∀ x : Nat`).
-/
theorem cousinDiamond9StepInt_ofNat_eq (x : Nat) :
    cousinDiamond9StepInt (x : Int) = (cousinDiamond9Step x : Int) := by
  have h1 : ((x : Int) ≥ 805060301) ↔ (x ≥ 805060301) := by omega
  have h2 : ((x : Int) % 268435456 = 268189389) ↔ (x % 268435456 = 268189389) :=
    ⟨Int.ofNat.inj, congrArg Int.ofNat⟩
  have h3 : ((x : Int) % 3 = 2) ↔ (x % 3 = 2) :=
    ⟨Int.ofNat.inj, congrArg Int.ofNat⟩
  have hdiv : ((3 * (x : Int) + 1) / 8) = (((3 * x + 1) / 8 : Nat) : Int) := by omega
  have htoNat : (x : Int).toNat = x := rfl
  unfold cousinDiamond9StepInt cousinDiamond9Step isDiamond9Cone10
  rw [htoNat]
  simp only [h1, h2, h3]
  by_cases hc10 : x ≥ 805060301 ∧ x % 268435456 = 268189389 ∧ x % 3 = 2 ∧ coprime23Core (246067 + x) = 1
  · simp only [hc10, and_self, ite_true, hdiv]
  · simp only [hc10, ite_false]
    exact cousinDiamond8StepInt_ofNat_eq x

theorem cousinDiamond9Step_pos (x : Nat) (hx : x > 0) : cousinDiamond9Step x > 0 := by
  unfold cousinDiamond9Step
  by_cases hc10 : isDiamond9Cone10 x
  · simp only [hc10, ite_true]
    have hge : x ≥ 805060301 := hc10.1
    clear hc10
    have hle : (3 * 805060301 + 1) / 8 ≤ (3 * x + 1) / 8 :=
      Nat.div_le_div_right (by omega)
    exact Nat.lt_of_lt_of_le (by decide : 0 < (3 * 805060301 + 1) / 8) hle
  · simp only [hc10, ite_false]; exact cousinDiamond8Step_pos x hx

theorem cousinDiamond9Step_eq_d8_of_not_cone10 (x : Nat) (hnc10 : ¬ isDiamond9Cone10 x) :
    cousinDiamond9Step x = cousinDiamond8Step x := by
  unfold cousinDiamond9Step; simp [hnc10]

/--
  Theorem W12.3e (`cousin_diamond9_outside_cones4to10_strict_descent`, `zero custom axioms`):
  Outside Cones 4, 5, 6, 7, 8, 9, and 10, EVERY `x > 2` strictly decreases `cousinDiamond2Phi` in 1 step!
-/
theorem cousin_diamond9_outside_cones4to10_strict_descent
    (x : Nat) (hx : x > 2)
    (hnc4 : ¬ isDiamond3Cone4 x) (hnc5 : ¬ isDiamond4Cone5 x)
    (hnc6 : ¬ isDiamond5Cone6 x) (hnc7 : ¬ isDiamond6Cone7 x)
    (hnc8 : ¬ isDiamond7Cone8 x) (hnc9 : ¬ isDiamond8Cone9 x)
    (hnc10 : ¬ isDiamond9Cone10 x) :
    cousinDiamond2Phi (cousinDiamond9Step x) < cousinDiamond2Phi x := by
  rw [cousinDiamond9Step_eq_d8_of_not_cone10 x hnc10]
  exact cousin_diamond8_outside_cones4to9_strict_descent x hx hnc4 hnc5 hnc6 hnc7 hnc8 hnc9

-- Modular Cone-10 avoidance helpers (`268189389 % 256 = 205, % 32 = 13, % 16 = 13, % 8 = 5, % 4 = 1, % 2 = 1`):

theorem mod256_of_cone10 (z : Nat) (hc10 : isDiamond9Cone10 z) : z % 256 = 205 := by
  have h := congrArg (· % 256) hc10.2.1
  rwa [Nat.mod_mod_of_dvd z (by decide : 256 ∣ 268435456)] at h

theorem mod32_of_cone10 (z : Nat) (hc10 : isDiamond9Cone10 z) : z % 32 = 13 := by
  have h := congrArg (· % 32) (mod256_of_cone10 z hc10)
  rwa [Nat.mod_mod_of_dvd z (by decide : 32 ∣ 256)] at h

theorem not_cone10_of_even (z : Nat) (hev : z % 2 = 0) : ¬ isDiamond9Cone10 z := by
  intro hc10
  have h := congrArg (· % 2) (mod32_of_cone10 z hc10)
  rw [Nat.mod_mod_of_dvd z (by decide : 2 ∣ 32), hev] at h
  cases h

theorem not_cone10_of_mod4_eq_3 (z : Nat) (hm4 : z % 4 = 3) : ¬ isDiamond9Cone10 z := by
  intro hc10
  have h := congrArg (· % 4) (mod32_of_cone10 z hc10)
  rw [Nat.mod_mod_of_dvd z (by decide : 4 ∣ 32), hm4] at h
  cases h

theorem not_cone10_of_mod8_ne_5 (z : Nat) (hm8 : z % 8 ≠ 5) : ¬ isDiamond9Cone10 z := by
  intro hc10
  have h := congrArg (· % 8) (mod32_of_cone10 z hc10)
  rw [Nat.mod_mod_of_dvd z (by decide : 8 ∣ 32)] at h
  exact hm8 h

theorem not_cone10_of_mod16_ne_13 (z : Nat) (hm16 : z % 16 ≠ 13) : ¬ isDiamond9Cone10 z := by
  intro hc10
  have h := congrArg (· % 16) (mod32_of_cone10 z hc10)
  rw [Nat.mod_mod_of_dvd z (by decide : 16 ∣ 32)] at h
  exact hm16 h

theorem not_cone10_of_mod32_ne_13 (z : Nat) (hm32 : z % 32 ≠ 13) : ¬ isDiamond9Cone10 z :=
  fun hc10 => hm32 (mod32_of_cone10 z hc10)

theorem not_cone10_of_mod256_ne_205 (z : Nat) (hm256 : z % 256 ≠ 205) : ¬ isDiamond9Cone10 z :=
  fun hc10 => hm256 (mod256_of_cone10 z hc10)

theorem not_cone10_of_mod3_ne_2 (z : Nat) (hm3 : z % 3 ≠ 2) : ¬ isDiamond9Cone10 z := by
  rintro ⟨_, _, h3, _⟩; exact hm3 h3

/--
  Theorem W12.3f (`not_cone10_six_mul_pow9_sub1`, choice-free `zero custom axioms`):
  Universal Post-Climb Drain Non-Reentry into Cone 10 (`∀ m : Nat`, `(6 * 9^m - 1) % 16 = 5 ≠ 13`).
-/
theorem not_cone10_six_mul_pow9_sub1 (m : Nat) :
    ¬ isDiamond9Cone10 (6 * 9 ^ m - 1) := by
  apply not_cone10_of_mod16_ne_13
  have hp9 := nat_pow_pos_of_pos 9 (by decide) m
  have hm8 := pow9_mod8_eq_one_w5 m
  have hdm := (Nat.div_add_mod (9 ^ m) 8).symm
  omega

theorem isDiamond8Cone9_of_pow2_pow3 (w z : Nat) (hw : w ≥ 25) (hz : z ≥ 1) :
    isDiamond8Cone9 (2 ^ w * 3 ^ z - 92275) := by
  have hc : (2 : Nat) ^ 25 = 33554432 := by decide
  have hp2_ge : 2 ^ w ≥ 33554432 := by
    rw [← hc]; exact pow2_mono_nat hw
  have hp3_ge : 3 ^ z ≥ 3 := by
    simpa using nat_pow_mono_exp_pos 3 1 z (by decide) hz
  have hprod_ge : 2 ^ w * 3 ^ z ≥ 100663296 := by
    simpa using Nat.mul_le_mul hp2_ge hp3_ge
  have hp33m : 33554432 ∣ 2 ^ w * 3 ^ z := by
    have hsp : w = 25 + (w - 25) := by omega
    rw [hsp, Nat.pow_add 2 25 (w - 25), hc, Nat.mul_assoc]
    exact ⟨2 ^ (w - 25) * 3 ^ z, rfl⟩
  have hp3_div : 3 ∣ 2 ^ w * 3 ^ z := by
    have hsp : z = 1 + (z - 1) := by omega
    rw [hsp, Nat.pow_add 3 1 (z - 1), Nat.pow_one,
        ← Nat.mul_assoc (2 ^ w) 3, Nat.mul_comm (2 ^ w) 3, Nat.mul_assoc]
    exact ⟨2 ^ w * 3 ^ (z - 1), rfl⟩
  refine ⟨by clear hc hp2_ge hp3_ge hp33m hp3_div; generalize 2 ^ w * 3 ^ z = P at hprod_ge ⊢; omega,
          ?_, ?_, ?_⟩
  · rcases hp33m with ⟨q, hq⟩
    clear hc hp2_ge hp3_ge hp3_div
    generalize 2 ^ w * 3 ^ z = P at hprod_ge hq ⊢
    have hq_ge : q ≥ 3 := by omega
    rw [hq, show q = (q - 1) + 1 by omega, Nat.mul_add 33554432 (q - 1) 1, Nat.mul_one]
    generalize q - 1 = q'
    have hsub : 33554432 * q' + 33554432 - 92275 = 33462157 + 33554432 * q' := by omega
    rw [hsub, Nat.add_mul_mod_self_left]
  · rcases hp3_div with ⟨q3, hq3⟩
    clear hc hp2_ge hp3_ge hp33m
    generalize 2 ^ w * 3 ^ z = P at hprod_ge hq3 ⊢
    omega
  · have hadd : 92275 + (2 ^ w * 3 ^ z - 92275) = 2 ^ w * 3 ^ z := by
      clear hc hp2_ge hp3_ge hp33m hp3_div
      generalize 2 ^ w * 3 ^ z = P at hprod_ge ⊢
      omega
    rw [hadd]
    exact coprime23Core_pow2_pow3 w z

theorem cousin_diamond9_mersenne_scaled :
    ∀ (k a q : Nat), k + 1 ≤ a -> q ≥ 1 ->
      cousinDiamond9Iter k (2 ^ a * q - 1) = 3 ^ k * 2 ^ (a - k) * q - 1
  | 0, _, _, _, _ => by simp [cousinDiamond9Iter]
  | k + 1, a, q, hka, hq => by
    have hp4 : 2 ^ a * q = 4 * (2 ^ (a - 2) * q) := by
      conv => lhs; rw [show a = (a - 2) + 2 by omega]
      rw [Nat.pow_add 2 (a - 2) 2, show (2 : Nat) ^ 2 = 4 from rfl,
          Nat.mul_comm (2 ^ (a - 2)) 4, Nat.mul_assoc]
    have hm_pos : 2 ^ (a - 2) * q ≥ 1 := Nat.mul_le_mul (pow2_pos_nat (a - 2)) hq
    have hz4 : (2 ^ a * q - 1) % 4 = 3 := by omega
    simp only [cousinDiamond9Iter]
    rw [cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_mod4_eq_3 _ hz4)]
    have hd8 := cousin_diamond8_mersenne_scaled 1 a q (by omega) hq
    simp only [cousinDiamond8Iter, Nat.pow_one] at hd8
    have hstep_eq : cousinDiamond8Step (2 ^ a * q - 1) = 2 ^ (a - 1) * (3 * q) - 1 := by
      rw [hd8]; apply congrArg (· - 1); ac_rfl
    rw [hstep_eq, cousin_diamond9_mersenne_scaled k (a - 1) (3 * q) (by omega) (by omega),
        show a - 1 - k = a - (k + 1) by omega, Nat.pow_succ 3 k]
    apply congrArg (· - 1); ac_rfl

theorem cousin_diamond9_even9_spine_drain :
    ∀ k : Nat, cousinDiamond9Iter k ((9 ^ (k + 1) - 1) / 4) = 2
  | 0 => rfl
  | k + 1 => by
    let j := k + 1
    have hp9j_ge9 : 9 ^ j ≥ 9 := by
      dsimp [j]; rw [Nat.pow_succ]; have hp := nat_pow_pos_of_pos 9 (by decide) k; omega
    have hp9j_m8 : 9 ^ j % 8 = 1 := pow9_mod8_eq_one_w5 j
    let q := (9 ^ j - 1) / 8
    have hp9j_eq : 9 ^ j = 8 * q + 1 := by dsimp [q]; omega
    have he_j1 : (9 ^ (j + 1) - 1) / 4 = 18 * q + 2 := by rw [Nat.pow_succ 9 j, hp9j_eq]; omega
    simp only [cousinDiamond9Iter]
    change cousinDiamond9Iter k (cousinDiamond9Step ((9 ^ (j + 1) - 1) / 4)) = 2
    have hnc10 : ¬ isDiamond9Cone10 ((9 ^ (j + 1) - 1) / 4) := by
      rw [he_j1]; exact not_cone10_of_even _ (by omega)
    rw [cousinDiamond9Step_eq_d8_of_not_cone10 _ hnc10]
    -- Show `cousinDiamond8Step ((9 ^ (j + 1) - 1) / 4) = (9 ^ j - 1) / 4`:
    have hd8 : cousinDiamond8Step ((9 ^ (j + 1) - 1) / 4) = (9 ^ j - 1) / 4 := by
      have he_j : (9 ^ j - 1) / 4 = 2 * q := by rw [hp9j_eq]; omega
      rw [he_j1, he_j,
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
    rw [hd8]
    exact cousin_diamond9_even9_spine_drain k

theorem cousin_diamond9_pow3_sub1_drain :
    ∀ k : Nat, cousinDiamond9Iter k (3 ^ (k + 1) - 1) = 2
  | 0 => rfl
  | k + 1 => by
    let j := k + 1
    have hp3_ge3 : 3 ^ j ≥ 3 := by dsimp [j]; rw [Nat.pow_succ]; have hp := pow3_pos_nat k; omega
    have ho_j1 := pow3_odd_nat_sec8 (j + 1)
    have hp_j1 := pow3_pos_nat (j + 1)
    simp only [cousinDiamond9Iter]
    change cousinDiamond9Iter k (cousinDiamond9Step (3 ^ (j + 1) - 1)) = 2
    rw [cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
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
      unfold cousinDiamond3Step
      simp only [hev, hn18, hm6, and_self, ite_true, ite_false]
      rw [h3j1]; omega
    rw [hd4]
    exact cousin_diamond9_pow3_sub1_drain k

theorem cousin_diamond9_cone5_two_step_climb :
    ∀ (q_c a b : Nat), 3 * q_c + 2 ≤ a -> b ≥ 1 ->
      cousinDiamond9Iter (2 * q_c) (2 ^ a * 3 ^ b - 7) =
        2 ^ (a - 3 * q_c) * 3 ^ (b + 2 * q_c) - 7
  | 0, _, _, _, _ => by simp [cousinDiamond9Iter]
  | q_c + 1, a, b, ha, hb => by
    have ha5 : a ≥ 5 := by omega
    have hc5 := isDiamond4Cone5_of_pow2_pow3 a b ha5 hb
    have hnc10_0 : ¬ isDiamond9Cone10 (2 ^ a * 3 ^ b - 7) :=
      not_cone10_of_mod32_ne_13 _ (by have h := hc5.2.1; omega)
    let mid := 2 ^ (a - 2) * 3 ^ (b + 1) - 5
    have hmid_4 : mid % 4 = 3 := by
      dsimp [mid]
      have hp8 : 2 ^ (a - 2) = 8 * 2 ^ (a - 5) := by
        conv => lhs; rw [show a - 2 = 3 + (a - 5) by omega]; rw [Nat.pow_add]
      rw [hp8, Nat.mul_assoc 8]
      have hp_pos : 2 ^ (a - 5) * 3 ^ (b + 1) ≥ 1 :=
        Nat.mul_le_mul (pow2_pos_nat _) (pow3_pos_nat _)
      omega
    have hnc10_1 : ¬ isDiamond9Cone10 mid := not_cone10_of_mod4_eq_3 mid hmid_4
    have hd8_2 := cousin_diamond8_cone5_two_step_climb 1 a b (by omega) hb
    simp only [Nat.mul_one, cousinDiamond8Iter] at hd8_2
    have hd8_s1 : cousinDiamond8Step (2 ^ a * 3 ^ b - 7) = mid := by
      rw [cousinDiamond8Step_eq_d7_of_not_cone9 _
            (not_cone9_of_mod32_ne_13 _ (by have h := hc5.2.1; omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _
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
    rw [hd8_s1] at hd8_2
    have hs1 : cousinDiamond9Step (2 ^ a * 3 ^ b - 7) = mid := by
      rw [cousinDiamond9Step_eq_d8_of_not_cone10 _ hnc10_0]; exact hd8_s1
    have hs2 : cousinDiamond9Step mid = 2 ^ (a - 3) * 3 ^ (b + 2) - 7 := by
      rw [cousinDiamond9Step_eq_d8_of_not_cone10 _ hnc10_1]; exact hd8_2
    rw [Nat.mul_succ 2 q_c, Nat.add_comm (2 * q_c) 2,
        cousinDiamond9Iter_add 2 (2 * q_c)]
    have hi2 : cousinDiamond9Iter 2 (2 ^ a * 3 ^ b - 7) = 2 ^ (a - 3) * 3 ^ (b + 2) - 7 := by
      simp only [cousinDiamond9Iter, hs1, hs2]
    rw [hi2, cousin_diamond9_cone5_two_step_climb q_c (a - 3) (b + 2) (by omega) (by omega)]
    apply congrArg (· - 7)
    congr 1
    · apply congrArg (2 ^ ·); omega
    · apply congrArg (3 ^ ·); omega

theorem cousin_diamond9_a0_3_drain (b0 : Nat) (hb0 : b0 ≥ 3) :
    cousinDiamond9Step (8 * 3 ^ b0 - 7) = 12 * 3 ^ b0 - 10 ∧
    cousinDiamond9Step (12 * 3 ^ b0 - 10) = 4 * 3 ^ b0 - 4 ∧
    cousinDiamond9Step (4 * 3 ^ b0 - 4) = 4 * 3 ^ (b0 - 1) - 2 ∧
    cousinDiamond9Iter ((b0 - 1) / 2 + 7) (8 * 3 ^ b0 - 7) = 1 := by
  rcases cousin_diamond8_a0_3_drain b0 hb0 with ⟨hd8_1, hd8_2, hd8_3, _⟩
  have hp3_ge27 : 3 ^ b0 ≥ 27 := by simpa using nat_pow_mono_exp_pos 3 3 b0 (by decide) hb0
  have hp3_b1_ge9 : 3 ^ (b0 - 1) ≥ 9 := by
    simpa using nat_pow_mono_exp_pos 3 2 (b0 - 1) (by decide) (by omega)
  have hnc10_1 : ¬ isDiamond9Cone10 (8 * 3 ^ b0 - 7) := by
    apply not_cone10_of_mod32_ne_13; have ho := pow3_odd_nat_sec8 b0; omega
  have hs1 : cousinDiamond9Step (8 * 3 ^ b0 - 7) = 12 * 3 ^ b0 - 10 := by
    rw [cousinDiamond9Step_eq_d8_of_not_cone10 _ hnc10_1]; exact hd8_1
  have hs2 : cousinDiamond9Step (12 * 3 ^ b0 - 10) = 4 * 3 ^ b0 - 4 := by
    rw [cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega))]; exact hd8_2
  have hs3 : cousinDiamond9Step (4 * 3 ^ b0 - 4) = 4 * 3 ^ (b0 - 1) - 2 := by
    rw [cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega))]; exact hd8_3
  refine ⟨hs1, hs2, hs3, ?_⟩
  by_cases hev_b1 : (b0 - 1) % 2 = 0
  · let m := (b0 - 1) / 2
    have hm1 : m ≥ 1 := by dsimp [m]; omega
    have hb1_eq : b0 - 1 = 2 * m := by dsimp [m]; omega
    have hp9_ge9 : 9 ^ m ≥ 9 := by rw [pow9_eq_pow3_double m, ← hb1_eq]; exact hp3_b1_ge9
    have hp9_m8 : 9 ^ m % 8 = 1 := pow9_mod8_eq_one_w5 m
    have h4_eq : 4 * 3 ^ (b0 - 1) - 2 = 4 * 9 ^ m - 2 := by
      rw [hb1_eq, ← pow9_eq_pow3_double m]
    let zr := 2 * 9 ^ m - 1
    let yr := (3 * 9 ^ m - 1) / 2
    have hs4 : cousinDiamond9Step (4 * 9 ^ m - 2) = zr := by
      rw [cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (4 * 9 ^ m - 2) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h9m9 : 9 ^ m % 9 = 0 := by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
      have h9m3 : 9 ^ m % 3 = 0 := by omega
      rw [cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) (by omega)]
      dsimp [zr]; omega
    have hsz : cousinDiamond9Step zr = yr := by
      rw [cousinDiamond9Step_eq_d8_of_not_cone10 zr (not_cone10_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 zr (not_cone9_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
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
    have hsy : cousinDiamond9Step yr = (9 ^ (m + 1) - 1) / 4 := by
      have hyr_m3 : yr % 3 = 1 := by
        have hm3 : 9 ^ m % 3 = 0 := by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
        dsimp [yr]; omega
      rw [cousinDiamond9Step_eq_d8_of_not_cone10 yr (not_cone10_of_mod3_ne_2 yr (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 yr (not_cone9_of_mod3_ne_2 yr (by omega)),
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
          clear hd8_1 hd8_2 hd8_3 hs1 hs2 hs3 h4_eq hs4 hsz hnc5 hc3_2; omega
        rw [core3_not_div3 (yr + 1) hnd3]
        clear hd8_1 hd8_2 hd8_3 hs1 hs2 hs3 h4_eq hs4 hsz hnc5 hc3_2
        dsimp [yr]; omega
      have hnc4 : ¬ isDiamond3Cone4 yr := by
        rintro ⟨hge169, _, hc2⟩
        by_cases hm_eq1 : m = 1
        · clear hd8_1 hd8_2 hd8_3 hs1 hs2 hs3 h4_eq hs4 hsz hnc5 hc3_2 hc3_1 hc2
          dsimp only [yr] at hge169; rw [hm_eq1] at hge169; omega
        · have hm2 : m ≥ 2 := by
            clear hd8_1 hd8_2 hd8_3 hs1 hs2 hs3 h4_eq hs4 hsz hnc5 hc3_2 hc3_1 hge169 hc2; omega
          rcases eq_pow2_of_core2_eq_one (3 * yr + 5)
            (by clear hd8_1 hd8_2 hd8_3 hs1 hs2 hs3 h4_eq hs4 hsz hnc5 hc3_2 hc3_1; dsimp [yr]; omega) hc2 with
            ⟨M0, hM0⟩
          have h9_eq : 9 ^ (m + 1) + 7 = 2 ^ (M0 + 1) := by
            have h2mul : 2 * (3 * yr + 5) = 9 ^ (m + 1) + 7 := by
              clear hd8_1 hd8_2 hd8_3 hs1 hs2 hs3 h4_eq hs4 hsz hnc5 hc3_2 hc3_1 hc2 hM0
              rw [Nat.pow_succ 9 m, Nat.mul_comm (9 ^ m) 9]; dsimp [yr]; omega
            rw [← h2mul, hM0, Nat.pow_succ 2 M0, Nat.mul_comm]
          exact pow9_succ_add_seven_ne_pow2 m (M0 + 1) hm2 h9_eq
      rw [cousinDiamond3Step_odd_half_w8 yr (by dsimp [yr]; omega) hnc4 hc3_2 hc3_1]
      dsimp [yr]; rw [Nat.pow_succ 9 m]; omega
    change cousinDiamond9Iter (m + 7) (8 * 3 ^ b0 - 7) = 1
    rw [show m + 7 = 4 + 1 + 1 + m + 1 by omega,
        cousinDiamond9Iter_add (4 + 1 + 1 + m) 1,
        cousinDiamond9Iter_add (4 + 1 + 1) m,
        cousinDiamond9Iter_add (4 + 1) 1,
        cousinDiamond9Iter_add 4 1]
    have hi4 : cousinDiamond9Iter 4 (8 * 3 ^ b0 - 7) = zr := by
      simp only [cousinDiamond9Iter, hs1, hs2, hs3, h4_eq, hs4]
    rw [hi4]
    have hiz : cousinDiamond9Iter 1 zr = yr := hsz
    rw [hiz]
    have hiy : cousinDiamond9Iter 1 yr = (9 ^ (m + 1) - 1) / 4 := hsy
    rw [hiy, cousin_diamond9_even9_spine_drain m]
    decide
  · let m := (b0 - 1) / 2
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
    have hs4 : cousinDiamond9Step (12 * 9 ^ m - 2) = ur := by
      rw [cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (12 * 9 ^ m - 2) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h9m9 : 9 ^ m % 9 = 0 := by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
      rw [cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) (by omega)]
      dsimp [ur]; omega
    have hsu : cousinDiamond9Step ur = wr := by
      rw [cousinDiamond9Step_eq_d8_of_not_cone10 ur (not_cone10_six_mul_pow9_sub1 m),
          cousinDiamond8Step_eq_d7_of_not_cone9 ur (not_cone9_six_mul_pow9_sub1 m),
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
    have hsw : cousinDiamond9Step wr = (9 ^ (m + 1) - 1) / 4 := by
      let q := (9 ^ m - 1) / 8
      have hq_pos : q ≥ 1 := by dsimp [q]; omega
      have hp9_eq : 9 ^ m = 8 * q + 1 := by dsimp [q]; omega
      have hwr_eq : wr = 36 * q + 4 := by dsimp [wr]; rw [Nat.pow_succ 9 m, hp9_eq]; omega
      have hnext_eq : (9 ^ (m + 1) - 1) / 4 = 18 * q + 2 := by rw [Nat.pow_succ 9 m, hp9_eq]; omega
      rw [hwr_eq, hnext_eq,
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (36 * q + 4) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5,
          cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) (by omega)]
      omega
    change cousinDiamond9Iter (m + 7) (8 * 3 ^ b0 - 7) = 1
    rw [show m + 7 = 4 + 1 + 1 + m + 1 by omega,
        cousinDiamond9Iter_add (4 + 1 + 1 + m) 1,
        cousinDiamond9Iter_add (4 + 1 + 1) m,
        cousinDiamond9Iter_add (4 + 1) 1,
        cousinDiamond9Iter_add 4 1]
    have hi4 : cousinDiamond9Iter 4 (8 * 3 ^ b0 - 7) = ur := by
      simp only [cousinDiamond9Iter, hs1, hs2, hs3, hu_eq, hs4]
    rw [hi4]
    have hiu : cousinDiamond9Iter 1 ur = wr := hsu
    rw [hiu]
    have hiw : cousinDiamond9Iter 1 wr = (9 ^ (m + 1) - 1) / 4 := hsw
    rw [hiw, cousin_diamond9_even9_spine_drain m]
    decide

theorem cousin_diamond9_a0_2_and_4_drain (b0 : Nat) (hb0 : b0 ≥ 3) :
    cousinDiamond9Iter (b0 + 3) (4 * 3 ^ b0 - 7) = 1 ∧
    cousinDiamond9Iter ((b0 - 1) / 2 + 8) (16 * 3 ^ b0 - 7) = 1 := by
  have hp3_ge27 : 3 ^ b0 ≥ 27 := by simpa using nat_pow_mono_exp_pos 3 3 b0 (by decide) hb0
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
  have hnc10_4 : ¬ isDiamond9Cone10 (4 * 3 ^ b0 - 7) := by
    apply not_cone10_of_mod32_ne_13
    have hdm := (Nat.div_add_mod (3 ^ b0) 8).symm
    rcases h3b0_m8 with h1 | h3 <;> omega
  have hnc10_16 : ¬ isDiamond9Cone10 (16 * 3 ^ b0 - 7) := by
    apply not_cone10_of_mod32_ne_13; have ho := pow3_odd_nat_sec8 b0; omega
  have hnc9_4 : ¬ isDiamond8Cone9 (4 * 3 ^ b0 - 7) := by
    apply not_cone9_of_mod32_ne_13
    have hdm := (Nat.div_add_mod (3 ^ b0) 8).symm
    rcases h3b0_m8 with h1 | h3 <;> omega
  have hnc9_16 : ¬ isDiamond8Cone9 (16 * 3 ^ b0 - 7) := by
    apply not_cone9_of_mod32_ne_13; have ho := pow3_odd_nat_sec8 b0; omega
  have hnc8_4 : ¬ isDiamond7Cone8 (4 * 3 ^ b0 - 7) := by
    apply not_cone8_of_mod32_ne_21
    have hdm := (Nat.div_add_mod (3 ^ b0) 8).symm
    rcases h3b0_m8 with h1 | h3 <;> omega
  have hnc8_16 : ¬ isDiamond7Cone8 (16 * 3 ^ b0 - 7) := by
    apply not_cone8_of_mod32_ne_21; have ho := pow3_odd_nat_sec8 b0; omega
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
  · have hs1 : cousinDiamond9Step (4 * 3 ^ b0 - 7) = 6 * 3 ^ b0 - 10 := by
      rw [cousinDiamond9Step_eq_d8_of_not_cone10 _ hnc10_4,
          cousinDiamond8Step_eq_d7_of_not_cone9 _ hnc9_4,
          cousinDiamond7Step_eq_d6_of_not_cone8 _ hnc8_4,
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (hnc7_c 4 (by decide)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (hnc6_c 4 (by decide))]
      exact cousin_diamond4_exit_step_general_odd 4 b0 (Or.inl rfl) hb0
    have hs2 : cousinDiamond9Step (6 * 3 ^ b0 - 10) = 2 * 3 ^ b0 - 4 := by
      rw [cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (6 * 3 ^ b0 - 10) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 6 * 3 ^ b0 = 18 * 3 ^ (b0 - 1) := by rw [h3b0_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    have hs3 : cousinDiamond9Step (2 * 3 ^ b0 - 4) = 2 * 3 ^ (b0 - 1) - 2 := by
      rw [cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (2 * 3 ^ b0 - 4) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 2 * 3 ^ b0 = 18 * 3 ^ (b0 - 2) := by rw [h3b0_sp, h3b1_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    have hs4 : cousinDiamond9Step (2 * 3 ^ (b0 - 1) - 2) = 3 ^ (b0 - 1) - 1 := by
      rw [cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
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
        cousinDiamond9Iter_add (4 + (b0 - 2)) 1,
        cousinDiamond9Iter_add 4 (b0 - 2)]
    have hi4 : cousinDiamond9Iter 4 (4 * 3 ^ b0 - 7) = 3 ^ ((b0 - 2) + 1) - 1 := by
      simp only [cousinDiamond9Iter, hs1, hs2, hs3, hs4]
      rw [show b0 - 1 = (b0 - 2) + 1 by omega]
    rw [hi4, cousin_diamond9_pow3_sub1_drain (b0 - 2)]
    decide
  · rcases cousin_diamond9_a0_3_drain b0 hb0 with ⟨ha3_s1, ha3_s2, ha3_s3, ha3⟩
    have hs1 : cousinDiamond9Step (16 * 3 ^ b0 - 7) = 24 * 3 ^ b0 - 10 := by
      rw [cousinDiamond9Step_eq_d8_of_not_cone10 _ hnc10_16,
          cousinDiamond8Step_eq_d7_of_not_cone9 _ hnc9_16,
          cousinDiamond7Step_eq_d6_of_not_cone8 _ hnc8_16,
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (hnc7_c 16 (by decide)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (hnc6_c 16 (by decide))]
      exact cousin_diamond4_exit_step_general_odd 16 b0 (Or.inr (Or.inr rfl)) hb0
    have hs2 : cousinDiamond9Step (24 * 3 ^ b0 - 10) = 8 * 3 ^ b0 - 4 := by
      rw [cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (24 * 3 ^ b0 - 10) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 24 * 3 ^ b0 = 18 * (4 * 3 ^ (b0 - 1)) := by rw [h3b0_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    have hs3 : cousinDiamond9Step (8 * 3 ^ b0 - 4) = 8 * 3 ^ (b0 - 1) - 2 := by
      rw [cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (8 * 3 ^ b0 - 4) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 8 * 3 ^ b0 = 18 * (4 * 3 ^ (b0 - 2)) := by rw [h3b0_sp, h3b1_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    have hs4 : cousinDiamond9Step (8 * 3 ^ (b0 - 1) - 2) = 4 * 3 ^ (b0 - 1) - 2 := by
      rw [cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
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
        cousinDiamond9Iter_add 3 ((b0 - 1) / 2 + 4)] at ha3
    have hi3 : cousinDiamond9Iter 3 (8 * 3 ^ b0 - 7) = 4 * 3 ^ (b0 - 1) - 2 := by
      simp only [cousinDiamond9Iter, ha3_s1, ha3_s2, ha3_s3]
    rw [hi3] at ha3
    rw [show (b0 - 1) / 2 + 8 = 4 + ((b0 - 1) / 2 + 4) by omega,
        cousinDiamond9Iter_add 4 ((b0 - 1) / 2 + 4)]
    have hi4 : cousinDiamond9Iter 4 (16 * 3 ^ b0 - 7) = 4 * 3 ^ (b0 - 1) - 2 := by
      simp only [cousinDiamond9Iter, hs1, hs2, hs3, hs4]
    rw [hi4]
    exact ha3

theorem cousin_diamond9_cone4_return_aux (x : Nat) (hc4 : isDiamond3Cone4 x) :
    ∃ k : Nat, k ≤ cousinDiamond2Phi x ∧ cousinDiamond9Iter k x = 1 := by
  rcases cousin_diamond3_cone4_reaches_one_exact x hc4 with ⟨r, hr_ge3, hE, _, hphi_ge⟩
  refine ⟨3 * r + 4, hphi_ge, ?_⟩
  have hnc10_x : ¬ isDiamond9Cone10 x := not_cone10_of_mod8_ne_5 x (by have h8 := hc4.2.1; omega)
  have hnc9_x : ¬ isDiamond8Cone9 x := not_cone9_of_mod8_ne_5 x (by have h8 := hc4.2.1; omega)
  have hnc8_x : ¬ isDiamond7Cone8 x := not_cone8_of_mod8_ne_5 x (by have h8 := hc4.2.1; omega)
  have hnc7_x : ¬ isDiamond6Cone7 x := not_cone7_of_mod8_ne_5 x (by have h8 := hc4.2.1; omega)
  have hnc6_x : ¬ isDiamond5Cone6 x := by rintro ⟨_, h256, _, _⟩; have h8 := hc4.2.1; omega
  have hx_odd : x % 2 = 1 := by have h8 := hc4.2.1; omega
  have hs1 : cousinDiamond9Step x = 2 ^ (2 * r + 1) - 1 := by
    rw [cousinDiamond9Step_eq_d8_of_not_cone10 x hnc10_x,
        cousinDiamond8Step_eq_d7_of_not_cone9 x hnc9_x,
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
  have hglide : cousinDiamond9Iter (2 * r) (2 ^ (2 * r + 1) - 1) = zr := by
    have hf := cousin_diamond9_mersenne_scaled (2 * r) (2 * r + 1) 1 (by omega) (by decide)
    simp only [Nat.mul_one, show 2 * r + 1 - 2 * r = 1 by omega, Nat.pow_one] at hf
    rw [hf, ← pow9_eq_pow3_double r, Nat.mul_comm]
  have hp9_ge729 : 9 ^ r ≥ 729 := by simpa using nat_pow_mono_exp_pos 9 3 r (by decide) hr_ge3
  have hp9_m8 : 9 ^ r % 8 = 1 := pow9_mod8_eq_one_w5 r
  have hsz : cousinDiamond9Step zr = yr := by
    rw [cousinDiamond9Step_eq_d8_of_not_cone10 zr (not_cone10_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
        cousinDiamond8Step_eq_d7_of_not_cone9 zr (not_cone9_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
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
  have hsy : cousinDiamond9Step yr = (9 ^ (r + 1) - 1) / 4 := by
    have hyr_m3 : yr % 3 = 1 := by
      have hm3 : 9 ^ r % 3 = 0 := by rw [show r = (r - 1) + 1 by omega, Nat.pow_succ]; omega
      dsimp [yr]; omega
    rw [cousinDiamond9Step_eq_d8_of_not_cone10 yr (not_cone10_of_mod3_ne_2 yr (by omega)),
        cousinDiamond8Step_eq_d7_of_not_cone9 yr (not_cone9_of_mod3_ne_2 yr (by omega)),
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
      cousinDiamond9Iter_add (1 + 2 * r + 1 + 1 + r) 1,
      cousinDiamond9Iter_add (1 + 2 * r + 1 + 1) r,
      cousinDiamond9Iter_add (1 + 2 * r + 1) 1,
      cousinDiamond9Iter_add (1 + 2 * r) 1,
      cousinDiamond9Iter_add 1 (2 * r)]
  have hi1 : cousinDiamond9Iter 1 x = 2 ^ (2 * r + 1) - 1 := hs1
  rw [hi1, hglide]
  have hiz : cousinDiamond9Iter 1 zr = yr := hsz
  rw [hiz]
  have hiy : cousinDiamond9Iter 1 yr = (9 ^ (r + 1) - 1) / 4 := hsy
  rw [hiy, cousin_diamond9_even9_spine_drain r]
  decide

theorem cousin_diamond9_cone5_return_aux (x : Nat) (hc5 : isDiamond4Cone5 x) :
    ∃ (a b k : Nat),
      a ≥ 5 ∧ b ≥ 1 ∧ x + 7 = 2 ^ a * 3 ^ b ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond9Iter k x = 1 := by
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
  have hclimb := cousin_diamond9_cone5_two_step_climb q_c a b (by dsimp [q_c]; omega) hb1
  rw [← hx_eq] at hclimb
  change cousinDiamond9Iter (2 * q_c) x = 2 ^ a0 * 3 ^ b0 - 7 at hclimb
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
  have hd_3 := (cousin_diamond9_a0_3_drain b0 hb0_ge3).2.2.2
  rcases cousin_diamond9_a0_2_and_4_drain b0 hb0_ge3 with ⟨hd_2, hd_4⟩
  rcases ha0_234 with ha2 | ha3 | ha4
  · have hkx := hbound_x (b0 + 3) (by omega)
    refine ⟨a, b, 2 * q_c + (b0 + 3), ha5, hb1, hmul.symm, hkx,
      Nat.le_trans (by omega : 2 * q_c + (b0 + 3) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond9Iter_add (2 * q_c) (b0 + 3) x, hclimb, ha2]; exact hd_2
  · have hkx := hbound_x ((b0 - 1) / 2 + 7) (by omega)
    refine ⟨a, b, 2 * q_c + ((b0 - 1) / 2 + 7), ha5, hb1, hmul.symm, hkx,
      Nat.le_trans (by omega : 2 * q_c + ((b0 - 1) / 2 + 7) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond9Iter_add (2 * q_c) ((b0 - 1) / 2 + 7) x, hclimb, ha3]; exact hd_3
  · have hkx := hbound_x ((b0 - 1) / 2 + 8) (by omega)
    refine ⟨a, b, 2 * q_c + ((b0 - 1) / 2 + 8), ha5, hb1, hmul.symm, hkx,
      Nat.le_trans (by omega : 2 * q_c + ((b0 - 1) / 2 + 8) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond9Iter_add (2 * q_c) ((b0 - 1) / 2 + 8) x, hclimb, ha4]; exact hd_4

theorem cousin_diamond9_cone6_return_aux (x : Nat) (hc6 : isDiamond5Cone6 x) :
    ∃ (e f k : Nat),
      e ≥ 8 ∧ f ≥ 2 ∧ x + 19 = 2 ^ e * 3 ^ f ∧
      cousinDiamond9Step x = 2 ^ (e - 3) * 3 ^ (f + 1) - 7 ∧
      isDiamond4Cone5 (cousinDiamond9Step x) ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond9Iter k x = 1 := by
  have hnc10_x : ¬ isDiamond9Cone10 x :=
    not_cone10_of_mod256_ne_205 x (by rw [hc6.2.1]; decide)
  have hx_ge : x ≥ 2285 := hc6.1
  rcases (cousin_diamond8_cones4to9_exact_return.2.2.1 x hc6) with
    ⟨e, f, _, he8, hf2, hmul, hd8_x, _, _, _, _⟩
  let y := 2 ^ (e - 3) * 3 ^ (f + 1) - 7
  have hstep_x : cousinDiamond9Step x = y := by
    rw [cousinDiamond9Step_eq_d8_of_not_cone10 x hnc10_x]; exact hd8_x
  have hnc9_x : ¬ isDiamond8Cone9 x :=
    not_cone9_of_mod256_ne_141 x (by rw [hc6.2.1]; decide)
  have hnc8_x : ¬ isDiamond7Cone8 x :=
    not_cone8_of_mod256_ne_213 x (by rw [hc6.2.1]; decide)
  have hnc7_x : ¬ isDiamond6Cone7 x :=
    not_cone7_of_mod256_ne_213 x (by rw [hc6.2.1]; decide)
  have hy_step : y = (3 * x + 1) / 8 :=
    hd8_x.symm.trans (by
      rw [cousinDiamond8Step_eq_d7_of_not_cone9 x hnc9_x,
          cousinDiamond7Step_eq_d6_of_not_cone8 x hnc8_x,
          cousinDiamond6Step_eq_d5_of_not_cone7 x hnc7_x]
      unfold cousinDiamond5Step; simp [hc6])
  clear hc6 hnc10_x hnc9_x hnc8_x hnc7_x hd8_x
  have hc5_y : isDiamond4Cone5 y :=
    isDiamond4Cone5_of_pow2_pow3 (e - 3) (f + 1) (by omega) (by omega)
  rcases cousin_diamond9_cone5_return_aux y hc5_y with ⟨_, _, ky, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hdiv : y * 8 ≤ 3 * x + 1 := by rw [hy_step]; exact Nat.div_mul_le_self (3 * x + 1) 8
    clear hy_step hmul hstep_x hc5_y hky_1; omega
  have h1ky_x : 1 + ky ≤ x := by clear hy_step hmul hstep_x hc5_y hky_1; omega
  have h1ky_phi : 1 + ky ≤ cousinDiamond2Phi x :=
    Nat.le_trans (by clear hy_step hmul hstep_x hc5_y hky_1; omega : 1 + ky ≤ x + 1) (cousinDiamond2Phi_ge_succ x)
  refine ⟨e, f, 1 + ky, he8, hf2, hmul, hstep_x, ?_, h1ky_x, h1ky_phi, ?_⟩
  · rw [hstep_x]; exact hc5_y
  · rw [cousinDiamond9Iter_add 1 ky x]
    have hi1 : cousinDiamond9Iter 1 x = y := hstep_x
    rw [hi1]; exact hky_1

theorem cousin_diamond9_cone7_return_aux (x : Nat) (hc7 : isDiamond6Cone7 x) :
    ∃ (g h k : Nat),
      g ≥ 15 ∧ h ≥ 2 ∧ x + 811 = 2 ^ g * 3 ^ h ∧
      cousinDiamond9Step x = 2 ^ (g - 7) * 3 ^ (h + 1) - 19 ∧
      isDiamond5Cone6 (cousinDiamond9Step x) ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond9Iter k x = 1 := by
  have hnc10_x : ¬ isDiamond9Cone10 x := by
    apply not_cone10_of_mod32_ne_13
    have h32 : x % 32 = 31957 % 32 := by
      have h := congrArg (· % 32) hc7.2.1
      rwa [Nat.mod_mod_of_dvd x (by decide : 32 ∣ 32768)] at h
    rw [h32]; decide
  have hnc9_x : ¬ isDiamond8Cone9 x := by
    apply not_cone9_of_mod32_ne_13
    have h32 : x % 32 = 31957 % 32 := by
      have h := congrArg (· % 32) hc7.2.1
      rwa [Nat.mod_mod_of_dvd x (by decide : 32 ∣ 32768)] at h
    rw [h32]; decide
  have hnc8_x : ¬ isDiamond7Cone8 x :=
    not_cone8_of_mod32768_ne_30933 x (by rw [hc7.2.1]; decide)
  have hx_ge : x ≥ 294101 := hc7.1
  rcases (cousin_diamond8_cones4to9_exact_return.2.2.2.1 x hc7) with
    ⟨g, h, _, hg15, hh2, hmul, hd8_x, _, _, _, _⟩
  let y := 2 ^ (g - 7) * 3 ^ (h + 1) - 19
  have hstep_x : cousinDiamond9Step x = y := by
    rw [cousinDiamond9Step_eq_d8_of_not_cone10 x hnc10_x]; exact hd8_x
  have hy_step : y = (3 * x + 1) / 128 :=
    hd8_x.symm.trans (by
      rw [cousinDiamond8Step_eq_d7_of_not_cone9 x hnc9_x,
          cousinDiamond7Step_eq_d6_of_not_cone8 x hnc8_x]
      unfold cousinDiamond6Step; simp [hc7])
  clear hc7 hnc10_x hnc9_x hnc8_x hd8_x
  have hc6_y : isDiamond5Cone6 y :=
    isDiamond5Cone6_of_pow2_pow3 (g - 7) (h + 1) (by omega) (by omega)
  rcases cousin_diamond9_cone6_return_aux y hc6_y with ⟨_, _, ky, _, _, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hdiv : y * 128 ≤ 3 * x + 1 := by rw [hy_step]; exact Nat.div_mul_le_self (3 * x + 1) 128
    clear hy_step hmul hstep_x hc6_y hky_1; omega
  have h1ky_x : 1 + ky ≤ x := by clear hy_step hmul hstep_x hc6_y hky_1; omega
  have h1ky_phi : 1 + ky ≤ cousinDiamond2Phi x :=
    Nat.le_trans (by clear hy_step hmul hstep_x hc6_y hky_1; omega : 1 + ky ≤ x + 1) (cousinDiamond2Phi_ge_succ x)
  refine ⟨g, h, 1 + ky, hg15, hh2, hmul, hstep_x, ?_, h1ky_x, h1ky_phi, ?_⟩
  · rw [hstep_x]; exact hc6_y
  · rw [cousinDiamond9Iter_add 1 ky x]
    have hi1 : cousinDiamond9Iter 1 x = y := hstep_x
    rw [hi1]; exact hky_1

theorem cousin_diamond9_cone8_return_aux (x : Nat) (hc8 : isDiamond7Cone8 x) :
    ∃ (u v k : Nat),
      u ≥ 22 ∧ v ≥ 1 ∧ x + 34603 = 2 ^ u * 3 ^ v ∧
      cousinDiamond9Step x = 2 ^ (u - 7) * 3 ^ (v + 1) - 811 ∧
      isDiamond6Cone7 (cousinDiamond9Step x) ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond9Iter k x = 1 := by
  have hnc10_x : ¬ isDiamond9Cone10 x :=
    not_cone10_of_mod32_ne_13 x (by have h := mod32_of_cone8 x hc8; omega)
  have hnc9_x : ¬ isDiamond8Cone9 x :=
    not_cone9_of_mod32_ne_13 x (by have h := mod32_of_cone8 x hc8; omega)
  have hx_ge : x ≥ 12548309 := hc8.1
  rcases (cousin_diamond8_cones4to9_exact_return.2.2.2.2.1 x hc8) with
    ⟨u, v, _, hu22, hv1, hmul, hd8_x, _, _, _, _⟩
  let y := 2 ^ (u - 7) * 3 ^ (v + 1) - 811
  have hstep_x : cousinDiamond9Step x = y := by
    rw [cousinDiamond9Step_eq_d8_of_not_cone10 x hnc10_x]; exact hd8_x
  have hy_step : y = (3 * x + 1) / 128 :=
    hd8_x.symm.trans (by
      rw [cousinDiamond8Step_eq_d7_of_not_cone9 x hnc9_x]
      unfold cousinDiamond7Step; simp [hc8])
  clear hc8 hnc10_x hnc9_x hd8_x
  have hc7_y : isDiamond6Cone7 y :=
    isDiamond6Cone7_of_pow2_pow3 (u - 7) (v + 1) (by omega) (by omega)
  rcases cousin_diamond9_cone7_return_aux y hc7_y with ⟨_, _, ky, _, _, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hdiv : y * 128 ≤ 3 * x + 1 := by rw [hy_step]; exact Nat.div_mul_le_self (3 * x + 1) 128
    clear hy_step hmul hstep_x hc7_y hky_1; omega
  have h1ky_x : 1 + ky ≤ x := by clear hy_step hmul hstep_x hc7_y hky_1; omega
  have h1ky_phi : 1 + ky ≤ cousinDiamond2Phi x :=
    Nat.le_trans (by clear hy_step hmul hstep_x hc7_y hky_1; omega : 1 + ky ≤ x + 1) (cousinDiamond2Phi_ge_succ x)
  refine ⟨u, v, 1 + ky, hu22, hv1, hmul, hstep_x, ?_, h1ky_x, h1ky_phi, ?_⟩
  · rw [hstep_x]; exact hc7_y
  · rw [cousinDiamond9Iter_add 1 ky x]
    have hi1 : cousinDiamond9Iter 1 x = y := hstep_x
    rw [hi1]; exact hky_1

theorem cousin_diamond9_cone9_return_aux (x : Nat) (hc9 : isDiamond8Cone9 x) :
    ∃ (w z k : Nat),
      w ≥ 25 ∧ z ≥ 1 ∧ x + 92275 = 2 ^ w * 3 ^ z ∧
      cousinDiamond9Step x = 2 ^ (w - 3) * 3 ^ (z + 1) - 34603 ∧
      isDiamond7Cone8 (cousinDiamond9Step x) ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond9Iter k x = 1 := by
  have hnc10_x : ¬ isDiamond9Cone10 x :=
    not_cone10_of_mod256_ne_205 x (by rw [mod256_of_cone9 x hc9]; decide)
  have hx_ge : x ≥ 100571021 := hc9.1
  rcases (cousin_diamond8_cones4to9_exact_return.2.2.2.2.2 x hc9) with
    ⟨w, z, _, hw25, hz1, hmul, hd8_x, _, _, _, _⟩
  let y := 2 ^ (w - 3) * 3 ^ (z + 1) - 34603
  have hstep_x : cousinDiamond9Step x = y := by
    rw [cousinDiamond9Step_eq_d8_of_not_cone10 x hnc10_x]; exact hd8_x
  have hy_step : y = (3 * x + 1) / 8 :=
    hd8_x.symm.trans (by unfold cousinDiamond8Step; simp [hc9])
  clear hc9 hnc10_x hd8_x
  have hc8_y : isDiamond7Cone8 y :=
    isDiamond7Cone8_of_pow2_pow3 (w - 3) (z + 1) (by omega) (by omega)
  rcases cousin_diamond9_cone8_return_aux y hc8_y with ⟨_, _, ky, _, _, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hdiv : y * 8 ≤ 3 * x + 1 := by rw [hy_step]; exact Nat.div_mul_le_self (3 * x + 1) 8
    clear hy_step hmul hstep_x hc8_y hky_1; omega
  have h1ky_x : 1 + ky ≤ x := by clear hy_step hmul hstep_x hc8_y hky_1; omega
  have h1ky_phi : 1 + ky ≤ cousinDiamond2Phi x :=
    Nat.le_trans (by clear hy_step hmul hstep_x hc8_y hky_1; omega : 1 + ky ≤ x + 1) (cousinDiamond2Phi_ge_succ x)
  refine ⟨w, z, 1 + ky, hw25, hz1, hmul, hstep_x, ?_, h1ky_x, h1ky_phi, ?_⟩
  · rw [hstep_x]; exact hc8_y
  · rw [cousinDiamond9Iter_add 1 ky x]
    have hi1 : cousinDiamond9Iter 1 x = y := hstep_x
    rw [hi1]; exact hky_1

/--
  Theorem W12.3g (`cousin_diamond9_cones4to10_exact_return`, `zero custom axioms`):
  Exact 7-Tier `ω^7` Multi-Block Return Across Cones 4, 5, 6, 7, 8, 9, AND 10 of `T_diamond9`:
  1–6. Every `x` in Cone 4, 5, 6, 7, 8, or 9 reaches `1` in `k ≤ cousinDiamond2Phi x` steps!
  7. Every `x` in Cone 10 (`isDiamond9Cone10 x`) has `x + 246067 = 2 ^ p * 3 ^ q` (`p ≥ 28, q ≥ 1`),
     steps in 1 genuine `v_2(3x + 1) = 3` jump `(3 * x + 1) / 8` directly into the Cone-9 state
     `y = 2 ^ (p - 3) * 3 ^ (q + 1) - 92275`, and reaches `1` in `1 + k_y ≤ x` (`≤ cousinDiamond2Phi x`) steps!
-/
theorem cousin_diamond9_cones4to10_exact_return :
    (∀ x : Nat, isDiamond3Cone4 x ->
      ∃ k : Nat, k ≤ cousinDiamond2Phi x ∧ cousinDiamond9Iter k x = 1) ∧
    (∀ x : Nat, isDiamond4Cone5 x ->
      ∃ (a b k : Nat),
        a ≥ 5 ∧ b ≥ 1 ∧ x + 7 = 2 ^ a * 3 ^ b ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond9Iter k x = 1) ∧
    (∀ x : Nat, isDiamond5Cone6 x ->
      ∃ (e f k : Nat),
        e ≥ 8 ∧ f ≥ 2 ∧ x + 19 = 2 ^ e * 3 ^ f ∧
        cousinDiamond9Step x = 2 ^ (e - 3) * 3 ^ (f + 1) - 7 ∧
        isDiamond4Cone5 (cousinDiamond9Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond9Iter k x = 1) ∧
    (∀ x : Nat, isDiamond6Cone7 x ->
      ∃ (g h k : Nat),
        g ≥ 15 ∧ h ≥ 2 ∧ x + 811 = 2 ^ g * 3 ^ h ∧
        cousinDiamond9Step x = 2 ^ (g - 7) * 3 ^ (h + 1) - 19 ∧
        isDiamond5Cone6 (cousinDiamond9Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond9Iter k x = 1) ∧
    (∀ x : Nat, isDiamond7Cone8 x ->
      ∃ (u v k : Nat),
        u ≥ 22 ∧ v ≥ 1 ∧ x + 34603 = 2 ^ u * 3 ^ v ∧
        cousinDiamond9Step x = 2 ^ (u - 7) * 3 ^ (v + 1) - 811 ∧
        isDiamond6Cone7 (cousinDiamond9Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond9Iter k x = 1) ∧
    (∀ x : Nat, isDiamond8Cone9 x ->
      ∃ (w z k : Nat),
        w ≥ 25 ∧ z ≥ 1 ∧ x + 92275 = 2 ^ w * 3 ^ z ∧
        cousinDiamond9Step x = 2 ^ (w - 3) * 3 ^ (z + 1) - 34603 ∧
        isDiamond7Cone8 (cousinDiamond9Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond9Iter k x = 1) ∧
    (∀ x : Nat, isDiamond9Cone10 x ->
      ∃ (p q k : Nat),
        p ≥ 28 ∧ q ≥ 1 ∧ x + 246067 = 2 ^ p * 3 ^ q ∧
        cousinDiamond9Step x = 2 ^ (p - 3) * 3 ^ (q + 1) - 92275 ∧
        isDiamond8Cone9 (cousinDiamond9Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond9Iter k x = 1) := by
  refine ⟨cousin_diamond9_cone4_return_aux,
          cousin_diamond9_cone5_return_aux,
          cousin_diamond9_cone6_return_aux,
          cousin_diamond9_cone7_return_aux,
          cousin_diamond9_cone8_return_aux,
          cousin_diamond9_cone9_return_aux, ?_⟩
  intro x hc10
  have hraw_step : cousinDiamond9Step x = (3 * x + 1) / 8 := by
    unfold cousinDiamond9Step; simp only [hc10, ite_true]
  rcases hc10 with ⟨hx_ge, hx268m, hx3, hg1⟩
  have hdvd268m : 268435456 ∣ (x + 246067) :=
    Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, hx268m])
  clear hx268m
  rcases (⟨246067 + x, rfl⟩ : ∃ N : Nat, N = 246067 + x) with ⟨N, hN_def⟩
  rw [← hN_def] at hg1
  have hN_pos : N > 0 := by clear hraw_step hdvd268m hx3 hg1; omega
  rcases decomp_2_3_exact N hN_pos with ⟨_, _, _, _, _, hmul⟩
  rw [hg1, Nat.mul_one] at hmul
  rcases eq_pow2_of_v2Pow_aux N N hN_pos (Nat.le_refl _) with ⟨p, hp⟩
  rcases eq_pow3_of_v3Pow_aux N N hN_pos (Nat.le_refl _) with ⟨q, hq⟩
  rw [hp, hq] at hmul
  have hmul_comm : x + 246067 = 2 ^ p * 3 ^ q := by
    rw [Nat.add_comm x 246067, ← hN_def, ← hmul]
  clear hg1 hp hq hN_def hmul hN_pos
  have hp28 : p ≥ 28 := by
    by_cases hlt : p < 28
    · exfalso
      have h268m_sp : 268435456 = 2 ^ (p + 1) * 2 ^ (27 - p) := by
        have hsum28 : p + 1 + (27 - p) = 28 := by clear hraw_step hx_ge hx3 hdvd268m hmul_comm; omega
        rw [← Nat.pow_add 2 (p + 1) (27 - p), hsum28]
      rcases hdvd268m with ⟨c, hc⟩
      rw [hmul_comm, h268m_sp, Nat.mul_assoc (2 ^ (p + 1)),
          Nat.pow_succ 2 p, Nat.mul_assoc (2 ^ p) 2] at hc
      have h3q_ev : 3 ^ q = 2 * (2 ^ (27 - p) * c) :=
        nat_mul_left_cancel_pos (2 ^ p) _ _ (pow2_pos_nat p) hc
      have ho := pow3_odd_nat_sec8 q
      rw [h3q_ev, Nat.mul_mod_right] at ho
      cases ho
    · clear hraw_step hx_ge hx3 hdvd268m hmul_comm; omega
  clear hdvd268m
  have hq1 : q ≥ 1 := by
    cases q with
    | zero =>
      rw [Nat.pow_zero, Nat.mul_one] at hmul_comm
      exact False.elim (pow2_mod3_nonzero_w5 p (by rw [← hmul_comm, Nat.add_mod, hx3]))
    | succ _ => clear hraw_step hx_ge hx3 hmul_comm hp28; omega
  clear hx3
  let y := 2 ^ (p - 3) * 3 ^ (q + 1) - 92275
  have hstep_x : cousinDiamond9Step x = y := by
    rw [hraw_step]
    dsimp [y]
    have hp8 : 2 ^ p = 8 * 2 ^ (p - 3) := by
      have hp_sp : p = 3 + (p - 3) := by clear hraw_step hx_ge hmul_comm hq1; omega
      conv => lhs; rw [hp_sp]; rw [Nat.pow_add]
    have hprod_pos : 2 ^ (p - 3) * 3 ^ q ≥ 33554432 * 3 := by
      have h1 : 33554432 ≤ 2 ^ (p - 3) := by
        have hc : (2 : Nat) ^ 25 = 33554432 := by decide
        have h25 : 25 ≤ p - 3 := by clear hraw_step hx_ge hmul_comm hq1 hp8; omega
        rw [← hc]; exact pow2_mono_nat h25
      have h2 : 3 ≤ 3 ^ q := by simpa using nat_pow_mono_exp_pos 3 1 q (by decide) hq1
      simpa using Nat.mul_le_mul h1 h2
    have h3_eq : 2 ^ (p - 3) * 3 ^ (q + 1) = 3 * (2 ^ (p - 3) * 3 ^ q) := by
      rw [Nat.pow_succ 3 q, ← Nat.mul_assoc, Nat.mul_comm _ 3]
    rw [h3_eq]
    have hx8 : x + 246067 = 8 * (2 ^ (p - 3) * 3 ^ q) := by
      rw [hmul_comm, hp8, Nat.mul_assoc]
    have h3x1 : 3 * x + 1 = (3 * (2 ^ (p - 3) * 3 ^ q) - 92275) * 8 := by
      clear hraw_step hp28 hq1 hp8 h3_eq hmul_comm
      generalize 2 ^ (p - 3) * 3 ^ q = A at hprod_pos hx8 ⊢
      omega
    rw [h3x1]
    exact Nat.mul_div_left _ (by decide : 0 < 8)
  have hc9_y : isDiamond8Cone9 y :=
    isDiamond8Cone9_of_pow2_pow3 (p - 3) (q + 1)
      (by clear hraw_step hx_ge hmul_comm hstep_x; omega)
      (by clear hraw_step hx_ge hmul_comm hstep_x; omega)
  rcases cousin_diamond9_cone9_return_aux y hc9_y with ⟨_, _, ky, _, _, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hstep_eq : y = (3 * x + 1) / 8 := hstep_x.symm.trans hraw_step
    have hdiv : y * 8 ≤ 3 * x + 1 := by rw [hstep_eq]; exact Nat.div_mul_le_self (3 * x + 1) 8
    clear hraw_step hmul_comm hstep_x hc9_y hky_1 hstep_eq
    omega
  have h1ky_x : 1 + ky ≤ x := by clear hraw_step hmul_comm hstep_x hc9_y hky_1; omega
  have h1ky_phi : 1 + ky ≤ cousinDiamond2Phi x :=
    Nat.le_trans (by clear hraw_step hmul_comm hstep_x hc9_y hky_1; omega : 1 + ky ≤ x + 1)
      (cousinDiamond2Phi_ge_succ x)
  refine ⟨p, q, 1 + ky, hp28, hq1, hmul_comm, hstep_x, ?_, h1ky_x, h1ky_phi, ?_⟩
  · rw [hstep_x]; exact hc9_y
  · rw [cousinDiamond9Iter_add 1 ky x]
    have hi1 : cousinDiamond9Iter 1 x = y := hstep_x
    rw [hi1]; exact hky_1

theorem cousin_diamond9_reaches_one_within_phi :
    ∀ (B x : Nat), x > 0 -> cousinDiamond2Phi x ≤ B ->
      ∃ k : Nat, k ≤ B ∧ cousinDiamond9Iter k x = 1
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
        · rcases cousin_diamond9_cones4to10_exact_return.1 x hc4 with ⟨k, hle_phi, hk1⟩
          exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
        · by_cases hc5 : isDiamond4Cone5 x
          · rcases cousin_diamond9_cones4to10_exact_return.2.1 x hc5 with
              ⟨_, _, k, _, _, _, _, hle_phi, hk1⟩
            exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
          · by_cases hc6 : isDiamond5Cone6 x
            · rcases cousin_diamond9_cones4to10_exact_return.2.2.1 x hc6 with
                ⟨_, _, k, _, _, _, _, _, _, hle_phi, hk1⟩
              exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
            · by_cases hc7 : isDiamond6Cone7 x
              · rcases cousin_diamond9_cones4to10_exact_return.2.2.2.1 x hc7 with
                  ⟨_, _, k, _, _, _, _, _, _, hle_phi, hk1⟩
                exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
              · by_cases hc8 : isDiamond7Cone8 x
                · rcases cousin_diamond9_cones4to10_exact_return.2.2.2.2.1 x hc8 with
                    ⟨_, _, k, _, _, _, _, _, _, hle_phi, hk1⟩
                  exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
                · by_cases hc9 : isDiamond8Cone9 x
                  · rcases cousin_diamond9_cones4to10_exact_return.2.2.2.2.2.1 x hc9 with
                      ⟨_, _, k, _, _, _, _, _, _, hle_phi, hk1⟩
                    exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
                  · by_cases hc10 : isDiamond9Cone10 x
                    · rcases cousin_diamond9_cones4to10_exact_return.2.2.2.2.2.2 x hc10 with
                        ⟨_, _, k, _, _, _, _, _, _, hle_phi, hk1⟩
                      exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
                    · have hdesc := cousin_diamond9_outside_cones4to10_strict_descent x
                        (by omega) hc4 hc5 hc6 hc7 hc8 hc9 hc10
                      have hpos := cousinDiamond9Step_pos x hx
                      rcases cousin_diamond9_reaches_one_within_phi B (cousinDiamond9Step x) hpos (by omega) with
                        ⟨k, hk_le, hk_eq⟩
                      exact ⟨k + 1, by omega, hk_eq⟩

/--
  Theorem W12.3h (`cousin_diamond9_global_convergence`, `zero custom axioms`):
  Unconditional Global Convergence & Degree-5 Polynomial Stopping Bound for `T_diamond9`:
  For EVERY `x > 0`, `cousinDiamond9Iter` reaches `1` within `k ≤ (x + 1) ^ 3 + (x + 1) ^ 5` steps!
-/
theorem cousin_diamond9_global_convergence (x : Nat) (hx : x > 0) :
    ∃ k : Nat, k ≤ (x + 1) ^ 3 + (x + 1) ^ 5 ∧ cousinDiamond9Iter k x = 1 := by
  rcases cousin_diamond9_reaches_one_within_phi (cousinDiamond2Phi x) x hx (Nat.le_refl _) with
    ⟨k, hk_phi, hk1⟩
  exact ⟨k, Nat.le_trans hk_phi (cousinDiamond2Phi_upper_poly_bound x), hk1⟩

theorem exists_non_desc_along_diamond9_iter_clean :
    ∀ (terms : List LaurentTerm) (A0 B0 C0 N z : Nat),
      N ≥ 1 ->
      (∀ i : Nat, i < N ->
        cousinDiamond9Iter i z ≥ 3 ∧
        (cousinDiamond9Iter i z) % 2 = 1 ∧
        cousinDiamond9Step (cousinDiamond9Iter i z) ≥ 3) ->
      ¬ laurentDescProp terms A0 B0 C0 z (cousinDiamond9Iter N z) ->
      ∃ x : Nat,
        x ≥ 3 ∧ x % 2 = 1 ∧ cousinDiamond9Step x ≥ 3 ∧
        ¬ laurentDescProp terms A0 B0 C0 x (cousinDiamond9Step x)
  | _, _, _, _, 0, _, hN, _, _ => by omega
  | _, _, _, _, 1, z, _, hall, hnd => by
    rcases hall 0 (by decide) with ⟨hz3, hzo, hsz3⟩
    exact ⟨z, hz3, hzo, hsz3, hnd⟩
  | terms, A0, B0, C0, m + 2, z, _, hall, hnd => by
    if h0 : laurentDescProp terms A0 B0 C0 z (cousinDiamond9Step z) then
      have hnd_next : ¬ laurentDescProp terms A0 B0 C0 (cousinDiamond9Step z)
          (cousinDiamond9Iter (m + 1) (cousinDiamond9Step z)) :=
        fun hrest => hnd (laurentDescProp_trans terms A0 B0 C0 z (cousinDiamond9Step z) _ h0 hrest)
      exact exists_non_desc_along_diamond9_iter_clean terms A0 B0 C0 (m + 1) (cousinDiamond9Step z)
        (by omega) (fun i hi => hall (i + 1) (by omega)) hnd_next
    else
      rcases hall 0 (by omega) with ⟨hz3, hzo, hsz3⟩
      exact ⟨z, hz3, hzo, hsz3, h0⟩

/--
  Theorem W12.3i (`cousin_diamond9_r_block_spiral_climb_and_laurent_impossibility`, `zero custom axioms`):
  1. Cone-10 -> Cone-9 -> Cone-8 -> Cone-7 -> Cone-6 -> Cone-5 7-Tier Cascade & Unbounded `r`-Block Spiral Climb:
     `1610366669 -> 603887501 -> 226457813 -> 5307605 -> 124397 -> 46649` AND
     `cousinDiamond9Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5` for ALL `r ≥ 1, j ≤ r`!
  2. Universal `∀ L ≥ 1` Multi-Term Laurent Valuation Impossibility on `cousinDiamond9Step`!
-/
theorem cousin_diamond9_r_block_spiral_climb_and_laurent_impossibility :
    cousinDiamond9Step 1610366669 = 603887501 ∧
    cousinDiamond9Step 603887501 = 226457813 ∧
    cousinDiamond9Step 226457813 = 5307605 ∧
    cousinDiamond9Step 5307605 = 124397 ∧
    cousinDiamond9Step 124397 = 46649 ∧
    (∀ (r j : Nat), r ≥ 1 -> j ≤ r ->
      cousinDiamond9Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5) ∧
    (∀ (terms : List LaurentTerm) (A0 B0 C0 : Nat),
      (∃ t ∈ terms, t.coeff > 0) ->
      ∃ x : Nat,
        x ≥ 3 ∧ x % 2 = 1 ∧ cousinDiamond9Step x ≥ 3 ∧
        ¬ (evalLaurentSumNum terms (cousinDiamond9Step x) * laurentValDen A0 B0 C0 x <
            evalLaurentSumNum terms x * laurentValDen A0 B0 C0 (cousinDiamond9Step x))) := by
  have hspiral : ∀ (r j : Nat), r ≥ 1 -> j ≤ r ->
      cousinDiamond9Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5 := by
    intro r j hr hj
    cases j with
    | zero => simp [cousinDiamond9Iter]
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
      have hs_first : cousinDiamond9Step x0 = 2 ^ (4 * r + 1) * 3 ^ 1 - 7 := by
        rw [cousinDiamond9Step_eq_d8_of_not_cone10 x0 (not_cone10_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond8Step_eq_d7_of_not_cone9 x0 (not_cone9_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond7Step_eq_d6_of_not_cone8 x0 (not_cone8_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond6Step_eq_d5_of_not_cone7 x0 (not_cone7_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond5Step_eq_d4_of_not_cone6 x0 (not_cone6_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond4Step_mod4_eq_3 x0 hx0_m4]
        dsimp [x0]
        rw [hx0_pow, show 4 * r + 2 = (4 * r + 1) + 1 by omega, Nat.pow_succ 2 (4 * r + 1)]
        have hp := pow2_pos_nat (4 * r + 1); omega
      have hclimb := cousin_diamond9_cone5_two_step_climb j' (4 * r + 1) 1 (by omega) (by decide)
      let y_end := 2 ^ (4 * r + 1 - 3 * j') * 3 ^ (1 + 2 * j') - 7
      have hy_c5 : isDiamond4Cone5 y_end :=
        isDiamond4Cone5_of_pow2_pow3 (4 * r + 1 - 3 * j') (1 + 2 * j') (by omega) (by omega)
      have hy_nc10 : ¬ isDiamond9Cone10 y_end :=
        not_cone10_of_mod32_ne_13 y_end (by have h := hy_c5.2.1; omega)
      have hy_nc9 : ¬ isDiamond8Cone9 y_end :=
        not_cone9_of_mod32_ne_13 y_end (by have h := hy_c5.2.1; omega)
      have hy_nc8 : ¬ isDiamond7Cone8 y_end :=
        not_cone8_of_mod32_ne_21 y_end (by have h := hy_c5.2.1; omega)
      have hy_nc7 : ¬ isDiamond6Cone7 y_end :=
        not_cone7_of_mod32_ne_21 y_end (by have h := hy_c5.2.1; omega)
      have hy_nc6 : ¬ isDiamond5Cone6 y_end :=
        not_cone6_of_mod32_ne_13 y_end (by have h := hy_c5.2.1; omega)
      have hs_last : cousinDiamond9Step y_end = 4 * 16 ^ (r - (j' + 1)) * 18 ^ (j' + 1) - 5 := by
        rw [cousinDiamond9Step_eq_d8_of_not_cone10 y_end hy_nc10,
            cousinDiamond8Step_eq_d7_of_not_cone9 y_end hy_nc9,
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
          ac_rfl
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
                = 2 ^ (4 * r + 1 - 3 * j') * (3 * 3 ^ (1 + 2 * j')) := by ac_rfl
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
          cousinDiamond9Iter_add (1 + 2 * j') 1,
          cousinDiamond9Iter_add 1 (2 * j')]
      have hi1 : cousinDiamond9Iter 1 x0 = 2 ^ (4 * r + 1) * 3 ^ 1 - 7 := hs_first
      rw [hi1, hclimb]
      exact hs_last
  refine ⟨by decide, by decide, by decide, by decide, by decide, hspiral, ?_⟩
  intro terms A0 B0 C0 hnonempty
  rcases three_family_multiterm_laurent_obstruction terms A0 B0 C0 hnonempty with
    h97 | ⟨j2, hj2⟩ | ⟨r, hr_pos, hr3⟩
  · have hs97 : cousinDiamond9Step 97 = 73 := by decide
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
      refine ⟨by dsimp [xj2]; omega, by dsimp [xj2]; omega, ?_⟩
      have hpow2 : 3 * xj2 + 5 = 2 ^ (6 * j2 + 9) * 1 := by
        rw [Nat.mul_one, show 6 * j2 + 9 = 2 * (3 * j2 + 4) + 1 by omega,
            Nat.pow_succ, ← pow4_eq_pow2_even (3 * j2 + 4), Nat.mul_comm]
        dsimp [xj2]; omega
      rw [hpow2]
      exact core2_pow2_mul (6 * j2 + 9) 1 (by decide) (by decide)
    have hstep_xj2 : cousinDiamond9Step xj2 = yj2 := by
      rw [cousinDiamond9Step_eq_d8_of_not_cone10 xj2
            (not_cone10_of_mod8_ne_5 xj2 (by have h := hc4_xj2.2.1; omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 xj2
            (not_cone9_of_mod8_ne_5 xj2 (by have h := hc4_xj2.2.1; omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 xj2
            (not_cone8_of_mod8_ne_5 xj2 (by have h := hc4_xj2.2.1; omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 xj2
            (not_cone7_of_mod8_ne_5 xj2 (by have h := hc4_xj2.2.1; omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 xj2
            (by rintro ⟨_, h256, _, _⟩; have h := hc4_xj2.2.1; omega)]
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
        cousinDiamond9Iter i xr3 = 3 ^ i * 2 ^ (2 * r + 1 - i) - 1 ∧
        cousinDiamond9Iter i xr3 ≥ 7 ∧
        (cousinDiamond9Iter i xr3) % 2 = 1 := by
      intro i hi
      have hf := cousin_diamond9_mersenne_scaled i (2 * r + 1) 1 (by omega) (by decide)
      rw [← hxr3_pow, Nat.mul_one] at hf
      have hprod_ge8 : 3 ^ i * 2 ^ (2 * r + 1 - i) ≥ 8 := by
        have h1 : 2 ^ i * 2 ^ (2 * r + 1 - i) ≤ 3 ^ i * 2 ^ (2 * r + 1 - i) :=
          Nat.mul_le_mul_right _ (pow2_le_pow3 i)
        rw [← Nat.pow_add, show i + (2 * r + 1 - i) = 2 * r + 1 by omega] at h1
        exact Nat.le_trans (pow2_mono_nat (by omega : 3 ≤ 2 * r + 1)) h1
      have hprod_ev : (3 ^ i * 2 ^ (2 * r + 1 - i)) % 2 = 0 := by
        rw [show 2 * r + 1 - i = (2 * r - i) + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc]; omega
      exact ⟨hf, by rw [hf]; omega, by rw [hf]; omega⟩
    have hiter_2r : cousinDiamond9Iter (2 * r) xr3 = zr := by
      have hf := (hglide_i (2 * r) (Nat.le_refl _)).1
      rw [hf, show 2 * r + 1 - 2 * r = 1 by omega, Nat.pow_one,
          ← pow9_eq_pow3_double r, Nat.mul_comm]
    have hstep_zr : cousinDiamond9Step zr = yr3 := by
      rw [cousinDiamond9Step_eq_d8_of_not_cone10 zr (not_cone10_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 zr (not_cone9_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
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
    have hiter_2r1 : cousinDiamond9Iter (2 * r + 1) xr3 = yr3 := by
      rw [cousinDiamond9Iter_add (2 * r) 1 xr3, hiter_2r]; exact hstep_zr
    have hall : ∀ i : Nat, i < 2 * r + 1 ->
        cousinDiamond9Iter i xr3 ≥ 3 ∧
        (cousinDiamond9Iter i xr3) % 2 = 1 ∧
        cousinDiamond9Step (cousinDiamond9Iter i xr3) ≥ 3 := by
      intro i hi
      by_cases hlt : i < 2 * r
      · rcases hglide_i i (by omega) with ⟨_, hge7, hodd_i⟩
        have hnext : cousinDiamond9Step (cousinDiamond9Iter i xr3) =
            cousinDiamond9Iter (i + 1) xr3 :=
          (cousinDiamond9Iter_add i 1 xr3).symm
        rcases hglide_i (i + 1) (by omega) with ⟨_, hge7_n, _⟩
        exact ⟨by omega, hodd_i, by rw [hnext]; omega⟩
      · have hi_eq : i = 2 * r := by omega
        rw [hi_eq, hiter_2r, hstep_zr]
        exact ⟨by dsimp [zr]; omega, by dsimp [zr]; omega, by dsimp [yr3]; omega⟩
    change ¬ laurentDescProp terms A0 B0 C0 xr3 yr3 at hr3
    rw [← hiter_2r1] at hr3
    exact exists_non_desc_along_diamond9_iter_clean terms A0 B0 C0 (2 * r + 1) xr3 (by omega) hall hr3

/--
  Theorem W12.3j (`cousin_diamond9_q6_noninteger_avoids_cone10`, choice-free `zero custom axioms`):
  Universal Non-Integer Rational Exclusion from Cone 10 on `M1 = Q_(6)^+`:
  For EVERY reduced non-integer rational `(num, den)` (`Nat.gcd num den = 1` and `den > 1`),
  `core3 (core2 (246067 * den + num)) ≠ den`, so `cousinDiamond9StepQ6 (num, den)` NEVER enters
  Cone 10 and agrees identically with `cousinDiamond8StepQ6 (num, den)`!
-/
theorem cousin_diamond9_q6_noninteger_avoids_cone10 (num den : Nat)
    (hgcd : Nat.gcd num den = 1) (hden : den > 1) :
    core3 (core2 (246067 * den + num)) ≠ den ∧
    cousinDiamond9StepQ6 (num, den) = cousinDiamond8StepQ6 (num, den) := by
  have hne : core3 (core2 (246067 * den + num)) ≠ den := by
    intro heq
    have hdvd_sum : den ∣ (246067 * den + num) := by
      have hc_dvd : core3 (core2 (246067 * den + num)) ∣ (246067 * den + num) :=
        Nat.dvd_trans (core3Aux_dvd_w8 _ _) (core2Aux_dvd_w8 _ _)
      rwa [heq] at hc_dvd
    rcases hdvd_sum with ⟨k, hk⟩
    have hdvd_num : den ∣ num := ⟨k - 246067, by
      have hge : k ≥ 246067 := by
        by_cases hlt : k < 246067
        · have hm := Nat.mul_le_mul_left den (show k ≤ 246066 by omega); omega
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
  unfold cousinDiamond9StepQ6
  have hcond : ¬ (num ≥ 805060301 * den ∧ (num * invMod268435456Odd den) % 268435456 = 268189389 ∧
      (num * (den % 3)) % 3 = 2 ∧ core3 (core2 (246067 * den + num)) = den) :=
    fun ⟨_, _, _, hc⟩ => hne hc
  simp only [hcond, ite_false]

private theorem hensel_inv_lift_nat (M1 M2 S C d i1 : Nat)
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
    calc
      x = (M2 * (d / M2) + d % M2) * i1 := by dsimp [x]; rw [← hd_div]
      _ = M2 * ((d / M2) * i1) + (d % M2) * i1 := by rw [Nat.add_mul, Nat.mul_assoc]
      _ = M2 * ((d / M2) * i1) + (M2 * (((d % M2) * i1) / M2) + r) := by rw [← hdr_div]
      _ = M2 * K + r := by dsimp [K]; rw [Nat.mul_add]; omega
  let q1 := x / M1
  have hx_M1 : x = M1 * q1 + 1 := by
    have hdm := (Nat.div_add_mod x M1).symm
    dsimp [x] at hdm ⊢
    rw [h1] at hdm
    exact hdm
  have hsq_x : (M1 * q1) * (M1 * q1) + 2 * x = x * x + 1 := by
    rw [hx_M1]
    calc
      (M1 * q1) * (M1 * q1) + 2 * (M1 * q1 + 1)
          = (M1 * q1) * (M1 * q1) + (M1 * q1) + (M1 * q1 + 1) + 1 := by omega
      _ = (M1 * q1 + 1) * (M1 * q1 + 1) + 1 := by
            rw [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  have hmain : x * (C - r) + M2 * (S * (q1 * q1)) = M2 * (x * (2 + K)) + 1 := by
    have hlhs1 : (M1 * q1) * (M1 * q1) = M2 * (S * (q1 * q1)) := by
      calc
        (M1 * q1) * (M1 * q1) = (M1 * M1) * (q1 * q1) := by ac_rfl
        _ = (M2 * S) * (q1 * q1) := by rw [hsq]
        _ = M2 * (S * (q1 * q1)) := by ac_rfl
    have hsplit_c : C - r = (2 * M2 - r) + 2 := by omega
    calc
      x * (C - r) + M2 * (S * (q1 * q1))
          = x * (2 * M2 - r) + (x * 2 + (M1 * q1) * (M1 * q1)) := by
              rw [hsplit_c, Nat.mul_add, ← hlhs1, Nat.add_assoc]
      _ = x * (2 * M2 - r) + (x * x + 1) := by
            rw [Nat.mul_comm x 2, Nat.add_comm (2 * x), hsq_x]
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
      have hgt : x * (2 + K) + 1 ≤ S * (q1 * q1) := by omega
      have hm := Nat.mul_le_mul_left M2 hgt
      rw [Nat.mul_add, Nat.mul_one] at hm
      omega
  have hx_mod : (x * (C - r)) % M2 = 1 := by
    have hm_sub : M2 * (x * (2 + K) - S * (q1 * q1)) + M2 * (S * (q1 * q1)) = M2 * (x * (2 + K)) := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hle_q]
    have heq : x * (C - r) = M2 * (x * (2 + K) - S * (q1 * q1)) + 1 := by
      generalize x * (C - r) = A, M2 * (S * (q1 * q1)) = B,
        M2 * (x * (2 + K)) = E, M2 * (x * (2 + K) - S * (q1 * q1)) = F at hmain hm_sub ⊢
      omega
    rw [heq, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hM2]
  let Y := i1 * (C - r)
  have hdY : d * Y = M2 * (d * (Y / M2)) + d * (Y % M2) := by
    conv => lhs; rhs; rw [(Nat.div_add_mod Y M2).symm]
    rw [Nat.mul_add, ← Nat.mul_assoc d M2, Nat.mul_comm d M2, Nat.mul_assoc M2 d]
  have hdY_mod : (d * Y) % M2 = (d * (Y % M2)) % M2 := by
    rw [hdY, Nat.add_comm (M2 * (d * (Y / M2))), Nat.add_mul_mod_self_left]
  have hdY_eq : d * Y = x * (C - r) := by dsimp [x, Y]; ac_rfl
  dsimp [Y] at hdY_mod
  rw [← hdY_mod, hdY_eq, hx_mod]

private theorem invMod64Odd_fin_ok :
    ∀ r : Fin 64, r.val % 2 = 1 -> (r.val * invMod64Odd r.val) % 64 = 1 := by
  decide

private theorem invMod64Odd_mul_mod (d : Nat) (hodd : d % 2 = 1) :
    (d * invMod64Odd d) % 64 = 1 := by
  let r := d % 64
  have hr_odd : r % 2 = 1 := by dsimp [r]; omega
  have hinv_eq : invMod64Odd d = invMod64Odd r := by
    unfold invMod64Odd; dsimp [r]; rw [Nat.mod_mod]
  have hr_mod : (r * invMod64Odd r) % 64 = 1 :=
    invMod64Odd_fin_ok ⟨r, Nat.mod_lt d (by decide)⟩ hr_odd
  have hd_split : d * invMod64Odd r = 64 * ((d / 64) * invMod64Odd r) + r * invMod64Odd r := by
    conv => lhs; lhs; rw [(Nat.div_add_mod d 64).symm]
    rw [Nat.add_mul, Nat.mul_assoc]
  rw [hinv_eq, hd_split, Nat.add_comm (64 * ((d / 64) * invMod64Odd r)),
      Nat.add_mul_mod_self_left, hr_mod]

set_option maxRecDepth 16384 in
private theorem invMod256Odd_fin_ok :
    ∀ r : Fin 256, r.val % 2 = 1 -> (r.val * invMod256Odd r.val) % 256 = 1 := by
  decide

private theorem core3_core2_eq_coprime23Core_aux :
    ∀ (fuel n : Nat), n > 0 -> n ≤ fuel -> core3 (core2 n) = coprime23Core n
  | 0, _, hn, hle => by omega
  | fuel + 1, n, hn, hle => by
    by_cases hev : n % 2 = 0
    · let k := n / 2
      have hk_pos : k > 0 := by dsimp [k]; omega
      have hn_eq : n = 2 * k := by dsimp [k]; omega
      rw [hn_eq, core2_mul2 k hk_pos, coprime23Core_mul2 k hk_pos]
      exact core3_core2_eq_coprime23Core_aux fuel k hk_pos (by dsimp [k]; omega)
    · have hodd : n % 2 = 1 := by omega
      rcases core3_decomp n hn with ⟨_, _, _, _, hmul⟩
      have hc3_odd : core3 n % 2 = 1 := by
        by_cases hc3_ev : core3 n % 2 = 0
        · have hm0 : (v3Pow n * core3 n) % 2 = 0 := by
            rw [Nat.mul_mod, hc3_ev, Nat.mul_zero]
          rw [hmul] at hm0; omega
        · omega
      unfold coprime23Core
      rw [core2_of_odd n hodd, core2_of_odd (core3 n) hc3_odd]

private theorem reduceRatPair_div_exact (a m : Nat) (hm : m > 0) (hdvd : m ∣ a) :
    reduceRatPair a m = (a / m, 1) := by
  rcases hdvd with ⟨q, rfl⟩
  unfold reduceRatPair
  have hgcd : Nat.gcd (m * q) m = m :=
    Nat.dvd_antisymm (Nat.gcd_dvd_right (m * q) m) (Nat.dvd_gcd ⟨q, rfl⟩ (Nat.dvd_refl m))
  dsimp only
  rw [hgcd, Nat.div_self hm]

private theorem dvd_three_mul_add_one_of_mod (x M D Qm Qr R Qt : Nat)
    (hM : M = D * Qm) (hmod : x % M = D * Qr + R) (h3 : 3 * R + 1 = D * Qt) :
    D ∣ (3 * x + 1) := by
  refine ⟨3 * (Qm * (x / M) + Qr) + Qt, ?_⟩
  have hdiv : M * (x / M) + x % M = x := Nat.div_add_mod x M
  calc
    3 * x + 1 = 3 * (M * (x / M) + x % M) + 1 := by rw [hdiv]
    _ = 3 * ((D * Qm) * (x / M) + (D * Qr + R)) + 1 := by rw [← hM, ← hmod]
    _ = D * (3 * (Qm * (x / M) + Qr)) + (3 * R + 1) := by
          rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add]
          ac_rfl
    _ = D * (3 * (Qm * (x / M) + Qr) + Qt) := by rw [h3, ← Nat.mul_add]

/--
  Theorem W12.3j' (`invMod268435456Odd_mul_and_q6_nat_agreement`,
  `zero custom axioms`):
  Universal 5-Step Newton–Hensel `mod 2^28` Odd-Inverse Correctness & Exact `Q_(6)^+` / `Nat`
  Step Agreement for `T_diamond9` (`Branch P5.11`):
  1. For EVERY odd `d : Nat` (`d % 2 = 1`), `(d * invMod268435456Odd d) % 268435456 = 1`!
  2. For EVERY `x : Nat`, `cousinDiamond9StepQ6 (x, 1) = (cousinDiamond9Step x, 1)`!
-/
theorem invMod268435456Odd_mul_and_q6_nat_agreement :
    (∀ d : Nat, d % 2 = 1 -> (d * invMod268435456Odd d) % 268435456 = 1) ∧
    (∀ x : Nat, cousinDiamond9StepQ6 (x, 1) = (cousinDiamond9Step x, 1)) := by
  have hinv268m : ∀ d : Nat, d % 2 = 1 -> (d * invMod268435456Odd d) % 268435456 = 1 := by
    intro d hodd
    have h256 : (d * invMod256Odd d) % 256 = 1 := by
      let r := d % 256
      have hr_odd : r % 2 = 1 := by dsimp [r]; omega
      have h64_r : invMod64Odd d = invMod64Odd r := by
        unfold invMod64Odd; dsimp [r]
        have hm : (d % 256) % 64 = d % 64 := by omega
        rw [hm]
      have h256_r : invMod256Odd d = invMod256Odd r := by
        unfold invMod256Odd; rw [h64_r]; dsimp [r]; rw [Nat.mod_mod]
      have hr_m : (r * invMod256Odd r) % 256 = 1 :=
        invMod256Odd_fin_ok ⟨r, Nat.mod_lt d (by decide)⟩ hr_odd
      have hd_sp : d * invMod256Odd r = 256 * ((d / 256) * invMod256Odd r) + r * invMod256Odd r := by
        conv => lhs; lhs; rw [(Nat.div_add_mod d 256).symm]
        rw [Nat.add_mul, Nat.mul_assoc]
      rw [h256_r, hd_sp, Nat.add_comm (256 * ((d / 256) * invMod256Odd r)),
          Nat.add_mul_mod_self_left, hr_m]
    have h32k : (d * invMod32768Odd d) % 32768 = 1 :=
      hensel_inv_lift_nat 256 32768 2 65538 d (invMod256Odd d)
        (by decide) (by decide) (by decide) h256
    have h4m : (d * invMod4194304Odd d) % 4194304 = 1 :=
      hensel_inv_lift_nat 32768 4194304 256 8388610 d (invMod32768Odd d)
        (by decide) (by decide) (by decide) h32k
    have h33m : (d * invMod33554432Odd d) % 33554432 = 1 :=
      hensel_inv_lift_nat 4194304 33554432 524288 67108866 d (invMod4194304Odd d)
        (by decide) (by decide) (by decide) h4m
    exact hensel_inv_lift_nat 33554432 268435456 4194304 536870914 d (invMod33554432Odd d)
      (by decide) (by decide) (by decide) h33m
  refine ⟨hinv268m, ?_⟩
  have hi64 : invMod64Odd 1 = 1 := by decide
  have hi256 : invMod256Odd 1 = 1 := by decide
  have hi32k : invMod32768Odd 1 = 1 := by decide
  have hi4m : invMod4194304Odd 1 = 1 := by decide
  have hi33m : invMod33554432Odd 1 = 1 := by decide
  have hi268m : invMod268435456Odd 1 = 1 := by decide
  have hm3_1 : (1 : Nat) % 3 = 1 := by decide
  have hm9_1 : ((1 : Nat) % 9) ^ 5 % 9 = 1 := by decide
  have hm18_2 : (2 : Nat) % 18 = 2 := by decide
  intro x
  have hcc : ∀ c : Nat, c > 0 -> core3 (core2 (c + x)) = coprime23Core (c + x) :=
    fun c hc => core3_core2_eq_coprime23Core_aux (c + x) (c + x) (by omega) (Nat.le_refl _)
  have hcc_r : ∀ c : Nat, c > 0 -> core3 (core2 (x + c)) = coprime23Core (x + c) :=
    fun c hc => core3_core2_eq_coprime23Core_aux (x + c) (x + c) (by omega) (Nat.le_refl _)
  -- Step 1: `cousinDiamond3StepQ6 (x, 1) = (cousinDiamond3Step x, 1)`:
  have hd3 : cousinDiamond3StepQ6 (x, 1) = (cousinDiamond3Step x, 1) := by
    unfold cousinDiamond3StepQ6 cousinDiamond3Step isDiamond3Cone4
    simp only [hi64, hm3_1, hm18_2, Nat.mul_one,
               show (x % 64) % 2 = x % 2 by omega,
               show (x % 64) % 8 = x % 8 by omega,
               show (x % 64) % 16 = x % 16 by omega]
    by_cases hodd : x % 2 = 1
    · simp only [hodd, ite_true]
      by_cases hc : (x ≥ 169 ∧ x % 8 = 1 ∧ core2 (3 * x + 5) = 1) ∨
          (x > 1 ∧ x % 16 = 1 ∧ x % 3 ≠ 2 ∧ core3 (2 * x + 1) ≠ 1) ∨
          (x ≥ 73 ∧ x % 64 = 9 ∧ x % 3 ≠ 2 ∧ core3 (2 * x + 1) ≠ 1) ∨
          (x ≥ 17 ∧ core3 (x + 1) = 2)
      · simp only [hc, ite_true]
        have hdvd4 : 4 ∣ (3 * x + 1) := by
          rcases hc with ⟨_, h8, _⟩ | ⟨_, h16, _⟩ | ⟨_, h64, _⟩ | ⟨hx17, hc3_2⟩
          · exact ⟨(3 * x + 1) / 4, by omega⟩
          · exact ⟨(3 * x + 1) / 4, by omega⟩
          · exact ⟨(3 * x + 1) / 4, by omega⟩
          · rcases core3_decomp (x + 1) (by omega) with ⟨_, _, _, hm8, hmul⟩
            rw [hc3_2] at hmul
            have hx_m4 : (x + 1) % 4 = 2 := by
              rcases hm8 with hm1 | hm3 <;> omega
            exact ⟨(3 * x + 1) / 4, by omega⟩
        exact reduceRatPair_div_exact (3 * x + 1) 4 (by decide) hdvd4
      · simp only [hc, ite_false]
        exact reduceRatPair_div_exact (3 * x + 1) 2 (by decide) ⟨(3 * x + 1) / 2, by omega⟩
    · simp only [hodd, ite_false]
      by_cases h18 : x ≥ 20 ∧ x % 18 = 2
      · simp only [h18, and_self, ite_true]
        exact reduceRatPair_div_exact (x - 2) 9 (by decide) ⟨(x - 2) / 9, by omega⟩
      · simp only [h18, ite_false]
        have hev : x % 2 = 0 := by omega
        have hm6 : (x % 3 = 2) ↔ (x % 6 = 2) := by omega
        simp only [hm6]
        by_cases h6 : x > 2 ∧ x % 6 = 2
        · simp only [h6, and_self, ite_true]
          exact reduceRatPair_div_exact (x - 2) 3 (by decide) ⟨(x - 2) / 3, by omega⟩
        · simp only [h6, ite_false]
          by_cases h8 : x > 2 ∧ x % 8 = 6
          · simp only [h8, and_self, ite_true]
            exact reduceRatPair_div_exact (x - 2) 2 (by decide) ⟨(x - 2) / 2, by omega⟩
          · simp only [h8, ite_false]
            exact reduceRatPair_div_exact x 2 (by decide) ⟨x / 2, by omega⟩
  -- Step 2: Lift through Cones 5, 6, 7, 8, 9, 10:
  have hd4 : cousinDiamond4StepQ6 (x, 1) = (cousinDiamond4Step x, 1) := by
    unfold cousinDiamond4StepQ6 cousinDiamond4Step isDiamond4Cone5
    simp only [hi64, hm3_1, Nat.mul_one,
               show (x % 64) % 32 = x % 32 by omega, hcc_r 7 (by decide)]
    by_cases hc5 : x ≥ 89 ∧ x % 32 = 25 ∧ x % 3 = 2 ∧ coprime23Core (x + 7) = 1
    · simp only [hc5, and_self, ite_true]
      exact reduceRatPair_div_exact (3 * x + 1) 4 (by decide)
        (dvd_three_mul_add_one_of_mod x 32 4 8 6 1 1 (by decide) hc5.2.1 (by decide))
    · simp only [hc5, ite_false]; exact hd3
  have hd5 : cousinDiamond5StepQ6 (x, 1) = (cousinDiamond5Step x, 1) := by
    unfold cousinDiamond5StepQ6 cousinDiamond5Step isDiamond5Cone6
    simp only [hi256, hm9_1, Nat.mul_one, hcc_r 19 (by decide)]
    by_cases hc6 : x ≥ 2285 ∧ x % 256 = 237 ∧ x % 9 = 8 ∧ coprime23Core (x + 19) = 1
    · simp only [hc6, and_self, ite_true]
      exact reduceRatPair_div_exact (3 * x + 1) 8 (by decide)
        (dvd_three_mul_add_one_of_mod x 256 8 32 29 5 2 (by decide) hc6.2.1 (by decide))
    · simp only [hc6, ite_false]; exact hd4
  have hd6 : cousinDiamond6StepQ6 (x, 1) = (cousinDiamond6Step x, 1) := by
    unfold cousinDiamond6StepQ6 cousinDiamond6Step isDiamond6Cone7
    simp only [hi32k, hm9_1, Nat.mul_one, hcc_r 811 (by decide)]
    by_cases hc7 : x ≥ 294101 ∧ x % 32768 = 31957 ∧ x % 9 = 8 ∧ coprime23Core (x + 811) = 1
    · simp only [hc7, and_self, ite_true]
      exact reduceRatPair_div_exact (3 * x + 1) 128 (by decide)
        (dvd_three_mul_add_one_of_mod x 32768 128 256 249 85 2 (by decide) hc7.2.1 (by decide))
    · simp only [hc7, ite_false]; exact hd5
  have hd7 : cousinDiamond7StepQ6 (x, 1) = (cousinDiamond7Step x, 1) := by
    unfold cousinDiamond7StepQ6 cousinDiamond7Step isDiamond7Cone8
    simp only [hi4m, hm3_1, Nat.mul_one, hcc 34603 (by decide)]
    by_cases hc8 : x ≥ 12548309 ∧ x % 4194304 = 4159701 ∧ x % 3 = 2 ∧ coprime23Core (34603 + x) = 1
    · simp only [hc8, and_self, ite_true]
      exact reduceRatPair_div_exact (3 * x + 1) 128 (by decide)
        (dvd_three_mul_add_one_of_mod x 4194304 128 32768 32497 85 2 (by decide) hc8.2.1 (by decide))
    · simp only [hc8, ite_false]; exact hd6
  have hd8 : cousinDiamond8StepQ6 (x, 1) = (cousinDiamond8Step x, 1) := by
    unfold cousinDiamond8StepQ6 cousinDiamond8Step isDiamond8Cone9
    simp only [hi33m, hm3_1, Nat.mul_one, hcc 92275 (by decide)]
    by_cases hc9 : x ≥ 100571021 ∧ x % 33554432 = 33462157 ∧ x % 3 = 2 ∧ coprime23Core (92275 + x) = 1
    · simp only [hc9, and_self, ite_true]
      exact reduceRatPair_div_exact (3 * x + 1) 8 (by decide)
        (dvd_three_mul_add_one_of_mod x 33554432 8 4194304 4182769 5 2 (by decide) hc9.2.1 (by decide))
    · simp only [hc9, ite_false]; exact hd7
  unfold cousinDiamond9StepQ6 cousinDiamond9Step isDiamond9Cone10
  simp only [hi268m, hm3_1, Nat.mul_one, hcc 246067 (by decide)]
  by_cases hc10 : x ≥ 805060301 ∧ x % 268435456 = 268189389 ∧ x % 3 = 2 ∧ coprime23Core (246067 + x) = 1
  · simp only [hc10, and_self, ite_true]
    exact reduceRatPair_div_exact (3 * x + 1) 8 (by decide)
      (dvd_three_mul_add_one_of_mod x 268435456 8 33554432 33523673 5 2 (by decide) hc10.2.1 (by decide))
  · simp only [hc10, ite_false]; exact hd8

set_option maxRecDepth 16384 in
/--
  Theorem W12.3k (`cousin_diamond9_counter_model_separation`, `[]` axioms):
  `T_diamond9` rejects ALL three Counter-Models (`M1 = Q_(6)^+` 5-cycle `(1, 7) -> ... -> (1, 7)`
  plus non-integers `(805060301, 7)` and `(1610366669, 7)` bypassing Cone 10 by `W12.3j`,
  `M2 = Z^-` cycles `-1` and `-5 -> -7 -> -10 -> -5`, and `M3` supercritical `q = 7` 5-cycle at `5`),
  AND at the genuine `v_2(3x + 1) = 3` Cone-10 jumps `805060301 -> 301897613` (`18` steps to `1`) and
  `1610366669 -> 603887501 -> 226457813 -> 5307605 -> 124397 -> 46649`
  (`ZPOS_COUSIN_DIAMOND9_CONE10_1610366669_JUMP`, `17` steps to `1`) strictly increases
  `cousinDiamond2Phi` (`+1037.97x`) directly into `Cone 9 -> Cone 8 -> Cone 7 -> Cone 6 -> Cone 5`!
-/
theorem cousin_diamond9_counter_model_separation :
    cousinDiamond9StepInt (-1) = -1 ∧
    cousinDiamond9IterInt 3 (-5) = -5 ∧
    cousinDiamond9IterParam 7 5 5 = 5 ∧
    cousinDiamond9StepQ6 (1, 7) = (5, 7) ∧
    cousinDiamond9IterQ6 5 (1, 7) = (1, 7) ∧
    cousinDiamond9StepQ6 (805060301, 7) = cousinDiamond8StepQ6 (805060301, 7) ∧
    cousinDiamond9StepQ6 (1610366669, 7) = cousinDiamond8StepQ6 (1610366669, 7) ∧
    isDiamond9Cone10 805060301 ∧
    cousinDiamond9Step 805060301 = 301897613 ∧
    cousinDiamond9Iter 18 805060301 = 1 ∧
    isDiamond9Cone10 1610366669 ∧
    cousinDiamond9Step 1610366669 = 603887501 ∧
    cousinDiamond9StepInt 1610366669 = 603887501 ∧
    cousinDiamond9StepQ6 (1610366669, 1) = (603887501, 1) ∧
    isDiamond8Cone9 603887501 ∧
    isDiamond7Cone8 226457813 ∧
    isDiamond6Cone7 5307605 ∧
    isDiamond5Cone6 124397 ∧
    isDiamond4Cone5 46649 ∧
    cousinDiamond2Phi 1610366669 < cousinDiamond2Phi 603887501 ∧
    cousinDiamond9Iter 17 1610366669 = 1 := by
  decide

-- ============================================================================
-- SECTION 3: Front D (Branches P2.2 & P5.3) — Complete Mod-`486` (`2 * 3^5`)
--            Markov Bijection, Equal-Shift `(M, L, w, a)` Carry-Spread Ceiling,
--            & `11 + 16 = 27` Surviving `Mod 512` Window Occupancy
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Section 3A: Complete Mod-`486` (`2 * 3^5`) Markov Bijection & `243 mod 486` Lock (`P5.3`)
-- ----------------------------------------------------------------------------

def survivingMod486List : List Nat :=
  [1, 3, 7, 9, 13, 15, 19, 21, 25, 27, 31, 33, 37, 39, 43, 45, 49, 51,
   55, 57, 61, 63, 67, 69, 73, 75, 79, 81, 85, 87, 91, 93, 97, 99, 103, 105,
   109, 111, 115, 117, 121, 123, 127, 129, 133, 135, 139, 141, 145, 147, 151, 153, 157, 159,
   163, 165, 169, 171, 175, 177, 181, 183, 187, 189, 193, 195, 199, 201, 205, 207, 211, 213,
   217, 219, 223, 225, 229, 231, 235, 237, 241, 243, 247, 249, 253, 255, 259, 261, 265, 267,
   271, 273, 277, 279, 283, 285, 289, 291, 295, 297, 301, 303, 307, 309, 313, 315, 319, 321,
   325, 327, 331, 333, 337, 339, 343, 345, 349, 351, 355, 357, 361, 363, 367, 369, 373, 375,
   379, 381, 385, 387, 391, 393, 397, 399, 403, 405, 409, 411, 415, 417, 421, 423, 427, 429,
   433, 435, 439, 441, 445, 447, 451, 453, 457, 459, 463, 465, 469, 471, 475, 477, 481, 483]

def markovShiftTrue5Mod486Table (x : Fin 162) : Nat :=
  match x.val with
  | 0   => 1   | 1   => 393 | 2   => 331 | 3   => 45  | 4   => 301 | 5   => 381
  | 6   => 451 | 7   => 213 | 8   => 25  | 9   => 135 | 10  => 373 | 11  => 93
  | 12  => 91  | 13  => 357 | 14  => 367 | 15  => 63  | 16  => 121 | 17  => 129
  | 18  => 379 | 19  => 339 | 20  => 385 | 21  => 315 | 22  => 31  | 23  => 3
  | 24  => 343 | 25  => 159 | 26  => 79  | 27  => 405 | 28  => 103 | 29  => 201
  | 30  => 469 | 31  => 303 | 32  => 421 | 33  => 333 | 34  => 337 | 35  => 237
  | 36  => 271 | 37  => 285 | 38  => 439 | 39  => 99  | 40  => 247 | 41  => 111
  | 42  => 235 | 43  => 105 | 44  => 133 | 45  => 189 | 46  => 319 | 47  => 309
  | 48  => 361 | 49  => 249 | 50  => 475 | 51  => 117 | 52  => 67  | 53  => 345
  | 54  => 163 | 55  => 231 | 56  => 7   | 57  => 369 | 58  => 463 | 59  => 219
  | 60  => 127 | 61  => 51  | 62  => 187 | 63  => 459 | 64  => 49  | 65  => 417
  | 66  => 253 | 67  => 195 | 68  => 43  | 69  => 387 | 70  => 283 | 71  => 453
  | 72  => 55  | 73  => 177 | 74  => 61  | 75  => 153 | 76  => 193 | 77  => 327
  | 78  => 19  | 79  => 483 | 80  => 241 | 81  => 243 | 82  => 265 | 83  => 39
  | 84  => 145 | 85  => 141 | 86  => 97  | 87  => 171 | 88  => 13  | 89  => 75
  | 90  => 433 | 91  => 123 | 92  => 115 | 93  => 423 | 94  => 409 | 95  => 435
  | 96  => 397 | 97  => 429 | 98  => 295 | 99  => 27  | 100 => 481 | 101 => 147
  | 102 => 37  | 103 => 87  | 104 => 151 | 105 => 441 | 106 => 229 | 107 => 183
  | 108 => 325 | 109 => 69  | 110 => 169 | 111 => 207 | 112 => 139 | 113 => 57
  | 114 => 289 | 115 => 375 | 116 => 349 | 117 => 297 | 118 => 211 | 119 => 255
  | 120 => 415 | 121 => 33  | 122 => 205 | 123 => 225 | 124 => 445 | 125 => 291
  | 126 => 217 | 127 => 15  | 128 => 223 | 129 => 477 | 130 => 355 | 131 => 165
  | 132 => 181 | 133 => 321 | 134 => 403 | 135 => 81  | 136 => 427 | 137 => 363
  | 138 => 307 | 139 => 465 | 140 => 259 | 141 => 9   | 142 => 175 | 143 => 399
  | 144 => 109 | 145 => 447 | 146 => 277 | 147 => 261 | 148 => 85  | 149 => 273
  | 150 => 73  | 151 => 267 | 152 => 457 | 153 => 351 | 154 => 157 | 155 => 471
  | 156 => 199 | 157 => 411 | 158 => 313 | 159 => 279 | 160 => 391 | _   => 21

set_option exponentiation.threshold 512 in
set_option maxRecDepth 32768 in
private theorem markovShiftTrue5_eq_table :
    ∀ x : Fin 162, markovShiftTrue 5 x.val % 486 = markovShiftTrue5Mod486Table x := by
  decide

set_option maxRecDepth 32768 in
private theorem markovShiftTrue5_table_inj :
    ∀ x1 x2 : Fin 162, markovShiftTrue5Mod486Table x1 = markovShiftTrue5Mod486Table x2 -> x1 = x2 := by
  decide

set_option maxRecDepth 32768 in
private theorem markovShiftTrue5_table_mem :
    ∀ x : Fin 162, markovShiftTrue5Mod486Table x ∈ survivingMod486List := by
  decide

/--
  Theorem W12.4a (`markovShift_mod486_bijection_and_six_ones_243_lock`, `zero custom axioms`):
  Complete Mod-`486` (`2 * 3^5`) Markov Image Bijection, `324 / 486 = 2 / 3` Forbidden-Residue
  Confinement Matching the Exact Sharp `w(u) ≥ 6` Surviving Floor, & Universal `6`-Ones `243 mod 486`
  Suffix Lock (`Branch P5.3`):
  1. **Exact Mod-`486` Contraction & Bijection onto `162` Odd Non-`5 mod 6` Classes (`∀ w ≥ 5`)**:
     For EVERY weight `w ≥ 5` and `a < 2 * 3 ^ (w - 1)`,
       `markovShiftTrue w a % 486 = markovShiftTrue 5 (a % 162) % 486`,
     and `r ↦ markovShiftTrue 5 r.val % 486` is strictly injective on `Fin 162`, mapping `[0, 162)`
     bijectively onto the `162`-element `survivingMod486List`!
  2. **Universal `324 / 486 = 2 / 3` Confinement on `w(u) ≥ 6` (`∀ u`, `IsCoreParityWord u`, `parityWeight u ≥ 6`)**:
       `canonicalSuffixShift u 1 % 486 ∈ survivingMod486List`!
  3. **Exact Mod-`486` Suffix Locks Across Unrestricted Prefixes**:
     - For EVERY `pref : List Bool` with `parityWeight pref ≥ 1`:
       `canonicalSuffixShift (pref ++ [true, true, true, true, true]) 1 % 486 = 243 ∨
        canonicalSuffixShift (pref ++ [true, true, true, true, true]) 1 % 486 = 81`;
     - For EVERY completely unrestricted `pref : List Bool` (including `pref = []`):
       `canonicalSuffixShift (pref ++ [true, true, true, true, true, true]) 1 % 486 = 243` AND
       `canonicalSuffixShift (pref ++ [true, false, true, true, true, true, true]) 1 % 486 = 81`!
-/
theorem markovShift_mod486_bijection_and_six_ones_243_lock :
    ((∀ (w a : Nat), w ≥ 5 -> a < 2 * 3 ^ (w - 1) ->
        markovShiftTrue w a % 486 = markovShiftTrue 5 (a % 162) % 486) ∧
     survivingMod486List.length = 162 ∧
     (∀ x1 x2 : Fin 162,
        markovShiftTrue 5 x1.val % 486 = markovShiftTrue 5 x2.val % 486 -> x1 = x2) ∧
     (∀ x : Fin 162,
        markovShiftTrue 5 x.val % 486 ∈ survivingMod486List)) ∧
    (∀ u : List Bool, IsCoreParityWord u -> parityWeight u ≥ 6 ->
      canonicalSuffixShift u 1 % 486 ∈ survivingMod486List) ∧
    ((∀ pref : List Bool, parityWeight pref ≥ 1 ->
        canonicalSuffixShift (pref ++ [true, true, true, true, true]) 1 % 486 = 243 ∨
        canonicalSuffixShift (pref ++ [true, true, true, true, true]) 1 % 486 = 81) ∧
     (∀ pref : List Bool,
        canonicalSuffixShift (pref ++ [true, true, true, true, true, true]) 1 % 486 = 243 ∧
        canonicalSuffixShift (pref ++ [true, false, true, true, true, true, true]) 1 % 486 = 81)) := by
  have hcongr486 : ∀ (w a : Nat), w ≥ 5 -> a < 2 * 3 ^ (w - 1) ->
      markovShiftTrue w a % 486 = markovShiftTrue 5 (a % 162) % 486 := by
    intro w a hw5 ha_lt
    have hr_lt : a % 162 < 2 * 3 ^ (5 - 1) := Nat.mod_lt a (by decide)
    exact markovShiftTrue_contraction_mod_pow3 4 w 5 a (a % 162)
      (by omega) (by decide) ha_lt hr_lt (by simp)
  have hinj162 : ∀ x1 x2 : Fin 162,
      markovShiftTrue 5 x1.val % 486 = markovShiftTrue 5 x2.val % 486 -> x1 = x2 := by
    intro x1 x2 heq
    rw [markovShiftTrue5_eq_table x1, markovShiftTrue5_eq_table x2] at heq
    exact markovShiftTrue5_table_inj x1 x2 heq
  have hmem162 : ∀ x : Fin 162, markovShiftTrue 5 x.val % 486 ∈ survivingMod486List := by
    intro x
    rw [markovShiftTrue5_eq_table x]
    exact markovShiftTrue5_table_mem x
  refine ⟨⟨hcongr486, rfl, hinj162, hmem162⟩, ?_, ⟨?_, ?_⟩⟩
  · -- Core-word mod-`486` confinement on `w(u) ≥ 6`:
    intro u hu hw6
    rcases list_eq_append_true_of_reverse_head u hu.2 with ⟨v, rfl⟩
    have hw_v : parityWeight v ≥ 5 := by
      rw [parityWeight_append] at hw6
      have h1 : parityWeight [true] = 1 := rfl
      rw [h1] at hw6; omega
    have hrec : canonicalSuffixShift (v ++ [true]) 1 =
        markovShiftTrue (parityWeight v) (canonicalSuffixShift v 1) :=
      (canonicalSuffixShift_append_markov_recurrence.2.2 v (by omega)).2.2.1
    have ha_lt := (canonicalSuffixShift_spec_unique v 1 (by omega) (by decide)).1
    rw [hrec, hcongr486 (parityWeight v) (canonicalSuffixShift v 1) hw_v ha_lt]
    exact hmem162 ⟨canonicalSuffixShift v 1 % 162, Nat.mod_lt _ (by decide)⟩
  · -- `pref ++ [true, true, true, true, true]` (`parityWeight pref ≥ 1`) mod `486 ∈ {243, 81}`:
    intro pref hwp
    let t5 : List Bool := [true, true, true, true, true]
    have hap1 := iterMarkovShift_append_canonical t5 pref hwp
    have ha_lt := (canonicalSuffixShift_spec_unique pref 1 hwp (by decide)).1
    by_cases hpar : canonicalSuffixShift pref 1 % 2 = 0
    · right
      have hbase0 : canonicalSuffixShift [true, false] 1 % 2 = 0 := by decide
      have hap0 := iterMarkovShift_append_canonical t5 [true, false] (by decide)
      change canonicalSuffixShift ([true, false] ++ t5) 1 =
        iterMarkovShift t5 1 (canonicalSuffixShift [true, false] 1) at hap0
      have hc := iterMarkovShift_congr_mod_pow3 t5 0 (parityWeight pref) 1
        (canonicalSuffixShift pref 1) (canonicalSuffixShift [true, false] 1)
        hwp (by decide) ha_lt (by decide)
        (by simp only [Nat.pow_zero, Nat.mul_one]; exact hpar.trans hbase0.symm)
      rw [← hap1, ← hap0] at hc
      have hv : canonicalSuffixShift ([true, false] ++ t5) 1 % 486 = 81 := by decide
      exact hc.trans hv
    · left
      have hodd : canonicalSuffixShift pref 1 % 2 = 1 := by omega
      have hbase1 : canonicalSuffixShift [true] 1 % 2 = 1 := by decide
      have hap1' := iterMarkovShift_append_canonical t5 [true] (by decide)
      change canonicalSuffixShift ([true] ++ t5) 1 =
        iterMarkovShift t5 1 (canonicalSuffixShift [true] 1) at hap1'
      have hc := iterMarkovShift_congr_mod_pow3 t5 0 (parityWeight pref) 1
        (canonicalSuffixShift pref 1) (canonicalSuffixShift [true] 1)
        hwp (by decide) ha_lt (by decide)
        (by simp only [Nat.pow_zero, Nat.mul_one]; exact hodd.trans hbase1.symm)
      rw [← hap1, ← hap1'] at hc
      have hv : canonicalSuffixShift ([true] ++ t5) 1 % 486 = 243 := by decide
      exact hc.trans hv
  · -- Unrestricted `pref ++ replicate 6 true` and `pref ++ [true, false, true, true, true, true, true]`:
    intro pref
    have ha1 := first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.1 6 pref (by decide)
    have ha2 := canonicalSuffixShift_mod18_and_pow3_memory_annihilation.2.1 5 pref
      [true, false, true, true, true, true, true] (by decide)
    have hv2 : canonicalSuffixShift [true, false, true, true, true, true, true] 1 % 486 = 81 := by decide
    exact ⟨by simpa using ha1, by simpa using ha2.trans hv2⟩

-- ----------------------------------------------------------------------------
-- Section 3B: Equal-Shift `(M, L, w, a)` Carry-Difference Law, `< 2^(L - w)`
--             Spread Ceiling, Mod-`512` Fiber Uniqueness, & `369 vs 373` Split (`W12_H4`)
-- ----------------------------------------------------------------------------

/--
  Theorem W12.4b (`dyadic_window_equal_shift_carry_spread_and_subcrit_split`, `zero custom axioms`):
  Universal Equal-Shift `(M, L, w, a)` Carry-Difference Identity, `< 2^(L - w)` Leaf-Spread Ceiling,
  `L ≤ w + 1` / `L ≤ w + 9` Mod-`512` Fiber Uniqueness, & Sub-Critical Multi-Leaf Split (`Branches P2.2 & P5.3`,
  witness `ZPOS_DYADIC_SUBCRIT_CELL_MULTI_LEAF_369_VS_373`, `W12_H4`):
  1. **Exact Equal-Shift Carry-Difference Identity & `< 2^(L - w)` Spread Ceiling**:
     For ANY two core parity words `u1, u2` with `u1.length = u2.length`, `parityWeight u1 = parityWeight u2`,
     `canonicalSuffixShift u1 1 = canonicalSuffixShift u2 1`, and
     `exactBackwardQuotient 1 u1 0 ≤ exactBackwardQuotient 1 u2 0`:
     - `affineCarry u2 ≤ affineCarry u1`,
     - `3 ^ parityWeight u1 * (exactBackwardQuotient 1 u2 0 - exactBackwardQuotient 1 u1 0) =
          affineCarry u1 - affineCarry u2`, AND
     - `exactBackwardQuotient 1 u2 0 - exactBackwardQuotient 1 u1 0 < 2 ^ (u1.length - parityWeight u1)`!
  2. **Single-Zero Cell Uniqueness (`L ≤ w + 1`) & Mod-`512` Prefix Fiber Uniqueness (`L ≤ w + 9`)**:
     Under equal `(L, w, a)`:
     - Whenever `u1.length ≤ parityWeight u1 + 1`, `exactBackwardQuotient 1 u1 0 = exactBackwardQuotient 1 u2 0`
       (and if `IsFirstHitOnePair u1 0 ∧ IsFirstHitOnePair u2 0`, `u1 = u2`: at most `1` leaf!);
     - Whenever `u1.length ≤ parityWeight u1 + 9` AND `exactBackwardQuotient 1 u1 0 % 512 =
       exactBackwardQuotient 1 u2 0 % 512`, `exactBackwardQuotient 1 u1 0 = exactBackwardQuotient 1 u2 0`
       (at most `1` equal-shift leaf per surviving `mod 512` prefix whenever `L ≤ w + 9`!)!
  3. **Concrete Sub-Critical Multi-Leaf Split (`369 vs 373` at `(M, L, w) = (8, 12, 4)`, `12 ≤ 13`)**:
     Inside `[256, 512)` (`M = 8`), `u369` and `u373` both satisfy `IsFirstHitOnePair _ 0`, share
     `L = 12 ≤ 8 + 4 + 1`, `w = 4`, and uniquely pinned shift `a = 3`, yet yield distinct leaves
     `369 < 373` with `affineCarry u369 - affineCarry u373 = 324 = 3^4 * (373 - 369)` (`W12_H4`)!
-/
theorem dyadic_window_equal_shift_carry_spread_and_subcrit_split :
    (∀ (u1 u2 : List Bool),
      IsCoreParityWord u1 -> IsCoreParityWord u2 ->
      u1.length = u2.length ->
      parityWeight u1 = parityWeight u2 ->
      canonicalSuffixShift u1 1 = canonicalSuffixShift u2 1 ->
      exactBackwardQuotient 1 u1 0 ≤ exactBackwardQuotient 1 u2 0 ->
      affineCarry u2 ≤ affineCarry u1 ∧
      3 ^ parityWeight u1 * (exactBackwardQuotient 1 u2 0 - exactBackwardQuotient 1 u1 0) =
        affineCarry u1 - affineCarry u2 ∧
      exactBackwardQuotient 1 u2 0 - exactBackwardQuotient 1 u1 0 <
        2 ^ (u1.length - parityWeight u1)) ∧
    (∀ (u1 u2 : List Bool),
      IsCoreParityWord u1 -> IsCoreParityWord u2 ->
      u1.length = u2.length ->
      parityWeight u1 = parityWeight u2 ->
      canonicalSuffixShift u1 1 = canonicalSuffixShift u2 1 ->
      (u1.length ≤ parityWeight u1 + 1 ->
        exactBackwardQuotient 1 u1 0 = exactBackwardQuotient 1 u2 0 ∧
        (IsFirstHitOnePair u1 0 -> IsFirstHitOnePair u2 0 -> u1 = u2)) ∧
      (u1.length ≤ parityWeight u1 + 9 ->
        exactBackwardQuotient 1 u1 0 % 512 = exactBackwardQuotient 1 u2 0 % 512 ->
        exactBackwardQuotient 1 u1 0 = exactBackwardQuotient 1 u2 0 ∧
        (IsFirstHitOnePair u1 0 -> IsFirstHitOnePair u2 0 -> u1 = u2))) ∧
    (let u369 : List Bool :=
       [true, false, true, false, false, false, false, false, true, false, false, true]
     let u373 : List Bool :=
       [true, false, false, false, false, true, true, false, false, false, false, true]
     IsFirstHitOnePair u369 0 ∧ IsFirstHitOnePair u373 0 ∧
     u369.length = 12 ∧ u373.length = 12 ∧
     parityWeight u369 = 4 ∧ parityWeight u373 = 4 ∧
     12 ≤ 8 + 4 + 1 ∧
     canonicalSuffixShift u369 1 = 3 ∧ canonicalSuffixShift u373 1 = 3 ∧
     exactBackwardQuotient 1 u369 0 = 369 ∧ exactBackwardQuotient 1 u373 0 = 373 ∧
     2 ^ 8 ≤ 369 ∧ 369 < 2 ^ 9 ∧ 2 ^ 8 ≤ 373 ∧ 373 < 2 ^ 9 ∧
     affineCarry u369 - affineCarry u373 = 324 ∧
     3 ^ 4 * (373 - 369) = 324) := by
  have hmain : ∀ (u1 u2 : List Bool),
      IsCoreParityWord u1 -> IsCoreParityWord u2 ->
      u1.length = u2.length ->
      parityWeight u1 = parityWeight u2 ->
      canonicalSuffixShift u1 1 = canonicalSuffixShift u2 1 ->
      exactBackwardQuotient 1 u1 0 ≤ exactBackwardQuotient 1 u2 0 ->
      affineCarry u2 ≤ affineCarry u1 ∧
      3 ^ parityWeight u1 * (exactBackwardQuotient 1 u2 0 - exactBackwardQuotient 1 u1 0) =
        affineCarry u1 - affineCarry u2 ∧
      exactBackwardQuotient 1 u2 0 - exactBackwardQuotient 1 u1 0 <
        2 ^ (u1.length - parityWeight u1) := by
    intro u1 u2 hu1 hu2 hL hw ha hy_le
    rcases one_generator_pos_odd_and_reaches_one u1 0 hu1 with ⟨_, _, heq1, _⟩
    rcases one_generator_pos_odd_and_reaches_one u2 0 hu2 with ⟨_, _, heq2, _⟩
    have hK_eq : backwardOneTotalSteps u1 0 = backwardOneTotalSteps u2 0 := by
      unfold backwardOneTotalSteps; rw [hL, hw, ha]
    rw [← hK_eq, ← hw] at heq2
    let w := parityWeight u1
    let y1 := exactBackwardQuotient 1 u1 0
    let y2 := exactBackwardQuotient 1 u2 0
    change 2 ^ backwardOneTotalSteps u1 0 = 3 ^ w * y1 + affineCarry u1 at heq1
    change 2 ^ backwardOneTotalSteps u1 0 = 3 ^ w * y2 + affineCarry u2 at heq2
    change y1 ≤ y2 at hy_le
    have hsum_eq : 3 ^ w * y1 + affineCarry u1 = 3 ^ w * y2 + affineCarry u2 :=
      heq1.symm.trans heq2
    have hm_y : 3 ^ w * y1 ≤ 3 ^ w * y2 := Nat.mul_le_mul_left (3 ^ w) hy_le
    have hc_le : affineCarry u2 ≤ affineCarry u1 := by omega
    have hdiff : 3 ^ w * (y2 - y1) = affineCarry u1 - affineCarry u2 := by
      rw [Nat.mul_sub_left_distrib]; omega
    -- Use `affineCarry u1 + 2^L ≤ 3^w * 2^(L - w)` (`2^L ≥ 1`) -> `affineCarry u1 < 3^w * 2^(L - w)`:
    have hcar_lt : affineCarry u1 < 3 ^ w * 2 ^ (u1.length - w) := by
      have hex := affineCarry_add_pow2_le_pow3_mul_pow2 u1
      have hp2 := pow2_pos_nat u1.length
      dsimp [w] at hex ⊢; omega
    have h3w_lt : 3 ^ w * (y2 - y1) < 3 ^ w * 2 ^ (u1.length - w) := by omega
    have hspread : y2 - y1 < 2 ^ (u1.length - w) := by
      by_cases hlt : y2 - y1 < 2 ^ (u1.length - w)
      · exact hlt
      · exfalso
        have hge : 2 ^ (u1.length - w) ≤ y2 - y1 := by omega
        exact Nat.not_le_of_gt h3w_lt (Nat.mul_le_mul_left (3 ^ w) hge)
    exact ⟨hc_le, hdiff, hspread⟩
  refine ⟨hmain, ?_, ?_⟩
  · -- Part 2: `L ≤ w + 1` uniqueness and `L ≤ w + 9` mod-`512` fiber uniqueness:
    intro u1 u2 hu1 hu2 hL hw ha
    have hodd1 := (one_generator_pos_odd_and_reaches_one u1 0 hu1).2.1
    have hodd2 := (one_generator_pos_odd_and_reaches_one u2 0 hu2).2.1
    refine ⟨?_, ?_⟩
    · intro hLw1
      have heq_y : exactBackwardQuotient 1 u1 0 = exactBackwardQuotient 1 u2 0 := by
        have hp2 : 2 ^ (u1.length - parityWeight u1) ≤ 2 := by
          have hc : (2 : Nat) ^ 1 = 2 := by decide
          rw [← hc]; exact pow2_mono_nat (by omega)
        by_cases hle : exactBackwardQuotient 1 u1 0 ≤ exactBackwardQuotient 1 u2 0
        · have hsp := (hmain u1 u2 hu1 hu2 hL hw ha hle).2.2
          omega
        · have hsp := (hmain u2 u1 hu2 hu1 hL.symm hw.symm ha.symm (by omega)).2.2
          rw [← hL, ← hw] at hsp
          omega
      exact ⟨heq_y, fun hfh1 hfh2 =>
        (first_hit_one_pair_sound_and_injective u1 u2 0 0 hfh1 hfh2).2.2.2 heq_y |>.1⟩
    · intro hLw9 hmod512
      have heq_y : exactBackwardQuotient 1 u1 0 = exactBackwardQuotient 1 u2 0 := by
        by_cases hle : exactBackwardQuotient 1 u1 0 ≤ exactBackwardQuotient 1 u2 0
        · have hsp := (hmain u1 u2 hu1 hu2 hL hw ha hle).2.2
          have hp512 : 2 ^ (u1.length - parityWeight u1) ≤ 512 := by
            have hc : (2 : Nat) ^ 9 = 512 := by decide
            rw [← hc]; exact pow2_mono_nat (by omega)
          have hdm1 := (Nat.div_add_mod (exactBackwardQuotient 1 u1 0) 512).symm
          have hdm2 := (Nat.div_add_mod (exactBackwardQuotient 1 u2 0) 512).symm
          omega
        · have hsp := (hmain u2 u1 hu2 hu1 hL.symm hw.symm ha.symm (by omega)).2.2
          rw [← hL, ← hw] at hsp
          have hp512 : 2 ^ (u1.length - parityWeight u1) ≤ 512 := by
            have hc : (2 : Nat) ^ 9 = 512 := by decide
            rw [← hc]; exact pow2_mono_nat (by omega)
          have hdm1 := (Nat.div_add_mod (exactBackwardQuotient 1 u1 0) 512).symm
          have hdm2 := (Nat.div_add_mod (exactBackwardQuotient 1 u2 0) 512).symm
          omega
      exact ⟨heq_y, fun hfh1 hfh2 =>
        (first_hit_one_pair_sound_and_injective u1 u2 0 0 hfh1 hfh2).2.2.2 heq_y |>.1⟩
  · -- Part 3: Concrete sub-critical split `369 vs 373` at `(M, L, w) = (8, 12, 4)`:
    dsimp only
    let u369 : List Bool :=
      [true, false, true, false, false, false, false, false, true, false, false, true]
    let u373 : List Bool :=
      [true, false, false, false, false, true, true, false, false, false, false, true]
    have hfh369 : IsFirstHitOnePair u369 0 :=
      (first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.2 u369 ⟨rfl, rfl⟩).mpr (by decide)
    have hfh373 : IsFirstHitOnePair u373 0 :=
      (first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.2 u373 ⟨rfl, rfl⟩).mpr (by decide)
    exact ⟨hfh369, hfh373, rfl, rfl, by decide, by decide, by decide,
           by decide, by decide, by decide, by decide,
           by decide, by decide, by decide, by decide, by decide, by decide⟩

-- ----------------------------------------------------------------------------
-- Section 3C: `11 + 16 = 27` Surviving `Mod 512` Decomposition, Mod-`486`
--             Confinement, `3^(w - 6)` Fiber Equidistribution, & `27 * 2^(L_max - 9)`
--             Window Occupancy (`dyadicWindowSurvivingQ0Leaves L_max M`)
-- ----------------------------------------------------------------------------

def survivingMod512Residues27 : List Nat :=
  [27, 31, 47, 71, 91, 103, 111, 127, 155, 159, 167, 191, 231, 239,
   251, 255, 283, 303, 327, 347, 359, 415, 423, 447, 495, 507, 511]

private theorem survivingMod512Residues27_complete :
    survivingMod512Residues27.length = 27 ∧
    (∀ r : Fin 512, isSurvivingMod512Bool r.val = true -> r.val ∈ survivingMod512Residues27) := by
  refine ⟨rfl, ?_⟩
  have hgrid : ∀ (hi : Fin 8) (lo : Fin 64),
      isSurvivingMod512Bool (64 * hi.val + lo.val) = true ->
      (64 * hi.val + lo.val) ∈ survivingMod512Residues27 := by
    decide
  intro r hr
  have hdecomp : 64 * (r.val / 64) + r.val % 64 = r.val := Nat.div_add_mod r.val 64
  have hhi : r.val / 64 < 8 := by have := r.isLt; omega
  have hlo : r.val % 64 < 64 := Nat.mod_lt r.val (by decide)
  have hm := hgrid ⟨r.val / 64, hhi⟩ ⟨r.val % 64, hlo⟩ (by dsimp only; rwa [hdecomp])
  dsimp only at hm
  rwa [hdecomp] at hm

private theorem coreWords8_9_mod512_counts :
    ((allCoreWordsOfLen 8).filter (fun u =>
      decide (parityWeight u ≥ 6) && isSurvivingMod512Bool (coreWordMod512 u))).length = 11 ∧
    ((allCoreWordsOfLen 9).filter (fun u =>
      decide (parityWeight u ≥ 6) && isSurvivingMod512Bool (coreWordMod512 u))).length = 16 := by
  decide

private def eraseAllBoolWord (b : List Bool) : List (List Bool) -> List (List Bool)
  | [] => []
  | u :: us => if u = b then eraseAllBoolWord b us else u :: eraseAllBoolWord b us

private theorem mem_eraseAllBoolWord_iff (b : List Bool) :
    ∀ (ws : List (List Bool)) (v : List Bool),
      v ∈ eraseAllBoolWord b ws ↔ (v ∈ ws ∧ v ≠ b)
  | [], _ => by simp [eraseAllBoolWord]
  | u :: us, v => by
    simp only [eraseAllBoolWord]
    by_cases hub : u = b
    · simp only [hub, ite_true, mem_eraseAllBoolWord_iff b us v, List.mem_cons]
      constructor
      · rintro ⟨hm, hne⟩; exact ⟨Or.inr hm, hne⟩
      · rintro ⟨rfl | hm, hne⟩
        · exact False.elim (hne rfl)
        · exact ⟨hm, hne⟩
    · simp only [hub, ite_false, List.mem_cons, mem_eraseAllBoolWord_iff b us v]
      constructor
      · rintro (rfl | ⟨hm, hne⟩)
        · exact ⟨Or.inl rfl, hub⟩
        · exact ⟨Or.inr hm, hne⟩
      · rintro ⟨rfl | hm, hne⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hm, hne⟩

private theorem eraseAllBoolWord_of_not_mem (b : List Bool) :
    ∀ (ws : List (List Bool)), b ∉ ws -> eraseAllBoolWord b ws = ws
  | [], _ => rfl
  | u :: us, hnm => by
    have hub : u ≠ b := fun h => hnm (h ▸ List.Mem.head _)
    have hnm_us : b ∉ us := fun hm => hnm (List.mem_cons_of_mem _ hm)
    simp only [eraseAllBoolWord, hub, ite_false, eraseAllBoolWord_of_not_mem b us hnm_us]

private theorem nodup_eraseAllBoolWord_and_len (b : List Bool) :
    ∀ (ws : List (List Bool)),
      NoDupBoolWords ws ->
      NoDupBoolWords (eraseAllBoolWord b ws) ∧ ws.length ≤ (eraseAllBoolWord b ws).length + 1
  | [], _ => ⟨NoDupBoolWords.nil, by simp [eraseAllBoolWord]⟩
  | u :: us, NoDupBoolWords.cons _ _ hnu hnd => by
    by_cases hub : u = b
    · subst hub
      simp only [eraseAllBoolWord, ite_true, eraseAllBoolWord_of_not_mem u us hnu, List.length_cons]
      exact ⟨hnd, Nat.le_refl _⟩
    · rcases nodup_eraseAllBoolWord_and_len b us hnd with ⟨hnd_er, hlen_er⟩
      simp only [eraseAllBoolWord, hub, ite_false, List.length_cons]
      have hnu_er : u ∉ eraseAllBoolWord b us :=
        fun hm => hnu ((mem_eraseAllBoolWord_iff b us u).mp hm).1
      exact ⟨NoDupBoolWords.cons u _ hnu_er hnd_er, by omega⟩

private theorem noDupBoolWords_length_le_of_subset :
    ∀ (cands ws : List (List Bool)),
      NoDupBoolWords ws ->
      (∀ u ∈ ws, u ∈ cands) ->
      ws.length ≤ cands.length
  | [], [], _, _ => Nat.le_refl 0
  | [], u :: _, _, hsub => by cases hsub u (List.Mem.head _)
  | b :: bs, ws, hnd, hsub => by
    rcases nodup_eraseAllBoolWord_and_len b ws hnd with ⟨hnd', hlen'⟩
    have hsub' : ∀ u ∈ eraseAllBoolWord b ws, u ∈ bs := by
      intro u hu
      rcases (mem_eraseAllBoolWord_iff b ws u).mp hu with ⟨hu_ws, hne⟩
      rcases List.mem_cons.mp (hsub u hu_ws) with rfl | hbs
      · exact False.elim (hne rfl)
      · exact hbs
    have ih := noDupBoolWords_length_le_of_subset bs (eraseAllBoolWord b ws) hnd' hsub'
    simp only [List.length_cons]; omega

private theorem filter_length_le_of_imp {α : Type} (p q : α -> Bool) :
    ∀ (xs : List α),
      (∀ x ∈ xs, p x = true -> q x = true) ->
      (xs.filter p).length ≤ (xs.filter q).length
  | [], _ => Nat.le_refl 0
  | x :: xs, himp => by
    have ih := filter_length_le_of_imp p q xs (fun y hy => himp y (List.mem_cons_of_mem x hy))
    cases hpx : p x with
    | false =>
      cases hqx : q x <;> simp only [List.filter, hpx, hqx, List.length_cons] <;> omega
    | true =>
      have hqx := himp x (List.Mem.head _) hpx
      simp only [List.filter, hpx, hqx, List.length_cons]
      omega

private theorem filter_length_le_self {α : Type} (p : α -> Bool) :
    ∀ (xs : List α), (xs.filter p).length ≤ xs.length
  | [] => Nat.le_refl 0
  | x :: xs => by
    have ih := filter_length_le_self p xs
    cases hpx : p x <;> simp only [List.filter, hpx, List.length_cons] <;> omega

private def candSurvivingWords10PlusAux (m : Nat) : List Nat -> List (List Bool)
  | [] => []
  | r :: rs =>
    (allBoolWordsOfLen m).map (fun fb => parityOfIter 9 r ++ fb ++ [true]) ++
      candSurvivingWords10PlusAux m rs

private theorem candSurvivingWords10PlusAux_spec (m : Nat) :
    ∀ rs : List Nat,
      (candSurvivingWords10PlusAux m rs).length = rs.length * 2 ^ m ∧
      (∀ (r : Nat) (fb : List Bool),
        r ∈ rs -> fb ∈ allBoolWordsOfLen m ->
        (parityOfIter 9 r ++ fb ++ [true]) ∈ candSurvivingWords10PlusAux m rs)
  | [] => ⟨by simp [candSurvivingWords10PlusAux], fun _ _ hr _ => by cases hr⟩
  | r0 :: rs => by
    rcases candSurvivingWords10PlusAux_spec m rs with ⟨hlen_rs, hmem_rs⟩
    have hlen_b := (allBoolWordsOfLen_spec m).1
    refine ⟨?_, ?_⟩
    · simp only [candSurvivingWords10PlusAux, List.length_append, List.length_map,
                 List.length_cons, hlen_b, hlen_rs, Nat.add_mul, Nat.one_mul]
      omega
    · intro r fb hr hfb
      simp only [candSurvivingWords10PlusAux, List.mem_append]
      rcases List.mem_cons.mp hr with rfl | hrs
      · exact Or.inl (List.mem_map.mpr ⟨fb, hfb, rfl⟩)
      · exact Or.inr (hmem_rs r fb hrs hfb)

private theorem take_drop_split_eq_w12 :
    ∀ (k : Nat) (xs : List Bool), xs.take k ++ xs.drop k = xs
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, x :: xs => by
    simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append,
               take_drop_split_eq_w12 k xs]

private theorem take_len_of_ge_w12 :
    ∀ (k : Nat) (xs : List Bool), k ≤ xs.length -> (xs.take k).length = k
  | 0, _, _ => rfl
  | _ + 1, [], h => by simp at h
  | k + 1, _ :: xs, h => by
    simp only [List.length_cons] at h
    simp only [List.take_succ_cons, List.length_cons, take_len_of_ge_w12 k xs (by omega)]

private theorem drop_len_w12 :
    ∀ (k : Nat) (xs : List Bool), (xs.drop k).length = xs.length - k
  | 0, _ => by simp
  | _ + 1, [] => by simp
  | k + 1, _ :: xs => by
    simp only [List.drop_succ_cons, List.length_cons, drop_len_w12 k xs]; omega

private theorem firstHitSurvivingQ0LeavesUpToLen_bound_27 :
    ∀ k : Nat,
      (firstHitSurvivingQ0LeavesUpToLen (9 + k)).length ≤ 27 * 2 ^ k := by
  let pSurv : List Bool -> Bool := fun u =>
    isFirstHitOneQ0Bool u && isSurvivingMod373248Bool (exactBackwardQuotient 1 u 0)
  have hup7_empty : ((allCoreWordsUpToLen 7).filter pSurv).length = 0 := by
    have hall_false : ∀ u ∈ allCoreWordsUpToLen 7, pSurv u = false := by
      -- Prove `u ∈ allCoreWordsUpToLen L -> IsCoreParityWord u ∧ u.length ≤ L`:
      have hmem_up : ∀ (L : Nat) (u : List Bool),
          u ∈ allCoreWordsUpToLen L -> IsCoreParityWord u ∧ u.length ≤ L := by
        intro L; induction L with
        | zero => intro _ hm; simp [allCoreWordsUpToLen] at hm
        | succ L' ihL =>
          intro u hm
          rcases List.mem_append.mp hm with h1 | h2
          · rcases ihL u h1 with ⟨hc, hl⟩; exact ⟨hc, by omega⟩
          · rcases (allCoreWordsOfLen_spec (L' + 1)).2 u |>.mp h2 with ⟨hc, hl⟩
            exact ⟨hc, by omega⟩
      intro u hu
      rcases hmem_up 7 u hu with ⟨hcore, hle7⟩
      cases hp : pSurv u with
      | false => rfl
      | true =>
        rcases bool_and_split hp with ⟨_, hs_b⟩
        have hcls := isSurvivingMod373248Bool_imp_class _ hs_b
        exact False.elim (one_generator_length_le_seven_never_surviving_mod373248 u 0 hcore hle7 hcls)
    have hfilt_nil : ∀ ws : List (List Bool),
        (∀ u ∈ ws, pSurv u = false) -> (ws.filter pSurv).length = 0 := by
      intro ws; induction ws with
      | nil => intro _; rfl
      | cons w rest ih =>
        intro hf
        have hw := hf w (List.Mem.head _)
        simp only [List.filter, hw]
        exact ih (fun y hy => hf y (List.mem_cons_of_mem w hy))
    exact hfilt_nil _ hall_false
  have h8_le11 : ((allCoreWordsOfLen 8).filter pSurv).length ≤ 11 := by
    have hle := filter_length_le_of_imp pSurv
      (fun u => decide (parityWeight u ≥ 6) && isSurvivingMod512Bool (coreWordMod512 u))
      (allCoreWordsOfLen 8) ?_
    · rwa [coreWords8_9_mod512_counts.1] at hle
    · intro u hu hp
      rcases (allCoreWordsOfLen_spec 8).2 u |>.mp hu with ⟨hcore, _⟩
      rcases bool_and_split hp with ⟨_, hs_b⟩
      have hcls := isSurvivingMod373248Bool_imp_class _ hs_b
      have hw6 : parityWeight u ≥ 6 := by
        by_cases hw5 : parityWeight u ≤ 5
        · exact False.elim (one_generator_weight_le_five_never_surviving_mod373248 u 0 hcore hw5 hcls)
        · omega
      have hm512 := exactBackwardQuotient_mod512_eq_coreWordMod512 u 0 hcore hw6
      have hb512 := survivingMod512_imp_bool_true _ hcls.1
      rw [hm512] at hb512
      simp [hw6, hb512]
  have h9_le16 : ((allCoreWordsOfLen 9).filter pSurv).length ≤ 16 := by
    have hle := filter_length_le_of_imp pSurv
      (fun u => decide (parityWeight u ≥ 6) && isSurvivingMod512Bool (coreWordMod512 u))
      (allCoreWordsOfLen 9) ?_
    · rwa [coreWords8_9_mod512_counts.2] at hle
    · intro u hu hp
      rcases (allCoreWordsOfLen_spec 9).2 u |>.mp hu with ⟨hcore, _⟩
      rcases bool_and_split hp with ⟨_, hs_b⟩
      have hcls := isSurvivingMod373248Bool_imp_class _ hs_b
      have hw6 : parityWeight u ≥ 6 := by
        by_cases hw5 : parityWeight u ≤ 5
        · exact False.elim (one_generator_weight_le_five_never_surviving_mod373248 u 0 hcore hw5 hcls)
        · omega
      have hm512 := exactBackwardQuotient_mod512_eq_coreWordMod512 u 0 hcore hw6
      have hb512 := survivingMod512_imp_bool_true _ hcls.1
      rw [hm512] at hb512
      simp [hw6, hb512]
  have h10plus_le : ∀ m : Nat,
      ((allCoreWordsOfLen (m + 10)).filter pSurv).length ≤ 27 * 2 ^ m := by
    intro m
    have hnd := noDupBoolWords_filter pSurv (allCoreWordsOfLen (m + 10))
      (allCoreWordsOfLen_spec (m + 10)).1
    rcases candSurvivingWords10PlusAux_spec m survivingMod512Residues27 with ⟨hlen_c, hmem_c⟩
    rw [survivingMod512Residues27_complete.1] at hlen_c
    rw [← hlen_c]
    apply noDupBoolWords_length_le_of_subset _ _ hnd
    intro u hu
    rcases (mem_filter_iff_w8 pSurv u (allCoreWordsOfLen (m + 10))).mp hu with ⟨hu_len, hp⟩
    rcases (allCoreWordsOfLen_spec (m + 10)).2 u |>.mp hu_len with ⟨hcore, hlen_u⟩
    rcases bool_and_split hp with ⟨_, hs_b⟩
    have hcls := isSurvivingMod373248Bool_imp_class _ hs_b
    rcases list_eq_append_true_of_reverse_head u hcore.2 with ⟨pre, rfl⟩
    have hpre_len : pre.length = m + 9 := by
      rw [List.length_append, List.length_singleton] at hlen_u; omega
    let p9 := pre.take 9
    let fb := pre.drop 9
    have hp9_len : p9.length = 9 := take_len_of_ge_w12 9 pre (by omega)
    have hfb_len : fb.length = m := by dsimp [fb]; rw [drop_len_w12 9 pre]; omega
    have hpre_sp : p9 ++ fb = pre := take_drop_split_eq_w12 9 pre
    rw [← hpre_sp] at hcore hcls ⊢
    rcases surviving_mod512_nine_prefix_auto_weight_and_characterization.2
      p9 fb 0 hp9_len hcore hcls with ⟨r, hr_lt, hr_b, hp9_eq⟩
    have hr_mem : r ∈ survivingMod512Residues27 :=
      survivingMod512Residues27_complete.2 ⟨r, hr_lt⟩ hr_b
    have hfb_mem : fb ∈ allBoolWordsOfLen m := (allBoolWordsOfLen_spec m).2 fb hfb_len
    rw [hp9_eq]
    exact hmem_c r fb hr_mem hfb_mem
  intro k; induction k with
  | zero =>
    change (firstHitSurvivingQ0LeavesUpToLen 9).length ≤ 27 * 1
    unfold firstHitSurvivingQ0LeavesUpToLen
    rw [List.length_map]
    change (((allCoreWordsUpToLen 7 ++ allCoreWordsOfLen 8) ++ allCoreWordsOfLen 9).filter pSurv).length ≤ 27 * 1
    rw [List.filter_append, List.filter_append, List.length_append, List.length_append, hup7_empty]
    omega
  | succ k' ih =>
    rw [Nat.add_succ 9 k']
    unfold firstHitSurvivingQ0LeavesUpToLen at ih ⊢
    rw [List.length_map] at ih ⊢
    change ((allCoreWordsUpToLen (9 + k')).filter pSurv).length ≤ 27 * 2 ^ k' at ih
    change ((allCoreWordsUpToLen (9 + k') ++ allCoreWordsOfLen (9 + k' + 1)).filter pSurv).length ≤
      27 * 2 ^ (k' + 1)
    rw [List.filter_append, List.length_append, show 9 + k' + 1 = k' + 10 by omega,
        Nat.pow_succ 2 k']
    have hstep_k := h10plus_le k'
    omega

/--
  Theorem W12.4c (`dyadic_window_surviving_leaves_mod486_fiber_and_27_prefix_occupancy`,
  `zero custom axioms`):
  Complete Mod-`486` (`162/486`) Surviving-Window Confinement Matching the Exact Sharp `w(u) ≥ 6`
  Floor, `3^(w - 6)` (`j = 5`) Multi-Step Fiber Equidistribution, & `11 + 16 = 27` Prefix Summed
  Window Occupancy Ceiling (`Branches P2.2 & P5.3`, `W12_H4`):
  1. **Universal Surviving-Window Leaf Decomposition & Exact `162/486` Confinement (`∀ L_max, M`)**:
     Every `y ∈ dyadicWindowSurvivingQ0Leaves L_max M` is realized by a UNIQUE core parity word `u`
     (`IsFirstHitOnePair u 0 ∧ u.length ≤ L_max`) satisfying:
     - `IsSurvivingMod373248Class y ∧ y ≥ 27 ∧ 2 ^ M ≤ y ∧ y < 2 ^ (M + 1)`,
     - `parityWeight u ≥ 6 ∧ u.length ≥ 8`, AND
     - **`canonicalSuffixShift u 1 ≥ 3` AND `canonicalSuffixShift u 1 % 486 ∈ survivingMod486List`**
       (`162 / 486` surviving classes, matching the exact sharp `w(u) ≥ 6` floor across 100% of
       `dyadicWindowSurvivingQ0Leaves L_max M`!)!
  2. **Mod-`486` (`j = 5`) Multi-Step `3 ^ (w - 6)` Fiber Equidistribution (`∀ tail, ∀ w ≥ 6, ∀ r0 < 486`)**:
     Along any suffix `tail : List Bool` from weight `w ≥ 6`, `iterMarkovShift tail w` maps
     `{r0 + 486 * t | t < 3 ^ (w - 6)}` bijectively and uniformly onto
     `{base + (2 * 3 ^ (5 + parityWeight tail)) * q | q < 3 ^ (w - 6)}`!
  3. **Exact `11 + 16 = 27` Surviving `Mod 512` Prefix Decomposition & Summed Occupancy Ceiling**:
     - Length-`8` (`11` prefixes) and length-`9` (`16` prefixes) partition the `27` surviving `mod 512`
       fibers, bounding `(firstHitSurvivingQ0LeavesUpToLen L_max).length ≤ 27 * 2 ^ (L_max - 9)` across
       ALL `L_max ≥ 9`; AND
     - For EVERY `L_max ≥ 9` and `M ≥ 1`:
         `NoDupNat (dyadicWindowSurvivingQ0Leaves L_max M) ∧
          l2CollisionEnergy (dyadicWindowSurvivingQ0Leaves L_max M) =
            (dyadicWindowSurvivingQ0Leaves L_max M).length ∧
          (dyadicWindowSurvivingQ0Leaves L_max M).length ≤ 2 ^ (M - 1) ∧
          (dyadicWindowSurvivingQ0Leaves L_max M).length ≤ 27 * 2 ^ (L_max - 9)`!
-/
theorem dyadic_window_surviving_leaves_mod486_fiber_and_27_prefix_occupancy :
    -- Part 1: Universal surviving-leaf unique first-hit decomposition & mod-`486` confinement:
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
        canonicalSuffixShift u 1 % 486 ∈ survivingMod486List ∧
        (∀ u' : List Bool,
          IsFirstHitOnePair u' 0 -> exactBackwardQuotient 1 u' 0 = y -> u' = u)) ∧
    -- Part 2: Mod-`486` (`j = 5`) multi-step `3 ^ (w - 6)` fiber equidistribution:
    (∀ (tail : List Bool) (w r0 : Nat),
      w ≥ 6 -> r0 < 486 ->
      let Mk := 2 * 3 ^ (5 + parityWeight tail)
      let N := 3 ^ (w - 6)
      let base := iterMarkovShift tail w r0 % Mk
      (∀ t : Nat, t < N ->
        ∃ q : Nat, q < N ∧ iterMarkovShift tail w (r0 + 486 * t) = base + Mk * q) ∧
      (∀ q : Nat, q < N ->
        ∃ t : Nat, t < N ∧
          iterMarkovShift tail w (r0 + 486 * t) = base + Mk * q ∧
          ∀ t' : Nat, t' < N ->
            iterMarkovShift tail w (r0 + 486 * t') = base + Mk * q -> t' = t)) ∧
    -- Part 3: `11 + 16 = 27` prefix decomposition & summed window occupancy ceiling:
    (((allCoreWordsOfLen 8).filter (fun u =>
        decide (parityWeight u ≥ 6) && isSurvivingMod512Bool (coreWordMod512 u))).length = 11 ∧
     ((allCoreWordsOfLen 9).filter (fun u =>
        decide (parityWeight u ≥ 6) && isSurvivingMod512Bool (coreWordMod512 u))).length = 16 ∧
     (∀ L_max : Nat, L_max ≥ 9 ->
        (firstHitSurvivingQ0LeavesUpToLen L_max).length ≤ 27 * 2 ^ (L_max - 9)) ∧
     (∀ (L_max M : Nat), L_max ≥ 9 -> M ≥ 1 ->
        let win := dyadicWindowSurvivingQ0Leaves L_max M
        NoDupNat win ∧
        (∀ n : Nat, countEqInList n win ≤ 1) ∧
        l2CollisionEnergy win = win.length ∧
        win.length ≤ 2 ^ (M - 1) ∧
        win.length ≤ 27 * 2 ^ (L_max - 9))) := by
  refine ⟨?_, ?_, ⟨coreWords8_9_mod512_counts.1, coreWords8_9_mod512_counts.2, ?_, ?_⟩⟩
  · -- Part 1: Upgrade Wave 11's surviving-leaf decomposition with `markovShift_mod486`:
    intro L_max M y hy
    rcases dyadic_window_surviving_leaves_mod162_fiber_and_cell_occupancy.1 L_max M y hy with
      ⟨u, hfh, hlen_max, hy_eq, hcls, hy27, hlo, hhi, hw6, hlen8, hsh3, _, huniq⟩
    have hsh486 : canonicalSuffixShift u 1 % 486 ∈ survivingMod486List :=
      markovShift_mod486_bijection_and_six_ones_243_lock.2.1 u hfh.1 hw6
    exact ⟨u, hfh, hlen_max, hy_eq, hcls, hy27, hlo, hhi, hw6, hlen8, hsh3, hsh486, huniq⟩
  · -- Part 2: Mod-`486` (`j = 5`) `3 ^ (w - 6)` fiber equidistribution:
    intro tail w r0 hw6 hr0
    have hm486 : (2 : Nat) * 3 ^ 5 = 486 := by decide
    have hw_sub : w - 1 - 5 = w - 6 := by omega
    have heq := markovShift_mod18_bijection_and_multistep_fiber_equidistribution.2.2
      tail 5 w r0 (by omega) (by rw [hm486]; exact hr0)
    dsimp only at heq ⊢
    rwa [hm486, hw_sub] at heq
  · -- Part 3a: Global surviving leaves `≤ 27 * 2^(L_max - 9)` for all `L_max ≥ 9`:
    intro L_max hL9
    have hb := firstHitSurvivingQ0LeavesUpToLen_bound_27 (L_max - 9)
    rwa [show 9 + (L_max - 9) = L_max by omega] at hb
  · -- Part 3b: Coupled window `NoDupNat`, diagonal `L^2` energy, `≤ 2^(M - 1)`, & `≤ 27 * 2^(L_max - 9)`:
    intro L_max M hL9 hM1
    rcases dyadic_window_unique_shift_pinning_and_l2_energy.2.2.2 L_max M hM1 with
      ⟨hnd, hcnt, hl2, h2M⟩
    have hfilt_le : (dyadicWindowSurvivingQ0Leaves L_max M).length ≤
        (firstHitSurvivingQ0LeavesUpToLen L_max).length :=
      filter_length_le_self _ _
    have h27_le := firstHitSurvivingQ0LeavesUpToLen_bound_27 (L_max - 9)
    rw [show 9 + (L_max - 9) = L_max by omega] at h27_le
    exact ⟨hnd, hcnt, hl2, h2M, Nat.le_trans hfilt_le h27_le⟩

end CollatzFormal
