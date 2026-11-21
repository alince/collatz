/-
  CollatzFormal/Wave14WholeSpace.lean
  Wave 14 Whole-Space Mathematical & CS Proof Loop (Synthesis — Fronts C & D):
  1. Front C (Branches P1.2 & P5.13):
     - Universal Cube-Root-of-2 Non-Resonance (`A^3 ≠ 2 * B^3`), Overlapping Pincer Dichotomy
       (`(p_D * q_N)^3 < 2 * (q_D * p_N)^3 ∨ q_D * p_N < p_D * q_N`, covering `(0, 2^(1/3)) ∪ (1, ∞) = (0, ∞)`!),
       & Eventual (`∀ M_0 ≥ 3`) All-Bases Impossibility of Equal-Order Exponential Numerator/Denominator
       Preimage Ratios `w(n) = floorRatioExp p_N q_N (binBitLength n) / floorRatioExp p_D q_D (binBitLength n)`
       across 100% of `p_N ≥ q_N ≥ 1, p_D ≥ q_D ≥ 1`,
     - Choice-Free Joint `(binBitLength, binaryPopcount)` Preimage Barriers (`∀ M_0 ≥ 3`):
       Mersenne Equal-Popcount Lock (`3 * 2^r - 1` -> `(r+1, r+1, r+1)`), Single-Step Alternating
       Popcount Explosion (`4^s + 1 <- (2 * 4^s + 1) / 3` jumping `(2s + 1, 2) -> (2s, s + 1)` and
       refuting ALL arbitrary-slack `p_P > q_P ≥ 1` popcount-rewarding exponential weights), &
       Unrestricted-Numerator Sub-Cube-Root-of-2 Joint Denominator Impossibility (`(p_L * p_P)^3 < 2 * (q_L * q_P)^3`),
     - End-to-End Global Convergence, 9-Tier `ω^9` Cascade (`Cone 12 -> Cone 11 -> ... -> Cone 5 -> Φ_2`),
       Choice-Free `Q_(6)^+` Cone-12 Avoidance, 7-Step Newton–Hensel `mod 2^34` Odd-Inverse, & `[]`-Axiom
       `M1/M2/M3` Counter-Model Separation for the 11th Solvable `(3x + 1)`-Cousin `T_diamond11`
       (`51537857741 -> 19326696653` in `22` steps to `1`).
  2. Front D (Branches P2.2 & P5.3):
     - Complete Mod-`4374` (`2 * 3^7`) Markov Shift Bijection (`Fin 1458` ↔ `1458` surviving classes on `w ≥ 8`),
       Universal `8`-Ones `2187 mod 4374` Lock, Exact `22 + 5 = 27` Surviving Mod-`512` Prefix Dichotomy
       (`w(u) ≥ 8` across 100% of length `≥ 10` extensions of the `22` weight-`≥ 7` prefixes vs explicit
       `w(u) = 7` escape on the `5` weight-`6` prefixes), & `3^(w - 8)` (`j = 7`) Multi-Step Fiber Equidistribution,
     - Constructive Three-Zero-Run Family `uWinQuad M j1 j2` (`a = 3, w = 12, y % 512 = 511, y % 81 = 1`)
       Proving Unconditional Quadratic Surviving-Leaf Dyadic-Window Occupancy
       `(dyadicWindowSurvivingQ0Leaves L_max M).length ≥ R * R` (`≥ R * (R + 1) / 2`) across
       `∀ R ≥ 1, ∀ M ≥ R * 19131876, ∀ L_max ≥ M + 17`.

  Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

import CollatzFormal.Wave14WholeSpaceCore

namespace CollatzFormal

-- ============================================================================
-- SECTION 1: Front C Part 1 (Branch P1.2) — All-Bases Equal-Order Exponential
--            Ratio Pincer Impossibility & Choice-Free Joint `(binBitLength,
--            binaryPopcount)` Preimage Barriers (`W14_H3`)
-- ============================================================================

/-- Clamped positive integer floor of `(p / q)^L` (`max(1, ⌊(p / q)^L⌋)`). -/
def floorRatioExp (p q L : Nat) : Nat :=
  Nat.max 1 (p ^ L / q ^ L)

/-- Alias `binaryPopcount` for Wave 7's `binPopcount` (`s_2(n)`). -/
abbrev binaryPopcount : Nat -> Nat := binPopcount

private theorem mul_pow_w14s (a b : Nat) : ∀ n : Nat, (a * b) ^ n = a ^ n * b ^ n
  | 0 => rfl
  | n + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, mul_pow_w14s a b n]
    ac_rfl

private theorem pow_mono_base_w14s (a b : Nat) (hle : a ≤ b) : ∀ n : Nat, a ^ n ≤ b ^ n
  | 0 => Nat.le_refl 1
  | n + 1 => Nat.mul_le_mul (pow_mono_base_w14s a b hle n) hle

private theorem id_lt_pow2_w14s : ∀ n : Nat, n < 2 ^ n
  | 0 => by decide
  | n + 1 => by
    have ih := id_lt_pow2_w14s n
    have hp := pow2_pos_nat n
    rw [Nat.pow_succ]
    omega

private theorem ite_true_dec_w14s {p : Prop} [inst : Decidable p] {α : Type} {a b : α} (hp : p) :
    (if p then a else b) = a := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hnp => exact False.elim (hnp hp)

private theorem ite_false_dec_w14s {p : Prop} [inst : Decidable p] {α : Type} {a b : α} (hnp : ¬ p) :
    (if p then a else b) = b := by
  cases inst with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

private theorem bernoulli_nat_mul_w14s (A : Nat) :
    ∀ n : Nat, A ^ (n + 1) + n * A ^ n ≤ A * (A + 1) ^ n
  | 0 => by simp
  | n + 1 => by
    have ih := bernoulli_nat_mul_w14s A n
    have hm := Nat.mul_le_mul_right (A + 1) ih
    have hr : (A * (A + 1) ^ n) * (A + 1) = A * (A + 1) ^ (n + 1) := by
      rw [Nat.mul_assoc, ← Nat.pow_succ]
    rw [hr] at hm
    have hl : A ^ (n + 2) + (n + 1) * A ^ (n + 1) ≤ (A ^ (n + 1) + n * A ^ n) * (A + 1) := by
      have heq : (A ^ (n + 1) + n * A ^ n) * (A + 1) =
          (A ^ (n + 2) + (n + 1) * A ^ (n + 1)) + n * A ^ n := by
        rw [show n + 2 = (n + 1) + 1 from rfl, Nat.pow_succ A (n + 1),
            Nat.add_mul n 1 (A ^ (n + 1)), Nat.one_mul,
            Nat.pow_succ A n,
            Nat.add_mul (A ^ n * A) (n * A ^ n) (A + 1),
            Nat.mul_add (A ^ n * A) A 1, Nat.mul_one,
            Nat.mul_add (n * A ^ n) A 1, Nat.mul_one]
        ac_rfl
      rw [heq]
      exact Nat.le_add_right _ _
    exact Nat.le_trans hl hm

private theorem pow_gt_const_mul_pow_of_lt_w14s (A B K_0 : Nat) (hA : A ≥ 1) (hAB : A < B) :
    let k := K_0 * A
    K_0 * A ^ k < B ^ k := by
  dsimp only
  let k := K_0 * A
  have hbern := bernoulli_nat_mul_w14s A k
  have hb_mono : A * (A + 1) ^ k ≤ A * B ^ k :=
    Nat.mul_le_mul_left A (pow_mono_base_w14s (A + 1) B (by omega) k)
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

private theorem cube_ne_two_mul_cube_aux :
    ∀ (fuel A B : Nat), A ≥ 1 -> B ≥ 1 -> A ≤ fuel -> A ^ 3 ≠ 2 * B ^ 3
  | 0, A, _, hA, _, hle => by omega
  | fuel + 1, A, B, hA, hB, hle => by
    intro heq
    have hc_exp : ∀ x : Nat, x ^ 3 = x * (x * x) := fun x => by
      rw [show (3 : Nat) = 1 + 1 + 1 from rfl, Nat.pow_add, Nat.pow_add, Nat.pow_one]; ac_rfl
    if hA_ev : A % 2 = 0 then
      let A' := A / 2
      have hA_eq : A = 2 * A' := by dsimp [A']; omega
      have hA'1 : A' ≥ 1 := by dsimp [A']; omega
      have hA'lt : A' ≤ fuel := by dsimp [A']; omega
      have hA3 : A ^ 3 = 8 * A' ^ 3 := by
        rw [hA_eq, mul_pow_w14s 2 A' 3]
      rw [hA3] at heq
      have hB3 : B ^ 3 = 4 * A' ^ 3 := by omega
      if hB_ev : B % 2 = 0 then
        let B' := B / 2
        have hB_eq : B = 2 * B' := by dsimp [B']; omega
        have hB'1 : B' ≥ 1 := by dsimp [B']; omega
        have hB3' : B ^ 3 = 8 * B' ^ 3 := by
          rw [hB_eq, mul_pow_w14s 2 B' 3]
        rw [hB3'] at hB3
        have hsub : A' ^ 3 = 2 * B' ^ 3 := by omega
        exact cube_ne_two_mul_cube_aux fuel A' B' hA'1 hB'1 hA'lt hsub
      else
        have hB_odd : B % 2 = 1 := by omega
        have hB3_m2 : B ^ 3 % 2 = 1 := by
          rw [hc_exp B, Nat.mul_mod, Nat.mul_mod B B 2, hB_odd]
        rw [hB3] at hB3_m2
        omega
    else
      have hA_odd : A % 2 = 1 := by omega
      have hA3_m2 : A ^ 3 % 2 = 1 := by
        rw [hc_exp A, Nat.mul_mod, Nat.mul_mod A A 2, hA_odd]
      rw [heq] at hA3_m2
      omega

private theorem floorRatioExp_sandwich (p q L : Nat) (hq : q ≥ 1) (hq_le_p : q ≤ p) :
    floorRatioExp p q L ≥ 1 ∧
    p ^ L ≤ 2 * q ^ L * floorRatioExp p q L ∧
    q ^ L * floorRatioExp p q L ≤ p ^ L := by
  unfold floorRatioExp
  have hqL_pos : q ^ L ≥ 1 := nat_pow_pos_of_pos q hq L
  have hqpL : q ^ L ≤ p ^ L := pow_mono_base_w14s q p hq_le_p L
  have hdiv_ge1 : p ^ L / q ^ L ≥ 1 := by
    have hm : q ^ L * 1 ≤ p ^ L := by omega
    exact (Nat.le_div_iff_mul_le (by omega : 0 < q ^ L)).mpr (by rw [Nat.one_mul]; omega)
  have hmax_eq : Nat.max 1 (p ^ L / q ^ L) = p ^ L / q ^ L := Nat.max_eq_right hdiv_ge1
  rw [hmax_eq]
  refine ⟨hdiv_ge1, ?_, Nat.mul_div_le (p ^ L) (q ^ L)⟩
  have hdm := (Nat.div_add_mod (p ^ L) (q ^ L)).symm
  have hmod_lt : p ^ L % q ^ L < q ^ L := Nat.mod_lt (p ^ L) (by omega)
  have h2q : 2 * q ^ L * (p ^ L / q ^ L) =
      q ^ L * (p ^ L / q ^ L) + q ^ L * (p ^ L / q ^ L) := by
    rw [show (2 : Nat) = 1 + 1 from rfl, Nat.add_mul, Nat.one_mul, Nat.add_mul]
  have hq_ge : q ^ L * 1 ≤ q ^ L * (p ^ L / q ^ L) := Nat.mul_le_mul_left _ hdiv_ge1
  rw [Nat.mul_one] at hq_ge
  omega

private theorem cMod9_bounds_w14s (z : Nat) : 1 ≤ cMod9 z ∧ cMod9 z ≤ 4 := by
  unfold cMod9
  have hr : z % 9 < 9 := Nat.mod_lt z (by decide)
  rcases (by omega :
    z % 9 = 0 ∨ z % 9 = 1 ∨ z % 9 = 2 ∨ z % 9 = 3 ∨ z % 9 = 4 ∨
    z % 9 = 5 ∨ z % 9 = 6 ∨ z % 9 = 7 ∨ z % 9 = 8) with
    h | h | h | h | h | h | h | h | h <;> simp [h]

private theorem cubeRootTwoBranchNext_step_w14s
    (M_0 : Nat) (hM0 : M_0 ≥ 3)
    (wNum wDen : Nat -> Nat) (pTheta qTheta x : Nat)
    (hw : IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta)
    (hx_2M0 : x ≥ 2 * M_0) (hx3 : x % 3 ≠ 0) :
    let x' := cubeRootTwoBranchNext wNum wDen x
    x < x' ∧ x' % 3 ≠ 0 ∧ cMod9 x' * x' ≤ 8 * (cMod9 x * x) ∧
    2 * wNum x' * wDen x ≤ wNum x * wDen x' := by
  dsimp only
  have hq_pos : qTheta > 0 := Nat.lt_of_lt_of_le hw.1 hw.2.1
  have hpot := eventual_exp_bitlength_cube_root_two_impossibility.1.1 wNum wDen x (by omega) hx3
  let r := optShiftMod9 x
  have hr_bd : 1 ≤ r ∧ r ≤ 4 ∧ (2 ^ r * x) % 3 = 2 := by
    dsimp [r]; unfold optShiftMod9
    have hr9 : x % 9 < 9 := Nat.mod_lt x (by decide)
    rcases (by omega :
      x % 9 = 1 ∨ x % 9 = 2 ∨ x % 9 = 4 ∨ x % 9 = 5 ∨ x % 9 = 7 ∨ x % 9 = 8) with
      h | h | h | h | h | h <;> (simp only [h]; omega)
  let m := 2 ^ r * x
  let y0 := 2 * m
  let y1 := (2 * m - 1) / 3
  have hp_lo : 2 ≤ 2 ^ r := by simpa using pow2_mono_nat hr_bd.1
  have hm_ge2x : m ≥ 2 * x := Nat.mul_le_mul_right x hp_lo
  have hlt0 : x < y0 := by dsimp [y0]; omega
  have hlt1 : x < y1 := by dsimp [y1]; omega
  have hy0_3 : y0 % 3 ≠ 0 := by dsimp [y0]; have := hr_bd.2.2; omega
  have hy1_3 : y1 % 3 ≠ 0 := by
    dsimp [y1, m, r]; unfold optShiftMod9
    have hr9 : x % 9 < 9 := Nat.mod_lt x (by decide)
    rcases (by omega :
      x % 9 = 1 ∨ x % 9 = 2 ∨ x % 9 = 4 ∨ x % 9 = 5 ∨ x % 9 = 7 ∨ x % 9 = 8) with
      h | h | h | h | h | h
    · simp only [h]; rw [show 2 * (2 ^ 1 * x) = 4 * x by omega]; omega
    · simp only [h]; rw [show 2 * (2 ^ 2 * x) = 8 * x by omega]; omega
    · simp only [h]; rw [show 2 * (2 ^ 1 * x) = 4 * x by omega]; omega
    · simp only [h]; rw [show 2 * (2 ^ 2 * x) = 8 * x by omega]; omega
    · simp only [h]; rw [show 2 * (2 ^ 3 * x) = 16 * x by omega]; omega
    · simp only [h]; rw [show 2 * (2 ^ 4 * x) = 32 * x by omega]; omega
  have heven_step : ∀ z : Nat, z ≥ 2 * M_0 -> wNum (2 * z) * wDen z ≤ wNum z * wDen (2 * z) := by
    intro z hz
    if hz2 : z % 3 = 2 then
      let nOdd := (2 * z - 1) / 3
      have hdn_pos : wDen nOdd > 0 := (hw.2.2.1 nOdd (by dsimp only [nOdd]; omega)).2
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
    else
      exact nat_mul_le_cancel_left_w5 qTheta _ _ hq_pos
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
  have hpre := hw.2.2.2.2 m (by omega) hr_bd.2.2
  dsimp only at hpre
  have hbr : (wNum y0 * wDen y1 + wNum y1 * wDen y0) * wDen m ≤
      wNum m * (wDen y0 * wDen y1) :=
    nat_mul_le_cancel_left_w5 qTheta _ _ hq_pos
      (Nat.le_trans hpre (Nat.mul_le_mul_right _ hw.2.1))
  have hbm_pos : wDen m > 0 := (hw.2.2.1 m (by omega)).2
  have hb0_pos : wDen y0 > 0 := (hw.2.2.1 y0 (by omega)).2
  have hb1_pos : wDen y1 > 0 := (hw.2.2.1 y1 (by omega)).2
  refine ⟨?_, ?_, hpot, ?_⟩
  · unfold cubeRootTwoBranchNext; dsimp only
    if hc : 2 * wNum y0 * wDen m ≤ wNum m * wDen y0 then
      change x < (if 2 * wNum y0 * wDen m ≤ wNum m * wDen y0 then y0 else y1)
      rw [ite_true_dec_w14s hc]; exact hlt0
    else
      change x < (if 2 * wNum y0 * wDen m ≤ wNum m * wDen y0 then y0 else y1)
      rw [ite_false_dec_w14s hc]; exact hlt1
  · unfold cubeRootTwoBranchNext; dsimp only
    if hc : 2 * wNum y0 * wDen m ≤ wNum m * wDen y0 then
      change (if 2 * wNum y0 * wDen m ≤ wNum m * wDen y0 then y0 else y1) % 3 ≠ 0
      rw [ite_true_dec_w14s hc]; exact hy0_3
    else
      change (if 2 * wNum y0 * wDen m ≤ wNum m * wDen y0 then y0 else y1) % 3 ≠ 0
      rw [ite_false_dec_w14s hc]; exact hy1_3
  · unfold cubeRootTwoBranchNext; dsimp only
    change 2 * wNum (if 2 * wNum y0 * wDen m ≤ wNum m * wDen y0 then y0 else y1) * wDen x ≤
      wNum x * wDen (if 2 * wNum y0 * wDen m ≤ wNum m * wDen y0 then y0 else y1)
    if hc : 2 * wNum y0 * wDen m ≤ wNum m * wDen y0 then
      rw [ite_true_dec_w14s hc]
      exact rat_le_trans_pos_w5 _ _ (wNum m) (wDen m) _ _ hbm_pos hc hm_le_x
    else
      rw [ite_false_dec_w14s hc]
      have hc1 : 2 * wNum y1 * wDen m ≤ wNum m * wDen y1 := by
        if hc' : 2 * wNum y1 * wDen m ≤ wNum m * wDen y1 then
          exact hc'
        else
          exfalso
          have hm0 := Nat.mul_lt_mul_of_pos_right (by omega : wNum m * wDen y0 < 2 * wNum y0 * wDen m) hb1_pos
          have hm1 := Nat.mul_lt_mul_of_pos_right (by omega : wNum m * wDen y1 < 2 * wNum y1 * wDen m) hb0_pos
          have hl0 : (wNum m * wDen y0) * wDen y1 = wNum m * (wDen y0 * wDen y1) := by ac_rfl
          have hl1 : (wNum m * wDen y1) * wDen y0 = wNum m * (wDen y0 * wDen y1) := by ac_rfl
          have hr0 : (2 * wNum y0 * wDen m) * wDen y1 = 2 * ((wNum y0 * wDen y1) * wDen m) := by ac_rfl
          have hr1 : (2 * wNum y1 * wDen m) * wDen y0 = 2 * ((wNum y1 * wDen y0) * wDen m) := by ac_rfl
          rw [hl0, hr0] at hm0; rw [hl1, hr1] at hm1; rw [Nat.add_mul] at hbr
          omega
      exact rat_le_trans_pos_w5 _ _ (wNum m) (wDen m) _ _ hbm_pos hc1 hm_le_x

/--
  Theorem W14.3a (`eventual_equal_order_exp_ratio_all_bases_impossibility`,
  `zero custom axioms`):
  Universal Cube-Root-of-2 Non-Resonance (`A^3 ≠ 2 * B^3`), Overlapping Pincer Dichotomy
  (`(0, 2^(1/3)) ∪ (1, ∞) = (0, ∞)`), & Complete All-Bases Impossibility of Equal-Order
  Exponential Numerator/Denominator Preimage Ratios (`Branch P1.2`,
  witness `ZPOS_POPCOUNT_EXPLOSION_171_TO_257_AND_EQ_EXP`, `W14_H3`):
  1. **Universal Non-Resonance, Pincer Coverage, & `(3/2, 7/4)` `k = 1` Collapse**:
     - For ALL `A, B ≥ 1`, `A ^ 3 ≠ 2 * B ^ 3`!
     - For ALL `p_N, q_N, p_D, q_D ≥ 1`,
         `(p_D * q_N) ^ 3 < 2 * (q_D * p_N) ^ 3 ∨ q_D * p_N < p_D * q_N`!
     - Explicit `(3/2, 7/4)` collapse (`(7 * 2)^3 = 2744 < 3456 = 2 * (4 * 3)^3`):
       at `k = 1` from `x_0 = 5`, `x_1 = 13` violates `2 * w(13) ≤ w(5)`!
  2. **Sub-Critical Pincer Arm (`(p_D * q_N) ^ 3 < 2 * (q_D * p_N) ^ 3`, `∀ M_0 ≥ 3`)**:
     Refutes EVERY eventual preimage weight where `p_N ^ L ≤ C_0 * q_N ^ L * wNum n` and
     `q_D ^ L * wDen n ≤ C_den * p_D ^ L` (`L = binBitLength n`) via `cubeRootTwoBranchIter`!
  3. **Super-Unit Pincer Arm (`q_D * p_N < p_D * q_N`, `∀ M_0 ≥ 3`)**:
     Refutes EVERY eventual two-sided equal-order exponential ratio with `q_D * p_N < p_D * q_N`
     along reverse Syracuse chains `revSyracuseNode (2 * s)` (`2 * 9^(2s) - 1 -> 2^(4s+1) - 1`)!
  4. **Complete All-Bases Floor-Ratio Corollary (`∀ M_0 ≥ 3, ∀ p_N ≥ q_N ≥ 1, ∀ p_D ≥ q_D ≥ 1`)**:
     Refutes `w(n) = floorRatioExp p_N q_N (binBitLength n) / floorRatioExp p_D q_D (binBitLength n)`
     across **100% of all rational base pairs** `p_N ≥ q_N ≥ 1` and `p_D ≥ q_D ≥ 1`!
-/
theorem eventual_equal_order_exp_ratio_all_bases_impossibility :
    ((∀ A B : Nat, A ≥ 1 -> B ≥ 1 -> A ^ 3 ≠ 2 * B ^ 3) ∧
     (∀ p_N q_N p_D q_D : Nat,
        p_N ≥ 1 -> q_N ≥ 1 -> p_D ≥ 1 -> q_D ≥ 1 ->
        (p_D * q_N) ^ 3 < 2 * (q_D * p_N) ^ 3 ∨ q_D * p_N < p_D * q_N) ∧
     ((7 * 2) ^ 3 < 2 * (4 * 3) ^ 3 ∧
      let w32 : Nat -> Nat := fun n => floorRatioExp 3 2 (binBitLength n)
      let w74 : Nat -> Nat := fun n => floorRatioExp 7 4 (binBitLength n)
      let x1 := cubeRootTwoBranchIter w32 w74 1 5
      x1 = 13 ∧ 2 * w32 x1 * w74 5 > w32 5 * w74 x1)) ∧
    (∀ (M_0 : Nat), M_0 ≥ 3 ->
      ∀ (wNum wDen : Nat -> Nat) (C_0 C_den p_N q_N p_D q_D pTheta qTheta : Nat),
        C_0 ≥ 1 -> p_N ≥ 1 -> q_N ≥ 1 -> p_D ≥ 1 -> q_D ≥ 1 ->
        (p_D * q_N) ^ 3 < 2 * (q_D * p_N) ^ 3 ->
        (∀ n : Nat, n ≥ M_0 -> p_N ^ binBitLength n ≤ C_0 * q_N ^ binBitLength n * wNum n) ->
        (∀ n : Nat, n ≥ M_0 -> q_D ^ binBitLength n * wDen n ≤ C_den * p_D ^ binBitLength n) ->
        ¬ IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta) ∧
    (∀ (M_0 : Nat), M_0 ≥ 3 ->
      ∀ (wNum wDen : Nat -> Nat) (C_0 C_num C_1 C_den p_N q_N p_D q_D pTheta qTheta : Nat),
        C_0 ≥ 1 -> C_1 ≥ 1 -> p_N ≥ 1 -> q_N ≥ 1 -> p_D ≥ 1 -> q_D ≥ 1 ->
        q_D * p_N < p_D * q_N ->
        (∀ n : Nat, n ≥ M_0 ->
          p_N ^ binBitLength n ≤ C_0 * q_N ^ binBitLength n * wNum n ∧
          q_N ^ binBitLength n * wNum n ≤ C_num * p_N ^ binBitLength n) ->
        (∀ n : Nat, n ≥ M_0 ->
          p_D ^ binBitLength n ≤ C_1 * q_D ^ binBitLength n * wDen n ∧
          q_D ^ binBitLength n * wDen n ≤ C_den * p_D ^ binBitLength n) ->
        ¬ IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta) ∧
    (∀ (M_0 : Nat), M_0 ≥ 3 ->
      ∀ (p_N q_N p_D q_D pTheta qTheta : Nat),
        q_N ≥ 1 -> q_N ≤ p_N -> q_D ≥ 1 -> q_D ≤ p_D ->
        ¬ IsEventualPositiveRationalPreimageWeight M_0
            (fun n => floorRatioExp p_N q_N (binBitLength n))
            (fun n => floorRatioExp p_D q_D (binBitLength n))
            pTheta qTheta) := by
  have hpincer_cov : ∀ p_N q_N p_D q_D : Nat,
      p_N ≥ 1 -> q_N ≥ 1 -> p_D ≥ 1 -> q_D ≥ 1 ->
      (p_D * q_N) ^ 3 < 2 * (q_D * p_N) ^ 3 ∨ q_D * p_N < p_D * q_N := by
    intro p_N q_N p_D q_D hpN hqN hpD hqD
    if hle : p_D * q_N ≤ q_D * p_N then
      left
      have hm := pow_mono_base_w14s (p_D * q_N) (q_D * p_N) hle 3
      have hp_pos := nat_pow_pos_of_pos (q_D * p_N) (Nat.mul_le_mul hqD hpN) 3
      omega
    else
      right; omega
  have harm_sub : ∀ (M_0 : Nat), M_0 ≥ 3 ->
      ∀ (wNum wDen : Nat -> Nat) (C_0 C_den p_N q_N p_D q_D pTheta qTheta : Nat),
        C_0 ≥ 1 -> p_N ≥ 1 -> q_N ≥ 1 -> p_D ≥ 1 -> q_D ≥ 1 ->
        (p_D * q_N) ^ 3 < 2 * (q_D * p_N) ^ 3 ->
        (∀ n : Nat, n ≥ M_0 -> p_N ^ binBitLength n ≤ C_0 * q_N ^ binBitLength n * wNum n) ->
        (∀ n : Nat, n ≥ M_0 -> q_D ^ binBitLength n * wDen n ≤ C_den * p_D ^ binBitLength n) ->
        ¬ IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta := by
    intro M_0 hM0 wNum wDen C_0 C_den p_N q_N p_D q_D pTheta qTheta
      hC0 hpN hqN hpD hqD hcrit hnum_lo hden_hi hw
    let P_e := p_D * q_N
    let Q_e := q_D * p_N
    have hPe1 : P_e ≥ 1 := Nat.mul_le_mul hpD hqN
    have hQe1 : Q_e ≥ 1 := Nat.mul_le_mul hqD hpN
    let C_e := C_0 * C_den
    have hcross : ∀ n : Nat, n ≥ M_0 ->
        Q_e ^ binBitLength n * wDen n ≤ C_e * P_e ^ binBitLength n * wNum n := by
      intro n hn
      let L := binBitLength n
      have h1 := hnum_lo n hn
      have h2 := hden_hi n hn
      change p_N ^ L ≤ C_0 * q_N ^ L * wNum n at h1
      change q_D ^ L * wDen n ≤ C_den * p_D ^ L at h2
      dsimp [Q_e, P_e, C_e]
      rw [mul_pow_w14s q_D p_N L, mul_pow_w14s p_D q_N L]
      calc
        (q_D ^ L * p_N ^ L) * wDen n
            = p_N ^ L * (q_D ^ L * wDen n) := by ac_rfl
        _ ≤ (C_0 * q_N ^ L * wNum n) * (C_den * p_D ^ L) := Nat.mul_le_mul h1 h2
        _ = (C_0 * C_den) * (p_D ^ L * q_N ^ L) * wNum n := by ac_rfl
    let x0 := 6 * M_0 + 5
    have hx0_2M0 : x0 ≥ 2 * M_0 := by dsimp [x0]; omega
    have hx0_3 : x0 % 3 ≠ 0 := by dsimp [x0]; omega
    have hiter : ∀ (k z : Nat), z ≥ 2 * M_0 -> z % 3 ≠ 0 ->
        let zk := cubeRootTwoBranchIter wNum wDen k z
        zk ≥ z ∧ zk % 3 ≠ 0 ∧
        cMod9 zk * zk ≤ 8 ^ k * (cMod9 z * z) ∧
        2 ^ k * wNum zk * wDen z ≤ wNum z * wDen zk := by
      intro k; induction k with
      | zero => intro z _ hz3; simp [cubeRootTwoBranchIter, hz3]
      | succ k' ih =>
        intro z hz hz3
        rcases cubeRootTwoBranchNext_step_w14s M_0 hM0 wNum wDen pTheta qTheta z hw hz hz3 with
          ⟨hlt1, hz1_3, hpot1, hrat1⟩
        let z1 := cubeRootTwoBranchNext wNum wDen z
        rcases ih z1 (by dsimp [z1]; omega) hz1_3 with ⟨hge_k, hzk_3, hpot_k, hrat_k⟩
        let zk := cubeRootTwoBranchIter wNum wDen k' z1
        change zk ≥ z ∧ zk % 3 ≠ 0 ∧ cMod9 zk * zk ≤ 8 ^ (k' + 1) * (cMod9 z * z) ∧
          2 ^ (k' + 1) * wNum zk * wDen z ≤ wNum z * wDen zk
        have hpot_tot : cMod9 zk * zk ≤ 8 ^ (k' + 1) * (cMod9 z * z) := by
          calc
            cMod9 zk * zk ≤ 8 ^ k' * (cMod9 z1 * z1) := hpot_k
            _ ≤ 8 ^ k' * (8 * (cMod9 z * z)) := Nat.mul_le_mul_left _ hpot1
            _ = (8 ^ k' * 8) * (cMod9 z * z) := by ac_rfl
            _ = 8 ^ (k' + 1) * (cMod9 z * z) := by rw [Nat.pow_succ]
        have hdz1_pos : wDen z1 > 0 := (hw.2.2.1 z1 (by dsimp [z1]; omega)).2
        have hrat_tot : 2 ^ (k' + 1) * wNum zk * wDen z ≤ wNum z * wDen zk := by
          have hm : (2 ^ (k' + 1) * wNum zk * wDen z) * wDen z1 ≤ (wNum z * wDen zk) * wDen z1 := by
            calc
              (2 ^ (k' + 1) * wNum zk * wDen z) * wDen z1
                  = (2 * wDen z) * (2 ^ k' * wNum zk * wDen z1) := by rw [Nat.pow_succ]; ac_rfl
              _ ≤ (2 * wDen z) * (wNum z1 * wDen zk) := Nat.mul_le_mul_left _ hrat_k
              _ = wDen zk * (2 * wNum z1 * wDen z) := by ac_rfl
              _ ≤ wDen zk * (wNum z * wDen z1) := Nat.mul_le_mul_left _ hrat1
              _ = (wNum z * wDen zk) * wDen z1 := by ac_rfl
          exact nat_mul_le_cancel_right_w5 (wDen z1) _ _ hdz1_pos hm
        exact ⟨Nat.le_trans (Nat.le_of_lt hlt1) hge_k, hzk_3, hpot_tot, hrat_tot⟩
    have hstep_cancel : ∀ k : Nat,
        let xk := cubeRootTwoBranchIter wNum wDen k x0
        let Lk := binBitLength xk
        Lk ≤ 3 * k + (3 + x0) ∧
        2 ^ k * Q_e ^ Lk ≤ wNum x0 * C_e * P_e ^ Lk := by
      intro k; dsimp only
      rcases hiter k x0 hx0_2M0 hx0_3 with ⟨hxk_ge, _, hpot_k, hrat_k⟩
      let xk := cubeRootTwoBranchIter wNum wDen k x0
      let Lk := binBitLength xk
      have hxk_M0 : xk ≥ M_0 := by dsimp [xk]; omega
      have hbl_k : Lk ≤ 3 * k + (3 + x0) := by
        have hc1 : 1 * xk ≤ cMod9 xk * xk := Nat.mul_le_mul_right xk (cMod9_bounds_w14s xk).1
        rw [Nat.one_mul] at hc1
        have hc0 : cMod9 x0 * x0 < 2 ^ (2 + x0) := by
          have h1 : cMod9 x0 * x0 ≤ 4 * x0 := Nat.mul_le_mul_right x0 (cMod9_bounds_w14s x0).2
          have h2 : 4 * x0 < 4 * 2 ^ x0 := Nat.mul_lt_mul_of_pos_left (id_lt_pow2_w14s x0) (by decide)
          have h4p : 4 * 2 ^ x0 = 2 ^ (2 + x0) := by rw [Nat.pow_add 2 2 x0]
          rw [h4p] at h2
          exact Nat.lt_of_le_of_lt h1 h2
        have h8k : 8 ^ k = 2 ^ (3 * k) := by
          rw [show (8 : Nat) = 2 ^ 3 from rfl, pow_pow_eq_mul_w5 2 3 k]
        have hxk_lt : xk < 2 ^ (3 * k + (2 + x0)) := by
          have hm := Nat.mul_lt_mul_of_pos_left hc0 (pow2_pos_nat (3 * k))
          rw [← h8k] at hm
          have hlt := Nat.lt_of_le_of_lt (Nat.le_trans hc1 hpot_k) hm
          rwa [h8k, ← Nat.pow_add 2 (3 * k) (2 + x0)] at hlt
        have hle := binBitLength_mono xk (2 ^ ((3 * k + 1 + x0) + 1) - 1)
          (by rw [show (3 * k + 1 + x0) + 1 = 3 * k + (2 + x0) by omega]; omega)
        rw [(binBitLength_pow2_and_pred (3 * k + 1 + x0)).2] at hle
        dsimp [Lk]; omega
      have hwn_pos : wNum xk > 0 := (hw.2.2.1 xk hxk_M0).1
      have hwd0_pos : wDen x0 ≥ 1 := (hw.2.2.1 x0 (by omega)).2
      have hcr := hcross xk hxk_M0
      change Q_e ^ Lk * wDen xk ≤ C_e * P_e ^ Lk * wNum xk at hcr
      have hm_comb : (2 ^ k * Q_e ^ Lk * wDen x0) * wNum xk ≤
          (wNum x0 * C_e * P_e ^ Lk) * wNum xk := by
        calc
          (2 ^ k * Q_e ^ Lk * wDen x0) * wNum xk
              = Q_e ^ Lk * (2 ^ k * wNum xk * wDen x0) := by ac_rfl
          _ ≤ Q_e ^ Lk * (wNum x0 * wDen xk) := Nat.mul_le_mul_left _ hrat_k
          _ = wNum x0 * (Q_e ^ Lk * wDen xk) := by ac_rfl
          _ ≤ wNum x0 * (C_e * P_e ^ Lk * wNum xk) := Nat.mul_le_mul_left _ hcr
          _ = (wNum x0 * C_e * P_e ^ Lk) * wNum xk := by ac_rfl
      have hcanc := nat_mul_le_cancel_right_w5 (wNum xk) _ _ hwn_pos hm_comb
      have h1 : (2 ^ k * Q_e ^ Lk) * 1 ≤ (2 ^ k * Q_e ^ Lk) * wDen x0 :=
        Nat.mul_le_mul_left _ hwd0_pos
      rw [Nat.mul_one] at h1
      exact ⟨hbl_k, Nat.le_trans h1 hcanc⟩
    if hPQ_le : P_e ≤ Q_e then
      let k := wNum x0 * C_e + 1
      rcases hstep_cancel k with ⟨_, hineq⟩
      let Lk := binBitLength (cubeRootTwoBranchIter wNum wDen k x0)
      change 2 ^ k * Q_e ^ Lk ≤ wNum x0 * C_e * P_e ^ Lk at hineq
      have hp_le : P_e ^ Lk ≤ Q_e ^ Lk := pow_mono_base_w14s P_e Q_e hPQ_le Lk
      have h2 : 2 ^ k * Q_e ^ Lk ≤ (wNum x0 * C_e) * Q_e ^ Lk :=
        Nat.le_trans hineq (Nat.mul_le_mul_left _ hp_le)
      have h2k_le : 2 ^ k ≤ wNum x0 * C_e :=
        nat_mul_le_cancel_right_w5 (Q_e ^ Lk) _ _ (nat_pow_pos_of_pos Q_e hQe1 Lk) h2
      have hgt := id_lt_pow2_w14s k
      dsimp [k] at h2k_le hgt; omega
    else
      have hQP : Q_e ≤ P_e := by omega
      let E0 := 3 + x0
      let K_0 := wNum x0 * C_e * P_e ^ E0 + 1
      let k := K_0 * P_e ^ 3
      rcases hstep_cancel k with ⟨hLk_le, hineq⟩
      let Lk := binBitLength (cubeRootTwoBranchIter wNum wDen k x0)
      change Lk ≤ 3 * k + E0 at hLk_le
      change 2 ^ k * Q_e ^ Lk ≤ wNum x0 * C_e * P_e ^ Lk at hineq
      let D_ex := (3 * k + E0) - Lk
      have hsp : Lk + D_ex = 3 * k + E0 := by dsimp [D_ex]; omega
      have hQD_PD : Q_e ^ D_ex ≤ P_e ^ D_ex := pow_mono_base_w14s Q_e P_e hQP D_ex
      have hstep_up : 2 ^ k * Q_e ^ (3 * k + E0) ≤ (wNum x0 * C_e * P_e ^ E0) * (P_e ^ 3) ^ k := by
        calc
          2 ^ k * Q_e ^ (3 * k + E0)
              = (2 ^ k * Q_e ^ Lk) * Q_e ^ D_ex := by
                  rw [← hsp, Nat.pow_add Q_e Lk D_ex]; ac_rfl
          _ ≤ (wNum x0 * C_e * P_e ^ Lk) * P_e ^ D_ex := Nat.mul_le_mul hineq hQD_PD
          _ = wNum x0 * C_e * P_e ^ (3 * k + E0) := by
                rw [Nat.mul_assoc (wNum x0 * C_e), ← Nat.pow_add P_e Lk D_ex, hsp]
          _ = (wNum x0 * C_e * P_e ^ E0) * (P_e ^ 3) ^ k := by
                rw [Nat.pow_add P_e (3 * k) E0, ← pow_pow_eq_mul_w5 P_e 3 k]; ac_rfl
      have hlhs_rew : 2 ^ k * Q_e ^ (3 * k + E0) = Q_e ^ E0 * (2 * Q_e ^ 3) ^ k := by
        rw [Nat.pow_add Q_e (3 * k) E0, ← pow_pow_eq_mul_w5 Q_e 3 k,
            mul_pow_w14s 2 (Q_e ^ 3) k]
        ac_rfl
      rw [hlhs_rew] at hstep_up
      have hQeE0 : Q_e ^ E0 ≥ 1 := nat_pow_pos_of_pos Q_e hQe1 E0
      have h1 : 1 * (2 * Q_e ^ 3) ^ k ≤ Q_e ^ E0 * (2 * Q_e ^ 3) ^ k :=
        Nat.mul_le_mul_right _ hQeE0
      rw [Nat.one_mul] at h1
      have hle_pow : (2 * Q_e ^ 3) ^ k ≤ K_0 * (P_e ^ 3) ^ k := by
        have hle1 := Nat.le_trans h1 hstep_up
        have hK0 : wNum x0 * C_e * P_e ^ E0 ≤ K_0 := by dsimp [K_0]; omega
        exact Nat.le_trans hle1 (Nat.mul_le_mul_right _ hK0)
      have hgt_pow := pow_gt_const_mul_pow_of_lt_w14s (P_e ^ 3) (2 * Q_e ^ 3) K_0
        (nat_pow_pos_of_pos P_e hPe1 3) hcrit
      dsimp only [k] at hle_pow hgt_pow
      omega
  have harm_sup : ∀ (M_0 : Nat), M_0 ≥ 3 ->
      ∀ (wNum wDen : Nat -> Nat) (C_0 C_num C_1 C_den p_N q_N p_D q_D pTheta qTheta : Nat),
        C_0 ≥ 1 -> C_1 ≥ 1 -> p_N ≥ 1 -> q_N ≥ 1 -> p_D ≥ 1 -> q_D ≥ 1 ->
        q_D * p_N < p_D * q_N ->
        (∀ n : Nat, n ≥ M_0 ->
          p_N ^ binBitLength n ≤ C_0 * q_N ^ binBitLength n * wNum n ∧
          q_N ^ binBitLength n * wNum n ≤ C_num * p_N ^ binBitLength n) ->
        (∀ n : Nat, n ≥ M_0 ->
          p_D ^ binBitLength n ≤ C_1 * q_D ^ binBitLength n * wDen n ∧
          q_D ^ binBitLength n * wDen n ≤ C_den * p_D ^ binBitLength n) ->
        ¬ IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta := by
    intro M_0 hM0 wNum wDen C_0 C_num C_1 C_den p_N q_N p_D q_D pTheta qTheta
      hC0 hC1 hpN hqN hpD hqD hlt_AB hnum hden hw
    rcases eventual_poly_num_any_exp_base_bitlength_impossibility.1 with ⟨hchain, hbits⟩
    have hq_pos : qTheta > 0 := Nat.lt_of_lt_of_le hw.1 hw.2.1
    let A := q_D * p_N
    let B := p_D * q_N
    have hA1 : A ≥ 1 := Nat.mul_le_mul hqD hpN
    have hB1 : B ≥ 1 := Nat.mul_le_mul hpD hqN
    let C_tot := C_0 * C_1 * C_num * C_den + M_0 + 1
    let s := C_tot * A
    have hs1 : s ≥ 1 := by
      dsimp [s, C_tot]; simpa using Nat.mul_le_mul (by omega : 1 ≤ C_0 * C_1 * C_num * C_den + M_0 + 1) hA1
    let m := 2 * s
    have hnode_ge : ∀ t : Nat, t ≤ 2 * m -> revSyracuseNode m t ≥ M_0 := by
      intro t ht
      unfold revSyracuseNode
      have h1 : 2 ^ (t + 1) * 3 ^ (2 * m - t) ≥ 2 ^ (t + 1) * 2 ^ (2 * m - t) :=
        Nat.mul_le_mul_left _ (pow2_le_pow3 _)
      rw [← Nat.pow_add, show (t + 1) + (2 * m - t) = 2 * m + 1 by omega] at h1
      have h2 : 2 * m + 1 < 2 ^ (2 * m + 1) := id_lt_pow2_w14s (2 * m + 1)
      have hs_M0 : s ≥ M_0 := by
        have hm1 : C_tot * 1 ≤ C_tot * A := Nat.mul_le_mul_left C_tot hA1
        dsimp [s, C_tot] at hm1 ⊢; omega
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
        exact rat_le_trans_pos_w5 _ _ (wNum (revSyracuseNode m r')) (wDen (revSyracuseNode m r')) _ _
          ((hw.2.2.1 _ (hnode_ge r' (Nat.le_of_lt hr))).2) (hstep_rs r' hr) (ih (Nat.le_of_lt hr))
    let x0 := revSyracuseNode m 0
    let xe := revSyracuseNode m (2 * m)
    have hrat_end := htele (2 * m) (Nat.le_refl _)
    change wNum xe * wDen x0 ≤ wNum x0 * wDen xe at hrat_end
    rcases hbits s hs1 with ⟨hbl_end, hbl_lo0, _⟩
    have hxe_rew : revSyracuseNode (2 * s) (4 * s) = xe := by
      dsimp [xe, m]; rw [show 2 * (2 * s) = 4 * s by omega]
    rw [hxe_rew] at hbl_end
    let L0 := binBitLength x0
    let Le := binBitLength xe
    have hL_gap : Le + s ≤ L0 := by
      change Le = 4 * s + 1 at hbl_end
      change 6 * s + 2 ≤ L0 at hbl_lo0
      omega
    let D_L := L0 - Le
    have hDL_ge : s ≤ D_L := by dsimp [D_L]; omega
    have hL0_sp : Le + D_L = L0 := by dsimp [D_L]; omega
    have hn_e := (hnum xe (hnode_ge (2 * m) (Nat.le_refl _))).1
    have hn_0 := (hnum x0 (hnode_ge 0 (Nat.zero_le _))).2
    have hd_0 := (hden x0 (hnode_ge 0 (Nat.zero_le _))).1
    have hd_e := (hden xe (hnode_ge (2 * m) (Nat.le_refl _))).2
    change p_N ^ Le ≤ C_0 * q_N ^ Le * wNum xe at hn_e
    change q_N ^ L0 * wNum x0 ≤ C_num * p_N ^ L0 at hn_0
    change p_D ^ L0 ≤ C_1 * q_D ^ L0 * wDen x0 at hd_0
    change q_D ^ Le * wDen xe ≤ C_den * p_D ^ Le at hd_e
    have hcomb : (A ^ Le * B ^ Le) * B ^ D_L ≤
        (A ^ Le * B ^ Le) * ((C_0 * C_1 * C_num * C_den) * A ^ D_L) := by
      have hl : (A ^ Le * B ^ Le) * B ^ D_L =
          (p_N ^ Le * p_D ^ L0) * (q_N ^ L0 * q_D ^ Le) := by
        rw [Nat.mul_assoc (A ^ Le), ← Nat.pow_add B Le D_L, hL0_sp]
        dsimp [A, B]
        rw [mul_pow_w14s q_D p_N Le, mul_pow_w14s p_D q_N L0]
        ac_rfl
      have hr : (A ^ Le * B ^ Le) * ((C_0 * C_1 * C_num * C_den) * A ^ D_L) =
          (C_0 * q_N ^ Le) * (C_1 * q_D ^ L0) * (C_num * p_N ^ L0) * (C_den * p_D ^ Le) := by
        have h1 : (A ^ Le * B ^ Le) * ((C_0 * C_1 * C_num * C_den) * A ^ D_L) =
            (C_0 * C_1 * C_num * C_den) * ((A ^ Le * A ^ D_L) * B ^ Le) := by ac_rfl
        rw [h1, ← Nat.pow_add A Le D_L, hL0_sp]
        dsimp [A, B]
        rw [mul_pow_w14s q_D p_N L0, mul_pow_w14s p_D q_N Le]
        ac_rfl
      rw [hl, hr]
      calc
        (p_N ^ Le * p_D ^ L0) * (q_N ^ L0 * q_D ^ Le)
            ≤ ((C_0 * q_N ^ Le * wNum xe) * (C_1 * q_D ^ L0 * wDen x0)) * (q_N ^ L0 * q_D ^ Le) :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul hn_e hd_0)
        _ = (C_0 * q_N ^ Le) * (C_1 * q_D ^ L0) * ((wNum xe * wDen x0) * (q_N ^ L0 * q_D ^ Le)) := by ac_rfl
        _ ≤ (C_0 * q_N ^ Le) * (C_1 * q_D ^ L0) * ((wNum x0 * wDen xe) * (q_N ^ L0 * q_D ^ Le)) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hrat_end)
        _ = (C_0 * q_N ^ Le) * (C_1 * q_D ^ L0) * ((q_N ^ L0 * wNum x0) * (q_D ^ Le * wDen xe)) := by ac_rfl
        _ ≤ (C_0 * q_N ^ Le) * (C_1 * q_D ^ L0) * ((C_num * p_N ^ L0) * (C_den * p_D ^ Le)) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul hn_0 hd_e)
        _ = (C_0 * q_N ^ Le) * (C_1 * q_D ^ L0) * (C_num * p_N ^ L0) * (C_den * p_D ^ Le) := by ac_rfl
    have hAB_pos : A ^ Le * B ^ Le > 0 := by
      have h1 := nat_pow_pos_of_pos A hA1 Le
      have h2 := nat_pow_pos_of_pos B hB1 Le
      have hm := Nat.mul_le_mul h1 h2; omega
    have hDL_ineq : B ^ D_L ≤ C_tot * A ^ D_L := by
      have hc := nat_mul_le_cancel_left_w5 _ _ _ hAB_pos hcomb
      exact Nat.le_trans hc (Nat.mul_le_mul_right _ (by dsimp [C_tot]; omega))
    let E_ex := D_L - s
    have hs_sp : s + E_ex = D_L := by dsimp [E_ex]; omega
    have hs_ineq : B ^ s ≤ C_tot * A ^ s := by
      have hAE_BE : A ^ E_ex ≤ B ^ E_ex := pow_mono_base_w14s A B (Nat.le_of_lt hlt_AB) E_ex
      have hm1 : A ^ E_ex * B ^ s ≤ A ^ E_ex * (C_tot * A ^ s) := by
        calc
          A ^ E_ex * B ^ s ≤ B ^ E_ex * B ^ s := Nat.mul_le_mul_right _ hAE_BE
          _ = B ^ D_L := by rw [← hs_sp, Nat.pow_add B s E_ex, Nat.mul_comm]
          _ ≤ C_tot * A ^ D_L := hDL_ineq
          _ = A ^ E_ex * (C_tot * A ^ s) := by
                rw [← hs_sp, Nat.pow_add A s E_ex]; ac_rfl
      exact nat_mul_le_cancel_left_w5 (A ^ E_ex) _ _ (nat_pow_pos_of_pos A hA1 E_ex) hm1
    have hgt := pow_gt_const_mul_pow_of_lt_w14s A B C_tot hA1 hlt_AB
    dsimp only [s] at hs_ineq hgt
    omega
  refine ⟨⟨fun A B hA hB => cube_ne_two_mul_cube_aux A A B hA hB (Nat.le_refl A),
           hpincer_cov, by decide⟩,
          harm_sub, harm_sup, ?_⟩
  intro M_0 hM0 p_N q_N p_D q_D pTheta qTheta hqN hqNp hqD hqDp
  have hpN : p_N ≥ 1 := Nat.le_trans hqN hqNp
  have hpD : p_D ≥ 1 := Nat.le_trans hqD hqDp
  rcases hpincer_cov p_N q_N p_D q_D hpN hqN hpD hqD with hsub | hsup
  · exact harm_sub M_0 hM0 _ _ 2 1 p_N q_N p_D q_D pTheta qTheta
      (by decide) hpN hqN hpD hqD hsub
      (fun n _ => (floorRatioExp_sandwich p_N q_N (binBitLength n) hqN hqNp).2.1)
      (fun n _ => by
        simpa using (floorRatioExp_sandwich p_D q_D (binBitLength n) hqD hqDp).2.2)
  · exact harm_sup M_0 hM0 _ _ 2 1 2 1 p_N q_N p_D q_D pTheta qTheta
      (by decide) (by decide) hpN hqN hpD hqD hsup
      (fun n _ => ⟨(floorRatioExp_sandwich p_N q_N (binBitLength n) hqN hqNp).2.1,
        by simpa using (floorRatioExp_sandwich p_N q_N (binBitLength n) hqN hqNp).2.2⟩)
      (fun n _ => ⟨(floorRatioExp_sandwich p_D q_D (binBitLength n) hqD hqDp).2.1,
        by simpa using (floorRatioExp_sandwich p_D q_D (binBitLength n) hqD hqDp).2.2⟩)

-- ----------------------------------------------------------------------------
-- Section 1B: Choice-Free Joint `(binBitLength, binaryPopcount)` Preimage Barriers
-- ----------------------------------------------------------------------------

private theorem binPopcount_double : ∀ n : Nat,
    binPopcount (2 * n) = binPopcount n
  | 0 => rfl
  | n + 1 => by
    rw [binPopcount_step_pos (2 * (n + 1)) (by omega), Nat.mul_mod_right, Nat.zero_add,
        Nat.mul_div_right (n + 1) (by decide : 0 < 2)]

private theorem binPopcount_double_add_one (n : Nat) :
    binPopcount (2 * n + 1) = binPopcount n + 1 := by
  rw [binPopcount_step_pos (2 * n + 1) (by omega)]
  have hm : (2 * n + 1) % 2 = 1 := by omega
  have hd : (2 * n + 1) / 2 = n := by omega
  rw [hm, hd]; omega

private theorem binPopcount_pow2 :
    ∀ k : Nat, binPopcount (2 ^ k) = 1
  | 0 => rfl
  | k + 1 => by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, binPopcount_double (2 ^ k)]
    exact binPopcount_pow2 k

private theorem binPopcount_mersenne :
    ∀ k : Nat, binPopcount (2 ^ k - 1) = k
  | 0 => rfl
  | k + 1 => by
    have hp := pow2_pos_nat k
    have heq : 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 := by
      rw [Nat.pow_succ]; omega
    rw [heq, binPopcount_double_add_one, binPopcount_mersenne k]

private theorem binPopcount_three_mul_pow2_sub1 :
    ∀ r : Nat, r ≥ 1 -> binPopcount (3 * 2 ^ r - 1) = r + 1
  | 0, hr => by omega
  | 1, _ => by decide
  | r + 2, _ => by
    have hp := pow2_pos_nat (r + 1)
    have heq : 3 * 2 ^ (r + 2) - 1 = 2 * (3 * 2 ^ (r + 1) - 1) + 1 := by
      rw [Nat.pow_succ 2 (r + 1)]; omega
    rw [heq, binPopcount_double_add_one,
        binPopcount_three_mul_pow2_sub1 (r + 1) (by omega)]

private theorem binPopcount_alt_geom :
    ∀ s : Nat, binPopcount ((4 ^ s - 1) / 3) = s
  | 0 => rfl
  | s + 1 => by
    have hm3 : ∀ k : Nat, 4 ^ k % 3 = 1 := by
      intro k; induction k with
      | zero => rfl
      | succ k' ih => rw [Nat.pow_succ, Nat.mul_mod, ih]
    have hp_pos : 4 ^ s ≥ 1 := nat_pow_pos_of_pos 4 (by decide) s
    have h4_m3 := hm3 s
    have hrec : (4 ^ (s + 1) - 1) / 3 = 2 * (2 * ((4 ^ s - 1) / 3)) + 1 := by
      rw [Nat.pow_succ 4 s]; omega
    rw [hrec, binPopcount_double_add_one, binPopcount_double, binPopcount_alt_geom s]

private theorem binPopcount_le_binBitLength_aux :
    ∀ (fuel n : Nat), n ≤ fuel ->
      binPopcount n ≤ binBitLength n ∧ (n ≥ 1 -> 1 ≤ binPopcount n)
  | 0, 0, _ => ⟨Nat.le_refl 0, fun h => by omega⟩
  | 0, _ + 1, hle => by omega
  | _ + 1, 0, _ => ⟨Nat.le_refl 0, fun h => by omega⟩
  | fuel + 1, n + 1, hle => by
    rcases binPopcount_le_binBitLength_aux fuel ((n + 1) / 2) (by omega) with ⟨ih_le, ih_pos⟩
    rw [binPopcount_step_pos (n + 1) (by omega), binBitLength_step_pos (n + 1) (by omega)]
    have hm2 : (n + 1) % 2 ≤ 1 := by omega
    refine ⟨by omega, fun _ => ?_⟩
    cases hdiv : (n + 1) / 2 with
    | zero => omega
    | succ _ => have hp1 := ih_pos (by omega); rw [hdiv] at hp1; omega

/--
  Theorem W14.3b (`eventual_joint_bitlength_popcount_exp_impossibility`,
  choice-free `zero custom axioms`):
  Choice-Free Joint `(binBitLength, binaryPopcount)` Preimage Barriers (`Branch P1.2`,
  witness `ZPOS_POPCOUNT_EXPLOSION_171_TO_257_AND_EQ_EXP`, `W14_H3`):
  1. **Mersenne Equal-Popcount Lock & Alternating-Bit Popcount Explosion**:
     - For EVERY `r ≥ 2`, `m_r := 3 * 2 ^ r - 1` satisfies `m_r % 3 = 2`,
       `(2 * m_r - 1) / 3 = 2 ^ (r + 1) - 1`, and
         `binaryPopcount m_r = r + 1 ∧ binaryPopcount (2 * m_r) = r + 1 ∧
          binaryPopcount ((2 * m_r - 1) / 3) = r + 1`!
     - For EVERY `s ≥ 2`, `m_s := 4 ^ s + 1` satisfies `m_s % 3 = 2`,
       `binBitLength m_s = 2 * s + 1`, `binBitLength ((2 * m_s - 1) / 3) = 2 * s`,
       `binaryPopcount m_s = 2`, `binaryPopcount (2 * m_s) = 2`, AND
       `binaryPopcount ((2 * m_s - 1) / 3) = s + 1` (at `s = 4`: `257 <- 171`, `2 -> 5`)!
  2. **Universal Pure-Popcount Impossibility (`∀ M_0 ≥ 3`)**:
     NO weight `wNum n = fNum (binaryPopcount n), wDen n = fDen (binaryPopcount n)` can be an
     eventual preimage weight!
  3. **Arbitrary-Slack Popcount-Rewarding Joint Exponential Impossibility (`∀ M_0 ≥ 3`, `q_P < p_P`)**:
     Even if `binBitLength` decays at an arbitrary base `p_L / q_L`, ANY two-sided joint weight
     rewarding `binaryPopcount` (`q_P < p_P`) collapses in 1 step on `m_s = 4 ^ s + 1`!
  4. **Unrestricted-Numerator Joint Sub-Cube-Root-of-2 Impossibility (`∀ M_0 ≥ 3`)**:
     For ANY unrestricted numerator `wNum` and ANY `p_L, q_L, p_P, q_P ≥ 1` with
     `(p_P ≤ q_P ∧ p_L ^ 3 < 2 * q_L ^ 3) ∨ (q_P ≤ p_P ∧ (p_L * p_P) ^ 3 < 2 * (q_L * q_P) ^ 3)`:
     if `∀ n ≥ M_0`, `(q_L ^ binBitLength n * q_P ^ binaryPopcount n) * wDen n ≤
       C_den * (p_L ^ binBitLength n * p_P ^ binaryPopcount n)`,
     then `¬ IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta`!
-/
theorem eventual_joint_bitlength_popcount_exp_impossibility :
    ((∀ r : Nat, r ≥ 2 ->
        let m := 3 * 2 ^ r - 1
        m % 3 = 2 ∧ (2 * m - 1) / 3 = 2 ^ (r + 1) - 1 ∧
        binaryPopcount m = r + 1 ∧
        binaryPopcount (2 * m) = r + 1 ∧
        binaryPopcount ((2 * m - 1) / 3) = r + 1) ∧
     (∀ s : Nat, s ≥ 2 ->
        let m := 4 ^ s + 1
        let nOdd := (2 * m - 1) / 3
        m % 3 = 2 ∧
        binBitLength m = 2 * s + 1 ∧
        binBitLength nOdd = 2 * s ∧
        binaryPopcount m = 2 ∧
        binaryPopcount (2 * m) = 2 ∧
        binaryPopcount nOdd = s + 1) ∧
     binaryPopcount 257 = 2 ∧ binaryPopcount 514 = 2 ∧ binaryPopcount 171 = 5) ∧
    (∀ (M_0 : Nat), M_0 ≥ 3 ->
      ∀ (fNum fDen : Nat -> Nat) (pTheta qTheta : Nat),
        ¬ IsEventualPositiveRationalPreimageWeight M_0
            (fun n => fNum (binaryPopcount n))
            (fun n => fDen (binaryPopcount n))
            pTheta qTheta) ∧
    (∀ (M_0 : Nat), M_0 ≥ 3 ->
      ∀ (wNum wDen : Nat -> Nat) (c_0 C_hi p_L q_L p_P q_P pTheta qTheta : Nat),
        c_0 ≥ 1 -> p_L ≥ 1 -> q_L ≥ 1 -> q_P ≥ 1 -> q_P < p_P ->
        (∀ n : Nat, n ≥ M_0 ->
          c_0 * (q_L ^ binBitLength n * p_P ^ binaryPopcount n) * wDen n ≤
            (p_L ^ binBitLength n * q_P ^ binaryPopcount n) * wNum n ∧
          (p_L ^ binBitLength n * q_P ^ binaryPopcount n) * wNum n ≤
            C_hi * (q_L ^ binBitLength n * p_P ^ binaryPopcount n) * wDen n) ->
        ¬ IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta) ∧
    (∀ (M_0 : Nat), M_0 ≥ 3 ->
      ∀ (wNum wDen : Nat -> Nat) (C_den p_L q_L p_P q_P pTheta qTheta : Nat),
        p_L ≥ 1 -> q_L ≥ 1 -> p_P ≥ 1 -> q_P ≥ 1 ->
        ((p_P ≤ q_P ∧ p_L ^ 3 < 2 * q_L ^ 3) ∨
         (q_P ≤ p_P ∧ (p_L * p_P) ^ 3 < 2 * (q_L * q_P) ^ 3)) ->
        (∀ n : Nat, n ≥ M_0 ->
          (q_L ^ binBitLength n * q_P ^ binaryPopcount n) * wDen n ≤
            C_den * (p_L ^ binBitLength n * p_P ^ binaryPopcount n)) ->
        ¬ IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta) := by
  have hmers : ∀ r : Nat, r ≥ 2 ->
      let m := 3 * 2 ^ r - 1
      m % 3 = 2 ∧ (2 * m - 1) / 3 = 2 ^ (r + 1) - 1 ∧
      binaryPopcount m = r + 1 ∧
      binaryPopcount (2 * m) = r + 1 ∧
      binaryPopcount ((2 * m - 1) / 3) = r + 1 := by
    intro r hr; dsimp only
    have hp := pow2_pos_nat r
    have hodd_eq : (2 * (3 * 2 ^ r - 1) - 1) / 3 = 2 ^ (r + 1) - 1 := by
      rw [Nat.pow_succ 2 r]; omega
    have hpm : binaryPopcount (3 * 2 ^ r - 1) = r + 1 :=
      binPopcount_three_mul_pow2_sub1 r (by omega)
    refine ⟨by omega, hodd_eq, hpm, ?_, ?_⟩
    · unfold binaryPopcount; rw [binPopcount_double]; exact hpm
    · rw [hodd_eq]; exact binPopcount_mersenne (r + 1)
  have halt : ∀ s : Nat, s ≥ 2 ->
      let m := 4 ^ s + 1
      let nOdd := (2 * m - 1) / 3
      m % 3 = 2 ∧
      binBitLength m = 2 * s + 1 ∧
      binBitLength nOdd = 2 * s ∧
      binaryPopcount m = 2 ∧
      binaryPopcount (2 * m) = 2 ∧
      binaryPopcount nOdd = s + 1 := by
    intro s hs; dsimp only
    have hm3 : ∀ k : Nat, 4 ^ k % 3 = 1 := by
      intro k; induction k with
      | zero => rfl
      | succ k' ih => rw [Nat.pow_succ, Nat.mul_mod, ih]
    have h4_m3 := hm3 s
    have h4_pow2 : 4 ^ s = 2 ^ (2 * s) := pow4_eq_pow2_even s
    have hp2s_ge4 : 2 ^ (2 * s) ≥ 16 := by
      have hc : (2 : Nat) ^ 4 = 16 := by decide
      rw [← hc]; exact pow2_mono_nat (by omega)
    have hbl_m : binBitLength (4 ^ s + 1) = 2 * s + 1 := by
      apply binBitLength_of_pow2_sandwich (2 * s) (4 ^ s + 1)
      · rw [h4_pow2]; omega
      · rw [Nat.pow_succ 2 (2 * s), h4_pow2]; omega
    have hbl_o : binBitLength ((2 * (4 ^ s + 1) - 1) / 3) = 2 * s := by
      have hlo : 2 ^ (2 * s - 1) ≤ (2 * (4 ^ s + 1) - 1) / 3 := by
        have hp_sp : 2 ^ (2 * s) = 2 * 2 ^ (2 * s - 1) := by
          conv => lhs; rw [show 2 * s = (2 * s - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
        rw [h4_pow2, hp_sp]
        have hp1 := pow2_pos_nat (2 * s - 1)
        omega
      have hhi : (2 * (4 ^ s + 1) - 1) / 3 < 2 ^ (2 * s) := by
        rw [h4_pow2]; omega
      have h := binBitLength_of_pow2_sandwich (2 * s - 1) ((2 * (4 ^ s + 1) - 1) / 3) hlo
        (by rwa [show (2 * s - 1) + 1 = 2 * s by omega])
      omega
    have hpop_m : binaryPopcount (4 ^ s + 1) = 2 := by
      have heq : 4 ^ s + 1 = 2 * 2 ^ (2 * s - 1) + 1 := by
        rw [h4_pow2]
        conv => lhs; lhs; rw [show 2 * s = (2 * s - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
      unfold binaryPopcount
      rw [heq, binPopcount_double_add_one, binPopcount_pow2]
    have hpop_o : binaryPopcount ((2 * (4 ^ s + 1) - 1) / 3) = s + 1 := by
      have heq : (2 * (4 ^ s + 1) - 1) / 3 = 2 * ((4 ^ s - 1) / 3) + 1 := by omega
      unfold binaryPopcount
      rw [heq, binPopcount_double_add_one, binPopcount_alt_geom s]
    exact ⟨by omega, hbl_m, hbl_o, hpop_m,
           by unfold binaryPopcount; rw [binPopcount_double]; exact hpop_m,
           hpop_o⟩
  refine ⟨⟨hmers, halt, by decide, by decide, by decide⟩, ?_, ?_, ?_⟩
  · intro M_0 hM0 fNum fDen pTheta qTheta hw
    let r := M_0 + 2
    rcases hmers r (by omega) with ⟨hm_3, hodd_eq, hpm, hp2m, hpo⟩
    let m := 3 * 2 ^ r - 1
    have hr_lt : r + 1 < 2 ^ (r + 1) := id_lt_pow2_w14s (r + 1)
    have hnOdd_M0 : (2 * m - 1) / 3 ≥ M_0 := by
      dsimp [m]; rw [hodd_eq]; dsimp [r] at hr_lt ⊢; omega
    have hm_M0 : m ≥ M_0 := by omega
    have hpre := hw.2.2.2.2 m hm_M0 hm_3
    dsimp only at hpre
    rw [hpm, hp2m, hpo] at hpre
    have hA_pos : fNum (r + 1) ≥ 1 := by
      have h := (hw.2.2.1 m hm_M0).1; dsimp only at h; rwa [hpm] at h
    have hB_pos : fDen (r + 1) ≥ 1 := by
      have h := (hw.2.2.1 m hm_M0).2; dsimp only at h; rwa [hpm] at h
    let P_ab := fNum (r + 1) * (fDen (r + 1) * fDen (r + 1))
    have hP_pos : P_ab > 0 :=
      Nat.mul_le_mul hA_pos (Nat.mul_le_mul hB_pos hB_pos)
    have hlhs : qTheta * ((fNum (r + 1) * fDen (r + 1) + fNum (r + 1) * fDen (r + 1)) * fDen (r + 1)) =
        (2 * qTheta) * P_ab := by
      dsimp [P_ab]
      rw [Nat.add_mul (fNum (r + 1) * fDen (r + 1)) (fNum (r + 1) * fDen (r + 1)) (fDen (r + 1)),
          Nat.mul_add qTheta,
          show (2 : Nat) = 1 + 1 from rfl, Nat.add_mul 1 1 qTheta, Nat.one_mul, Nat.add_mul]
      ac_rfl
    rw [hlhs] at hpre
    have h2q_le : 2 * qTheta ≤ pTheta := nat_mul_le_cancel_right_w5 P_ab _ _ hP_pos hpre
    have hp_pos := hw.1
    have hpq_le := hw.2.1
    omega
  · intro M_0 hM0 wNum wDen c_0 C_hi p_L q_L p_P q_P pTheta qTheta
      hc0 hpL hqL hqP hqp_lt hsand hw
    have hq_pos : qTheta > 0 := Nat.lt_of_lt_of_le hw.1 hw.2.1
    let K_0 := C_hi * q_L + M_0 + 2
    let e := K_0 * q_P
    let s := e + 1
    have hs2 : s ≥ 2 := by
      have hm1 : 2 * 1 ≤ K_0 * q_P := Nat.mul_le_mul (by dsimp [K_0]; omega) hqP
      dsimp [s, e]; omega
    rcases halt s hs2 with ⟨hm_3, hbl_m, hbl_o, hpop_m, _, hpop_o⟩
    let m := 4 ^ s + 1
    let nOdd := (2 * m - 1) / 3
    have hnOdd_M0 : nOdd ≥ M_0 := by
      have hs_M0 : 2 * s ≥ M_0 + 2 := by
        have hm1 : K_0 * 1 ≤ K_0 * q_P := Nat.mul_le_mul_left K_0 hqP
        dsimp [s, e, K_0] at hm1 ⊢; omega
      have hlt := id_lt_pow2_w14s (2 * s - 1)
      have h4p := pow4_eq_pow2_even s
      have hp_sp : 2 ^ (2 * s) = 2 * 2 ^ (2 * s - 1) := by
        conv => lhs; rw [show 2 * s = (2 * s - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
      dsimp [nOdd, m]
      rw [h4p, hp_sp]; omega
    have hm_M0 : m ≥ M_0 := by dsimp [nOdd] at hnOdd_M0; omega
    have hpre := hw.2.2.2.2 m hm_M0 hm_3
    dsimp only at hpre
    have hbr : (wNum (2 * m) * wDen nOdd + wNum nOdd * wDen (2 * m)) * wDen m ≤
        wNum m * (wDen (2 * m) * wDen nOdd) :=
      nat_mul_le_cancel_left_w5 qTheta _ _ hq_pos
        (Nat.le_trans hpre (Nat.mul_le_mul_right _ hw.2.1))
    have hd2_pos : wDen (2 * m) > 0 := (hw.2.2.1 (2 * m) (by omega)).2
    have hdrop : wNum nOdd * wDen m ≤ wNum m * wDen nOdd := by
      have hm_d2 : (wNum nOdd * wDen m) * wDen (2 * m) ≤ (wNum m * wDen nOdd) * wDen (2 * m) := by
        have hl : (wNum nOdd * wDen m) * wDen (2 * m) = (wNum nOdd * wDen (2 * m)) * wDen m := by ac_rfl
        have hr : (wNum m * wDen nOdd) * wDen (2 * m) = wNum m * (wDen (2 * m) * wDen nOdd) := by ac_rfl
        rw [hl, hr]; rw [Nat.add_mul] at hbr; omega
      exact nat_mul_le_cancel_right_w5 (wDen (2 * m)) _ _ hd2_pos hm_d2
    have hlo_o := (hsand nOdd hnOdd_M0).1
    have hhi_m := (hsand m hm_M0).2
    rw [hbl_o, hpop_o] at hlo_o
    rw [hbl_m, hpop_m] at hhi_m
    have hwd_m_pos : wDen m ≥ 1 := (hw.2.2.1 m hm_M0).2
    have hwd_o_pos : wDen nOdd ≥ 1 := (hw.2.2.1 nOdd hnOdd_M0).2
    let F_common := (p_L ^ (2 * s) * q_L ^ (2 * s) * q_P ^ 2 * p_P ^ 2) * (wDen m * wDen nOdd)
    have hF_pos : F_common > 0 := by
      dsimp [F_common]
      have h1 := nat_pow_pos_of_pos p_L hpL (2 * s)
      have h2 := nat_pow_pos_of_pos q_L hqL (2 * s)
      have h3 := nat_pow_pos_of_pos q_P hqP 2
      have h4 := nat_pow_pos_of_pos p_P (by omega) 2
      exact Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3) h4)
        (Nat.mul_le_mul hwd_m_pos hwd_o_pos)
    have hcomb_p : F_common * (c_0 * p_L * p_P ^ e) ≤
        F_common * ((C_hi * q_L) * q_P ^ e) := by
      have hpP_sp : p_P ^ (s + 1) = p_P ^ 2 * p_P ^ e := by
        dsimp [s]; rw [show e + 1 + 1 = 2 + e by omega, Nat.pow_add]
      have hqP_sp : q_P ^ (s + 1) = q_P ^ 2 * q_P ^ e := by
        dsimp [s]; rw [show e + 1 + 1 = 2 + e by omega, Nat.pow_add]
      have hpL_sp : p_L ^ (2 * s + 1) = p_L ^ (2 * s) * p_L := by rw [Nat.pow_succ]
      have hqL_sp : q_L ^ (2 * s + 1) = q_L ^ (2 * s) * q_L := by rw [Nat.pow_succ]
      have hl : F_common * (c_0 * p_L * p_P ^ e) =
          ((p_L ^ (2 * s + 1) * q_P ^ 2) * wDen m) *
            (c_0 * (q_L ^ (2 * s) * p_P ^ (s + 1)) * wDen nOdd) := by
        dsimp [F_common]; rw [hpP_sp, hpL_sp]; ac_rfl
      have hr : F_common * ((C_hi * q_L) * q_P ^ e) =
          (p_L ^ (2 * s) * q_P ^ (s + 1)) *
            ((C_hi * (q_L ^ (2 * s + 1) * p_P ^ 2) * wDen m) * wDen nOdd) := by
        dsimp [F_common]; rw [hqP_sp, hqL_sp]; ac_rfl
      rw [hl, hr]
      calc
        ((p_L ^ (2 * s + 1) * q_P ^ 2) * wDen m) *
            (c_0 * (q_L ^ (2 * s) * p_P ^ (s + 1)) * wDen nOdd)
            ≤ ((p_L ^ (2 * s + 1) * q_P ^ 2) * wDen m) *
                ((p_L ^ (2 * s) * q_P ^ (s + 1)) * wNum nOdd) :=
              Nat.mul_le_mul_left _ hlo_o
        _ = (p_L ^ (2 * s) * q_P ^ (s + 1)) *
              ((p_L ^ (2 * s + 1) * q_P ^ 2) * (wNum nOdd * wDen m)) := by ac_rfl
        _ ≤ (p_L ^ (2 * s) * q_P ^ (s + 1)) *
              ((p_L ^ (2 * s + 1) * q_P ^ 2) * (wNum m * wDen nOdd)) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hdrop)
        _ = (p_L ^ (2 * s) * q_P ^ (s + 1)) *
              (((p_L ^ (2 * s + 1) * q_P ^ 2) * wNum m) * wDen nOdd) := by ac_rfl
        _ ≤ (p_L ^ (2 * s) * q_P ^ (s + 1)) *
              ((C_hi * (q_L ^ (2 * s + 1) * p_P ^ 2) * wDen m) * wDen nOdd) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hhi_m)
    have hcanc_F := nat_mul_le_cancel_left_w5 F_common _ _ hF_pos hcomb_p
    have hc0_pL : 1 ≤ c_0 * p_L := Nat.mul_le_mul hc0 hpL
    have hpP_le : p_P ^ e ≤ K_0 * q_P ^ e := by
      have h1 : 1 * p_P ^ e ≤ (c_0 * p_L) * p_P ^ e := Nat.mul_le_mul_right _ hc0_pL
      rw [Nat.one_mul] at h1
      have hK : C_hi * q_L ≤ K_0 := by dsimp [K_0]; omega
      exact Nat.le_trans (Nat.le_trans h1 hcanc_F) (Nat.mul_le_mul_right _ hK)
    have hgt_pow := pow_gt_const_mul_pow_of_lt_w14s q_P p_P K_0 hqP hqp_lt
    dsimp only [e] at hpP_le hgt_pow
    omega
  · intro M_0 hM0 wNum wDen C_den p_L q_L p_P q_P pTheta qTheta
      hpL hqL hpP hqP hcases hden
    rcases hcases with ⟨hpqP, hcritL⟩ | ⟨hqpP, hcritLP⟩
    · apply eventual_exp_bitlength_cube_root_two_impossibility.2 M_0 hM0
        wNum wDen C_den p_L q_L pTheta qTheta hpL hqL hcritL
      intro n hn
      have hd := hden n hn
      let L := binBitLength n
      let P := binaryPopcount n
      have hp_le : p_P ^ P ≤ q_P ^ P := pow_mono_base_w14s p_P q_P hpqP P
      have hqP_pos : q_P ^ P > 0 := nat_pow_pos_of_pos q_P hqP P
      have hm : (q_L ^ L * wDen n) * q_P ^ P ≤ (C_den * p_L ^ L) * q_P ^ P := by
        calc
          (q_L ^ L * wDen n) * q_P ^ P = (q_L ^ L * q_P ^ P) * wDen n := by ac_rfl
          _ ≤ C_den * (p_L ^ L * p_P ^ P) := hd
          _ ≤ C_den * (p_L ^ L * q_P ^ P) := Nat.mul_le_mul_left C_den (Nat.mul_le_mul_left _ hp_le)
          _ = (C_den * p_L ^ L) * q_P ^ P := by ac_rfl
      exact nat_mul_le_cancel_right_w5 (q_P ^ P) _ _ hqP_pos hm
    · apply eventual_exp_bitlength_cube_root_two_impossibility.2 M_0 hM0
        wNum wDen C_den (p_L * p_P) (q_L * q_P) pTheta qTheta
        (Nat.mul_le_mul hpL hpP) (Nat.mul_le_mul hqL hqP) hcritLP
      intro n hn
      have hd := hden n hn
      let L := binBitLength n
      let P := binaryPopcount n
      have hPL : P ≤ L := (binPopcount_le_binBitLength_aux n n (Nat.le_refl n)).1
      let D_p := L - P
      have hsp : P + D_p = L := by dsimp [D_p]; omega
      have hqD_pD : q_P ^ D_p ≤ p_P ^ D_p := pow_mono_base_w14s q_P p_P hqpP D_p
      rw [mul_pow_w14s q_L q_P L, mul_pow_w14s p_L p_P L]
      calc
        (q_L ^ L * q_P ^ L) * wDen n
            = ((q_L ^ L * q_P ^ P) * wDen n) * q_P ^ D_p := by
                rw [← hsp, Nat.pow_add q_P P D_p]; ac_rfl
        _ ≤ (C_den * (p_L ^ L * p_P ^ P)) * p_P ^ D_p := Nat.mul_le_mul hd hqD_pD
        _ = C_den * (p_L ^ L * p_P ^ L) := by
              rw [← hsp, Nat.pow_add p_P P D_p]; ac_rfl

-- ============================================================================
-- SECTION 2: Front C Part 2 (Branch P5.13) — 11th Solvable `(3x+1)`-Cousin
--            `T_diamond11` with Genuine 9-Tier `ω^9` Cascade
--            (`Cone 12 -> Cone 11 -> ... -> Cone 5 -> Φ_diamond2`, `W14_H1`)
-- ============================================================================

/-- Cone 12 of `T_diamond11`: `1749811 + x = 2 ^ a * 3 ^ b` with `a ≥ 34, b ≥ 1`
    (starting at `x = 2 ^ 34 * 3 - 1749811 = 51537857741`). -/
def isDiamond11Cone12 (x : Nat) : Prop :=
  x ≥ 51537857741 ∧ x % 17179869184 = 17178119373 ∧ x % 3 = 2 ∧ coprime23Core (1749811 + x) = 1

instance (x : Nat) : Decidable (isDiamond11Cone12 x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/--
  11th solvable mixed-(2, 3) Collatz cousin `T_diamond11` on `Nat`:
  Extends `T_diamond10` by adding Cone 12 (`isDiamond11Cone12 x -> (3 * x + 1) / 8`, a genuine
  `v_2(3x + 1) = 3` Syracuse jump that steps `2 ^ a * 3 ^ b - 1749811 -> 2 ^ (a - 3) * 3 ^ (b + 1) - 656179`
  directly into Cone 11 -> Cone 10 -> Cone 9 -> Cone 8 -> Cone 7 -> Cone 6 -> Cone 5's `r`-block spiral climb, e.g.
  `51537857741 -> 19326696653 -> 7247511245 -> 2717816717 -> 1019181269 -> 23887061 -> 559853 -> 209945 -> ... -> 1`
  in `22` steps, jumping `cousinDiamond2Phi` upward `+38.44x` and defeating 8-tier `ω^8` rankings)!
-/
def cousinDiamond11Step (x : Nat) : Nat :=
  if isDiamond11Cone12 x then (3 * x + 1) / 8 else cousinDiamond10Step x

def cousinDiamond11Iter : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamond11Iter k (cousinDiamond11Step x)

theorem cousinDiamond11Iter_add : ∀ (a b x : Nat),
    cousinDiamond11Iter (a + b) x = cousinDiamond11Iter b (cousinDiamond11Iter a x)
  | 0, _, _ => by simp [cousinDiamond11Iter]
  | a + 1, b, x => by
    rw [Nat.succ_add]
    exact cousinDiamond11Iter_add a b (cousinDiamond11Step x)

/-- Signed extension of `T_diamond11` (`q = 3`) to `Int` for `M2 = Z^-` separation. -/
def cousinDiamond11StepInt (x : Int) : Int :=
  if x ≥ 51537857741 ∧ x % 17179869184 = 17178119373 ∧ x % 3 = 2 ∧ coprime23Core (1749811 + x.toNat) = 1
  then (3 * x + 1) / 8
  else cousinDiamond10StepInt x

def cousinDiamond11IterInt : Nat -> Int -> Int
  | 0, x => x
  | k + 1, x => cousinDiamond11IterInt k (cousinDiamond11StepInt x)

/-- Hensel lift of `invMod2147483648Odd` (`2^31`) to `mod 17179869184` (`2^34`, since `31 * 2 = 62 ≥ 34`). -/
def invMod17179869184Odd (d : Nat) : Nat :=
  let i2b := invMod2147483648Odd d
  (i2b * (34359738370 - ((d % 17179869184) * i2b) % 17179869184)) % 17179869184

/-- Canonical reduced-pair extension of `T_diamond11` (`q = 3`) to positive `Q_(6)^+`. -/
def cousinDiamond11StepQ6 (p : Nat × Nat) : Nat × Nat :=
  let num := p.1
  let den := p.2
  let r17b := (num * invMod17179869184Odd den) % 17179869184
  let r3 := (num * (den % 3)) % 3
  if num ≥ 51537857741 * den ∧ r17b = 17178119373 ∧ r3 = 2 ∧ core3 (core2 (1749811 * den + num)) = den
  then reduceRatPair (3 * num + den) (8 * den)
  else cousinDiamond10StepQ6 p

def cousinDiamond11IterQ6 : Nat -> (Nat × Nat) -> (Nat × Nat)
  | 0, p => p
  | k + 1, p => cousinDiamond11IterQ6 k (cousinDiamond11StepQ6 p)

/-- Generalized odd-multiplier `q` step of `T_diamond11` on `Nat` for `M3` (`q = 7`) separation. -/
def cousinDiamond11StepParam (q x : Nat) : Nat :=
  if isDiamond11Cone12 x then (q * x + 1) / 8 else cousinDiamond10StepParam q x

def cousinDiamond11IterParam (q : Nat) : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamond11IterParam q k (cousinDiamond11StepParam q x)

/--
  Theorem W14.3c (`cousinDiamond11StepInt_ofNat_eq`, `zero custom axioms`):
  Exact `Nat`/`Int` step agreement for `T_diamond11` (`∀ x : Nat`).
-/
theorem cousinDiamond11StepInt_ofNat_eq (x : Nat) :
    cousinDiamond11StepInt (x : Int) = (cousinDiamond11Step x : Int) := by
  have h1 : ((x : Int) ≥ 51537857741) ↔ (x ≥ 51537857741) := by omega
  have h2 : ((x : Int) % 17179869184 = 17178119373) ↔ (x % 17179869184 = 17178119373) :=
    ⟨Int.ofNat.inj, congrArg Int.ofNat⟩
  have h3 : ((x : Int) % 3 = 2) ↔ (x % 3 = 2) :=
    ⟨Int.ofNat.inj, congrArg Int.ofNat⟩
  have hdiv : ((3 * (x : Int) + 1) / 8) = (((3 * x + 1) / 8 : Nat) : Int) := by omega
  have htoNat : (x : Int).toNat = x := rfl
  unfold cousinDiamond11StepInt cousinDiamond11Step isDiamond11Cone12
  rw [htoNat]
  simp only [h1, h2, h3]
  by_cases hc12 : x ≥ 51537857741 ∧ x % 17179869184 = 17178119373 ∧ x % 3 = 2 ∧ coprime23Core (1749811 + x) = 1
  · simp only [hc12, and_self, ite_true, hdiv]
  · simp only [hc12, ite_false]
    exact cousinDiamond10StepInt_ofNat_eq x

theorem cousinDiamond11Step_pos (x : Nat) (hx : x > 0) : cousinDiamond11Step x > 0 := by
  unfold cousinDiamond11Step
  by_cases hc12 : isDiamond11Cone12 x
  · simp only [hc12, ite_true]
    have hge : x ≥ 51537857741 := hc12.1
    clear hc12
    have hle : (3 * 51537857741 + 1) / 8 ≤ (3 * x + 1) / 8 :=
      Nat.div_le_div_right (by omega)
    exact Nat.lt_of_lt_of_le (by decide : 0 < (3 * 51537857741 + 1) / 8) hle
  · simp only [hc12, ite_false]; exact cousinDiamond10Step_pos x hx

theorem cousinDiamond11Step_eq_d10_of_not_cone12 (x : Nat) (hnc12 : ¬ isDiamond11Cone12 x) :
    cousinDiamond11Step x = cousinDiamond10Step x := by
  unfold cousinDiamond11Step; simp [hnc12]

/--
  Theorem W14.3d (`cousin_diamond11_outside_cones4to12_strict_descent`, `zero custom axioms`):
  Outside Cones 4, 5, 6, 7, 8, 9, 10, 11, and 12, EVERY `x > 2` strictly decreases `cousinDiamond2Phi` in 1 step!
-/
theorem cousin_diamond11_outside_cones4to12_strict_descent
    (x : Nat) (hx : x > 2)
    (hnc4 : ¬ isDiamond3Cone4 x) (hnc5 : ¬ isDiamond4Cone5 x)
    (hnc6 : ¬ isDiamond5Cone6 x) (hnc7 : ¬ isDiamond6Cone7 x)
    (hnc8 : ¬ isDiamond7Cone8 x) (hnc9 : ¬ isDiamond8Cone9 x)
    (hnc10 : ¬ isDiamond9Cone10 x) (hnc11 : ¬ isDiamond10Cone11 x)
    (hnc12 : ¬ isDiamond11Cone12 x) :
    cousinDiamond2Phi (cousinDiamond11Step x) < cousinDiamond2Phi x := by
  rw [cousinDiamond11Step_eq_d10_of_not_cone12 x hnc12]
  exact cousin_diamond10_outside_cones4to11_strict_descent x hx hnc4 hnc5 hnc6 hnc7 hnc8 hnc9 hnc10 hnc11

-- Modular Cone-12 avoidance helpers (`17178119373 % 2147483648 = 2145733837, % 268435456 = 266685645, % 256 = 205, % 32 = 13`):

theorem mod2b_of_cone12 (z : Nat) (hc12 : isDiamond11Cone12 z) : z % 2147483648 = 2145733837 := by
  have h := congrArg (· % 2147483648) hc12.2.1
  rwa [Nat.mod_mod_of_dvd z (by decide : 2147483648 ∣ 17179869184)] at h

theorem mod268m_of_cone12 (z : Nat) (hc12 : isDiamond11Cone12 z) : z % 268435456 = 266685645 := by
  have h := congrArg (· % 268435456) (mod2b_of_cone12 z hc12)
  rwa [Nat.mod_mod_of_dvd z (by decide : 268435456 ∣ 2147483648)] at h

theorem mod256_of_cone12 (z : Nat) (hc12 : isDiamond11Cone12 z) : z % 256 = 205 := by
  have h := congrArg (· % 256) (mod268m_of_cone12 z hc12)
  rwa [Nat.mod_mod_of_dvd z (by decide : 256 ∣ 268435456)] at h

theorem mod32_of_cone12 (z : Nat) (hc12 : isDiamond11Cone12 z) : z % 32 = 13 := by
  have h := congrArg (· % 32) (mod256_of_cone12 z hc12)
  rwa [Nat.mod_mod_of_dvd z (by decide : 32 ∣ 256)] at h

theorem not_cone12_of_even (z : Nat) (hev : z % 2 = 0) : ¬ isDiamond11Cone12 z := by
  intro hc12
  have h := congrArg (· % 2) (mod32_of_cone12 z hc12)
  rw [Nat.mod_mod_of_dvd z (by decide : 2 ∣ 32), hev] at h
  cases h

theorem not_cone12_of_mod4_eq_3 (z : Nat) (hm4 : z % 4 = 3) : ¬ isDiamond11Cone12 z := by
  intro hc12
  have h := congrArg (· % 4) (mod32_of_cone12 z hc12)
  rw [Nat.mod_mod_of_dvd z (by decide : 4 ∣ 32), hm4] at h
  cases h

theorem not_cone12_of_mod8_ne_5 (z : Nat) (hm8 : z % 8 ≠ 5) : ¬ isDiamond11Cone12 z := by
  intro hc12
  have h := congrArg (· % 8) (mod32_of_cone12 z hc12)
  rw [Nat.mod_mod_of_dvd z (by decide : 8 ∣ 32)] at h
  exact hm8 h

theorem not_cone12_of_mod16_ne_13 (z : Nat) (hm16 : z % 16 ≠ 13) : ¬ isDiamond11Cone12 z := by
  intro hc12
  have h := congrArg (· % 16) (mod32_of_cone12 z hc12)
  rw [Nat.mod_mod_of_dvd z (by decide : 16 ∣ 32)] at h
  exact hm16 h

theorem not_cone12_of_mod32_ne_13 (z : Nat) (hm32 : z % 32 ≠ 13) : ¬ isDiamond11Cone12 z :=
  fun hc12 => hm32 (mod32_of_cone12 z hc12)

theorem not_cone12_of_mod256_ne_205 (z : Nat) (hm256 : z % 256 ≠ 205) : ¬ isDiamond11Cone12 z :=
  fun hc12 => hm256 (mod256_of_cone12 z hc12)

theorem not_cone12_of_mod268m_ne (z : Nat) (hm : z % 268435456 ≠ 266685645) : ¬ isDiamond11Cone12 z :=
  fun hc12 => hm (mod268m_of_cone12 z hc12)

theorem not_cone12_of_mod2b_ne (z : Nat) (hm : z % 2147483648 ≠ 2145733837) : ¬ isDiamond11Cone12 z :=
  fun hc12 => hm (mod2b_of_cone12 z hc12)

theorem not_cone12_of_mod3_ne_2 (z : Nat) (hm3 : z % 3 ≠ 2) : ¬ isDiamond11Cone12 z := by
  rintro ⟨_, _, h3, _⟩; exact hm3 h3

/--
  Theorem W14.3e (`not_cone12_six_mul_pow9_sub1`, choice-free `zero custom axioms`):
  Universal Post-Climb Drain Non-Reentry into Cone 12 (`∀ m : Nat`, `(6 * 9^m - 1) % 16 = 5 ≠ 13`).
-/
theorem not_cone12_six_mul_pow9_sub1 (m : Nat) :
    ¬ isDiamond11Cone12 (6 * 9 ^ m - 1) := by
  apply not_cone12_of_mod16_ne_13
  have hp9 := nat_pow_pos_of_pos 9 (by decide) m
  have hm8 := pow9_mod8_eq_one_w5 m
  have hdm := (Nat.div_add_mod (9 ^ m) 8).symm
  omega

private theorem d11_eq_d9_of_not_cone1211 (x : Nat)
    (h : ¬ isDiamond11Cone12 x ∧ ¬ isDiamond10Cone11 x) :
    cousinDiamond11Step x = cousinDiamond9Step x := by
  rw [cousinDiamond11Step_eq_d10_of_not_cone12 x h.1,
      cousinDiamond10Step_eq_d9_of_not_cone11 x h.2]

private theorem not_cone1211_of_even (z : Nat) (hev : z % 2 = 0) :
    ¬ isDiamond11Cone12 z ∧ ¬ isDiamond10Cone11 z :=
  ⟨not_cone12_of_even z hev, not_cone11_of_even z hev⟩

private theorem not_cone1211_of_mod4_eq_3 (z : Nat) (hm4 : z % 4 = 3) :
    ¬ isDiamond11Cone12 z ∧ ¬ isDiamond10Cone11 z :=
  ⟨not_cone12_of_mod4_eq_3 z hm4, not_cone11_of_mod4_eq_3 z hm4⟩

private theorem not_cone1211_of_mod8_ne_5 (z : Nat) (hm8 : z % 8 ≠ 5) :
    ¬ isDiamond11Cone12 z ∧ ¬ isDiamond10Cone11 z :=
  ⟨not_cone12_of_mod8_ne_5 z hm8, not_cone11_of_mod8_ne_5 z hm8⟩

private theorem not_cone1211_of_mod16_ne_13 (z : Nat) (hm16 : z % 16 ≠ 13) :
    ¬ isDiamond11Cone12 z ∧ ¬ isDiamond10Cone11 z :=
  ⟨not_cone12_of_mod16_ne_13 z hm16, not_cone11_of_mod16_ne_13 z hm16⟩

private theorem not_cone1211_of_mod32_ne_13 (z : Nat) (hm32 : z % 32 ≠ 13) :
    ¬ isDiamond11Cone12 z ∧ ¬ isDiamond10Cone11 z :=
  ⟨not_cone12_of_mod32_ne_13 z hm32, not_cone11_of_mod32_ne_13 z hm32⟩

private theorem not_cone1211_of_mod256_ne_205 (z : Nat) (hm256 : z % 256 ≠ 205) :
    ¬ isDiamond11Cone12 z ∧ ¬ isDiamond10Cone11 z :=
  ⟨not_cone12_of_mod256_ne_205 z hm256, not_cone11_of_mod256_ne_205 z hm256⟩

private theorem not_cone1211_of_cone10 (z : Nat) (hc10 : isDiamond9Cone10 z) :
    ¬ isDiamond11Cone12 z ∧ ¬ isDiamond10Cone11 z :=
  ⟨not_cone12_of_mod268m_ne z (by rw [hc10.2.1]; decide),
   not_cone11_of_mod268m_ne z (by rw [hc10.2.1]; decide)⟩

private theorem not_cone1211_of_mod3_ne_2 (z : Nat) (hm3 : z % 3 ≠ 2) :
    ¬ isDiamond11Cone12 z ∧ ¬ isDiamond10Cone11 z :=
  ⟨not_cone12_of_mod3_ne_2 z hm3, not_cone11_of_mod3_ne_2 z hm3⟩

private theorem not_cone1211_six_mul_pow9_sub1 (m : Nat) :
    ¬ isDiamond11Cone12 (6 * 9 ^ m - 1) ∧ ¬ isDiamond10Cone11 (6 * 9 ^ m - 1) :=
  ⟨not_cone12_six_mul_pow9_sub1 m, not_cone11_six_mul_pow9_sub1 m⟩

theorem isDiamond10Cone11_of_pow2_pow3 (r s : Nat) (hr : r ≥ 31) (hs : s ≥ 1) :
    isDiamond10Cone11 (2 ^ r * 3 ^ s - 656179) := by
  have hc : (2 : Nat) ^ 31 = 2147483648 := by decide
  have hp2_ge : 2 ^ r ≥ 2147483648 := by
    rw [← hc]; exact pow2_mono_nat hr
  have hp3_ge : 3 ^ s ≥ 3 := by
    simpa using nat_pow_mono_exp_pos 3 1 s (by decide) hs
  have hprod_ge : 2 ^ r * 3 ^ s ≥ 6442450944 := by
    simpa using Nat.mul_le_mul hp2_ge hp3_ge
  have hp2b : 2147483648 ∣ 2 ^ r * 3 ^ s := by
    have hsp : r = 31 + (r - 31) := by omega
    rw [hsp, Nat.pow_add 2 31 (r - 31), hc, Nat.mul_assoc]
    exact ⟨2 ^ (r - 31) * 3 ^ s, rfl⟩
  have hp3_div : 3 ∣ 2 ^ r * 3 ^ s := by
    have hsp : s = 1 + (s - 1) := by omega
    rw [hsp, Nat.pow_add 3 1 (s - 1), Nat.pow_one,
        ← Nat.mul_assoc (2 ^ r) 3, Nat.mul_comm (2 ^ r) 3, Nat.mul_assoc]
    exact ⟨2 ^ r * 3 ^ (s - 1), rfl⟩
  refine ⟨by clear hc hp2_ge hp3_ge hp2b hp3_div; generalize 2 ^ r * 3 ^ s = P at hprod_ge ⊢; omega,
          ?_, ?_, ?_⟩
  · rcases hp2b with ⟨k, hk⟩
    clear hc hp2_ge hp3_ge hp3_div
    generalize 2 ^ r * 3 ^ s = P at hprod_ge hk ⊢
    have hk_ge : k ≥ 3 := by omega
    rw [hk, show k = (k - 1) + 1 by omega, Nat.mul_add 2147483648 (k - 1) 1, Nat.mul_one]
    generalize k - 1 = k'
    have hsub : 2147483648 * k' + 2147483648 - 656179 = 2146827469 + 2147483648 * k' := by omega
    rw [hsub, Nat.add_mul_mod_self_left]
  · rcases hp3_div with ⟨k3, hk3⟩
    clear hc hp2_ge hp3_ge hp2b
    generalize 2 ^ r * 3 ^ s = P at hprod_ge hk3 ⊢
    omega
  · have hadd : 656179 + (2 ^ r * 3 ^ s - 656179) = 2 ^ r * 3 ^ s := by
      clear hc hp2_ge hp3_ge hp2b hp3_div
      generalize 2 ^ r * 3 ^ s = P at hprod_ge ⊢
      omega
    rw [hadd]
    exact coprime23Core_pow2_pow3 r s

theorem cousin_diamond11_mersenne_scaled :
    ∀ (k a q : Nat), k + 1 ≤ a -> q ≥ 1 ->
      cousinDiamond11Iter k (2 ^ a * q - 1) = 3 ^ k * 2 ^ (a - k) * q - 1
  | 0, _, _, _, _ => by simp [cousinDiamond11Iter]
  | k + 1, a, q, hka, hq => by
    have hp4 : 2 ^ a * q = 4 * (2 ^ (a - 2) * q) := by
      conv => lhs; rw [show a = (a - 2) + 2 by omega]
      rw [Nat.pow_add 2 (a - 2) 2, show (2 : Nat) ^ 2 = 4 from rfl,
          Nat.mul_comm (2 ^ (a - 2)) 4, Nat.mul_assoc]
    have hm_pos : 2 ^ (a - 2) * q ≥ 1 := Nat.mul_le_mul (pow2_pos_nat (a - 2)) hq
    have hz4 : (2 ^ a * q - 1) % 4 = 3 := by omega
    simp only [cousinDiamond11Iter]
    rw [d11_eq_d9_of_not_cone1211 _ (not_cone1211_of_mod4_eq_3 _ hz4)]
    have hd9 := cousin_diamond9_mersenne_scaled 1 a q (by omega) hq
    simp only [cousinDiamond9Iter, Nat.pow_one] at hd9
    have hstep_eq : cousinDiamond9Step (2 ^ a * q - 1) = 2 ^ (a - 1) * (3 * q) - 1 := by
      rw [hd9]; apply congrArg (· - 1); ac_rfl
    rw [hstep_eq, cousin_diamond11_mersenne_scaled k (a - 1) (3 * q) (by omega) (by omega),
        show a - 1 - k = a - (k + 1) by omega, Nat.pow_succ 3 k]
    apply congrArg (· - 1); ac_rfl

theorem cousin_diamond11_even9_spine_drain :
    ∀ k : Nat, cousinDiamond11Iter k ((9 ^ (k + 1) - 1) / 4) = 2
  | 0 => rfl
  | k + 1 => by
    let j := k + 1
    have hp9j_ge9 : 9 ^ j ≥ 9 := by
      dsimp only [j]; rw [Nat.pow_succ]; have hp := nat_pow_pos_of_pos 9 (by decide) k; omega
    have hp9j_m8 : 9 ^ j % 8 = 1 := pow9_mod8_eq_one_w5 j
    let q := (9 ^ j - 1) / 8
    have hp9j_eq : 9 ^ j = 8 * q + 1 := by dsimp only [q]; omega
    have he_j1 : (9 ^ (j + 1) - 1) / 4 = 18 * q + 2 := by rw [Nat.pow_succ 9 j, hp9j_eq]; omega
    simp only [cousinDiamond11Iter]
    change cousinDiamond11Iter k (cousinDiamond11Step ((9 ^ (j + 1) - 1) / 4)) = 2
    have hnc1211 : ¬ isDiamond11Cone12 ((9 ^ (j + 1) - 1) / 4) ∧ ¬ isDiamond10Cone11 ((9 ^ (j + 1) - 1) / 4) := by
      rw [he_j1]; exact not_cone1211_of_even (18 * q + 2) (by omega)
    rw [d11_eq_d9_of_not_cone1211 _ hnc1211]
    have hd9 : cousinDiamond9Step ((9 ^ (j + 1) - 1) / 4) = (9 ^ j - 1) / 4 := by
      have he_j : (9 ^ j - 1) / 4 = 2 * q := by rw [hp9j_eq]; omega
      rw [he_j1, he_j,
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (18 * q + 2) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]; unfold cousinDiamond3Step
      have hq_pos : q ≥ 1 := by dsimp only [q]; omega
      have hodd_f : ¬ ((18 * q + 2) % 2 = 1) := by omega
      have h18_t : 18 * q + 2 ≥ 20 ∧ (18 * q + 2) % 18 = 2 := ⟨by omega, by omega⟩
      simp only [hodd_f, h18_t, and_self, ite_true, ite_false]; omega
    rw [hd9]
    exact cousin_diamond11_even9_spine_drain k

theorem cousin_diamond11_pow3_sub1_drain :
    ∀ k : Nat, cousinDiamond11Iter k (3 ^ (k + 1) - 1) = 2
  | 0 => rfl
  | k + 1 => by
    let j := k + 1
    have hp3_ge3 : 3 ^ j ≥ 3 := by dsimp only [j]; rw [Nat.pow_succ]; have hp := pow3_pos_nat k; omega
    have ho_j1 := pow3_odd_nat_sec8 (j + 1)
    have hp_j1 := pow3_pos_nat (j + 1)
    simp only [cousinDiamond11Iter]
    change cousinDiamond11Iter k (cousinDiamond11Step (3 ^ (j + 1) - 1)) = 2
    rw [d11_eq_d9_of_not_cone1211 _ (not_cone1211_of_even _ (by omega)),
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
            dsimp only [j]; rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]; omega
          have ho' := pow3_odd_nat_sec8 k'; omega
      have hm6 : 3 ^ (j + 1) - 1 > 2 ∧ (3 ^ (j + 1) - 1) % 6 = 2 := by rw [h3j1]; omega
      unfold cousinDiamond3Step
      simp only [hev, hn18, hm6, and_self, ite_true, ite_false]
      rw [h3j1]; omega
    rw [hd4]
    exact cousin_diamond11_pow3_sub1_drain k

theorem cousin_diamond11_cone5_two_step_climb :
    ∀ (q_c a b : Nat), 3 * q_c + 2 ≤ a -> b ≥ 1 ->
      cousinDiamond11Iter (2 * q_c) (2 ^ a * 3 ^ b - 7) =
        2 ^ (a - 3 * q_c) * 3 ^ (b + 2 * q_c) - 7
  | 0, _, _, _, _ => by simp [cousinDiamond11Iter]
  | q_c + 1, a, b, ha, hb => by
    have ha5 : a ≥ 5 := by omega
    have hc5 := isDiamond4Cone5_of_pow2_pow3 a b ha5 hb
    have hnc1211_0 : ¬ isDiamond11Cone12 (2 ^ a * 3 ^ b - 7) ∧ ¬ isDiamond10Cone11 (2 ^ a * 3 ^ b - 7) :=
      not_cone1211_of_mod32_ne_13 (2 ^ a * 3 ^ b - 7) (by have h := hc5.2.1; omega)
    let mid := 2 ^ (a - 2) * 3 ^ (b + 1) - 5
    have hmid_4 : mid % 4 = 3 := by
      dsimp only [mid]
      have hp8 : 2 ^ (a - 2) = 8 * 2 ^ (a - 5) := by
        conv => lhs; rw [show a - 2 = 3 + (a - 5) by omega]; rw [Nat.pow_add]
      rw [hp8, Nat.mul_assoc 8]
      have hp_pos : 2 ^ (a - 5) * 3 ^ (b + 1) ≥ 1 :=
        Nat.mul_le_mul (pow2_pos_nat _) (pow3_pos_nat _)
      omega
    have hnc1211_1 : ¬ isDiamond11Cone12 mid ∧ ¬ isDiamond10Cone11 mid := not_cone1211_of_mod4_eq_3 mid hmid_4
    have hd9_2 := cousin_diamond9_cone5_two_step_climb 1 a b (by omega) hb
    simp only [Nat.mul_one, cousinDiamond9Iter] at hd9_2
    have hd9_s1 : cousinDiamond9Step (2 ^ a * 3 ^ b - 7) = mid := by
      rw [cousinDiamond9Step_eq_d8_of_not_cone10 _
            (not_cone10_of_mod32_ne_13 _ (by have h := hc5.2.1; omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _
            (not_cone9_of_mod32_ne_13 _ (by have h := hc5.2.1; omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _
            (not_cone8_of_mod32_ne_21 _ (by have h := hc5.2.1; omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _
            (not_cone7_of_mod32_ne_21 _ (by have h := hc5.2.1; omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _
            (not_cone6_of_mod32_ne_13 _ (by have h := hc5.2.1; omega))]
      unfold cousinDiamond4Step; simp only [hc5, ite_true]
      dsimp only [mid]
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
    rw [hd9_s1] at hd9_2
    have hs1 : cousinDiamond11Step (2 ^ a * 3 ^ b - 7) = mid := by
      rw [d11_eq_d9_of_not_cone1211 _ hnc1211_0]; exact hd9_s1
    have hs2 : cousinDiamond11Step mid = 2 ^ (a - 3) * 3 ^ (b + 2) - 7 := by
      rw [d11_eq_d9_of_not_cone1211 _ hnc1211_1]; exact hd9_2
    rw [Nat.mul_succ 2 q_c, Nat.add_comm (2 * q_c) 2,
        cousinDiamond11Iter_add 2 (2 * q_c)]
    have hi2 : cousinDiamond11Iter 2 (2 ^ a * 3 ^ b - 7) = 2 ^ (a - 3) * 3 ^ (b + 2) - 7 := by
      simp only [cousinDiamond11Iter, hs1, hs2]
    rw [hi2, cousin_diamond11_cone5_two_step_climb q_c (a - 3) (b + 2) (by omega) (by omega)]
    apply congrArg (· - 7)
    congr 1
    · apply congrArg (2 ^ ·); omega
    · apply congrArg (3 ^ ·); omega

theorem cousin_diamond11_a0_3_drain (b0 : Nat) (hb0 : b0 ≥ 3) :
    cousinDiamond11Step (8 * 3 ^ b0 - 7) = 12 * 3 ^ b0 - 10 ∧
    cousinDiamond11Step (12 * 3 ^ b0 - 10) = 4 * 3 ^ b0 - 4 ∧
    cousinDiamond11Step (4 * 3 ^ b0 - 4) = 4 * 3 ^ (b0 - 1) - 2 ∧
    cousinDiamond11Iter ((b0 - 1) / 2 + 7) (8 * 3 ^ b0 - 7) = 1 := by
  rcases cousin_diamond9_a0_3_drain b0 hb0 with ⟨hd9_1, hd9_2, hd9_3, _⟩
  have hp3_ge27 : 3 ^ b0 ≥ 27 := by simpa using nat_pow_mono_exp_pos 3 3 b0 (by decide) hb0
  have hp3_b1_ge9 : 3 ^ (b0 - 1) ≥ 9 := by
    simpa using nat_pow_mono_exp_pos 3 2 (b0 - 1) (by decide) (by omega)
  have hnc1211_1 : ¬ isDiamond11Cone12 (8 * 3 ^ b0 - 7) ∧ ¬ isDiamond10Cone11 (8 * 3 ^ b0 - 7) := by
    apply not_cone1211_of_mod32_ne_13; have ho := pow3_odd_nat_sec8 b0; omega
  have hs1 : cousinDiamond11Step (8 * 3 ^ b0 - 7) = 12 * 3 ^ b0 - 10 := by
    rw [d11_eq_d9_of_not_cone1211 _ hnc1211_1]; exact hd9_1
  have hs2 : cousinDiamond11Step (12 * 3 ^ b0 - 10) = 4 * 3 ^ b0 - 4 := by
    rw [d11_eq_d9_of_not_cone1211 _ (not_cone1211_of_even _ (by omega))]; exact hd9_2
  have hs3 : cousinDiamond11Step (4 * 3 ^ b0 - 4) = 4 * 3 ^ (b0 - 1) - 2 := by
    rw [d11_eq_d9_of_not_cone1211 _ (not_cone1211_of_even _ (by omega))]; exact hd9_3
  refine ⟨hs1, hs2, hs3, ?_⟩
  by_cases hev_b1 : (b0 - 1) % 2 = 0
  · let m := (b0 - 1) / 2
    have hm1 : m ≥ 1 := by dsimp only [m]; omega
    have hb1_eq : b0 - 1 = 2 * m := by dsimp only [m]; omega
    have hp9_ge9 : 9 ^ m ≥ 9 := by rw [pow9_eq_pow3_double m, ← hb1_eq]; exact hp3_b1_ge9
    have hp9_m8 : 9 ^ m % 8 = 1 := pow9_mod8_eq_one_w5 m
    have h4_eq : 4 * 3 ^ (b0 - 1) - 2 = 4 * 9 ^ m - 2 := by
      rw [hb1_eq, ← pow9_eq_pow3_double m]
    let zr := 2 * 9 ^ m - 1
    let yr := (3 * 9 ^ m - 1) / 2
    have hs4 : cousinDiamond11Step (4 * 9 ^ m - 2) = zr := by
      rw [d11_eq_d9_of_not_cone1211 _ (not_cone1211_of_even _ (by omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (4 * 9 ^ m - 2) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h9m9 : 9 ^ m % 9 = 0 := by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
      rw [cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) (by omega)]
      dsimp only [zr]; omega
    have hsz : cousinDiamond11Step zr = yr := by
      rw [d11_eq_d9_of_not_cone1211 zr (not_cone1211_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 zr (not_cone10_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 zr (not_cone9_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 zr (not_cone8_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 zr (not_cone7_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 zr (not_cone6_of_mod16_ne_13 zr (by dsimp only [zr]; omega))]
      have hnc5 : ¬ isDiamond4Cone5 zr := by rintro ⟨_, h32, _, _⟩; dsimp only [zr] at h32; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 zr hnc5]
      have hc3 : core3 (zr + 1) = 2 := by
        rw [show zr + 1 = 2 * 9 ^ m by dsimp only [zr]; omega,
            core3_mul2 (9 ^ m) (by omega), (pow9_eq_v3Pow_w5 m).2]
      rw [cousinDiamond3Step_of_core3_succ_two_w8 zr (by dsimp only [zr]; omega) (by dsimp only [zr]; omega) hc3]
      dsimp only [zr, yr]; omega
    have hsy : cousinDiamond11Step yr = (9 ^ (m + 1) - 1) / 4 := by
      have hyr_m3 : yr % 3 = 1 := by
        have hm3 : 9 ^ m % 3 = 0 := by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
        dsimp only [yr]; omega
      rw [d11_eq_d9_of_not_cone1211 yr (not_cone1211_of_mod3_ne_2 yr (by omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 yr (not_cone10_of_mod3_ne_2 yr (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 yr (not_cone9_of_mod3_ne_2 yr (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 yr (not_cone8_of_mod3_ne_2 yr (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 yr (not_cone7_of_mod9_ne_8 yr (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 yr (not_cone6_of_mod9_ne_8 yr (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 yr := by rintro ⟨_, _, hm3, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 yr hnc5]
      have hc3_2 : core3 (2 * yr + 1) = 1 := by
        rw [show 2 * yr + 1 = 3 * 9 ^ m by dsimp only [yr]; omega,
            core3_mul3 (9 ^ m) (by omega), (pow9_eq_v3Pow_w5 m).2]
      have hc3_1 : core3 (yr + 1) ≠ 2 := by
        have hnd3 : (yr + 1) % 3 ≠ 0 := by
          clear hd9_1 hd9_2 hd9_3 hs1 hs2 hs3 h4_eq hs4 hsz hnc5 hc3_2; omega
        rw [core3_not_div3 (yr + 1) hnd3]
        clear hd9_1 hd9_2 hd9_3 hs1 hs2 hs3 h4_eq hs4 hsz hnc5 hc3_2
        dsimp only [yr]; omega
      have hnc4 : ¬ isDiamond3Cone4 yr := by
        rintro ⟨hge169, _, hc2⟩
        by_cases hm_eq1 : m = 1
        · clear hd9_1 hd9_2 hd9_3 hs1 hs2 hs3 h4_eq hs4 hsz hnc5 hc3_2 hc3_1 hc2
          dsimp only [yr] at hge169; rw [hm_eq1] at hge169; omega
        · have hm2 : m ≥ 2 := by
            clear hd9_1 hd9_2 hd9_3 hs1 hs2 hs3 h4_eq hs4 hsz hnc5 hc3_2 hc3_1 hge169 hc2; omega
          rcases eq_pow2_of_core2_eq_one (3 * yr + 5)
            (by clear hd9_1 hd9_2 hd9_3 hs1 hs2 hs3 h4_eq hs4 hsz hnc5 hc3_2 hc3_1; dsimp only [yr]; omega) hc2 with
            ⟨M0, hM0⟩
          have h9_eq : 9 ^ (m + 1) + 7 = 2 ^ (M0 + 1) := by
            have h2mul : 2 * (3 * yr + 5) = 9 ^ (m + 1) + 7 := by
              clear hd9_1 hd9_2 hd9_3 hs1 hs2 hs3 h4_eq hs4 hsz hnc5 hc3_2 hc3_1 hc2 hM0
              rw [Nat.pow_succ 9 m, Nat.mul_comm (9 ^ m) 9]; dsimp only [yr]; omega
            rw [← h2mul, hM0, Nat.pow_succ 2 M0, Nat.mul_comm]
          exact pow9_succ_add_seven_ne_pow2 m (M0 + 1) hm2 h9_eq
      rw [cousinDiamond3Step_odd_half_w8 yr (by dsimp only [yr]; omega) hnc4 hc3_2 hc3_1]
      dsimp only [yr]; rw [Nat.pow_succ 9 m]; omega
    change cousinDiamond11Iter (m + 7) (8 * 3 ^ b0 - 7) = 1
    rw [show m + 7 = 4 + 1 + 1 + m + 1 by omega,
        cousinDiamond11Iter_add (4 + 1 + 1 + m) 1,
        cousinDiamond11Iter_add (4 + 1 + 1) m,
        cousinDiamond11Iter_add (4 + 1) 1,
        cousinDiamond11Iter_add 4 1]
    have hi4 : cousinDiamond11Iter 4 (8 * 3 ^ b0 - 7) = zr := by
      simp only [cousinDiamond11Iter, hs1, hs2, hs3, h4_eq, hs4]
    rw [hi4]
    have hiz : cousinDiamond11Iter 1 zr = yr := hsz
    rw [hiz]
    have hiy : cousinDiamond11Iter 1 yr = (9 ^ (m + 1) - 1) / 4 := hsy
    rw [hiy, cousin_diamond11_even9_spine_drain m]
    decide
  · let m := (b0 - 1) / 2
    have hm1 : m ≥ 1 := by dsimp only [m]; omega
    have hb1_eq : b0 - 1 = 2 * m + 1 := by dsimp only [m]; omega
    have hp9_ge9 : 9 ^ m ≥ 9 := by
      rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]
      have hp := nat_pow_pos_of_pos 9 (by decide) (m - 1); omega
    have hp9_m8 : 9 ^ m % 8 = 1 := pow9_mod8_eq_one_w5 m
    let ur := 6 * 9 ^ m - 1
    let wr := (9 ^ (m + 1) - 1) / 2
    have hu_eq : 4 * 3 ^ (b0 - 1) - 2 = 12 * 9 ^ m - 2 := by
      rw [hb1_eq, Nat.pow_succ 3 (2 * m), ← pow9_eq_pow3_double m]; omega
    have hs4 : cousinDiamond11Step (12 * 9 ^ m - 2) = ur := by
      rw [d11_eq_d9_of_not_cone1211 _ (not_cone1211_of_even _ (by omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (12 * 9 ^ m - 2) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h9m9 : 9 ^ m % 9 = 0 := by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
      rw [cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) (by omega)]
      dsimp only [ur]; omega
    have hsu : cousinDiamond11Step ur = wr := by
      rw [d11_eq_d9_of_not_cone1211 ur (not_cone1211_six_mul_pow9_sub1 m),
          cousinDiamond9Step_eq_d8_of_not_cone10 ur (not_cone10_six_mul_pow9_sub1 m),
          cousinDiamond8Step_eq_d7_of_not_cone9 ur (not_cone9_six_mul_pow9_sub1 m),
          cousinDiamond7Step_eq_d6_of_not_cone8 ur (not_cone8_six_mul_pow9_sub1 m),
          cousinDiamond6Step_eq_d5_of_not_cone7 ur (not_cone7_six_mul_pow9_sub1 m),
          cousinDiamond5Step_eq_d4_of_not_cone6 ur (not_cone6_of_mod16_ne_13 ur (by dsimp only [ur]; omega))]
      have hnc5 : ¬ isDiamond4Cone5 ur := by rintro ⟨_, h32, _, _⟩; dsimp only [ur] at h32; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 ur hnc5]
      have hc3 : core3 (ur + 1) = 2 := by
        rw [show ur + 1 = 2 * (3 * 9 ^ m) by dsimp only [ur]; omega,
            core3_mul2 (3 * 9 ^ m) (by omega),
            core3_mul3 (9 ^ m) (by omega), (pow9_eq_v3Pow_w5 m).2]
      rw [cousinDiamond3Step_of_core3_succ_two_w8 ur (by dsimp only [ur]; omega) (by dsimp only [ur]; omega) hc3]
      dsimp only [ur, wr]; rw [Nat.pow_succ 9 m]; omega
    have hsw : cousinDiamond11Step wr = (9 ^ (m + 1) - 1) / 4 := by
      let q := (9 ^ m - 1) / 8
      have hq_pos : q ≥ 1 := by dsimp only [q]; omega
      have hp9_eq : 9 ^ m = 8 * q + 1 := by dsimp only [q]; omega
      have hwr_eq : wr = 36 * q + 4 := by dsimp only [wr]; rw [Nat.pow_succ 9 m, hp9_eq]; omega
      have hnext_eq : (9 ^ (m + 1) - 1) / 4 = 18 * q + 2 := by rw [Nat.pow_succ 9 m, hp9_eq]; omega
      rw [hwr_eq, hnext_eq,
          d11_eq_d9_of_not_cone1211 _ (not_cone1211_of_even _ (by omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (36 * q + 4) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5,
          cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) (by omega)]
      omega
    change cousinDiamond11Iter (m + 7) (8 * 3 ^ b0 - 7) = 1
    rw [show m + 7 = 4 + 1 + 1 + m + 1 by omega,
        cousinDiamond11Iter_add (4 + 1 + 1 + m) 1,
        cousinDiamond11Iter_add (4 + 1 + 1) m,
        cousinDiamond11Iter_add (4 + 1) 1,
        cousinDiamond11Iter_add 4 1]
    have hi4 : cousinDiamond11Iter 4 (8 * 3 ^ b0 - 7) = ur := by
      simp only [cousinDiamond11Iter, hs1, hs2, hs3, hu_eq, hs4]
    rw [hi4]
    have hiu : cousinDiamond11Iter 1 ur = wr := hsu
    rw [hiu]
    have hiw : cousinDiamond11Iter 1 wr = (9 ^ (m + 1) - 1) / 4 := hsw
    rw [hiw, cousin_diamond11_even9_spine_drain m]
    decide

theorem cousin_diamond11_a0_2_and_4_drain (b0 : Nat) (hb0 : b0 ≥ 3) :
    cousinDiamond11Iter (b0 + 3) (4 * 3 ^ b0 - 7) = 1 ∧
    cousinDiamond11Iter ((b0 - 1) / 2 + 8) (16 * 3 ^ b0 - 7) = 1 := by
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
  have hnc1211_4 : ¬ isDiamond11Cone12 (4 * 3 ^ b0 - 7) ∧ ¬ isDiamond10Cone11 (4 * 3 ^ b0 - 7) := by
    apply not_cone1211_of_mod32_ne_13
    have hdm := (Nat.div_add_mod (3 ^ b0) 8).symm
    rcases h3b0_m8 with h1 | h3 <;> omega
  have hnc1211_16 : ¬ isDiamond11Cone12 (16 * 3 ^ b0 - 7) ∧ ¬ isDiamond10Cone11 (16 * 3 ^ b0 - 7) := by
    apply not_cone1211_of_mod32_ne_13; have ho := pow3_odd_nat_sec8 b0; omega
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
  · have hs1 : cousinDiamond11Step (4 * 3 ^ b0 - 7) = 6 * 3 ^ b0 - 10 := by
      rw [d11_eq_d9_of_not_cone1211 _ hnc1211_4,
          cousinDiamond9Step_eq_d8_of_not_cone10 _ hnc10_4,
          cousinDiamond8Step_eq_d7_of_not_cone9 _ hnc9_4,
          cousinDiamond7Step_eq_d6_of_not_cone8 _ hnc8_4,
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (hnc7_c 4 (by decide)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (hnc6_c 4 (by decide))]
      exact cousin_diamond4_exit_step_general_odd 4 b0 (Or.inl rfl) hb0
    have hs2 : cousinDiamond11Step (6 * 3 ^ b0 - 10) = 2 * 3 ^ b0 - 4 := by
      rw [d11_eq_d9_of_not_cone1211 _ (not_cone1211_of_even _ (by omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (6 * 3 ^ b0 - 10) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 6 * 3 ^ b0 = 18 * 3 ^ (b0 - 1) := by rw [h3b0_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    have hs3 : cousinDiamond11Step (2 * 3 ^ b0 - 4) = 2 * 3 ^ (b0 - 1) - 2 := by
      rw [d11_eq_d9_of_not_cone1211 _ (not_cone1211_of_even _ (by omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (2 * 3 ^ b0 - 4) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 2 * 3 ^ b0 = 18 * 3 ^ (b0 - 2) := by rw [h3b0_sp, h3b1_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    have hs4 : cousinDiamond11Step (2 * 3 ^ (b0 - 1) - 2) = 3 ^ (b0 - 1) - 1 := by
      rw [d11_eq_d9_of_not_cone1211 _ (not_cone1211_of_even _ (by omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
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
        cousinDiamond11Iter_add (4 + (b0 - 2)) 1,
        cousinDiamond11Iter_add 4 (b0 - 2)]
    have hi4 : cousinDiamond11Iter 4 (4 * 3 ^ b0 - 7) = 3 ^ ((b0 - 2) + 1) - 1 := by
      simp only [cousinDiamond11Iter, hs1, hs2, hs3, hs4]
      rw [show b0 - 1 = (b0 - 2) + 1 by omega]
    rw [hi4, cousin_diamond11_pow3_sub1_drain (b0 - 2)]
    decide
  · rcases cousin_diamond11_a0_3_drain b0 hb0 with ⟨ha3_s1, ha3_s2, ha3_s3, ha3⟩
    have hs1 : cousinDiamond11Step (16 * 3 ^ b0 - 7) = 24 * 3 ^ b0 - 10 := by
      rw [d11_eq_d9_of_not_cone1211 _ hnc1211_16,
          cousinDiamond9Step_eq_d8_of_not_cone10 _ hnc10_16,
          cousinDiamond8Step_eq_d7_of_not_cone9 _ hnc9_16,
          cousinDiamond7Step_eq_d6_of_not_cone8 _ hnc8_16,
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (hnc7_c 16 (by decide)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (hnc6_c 16 (by decide))]
      exact cousin_diamond4_exit_step_general_odd 16 b0 (Or.inr (Or.inr rfl)) hb0
    have hs2 : cousinDiamond11Step (24 * 3 ^ b0 - 10) = 8 * 3 ^ b0 - 4 := by
      rw [d11_eq_d9_of_not_cone1211 _ (not_cone1211_of_even _ (by omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (24 * 3 ^ b0 - 10) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 24 * 3 ^ b0 = 18 * (4 * 3 ^ (b0 - 1)) := by rw [h3b0_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    have hs3 : cousinDiamond11Step (8 * 3 ^ b0 - 4) = 8 * 3 ^ (b0 - 1) - 2 := by
      rw [d11_eq_d9_of_not_cone1211 _ (not_cone1211_of_even _ (by omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (8 * 3 ^ b0 - 4) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 8 * 3 ^ b0 = 18 * (4 * 3 ^ (b0 - 2)) := by rw [h3b0_sp, h3b1_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    have hs4 : cousinDiamond11Step (8 * 3 ^ (b0 - 1) - 2) = 4 * 3 ^ (b0 - 1) - 2 := by
      rw [d11_eq_d9_of_not_cone1211 _ (not_cone1211_of_even _ (by omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
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
        cousinDiamond11Iter_add 3 ((b0 - 1) / 2 + 4)] at ha3
    have hi3 : cousinDiamond11Iter 3 (8 * 3 ^ b0 - 7) = 4 * 3 ^ (b0 - 1) - 2 := by
      simp only [cousinDiamond11Iter, ha3_s1, ha3_s2, ha3_s3]
    rw [hi3] at ha3
    rw [show (b0 - 1) / 2 + 8 = 4 + ((b0 - 1) / 2 + 4) by omega,
        cousinDiamond11Iter_add 4 ((b0 - 1) / 2 + 4)]
    have hi4 : cousinDiamond11Iter 4 (16 * 3 ^ b0 - 7) = 4 * 3 ^ (b0 - 1) - 2 := by
      simp only [cousinDiamond11Iter, hs1, hs2, hs3, hs4]
    rw [hi4]
    exact ha3

theorem cousin_diamond11_cone4_return_aux (x : Nat) (hc4 : isDiamond3Cone4 x) :
    ∃ k : Nat, k ≤ cousinDiamond2Phi x ∧ cousinDiamond11Iter k x = 1 := by
  rcases cousin_diamond3_cone4_reaches_one_exact x hc4 with ⟨r, hr_ge3, hE, _, hphi_ge⟩
  refine ⟨3 * r + 4, hphi_ge, ?_⟩
  have hnc1211_x : ¬ isDiamond11Cone12 x ∧ ¬ isDiamond10Cone11 x := not_cone1211_of_mod8_ne_5 x (by have h8 := hc4.2.1; omega)
  have hnc10_x : ¬ isDiamond9Cone10 x := not_cone10_of_mod8_ne_5 x (by have h8 := hc4.2.1; omega)
  have hnc9_x : ¬ isDiamond8Cone9 x := not_cone9_of_mod8_ne_5 x (by have h8 := hc4.2.1; omega)
  have hnc8_x : ¬ isDiamond7Cone8 x := not_cone8_of_mod8_ne_5 x (by have h8 := hc4.2.1; omega)
  have hnc7_x : ¬ isDiamond6Cone7 x := not_cone7_of_mod8_ne_5 x (by have h8 := hc4.2.1; omega)
  have hnc6_x : ¬ isDiamond5Cone6 x := by rintro ⟨_, h256, _, _⟩; have h8 := hc4.2.1; omega
  have hx_odd : x % 2 = 1 := by have h8 := hc4.2.1; omega
  have hs1 : cousinDiamond11Step x = 2 ^ (2 * r + 1) - 1 := by
    rw [d11_eq_d9_of_not_cone1211 x hnc1211_x,
        cousinDiamond9Step_eq_d8_of_not_cone10 x hnc10_x,
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
  have hglide : cousinDiamond11Iter (2 * r) (2 ^ (2 * r + 1) - 1) = zr := by
    have hf := cousin_diamond11_mersenne_scaled (2 * r) (2 * r + 1) 1 (by omega) (by decide)
    simp only [Nat.mul_one, show 2 * r + 1 - 2 * r = 1 by omega, Nat.pow_one] at hf
    rw [hf, ← pow9_eq_pow3_double r, Nat.mul_comm]
  have hp9_ge729 : 9 ^ r ≥ 729 := by simpa using nat_pow_mono_exp_pos 9 3 r (by decide) hr_ge3
  have hp9_m8 : 9 ^ r % 8 = 1 := pow9_mod8_eq_one_w5 r
  have hsz : cousinDiamond11Step zr = yr := by
    rw [d11_eq_d9_of_not_cone1211 zr (not_cone1211_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
        cousinDiamond9Step_eq_d8_of_not_cone10 zr (not_cone10_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
        cousinDiamond8Step_eq_d7_of_not_cone9 zr (not_cone9_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
        cousinDiamond7Step_eq_d6_of_not_cone8 zr (not_cone8_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
        cousinDiamond6Step_eq_d5_of_not_cone7 zr (not_cone7_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
        cousinDiamond5Step_eq_d4_of_not_cone6 zr (not_cone6_of_mod16_ne_13 zr (by dsimp only [zr]; omega))]
    have hnc5 : ¬ isDiamond4Cone5 zr := by rintro ⟨_, h32, _, _⟩; dsimp only [zr] at h32; omega
    rw [cousinDiamond4Step_eq_d3_of_not_cone5 zr hnc5]
    have hc3 : core3 (zr + 1) = 2 := by
      rw [show zr + 1 = 2 * 9 ^ r by dsimp only [zr]; omega,
          core3_mul2 (9 ^ r) (by omega), (pow9_eq_v3Pow_w5 r).2]
    rw [cousinDiamond3Step_of_core3_succ_two_w8 zr (by dsimp only [zr]; omega) (by dsimp only [zr]; omega) hc3]
    dsimp only [zr, yr]; omega
  have hsy : cousinDiamond11Step yr = (9 ^ (r + 1) - 1) / 4 := by
    have hyr_m3 : yr % 3 = 1 := by
      have hm3 : 9 ^ r % 3 = 0 := by rw [show r = (r - 1) + 1 by omega, Nat.pow_succ]; omega
      dsimp only [yr]; omega
    rw [d11_eq_d9_of_not_cone1211 yr (not_cone1211_of_mod3_ne_2 yr (by omega)),
        cousinDiamond9Step_eq_d8_of_not_cone10 yr (not_cone10_of_mod3_ne_2 yr (by omega)),
        cousinDiamond8Step_eq_d7_of_not_cone9 yr (not_cone9_of_mod3_ne_2 yr (by omega)),
        cousinDiamond7Step_eq_d6_of_not_cone8 yr (not_cone8_of_mod3_ne_2 yr (by omega)),
        cousinDiamond6Step_eq_d5_of_not_cone7 yr (not_cone7_of_mod9_ne_8 yr (by omega)),
        cousinDiamond5Step_eq_d4_of_not_cone6 yr (not_cone6_of_mod9_ne_8 yr (by omega))]
    have hnc5 : ¬ isDiamond4Cone5 yr := by rintro ⟨_, _, hm3, _⟩; omega
    rw [cousinDiamond4Step_eq_d3_of_not_cone5 yr hnc5]
    have hc3_2 : core3 (2 * yr + 1) = 1 := by
      rw [show 2 * yr + 1 = 3 * 9 ^ r by dsimp only [yr]; omega,
          core3_mul3 (9 ^ r) (by omega), (pow9_eq_v3Pow_w5 r).2]
    have hc3_1 : core3 (yr + 1) ≠ 2 := by
      rw [core3_not_div3 (yr + 1) (by omega)]; dsimp only [yr]; omega
    have hnc4 : ¬ isDiamond3Cone4 yr := by
      rintro ⟨_, _, hc2⟩
      rcases eq_pow2_of_core2_eq_one (3 * yr + 5) (by dsimp only [yr]; omega) hc2 with ⟨M0, hM0⟩
      have h9_eq : 9 ^ (r + 1) + 7 = 2 ^ (M0 + 1) := by
        have h2mul : 2 * (3 * yr + 5) = 9 ^ (r + 1) + 7 := by
          rw [Nat.pow_succ 9 r, Nat.mul_comm (9 ^ r) 9]; dsimp only [yr]; omega
        rw [← h2mul, hM0, Nat.pow_succ 2 M0, Nat.mul_comm]
      exact pow9_succ_add_seven_ne_pow2 r (M0 + 1) (by omega) h9_eq
    rw [cousinDiamond3Step_odd_half_w8 yr (by dsimp only [yr]; omega) hnc4 hc3_2 hc3_1]
    dsimp only [yr]; rw [Nat.pow_succ 9 r]; omega
  rw [show 3 * r + 4 = 1 + 2 * r + 1 + 1 + r + 1 by omega,
      cousinDiamond11Iter_add (1 + 2 * r + 1 + 1 + r) 1,
      cousinDiamond11Iter_add (1 + 2 * r + 1 + 1) r,
      cousinDiamond11Iter_add (1 + 2 * r + 1) 1,
      cousinDiamond11Iter_add (1 + 2 * r) 1,
      cousinDiamond11Iter_add 1 (2 * r)]
  have hi1 : cousinDiamond11Iter 1 x = 2 ^ (2 * r + 1) - 1 := hs1
  rw [hi1, hglide]
  have hiz : cousinDiamond11Iter 1 zr = yr := hsz
  rw [hiz]
  have hiy : cousinDiamond11Iter 1 yr = (9 ^ (r + 1) - 1) / 4 := hsy
  rw [hiy, cousin_diamond11_even9_spine_drain r]
  decide

theorem cousin_diamond11_cone5_return_aux (x : Nat) (hc5 : isDiamond4Cone5 x) :
    ∃ (a b k : Nat),
      a ≥ 5 ∧ b ≥ 1 ∧ x + 7 = 2 ^ a * 3 ^ b ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond11Iter k x = 1 := by
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
  have hb0_ge3 : b0 ≥ 3 := by dsimp only [b0, q_c]; omega
  have ha0_234 : a0 = 2 ∨ a0 = 3 ∨ a0 = 4 := by dsimp only [a0, q_c]; omega
  have hclimb := cousin_diamond11_cone5_two_step_climb q_c a b (by dsimp only [q_c]; omega) hb1
  rw [← hx_eq] at hclimb
  change cousinDiamond11Iter (2 * q_c) x = 2 ^ a0 * 3 ^ b0 - 7 at hclimb
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
    dsimp only [q_c, b0] at hex ⊢
    omega
  have hd_3 := (cousin_diamond11_a0_3_drain b0 hb0_ge3).2.2.2
  rcases cousin_diamond11_a0_2_and_4_drain b0 hb0_ge3 with ⟨hd_2, hd_4⟩
  rcases ha0_234 with ha2 | ha3 | ha4
  · have hkx := hbound_x (b0 + 3) (by omega)
    refine ⟨a, b, 2 * q_c + (b0 + 3), ha5, hb1, hmul.symm, hkx,
      Nat.le_trans (by omega : 2 * q_c + (b0 + 3) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond11Iter_add (2 * q_c) (b0 + 3) x, hclimb, ha2]; exact hd_2
  · have hkx := hbound_x ((b0 - 1) / 2 + 7) (by omega)
    refine ⟨a, b, 2 * q_c + ((b0 - 1) / 2 + 7), ha5, hb1, hmul.symm, hkx,
      Nat.le_trans (by omega : 2 * q_c + ((b0 - 1) / 2 + 7) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond11Iter_add (2 * q_c) ((b0 - 1) / 2 + 7) x, hclimb, ha3]; exact hd_3
  · have hkx := hbound_x ((b0 - 1) / 2 + 8) (by omega)
    refine ⟨a, b, 2 * q_c + ((b0 - 1) / 2 + 8), ha5, hb1, hmul.symm, hkx,
      Nat.le_trans (by omega : 2 * q_c + ((b0 - 1) / 2 + 8) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond11Iter_add (2 * q_c) ((b0 - 1) / 2 + 8) x, hclimb, ha4]; exact hd_4

theorem cousin_diamond11_cone6_return_aux (x : Nat) (hc6 : isDiamond5Cone6 x) :
    ∃ (e f k : Nat),
      e ≥ 8 ∧ f ≥ 2 ∧ x + 19 = 2 ^ e * 3 ^ f ∧
      cousinDiamond11Step x = 2 ^ (e - 3) * 3 ^ (f + 1) - 7 ∧
      isDiamond4Cone5 (cousinDiamond11Step x) ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond11Iter k x = 1 := by
  have hnc1211_x : ¬ isDiamond11Cone12 x ∧ ¬ isDiamond10Cone11 x :=
    not_cone1211_of_mod256_ne_205 x (by rw [hc6.2.1]; decide)
  have hx_ge : x ≥ 2285 := hc6.1
  rcases (cousin_diamond9_cones4to10_exact_return.2.2.1 x hc6) with
    ⟨e, f, _, he8, hf2, hmul, hd9_x, _, _, _, _⟩
  let y := 2 ^ (e - 3) * 3 ^ (f + 1) - 7
  have hstep_x : cousinDiamond11Step x = y := by
    rw [d11_eq_d9_of_not_cone1211 x hnc1211_x]; exact hd9_x
  have hnc10_x : ¬ isDiamond9Cone10 x :=
    not_cone10_of_mod256_ne_205 x (by rw [hc6.2.1]; decide)
  have hnc9_x : ¬ isDiamond8Cone9 x :=
    not_cone9_of_mod256_ne_141 x (by rw [hc6.2.1]; decide)
  have hnc8_x : ¬ isDiamond7Cone8 x :=
    not_cone8_of_mod256_ne_213 x (by rw [hc6.2.1]; decide)
  have hnc7_x : ¬ isDiamond6Cone7 x :=
    not_cone7_of_mod256_ne_213 x (by rw [hc6.2.1]; decide)
  have hy_step : y = (3 * x + 1) / 8 :=
    hd9_x.symm.trans (by
      rw [cousinDiamond9Step_eq_d8_of_not_cone10 x hnc10_x,
          cousinDiamond8Step_eq_d7_of_not_cone9 x hnc9_x,
          cousinDiamond7Step_eq_d6_of_not_cone8 x hnc8_x,
          cousinDiamond6Step_eq_d5_of_not_cone7 x hnc7_x]
      unfold cousinDiamond5Step; simp [hc6])
  clear hc6 hnc1211_x hnc10_x hnc9_x hnc8_x hnc7_x hd9_x
  have hc5_y : isDiamond4Cone5 y :=
    isDiamond4Cone5_of_pow2_pow3 (e - 3) (f + 1) (by omega) (by omega)
  rcases cousin_diamond11_cone5_return_aux y hc5_y with ⟨_, _, ky, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hdiv : y * 8 ≤ 3 * x + 1 := by rw [hy_step]; exact Nat.div_mul_le_self (3 * x + 1) 8
    clear hy_step hmul hstep_x hc5_y hky_1; omega
  have h1ky_x : 1 + ky ≤ x := by clear hy_step hmul hstep_x hc5_y hky_1; omega
  have h1ky_phi : 1 + ky ≤ cousinDiamond2Phi x :=
    Nat.le_trans (by clear hy_step hmul hstep_x hc5_y hky_1; omega : 1 + ky ≤ x + 1) (cousinDiamond2Phi_ge_succ x)
  refine ⟨e, f, 1 + ky, he8, hf2, hmul, hstep_x, ?_, h1ky_x, h1ky_phi, ?_⟩
  · rw [hstep_x]; exact hc5_y
  · rw [cousinDiamond11Iter_add 1 ky x]
    have hi1 : cousinDiamond11Iter 1 x = y := hstep_x
    rw [hi1]; exact hky_1

theorem cousin_diamond11_cone7_return_aux (x : Nat) (hc7 : isDiamond6Cone7 x) :
    ∃ (g h k : Nat),
      g ≥ 15 ∧ h ≥ 2 ∧ x + 811 = 2 ^ g * 3 ^ h ∧
      cousinDiamond11Step x = 2 ^ (g - 7) * 3 ^ (h + 1) - 19 ∧
      isDiamond5Cone6 (cousinDiamond11Step x) ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond11Iter k x = 1 := by
  have hnc1211_x : ¬ isDiamond11Cone12 x ∧ ¬ isDiamond10Cone11 x := by
    apply not_cone1211_of_mod32_ne_13
    have h32 : x % 32 = 31957 % 32 := by
      have h := congrArg (· % 32) hc7.2.1
      rwa [Nat.mod_mod_of_dvd x (by decide : 32 ∣ 32768)] at h
    rw [h32]; decide
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
  rcases (cousin_diamond9_cones4to10_exact_return.2.2.2.1 x hc7) with
    ⟨g, h, _, hg15, hh2, hmul, hd9_x, _, _, _, _⟩
  let y := 2 ^ (g - 7) * 3 ^ (h + 1) - 19
  have hstep_x : cousinDiamond11Step x = y := by
    rw [d11_eq_d9_of_not_cone1211 x hnc1211_x]; exact hd9_x
  have hy_step : y = (3 * x + 1) / 128 :=
    hd9_x.symm.trans (by
      rw [cousinDiamond9Step_eq_d8_of_not_cone10 x hnc10_x,
          cousinDiamond8Step_eq_d7_of_not_cone9 x hnc9_x,
          cousinDiamond7Step_eq_d6_of_not_cone8 x hnc8_x]
      unfold cousinDiamond6Step; simp [hc7])
  clear hc7 hnc1211_x hnc10_x hnc9_x hnc8_x hd9_x
  have hc6_y : isDiamond5Cone6 y :=
    isDiamond5Cone6_of_pow2_pow3 (g - 7) (h + 1) (by omega) (by omega)
  rcases cousin_diamond11_cone6_return_aux y hc6_y with ⟨_, _, ky, _, _, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hdiv : y * 128 ≤ 3 * x + 1 := by rw [hy_step]; exact Nat.div_mul_le_self (3 * x + 1) 128
    clear hy_step hmul hstep_x hc6_y hky_1; omega
  have h1ky_x : 1 + ky ≤ x := by clear hy_step hmul hstep_x hc6_y hky_1; omega
  have h1ky_phi : 1 + ky ≤ cousinDiamond2Phi x :=
    Nat.le_trans (by clear hy_step hmul hstep_x hc6_y hky_1; omega : 1 + ky ≤ x + 1) (cousinDiamond2Phi_ge_succ x)
  refine ⟨g, h, 1 + ky, hg15, hh2, hmul, hstep_x, ?_, h1ky_x, h1ky_phi, ?_⟩
  · rw [hstep_x]; exact hc6_y
  · rw [cousinDiamond11Iter_add 1 ky x]
    have hi1 : cousinDiamond11Iter 1 x = y := hstep_x
    rw [hi1]; exact hky_1

theorem cousin_diamond11_cone8_return_aux (x : Nat) (hc8 : isDiamond7Cone8 x) :
    ∃ (u v k : Nat),
      u ≥ 22 ∧ v ≥ 1 ∧ x + 34603 = 2 ^ u * 3 ^ v ∧
      cousinDiamond11Step x = 2 ^ (u - 7) * 3 ^ (v + 1) - 811 ∧
      isDiamond6Cone7 (cousinDiamond11Step x) ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond11Iter k x = 1 := by
  have hnc1211_x : ¬ isDiamond11Cone12 x ∧ ¬ isDiamond10Cone11 x :=
    not_cone1211_of_mod32_ne_13 x (by have h := mod32_of_cone8 x hc8; omega)
  have hnc10_x : ¬ isDiamond9Cone10 x :=
    not_cone10_of_mod32_ne_13 x (by have h := mod32_of_cone8 x hc8; omega)
  have hnc9_x : ¬ isDiamond8Cone9 x :=
    not_cone9_of_mod32_ne_13 x (by have h := mod32_of_cone8 x hc8; omega)
  have hx_ge : x ≥ 12548309 := hc8.1
  rcases (cousin_diamond9_cones4to10_exact_return.2.2.2.2.1 x hc8) with
    ⟨u, v, _, hu22, hv1, hmul, hd9_x, _, _, _, _⟩
  let y := 2 ^ (u - 7) * 3 ^ (v + 1) - 811
  have hstep_x : cousinDiamond11Step x = y := by
    rw [d11_eq_d9_of_not_cone1211 x hnc1211_x]; exact hd9_x
  have hy_step : y = (3 * x + 1) / 128 :=
    hd9_x.symm.trans (by
      rw [cousinDiamond9Step_eq_d8_of_not_cone10 x hnc10_x,
          cousinDiamond8Step_eq_d7_of_not_cone9 x hnc9_x]
      unfold cousinDiamond7Step; simp [hc8])
  clear hc8 hnc1211_x hnc10_x hnc9_x hd9_x
  have hc7_y : isDiamond6Cone7 y :=
    isDiamond6Cone7_of_pow2_pow3 (u - 7) (v + 1) (by omega) (by omega)
  rcases cousin_diamond11_cone7_return_aux y hc7_y with ⟨_, _, ky, _, _, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hdiv : y * 128 ≤ 3 * x + 1 := by rw [hy_step]; exact Nat.div_mul_le_self (3 * x + 1) 128
    clear hy_step hmul hstep_x hc7_y hky_1; omega
  have h1ky_x : 1 + ky ≤ x := by clear hy_step hmul hstep_x hc7_y hky_1; omega
  have h1ky_phi : 1 + ky ≤ cousinDiamond2Phi x :=
    Nat.le_trans (by clear hy_step hmul hstep_x hc7_y hky_1; omega : 1 + ky ≤ x + 1) (cousinDiamond2Phi_ge_succ x)
  refine ⟨u, v, 1 + ky, hu22, hv1, hmul, hstep_x, ?_, h1ky_x, h1ky_phi, ?_⟩
  · rw [hstep_x]; exact hc7_y
  · rw [cousinDiamond11Iter_add 1 ky x]
    have hi1 : cousinDiamond11Iter 1 x = y := hstep_x
    rw [hi1]; exact hky_1

theorem cousin_diamond11_cone9_return_aux (x : Nat) (hc9 : isDiamond8Cone9 x) :
    ∃ (w z k : Nat),
      w ≥ 25 ∧ z ≥ 1 ∧ x + 92275 = 2 ^ w * 3 ^ z ∧
      cousinDiamond11Step x = 2 ^ (w - 3) * 3 ^ (z + 1) - 34603 ∧
      isDiamond7Cone8 (cousinDiamond11Step x) ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond11Iter k x = 1 := by
  have hnc1211_x : ¬ isDiamond11Cone12 x ∧ ¬ isDiamond10Cone11 x :=
    not_cone1211_of_mod256_ne_205 x (by rw [mod256_of_cone9 x hc9]; decide)
  have hnc10_x : ¬ isDiamond9Cone10 x :=
    not_cone10_of_mod256_ne_205 x (by rw [mod256_of_cone9 x hc9]; decide)
  have hx_ge : x ≥ 100571021 := hc9.1
  rcases (cousin_diamond9_cones4to10_exact_return.2.2.2.2.2.1 x hc9) with
    ⟨w, z, _, hw25, hz1, hmul, hd9_x, _, _, _, _⟩
  let y := 2 ^ (w - 3) * 3 ^ (z + 1) - 34603
  have hstep_x : cousinDiamond11Step x = y := by
    rw [d11_eq_d9_of_not_cone1211 x hnc1211_x]; exact hd9_x
  have hy_step : y = (3 * x + 1) / 8 :=
    hd9_x.symm.trans (by
      rw [cousinDiamond9Step_eq_d8_of_not_cone10 x hnc10_x]
      unfold cousinDiamond8Step; simp [hc9])
  clear hc9 hnc1211_x hnc10_x hd9_x
  have hc8_y : isDiamond7Cone8 y :=
    isDiamond7Cone8_of_pow2_pow3 (w - 3) (z + 1) (by omega) (by omega)
  rcases cousin_diamond11_cone8_return_aux y hc8_y with ⟨_, _, ky, _, _, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hdiv : y * 8 ≤ 3 * x + 1 := by rw [hy_step]; exact Nat.div_mul_le_self (3 * x + 1) 8
    clear hy_step hmul hstep_x hc8_y hky_1; omega
  have h1ky_x : 1 + ky ≤ x := by clear hy_step hmul hstep_x hc8_y hky_1; omega
  have h1ky_phi : 1 + ky ≤ cousinDiamond2Phi x :=
    Nat.le_trans (by clear hy_step hmul hstep_x hc8_y hky_1; omega : 1 + ky ≤ x + 1) (cousinDiamond2Phi_ge_succ x)
  refine ⟨w, z, 1 + ky, hw25, hz1, hmul, hstep_x, ?_, h1ky_x, h1ky_phi, ?_⟩
  · rw [hstep_x]; exact hc8_y
  · rw [cousinDiamond11Iter_add 1 ky x]
    have hi1 : cousinDiamond11Iter 1 x = y := hstep_x
    rw [hi1]; exact hky_1

theorem cousin_diamond11_cone10_return_aux (x : Nat) (hc10 : isDiamond9Cone10 x) :
    ∃ (p q k : Nat),
      p ≥ 28 ∧ q ≥ 1 ∧ x + 246067 = 2 ^ p * 3 ^ q ∧
      cousinDiamond11Step x = 2 ^ (p - 3) * 3 ^ (q + 1) - 92275 ∧
      isDiamond8Cone9 (cousinDiamond11Step x) ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond11Iter k x = 1 := by
  have hnc1211_x : ¬ isDiamond11Cone12 x ∧ ¬ isDiamond10Cone11 x :=
    not_cone1211_of_cone10 x hc10
  have hx_ge : x ≥ 805060301 := hc10.1
  rcases (cousin_diamond9_cones4to10_exact_return.2.2.2.2.2.2 x hc10) with
    ⟨p, q, _, hp28, hq1, hmul, hd9_x, _, _, _, _⟩
  let y := 2 ^ (p - 3) * 3 ^ (q + 1) - 92275
  have hstep_x : cousinDiamond11Step x = y := by
    rw [d11_eq_d9_of_not_cone1211 x hnc1211_x]; exact hd9_x
  have hy_step : y = (3 * x + 1) / 8 :=
    hd9_x.symm.trans (by unfold cousinDiamond9Step; simp [hc10])
  clear hc10 hnc1211_x hd9_x
  have hc9_y : isDiamond8Cone9 y :=
    isDiamond8Cone9_of_pow2_pow3 (p - 3) (q + 1) (by omega) (by omega)
  rcases cousin_diamond11_cone9_return_aux y hc9_y with ⟨_, _, ky, _, _, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hdiv : y * 8 ≤ 3 * x + 1 := by rw [hy_step]; exact Nat.div_mul_le_self (3 * x + 1) 8
    clear hy_step hmul hstep_x hc9_y hky_1; omega
  have h1ky_x : 1 + ky ≤ x := by clear hy_step hmul hstep_x hc9_y hky_1; omega
  have h1ky_phi : 1 + ky ≤ cousinDiamond2Phi x :=
    Nat.le_trans (by clear hy_step hmul hstep_x hc9_y hky_1; omega : 1 + ky ≤ x + 1) (cousinDiamond2Phi_ge_succ x)
  refine ⟨p, q, 1 + ky, hp28, hq1, hmul, hstep_x, ?_, h1ky_x, h1ky_phi, ?_⟩
  · rw [hstep_x]; exact hc9_y
  · rw [cousinDiamond11Iter_add 1 ky x]
    have hi1 : cousinDiamond11Iter 1 x = y := hstep_x
    rw [hi1]; exact hky_1


theorem cousin_diamond11_cone11_return_aux (x : Nat) (hc11 : isDiamond10Cone11 x) :
    ∃ (r s k : Nat),
      r ≥ 31 ∧ s ≥ 1 ∧ x + 656179 = 2 ^ r * 3 ^ s ∧
      cousinDiamond11Step x = 2 ^ (r - 3) * 3 ^ (s + 1) - 246067 ∧
      isDiamond9Cone10 (cousinDiamond11Step x) ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond11Iter k x = 1 := by
  have hnc12_x : ¬ isDiamond11Cone12 x :=
    not_cone12_of_mod2b_ne x (by rw [hc11.2.1]; decide)
  have hx_ge : x ≥ 6441794765 := hc11.1
  rcases (cousin_diamond10_cones4to11_exact_return.2.2.2.2.2.2.2 x hc11) with
    ⟨r, s, _, hr31, hs1, hmul, hd10_x, _, _, _, _⟩
  let y := 2 ^ (r - 3) * 3 ^ (s + 1) - 246067
  have hstep_x : cousinDiamond11Step x = y := by
    rw [cousinDiamond11Step_eq_d10_of_not_cone12 x hnc12_x]; exact hd10_x
  have hy_step : y = (3 * x + 1) / 8 :=
    hd10_x.symm.trans (by unfold cousinDiamond10Step; simp [hc11])
  clear hc11 hnc12_x hd10_x
  have hc10_y : isDiamond9Cone10 y :=
    isDiamond9Cone10_of_pow2_pow3 (r - 3) (s + 1) (by omega) (by omega)
  rcases cousin_diamond11_cone10_return_aux y hc10_y with ⟨_, _, ky, _, _, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hdiv : y * 8 ≤ 3 * x + 1 := by rw [hy_step]; exact Nat.div_mul_le_self (3 * x + 1) 8
    clear hy_step hmul hstep_x hc10_y hky_1; omega
  have h1ky_x : 1 + ky ≤ x := by clear hy_step hmul hstep_x hc10_y hky_1; omega
  have h1ky_phi : 1 + ky ≤ cousinDiamond2Phi x :=
    Nat.le_trans (by clear hy_step hmul hstep_x hc10_y hky_1; omega : 1 + ky ≤ x + 1) (cousinDiamond2Phi_ge_succ x)
  refine ⟨r, s, 1 + ky, hr31, hs1, hmul, hstep_x, ?_, h1ky_x, h1ky_phi, ?_⟩
  · rw [hstep_x]; exact hc10_y
  · rw [cousinDiamond11Iter_add 1 ky x]
    have hi1 : cousinDiamond11Iter 1 x = y := hstep_x
    rw [hi1]; exact hky_1

/--
  Theorem W14.3f (`cousin_diamond11_cones4to12_exact_return`, `zero custom axioms`):
  Exact 9-Tier `ω^9` Multi-Block Return Across Cones 4, 5, 6, 7, 8, 9, 10, 11, AND 12 of `T_diamond11`:
  1–8. Every `x` in Cone 4, 5, 6, 7, 8, 9, 10, or 11 reaches `1` in `k ≤ cousinDiamond2Phi x` steps!
  9. Every `x` in Cone 12 (`isDiamond11Cone12 x`) has `x + 1749811 = 2 ^ m * 3 ^ n` (`m ≥ 34, n ≥ 1`),
     steps in 1 genuine `v_2(3x + 1) = 3` jump `(3 * x + 1) / 8` directly into the Cone-11 state
     `y = 2 ^ (m - 3) * 3 ^ (n + 1) - 656179`, and reaches `1` in `1 + k_y ≤ x` (`≤ cousinDiamond2Phi x`) steps!
-/
theorem cousin_diamond11_cones4to12_exact_return :
    (∀ x : Nat, isDiamond3Cone4 x ->
      ∃ k : Nat, k ≤ cousinDiamond2Phi x ∧ cousinDiamond11Iter k x = 1) ∧
    (∀ x : Nat, isDiamond4Cone5 x ->
      ∃ (a b k : Nat),
        a ≥ 5 ∧ b ≥ 1 ∧ x + 7 = 2 ^ a * 3 ^ b ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond11Iter k x = 1) ∧
    (∀ x : Nat, isDiamond5Cone6 x ->
      ∃ (e f k : Nat),
        e ≥ 8 ∧ f ≥ 2 ∧ x + 19 = 2 ^ e * 3 ^ f ∧
        cousinDiamond11Step x = 2 ^ (e - 3) * 3 ^ (f + 1) - 7 ∧
        isDiamond4Cone5 (cousinDiamond11Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond11Iter k x = 1) ∧
    (∀ x : Nat, isDiamond6Cone7 x ->
      ∃ (g h k : Nat),
        g ≥ 15 ∧ h ≥ 2 ∧ x + 811 = 2 ^ g * 3 ^ h ∧
        cousinDiamond11Step x = 2 ^ (g - 7) * 3 ^ (h + 1) - 19 ∧
        isDiamond5Cone6 (cousinDiamond11Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond11Iter k x = 1) ∧
    (∀ x : Nat, isDiamond7Cone8 x ->
      ∃ (u v k : Nat),
        u ≥ 22 ∧ v ≥ 1 ∧ x + 34603 = 2 ^ u * 3 ^ v ∧
        cousinDiamond11Step x = 2 ^ (u - 7) * 3 ^ (v + 1) - 811 ∧
        isDiamond6Cone7 (cousinDiamond11Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond11Iter k x = 1) ∧
    (∀ x : Nat, isDiamond8Cone9 x ->
      ∃ (w z k : Nat),
        w ≥ 25 ∧ z ≥ 1 ∧ x + 92275 = 2 ^ w * 3 ^ z ∧
        cousinDiamond11Step x = 2 ^ (w - 3) * 3 ^ (z + 1) - 34603 ∧
        isDiamond7Cone8 (cousinDiamond11Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond11Iter k x = 1) ∧
    (∀ x : Nat, isDiamond9Cone10 x ->
      ∃ (p q k : Nat),
        p ≥ 28 ∧ q ≥ 1 ∧ x + 246067 = 2 ^ p * 3 ^ q ∧
        cousinDiamond11Step x = 2 ^ (p - 3) * 3 ^ (q + 1) - 92275 ∧
        isDiamond8Cone9 (cousinDiamond11Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond11Iter k x = 1) ∧
    (∀ x : Nat, isDiamond10Cone11 x ->
      ∃ (r s k : Nat),
        r ≥ 31 ∧ s ≥ 1 ∧ x + 656179 = 2 ^ r * 3 ^ s ∧
        cousinDiamond11Step x = 2 ^ (r - 3) * 3 ^ (s + 1) - 246067 ∧
        isDiamond9Cone10 (cousinDiamond11Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond11Iter k x = 1) ∧
    (∀ x : Nat, isDiamond11Cone12 x ->
      ∃ (m n k : Nat),
        m ≥ 34 ∧ n ≥ 1 ∧ x + 1749811 = 2 ^ m * 3 ^ n ∧
        cousinDiamond11Step x = 2 ^ (m - 3) * 3 ^ (n + 1) - 656179 ∧
        isDiamond10Cone11 (cousinDiamond11Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond11Iter k x = 1) := by
  refine ⟨cousin_diamond11_cone4_return_aux,
          cousin_diamond11_cone5_return_aux,
          cousin_diamond11_cone6_return_aux,
          cousin_diamond11_cone7_return_aux,
          cousin_diamond11_cone8_return_aux,
          cousin_diamond11_cone9_return_aux,
          cousin_diamond11_cone10_return_aux,
          cousin_diamond11_cone11_return_aux, ?_⟩
  intro x hc12
  have hraw_step : cousinDiamond11Step x = (3 * x + 1) / 8 := by
    unfold cousinDiamond11Step; simp only [hc12, ite_true]
  rcases hc12 with ⟨hx_ge, hx17b, hx3, hg1⟩
  have hdvd17b : 17179869184 ∣ (x + 1749811) :=
    Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, hx17b])
  clear hx17b
  rcases (⟨1749811 + x, rfl⟩ : ∃ N : Nat, N = 1749811 + x) with ⟨N, hN_def⟩
  rw [← hN_def] at hg1
  have hN_pos : N > 0 := by clear hraw_step hdvd17b hx3 hg1; omega
  rcases decomp_2_3_exact N hN_pos with ⟨_, _, _, _, _, hmul⟩
  rw [hg1, Nat.mul_one] at hmul
  rcases eq_pow2_of_v2Pow_aux N N hN_pos (Nat.le_refl _) with ⟨m, hm⟩
  rcases eq_pow3_of_v3Pow_aux N N hN_pos (Nat.le_refl _) with ⟨n, hn⟩
  rw [hm, hn] at hmul
  have hmul_comm : x + 1749811 = 2 ^ m * 3 ^ n := by
    rw [Nat.add_comm x 1749811, ← hN_def, ← hmul]
  clear hg1 hm hn hN_def hmul hN_pos
  have hm34 : m ≥ 34 := by
    by_cases hlt : m < 34
    · exfalso
      have h17b_sp : 17179869184 = 2 ^ (m + 1) * 2 ^ (33 - m) := by
        have hsum34 : m + 1 + (33 - m) = 34 := by clear hraw_step hx_ge hx3 hdvd17b hmul_comm; omega
        rw [← Nat.pow_add 2 (m + 1) (33 - m), hsum34]
      rcases hdvd17b with ⟨c, hc⟩
      rw [hmul_comm, h17b_sp, Nat.mul_assoc (2 ^ (m + 1)),
          Nat.pow_succ 2 m, Nat.mul_assoc (2 ^ m) 2] at hc
      have h3n_ev : 3 ^ n = 2 * (2 ^ (33 - m) * c) :=
        nat_mul_left_cancel_pos (2 ^ m) _ _ (pow2_pos_nat m) hc
      have ho := pow3_odd_nat_sec8 n
      rw [h3n_ev, Nat.mul_mod_right] at ho
      cases ho
    · clear hraw_step hx_ge hx3 hdvd17b hmul_comm; omega
  clear hdvd17b
  have hn1 : n ≥ 1 := by
    cases n with
    | zero =>
      rw [Nat.pow_zero, Nat.mul_one] at hmul_comm
      exact False.elim (pow2_mod3_nonzero_w5 m (by rw [← hmul_comm, Nat.add_mod, hx3]))
    | succ _ => clear hraw_step hx_ge hx3 hmul_comm hm34; omega
  clear hx3
  let y := 2 ^ (m - 3) * 3 ^ (n + 1) - 656179
  have hstep_x : cousinDiamond11Step x = y := by
    rw [hraw_step]
    dsimp only [y]
    have hp8 : 2 ^ m = 8 * 2 ^ (m - 3) := by
      have hm_sp : m = 3 + (m - 3) := by clear hraw_step hx_ge hmul_comm hn1; omega
      conv => lhs; rw [hm_sp]; rw [Nat.pow_add]
    have hprod_pos : 2 ^ (m - 3) * 3 ^ n ≥ 2147483648 * 3 := by
      have h1 : 2147483648 ≤ 2 ^ (m - 3) := by
        have hc : (2 : Nat) ^ 31 = 2147483648 := by decide
        have h31 : 31 ≤ m - 3 := by clear hraw_step hx_ge hmul_comm hn1 hp8; omega
        rw [← hc]; exact pow2_mono_nat h31
      have h2 : 3 ≤ 3 ^ n := by simpa using nat_pow_mono_exp_pos 3 1 n (by decide) hn1
      simpa using Nat.mul_le_mul h1 h2
    have h3_eq : 2 ^ (m - 3) * 3 ^ (n + 1) = 3 * (2 ^ (m - 3) * 3 ^ n) := by
      rw [Nat.pow_succ 3 n, ← Nat.mul_assoc, Nat.mul_comm _ 3]
    rw [h3_eq]
    have hx8 : x + 1749811 = 8 * (2 ^ (m - 3) * 3 ^ n) := by
      rw [hmul_comm, hp8, Nat.mul_assoc]
    have h3x1 : 3 * x + 1 = (3 * (2 ^ (m - 3) * 3 ^ n) - 656179) * 8 := by
      clear hraw_step hm34 hn1 hp8 h3_eq hmul_comm
      generalize 2 ^ (m - 3) * 3 ^ n = A at hprod_pos hx8 ⊢
      omega
    rw [h3x1]
    exact Nat.mul_div_left _ (by decide : 0 < 8)
  have hc11_y : isDiamond10Cone11 y :=
    isDiamond10Cone11_of_pow2_pow3 (m - 3) (n + 1)
      (by clear hraw_step hx_ge hmul_comm hstep_x; omega)
      (by clear hraw_step hx_ge hmul_comm hstep_x; omega)
  rcases cousin_diamond11_cone11_return_aux y hc11_y with ⟨_, _, ky, _, _, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hstep_eq : y = (3 * x + 1) / 8 := hstep_x.symm.trans hraw_step
    have hdiv : y * 8 ≤ 3 * x + 1 := by rw [hstep_eq]; exact Nat.div_mul_le_self (3 * x + 1) 8
    clear hraw_step hmul_comm hstep_x hc11_y hky_1 hstep_eq
    omega
  have h1ky_x : 1 + ky ≤ x := by clear hraw_step hmul_comm hstep_x hc11_y hky_1; omega
  have h1ky_phi : 1 + ky ≤ cousinDiamond2Phi x :=
    Nat.le_trans (by clear hraw_step hmul_comm hstep_x hc11_y hky_1; omega : 1 + ky ≤ x + 1)
      (cousinDiamond2Phi_ge_succ x)
  refine ⟨m, n, 1 + ky, hm34, hn1, hmul_comm, hstep_x, ?_, h1ky_x, h1ky_phi, ?_⟩
  · rw [hstep_x]; exact hc11_y
  · rw [cousinDiamond11Iter_add 1 ky x]
    have hi1 : cousinDiamond11Iter 1 x = y := hstep_x
    rw [hi1]; exact hky_1

theorem cousin_diamond11_reaches_one_within_phi :
    ∀ (B x : Nat), x > 0 -> cousinDiamond2Phi x ≤ B ->
      ∃ k : Nat, k ≤ B ∧ cousinDiamond11Iter k x = 1
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
        · rcases cousin_diamond11_cones4to12_exact_return.1 x hc4 with ⟨k, hle_phi, hk1⟩
          exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
        · by_cases hc5 : isDiamond4Cone5 x
          · rcases cousin_diamond11_cones4to12_exact_return.2.1 x hc5 with
              ⟨_, _, k, _, _, _, _, hle_phi, hk1⟩
            exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
          · by_cases hc6 : isDiamond5Cone6 x
            · rcases cousin_diamond11_cones4to12_exact_return.2.2.1 x hc6 with
                ⟨_, _, k, _, _, _, _, _, _, hle_phi, hk1⟩
              exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
            · by_cases hc7 : isDiamond6Cone7 x
              · rcases cousin_diamond11_cones4to12_exact_return.2.2.2.1 x hc7 with
                  ⟨_, _, k, _, _, _, _, _, _, hle_phi, hk1⟩
                exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
              · by_cases hc8 : isDiamond7Cone8 x
                · rcases cousin_diamond11_cones4to12_exact_return.2.2.2.2.1 x hc8 with
                    ⟨_, _, k, _, _, _, _, _, _, hle_phi, hk1⟩
                  exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
                · by_cases hc9 : isDiamond8Cone9 x
                  · rcases cousin_diamond11_cones4to12_exact_return.2.2.2.2.2.1 x hc9 with
                      ⟨_, _, k, _, _, _, _, _, _, hle_phi, hk1⟩
                    exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
                  · by_cases hc10 : isDiamond9Cone10 x
                    · rcases cousin_diamond11_cones4to12_exact_return.2.2.2.2.2.2.1 x hc10 with
                        ⟨_, _, k, _, _, _, _, _, _, hle_phi, hk1⟩
                      exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
                    · by_cases hc11 : isDiamond10Cone11 x
                      · rcases cousin_diamond11_cones4to12_exact_return.2.2.2.2.2.2.2.1 x hc11 with
                          ⟨_, _, k, _, _, _, _, _, _, hle_phi, hk1⟩
                        exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
                      · by_cases hc12 : isDiamond11Cone12 x
                        · rcases cousin_diamond11_cones4to12_exact_return.2.2.2.2.2.2.2.2 x hc12 with
                            ⟨_, _, k, _, _, _, _, _, _, hle_phi, hk1⟩
                          exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
                        · have hdesc := cousin_diamond11_outside_cones4to12_strict_descent x
                            (by omega) hc4 hc5 hc6 hc7 hc8 hc9 hc10 hc11 hc12
                          have hpos := cousinDiamond11Step_pos x hx
                          rcases cousin_diamond11_reaches_one_within_phi B (cousinDiamond11Step x) hpos (by omega) with
                            ⟨k, hk_le, hk_eq⟩
                          exact ⟨k + 1, by omega, hk_eq⟩

/--
  Theorem W14.3g (`cousin_diamond11_global_convergence`, `zero custom axioms`):
  Unconditional Global Convergence & Degree-5 Polynomial Stopping Bound for `T_diamond11`:
  For EVERY `x > 0`, `cousinDiamond11Iter` reaches `1` within `k ≤ (x + 1) ^ 3 + (x + 1) ^ 5` steps!
-/
theorem cousin_diamond11_global_convergence (x : Nat) (hx : x > 0) :
    ∃ k : Nat, k ≤ (x + 1) ^ 3 + (x + 1) ^ 5 ∧ cousinDiamond11Iter k x = 1 := by
  rcases cousin_diamond11_reaches_one_within_phi (cousinDiamond2Phi x) x hx (Nat.le_refl _) with
    ⟨k, hk_phi, hk1⟩
  exact ⟨k, Nat.le_trans hk_phi (cousinDiamond2Phi_upper_poly_bound x), hk1⟩

theorem exists_non_desc_along_diamond11_iter_clean :
    ∀ (terms : List LaurentTerm) (A0 B0 C0 N z : Nat),
      N ≥ 1 ->
      (∀ i : Nat, i < N ->
        cousinDiamond11Iter i z ≥ 3 ∧
        (cousinDiamond11Iter i z) % 2 = 1 ∧
        cousinDiamond11Step (cousinDiamond11Iter i z) ≥ 3) ->
      ¬ laurentDescProp terms A0 B0 C0 z (cousinDiamond11Iter N z) ->
      ∃ x : Nat,
        x ≥ 3 ∧ x % 2 = 1 ∧ cousinDiamond11Step x ≥ 3 ∧
        ¬ laurentDescProp terms A0 B0 C0 x (cousinDiamond11Step x)
  | _, _, _, _, 0, _, hN, _, _ => by omega
  | _, _, _, _, 1, z, _, hall, hnd => by
    rcases hall 0 (by decide) with ⟨hz3, hzo, hsz3⟩
    exact ⟨z, hz3, hzo, hsz3, hnd⟩
  | terms, A0, B0, C0, m + 2, z, _, hall, hnd => by
    if h0 : laurentDescProp terms A0 B0 C0 z (cousinDiamond11Step z) then
      have hnd_next : ¬ laurentDescProp terms A0 B0 C0 (cousinDiamond11Step z)
          (cousinDiamond11Iter (m + 1) (cousinDiamond11Step z)) :=
        fun hrest => hnd (laurentDescProp_trans terms A0 B0 C0 z (cousinDiamond11Step z) _ h0 hrest)
      exact exists_non_desc_along_diamond11_iter_clean terms A0 B0 C0 (m + 1) (cousinDiamond11Step z)
        (by omega) (fun i hi => hall (i + 1) (by omega)) hnd_next
    else
      rcases hall 0 (by omega) with ⟨hz3, hzo, hsz3⟩
      exact ⟨z, hz3, hzo, hsz3, h0⟩

/--
  Theorem W14.3h (`cousin_diamond11_r_block_spiral_climb_and_laurent_impossibility`,
  `zero custom axioms`):
  1. Cone-12 -> Cone-11 -> Cone-10 -> Cone-9 -> Cone-8 -> Cone-7 -> Cone-6 -> Cone-5 9-Tier Cascade & Unbounded `r`-Block Spiral Climb:
     `51537857741 -> 19326696653 -> 7247511245 -> 2717816717 -> 1019181269 -> 23887061 -> 559853 -> 209945` AND
     `cousinDiamond11Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5` for ALL `r ≥ 1, j ≤ r`!
  2. Universal `∀ L ≥ 1` Multi-Term Laurent Valuation Impossibility on `cousinDiamond11Step`!
-/
theorem cousin_diamond11_r_block_spiral_climb_and_laurent_impossibility :
    cousinDiamond11Step 51537857741 = 19326696653 ∧
    cousinDiamond11Step 19326696653 = 7247511245 ∧
    cousinDiamond11Step 7247511245 = 2717816717 ∧
    cousinDiamond11Step 2717816717 = 1019181269 ∧
    cousinDiamond11Step 1019181269 = 23887061 ∧
    cousinDiamond11Step 23887061 = 559853 ∧
    cousinDiamond11Step 559853 = 209945 ∧
    (∀ (r j : Nat), r ≥ 1 -> j ≤ r ->
      cousinDiamond11Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5) ∧
    (∀ (terms : List LaurentTerm) (A0 B0 C0 : Nat),
      (∃ t ∈ terms, t.coeff > 0) ->
      ∃ x : Nat,
        x ≥ 3 ∧ x % 2 = 1 ∧ cousinDiamond11Step x ≥ 3 ∧
        ¬ (evalLaurentSumNum terms (cousinDiamond11Step x) * laurentValDen A0 B0 C0 x <
            evalLaurentSumNum terms x * laurentValDen A0 B0 C0 (cousinDiamond11Step x))) := by
  have hspiral : ∀ (r j : Nat), r ≥ 1 -> j ≤ r ->
      cousinDiamond11Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5 := by
    intro r j hr hj
    cases j with
    | zero => simp [cousinDiamond11Iter]
    | succ j' =>
      have hp16_ge16 : 16 ^ r ≥ 16 := by
        rw [show r = (r - 1) + 1 by omega, Nat.pow_succ]
        have hp := nat_pow_pos_of_pos 16 (by decide) (r - 1); omega
      let x0 := 4 * 16 ^ r - 5
      have hx0_m4 : x0 % 4 = 3 := by dsimp only [x0]; omega
      have hx0_pow : 4 * 16 ^ r = 2 ^ (4 * r + 2) := by
        have h16 : 16 ^ r = 2 ^ (4 * r) := by
          rw [show (16 : Nat) = 2 ^ 4 from rfl, pow_pow_eq_mul_w5 2 4 r]
        rw [h16, show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add 2 2 (4 * r), Nat.add_comm 2 (4 * r)]
      have hs_first : cousinDiamond11Step x0 = 2 ^ (4 * r + 1) * 3 ^ 1 - 7 := by
        rw [d11_eq_d9_of_not_cone1211 x0 (not_cone1211_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond9Step_eq_d8_of_not_cone10 x0 (not_cone10_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond8Step_eq_d7_of_not_cone9 x0 (not_cone9_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond7Step_eq_d6_of_not_cone8 x0 (not_cone8_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond6Step_eq_d5_of_not_cone7 x0 (not_cone7_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond5Step_eq_d4_of_not_cone6 x0 (not_cone6_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond4Step_mod4_eq_3 x0 hx0_m4]
        dsimp only [x0]
        rw [hx0_pow, show 4 * r + 2 = (4 * r + 1) + 1 by omega, Nat.pow_succ 2 (4 * r + 1)]
        have hp := pow2_pos_nat (4 * r + 1); omega
      have hclimb := cousin_diamond11_cone5_two_step_climb j' (4 * r + 1) 1 (by omega) (by decide)
      let y_end := 2 ^ (4 * r + 1 - 3 * j') * 3 ^ (1 + 2 * j') - 7
      have hy_c5 : isDiamond4Cone5 y_end :=
        isDiamond4Cone5_of_pow2_pow3 (4 * r + 1 - 3 * j') (1 + 2 * j') (by omega) (by omega)
      have hy_nc1211 : ¬ isDiamond11Cone12 y_end ∧ ¬ isDiamond10Cone11 y_end :=
        not_cone1211_of_mod32_ne_13 y_end (by have h := hy_c5.2.1; omega)
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
      have hs_last : cousinDiamond11Step y_end = 4 * 16 ^ (r - (j' + 1)) * 18 ^ (j' + 1) - 5 := by
        rw [d11_eq_d9_of_not_cone1211 y_end hy_nc1211,
            cousinDiamond9Step_eq_d8_of_not_cone10 y_end hy_nc10,
            cousinDiamond8Step_eq_d7_of_not_cone9 y_end hy_nc9,
            cousinDiamond7Step_eq_d6_of_not_cone8 y_end hy_nc8,
            cousinDiamond6Step_eq_d5_of_not_cone7 y_end hy_nc7,
            cousinDiamond5Step_eq_d4_of_not_cone6 y_end hy_nc6]
        unfold cousinDiamond4Step; simp only [hy_c5, ite_true]
        dsimp only [y_end]
        have ha_sp : 4 * r + 1 - 3 * j' = 2 + (4 * (r - (j' + 1)) + (j' + 1) + 2) := by omega
        have hp2_sp : 2 ^ (4 * r + 1 - 3 * j') = 4 * (4 * 2 ^ (4 * (r - (j' + 1))) * 2 ^ (j' + 1)) := by
          rw [ha_sp, Nat.pow_add 2 2, Nat.pow_add 2 (4 * (r - (j' + 1)) + (j' + 1)) 2,
              Nat.pow_add 2 (4 * (r - (j' + 1))) (j' + 1)]
          change 4 * (2 ^ (4 * (r - (j' + 1))) * 2 ^ (j' + 1) * 4) = _
          ac_rfl
        have h16_rj : 2 ^ (4 * (r - (j' + 1))) = 16 ^ (r - (j' + 1)) := by
          rw [show (16 : Nat) = 2 ^ 4 from rfl, pow_pow_eq_mul_w5 2 4]
        have h18_j : 2 ^ (j' + 1) * 3 ^ (2 * (j' + 1)) = 18 ^ (j' + 1) := by
          rw [← pow9_eq_pow3_double (j' + 1), ← mul_pow_w14s 2 9 (j' + 1)]
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
          cousinDiamond11Iter_add (1 + 2 * j') 1,
          cousinDiamond11Iter_add 1 (2 * j')]
      have hi1 : cousinDiamond11Iter 1 x0 = 2 ^ (4 * r + 1) * 3 ^ 1 - 7 := hs_first
      rw [hi1, hclimb]
      exact hs_last
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, hspiral, ?_⟩
  intro terms A0 B0 C0 hnonempty
  rcases three_family_multiterm_laurent_obstruction terms A0 B0 C0 hnonempty with
    h97 | ⟨j2, hj2⟩ | ⟨r, hr_pos, hr3⟩
  · have hs97 : cousinDiamond11Step 97 = 73 := by decide
    refine ⟨97, by decide, by decide, by rw [hs97]; decide, ?_⟩
    rw [hs97]; exact h97
  · let zj := geomSpineEntry j2
    let Mj := 4 ^ (3 * j2 + 3)
    rcases geomSpineEntry_valuations_constant j2 with ⟨h3zj1, hzj_ge, _, _, _, _⟩
    change 3 * zj + 1 = 4 ^ (3 * j2 + 4) at h3zj1
    change zj ≥ 85 at hzj_ge
    have hMj_ge64 : Mj ≥ 64 := by
      dsimp only [Mj]; rw [Nat.pow_add 4 (3 * j2) 3]
      simpa using Nat.mul_le_mul_right 64 (nat_pow_pos_of_pos 4 (by decide) (3 * j2))
    have h3zj1_M : 3 * zj + 1 = 4 * Mj := by
      rw [h3zj1]; dsimp only [Mj]
      rw [show 3 * j2 + 4 = (3 * j2 + 3) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    let xj2 := 2 * zj - 1
    let yj2 := 2 * Mj - 1
    have hxj2_odd : xj2 % 2 = 1 := by dsimp only [xj2]; omega
    have hc4_xj2 : isDiamond3Cone4 xj2 := by
      refine ⟨by dsimp only [xj2]; omega, by dsimp only [xj2]; omega, ?_⟩
      have hpow2 : 3 * xj2 + 5 = 2 ^ (6 * j2 + 9) * 1 := by
        rw [Nat.mul_one, show 6 * j2 + 9 = 2 * (3 * j2 + 4) + 1 by omega,
            Nat.pow_succ, ← pow4_eq_pow2_even (3 * j2 + 4), Nat.mul_comm]
        dsimp only [xj2]; omega
      rw [hpow2]
      exact core2_pow2_mul (6 * j2 + 9) 1 (by decide) (by decide)
    have hstep_xj2 : cousinDiamond11Step xj2 = yj2 := by
      rw [d11_eq_d9_of_not_cone1211 xj2
            (not_cone1211_of_mod8_ne_5 xj2 (by have h := hc4_xj2.2.1; omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 xj2
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
      · simp only [hc5, ite_true]; dsimp only [xj2, yj2]; omega
      · simp only [hc5, ite_false]
        rw [cousinDiamond3Step_of_cone4_w8 xj2 hxj2_odd hc4_xj2]
        dsimp only [xj2, yj2]; omega
    refine ⟨xj2, by dsimp only [xj2]; omega, hxj2_odd, by rw [hstep_xj2]; dsimp only [yj2]; omega, ?_⟩
    rw [hstep_xj2]; exact hj2
  · let xr3 := 2 * 4 ^ r - 1
    let zr := 2 * 9 ^ r - 1
    let yr3 := (3 * 9 ^ r - 1) / 2
    have hp9_ge9 : 9 ^ r ≥ 9 := by
      rw [show r = (r - 1) + 1 by omega, Nat.pow_succ]
      have hp := nat_pow_pos_of_pos 9 (by decide) (r - 1); omega
    have hp9_m8 : 9 ^ r % 8 = 1 := pow9_mod8_eq_one_w5 r
    have hxr3_pow : xr3 = 2 ^ (2 * r + 1) * 1 - 1 := by
      dsimp only [xr3]; rw [Nat.mul_one, pow4_eq_pow2_even r, Nat.pow_succ, Nat.mul_comm]
    have hglide_i : ∀ i : Nat, i ≤ 2 * r ->
        cousinDiamond11Iter i xr3 = 3 ^ i * 2 ^ (2 * r + 1 - i) - 1 ∧
        cousinDiamond11Iter i xr3 ≥ 7 ∧
        (cousinDiamond11Iter i xr3) % 2 = 1 := by
      intro i hi
      have hf := cousin_diamond11_mersenne_scaled i (2 * r + 1) 1 (by omega) (by decide)
      rw [← hxr3_pow, Nat.mul_one] at hf
      have hprod_ge8 : 3 ^ i * 2 ^ (2 * r + 1 - i) ≥ 8 := by
        have h1 : 2 ^ i * 2 ^ (2 * r + 1 - i) ≤ 3 ^ i * 2 ^ (2 * r + 1 - i) :=
          Nat.mul_le_mul_right _ (pow2_le_pow3 i)
        rw [← Nat.pow_add, show i + (2 * r + 1 - i) = 2 * r + 1 by omega] at h1
        exact Nat.le_trans (pow2_mono_nat (by omega : 3 ≤ 2 * r + 1)) h1
      have hprod_ev : (3 ^ i * 2 ^ (2 * r + 1 - i)) % 2 = 0 := by
        rw [show 2 * r + 1 - i = (2 * r - i) + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc]; omega
      exact ⟨hf, by rw [hf]; omega, by rw [hf]; omega⟩
    have hiter_2r : cousinDiamond11Iter (2 * r) xr3 = zr := by
      have hf := (hglide_i (2 * r) (Nat.le_refl _)).1
      rw [hf, show 2 * r + 1 - 2 * r = 1 by omega, Nat.pow_one,
          ← pow9_eq_pow3_double r, Nat.mul_comm]
    have hstep_zr : cousinDiamond11Step zr = yr3 := by
      rw [d11_eq_d9_of_not_cone1211 zr (not_cone1211_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 zr (not_cone10_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 zr (not_cone9_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 zr (not_cone8_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 zr (not_cone7_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 zr (not_cone6_of_mod16_ne_13 zr (by dsimp only [zr]; omega))]
      have hnc5 : ¬ isDiamond4Cone5 zr := by rintro ⟨_, h32, _, _⟩; dsimp only [zr] at h32; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 zr hnc5]
      have hc3 : core3 (zr + 1) = 2 := by
        rw [show zr + 1 = 2 * 9 ^ r by dsimp only [zr]; omega,
            core3_mul2 (9 ^ r) (by omega), (pow9_eq_v3Pow_w5 r).2]
      rw [cousinDiamond3Step_of_core3_succ_two_w8 zr (by dsimp only [zr]; omega) (by dsimp only [zr]; omega) hc3]
      dsimp only [zr, yr3]; omega
    have hiter_2r1 : cousinDiamond11Iter (2 * r + 1) xr3 = yr3 := by
      rw [cousinDiamond11Iter_add (2 * r) 1 xr3, hiter_2r]; exact hstep_zr
    have hall : ∀ i : Nat, i < 2 * r + 1 ->
        cousinDiamond11Iter i xr3 ≥ 3 ∧
        (cousinDiamond11Iter i xr3) % 2 = 1 ∧
        cousinDiamond11Step (cousinDiamond11Iter i xr3) ≥ 3 := by
      intro i hi
      by_cases hlt : i < 2 * r
      · rcases hglide_i i (by omega) with ⟨_, hge7, hodd_i⟩
        have hnext : cousinDiamond11Step (cousinDiamond11Iter i xr3) =
            cousinDiamond11Iter (i + 1) xr3 :=
          (cousinDiamond11Iter_add i 1 xr3).symm
        rcases hglide_i (i + 1) (by omega) with ⟨_, hge7_n, _⟩
        exact ⟨by omega, hodd_i, by rw [hnext]; omega⟩
      · have hi_eq : i = 2 * r := by omega
        rw [hi_eq, hiter_2r, hstep_zr]
        exact ⟨by dsimp only [zr]; omega, by dsimp only [zr]; omega, by dsimp only [yr3]; omega⟩
    change ¬ laurentDescProp terms A0 B0 C0 xr3 yr3 at hr3
    rw [← hiter_2r1] at hr3
    exact exists_non_desc_along_diamond11_iter_clean terms A0 B0 C0 (2 * r + 1) xr3 (by omega) hall hr3


/--
  Theorem W14.3i (`cousin_diamond11_q6_noninteger_avoids_cone12`, choice-free `zero custom axioms`):
  Universal Non-Integer Rational Exclusion from Cone 12 on `M1 = Q_(6)^+`:
  For EVERY reduced non-integer rational `(num, den)` (`Nat.gcd num den = 1` and `den > 1`),
  `core3 (core2 (1749811 * den + num)) ≠ den`, so `cousinDiamond11StepQ6 (num, den)` NEVER enters
  Cone 12 and agrees identically with `cousinDiamond10StepQ6 (num, den)`!
-/
theorem cousin_diamond11_q6_noninteger_avoids_cone12 (num den : Nat)
    (hgcd : Nat.gcd num den = 1) (hden : den > 1) :
    core3 (core2 (1749811 * den + num)) ≠ den ∧
    cousinDiamond11StepQ6 (num, den) = cousinDiamond10StepQ6 (num, den) := by
  have hne : core3 (core2 (1749811 * den + num)) ≠ den := by
    intro heq
    have hdvd_sum : den ∣ (1749811 * den + num) := by
      have hc_dvd : core3 (core2 (1749811 * den + num)) ∣ (1749811 * den + num) :=
        Nat.dvd_trans (core3Aux_dvd_w8 _ _) (core2Aux_dvd_w8 _ _)
      rwa [heq] at hc_dvd
    rcases hdvd_sum with ⟨k, hk⟩
    have hdvd_num : den ∣ num := ⟨k - 1749811, by
      have hge : k ≥ 1749811 := by
        by_cases hlt : k < 1749811
        · have hm := Nat.mul_le_mul_left den (show k ≤ 1749810 by omega); omega
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
  unfold cousinDiamond11StepQ6
  have hcond : ¬ (num ≥ 51537857741 * den ∧ (num * invMod17179869184Odd den) % 17179869184 = 17178119373 ∧
      (num * (den % 3)) % 3 = 2 ∧ core3 (core2 (1749811 * den + num)) = den) :=
    fun ⟨_, _, _, hc⟩ => hne hc
  simp only [hcond, ite_false]

private theorem hensel_inv_lift_w14 (M1 M2 S C d i1 : Nat)
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
      x = (M2 * (d / M2) + d % M2) * i1 := by dsimp only [x]; rw [← hd_div]
      _ = M2 * ((d / M2) * i1) + (d % M2) * i1 := by rw [Nat.add_mul, Nat.mul_assoc]
      _ = M2 * ((d / M2) * i1) + (M2 * (((d % M2) * i1) / M2) + r) := by rw [← hdr_div]
      _ = M2 * K + r := by dsimp only [K]; rw [Nat.mul_add]; omega
  let q1 := x / M1
  have hx_M1 : x = M1 * q1 + 1 := by
    have hdm := (Nat.div_add_mod x M1).symm
    dsimp only [x] at hdm ⊢
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
  have hdY_eq : d * Y = x * (C - r) := by dsimp only [x, Y]; ac_rfl
  dsimp only [Y] at hdY_mod
  rw [← hdY_mod, hdY_eq, hx_mod]

private theorem core3_core2_eq_coprime23Core_w14 :
    ∀ (fuel n : Nat), n > 0 -> n ≤ fuel -> core3 (core2 n) = coprime23Core n
  | 0, _, hn, hle => by omega
  | fuel + 1, n, hn, hle => by
    by_cases hev : n % 2 = 0
    · let k := n / 2
      have hk_pos : k > 0 := by dsimp only [k]; omega
      have hn_eq : n = 2 * k := by dsimp only [k]; omega
      rw [hn_eq, core2_mul2 k hk_pos, coprime23Core_mul2 k hk_pos]
      exact core3_core2_eq_coprime23Core_w14 fuel k hk_pos (by dsimp only [k]; omega)
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

private theorem reduceRatPair_div_exact_w14 (a m : Nat) (hm : m > 0) (hdvd : m ∣ a) :
    reduceRatPair a m = (a / m, 1) := by
  rcases hdvd with ⟨q, rfl⟩
  unfold reduceRatPair
  have hgcd : Nat.gcd (m * q) m = m :=
    Nat.dvd_antisymm (Nat.gcd_dvd_right (m * q) m) (Nat.dvd_gcd ⟨q, rfl⟩ (Nat.dvd_refl m))
  dsimp only
  rw [hgcd, Nat.div_self hm]

private theorem dvd_three_mul_add_one_of_mod_w14 (x M D Qm Qr R Qt : Nat)
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
  Theorem W14.3j (`invMod17179869184Odd_mul_and_q6_nat_agreement`,
  `zero custom axioms`):
  Universal 7-Step Newton–Hensel `mod 2^34` Odd-Inverse Correctness & Exact `Q_(6)^+` / `Nat`
  Step Agreement for `T_diamond11` (`Branch P5.13`):
  1. For EVERY odd `d : Nat` (`d % 2 = 1`), `(d * invMod17179869184Odd d) % 17179869184 = 1`!
  2. For EVERY `x : Nat`, `cousinDiamond11StepQ6 (x, 1) = (cousinDiamond11Step x, 1)`!
-/
theorem invMod17179869184Odd_mul_and_q6_nat_agreement :
    (∀ d : Nat, d % 2 = 1 -> (d * invMod17179869184Odd d) % 17179869184 = 1) ∧
    (∀ x : Nat, cousinDiamond11StepQ6 (x, 1) = (cousinDiamond11Step x, 1)) := by
  rcases invMod2147483648Odd_mul_and_q6_nat_agreement with ⟨hinv2b, hd10_all⟩
  have hinv17b : ∀ d : Nat, d % 2 = 1 -> (d * invMod17179869184Odd d) % 17179869184 = 1 := by
    intro d hodd
    exact hensel_inv_lift_w14 2147483648 17179869184 268435456 34359738370 d (invMod2147483648Odd d)
      (by decide) (by decide) (by decide) (hinv2b d hodd)
  refine ⟨hinv17b, ?_⟩
  have hi17b : invMod17179869184Odd 1 = 1 := by decide
  have hm3_1 : (1 : Nat) % 3 = 1 := by decide
  intro x
  have hcc : core3 (core2 (1749811 + x)) = coprime23Core (1749811 + x) :=
    core3_core2_eq_coprime23Core_w14 (1749811 + x) (1749811 + x) (by omega) (Nat.le_refl _)
  unfold cousinDiamond11StepQ6 cousinDiamond11Step isDiamond11Cone12
  simp only [hi17b, hm3_1, Nat.mul_one, hcc]
  by_cases hc12 : x ≥ 51537857741 ∧ x % 17179869184 = 17178119373 ∧ x % 3 = 2 ∧ coprime23Core (1749811 + x) = 1
  · simp only [hc12, and_self, ite_true]
    exact reduceRatPair_div_exact_w14 (3 * x + 1) 8 (by decide)
      (dvd_three_mul_add_one_of_mod_w14 x 17179869184 8 2147483648 2147264921 5 2
        (by decide) hc12.2.1 (by decide))
  · simp only [hc12, ite_false]; exact hd10_all x

set_option maxRecDepth 16384 in
/--
  Theorem W14.3k (`cousin_diamond11_counter_model_separation`, `[]` axioms):
  `T_diamond11` rejects ALL three Counter-Models (`M1 = Q_(6)^+` 5-cycle `(1, 7) -> ... -> (1, 7)`
  plus non-integers `(51537857741, 7)` and `(206156680397, 7)` bypassing Cone 12 by `W14.3i`,
  `M2 = Z^-` cycles `-1` and `-5 -> -7 -> -10 -> -5`, and `M3` supercritical `q = 7` 5-cycle at `5`),
  AND at the genuine `v_2(3x + 1) = 3` Cone-12 jumps `206156680397 -> 77308755149` (`21` steps to `1`) and
  `51537857741 -> 19326696653 -> 7247511245 -> 2717816717 -> 1019181269 -> 23887061 -> 559853 -> 209945`
  (`ZPOS_COUSIN_DIAMOND11_CONE12_51537857741_JUMP`, `22` steps to `1`) strictly increases
  `cousinDiamond2Phi` (`+38.44x`) directly into `Cone 11 -> Cone 10 -> Cone 9 -> Cone 8 -> Cone 7 -> Cone 6 -> Cone 5`!
-/
theorem cousin_diamond11_counter_model_separation :
    cousinDiamond11StepInt (-1) = -1 ∧
    cousinDiamond11IterInt 3 (-5) = -5 ∧
    cousinDiamond11IterParam 7 5 5 = 5 ∧
    cousinDiamond11StepQ6 (1, 7) = (5, 7) ∧
    cousinDiamond11IterQ6 5 (1, 7) = (1, 7) ∧
    cousinDiamond11StepQ6 (51537857741, 7) = cousinDiamond10StepQ6 (51537857741, 7) ∧
    cousinDiamond11StepQ6 (206156680397, 7) = cousinDiamond10StepQ6 (206156680397, 7) ∧
    isDiamond11Cone12 206156680397 ∧
    cousinDiamond11Step 206156680397 = 77308755149 ∧
    cousinDiamond11Iter 21 206156680397 = 1 ∧
    isDiamond11Cone12 51537857741 ∧
    cousinDiamond11Step 51537857741 = 19326696653 ∧
    cousinDiamond11StepInt 51537857741 = 19326696653 ∧
    cousinDiamond11StepQ6 (51537857741, 1) = (19326696653, 1) ∧
    isDiamond10Cone11 19326696653 ∧
    isDiamond9Cone10 7247511245 ∧
    isDiamond8Cone9 2717816717 ∧
    isDiamond7Cone8 1019181269 ∧
    isDiamond6Cone7 23887061 ∧
    isDiamond5Cone6 559853 ∧
    isDiamond4Cone5 209945 ∧
    cousinDiamond2Phi 51537857741 < cousinDiamond2Phi 19326696653 ∧
    cousinDiamond11Iter 22 51537857741 = 1 := by
  decide

-- ============================================================================
-- SECTION 3: Front D (Branches P2.2 & P5.3) — Complete Mod-`4374` (`2 * 3^7`)
--            Markov Bijection, `22 + 5 = 27` Prefix-Weight-`8` Dichotomy, &
--            Unconditional Three-Zero-Run Quadratic Dyadic-Window Occupancy
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Section 3A: Complete Mod-`4374` (`2 * 3^7`) Markov Bijection, `22 + 5 = 27`
--             Prefix-Weight-`8` Dichotomy, & `3^(w - 8)` Fiber Equidistribution (`P5.3`, `W14_H4`)
-- ----------------------------------------------------------------------------

def survivingMod4374List : List Nat :=
  (List.range 4374).filter (fun r => r % 6 == 1 || r % 6 == 3)

private theorem mem_survivingMod4374List_iff (y : Nat) :
    y ∈ survivingMod4374List ↔ (y < 4374 ∧ (y % 6 = 1 ∨ y % 6 = 3)) := by
  unfold survivingMod4374List
  rw [List.mem_filter, List.mem_range, Bool.or_eq_true, beq_iff_eq, beq_iff_eq]

private def markov7Aux (q r : Nat) : Nat :=
  match q with
  | 0 =>
    match r with
    | 0 => 1 | 1 => 1851 | 2 => 2761 | 3 => 531 | 4 => 3703 | 5 => 1353 | 6 => 1423 | 7 => 3615 | 8 => 2941
    | 9 => 2565 | 10 => 2317 | 11 => 579 | 12 => 91 | 13 => 3759 | 14 => 2311 | 15 => 3951 | 16 => 3523 | 17 => 3045
    | 18 => 1837 | 19 => 825 | 20 => 2329 | 21 => 3231 | 22 => 31 | 23 => 2919 | 24 => 3745 | 25 => 2103 | _ => 79
  | 1 =>
    match r with
    | 0 => 3321 | 1 => 2047 | 2 => 3117 | 3 => 2899 | 4 => 1761 | 5 => 1393 | 6 => 2763 | 7 => 2281 | 8 => 2181
    | 9 => 757 | 10 => 2715 | 11 => 3355 | 12 => 99 | 13 => 2191 | 14 => 3027 | 15 => 3151 | 16 => 3507 | 17 => 3049
    | 18 => 2619 | 19 => 3235 | 20 => 4197 | 21 => 2791 | 22 => 2679 | 23 => 1933 | 24 => 117 | 25 => 2497 | _ => 4233
  | 2 =>
    match r with
    | 0 => 1135 | 1 => 3147 | 2 => 1465 | 3 => 4257 | 4 => 1435 | 5 => 1677 | 6 => 4015 | 7 => 3453 | 8 => 3103
    | 9 => 459 | 10 => 1507 | 11 => 3819 | 12 => 4141 | 13 => 2139 | 14 => 3931 | 15 => 387 | 16 => 4171 | 17 => 453
    | 18 => 2971 | 19 => 2121 | 20 => 1033 | 21 => 2583 | 22 => 2137 | 23 => 3243 | 24 => 1963 | 25 => 1941 | _ => 241
  | 3 =>
    match r with
    | 0 => 1215 | 1 => 1237 | 2 => 1983 | 3 => 2575 | 4 => 141 | 5 => 3013 | 6 => 3573 | 7 => 2929 | 8 => 3963
    | 9 => 1891 | 10 => 4011 | 11 => 2059 | 12 => 3825 | 13 => 4297 | 14 => 3351 | 15 => 1369 | 16 => 3345 | 17 => 3211
    | 18 => 513 | 19 => 2425 | 20 => 3063 | 21 => 2467 | 22 => 1059 | 23 => 3553 | 24 => 927 | 25 => 3145 | _ => 1641
  | 4 =>
    match r with
    | 0 => 2269 | 1 => 69 | 2 => 169 | 3 => 3609 | 4 => 3541 | 5 => 2001 | 6 => 2233 | 7 => 3291 | 8 => 3265
    | 9 => 2727 | 10 => 697 | 11 => 2685 | 12 => 3817 | 13 => 519 | 14 => 1177 | 15 => 1197 | 16 => 445 | 17 => 2235
    | 18 => 4105 | 19 => 3417 | 20 => 4111 | 21 => 1935 | 22 => 4243 | 23 => 3567 | 24 => 181 | 25 => 1779 | _ => 403
  | 5 =>
    match r with
    | 0 => 3483 | 1 => 427 | 2 => 849 | 3 => 2251 | 4 => 2895 | 5 => 259 | 6 => 9 | 7 => 3577 | 8 => 1371
    | 9 => 3025 | 10 => 933 | 11 => 763 | 12 => 3177 | 13 => 2029 | 14 => 3675 | 15 => 3961 | 16 => 3183 | 17 => 3373
    | 18 => 2781 | 19 => 1615 | 20 => 1929 | 21 => 2143 | 22 => 3813 | 23 => 799 | 24 => 1737 | 25 => 3793 | _ => 3423
  | 6 =>
    match r with
    | 0 => 3403 | 1 => 1365 | 2 => 3247 | 3 => 2961 | 4 => 1273 | 5 => 2325 | 6 => 451 | 7 => 3129 | 8 => 3427
    | 9 => 621 | 10 => 4261 | 11 => 1551 | 12 => 3493 | 13 => 3273 | 14 => 2797 | 15 => 2007 | 16 => 1093 | 17 => 4017
    | 18 => 865 | 19 => 339 | 20 => 2815 | 21 => 1287 | 22 => 1975 | 23 => 3891 | 24 => 2773 | 25 => 1617 | _ => 565
  | 7 =>
    match r with
    | 0 => 1377 | 1 => 3991 | 2 => 4089 | 3 => 1927 | 4 => 1275 | 5 => 1879 | 6 => 819 | 7 => 4225 | 8 => 3153
    | 9 => 4159 | 10 => 2229 | 11 => 3841 | 12 => 2529 | 13 => 4135 | 14 => 3999 | 15 => 2179 | 16 => 3021 | 17 => 3535
    | 18 => 675 | 19 => 805 | 20 => 795 | 21 => 1819 | 22 => 2193 | 23 => 2419 | 24 => 2547 | 25 => 67 | _ => 831
  | 8 =>
    match r with
    | 0 => 163 | 1 => 2661 | 2 => 1951 | 3 => 2313 | 4 => 3379 | 5 => 2649 | 6 => 3043 | 7 => 2967 | 8 => 3589
    | 9 => 2889 | 10 => 3451 | 11 => 417 | 12 => 3169 | 13 => 1653 | 14 => 43 | 15 => 2817 | 16 => 1741 | 17 => 1425
    | 18 => 1999 | 19 => 1635 | 20 => 1519 | 21 => 639 | 22 => 4081 | 23 => 4215 | 24 => 991 | 25 => 1455 | _ => 727
  | 9 =>
    match r with
    | 0 => 3645 | 1 => 3181 | 2 => 2955 | 3 => 1603 | 4 => 4029 | 5 => 3499 | 6 => 1629 | 7 => 499 | 8 => 561
    | 9 => 919 | 10 => 3525 | 11 => 2545 | 12 => 1881 | 13 => 1867 | 14 => 4323 | 15 => 397 | 16 => 2859 | 17 => 3697
    | 18 => 2943 | 19 => 4369 | 20 => 4035 | 21 => 1495 | 22 => 573 | 23 => 4039 | 24 => 3357 | 25 => 715 | _ => 2613
  | 10 =>
    match r with
    | 0 => 1297 | 1 => 3957 | 2 => 655 | 3 => 1665 | 4 => 1111 | 5 => 2973 | 6 => 1261 | 7 => 2805 | 8 => 3751
    | 9 => 783 | 10 => 2641 | 11 => 3657 | 12 => 2845 | 13 => 33 | 14 => 1663 | 15 => 3627 | 16 => 2389 | 17 => 3207
    | 18 => 3133 | 19 => 2931 | 20 => 223 | 21 => 4365 | 22 => 1813 | 23 => 165 | 24 => 3583 | 25 => 1293 | _ => 889
  | 11 =>
    match r with
    | 0 => 1539 | 1 => 2371 | 2 => 1821 | 3 => 1279 | 4 => 2409 | 5 => 745 | 6 => 2439 | 7 => 1147 | 8 => 2343
    | 9 => 2053 | 10 => 447 | 11 => 1249 | 12 => 1233 | 13 => 3973 | 14 => 273 | 15 => 2989 | 16 => 2697 | 17 => 3859
    | 18 => 837 | 19 => 3559 | 20 => 2901 | 21 => 1171 | 22 => 3327 | 23 => 1285 | 24 => 4167 | 25 => 1363 | _ => 21
  | 12 =>
    match r with
    | 0 => 2431 | 1 => 879 | 2 => 3733 | 3 => 1017 | 4 => 3217 | 5 => 3297 | 6 => 3853 | 7 => 2643 | 8 => 3913
    | 9 => 3051 | 10 => 1831 | 11 => 2523 | 12 => 2521 | 13 => 2787 | 14 => 3283 | 15 => 63 | 16 => 3037 | 17 => 615
    | 18 => 4267 | 19 => 4227 | 20 => 3301 | 21 => 3717 | 22 => 3919 | 23 => 489 | 24 => 1801 | 25 => 1131 | _ => 1051
  | 13 =>
    match r with
    | 0 => 3807 | 1 => 1561 | 2 => 687 | 3 => 955 | 4 => 789 | 5 => 2365 | 6 => 3249 | 7 => 1795 | 8 => 4125
    | 9 => 3187 | 10 => 1743 | 11 => 4327 | 12 => 585 | 13 => 1705 | 14 => 597 | 15 => 1207 | 16 => 2535 | 17 => 4021
    | 18 => 3105 | 19 => 2749 | 20 => 1767 | 21 => 847 | 22 => 1707 | 23 => 2905 | 24 => 603 | 25 => 2011 | _ => 1803
  | 14 =>
    match r with
    | 0 => 3565 | 1 => 2175 | 2 => 2437 | 3 => 369 | 4 => 949 | 5 => 3621 | 6 => 2071 | 7 => 2481 | 8 => 4075
    | 9 => 945 | 10 => 1021 | 11 => 1389 | 12 => 2197 | 13 => 1167 | 14 => 529 | 15 => 873 | 16 => 3685 | 17 => 2397
    | 18 => 1027 | 19 => 1149 | 20 => 2005 | 21 => 3069 | 22 => 1651 | 23 => 813 | 24 => 19 | 25 => 969 | _ => 1213
  | 15 =>
    match r with
    | 0 => 1701 | 1 => 751 | 2 => 3927 | 3 => 631 | 4 => 3543 | 5 => 3985 | 6 => 4059 | 7 => 2443 | 8 => 1533
    | 9 => 4321 | 10 => 3039 | 11 => 3031 | 12 => 4311 | 13 => 3811 | 14 => 921 | 15 => 3799 | 16 => 2373 | 17 => 4183
    | 18 => 999 | 19 => 1939 | 20 => 633 | 21 => 523 | 22 => 87 | 23 => 151 | 24 => 1413 | 25 => 2659 | _ => 3585
  | 16 =>
    match r with
    | 0 => 325 | 1 => 3471 | 2 => 1141 | 3 => 4095 | 4 => 3055 | 5 => 3945 | 6 => 289 | 7 => 2319 | 8 => 4237
    | 9 => 3213 | 10 => 211 | 11 => 255 | 12 => 1873 | 13 => 3921 | 14 => 2149 | 15 => 1683 | 16 => 4333 | 17 => 4179
    | 18 => 2161 | 19 => 2445 | 20 => 709 | 21 => 2421 | 22 => 3757 | 23 => 1137 | 24 => 2611 | 25 => 807 | _ => 1375
  | 17 =>
    match r with
    | 0 => 3969 | 1 => 4315 | 2 => 2793 | 3 => 307 | 4 => 1923 | 5 => 1231 | 6 => 495 | 7 => 3091 | 8 => 3315
    | 9 => 1081 | 10 => 4335 | 11 => 1735 | 12 => 3663 | 13 => 1543 | 14 => 1245 | 15 => 2017 | 16 => 2211 | 17 => 4345
    | 18 => 3267 | 19 => 1129 | 20 => 3873 | 21 => 199 | 22 => 2841 | 23 => 1771 | 24 => 2223 | 25 => 3307 | _ => 993
  | 18 =>
    match r with
    | 0 => 1459 | 1 => 393 | 2 => 4219 | 3 => 3447 | 4 => 787 | 5 => 4269 | 6 => 2881 | 7 => 2157 | 8 => 25
    | 9 => 1107 | 10 => 3775 | 11 => 3495 | 12 => 1549 | 13 => 2301 | 14 => 3769 | 15 => 2493 | 16 => 607 | 17 => 1587
    | 18 => 3295 | 19 => 3741 | 20 => 3787 | 21 => 1773 | 22 => 1489 | 23 => 1461 | 24 => 829 | 25 => 645 | _ => 1537
  | 19 =>
    match r with
    | 0 => 1863 | 1 => 3505 | 2 => 1659 | 3 => 4357 | 4 => 303 | 5 => 2851 | 6 => 1305 | 7 => 3739 | 8 => 723
    | 9 => 2215 | 10 => 1257 | 11 => 439 | 12 => 3015 | 13 => 3649 | 14 => 1569 | 15 => 235 | 16 => 2049 | 17 => 133
    | 18 => 1161 | 19 => 319 | 20 => 2739 | 21 => 4249 | 22 => 1221 | 23 => 3391 | 24 => 3033 | 25 => 3955 | _ => 2775
  | 20 =>
    match r with
    | 0 => 2593 | 1 => 1689 | 2 => 2923 | 3 => 2799 | 4 => 2893 | 5 => 219 | 6 => 1099 | 7 => 1995 | 8 => 187
    | 9 => 3375 | 10 => 2965 | 11 => 2361 | 12 => 1225 | 13 => 681 | 14 => 1015 | 15 => 3303 | 16 => 1255 | 17 => 3369
    | 18 => 55 | 19 => 663 | 20 => 2491 | 21 => 1125 | 22 => 3595 | 23 => 1785 | 24 => 3421 | 25 => 483 | _ => 1699
  | 21 =>
    match r with
    | 0 => 4131 | 1 => 2695 | 2 => 525 | 3 => 4033 | 4 => 3057 | 5 => 97 | 6 => 2115 | 7 => 13 | 8 => 2505
    | 9 => 3349 | 10 => 2553 | 11 => 3517 | 12 => 2367 | 13 => 1381 | 14 => 1893 | 15 => 2827 | 16 => 1887 | 17 => 295
    | 18 => 3429 | 19 => 3883 | 20 => 1605 | 21 => 3925 | 22 => 3975 | 23 => 637 | 24 => 3843 | 25 => 229 | _ => 183
  | 22 =>
    match r with
    | 0 => 3727 | 1 => 2985 | 2 => 1627 | 3 => 2151 | 4 => 625 | 5 => 543 | 6 => 3691 | 7 => 1833 | 8 => 349
    | 9 => 1269 | 10 => 2155 | 11 => 1227 | 12 => 901 | 13 => 3435 | 14 => 2635 | 15 => 4113 | 16 => 1903 | 17 => 777
    | 18 => 1189 | 19 => 1959 | 20 => 1195 | 21 => 477 | 22 => 1327 | 23 => 2109 | 24 => 1639 | 25 => 321 | _ => 1861
  | 23 =>
    match r with
    | 0 => 2025 | 1 => 1885 | 2 => 3765 | 3 => 3709 | 4 => 1437 | 5 => 1717 | 6 => 2925 | 7 => 661 | 8 => 4287
    | 9 => 109 | 10 => 3849 | 11 => 2221 | 12 => 1719 | 13 => 3487 | 14 => 2217 | 15 => 1045 | 16 => 1725 | 17 => 457
    | 18 => 1323 | 19 => 3073 | 20 => 471 | 21 => 3601 | 22 => 2355 | 23 => 2257 | 24 => 279 | 25 => 877 | _ => 1965
  | 24 =>
    match r with
    | 0 => 487 | 1 => 4281 | 2 => 331 | 3 => 1503 | 4 => 2731 | 5 => 867 | 6 => 1909 | 7 => 1671 | 8 => 511
    | 9 => 3537 | 10 => 1345 | 11 => 93 | 12 => 577 | 13 => 1815 | 14 => 4255 | 15 => 549 | 16 => 2551 | 17 => 2559
    | 18 => 2323 | 19 => 3255 | 20 => 4273 | 21 => 4203 | 22 => 3433 | 23 => 2433 | 24 => 4231 | 25 => 159 | _ => 2023
  | 25 =>
    match r with
    | 0 => 4293 | 1 => 1075 | 2 => 2631 | 3 => 3385 | 4 => 4191 | 5 => 3337 | 6 => 3735 | 7 => 1309 | 8 => 1695
    | 9 => 1243 | 10 => 771 | 11 => 925 | 12 => 1071 | 13 => 1219 | 14 => 2541 | 15 => 3637 | 16 => 1563 | 17 => 619
    | 18 => 3591 | 19 => 2263 | 20 => 3711 | 21 => 3277 | 22 => 735 | 23 => 3877 | 24 => 1089 | 25 => 1525 | _ => 3747
  | 26 =>
    match r with
    | 0 => 1621 | 1 => 1203 | 2 => 3409 | 3 => 855 | 4 => 463 | 5 => 1191 | 6 => 127 | 7 => 1509 | 8 => 673
    | 9 => 1431 | 10 => 535 | 11 => 3333 | 12 => 253 | 13 => 195 | 14 => 1501 | 15 => 1359 | 16 => 3199 | 17 => 4341
    | 18 => 3457 | 19 => 177 | 20 => 2977 | 21 => 3555 | 22 => 1165 | 23 => 2757 | 24 => 2449 | 25 => 4371 | _ => 2185
  | 27 =>
    match r with
    | 0 => 2187 | 1 => 265 | 2 => 1497 | 3 => 3061 | 4 => 2571 | 5 => 583 | 6 => 171 | 7 => 1957 | 8 => 3477
    | 9 => 2377 | 10 => 2067 | 11 => 4003 | 12 => 423 | 13 => 3325 | 14 => 2865 | 15 => 1855 | 16 => 1401 | 17 => 781
    | 18 => 1485 | 19 => 1453 | 20 => 2577 | 21 => 2953 | 22 => 3489 | 23 => 1123 | 24 => 1899 | 25 => 2173 | _ => 1155
  | 28 =>
    match r with
    | 0 => 2755 | 1 => 2499 | 2 => 2113 | 3 => 207 | 4 => 2569 | 5 => 1515 | 6 => 2719 | 7 => 1347 | 8 => 835
    | 9 => 3699 | 10 => 4099 | 11 => 2199 | 12 => 4303 | 13 => 2949 | 14 => 3121 | 15 => 2169 | 16 => 3847 | 17 => 1749
    | 18 => 217 | 19 => 1473 | 20 => 1681 | 21 => 2907 | 22 => 3271 | 23 => 3081 | 24 => 667 | 25 => 4209 | _ => 2347
  | 29 =>
    match r with
    | 0 => 81 | 1 => 3829 | 2 => 363 | 3 => 2737 | 4 => 951 | 5 => 2203 | 6 => 981 | 7 => 2605 | 8 => 885
    | 9 => 3511 | 10 => 3363 | 11 => 2707 | 12 => 4149 | 13 => 1057 | 14 => 3189 | 15 => 73 | 16 => 1239 | 17 => 943
    | 18 => 3753 | 19 => 643 | 20 => 1443 | 21 => 2629 | 22 => 1869 | 23 => 2743 | 24 => 2709 | 25 => 2821 | _ => 2937
  | 30 =>
    match r with
    | 0 => 3889 | 1 => 3795 | 2 => 817 | 3 => 3933 | 4 => 301 | 5 => 1839 | 6 => 937 | 7 => 1185 | 8 => 997
    | 9 => 1593 | 10 => 3289 | 11 => 1065 | 12 => 3979 | 13 => 1329 | 14 => 367 | 15 => 2979 | 16 => 121 | 17 => 3531
    | 18 => 1351 | 19 => 2769 | 20 => 385 | 21 => 2259 | 22 => 1003 | 23 => 3405 | 24 => 3259 | 25 => 4047 | _ => 2509
  | 31 =>
    match r with
    | 0 => 2349 | 1 => 3019 | 2 => 3603 | 3 => 2413 | 4 => 3705 | 5 => 3823 | 6 => 1791 | 7 => 3253 | 8 => 2667
    | 9 => 271 | 10 => 285 | 11 => 1411 | 12 => 3501 | 13 => 3163 | 14 => 3513 | 15 => 2665 | 16 => 1077 | 17 => 1105
    | 18 => 1647 | 19 => 4207 | 20 => 309 | 21 => 2305 | 22 => 249 | 23 => 4363 | 24 => 3519 | 25 => 3469 | _ => 345
  | 32 =>
    match r with
    | 0 => 649 | 1 => 717 | 2 => 3895 | 3 => 3285 | 4 => 2407 | 5 => 2163 | 6 => 3529 | 7 => 1023 | 8 => 1159
    | 9 => 3861 | 10 => 2479 | 11 => 4305 | 12 => 3655 | 13 => 4083 | 14 => 1987 | 15 => 3789 | 16 => 769 | 17 => 939
    | 18 => 2485 | 19 => 4065 | 20 => 3463 | 21 => 1611 | 22 => 3109 | 23 => 3729 | 24 => 1477 | 25 => 3885 | _ => 2671
  | 33 =>
    match r with
    | 0 => 243 | 1 => 2209 | 2 => 2469 | 3 => 2089 | 4 => 2085 | 5 => 1069 | 6 => 2601 | 7 => 3901 | 8 => 75
    | 9 => 1405 | 10 => 1581 | 11 => 115 | 12 => 2853 | 13 => 895 | 14 => 3837 | 15 => 883 | 16 => 915 | 17 => 1267
    | 18 => 3915 | 19 => 3397 | 20 => 3549 | 21 => 1981 | 22 => 3003 | 23 => 1609 | 24 => 4329 | 25 => 4117 | _ => 2127
  | 34 =>
    match r with
    | 0 => 1783 | 1 => 2013 | 2 => 2599 | 3 => 2637 | 4 => 139 | 5 => 2487 | 6 => 1747 | 7 => 861 | 8 => 1321
    | 9 => 1755 | 10 => 1669 | 11 => 3171 | 12 => 3331 | 13 => 2463 | 14 => 3607 | 15 => 225 | 16 => 1417 | 17 => 2721
    | 18 => 3619 | 19 => 987 | 20 => 2167 | 21 => 963 | 22 => 841 | 23 => 4053 | 24 => 4069 | 25 => 3723 | _ => 2833
  | 35 =>
    match r with
    | 0 => 2511 | 1 => 1399 | 2 => 1335 | 3 => 1765 | 4 => 465 | 5 => 2689 | 6 => 3411 | 7 => 175 | 8 => 1857
    | 9 => 2539 | 10 => 2877 | 11 => 3193 | 12 => 2205 | 13 => 3001 | 14 => 4161 | 15 => 3475 | 16 => 753 | 17 => 1429
    | 18 => 1809 | 19 => 2587 | 20 => 2415 | 21 => 1657 | 22 => 1383 | 23 => 3229 | 24 => 765 | 25 => 391 | _ => 3909
  | 36 =>
    match r with
    | 0 => 2917 | 1 => 3309 | 2 => 1303 | 3 => 1989 | 4 => 2245 | 5 => 2811 | 6 => 4339 | 7 => 699 | 8 => 1483
    | 9 => 4023 | 10 => 859 | 11 => 2037 | 12 => 3007 | 13 => 843 | 14 => 853 | 15 => 1035 | 16 => 2065 | 17 => 129
    | 18 => 379 | 19 => 2283 | 20 => 871 | 21 => 315 | 22 => 2947 | 23 => 3 | 24 => 2287 | 25 => 3561 | _ => 2995
  | 37 =>
    match r with
    | 0 => 405 | 1 => 589 | 2 => 201 | 3 => 1441 | 4 => 3219 | 5 => 4309 | 6 => 4221 | 7 => 823 | 8 => 3639
    | 9 => 3673 | 10 => 4173 | 11 => 1897 | 12 => 1557 | 13 => 733 | 14 => 111 | 15 => 1693 | 16 => 591 | 17 => 1591
    | 18 => 4077 | 19 => 1777 | 20 => 1281 | 21 => 1333 | 22 => 4137 | 23 => 475 | 24 => 1575 | 25 => 1039 | _ => 1317
  | 38 =>
    match r with
    | 0 => 4051 | 1 => 231 | 2 => 7 | 3 => 1341 | 4 => 4351 | 5 => 3135 | 6 => 2557 | 7 => 537 | 8 => 1645
    | 9 => 1917 | 10 => 49 | 11 => 903 | 12 => 2683 | 13 => 3597 | 14 => 2473 | 15 => 1845 | 16 => 2713 | 17 => 1911
    | 18 => 1513 | 19 => 3579 | 20 => 3949 | 21 => 4041 | 22 => 679 | 23 => 327 | 24 => 505 | 25 => 3399 | _ => 3157
  | 39 =>
    match r with
    | 0 => 2673 | 1 => 4153 | 2 => 3441 | 3 => 1117 | 4 => 1599 | 5 => 1555 | 6 => 657 | 7 => 1471 | 8 => 1047
    | 9 => 433 | 10 => 1095 | 11 => 601 | 12 => 909 | 13 => 2839 | 14 => 435 | 15 => 4285 | 16 => 429 | 17 => 1753
    | 18 => 1971 | 19 => 967 | 20 => 147 | 21 => 1009 | 22 => 2517 | 23 => 2095 | 24 => 2385 | 25 => 1687 | _ => 3099
  | 40 =>
    match r with
    | 0 => 811 | 1 => 1527 | 2 => 3085 | 3 => 693 | 4 => 2083 | 5 => 3459 | 6 => 775 | 7 => 375 | 8 => 1807
    | 9 => 4185 | 10 => 3613 | 11 => 4143 | 12 => 2359 | 13 => 1977 | 14 => 4093 | 15 => 2655 | 16 => 3361 | 17 => 3693
    | 18 => 2647 | 19 => 501 | 20 => 2653 | 21 => 3393 | 22 => 2785 | 23 => 651 | 24 => 3097 | 25 => 3237 | _ => 3319
  | 41 =>
    match r with
    | 0 => 567 | 1 => 3343 | 2 => 2307 | 3 => 793 | 4 => 4353 | 5 => 3175 | 6 => 1467 | 7 => 2119 | 8 => 2829
    | 9 => 1567 | 10 => 2391 | 11 => 3679 | 12 => 261 | 13 => 571 | 14 => 759 | 15 => 2503 | 16 => 267 | 17 => 1915
    | 18 => 4239 | 19 => 157 | 20 => 3387 | 21 => 685 | 22 => 897 | 23 => 3715 | 24 => 3195 | 25 => 2335 | _ => 507
  | 42 =>
    match r with
    | 0 => 1945 | 1 => 2823 | 2 => 1789 | 3 => 45 | 4 => 4189 | 5 => 3783 | 6 => 3367 | 7 => 213 | 8 => 1969
    | 9 => 2079 | 10 => 2803 | 11 => 3009 | 12 => 2035 | 13 => 357 | 14 => 1339 | 15 => 3465 | 16 => 4009 | 17 => 1101
    | 18 => 3781 | 19 => 1797 | 20 => 1357 | 21 => 2745 | 22 => 517 | 23 => 975 | 24 => 1315 | 25 => 3075 | _ => 3481
  | 43 =>
    match r with
    | 0 => 2835 | 1 => 2533 | 2 => 1173 | 3 => 469 | 4 => 2733 | 5 => 421 | 6 => 2277 | 7 => 2767 | 8 => 237
    | 9 => 2701 | 10 => 3687 | 11 => 2383 | 12 => 3987 | 13 => 2677 | 14 => 1083 | 15 => 721 | 16 => 105 | 17 => 2077
    | 18 => 2133 | 19 => 3721 | 20 => 2253 | 21 => 361 | 22 => 3651 | 23 => 961 | 24 => 4005 | 25 => 2983 | _ => 2289
  | 44 =>
    match r with
    | 0 => 3079 | 1 => 4119 | 2 => 493 | 3 => 3771 | 4 => 1921 | 5 => 4107 | 6 => 1585 | 7 => 51 | 8 => 2131
    | 9 => 4347 | 10 => 1993 | 11 => 1875 | 12 => 1711 | 13 => 3111 | 14 => 2959 | 15 => 4275 | 16 => 283 | 17 => 2883
    | 18 => 541 | 19 => 3093 | 20 => 61 | 21 => 2097 | 22 => 2623 | 23 => 1299 | 24 => 3907 | 25 => 2913 | _ => 3643
  | 45 =>
    match r with
    | 0 => 729 | 1 => 1723 | 2 => 39 | 3 => 145 | 4 => 1113 | 5 => 2041 | 6 => 3087 | 7 => 3415 | 8 => 2019
    | 9 => 3835 | 10 => 609 | 11 => 1087 | 12 => 3339 | 13 => 409 | 14 => 1407 | 15 => 3313 | 16 => 4317 | 17 => 2239
    | 18 => 27 | 19 => 2911 | 20 => 1119 | 21 => 37 | 22 => 2031 | 23 => 2581 | 24 => 441 | 25 => 3631 | _ => 4071
  | 46 =>
    match r with
    | 0 => 4213 | 1 => 1041 | 2 => 3571 | 3 => 3123 | 4 => 4027 | 5 => 57 | 6 => 4177 | 7 => 4263 | 8 => 2293
    | 9 => 2241 | 10 => 1183 | 11 => 741 | 12 => 1387 | 13 => 1491 | 14 => 205 | 15 => 711 | 16 => 931 | 17 => 291
    | 18 => 1675 | 19 => 15 | 20 => 3139 | 21 => 1449 | 22 => 355 | 23 => 1623 | 24 => 2125 | 25 => 2751 | _ => 3805
  | 47 =>
    match r with
    | 0 => 2997 | 1 => 913 | 2 => 3279 | 3 => 4195 | 4 => 3867 | 5 => 3661 | 6 => 3897 | 7 => 4063 | 8 => 3801
    | 9 => 595 | 10 => 1905 | 11 => 4165 | 12 => 2691 | 13 => 2515 | 14 => 1731 | 15 => 1531 | 16 => 4155 | 17 => 2401
    | 18 => 2295 | 19 => 2101 | 20 => 4359 | 21 => 4087 | 22 => 411 | 23 => 4201 | 24 => 1251 | 25 => 4279 | _ => 1479
  | 48 =>
    match r with
    | 0 => 973 | 1 => 2337 | 2 => 2275 | 3 => 2475 | 4 => 1759 | 5 => 381 | 6 => 2395 | 7 => 4101 | 8 => 2455
    | 9 => 135 | 10 => 373 | 11 => 3981 | 12 => 1063 | 13 => 4245 | 14 => 1825 | 15 => 1521 | 16 => 1579 | 17 => 2073
    | 18 => 2809 | 19 => 1311 | 20 => 1843 | 21 => 801 | 22 => 2461 | 23 => 1947 | 24 => 343 | 25 => 2589 | _ => 3967
  | 49 =>
    match r with
    | 0 => 891 | 1 => 103 | 2 => 2145 | 3 => 3871 | 4 => 2247 | 5 => 907 | 6 => 333 | 7 => 337 | 8 => 1209
    | 9 => 1729 | 10 => 3201 | 11 => 2869 | 12 => 2043 | 13 => 247 | 14 => 2055 | 15 => 4123 | 16 => 3993 | 17 => 2563
    | 18 => 189 | 19 => 1291 | 20 => 3225 | 21 => 3763 | 22 => 3165 | 23 => 1447 | 24 => 2061 | 25 => 553 | _ => 3261
  | 50 =>
    match r with
    | 0 => 2107 | 1 => 3633 | 2 => 979 | 3 => 1827 | 4 => 3865 | 5 => 705 | 6 => 613 | 7 => 3939 | 8 => 2617
    | 9 => 2403 | 10 => 3937 | 11 => 2847 | 12 => 739 | 13 => 2625 | 14 => 3445 | 15 => 2331 | 16 => 2227 | 17 => 3855
    | 18 => 3943 | 19 => 2607 | 20 => 547 | 21 => 153 | 22 => 193 | 23 => 2271 | 24 => 2935 | 25 => 2427 | _ => 4129
  | 51 =>
    match r with
    | 0 => 3159 | 1 => 3667 | 2 => 1011 | 3 => 3547 | 4 => 627 | 5 => 2527 | 6 => 1143 | 7 => 985 | 8 => 2991
    | 9 => 2863 | 10 => 123 | 11 => 1573 | 12 => 1395 | 13 => 2353 | 14 => 2379 | 15 => 2341 | 16 => 3831 | 17 => 2725
    | 18 => 2457 | 19 => 481 | 20 => 2091 | 21 => 3439 | 22 => 1545 | 23 => 3067 | 24 => 2871 | 25 => 1201 | _ => 669
  | 52 =>
    match r with
    | 0 => 3241 | 1 => 555 | 2 => 4057 | 3 => 1179 | 4 => 1597 | 5 => 1029 | 6 => 3205 | 7 => 3777 | 8 => 2779
    | 9 => 297 | 10 => 3127 | 11 => 1713 | 12 => 415 | 13 => 1005 | 14 => 691 | 15 => 3141 | 16 => 2875 | 17 => 1263
    | 18 => 703 | 19 => 3903 | 20 => 3625 | 21 => 3879 | 22 => 2299 | 23 => 2595 | 24 => 1153 | 25 => 2265 | _ => 4291
  | _ =>
    match r with
    | 0 => 1053 | 1 => 2857 | 2 => 4251 | 3 => 3223 | 4 => 3381 | 5 => 4147 | 6 => 1953 | 7 => 1633 | 8 => 399
    | 9 => 3997 | 10 => 1419 | 11 => 277 | 12 => 747 | 13 => 85 | 14 => 2703 | 15 => 559 | 16 => 3669 | 17 => 2887
    | 18 => 351 | 19 => 4045 | 20 => 957 | 21 => 3115 | 22 => 4299 | 23 => 313 | 24 => 3681 | 25 => 1849 | _ => 2451

def markovShiftTrue7Mod4374Table (x : Fin 1458) : Nat :=
  markov7Aux (x.val / 27) (x.val % 27)

private def invMarkov7Aux (q r : Nat) : Nat :=
  match q with
  | 0 =>
    match r with
    | 0 => 0 | 1 => 995 | 2 => 1028 | 3 => 141 | 4 => 574 | 5 => 1261 | 6 => 402 | 7 => 323 | 8 => 494
    | 9 => 1233 | 10 => 22 | 11 => 283 | 12 => 1236 | 13 => 1217 | 14 => 230 | 15 => 1137 | 16 => 1036 | 17 => 1195
    | 18 => 558 | 19 => 1247 | 20 => 1208 | 21 => 339 | 22 => 214 | 23 => 109 | 24 => 798 | 25 => 899 | _ => 26
  | 1 =>
    match r with
    | 0 => 783 | 1 => 1444 | 2 => 427 | 3 => 12 | 4 => 659 | 5 => 572 | 6 => 39 | 7 => 1324 | 8 => 1177
    | 9 => 630 | 10 => 1013 | 11 => 902 | 12 => 51 | 13 => 826 | 14 => 1387 | 15 => 708 | 16 => 989 | 17 => 530
    | 18 => 1305 | 19 => 922 | 20 => 85 | 21 => 1218 | 22 => 1073 | 23 => 428 | 24 => 1371 | 25 => 1126 | _ => 673
  | 2 =>
    match r with
    | 0 => 216 | 1 => 293 | 2 => 110 | 3 => 735 | 4 => 952 | 5 => 721 | 6 => 132 | 7 => 593 | 8 => 548
    | 9 => 1341 | 10 => 1372 | 11 => 715 | 12 => 480 | 13 => 1001 | 14 => 1256 | 15 => 759 | 16 => 442 | 17 => 1141
    | 18 => 774 | 19 => 545 | 20 => 290 | 21 => 933 | 22 => 592 | 23 => 1027 | 24 => 528 | 25 => 1169 | _ => 80
  | 3 =>
    match r with
    | 0 => 891 | 1 => 1336 | 2 => 859 | 3 => 714 | 4 => 443 | 5 => 140 | 6 => 1119 | 7 => 730 | 8 => 1123
    | 9 => 846 | 10 => 311 | 11 => 1442 | 12 => 645 | 13 => 1204 | 14 => 847 | 15 => 438 | 16 => 1259 | 17 => 584
    | 18 => 1413 | 19 => 814 | 20 => 517 | 21 => 462 | 22 => 857 | 23 => 1454 | 24 => 993 | 25 => 532 | _ => 619
  | 4 =>
    match r with
    | 0 => 432 | 1 => 1049 | 2 => 650 | 3 => 1329 | 4 => 1330 | 5 => 181 | 6 => 1320 | 7 => 863 | 8 => 602
    | 9 => 1449 | 10 => 1264 | 11 => 1147 | 12 => 1182 | 13 => 785 | 14 => 824 | 15 => 381 | 16 => 1306 | 17 => 1087
    | 18 => 990 | 19 => 1301 | 20 => 830 | 21 => 69 | 22 => 970 | 23 => 487 | 24 => 258 | 25 => 1439 | _ => 134
  | 5 =>
    match r with
    | 0 => 999 | 1 => 1228 | 2 => 1291 | 3 => 1416 | 4 => 227 | 5 => 1166 | 6 => 741 | 7 => 136 | 8 => 1069
    | 9 => 1062 | 10 => 1067 | 11 => 524 | 12 => 1239 | 13 => 124 | 14 => 307 | 15 => 168 | 16 => 71 | 17 => 638
    | 18 => 63 | 19 => 706 | 20 => 949 | 21 => 1164 | 22 => 641 | 23 => 1022 | 24 => 615 | 25 => 1396 | _ => 565
  | 6 =>
    match r with
    | 0 => 648 | 1 => 347 | 2 => 1190 | 3 => 465 | 4 => 250 | 5 => 1099 | 6 => 1050 | 7 => 1133 | 8 => 656
    | 9 => 99 | 10 => 1156 | 11 => 121 | 12 => 426 | 13 => 569 | 14 => 392 | 15 => 3 | 16 => 712 | 17 => 1033
    | 18 => 1206 | 19 => 599 | 20 => 1370 | 21 => 663 | 22 => 1348 | 23 => 1405 | 24 => 1446 | 25 => 251 | _ => 188
  | 7 =>
    match r with
    | 0 => 1107 | 1 => 1120 | 2 => 265 | 3 => 660 | 4 => 11 | 5 => 734 | 6 => 363 | 7 => 1000 | 8 => 1015
    | 9 => 1278 | 10 => 365 | 11 => 1064 | 12 => 375 | 13 => 502 | 14 => 1225 | 15 => 1356 | 16 => 341 | 17 => 692
    | 18 => 171 | 19 => 598 | 20 => 1381 | 21 => 408 | 22 => 425 | 23 => 590 | 24 => 237 | 25 => 802 | _ => 511
  | 8 =>
    match r with
    | 0 => 864 | 1 => 1103 | 2 => 272 | 3 => 1059 | 4 => 628 | 5 => 559 | 6 => 780 | 7 => 1403 | 8 => 710
    | 9 => 207 | 10 => 1048 | 11 => 553 | 12 => 1128 | 13 => 353 | 14 => 1418 | 15 => 1083 | 16 => 118 | 17 => 979
    | 18 => 1422 | 19 => 1355 | 20 => 452 | 21 => 1257 | 22 => 268 | 23 => 865 | 24 => 1176 | 25 => 521 | _ => 242
  | 9 =>
    match r with
    | 0 => 1215 | 1 => 1012 | 2 => 697 | 3 => 1362 | 4 => 1253 | 5 => 302 | 6 => 1443 | 7 => 406 | 8 => 961
    | 9 => 36 | 10 => 1121 | 11 => 146 | 12 => 969 | 13 => 880 | 14 => 685 | 15 => 1086 | 16 => 611 | 17 => 746
    | 18 => 279 | 19 => 490 | 20 => 355 | 21 => 1110 | 22 => 209 | 23 => 158 | 24 => 1317 | 25 => 208 | _ => 457
  | 10 =>
    match r with
    | 0 => 1080 | 1 => 401 | 2 => 812 | 3 => 195 | 4 => 1006 | 5 => 19 | 6 => 510 | 7 => 215 | 8 => 764
    | 9 => 315 | 10 => 940 | 11 => 985 | 12 => 372 | 13 => 137 | 14 => 986 | 15 => 705 | 16 => 982 | 17 => 925
    | 18 => 180 | 19 => 653 | 20 => 992 | 21 => 393 | 22 => 646 | 23 => 325 | 24 => 906 | 25 => 791 | _ => 296
  | 11 =>
    match r with
    | 0 => 1323 | 1 => 904 | 2 => 1129 | 3 => 606 | 4 => 1037 | 5 => 1328 | 6 => 1065 | 7 => 1270 | 8 => 907
    | 9 => 252 | 10 => 419 | 11 => 686 | 12 => 105 | 13 => 1258 | 14 => 145 | 15 => 816 | 16 => 881 | 17 => 800
    | 18 => 387 | 19 => 382 | 20 => 787 | 21 => 354 | 22 => 1451 | 23 => 1184 | 24 => 939 | 25 => 1072 | _ => 403
  | 12 =>
    match r with
    | 0 => 1296 | 1 => 1157 | 2 => 1352 | 3 => 789 | 4 => 1384 | 5 => 937 | 6 => 240 | 7 => 485 | 8 => 818
    | 9 => 423 | 10 => 832 | 11 => 1417 | 12 => 1074 | 13 => 1379 | 14 => 554 | 15 => 327 | 16 => 388 | 17 => 871
    | 18 => 396 | 19 => 1409 | 20 => 74 | 21 => 987 | 22 => 1024 | 23 => 1243 | 24 => 636 | 25 => 1061 | _ => 350
  | 13 =>
    match r with
    | 0 => 1431 | 1 => 796 | 2 => 103 | 3 => 1308 | 4 => 821 | 5 => 896 | 6 => 687 | 7 => 676 | 8 => 853
    | 9 => 468 | 10 => 1175 | 11 => 1226 | 12 => 699 | 13 => 178 | 14 => 1063 | 15 => 546 | 16 => 1151 | 17 => 854
    | 18 => 495 | 19 => 274 | 20 => 1219 | 21 => 1056 | 22 => 1235 | 23 => 752 | 24 => 561 | 25 => 478 | _ => 349
  | 14 =>
    match r with
    | 0 => 54 | 1 => 455 | 2 => 434 | 3 => 1383 | 4 => 304 | 5 => 397 | 6 => 1428 | 7 => 755 | 8 => 872
    | 9 => 531 | 10 => 724 | 11 => 391 | 12 => 318 | 13 => 1163 | 14 => 122 | 15 => 1407 | 16 => 1252 | 17 => 817
    | 18 => 612 | 19 => 707 | 20 => 614 | 21 => 123 | 22 => 1402 | 23 => 703 | 24 => 366 | 25 => 1331 | _ => 404
  | 15 =>
    match r with
    | 0 => 81 | 1 => 688 | 2 => 535 | 3 => 552 | 4 => 605 | 5 => 464 | 6 => 309 | 7 => 82 | 8 => 799
    | 9 => 684 | 10 => 473 | 11 => 308 | 12 => 1293 | 13 => 556 | 14 => 523 | 15 => 276 | 16 => 1421 | 17 => 908
    | 18 => 603 | 19 => 166 | 20 => 193 | 21 => 300 | 22 => 1019 | 23 => 320 | 24 => 183 | 25 => 1342 | _ => 295
  | 16 =>
    match r with
    | 0 => 270 | 1 => 1211 | 2 => 974 | 3 => 519 | 4 => 682 | 5 => 1315 | 6 => 1158 | 7 => 1025 | 8 => 926
    | 9 => 639 | 10 => 616 | 11 => 823 | 12 => 1020 | 13 => 947 | 14 => 1148 | 15 => 1029 | 16 => 658 | 17 => 763
    | 18 => 828 | 19 => 5 | 20 => 1154 | 21 => 717 | 22 => 322 | 23 => 163 | 24 => 96 | 25 => 143 | _ => 458
  | 17 =>
    match r with
    | 0 => 189 | 1 => 580 | 2 => 967 | 3 => 1254 | 4 => 389 | 5 => 32 | 6 => 1389 | 7 => 946 | 8 => 745
    | 9 => 900 | 10 => 1229 | 11 => 848 | 12 => 429 | 13 => 934 | 14 => 1441 | 15 => 6 | 16 => 233 | 17 => 962
    | 18 => 711 | 19 => 58 | 20 => 625 | 21 => 1002 | 22 => 803 | 23 => 1346 | 24 => 1263 | 25 => 748 | _ => 241
  | 18 =>
    match r with
    | 0 => 486 | 1 => 509 | 2 => 56 | 3 => 1113 | 4 => 1060 | 5 => 775 | 6 => 888 | 7 => 1295 | 8 => 980
    | 9 => 747 | 10 => 508 | 11 => 1255 | 12 => 264 | 13 => 731 | 14 => 716 | 15 => 651 | 16 => 64 | 17 => 709
    | 18 => 1044 | 19 => 761 | 20 => 236 | 21 => 1311 | 22 => 700 | 23 => 1081 | 24 => 1284 | 25 => 413 | _ => 512
  | 19 =>
    match r with
    | 0 => 297 | 1 => 472 | 2 => 1399 | 3 => 498 | 4 => 173 | 5 => 1058 | 6 => 1011 | 7 => 352 | 8 => 691
    | 9 => 1116 | 10 => 527 | 11 => 1388 | 12 => 1023 | 13 => 1312 | 14 => 901 | 15 => 1194 | 16 => 503 | 17 => 1016
    | 18 => 819 | 19 => 1408 | 20 => 1057 | 21 => 246 | 22 => 587 | 23 => 914 | 24 => 885 | 25 => 154 | _ => 187
  | 20 =>
    match r with
    | 0 => 702 | 1 => 1265 | 2 => 596 | 3 => 249 | 4 => 1438 | 5 => 235 | 6 => 618 | 7 => 107 | 8 => 1034
    | 9 => 855 | 10 => 400 | 11 => 229 | 12 => 966 | 13 => 515 | 14 => 284 | 15 => 273 | 16 => 928 | 17 => 655
    | 18 => 1260 | 19 => 59 | 20 => 776 | 21 => 447 | 22 => 1078 | 23 => 541 | 24 => 1014 | 25 => 683 | _ => 566
  | 21 =>
    match r with
    | 0 => 405 | 1 => 364 | 2 => 373 | 3 => 1200 | 4 => 1415 | 5 => 626 | 6 => 633 | 7 => 1216 | 8 => 637
    | 9 => 1332 | 10 => 1283 | 11 => 470 | 12 => 159 | 13 => 232 | 14 => 361 | 15 => 924 | 16 => 773 | 17 => 1070
    | 18 => 927 | 19 => 1300 | 20 => 31 | 21 => 948 | 22 => 371 | 23 => 482 | 24 => 507 | 25 => 1018 | _ => 133
  | 22 =>
    match r with
    | 0 => 918 | 1 => 563 | 2 => 1136 | 3 => 843 | 4 => 358 | 5 => 1153 | 6 => 348 | 7 => 377 | 8 => 1088
    | 9 => 963 | 10 => 292 | 11 => 661 | 12 => 210 | 13 => 299 | 14 => 1310 | 15 => 1353 | 16 => 334 | 17 => 601
    | 18 => 18 | 19 => 815 | 20 => 1316 | 21 => 1041 | 22 => 1456 | 23 => 1 | 24 => 744 | 25 => 953 | _ => 620
  | 23 =>
    match r with
    | 0 => 513 | 1 => 256 | 2 => 805 | 3 => 444 | 4 => 1199 | 5 => 194 | 6 => 255 | 7 => 622 | 8 => 583
    | 9 => 90 | 10 => 581 | 11 => 1010 | 12 => 753 | 13 => 610 | 14 => 1279 | 15 => 654 | 16 => 1043 | 17 => 1124
    | 18 => 1035 | 19 => 1192 | 20 => 463 | 21 => 192 | 22 => 155 | 23 => 50 | 24 => 129 | 25 => 424 | _ => 79
  | 24 =>
    match r with
    | 0 => 1134 | 1 => 1319 | 2 => 218 | 3 => 1437 | 4 => 736 | 5 => 613 | 6 => 78 | 7 => 647 | 8 => 1142
    | 9 => 1071 | 10 => 184 | 11 => 1093 | 12 => 912 | 13 => 83 | 14 => 878 | 15 => 975 | 16 => 1198 | 17 => 547
    | 18 => 234 | 19 => 113 | 20 => 398 | 21 => 177 | 22 => 376 | 23 => 919 | 24 => 474 | 25 => 1223 | _ => 674
  | 25 =>
    match r with
    | 0 => 621 | 1 => 148 | 2 => 1237 | 3 => 1146 | 4 => 983 | 5 => 1220 | 6 => 1335 | 7 => 28 | 8 => 529
    | 9 => 306 | 10 => 1337 | 11 => 92 | 12 => 1347 | 13 => 988 | 14 => 739 | 15 => 384 | 16 => 1313 | 17 => 1178
    | 18 => 1143 | 19 => 1084 | 20 => 895 | 21 => 894 | 22 => 1397 | 23 => 1076 | 24 => 1209 | 25 => 1288 | _ => 25
  | 26 =>
    match r with
    | 0 => 1350 | 1 => 617 | 2 => 758 | 3 => 573 | 4 => 1114 | 5 => 73 | 6 => 1266 | 7 => 917 | 8 => 1196
    | 9 => 1179 | 10 => 76 | 11 => 67 | 12 => 156 | 13 => 1325 | 14 => 446 | 15 => 597 | 16 => 604 | 17 => 493
    | 18 => 450 | 19 => 869 | 20 => 938 | 21 => 771 | 22 => 754 | 23 => 379 | 24 => 204 | 25 => 35 | _ => 728
  | 27 =>
    match r with
    | 0 => 729 | 1 => 40 | 2 => 211 | 3 => 390 | 4 => 767 | 5 => 788 | 6 => 957 | 7 => 892 | 8 => 475
    | 9 => 522 | 10 => 635 | 11 => 632 | 12 => 483 | 13 => 1366 | 14 => 199 | 15 => 114 | 16 => 125 | 17 => 1232
    | 18 => 1251 | 19 => 976 | 20 => 1327 | 21 => 138 | 22 => 1181 | 23 => 644 | 24 => 831 | 25 => 694 | _ => 1429
  | 28 =>
    match r with
    | 0 => 108 | 1 => 1373 | 2 => 1298 | 3 => 1167 | 4 => 34 | 5 => 991 | 6 => 996 | 7 => 1187 | 8 => 1250
    | 9 => 1287 | 10 => 1426 | 11 => 499 | 12 => 858 | 13 => 1109 | 14 => 14 | 15 => 219 | 16 => 10 | 17 => 439
    | 18 => 666 | 19 => 167 | 20 => 20 | 21 => 1365 | 22 => 1132 | 23 => 1297 | 24 => 1392 | 25 => 305 | _ => 782
  | 29 =>
    match r with
    | 0 => 837 | 1 => 1390 | 2 => 643 | 3 => 1092 | 4 => 551 | 5 => 356 | 6 => 579 | 7 => 298 | 8 => 421
    | 9 => 738 | 10 => 1391 | 11 => 1172 | 12 => 1077 | 13 => 286 | 14 => 1117 | 15 => 1302 | 16 => 395 | 17 => 1286
    | 18 => 1359 | 19 => 868 | 20 => 301 | 21 => 840 | 22 => 965 | 23 => 212 | 24 => 453 | 25 => 100 | _ => 1375
  | 30 =>
    match r with
    | 0 => 324 | 1 => 671 | 2 => 380 | 3 => 303 | 4 => 412 | 5 => 451 | 6 => 726 | 7 => 1457 | 8 => 1304
    | 9 => 1395 | 10 => 1318 | 11 => 931 | 12 => 102 | 13 => 893 | 14 => 1040 | 15 => 1299 | 16 => 874 | 17 => 385
    | 18 => 882 | 19 => 923 | 20 => 560 | 21 => 501 | 22 => 52 | 23 => 757 | 24 => 1122 | 25 => 575 | _ => 836
  | 31 =>
    match r with
    | 0 => 945 | 1 => 1282 | 2 => 1075 | 3 => 336 | 4 => 335 | 5 => 1382 | 6 => 201 | 7 => 1162 | 8 => 367
    | 9 => 954 | 10 => 689 | 11 => 254 | 12 => 213 | 13 => 664 | 14 => 577 | 15 => 1032 | 16 => 665 | 17 => 1340
    | 18 => 9 | 19 => 760 | 20 => 733 | 21 => 84 | 22 => 749 | 23 => 1238 | 24 => 75 | 25 => 964 | _ => 1321
  | 32 =>
    match r with
    | 0 => 540 | 1 => 1427 | 2 => 920 | 3 => 897 | 4 => 790 | 5 => 1369 | 6 => 456 | 7 => 269 | 8 => 1358
    | 9 => 45 | 10 => 1210 | 11 => 1363 | 12 => 804 | 13 => 677 | 14 => 608 | 15 => 921 | 16 => 280 | 17 => 331
    | 18 => 1098 | 19 => 221 | 20 => 1100 | 21 => 1095 | 22 => 430 | 23 => 217 | 24 => 852 | 25 => 845 | _ => 890
  | 33 =>
    match r with
    | 0 => 1053 | 1 => 1174 | 2 => 49 | 3 => 1038 | 4 => 119 | 5 => 950 | 6 => 1281 | 7 => 568 | 8 => 313
    | 9 => 1170 | 10 => 1445 | 11 => 794 | 12 => 807 | 13 => 1042 | 14 => 37 | 15 => 762 | 16 => 935 | 17 => 1394
    | 18 => 117 | 19 => 652 | 20 => 1165 | 21 => 786 | 22 => 533 | 23 => 806 | 24 => 1155 | 25 => 370 | _ => 1267
  | 34 =>
    match r with
    | 0 => 756 | 1 => 725 | 2 => 2 | 3 => 33 | 4 => 1168 | 5 => 829 | 6 => 186 | 7 => 539 | 8 => 1412
    | 9 => 153 | 10 => 1102 | 11 => 337 | 12 => 48 | 13 => 461 | 14 => 176 | 15 => 543 | 16 => 1144 | 17 => 277
    | 18 => 1314 | 19 => 977 | 20 => 182 | 21 => 231 | 22 => 808 | 23 => 1135 | 24 => 582 | 25 => 1115 | _ => 944
  | 35 =>
    match r with
    | 0 => 1161 | 1 => 1066 | 2 => 481 | 3 => 282 | 4 => 1361 | 5 => 518 | 6 => 903 | 7 => 1432 | 8 => 259
    | 9 => 1386 | 10 => 743 | 11 => 1334 | 12 => 1401 | 13 => 1420 | 14 => 955 | 15 => 492 | 16 => 1205 | 17 => 1448
    | 18 => 225 | 19 => 544 | 20 => 139 | 21 => 30 | 22 => 317 | 23 => 374 | 24 => 777 | 25 => 1234 | _ => 1213
  | 36 =>
    match r with
    | 0 => 972 | 1 => 23 | 2 => 542 | 3 => 627 | 4 => 88 | 5 => 289 | 6 => 1374 | 7 => 809 | 8 => 8
    | 9 => 261 | 10 => 994 | 11 => 769 | 12 => 750 | 13 => 245 | 14 => 1202 | 15 => 165 | 16 => 550 | 17 => 223
    | 18 => 72 | 19 => 275 | 20 => 722 | 21 => 825 | 22 => 1186 | 23 => 595 | 24 => 312 | 25 => 1385 | _ => 998
  | 37 =>
    match r with
    | 0 => 1269 | 1 => 958 | 2 => 913 | 3 => 984 | 4 => 1145 | 5 => 86 | 6 => 525 | 7 => 838 | 8 => 205
    | 9 => 144 | 10 => 41 | 11 => 416 | 12 => 537 | 13 => 340 | 14 => 415 | 15 => 222 | 16 => 17 | 17 => 44
    | 18 => 333 | 19 => 436 | 20 => 571 | 21 => 732 | 22 => 101 | 23 => 1400 | 24 => 399 | 25 => 640 | _ => 1159
  | 38 =>
    match r with
    | 0 => 1188 | 1 => 779 | 2 => 1082 | 3 => 1221 | 4 => 466 | 5 => 1207 | 6 => 1104 | 7 => 1079 | 8 => 62
    | 9 => 369 | 10 => 886 | 11 => 1201 | 12 => 1452 | 13 => 29 | 14 => 770 | 15 => 1245 | 16 => 1414 | 17 => 169
    | 18 => 288 | 19 => 1031 | 20 => 1262 | 21 => 1419 | 22 => 106 | 23 => 55 | 24 => 42 | 25 => 197 | _ => 1052
  | 39 =>
    match r with
    | 0 => 1377 | 1 => 850 | 2 => 1345 | 3 => 228 | 4 => 929 | 5 => 1112 | 6 => 147 | 7 => 244 | 8 => 151
    | 9 => 360 | 10 => 797 | 11 => 956 | 12 => 1131 | 13 => 718 | 14 => 1333 | 15 => 1410 | 16 => 287 | 17 => 98
    | 18 => 441 | 19 => 328 | 20 => 1003 | 21 => 1434 | 22 => 1343 | 23 => 968 | 24 => 21 | 25 => 46 | _ => 1105
  | 40 =>
    match r with
    | 0 => 1404 | 1 => 77 | 2 => 164 | 3 => 357 | 4 => 844 | 5 => 667 | 6 => 834 | 7 => 1349 | 8 => 116
    | 9 => 477 | 10 => 778 | 11 => 175 | 12 => 696 | 13 => 1271 | 14 => 338 | 15 => 867 | 16 => 820 | 17 => 115
    | 18 => 504 | 19 => 329 | 20 => 344 | 21 => 555 | 22 => 484 | 23 => 973 | 24 => 1230 | 25 => 467 | _ => 1106
  | 41 =>
    match r with
    | 0 => 27 | 1 => 742 | 2 => 319 | 3 => 930 | 4 => 713 | 5 => 680 | 6 => 1227 | 7 => 1108 | 8 => 97
    | 9 => 576 | 10 => 95 | 11 => 38 | 12 => 267 | 13 => 1096 | 14 => 793 | 15 => 1140 | 16 => 557 | 17 => 152
    | 18 => 549 | 19 => 220 | 20 => 1435 | 21 => 678 | 22 => 1127 | 23 => 536 | 24 => 1101 | 25 => 910 | _ => 1051
  | 42 =>
    match r with
    | 0 => 162 | 1 => 833 | 2 => 704 | 3 => 951 | 4 => 1222 | 5 => 127 | 6 => 564 | 7 => 161 | 8 => 170
    | 9 => 585 | 10 => 670 | 11 => 607 | 12 => 1398 | 13 => 1055 | 14 => 1364 | 15 => 489 | 16 => 226 | 17 => 61
    | 18 => 720 | 19 => 1085 | 20 => 884 | 21 => 1149 | 22 => 862 | 23 => 433 | 24 => 960 | 25 => 737 | _ => 1160
  | 43 =>
    match r with
    | 0 => 135 | 1 => 634 | 2 => 751 | 3 => 174 | 4 => 497 | 5 => 248 | 6 => 849 | 7 => 514 | 8 => 43
    | 9 => 792 | 10 => 851 | 11 => 578 | 12 => 861 | 13 => 16 | 14 => 253 | 15 => 870 | 16 => 827 | 17 => 206
    | 18 => 657 | 19 => 112 | 20 => 409 | 21 => 1380 | 22 => 911 | 23 => 104 | 24 => 723 | 25 => 316 | _ => 997
  | 44 =>
    match r with
    | 0 => 378 | 1 => 131 | 2 => 1244 | 3 => 87 | 4 => 142 | 5 => 1045 | 6 => 294 | 7 => 431 | 8 => 224
    | 9 => 693 | 10 => 562 | 11 => 1039 | 12 => 642 | 13 => 839 | 14 => 932 | 15 => 111 | 16 => 1090 | 17 => 7
    | 18 => 936 | 19 => 383 | 20 => 1424 | 21 => 285 | 22 => 1240 | 23 => 1351 | 24 => 690 | 25 => 1007 | _ => 1214
  | 45 =>
    match r with
    | 0 => 243 | 1 => 526 | 2 => 1183 | 3 => 876 | 4 => 281 | 5 => 1274 | 6 => 471 | 7 => 1378 | 8 => 1447
    | 9 => 1008 | 10 => 149 | 11 => 1118 | 12 => 1455 | 13 => 394 | 14 => 1171 | 15 => 600 | 16 => 1097 | 17 => 260
    | 18 => 765 | 19 => 4 | 20 => 841 | 21 => 624 | 22 => 695 | 23 => 1130 | 24 => 345 | 25 => 1180 | _ => 943
  | 46 =>
    match r with
    | 0 => 594 | 1 => 887 | 2 => 326 | 3 => 681 | 4 => 520 | 5 => 505 | 6 => 24 | 7 => 701 | 8 => 278
    | 9 => 801 | 10 => 454 | 11 => 13 | 12 => 1344 | 13 => 623 | 14 => 500 | 15 => 1191 | 16 => 496 | 17 => 1411
    | 18 => 1152 | 19 => 1139 | 20 => 506 | 21 => 879 | 22 => 160 | 23 => 811 | 24 => 420 | 25 => 1277 | _ => 1268
  | 47 =>
    match r with
    | 0 => 351 | 1 => 418 | 2 => 157 | 3 => 120 | 4 => 65 | 5 => 842 | 6 => 93 | 7 => 784 | 8 => 1393
    | 9 => 1224 | 10 => 905 | 11 => 200 | 12 => 591 | 13 => 772 | 14 => 631 | 15 => 330 | 16 => 1367 | 17 => 314
    | 18 => 873 | 19 => 1354 | 20 => 1273 | 21 => 1326 | 22 => 479 | 23 => 698 | 24 => 1425 | 25 => 586 | _ => 889
  | 48 =>
    match r with
    | 0 => 810 | 1 => 185 | 2 => 866 | 3 => 1275 | 4 => 898 | 5 => 1423 | 6 => 1212 | 7 => 971 | 8 => 332
    | 9 => 909 | 10 => 346 | 11 => 445 | 12 => 588 | 13 => 407 | 14 => 68 | 15 => 813 | 16 => 1360 | 17 => 1357
    | 18 => 1368 | 19 => 437 | 20 => 1046 | 21 => 15 | 22 => 538 | 23 => 271 | 24 => 150 | 25 => 89 | _ => 1322
  | 49 =>
    match r with
    | 0 => 459 | 1 => 310 | 2 => 589 | 3 => 822 | 4 => 1307 | 5 => 410 | 6 => 1173 | 7 => 190 | 8 => 1339
    | 9 => 1440 | 10 => 203 | 11 => 740 | 12 => 1185 | 13 => 1150 | 14 => 91 | 15 => 60 | 16 => 179 | 17 => 368
    | 18 => 981 | 19 => 1246 | 20 => 247 | 21 => 570 | 22 => 263 | 23 => 266 | 24 => 1047 | 25 => 1450 | _ => 835
  | 50 =>
    match r with
    | 0 => 1026 | 1 => 941 | 2 => 1406 | 3 => 411 | 4 => 1276 | 5 => 883 | 6 => 942 | 7 => 1241 | 8 => 386
    | 9 => 1017 | 10 => 238 | 11 => 877 | 12 => 1290 | 13 => 191 | 14 => 1094 | 15 => 435 | 16 => 766 | 17 => 1303
    | 18 => 126 | 19 => 1193 | 20 => 128 | 21 => 609 | 22 => 916 | 23 => 1189 | 24 => 1338 | 25 => 359 | _ => 1376
  | 51 =>
    match r with
    | 0 => 567 | 1 => 202 | 2 => 1021 | 3 => 66 | 4 => 1091 | 5 => 1436 | 6 => 795 | 7 => 1054 | 8 => 1285
    | 9 => 198 | 10 => 959 | 11 => 1280 | 12 => 321 | 13 => 70 | 14 => 1009 | 15 => 1248 | 16 => 449 | 17 => 422
    | 18 => 1089 | 19 => 1138 | 20 => 679 | 21 => 1272 | 22 => 47 | 23 => 1292 | 24 => 669 | 25 => 856 | _ => 781
  | 52 =>
    match r with
    | 0 => 1242 | 1 => 239 | 2 => 488 | 3 => 1005 | 4 => 196 | 5 => 343 | 6 => 672 | 7 => 53 | 8 => 440
    | 9 => 1125 | 10 => 130 | 11 => 1309 | 12 => 534 | 13 => 1433 | 14 => 662 | 15 => 57 | 16 => 172 | 17 => 1249
    | 18 => 342 | 19 => 491 | 20 => 668 | 21 => 1203 | 22 => 1294 | 23 => 649 | 24 => 1068 | 25 => 629 | _ => 1430
  | _ =>
    match r with
    | 0 => 675 | 1 => 94 | 2 => 1453 | 3 => 768 | 4 => 875 | 5 => 1004 | 6 => 417 | 7 => 460 | 8 => 1231
    | 9 => 414 | 10 => 257 | 11 => 362 | 12 => 915 | 13 => 448 | 14 => 469 | 15 => 978 | 16 => 719 | 17 => 476
    | 18 => 1197 | 19 => 1030 | 20 => 1111 | 21 => 516 | 22 => 1289 | 23 => 860 | 24 => 291 | 25 => 262 | _ => 727

private def invMarkov7ByIdx (idx : Nat) : Nat :=
  invMarkov7Aux (idx / 27) (idx % 27)

private def pow2Mod6561Aux : Nat -> Nat -> Nat
  | 0, _ => 1
  | fuel + 1, e =>
    if e = 0 then 1
    else
      let half := pow2Mod6561Aux fuel (e / 2)
      let sq := (half * half) % 6561
      if e % 2 = 0 then sq else (2 * sq) % 6561

private theorem pow2Mod6561Aux_eq :
    ∀ (fuel e : Nat), e < 2 ^ fuel -> pow2Mod6561Aux fuel e = 2 ^ e % 6561
  | 0, e, hlt => by
    have he0 : e = 0 := by simp at hlt; exact hlt
    subst he0; rfl
  | fuel + 1, e, hlt => by
    simp only [pow2Mod6561Aux]
    by_cases he0 : e = 0
    · subst he0; rfl
    · simp only [he0, ite_false]
      have hlt_half : e / 2 < 2 ^ fuel := by
        rw [Nat.pow_succ] at hlt; omega
      have ih := pow2Mod6561Aux_eq fuel (e / 2) hlt_half
      have he_div : 2 * (e / 2) + e % 2 = e := Nat.div_add_mod e 2
      have hsq : ((2 ^ (e / 2) % 6561) * (2 ^ (e / 2) % 6561)) % 6561 =
          2 ^ (2 * (e / 2)) % 6561 := by
        rw [← Nat.mul_mod, ← Nat.pow_add, show e / 2 + e / 2 = 2 * (e / 2) by omega]
      by_cases hev : e % 2 = 0
      · simp only [hev, ite_true, ih, hsq]
        have he_eq : 2 * (e / 2) = e := by omega
        rw [he_eq]
      · simp only [hev, ite_false, ih, hsq]
        have he_eq : 2 * (e / 2) + 1 = e := by omega
        calc
          (2 * (2 ^ (2 * (e / 2)) % 6561)) % 6561
              = ((2 % 6561) * (2 ^ (2 * (e / 2)) % 6561)) % 6561 := rfl
          _ = (2 * 2 ^ (2 * (e / 2))) % 6561 := (Nat.mul_mod 2 _ 6561).symm
          _ = 2 ^ (2 * (e / 2) + 1) % 6561 := by
                rw [Nat.pow_succ, Nat.mul_comm _ 2]
          _ = 2 ^ e % 6561 := by rw [he_eq]

set_option maxRecDepth 65536 in
private theorem markovShiftTrue7_grid_cert :
    ∀ (hi : Fin 54) (lo : Fin 27),
      let x := 27 * hi.val + lo.val
      let t := markov7Aux hi.val lo.val
      t < 4373 ∧
      (t % 6 = 1 ∨ t % 6 = 3) ∧
      pow2Mod6561Aux 13 (t + 1) = (3 * pow2Mod6561Aux 13 x + 1) % 6561 ∧
      invMarkov7ByIdx (2 * (t / 6) + (if t % 6 == 3 then 1 else 0)) = x := by
  decide

private theorem markovShiftTrue7_table_cert (x : Fin 1458) :
    let t := markovShiftTrue7Mod4374Table x
    t < 4373 ∧
    (t % 6 = 1 ∨ t % 6 = 3) ∧
    pow2Mod6561Aux 13 (t + 1) = (3 * pow2Mod6561Aux 13 x.val + 1) % 6561 ∧
    invMarkov7ByIdx (2 * (t / 6) + (if t % 6 == 3 then 1 else 0)) = x.val := by
  have hhi : x.val / 27 < 54 := by have := x.isLt; omega
  have hlo : x.val % 27 < 27 := Nat.mod_lt x.val (by decide)
  have hg := markovShiftTrue7_grid_cert ⟨x.val / 27, hhi⟩ ⟨x.val % 27, hlo⟩
  dsimp only at hg ⊢
  rwa [Nat.div_add_mod x.val 27] at hg

private theorem markovShiftTrue7_eq_table (x : Fin 1458) :
    markovShiftTrue 7 x.val % 4374 = markovShiftTrue7Mod4374Table x := by
  rcases markovShiftTrue7_table_cert x with ⟨ht_lt, _, hpow, _⟩
  let t := markovShiftTrue7Mod4374Table x
  change t < 4373 at ht_lt
  rw [pow2Mod6561Aux_eq 13 (t + 1) (by omega),
      pow2Mod6561Aux_eq 13 x.val (by have := x.isLt; omega)] at hpow
  have h3_rhs : (3 * (2 ^ x.val % 6561) + 1) % 6561 = (3 * 2 ^ x.val + 1) % 6561 := by
    have hm : (3 * (2 ^ x.val % 6561)) % 6561 = (3 * 2 ^ x.val) % 6561 := by
      calc
        (3 * (2 ^ x.val % 6561)) % 6561
            = ((3 % 6561) * (2 ^ x.val % 6561)) % 6561 := rfl
        _ = (3 * 2 ^ x.val) % 6561 := (Nat.mul_mod 3 _ 6561).symm
    rw [Nat.add_mod, hm, ← Nat.add_mod]
  rw [h3_rhs] at hpow
  have hr_n3 : (3 * 2 ^ x.val + 1) % 3 ≠ 0 := by omega
  rcases dlog2ModPow3_spec 8 (3 * 2 ^ x.val + 1) (by decide) hr_n3 with ⟨he_lt, he_mod⟩
  have he_eq : dlog2ModPow3 8 (3 * 2 ^ x.val + 1) = t + 1 :=
    pow2_inj_mod_pow3_w8 8 _ (t + 1) (by decide) he_lt (by omega)
      (by simpa using he_mod.trans hpow.symm)
  unfold markovShiftTrue
  rw [show (7 : Nat) + 1 = 8 from rfl, he_eq, show t + 1 - 1 = t by omega]
  exact Nat.mod_eq_of_lt (by omega)

private theorem markovShiftTrue7_table_inj (x1 x2 : Fin 1458)
    (heq : markovShiftTrue7Mod4374Table x1 = markovShiftTrue7Mod4374Table x2) :
    x1 = x2 := by
  have hi1 := (markovShiftTrue7_table_cert x1).2.2.2
  have hi2 := (markovShiftTrue7_table_cert x2).2.2.2
  rw [heq] at hi1
  exact Fin.ext (hi1.symm.trans hi2)

private theorem markovShiftTrue7_table_mem (x : Fin 1458) :
    markovShiftTrue7Mod4374Table x ∈ survivingMod4374List := by
  rcases markovShiftTrue7_table_cert x with ⟨ht_lt, hm6, _, _⟩
  exact (mem_survivingMod4374List_iff _).mpr ⟨by omega, hm6⟩

/-- High-weight (`w(pref_9) ≥ 7`, `22 / 27` classes) vs low-weight (`w(pref_9) = 6`, `5 / 27` classes)
    mod-`512` surviving prefix predicates (`Branch P5.3`, `W14_H4`). -/
def isHighWeight7SurvivingMod512Bool (y : Nat) : Bool :=
  isSurvivingMod512Bool (y % 512) && decide (parityWeight (parityOfIter 9 (y % 512)) ≥ 7)

def isLowWeight6SurvivingMod512Bool (y : Nat) : Bool :=
  isSurvivingMod512Bool (y % 512) && decide (parityWeight (parityOfIter 9 (y % 512)) = 6)

def highWeight7Mod512Residues22 : List Nat :=
  survivingMod512Residues27.filter isHighWeight7SurvivingMod512Bool

def lowWeight6Mod512Residues5 : List Nat :=
  survivingMod512Residues27.filter isLowWeight6SurvivingMod512Bool

private theorem take_drop_split_eq_w14 :
    ∀ (k : Nat) (xs : List Bool), xs.take k ++ xs.drop k = xs
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, x :: xs => by
    simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append,
               take_drop_split_eq_w14 k xs]

private theorem take_len_of_ge_w14 :
    ∀ (k : Nat) (xs : List Bool), k ≤ xs.length -> (xs.take k).length = k
  | 0, _, _ => rfl
  | _ + 1, [], h => by simp at h
  | k + 1, _ :: xs, h => by
    simp only [List.length_cons] at h
    simp only [List.take_succ_cons, List.length_cons, take_len_of_ge_w14 k xs (by omega)]

private theorem len10_core_mod512_prefix9_w14
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

set_option exponentiation.threshold 4096 in
set_option maxRecDepth 131072 in
/--
  Theorem W14.4a (`markovShift_mod4374_bijection_and_prefix22_weight8_dichotomy`,
  `zero custom axioms`):
  Complete Mod-`4374` (`2 * 3^7`) Markov Bijection onto `1458` Surviving Classes, Exact `22 + 5 = 27`
  Mod-`512` Prefix-Weight-`8` Dichotomy (`w(u) ≥ 8` Automatic Lock vs Low-Prefix `w(u) = 7` Escape
  `ZPOS_DYADIC_LEN10_WEIGHT7_LOW_PREFIX_ESCAPE`), Mod-`4374` Suffix Locks (`2187` & `729`), &
  `3 ^ (w - 8)` (`j = 7`) Multi-Step Fiber Equidistribution (`Branch P5.3`, `W14_H4`).
-/
theorem markovShift_mod4374_bijection_and_prefix22_weight8_dichotomy :
    ((∀ (w a : Nat), w ≥ 7 -> a < 2 * 3 ^ (w - 1) ->
        markovShiftTrue w a % 4374 = markovShiftTrue 7 (a % 1458) % 4374) ∧
     survivingMod4374List.length = 1458 ∧
     (∀ x1 x2 : Fin 1458,
        markovShiftTrue 7 x1.val % 4374 = markovShiftTrue 7 x2.val % 4374 -> x1 = x2) ∧
     (∀ x : Fin 1458,
        markovShiftTrue 7 x.val % 4374 ∈ survivingMod4374List)) ∧
    (highWeight7Mod512Residues22.length = 22 ∧
     lowWeight6Mod512Residues5.length = 5 ∧
     (∀ r : Fin 512, isSurvivingMod512Bool r.val = true ->
        (isHighWeight7SurvivingMod512Bool r.val = true ∧ isLowWeight6SurvivingMod512Bool r.val = false) ∨
        (isLowWeight6SurvivingMod512Bool r.val = true ∧ isHighWeight7SurvivingMod512Bool r.val = false)) ∧
     (∀ u : List Bool, IsCoreParityWord u -> parityWeight u ≥ 8 ->
        canonicalSuffixShift u 1 % 4374 ∈ survivingMod4374List) ∧
     (∀ (u : List Bool) (q : Nat),
        IsCoreParityWord u -> u.length ≥ 10 ->
        isHighWeight7SurvivingMod512Bool (exactBackwardQuotient 1 u q) = true ->
        parityWeight u ≥ 8 ∧ canonicalSuffixShift u 1 % 4374 ∈ survivingMod4374List) ∧
     (let u_esc : List Bool := [true, true, false, true, true, true, false, true, false, true]
      u_esc.length = 10 ∧
      parityWeight u_esc = 7 ∧
      IsFirstHitOnePair u_esc 0 ∧
      IsSurvivingMod373248Class (exactBackwardQuotient 1 u_esc 0) ∧
      isLowWeight6SurvivingMod512Bool (exactBackwardQuotient 1 u_esc 0) = true)) ∧
    ((∀ pref : List Bool, parityWeight pref ≥ 1 ->
        canonicalSuffixShift (pref ++ List.replicate 7 true) 1 % 4374 = 2187 ∨
        canonicalSuffixShift (pref ++ List.replicate 7 true) 1 % 4374 = 729) ∧
     (∀ pref : List Bool,
        canonicalSuffixShift (pref ++ List.replicate 8 true) 1 % 4374 = 2187 ∧
        canonicalSuffixShift (pref ++ [true, false, true, true, true, true, true, true, true]) 1 % 4374 = 729)) ∧
    (∀ (tail : List Bool) (w r0 : Nat),
      w ≥ 8 -> r0 < 4374 ->
      let Mk := 2 * 3 ^ (7 + parityWeight tail)
      let N := 3 ^ (w - 8)
      let base := iterMarkovShift tail w r0 % Mk
      (∀ t : Nat, t < N ->
        ∃ q : Nat, q < N ∧ iterMarkovShift tail w (r0 + 4374 * t) = base + Mk * q) ∧
      (∀ q : Nat, q < N ->
        ∃ t : Nat, t < N ∧
          iterMarkovShift tail w (r0 + 4374 * t) = base + Mk * q ∧
          ∀ t' : Nat, t' < N ->
            iterMarkovShift tail w (r0 + 4374 * t') = base + Mk * q -> t' = t)) := by
  have hcongr4374 : ∀ (w a : Nat), w ≥ 7 -> a < 2 * 3 ^ (w - 1) ->
      markovShiftTrue w a % 4374 = markovShiftTrue 7 (a % 1458) % 4374 := by
    intro w a hw7 ha_lt
    have hr_lt : a % 1458 < 2 * 3 ^ (7 - 1) := Nat.mod_lt a (by decide)
    exact markovShiftTrue_contraction_mod_pow3 6 w 7 a (a % 1458)
      (by omega) (by decide) ha_lt hr_lt (by simp)
  have hinj1458 : ∀ x1 x2 : Fin 1458,
      markovShiftTrue 7 x1.val % 4374 = markovShiftTrue 7 x2.val % 4374 -> x1 = x2 := by
    intro x1 x2 heq
    rw [markovShiftTrue7_eq_table x1, markovShiftTrue7_eq_table x2] at heq
    exact markovShiftTrue7_table_inj x1 x2 heq
  have hmem1458 : ∀ x : Fin 1458, markovShiftTrue 7 x.val % 4374 ∈ survivingMod4374List := by
    intro x
    rw [markovShiftTrue7_eq_table x]
    exact markovShiftTrue7_table_mem x
  have hconf8 : ∀ u : List Bool, IsCoreParityWord u -> parityWeight u ≥ 8 ->
      canonicalSuffixShift u 1 % 4374 ∈ survivingMod4374List := by
    intro u hu hw8
    rcases list_eq_append_true_of_reverse_head u hu.2 with ⟨v, rfl⟩
    have hw_v : parityWeight v ≥ 7 := by
      rw [parityWeight_append] at hw8
      have h1 : parityWeight [true] = 1 := rfl
      rw [h1] at hw8; omega
    have hrec : canonicalSuffixShift (v ++ [true]) 1 =
        markovShiftTrue (parityWeight v) (canonicalSuffixShift v 1) :=
      (canonicalSuffixShift_append_markov_recurrence.2.2 v (by omega)).2.2.1
    have ha_lt := (canonicalSuffixShift_spec_unique v 1 (by omega) (by decide)).1
    rw [hrec, hcongr4374 (parityWeight v) (canonicalSuffixShift v 1) hw_v ha_lt]
    exact hmem1458 ⟨canonicalSuffixShift v 1 % 1458, Nat.mod_lt _ (by decide)⟩
  have h512_dich : ∀ r : Fin 512, isSurvivingMod512Bool r.val = true ->
      (isHighWeight7SurvivingMod512Bool r.val = true ∧ isLowWeight6SurvivingMod512Bool r.val = false) ∨
      (isLowWeight6SurvivingMod512Bool r.val = true ∧ isHighWeight7SurvivingMod512Bool r.val = false) := by
    have hgrid : ∀ (hi : Fin 8) (lo : Fin 64),
        let rv := 64 * hi.val + lo.val
        isSurvivingMod512Bool rv = true ->
        (isHighWeight7SurvivingMod512Bool rv = true ∧ isLowWeight6SurvivingMod512Bool rv = false) ∨
        (isLowWeight6SurvivingMod512Bool rv = true ∧ isHighWeight7SurvivingMod512Bool rv = false) := by
      decide
    intro r hr
    have hhi : r.val / 64 < 8 := by have := r.isLt; omega
    have hlo : r.val % 64 < 64 := Nat.mod_lt r.val (by decide)
    have hg := hgrid ⟨r.val / 64, hhi⟩ ⟨r.val % 64, hlo⟩
    dsimp only at hg
    rw [Nat.div_add_mod r.val 64] at hg
    exact hg hr
  have hlen10_high : ∀ (u : List Bool) (q : Nat),
      IsCoreParityWord u -> u.length ≥ 10 ->
      isHighWeight7SurvivingMod512Bool (exactBackwardQuotient 1 u q) = true ->
      parityWeight u ≥ 8 ∧ canonicalSuffixShift u 1 % 4374 ∈ survivingMod4374List := by
    intro u q hu hlen10 hhigh
    rcases list_eq_append_true_of_reverse_head u hu.2 with ⟨pre, rfl⟩
    have hpre_ge9 : pre.length ≥ 9 := by
      rw [List.length_append, List.length_singleton] at hlen10; omega
    let p9 := pre.take 9
    let fb := pre.drop 9
    have hp9_len : p9.length = 9 := take_len_of_ge_w14 9 pre hpre_ge9
    have hpre_sp : p9 ++ fb = pre := take_drop_split_eq_w14 9 pre
    have hu' : IsCoreParityWord (p9 ++ fb ++ [true]) := by rwa [hpre_sp]
    have hp9_eq : parityOfIter 9 (exactBackwardQuotient 1 (p9 ++ fb ++ [true]) q % 512) = p9 :=
      len10_core_mod512_prefix9_w14 p9 fb q hp9_len hu'
    rw [hpre_sp] at hp9_eq
    unfold isHighWeight7SurvivingMod512Bool at hhigh
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hhigh
    have hhigh2 := hhigh.2
    have hw_p9 : parityWeight p9 ≥ 7 := by rwa [hp9_eq] at hhigh2
    have hw8 : parityWeight (pre ++ [true]) ≥ 8 := by
      rw [← hpre_sp, parityWeight_append, parityWeight_append]
      have h1 : parityWeight [true] = 1 := rfl
      rw [h1]; omega
    exact ⟨hw8, hconf8 (pre ++ [true]) hu hw8⟩
  have hesc_cert :
      let u_esc : List Bool := [true, true, false, true, true, true, false, true, false, true]
      u_esc.length = 10 ∧
      parityWeight u_esc = 7 ∧
      IsFirstHitOnePair u_esc 0 ∧
      IsSurvivingMod373248Class (exactBackwardQuotient 1 u_esc 0) ∧
      isLowWeight6SurvivingMod512Bool (exactBackwardQuotient 1 u_esc 0) = true := by
    dsimp only
    let u_esc : List Bool := [true, true, false, true, true, true, false, true, false, true]
    have hfh_esc : IsFirstHitOnePair u_esc 0 :=
      (first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.2 u_esc ⟨rfl, rfl⟩).mpr (by decide)
    have hb_surv : isSurvivingMod373248Bool (exactBackwardQuotient 1 u_esc 0) = true := by decide
    exact ⟨rfl, rfl, hfh_esc, isSurvivingMod373248Bool_imp_class _ hb_surv, by decide⟩
  refine ⟨⟨hcongr4374, by decide, hinj1458, hmem1458⟩,
          ⟨rfl, rfl, h512_dich, hconf8, hlen10_high, hesc_cert⟩, ⟨?_, ?_⟩, ?_⟩
  · intro pref hwp
    let t7 : List Bool := List.replicate 7 true
    have hap1 := iterMarkovShift_append_canonical t7 pref hwp
    have ha_lt := (canonicalSuffixShift_spec_unique pref 1 hwp (by decide)).1
    by_cases hpar : canonicalSuffixShift pref 1 % 2 = 0
    · right
      have hbase0 : canonicalSuffixShift [true, false] 1 % 2 = 0 := by decide
      have hap0 := iterMarkovShift_append_canonical t7 [true, false] (by decide)
      change canonicalSuffixShift ([true, false] ++ t7) 1 =
        iterMarkovShift t7 1 (canonicalSuffixShift [true, false] 1) at hap0
      have hc := iterMarkovShift_congr_mod_pow3 t7 0 (parityWeight pref) 1
        (canonicalSuffixShift pref 1) (canonicalSuffixShift [true, false] 1)
        hwp (by decide) ha_lt (by decide)
        (by simp only [Nat.pow_zero, Nat.mul_one]; exact hpar.trans hbase0.symm)
      rw [← hap1, ← hap0] at hc
      have hv : canonicalSuffixShift ([true, false] ++ t7) 1 % 4374 = 729 := by decide
      exact hc.trans hv
    · left
      have hodd : canonicalSuffixShift pref 1 % 2 = 1 := by omega
      have hbase1 : canonicalSuffixShift [true] 1 % 2 = 1 := by decide
      have hap1' := iterMarkovShift_append_canonical t7 [true] (by decide)
      change canonicalSuffixShift ([true] ++ t7) 1 =
        iterMarkovShift t7 1 (canonicalSuffixShift [true] 1) at hap1'
      have hc := iterMarkovShift_congr_mod_pow3 t7 0 (parityWeight pref) 1
        (canonicalSuffixShift pref 1) (canonicalSuffixShift [true] 1)
        hwp (by decide) ha_lt (by decide)
        (by simp only [Nat.pow_zero, Nat.mul_one]; exact hodd.trans hbase1.symm)
      rw [← hap1, ← hap1'] at hc
      have hv : canonicalSuffixShift ([true] ++ t7) 1 % 4374 = 2187 := by decide
      exact hc.trans hv
  · intro pref
    have ha1 := first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.1 8 pref (by decide)
    have ha2 := canonicalSuffixShift_mod18_and_pow3_memory_annihilation.2.1 7 pref
      [true, false, true, true, true, true, true, true, true] (by decide)
    have hv2 : canonicalSuffixShift [true, false, true, true, true, true, true, true, true] 1 % 4374 = 729 := by
      decide
    exact ⟨by simpa using ha1, by simpa using ha2.trans hv2⟩
  · intro tail w r0 hw8 hr0
    have hm4374 : (2 : Nat) * 3 ^ 7 = 4374 := by decide
    have hw_sub : w - 1 - 7 = w - 8 := by omega
    have heq := markovShift_mod18_bijection_and_multistep_fiber_equidistribution.2.2
      tail 7 w r0 (by omega) (by rw [hm4374]; exact hr0)
    dsimp only at heq ⊢
    rwa [hm4374, hw_sub] at heq

-- ----------------------------------------------------------------------------
-- Section 3B: Explicit Three-Zero-Run Family `uThreeZero` / `uWinQuad` &
--             Unconditional Quadratic Dyadic-Window Occupancy (`≥ R^2`, `W14_H4`)
-- ----------------------------------------------------------------------------

/-- Explicit three-zero-run core parity word `1^9 ++ 0^k1 ++ [1] ++ 0^k2 ++ [1] ++ 0^k3 ++ [1]`
    of weight `12` and length `12 + k1 + k2 + k3`. -/
def uThreeZero (k1 k2 k3 : Nat) : List Bool :=
  List.replicate 9 true ++ List.replicate k1 false ++ [true] ++
    List.replicate k2 false ++ [true] ++ List.replicate k3 false ++ [true]

/-- Two-index `(j1, j2)` 2-adic/3-adic carry-decoded surviving `Mod373248` first-hit `q = 0`
    family inside `[2^M, 2^(M+1))` at scale `L = M + 17`, weight `w = 12`, and shift `a = 3`. -/
def uWinQuad (M j1 j2 : Nat) : List Bool :=
  let S := M + 5
  let rhs15 := (5 * 2 ^ (11 + S) - (349686 + 1536 * 2 ^ (2 * j1))) % 3 ^ 15
  let e_base := dlog2ShiftModPow3 15 1024 rhs15
  let t := e_base + (j1 + j2 + 1) * 9565938
  uThreeZero (2 * j1) (t - 2 * j1) (S - t)

set_option maxRecDepth 65536 in
private theorem uThreeZero_core_len_wt_carry (k1 k2 k3 : Nat) :
    IsCoreParityWord (uThreeZero k1 k2 k3) ∧
    (uThreeZero k1 k2 k3).length = 12 + (k1 + k2 + k3) ∧
    parityWeight (uThreeZero k1 k2 k3) = 12 ∧
    affineCarry (uThreeZero k1 k2 k3) =
      517617 + 4608 * 2 ^ k1 + 3072 * 2 ^ (k1 + k2) + 2 ^ (11 + (k1 + k2 + k3)) := by
  let p9 := List.replicate 9 true
  let s1 := p9 ++ List.replicate k1 false
  let s2 := s1 ++ [true]
  let s3 := s2 ++ List.replicate k2 false
  let s4 := s3 ++ [true]
  let s5 := s4 ++ List.replicate k3 false
  have hp9_len : p9.length = 9 := rfl
  have hp9_wt : parityWeight p9 = 9 := rfl
  have hp9_car : affineCarry p9 = 19171 := by decide
  rcases affineCarry_append_replicate_false p9 k1 with ⟨hs1_wt, hs1_car⟩
  change parityWeight s1 = parityWeight p9 at hs1_wt
  change affineCarry s1 = affineCarry p9 at hs1_car
  rw [hp9_wt] at hs1_wt; rw [hp9_car] at hs1_car
  have hs1_len : s1.length = 9 + k1 := by
    dsimp only [s1]; rw [List.length_append, hp9_len, List.length_replicate]
  have hs2_wt : parityWeight s2 = 10 := by
    dsimp only [s2]; rw [parityWeight_append, hs1_wt]; rfl
  have hs2_len : s2.length = 10 + k1 := by
    dsimp only [s2]; rw [List.length_append, hs1_len, List.length_singleton]; omega
  have hs2_car : affineCarry s2 = 57513 + 512 * 2 ^ k1 := by
    dsimp only [s2]
    rw [affineCarry_append, hs1_car, hs1_len, Nat.pow_add 2 9 k1]
    have hc1 : affineCarry [true] = 1 := rfl
    have hw1 : parityWeight [true] = 1 := rfl
    rw [hc1, hw1]; omega
  rcases affineCarry_append_replicate_false s2 k2 with ⟨hs3_wt, hs3_car⟩
  change parityWeight s3 = parityWeight s2 at hs3_wt
  change affineCarry s3 = affineCarry s2 at hs3_car
  rw [hs2_wt] at hs3_wt; rw [hs2_car] at hs3_car
  have hs3_len : s3.length = 10 + (k1 + k2) := by
    dsimp only [s3]; rw [List.length_append, hs2_len, List.length_replicate]; omega
  have hs4_wt : parityWeight s4 = 11 := by
    dsimp only [s4]; rw [parityWeight_append, hs3_wt]; rfl
  have hs4_len : s4.length = 11 + (k1 + k2) := by
    dsimp only [s4]; rw [List.length_append, hs3_len, List.length_singleton]; omega
  have hs4_car : affineCarry s4 = 172539 + 1536 * 2 ^ k1 + 1024 * 2 ^ (k1 + k2) := by
    dsimp only [s4]
    rw [affineCarry_append, hs3_car, hs3_len, Nat.pow_add 2 10 (k1 + k2)]
    have hc1 : affineCarry [true] = 1 := rfl
    have hw1 : parityWeight [true] = 1 := rfl
    rw [hc1, hw1]; omega
  rcases affineCarry_append_replicate_false s4 k3 with ⟨hs5_wt, hs5_car⟩
  change parityWeight s5 = parityWeight s4 at hs5_wt
  change affineCarry s5 = affineCarry s4 at hs5_car
  rw [hs4_wt] at hs5_wt; rw [hs4_car] at hs5_car
  have hs5_len : s5.length = 11 + (k1 + k2 + k3) := by
    dsimp only [s5]; rw [List.length_append, hs4_len, List.length_replicate]; omega
  have hu_eq : uThreeZero k1 k2 k3 = s5 ++ [true] := rfl
  have hcore : IsCoreParityWord (uThreeZero k1 k2 k3) := by
    refine ⟨rfl, ?_⟩
    rw [hu_eq, List.reverse_append]; rfl
  have hlen : (uThreeZero k1 k2 k3).length = 12 + (k1 + k2 + k3) := by
    rw [hu_eq, List.length_append, hs5_len, List.length_singleton]; omega
  have hwt : parityWeight (uThreeZero k1 k2 k3) = 12 := by
    rw [hu_eq, parityWeight_append, hs5_wt]; rfl
  have hcar : affineCarry (uThreeZero k1 k2 k3) =
      517617 + 4608 * 2 ^ k1 + 3072 * 2 ^ (k1 + k2) + 2 ^ (11 + (k1 + k2 + k3)) := by
    rw [hu_eq, affineCarry_append, hs5_car, hs5_len]
    have hc1 : affineCarry [true] = 1 := rfl
    have hw1 : parityWeight [true] = 1 := rfl
    rw [hc1, hw1]; omega
  exact ⟨hcore, hlen, hwt, hcar⟩

private theorem replicate_false_cons_true_inj_w14 :
    ∀ (a b : Nat) (xs ys : List Bool),
      List.replicate a false ++ (true :: xs) = List.replicate b false ++ (true :: ys) ->
      a = b ∧ xs = ys
  | 0, 0, xs, ys, h => ⟨rfl, by simpa using h⟩
  | 0, b + 1, xs, ys, h => by simp [List.replicate_succ] at h
  | a + 1, 0, xs, ys, h => by simp [List.replicate_succ] at h
  | a + 1, b + 1, xs, ys, h => by
    simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
    rcases replicate_false_cons_true_inj_w14 a b xs ys h with ⟨hab, hxy⟩
    exact ⟨congrArg Nat.succ hab, hxy⟩

private theorem uThreeZero_inj_k1_k2 (a1 a2 a3 b1 b2 b3 : Nat)
    (heq : uThreeZero a1 a2 a3 = uThreeZero b1 b2 b3) :
    a1 = b1 ∧ a2 = b2 := by
  have hsp : ∀ k1 k2 k3 : Nat,
      uThreeZero k1 k2 k3 =
        List.replicate 9 true ++
          (List.replicate k1 false ++ (true :: (List.replicate k2 false ++ (true :: (List.replicate k3 false ++ [true]))))) := by
    intro k1 k2 k3; unfold uThreeZero; simp [List.append_assoc]
  rw [hsp a1 a2 a3, hsp b1 b2 b3] at heq
  have htail1 :
      List.replicate a1 false ++ (true :: (List.replicate a2 false ++ (true :: (List.replicate a3 false ++ [true])))) =
      List.replicate b1 false ++ (true :: (List.replicate b2 false ++ (true :: (List.replicate b3 false ++ [true])))) :=
    (list_append_inj_left_eq_len _ _ _ _ rfl heq).2
  rcases replicate_false_cons_true_inj_w14 a1 b1 _ _ htail1 with ⟨ha1, htail2⟩
  rcases replicate_false_cons_true_inj_w14 a2 b2 _ _ htail2 with ⟨ha2, _⟩
  exact ⟨ha1, ha2⟩

private theorem isSurvivingMod373248_of_511_and_1_w14 (y : Nat)
    (h512 : y % 512 = 511) (h81 : y % 81 = 1) :
    isSurvivingMod373248Bool y = true ∧ IsSurvivingMod373248Class y := by
  let r729 := y % 729
  have hr_lt : r729 < 729 := Nat.mod_lt y (by decide)
  have hr_m81 : r729 % 81 = 1 := by
    dsimp only [r729]
    have hdvd81 : 81 ∣ 729 := ⟨9, by decide⟩
    rw [Nat.mod_mod_of_dvd y hdvd81, h81]
  have hb729 : isSurvivingMod729Bool (y % 729) = true := by
    change isSurvivingMod729Bool r729 = true
    unfold isSurvivingMod729Bool
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, decide_eq_true_eq]
    omega
  have hb512 : isSurvivingMod512Bool (y % 512) = true := by rw [h512]; decide
  have hb373 : isSurvivingMod373248Bool y = true := by
    unfold isSurvivingMod373248Bool; rw [hb512, hb729]; rfl
  exact ⟨hb373, isSurvivingMod373248Bool_imp_class y hb373⟩

private def eraseAllNatW14 (b : Nat) : List Nat -> List Nat
  | [] => []
  | x :: xs => if x = b then eraseAllNatW14 b xs else x :: eraseAllNatW14 b xs

private theorem mem_eraseAllNatW14_iff (b : Nat) :
    ∀ (xs : List Nat) (v : Nat), v ∈ eraseAllNatW14 b xs ↔ (v ∈ xs ∧ v ≠ b)
  | [], _ => by simp [eraseAllNatW14]
  | x :: xs, v => by
    simp only [eraseAllNatW14]
    by_cases hxb : x = b
    · simp only [hxb, ite_true, mem_eraseAllNatW14_iff b xs v, List.mem_cons]
      constructor
      · rintro ⟨hm, hne⟩; exact ⟨Or.inr hm, hne⟩
      · rintro ⟨rfl | hm, hne⟩
        · exact False.elim (hne rfl)
        · exact ⟨hm, hne⟩
    · simp only [hxb, ite_false, List.mem_cons, mem_eraseAllNatW14_iff b xs v]
      constructor
      · rintro (rfl | ⟨hm, hne⟩)
        · exact ⟨Or.inl rfl, hxb⟩
        · exact ⟨Or.inr hm, hne⟩
      · rintro ⟨rfl | hm, hne⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hm, hne⟩

private theorem eraseAllNatW14_of_not_mem (b : Nat) :
    ∀ (xs : List Nat), b ∉ xs -> eraseAllNatW14 b xs = xs
  | [], _ => rfl
  | x :: xs, hnm => by
    have hxb : x ≠ b := fun h => hnm (h ▸ List.Mem.head _)
    have hnm_xs : b ∉ xs := fun hm => hnm (List.mem_cons_of_mem _ hm)
    simp only [eraseAllNatW14, hxb, ite_false, eraseAllNatW14_of_not_mem b xs hnm_xs]

private theorem nodup_eraseAllNatW14_and_len (b : Nat) :
    ∀ (xs : List Nat),
      NoDupNat xs -> NoDupNat (eraseAllNatW14 b xs) ∧ xs.length ≤ (eraseAllNatW14 b xs).length + 1
  | [], _ => ⟨NoDupNat.nil, by simp [eraseAllNatW14]⟩
  | x :: xs, NoDupNat.cons _ _ hnx hnd => by
    by_cases hxb : x = b
    · subst hxb
      simp only [eraseAllNatW14, ite_true, eraseAllNatW14_of_not_mem x xs hnx, List.length_cons]
      exact ⟨hnd, Nat.le_refl _⟩
    · rcases nodup_eraseAllNatW14_and_len b xs hnd with ⟨hnd_er, hlen_er⟩
      simp only [eraseAllNatW14, hxb, ite_false, List.length_cons]
      have hnx_er : x ∉ eraseAllNatW14 b xs :=
        fun hm => hnx ((mem_eraseAllNatW14_iff b xs x).mp hm).1
      exact ⟨NoDupNat.cons x _ hnx_er hnd_er, by omega⟩

private theorem noDupNat_length_le_of_subset_w14 :
    ∀ (cands xs : List Nat),
      NoDupNat xs -> (∀ y ∈ xs, y ∈ cands) -> xs.length ≤ cands.length
  | [], [], _, _ => Nat.le_refl 0
  | [], x :: _, _, hsub => by cases hsub x (List.Mem.head _)
  | b :: bs, xs, hnd, hsub => by
    rcases nodup_eraseAllNatW14_and_len b xs hnd with ⟨hnd', hlen'⟩
    have hsub' : ∀ y ∈ eraseAllNatW14 b xs, y ∈ bs := by
      intro y hy
      rcases (mem_eraseAllNatW14_iff b xs y).mp hy with ⟨hy_xs, hne⟩
      rcases List.mem_cons.mp (hsub y hy_xs) with rfl | hbs
      · exact False.elim (hne rfl)
      · exact hbs
    have ih := noDupNat_length_le_of_subset_w14 bs (eraseAllNatW14 b xs) hnd' hsub'
    simp only [List.length_cons]; omega

private def descIdxListW14 : Nat -> List Nat
  | 0 => []
  | r + 1 => r :: descIdxListW14 r

private theorem descIdxListW14_spec :
    ∀ r : Nat,
      (descIdxListW14 r).length = r ∧
      NoDupNat (descIdxListW14 r) ∧
      (∀ j ∈ descIdxListW14 r, j < r)
  | 0 => ⟨rfl, NoDupNat.nil, fun _ hm => by cases hm⟩
  | r + 1 => by
    rcases descIdxListW14_spec r with ⟨hlen, hnd, hlt⟩
    have hnot_mem : r ∉ descIdxListW14 r := fun hm => Nat.lt_irrefl r (hlt r hm)
    refine ⟨by simp [descIdxListW14, hlen], NoDupNat.cons r _ hnot_mem hnd, ?_⟩
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hm
    · omega
    · have := hlt j hm; omega

private theorem noDupNat_map_inj_on_w14 (f : Nat -> Nat) :
    ∀ (js : List Nat),
      NoDupNat js ->
      (∀ a ∈ js, ∀ b ∈ js, f a = f b -> a = b) ->
      NoDupNat (js.map f)
  | [], _, _ => NoDupNat.nil
  | j :: js, NoDupNat.cons _ _ hnj hnd, hinj => by
    refine NoDupNat.cons (f j) (js.map f) ?_
      (noDupNat_map_inj_on_w14 f js hnd (fun a ha b hb =>
        hinj a (List.mem_cons_of_mem j ha) b (List.mem_cons_of_mem j hb)))
    intro hm
    rcases List.mem_map.mp hm with ⟨j', hj', heq⟩
    have hj_eq := hinj j' (List.mem_cons_of_mem j hj') j (List.Mem.head _) heq
    exact hnj (hj_eq ▸ hj')

set_option maxRecDepth 131072 in
/--
  Theorem W14.4b (`dyadic_window_three_zero_run_quadratic_occupancy`, `zero custom axioms`):
  Unconditional Three-Zero-Run Surviving Family `uWinQuad M j1 j2` & Quadratic Surviving-Leaf
  Dyadic-Window Occupancy (`≥ R * R` and `≥ R * (R + 1) / 2` for `M ≥ R * 19131876`,
  `Branches P2.2 & P5.3`, `W14_H4`):
  For EVERY target parameter `R ≥ 1` and EVERY dyadic window scale `M ≥ R * 19131876`
  (`19131876 = 4 * 3 ^ 14`):
  1. **Explicit Two-Parameter Surviving First-Hit Family (`∀ j1 < R, ∀ j2 < R`)**:
     Each word `u := uWinQuad M j1 j2` satisfies:
     - `IsFirstHitOnePair u 0`, `u.length = M + 17`, `parityWeight u = 12`, `canonicalSuffixShift u 1 = 3`, AND
     - `y := exactBackwardQuotient 1 u 0` satisfies `y % 512 = 511`, `y % 81 = 1`,
       `IsSurvivingMod373248Class y`, `2 ^ M ≤ y ∧ y < 2 ^ (M + 1)`,
       `y ∈ dyadicWindowSurvivingQ0Leaves (M + 17) M`, and
       `∀ L_max ≥ M + 17, y ∈ dyadicWindowSurvivingQ0Leaves L_max M`!
  2. **Joint Pairwise `(j1, j2)` Leaf Distinctness (`∀ j1, j2, j1', j2' < R`)**:
     `exactBackwardQuotient 1 (uWinQuad M j1 j2) 0 = exactBackwardQuotient 1 (uWinQuad M j1' j2') 0 -> j1 = j1' ∧ j2 = j2'`!
  3. **Unconditional Quadratic Window Occupancy Lower Bound (`∀ L_max ≥ M + 17`)**:
       `(dyadicWindowSurvivingQ0Leaves (M + 17) M).length ≥ R * R` AND
       `∀ L_max ≥ M + 17, (dyadicWindowSurvivingQ0Leaves L_max M).length ≥ R * R ∧
         (dyadicWindowSurvivingQ0Leaves L_max M).length ≥ R * (R + 1) / 2`!
-/
theorem dyadic_window_three_zero_run_quadratic_occupancy
    (R M : Nat) (hR : R ≥ 1) (hM : M ≥ R * 19131876) :
    (∀ j1 j2 : Nat, j1 < R -> j2 < R ->
      let u := uWinQuad M j1 j2
      let y := exactBackwardQuotient 1 u 0
      IsFirstHitOnePair u 0 ∧
      u.length = M + 17 ∧
      parityWeight u = 12 ∧
      canonicalSuffixShift u 1 = 3 ∧
      y % 512 = 511 ∧
      y % 81 = 1 ∧
      IsSurvivingMod373248Class y ∧
      2 ^ M ≤ y ∧ y < 2 ^ (M + 1) ∧
      y ∈ dyadicWindowSurvivingQ0Leaves (M + 17) M ∧
      (∀ L_max : Nat, L_max ≥ M + 17 -> y ∈ dyadicWindowSurvivingQ0Leaves L_max M)) ∧
    (∀ j1 j2 j1' j2' : Nat, j1 < R -> j2 < R -> j1' < R -> j2' < R ->
      exactBackwardQuotient 1 (uWinQuad M j1 j2) 0 =
        exactBackwardQuotient 1 (uWinQuad M j1' j2') 0 ->
      j1 = j1' ∧ j2 = j2') ∧
    ((dyadicWindowSurvivingQ0Leaves (M + 17) M).length ≥ R * R ∧
     ∀ L_max : Nat, L_max ≥ M + 17 ->
       (dyadicWindowSurvivingQ0Leaves L_max M).length ≥ R * R ∧
       (dyadicWindowSurvivingQ0Leaves L_max M).length ≥ R * (R + 1) / 2) := by
  let S := M + 5
  have h312_val : (3 : Nat) ^ 12 = 531441 := by decide
  have hp14_val : 2 * 3 ^ (15 - 1) = 9565938 := by decide
  have h216_val : (2 : Nat) ^ 16 = 65536 := by decide
  have h220_val : (2 : Nat) ^ 20 = 1048576 := by decide
  have hM_ge6 : M ≥ 6 := by
    have hm1 : 1 * 19131876 ≤ R * 19131876 := Nat.mul_le_mul_right 19131876 hR
    rw [Nat.one_mul] at hm1
    exact Nat.le_trans (by decide : 6 ≤ 19131876) (Nat.le_trans hm1 hM)
  have hPM_ge64 : 2 ^ M ≥ 64 := by
    have hc : (2 : Nat) ^ 6 = 64 := by decide
    rw [← hc]; exact pow2_mono_nat hM_ge6
  have hp11S_eq : 2 ^ (11 + S) = 65536 * 2 ^ M := by
    dsimp only [S]
    rw [show 11 + (M + 5) = 16 + M by omega, Nat.pow_add 2 16 M, h216_val]
  have hper_ij : ∀ j1 j2 : Nat, j1 < R -> j2 < R ->
      let u := uWinQuad M j1 j2
      let y := exactBackwardQuotient 1 u 0
      IsFirstHitOnePair u 0 ∧
      u.length = M + 17 ∧
      parityWeight u = 12 ∧
      canonicalSuffixShift u 1 = 3 ∧
      y % 512 = 511 ∧
      y % 81 = 1 ∧
      isSurvivingMod373248Bool y = true ∧
      IsSurvivingMod373248Class y ∧
      2 ^ M ≤ y ∧ y < 2 ^ (M + 1) ∧
      (∀ L_max : Nat, L_max ≥ M + 17 -> y ∈ dyadicWindowSurvivingQ0Leaves L_max M) := by
    intro j1 j2 hj1 hj2
    dsimp only
    let sub_j1 := 349686 + 1536 * 2 ^ (2 * j1)
    let A_num := 5 * 2 ^ (11 + S) - sub_j1
    rcases (⟨A_num % 3 ^ 15, rfl⟩ : ∃ r0 : Nat, r0 = A_num % 3 ^ 15) with ⟨rhs15, hrhs_def⟩
    have hj1_2_lt_M : 2 * j1 < M := by
      have h1 : 2 * j1 < (j1 + 1) * 2 := by omega
      have h2 : (j1 + 1) * 2 ≤ (j1 + 1) * 19131876 :=
        Nat.mul_le_mul_left (j1 + 1) (by decide : 2 ≤ 19131876)
      have h3 : (j1 + 1) * 19131876 ≤ R * 19131876 := Nat.mul_le_mul_right 19131876 (by omega)
      exact Nat.lt_of_lt_of_le h1 (Nat.le_trans h2 (Nat.le_trans h3 hM))
    have hP2j1_le_PM : 2 ^ (2 * j1) ≤ 2 ^ M := pow2_mono_nat (Nat.le_of_lt hj1_2_lt_M)
    have hsub_lt_5p : sub_j1 < 5 * 2 ^ (11 + S) := by
      dsimp only [sub_j1]
      rw [hp11S_eq]
      have h1 : 349686 < 6000 * 2 ^ M :=
        Nat.lt_of_lt_of_le (by decide : 349686 < 6000 * 64) (Nat.mul_le_mul_left 6000 hPM_ge64)
      have h2 : 1536 * 2 ^ (2 * j1) ≤ 1536 * 2 ^ M := Nat.mul_le_mul_left 1536 hP2j1_le_PM
      have h3 : 6000 * 2 ^ M + 1536 * 2 ^ M ≤ 5 * (65536 * 2 ^ M) := by
        rw [← Nat.add_mul, ← Nat.mul_assoc 5 65536]
        exact Nat.mul_le_mul_right (2 ^ M) (by decide : 6000 + 1536 ≤ 5 * 65536)
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_of_lt_of_le h1 h2) h3
    have hrhs_n3 : rhs15 % 3 ≠ 0 := by
      have hA_m3 : A_num % 3 ≠ 0 := by
        have hp_m3 := pow2_mod3_nonzero_w5 (11 + S)
        have hsub_3 : sub_j1 = 3 * (116562 + 512 * 2 ^ (2 * j1)) := by
          dsimp only [sub_j1]; rw [Nat.mul_add, ← Nat.mul_assoc]
        have hrew : 5 * 2 ^ (11 + S) = A_num + 3 * (116562 + 512 * 2 ^ (2 * j1)) := by
          dsimp only [A_num]
          rw [← hsub_3, Nat.sub_add_cancel (Nat.le_of_lt hsub_lt_5p)]
        intro h0
        have hm5 : (5 * 2 ^ (11 + S)) % 3 = 0 := by
          rw [hrew, Nat.add_mul_mod_self_left, h0]
        rw [Nat.mul_mod] at hm5
        have hlt3 : 2 ^ (11 + S) % 3 < 3 := Nat.mod_lt _ (by decide)
        have h12 : 2 ^ (11 + S) % 3 = 1 ∨ 2 ^ (11 + S) % 3 = 2 := by
          clear hrhs_def h312_val hp14_val h216_val h220_val hp11S_eq hsub_lt_5p hsub_3 hrew hm5 h0
          omega
        rcases h12 with h1 | h2
        · rw [h1] at hm5; cases hm5
        · rw [h2] at hm5; cases hm5
      have hdvd3_15 : 3 ∣ 3 ^ 15 := ⟨3 ^ 14, (@Nat.pow_succ' 3 14).symm⟩
      rw [hrhs_def, Nat.mod_mod_of_dvd A_num hdvd3_15]
      exact hA_m3
    have hspec15 := dlog2ShiftModPow3_spec_unique 15 1024 rhs15 (by decide) (by decide) hrhs_n3
    dsimp only at hspec15
    rcases hspec15 with ⟨heb_lt_raw, h0_raw, heb_per_raw, hu_raw⟩
    rcases (⟨dlog2ShiftModPow3 15 1024 rhs15, rfl⟩ :
        ∃ eb : Nat, eb = dlog2ShiftModPow3 15 1024 rhs15) with ⟨e_base, heb_def⟩
    have heb_lt : e_base < 9565938 := by
      rw [← heb_def, hp14_val] at heb_lt_raw; exact heb_lt_raw
    have heb_per : (2 ^ (e_base + (j1 + j2 + 1) * 9565938) * 1024) % 3 ^ 15 = rhs15 % 3 ^ 15 := by
      have hp := heb_per_raw (j1 + j2 + 1)
      rwa [← heb_def, hp14_val] at hp
    let t := e_base + (j1 + j2 + 1) * 9565938
    let k1 := 2 * j1
    let k2 := t - 2 * j1
    let k3 := S - t
    rcases (⟨uWinQuad M j1 j2, rfl⟩ : ∃ u0 : List Bool, u0 = uWinQuad M j1 j2) with ⟨u_q, huq_def⟩
    have hu_def : u_q = uThreeZero k1 k2 k3 := by
      rw [huq_def]; unfold uWinQuad
      dsimp only [S, A_num, sub_j1, k1, k2, k3, t] at hrhs_def heb_def ⊢
      rw [← hrhs_def, ← heb_def]
    clear heb_lt_raw h0_raw heb_per_raw hu_raw heb_def
    have h2j1_le_t : 2 * j1 ≤ t := by
      have h1 : 2 * j1 ≤ (j1 + j2 + 1) * 2 := by omega
      have h2 : (j1 + j2 + 1) * 2 ≤ (j1 + j2 + 1) * 9565938 :=
        Nat.mul_le_mul_left _ (by decide : 2 ≤ 9565938)
      exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_add_left _ e_base))
    have ht_lt_M : t < M := by
      have hj_le : (j1 + j2 + 2) * 9565938 ≤ (2 * R) * 9565938 :=
        Nat.mul_le_mul_right 9565938 (by omega)
      have h2R_eq : (2 * R) * 9565938 = R * 19131876 := by
        rw [Nat.mul_comm 2 R, Nat.mul_assoc R 2 9565938]
      rw [h2R_eq] at hj_le
      have ht_lt_step : t < (j1 + j2 + 2) * 9565938 := by
        change e_base + (j1 + j2 + 1) * 9565938 < (j1 + j2 + 2) * 9565938
        rw [show j1 + j2 + 2 = 1 + (j1 + j2 + 1) by omega, Nat.add_mul 1 (j1 + j2 + 1) 9565938, Nat.one_mul]
        exact Nat.add_lt_add_right heb_lt _
      exact Nat.lt_of_lt_of_le ht_lt_step (Nat.le_trans hj_le hM)
    have hk12 : k1 + k2 = t := by dsimp only [k1, k2]; omega
    have hk123 : k1 + k2 + k3 = S := by rw [hk12]; dsimp only [k3, S]; omega
    rcases uThreeZero_core_len_wt_carry k1 k2 k3 with ⟨hcore, hlen_tz, hwt_tz, hcar_tz⟩
    rw [← hu_def] at hcore hlen_tz hwt_tz hcar_tz
    rw [hk123] at hlen_tz hcar_tz
    rw [hk12] at hcar_tz
    have hlen_u : u_q.length = M + 17 := by rw [hlen_tz]; dsimp only [S]; omega
    have hmod15 : (2 ^ t * 1024) % 3 ^ 15 = A_num % 3 ^ 15 := by
      dsimp only [t]; rw [hrhs_def, Nat.mod_mod] at heb_per; exact heb_per
    have hPt_le_PM : 2 ^ t ≤ 2 ^ M := pow2_mono_nat (Nat.le_of_lt ht_lt_M)
    have hB_lt_A : 2 ^ t * 1024 < A_num := by
      dsimp only [A_num, sub_j1]
      rw [hp11S_eq]
      have hm1 : 2 ^ t * 1024 ≤ 1024 * 2 ^ M := by
        rw [Nat.mul_comm (2 ^ t) 1024]; exact Nat.mul_le_mul_left 1024 hPt_le_PM
      have hm2 : 349686 < 6000 * 2 ^ M :=
        Nat.lt_of_lt_of_le (by decide : 349686 < 6000 * 64) (Nat.mul_le_mul_left 6000 hPM_ge64)
      have hm3 : 1536 * 2 ^ (2 * j1) ≤ 1536 * 2 ^ M := Nat.mul_le_mul_left 1536 hP2j1_le_PM
      have hsum_le : (1024 + 6000 + 1536) * 2 ^ M ≤ 5 * (65536 * 2 ^ M) := by
        rw [← Nat.mul_assoc 5 65536]
        exact Nat.mul_le_mul_right (2 ^ M) (by decide : 1024 + 6000 + 1536 ≤ 5 * 65536)
      have hlt_all : 2 ^ t * 1024 + (349686 + 1536 * 2 ^ (2 * j1)) < 5 * (65536 * 2 ^ M) := by
        have hadd := Nat.add_lt_add_of_le_of_lt hm1 (Nat.add_lt_add_of_lt_of_le hm2 hm3)
        simp only [Nat.add_mul, Nat.add_assoc] at hsum_le
        exact Nat.lt_of_lt_of_le hadd hsum_le
      exact Nat.lt_sub_of_add_lt hlt_all
    have hdiff_mod15 : (A_num - 2 ^ t * 1024) % 3 ^ 15 = 0 := by
      rcases (⟨3 ^ 15, rfl⟩ : ∃ P15 : Nat, P15 = 3 ^ 15) with ⟨P15, hP15⟩
      rw [← hP15] at hmod15 ⊢
      have hdmA := (Nat.div_add_mod A_num P15).symm
      have hdmB := (Nat.div_add_mod (2 ^ t * 1024) P15).symm
      rw [hmod15] at hdmB
      have hsub_eq : A_num - 2 ^ t * 1024 =
          P15 * (A_num / P15 - (2 ^ t * 1024) / P15) := by
        rw [Nat.mul_sub_left_distrib]
        generalize P15 * (A_num / P15) = QA,
          P15 * ((2 ^ t * 1024) / P15) = QB,
          A_num % P15 = rem, A_num = AN, 2 ^ t * 1024 = BN at hdmA hdmB hB_lt_A ⊢
        omega
      rw [hsub_eq, Nat.mul_mod_right]
    rcases Nat.dvd_of_mod_eq_zero hdiff_mod15 with ⟨m, hm_eq⟩
    have hkey_eq : 2 ^ (u_q.length + 3) =
        3 ^ 12 * (81 * m + 1) + affineCarry u_q := by
      have hp_lhs : 2 ^ (u_q.length + 3) = 16 * 2 ^ (11 + S) := by
        rw [hlen_tz, show 12 + S + 3 = 4 + (11 + S) by omega, Nat.pow_add 2 4 (11 + S)]
      have hA_rec : A_num = 3 ^ 15 * m + 2 ^ t * 1024 := by
        rw [← hm_eq, Nat.sub_add_cancel (Nat.le_of_lt hB_lt_A)]
      have h3A_lhs : 3 * A_num + (1049058 + 4608 * 2 ^ k1) = 15 * 2 ^ (11 + S) := by
        dsimp only [A_num, sub_j1, k1]
        rw [Nat.mul_sub_left_distrib]
        have h3_sub : 3 * (349686 + 1536 * 2 ^ (2 * j1)) = 1049058 + 4608 * 2 ^ (2 * j1) := by
          rw [Nat.mul_add, ← Nat.mul_assoc]
        have h3_5 : 3 * (5 * 2 ^ (11 + S)) = 15 * 2 ^ (11 + S) := by rw [← Nat.mul_assoc]
        rw [h3_sub, h3_5]
        have hgt3 : 1049058 + 4608 * 2 ^ (2 * j1) ≤ 15 * 2 ^ (11 + S) := by
          rw [← h3_sub, ← h3_5]
          exact Nat.mul_le_mul_left 3 (Nat.le_of_lt hsub_lt_5p)
        exact Nat.sub_add_cancel hgt3
      have h3_pow15 : 3 * (3 ^ 15 * m) = 3 ^ 12 * (81 * m) := by
        have hp16 : 3 * 3 ^ 15 = 3 ^ 12 * 81 := by decide
        rw [← Nat.mul_assoc 3 (3 ^ 15) m, hp16, Nat.mul_assoc]
      have h3_1024 : 3 * (2 ^ t * 1024) = 3072 * 2 ^ t := by
        rw [Nat.mul_comm (2 ^ t) 1024, ← Nat.mul_assoc]
      have h3A_rhs : 3 * A_num = 3 ^ 12 * (81 * m) + 3072 * 2 ^ t := by
        rw [hA_rec, Nat.mul_add, h3_pow15, h3_1024]
      have h1049_sp : (1049058 : Nat) = 3 ^ 12 + 517617 := by decide
      rw [hp_lhs, hcar_tz]
      calc
        16 * 2 ^ (11 + S)
            = 15 * 2 ^ (11 + S) + 2 ^ (11 + S) := by
                rw [show (16 : Nat) = 15 + 1 from rfl, Nat.add_mul, Nat.one_mul]
        _ = (3 * A_num + (1049058 + 4608 * 2 ^ k1)) + 2 ^ (11 + S) := by rw [← h3A_lhs]
        _ = (3 ^ 12 * (81 * m) + 3072 * 2 ^ t) + ((3 ^ 12 + 517617) + 4608 * 2 ^ k1) + 2 ^ (11 + S) := by
              rw [h3A_rhs, h1049_sp]
        _ = 3 ^ 12 * (81 * m + 1) + (517617 + 4608 * 2 ^ k1 + 3072 * 2 ^ t + 2 ^ (11 + S)) := by
              rw [Nat.mul_add (3 ^ 12) (81 * m) 1, Nat.mul_one]
              ac_rfl
    have hsh3 : canonicalSuffixShift u_q 1 = 3 := by
      rcases canonicalSuffixShift_spec_unique u_q 1
        (by rw [hwt_tz]; decide) (by decide) with ⟨_, _, huniq⟩
      symm
      apply huniq 3
      · rw [hwt_tz]; decide
      · rw [Nat.mul_one, hwt_tz, hkey_eq, Nat.add_comm]
        exact Nat.add_mul_mod_self_left _ _ _
    have hfh : IsFirstHitOnePair u_q 0 :=
      (first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.2 u_q hcore).mpr (by rw [hsh3]; decide)
    rcases (⟨exactBackwardQuotient 1 u_q 0, rfl⟩ :
        ∃ y0 : Nat, y0 = exactBackwardQuotient 1 u_q 0) with ⟨y, hy_def⟩
    have hy_81m1 : y = 81 * m + 1 := by
      rcases one_generator_pos_odd_and_reaches_one u_q 0 hcore with ⟨_, _, heq_bw, _⟩
      have hbw_steps : backwardOneTotalSteps u_q 0 = u_q.length + 3 := by
        unfold backwardOneTotalSteps; rw [hsh3]; omega
      rw [hbw_steps, hwt_tz, ← hy_def] at heq_bw
      have hcomb : 3 ^ 12 * y = 3 ^ 12 * (81 * m + 1) :=
        Nat.add_right_cancel (heq_bw.symm.trans hkey_eq)
      exact Nat.eq_of_mul_eq_mul_left (pow3_pos_nat 12) hcomb
    have hy_m81 : y % 81 = 1 := by rw [hy_81m1]; omega
    have hy_m512 : y % 512 = 511 := by
      let fb_mid := List.replicate k1 false ++ [true] ++ List.replicate k2 false ++ [true] ++ List.replicate k3 false
      have hp9_511 : parityOfIter 9 511 = List.replicate 9 true := by decide
      have hu_split : u_q = parityOfIter 9 511 ++ fb_mid ++ [true] := by
        rw [hp9_511, hu_def]
        dsimp only [uThreeZero, fb_mid]
        simp only [List.append_assoc]
      have hm := (surviving_mod512_nine_prefix_auto_weight_and_characterization.1 511
        (by decide) (by decide)).2.2.2 fb_mid 0 |>.2.2.1
      rwa [← hu_split, ← hy_def] at hm
    rcases isSurvivingMod373248_of_511_and_1_w14 y hy_m512 hy_m81 with ⟨hb_surv, hcls_surv⟩
    have hy_win : 2 ^ M ≤ y ∧ y < 2 ^ (M + 1) := by
      have hlhs_20 : 2 ^ (u_q.length + 3) = 1048576 * 2 ^ M := by
        rw [hlen_u, show M + 17 + 3 = 20 + M by omega, Nat.pow_add 2 20 M, h220_val]
      have heq_y : 531441 * y + (517617 + 4608 * 2 ^ k1 + 3072 * 2 ^ t + 65536 * 2 ^ M) =
          1048576 * 2 ^ M := by
        have hk2 := hkey_eq.symm
        rwa [← hy_81m1, hlhs_20, h312_val, hcar_tz, hp11S_eq] at hk2
      have hPM_pos : 0 < 2 ^ M := pow2_pos_nat M
      refine ⟨?_, ?_⟩
      · by_cases hge : 2 ^ M ≤ y
        · exact hge
        · exfalso
          have hy_le : y ≤ 2 ^ M := Nat.le_of_lt (Nat.lt_of_not_le hge)
          have t1 : 531441 * y ≤ 531441 * 2 ^ M := Nat.mul_le_mul_left 531441 hy_le
          have t2 : 517617 ≤ 8100 * 2 ^ M :=
            Nat.le_trans (by decide : 517617 ≤ 8100 * 64) (Nat.mul_le_mul_left 8100 hPM_ge64)
          have t3 : 4608 * 2 ^ k1 ≤ 4608 * 2 ^ M := Nat.mul_le_mul_left 4608 hP2j1_le_PM
          have t4 : 3072 * 2 ^ t ≤ 3072 * 2 ^ M := Nat.mul_le_mul_left 3072 hPt_le_PM
          have tsum : 1048576 * 2 ^ M ≤ 612757 * 2 ^ M := by
            calc
              1048576 * 2 ^ M
                  = 531441 * y + (517617 + 4608 * 2 ^ k1 + 3072 * 2 ^ t + 65536 * 2 ^ M) := heq_y.symm
              _ ≤ 531441 * 2 ^ M + (8100 * 2 ^ M + 4608 * 2 ^ M + 3072 * 2 ^ M + 65536 * 2 ^ M) :=
                    Nat.add_le_add t1 (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add t2 t3) t4) (Nat.le_refl _))
              _ = (531441 + 8100 + 4608 + 3072 + 65536) * 2 ^ M := by
                    simp only [Nat.add_mul, Nat.add_assoc]
              _ = 612757 * 2 ^ M := by
                    rw [show (531441 : Nat) + 8100 + 4608 + 3072 + 65536 = 612757 by decide]
          have hbad : 1048576 ≤ 612757 := Nat.le_of_mul_le_mul_right tsum hPM_pos
          exact absurd hbad (by decide)
      · rw [Nat.pow_succ, Nat.mul_comm (2 ^ M) 2]
        by_cases hlt : y < 2 * 2 ^ M
        · exact hlt
        · exfalso
          have hy_ge : 2 * 2 ^ M ≤ y := Nat.le_of_not_lt hlt
          have t1 : 1062882 * 2 ^ M ≤ 531441 * y := by
            have hmul : 531441 * (2 * 2 ^ M) ≤ 531441 * y := Nat.mul_le_mul_left 531441 hy_ge
            have h106 : (1062882 : Nat) = 531441 * 2 := by decide
            rwa [← Nat.mul_assoc, ← h106] at hmul
          have t2 : 531441 * y ≤ 1048576 * 2 ^ M := by
            rw [← heq_y]; exact Nat.le_add_right _ _
          have hbad : 1062882 ≤ 1048576 :=
            Nat.le_of_mul_le_mul_right (Nat.le_trans t1 t2) hPM_pos
          exact absurd hbad (by decide)
    have hy_mem_win : ∀ L_max : Nat, L_max ≥ M + 17 ->
        y ∈ dyadicWindowSurvivingQ0Leaves L_max M := by
      intro L_max hL_ge
      have hy_mem_fh : y ∈ firstHitSurvivingQ0LeavesUpToLen L_max :=
        (multiscale_first_hit_surviving_q0_leaves_nodup L_max).2.2 y |>.mpr
          ⟨u_q, hfh, by omega, hb_surv, hy_def.symm⟩
      unfold dyadicWindowSurvivingQ0Leaves
      exact List.mem_filter.mpr ⟨hy_mem_fh, decide_eq_true hy_win⟩
    subst huq_def
    rw [← hy_def]
    exact ⟨hfh, hlen_u, hwt_tz, hsh3, hy_m512, hy_m81,
           hb_surv, hcls_surv, hy_win.1, hy_win.2, hy_mem_win⟩
  have hinj_ij : ∀ j1 j2 j1' j2' : Nat, j1 < R -> j2 < R -> j1' < R -> j2' < R ->
      exactBackwardQuotient 1 (uWinQuad M j1 j2) 0 =
        exactBackwardQuotient 1 (uWinQuad M j1' j2') 0 ->
      j1 = j1' ∧ j2 = j2' := by
    intro j1 j2 j1' j2' hj1 hj2 hj1' hj2' hy_eq
    have hfh1 := (hper_ij j1 j2 hj1 hj2).1
    have hfh2 := (hper_ij j1' j2' hj1' hj2').1
    have hu_eq : uWinQuad M j1 j2 = uWinQuad M j1' j2' :=
      (first_hit_one_pair_sound_and_injective _ _ 0 0 hfh1 hfh2).2.2.2 hy_eq |>.1
    unfold uWinQuad at hu_eq
    dsimp only at hu_eq
    rcases uThreeZero_inj_k1_k2 _ _ _ _ _ _ hu_eq with ⟨hk1_eq, hk2_eq⟩
    have hj1_eq : j1 = j1' := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hk1_eq
    subst hj1_eq
    rcases (⟨dlog2ShiftModPow3 15 1024 ((5 * 2 ^ (11 + (M + 5)) - (349686 + 1536 * 2 ^ (2 * j1))) % 3 ^ 15), rfl⟩ :
        ∃ eb0 : Nat, eb0 = dlog2ShiftModPow3 15 1024 ((5 * 2 ^ (11 + (M + 5)) - (349686 + 1536 * 2 ^ (2 * j1))) % 3 ^ 15)) with
      ⟨eb, heb_tmp⟩
    rw [← heb_tmp] at hk2_eq
    clear heb_tmp hu_eq hfh1 hfh2 hy_eq hk1_eq
    have hle1 : 2 * j1 ≤ eb + (j1 + j2 + 1) * 9565938 :=
      Nat.le_trans (by omega : 2 * j1 ≤ (j1 + j2 + 1) * 2)
        (Nat.le_trans (Nat.mul_le_mul_left _ (by decide : 2 ≤ 9565938)) (Nat.le_add_left _ eb))
    have hle2 : 2 * j1 ≤ eb + (j1 + j2' + 1) * 9565938 :=
      Nat.le_trans (by omega : 2 * j1 ≤ (j1 + j2' + 1) * 2)
        (Nat.le_trans (Nat.mul_le_mul_left _ (by decide : 2 ≤ 9565938)) (Nat.le_add_left _ eb))
    have hadd_eq : eb + (j1 + j2 + 1) * 9565938 = eb + (j1 + j2' + 1) * 9565938 := by
      have hsub_add :
          (eb + (j1 + j2 + 1) * 9565938 - 2 * j1) + 2 * j1 =
          (eb + (j1 + j2' + 1) * 9565938 - 2 * j1) + 2 * j1 :=
        congrArg (· + 2 * j1) hk2_eq
      rwa [Nat.sub_add_cancel hle1, Nat.sub_add_cancel hle2] at hsub_add
    have hj_sum_eq : j1 + j2 + 1 = j1 + j2' + 1 :=
      Nat.eq_of_mul_eq_mul_right (by decide : 0 < 9565938) (Nat.add_left_cancel hadd_eq)
    exact ⟨rfl, by omega⟩
  refine ⟨?_, hinj_ij, ?_⟩
  · intro j1 j2 hj1 hj2
    rcases hper_ij j1 j2 hj1 hj2 with ⟨hfh, hlen, hwt, hsh, h512, h81, _, hcls, hlo, hhi, hmem⟩
    exact ⟨hfh, hlen, hwt, hsh, h512, h81, hcls, hlo, hhi, hmem (M + 17) (Nat.le_refl _), hmem⟩
  · rcases descIdxListW14_spec (R * R) with ⟨hd_len, hd_nd, hd_lt⟩
    have hdiv_lt : ∀ idx : Nat, idx < R * R -> idx / R < R ∧ idx % R < R := by
      intro idx hidx
      have hmod : idx % R < R := Nat.mod_lt idx (by omega)
      have hdiv : idx / R < R := by
        by_cases hlt : idx / R < R
        · exact hlt
        · exfalso
          have hge : R ≤ idx / R := by omega
          have hm := Nat.mul_le_mul_left R hge
          have hdm := (Nat.div_add_mod idx R).symm
          omega
      exact ⟨hdiv, hmod⟩
    have hquad_half : R * (R + 1) / 2 ≤ R * R := by
      have h2 : R * (R + 1) ≤ (R * R) * 2 := by
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_two]
        exact Nat.add_le_add_left (Nat.le_mul_of_pos_left R (by omega)) (R * R)
      exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm 2 (R * R)]; exact h2)
    rcases (⟨fun idx : Nat => exactBackwardQuotient 1 (uWinQuad M (idx / R) (idx % R)) 0, rfl⟩ :
        ∃ fn : Nat -> Nat, fn = fun idx => exactBackwardQuotient 1 (uWinQuad M (idx / R) (idx % R)) 0) with
      ⟨fnLeaf, hfn_def⟩
    have hfn_inj : ∀ a b : Nat, a < R * R -> b < R * R -> fnLeaf a = fnLeaf b -> a = b := by
      intro a b ha_lt hb_lt heq
      rw [hfn_def] at heq
      rcases hdiv_lt a ha_lt with ⟨ha_q, ha_r⟩
      rcases hdiv_lt b hb_lt with ⟨hb_q, hb_r⟩
      rcases hinj_ij (a / R) (a % R) (b / R) (b % R) ha_q ha_r hb_q hb_r heq with ⟨hq_eq, hr_eq⟩
      clear heq hfn_def
      have hdma := (Nat.div_add_mod a R).symm
      have hdmb := (Nat.div_add_mod b R).symm
      rw [hq_eq, hr_eq] at hdma
      omega
    have hfn_mem : ∀ (L_max idx : Nat), L_max ≥ M + 17 -> idx < R * R ->
        fnLeaf idx ∈ dyadicWindowSurvivingQ0Leaves L_max M := by
      intro L_max idx hL_ge hidx
      rw [hfn_def]
      rcases hdiv_lt idx hidx with ⟨hq_lt, hr_lt⟩
      exact (hper_ij (idx / R) (idx % R) hq_lt hr_lt).2.2.2.2.2.2.2.2.2.2 L_max hL_ge
    clear hfn_def
    let leavesRR := (descIdxListW14 (R * R)).map fnLeaf
    have hnd_RR : NoDupNat leavesRR :=
      noDupNat_map_inj_on_w14 fnLeaf (descIdxListW14 (R * R)) hd_nd
        (fun a ha b hb heq => hfn_inj a b (hd_lt a ha) (hd_lt b hb) heq)
    have hlen_RR : leavesRR.length = R * R := by dsimp only [leavesRR]; rw [List.length_map, hd_len]
    have hall_L : ∀ L_max : Nat, L_max ≥ M + 17 ->
        (dyadicWindowSurvivingQ0Leaves L_max M).length ≥ R * R ∧
        (dyadicWindowSurvivingQ0Leaves L_max M).length ≥ R * (R + 1) / 2 := by
      intro L_max hL_ge
      have hsub_RR : ∀ y ∈ leavesRR, y ∈ dyadicWindowSurvivingQ0Leaves L_max M := by
        intro y hy
        rcases List.mem_map.mp hy with ⟨idx, hidx, rfl⟩
        exact hfn_mem L_max idx hL_ge (hd_lt idx hidx)
      have hle := noDupNat_length_le_of_subset_w14
        (dyadicWindowSurvivingQ0Leaves L_max M) leavesRR hnd_RR hsub_RR
      exact ⟨by omega, by omega⟩
    exact ⟨(hall_L (M + 17) (Nat.le_refl _)).1, hall_L⟩

end CollatzFormal
