/-
  CollatzFormal/Wave17WholeSpace.lean
  Wave 17 Whole-Space Mathematical & CS Proof Loop (Synthesis — Fronts C & D):
  1. Front C (Branches P1.2 & P5.16):
     - Six Exact Algebraic Binary Run & Complete `2`-Gram Syzygies (`∀ n ≥ 1`:
       `2 * binaryOneRuns n = binaryAltTransitions n + 1 + n % 2`,
       `c_00 + c_01 + c_10 + c_11 + 1 = binBitLength n`,
       `2 * c_10 = binaryAltTransitions n + (1 - n % 2)`,
       `2 * c_01 + (1 - n % 2) = binaryAltTransitions n`,
       `2 * c_11 + binaryAltTransitions n + 1 + n % 2 = 2 * binaryPopcount n`, &
       `2 * c_00 + 2 * binaryPopcount n + binaryAltTransitions n + (1 - n % 2) = 2 * binBitLength n`),
       Universal Choice-Free Squared-Weight Superharmonicity Preservation
       (`IsEventualPositiveRationalPreimageWeight M_0 (wNum^2) (wDen^2) (pTheta^2) (qTheta^2)`), &
       Complete 100% `(0, ∞)^4` All-Bases Two-Sided Impossibility for BOTH 4-Variable
       `(binBitLength, binaryPopcount, binaryAltTransitions, binaryOneRuns)` AND Complete `2`-Gram
       `(binaryTwoGram00, binaryTwoGram01, binaryTwoGram10, binaryTwoGram11)` Preimage Weights Across
       `∀ M_0 ≥ 3`,
     - End-to-End Global Convergence (`k ≤ (x + 1)^3 + (x + 1)^5`), Genuine 12-Tier `ω^12` Syracuse
       Cascade (`Cone 15 -> Cone 14 -> ... -> Cone 5 -> Φ_diamond2`, `6755390946565685 -> 633317901240533`
       in `28` steps to `1`, `+16.22x` `Φ_2` jump), `mod 2^51` Newton–Hensel Odd-Inverse &
       `Nat`/`Int`/`Q_(6)^+` Agreement + Choice-Free Non-Integer Rational Cone-15 Avoidance, `mod 117`
       Post-Climb Non-Reentry, & `[]`-Axiom `M1/M2/M3` Counter-Model Separation for the 14th Solvable
       `(3x + 1)`-Cousin `T_diamond14`.
  2. Front D (Branches P2.2 & P5.3):
     - Complete Mod-`118098` (`2 * 3^10`, `39366/118098` Surviving Classes on `w ≥ 11`) Markov Shift
       Bijection, Universal `11`-Ones `59049 mod 118098` & `[true, false] ++ 10`-Ones `98415 mod 118098`
       Locks, Exhaustive Proof that ZERO Length-`9` `Mod 512` Prefixes Force `w(u) ≥ 11` (`u_esc10`
       escapes at `w = 10` on All-Ones `511`), Exact Length-`10` `Mod 1024` `1 + 8 + 21 + 19 + 5 = 54`
       Surviving Prefix Lift (`1023` Forces `w(u) ≥ 11`), & `3^(w - 11)` (`j = 10`) Multi-Step Fiber
       Equidistribution,
     - Choice-Free 3-Adic Carry-Deficit Invariance (`w_0 + 1 + d_top ≥ 9 -> 3^9 = 19683`) & Intermediate
       `Mod 9` Stall Barrier, Plus Constructive `243x`-Compressed (`6377332 -> 26265`) Steeper-Slope
       (`c = 6 <= 6`, Beating `c = 8` via 2-Step `Mod 27` Ternary-Carry Macro-Selector
       `chooseTwoStepTernaryCarry27` + Minimum-Weight `w_0 = 6` `Mod 512` Prefix `507` + Full-Fiber
       `y % 9 = 7` `Mod 729` Lift) Exponential Surviving-Leaf Dyadic-Window Occupancy `≥ 2 ^ B`
       (`≥ 2 ^ ((M - 26265) / 6)`) at Linear Horizon `L_max ≥ M` Across `∀ B ≥ 1, ∀ M ≥ 26265 + 6 * B`.

  Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

import CollatzFormal.Wave17WholeSpaceCore

namespace CollatzFormal

-- ============================================================================
-- SECTION 1: Front C Part 1 (Branch P1.2) — Six Exact Binary Run & Complete
--            `2`-Gram Syzygies, Universal Squared-Weight Superharmonicity, &
--            Complete 100% `(0, ∞)^4` 4-Variable `(L, P, T, R_1)` + Complete
--            `2`-Gram `(c_00, c_01, c_10, c_11)` Preimage Impossibility (`W17_H3`)
-- ============================================================================

/-- Canonical binary `1`-run count (`R_1(n) = binOneRuns n`). -/
def binaryOneRuns (n : Nat) : Nat :=
  binOneRuns n

/-- Fuel-bounded MSB-to-LSB adjacent binary `2`-gram `(b1, b2)` counter (`0` for `n < 2`). -/
def binaryTwoGramAux (b1 b2 : Nat) : Nat -> Nat -> Nat
  | 0, _ => 0
  | _ + 1, 0 => 0
  | _ + 1, 1 => 0
  | fuel + 1, n =>
    (if ((n / 2) % 2 == b1) && (n % 2 == b2) then 1 else 0) +
      binaryTwoGramAux b1 b2 fuel (n / 2)

/-- Number of adjacent `(0, 0)` bit pairs in the standard MSB-to-LSB binary expansion of `n`. -/
def binaryTwoGram00 (n : Nat) : Nat := binaryTwoGramAux 0 0 n n

/-- Number of adjacent `(0, 1)` bit pairs in the standard MSB-to-LSB binary expansion of `n`. -/
def binaryTwoGram01 (n : Nat) : Nat := binaryTwoGramAux 0 1 n n

/-- Number of adjacent `(1, 0)` bit pairs in the standard MSB-to-LSB binary expansion of `n`. -/
def binaryTwoGram10 (n : Nat) : Nat := binaryTwoGramAux 1 0 n n

/-- Number of adjacent `(1, 1)` bit pairs in the standard MSB-to-LSB binary expansion of `n`. -/
def binaryTwoGram11 (n : Nat) : Nat := binaryTwoGramAux 1 1 n n

private theorem mul_pow_w17s (a b : Nat) : ∀ n : Nat, (a * b) ^ n = a ^ n * b ^ n
  | 0 => rfl
  | n + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, mul_pow_w17s a b n]
    ac_rfl

private theorem pow_mono_exp_ge1_w17s (a : Nat) (ha : a ≥ 1) :
    ∀ e1 e2 : Nat, e1 ≤ e2 -> a ^ e1 ≤ a ^ e2
  | 0, e2, _ => nat_pow_pos_of_pos a ha e2
  | e1 + 1, 0, hle => by omega
  | e1 + 1, e2 + 1, hle =>
    Nat.mul_le_mul_right a (pow_mono_exp_ge1_w17s a ha e1 e2 (by omega))

private theorem ite_false_dec_w17s {p : Prop} [inst : Decidable p] {α : Type} {a b : α} (hnp : ¬ p) :
    (if p then a else b) = b := by
  cases inst with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

private theorem binaryTwoGramAux_eq_of_le_w17 (b1 b2 : Nat) :
    ∀ (f1 f2 n : Nat), n ≤ f1 -> n ≤ f2 ->
      binaryTwoGramAux b1 b2 f1 n = binaryTwoGramAux b1 b2 f2 n
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, n, h1, _ => by rw [show n = 0 by omega]; rfl
  | _ + 1, 0, n, _, h2 => by rw [show n = 0 by omega]; rfl
  | _ + 1, _ + 1, 0, _, _ => rfl
  | _ + 1, _ + 1, 1, _, _ => rfl
  | f1 + 1, f2 + 1, n + 2, h1, h2 => by
    simp only [binaryTwoGramAux]
    rw [binaryTwoGramAux_eq_of_le_w17 b1 b2 f1 f2 ((n + 2) / 2) (by omega) (by omega)]

private theorem binaryTwoGram_step_ge2_w17 (b1 b2 m : Nat) (hm : m ≥ 2) :
    binaryTwoGramAux b1 b2 m m =
      (if ((m / 2) % 2 == b1) && (m % 2 == b2) then 1 else 0) +
        binaryTwoGramAux b1 b2 (m / 2) (m / 2) := by
  rcases (⟨m - 2, by omega⟩ : ∃ k : Nat, m = k + 2) with ⟨k, rfl⟩
  simp only [binaryTwoGramAux]
  rw [binaryTwoGramAux_eq_of_le_w17 b1 b2 (k + 1) ((k + 2) / 2) ((k + 2) / 2) (by omega) (Nat.le_refl _)]

private theorem binOneRunsAux_eq_of_le_w17 :
    ∀ (f1 f2 prev n : Nat), n ≤ f1 -> n ≤ f2 ->
      binOneRunsAux f1 prev n = binOneRunsAux f2 prev n
  | 0, 0, _, _, _, _ => rfl
  | 0, _ + 1, _, n, h1, _ => by rw [show n = 0 by omega]; simp [binOneRunsAux]
  | _ + 1, 0, _, n, _, h2 => by rw [show n = 0 by omega]; simp [binOneRunsAux]
  | f1 + 1, f2 + 1, prev, 0, _, _ => rfl
  | f1 + 1, f2 + 1, prev, n' + 1, h1, h2 => by
    simp only [binOneRunsAux, Nat.succ_ne_zero, ite_false]
    rw [binOneRunsAux_eq_of_le_w17 f1 f2 ((n' + 1) % 2) ((n' + 1) / 2) (by omega) (by omega)]

private theorem binOneRunsAux_prev0_eq_prev1_w17 (f n : Nat) (hf : f ≥ 1) (hn : n ≥ 1) :
    binOneRunsAux f 0 n = n % 2 + binOneRunsAux f 1 n := by
  rcases (⟨f - 1, by omega⟩ : ∃ f' : Nat, f = f' + 1) with ⟨f', rfl⟩
  have hne0 : n ≠ 0 := by omega
  simp only [binOneRunsAux, hne0, ite_false]
  rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with hm0 | hm1
  · simp [hm0]
  · simp [hm1]

private theorem binaryOneRuns_steps_w17 (m : Nat) (hm : m ≥ 1) :
    binaryOneRuns (2 * m) = binaryOneRuns m ∧
    binaryOneRuns (2 * m + 1) + m % 2 = binaryOneRuns m + 1 := by
  unfold binaryOneRuns binOneRuns
  refine ⟨?_, ?_⟩
  · rcases (⟨2 * m - 1, by omega⟩ : ∃ f : Nat, 2 * m = f + 1) with ⟨f, hf⟩
    conv => lhs; rw [hf]
    change (if f + 1 = 0 then 0
        else (if (f + 1) % 2 = 1 ∧ 0 = 0 then 1 else 0) +
          binOneRunsAux f ((f + 1) % 2) ((f + 1) / 2)) = binOneRunsAux m 0 m
    rw [ite_false_dec_w17s (by omega : f + 1 ≠ 0),
        show (f + 1) % 2 = 0 by omega, show (f + 1) / 2 = m by omega,
        ite_false_dec_w17s (by decide : ¬ (0 = 1 ∧ 0 = 0)), Nat.zero_add]
    exact binOneRunsAux_eq_of_le_w17 f m 0 m (by omega) (Nat.le_refl _)
  · simp only [binOneRunsAux, show 2 * m + 1 ≠ 0 by omega, ite_false,
               show (2 * m + 1) % 2 = 1 by omega, show (2 * m + 1) / 2 = m by omega,
               and_self, ite_true]
    rw [binOneRunsAux_eq_of_le_w17 (2 * m) m 1 m (by omega) (Nat.le_refl _)]
    have hp := binOneRunsAux_prev0_eq_prev1_w17 m m hm hm
    omega

private theorem binaryAltTransitionsAux_eq_of_le_w17 :
    ∀ (f1 f2 n : Nat), n ≤ f1 -> n ≤ f2 ->
      binaryAltTransitionsAux f1 n = binaryAltTransitionsAux f2 n
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, n, h1, _ => by rw [show n = 0 by omega]; rfl
  | _ + 1, 0, n, _, h2 => by rw [show n = 0 by omega]; rfl
  | _ + 1, _ + 1, 0, _, _ => rfl
  | _ + 1, _ + 1, 1, _, _ => rfl
  | f1 + 1, f2 + 1, n + 2, h1, h2 => by
    simp only [binaryAltTransitionsAux]
    rw [binaryAltTransitionsAux_eq_of_le_w17 f1 f2 ((n + 2) / 2) (by omega) (by omega)]

private theorem binaryAltTransitions_step_ge2_w17 (n : Nat) (hn : n ≥ 2) :
    binaryAltTransitions n =
      (if n % 2 != (n / 2) % 2 then 1 else 0) + binaryAltTransitions (n / 2) := by
  rcases (⟨n - 2, by omega⟩ : ∃ k : Nat, n = k + 2) with ⟨k, rfl⟩
  unfold binaryAltTransitions
  simp only [binaryAltTransitionsAux]
  rw [binaryAltTransitionsAux_eq_of_le_w17 (k + 1) ((k + 2) / 2) ((k + 2) / 2) (by omega) (Nat.le_refl _)]

private theorem binBitLengthAux_eq_cf_w17 :
    ∀ (f1 f2 n : Nat), n ≤ f1 -> n ≤ f2 -> binBitLengthAux f1 n = binBitLengthAux f2 n
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, n, h1, _ => by rw [show n = 0 by omega]; simp [binBitLengthAux]
  | _ + 1, 0, n, _, h2 => by rw [show n = 0 by omega]; simp [binBitLengthAux]
  | _ + 1, _ + 1, 0, _, _ => rfl
  | f1 + 1, f2 + 1, n' + 1, h1, h2 => by
    simp only [binBitLengthAux, Nat.succ_ne_zero, ite_false]
    rw [binBitLengthAux_eq_cf_w17 f1 f2 ((n' + 1) / 2) (by omega) (by omega)]

private theorem binBitLength_step_cf_w17 (n : Nat) (hn : n ≥ 1) :
    binBitLength n = 1 + binBitLength (n / 2) := by
  unfold binBitLength
  cases n with
  | zero => omega
  | succ m =>
    simp only [binBitLengthAux, Nat.succ_ne_zero, ite_false]
    rw [binBitLengthAux_eq_cf_w17 m ((m + 1) / 2) ((m + 1) / 2) (by omega) (Nat.le_refl _)]

private theorem binPopcountAux_eq_cf_w17 :
    ∀ (f1 f2 n : Nat), n ≤ f1 -> n ≤ f2 -> binPopcountAux f1 n = binPopcountAux f2 n
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, n, h1, _ => by rw [show n = 0 by omega]; simp [binPopcountAux]
  | _ + 1, 0, n, _, h2 => by rw [show n = 0 by omega]; simp [binPopcountAux]
  | _ + 1, _ + 1, 0, _, _ => rfl
  | f1 + 1, f2 + 1, n' + 1, h1, h2 => by
    simp only [binPopcountAux, Nat.succ_ne_zero, ite_false]
    rw [binPopcountAux_eq_cf_w17 f1 f2 ((n' + 1) / 2) (by omega) (by omega)]

private theorem binPopcount_step_cf_w17 (n : Nat) (hn : n ≥ 1) :
    binPopcount n = (n % 2) + binPopcount (n / 2) := by
  unfold binPopcount
  cases n with
  | zero => omega
  | succ m =>
    simp only [binPopcountAux, Nat.succ_ne_zero, ite_false]
    rw [binPopcountAux_eq_cf_w17 m ((m + 1) / 2) ((m + 1) / 2) (by omega) (Nat.le_refl _)]

private theorem binaryPopcount_steps_w17 (m : Nat) (hm : m ≥ 1) :
    binaryPopcount (2 * m) = binaryPopcount m ∧
    binaryPopcount (2 * m + 1) = 1 + binaryPopcount m := by
  change binPopcount (2 * m) = binPopcount m ∧ binPopcount (2 * m + 1) = 1 + binPopcount m
  refine ⟨?_, ?_⟩
  · rw [binPopcount_step_cf_w17 (2 * m) (by omega), Nat.mul_mod_right, Nat.zero_add,
        show (2 * m) / 2 = m by omega]
  · rw [binPopcount_step_cf_w17 (2 * m + 1) (by omega),
        show (2 * m + 1) % 2 = 1 by omega, show (2 * m + 1) / 2 = m by omega]

/--
  Theorem W17.3a (`binary_runs_and_2gram_syzygies`, `zero custom axioms`):
  Six Exact Algebraic Binary Run & Complete `2`-Gram Syzygies Across ALL Positive Integers `n ≥ 1`
  (`Branch P1.2`, witness `ZPOS_PREIMAGE_4VAR_RUNS_AND_2GRAM_341_TO_227`, `W17_H3`):
  1. `2 * binaryOneRuns n = binaryAltTransitions n + 1 + n % 2`
  2. `binaryTwoGram00 n + binaryTwoGram01 n + binaryTwoGram10 n + binaryTwoGram11 n + 1 = binBitLength n`
  3. `2 * binaryTwoGram10 n = binaryAltTransitions n + (1 - n % 2)`
  4. `2 * binaryTwoGram01 n + (1 - n % 2) = binaryAltTransitions n`
  5. `2 * binaryTwoGram11 n + binaryAltTransitions n + 1 + n % 2 = 2 * binaryPopcount n`
  6. `2 * binaryTwoGram00 n + 2 * binaryPopcount n + binaryAltTransitions n + (1 - n % 2) = 2 * binBitLength n`
-/
theorem binary_runs_and_2gram_syzygies (n : Nat) (hn : n ≥ 1) :
    2 * binaryOneRuns n = binaryAltTransitions n + 1 + n % 2 ∧
    binaryTwoGram00 n + binaryTwoGram01 n + binaryTwoGram10 n + binaryTwoGram11 n + 1 = binBitLength n ∧
    2 * binaryTwoGram10 n = binaryAltTransitions n + (1 - n % 2) ∧
    2 * binaryTwoGram01 n + (1 - n % 2) = binaryAltTransitions n ∧
    2 * binaryTwoGram11 n + binaryAltTransitions n + 1 + n % 2 = 2 * binaryPopcount n ∧
    2 * binaryTwoGram00 n + 2 * binaryPopcount n + binaryAltTransitions n + (1 - n % 2) = 2 * binBitLength n := by
  have hind : ∀ (fuel k : Nat), k ≥ 1 -> k ≤ fuel ->
      2 * binaryOneRuns k = binaryAltTransitions k + 1 + k % 2 ∧
      binaryTwoGram00 k + binaryTwoGram01 k + binaryTwoGram10 k + binaryTwoGram11 k + 1 = binBitLength k ∧
      2 * binaryTwoGram10 k = binaryAltTransitions k + (1 - k % 2) ∧
      2 * binaryTwoGram01 k + (1 - k % 2) = binaryAltTransitions k ∧
      2 * binaryTwoGram11 k + binaryAltTransitions k + 1 + k % 2 = 2 * binaryPopcount k ∧
      2 * binaryTwoGram00 k + 2 * binaryPopcount k + binaryAltTransitions k + (1 - k % 2) = 2 * binBitLength k := by
    intro fuel; induction fuel with
    | zero => intro _ hk hle; omega
    | succ f' ih =>
      intro k hk hle
      rcases (by clear ih; omega : k = 1 ∨ k ≥ 2) with hk1 | hk2
      · subst hk1; decide
      · let m := k / 2
        have hm1 : m ≥ 1 := by clear ih; dsimp [m]; omega
        have hm_le : m ≤ f' := by clear ih; dsimp [m]; omega
        have hk_par : (k = 2 * m ∧ k % 2 = 0) ∨ (k = 2 * m + 1 ∧ k % 2 = 1) := by
          clear ih; dsimp [m]; omega
        have hm_par : m % 2 = 0 ∨ m % 2 = 1 := by clear ih; omega
        rcases ih m hm1 hm_le with ⟨s1, s2, s3, s4, s5, s6⟩
        clear ih
        have hbl : binBitLength k = 1 + binBitLength m := binBitLength_step_cf_w17 k hk
        have htr := binaryAltTransitions_step_ge2_w17 k hk2
        have hg00 : binaryTwoGram00 k =
            (if (m % 2 == 0) && (k % 2 == 0) then 1 else 0) + binaryTwoGram00 m :=
          binaryTwoGram_step_ge2_w17 0 0 k hk2
        have hg01 : binaryTwoGram01 k =
            (if (m % 2 == 0) && (k % 2 == 1) then 1 else 0) + binaryTwoGram01 m :=
          binaryTwoGram_step_ge2_w17 0 1 k hk2
        have hg10 : binaryTwoGram10 k =
            (if (m % 2 == 1) && (k % 2 == 0) then 1 else 0) + binaryTwoGram10 m :=
          binaryTwoGram_step_ge2_w17 1 0 k hk2
        have hg11 : binaryTwoGram11 k =
            (if (m % 2 == 1) && (k % 2 == 1) then 1 else 0) + binaryTwoGram11 m :=
          binaryTwoGram_step_ge2_w17 1 1 k hk2
        change binaryAltTransitions k = (if k % 2 != m % 2 then 1 else 0) + binaryAltTransitions m at htr
        rcases binaryPopcount_steps_w17 m hm1 with ⟨hp_ev, hp_od⟩
        rcases binaryOneRuns_steps_w17 m hm1 with ⟨hr_ev, hr_od⟩
        rcases hk_par with ⟨hk_ev, hkm0⟩ | ⟨hk_od, hkm1⟩
        · have hp_k : binaryPopcount k = binaryPopcount m := by rw [hk_ev]; exact hp_ev
          have hr_k : binaryOneRuns k = binaryOneRuns m := by rw [hk_ev]; exact hr_ev
          clear hp_ev hp_od hr_ev hr_od hk_ev hk hk2 hle hm1 hm_le
          rcases hm_par with hm0 | hm1_p
          · simp only [hkm0, hm0] at htr hg00 hg01 hg10 hg11 s1 s3 s4 s5 s6 ⊢
            simp at htr hg00 hg01 hg10 hg11
            rw [hbl, hp_k, hr_k, htr, hg00, hg01, hg10, hg11]
            clear hbl hp_k hr_k htr hg00 hg01 hg10 hg11 hkm0 hm0
            generalize binaryOneRuns m = Rm, binaryAltTransitions m = Tm,
              binaryPopcount m = Pm, binBitLength m = Lm,
              binaryTwoGram00 m = G00, binaryTwoGram01 m = G01,
              binaryTwoGram10 m = G10, binaryTwoGram11 m = G11 at *
            exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
          · simp only [hkm0, hm1_p] at htr hg00 hg01 hg10 hg11 s1 s3 s4 s5 s6 ⊢
            simp at htr hg00 hg01 hg10 hg11
            rw [hbl, hp_k, hr_k, htr, hg00, hg01, hg10, hg11]
            clear hbl hp_k hr_k htr hg00 hg01 hg10 hg11 hkm0 hm1_p
            generalize binaryOneRuns m = Rm, binaryAltTransitions m = Tm,
              binaryPopcount m = Pm, binBitLength m = Lm,
              binaryTwoGram00 m = G00, binaryTwoGram01 m = G01,
              binaryTwoGram10 m = G10, binaryTwoGram11 m = G11 at *
            exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
        · have hp_k : binaryPopcount k = 1 + binaryPopcount m := by rw [hk_od]; exact hp_od
          have hr_k : binaryOneRuns k + m % 2 = binaryOneRuns m + 1 := by rw [hk_od]; exact hr_od
          clear hp_ev hp_od hr_ev hr_od hk_od hk hk2 hle hm1 hm_le
          rcases hm_par with hm0 | hm1_p
          · simp only [hkm1, hm0] at htr hg00 hg01 hg10 hg11 hr_k s1 s3 s4 s5 s6 ⊢
            simp at htr hg00 hg01 hg10 hg11
            rw [hbl, hp_k, htr, hg00, hg01, hg10, hg11]
            clear hbl hp_k htr hg00 hg01 hg10 hg11 hkm1 hm0
            generalize binaryOneRuns k = Rk, binaryOneRuns m = Rm, binaryAltTransitions m = Tm,
              binaryPopcount m = Pm, binBitLength m = Lm,
              binaryTwoGram00 m = G00, binaryTwoGram01 m = G01,
              binaryTwoGram10 m = G10, binaryTwoGram11 m = G11 at *
            exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
          · simp only [hkm1, hm1_p] at htr hg00 hg01 hg10 hg11 hr_k s1 s3 s4 s5 s6 ⊢
            simp at htr hg00 hg01 hg10 hg11
            rw [hbl, hp_k, htr, hg00, hg01, hg10, hg11]
            clear hbl hp_k htr hg00 hg01 hg10 hg11 hkm1 hm1_p
            generalize binaryOneRuns k = Rk, binaryOneRuns m = Rm, binaryAltTransitions m = Tm,
              binaryPopcount m = Pm, binBitLength m = Lm,
              binaryTwoGram00 m = G00, binaryTwoGram01 m = G01,
              binaryTwoGram10 m = G10, binaryTwoGram11 m = G11 at *
            exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  exact hind n n hn (Nat.le_refl n)

/--
  Theorem W17.3b (`preimage_weight_square_preserves_superharmonicity`,
  choice-free `zero custom axioms`):
  Universal Squared-Weight & Constant-Rescaling Superharmonicity Preservation:
  If `(wNum, wDen)` satisfies `IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta`,
  then for EVERY `K_num ≥ 1`, `wTilNum n := K_num * (wNum n * wNum n)` and
  `wTilDen n := wDen n * wDen n` satisfy
  `IsEventualPositiveRationalPreimageWeight M_0 wTilNum wTilDen (pTheta * pTheta) (qTheta * qTheta)`
  (via `(A^2 + B^2) ≤ (A + B)^2`, eliminating half-integer syzygy coefficients `1/2` globally!).
-/
theorem preimage_weight_square_preserves_superharmonicity
    (M_0 : Nat) (wNum wDen : Nat -> Nat) (pTheta qTheta K_num : Nat)
    (hK : K_num ≥ 1)
    (hw : IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta) :
    IsEventualPositiveRationalPreimageWeight M_0
      (fun n => K_num * (wNum n * wNum n))
      (fun n => wDen n * wDen n)
      (pTheta * pTheta) (qTheta * qTheta) := by
  rcases hw with ⟨hp_pos, hpq, hpos, hev_plain, hev_br⟩
  refine ⟨Nat.mul_pos hp_pos hp_pos, Nat.mul_le_mul hpq hpq, ?_, ?_, ?_⟩
  · intro n hn
    rcases hpos n hn with ⟨hn_pos, hd_pos⟩
    exact ⟨Nat.mul_pos hK (Nat.mul_pos hn_pos hn_pos), Nat.mul_pos hd_pos hd_pos⟩
  · intro m hm hm3
    have h1 := hev_plain m hm hm3
    have hsq := Nat.mul_le_mul h1 h1
    have hmulK := Nat.mul_le_mul_left K_num hsq
    calc (qTheta * qTheta) * ((K_num * (wNum (2 * m) * wNum (2 * m))) * (wDen m * wDen m))
        = K_num * ((qTheta * (wNum (2 * m) * wDen m)) * (qTheta * (wNum (2 * m) * wDen m))) := by ac_rfl
      _ ≤ K_num * ((pTheta * (wNum m * wDen (2 * m))) * (pTheta * (wNum m * wDen (2 * m)))) := hmulK
      _ = (pTheta * pTheta) * ((K_num * (wNum m * wNum m)) * (wDen (2 * m) * wDen (2 * m))) := by ac_rfl
  · intro m hm hm3; dsimp only
    let nOdd := (2 * m - 1) / 3
    have h2 := hev_br m hm hm3
    dsimp only at h2
    let A := wNum (2 * m) * wDen nOdd
    let B := wNum nOdd * wDen (2 * m)
    have hab_sq : A * A + B * B ≤ (A + B) * (A + B) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
      omega
    have hsq := Nat.mul_le_mul h2 h2
    have hmulK := Nat.mul_le_mul_left K_num hsq
    have hlhs_le :
        (qTheta * qTheta) *
          (((K_num * (wNum (2 * m) * wNum (2 * m))) * (wDen nOdd * wDen nOdd) +
            (K_num * (wNum nOdd * wNum nOdd)) * (wDen (2 * m) * wDen (2 * m))) *
            (wDen m * wDen m)) ≤
        K_num * ((qTheta * ((A + B) * wDen m)) * (qTheta * ((A + B) * wDen m))) := by
      have hl_eq :
          (qTheta * qTheta) *
            (((K_num * (wNum (2 * m) * wNum (2 * m))) * (wDen nOdd * wDen nOdd) +
              (K_num * (wNum nOdd * wNum nOdd)) * (wDen (2 * m) * wDen (2 * m))) *
              (wDen m * wDen m)) =
          (K_num * (qTheta * qTheta) * (wDen m * wDen m)) * (A * A + B * B) := by
        dsimp [A, B]
        simp only [Nat.add_mul, Nat.mul_add]
        ac_rfl
      have hr_eq :
          K_num * ((qTheta * ((A + B) * wDen m)) * (qTheta * ((A + B) * wDen m))) =
          (K_num * (qTheta * qTheta) * (wDen m * wDen m)) * ((A + B) * (A + B)) := by ac_rfl
      rw [hl_eq, hr_eq]
      exact Nat.mul_le_mul_left _ hab_sq
    have hrhs_eq :
        K_num * ((pTheta * (wNum m * (wDen (2 * m) * wDen nOdd))) *
          (pTheta * (wNum m * (wDen (2 * m) * wDen nOdd)))) =
        (pTheta * pTheta) *
          ((K_num * (wNum m * wNum m)) *
            ((wDen (2 * m) * wDen (2 * m)) * (wDen nOdd * wDen nOdd))) := by ac_rfl
    exact Nat.le_trans hlhs_le (hrhs_eq ▸ hmulK)

/--
  Theorem W17.3c (`eventual_four_var_runs_and_complete_2gram_exp_impossibility`,
  `zero custom axioms`):
  Complete 100% `(0, ∞)^4` All-Bases Two-Sided Exponential Preimage Impossibility for BOTH:
  1. **4-Variable `(binBitLength, binaryPopcount, binaryAltTransitions, binaryOneRuns)`** Across
     `∀ M_0 ≥ 3, ∀ p_L, q_L, p_P, q_P, p_T, q_T, p_R, q_R ≥ 1`, AND
  2. **Complete `2`-Gram `(binaryTwoGram00, binaryTwoGram01, binaryTwoGram10, binaryTwoGram11)`**
     Across `∀ M_0 ≥ 3, ∀ p_00, q_00, p_01, q_01, p_10, q_10, p_11, q_11 ≥ 1`
  (`Branch P1.2`, witness `ZPOS_PREIMAGE_4VAR_RUNS_AND_2GRAM_341_TO_227`, `W17_H3`).
-/
theorem eventual_four_var_runs_and_complete_2gram_exp_impossibility :
    (∀ (M_0 : Nat), M_0 ≥ 3 ->
      ∀ (wNum wDen : Nat -> Nat)
        (c_0 C_hi p_L q_L p_P q_P p_T q_T p_R q_R pTheta qTheta : Nat),
        c_0 ≥ 1 -> p_L ≥ 1 -> q_L ≥ 1 -> p_P ≥ 1 -> q_P ≥ 1 ->
        p_T ≥ 1 -> q_T ≥ 1 -> p_R ≥ 1 -> q_R ≥ 1 ->
        (∀ n : Nat, n ≥ M_0 ->
          c_0 * (q_L ^ binBitLength n * p_P ^ binaryPopcount n *
              p_T ^ binaryAltTransitions n * p_R ^ binaryOneRuns n) * wDen n ≤
            (p_L ^ binBitLength n * q_P ^ binaryPopcount n *
              q_T ^ binaryAltTransitions n * q_R ^ binaryOneRuns n) * wNum n ∧
          (p_L ^ binBitLength n * q_P ^ binaryPopcount n *
              q_T ^ binaryAltTransitions n * q_R ^ binaryOneRuns n) * wNum n ≤
            C_hi * (q_L ^ binBitLength n * p_P ^ binaryPopcount n *
              p_T ^ binaryAltTransitions n * p_R ^ binaryOneRuns n) * wDen n) ->
        ¬ IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta) ∧
    (∀ (M_0 : Nat), M_0 ≥ 3 ->
      ∀ (wNum wDen : Nat -> Nat)
        (c_0 C_hi p_00 q_00 p_01 q_01 p_10 q_10 p_11 q_11 pTheta qTheta : Nat),
        c_0 ≥ 1 -> p_00 ≥ 1 -> q_00 ≥ 1 -> p_01 ≥ 1 -> q_01 ≥ 1 ->
        p_10 ≥ 1 -> q_10 ≥ 1 -> p_11 ≥ 1 -> q_11 ≥ 1 ->
        (∀ n : Nat, n ≥ M_0 ->
          c_0 * (q_00 ^ binaryTwoGram00 n * q_01 ^ binaryTwoGram01 n *
              q_10 ^ binaryTwoGram10 n * q_11 ^ binaryTwoGram11 n) * wDen n ≤
            (p_00 ^ binaryTwoGram00 n * p_01 ^ binaryTwoGram01 n *
              p_10 ^ binaryTwoGram10 n * p_11 ^ binaryTwoGram11 n) * wNum n ∧
          (p_00 ^ binaryTwoGram00 n * p_01 ^ binaryTwoGram01 n *
              p_10 ^ binaryTwoGram10 n * p_11 ^ binaryTwoGram11 n) * wNum n ≤
            C_hi * (q_00 ^ binaryTwoGram00 n * q_01 ^ binaryTwoGram01 n *
              q_10 ^ binaryTwoGram10 n * q_11 ^ binaryTwoGram11 n) * wDen n) ->
        ¬ IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta) := by
  refine ⟨?_, ?_⟩
  · -- Part 1: 4-Variable `(binBitLength, binaryPopcount, binaryAltTransitions, binaryOneRuns)` -> 3-Variable `(L, P, T)`
    intro M_0 hM0 wNum wDen c_0 C_hi p_L q_L p_P q_P p_T q_T p_R q_R pTheta qTheta
      hc0 hpL hqL hpP hqP hpT hqT hpR hqR hsand hw
    let K_num := q_R * q_R
    have hK_pos : K_num ≥ 1 := Nat.mul_le_mul hqR hqR
    have hw_sq := preimage_weight_square_preserves_superharmonicity M_0 wNum wDen pTheta qTheta K_num hK_pos hw
    let P_L := p_L * p_L
    let Q_L := q_L * q_L
    let P_P := p_P * p_P
    let Q_P := q_P * q_P
    let P_T := p_T * p_T * p_R
    let Q_T := q_T * q_T * q_R
    let C_top := (C_hi * C_hi + 1) * K_num * (p_R * p_R)
    apply eventual_three_var_bitlength_popcount_alt_exp_impossibility.2 M_0 hM0
      (fun n => K_num * (wNum n * wNum n)) (fun n => wDen n * wDen n)
      1 C_top P_L Q_L P_P Q_P P_T Q_T (pTheta * pTheta) (qTheta * qTheta)
      (by decide) (Nat.mul_le_mul hpL hpL) (Nat.mul_le_mul hqL hqL)
      (Nat.mul_le_mul hpP hpP) (Nat.mul_le_mul hqP hqP)
      (Nat.mul_le_mul (Nat.mul_le_mul hpT hpT) hpR)
      (Nat.mul_le_mul (Nat.mul_le_mul hqT hqT) hqR)
      ?hsand3 hw_sq
    intro n hn
    rcases hsand n hn with ⟨hlo, hhi⟩
    have hsyz1 := (binary_runs_and_2gram_syzygies n (by omega)).1
    let L := binBitLength n
    let P := binaryPopcount n
    let T := binaryAltTransitions n
    let R := binaryOneRuns n
    let e_par := 1 + n % 2
    have he_le2 : e_par ≤ 2 := by dsimp [e_par]; omega
    have h2R_eq : 2 * R = T + e_par := by dsimp [R, T, e_par]; omega
    have hlo_sq := Nat.mul_le_mul hlo hlo
    have hhi_sq := Nat.mul_le_mul hhi hhi
    -- Rewrite squared monomials into `Base3 * x_R ^ (2 * R) = Base3_T * x_R ^ e_par`:
    have hl_mon :
        (q_L ^ L * p_P ^ P * p_T ^ T * p_R ^ R) * (q_L ^ L * p_P ^ P * p_T ^ T * p_R ^ R) =
          (Q_L ^ L * P_P ^ P * P_T ^ T) * p_R ^ e_par := by
      have hp2 : ∀ (x e : Nat), x ^ e * x ^ e = (x * x) ^ e := fun x e => (mul_pow_w17s x x e).symm
      have hr2 : p_R ^ R * p_R ^ R = p_R ^ T * p_R ^ e_par := by
        rw [← Nat.pow_add, ← Nat.two_mul, h2R_eq, Nat.pow_add]
      have ht_merge : (p_T * p_T) ^ T * p_R ^ T = P_T ^ T := (mul_pow_w17s (p_T * p_T) p_R T).symm
      calc (q_L ^ L * p_P ^ P * p_T ^ T * p_R ^ R) * (q_L ^ L * p_P ^ P * p_T ^ T * p_R ^ R)
          = (q_L ^ L * q_L ^ L) * (p_P ^ P * p_P ^ P) * (p_T ^ T * p_T ^ T) * (p_R ^ R * p_R ^ R) := by ac_rfl
        _ = Q_L ^ L * P_P ^ P * ((p_T * p_T) ^ T * p_R ^ T) * p_R ^ e_par := by
              rw [hp2 q_L L, hp2 p_P P, hp2 p_T T, hr2]; dsimp [Q_L, P_P]; ac_rfl
        _ = (Q_L ^ L * P_P ^ P * P_T ^ T) * p_R ^ e_par := by rw [ht_merge]
    have hr_mon :
        (p_L ^ L * q_P ^ P * q_T ^ T * q_R ^ R) * (p_L ^ L * q_P ^ P * q_T ^ T * q_R ^ R) =
          (P_L ^ L * Q_P ^ P * Q_T ^ T) * q_R ^ e_par := by
      have hp2 : ∀ (x e : Nat), x ^ e * x ^ e = (x * x) ^ e := fun x e => (mul_pow_w17s x x e).symm
      have hr2 : q_R ^ R * q_R ^ R = q_R ^ T * q_R ^ e_par := by
        rw [← Nat.pow_add, ← Nat.two_mul, h2R_eq, Nat.pow_add]
      have ht_merge : (q_T * q_T) ^ T * q_R ^ T = Q_T ^ T := (mul_pow_w17s (q_T * q_T) q_R T).symm
      calc (p_L ^ L * q_P ^ P * q_T ^ T * q_R ^ R) * (p_L ^ L * q_P ^ P * q_T ^ T * q_R ^ R)
          = (p_L ^ L * p_L ^ L) * (q_P ^ P * q_P ^ P) * (q_T ^ T * q_T ^ T) * (q_R ^ R * q_R ^ R) := by ac_rfl
        _ = P_L ^ L * Q_P ^ P * ((q_T * q_T) ^ T * q_R ^ T) * q_R ^ e_par := by
              rw [hp2 p_L L, hp2 q_P P, hp2 q_T T, hr2]; dsimp [P_L, Q_P]; ac_rfl
        _ = (P_L ^ L * Q_P ^ P * Q_T ^ T) * q_R ^ e_par := by rw [ht_merge]
    have hpR_ge1 : p_R ^ e_par ≥ 1 := nat_pow_pos_of_pos p_R hpR e_par
    have hpR_le2 : p_R ^ e_par ≤ p_R * p_R := by
      simpa [Nat.pow_succ, Nat.pow_one] using pow_mono_exp_ge1_w17s p_R hpR e_par 2 he_le2
    have hqR_ge1 : q_R ^ e_par ≥ 1 := nat_pow_pos_of_pos q_R hqR e_par
    have hqR_leK : q_R ^ e_par ≤ K_num := by
      dsimp [K_num]; simpa [Nat.pow_succ, Nat.pow_one] using pow_mono_exp_ge1_w17s q_R hqR e_par 2 he_le2
    refine ⟨?_, ?_⟩
    · -- Lower bound: `1 * Base3_lo * wDen^2 ≤ Base3_hi * (K_num * wNum^2)`
      have h1 : 1 * (Q_L ^ L * P_P ^ P * P_T ^ T) * (wDen n * wDen n) ≤
          (c_0 * c_0 * p_R ^ e_par) * ((Q_L ^ L * P_P ^ P * P_T ^ T) * (wDen n * wDen n)) := by
        rw [Nat.one_mul]
        simpa using Nat.mul_le_mul_right ((Q_L ^ L * P_P ^ P * P_T ^ T) * (wDen n * wDen n))
          (Nat.mul_le_mul (Nat.mul_le_mul hc0 hc0) hpR_ge1)
      have h2 : (c_0 * c_0 * p_R ^ e_par) * ((Q_L ^ L * P_P ^ P * P_T ^ T) * (wDen n * wDen n)) =
          (c_0 * (q_L ^ L * p_P ^ P * p_T ^ T * p_R ^ R) * wDen n) *
            (c_0 * (q_L ^ L * p_P ^ P * p_T ^ T * p_R ^ R) * wDen n) := by
        calc (c_0 * c_0 * p_R ^ e_par) * ((Q_L ^ L * P_P ^ P * P_T ^ T) * (wDen n * wDen n))
            = (c_0 * c_0) * (((Q_L ^ L * P_P ^ P * P_T ^ T) * p_R ^ e_par) * (wDen n * wDen n)) := by ac_rfl
          _ = (c_0 * c_0) * (((q_L ^ L * p_P ^ P * p_T ^ T * p_R ^ R) *
                (q_L ^ L * p_P ^ P * p_T ^ T * p_R ^ R)) * (wDen n * wDen n)) := by rw [hl_mon]
          _ = _ := by ac_rfl
      have h3 : ((p_L ^ L * q_P ^ P * q_T ^ T * q_R ^ R) * wNum n) *
            ((p_L ^ L * q_P ^ P * q_T ^ T * q_R ^ R) * wNum n) =
          (P_L ^ L * Q_P ^ P * Q_T ^ T) * (q_R ^ e_par * (wNum n * wNum n)) := by
        calc ((p_L ^ L * q_P ^ P * q_T ^ T * q_R ^ R) * wNum n) *
              ((p_L ^ L * q_P ^ P * q_T ^ T * q_R ^ R) * wNum n)
            = ((p_L ^ L * q_P ^ P * q_T ^ T * q_R ^ R) *
                (p_L ^ L * q_P ^ P * q_T ^ T * q_R ^ R)) * (wNum n * wNum n) := by ac_rfl
          _ = ((P_L ^ L * Q_P ^ P * Q_T ^ T) * q_R ^ e_par) * (wNum n * wNum n) := by rw [hr_mon]
          _ = _ := by ac_rfl
      exact Nat.le_trans h1 (Nat.le_trans (h3 ▸ h2.symm ▸ hlo_sq)
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hqR_leK)))
    · -- Upper bound: `Base3_hi * (K_num * wNum^2) ≤ C_top * Base3_lo * wDen^2`
      have h1 : (P_L ^ L * Q_P ^ P * Q_T ^ T) * (K_num * (wNum n * wNum n)) ≤
          K_num * (((P_L ^ L * Q_P ^ P * Q_T ^ T) * q_R ^ e_par) * (wNum n * wNum n)) := by
        have heq : K_num * (((P_L ^ L * Q_P ^ P * Q_T ^ T) * q_R ^ e_par) * (wNum n * wNum n)) =
            q_R ^ e_par * ((P_L ^ L * Q_P ^ P * Q_T ^ T) * (K_num * (wNum n * wNum n))) := by ac_rfl
        rw [heq]
        simpa using Nat.mul_le_mul_right _ hqR_ge1
      have h2 : ((P_L ^ L * Q_P ^ P * Q_T ^ T) * q_R ^ e_par) * (wNum n * wNum n) ≤
          (C_hi * C_hi) * (((Q_L ^ L * P_P ^ P * P_T ^ T) * p_R ^ e_par) * (wDen n * wDen n)) := by
        calc ((P_L ^ L * Q_P ^ P * Q_T ^ T) * q_R ^ e_par) * (wNum n * wNum n)
            = ((p_L ^ L * q_P ^ P * q_T ^ T * q_R ^ R) * wNum n) *
                ((p_L ^ L * q_P ^ P * q_T ^ T * q_R ^ R) * wNum n) := by rw [← hr_mon]; ac_rfl
          _ ≤ (C_hi * (q_L ^ L * p_P ^ P * p_T ^ T * p_R ^ R) * wDen n) *
                (C_hi * (q_L ^ L * p_P ^ P * p_T ^ T * p_R ^ R) * wDen n) := hhi_sq
          _ = (C_hi * C_hi) * (((q_L ^ L * p_P ^ P * p_T ^ T * p_R ^ R) *
                (q_L ^ L * p_P ^ P * p_T ^ T * p_R ^ R)) * (wDen n * wDen n)) := by ac_rfl
          _ = _ := by rw [hl_mon]
      have h3 : K_num * ((C_hi * C_hi) * (((Q_L ^ L * P_P ^ P * P_T ^ T) * p_R ^ e_par) * (wDen n * wDen n))) ≤
          C_top * (Q_L ^ L * P_P ^ P * P_T ^ T) * (wDen n * wDen n) := by
        have hl : K_num * ((C_hi * C_hi) * (((Q_L ^ L * P_P ^ P * P_T ^ T) * p_R ^ e_par) * (wDen n * wDen n))) =
            ((C_hi * C_hi) * K_num * p_R ^ e_par) * ((Q_L ^ L * P_P ^ P * P_T ^ T) * (wDen n * wDen n)) := by ac_rfl
        rw [hl, Nat.mul_assoc C_top]
        exact Nat.mul_le_mul_right _
          (Nat.mul_le_mul (Nat.mul_le_mul_right K_num (Nat.le_succ _)) hpR_le2)
      exact Nat.le_trans h1 (Nat.le_trans (Nat.mul_le_mul_left K_num h2) h3)
  · -- Part 2: Complete `2`-Gram `(c_00, c_01, c_10, c_11)` -> 3-Variable `(L, P, T)`
    intro M_0 hM0 wNum wDen c_0 C_hi p_00 q_00 p_01 q_01 p_10 q_10 p_11 q_11 pTheta qTheta
      hc0 hp00 hq00 hp01 hq01 hp10 hq10 hp11 hq11 hsand hw
    let K_num := (q_00 * q_01 * (q_11 * q_11)) * (p_00 * p_01 * p_10 * p_11)
    have hK_pos : K_num ≥ 1 := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.mul_le_mul hq00 hq01) (Nat.mul_le_mul hq11 hq11))
      (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hp00 hp01) hp10) hp11)
    have hw_sq := preimage_weight_square_preserves_superharmonicity M_0 wNum wDen pTheta qTheta K_num hK_pos hw
    let P_L := p_00 * p_00
    let Q_L := q_00 * q_00
    let P_P := q_11 * q_11 * (p_00 * p_00)
    let Q_P := p_11 * p_11 * (q_00 * q_00)
    let P_T := q_01 * q_10 * p_00 * p_11
    let Q_T := p_01 * p_10 * q_00 * q_11
    let E_lo_max := (p_00 * p_01 * (p_11 * p_11)) * (q_00 * q_01 * q_10 * q_11)
    let C_top := (C_hi * C_hi + 1) * K_num * E_lo_max
    apply eventual_three_var_bitlength_popcount_alt_exp_impossibility.2 M_0 hM0
      (fun n => K_num * (wNum n * wNum n)) (fun n => wDen n * wDen n)
      1 C_top P_L Q_L P_P Q_P P_T Q_T (pTheta * pTheta) (qTheta * qTheta)
      (by decide)
      (Nat.mul_le_mul hp00 hp00) (Nat.mul_le_mul hq00 hq00)
      (Nat.mul_le_mul (Nat.mul_le_mul hq11 hq11) (Nat.mul_le_mul hp00 hp00))
      (Nat.mul_le_mul (Nat.mul_le_mul hp11 hp11) (Nat.mul_le_mul hq00 hq00))
      (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hq01 hq10) hp00) hp11)
      (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hp01 hp10) hq00) hq11)
      ?hsand2g hw_sq
    intro n hn
    rcases hsand n hn with ⟨hlo, hhi⟩
    rcases binary_runs_and_2gram_syzygies n (by omega) with ⟨_, _, s10, s01, s11, s00⟩
    let L := binBitLength n
    let P := binaryPopcount n
    let T := binaryAltTransitions n
    let c00 := binaryTwoGram00 n
    let c01 := binaryTwoGram01 n
    let c10 := binaryTwoGram10 n
    let c11 := binaryTwoGram11 n
    let b := n % 2
    have hb_le1 : b ≤ 1 := by dsimp [b]; omega
    have h1b_le1 : 1 - b ≤ 1 := by omega
    -- Nonnegative additive 2-gram syzygies (zero subtraction of `(L, P, T)`!):
    have hA : 2 * c00 + (2 * P + T + 1) = 2 * L + b := by dsimp [c00, L, P, T, b]; omega
    have hB : 2 * c01 + 1 = T + b := by dsimp [c01, T, b]; omega
    have hC : 2 * c10 = T + (1 - b) := by dsimp [c10, T, b]; omega
    have hD : 2 * c11 + (T + 2) = 2 * P + (1 - b) := by dsimp [c11, P, T, b]; omega
    -- Common positive monomial clearing `2 * P + T + 1`, `1`, `T + 2`:
    let Common := (p_00 * q_00) ^ (2 * P + T + 1) * (p_01 * q_01) * (p_11 * q_11) ^ (T + 2)
    have hCom_pos : Common > 0 := Nat.mul_le_mul
      (Nat.mul_le_mul
        (nat_pow_pos_of_pos _ (Nat.mul_le_mul hp00 hq00) _)
        (Nat.mul_le_mul hp01 hq01))
      (nat_pow_pos_of_pos _ (Nat.mul_le_mul hp11 hq11) _)
    -- Universal 2-gram-to-3-var identity for any `(x00, x01, x10, x11)` paired with `(y00, y01, y10, y11)`:
    have h2g_id : ∀ (x00 x01 x10 x11 y00 y01 y11 : Nat),
        ((x00 ^ c00 * x01 ^ c01 * x10 ^ c10 * x11 ^ c11) *
          (x00 ^ c00 * x01 ^ c01 * x10 ^ c10 * x11 ^ c11)) *
          ((x00 * y00) ^ (2 * P + T + 1) * (x01 * y01) * (x11 * y11) ^ (T + 2)) =
        ((x00 * x00) ^ L * (x11 * x11 * (y00 * y00)) ^ P * (x01 * x10 * y00 * y11) ^ T) *
          ((y00 * y01 * (y11 * y11)) * (x00 ^ b * x01 ^ b * x10 ^ (1 - b) * x11 ^ (1 - b))) := by
      intro x00 x01 x10 x11 y00 y01 y11
      have hx00 : x00 ^ c00 * x00 ^ c00 * x00 ^ (2 * P + T + 1) = (x00 * x00) ^ L * x00 ^ b := by
        rw [← Nat.pow_add x00 c00 c00, ← Nat.two_mul, ← Nat.pow_add, hA,
            Nat.pow_add x00 (2 * L) b, ← pow_pow_eq_mul_w5 x00 2 L,
            show x00 ^ 2 = x00 * x00 by rw [Nat.pow_succ, Nat.pow_one]]
      have hx01 : x01 ^ c01 * x01 ^ c01 * x01 = x01 ^ T * x01 ^ b := by
        rw [← Nat.pow_add x01 c01 c01, ← Nat.two_mul,
            show x01 ^ (2 * c01) * x01 = x01 ^ (2 * c01 + 1) from (Nat.pow_succ x01 (2 * c01)).symm,
            hB, Nat.pow_add]
      have hx10 : x10 ^ c10 * x10 ^ c10 = x10 ^ T * x10 ^ (1 - b) := by
        rw [← Nat.pow_add x10 c10 c10, ← Nat.two_mul, hC, Nat.pow_add]
      have hx11 : x11 ^ c11 * x11 ^ c11 * x11 ^ (T + 2) = (x11 * x11) ^ P * x11 ^ (1 - b) := by
        rw [← Nat.pow_add x11 c11 c11, ← Nat.two_mul, ← Nat.pow_add, hD,
            Nat.pow_add x11 (2 * P) (1 - b), ← pow_pow_eq_mul_w5 x11 2 P,
            show x11 ^ 2 = x11 * x11 by rw [Nat.pow_succ, Nat.pow_one]]
      have hy00 : y00 ^ (2 * P + T + 1) = (y00 * y00) ^ P * y00 ^ T * y00 := by
        rw [Nat.pow_succ, Nat.pow_add y00 (2 * P) T, ← pow_pow_eq_mul_w5 y00 2 P,
            show y00 ^ 2 = y00 * y00 by rw [Nat.pow_succ, Nat.pow_one]]
      have hy11 : y11 ^ (T + 2) = y11 ^ T * (y11 * y11) := by
        rw [Nat.pow_add y11 T 2, show y11 ^ 2 = y11 * y11 by rw [Nat.pow_succ, Nat.pow_one]]
      rw [mul_pow_w17s x00 y00 (2 * P + T + 1), mul_pow_w17s x11 y11 (T + 2),
          mul_pow_w17s (x11 * x11) (y00 * y00) P,
          mul_pow_w17s (x01 * x10 * y00) y11 T, mul_pow_w17s (x01 * x10) y00 T, mul_pow_w17s x01 x10 T]
      calc ((x00 ^ c00 * x01 ^ c01 * x10 ^ c10 * x11 ^ c11) *
              (x00 ^ c00 * x01 ^ c01 * x10 ^ c10 * x11 ^ c11)) *
              ((x00 ^ (2 * P + T + 1) * y00 ^ (2 * P + T + 1)) * (x01 * y01) *
                (x11 ^ (T + 2) * y11 ^ (T + 2)))
          = (x00 ^ c00 * x00 ^ c00 * x00 ^ (2 * P + T + 1)) *
              (x01 ^ c01 * x01 ^ c01 * x01) *
              (x10 ^ c10 * x10 ^ c10) *
              (x11 ^ c11 * x11 ^ c11 * x11 ^ (T + 2)) *
              y00 ^ (2 * P + T + 1) * y01 * y11 ^ (T + 2) := by ac_rfl
        _ = ((x00 * x00) ^ L * x00 ^ b) * (x01 ^ T * x01 ^ b) * (x10 ^ T * x10 ^ (1 - b)) *
              ((x11 * x11) ^ P * x11 ^ (1 - b)) *
              ((y00 * y00) ^ P * y00 ^ T * y00) * y01 * (y11 ^ T * (y11 * y11)) := by
              rw [hx00, hx01, hx10, hx11, hy00, hy11]
        _ = _ := by ac_rfl
    have hq_id := h2g_id q_00 q_01 q_10 q_11 p_00 p_01 p_11
    have hp_id := h2g_id p_00 p_01 p_10 p_11 q_00 q_01 q_11
    rw [Nat.mul_comm q_00 p_00, Nat.mul_comm q_01 p_01, Nat.mul_comm q_11 p_11] at hq_id
    let E_lo := (p_00 * p_01 * (p_11 * p_11)) * (q_00 ^ b * q_01 ^ b * q_10 ^ (1 - b) * q_11 ^ (1 - b))
    let E_hi := (q_00 * q_01 * (q_11 * q_11)) * (p_00 ^ b * p_01 ^ b * p_10 ^ (1 - b) * p_11 ^ (1 - b))
    have hE_lo_ge1 : E_lo ≥ 1 := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.mul_le_mul hp00 hp01) (Nat.mul_le_mul hp11 hp11))
      (Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul (nat_pow_pos_of_pos _ hq00 _) (nat_pow_pos_of_pos _ hq01 _))
          (nat_pow_pos_of_pos _ hq10 _))
        (nat_pow_pos_of_pos _ hq11 _))
    have hE_hi_ge1 : E_hi ≥ 1 := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.mul_le_mul hq00 hq01) (Nat.mul_le_mul hq11 hq11))
      (Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul (nat_pow_pos_of_pos _ hp00 _) (nat_pow_pos_of_pos _ hp01 _))
          (nat_pow_pos_of_pos _ hp10 _))
        (nat_pow_pos_of_pos _ hp11 _))
    have hE_lo_le : E_lo ≤ E_lo_max := Nat.mul_le_mul_left _
      (Nat.mul_le_mul
        (Nat.mul_le_mul
          (Nat.mul_le_mul
            (by simpa using pow_mono_exp_ge1_w17s q_00 hq00 b 1 hb_le1)
            (by simpa using pow_mono_exp_ge1_w17s q_01 hq01 b 1 hb_le1))
          (by simpa using pow_mono_exp_ge1_w17s q_10 hq10 (1 - b) 1 h1b_le1))
        (by simpa using pow_mono_exp_ge1_w17s q_11 hq11 (1 - b) 1 h1b_le1))
    have hE_hi_leK : E_hi ≤ K_num := Nat.mul_le_mul_left _
      (Nat.mul_le_mul
        (Nat.mul_le_mul
          (Nat.mul_le_mul
            (by simpa using pow_mono_exp_ge1_w17s p_00 hp00 b 1 hb_le1)
            (by simpa using pow_mono_exp_ge1_w17s p_01 hp01 b 1 hb_le1))
          (by simpa using pow_mono_exp_ge1_w17s p_10 hp10 (1 - b) 1 h1b_le1))
        (by simpa using pow_mono_exp_ge1_w17s p_11 hp11 (1 - b) 1 h1b_le1))
    have hlo_c := Nat.mul_le_mul_right Common (Nat.mul_le_mul hlo hlo)
    have hhi_c := Nat.mul_le_mul_right Common (Nat.mul_le_mul hhi hhi)
    have hl_rew :
        ((c_0 * (q_00 ^ c00 * q_01 ^ c01 * q_10 ^ c10 * q_11 ^ c11) * wDen n) *
          (c_0 * (q_00 ^ c00 * q_01 ^ c01 * q_10 ^ c10 * q_11 ^ c11) * wDen n)) * Common =
        (c_0 * c_0 * E_lo) * ((Q_L ^ L * P_P ^ P * P_T ^ T) * (wDen n * wDen n)) := by
      calc ((c_0 * (q_00 ^ c00 * q_01 ^ c01 * q_10 ^ c10 * q_11 ^ c11) * wDen n) *
              (c_0 * (q_00 ^ c00 * q_01 ^ c01 * q_10 ^ c10 * q_11 ^ c11) * wDen n)) * Common
          = (c_0 * c_0) * ((((q_00 ^ c00 * q_01 ^ c01 * q_10 ^ c10 * q_11 ^ c11) *
              (q_00 ^ c00 * q_01 ^ c01 * q_10 ^ c10 * q_11 ^ c11)) * Common) * (wDen n * wDen n)) := by ac_rfl
        _ = (c_0 * c_0) * (((Q_L ^ L * P_P ^ P * P_T ^ T) * E_lo) * (wDen n * wDen n)) := by
              dsimp [Common, Q_L, P_P, P_T, E_lo] at hq_id ⊢; rw [hq_id]
        _ = _ := by ac_rfl
    have hr_rew :
        (((p_00 ^ c00 * p_01 ^ c01 * p_10 ^ c10 * p_11 ^ c11) * wNum n) *
          ((p_00 ^ c00 * p_01 ^ c01 * p_10 ^ c10 * p_11 ^ c11) * wNum n)) * Common =
        (P_L ^ L * Q_P ^ P * Q_T ^ T) * (E_hi * (wNum n * wNum n)) := by
      calc (((p_00 ^ c00 * p_01 ^ c01 * p_10 ^ c10 * p_11 ^ c11) * wNum n) *
              ((p_00 ^ c00 * p_01 ^ c01 * p_10 ^ c10 * p_11 ^ c11) * wNum n)) * Common
          = (((p_00 ^ c00 * p_01 ^ c01 * p_10 ^ c10 * p_11 ^ c11) *
              (p_00 ^ c00 * p_01 ^ c01 * p_10 ^ c10 * p_11 ^ c11)) * Common) * (wNum n * wNum n) := by ac_rfl
        _ = ((P_L ^ L * Q_P ^ P * Q_T ^ T) * E_hi) * (wNum n * wNum n) := by
              dsimp [Common, P_L, Q_P, Q_T, E_hi] at hp_id ⊢; rw [hp_id]
        _ = _ := by ac_rfl
    have hhi_rhs_rew :
        ((C_hi * (q_00 ^ c00 * q_01 ^ c01 * q_10 ^ c10 * q_11 ^ c11) * wDen n) *
          (C_hi * (q_00 ^ c00 * q_01 ^ c01 * q_10 ^ c10 * q_11 ^ c11) * wDen n)) * Common =
        (C_hi * C_hi * E_lo) * ((Q_L ^ L * P_P ^ P * P_T ^ T) * (wDen n * wDen n)) := by
      calc ((C_hi * (q_00 ^ c00 * q_01 ^ c01 * q_10 ^ c10 * q_11 ^ c11) * wDen n) *
              (C_hi * (q_00 ^ c00 * q_01 ^ c01 * q_10 ^ c10 * q_11 ^ c11) * wDen n)) * Common
          = (C_hi * C_hi) * ((((q_00 ^ c00 * q_01 ^ c01 * q_10 ^ c10 * q_11 ^ c11) *
              (q_00 ^ c00 * q_01 ^ c01 * q_10 ^ c10 * q_11 ^ c11)) * Common) * (wDen n * wDen n)) := by ac_rfl
        _ = (C_hi * C_hi) * (((Q_L ^ L * P_P ^ P * P_T ^ T) * E_lo) * (wDen n * wDen n)) := by
              dsimp [Common, Q_L, P_P, P_T, E_lo] at hq_id ⊢; rw [hq_id]
        _ = _ := by ac_rfl
    rw [hl_rew, hr_rew] at hlo_c
    rw [hr_rew, hhi_rhs_rew] at hhi_c
    refine ⟨?_, ?_⟩
    · have h1 : 1 * (Q_L ^ L * P_P ^ P * P_T ^ T) * (wDen n * wDen n) ≤
          (c_0 * c_0 * E_lo) * ((Q_L ^ L * P_P ^ P * P_T ^ T) * (wDen n * wDen n)) := by
        rw [Nat.one_mul]
        simpa using Nat.mul_le_mul_right ((Q_L ^ L * P_P ^ P * P_T ^ T) * (wDen n * wDen n))
          (Nat.mul_le_mul (Nat.mul_le_mul hc0 hc0) hE_lo_ge1)
      exact Nat.le_trans h1 (Nat.le_trans hlo_c
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hE_hi_leK)))
    · have h1 : (P_L ^ L * Q_P ^ P * Q_T ^ T) * (K_num * (wNum n * wNum n)) ≤
          K_num * ((P_L ^ L * Q_P ^ P * Q_T ^ T) * (E_hi * (wNum n * wNum n))) := by
        have heq : K_num * ((P_L ^ L * Q_P ^ P * Q_T ^ T) * (E_hi * (wNum n * wNum n))) =
            E_hi * ((P_L ^ L * Q_P ^ P * Q_T ^ T) * (K_num * (wNum n * wNum n))) := by ac_rfl
        rw [heq]; simpa using Nat.mul_le_mul_right _ hE_hi_ge1
      have h2 : K_num * ((C_hi * C_hi * E_lo) * ((Q_L ^ L * P_P ^ P * P_T ^ T) * (wDen n * wDen n))) ≤
          C_top * (Q_L ^ L * P_P ^ P * P_T ^ T) * (wDen n * wDen n) := by
        have hl : K_num * ((C_hi * C_hi * E_lo) * ((Q_L ^ L * P_P ^ P * P_T ^ T) * (wDen n * wDen n))) =
            ((C_hi * C_hi) * K_num * E_lo) * ((Q_L ^ L * P_P ^ P * P_T ^ T) * (wDen n * wDen n)) := by ac_rfl
        rw [hl, Nat.mul_assoc C_top]
        exact Nat.mul_le_mul_right _
          (Nat.mul_le_mul (Nat.mul_le_mul_right K_num (Nat.le_succ _)) hE_lo_le)
      exact Nat.le_trans h1 (Nat.le_trans (Nat.mul_le_mul_left K_num hhi_c) h2)


-- ============================================================================
-- SECTION 2: Front C Part 2 (Branch P5.16) — 14th Solvable `(3x + 1)`-Cousin
--            `T_diamond14` with Genuine 12-Tier `ω^12` Cascade
--            (`Cone 15 -> Cone 14 -> ... -> Cone 5 -> Φ_diamond2`, `W17_H3`)
-- ============================================================================

/-- Cone 15 of `T_diamond14`: `8494490059 + x = 2 ^ k * 3 ^ m` with `k ≥ 51, m ≥ 1`
    (starting at `x = 2 ^ 51 * 3 - 8494490059 = 6755390946565685`). -/
def isDiamond14Cone15 (x : Nat) : Prop :=
  x ≥ 6755390946565685 ∧ x % 2251799813685248 = 2251791319195189 ∧ x % 3 = 2 ∧
    coprime23Core (8494490059 + x) = 1

instance (x : Nat) : Decidable (isDiamond14Cone15 x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/--
  14th solvable mixed-(2, 3) Collatz cousin `T_diamond14` on `Nat`:
  Extends `T_diamond13` by adding Cone 15 (`isDiamond14Cone15 x -> (3 * x + 1) / 32`, a genuine
  `v_2(3x + 1) = 5` Syracuse jump that steps `2 ^ k * 3 ^ m - 8494490059 -> 2 ^ (k - 5) * 3 ^ (m + 1) - 796358443`
  directly into `Cone 14 -> Cone 13 -> ... -> Cone 5 -> Φ_diamond2`, e.g. `6755390946565685 -> 633317901240533`
  in `28` steps to `1`, jumping `cousinDiamond2Phi` upward `+16.22x` and defeating 11-tier `ω^11` rankings)!
-/
def cousinDiamond14Step (x : Nat) : Nat :=
  if isDiamond14Cone15 x then (3 * x + 1) / 32 else cousinDiamond13Step x

def cousinDiamond14Iter : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamond14Iter k (cousinDiamond14Step x)

private theorem cousinDiamond14Iter_add : ∀ (a b x : Nat),
    cousinDiamond14Iter (a + b) x = cousinDiamond14Iter b (cousinDiamond14Iter a x)
  | 0, _, _ => by simp [cousinDiamond14Iter]
  | a + 1, b, x => by
    rw [Nat.succ_add]
    exact cousinDiamond14Iter_add a b (cousinDiamond14Step x)

/-- Signed extension of `T_diamond14` (`q = 3`) to `Int` for `M2 = Z^-` separation. -/
def cousinDiamond14StepInt (x : Int) : Int :=
  if x ≥ 6755390946565685 ∧ x % 2251799813685248 = 2251791319195189 ∧ x % 3 = 2 ∧
      coprime23Core (8494490059 + x.toNat) = 1
  then (3 * x + 1) / 32
  else cousinDiamond13StepInt x

def cousinDiamond14IterInt : Nat -> Int -> Int
  | 0, x => x
  | k + 1, x => cousinDiamond14IterInt k (cousinDiamond14StepInt x)

/-- Hensel lift of `invMod70368744177664Odd` (`2^46`) to `mod 2251799813685248` (`2^51`, `46 * 2 = 92 ≥ 51`). -/
def invMod2251799813685248Odd (d : Nat) : Nat :=
  let i46 := invMod70368744177664Odd d
  (i46 * (4503599627370498 - ((d % 2251799813685248) * i46) % 2251799813685248)) % 2251799813685248

/-- Canonical reduced-pair extension of `T_diamond14` (`q = 3`) to positive `Q_(6)^+`. -/
def cousinDiamond14StepQ6 (p : Nat × Nat) : Nat × Nat :=
  let num := p.1
  let den := p.2
  let r51 := (num * invMod2251799813685248Odd den) % 2251799813685248
  let r3 := (num * (den % 3)) % 3
  if num ≥ 6755390946565685 * den ∧ r51 = 2251791319195189 ∧ r3 = 2 ∧
      core3 (core2 (8494490059 * den + num)) = den
  then reduceRatPair (3 * num + den) (32 * den)
  else cousinDiamond13StepQ6 p

def cousinDiamond14IterQ6 : Nat -> (Nat × Nat) -> (Nat × Nat)
  | 0, p => p
  | k + 1, p => cousinDiamond14IterQ6 k (cousinDiamond14StepQ6 p)

/-- Generalized odd-multiplier `q` step of `T_diamond14` on `Nat` for `M3` (`q = 7`) separation. -/
def cousinDiamond14StepParam (q x : Nat) : Nat :=
  if isDiamond14Cone15 x then (q * x + 1) / 32 else cousinDiamond13StepParam q x

def cousinDiamond14IterParam (q : Nat) : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamond14IterParam q k (cousinDiamond14StepParam q x)

private theorem hensel_inv_lift_w17 (M1 M2 S C d i1 : Nat)
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

private theorem core3_core2_eq_coprime23Core_w17 :
    ∀ (fuel n : Nat), n > 0 -> n ≤ fuel -> core3 (core2 n) = coprime23Core n
  | 0, _, hn, hle => by omega
  | fuel + 1, n, hn, hle => by
    by_cases hev : n % 2 = 0
    · let k := n / 2
      have hk_pos : k > 0 := by dsimp [k]; omega
      rw [show n = 2 * k by dsimp [k]; omega, core2_mul2 k hk_pos, coprime23Core_mul2 k hk_pos]
      exact core3_core2_eq_coprime23Core_w17 fuel k hk_pos (by dsimp [k]; omega)
    · have hodd : n % 2 = 1 := by omega
      rcases core3_decomp n hn with ⟨_, _, _, _, hmul⟩
      have hc3_odd : core3 n % 2 = 1 := by
        by_cases hc3_ev : core3 n % 2 = 0
        · have hm0 : (v3Pow n * core3 n) % 2 = 0 := by rw [Nat.mul_mod, hc3_ev, Nat.mul_zero]
          rw [hmul] at hm0; omega
        · omega
      unfold coprime23Core
      rw [core2_of_odd n hodd, core2_of_odd (core3 n) hc3_odd]

private theorem reduceRatPair_div_exact_w17 (a m : Nat) (hm : m > 0) (hdvd : m ∣ a) :
    reduceRatPair a m = (a / m, 1) := by
  rcases hdvd with ⟨q, rfl⟩
  unfold reduceRatPair
  have hgcd : Nat.gcd (m * q) m = m :=
    Nat.dvd_antisymm (Nat.gcd_dvd_right (m * q) m) (Nat.dvd_gcd ⟨q, rfl⟩ (Nat.dvd_refl m))
  dsimp only
  rw [hgcd, Nat.div_self hm]

private theorem dvd_three_mul_add_one_of_mod_w17 (x M D Qm Qr R Qt : Nat)
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
  Theorem W17.3d (`cousin_diamond14_q6_noninteger_avoids_cone15`,
  choice-free `zero custom axioms`):
  Universal Non-Integer Rational Exclusion from Cone 15 on `M1 = Q_(6)^+`:
  For EVERY reduced non-integer rational `(num, den)` (`Nat.gcd num den = 1` and `den > 1`),
  `core3 (core2 (8494490059 * den + num)) ≠ den`, so `cousinDiamond14StepQ6 (num, den)` NEVER enters
  Cone 15 and agrees identically with `cousinDiamond13StepQ6 (num, den)` (`Branch P5.16`, `W17_H3`).
-/
theorem cousin_diamond14_q6_noninteger_avoids_cone15 (num den : Nat)
    (hgcd : Nat.gcd num den = 1) (hden : den > 1) :
    core3 (core2 (8494490059 * den + num)) ≠ den ∧
    cousinDiamond14StepQ6 (num, den) = cousinDiamond13StepQ6 (num, den) := by
  have hne : core3 (core2 (8494490059 * den + num)) ≠ den := by
    intro heq
    have hdvd_sum : den ∣ (8494490059 * den + num) := by
      have hc_dvd : core3 (core2 (8494490059 * den + num)) ∣ (8494490059 * den + num) :=
        Nat.dvd_trans (core3Aux_dvd_w8 _ _) (core2Aux_dvd_w8 _ _)
      rwa [heq] at hc_dvd
    rcases hdvd_sum with ⟨k, hk⟩
    have hdvd_num : den ∣ num := ⟨k - 8494490059, by
      rcases Nat.lt_or_ge k 8494490059 with hlt | hge
      · exfalso
        have hm := Nat.mul_le_mul_left den (show k ≤ 8494490058 by omega)
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
  unfold cousinDiamond14StepQ6
  dsimp only
  exact ite_false_dec_w17s (fun ⟨_, _, _, hc⟩ => hne hc)

/--
  Theorem W17.3e (`cousin_diamond14_hensel_inv_and_nat_int_q6_agreement`,
  `zero custom axioms`):
  Universal Newton–Hensel `mod 2^51` (`2251799813685248`) Odd-Inverse Correctness, Exact
  `Nat`/`Int`/`Q_(6)^+` Step Agreement, & Universal Non-Integer Rational Exclusion from Cone 15
  on `M1 = Q_(6)^+` (`Branch P5.16`, `W17_H3`).
-/
theorem cousin_diamond14_hensel_inv_and_nat_int_q6_agreement :
    (∀ d : Nat, d % 2 = 1 -> (d * invMod2251799813685248Odd d) % 2251799813685248 = 1) ∧
    (∀ x : Nat, cousinDiamond14StepInt (x : Int) = (cousinDiamond14Step x : Int)) ∧
    (∀ x : Nat, cousinDiamond14StepQ6 (x, 1) = (cousinDiamond14Step x, 1)) ∧
    (∀ num den : Nat, Nat.gcd num den = 1 -> den > 1 ->
      core3 (core2 (8494490059 * den + num)) ≠ den ∧
      cousinDiamond14StepQ6 (num, den) = cousinDiamond13StepQ6 (num, den)) := by
  have hinv46 := cousin_diamond13_hensel_inv_and_nat_int_q6_agreement.1
  have hinv51 : ∀ d : Nat, d % 2 = 1 -> (d * invMod2251799813685248Odd d) % 2251799813685248 = 1 := by
    intro d hodd
    exact hensel_inv_lift_w17 70368744177664 2251799813685248 2199023255552 4503599627370498
      d (invMod70368744177664Odd d) (by decide) (by decide) (by decide) (hinv46 d hodd)
  refine ⟨hinv51, ?_, ?_, cousin_diamond14_q6_noninteger_avoids_cone15⟩
  · intro x
    have h1 : ((x : Int) ≥ 6755390946565685) ↔ (x ≥ 6755390946565685) := by omega
    have h2 : ((x : Int) % 2251799813685248 = 2251791319195189) ↔
        (x % 2251799813685248 = 2251791319195189) := ⟨Int.ofNat.inj, congrArg Int.ofNat⟩
    have h3 : ((x : Int) % 3 = 2) ↔ (x % 3 = 2) := ⟨Int.ofNat.inj, congrArg Int.ofNat⟩
    have hdiv : ((3 * (x : Int) + 1) / 32) = (((3 * x + 1) / 32 : Nat) : Int) := by omega
    have htoNat : (x : Int).toNat = x := rfl
    unfold cousinDiamond14StepInt cousinDiamond14Step isDiamond14Cone15
    rw [htoNat]; simp only [h1, h2, h3]
    by_cases hc15 : x ≥ 6755390946565685 ∧ x % 2251799813685248 = 2251791319195189 ∧ x % 3 = 2 ∧
        coprime23Core (8494490059 + x) = 1
    · simp only [hc15, and_self, ite_true, hdiv]
    · simp only [hc15, ite_false]
      exact cousin_diamond13_hensel_inv_and_nat_int_q6_agreement.2.1 x
  · have hi51 : invMod2251799813685248Odd 1 = 1 := by decide
    have hm3_1 : (1 : Nat) % 3 = 1 := by decide
    intro x
    have hcc : core3 (core2 (8494490059 + x)) = coprime23Core (8494490059 + x) :=
      core3_core2_eq_coprime23Core_w17 (8494490059 + x) (8494490059 + x) (by omega) (Nat.le_refl _)
    unfold cousinDiamond14StepQ6 cousinDiamond14Step isDiamond14Cone15
    simp only [hi51, hm3_1, Nat.mul_one, hcc]
    by_cases hc15 : x ≥ 6755390946565685 ∧ x % 2251799813685248 = 2251791319195189 ∧ x % 3 = 2 ∧
        coprime23Core (8494490059 + x) = 1
    · simp only [hc15, and_self, ite_true]
      exact reduceRatPair_div_exact_w17 (3 * x + 1) 32 (by decide)
        (dvd_three_mul_add_one_of_mod_w17 x 2251799813685248 32 70368744177664 70368478724849 21 2
          (by decide) hc15.2.1 (by decide))
    · simp only [hc15, ite_false]
      exact cousin_diamond13_hensel_inv_and_nat_int_q6_agreement.2.2.1 x

private theorem d14_eq_d13_of_not_cone15 (x : Nat) (hnc15 : ¬ isDiamond14Cone15 x) :
    cousinDiamond14Step x = cousinDiamond13Step x := by
  unfold cousinDiamond14Step; simp [hnc15]

-- Modular Cone-15 avoidance helpers (`2251791319195189 % 512 = 53, % 64 = 53, % 32 = 21, % 8 = 5`):

private theorem mod512_of_cone15 (z : Nat) (hc15 : isDiamond14Cone15 z) : z % 512 = 53 := by
  have h := congrArg (· % 512) hc15.2.1
  rw [Nat.mod_mod_of_dvd z (by decide : 512 ∣ 2251799813685248),
      show 2251791319195189 % 512 = 53 by decide] at h
  exact h

private theorem mod64_of_cone15 (z : Nat) (hc15 : isDiamond14Cone15 z) : z % 64 = 53 := by
  have h := congrArg (· % 64) (mod512_of_cone15 z hc15)
  rw [Nat.mod_mod_of_dvd z (by decide : 64 ∣ 512), show 53 % 64 = 53 by decide] at h
  exact h

private theorem mod32_of_cone15 (z : Nat) (hc15 : isDiamond14Cone15 z) : z % 32 = 21 := by
  have h := congrArg (· % 32) (mod64_of_cone15 z hc15)
  rw [Nat.mod_mod_of_dvd z (by decide : 32 ∣ 64), show 53 % 32 = 21 by decide] at h
  exact h

private theorem not_cone15_of_even (z : Nat) (hev : z % 2 = 0) : ¬ isDiamond14Cone15 z := by
  intro hc15
  have h := congrArg (· % 2) (mod32_of_cone15 z hc15)
  rw [Nat.mod_mod_of_dvd z (by decide : 2 ∣ 32), hev] at h
  cases h

private theorem not_cone15_of_mod4_eq_3 (z : Nat) (hm4 : z % 4 = 3) : ¬ isDiamond14Cone15 z := by
  intro hc15
  have h := congrArg (· % 4) (mod32_of_cone15 z hc15)
  rw [Nat.mod_mod_of_dvd z (by decide : 4 ∣ 32), hm4] at h
  cases h

private theorem not_cone15_of_mod8_ne_5 (z : Nat) (hm8 : z % 8 ≠ 5) : ¬ isDiamond14Cone15 z := by
  intro hc15
  have h := congrArg (· % 8) (mod32_of_cone15 z hc15)
  rw [Nat.mod_mod_of_dvd z (by decide : 8 ∣ 32)] at h
  exact hm8 h

private theorem not_cone15_of_mod32_ne_21 (z : Nat) (hm32 : z % 32 ≠ 21) : ¬ isDiamond14Cone15 z :=
  fun hc15 => hm32 (mod32_of_cone15 z hc15)

private theorem not_cone15_of_mod64_ne_53 (z : Nat) (hm64 : z % 64 ≠ 53) : ¬ isDiamond14Cone15 z :=
  fun hc15 => hm64 (mod64_of_cone15 z hc15)

private theorem not_cone15_of_mod512_ne_53 (z : Nat) (hm512 : z % 512 ≠ 53) : ¬ isDiamond14Cone15 z :=
  fun hc15 => hm512 (mod512_of_cone15 z hc15)

private theorem not_cone15_of_mod3_ne_2 (z : Nat) (hm3 : z % 3 ≠ 2) : ¬ isDiamond14Cone15 z :=
  fun ⟨_, _, h3, _⟩ => hm3 h3

private theorem cousinDiamond14Step_pos (x : Nat) (hx : x > 0) : cousinDiamond14Step x > 0 := by
  unfold cousinDiamond14Step
  by_cases hc15 : isDiamond14Cone15 x
  · simp only [hc15, ite_true]
    have hge : x ≥ 6755390946565685 := hc15.1
    clear hc15
    exact Nat.lt_of_lt_of_le (by decide : 0 < (3 * 6755390946565685 + 1) / 32)
      (Nat.div_le_div_right (by omega))
  · simp only [hc15, ite_false]
    unfold cousinDiamond13Step
    by_cases hc14 : isDiamond13Cone14 x
    · simp only [hc14, ite_true]
      have hge : x ≥ 211105436174549 := hc14.1
      clear hc14 hc15
      exact Nat.lt_of_lt_of_le (by decide : 0 < (3 * 211105436174549 + 1) / 128)
        (Nat.div_le_div_right (by omega))
    · simp only [hc14, ite_false]
      unfold cousinDiamond12Step
      by_cases hc13 : isDiamond12Cone13 x
      · simp only [hc13, ite_true]
        have hge : x ≥ 1649248777013 := hc13.1
        clear hc13 hc14 hc15
        exact Nat.lt_of_lt_of_le (by decide : 0 < (3 * 1649248777013 + 1) / 32)
          (Nat.div_le_div_right (by omega))
      · simp only [hc13, ite_false]; exact cousinDiamond11Step_pos x hx

private theorem not_cone15_six_mul_pow9_sub1_w17 (m : Nat) :
    ¬ isDiamond14Cone15 (6 * 9 ^ m - 1) := by
  cases m with
  | zero => rintro ⟨hge, _, _, _⟩; simp at hge
  | succ m1 =>
    cases m1 with
    | zero => rintro ⟨hge, _, _, _⟩; simp at hge
    | succ t =>
      have h9_117 : ∀ s : Nat,
          9 ^ (s + 2) % 117 = 81 ∨ 9 ^ (s + 2) % 117 = 27 ∨ 9 ^ (s + 2) % 117 = 9 := by
        intro s; induction s with
        | zero => exact Or.inl rfl
        | succ s' ih =>
          rw [Nat.pow_succ 9 (s' + 2), Nat.mul_mod]
          rcases ih with h | h | h <;> (rw [h]; decide)
      have h2_117 : ∀ s : Nat,
          2 ^ s % 117 = 1 ∨ 2 ^ s % 117 = 2 ∨ 2 ^ s % 117 = 4 ∨ 2 ^ s % 117 = 8 ∨
          2 ^ s % 117 = 16 ∨ 2 ^ s % 117 = 32 ∨ 2 ^ s % 117 = 64 ∨ 2 ^ s % 117 = 11 ∨
          2 ^ s % 117 = 22 ∨ 2 ^ s % 117 = 44 ∨ 2 ^ s % 117 = 88 ∨ 2 ^ s % 117 = 59 := by
        intro s; induction s with
        | zero => exact Or.inl rfl
        | succ s' ih =>
          rw [Nat.pow_succ 2 s', Nat.mul_mod]
          rcases ih with h | h | h | h | h | h | h | h | h | h | h | h <;> (rw [h]; decide)
      rcases (⟨9 ^ (t + 2), rfl⟩ : ∃ p9 : Nat, p9 = 9 ^ (t + 2)) with ⟨P9, hP9_def⟩
      have hp9_pos : P9 ≥ 1 := by rw [hP9_def]; exact nat_pow_pos_of_pos 9 (by decide) (t + 2)
      rcases (⟨2 * P9 + 2831496686, rfl⟩ : ∃ a0 : Nat, a0 = 2 * P9 + 2831496686) with ⟨A, hA_def⟩
      have hsum_eq : 8494490059 + (6 * 9 ^ (t + 2) - 1) = 3 * A := by
        rw [← hP9_def, hA_def]; omega
      have hN_pos : 3 * A > 0 := by rw [hA_def]; omega
      have hA_m3 : A % 3 = 2 := by
        have hp9_3 : P9 % 3 = 0 := by rw [hP9_def, Nat.pow_succ 9 (t + 1)]; omega
        rw [hA_def]; omega
      have hA_117 : A % 117 = 89 ∨ A % 117 = 98 ∨ A % 117 = 62 := by
        rw [hA_def, hP9_def]
        have hdm := (Nat.div_add_mod (9 ^ (t + 2)) 117).symm
        rcases h9_117 t with h | h | h <;> clear h9_117 h2_117 hsum_eq hN_pos hA_m3 <;> omega
      rintro ⟨hc_ge, hc_51, hc_3, hcop⟩
      clear hc_ge hc_51 hc_3
      rw [hsum_eq] at hcop
      rcases decomp_2_3_exact (3 * A) hN_pos with ⟨hd1, hd2, hd3, hd4, hd5, hmul⟩
      clear hd1 hd2 hd3 hd4 hd5
      rw [hcop, Nat.mul_one] at hmul
      rcases eq_pow2_of_v2Pow_aux (3 * A) (3 * A) hN_pos (Nat.le_refl _) with ⟨k, hk⟩
      rcases eq_pow3_of_v3Pow_aux (3 * A) (3 * A) hN_pos (Nat.le_refl _) with ⟨r, hr⟩
      rw [hk, hr] at hmul
      clear hcop hsum_eq hk hr hA_def hP9_def hp9_pos hN_pos h9_117
      have hr1 : r = 1 := by
        cases r with
        | zero =>
          rw [Nat.pow_zero, Nat.mul_one] at hmul
          exact False.elim (pow2_mod3_nonzero_w5 k (by clear h2_117 hA_117; omega))
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
      have hA_pow2 : A = 2 ^ k := by clear h2_117 hA_117 hr1; omega
      rw [hA_pow2] at hA_117
      rcases h2_117 k with h | h | h | h | h | h | h | h | h | h | h | h <;>
        clear h2_117 hmul hA_pow2 hr1 <;> omega

/--
  Theorem W17.3f (`cousin_diamond14_outside_cones4to15_descent_and_mod117_nonreentry`,
  `zero custom axioms`):
  Strict `cousinDiamond2Phi` Descent Outside Cones 4..15 & Universal `mod 117` Post-Climb
  Non-Reentry into Cone 15 (`∀ m : Nat, ¬ isDiamond14Cone15 (6 * 9 ^ m - 1)`,
  `Branch P5.16`, `W17_H3`).
-/
theorem cousin_diamond14_outside_cones4to15_descent_and_mod117_nonreentry :
    (∀ x : Nat, x > 2 ->
      ¬ isDiamond3Cone4 x -> ¬ isDiamond4Cone5 x ->
      ¬ isDiamond5Cone6 x -> ¬ isDiamond6Cone7 x ->
      ¬ isDiamond7Cone8 x -> ¬ isDiamond8Cone9 x ->
      ¬ isDiamond9Cone10 x -> ¬ isDiamond10Cone11 x ->
      ¬ isDiamond11Cone12 x -> ¬ isDiamond12Cone13 x ->
      ¬ isDiamond13Cone14 x -> ¬ isDiamond14Cone15 x ->
      cousinDiamond2Phi (cousinDiamond14Step x) < cousinDiamond2Phi x) ∧
    (∀ m : Nat, ¬ isDiamond14Cone15 (6 * 9 ^ m - 1)) := by
  refine ⟨?_, not_cone15_six_mul_pow9_sub1_w17⟩
  intro x hx hnc4 hnc5 hnc6 hnc7 hnc8 hnc9 hnc10 hnc11 hnc12 hnc13 hnc14 hnc15
  rw [d14_eq_d13_of_not_cone15 x hnc15]
  exact cousin_diamond13_outside_cones4to14_descent_and_mod33_nonreentry.1 x hx
    hnc4 hnc5 hnc6 hnc7 hnc8 hnc9 hnc10 hnc11 hnc12 hnc13 hnc14

private theorem isDiamond13Cone14_of_pow2_pow3_w17 (a b : Nat) (ha : a ≥ 46) (hb : b ≥ 1) :
    isDiamond13Cone14 (2 ^ a * 3 ^ b - 796358443) := by
  have hc : (2 : Nat) ^ 46 = 70368744177664 := by decide
  have hp2_ge : 2 ^ a ≥ 70368744177664 := by rw [← hc]; exact pow2_mono_nat ha
  have hp3_ge : 3 ^ b ≥ 3 := by simpa using nat_pow_mono_exp_pos 3 1 b (by decide) hb
  have hprod_ge : 2 ^ a * 3 ^ b ≥ 211106232532992 := by simpa using Nat.mul_le_mul hp2_ge hp3_ge
  have hp46 : 70368744177664 ∣ 2 ^ a * 3 ^ b := by
    rw [show a = 46 + (a - 46) by omega, Nat.pow_add 2 46 (a - 46), hc, Nat.mul_assoc]
    exact ⟨2 ^ (a - 46) * 3 ^ b, rfl⟩
  have hp3_div : 3 ∣ 2 ^ a * 3 ^ b := by
    rw [show b = 1 + (b - 1) by omega, Nat.pow_add 3 1 (b - 1), Nat.pow_one,
        ← Nat.mul_assoc (2 ^ a) 3, Nat.mul_comm (2 ^ a) 3, Nat.mul_assoc]
    exact ⟨2 ^ a * 3 ^ (b - 1), rfl⟩
  refine ⟨by clear hc hp2_ge hp3_ge hp46 hp3_div; generalize 2 ^ a * 3 ^ b = P at hprod_ge ⊢; omega,
          ?_, ?_, ?_⟩
  · rcases hp46 with ⟨k, hk⟩
    clear hc hp2_ge hp3_ge hp3_div
    generalize 2 ^ a * 3 ^ b = P at hprod_ge hk ⊢
    rw [hk, show k = (k - 1) + 1 by omega, Nat.mul_add 70368744177664 (k - 1) 1, Nat.mul_one]
    generalize k - 1 = k'
    rw [show 70368744177664 * k' + 70368744177664 - 796358443 = 70367947819221 + 70368744177664 * k' by omega,
        Nat.add_mul_mod_self_left]
  · rcases hp3_div with ⟨k3, hk3⟩
    clear hc hp2_ge hp3_ge hp46
    generalize 2 ^ a * 3 ^ b = P at hprod_ge hk3 ⊢; omega
  · rw [show 796358443 + (2 ^ a * 3 ^ b - 796358443) = 2 ^ a * 3 ^ b by
          clear hc hp2_ge hp3_ge hp46 hp3_div; generalize 2 ^ a * 3 ^ b = P at hprod_ge ⊢; omega]
    exact coprime23Core_pow2_pow3 a b

private theorem d14_eq_d3_of_even_w17 (z : Nat) (hev : z % 2 = 0) :
    cousinDiamond14Step z = cousinDiamond3Step z := by
  rw [d14_eq_d13_of_not_cone15 z (not_cone15_of_even z hev)]
  unfold cousinDiamond13Step
  have hnc14 : ¬ isDiamond13Cone14 z := by
    rintro ⟨_, h46, _, _⟩
    have h2 := congrArg (· % 2) h46
    rw [Nat.mod_mod_of_dvd z (by decide : 2 ∣ 70368744177664), hev] at h2
    cases h2
  rw [ite_false_dec_w17s hnc14]
  unfold cousinDiamond12Step
  have hnc13 : ¬ isDiamond12Cone13 z := by
    rintro ⟨_, h39, _, _⟩
    have h2 := congrArg (· % 2) h39
    rw [Nat.mod_mod_of_dvd z (by decide : 2 ∣ 549755813888), hev] at h2
    cases h2
  rw [ite_false_dec_w17s hnc13,
      cousinDiamond11Step_eq_d10_of_not_cone12 z (not_cone12_of_even z hev),
      cousinDiamond10Step_eq_d9_of_not_cone11 z (not_cone11_of_even z hev),
      cousinDiamond9Step_eq_d8_of_not_cone10 z (not_cone10_of_even z hev),
      cousinDiamond8Step_eq_d7_of_not_cone9 z (not_cone9_of_even z hev),
      cousinDiamond7Step_eq_d6_of_not_cone8 z (not_cone8_of_even z hev),
      cousinDiamond6Step_eq_d5_of_not_cone7 z (not_cone7_of_even z hev),
      cousinDiamond5Step_eq_d4_of_not_cone6 z (not_cone6_of_even z hev),
      cousinDiamond4Step_eq_d3_of_not_cone5 z (by rintro ⟨_, h32, _, _⟩; omega)]

private theorem not_cone14_of_mod32_ne_21_w17 (z : Nat) (hm32 : z % 32 ≠ 21) : ¬ isDiamond13Cone14 z := by
  rintro ⟨_, h46, _, _⟩
  have h := congrArg (· % 32) h46
  rw [Nat.mod_mod_of_dvd z (by decide : 32 ∣ 70368744177664),
      show 70367947819221 % 32 = 21 by decide] at h
  exact hm32 h

private theorem not_cone13_of_mod32_ne_21_w17 (z : Nat) (hm32 : z % 32 ≠ 21) : ¬ isDiamond12Cone13 z := by
  rintro ⟨_, h39, _, _⟩
  have h := congrArg (· % 32) h39
  rw [Nat.mod_mod_of_dvd z (by decide : 32 ∣ 549755813888),
      show 549737149237 % 32 = 21 by decide] at h
  exact hm32 h

private theorem d13_eq_d12_of_not_cone14_w17 (x : Nat) (hnc14 : ¬ isDiamond13Cone14 x) :
    cousinDiamond13Step x = cousinDiamond12Step x := by
  unfold cousinDiamond13Step; exact ite_false_dec_w17s hnc14

private theorem d12_eq_d11_of_not_cone13_w17 (x : Nat) (hnc13 : ¬ isDiamond12Cone13 x) :
    cousinDiamond12Step x = cousinDiamond11Step x := by
  unfold cousinDiamond12Step; exact ite_false_dec_w17s hnc13

private theorem d13_eq_d3_of_not_cones5to14_w17 (z : Nat)
    (h14 : ¬ isDiamond13Cone14 z) (h13 : ¬ isDiamond12Cone13 z) (h12 : ¬ isDiamond11Cone12 z)
    (h11 : ¬ isDiamond10Cone11 z) (h10 : ¬ isDiamond9Cone10 z) (h9 : ¬ isDiamond8Cone9 z)
    (h8 : ¬ isDiamond7Cone8 z) (h7 : ¬ isDiamond6Cone7 z) (h6 : ¬ isDiamond5Cone6 z)
    (h5 : ¬ isDiamond4Cone5 z) :
    cousinDiamond13Step z = cousinDiamond3Step z := by
  rw [d13_eq_d12_of_not_cone14_w17 z h14,
      d12_eq_d11_of_not_cone13_w17 z h13,
      cousinDiamond11Step_eq_d10_of_not_cone12 z h12,
      cousinDiamond10Step_eq_d9_of_not_cone11 z h11,
      cousinDiamond9Step_eq_d8_of_not_cone10 z h10,
      cousinDiamond8Step_eq_d7_of_not_cone9 z h9,
      cousinDiamond7Step_eq_d6_of_not_cone8 z h8,
      cousinDiamond6Step_eq_d5_of_not_cone7 z h7,
      cousinDiamond5Step_eq_d4_of_not_cone6 z h6,
      cousinDiamond4Step_eq_d3_of_not_cone5 z h5]

private theorem cousin_diamond14_mersenne_scaled :
    ∀ (k a q : Nat), k + 1 ≤ a -> q ≥ 1 ->
      cousinDiamond14Iter k (2 ^ a * q - 1) = 3 ^ k * 2 ^ (a - k) * q - 1
  | 0, _, _, _, _ => by simp [cousinDiamond14Iter]
  | k + 1, a, q, hka, hq => by
    have hp4 : 2 ^ a * q = 4 * (2 ^ (a - 2) * q) := by
      conv => lhs; rw [show a = (a - 2) + 2 by omega]
      rw [Nat.pow_add 2 (a - 2) 2, show (2 : Nat) ^ 2 = 4 from rfl,
          Nat.mul_comm (2 ^ (a - 2)) 4, Nat.mul_assoc]
    have hm_pos : 2 ^ (a - 2) * q ≥ 1 := Nat.mul_le_mul (pow2_pos_nat (a - 2)) hq
    simp only [cousinDiamond14Iter]
    rw [d14_eq_d13_of_not_cone15 _ (not_cone15_of_mod4_eq_3 _ (by omega)),
        d13_eq_d12_of_not_cone14_w17 _ (not_cone14_of_mod32_ne_21_w17 _ (by omega)),
        d12_eq_d11_of_not_cone13_w17 _ (not_cone13_of_mod32_ne_21_w17 _ (by omega))]
    have hd11 := cousin_diamond11_mersenne_scaled 1 a q (by omega) hq
    simp only [cousinDiamond11Iter, Nat.pow_one] at hd11
    rw [show cousinDiamond11Step (2 ^ a * q - 1) = 2 ^ (a - 1) * (3 * q) - 1 by
          rw [hd11]; apply congrArg (· - 1); ac_rfl,
        cousin_diamond14_mersenne_scaled k (a - 1) (3 * q) (by omega) (by omega),
        show a - 1 - k = a - (k + 1) by omega, Nat.pow_succ 3 k]
    apply congrArg (· - 1); ac_rfl

private theorem cousin_diamond14_even9_spine_drain :
    ∀ k : Nat, cousinDiamond14Iter k ((9 ^ (k + 1) - 1) / 4) = 2
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
    simp only [cousinDiamond14Iter]
    change cousinDiamond14Iter k (cousinDiamond14Step ((9 ^ (j + 1) - 1) / 4)) = 2
    rw [he_j1, d14_eq_d3_of_even_w17 _ (by omega)]
    have hd3 : cousinDiamond3Step (18 * q + 2) = (9 ^ j - 1) / 4 := by
      rw [he_j]; unfold cousinDiamond3Step
      have hq_pos : q ≥ 1 := by dsimp [q]; omega
      have hodd_f : ¬ ((18 * q + 2) % 2 = 1) := by omega
      have h18_t : 18 * q + 2 ≥ 20 ∧ (18 * q + 2) % 18 = 2 := ⟨by omega, by omega⟩
      simp only [hodd_f, h18_t, and_self, ite_true, ite_false]; omega
    rw [hd3]
    exact cousin_diamond14_even9_spine_drain k

private theorem cousin_diamond14_pow3_sub1_drain :
    ∀ k : Nat, cousinDiamond14Iter k (3 ^ (k + 1) - 1) = 2
  | 0 => rfl
  | k + 1 => by
    let j := k + 1
    have hp3_ge3 : 3 ^ j ≥ 3 := by dsimp [j]; rw [Nat.pow_succ]; have := pow3_pos_nat k; omega
    have ho_j1 := pow3_odd_nat_sec8 (j + 1)
    have hp_j1 := pow3_pos_nat (j + 1)
    simp only [cousinDiamond14Iter]
    change cousinDiamond14Iter k (cousinDiamond14Step (3 ^ (j + 1) - 1)) = 2
    rw [d14_eq_d3_of_even_w17 _ (by omega)]
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
    exact cousin_diamond14_pow3_sub1_drain k

private theorem cousin_diamond14_cone5_two_step_climb :
    ∀ (q_c a b : Nat), 3 * q_c + 2 ≤ a -> b ≥ 1 ->
      cousinDiamond14Iter (2 * q_c) (2 ^ a * 3 ^ b - 7) =
        2 ^ (a - 3 * q_c) * 3 ^ (b + 2 * q_c) - 7
  | 0, _, _, _, _ => by simp [cousinDiamond14Iter]
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
    have hs1 : cousinDiamond14Step (2 ^ a * 3 ^ b - 7) = mid := by
      rw [d14_eq_d13_of_not_cone15 _ (not_cone15_of_mod32_ne_21 _ (by have := hc5.2.1; omega)),
          d13_eq_d12_of_not_cone14_w17 _ (not_cone14_of_mod32_ne_21_w17 _ (by have := hc5.2.1; omega)),
          d12_eq_d11_of_not_cone13_w17 _ (not_cone13_of_mod32_ne_21_w17 _ (by have := hc5.2.1; omega))]
      exact hd11_s1
    have hs2 : cousinDiamond14Step mid = 2 ^ (a - 3) * 3 ^ (b + 2) - 7 := by
      rw [d14_eq_d13_of_not_cone15 _ (not_cone15_of_mod4_eq_3 _ hmid_4),
          d13_eq_d12_of_not_cone14_w17 _ (not_cone14_of_mod32_ne_21_w17 _ (by omega)),
          d12_eq_d11_of_not_cone13_w17 _ (not_cone13_of_mod32_ne_21_w17 _ (by omega))]
      exact hd11_2
    rw [Nat.mul_succ 2 q_c, Nat.add_comm (2 * q_c) 2, cousinDiamond14Iter_add 2 (2 * q_c)]
    have hi2 : cousinDiamond14Iter 2 (2 ^ a * 3 ^ b - 7) = 2 ^ (a - 3) * 3 ^ (b + 2) - 7 := by
      simp only [cousinDiamond14Iter, hs1, hs2]
    rw [hi2, cousin_diamond14_cone5_two_step_climb q_c (a - 3) (b + 2) (by omega) (by omega)]
    apply congrArg (· - 7); congr 1
    · apply congrArg (2 ^ ·); omega
    · apply congrArg (3 ^ ·); omega

private theorem not_cone14_of_mod3_ne_2_w17 (x : Nat) (h : x % 3 ≠ 2) : ¬ isDiamond13Cone14 x :=
  fun hc => h hc.2.2.1

private theorem not_cone13_of_mod3_ne_2_w17 (x : Nat) (h : x % 3 ≠ 2) : ¬ isDiamond12Cone13 x :=
  fun hc => h hc.2.2.1

private theorem not_cone5_of_mod3_ne_2_w17 (x : Nat) (h : x % 3 ≠ 2) : ¬ isDiamond4Cone5 x :=
  fun hc => h hc.2.2.1

private theorem ne8_mod9_of_mod3_eq1_w17 (x : Nat) (h : x % 3 = 1) : x % 9 ≠ 8 := by omega

private theorem cousin_diamond14_a0_3_drain (b0 : Nat) (hb0 : b0 ≥ 3) :
    cousinDiamond14Step (8 * 3 ^ b0 - 7) = 12 * 3 ^ b0 - 10 ∧
    cousinDiamond14Step (12 * 3 ^ b0 - 10) = 4 * 3 ^ b0 - 4 ∧
    cousinDiamond14Step (4 * 3 ^ b0 - 4) = 4 * 3 ^ (b0 - 1) - 2 ∧
    cousinDiamond14Iter ((b0 - 1) / 2 + 7) (8 * 3 ^ b0 - 7) = 1 := by
  rcases cousin_diamond11_a0_3_drain b0 hb0 with ⟨hd11_1, hd11_2, hd11_3, _⟩
  have hp3_ge27 : 3 ^ b0 ≥ 27 := by simpa using nat_pow_mono_exp_pos 3 3 b0 (by decide) hb0
  have hp3_b1_ge9 : 3 ^ (b0 - 1) ≥ 9 := by simpa using nat_pow_mono_exp_pos 3 2 (b0 - 1) (by decide) (by omega)
  have hs1 : cousinDiamond14Step (8 * 3 ^ b0 - 7) = 12 * 3 ^ b0 - 10 := by
    have ho := pow3_odd_nat_sec8 b0
    rw [d14_eq_d13_of_not_cone15 _ (not_cone15_of_mod8_ne_5 _ (by omega)),
        d13_eq_d12_of_not_cone14_w17 _ (not_cone14_of_mod32_ne_21_w17 _ (by omega)),
        d12_eq_d11_of_not_cone13_w17 _ (not_cone13_of_mod32_ne_21_w17 _ (by omega))]
    exact hd11_1
  have hs2 : cousinDiamond14Step (12 * 3 ^ b0 - 10) = 4 * 3 ^ b0 - 4 := by
    rw [d14_eq_d13_of_not_cone15 _ (not_cone15_of_even _ (by omega)),
        d13_eq_d12_of_not_cone14_w17 _ (not_cone14_of_mod32_ne_21_w17 _ (by omega)),
        d12_eq_d11_of_not_cone13_w17 _ (not_cone13_of_mod32_ne_21_w17 _ (by omega))]
    exact hd11_2
  have hs3 : cousinDiamond14Step (4 * 3 ^ b0 - 4) = 4 * 3 ^ (b0 - 1) - 2 := by
    rw [d14_eq_d13_of_not_cone15 _ (not_cone15_of_even _ (by omega)),
        d13_eq_d12_of_not_cone14_w17 _ (not_cone14_of_mod32_ne_21_w17 _ (by omega)),
        d12_eq_d11_of_not_cone13_w17 _ (not_cone13_of_mod32_ne_21_w17 _ (by omega))]
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
    have hs4 : cousinDiamond14Step (4 * 9 ^ m - 2) = zr := by
      rw [d14_eq_d3_of_even_w17 _ (by omega)]
      have h9m9 : 9 ^ m % 9 = 0 := by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
      rw [cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) (by omega)]
      dsimp [zr]; omega
    have hsz : cousinDiamond14Step zr = yr := by
      rw [d14_eq_d13_of_not_cone15 zr (not_cone15_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          d13_eq_d3_of_not_cones5to14_w17 zr
            (not_cone14_of_mod32_ne_21_w17 zr (by dsimp [zr]; omega))
            (not_cone13_of_mod32_ne_21_w17 zr (by dsimp [zr]; omega))
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
    have hsy : cousinDiamond14Step yr = (9 ^ (m + 1) - 1) / 4 := by
      have hyr_m3 : yr % 3 = 1 := by
        clear hd11_1 hd11_2 hd11_3 hs1 hs2 hs3 h4_eq hs4 hsz
        have hm3 : 9 ^ m % 3 = 0 := by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
        dsimp [yr]; omega
      have hyr_ne2 : yr % 3 ≠ 2 := by rw [hyr_m3]; decide
      have hyr_ne8 : yr % 9 ≠ 8 := ne8_mod9_of_mod3_eq1_w17 yr hyr_m3
      rw [d14_eq_d13_of_not_cone15 yr (not_cone15_of_mod3_ne_2 yr hyr_ne2),
          d13_eq_d3_of_not_cones5to14_w17 yr
            (not_cone14_of_mod3_ne_2_w17 yr hyr_ne2)
            (not_cone13_of_mod3_ne_2_w17 yr hyr_ne2)
            (not_cone12_of_mod3_ne_2 yr hyr_ne2)
            (not_cone11_of_mod3_ne_2 yr hyr_ne2)
            (not_cone10_of_mod3_ne_2 yr hyr_ne2)
            (not_cone9_of_mod3_ne_2 yr hyr_ne2)
            (not_cone8_of_mod3_ne_2 yr hyr_ne2)
            (not_cone7_of_mod9_ne_8 yr hyr_ne8)
            (not_cone6_of_mod9_ne_8 yr hyr_ne8)
            (not_cone5_of_mod3_ne_2_w17 yr hyr_ne2)]
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
    change cousinDiamond14Iter (m + 7) (8 * 3 ^ b0 - 7) = 1
    rw [show m + 7 = 4 + 1 + 1 + m + 1 by omega,
        cousinDiamond14Iter_add (4 + 1 + 1 + m) 1,
        cousinDiamond14Iter_add (4 + 1 + 1) m,
        cousinDiamond14Iter_add (4 + 1) 1,
        cousinDiamond14Iter_add 4 1]
    have hi4 : cousinDiamond14Iter 4 (8 * 3 ^ b0 - 7) = zr := by
      simp only [cousinDiamond14Iter, hs1, hs2, hs3, h4_eq, hs4]
    rw [hi4, show cousinDiamond14Iter 1 zr = yr from hsz,
        show cousinDiamond14Iter 1 yr = (9 ^ (m + 1) - 1) / 4 from hsy,
        cousin_diamond14_even9_spine_drain m]
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
    have hs4 : cousinDiamond14Step (12 * 9 ^ m - 2) = ur := by
      rw [d14_eq_d3_of_even_w17 _ (by omega)]
      have h9m9 : 9 ^ m % 9 = 0 := by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
      rw [cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) (by omega)]
      dsimp [ur]; omega
    have hsu : cousinDiamond14Step ur = wr := by
      rw [d14_eq_d13_of_not_cone15 ur (not_cone15_six_mul_pow9_sub1_w17 m),
          d13_eq_d3_of_not_cones5to14_w17 ur
            (cousin_diamond13_outside_cones4to14_descent_and_mod33_nonreentry.2 m)
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
    have hsw : cousinDiamond14Step wr = (9 ^ (m + 1) - 1) / 4 := by
      let q := (9 ^ m - 1) / 8
      have hq_pos : q ≥ 1 := by dsimp [q]; omega
      have hp9_eq : 9 ^ m = 8 * q + 1 := by dsimp [q]; omega
      have hwr_eq : wr = 36 * q + 4 := by dsimp [wr]; rw [Nat.pow_succ 9 m, hp9_eq]; omega
      have hnext_eq : (9 ^ (m + 1) - 1) / 4 = 18 * q + 2 := by rw [Nat.pow_succ 9 m, hp9_eq]; omega
      rw [hwr_eq, hnext_eq, d14_eq_d3_of_even_w17 _ (by omega),
          cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) (by omega)]
      omega
    change cousinDiamond14Iter (m + 7) (8 * 3 ^ b0 - 7) = 1
    rw [show m + 7 = 4 + 1 + 1 + m + 1 by omega,
        cousinDiamond14Iter_add (4 + 1 + 1 + m) 1,
        cousinDiamond14Iter_add (4 + 1 + 1) m,
        cousinDiamond14Iter_add (4 + 1) 1,
        cousinDiamond14Iter_add 4 1]
    have hi4 : cousinDiamond14Iter 4 (8 * 3 ^ b0 - 7) = ur := by
      simp only [cousinDiamond14Iter, hs1, hs2, hs3, hu_eq, hs4]
    rw [hi4, show cousinDiamond14Iter 1 ur = wr from hsu,
        show cousinDiamond14Iter 1 wr = (9 ^ (m + 1) - 1) / 4 from hsw,
        cousin_diamond14_even9_spine_drain m]
    decide

private theorem cousin_diamond14_a0_2_and_4_drain (b0 : Nat) (hb0 : b0 ≥ 3) :
    cousinDiamond14Iter (b0 + 3) (4 * 3 ^ b0 - 7) = 1 ∧
    cousinDiamond14Iter ((b0 - 1) / 2 + 8) (16 * 3 ^ b0 - 7) = 1 := by
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
  · have hs1 : cousinDiamond14Step (4 * 3 ^ b0 - 7) = 6 * 3 ^ b0 - 10 := by
      have hdm := (Nat.div_add_mod (3 ^ b0) 8).symm
      rw [d14_eq_d13_of_not_cone15 _ (not_cone15_of_mod32_ne_21 _ (by rcases h3b0_m8 with h1 | h3 <;> omega)),
          d13_eq_d12_of_not_cone14_w17 _ (not_cone14_of_mod32_ne_21_w17 _ (by rcases h3b0_m8 with h1 | h3 <;> omega)),
          d12_eq_d11_of_not_cone13_w17 _ (not_cone13_of_mod32_ne_21_w17 _ (by rcases h3b0_m8 with h1 | h3 <;> omega)),
          cousinDiamond11Step_eq_d10_of_not_cone12 _ (not_cone12_of_mod32_ne_13 _ (by rcases h3b0_m8 with h1 | h3 <;> omega)),
          cousinDiamond10Step_eq_d9_of_not_cone11 _ (not_cone11_of_mod32_ne_13 _ (by rcases h3b0_m8 with h1 | h3 <;> omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_mod32_ne_13 _ (by rcases h3b0_m8 with h1 | h3 <;> omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_mod32_ne_13 _ (by rcases h3b0_m8 with h1 | h3 <;> omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_mod32_ne_21 _ (by rcases h3b0_m8 with h1 | h3 <;> omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (hnc7_c 4 (by decide)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (hnc6_c 4 (by decide))]
      exact cousin_diamond4_exit_step_general_odd 4 b0 (Or.inl rfl) hb0
    have hs2 : cousinDiamond14Step (6 * 3 ^ b0 - 10) = 2 * 3 ^ b0 - 4 := by
      rw [d14_eq_d3_of_even_w17 _ (by omega)]
      have h18 : 6 * 3 ^ b0 = 18 * 3 ^ (b0 - 1) := by rw [h3b0_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]; omega
    have hs3 : cousinDiamond14Step (2 * 3 ^ b0 - 4) = 2 * 3 ^ (b0 - 1) - 2 := by
      rw [d14_eq_d3_of_even_w17 _ (by omega)]
      have h18 : 2 * 3 ^ b0 = 18 * 3 ^ (b0 - 2) := by rw [h3b0_sp, h3b1_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]; omega
    have hs4 : cousinDiamond14Step (2 * 3 ^ (b0 - 1) - 2) = 3 ^ (b0 - 1) - 1 := by
      rw [d14_eq_d3_of_even_w17 _ (by omega)]
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
        cousinDiamond14Iter_add (4 + (b0 - 2)) 1,
        cousinDiamond14Iter_add 4 (b0 - 2)]
    have hi4 : cousinDiamond14Iter 4 (4 * 3 ^ b0 - 7) = 3 ^ ((b0 - 2) + 1) - 1 := by
      simp only [cousinDiamond14Iter, hs1, hs2, hs3, hs4]; rw [show b0 - 1 = (b0 - 2) + 1 by omega]
    rw [hi4, cousin_diamond14_pow3_sub1_drain (b0 - 2)]; decide
  · rcases cousin_diamond14_a0_3_drain b0 hb0 with ⟨ha3_s1, ha3_s2, ha3_s3, ha3⟩
    have ho := pow3_odd_nat_sec8 b0
    have hs1 : cousinDiamond14Step (16 * 3 ^ b0 - 7) = 24 * 3 ^ b0 - 10 := by
      rw [d14_eq_d13_of_not_cone15 _ (not_cone15_of_mod8_ne_5 _ (by omega)),
          d13_eq_d12_of_not_cone14_w17 _ (not_cone14_of_mod32_ne_21_w17 _ (by omega)),
          d12_eq_d11_of_not_cone13_w17 _ (not_cone13_of_mod32_ne_21_w17 _ (by omega)),
          cousinDiamond11Step_eq_d10_of_not_cone12 _ (not_cone12_of_mod32_ne_13 _ (by omega)),
          cousinDiamond10Step_eq_d9_of_not_cone11 _ (not_cone11_of_mod32_ne_13 _ (by omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_mod32_ne_13 _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_mod32_ne_13 _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_mod32_ne_21 _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (hnc7_c 16 (by decide)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (hnc6_c 16 (by decide))]
      exact cousin_diamond4_exit_step_general_odd 16 b0 (Or.inr (Or.inr rfl)) hb0
    have hs2 : cousinDiamond14Step (24 * 3 ^ b0 - 10) = 8 * 3 ^ b0 - 4 := by
      rw [d14_eq_d3_of_even_w17 _ (by omega)]
      have h18 : 24 * 3 ^ b0 = 18 * (4 * 3 ^ (b0 - 1)) := by rw [h3b0_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]; omega
    have hs3 : cousinDiamond14Step (8 * 3 ^ b0 - 4) = 8 * 3 ^ (b0 - 1) - 2 := by
      rw [d14_eq_d3_of_even_w17 _ (by omega)]
      have h18 : 8 * 3 ^ b0 = 18 * (4 * 3 ^ (b0 - 2)) := by rw [h3b0_sp, h3b1_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]; omega
    have hs4 : cousinDiamond14Step (8 * 3 ^ (b0 - 1) - 2) = 4 * 3 ^ (b0 - 1) - 2 := by
      rw [d14_eq_d3_of_even_w17 _ (by omega)]
      have h18 : 8 * 3 ^ (b0 - 1) = 18 * (4 * 3 ^ (b0 - 3)) := by
        calc 8 * 3 ^ (b0 - 1) = 8 * 3 ^ (2 + (b0 - 3)) := by congr 2; omega
          _ = 8 * (3 ^ 2 * 3 ^ (b0 - 3)) := by rw [Nat.pow_add]
          _ = 18 * (4 * 3 ^ (b0 - 3)) := by omega
      have hp3_b3 := pow3_pos_nat (b0 - 3)
      rw [cousinDiamond3Step_even_mod8_eq6_w8 _ (by omega) (by omega) (by omega) ⟨by omega, by omega⟩]; omega
    rw [show (b0 - 1) / 2 + 7 = 3 + ((b0 - 1) / 2 + 4) by omega,
        cousinDiamond14Iter_add 3 ((b0 - 1) / 2 + 4)] at ha3
    have hi3 : cousinDiamond14Iter 3 (8 * 3 ^ b0 - 7) = 4 * 3 ^ (b0 - 1) - 2 := by
      simp only [cousinDiamond14Iter, ha3_s1, ha3_s2, ha3_s3]
    rw [hi3] at ha3
    rw [show (b0 - 1) / 2 + 8 = 4 + ((b0 - 1) / 2 + 4) by omega,
        cousinDiamond14Iter_add 4 ((b0 - 1) / 2 + 4)]
    have hi4 : cousinDiamond14Iter 4 (16 * 3 ^ b0 - 7) = 4 * 3 ^ (b0 - 1) - 2 := by
      simp only [cousinDiamond14Iter, hs1, hs2, hs3, hs4]
    rw [hi4]; exact ha3

private theorem cousin_diamond14_cone4_return_aux (x : Nat) (hc4 : isDiamond3Cone4 x) :
    ∃ k : Nat, k ≤ cousinDiamond2Phi x ∧ cousinDiamond14Iter k x = 1 := by
  rcases cousin_diamond3_cone4_reaches_one_exact x hc4 with ⟨r, hr_ge3, hE, _, hphi_ge⟩
  refine ⟨3 * r + 4, hphi_ge, ?_⟩
  have hx_odd : x % 2 = 1 := by have := hc4.2.1; omega
  have hs1 : cousinDiamond14Step x = 2 ^ (2 * r + 1) - 1 := by
    rw [d14_eq_d13_of_not_cone15 x (not_cone15_of_mod8_ne_5 x (by have := hc4.2.1; omega)),
        d13_eq_d12_of_not_cone14_w17 x (not_cone14_of_mod32_ne_21_w17 x (by have := hc4.2.1; omega)),
        d12_eq_d11_of_not_cone13_w17 x (not_cone13_of_mod32_ne_21_w17 x (by have := hc4.2.1; omega)),
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
  have hglide : cousinDiamond14Iter (2 * r) (2 ^ (2 * r + 1) - 1) = zr := by
    have hf := cousin_diamond14_mersenne_scaled (2 * r) (2 * r + 1) 1 (by omega) (by decide)
    simp only [Nat.mul_one, show 2 * r + 1 - 2 * r = 1 by omega, Nat.pow_one] at hf
    rw [hf, ← pow9_eq_pow3_double r, Nat.mul_comm]
  have hp9_ge729 : 9 ^ r ≥ 729 := by simpa using nat_pow_mono_exp_pos 9 3 r (by decide) hr_ge3
  have hp9_m8 := pow9_mod8_eq_one_w5 r
  have hsz : cousinDiamond14Step zr = yr := by
    rw [d14_eq_d13_of_not_cone15 zr (not_cone15_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
        d13_eq_d3_of_not_cones5to14_w17 zr
          (not_cone14_of_mod32_ne_21_w17 zr (by dsimp [zr]; omega))
          (not_cone13_of_mod32_ne_21_w17 zr (by dsimp [zr]; omega))
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
  have hsy : cousinDiamond14Step yr = (9 ^ (r + 1) - 1) / 4 := by
    have hyr_m3 : yr % 3 = 1 := by
      clear hs1 hglide hsz
      have hm3 : 9 ^ r % 3 = 0 := by rw [show r = (r - 1) + 1 by omega, Nat.pow_succ]; omega
      dsimp [yr]; omega
    have hyr_ne2 : yr % 3 ≠ 2 := by rw [hyr_m3]; decide
    have hyr_ne8 : yr % 9 ≠ 8 := ne8_mod9_of_mod3_eq1_w17 yr hyr_m3
    rw [d14_eq_d13_of_not_cone15 yr (not_cone15_of_mod3_ne_2 yr hyr_ne2),
        d13_eq_d3_of_not_cones5to14_w17 yr
          (not_cone14_of_mod3_ne_2_w17 yr hyr_ne2)
          (not_cone13_of_mod3_ne_2_w17 yr hyr_ne2)
          (not_cone12_of_mod3_ne_2 yr hyr_ne2)
          (not_cone11_of_mod3_ne_2 yr hyr_ne2)
          (not_cone10_of_mod3_ne_2 yr hyr_ne2)
          (not_cone9_of_mod3_ne_2 yr hyr_ne2)
          (not_cone8_of_mod3_ne_2 yr hyr_ne2)
          (not_cone7_of_mod9_ne_8 yr hyr_ne8)
          (not_cone6_of_mod9_ne_8 yr hyr_ne8)
          (not_cone5_of_mod3_ne_2_w17 yr hyr_ne2)]
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
      cousinDiamond14Iter_add (1 + 2 * r + 1 + 1 + r) 1,
      cousinDiamond14Iter_add (1 + 2 * r + 1 + 1) r,
      cousinDiamond14Iter_add (1 + 2 * r + 1) 1,
      cousinDiamond14Iter_add (1 + 2 * r) 1,
      cousinDiamond14Iter_add 1 (2 * r)]
  rw [show cousinDiamond14Iter 1 x = 2 ^ (2 * r + 1) - 1 from hs1, hglide,
      show cousinDiamond14Iter 1 zr = yr from hsz,
      show cousinDiamond14Iter 1 yr = (9 ^ (r + 1) - 1) / 4 from hsy,
      cousin_diamond14_even9_spine_drain r]
  decide

private theorem cousin_diamond14_cone5_return_aux (x : Nat) (hc5 : isDiamond4Cone5 x) :
    ∃ (a b k : Nat),
      a ≥ 5 ∧ b ≥ 1 ∧ x + 7 = 2 ^ a * 3 ^ b ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond14Iter k x = 1 := by
  rcases cousin_diamond13_cones4to14_exact_return.2.1 x hc5 with ⟨a, b, _, ha5, hb1, hmul, _, _, _⟩
  have hx_eq : x = 2 ^ a * 3 ^ b - 7 := by omega
  let q_c := (a - 2) / 3
  let a0 := a - 3 * q_c
  let b0 := b + 2 * q_c
  have hb0_ge3 : b0 ≥ 3 := by dsimp [b0, q_c]; omega
  have ha0_234 : a0 = 2 ∨ a0 = 3 ∨ a0 = 4 := by dsimp [a0, q_c]; omega
  have hclimb := cousin_diamond14_cone5_two_step_climb q_c a b (by dsimp [q_c]; omega) hb1
  rw [← hx_eq] at hclimb
  change cousinDiamond14Iter (2 * q_c) x = 2 ^ a0 * 3 ^ b0 - 7 at hclimb
  have hbound_x : ∀ ex : Nat, ex ≤ b0 + 8 -> 2 * q_c + ex ≤ x := by
    intro ex hex
    have hprod := Nat.mul_le_mul (pow2_ge_six_mul_ge5 a ha5) (pow3_ge_add_two_ge1 b hb1)
    rw [hmul.symm] at hprod
    have hab : 6 * b ≤ 6 * a * b := by
      rw [Nat.mul_comm (6 * a) b, ← Nat.mul_assoc, Nat.mul_comm b 6]
      simpa using Nat.mul_le_mul_left (6 * b) (by omega : 1 ≤ a)
    rw [show (6 * a) * (b + 2) = 6 * a * b + 12 * a by rw [Nat.mul_add]; omega] at hprod
    dsimp [q_c, b0] at hex ⊢; omega
  have hd_3 := (cousin_diamond14_a0_3_drain b0 hb0_ge3).2.2.2
  rcases cousin_diamond14_a0_2_and_4_drain b0 hb0_ge3 with ⟨hd_2, hd_4⟩
  rcases ha0_234 with ha2 | ha3 | ha4
  · have hkx := hbound_x (b0 + 3) (by omega)
    refine ⟨a, b, 2 * q_c + (b0 + 3), ha5, hb1, hmul, hkx,
      Nat.le_trans (by omega : 2 * q_c + (b0 + 3) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond14Iter_add (2 * q_c) (b0 + 3) x, hclimb, ha2]; exact hd_2
  · have hkx := hbound_x ((b0 - 1) / 2 + 7) (by omega)
    refine ⟨a, b, 2 * q_c + ((b0 - 1) / 2 + 7), ha5, hb1, hmul, hkx,
      Nat.le_trans (by omega : 2 * q_c + ((b0 - 1) / 2 + 7) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond14Iter_add (2 * q_c) ((b0 - 1) / 2 + 7) x, hclimb, ha3]; exact hd_3
  · have hkx := hbound_x ((b0 - 1) / 2 + 8) (by omega)
    refine ⟨a, b, 2 * q_c + ((b0 - 1) / 2 + 8), ha5, hb1, hmul, hkx,
      Nat.le_trans (by omega : 2 * q_c + ((b0 - 1) / 2 + 8) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond14Iter_add (2 * q_c) ((b0 - 1) / 2 + 8) x, hclimb, ha4]; exact hd_4

private theorem lift_cone_step_to_d14 (x y D : Nat) (hD8 : D ≥ 8) (hx_ge : x ≥ 2000)
    (hnc15 : ¬ isDiamond14Cone15 x)
    (hd13 : cousinDiamond13Step x = y)
    (hy_div : y = (3 * x + 1) / D)
    (hret_y : ∃ ky : Nat, ky ≤ y ∧ cousinDiamond14Iter ky y = 1) :
    ∃ k : Nat, k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond14Step x = y ∧ cousinDiamond14Iter k x = 1 := by
  rcases hret_y with ⟨ky, hky_y, hky_1⟩
  have hstep : cousinDiamond14Step x = y := (d14_eq_d13_of_not_cone15 x hnc15).trans hd13
  have hy_lt : y + 1 ≤ x := by
    have hdiv : y * D ≤ 3 * x + 1 := by rw [hy_div]; exact Nat.div_mul_le_self (3 * x + 1) D
    have h8 : y * 8 ≤ y * D := Nat.mul_le_mul_left y hD8
    omega
  refine ⟨1 + ky, by omega, Nat.le_trans (by omega : 1 + ky ≤ x + 1) (cousinDiamond2Phi_ge_succ x), hstep, ?_⟩
  rw [cousinDiamond14Iter_add 1 ky x, show cousinDiamond14Iter 1 x = y from hstep]; exact hky_1

/--
  Theorem W17.3g (`cousin_diamond14_cones4to15_exact_return`, `zero custom axioms`):
  Exact 12-Tier `ω^12` Multi-Block Return Across Cones 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, AND 15
  of `T_diamond14` (`Branch P5.16`, `W17_H3`).
-/
theorem cousin_diamond14_cones4to15_exact_return :
    (∀ x : Nat, isDiamond3Cone4 x ->
      ∃ k : Nat, k ≤ cousinDiamond2Phi x ∧ cousinDiamond14Iter k x = 1) ∧
    (∀ x : Nat, isDiamond4Cone5 x ->
      ∃ (a b k : Nat),
        a ≥ 5 ∧ b ≥ 1 ∧ x + 7 = 2 ^ a * 3 ^ b ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond14Iter k x = 1) ∧
    (∀ x : Nat, isDiamond5Cone6 x ->
      ∃ (e f k : Nat),
        e ≥ 8 ∧ f ≥ 2 ∧ x + 19 = 2 ^ e * 3 ^ f ∧
        cousinDiamond14Step x = 2 ^ (e - 3) * 3 ^ (f + 1) - 7 ∧
        isDiamond4Cone5 (cousinDiamond14Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond14Iter k x = 1) ∧
    (∀ x : Nat, isDiamond6Cone7 x ->
      ∃ (g h k : Nat),
        g ≥ 15 ∧ h ≥ 2 ∧ x + 811 = 2 ^ g * 3 ^ h ∧
        cousinDiamond14Step x = 2 ^ (g - 7) * 3 ^ (h + 1) - 19 ∧
        isDiamond5Cone6 (cousinDiamond14Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond14Iter k x = 1) ∧
    (∀ x : Nat, isDiamond7Cone8 x ->
      ∃ (u v k : Nat),
        u ≥ 22 ∧ v ≥ 1 ∧ x + 34603 = 2 ^ u * 3 ^ v ∧
        cousinDiamond14Step x = 2 ^ (u - 7) * 3 ^ (v + 1) - 811 ∧
        isDiamond6Cone7 (cousinDiamond14Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond14Iter k x = 1) ∧
    (∀ x : Nat, isDiamond8Cone9 x ->
      ∃ (w z k : Nat),
        w ≥ 25 ∧ z ≥ 1 ∧ x + 92275 = 2 ^ w * 3 ^ z ∧
        cousinDiamond14Step x = 2 ^ (w - 3) * 3 ^ (z + 1) - 34603 ∧
        isDiamond7Cone8 (cousinDiamond14Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond14Iter k x = 1) ∧
    (∀ x : Nat, isDiamond9Cone10 x ->
      ∃ (p q k : Nat),
        p ≥ 28 ∧ q ≥ 1 ∧ x + 246067 = 2 ^ p * 3 ^ q ∧
        cousinDiamond14Step x = 2 ^ (p - 3) * 3 ^ (q + 1) - 92275 ∧
        isDiamond8Cone9 (cousinDiamond14Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond14Iter k x = 1) ∧
    (∀ x : Nat, isDiamond10Cone11 x ->
      ∃ (r s k : Nat),
        r ≥ 31 ∧ s ≥ 1 ∧ x + 656179 = 2 ^ r * 3 ^ s ∧
        cousinDiamond14Step x = 2 ^ (r - 3) * 3 ^ (s + 1) - 246067 ∧
        isDiamond9Cone10 (cousinDiamond14Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond14Iter k x = 1) ∧
    (∀ x : Nat, isDiamond11Cone12 x ->
      ∃ (m n k : Nat),
        m ≥ 34 ∧ n ≥ 1 ∧ x + 1749811 = 2 ^ m * 3 ^ n ∧
        cousinDiamond14Step x = 2 ^ (m - 3) * 3 ^ (n + 1) - 656179 ∧
        isDiamond10Cone11 (cousinDiamond14Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond14Iter k x = 1) ∧
    (∀ x : Nat, isDiamond12Cone13 x ->
      ∃ (a b k : Nat),
        a ≥ 39 ∧ b ≥ 1 ∧ x + 18664651 = 2 ^ a * 3 ^ b ∧
        cousinDiamond14Step x = 2 ^ (a - 5) * 3 ^ (b + 1) - 1749811 ∧
        isDiamond11Cone12 (cousinDiamond14Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond14Iter k x = 1) ∧
    (∀ x : Nat, isDiamond13Cone14 x ->
      ∃ (k_e m_e k : Nat),
        k_e ≥ 46 ∧ m_e ≥ 1 ∧ x + 796358443 = 2 ^ k_e * 3 ^ m_e ∧
        cousinDiamond14Step x = 2 ^ (k_e - 7) * 3 ^ (m_e + 1) - 18664651 ∧
        isDiamond12Cone13 (cousinDiamond14Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond14Iter k x = 1) ∧
    (∀ x : Nat, isDiamond14Cone15 x ->
      ∃ (a_e b_e k : Nat),
        a_e ≥ 51 ∧ b_e ≥ 1 ∧ x + 8494490059 = 2 ^ a_e * 3 ^ b_e ∧
        cousinDiamond14Step x = 2 ^ (a_e - 5) * 3 ^ (b_e + 1) - 796358443 ∧
        isDiamond13Cone14 (cousinDiamond14Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond14Iter k x = 1) := by
  have hw16 := cousin_diamond13_cones4to14_exact_return
  have hc6_ret : ∀ x : Nat, isDiamond5Cone6 x ->
      ∃ (e f k : Nat), e ≥ 8 ∧ f ≥ 2 ∧ x + 19 = 2 ^ e * 3 ^ f ∧
        cousinDiamond14Step x = 2 ^ (e - 3) * 3 ^ (f + 1) - 7 ∧
        isDiamond4Cone5 (cousinDiamond14Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond14Iter k x = 1 := by
    intro x hc6
    rcases hw16.2.2.1 x hc6 with ⟨e, f, _, he8, hf2, hmul, hd13, hc5_y, _, _, _⟩
    rw [hd13] at hc5_y
    rcases cousin_diamond14_cone5_return_aux _ hc5_y with ⟨_, _, ky, _, _, _, hky_y, _, hky_1⟩
    have hnc15 : ¬ isDiamond14Cone15 x := not_cone15_of_mod32_ne_21 x (by
      have h := congrArg (· % 32) hc6.2.1; rw [Nat.mod_mod_of_dvd x (by decide : 32 ∣ 256)] at h; omega)
    have hy_div : 2 ^ (e - 3) * 3 ^ (f + 1) - 7 = (3 * x + 1) / 8 := by
      have hp2 : 2 ^ e = 8 * 2 ^ (e - 3) := by
        conv => lhs; rw [show e = 3 + (e - 3) by omega, Nat.pow_add]
      have h3x : 3 * (x + 19) = 8 * (2 ^ (e - 3) * 3 ^ (f + 1)) := by
        rw [hmul, hp2, Nat.pow_succ 3 f]; ac_rfl
      have hge := hc6.1; omega
    rcases lift_cone_step_to_d14 x _ 8 (by decide) (by have := hc6.1; omega) hnc15 hd13 hy_div ⟨ky, hky_y, hky_1⟩ with
      ⟨k, hkx, hkphi, hst, hk1⟩
    exact ⟨e, f, k, he8, hf2, hmul, hst, by rw [hst]; exact hc5_y, hkx, hkphi, hk1⟩
  have hc7_ret : ∀ x : Nat, isDiamond6Cone7 x ->
      ∃ (g h k : Nat), g ≥ 15 ∧ h ≥ 2 ∧ x + 811 = 2 ^ g * 3 ^ h ∧
        cousinDiamond14Step x = 2 ^ (g - 7) * 3 ^ (h + 1) - 19 ∧
        isDiamond5Cone6 (cousinDiamond14Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond14Iter k x = 1 := by
    intro x hc7
    rcases hw16.2.2.2.1 x hc7 with ⟨g, h, _, hg15, hh2, hmul, hd13, hc6_y, _, _, _⟩
    rw [hd13] at hc6_y
    rcases hc6_ret _ hc6_y with ⟨_, _, ky, _, _, _, _, _, hky_y, _, hky_1⟩
    have hnc15 : ¬ isDiamond14Cone15 x := not_cone15_of_mod64_ne_53 x (by
      have h64 := congrArg (· % 64) hc7.2.1
      rw [Nat.mod_mod_of_dvd x (by decide : 64 ∣ 32768),
          show 31957 % 64 = 21 by decide] at h64; omega)
    have hy_div : 2 ^ (g - 7) * 3 ^ (h + 1) - 19 = (3 * x + 1) / 128 := by
      have hp2 : 2 ^ g = 128 * 2 ^ (g - 7) := by
        conv => lhs; rw [show g = 7 + (g - 7) by omega, Nat.pow_add]
      have h3x : 3 * (x + 811) = 128 * (2 ^ (g - 7) * 3 ^ (h + 1)) := by
        rw [hmul, hp2, Nat.pow_succ 3 h]; ac_rfl
      have hge := hc7.1; omega
    rcases lift_cone_step_to_d14 x _ 128 (by decide) (by have := hc7.1; omega) hnc15 hd13 hy_div ⟨ky, hky_y, hky_1⟩ with
      ⟨k, hkx, hkphi, hst, hk1⟩
    exact ⟨g, h, k, hg15, hh2, hmul, hst, by rw [hst]; exact hc6_y, hkx, hkphi, hk1⟩
  have hc8_ret : ∀ x : Nat, isDiamond7Cone8 x ->
      ∃ (u v k : Nat), u ≥ 22 ∧ v ≥ 1 ∧ x + 34603 = 2 ^ u * 3 ^ v ∧
        cousinDiamond14Step x = 2 ^ (u - 7) * 3 ^ (v + 1) - 811 ∧
        isDiamond6Cone7 (cousinDiamond14Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond14Iter k x = 1 := by
    intro x hc8
    rcases hw16.2.2.2.2.1 x hc8 with ⟨u, v, _, hu22, hv1, hmul, hd13, hc7_y, _, _, _⟩
    rw [hd13] at hc7_y
    rcases hc7_ret _ hc7_y with ⟨_, _, ky, _, _, _, _, _, hky_y, _, hky_1⟩
    have hnc15 : ¬ isDiamond14Cone15 x := not_cone15_of_mod64_ne_53 x (by
      have h64 := congrArg (· % 64) hc8.2.1
      rw [Nat.mod_mod_of_dvd x (by decide : 64 ∣ 4194304),
          show 4159701 % 64 = 21 by decide] at h64; omega)
    have hy_div : 2 ^ (u - 7) * 3 ^ (v + 1) - 811 = (3 * x + 1) / 128 := by
      have hp2 : 2 ^ u = 128 * 2 ^ (u - 7) := by
        conv => lhs; rw [show u = 7 + (u - 7) by omega, Nat.pow_add]
      have h3x : 3 * (x + 34603) = 128 * (2 ^ (u - 7) * 3 ^ (v + 1)) := by
        rw [hmul, hp2, Nat.pow_succ 3 v]; ac_rfl
      have hge := hc8.1; omega
    rcases lift_cone_step_to_d14 x _ 128 (by decide) (by have := hc8.1; omega) hnc15 hd13 hy_div ⟨ky, hky_y, hky_1⟩ with
      ⟨k, hkx, hkphi, hst, hk1⟩
    exact ⟨u, v, k, hu22, hv1, hmul, hst, by rw [hst]; exact hc7_y, hkx, hkphi, hk1⟩
  have hc9_ret : ∀ x : Nat, isDiamond8Cone9 x ->
      ∃ (w z k : Nat), w ≥ 25 ∧ z ≥ 1 ∧ x + 92275 = 2 ^ w * 3 ^ z ∧
        cousinDiamond14Step x = 2 ^ (w - 3) * 3 ^ (z + 1) - 34603 ∧
        isDiamond7Cone8 (cousinDiamond14Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond14Iter k x = 1 := by
    intro x hc9
    rcases hw16.2.2.2.2.2.1 x hc9 with ⟨w, z, _, hw25, hz1, hmul, hd13, hc8_y, _, _, _⟩
    rw [hd13] at hc8_y
    rcases hc8_ret _ hc8_y with ⟨_, _, ky, _, _, _, _, _, hky_y, _, hky_1⟩
    have hnc15 : ¬ isDiamond14Cone15 x := not_cone15_of_mod32_ne_21 x (by
      have h := congrArg (· % 32) hc9.2.1
      rw [Nat.mod_mod_of_dvd x (by decide : 32 ∣ 33554432),
          show 33462157 % 32 = 13 by decide] at h; omega)
    have hy_div : 2 ^ (w - 3) * 3 ^ (z + 1) - 34603 = (3 * x + 1) / 8 := by
      have hp2 : 2 ^ w = 8 * 2 ^ (w - 3) := by
        conv => lhs; rw [show w = 3 + (w - 3) by omega, Nat.pow_add]
      have h3x : 3 * (x + 92275) = 8 * (2 ^ (w - 3) * 3 ^ (z + 1)) := by
        rw [hmul, hp2, Nat.pow_succ 3 z]; ac_rfl
      have hge := hc9.1; omega
    rcases lift_cone_step_to_d14 x _ 8 (by decide) (by have := hc9.1; omega) hnc15 hd13 hy_div ⟨ky, hky_y, hky_1⟩ with
      ⟨k, hkx, hkphi, hst, hk1⟩
    exact ⟨w, z, k, hw25, hz1, hmul, hst, by rw [hst]; exact hc8_y, hkx, hkphi, hk1⟩
  have hc10_ret : ∀ x : Nat, isDiamond9Cone10 x ->
      ∃ (p q k : Nat), p ≥ 28 ∧ q ≥ 1 ∧ x + 246067 = 2 ^ p * 3 ^ q ∧
        cousinDiamond14Step x = 2 ^ (p - 3) * 3 ^ (q + 1) - 92275 ∧
        isDiamond8Cone9 (cousinDiamond14Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond14Iter k x = 1 := by
    intro x hc10
    rcases hw16.2.2.2.2.2.2.1 x hc10 with ⟨p, q, _, hp28, hq1, hmul, hd13, hc9_y, _, _, _⟩
    rw [hd13] at hc9_y
    rcases hc9_ret _ hc9_y with ⟨_, _, ky, _, _, _, _, _, hky_y, _, hky_1⟩
    have hnc15 : ¬ isDiamond14Cone15 x := not_cone15_of_mod32_ne_21 x (by
      have h := congrArg (· % 32) hc10.2.1
      rw [Nat.mod_mod_of_dvd x (by decide : 32 ∣ 268435456),
          show 268189389 % 32 = 13 by decide] at h; omega)
    have hy_div : 2 ^ (p - 3) * 3 ^ (q + 1) - 92275 = (3 * x + 1) / 8 := by
      have hp2 : 2 ^ p = 8 * 2 ^ (p - 3) := by
        conv => lhs; rw [show p = 3 + (p - 3) by omega, Nat.pow_add]
      have h3x : 3 * (x + 246067) = 8 * (2 ^ (p - 3) * 3 ^ (q + 1)) := by
        rw [hmul, hp2, Nat.pow_succ 3 q]; ac_rfl
      have hge := hc10.1; omega
    rcases lift_cone_step_to_d14 x _ 8 (by decide) (by have := hc10.1; omega) hnc15 hd13 hy_div ⟨ky, hky_y, hky_1⟩ with
      ⟨k, hkx, hkphi, hst, hk1⟩
    exact ⟨p, q, k, hp28, hq1, hmul, hst, by rw [hst]; exact hc9_y, hkx, hkphi, hk1⟩
  have hc11_ret : ∀ x : Nat, isDiamond10Cone11 x ->
      ∃ (r s k : Nat), r ≥ 31 ∧ s ≥ 1 ∧ x + 656179 = 2 ^ r * 3 ^ s ∧
        cousinDiamond14Step x = 2 ^ (r - 3) * 3 ^ (s + 1) - 246067 ∧
        isDiamond9Cone10 (cousinDiamond14Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond14Iter k x = 1 := by
    intro x hc11
    rcases hw16.2.2.2.2.2.2.2.1 x hc11 with ⟨r, s, _, hr31, hs1, hmul, hd13, hc10_y, _, _, _⟩
    rw [hd13] at hc10_y
    rcases hc10_ret _ hc10_y with ⟨_, _, ky, _, _, _, _, _, hky_y, _, hky_1⟩
    have hnc15 : ¬ isDiamond14Cone15 x := not_cone15_of_mod32_ne_21 x (by rw [mod32_of_cone11 x hc11]; decide)
    have hy_div : 2 ^ (r - 3) * 3 ^ (s + 1) - 246067 = (3 * x + 1) / 8 := by
      have hp2 : 2 ^ r = 8 * 2 ^ (r - 3) := by
        conv => lhs; rw [show r = 3 + (r - 3) by omega, Nat.pow_add]
      have h3x : 3 * (x + 656179) = 8 * (2 ^ (r - 3) * 3 ^ (s + 1)) := by
        rw [hmul, hp2, Nat.pow_succ 3 s]; ac_rfl
      have hge := hc11.1; omega
    rcases lift_cone_step_to_d14 x _ 8 (by decide) (by have := hc11.1; omega) hnc15 hd13 hy_div ⟨ky, hky_y, hky_1⟩ with
      ⟨k, hkx, hkphi, hst, hk1⟩
    exact ⟨r, s, k, hr31, hs1, hmul, hst, by rw [hst]; exact hc10_y, hkx, hkphi, hk1⟩
  have hc12_ret : ∀ x : Nat, isDiamond11Cone12 x ->
      ∃ (m n k : Nat), m ≥ 34 ∧ n ≥ 1 ∧ x + 1749811 = 2 ^ m * 3 ^ n ∧
        cousinDiamond14Step x = 2 ^ (m - 3) * 3 ^ (n + 1) - 656179 ∧
        isDiamond10Cone11 (cousinDiamond14Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond14Iter k x = 1 := by
    intro x hc12
    rcases hw16.2.2.2.2.2.2.2.2.1 x hc12 with ⟨m, n, _, hm34, hn1, hmul, hd13, hc11_y, _, _, _⟩
    rw [hd13] at hc11_y
    rcases hc11_ret _ hc11_y with ⟨_, _, ky, _, _, _, _, _, hky_y, _, hky_1⟩
    have hnc15 : ¬ isDiamond14Cone15 x := not_cone15_of_mod32_ne_21 x (by rw [mod32_of_cone12 x hc12]; decide)
    have hy_div : 2 ^ (m - 3) * 3 ^ (n + 1) - 656179 = (3 * x + 1) / 8 := by
      have hp2 : 2 ^ m = 8 * 2 ^ (m - 3) := by
        conv => lhs; rw [show m = 3 + (m - 3) by omega, Nat.pow_add]
      have h3x : 3 * (x + 1749811) = 8 * (2 ^ (m - 3) * 3 ^ (n + 1)) := by
        rw [hmul, hp2, Nat.pow_succ 3 n]; ac_rfl
      have hge := hc12.1; omega
    rcases lift_cone_step_to_d14 x _ 8 (by decide) (by have := hc12.1; omega) hnc15 hd13 hy_div ⟨ky, hky_y, hky_1⟩ with
      ⟨k, hkx, hkphi, hst, hk1⟩
    exact ⟨m, n, k, hm34, hn1, hmul, hst, by rw [hst]; exact hc11_y, hkx, hkphi, hk1⟩
  have hc13_ret : ∀ x : Nat, isDiamond12Cone13 x ->
      ∃ (a b k : Nat), a ≥ 39 ∧ b ≥ 1 ∧ x + 18664651 = 2 ^ a * 3 ^ b ∧
        cousinDiamond14Step x = 2 ^ (a - 5) * 3 ^ (b + 1) - 1749811 ∧
        isDiamond11Cone12 (cousinDiamond14Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond14Iter k x = 1 := by
    intro x hc13
    rcases hw16.2.2.2.2.2.2.2.2.2.1 x hc13 with ⟨a, b, _, ha39, hb1, hmul, hd13, hc12_y, _, _, _⟩
    rw [hd13] at hc12_y
    rcases hc12_ret _ hc12_y with ⟨_, _, ky, _, _, _, _, _, hky_y, _, hky_1⟩
    have hnc15 : ¬ isDiamond14Cone15 x := not_cone15_of_mod512_ne_53 x (by
      have h := congrArg (· % 512) hc13.2.1
      rw [Nat.mod_mod_of_dvd x (by decide : 512 ∣ 549755813888),
          show 549737149237 % 512 = 309 by decide] at h; omega)
    have hy_div : 2 ^ (a - 5) * 3 ^ (b + 1) - 1749811 = (3 * x + 1) / 32 := by
      have hp2 : 2 ^ a = 32 * 2 ^ (a - 5) := by
        conv => lhs; rw [show a = 5 + (a - 5) by omega, Nat.pow_add]
      have h3x : 3 * (x + 18664651) = 32 * (2 ^ (a - 5) * 3 ^ (b + 1)) := by
        rw [hmul, hp2, Nat.pow_succ 3 b]; ac_rfl
      have hge := hc13.1; omega
    rcases lift_cone_step_to_d14 x _ 32 (by decide) (by have := hc13.1; omega) hnc15 hd13 hy_div ⟨ky, hky_y, hky_1⟩ with
      ⟨k, hkx, hkphi, hst, hk1⟩
    exact ⟨a, b, k, ha39, hb1, hmul, hst, by rw [hst]; exact hc12_y, hkx, hkphi, hk1⟩
  have hc14_ret : ∀ x : Nat, isDiamond13Cone14 x ->
      ∃ (k_e m_e k : Nat), k_e ≥ 46 ∧ m_e ≥ 1 ∧ x + 796358443 = 2 ^ k_e * 3 ^ m_e ∧
        cousinDiamond14Step x = 2 ^ (k_e - 7) * 3 ^ (m_e + 1) - 18664651 ∧
        isDiamond12Cone13 (cousinDiamond14Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond14Iter k x = 1 := by
    intro x hc14
    rcases hw16.2.2.2.2.2.2.2.2.2.2 x hc14 with ⟨k_e, m_e, _, hk46, hm1, hmul, hd13, hc13_y, _, _, _⟩
    rw [hd13] at hc13_y
    rcases hc13_ret _ hc13_y with ⟨_, _, ky, _, _, _, _, _, hky_y, _, hky_1⟩
    have hnc15 : ¬ isDiamond14Cone15 x := not_cone15_of_mod64_ne_53 x (by
      have h := congrArg (· % 64) hc14.2.1
      rw [Nat.mod_mod_of_dvd x (by decide : 64 ∣ 70368744177664),
          show 70367947819221 % 64 = 21 by decide] at h; omega)
    have hy_div : 2 ^ (k_e - 7) * 3 ^ (m_e + 1) - 18664651 = (3 * x + 1) / 128 := by
      have hp2 : 2 ^ k_e = 128 * 2 ^ (k_e - 7) := by
        conv => lhs; rw [show k_e = 7 + (k_e - 7) by omega, Nat.pow_add]
      have h3x : 3 * (x + 796358443) = 128 * (2 ^ (k_e - 7) * 3 ^ (m_e + 1)) := by
        rw [hmul, hp2, Nat.pow_succ 3 m_e]; ac_rfl
      have hge := hc14.1; omega
    rcases lift_cone_step_to_d14 x _ 128 (by decide) (by have := hc14.1; omega) hnc15 hd13 hy_div ⟨ky, hky_y, hky_1⟩ with
      ⟨k, hkx, hkphi, hst, hk1⟩
    exact ⟨k_e, m_e, k, hk46, hm1, hmul, hst, by rw [hst]; exact hc13_y, hkx, hkphi, hk1⟩
  refine ⟨cousin_diamond14_cone4_return_aux, cousin_diamond14_cone5_return_aux,
          hc6_ret, hc7_ret, hc8_ret, hc9_ret, hc10_ret, hc11_ret, hc12_ret, hc13_ret, hc14_ret, ?_⟩
  intro x hc15
  have hraw_step : cousinDiamond14Step x = (3 * x + 1) / 32 := by
    unfold cousinDiamond14Step; simp only [hc15, ite_true]
  rcases hc15 with ⟨hx_ge, hx51, hx3, hg1⟩
  have hdvd51 : 2251799813685248 ∣ (x + 8494490059) :=
    Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, hx51])
  clear hx51
  rcases (⟨8494490059 + x, rfl⟩ : ∃ N : Nat, N = 8494490059 + x) with ⟨N, hN_def⟩
  rw [← hN_def] at hg1
  have hN_pos : N > 0 := by clear hraw_step hdvd51 hx3 hg1; omega
  rcases decomp_2_3_exact N hN_pos with ⟨_, _, _, _, _, hmul⟩
  rw [hg1, Nat.mul_one] at hmul
  rcases eq_pow2_of_v2Pow_aux N N hN_pos (Nat.le_refl _) with ⟨a_e, ha_e⟩
  rcases eq_pow3_of_v3Pow_aux N N hN_pos (Nat.le_refl _) with ⟨b_e, hb_e⟩
  rw [ha_e, hb_e] at hmul
  have hmul_comm : x + 8494490059 = 2 ^ a_e * 3 ^ b_e := by
    rw [Nat.add_comm x 8494490059, ← hN_def, ← hmul]
  clear hg1 ha_e hb_e hN_def hmul hN_pos
  have ha51 : a_e ≥ 51 := by
    by_cases hlt : a_e < 51
    · exfalso
      have h51_sp : 2251799813685248 = 2 ^ (a_e + 1) * 2 ^ (50 - a_e) := by
        rw [← Nat.pow_add 2 (a_e + 1) (50 - a_e),
            show a_e + 1 + (50 - a_e) = 51 by clear hraw_step hx_ge hx3 hdvd51 hmul_comm; omega]
      rcases hdvd51 with ⟨c, hc⟩
      rw [hmul_comm, h51_sp, Nat.mul_assoc (2 ^ (a_e + 1)), Nat.pow_succ 2 a_e, Nat.mul_assoc (2 ^ a_e) 2] at hc
      have h3m_ev : 3 ^ b_e = 2 * (2 ^ (50 - a_e) * c) :=
        nat_mul_left_cancel_pos (2 ^ a_e) _ _ (pow2_pos_nat a_e) hc
      have ho := pow3_odd_nat_sec8 b_e
      rw [h3m_ev, Nat.mul_mod_right] at ho; cases ho
    · clear hraw_step hx_ge hx3 hdvd51 hmul_comm; omega
  clear hdvd51
  have hb1 : b_e ≥ 1 := by
    cases b_e with
    | zero =>
      rw [Nat.pow_zero, Nat.mul_one] at hmul_comm
      exact False.elim (pow2_mod3_nonzero_w5 a_e (by rw [← hmul_comm, Nat.add_mod, hx3]))
    | succ _ => clear hraw_step hx_ge hx3 hmul_comm ha51; omega
  clear hx3
  let y := 2 ^ (a_e - 5) * 3 ^ (b_e + 1) - 796358443
  have hstep_x : cousinDiamond14Step x = y := by
    rw [hraw_step]; dsimp only [y]
    have hp32 : 2 ^ a_e = 32 * 2 ^ (a_e - 5) := by
      conv => lhs; rw [show a_e = 5 + (a_e - 5) by clear hraw_step hx_ge hmul_comm hb1; omega, Nat.pow_add]
    have hprod_pos : 2 ^ (a_e - 5) * 3 ^ b_e ≥ 70368744177664 * 3 := by
      have h1 : 70368744177664 ≤ 2 ^ (a_e - 5) := by
        rw [show (70368744177664 : Nat) = 2 ^ 46 from rfl]
        exact pow2_mono_nat (by clear hraw_step hx_ge hmul_comm hb1 hp32; omega)
      have h2 : 3 ≤ 3 ^ b_e := by simpa using nat_pow_mono_exp_pos 3 1 b_e (by decide) hb1
      simpa using Nat.mul_le_mul h1 h2
    have h3_eq : 2 ^ (a_e - 5) * 3 ^ (b_e + 1) = 3 * (2 ^ (a_e - 5) * 3 ^ b_e) := by
      rw [Nat.pow_succ 3 b_e, ← Nat.mul_assoc, Nat.mul_comm _ 3]
    rw [h3_eq]
    have hx32 : x + 8494490059 = 32 * (2 ^ (a_e - 5) * 3 ^ b_e) := by rw [hmul_comm, hp32, Nat.mul_assoc]
    have h3x1 : 3 * x + 1 = (3 * (2 ^ (a_e - 5) * 3 ^ b_e) - 796358443) * 32 := by
      clear hraw_step ha51 hb1 hp32 h3_eq hmul_comm
      generalize 2 ^ (a_e - 5) * 3 ^ b_e = A at hprod_pos hx32 ⊢; omega
    rw [h3x1]
    clear hraw_step hx_ge ha51 hb1 hp32 h3_eq hmul_comm hx32 h3x1
    generalize 3 * (2 ^ (a_e - 5) * 3 ^ b_e) - 796358443 = Q; omega
  have hc14_y : isDiamond13Cone14 y :=
    isDiamond13Cone14_of_pow2_pow3_w17 (a_e - 5) (b_e + 1)
      (by clear hraw_step hx_ge hmul_comm hstep_x; omega)
      (by clear hraw_step hx_ge hmul_comm hstep_x; omega)
  rcases hc14_ret y hc14_y with ⟨_, _, ky, _, _, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hstep_eq : y = (3 * x + 1) / 32 := hstep_x.symm.trans hraw_step
    have hdiv : y * 32 ≤ 3 * x + 1 := by rw [hstep_eq]; exact Nat.div_mul_le_self (3 * x + 1) 32
    clear hraw_step hmul_comm hstep_x hc14_y hky_1 hstep_eq; omega
  refine ⟨a_e, b_e, 1 + ky, ha51, hb1, hmul_comm, hstep_x, by rw [hstep_x]; exact hc14_y,
          by clear hraw_step hmul_comm hstep_x hc14_y hky_1; omega,
          Nat.le_trans (by clear hraw_step hmul_comm hstep_x hc14_y hky_1; omega : 1 + ky ≤ x + 1)
            (cousinDiamond2Phi_ge_succ x), ?_⟩
  rw [cousinDiamond14Iter_add 1 ky x, show cousinDiamond14Iter 1 x = y from hstep_x]; exact hky_1

private theorem cousin_diamond14_reaches_one_within_phi :
    ∀ (B x : Nat), x > 0 -> cousinDiamond2Phi x ≤ B ->
      ∃ k : Nat, k ≤ B ∧ cousinDiamond14Iter k x = 1
  | 0, x, _, hB => by have := cousinDiamond2Phi_ge_succ x; omega
  | B + 1, x, hx, hB => by
    by_cases hx1 : x = 1
    · subst hx1; exact ⟨0, by omega, rfl⟩
    · by_cases hx2 : x = 2
      · subst hx2
        have hphi2 : cousinDiamond2Phi 2 = 28 := by decide
        rw [hphi2] at hB; exact ⟨1, by omega, by decide⟩
      · by_cases hc4 : isDiamond3Cone4 x
        · rcases cousin_diamond14_cones4to15_exact_return.1 x hc4 with ⟨k, hle, hk1⟩
          exact ⟨k, Nat.le_trans hle hB, hk1⟩
        · by_cases hc5 : isDiamond4Cone5 x
          · rcases cousin_diamond14_cones4to15_exact_return.2.1 x hc5 with ⟨_, _, k, _, _, _, _, hle, hk1⟩
            exact ⟨k, Nat.le_trans hle hB, hk1⟩
          · by_cases hc6 : isDiamond5Cone6 x
            · rcases cousin_diamond14_cones4to15_exact_return.2.2.1 x hc6 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
              exact ⟨k, Nat.le_trans hle hB, hk1⟩
            · by_cases hc7 : isDiamond6Cone7 x
              · rcases cousin_diamond14_cones4to15_exact_return.2.2.2.1 x hc7 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                exact ⟨k, Nat.le_trans hle hB, hk1⟩
              · by_cases hc8 : isDiamond7Cone8 x
                · rcases cousin_diamond14_cones4to15_exact_return.2.2.2.2.1 x hc8 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                  exact ⟨k, Nat.le_trans hle hB, hk1⟩
                · by_cases hc9 : isDiamond8Cone9 x
                  · rcases cousin_diamond14_cones4to15_exact_return.2.2.2.2.2.1 x hc9 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                    exact ⟨k, Nat.le_trans hle hB, hk1⟩
                  · by_cases hc10 : isDiamond9Cone10 x
                    · rcases cousin_diamond14_cones4to15_exact_return.2.2.2.2.2.2.1 x hc10 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                      exact ⟨k, Nat.le_trans hle hB, hk1⟩
                    · by_cases hc11 : isDiamond10Cone11 x
                      · rcases cousin_diamond14_cones4to15_exact_return.2.2.2.2.2.2.2.1 x hc11 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                        exact ⟨k, Nat.le_trans hle hB, hk1⟩
                      · by_cases hc12 : isDiamond11Cone12 x
                        · rcases cousin_diamond14_cones4to15_exact_return.2.2.2.2.2.2.2.2.1 x hc12 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                          exact ⟨k, Nat.le_trans hle hB, hk1⟩
                        · by_cases hc13 : isDiamond12Cone13 x
                          · rcases cousin_diamond14_cones4to15_exact_return.2.2.2.2.2.2.2.2.2.1 x hc13 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                            exact ⟨k, Nat.le_trans hle hB, hk1⟩
                          · by_cases hc14 : isDiamond13Cone14 x
                            · rcases cousin_diamond14_cones4to15_exact_return.2.2.2.2.2.2.2.2.2.2.1 x hc14 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                              exact ⟨k, Nat.le_trans hle hB, hk1⟩
                            · by_cases hc15 : isDiamond14Cone15 x
                              · rcases cousin_diamond14_cones4to15_exact_return.2.2.2.2.2.2.2.2.2.2.2 x hc15 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                                exact ⟨k, Nat.le_trans hle hB, hk1⟩
                              · have hdesc := cousin_diamond14_outside_cones4to15_descent_and_mod117_nonreentry.1 x
                                  (by omega) hc4 hc5 hc6 hc7 hc8 hc9 hc10 hc11 hc12 hc13 hc14 hc15
                                rcases cousin_diamond14_reaches_one_within_phi B (cousinDiamond14Step x)
                                  (cousinDiamond14Step_pos x hx) (by omega) with ⟨k, hk_le, hk_eq⟩
                                exact ⟨k + 1, by omega, hk_eq⟩

/--
  Theorem W17.3h (`cousin_diamond14_global_convergence`, `zero custom axioms`):
  Unconditional Global Convergence & Degree-5 Polynomial Stopping Bound for `T_diamond14`:
  For EVERY `x > 0`, `cousinDiamond14Iter` reaches `1` within `k ≤ (x + 1) ^ 3 + (x + 1) ^ 5` steps!
-/
theorem cousin_diamond14_global_convergence (x : Nat) (hx : x > 0) :
    ∃ k : Nat, k ≤ (x + 1) ^ 3 + (x + 1) ^ 5 ∧ cousinDiamond14Iter k x = 1 := by
  rcases cousin_diamond14_reaches_one_within_phi (cousinDiamond2Phi x) x hx (Nat.le_refl _) with
    ⟨k, hk_phi, hk1⟩
  exact ⟨k, Nat.le_trans hk_phi (cousinDiamond2Phi_upper_poly_bound x), hk1⟩

private theorem exists_non_desc_along_diamond14_iter_w17 :
    ∀ (terms : List LaurentTerm) (A0 B0 C0 N z : Nat),
      N ≥ 1 ->
      (∀ i : Nat, i < N ->
        cousinDiamond14Iter i z ≥ 3 ∧
        (cousinDiamond14Iter i z) % 2 = 1 ∧
        cousinDiamond14Step (cousinDiamond14Iter i z) ≥ 3) ->
      ¬ laurentDescProp terms A0 B0 C0 z (cousinDiamond14Iter N z) ->
      ∃ x : Nat,
        x ≥ 3 ∧ x % 2 = 1 ∧ cousinDiamond14Step x ≥ 3 ∧
        ¬ laurentDescProp terms A0 B0 C0 x (cousinDiamond14Step x)
  | _, _, _, _, 0, _, hN, _, _ => by omega
  | _, _, _, _, 1, z, _, hall, hnd => by
    rcases hall 0 (by decide) with ⟨hz3, hzo, hsz3⟩
    exact ⟨z, hz3, hzo, hsz3, hnd⟩
  | terms, A0, B0, C0, m + 2, z, _, hall, hnd => by
    if h0 : laurentDescProp terms A0 B0 C0 z (cousinDiamond14Step z) then
      have hnd_next : ¬ laurentDescProp terms A0 B0 C0 (cousinDiamond14Step z)
          (cousinDiamond14Iter (m + 1) (cousinDiamond14Step z)) :=
        fun hrest => hnd (laurentDescProp_trans terms A0 B0 C0 z (cousinDiamond14Step z) _ h0 hrest)
      exact exists_non_desc_along_diamond14_iter_w17 terms A0 B0 C0 (m + 1) (cousinDiamond14Step z)
        (by omega) (fun i hi => hall (i + 1) (by omega)) hnd_next
    else
      rcases hall 0 (by omega) with ⟨hz3, hzo, hsz3⟩
      exact ⟨z, hz3, hzo, hsz3, h0⟩

/--
  Theorem W17.3i (`cousin_diamond14_twelve_tier_cascade_and_laurent_impossibility`,
  `zero custom axioms`):
  1. Genuine 12-Tier `Cone 15 -> Cone 14 -> Cone 13 -> ... -> Cone 5` Cascade
     `6755390946565685 -> 633317901240533 -> 14843388310325 -> 1391567654093 -> 521837870285 ->
      195689201357 -> 73383450509 -> 27518793941 -> 644971733 -> 15116525 -> 5668697` & Unbounded
     `r`-Block Spiral Climb `cousinDiamond14Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5`!
  2. Universal `∀ L ≥ 1` Multi-Term Laurent Valuation Impossibility on `cousinDiamond14Step`!
-/
theorem cousin_diamond14_twelve_tier_cascade_and_laurent_impossibility :
    cousinDiamond14Step 6755390946565685 = 633317901240533 ∧
    cousinDiamond14Step 633317901240533 = 14843388310325 ∧
    cousinDiamond14Step 14843388310325 = 1391567654093 ∧
    cousinDiamond14Step 1391567654093 = 521837870285 ∧
    cousinDiamond14Step 521837870285 = 195689201357 ∧
    cousinDiamond14Step 195689201357 = 73383450509 ∧
    cousinDiamond14Step 73383450509 = 27518793941 ∧
    cousinDiamond14Step 27518793941 = 644971733 ∧
    cousinDiamond14Step 644971733 = 15116525 ∧
    cousinDiamond14Step 15116525 = 5668697 ∧
    (∀ (r j : Nat), r ≥ 1 -> j ≤ r ->
      cousinDiamond14Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5) ∧
    (∀ (terms : List LaurentTerm) (A0 B0 C0 : Nat),
      (∃ t ∈ terms, t.coeff > 0) ->
      ∃ x : Nat,
        x ≥ 3 ∧ x % 2 = 1 ∧ cousinDiamond14Step x ≥ 3 ∧
        ¬ (evalLaurentSumNum terms (cousinDiamond14Step x) * laurentValDen A0 B0 C0 x <
            evalLaurentSumNum terms x * laurentValDen A0 B0 C0 (cousinDiamond14Step x))) := by
  have hspiral : ∀ (r j : Nat), r ≥ 1 -> j ≤ r ->
      cousinDiamond14Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5 := by
    intro r j hr hj
    cases j with
    | zero => simp [cousinDiamond14Iter]
    | succ j' =>
      have hp16_ge16 : 16 ^ r ≥ 16 := by
        rw [show r = (r - 1) + 1 by omega, Nat.pow_succ]
        have := nat_pow_pos_of_pos 16 (by decide) (r - 1); omega
      let x0 := 4 * 16 ^ r - 5
      have hx0_m4 : x0 % 4 = 3 := by dsimp [x0]; omega
      have hx0_pow : 4 * 16 ^ r = 2 ^ (4 * r + 2) := by
        rw [show (16 : Nat) = 2 ^ 4 from rfl, pow_pow_eq_mul_w5 2 4 r,
            show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add 2 2 (4 * r), Nat.add_comm 2 (4 * r)]
      have hs_first : cousinDiamond14Step x0 = 2 ^ (4 * r + 1) * 3 ^ 1 - 7 := by
        rw [d14_eq_d13_of_not_cone15 x0 (not_cone15_of_mod4_eq_3 x0 hx0_m4),
            d13_eq_d12_of_not_cone14_w17 x0 (not_cone14_of_mod32_ne_21_w17 x0 (by omega)),
            d12_eq_d11_of_not_cone13_w17 x0 (not_cone13_of_mod32_ne_21_w17 x0 (by omega)),
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
      have hclimb := cousin_diamond14_cone5_two_step_climb j' (4 * r + 1) 1 (by omega) (by decide)
      let y_end := 2 ^ (4 * r + 1 - 3 * j') * 3 ^ (1 + 2 * j') - 7
      have hy_c5 := isDiamond4Cone5_of_pow2_pow3 (4 * r + 1 - 3 * j') (1 + 2 * j') (by omega) (by omega)
      have hs_last : cousinDiamond14Step y_end = 4 * 16 ^ (r - (j' + 1)) * 18 ^ (j' + 1) - 5 := by
        rw [d14_eq_d13_of_not_cone15 y_end (not_cone15_of_mod32_ne_21 y_end (by have := hy_c5.2.1; omega)),
            d13_eq_d12_of_not_cone14_w17 y_end (not_cone14_of_mod32_ne_21_w17 y_end (by have := hy_c5.2.1; omega)),
            d12_eq_d11_of_not_cone13_w17 y_end (not_cone13_of_mod32_ne_21_w17 y_end (by have := hy_c5.2.1; omega)),
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
          rw [← pow9_eq_pow3_double (j' + 1), ← mul_pow_w17s 2 9 (j' + 1)]
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
          cousinDiamond14Iter_add (1 + 2 * j') 1,
          cousinDiamond14Iter_add 1 (2 * j'),
          show cousinDiamond14Iter 1 x0 = 2 ^ (4 * r + 1) * 3 ^ 1 - 7 from hs_first, hclimb]
      exact hs_last
  refine ⟨by decide, by decide, by decide, by decide, by decide,
          by decide, by decide, by decide, by decide, by decide, hspiral, ?_⟩
  intro terms A0 B0 C0 hnonempty
  rcases three_family_multiterm_laurent_obstruction terms A0 B0 C0 hnonempty with
    h97 | ⟨j2, hj2⟩ | ⟨r, hr_pos, hr3⟩
  · have hs97 : cousinDiamond14Step 97 = 73 := by decide
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
    have hstep_xj2 : cousinDiamond14Step xj2 = yj2 := by
      rw [d14_eq_d13_of_not_cone15 xj2 (not_cone15_of_mod8_ne_5 xj2 (by have := hc4_xj2.2.1; omega)),
          d13_eq_d12_of_not_cone14_w17 xj2 (not_cone14_of_mod32_ne_21_w17 xj2 (by have := hc4_xj2.2.1; omega)),
          d12_eq_d11_of_not_cone13_w17 xj2 (not_cone13_of_mod32_ne_21_w17 xj2 (by have := hc4_xj2.2.1; omega)),
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
        cousinDiamond14Iter i xr3 = 3 ^ i * 2 ^ (2 * r + 1 - i) - 1 ∧
        cousinDiamond14Iter i xr3 ≥ 7 ∧ (cousinDiamond14Iter i xr3) % 2 = 1 := by
      intro i hi
      have hf := cousin_diamond14_mersenne_scaled i (2 * r + 1) 1 (by omega) (by decide)
      rw [← hxr3_pow, Nat.mul_one] at hf
      have hprod_ge8 : 3 ^ i * 2 ^ (2 * r + 1 - i) ≥ 8 := by
        have h1 : 2 ^ i * 2 ^ (2 * r + 1 - i) ≤ 3 ^ i * 2 ^ (2 * r + 1 - i) :=
          Nat.mul_le_mul_right _ (pow2_le_pow3 i)
        rw [← Nat.pow_add, show i + (2 * r + 1 - i) = 2 * r + 1 by omega] at h1
        exact Nat.le_trans (pow2_mono_nat (by omega : 3 ≤ 2 * r + 1)) h1
      have hprod_ev : (3 ^ i * 2 ^ (2 * r + 1 - i)) % 2 = 0 := by
        rw [show 2 * r + 1 - i = (2 * r - i) + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc]; omega
      exact ⟨hf, by rw [hf]; omega, by rw [hf]; omega⟩
    have hiter_2r : cousinDiamond14Iter (2 * r) xr3 = zr := by
      have hf := (hglide_i (2 * r) (Nat.le_refl _)).1
      rw [hf, show 2 * r + 1 - 2 * r = 1 by omega, Nat.pow_one, ← pow9_eq_pow3_double r, Nat.mul_comm]
    have hstep_zr : cousinDiamond14Step zr = yr3 := by
      rw [d14_eq_d13_of_not_cone15 zr (not_cone15_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          d13_eq_d3_of_not_cones5to14_w17 zr
            (not_cone14_of_mod32_ne_21_w17 zr (by dsimp [zr]; omega))
            (not_cone13_of_mod32_ne_21_w17 zr (by dsimp [zr]; omega))
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
    have hiter_2r1 : cousinDiamond14Iter (2 * r + 1) xr3 = yr3 := by
      rw [cousinDiamond14Iter_add (2 * r) 1 xr3, hiter_2r]; exact hstep_zr
    have hall : ∀ i : Nat, i < 2 * r + 1 ->
        cousinDiamond14Iter i xr3 ≥ 3 ∧ (cousinDiamond14Iter i xr3) % 2 = 1 ∧
        cousinDiamond14Step (cousinDiamond14Iter i xr3) ≥ 3 := by
      intro i hi
      by_cases hlt : i < 2 * r
      · rcases hglide_i i (by omega) with ⟨_, hge7, hodd_i⟩
        rcases hglide_i (i + 1) (by omega) with ⟨_, hge7_n, _⟩
        refine ⟨by omega, hodd_i, ?_⟩
        change cousinDiamond14Iter 1 (cousinDiamond14Iter i xr3) ≥ 3
        rw [← cousinDiamond14Iter_add i 1 xr3]; omega
      · rw [show i = 2 * r by omega, hiter_2r, hstep_zr]
        exact ⟨by dsimp [zr]; omega, by dsimp [zr]; omega, by dsimp [yr3]; omega⟩
    change ¬ laurentDescProp terms A0 B0 C0 xr3 yr3 at hr3
    rw [← hiter_2r1] at hr3
    exact exists_non_desc_along_diamond14_iter_w17 terms A0 B0 C0 (2 * r + 1) xr3 (by omega) hall hr3

set_option maxRecDepth 16384 in
/--
  Theorem W17.3j (`cousin_diamond14_counter_model_separation`, `[]` axioms):
  `T_diamond14` rejects ALL three Counter-Models (`M1 = Q_(6)^+` 5-cycle `(1, 7) -> ... -> (1, 7)`
  plus non-integers `(6755390946565685, 7)` and `(13510790387621429, 7)` bypassing Cone 15 by `W17.3d`,
  `M2 = Z^-` cycles `-1` and `-5 -> -7 -> -10 -> -5`, and `M3` supercritical `q = 7` 5-cycle at `5`),
  AND at the genuine `v_2(3x + 1) = 5` Cone-15 jumps
  `6755390946565685 -> 633317901240533 -> 14843388310325 -> 1391567654093 -> 521837870285 ->
   195689201357 -> 73383450509 -> 27518793941 -> 644971733 -> 15116525 -> 5668697`
  (`ZPOS_COUSIN_DIAMOND14_CONE15_6755390946565685_JUMP`, `28` steps to `1`, `+16.22x` `Φ_2` jump)
  and `13510790387621429 -> 1266636598839509` (`25` steps to `1`) strictly increases `cousinDiamond2Phi`
  directly into `Cone 14 -> Cone 13 -> ... -> Cone 5`!
-/
theorem cousin_diamond14_counter_model_separation :
    cousinDiamond14StepInt (-1) = -1 ∧
    cousinDiamond14IterInt 3 (-5) = -5 ∧
    cousinDiamond14IterParam 7 5 5 = 5 ∧
    cousinDiamond14StepQ6 (1, 7) = (5, 7) ∧
    cousinDiamond14IterQ6 5 (1, 7) = (1, 7) ∧
    cousinDiamond14StepQ6 (6755390946565685, 7) = cousinDiamond13StepQ6 (6755390946565685, 7) ∧
    cousinDiamond14StepQ6 (13510790387621429, 7) = cousinDiamond13StepQ6 (13510790387621429, 7) ∧
    isDiamond14Cone15 13510790387621429 ∧
    cousinDiamond14Step 13510790387621429 = 1266636598839509 ∧
    cousinDiamond14Iter 25 13510790387621429 = 1 ∧
    isDiamond14Cone15 6755390946565685 ∧
    cousinDiamond14Step 6755390946565685 = 633317901240533 ∧
    cousinDiamond14StepInt 6755390946565685 = 633317901240533 ∧
    cousinDiamond14StepQ6 (6755390946565685, 1) = (633317901240533, 1) ∧
    isDiamond13Cone14 633317901240533 ∧
    isDiamond12Cone13 14843388310325 ∧
    isDiamond11Cone12 1391567654093 ∧
    isDiamond10Cone11 521837870285 ∧
    isDiamond9Cone10 195689201357 ∧
    isDiamond8Cone9 73383450509 ∧
    isDiamond7Cone8 27518793941 ∧
    isDiamond6Cone7 644971733 ∧
    isDiamond5Cone6 15116525 ∧
    isDiamond4Cone5 5668697 ∧
    cousinDiamond2Phi 6755390946565685 < cousinDiamond2Phi 633317901240533 ∧
    cousinDiamond14Iter 28 6755390946565685 = 1 := by
  decide


-- ============================================================================
-- SECTION 3: Front D (Branches P2.2 & P5.3) — Complete Mod-`118098` (`2 * 3^10`,
--            `w ≥ 11`) Markov Shift Bijection, Mod-`1024` 54-Prefix Lift,
--            Choice-Free 3-Adic Carry-Deficit Invariance, & `243x`-Compressed
--            Steeper-Slope (`c = 6`) Exponential Dyadic-Window Occupancy (`W17_H4`)
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Section 3A: Complete Mod-`118098` (`2 * 3^10`) Markov Bijection (`39366 / 118098`
--             Surviving Classes on `w ≥ 11`), Length-`9` Exhaustion (`u_esc10` at `w = 10`),
--             Length-`10` `Mod 1024` `1 + 8 + 21 + 19 + 5 = 54` Prefix Lift, &
--             `3 ^ (w - 11)` (`j = 10`) Multi-Step Fiber Equidistribution
-- ----------------------------------------------------------------------------

/-- Canonical ordered list of the `39366` (`= 2 * 3^9`) surviving mod-`118098` (`= 2 * 3^10`)
    suffix-shift classes `{r < 118098 | r % 6 = 1 ∨ r % 6 = 3}` on `w ≥ 11`. -/
def survivingMod118098List : List Nat :=
  (List.range 118098).filter (fun r => r % 6 == 1 || r % 6 == 3)

private theorem mem_survivingMod118098List_iff_w17 (r : Nat) :
    r ∈ survivingMod118098List ↔ (r < 118098 ∧ (r % 6 = 1 ∨ r % 6 = 3)) := by
  unfold survivingMod118098List
  rw [List.mem_filter, List.mem_range]
  simp only [Bool.or_eq_true, beq_iff_eq]

private theorem range_six_mul_surviving_len_w17 :
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
    have ih := range_six_mul_surviving_len_w17 n
    change ((List.range (6 * n)).filter p).length = 2 * n at ih
    omega

/-- Surviving mod-`1024` length-`10` prefix predicate (`54 = 2 * 27` residues lifting `Mod 512`). -/
def isSurvivingMod1024Bool (r : Nat) : Bool :=
  isSurvivingMod512Bool (r % 512)

/-- Canonical ordered list of the `54` surviving mod-`1024` residues. -/
def survivingMod1024Residues54 : List Nat :=
  (List.range 1024).filter isSurvivingMod1024Bool

/-- Exact weight-`k` (`k ∈ {10, 9, 8, 7, 6}`) surviving mod-`1024` length-`10` prefix predicate. -/
def isWeightKSurvivingMod1024Bool (k y : Nat) : Bool :=
  isSurvivingMod1024Bool (y % 1024) && decide (parityWeight (parityOfIter 10 (y % 1024)) = k)

def topWeight10Mod1024Residues1 : List Nat :=
  survivingMod1024Residues54.filter (isWeightKSurvivingMod1024Bool 10)

private theorem take_drop_split_eq_w17 :
    ∀ (k : Nat) (xs : List Bool), xs.take k ++ xs.drop k = xs
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, x :: xs => by
    simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append,
               take_drop_split_eq_w17 k xs]

private theorem take_len_of_ge_w17 :
    ∀ (k : Nat) (xs : List Bool), k ≤ xs.length -> (xs.take k).length = k
  | 0, _, _ => rfl
  | _ + 1, [], h => by simp at h
  | k + 1, _ :: xs, h => by
    simp only [List.length_cons] at h
    simp only [List.take_succ_cons, List.length_cons, take_len_of_ge_w17 k xs (by omega)]

private theorem len11_core_mod1024_prefix10_w17
    (p10 freeBits : List Bool) (q : Nat)
    (hp10_len : p10.length = 10)
    (hu : IsCoreParityWord (p10 ++ freeBits ++ [true])) :
    parityOfIter 10 (exactBackwardQuotient 1 (p10 ++ freeBits ++ [true]) q % 1024) = p10 := by
  let u := p10 ++ freeBits ++ [true]
  let y := exactBackwardQuotient 1 u q
  let K := backwardOneTotalSteps u q
  let shift := canonicalSuffixShift u 1 + q * (2 * 3 ^ (parityWeight u - 1))
  have hu_len : u.length = 10 + (freeBits.length + 1) := by
    dsimp [u]; rw [List.length_append, List.length_append, hp10_len, List.length_singleton]
    omega
  have hK_ge11 : K ≥ 11 := by unfold K backwardOneTotalSteps; omega
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
  have hKs10 : K = 10 + (K - 10) := by omega
  have hpar_sp := parityOfIter_append_split 10 (K - 10) y
  rw [← hKs10, ← hv_par] at hpar_sp
  have hv_p10 : v = p10 ++ (freeBits ++ [true] ++ List.replicate shift false) := by
    dsimp [v, u]
    rw [List.append_assoc p10 freeBits [true],
        List.append_assoc p10 (freeBits ++ [true]) (List.replicate shift false)]
  rw [hv_p10] at hpar_sp
  have hlen10 : p10.length = (parityOfIter 10 y).length := by
    rw [hp10_len, parityOfIter_length]
  have hp10_eq : parityOfIter 10 y = p10 :=
    (list_append_inj_left_eq_len _ _ _ _ hlen10 hpar_sp).1.symm
  have hy_div10 : y = y % 1024 + 2 ^ 10 * (y / 1024) := by
    have hdm := (Nat.div_add_mod y 1024).symm
    rw [show (2 : Nat) ^ 10 = 1024 from rfl]; omega
  have hpar10_mod : parityOfIter 10 y = parityOfIter 10 (y % 1024) := by
    conv => lhs; rw [hy_div10]
    exact parityOfIter_mod_pow2_shift 10 (y % 1024) (y / 1024)
  rw [← hpar10_mod, hp10_eq]

private theorem pow_mod_eq_pow_mod_w17 (b m : Nat) :
    ∀ e : Nat, (b ^ e) % m = ((b % m) ^ e) % m
  | 0 => rfl
  | e + 1 => by
    rw [Nat.pow_succ b e, Nat.pow_succ (b % m) e, Nat.mul_mod (b ^ e) b m,
        pow_mod_eq_pow_mod_w17 b m e, Nat.mul_mod ((b % m) ^ e % m) (b % m) m,
        Nat.mod_mod, ← Nat.mul_mod ((b % m) ^ e) (b % m) m]

private def len9SurvivingEscapeTable (r : Nat) : List Nat × Nat :=
  match r with
  | 27  => ([58], 31)
  | 31  => ([3, 33], 13)
  | 47  => ([27], 73)
  | 71  => ([5], 135)
  | 91  => ([5], 157)
  | 103 => ([1, 60], 27)
  | 111 => ([0, 22], 39)
  | 127 => ([68], 93)
  | 155 => ([2, 15], 73)
  | 159 => ([12, 39], 19)
  | 167 => ([3], 37)
  | 191 => ([4, 39], 31)
  | 231 => ([9], 121)
  | 239 => ([2, 57], 37)
  | 251 => ([39], 19)
  | 255 => ([69], 93)
  | 283 => ([38], 105)
  | 303 => ([6], 91)
  | 327 => ([24], 99)
  | 347 => ([9], 63)
  | 359 => ([42], 99)
  | 415 => ([17, 1], 25)
  | 423 => ([15], 81)
  | 447 => ([10, 28], 39)
  | 495 => ([2, 44], 39)
  | 507 => ([36], 43)
  | 511 => ([155], 13)
  | _   => ([0], 3)

private def checkLen9EscapeEntryBool (r : Nat) : Bool :=
  let pr := len9SurvivingEscapeTable r
  let pref := parityOfIter 9 r
  let u := pref ++ zeroRunsSuffix pr.1
  let L := u.length
  let w := parityWeight u
  let a := pr.2
  let C := affineCarry u
  let P2 := 2 ^ (L + a)
  let P3 := 3 ^ w
  let y := (P2 - C) / P3
  (u.head? == some true) &&
  (u.reverse.head? == some true) &&
  decide (L ≥ 10 ∧ 1 ≤ w ∧ w ≤ 10 ∧ 3 ≤ a ∧ a < 2 * 3 ^ (w - 1) ∧ C < P2) &&
  (P3 * y + C == P2) &&
  isSurvivingMod373248Bool y &&
  (y % 512 == r)

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 131072 in
private theorem len9_all27_surviving_escape_grid_cert :
    ∀ (hi : Fin 8) (lo : Fin 64),
      let rv := 64 * hi.val + lo.val
      isSurvivingMod512Bool rv = true -> checkLen9EscapeEntryBool rv = true := by
  decide

private theorem len9_all27_surviving_escape_sound (r : Fin 512)
    (hsurv : isSurvivingMod512Bool r.val = true) :
    ∃ u : List Bool,
      u.take 9 = parityOfIter 9 r.val ∧
      u.length ≥ 10 ∧
      parityWeight u ≤ 10 ∧
      IsFirstHitOnePair u 0 ∧
      IsSurvivingMod373248Class (exactBackwardQuotient 1 u 0) ∧
      exactBackwardQuotient 1 u 0 % 512 = r.val := by
  have hhi : r.val / 64 < 8 := by have := r.isLt; omega
  have hlo : r.val % 64 < 64 := Nat.mod_lt r.val (by decide)
  have hg := len9_all27_surviving_escape_grid_cert ⟨r.val / 64, hhi⟩ ⟨r.val % 64, hlo⟩
  dsimp only at hg
  rw [Nat.div_add_mod r.val 64] at hg
  have hc := hg hsurv
  unfold checkLen9EscapeEntryBool at hc
  dsimp only at hc
  let pr := len9SurvivingEscapeTable r.val
  let pref := parityOfIter 9 r.val
  let u := pref ++ zeroRunsSuffix pr.1
  let L := u.length
  let w := parityWeight u
  let a := pr.2
  let C := affineCarry u
  let P2 := 2 ^ (L + a)
  let P3 := 3 ^ w
  let y := (P2 - C) / P3
  rcases Bool.and_eq_true_iff.mp hc with ⟨hc1, hy512_b⟩
  rcases Bool.and_eq_true_iff.mp hc1 with ⟨hc2, hsurv373⟩
  rcases Bool.and_eq_true_iff.mp hc2 with ⟨hc3, heq_b⟩
  rcases Bool.and_eq_true_iff.mp hc3 with ⟨hc4, hbds_b⟩
  rcases Bool.and_eq_true_iff.mp hc4 with ⟨hhd_b, hrhd_b⟩
  rcases of_decide_eq_true hbds_b with ⟨hL10, hw1, hw10, ha3, ha_lt, hC_lt⟩
  have heq_y : P3 * y + C = P2 := beq_iff_eq.mp heq_b
  have hy512 : y % 512 = r.val := beq_iff_eq.mp hy512_b
  have hcore : IsCoreParityWord u := ⟨beq_iff_eq.mp hhd_b, beq_iff_eq.mp hrhd_b⟩
  have hsh_a : canonicalSuffixShift u 1 = a := by
    rcases canonicalSuffixShift_spec_unique u 1 hw1 (by decide) with ⟨_, _, huniq⟩
    symm
    apply huniq a ha_lt
    rw [Nat.mul_one]
    change P2 % P3 = C % P3
    rw [← heq_y, Nat.add_comm, Nat.add_mul_mod_self_left]
  have hfh : IsFirstHitOnePair u 0 :=
    (first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.2 u hcore).mpr (by rw [hsh_a]; exact ha3)
  have hbw_eq : exactBackwardQuotient 1 u 0 = y := by
    rcases one_generator_pos_odd_and_reaches_one u 0 hcore with ⟨_, _, heq_bw, _⟩
    have hst : backwardOneTotalSteps u 0 = L + a := by
      unfold backwardOneTotalSteps; rw [hsh_a]; dsimp [L]; omega
    rw [hst] at heq_bw
    change P2 = P3 * exactBackwardQuotient 1 u 0 + C at heq_bw
    exact Nat.eq_of_mul_eq_mul_left
      (by dsimp [P3]; exact nat_pow_pos_of_pos 3 (by decide) w)
      (Nat.add_right_cancel (heq_bw.symm.trans heq_y.symm))
  have htake9 : u.take 9 = pref := by
    have hplen : pref.length = 9 := parityOfIter_length 9 r.val
    have htake_pref : ∀ (xs ys : List Bool) (n : Nat), xs.length = n -> (xs ++ ys).take n = xs := by
      intro xs; induction xs with
      | nil => intro _ n hn; subst hn; rfl
      | cons x xtl ih =>
        intro ys n hn; cases n with
        | zero => simp at hn
        | succ n' => simp only [List.cons_append, List.take]; rw [ih ys n' (by simp at hn; omega)]
    exact htake_pref pref (zeroRunsSuffix pr.1) 9 hplen
  refine ⟨u, htake9, hL10, hw10, hfh, ?_, ?_⟩
  · rw [hbw_eq]; exact isSurvivingMod373248Bool_imp_class y hsurv373
  · rw [hbw_eq]; exact hy512

set_option exponentiation.threshold 8192 in
set_option maxRecDepth 131072 in
/--
  Theorem W17.4a (`markovShift_mod118098_bijection_and_mod1024_prefix54_lift`,
  `zero custom axioms`):
  Complete Mod-`118098` (`2 * 3^10`) Markov Bijection onto `39366` Surviving Classes (`w ≥ 11`),
  Exhaustive Length-`9` Prefix Bound (`∀ r < 512, w(pref_9) ≤ 9`) + Universal `27/27` Surviving
  `Mod 512` Length-`≥ 10` Weight-`≤ 10` Escape Theorem + All-Ones `511` Weight-`10` Escape Witness
  `u_esc10` (`ZPOS_DYADIC_ALLONES9_WEIGHT10_PREFIX_ESCAPE`, Proving ZERO Length-`9` Prefixes Force
  `w(u) ≥ 11`), Exact Length-`10` `Mod 1024` `1 + 8 + 21 + 19 + 5 = 54` Surviving Prefix Lift
  (`1023` Forces `w(u) ≥ 11` on `|u| ≥ 11`), Mod-`118098` Suffix Locks (`59049`, `98415`, &
  `{19683, 59049, 98415}`), & `3 ^ (w - 11)` (`j = 10`) Multi-Step Fiber Equidistribution
  (`Branch P5.3`, `W17_H4`).
-/
theorem markovShift_mod118098_bijection_and_mod1024_prefix54_lift :
    ((∀ (w a : Nat), w ≥ 10 -> a < 2 * 3 ^ (w - 1) ->
        markovShiftTrue w a % 118098 = markovShiftTrue 10 (a % 39366) % 118098) ∧
     survivingMod118098List.length = 39366 ∧
     (∀ x1 x2 : Fin 39366,
        markovShiftTrue 10 x1.val % 118098 = markovShiftTrue 10 x2.val % 118098 -> x1 = x2) ∧
     (∀ x : Fin 39366,
        markovShiftTrue 10 x.val % 118098 ∈ survivingMod118098List) ∧
     (∀ r ∈ survivingMod118098List,
        ∃ x : Fin 39366, markovShiftTrue 10 x.val % 118098 = r)) ∧
    ((∀ r : Fin 512, parityWeight (parityOfIter 9 r.val) ≤ 9) ∧
     (∀ r : Fin 512, isSurvivingMod512Bool r.val = true ->
       ∃ u : List Bool,
         u.take 9 = parityOfIter 9 r.val ∧
         u.length ≥ 10 ∧
         parityWeight u ≤ 10 ∧
         IsFirstHitOnePair u 0 ∧
         IsSurvivingMod373248Class (exactBackwardQuotient 1 u 0) ∧
         exactBackwardQuotient 1 u 0 % 512 = r.val) ∧
     (let u_esc10 : List Bool :=
        List.replicate 9 true ++ List.replicate 155 false ++ [true]
      u_esc10.length = 165 ∧
      parityWeight u_esc10 = 10 ∧
      IsFirstHitOnePair u_esc10 0 ∧
      exactBackwardQuotient 1 u_esc10 0 =
        6487840627110957342933758367292483113623774926335 ∧
      IsSurvivingMod373248Class (exactBackwardQuotient 1 u_esc10 0) ∧
      exactBackwardQuotient 1 u_esc10 0 % 512 = 511 ∧
      exactBackwardQuotient 1 u_esc10 0 % 1024 = 511) ∧
     survivingMod1024Residues54.length = 54 ∧
     topWeight10Mod1024Residues1 = [1023] ∧
     (survivingMod1024Residues54.filter (isWeightKSurvivingMod1024Bool 9)).length = 8 ∧
     (survivingMod1024Residues54.filter (isWeightKSurvivingMod1024Bool 8)).length = 21 ∧
     (survivingMod1024Residues54.filter (isWeightKSurvivingMod1024Bool 7)).length = 19 ∧
     (survivingMod1024Residues54.filter (isWeightKSurvivingMod1024Bool 6)).length = 5 ∧
     (∀ u : List Bool, IsCoreParityWord u -> parityWeight u ≥ 11 ->
        canonicalSuffixShift u 1 % 118098 ∈ survivingMod118098List) ∧
     (∀ (u : List Bool) (q : Nat),
        IsCoreParityWord u -> u.length ≥ 11 ->
        isWeightKSurvivingMod1024Bool 10 (exactBackwardQuotient 1 u q) = true ->
        parityWeight u ≥ 11 ∧ canonicalSuffixShift u 1 % 118098 ∈ survivingMod118098List)) ∧
    ((∀ pref : List Bool,
        canonicalSuffixShift (pref ++ List.replicate 10 true) 1 % 118098 = 19683 ∨
        canonicalSuffixShift (pref ++ List.replicate 10 true) 1 % 118098 = 59049 ∨
        canonicalSuffixShift (pref ++ List.replicate 10 true) 1 % 118098 = 98415) ∧
     (∀ pref : List Bool,
        canonicalSuffixShift (pref ++ List.replicate 11 true) 1 % 118098 = 59049 ∧
        canonicalSuffixShift (pref ++ ([true, false] ++ List.replicate 10 true)) 1 % 118098 = 98415)) ∧
    (∀ (tail : List Bool) (w r0 : Nat),
      w ≥ 11 -> r0 < 118098 ->
      let Mk := 2 * 3 ^ (10 + parityWeight tail)
      let N := 3 ^ (w - 11)
      let base := iterMarkovShift tail w r0 % Mk
      (∀ t : Nat, t < N ->
        ∃ q : Nat, q < N ∧ iterMarkovShift tail w (r0 + 118098 * t) = base + Mk * q) ∧
      (∀ q : Nat, q < N ->
        ∃ t : Nat, t < N ∧
          iterMarkovShift tail w (r0 + 118098 * t) = base + Mk * q ∧
          ∀ t' : Nat, t' < N ->
            iterMarkovShift tail w (r0 + 118098 * t') = base + Mk * q -> t' = t)) := by
  have h39366_eq : (2 : Nat) * 3 ^ (10 - 1) = 39366 := by decide
  have h118098_eq : (2 : Nat) * 3 ^ 10 = 118098 := by decide
  have hcongr118098 : ∀ (w a : Nat), w ≥ 10 -> a < 2 * 3 ^ (w - 1) ->
      markovShiftTrue w a % 118098 = markovShiftTrue 10 (a % 39366) % 118098 := by
    intro w a hw10 ha_lt
    have hr_lt : a % 39366 < 2 * 3 ^ (10 - 1) := by rw [h39366_eq]; exact Nat.mod_lt a (by decide)
    exact markovShiftTrue_contraction_mod_pow3 9 w 10 a (a % 39366)
      (by omega) (by decide) ha_lt hr_lt (by simp)
  have hlen118098 : survivingMod118098List.length = 39366 := by
    unfold survivingMod118098List
    have h := range_six_mul_surviving_len_w17 19683
    simpa using h
  have hinj39366 : ∀ x1 x2 : Fin 39366,
      markovShiftTrue 10 x1.val % 118098 = markovShiftTrue 10 x2.val % 118098 -> x1 = x2 := by
    intro x1 x2 heq
    have hx1 : x1.val < 2 * 3 ^ (10 - 1) := by rw [h39366_eq]; exact x1.isLt
    have hx2 : x2.val < 2 * 3 ^ (10 - 1) := by rw [h39366_eq]; exact x2.isLt
    have hm1_lt : markovShiftTrue 10 x1.val < 118098 := by
      rw [← h118098_eq]
      exact (canonicalSuffixShift_markov_bijection_and_mod6_lock.2.1 10 x1.val (by decide) hx1).1
    have hm2_lt : markovShiftTrue 10 x2.val < 118098 := by
      rw [← h118098_eq]
      exact (canonicalSuffixShift_markov_bijection_and_mod6_lock.2.1 10 x2.val (by decide) hx2).1
    rw [Nat.mod_eq_of_lt hm1_lt, Nat.mod_eq_of_lt hm2_lt] at heq
    exact Fin.ext (canonicalSuffixShift_markov_bijection_and_mod6_lock.2.2.1 10 x1.val x2.val
      (by decide) hx1 hx2 heq)
  have hmem39366 : ∀ x : Fin 39366, markovShiftTrue 10 x.val % 118098 ∈ survivingMod118098List := by
    intro x
    have hx : x.val < 2 * 3 ^ (10 - 1) := by rw [h39366_eq]; exact x.isLt
    rcases canonicalSuffixShift_markov_bijection_and_mod6_lock.2.1 10 x.val (by decide) hx with
      ⟨hlt, hm6⟩
    rw [h118098_eq] at hlt
    rw [Nat.mod_eq_of_lt hlt]
    exact (mem_survivingMod118098List_iff_w17 _).mpr ⟨hlt, hm6⟩
  have hsurj39366 : ∀ r ∈ survivingMod118098List,
      ∃ x : Fin 39366, markovShiftTrue 10 x.val % 118098 = r := by
    intro r hr
    rcases (mem_survivingMod118098List_iff_w17 r).mp hr with ⟨hr_lt, hr_m6⟩
    rcases canonicalSuffixShift_markov_bijection_and_mod6_lock.2.2.2.1 10 r (by decide)
      (by rw [h118098_eq]; exact hr_lt) hr_m6 with ⟨a, ha_lt, ha_eq⟩
    rw [h39366_eq] at ha_lt
    refine ⟨⟨a, ha_lt⟩, ?_⟩
    dsimp only
    rw [ha_eq, Nat.mod_eq_of_lt hr_lt]
  have hconf11 : ∀ u : List Bool, IsCoreParityWord u -> parityWeight u ≥ 11 ->
      canonicalSuffixShift u 1 % 118098 ∈ survivingMod118098List := by
    intro u hu hw11
    rcases list_eq_append_true_of_reverse_head u hu.2 with ⟨v, rfl⟩
    have hw_v : parityWeight v ≥ 10 := by
      rw [parityWeight_append] at hw11
      have h1 : parityWeight [true] = 1 := rfl
      rw [h1] at hw11; omega
    have hrec : canonicalSuffixShift (v ++ [true]) 1 =
        markovShiftTrue (parityWeight v) (canonicalSuffixShift v 1) :=
      (canonicalSuffixShift_append_markov_recurrence.2.2 v (by omega)).2.2.1
    have ha_lt := (canonicalSuffixShift_spec_unique v 1 (by omega) (by decide)).1
    rw [hrec, hcongr118098 (parityWeight v) (canonicalSuffixShift v 1) hw_v ha_lt]
    exact hmem39366 ⟨canonicalSuffixShift v 1 % 39366, Nat.mod_lt _ (by decide)⟩
  have hpref9_le9 : ∀ r : Fin 512, parityWeight (parityOfIter 9 r.val) ≤ 9 := by
    have hle_len : ∀ xs : List Bool, parityWeight xs ≤ xs.length := by
      intro xs; induction xs with
      | nil => exact Nat.le_refl 0
      | cons b tl ih =>
        cases b <;> (simp only [parityWeight, List.length_cons]; omega)
    intro r
    exact Nat.le_trans (hle_len _) (by rw [parityOfIter_length]; exact Nat.le_refl 9)
  have hesc10_cert :
      let u_esc10 : List Bool :=
        List.replicate 9 true ++ List.replicate 155 false ++ [true]
      u_esc10.length = 165 ∧
      parityWeight u_esc10 = 10 ∧
      IsFirstHitOnePair u_esc10 0 ∧
      exactBackwardQuotient 1 u_esc10 0 =
        6487840627110957342933758367292483113623774926335 ∧
      IsSurvivingMod373248Class (exactBackwardQuotient 1 u_esc10 0) ∧
      exactBackwardQuotient 1 u_esc10 0 % 512 = 511 ∧
      exactBackwardQuotient 1 u_esc10 0 % 1024 = 511 := by
    dsimp only
    let u_esc10 : List Bool := List.replicate 9 true ++ List.replicate 155 false ++ [true]
    have hsh13 : canonicalSuffixShift u_esc10 1 = 13 := by
      rcases canonicalSuffixShift_spec_unique u_esc10 1 (by decide) (by decide) with ⟨_, _, huniq⟩
      symm
      apply huniq 13 (by decide)
      decide
    have hfh_esc : IsFirstHitOnePair u_esc10 0 :=
      (first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.2 u_esc10 ⟨rfl, rfl⟩).mpr
        (by rw [hsh13]; decide)
    have hq_val : exactBackwardQuotient 1 u_esc10 0 =
        6487840627110957342933758367292483113623774926335 := by
      unfold exactBackwardQuotient
      dsimp only
      rw [hsh13]
      decide
    have hb_surv : isSurvivingMod373248Bool
        6487840627110957342933758367292483113623774926335 = true := by decide
    rw [hq_val]
    exact ⟨rfl, rfl, hfh_esc, rfl, isSurvivingMod373248Bool_imp_class _ hb_surv, by decide, by decide⟩
  have hlen11_top10 : ∀ (u : List Bool) (q : Nat),
      IsCoreParityWord u -> u.length ≥ 11 ->
      isWeightKSurvivingMod1024Bool 10 (exactBackwardQuotient 1 u q) = true ->
      parityWeight u ≥ 11 ∧ canonicalSuffixShift u 1 % 118098 ∈ survivingMod118098List := by
    intro u q hu hlen11 htop
    rcases list_eq_append_true_of_reverse_head u hu.2 with ⟨pre, rfl⟩
    have hpre_ge10 : pre.length ≥ 10 := by
      rw [List.length_append, List.length_singleton] at hlen11; omega
    let p10 := pre.take 10
    let fb := pre.drop 10
    have hp10_len : p10.length = 10 := take_len_of_ge_w17 10 pre hpre_ge10
    have hpre_sp : p10 ++ fb = pre := take_drop_split_eq_w17 10 pre
    have hu' : IsCoreParityWord (p10 ++ fb ++ [true]) := by rwa [hpre_sp]
    have hp10_eq : parityOfIter 10 (exactBackwardQuotient 1 (p10 ++ fb ++ [true]) q % 1024) = p10 :=
      len11_core_mod1024_prefix10_w17 p10 fb q hp10_len hu'
    rw [hpre_sp] at hp10_eq
    unfold isWeightKSurvivingMod1024Bool at htop
    simp only [Bool.and_eq_true, decide_eq_true_eq] at htop
    have htop2 := htop.2
    have hw_p10 : parityWeight p10 = 10 := by rwa [hp10_eq] at htop2
    have hw11 : parityWeight (pre ++ [true]) ≥ 11 := by
      rw [← hpre_sp, parityWeight_append, parityWeight_append]
      have h1 : parityWeight [true] = 1 := rfl
      rw [h1]; omega
    exact ⟨hw11, hconf11 (pre ++ [true]) hu hw11⟩
  refine ⟨⟨hcongr118098, hlen118098, hinj39366, hmem39366, hsurj39366⟩,
          ⟨hpref9_le9, len9_all27_surviving_escape_sound, hesc10_cert,
           by decide, by decide, by decide, by decide, by decide, by decide,
           hconf11, hlen11_top10⟩, ⟨?_, ?_⟩, ?_⟩
  · intro pref
    have hm39366 := first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.1 10 pref (by decide)
    change canonicalSuffixShift (pref ++ List.replicate 10 true) 1 % 39366 = 19683 at hm39366
    let A := canonicalSuffixShift (pref ++ List.replicate 10 true) 1 % 118098
    have hA_lt : A < 118098 := Nat.mod_lt _ (by decide)
    have hA_m39366 : A % 39366 = 19683 := by
      dsimp only [A]
      rw [Nat.mod_mod_of_dvd _ ⟨3, by decide⟩]
      exact hm39366
    have hdm := (Nat.div_add_mod A 39366).symm
    change A = 19683 ∨ A = 59049 ∨ A = 98415
    omega
  · intro pref
    have ha1 := first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.1 11 pref (by decide)
    let u12 : List Bool := [true, false] ++ List.replicate 10 true
    have ha2 := canonicalSuffixShift_mod18_and_pow3_memory_annihilation.2.1 10 pref u12 (by decide)
    have hu12_sh : canonicalSuffixShift u12 1 = 98415 := by
      rcases canonicalSuffixShift_spec_unique u12 1 (by decide) (by decide) with ⟨_, _, huniq⟩
      symm
      apply huniq 98415 (by decide)
      have hlen12 : u12.length = 12 := rfl
      have hwt11 : parityWeight u12 = 11 := rfl
      rw [Nat.mul_one, hlen12, hwt11, show (3 : Nat) ^ 11 = 177147 from rfl,
          show 12 + 98415 = 12 + (81 * 81) * 15 from rfl,
          Nat.pow_add 2 12 ((81 * 81) * 15),
          ← pow_pow_eq_mul_w5 2 (81 * 81) 15,
          ← pow_pow_eq_mul_w5 2 81 81,
          Nat.mul_mod,
          pow_mod_eq_pow_mod_w17 ((2 ^ 81) ^ 81) 177147 15,
          pow_mod_eq_pow_mod_w17 (2 ^ 81) 177147 81]
      decide
    have hv2 : canonicalSuffixShift u12 1 % 118098 = 98415 := by rw [hu12_sh]
    exact ⟨by simpa using ha1, by simpa [u12] using ha2.trans hv2⟩
  · intro tail w r0 hw11 hr0
    have hm118098 : (2 : Nat) * 3 ^ 10 = 118098 := by decide
    have hw_sub : w - 1 - 10 = w - 11 := by omega
    have heq := markovShift_mod18_bijection_and_multistep_fiber_equidistribution.2.2
      tail 10 w r0 (by omega) (by rw [hm118098]; exact hr0)
    dsimp only at heq ⊢
    rwa [hm118098, hw_sub] at heq


-- ----------------------------------------------------------------------------
-- Section 3B: Choice-Free 3-Adic Carry-Deficit Invariance & Intermediate `Mod 9`
--             Stall Barrier + Constructive `243x`-Compressed (`6377332 -> 26265`)
--             Steeper-Slope (`c = 6`, Beating `c = 8`) Exponential Dyadic-Window
--             Occupancy (`W17_H4`)
-- ----------------------------------------------------------------------------

/-- Minimum-weight (`w_0 = 6`) surviving `Mod 512` length-`9` prefix `parityOfIter 9 507`
    (`affineCarry = 1085`, saving `3^3 = 27x` over all-ones `w_0 = 9`). -/
def minWeight6Prefix507 : List Bool :=
  [true, true, false, true, true, false, true, true, false]

/--
  Theorem W17.4b (`ternary_carry_deficit_invariance_and_mod9_stall_barrier`,
  choice-free `zero custom axioms`):
  1. **Surviving `Mod 512` Minimum-Weight Floor (`w_0 ≥ 6`):**
     Every surviving `Mod 512` residue `r < 512` satisfies `parityWeight (parityOfIter 9 r) ≥ 6`,
     attained at `r = 507` (`parityOfIter 9 507 = minWeight6Prefix507`, `parityWeight = 6`).
  2. **Universal 1-Step Ternary-Carry Bottom-Deficit Invariance:**
     For every `k ≥ 0` 1-bit ternary-carry steps (`w = w_0 + 1 + k`, initial modulus exponent
     `w + d_top = w_0 + 1 + k + d_top`), `k` divisions by `3` leave bottom exponent
     `(w_0 + 1 + k + d_top) - k = w_0 + 1 + d_top` strictly invariant in `k`; hence from ANY
     surviving `Mod 512` prefix (`w_0 ≥ 6`), `1` bottom Hensel bit, and `Mod 9` top lift (`d_top ≥ 2`),
     the bottom 3-adic exponent satisfies `w_0 + 1 + d_top ≥ 9` (`3 ^ 9 = 19683`, Euler period
     `2 * 3 ^ 8 = 13122`).
  3. **Intermediate `Mod 9` Stall Obstruction:**
     Whenever `(R - 2 ^ e) % 9 = 0` with `2 ^ e ≤ R`, `R_nxt := (R - 2 ^ e) / 3` satisfies
     `R_nxt % 3 = 0`, so for EVERY next exponent `e_next : Nat`, `(R_nxt + 3 - 2 ^ e_next % 3) % 3 ≠ 0`
     (and if `2 ^ e_next ≤ R_nxt`, `(R_nxt - 2 ^ e_next) % 3 ≠ 0`), proving constructively why no
     intermediate 1-bit carry step can divide out `3 ^ 2` without stalling mod `3`!
-/
theorem ternary_carry_deficit_invariance_and_mod9_stall_barrier :
    ((∀ r : Fin 512, isSurvivingMod512Bool r.val = true ->
        parityWeight (parityOfIter 9 r.val) ≥ 6) ∧
     isSurvivingMod512Bool 507 = true ∧
     parityOfIter 9 507 = minWeight6Prefix507 ∧
     parityWeight minWeight6Prefix507 = 6) ∧
    (∀ (w_0 d_top k : Nat), w_0 ≥ 6 -> d_top ≥ 2 ->
      ((w_0 + 1 + k + d_top) - k = w_0 + 1 + d_top) ∧
      3 ^ (w_0 + 1 + d_top) ≥ 19683 ∧
      2 * 3 ^ (w_0 + d_top) ≥ 13122 ∧
      4 * 3 ^ (w_0 + d_top) ≥ 26244) ∧
    (∀ (R e : Nat), 2 ^ e ≤ R -> (R - 2 ^ e) % 9 = 0 ->
      let R_nxt := (R - 2 ^ e) / 3
      R_nxt % 3 = 0 ∧
      (∀ e_next : Nat, (R_nxt + 3 - 2 ^ e_next % 3) % 3 ≠ 0) ∧
      (∀ e_next : Nat, 2 ^ e_next ≤ R_nxt -> (R_nxt - 2 ^ e_next) % 3 ≠ 0)) := by
  have hmin6 : ∀ r : Fin 512, isSurvivingMod512Bool r.val = true ->
      parityWeight (parityOfIter 9 r.val) ≥ 6 := by
    have hgrid : ∀ (hi : Fin 8) (lo : Fin 64),
        let rv := 64 * hi.val + lo.val
        isSurvivingMod512Bool rv = true -> parityWeight (parityOfIter 9 rv) ≥ 6 := by
      decide
    intro r hr
    have hhi : r.val / 64 < 8 := by have := r.isLt; omega
    have hlo : r.val % 64 < 64 := Nat.mod_lt r.val (by decide)
    have hg := hgrid ⟨r.val / 64, hhi⟩ ⟨r.val % 64, hlo⟩
    dsimp only at hg
    rw [Nat.div_add_mod r.val 64] at hg
    exact hg hr
  refine ⟨⟨hmin6, by decide, by decide, rfl⟩, ?_, ?_⟩
  · intro w_0 d_top k hw6 hd2
    have h9 : 3 ^ 9 ≤ 3 ^ (w_0 + 1 + d_top) :=
      nat_pow_mono_exp_pos 3 9 (w_0 + 1 + d_top) (by decide) (by omega)
    have h8 : 3 ^ 8 ≤ 3 ^ (w_0 + d_top) :=
      nat_pow_mono_exp_pos 3 8 (w_0 + d_top) (by decide) (by omega)
    have v9 : (3 : Nat) ^ 9 = 19683 := by decide
    have v8 : (3 : Nat) ^ 8 = 6561 := by decide
    exact ⟨by omega, by omega, by omega, by omega⟩
  · intro R e hle hm9; dsimp only
    let D := R - 2 ^ e
    have hdm9 := (Nat.div_add_mod D 9).symm
    change D % 9 = 0 at hm9
    have hRnxt_3 : (D / 3) % 3 = 0 := by omega
    refine ⟨hRnxt_3, ?_, ?_⟩
    · intro e_next
      have hp_nz := pow2_mod3_nonzero_w5 e_next
      have hp_lt : 2 ^ e_next % 3 < 3 := Nat.mod_lt _ (by decide)
      omega
    · intro e_next hle_n
      have hp_nz := pow2_mod3_nonzero_w5 e_next
      have hp_lt : 2 ^ e_next % 3 < 3 := Nat.mod_lt _ (by decide)
      have hdm_r := (Nat.div_add_mod (D / 3) 3).symm
      have hdm_p := (Nat.div_add_mod (2 ^ e_next) 3).symm
      omega

private def candPairs27 : List (Nat × Nat) :=
  [(1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10),
   (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9),
   (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8),
   (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7),
   (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6),
   (6, 1), (6, 2), (6, 3), (6, 4), (6, 5),
   (7, 1), (7, 2), (7, 3), (7, 4),
   (8, 1), (8, 2), (8, 3),
   (9, 1), (9, 2),
   (10, 1)]

private def validPair27Bool (rem27 exp18 : Nat) (p : Nat × Nat) : Bool :=
  let e1 := (exp18 + 18 - p.1) % 18
  let diff1 := (rem27 + 27 - (2 ^ e1) % 27) % 27
  let r1_9 := (diff1 / 3) % 9
  let e2 := (e1 + 12 - p.2) % 6
  let diff2 := (r1_9 + 9 - (2 ^ e2) % 9) % 9
  (diff1 % 3 == 0) && (r1_9 % 3 != 0) && (diff2 == 3 || diff2 == 6)

private def listPairAtW17 : List (Nat × Nat) -> Nat -> (Nat × Nat)
  | [], _ => (2, 2)
  | p :: _, 0 => p
  | _ :: ps, k + 1 => listPairAtW17 ps k

/-- Exact 2-step `Mod 27` ternary carry macro-selector (`2^18 ≡ 1 (mod 27)`):
    Encodes `2` full binary mask bits (`twoBits % 4 ∈ {0, 1, 2, 3}`) in `s1 + s2 ≤ 11` positions
    (`s1 ≥ 1, s2 ≥ 1, 4 ≤ s1 + s2 ≤ 11`), achieving exponential slope `2 / 11 > 1 / 6 > 1 / 8`. -/
def chooseTwoStepTernaryCarry27 (rem27 exp18 twoBits : Nat) : Nat × Nat :=
  listPairAtW17 (candPairs27.filter (validPair27Bool rem27 exp18)) (twoBits % 4)

/-- Top-down `k`-macro-step (`2 * k` ternary carry steps) chain starting from `(e_cur, R_cur)` and `mask`. -/
def twoStepTernaryCarryChain : Nat -> Nat -> Nat -> Nat -> (Nat × Nat × List Nat)
  | 0, e_cur, R_cur, _ => (e_cur, R_cur, [])
  | k + 1, e_cur, R_cur, mask =>
    let p := chooseTwoStepTernaryCarry27 (R_cur % 27) (e_cur % 18) (mask % 4)
    let e1 := e_cur - p.1
    let R1 := (R_cur - 2 ^ e1) / 3
    let e2 := e1 - p.2
    let R2 := (R1 - 2 ^ e2) / 3
    let sub := twoStepTernaryCarryChain k e2 R2 (mask / 4)
    (sub.1, sub.2.1, sub.2.2 ++ [p.2 - 1, p.1 - 1])

/-- `243x`-compressed, steeper-slope (`c = 6`) linear minimum dyadic window scale
    `dyadicExpWindowMinM17 B = 26265 + 6 * B` (down from Wave 16's `6377332 + 8 * B`). -/
def dyadicExpWindowMinM17 (B : Nat) : Nat :=
  26265 + 6 * B

/-- Zero-run length list `(p_last - 9) :: (e_fin - (p_last + 1)) :: gaps` for `uWinExp17 B M mask`. -/
def uWinExp17Runs (B M mask : Nat) : List Nat :=
  let k2 := (B + 1) / 2
  let w := 2 * k2 + 8
  let b0 := binBitLength (3 ^ w)
  let delta2 := 2 + dyadicPolyShiftDelta (b0 + 2)
  let a := b0 + delta2
  let q3 := (2 ^ (a + 1) - 1) / 3
  let L := M - delta2
  let chain := twoStepTernaryCarryChain k2 (L - 1) (q3 * 2 ^ (L - 1)) mask
  let e_fin := chain.1
  let R_fin := chain.2.1
  let gaps := chain.2.2
  let A_last := R_fin - (3 * 1085 + 7 * 3 ^ 7)
  let t_base := dlog2ModPow3 9 (A_last % 3 ^ 9)
  let p_last := 13122 + t_base
  (p_last - 9) :: (e_fin - (p_last + 1)) :: gaps

/-- Constructive `243x`-compressed, steeper-slope (`c = 6`) surviving `Mod373248` first-hit `q = 0`
    family `uWinExp17 B M mask` inside `[2^M, 2^(M+1))` at linear length `L = M - delta2 ≤ M`. -/
def uWinExp17 (B M mask : Nat) : List Bool :=
  minWeight6Prefix507 ++ zeroRunsSuffix (uWinExp17Runs B M mask)

private def checkTwoStepPairSpecBool (r e : Nat) (p : Nat × Nat) : Bool :=
  decide (1 ≤ p.1) && decide (1 ≤ p.2) && decide (4 ≤ p.1 + p.2) &&
  decide (p.1 + p.2 ≤ 11) && validPair27Bool r e p

private def checkTwoStepREBool (r e : Nat) : Bool :=
  if decide (r % 3 = 0) then true
  else
    match chooseTwoStepTernaryCarry27 r e 0,
          chooseTwoStepTernaryCarry27 r e 1,
          chooseTwoStepTernaryCarry27 r e 2,
          chooseTwoStepTernaryCarry27 r e 3 with
    | (a0, b0), (a1, b1), (a2, b2), (a3, b3) =>
      checkTwoStepPairSpecBool r e (a0, b0) &&
      checkTwoStepPairSpecBool r e (a1, b1) &&
      checkTwoStepPairSpecBool r e (a2, b2) &&
      checkTwoStepPairSpecBool r e (a3, b3) &&
      decide ((a0, b0) ≠ (a1, b1)) &&
      decide ((a0, b0) ≠ (a2, b2)) &&
      decide ((a0, b0) ≠ (a3, b3)) &&
      decide ((a1, b1) ≠ (a2, b2)) &&
      decide ((a1, b1) ≠ (a3, b3)) &&
      decide ((a2, b2) ≠ (a3, b3))

private def checkTwoStepELoopBool (r : Nat) : Nat -> Bool
  | 0 => true
  | k + 1 => checkTwoStepREBool r k && checkTwoStepELoopBool r k

private def checkTwoStepRRangeBool : Nat -> Nat -> Bool
  | _, 0 => true
  | start, cnt + 1 => checkTwoStepELoopBool start 18 && checkTwoStepRRangeBool (start + 1) cnt

private theorem checkTwoStepRRangeBool_append (s : Nat) :
    ∀ (a b : Nat),
      checkTwoStepRRangeBool s a = true ->
      checkTwoStepRRangeBool (s + a) b = true ->
      checkTwoStepRRangeBool s (a + b) = true := by
  intro a
  induction a generalizing s with
  | zero =>
    intro b _ h2
    simpa only [Nat.add_zero, Nat.zero_add] using h2
  | succ a' ih =>
    intro b h1 h2
    rw [show a' + 1 + b = (a' + b) + 1 by omega]
    unfold checkTwoStepRRangeBool at h1 ⊢
    simp only [Bool.and_eq_true] at h1 ⊢
    refine ⟨h1.1, ih (s + 1) b h1.2 ?_⟩
    rwa [show s + 1 + a' = s + (a' + 1) by omega]

private theorem checkTwoStep_c0 : checkTwoStepRRangeBool 0 5 = true := by decide
private theorem checkTwoStep_c1 : checkTwoStepRRangeBool 5 5 = true := by decide
private theorem checkTwoStep_c2 : checkTwoStepRRangeBool 10 5 = true := by decide
private theorem checkTwoStep_c3 : checkTwoStepRRangeBool 15 5 = true := by decide
private theorem checkTwoStep_c4 : checkTwoStepRRangeBool 20 7 = true := by decide

private theorem checkTwoStepRRangeBool_get :
    ∀ (s cnt r : Nat), checkTwoStepRRangeBool s cnt = true -> s ≤ r -> r < s + cnt ->
      checkTwoStepELoopBool r 18 = true
  | _, 0, _, _, hs, hr => by omega
  | s, cnt + 1, r, h, hs, hr => by
    unfold checkTwoStepRRangeBool at h
    simp only [Bool.and_eq_true] at h
    by_cases heq : r = s
    · subst heq; exact h.1
    · exact checkTwoStepRRangeBool_get (s + 1) cnt r h.2 (by omega) (by omega)

private theorem checkTwoStepELoopBool_get (r : Nat) :
    ∀ (k e : Nat), checkTwoStepELoopBool r k = true -> e < k ->
      checkTwoStepREBool r e = true
  | 0, _, _, he => by omega
  | k + 1, e, h, he => by
    unfold checkTwoStepELoopBool at h
    simp only [Bool.and_eq_true] at h
    by_cases heq : e = k
    · subst heq; exact h.1
    · exact checkTwoStepELoopBool_get r k e h.2 (by omega)

private theorem checkTwoStepPairSpecBool_sound (r e : Nat) (p : Nat × Nat)
    (h : checkTwoStepPairSpecBool r e p = true) :
    1 ≤ p.1 ∧ 1 ≤ p.2 ∧ 4 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ 11 ∧ validPair27Bool r e p = true := by
  unfold checkTwoStepPairSpecBool at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

private theorem chooseTwoStepTernaryCarry27_fin_spec :
    ∀ (r : Fin 27), r.val % 3 ≠ 0 -> ∀ (e : Fin 18) (b : Fin 4),
      let p := chooseTwoStepTernaryCarry27 r.val e.val b.val
      1 ≤ p.1 ∧ 1 ≤ p.2 ∧ 4 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ 11 ∧
      validPair27Bool r.val e.val p = true ∧
      (∀ b1 b2 : Fin 4,
        chooseTwoStepTernaryCarry27 r.val e.val b1.val =
          chooseTwoStepTernaryCarry27 r.val e.val b2.val -> b1 = b2) := by
  have h01 := checkTwoStepRRangeBool_append 0 5 5 checkTwoStep_c0 checkTwoStep_c1
  have h02 := checkTwoStepRRangeBool_append 0 10 5 h01 checkTwoStep_c2
  have h03 := checkTwoStepRRangeBool_append 0 15 5 h02 checkTwoStep_c3
  have hall := checkTwoStepRRangeBool_append 0 20 7 h03 checkTwoStep_c4
  intro r hr3 e b
  have hel := checkTwoStepRRangeBool_get 0 27 r.val hall (Nat.zero_le _) r.isLt
  have hre := checkTwoStepELoopBool_get r.val 18 e.val hel e.isLt
  unfold checkTwoStepREBool at hre
  simp only [hr3, decide_false, Bool.false_eq_true, ite_false] at hre
  rcases hp0 : chooseTwoStepTernaryCarry27 r.val e.val 0 with ⟨a0, d0⟩
  rcases hp1 : chooseTwoStepTernaryCarry27 r.val e.val 1 with ⟨a1, d1⟩
  rcases hp2 : chooseTwoStepTernaryCarry27 r.val e.val 2 with ⟨a2, d2⟩
  rcases hp3 : chooseTwoStepTernaryCarry27 r.val e.val 3 with ⟨a3, d3⟩
  rw [hp0, hp1, hp2, hp3] at hre
  dsimp only at hre ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hre
  rcases hre with ⟨⟨⟨⟨⟨⟨⟨⟨⟨hs0, hs1⟩, hs2⟩, hs3⟩, hn01⟩, hn02⟩, hn03⟩, hn12⟩, hn13⟩, hn23⟩
  have hinj : ∀ b1 b2 : Fin 4,
      chooseTwoStepTernaryCarry27 r.val e.val b1.val =
        chooseTwoStepTernaryCarry27 r.val e.val b2.val -> b1 = b2 := by
    intro ⟨v1, hv1⟩ ⟨v2, hv2⟩ heq
    dsimp only at heq
    have hc1 : v1 = 0 ∨ v1 = 1 ∨ v1 = 2 ∨ v1 = 3 := by omega
    have hc2 : v2 = 0 ∨ v2 = 1 ∨ v2 = 2 ∨ v2 = 3 := by omega
    rcases hc1 with rfl | rfl | rfl | rfl <;> rcases hc2 with rfl | rfl | rfl | rfl
    · rfl
    · rw [hp0, hp1] at heq; exact False.elim (hn01 heq)
    · rw [hp0, hp2] at heq; exact False.elim (hn02 heq)
    · rw [hp0, hp3] at heq; exact False.elim (hn03 heq)
    · rw [hp1, hp0] at heq; exact False.elim (hn01 heq.symm)
    · rfl
    · rw [hp1, hp2] at heq; exact False.elim (hn12 heq)
    · rw [hp1, hp3] at heq; exact False.elim (hn13 heq)
    · rw [hp2, hp0] at heq; exact False.elim (hn02 heq.symm)
    · rw [hp2, hp1] at heq; exact False.elim (hn12 heq.symm)
    · rfl
    · rw [hp2, hp3] at heq; exact False.elim (hn23 heq)
    · rw [hp3, hp0] at heq; exact False.elim (hn03 heq.symm)
    · rw [hp3, hp1] at heq; exact False.elim (hn13 heq.symm)
    · rw [hp3, hp2] at heq; exact False.elim (hn23 heq.symm)
    · rfl
  rcases b with ⟨vb, hvb⟩
  dsimp only
  have hbc : vb = 0 ∨ vb = 1 ∨ vb = 2 ∨ vb = 3 := by omega
  rcases hbc with rfl | rfl | rfl | rfl
  · rw [hp0]; rcases checkTwoStepPairSpecBool_sound r.val e.val (a0, d0) hs0 with ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, h4, h5, hinj⟩
  · rw [hp1]; rcases checkTwoStepPairSpecBool_sound r.val e.val (a1, d1) hs1 with ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, h4, h5, hinj⟩
  · rw [hp2]; rcases checkTwoStepPairSpecBool_sound r.val e.val (a2, d2) hs2 with ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, h4, h5, hinj⟩
  · rw [hp3]; rcases checkTwoStepPairSpecBool_sound r.val e.val (a3, d3) hs3 with ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, h4, h5, hinj⟩

private theorem pow2_mod27_period18_w17 (n : Nat) :
    2 ^ n % 27 = 2 ^ (n % 18) % 27 := by
  have hp18 : ∀ q : Nat, 2 ^ (18 * q) % 27 = 1 := by
    intro q; induction q with
    | zero => rfl
    | succ q' ih => rw [Nat.mul_succ 18 q', Nat.pow_add 2 (18 * q') 18, Nat.mul_mod, ih]
  conv => lhs; rw [(Nat.div_add_mod n 18).symm]
  rw [Nat.pow_add 2 (18 * (n / 18)) (n % 18), Nat.mul_mod, hp18 (n / 18), Nat.one_mul, Nat.mod_mod]

private theorem pow2_mod9_period6_w17 (n : Nat) :
    2 ^ n % 9 = 2 ^ (n % 6) % 9 := by
  have hp6 : ∀ q : Nat, 2 ^ (6 * q) % 9 = 1 := by
    intro q; induction q with
    | zero => rfl
    | succ q' ih => rw [Nat.mul_succ 6 q', Nat.pow_add 2 (6 * q') 6, Nat.mul_mod, ih]
  conv => lhs; rw [(Nat.div_add_mod n 6).symm]
  rw [Nat.pow_add 2 (6 * (n / 6)) (n % 6), Nat.mul_mod, hp6 (n / 6), Nat.one_mul, Nat.mod_mod]

private theorem sub_mod_of_le_w17 (M R U : Nat) (hM : M ≥ 1) (hUR : U ≤ R) :
    (R - U) % M = (R % M + M - U % M) % M := by
  have hR := (Nat.div_add_mod R M).symm
  have hU := (Nat.div_add_mod U M).symm
  have hrm : R % M < M := Nat.mod_lt R hM
  have hum : U % M < M := Nat.mod_lt U hM
  by_cases hcmp : U % M ≤ R % M
  · have hsub : R - U = M * (R / M - U / M) + (R % M - U % M) := by
      have hq : U / M ≤ R / M := by
        by_cases hq : U / M ≤ R / M
        · exact hq
        · exfalso
          have hm := Nat.mul_le_mul_left M (by omega : R / M + 1 ≤ U / M)
          rw [Nat.mul_add, Nat.mul_one] at hm; omega
      have hq_mul : M * (U / M) ≤ M * (R / M) := Nat.mul_le_mul_left M hq
      rw [Nat.mul_sub_left_distrib]
      generalize M * (R / M) = QR, M * (U / M) = QU at hR hU hq_mul ⊢; omega
    have hadd : R % M + M - U % M = M * 1 + (R % M - U % M) := by omega
    rw [hsub, hadd, Nat.add_comm (M * _), Nat.add_mul_mod_self_left,
        Nat.add_comm (M * 1), Nat.add_mul_mod_self_left]
  · have hq : U / M + 1 ≤ R / M := by
      by_cases hq : U / M + 1 ≤ R / M
      · exact hq
      · exfalso
        have hm := Nat.mul_le_mul_left M (by omega : R / M ≤ U / M)
        omega
    have hsub : R - U = M * (R / M - (U / M + 1)) + (R % M + M - U % M) := by
      have hq_mul : M * (U / M) + M ≤ M * (R / M) := by
        simpa [Nat.mul_add, Nat.mul_one] using Nat.mul_le_mul_left M hq
      rw [Nat.mul_sub_left_distrib, Nat.mul_add, Nat.mul_one]
      generalize M * (R / M) = QR, M * (U / M) = QU at hR hU hq_mul ⊢; omega
    rw [hsub, Nat.add_comm (M * _), Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by omega : R % M + M - U % M < M)]

private theorem chooseTwoStepTernaryCarry27_nat_step_w17 (R e twoBits : Nat)
    (hR3 : R % 3 ≠ 0) (he18 : e ≥ 18)
    (hR_big : R ≥ 10 * 2 ^ e) :
    let p := chooseTwoStepTernaryCarry27 (R % 27) (e % 18) (twoBits % 4)
    let e1 := e - p.1
    let R1 := (R - 2 ^ e1) / 3
    let e2 := e1 - p.2
    let R2 := (R1 - 2 ^ e2) / 3
    1 ≤ p.1 ∧ 1 ≤ p.2 ∧ 4 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ 11 ∧
    3 * R1 + 2 ^ e1 = R ∧
    3 * R2 + 2 ^ e2 = R1 ∧
    R2 % 3 ≠ 0 ∧
    (∀ b1 b2 : Nat, b1 < 4 -> b2 < 4 ->
      chooseTwoStepTernaryCarry27 (R % 27) (e % 18) b1 =
        chooseTwoStepTernaryCarry27 (R % 27) (e % 18) b2 -> b1 = b2) := by
  dsimp only
  have hr27_lt : R % 27 < 27 := Nat.mod_lt R (by decide)
  have hr27_3 : (R % 27) % 3 ≠ 0 := by rw [Nat.mod_mod_of_dvd R ⟨9, by decide⟩]; exact hR3
  have he18_lt : e % 18 < 18 := Nat.mod_lt e (by decide)
  have hb4_lt : twoBits % 4 < 4 := Nat.mod_lt twoBits (by decide)
  rcases chooseTwoStepTernaryCarry27_fin_spec ⟨R % 27, hr27_lt⟩ hr27_3 ⟨e % 18, he18_lt⟩ ⟨twoBits % 4, hb4_lt⟩ with
    ⟨hs1_1, hs2_1, hsum4, hsum11, hval_b, hinj_fin⟩
  dsimp only at hs1_1 hs2_1 hsum4 hsum11 hval_b hinj_fin
  let p := chooseTwoStepTernaryCarry27 (R % 27) (e % 18) (twoBits % 4)
  change 1 ≤ p.1 at hs1_1; change 1 ≤ p.2 at hs2_1
  change 4 ≤ p.1 + p.2 at hsum4; change p.1 + p.2 ≤ 11 at hsum11
  let e1 := e - p.1
  let e2 := e1 - p.2
  have he1_le : 2 ^ e1 ≤ 2 ^ e := pow2_mono_nat (by dsimp [e1]; omega)
  have he2_le : 2 ^ e2 ≤ 2 ^ e := pow2_mono_nat (by dsimp [e2, e1]; omega)
  have hp1_le_R : 2 ^ e1 ≤ R := by omega
  unfold validPair27Bool at hval_b
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at hval_b
  rcases hval_b with ⟨⟨hdiff1_3, hr1_n3⟩, hdiff2_36⟩
  have he1_m18 : e1 % 18 = (e % 18 + 18 - p.1) % 18 := by
    have hdm := (Nat.div_add_mod e 18).symm; dsimp [e1]; omega
  have hdiff1_eq : (R - 2 ^ e1) % 27 = (R % 27 + 27 - (2 ^ (e1 % 18)) % 27) % 27 := by
    rw [sub_mod_of_le_w17 27 R (2 ^ e1) (by decide) hp1_le_R, pow2_mod27_period18_w17 e1]
  rw [he1_m18] at hdiff1_eq
  let diff1 := (R % 27 + 27 - 2 ^ ((e % 18 + 18 - p.1) % 18) % 27) % 27
  change (R - 2 ^ e1) % 27 = diff1 at hdiff1_eq
  change diff1 % 3 = 0 at hdiff1_3
  have hdiff1_lt : diff1 < 27 := Nat.mod_lt _ (by decide)
  have hdm27 := (Nat.div_add_mod (R - 2 ^ e1) 27).symm
  rw [hdiff1_eq] at hdm27
  let R1 := (R - 2 ^ e1) / 3
  have h3R1 : 3 * R1 + 2 ^ e1 = R := by
    dsimp [R1]
    generalize R - 2 ^ e1 = D1, 2 ^ e1 = U1 at hp1_le_R hdm27 ⊢
    omega
  have hR1_m9 : R1 % 9 = (diff1 / 3) % 9 := by
    dsimp [R1]
    generalize R - 2 ^ e1 = D1 at hdm27 ⊢
    omega
  have hp2_le_R1 : 2 ^ e2 ≤ R1 := by
    have h3 : 3 * 2 ^ e2 ≤ 3 * R1 := by
      calc 3 * 2 ^ e2 ≤ 3 * 2 ^ e := Nat.mul_le_mul_left 3 he2_le
        _ ≤ 9 * 2 ^ e := Nat.mul_le_mul_right _ (by decide)
        _ ≤ R - 2 ^ e1 := by omega
        _ = 3 * R1 := by omega
    omega
  have he2_m6 : e2 % 6 = ((e1 % 18) + 12 - p.2) % 6 := by
    have hdm18 := (Nat.div_add_mod e1 18).symm
    dsimp [e2]; omega
  rw [he1_m18] at he2_m6
  have hdiff2_eq : (R1 - 2 ^ e2) % 9 = ((diff1 / 3) % 9 + 9 - (2 ^ (e2 % 6)) % 9) % 9 := by
    rw [sub_mod_of_le_w17 9 R1 (2 ^ e2) (by decide) hp2_le_R1, hR1_m9, pow2_mod9_period6_w17 e2]
  rw [he2_m6] at hdiff2_eq
  let diff2 := ((diff1 / 3) % 9 + 9 - 2 ^ (((e % 18 + 18 - p.1) % 18 + 12 - p.2) % 6) % 9) % 9
  change (R1 - 2 ^ e2) % 9 = diff2 at hdiff2_eq
  change diff2 = 3 ∨ diff2 = 6 at hdiff2_36
  rw [← hdiff2_eq] at hdiff2_36
  have hdm9 := (Nat.div_add_mod (R1 - 2 ^ e2) 9).symm
  let R2 := (R1 - 2 ^ e2) / 3
  have h3R2 : 3 * R2 + 2 ^ e2 = R1 := by
    dsimp [R2]
    generalize R1 - 2 ^ e2 = D2, 2 ^ e2 = U2 at hp2_le_R1 hdm9 hdiff2_36 ⊢
    rcases hdiff2_36 with h3 | h6 <;> omega
  have hR2_n3 : R2 % 3 ≠ 0 := by
    dsimp [R2]
    generalize R1 - 2 ^ e2 = D2 at hdm9 hdiff2_36 ⊢
    rcases hdiff2_36 with h3 | h6 <;> omega
  refine ⟨hs1_1, hs2_1, hsum4, hsum11, h3R1, h3R2, hR2_n3, ?_⟩
  intro b1 b2 hb1 hb2 heq
  exact congrArg Fin.val (hinj_fin ⟨b1, hb1⟩ ⟨b2, hb2⟩ heq)

private theorem list_append_singleton_inj_w17 {α : Type} :
    ∀ (xs ys : List α) (a b : α), xs ++ [a] = ys ++ [b] -> xs = ys ∧ a = b
  | [], [], a, b, h => ⟨rfl, by simpa using h⟩
  | [], _ :: _, _, _, h => by exfalso; have hlen := congrArg List.length h; simp at hlen
  | _ :: _, [], _, _, h => by exfalso; have hlen := congrArg List.length h; simp at hlen
  | x :: xs, y :: ys, a, b, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    rcases list_append_singleton_inj_w17 xs ys a b h.2 with ⟨hxy, hab⟩
    exact ⟨by rw [h.1, hxy], hab⟩

private theorem replicate_false_cons_true_inj_w17 :
    ∀ (a b : Nat) (xs ys : List Bool),
      List.replicate a false ++ (true :: xs) = List.replicate b false ++ (true :: ys) ->
      a = b ∧ xs = ys
  | 0, 0, xs, ys, h => ⟨rfl, by simpa using h⟩
  | 0, _ + 1, _, _, h => by simp [List.replicate_succ] at h
  | _ + 1, 0, _, _, h => by simp [List.replicate_succ] at h
  | a + 1, b + 1, xs, ys, h => by
    simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
    rcases replicate_false_cons_true_inj_w17 a b xs ys h with ⟨hab, hxy⟩
    exact ⟨congrArg Nat.succ hab, hxy⟩

private theorem zeroRunsSuffix_append_and_inj_w17 :
    (∀ xs ys : List Nat, zeroRunsSuffix (xs ++ ys) = zeroRunsSuffix xs ++ zeroRunsSuffix ys) ∧
    (∀ xs ys : List Nat, zeroRunsSuffix xs = zeroRunsSuffix ys -> xs = ys) := by
  have happ : ∀ xs ys : List Nat, zeroRunsSuffix (xs ++ ys) = zeroRunsSuffix xs ++ zeroRunsSuffix ys := by
    intro xs; induction xs with
    | nil => intro _; rfl
    | cons k tl ih => intro ys; simp only [List.cons_append, zeroRunsSuffix, ih ys, List.append_assoc]
  have hinj : ∀ xs ys : List Nat, zeroRunsSuffix xs = zeroRunsSuffix ys -> xs = ys := by
    intro xs; induction xs with
    | nil =>
      intro ys h; cases ys with
      | nil => rfl
      | cons _ _ => exfalso; have hlen := congrArg List.length h; simp [zeroRunsSuffix] at hlen
    | cons k1 tl1 ih =>
      intro ys h; cases ys with
      | nil => exfalso; have hlen := congrArg List.length h; simp [zeroRunsSuffix] at hlen
      | cons k2 tl2 =>
        simp only [zeroRunsSuffix] at h
        rcases replicate_false_cons_true_inj_w17 k1 k2 _ _ h with ⟨hk, htl⟩
        rw [hk, ih tl2 htl]
  exact ⟨happ, hinj⟩

private theorem zeroRunsSuffix_nonempty_eq_mid_true_w17 :
    ∀ (k : Nat) (ks : List Nat), ∃ mid : List Bool, zeroRunsSuffix (k :: ks) = mid ++ [true]
  | k, [] => ⟨List.replicate k false, by simp [zeroRunsSuffix]⟩
  | k, k2 :: tl => by
    rcases zeroRunsSuffix_nonempty_eq_mid_true_w17 k2 tl with ⟨mid_tl, htl⟩
    refine ⟨List.replicate k false ++ [true] ++ mid_tl, ?_⟩
    simp only [zeroRunsSuffix] at htl ⊢
    rw [htl]; simp [List.append_assoc]

private theorem twoStepTernaryCarryChain_spec_and_inj_w17 :
    ∀ (k e_cur R_cur L1 : Nat),
      e_cur ≤ L1 ->
      e_cur ≥ 11 * k + 18 ->
      R_cur % 3 ≠ 0 ->
      R_cur ≥ (2 * 3 ^ (2 * k + 8) - 1) * 2 ^ L1 ->
      (∀ mask : Nat,
        let ch := twoStepTernaryCarryChain k e_cur R_cur mask
        let e_fin := ch.1
        let R_fin := ch.2.1
        let gaps := ch.2.2
        e_cur - 11 * k ≤ e_fin ∧ e_fin ≤ e_cur ∧
        gaps.length = 2 * k ∧
        R_fin % 3 ≠ 0 ∧
        R_fin ≥ (2 * 3 ^ 8 - 1) * 2 ^ L1 ∧
        (∀ (acc : List Bool) (Q1 : Nat),
          acc.length = e_fin + 1 ->
          affineCarry acc < 6 * 2 ^ e_fin ->
          3 * R_fin + 2 ^ e_fin = 3 * Q1 + affineCarry acc ->
          let w_out := acc ++ zeroRunsSuffix gaps
          w_out.length = e_cur + 1 ∧
          parityWeight w_out = parityWeight acc + 2 * k ∧
          affineCarry w_out < 6 * 2 ^ e_cur ∧
          3 * R_cur + 2 ^ e_cur = 3 ^ (2 * k + 1) * Q1 + affineCarry w_out)) ∧
      (∀ m1 m2 : Nat, m1 < 4 ^ k -> m2 < 4 ^ k ->
        (twoStepTernaryCarryChain k e_cur R_cur m1).2.2 =
          (twoStepTernaryCarryChain k e_cur R_cur m2).2.2 ->
        m1 = m2) := by
  intro k; induction k with
  | zero =>
    intro e_cur R_cur L1 _ _ hR3 hR_lo
    refine ⟨?_, ?_⟩
    · intro mask; dsimp only [twoStepTernaryCarryChain]
      refine ⟨by omega, Nat.le_refl _, rfl, hR3, by simpa using hR_lo, ?_⟩
      intro acc Q1 hlen hcar heq
      rw [zeroRunsSuffix, List.append_nil, Nat.pow_one]
      exact ⟨hlen, by omega, hcar, heq⟩
    · intro m1 m2 h1 h2 _; rw [Nat.pow_zero] at h1 h2; omega
  | succ k' ih =>
    intro e_cur R_cur L1 he_L1 he_11k hR3 hR_lo
    have hR_big : R_cur ≥ 10 * 2 ^ e_cur := by
      have hp8 : (2 : Nat) * 3 ^ (2 * (k' + 1) + 8) - 1 ≥ 10 := by
        have h := nat_pow_mono_exp_pos 3 8 (2 * (k' + 1) + 8) (by decide) (by omega)
        have v8 : (3 : Nat) ^ 8 = 6561 := by decide
        omega
      have he_pow : 2 ^ e_cur ≤ 2 ^ L1 := pow2_mono_nat he_L1
      calc 10 * 2 ^ e_cur ≤ 10 * 2 ^ L1 := Nat.mul_le_mul_left 10 he_pow
        _ ≤ (2 * 3 ^ (2 * (k' + 1) + 8) - 1) * 2 ^ L1 := Nat.mul_le_mul_right _ hp8
        _ ≤ R_cur := hR_lo
    have hR2_lo_of : ∀ (e1 e2 R1 R2 : Nat),
        e1 ≤ L1 -> e2 ≤ L1 ->
        3 * R1 + 2 ^ e1 = R_cur -> 3 * R2 + 2 ^ e2 = R1 ->
        R2 ≥ (2 * 3 ^ (2 * k' + 8) - 1) * 2 ^ L1 := by
      intro e1 e2 R1 R2 he1_L1 he2_L1 h3R1 h3R2
      let P3 := 3 ^ (2 * k' + 8)
      have hP3_pos : P3 ≥ 1 := pow3_pos_nat (2 * k' + 8)
      have hp_sp : 3 ^ (2 * (k' + 1) + 8) = 9 * P3 := by
        dsimp [P3]; rw [show 2 * (k' + 1) + 8 = (2 * k' + 8) + 2 by omega, Nat.pow_add 3 _ 2]
        change _ = 9 * _; ac_rfl
      have hR_sp : R_cur ≥ (18 * P3 - 1) * 2 ^ L1 := by
        rw [hp_sp, show 2 * (9 * P3) = 18 * P3 by omega] at hR_lo; exact hR_lo
      have h2e1_le : 2 ^ e1 ≤ 2 ^ L1 := pow2_mono_nat he1_L1
      have h2e2_le : 2 ^ e2 ≤ 2 ^ L1 := pow2_mono_nat he2_L1
      let B1 := (6 * P3 - 1) * 2 ^ L1
      have h3B1 : 3 * B1 + 2 ^ L1 ≤ 3 * R1 + 2 ^ L1 := by
        calc 3 * B1 + 2 ^ L1
            = (3 * (6 * P3 - 1) + 1) * 2 ^ L1 := by dsimp [B1]; rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
          _ ≤ (18 * P3 - 1) * 2 ^ L1 := Nat.mul_le_mul_right _ (by omega)
          _ ≤ R_cur := hR_sp
          _ = 3 * R1 + 2 ^ e1 := h3R1.symm
          _ ≤ 3 * R1 + 2 ^ L1 := Nat.add_le_add_left h2e1_le _
      have hR1_ge : R1 ≥ B1 := by omega
      let B2 := (2 * P3 - 1) * 2 ^ L1
      have h3B2 : 3 * B2 + 2 ^ L1 ≤ 3 * R2 + 2 ^ L1 := by
        calc 3 * B2 + 2 ^ L1
            = (3 * (2 * P3 - 1) + 1) * 2 ^ L1 := by dsimp [B2]; rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
          _ ≤ B1 := by dsimp [B1]; exact Nat.mul_le_mul_right _ (by omega)
          _ ≤ R1 := hR1_ge
          _ = 3 * R2 + 2 ^ e2 := h3R2.symm
          _ ≤ 3 * R2 + 2 ^ L1 := Nat.add_le_add_left h2e2_le _
      change B2 ≤ R2; omega
    refine ⟨?_, ?_⟩
    · intro mask
      rcases chooseTwoStepTernaryCarry27_nat_step_w17 R_cur e_cur mask hR3 (by omega) hR_big with
        ⟨hs1_1, hs2_1, hsum4, hsum11, h3R1, h3R2, hR2_n3, _⟩
      let p := chooseTwoStepTernaryCarry27 (R_cur % 27) (e_cur % 18) (mask % 4)
      change 1 ≤ p.1 at hs1_1; change 1 ≤ p.2 at hs2_1
      change 4 ≤ p.1 + p.2 at hsum4; change p.1 + p.2 ≤ 11 at hsum11
      let e1 := e_cur - p.1
      let R1 := (R_cur - 2 ^ e1) / 3
      let e2 := e1 - p.2
      let R2 := (R1 - 2 ^ e2) / 3
      change 3 * R1 + 2 ^ e1 = R_cur at h3R1
      change 3 * R2 + 2 ^ e2 = R1 at h3R2
      change R2 % 3 ≠ 0 at hR2_n3
      have hR2_lo := hR2_lo_of e1 e2 R1 R2 (by dsimp [e1]; omega) (by dsimp [e2, e1]; omega) h3R1 h3R2
      rcases (ih e2 R2 L1 (by dsimp [e2, e1]; omega) (by dsimp [e2, e1]; omega) hR2_n3 hR2_lo).1 (mask / 4) with
        ⟨he_lo, he_hi, hlen_sub, hRfin_3, hRfin_lo, hunwind_sub⟩
      let ch_sub := twoStepTernaryCarryChain k' e2 R2 (mask / 4)
      change e2 - 11 * k' ≤ ch_sub.1 at he_lo
      change ch_sub.1 ≤ e2 at he_hi
      change ch_sub.2.2.length = 2 * k' at hlen_sub
      simp only [twoStepTernaryCarryChain]
      change e_cur - 11 * (k' + 1) ≤ ch_sub.1 ∧ ch_sub.1 ≤ e_cur ∧
        (ch_sub.2.2 ++ [p.2 - 1, p.1 - 1]).length = 2 * (k' + 1) ∧
        ch_sub.2.1 % 3 ≠ 0 ∧ ch_sub.2.1 ≥ (2 * 3 ^ 8 - 1) * 2 ^ L1 ∧ _
      refine ⟨by dsimp [e2, e1] at he_lo; omega,
              by dsimp [e2, e1] at he_hi; omega,
              by rw [List.length_append, hlen_sub]; simp; omega,
              hRfin_3, hRfin_lo, ?_⟩
      intro acc Q1 hacc_len hacc_car hacc_eq
      rcases hunwind_sub acc Q1 hacc_len hacc_car hacc_eq with
        ⟨hw2_len, hw2_wt, hw2_car, hw2_eq⟩
      let w2 := acc ++ zeroRunsSuffix ch_sub.2.2
      change w2.length = e2 + 1 at hw2_len
      change parityWeight w2 = parityWeight acc + 2 * k' at hw2_wt
      change affineCarry w2 < 6 * 2 ^ e2 at hw2_car
      change 3 * R2 + 2 ^ e2 = 3 ^ (2 * k' + 1) * Q1 + affineCarry w2 at hw2_eq
      rw [h3R2] at hw2_eq
      let w1 := (w2 ++ List.replicate (p.2 - 1) false) ++ [true]
      let w0 := (w1 ++ List.replicate (p.1 - 1) false) ++ [true]
      have hw_out_eq : acc ++ zeroRunsSuffix (ch_sub.2.2 ++ [p.2 - 1, p.1 - 1]) = w0 := by
        rw [zeroRunsSuffix_append_and_inj_w17.1 ch_sub.2.2 [p.2 - 1, p.1 - 1]]
        dsimp only [zeroRunsSuffix, w0, w1, w2]
        simp [List.append_assoc]
      rw [hw_out_eq]
      rcases affineCarry_append_replicate_false w2 (p.2 - 1) with ⟨hwt_z2, hcar_z2⟩
      have hlen_z2 : (w2 ++ List.replicate (p.2 - 1) false).length = e1 := by
        rw [List.length_append, hw2_len, List.length_replicate]; dsimp [e2, e1]; omega
      have hlen_w1 : w1.length = e1 + 1 := by
        dsimp [w1]; rw [List.length_append, hlen_z2, List.length_singleton]
      have hwt_w1 : parityWeight w1 = parityWeight w2 + 1 := by
        dsimp [w1]; rw [parityWeight_append, hwt_z2]; rfl
      have hcar_w1 : affineCarry w1 = 3 * affineCarry w2 + 2 ^ e1 := by
        dsimp [w1]; rw [affineCarry_append, hcar_z2, hlen_z2]
        have hc1 : affineCarry [true] = 1 := rfl
        have hw1 : parityWeight [true] = 1 := rfl
        rw [hc1, hw1]; omega
      rcases affineCarry_append_replicate_false w1 (p.1 - 1) with ⟨hwt_z1, hcar_z1⟩
      have hlen_z1 : (w1 ++ List.replicate (p.1 - 1) false).length = e_cur := by
        rw [List.length_append, hlen_w1, List.length_replicate]; dsimp [e1]; omega
      have hlen_w0 : w0.length = e_cur + 1 := by
        dsimp [w0]; rw [List.length_append, hlen_z1, List.length_singleton]
      have hwt_w0 : parityWeight w0 = parityWeight acc + 2 * (k' + 1) := by
        dsimp [w0]; rw [parityWeight_append, hwt_z1, hwt_w1, hw2_wt]
        have h1 : parityWeight [true] = 1 := rfl
        rw [h1]; omega
      have hcar_w0 : affineCarry w0 = 3 * affineCarry w1 + 2 ^ e_cur := by
        dsimp [w0]; rw [affineCarry_append, hcar_z1, hlen_z1]
        have hc1 : affineCarry [true] = 1 := rfl
        have hw1 : parityWeight [true] = 1 := rfl
        rw [hc1, hw1]; omega
      -- Crucial steeper-slope `94 * Z - 9 < 96 * Z` invariant (`affineCarry < 6 * 2 ^ e_cur`):
      have hcar_w0_lt : affineCarry w0 < 6 * 2 ^ e_cur := by
        rw [hcar_w0, hcar_w1]
        have he2_le4 : 2 ^ e2 ≤ 2 ^ (e_cur - 4) := pow2_mono_nat (by dsimp [e2, e1]; omega)
        have he1_le1 : 2 ^ e1 ≤ 8 * 2 ^ (e_cur - 4) := by
          have h := pow2_mono_nat (by dsimp [e1]; omega : e1 ≤ 3 + (e_cur - 4))
          rwa [Nat.pow_add 2 3 (e_cur - 4)] at h
        have hp_ecur : 2 ^ e_cur = 16 * 2 ^ (e_cur - 4) := by
          conv => lhs; rw [show e_cur = 4 + (e_cur - 4) by omega, Nat.pow_add]
        have hZ_pos : 2 ^ (e_cur - 4) ≥ 1 := pow2_pos_nat _
        have hc2_le : affineCarry w2 < 6 * 2 ^ (e_cur - 4) :=
          Nat.lt_of_lt_of_le hw2_car (Nat.mul_le_mul_left 6 he2_le4)
        rw [hp_ecur]
        generalize 2 ^ (e_cur - 4) = Z at hZ_pos hc2_le he1_le1 ⊢
        omega
      have hkey_w0 : 3 * R_cur + 2 ^ e_cur = 3 ^ (2 * (k' + 1) + 1) * Q1 + affineCarry w0 := by
        have hw1_eq : 3 * R1 + 2 ^ e1 = 3 ^ (2 * k' + 2) * Q1 + affineCarry w1 := by
          rw [hcar_w1, hw2_eq, Nat.mul_add 3 (3 ^ (2 * k' + 1) * Q1) (affineCarry w2),
              ← Nat.mul_assoc 3 (3 ^ (2 * k' + 1)) Q1,
              show 3 * 3 ^ (2 * k' + 1) = 3 ^ (2 * k' + 2) by
                rw [Nat.pow_succ 3 (2 * k' + 1), Nat.mul_comm],
              Nat.add_assoc]
        rw [h3R1] at hw1_eq
        rw [hcar_w0, hw1_eq, Nat.mul_add 3 (3 ^ (2 * k' + 2) * Q1) (affineCarry w1),
            ← Nat.mul_assoc 3 (3 ^ (2 * k' + 2)) Q1,
            show 3 * 3 ^ (2 * k' + 2) = 3 ^ (2 * (k' + 1) + 1) by
              rw [show 2 * (k' + 1) + 1 = (2 * k' + 2) + 1 by omega,
                  Nat.pow_succ 3 (2 * k' + 2), Nat.mul_comm 3 (3 ^ (2 * k' + 2))],
            Nat.add_assoc]
      exact ⟨hlen_w0, hwt_w0, hcar_w0_lt, hkey_w0⟩
    · intro m1 m2 hm1 hm2 hgaps_eq
      rcases chooseTwoStepTernaryCarry27_nat_step_w17 R_cur e_cur m1 hR3 (by omega) hR_big with
        ⟨hp1_s1, hp1_s2, _, hp1_sum11, h3R1, h3R2, hR2_n3, hbit_inj⟩
      rcases chooseTwoStepTernaryCarry27_nat_step_w17 R_cur e_cur m2 hR3 (by omega) hR_big with
        ⟨hp2_s1, hp2_s2, _, _, _, _, _, _⟩
      let p1 := chooseTwoStepTernaryCarry27 (R_cur % 27) (e_cur % 18) (m1 % 4)
      let p2 := chooseTwoStepTernaryCarry27 (R_cur % 27) (e_cur % 18) (m2 % 4)
      change 1 ≤ p1.1 at hp1_s1; change 1 ≤ p1.2 at hp1_s2; change p1.1 + p1.2 ≤ 11 at hp1_sum11
      change 1 ≤ p2.1 at hp2_s1; change 1 ≤ p2.2 at hp2_s2
      simp only [twoStepTernaryCarryChain] at hgaps_eq
      have htwo_eq : ∀ (xs ys : List Nat) (a1 b1 a2 b2 : Nat),
          xs ++ [a1, b1] = ys ++ [a2, b2] -> xs = ys ∧ a1 = a2 ∧ b1 = b2 := by
        intro xs ys a1 b1 a2 b2 h
        have h1 : (xs ++ [a1]) ++ [b1] = (ys ++ [a2]) ++ [b2] := by simp [List.append_assoc, h]
        rcases list_append_singleton_inj_w17 _ _ _ _ h1 with ⟨h_pre, hb⟩
        rcases list_append_singleton_inj_w17 _ _ _ _ h_pre with ⟨hxy, ha⟩
        exact ⟨hxy, ha, hb⟩
      rcases htwo_eq _ _ _ _ _ _ hgaps_eq with ⟨hsub_eq, hs2_sub, hs1_sub⟩
      change p1.2 - 1 = p2.2 - 1 at hs2_sub
      change p1.1 - 1 = p2.1 - 1 at hs1_sub
      have hp_eq : p1 = p2 := by
        cases hp1_pair : p1 with
        | mk a1 b1 =>
          cases hp2_pair : p2 with
          | mk a2 b2 =>
            rw [hp1_pair] at hp1_s1 hp1_s2 hs1_sub hs2_sub
            rw [hp2_pair] at hp2_s1 hp2_s2 hs1_sub hs2_sub
            dsimp at hp1_s1 hp1_s2 hp2_s1 hp2_s2 hs1_sub hs2_sub
            congr <;> omega
      have hmod4_eq : m1 % 4 = m2 % 4 :=
        hbit_inj (m1 % 4) (m2 % 4) (Nat.mod_lt m1 (by decide)) (Nat.mod_lt m2 (by decide)) hp_eq
      let e1 := e_cur - p1.1
      let R1 := (R_cur - 2 ^ e1) / 3
      let e2 := e1 - p1.2
      let R2 := (R1 - 2 ^ e2) / 3
      change 3 * R1 + 2 ^ e1 = R_cur at h3R1
      change 3 * R2 + 2 ^ e2 = R1 at h3R2
      change R2 % 3 ≠ 0 at hR2_n3
      have hsub_same : (twoStepTernaryCarryChain k' e2 R2 (m1 / 4)).2.2 =
          (twoStepTernaryCarryChain k' e2 R2 (m2 / 4)).2.2 := by
        dsimp only [p1, p2] at hp_eq
        simpa [e2, R2, e1, R1, p1, hp_eq] using hsub_eq
      have hR2_lo := hR2_lo_of e1 e2 R1 R2 (by dsimp [e1]; omega) (by dsimp [e2, e1]; omega) h3R1 h3R2
      have hdiv_lt : ∀ m : Nat, m < 4 ^ (k' + 1) -> m / 4 < 4 ^ k' := by
        intro m hm; rw [Nat.pow_succ] at hm; omega
      have hdiv_eq : m1 / 4 = m2 / 4 :=
        (ih e2 R2 L1 (by dsimp [e2, e1]; omega) (by dsimp [e2, e1]; omega) hR2_n3 hR2_lo).2
          (m1 / 4) (m2 / 4) (hdiv_lt m1 hm1) (hdiv_lt m2 hm2) hsub_same
      have hdm1 := (Nat.div_add_mod m1 4).symm
      have hdm2 := (Nat.div_add_mod m2 4).symm
      rw [hdiv_eq, hmod4_eq] at hdm1
      exact hdm1.trans hdm2.symm

private theorem binBitLength_pow2_sandwich_w17 :
    ∀ (fuel n : Nat), n ≥ 1 -> n ≤ fuel ->
      binBitLength n ≥ 1 ∧ 2 ^ (binBitLength n - 1) ≤ n ∧ n < 2 ^ binBitLength n
  | 0, _, hn, hle => by omega
  | fuel + 1, n, hn, hle => by
    by_cases hn1 : n = 1
    · subst hn1; decide
    · let k := n / 2
      have hk_pos : k ≥ 1 := by dsimp [k]; omega
      have hbl_n : binBitLength n = 1 + binBitLength k := binBitLength_step_pos n hn
      rcases binBitLength_pow2_sandwich_w17 fuel k hk_pos (by dsimp [k]; omega) with
        ⟨hbl_k, hk_lo, hk_hi⟩
      rw [hbl_n]
      have hsub : 1 + binBitLength k - 1 = (binBitLength k - 1) + 1 := by omega
      refine ⟨by omega, ?_, ?_⟩
      · rw [hsub, Nat.pow_succ]
        have hm := Nat.mul_le_mul_right 2 hk_lo; dsimp [k] at hm; omega
      · rw [Nat.add_comm 1 (binBitLength k), Nat.pow_succ]
        have hm := Nat.mul_lt_mul_of_pos_right hk_hi (by decide : 0 < 2); dsimp [k] at hm; omega

private theorem pow3_bitlength_strict_bounds_w17 (w : Nat) (hw : w ≥ 10) :
    let b0 := binBitLength (3 ^ w)
    b0 ≥ 16 ∧ b0 ≤ 2 * w ∧ 3 ^ w + 1 ≤ 2 ^ b0 ∧ 2 ^ b0 < 2 * 3 ^ w := by
  dsimp only
  let b0 := binBitLength (3 ^ w)
  have hp3_ge10 : 3 ^ w ≥ 59049 := by
    simpa using nat_pow_mono_exp_pos 3 10 w (by decide) hw
  have hb0_ge16 : b0 ≥ 16 := by
    have h15 : (2 : Nat) ^ 15 ≤ 3 ^ w := by omega
    have hm := binBitLength_mono (2 ^ 15) (3 ^ w) h15
    rwa [(binBitLength_pow2_and_pred 15).1] at hm
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
    rwa [(binBitLength_pow2_and_pred (2 * w - 1)).2, show (2 * w - 1) + 1 = 2 * w by omega] at hm
  rcases binBitLength_pow2_sandwich_w17 (3 ^ w) (3 ^ w) (by omega) (Nat.le_refl _) with
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
  exact ⟨hb0_ge16, hb0_le2w, Nat.succ_le_of_lt hhi, h2b0_lt⟩

private theorem dyadicPolyShiftDelta2_spec_w17 (b0 : Nat) :
    let delta2 := 2 + dyadicPolyShiftDelta (b0 + 2)
    let a := b0 + delta2
    let q3 := (2 ^ (a + 1) - 1) / 3
    2 ≤ delta2 ∧ delta2 ≤ 5 ∧ 3 * q3 + 1 = 2 ^ (a + 1) ∧ q3 % 3 ≠ 0 ∧ q3 ≥ 1 := by
  dsimp only
  let d0 := dyadicPolyShiftDelta (b0 + 2)
  have hd_mod6 : d0 ≤ 3 ∧ (((b0 + 2) + 1 + d0) % 6 = 2 ∨ ((b0 + 2) + 1 + d0) % 6 = 4) := by
    dsimp [d0]; unfold dyadicPolyShiftDelta
    have hr6 : (b0 + 2 + 1) % 6 < 6 := Nat.mod_lt (b0 + 2 + 1) (by decide)
    have hdm := (Nat.div_add_mod (b0 + 2 + 1) 6).symm
    rcases (by omega :
      (b0 + 2 + 1) % 6 = 0 ∨ (b0 + 2 + 1) % 6 = 1 ∨ (b0 + 2 + 1) % 6 = 2 ∨
      (b0 + 2 + 1) % 6 = 3 ∨ (b0 + 2 + 1) % 6 = 4 ∨ (b0 + 2 + 1) % 6 = 5) with
      h | h | h | h | h | h <;> (simp [h]; omega)
  let E := b0 + (2 + d0) + 1
  have hE_eq : (b0 + 2) + 1 + d0 = E := by dsimp [E]; omega
  rw [hE_eq] at hd_mod6
  have hpE_m9 : 2 ^ E % 9 = 4 ∨ 2 ^ E % 9 = 7 := by
    rw [pow2_mod9_period6_w17 E]
    rcases hd_mod6.2 with h2 | h4
    · left; rw [h2]
    · right; rw [h4]
  have hpE_ge4 : 2 ^ E ≥ 4 := by
    have hE2 : E ≥ 2 := by dsimp [E]; omega
    simpa using pow2_mono_nat hE2
  have hdm9 := (Nat.div_add_mod (2 ^ E) 9).symm
  change 2 ≤ 2 + d0 ∧ 2 + d0 ≤ 5 ∧ 3 * ((2 ^ E - 1) / 3) + 1 = 2 ^ E ∧
    ((2 ^ E - 1) / 3) % 3 ≠ 0 ∧ (2 ^ E - 1) / 3 ≥ 1
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · rcases hpE_m9 with h4 | h7 <;> omega
  · rcases hpE_m9 with h4 | h7 <;> omega
  · omega

private theorem pow2_euler_pow3_mod_one_w17 :
    ∀ n : Nat, 3 ^ (n + 1) ∣ (2 ^ (2 * 3 ^ n) - 1)
  | 0 => ⟨1, by decide⟩
  | n + 1 => by
    rcases pow2_euler_pow3_mod_one_w17 n with ⟨q, hq⟩
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
      rw [hM_sp]; exact hc (3 ^ n) q
    rw [hexp]; omega

private theorem pow2_add_period_mod_pow3_w17 (n t : Nat) :
    2 ^ (t + 2 * 3 ^ n) % 3 ^ (n + 1) = 2 ^ t % 3 ^ (n + 1) := by
  let P := 2 * 3 ^ n
  let M := 3 ^ (n + 1)
  have hM_ge3 : M ≥ 3 := by dsimp [M]; rw [Nat.pow_succ]; have := pow3_pos_nat n; omega
  have hp_one : 2 ^ P % M = 1 := by
    rcases pow2_euler_pow3_mod_one_w17 n with ⟨q, hq⟩
    have hp_pos := pow2_pos_nat (2 * 3 ^ n)
    have heq : 2 ^ P = 1 + M * q := by dsimp [P, M] at hq ⊢; omega
    rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  rw [Nat.pow_add 2 t P, Nat.mul_mod, hp_one, Nat.mul_one, Nat.mod_mod]

private theorem surviving729_all_mod9_eq7_w17 :
    ∀ q : Fin 81, isSurvivingMod729Bool (9 * q.val + 7) = true := by
  decide

private theorem isSurvivingMod373248_of_507_and_mod9_eq7_w17 (y : Nat)
    (h512 : y % 512 = 507) (h9 : y % 9 = 7) :
    isSurvivingMod373248Bool y = true ∧ IsSurvivingMod373248Class y := by
  let r729 := y % 729
  have hr_lt : r729 < 729 := Nat.mod_lt y (by decide)
  have hr_m9 : r729 % 9 = 7 := by
    dsimp only [r729]
    rw [Nat.mod_mod_of_dvd y ⟨81, by decide⟩, h9]
  have hq81_lt : r729 / 9 < 81 := by omega
  have hr_eq : r729 = 9 * (r729 / 9) + 7 := by
    have hdm := (Nat.div_add_mod r729 9).symm
    omega
  have hb729 : isSurvivingMod729Bool (y % 729) = true := by
    change isSurvivingMod729Bool r729 = true
    rw [hr_eq]
    exact surviving729_all_mod9_eq7_w17 ⟨r729 / 9, hq81_lt⟩
  have hb512 : isSurvivingMod512Bool (y % 512) = true := by rw [h512]; decide
  have hb373 : isSurvivingMod373248Bool y = true := by
    unfold isSurvivingMod373248Bool; rw [hb512, hb729]; rfl
  exact ⟨hb373, isSurvivingMod373248Bool_imp_class y hb373⟩

private def eraseAllNatW17 (b : Nat) : List Nat -> List Nat
  | [] => []
  | x :: xs => if x = b then eraseAllNatW17 b xs else x :: eraseAllNatW17 b xs

private theorem mem_eraseAllNatW17_iff (b : Nat) :
    ∀ (xs : List Nat) (v : Nat), v ∈ eraseAllNatW17 b xs ↔ (v ∈ xs ∧ v ≠ b)
  | [], _ => by simp [eraseAllNatW17]
  | x :: xs, v => by
    simp only [eraseAllNatW17]
    by_cases hxb : x = b
    · simp only [hxb, ite_true, mem_eraseAllNatW17_iff b xs v, List.mem_cons]
      exact ⟨fun ⟨hm, hne⟩ => ⟨Or.inr hm, hne⟩,
             fun ⟨h, hne⟩ => ⟨by rcases h with rfl | hm; { exact False.elim (hne rfl) }; exact hm, hne⟩⟩
    · simp only [hxb, ite_false, List.mem_cons, mem_eraseAllNatW17_iff b xs v]
      exact ⟨fun h => by rcases h with rfl | ⟨hm, hne⟩; { exact ⟨Or.inl rfl, hxb⟩ }; exact ⟨Or.inr hm, hne⟩,
             fun ⟨h, hne⟩ => by rcases h with rfl | hm; { exact Or.inl rfl }; exact Or.inr ⟨hm, hne⟩⟩

private theorem eraseAllNatW17_of_not_mem (b : Nat) :
    ∀ (xs : List Nat), b ∉ xs -> eraseAllNatW17 b xs = xs
  | [], _ => rfl
  | x :: xs, hnm => by
    have hxb : x ≠ b := fun h => hnm (h ▸ List.Mem.head _)
    have hnm_xs : b ∉ xs := fun hm => hnm (List.mem_cons_of_mem _ hm)
    simp only [eraseAllNatW17, hxb, ite_false, eraseAllNatW17_of_not_mem b xs hnm_xs]

private theorem nodup_eraseAllNatW17_and_len (b : Nat) :
    ∀ (xs : List Nat),
      NoDupNat xs -> NoDupNat (eraseAllNatW17 b xs) ∧ xs.length ≤ (eraseAllNatW17 b xs).length + 1
  | [], _ => ⟨NoDupNat.nil, by simp [eraseAllNatW17]⟩
  | x :: xs, NoDupNat.cons _ _ hnx hnd => by
    by_cases hxb : x = b
    · subst hxb
      simp only [eraseAllNatW17, ite_true, eraseAllNatW17_of_not_mem x xs hnx, List.length_cons]
      exact ⟨hnd, Nat.le_refl _⟩
    · rcases nodup_eraseAllNatW17_and_len b xs hnd with ⟨hnd_er, hlen_er⟩
      simp only [eraseAllNatW17, hxb, ite_false, List.length_cons]
      have hnx_er : x ∉ eraseAllNatW17 b xs :=
        fun hm => hnx ((mem_eraseAllNatW17_iff b xs x).mp hm).1
      exact ⟨NoDupNat.cons x _ hnx_er hnd_er, by omega⟩

private theorem noDupNat_length_le_of_subset_w17 :
    ∀ (cands xs : List Nat),
      NoDupNat xs -> (∀ y ∈ xs, y ∈ cands) -> xs.length ≤ cands.length
  | [], [], _, _ => Nat.le_refl 0
  | [], x :: _, _, hsub => by cases hsub x (List.Mem.head _)
  | b :: bs, xs, hnd, hsub => by
    rcases nodup_eraseAllNatW17_and_len b xs hnd with ⟨hnd', hlen'⟩
    have hsub' : ∀ y ∈ eraseAllNatW17 b xs, y ∈ bs := by
      intro y hy
      rcases (mem_eraseAllNatW17_iff b xs y).mp hy with ⟨hy_xs, hne⟩
      rcases List.mem_cons.mp (hsub y hy_xs) with rfl | hbs
      · exact False.elim (hne rfl)
      · exact hbs
    have ih := noDupNat_length_le_of_subset_w17 bs (eraseAllNatW17 b xs) hnd' hsub'
    simp only [List.length_cons]; omega

private def descIdxListW17 : Nat -> List Nat
  | 0 => []
  | r + 1 => r :: descIdxListW17 r

private theorem descIdxListW17_spec :
    ∀ r : Nat,
      (descIdxListW17 r).length = r ∧
      NoDupNat (descIdxListW17 r) ∧
      (∀ j ∈ descIdxListW17 r, j < r)
  | 0 => ⟨rfl, NoDupNat.nil, fun _ hm => by cases hm⟩
  | r + 1 => by
    rcases descIdxListW17_spec r with ⟨hlen, hnd, hlt⟩
    have hnot_mem : r ∉ descIdxListW17 r := fun hm => Nat.lt_irrefl r (hlt r hm)
    refine ⟨by simp [descIdxListW17, hlen], NoDupNat.cons r _ hnot_mem hnd, ?_⟩
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hm
    · omega
    · have := hlt j hm; omega

private theorem noDupNat_map_inj_on_w17 (f : Nat -> Nat) :
    ∀ (js : List Nat),
      NoDupNat js ->
      (∀ a ∈ js, ∀ b ∈ js, f a = f b -> a = b) ->
      NoDupNat (js.map f)
  | [], _, _ => NoDupNat.nil
  | j :: js, NoDupNat.cons _ _ hnj hnd, hinj => by
    refine NoDupNat.cons (f j) (js.map f) ?_
      (noDupNat_map_inj_on_w17 f js hnd (fun a ha b hb =>
        hinj a (List.mem_cons_of_mem j ha) b (List.mem_cons_of_mem j hb)))
    intro hm
    rcases List.mem_map.mp hm with ⟨j', hj', heq⟩
    have hj_eq := hinj j' (List.mem_cons_of_mem j hj') j (List.Mem.head _) heq
    exact hnj (hj_eq ▸ hj')

private theorem pow3_gt_two_mul_w17 : ∀ n : Nat, 3 ^ n > 2 * n
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by have ih := pow3_gt_two_mul_w17 (n + 1); rw [Nat.pow_succ]; omega

private theorem uWinExp17_per_mask_core_and_key_w17
    (B M mask : Nat) (hB : B ≥ 1) (hM : M ≥ dyadicExpWindowMinM17 B)
    (_hmask : mask < 2 ^ B) :
    let k2 := (B + 1) / 2
    let w := 2 * k2 + 8
    let b0 := binBitLength (3 ^ w)
    let delta2 := 2 + dyadicPolyShiftDelta (b0 + 2)
    let a := b0 + delta2
    let u_e := uWinExp17 B M mask
    IsCoreParityWord u_e ∧
    u_e.length = M - delta2 ∧
    parityWeight u_e = w ∧
    canonicalSuffixShift u_e 1 = a ∧
    IsFirstHitOnePair u_e 0 ∧
    affineCarry u_e ≥ 1 ∧
    affineCarry u_e < 2 ^ M ∧
    (∃ mid : List Bool, u_e = minWeight6Prefix507 ++ mid ++ [true]) ∧
    (∃ m : Nat, 2 ^ (u_e.length + a) = 3 ^ w * (9 * m + 7) + affineCarry u_e) := by
  dsimp only
  let k2 := (B + 1) / 2
  let w := 2 * k2 + 8
  let b0 := binBitLength (3 ^ w)
  let delta2 := 2 + dyadicPolyShiftDelta (b0 + 2)
  let a := b0 + delta2
  let q3 := (2 ^ (a + 1) - 1) / 3
  let L := M - delta2
  have hk2_ge1 : k2 ≥ 1 := by dsimp [k2]; omega
  have h11k2_le : 11 * k2 ≤ 6 * B + 5 := by dsimp [k2]; omega
  have hw_eq : w = 2 * k2 + 8 := rfl
  have ha_eq : a = b0 + delta2 := rfl
  have hL_eq : L = M - delta2 := rfl
  have hw_ge10 : w ≥ 10 := by rw [hw_eq]; omega
  rcases pow3_bitlength_strict_bounds_w17 w hw_ge10 with ⟨hb0_ge16, hb0_le2w, h3w_lo, _⟩
  change b0 ≥ 16 at hb0_ge16
  change b0 ≤ 2 * w at hb0_le2w
  change 3 ^ w + 1 ≤ 2 ^ b0 at h3w_lo
  rcases dyadicPolyShiftDelta2_spec_w17 b0 with ⟨hd2_lo, hd2_hi, h3q3, hq3_n3, _⟩
  change 2 ≤ delta2 at hd2_lo
  change delta2 ≤ 5 at hd2_hi
  change 3 * q3 + 1 = 2 ^ (a + 1) at h3q3
  change q3 % 3 ≠ 0 at hq3_n3
  have hM_def : M ≥ 26265 + 6 * B := hM
  have hL_ge : L ≥ 26260 + 6 * B := by rw [hL_eq]; omega
  have ha_lt_P : a < 2 * 3 ^ (w - 1) := by
    have ha_le : a ≤ 2 * w + 5 := by rw [ha_eq]; omega
    have hw1_gt : 3 ^ (w - 1) > 2 * (w - 1) := pow3_gt_two_mul_w17 (w - 1)
    have hp9 : 3 ^ (w - 1) ≥ 19683 := by
      simpa using nat_pow_mono_exp_pos 3 9 (w - 1) (by decide) (by omega)
    omega
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
  have hq3_ge_pow3 : q3 ≥ 2 * 3 ^ (2 * k2 + 8) - 1 := by
    have ha1_ge8 : 2 ^ (a + 1) ≥ 8 * 2 ^ b0 := by
      have h : 2 ^ (3 + b0) ≤ 2 ^ (a + 1) := pow2_mono_nat (by rw [ha_eq]; omega)
      rwa [Nat.pow_add 2 3 b0] at h
    have hge8 : 3 * q3 + 1 ≥ 8 * (3 ^ (2 * k2 + 8) + 1) := by
      rw [h3q3, ← hw_eq]
      exact Nat.le_trans (Nat.mul_le_mul_left 8 h3w_lo) ha1_ge8
    generalize 3 ^ (2 * k2 + 8) = P3 at hge8 ⊢
    omega
  have hR0_lo : R0 ≥ (2 * 3 ^ (2 * k2 + 8) - 1) * 2 ^ (L - 1) :=
    Nat.mul_le_mul_right _ hq3_ge_pow3
  rcases (twoStepTernaryCarryChain_spec_and_inj_w17 k2 (L - 1) R0 (L - 1)
    (Nat.le_refl _) (by omega) hR0_n3 hR0_lo).1 mask with
    ⟨he_lo, he_hi, hlen_gaps, hRfin_n3, hRfin_lo, hunwind⟩
  let ch := twoStepTernaryCarryChain k2 (L - 1) R0 mask
  let e_fin := ch.1
  let R_fin := ch.2.1
  let gaps := ch.2.2
  change (L - 1) - 11 * k2 ≤ e_fin at he_lo
  change e_fin ≤ L - 1 at he_hi
  change gaps.length = 2 * k2 at hlen_gaps
  change R_fin % 3 ≠ 0 at hRfin_n3
  change R_fin ≥ (2 * 3 ^ 8 - 1) * 2 ^ (L - 1) at hRfin_lo
  have he_fin_ge : e_fin ≥ 26254 := by omega
  have h2L1_ge20 : 2 ^ (L - 1) ≥ 1048576 := by
    rw [show (1048576 : Nat) = 2 ^ 20 from rfl]; exact pow2_mono_nat (by omega)
  have hRfin_big : R_fin ≥ 13121 * 2 ^ (L - 1) := by
    simpa [show 2 * 3 ^ 8 - 1 = 13121 by decide] using hRfin_lo
  -- Final Hensel step at `243x`-smaller fixed modulus `3 ^ 9 = 19683`:
  let sub_c := 3 * 1085 + 7 * 3 ^ 7
  have hsub_val : sub_c = 18564 := by decide
  let A_last := R_fin - sub_c
  have hA_eq_def : A_last = R_fin - sub_c := rfl
  have hsub_lt_Rfin : sub_c < R_fin := by omega
  have hA_n3 : (A_last % 3 ^ 9) % 3 ≠ 0 := by
    have hAn3 : A_last % 3 ≠ 0 := by
      have hrew : R_fin = A_last + 3 * 6188 := by rw [hA_eq_def, hsub_val]; omega
      intro h0
      have hm0 : R_fin % 3 = 0 := by rw [hrew, Nat.add_mul_mod_self_left, h0]
      exact hRfin_n3 hm0
    rwa [Nat.mod_mod_of_dvd A_last ⟨3 ^ 8, by decide⟩]
  rcases dlog2ModPow3_spec 9 (A_last % 3 ^ 9) (by decide) hA_n3 with
    ⟨htb_lt_raw, htb_mod_raw⟩
  let t_base := dlog2ModPow3 9 (A_last % 3 ^ 9)
  change t_base < 2 * 3 ^ (9 - 1) at htb_lt_raw
  change 2 ^ t_base % 3 ^ 9 = (A_last % 3 ^ 9) % 3 ^ 9 at htb_mod_raw
  have hper9_eq : 2 * 3 ^ (9 - 1) = 13122 := by decide
  have htb_lt : t_base < 13122 := by rwa [hper9_eq] at htb_lt_raw
  rcases (⟨13122 + t_base, rfl⟩ : ∃ p : Nat, p = 13122 + t_base) with ⟨p_last, hplast_def⟩
  have hplast_ge : p_last ≥ 13122 := by rw [hplast_def]; omega
  have hplast_lt : p_last < 26244 := by rw [hplast_def]; omega
  have hplast_efin : p_last + 10 ≤ e_fin := by omega
  have hmod_plast : 2 ^ p_last % 3 ^ 9 = A_last % 3 ^ 9 := by
    have hp_per : 2 ^ p_last % 3 ^ (8 + 1) = 2 ^ t_base % 3 ^ (8 + 1) := by
      rw [hplast_def, Nat.add_comm 13122 t_base, show (13122 : Nat) = 2 * 3 ^ 8 by decide]
      exact pow2_add_period_mod_pow3_w17 8 t_base
    change 2 ^ p_last % 3 ^ 9 = 2 ^ t_base % 3 ^ 9 at hp_per
    rw [hp_per]
    rw [Nat.mod_mod] at htb_mod_raw
    exact htb_mod_raw
  have h2p_lt_A : 2 ^ p_last < A_last := by
    have hle : 2 ^ p_last ≤ 2 ^ (L - 1) := pow2_mono_nat (by omega)
    omega
  have hdiff_mod : (A_last - 2 ^ p_last) % 3 ^ 9 = 0 := by
    let P9 := (3 : Nat) ^ 9
    change (A_last - 2 ^ p_last) % P9 = 0
    change 2 ^ p_last % P9 = A_last % P9 at hmod_plast
    have hdmA := (Nat.div_add_mod A_last P9).symm
    have hdmB := (Nat.div_add_mod (2 ^ p_last) P9).symm
    rw [hmod_plast] at hdmB
    have hsub_eq : A_last - 2 ^ p_last = P9 * (A_last / P9 - (2 ^ p_last) / P9) := by
      rw [Nat.mul_sub_left_distrib]
      generalize P9 * (A_last / P9) = QA, P9 * ((2 ^ p_last) / P9) = QB,
        A_last % P9 = rem, A_last = AN, 2 ^ p_last = BN at hdmA hdmB h2p_lt_A ⊢
      omega
    rw [hsub_eq, Nat.mul_mod_right]
  rcases Nat.dvd_of_mod_eq_zero hdiff_mod with ⟨m, hm_eq⟩
  have hA_rec : A_last = 3 ^ 9 * m + 2 ^ p_last := by
    rw [← hm_eq, Nat.sub_add_cancel (Nat.le_of_lt h2p_lt_A)]
  -- Build prefix words `u_0`, `u_1`, `u_2` up to `e_fin + 1`:
  let u0 := minWeight6Prefix507
  let u1 := (u0 ++ List.replicate (p_last - 9) false) ++ [true]
  let u2 := (u1 ++ List.replicate (e_fin - (p_last + 1)) false) ++ [true]
  have hu0_car : affineCarry u0 = 1085 := by decide
  rcases affineCarry_append_replicate_false u0 (p_last - 9) with ⟨hwt_u0z, hcar_u0z⟩
  have hlen_u0z : (u0 ++ List.replicate (p_last - 9) false).length = p_last := by
    rw [List.length_append, show u0.length = 9 from rfl, List.length_replicate]; omega
  have hlen_u1 : u1.length = p_last + 1 := by
    dsimp [u1]; rw [List.length_append, hlen_u0z, List.length_singleton]
  have hwt_u1 : parityWeight u1 = 7 := by
    dsimp [u1]; rw [parityWeight_append, hwt_u0z]; rfl
  have hcar_u1 : affineCarry u1 = 3 * 1085 + 2 ^ p_last := by
    dsimp [u1]; rw [affineCarry_append, hcar_u0z, hu0_car, hlen_u0z]
    have hc1 : affineCarry [true] = 1 := rfl
    have hw1 : parityWeight [true] = 1 := rfl
    rw [hc1, hw1]; omega
  have hcar_u1_lt : affineCarry u1 < 2 ^ (p_last + 1) := by
    rw [hcar_u1, Nat.pow_succ 2 p_last]
    have hp20 : 2 ^ p_last ≥ 1048576 := by
      rw [show (1048576 : Nat) = 2 ^ 20 from rfl]; exact pow2_mono_nat (by omega)
    generalize 2 ^ p_last = ZP at hp20 ⊢; omega
  rcases affineCarry_append_replicate_false u1 (e_fin - (p_last + 1)) with ⟨hwt_u1z, hcar_u1z⟩
  have hlen_u1z : (u1 ++ List.replicate (e_fin - (p_last + 1)) false).length = e_fin := by
    rw [List.length_append, hlen_u1, List.length_replicate]; omega
  have hlen_u2 : u2.length = e_fin + 1 := by
    dsimp [u2]; rw [List.length_append, hlen_u1z, List.length_singleton]
  have hwt_u2 : parityWeight u2 = 8 := by
    dsimp [u2]; rw [parityWeight_append, hwt_u1z, hwt_u1]; rfl
  have hcar_u2 : affineCarry u2 = 3 * affineCarry u1 + 2 ^ e_fin := by
    dsimp [u2]; rw [affineCarry_append, hcar_u1z, hlen_u1z]
    have hc1 : affineCarry [true] = 1 := rfl
    have hw1 : parityWeight [true] = 1 := rfl
    rw [hc1, hw1]; omega
  have hcar_u2_lt : affineCarry u2 < 6 * 2 ^ e_fin := by
    rw [hcar_u2]
    have hc_le : affineCarry u1 < 2 ^ e_fin :=
      Nat.lt_of_lt_of_le hcar_u1_lt (pow2_mono_nat (by omega))
    generalize 2 ^ e_fin = Z at hc_le ⊢; omega
  let Q1 := 3 ^ 7 * (9 * m + 7)
  have hRfin_Q1 : R_fin = Q1 + affineCarry u1 := by
    have hR_sub : R_fin = A_last + sub_c := by
      rw [hA_eq_def, Nat.sub_add_cancel (Nat.le_of_lt hsub_lt_Rfin)]
    have hQ1_exp : Q1 = 19683 * m + 15309 := by
      have h37 : (3 : Nat) ^ 7 = 2187 := by decide
      dsimp only [Q1]; rw [h37]; omega
    have h39 : (3 : Nat) ^ 9 = 19683 := by decide
    rw [hR_sub, hA_rec, h39, hQ1_exp, hcar_u1, hsub_val]
    generalize 2 ^ p_last = ZP; omega
  have hu2_base_eq : 3 * R_fin + 2 ^ e_fin = 3 * Q1 + affineCarry u2 := by
    rw [hRfin_Q1, hcar_u2, Nat.mul_add, Nat.add_assoc]
  rcases hunwind u2 Q1 hlen_u2 hcar_u2_lt hu2_base_eq with
    ⟨hw_len, hw_wt, hw_car, hw_key⟩
  have hu_eq_wout : uWinExp17 B M mask = u2 ++ zeroRunsSuffix gaps := by
    unfold uWinExp17 uWinExp17Runs
    have hr_split : (p_last - 9) :: (e_fin - (p_last + 1)) :: gaps =
        [p_last - 9, e_fin - (p_last + 1)] ++ gaps := rfl
    dsimp only
    change u0 ++ zeroRunsSuffix (((13122 + t_base) - 9) :: (e_fin - ((13122 + t_base) + 1)) :: gaps) = _
    rw [← hplast_def, hr_split, zeroRunsSuffix_append_and_inj_w17.1 [p_last - 9, e_fin - (p_last + 1)] gaps]
    dsimp only [zeroRunsSuffix, u2, u1]
    simp [List.append_assoc]
  rcases (⟨uWinExp17 B M mask, rfl⟩ : ∃ u_x : List Bool, u_x = uWinExp17 B M mask) with ⟨u_e, hue_def⟩
  have hue_wout : u_e = u2 ++ zeroRunsSuffix gaps := hue_def.trans hu_eq_wout
  rw [← hue_wout] at hw_len hw_wt hw_car hw_key
  have hlen_final : u_e.length = L := by rw [hw_len]; omega
  have hwt_final : parityWeight u_e = w := by rw [hw_wt, hwt_u2, hw_eq]; omega
  have hcar_lt_M : affineCarry u_e < 2 ^ M := by
    have h8 : affineCarry u_e < 8 * 2 ^ (L - 1) := by omega
    have hp8 : 8 * 2 ^ (L - 1) = 2 ^ (L + 2) := by
      rw [show (8 : Nat) = 2 ^ 3 from rfl, ← Nat.pow_add 2 3 (L - 1),
          show 3 + (L - 1) = L + 2 by omega]
    rw [hp8] at h8
    exact Nat.lt_of_lt_of_le h8 (pow2_mono_nat (by rw [hL_eq]; omega))
  have hkey_final : 2 ^ (u_e.length + a) = 3 ^ w * (9 * m + 7) + affineCarry u_e := by
    have hlhs : 2 ^ (L + a) = 3 * R0 + 2 ^ (L - 1) := by
      dsimp [R0]
      rw [show L + a = (a + 1) + (L - 1) by omega, Nat.pow_add 2 (a + 1) (L - 1),
          ← h3q3, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
    have hrhs : 3 ^ (2 * k2 + 1) * Q1 = 3 ^ w * (9 * m + 7) := by
      dsimp [Q1]
      rw [← Nat.mul_assoc, ← Nat.pow_add 3 (2 * k2 + 1) 7,
          show (2 * k2 + 1) + 7 = w by rw [hw_eq]]
    rw [hlen_final, hlhs, hw_key, hrhs]
  have hmid_ex : ∃ mid : List Bool, u_e = minWeight6Prefix507 ++ mid ++ [true] := by
    rcases zeroRunsSuffix_nonempty_eq_mid_true_w17 (p_last - 9) ((e_fin - (p_last + 1)) :: gaps) with
      ⟨mid, hmid⟩
    refine ⟨mid, ?_⟩
    rw [hue_def]; unfold uWinExp17 uWinExp17Runs
    dsimp only
    change minWeight6Prefix507 ++ zeroRunsSuffix (((13122 + t_base) - 9) :: (e_fin - ((13122 + t_base) + 1)) :: gaps) = _
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
      rcases zeroRunsSuffix_nonempty_eq_mid_true_w17 g0 gtl with ⟨m_g, hmg⟩
      rw [hmg, ← List.append_assoc u2 m_g [true], affineCarry_append]
      have hc1 : affineCarry [true] = 1 := rfl
      rw [hc1, Nat.mul_one]
      have hp := pow2_pos_nat (u2 ++ m_g).length
      omega
  subst hue_def
  exact ⟨hcore_u, hlen_final, hwt_final, hsh_a, hfh, hcar_pos, hcar_lt_M, hmid_ex, ⟨m, hkey_final⟩⟩

private theorem uWinExp17_per_mask_leaf_spec_w17
    (B M mask : Nat) (hB : B ≥ 1) (hM : M ≥ dyadicExpWindowMinM17 B)
    (hmask : mask < 2 ^ B) :
    let k2 := (B + 1) / 2
    let w := 2 * k2 + 8
    let b0 := binBitLength (3 ^ w)
    let delta2 := 2 + dyadicPolyShiftDelta (b0 + 2)
    let u := uWinExp17 B M mask
    let y := exactBackwardQuotient 1 u 0
    IsFirstHitOnePair u 0 ∧
    u.length = M - delta2 ∧
    u.length ≤ M ∧
    parityWeight u = w ∧
    canonicalSuffixShift u 1 = b0 + delta2 ∧
    y % 512 = 507 ∧
    y % 9 = 7 ∧
    isSurvivingMod373248Bool y = true ∧
    IsSurvivingMod373248Class y ∧
    2 ^ M ≤ y ∧ y < 2 ^ (M + 1) ∧
    (∀ L_max : Nat, L_max ≥ M -> y ∈ dyadicWindowSurvivingQ0Leaves L_max M) := by
  dsimp only
  let k2 := (B + 1) / 2
  let w := 2 * k2 + 8
  let b0 := binBitLength (3 ^ w)
  let delta2 := 2 + dyadicPolyShiftDelta (b0 + 2)
  let a := b0 + delta2
  have hk2_ge1 : k2 ≥ 1 := by dsimp [k2]; omega
  have hw_eq : w = 2 * k2 + 8 := rfl
  have ha_eq : a = b0 + delta2 := rfl
  rcases pow3_bitlength_strict_bounds_w17 w (by rw [hw_eq]; omega) with ⟨_, _, h3w_lo, h2b0_hi⟩
  change 3 ^ w + 1 ≤ 2 ^ b0 at h3w_lo
  change 2 ^ b0 < 2 * 3 ^ w at h2b0_hi
  rcases dyadicPolyShiftDelta2_spec_w17 b0 with ⟨_, hd2_hi, _, _, _⟩
  change delta2 ≤ 5 at hd2_hi
  have hM_ge30 : M ≥ 30 := by unfold dyadicExpWindowMinM17 at hM; omega
  rcases uWinExp17_per_mask_core_and_key_w17 B M mask hB hM hmask with
    ⟨hcore_r, hlen_r, hwt_r, hsh_r, hfh_r, hcar_pos_r, hcar_lt_r, ⟨mid, hu_mid_r⟩, ⟨m, hkey_r⟩⟩
  rcases (⟨uWinExp17 B M mask, rfl⟩ : ∃ u0 : List Bool, u0 = uWinExp17 B M mask) with ⟨u_e, hue_def⟩
  rw [← hue_def] at hcore_r hlen_r hwt_r hsh_r hfh_r hcar_pos_r hcar_lt_r hu_mid_r hkey_r
  change u_e.length = M - delta2 at hlen_r
  change parityWeight u_e = w at hwt_r
  change canonicalSuffixShift u_e 1 = a at hsh_r
  change 2 ^ (u_e.length + a) = 3 ^ w * (9 * m + 7) + affineCarry u_e at hkey_r
  rcases (⟨exactBackwardQuotient 1 u_e 0, rfl⟩ :
      ∃ y0 : Nat, y0 = exactBackwardQuotient 1 u_e 0) with ⟨y, hy_def⟩
  have hy_9m7 : y = 9 * m + 7 := by
    rcases one_generator_pos_odd_and_reaches_one u_e 0 hcore_r with ⟨_, _, heq_bw, _⟩
    have hbw_steps : backwardOneTotalSteps u_e 0 = u_e.length + a := by
      unfold backwardOneTotalSteps; rw [hsh_r]; omega
    rw [hbw_steps, hwt_r, ← hy_def] at heq_bw
    have hcomb : 3 ^ w * y = 3 ^ w * (9 * m + 7) :=
      Nat.add_right_cancel (heq_bw.symm.trans hkey_r)
    exact Nat.eq_of_mul_eq_mul_left (pow3_pos_nat w) hcomb
  have hy_m9 : y % 9 = 7 := by rw [hy_9m7]; omega
  have hy_m512 : y % 512 = 507 := by
    have hp9_507 : parityOfIter 9 507 = minWeight6Prefix507 := by decide
    have hu_507 : u_e = parityOfIter 9 507 ++ mid ++ [true] := by rw [hp9_507]; exact hu_mid_r
    have hm := (surviving_mod512_nine_prefix_auto_weight_and_characterization.1 507
      (by decide) (by decide)).2.2.2 mid 0 |>.2.2.1
    rwa [← hu_507, ← hy_def] at hm
  rcases isSurvivingMod373248_of_507_and_mod9_eq7_w17 y hy_m512 hy_m9 with ⟨hb_surv, hcls_surv⟩
  have hy_win : 2 ^ M ≤ y ∧ y < 2 ^ (M + 1) := by
    have hLa_eq : u_e.length + a = b0 + M := by rw [hlen_r, ha_eq]; omega
    have heq_y : 3 ^ w * y + affineCarry u_e = 2 ^ b0 * 2 ^ M := by
      have hk := hkey_r.symm
      rwa [← hy_9m7, hLa_eq, Nat.pow_add 2 b0 M] at hk
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
         hy_m512, hy_m9, hb_surv, hcls_surv, hy_win.1, hy_win.2, hy_mem_win⟩

private theorem uWinExp17_inj_mask_w17
    (B M m1 m2 : Nat) (hB : B ≥ 1) (hM : M ≥ dyadicExpWindowMinM17 B)
    (hm1 : m1 < 2 ^ B) (hm2 : m2 < 2 ^ B)
    (hy_eq : exactBackwardQuotient 1 (uWinExp17 B M m1) 0 =
      exactBackwardQuotient 1 (uWinExp17 B M m2) 0) :
    m1 = m2 := by
  have hfh1 := (uWinExp17_per_mask_core_and_key_w17 B M m1 hB hM hm1).2.2.2.2.1
  have hfh2 := (uWinExp17_per_mask_core_and_key_w17 B M m2 hB hM hm2).2.2.2.2.1
  have hu_eq : uWinExp17 B M m1 = uWinExp17 B M m2 :=
    (first_hit_one_pair_sound_and_injective _ _ 0 0 hfh1 hfh2).2.2.2 hy_eq |>.1
  unfold uWinExp17 at hu_eq
  have hzs_eq := (list_append_inj_left_eq_len _ _ _ _ rfl hu_eq).2
  have hruns_eq := zeroRunsSuffix_append_and_inj_w17.2 _ _ hzs_eq
  unfold uWinExp17Runs at hruns_eq
  dsimp only at hruns_eq
  have hgaps_eq := (List.cons.inj (List.cons.inj hruns_eq).2).2
  let k2 := (B + 1) / 2
  let w := 2 * k2 + 8
  let b0 := binBitLength (3 ^ w)
  let delta2 := 2 + dyadicPolyShiftDelta (b0 + 2)
  let a := b0 + delta2
  let q3 := (2 ^ (a + 1) - 1) / 3
  let L := M - delta2
  have hk2_ge1 : k2 ≥ 1 := by dsimp [k2]; omega
  have h11k2_le : 11 * k2 ≤ 6 * B + 5 := by dsimp [k2]; omega
  rcases pow3_bitlength_strict_bounds_w17 w (by dsimp [w]; omega) with ⟨_, _, h3w_lo, _⟩
  change 3 ^ w + 1 ≤ 2 ^ b0 at h3w_lo
  rcases dyadicPolyShiftDelta2_spec_w17 b0 with ⟨hd2_lo, hd2_hi, h3q3, hq3_n3, _⟩
  change 2 ≤ delta2 at hd2_lo
  change delta2 ≤ 5 at hd2_hi
  change 3 * q3 + 1 = 2 ^ (a + 1) at h3q3
  change q3 % 3 ≠ 0 at hq3_n3
  have hL_ge : L ≥ 26260 + 6 * B := by dsimp [L]; unfold dyadicExpWindowMinM17 at hM; omega
  have hR0_n3 : (q3 * 2 ^ (L - 1)) % 3 ≠ 0 := by
    intro h0; rw [Nat.mul_mod] at h0
    have hp2_n3 := pow2_mod3_nonzero_w5 (L - 1)
    have hq3_lt : q3 % 3 < 3 := Nat.mod_lt q3 (by decide)
    have hp2_lt : 2 ^ (L - 1) % 3 < 3 := Nat.mod_lt _ (by decide)
    rcases (by omega : q3 % 3 = 1 ∨ q3 % 3 = 2) with hq | hq <;>
    rcases (by omega : 2 ^ (L - 1) % 3 = 1 ∨ 2 ^ (L - 1) % 3 = 2) with hp | hp <;>
    (rw [hq, hp] at h0; cases h0)
  have hq3_ge : q3 ≥ 2 * 3 ^ (2 * k2 + 8) - 1 := by
    have ha1_ge8 : 2 ^ (a + 1) ≥ 8 * 2 ^ b0 := by
      have h : 2 ^ (3 + b0) ≤ 2 ^ (a + 1) := pow2_mono_nat (by dsimp [a]; omega)
      rwa [Nat.pow_add 2 3 b0] at h
    have hge8 : 3 * q3 + 1 ≥ 8 * (3 ^ (2 * k2 + 8) + 1) := by
      rw [h3q3]; exact Nat.le_trans (Nat.mul_le_mul_left 8 h3w_lo) ha1_ge8
    generalize 3 ^ (2 * k2 + 8) = P3 at hge8 ⊢; omega
  have h4k2 : 2 ^ B ≤ 4 ^ k2 := by
    rw [pow4_eq_pow2_even k2]
    exact pow2_mono_nat (by dsimp [k2]; omega)
  exact (twoStepTernaryCarryChain_spec_and_inj_w17 k2 (L - 1) (q3 * 2 ^ (L - 1)) (L - 1)
    (Nat.le_refl _) (by omega) hR0_n3 (Nat.mul_le_mul_right _ hq3_ge)).2
    m1 m2 (Nat.lt_of_lt_of_le hm1 h4k2) (Nat.lt_of_lt_of_le hm2 h4k2) hgaps_eq

/--
  Theorem W17.4c (`dyadic_window_243x_compressed_steeper_slope_exponential_occupancy`,
  `zero custom axioms`):
  Constructive `243x`-Compressed (`6377332 -> 26265`), Steeper-Slope (`c = 6 <= 6`, Beating `c = 8`!)
  2-Step `Mod 27` Ternary-Carry-Lifted Family `uWinExp17 B M mask` & Unconditional True Exponential
  Surviving-Leaf Dyadic-Window Occupancy (`≥ 2 ^ B` at Linear Threshold `M ≥ 26265 + 6 * B`, i.e.
  `≥ 2 ^ ((M - 26265) / 6)` at Linear Horizon `L_max ≥ M`, `Branches P2.2 & P5.3`, `W17_H4`).
-/
theorem dyadic_window_243x_compressed_steeper_slope_exponential_occupancy :
    (∀ (B M : Nat), B ≥ 1 -> M ≥ dyadicExpWindowMinM17 B ->
      let k2 := (B + 1) / 2
      let w := 2 * k2 + 8
      let b0 := binBitLength (3 ^ w)
      let delta2 := 2 + dyadicPolyShiftDelta (b0 + 2)
      (∀ mask : Nat, mask < 2 ^ B ->
        let u := uWinExp17 B M mask
        let y := exactBackwardQuotient 1 u 0
        IsFirstHitOnePair u 0 ∧
        u.length = M - delta2 ∧
        u.length ≤ M ∧
        parityWeight u = w ∧
        canonicalSuffixShift u 1 = b0 + delta2 ∧
        y % 512 = 507 ∧
        y % 9 = 7 ∧
        IsSurvivingMod373248Class y ∧
        2 ^ M ≤ y ∧ y < 2 ^ (M + 1) ∧
        y ∈ dyadicWindowSurvivingQ0Leaves M M ∧
        (∀ L_max : Nat, L_max ≥ M -> y ∈ dyadicWindowSurvivingQ0Leaves L_max M)) ∧
      (∀ m1 m2 : Nat, m1 < 2 ^ B -> m2 < 2 ^ B ->
        exactBackwardQuotient 1 (uWinExp17 B M m1) 0 =
          exactBackwardQuotient 1 (uWinExp17 B M m2) 0 ->
        m1 = m2) ∧
      ((dyadicWindowSurvivingQ0Leaves M M).length ≥ 2 ^ B ∧
       ∀ L_max : Nat, L_max ≥ M ->
         (dyadicWindowSurvivingQ0Leaves L_max M).length ≥ 2 ^ B)) ∧
    (∀ (M L_max : Nat), M ≥ 26271 -> L_max ≥ M ->
      (dyadicWindowSurvivingQ0Leaves L_max M).length ≥ 2 ^ ((M - 26265) / 6)) := by
  have hmain : ∀ (B M : Nat), B ≥ 1 -> M ≥ dyadicExpWindowMinM17 B ->
      let k2 := (B + 1) / 2
      let w := 2 * k2 + 8
      let b0 := binBitLength (3 ^ w)
      let delta2 := 2 + dyadicPolyShiftDelta (b0 + 2)
      (∀ mask : Nat, mask < 2 ^ B ->
        let u := uWinExp17 B M mask
        let y := exactBackwardQuotient 1 u 0
        IsFirstHitOnePair u 0 ∧
        u.length = M - delta2 ∧
        u.length ≤ M ∧
        parityWeight u = w ∧
        canonicalSuffixShift u 1 = b0 + delta2 ∧
        y % 512 = 507 ∧
        y % 9 = 7 ∧
        IsSurvivingMod373248Class y ∧
        2 ^ M ≤ y ∧ y < 2 ^ (M + 1) ∧
        y ∈ dyadicWindowSurvivingQ0Leaves M M ∧
        (∀ L_max : Nat, L_max ≥ M -> y ∈ dyadicWindowSurvivingQ0Leaves L_max M)) ∧
      (∀ m1 m2 : Nat, m1 < 2 ^ B -> m2 < 2 ^ B ->
        exactBackwardQuotient 1 (uWinExp17 B M m1) 0 =
          exactBackwardQuotient 1 (uWinExp17 B M m2) 0 ->
        m1 = m2) ∧
      ((dyadicWindowSurvivingQ0Leaves M M).length ≥ 2 ^ B ∧
       ∀ L_max : Nat, L_max ≥ M ->
         (dyadicWindowSurvivingQ0Leaves L_max M).length ≥ 2 ^ B) := by
    intro B M hB hM; dsimp only
    refine ⟨?_, fun m1 m2 h1 h2 heq => uWinExp17_inj_mask_w17 B M m1 m2 hB hM h1 h2 heq, ?_⟩
    · intro mask hmask
      rcases uWinExp17_per_mask_leaf_spec_w17 B M mask hB hM hmask with
        ⟨hfh, hlen, hle_M, hwt, hsh, h512, h9, _, hcls, hlo, hhi, hmem⟩
      exact ⟨hfh, hlen, hle_M, hwt, hsh, h512, h9, hcls, hlo, hhi, hmem M (Nat.le_refl M), hmem⟩
    · rcases descIdxListW17_spec (2 ^ B) with ⟨hd_len, hd_nd, hd_lt⟩
      let fnLeaf : Nat -> Nat := fun mask => exactBackwardQuotient 1 (uWinExp17 B M mask) 0
      let leaves2B := (descIdxListW17 (2 ^ B)).map fnLeaf
      have hnd_2B : NoDupNat leaves2B :=
        noDupNat_map_inj_on_w17 fnLeaf (descIdxListW17 (2 ^ B)) hd_nd
          (fun a ha b hb heq => uWinExp17_inj_mask_w17 B M a b hB hM (hd_lt a ha) (hd_lt b hb) heq)
      have hlen_2B : leaves2B.length = 2 ^ B := by
        dsimp only [leaves2B]; rw [List.length_map, hd_len]
      have hall_L : ∀ L_max : Nat, L_max ≥ M ->
          (dyadicWindowSurvivingQ0Leaves L_max M).length ≥ 2 ^ B := by
        intro L_max hL_max
        have hsub_2B : ∀ y ∈ leaves2B, y ∈ dyadicWindowSurvivingQ0Leaves L_max M := by
          intro y hy
          rcases List.mem_map.mp hy with ⟨mask, hmask, rfl⟩
          exact (uWinExp17_per_mask_leaf_spec_w17 B M mask hB hM (hd_lt mask hmask)).2.2.2.2.2.2.2.2.2.2.2 L_max hL_max
        have hle := noDupNat_length_le_of_subset_w17
          (dyadicWindowSurvivingQ0Leaves L_max M) leaves2B hnd_2B hsub_2B
        omega
      exact ⟨hall_L M (Nat.le_refl M), hall_L⟩
  refine ⟨hmain, ?_⟩
  intro M L_max hM hL_max
  let B := (M - 26265) / 6
  have hB1 : B ≥ 1 := by dsimp [B]; omega
  have hM_min : M ≥ dyadicExpWindowMinM17 B := by
    dsimp [B]; unfold dyadicExpWindowMinM17; omega
  exact (hmain B M hB1 hM_min).2.2.2 L_max hL_max

-- ----------------------------------------------------------------------------
-- Section 3C: Breaking the `s = 1` Unary Bottom Barrier via 3-Bit (`s = 3`)
--             Multiplicative-Dlog `Mod 177147` (`3^11`) Collision Lifting:
--             Unconditional Sub-`500` Threshold (`M_0 = 360 ≤ 500`), Steeper-Slope
--             (`c = 6 ≤ 6`) Exponential Dyadic-Window Occupancy (`W17_H4`)
-- ----------------------------------------------------------------------------

private def pow2ModFast : Nat -> Nat -> Nat
  | 0, _ => 1
  | f + 1, n =>
    if decide (n = 0) then 1
    else
      match pow2ModFast f (n / 2) with
      | 0 => 0
      | h + 1 =>
        let sq := ((h + 1) * (h + 1)) % 177147
        if decide (n % 2 = 1) then (2 * sq) % 177147 else sq

private theorem pow2ModFast_step (f n : Nat) :
    pow2ModFast (f + 1) n =
      if n = 0 then 1
      else
        let x := pow2ModFast f (n / 2)
        let sq := (x * x) % 177147
        if n % 2 = 1 then (2 * sq) % 177147 else sq := by
  conv => lhs; unfold pow2ModFast
  by_cases hn0 : n = 0
  · simp [hn0]
  · simp only [hn0, decide_false, Bool.false_eq_true, ite_false]
    rcases hx : pow2ModFast f (n / 2) with _ | h
    · by_cases hodd : n % 2 = 1 <;> simp [hodd]
    · by_cases hodd : n % 2 = 1 <;> simp [hodd]

private theorem pow2ModFast_eq :
    ∀ (f n : Nat), n < 2 ^ f -> pow2ModFast f n = 2 ^ n % 177147
  | 0, n, hn => by
    rw [Nat.pow_zero] at hn
    have hn0 : n = 0 := by omega
    subst hn0; rfl
  | f + 1, n, hn => by
    rw [pow2ModFast_step f n]
    by_cases hn0 : n = 0
    · subst hn0; rfl
    · have hlt_half : n / 2 < 2 ^ f := by rw [Nat.pow_succ] at hn; omega
      have ih := pow2ModFast_eq f (n / 2) hlt_half
      have hsq_eq : ((2 ^ (n / 2) % 177147) * (2 ^ (n / 2) % 177147)) % 177147 =
          2 ^ (2 * (n / 2)) % 177147 := by
        rw [← Nat.mul_mod, ← Nat.pow_add, show (n / 2) + (n / 2) = 2 * (n / 2) by omega]
      by_cases hodd : n % 2 = 1
      · simp only [hn0, ite_false, hodd, ite_true, ih, hsq_eq]
        rw [Nat.mul_mod 2 (2 ^ (2 * (n / 2)) % 177147) 177147, Nat.mod_mod, ← Nat.mul_mod,
            show 2 * 2 ^ (2 * (n / 2)) = 2 ^ (2 * (n / 2) + 1) by rw [Nat.pow_succ, Nat.mul_comm],
            show 2 * (n / 2) + 1 = n by omega]
      · simp only [hn0, ite_false, hodd, ite_false, ih, hsq_eq]
        rw [show 2 * (n / 2) = n by omega]

private theorem sub_mod_eq_zero_of_mod_eq_w17 (M A B : Nat) (hM : M ≥ 1)
    (hBA : B ≤ A) (hmod : B % M = A % M) :
    (A - B) % M = 0 := by
  have hm_lt : A % M < M := Nat.mod_lt A hM
  rw [sub_mod_of_le_w17 M A B hM hBA, hmod,
      show A % M + M - A % M = M by omega, Nat.mod_self]

private def bottom3BitPackedGrid177147 : List (List Nat) :=
  [[3284237, 6168078, 3809815, 9720333, 6046521, 8933453, 4865289, 6578713, 5391900, 3285268, 9184009, 7361099, 6561819, 4078884, 5257004, 2893589, 6954519, 6833434, 9205611, 6169109, 6957601, 8536610, 5781045, 3023386, 5777939, 6178876, 5779990],
   [7623962, 7620886, 6052136, 4999218, 7610643, 5391385, 3414538, 6968876, 8016667, 4602903, 6574117, 4473115, 4073239, 2496268, 2627089, 5388315, 4459273, 2235931, 3283736, 7616272, 5257503, 7630096, 6965309, 4991518, 7235393, 6969941, 7748124],
   [5773842, 6051087, 4467990, 5378058, 6575697, 4865307, 5247758, 6840121, 6041376, 8931879, 7621411, 4863797, 5647660, 4207646, 6962215, 6181920, 6441743, 4859159, 3025939, 9340031, 2499338, 8013593, 8804105, 8140822, 6446363, 4999236, 8548421],
   [8152625, 5643028, 4074252, 4077352, 4997690, 5255460, 5787149, 3024914, 3682066, 4068619, 6167577, 6171170, 4078866, 6052118, 3678990, 6178858, 5784592, 7221551, 3288350, 7367221, 3286794, 6826279, 4867900, 6968397, 5263174, 3024407, 8021305],
   [5255951, 8014630, 7362625, 5393434, 2498313, 7224074, 7616308, 8137742, 5644572, 6970428, 8400662, 5655845, 4599833, 3420698, 4078902, 3811878, 8025907, 4998675, 4598804, 4992523, 7367257, 4598307, 5655356, 6178337, 4863779, 5776928, 8136202],
   [2232849, 7235375, 6838605, 5776910, 8420662, 6830881, 4208671, 8016685, 8419172, 7631682, 3417630, 7611676, 2891548, 6574632, 4602921, 3417113, 1445901, 9594156, 4597282, 2628627, 6973496, 2892049, 7613729, 2630159, 2101002, 7619348, 7623998],
   [7361614, 7631700, 7761481, 5784628, 2890521, 4995593, 6575661, 4598289, 4996120, 3803657, 4863761, 7627571, 4867882, 4986898, 4069656, 3287311, 8020770, 6050604, 2499356, 4991015, 6971443, 4998711, 4864824, 1710358, 6427404, 5783082, 6576166],
   [6436650, 8403762, 4595219, 4072738, 5651243, 4207664, 5653800, 4074761, 9604988, 5385239, 6172191, 3811860, 5655338, 4204057, 6965772, 5646110, 3418633, 5787167, 3286812, 4998693, 9194777, 4860192, 6962233, 7216913, 3419158, 4466446, 2627594],
   [8404257, 8022869, 4076331, 3285777, 6577730, 8010513, 6962197, 6052172, 2103053, 6965273, 5249296, 6838030, 8149513, 7236885, 7758411, 5657403, 8807257, 8143379, 4864806, 8808761, 6968894, 8945721, 6560275, 4466961, 7621429, 1707276, 4600356],
   [3684129, 9191212, 5393470, 8399637, 6049577, 4601884, 1444874, 6839628, 4068106, 3682084, 3684111, 8153118, 8131600, 3676429, 8408841, 5782571, 4591116, 8407331, 6971956, 6572603, 11311239, 5789248, 7364109, 3814447, 9728059, 6045972, 6832427],
   [6041865, 8417604, 3811353, 6957583, 3282709, 8419693, 6035735, 2626060, 5261582, 6435118, 6183478, 4604940, 5784127, 4471096, 7362571, 4997672, 7759949, 6042890, 8947277, 4471581, 5657421, 7227663, 5782553, 6838084, 7236402, 8024391, 4463893],
   [6570012, 6044939, 4596757, 2893080, 5257521, 6176787, 1709331, 6444310, 5262141, 3683622, 6577163, 6435100, 9336847, 4993052, 4864788, 3414037, 3420201, 2894606, 9318946, 5646623, 6175754, 5654281, 8007463, 3810314, 6174256, 3019793, 5392965],
   [3814429, 2104090, 7619366, 7629159, 6963765, 2888466, 5390396, 5394503, 2630680, 3679008, 8419154, 6834960, 7364181, 2497806, 5253928, 8148498, 5787720, 6438711, 2629140, 6969887, 5261636, 6049066, 4604976, 8142362, 4857625, 8003852, 5649715],
   [5789194, 10786615, 4592143, 6443331, 6171152, 1841675, 7756813, 7233823, 7629123, 6176823, 3805712, 5779477, 8537661, 7617804, 9727054, 7230268, 4200969, 6569503, 7233841, 2888969, 3413010, 2104593, 8405258, 6040337, 6966811, 8408376, 5381138],
   [6573092, 3812885, 4987927, 6576184, 7627535, 3683604, 6178319, 5640457, 10508819, 4861742, 5391882, 7621447, 4994598, 2630177, 4077334, 4472586, 8538156, 5263156, 4996138, 6833967, 3025957, 8144953, 6966847, 5773325, 5252901, 3022869, 3288332],
   [7354899, 10912341, 3806739, 2498331, 4856085, 1840137, 8151117, 6956045, 2236432, 6439732, 6170653, 4861724, 7612189, 5390360, 5787684, 3813400, 7740436, 7622472, 6175772, 5392929, 4860687, 3810332, 6830899, 5789230, 6841649, 6041901, 6038294],
   [3018766, 6444364, 3288875, 7226171, 5642003, 6174238, 7362607, 6169618, 4210215, 7741964, 4466979, 3420183, 9207163, 6561801, 6170635, 4993034, 6973478, 8006946, 5382175, 4857110, 8941107, 8140339, 7230232, 9723914, 3677452, 6971974, 3808780],
   [6961206, 5787185, 8154199, 6837029, 6177318, 7760480, 6838048, 7367786, 4994580, 3812903, 5259067, 4472622, 6956568, 5385740, 4205583, 2496785, 4206100, 7360074, 3679509, 5654317, 5252372, 5785659, 10392949, 7233805, 8545832, 6960677, 8411416],
   [6440239, 6434091, 3680522, 7219981, 6050586, 5648163, 4074779, 6442790, 3024932, 4076313, 5382678, 3808271, 5260553, 6174220, 6047540, 3418651, 5258524, 4199443, 6571546, 4604447, 4997137, 4074270, 4208653, 5646092, 8008973, 6446345, 3280654],
   [5259031, 7627589, 7233859, 2499853, 3021834, 6971992, 4866338, 9191733, 7762989, 2625545, 6830364, 4470059, 1840654, 7351817, 8013611, 9600302, 5250846, 7356940, 6435619, 5394449, 8134674, 4464914, 4598822, 5386789, 7232337, 5261618, 3420716],
   [5254411, 7630651, 6038803, 6445842, 6175285, 5775370, 4986383, 6182951, 4603442, 5649697, 4994079, 5260571, 2894624, 6820107, 9602423, 6433562, 4469546, 8416102, 4601353, 5649679, 6181902, 4077859, 5252883, 5260056, 6565410, 4600338, 7752235],
   [9707034, 6577676, 8546853, 4995629, 6435601, 4599851, 4469528, 8016192, 6036762, 6049595, 4868399, 4990997, 4465421, 7364622, 4988432, 4595736, 3410955, 5255969, 7630615, 10522733, 4858654, 7357975, 7622933, 5652238, 3682583, 4209168, 4997654],
   [3680540, 7344650, 8137760, 4075814, 1315084, 6178840, 7350285, 4077841, 5783100, 5643543, 7750721, 9987898, 8002843, 4866356, 6574153, 6438693, 6432539, 4601371, 6838102, 4070159, 10507311, 4207628, 5788723, 9971489, 4468513, 9732673, 5647642],
   [7752744, 6181419, 5781548, 9202471, 2102540, 5259049, 6046008, 4468495, 4604429, 8799521, 5657385, 4593675, 7624016, 9332770, 2499871, 6952969, 3677981, 4208689, 5258506, 7629141, 4206118, 8155659, 4203026, 6182987, 8812836, 6834996, 6840103],
   [10372881, 4858636, 9201948, 5775388, 6052627, 3287329, 6827789, 6047522, 4202507, 5257485, 4860705, 4597264, 4209204, 2234904, 4604994, 4201498, 8406820, 8022851, 4868363, 6438158, 3677963, 7749694, 5389835, 11556632, 3415569, 7631646, 4075796],
   [6047504, 6173705, 4867864, 7622951, 4071711, 4866847, 6578785, 9588004, 6574099, 4071182, 4863268, 5652765, 8814380, 6435082, 8416607, 4989978, 7612171, 4207121, 3417612, 5779495, 4466464, 10888208, 5246729, 4072720, 6180410, 7221022, 4860174],
   [6578731, 5778444, 3682601, 4604958, 4205601, 6823187, 5391918, 3021325, 7628630, 3288857, 7363148, 5651225, 4473097, 8018195, 5258542, 9338415, 4601389, 6841148, 2235913, 4602939, 6964238, 4460300, 5262105, 6577748, 8139276, 7362643, 9595688]]

private def listRowAtW17 : List (List Nat) -> Nat -> List Nat
  | [], _ => []
  | r :: _, 0 => r
  | _ :: rs, k + 1 => listRowAtW17 rs k

private def listNatAtW17 : List Nat -> Nat -> Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, k + 1 => listNatAtW17 xs k

/-- 729-bucket multiplicative discrete-log 3-bit bottom collision lookup modulo `3 ^ 11 = 177147`
    (`118098 = 729 * 162`): maps bucket `q < 729` to `(b_1, b_2, b_3)` with `9 ≤ b_3 < b_2 < b_1 ≤ 176`
    satisfying `(2 ^ b_1 + 3 * 2 ^ b_2 + 9 * 2 ^ b_3) % 177147 = 2 ^ (162 * q) % 177147`. -/
def bottom3BitBucket177147 (q : Nat) : Nat × Nat × Nat :=
  let packed := listNatAtW17 (listRowAtW17 bottom3BitPackedGrid177147 (q / 27)) (q % 27)
  (packed / 65536, (packed / 256) % 256, packed % 256)

private def checkBottom3BitHiLoBool (hi lo : Nat) : Bool :=
  match bottom3BitBucket177147 (27 * hi + lo) with
  | (b1, b2, b3) =>
    decide (9 ≤ b3) && decide (b3 < b2) && decide (b2 < b1) && decide (b1 ≤ 176) &&
    decide (((2 ^ b1 + 3 * 2 ^ b2 + 9 * 2 ^ b3) % 177147) =
      pow2ModFast 17 (162 * (27 * hi + lo)))

private def checkBottom3BitLoLoopBool (hi : Nat) : Nat -> Bool
  | 0 => true
  | k + 1 => checkBottom3BitHiLoBool hi k && checkBottom3BitLoLoopBool hi k

private def checkBottom3BitHiRangeBool : Nat -> Nat -> Bool
  | _, 0 => true
  | start, cnt + 1 => checkBottom3BitLoLoopBool start 27 && checkBottom3BitHiRangeBool (start + 1) cnt

private theorem checkBottom3BitHiRangeBool_append (s : Nat) :
    ∀ (a b : Nat),
      checkBottom3BitHiRangeBool s a = true ->
      checkBottom3BitHiRangeBool (s + a) b = true ->
      checkBottom3BitHiRangeBool s (a + b) = true := by
  intro a
  induction a generalizing s with
  | zero =>
    intro b _ h2
    simpa only [Nat.add_zero, Nat.zero_add] using h2
  | succ a' ih =>
    intro b h1 h2
    rw [show a' + 1 + b = (a' + b) + 1 by omega]
    unfold checkBottom3BitHiRangeBool at h1 ⊢
    simp only [Bool.and_eq_true] at h1 ⊢
    refine ⟨h1.1, ih (s + 1) b h1.2 ?_⟩
    rwa [show s + 1 + a' = s + (a' + 1) by omega]

private theorem checkBottom3Bit_c0 : checkBottom3BitHiRangeBool 0 9 = true := by decide
private theorem checkBottom3Bit_c1 : checkBottom3BitHiRangeBool 9 9 = true := by decide
private theorem checkBottom3Bit_c2 : checkBottom3BitHiRangeBool 18 9 = true := by decide

private theorem checkBottom3BitHiRangeBool_get :
    ∀ (s cnt hi : Nat), checkBottom3BitHiRangeBool s cnt = true -> s ≤ hi -> hi < s + cnt ->
      checkBottom3BitLoLoopBool hi 27 = true
  | _, 0, _, _, _, hhi => by omega
  | s, cnt + 1, hi, h, hs, hhi => by
    unfold checkBottom3BitHiRangeBool at h
    simp only [Bool.and_eq_true] at h
    by_cases heq : hi = s
    · subst heq; exact h.1
    · exact checkBottom3BitHiRangeBool_get (s + 1) cnt hi h.2 (by omega) (by omega)

private theorem checkBottom3BitLoLoopBool_get (hi : Nat) :
    ∀ (k lo : Nat), checkBottom3BitLoLoopBool hi k = true -> lo < k ->
      checkBottom3BitHiLoBool hi lo = true
  | 0, _, _, hlo => by omega
  | k + 1, lo, h, hlo => by
    unfold checkBottom3BitLoLoopBool at h
    simp only [Bool.and_eq_true] at h
    by_cases heq : lo = k
    · subst heq; exact h.1
    · exact checkBottom3BitLoLoopBool_get hi k lo h.2 (by omega)

private theorem bottom3BitBucket177147_fin_spec (hi lo : Nat) (hhi : hi < 27) (hlo : lo < 27) :
    let q := 27 * hi + lo
    let b := bottom3BitBucket177147 q
    9 ≤ b.2.2 ∧ b.2.2 < b.2.1 ∧ b.2.1 < b.1 ∧ b.1 ≤ 176 ∧
    (2 ^ b.1 + 3 * 2 ^ b.2.1 + 9 * 2 ^ b.2.2) % 177147 = 2 ^ (162 * q) % 177147 := by
  have h01 := checkBottom3BitHiRangeBool_append 0 9 9 checkBottom3Bit_c0 checkBottom3Bit_c1
  have hall := checkBottom3BitHiRangeBool_append 0 18 9 h01 checkBottom3Bit_c2
  have hrow := checkBottom3BitHiRangeBool_get 0 27 hi hall (Nat.zero_le _) hhi
  have hcell := checkBottom3BitLoLoopBool_get hi 27 lo hrow hlo
  unfold checkBottom3BitHiLoBool at hcell
  dsimp only
  rcases hb : bottom3BitBucket177147 (27 * hi + lo) with ⟨b1, b2, b3⟩
  rw [hb] at hcell
  dsimp only at hcell ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcell
  rcases hcell with ⟨⟨⟨⟨hb3, hb32⟩, hb21⟩, hb1⟩, hmod⟩
  have hp17 : (2 : Nat) ^ 17 = 131072 := by decide
  rw [pow2ModFast_eq 17 (162 * (27 * hi + lo)) (by rw [hp17]; omega)] at hmod
  exact ⟨hb3, hb32, hb21, hb1, hmod⟩

private theorem bottom3BitBucket177147_mod_spec (k : Nat) (hk : k < 118098) :
    9 ≤ (bottom3BitBucket177147 (k / 162)).2.2 + k % 162 ∧
    (bottom3BitBucket177147 (k / 162)).2.2 + k % 162 <
      (bottom3BitBucket177147 (k / 162)).2.1 + k % 162 ∧
    (bottom3BitBucket177147 (k / 162)).2.1 + k % 162 <
      (bottom3BitBucket177147 (k / 162)).1 + k % 162 ∧
    (bottom3BitBucket177147 (k / 162)).1 + k % 162 ≤ 337 ∧
    (2 ^ ((bottom3BitBucket177147 (k / 162)).1 + k % 162) +
     3 * 2 ^ ((bottom3BitBucket177147 (k / 162)).2.1 + k % 162) +
     9 * 2 ^ ((bottom3BitBucket177147 (k / 162)).2.2 + k % 162)) % 177147 =
      2 ^ k % 177147 := by
  have hq_lt : k / 162 < 729 := by
    by_cases hlt : k / 162 < 729
    · exact hlt
    · exfalso
      have hge : 729 ≤ k / 162 := by omega
      have hm := Nat.mul_le_mul_left 162 hge
      have hc : 162 * 729 = 118098 := by decide
      have hd := Nat.mul_div_le k 162
      rw [hc] at hm
      exact Nat.not_le_of_gt hk (Nat.le_trans hm hd)
  have ht_lt : k % 162 < 162 := Nat.mod_lt k (by decide)
  have hhi : (k / 162) / 27 < 27 := by omega
  have hlo : (k / 162) % 27 < 27 := Nat.mod_lt (k / 162) (by decide)
  have hfin := bottom3BitBucket177147_fin_spec ((k / 162) / 27) ((k / 162) % 27) hhi hlo
  dsimp only at hfin
  rw [Nat.div_add_mod (k / 162) 27] at hfin
  rcases hb : bottom3BitBucket177147 (k / 162) with ⟨b1, b2, b3⟩
  rw [hb] at hfin
  dsimp only at hfin ⊢
  rcases hfin with ⟨hb3_9, hb32, hb21, hb1_176, hsum_b⟩
  clear hk hq_lt hhi hlo hb
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  have hmul_t : 2 ^ (b1 + k % 162) + 3 * 2 ^ (b2 + k % 162) + 9 * 2 ^ (b3 + k % 162) =
      (2 ^ b1 + 3 * 2 ^ b2 + 9 * 2 ^ b3) * 2 ^ (k % 162) := by
    rw [Nat.pow_add 2 b1 (k % 162), Nat.pow_add 2 b2 (k % 162), Nat.pow_add 2 b3 (k % 162),
        Nat.add_mul, Nat.add_mul, Nat.mul_assoc 3, Nat.mul_assoc 9]
  rw [hmul_t, Nat.mul_mod, hsum_b, ← Nat.mul_mod, ← Nat.pow_add 2 (162 * (k / 162)) (k % 162),
      Nat.div_add_mod k 162]

/-- Sub-`500` (`M_0 = 360 ≤ 500`, `17,714x` smaller than Wave 16's `6,377,332` and `72x` smaller
    than unary `26,265`!), steeper-slope (`c = 6 ≤ 6`) linear minimum dyadic window scale
    `dyadicExpWindowMinM17Low B = 360 + 6 * B`. -/
def dyadicExpWindowMinM17Low (B : Nat) : Nat :=
  360 + 6 * B

/-- Zero-run length list `[e3 - 9, e2 - (e3 + 1), e1 - (e2 + 1), e_fin - (e1 + 1)] ++ gaps`
    for `uWinExp17Low B M mask` (using 3-bit bottom collision lifting modulo `3 ^ 11 = 177147`). -/
def uWinExp17LowRuns (B M mask : Nat) : List Nat :=
  let k2 := (B + 1) / 2
  let w := 2 * k2 + 10
  let b0 := binBitLength (3 ^ w)
  let delta2 := 2 + dyadicPolyShiftDelta (b0 + 2)
  let a := b0 + delta2
  let q3 := (2 ^ (a + 1) - 1) / 3
  let L := M - delta2
  let chain := twoStepTernaryCarryChain k2 (L - 1) (q3 * 2 ^ (L - 1)) mask
  let e_fin := chain.1
  let R_fin := chain.2.1
  let gaps := chain.2.2
  let A_last := R_fin - (27 * 1085 + 7 * 3 ^ 9)
  let k_dlog := dlog2ModPow3 11 (A_last % 3 ^ 11)
  let b := bottom3BitBucket177147 (k_dlog / 162)
  let t := k_dlog % 162
  let e1 := b.1 + t
  let e2 := b.2.1 + t
  let e3 := b.2.2 + t
  (e3 - 9) :: (e2 - (e3 + 1)) :: (e1 - (e2 + 1)) :: (e_fin - (e1 + 1)) :: gaps

/-- Constructive sub-`500`-threshold (`M_0 = 360 ≤ 500`), steeper-slope (`c = 6 ≤ 6`) surviving
    `Mod373248` first-hit `q = 0` family `uWinExp17Low B M mask` inside `[2^M, 2^(M+1))` at linear
    length `L = M - delta2 ≤ M`. -/
def uWinExp17Low (B M mask : Nat) : List Bool :=
  minWeight6Prefix507 ++ zeroRunsSuffix (uWinExp17LowRuns B M mask)

private theorem bottom_3bit_collision_solve_w17 (R_fin L e_fin : Nat)
    (_hL : L ≥ 355) (he_fin : e_fin ≥ 349) (he_hi : e_fin ≤ L - 1)
    (hRfin_n3 : R_fin % 3 ≠ 0)
    (hRfin_lo : R_fin ≥ (2 * 3 ^ 8 - 1) * 2 ^ (L - 1)) :
    let A_last := R_fin - (27 * 1085 + 7 * 3 ^ 9)
    let k_dlog := dlog2ModPow3 11 (A_last % 3 ^ 11)
    let b := bottom3BitBucket177147 (k_dlog / 162)
    let t := k_dlog % 162
    ∃ (e1 e2 e3 m : Nat),
      e1 = b.1 + t ∧ e2 = b.2.1 + t ∧ e3 = b.2.2 + t ∧
      9 ≤ e3 ∧ e3 < e2 ∧ e2 < e1 ∧ e1 < e_fin ∧
      27 * 1085 + (2 ^ e1 + 3 * 2 ^ e2 + 9 * 2 ^ e3) < 2 ^ e_fin ∧
      R_fin = 3 ^ 9 * (9 * m + 7) + (27 * 1085 + (2 ^ e1 + 3 * 2 ^ e2 + 9 * 2 ^ e3)) := by
  dsimp only
  rcases (⟨27 * 1085 + 7 * 3 ^ 9, rfl⟩ : ∃ sc : Nat, sc = 27 * 1085 + 7 * 3 ^ 9) with ⟨sub_c, hsub_def⟩
  have h2L1_ge20 : 2 ^ (L - 1) ≥ 1048576 :=
    Nat.le_trans (by decide : 1048576 ≤ 2 ^ 20) (pow2_mono_nat (by omega))
  have hRfin_big : R_fin ≥ 13121 * 2 ^ (L - 1) := by
    have hc : 2 * 3 ^ 8 - 1 = 13121 := by decide
    exact hc ▸ hRfin_lo
  have hsub_lt_2L1 : sub_c < 2 ^ (L - 1) :=
    Nat.lt_of_lt_of_le (by rw [hsub_def]; decide) h2L1_ge20
  have hsub_lt_Rfin : sub_c < R_fin := by
    have h1 : 2 ^ (L - 1) ≤ R_fin :=
      Nat.le_trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 13121)) hRfin_big
    exact Nat.lt_of_lt_of_le hsub_lt_2L1 h1
  rcases (⟨R_fin - sub_c, rfl⟩ : ∃ al : Nat, al = R_fin - sub_c) with ⟨A_last, hA_eq_def⟩
  have hA_n3 : (A_last % 3 ^ 11) % 3 ≠ 0 := by
    have hAn3 : A_last % 3 ≠ 0 := by
      have hsub_3 : sub_c = 3 * 55692 := hsub_def.trans (by decide)
      have hrew : R_fin = A_last + 3 * 55692 := by
        rw [hA_eq_def, ← hsub_3, Nat.sub_add_cancel (Nat.le_of_lt hsub_lt_Rfin)]
      intro h0
      have hm0 : R_fin % 3 = 0 := by rw [hrew, Nat.add_mul_mod_self_left, h0]
      exact hRfin_n3 hm0
    have hdvd11 : 3 ∣ 3 ^ 11 := ⟨59049, by decide⟩
    rwa [Nat.mod_mod_of_dvd A_last hdvd11]
  rcases (⟨dlog2ModPow3 11 (A_last % 3 ^ 11), rfl⟩ :
      ∃ kd : Nat, kd = dlog2ModPow3 11 (A_last % 3 ^ 11)) with ⟨k_dlog, hk_def⟩
  rcases dlog2ModPow3_spec 11 (A_last % 3 ^ 11) (by decide) hA_n3 with
    ⟨hk_lt_raw, hk_mod_raw⟩
  rw [← hk_def] at hk_lt_raw hk_mod_raw
  have hk_lt : k_dlog < 118098 := by
    have hp : 2 * 3 ^ (11 - 1) = 118098 := by decide
    exact hp ▸ hk_lt_raw
  rcases bottom3BitBucket177147_mod_spec k_dlog hk_lt with
    ⟨he3_9, he32, he21, he1_337, h3bit_mod⟩
  rcases hb : bottom3BitBucket177147 (k_dlog / 162) with ⟨b1, b2, b3⟩
  rw [hb] at he3_9 he32 he21 he1_337 h3bit_mod
  dsimp only at he3_9 he32 he21 he1_337 h3bit_mod
  rcases (⟨b1 + k_dlog % 162, rfl⟩ : ∃ v : Nat, v = b1 + k_dlog % 162) with ⟨e1, he1_def⟩
  rcases (⟨b2 + k_dlog % 162, rfl⟩ : ∃ v : Nat, v = b2 + k_dlog % 162) with ⟨e2, he2_def⟩
  rcases (⟨b3 + k_dlog % 162, rfl⟩ : ∃ v : Nat, v = b3 + k_dlog % 162) with ⟨e3, he3_def⟩
  rw [← he1_def] at he21 he1_337 h3bit_mod
  rw [← he2_def] at he32 he21 h3bit_mod
  rw [← he3_def] at he3_9 he32 h3bit_mod
  rcases (⟨2 ^ e1 + 3 * 2 ^ e2 + 9 * 2 ^ e3, rfl⟩ :
      ∃ s3 : Nat, s3 = 2 ^ e1 + 3 * 2 ^ e2 + 9 * 2 ^ e3) with ⟨S3, hS3_def⟩
  rw [← hS3_def] at h3bit_mod
  have hS3_mod : S3 % 177147 = A_last % 177147 := by
    have h311_val : (3 : Nat) ^ 11 = 177147 := by decide
    rw [h311_val, Nat.mod_mod] at hk_mod_raw
    exact h3bit_mod.trans hk_mod_raw
  rcases (⟨e_fin - 4, rfl⟩ : ∃ n0 : Nat, n0 = e_fin - 4) with ⟨n0, hn0_def⟩
  have hn0_ge345 : n0 ≥ 345 := by
    clear hsub_def h2L1_ge20 hRfin_big hRfin_lo hsub_lt_2L1 hsub_lt_Rfin hA_eq_def hA_n3
    clear hk_def hk_lt_raw hk_mod_raw hk_lt hb he1_def he2_def he3_def hS3_def h3bit_mod hS3_mod
    omega
  have he1_lt_efin : e1 < e_fin := by
    clear hsub_def h2L1_ge20 hRfin_big hRfin_lo hsub_lt_2L1 hsub_lt_Rfin hA_eq_def hA_n3
    clear hk_def hk_lt_raw hk_mod_raw hk_lt hb he1_def he2_def he3_def hS3_def h3bit_mod hS3_mod hn0_def
    omega
  have hS3_lt_efin : 27 * 1085 + S3 < 2 ^ e_fin := by
    have hc29 : 27 * 1085 < 2 ^ n0 :=
      Nat.lt_of_lt_of_le (by decide : 27 * 1085 < 2 ^ 15)
        (pow2_mono_nat (Nat.le_trans (by decide : 15 ≤ 345) hn0_ge345))
    have he1_n0 : e1 ≤ n0 := Nat.le_trans he1_337 (Nat.le_trans (by decide : 337 ≤ 345) hn0_ge345)
    have hp1 : 2 ^ e1 ≤ 2 ^ n0 := pow2_mono_nat he1_n0
    have hp2 : 2 ^ e2 ≤ 2 ^ n0 := pow2_mono_nat (Nat.le_trans (Nat.le_of_lt he21) he1_n0)
    have hp3 : 2 ^ e3 ≤ 2 ^ n0 :=
      pow2_mono_nat (Nat.le_trans (Nat.le_of_lt he32) (Nat.le_trans (Nat.le_of_lt he21) he1_n0))
    have hpef : 2 ^ e_fin = 16 * 2 ^ n0 := by
      have hef4 : e_fin = 4 + n0 := by
        clear hsub_def h2L1_ge20 hRfin_big hRfin_lo hsub_lt_2L1 hsub_lt_Rfin hA_eq_def hA_n3
        clear hk_def hk_lt_raw hk_mod_raw hk_lt hb he1_def he2_def he3_def hS3_def h3bit_mod hS3_mod
        clear hc29 hp1 hp2 hp3
        omega
      rw [hef4, Nat.pow_add 2 4 n0, show (2 : Nat) ^ 4 = 16 from rfl]
    rw [hS3_def, hpef]
    clear hsub_def h2L1_ge20 hRfin_big hRfin_lo hsub_lt_2L1 hsub_lt_Rfin hA_eq_def hA_n3
    clear hk_def hk_lt_raw hk_mod_raw hk_lt hb he1_def he2_def he3_def hS3_def h3bit_mod hS3_mod
    clear hn0_def hpef
    generalize 27 * 1085 = C29, 2 ^ n0 = ZN, 2 ^ e1 = Z1, 2 ^ e2 = Z2, 2 ^ e3 = Z3 at hc29 hp1 hp2 hp3 ⊢
    omega
  have hS3_lt_A : S3 < A_last := by
    have hs1 : S3 < 2 ^ (L - 1) :=
      Nat.lt_of_lt_of_le
        (Nat.lt_of_le_of_lt (Nat.le_add_left S3 (27 * 1085)) hS3_lt_efin)
        (pow2_mono_nat he_hi)
    have h2_le : 2 * 2 ^ (L - 1) ≤ R_fin :=
      Nat.le_trans (Nat.mul_le_mul_right _ (by decide : 2 ≤ 13121)) hRfin_big
    rw [hA_eq_def]
    clear hsub_def h2L1_ge20 hRfin_big hRfin_lo hk_def hk_lt_raw hk_mod_raw hk_lt hb
    clear he1_def he2_def he3_def hS3_def h3bit_mod hS3_mod hn0_def hS3_lt_efin hA_n3
    generalize 2 ^ (L - 1) = Z2L, sub_c = ZSC, S3 = ZS, R_fin = ZR at hs1 hsub_lt_2L1 h2_le hsub_lt_Rfin ⊢
    omega
  have hdiff_mod : (A_last - S3) % 177147 = 0 :=
    sub_mod_eq_zero_of_mod_eq_w17 177147 A_last S3 (by decide) (Nat.le_of_lt hS3_lt_A) hS3_mod
  rcases Nat.dvd_of_mod_eq_zero hdiff_mod with ⟨m, hm_eq⟩
  have hA_rec : A_last = 177147 * m + S3 := by
    rw [← hm_eq, Nat.sub_add_cancel (Nat.le_of_lt hS3_lt_A)]
  have hR_eq_m : R_fin = 3 ^ 9 * (9 * m + 7) + (27 * 1085 + S3) := by
    have hR_sub : R_fin = A_last + sub_c := by
      rw [hA_eq_def, Nat.sub_add_cancel (Nat.le_of_lt hsub_lt_Rfin)]
    have hQ1_exp : 3 ^ 9 * (9 * m + 7) = 177147 * m + 137781 := by
      rw [Nat.mul_add, ← Nat.mul_assoc,
          show 3 ^ 9 * 9 = 177147 by decide,
          show 3 ^ 9 * 7 = 137781 by decide]
    have hconst : sub_c = 137781 + 27 * 1085 := hsub_def.trans (by decide)
    rw [hR_sub, hA_rec, hQ1_exp, hconst]
    clear hsub_def h2L1_ge20 hRfin_big hRfin_lo hsub_lt_2L1 hsub_lt_Rfin hA_eq_def hA_n3
    clear hk_def hk_lt_raw hk_mod_raw hk_lt hb he1_def he2_def he3_def hS3_def h3bit_mod hS3_mod
    clear hn0_def hS3_lt_efin hS3_lt_A hdiff_mod hm_eq hA_rec hR_sub hQ1_exp hconst
    generalize 177147 * m = ZM, (137781 : Nat) = ZD, 27 * 1085 = ZC, S3 = ZS
    omega
  rw [hS3_def] at hS3_lt_efin hR_eq_m
  refine ⟨e1, e2, e3, m, ?_, ?_, ?_, he3_9, he32, he21, he1_lt_efin, hS3_lt_efin, hR_eq_m⟩
  · rw [← hsub_def, ← hA_eq_def, ← hk_def, hb]; exact he1_def
  · rw [← hsub_def, ← hA_eq_def, ← hk_def, hb]; exact he2_def
  · rw [← hsub_def, ← hA_eq_def, ← hk_def, hb]; exact he3_def

private theorem four_step_bottom_runs_spec_w17
    (e3 e2 e1 e_fin : Nat)
    (he3 : 9 ≤ e3) (he32 : e3 < e2) (he21 : e2 < e1) (he1f : e1 < e_fin) :
    ∃ u_acc : List Bool,
      u_acc = minWeight6Prefix507 ++
        zeroRunsSuffix [e3 - 9, e2 - (e3 + 1), e1 - (e2 + 1), e_fin - (e1 + 1)] ∧
      u_acc.length = e_fin + 1 ∧
      parityWeight u_acc = 10 ∧
      affineCarry u_acc = 3 * (27 * 1085 + (2 ^ e1 + 3 * 2 ^ e2 + 9 * 2 ^ e3)) + 2 ^ e_fin := by
  let u0 := minWeight6Prefix507
  let u_b3 := (u0 ++ List.replicate (e3 - 9) false) ++ [true]
  let u_b2 := (u_b3 ++ List.replicate (e2 - (e3 + 1)) false) ++ [true]
  let u_b1 := (u_b2 ++ List.replicate (e1 - (e2 + 1)) false) ++ [true]
  let u_acc := (u_b1 ++ List.replicate (e_fin - (e1 + 1)) false) ++ [true]
  have hu0_car : affineCarry u0 = 1085 := by decide
  have hc1_t : affineCarry [true] = 1 := rfl
  have hw1_t : parityWeight [true] = 1 := rfl
  rcases affineCarry_append_replicate_false u0 (e3 - 9) with ⟨hwt_z3, hcar_z3⟩
  have hlen_z3 : (u0 ++ List.replicate (e3 - 9) false).length = e3 := by
    rw [List.length_append, show u0.length = 9 from rfl, List.length_replicate]; omega
  have hlen_b3 : u_b3.length = e3 + 1 := by
    dsimp [u_b3]; rw [List.length_append, hlen_z3, List.length_singleton]
  have hwt_b3 : parityWeight u_b3 = 7 := by
    dsimp [u_b3]; rw [parityWeight_append, hwt_z3]; rfl
  have hcar_b3 : affineCarry u_b3 = 3 * 1085 + 2 ^ e3 := by
    dsimp [u_b3]; rw [affineCarry_append, hcar_z3, hu0_car, hlen_z3, hc1_t, hw1_t]; omega
  rcases affineCarry_append_replicate_false u_b3 (e2 - (e3 + 1)) with ⟨hwt_z2, hcar_z2⟩
  have hlen_z2 : (u_b3 ++ List.replicate (e2 - (e3 + 1)) false).length = e2 := by
    rw [List.length_append, hlen_b3, List.length_replicate]; omega
  have hlen_b2 : u_b2.length = e2 + 1 := by
    dsimp [u_b2]; rw [List.length_append, hlen_z2, List.length_singleton]
  have hwt_b2 : parityWeight u_b2 = 8 := by
    dsimp [u_b2]; rw [parityWeight_append, hwt_z2, hwt_b3]; rfl
  have hcar_b2 : affineCarry u_b2 = 9 * 1085 + 3 * 2 ^ e3 + 2 ^ e2 := by
    dsimp [u_b2]; rw [affineCarry_append, hcar_z2, hcar_b3, hlen_z2, hc1_t, hw1_t]; omega
  rcases affineCarry_append_replicate_false u_b2 (e1 - (e2 + 1)) with ⟨hwt_z1, hcar_z1⟩
  have hlen_z1 : (u_b2 ++ List.replicate (e1 - (e2 + 1)) false).length = e1 := by
    rw [List.length_append, hlen_b2, List.length_replicate]; omega
  have hlen_b1 : u_b1.length = e1 + 1 := by
    dsimp [u_b1]; rw [List.length_append, hlen_z1, List.length_singleton]
  have hwt_b1 : parityWeight u_b1 = 9 := by
    dsimp [u_b1]; rw [parityWeight_append, hwt_z1, hwt_b2]; rfl
  have hcar_b1 : affineCarry u_b1 = 27 * 1085 + (2 ^ e1 + 3 * 2 ^ e2 + 9 * 2 ^ e3) := by
    dsimp [u_b1]; rw [affineCarry_append, hcar_z1, hcar_b2, hlen_z1, hc1_t, hw1_t]; omega
  rcases affineCarry_append_replicate_false u_b1 (e_fin - (e1 + 1)) with ⟨hwt_z0, hcar_z0⟩
  have hlen_z0 : (u_b1 ++ List.replicate (e_fin - (e1 + 1)) false).length = e_fin := by
    rw [List.length_append, hlen_b1, List.length_replicate]; omega
  have hlen_acc : u_acc.length = e_fin + 1 := by
    dsimp [u_acc]; rw [List.length_append, hlen_z0, List.length_singleton]
  have hwt_acc : parityWeight u_acc = 10 := by
    dsimp [u_acc]; rw [parityWeight_append, hwt_z0, hwt_b1]; rfl
  have hcar_acc : affineCarry u_acc = 3 * affineCarry u_b1 + 2 ^ e_fin := by
    dsimp [u_acc]; rw [affineCarry_append, hcar_z0, hlen_z0, hc1_t, hw1_t, Nat.pow_one]
    generalize affineCarry u_b1 = CB1, 2 ^ e_fin = ZE; omega
  rw [hcar_b1] at hcar_acc
  have hu_eq : u_acc = minWeight6Prefix507 ++
      zeroRunsSuffix [e3 - 9, e2 - (e3 + 1), e1 - (e2 + 1), e_fin - (e1 + 1)] := by
    dsimp only [zeroRunsSuffix, u_acc, u_b1, u_b2, u_b3, u0]
    simp [List.append_assoc]
  exact ⟨u_acc, hu_eq, hlen_acc, hwt_acc, hcar_acc⟩

private theorem uWinExp17Low_per_mask_core_and_key_w17
    (B M mask : Nat) (hB : B ≥ 1) (hM : M ≥ dyadicExpWindowMinM17Low B)
    (_hmask : mask < 2 ^ B) :
    let k2 := (B + 1) / 2
    let w := 2 * k2 + 10
    let b0 := binBitLength (3 ^ w)
    let delta2 := 2 + dyadicPolyShiftDelta (b0 + 2)
    let a := b0 + delta2
    let u_e := uWinExp17Low B M mask
    IsCoreParityWord u_e ∧
    u_e.length = M - delta2 ∧
    parityWeight u_e = w ∧
    canonicalSuffixShift u_e 1 = a ∧
    IsFirstHitOnePair u_e 0 ∧
    affineCarry u_e ≥ 1 ∧
    affineCarry u_e < 2 ^ M ∧
    (∃ mid : List Bool, u_e = minWeight6Prefix507 ++ mid ++ [true]) ∧
    (∃ m : Nat, 2 ^ (u_e.length + a) = 3 ^ w * (9 * m + 7) + affineCarry u_e) := by
  dsimp only
  rcases (⟨(B + 1) / 2, rfl⟩ : ∃ v : Nat, v = (B + 1) / 2) with ⟨k2, hk2_def⟩
  rcases (⟨2 * k2 + 10, rfl⟩ : ∃ v : Nat, v = 2 * k2 + 10) with ⟨w, hw_eq⟩
  rcases (⟨binBitLength (3 ^ w), rfl⟩ : ∃ v : Nat, v = binBitLength (3 ^ w)) with ⟨b0, hb0_def⟩
  rcases (⟨2 + dyadicPolyShiftDelta (b0 + 2), rfl⟩ :
      ∃ v : Nat, v = 2 + dyadicPolyShiftDelta (b0 + 2)) with ⟨delta2, hd2_def⟩
  rcases (⟨b0 + delta2, rfl⟩ : ∃ v : Nat, v = b0 + delta2) with ⟨a, ha_eq⟩
  rcases (⟨(2 ^ (a + 1) - 1) / 3, rfl⟩ : ∃ v : Nat, v = (2 ^ (a + 1) - 1) / 3) with ⟨q3, hq3_def⟩
  rcases (⟨M - delta2, rfl⟩ : ∃ v : Nat, v = M - delta2) with ⟨L, hL_eq⟩
  have hk2_ge1 : k2 ≥ 1 := by rw [hk2_def]; omega
  have h11k2_le : 11 * k2 ≤ 6 * B + 5 := by rw [hk2_def]; omega
  have hw_ge12 : w ≥ 12 := by rw [hw_eq]; omega
  rcases pow3_bitlength_strict_bounds_w17 w (by omega) with ⟨hb0_ge16, hb0_le2w, h3w_lo, _⟩
  rw [← hb0_def] at hb0_ge16 hb0_le2w h3w_lo
  rcases dyadicPolyShiftDelta2_spec_w17 b0 with ⟨hd2_lo, hd2_hi, h3q3, hq3_n3, _⟩
  rw [← hd2_def] at hd2_lo hd2_hi h3q3 hq3_n3
  rw [← ha_eq] at h3q3 hq3_n3
  rw [← hq3_def] at h3q3 hq3_n3
  have hM_def : M ≥ 360 + 6 * B := hM
  have hL_ge : L ≥ 355 + 6 * B := by rw [hL_eq]; omega
  have ha_lt_P : a < 2 * 3 ^ (w - 1) := by
    have ha_le : a ≤ 2 * w + 5 := by rw [ha_eq]; omega
    have hw1_gt : 3 ^ (w - 1) > 2 * (w - 1) := pow3_gt_two_mul_w17 (w - 1)
    have hp4 : 3 ^ (w - 1) ≥ 81 := by
      have h := nat_pow_mono_exp_pos 3 4 (w - 1) (by decide) (by omega)
      have h81 : (3 : Nat) ^ 4 = 81 := by decide
      rwa [h81] at h
    generalize 3 ^ (w - 1) = PW1 at hw1_gt hp4 ⊢
    omega
  rcases (⟨q3 * 2 ^ (L - 1), rfl⟩ : ∃ v : Nat, v = q3 * 2 ^ (L - 1)) with ⟨R0, hR0_def⟩
  have hR0_n3 : R0 % 3 ≠ 0 := by
    intro h0
    rw [hR0_def, Nat.mul_mod] at h0
    have hp2_n3 := pow2_mod3_nonzero_w5 (L - 1)
    have hq3_lt : q3 % 3 < 3 := Nat.mod_lt q3 (by decide)
    have hp2_lt : 2 ^ (L - 1) % 3 < 3 := Nat.mod_lt _ (by decide)
    rcases (by omega : q3 % 3 = 1 ∨ q3 % 3 = 2) with hq | hq <;>
    rcases (by omega : 2 ^ (L - 1) % 3 = 1 ∨ 2 ^ (L - 1) % 3 = 2) with hp | hp <;>
    (rw [hq, hp] at h0; cases h0)
  have hq3_ge_pow3 : q3 ≥ 2 * 3 ^ (2 * k2 + 8) - 1 := by
    have ha1_ge8 : 2 ^ (a + 1) ≥ 8 * 2 ^ b0 := by
      have h : 2 ^ (3 + b0) ≤ 2 ^ (a + 1) := pow2_mono_nat (by rw [ha_eq]; omega)
      rwa [Nat.pow_add 2 3 b0] at h
    have hp3_le : 3 ^ (2 * k2 + 8) ≤ 3 ^ w :=
      nat_pow_mono_exp_pos 3 (2 * k2 + 8) w (by decide) (by rw [hw_eq]; omega)
    have hge8 : 3 * q3 + 1 ≥ 8 * (3 ^ (2 * k2 + 8) + 1) := by
      rw [h3q3]
      exact Nat.le_trans (Nat.mul_le_mul_left 8 (Nat.add_le_add_right hp3_le 1))
        (Nat.le_trans (Nat.mul_le_mul_left 8 h3w_lo) ha1_ge8)
    generalize 3 ^ (2 * k2 + 8) = P3 at hge8 ⊢
    omega
  have hR0_lo : R0 ≥ (2 * 3 ^ (2 * k2 + 8) - 1) * 2 ^ (L - 1) := by
    rw [hR0_def]; exact Nat.mul_le_mul_right _ hq3_ge_pow3
  rcases (twoStepTernaryCarryChain_spec_and_inj_w17 k2 (L - 1) R0 (L - 1)
    (Nat.le_refl _) (by omega) hR0_n3 hR0_lo).1 mask with
    ⟨he_lo, he_hi, hlen_gaps, hRfin_n3, hRfin_lo, hunwind⟩
  rcases hch : twoStepTernaryCarryChain k2 (L - 1) R0 mask with ⟨e_fin, R_fin, gaps⟩
  rw [hch] at he_lo he_hi hlen_gaps hRfin_n3 hRfin_lo hunwind
  dsimp only at he_lo he_hi hlen_gaps hRfin_n3 hRfin_lo hunwind
  have he_fin_ge : e_fin ≥ 349 := by
    clear hk2_def hb0_def hd2_def hq3_def hR0_def hch hR0_lo hRfin_lo hunwind
    omega
  rcases bottom_3bit_collision_solve_w17 R_fin L e_fin (by omega) he_fin_ge he_hi hRfin_n3 hRfin_lo with
    ⟨e1, e2, e3, m, he1_def, he2_def, he3_def, he3_9, he32, he21, he1_lt_efin, hS3_lt_efin, hRfin_Q1⟩
  rcases (⟨27 * 1085 + (2 ^ e1 + 3 * 2 ^ e2 + 9 * 2 ^ e3), rfl⟩ :
      ∃ v : Nat, v = 27 * 1085 + (2 ^ e1 + 3 * 2 ^ e2 + 9 * 2 ^ e3)) with ⟨B1_car, hB1_def⟩
  rw [← hB1_def] at hS3_lt_efin hRfin_Q1
  rcases (⟨3 ^ 9 * (9 * m + 7), rfl⟩ : ∃ v : Nat, v = 3 ^ 9 * (9 * m + 7)) with ⟨Q1, hQ1_def⟩
  rw [← hQ1_def] at hRfin_Q1
  rcases four_step_bottom_runs_spec_w17 e3 e2 e1 e_fin he3_9 he32 he21 he1_lt_efin with
    ⟨u_acc, hu_acc_eq, hlen_acc, hwt_acc, hcar_acc⟩
  rw [← hB1_def] at hcar_acc
  have hcar_acc_lt : affineCarry u_acc < 6 * 2 ^ e_fin := by
    rw [hcar_acc]
    clear hk2_def hb0_def hd2_def hq3_def hR0_def hch he1_def he2_def he3_def hB1_def hQ1_def
    clear hu_acc_eq hR0_lo hRfin_lo hunwind
    generalize B1_car = CB1, 2 ^ e_fin = ZE at hS3_lt_efin ⊢
    omega
  have hacc_base_eq : 3 * R_fin + 2 ^ e_fin = 3 * Q1 + affineCarry u_acc := by
    rw [hRfin_Q1, hcar_acc, Nat.mul_add, Nat.add_assoc]
  rcases hunwind u_acc Q1 hlen_acc hcar_acc_lt hacc_base_eq with
    ⟨hw_len, hw_wt, hw_car, hw_key⟩
  rcases (⟨uWinExp17Low B M mask, rfl⟩ : ∃ u_x : List Bool, u_x = uWinExp17Low B M mask) with
    ⟨u_e, hue_def⟩
  have hue_runs : u_e = minWeight6Prefix507 ++
      zeroRunsSuffix ((e3 - 9) :: (e2 - (e3 + 1)) :: (e1 - (e2 + 1)) :: (e_fin - (e1 + 1)) :: gaps) := by
    rw [hue_def]
    unfold uWinExp17Low uWinExp17LowRuns
    dsimp only
    rw [← hk2_def, ← hw_eq, ← hb0_def, ← hd2_def, ← ha_eq, ← hq3_def, ← hL_eq, ← hR0_def, hch]
    dsimp only
    rw [← he3_def, ← he2_def, ← he1_def]
  have hue_wout : u_e = u_acc ++ zeroRunsSuffix gaps := by
    have hr_split :
        (e3 - 9) :: (e2 - (e3 + 1)) :: (e1 - (e2 + 1)) :: (e_fin - (e1 + 1)) :: gaps =
        [e3 - 9, e2 - (e3 + 1), e1 - (e2 + 1), e_fin - (e1 + 1)] ++ gaps := rfl
    rw [hue_runs, hr_split, zeroRunsSuffix_append_and_inj_w17.1
      [e3 - 9, e2 - (e3 + 1), e1 - (e2 + 1), e_fin - (e1 + 1)] gaps,
      ← List.append_assoc, ← hu_acc_eq]
  rw [← hue_wout] at hw_len hw_wt hw_car hw_key
  have hlen_final : u_e.length = L := by
    rw [hw_len]
    clear hk2_def hb0_def hd2_def hq3_def hR0_def hch he1_def he2_def he3_def hB1_def hQ1_def
    clear hu_acc_eq hue_def hue_runs hue_wout hunwind
    omega
  have hwt_final : parityWeight u_e = w := by
    rw [hw_wt, hwt_acc, hw_eq]
    clear hk2_def hb0_def hd2_def hq3_def hR0_def hch he1_def he2_def he3_def hB1_def hQ1_def
    clear hu_acc_eq hue_def hue_runs hue_wout hunwind
    omega
  have hcar_lt_M : affineCarry u_e < 2 ^ M := by
    have h8 : affineCarry u_e < 8 * 2 ^ (L - 1) := by
      clear hk2_def hb0_def hd2_def hq3_def hR0_def hch he1_def he2_def he3_def hB1_def hQ1_def
      clear hu_acc_eq hue_def hue_runs hue_wout hunwind
      omega
    have hp8 : 8 * 2 ^ (L - 1) = 2 ^ (L + 2) := by
      rw [show (8 : Nat) = 2 ^ 3 from rfl, ← Nat.pow_add 2 3 (L - 1),
          show 3 + (L - 1) = L + 2 by omega]
    rw [hp8] at h8
    exact Nat.lt_of_lt_of_le h8 (pow2_mono_nat (by rw [hL_eq]; omega))
  have hkey_final : 2 ^ (u_e.length + a) = 3 ^ w * (9 * m + 7) + affineCarry u_e := by
    have hlhs : 2 ^ (L + a) = 3 * R0 + 2 ^ (L - 1) := by
      rw [hR0_def, show L + a = (a + 1) + (L - 1) by omega, Nat.pow_add 2 (a + 1) (L - 1),
          ← h3q3, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
    have hrhs : 3 ^ (2 * k2 + 1) * Q1 = 3 ^ w * (9 * m + 7) := by
      rw [hQ1_def, ← Nat.mul_assoc, ← Nat.pow_add 3 (2 * k2 + 1) 9,
          show (2 * k2 + 1) + 9 = w by rw [hw_eq]]
    rw [hlen_final, hlhs, hw_key, hrhs]
  have hmid_ex : ∃ mid : List Bool, u_e = minWeight6Prefix507 ++ mid ++ [true] := by
    rcases zeroRunsSuffix_nonempty_eq_mid_true_w17 (e3 - 9)
      ((e2 - (e3 + 1)) :: (e1 - (e2 + 1)) :: (e_fin - (e1 + 1)) :: gaps) with ⟨mid, hmid⟩
    exact ⟨mid, by rw [hue_runs, hmid, List.append_assoc]⟩
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
      rcases zeroRunsSuffix_nonempty_eq_mid_true_w17 g0 gtl with ⟨m_g, hmg⟩
      rw [hmg, ← List.append_assoc u_acc m_g [true], affineCarry_append]
      have hc1_t : affineCarry [true] = 1 := rfl
      rw [hc1_t, Nat.mul_one]
      have hp := pow2_pos_nat (u_acc ++ m_g).length
      clear hk2_def hb0_def hd2_def hq3_def hR0_def hch he1_def he2_def he3_def hB1_def hQ1_def
      clear hu_acc_eq hue_def hue_runs hue_wout hunwind
      omega
  rw [← hk2_def, ← hw_eq, ← hb0_def, ← hd2_def, ← ha_eq, ← hL_eq, ← hue_def]
  exact ⟨hcore_u, hlen_final, hwt_final, hsh_a, hfh, hcar_pos, hcar_lt_M, hmid_ex, ⟨m, hkey_final⟩⟩

private theorem uWinExp17Low_per_mask_leaf_spec_w17
    (B M mask : Nat) (hB : B ≥ 1) (hM : M ≥ dyadicExpWindowMinM17Low B)
    (hmask : mask < 2 ^ B) :
    let k2 := (B + 1) / 2
    let w := 2 * k2 + 10
    let b0 := binBitLength (3 ^ w)
    let delta2 := 2 + dyadicPolyShiftDelta (b0 + 2)
    let u := uWinExp17Low B M mask
    let y := exactBackwardQuotient 1 u 0
    IsFirstHitOnePair u 0 ∧
    u.length = M - delta2 ∧
    u.length ≤ M ∧
    parityWeight u = w ∧
    canonicalSuffixShift u 1 = b0 + delta2 ∧
    y % 512 = 507 ∧
    y % 9 = 7 ∧
    isSurvivingMod373248Bool y = true ∧
    IsSurvivingMod373248Class y ∧
    2 ^ M ≤ y ∧ y < 2 ^ (M + 1) ∧
    (∀ L_max : Nat, L_max ≥ M -> y ∈ dyadicWindowSurvivingQ0Leaves L_max M) := by
  dsimp only
  let k2 := (B + 1) / 2
  let w := 2 * k2 + 10
  let b0 := binBitLength (3 ^ w)
  let delta2 := 2 + dyadicPolyShiftDelta (b0 + 2)
  let a := b0 + delta2
  have hk2_ge1 : k2 ≥ 1 := by dsimp [k2]; omega
  have hw_eq : w = 2 * k2 + 10 := rfl
  have ha_eq : a = b0 + delta2 := rfl
  rcases pow3_bitlength_strict_bounds_w17 w (by rw [hw_eq]; omega) with ⟨_, _, h3w_lo, h2b0_hi⟩
  change 3 ^ w + 1 ≤ 2 ^ b0 at h3w_lo
  change 2 ^ b0 < 2 * 3 ^ w at h2b0_hi
  rcases dyadicPolyShiftDelta2_spec_w17 b0 with ⟨_, hd2_hi, _, _, _⟩
  change delta2 ≤ 5 at hd2_hi
  have hM_ge30 : M ≥ 30 := by unfold dyadicExpWindowMinM17Low at hM; omega
  rcases uWinExp17Low_per_mask_core_and_key_w17 B M mask hB hM hmask with
    ⟨hcore_r, hlen_r, hwt_r, hsh_r, hfh_r, hcar_pos_r, hcar_lt_r, ⟨mid, hu_mid_r⟩, ⟨m, hkey_r⟩⟩
  rcases (⟨uWinExp17Low B M mask, rfl⟩ : ∃ u0 : List Bool, u0 = uWinExp17Low B M mask) with
    ⟨u_e, hue_def⟩
  rw [← hue_def] at hcore_r hlen_r hwt_r hsh_r hfh_r hcar_pos_r hcar_lt_r hu_mid_r hkey_r
  change u_e.length = M - delta2 at hlen_r
  change parityWeight u_e = w at hwt_r
  change canonicalSuffixShift u_e 1 = a at hsh_r
  change 2 ^ (u_e.length + a) = 3 ^ w * (9 * m + 7) + affineCarry u_e at hkey_r
  rcases (⟨exactBackwardQuotient 1 u_e 0, rfl⟩ :
      ∃ y0 : Nat, y0 = exactBackwardQuotient 1 u_e 0) with ⟨y, hy_def⟩
  have hy_9m7 : y = 9 * m + 7 := by
    rcases one_generator_pos_odd_and_reaches_one u_e 0 hcore_r with ⟨_, _, heq_bw, _⟩
    have hbw_steps : backwardOneTotalSteps u_e 0 = u_e.length + a := by
      unfold backwardOneTotalSteps; rw [hsh_r]; omega
    rw [hbw_steps, hwt_r, ← hy_def] at heq_bw
    have hcomb : 3 ^ w * y = 3 ^ w * (9 * m + 7) :=
      Nat.add_right_cancel (heq_bw.symm.trans hkey_r)
    exact Nat.eq_of_mul_eq_mul_left (pow3_pos_nat w) hcomb
  have hy_m9 : y % 9 = 7 := by rw [hy_9m7]; omega
  have hy_m512 : y % 512 = 507 := by
    have hp9_507 : parityOfIter 9 507 = minWeight6Prefix507 := by decide
    have hu_507 : u_e = parityOfIter 9 507 ++ mid ++ [true] := by rw [hp9_507]; exact hu_mid_r
    have hm := (surviving_mod512_nine_prefix_auto_weight_and_characterization.1 507
      (by decide) (by decide)).2.2.2 mid 0 |>.2.2.1
    rwa [← hu_507, ← hy_def] at hm
  rcases isSurvivingMod373248_of_507_and_mod9_eq7_w17 y hy_m512 hy_m9 with ⟨hb_surv, hcls_surv⟩
  have hy_win : 2 ^ M ≤ y ∧ y < 2 ^ (M + 1) := by
    have hLa_eq : u_e.length + a = b0 + M := by rw [hlen_r, ha_eq]; omega
    have heq_y : 3 ^ w * y + affineCarry u_e = 2 ^ b0 * 2 ^ M := by
      have hk := hkey_r.symm
      rwa [← hy_9m7, hLa_eq, Nat.pow_add 2 b0 M] at hk
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
         hy_m512, hy_m9, hb_surv, hcls_surv, hy_win.1, hy_win.2, hy_mem_win⟩

private theorem uWinExp17Low_inj_mask_w17
    (B M m1 m2 : Nat) (hB : B ≥ 1) (hM : M ≥ dyadicExpWindowMinM17Low B)
    (hm1 : m1 < 2 ^ B) (hm2 : m2 < 2 ^ B)
    (hy_eq : exactBackwardQuotient 1 (uWinExp17Low B M m1) 0 =
      exactBackwardQuotient 1 (uWinExp17Low B M m2) 0) :
    m1 = m2 := by
  have hfh1 := (uWinExp17Low_per_mask_core_and_key_w17 B M m1 hB hM hm1).2.2.2.2.1
  have hfh2 := (uWinExp17Low_per_mask_core_and_key_w17 B M m2 hB hM hm2).2.2.2.2.1
  have hu_eq : uWinExp17Low B M m1 = uWinExp17Low B M m2 :=
    (first_hit_one_pair_sound_and_injective _ _ 0 0 hfh1 hfh2).2.2.2 hy_eq |>.1
  unfold uWinExp17Low at hu_eq
  have hzs_eq := (list_append_inj_left_eq_len _ _ _ _ rfl hu_eq).2
  have hruns_eq := zeroRunsSuffix_append_and_inj_w17.2 _ _ hzs_eq
  unfold uWinExp17LowRuns at hruns_eq
  dsimp only at hruns_eq
  have hgaps_eq := (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj hruns_eq).2).2).2).2
  let k2 := (B + 1) / 2
  let w := 2 * k2 + 10
  let b0 := binBitLength (3 ^ w)
  let delta2 := 2 + dyadicPolyShiftDelta (b0 + 2)
  let a := b0 + delta2
  let q3 := (2 ^ (a + 1) - 1) / 3
  let L := M - delta2
  have hk2_ge1 : k2 ≥ 1 := by dsimp [k2]; omega
  have h11k2_le : 11 * k2 ≤ 6 * B + 5 := by dsimp [k2]; omega
  rcases pow3_bitlength_strict_bounds_w17 w (by dsimp [w]; omega) with ⟨_, _, h3w_lo, _⟩
  change 3 ^ w + 1 ≤ 2 ^ b0 at h3w_lo
  rcases dyadicPolyShiftDelta2_spec_w17 b0 with ⟨hd2_lo, hd2_hi, h3q3, hq3_n3, _⟩
  change 2 ≤ delta2 at hd2_lo
  change delta2 ≤ 5 at hd2_hi
  change 3 * q3 + 1 = 2 ^ (a + 1) at h3q3
  change q3 % 3 ≠ 0 at hq3_n3
  have hL_ge : L ≥ 355 + 6 * B := by dsimp [L]; unfold dyadicExpWindowMinM17Low at hM; omega
  have hR0_n3 : (q3 * 2 ^ (L - 1)) % 3 ≠ 0 := by
    intro h0; rw [Nat.mul_mod] at h0
    have hp2_n3 := pow2_mod3_nonzero_w5 (L - 1)
    have hq3_lt : q3 % 3 < 3 := Nat.mod_lt q3 (by decide)
    have hp2_lt : 2 ^ (L - 1) % 3 < 3 := Nat.mod_lt _ (by decide)
    rcases (by omega : q3 % 3 = 1 ∨ q3 % 3 = 2) with hq | hq <;>
    rcases (by omega : 2 ^ (L - 1) % 3 = 1 ∨ 2 ^ (L - 1) % 3 = 2) with hp | hp <;>
    (rw [hq, hp] at h0; cases h0)
  have hq3_ge : q3 ≥ 2 * 3 ^ (2 * k2 + 8) - 1 := by
    have ha1_ge8 : 2 ^ (a + 1) ≥ 8 * 2 ^ b0 := by
      have h : 2 ^ (3 + b0) ≤ 2 ^ (a + 1) := pow2_mono_nat (by dsimp [a]; omega)
      rwa [Nat.pow_add 2 3 b0] at h
    have hp3_le : 3 ^ (2 * k2 + 8) ≤ 3 ^ w :=
      nat_pow_mono_exp_pos 3 (2 * k2 + 8) w (by decide) (by dsimp [w]; omega)
    have hge8 : 3 * q3 + 1 ≥ 8 * (3 ^ (2 * k2 + 8) + 1) := by
      rw [h3q3]
      exact Nat.le_trans (Nat.mul_le_mul_left 8 (Nat.add_le_add_right hp3_le 1))
        (Nat.le_trans (Nat.mul_le_mul_left 8 h3w_lo) ha1_ge8)
    generalize 3 ^ (2 * k2 + 8) = P3 at hge8 ⊢; omega
  have h4k2 : 2 ^ B ≤ 4 ^ k2 := by
    rw [pow4_eq_pow2_even k2]
    exact pow2_mono_nat (by dsimp [k2]; omega)
  exact (twoStepTernaryCarryChain_spec_and_inj_w17 k2 (L - 1) (q3 * 2 ^ (L - 1)) (L - 1)
    (Nat.le_refl _) (by omega) hR0_n3 (Nat.mul_le_mul_right _ hq3_ge)).2
    m1 m2 (Nat.lt_of_lt_of_le hm1 h4k2) (Nat.lt_of_lt_of_le hm2 h4k2) hgaps_eq

/--
  Theorem W17.4d (`dyadic_window_sub500_3bit_collision_steeper_slope_exponential_occupancy`,
  `zero custom axioms`):
  Breaking the `s = 1` Unary Bottom Barrier via 3-Bit (`s = 3`) Multiplicative-Dlog `Mod 177147`
  (`3^11`) Collision Lifting (`bottom3BitBucket177147`): Unconditional Sub-`500` Threshold
  (`M_0 = 360 ≤ 500`, `17,714x` Smaller Than Wave 16's `6,377,332` and `72x` Smaller Than Unary
  `26,265`!), Steeper-Slope (`c = 6 ≤ 6`, Beating `c = 8`!) True Exponential Surviving-Leaf
  Dyadic-Window Occupancy `≥ 2 ^ ((M - 360) / 6)` Across ALL `M ≥ 366` and ALL `L_max ≥ M`
  (`Branches P2.2 & P5.3`, `W17_H4`).
-/
theorem dyadic_window_sub500_3bit_collision_steeper_slope_exponential_occupancy :
    (dyadicExpWindowMinM17Low 0 = 360 ∧ 360 ≤ 500 ∧ 6 ≤ 6) ∧
    (∀ (B M : Nat), B ≥ 1 -> M ≥ dyadicExpWindowMinM17Low B ->
      let k2 := (B + 1) / 2
      let w := 2 * k2 + 10
      let b0 := binBitLength (3 ^ w)
      let delta2 := 2 + dyadicPolyShiftDelta (b0 + 2)
      (∀ mask : Nat, mask < 2 ^ B ->
        let u := uWinExp17Low B M mask
        let y := exactBackwardQuotient 1 u 0
        IsFirstHitOnePair u 0 ∧
        u.length = M - delta2 ∧
        u.length ≤ M ∧
        parityWeight u = w ∧
        canonicalSuffixShift u 1 = b0 + delta2 ∧
        y % 512 = 507 ∧
        y % 9 = 7 ∧
        IsSurvivingMod373248Class y ∧
        2 ^ M ≤ y ∧ y < 2 ^ (M + 1) ∧
        y ∈ dyadicWindowSurvivingQ0Leaves M M ∧
        (∀ L_max : Nat, L_max ≥ M -> y ∈ dyadicWindowSurvivingQ0Leaves L_max M)) ∧
      (∀ m1 m2 : Nat, m1 < 2 ^ B -> m2 < 2 ^ B ->
        exactBackwardQuotient 1 (uWinExp17Low B M m1) 0 =
          exactBackwardQuotient 1 (uWinExp17Low B M m2) 0 ->
        m1 = m2) ∧
      ((dyadicWindowSurvivingQ0Leaves M M).length ≥ 2 ^ B ∧
       ∀ L_max : Nat, L_max ≥ M ->
         (dyadicWindowSurvivingQ0Leaves L_max M).length ≥ 2 ^ B)) ∧
    (∀ (M L_max : Nat), M ≥ 366 -> L_max ≥ M ->
      (dyadicWindowSurvivingQ0Leaves L_max M).length ≥ 2 ^ ((M - 360) / 6)) := by
  have hmain : ∀ (B M : Nat), B ≥ 1 -> M ≥ dyadicExpWindowMinM17Low B ->
      let k2 := (B + 1) / 2
      let w := 2 * k2 + 10
      let b0 := binBitLength (3 ^ w)
      let delta2 := 2 + dyadicPolyShiftDelta (b0 + 2)
      (∀ mask : Nat, mask < 2 ^ B ->
        let u := uWinExp17Low B M mask
        let y := exactBackwardQuotient 1 u 0
        IsFirstHitOnePair u 0 ∧
        u.length = M - delta2 ∧
        u.length ≤ M ∧
        parityWeight u = w ∧
        canonicalSuffixShift u 1 = b0 + delta2 ∧
        y % 512 = 507 ∧
        y % 9 = 7 ∧
        IsSurvivingMod373248Class y ∧
        2 ^ M ≤ y ∧ y < 2 ^ (M + 1) ∧
        y ∈ dyadicWindowSurvivingQ0Leaves M M ∧
        (∀ L_max : Nat, L_max ≥ M -> y ∈ dyadicWindowSurvivingQ0Leaves L_max M)) ∧
      (∀ m1 m2 : Nat, m1 < 2 ^ B -> m2 < 2 ^ B ->
        exactBackwardQuotient 1 (uWinExp17Low B M m1) 0 =
          exactBackwardQuotient 1 (uWinExp17Low B M m2) 0 ->
        m1 = m2) ∧
      ((dyadicWindowSurvivingQ0Leaves M M).length ≥ 2 ^ B ∧
       ∀ L_max : Nat, L_max ≥ M ->
         (dyadicWindowSurvivingQ0Leaves L_max M).length ≥ 2 ^ B) := by
    intro B M hB hM; dsimp only
    refine ⟨?_, fun m1 m2 h1 h2 heq => uWinExp17Low_inj_mask_w17 B M m1 m2 hB hM h1 h2 heq, ?_⟩
    · intro mask hmask
      rcases uWinExp17Low_per_mask_leaf_spec_w17 B M mask hB hM hmask with
        ⟨hfh, hlen, hle_M, hwt, hsh, h512, h9, _, hcls, hlo, hhi, hmem⟩
      exact ⟨hfh, hlen, hle_M, hwt, hsh, h512, h9, hcls, hlo, hhi, hmem M (Nat.le_refl M), hmem⟩
    · rcases descIdxListW17_spec (2 ^ B) with ⟨hd_len, hd_nd, hd_lt⟩
      let fnLeaf : Nat -> Nat := fun mask => exactBackwardQuotient 1 (uWinExp17Low B M mask) 0
      let leaves2B := (descIdxListW17 (2 ^ B)).map fnLeaf
      have hnd_2B : NoDupNat leaves2B :=
        noDupNat_map_inj_on_w17 fnLeaf (descIdxListW17 (2 ^ B)) hd_nd
          (fun a ha b hb heq => uWinExp17Low_inj_mask_w17 B M a b hB hM (hd_lt a ha) (hd_lt b hb) heq)
      have hlen_2B : leaves2B.length = 2 ^ B := by
        dsimp only [leaves2B]; rw [List.length_map, hd_len]
      have hall_L : ∀ L_max : Nat, L_max ≥ M ->
          (dyadicWindowSurvivingQ0Leaves L_max M).length ≥ 2 ^ B := by
        intro L_max hL_max
        have hsub_2B : ∀ y ∈ leaves2B, y ∈ dyadicWindowSurvivingQ0Leaves L_max M := by
          intro y hy
          rcases List.mem_map.mp hy with ⟨mask, hmask, rfl⟩
          exact (uWinExp17Low_per_mask_leaf_spec_w17 B M mask hB hM (hd_lt mask hmask)).2.2.2.2.2.2.2.2.2.2.2 L_max hL_max
        have hle := noDupNat_length_le_of_subset_w17
          (dyadicWindowSurvivingQ0Leaves L_max M) leaves2B hnd_2B hsub_2B
        omega
      exact ⟨hall_L M (Nat.le_refl M), hall_L⟩
  refine ⟨⟨rfl, by decide, by decide⟩, hmain, ?_⟩
  intro M L_max hM hL_max
  let B := (M - 360) / 6
  have hB1 : B ≥ 1 := by dsimp [B]; omega
  have hM_min : M ≥ dyadicExpWindowMinM17Low B := by
    dsimp [B]; unfold dyadicExpWindowMinM17Low; omega
  exact (hmain B M hB1 hM_min).2.2.2 L_max hL_max

end CollatzFormal
