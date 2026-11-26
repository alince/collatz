/-
  CollatzFormal/Wave18WholeSpace.lean
  Wave 18 Whole-Space Mathematical & CS Proof Loop (Synthesis — Fronts C & D):
  1. Front C (Branches P1.2 & P5.17):
     - Universal Choice-Free Binary De Bruijn / Kirchoff Vertex-Flow Conservation Identities on
       All Eight Binary `3`-Gram Counts `(c_000, c_001, c_010, c_011, c_100, c_101, c_110, c_111)`
       Across ALL `n ≥ 4` (`binary_three_gram_debruijn_syzygies` `[choice-free]`), Expressing All
       Eight `2 * c_{ijk}` Nonnegatively in the Exact 5-Coordinate Basis
       `(binBitLength, binaryPopcount, binaryAltTransitions, 2 * c_001, 2 * c_111)` Up to Bounded
       Boundary Indicators in `{0, 1, 2, 3, 4}`, Plus Complete 100% `(0, ∞)^5` & `(0, ∞)^8`
       All-Bases Two-Sided Exponential Berg–Meinardus Preimage Impossibility Across `∀ M_0 ≥ 3`
       via Four Cardinal Periodic Collatz Preimage Families (`F_pos111`, `F_neg111`, `F_pos001`,
       `F_neg001`) + Squared-Weight Superharmonicity (`eventual_five_var_and_complete_3gram_exp_impossibility`),
     - End-to-End Global Convergence (`k ≤ (x + 1)^3 + (x + 1)^5`), Genuine 13-Tier `ω^13` Syracuse
       Cascade (`Cone 16 -> Cone 15 -> ... -> Cone 5 -> Φ_diamond2`, `54043172876472461 -> 20266189828677173`
       in `30` steps to `1`, `+38.44x` `Φ_2` jump), `mod 2^54` Newton–Hensel Odd-Inverse &
       `Nat`/`Int`/`Q_(6)^+` Agreement + Choice-Free Non-Integer Rational Cone-16 Avoidance, `mod 16`
       Post-Climb Non-Reentry, & `[]`-Axiom `M1/M2/M3` Counter-Model Separation for the 15th Solvable
       `(3x + 1)`-Cousin `T_diamond15`.
  2. Front D (Branches P2.2 & P5.3):
     - Complete Mod-`354294` (`2 * 3^11`, `118098/354294` Surviving Classes on `w ≥ 12`) Markov Shift
       Bijection, Universal `12`-Ones `177147 mod 354294` & `[true, false] ++ 11`-Ones `59049 mod 354294`
       Locks, Exhaustive Proof that ZERO of the `54` Surviving Length-`10` `Mod 1024` Prefixes Force
       `w(u) ≥ 12` (`u_esc11` escapes at `w = 11` on All-Ones `1023`), Exact Length-`11` `Mod 2048`
       `1 + 9 + 29 + 40 + 24 + 5 = 108` Surviving Prefix Lift (`2047` Forces `w(u) ≥ 12`), &
       `3^(w - 12)` (`j = 11`) Multi-Step Fiber Equidistribution,
     - Choice-Free 3-Step `Mod 81` Span-`≤ 14` Stall Obstruction (`u_norm = 79` Stalls at `7 < 8 = 2^3`
       Valid Branches) vs Normalized `162`-State 4-Step `Mod 243` Ternary-Carry Macro-Selector
       (`chooseFourStepTernaryCarry243`, `16 = 2^4` Distinct Branches in `8 ≤ span ≤ 18 ≤ 19`),
       Paired with 4-Bit (`s = 4`) Multiplicative-Dlog `Mod 531441` (`3^12`) Bottom Collision Lifting
       (`bottom4BitBucket531441` at `stride = 81`, `max e_1 ≤ 181`) Proving Unconditional Sub-`250`
       Threshold (`M_0 = 210 ≤ 250`, Down from `360`!) AND Strictly Steeper-Slope (`c = 5 ≤ 5`,
       Beating `c = 6`!) Exponential Surviving-Leaf Dyadic-Window Occupancy `≥ 2 ^ ((M - 210) / 5)`
       Across ALL `M ≥ 215` and ALL `L_max ≥ M`.

  Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

import CollatzFormal.Wave17WholeSpace

namespace CollatzFormal

-- ============================================================================
-- SECTION 1: Front C Part 1 (Branch P1.2) — Choice-Free Binary De Bruijn /
--            Kirchoff `3`-Gram Flow Syzygies & Complete 100% `(0, ∞)^5` +
--            `(0, ∞)^8` Exponential Preimage Impossibility (`W18_H3`)
-- ============================================================================

/-- Fuel-bounded second-most-significant binary bit `b_{L-2}(n) ∈ {0, 1}` (`0` for `n < 2`). -/
def binarySecondMSBAux : Nat -> Nat -> Nat
  | 0, _ => 0
  | _ + 1, 0 => 0
  | _ + 1, 1 => 0
  | _ + 1, 2 => 0
  | _ + 1, 3 => 1
  | fuel + 1, n + 4 => binarySecondMSBAux fuel ((n + 4) / 2)

/-- Second-most-significant bit `b_{L-2}(n) ∈ {0, 1}` of `n` (`(n >> (L - 2)) & 1` for `n ≥ 2`). -/
def binarySecondMSB (n : Nat) : Nat :=
  binarySecondMSBAux n n

/-- Fuel-bounded MSB-to-LSB adjacent binary `3`-gram `(b2, b1, b0)` counter (`0` for `n < 4`). -/
def binaryThreeGramAux (b2 b1 b0 : Nat) : Nat -> Nat -> Nat
  | 0, _ => 0
  | _ + 1, 0 => 0
  | _ + 1, 1 => 0
  | _ + 1, 2 => 0
  | _ + 1, 3 => 0
  | fuel + 1, n + 4 =>
    let m := n + 4
    (if (((m / 4) % 2 == b2) && ((m / 2) % 2 == b1) && (m % 2 == b0)) then 1 else 0) +
      binaryThreeGramAux b2 b1 b0 fuel (m / 2)

/-- Adjacent `(0, 0, 0)` `3`-gram count in the standard MSB-to-LSB binary expansion of `n`. -/
def binaryThreeGram000 (n : Nat) : Nat := binaryThreeGramAux 0 0 0 n n
/-- Adjacent `(0, 0, 1)` `3`-gram count in the standard MSB-to-LSB binary expansion of `n`. -/
def binaryThreeGram001 (n : Nat) : Nat := binaryThreeGramAux 0 0 1 n n
/-- Adjacent `(0, 1, 0)` `3`-gram count in the standard MSB-to-LSB binary expansion of `n`. -/
def binaryThreeGram010 (n : Nat) : Nat := binaryThreeGramAux 0 1 0 n n
/-- Adjacent `(0, 1, 1)` `3`-gram count in the standard MSB-to-LSB binary expansion of `n`. -/
def binaryThreeGram011 (n : Nat) : Nat := binaryThreeGramAux 0 1 1 n n
/-- Adjacent `(1, 0, 0)` `3`-gram count in the standard MSB-to-LSB binary expansion of `n`. -/
def binaryThreeGram100 (n : Nat) : Nat := binaryThreeGramAux 1 0 0 n n
/-- Adjacent `(1, 0, 1)` `3`-gram count in the standard MSB-to-LSB binary expansion of `n`. -/
def binaryThreeGram101 (n : Nat) : Nat := binaryThreeGramAux 1 0 1 n n
/-- Adjacent `(1, 1, 0)` `3`-gram count in the standard MSB-to-LSB binary expansion of `n`. -/
def binaryThreeGram110 (n : Nat) : Nat := binaryThreeGramAux 1 1 0 n n
/-- Adjacent `(1, 1, 1)` `3`-gram count in the standard MSB-to-LSB binary expansion of `n`. -/
def binaryThreeGram111 (n : Nat) : Nat := binaryThreeGramAux 1 1 1 n n

private theorem mul_pow_w18s (a b : Nat) : ∀ n : Nat, (a * b) ^ n = a ^ n * b ^ n
  | 0 => rfl
  | n + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, mul_pow_w18s a b n]
    ac_rfl

private theorem pow_mono_base_w18s (a b : Nat) (hle : a ≤ b) : ∀ n : Nat, a ^ n ≤ b ^ n
  | 0 => Nat.le_refl 1
  | n + 1 => Nat.mul_le_mul (pow_mono_base_w18s a b hle n) hle

private theorem pow_mono_exp_ge1_w18s (a : Nat) (ha : a ≥ 1) :
    ∀ e1 e2 : Nat, e1 ≤ e2 -> a ^ e1 ≤ a ^ e2
  | 0, e2, _ => nat_pow_pos_of_pos a ha e2
  | e1 + 1, 0, hle => by omega
  | e1 + 1, e2 + 1, hle =>
    Nat.mul_le_mul_right a (pow_mono_exp_ge1_w18s a ha e1 e2 (by omega))

private theorem binarySecondMSBAux_lt2_w18 :
    ∀ (f n : Nat), binarySecondMSBAux f n < 2
  | 0, _ => by dsimp [binarySecondMSBAux]; decide
  | _ + 1, 0 => by dsimp [binarySecondMSBAux]; decide
  | _ + 1, 1 => by dsimp [binarySecondMSBAux]; decide
  | _ + 1, 2 => by dsimp [binarySecondMSBAux]; decide
  | _ + 1, 3 => by dsimp [binarySecondMSBAux]; decide
  | f + 1, n + 4 => binarySecondMSBAux_lt2_w18 f ((n + 4) / 2)

private theorem binarySecondMSBAux_eq_cf_w18 :
    ∀ (f1 f2 n : Nat), n ≤ f1 -> n ≤ f2 ->
      binarySecondMSBAux f1 n = binarySecondMSBAux f2 n
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, 0, _, _ => rfl
  | 0, _ + 1, _ + 1, h1, _ => by omega
  | _ + 1, 0, 0, _, _ => rfl
  | _ + 1, 0, _ + 1, _, h2 => by omega
  | _ + 1, _ + 1, 0, _, _ => rfl
  | _ + 1, _ + 1, 1, _, _ => rfl
  | _ + 1, _ + 1, 2, _, _ => rfl
  | _ + 1, _ + 1, 3, _, _ => rfl
  | f1 + 1, f2 + 1, n + 4, h1, h2 => by
    dsimp only [binarySecondMSBAux]
    exact binarySecondMSBAux_eq_cf_w18 f1 f2 ((n + 4) / 2) (by omega) (by omega)

private theorem binarySecondMSB_step_ge4_cf_w18 :
    ∀ k0 : Nat, binarySecondMSB (k0 + 4) = binarySecondMSB ((k0 + 4) / 2) := by
  intro k0
  unfold binarySecondMSB
  conv => lhs; unfold binarySecondMSBAux
  exact binarySecondMSBAux_eq_cf_w18 (k0 + 3) ((k0 + 4) / 2) ((k0 + 4) / 2) (by omega) (Nat.le_refl _)

private theorem binaryThreeGramAux_eq_cf_w18 (b2 b1 b0 : Nat) :
    ∀ (f1 f2 n : Nat), n ≤ f1 -> n ≤ f2 ->
      binaryThreeGramAux b2 b1 b0 f1 n = binaryThreeGramAux b2 b1 b0 f2 n
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, 0, _, _ => rfl
  | 0, _ + 1, _ + 1, h1, _ => by omega
  | _ + 1, 0, 0, _, _ => rfl
  | _ + 1, 0, _ + 1, _, h2 => by omega
  | _ + 1, _ + 1, 0, _, _ => rfl
  | _ + 1, _ + 1, 1, _, _ => rfl
  | _ + 1, _ + 1, 2, _, _ => rfl
  | _ + 1, _ + 1, 3, _, _ => rfl
  | f1 + 1, f2 + 1, n + 4, h1, h2 => by
    dsimp only [binaryThreeGramAux]
    rw [binaryThreeGramAux_eq_cf_w18 b2 b1 b0 f1 f2 ((n + 4) / 2) (by omega) (by omega)]

private theorem binaryThreeGram_step_ge4_cf_w18 (b2 b1 b0 k0 : Nat) :
    binaryThreeGramAux b2 b1 b0 (k0 + 4) (k0 + 4) =
      (if ((((k0 + 4) / 4) % 2 == b2) && (((k0 + 4) / 2) % 2 == b1) && ((k0 + 4) % 2 == b0))
       then 1 else 0) +
        binaryThreeGramAux b2 b1 b0 ((k0 + 4) / 2) ((k0 + 4) / 2) := by
  conv => lhs; unfold binaryThreeGramAux
  dsimp only
  rw [binaryThreeGramAux_eq_cf_w18 b2 b1 b0 (k0 + 3) ((k0 + 4) / 2) ((k0 + 4) / 2) (by omega) (Nat.le_refl _)]

private theorem binaryTwoGramAux_eq_cf_w18 (b1 b0 : Nat) :
    ∀ (f1 f2 n : Nat), n ≤ f1 -> n ≤ f2 ->
      binaryTwoGramAux b1 b0 f1 n = binaryTwoGramAux b1 b0 f2 n
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, 0, _, _ => rfl
  | 0, _ + 1, _ + 1, h1, _ => by omega
  | _ + 1, 0, 0, _, _ => rfl
  | _ + 1, 0, _ + 1, _, h2 => by omega
  | _ + 1, _ + 1, 0, _, _ => rfl
  | _ + 1, _ + 1, 1, _, _ => rfl
  | f1 + 1, f2 + 1, n + 2, h1, h2 => by
    simp only [binaryTwoGramAux]
    exact congrArg _ (binaryTwoGramAux_eq_cf_w18 b1 b0 f1 f2 ((n + 2) / 2) (by omega) (by omega))

private theorem binaryTwoGram_step_ge2_cf_w18 (b1 b0 k0 : Nat) :
    binaryTwoGramAux b1 b0 (k0 + 2) (k0 + 2) =
      (if (((k0 + 2) / 2) % 2 == b1) && ((k0 + 2) % 2 == b0) then 1 else 0) +
        binaryTwoGramAux b1 b0 ((k0 + 2) / 2) ((k0 + 2) / 2) := by
  conv => lhs; simp only [binaryTwoGramAux]
  exact congrArg _ (binaryTwoGramAux_eq_cf_w18 b1 b0 (k0 + 1) ((k0 + 2) / 2) ((k0 + 2) / 2) (by omega) (Nat.le_refl _))

private theorem binBitLengthAux_eq_cf_w18 :
    ∀ (f1 f2 n : Nat), n ≤ f1 -> n ≤ f2 -> binBitLengthAux f1 n = binBitLengthAux f2 n
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, 0, _, _ => rfl
  | 0, _ + 1, _ + 1, h1, _ => by omega
  | _ + 1, 0, 0, _, _ => rfl
  | _ + 1, 0, _ + 1, _, h2 => by omega
  | _ + 1, _ + 1, 0, _, _ => rfl
  | f1 + 1, f2 + 1, n' + 1, h1, h2 => by
    simp only [binBitLengthAux, Nat.succ_ne_zero, ite_false]
    exact congrArg _ (binBitLengthAux_eq_cf_w18 f1 f2 ((n' + 1) / 2) (by omega) (by omega))

private theorem binBitLength_step_succ_cf_w18 (m : Nat) :
    binBitLength (m + 1) = 1 + binBitLength ((m + 1) / 2) := by
  unfold binBitLength
  conv => lhs; simp only [binBitLengthAux, Nat.succ_ne_zero, ite_false]
  exact congrArg _ (binBitLengthAux_eq_cf_w18 m ((m + 1) / 2) ((m + 1) / 2) (by omega) (Nat.le_refl _))

private theorem binPopcountAux_eq_cf_w18 :
    ∀ (f1 f2 n : Nat), n ≤ f1 -> n ≤ f2 -> binPopcountAux f1 n = binPopcountAux f2 n
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, 0, _, _ => rfl
  | 0, _ + 1, _ + 1, h1, _ => by omega
  | _ + 1, 0, 0, _, _ => rfl
  | _ + 1, 0, _ + 1, _, h2 => by omega
  | _ + 1, _ + 1, 0, _, _ => rfl
  | f1 + 1, f2 + 1, n' + 1, h1, h2 => by
    simp only [binPopcountAux, Nat.succ_ne_zero, ite_false]
    exact congrArg _ (binPopcountAux_eq_cf_w18 f1 f2 ((n' + 1) / 2) (by omega) (by omega))

private theorem binaryPopcount_step_succ_cf_w18 (m : Nat) :
    binaryPopcount (m + 1) = (m + 1) % 2 + binaryPopcount ((m + 1) / 2) := by
  change binPopcount (m + 1) = (m + 1) % 2 + binPopcount ((m + 1) / 2)
  unfold binPopcount
  conv => lhs; simp only [binPopcountAux, Nat.succ_ne_zero, ite_false]
  exact congrArg _ (binPopcountAux_eq_cf_w18 m ((m + 1) / 2) ((m + 1) / 2) (by omega) (Nat.le_refl _))

private theorem binaryAltTransitionsAux_eq_cf_w18 :
    ∀ (f1 f2 n : Nat), n ≤ f1 -> n ≤ f2 ->
      binaryAltTransitionsAux f1 n = binaryAltTransitionsAux f2 n
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, 0, _, _ => rfl
  | 0, _ + 1, _ + 1, h1, _ => by omega
  | _ + 1, 0, 0, _, _ => rfl
  | _ + 1, 0, _ + 1, _, h2 => by omega
  | _ + 1, _ + 1, 0, _, _ => rfl
  | _ + 1, _ + 1, 1, _, _ => rfl
  | f1 + 1, f2 + 1, n + 2, h1, h2 => by
    simp only [binaryAltTransitionsAux]
    exact congrArg _ (binaryAltTransitionsAux_eq_cf_w18 f1 f2 ((n + 2) / 2) (by omega) (by omega))

private theorem binaryAltTransitions_step_ge2_cf_w18 (k0 : Nat) :
    binaryAltTransitions (k0 + 2) =
      (if (k0 + 2) % 2 != ((k0 + 2) / 2) % 2 then 1 else 0) +
        binaryAltTransitions ((k0 + 2) / 2) := by
  unfold binaryAltTransitions
  conv => lhs; simp only [binaryAltTransitionsAux]
  exact congrArg _ (binaryAltTransitionsAux_eq_cf_w18 (k0 + 1) ((k0 + 2) / 2) ((k0 + 2) / 2) (by omega) (Nat.le_refl _))

private def twoGramSyzPropW18 (k : Nat) : Prop :=
  2 * binaryTwoGram00 k + (2 * binaryPopcount k + binaryAltTransitions k + 1) =
    2 * binBitLength k + k % 2 ∧
  2 * binaryTwoGram01 k + 1 = binaryAltTransitions k + k % 2 ∧
  2 * binaryTwoGram11 k + (binaryAltTransitions k + 2) =
    2 * binaryPopcount k + (1 - k % 2)

private theorem twoGram_step_alg_w18 (g00 g01 g11 P T L r : Nat) (hr : r < 4)
    (s00 : 2 * g00 + (2 * P + T + 1) = 2 * L + r / 2)
    (s01 : 2 * g01 + 1 = T + r / 2)
    (s11 : 2 * g11 + (T + 2) = 2 * P + (1 - r / 2)) :
    2 * ((if (r / 2 == 0) && (r % 2 == 0) then 1 else 0) + g00) +
        (2 * (r % 2 + P) + ((if r % 2 != r / 2 then 1 else 0) + T) + 1) =
      2 * (1 + L) + r % 2 ∧
    2 * ((if (r / 2 == 0) && (r % 2 == 1) then 1 else 0) + g01) + 1 =
      ((if r % 2 != r / 2 then 1 else 0) + T) + r % 2 ∧
    2 * ((if (r / 2 == 1) && (r % 2 == 1) then 1 else 0) + g11) +
        (((if r % 2 != r / 2 then 1 else 0) + T) + 2) =
      2 * (r % 2 + P) + (1 - r % 2) := by
  match r, hr with
  | 0, _ =>
    change 2 * (1 + g00) + (2 * (0 + P) + (0 + T) + 1) = 2 * (1 + L) + 0 ∧
      2 * (0 + g01) + 1 = (0 + T) + 0 ∧
      2 * (0 + g11) + ((0 + T) + 2) = 2 * (0 + P) + 1
    change 2 * g00 + (2 * P + T + 1) = 2 * L + 0 at s00
    change 2 * g01 + 1 = T + 0 at s01
    change 2 * g11 + (T + 2) = 2 * P + 1 at s11
    exact ⟨by omega, by omega, by omega⟩
  | 1, _ =>
    change 2 * (0 + g00) + (2 * (1 + P) + (1 + T) + 1) = 2 * (1 + L) + 1 ∧
      2 * (1 + g01) + 1 = (1 + T) + 1 ∧
      2 * (0 + g11) + ((1 + T) + 2) = 2 * (1 + P) + 0
    change 2 * g00 + (2 * P + T + 1) = 2 * L + 0 at s00
    change 2 * g01 + 1 = T + 0 at s01
    change 2 * g11 + (T + 2) = 2 * P + 1 at s11
    exact ⟨by omega, by omega, by omega⟩
  | 2, _ =>
    change 2 * (0 + g00) + (2 * (0 + P) + (1 + T) + 1) = 2 * (1 + L) + 0 ∧
      2 * (0 + g01) + 1 = (1 + T) + 0 ∧
      2 * (0 + g11) + ((1 + T) + 2) = 2 * (0 + P) + 1
    change 2 * g00 + (2 * P + T + 1) = 2 * L + 1 at s00
    change 2 * g01 + 1 = T + 1 at s01
    change 2 * g11 + (T + 2) = 2 * P + 0 at s11
    exact ⟨by omega, by omega, by omega⟩
  | 3, _ =>
    change 2 * (0 + g00) + (2 * (1 + P) + (0 + T) + 1) = 2 * (1 + L) + 1 ∧
      2 * (0 + g01) + 1 = (0 + T) + 1 ∧
      2 * (1 + g11) + ((0 + T) + 2) = 2 * (1 + P) + 0
    change 2 * g00 + (2 * P + T + 1) = 2 * L + 1 at s00
    change 2 * g01 + 1 = T + 1 at s01
    change 2 * g11 + (T + 2) = 2 * P + 0 at s11
    exact ⟨by omega, by omega, by omega⟩
  | _ + 4, hlt => exact False.elim (by omega)

private theorem binaryTwoGram_step_cf_w18 (k0 : Nat)
    (ih : twoGramSyzPropW18 ((k0 + 4) / 2)) : twoGramSyzPropW18 (k0 + 4) := by
  let K := k0 + 4
  let m := K / 2
  let r := K % 4
  change twoGramSyzPropW18 m at ih
  rcases ih with ⟨s00, s01, s11⟩
  have hr4 : r < 4 := Nat.mod_lt K (by decide)
  have hk2 : K % 2 = r % 2 := by dsimp [K, r]; omega
  have hm2 : m % 2 = r / 2 := by dsimp [m, K, r]; omega
  have hbl : binBitLength K = 1 + binBitLength m := binBitLength_step_succ_cf_w18 (k0 + 3)
  have hpop : binaryPopcount K = r % 2 + binaryPopcount m := by
    rw [← hk2]; exact binaryPopcount_step_succ_cf_w18 (k0 + 3)
  have htr : binaryAltTransitions K =
      (if r % 2 != r / 2 then 1 else 0) + binaryAltTransitions m := by
    rw [← hk2, ← hm2]; exact binaryAltTransitions_step_ge2_cf_w18 (k0 + 2)
  have hg00 : binaryTwoGram00 K =
      (if (r / 2 == 0) && (r % 2 == 0) then 1 else 0) + binaryTwoGram00 m := by
    rw [← hk2, ← hm2]; exact binaryTwoGram_step_ge2_cf_w18 0 0 (k0 + 2)
  have hg01 : binaryTwoGram01 K =
      (if (r / 2 == 0) && (r % 2 == 1) then 1 else 0) + binaryTwoGram01 m := by
    rw [← hk2, ← hm2]; exact binaryTwoGram_step_ge2_cf_w18 0 1 (k0 + 2)
  have hg11 : binaryTwoGram11 K =
      (if (r / 2 == 1) && (r % 2 == 1) then 1 else 0) + binaryTwoGram11 m := by
    rw [← hk2, ← hm2]; exact binaryTwoGram_step_ge2_cf_w18 1 1 (k0 + 2)
  rw [hm2] at s00 s01 s11
  change twoGramSyzPropW18 K
  unfold twoGramSyzPropW18
  rw [hk2, hbl, hpop, htr, hg00, hg01, hg11]
  exact twoGram_step_alg_w18
    (binaryTwoGram00 m) (binaryTwoGram01 m) (binaryTwoGram11 m)
    (binaryPopcount m) (binaryAltTransitions m) (binBitLength m) r hr4 s00 s01 s11

private theorem binaryTwoGram_syzygies_cf_w18 :
    ∀ (fuel k : Nat), k ≥ 2 -> k ≤ fuel -> twoGramSyzPropW18 k
  | 0, _, hk, _ => False.elim (by omega)
  | _ + 1, 0, hk, _ => False.elim (by omega)
  | _ + 1, 1, hk, _ => False.elim (by omega)
  | _ + 1, 2, _, _ => by unfold twoGramSyzPropW18; decide
  | _ + 1, 3, _, _ => by unfold twoGramSyzPropW18; decide
  | f + 1, k0 + 4, _, hle =>
    binaryTwoGram_step_cf_w18 k0
      (binaryTwoGram_syzygies_cf_w18 f ((k0 + 4) / 2) (by omega) (by omega))

private def threeGramFlowPropW18 (k : Nat) : Prop :=
  binaryThreeGram000 k + binaryThreeGram001 k + binaryThreeGram010 k + binaryThreeGram011 k +
    binaryThreeGram100 k + binaryThreeGram101 k + binaryThreeGram110 k + binaryThreeGram111 k + 2 =
      binBitLength k ∧
  binaryThreeGram100 k = binaryThreeGram001 k + (if k % 4 == 0 then 1 else 0) ∧
  binaryThreeGram001 k + binaryThreeGram101 k = binaryTwoGram01 k ∧
  binaryThreeGram000 k + binaryThreeGram001 k + (if k % 4 == 0 then 1 else 0) = binaryTwoGram00 k ∧
  binaryThreeGram011 k + binaryThreeGram111 k + binarySecondMSB k = binaryTwoGram11 k ∧
  binaryThreeGram110 k + binaryThreeGram111 k + (if k % 4 == 3 then 1 else 0) = binaryTwoGram11 k ∧
  binaryThreeGram010 k + binaryThreeGram011 k + (if k % 4 == 1 then 1 else 0) = binaryTwoGram01 k

private theorem threeGramFlow_r8_deltas_w18 :
    ∀ r : Fin 8,
      let b0 := r.val % 2
      let b1 := (r.val / 2) % 2
      let b2 := r.val / 4
      let im0 := if r.val / 2 == 0 then 1 else 0
      let im1 := if r.val / 2 == 1 then 1 else 0
      let im3 := if r.val / 2 == 3 then 1 else 0
      let ik0 := if r.val % 4 == 0 then 1 else 0
      let ik1 := if r.val % 4 == 1 then 1 else 0
      let ik3 := if r.val % 4 == 3 then 1 else 0
      let dc00 := if (b1 == 0) && (b0 == 0) then 1 else 0
      let dc01 := if (b1 == 0) && (b0 == 1) then 1 else 0
      let dc11 := if (b1 == 1) && (b0 == 1) then 1 else 0
      let d000 := if (b2 == 0) && (b1 == 0) && (b0 == 0) then 1 else 0
      let d001 := if (b2 == 0) && (b1 == 0) && (b0 == 1) then 1 else 0
      let d010 := if (b2 == 0) && (b1 == 1) && (b0 == 0) then 1 else 0
      let d011 := if (b2 == 0) && (b1 == 1) && (b0 == 1) then 1 else 0
      let d100 := if (b2 == 1) && (b1 == 0) && (b0 == 0) then 1 else 0
      let d101 := if (b2 == 1) && (b1 == 0) && (b0 == 1) then 1 else 0
      let d110 := if (b2 == 1) && (b1 == 1) && (b0 == 0) then 1 else 0
      let d111 := if (b2 == 1) && (b1 == 1) && (b0 == 1) then 1 else 0
      d000 + d001 + d010 + d011 + d100 + d101 + d110 + d111 = 1 ∧
      d100 + im0 = d001 + ik0 ∧
      d001 + d101 = dc01 ∧
      d000 + d001 + ik0 = dc00 + im0 ∧
      d011 + d111 = dc11 ∧
      d110 + d111 + ik3 = dc11 + im3 ∧
      d010 + d011 + ik1 = dc01 + im1 := by
  decide

private theorem threeGramFlow_step_alg_w18
    (g000 g001 g010 g011 g100 g101 g110 g111 c00 c01 c11 L s2 : Nat)
    (im0 im1 im3 ik0 ik1 ik3 dc00 dc01 dc11
     d000 d001 d010 d011 d100 d101 d110 d111 : Nat)
    (hsum : d000 + d001 + d010 + d011 + d100 + d101 + d110 + d111 = 1 ∧
      d100 + im0 = d001 + ik0 ∧
      d001 + d101 = dc01 ∧
      d000 + d001 + ik0 = dc00 + im0 ∧
      d011 + d111 = dc11 ∧
      d110 + d111 + ik3 = dc11 + im3 ∧
      d010 + d011 + ik1 = dc01 + im1)
    (e1 : g000 + g001 + g010 + g011 + g100 + g101 + g110 + g111 + 2 = L)
    (e2 : g100 = g001 + im0)
    (e3 : g001 + g101 = c01)
    (e4 : g000 + g001 + im0 = c00)
    (e5 : g011 + g111 + s2 = c11)
    (e6 : g110 + g111 + im3 = c11)
    (e7 : g010 + g011 + im1 = c01) :
    (d000 + g000) + (d001 + g001) + (d010 + g010) + (d011 + g011) +
      (d100 + g100) + (d101 + g101) + (d110 + g110) + (d111 + g111) + 2 = 1 + L ∧
    (d100 + g100) = (d001 + g001) + ik0 ∧
    (d001 + g001) + (d101 + g101) = (dc01 + c01) ∧
    (d000 + g000) + (d001 + g001) + ik0 = (dc00 + c00) ∧
    (d011 + g011) + (d111 + g111) + s2 = (dc11 + c11) ∧
    (d110 + g110) + (d111 + g111) + ik3 = (dc11 + c11) ∧
    (d010 + g010) + (d011 + g011) + ik1 = (dc01 + c01) := by
  rcases hsum with ⟨hd1, hd2, hd3, hd4, hd5, hd6, hd7⟩
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

private theorem threeGramFlow_step_cf_w18 (k0 : Nat)
    (ih : threeGramFlowPropW18 ((k0 + 8) / 2)) : threeGramFlowPropW18 (k0 + 8) := by
  let K := k0 + 8
  let m := K / 2
  let r := K % 8
  change threeGramFlowPropW18 m at ih
  rcases ih with ⟨e1, e2, e3, e4, e5, e6, e7⟩
  have hr8 : r < 8 := Nat.mod_lt K (by decide)
  have hk2 : K % 2 = r % 2 := by dsimp [K, r]; omega
  have hk4 : K % 4 = r % 4 := by dsimp [K, r]; omega
  have hm2 : m % 2 = (r / 2) % 2 := by dsimp [m, K, r]; omega
  have hm4 : m % 4 = r / 2 := by dsimp [m, K, r]; omega
  have hq2 : (K / 4) % 2 = r / 4 := by dsimp [K, r]; omega
  have hbl : binBitLength K = 1 + binBitLength m := binBitLength_step_succ_cf_w18 (k0 + 7)
  have hs2 : binarySecondMSB K = binarySecondMSB m := binarySecondMSB_step_ge4_cf_w18 (k0 + 4)
  have hc00 : binaryTwoGram00 K =
      (if ((r / 2) % 2 == 0) && (r % 2 == 0) then 1 else 0) + binaryTwoGram00 m := by
    rw [← hk2, ← hm2]; exact binaryTwoGram_step_ge2_cf_w18 0 0 (k0 + 6)
  have hc01 : binaryTwoGram01 K =
      (if ((r / 2) % 2 == 0) && (r % 2 == 1) then 1 else 0) + binaryTwoGram01 m := by
    rw [← hk2, ← hm2]; exact binaryTwoGram_step_ge2_cf_w18 0 1 (k0 + 6)
  have hc11 : binaryTwoGram11 K =
      (if ((r / 2) % 2 == 1) && (r % 2 == 1) then 1 else 0) + binaryTwoGram11 m := by
    rw [← hk2, ← hm2]; exact binaryTwoGram_step_ge2_cf_w18 1 1 (k0 + 6)
  have hg000 : binaryThreeGram000 K =
      (if ((r / 4 == 0) && ((r / 2) % 2 == 0) && (r % 2 == 0)) then 1 else 0) + binaryThreeGram000 m := by
    rw [← hk2, ← hm2, ← hq2]; exact binaryThreeGram_step_ge4_cf_w18 0 0 0 (k0 + 4)
  have hg001 : binaryThreeGram001 K =
      (if ((r / 4 == 0) && ((r / 2) % 2 == 0) && (r % 2 == 1)) then 1 else 0) + binaryThreeGram001 m := by
    rw [← hk2, ← hm2, ← hq2]; exact binaryThreeGram_step_ge4_cf_w18 0 0 1 (k0 + 4)
  have hg010 : binaryThreeGram010 K =
      (if ((r / 4 == 0) && ((r / 2) % 2 == 1) && (r % 2 == 0)) then 1 else 0) + binaryThreeGram010 m := by
    rw [← hk2, ← hm2, ← hq2]; exact binaryThreeGram_step_ge4_cf_w18 0 1 0 (k0 + 4)
  have hg011 : binaryThreeGram011 K =
      (if ((r / 4 == 0) && ((r / 2) % 2 == 1) && (r % 2 == 1)) then 1 else 0) + binaryThreeGram011 m := by
    rw [← hk2, ← hm2, ← hq2]; exact binaryThreeGram_step_ge4_cf_w18 0 1 1 (k0 + 4)
  have hg100 : binaryThreeGram100 K =
      (if ((r / 4 == 1) && ((r / 2) % 2 == 0) && (r % 2 == 0)) then 1 else 0) + binaryThreeGram100 m := by
    rw [← hk2, ← hm2, ← hq2]; exact binaryThreeGram_step_ge4_cf_w18 1 0 0 (k0 + 4)
  have hg101 : binaryThreeGram101 K =
      (if ((r / 4 == 1) && ((r / 2) % 2 == 0) && (r % 2 == 1)) then 1 else 0) + binaryThreeGram101 m := by
    rw [← hk2, ← hm2, ← hq2]; exact binaryThreeGram_step_ge4_cf_w18 1 0 1 (k0 + 4)
  have hg110 : binaryThreeGram110 K =
      (if ((r / 4 == 1) && ((r / 2) % 2 == 1) && (r % 2 == 0)) then 1 else 0) + binaryThreeGram110 m := by
    rw [← hk2, ← hm2, ← hq2]; exact binaryThreeGram_step_ge4_cf_w18 1 1 0 (k0 + 4)
  have hg111 : binaryThreeGram111 K =
      (if ((r / 4 == 1) && ((r / 2) % 2 == 1) && (r % 2 == 1)) then 1 else 0) + binaryThreeGram111 m := by
    rw [← hk2, ← hm2, ← hq2]; exact binaryThreeGram_step_ge4_cf_w18 1 1 1 (k0 + 4)
  rw [hm4] at e2 e4 e6 e7
  change threeGramFlowPropW18 K
  unfold threeGramFlowPropW18
  rw [hk4, hbl, hs2, hc00, hc01, hc11, hg000, hg001, hg010, hg011, hg100, hg101, hg110, hg111]
  exact threeGramFlow_step_alg_w18
    (binaryThreeGram000 m) (binaryThreeGram001 m) (binaryThreeGram010 m) (binaryThreeGram011 m)
    (binaryThreeGram100 m) (binaryThreeGram101 m) (binaryThreeGram110 m) (binaryThreeGram111 m)
    (binaryTwoGram00 m) (binaryTwoGram01 m) (binaryTwoGram11 m)
    (binBitLength m) (binarySecondMSB m)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (threeGramFlow_r8_deltas_w18 ⟨r, hr8⟩) e1 e2 e3 e4 e5 e6 e7

private theorem threeGramFlow_ind_cf_w18 :
    ∀ (fuel k : Nat), k ≥ 4 -> k ≤ fuel -> threeGramFlowPropW18 k
  | 0, _, hk, _ => False.elim (by omega)
  | _ + 1, 0, hk, _ => False.elim (by omega)
  | _ + 1, 1, hk, _ => False.elim (by omega)
  | _ + 1, 2, hk, _ => False.elim (by omega)
  | _ + 1, 3, hk, _ => False.elim (by omega)
  | _ + 1, 4, _, _ => by unfold threeGramFlowPropW18; decide
  | _ + 1, 5, _, _ => by unfold threeGramFlowPropW18; decide
  | _ + 1, 6, _, _ => by unfold threeGramFlowPropW18; decide
  | _ + 1, 7, _, _ => by unfold threeGramFlowPropW18; decide
  | f + 1, k0 + 8, _, hle =>
    threeGramFlow_step_cf_w18 k0
      (threeGramFlow_ind_cf_w18 f ((k0 + 8) / 2) (by omega) (by omega))

private theorem debruijn_doubled_alg_w18
    (g000 g001 g010 g011 g100 g101 g110 g111 c00 c01 c11 L P T s2 r : Nat)
    (hs2_lt : s2 < 2) (hr4 : r < 4)
    (f2 : g100 = g001 + (if r == 0 then 1 else 0))
    (f3 : g001 + g101 = c01)
    (f4 : g000 + g001 + (if r == 0 then 1 else 0) = c00)
    (f5 : g011 + g111 + s2 = c11)
    (f6 : g110 + g111 + (if r == 3 then 1 else 0) = c11)
    (f7 : g010 + g011 + (if r == 1 then 1 else 0) = c01)
    (t00 : 2 * c00 + (2 * P + T + 1) = 2 * L + r % 2)
    (t01 : 2 * c01 + 1 = T + r % 2)
    (t11 : 2 * c11 + (T + 2) = 2 * P + (1 - r % 2)) :
    let b := r % 2
    let i0 := if r == 0 then 1 else 0
    let i1 := if r == 1 then 1 else 0
    let i3 := if r == 3 then 1 else 0
    let e000 := b + 2 - 2 * i0
    let e100 := 2 * i0
    let e101 := b
    let e011 := (1 - b) + 2 - 2 * s2
    let e110 := (1 - b) + 2 - 2 * i3
    let e010 := 2 * b + 2 * s2 - 2 * i1
    e000 ≤ 3 ∧ e100 ≤ 2 ∧ e101 ≤ 1 ∧ e011 ≤ 3 ∧ e110 ≤ 3 ∧ e010 ≤ 4 ∧
    2 * g000 + (2 * P + T + 2 * g001 + 3) = 2 * L + e000 ∧
    2 * g100 = 2 * g001 + e100 ∧
    2 * g101 + (2 * g001 + 1) = T + e101 ∧
    2 * g011 + (T + 2 * g111 + 4) = 2 * P + e011 ∧
    2 * g110 + (T + 2 * g111 + 4) = 2 * P + e110 ∧
    2 * g010 + 2 * P = 2 * T + 2 * g111 + e010 := by
  dsimp only
  match r, hr4 with
  | 0, _ =>
    change g100 = g001 + 1 at f2
    change g000 + g001 + 1 = c00 at f4
    change g110 + g111 + 0 = c11 at f6
    change g010 + g011 + 0 = c01 at f7
    change 2 * c00 + (2 * P + T + 1) = 2 * L + 0 at t00
    change 2 * c01 + 1 = T + 0 at t01
    change 2 * c11 + (T + 2) = 2 * P + 1 at t11
    have hi0 : (if (0 == 0) then 1 else 0) = 1 := rfl
    have hi1 : (if (0 == 1) then 1 else 0) = 0 := rfl
    have hi3 : (if (0 == 3) then 1 else 0) = 0 := rfl
    have hb0 : 0 % 2 = 0 := rfl
    rw [hb0, hi0, hi1, hi3]; clear hi0 hi1 hi3 hb0
    exact ⟨by decide, by decide, by decide, by omega, by decide, by omega,
           by omega, by omega, by omega, by omega, by omega, by omega⟩
  | 1, _ =>
    change g100 = g001 + 0 at f2
    change g000 + g001 + 0 = c00 at f4
    change g110 + g111 + 0 = c11 at f6
    change g010 + g011 + 1 = c01 at f7
    change 2 * c00 + (2 * P + T + 1) = 2 * L + 1 at t00
    change 2 * c01 + 1 = T + 1 at t01
    change 2 * c11 + (T + 2) = 2 * P + 0 at t11
    have hi0 : (if (1 == 0) then 1 else 0) = 0 := rfl
    have hi1 : (if (1 == 1) then 1 else 0) = 1 := rfl
    have hi3 : (if (1 == 3) then 1 else 0) = 0 := rfl
    have hb0 : 1 % 2 = 1 := rfl
    rw [hb0, hi0, hi1, hi3]; clear hi0 hi1 hi3 hb0
    exact ⟨by decide, by decide, by decide, by omega, by decide, by omega,
           by omega, by omega, by omega, by omega, by omega, by omega⟩
  | 2, _ =>
    change g100 = g001 + 0 at f2
    change g000 + g001 + 0 = c00 at f4
    change g110 + g111 + 0 = c11 at f6
    change g010 + g011 + 0 = c01 at f7
    change 2 * c00 + (2 * P + T + 1) = 2 * L + 0 at t00
    change 2 * c01 + 1 = T + 0 at t01
    change 2 * c11 + (T + 2) = 2 * P + 1 at t11
    have hi0 : (if (2 == 0) then 1 else 0) = 0 := rfl
    have hi1 : (if (2 == 1) then 1 else 0) = 0 := rfl
    have hi3 : (if (2 == 3) then 1 else 0) = 0 := rfl
    have hb0 : 2 % 2 = 0 := rfl
    rw [hb0, hi0, hi1, hi3]; clear hi0 hi1 hi3 hb0
    exact ⟨by decide, by decide, by decide, by omega, by decide, by omega,
           by omega, by omega, by omega, by omega, by omega, by omega⟩
  | 3, _ =>
    change g100 = g001 + 0 at f2
    change g000 + g001 + 0 = c00 at f4
    change g110 + g111 + 1 = c11 at f6
    change g010 + g011 + 0 = c01 at f7
    change 2 * c00 + (2 * P + T + 1) = 2 * L + 1 at t00
    change 2 * c01 + 1 = T + 1 at t01
    change 2 * c11 + (T + 2) = 2 * P + 0 at t11
    have hi0 : (if (3 == 0) then 1 else 0) = 0 := rfl
    have hi1 : (if (3 == 1) then 1 else 0) = 0 := rfl
    have hi3 : (if (3 == 3) then 1 else 0) = 1 := rfl
    have hb0 : 3 % 2 = 1 := rfl
    rw [hb0, hi0, hi1, hi3]; clear hi0 hi1 hi3 hb0
    exact ⟨by decide, by decide, by decide, by omega, by decide, by omega,
           by omega, by omega, by omega, by omega, by omega, by omega⟩
  | _ + 4, hlt => exact False.elim (by omega)

/--
  Theorem W18.3a (`binary_three_gram_debruijn_syzygies`, choice-free `zero custom axioms`):
  Universal Binary De Bruijn / Kirchoff Vertex-Flow Conservation Identities on All Eight
  Binary `3`-Grams `(c_000 .. c_111)` Across ALL `n ≥ 4`, Determining Exact Independent
  Coordinate Dimension `5` (`binBitLength, binaryPopcount, binaryAltTransitions, c_001, c_111`)
  and Nonnegative Doubled Basis Reductions with Bounded Boundary Indicators in `{0..4}`
  (`Branch P1.2`, witness `ZPOS_PREIMAGE_3GRAM_PURE_535_TO_803`, `W18_H3`).
-/
theorem binary_three_gram_debruijn_syzygies (n : Nat) (hn : n ≥ 4) :
    (binaryThreeGram000 n + binaryThreeGram001 n + binaryThreeGram010 n + binaryThreeGram011 n +
       binaryThreeGram100 n + binaryThreeGram101 n + binaryThreeGram110 n + binaryThreeGram111 n + 2 =
         binBitLength n ∧
     binaryThreeGram100 n = binaryThreeGram001 n + (if n % 4 == 0 then 1 else 0) ∧
     binaryThreeGram001 n + binaryThreeGram101 n = binaryTwoGram01 n ∧
     binaryThreeGram000 n + binaryThreeGram001 n + (if n % 4 == 0 then 1 else 0) = binaryTwoGram00 n ∧
     binaryThreeGram011 n + binaryThreeGram111 n + binarySecondMSB n = binaryTwoGram11 n ∧
     binaryThreeGram110 n + binaryThreeGram111 n + (if n % 4 == 3 then 1 else 0) = binaryTwoGram11 n ∧
     binaryThreeGram010 n + binaryThreeGram011 n + (if n % 4 == 1 then 1 else 0) = binaryTwoGram01 n) ∧
    (let b := n % 2
     let s2 := binarySecondMSB n
     let i0 := if n % 4 == 0 then 1 else 0
     let i1 := if n % 4 == 1 then 1 else 0
     let i3 := if n % 4 == 3 then 1 else 0
     let e000 := b + 2 - 2 * i0
     let e100 := 2 * i0
     let e101 := b
     let e011 := (1 - b) + 2 - 2 * s2
     let e110 := (1 - b) + 2 - 2 * i3
     let e010 := 2 * b + 2 * s2 - 2 * i1
     e000 ≤ 3 ∧ e100 ≤ 2 ∧ e101 ≤ 1 ∧ e011 ≤ 3 ∧ e110 ≤ 3 ∧ e010 ≤ 4 ∧
     2 * binaryThreeGram000 n +
       (2 * binaryPopcount n + binaryAltTransitions n + 2 * binaryThreeGram001 n + 3) =
         2 * binBitLength n + e000 ∧
     2 * binaryThreeGram100 n = 2 * binaryThreeGram001 n + e100 ∧
     2 * binaryThreeGram101 n + (2 * binaryThreeGram001 n + 1) =
       binaryAltTransitions n + e101 ∧
     2 * binaryThreeGram011 n + (binaryAltTransitions n + 2 * binaryThreeGram111 n + 4) =
       2 * binaryPopcount n + e011 ∧
     2 * binaryThreeGram110 n + (binaryAltTransitions n + 2 * binaryThreeGram111 n + 4) =
       2 * binaryPopcount n + e110 ∧
     2 * binaryThreeGram010 n + 2 * binaryPopcount n =
       2 * binaryAltTransitions n + 2 * binaryThreeGram111 n + e010) := by
  have hflow := threeGramFlow_ind_cf_w18 n n hn (Nat.le_refl n)
  rcases hflow with ⟨f1, f2, f3, f4, f5, f6, f7⟩
  rcases binaryTwoGram_syzygies_cf_w18 n n (by omega) (Nat.le_refl n) with ⟨t00, t01, t11⟩
  refine ⟨⟨f1, f2, f3, f4, f5, f6, f7⟩, ?_⟩
  let r := n % 4
  have hr4 : r < 4 := Nat.mod_lt n (by decide)
  have hn2 : n % 2 = r % 2 := by dsimp [r]; omega
  rw [hn2] at t00 t01 t11 ⊢
  exact debruijn_doubled_alg_w18
    (binaryThreeGram000 n) (binaryThreeGram001 n) (binaryThreeGram010 n) (binaryThreeGram011 n)
    (binaryThreeGram100 n) (binaryThreeGram101 n) (binaryThreeGram110 n) (binaryThreeGram111 n)
    (binaryTwoGram00 n) (binaryTwoGram01 n) (binaryTwoGram11 n)
    (binBitLength n) (binaryPopcount n) (binaryAltTransitions n) (binarySecondMSB n) r
    (binarySecondMSBAux_lt2_w18 n n) hr4 f2 f3 f4 f5 f6 f7 t00 t01 t11

-- Helpers for `eventual_five_var_and_complete_3gram_exp_impossibility`:

private theorem add_one_pow_bernoulli_w18 (p : Nat) :
    ∀ j : Nat, p ^ (j + 1) + (j + 1) * p ^ j ≤ (p + 1) ^ (j + 1)
  | 0 => by rw [Nat.pow_one, Nat.pow_zero, Nat.pow_one, Nat.one_mul]; exact Nat.le_refl _
  | j + 1 => by
    have ih := Nat.mul_le_mul_right (p + 1) (add_one_pow_bernoulli_w18 p j)
    rw [← Nat.pow_succ (p + 1) (j + 1),
        Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_one,
        ← Nat.pow_succ p (j + 1),
        Nat.mul_assoc (j + 1) (p ^ j) p, ← Nat.pow_succ p j] at ih
    have h1 : (j + 2) * p ^ (j + 1) = p ^ (j + 1) + (j + 1) * p ^ (j + 1) := by
      rw [show j + 2 = 1 + (j + 1) by omega, Nat.add_mul, Nat.one_mul]
    rw [h1]
    generalize p ^ (j + 2) = A, p ^ (j + 1) = B, (j + 1) * p ^ (j + 1) = C,
      (j + 1) * p ^ j = D, (p + 1) ^ (j + 2) = E at ih ⊢
    omega

private theorem pow2_gt_self_w18 : ∀ c : Nat, c + 2 ≤ 2 ^ (c + 1)
  | 0 => by decide
  | c + 1 => by
    have ih := pow2_gt_self_w18 c
    rw [Nat.pow_succ 2 (c + 1)]
    omega

private theorem archimedean_pow_contra_w18 (p q C D : Nat)
    (hp : p ≥ 1) (hlt : p < q) (hD : D ≥ p * (C + 1))
    (hle : q ^ D ≤ C * p ^ D) : False := by
  have h1 : 2 * p ^ p ≤ (p + 1) ^ p := by
    cases p with
    | zero => omega
    | succ p' =>
      have hb := add_one_pow_bernoulli_w18 (p' + 1) p'
      have hmul : (p' + 1) * (p' + 1) ^ p' = (p' + 1) ^ (p' + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]
      rw [hmul, ← Nat.two_mul] at hb
      exact hb
  have hqp : 2 * p ^ p ≤ q ^ p :=
    Nat.le_trans h1 (pow_mono_base_w18s (p + 1) q hlt p)
  have hpowC : 2 ^ (C + 1) * p ^ (p * (C + 1)) ≤ q ^ (p * (C + 1)) := by
    calc 2 ^ (C + 1) * p ^ (p * (C + 1))
        = 2 ^ (C + 1) * (p ^ p) ^ (C + 1) := by rw [pow_pow_eq_mul_w5 p p (C + 1)]
      _ = (2 * p ^ p) ^ (C + 1) := (mul_pow_w18s 2 (p ^ p) (C + 1)).symm
      _ ≤ (q ^ p) ^ (C + 1) := pow_mono_base_w18s _ _ hqp (C + 1)
      _ = q ^ (p * (C + 1)) := pow_pow_eq_mul_w5 q p (C + 1)
  let r := D - p * (C + 1)
  have hD_sp : D = p * (C + 1) + r := by dsimp [r]; omega
  have hqr_ge : p ^ r ≤ q ^ r := pow_mono_base_w18s p q (Nat.le_of_lt hlt) r
  have hp_pos : p ^ (p * (C + 1)) ≥ 1 := nat_pow_pos_of_pos p hp _
  have hpr_pos : p ^ r ≥ 1 := nat_pow_pos_of_pos p hp r
  have hgt_base : C * p ^ (p * (C + 1)) < q ^ (p * (C + 1)) := by
    have h2c := pow2_gt_self_w18 C
    have hm := Nat.mul_le_mul_right (p ^ (p * (C + 1))) h2c
    rw [Nat.add_mul] at hm
    omega
  have hgt_D : C * p ^ D < q ^ D := by
    rw [hD_sp, Nat.pow_add q, Nat.pow_add p, ← Nat.mul_assoc C]
    exact Nat.lt_of_lt_of_le
      (Nat.mul_lt_mul_of_pos_right hgt_base hpr_pos)
      (Nat.mul_le_mul_left _ hqr_ge)
  omega

private theorem preimage_weight_mono_cutoff_w18 (M_0 M_1 : Nat) (hM : M_0 ≤ M_1)
    (wNum wDen : Nat -> Nat) (pTheta qTheta : Nat)
    (hw : IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta) :
    IsEventualPositiveRationalPreimageWeight M_1 wNum wDen pTheta qTheta := by
  rcases hw with ⟨hp, hpq, hpos, hev, hbr⟩
  exact ⟨hp, hpq,
    fun n hn => hpos n (Nat.le_trans hM hn),
    fun m hm hm3 => hev m (Nat.le_trans hM hm) hm3,
    fun m hm hm3 => hbr m (Nat.le_trans hM hm) hm3⟩

private theorem odd_branch_monomial_ratio_le_w18
    (M_0 : Nat) (wNum wDen MonHi MonLo : Nat -> Nat)
    (c_0 C_hi pTheta qTheta nOdd m : Nat)
    (hc0 : c_0 ≥ 1) (hn_ge : nOdd ≥ M_0) (hm_ge : m ≥ M_0)
    (hm3 : m % 3 = 2) (hstep : 3 * nOdd + 1 = 2 * m)
    (hlo_n : c_0 * MonLo nOdd * wDen nOdd ≤ MonHi nOdd * wNum nOdd)
    (hhi_m : MonHi m * wNum m ≤ C_hi * MonLo m * wDen m)
    (hw : IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta) :
    MonLo nOdd * MonHi m ≤ C_hi * MonHi nOdd * MonLo m := by
  rcases hw with ⟨hp_pos, hpq, hpos, _, hbr⟩
  have hdn_pos : wDen nOdd > 0 := (hpos nOdd hn_ge).2
  have hdm_pos : wDen m > 0 := (hpos m hm_ge).2
  have hd2m_pos : wDen (2 * m) > 0 := (hpos (2 * m) (by omega)).2
  have hb_step := hbr m hm_ge hm3
  dsimp only at hb_step
  have hn_eq : (2 * m - 1) / 3 = nOdd := by omega
  rw [hn_eq] at hb_step
  have hbr_simple : wNum nOdd * wDen m ≤ wNum m * wDen nOdd := by
    have h1 : pTheta * ((wNum nOdd * wDen m) * wDen (2 * m)) ≤
        qTheta * ((wNum (2 * m) * wDen nOdd + wNum nOdd * wDen (2 * m)) * wDen m) := by
      have hle_sum : (wNum nOdd * wDen m) * wDen (2 * m) ≤
          (wNum (2 * m) * wDen nOdd + wNum nOdd * wDen (2 * m)) * wDen m := by
        rw [Nat.add_mul]
        have hr : (wNum nOdd * wDen m) * wDen (2 * m) =
            (wNum nOdd * wDen (2 * m)) * wDen m := by ac_rfl
        rw [hr]
        exact Nat.le_add_left _ _
      exact Nat.mul_le_mul hpq hle_sum
    have h2 : pTheta * ((wNum m * wDen nOdd) * wDen (2 * m)) =
        pTheta * (wNum m * (wDen (2 * m) * wDen nOdd)) := by ac_rfl
    have h3 := Nat.le_trans h1 (h2.symm ▸ hb_step)
    have h4 := Nat.le_of_mul_le_mul_left h3 hp_pos
    exact Nat.le_of_mul_le_mul_right h4 hd2m_pos
  have hd_prod : wDen nOdd * wDen m > 0 := Nat.mul_pos hdn_pos hdm_pos
  apply Nat.le_of_mul_le_mul_right _ hd_prod
  calc (MonLo nOdd * MonHi m) * (wDen nOdd * wDen m)
      = (1 * MonLo nOdd * wDen nOdd) * (MonHi m * wDen m) := by ac_rfl
    _ ≤ (c_0 * MonLo nOdd * wDen nOdd) * (MonHi m * wDen m) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc0))
    _ ≤ (MonHi nOdd * wNum nOdd) * (MonHi m * wDen m) :=
          Nat.mul_le_mul_right _ hlo_n
    _ = (MonHi nOdd * MonHi m) * (wNum nOdd * wDen m) := by ac_rfl
    _ ≤ (MonHi nOdd * MonHi m) * (wNum m * wDen nOdd) :=
          Nat.mul_le_mul_left _ hbr_simple
    _ = MonHi nOdd * (MonHi m * wNum m) * wDen nOdd := by ac_rfl
    _ ≤ MonHi nOdd * (C_hi * MonLo m * wDen m) * wDen nOdd :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hhi_m)
    _ = (C_hi * MonHi nOdd * MonLo m) * (wDen nOdd * wDen m) := by ac_rfl

-- Universal multi-bit shift delta functions (`2 ^ k * x + r` for `x ≥ 2`, `r < 2 ^ k`):

private def shiftMod4W18 : Nat -> Nat -> Nat -> Nat
  | 0, c4, _ => c4 % 4
  | k + 1, c4, r => (2 * (shiftMod4W18 k c4 (r / 2) % 2) + r % 2) % 4

private def deltaPopW18 : Nat -> Nat -> Nat
  | 0, _ => 0
  | k + 1, r => r % 2 + deltaPopW18 k (r / 2)

private def deltaAltW18 : Nat -> Nat -> Nat -> Nat
  | 0, _, _ => 0
  | k + 1, c4, r =>
    let sm := shiftMod4W18 k c4 (r / 2)
    (if r % 2 != sm % 2 then 1 else 0) + deltaAltW18 k c4 (r / 2)

private def delta3GW18 (b2 b1 b0 : Nat) : Nat -> Nat -> Nat -> Nat
  | 0, _, _ => 0
  | k + 1, c4, r =>
    let sm := shiftMod4W18 k c4 (r / 2)
    (if ((sm / 2 == b2) && (sm % 2 == b1) && (r % 2 == b0)) then 1 else 0) +
      delta3GW18 b2 b1 b0 k c4 (r / 2)

private def shiftBitsStatsPropW18 (k x r : Nat) : Prop :=
  let v := 2 ^ k * x + r
  v ≥ 2 ∧
  v % 4 = shiftMod4W18 k (x % 4) r ∧
  binBitLength v = k + binBitLength x ∧
  binaryPopcount v = deltaPopW18 k r + binaryPopcount x ∧
  binaryAltTransitions v = deltaAltW18 k (x % 4) r + binaryAltTransitions x ∧
  binaryThreeGram001 v = delta3GW18 0 0 1 k (x % 4) r + binaryThreeGram001 x ∧
  binaryThreeGram111 v = delta3GW18 1 1 1 k (x % 4) r + binaryThreeGram111 x

private theorem shift_bits_stats_step_w18 (k x r : Nat)
    (ih : shiftBitsStatsPropW18 k x (r / 2)) :
    shiftBitsStatsPropW18 (k + 1) x r := by
  rcases ih with ⟨hu_ge2, hu_m4, hu_bl, hu_pop, hu_alt, hu_001, hu_111⟩
  let u := 2 ^ k * x + r / 2
  change u ≥ 2 at hu_ge2
  change u % 4 = shiftMod4W18 k (x % 4) (r / 2) at hu_m4
  change binBitLength u = k + binBitLength x at hu_bl
  change binaryPopcount u = deltaPopW18 k (r / 2) + binaryPopcount x at hu_pop
  change binaryAltTransitions u = deltaAltW18 k (x % 4) (r / 2) + binaryAltTransitions x at hu_alt
  change binaryThreeGram001 u = delta3GW18 0 0 1 k (x % 4) (r / 2) + binaryThreeGram001 x at hu_001
  change binaryThreeGram111 u = delta3GW18 1 1 1 k (x % 4) (r / 2) + binaryThreeGram111 x at hu_111
  unfold shiftBitsStatsPropW18
  dsimp only
  let v := 2 ^ (k + 1) * x + r
  have hv_eq : v = 2 * u + r % 2 := by
    dsimp [v, u]
    rw [Nat.pow_succ 2 k, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc 2 (2 ^ k) x]
    have hdm := (Nat.div_add_mod r 2).symm
    omega
  have hv_ge4 : v ≥ 4 := by omega
  have hv_div2 : v / 2 = u := by omega
  have hv_mod2 : v % 2 = r % 2 := by omega
  have hv_div4_m2 : (v / 4) % 2 = (u % 4) / 2 := by
    have hv4 : v / 4 = u / 2 := by omega
    have hu_dm4 := (Nat.div_add_mod u 4).symm
    have hum4_lt : u % 4 < 4 := Nat.mod_lt u (by decide)
    rw [hv4]; omega
  have hu_m2 : u % 2 = (u % 4) % 2 := by
    have hu_dm4 := (Nat.div_add_mod u 4).symm
    omega
  have hv_m4 : v % 4 = (2 * ((u % 4) % 2) + r % 2) % 4 := by
    rw [hv_eq, ← hu_m2]
    have hu_dm2 := (Nat.div_add_mod u 2).symm
    omega
  have hbl_v : binBitLength v = 1 + binBitLength u := by
    have h := binBitLength_step_succ_cf_w18 (v - 1)
    rw [show v - 1 + 1 = v by omega, hv_div2] at h
    exact h
  have hpop_v : binaryPopcount v = r % 2 + binaryPopcount u := by
    have h := binaryPopcount_step_succ_cf_w18 (v - 1)
    rw [show v - 1 + 1 = v by omega, hv_mod2, hv_div2] at h
    exact h
  have halt_v : binaryAltTransitions v =
      (if r % 2 != (u % 4) % 2 then 1 else 0) + binaryAltTransitions u := by
    have h := binaryAltTransitions_step_ge2_cf_w18 (v - 2)
    rw [show v - 2 + 2 = v by omega, hv_mod2, hv_div2, hu_m2] at h
    exact h
  have hg001_v : binaryThreeGram001 v =
      (if (((u % 4) / 2 == 0) && ((u % 4) % 2 == 0) && (r % 2 == 1)) then 1 else 0) +
        binaryThreeGram001 u := by
    unfold binaryThreeGram001
    have h := binaryThreeGram_step_ge4_cf_w18 0 0 1 (v - 4)
    rw [show v - 4 + 4 = v by omega, hv_div4_m2, hv_div2, hv_mod2, hu_m2] at h
    exact h
  have hg111_v : binaryThreeGram111 v =
      (if (((u % 4) / 2 == 1) && ((u % 4) % 2 == 1) && (r % 2 == 1)) then 1 else 0) +
        binaryThreeGram111 u := by
    unfold binaryThreeGram111
    have h := binaryThreeGram_step_ge4_cf_w18 1 1 1 (v - 4)
    rw [show v - 4 + 4 = v by omega, hv_div4_m2, hv_div2, hv_mod2, hu_m2] at h
    exact h
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change v % 4 = shiftMod4W18 (k + 1) (x % 4) r
    unfold shiftMod4W18
    rw [← hu_m4]; exact hv_m4
  · change binBitLength v = (k + 1) + binBitLength x
    rw [hbl_v, hu_bl]; omega
  · change binaryPopcount v = deltaPopW18 (k + 1) r + binaryPopcount x
    unfold deltaPopW18
    rw [hpop_v, hu_pop]; omega
  · change binaryAltTransitions v = deltaAltW18 (k + 1) (x % 4) r + binaryAltTransitions x
    unfold deltaAltW18; dsimp only
    rw [← hu_m4, halt_v, hu_alt]; omega
  · change binaryThreeGram001 v = delta3GW18 0 0 1 (k + 1) (x % 4) r + binaryThreeGram001 x
    unfold delta3GW18; dsimp only
    rw [← hu_m4, hg001_v, hu_001]; omega
  · change binaryThreeGram111 v = delta3GW18 1 1 1 (k + 1) (x % 4) r + binaryThreeGram111 x
    unfold delta3GW18; dsimp only
    rw [← hu_m4, hg111_v, hu_111]; omega

private theorem shift_bits_stats_w18 :
    ∀ (k x r : Nat), x ≥ 2 -> r < 2 ^ k -> shiftBitsStatsPropW18 k x r
  | 0, x, r, hx, hr => by
    have hr0 : r = 0 := by rw [Nat.pow_zero] at hr; omega
    subst hr0
    unfold shiftBitsStatsPropW18; dsimp only
    rw [Nat.pow_zero, Nat.one_mul, Nat.add_zero]
    exact ⟨hx, by simp [shiftMod4W18],
           by simp, by simp [deltaPopW18], by simp [deltaAltW18],
           by simp [delta3GW18], by simp [delta3GW18]⟩
  | k + 1, x, r, hx, hr =>
    shift_bits_stats_step_w18 k x r
      (shift_bits_stats_w18 k x (r / 2) hx (by rw [Nat.pow_succ] at hr; omega))

-- Four cardinal periodic Collatz `(nOdd, m)` preimage families (`s ≥ 1`):

private def fam1NOddW18 : Nat -> Nat
  | 0 => 1303
  | k + 1 => 2048 * fam1NOddW18 k + 1303

private def fam1MW18 : Nat -> Nat
  | 0 => 1955
  | k + 1 => 2048 * fam1MW18 k + 931

private def fam2NOddW18 : Nat -> Nat
  | 0 => 581
  | k + 1 => 1024 * fam2NOddW18 k + 581

private def fam2MW18 : Nat -> Nat
  | 0 => 872
  | k + 1 => 1024 * fam2MW18 k + 360

private def fam3NOddW18 : Nat -> Nat
  | 0 => 653
  | k + 1 => 1024 * fam3NOddW18 k + 653

private def fam3MW18 : Nat -> Nat
  | 0 => 980
  | k + 1 => 1024 * fam3MW18 k + 468

private def fam4NOddW18 : Nat -> Nat
  | 0 => 1291
  | k + 1 => 2048 * fam4NOddW18 k + 1291

private def fam4MW18 : Nat -> Nat
  | 0 => 1937
  | k + 1 => 2048 * fam4MW18 k + 913

private def fam1SpecPropW18 (k : Nat) : Prop :=
  let s := k + 1
  let n := fam1NOddW18 k
  let m := fam1MW18 k
  n ≥ 2048 ^ k * 1303 ∧
  m ≥ 2048 ^ k * 1955 ∧
  n % 4 = 3 ∧ m % 4 = 3 ∧ m % 3 = 2 ∧ 3 * n + 1 = 2 * m ∧
  binBitLength n = 11 * s ∧ binBitLength m = 11 * s ∧
  binaryPopcount n = 6 * s ∧ binaryPopcount m = 6 * s + 1 ∧
  binaryAltTransitions n = 6 * s ∧ binaryAltTransitions m = 6 * s - 2 ∧
  binaryThreeGram001 n = s ∧ binaryThreeGram001 m = s ∧
  binaryThreeGram111 n = 2 * s - 1 ∧ binaryThreeGram111 m = s + 1

private theorem fam1_spec_step_w18 (k : Nat) (ih : fam1SpecPropW18 k) : fam1SpecPropW18 (k + 1) := by
  unfold fam1SpecPropW18 at ih ⊢
  rcases ih with
      ⟨hn_lo, hm_lo, hn4, hm4, hm3, hstep, hLn, hLm, hPn, hPm, hTn, hTm, h001n, h001m, h111n, h111m⟩
  have hpk := nat_pow_pos_of_pos 2048 (by decide) k
  have hn_ge2 : fam1NOddW18 k ≥ 2 := by omega
  have hm_ge2 : fam1MW18 k ≥ 2 := by omega
  rcases shift_bits_stats_w18 11 (fam1NOddW18 k) 1303 hn_ge2 (by decide) with
    ⟨_, _, hLn', hPn', hTn', h001n', h111n'⟩
  rcases shift_bits_stats_w18 11 (fam1MW18 k) 931 hm_ge2 (by decide) with
    ⟨_, _, hLm', hPm', hTm', h001m', h111m'⟩
  dsimp only at hLn' hPn' hTn' h001n' h111n' hLm' hPm' hTm' h001m' h111m' ⊢
  change binBitLength (fam1NOddW18 (k + 1)) = _ at hLn'
  change binaryPopcount (fam1NOddW18 (k + 1)) = _ at hPn'
  change binaryAltTransitions (fam1NOddW18 (k + 1)) = _ at hTn'
  change binaryThreeGram001 (fam1NOddW18 (k + 1)) = _ at h001n'
  change binaryThreeGram111 (fam1NOddW18 (k + 1)) = _ at h111n'
  change binBitLength (fam1MW18 (k + 1)) = _ at hLm'
  change binaryPopcount (fam1MW18 (k + 1)) = _ at hPm'
  change binaryAltTransitions (fam1MW18 (k + 1)) = _ at hTm'
  change binaryThreeGram001 (fam1MW18 (k + 1)) = _ at h001m'
  change binaryThreeGram111 (fam1MW18 (k + 1)) = _ at h111m'
  rw [hn4] at hTn' h001n' h111n'
  rw [hm4] at hTm' h001m' h111m'
  have c1 : deltaPopW18 11 1303 = 6 := by decide
  have c2 : deltaAltW18 11 3 1303 = 6 := by decide
  have c3 : delta3GW18 0 0 1 11 3 1303 = 1 := by decide
  have c4 : delta3GW18 1 1 1 11 3 1303 = 2 := by decide
  have d1 : deltaPopW18 11 931 = 6 := by decide
  have d2 : deltaAltW18 11 3 931 = 6 := by decide
  have d3 : delta3GW18 0 0 1 11 3 931 = 1 := by decide
  have d4 : delta3GW18 1 1 1 11 3 931 = 1 := by decide
  rw [c1] at hPn'; rw [c2] at hTn'; rw [c3] at h001n'; rw [c4] at h111n'
  rw [d1] at hPm'; rw [d2] at hTm'; rw [d3] at h001m'; rw [d4] at h111m'
  have hn_lo' : fam1NOddW18 (k + 1) ≥ 2048 ^ (k + 1) * 1303 := by
    unfold fam1NOddW18
    rw [Nat.pow_succ 2048 k, Nat.mul_comm (2048 ^ k) 2048, Nat.mul_assoc]
    exact Nat.le_trans (Nat.mul_le_mul_left 2048 hn_lo) (Nat.le_add_right _ _)
  have hm_lo' : fam1MW18 (k + 1) ≥ 2048 ^ (k + 1) * 1955 := by
    unfold fam1MW18
    rw [Nat.pow_succ 2048 k, Nat.mul_comm (2048 ^ k) 2048, Nat.mul_assoc]
    exact Nat.le_trans (Nat.mul_le_mul_left 2048 hm_lo) (Nat.le_add_right _ _)
  rw [hLn', hLm', hPn', hPm', hTn', hTm', h001n', h001m', h111n', h111m',
      hLn, hLm, hPn, hPm, hTn, hTm, h001n, h001m, h111n, h111m]
  clear hLn hLm hPn hPm hTn hTm h001n h001m h111n h111m
  clear hLn' hLm' hPn' hPm' hTn' hTm' h001n' h001m' h111n' h111m'
  clear c1 c2 c3 c4 d1 d2 d3 d4 hpk hn_ge2 hm_ge2 hn_lo hm_lo
  refine ⟨hn_lo', hm_lo', ?_, ?_, ?_, ?_,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega⟩
  · unfold fam1NOddW18; omega
  · unfold fam1MW18; omega
  · unfold fam1MW18; omega
  · unfold fam1NOddW18 fam1MW18; omega

private theorem fam1_pos111_spec_w18 : ∀ k : Nat, fam1SpecPropW18 k
  | 0 => by unfold fam1SpecPropW18; decide
  | k + 1 => fam1_spec_step_w18 k (fam1_pos111_spec_w18 k)

private def fam2SpecPropW18 (k : Nat) : Prop :=
  let s := k + 1
  let n := fam2NOddW18 k
  let m := fam2MW18 k
  n ≥ 1024 ^ k * 581 ∧
  m ≥ 1024 ^ k * 872 ∧
  n % 4 = 1 ∧ m % 4 = 0 ∧ m % 3 = 2 ∧ 3 * n + 1 = 2 * m ∧
  binBitLength n = 10 * s ∧ binBitLength m = 10 * s ∧
  binaryPopcount n = 4 * s ∧ binaryPopcount m = 4 * s + 1 ∧
  binaryAltTransitions n = 6 * s ∧ binaryAltTransitions m = 6 * s - 1 ∧
  binaryThreeGram001 n = 2 * s ∧ binaryThreeGram001 m = s - 1 ∧
  binaryThreeGram111 n = 0 ∧ binaryThreeGram111 m = 0

private theorem fam2_spec_step_w18 (k : Nat) (ih : fam2SpecPropW18 k) : fam2SpecPropW18 (k + 1) := by
  unfold fam2SpecPropW18 at ih ⊢
  rcases ih with
      ⟨hn_lo, hm_lo, hn4, hm4, hm3, hstep, hLn, hLm, hPn, hPm, hTn, hTm, h001n, h001m, h111n, h111m⟩
  have hpk := nat_pow_pos_of_pos 1024 (by decide) k
  have hn_ge2 : fam2NOddW18 k ≥ 2 := by omega
  have hm_ge2 : fam2MW18 k ≥ 2 := by omega
  rcases shift_bits_stats_w18 10 (fam2NOddW18 k) 581 hn_ge2 (by decide) with
    ⟨_, _, hLn', hPn', hTn', h001n', h111n'⟩
  rcases shift_bits_stats_w18 10 (fam2MW18 k) 360 hm_ge2 (by decide) with
    ⟨_, _, hLm', hPm', hTm', h001m', h111m'⟩
  dsimp only at hLn' hPn' hTn' h001n' h111n' hLm' hPm' hTm' h001m' h111m' ⊢
  change binBitLength (fam2NOddW18 (k + 1)) = _ at hLn'
  change binaryPopcount (fam2NOddW18 (k + 1)) = _ at hPn'
  change binaryAltTransitions (fam2NOddW18 (k + 1)) = _ at hTn'
  change binaryThreeGram001 (fam2NOddW18 (k + 1)) = _ at h001n'
  change binaryThreeGram111 (fam2NOddW18 (k + 1)) = _ at h111n'
  change binBitLength (fam2MW18 (k + 1)) = _ at hLm'
  change binaryPopcount (fam2MW18 (k + 1)) = _ at hPm'
  change binaryAltTransitions (fam2MW18 (k + 1)) = _ at hTm'
  change binaryThreeGram001 (fam2MW18 (k + 1)) = _ at h001m'
  change binaryThreeGram111 (fam2MW18 (k + 1)) = _ at h111m'
  rw [hn4] at hTn' h001n' h111n'
  rw [hm4] at hTm' h001m' h111m'
  have c1 : deltaPopW18 10 581 = 4 := by decide
  have c2 : deltaAltW18 10 1 581 = 6 := by decide
  have c3 : delta3GW18 0 0 1 10 1 581 = 2 := by decide
  have c4 : delta3GW18 1 1 1 10 1 581 = 0 := by decide
  have d1 : deltaPopW18 10 360 = 4 := by decide
  have d2 : deltaAltW18 10 0 360 = 6 := by decide
  have d3 : delta3GW18 0 0 1 10 0 360 = 1 := by decide
  have d4 : delta3GW18 1 1 1 10 0 360 = 0 := by decide
  rw [c1] at hPn'; rw [c2] at hTn'; rw [c3] at h001n'; rw [c4] at h111n'
  rw [d1] at hPm'; rw [d2] at hTm'; rw [d3] at h001m'; rw [d4] at h111m'
  have hn_lo' : fam2NOddW18 (k + 1) ≥ 1024 ^ (k + 1) * 581 := by
    unfold fam2NOddW18
    rw [Nat.pow_succ 1024 k, Nat.mul_comm (1024 ^ k) 1024, Nat.mul_assoc]
    exact Nat.le_trans (Nat.mul_le_mul_left 1024 hn_lo) (Nat.le_add_right _ _)
  have hm_lo' : fam2MW18 (k + 1) ≥ 1024 ^ (k + 1) * 872 := by
    unfold fam2MW18
    rw [Nat.pow_succ 1024 k, Nat.mul_comm (1024 ^ k) 1024, Nat.mul_assoc]
    exact Nat.le_trans (Nat.mul_le_mul_left 1024 hm_lo) (Nat.le_add_right _ _)
  rw [hLn', hLm', hPn', hPm', hTn', hTm', h001n', h001m', h111n', h111m',
      hLn, hLm, hPn, hPm, hTn, hTm, h001n, h001m, h111n, h111m]
  clear hLn hLm hPn hPm hTn hTm h001n h001m h111n h111m
  clear hLn' hLm' hPn' hPm' hTn' hTm' h001n' h001m' h111n' h111m'
  clear c1 c2 c3 c4 d1 d2 d3 d4 hpk hn_ge2 hm_ge2 hn_lo hm_lo
  refine ⟨hn_lo', hm_lo', ?_, ?_, ?_, ?_,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega⟩
  · unfold fam2NOddW18; omega
  · unfold fam2MW18; omega
  · unfold fam2MW18; omega
  · unfold fam2NOddW18 fam2MW18; omega

private theorem fam2_pos001_spec_w18 : ∀ k : Nat, fam2SpecPropW18 k
  | 0 => by unfold fam2SpecPropW18; decide
  | k + 1 => fam2_spec_step_w18 k (fam2_pos001_spec_w18 k)

private def fam3SpecPropW18 (k : Nat) : Prop :=
  let s := k + 1
  let n := fam3NOddW18 k
  let m := fam3MW18 k
  n ≥ 1024 ^ k * 653 ∧
  m ≥ 1024 ^ k * 980 ∧
  n % 4 = 1 ∧ m % 4 = 0 ∧ m % 3 = 2 ∧ 3 * n + 1 = 2 * m ∧
  binBitLength n = 10 * s ∧ binBitLength m = 10 * s ∧
  binaryPopcount n = 5 * s ∧ binaryPopcount m = 5 * s + 1 ∧
  binaryAltTransitions n = 6 * s ∧ binaryAltTransitions m = 6 * s - 1 ∧
  binaryThreeGram001 n = s ∧ binaryThreeGram001 m = s - 1 ∧
  binaryThreeGram111 n = 0 ∧ binaryThreeGram111 m = s + 1

private theorem fam3_spec_step_w18 (k : Nat) (ih : fam3SpecPropW18 k) : fam3SpecPropW18 (k + 1) := by
  unfold fam3SpecPropW18 at ih ⊢
  rcases ih with
      ⟨hn_lo, hm_lo, hn4, hm4, hm3, hstep, hLn, hLm, hPn, hPm, hTn, hTm, h001n, h001m, h111n, h111m⟩
  have hpk := nat_pow_pos_of_pos 1024 (by decide) k
  have hn_ge2 : fam3NOddW18 k ≥ 2 := by omega
  have hm_ge2 : fam3MW18 k ≥ 2 := by omega
  rcases shift_bits_stats_w18 10 (fam3NOddW18 k) 653 hn_ge2 (by decide) with
    ⟨_, _, hLn', hPn', hTn', h001n', h111n'⟩
  rcases shift_bits_stats_w18 10 (fam3MW18 k) 468 hm_ge2 (by decide) with
    ⟨_, _, hLm', hPm', hTm', h001m', h111m'⟩
  dsimp only at hLn' hPn' hTn' h001n' h111n' hLm' hPm' hTm' h001m' h111m' ⊢
  change binBitLength (fam3NOddW18 (k + 1)) = _ at hLn'
  change binaryPopcount (fam3NOddW18 (k + 1)) = _ at hPn'
  change binaryAltTransitions (fam3NOddW18 (k + 1)) = _ at hTn'
  change binaryThreeGram001 (fam3NOddW18 (k + 1)) = _ at h001n'
  change binaryThreeGram111 (fam3NOddW18 (k + 1)) = _ at h111n'
  change binBitLength (fam3MW18 (k + 1)) = _ at hLm'
  change binaryPopcount (fam3MW18 (k + 1)) = _ at hPm'
  change binaryAltTransitions (fam3MW18 (k + 1)) = _ at hTm'
  change binaryThreeGram001 (fam3MW18 (k + 1)) = _ at h001m'
  change binaryThreeGram111 (fam3MW18 (k + 1)) = _ at h111m'
  rw [hn4] at hTn' h001n' h111n'
  rw [hm4] at hTm' h001m' h111m'
  have c1 : deltaPopW18 10 653 = 5 := by decide
  have c2 : deltaAltW18 10 1 653 = 6 := by decide
  have c3 : delta3GW18 0 0 1 10 1 653 = 1 := by decide
  have c4 : delta3GW18 1 1 1 10 1 653 = 0 := by decide
  have d1 : deltaPopW18 10 468 = 5 := by decide
  have d2 : deltaAltW18 10 0 468 = 6 := by decide
  have d3 : delta3GW18 0 0 1 10 0 468 = 1 := by decide
  have d4 : delta3GW18 1 1 1 10 0 468 = 1 := by decide
  rw [c1] at hPn'; rw [c2] at hTn'; rw [c3] at h001n'; rw [c4] at h111n'
  rw [d1] at hPm'; rw [d2] at hTm'; rw [d3] at h001m'; rw [d4] at h111m'
  have hn_lo' : fam3NOddW18 (k + 1) ≥ 1024 ^ (k + 1) * 653 := by
    unfold fam3NOddW18
    rw [Nat.pow_succ 1024 k, Nat.mul_comm (1024 ^ k) 1024, Nat.mul_assoc]
    exact Nat.le_trans (Nat.mul_le_mul_left 1024 hn_lo) (Nat.le_add_right _ _)
  have hm_lo' : fam3MW18 (k + 1) ≥ 1024 ^ (k + 1) * 980 := by
    unfold fam3MW18
    rw [Nat.pow_succ 1024 k, Nat.mul_comm (1024 ^ k) 1024, Nat.mul_assoc]
    exact Nat.le_trans (Nat.mul_le_mul_left 1024 hm_lo) (Nat.le_add_right _ _)
  rw [hLn', hLm', hPn', hPm', hTn', hTm', h001n', h001m', h111n', h111m',
      hLn, hLm, hPn, hPm, hTn, hTm, h001n, h001m, h111n, h111m]
  clear hLn hLm hPn hPm hTn hTm h001n h001m h111n h111m
  clear hLn' hLm' hPn' hPm' hTn' hTm' h001n' h001m' h111n' h111m'
  clear c1 c2 c3 c4 d1 d2 d3 d4 hpk hn_ge2 hm_ge2 hn_lo hm_lo
  refine ⟨hn_lo', hm_lo', ?_, ?_, ?_, ?_,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega⟩
  · unfold fam3NOddW18; omega
  · unfold fam3MW18; omega
  · unfold fam3MW18; omega
  · unfold fam3NOddW18 fam3MW18; omega

private theorem fam3_neg111_spec_w18 : ∀ k : Nat, fam3SpecPropW18 k
  | 0 => by unfold fam3SpecPropW18; decide
  | k + 1 => fam3_spec_step_w18 k (fam3_neg111_spec_w18 k)

private def fam4SpecPropW18 (k : Nat) : Prop :=
  let s := k + 1
  let n := fam4NOddW18 k
  let m := fam4MW18 k
  n ≥ 2048 ^ k * 1291 ∧
  m ≥ 2048 ^ k * 1937 ∧
  n % 4 = 3 ∧ m % 4 = 1 ∧ m % 3 = 2 ∧ 3 * n + 1 = 2 * m ∧
  binBitLength n = 11 * s ∧ binBitLength m = 11 * s ∧
  binaryPopcount n = 5 * s ∧ binaryPopcount m = 5 * s + 1 ∧
  binaryAltTransitions n = 6 * s ∧ binaryAltTransitions m = 6 * s - 2 ∧
  binaryThreeGram001 n = s ∧ binaryThreeGram001 m = 2 * s ∧
  binaryThreeGram111 n = s - 1 ∧ binaryThreeGram111 m = s + 1

private theorem fam4_spec_step_w18 (k : Nat) (ih : fam4SpecPropW18 k) : fam4SpecPropW18 (k + 1) := by
  unfold fam4SpecPropW18 at ih ⊢
  rcases ih with
      ⟨hn_lo, hm_lo, hn4, hm4, hm3, hstep, hLn, hLm, hPn, hPm, hTn, hTm, h001n, h001m, h111n, h111m⟩
  have hpk := nat_pow_pos_of_pos 2048 (by decide) k
  have hn_ge2 : fam4NOddW18 k ≥ 2 := by omega
  have hm_ge2 : fam4MW18 k ≥ 2 := by omega
  rcases shift_bits_stats_w18 11 (fam4NOddW18 k) 1291 hn_ge2 (by decide) with
    ⟨_, _, hLn', hPn', hTn', h001n', h111n'⟩
  rcases shift_bits_stats_w18 11 (fam4MW18 k) 913 hm_ge2 (by decide) with
    ⟨_, _, hLm', hPm', hTm', h001m', h111m'⟩
  dsimp only at hLn' hPn' hTn' h001n' h111n' hLm' hPm' hTm' h001m' h111m' ⊢
  change binBitLength (fam4NOddW18 (k + 1)) = _ at hLn'
  change binaryPopcount (fam4NOddW18 (k + 1)) = _ at hPn'
  change binaryAltTransitions (fam4NOddW18 (k + 1)) = _ at hTn'
  change binaryThreeGram001 (fam4NOddW18 (k + 1)) = _ at h001n'
  change binaryThreeGram111 (fam4NOddW18 (k + 1)) = _ at h111n'
  change binBitLength (fam4MW18 (k + 1)) = _ at hLm'
  change binaryPopcount (fam4MW18 (k + 1)) = _ at hPm'
  change binaryAltTransitions (fam4MW18 (k + 1)) = _ at hTm'
  change binaryThreeGram001 (fam4MW18 (k + 1)) = _ at h001m'
  change binaryThreeGram111 (fam4MW18 (k + 1)) = _ at h111m'
  rw [hn4] at hTn' h001n' h111n'
  rw [hm4] at hTm' h001m' h111m'
  have c1 : deltaPopW18 11 1291 = 5 := by decide
  have c2 : deltaAltW18 11 3 1291 = 6 := by decide
  have c3 : delta3GW18 0 0 1 11 3 1291 = 1 := by decide
  have c4 : delta3GW18 1 1 1 11 3 1291 = 1 := by decide
  have d1 : deltaPopW18 11 913 = 5 := by decide
  have d2 : deltaAltW18 11 1 913 = 6 := by decide
  have d3 : delta3GW18 0 0 1 11 1 913 = 2 := by decide
  have d4 : delta3GW18 1 1 1 11 1 913 = 1 := by decide
  rw [c1] at hPn'; rw [c2] at hTn'; rw [c3] at h001n'; rw [c4] at h111n'
  rw [d1] at hPm'; rw [d2] at hTm'; rw [d3] at h001m'; rw [d4] at h111m'
  have hn_lo' : fam4NOddW18 (k + 1) ≥ 2048 ^ (k + 1) * 1291 := by
    unfold fam4NOddW18
    rw [Nat.pow_succ 2048 k, Nat.mul_comm (2048 ^ k) 2048, Nat.mul_assoc]
    exact Nat.le_trans (Nat.mul_le_mul_left 2048 hn_lo) (Nat.le_add_right _ _)
  have hm_lo' : fam4MW18 (k + 1) ≥ 2048 ^ (k + 1) * 1937 := by
    unfold fam4MW18
    rw [Nat.pow_succ 2048 k, Nat.mul_comm (2048 ^ k) 2048, Nat.mul_assoc]
    exact Nat.le_trans (Nat.mul_le_mul_left 2048 hm_lo) (Nat.le_add_right _ _)
  rw [hLn', hLm', hPn', hPm', hTn', hTm', h001n', h001m', h111n', h111m',
      hLn, hLm, hPn, hPm, hTn, hTm, h001n, h001m, h111n, h111m]
  clear hLn hLm hPn hPm hTn hTm h001n h001m h111n h111m
  clear hLn' hLm' hPn' hPm' hTn' hTm' h001n' h001m' h111n' h111m'
  clear c1 c2 c3 c4 d1 d2 d3 d4 hpk hn_ge2 hm_ge2 hn_lo hm_lo
  refine ⟨hn_lo', hm_lo', ?_, ?_, ?_, ?_,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega,
          by clear hn_lo' hm_lo' hn4 hm4 hm3 hstep; omega⟩
  · unfold fam4NOddW18; omega
  · unfold fam4MW18; omega
  · unfold fam4MW18; omega
  · unfold fam4NOddW18 fam4MW18; omega

private theorem fam4_neg001_spec_w18 : ∀ k : Nat, fam4SpecPropW18 k
  | 0 => by unfold fam4SpecPropW18; decide
  | k + 1 => fam4_spec_step_w18 k (fam4_neg001_spec_w18 k)

private theorem base_ge2_gt_self_w18 (B : Nat) (hB : B ≥ 2) : ∀ k : Nat, k + 1 ≤ B ^ k
  | 0 => by simp
  | k + 1 => by
    have ih := base_ge2_gt_self_w18 B hB k
    calc k + 2 ≤ (k + 1) * 2 := by omega
      _ ≤ B ^ k * B := Nat.mul_le_mul ih hB
      _ = B ^ (k + 1) := (Nat.pow_succ B k).symm

private theorem sq_four_w18 (a0 a1 a2 a3 : Nat) :
    (a0 * a1 * a2 * a3) * (a0 * a1 * a2 * a3) =
    (a0 * a0) * (a1 * a1) * (a2 * a2) * (a3 * a3) := by ac_rfl

private theorem regroup_eight_sq_five_w18
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 y0 b2 y2 b3 y3 b5 y5 b6 y6 : Nat) :
    ((a0 * a1 * a2 * a3 * a4 * a5 * a6 * a7) *
     (a0 * a1 * a2 * a3 * a4 * a5 * a6 * a7)) *
    ((b0 * y0) * (b2 * y2) * (b3 * y3) * (b5 * y5) * (b6 * y6)) =
    ((a0 * a0 * b0) * (a1 * a1) * (a2 * a2 * b2) * (a3 * a3 * b3) *
     (a4 * a4) * (a5 * a5 * b5) * (a6 * a6 * b6) * (a7 * a7)) *
    (y0 * y2 * y3 * y5 * y6) := by
  have hsp8 : a0 * a1 * a2 * a3 * a4 * a5 * a6 * a7 =
      (a0 * a1 * a2 * a3) * (a4 * a5 * a6 * a7) := by simp only [Nat.mul_assoc]
  rw [hsp8]
  have h2 : ((a0 * a1 * a2 * a3) * (a4 * a5 * a6 * a7)) *
      ((a0 * a1 * a2 * a3) * (a4 * a5 * a6 * a7)) =
      ((a0 * a1 * a2 * a3) * (a0 * a1 * a2 * a3)) *
      ((a4 * a5 * a6 * a7) * (a4 * a5 * a6 * a7)) := by
    generalize a0 * a1 * a2 * a3 = U, a4 * a5 * a6 * a7 = V; ac_rfl
  rw [h2, sq_four_w18 a0 a1 a2 a3, sq_four_w18 a4 a5 a6 a7]
  generalize a0 * a0 = s0, a1 * a1 = s1, a2 * a2 = s2, a3 * a3 = s3,
             a4 * a4 = s4, a5 * a5 = s5, a6 * a6 = s6, a7 * a7 = s7
  have hxy1 : (b0 * y0) * (b2 * y2) * (b3 * y3) = (b0 * b2 * b3) * (y0 * y2 * y3) := by ac_rfl
  have hxy2 : (b5 * y5) * (b6 * y6) = (b5 * b6) * (y5 * y6) := by ac_rfl
  have hxy : (b0 * y0) * (b2 * y2) * (b3 * y3) * (b5 * y5) * (b6 * y6) =
      ((b0 * b2 * b3) * (b5 * b6)) * ((y0 * y2 * y3) * (y5 * y6)) := by
    rw [show (b0 * y0) * (b2 * y2) * (b3 * y3) * (b5 * y5) * (b6 * y6) =
        ((b0 * y0) * (b2 * y2) * (b3 * y3)) * ((b5 * y5) * (b6 * y6)) by simp only [Nat.mul_assoc],
        hxy1, hxy2]
    generalize b0 * b2 * b3 = B1, y0 * y2 * y3 = Y1, b5 * b6 = B2, y5 * y6 = Y2; ac_rfl
  rw [hxy, show y0 * y2 * y3 * y5 * y6 = (y0 * y2 * y3) * (y5 * y6) by simp only [Nat.mul_assoc],
      ← Nat.mul_assoc]
  apply congrArg (· * ((y0 * y2 * y3) * (y5 * y6)))
  have hl : (s0 * s1 * s2 * s3) * (b0 * b2 * b3) =
      (s0 * b0) * s1 * (s2 * b2) * (s3 * b3) := by ac_rfl
  have hr : (s4 * s5 * s6 * s7) * (b5 * b6) =
      s4 * (s5 * b5) * (s6 * b6) * s7 := by ac_rfl
  have hm : ((s0 * s1 * s2 * s3) * (s4 * s5 * s6 * s7)) * ((b0 * b2 * b3) * (b5 * b6)) =
      ((s0 * s1 * s2 * s3) * (b0 * b2 * b3)) * ((s4 * s5 * s6 * s7) * (b5 * b6)) := by
    generalize s0 * s1 * s2 * s3 = S1, s4 * s5 * s6 * s7 = S2,
               b0 * b2 * b3 = B1, b5 * b6 = B2; ac_rfl
  rw [hm, hl, hr]; simp only [Nat.mul_assoc]

private theorem regroup_u_blocks_w18
    (L0 r0 G0a Ta Ha r2 Pa r3 G0b r4 Tb r5 Pb r6 Hb : Nat) :
    (L0 * r0) * G0a * (Ta * Ha * r2) * (Pa * r3) * (G0b * r4) * (Tb * r5) * (Pb * r6) * Hb =
    (L0 * (Pa * Pb) * (Ta * Tb) * (G0a * G0b) * (Ha * Hb)) *
    (r0 * r2 * r3 * r4 * r5 * r6) := by
  have h1 :
      (L0 * r0) * G0a * (Ta * Ha * r2) * (Pa * r3) =
      (L0 * Pa * Ta * G0a * Ha) * (r0 * r2 * r3) := by ac_rfl
  have h2 :
      (G0b * r4) * (Tb * r5) * (Pb * r6) * Hb =
      (Pb * Tb * G0b * Hb) * (r4 * r5 * r6) := by ac_rfl
  have hsplit :
      (L0 * r0) * G0a * (Ta * Ha * r2) * (Pa * r3) * (G0b * r4) * (Tb * r5) * (Pb * r6) * Hb =
      ((L0 * r0) * G0a * (Ta * Ha * r2) * (Pa * r3)) *
      ((G0b * r4) * (Tb * r5) * (Pb * r6) * Hb) := by simp only [Nat.mul_assoc]
  rw [hsplit, h1, h2, show r0 * r2 * r3 * r4 * r5 * r6 = (r0 * r2 * r3) * (r4 * r5 * r6) by simp only [Nat.mul_assoc]]
  generalize r0 * r2 * r3 = R1, r4 * r5 * r6 = R2
  have h3 :
      ((L0 * Pa * Ta * G0a * Ha) * R1) * ((Pb * Tb * G0b * Hb) * R2) =
      ((L0 * Pa * Ta * G0a * Ha) * (Pb * Tb * G0b * Hb)) * (R1 * R2) := by
    generalize L0 * Pa * Ta * G0a * Ha = U1, Pb * Tb * G0b * Hb = U2; ac_rfl
  rw [h3]
  apply congrArg (· * (R1 * R2))
  ac_rfl

private theorem regroup_v_blocks_w18
    (Pc Tc G0c c0 Pd Td Hc c3 G0d c5 Te Hd c6 : Nat) :
    (Pc * Tc * G0c * c0) * Pd * (Td * Hc * c3) * (G0d * c5) * (Te * Hd * c6) =
    ((Pc * Pd) * (Tc * Td * Te) * (G0c * G0d) * (Hc * Hd)) * (c0 * c3 * c5 * c6) := by
  have h1 :
      (Pc * Tc * G0c * c0) * Pd * (Td * Hc * c3) =
      ((Pc * Pd) * (Tc * Td) * G0c * Hc) * (c0 * c3) := by ac_rfl
  have h2 :
      (G0d * c5) * (Te * Hd * c6) = (Te * G0d * Hd) * (c5 * c6) := by ac_rfl
  have hsplit :
      (Pc * Tc * G0c * c0) * Pd * (Td * Hc * c3) * (G0d * c5) * (Te * Hd * c6) =
      ((Pc * Tc * G0c * c0) * Pd * (Td * Hc * c3)) * ((G0d * c5) * (Te * Hd * c6)) := by
    simp only [Nat.mul_assoc]
  rw [hsplit, h1, h2, show c0 * c3 * c5 * c6 = (c0 * c3) * (c5 * c6) by simp only [Nat.mul_assoc]]
  generalize Pc * Pd = Pcd, c0 * c3 = C1, c5 * c6 = C2
  have h3 :
      ((Pcd * (Tc * Td) * G0c * Hc) * C1) * ((Te * G0d * Hd) * C2) =
      ((Pcd * (Tc * Td) * G0c * Hc) * (Te * G0d * Hd)) * (C1 * C2) := by
    generalize Pcd * (Tc * Td) * G0c * Hc = V1, Te * G0d * Hd = V2; ac_rfl
  rw [h3]
  apply congrArg (· * (C1 * C2))
  ac_rfl

private theorem regroup_uv_merge_w18
    (L0 P1 T1 G1 H1 R P2 T2 G2 H2 C : Nat) :
    ((L0 * P1 * T1 * G1 * H1) * R) * ((P2 * T2 * G2 * H2) * C) =
    (L0 * (P1 * P2) * (T1 * T2) * (G1 * G2) * (H1 * H2)) * (C * R) := by
  have h1 :
      ((L0 * P1 * T1 * G1 * H1) * R) * ((P2 * T2 * G2 * H2) * C) =
      ((L0 * P1 * T1 * G1 * H1) * (P2 * T2 * G2 * H2)) * (C * R) := by
    generalize L0 * P1 * T1 * G1 * H1 = U, P2 * T2 * G2 * H2 = V; ac_rfl
  rw [h1]
  apply congrArg (· * (C * R))
  ac_rfl

private theorem pair5_prod_w18 (a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 : Nat) :
    (b0 * a1 * a2 * a3 * a4) * (a0 * b1 * b2 * b3 * b4) =
    (a0 * b0) * (a1 * b1) * (a2 * b2) * (a3 * b3) * (a4 * b4) := by
  have h1 : (b0 * a1 * a2) * (a0 * b1 * b2) = (a0 * b0) * (a1 * b1) * (a2 * b2) := by ac_rfl
  have h2 : (a3 * a4) * (b3 * b4) = (a3 * b3) * (a4 * b4) := by ac_rfl
  have hsp : (b0 * a1 * a2 * a3 * a4) * (a0 * b1 * b2 * b3 * b4) =
      ((b0 * a1 * a2) * (a0 * b1 * b2)) * ((a3 * a4) * (b3 * b4)) := by
    rw [show b0 * a1 * a2 * a3 * a4 = (b0 * a1 * a2) * (a3 * a4) by simp only [Nat.mul_assoc],
        show a0 * b1 * b2 * b3 * b4 = (a0 * b1 * b2) * (b3 * b4) by simp only [Nat.mul_assoc]]
    generalize b0 * a1 * a2 = X1, a3 * a4 = X2, a0 * b1 * b2 = Y1, b3 * b4 = Y2; ac_rfl
  rw [hsp, h1, h2]; simp only [Nat.mul_assoc]

private theorem pair4_prod_w18 (a0 b0 a1 b1 a2 b2 a3 b3 : Nat) :
    (b0 * a1 * a2 * a3) * (a0 * b1 * b2 * b3) =
    (a0 * b0) * (a1 * b1) * (a2 * b2) * (a3 * b3) := by
  have h1 : (b0 * a1) * (a0 * b1) = (a0 * b0) * (a1 * b1) := by ac_rfl
  have h2 : (a2 * a3) * (b2 * b3) = (a2 * b2) * (a3 * b3) := by ac_rfl
  have hsp : (b0 * a1 * a2 * a3) * (a0 * b1 * b2 * b3) =
      ((b0 * a1) * (a0 * b1)) * ((a2 * a3) * (b2 * b3)) := by
    rw [show b0 * a1 * a2 * a3 = (b0 * a1) * (a2 * a3) by simp only [Nat.mul_assoc],
        show a0 * b1 * b2 * b3 = (a0 * b1) * (b2 * b3) by simp only [Nat.mul_assoc]]
    generalize b0 * a1 = X1, a2 * a3 = X2, a0 * b1 = Y1, b2 * b3 = Y2; ac_rfl
  rw [hsp, h1, h2]; simp only [Nat.mul_assoc]

private theorem cancel_fam1_lhs_w18 (pL qL pP qP pT qT p0 q0 p1 q1 pT2 qP1 p1D : Nat) :
    (qL * pP * (pT * pT2) * p0 * (p1 * p1D)) * (pL * (qP * qP1) * qT * q0 * q1) =
    (qP1 * pT2 * p1D) * ((pL * qL) * (pP * qP) * (pT * qT) * (p0 * q0) * (p1 * q1)) := by
  have h1 : qL * pP * (pT * pT2) * p0 * (p1 * p1D) = (pT2 * p1D) * (qL * pP * pT * p0 * p1) := by
    have ha : qL * pP * (pT * pT2) = pT2 * (qL * pP * pT) := by ac_rfl
    rw [ha]; generalize qL * pP * pT = A; ac_rfl
  have h2 : pL * (qP * qP1) * qT * q0 * q1 = qP1 * (pL * qP * qT * q0 * q1) := by
    have hb : pL * (qP * qP1) = qP1 * (pL * qP) := by ac_rfl
    rw [hb]; simp only [Nat.mul_assoc]
  rw [h1, h2]
  have h3 : ((pT2 * p1D) * (qL * pP * pT * p0 * p1)) * (qP1 * (pL * qP * qT * q0 * q1)) =
      (qP1 * pT2 * p1D) * ((qL * pP * pT * p0 * p1) * (pL * qP * qT * q0 * q1)) := by
    generalize qL * pP * pT * p0 * p1 = U, pL * qP * qT * q0 * q1 = V; ac_rfl
  rw [h3, pair5_prod_w18]

private theorem cancel_fam1_rhs_w18 (Chi pL qL pP qP pT qT p0 q0 p1 q1 pP1 qT2 q1D : Nat) :
    Chi * (pL * qP * (qT * qT2) * q0 * (q1 * q1D)) * (qL * (pP * pP1) * pT * p0 * p1) =
    ((Chi * pP1 * qT2) * q1D) * ((pL * qL) * (pP * qP) * (pT * qT) * (p0 * q0) * (p1 * q1)) := by
  have h0 := cancel_fam1_lhs_w18 qL pL qP pP qT pT q0 p0 q1 p1 qT2 pP1 q1D
  rw [Nat.mul_assoc Chi, h0,
      Nat.mul_comm qL pL, Nat.mul_comm qP pP, Nat.mul_comm qT pT,
      Nat.mul_comm q0 p0, Nat.mul_comm q1 p1]
  generalize (pL * qL) * (pP * qP) * (pT * qT) * (p0 * q0) * (p1 * q1) = B; ac_rfl

private theorem cancel_fam3_lhs_w18 (pL qL pP qP pT qT p0 q0 pT1 p01 qP1 q1D : Nat) :
    (qL * pP * (pT * pT1) * (p0 * p01)) * (pL * (qP * qP1) * qT * q0 * q1D) =
    (qP1 * pT1 * p01 * q1D) * ((pL * qL) * (pP * qP) * (pT * qT) * (p0 * q0)) := by
  have h1 : qL * pP * (pT * pT1) * (p0 * p01) = (pT1 * p01) * (qL * pP * pT * p0) := by
    have ha : qL * pP * (pT * pT1) = pT1 * (qL * pP * pT) := by ac_rfl
    rw [ha]; generalize qL * pP * pT = A; ac_rfl
  have h2 : pL * (qP * qP1) * qT * q0 * q1D = (qP1 * q1D) * (pL * qP * qT * q0) := by
    have hb : pL * (qP * qP1) = qP1 * (pL * qP) := by ac_rfl
    rw [hb]; generalize pL * qP = B; ac_rfl
  rw [h1, h2]
  have h3 : ((pT1 * p01) * (qL * pP * pT * p0)) * ((qP1 * q1D) * (pL * qP * qT * q0)) =
      (qP1 * pT1 * p01 * q1D) * ((qL * pP * pT * p0) * (pL * qP * qT * q0)) := by
    generalize qL * pP * pT * p0 = U, pL * qP * qT * q0 = V; ac_rfl
  rw [h3, pair4_prod_w18 pL qL pP qP pT qT p0 q0]

private theorem cancel_fam3_rhs_w18 (Chi pL qL pP qP pT qT p0 q0 qT1 q01 pP1 p1D : Nat) :
    Chi * (pL * qP * (qT * qT1) * (q0 * q01)) * (qL * (pP * pP1) * pT * p0 * p1D) =
    ((Chi * pP1 * qT1 * q01) * p1D) * ((pL * qL) * (pP * qP) * (pT * qT) * (p0 * q0)) := by
  have h0 := cancel_fam3_lhs_w18 qL pL qP pP qT pT q0 p0 qT1 q01 pP1 p1D
  rw [Nat.mul_assoc Chi, h0,
      Nat.mul_comm qL pL, Nat.mul_comm qP pP, Nat.mul_comm qT pT, Nat.mul_comm q0 p0]
  generalize (pL * qL) * (pP * qP) * (pT * qT) * (p0 * q0) = B; ac_rfl

private theorem cancel_fam2_lhs_w18 (pL qL pP qP pT qT p0 q0 pT1 p0D qP1 : Nat) :
    (qL * pP * (pT * pT1) * (p0 * p0D)) * (pL * (qP * qP1) * qT * q0) =
    (qP1 * pT1 * p0D) * ((pL * qL) * (pP * qP) * (pT * qT) * (p0 * q0)) := by
  have h0 := cancel_fam3_lhs_w18 pL qL pP qP pT qT p0 q0 pT1 p0D qP1 1
  simpa only [Nat.mul_one] using h0

private theorem cancel_fam2_rhs_w18 (Chi pL qL pP qP pT qT p0 q0 qT1 q0D pP1 : Nat) :
    Chi * (pL * qP * (qT * qT1) * (q0 * q0D)) * (qL * (pP * pP1) * pT * p0) =
    ((Chi * pP1 * qT1) * q0D) * ((pL * qL) * (pP * qP) * (pT * qT) * (p0 * q0)) := by
  have h0 := cancel_fam3_rhs_w18 Chi pL qL pP qP pT qT p0 q0 qT1 q0D pP1 1
  simpa only [Nat.mul_one] using h0

private theorem cancel_fam4_lhs_w18 (pL qL pP qP pT qT p0 q0 p1 pT2 qP1 q0s p12 : Nat) :
    (qL * pP * (pT * pT2) * p0 * p1) * (pL * (qP * qP1) * qT * (q0 * q0s) * (p1 * p12)) =
    (qP1 * pT2 * p12 * q0s) * ((pL * qL) * (pP * qP) * (pT * qT) * (p0 * q0) * (p1 * p1)) := by
  have h1 : qL * pP * (pT * pT2) * p0 * p1 = pT2 * (qL * pP * pT * p0 * p1) := by
    have ha : qL * pP * (pT * pT2) = pT2 * (qL * pP * pT) := by ac_rfl
    rw [ha]; simp only [Nat.mul_assoc]
  have h2 : pL * (qP * qP1) * qT * (q0 * q0s) * (p1 * p12) =
      (qP1 * q0s * p12) * (pL * qP * qT * q0 * p1) := by
    have hb : pL * (qP * qP1) * qT = qP1 * (pL * qP * qT) := by ac_rfl
    rw [hb]; generalize pL * qP * qT = B; ac_rfl
  rw [h1, h2]
  have h3 : (pT2 * (qL * pP * pT * p0 * p1)) * ((qP1 * q0s * p12) * (pL * qP * qT * q0 * p1)) =
      (qP1 * pT2 * p12 * q0s) * ((qL * pP * pT * p0 * p1) * (pL * qP * qT * q0 * p1)) := by
    generalize qL * pP * pT * p0 * p1 = U, pL * qP * qT * q0 * p1 = V; ac_rfl
  rw [h3, pair5_prod_w18]

private theorem cancel_fam4_rhs_w18 (Chi pL qL pP qP pT qT p0 q0 p1 qT2 pP1 p0s p12 : Nat) :
    Chi * (pL * qP * (qT * qT2) * q0 * p1) * (qL * (pP * pP1) * pT * (p0 * p0s) * (p1 * p12)) =
    ((Chi * pP1 * qT2 * p12) * p0s) * ((pL * qL) * (pP * qP) * (pT * qT) * (p0 * q0) * (p1 * p1)) := by
  have h0 := cancel_fam4_lhs_w18 qL pL qP pP qT pT q0 p0 p1 qT2 pP1 p0s p12
  rw [Nat.mul_assoc Chi, h0,
      Nat.mul_comm qL pL, Nat.mul_comm qP pP, Nat.mul_comm qT pT, Nat.mul_comm q0 p0]
  generalize (pL * qL) * (pP * qP) * (pT * qT) * (p0 * q0) * (p1 * p1) = B; ac_rfl

private theorem five_var_not_q111_lt_w18 (M_0 : Nat) (wNum wDen : Nat -> Nat)
    (c_0 C_hi p_L q_L p_P q_P p_T q_T p_001 q_001 p_111 q_111 pTheta qTheta : Nat)
    (hc0 : c_0 ≥ 1) (hpL : p_L ≥ 1) (hqL : q_L ≥ 1) (hpP : p_P ≥ 1) (hqP : q_P ≥ 1)
    (hpT : p_T ≥ 1) (hqT : q_T ≥ 1) (hp001 : p_001 ≥ 1) (hq001 : q_001 ≥ 1)
    (hp111 : p_111 ≥ 1) (hq111 : q_111 ≥ 1)
    (hsand : ∀ n : Nat, n ≥ M_0 ->
      c_0 * (q_L ^ binBitLength n * p_P ^ binaryPopcount n * p_T ^ binaryAltTransitions n *
          p_001 ^ binaryThreeGram001 n * p_111 ^ binaryThreeGram111 n) * wDen n ≤
        (p_L ^ binBitLength n * q_P ^ binaryPopcount n * q_T ^ binaryAltTransitions n *
          q_001 ^ binaryThreeGram001 n * q_111 ^ binaryThreeGram111 n) * wNum n ∧
      (p_L ^ binBitLength n * q_P ^ binaryPopcount n * q_T ^ binaryAltTransitions n *
          q_001 ^ binaryThreeGram001 n * q_111 ^ binaryThreeGram111 n) * wNum n ≤
        C_hi * (q_L ^ binBitLength n * p_P ^ binaryPopcount n * p_T ^ binaryAltTransitions n *
          p_001 ^ binaryThreeGram001 n * p_111 ^ binaryThreeGram111 n) * wDen n)
    (hw : IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta) :
    ¬ (q_111 < p_111) := by
  intro hlt
  let MonLo : Nat -> Nat := fun n =>
    q_L ^ binBitLength n * p_P ^ binaryPopcount n * p_T ^ binaryAltTransitions n *
      p_001 ^ binaryThreeGram001 n * p_111 ^ binaryThreeGram111 n
  let MonHi : Nat -> Nat := fun n =>
    p_L ^ binBitLength n * q_P ^ binaryPopcount n * q_T ^ binaryAltTransitions n *
      q_001 ^ binaryThreeGram001 n * q_111 ^ binaryThreeGram111 n
  let C1 := C_hi * p_P * (q_T * q_T)
  let k := M_0 + q_111 * (C1 + 1) + 3
  let s := k + 1
  rcases fam1_pos111_spec_w18 k with
    ⟨hn_lo, hm_lo, _, _, hm3, hstep, hLn, hLm, hPn, hPm, hTn, hTm, h001n, h001m, h111n, h111m⟩
  let n := fam1NOddW18 k
  let m := fam1MW18 k
  have hgk := base_ge2_gt_self_w18 2048 (by decide) k
  have hn_ge : n ≥ M_0 := by dsimp [n, k] at hn_lo hgk ⊢; omega
  have hm_ge : m ≥ M_0 := by dsimp [m, k] at hm_lo hgk ⊢; omega
  have hrat := odd_branch_monomial_ratio_le_w18 M_0 wNum wDen MonHi MonLo c_0 C_hi pTheta qTheta n m
    hc0 hn_ge hm_ge hm3 hstep (hsand n hn_ge).1 (hsand m hm_ge).2 hw
  dsimp only [MonLo, MonHi] at hrat
  let L0 := 11 * s
  let P0 := 6 * s
  let T0 := 6 * s - 2
  let G1 := s + 1
  let D := s - 2
  have hLn' : binBitLength n = L0 := hLn
  have hLm' : binBitLength m = L0 := hLm
  have hPn' : binaryPopcount n = P0 := hPn
  have hPm' : binaryPopcount m = P0 + 1 := hPm
  have hTn' : binaryAltTransitions n = T0 + 2 := by rw [hTn]; dsimp [T0, s, k]; omega
  have hTm' : binaryAltTransitions m = T0 := hTm
  have h001n' : binaryThreeGram001 n = s := h001n
  have h001m' : binaryThreeGram001 m = s := h001m
  have h111n' : binaryThreeGram111 n = G1 + D := by rw [h111n]; dsimp [G1, D, s, k]; omega
  have h111m' : binaryThreeGram111 m = G1 := h111m
  rw [hLn', hLm', hPn', hPm', hTn', hTm', h001n', h001m', h111n', h111m',
      Nat.pow_add p_P P0 1, Nat.pow_add q_P P0 1, Nat.pow_one p_P, Nat.pow_one q_P,
      Nat.pow_add p_T T0 2, Nat.pow_add q_T T0 2,
      show p_T ^ 2 = p_T * p_T by rw [Nat.pow_succ, Nat.pow_one],
      show q_T ^ 2 = q_T * q_T by rw [Nat.pow_succ, Nat.pow_one],
      Nat.pow_add p_111 G1 D, Nat.pow_add q_111 G1 D] at hrat
  let Base := (p_L ^ L0 * q_L ^ L0) * (p_P ^ P0 * q_P ^ P0) *
    (p_T ^ T0 * q_T ^ T0) * (p_001 ^ s * q_001 ^ s) * (p_111 ^ G1 * q_111 ^ G1)
  have hBase_pos : Base > 0 :=
    Nat.mul_pos
      (Nat.mul_pos
        (Nat.mul_pos
          (Nat.mul_pos
            (Nat.mul_pos (nat_pow_pos_of_pos _ hpL _) (nat_pow_pos_of_pos _ hqL _))
            (Nat.mul_pos (nat_pow_pos_of_pos _ hpP _) (nat_pow_pos_of_pos _ hqP _)))
          (Nat.mul_pos (nat_pow_pos_of_pos _ hpT _) (nat_pow_pos_of_pos _ hqT _)))
        (Nat.mul_pos (nat_pow_pos_of_pos _ hp001 _) (nat_pow_pos_of_pos _ hq001 _)))
      (Nat.mul_pos (nat_pow_pos_of_pos _ hp111 _) (nat_pow_pos_of_pos _ hq111 _))
  have hlhs :
      (q_L ^ L0 * p_P ^ P0 * (p_T ^ T0 * (p_T * p_T)) * p_001 ^ s * (p_111 ^ G1 * p_111 ^ D)) *
      (p_L ^ L0 * (q_P ^ P0 * q_P) * q_T ^ T0 * q_001 ^ s * q_111 ^ G1) =
      (q_P * (p_T * p_T) * p_111 ^ D) * Base :=
    cancel_fam1_lhs_w18 _ _ _ _ _ _ _ _ _ _ _ _ _
  have hrhs :
      C_hi * (p_L ^ L0 * q_P ^ P0 * (q_T ^ T0 * (q_T * q_T)) * q_001 ^ s * (q_111 ^ G1 * q_111 ^ D)) *
      (q_L ^ L0 * (p_P ^ P0 * p_P) * p_T ^ T0 * p_001 ^ s * p_111 ^ G1) =
      (C1 * q_111 ^ D) * Base :=
    cancel_fam1_rhs_w18 _ _ _ _ _ _ _ _ _ _ _ _ _ _
  rw [hlhs, hrhs] at hrat
  have hcan := Nat.le_of_mul_le_mul_right hrat hBase_pos
  have h1_le : p_111 ^ D ≤ q_P * (p_T * p_T) * p_111 ^ D := by
    simpa using Nat.mul_le_mul_right (p_111 ^ D)
      (Nat.mul_le_mul hqP (Nat.mul_le_mul hpT hpT))
  exact archimedean_pow_contra_w18 q_111 p_111 C1 D hq111 hlt
    (by dsimp [D, s, k]; omega) (Nat.le_trans h1_le hcan)

private theorem five_var_not_p111_lt_w18 (M_0 : Nat) (wNum wDen : Nat -> Nat)
    (c_0 C_hi p_L q_L p_P q_P p_T q_T p_001 q_001 p_111 q_111 pTheta qTheta : Nat)
    (hc0 : c_0 ≥ 1) (hpL : p_L ≥ 1) (hqL : q_L ≥ 1) (hpP : p_P ≥ 1) (hqP : q_P ≥ 1)
    (hpT : p_T ≥ 1) (hqT : q_T ≥ 1) (hp001 : p_001 ≥ 1) (hq001 : q_001 ≥ 1)
    (hp111 : p_111 ≥ 1)
    (hsand : ∀ n : Nat, n ≥ M_0 ->
      c_0 * (q_L ^ binBitLength n * p_P ^ binaryPopcount n * p_T ^ binaryAltTransitions n *
          p_001 ^ binaryThreeGram001 n * p_111 ^ binaryThreeGram111 n) * wDen n ≤
        (p_L ^ binBitLength n * q_P ^ binaryPopcount n * q_T ^ binaryAltTransitions n *
          q_001 ^ binaryThreeGram001 n * q_111 ^ binaryThreeGram111 n) * wNum n ∧
      (p_L ^ binBitLength n * q_P ^ binaryPopcount n * q_T ^ binaryAltTransitions n *
          q_001 ^ binaryThreeGram001 n * q_111 ^ binaryThreeGram111 n) * wNum n ≤
        C_hi * (q_L ^ binBitLength n * p_P ^ binaryPopcount n * p_T ^ binaryAltTransitions n *
          p_001 ^ binaryThreeGram001 n * p_111 ^ binaryThreeGram111 n) * wDen n)
    (hw : IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta) :
    ¬ (p_111 < q_111) := by
  intro hlt
  let MonLo : Nat -> Nat := fun n =>
    q_L ^ binBitLength n * p_P ^ binaryPopcount n * p_T ^ binaryAltTransitions n *
      p_001 ^ binaryThreeGram001 n * p_111 ^ binaryThreeGram111 n
  let MonHi : Nat -> Nat := fun n =>
    p_L ^ binBitLength n * q_P ^ binaryPopcount n * q_T ^ binaryAltTransitions n *
      q_001 ^ binaryThreeGram001 n * q_111 ^ binaryThreeGram111 n
  let C3 := C_hi * p_P * q_T * q_001
  let k := M_0 + p_111 * (C3 + 1) + 2
  let s := k + 1
  rcases fam3_neg111_spec_w18 k with
    ⟨hn_lo, hm_lo, _, _, hm3, hstep, hLn, hLm, hPn, hPm, hTn, hTm, h001n, h001m, h111n, h111m⟩
  let n := fam3NOddW18 k
  let m := fam3MW18 k
  have hgk := base_ge2_gt_self_w18 1024 (by decide) k
  have hn_ge : n ≥ M_0 := by dsimp [n, k] at hn_lo hgk ⊢; omega
  have hm_ge : m ≥ M_0 := by dsimp [m, k] at hm_lo hgk ⊢; omega
  have hrat := odd_branch_monomial_ratio_le_w18 M_0 wNum wDen MonHi MonLo c_0 C_hi pTheta qTheta n m
    hc0 hn_ge hm_ge hm3 hstep (hsand n hn_ge).1 (hsand m hm_ge).2 hw
  dsimp only [MonLo, MonHi] at hrat
  let L0 := 10 * s
  let P0 := 5 * s
  let T0 := 6 * s - 1
  let G0 := s - 1
  let D := s + 1
  have hLn' : binBitLength n = L0 := hLn
  have hLm' : binBitLength m = L0 := hLm
  have hPn' : binaryPopcount n = P0 := hPn
  have hPm' : binaryPopcount m = P0 + 1 := hPm
  have hTn' : binaryAltTransitions n = T0 + 1 := by rw [hTn]; dsimp [T0, s, k]; omega
  have hTm' : binaryAltTransitions m = T0 := hTm
  have h001n' : binaryThreeGram001 n = G0 + 1 := h001n
  have h001m' : binaryThreeGram001 m = G0 := h001m
  have h111m' : binaryThreeGram111 m = D := h111m
  rw [hLn', hLm', hPn', hPm', hTn', hTm', h001n', h001m', h111n, h111m',
      Nat.pow_zero p_111, Nat.pow_zero q_111] at hrat
  simp only [Nat.mul_one] at hrat
  rw [Nat.pow_add p_P P0 1, Nat.pow_add q_P P0 1, Nat.pow_one p_P, Nat.pow_one q_P,
      Nat.pow_add p_T T0 1, Nat.pow_add q_T T0 1, Nat.pow_one p_T, Nat.pow_one q_T,
      Nat.pow_add p_001 G0 1, Nat.pow_add q_001 G0 1, Nat.pow_one p_001, Nat.pow_one q_001] at hrat
  let Base := (p_L ^ L0 * q_L ^ L0) * (p_P ^ P0 * q_P ^ P0) *
    (p_T ^ T0 * q_T ^ T0) * (p_001 ^ G0 * q_001 ^ G0)
  have hBase_pos : Base > 0 :=
    Nat.mul_pos
      (Nat.mul_pos
        (Nat.mul_pos
          (Nat.mul_pos (nat_pow_pos_of_pos _ hpL _) (nat_pow_pos_of_pos _ hqL _))
          (Nat.mul_pos (nat_pow_pos_of_pos _ hpP _) (nat_pow_pos_of_pos _ hqP _)))
        (Nat.mul_pos (nat_pow_pos_of_pos _ hpT _) (nat_pow_pos_of_pos _ hqT _)))
      (Nat.mul_pos (nat_pow_pos_of_pos _ hp001 _) (nat_pow_pos_of_pos _ hq001 _))
  have hlhs :
      (q_L ^ L0 * p_P ^ P0 * (p_T ^ T0 * p_T) * (p_001 ^ G0 * p_001)) *
      (p_L ^ L0 * (q_P ^ P0 * q_P) * q_T ^ T0 * q_001 ^ G0 * q_111 ^ D) =
      (q_P * p_T * p_001 * q_111 ^ D) * Base :=
    cancel_fam3_lhs_w18 _ _ _ _ _ _ _ _ _ _ _ _
  have hrhs :
      C_hi * (p_L ^ L0 * q_P ^ P0 * (q_T ^ T0 * q_T) * (q_001 ^ G0 * q_001)) *
      (q_L ^ L0 * (p_P ^ P0 * p_P) * p_T ^ T0 * p_001 ^ G0 * p_111 ^ D) =
      (C3 * p_111 ^ D) * Base :=
    cancel_fam3_rhs_w18 _ _ _ _ _ _ _ _ _ _ _ _ _
  rw [hlhs, hrhs] at hrat
  have hcan := Nat.le_of_mul_le_mul_right hrat hBase_pos
  have h1_le : q_111 ^ D ≤ q_P * p_T * p_001 * q_111 ^ D := by
    simpa using Nat.mul_le_mul_right (q_111 ^ D)
      (Nat.mul_le_mul (Nat.mul_le_mul hqP hpT) hp001)
  exact archimedean_pow_contra_w18 p_111 q_111 C3 D hp111 hlt
    (by dsimp [D, s, k]; omega) (Nat.le_trans h1_le hcan)

private theorem five_var_not_q001_lt_w18 (M_0 : Nat) (wNum wDen : Nat -> Nat)
    (c_0 C_hi p_L q_L p_P q_P p_T q_T p_001 q_001 p_111 q_111 pTheta qTheta : Nat)
    (hc0 : c_0 ≥ 1) (hpL : p_L ≥ 1) (hqL : q_L ≥ 1) (hpP : p_P ≥ 1) (hqP : q_P ≥ 1)
    (hpT : p_T ≥ 1) (hqT : q_T ≥ 1) (hp001 : p_001 ≥ 1) (hq001 : q_001 ≥ 1)
    (hsand : ∀ n : Nat, n ≥ M_0 ->
      c_0 * (q_L ^ binBitLength n * p_P ^ binaryPopcount n * p_T ^ binaryAltTransitions n *
          p_001 ^ binaryThreeGram001 n * p_111 ^ binaryThreeGram111 n) * wDen n ≤
        (p_L ^ binBitLength n * q_P ^ binaryPopcount n * q_T ^ binaryAltTransitions n *
          q_001 ^ binaryThreeGram001 n * q_111 ^ binaryThreeGram111 n) * wNum n ∧
      (p_L ^ binBitLength n * q_P ^ binaryPopcount n * q_T ^ binaryAltTransitions n *
          q_001 ^ binaryThreeGram001 n * q_111 ^ binaryThreeGram111 n) * wNum n ≤
        C_hi * (q_L ^ binBitLength n * p_P ^ binaryPopcount n * p_T ^ binaryAltTransitions n *
          p_001 ^ binaryThreeGram001 n * p_111 ^ binaryThreeGram111 n) * wDen n)
    (hw : IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta) :
    ¬ (q_001 < p_001) := by
  intro hlt
  let MonLo : Nat -> Nat := fun n =>
    q_L ^ binBitLength n * p_P ^ binaryPopcount n * p_T ^ binaryAltTransitions n *
      p_001 ^ binaryThreeGram001 n * p_111 ^ binaryThreeGram111 n
  let MonHi : Nat -> Nat := fun n =>
    p_L ^ binBitLength n * q_P ^ binaryPopcount n * q_T ^ binaryAltTransitions n *
      q_001 ^ binaryThreeGram001 n * q_111 ^ binaryThreeGram111 n
  let C2 := C_hi * p_P * q_T
  let k := M_0 + q_001 * (C2 + 1) + 2
  let s := k + 1
  rcases fam2_pos001_spec_w18 k with
    ⟨hn_lo, hm_lo, _, _, hm3, hstep, hLn, hLm, hPn, hPm, hTn, hTm, h001n, h001m, h111n, h111m⟩
  let n := fam2NOddW18 k
  let m := fam2MW18 k
  have hgk := base_ge2_gt_self_w18 1024 (by decide) k
  have hn_ge : n ≥ M_0 := by dsimp [n, k] at hn_lo hgk ⊢; omega
  have hm_ge : m ≥ M_0 := by dsimp [m, k] at hm_lo hgk ⊢; omega
  have hrat := odd_branch_monomial_ratio_le_w18 M_0 wNum wDen MonHi MonLo c_0 C_hi pTheta qTheta n m
    hc0 hn_ge hm_ge hm3 hstep (hsand n hn_ge).1 (hsand m hm_ge).2 hw
  dsimp only [MonLo, MonHi] at hrat
  let L0 := 10 * s
  let P0 := 4 * s
  let T0 := 6 * s - 1
  let G0 := s - 1
  let D := s + 1
  have hLn' : binBitLength n = L0 := hLn
  have hLm' : binBitLength m = L0 := hLm
  have hPn' : binaryPopcount n = P0 := hPn
  have hPm' : binaryPopcount m = P0 + 1 := hPm
  have hTn' : binaryAltTransitions n = T0 + 1 := by rw [hTn]; dsimp [T0, s, k]; omega
  have hTm' : binaryAltTransitions m = T0 := hTm
  have h001n' : binaryThreeGram001 n = G0 + D := by rw [h001n]; dsimp [G0, D, s, k]; omega
  have h001m' : binaryThreeGram001 m = G0 := h001m
  rw [hLn', hLm', hPn', hPm', hTn', hTm', h001n', h001m', h111n, h111m,
      Nat.pow_zero p_111, Nat.pow_zero q_111] at hrat
  simp only [Nat.mul_one] at hrat
  rw [Nat.pow_add p_P P0 1, Nat.pow_add q_P P0 1, Nat.pow_one p_P, Nat.pow_one q_P,
      Nat.pow_add p_T T0 1, Nat.pow_add q_T T0 1, Nat.pow_one p_T, Nat.pow_one q_T,
      Nat.pow_add p_001 G0 D, Nat.pow_add q_001 G0 D] at hrat
  let Base := (p_L ^ L0 * q_L ^ L0) * (p_P ^ P0 * q_P ^ P0) *
    (p_T ^ T0 * q_T ^ T0) * (p_001 ^ G0 * q_001 ^ G0)
  have hBase_pos : Base > 0 :=
    Nat.mul_pos
      (Nat.mul_pos
        (Nat.mul_pos
          (Nat.mul_pos (nat_pow_pos_of_pos _ hpL _) (nat_pow_pos_of_pos _ hqL _))
          (Nat.mul_pos (nat_pow_pos_of_pos _ hpP _) (nat_pow_pos_of_pos _ hqP _)))
        (Nat.mul_pos (nat_pow_pos_of_pos _ hpT _) (nat_pow_pos_of_pos _ hqT _)))
      (Nat.mul_pos (nat_pow_pos_of_pos _ hp001 _) (nat_pow_pos_of_pos _ hq001 _))
  have hlhs :
      (q_L ^ L0 * p_P ^ P0 * (p_T ^ T0 * p_T) * (p_001 ^ G0 * p_001 ^ D)) *
      (p_L ^ L0 * (q_P ^ P0 * q_P) * q_T ^ T0 * q_001 ^ G0) =
      (q_P * p_T * p_001 ^ D) * Base :=
    cancel_fam2_lhs_w18 _ _ _ _ _ _ _ _ _ _ _
  have hrhs :
      C_hi * (p_L ^ L0 * q_P ^ P0 * (q_T ^ T0 * q_T) * (q_001 ^ G0 * q_001 ^ D)) *
      (q_L ^ L0 * (p_P ^ P0 * p_P) * p_T ^ T0 * p_001 ^ G0) =
      (C2 * q_001 ^ D) * Base :=
    cancel_fam2_rhs_w18 _ _ _ _ _ _ _ _ _ _ _ _
  rw [hlhs, hrhs] at hrat
  have hcan := Nat.le_of_mul_le_mul_right hrat hBase_pos
  have h1_le : p_001 ^ D ≤ q_P * p_T * p_001 ^ D := by
    simpa using Nat.mul_le_mul_right (p_001 ^ D) (Nat.mul_le_mul hqP hpT)
  exact archimedean_pow_contra_w18 q_001 p_001 C2 D hq001 hlt
    (by dsimp [D, s, k]; omega) (Nat.le_trans h1_le hcan)

private theorem five_var_not_p001_lt_w18 (M_0 : Nat) (wNum wDen : Nat -> Nat)
    (c_0 C_hi p_L q_L p_P q_P p_T q_T p_001 q_001 p_111 q_111 pTheta qTheta : Nat)
    (hc0 : c_0 ≥ 1) (hpL : p_L ≥ 1) (hqL : q_L ≥ 1) (hpP : p_P ≥ 1) (hqP : q_P ≥ 1)
    (hpT : p_T ≥ 1) (hqT : q_T ≥ 1) (hp001 : p_001 ≥ 1) (hq001 : q_001 ≥ 1)
    (hp111 : p_111 ≥ 1) (hpq111 : p_111 = q_111)
    (hsand : ∀ n : Nat, n ≥ M_0 ->
      c_0 * (q_L ^ binBitLength n * p_P ^ binaryPopcount n * p_T ^ binaryAltTransitions n *
          p_001 ^ binaryThreeGram001 n * p_111 ^ binaryThreeGram111 n) * wDen n ≤
        (p_L ^ binBitLength n * q_P ^ binaryPopcount n * q_T ^ binaryAltTransitions n *
          q_001 ^ binaryThreeGram001 n * q_111 ^ binaryThreeGram111 n) * wNum n ∧
      (p_L ^ binBitLength n * q_P ^ binaryPopcount n * q_T ^ binaryAltTransitions n *
          q_001 ^ binaryThreeGram001 n * q_111 ^ binaryThreeGram111 n) * wNum n ≤
        C_hi * (q_L ^ binBitLength n * p_P ^ binaryPopcount n * p_T ^ binaryAltTransitions n *
          p_001 ^ binaryThreeGram001 n * p_111 ^ binaryThreeGram111 n) * wDen n)
    (hw : IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta) :
    ¬ (p_001 < q_001) := by
  intro hlt
  let MonLo : Nat -> Nat := fun n =>
    q_L ^ binBitLength n * p_P ^ binaryPopcount n * p_T ^ binaryAltTransitions n *
      p_001 ^ binaryThreeGram001 n * p_111 ^ binaryThreeGram111 n
  let MonHi : Nat -> Nat := fun n =>
    p_L ^ binBitLength n * q_P ^ binaryPopcount n * q_T ^ binaryAltTransitions n *
      q_001 ^ binaryThreeGram001 n * q_111 ^ binaryThreeGram111 n
  let C4 := C_hi * p_P * (q_T * q_T) * (p_111 * p_111)
  let k := M_0 + p_001 * (C4 + 1) + 2
  let s := k + 1
  rcases fam4_neg001_spec_w18 k with
    ⟨hn_lo, hm_lo, _, _, hm3, hstep, hLn, hLm, hPn, hPm, hTn, hTm, h001n, h001m, h111n, h111m⟩
  let n := fam4NOddW18 k
  let m := fam4MW18 k
  have hgk := base_ge2_gt_self_w18 2048 (by decide) k
  have hn_ge : n ≥ M_0 := by dsimp [n, k] at hn_lo hgk ⊢; omega
  have hm_ge : m ≥ M_0 := by dsimp [m, k] at hm_lo hgk ⊢; omega
  have hrat := odd_branch_monomial_ratio_le_w18 M_0 wNum wDen MonHi MonLo c_0 C_hi pTheta qTheta n m
    hc0 hn_ge hm_ge hm3 hstep (hsand n hn_ge).1 (hsand m hm_ge).2 hw
  dsimp only [MonLo, MonHi] at hrat
  let L0 := 11 * s
  let P0 := 5 * s
  let T0 := 6 * s - 2
  let G1 := s - 1
  have hLn' : binBitLength n = L0 := hLn
  have hLm' : binBitLength m = L0 := hLm
  have hPn' : binaryPopcount n = P0 := hPn
  have hPm' : binaryPopcount m = P0 + 1 := hPm
  have hTn' : binaryAltTransitions n = T0 + 2 := by rw [hTn]; dsimp [T0, s, k]; omega
  have hTm' : binaryAltTransitions m = T0 := hTm
  have h001n' : binaryThreeGram001 n = s := h001n
  have h001m' : binaryThreeGram001 m = s + s := by rw [h001m, Nat.two_mul]
  have h111n' : binaryThreeGram111 n = G1 := h111n
  have h111m' : binaryThreeGram111 m = G1 + 2 := h111m
  rw [← hpq111, hLn', hLm', hPn', hPm', hTn', hTm', h001n', h001m', h111n', h111m',
      Nat.pow_add p_P P0 1, Nat.pow_add q_P P0 1, Nat.pow_one p_P, Nat.pow_one q_P,
      Nat.pow_add p_T T0 2, Nat.pow_add q_T T0 2,
      show p_T ^ 2 = p_T * p_T by rw [Nat.pow_succ, Nat.pow_one],
      show q_T ^ 2 = q_T * q_T by rw [Nat.pow_succ, Nat.pow_one],
      Nat.pow_add p_001 s s, Nat.pow_add q_001 s s,
      Nat.pow_add p_111 G1 2,
      show p_111 ^ 2 = p_111 * p_111 by rw [Nat.pow_succ, Nat.pow_one]] at hrat
  let Base := (p_L ^ L0 * q_L ^ L0) * (p_P ^ P0 * q_P ^ P0) *
    (p_T ^ T0 * q_T ^ T0) * (p_001 ^ s * q_001 ^ s) * (p_111 ^ G1 * p_111 ^ G1)
  have hBase_pos : Base > 0 :=
    Nat.mul_pos
      (Nat.mul_pos
        (Nat.mul_pos
          (Nat.mul_pos
            (Nat.mul_pos (nat_pow_pos_of_pos _ hpL _) (nat_pow_pos_of_pos _ hqL _))
            (Nat.mul_pos (nat_pow_pos_of_pos _ hpP _) (nat_pow_pos_of_pos _ hqP _)))
          (Nat.mul_pos (nat_pow_pos_of_pos _ hpT _) (nat_pow_pos_of_pos _ hqT _)))
        (Nat.mul_pos (nat_pow_pos_of_pos _ hp001 _) (nat_pow_pos_of_pos _ hq001 _)))
      (Nat.mul_pos (nat_pow_pos_of_pos _ hp111 _) (nat_pow_pos_of_pos _ hp111 _))
  have hlhs :
      (q_L ^ L0 * p_P ^ P0 * (p_T ^ T0 * (p_T * p_T)) * p_001 ^ s * p_111 ^ G1) *
      (p_L ^ L0 * (q_P ^ P0 * q_P) * q_T ^ T0 * (q_001 ^ s * q_001 ^ s) *
        (p_111 ^ G1 * (p_111 * p_111))) =
      (q_P * (p_T * p_T) * (p_111 * p_111) * q_001 ^ s) * Base :=
    cancel_fam4_lhs_w18 _ _ _ _ _ _ _ _ _ _ _ _ _
  have hrhs :
      C_hi * (p_L ^ L0 * q_P ^ P0 * (q_T ^ T0 * (q_T * q_T)) * q_001 ^ s * p_111 ^ G1) *
      (q_L ^ L0 * (p_P ^ P0 * p_P) * p_T ^ T0 * (p_001 ^ s * p_001 ^ s) *
        (p_111 ^ G1 * (p_111 * p_111))) =
      (C4 * p_001 ^ s) * Base :=
    cancel_fam4_rhs_w18 _ _ _ _ _ _ _ _ _ _ _ _ _ _
  rw [hlhs, hrhs] at hrat
  have hcan := Nat.le_of_mul_le_mul_right hrat hBase_pos
  have h1_le : q_001 ^ s ≤ q_P * (p_T * p_T) * (p_111 * p_111) * q_001 ^ s := by
    simpa using Nat.mul_le_mul_right (q_001 ^ s)
      (Nat.mul_le_mul (Nat.mul_le_mul hqP (Nat.mul_le_mul hpT hpT)) (Nat.mul_le_mul hp111 hp111))
  exact archimedean_pow_contra_w18 p_001 q_001 C4 s hp001 hlt
    (by dsimp [s, k]; omega) (Nat.le_trans h1_le hcan)

private theorem three_gram_monomial_sq_id_w18
    (L P T g000 g001 g010 g011 g100 g101 g110 g111 e000 e010 e011 e100 e101 e110 : Nat)
    (s000 : 2 * g000 + (2 * P + T + 2 * g001 + 3) = 2 * L + e000)
    (s100 : 2 * g100 = 2 * g001 + e100)
    (s101 : 2 * g101 + (2 * g001 + 1) = T + e101)
    (s011 : 2 * g011 + (T + 2 * g111 + 4) = 2 * P + e011)
    (s110 : 2 * g110 + (T + 2 * g111 + 4) = 2 * P + e110)
    (s010 : 2 * g010 + 2 * P = 2 * T + 2 * g111 + e010)
    (x000 x001 x010 x011 x100 x101 x110 x111 y000 y010 y011 y101 y110 : Nat) :
    let m8 := x000 ^ g000 * x001 ^ g001 * x010 ^ g010 * x011 ^ g011 *
              x100 ^ g100 * x101 ^ g101 * x110 ^ g110 * x111 ^ g111
    (m8 * m8) *
      ((x000 * y000) ^ (2 * P + T + 2 * g001 + 3) *
       (x010 * y010) ^ (2 * P) *
       (x011 * y011) ^ (T + 2 * g111 + 4) *
       (x101 * y101) ^ (2 * g001 + 1) *
       (x110 * y110) ^ (T + 2 * g111 + 4)) =
    ((x000 * x000) ^ L *
     ((x011 * x011) * (x110 * x110) * (y000 * y000) * (y010 * y010)) ^ P *
     ((x010 * x010) * x101 * y000 * y011 * y110) ^ T *
     ((x001 * x001) * (x100 * x100) * (y000 * y000) * (y101 * y101)) ^ g001 *
     ((x010 * x010) * (x111 * x111) * (y011 * y011) * (y110 * y110)) ^ g111) *
    (((y000 * y000 * y000) * (y011 * y011 * y011 * y011) * y101 * (y110 * y110 * y110 * y110)) *
     (x000 ^ e000 * x010 ^ e010 * x011 ^ e011 * x100 ^ e100 * x101 ^ e101 * x110 ^ e110)) := by
  dsimp only
  have sq_pow : ∀ (z e : Nat), (z * z) ^ e = z ^ (2 * e) := fun z e => by
    rw [← pow_pow_eq_mul_w5 z 2 e, show z ^ 2 = z * z by rw [Nat.pow_succ, Nat.pow_one]]
  have hx000 : x000 ^ g000 * x000 ^ g000 * x000 ^ (2 * P + T + 2 * g001 + 3) =
      (x000 * x000) ^ L * x000 ^ e000 := by
    rw [← Nat.pow_add x000 g000 g000, ← Nat.two_mul, ← Nat.pow_add, s000,
        Nat.pow_add, sq_pow]
  have hx001 : x001 ^ g001 * x001 ^ g001 = (x001 * x001) ^ g001 := (mul_pow_w18s x001 x001 g001).symm
  have hx010 : x010 ^ g010 * x010 ^ g010 * x010 ^ (2 * P) =
      (x010 * x010) ^ T * (x010 * x010) ^ g111 * x010 ^ e010 := by
    rw [← Nat.pow_add x010 g010 g010, ← Nat.two_mul, ← Nat.pow_add, s010,
        Nat.pow_add x010 (2 * T + 2 * g111) e010, Nat.pow_add x010 (2 * T) (2 * g111),
        sq_pow x010 T, sq_pow x010 g111]
  have hx011 : x011 ^ g011 * x011 ^ g011 * x011 ^ (T + 2 * g111 + 4) =
      (x011 * x011) ^ P * x011 ^ e011 := by
    rw [← Nat.pow_add x011 g011 g011, ← Nat.two_mul, ← Nat.pow_add, s011,
        Nat.pow_add, sq_pow]
  have hx100 : x100 ^ g100 * x100 ^ g100 = (x100 * x100) ^ g001 * x100 ^ e100 := by
    rw [← Nat.pow_add x100 g100 g100, ← Nat.two_mul, s100, Nat.pow_add, sq_pow]
  have hx101 : x101 ^ g101 * x101 ^ g101 * x101 ^ (2 * g001 + 1) =
      x101 ^ T * x101 ^ e101 := by
    rw [← Nat.pow_add x101 g101 g101, ← Nat.two_mul, ← Nat.pow_add, s101, Nat.pow_add]
  have hx110 : x110 ^ g110 * x110 ^ g110 * x110 ^ (T + 2 * g111 + 4) =
      (x110 * x110) ^ P * x110 ^ e110 := by
    rw [← Nat.pow_add x110 g110 g110, ← Nat.two_mul, ← Nat.pow_add, s110,
        Nat.pow_add, sq_pow]
  have hx111 : x111 ^ g111 * x111 ^ g111 = (x111 * x111) ^ g111 := (mul_pow_w18s x111 x111 g111).symm
  have hy000 : y000 ^ (2 * P + T + 2 * g001 + 3) =
      (y000 * y000) ^ P * y000 ^ T * (y000 * y000) ^ g001 * (y000 * y000 * y000) := by
    rw [Nat.pow_add y000 (2 * P + T + 2 * g001) 3,
        Nat.pow_add y000 (2 * P + T) (2 * g001),
        Nat.pow_add y000 (2 * P) T,
        sq_pow y000 P, sq_pow y000 g001,
        show y000 ^ 3 = y000 * y000 * y000 by rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_one]]
  have hy010 : y010 ^ (2 * P) = (y010 * y010) ^ P := (sq_pow y010 P).symm
  have hy011 : y011 ^ (T + 2 * g111 + 4) =
      y011 ^ T * (y011 * y011) ^ g111 * (y011 * y011 * y011 * y011) := by
    rw [Nat.pow_add y011 (T + 2 * g111) 4, Nat.pow_add y011 T (2 * g111), sq_pow y011 g111,
        show y011 ^ 4 = y011 * y011 * y011 * y011 by rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_one]]
  have hy101 : y101 ^ (2 * g001 + 1) = (y101 * y101) ^ g001 * y101 := by
    rw [Nat.pow_succ, sq_pow]
  have hy110 : y110 ^ (T + 2 * g111 + 4) =
      y110 ^ T * (y110 * y110) ^ g111 * (y110 * y110 * y110 * y110) := by
    rw [Nat.pow_add y110 (T + 2 * g111) 4, Nat.pow_add y110 T (2 * g111), sq_pow y110 g111,
        show y110 ^ 4 = y110 * y110 * y110 * y110 by rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_one]]
  rw [mul_pow_w18s x000 y000, mul_pow_w18s x010 y010, mul_pow_w18s x011 y011,
      mul_pow_w18s x101 y101, mul_pow_w18s x110 y110,
      regroup_eight_sq_five_w18
        (x000 ^ g000) (x001 ^ g001) (x010 ^ g010) (x011 ^ g011)
        (x100 ^ g100) (x101 ^ g101) (x110 ^ g110) (x111 ^ g111)
        (x000 ^ (2 * P + T + 2 * g001 + 3)) (y000 ^ (2 * P + T + 2 * g001 + 3))
        (x010 ^ (2 * P)) (y010 ^ (2 * P))
        (x011 ^ (T + 2 * g111 + 4)) (y011 ^ (T + 2 * g111 + 4))
        (x101 ^ (2 * g001 + 1)) (y101 ^ (2 * g001 + 1))
        (x110 ^ (T + 2 * g111 + 4)) (y110 ^ (T + 2 * g111 + 4)),
      hx000, hx001, hx010, hx011, hx100, hx101, hx110, hx111,
      hy000, hy010, hy011, hy101, hy110,
      regroup_u_blocks_w18
        ((x000 * x000) ^ L) (x000 ^ e000) ((x001 * x001) ^ g001)
        ((x010 * x010) ^ T) ((x010 * x010) ^ g111) (x010 ^ e010)
        ((x011 * x011) ^ P) (x011 ^ e011) ((x100 * x100) ^ g001) (x100 ^ e100)
        (x101 ^ T) (x101 ^ e101) ((x110 * x110) ^ P) (x110 ^ e110) ((x111 * x111) ^ g111),
      regroup_v_blocks_w18
        ((y000 * y000) ^ P) (y000 ^ T) ((y000 * y000) ^ g001) (y000 * y000 * y000)
        ((y010 * y010) ^ P) (y011 ^ T) ((y011 * y011) ^ g111) (y011 * y011 * y011 * y011)
        ((y101 * y101) ^ g001) y101 (y110 ^ T) ((y110 * y110) ^ g111) (y110 * y110 * y110 * y110),
      regroup_uv_merge_w18]
  have hp_comb :
      ((x011 * x011) ^ P * (x110 * x110) ^ P) * ((y000 * y000) ^ P * (y010 * y010) ^ P) =
      ((x011 * x011) * (x110 * x110) * (y000 * y000) * (y010 * y010)) ^ P := by
    rw [← mul_pow_w18s, ← mul_pow_w18s, ← mul_pow_w18s, ← Nat.mul_assoc]
  have ht_comb :
      ((x010 * x010) ^ T * x101 ^ T) * (y000 ^ T * y011 ^ T * y110 ^ T) =
      ((x010 * x010) * x101 * y000 * y011 * y110) ^ T := by
    rw [← mul_pow_w18s, ← mul_pow_w18s, ← mul_pow_w18s, ← mul_pow_w18s]
    apply congrArg (· ^ T); simp only [Nat.mul_assoc]
  have hg0_comb :
      ((x001 * x001) ^ g001 * (x100 * x100) ^ g001) * ((y000 * y000) ^ g001 * (y101 * y101) ^ g001) =
      ((x001 * x001) * (x100 * x100) * (y000 * y000) * (y101 * y101)) ^ g001 := by
    rw [← mul_pow_w18s, ← mul_pow_w18s, ← mul_pow_w18s, ← Nat.mul_assoc]
  have hg1_comb :
      ((x010 * x010) ^ g111 * (x111 * x111) ^ g111) * ((y011 * y011) ^ g111 * (y110 * y110) ^ g111) =
      ((x010 * x010) * (x111 * x111) * (y011 * y011) * (y110 * y110)) ^ g111 := by
    rw [← mul_pow_w18s, ← mul_pow_w18s, ← mul_pow_w18s, ← Nat.mul_assoc]
  rw [hp_comb, ht_comb, hg0_comb, hg1_comb]

private theorem five_var_exp_impossibility_w18 :
    ∀ (M_0 : Nat), M_0 ≥ 3 ->
      ∀ (wNum wDen : Nat -> Nat)
        (c_0 C_hi p_L q_L p_P q_P p_T q_T p_001 q_001 p_111 q_111 pTheta qTheta : Nat),
        c_0 ≥ 1 -> p_L ≥ 1 -> q_L ≥ 1 -> p_P ≥ 1 -> q_P ≥ 1 ->
        p_T ≥ 1 -> q_T ≥ 1 -> p_001 ≥ 1 -> q_001 ≥ 1 -> p_111 ≥ 1 -> q_111 ≥ 1 ->
        (∀ n : Nat, n ≥ M_0 ->
          c_0 * (q_L ^ binBitLength n * p_P ^ binaryPopcount n * p_T ^ binaryAltTransitions n *
              p_001 ^ binaryThreeGram001 n * p_111 ^ binaryThreeGram111 n) * wDen n ≤
            (p_L ^ binBitLength n * q_P ^ binaryPopcount n * q_T ^ binaryAltTransitions n *
              q_001 ^ binaryThreeGram001 n * q_111 ^ binaryThreeGram111 n) * wNum n ∧
          (p_L ^ binBitLength n * q_P ^ binaryPopcount n * q_T ^ binaryAltTransitions n *
              q_001 ^ binaryThreeGram001 n * q_111 ^ binaryThreeGram111 n) * wNum n ≤
            C_hi * (q_L ^ binBitLength n * p_P ^ binaryPopcount n * p_T ^ binaryAltTransitions n *
              p_001 ^ binaryThreeGram001 n * p_111 ^ binaryThreeGram111 n) * wDen n) ->
        ¬ IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta := by
  intro M_0 hM0 wNum wDen c_0 C_hi p_L q_L p_P q_P p_T q_T p_001 q_001 p_111 q_111 pTheta qTheta
    hc0 hpL hqL hpP hqP hpT hqT hp001 hq001 hp111 hq111 hsand hw
  have hn_q111_lt := five_var_not_q111_lt_w18 M_0 wNum wDen c_0 C_hi p_L q_L p_P q_P p_T q_T
    p_001 q_001 p_111 q_111 pTheta qTheta hc0 hpL hqL hpP hqP hpT hqT hp001 hq001 hp111 hq111 hsand hw
  have hn_p111_lt := five_var_not_p111_lt_w18 M_0 wNum wDen c_0 C_hi p_L q_L p_P q_P p_T q_T
    p_001 q_001 p_111 q_111 pTheta qTheta hc0 hpL hqL hpP hqP hpT hqT hp001 hq001 hp111 hsand hw
  have hpq111 : p_111 = q_111 := by omega
  have hn_q001_lt := five_var_not_q001_lt_w18 M_0 wNum wDen c_0 C_hi p_L q_L p_P q_P p_T q_T
    p_001 q_001 p_111 q_111 pTheta qTheta hc0 hpL hqL hpP hqP hpT hqT hp001 hq001 hsand hw
  have hn_p001_lt := five_var_not_p001_lt_w18 M_0 wNum wDen c_0 C_hi p_L q_L p_P q_P p_T q_T
    p_001 q_001 p_111 q_111 pTheta qTheta hc0 hpL hqL hpP hqP hpT hqT hp001 hq001 hp111 hpq111 hsand hw
  have hpq001 : p_001 = q_001 := by omega
  apply eventual_three_var_bitlength_popcount_alt_exp_impossibility.2 M_0 hM0
    wNum wDen c_0 C_hi p_L q_L p_P q_P p_T q_T pTheta qTheta
    hc0 hpL hqL hpP hqP hpT hqT ?_ hw
  intro n hn
  rcases hsand n hn with ⟨hlo, hhi⟩
  rw [← hpq001, ← hpq111] at hlo hhi
  let E := p_001 ^ binaryThreeGram001 n * p_111 ^ binaryThreeGram111 n
  have hE_pos : E > 0 :=
    Nat.mul_pos (nat_pow_pos_of_pos _ hp001 _) (nat_pow_pos_of_pos _ hp111 _)
  let A := q_L ^ binBitLength n * p_P ^ binaryPopcount n * p_T ^ binaryAltTransitions n
  let B := p_L ^ binBitLength n * q_P ^ binaryPopcount n * q_T ^ binaryAltTransitions n
  have hl_eq1 : (c_0 * A * wDen n) * E =
      c_0 * (q_L ^ binBitLength n * p_P ^ binaryPopcount n * p_T ^ binaryAltTransitions n *
        p_001 ^ binaryThreeGram001 n * p_111 ^ binaryThreeGram111 n) * wDen n := by
    dsimp [A, E]; ac_rfl
  have hr_eq1 : (B * wNum n) * E =
      (p_L ^ binBitLength n * q_P ^ binaryPopcount n * q_T ^ binaryAltTransitions n *
        p_001 ^ binaryThreeGram001 n * p_111 ^ binaryThreeGram111 n) * wNum n := by
    dsimp [B, E]; ac_rfl
  have hr_eq2 : (C_hi * A * wDen n) * E =
      C_hi * (q_L ^ binBitLength n * p_P ^ binaryPopcount n * p_T ^ binaryAltTransitions n *
        p_001 ^ binaryThreeGram001 n * p_111 ^ binaryThreeGram111 n) * wDen n := by
    dsimp [A, E]; ac_rfl
  rw [← hl_eq1, ← hr_eq1] at hlo
  rw [← hr_eq1, ← hr_eq2] at hhi
  exact ⟨Nat.le_of_mul_le_mul_right hlo hE_pos, Nat.le_of_mul_le_mul_right hhi hE_pos⟩

private theorem sq_common_scale_rew_w18 (c Q D Com BL EL : Nat)
    (h : (Q * Q) * Com = BL * EL) :
    ((c * Q * D) * (c * Q * D)) * Com = (c * c * EL) * (BL * (D * D)) := by
  calc ((c * Q * D) * (c * Q * D)) * Com
      = (c * c) * (((Q * Q) * Com) * (D * D)) := by ac_rfl
    _ = (c * c) * ((BL * EL) * (D * D)) := by rw [h]
    _ = (c * c * EL) * (BL * (D * D)) := by ac_rfl

private theorem sq_common_noscale_rew_w18 (P N Com BH EH : Nat)
    (h : (P * P) * Com = BH * EH) :
    ((P * N) * (P * N)) * Com = BH * (EH * (N * N)) := by
  calc ((P * N) * (P * N)) * Com
      = ((P * P) * Com) * (N * N) := by ac_rfl
    _ = (BH * EH) * (N * N) := by rw [h]
    _ = BH * (EH * (N * N)) := by ac_rfl

private theorem sq_common_hi_swap_w18 (K BH EH NN : Nat) :
    K * (BH * (EH * NN)) = EH * (BH * (K * NN)) := by ac_rfl

private theorem sq_common_top_assoc_w18 (K CC EL BL DD : Nat) :
    K * ((CC * EL) * (BL * DD)) = (CC * K * EL) * (BL * DD) := by ac_rfl

/--
  Theorem W18.3b (`eventual_five_var_and_complete_3gram_exp_impossibility`,
  `zero custom axioms`):
  1. **Complete 100% `(0, ∞)^5` Closure of Independent 5-Variable `(binBitLength, binaryPopcount,
     binaryAltTransitions, binaryThreeGram001, binaryThreeGram111)` Exponential Preimage Weights:**
     Across ALL eventual cutoffs `∀ M_0 ≥ 3` and ALL 10 positive integer base parameters, NO
     two-sided positive rational preimage weight sandwiched by `L, P, T, c_001, c_111` exponentials
     satisfies `IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta`!
  2. **Complete 100% `(0, ∞)^8` Closure of All Eight Binary `3`-Gram `(c_000 .. c_111)` Exponential
     Preimage Weights:**
     Via `binary_three_gram_debruijn_syzygies` + `preimage_weight_square_preserves_superharmonicity`,
     every two-sided `(0, ∞)^8` complete `3`-gram exponential preimage weight squares into the
     independent `(L, P, T, c_001, c_111)` cone and is unconditionally impossible across `∀ M_0 ≥ 3`
     (`Branch P1.2`, witness `ZPOS_PREIMAGE_3GRAM_PURE_535_TO_803`, `W18_H3`)!
-/
theorem eventual_five_var_and_complete_3gram_exp_impossibility :
    (∀ (M_0 : Nat), M_0 ≥ 3 ->
      ∀ (wNum wDen : Nat -> Nat)
        (c_0 C_hi p_L q_L p_P q_P p_T q_T p_001 q_001 p_111 q_111 pTheta qTheta : Nat),
        c_0 ≥ 1 -> p_L ≥ 1 -> q_L ≥ 1 -> p_P ≥ 1 -> q_P ≥ 1 ->
        p_T ≥ 1 -> q_T ≥ 1 -> p_001 ≥ 1 -> q_001 ≥ 1 -> p_111 ≥ 1 -> q_111 ≥ 1 ->
        (∀ n : Nat, n ≥ M_0 ->
          c_0 * (q_L ^ binBitLength n * p_P ^ binaryPopcount n * p_T ^ binaryAltTransitions n *
              p_001 ^ binaryThreeGram001 n * p_111 ^ binaryThreeGram111 n) * wDen n ≤
            (p_L ^ binBitLength n * q_P ^ binaryPopcount n * q_T ^ binaryAltTransitions n *
              q_001 ^ binaryThreeGram001 n * q_111 ^ binaryThreeGram111 n) * wNum n ∧
          (p_L ^ binBitLength n * q_P ^ binaryPopcount n * q_T ^ binaryAltTransitions n *
              q_001 ^ binaryThreeGram001 n * q_111 ^ binaryThreeGram111 n) * wNum n ≤
            C_hi * (q_L ^ binBitLength n * p_P ^ binaryPopcount n * p_T ^ binaryAltTransitions n *
              p_001 ^ binaryThreeGram001 n * p_111 ^ binaryThreeGram111 n) * wDen n) ->
        ¬ IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta) ∧
    (∀ (M_0 : Nat), M_0 ≥ 3 ->
      ∀ (wNum wDen : Nat -> Nat)
        (c_0 C_hi p_000 q_000 p_001 q_001 p_010 q_010 p_011 q_011
          p_100 q_100 p_101 q_101 p_110 q_110 p_111 q_111 pTheta qTheta : Nat),
        c_0 ≥ 1 -> p_000 ≥ 1 -> q_000 ≥ 1 -> p_001 ≥ 1 -> q_001 ≥ 1 ->
        p_010 ≥ 1 -> q_010 ≥ 1 -> p_011 ≥ 1 -> q_011 ≥ 1 ->
        p_100 ≥ 1 -> q_100 ≥ 1 -> p_101 ≥ 1 -> q_101 ≥ 1 ->
        p_110 ≥ 1 -> q_110 ≥ 1 -> p_111 ≥ 1 -> q_111 ≥ 1 ->
        (∀ n : Nat, n ≥ M_0 ->
          c_0 * (q_000 ^ binaryThreeGram000 n * q_001 ^ binaryThreeGram001 n *
              q_010 ^ binaryThreeGram010 n * q_011 ^ binaryThreeGram011 n *
              q_100 ^ binaryThreeGram100 n * q_101 ^ binaryThreeGram101 n *
              q_110 ^ binaryThreeGram110 n * q_111 ^ binaryThreeGram111 n) * wDen n ≤
            (p_000 ^ binaryThreeGram000 n * p_001 ^ binaryThreeGram001 n *
              p_010 ^ binaryThreeGram010 n * p_011 ^ binaryThreeGram011 n *
              p_100 ^ binaryThreeGram100 n * p_101 ^ binaryThreeGram101 n *
              p_110 ^ binaryThreeGram110 n * p_111 ^ binaryThreeGram111 n) * wNum n ∧
          (p_000 ^ binaryThreeGram000 n * p_001 ^ binaryThreeGram001 n *
              p_010 ^ binaryThreeGram010 n * p_011 ^ binaryThreeGram011 n *
              p_100 ^ binaryThreeGram100 n * p_101 ^ binaryThreeGram101 n *
              p_110 ^ binaryThreeGram110 n * p_111 ^ binaryThreeGram111 n) * wNum n ≤
            C_hi * (q_000 ^ binaryThreeGram000 n * q_001 ^ binaryThreeGram001 n *
              q_010 ^ binaryThreeGram010 n * q_011 ^ binaryThreeGram011 n *
              q_100 ^ binaryThreeGram100 n * q_101 ^ binaryThreeGram101 n *
              q_110 ^ binaryThreeGram110 n * q_111 ^ binaryThreeGram111 n) * wDen n) ->
        ¬ IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta) := by
  refine ⟨five_var_exp_impossibility_w18, ?_⟩
  -- Part 2: Complete `8`-Variable Binary `3`-Grams `(c_000 .. c_111)` -> 5-Variable `(L, P, T, c_001, c_111)`:
  intro M_0 hM0 wNum wDen c_0 C_hi
    p_000 q_000 p_001 q_001 p_010 q_010 p_011 q_011
    p_100 q_100 p_101 q_101 p_110 q_110 p_111 q_111 pTheta qTheta
    hc0 hp000 hq000 hp001 hq001 hp010 hq010 hp011 hq011
    hp100 hq100 hp101 hq101 hp110 hq110 hp111 hq111 hsand hw
  let M_1 := if M_0 ≤ 4 then 4 else M_0
  have hM1_ge4 : M_1 ≥ 4 := by dsimp [M_1]; split <;> omega
  have hM0_le_M1 : M_0 ≤ M_1 := by dsimp [M_1]; split <;> omega
  have hw_M1 := preimage_weight_mono_cutoff_w18 M_0 M_1 hM0_le_M1 wNum wDen pTheta qTheta hw
  let pow3 := fun x : Nat => x * x * x
  let pow4 := fun x : Nat => x * x * x * x
  let K_num :=
    (pow3 q_000 * pow4 q_011 * q_101 * pow4 q_110) *
    (pow3 p_000 * pow4 p_010 * pow3 p_011 * (p_100 * p_100) * p_101 * pow3 p_110)
  have p3_pos : ∀ z : Nat, z ≥ 1 -> pow3 z ≥ 1 := fun _ hz => Nat.mul_pos (Nat.mul_pos hz hz) hz
  have p4_pos : ∀ z : Nat, z ≥ 1 -> pow4 z ≥ 1 := fun _ hz => Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hz hz) hz) hz
  have hK_pos : K_num ≥ 1 :=
    Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (p3_pos _ hq000) (p4_pos _ hq011)) hq101) (p4_pos _ hq110))
      (Nat.mul_pos
        (Nat.mul_pos
          (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (p3_pos _ hp000) (p4_pos _ hp010)) (p3_pos _ hp011))
            (Nat.mul_pos hp100 hp100))
          hp101)
        (p3_pos _ hp110))
  have hw_sq := preimage_weight_square_preserves_superharmonicity M_1 wNum wDen pTheta qTheta K_num hK_pos hw_M1
  let P_L := p_000 * p_000
  let Q_L := q_000 * q_000
  let P_P := (q_011 * q_011) * (q_110 * q_110) * (p_000 * p_000) * (p_010 * p_010)
  let Q_P := (p_011 * p_011) * (p_110 * p_110) * (q_000 * q_000) * (q_010 * q_010)
  let P_T := (q_010 * q_010) * q_101 * p_000 * p_011 * p_110
  let Q_T := (p_010 * p_010) * p_101 * q_000 * q_011 * q_110
  let P_001 := (q_001 * q_001) * (q_100 * q_100) * (p_000 * p_000) * (p_101 * p_101)
  let Q_001 := (p_001 * p_001) * (p_100 * p_100) * (q_000 * q_000) * (q_101 * q_101)
  let P_111 := (q_010 * q_010) * (q_111 * q_111) * (p_011 * p_011) * (p_110 * p_110)
  let Q_111 := (p_010 * p_010) * (p_111 * p_111) * (q_011 * q_011) * (q_110 * q_110)
  let E_lo_max :=
    (pow3 p_000 * pow4 p_011 * p_101 * pow4 p_110) *
    (pow3 q_000 * pow4 q_010 * pow3 q_011 * (q_100 * q_100) * q_101 * pow3 q_110)
  let C_top := (C_hi * C_hi + 1) * K_num * E_lo_max
  have hpos_PL : P_L ≥ 1 := Nat.mul_pos hp000 hp000
  have hpos_QL : Q_L ≥ 1 := Nat.mul_pos hq000 hq000
  have hpos_PP : P_P ≥ 1 :=
    Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hq011 hq011) (Nat.mul_pos hq110 hq110))
        (Nat.mul_pos hp000 hp000))
      (Nat.mul_pos hp010 hp010)
  have hpos_QP : Q_P ≥ 1 :=
    Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp011 hp011) (Nat.mul_pos hp110 hp110))
        (Nat.mul_pos hq000 hq000))
      (Nat.mul_pos hq010 hq010)
  have hpos_PT : P_T ≥ 1 :=
    Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hq010 hq010) hq101) hp000) hp011)
      hp110
  have hpos_QT : Q_T ≥ 1 :=
    Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp010 hp010) hp101) hq000) hq011)
      hq110
  have hpos_P001 : P_001 ≥ 1 :=
    Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hq001 hq001) (Nat.mul_pos hq100 hq100))
        (Nat.mul_pos hp000 hp000))
      (Nat.mul_pos hp101 hp101)
  have hpos_Q001 : Q_001 ≥ 1 :=
    Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp001 hp001) (Nat.mul_pos hp100 hp100))
        (Nat.mul_pos hq000 hq000))
      (Nat.mul_pos hq101 hq101)
  have hpos_P111 : P_111 ≥ 1 :=
    Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hq010 hq010) (Nat.mul_pos hq111 hq111))
        (Nat.mul_pos hp011 hp011))
      (Nat.mul_pos hp110 hp110)
  have hpos_Q111 : Q_111 ≥ 1 :=
    Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp010 hp010) (Nat.mul_pos hp111 hp111))
        (Nat.mul_pos hq011 hq011))
      (Nat.mul_pos hq110 hq110)
  apply five_var_exp_impossibility_w18 M_1 (by omega)
    (fun n => K_num * (wNum n * wNum n)) (fun n => wDen n * wDen n)
    1 C_top P_L Q_L P_P Q_P P_T Q_T P_001 Q_001 P_111 Q_111 (pTheta * pTheta) (qTheta * qTheta)
    (by decide) hpos_PL hpos_QL hpos_PP hpos_QP hpos_PT hpos_QT hpos_P001 hpos_Q001 hpos_P111 hpos_Q111
    ?hsand3g hw_sq
  intro n hn
  rcases hsand n (Nat.le_trans hM0_le_M1 hn) with ⟨hlo, hhi⟩
  rcases (binary_three_gram_debruijn_syzygies n (Nat.le_trans hM1_ge4 hn)).2 with
    ⟨he000, he100, he101, he011, he110, he010, s000, s100, s101, s011, s110, s010⟩
  let L := binBitLength n
  let P := binaryPopcount n
  let T := binaryAltTransitions n
  let g000 := binaryThreeGram000 n
  let g001 := binaryThreeGram001 n
  let g010 := binaryThreeGram010 n
  let g011 := binaryThreeGram011 n
  let g100 := binaryThreeGram100 n
  let g101 := binaryThreeGram101 n
  let g110 := binaryThreeGram110 n
  let g111 := binaryThreeGram111 n
  let b := n % 2
  let s2 := binarySecondMSB n
  let i0 := if n % 4 == 0 then 1 else 0
  let i1 := if n % 4 == 1 then 1 else 0
  let i3 := if n % 4 == 3 then 1 else 0
  let e000 := b + 2 - 2 * i0
  let e100 := 2 * i0
  let e101 := b
  let e011 := (1 - b) + 2 - 2 * s2
  let e110 := (1 - b) + 2 - 2 * i3
  let e010 := 2 * b + 2 * s2 - 2 * i1
  change e000 ≤ 3 at he000; change e100 ≤ 2 at he100; change e101 ≤ 1 at he101
  change e011 ≤ 3 at he011; change e110 ≤ 3 at he110; change e010 ≤ 4 at he010
  change 2 * g000 + (2 * P + T + 2 * g001 + 3) = 2 * L + e000 at s000
  change 2 * g100 = 2 * g001 + e100 at s100
  change 2 * g101 + (2 * g001 + 1) = T + e101 at s101
  change 2 * g011 + (T + 2 * g111 + 4) = 2 * P + e011 at s011
  change 2 * g110 + (T + 2 * g111 + 4) = 2 * P + e110 at s110
  change 2 * g010 + 2 * P = 2 * T + 2 * g111 + e010 at s010
  let Common :=
    (p_000 * q_000) ^ (2 * P + T + 2 * g001 + 3) *
    (p_010 * q_010) ^ (2 * P) *
    (p_011 * q_011) ^ (T + 2 * g111 + 4) *
    (p_101 * q_101) ^ (2 * g001 + 1) *
    (p_110 * q_110) ^ (T + 2 * g111 + 4)
  have hq_id := three_gram_monomial_sq_id_w18
    L P T g000 g001 g010 g011 g100 g101 g110 g111 e000 e010 e011 e100 e101 e110
    s000 s100 s101 s011 s110 s010
    q_000 q_001 q_010 q_011 q_100 q_101 q_110 q_111 p_000 p_010 p_011 p_101 p_110
  have hp_id := three_gram_monomial_sq_id_w18
    L P T g000 g001 g010 g011 g100 g101 g110 g111 e000 e010 e011 e100 e101 e110
    s000 s100 s101 s011 s110 s010
    p_000 p_001 p_010 p_011 p_100 p_101 p_110 p_111 q_000 q_010 q_011 q_101 q_110
  dsimp only at hq_id hp_id
  rw [Nat.mul_comm q_000 p_000, Nat.mul_comm q_010 p_010, Nat.mul_comm q_011 p_011,
      Nat.mul_comm q_101 p_101, Nat.mul_comm q_110 p_110] at hq_id
  let E_lo := (pow3 p_000 * pow4 p_011 * p_101 * pow4 p_110) *
    (q_000 ^ e000 * q_010 ^ e010 * q_011 ^ e011 * q_100 ^ e100 * q_101 ^ e101 * q_110 ^ e110)
  let E_hi := (pow3 q_000 * pow4 q_011 * q_101 * pow4 q_110) *
    (p_000 ^ e000 * p_010 ^ e010 * p_011 ^ e011 * p_100 ^ e100 * p_101 ^ e101 * p_110 ^ e110)
  have hE_lo_ge1 : E_lo ≥ 1 :=
    Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (p3_pos _ hp000) (p4_pos _ hp011)) hp101) (p4_pos _ hp110))
      (Nat.mul_pos
        (Nat.mul_pos
          (Nat.mul_pos
            (Nat.mul_pos (Nat.mul_pos (nat_pow_pos_of_pos _ hq000 _) (nat_pow_pos_of_pos _ hq010 _))
              (nat_pow_pos_of_pos _ hq011 _))
            (nat_pow_pos_of_pos _ hq100 _))
          (nat_pow_pos_of_pos _ hq101 _))
        (nat_pow_pos_of_pos _ hq110 _))
  have hE_hi_ge1 : E_hi ≥ 1 :=
    Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (p3_pos _ hq000) (p4_pos _ hq011)) hq101) (p4_pos _ hq110))
      (Nat.mul_pos
        (Nat.mul_pos
          (Nat.mul_pos
            (Nat.mul_pos (Nat.mul_pos (nat_pow_pos_of_pos _ hp000 _) (nat_pow_pos_of_pos _ hp010 _))
              (nat_pow_pos_of_pos _ hp011 _))
            (nat_pow_pos_of_pos _ hp100 _))
          (nat_pow_pos_of_pos _ hp101 _))
        (nat_pow_pos_of_pos _ hp110 _))
  have hp3_eq : ∀ z : Nat, z ^ 3 = pow3 z := fun z => by dsimp [pow3]; rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_one]
  have hp4_eq : ∀ z : Nat, z ^ 4 = pow4 z := fun z => by dsimp [pow4]; rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_one]
  have hp2_eq : ∀ z : Nat, z ^ 2 = z * z := fun z => by rw [Nat.pow_succ, Nat.pow_one]
  have hE_lo_le : E_lo ≤ E_lo_max := by
    dsimp only [E_lo, E_lo_max]
    exact Nat.mul_le_mul_left _
      (Nat.mul_le_mul
        (Nat.mul_le_mul
          (Nat.mul_le_mul
            (Nat.mul_le_mul
              (Nat.mul_le_mul
                (hp3_eq q_000 ▸ pow_mono_exp_ge1_w18s q_000 hq000 e000 3 he000)
                (hp4_eq q_010 ▸ pow_mono_exp_ge1_w18s q_010 hq010 e010 4 he010))
              (hp3_eq q_011 ▸ pow_mono_exp_ge1_w18s q_011 hq011 e011 3 he011))
            (hp2_eq q_100 ▸ pow_mono_exp_ge1_w18s q_100 hq100 e100 2 he100))
          (by simpa using pow_mono_exp_ge1_w18s q_101 hq101 e101 1 he101))
        (hp3_eq q_110 ▸ pow_mono_exp_ge1_w18s q_110 hq110 e110 3 he110))
  have hE_hi_leK : E_hi ≤ K_num := by
    dsimp only [E_hi, K_num]
    exact Nat.mul_le_mul_left _
      (Nat.mul_le_mul
        (Nat.mul_le_mul
          (Nat.mul_le_mul
            (Nat.mul_le_mul
              (Nat.mul_le_mul
                (hp3_eq p_000 ▸ pow_mono_exp_ge1_w18s p_000 hp000 e000 3 he000)
                (hp4_eq p_010 ▸ pow_mono_exp_ge1_w18s p_010 hp010 e010 4 he010))
              (hp3_eq p_011 ▸ pow_mono_exp_ge1_w18s p_011 hp011 e011 3 he011))
            (hp2_eq p_100 ▸ pow_mono_exp_ge1_w18s p_100 hp100 e100 2 he100))
          (by simpa using pow_mono_exp_ge1_w18s p_101 hp101 e101 1 he101))
        (hp3_eq p_110 ▸ pow_mono_exp_ge1_w18s p_110 hp110 e110 3 he110))
  have hlo_c := Nat.mul_le_mul_right Common (Nat.mul_le_mul hlo hlo)
  have hhi_c := Nat.mul_le_mul_right Common (Nat.mul_le_mul hhi hhi)
  let Q8 := q_000 ^ g000 * q_001 ^ g001 * q_010 ^ g010 * q_011 ^ g011 *
            q_100 ^ g100 * q_101 ^ g101 * q_110 ^ g110 * q_111 ^ g111
  let P8 := p_000 ^ g000 * p_001 ^ g001 * p_010 ^ g010 * p_011 ^ g011 *
            p_100 ^ g100 * p_101 ^ g101 * p_110 ^ g110 * p_111 ^ g111
  let BaseLo := Q_L ^ L * P_P ^ P * P_T ^ T * P_001 ^ g001 * P_111 ^ g111
  let BaseHi := P_L ^ L * Q_P ^ P * Q_T ^ T * Q_001 ^ g001 * Q_111 ^ g111
  change ((c_0 * Q8 * wDen n) * (c_0 * Q8 * wDen n)) * Common ≤
      ((P8 * wNum n) * (P8 * wNum n)) * Common at hlo_c
  change ((P8 * wNum n) * (P8 * wNum n)) * Common ≤
      ((C_hi * Q8 * wDen n) * (C_hi * Q8 * wDen n)) * Common at hhi_c
  change (Q8 * Q8) * Common = BaseLo * E_lo at hq_id
  change (P8 * P8) * Common = BaseHi * E_hi at hp_id
  have hl_rew := sq_common_scale_rew_w18 c_0 Q8 (wDen n) Common BaseLo E_lo hq_id
  have hr_rew := sq_common_noscale_rew_w18 P8 (wNum n) Common BaseHi E_hi hp_id
  have hhi_rhs_rew := sq_common_scale_rew_w18 C_hi Q8 (wDen n) Common BaseLo E_lo hq_id
  rw [hl_rew, hr_rew] at hlo_c
  rw [hr_rew, hhi_rhs_rew] at hhi_c
  change 1 * BaseLo * (wDen n * wDen n) ≤ BaseHi * (K_num * (wNum n * wNum n)) ∧
    BaseHi * (K_num * (wNum n * wNum n)) ≤ C_top * BaseLo * (wDen n * wDen n)
  refine ⟨?_, ?_⟩
  · have h1 : 1 * BaseLo * (wDen n * wDen n) ≤
        (c_0 * c_0 * E_lo) * (BaseLo * (wDen n * wDen n)) := by
      rw [Nat.one_mul]
      simpa using Nat.mul_le_mul_right (BaseLo * (wDen n * wDen n))
        (Nat.mul_le_mul (Nat.mul_le_mul hc0 hc0) hE_lo_ge1)
    exact Nat.le_trans h1 (Nat.le_trans hlo_c
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hE_hi_leK)))
  · have h1 : BaseHi * (K_num * (wNum n * wNum n)) ≤
        K_num * (BaseHi * (E_hi * (wNum n * wNum n))) := by
      have heq := sq_common_hi_swap_w18 K_num BaseHi E_hi (wNum n * wNum n)
      rw [heq]; simpa using Nat.mul_le_mul_right _ hE_hi_ge1
    have h2 : K_num * ((C_hi * C_hi * E_lo) * (BaseLo * (wDen n * wDen n))) ≤
        C_top * BaseLo * (wDen n * wDen n) := by
      have hl := sq_common_top_assoc_w18 K_num (C_hi * C_hi) E_lo BaseLo (wDen n * wDen n)
      rw [hl, Nat.mul_assoc C_top]
      exact Nat.mul_le_mul_right _
        (Nat.mul_le_mul (Nat.mul_le_mul_right K_num (Nat.le_succ _)) hE_lo_le)
    exact Nat.le_trans h1 (Nat.le_trans (Nat.mul_le_mul_left K_num hhi_c) h2)


-- ============================================================================
-- SECTION 2: Front C Part 2 (Branch P5.17) — 15th Solvable `(3x + 1)`-Cousin
--            `T_diamond15` with Genuine 13-Tier `ω^13` Cascade
--            (`Cone 16 -> Cone 15 -> ... -> Cone 5 -> Φ_diamond2`, `W18_H1`)
-- ============================================================================

/-- Cone 16 of `T_diamond15`: `22651973491 + x = 2 ^ k * 3 ^ m` with `k ≥ 54, m ≥ 1`
    (starting at `x = 2 ^ 54 * 3 - 22651973491 = 54043172876472461`). -/
def isDiamond15Cone16 (x : Nat) : Prop :=
  x ≥ 54043172876472461 ∧ x % 18014398509481984 = 18014375857508493 ∧ x % 3 = 2 ∧
    coprime23Core (22651973491 + x) = 1

instance (x : Nat) : Decidable (isDiamond15Cone16 x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/--
  15th solvable mixed-(2, 3) Collatz cousin `T_diamond15` on `Nat`:
  Extends `T_diamond14` by adding Cone 16 (`isDiamond15Cone16 x -> (3 * x + 1) / 8`, a genuine
  `v_2(3x + 1) = 3` Syracuse jump that steps `2 ^ k * 3 ^ m - 22651973491 -> 2 ^ (k - 3) * 3 ^ (m + 1) - 8494490059`
  directly into `Cone 15 -> Cone 14 -> ... -> Cone 5 -> Φ_diamond2`, e.g. `54043172876472461 -> 20266189828677173`
  in `30` steps to `1`, jumping `cousinDiamond2Phi` upward `+38.44x` and defeating 12-tier `ω^12` rankings)!
-/
def cousinDiamond15Step (x : Nat) : Nat :=
  if isDiamond15Cone16 x then (3 * x + 1) / 8 else cousinDiamond14Step x

def cousinDiamond15Iter : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamond15Iter k (cousinDiamond15Step x)

private theorem cousinDiamond15Iter_add : ∀ (a b x : Nat),
    cousinDiamond15Iter (a + b) x = cousinDiamond15Iter b (cousinDiamond15Iter a x)
  | 0, _, _ => by simp [cousinDiamond15Iter]
  | a + 1, b, x => by
    rw [Nat.succ_add]
    exact cousinDiamond15Iter_add a b (cousinDiamond15Step x)

/-- Signed extension of `T_diamond15` (`q = 3`) to `Int` for `M2 = Z^-` separation. -/
def cousinDiamond15StepInt (x : Int) : Int :=
  if x ≥ 54043172876472461 ∧ x % 18014398509481984 = 18014375857508493 ∧ x % 3 = 2 ∧
      coprime23Core (22651973491 + x.toNat) = 1
  then (3 * x + 1) / 8
  else cousinDiamond14StepInt x

def cousinDiamond15IterInt : Nat -> Int -> Int
  | 0, x => x
  | k + 1, x => cousinDiamond15IterInt k (cousinDiamond15StepInt x)

/-- Hensel lift of `invMod2251799813685248Odd` (`2^51`) to `mod 18014398509481984` (`2^54`, `51 * 2 = 102 ≥ 54`). -/
def invMod18014398509481984Odd (d : Nat) : Nat :=
  let i51 := invMod2251799813685248Odd d
  (i51 * (36028797018963970 - ((d % 18014398509481984) * i51) % 18014398509481984)) % 18014398509481984

/-- Canonical reduced-pair extension of `T_diamond15` (`q = 3`) to positive `Q_(6)^+`. -/
def cousinDiamond15StepQ6 (p : Nat × Nat) : Nat × Nat :=
  let num := p.1
  let den := p.2
  let r54 := (num * invMod18014398509481984Odd den) % 18014398509481984
  let r3 := (num * (den % 3)) % 3
  if num ≥ 54043172876472461 * den ∧ r54 = 18014375857508493 ∧ r3 = 2 ∧
      core3 (core2 (22651973491 * den + num)) = den
  then reduceRatPair (3 * num + den) (8 * den)
  else cousinDiamond14StepQ6 p

def cousinDiamond15IterQ6 : Nat -> (Nat × Nat) -> (Nat × Nat)
  | 0, p => p
  | k + 1, p => cousinDiamond15IterQ6 k (cousinDiamond15StepQ6 p)

/-- Generalized odd-multiplier `q` step of `T_diamond15` on `Nat` for `M3` (`q = 7`) separation. -/
def cousinDiamond15StepParam (q x : Nat) : Nat :=
  if isDiamond15Cone16 x then (q * x + 1) / 8 else cousinDiamond14StepParam q x

def cousinDiamond15IterParam (q : Nat) : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamond15IterParam q k (cousinDiamond15StepParam q x)

private theorem ite_false_dec_w18s {p : Prop} [inst : Decidable p] {α : Type} {a b : α} (hnp : ¬ p) :
    (if p then a else b) = b := by
  cases inst with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

private theorem hensel_inv_lift_w18 (M1 M2 S C d i1 : Nat)
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

private theorem core3_core2_eq_coprime23Core_w18 :
    ∀ (fuel n : Nat), n > 0 -> n ≤ fuel -> core3 (core2 n) = coprime23Core n
  | 0, _, hn, hle => by omega
  | fuel + 1, n, hn, hle => by
    by_cases hev : n % 2 = 0
    · let k := n / 2
      have hk_pos : k > 0 := by dsimp [k]; omega
      rw [show n = 2 * k by dsimp [k]; omega, core2_mul2 k hk_pos, coprime23Core_mul2 k hk_pos]
      exact core3_core2_eq_coprime23Core_w18 fuel k hk_pos (by dsimp [k]; omega)
    · have hodd : n % 2 = 1 := by omega
      rcases core3_decomp n hn with ⟨_, _, _, _, hmul⟩
      have hc3_odd : core3 n % 2 = 1 := by
        by_cases hc3_ev : core3 n % 2 = 0
        · have hm0 : (v3Pow n * core3 n) % 2 = 0 := by rw [Nat.mul_mod, hc3_ev, Nat.mul_zero]
          rw [hmul] at hm0; omega
        · omega
      unfold coprime23Core
      rw [core2_of_odd n hodd, core2_of_odd (core3 n) hc3_odd]

private theorem reduceRatPair_div_exact_w18 (a m : Nat) (hm : m > 0) (hdvd : m ∣ a) :
    reduceRatPair a m = (a / m, 1) := by
  rcases hdvd with ⟨q, rfl⟩
  unfold reduceRatPair
  have hgcd : Nat.gcd (m * q) m = m :=
    Nat.dvd_antisymm (Nat.gcd_dvd_right (m * q) m) (Nat.dvd_gcd ⟨q, rfl⟩ (Nat.dvd_refl m))
  dsimp only
  rw [hgcd, Nat.div_self hm]

private theorem dvd_three_mul_add_one_of_mod_w18 (x M D Qm Qr R Qt : Nat)
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
  Theorem W18.3c (`cousin_diamond15_q6_noninteger_avoids_cone16`,
  choice-free `zero custom axioms`):
  Universal Non-Integer Rational Exclusion from Cone 16 on `M1 = Q_(6)^+`:
  For EVERY reduced non-integer rational `(num, den)` (`Nat.gcd num den = 1` and `den > 1`),
  `core3 (core2 (22651973491 * den + num)) ≠ den`, so `cousinDiamond15StepQ6 (num, den)` NEVER enters
  Cone 16 and agrees identically with `cousinDiamond14StepQ6 (num, den)` (`Branch P5.17`, `W18_H1`).
-/
theorem cousin_diamond15_q6_noninteger_avoids_cone16 (num den : Nat)
    (hgcd : Nat.gcd num den = 1) (hden : den > 1) :
    core3 (core2 (22651973491 * den + num)) ≠ den ∧
    cousinDiamond15StepQ6 (num, den) = cousinDiamond14StepQ6 (num, den) := by
  have hne : core3 (core2 (22651973491 * den + num)) ≠ den := by
    intro heq
    have hdvd_sum : den ∣ (22651973491 * den + num) := by
      have hc_dvd : core3 (core2 (22651973491 * den + num)) ∣ (22651973491 * den + num) :=
        Nat.dvd_trans (core3Aux_dvd_w8 _ _) (core2Aux_dvd_w8 _ _)
      rwa [heq] at hc_dvd
    rcases hdvd_sum with ⟨k, hk⟩
    have hdvd_num : den ∣ num := ⟨k - 22651973491, by
      rcases Nat.lt_or_ge k 22651973491 with hlt | hge
      · exfalso
        have hm := Nat.mul_le_mul_left den (show k ≤ 22651973490 by omega)
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
  unfold cousinDiamond15StepQ6
  dsimp only
  exact ite_false_dec_w18s (fun ⟨_, _, _, hc⟩ => hne hc)

/--
  Theorem W18.3d (`cousin_diamond15_hensel_inv_and_nat_int_q6_agreement`,
  `zero custom axioms`):
  Universal Newton–Hensel `mod 2^54` (`18014398509481984`) Odd-Inverse Correctness, Exact
  `Nat`/`Int`/`Q_(6)^+` Step Agreement, & Universal Non-Integer Rational Exclusion from Cone 16
  on `M1 = Q_(6)^+` (`Branch P5.17`, `W18_H1`).
-/
theorem cousin_diamond15_hensel_inv_and_nat_int_q6_agreement :
    (∀ d : Nat, d % 2 = 1 -> (d * invMod18014398509481984Odd d) % 18014398509481984 = 1) ∧
    (∀ x : Nat, cousinDiamond15StepInt (x : Int) = (cousinDiamond15Step x : Int)) ∧
    (∀ x : Nat, cousinDiamond15StepQ6 (x, 1) = (cousinDiamond15Step x, 1)) ∧
    (∀ num den : Nat, Nat.gcd num den = 1 -> den > 1 ->
      core3 (core2 (22651973491 * den + num)) ≠ den ∧
      cousinDiamond15StepQ6 (num, den) = cousinDiamond14StepQ6 (num, den)) := by
  have hinv51 := cousin_diamond14_hensel_inv_and_nat_int_q6_agreement.1
  have hinv54 : ∀ d : Nat, d % 2 = 1 -> (d * invMod18014398509481984Odd d) % 18014398509481984 = 1 := by
    intro d hodd
    exact hensel_inv_lift_w18 2251799813685248 18014398509481984 281474976710656 36028797018963970
      d (invMod2251799813685248Odd d) (by decide) (by decide) (by decide) (hinv51 d hodd)
  refine ⟨hinv54, ?_, ?_, cousin_diamond15_q6_noninteger_avoids_cone16⟩
  · intro x
    have h1 : ((x : Int) ≥ 54043172876472461) ↔ (x ≥ 54043172876472461) := by omega
    have h2 : ((x : Int) % 18014398509481984 = 18014375857508493) ↔
        (x % 18014398509481984 = 18014375857508493) := ⟨Int.ofNat.inj, congrArg Int.ofNat⟩
    have h3 : ((x : Int) % 3 = 2) ↔ (x % 3 = 2) := ⟨Int.ofNat.inj, congrArg Int.ofNat⟩
    have hdiv : ((3 * (x : Int) + 1) / 8) = (((3 * x + 1) / 8 : Nat) : Int) := by omega
    have htoNat : (x : Int).toNat = x := rfl
    unfold cousinDiamond15StepInt cousinDiamond15Step isDiamond15Cone16
    rw [htoNat]; simp only [h1, h2, h3]
    by_cases hc16 : x ≥ 54043172876472461 ∧ x % 18014398509481984 = 18014375857508493 ∧ x % 3 = 2 ∧
        coprime23Core (22651973491 + x) = 1
    · simp only [hc16, and_self, ite_true, hdiv]
    · simp only [hc16, ite_false]
      exact cousin_diamond14_hensel_inv_and_nat_int_q6_agreement.2.1 x
  · have hi54 : invMod18014398509481984Odd 1 = 1 := by decide
    have hm3_1 : (1 : Nat) % 3 = 1 := by decide
    intro x
    have hcc : core3 (core2 (22651973491 + x)) = coprime23Core (22651973491 + x) :=
      core3_core2_eq_coprime23Core_w18 (22651973491 + x) (22651973491 + x) (by omega) (Nat.le_refl _)
    unfold cousinDiamond15StepQ6 cousinDiamond15Step isDiamond15Cone16
    simp only [hi54, hm3_1, Nat.mul_one, hcc]
    by_cases hc16 : x ≥ 54043172876472461 ∧ x % 18014398509481984 = 18014375857508493 ∧ x % 3 = 2 ∧
        coprime23Core (22651973491 + x) = 1
    · simp only [hc16, and_self, ite_true]
      exact reduceRatPair_div_exact_w18 (3 * x + 1) 8 (by decide)
        (dvd_three_mul_add_one_of_mod_w18 x 18014398509481984 8 2251799813685248 2251796982188561 5 2
          (by decide) hc16.2.1 (by decide))
    · simp only [hc16, ite_false]
      exact cousin_diamond14_hensel_inv_and_nat_int_q6_agreement.2.2.1 x

private theorem d15_eq_d14_of_not_cone16 (x : Nat) (hnc16 : ¬ isDiamond15Cone16 x) :
    cousinDiamond15Step x = cousinDiamond14Step x := by
  unfold cousinDiamond15Step; simp [hnc16]

-- Modular Cone-16 avoidance helpers (`18014375857508493 % 512 = 141, % 128 = 13, % 64 = 13, % 32 = 13, % 16 = 13, % 8 = 5`):

private theorem mod512_of_cone16 (z : Nat) (hc16 : isDiamond15Cone16 z) : z % 512 = 141 := by
  have h := congrArg (· % 512) hc16.2.1
  rw [Nat.mod_mod_of_dvd z (by decide : 512 ∣ 18014398509481984),
      show 18014375857508493 % 512 = 141 by decide] at h
  exact h

private theorem mod128_of_cone16 (z : Nat) (hc16 : isDiamond15Cone16 z) : z % 128 = 13 := by
  have h := congrArg (· % 128) (mod512_of_cone16 z hc16)
  rw [Nat.mod_mod_of_dvd z (by decide : 128 ∣ 512), show 141 % 128 = 13 by decide] at h
  exact h

private theorem mod64_of_cone16 (z : Nat) (hc16 : isDiamond15Cone16 z) : z % 64 = 13 := by
  have h := congrArg (· % 64) (mod128_of_cone16 z hc16)
  rw [Nat.mod_mod_of_dvd z (by decide : 64 ∣ 128), show 13 % 64 = 13 by decide] at h
  exact h

private theorem mod32_of_cone16 (z : Nat) (hc16 : isDiamond15Cone16 z) : z % 32 = 13 := by
  have h := congrArg (· % 32) (mod64_of_cone16 z hc16)
  rw [Nat.mod_mod_of_dvd z (by decide : 32 ∣ 64), show 13 % 32 = 13 by decide] at h
  exact h

private theorem mod16_of_cone16 (z : Nat) (hc16 : isDiamond15Cone16 z) : z % 16 = 13 := by
  have h := congrArg (· % 16) (mod32_of_cone16 z hc16)
  rw [Nat.mod_mod_of_dvd z (by decide : 16 ∣ 32), show 13 % 16 = 13 by decide] at h
  exact h

private theorem not_cone16_of_mod8_ne_5 (z : Nat) (hm8 : z % 8 ≠ 5) : ¬ isDiamond15Cone16 z := by
  intro hc16
  have h := congrArg (· % 8) (mod16_of_cone16 z hc16)
  rw [Nat.mod_mod_of_dvd z (by decide : 8 ∣ 16)] at h
  exact hm8 h

private theorem not_cone16_of_mod16_ne_13 (z : Nat) (hm16 : z % 16 ≠ 13) : ¬ isDiamond15Cone16 z :=
  fun hc16 => hm16 (mod16_of_cone16 z hc16)

private theorem not_cone16_of_mod32_ne_13 (z : Nat) (hm32 : z % 32 ≠ 13) : ¬ isDiamond15Cone16 z :=
  fun hc16 => hm32 (mod32_of_cone16 z hc16)

private theorem not_cone16_of_mod64_ne_13 (z : Nat) (hm64 : z % 64 ≠ 13) : ¬ isDiamond15Cone16 z :=
  fun hc16 => hm64 (mod64_of_cone16 z hc16)

private theorem not_cone16_of_mod128_ne_13 (z : Nat) (hm128 : z % 128 ≠ 13) : ¬ isDiamond15Cone16 z :=
  fun hc16 => hm128 (mod128_of_cone16 z hc16)

private theorem not_cone16_of_mod512_ne_141 (z : Nat) (hm512 : z % 512 ≠ 141) : ¬ isDiamond15Cone16 z :=
  fun hc16 => hm512 (mod512_of_cone16 z hc16)

private theorem not_cone16_of_mod3_ne_2 (z : Nat) (hm3 : z % 3 ≠ 2) : ¬ isDiamond15Cone16 z :=
  fun ⟨_, _, h3, _⟩ => hm3 h3

private theorem cousinDiamond15Step_pos (x : Nat) (hx : x > 0) : cousinDiamond15Step x > 0 := by
  unfold cousinDiamond15Step
  by_cases hc16 : isDiamond15Cone16 x
  · simp only [hc16, ite_true]
    have hge : x ≥ 54043172876472461 := hc16.1
    clear hc16
    exact Nat.lt_of_lt_of_le (by decide : 0 < (3 * 54043172876472461 + 1) / 8)
      (Nat.div_le_div_right (by omega))
  · simp only [hc16, ite_false]
    unfold cousinDiamond14Step
    by_cases hc15 : isDiamond14Cone15 x
    · simp only [hc15, ite_true]
      have hge : x ≥ 6755390946565685 := hc15.1
      clear hc15 hc16
      exact Nat.lt_of_lt_of_le (by decide : 0 < (3 * 6755390946565685 + 1) / 32)
        (Nat.div_le_div_right (by omega))
    · simp only [hc15, ite_false]
      unfold cousinDiamond13Step
      by_cases hc14 : isDiamond13Cone14 x
      · simp only [hc14, ite_true]
        have hge : x ≥ 211105436174549 := hc14.1
        clear hc14 hc15 hc16
        exact Nat.lt_of_lt_of_le (by decide : 0 < (3 * 211105436174549 + 1) / 128)
          (Nat.div_le_div_right (by omega))
      · simp only [hc14, ite_false]
        unfold cousinDiamond12Step
        by_cases hc13 : isDiamond12Cone13 x
        · simp only [hc13, ite_true]
          have hge : x ≥ 1649248777013 := hc13.1
          clear hc13 hc14 hc15 hc16
          exact Nat.lt_of_lt_of_le (by decide : 0 < (3 * 1649248777013 + 1) / 32)
            (Nat.div_le_div_right (by omega))
        · simp only [hc13, ite_false]; exact cousinDiamond11Step_pos x hx

private theorem not_cone16_six_mul_pow9_sub1_w18 (m : Nat) :
    ¬ isDiamond15Cone16 (6 * 9 ^ m - 1) := by
  have h9_16 : ∀ k : Nat, 9 ^ k % 16 = 1 ∨ 9 ^ k % 16 = 9 := by
    intro k; induction k with
    | zero => exact Or.inl rfl
    | succ k' ih =>
      rw [Nat.pow_succ 9 k', Nat.mul_mod]
      rcases ih with h | h <;> (rw [h]; decide)
  apply not_cone16_of_mod16_ne_13
  have hp9_pos : 9 ^ m ≥ 1 := nat_pow_pos_of_pos 9 (by decide) m
  have hdm := (Nat.div_add_mod (9 ^ m) 16).symm
  rcases h9_16 m with h1 | h9 <;> omega

/--
  Theorem W18.3e (`cousin_diamond15_outside_cones4to16_descent_and_mod16_nonreentry`,
  `zero custom axioms`):
  Strict `cousinDiamond2Phi` Descent Outside Cones 4..16 & Universal `mod 16` Post-Climb
  Non-Reentry into Cone 16 (`∀ m : Nat, ¬ isDiamond15Cone16 (6 * 9 ^ m - 1)`,
  `Branch P5.17`, `W18_H1`).
-/
theorem cousin_diamond15_outside_cones4to16_descent_and_mod16_nonreentry :
    (∀ x : Nat, x > 2 ->
      ¬ isDiamond3Cone4 x -> ¬ isDiamond4Cone5 x ->
      ¬ isDiamond5Cone6 x -> ¬ isDiamond6Cone7 x ->
      ¬ isDiamond7Cone8 x -> ¬ isDiamond8Cone9 x ->
      ¬ isDiamond9Cone10 x -> ¬ isDiamond10Cone11 x ->
      ¬ isDiamond11Cone12 x -> ¬ isDiamond12Cone13 x ->
      ¬ isDiamond13Cone14 x -> ¬ isDiamond14Cone15 x ->
      ¬ isDiamond15Cone16 x ->
      cousinDiamond2Phi (cousinDiamond15Step x) < cousinDiamond2Phi x) ∧
    (∀ m : Nat, ¬ isDiamond15Cone16 (6 * 9 ^ m - 1)) := by
  refine ⟨?_, not_cone16_six_mul_pow9_sub1_w18⟩
  intro x hx hnc4 hnc5 hnc6 hnc7 hnc8 hnc9 hnc10 hnc11 hnc12 hnc13 hnc14 hnc15 hnc16
  rw [d15_eq_d14_of_not_cone16 x hnc16]
  exact cousin_diamond14_outside_cones4to15_descent_and_mod117_nonreentry.1 x hx
    hnc4 hnc5 hnc6 hnc7 hnc8 hnc9 hnc10 hnc11 hnc12 hnc13 hnc14 hnc15

private theorem isDiamond14Cone15_of_pow2_pow3_w18 (a b : Nat) (ha : a ≥ 51) (hb : b ≥ 1) :
    isDiamond14Cone15 (2 ^ a * 3 ^ b - 8494490059) := by
  have hc : (2 : Nat) ^ 51 = 2251799813685248 := by decide
  have hp2_ge : 2 ^ a ≥ 2251799813685248 := by rw [← hc]; exact pow2_mono_nat ha
  have hp3_ge : 3 ^ b ≥ 3 := by simpa using nat_pow_mono_exp_pos 3 1 b (by decide) hb
  have hprod_ge : 2 ^ a * 3 ^ b ≥ 6755399441055744 := by simpa using Nat.mul_le_mul hp2_ge hp3_ge
  have hp51 : 2251799813685248 ∣ 2 ^ a * 3 ^ b := by
    rw [show a = 51 + (a - 51) by omega, Nat.pow_add 2 51 (a - 51), hc, Nat.mul_assoc]
    exact ⟨2 ^ (a - 51) * 3 ^ b, rfl⟩
  have hp3_div : 3 ∣ 2 ^ a * 3 ^ b := by
    rw [show b = 1 + (b - 1) by omega, Nat.pow_add 3 1 (b - 1), Nat.pow_one,
        ← Nat.mul_assoc (2 ^ a) 3, Nat.mul_comm (2 ^ a) 3, Nat.mul_assoc]
    exact ⟨2 ^ a * 3 ^ (b - 1), rfl⟩
  refine ⟨by clear hc hp2_ge hp3_ge hp51 hp3_div; generalize 2 ^ a * 3 ^ b = P at hprod_ge ⊢; omega,
          ?_, ?_, ?_⟩
  · rcases hp51 with ⟨k, hk⟩
    clear hc hp2_ge hp3_ge hp3_div
    generalize 2 ^ a * 3 ^ b = P at hprod_ge hk ⊢
    rw [hk, show k = (k - 1) + 1 by omega, Nat.mul_add 2251799813685248 (k - 1) 1, Nat.mul_one]
    generalize k - 1 = k'
    rw [show 2251799813685248 * k' + 2251799813685248 - 8494490059 = 2251791319195189 + 2251799813685248 * k' by omega,
        Nat.add_mul_mod_self_left]
  · rcases hp3_div with ⟨k3, hk3⟩
    clear hc hp2_ge hp3_ge hp51
    generalize 2 ^ a * 3 ^ b = P at hprod_ge hk3 ⊢; omega
  · rw [show 8494490059 + (2 ^ a * 3 ^ b - 8494490059) = 2 ^ a * 3 ^ b by
          clear hc hp2_ge hp3_ge hp51 hp3_div; generalize 2 ^ a * 3 ^ b = P at hprod_ge ⊢; omega]
    exact coprime23Core_pow2_pow3 a b

private theorem not_cone15_of_mod32_ne_21_w18 (z : Nat) (hm32 : z % 32 ≠ 21) : ¬ isDiamond14Cone15 z := by
  rintro ⟨_, h51, _, _⟩
  have h := congrArg (· % 32) h51
  rw [Nat.mod_mod_of_dvd z (by decide : 32 ∣ 2251799813685248),
      show 2251791319195189 % 32 = 21 by decide] at h
  exact hm32 h

private theorem not_cone14_of_mod32_ne_21_w18 (z : Nat) (hm32 : z % 32 ≠ 21) : ¬ isDiamond13Cone14 z := by
  rintro ⟨_, h46, _, _⟩
  have h := congrArg (· % 32) h46
  rw [Nat.mod_mod_of_dvd z (by decide : 32 ∣ 70368744177664),
      show 70367947819221 % 32 = 21 by decide] at h
  exact hm32 h

private theorem not_cone13_of_mod32_ne_21_w18 (z : Nat) (hm32 : z % 32 ≠ 21) : ¬ isDiamond12Cone13 z := by
  rintro ⟨_, h39, _, _⟩
  have h := congrArg (· % 32) h39
  rw [Nat.mod_mod_of_dvd z (by decide : 32 ∣ 549755813888),
      show 549737149237 % 32 = 21 by decide] at h
  exact hm32 h

private theorem d14_eq_d13_of_not_cone15_w18 (x : Nat) (hnc15 : ¬ isDiamond14Cone15 x) :
    cousinDiamond14Step x = cousinDiamond13Step x := by
  unfold cousinDiamond14Step; exact ite_false_dec_w18s hnc15

private theorem d13_eq_d12_of_not_cone14_w18 (x : Nat) (hnc14 : ¬ isDiamond13Cone14 x) :
    cousinDiamond13Step x = cousinDiamond12Step x := by
  unfold cousinDiamond13Step; exact ite_false_dec_w18s hnc14

private theorem d12_eq_d11_of_not_cone13_w18 (x : Nat) (hnc13 : ¬ isDiamond12Cone13 x) :
    cousinDiamond12Step x = cousinDiamond11Step x := by
  unfold cousinDiamond12Step; exact ite_false_dec_w18s hnc13

private theorem d15_eq_d11_of_mod32_w18 (z : Nat)
    (h16 : z % 32 ≠ 13) (h15 : z % 32 ≠ 21) :
    cousinDiamond15Step z = cousinDiamond11Step z := by
  rw [d15_eq_d14_of_not_cone16 z (not_cone16_of_mod32_ne_13 z h16),
      d14_eq_d13_of_not_cone15_w18 z (not_cone15_of_mod32_ne_21_w18 z h15),
      d13_eq_d12_of_not_cone14_w18 z (not_cone14_of_mod32_ne_21_w18 z h15),
      d12_eq_d11_of_not_cone13_w18 z (not_cone13_of_mod32_ne_21_w18 z h15)]

private theorem d15_eq_d3_of_even_w18 (z : Nat) (hev : z % 2 = 0) :
    cousinDiamond15Step z = cousinDiamond3Step z := by
  have hdm := (Nat.div_add_mod z 32).symm
  rw [d15_eq_d11_of_mod32_w18 z (by omega) (by omega),
      cousinDiamond11Step_eq_d10_of_not_cone12 z (not_cone12_of_even z hev),
      cousinDiamond10Step_eq_d9_of_not_cone11 z (not_cone11_of_even z hev),
      cousinDiamond9Step_eq_d8_of_not_cone10 z (not_cone10_of_even z hev),
      cousinDiamond8Step_eq_d7_of_not_cone9 z (not_cone9_of_even z hev),
      cousinDiamond7Step_eq_d6_of_not_cone8 z (not_cone8_of_even z hev),
      cousinDiamond6Step_eq_d5_of_not_cone7 z (not_cone7_of_even z hev),
      cousinDiamond5Step_eq_d4_of_not_cone6 z (not_cone6_of_even z hev),
      cousinDiamond4Step_eq_d3_of_not_cone5 z (by rintro ⟨_, h32, _, _⟩; omega)]

private theorem d15_eq_d3_of_not_cones5to16_w18 (z : Nat)
    (h16 : ¬ isDiamond15Cone16 z) (h15 : ¬ isDiamond14Cone15 z)
    (h14 : ¬ isDiamond13Cone14 z) (h13 : ¬ isDiamond12Cone13 z) (h12 : ¬ isDiamond11Cone12 z)
    (h11 : ¬ isDiamond10Cone11 z) (h10 : ¬ isDiamond9Cone10 z) (h9 : ¬ isDiamond8Cone9 z)
    (h8 : ¬ isDiamond7Cone8 z) (h7 : ¬ isDiamond6Cone7 z) (h6 : ¬ isDiamond5Cone6 z)
    (h5 : ¬ isDiamond4Cone5 z) :
    cousinDiamond15Step z = cousinDiamond3Step z := by
  rw [d15_eq_d14_of_not_cone16 z h16,
      d14_eq_d13_of_not_cone15_w18 z h15,
      d13_eq_d12_of_not_cone14_w18 z h14,
      d12_eq_d11_of_not_cone13_w18 z h13,
      cousinDiamond11Step_eq_d10_of_not_cone12 z h12,
      cousinDiamond10Step_eq_d9_of_not_cone11 z h11,
      cousinDiamond9Step_eq_d8_of_not_cone10 z h10,
      cousinDiamond8Step_eq_d7_of_not_cone9 z h9,
      cousinDiamond7Step_eq_d6_of_not_cone8 z h8,
      cousinDiamond6Step_eq_d5_of_not_cone7 z h7,
      cousinDiamond5Step_eq_d4_of_not_cone6 z h6,
      cousinDiamond4Step_eq_d3_of_not_cone5 z h5]

private theorem cousin_diamond15_mersenne_scaled :
    ∀ (k a q : Nat), k + 1 ≤ a -> q ≥ 1 ->
      cousinDiamond15Iter k (2 ^ a * q - 1) = 3 ^ k * 2 ^ (a - k) * q - 1
  | 0, _, _, _, _ => by simp [cousinDiamond15Iter]
  | k + 1, a, q, hka, hq => by
    have hp4 : 2 ^ a * q = 4 * (2 ^ (a - 2) * q) := by
      conv => lhs; rw [show a = (a - 2) + 2 by omega]
      rw [Nat.pow_add 2 (a - 2) 2, show (2 : Nat) ^ 2 = 4 from rfl,
          Nat.mul_comm (2 ^ (a - 2)) 4, Nat.mul_assoc]
    have hm_pos : 2 ^ (a - 2) * q ≥ 1 := Nat.mul_le_mul (pow2_pos_nat (a - 2)) hq
    have hdm32 := (Nat.div_add_mod (2 ^ a * q - 1) 32).symm
    have hm4 : (2 ^ a * q - 1) % 4 = 3 := by omega
    simp only [cousinDiamond15Iter]
    rw [d15_eq_d11_of_mod32_w18 _ (by omega) (by omega)]
    have hd11 := cousin_diamond11_mersenne_scaled 1 a q (by omega) hq
    simp only [cousinDiamond11Iter, Nat.pow_one] at hd11
    rw [show cousinDiamond11Step (2 ^ a * q - 1) = 2 ^ (a - 1) * (3 * q) - 1 by
          rw [hd11]; apply congrArg (· - 1); ac_rfl,
        cousin_diamond15_mersenne_scaled k (a - 1) (3 * q) (by omega) (by omega),
        show a - 1 - k = a - (k + 1) by omega, Nat.pow_succ 3 k]
    apply congrArg (· - 1); ac_rfl

private theorem cousin_diamond15_even9_spine_drain :
    ∀ k : Nat, cousinDiamond15Iter k ((9 ^ (k + 1) - 1) / 4) = 2
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
    simp only [cousinDiamond15Iter]
    change cousinDiamond15Iter k (cousinDiamond15Step ((9 ^ (j + 1) - 1) / 4)) = 2
    rw [he_j1, d15_eq_d3_of_even_w18 _ (by omega)]
    have hd3 : cousinDiamond3Step (18 * q + 2) = (9 ^ j - 1) / 4 := by
      rw [he_j]; unfold cousinDiamond3Step
      have hq_pos : q ≥ 1 := by dsimp [q]; omega
      have hodd_f : ¬ ((18 * q + 2) % 2 = 1) := by omega
      have h18_t : 18 * q + 2 ≥ 20 ∧ (18 * q + 2) % 18 = 2 := ⟨by omega, by omega⟩
      simp only [hodd_f, h18_t, and_self, ite_true, ite_false]; omega
    rw [hd3]
    exact cousin_diamond15_even9_spine_drain k

private theorem cousin_diamond15_pow3_sub1_drain :
    ∀ k : Nat, cousinDiamond15Iter k (3 ^ (k + 1) - 1) = 2
  | 0 => rfl
  | k + 1 => by
    let j := k + 1
    have hp3_ge3 : 3 ^ j ≥ 3 := by dsimp [j]; rw [Nat.pow_succ]; have := pow3_pos_nat k; omega
    have ho_j1 := pow3_odd_nat_sec8 (j + 1)
    have hp_j1 := pow3_pos_nat (j + 1)
    simp only [cousinDiamond15Iter]
    change cousinDiamond15Iter k (cousinDiamond15Step (3 ^ (j + 1) - 1)) = 2
    rw [d15_eq_d3_of_even_w18 _ (by omega)]
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
    exact cousin_diamond15_pow3_sub1_drain k

private theorem cousin_diamond15_cone5_two_step_climb :
    ∀ (q_c a b : Nat), 3 * q_c + 2 ≤ a -> b ≥ 1 ->
      cousinDiamond15Iter (2 * q_c) (2 ^ a * 3 ^ b - 7) =
        2 ^ (a - 3 * q_c) * 3 ^ (b + 2 * q_c) - 7
  | 0, _, _, _, _ => by simp [cousinDiamond15Iter]
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
    have hs1 : cousinDiamond15Step (2 ^ a * 3 ^ b - 7) = mid := by
      rw [d15_eq_d11_of_mod32_w18 _ (by have := hc5.2.1; omega) (by have := hc5.2.1; omega)]
      exact hd11_s1
    have hs2 : cousinDiamond15Step mid = 2 ^ (a - 3) * 3 ^ (b + 2) - 7 := by
      have hdm32 := (Nat.div_add_mod mid 32).symm
      rw [d15_eq_d11_of_mod32_w18 _ (by omega) (by omega)]
      exact hd11_2
    rw [Nat.mul_succ 2 q_c, Nat.add_comm (2 * q_c) 2, cousinDiamond15Iter_add 2 (2 * q_c)]
    have hi2 : cousinDiamond15Iter 2 (2 ^ a * 3 ^ b - 7) = 2 ^ (a - 3) * 3 ^ (b + 2) - 7 := by
      simp only [cousinDiamond15Iter, hs1, hs2]
    rw [hi2, cousin_diamond15_cone5_two_step_climb q_c (a - 3) (b + 2) (by omega) (by omega)]
    apply congrArg (· - 7); congr 1
    · apply congrArg (2 ^ ·); omega
    · apply congrArg (3 ^ ·); omega

private theorem not_cone15_of_mod3_ne_2_w18 (x : Nat) (h : x % 3 ≠ 2) : ¬ isDiamond14Cone15 x :=
  fun hc => h hc.2.2.1

private theorem not_cone14_of_mod3_ne_2_w18 (x : Nat) (h : x % 3 ≠ 2) : ¬ isDiamond13Cone14 x :=
  fun hc => h hc.2.2.1

private theorem not_cone13_of_mod3_ne_2_w18 (x : Nat) (h : x % 3 ≠ 2) : ¬ isDiamond12Cone13 x :=
  fun hc => h hc.2.2.1

private theorem not_cone5_of_mod3_ne_2_w18 (x : Nat) (h : x % 3 ≠ 2) : ¬ isDiamond4Cone5 x :=
  fun hc => h hc.2.2.1

private theorem ne8_mod9_of_mod3_eq1_w18 (x : Nat) (h : x % 3 = 1) : x % 9 ≠ 8 := by omega

private theorem d15_zr_yr_steps_w18 (m : Nat) (hm1 : m ≥ 1) :
    cousinDiamond15Step (2 * 9 ^ m - 1) = (3 * 9 ^ m - 1) / 2 ∧
    cousinDiamond15Step ((3 * 9 ^ m - 1) / 2) = (9 ^ (m + 1) - 1) / 4 := by
  have hp9_ge9 : 9 ^ m ≥ 9 := by
    rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]
    have := nat_pow_pos_of_pos 9 (by decide) (m - 1); omega
  have hp9_m8 := pow9_mod8_eq_one_w5 m
  let zr := 2 * 9 ^ m - 1
  let yr := (3 * 9 ^ m - 1) / 2
  have hsz : cousinDiamond15Step zr = yr := by
    have hz_dm := (Nat.div_add_mod zr 32).symm
    have hz_m8 : zr % 8 = 1 := by dsimp [zr]; omega
    rw [d15_eq_d3_of_not_cones5to16_w18 zr
          (not_cone16_of_mod8_ne_5 zr (by omega))
          (not_cone15_of_mod32_ne_21_w18 zr (by omega))
          (not_cone14_of_mod32_ne_21_w18 zr (by omega))
          (not_cone13_of_mod32_ne_21_w18 zr (by omega))
          (not_cone12_of_mod8_ne_5 zr (by omega))
          (not_cone11_of_mod8_ne_5 zr (by omega))
          (not_cone10_of_mod8_ne_5 zr (by omega))
          (not_cone9_of_mod8_ne_5 zr (by omega))
          (not_cone8_of_mod8_ne_5 zr (by omega))
          (not_cone7_of_mod8_ne_5 zr (by omega))
          (not_cone6_of_mod16_ne_13 zr (by omega))
          (by rintro ⟨_, h32, _, _⟩; omega)]
    have hc3 : core3 (zr + 1) = 2 := by
      rw [show zr + 1 = 2 * 9 ^ m by dsimp [zr]; omega, core3_mul2 (9 ^ m) (by omega), (pow9_eq_v3Pow_w5 m).2]
    rw [cousinDiamond3Step_of_core3_succ_two_w8 zr (by dsimp [zr]; omega) (by dsimp [zr]; omega) hc3]
    dsimp [zr, yr]; omega
  have hsy : cousinDiamond15Step yr = (9 ^ (m + 1) - 1) / 4 := by
    clear hsz
    have hyr_m3 : yr % 3 = 1 := by
      have hm3 : 9 ^ m % 3 = 0 := by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
      dsimp [yr]; omega
    have hyr_ne2 : yr % 3 ≠ 2 := by rw [hyr_m3]; decide
    have hyr_ne8 : yr % 9 ≠ 8 := ne8_mod9_of_mod3_eq1_w18 yr hyr_m3
    rw [d15_eq_d3_of_not_cones5to16_w18 yr
          (not_cone16_of_mod3_ne_2 yr hyr_ne2)
          (not_cone15_of_mod3_ne_2_w18 yr hyr_ne2)
          (not_cone14_of_mod3_ne_2_w18 yr hyr_ne2)
          (not_cone13_of_mod3_ne_2_w18 yr hyr_ne2)
          (not_cone12_of_mod3_ne_2 yr hyr_ne2)
          (not_cone11_of_mod3_ne_2 yr hyr_ne2)
          (not_cone10_of_mod3_ne_2 yr hyr_ne2)
          (not_cone9_of_mod3_ne_2 yr hyr_ne2)
          (not_cone8_of_mod3_ne_2 yr hyr_ne2)
          (not_cone7_of_mod9_ne_8 yr hyr_ne8)
          (not_cone6_of_mod9_ne_8 yr hyr_ne8)
          (not_cone5_of_mod3_ne_2_w18 yr hyr_ne2)]
    have hc3_2 : core3 (2 * yr + 1) = 1 := by
      rw [show 2 * yr + 1 = 3 * 9 ^ m by dsimp [yr]; omega, core3_mul3 (9 ^ m) (by omega), (pow9_eq_v3Pow_w5 m).2]
    have hc3_1 : core3 (yr + 1) ≠ 2 := by
      rw [core3_not_div3 (yr + 1) (by clear hc3_2; omega)]
      clear hc3_2; dsimp [yr]; omega
    have hnc4 : ¬ isDiamond3Cone4 yr := by
      rintro ⟨hge169, _, hc2⟩
      by_cases hm_eq1 : m = 1
      · clear hc3_2 hc3_1 hc2
        dsimp [yr] at hge169; rw [hm_eq1] at hge169; omega
      · rcases eq_pow2_of_core2_eq_one (3 * yr + 5)
          (by clear hc3_2 hc3_1; dsimp [yr]; omega) hc2 with ⟨M0, hM0⟩
        have h9_eq : 9 ^ (m + 1) + 7 = 2 ^ (M0 + 1) := by
          have h2mul : 2 * (3 * yr + 5) = 9 ^ (m + 1) + 7 := by
            clear hc3_2 hc3_1 hc2 hM0
            rw [Nat.pow_succ 9 m, Nat.mul_comm (9 ^ m) 9]; dsimp [yr]; omega
          rw [← h2mul, hM0, Nat.pow_succ 2 M0, Nat.mul_comm]
        exact pow9_succ_add_seven_ne_pow2 m (M0 + 1)
          (by clear hc3_2 hc3_1 hge169 hc2 hM0 h9_eq; omega) h9_eq
    rw [cousinDiamond3Step_odd_half_w8 yr (by clear hc3_2 hc3_1 hnc4; dsimp [yr]; omega) hnc4 hc3_2 hc3_1]
    clear hc3_2 hc3_1 hnc4; dsimp [yr]; rw [Nat.pow_succ 9 m]; omega
  exact ⟨hsz, hsy⟩

private theorem d15_cone4_step_exact_w18 (x M : Nat)
    (hc4 : isDiamond3Cone4 x) (hM : M ≥ 1) (h3x5 : 3 * x + 5 = 4 * M) :
    cousinDiamond15Step x = M - 1 := by
  have hx_odd : x % 2 = 1 := by have := hc4.2.1; omega
  have hdm32 := (Nat.div_add_mod x 32).symm
  rw [d15_eq_d11_of_mod32_w18 x (by have := hc4.2.1; omega) (by have := hc4.2.1; omega),
      cousinDiamond11Step_eq_d10_of_not_cone12 x (not_cone12_of_mod8_ne_5 x (by have := hc4.2.1; omega)),
      cousinDiamond10Step_eq_d9_of_not_cone11 x (not_cone11_of_mod8_ne_5 x (by have := hc4.2.1; omega)),
      cousinDiamond9Step_eq_d8_of_not_cone10 x (not_cone10_of_mod8_ne_5 x (by have := hc4.2.1; omega)),
      cousinDiamond8Step_eq_d7_of_not_cone9 x (not_cone9_of_mod8_ne_5 x (by have := hc4.2.1; omega)),
      cousinDiamond7Step_eq_d6_of_not_cone8 x (not_cone8_of_mod8_ne_5 x (by have := hc4.2.1; omega)),
      cousinDiamond6Step_eq_d5_of_not_cone7 x (not_cone7_of_mod8_ne_5 x (by have := hc4.2.1; omega)),
      cousinDiamond5Step_eq_d4_of_not_cone6 x (by rintro ⟨_, h256, _, _⟩; have := hc4.2.1; omega)]
  unfold cousinDiamond4Step
  by_cases hc5 : isDiamond4Cone5 x
  · simp only [hc5, ite_true]; omega
  · simp only [hc5, ite_false]; rw [cousinDiamond3Step_of_cone4_w8 x hx_odd hc4]; omega

private theorem cousin_diamond15_a0_3_drain (b0 : Nat) (hb0 : b0 ≥ 3) :
    cousinDiamond15Step (8 * 3 ^ b0 - 7) = 12 * 3 ^ b0 - 10 ∧
    cousinDiamond15Step (12 * 3 ^ b0 - 10) = 4 * 3 ^ b0 - 4 ∧
    cousinDiamond15Step (4 * 3 ^ b0 - 4) = 4 * 3 ^ (b0 - 1) - 2 ∧
    cousinDiamond15Iter ((b0 - 1) / 2 + 7) (8 * 3 ^ b0 - 7) = 1 := by
  rcases cousin_diamond11_a0_3_drain b0 hb0 with ⟨hd11_1, hd11_2, hd11_3, _⟩
  have hp3_ge27 : 3 ^ b0 ≥ 27 := by simpa using nat_pow_mono_exp_pos 3 3 b0 (by decide) hb0
  have hp3_b1_ge9 : 3 ^ (b0 - 1) ≥ 9 := by simpa using nat_pow_mono_exp_pos 3 2 (b0 - 1) (by decide) (by omega)
  have hs1 : cousinDiamond15Step (8 * 3 ^ b0 - 7) = 12 * 3 ^ b0 - 10 := by
    have ho := pow3_odd_nat_sec8 b0
    have hdm32 := (Nat.div_add_mod (8 * 3 ^ b0 - 7) 32).symm
    have hm8 : (8 * 3 ^ b0 - 7) % 8 = 1 := by omega
    rw [d15_eq_d11_of_mod32_w18 _ (by omega) (by omega)]
    exact hd11_1
  have hs2 : cousinDiamond15Step (12 * 3 ^ b0 - 10) = 4 * 3 ^ b0 - 4 := by
    have hdm32 := (Nat.div_add_mod (12 * 3 ^ b0 - 10) 32).symm
    have hev : (12 * 3 ^ b0 - 10) % 2 = 0 := by omega
    rw [d15_eq_d11_of_mod32_w18 _ (by omega) (by omega)]
    exact hd11_2
  have hs3 : cousinDiamond15Step (4 * 3 ^ b0 - 4) = 4 * 3 ^ (b0 - 1) - 2 := by
    have hdm32 := (Nat.div_add_mod (4 * 3 ^ b0 - 4) 32).symm
    have hev : (4 * 3 ^ b0 - 4) % 2 = 0 := by omega
    rw [d15_eq_d11_of_mod32_w18 _ (by omega) (by omega)]
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
    have hs4 : cousinDiamond15Step (4 * 9 ^ m - 2) = zr := by
      rw [d15_eq_d3_of_even_w18 _ (by omega)]
      have h9m9 : 9 ^ m % 9 = 0 := by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
      rw [cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) (by omega)]
      dsimp [zr]; omega
    rcases d15_zr_yr_steps_w18 m hm1 with ⟨hsz, hsy⟩
    change cousinDiamond15Iter (m + 7) (8 * 3 ^ b0 - 7) = 1
    rw [show m + 7 = 4 + 1 + 1 + m + 1 by omega,
        cousinDiamond15Iter_add (4 + 1 + 1 + m) 1,
        cousinDiamond15Iter_add (4 + 1 + 1) m,
        cousinDiamond15Iter_add (4 + 1) 1,
        cousinDiamond15Iter_add 4 1]
    have hi4 : cousinDiamond15Iter 4 (8 * 3 ^ b0 - 7) = zr := by
      simp only [cousinDiamond15Iter, hs1, hs2, hs3, h4_eq, hs4]
    rw [hi4, show cousinDiamond15Iter 1 zr = yr from hsz,
        show cousinDiamond15Iter 1 yr = (9 ^ (m + 1) - 1) / 4 from hsy,
        cousin_diamond15_even9_spine_drain m]
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
    have hs4 : cousinDiamond15Step (12 * 9 ^ m - 2) = ur := by
      rw [d15_eq_d3_of_even_w18 _ (by omega)]
      have h9m9 : 9 ^ m % 9 = 0 := by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
      rw [cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) (by omega)]
      dsimp [ur]; omega
    have hsu : cousinDiamond15Step ur = wr := by
      rw [d15_eq_d3_of_not_cones5to16_w18 ur
            (not_cone16_six_mul_pow9_sub1_w18 m)
            (cousin_diamond14_outside_cones4to15_descent_and_mod117_nonreentry.2 m)
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
    have hsw : cousinDiamond15Step wr = (9 ^ (m + 1) - 1) / 4 := by
      let q := (9 ^ m - 1) / 8
      have hq_pos : q ≥ 1 := by dsimp [q]; omega
      have hp9_eq : 9 ^ m = 8 * q + 1 := by dsimp [q]; omega
      have hwr_eq : wr = 36 * q + 4 := by dsimp [wr]; rw [Nat.pow_succ 9 m, hp9_eq]; omega
      have hnext_eq : (9 ^ (m + 1) - 1) / 4 = 18 * q + 2 := by rw [Nat.pow_succ 9 m, hp9_eq]; omega
      rw [hwr_eq, hnext_eq, d15_eq_d3_of_even_w18 _ (by omega),
          cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) (by omega)]
      omega
    change cousinDiamond15Iter (m + 7) (8 * 3 ^ b0 - 7) = 1
    rw [show m + 7 = 4 + 1 + 1 + m + 1 by omega,
        cousinDiamond15Iter_add (4 + 1 + 1 + m) 1,
        cousinDiamond15Iter_add (4 + 1 + 1) m,
        cousinDiamond15Iter_add (4 + 1) 1,
        cousinDiamond15Iter_add 4 1]
    have hi4 : cousinDiamond15Iter 4 (8 * 3 ^ b0 - 7) = ur := by
      simp only [cousinDiamond15Iter, hs1, hs2, hs3, hu_eq, hs4]
    rw [hi4, show cousinDiamond15Iter 1 ur = wr from hsu,
        show cousinDiamond15Iter 1 wr = (9 ^ (m + 1) - 1) / 4 from hsw,
        cousin_diamond15_even9_spine_drain m]
    decide

private theorem cousin_diamond15_a0_2_and_4_drain (b0 : Nat) (hb0 : b0 ≥ 3) :
    cousinDiamond15Iter (b0 + 3) (4 * 3 ^ b0 - 7) = 1 ∧
    cousinDiamond15Iter ((b0 - 1) / 2 + 8) (16 * 3 ^ b0 - 7) = 1 := by
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
  · have hs1 : cousinDiamond15Step (4 * 3 ^ b0 - 7) = 6 * 3 ^ b0 - 10 := by
      have hdm := (Nat.div_add_mod (3 ^ b0) 8).symm
      rw [d15_eq_d11_of_mod32_w18 _ (by rcases h3b0_m8 with h1 | h3 <;> omega) (by rcases h3b0_m8 with h1 | h3 <;> omega),
          cousinDiamond11Step_eq_d10_of_not_cone12 _ (not_cone12_of_mod32_ne_13 _ (by rcases h3b0_m8 with h1 | h3 <;> omega)),
          cousinDiamond10Step_eq_d9_of_not_cone11 _ (not_cone11_of_mod32_ne_13 _ (by rcases h3b0_m8 with h1 | h3 <;> omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_mod32_ne_13 _ (by rcases h3b0_m8 with h1 | h3 <;> omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_mod32_ne_13 _ (by rcases h3b0_m8 with h1 | h3 <;> omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_mod32_ne_21 _ (by rcases h3b0_m8 with h1 | h3 <;> omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (hnc7_c 4 (by decide)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (hnc6_c 4 (by decide))]
      exact cousin_diamond4_exit_step_general_odd 4 b0 (Or.inl rfl) hb0
    have hs2 : cousinDiamond15Step (6 * 3 ^ b0 - 10) = 2 * 3 ^ b0 - 4 := by
      rw [d15_eq_d3_of_even_w18 _ (by omega)]
      have h18 : 6 * 3 ^ b0 = 18 * 3 ^ (b0 - 1) := by rw [h3b0_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]; omega
    have hs3 : cousinDiamond15Step (2 * 3 ^ b0 - 4) = 2 * 3 ^ (b0 - 1) - 2 := by
      rw [d15_eq_d3_of_even_w18 _ (by omega)]
      have h18 : 2 * 3 ^ b0 = 18 * 3 ^ (b0 - 2) := by rw [h3b0_sp, h3b1_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]; omega
    have hs4 : cousinDiamond15Step (2 * 3 ^ (b0 - 1) - 2) = 3 ^ (b0 - 1) - 1 := by
      rw [d15_eq_d3_of_even_w18 _ (by omega)]
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
        cousinDiamond15Iter_add (4 + (b0 - 2)) 1,
        cousinDiamond15Iter_add 4 (b0 - 2)]
    have hi4 : cousinDiamond15Iter 4 (4 * 3 ^ b0 - 7) = 3 ^ ((b0 - 2) + 1) - 1 := by
      simp only [cousinDiamond15Iter, hs1, hs2, hs3, hs4]; rw [show b0 - 1 = (b0 - 2) + 1 by omega]
    rw [hi4, cousin_diamond15_pow3_sub1_drain (b0 - 2)]; decide
  · rcases cousin_diamond15_a0_3_drain b0 hb0 with ⟨ha3_s1, ha3_s2, ha3_s3, ha3⟩
    have ho := pow3_odd_nat_sec8 b0
    have hs1 : cousinDiamond15Step (16 * 3 ^ b0 - 7) = 24 * 3 ^ b0 - 10 := by
      have hdm32 := (Nat.div_add_mod (3 ^ b0) 2).symm
      rw [d15_eq_d11_of_mod32_w18 _ (by omega) (by omega),
          cousinDiamond11Step_eq_d10_of_not_cone12 _ (not_cone12_of_mod32_ne_13 _ (by omega)),
          cousinDiamond10Step_eq_d9_of_not_cone11 _ (not_cone11_of_mod32_ne_13 _ (by omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_mod32_ne_13 _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_mod32_ne_13 _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_mod32_ne_21 _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (hnc7_c 16 (by decide)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (hnc6_c 16 (by decide))]
      exact cousin_diamond4_exit_step_general_odd 16 b0 (Or.inr (Or.inr rfl)) hb0
    have hs2 : cousinDiamond15Step (24 * 3 ^ b0 - 10) = 8 * 3 ^ b0 - 4 := by
      rw [d15_eq_d3_of_even_w18 _ (by omega)]
      have h18 : 24 * 3 ^ b0 = 18 * (4 * 3 ^ (b0 - 1)) := by rw [h3b0_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]; omega
    have hs3 : cousinDiamond15Step (8 * 3 ^ b0 - 4) = 8 * 3 ^ (b0 - 1) - 2 := by
      rw [d15_eq_d3_of_even_w18 _ (by omega)]
      have h18 : 8 * 3 ^ b0 = 18 * (4 * 3 ^ (b0 - 2)) := by rw [h3b0_sp, h3b1_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]; omega
    have hs4 : cousinDiamond15Step (8 * 3 ^ (b0 - 1) - 2) = 4 * 3 ^ (b0 - 1) - 2 := by
      rw [d15_eq_d3_of_even_w18 _ (by omega)]
      have h18 : 8 * 3 ^ (b0 - 1) = 18 * (4 * 3 ^ (b0 - 3)) := by
        calc 8 * 3 ^ (b0 - 1) = 8 * 3 ^ (2 + (b0 - 3)) := by congr 2; omega
          _ = 8 * (3 ^ 2 * 3 ^ (b0 - 3)) := by rw [Nat.pow_add]
          _ = 18 * (4 * 3 ^ (b0 - 3)) := by omega
      have hp3_b3 := pow3_pos_nat (b0 - 3)
      rw [cousinDiamond3Step_even_mod8_eq6_w8 _ (by omega) (by omega) (by omega) ⟨by omega, by omega⟩]; omega
    rw [show (b0 - 1) / 2 + 7 = 3 + ((b0 - 1) / 2 + 4) by omega,
        cousinDiamond15Iter_add 3 ((b0 - 1) / 2 + 4)] at ha3
    have hi3 : cousinDiamond15Iter 3 (8 * 3 ^ b0 - 7) = 4 * 3 ^ (b0 - 1) - 2 := by
      simp only [cousinDiamond15Iter, ha3_s1, ha3_s2, ha3_s3]
    rw [hi3] at ha3
    rw [show (b0 - 1) / 2 + 8 = 4 + ((b0 - 1) / 2 + 4) by omega,
        cousinDiamond15Iter_add 4 ((b0 - 1) / 2 + 4)]
    have hi4 : cousinDiamond15Iter 4 (16 * 3 ^ b0 - 7) = 4 * 3 ^ (b0 - 1) - 2 := by
      simp only [cousinDiamond15Iter, hs1, hs2, hs3, hs4]
    rw [hi4]; exact ha3

private theorem cousin_diamond15_cone4_return_aux (x : Nat) (hc4 : isDiamond3Cone4 x) :
    ∃ k : Nat, k ≤ cousinDiamond2Phi x ∧ cousinDiamond15Iter k x = 1 := by
  rcases cousin_diamond3_cone4_reaches_one_exact x hc4 with ⟨r, hr_ge3, hE, _, hphi_ge⟩
  refine ⟨3 * r + 4, hphi_ge, ?_⟩
  have hs1 : cousinDiamond15Step x = 2 ^ (2 * r + 1) - 1 :=
    d15_cone4_step_exact_w18 x (2 ^ (2 * r + 1)) hc4 (pow2_pos_nat _)
      (by rw [hE, show 2 * r + 3 = 2 + (2 * r + 1) by omega, Nat.pow_add])
  let zr := 2 * 9 ^ r - 1
  let yr := (3 * 9 ^ r - 1) / 2
  have hglide : cousinDiamond15Iter (2 * r) (2 ^ (2 * r + 1) - 1) = zr := by
    have hf := cousin_diamond15_mersenne_scaled (2 * r) (2 * r + 1) 1 (by omega) (by decide)
    simp only [Nat.mul_one, show 2 * r + 1 - 2 * r = 1 by omega, Nat.pow_one] at hf
    rw [hf, ← pow9_eq_pow3_double r, Nat.mul_comm]
  rcases d15_zr_yr_steps_w18 r (by omega) with ⟨hsz, hsy⟩
  rw [show 3 * r + 4 = 1 + 2 * r + 1 + 1 + r + 1 by omega,
      cousinDiamond15Iter_add (1 + 2 * r + 1 + 1 + r) 1,
      cousinDiamond15Iter_add (1 + 2 * r + 1 + 1) r,
      cousinDiamond15Iter_add (1 + 2 * r + 1) 1,
      cousinDiamond15Iter_add (1 + 2 * r) 1,
      cousinDiamond15Iter_add 1 (2 * r)]
  rw [show cousinDiamond15Iter 1 x = 2 ^ (2 * r + 1) - 1 from hs1, hglide,
      show cousinDiamond15Iter 1 zr = yr from hsz,
      show cousinDiamond15Iter 1 yr = (9 ^ (r + 1) - 1) / 4 from hsy,
      cousin_diamond15_even9_spine_drain r]
  decide

private theorem cousin_diamond15_cone5_return_aux (x : Nat) (hc5 : isDiamond4Cone5 x) :
    ∃ (a b k : Nat),
      a ≥ 5 ∧ b ≥ 1 ∧ x + 7 = 2 ^ a * 3 ^ b ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond15Iter k x = 1 := by
  rcases cousin_diamond14_cones4to15_exact_return.2.1 x hc5 with ⟨a, b, _, ha5, hb1, hmul, _, _, _⟩
  have hx_eq : x = 2 ^ a * 3 ^ b - 7 := by omega
  let q_c := (a - 2) / 3
  let a0 := a - 3 * q_c
  let b0 := b + 2 * q_c
  have hb0_ge3 : b0 ≥ 3 := by dsimp [b0, q_c]; omega
  have ha0_234 : a0 = 2 ∨ a0 = 3 ∨ a0 = 4 := by dsimp [a0, q_c]; omega
  have hclimb := cousin_diamond15_cone5_two_step_climb q_c a b (by dsimp [q_c]; omega) hb1
  rw [← hx_eq] at hclimb
  change cousinDiamond15Iter (2 * q_c) x = 2 ^ a0 * 3 ^ b0 - 7 at hclimb
  have hbound_x : ∀ ex : Nat, ex ≤ b0 + 8 -> 2 * q_c + ex ≤ x := by
    intro ex hex
    have hprod := Nat.mul_le_mul (pow2_ge_six_mul_ge5 a ha5) (pow3_ge_add_two_ge1 b hb1)
    rw [hmul.symm] at hprod
    have hab : 6 * b ≤ 6 * a * b := by
      rw [Nat.mul_comm (6 * a) b, ← Nat.mul_assoc, Nat.mul_comm b 6]
      simpa using Nat.mul_le_mul_left (6 * b) (by omega : 1 ≤ a)
    rw [show (6 * a) * (b + 2) = 6 * a * b + 12 * a by rw [Nat.mul_add]; omega] at hprod
    dsimp [q_c, b0] at hex ⊢; omega
  have hd_3 := (cousin_diamond15_a0_3_drain b0 hb0_ge3).2.2.2
  rcases cousin_diamond15_a0_2_and_4_drain b0 hb0_ge3 with ⟨hd_2, hd_4⟩
  rcases ha0_234 with ha2 | ha3 | ha4
  · have hkx := hbound_x (b0 + 3) (by omega)
    refine ⟨a, b, 2 * q_c + (b0 + 3), ha5, hb1, hmul, hkx,
      Nat.le_trans (by omega : 2 * q_c + (b0 + 3) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond15Iter_add (2 * q_c) (b0 + 3) x, hclimb, ha2]; exact hd_2
  · have hkx := hbound_x ((b0 - 1) / 2 + 7) (by omega)
    refine ⟨a, b, 2 * q_c + ((b0 - 1) / 2 + 7), ha5, hb1, hmul, hkx,
      Nat.le_trans (by omega : 2 * q_c + ((b0 - 1) / 2 + 7) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond15Iter_add (2 * q_c) ((b0 - 1) / 2 + 7) x, hclimb, ha3]; exact hd_3
  · have hkx := hbound_x ((b0 - 1) / 2 + 8) (by omega)
    refine ⟨a, b, 2 * q_c + ((b0 - 1) / 2 + 8), ha5, hb1, hmul, hkx,
      Nat.le_trans (by omega : 2 * q_c + ((b0 - 1) / 2 + 8) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond15Iter_add (2 * q_c) ((b0 - 1) / 2 + 8) x, hclimb, ha4]; exact hd_4

private theorem sub_eq_div_of_add_pow23_w18 (x C1 C2 a b s D : Nat)
    (hD_pos : D > 0) (hs : s ≤ a) (h2s : 2 ^ s = D) (hC : 3 * C1 = D * C2 + 1)
    (hmul : x + C1 = 2 ^ a * 3 ^ b) :
    2 ^ (a - s) * 3 ^ (b + 1) - C2 = (3 * x + 1) / D := by
  have hp2 : 2 ^ a = D * 2 ^ (a - s) := by
    conv => lhs; rw [show a = s + (a - s) by omega, Nat.pow_add, h2s]
  have h3x : 3 * x + 3 * C1 = D * (2 ^ (a - s) * 3 ^ (b + 1)) := by
    rw [← Nat.mul_add 3 x C1, hmul, hp2, Nat.pow_succ 3 b]
    generalize 2 ^ (a - s) = P2, 3 ^ b = P3; ac_rfl
  generalize 2 ^ (a - s) * 3 ^ (b + 1) = Q at h3x ⊢
  have hsum : (3 * x + 1) + D * C2 = D * Q := by rw [hC] at h3x; omega
  have hC2_le : C2 ≤ Q := by
    by_cases hle : C2 ≤ Q
    · exact hle
    · exfalso
      have hm := Nat.mul_le_mul_left D (show Q + 1 ≤ C2 by omega)
      rw [Nat.mul_add, Nat.mul_one] at hm; omega
  have hsub_mul : D * (Q - C2) + D * C2 = D * Q := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hC2_le]
  have h3x1 : 3 * x + 1 = (Q - C2) * D := by
    rw [Nat.mul_comm (Q - C2) D]
    exact Nat.add_right_cancel (hsum.trans hsub_mul.symm)
  rw [h3x1, Nat.mul_div_cancel _ hD_pos]

private theorem lift_cone_step_to_d15 (x y D : Nat) (hD8 : D ≥ 8) (hx_ge : x ≥ 2000)
    (hnc16 : ¬ isDiamond15Cone16 x)
    (hd14 : cousinDiamond14Step x = y)
    (hy_div : y = (3 * x + 1) / D)
    (hret_y : ∃ ky : Nat, ky ≤ y ∧ cousinDiamond15Iter ky y = 1) :
    ∃ k : Nat, k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond15Step x = y ∧ cousinDiamond15Iter k x = 1 := by
  rcases hret_y with ⟨ky, hky_y, hky_1⟩
  have hstep : cousinDiamond15Step x = y := (d15_eq_d14_of_not_cone16 x hnc16).trans hd14
  have hy_lt : y + 1 ≤ x := by
    have hdiv : y * D ≤ 3 * x + 1 := by rw [hy_div]; exact Nat.div_mul_le_self (3 * x + 1) D
    have h8 : y * 8 ≤ y * D := Nat.mul_le_mul_left y hD8
    have hy8 : y * 8 ≤ 3 * x + 1 := Nat.le_trans h8 hdiv
    clear hy_div hdiv h8 hD8 hnc16 hd14 hky_1 hstep; omega
  refine ⟨1 + ky, by omega, Nat.le_trans (by omega : 1 + ky ≤ x + 1) (cousinDiamond2Phi_ge_succ x), hstep, ?_⟩
  rw [cousinDiamond15Iter_add 1 ky x, show cousinDiamond15Iter 1 x = y from hstep]; exact hky_1

private theorem not_cone16_mod_sub_w18 (x M R sub c16r : Nat)
    (hm : x % M = R) (hdvd : sub ∣ M)
    (hc16 : ∀ z : Nat, isDiamond15Cone16 z -> z % sub = c16r)
    (hne : R % sub ≠ c16r) : ¬ isDiamond15Cone16 x := by
  intro h16
  have h := congrArg (· % sub) hm
  rw [Nat.mod_mod_of_dvd x hdvd, hc16 x h16] at h
  exact hne h.symm

private theorem lift_cone_ret_to_d15_w18
    (P_cur P_prev : Nat -> Prop) (A_min B_min C1 C2 s D : Nat)
    (hD8 : D ≥ 8) (hAmin : s ≤ A_min) (h2s : 2 ^ s = D) (hC : 3 * C1 = D * C2 + 1)
    (hcur_ge : ∀ x : Nat, P_cur x -> x ≥ 2000 ∧ ¬ isDiamond15Cone16 x)
    (hd14_cur : ∀ x : Nat, P_cur x ->
      ∃ (a b k14 : Nat), a ≥ A_min ∧ b ≥ B_min ∧ x + C1 = 2 ^ a * 3 ^ b ∧
        cousinDiamond14Step x = 2 ^ (a - s) * 3 ^ (b + 1) - C2 ∧
        P_prev (cousinDiamond14Step x) ∧
        k14 ≤ x ∧ k14 ≤ cousinDiamond2Phi x ∧ cousinDiamond14Iter k14 x = 1)
    (hprev_ret : ∀ y : Nat, P_prev y -> ∃ ky : Nat, ky ≤ y ∧ cousinDiamond15Iter ky y = 1) :
    ∀ x : Nat, P_cur x ->
      ∃ (a b k : Nat), a ≥ A_min ∧ b ≥ B_min ∧ x + C1 = 2 ^ a * 3 ^ b ∧
        cousinDiamond15Step x = 2 ^ (a - s) * 3 ^ (b + 1) - C2 ∧
        P_prev (cousinDiamond15Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond15Iter k x = 1 := by
  intro x hcur
  rcases hcur_ge x hcur with ⟨hx_ge, hnc16⟩
  rcases hd14_cur x hcur with ⟨a, b, _, ha, hb, hmul, hd14, hprev_y, _, _, _⟩
  rw [hd14] at hprev_y
  have hy_div := sub_eq_div_of_add_pow23_w18 x C1 C2 a b s D
    (by omega) (Nat.le_trans hAmin ha) h2s hC hmul
  rcases lift_cone_step_to_d15 x _ D hD8 hx_ge hnc16 hd14 hy_div
    (hprev_ret _ hprev_y) with ⟨k, hkx, hkphi, hst, hk1⟩
  exact ⟨a, b, k, ha, hb, hmul, hst, by rw [hst]; exact hprev_y, hkx, hkphi, hk1⟩

private theorem hc6_ret_w18 : ∀ x : Nat, isDiamond5Cone6 x ->
    ∃ (e f k : Nat), e ≥ 8 ∧ f ≥ 2 ∧ x + 19 = 2 ^ e * 3 ^ f ∧
      cousinDiamond15Step x = 2 ^ (e - 3) * 3 ^ (f + 1) - 7 ∧
      isDiamond4Cone5 (cousinDiamond15Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond15Iter k x = 1 :=
  lift_cone_ret_to_d15_w18 isDiamond5Cone6 isDiamond4Cone5 8 2 19 7 3 8
    (by decide) (by decide) (by decide) (by decide)
    (fun x hc => ⟨Nat.le_trans (by decide) hc.1,
      not_cone16_mod_sub_w18 x 256 237 64 13 hc.2.1 (by decide) mod64_of_cone16 (by decide)⟩)
    cousin_diamond14_cones4to15_exact_return.2.2.1
    (fun y hy => let ⟨_, _, ky, _, _, _, hle, _, hk1⟩ := cousin_diamond15_cone5_return_aux y hy; ⟨ky, hle, hk1⟩)

private theorem hc7_ret_w18 : ∀ x : Nat, isDiamond6Cone7 x ->
    ∃ (g h k : Nat), g ≥ 15 ∧ h ≥ 2 ∧ x + 811 = 2 ^ g * 3 ^ h ∧
      cousinDiamond15Step x = 2 ^ (g - 7) * 3 ^ (h + 1) - 19 ∧
      isDiamond5Cone6 (cousinDiamond15Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond15Iter k x = 1 :=
  lift_cone_ret_to_d15_w18 isDiamond6Cone7 isDiamond5Cone6 15 2 811 19 7 128
    (by decide) (by decide) (by decide) (by decide)
    (fun x hc => ⟨Nat.le_trans (by decide) hc.1,
      not_cone16_mod_sub_w18 x 32768 31957 16 13 hc.2.1 (by decide) mod16_of_cone16 (by decide)⟩)
    cousin_diamond14_cones4to15_exact_return.2.2.2.1
    (fun y hy => let ⟨_, _, ky, _, _, _, _, _, hle, _, hk1⟩ := hc6_ret_w18 y hy; ⟨ky, hle, hk1⟩)

private theorem hc8_ret_w18 : ∀ x : Nat, isDiamond7Cone8 x ->
    ∃ (u v k : Nat), u ≥ 22 ∧ v ≥ 1 ∧ x + 34603 = 2 ^ u * 3 ^ v ∧
      cousinDiamond15Step x = 2 ^ (u - 7) * 3 ^ (v + 1) - 811 ∧
      isDiamond6Cone7 (cousinDiamond15Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond15Iter k x = 1 :=
  lift_cone_ret_to_d15_w18 isDiamond7Cone8 isDiamond6Cone7 22 1 34603 811 7 128
    (by decide) (by decide) (by decide) (by decide)
    (fun x hc => ⟨Nat.le_trans (by decide) hc.1,
      not_cone16_mod_sub_w18 x 4194304 4159701 16 13 hc.2.1 (by decide) mod16_of_cone16 (by decide)⟩)
    cousin_diamond14_cones4to15_exact_return.2.2.2.2.1
    (fun y hy => let ⟨_, _, ky, _, _, _, _, _, hle, _, hk1⟩ := hc7_ret_w18 y hy; ⟨ky, hle, hk1⟩)

private theorem hc9_ret_w18 : ∀ x : Nat, isDiamond8Cone9 x ->
    ∃ (w z k : Nat), w ≥ 25 ∧ z ≥ 1 ∧ x + 92275 = 2 ^ w * 3 ^ z ∧
      cousinDiamond15Step x = 2 ^ (w - 3) * 3 ^ (z + 1) - 34603 ∧
      isDiamond7Cone8 (cousinDiamond15Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond15Iter k x = 1 :=
  lift_cone_ret_to_d15_w18 isDiamond8Cone9 isDiamond7Cone8 25 1 92275 34603 3 8
    (by decide) (by decide) (by decide) (by decide)
    (fun x hc => ⟨Nat.le_trans (by decide) hc.1,
      not_cone16_mod_sub_w18 x 33554432 33462157 512 141 hc.2.1 (by decide) mod512_of_cone16 (by decide)⟩)
    cousin_diamond14_cones4to15_exact_return.2.2.2.2.2.1
    (fun y hy => let ⟨_, _, ky, _, _, _, _, _, hle, _, hk1⟩ := hc8_ret_w18 y hy; ⟨ky, hle, hk1⟩)

private theorem hc10_ret_w18 : ∀ x : Nat, isDiamond9Cone10 x ->
    ∃ (p q k : Nat), p ≥ 28 ∧ q ≥ 1 ∧ x + 246067 = 2 ^ p * 3 ^ q ∧
      cousinDiamond15Step x = 2 ^ (p - 3) * 3 ^ (q + 1) - 92275 ∧
      isDiamond8Cone9 (cousinDiamond15Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond15Iter k x = 1 :=
  lift_cone_ret_to_d15_w18 isDiamond9Cone10 isDiamond8Cone9 28 1 246067 92275 3 8
    (by decide) (by decide) (by decide) (by decide)
    (fun x hc => ⟨Nat.le_trans (by decide) hc.1,
      not_cone16_mod_sub_w18 x 268435456 268189389 128 13 hc.2.1 (by decide) mod128_of_cone16 (by decide)⟩)
    cousin_diamond14_cones4to15_exact_return.2.2.2.2.2.2.1
    (fun y hy => let ⟨_, _, ky, _, _, _, _, _, hle, _, hk1⟩ := hc9_ret_w18 y hy; ⟨ky, hle, hk1⟩)

private theorem hc11_ret_w18 : ∀ x : Nat, isDiamond10Cone11 x ->
    ∃ (r s k : Nat), r ≥ 31 ∧ s ≥ 1 ∧ x + 656179 = 2 ^ r * 3 ^ s ∧
      cousinDiamond15Step x = 2 ^ (r - 3) * 3 ^ (s + 1) - 246067 ∧
      isDiamond9Cone10 (cousinDiamond15Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond15Iter k x = 1 :=
  lift_cone_ret_to_d15_w18 isDiamond10Cone11 isDiamond9Cone10 31 1 656179 246067 3 8
    (by decide) (by decide) (by decide) (by decide)
    (fun x hc => ⟨Nat.le_trans (by decide) hc.1,
      not_cone16_mod_sub_w18 x 2147483648 2146827469 128 13 hc.2.1 (by decide) mod128_of_cone16 (by decide)⟩)
    cousin_diamond14_cones4to15_exact_return.2.2.2.2.2.2.2.1
    (fun y hy => let ⟨_, _, ky, _, _, _, _, _, hle, _, hk1⟩ := hc10_ret_w18 y hy; ⟨ky, hle, hk1⟩)

private theorem hc12_ret_w18 : ∀ x : Nat, isDiamond11Cone12 x ->
    ∃ (m n k : Nat), m ≥ 34 ∧ n ≥ 1 ∧ x + 1749811 = 2 ^ m * 3 ^ n ∧
      cousinDiamond15Step x = 2 ^ (m - 3) * 3 ^ (n + 1) - 656179 ∧
      isDiamond10Cone11 (cousinDiamond15Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond15Iter k x = 1 :=
  lift_cone_ret_to_d15_w18 isDiamond11Cone12 isDiamond10Cone11 34 1 1749811 656179 3 8
    (by decide) (by decide) (by decide) (by decide)
    (fun x hc => ⟨Nat.le_trans (by decide) hc.1,
      not_cone16_mod_sub_w18 x 17179869184 17178119373 128 13 hc.2.1 (by decide) mod128_of_cone16 (by decide)⟩)
    cousin_diamond14_cones4to15_exact_return.2.2.2.2.2.2.2.2.1
    (fun y hy => let ⟨_, _, ky, _, _, _, _, _, hle, _, hk1⟩ := hc11_ret_w18 y hy; ⟨ky, hle, hk1⟩)

private theorem hc13_ret_w18 : ∀ x : Nat, isDiamond12Cone13 x ->
    ∃ (a b k : Nat), a ≥ 39 ∧ b ≥ 1 ∧ x + 18664651 = 2 ^ a * 3 ^ b ∧
      cousinDiamond15Step x = 2 ^ (a - 5) * 3 ^ (b + 1) - 1749811 ∧
      isDiamond11Cone12 (cousinDiamond15Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond15Iter k x = 1 :=
  lift_cone_ret_to_d15_w18 isDiamond12Cone13 isDiamond11Cone12 39 1 18664651 1749811 5 32
    (by decide) (by decide) (by decide) (by decide)
    (fun x hc => ⟨Nat.le_trans (by decide) hc.1,
      not_cone16_mod_sub_w18 x 549755813888 549737149237 16 13 hc.2.1 (by decide) mod16_of_cone16 (by decide)⟩)
    cousin_diamond14_cones4to15_exact_return.2.2.2.2.2.2.2.2.2.1
    (fun y hy => let ⟨_, _, ky, _, _, _, _, _, hle, _, hk1⟩ := hc12_ret_w18 y hy; ⟨ky, hle, hk1⟩)

private theorem hc14_ret_w18 : ∀ x : Nat, isDiamond13Cone14 x ->
    ∃ (k_e m_e k : Nat), k_e ≥ 46 ∧ m_e ≥ 1 ∧ x + 796358443 = 2 ^ k_e * 3 ^ m_e ∧
      cousinDiamond15Step x = 2 ^ (k_e - 7) * 3 ^ (m_e + 1) - 18664651 ∧
      isDiamond12Cone13 (cousinDiamond15Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond15Iter k x = 1 :=
  lift_cone_ret_to_d15_w18 isDiamond13Cone14 isDiamond12Cone13 46 1 796358443 18664651 7 128
    (by decide) (by decide) (by decide) (by decide)
    (fun x hc => ⟨Nat.le_trans (by decide) hc.1,
      not_cone16_mod_sub_w18 x 70368744177664 70367947819221 16 13 hc.2.1 (by decide) mod16_of_cone16 (by decide)⟩)
    cousin_diamond14_cones4to15_exact_return.2.2.2.2.2.2.2.2.2.2.1
    (fun y hy => let ⟨_, _, ky, _, _, _, _, _, hle, _, hk1⟩ := hc13_ret_w18 y hy; ⟨ky, hle, hk1⟩)

private theorem hc15_ret_w18 : ∀ x : Nat, isDiamond14Cone15 x ->
    ∃ (a_e b_e k : Nat), a_e ≥ 51 ∧ b_e ≥ 1 ∧ x + 8494490059 = 2 ^ a_e * 3 ^ b_e ∧
      cousinDiamond15Step x = 2 ^ (a_e - 5) * 3 ^ (b_e + 1) - 796358443 ∧
      isDiamond13Cone14 (cousinDiamond15Step x) ∧ k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond15Iter k x = 1 :=
  lift_cone_ret_to_d15_w18 isDiamond14Cone15 isDiamond13Cone14 51 1 8494490059 796358443 5 32
    (by decide) (by decide) (by decide) (by decide)
    (fun x hc => ⟨Nat.le_trans (by decide) hc.1,
      not_cone16_mod_sub_w18 x 2251799813685248 2251791319195189 16 13 hc.2.1 (by decide) mod16_of_cone16 (by decide)⟩)
    cousin_diamond14_cones4to15_exact_return.2.2.2.2.2.2.2.2.2.2.2
    (fun y hy => let ⟨_, _, ky, _, _, _, _, _, hle, _, hk1⟩ := hc14_ret_w18 y hy; ⟨ky, hle, hk1⟩)

private theorem hc16_ret_w18 :
    ∀ x : Nat, isDiamond15Cone16 x ->
      ∃ (c_e d_e k : Nat),
        c_e ≥ 54 ∧ d_e ≥ 1 ∧ x + 22651973491 = 2 ^ c_e * 3 ^ d_e ∧
        cousinDiamond15Step x = 2 ^ (c_e - 3) * 3 ^ (d_e + 1) - 8494490059 ∧
        isDiamond14Cone15 (cousinDiamond15Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond15Iter k x = 1 := by
  intro x hc16
  have hraw_step : cousinDiamond15Step x = (3 * x + 1) / 8 := by
    unfold cousinDiamond15Step; simp only [hc16, ite_true]
  rcases hc16 with ⟨hx_ge, hx54, hx3, hg1⟩
  have hdvd54 : 18014398509481984 ∣ (x + 22651973491) :=
    Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, hx54])
  clear hx54
  rcases (⟨22651973491 + x, rfl⟩ : ∃ N : Nat, N = 22651973491 + x) with ⟨N, hN_def⟩
  rw [← hN_def] at hg1
  have hN_pos : N > 0 := by clear hraw_step hdvd54 hx3 hg1; omega
  rcases decomp_2_3_exact N hN_pos with ⟨_, _, _, _, _, hmul⟩
  rw [hg1, Nat.mul_one] at hmul
  rcases eq_pow2_of_v2Pow_aux N N hN_pos (Nat.le_refl _) with ⟨c_e, hc_e⟩
  rcases eq_pow3_of_v3Pow_aux N N hN_pos (Nat.le_refl _) with ⟨d_e, hd_e⟩
  rw [hc_e, hd_e] at hmul
  have hmul_comm : x + 22651973491 = 2 ^ c_e * 3 ^ d_e := by
    rw [Nat.add_comm x 22651973491, ← hN_def, ← hmul]
  clear hg1 hc_e hd_e hN_def hmul hN_pos
  have hc54 : c_e ≥ 54 := by
    by_cases hlt : c_e < 54
    · exfalso
      have h54_sp : 18014398509481984 = 2 ^ (c_e + 1) * 2 ^ (53 - c_e) := by
        rw [← Nat.pow_add 2 (c_e + 1) (53 - c_e),
            show c_e + 1 + (53 - c_e) = 54 by clear hraw_step hx_ge hx3 hdvd54 hmul_comm; omega]
      rcases hdvd54 with ⟨c, hc⟩
      rw [hmul_comm, h54_sp, Nat.mul_assoc (2 ^ (c_e + 1)), Nat.pow_succ 2 c_e, Nat.mul_assoc (2 ^ c_e) 2] at hc
      have h3m_ev : 3 ^ d_e = 2 * (2 ^ (53 - c_e) * c) :=
        nat_mul_left_cancel_pos (2 ^ c_e) _ _ (pow2_pos_nat c_e) hc
      have ho := pow3_odd_nat_sec8 d_e
      rw [h3m_ev, Nat.mul_mod_right] at ho; cases ho
    · clear hraw_step hx_ge hx3 hdvd54 hmul_comm; omega
  clear hdvd54
  have hd1 : d_e ≥ 1 := by
    cases d_e with
    | zero =>
      rw [Nat.pow_zero, Nat.mul_one] at hmul_comm
      exact False.elim (pow2_mod3_nonzero_w5 c_e (by rw [← hmul_comm, Nat.add_mod, hx3]))
    | succ _ => clear hraw_step hx_ge hx3 hmul_comm hc54; omega
  clear hx3
  let y := 2 ^ (c_e - 3) * 3 ^ (d_e + 1) - 8494490059
  have hstep_x : cousinDiamond15Step x = y :=
    hraw_step.trans (sub_eq_div_of_add_pow23_w18 x 22651973491 8494490059 c_e d_e 3 8
      (by decide) (by clear hraw_step hx_ge hmul_comm hd1; omega) (by decide) (by decide) hmul_comm).symm
  have hc15_y : isDiamond14Cone15 y :=
    isDiamond14Cone15_of_pow2_pow3_w18 (c_e - 3) (d_e + 1)
      (by clear hraw_step hx_ge hmul_comm hstep_x; omega)
      (by clear hraw_step hx_ge hmul_comm hstep_x; omega)
  rcases hc15_ret_w18 y hc15_y with ⟨_, _, ky, _, _, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hstep_eq : y = (3 * x + 1) / 8 := hstep_x.symm.trans hraw_step
    have hdiv : y * 8 ≤ 3 * x + 1 := by rw [hstep_eq]; exact Nat.div_mul_le_self (3 * x + 1) 8
    clear hraw_step hmul_comm hstep_x hc15_y hky_1 hstep_eq; omega
  refine ⟨c_e, d_e, 1 + ky, hc54, hd1, hmul_comm, hstep_x, by rw [hstep_x]; exact hc15_y,
          by clear hraw_step hmul_comm hstep_x hc15_y hky_1; omega,
          Nat.le_trans (by clear hraw_step hmul_comm hstep_x hc15_y hky_1; omega : 1 + ky ≤ x + 1)
            (cousinDiamond2Phi_ge_succ x), ?_⟩
  rw [cousinDiamond15Iter_add 1 ky x, show cousinDiamond15Iter 1 x = y from hstep_x]; exact hky_1

/--
  Theorem W18.3f (`cousin_diamond15_cones4to16_exact_return`, `zero custom axioms`):
  Exact 13-Tier `ω^13` Multi-Block Return Across Cones 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, AND 16
  of `T_diamond15` (`Branch P5.17`, `W18_H1`).
-/
theorem cousin_diamond15_cones4to16_exact_return :
    (∀ x : Nat, isDiamond3Cone4 x ->
      ∃ k : Nat, k ≤ cousinDiamond2Phi x ∧ cousinDiamond15Iter k x = 1) ∧
    (∀ x : Nat, isDiamond4Cone5 x ->
      ∃ (a b k : Nat),
        a ≥ 5 ∧ b ≥ 1 ∧ x + 7 = 2 ^ a * 3 ^ b ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond15Iter k x = 1) ∧
    (∀ x : Nat, isDiamond5Cone6 x ->
      ∃ (e f k : Nat),
        e ≥ 8 ∧ f ≥ 2 ∧ x + 19 = 2 ^ e * 3 ^ f ∧
        cousinDiamond15Step x = 2 ^ (e - 3) * 3 ^ (f + 1) - 7 ∧
        isDiamond4Cone5 (cousinDiamond15Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond15Iter k x = 1) ∧
    (∀ x : Nat, isDiamond6Cone7 x ->
      ∃ (g h k : Nat),
        g ≥ 15 ∧ h ≥ 2 ∧ x + 811 = 2 ^ g * 3 ^ h ∧
        cousinDiamond15Step x = 2 ^ (g - 7) * 3 ^ (h + 1) - 19 ∧
        isDiamond5Cone6 (cousinDiamond15Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond15Iter k x = 1) ∧
    (∀ x : Nat, isDiamond7Cone8 x ->
      ∃ (u v k : Nat),
        u ≥ 22 ∧ v ≥ 1 ∧ x + 34603 = 2 ^ u * 3 ^ v ∧
        cousinDiamond15Step x = 2 ^ (u - 7) * 3 ^ (v + 1) - 811 ∧
        isDiamond6Cone7 (cousinDiamond15Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond15Iter k x = 1) ∧
    (∀ x : Nat, isDiamond8Cone9 x ->
      ∃ (w z k : Nat),
        w ≥ 25 ∧ z ≥ 1 ∧ x + 92275 = 2 ^ w * 3 ^ z ∧
        cousinDiamond15Step x = 2 ^ (w - 3) * 3 ^ (z + 1) - 34603 ∧
        isDiamond7Cone8 (cousinDiamond15Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond15Iter k x = 1) ∧
    (∀ x : Nat, isDiamond9Cone10 x ->
      ∃ (p q k : Nat),
        p ≥ 28 ∧ q ≥ 1 ∧ x + 246067 = 2 ^ p * 3 ^ q ∧
        cousinDiamond15Step x = 2 ^ (p - 3) * 3 ^ (q + 1) - 92275 ∧
        isDiamond8Cone9 (cousinDiamond15Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond15Iter k x = 1) ∧
    (∀ x : Nat, isDiamond10Cone11 x ->
      ∃ (r s k : Nat),
        r ≥ 31 ∧ s ≥ 1 ∧ x + 656179 = 2 ^ r * 3 ^ s ∧
        cousinDiamond15Step x = 2 ^ (r - 3) * 3 ^ (s + 1) - 246067 ∧
        isDiamond9Cone10 (cousinDiamond15Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond15Iter k x = 1) ∧
    (∀ x : Nat, isDiamond11Cone12 x ->
      ∃ (m n k : Nat),
        m ≥ 34 ∧ n ≥ 1 ∧ x + 1749811 = 2 ^ m * 3 ^ n ∧
        cousinDiamond15Step x = 2 ^ (m - 3) * 3 ^ (n + 1) - 656179 ∧
        isDiamond10Cone11 (cousinDiamond15Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond15Iter k x = 1) ∧
    (∀ x : Nat, isDiamond12Cone13 x ->
      ∃ (a b k : Nat),
        a ≥ 39 ∧ b ≥ 1 ∧ x + 18664651 = 2 ^ a * 3 ^ b ∧
        cousinDiamond15Step x = 2 ^ (a - 5) * 3 ^ (b + 1) - 1749811 ∧
        isDiamond11Cone12 (cousinDiamond15Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond15Iter k x = 1) ∧
    (∀ x : Nat, isDiamond13Cone14 x ->
      ∃ (k_e m_e k : Nat),
        k_e ≥ 46 ∧ m_e ≥ 1 ∧ x + 796358443 = 2 ^ k_e * 3 ^ m_e ∧
        cousinDiamond15Step x = 2 ^ (k_e - 7) * 3 ^ (m_e + 1) - 18664651 ∧
        isDiamond12Cone13 (cousinDiamond15Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond15Iter k x = 1) ∧
    (∀ x : Nat, isDiamond14Cone15 x ->
      ∃ (a_e b_e k : Nat),
        a_e ≥ 51 ∧ b_e ≥ 1 ∧ x + 8494490059 = 2 ^ a_e * 3 ^ b_e ∧
        cousinDiamond15Step x = 2 ^ (a_e - 5) * 3 ^ (b_e + 1) - 796358443 ∧
        isDiamond13Cone14 (cousinDiamond15Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond15Iter k x = 1) ∧
    (∀ x : Nat, isDiamond15Cone16 x ->
      ∃ (c_e d_e k : Nat),
        c_e ≥ 54 ∧ d_e ≥ 1 ∧ x + 22651973491 = 2 ^ c_e * 3 ^ d_e ∧
        cousinDiamond15Step x = 2 ^ (c_e - 3) * 3 ^ (d_e + 1) - 8494490059 ∧
        isDiamond14Cone15 (cousinDiamond15Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond15Iter k x = 1) :=
  ⟨cousin_diamond15_cone4_return_aux, cousin_diamond15_cone5_return_aux,
   hc6_ret_w18, hc7_ret_w18, hc8_ret_w18, hc9_ret_w18, hc10_ret_w18,
   hc11_ret_w18, hc12_ret_w18, hc13_ret_w18, hc14_ret_w18, hc15_ret_w18, hc16_ret_w18⟩
private theorem cousin_diamond15_reaches_one_step_w18 (B x : Nat)
    (hx : x > 0) (hB : cousinDiamond2Phi x ≤ B + 1)
    (ih : ∀ y : Nat, y > 0 -> cousinDiamond2Phi y ≤ B -> ∃ k : Nat, k ≤ B ∧ cousinDiamond15Iter k y = 1) :
    ∃ k : Nat, k ≤ B + 1 ∧ cousinDiamond15Iter k x = 1 := by
  by_cases hx1 : x = 1
  · subst hx1; exact ⟨0, by omega, rfl⟩
  · by_cases hx2 : x = 2
    · subst hx2
      have hphi2 : cousinDiamond2Phi 2 = 28 := by decide
      rw [hphi2] at hB; exact ⟨1, by omega, by decide⟩
    · by_cases hc4 : isDiamond3Cone4 x
      · rcases cousin_diamond15_cone4_return_aux x hc4 with ⟨k, hle, hk1⟩
        exact ⟨k, Nat.le_trans hle hB, hk1⟩
      · by_cases hc5 : isDiamond4Cone5 x
        · rcases cousin_diamond15_cone5_return_aux x hc5 with ⟨_, _, k, _, _, _, _, hle, hk1⟩
          exact ⟨k, Nat.le_trans hle hB, hk1⟩
        · by_cases hc6 : isDiamond5Cone6 x
          · rcases hc6_ret_w18 x hc6 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
            exact ⟨k, Nat.le_trans hle hB, hk1⟩
          · by_cases hc7 : isDiamond6Cone7 x
            · rcases hc7_ret_w18 x hc7 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
              exact ⟨k, Nat.le_trans hle hB, hk1⟩
            · by_cases hc8 : isDiamond7Cone8 x
              · rcases hc8_ret_w18 x hc8 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                exact ⟨k, Nat.le_trans hle hB, hk1⟩
              · by_cases hc9 : isDiamond8Cone9 x
                · rcases hc9_ret_w18 x hc9 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                  exact ⟨k, Nat.le_trans hle hB, hk1⟩
                · by_cases hc10 : isDiamond9Cone10 x
                  · rcases hc10_ret_w18 x hc10 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                    exact ⟨k, Nat.le_trans hle hB, hk1⟩
                  · by_cases hc11 : isDiamond10Cone11 x
                    · rcases hc11_ret_w18 x hc11 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                      exact ⟨k, Nat.le_trans hle hB, hk1⟩
                    · by_cases hc12 : isDiamond11Cone12 x
                      · rcases hc12_ret_w18 x hc12 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                        exact ⟨k, Nat.le_trans hle hB, hk1⟩
                      · by_cases hc13 : isDiamond12Cone13 x
                        · rcases hc13_ret_w18 x hc13 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                          exact ⟨k, Nat.le_trans hle hB, hk1⟩
                        · by_cases hc14 : isDiamond13Cone14 x
                          · rcases hc14_ret_w18 x hc14 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                            exact ⟨k, Nat.le_trans hle hB, hk1⟩
                          · by_cases hc15 : isDiamond14Cone15 x
                            · rcases hc15_ret_w18 x hc15 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                              exact ⟨k, Nat.le_trans hle hB, hk1⟩
                            · by_cases hc16 : isDiamond15Cone16 x
                              · rcases hc16_ret_w18 x hc16 with ⟨_, _, k, _, _, _, _, _, _, hle, hk1⟩
                                exact ⟨k, Nat.le_trans hle hB, hk1⟩
                              · have hdesc := cousin_diamond15_outside_cones4to16_descent_and_mod16_nonreentry.1 x
                                  (by omega) hc4 hc5 hc6 hc7 hc8 hc9 hc10 hc11 hc12 hc13 hc14 hc15 hc16
                                rcases ih (cousinDiamond15Step x) (cousinDiamond15Step_pos x hx) (by omega) with
                                  ⟨k, hk_le, hk_eq⟩
                                exact ⟨k + 1, by omega, hk_eq⟩

private theorem cousin_diamond15_reaches_one_within_phi :
    ∀ (B x : Nat), x > 0 -> cousinDiamond2Phi x ≤ B ->
      ∃ k : Nat, k ≤ B ∧ cousinDiamond15Iter k x = 1
  | 0, x, _, hB => by have := cousinDiamond2Phi_ge_succ x; omega
  | B + 1, x, hx, hB =>
    cousin_diamond15_reaches_one_step_w18 B x hx hB
      (fun y hy hyB => cousin_diamond15_reaches_one_within_phi B y hy hyB)

/--
  Theorem W18.3g (`cousin_diamond15_global_convergence`, `zero custom axioms`):
  Unconditional Global Convergence & Degree-5 Polynomial Stopping Bound for `T_diamond15`:
  For EVERY `x > 0`, `cousinDiamond15Iter` reaches `1` within `k ≤ (x + 1) ^ 3 + (x + 1) ^ 5` steps!
-/
theorem cousin_diamond15_global_convergence (x : Nat) (hx : x > 0) :
    ∃ k : Nat, k ≤ (x + 1) ^ 3 + (x + 1) ^ 5 ∧ cousinDiamond15Iter k x = 1 := by
  rcases cousin_diamond15_reaches_one_within_phi (cousinDiamond2Phi x) x hx (Nat.le_refl _) with
    ⟨k, hk_phi, hk1⟩
  exact ⟨k, Nat.le_trans hk_phi (cousinDiamond2Phi_upper_poly_bound x), hk1⟩

private theorem exists_non_desc_along_diamond15_iter_w18 :
    ∀ (terms : List LaurentTerm) (A0 B0 C0 N z : Nat),
      N ≥ 1 ->
      (∀ i : Nat, i < N ->
        cousinDiamond15Iter i z ≥ 3 ∧
        (cousinDiamond15Iter i z) % 2 = 1 ∧
        cousinDiamond15Step (cousinDiamond15Iter i z) ≥ 3) ->
      ¬ laurentDescProp terms A0 B0 C0 z (cousinDiamond15Iter N z) ->
      ∃ x : Nat,
        x ≥ 3 ∧ x % 2 = 1 ∧ cousinDiamond15Step x ≥ 3 ∧
        ¬ laurentDescProp terms A0 B0 C0 x (cousinDiamond15Step x)
  | _, _, _, _, 0, _, hN, _, _ => by omega
  | _, _, _, _, 1, z, _, hall, hnd => by
    rcases hall 0 (by decide) with ⟨hz3, hzo, hsz3⟩
    exact ⟨z, hz3, hzo, hsz3, hnd⟩
  | terms, A0, B0, C0, m + 2, z, _, hall, hnd => by
    if h0 : laurentDescProp terms A0 B0 C0 z (cousinDiamond15Step z) then
      have hnd_next : ¬ laurentDescProp terms A0 B0 C0 (cousinDiamond15Step z)
          (cousinDiamond15Iter (m + 1) (cousinDiamond15Step z)) :=
        fun hrest => hnd (laurentDescProp_trans terms A0 B0 C0 z (cousinDiamond15Step z) _ h0 hrest)
      exact exists_non_desc_along_diamond15_iter_w18 terms A0 B0 C0 (m + 1) (cousinDiamond15Step z)
        (by omega) (fun i hi => hall (i + 1) (by omega)) hnd_next
    else
      rcases hall 0 (by omega) with ⟨hz3, hzo, hsz3⟩
      exact ⟨z, hz3, hzo, hsz3, h0⟩

private theorem d14Iter_add_w18 : ∀ (a b x : Nat),
    cousinDiamond14Iter (a + b) x = cousinDiamond14Iter b (cousinDiamond14Iter a x)
  | 0, _, _ => by simp [cousinDiamond14Iter]
  | a + 1, b, x => by
    rw [Nat.succ_add]
    exact d14Iter_add_w18 a b (cousinDiamond14Step x)

private theorem d14Step_of_mod4_eq_3_w18 (z : Nat) (hm4 : z % 4 = 3) :
    cousinDiamond14Step z = (3 * z + 1) / 2 := by
  have hdm32 := (Nat.div_add_mod z 32).symm
  rw [d14_eq_d13_of_not_cone15_w18 z (not_cone15_of_mod32_ne_21_w18 z (by omega)),
      d13_eq_d12_of_not_cone14_w18 z (not_cone14_of_mod32_ne_21_w18 z (by omega)),
      d12_eq_d11_of_not_cone13_w18 z (not_cone13_of_mod32_ne_21_w18 z (by omega)),
      cousinDiamond11Step_eq_d10_of_not_cone12 z (not_cone12_of_mod4_eq_3 z hm4),
      cousinDiamond10Step_eq_d9_of_not_cone11 z (not_cone11_of_mod4_eq_3 z hm4),
      cousinDiamond9Step_eq_d8_of_not_cone10 z (not_cone10_of_mod4_eq_3 z hm4),
      cousinDiamond8Step_eq_d7_of_not_cone9 z (not_cone9_of_mod4_eq_3 z hm4),
      cousinDiamond7Step_eq_d6_of_not_cone8 z (not_cone8_of_mod4_eq_3 z hm4),
      cousinDiamond6Step_eq_d5_of_not_cone7 z (not_cone7_of_mod4_eq_3 z hm4),
      cousinDiamond5Step_eq_d4_of_not_cone6 z (not_cone6_of_mod4_eq_3 z hm4),
      cousinDiamond4Step_mod4_eq_3 z hm4]

private theorem d15_iter_eq_d14_of_avoids_cone16 :
    ∀ (k x : Nat), (∀ i : Nat, i < k -> ¬ isDiamond15Cone16 (cousinDiamond14Iter i x)) ->
      cousinDiamond15Iter k x = cousinDiamond14Iter k x
  | 0, _, _ => rfl
  | k + 1, x, hav => by
    simp only [cousinDiamond15Iter, cousinDiamond14Iter]
    rw [d15_eq_d14_of_not_cone16 x (hav 0 (by omega))]
    exact d15_iter_eq_d14_of_avoids_cone16 k (cousinDiamond14Step x)
      (fun i hi => hav (i + 1) (by omega))

private theorem d15_cascade11_steps_w18 :
    cousinDiamond15Step 54043172876472461 = 20266189828677173 ∧
    cousinDiamond15Step 20266189828677173 = 1899955296438485 ∧
    cousinDiamond15Step 1899955296438485 = 44530202260277 ∧
    cousinDiamond15Step 44530202260277 = 4174706461901 ∧
    cousinDiamond15Step 4174706461901 = 1565514923213 ∧
    cousinDiamond15Step 1565514923213 = 587068096205 ∧
    cousinDiamond15Step 587068096205 = 220150536077 ∧
    cousinDiamond15Step 220150536077 = 82556451029 ∧
    cousinDiamond15Step 82556451029 = 1934916821 ∧
    cousinDiamond15Step 1934916821 = 45349613 ∧
    cousinDiamond15Step 45349613 = 17006105 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
   by decide, by decide, by decide, by decide, by decide⟩

/--
  Theorem W18.3h (`cousin_diamond15_thirteen_tier_cascade_and_laurent_impossibility`,
  `zero custom axioms`):
  1. Genuine 13-Tier `Cone 16 -> Cone 15 -> Cone 14 -> ... -> Cone 5` Cascade
     `54043172876472461 -> 20266189828677173 -> 1899955296438485 -> 44530202260277 -> 4174706461901 ->
      1565514923213 -> 587068096205 -> 220150536077 -> 82556451029 -> 1934916821 -> 45349613 -> 17006105`
     & Unbounded `r`-Block Spiral Climb
     `cousinDiamond15Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5`!
  2. Universal `∀ L ≥ 1` Multi-Term Laurent Valuation Impossibility on `cousinDiamond15Step`!
-/
theorem cousin_diamond15_thirteen_tier_cascade_and_laurent_impossibility :
    cousinDiamond15Step 54043172876472461 = 20266189828677173 ∧
    cousinDiamond15Step 20266189828677173 = 1899955296438485 ∧
    cousinDiamond15Step 1899955296438485 = 44530202260277 ∧
    cousinDiamond15Step 44530202260277 = 4174706461901 ∧
    cousinDiamond15Step 4174706461901 = 1565514923213 ∧
    cousinDiamond15Step 1565514923213 = 587068096205 ∧
    cousinDiamond15Step 587068096205 = 220150536077 ∧
    cousinDiamond15Step 220150536077 = 82556451029 ∧
    cousinDiamond15Step 82556451029 = 1934916821 ∧
    cousinDiamond15Step 1934916821 = 45349613 ∧
    cousinDiamond15Step 45349613 = 17006105 ∧
    (∀ (r j : Nat), r ≥ 1 -> j ≤ r ->
      cousinDiamond15Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5) ∧
    (∀ (terms : List LaurentTerm) (A0 B0 C0 : Nat),
      (∃ t ∈ terms, t.coeff > 0) ->
      ∃ x : Nat,
        x ≥ 3 ∧ x % 2 = 1 ∧ cousinDiamond15Step x ≥ 3 ∧
        ¬ (evalLaurentSumNum terms (cousinDiamond15Step x) * laurentValDen A0 B0 C0 x <
            evalLaurentSumNum terms x * laurentValDen A0 B0 C0 (cousinDiamond15Step x))) := by
  have hspiral : ∀ (r j : Nat), r ≥ 1 -> j ≤ r ->
      cousinDiamond15Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5 := by
    have hsp14 := cousin_diamond14_twelve_tier_cascade_and_laurent_impossibility.2.2.2.2.2.2.2.2.2.2.1
    intro r j hr hj
    rw [← hsp14 r j hr hj]
    apply d15_iter_eq_d14_of_avoids_cone16 (2 * j) (4 * 16 ^ r - 5)
    intro i hi
    let q := i / 2
    have hq_lt : q < r := by dsimp [q]; omega
    have h2q := hsp14 r q hr (by omega)
    let M := 16 ^ (r - q - 1) * 18 ^ q
    have hM_pos : M ≥ 1 :=
      Nat.mul_le_mul (nat_pow_pos_of_pos 16 (by decide) _) (nat_pow_pos_of_pos 18 (by decide) _)
    have hze : 4 * 16 ^ (r - q) * 18 ^ q - 5 = 64 * M - 5 := by
      apply congrArg (· - 5)
      rw [show r - q = (r - q - 1) + 1 by omega, Nat.pow_succ 16 (r - q - 1)]
      dsimp only [M]
      generalize 16 ^ (r - q - 1) = A, 18 ^ q = B
      change 4 * (A * 16) * B = (4 * 16) * (A * B); ac_rfl
    if hev : i % 2 = 0 then
      have hi_eq : i = 2 * q := by dsimp [q]; omega
      rw [hi_eq, h2q, hze]
      exact not_cone16_of_mod8_ne_5 _ (by omega)
    else
      have hi_eq : i = 2 * q + 1 := by dsimp [q]; omega
      rw [hi_eq, d14Iter_add_w18 (2 * q) 1, h2q, hze]
      change ¬ isDiamond15Cone16 (cousinDiamond14Step (64 * M - 5))
      rw [d14Step_of_mod4_eq_3_w18 (64 * M - 5) (by omega)]
      exact not_cone16_of_mod8_ne_5 _ (by omega)
  rcases d15_cascade11_steps_w18 with ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩
  refine ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, hspiral, ?_⟩
  intro terms A0 B0 C0 hnonempty
  rcases three_family_multiterm_laurent_obstruction terms A0 B0 C0 hnonempty with
    h97 | ⟨j2, hj2⟩ | ⟨r, hr_pos, hr3⟩
  · have hs97 : cousinDiamond15Step 97 = 73 := by decide
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
    have hstep_xj2 : cousinDiamond15Step xj2 = yj2 :=
      d15_cone4_step_exact_w18 xj2 (2 * Mj) hc4_xj2 (by omega) (by dsimp [xj2]; omega)
    exact ⟨xj2, by dsimp [xj2]; omega, hxj2_odd, by rw [hstep_xj2]; dsimp [yj2]; omega, by rwa [hstep_xj2]⟩
  · let xr3 := 2 * 4 ^ r - 1
    let zr := 2 * 9 ^ r - 1
    let yr3 := (3 * 9 ^ r - 1) / 2
    have hp9_ge9 : 9 ^ r ≥ 9 := by
      rw [show r = (r - 1) + 1 by omega, Nat.pow_succ]; have := nat_pow_pos_of_pos 9 (by decide) (r - 1); omega
    have hxr3_pow : xr3 = 2 ^ (2 * r + 1) * 1 - 1 := by
      dsimp [xr3]; rw [Nat.mul_one, pow4_eq_pow2_even r, Nat.pow_succ, Nat.mul_comm]
    have hglide_i : ∀ i : Nat, i ≤ 2 * r ->
        cousinDiamond15Iter i xr3 = 3 ^ i * 2 ^ (2 * r + 1 - i) - 1 ∧
        cousinDiamond15Iter i xr3 ≥ 7 ∧ (cousinDiamond15Iter i xr3) % 2 = 1 := by
      intro i hi
      have hf := cousin_diamond15_mersenne_scaled i (2 * r + 1) 1 (by omega) (by decide)
      rw [← hxr3_pow, Nat.mul_one] at hf
      have hprod_ge8 : 3 ^ i * 2 ^ (2 * r + 1 - i) ≥ 8 := by
        have h1 : 2 ^ i * 2 ^ (2 * r + 1 - i) ≤ 3 ^ i * 2 ^ (2 * r + 1 - i) :=
          Nat.mul_le_mul_right _ (pow2_le_pow3 i)
        rw [← Nat.pow_add, show i + (2 * r + 1 - i) = 2 * r + 1 by omega] at h1
        exact Nat.le_trans (pow2_mono_nat (by omega : 3 ≤ 2 * r + 1)) h1
      have hprod_ev : (3 ^ i * 2 ^ (2 * r + 1 - i)) % 2 = 0 := by
        rw [show 2 * r + 1 - i = (2 * r - i) + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc]; omega
      exact ⟨hf, by rw [hf]; omega, by rw [hf]; omega⟩
    have hiter_2r : cousinDiamond15Iter (2 * r) xr3 = zr := by
      have hf := (hglide_i (2 * r) (Nat.le_refl _)).1
      rw [hf, show 2 * r + 1 - 2 * r = 1 by omega, Nat.pow_one, ← pow9_eq_pow3_double r, Nat.mul_comm]
    have hstep_zr : cousinDiamond15Step zr = yr3 := (d15_zr_yr_steps_w18 r (by omega)).1
    have hiter_2r1 : cousinDiamond15Iter (2 * r + 1) xr3 = yr3 := by
      rw [cousinDiamond15Iter_add (2 * r) 1 xr3, hiter_2r]; exact hstep_zr
    have hall : ∀ i : Nat, i < 2 * r + 1 ->
        cousinDiamond15Iter i xr3 ≥ 3 ∧ (cousinDiamond15Iter i xr3) % 2 = 1 ∧
        cousinDiamond15Step (cousinDiamond15Iter i xr3) ≥ 3 := by
      intro i hi
      by_cases hlt : i < 2 * r
      · rcases hglide_i i (by omega) with ⟨_, hge7, hodd_i⟩
        rcases hglide_i (i + 1) (by omega) with ⟨_, hge7_n, _⟩
        refine ⟨by omega, hodd_i, ?_⟩
        change cousinDiamond15Iter 1 (cousinDiamond15Iter i xr3) ≥ 3
        rw [← cousinDiamond15Iter_add i 1 xr3]; omega
      · rw [show i = 2 * r by omega, hiter_2r, hstep_zr]
        exact ⟨by dsimp [zr]; omega, by dsimp [zr]; omega, by dsimp [yr3]; omega⟩
    change ¬ laurentDescProp terms A0 B0 C0 xr3 yr3 at hr3
    rw [← hiter_2r1] at hr3
    exact exists_non_desc_along_diamond15_iter_w18 terms A0 B0 C0 (2 * r + 1) xr3 (by omega) hall hr3

set_option maxRecDepth 16384 in
private theorem d15_sep_chunk1_w18 :
    cousinDiamond15StepInt (-1) = -1 ∧
    cousinDiamond15IterInt 3 (-5) = -5 ∧
    cousinDiamond15IterParam 7 5 5 = 5 ∧
    cousinDiamond15StepQ6 (1, 7) = (5, 7) ∧
    cousinDiamond15IterQ6 5 (1, 7) = (1, 7) ∧
    cousinDiamond15StepQ6 (54043172876472461, 7) = cousinDiamond14StepQ6 (54043172876472461, 7) ∧
    cousinDiamond15StepQ6 (108086368404918413, 7) = cousinDiamond14StepQ6 (108086368404918413, 7) := by
  decide

set_option maxRecDepth 16384 in
private theorem d15_sep_chunk2_w18 :
    isDiamond15Cone16 108086368404918413 ∧
    cousinDiamond15Step 108086368404918413 = 40532388151844405 ∧
    cousinDiamond15Iter 26 108086368404918413 = 1 ∧
    isDiamond15Cone16 54043172876472461 ∧
    cousinDiamond15Step 54043172876472461 = 20266189828677173 ∧
    cousinDiamond15StepInt 54043172876472461 = 20266189828677173 ∧
    cousinDiamond15StepQ6 (54043172876472461, 1) = (20266189828677173, 1) :=
  ⟨by decide, by decide, by decide, by decide, d15_cascade11_steps_w18.1, by decide, by decide⟩

set_option maxRecDepth 16384 in
private theorem d15_sep_chunk3_w18 :
    isDiamond14Cone15 20266189828677173 ∧
    isDiamond13Cone14 1899955296438485 ∧
    isDiamond12Cone13 44530202260277 ∧
    isDiamond11Cone12 4174706461901 ∧
    isDiamond10Cone11 1565514923213 ∧
    isDiamond9Cone10 587068096205 ∧
    isDiamond8Cone9 220150536077 ∧
    isDiamond7Cone8 82556451029 ∧
    isDiamond6Cone7 1934916821 ∧
    isDiamond5Cone6 45349613 ∧
    isDiamond4Cone5 17006105 ∧
    cousinDiamond2Phi 54043172876472461 < cousinDiamond2Phi 20266189828677173 ∧
    cousinDiamond15Iter 30 54043172876472461 = 1 := by
  have hi30 : cousinDiamond15Iter 30 54043172876472461 = 1 := by
    rcases d15_cascade11_steps_w18 with ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩
    change cousinDiamond15Iter 29 (cousinDiamond15Step 54043172876472461) = 1; rw [s1]
    change cousinDiamond15Iter 28 (cousinDiamond15Step 20266189828677173) = 1; rw [s2]
    change cousinDiamond15Iter 27 (cousinDiamond15Step 1899955296438485) = 1; rw [s3]
    change cousinDiamond15Iter 26 (cousinDiamond15Step 44530202260277) = 1; rw [s4]
    change cousinDiamond15Iter 25 (cousinDiamond15Step 4174706461901) = 1; rw [s5]
    change cousinDiamond15Iter 24 (cousinDiamond15Step 1565514923213) = 1; rw [s6]
    change cousinDiamond15Iter 23 (cousinDiamond15Step 587068096205) = 1; rw [s7]
    change cousinDiamond15Iter 22 (cousinDiamond15Step 220150536077) = 1; rw [s8]
    change cousinDiamond15Iter 21 (cousinDiamond15Step 82556451029) = 1; rw [s9]
    change cousinDiamond15Iter 20 (cousinDiamond15Step 1934916821) = 1; rw [s10]
    change cousinDiamond15Iter 19 (cousinDiamond15Step 45349613) = 1; rw [s11]
    decide
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide,
         by decide, by decide, by decide, by decide, by decide, by decide, hi30⟩

set_option maxRecDepth 16384 in
/--
  Theorem W18.3i (`cousin_diamond15_counter_model_separation`, `[]` axioms):
  `T_diamond15` rejects ALL three Counter-Models (`M1 = Q_(6)^+` 5-cycle `(1, 7) -> ... -> (1, 7)`
  plus non-integers `(54043172876472461, 7)` and `(108086368404918413, 7)` bypassing Cone 16 by `W18.3c`,
  `M2 = Z^-` cycles `-1` and `-5 -> -7 -> -10 -> -5`, and `M3` supercritical `q = 7` 5-cycle at `5`),
  AND at the genuine `v_2(3x + 1) = 3` Cone-16 jumps
  `54043172876472461 -> 20266189828677173 -> 1899955296438485 -> 44530202260277 -> 4174706461901 ->
   1565514923213 -> 587068096205 -> 220150536077 -> 82556451029 -> 1934916821 -> 45349613 -> 17006105`
  (`ZPOS_COUSIN_DIAMOND15_CONE16_54043172876472461_JUMP`, `30` steps to `1`, `+38.44x` `Φ_2` jump)
  and `108086368404918413 -> 40532388151844405` (`26` steps to `1`) strictly increases `cousinDiamond2Phi`
  directly into `Cone 15 -> Cone 14 -> ... -> Cone 5`!
-/
theorem cousin_diamond15_counter_model_separation :
    cousinDiamond15StepInt (-1) = -1 ∧
    cousinDiamond15IterInt 3 (-5) = -5 ∧
    cousinDiamond15IterParam 7 5 5 = 5 ∧
    cousinDiamond15StepQ6 (1, 7) = (5, 7) ∧
    cousinDiamond15IterQ6 5 (1, 7) = (1, 7) ∧
    cousinDiamond15StepQ6 (54043172876472461, 7) = cousinDiamond14StepQ6 (54043172876472461, 7) ∧
    cousinDiamond15StepQ6 (108086368404918413, 7) = cousinDiamond14StepQ6 (108086368404918413, 7) ∧
    isDiamond15Cone16 108086368404918413 ∧
    cousinDiamond15Step 108086368404918413 = 40532388151844405 ∧
    cousinDiamond15Iter 26 108086368404918413 = 1 ∧
    isDiamond15Cone16 54043172876472461 ∧
    cousinDiamond15Step 54043172876472461 = 20266189828677173 ∧
    cousinDiamond15StepInt 54043172876472461 = 20266189828677173 ∧
    cousinDiamond15StepQ6 (54043172876472461, 1) = (20266189828677173, 1) ∧
    isDiamond14Cone15 20266189828677173 ∧
    isDiamond13Cone14 1899955296438485 ∧
    isDiamond12Cone13 44530202260277 ∧
    isDiamond11Cone12 4174706461901 ∧
    isDiamond10Cone11 1565514923213 ∧
    isDiamond9Cone10 587068096205 ∧
    isDiamond8Cone9 220150536077 ∧
    isDiamond7Cone8 82556451029 ∧
    isDiamond6Cone7 1934916821 ∧
    isDiamond5Cone6 45349613 ∧
    isDiamond4Cone5 17006105 ∧
    cousinDiamond2Phi 54043172876472461 < cousinDiamond2Phi 20266189828677173 ∧
    cousinDiamond15Iter 30 54043172876472461 = 1  :=
  let c1 := d15_sep_chunk1_w18
  let c2 := d15_sep_chunk2_w18
  let c3 := d15_sep_chunk3_w18
  ⟨c1.1, c1.2.1, c1.2.2.1, c1.2.2.2.1, c1.2.2.2.2.1, c1.2.2.2.2.2.1, c1.2.2.2.2.2.2,
   c2.1, c2.2.1, c2.2.2.1, c2.2.2.2.1, c2.2.2.2.2.1, c2.2.2.2.2.2.1, c2.2.2.2.2.2.2,
   c3⟩


-- ============================================================================
-- SECTION 3: Front D (Branches P2.2 & P5.3) — Complete Mod-`354294` (`2 * 3^11`,
--            `w ≥ 12`, Length-`11` `Mod 2048` `108`-Prefix Lift!) Markov
--            Bijection, Choice-Free `Mod 81` Stall vs `Mod 243` 4-Step
--            Macro-Selector, & Sub-`250` (`M_0 = 210 ≤ 250`), Steeper-Slope
--            (`c = 5 ≤ 5`, Beating `c = 6`!) Exponential Dyadic Occupancy (`W18_H4`)
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Section 3A: Complete Mod-`354294` (`2 * 3^11`) Markov Bijection, `54/54`
--             Length-`10` `Mod 1024` Weight-`≤ 11` Escapes, & Exact `108`-Prefix
--             Length-`11` `Mod 2048` Lift (`W18_H4`)
-- ----------------------------------------------------------------------------

/-- Canonical ordered list of the `118098 = 2 * 3^10` surviving mod-`354294` (`2 * 3^11`)
    suffix-shift classes `{r < 354294 | r % 6 = 1 ∨ r % 6 = 3}` on `w ≥ 12`. -/
def survivingMod354294List : List Nat :=
  (List.range 354294).filter (fun r => r % 6 == 1 || r % 6 == 3)

private theorem mem_survivingMod354294List_iff_w18 (r : Nat) :
    r ∈ survivingMod354294List ↔ (r < 354294 ∧ (r % 6 = 1 ∨ r % 6 = 3)) := by
  unfold survivingMod354294List
  rw [List.mem_filter, List.mem_range]
  simp only [Bool.or_eq_true, beq_iff_eq]

private theorem range_six_mul_surviving_step_w18 (n : Nat)
    (ih : ((List.range (6 * n)).filter (fun r => r % 6 == 1 || r % 6 == 3)).length = 2 * n) :
    ((List.range (6 * (n + 1))).filter (fun r => r % 6 == 1 || r % 6 == 3)).length = 2 * (n + 1) := by
  let p : Nat -> Bool := fun r => r % 6 == 1 || r % 6 == 3
  change ((List.range (6 * (n + 1))).filter p).length = 2 * (n + 1)
  change ((List.range (6 * n)).filter p).length = 2 * n at ih
  rw [show 6 * (n + 1) = (6 * n + 5) + 1 by omega, List.range_succ,
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
  omega

private theorem range_six_mul_surviving_len_w18 :
    ∀ n : Nat, ((List.range (6 * n)).filter (fun r => r % 6 == 1 || r % 6 == 3)).length = 2 * n
  | 0 => rfl
  | n + 1 => range_six_mul_surviving_step_w18 n (range_six_mul_surviving_len_w18 n)

/-- Surviving mod-`2048` length-`11` prefix predicate (`108 = 4 * 27` residues lifting `Mod 512`). -/
def isSurvivingMod2048Bool (r : Nat) : Bool :=
  isSurvivingMod512Bool (r % 512)

/-- Canonical ordered list of the `108` surviving mod-`2048` residues. -/
def survivingMod2048Residues108 : List Nat :=
  (List.range 2048).filter isSurvivingMod2048Bool

/-- Exact weight-`k` (`k ∈ {11, 10, 9, 8, 7, 6}`) surviving mod-`2048` length-`11` prefix predicate. -/
def isWeightKSurvivingMod2048Bool (k y : Nat) : Bool :=
  isSurvivingMod2048Bool (y % 2048) && decide (parityWeight (parityOfIter 11 (y % 2048)) = k)

/-- Unique top-weight (`w = 11`) surviving mod-`2048` residue `[2047]`. -/
def topWeight11Mod2048Residues1 : List Nat :=
  survivingMod2048Residues108.filter (isWeightKSurvivingMod2048Bool 11)

private theorem take_drop_split_eq_w18 :
    ∀ (k : Nat) (xs : List Bool), xs.take k ++ xs.drop k = xs
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, x :: xs => by
    simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append,
               take_drop_split_eq_w18 k xs]

private theorem take_len_of_ge_w18 :
    ∀ (k : Nat) (xs : List Bool), k ≤ xs.length -> (xs.take k).length = k
  | 0, _, _ => rfl
  | _ + 1, [], h => by simp at h
  | k + 1, _ :: xs, h => by
    simp only [List.length_cons] at h
    simp only [List.take_succ_cons, List.length_cons, take_len_of_ge_w18 k xs (by omega)]

private theorem len12_core_mod2048_prefix11_w18
    (p11 freeBits : List Bool) (q : Nat)
    (hp11_len : p11.length = 11)
    (hu : IsCoreParityWord (p11 ++ freeBits ++ [true])) :
    parityOfIter 11 (exactBackwardQuotient 1 (p11 ++ freeBits ++ [true]) q % 2048) = p11 := by
  let u := p11 ++ freeBits ++ [true]
  let y := exactBackwardQuotient 1 u q
  let K := backwardOneTotalSteps u q
  let shift := canonicalSuffixShift u 1 + q * (2 * 3 ^ (parityWeight u - 1))
  have hu_len : u.length = 11 + (freeBits.length + 1) := by
    dsimp [u]; rw [List.length_append, List.length_append, hp11_len, List.length_singleton]
    omega
  have hK_ge12 : K ≥ 12 := by unfold K backwardOneTotalSteps; omega
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
  have hKs11 : K = 11 + (K - 11) := by omega
  have hpar_sp := parityOfIter_append_split 11 (K - 11) y
  rw [← hKs11, ← hv_par] at hpar_sp
  have hv_p11 : v = p11 ++ (freeBits ++ [true] ++ List.replicate shift false) := by
    dsimp [v, u]
    rw [List.append_assoc p11 freeBits [true],
        List.append_assoc p11 (freeBits ++ [true]) (List.replicate shift false)]
  rw [hv_p11] at hpar_sp
  have hlen11 : p11.length = (parityOfIter 11 y).length := by
    rw [hp11_len, parityOfIter_length]
  have hp11_eq : parityOfIter 11 y = p11 :=
    (list_append_inj_left_eq_len _ _ _ _ hlen11 hpar_sp).1.symm
  have hy_div11 : y = y % 2048 + 2 ^ 11 * (y / 2048) := by
    have hdm := (Nat.div_add_mod y 2048).symm
    rw [show (2 : Nat) ^ 11 = 2048 from rfl]; omega
  have hpar11_mod : parityOfIter 11 y = parityOfIter 11 (y % 2048) := by
    conv => lhs; rw [hy_div11]
    exact parityOfIter_mod_pow2_shift 11 (y % 2048) (y / 2048)
  rw [← hpar11_mod, hp11_eq]

private theorem pow_mod_eq_pow_mod_w18 (b m : Nat) :
    ∀ e : Nat, (b ^ e) % m = ((b % m) ^ e) % m
  | 0 => rfl
  | e + 1 => by
    rw [Nat.pow_succ b e, Nat.pow_succ (b % m) e, Nat.mul_mod (b ^ e) b m,
        pow_mod_eq_pow_mod_w18 b m e, Nat.mul_mod ((b % m) ^ e % m) (b % m) m,
        Nat.mod_mod, ← Nat.mul_mod ((b % m) ^ e) (b % m) m]

private def len10SurvivingEscapeTable (r : Nat) : List Nat × Nat :=
  match r with
  | 27   => ([43, 10], 27)
  | 31   => ([2, 68], 15)
  | 47   => ([19, 9], 19)
  | 71   => ([6, 2], 33)
  | 91   => ([33, 4], 9)
  | 103  => ([15, 26], 3)
  | 111  => ([19, 9], 13)
  | 127  => ([43, 7], 43)
  | 155  => ([3, 12], 9)
  | 159  => ([20, 23], 103)
  | 167  => ([1, 88], 27)
  | 191  => ([23, 22], 9)
  | 231  => ([29, 9], 19)
  | 239  => ([9, 33], 31)
  | 251  => ([5, 16], 63)
  | 255  => ([44, 7], 43)
  | 283  => ([12, 21], 31)
  | 303  => ([18, 2], 33)
  | 327  => ([15, 13], 19)
  | 347  => ([1, 8], 3)
  | 359  => ([10, 19], 37)
  | 415  => ([13, 18], 15)
  | 423  => ([22], 15)
  | 447  => ([58, 14], 105)
  | 495  => ([10, 41], 31)
  | 507  => ([19, 4], 9)
  | 511  => ([78, 8], 21)
  | 539  => ([5, 5], 7)
  | 543  => ([2, 33], 13)
  | 559  => ([14, 4], 39)
  | 583  => ([5, 2], 3)
  | 603  => ([6, 55], 19)
  | 615  => ([12, 11], 31)
  | 623  => ([29], 33)
  | 639  => ([13, 63], 67)
  | 667  => ([10, 12], 27)
  | 671  => ([11, 39], 19)
  | 679  => ([5], 27)
  | 703  => ([4, 7], 7)
  | 743  => ([9, 50], 3)
  | 751  => ([8, 3], 67)
  | 763  => ([8, 2], 21)
  | 767  => ([77, 8], 21)
  | 795  => ([8, 68], 69)
  | 815  => ([9], 25)
  | 839  => ([10, 44], 3)
  | 859  => ([4], 63)
  | 871  => ([4, 38], 15)
  | 927  => ([16, 1], 25)
  | 935  => ([3, 22], 27)
  | 959  => ([9, 28], 39)
  | 1007 => ([27, 5], 25)
  | 1019 => ([1, 50], 3)
  | 1023 => ([446], 33)
  | _    => ([0], 3)

private def checkLen10EscapeEntryBool (r : Nat) : Bool :=
  let pr := len10SurvivingEscapeTable r
  let pref := parityOfIter 10 r
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
  decide (L ≥ 11 ∧ 1 ≤ w ∧ w ≤ 11 ∧ 3 ≤ a ∧ a < 2 * 3 ^ (w - 1) ∧ C < P2) &&
  (P3 * y + C == P2) &&
  isSurvivingMod373248Bool y &&
  (y % 1024 == r)

set_option exponentiation.threshold 8192 in
private theorem esc11_allones10_cert_w18 :
    let u_esc11 : List Bool :=
      List.replicate 10 true ++ List.replicate 446 false ++ [true]
    u_esc11.length = 457 ∧
    parityWeight u_esc11 = 11 ∧
    IsFirstHitOnePair u_esc11 0 ∧
    exactBackwardQuotient 1 u_esc11 0 =
      18045298623953582795729423582265437192090384467670343105690885553942878906000080934174237109098719535103271885410225272309068657920294140666879 ∧
    IsSurvivingMod373248Class (exactBackwardQuotient 1 u_esc11 0) ∧
    exactBackwardQuotient 1 u_esc11 0 % 1024 = 1023 ∧
    exactBackwardQuotient 1 u_esc11 0 % 2048 = 1023 := by
  dsimp only
  let u_esc11 : List Bool := List.replicate 10 true ++ List.replicate 446 false ++ [true]
  have hlen : u_esc11.length = 457 := by
    dsimp only [u_esc11]
    simp only [List.length_append, List.length_replicate, List.length_singleton]
  have hwt : parityWeight u_esc11 = 11 := by
    dsimp only [u_esc11]
    rw [parityWeight_append, (affineCarry_append_replicate_false (List.replicate 10 true) 446).1]
    decide
  have hcore : IsCoreParityWord u_esc11 := by
    refine ⟨rfl, ?_⟩
    dsimp only [u_esc11]; rw [List.reverse_append]; rfl
  have hcar : affineCarry u_esc11 = 174075 + 2 ^ 456 := by
    dsimp only [u_esc11]
    rw [affineCarry_append,
        (affineCarry_append_replicate_false (List.replicate 10 true) 446).2,
        List.length_append, List.length_replicate, List.length_replicate,
        show affineCarry (List.replicate 10 true) = 58025 by decide,
        show affineCarry [true] = 1 from rfl,
        show parityWeight [true] = 1 from rfl,
        show 10 + 446 = 456 from rfl]
  have hsh33 : canonicalSuffixShift u_esc11 1 = 33 := by
    rcases canonicalSuffixShift_spec_unique u_esc11 1 (by rw [hwt]; decide) (by decide) with ⟨_, _, huniq⟩
    symm
    apply huniq 33 (by rw [hwt]; decide)
    rw [Nat.mul_one, hlen, hwt, hcar]
  have hfh_esc : IsFirstHitOnePair u_esc11 0 :=
    (first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.2 u_esc11 hcore).mpr
      (by rw [hsh33]; decide)
  let q_esc11 : Nat :=
    18045298623953582795729423582265437192090384467670343105690885553942878906000080934174237109098719535103271885410225272309068657920294140666879
  have hq_eq : 3 ^ 11 * q_esc11 + (174075 + 2 ^ 456) = 2 ^ 490 := by decide
  have hq_val : exactBackwardQuotient 1 u_esc11 0 = q_esc11 := by
    rcases one_generator_pos_odd_and_reaches_one u_esc11 0 hcore with ⟨_, _, heq_bw, _⟩
    have hst : backwardOneTotalSteps u_esc11 0 = 490 := by
      unfold backwardOneTotalSteps; rw [hlen, hsh33, Nat.zero_mul, Nat.add_zero]
    rw [hst, hwt, hcar] at heq_bw
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3 ^ 11)
      (Nat.add_right_cancel (heq_bw.symm.trans hq_eq.symm))
  have hb_surv : isSurvivingMod373248Bool q_esc11 = true := by decide
  rw [hq_val]
  exact ⟨hlen, hwt, hfh_esc, rfl, isSurvivingMod373248Bool_imp_class _ hb_surv, by decide, by decide⟩

private def checkRangeLen10EscW18 (base : Nat) : Nat -> Bool
  | 0 => !(isSurvivingMod1024Bool base) || checkLen10EscapeEntryBool base
  | k + 1 =>
    (!(isSurvivingMod1024Bool (base + (k + 1))) || checkLen10EscapeEntryBool (base + (k + 1))) &&
      checkRangeLen10EscW18 base k

private theorem checkRangeLen10EscW18_get (base : Nat) :
    ∀ (top j : Nat), checkRangeLen10EscW18 base top = true -> j ≤ top ->
      isSurvivingMod1024Bool (base + j) = true -> checkLen10EscapeEntryBool (base + j) = true
  | 0, j, h, hj, hsurv => by
    have hj0 : j = 0 := by omega
    subst hj0; rw [Nat.add_zero] at hsurv ⊢
    unfold checkRangeLen10EscW18 at h
    simp [hsurv] at h; exact h
  | top + 1, j, h, hj, hsurv => by
    unfold checkRangeLen10EscW18 at h
    rcases Bool.and_eq_true_iff.mp h with ⟨hhd, htl⟩
    if hjt : j = top + 1 then
      subst hjt; simp [hsurv] at hhd; exact hhd
    else
      exact checkRangeLen10EscW18_get base top j htl (by omega) hsurv

set_option exponentiation.threshold 2048 in
set_option maxRecDepth 8192 in
private theorem len10_escape_range_0 : checkRangeLen10EscW18 0 255 = true := by decide

set_option exponentiation.threshold 2048 in
set_option maxRecDepth 8192 in
private theorem len10_escape_range_1 : checkRangeLen10EscW18 256 255 = true := by decide

set_option exponentiation.threshold 2048 in
set_option maxRecDepth 8192 in
private theorem len10_escape_range_2 : checkRangeLen10EscW18 512 255 = true := by decide

set_option exponentiation.threshold 2048 in
set_option maxRecDepth 8192 in
private theorem len10_escape_range_3 : checkRangeLen10EscW18 768 254 = true := by decide

private theorem take_append_eq_left_w18 :
    ∀ (xs ys : List Bool) (n : Nat), xs.length = n -> (xs ++ ys).take n = xs
  | [], _, n, hn => by subst hn; rfl
  | _ :: xtl, ys, n, hn => by
    cases n with
    | zero => simp at hn
    | succ n' =>
      simp only [List.cons_append, List.take]
      rw [take_append_eq_left_w18 xtl ys n' (by simp at hn; omega)]

private theorem len10_all54_surviving_escape_sound (r : Fin 1024)
    (hsurv : isSurvivingMod1024Bool r.val = true) :
    ∃ u : List Bool,
      u.take 10 = parityOfIter 10 r.val ∧
      u.length ≥ 11 ∧
      parityWeight u ≤ 11 ∧
      IsFirstHitOnePair u 0 ∧
      IsSurvivingMod373248Class (exactBackwardQuotient 1 u 0) ∧
      exactBackwardQuotient 1 u 0 % 1024 = r.val := by
  if hr1023 : r.val = 1023 then
    rcases esc11_allones10_cert_w18 with ⟨hlen, hwt, hfh, _, hsurv_c, hm1024, _⟩
    let u1023 := List.replicate 10 true ++ List.replicate 446 false ++ [true]
    have hp1023 : parityOfIter 10 1023 = List.replicate 10 true := by decide
    have htake : u1023.take 10 = parityOfIter 10 r.val := by
      rw [hr1023, hp1023]; dsimp only [u1023]; rw [List.append_assoc]
      exact take_append_eq_left_w18 (List.replicate 10 true) _ 10 (by simp)
    exact ⟨u1023, htake, by dsimp only [u1023]; omega, by dsimp only [u1023]; omega,
           hfh, hsurv_c, hm1024.trans hr1023.symm⟩
  else
    have hr_lt1023 : r.val < 1023 := by have := r.isLt; omega
    have hc : checkLen10EscapeEntryBool r.val = true := by
      rcases (by omega : r.val < 256 ∨ (256 ≤ r.val ∧ r.val < 512) ∨
        (512 ≤ r.val ∧ r.val < 768) ∨ (768 ≤ r.val ∧ r.val ≤ 1022)) with
        h0 | ⟨h1a, h1b⟩ | ⟨h2a, h2b⟩ | ⟨h3a, h3b⟩
      · simpa using checkRangeLen10EscW18_get 0 255 r.val len10_escape_range_0 (by omega)
          (by simpa using hsurv)
      · have hg := checkRangeLen10EscW18_get 256 255 (r.val - 256) len10_escape_range_1 (by omega)
          (by rwa [show 256 + (r.val - 256) = r.val by omega])
        rwa [show 256 + (r.val - 256) = r.val by omega] at hg
      · have hg := checkRangeLen10EscW18_get 512 255 (r.val - 512) len10_escape_range_2 (by omega)
          (by rwa [show 512 + (r.val - 512) = r.val by omega])
        rwa [show 512 + (r.val - 512) = r.val by omega] at hg
      · have hg := checkRangeLen10EscW18_get 768 254 (r.val - 768) len10_escape_range_3 (by omega)
          (by rwa [show 768 + (r.val - 768) = r.val by omega])
        rwa [show 768 + (r.val - 768) = r.val by omega] at hg
    unfold checkLen10EscapeEntryBool at hc
    dsimp only at hc
    let pr := len10SurvivingEscapeTable r.val
    let pref := parityOfIter 10 r.val
    let u := pref ++ zeroRunsSuffix pr.1
    let L := u.length
    let w := parityWeight u
    let a := pr.2
    let C := affineCarry u
    let P2 := 2 ^ (L + a)
    let P3 := 3 ^ w
    let y := (P2 - C) / P3
    rcases Bool.and_eq_true_iff.mp hc with ⟨hc1, hy1024_b⟩
    rcases Bool.and_eq_true_iff.mp hc1 with ⟨hc2, hsurv373⟩
    rcases Bool.and_eq_true_iff.mp hc2 with ⟨hc3, heq_b⟩
    rcases Bool.and_eq_true_iff.mp hc3 with ⟨hc4, hbds_b⟩
    rcases Bool.and_eq_true_iff.mp hc4 with ⟨hhd_b, hrhd_b⟩
    rcases of_decide_eq_true hbds_b with ⟨hL11, hw1, hw11, ha3, ha_lt, _⟩
    have heq_y : P3 * y + C = P2 := beq_iff_eq.mp heq_b
    have hy1024 : y % 1024 = r.val := beq_iff_eq.mp hy1024_b
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
    have htake10 : u.take 10 = pref :=
      take_append_eq_left_w18 pref (zeroRunsSuffix pr.1) 10 (parityOfIter_length 10 r.val)
    refine ⟨u, htake10, hL11, hw11, hfh, ?_, ?_⟩
    · rw [hbw_eq]; exact isSurvivingMod373248Bool_imp_class y hsurv373
    · rw [hbw_eq]; exact hy1024

private def surv512List27W18 : List Nat :=
  [27, 31, 47, 71, 91, 103, 111, 127, 155, 159, 167, 191, 231, 239,
   251, 255, 283, 303, 327, 347, 359, 415, 423, 447, 495, 507, 511]

private def surv2048Explicit108W18 : List Nat :=
  surv512List27W18 ++ surv512List27W18.map (fun i => 512 + i) ++
    surv512List27W18.map (fun i => 1024 + i) ++ surv512List27W18.map (fun i => 1536 + i)

private theorem range_add_eq_w18 (a : Nat) :
    ∀ b : Nat, List.range (a + b) = List.range a ++ (List.range b).map (fun i => a + i)
  | 0 => by simp
  | b + 1 => by
    rw [Nat.add_succ, List.range_succ, range_add_eq_w18 a b, List.range_succ,
        List.map_append, List.map_singleton, List.append_assoc]

private theorem filter_map_shift512_w18 (k : Nat) :
    ∀ xs : List Nat, (∀ x ∈ xs, x < 512) ->
      (xs.map (fun i => 512 * k + i)).filter isSurvivingMod2048Bool =
        (xs.filter isSurvivingMod512Bool).map (fun i => 512 * k + i)
  | [], _ => rfl
  | x :: xs, hall => by
    have hx_lt : x < 512 := hall x (List.Mem.head _)
    have hm : isSurvivingMod2048Bool (512 * k + x) = isSurvivingMod512Bool x := by
      unfold isSurvivingMod2048Bool
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx_lt]
    simp only [List.map_cons, List.filter_cons, hm]
    cases isSurvivingMod512Bool x <;>
      simp [filter_map_shift512_w18 k xs (fun y hy => hall y (List.mem_cons_of_mem x hy))]

private theorem filter_surv2048_lt512_w18 :
    ∀ xs : List Nat, (∀ x ∈ xs, x < 512) ->
      xs.filter isSurvivingMod2048Bool = xs.filter isSurvivingMod512Bool
  | [], _ => rfl
  | x :: xs, hall => by
    have hx_lt : x < 512 := hall x (List.Mem.head _)
    have hm : isSurvivingMod2048Bool x = isSurvivingMod512Bool x := by
      unfold isSurvivingMod2048Bool; rw [Nat.mod_eq_of_lt hx_lt]
    simp only [List.filter_cons, hm]
    cases isSurvivingMod512Bool x <;>
      simp [filter_surv2048_lt512_w18 xs (fun y hy => hall y (List.mem_cons_of_mem x hy))]

set_option maxRecDepth 32768 in
private theorem surv512_range_eq_w18 :
    (List.range 512).filter isSurvivingMod512Bool = surv512List27W18 := by
  decide

private theorem survivingMod2048Residues108_eq_w18 :
    survivingMod2048Residues108 = surv2048Explicit108W18 := by
  have hall512 : ∀ x ∈ List.range 512, x < 512 := fun _ hx => List.mem_range.mp hx
  unfold survivingMod2048Residues108 surv2048Explicit108W18
  rw [show (2048 : Nat) = 1536 + 512 from rfl, range_add_eq_w18 1536 512,
      show (1536 : Nat) = 1024 + 512 from rfl, range_add_eq_w18 1024 512,
      show (1024 : Nat) = 512 + 512 from rfl, range_add_eq_w18 512 512]
  simp only [List.filter_append]
  rw [filter_surv2048_lt512_w18 (List.range 512) hall512,
      show (fun i => 512 + i) = (fun i => 512 * 1 + i) from rfl,
      filter_map_shift512_w18 1 (List.range 512) hall512,
      show (fun i => 512 + 512 + i) = (fun i => 512 * 2 + i) from rfl,
      filter_map_shift512_w18 2 (List.range 512) hall512,
      show (fun i => 512 + 512 + 512 + i) = (fun i => 512 * 3 + i) from rfl,
      filter_map_shift512_w18 3 (List.range 512) hall512,
      surv512_range_eq_w18]

set_option maxRecDepth 32768 in
private theorem mod2048_prefix108_counts_cert_w18 :
    survivingMod2048Residues108.length = 108 ∧
    topWeight11Mod2048Residues1 = [2047] ∧
    (survivingMod2048Residues108.filter (isWeightKSurvivingMod2048Bool 10)).length = 9 ∧
    (survivingMod2048Residues108.filter (isWeightKSurvivingMod2048Bool 9)).length = 29 ∧
    (survivingMod2048Residues108.filter (isWeightKSurvivingMod2048Bool 8)).length = 40 ∧
    (survivingMod2048Residues108.filter (isWeightKSurvivingMod2048Bool 7)).length = 24 ∧
    (survivingMod2048Residues108.filter (isWeightKSurvivingMod2048Bool 6)).length = 5 := by
  unfold topWeight11Mod2048Residues1
  rw [survivingMod2048Residues108_eq_w18]
  exact ⟨rfl, by decide, by decide, by decide, by decide, by decide, by decide⟩

/--
  Theorem W18.4a (`markovShift_mod354294_bijection_and_mod2048_prefix108_lift`,
  `zero custom axioms`):
  Complete Mod-`354294` (`2 * 3^11`) Markov Bijection onto `118098` Surviving Classes (`w ≥ 12`),
  Exhaustive Length-`10` Prefix Bound (`∀ r < 1024, w(pref_10) ≤ 10`) + Universal `54/54` Surviving
  `Mod 1024` Length-`≥ 11` Weight-`≤ 11` Escape Theorem + All-Ones `1023` Weight-`11` Escape Witness
  `u_esc11` (`ZPOS_DYADIC_ALLONES10_WEIGHT11_PREFIX_ESCAPE`, Proving ZERO Length-`10` Prefixes Force
  `w(u) ≥ 12`), Exact Length-`11` `Mod 2048` `1 + 9 + 29 + 40 + 24 + 5 = 108` Surviving Prefix Lift
  (`2047` Forces `w(u) ≥ 12` on `|u| ≥ 12`), Mod-`354294` Suffix Locks (`177147`, `59049`, &
  `{59049, 177147, 295245}`), & `3 ^ (w - 12)` (`j = 11`) Multi-Step Fiber Equidistribution
  (`Branch P2.2` & `P5.3`, `W18_H4`).
-/
theorem markovShift_mod354294_bijection_and_mod2048_prefix108_lift :
    ((∀ (w a : Nat), w ≥ 11 -> a < 2 * 3 ^ (w - 1) ->
        markovShiftTrue w a % 354294 = markovShiftTrue 11 (a % 118098) % 354294) ∧
     survivingMod354294List.length = 118098 ∧
     (∀ x1 x2 : Fin 118098,
        markovShiftTrue 11 x1.val % 354294 = markovShiftTrue 11 x2.val % 354294 -> x1 = x2) ∧
     (∀ x : Fin 118098,
        markovShiftTrue 11 x.val % 354294 ∈ survivingMod354294List) ∧
     (∀ r ∈ survivingMod354294List,
        ∃ x : Fin 118098, markovShiftTrue 11 x.val % 354294 = r)) ∧
    ((∀ r : Fin 1024, parityWeight (parityOfIter 10 r.val) ≤ 10) ∧
     (∀ r : Fin 1024, isSurvivingMod1024Bool r.val = true ->
       ∃ u : List Bool,
         u.take 10 = parityOfIter 10 r.val ∧
         u.length ≥ 11 ∧
         parityWeight u ≤ 11 ∧
         IsFirstHitOnePair u 0 ∧
         IsSurvivingMod373248Class (exactBackwardQuotient 1 u 0) ∧
         exactBackwardQuotient 1 u 0 % 1024 = r.val) ∧
     (let u_esc11 : List Bool :=
        List.replicate 10 true ++ List.replicate 446 false ++ [true]
      u_esc11.length = 457 ∧
      parityWeight u_esc11 = 11 ∧
      IsFirstHitOnePair u_esc11 0 ∧
      exactBackwardQuotient 1 u_esc11 0 =
        18045298623953582795729423582265437192090384467670343105690885553942878906000080934174237109098719535103271885410225272309068657920294140666879 ∧
      IsSurvivingMod373248Class (exactBackwardQuotient 1 u_esc11 0) ∧
      exactBackwardQuotient 1 u_esc11 0 % 1024 = 1023 ∧
      exactBackwardQuotient 1 u_esc11 0 % 2048 = 1023) ∧
     survivingMod2048Residues108.length = 108 ∧
     topWeight11Mod2048Residues1 = [2047] ∧
     (survivingMod2048Residues108.filter (isWeightKSurvivingMod2048Bool 10)).length = 9 ∧
     (survivingMod2048Residues108.filter (isWeightKSurvivingMod2048Bool 9)).length = 29 ∧
     (survivingMod2048Residues108.filter (isWeightKSurvivingMod2048Bool 8)).length = 40 ∧
     (survivingMod2048Residues108.filter (isWeightKSurvivingMod2048Bool 7)).length = 24 ∧
     (survivingMod2048Residues108.filter (isWeightKSurvivingMod2048Bool 6)).length = 5 ∧
     (∀ u : List Bool, IsCoreParityWord u -> parityWeight u ≥ 12 ->
        canonicalSuffixShift u 1 % 354294 ∈ survivingMod354294List) ∧
     (∀ (u : List Bool) (q : Nat),
        IsCoreParityWord u -> u.length ≥ 12 ->
        isWeightKSurvivingMod2048Bool 11 (exactBackwardQuotient 1 u q) = true ->
        parityWeight u ≥ 12 ∧ canonicalSuffixShift u 1 % 354294 ∈ survivingMod354294List)) ∧
    ((∀ pref : List Bool,
        canonicalSuffixShift (pref ++ List.replicate 11 true) 1 % 354294 = 59049 ∨
        canonicalSuffixShift (pref ++ List.replicate 11 true) 1 % 354294 = 177147 ∨
        canonicalSuffixShift (pref ++ List.replicate 11 true) 1 % 354294 = 295245) ∧
     (∀ pref : List Bool,
        canonicalSuffixShift (pref ++ List.replicate 12 true) 1 % 354294 = 177147 ∧
        canonicalSuffixShift (pref ++ ([true, false] ++ List.replicate 11 true)) 1 % 354294 = 59049)) ∧
    (∀ (tail : List Bool) (w r0 : Nat),
      w ≥ 12 -> r0 < 354294 ->
      let Mk := 2 * 3 ^ (11 + parityWeight tail)
      let N := 3 ^ (w - 12)
      let base := iterMarkovShift tail w r0 % Mk
      (∀ t : Nat, t < N ->
        ∃ q : Nat, q < N ∧ iterMarkovShift tail w (r0 + 354294 * t) = base + Mk * q) ∧
      (∀ q : Nat, q < N ->
        ∃ t : Nat, t < N ∧
          iterMarkovShift tail w (r0 + 354294 * t) = base + Mk * q ∧
          ∀ t' : Nat, t' < N ->
            iterMarkovShift tail w (r0 + 354294 * t') = base + Mk * q -> t' = t)) := by
  have h118098_eq : (2 : Nat) * 3 ^ (11 - 1) = 118098 := by decide
  have h354294_eq : (2 : Nat) * 3 ^ 11 = 354294 := by decide
  have hcongr354294 : ∀ (w a : Nat), w ≥ 11 -> a < 2 * 3 ^ (w - 1) ->
      markovShiftTrue w a % 354294 = markovShiftTrue 11 (a % 118098) % 354294 := by
    intro w a hw11 ha_lt
    have hr_lt : a % 118098 < 2 * 3 ^ (11 - 1) := by rw [h118098_eq]; exact Nat.mod_lt a (by decide)
    exact markovShiftTrue_contraction_mod_pow3 10 w 11 a (a % 118098)
      (by omega) (by decide) ha_lt hr_lt (by simp)
  have hlen354294 : survivingMod354294List.length = 118098 := by
    unfold survivingMod354294List
    have h := range_six_mul_surviving_len_w18 59049
    rwa [show 6 * 59049 = 354294 by decide, show 2 * 59049 = 118098 by decide] at h
  have hinj118098 : ∀ x1 x2 : Fin 118098,
      markovShiftTrue 11 x1.val % 354294 = markovShiftTrue 11 x2.val % 354294 -> x1 = x2 := by
    intro x1 x2 heq
    have hx1 : x1.val < 2 * 3 ^ (11 - 1) := by rw [h118098_eq]; exact x1.isLt
    have hx2 : x2.val < 2 * 3 ^ (11 - 1) := by rw [h118098_eq]; exact x2.isLt
    have hm1_lt : markovShiftTrue 11 x1.val < 354294 := by
      rw [← h354294_eq]
      exact (canonicalSuffixShift_markov_bijection_and_mod6_lock.2.1 11 x1.val (by decide) hx1).1
    have hm2_lt : markovShiftTrue 11 x2.val < 354294 := by
      rw [← h354294_eq]
      exact (canonicalSuffixShift_markov_bijection_and_mod6_lock.2.1 11 x2.val (by decide) hx2).1
    rw [Nat.mod_eq_of_lt hm1_lt, Nat.mod_eq_of_lt hm2_lt] at heq
    exact Fin.ext (canonicalSuffixShift_markov_bijection_and_mod6_lock.2.2.1 11 x1.val x2.val
      (by decide) hx1 hx2 heq)
  have hmem118098 : ∀ x : Fin 118098, markovShiftTrue 11 x.val % 354294 ∈ survivingMod354294List := by
    intro x
    have hx : x.val < 2 * 3 ^ (11 - 1) := by rw [h118098_eq]; exact x.isLt
    rcases canonicalSuffixShift_markov_bijection_and_mod6_lock.2.1 11 x.val (by decide) hx with
      ⟨hlt, hm6⟩
    rw [h354294_eq] at hlt
    rw [Nat.mod_eq_of_lt hlt]
    exact (mem_survivingMod354294List_iff_w18 _).mpr ⟨hlt, hm6⟩
  have hsurj118098 : ∀ r ∈ survivingMod354294List,
      ∃ x : Fin 118098, markovShiftTrue 11 x.val % 354294 = r := by
    intro r hr
    rcases (mem_survivingMod354294List_iff_w18 r).mp hr with ⟨hr_lt, hr_m6⟩
    rcases canonicalSuffixShift_markov_bijection_and_mod6_lock.2.2.2.1 11 r (by decide)
      (by rw [h354294_eq]; exact hr_lt) hr_m6 with ⟨a, ha_lt, ha_eq⟩
    rw [h118098_eq] at ha_lt
    refine ⟨⟨a, ha_lt⟩, ?_⟩
    dsimp only
    rw [ha_eq, Nat.mod_eq_of_lt hr_lt]
  have hconf12 : ∀ u : List Bool, IsCoreParityWord u -> parityWeight u ≥ 12 ->
      canonicalSuffixShift u 1 % 354294 ∈ survivingMod354294List := by
    intro u hu hw12
    rcases list_eq_append_true_of_reverse_head u hu.2 with ⟨v, rfl⟩
    have hw_v : parityWeight v ≥ 11 := by
      rw [parityWeight_append] at hw12
      have h1 : parityWeight [true] = 1 := rfl
      rw [h1] at hw12; omega
    have hrec : canonicalSuffixShift (v ++ [true]) 1 =
        markovShiftTrue (parityWeight v) (canonicalSuffixShift v 1) :=
      (canonicalSuffixShift_append_markov_recurrence.2.2 v (by omega)).2.2.1
    have ha_lt := (canonicalSuffixShift_spec_unique v 1 (by omega) (by decide)).1
    rw [hrec, hcongr354294 (parityWeight v) (canonicalSuffixShift v 1) hw_v ha_lt]
    exact hmem118098 ⟨canonicalSuffixShift v 1 % 118098, Nat.mod_lt _ (by decide)⟩
  have hpref10_le10 : ∀ r : Fin 1024, parityWeight (parityOfIter 10 r.val) ≤ 10 := by
    have hle_len : ∀ xs : List Bool, parityWeight xs ≤ xs.length := by
      intro xs; induction xs with
      | nil => exact Nat.le_refl 0
      | cons b tl ih =>
        cases b <;> (simp only [parityWeight, List.length_cons]; omega)
    intro r
    exact Nat.le_trans (hle_len _) (by rw [parityOfIter_length]; exact Nat.le_refl 10)
  have hlen12_top11 : ∀ (u : List Bool) (q : Nat),
      IsCoreParityWord u -> u.length ≥ 12 ->
      isWeightKSurvivingMod2048Bool 11 (exactBackwardQuotient 1 u q) = true ->
      parityWeight u ≥ 12 ∧ canonicalSuffixShift u 1 % 354294 ∈ survivingMod354294List := by
    intro u q hu hlen12 htop
    rcases list_eq_append_true_of_reverse_head u hu.2 with ⟨pre, rfl⟩
    have hpre_ge11 : pre.length ≥ 11 := by
      rw [List.length_append, List.length_singleton] at hlen12; omega
    let p11 := pre.take 11
    let fb := pre.drop 11
    have hp11_len : p11.length = 11 := take_len_of_ge_w18 11 pre hpre_ge11
    have hpre_sp : p11 ++ fb = pre := take_drop_split_eq_w18 11 pre
    have hu' : IsCoreParityWord (p11 ++ fb ++ [true]) := by rwa [hpre_sp]
    have hp11_eq : parityOfIter 11 (exactBackwardQuotient 1 (p11 ++ fb ++ [true]) q % 2048) = p11 :=
      len12_core_mod2048_prefix11_w18 p11 fb q hp11_len hu'
    rw [hpre_sp] at hp11_eq
    unfold isWeightKSurvivingMod2048Bool at htop
    simp only [Bool.and_eq_true, decide_eq_true_eq] at htop
    have htop2 := htop.2
    have hw_p11 : parityWeight p11 = 11 := by rwa [hp11_eq] at htop2
    have hw12 : parityWeight (pre ++ [true]) ≥ 12 := by
      rw [← hpre_sp, parityWeight_append, parityWeight_append]
      have h1 : parityWeight [true] = 1 := rfl
      rw [h1]; omega
    exact ⟨hw12, hconf12 (pre ++ [true]) hu hw12⟩
  rcases mod2048_prefix108_counts_cert_w18 with ⟨hc108, htop1, hc10, hc9, hc8, hc7, hc6⟩
  refine ⟨⟨hcongr354294, hlen354294, hinj118098, hmem118098, hsurj118098⟩,
          ⟨hpref10_le10, len10_all54_surviving_escape_sound, esc11_allones10_cert_w18,
           hc108, htop1, hc10, hc9, hc8, hc7, hc6, hconf12, hlen12_top11⟩, ⟨?_, ?_⟩, ?_⟩
  · intro pref
    have hm118098 := first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.1 11 pref (by decide)
    change canonicalSuffixShift (pref ++ List.replicate 11 true) 1 % 118098 = 59049 at hm118098
    let A := canonicalSuffixShift (pref ++ List.replicate 11 true) 1 % 354294
    have hA_lt : A < 354294 := Nat.mod_lt _ (by decide)
    have hA_m118098 : A % 118098 = 59049 := by
      dsimp only [A]
      rw [Nat.mod_mod_of_dvd _ ⟨3, by decide⟩]
      exact hm118098
    have hdm := (Nat.div_add_mod A 118098).symm
    change A = 59049 ∨ A = 177147 ∨ A = 295245
    omega
  · intro pref
    have ha1 := first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.1 12 pref (by decide)
    let u13 : List Bool := [true, false] ++ List.replicate 11 true
    have ha2 := canonicalSuffixShift_mod18_and_pow3_memory_annihilation.2.1 11 pref u13 (by decide)
    have hu13_sh : canonicalSuffixShift u13 1 = 59049 := by
      rcases canonicalSuffixShift_spec_unique u13 1 (by decide) (by decide) with ⟨_, _, huniq⟩
      symm
      apply huniq 59049 (by decide)
      have hlen13 : u13.length = 13 := rfl
      have hwt12 : parityWeight u13 = 12 := rfl
      rw [Nat.mul_one, hlen13, hwt12, show (3 : Nat) ^ 12 = 531441 from rfl,
          show 13 + 59049 = 13 + (81 * 81) * 9 from rfl,
          Nat.pow_add 2 13 ((81 * 81) * 9),
          ← pow_pow_eq_mul_w5 2 (81 * 81) 9,
          ← pow_pow_eq_mul_w5 2 81 81,
          Nat.mul_mod,
          pow_mod_eq_pow_mod_w18 ((2 ^ 81) ^ 81) 531441 9,
          pow_mod_eq_pow_mod_w18 (2 ^ 81) 531441 81]
      decide
    have hv2 : canonicalSuffixShift u13 1 % 354294 = 59049 := by rw [hu13_sh]
    exact ⟨by simpa using ha1, by simpa [u13] using ha2.trans hv2⟩
  · intro tail w r0 hw12 hr0
    have hm354294 : (2 : Nat) * 3 ^ 11 = 354294 := by decide
    have hw_sub : w - 1 - 11 = w - 12 := by omega
    have heq := markovShift_mod18_bijection_and_multistep_fiber_equidistribution.2.2
      tail 11 w r0 (by omega) (by rw [hm354294]; exact hr0)
    dsimp only at heq ⊢
    rwa [hm354294, hw_sub] at heq


-- ----------------------------------------------------------------------------
-- Section 3B: Choice-Free 3-Step `Mod 81` Span-`≤ 14` Stall Obstruction vs
--             Normalized `162`-State 4-Step `Mod 243` Ternary-Carry
--             Macro-Selector (`W18_H4`, `[choice-free]`)
-- ----------------------------------------------------------------------------

/-- Normalized 3-step `Mod 81` (`2^54 ≡ 1 (mod 81)`) ternary-carry branch validity in span `≤ 14`. -/
def validTriple81NormBool (u81 : Nat) (t : Nat × Nat × Nat) : Bool :=
  let s1 := t.1
  let s2 := t.2.1
  let s3 := t.2.2
  let d1 := (u81 + 81 - (2 ^ ((54 - s1) % 54)) % 81) % 81
  let r1 := (d1 / 3) % 27
  let d2 := (r1 + 27 - (2 ^ ((54 - s1 - s2) % 54)) % 27) % 27
  let r2 := (d2 / 3) % 9
  let d3 := (r2 + 9 - (2 ^ ((54 - s1 - s2 - s3) % 54)) % 9) % 9
  decide (1 ≤ s1 ∧ 1 ≤ s2 ∧ 1 ≤ s3 ∧ s1 + s2 + s3 ≤ 14) &&
  (d1 % 3 == 0) && (r1 % 3 != 0) &&
  (d2 % 3 == 0) && (r2 % 3 != 0) &&
  (d3 == 3 || d3 == 6)

/-- Complete `7`-element list (`7 < 8 = 2^3`) of valid 3-step `Mod 81` triples at `u_norm = 79` in span `≤ 14`. -/
def validTriples81Span14At79 : List (Nat × Nat × Nat) :=
  [(4, 4, 2), (4, 4, 6), (4, 6, 1), (6, 1, 4), (6, 1, 6), (6, 3, 1), (6, 3, 3)]

private def memValid79BoolW18 (s1 s2 s3 : Nat) : Bool :=
  (s1 == 4 && s2 == 4 && s3 == 2) ||
  (s1 == 4 && s2 == 4 && s3 == 6) ||
  (s1 == 4 && s2 == 6 && s3 == 1) ||
  (s1 == 6 && s2 == 1 && s3 == 4) ||
  (s1 == 6 && s2 == 1 && s3 == 6) ||
  (s1 == 6 && s2 == 3 && s3 == 1) ||
  (s1 == 6 && s2 == 3 && s3 == 3)

private theorem memValid79BoolW18_iff (s1 s2 s3 : Nat) :
    memValid79BoolW18 s1 s2 s3 = true ↔ (s1, s2, s3) ∈ validTriples81Span14At79 := by
  unfold memValid79BoolW18 validTriples81Span14At79
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.mem_cons, List.not_mem_nil,
             Prod.mk.injEq, or_false]
  constructor
  · intro h
    rcases h with (((((h1 | h2) | h3) | h4) | h5) | h6) | h7
    · exact Or.inl ⟨h1.1.1, h1.1.2, h1.2⟩
    · exact Or.inr (Or.inl ⟨h2.1.1, h2.1.2, h2.2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h3.1.1, h3.1.2, h3.2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h4.1.1, h4.1.2, h4.2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h5.1.1, h5.1.2, h5.2⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h6.1.1, h6.1.2, h6.2⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h7.1.1, h7.1.2, h7.2⟩)))))
  · intro h
    rcases h with h1 | h2 | h3 | h4 | h5 | h6 | h7
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨⟨h1.1, h1.2.1⟩, h1.2.2⟩)))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨h2.1, h2.2.1⟩, h2.2.2⟩)))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨h3.1, h3.2.1⟩, h3.2.2⟩))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨h4.1, h4.2.1⟩, h4.2.2⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨⟨h5.1, h5.2.1⟩, h5.2.2⟩))
    · exact Or.inl (Or.inr ⟨⟨h6.1, h6.2.1⟩, h6.2.2⟩)
    · exact Or.inr ⟨⟨h7.1, h7.2.1⟩, h7.2.2⟩

private def check81At79CW18 (s1 s2 : Nat) : Nat -> Bool
  | 0 => validTriple81NormBool 79 (s1, s2, 0) == memValid79BoolW18 s1 s2 0
  | c + 1 =>
    (validTriple81NormBool 79 (s1, s2, c + 1) == memValid79BoolW18 s1 s2 (c + 1)) &&
      check81At79CW18 s1 s2 c

private theorem check81At79CW18_get (s1 s2 : Nat) :
    ∀ (top c : Nat), check81At79CW18 s1 s2 top = true -> c ≤ top ->
      validTriple81NormBool 79 (s1, s2, c) = memValid79BoolW18 s1 s2 c
  | 0, c, h, hc => by
    have hc0 : c = 0 := by omega
    subst hc0; exact beq_iff_eq.mp h
  | top + 1, c, h, hc => by
    rcases Bool.and_eq_true_iff.mp h with ⟨heq_b, htl⟩
    if hct : c = top + 1 then
      subst hct; exact beq_iff_eq.mp heq_b
    else
      exact check81At79CW18_get s1 s2 top c htl (by omega)

private def check81At79BCW18 (s1 : Nat) : Nat -> Bool
  | 0 => check81At79CW18 s1 0 14
  | b + 1 => check81At79CW18 s1 (b + 1) 14 && check81At79BCW18 s1 b

private theorem check81At79BCW18_get (s1 : Nat) :
    ∀ (top b c : Nat), check81At79BCW18 s1 top = true -> b ≤ top -> c ≤ 14 ->
      validTriple81NormBool 79 (s1, b, c) = memValid79BoolW18 s1 b c
  | 0, b, c, h, hb, hc => by
    have hb0 : b = 0 := by omega
    subst hb0; exact check81At79CW18_get s1 0 14 c h hc
  | top + 1, b, c, h, hb, hc => by
    rcases Bool.and_eq_true_iff.mp h with ⟨hhd, htl⟩
    if hbt : b = top + 1 then
      subst hbt; exact check81At79CW18_get s1 (top + 1) 14 c hhd hc
    else
      exact check81At79BCW18_get s1 top b c htl (by omega) hc

private def check81At79ABCW18 : Nat -> Bool
  | 0 => check81At79BCW18 0 14
  | a + 1 => check81At79BCW18 (a + 1) 14 && check81At79ABCW18 a

private theorem check81At79ABCW18_get :
    ∀ (top a b c : Nat), check81At79ABCW18 top = true -> a ≤ top -> b ≤ 14 -> c ≤ 14 ->
      validTriple81NormBool 79 (a, b, c) = memValid79BoolW18 a b c
  | 0, a, b, c, h, ha, hb, hc => by
    have ha0 : a = 0 := by omega
    subst ha0; exact check81At79BCW18_get 0 14 b c h hb hc
  | top + 1, a, b, c, h, ha, hb, hc => by
    rcases Bool.and_eq_true_iff.mp h with ⟨hhd, htl⟩
    if hat : a = top + 1 then
      subst hat; exact check81At79BCW18_get (top + 1) 14 b c hhd hb hc
    else
      exact check81At79ABCW18_get top a b c htl (by omega) hb hc

private theorem check81At79_cert_w18 : check81At79ABCW18 14 = true := by decide

private theorem mod81_at79_fin15_iff_cf_w18 (a b c : Fin 15) :
    validTriple81NormBool 79 (a.val, b.val, c.val) = true ↔
      (a.val, b.val, c.val) ∈ validTriples81Span14At79 := by
  have heq := check81At79ABCW18_get 14 a.val b.val c.val check81At79_cert_w18
    (by have := a.isLt; omega) (by have := b.isLt; omega) (by have := c.isLt; omega)
  rw [heq]
  exact memValid79BoolW18_iff a.val b.val c.val

private theorem mod81_at79_all_iff_cf_w18 (s1 s2 s3 : Nat) :
    validTriple81NormBool 79 (s1, s2, s3) = true ↔
      (s1, s2, s3) ∈ validTriples81Span14At79 := by
  if hs1 : s1 < 15 then
    if hs2 : s2 < 15 then
      if hs3 : s3 < 15 then
        exact mod81_at79_fin15_iff_cf_w18 ⟨s1, hs1⟩ ⟨s2, hs2⟩ ⟨s3, hs3⟩
      else
        constructor
        · intro hv
          unfold validTriple81NormBool at hv
          dsimp only at hv
          rcases Bool.and_eq_true_iff.mp hv with ⟨h1, _⟩
          rcases Bool.and_eq_true_iff.mp h1 with ⟨h2, _⟩
          rcases Bool.and_eq_true_iff.mp h2 with ⟨h3, _⟩
          rcases Bool.and_eq_true_iff.mp h3 with ⟨h4, _⟩
          rcases Bool.and_eq_true_iff.mp h4 with ⟨hbds, _⟩
          have hb := of_decide_eq_true hbds
          exact False.elim (by omega)
        · intro hm
          unfold validTriples81Span14At79 at hm
          simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at hm
          rcases hm with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ |
            ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> exact False.elim (by omega)
    else
      constructor
      · intro hv
        unfold validTriple81NormBool at hv
        dsimp only at hv
        rcases Bool.and_eq_true_iff.mp hv with ⟨h1, _⟩
        rcases Bool.and_eq_true_iff.mp h1 with ⟨h2, _⟩
        rcases Bool.and_eq_true_iff.mp h2 with ⟨h3, _⟩
        rcases Bool.and_eq_true_iff.mp h3 with ⟨h4, _⟩
        rcases Bool.and_eq_true_iff.mp h4 with ⟨hbds, _⟩
        have hb := of_decide_eq_true hbds
        exact False.elim (by omega)
      · intro hm
        unfold validTriples81Span14At79 at hm
        simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at hm
        rcases hm with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ |
          ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> exact False.elim (by omega)
  else
    constructor
    · intro hv
      unfold validTriple81NormBool at hv
      dsimp only at hv
      rcases Bool.and_eq_true_iff.mp hv with ⟨h1, _⟩
      rcases Bool.and_eq_true_iff.mp h1 with ⟨h2, _⟩
      rcases Bool.and_eq_true_iff.mp h2 with ⟨h3, _⟩
      rcases Bool.and_eq_true_iff.mp h3 with ⟨h4, _⟩
      rcases Bool.and_eq_true_iff.mp h4 with ⟨hbds, _⟩
      have hb := of_decide_eq_true hbds
      exact False.elim (by omega)
    · intro hm
      unfold validTriples81Span14At79 at hm
      simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at hm
      rcases hm with ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ |
        ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ <;> exact False.elim (by omega)

-- Choice-free list/pigeonhole helpers:

private def eraseAllNatCFW18 (b : Nat) : List Nat -> List Nat
  | [] => []
  | x :: xs => if x = b then eraseAllNatCFW18 b xs else x :: eraseAllNatCFW18 b xs

private theorem mem_eraseAllNatCFW18_iff (b : Nat) :
    ∀ (xs : List Nat) (v : Nat), v ∈ eraseAllNatCFW18 b xs ↔ (v ∈ xs ∧ v ≠ b)
  | [], _ => by simp [eraseAllNatCFW18]
  | x :: xs, v => by
    simp only [eraseAllNatCFW18]
    if hxb : x = b then
      simp only [hxb, ite_true, mem_eraseAllNatCFW18_iff b xs v, List.mem_cons]
      exact ⟨fun ⟨hm, hne⟩ => ⟨Or.inr hm, hne⟩,
             fun ⟨h, hne⟩ => ⟨by rcases h with rfl | hm; { exact False.elim (hne rfl) }; exact hm, hne⟩⟩
    else
      simp only [hxb, ite_false, List.mem_cons, mem_eraseAllNatCFW18_iff b xs v]
      exact ⟨fun h => by rcases h with rfl | ⟨hm, hne⟩; { exact ⟨Or.inl rfl, hxb⟩ }; exact ⟨Or.inr hm, hne⟩,
             fun ⟨h, hne⟩ => by rcases h with rfl | hm; { exact Or.inl rfl }; exact Or.inr ⟨hm, hne⟩⟩

private theorem eraseAllNatCFW18_of_not_mem (b : Nat) :
    ∀ (xs : List Nat), b ∉ xs -> eraseAllNatCFW18 b xs = xs
  | [], _ => rfl
  | x :: xs, hnm => by
    have hxb : x ≠ b := fun h => hnm (h ▸ List.Mem.head _)
    have hnm_xs : b ∉ xs := fun hm => hnm (List.mem_cons_of_mem _ hm)
    simp only [eraseAllNatCFW18, hxb, ite_false, eraseAllNatCFW18_of_not_mem b xs hnm_xs]

private theorem nodup_eraseAllNatCFW18_and_len (b : Nat) :
    ∀ (xs : List Nat),
      NoDupNat xs -> NoDupNat (eraseAllNatCFW18 b xs) ∧ xs.length ≤ (eraseAllNatCFW18 b xs).length + 1
  | [], _ => ⟨NoDupNat.nil, by simp [eraseAllNatCFW18]⟩
  | x :: xs, NoDupNat.cons _ _ hnx hnd => by
    if hxb : x = b then
      subst hxb
      simp only [eraseAllNatCFW18, ite_true, eraseAllNatCFW18_of_not_mem x xs hnx, List.length_cons]
      exact ⟨hnd, Nat.le_refl _⟩
    else
      rcases nodup_eraseAllNatCFW18_and_len b xs hnd with ⟨hnd_er, hlen_er⟩
      simp only [eraseAllNatCFW18, hxb, ite_false, List.length_cons]
      have hnx_er : x ∉ eraseAllNatCFW18 b xs :=
        fun hm => hnx ((mem_eraseAllNatCFW18_iff b xs x).mp hm).1
      exact ⟨NoDupNat.cons x _ hnx_er hnd_er, by omega⟩

private theorem noDupNat_length_le_of_subset_cf_w18 :
    ∀ (cands xs : List Nat),
      NoDupNat xs -> (∀ y ∈ xs, y ∈ cands) -> xs.length ≤ cands.length
  | [], [], _, _ => Nat.le_refl 0
  | [], x :: _, _, hsub => False.elim (by cases hsub x (List.Mem.head _))
  | b :: bs, xs, hnd, hsub => by
    rcases nodup_eraseAllNatCFW18_and_len b xs hnd with ⟨hnd', hlen'⟩
    have hsub' : ∀ y ∈ eraseAllNatCFW18 b xs, y ∈ bs := by
      intro y hy
      rcases (mem_eraseAllNatCFW18_iff b xs y).mp hy with ⟨hy_xs, hne⟩
      rcases List.mem_cons.mp (hsub y hy_xs) with rfl | hbs
      · exact False.elim (hne rfl)
      · exact hbs
    have ih := noDupNat_length_le_of_subset_cf_w18 bs (eraseAllNatCFW18 b xs) hnd' hsub'
    simp only [List.length_cons]; omega

private theorem noDupNat_map_inj_on_cf_w18 (f : Nat -> Nat) :
    ∀ (js : List Nat),
      NoDupNat js ->
      (∀ a ∈ js, ∀ b ∈ js, f a = f b -> a = b) ->
      NoDupNat (js.map f)
  | [], _, _ => NoDupNat.nil
  | j :: js, NoDupNat.cons _ _ hnj hnd, hinj => by
    refine NoDupNat.cons (f j) (js.map f) ?_
      (noDupNat_map_inj_on_cf_w18 f js hnd (fun a ha b hb =>
        hinj a (List.mem_cons_of_mem j ha) b (List.mem_cons_of_mem j hb)))
    intro hm
    rcases List.mem_map.mp hm with ⟨j', hj', heq⟩
    have hj_eq := hinj j' (List.mem_cons_of_mem j hj') j (List.Mem.head _) heq
    exact hnj (hj_eq ▸ hj')

private def packTripleW18 (t : Nat × Nat × Nat) : Nat :=
  t.1 * 65536 + t.2.1 * 256 + t.2.2

private theorem packTripleW18_inj_le14 (t1 t2 : Nat × Nat × Nat)
    (hb1 : t1.1 ≤ 14 ∧ t1.2.1 ≤ 14 ∧ t1.2.2 ≤ 14)
    (hb2 : t2.1 ≤ 14 ∧ t2.2.1 ≤ 14 ∧ t2.2.2 ≤ 14)
    (heq : packTripleW18 t1 = packTripleW18 t2) : t1 = t2 := by
  rcases t1 with ⟨a1, b1, c1⟩
  rcases t2 with ⟨a2, b2, c2⟩
  unfold packTripleW18 at heq
  dsimp only at hb1 hb2 heq
  have ha : a1 = a2 := by omega
  have hb : b1 = b2 := by omega
  have hc : c1 = c2 := by omega
  rw [ha, hb, hc]

private theorem mod81_at79_no_8branch_selector_cf_w18
    (f : Fin 8 -> Nat × Nat × Nat)
    (hval : ∀ b : Fin 8, validTriple81NormBool 79 (f b) = true) :
    ¬ (∀ b1 b2 : Fin 8, f b1 = f b2 -> b1 = b2) := by
  intro hinj
  let idxs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]
  have hnd_idxs : NoDupNat idxs := by
    repeat (first | exact NoDupNat.nil | refine NoDupNat.cons _ _ (by decide) ?_)
  let g : Nat -> Nat := fun i => packTripleW18 (f ⟨i % 8, Nat.mod_lt i (by decide)⟩)
  have hbds_f : ∀ b : Fin 8, (f b).1 ≤ 14 ∧ (f b).2.1 ≤ 14 ∧ (f b).2.2 ≤ 14 := by
    intro b
    have hv := hval b
    unfold validTriple81NormBool at hv
    dsimp only at hv
    rcases Bool.and_eq_true_iff.mp hv with ⟨h1, _⟩
    rcases Bool.and_eq_true_iff.mp h1 with ⟨h2, _⟩
    rcases Bool.and_eq_true_iff.mp h2 with ⟨h3, _⟩
    rcases Bool.and_eq_true_iff.mp h3 with ⟨h4, _⟩
    rcases Bool.and_eq_true_iff.mp h4 with ⟨hbds, _⟩
    have hb := of_decide_eq_true hbds
    exact ⟨by omega, by omega, by omega⟩
  have hnd_map : NoDupNat (idxs.map g) := by
    apply noDupNat_map_inj_on_cf_w18 g idxs hnd_idxs
    intro a ha b hb heq
    have ha8 : a < 8 := by simp [idxs] at ha; omega
    have hb8 : b < 8 := by simp [idxs] at hb; omega
    dsimp only [g] at heq
    have hfa : (⟨a % 8, Nat.mod_lt a (by decide)⟩ : Fin 8) = ⟨a, ha8⟩ := Fin.ext (Nat.mod_eq_of_lt ha8)
    have hfb : (⟨b % 8, Nat.mod_lt b (by decide)⟩ : Fin 8) = ⟨b, hb8⟩ := Fin.ext (Nat.mod_eq_of_lt hb8)
    rw [hfa, hfb] at heq
    have hf_eq := packTripleW18_inj_le14 _ _ (hbds_f ⟨a, ha8⟩) (hbds_f ⟨b, hb8⟩) heq
    exact congrArg Fin.val (hinj ⟨a, ha8⟩ ⟨b, hb8⟩ hf_eq)
  let cands := validTriples81Span14At79.map packTripleW18
  have hsub : ∀ y ∈ idxs.map g, y ∈ cands := by
    intro y hy
    rcases List.mem_map.mp hy with ⟨i, _, rfl⟩
    dsimp only [g, cands]
    apply List.mem_map_of_mem
    rcases hfp : f ⟨i % 8, Nat.mod_lt i (by decide)⟩ with ⟨s1, s2, s3⟩
    exact (mod81_at79_all_iff_cf_w18 s1 s2 s3).mp (hfp ▸ hval ⟨i % 8, Nat.mod_lt i (by decide)⟩)
  have hle := noDupNat_length_le_of_subset_cf_w18 cands (idxs.map g) hnd_map hsub
  have hlen_l : (idxs.map g).length = 8 := rfl
  have hlen_r : cands.length = 7 := rfl
  rw [hlen_l, hlen_r] at hle
  omega

-- Normalized `162`-state 4-step `Mod 243` macro-selector (`chooseFourStepTernaryCarry243`):

private def listNatAtW18 : List Nat -> Nat -> Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, k + 1 => listNatAtW18 xs k

private def listRowAtW18 : List (List Nat) -> Nat -> List Nat
  | [], _ => []
  | r :: _, 0 => r
  | _ :: rs, k + 1 => listRowAtW18 rs k

private def unpackQuadW18 (p : Nat) : Nat × Nat × Nat × Nat :=
  (p / 16777216, (p / 65536) % 256, (p / 256) % 256, p % 256)

private def packQuadW18 (q : Nat × Nat × Nat × Nat) : Nat :=
  q.1 * 16777216 + q.2.1 * 65536 + q.2.2.1 * 256 + q.2.2.2

private theorem packQuad_unpackQuad_cf_w18 (p : Nat) :
    packQuadW18 (unpackQuadW18 p) = p := by
  unfold packQuadW18 unpackQuadW18
  dsimp only
  omega

private def uIdxOf243W18 (u : Nat) : Nat :=
  (u / 3) * 2 + (u % 3 - 1)

private def uNormOfIdxW18 (idx : Nat) : Nat :=
  (idx / 2) * 3 + (idx % 2 + 1)

private def uNorm243W18 (rem243 exp162 : Nat) : Nat :=
  ((rem243 % 243) * (2 ^ ((162 - exp162 % 162) % 162))) % 243

private def unpackQuadsBigW18 : Nat -> Nat -> List Nat
  | 0, _ => []
  | c + 1, big => (big % 4294967296) :: unpackQuadsBigW18 c (big / 4294967296)

private def unpackRow81W18 (t : Nat × Nat × Nat) : List Nat :=
  unpackQuadsBigW18 27 t.1 ++ unpackQuadsBigW18 27 t.2.1 ++ unpackQuadsBigW18 27 t.2.2


private def mod243NormBlock0 : List (List Nat) :=
  ([
    105570864819614962943296319607612077225663731528345761270261778589812949221591665852382375084058854053505689117453598587104854537168996913844340490633730,
    53196608837585259206234780630157689160394716117260670637543196352800214242629909317867489880451433498483791591031808499925484905787902390628584593162756,
    106592984608258879594099055768393973464345931388687290666628098660915954592466352356302070721403960988533264956232298128010137638987952981070548606059009,
    262076644114524014356280799688230331574959175459355030814974045688263134976945012844274018020376855784219782108399026019585662359865985290632034917679363,
    314860876236068468822056546762344543016562129864908147376233079756727104121066074543013900546854567146846372274934972638632343009575487368679309963297281,
    53402787842387435473222062830949981220284811454631743666026232674834434228447295710985282621473135712893757355857734873562397932901135508749067198071301,
    106386006436017613833972109134886314822945211273373023882693316792268486040577535132072239429804166454960450894911115925400233010043108365800313970622723,
    54421720325761481676472644452622640863947096136396772091629476511550042834939635383044065184765130418982954472779233444130853778555401881771123920863746,
    105774633834535365637552385365451494777058733869946728400531973659789636359572236107340060135241855052298664673941816915500270971846974654893624328782084,
    159169423757041060760167624362470232479496751901710638733486335866137171713384959339800356470921834419898894585774106472016187669436012554336829442228737,
    314452485968872130492981552769158702947188056395414104721454721196727910255232815774582152160602338632850986556585044288354877171832748655939188970095362,
    52990436076280186478586943836303064166275339468944137214530727112880863224598683981577981341158030160006495661573152954951255505235377582720176183378946,
    209703199811172429991081390039158692192346785318889184389219447697468324446489059077380527033694132619497964704079865275021058377770127886898490685785092,
    54011750453893577333077950278457628049412336126893080797013227130512615194605126521810462608320168714045461261477269594130246308666597276162588915400967,
    105366259176082149570587275717549057636535641657441189428826438889670814831248792557679521388478020673999319453754806263075784350208610482150678860988932,
    262077465158447786862214322012779747189096329638845920739573025283247722912175629986682878702862155597395859276685642299310010822811692295869987989750274,
    314860080190187951452086106621575121581796406498259833576809074708164714932796936156289927848236174959953789587168558238854059199425924594624367111177218,
    53398801369487753778047732709660188765449989369268803711154344017719034600323908566491199768747711147554003728603139349381782025153885611150351100084486,
    105572444424381423562204123160647551071820730904347700662660514350463329826669192772990330442068023424150852239040225694191071402743437075556326875202051,
    53195010502327125276785387932641424476183572856434747148364014898397615114620250459629352462006088561981366835826030110343470166898726801065149135455236,
    106591395638436374811027845762293638117257369626038740788687323798945002045608731600873906359135550950506250194820388166734212421330699865415498659463682,
    262076647236272936086861145955718304022885669128922607831111353223334956992542089618731598532588715209326131585623087384678210038436601551242015023432450,
    314864057297841611505867491196604774869629243494496758972598845099878653819921779608596122936273676375726074049514812480749810942961076696579021218120708,
    53402784720638146689085860297593663815132509576751294012705634531104445534895656788610078995985443897502580896653743340676919164815500026561487956018178,
    105979226991073977746292418267820167954840428414385339191787303441334110313284553333633988259437130520056894370775765243360427812288523560669407135006980,
    54421729691196366539997321057517218518420608204038314276577786076336344062081753128006943801901692244854396221164917155034519594871903837844102638208004,
    106181413279385033107600242991290081067055447342146104597710710318165799536495958695966560688366787645932467428275334344965948602745108604824022859972869
  ]).map (unpackQuadsBigW18 16)

private def mod243NormBlock1 : List (List Nat) :=
  ([
    158761045976744396132872127737636420980135090623408337828190125832078165508851401941108320093690986011305434126873053595714411617177198071277342865621506,
    314450912607602769052380763049643231394281597532419380930947197952518653613011003705234848550060295925012728601856343334421605335648202289945383220150531,
    52990439198028737521417899682732478833972311305287412338692635754958488230495289658365367894330696969944841562044192388960706198570720532439412819165700,
    209703190422061909005736978854415532152288302917680198140557517884038748653289539955609284588156156028650908580859280223032880108684231774126132571668994,
    53608173923057645407469111107717904313748352911248719213230964216117183136003694503091845260924613114993137363060481311514544390984478462713005793739522,
    105364679571315684590647125713950888538990129372269525818453163398700296676059625807578327236518325335145466297752621787900459719052799571956513554629634,
    262080636854974908637160130180402435645091230222473568889323102643834119638451000864441538714936519648395526563995886179610798638192140396842611099567106,
    314458080142274852782684404530327376579652255834589949883793213021680797134545226888459461615434168973191782144614532690520485942213773376913803120476676,
    53398810734733406906584399596317738564823412792218457083072241882256959184779143026485637427506726621337331628445459484002147303005182826359165420634884,
    105572447546129603917285602278561209893833794098156929970060587017319812535203650099195648953884504665089264654684688420947522641566181785738920079787010,
    53196599472338871243791564263281349288164696502836467631166696430492515597695684642206595348446080097449194053752338252627560971099111114813600107201027,
    106591392516498219164899775618643977374732277759491348335965114553932191092105456335116311263196471920614426987715600219488697512218794818887825966171138,
    158761848266216167375117678800616801446476276531867623303337407944014242029902897361933859403428787922471080361872846089174943268098165480941552631152898,
    314860860603270308613647528182038982263364152167604387409517839187433945150930736332628736899857384596769138746158059270962119365994523632607398342033922,
    53401201994123505715096577965105187167569734284839978401981453929548887884635782573350247629595926257344449290406688511313075617858098819091231018254850,
    106386015801263265508809491979557392290824707709505352224039044881882168621969748924839974058407962355812742954801032662986707500063614724779953468080898,
    54423321782767422365899314125887083406251934145181507798347774000651893255510469077269943266941033192372025129185388052218358719677054886317439133680129,
    105777830505051630589096102486205021502829378483668745016971050230971520456242069613961328572385421201204571706271925025258127406350329107631376143811330,
    158761055342179280996396804342530998634608602691049880013138435396864466735993519686071198710827547837176875875258737306618077433493700027350321582965764,
    314452495310063297345744931219743599729513178345028484663077854721096757286448524078847401762203098026760711923145437406785622583862380599975965976822020,
    52992012559297729727946660926485299524212034486365844634112281046958494317075127308121922371432699853541142768636739701399711838136142100894016350519813,
    209704788757319670066898670717149290543792178809707537724614907240208967898579842527350176249964241621283670853574512522317905615548623900997676314132995,
    53604971009043908409352643722944604718964736626440945532251648999525575022616352828307932680778927256137424846894906839708492052536076560140514856403204,
    105367857511340280592681771571098376151023723364111699318623433905081612087155387965484410789100526565155671078156851687549508130096605197507848742961669,
    262080646220221299506958244406627649756133459168238074047614230183724807414498106160810939784153347243216204048775198198885295846372555849877532692447745,
    314861666038451882663889040078638770726507044821858408654379546429393819294211297729074294497897105106939885126973675297379795648613899024483475477758467,
    53401982431260899369279685169372330447365005761055016951860233123164772573331589846460194490345369403894049331143071481331335761955844528015057518395653
  ]).map (unpackQuadsBigW18 16)

private def mod243NormBlock2 : List (List Nat) :=
  ([
    105570858576117860857634322791888191179736606929255213913171405075023364294428260704095575213268239977429663258685540582324964828470151475208256319783426,
    53196596350590692342387534075042167578441644413935406560546114229406753494292909278647393934015092877838079626707896187284005430897712387397569388610052,
    106592984608258879594098969630157016062184459424436717139782883133197074670321453636507924160565365360213083852269598870761022603659248527538482122523139,
    262076637871026912270618888672282746910586230849530315577745196272194171134595019730409500245217742844689327499276961742241850408052150187252373098987779,
    314860863725018858202778984048588316346885790525980825193317139514397795831262502004137747085246804745004638347311488531462845298943343643165150570217987,
    53402781598889966334004381518140661013726733660841917794380189690199268489713309493958202987605095627989612411993315618399292483432538980803217402823171,
    106387595406029727581394744462267303138030586944887557038057049457530548832028228595850842850359687086392969966598454427003175557876643418042280014119173,
    54421732812944917582828104119786748059163372382532957920406999138680940708652848321841778904672623154345010367773478090942433502019801770662389187084802,
    105773057351517456061475537320389752978018721609044790201635503748082940310557799135882963540394103284547283972951007078984319207164311814801444434936068,
    158762647433750336822298797410900863522439928632193073534908423321180015929422235635334198175866888784694504783279208203801916558298851075823658078437889,
    314452492212369231124966015870813818554431570131918034468461074004058486285577216978431841007022398244306481920566818910370739434131187991368743539311362,
    52990411102291416897093238040729853051475012711983956168987773433335303163346841758417800833339386477379264706646554352491820219775819623917013830796290,
    209703193543715747874899009019163915416581897859686004010325658569719006950275270089149830178765558454804811378370507573377750307349601574218906162430978,
    54011750453893575879400501348783191008961450098640321729430385657901738199540075416934433233903859849771227601228424269174169683434210510070913387593989,
    105366265419579250202571738819204173243476721804500429865446739301636986964322605142590378383379027519944242019362252286393386583838893120977179791917574,
    262079035397968595806306707294646989172354203760180510427709826328796046329804066270518822104249947461130312783052039088470203787299389900294595805446660,
    314860073946690850820079766100036125905698562775232512889766706273591325744335161566503117633113204655782497449602689263613687663004614994164031074599938,
    53398795125990651692385734878554294664664727457988207814418566520116486954907421770441611432679241042206148153274718591027445612718989236507583998656774,
    105572450667878522740511137332628229480701714214397969928569468328130866986022758175882037163825427542553328902511553458886978434944865376239825430118915,
    53195016745824227362447384071443998480896132128763742950172838738436235339103742528546199782055397538984226470705711712108680799741901477203404082250754,
    106591383151252938904672385756668874822629798305384969894652312193046431841630291501325829421882953014016518728086557132156164131786757410392635561148932,
    262076640992775835454876683530984500535964347999984745378228944760531532598626091742410982427513322293589709430432185453449101530989058879057115123680004,
    314862462060181909270832025724569019628806290391859237744515219761477531638246742186166784087191555530812275375058020781497912034023441228302248753366018,
    53402784720638146689085860636054319835739796854651147101780262357055751198247766820163521499421576868928024827637778345155743722255283690985810607408130,
    105979233234571079831954329960689064660430326791256028538303004642001959149896780629288462540907786151361342854931201067726126672338335068141063673872646,
    54421729691006761936700033976137087316638280515985565467684789893668129755149573056084183808733544124453187160668690143696918592907896724134716493792258,
    105776244656788069338203922477442373325194458341422432831312028546902783846130648380124216872575937019951232011383317569542534854727748550375861865480453
  ]).map (unpackQuadsBigW18 16)

private def mod243NormBlock3 : List (List Nat) :=
  ([
    158761058463927832039227587404800528175351366869544523656967648459209063382564614879906033813598478746667490021867298242525991340641597960168608131842562,
    314450912607602767598703314457125434359831273195833205997443969162394657267775835991845862029447468698400529715529001486750282438674188138711790372651265,
    52990432954531636889433436581077322997584090589251234620285047999202483743465479029015191813452786138654954253999736619976070844219824374354741989278212,
    209703202932920982487611931834474605444316021583312659613201754107670504168013366815351879407530331479701654442838990772629038212821347171850936398381570,
    53608167679560173360896360843698131444735381240162962148690725570707459119286186334929201117922493405043331879225014949466348487039431012878266671432450,
    105364685814812786676309037406819785165773626897718570211706332517783272757078111125923879765522771130742375781054324978892621166427745373016635614495746,
    262082232068484862211528045113847665511216840984507997931328610868576645383285230471594593803829863513189604608647679059801894455322775463697075944031236,
    314458080142275593431344461753748846419416506103999414664625859527229646565885572757187338907929290566101879789585721816588381995084903299153656866406914,
    53401998040004020183312698445892795368014076515635980879422023018676913129003013014626340799402513610593085377902118528263619205600311053036932917428998,
    105574042759639556037975895498167104041580281901217296551151322552075015383813003007256661845038845432971682797892251758132587210014457227865894896665604,
    53198194685848823364482029928591486092929726120605916450343109244817550750199504686452283334637598768994431251109941611757729210785707102754739270582789,
    106591386273001488493825979319356807315413868863814089510515843411011309591966807433927796980595192342669159168325173855484124663527989304961772137153538,
    158761854509713266553424692634136823992358002000811149565696867935585110479485597192238738743739624580538122685381772118733946947814786775924338052956420,
    314860873114319917779225504439207326946363056005885915489376731029342071350938373517275242191046057748427142730504564790259708904813669591406932100514306,
    53401195750626403629434581149381301121642609685749431044891080414759302957472377425063447758805312181268423431638630506533185909159253380455146847404546,
    106386009557766163423125702528343959495471956198787966341403701352834198995637601528316190868696675442625324848001751204464889367164830351771845521441538,
    54423321782767422365899227987650126004090462180930934271502558472933013333365570357475796706102437564051844025222688794969243684348350432785372650144259,
    105776235291541679922083257519352252433123223774888820498191717260843325832418238421018824598287538607189626052366533136187333412424864977114623448777476,
    158761055341989676393099517261150867432826275002997131204245439214196252429061339614148438717659399716775666814762510295280476431529692913640935438550018,
    314452495334118147762074671562099409575536345451192980315920694987014379137031794798760052918583336410362126987261961440696559861567053214385805990166786,
    52988850228016258174138822438817081848684223713608683855740624307204063609298052405484834155173640765551883025487010696777606405959820704398742959227397,
    209704788757320041481486785772270361248258014249587774595407790170216288266859521245332506780162595202227830183787113284765931244418972348203416215093761,
    53603394526025998833275795677882862919924724365539007333355179087818878973601915856850836085931175488386044145904097003192540287853413720048334962557188,
    105366268541328166845280928709976606575060323960929863199928500130416531606534104094189860723365239571051065524069874440676730721612189824007588515217923,
    262080646220221298053280795815413868736289855785018800390427805547357897144166219469684179625129797971292225956494774389050432356136513348041980835529219,
    314860083311936502494917062468009549918371013707331385160964315089233896139022703342120736214475593929434237135101064256724484703063007209389589535130113,
    53400405948242988339525388533096847700321687198903133036532515944913685478707641637573688291735043098584179593271898546906023634800057958854115834528007
  ]).map (unpackQuadsBigW18 16)

private def mod243NormBlock4 : List (List Nat) :=
  ([
    105570864819614961489618871016398296048212103341199469072232387849530964606979372288815467036051379431201004352679599124935262659277719789091966024811012,
    53196602594087792974371997176697283185382724560994646997166414641372925627366721863558250928916099723783002192315342210601607664527995026224070319538694,
    106999760931549603531967882719963342421402754658204855865206011205873110376429076060768229016458906623737654758727196396224408750125114459583719969849857,
    262076650382075963224056692041596127170684484019681320823876977070756643438612875619102402142513787568155516102684616339223041353613374082714655466324229,
    314860863725019229617367099103709387051351625965861062064110022444405116199542180722120077615445158325948797677524089293910870927813692090370890471178753,
    53402787842387065512311395690121339422607716970892187060289143667866805649066874896849909709362499746392089075464643383095199515633967281486715957740035,
    106386000192426176077122594919299912008459737527414754726605926769850791088683804575872272473127864008762834994515783713203555628376060204056465153065219,
    54421720325761481676472644114161984764535801061879187026371987532782370504674408222293701967420025217855278901039647056364385212475859315639526088770052,
    105774640078032467723214296719869953505501869097305592040120140465561290692818548051671385659280475114320926666018801745743142342688091070090695200014598,
    158762647433750336822298711272663906120278456667942500008063207793461136007277336915540051615028293156374323679316508946552801522970146622291591594902019,
    314452498455866697356828799324274224529443561688184058104565881644638601327093657416120417170822657830416106731338172770421987250574345655036591940436740,
    52990423589285982307263036004631593534779282671165823068451505648490807808667175637296207814409392562511576497876571178680889326209293959004907961910276,
    209703206054669532082321912310447048478315412788427010300024326116745171021594891213504728488777033880223489242102093129779674587472127358941265031070722,
    53606581831296612110004180834935483267100461097916649963031703886638722509174765101092089418113009223789992184336407493750755935416850455622752393101573,
    105366271663076716434434522272664579218488713360766453505823521013064275579585792596899617334914361294645031418078718575717263825098800485381694065541636,
    262079035397968597259984155885860770349807032015890346060409507335417786632810063198236479836261285771703267480204306632584622870695548483630658301985282,
    314860061459602683845833904176376334130542286542957706977918244493609732471893074581079993976346770977428852565238338087219184927018373519816309715764228,
    53398801369487752324370284118446367516158059467285417687257786524898626496530734367057997064270064290614714059702499806826009551651031263481483619270920,
    105572450667878892701421804473456871278378808698137526534306557335098495565403178990017410075936063509054997182904644949354176852212033603502176670450181,
    53195022989321329448109295764312895107679629654212787343426007857519211420122227846891752311059843334581135954007414903100842247116847278263526142116866,
    106591383151252938904672386095129530922041093379902554959909801171814104171895518662076192639228058215144194299826143519922632697866299976524233393242626,
    262076647260327413634903098648138482498156548383177186546638050779673962018750110227421337805663544481047855559141893590434684439827545983683158756950786,
    314864063541339083558063129800525279105544626405803071266645187334127598749577672851504977029483957272952885076635081368944637307948420173962846947902466,
    53404379934148098809776153855660213983486284657711513682870997891810954046857119728224534390575917636810442970845341682340808290703559133112785424286724,
    105979233234571078378276881369475283640586723408035918259850337539494886361865904221225963985879634072597579483393196929163346958282434638995184884515076,
    54421723447510031265626237676849917257319871620308306642235518750747248255010924154895669526132264546507919341278263779692345744217091210208662664774658,
    106181413279385034561277691920964518107506333370398863665293551790776676531561009800842590062783096510206701088524179669922025227977495370915698387779847
  ]).map (unpackQuadsBigW18 16)

private def mod243NormBlock5 : List (List Nat) :=
  ([
    158761045976744396132872127399175764880723795548890752762932636853310493178586174780357956876345880810177758555133467207947943051097655505145745033527812,
    314450906364105666966718851355470318752891383704819465114780467016548230671740829809755505197550226560944357232470942138175201807788877423042806243524865,
    52990439198028738975095348273951313476326661218270678809994494818667563901412465516139791859044029609739127552078055685683771502853013782715967582831110,
    209703190422061909005714841158287192212947126769172371066913012680734447773189557528896604189672041115700991729305823759513057370786840864271117708427780,
    53606572466050222693883515876845362375029226531383037629911392600579264495462355141986697143824610811028386225319623060395554493113966882361513976398596,
    105364673327818582504985129575148314534277570099940530016644339558661676451576133738661479916469016358142606662872940186135249086209624895818258607834116,
    262080643098472748464127202252725896092861466385252340457742275172698344910061388744095033965488799473151508135977032306682063539563783019037557887599618,
    314456484928765641310654168195682296251062735619210421438547476427404474566885271881204245463701091121413493743248418079332829625177196443711527675232770,
    53401998040004021636990146698645920446054409609916422950277373980125089016644774988077398268227453925209961540831696656080289100312442094723239717700356,
    105572447546129603917285601940100553873226506820257076880985959191368506871851540067642206450448371693663820723700653416468698084126398121314597428397058,
    53196605715836709617081187067469716516966326717424080331648175470152470269578220815157733268902311774889825697022964364884951802301291729254479042839043,
    106591392516687823768197062700024108576514605447544097144858110736600405399037636407039071256364620041015636048211827230826298514182801932597212110586884,
    158761854509808347961143423126445365804318578231083402245607416395624384272500678911067323594858021934024002233180202337099227244174055693177269447164162,
    314860860603270308613625390485910642324022976019096560335873333984129644270830753905916056501373269683819221894604602807442296628097132722752383478792708,
    53401201994123504261419129373891405990118106097693686203952063189266903270023489009783339581588451635039764525632689049143483739966821694338856552432132,
    106386003314174727119953550765734340226828321431870267036637643318645826812113715140952364503803936740200784217078638886056087277616192310569827012051716,
    54830098106058146303768141077456452363308757414699072996925686545609049039473192781736101561995978827576414931680286320432629830814216364830610497470977,
    105777836748549102635668852750224794371842350154754502081511288876381244472959577782123972715387540911154377190107391387306323310295376557466115266118402,
    158761049098492945722025720961863697373507866107319872378796168071275370928922690712959924435058120138830398995372083931275903582838887399714881609532418,
    314452507821112351938999200576342323696684476137471792932687399851541854593053697306319837450200493839688370912003674405853151460732361109648801416741122,
    52992012559297728274269212335271518346760406317567817502271479471040499670884092943073136025107799289960475226429830046879354660897265000916331404526087,
    209704801268179116417061325208917316526963163746302848011051503083790709344591386047998645186096326006145061392013203209434512693515661101618537997533697,
    53604977252541010495014555077363063447407871853799809171839815805297229355862664772639258204817547318159686838971891669951363423377192975337585727635718,
    105366262297830328471991305905788239346258693746342250499447021090756576934651567921238722802909007893610433880799248328419339890410009209566709579579907,
    262080639976724197421296332713758753050244727508528093221634557805773319872216910755381190345986239840267236370256719125282972117603253154463427472916993,
    314860083311936503948594511059223330938214617072203506520040358243532688567036544360217953571354157459107013522801631534748225748619373184461447255818753,
    53400399704745886253819504539488717671860320880146534587556280831688175850075198079994417088973017971168176346330917619788853223620424387268642567422213
  ]).map (unpackQuadsBigW18 16)

private def mod243RowAtW18 (u_idx : Nat) : List Nat :=
  let blk := u_idx / 27
  let off := u_idx % 27
  if blk == 0 then listRowAtW18 mod243NormBlock0 off
  else if blk == 1 then listRowAtW18 mod243NormBlock1 off
  else if blk == 2 then listRowAtW18 mod243NormBlock2 off
  else if blk == 3 then listRowAtW18 mod243NormBlock3 off
  else if blk == 4 then listRowAtW18 mod243NormBlock4 off
  else listRowAtW18 mod243NormBlock5 off

/-- Exact normalized `162`-state 4-step `Mod 243` (`2^162 ≡ 1 (mod 243)`) ternary-carry macro-selector:
    Normalizes `u_norm = ((rem243 % 243) * 2 ^ ((162 - exp162 % 162) % 162)) % 243` and selects the
    `(fourBits % 16)`-th valid 4-tuple `(s1, s2, s3, s4)` (`s_i ≥ 1`, `8 ≤ s1 + s2 + s3 + s4 ≤ 18 ≤ 19`),
    encoding `4` full binary mask bits in `≤ 18` positions (`18 / 4 = 4.5 < 5`). -/
def chooseFourStepTernaryCarry243 (rem243 exp162 fourBits : Nat) : Nat × Nat × Nat × Nat :=
  let u_n := uNorm243W18 rem243 exp162
  unpackQuadW18 (listNatAtW18 (mod243RowAtW18 (uIdxOf243W18 u_n)) (fourBits % 16))

/-- Normalized 4-step `Mod 243` branch validity predicate at `exp162 = 0` (`u_norm < 243`, `u_norm % 3 ≠ 0`). -/
def validQuad243NormBool (u_norm : Nat) (q : Nat × Nat × Nat × Nat) : Bool :=
  let s1 := q.1
  let s2 := q.2.1
  let s3 := q.2.2.1
  let s4 := q.2.2.2
  let d1 := (u_norm + 243 - (2 ^ ((162 - s1) % 162)) % 243) % 243
  let r1 := (d1 / 3) % 81
  let d2 := (r1 + 81 - (2 ^ ((162 - s1 - s2) % 162)) % 81) % 81
  let r2 := (d2 / 3) % 27
  let d3 := (r2 + 27 - (2 ^ ((162 - s1 - s2 - s3) % 162)) % 27) % 27
  let r3 := (d3 / 3) % 9
  let d4 := (r3 + 9 - (2 ^ ((162 - s1 - s2 - s3 - s4) % 162)) % 9) % 9
  (Nat.ble 1 s1 && Nat.ble 1 s2 && Nat.ble 1 s3 && Nat.ble 1 s4 && Nat.ble 8 (s1 + s2 + s3 + s4) && Nat.ble (s1 + s2 + s3 + s4) 18) &&
  (d1 % 3 == 0) && (r1 % 3 != 0) &&
  (d2 % 3 == 0) && (r2 % 3 != 0) &&
  (d3 % 3 == 0) && (r3 % 3 != 0) &&
  (d4 == 3 || d4 == 6)

private def noDupNatBoolW18 : List Nat -> Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => Nat.blt x y && noDupNatBoolW18 (y :: rest)

private theorem listNatAtW18_lt_of_strictInc_cf :
    ∀ (xs : List Nat) (i j : Nat),
      noDupNatBoolW18 xs = true -> i < j -> j < xs.length ->
      listNatAtW18 xs i < listNatAtW18 xs j
  | [], _, _, _, _, hj => False.elim (by simp at hj)
  | [_], _, _, _, hij, hj => False.elim (by simp at hj; omega)
  | x :: y :: rest, 0, 1, h, _, _ => by
    unfold noDupNatBoolW18 at h; unfold listNatAtW18
    exact Nat.blt_eq.mp (Bool.and_eq_true_iff.mp h).1
  | x :: y :: rest, 0, j' + 2, h, _, hj => by
    rcases Bool.and_eq_true_iff.mp h with ⟨hxy_b, hrest⟩
    have hxy : x < y := Nat.blt_eq.mp hxy_b
    have hy_lt := listNatAtW18_lt_of_strictInc_cf (y :: rest) 0 (j' + 1) hrest (by omega)
      (by simp at hj ⊢; omega)
    exact Nat.lt_trans hxy hy_lt
  | _ :: y :: rest, i + 1, j + 1, h, hij, hj => by
    unfold noDupNatBoolW18 at h; unfold listNatAtW18
    exact listNatAtW18_lt_of_strictInc_cf (y :: rest) i j (Bool.and_eq_true_iff.mp h).2
      (by omega) (by simp at hj ⊢; omega)

private theorem listNatAtW18_inj_of_noDupBool_cf (xs : List Nat) (i j : Nat)
    (h : noDupNatBoolW18 xs = true) (hi : i < xs.length) (hj : j < xs.length)
    (heq : listNatAtW18 xs i = listNatAtW18 xs j) : i = j := by
  if hij : i < j then
    have hlt := listNatAtW18_lt_of_strictInc_cf xs i j h hij hj
    omega
  else if hji : j < i then
    have hlt := listNatAtW18_lt_of_strictInc_cf xs j i h hji hi
    omega
  else
    omega

private def allElemQuadValidBoolW18 (u_norm : Nat) : List Nat -> Bool
  | [] => true
  | p :: ps => validQuad243NormBool u_norm (unpackQuadW18 p) && allElemQuadValidBoolW18 u_norm ps

private theorem allElemQuadValidBoolW18_get (u_norm : Nat) :
    ∀ (xs : List Nat) (k : Nat),
      allElemQuadValidBoolW18 u_norm xs = true -> k < xs.length ->
      validQuad243NormBool u_norm (unpackQuadW18 (listNatAtW18 xs k)) = true
  | [], _, _, hk => False.elim (by simp at hk)
  | p :: _, 0, h, _ => by
    unfold allElemQuadValidBoolW18 at h; unfold listNatAtW18
    exact (Bool.and_eq_true_iff.mp h).1
  | _ :: ps, k + 1, h, hk => by
    unfold allElemQuadValidBoolW18 at h; unfold listNatAtW18
    exact allElemQuadValidBoolW18_get u_norm ps k (Bool.and_eq_true_iff.mp h).2 (by simp at hk; omega)

private def checkMod243RowBoolW18 (u_idx : Nat) (row : List Nat) : Bool :=
  (row.length == 16) && noDupNatBoolW18 row && allElemQuadValidBoolW18 (uNormOfIdxW18 u_idx) row

private def allMod243RowsBoolW18 : Nat -> List (List Nat) -> Bool
  | _, [] => true
  | u_idx, row :: rows =>
    checkMod243RowBoolW18 u_idx row && allMod243RowsBoolW18 (u_idx + 1) rows

private theorem allMod243RowsBoolW18_get :
    ∀ (rows : List (List Nat)) (base off : Nat),
      allMod243RowsBoolW18 base rows = true -> off < rows.length ->
      checkMod243RowBoolW18 (base + off) (listRowAtW18 rows off) = true
  | [], _, _, _, ho => False.elim (by simp at ho)
  | row :: _, base, 0, h, _ => by
    unfold allMod243RowsBoolW18 at h; unfold listRowAtW18
    rw [Nat.add_zero]
    exact (Bool.and_eq_true_iff.mp h).1
  | _ :: rows, base, off + 1, h, ho => by
    unfold allMod243RowsBoolW18 at h; unfold listRowAtW18
    have ih := allMod243RowsBoolW18_get rows (base + 1) off (Bool.and_eq_true_iff.mp h).2
      (by simp at ho; omega)
    rwa [show base + 1 + off = base + (off + 1) by omega] at ih

set_option maxRecDepth 131072 in
private theorem checkMod243_b0 : allMod243RowsBoolW18 0 mod243NormBlock0 = true := by decide
set_option maxRecDepth 131072 in
private theorem checkMod243_b1 : allMod243RowsBoolW18 27 mod243NormBlock1 = true := by decide
set_option maxRecDepth 131072 in
private theorem checkMod243_b2 : allMod243RowsBoolW18 54 mod243NormBlock2 = true := by decide
set_option maxRecDepth 131072 in
private theorem checkMod243_b3 : allMod243RowsBoolW18 81 mod243NormBlock3 = true := by decide
set_option maxRecDepth 131072 in
private theorem checkMod243_b4 : allMod243RowsBoolW18 108 mod243NormBlock4 = true := by decide
set_option maxRecDepth 131072 in
private theorem checkMod243_b5 : allMod243RowsBoolW18 135 mod243NormBlock5 = true := by decide

private theorem mod243RowAtW18_spec_cf (u_idx : Nat) (hlt : u_idx < 162) :
    checkMod243RowBoolW18 u_idx (mod243RowAtW18 u_idx) = true := by
  have hblk : u_idx / 27 < 6 := by omega
  have hoff : u_idx % 27 < 27 := Nat.mod_lt u_idx (by decide)
  have hdm := (Nat.div_add_mod u_idx 27).symm
  unfold mod243RowAtW18
  dsimp only
  match hq : u_idx / 27, hblk with
  | 0, _ =>
    have h := allMod243RowsBoolW18_get mod243NormBlock0 0 (u_idx % 27) checkMod243_b0 (by simp only [mod243NormBlock0, List.length_map, List.length_cons, List.length_nil]; exact hoff)
    rwa [show 0 + u_idx % 27 = u_idx by omega] at h
  | 1, _ =>
    have h := allMod243RowsBoolW18_get mod243NormBlock1 27 (u_idx % 27) checkMod243_b1 (by simp only [mod243NormBlock1, List.length_map, List.length_cons, List.length_nil]; exact hoff)
    rwa [show 27 + u_idx % 27 = u_idx by omega] at h
  | 2, _ =>
    have h := allMod243RowsBoolW18_get mod243NormBlock2 54 (u_idx % 27) checkMod243_b2 (by simp only [mod243NormBlock2, List.length_map, List.length_cons, List.length_nil]; exact hoff)
    rwa [show 54 + u_idx % 27 = u_idx by omega] at h
  | 3, _ =>
    have h := allMod243RowsBoolW18_get mod243NormBlock3 81 (u_idx % 27) checkMod243_b3 (by simp only [mod243NormBlock3, List.length_map, List.length_cons, List.length_nil]; exact hoff)
    rwa [show 81 + u_idx % 27 = u_idx by omega] at h
  | 4, _ =>
    have h := allMod243RowsBoolW18_get mod243NormBlock4 108 (u_idx % 27) checkMod243_b4 (by simp only [mod243NormBlock4, List.length_map, List.length_cons, List.length_nil]; exact hoff)
    rwa [show 108 + u_idx % 27 = u_idx by omega] at h
  | 5, _ =>
    have h := allMod243RowsBoolW18_get mod243NormBlock5 135 (u_idx % 27) checkMod243_b5 (by simp only [mod243NormBlock5, List.length_map, List.length_cons, List.length_nil]; exact hoff)
    rwa [show 135 + u_idx % 27 = u_idx by omega] at h
  | _ + 6, hlt6 => exact False.elim (by omega)

-- Choice-free modular arithmetic & `2^162 ≡ 1 (mod 243)` normalization lemmas:

private theorem pow2_pos_cf_w18 : ∀ n : Nat, 1 ≤ 2 ^ n
  | 0 => Nat.le_refl 1
  | n + 1 => by rw [Nat.pow_succ]; have := pow2_pos_cf_w18 n; omega

private theorem pow2_mono_cf_w18 : ∀ {a b : Nat}, a ≤ b -> 2 ^ a ≤ 2 ^ b
  | 0, b, _ => pow2_pos_cf_w18 b
  | _ + 1, 0, h => False.elim (by omega)
  | a + 1, b + 1, h => by
    rw [Nat.pow_succ 2 a, Nat.pow_succ 2 b]
    exact Nat.mul_le_mul_right 2 (pow2_mono_cf_w18 (by omega))

private theorem pow2_mod3_ne_zero_cf_w18 : ∀ n : Nat, 2 ^ n % 3 ≠ 0
  | 0 => by decide
  | n + 1 => by
    have ih := pow2_mod3_ne_zero_cf_w18 n
    have hlt : 2 ^ n % 3 < 3 := Nat.mod_lt _ (by decide)
    rw [Nat.pow_succ, Nat.mul_mod]
    omega

private theorem pow2_mod243_period162_cf_w18 (n : Nat) :
    2 ^ n % 243 = 2 ^ (n % 162) % 243 := by
  have hp162 : ∀ q : Nat, 2 ^ (162 * q) % 243 = 1 := by
    intro q; induction q with
    | zero => rfl
    | succ q' ih =>
      rw [Nat.mul_succ 162 q', Nat.pow_add 2 (162 * q') 162, Nat.mul_mod, ih]
  conv => lhs; rw [(Nat.div_add_mod n 162).symm]
  rw [Nat.pow_add 2 (162 * (n / 162)) (n % 162), Nat.mul_mod, hp162 (n / 162), Nat.one_mul, Nat.mod_mod]

private theorem sub_mod_of_le_cf_w18 (M R U : Nat) (hM : M ≥ 1) (hUR : U ≤ R) :
    (R - U) % M = (R % M + M - U % M) % M := by
  have hR := (Nat.div_add_mod R M).symm
  have hU := (Nat.div_add_mod U M).symm
  have hrm : R % M < M := Nat.mod_lt R hM
  have hum : U % M < M := Nat.mod_lt U hM
  if hcmp : U % M ≤ R % M then
    have hsub : R - U = M * (R / M - U / M) + (R % M - U % M) := by
      have hq : U / M ≤ R / M := by
        if hq : U / M ≤ R / M then exact hq
        else
          exfalso
          have hm := Nat.mul_le_mul_left M (by omega : R / M + 1 ≤ U / M)
          rw [Nat.mul_add, Nat.mul_one] at hm; omega
      have hq_mul : M * (U / M) ≤ M * (R / M) := Nat.mul_le_mul_left M hq
      rw [Nat.mul_sub_left_distrib]
      generalize M * (R / M) = QR, M * (U / M) = QU at hR hU hq_mul ⊢; omega
    have hadd : R % M + M - U % M = M * 1 + (R % M - U % M) := by omega
    rw [hsub, hadd, Nat.add_comm (M * _), Nat.add_mul_mod_self_left,
        Nat.add_comm (M * 1), Nat.add_mul_mod_self_left]
  else
    have hq : U / M + 1 ≤ R / M := by
      if hq : U / M + 1 ≤ R / M then exact hq
      else
        exfalso
        have hm := Nat.mul_le_mul_left M (by omega : R / M ≤ U / M)
        omega
    have hsub : R - U = M * (R / M - (U / M + 1)) + (R % M + M - U % M) := by
      have hq_mul : M * (U / M) + M ≤ M * (R / M) := by
        simpa [Nat.mul_add, Nat.mul_one] using Nat.mul_le_mul_left M hq
      rw [Nat.mul_sub_left_distrib, Nat.mul_add, Nat.mul_one]
      generalize M * (R / M) = QR, M * (U / M) = QU at hR hU hq_mul ⊢; omega
    rw [hsub, Nat.add_comm (M * _), Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by omega : R % M + M - U % M < M)]

private theorem mul_norm_div3_step_cf_w18 (M' X Y W : Nat)
    (hM' : M' ≥ 1) (hYX : Y ≤ X) (hW3 : W % 3 ≠ 0) :
    let M := 3 * M'
    let d_n := ((X * W) % M + M - (Y * W) % M) % M
    d_n % 3 = 0 ->
    3 * ((X - Y) / 3) + Y = X ∧ (((X - Y) / 3) * W) % M' = (d_n / 3) % M' := by
  dsimp only
  intro hd3
  let M := 3 * M'
  have hM1 : M ≥ 1 := by dsimp [M]; omega
  have hYW_XW : Y * W ≤ X * W := Nat.mul_le_mul_right W hYX
  have hsub_mod : ((X - Y) * W) % M = ((X * W) % M + M - (Y * W) % M) % M := by
    rw [Nat.mul_sub_right_distrib]
    exact sub_mod_of_le_cf_w18 M (X * W) (Y * W) hM1 hYW_XW
  let d_n := ((X * W) % M + M - (Y * W) % M) % M
  change d_n % 3 = 0 at hd3
  change ((X - Y) * W) % M = d_n at hsub_mod
  have hd_xyw_3 : ((X - Y) * W) % 3 = 0 := by
    rw [← Nat.mod_mod_of_dvd ((X - Y) * W) ⟨M', rfl⟩, hsub_mod, hd3]
  have hd_xy_3 : (X - Y) % 3 = 0 := by
    rw [Nat.mul_mod] at hd_xyw_3
    have h1 : (X - Y) % 3 < 3 := Nat.mod_lt _ (by decide)
    have h2 : W % 3 < 3 := Nat.mod_lt _ (by decide)
    rcases (by omega : W % 3 = 1 ∨ W % 3 = 2) with hw1 | hw2
    · rw [hw1] at hd_xyw_3; omega
    · rw [hw2] at hd_xyw_3; omega
  let Q := (X - Y) / 3
  have hXY_3Q : X - Y = 3 * Q := by
    have hdm := (Nat.div_add_mod (X - Y) 3).symm
    dsimp [Q]; omega
  have h3Q_Y : 3 * Q + Y = X := by omega
  have h3_mod : (3 * (Q * W)) % (3 * M') = 3 * ((Q * W) % M') := by
    let rA := (Q * W) % M'
    have hrA_lt : rA < M' := Nat.mod_lt _ hM'
    have hdm := (Nat.div_add_mod (Q * W) M').symm
    have hexp : 3 * (Q * W) = 3 * rA + (3 * M') * ((Q * W) / M') := by
      dsimp [rA] at hdm ⊢
      calc 3 * (Q * W) = 3 * (M' * ((Q * W) / M') + (Q * W) % M') := by rw [← hdm]
        _ = 3 * ((Q * W) % M') + (3 * M') * ((Q * W) / M') := by
              rw [Nat.mul_add, ← Nat.mul_assoc 3 M', Nat.add_comm]
    rw [hexp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hdn_eq : d_n = 3 * ((Q * W) % M') := by
    rw [← hsub_mod, hXY_3Q, Nat.mul_assoc 3 Q W]
    exact h3_mod
  have hrem_lt : (Q * W) % M' < M' := Nat.mod_lt _ hM'
  refine ⟨h3Q_Y, ?_⟩
  change (Q * W) % M' = (d_n / 3) % M'
  rw [hdn_eq, show (3 * ((Q * W) % M')) / 3 = (Q * W) % M' by omega, Nat.mod_eq_of_lt hrem_lt]

private theorem pow2_sub_mul_norm_mod_cf_w18 (e S M : Nat)
    (he18 : e ≥ 18) (hS1 : 1 ≤ S) (hS18 : S ≤ 18) (hdvd : M ∣ 243) :
    ((2 ^ (e - S)) * (2 ^ ((162 - e % 162) % 162))) % M =
      (2 ^ ((162 - S) % 162)) % M := by
  let k_inv := (162 - e % 162) % 162
  have hexp_mod : (e - S + k_inv) % 162 = (162 - S) % 162 := by
    have hdm := (Nat.div_add_mod e 162).symm
    have hk_lt : e % 162 < 162 := Nat.mod_lt e (by decide)
    dsimp [k_inv]
    if hk0 : e % 162 = 0 then
      have hq1 : e / 162 ≥ 1 := by omega
      have hrew : e - S + (162 - e % 162) % 162 = (162 - S) + 162 * (e / 162 - 1) := by
        rw [hk0]; simp; omega
      rw [hrew, Nat.add_mul_mod_self_left]
    else
      have hkinv : (162 - e % 162) % 162 = 162 - e % 162 := Nat.mod_eq_of_lt (by omega)
      have hrew : e - S + (162 - e % 162) % 162 = (162 - S) + 162 * (e / 162) := by
        rw [hkinv]; omega
      rw [hrew, Nat.add_mul_mod_self_left]
  rw [← Nat.pow_add 2 (e - S) k_inv,
      ← Nat.mod_mod_of_dvd (2 ^ (e - S + k_inv)) hdvd,
      pow2_mod243_period162_cf_w18 (e - S + k_inv),
      hexp_mod,
      Nat.mod_mod_of_dvd _ hdvd]

private theorem uNorm243_bijection_cf_w18 (R e : Nat) (hR3 : R % 3 ≠ 0) :
    let u_n := uNorm243W18 R e
    u_n < 243 ∧ u_n % 3 ≠ 0 ∧ uIdxOf243W18 u_n < 162 ∧ uNormOfIdxW18 (uIdxOf243W18 u_n) = u_n := by
  dsimp only
  let W := 2 ^ ((162 - e % 162) % 162)
  let u_n := ((R % 243) * W) % 243
  have hu_lt : u_n < 243 := Nat.mod_lt _ (by decide)
  have hW3 : W % 3 ≠ 0 := pow2_mod3_ne_zero_cf_w18 _
  have hu3 : u_n % 3 ≠ 0 := by
    dsimp [u_n]
    have hd3_243 : 3 ∣ 243 := by decide
    rw [Nat.mod_mod_of_dvd ((R % 243) * W) hd3_243,
        Nat.mul_mod, Nat.mod_mod_of_dvd R hd3_243]
    have h1 : R % 3 < 3 := Nat.mod_lt R (by decide)
    have h2 : W % 3 < 3 := Nat.mod_lt W (by decide)
    rcases (by omega : W % 3 = 1 ∨ W % 3 = 2) with hw1 | hw2
    · rw [hw1]; omega
    · rw [hw2]; omega
  have hidx_lt : uIdxOf243W18 u_n < 162 := by
    unfold uIdxOf243W18; omega
  have hinv : uNormOfIdxW18 (uIdxOf243W18 u_n) = u_n := by
    unfold uNormOfIdxW18 uIdxOf243W18
    have hdm := (Nat.div_add_mod u_n 3).symm
    have hm3 : u_n % 3 < 3 := Nat.mod_lt u_n (by decide)
    omega
  exact ⟨hu_lt, hu3, hidx_lt, hinv⟩

private theorem chooseFourStepTernaryCarry243_nat_step_cf_w18 (R e fourBits : Nat)
    (hR3 : R % 3 ≠ 0) (he18 : e ≥ 18) (hR_big : R ≥ 40 * 2 ^ e) :
    let q := chooseFourStepTernaryCarry243 (R % 243) (e % 162) (fourBits % 16)
    let e1 := e - q.1
    let R1 := (R - 2 ^ e1) / 3
    let e2 := e1 - q.2.1
    let R2 := (R1 - 2 ^ e2) / 3
    let e3 := e2 - q.2.2.1
    let R3 := (R2 - 2 ^ e3) / 3
    let e4 := e3 - q.2.2.2
    let R4 := (R3 - 2 ^ e4) / 3
    1 ≤ q.1 ∧ 1 ≤ q.2.1 ∧ 1 ≤ q.2.2.1 ∧ 1 ≤ q.2.2.2 ∧
    8 ≤ q.1 + q.2.1 + q.2.2.1 + q.2.2.2 ∧
    q.1 + q.2.1 + q.2.2.1 + q.2.2.2 ≤ 18 ∧
    3 * R1 + 2 ^ e1 = R ∧
    3 * R2 + 2 ^ e2 = R1 ∧
    3 * R3 + 2 ^ e3 = R2 ∧
    3 * R4 + 2 ^ e4 = R3 ∧
    R4 % 3 ≠ 0 ∧
    (∀ b1 b2 : Nat, b1 < 16 -> b2 < 16 ->
      chooseFourStepTernaryCarry243 (R % 243) (e % 162) b1 =
        chooseFourStepTernaryCarry243 (R % 243) (e % 162) b2 -> b1 = b2) := by
  dsimp only
  have hun_eq : uNorm243W18 (R % 243) (e % 162) = uNorm243W18 R e := by
    unfold uNorm243W18; rw [Nat.mod_mod, Nat.mod_mod]
  rcases uNorm243_bijection_cf_w18 R e hR3 with ⟨_, _, hidx_lt, hinv⟩
  let u_n := uNorm243W18 R e
  let row := mod243RowAtW18 (uIdxOf243W18 u_n)
  have hrow_ok : checkMod243RowBoolW18 (uIdxOf243W18 u_n) row = true :=
    mod243RowAtW18_spec_cf (uIdxOf243W18 u_n) hidx_lt
  unfold checkMod243RowBoolW18 at hrow_ok
  rw [hinv] at hrow_ok
  rcases Bool.and_eq_true_iff.mp hrow_ok with ⟨h1, hall_valid⟩
  rcases Bool.and_eq_true_iff.mp h1 with ⟨hlen_b, hnodup⟩
  have hlen16 : row.length = 16 := beq_iff_eq.mp hlen_b
  have hb_lt16 : fourBits % 16 < 16 := Nat.mod_lt _ (by decide)
  have hsel_eq : ∀ b : Nat, b < 16 ->
      chooseFourStepTernaryCarry243 (R % 243) (e % 162) b = unpackQuadW18 (listNatAtW18 row b) := by
    intro b hb
    unfold chooseFourStepTernaryCarry243
    rw [hun_eq, Nat.mod_eq_of_lt hb]
  have hval := allElemQuadValidBoolW18_get u_n row (fourBits % 16) hall_valid (hlen16 ▸ hb_lt16)
  rw [← hsel_eq (fourBits % 16) hb_lt16] at hval
  let q := chooseFourStepTernaryCarry243 (R % 243) (e % 162) (fourBits % 16)
  change validQuad243NormBool u_n q = true at hval
  unfold validQuad243NormBool at hval
  dsimp only at hval
  rcases Bool.and_eq_true_iff.mp hval with ⟨hv1, hd4_b⟩
  rcases Bool.and_eq_true_iff.mp hv1 with ⟨hv2, _⟩
  rcases Bool.and_eq_true_iff.mp hv2 with ⟨hv3, hd3_b⟩
  rcases Bool.and_eq_true_iff.mp hv3 with ⟨hv4, _⟩
  rcases Bool.and_eq_true_iff.mp hv4 with ⟨hv5, hd2_b⟩
  rcases Bool.and_eq_true_iff.mp hv5 with ⟨hv6, _⟩
  rcases Bool.and_eq_true_iff.mp hv6 with ⟨hbds_b, hd1_b⟩
  rcases Bool.and_eq_true_iff.mp hbds_b with ⟨hb5, hsum18_b⟩
  rcases Bool.and_eq_true_iff.mp hb5 with ⟨hb4, hsum8_b⟩
  rcases Bool.and_eq_true_iff.mp hb4 with ⟨hb3, hs4_b⟩
  rcases Bool.and_eq_true_iff.mp hb3 with ⟨hb2, hs3_b⟩
  rcases Bool.and_eq_true_iff.mp hb2 with ⟨hs1_b, hs2_b⟩
  have hs1_1 : 1 ≤ q.1 := Nat.ble_eq.mp hs1_b
  have hs2_1 : 1 ≤ q.2.1 := Nat.ble_eq.mp hs2_b
  have hs3_1 : 1 ≤ q.2.2.1 := Nat.ble_eq.mp hs3_b
  have hs4_1 : 1 ≤ q.2.2.2 := Nat.ble_eq.mp hs4_b
  have hsum8 : 8 ≤ q.1 + q.2.1 + q.2.2.1 + q.2.2.2 := Nat.ble_eq.mp hsum8_b
  have hsum18 : q.1 + q.2.1 + q.2.2.1 + q.2.2.2 ≤ 18 := Nat.ble_eq.mp hsum18_b
  have hd1_3 : ((u_n + 243 - 2 ^ ((162 - q.1) % 162) % 243) % 243) % 3 = 0 := beq_iff_eq.mp hd1_b
  have hd2_3 : ((((u_n + 243 - 2 ^ ((162 - q.1) % 162) % 243) % 243 / 3) % 81 + 81 -
      2 ^ ((162 - q.1 - q.2.1) % 162) % 81) % 81) % 3 = 0 := beq_iff_eq.mp hd2_b
  have hd3_3 : ((((((u_n + 243 - 2 ^ ((162 - q.1) % 162) % 243) % 243 / 3) % 81 + 81 -
      2 ^ ((162 - q.1 - q.2.1) % 162) % 81) % 81 / 3) % 27 + 27 -
      2 ^ ((162 - q.1 - q.2.1 - q.2.2.1) % 162) % 27) % 27) % 3 = 0 := beq_iff_eq.mp hd3_b
  have hd4_36 : (((((((u_n + 243 - 2 ^ ((162 - q.1) % 162) % 243) % 243 / 3) % 81 + 81 -
      2 ^ ((162 - q.1 - q.2.1) % 162) % 81) % 81 / 3) % 27 + 27 -
      2 ^ ((162 - q.1 - q.2.1 - q.2.2.1) % 162) % 27) % 27 / 3) % 9 + 9 -
      2 ^ ((162 - q.1 - q.2.1 - q.2.2.1 - q.2.2.2) % 162) % 9) % 9 = 3 ∨
    (((((((u_n + 243 - 2 ^ ((162 - q.1) % 162) % 243) % 243 / 3) % 81 + 81 -
      2 ^ ((162 - q.1 - q.2.1) % 162) % 81) % 81 / 3) % 27 + 27 -
      2 ^ ((162 - q.1 - q.2.1 - q.2.2.1) % 162) % 27) % 27 / 3) % 9 + 9 -
      2 ^ ((162 - q.1 - q.2.1 - q.2.2.1 - q.2.2.2) % 162) % 9) % 9 = 6 := by
    rcases Bool.or_eq_true_iff.mp hd4_b with h3 | h6
    · exact Or.inl (beq_iff_eq.mp h3)
    · exact Or.inr (beq_iff_eq.mp h6)
  let W := 2 ^ ((162 - e % 162) % 162)
  have hW3 : W % 3 ≠ 0 := pow2_mod3_ne_zero_cf_w18 _
  have hRW_243 : (R * W) % 243 = u_n := by
    change (R * W) % 243 = ((R % 243) * W) % 243
    rw [Nat.mul_mod R W 243, Nat.mul_mod (R % 243) W 243, Nat.mod_mod]
  let e1 := e - q.1
  let e2 := e1 - q.2.1
  let e3 := e2 - q.2.2.1
  let e4 := e3 - q.2.2.2
  have he1_le : 2 ^ e1 ≤ 2 ^ e := pow2_mono_cf_w18 (by dsimp [e1]; omega)
  have he2_le : 2 ^ e2 ≤ 2 ^ e := pow2_mono_cf_w18 (by dsimp [e2, e1]; omega)
  have he3_le : 2 ^ e3 ≤ 2 ^ e := pow2_mono_cf_w18 (by dsimp [e3, e2, e1]; omega)
  have he4_le : 2 ^ e4 ≤ 2 ^ e := pow2_mono_cf_w18 (by dsimp [e4, e3, e2, e1]; omega)
  have hp1_norm : (2 ^ e1 * W) % 243 = 2 ^ ((162 - q.1) % 162) % 243 :=
    pow2_sub_mul_norm_mod_cf_w18 e q.1 243 he18 hs1_1 (by omega) ⟨1, by decide⟩
  have hp2_norm : (2 ^ e2 * W) % 81 = 2 ^ ((162 - q.1 - q.2.1) % 162) % 81 := by
    have h := pow2_sub_mul_norm_mod_cf_w18 e (q.1 + q.2.1) 81 he18 (by omega) (by omega) ⟨3, by decide⟩
    rwa [show e - (q.1 + q.2.1) = e2 by dsimp [e2, e1]; omega,
         show 162 - (q.1 + q.2.1) = 162 - q.1 - q.2.1 by omega] at h
  have hp3_norm : (2 ^ e3 * W) % 27 = 2 ^ ((162 - q.1 - q.2.1 - q.2.2.1) % 162) % 27 := by
    have h := pow2_sub_mul_norm_mod_cf_w18 e (q.1 + q.2.1 + q.2.2.1) 27 he18 (by omega) (by omega) ⟨9, by decide⟩
    rwa [show e - (q.1 + q.2.1 + q.2.2.1) = e3 by dsimp [e3, e2, e1]; omega,
         show 162 - (q.1 + q.2.1 + q.2.2.1) = 162 - q.1 - q.2.1 - q.2.2.1 by omega] at h
  have hp4_norm : (2 ^ e4 * W) % 9 = 2 ^ ((162 - q.1 - q.2.1 - q.2.2.1 - q.2.2.2) % 162) % 9 := by
    have h := pow2_sub_mul_norm_mod_cf_w18 e (q.1 + q.2.1 + q.2.2.1 + q.2.2.2) 9 he18 (by omega) hsum18 ⟨27, by decide⟩
    rwa [show e - (q.1 + q.2.1 + q.2.2.1 + q.2.2.2) = e4 by dsimp [e4, e3, e2, e1]; omega,
         show 162 - (q.1 + q.2.1 + q.2.2.1 + q.2.2.2) = 162 - q.1 - q.2.1 - q.2.2.1 - q.2.2.2 by omega] at h
  have hs_step1 := mul_norm_div3_step_cf_w18 81 R (2 ^ e1) W (by decide) (by omega) hW3
    (by rw [show 3 * 81 = 243 from rfl, hRW_243, hp1_norm]; exact hd1_3)
  let R1 := (R - 2 ^ e1) / 3
  have h3R1 : 3 * R1 + 2 ^ e1 = R := hs_step1.1
  have hR1W : (R1 * W) % 81 = (((u_n + 243 - 2 ^ ((162 - q.1) % 162) % 243) % 243) / 3) % 81 := by
    have h := hs_step1.2
    rwa [show 3 * 81 = 243 from rfl, hRW_243, hp1_norm] at h
  have hR1_ge : R1 ≥ 13 * 2 ^ e := by omega
  have hs_step2 := mul_norm_div3_step_cf_w18 27 R1 (2 ^ e2) W (by decide) (by omega) hW3
    (by rw [show 3 * 27 = 81 from rfl, hR1W, hp2_norm]; exact hd2_3)
  let R2 := (R1 - 2 ^ e2) / 3
  have h3R2 : 3 * R2 + 2 ^ e2 = R1 := hs_step2.1
  have hR2W : (R2 * W) % 27 = (((((u_n + 243 - 2 ^ ((162 - q.1) % 162) % 243) % 243 / 3) % 81 + 81 -
      2 ^ ((162 - q.1 - q.2.1) % 162) % 81) % 81) / 3) % 27 := by
    have h := hs_step2.2
    rwa [show 3 * 27 = 81 from rfl, hR1W, hp2_norm] at h
  have hR2_ge : R2 ≥ 4 * 2 ^ e := by omega
  have hs_step3 := mul_norm_div3_step_cf_w18 9 R2 (2 ^ e3) W (by decide) (by omega) hW3
    (by rw [show 3 * 9 = 27 from rfl, hR2W, hp3_norm]; exact hd3_3)
  let R3 := (R2 - 2 ^ e3) / 3
  have h3R3 : 3 * R3 + 2 ^ e3 = R2 := hs_step3.1
  have hR3W : (R3 * W) % 9 = (((((((u_n + 243 - 2 ^ ((162 - q.1) % 162) % 243) % 243 / 3) % 81 + 81 -
      2 ^ ((162 - q.1 - q.2.1) % 162) % 81) % 81 / 3) % 27 + 27 -
      2 ^ ((162 - q.1 - q.2.1 - q.2.2.1) % 162) % 27) % 27) / 3) % 9 := by
    have h := hs_step3.2
    rwa [show 3 * 9 = 27 from rfl, hR2W, hp3_norm] at h
  have hR3_ge : R3 ≥ 2 ^ e := by omega
  have hs_step4 := mul_norm_div3_step_cf_w18 3 R3 (2 ^ e4) W (by decide) (by omega) hW3
    (by rw [show 3 * 3 = 9 from rfl, hR3W, hp4_norm]; rcases hd4_36 with h3 | h6 <;> omega)
  let R4 := (R3 - 2 ^ e4) / 3
  have h3R4 : 3 * R4 + 2 ^ e4 = R3 := hs_step4.1
  have hR4W_n0 : (R4 * W) % 3 ≠ 0 := by
    have h := hs_step4.2
    rw [show 3 * 3 = 9 from rfl, hR3W, hp4_norm] at h
    rcases hd4_36 with h3 | h6
    · rw [h3] at h; rw [h]; decide
    · rw [h6] at h; rw [h]; decide
  have hR4_n3 : R4 % 3 ≠ 0 := by
    intro h0
    rw [Nat.mul_mod, h0, Nat.zero_mul, Nat.zero_mod] at hR4W_n0
    exact hR4W_n0 rfl
  refine ⟨hs1_1, hs2_1, hs3_1, hs4_1, hsum8, hsum18, h3R1, h3R2, h3R3, h3R4, hR4_n3, ?_⟩
  intro b1 b2 hb1 hb2 heq
  rw [hsel_eq b1 hb1, hsel_eq b2 hb2] at heq
  have hp_eq : listNatAtW18 row b1 = listNatAtW18 row b2 := by
    rw [← packQuad_unpackQuad_cf_w18 (listNatAtW18 row b1),
        ← packQuad_unpackQuad_cf_w18 (listNatAtW18 row b2), heq]
  exact listNatAtW18_inj_of_noDupBool_cf row b1 b2 hnodup (hlen16 ▸ hb1) (hlen16 ▸ hb2) hp_eq

/--
  Theorem W18.4b (`mod81_span14_stall_and_mod243_four_step_macro_cert`,
  choice-free `zero custom axioms`):
  1. **Choice-Free 3-Step `Mod 81` Span-`≤ 14` Stall Obstruction:**
     At normalized `Mod 81` state `u_norm = 79`, the complete set of valid 3-step `(s_1, s_2, s_3)`
     branches with `s_i ≥ 1` and `s_1 + s_2 + s_3 ≤ 14` is `validTriples81Span14At79` of exact
     cardinality `7 < 8 = 2 ^ 3`; hence NO 3-bit (`Fin 8`) selector into valid span-`≤ 14` triples
     at `u_norm = 79` can be injective!
  2. **Choice-Free Normalized `162`-State 4-Step `Mod 243` Macro-Selector:**
     Across ALL `(R, e)` with `R % 3 ≠ 0`, `e ≥ 18`, and `R ≥ 40 * 2 ^ e`, `chooseFourStepTernaryCarry243`
     produces `16 = 2 ^ 4` pairwise-distinct valid 4-step ternary-carry branches in `8 ≤ span ≤ 18 ≤ 19`
     (`18 / 4 = 4.5 < 5`) with exact division by `3` at all 4 steps and `R_4 % 3 ≠ 0`
     (`Branches P2.2 & P5.3`, `W18_H4`).
-/
theorem mod81_span14_stall_and_mod243_four_step_macro_cert :
    (validTriples81Span14At79.length = 7 ∧ 7 < 2 ^ 3 ∧
     (∀ s1 s2 s3 : Nat,
        validTriple81NormBool 79 (s1, s2, s3) = true ↔ (s1, s2, s3) ∈ validTriples81Span14At79) ∧
     (∀ f : Fin 8 -> Nat × Nat × Nat,
        (∀ b : Fin 8, validTriple81NormBool 79 (f b) = true) ->
        ¬ (∀ b1 b2 : Fin 8, f b1 = f b2 -> b1 = b2))) ∧
    (∀ (R e fourBits : Nat), R % 3 ≠ 0 -> e ≥ 18 -> R ≥ 40 * 2 ^ e ->
      let q := chooseFourStepTernaryCarry243 (R % 243) (e % 162) (fourBits % 16)
      let e1 := e - q.1
      let R1 := (R - 2 ^ e1) / 3
      let e2 := e1 - q.2.1
      let R2 := (R1 - 2 ^ e2) / 3
      let e3 := e2 - q.2.2.1
      let R3 := (R2 - 2 ^ e3) / 3
      let e4 := e3 - q.2.2.2
      let R4 := (R3 - 2 ^ e4) / 3
      1 ≤ q.1 ∧ 1 ≤ q.2.1 ∧ 1 ≤ q.2.2.1 ∧ 1 ≤ q.2.2.2 ∧
      8 ≤ q.1 + q.2.1 + q.2.2.1 + q.2.2.2 ∧
      q.1 + q.2.1 + q.2.2.1 + q.2.2.2 ≤ 18 ∧
      3 * R1 + 2 ^ e1 = R ∧
      3 * R2 + 2 ^ e2 = R1 ∧
      3 * R3 + 2 ^ e3 = R2 ∧
      3 * R4 + 2 ^ e4 = R3 ∧
      R4 % 3 ≠ 0 ∧
      (∀ b1 b2 : Nat, b1 < 16 -> b2 < 16 ->
        chooseFourStepTernaryCarry243 (R % 243) (e % 162) b1 =
          chooseFourStepTernaryCarry243 (R % 243) (e % 162) b2 -> b1 = b2)) :=
  ⟨⟨rfl, by decide, mod81_at79_all_iff_cf_w18, mod81_at79_no_8branch_selector_cf_w18⟩,
   chooseFourStepTernaryCarry243_nat_step_cf_w18⟩


-- ----------------------------------------------------------------------------
-- Section 3C: 4-Bit (`s = 4`) Multiplicative-Dlog `Mod 531441` (`3^12`) Bottom
--             Collision Lifting + 4-Step `Mod 243` Macro-Encoding:
--             Unconditional Sub-`250` Threshold (`M_0 = 210 ≤ 250`), Steeper-Slope
--             (`c = 5 ≤ 5`, Beating `c = 6`!) Exponential Dyadic Occupancy (`W18_H4`)
-- ----------------------------------------------------------------------------

/-- Top-down `k`-macro-step (`4 * k` ternary carry steps) chain starting from `(e_cur, R_cur)` and `mask`. -/
def fourStepTernaryCarryChain : Nat -> Nat -> Nat -> Nat -> (Nat × Nat × List Nat)
  | 0, e_cur, R_cur, _ => (e_cur, R_cur, [])
  | k + 1, e_cur, R_cur, mask =>
    let q := chooseFourStepTernaryCarry243 (R_cur % 243) (e_cur % 162) (mask % 16)
    let e1 := e_cur - q.1
    let R1 := (R_cur - 2 ^ e1) / 3
    let e2 := e1 - q.2.1
    let R2 := (R1 - 2 ^ e2) / 3
    let e3 := e2 - q.2.2.1
    let R3 := (R2 - 2 ^ e3) / 3
    let e4 := e3 - q.2.2.2
    let R4 := (R3 - 2 ^ e4) / 3
    let sub := fourStepTernaryCarryChain k e4 R4 (mask / 16)
    (sub.1, sub.2.1, sub.2.2 ++ [q.2.2.2 - 1, q.2.2.1 - 1, q.2.1 - 1, q.1 - 1])

private theorem list_append_singleton_inj_w18 {α : Type} :
    ∀ (xs ys : List α) (a b : α), xs ++ [a] = ys ++ [b] -> xs = ys ∧ a = b
  | [], [], a, b, h => ⟨rfl, by simpa using h⟩
  | [], _ :: _, _, _, h => by exfalso; have hlen := congrArg List.length h; simp at hlen
  | _ :: _, [], _, _, h => by exfalso; have hlen := congrArg List.length h; simp at hlen
  | x :: xs, y :: ys, a, b, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    rcases list_append_singleton_inj_w18 xs ys a b h.2 with ⟨hxy, hab⟩
    exact ⟨by rw [h.1, hxy], hab⟩

private theorem replicate_false_cons_true_inj_w18 :
    ∀ (a b : Nat) (xs ys : List Bool),
      List.replicate a false ++ (true :: xs) = List.replicate b false ++ (true :: ys) ->
      a = b ∧ xs = ys
  | 0, 0, xs, ys, h => ⟨rfl, by simpa using h⟩
  | 0, _ + 1, _, _, h => by simp [List.replicate_succ] at h
  | _ + 1, 0, _, _, h => by simp [List.replicate_succ] at h
  | a + 1, b + 1, xs, ys, h => by
    simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
    rcases replicate_false_cons_true_inj_w18 a b xs ys h with ⟨hab, hxy⟩
    exact ⟨congrArg Nat.succ hab, hxy⟩

private theorem zeroRunsSuffix_append_and_inj_w18 :
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
        rcases replicate_false_cons_true_inj_w18 k1 k2 _ _ h with ⟨hk, htl⟩
        rw [hk, ih tl2 htl]
  exact ⟨happ, hinj⟩

private theorem zeroRunsSuffix_nonempty_eq_mid_true_w18 :
    ∀ (k : Nat) (ks : List Nat), ∃ mid : List Bool, zeroRunsSuffix (k :: ks) = mid ++ [true]
  | k, [] => ⟨List.replicate k false, by simp [zeroRunsSuffix]⟩
  | k, k2 :: tl => by
    rcases zeroRunsSuffix_nonempty_eq_mid_true_w18 k2 tl with ⟨mid_tl, htl⟩
    refine ⟨List.replicate k false ++ [true] ++ mid_tl, ?_⟩
    simp only [zeroRunsSuffix] at htl ⊢
    rw [htl]; simp [List.append_assoc]

private def fourStepChainPropW18 (k : Nat) : Prop :=
  ∀ (e_cur R_cur L1 : Nat),
    e_cur ≤ L1 ->
    e_cur ≥ 18 * k + 18 ->
    R_cur % 3 ≠ 0 ->
    R_cur ≥ (2 * 3 ^ (4 * k + 10) - 1) * 2 ^ L1 ->
    (∀ mask : Nat,
      let ch := fourStepTernaryCarryChain k e_cur R_cur mask
      let e_fin := ch.1
      let R_fin := ch.2.1
      let gaps := ch.2.2
      e_cur - 18 * k ≤ e_fin ∧ e_fin ≤ e_cur ∧
      gaps.length = 4 * k ∧
      R_fin % 3 ≠ 0 ∧
      R_fin ≥ (2 * 3 ^ 10 - 1) * 2 ^ L1 ∧
      (∀ (acc : List Bool) (Q1 : Nat),
        acc.length = e_fin + 1 ->
        affineCarry acc < 16 * 2 ^ e_fin ->
        3 * R_fin + 2 ^ e_fin = 3 * Q1 + affineCarry acc ->
        let w_out := acc ++ zeroRunsSuffix gaps
        w_out.length = e_cur + 1 ∧
        parityWeight w_out = parityWeight acc + 4 * k ∧
        affineCarry w_out < 16 * 2 ^ e_cur ∧
        3 * R_cur + 2 ^ e_cur = 3 ^ (4 * k + 1) * Q1 + affineCarry w_out)) ∧
    (∀ m1 m2 : Nat, m1 < 16 ^ k -> m2 < 16 ^ k ->
      (fourStepTernaryCarryChain k e_cur R_cur m1).2.2 =
        (fourStepTernaryCarryChain k e_cur R_cur m2).2.2 ->
      m1 = m2)

private theorem fourStepTernaryCarryChain_step_w18 (k' : Nat)
    (ih : fourStepChainPropW18 k') : fourStepChainPropW18 (k' + 1) := by
  intro e_cur R_cur L1 he_L1 he_18k hR3 hR_lo
  have hR_big : R_cur ≥ 40 * 2 ^ e_cur := by
    have hp10 : (2 : Nat) * 3 ^ (4 * (k' + 1) + 10) - 1 ≥ 40 := by
      have h := nat_pow_mono_exp_pos 3 10 (4 * (k' + 1) + 10) (by decide) (by omega)
      have v10 : (3 : Nat) ^ 10 = 59049 := by decide
      omega
    have he_pow : 2 ^ e_cur ≤ 2 ^ L1 := pow2_mono_nat he_L1
    calc 40 * 2 ^ e_cur ≤ 40 * 2 ^ L1 := Nat.mul_le_mul_left 40 he_pow
      _ ≤ (2 * 3 ^ (4 * (k' + 1) + 10) - 1) * 2 ^ L1 := Nat.mul_le_mul_right _ hp10
      _ ≤ R_cur := hR_lo
  have hR4_lo_of : ∀ (e1 e2 e3 e4 R1 R2 R3 R4 : Nat),
      e1 ≤ L1 -> e2 ≤ L1 -> e3 ≤ L1 -> e4 ≤ L1 ->
      3 * R1 + 2 ^ e1 = R_cur -> 3 * R2 + 2 ^ e2 = R1 ->
      3 * R3 + 2 ^ e3 = R2 -> 3 * R4 + 2 ^ e4 = R3 ->
      R4 ≥ (2 * 3 ^ (4 * k' + 10) - 1) * 2 ^ L1 := by
    intro e1 e2 e3 e4 R1 R2 R3 R4 he1_L1 he2_L1 he3_L1 he4_L1 h3R1 h3R2 h3R3 h3R4
    let P3 := 3 ^ (4 * k' + 10)
    have hP3_pos : P3 ≥ 1 := pow3_pos_nat (4 * k' + 10)
    have hp_sp : 3 ^ (4 * (k' + 1) + 10) = 81 * P3 := by
      dsimp [P3]; rw [show 4 * (k' + 1) + 10 = (4 * k' + 10) + 4 by omega, Nat.pow_add 3 _ 4]
      change _ = 81 * _; ac_rfl
    have hR_sp : R_cur ≥ (162 * P3 - 1) * 2 ^ L1 := by
      rw [hp_sp, show 2 * (81 * P3) = 162 * P3 by omega] at hR_lo; exact hR_lo
    have h2e1_le : 2 ^ e1 ≤ 2 ^ L1 := pow2_mono_nat he1_L1
    have h2e2_le : 2 ^ e2 ≤ 2 ^ L1 := pow2_mono_nat he2_L1
    have h2e3_le : 2 ^ e3 ≤ 2 ^ L1 := pow2_mono_nat he3_L1
    have h2e4_le : 2 ^ e4 ≤ 2 ^ L1 := pow2_mono_nat he4_L1
    let B1 := (54 * P3 - 1) * 2 ^ L1
    have h3B1 : 3 * B1 + 2 ^ L1 ≤ 3 * R1 + 2 ^ L1 := by
      calc 3 * B1 + 2 ^ L1
          = (3 * (54 * P3 - 1) + 1) * 2 ^ L1 := by dsimp [B1]; rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
        _ ≤ (162 * P3 - 1) * 2 ^ L1 := Nat.mul_le_mul_right _ (by omega)
        _ ≤ R_cur := hR_sp
        _ = 3 * R1 + 2 ^ e1 := h3R1.symm
        _ ≤ 3 * R1 + 2 ^ L1 := Nat.add_le_add_left h2e1_le _
    have hR1_ge : R1 ≥ B1 := by omega
    let B2 := (18 * P3 - 1) * 2 ^ L1
    have h3B2 : 3 * B2 + 2 ^ L1 ≤ 3 * R2 + 2 ^ L1 := by
      calc 3 * B2 + 2 ^ L1
          = (3 * (18 * P3 - 1) + 1) * 2 ^ L1 := by dsimp [B2]; rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
        _ ≤ B1 := by dsimp [B1]; exact Nat.mul_le_mul_right _ (by omega)
        _ ≤ R1 := hR1_ge
        _ = 3 * R2 + 2 ^ e2 := h3R2.symm
        _ ≤ 3 * R2 + 2 ^ L1 := Nat.add_le_add_left h2e2_le _
    have hR2_ge : R2 ≥ B2 := by omega
    let B3 := (6 * P3 - 1) * 2 ^ L1
    have h3B3 : 3 * B3 + 2 ^ L1 ≤ 3 * R3 + 2 ^ L1 := by
      calc 3 * B3 + 2 ^ L1
          = (3 * (6 * P3 - 1) + 1) * 2 ^ L1 := by dsimp [B3]; rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
        _ ≤ B2 := by dsimp [B2]; exact Nat.mul_le_mul_right _ (by omega)
        _ ≤ R2 := hR2_ge
        _ = 3 * R3 + 2 ^ e3 := h3R3.symm
        _ ≤ 3 * R3 + 2 ^ L1 := Nat.add_le_add_left h2e3_le _
    have hR3_ge : R3 ≥ B3 := by omega
    let B4 := (2 * P3 - 1) * 2 ^ L1
    have h3B4 : 3 * B4 + 2 ^ L1 ≤ 3 * R4 + 2 ^ L1 := by
      calc 3 * B4 + 2 ^ L1
          = (3 * (2 * P3 - 1) + 1) * 2 ^ L1 := by dsimp [B4]; rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
        _ ≤ B3 := by dsimp [B3]; exact Nat.mul_le_mul_right _ (by omega)
        _ ≤ R3 := hR3_ge
        _ = 3 * R4 + 2 ^ e4 := h3R4.symm
        _ ≤ 3 * R4 + 2 ^ L1 := Nat.add_le_add_left h2e4_le _
    change B4 ≤ R4; omega
  refine ⟨?_, ?_⟩
  · intro mask
    rcases chooseFourStepTernaryCarry243_nat_step_cf_w18 R_cur e_cur mask hR3 (by omega) hR_big with
      ⟨hs1_1, hs2_1, hs3_1, hs4_1, hsum8, hsum18, h3R1, h3R2, h3R3, h3R4, hR4_n3, _⟩
    let q := chooseFourStepTernaryCarry243 (R_cur % 243) (e_cur % 162) (mask % 16)
    change 1 ≤ q.1 at hs1_1; change 1 ≤ q.2.1 at hs2_1
    change 1 ≤ q.2.2.1 at hs3_1; change 1 ≤ q.2.2.2 at hs4_1
    change 8 ≤ q.1 + q.2.1 + q.2.2.1 + q.2.2.2 at hsum8
    change q.1 + q.2.1 + q.2.2.1 + q.2.2.2 ≤ 18 at hsum18
    let e1 := e_cur - q.1
    let R1 := (R_cur - 2 ^ e1) / 3
    let e2 := e1 - q.2.1
    let R2 := (R1 - 2 ^ e2) / 3
    let e3 := e2 - q.2.2.1
    let R3 := (R2 - 2 ^ e3) / 3
    let e4 := e3 - q.2.2.2
    let R4 := (R3 - 2 ^ e4) / 3
    change 3 * R1 + 2 ^ e1 = R_cur at h3R1
    change 3 * R2 + 2 ^ e2 = R1 at h3R2
    change 3 * R3 + 2 ^ e3 = R2 at h3R3
    change 3 * R4 + 2 ^ e4 = R3 at h3R4
    change R4 % 3 ≠ 0 at hR4_n3
    have hR4_lo := hR4_lo_of e1 e2 e3 e4 R1 R2 R3 R4
      (by dsimp [e1]; omega) (by dsimp [e2, e1]; omega)
      (by dsimp [e3, e2, e1]; omega) (by dsimp [e4, e3, e2, e1]; omega)
      h3R1 h3R2 h3R3 h3R4
    rcases (ih e4 R4 L1 (by dsimp [e4, e3, e2, e1]; omega) (by dsimp [e4, e3, e2, e1]; omega) hR4_n3 hR4_lo).1 (mask / 16) with
      ⟨he_lo, he_hi, hlen_sub, hRfin_3, hRfin_lo, hunwind_sub⟩
    let ch_sub := fourStepTernaryCarryChain k' e4 R4 (mask / 16)
    change e4 - 18 * k' ≤ ch_sub.1 at he_lo
    change ch_sub.1 ≤ e4 at he_hi
    change ch_sub.2.2.length = 4 * k' at hlen_sub
    simp only [fourStepTernaryCarryChain]
    change e_cur - 18 * (k' + 1) ≤ ch_sub.1 ∧ ch_sub.1 ≤ e_cur ∧
      (ch_sub.2.2 ++ [q.2.2.2 - 1, q.2.2.1 - 1, q.2.1 - 1, q.1 - 1]).length = 4 * (k' + 1) ∧
      ch_sub.2.1 % 3 ≠ 0 ∧ ch_sub.2.1 ≥ (2 * 3 ^ 10 - 1) * 2 ^ L1 ∧ _
    refine ⟨by dsimp [e4, e3, e2, e1] at he_lo; omega,
            by dsimp [e4, e3, e2, e1] at he_hi; omega,
            by rw [List.length_append, hlen_sub]; simp; omega,
            hRfin_3, hRfin_lo, ?_⟩
    intro acc Q1 hacc_len hacc_car hacc_eq
    rcases hunwind_sub acc Q1 hacc_len hacc_car hacc_eq with
      ⟨hw4_len, hw4_wt, hw4_car, hw4_eq⟩
    let w4 := acc ++ zeroRunsSuffix ch_sub.2.2
    change w4.length = e4 + 1 at hw4_len
    change parityWeight w4 = parityWeight acc + 4 * k' at hw4_wt
    change affineCarry w4 < 16 * 2 ^ e4 at hw4_car
    change 3 * R4 + 2 ^ e4 = 3 ^ (4 * k' + 1) * Q1 + affineCarry w4 at hw4_eq
    rw [h3R4] at hw4_eq
    let w3 := (w4 ++ List.replicate (q.2.2.2 - 1) false) ++ [true]
    let w2 := (w3 ++ List.replicate (q.2.2.1 - 1) false) ++ [true]
    let w1 := (w2 ++ List.replicate (q.2.1 - 1) false) ++ [true]
    let w0 := (w1 ++ List.replicate (q.1 - 1) false) ++ [true]
    have hw_out_eq : acc ++ zeroRunsSuffix (ch_sub.2.2 ++ [q.2.2.2 - 1, q.2.2.1 - 1, q.2.1 - 1, q.1 - 1]) = w0 := by
      rw [zeroRunsSuffix_append_and_inj_w18.1 ch_sub.2.2 [q.2.2.2 - 1, q.2.2.1 - 1, q.2.1 - 1, q.1 - 1]]
      dsimp only [zeroRunsSuffix, w0, w1, w2, w3, w4]
      simp [List.append_assoc]
    rw [hw_out_eq]
    have hc1_t : affineCarry [true] = 1 := rfl
    have hw1_t : parityWeight [true] = 1 := rfl
    rcases affineCarry_append_replicate_false w4 (q.2.2.2 - 1) with ⟨hwt_z4, hcar_z4⟩
    have hlen_z4 : (w4 ++ List.replicate (q.2.2.2 - 1) false).length = e3 := by
      rw [List.length_append, hw4_len, List.length_replicate]; dsimp [e4, e3, e2, e1]; omega
    have hlen_w3 : w3.length = e3 + 1 := by dsimp [w3]; rw [List.length_append, hlen_z4, List.length_singleton]
    have hwt_w3 : parityWeight w3 = parityWeight w4 + 1 := by dsimp [w3]; rw [parityWeight_append, hwt_z4]; rfl
    have hcar_w3 : affineCarry w3 = 3 * affineCarry w4 + 2 ^ e3 := by
      dsimp [w3]; rw [affineCarry_append, hcar_z4, hlen_z4, hc1_t, hw1_t]; omega
    rcases affineCarry_append_replicate_false w3 (q.2.2.1 - 1) with ⟨hwt_z3, hcar_z3⟩
    have hlen_z3 : (w3 ++ List.replicate (q.2.2.1 - 1) false).length = e2 := by
      rw [List.length_append, hlen_w3, List.length_replicate]; dsimp [e3, e2, e1]; omega
    have hlen_w2 : w2.length = e2 + 1 := by dsimp [w2]; rw [List.length_append, hlen_z3, List.length_singleton]
    have hwt_w2 : parityWeight w2 = parityWeight w3 + 1 := by dsimp [w2]; rw [parityWeight_append, hwt_z3]; rfl
    have hcar_w2 : affineCarry w2 = 3 * affineCarry w3 + 2 ^ e2 := by
      dsimp [w2]; rw [affineCarry_append, hcar_z3, hlen_z3, hc1_t, hw1_t]; omega
    rcases affineCarry_append_replicate_false w2 (q.2.1 - 1) with ⟨hwt_z2, hcar_z2⟩
    have hlen_z2 : (w2 ++ List.replicate (q.2.1 - 1) false).length = e1 := by
      rw [List.length_append, hlen_w2, List.length_replicate]; dsimp [e2, e1]; omega
    have hlen_w1 : w1.length = e1 + 1 := by dsimp [w1]; rw [List.length_append, hlen_z2, List.length_singleton]
    have hwt_w1 : parityWeight w1 = parityWeight w2 + 1 := by dsimp [w1]; rw [parityWeight_append, hwt_z2]; rfl
    have hcar_w1 : affineCarry w1 = 3 * affineCarry w2 + 2 ^ e1 := by
      dsimp [w1]; rw [affineCarry_append, hcar_z2, hlen_z2, hc1_t, hw1_t]; omega
    rcases affineCarry_append_replicate_false w1 (q.1 - 1) with ⟨hwt_z1, hcar_z1⟩
    have hlen_z1 : (w1 ++ List.replicate (q.1 - 1) false).length = e_cur := by
      rw [List.length_append, hlen_w1, List.length_replicate]; dsimp [e1]; omega
    have hlen_w0 : w0.length = e_cur + 1 := by dsimp [w0]; rw [List.length_append, hlen_z1, List.length_singleton]
    have hwt_w0 : parityWeight w0 = parityWeight acc + 4 * (k' + 1) := by
      dsimp [w0]; rw [parityWeight_append, hwt_z1, hwt_w1, hwt_w2, hwt_w3, hw4_wt, hw1_t]; omega
    have hcar_w0 : affineCarry w0 = 3 * affineCarry w1 + 2 ^ e_cur := by
      dsimp [w0]; rw [affineCarry_append, hcar_z1, hlen_z1, hc1_t, hw1_t]; omega
    have hcar_w0_lt : affineCarry w0 < 16 * 2 ^ e_cur := by
      rw [hcar_w0, hcar_w1, hcar_w2, hcar_w3]
      have he4_le8 : 2 ^ e4 ≤ 2 ^ (e_cur - 8) := pow2_mono_nat (by dsimp [e4, e3, e2, e1]; omega)
      have he3_le5 : 2 ^ e3 ≤ 32 * 2 ^ (e_cur - 8) := by
        have h := pow2_mono_nat (by dsimp [e3, e2, e1]; omega : e3 ≤ 5 + (e_cur - 8))
        rwa [Nat.pow_add 2 5 (e_cur - 8)] at h
      have he2_le6 : 2 ^ e2 ≤ 64 * 2 ^ (e_cur - 8) := by
        have h := pow2_mono_nat (by dsimp [e2, e1]; omega : e2 ≤ 6 + (e_cur - 8))
        rwa [Nat.pow_add 2 6 (e_cur - 8)] at h
      have he1_le7 : 2 ^ e1 ≤ 128 * 2 ^ (e_cur - 8) := by
        have h := pow2_mono_nat (by dsimp [e1]; omega : e1 ≤ 7 + (e_cur - 8))
        rwa [Nat.pow_add 2 7 (e_cur - 8)] at h
      have hp_ecur : 2 ^ e_cur = 256 * 2 ^ (e_cur - 8) := by
        conv => lhs; rw [show e_cur = 8 + (e_cur - 8) by omega, Nat.pow_add]
      have hZ_pos : 2 ^ (e_cur - 8) ≥ 1 := pow2_pos_nat _
      have hc4_le : affineCarry w4 < 16 * 2 ^ (e_cur - 8) :=
        Nat.lt_of_lt_of_le hw4_car (Nat.mul_le_mul_left 16 he4_le8)
      rw [hp_ecur]
      generalize 2 ^ (e_cur - 8) = Z at hZ_pos hc4_le he3_le5 he2_le6 he1_le7 ⊢
      omega
    have hkey_w0 : 3 * R_cur + 2 ^ e_cur = 3 ^ (4 * (k' + 1) + 1) * Q1 + affineCarry w0 := by
      have hw3_eq : 3 * R3 + 2 ^ e3 = 3 ^ (4 * k' + 2) * Q1 + affineCarry w3 := by
        calc 3 * R3 + 2 ^ e3 = 3 * (3 ^ (4 * k' + 1) * Q1 + affineCarry w4) + 2 ^ e3 := by rw [hw4_eq]
          _ = 3 ^ (4 * k' + 2) * Q1 + (3 * affineCarry w4 + 2 ^ e3) := by
                rw [Nat.mul_add, ← Nat.mul_assoc,
                    show 3 * 3 ^ (4 * k' + 1) = 3 ^ (4 * k' + 2) by rw [Nat.pow_succ 3 (4 * k' + 1), Nat.mul_comm],
                    Nat.add_assoc]
          _ = 3 ^ (4 * k' + 2) * Q1 + affineCarry w3 := by rw [hcar_w3]
      rw [h3R3] at hw3_eq
      have hw2_eq : 3 * R2 + 2 ^ e2 = 3 ^ (4 * k' + 3) * Q1 + affineCarry w2 := by
        calc 3 * R2 + 2 ^ e2 = 3 * (3 ^ (4 * k' + 2) * Q1 + affineCarry w3) + 2 ^ e2 := by rw [hw3_eq]
          _ = 3 ^ (4 * k' + 3) * Q1 + (3 * affineCarry w3 + 2 ^ e2) := by
                rw [Nat.mul_add, ← Nat.mul_assoc,
                    show 3 * 3 ^ (4 * k' + 2) = 3 ^ (4 * k' + 3) by rw [Nat.pow_succ 3 (4 * k' + 2), Nat.mul_comm],
                    Nat.add_assoc]
          _ = 3 ^ (4 * k' + 3) * Q1 + affineCarry w2 := by rw [hcar_w2]
      rw [h3R2] at hw2_eq
      have hw1_eq : 3 * R1 + 2 ^ e1 = 3 ^ (4 * k' + 4) * Q1 + affineCarry w1 := by
        calc 3 * R1 + 2 ^ e1 = 3 * (3 ^ (4 * k' + 3) * Q1 + affineCarry w2) + 2 ^ e1 := by rw [hw2_eq]
          _ = 3 ^ (4 * k' + 4) * Q1 + (3 * affineCarry w2 + 2 ^ e1) := by
                rw [Nat.mul_add, ← Nat.mul_assoc,
                    show 3 * 3 ^ (4 * k' + 3) = 3 ^ (4 * k' + 4) by rw [Nat.pow_succ 3 (4 * k' + 3), Nat.mul_comm],
                    Nat.add_assoc]
          _ = 3 ^ (4 * k' + 4) * Q1 + affineCarry w1 := by rw [hcar_w1]
      rw [h3R1] at hw1_eq
      calc 3 * R_cur + 2 ^ e_cur = 3 * (3 ^ (4 * k' + 4) * Q1 + affineCarry w1) + 2 ^ e_cur := by rw [hw1_eq]
        _ = 3 ^ (4 * (k' + 1) + 1) * Q1 + (3 * affineCarry w1 + 2 ^ e_cur) := by
              rw [Nat.mul_add, ← Nat.mul_assoc,
                  show 3 * 3 ^ (4 * k' + 4) = 3 ^ (4 * (k' + 1) + 1) by
                    rw [show 4 * (k' + 1) + 1 = (4 * k' + 4) + 1 by omega, Nat.pow_succ 3 (4 * k' + 4), Nat.mul_comm],
                  Nat.add_assoc]
        _ = 3 ^ (4 * (k' + 1) + 1) * Q1 + affineCarry w0 := by rw [hcar_w0]
    exact ⟨hlen_w0, hwt_w0, hcar_w0_lt, hkey_w0⟩
  · intro m1 m2 hm1 hm2 hgaps_eq
    rcases chooseFourStepTernaryCarry243_nat_step_cf_w18 R_cur e_cur m1 hR3 (by omega) hR_big with
      ⟨hq1_1, hq1_2, hq1_3, hq1_4, _, hq1_sum18, h3R1, h3R2, h3R3, h3R4, hR4_n3, hbit_inj⟩
    rcases chooseFourStepTernaryCarry243_nat_step_cf_w18 R_cur e_cur m2 hR3 (by omega) hR_big with
      ⟨hq2_1, hq2_2, hq2_3, hq2_4, _, _, _, _, _, _, _, _⟩
    let q1 := chooseFourStepTernaryCarry243 (R_cur % 243) (e_cur % 162) (m1 % 16)
    let q2 := chooseFourStepTernaryCarry243 (R_cur % 243) (e_cur % 162) (m2 % 16)
    change 1 ≤ q1.1 at hq1_1; change 1 ≤ q1.2.1 at hq1_2
    change 1 ≤ q1.2.2.1 at hq1_3; change 1 ≤ q1.2.2.2 at hq1_4
    change q1.1 + q1.2.1 + q1.2.2.1 + q1.2.2.2 ≤ 18 at hq1_sum18
    change 1 ≤ q2.1 at hq2_1; change 1 ≤ q2.2.1 at hq2_2
    change 1 ≤ q2.2.2.1 at hq2_3; change 1 ≤ q2.2.2.2 at hq2_4
    simp only [fourStepTernaryCarryChain] at hgaps_eq
    have hfour_eq : ∀ (xs ys : List Nat) (a1 b1 c1 d1 a2 b2 c2 d2 : Nat),
        xs ++ [a1, b1, c1, d1] = ys ++ [a2, b2, c2, d2] ->
        xs = ys ∧ a1 = a2 ∧ b1 = b2 ∧ c1 = c2 ∧ d1 = d2 := by
      intro xs ys a1 b1 c1 d1 a2 b2 c2 d2 h
      have h1 : (((xs ++ [a1]) ++ [b1]) ++ [c1]) ++ [d1] = (((ys ++ [a2]) ++ [b2]) ++ [c2]) ++ [d2] := by
        simp [List.append_assoc, h]
      rcases list_append_singleton_inj_w18 _ _ _ _ h1 with ⟨hp3, hd⟩
      rcases list_append_singleton_inj_w18 _ _ _ _ hp3 with ⟨hp2, hc⟩
      rcases list_append_singleton_inj_w18 _ _ _ _ hp2 with ⟨hp1, hb⟩
      rcases list_append_singleton_inj_w18 _ _ _ _ hp1 with ⟨hxy, ha⟩
      exact ⟨hxy, ha, hb, hc, hd⟩
    rcases hfour_eq _ _ _ _ _ _ _ _ _ _ hgaps_eq with ⟨hsub_eq, hs4_sub, hs3_sub, hs2_sub, hs1_sub⟩
    change q1.2.2.2 - 1 = q2.2.2.2 - 1 at hs4_sub
    change q1.2.2.1 - 1 = q2.2.2.1 - 1 at hs3_sub
    change q1.2.1 - 1 = q2.2.1 - 1 at hs2_sub
    change q1.1 - 1 = q2.1 - 1 at hs1_sub
    have hq_eq : q1 = q2 := by
      rcases hq1_p : q1 with ⟨a1, b1, c1, d1⟩
      rcases hq2_p : q2 with ⟨a2, b2, c2, d2⟩
      rw [hq1_p] at hq1_1 hq1_2 hq1_3 hq1_4 hs1_sub hs2_sub hs3_sub hs4_sub
      rw [hq2_p] at hq2_1 hq2_2 hq2_3 hq2_4 hs1_sub hs2_sub hs3_sub hs4_sub
      dsimp at hq1_1 hq1_2 hq1_3 hq1_4 hq2_1 hq2_2 hq2_3 hq2_4 hs1_sub hs2_sub hs3_sub hs4_sub
      have ha : a1 = a2 := by omega
      have hb : b1 = b2 := by omega
      have hc : c1 = c2 := by omega
      have hd : d1 = d2 := by omega
      rw [ha, hb, hc, hd]
    have hmod16_eq : m1 % 16 = m2 % 16 :=
      hbit_inj (m1 % 16) (m2 % 16) (Nat.mod_lt m1 (by decide)) (Nat.mod_lt m2 (by decide)) hq_eq
    let e1 := e_cur - q1.1
    let R1 := (R_cur - 2 ^ e1) / 3
    let e2 := e1 - q1.2.1
    let R2 := (R1 - 2 ^ e2) / 3
    let e3 := e2 - q1.2.2.1
    let R3 := (R2 - 2 ^ e3) / 3
    let e4 := e3 - q1.2.2.2
    let R4 := (R3 - 2 ^ e4) / 3
    change 3 * R1 + 2 ^ e1 = R_cur at h3R1
    change 3 * R2 + 2 ^ e2 = R1 at h3R2
    change 3 * R3 + 2 ^ e3 = R2 at h3R3
    change 3 * R4 + 2 ^ e4 = R3 at h3R4
    change R4 % 3 ≠ 0 at hR4_n3
    have hsub_same : (fourStepTernaryCarryChain k' e4 R4 (m1 / 16)).2.2 =
        (fourStepTernaryCarryChain k' e4 R4 (m2 / 16)).2.2 := by
      dsimp only [q1, q2] at hq_eq
      simpa [e4, R4, e3, R3, e2, R2, e1, R1, q1, hq_eq] using hsub_eq
    have hR4_lo := hR4_lo_of e1 e2 e3 e4 R1 R2 R3 R4
      (by dsimp [e1]; omega) (by dsimp [e2, e1]; omega)
      (by dsimp [e3, e2, e1]; omega) (by dsimp [e4, e3, e2, e1]; omega)
      h3R1 h3R2 h3R3 h3R4
    have hdiv_lt : ∀ m : Nat, m < 16 ^ (k' + 1) -> m / 16 < 16 ^ k' := by
      intro m hm; rw [Nat.pow_succ] at hm; omega
    have hdiv_eq : m1 / 16 = m2 / 16 :=
      (ih e4 R4 L1 (by dsimp [e4, e3, e2, e1]; omega) (by dsimp [e4, e3, e2, e1]; omega) hR4_n3 hR4_lo).2
        (m1 / 16) (m2 / 16) (hdiv_lt m1 hm1) (hdiv_lt m2 hm2) hsub_same
    have hdm1 := (Nat.div_add_mod m1 16).symm
    have hdm2 := (Nat.div_add_mod m2 16).symm
    rw [hdiv_eq, hmod16_eq] at hdm1
    exact hdm1.trans hdm2.symm

private theorem fourStepTernaryCarryChain_spec_and_inj_w18 : ∀ k : Nat, fourStepChainPropW18 k
  | 0 => by
    intro e_cur R_cur L1 _ _ hR3 hR_lo
    refine ⟨?_, ?_⟩
    · intro mask; dsimp only [fourStepTernaryCarryChain]
      refine ⟨by omega, Nat.le_refl _, rfl, hR3, by simpa using hR_lo, ?_⟩
      intro acc Q1 hlen hcar heq
      rw [zeroRunsSuffix, List.append_nil, Nat.pow_one]
      exact ⟨hlen, by omega, hcar, heq⟩
    · intro m1 m2 h1 h2 _; rw [Nat.pow_zero] at h1 h2; omega
  | k + 1 => fourStepTernaryCarryChain_step_w18 k (fourStepTernaryCarryChain_spec_and_inj_w18 k)

-- Fast `2^n % 531441` (`3^12`) binary exponentiator & 4-bit (`s = 4`) bottom collision grid:

private def pow2Mod531441Fast : Nat -> Nat -> Nat
  | 0, _ => 1
  | f + 1, n =>
    if decide (n = 0) then 1
    else
      let x := pow2Mod531441Fast f (n / 2)
      let sq := (x * x) % 531441
      if decide (n % 2 = 1) then (2 * sq) % 531441 else sq

private theorem pow2Mod531441Fast_eq :
    ∀ (f n : Nat), n < 2 ^ f -> pow2Mod531441Fast f n = 2 ^ n % 531441
  | 0, n, hn => by
    rw [Nat.pow_zero] at hn
    have hn0 : n = 0 := by omega
    subst hn0; rfl
  | f + 1, n, hn => by
    unfold pow2Mod531441Fast
    if hn0 : n = 0 then
      subst hn0; rfl
    else
      have hlt_half : n / 2 < 2 ^ f := by rw [Nat.pow_succ] at hn; omega
      have ih := pow2Mod531441Fast_eq f (n / 2) hlt_half
      have hsq_eq : ((2 ^ (n / 2) % 531441) * (2 ^ (n / 2) % 531441)) % 531441 =
          2 ^ (2 * (n / 2)) % 531441 := by
        rw [← Nat.mul_mod, ← Nat.pow_add, show (n / 2) + (n / 2) = 2 * (n / 2) by omega]
      simp only [hn0, decide_false, Bool.false_eq_true, ite_false]
      if hodd : n % 2 = 1 then
        simp only [hodd, decide_true, ite_true, ih, hsq_eq]
        rw [Nat.mul_mod 2 (2 ^ (2 * (n / 2)) % 531441) 531441, Nat.mod_mod, ← Nat.mul_mod,
            show 2 * 2 ^ (2 * (n / 2)) = 2 ^ (2 * (n / 2) + 1) by rw [Nat.pow_succ, Nat.mul_comm],
            show 2 * (n / 2) + 1 = n by omega]
      else
        simp only [hodd, decide_false, Bool.false_eq_true, ite_false, ih, hsq_eq]
        rw [show 2 * (n / 2) = n by omega]

private def bottom4BitBlock0 : List (List Nat) :=
  ([
    (27920638636988509489943263916420560071542226440843420066303447140812816837801044546568183653641798417428701685218948413054907329669378674951691167215177011722470863834545577250271208224199035889148077772705028662224277761842648848412325730384104275748146721581, 29394113482145184093316976652799317271878532518898994910252042679349978127997687267812350939950887510209234039322645832188927859730996280737341121631308404569814965512096503716153922120785957674480562057484382583693203740169677933953492145142547559148419622666, 32768624962091892555401038031723851842200820624087683608367203353559350696925456701301935134808525225063314607106731970811230055660755589268983013618251223827720891105358915132803460478100641666792446513257477659648068350415755664265876963038479934535761404681),
    (22669256026905202746474082078674493269440191074294521182255539652664228824803814143829554699459787884849854607745773432289862240219245253237267207283874036918714809493327664820754429294115746620596253838533128124250508636507042519410136334940287248801293933593, 32795070298479242196318429280603619072942498015147760634227856103783118603652379524467949615407610361934277650493127382908238489952273955837781258666881992102896246848978596639805042154535463727575248928431789561601364276079278916750756529957261178534818231055, 35189836341658907066032381993359479610144038590765687163838668327048642441798002608982195499452402588437205406745125614234633683856569368805054764294977594054055588697279400293137458430235322886131122967104026495822121674939117177084362867650934223755199845652),
    (33750115484755161798922409345157037606142837243641200654982392794041373709048267953153106220209394659663530609647197635246265394753023698461168502926181288349291672800975144864408354202319500899428507807330887833276695548017852959887392885144025634303442296083, 38046490170023136312178581593047205469060321749299512337267202990268902547925148118870982165800658179005231135828803687239501888656752661241109850891089052012156817380804823229642943040461575295272668354284605871745211537745590457739990769127469609670881651234, 27954466454090861371200543326936300415654329493047536215254791533758084664612379466583350387672901718087216953990223004190302438661013996932710904602818682856253939751440363366529503168868015668474904692053364987683607573233211670359428822798514706302710853153),
    (35208568363394579029505603989824511612234514576593967736759720720616746588403960934077978513987199839237469260120474389276502666808745378670966614699975240170833020344198640682832008377789905920392492939228411793963493851720301867124305830558250097932394636573, 26995403547547114463590369578081342796370347158320310731196998422475014821326878385839480703739834840118973178141137888096562104747065589948424305799230270005716272338927595467360760574181610556525194570267193393936566435032290474481450471998641571553056070415, 31336559229396342871890378479454989786901981216905592228673032942355609728041235048365750563696181283045840372677539261263197546799834076374537633408213557459784688693189337198624702149317689058006996485829922054131824387532462512573972281808785985831214003737),
    (27935661148318729469488393001339917973779585855413587136239748615272747162866939954010490470976449146101200123609866599290197226424551994014201006138317113881520132666602875486517525603539543560590301449374730586144007318394014204337667184522896192639241298452, 16880864956588484977132438503812640906258072588443055585632178569018497281718594440754905434175722590268228545124915075710668447965438998115667230947885154908778144054851294747138337928228541377010772713887563900391570025226529230675006634356996415159885369873, 36614314060524174048203195016271053137875179802262261506717340787881764482773687253274742066990102690894162907809873467816991084611783136450493748274592757170192215847057379404966062383873729639962705133078642086759291260591211966720717313398362702368407960855),
    (34227077956850063487285387696261208405431698620148320269217636241323623355875476457545658003471143161847163586415905503026044129048025055008385254341692452362362229665897035414240101781116693988262197160196661018873547671646245127487656107216442556098831134480, 38523232324835954173762418579696052544820098777147797540837358066186401702984700398196764752978061635060154015562212089645931215399648695471880360780070421203039603791096755180520006715310811670081432269993319275645981947399062322318897124610683228084840247581, 29409136394183624102027099594608666358594624806059022909156736438282376168233642226620126696300931636262689790590658330605924236708928067108848834489054726976631050541379146790324424361393639809171942847050328519929970146260902431842887986386275233678933824788)
  ]).map unpackRow81W18

private def bottom4BitBlock1 : List (List Nat) :=
  ([
    (19264420417178758344940236835805948840047901702449029576514828762332684028524797301854237259746997479058366142949014058583820908539137412020452550799199468504937044732881998794932939904720120980328420184471204689882165602413114411747412443233217697434489792803, 37110074132297404871896526254545373066991746085287562243829202876004377896641278613307030390355051966386449303653356755074582799879411128674166485213872037023843818388804820608609244428284754227794316563904281848348950273769384656415312283630632201619022291477, 21222167522439977534015134617365631653037404747158910940234937442470842304550672280443906008668349896041303255559986719625593296050668989135849995110864283788504270744717796314642984373621245919305210729601108177155811600057163690582361133320351669836335093010),
    (12055334740833586380086490829991301573680017717296297327222507906179644770437673511094603591550051690567540764161875891239006166139533195429083891817095946807589573410272027862176923244516162807360707554614200259899232009429806600731374435416435716654912707094, 32794849950981038276404602104241665423865548991789942810305738077877262427127981373603650901449270294164746217441526216878039202700607290403269251894869299821492862205600127460718280349600827418487388168606965792823762555291863417505051517770686537943031618317, 31347923029894018623078430901042383237371665889967284663991272822524816077317467554497549647929638741718272192296195649766137105315505905723715709106053905307376149881540128384669293934344218004395770301689982181807193260677816679299611849184628421419653930510),
    (30860015597223722317452572114903562013883708946979758096813756449733041972094119812246401939208704156873207854324478328834488651443577958603077463227895074698341252292195789778977919006664982768564978422460073936262847106938659896959576642313942571924576083482, 29420499992877923328082416169474628916747475488334963668527311524733853207179400639373904908436882494814571818937114015700330624095757240657662810152429194229938270081966075951035644439127913124805289447192171515278148202299035127237572152423508460499079339529, 29897051611710857687655040784094235461191282641048757645173148349349519681765454173701255020557048493216862290012423758462852362286509292982055265864437507214118362459210292804461815132521048761064831084253625653207459661319028722326517317179520821943811577610),
    (29405390049443070494818979450111772818887077410943291375416570798228902993936013010089391478209447716776857923548600523035859739280288232516567528929758690110096349547673482757842694507127543785741720540207836327047101443965665440654360032075531757440989339152, 18327983014156782358530068892375369135952241068799755474719242737226807057781485119376020631317414281718616408294401199374696213475130573453720560492670901240222910185175665818533827249723293569091651587063726921385209244014407653772483704385923975101929630224, 28438731106339042095001996903139325048303962996771471102837813065206409904069943559944776980355550094567174839281365097124233018202601548621491387117552554532396301021856746382604833601855988142802146751976905407155636231903821831446169478171505015815579243276),
    (24097517030001188057546938915847694913603847943951777728640788998106663266001197856727995364717223383843234930391445893318619824576120889812052080418221767986597690292044360406034051524876922755611303059293548866768586505066613577861654456903453025657534623788, 25529553725306234022844159598614428596796925777860866121168745208841953074642876053822887641207673117921396031143441488809578756590204472784969296582834523436986198437771988969919878937954328459855245237547017885309261972110165562731606536448100772989854298138, 32723536132431456758035663345156601653332637543014452279661217864496866724000036985450569838218607831088139009633015671513570803090570576445933364714413026704536186207697258586647467591786606183229807482641740276516486466497506683120568533630991224434128788750),
    (28453826582199852019053419805475448270045953012483776347578329869854274777248531781905841756001226508397110218157188476130478173511444603784638650332422540715947648743217877034105360826342492032917243482682209092005323930654864372205241457965991121881479985966, 33746663060174299953098834288537873515138944926548214104317281018303512572880764114709511933115726410202775118904611497514280961777256555336053791440252073521846023292792202983627937559309223171597129252101000444285123965532666608694859066014195623612126802460, 31314109620174007159381725941268248793846692443344767650778244822688553509476290631622461658026329411425361287826692755230614012991521742559353256816729313681289713004687494146604456005076889099998641522843726549759163471386473901391919888371608280360293895179)
  ]).map unpackRow81W18

private def bottom4BitBlock2 : List (List Nat) :=
  ([
    (19283137915611202689433633039878863820412976903692375305392519606198375245101876348090409259554995100521109302305600220840337604517817380150984686082901823491294605718411104277758242438271149204596910659309597066256314663180424644204450770829238291982807802391, 20734075629949170165101816698642182612109911862602804762284194879208323337348730911732672316722597922387000496310288944701413678961569699277796495666422880505646799834163171389451393015699428980335875611854034686370987159004945472166523599277316618872569607988, 29870723925746074464531894567693115067774300783898775341253318717453727941380272407490266757429413778080609161940373603169510303881744239576106530767635618641969734940911562539874291029850883046543888243572920095432675970024653707122676357005367300956301694730),
    (28450095589023918519611111486924490817364101127722519647855896460470227027911497350170820589761751141033059998149678395451594764781039375987949128368745197903044564983069402275396450477475826935903794117160673018917825203489429246932103379624474464482057392905, 12539606490825185942128952325165477647814189145638893492974774675605875116210948589741148355477172013858079497084345406095725237891947490933348903905101736922024011708617520343215011295100020277453140884951322300164317415172953320513163265779163696266137376266, 29405301671582957327873111931285367672073693530911797869213605877808074664792548846989965542384588939721744934936505770318153124976961811101607544849855260919884587118545217376682078535085093771247484244423831183976743739222661560719293050930089174897050062091),
    (24112568092519873206672213541842788273820556197531918278365981387000070153135715330035611113884349595720582010893029897028471574988184158752992531407360796771042426866601577617444876967926340016158699758932488930696588990414122484609117836914311308554282735372, 29416665360442867213203831739247218876445970864981522132632833843754924368411799778830525393495661712392948228159759135048606324723331866509956847134082491014740172443702574492678735814964620722775613242794218262644620390250786793329800934269323862836162473749, 24089928379808638125601732072901479255320886567254103660174645403926220051958905232866646974836219989524685412395947106792623057447236448459981525422871273392338289191967130277388689780429510994138038889896002281913493704908301051494596791579800276671464616480),
    (17843740536481045897822097933881445141015726082767680726967046032435424318440263367569129498865216462161372570067004534484381554581079771121236878826894256086974359552045132053539504482395400582315830773762144856635633712231798743130311788156153061260664972563, 32746161635736126379458163038898834741095667910806157126311148022902580290693205313384941169318540523263508504591959366321830058245641563979181451448827794624937677806147918197459960452760648995932972386315808502191345408861627274302888312113465443743598252554, 23583112137009186570949435454558916799627222413739308214346335535323660776052659453392567105311549866714921298337642674470725443765611991023711285526164210131457529974773589238712238315394493413442043049139101862716049845124666208211979787006825987283867473686),
    (25067818902536025468693297410517025240170080052763609182332153377709327450213935338065275864527056718048918266027770420044895623328210804719156476745743204480944073945090255736620115531941442305779286003515671672609502783418545015380231771916976139621513307680, 29360153869702395259005945032956983209754112297473123945080654383730636545711904891506044972793754282826441317916738088708214296921952341949655807773516304724284810616171702771871909756718859493585037546652343852638848924512838645826915727879081696428454850061, 32783676971273338442950853354073140520643281359637382796499662740624567584823106278501057445915753289713992307683492666344055998779737481725385739149308472541258591960919420497778156771473422564888176026350773895447400546823590939711546615974410229502239518504),
    (29386510915490587898018726197063679698524412129811539542614807933148909879852141866048417755211407124921200885539275058750983919319470789971963774894412659531065075641757278049737817916522099455121005384870829557473603956233399599339424454187800299838867195150, 29904639315234513650516254299374550931710543095218503097917156063489415755283644997832933770678025628518686858194235707240610618317525358957695856470564994669360116619649203546907262276893779057226141897221784823429793943119156877993088926013063041375341650977, 16880879301759729954749275051712375323231328964395029600863184834525742443478566763261550310528351095131389884827081605827223691101323189108439478089793405870012913057234634291943859454326791388103783477567817804235746767711691072021916255328202181170094291509)
  ]).map unpackRow81W18

private def bottom4BitBlock3 : List (List Nat) :=
  ([
    (35681828856677477332135224553795087409565599588903906235743320556054920985519900286259886920199299166025571285095504936205333765863514301735471845424658503881313683871027124970387150920905274971360100988950655128947200515058299143842603339023364496141620419863, 32288107371459292197169144342543070116257470871799035140666437256114722009057851630006629018894343648985865994916638585405412799015125235304284777827310304987423641168679308799890955871613051454482192455338313136345257644495440008562788426929477407104332467979, 30859956288068259312055389366867348072358328207901998800090759092838282895605043391622050927078548584265559596338629392478620556434559990686036310176343441296772376314120914570320075456061628100215388438039454658835737581743632355844063344661299973760172239121),
    (31336646979004963322960064313375309620405198077974867743739831759869110044203046082727839122699915357843308295028570341600442842379049093670200976066045505252399287340400003764552759535706983392866467319445442002571964705980216373319132417077612669649808404759, 27006665138714560319312087335892752785221168958873271273695479705915203580622563817557232430631132875458275159402747997190935280771389902132260136994278324774016610418015042920394569631006319102162058939819926217588734105361615808080064463202086921413849652498, 28453885892473595595971456428179290153722832048976236810877574571520408300111133675182441646007206985024400218598935027711032901556691694537089731890446489620865650770676266434490676812993553203629023423088252089527717029358021744837571534911750993300813399064),
    (18316603918461968709413986390014679504684329427578038441588894873820525709414812179913888341996553589753469831969282047497380621724133025775862483992085797065587281204352022770179309663232349034678854805973529818613510341510559073889565100971364116964580741389, 23616969310327869590335233399223782973852032830075724434357969134076993775439208053153590950826095591332162329871759289064068556095884546610774944718769032096826386473127472945685004052025039930104805125691171633771506226493954047674446615294063070169314628366, 33761773551781828611768480589794615326032576174208487407064485890928379745010276008295750622861954925254751220721424890387897966488380941580555449197895515423337377296054359539280270849039475674752113792082851492210688535423162686732185558753934617307344211210),
    (28404785495638880075377528640336948923123362594478620263666046389321521324250459433697084320824868586223380790864130079043531967586438774139351249996649361616547038437243314237917041551985818955540000936972819655252235495741957978557506218056640475408467373071, 29904419429322808006423293772421496879257101465175624696462511633496903910760601160361840158999781439517362987075633961268348950257765840426065010085618690729728761544417057063472027538344731044699638624862149858557609327602322847379150493060634157348660189713, 22646615397322523196673333025173514570562425750464462295103166266302157360558794442781408016013030796413695864888480719253946263210627617372512340519899719717721186163969506598119254894757290903765856481500323540797656273909288056617117264921510881990574477326),
    (21210759102530020676426000066135395600343222701453171586112153659005822507834883021995302842689427396528743650279040172378475787813447330950671620254819527488490039281711483747752966300235312065560283696797693844720899512628576162520330875133551785963599372304, 14945743496471606667777321758479362263437574321052762518377245671979250451147202242325156767785740972604105574722795135519651296684242110234498435454108177472677271205752271023384838951907789614976341346391442813769986741268715620501594946313837396995164947735, 33750483236697058918226233334387282526952996611146136750660632829192034477916476741278867297781723777341083920075083196618118486065843044475753918038405798794922856925758142579749211592712512156092699087122468226762121607431065944984992622198699556332853538338),
    (13964069543200646678322571726550247924160762265723485371511741327111585376147171024354985605762020120872272148080439435307442097704162187772801728452576433397156409075051950792840060093675446497512073589615379147807299675792888128750011699693365655801721270298, 33739059518225046438666298520049447924973281672820153416225531245874608474840094465748332089265238550030955368508149056553738256206640262749642011007716402595399148110175840437222833681774478562473845916918657786423797326949886757210284372650920593840874857236, 34227107028049552156168294694015127127406367388645908836711073828692798245680125335670268161511178552445296910976537169617846677856259183722866514689680013195852954744779234764893960706954055388641211776646038265932387699327194519640059447381433479948992056842)
  ]).map unpackRow81W18

private def bottom4BitBlock4 : List (List Nat) :=
  ([
    (21222181869857859810325210872119481306500777089569269815947374819895730539803272970542309769702116081775430214133412272443338013818832630050464236195605813825134402686080370605635724472843517522351769868486181028293193529226746001071070909266908121104626500383, 25510703827412146395007471343581050792819899630349365718200663190441261652041199771826999494881764478821212765193954551547893513333546035932888574067481188378422046642814100117331582721695674353034696985585488684346837111840806331981056131291500165559194760201, 35647897910657089900229402933385326995443025994571408078126741617668910065011046534913486961110238030275770889485594733811557199365914064871121846465467313672624040432621256710534426514448405633163375792990778005105328757795848983235423236010739140514734746381),
    (31306536289132953664674944516504576464478321947639502454678889916830124906013617387555099046192713441244867420316975319297649996213818060573632982224465656629080278471085528262551144624533311466006500216800808845132799294108263990368324868199239820307289742613, 32727326689812368181894826809982658518707615799254277102450139239674150410143712907608060960712679803044282655534017018447937429149807015392696395060073529057759161849466507335122954850867024112424500093357836019211496275634612693543281275816402485755144442126, 13986665667478283475222024913851230937460382429309864982236600984478657531045432300927354864942170801725851012217215229409964792401071172548402157161126987262903299250041667286170441311133278648666305259688097563893839646053474808487605541545076759004828669196),
    (27943190515955656978548252995943617824338252690518119178161127749791797117483475920762679323172128995052804031667612389873124101374430101666324151485712406648484156142888312824945958716825749309024062576210173543167765975105163006784651694527264048892697322506, 26526316259616218249559350051685637426891478823652549513078589930821724271027022029399055749482560734574878125578863956321301829384719749831014608435170617710122819562670547192485999335591007098956819612683709769122648181023917872106341922575388878020321218313, 18305342619058639997638750339104234917553897214806146600956398016638292145205119521852470558401466853534446310916892969864207129639686828435674549088814900985755600269144582361515111333472879015405279390951840575487650016877294246863860200647373251666632968970),
    (22665450662312082205222305890971574170318416949188310331361676829724108126793598350757441626785338052564547417108089283228003831202517530694981278663551223839753022298834692079461333597271110900224425822147216630001196169220190985558547080554921295088774419988, 21214578871598141884235207748236620063443388490242162102048523156763023819554768155690559352873907550273088224664131506983222274092692880371897554988260170952996493245042148746475716551206491550186681179876380873342528480667510277246490274174786174753319625751, 34245854309159686917744773246959857980671143311793077781758303986837040447177227389484535237871475033232892065576004442802728556707328004400435666346248956562853836385145299140490960221030401033337329989312612442840267277303948391182059805665921960116820906513),
    (18327835723369757873385387723580167878526870368434093968376810257866710112874076793012638054316039125610376101012381579331866603242048444231293891837716783559047304329348113308822452305699169393258580705515419260678621022939012838479973711916732143423411003153, 26473506176724158230318554191842316727912901950212637186354133812090920091267635908352644944036192178109661925053781113400405249007339959039033108285981014527344078010424664652371681321575899509793701790691522525974361644167701058294498022426272858109871264524, 33761729963600354179504704647787952371909019073738419715932974808490605804046518371781720328659633251096563215560774641944197006228722051854319900022937596629109389615358796280214800332195303615659807367937799537806906376940579471216069560428281679616702289423),
    (34245898011447954072127610910805309667104226578529923522097370520329024412123622981189587441422832803420954601199680202028067966843319290406219049338558970129348901047122060480148709499684123094911201754749895714313825573434528031635705860247871590633699289881, 33746398438724518084781108244787443187797878906940282892356264763495314664833218561916034929008710724977796353519482058446877126967815289918117835334013423934083339373571662751331733289434160867618075516236976210950914067554464702139814361649418160079904575758, 16850739176708631995911154576579605934618267799485595005077368440383549744372699993395389797018128128782736320589411270908010668139150335470873413032801581573554748732733244060770554358791054227686643563001910431358583197805989337480541769013307275410271839504)
  ]).map unpackRow81W18

private def bottom4BitBlock5 : List (List Nat) :=
  ([
    (29874543698177281813888375600324838392600671359360224211592681387901012485354401819586484903467735767220484309478507596059690500945877090480622937531931828836594538395658441487652103280457703336024490508007787862413502230093778745606417822757305036732174770714, 28449845318123980934075743362294589642633551007313378700619222975389929749305702641633451992988223467460708167331414325415211566345481294160529371346653393612245380778350715493188499357467764572764420726196544494486688240291493029905200945569447379590898197002, 24101277662876026200647875667258007804050678771562847008523336213182603235673960204598457883709108899312940689076754174668664632281949032569231319862421381059711226292075223661839106854179836033326906591468722460371147707221665449871638449332522569761253370408),
    (42921076138150646232742265723421239189398577942216342842539029755472615215346516397636151486570858239572301615395073496399511542309253159889018787319549105706117948829559469880236161494324867879937816921405229142118297147644916036731845144858742018513383919887, 24097531378532953443941921126405976452735414978301755966988878091105606790057428826637950957357491245426419518563154041006189353363970750263602285209142701908828486655493472937876960324199880388527832097512858210919777596929442280568702079863728368282242264605, 20715226073471826964640151519642555978103643972159042230133975616206179078328649980142101709420821268069629373569380414629896787078200803102814177153272297846747644612155063980174509016769305861309542670718774179043059579376715719208710590270595386842428545550),
    (27010514063523151703912334086253972815993657721849347022535326234217494581749669695443404957639169668861414830915175822944778729163974707245853656638249710055425704717795731678914084657907262614348709342332119468875901274648627163425811134246181675367919261719, 19767416712352134956774373391838283686019254930569115117434820080875733362065569092522266336850071520005236109302602202264270721285568588959900366771422105937741107451314404697585158782930123601155191676900144336235901266904345708685679466831610396894646053670, 27010484365435604755767584594214539134237693952277044492150305655052887429811909319666284912378584838403750331220628248167814057986083184006151586018131876028662994246034138409443532443870232751118346725853591298683856497484000549631254180329332890372468907289),
    (26526242514676828010058753164495156329907147370436509007220091751095083523602300095759697458958690880473601727049156219503821757013434785699830055788848222412223352945647769752993739962591371040557392831711517943447422600574805681103857685672936808712843831573, 21210846850781262735525235729744639775641872092774767595456401037340061879504904082180724299137910555280635052648324822239002654295979722466828985442786533872109584069873905359352965589224258428265309178084343070615272556674956062621025373589894970883226742027, 26514966860470396396432445917653262631058003648007383268757064429726329964503395648794687163206348361659441774476564006544095470236846463237024476393563441665105919802966079928758842806391788823521118658188188281068939847907636176888928032071845773849008938267),
    (27958228117514826456748431790292502593666440453266228692386104656998784956094435182479755500549216981081856073370144638372067899142487680811180446702964379037420701998462565302432242302425457583102551684678954959309660947902355654476244106410917446236307918091, 40970799856987235490220753982260929431953084359204371111772352165399924994379945031364050058591609064834046214004668511154052599026200892384459398327392499683301488877166000549255832173321759732650478101678019319582781131633487530469428805129369693614007913994, 38564707385061468884353232251127409257370961995064119424582616027087665932403844296953758213302808828839089777609614769793359809221401089502002714996638140470189295210264358296340298250038724033244747757268769668588198126747873967050610366209123699170736874251),
    (19771207156310551784390394905426117594332459135793665580300774096529256569351244021080209510141476501122673520883671492193630586776382536214704298502940596279348287725719161093713355265475731937578732577210528286666593036545902269172078847275623594190240025610, 15429934199040796602892827590263299250934865207840572326045372162552451062353963015573196850422144555487484230650235058448774304707913941732880445222676468020473088213939973383541275519745766476849560200507589789904896708748974761499972237015609068112326700582, 39996670364961465643223447156653049673616524043520181343914549769797939101455969361355653819466160890464816004850057558196181066604890829639795341657134230394502397162931175520426894363577178533263743879892026145030224960051283550441962262649551127652028391689)
  ]).map unpackRow81W18

private def bottom4BitBlock6 : List (List Nat) :=
  ([
    (29870811675572741462016044124896894346184618671439722287411957555499488331616974729950840583760122540015722888215831623746049250628538209742314161088959624825786173529661557506456757172400404626449019644875416403591378015294334980628941547470620701682882848526, 25521950556564313627232423020726120262583025856796752558150344070981057894487224347709819586333308490738113288720682738276995055398735140173220540106908074294176830561466977705694096353235153481072319203797630045748678742603777779272252185257818009410641474057, 35670434439606514691002158131996985898818868150999636386039794472877660733158406144185730993273234366314964966754483067654543903838999332052911996475799447025097649163323753182501511728125938686952321618614260247228883002378438334444807102808069864221780613136),
    (22642869259775281777359004364754753543549355299757902106425992517011589631605927142892232295130422851396944663050367352032522855861642270170106032252549873558445676789389314798880627201127578439880531568099012729925286265117702176699123306679153675764818842379, 27920624292938108882578539065120161473960290710622791805740694817719564186411996396514447413885706173811516530392302402470308372328057230789609972571735801639512636252320161283463485623308335054373592259626101155434405373478456768020042648849826369553750235920, 32273143716889851662115824104564261647641333969413559037577037243171078431855986581873513763588667908392564798291996855313147818561297866273573248293513044976795882371732950215044151829383008332455303146220881668596905242241277622295086284729547161970327757594),
    (32779945578496974165162167642655485365678305975167899999102625476513718518627536819489345643966502757096922295365464951886092667041499653248095096731481515372802241740947189611239818109395360525516938994597579412646673246833849217133430838111591303999293700109, 32299456481774624910474292698017445427244513139596500149771926374594665656515143079708772871276480404785634394247750728126497971922834269303966507099595517727394952718481923736013602758260301234400397482179512654519434073961003450545496200952535337791451504397, 16396593148622371057034985175670761640894099918369882125984429980322779485572755336738276658461965400653208938685698779359151305952942360630816120355938449884951520686491615057016502996387884470836110861540926060983837917219108995577113048534064211700530092820),
    (25499369178398206663737668442727678552216978907058154465615626915142977561403553542602798437777398459144353461651336816839924974285150737656590649914818125465716857899250099688258051979564391958098761564806669724864444526797088634236867744153230482219535179027, 26976641914075811826927888167435619329257205256670326243396043677826500820324079243322735123450980996819754774281049802696140357101987631497168337530919934941531243985434351090645840796778980322067772362089123567019386269092782049538341644774310979292338725914, 25563396174207071584807623366411433167038029626947497543648895888569835251695316535851057915701006183336603930244512533252814998135018882801148217882776552870848108978488634263206347058375889927532225939543400538117610574991459478495736619811509036833904727568),
    (27958316212806629786974307386976195189293371281991767226229613694577114689663012304749044927637601942838577726630716215489792031740082905884456617005966163468653612319932164489724871492259531123399671226158773649364087462717255535604283954934328345541724808459, 34159363245534770955725755764647787592373781924498961404069574196645806452718062806301531968976937722743611964044889461985046929381977194805630358812654411313969125756418977509231154418835627326598942597885723255740573386848318068651339324079430357628916220188, 29904727926691644283991685420349256527634886580065455243682042003239180423119223250435644496457325740742007638845676588090696831857239280378504501398589897117629095206523352024316221074846380618719355907835896784502632090908818396251646932057321961506267143178),
    (29397890009160313628331939832930568783376814933845543586915064490758804680884440149948505446737565985939201995780968174996242894007431482435177416320104454033931208512218087774238134851011043604201943837565363289987646578930484481296648511130233913208603622197, 24086108607393174443992768222512425460274774671494163278640715258731539571855077879147645298077233716462685275526574423121397365529908849263902354085243590209542866642197827081230835856055907939537130568754942128482875524614117111467449715830413245424997504018, 23613281879616692120685095178038704818508720812929564636139001030488372960766610883663907673400703067058388880704169646764853287614252261455027661783218321260809314428269631789987126000585256245804270442874400241765004728862551327921656068347192460054135969041)
  ]).map unpackRow81W18

private def bottom4BitBlock7 : List (List Nat) :=
  ([
    (35659114713050944160267530749170407895356397308244800781761338638224727727559519548901879560486831297114806632372807950625578205928832366441677065650388489477169829396501535064375201091661404785073902269091325310200446788913522167993944695889872350627967152137, 28419969815872960523363346317686542826225371730792945804469703671675666674199526415657861430824997392592466120060353516342205914764478830336496828751277256579180091682356175816864950696803881038536894807536112591723954337859537486294121524067526850713056579340, 35689093398801482033346524845235793730667583160409274156487264555015792865468232265816824776547905101046767257867502454053340295387679626107675000372874910243236878524267499921409664046302599792483398750643674295981789290901047753312368381613038551500109321996),
    (29371415172239444218940744459347113735378844110539525930537360560304584813177821980034877279637573139385453515807147124262022186307558925920428639127543239103762556390455628051556899320342040565594205010378419037848168175402680363145035713892169483836606648332, 24112436294484943965202554501421533479493580017033107745741074525160310665520748041261462801150375418715616483087256358795493547707746935277426968865502553052775268913811646476616483732106548118634444677193153985778238324568702547878459758657325626696559505690, 34170624548516218271969509948308714911012084738886868869868833677249779835445516047525959201588732186172483859820634719056661058140597772839521575057134931675549791486948579939549134097147461014935044892563339093514081809701095671702368153730457256123397056541),
    (39531330135079898498398536483265065012224005630848120525901145540511304783586069319833276857759295471844130308473953016599494190376725819984607309692000027338191498199444453532431868210557142313088650727413992617353919938592731979107991317103718831055184402453, 25552149763899211987694778189502896401526957284622551605967509785004237200026368766799081539305297402006834193121860039431019631076193255448435070459312754858705018016067482772025072690387182403295855518176670841620812692149160932756684396466768802538834304019, 27010426142090764499112259454043079101503384806959309968086950884577739360607762013117749073734883205220686425794018992586526780566046723114267231493308365466030876998056542605236343053853043433455815467302994337924889756126639870400725943309037422209670589220),
    (34204482063492450459088452820959501767983758126091396618701637451129170474407840540586031530648964991808968031832279930552351359062698667681685502833989588042886019796866965473745011650090252164832472581821176601642655076145332455005861761324543639011121239565, 32757408050750422140077592114867034162550168849262209171997012027145538820857561880643899394823901689484704401930686693030411469417060581248112629766672535489585003099297827554624969215652115195117730690102157934931829898046972792159133617332679608518404349715, 32299573871067298844419024624381276357677421966624534140390795834987256790418137751046757847194352005186089594298938708213006109212442714158079583051435671339836822061413417924951528105446082804978437098025635692440258919968571646584861601563561397285056094493),
    (30837434109208483707042022005517382401652362325738074487838311402960783003716994020658975182125794006889916444299249169751321048598624461463516124289459699427332621930742817689241878957912461688580817314703792394571441721077342332907248012139751158641581043214, 28385994708665381792753289506325690353756399812962152000670822194701433746285670932838102911187341091114460037539032250741371118984470711586910483015648735417982942021865502540917051037290004209651384352478273521717965807597828635135765867130961246137938094873, 33746648717243951761274316699359348305345274479764591904752723237001095462533924316931031044124103236633156700075249564701969976875938638586319271579907877818555676175534606671057009755816235226975762812380837518426519182220384586375631537251102914236796837917),
    (37113571058144092747593130701056491685773263942794366960651879045140095388469779234815918049172477624037747768938716155862745562117861823627828867991850834122656867883568612947649613195833379799987254734038442572953279962623932136696301333458016763721736007199, 32749907667481714617641824358597868168194656464396480792242772813601721536773506438100971219944568251783090452353952473619245715049155325210109747276308847453540182220371788797998426665670233294210329814259249930930973159295617839275965209159260779954112241688, 25540844300174966562127190611407932084252785378498686597668993918150427723371631045182955062544028023069072028742913078792666450622166665801553807502465873445812277632312369066437937844771168975763491487107998986106166611762649196517362523694336130623489774090)
  ]).map unpackRow81W18

private def bottom4BitBlock8 : List (List Nat) :=
  ([
    (21203214642861083506069016169888964312902761462998776652429445074719447444145166850554165277017080346483732883899420904823838127073275565955558144138746716737949647705670391907083204593517586265870707031465824789312903314323077549635054202480083718254025449225, 28450109938236551232038305601814566704349828115261310578114618855116853816175889066990182580979837145714600302213093757963591977355112697728373885157513238198919193857336065658623349579293161994693486120210727575257572091290552925140308373537576461975988942107, 16392846663156760047801470169131270084306906651846711152521143845848947874620904316014061521333090872401620157367499277027317919338251471796428016381088433713106587437213110335193516773315368567392335755412493300767559603361017197760562607436988252565190155803),
    (25563425246943480301960802034255184334988706489805472724546483863206164624780784043917088325716410830945673004165108851692277822191234869338426221728871921120853577160717990000903189924522702874170914771764994873604774817023698307453293179796095836098391380234, 24108719167030467661220970137783481391900756640940696541880452777701839936356036025986676791446252941806968789253917298942874085099501448843305771795823092160073493510346772128842140310486251228864627827337455007230653382341685507906105003607727882009878934814, 22657876986246847937425957719529297020455501413114632242744655444737648037238054699351749861646700207371222560926345254537724611902238372031236893856254793778500281829130764010942398757487896485003778615194636230667379107472185591079443373372577957950450506260),
    (38568350740727205721445245558746769883743915124489952837391116353061135277880705297812026566586720904833306684643399734268892817862023839871822677240526471169499823527716844444367042528491672323141843415573909699281885850454201022402522556608295689579220248587, 26526228165019358398881749225089531466791554392663157934979461718046391032217880931349141360881699365387038521789502902569658111152620903752639887524555534616613474830500797079934683873063636788741817164342946513842079599253043610122699094113563141482928214800, 27924414592793944270833331657514473638727513177344685214276957299531338762082974038759896162467160718849043386454922419451510599994488521616404870469263196318053573046339210277724315075390212356158098093101164924366855865015058153550027668232954847005892548880),
    (32261941179362963184897440212448138193558303401813649773526512875989059769180693286974224912024871684043873398099813882178277048210036206855835205685039919229720617791779656205597304778165678462504267977289198572289146866346337919357878356978263652944295377681, 27954407888209717742089767210889862678289195243200850632655423264692727671038308353243962435791519593966571669079576095197993055175299161358967387089845141791024624173634194079708244451404456430745625824797260416300201591503604430466208167350830890408150768917, 26481035744178799968013206995164409903204300667672817569262606145654328763491390092858980429482364999725601318889730814802846389204621852760234722203404681434002208292836314376742701751621513259423788580282370039529834351703654773380126432687267281774128344094),
    (29885892982794716777693579043446438494100955578986479710014675624612333911477762690129880499144690137117606235320766394087258937069184951219549162494671979603106159763054469410435032388005925010413103204086214418978734104372909074056215023782095688419867237145, 32299412893129058368302361849080365060846664214675801875580329894747638473163525281553407860984931445159954696106286619697092105413552277690543040805355720133107737550924233041946680770635985610663045970979068606038544495250785269756785370383844600809015754298, 27006752884274773510456496478824574554806412969735909448071866962810686501293212010367071847224736999906096202537838626001656996180125029734281802243162943218287917283420352457915703560076901808750953842648517226719691790014410333380563732867880382504043946511),
    (35178721585965965848564920228750206944609591418575123361255837838330397290459249979254890627633924190372809798061786762359282053481107881039689426860246453313781722274895877232609040194636330578111877957537367600074232126229488271439222272696176764667433847561, 22184837189296886108427495384717058025266005983933480264434362691990776593169254766070935887956821098000711812716935254877514512426244334256041665836960977078797485805530647156017175271843523983150558092183865602608675543566079525948135348315972737774984762127, 25555719748714646599923319106518314142381283889570530985436473398023541029708406267164340931634859501943833591863075381467353720053783910047526703344023281212426860865317439788078670389022491876470430370321121799888223123564242722587699874588302281639362115629)
  ]).map unpackRow81W18

private def bottom4BitRowAtW18 (r_idx : Nat) : List Nat :=
  let blk := r_idx / 6
  let off := r_idx % 6
  if blk == 0 then listRowAtW18 bottom4BitBlock0 off
  else if blk == 1 then listRowAtW18 bottom4BitBlock1 off
  else if blk == 2 then listRowAtW18 bottom4BitBlock2 off
  else if blk == 3 then listRowAtW18 bottom4BitBlock3 off
  else if blk == 4 then listRowAtW18 bottom4BitBlock4 off
  else if blk == 5 then listRowAtW18 bottom4BitBlock5 off
  else if blk == 6 then listRowAtW18 bottom4BitBlock6 off
  else if blk == 7 then listRowAtW18 bottom4BitBlock7 off
  else listRowAtW18 bottom4BitBlock8 off

/-- `4,374`-bucket (`54 × 81`) multiplicative discrete-log 4-bit (`s = 4`) bottom collision lookup
    modulo `3 ^ 12 = 531441` (`354294 = 4374 * 81`, `stride = 81`): maps bucket `q < 4374` to
    `(b_1, b_2, b_3, b_4)` with `9 ≤ b_4 < b_3 < b_2 < b_1 ≤ 101` satisfying
    `(2 ^ b_1 + 3 * 2 ^ b_2 + 9 * 2 ^ b_3 + 27 * 2 ^ b_4) % 531441 = 2 ^ (81 * q) % 531441`. -/
def bottom4BitBucket531441 (q : Nat) : Nat × Nat × Nat × Nat :=
  unpackQuadW18 (listNatAtW18 (bottom4BitRowAtW18 (q / 81)) (q % 81))

private def checkBottom4BitCellFastW18 (targetPow packed : Nat) : Bool :=
  let b := unpackQuadW18 packed
  Nat.ble 9 b.2.2.2 && Nat.ble (b.2.2.2 + 1) b.2.2.1 &&
  Nat.ble (b.2.2.1 + 1) b.2.1 && Nat.ble (b.2.1 + 1) b.1 && Nat.ble b.1 101 &&
  (((2 ^ b.1 + 3 * 2 ^ b.2.1 + 9 * 2 ^ b.2.2.1 + 27 * 2 ^ b.2.2.2) % 531441) == targetPow)

private def allIdxRow4BitFastW18 : Nat -> List Nat -> Bool
  | _, [] => true
  | curPow, p :: ps => checkBottom4BitCellFastW18 curPow p && allIdxRow4BitFastW18 ((curPow * 155519) % 531441) ps

private theorem pow2_81_mod531441_w18 : 2 ^ 81 % 531441 = 155519 := by decide

private theorem pow2_6561_mod531441_w18 : 2 ^ 6561 % 531441 = 373976 :=
  (pow2Mod531441Fast_eq 13 6561 (by decide)).symm.trans (by decide)

private theorem allIdxRow4BitFastW18_get :
    ∀ (xs : List Nat) (base c : Nat),
      allIdxRow4BitFastW18 (2 ^ (81 * base) % 531441) xs = true -> c < xs.length ->
      checkBottom4BitCellFastW18 (2 ^ (81 * (base + c)) % 531441) (listNatAtW18 xs c) = true
  | [], _, _, _, hc => False.elim (by simp at hc)
  | p :: _, base, 0, h, _ => by
    unfold allIdxRow4BitFastW18 at h; unfold listNatAtW18
    rw [Nat.add_zero]
    exact (Bool.and_eq_true_iff.mp h).1
  | _ :: ps, base, c + 1, h, hc => by
    unfold allIdxRow4BitFastW18 at h; unfold listNatAtW18
    have h2 := (Bool.and_eq_true_iff.mp h).2
    have hstep : ((2 ^ (81 * base) % 531441) * 155519) % 531441 = 2 ^ (81 * (base + 1)) % 531441 := by
      rw [← pow2_81_mod531441_w18, ← Nat.mul_mod, ← Nat.pow_add 2 (81 * base) 81,
          show 81 * base + 81 = 81 * (base + 1) by omega]
    rw [hstep] at h2
    have ih := allIdxRow4BitFastW18_get ps (base + 1) c h2 (by simp at hc; omega)
    rwa [show base + 1 + c = base + (c + 1) by omega] at ih

private def allGrid4BitFastW18 : Nat -> List (List Nat) -> Bool
  | _, [] => true
  | rPow, row :: rows =>
    (row.length == 81) && allIdxRow4BitFastW18 rPow row &&
      allGrid4BitFastW18 ((rPow * 373976) % 531441) rows

set_option exponentiation.threshold 524288 in
private theorem allGrid4BitFastW18_get :
    ∀ (rows : List (List Nat)) (rBase off c : Nat),
      allGrid4BitFastW18 (2 ^ (6561 * rBase) % 531441) rows = true -> off < rows.length -> c < 81 ->
      checkBottom4BitCellFastW18 (2 ^ (81 * (81 * (rBase + off) + c)) % 531441)
        (listNatAtW18 (listRowAtW18 rows off) c) = true
  | [], _, _, _, _, ho, _ => False.elim (by simp at ho)
  | row :: _, rBase, 0, c, h, _, hc => by
    unfold allGrid4BitFastW18 at h; unfold listRowAtW18
    rcases Bool.and_eq_true_iff.mp h with ⟨h1, _⟩
    rcases Bool.and_eq_true_iff.mp h1 with ⟨hlen_b, hrow⟩
    have hlen : row.length = 81 := beq_iff_eq.mp hlen_b
    rw [Nat.add_zero]
    rw [show 6561 * rBase = 81 * (81 * rBase) by omega] at hrow
    exact allIdxRow4BitFastW18_get row (81 * rBase) c hrow (hlen ▸ hc)
  | _ :: rows, rBase, off + 1, c, h, ho, hc => by
    unfold allGrid4BitFastW18 at h; unfold listRowAtW18
    have h2 := (Bool.and_eq_true_iff.mp h).2
    have hstep : ((2 ^ (6561 * rBase) % 531441) * 373976) % 531441 = 2 ^ (6561 * (rBase + 1)) % 531441 := by
      rw [← pow2_6561_mod531441_w18, ← Nat.mul_mod, ← Nat.pow_add 2 (6561 * rBase) 6561,
          show 6561 * rBase + 6561 = 6561 * (rBase + 1) by omega]
    rw [hstep] at h2
    have ih := allGrid4BitFastW18_get rows (rBase + 1) off c h2 (by simp at ho; omega) hc
    rwa [show rBase + 1 + off = rBase + (off + 1) by omega] at ih

private theorem checkBot4_b0 : allGrid4BitFastW18 1 bottom4BitBlock0 = true := by decide
private theorem checkBot4_b1 : allGrid4BitFastW18 413344 bottom4BitBlock1 = true := by decide
private theorem checkBot4_b2 : allGrid4BitFastW18 295246 bottom4BitBlock2 = true := by decide
private theorem checkBot4_b3 : allGrid4BitFastW18 177148 bottom4BitBlock3 = true := by decide
private theorem checkBot4_b4 : allGrid4BitFastW18 59050 bottom4BitBlock4 = true := by decide
private theorem checkBot4_b5 : allGrid4BitFastW18 472393 bottom4BitBlock5 = true := by decide
private theorem checkBot4_b6 : allGrid4BitFastW18 354295 bottom4BitBlock6 = true := by decide
private theorem checkBot4_b7 : allGrid4BitFastW18 236197 bottom4BitBlock7 = true := by decide
private theorem checkBot4_b8 : allGrid4BitFastW18 118099 bottom4BitBlock8 = true := by decide

set_option exponentiation.threshold 524288 in
private theorem bottom4BitBucket531441_q_spec (q : Nat) (hq : q < 4374) :
    let b := bottom4BitBucket531441 q
    9 ≤ b.2.2.2 ∧ b.2.2.2 < b.2.2.1 ∧ b.2.2.1 < b.2.1 ∧ b.2.1 < b.1 ∧ b.1 ≤ 101 ∧
    (2 ^ b.1 + 3 * 2 ^ b.2.1 + 9 * 2 ^ b.2.2.1 + 27 * 2 ^ b.2.2.2) % 531441 =
      2 ^ (81 * q) % 531441 := by
  let r_i := q / 81
  let c_i := q % 81
  have hr_lt : r_i < 54 := by dsimp [r_i]; omega
  have hc_lt : c_i < 81 := Nat.mod_lt q (by decide)
  have hblk : r_i / 6 < 9 := by omega
  have hoff : r_i % 6 < 6 := Nat.mod_lt r_i (by decide)
  have hq_sp : q = 81 * (6 * (r_i / 6) + r_i % 6) + c_i := by
    rw [Nat.div_add_mod r_i 6]; dsimp [r_i, c_i]; exact (Nat.div_add_mod q 81).symm
  have hcell : checkBottom4BitCellFastW18 (2 ^ (81 * q) % 531441)
      (listNatAtW18 (bottom4BitRowAtW18 r_i) c_i) = true := by
    unfold bottom4BitRowAtW18
    dsimp only
    rcases (by omega : r_i / 6 = 0 ∨ r_i / 6 = 1 ∨ r_i / 6 = 2 ∨ r_i / 6 = 3 ∨
      r_i / 6 = 4 ∨ r_i / 6 = 5 ∨ r_i / 6 = 6 ∨ r_i / 6 = 7 ∨ r_i / 6 = 8) with
      hb | hb | hb | hb | hb | hb | hb | hb | hb
    · have hrp : 2 ^ (6561 * 0) % 531441 = 1 := (pow2Mod531441Fast_eq 19 (6561 * 0) (by decide)).symm.trans (by decide)
      have h := allGrid4BitFastW18_get bottom4BitBlock0 0 (r_i % 6) c_i (by rw [hrp]; exact checkBot4_b0) (by simp only [bottom4BitBlock0, List.length_map, List.length_cons, List.length_nil]; exact hoff) hc_lt
      rw [hb] at hq_sp ⊢; rwa [← hq_sp] at h
    · have hrp : 2 ^ (6561 * 6) % 531441 = 413344 := (pow2Mod531441Fast_eq 19 (6561 * 6) (by decide)).symm.trans (by decide)
      have h := allGrid4BitFastW18_get bottom4BitBlock1 6 (r_i % 6) c_i (by rw [hrp]; exact checkBot4_b1) (by simp only [bottom4BitBlock1, List.length_map, List.length_cons, List.length_nil]; exact hoff) hc_lt
      rw [hb] at hq_sp ⊢; rwa [← hq_sp] at h
    · have hrp : 2 ^ (6561 * 12) % 531441 = 295246 := (pow2Mod531441Fast_eq 19 (6561 * 12) (by decide)).symm.trans (by decide)
      have h := allGrid4BitFastW18_get bottom4BitBlock2 12 (r_i % 6) c_i (by rw [hrp]; exact checkBot4_b2) (by simp only [bottom4BitBlock2, List.length_map, List.length_cons, List.length_nil]; exact hoff) hc_lt
      rw [hb] at hq_sp ⊢; rwa [← hq_sp] at h
    · have hrp : 2 ^ (6561 * 18) % 531441 = 177148 := (pow2Mod531441Fast_eq 19 (6561 * 18) (by decide)).symm.trans (by decide)
      have h := allGrid4BitFastW18_get bottom4BitBlock3 18 (r_i % 6) c_i (by rw [hrp]; exact checkBot4_b3) (by simp only [bottom4BitBlock3, List.length_map, List.length_cons, List.length_nil]; exact hoff) hc_lt
      rw [hb] at hq_sp ⊢; rwa [← hq_sp] at h
    · have hrp : 2 ^ (6561 * 24) % 531441 = 59050 := (pow2Mod531441Fast_eq 19 (6561 * 24) (by decide)).symm.trans (by decide)
      have h := allGrid4BitFastW18_get bottom4BitBlock4 24 (r_i % 6) c_i (by rw [hrp]; exact checkBot4_b4) (by simp only [bottom4BitBlock4, List.length_map, List.length_cons, List.length_nil]; exact hoff) hc_lt
      rw [hb] at hq_sp ⊢; rwa [← hq_sp] at h
    · have hrp : 2 ^ (6561 * 30) % 531441 = 472393 := (pow2Mod531441Fast_eq 19 (6561 * 30) (by decide)).symm.trans (by decide)
      have h := allGrid4BitFastW18_get bottom4BitBlock5 30 (r_i % 6) c_i (by rw [hrp]; exact checkBot4_b5) (by simp only [bottom4BitBlock5, List.length_map, List.length_cons, List.length_nil]; exact hoff) hc_lt
      rw [hb] at hq_sp ⊢; rwa [← hq_sp] at h
    · have hrp : 2 ^ (6561 * 36) % 531441 = 354295 := (pow2Mod531441Fast_eq 19 (6561 * 36) (by decide)).symm.trans (by decide)
      have h := allGrid4BitFastW18_get bottom4BitBlock6 36 (r_i % 6) c_i (by rw [hrp]; exact checkBot4_b6) (by simp only [bottom4BitBlock6, List.length_map, List.length_cons, List.length_nil]; exact hoff) hc_lt
      rw [hb] at hq_sp ⊢; rwa [← hq_sp] at h
    · have hrp : 2 ^ (6561 * 42) % 531441 = 236197 := (pow2Mod531441Fast_eq 19 (6561 * 42) (by decide)).symm.trans (by decide)
      have h := allGrid4BitFastW18_get bottom4BitBlock7 42 (r_i % 6) c_i (by rw [hrp]; exact checkBot4_b7) (by simp only [bottom4BitBlock7, List.length_map, List.length_cons, List.length_nil]; exact hoff) hc_lt
      rw [hb] at hq_sp ⊢; rwa [← hq_sp] at h
    · have hrp : 2 ^ (6561 * 48) % 531441 = 118099 := (pow2Mod531441Fast_eq 19 (6561 * 48) (by decide)).symm.trans (by decide)
      have h := allGrid4BitFastW18_get bottom4BitBlock8 48 (r_i % 6) c_i (by rw [hrp]; exact checkBot4_b8) (by simp only [bottom4BitBlock8, List.length_map, List.length_cons, List.length_nil]; exact hoff) hc_lt
      rw [hb] at hq_sp ⊢; rwa [← hq_sp] at h
  unfold checkBottom4BitCellFastW18 at hcell
  change (let b := bottom4BitBucket531441 q; _) = true at hcell
  dsimp only at hcell ⊢
  rcases Bool.and_eq_true_iff.mp hcell with ⟨h5, hmod_b⟩
  rcases Bool.and_eq_true_iff.mp h5 with ⟨h4, hb1_b⟩
  rcases Bool.and_eq_true_iff.mp h4 with ⟨h3, hb21_b⟩
  rcases Bool.and_eq_true_iff.mp h3 with ⟨h2, hb32_b⟩
  rcases Bool.and_eq_true_iff.mp h2 with ⟨hb4_b, hb43_b⟩
  have hb4 : 9 ≤ (bottom4BitBucket531441 q).2.2.2 := Nat.ble_eq.mp hb4_b
  have hb43 : (bottom4BitBucket531441 q).2.2.2 + 1 ≤ (bottom4BitBucket531441 q).2.2.1 := Nat.ble_eq.mp hb43_b
  have hb32 : (bottom4BitBucket531441 q).2.2.1 + 1 ≤ (bottom4BitBucket531441 q).2.1 := Nat.ble_eq.mp hb32_b
  have hb21 : (bottom4BitBucket531441 q).2.1 + 1 ≤ (bottom4BitBucket531441 q).1 := Nat.ble_eq.mp hb21_b
  have hb1 : (bottom4BitBucket531441 q).1 ≤ 101 := Nat.ble_eq.mp hb1_b
  exact ⟨hb4, by omega, by omega, by omega, hb1, beq_iff_eq.mp hmod_b⟩

private theorem bottom4BitBucket531441_mod_spec (k : Nat) (hk : k < 354294) :
    let b := bottom4BitBucket531441 (k / 81)
    let t := k % 81
    9 ≤ b.2.2.2 + t ∧ b.2.2.2 + t < b.2.2.1 + t ∧
    b.2.2.1 + t < b.2.1 + t ∧ b.2.1 + t < b.1 + t ∧ b.1 + t ≤ 181 ∧
    (2 ^ (b.1 + t) + 3 * 2 ^ (b.2.1 + t) + 9 * 2 ^ (b.2.2.1 + t) + 27 * 2 ^ (b.2.2.2 + t)) % 531441 =
      2 ^ k % 531441 := by
  dsimp only
  have hq_lt : k / 81 < 4374 := by omega
  have ht_lt : k % 81 < 81 := Nat.mod_lt k (by decide)
  rcases bottom4BitBucket531441_q_spec (k / 81) hq_lt with ⟨hb4, hb43, hb32, hb21, hb1, hsum_b⟩
  rcases hb : bottom4BitBucket531441 (k / 81) with ⟨b1, b2, b3, b4⟩
  rw [hb] at hb4 hb43 hb32 hb21 hb1 hsum_b
  dsimp only at hb4 hb43 hb32 hb21 hb1 hsum_b ⊢
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
  have hmul_t :
      2 ^ (b1 + k % 81) + 3 * 2 ^ (b2 + k % 81) + 9 * 2 ^ (b3 + k % 81) + 27 * 2 ^ (b4 + k % 81) =
      (2 ^ b1 + 3 * 2 ^ b2 + 9 * 2 ^ b3 + 27 * 2 ^ b4) * 2 ^ (k % 81) := by
    rw [Nat.pow_add 2 b1 (k % 81), Nat.pow_add 2 b2 (k % 81),
        Nat.pow_add 2 b3 (k % 81), Nat.pow_add 2 b4 (k % 81),
        Nat.add_mul, Nat.add_mul, Nat.add_mul,
        Nat.mul_assoc 3, Nat.mul_assoc 9, Nat.mul_assoc 27]
  rw [hmul_t, Nat.mul_mod, hsum_b, ← Nat.mul_mod, ← Nat.pow_add 2 (81 * (k / 81)) (k % 81),
      Nat.div_add_mod k 81]

private theorem pow3_bitlength_strict_bounds_w18 (w : Nat) (hw : w ≥ 10) :
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
  have hsnd : ∀ (fuel n : Nat), n ≥ 1 -> n ≤ fuel ->
      binBitLength n ≥ 1 ∧ 2 ^ (binBitLength n - 1) ≤ n ∧ n < 2 ^ binBitLength n := by
    intro fuel; induction fuel with
    | zero => intro _ hn hle; omega
    | succ f ih =>
      intro n hn hle
      if hn1 : n = 1 then subst hn1; decide
      else
        let k := n / 2
        have hk_pos : k ≥ 1 := by dsimp [k]; omega
        have hbl_n : binBitLength n = 1 + binBitLength k := binBitLength_step_pos n hn
        rcases ih k hk_pos (by dsimp [k]; omega) with ⟨hbl_k, hk_lo, hk_hi⟩
        rw [hbl_n]
        refine ⟨by omega, ?_, ?_⟩
        · rw [show 1 + binBitLength k - 1 = (binBitLength k - 1) + 1 by omega, Nat.pow_succ]
          have hm := Nat.mul_le_mul_right 2 hk_lo; dsimp [k] at hm; omega
        · rw [Nat.add_comm 1 (binBitLength k), Nat.pow_succ]
          have hm := Nat.mul_lt_mul_of_pos_right hk_hi (by decide : 0 < 2); dsimp [k] at hm; omega
  rcases hsnd (3 ^ w) (3 ^ w) (by omega) (Nat.le_refl _) with ⟨_, hlo, hhi⟩
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

private theorem dyadicPolyShiftDelta3_spec_w18 (b0 : Nat) :
    let delta3 := 3 + dyadicPolyShiftDelta (b0 + 3)
    let a := b0 + delta3
    let q3 := (2 ^ (a + 1) - 1) / 3
    3 ≤ delta3 ∧ delta3 ≤ 6 ∧ 3 * q3 + 1 = 2 ^ (a + 1) ∧ q3 % 3 ≠ 0 ∧ q3 ≥ 1 := by
  dsimp only
  let d0 := dyadicPolyShiftDelta (b0 + 3)
  have hd_mod6 : d0 ≤ 3 ∧ (((b0 + 3) + 1 + d0) % 6 = 2 ∨ ((b0 + 3) + 1 + d0) % 6 = 4) := by
    dsimp [d0]; unfold dyadicPolyShiftDelta
    have hdm := (Nat.div_add_mod (b0 + 3 + 1) 6).symm
    rcases (by omega :
      (b0 + 3 + 1) % 6 = 0 ∨ (b0 + 3 + 1) % 6 = 1 ∨ (b0 + 3 + 1) % 6 = 2 ∨
      (b0 + 3 + 1) % 6 = 3 ∨ (b0 + 3 + 1) % 6 = 4 ∨ (b0 + 3 + 1) % 6 = 5) with
      h | h | h | h | h | h <;> (simp [h]; omega)
  let E := b0 + (3 + d0) + 1
  have hE_eq : (b0 + 3) + 1 + d0 = E := by dsimp [E]; omega
  rw [hE_eq] at hd_mod6
  have hp6 : ∀ n : Nat, 2 ^ n % 9 = 2 ^ (n % 6) % 9 := by
    intro n
    have hp : ∀ q : Nat, 2 ^ (6 * q) % 9 = 1 := by
      intro q; induction q with
      | zero => rfl
      | succ q' ih => rw [Nat.mul_succ 6 q', Nat.pow_add 2 (6 * q') 6, Nat.mul_mod, ih]
    conv => lhs; rw [(Nat.div_add_mod n 6).symm]
    rw [Nat.pow_add 2 (6 * (n / 6)) (n % 6), Nat.mul_mod, hp (n / 6), Nat.one_mul, Nat.mod_mod]
  have hpE_m9 : 2 ^ E % 9 = 4 ∨ 2 ^ E % 9 = 7 := by
    rw [hp6 E]
    rcases hd_mod6.2 with h2 | h4
    · left; rw [h2]
    · right; rw [h4]
  have hpE_ge4 : 2 ^ E ≥ 4 := pow2_mono_nat (by dsimp [E]; omega : 2 ≤ E)
  have hdm9 := (Nat.div_add_mod (2 ^ E) 9).symm
  change 3 ≤ 3 + d0 ∧ 3 + d0 ≤ 6 ∧ 3 * ((2 ^ E - 1) / 3) + 1 = 2 ^ E ∧
    ((2 ^ E - 1) / 3) % 3 ≠ 0 ∧ (2 ^ E - 1) / 3 ≥ 1
  refine ⟨by omega, by omega, ?_, ?_, by omega⟩
  · rcases hpE_m9 with h4 | h7 <;> omega
  · rcases hpE_m9 with h4 | h7 <;> omega

private theorem isSurvivingMod373248_of_507_and_mod9_eq7_w18 (y : Nat)
    (h512 : y % 512 = 507) (h9 : y % 9 = 7) :
    isSurvivingMod373248Bool y = true ∧ IsSurvivingMod373248Class y := by
  have hall729 : ∀ q : Fin 81, isSurvivingMod729Bool (9 * q.val + 7) = true := by decide
  let r729 := y % 729
  have hr_lt : r729 < 729 := Nat.mod_lt y (by decide)
  have hr_m9 : r729 % 9 = 7 := by
    dsimp only [r729]; rw [Nat.mod_mod_of_dvd y ⟨81, by decide⟩, h9]
  have hq81_lt : r729 / 9 < 81 := by omega
  have hr_eq : r729 = 9 * (r729 / 9) + 7 := by
    have hdm := (Nat.div_add_mod r729 9).symm; omega
  have hb729 : isSurvivingMod729Bool (y % 729) = true := by
    change isSurvivingMod729Bool r729 = true; rw [hr_eq]; exact hall729 ⟨r729 / 9, hq81_lt⟩
  have hb512 : isSurvivingMod512Bool (y % 512) = true := by rw [h512]; decide
  have hb373 : isSurvivingMod373248Bool y = true := by
    unfold isSurvivingMod373248Bool; rw [hb512, hb729]; rfl
  exact ⟨hb373, isSurvivingMod373248Bool_imp_class y hb373⟩

/-- Sub-`250` (`M_0 = 210 ≤ 250`, down from Wave 17's `360`!), steeper-slope (`c = 5 ≤ 5`, beating
    Wave 17's `c = 6`!) linear minimum dyadic window scale `dyadicExpWindowMinM18Low B = 210 + 5 * B`. -/
def dyadicExpWindowMinM18Low (B : Nat) : Nat :=
  210 + 5 * B

/-- Zero-run length list
    `[e4 - 9, e3 - (e4 + 1), e2 - (e3 + 1), e1 - (e2 + 1), e_fin - (e1 + 1)] ++ gaps`
    for `uWinExp18Low B M mask` (4-bit bottom collision mod `3^12 = 531441` + 4-step `Mod 243` chain). -/
def uWinExp18LowRuns (B M mask : Nat) : List Nat :=
  let k4 := (B + 3) / 4
  let w := 4 * k4 + 11
  let b0 := binBitLength (3 ^ w)
  let delta3 := 3 + dyadicPolyShiftDelta (b0 + 3)
  let a := b0 + delta3
  let q3 := (2 ^ (a + 1) - 1) / 3
  let L := M - delta3
  let chain := fourStepTernaryCarryChain k4 (L - 1) (q3 * 2 ^ (L - 1)) mask
  let e_fin := chain.1
  let R_fin := chain.2.1
  let gaps := chain.2.2
  let A_last := R_fin - (81 * 1085 + 7 * 3 ^ 10)
  let k_dlog := dlog2ModPow3 12 (A_last % 3 ^ 12)
  let b := bottom4BitBucket531441 (k_dlog / 81)
  let t := k_dlog % 81
  let e1 := b.1 + t
  let e2 := b.2.1 + t
  let e3 := b.2.2.1 + t
  let e4 := b.2.2.2 + t
  (e4 - 9) :: (e3 - (e4 + 1)) :: (e2 - (e3 + 1)) :: (e1 - (e2 + 1)) :: (e_fin - (e1 + 1)) :: gaps

/-- Constructive sub-`250`-threshold (`M_0 = 210 ≤ 250`), steeper-slope (`c = 5 ≤ 5`) surviving
    `Mod373248` first-hit `q = 0` family `uWinExp18Low B M mask` inside `[2^M, 2^(M+1))` at linear
    length `L = M - delta3 ≤ M`. -/
def uWinExp18Low (B M mask : Nat) : List Bool :=
  minWeight6Prefix507 ++ zeroRunsSuffix (uWinExp18LowRuns B M mask)

private theorem bottom_4bit_collision_solve_w18 (R_fin L e_fin : Nat)
    (_hL : L ≥ 204) (he_fin : e_fin ≥ 190) (he_hi : e_fin ≤ L - 1)
    (hRfin_n3 : R_fin % 3 ≠ 0)
    (hRfin_lo : R_fin ≥ (2 * 3 ^ 10 - 1) * 2 ^ (L - 1)) :
    let A_last := R_fin - (81 * 1085 + 7 * 3 ^ 10)
    let k_dlog := dlog2ModPow3 12 (A_last % 3 ^ 12)
    let b := bottom4BitBucket531441 (k_dlog / 81)
    let t := k_dlog % 81
    ∃ (e1 e2 e3 e4 m : Nat),
      e1 = b.1 + t ∧ e2 = b.2.1 + t ∧ e3 = b.2.2.1 + t ∧ e4 = b.2.2.2 + t ∧
      9 ≤ e4 ∧ e4 < e3 ∧ e3 < e2 ∧ e2 < e1 ∧ e1 < e_fin ∧
      81 * 1085 + (2 ^ e1 + 3 * 2 ^ e2 + 9 * 2 ^ e3 + 27 * 2 ^ e4) < 2 ^ e_fin ∧
      R_fin = 3 ^ 10 * (9 * m + 7) +
        (81 * 1085 + (2 ^ e1 + 3 * 2 ^ e2 + 9 * 2 ^ e3 + 27 * 2 ^ e4)) := by
  dsimp only
  rcases (⟨81 * 1085 + 7 * 3 ^ 10, rfl⟩ : ∃ sc : Nat, sc = 81 * 1085 + 7 * 3 ^ 10) with ⟨sub_c, hsub_def⟩
  have h2L1_ge20 : 2 ^ (L - 1) ≥ 1048576 :=
    Nat.le_trans (by decide : 1048576 ≤ 2 ^ 20) (pow2_mono_nat (by omega))
  have hRfin_big : R_fin ≥ 118097 * 2 ^ (L - 1) := by
    have hc : 2 * 3 ^ 10 - 1 = 118097 := by decide
    exact hc ▸ hRfin_lo
  have hsub_lt_2L1 : sub_c < 2 ^ (L - 1) :=
    Nat.lt_of_lt_of_le (by rw [hsub_def]; decide) h2L1_ge20
  have hsub_lt_Rfin : sub_c < R_fin := by
    have h1 : 2 ^ (L - 1) ≤ R_fin :=
      Nat.le_trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 118097)) hRfin_big
    exact Nat.lt_of_lt_of_le hsub_lt_2L1 h1
  rcases (⟨R_fin - sub_c, rfl⟩ : ∃ al : Nat, al = R_fin - sub_c) with ⟨A_last, hA_eq_def⟩
  have hA_n3 : (A_last % 3 ^ 12) % 3 ≠ 0 := by
    have hAn3 : A_last % 3 ≠ 0 := by
      have hsub_3 : sub_c = 3 * 167076 := hsub_def.trans (by decide)
      have hrew : R_fin = A_last + 3 * 167076 := by
        rw [hA_eq_def, ← hsub_3, Nat.sub_add_cancel (Nat.le_of_lt hsub_lt_Rfin)]
      intro h0
      have hm0 : R_fin % 3 = 0 := by rw [hrew, Nat.add_mul_mod_self_left, h0]
      exact hRfin_n3 hm0
    have hdvd12 : 3 ∣ 3 ^ 12 := ⟨177147, by decide⟩
    rwa [Nat.mod_mod_of_dvd A_last hdvd12]
  rcases (⟨dlog2ModPow3 12 (A_last % 3 ^ 12), rfl⟩ :
      ∃ kd : Nat, kd = dlog2ModPow3 12 (A_last % 3 ^ 12)) with ⟨k_dlog, hk_def⟩
  rcases dlog2ModPow3_spec 12 (A_last % 3 ^ 12) (by decide) hA_n3 with
    ⟨hk_lt_raw, hk_mod_raw⟩
  rw [← hk_def] at hk_lt_raw hk_mod_raw
  have hk_lt : k_dlog < 354294 := by
    have hp : 2 * 3 ^ (12 - 1) = 354294 := by decide
    exact hp ▸ hk_lt_raw
  rcases bottom4BitBucket531441_mod_spec k_dlog hk_lt with
    ⟨he4_9, he43, he32, he21, he1_181, h4bit_mod⟩
  rcases hb : bottom4BitBucket531441 (k_dlog / 81) with ⟨b1, b2, b3, b4⟩
  rw [hb] at he4_9 he43 he32 he21 he1_181 h4bit_mod
  dsimp only at he4_9 he43 he32 he21 he1_181 h4bit_mod
  rcases (⟨b1 + k_dlog % 81, rfl⟩ : ∃ v : Nat, v = b1 + k_dlog % 81) with ⟨e1, he1_def⟩
  rcases (⟨b2 + k_dlog % 81, rfl⟩ : ∃ v : Nat, v = b2 + k_dlog % 81) with ⟨e2, he2_def⟩
  rcases (⟨b3 + k_dlog % 81, rfl⟩ : ∃ v : Nat, v = b3 + k_dlog % 81) with ⟨e3, he3_def⟩
  rcases (⟨b4 + k_dlog % 81, rfl⟩ : ∃ v : Nat, v = b4 + k_dlog % 81) with ⟨e4, he4_def⟩
  rw [← he1_def] at he21 he1_181 h4bit_mod
  rw [← he2_def] at he32 he21 h4bit_mod
  rw [← he3_def] at he43 he32 h4bit_mod
  rw [← he4_def] at he4_9 he43 h4bit_mod
  rcases (⟨2 ^ e1 + 3 * 2 ^ e2 + 9 * 2 ^ e3 + 27 * 2 ^ e4, rfl⟩ :
      ∃ s4 : Nat, s4 = 2 ^ e1 + 3 * 2 ^ e2 + 9 * 2 ^ e3 + 27 * 2 ^ e4) with ⟨S4, hS4_def⟩
  rw [← hS4_def] at h4bit_mod
  have hS4_mod : S4 % 531441 = A_last % 531441 := by
    have h312_val : (3 : Nat) ^ 12 = 531441 := by decide
    rw [h312_val, Nat.mod_mod] at hk_mod_raw
    exact h4bit_mod.trans hk_mod_raw
  rcases (⟨e_fin - 6, rfl⟩ : ∃ n0 : Nat, n0 = e_fin - 6) with ⟨n0, hn0_def⟩
  have hn0_ge184 : n0 ≥ 184 := by
    clear hsub_def h2L1_ge20 hRfin_big hRfin_lo hsub_lt_2L1 hsub_lt_Rfin hA_eq_def hA_n3
    clear hk_def hk_lt_raw hk_mod_raw hk_lt hb he1_def he2_def he3_def he4_def hS4_def h4bit_mod hS4_mod
    omega
  have he1_lt_efin : e1 < e_fin := by
    clear hsub_def h2L1_ge20 hRfin_big hRfin_lo hsub_lt_2L1 hsub_lt_Rfin hA_eq_def hA_n3
    clear hk_def hk_lt_raw hk_mod_raw hk_lt hb he1_def he2_def he3_def he4_def hS4_def h4bit_mod hS4_mod hn0_def
    omega
  have hS4_lt_efin : 81 * 1085 + S4 < 2 ^ e_fin := by
    have hc81 : 81 * 1085 < 2 ^ n0 :=
      Nat.lt_of_lt_of_le (by decide : 81 * 1085 < 2 ^ 17)
        (pow2_mono_nat (Nat.le_trans (by decide : 17 ≤ 184) hn0_ge184))
    have he1_n0 : e1 ≤ n0 := Nat.le_trans he1_181 (Nat.le_trans (by decide : 181 ≤ 184) hn0_ge184)
    have he2_n0 : e2 ≤ n0 := Nat.le_trans (Nat.le_of_lt he21) he1_n0
    have he3_n0 : e3 ≤ n0 := Nat.le_trans (Nat.le_of_lt he32) he2_n0
    have he4_n0 : e4 ≤ n0 := Nat.le_trans (Nat.le_of_lt he43) he3_n0
    have hp1 : 2 ^ e1 ≤ 2 ^ n0 := pow2_mono_nat he1_n0
    have hp2 : 2 ^ e2 ≤ 2 ^ n0 := pow2_mono_nat he2_n0
    have hp3 : 2 ^ e3 ≤ 2 ^ n0 := pow2_mono_nat he3_n0
    have hp4 : 2 ^ e4 ≤ 2 ^ n0 := pow2_mono_nat he4_n0
    have hpef : 2 ^ e_fin = 64 * 2 ^ n0 := by
      have hef6 : e_fin = 6 + n0 := by
        clear hsub_def h2L1_ge20 hRfin_big hRfin_lo hsub_lt_2L1 hsub_lt_Rfin hA_eq_def hA_n3
        clear hk_def hk_lt_raw hk_mod_raw hk_lt hb he1_def he2_def he3_def he4_def hS4_def h4bit_mod hS4_mod
        clear hc81 hp1 hp2 hp3 hp4
        omega
      rw [hef6, Nat.pow_add 2 6 n0, show (2 : Nat) ^ 6 = 64 from rfl]
    rw [hS4_def, hpef]
    clear hsub_def h2L1_ge20 hRfin_big hRfin_lo hsub_lt_2L1 hsub_lt_Rfin hA_eq_def hA_n3
    clear hk_def hk_lt_raw hk_mod_raw hk_lt hb he1_def he2_def he3_def he4_def hS4_def h4bit_mod hS4_mod
    clear hn0_def hpef
    generalize 81 * 1085 = C81, 2 ^ n0 = ZN, 2 ^ e1 = Z1, 2 ^ e2 = Z2, 2 ^ e3 = Z3, 2 ^ e4 = Z4 at hc81 hp1 hp2 hp3 hp4 ⊢
    omega
  have hS4_lt_A : S4 < A_last := by
    have hs1 : S4 < 2 ^ (L - 1) :=
      Nat.lt_of_lt_of_le
        (Nat.lt_of_le_of_lt (Nat.le_add_left S4 (81 * 1085)) hS4_lt_efin)
        (pow2_mono_nat he_hi)
    have h2_le : 2 * 2 ^ (L - 1) ≤ R_fin :=
      Nat.le_trans (Nat.mul_le_mul_right _ (by decide : 2 ≤ 118097)) hRfin_big
    rw [hA_eq_def]
    clear hsub_def h2L1_ge20 hRfin_big hRfin_lo hk_def hk_lt_raw hk_mod_raw hk_lt hb
    clear he1_def he2_def he3_def he4_def hS4_def h4bit_mod hS4_mod hn0_def hS4_lt_efin hA_n3
    generalize 2 ^ (L - 1) = Z2L, sub_c = ZSC, S4 = ZS, R_fin = ZR at hs1 hsub_lt_2L1 h2_le hsub_lt_Rfin ⊢
    omega
  have hdiff_mod : (A_last - S4) % 531441 = 0 := by
    have hm_lt : A_last % 531441 < 531441 := Nat.mod_lt A_last (by decide)
    rw [sub_mod_of_le_cf_w18 531441 A_last S4 (by decide) (Nat.le_of_lt hS4_lt_A), hS4_mod,
        show A_last % 531441 + 531441 - A_last % 531441 = 531441 by omega, Nat.mod_self]
  rcases Nat.dvd_of_mod_eq_zero hdiff_mod with ⟨m, hm_eq⟩
  have hA_rec : A_last = 531441 * m + S4 := by
    rw [← hm_eq, Nat.sub_add_cancel (Nat.le_of_lt hS4_lt_A)]
  have hR_eq_m : R_fin = 3 ^ 10 * (9 * m + 7) + (81 * 1085 + S4) := by
    have hR_sub : R_fin = A_last + sub_c := by
      rw [hA_eq_def, Nat.sub_add_cancel (Nat.le_of_lt hsub_lt_Rfin)]
    have hQ1_exp : 3 ^ 10 * (9 * m + 7) = 531441 * m + 413343 := by
      rw [Nat.mul_add, ← Nat.mul_assoc,
          show 3 ^ 10 * 9 = 531441 by decide,
          show 3 ^ 10 * 7 = 413343 by decide]
    have hconst : sub_c = 413343 + 81 * 1085 := hsub_def.trans (by decide)
    rw [hR_sub, hA_rec, hQ1_exp, hconst]
    clear hsub_def h2L1_ge20 hRfin_big hRfin_lo hsub_lt_2L1 hsub_lt_Rfin hA_eq_def hA_n3
    clear hk_def hk_lt_raw hk_mod_raw hk_lt hb he1_def he2_def he3_def he4_def hS4_def h4bit_mod hS4_mod
    clear hn0_def hS4_lt_efin hS4_lt_A hdiff_mod hm_eq hA_rec hR_sub hQ1_exp hconst
    generalize 531441 * m = ZM, (413343 : Nat) = ZD, 81 * 1085 = ZC, S4 = ZS
    omega
  rw [hS4_def] at hS4_lt_efin hR_eq_m
  refine ⟨e1, e2, e3, e4, m, ?_, ?_, ?_, ?_, he4_9, he43, he32, he21, he1_lt_efin, hS4_lt_efin, hR_eq_m⟩
  · rw [← hsub_def, ← hA_eq_def, ← hk_def, hb]; exact he1_def
  · rw [← hsub_def, ← hA_eq_def, ← hk_def, hb]; exact he2_def
  · rw [← hsub_def, ← hA_eq_def, ← hk_def, hb]; exact he3_def
  · rw [← hsub_def, ← hA_eq_def, ← hk_def, hb]; exact he4_def

private theorem five_step_bottom_runs_spec_w18
    (e4 e3 e2 e1 e_fin : Nat)
    (he4 : 9 ≤ e4) (he43 : e4 < e3) (he32 : e3 < e2) (he21 : e2 < e1) (he1f : e1 < e_fin) :
    ∃ u_acc : List Bool,
      u_acc = minWeight6Prefix507 ++
        zeroRunsSuffix [e4 - 9, e3 - (e4 + 1), e2 - (e3 + 1), e1 - (e2 + 1), e_fin - (e1 + 1)] ∧
      u_acc.length = e_fin + 1 ∧
      parityWeight u_acc = 11 ∧
      affineCarry u_acc =
        3 * (81 * 1085 + (2 ^ e1 + 3 * 2 ^ e2 + 9 * 2 ^ e3 + 27 * 2 ^ e4)) + 2 ^ e_fin := by
  let u0 := minWeight6Prefix507
  let u_b4 := (u0 ++ List.replicate (e4 - 9) false) ++ [true]
  let u_b3 := (u_b4 ++ List.replicate (e3 - (e4 + 1)) false) ++ [true]
  let u_b2 := (u_b3 ++ List.replicate (e2 - (e3 + 1)) false) ++ [true]
  let u_b1 := (u_b2 ++ List.replicate (e1 - (e2 + 1)) false) ++ [true]
  let u_acc := (u_b1 ++ List.replicate (e_fin - (e1 + 1)) false) ++ [true]
  have hu0_car : affineCarry u0 = 1085 := by decide
  have hc1_t : affineCarry [true] = 1 := rfl
  have hw1_t : parityWeight [true] = 1 := rfl
  rcases affineCarry_append_replicate_false u0 (e4 - 9) with ⟨hwt_z4, hcar_z4⟩
  have hlen_z4 : (u0 ++ List.replicate (e4 - 9) false).length = e4 := by
    rw [List.length_append, show u0.length = 9 from rfl, List.length_replicate]; omega
  have hlen_b4 : u_b4.length = e4 + 1 := by dsimp [u_b4]; rw [List.length_append, hlen_z4, List.length_singleton]
  have hwt_b4 : parityWeight u_b4 = 7 := by dsimp [u_b4]; rw [parityWeight_append, hwt_z4]; rfl
  have hcar_b4 : affineCarry u_b4 = 3 * 1085 + 2 ^ e4 := by
    dsimp [u_b4]; rw [affineCarry_append, hcar_z4, hu0_car, hlen_z4, hc1_t, hw1_t]; omega
  rcases affineCarry_append_replicate_false u_b4 (e3 - (e4 + 1)) with ⟨hwt_z3, hcar_z3⟩
  have hlen_z3 : (u_b4 ++ List.replicate (e3 - (e4 + 1)) false).length = e3 := by
    rw [List.length_append, hlen_b4, List.length_replicate]; omega
  have hlen_b3 : u_b3.length = e3 + 1 := by dsimp [u_b3]; rw [List.length_append, hlen_z3, List.length_singleton]
  have hwt_b3 : parityWeight u_b3 = 8 := by dsimp [u_b3]; rw [parityWeight_append, hwt_z3, hwt_b4]; rfl
  have hcar_b3 : affineCarry u_b3 = 9 * 1085 + 3 * 2 ^ e4 + 2 ^ e3 := by
    dsimp [u_b3]; rw [affineCarry_append, hcar_z3, hcar_b4, hlen_z3, hc1_t, hw1_t]; omega
  rcases affineCarry_append_replicate_false u_b3 (e2 - (e3 + 1)) with ⟨hwt_z2, hcar_z2⟩
  have hlen_z2 : (u_b3 ++ List.replicate (e2 - (e3 + 1)) false).length = e2 := by
    rw [List.length_append, hlen_b3, List.length_replicate]; omega
  have hlen_b2 : u_b2.length = e2 + 1 := by dsimp [u_b2]; rw [List.length_append, hlen_z2, List.length_singleton]
  have hwt_b2 : parityWeight u_b2 = 9 := by dsimp [u_b2]; rw [parityWeight_append, hwt_z2, hwt_b3]; rfl
  have hcar_b2 : affineCarry u_b2 = 27 * 1085 + 9 * 2 ^ e4 + 3 * 2 ^ e3 + 2 ^ e2 := by
    dsimp [u_b2]; rw [affineCarry_append, hcar_z2, hcar_b3, hlen_z2, hc1_t, hw1_t]; omega
  rcases affineCarry_append_replicate_false u_b2 (e1 - (e2 + 1)) with ⟨hwt_z1, hcar_z1⟩
  have hlen_z1 : (u_b2 ++ List.replicate (e1 - (e2 + 1)) false).length = e1 := by
    rw [List.length_append, hlen_b2, List.length_replicate]; omega
  have hlen_b1 : u_b1.length = e1 + 1 := by dsimp [u_b1]; rw [List.length_append, hlen_z1, List.length_singleton]
  have hwt_b1 : parityWeight u_b1 = 10 := by dsimp [u_b1]; rw [parityWeight_append, hwt_z1, hwt_b2]; rfl
  have hcar_b1 : affineCarry u_b1 = 81 * 1085 + (2 ^ e1 + 3 * 2 ^ e2 + 9 * 2 ^ e3 + 27 * 2 ^ e4) := by
    dsimp [u_b1]; rw [affineCarry_append, hcar_z1, hcar_b2, hlen_z1, hc1_t, hw1_t]; omega
  rcases affineCarry_append_replicate_false u_b1 (e_fin - (e1 + 1)) with ⟨hwt_z0, hcar_z0⟩
  have hlen_z0 : (u_b1 ++ List.replicate (e_fin - (e1 + 1)) false).length = e_fin := by
    rw [List.length_append, hlen_b1, List.length_replicate]; omega
  have hlen_acc : u_acc.length = e_fin + 1 := by dsimp [u_acc]; rw [List.length_append, hlen_z0, List.length_singleton]
  have hwt_acc : parityWeight u_acc = 11 := by dsimp [u_acc]; rw [parityWeight_append, hwt_z0, hwt_b1]; rfl
  have hcar_acc : affineCarry u_acc = 3 * affineCarry u_b1 + 2 ^ e_fin := by
    dsimp [u_acc]; rw [affineCarry_append, hcar_z0, hlen_z0, hc1_t, hw1_t, Nat.pow_one]
    generalize affineCarry u_b1 = CB1, 2 ^ e_fin = ZE; omega
  rw [hcar_b1] at hcar_acc
  have hu_eq : u_acc = minWeight6Prefix507 ++
      zeroRunsSuffix [e4 - 9, e3 - (e4 + 1), e2 - (e3 + 1), e1 - (e2 + 1), e_fin - (e1 + 1)] := by
    dsimp only [zeroRunsSuffix, u_acc, u_b1, u_b2, u_b3, u_b4, u0]
    simp [List.append_assoc]
  exact ⟨u_acc, hu_eq, hlen_acc, hwt_acc, hcar_acc⟩

private theorem pow3_gt_two_mul_w18 : ∀ n : Nat, 3 ^ n > 2 * n
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by have ih := pow3_gt_two_mul_w18 (n + 1); rw [Nat.pow_succ]; omega

private theorem uWinExp18Low_per_mask_core_and_key_w18
    (B M mask : Nat) (hB : B ≥ 1) (hM : M ≥ dyadicExpWindowMinM18Low B)
    (_hmask : mask < 2 ^ B) :
    let k4 := (B + 3) / 4
    let w := 4 * k4 + 11
    let b0 := binBitLength (3 ^ w)
    let delta3 := 3 + dyadicPolyShiftDelta (b0 + 3)
    let a := b0 + delta3
    let u_e := uWinExp18Low B M mask
    IsCoreParityWord u_e ∧
    u_e.length = M - delta3 ∧
    parityWeight u_e = w ∧
    canonicalSuffixShift u_e 1 = a ∧
    IsFirstHitOnePair u_e 0 ∧
    affineCarry u_e ≥ 1 ∧
    affineCarry u_e < 2 ^ M ∧
    (∃ mid : List Bool, u_e = minWeight6Prefix507 ++ mid ++ [true]) ∧
    (∃ m : Nat, 2 ^ (u_e.length + a) = 3 ^ w * (9 * m + 7) + affineCarry u_e) := by
  dsimp only
  rcases (⟨(B + 3) / 4, rfl⟩ : ∃ v : Nat, v = (B + 3) / 4) with ⟨k4, hk4_def⟩
  rcases (⟨4 * k4 + 11, rfl⟩ : ∃ v : Nat, v = 4 * k4 + 11) with ⟨w, hw_eq⟩
  rcases (⟨binBitLength (3 ^ w), rfl⟩ : ∃ v : Nat, v = binBitLength (3 ^ w)) with ⟨b0, hb0_def⟩
  rcases (⟨3 + dyadicPolyShiftDelta (b0 + 3), rfl⟩ :
      ∃ v : Nat, v = 3 + dyadicPolyShiftDelta (b0 + 3)) with ⟨delta3, hd3_def⟩
  rcases (⟨b0 + delta3, rfl⟩ : ∃ v : Nat, v = b0 + delta3) with ⟨a, ha_eq⟩
  rcases (⟨(2 ^ (a + 1) - 1) / 3, rfl⟩ : ∃ v : Nat, v = (2 ^ (a + 1) - 1) / 3) with ⟨q3, hq3_def⟩
  rcases (⟨M - delta3, rfl⟩ : ∃ v : Nat, v = M - delta3) with ⟨L, hL_eq⟩
  have hk4_ge1 : k4 ≥ 1 := by rw [hk4_def]; omega
  have h18k4_le : 18 * k4 ≤ 5 * B + 13 := by rw [hk4_def]; omega
  have hw_ge15 : w ≥ 15 := by rw [hw_eq]; omega
  rcases pow3_bitlength_strict_bounds_w18 w (by omega) with ⟨hb0_ge16, hb0_le2w, h3w_lo, _⟩
  rw [← hb0_def] at hb0_ge16 hb0_le2w h3w_lo
  rcases dyadicPolyShiftDelta3_spec_w18 b0 with ⟨hd3_lo, hd3_hi, h3q3, hq3_n3, _⟩
  rw [← hd3_def] at hd3_lo hd3_hi h3q3 hq3_n3
  rw [← ha_eq] at h3q3 hq3_n3
  rw [← hq3_def] at h3q3 hq3_n3
  have hM_def : M ≥ 210 + 5 * B := hM
  have hL_ge : L ≥ 204 + 5 * B := by rw [hL_eq]; omega
  have ha_lt_P : a < 2 * 3 ^ (w - 1) := by
    have ha_le : a ≤ 2 * w + 6 := by rw [ha_eq]; omega
    have hw1_gt : 3 ^ (w - 1) > 2 * (w - 1) := pow3_gt_two_mul_w18 (w - 1)
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
  have hq3_ge_pow3 : q3 ≥ 2 * 3 ^ (4 * k4 + 10) - 1 := by
    have ha1_ge16 : 2 ^ (a + 1) ≥ 16 * 2 ^ b0 := by
      have h : 2 ^ (4 + b0) ≤ 2 ^ (a + 1) := pow2_mono_nat (by rw [ha_eq]; omega)
      rwa [Nat.pow_add 2 4 b0] at h
    have hp3_le : 3 ^ (4 * k4 + 10) ≤ 3 ^ w :=
      nat_pow_mono_exp_pos 3 (4 * k4 + 10) w (by decide) (by rw [hw_eq]; omega)
    have hge16 : 3 * q3 + 1 ≥ 16 * (3 ^ (4 * k4 + 10) + 1) := by
      rw [h3q3]
      exact Nat.le_trans (Nat.mul_le_mul_left 16 (Nat.add_le_add_right hp3_le 1))
        (Nat.le_trans (Nat.mul_le_mul_left 16 h3w_lo) ha1_ge16)
    generalize 3 ^ (4 * k4 + 10) = P3 at hge16 ⊢
    omega
  have hR0_lo : R0 ≥ (2 * 3 ^ (4 * k4 + 10) - 1) * 2 ^ (L - 1) := by
    rw [hR0_def]; exact Nat.mul_le_mul_right _ hq3_ge_pow3
  rcases (fourStepTernaryCarryChain_spec_and_inj_w18 k4 (L - 1) R0 (L - 1)
    (Nat.le_refl _) (by omega) hR0_n3 hR0_lo).1 mask with
    ⟨he_lo, he_hi, hlen_gaps, hRfin_n3, hRfin_lo, hunwind⟩
  rcases hch : fourStepTernaryCarryChain k4 (L - 1) R0 mask with ⟨e_fin, R_fin, gaps⟩
  rw [hch] at he_lo he_hi hlen_gaps hRfin_n3 hRfin_lo hunwind
  dsimp only at he_lo he_hi hlen_gaps hRfin_n3 hRfin_lo hunwind
  have he_fin_ge : e_fin ≥ 190 := by omega
  rcases bottom_4bit_collision_solve_w18 R_fin L e_fin (by omega) he_fin_ge he_hi hRfin_n3 hRfin_lo with
    ⟨e1, e2, e3, e4, m, he1_eq, he2_eq, he3_eq, he4_eq,
     he4_9, he43, he32, he21, he1_lt_efin, hS4_lt_efin, hR_eq_m⟩
  rcases five_step_bottom_runs_spec_w18 e4 e3 e2 e1 e_fin he4_9 he43 he32 he21 he1_lt_efin with
    ⟨u_acc, hu_acc_eq, hlen_acc, hwt_acc, hcar_acc⟩
  have hcar_acc_lt : affineCarry u_acc < 16 * 2 ^ e_fin := by
    rw [hcar_acc]
    generalize 81 * 1085 + (2 ^ e1 + 3 * 2 ^ e2 + 9 * 2 ^ e3 + 27 * 2 ^ e4) = B1,
      2 ^ e_fin = ZE at hS4_lt_efin ⊢
    omega
  let Q1 := 3 ^ 10 * (9 * m + 7)
  have hu_base_eq : 3 * R_fin + 2 ^ e_fin = 3 * Q1 + affineCarry u_acc := by
    dsimp [Q1]; rw [hR_eq_m, hcar_acc, Nat.mul_add, Nat.add_assoc]
  rcases hunwind u_acc Q1 hlen_acc hcar_acc_lt hu_base_eq with
    ⟨hw_len, hw_wt, hw_car, hw_key⟩
  have hu_eq_wout : uWinExp18Low B M mask = u_acc ++ zeroRunsSuffix gaps := by
    unfold uWinExp18Low uWinExp18LowRuns
    dsimp only
    rw [← hk4_def, ← hw_eq, ← hb0_def, ← hd3_def, ← ha_eq, ← hq3_def, ← hL_eq, ← hR0_def, hch]
    dsimp only
    rw [← he1_eq, ← he2_eq, ← he3_eq, ← he4_eq]
    have hr_sp : (e4 - 9) :: (e3 - (e4 + 1)) :: (e2 - (e3 + 1)) :: (e1 - (e2 + 1)) :: (e_fin - (e1 + 1)) :: gaps =
        [e4 - 9, e3 - (e4 + 1), e2 - (e3 + 1), e1 - (e2 + 1), e_fin - (e1 + 1)] ++ gaps := rfl
    rw [hr_sp, zeroRunsSuffix_append_and_inj_w18.1, hu_acc_eq, List.append_assoc]
  rcases (⟨uWinExp18Low B M mask, rfl⟩ : ∃ u_x : List Bool, u_x = uWinExp18Low B M mask) with ⟨u_e, hue_def⟩
  have hue_wout : u_e = u_acc ++ zeroRunsSuffix gaps := hue_def.trans hu_eq_wout
  rw [← hue_wout] at hw_len hw_wt hw_car hw_key
  have hlen_final : u_e.length = M - delta3 := by rw [hw_len, ← hL_eq]; omega
  have hwt_final : parityWeight u_e = 4 * ((B + 3) / 4) + 11 := by
    rw [hw_wt, hwt_acc, ← hk4_def]; omega
  have hcar_lt_M : affineCarry u_e < 2 ^ M := by
    have hp16 : 16 * 2 ^ (L - 1) = 2 ^ (L + 3) := by
      rw [show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_add 2 4 (L - 1),
          show 4 + (L - 1) = L + 3 by omega]
    rw [hp16] at hw_car
    exact Nat.lt_of_lt_of_le hw_car (pow2_mono_nat (by rw [hL_eq]; omega))
  have hkey_final : 2 ^ (u_e.length + a) = 3 ^ w * (9 * m + 7) + affineCarry u_e := by
    have hlhs : 2 ^ (L + a) = 3 * R0 + 2 ^ (L - 1) := by
      rw [hR0_def, show L + a = (a + 1) + (L - 1) by omega, Nat.pow_add 2 (a + 1) (L - 1),
          ← h3q3, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
    have hrhs : 3 ^ (4 * k4 + 1) * Q1 = 3 ^ w * (9 * m + 7) := by
      dsimp [Q1]
      rw [← Nat.mul_assoc, ← Nat.pow_add 3 (4 * k4 + 1) 10,
          show (4 * k4 + 1) + 10 = w by rw [hw_eq]]
    rw [hlen_final, ← hL_eq, hlhs, hw_key, hrhs]
  have hmid_ex : ∃ mid : List Bool, u_e = minWeight6Prefix507 ++ mid ++ [true] := by
    rcases zeroRunsSuffix_nonempty_eq_mid_true_w18 (e4 - 9)
      ([e3 - (e4 + 1), e2 - (e3 + 1), e1 - (e2 + 1), e_fin - (e1 + 1)] ++ gaps) with ⟨mid, hmid⟩
    refine ⟨mid, ?_⟩
    rw [hue_wout, hu_acc_eq, List.append_assoc minWeight6Prefix507,
        ← zeroRunsSuffix_append_and_inj_w18.1]
    change minWeight6Prefix507 ++
      zeroRunsSuffix ((e4 - 9) :: ([e3 - (e4 + 1), e2 - (e3 + 1), e1 - (e2 + 1), e_fin - (e1 + 1)] ++ gaps)) = _
    rw [hmid, List.append_assoc]
  have hcore_u : IsCoreParityWord u_e := by
    rcases hmid_ex with ⟨mid, hmid⟩
    exact ⟨by rw [hmid]; rfl, by rw [hmid, List.reverse_append]; rfl⟩
  have hwt_w : parityWeight u_e = w := by rw [hwt_final, ← hk4_def, ← hw_eq]
  have hsh_a : canonicalSuffixShift u_e 1 = a := by
    rcases canonicalSuffixShift_spec_unique u_e 1 (by rw [hwt_w]; omega) (by decide) with
      ⟨_, _, huniq⟩
    symm
    apply huniq a (by rw [hwt_w]; exact ha_lt_P)
    rw [Nat.mul_one, hwt_w, hkey_final, Nat.add_comm]
    exact Nat.add_mul_mod_self_left _ _ _
  have hfh : IsFirstHitOnePair u_e 0 :=
    (first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.2 u_e hcore_u).mpr
      (by rw [hsh_a, ha_eq]; omega)
  have hcar_pos : affineCarry u_e ≥ 1 := by
    rcases hmid_ex with ⟨mid, hmid⟩
    rw [hmid, affineCarry_append]
    have hc1 : affineCarry [true] = 1 := rfl
    rw [hc1, Nat.mul_one]
    have hp := pow2_pos_nat (minWeight6Prefix507 ++ mid).length
    omega
  subst hue_def ha_eq hL_eq hq3_def hd3_def hb0_def hw_eq hk4_def
  exact ⟨hcore_u, hlen_final, hwt_w, hsh_a, hfh, hcar_pos, hcar_lt_M, hmid_ex, ⟨m, hkey_final⟩⟩

private theorem uWinExp18Low_per_mask_leaf_spec_w18
    (B M mask : Nat) (hB : B ≥ 1) (hM : M ≥ dyadicExpWindowMinM18Low B)
    (hmask : mask < 2 ^ B) :
    let k4 := (B + 3) / 4
    let w := 4 * k4 + 11
    let b0 := binBitLength (3 ^ w)
    let delta3 := 3 + dyadicPolyShiftDelta (b0 + 3)
    let u := uWinExp18Low B M mask
    let y := exactBackwardQuotient 1 u 0
    IsFirstHitOnePair u 0 ∧
    u.length = M - delta3 ∧
    u.length ≤ M ∧
    parityWeight u = w ∧
    canonicalSuffixShift u 1 = b0 + delta3 ∧
    y % 512 = 507 ∧
    y % 9 = 7 ∧
    isSurvivingMod373248Bool y = true ∧
    IsSurvivingMod373248Class y ∧
    2 ^ M ≤ y ∧ y < 2 ^ (M + 1) ∧
    (∀ L_max : Nat, L_max ≥ M -> y ∈ dyadicWindowSurvivingQ0Leaves L_max M) := by
  dsimp only
  let k4 := (B + 3) / 4
  let w := 4 * k4 + 11
  let b0 := binBitLength (3 ^ w)
  let delta3 := 3 + dyadicPolyShiftDelta (b0 + 3)
  let a := b0 + delta3
  have hw_eq : w = 4 * k4 + 11 := rfl
  have ha_eq : a = b0 + delta3 := rfl
  rcases pow3_bitlength_strict_bounds_w18 w (by dsimp [w, k4]; omega) with ⟨_, _, h3w_lo, h2b0_hi⟩
  change 3 ^ w + 1 ≤ 2 ^ b0 at h3w_lo
  change 2 ^ b0 < 2 * 3 ^ w at h2b0_hi
  rcases dyadicPolyShiftDelta3_spec_w18 b0 with ⟨_, hd3_hi, _, _, _⟩
  change delta3 ≤ 6 at hd3_hi
  have hM_ge30 : M ≥ 30 := by unfold dyadicExpWindowMinM18Low at hM; omega
  rcases uWinExp18Low_per_mask_core_and_key_w18 B M mask hB hM hmask with
    ⟨hcore_r, hlen_r, hwt_r, hsh_r, hfh_r, hcar_pos_r, hcar_lt_r, ⟨mid, hu_mid_r⟩, ⟨m, hkey_r⟩⟩
  rcases (⟨uWinExp18Low B M mask, rfl⟩ : ∃ u0 : List Bool, u0 = uWinExp18Low B M mask) with ⟨u_e, hue_def⟩
  rw [← hue_def] at hcore_r hlen_r hwt_r hsh_r hfh_r hcar_pos_r hcar_lt_r hu_mid_r hkey_r
  change u_e.length = M - delta3 at hlen_r
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
    exact Nat.eq_of_mul_eq_mul_left (pow3_pos_nat w)
      (Nat.add_right_cancel (heq_bw.symm.trans hkey_r))
  have hy_m9 : y % 9 = 7 := by rw [hy_9m7]; omega
  have hy_m512 : y % 512 = 507 := by
    have hp9_507 : parityOfIter 9 507 = minWeight6Prefix507 := by decide
    have hu_507 : u_e = parityOfIter 9 507 ++ mid ++ [true] := by rw [hp9_507]; exact hu_mid_r
    have hm := (surviving_mod512_nine_prefix_auto_weight_and_characterization.1 507
      (by decide) (by decide)).2.2.2 mid 0 |>.2.2.1
    rwa [← hu_507, ← hy_def] at hm
  rcases isSurvivingMod373248_of_507_and_mod9_eq7_w18 y hy_m512 hy_m9 with ⟨hb_surv, hcls_surv⟩
  have hy_win : 2 ^ M ≤ y ∧ y < 2 ^ (M + 1) := by
    have hLa_eq : u_e.length + a = b0 + M := by rw [hlen_r, ha_eq]; omega
    have heq_y : 3 ^ w * y + affineCarry u_e = 2 ^ b0 * 2 ^ M := by
      have hk := hkey_r.symm
      rwa [← hy_9m7, hLa_eq, Nat.pow_add 2 b0 M] at hk
    have hPM_pos := pow2_pos_nat M
    refine ⟨?_, ?_⟩
    · if hge : 2 ^ M ≤ y then exact hge
      else
        exfalso
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
      if hlt : y < 2 * 2 ^ M then exact hlt
      else
        exfalso
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

private theorem uWinExp18Low_inj_mask_w18
    (B M m1 m2 : Nat) (hB : B ≥ 1) (hM : M ≥ dyadicExpWindowMinM18Low B)
    (hm1 : m1 < 2 ^ B) (hm2 : m2 < 2 ^ B)
    (hy_eq : exactBackwardQuotient 1 (uWinExp18Low B M m1) 0 =
      exactBackwardQuotient 1 (uWinExp18Low B M m2) 0) :
    m1 = m2 := by
  have hfh1 := (uWinExp18Low_per_mask_core_and_key_w18 B M m1 hB hM hm1).2.2.2.2.1
  have hfh2 := (uWinExp18Low_per_mask_core_and_key_w18 B M m2 hB hM hm2).2.2.2.2.1
  have hu_eq : uWinExp18Low B M m1 = uWinExp18Low B M m2 :=
    (first_hit_one_pair_sound_and_injective _ _ 0 0 hfh1 hfh2).2.2.2 hy_eq |>.1
  unfold uWinExp18Low at hu_eq
  have hzs_eq := (list_append_inj_left_eq_len _ _ _ _ rfl hu_eq).2
  have hruns_eq := zeroRunsSuffix_append_and_inj_w18.2 _ _ hzs_eq
  unfold uWinExp18LowRuns at hruns_eq
  dsimp only at hruns_eq
  have hgaps_eq :=
    (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj hruns_eq).2).2).2).2).2
  let k4 := (B + 3) / 4
  let w := 4 * k4 + 11
  let b0 := binBitLength (3 ^ w)
  let delta3 := 3 + dyadicPolyShiftDelta (b0 + 3)
  let a := b0 + delta3
  let q3 := (2 ^ (a + 1) - 1) / 3
  let L := M - delta3
  have hk4_ge1 : k4 ≥ 1 := by dsimp [k4]; omega
  have h18k4_le : 18 * k4 ≤ 5 * B + 13 := by dsimp [k4]; omega
  rcases pow3_bitlength_strict_bounds_w18 w (by dsimp [w]; omega) with ⟨_, _, h3w_lo, _⟩
  change 3 ^ w + 1 ≤ 2 ^ b0 at h3w_lo
  rcases dyadicPolyShiftDelta3_spec_w18 b0 with ⟨hd3_lo, hd3_hi, h3q3, hq3_n3, _⟩
  change 3 ≤ delta3 at hd3_lo
  change delta3 ≤ 6 at hd3_hi
  change 3 * q3 + 1 = 2 ^ (a + 1) at h3q3
  change q3 % 3 ≠ 0 at hq3_n3
  have hL_ge : L ≥ 204 + 5 * B := by dsimp [L]; unfold dyadicExpWindowMinM18Low at hM; omega
  have hR0_n3 : (q3 * 2 ^ (L - 1)) % 3 ≠ 0 := by
    intro h0; rw [Nat.mul_mod] at h0
    have hp2_n3 := pow2_mod3_nonzero_w5 (L - 1)
    have hq3_lt : q3 % 3 < 3 := Nat.mod_lt q3 (by decide)
    have hp2_lt : 2 ^ (L - 1) % 3 < 3 := Nat.mod_lt _ (by decide)
    rcases (by omega : q3 % 3 = 1 ∨ q3 % 3 = 2) with hq | hq <;>
    rcases (by omega : 2 ^ (L - 1) % 3 = 1 ∨ 2 ^ (L - 1) % 3 = 2) with hp | hp <;>
    (rw [hq, hp] at h0; cases h0)
  have hq3_ge : q3 ≥ 2 * 3 ^ (4 * k4 + 10) - 1 := by
    have ha1_ge16 : 2 ^ (a + 1) ≥ 16 * 2 ^ b0 := by
      have h : 2 ^ (4 + b0) ≤ 2 ^ (a + 1) := pow2_mono_nat (by dsimp [a]; omega)
      rwa [Nat.pow_add 2 4 b0] at h
    have hp3_le : 3 ^ (4 * k4 + 10) ≤ 3 ^ w :=
      nat_pow_mono_exp_pos 3 (4 * k4 + 10) w (by decide) (by dsimp [w]; omega)
    have hge16 : 3 * q3 + 1 ≥ 16 * (3 ^ (4 * k4 + 10) + 1) := by
      rw [h3q3]
      exact Nat.le_trans (Nat.mul_le_mul_left 16 (Nat.add_le_add_right hp3_le 1))
        (Nat.le_trans (Nat.mul_le_mul_left 16 h3w_lo) ha1_ge16)
    generalize 3 ^ (4 * k4 + 10) = P3 at hge16 ⊢; omega
  have h16k4 : 2 ^ B ≤ 16 ^ k4 := by
    rw [show (16 : Nat) = 2 ^ 4 from rfl, pow_pow_eq_mul_w5 2 4 k4]
    exact pow2_mono_nat (by dsimp [k4]; omega)
  exact (fourStepTernaryCarryChain_spec_and_inj_w18 k4 (L - 1) (q3 * 2 ^ (L - 1)) (L - 1)
    (Nat.le_refl _) (by omega) hR0_n3 (Nat.mul_le_mul_right _ hq3_ge)).2
    m1 m2 (Nat.lt_of_lt_of_le hm1 h16k4) (Nat.lt_of_lt_of_le hm2 h16k4) hgaps_eq

private def descIdxListW18 : Nat -> List Nat
  | 0 => []
  | r + 1 => r :: descIdxListW18 r

private theorem descIdxListW18_spec :
    ∀ r : Nat,
      (descIdxListW18 r).length = r ∧
      NoDupNat (descIdxListW18 r) ∧
      (∀ j ∈ descIdxListW18 r, j < r)
  | 0 => ⟨rfl, NoDupNat.nil, fun _ hm => by cases hm⟩
  | r + 1 => by
    rcases descIdxListW18_spec r with ⟨hlen, hnd, hlt⟩
    have hnot_mem : r ∉ descIdxListW18 r := fun hm => Nat.lt_irrefl r (hlt r hm)
    refine ⟨by simp [descIdxListW18, hlen], NoDupNat.cons r _ hnot_mem hnd, ?_⟩
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hm
    · omega
    · have := hlt j hm; omega

/--
  Theorem W18.4c (`dyadic_window_sub250_4bit_collision_slope5_exponential_occupancy`,
  `zero custom axioms`):
  1. **Universal `4,374`-Bucket 4-Bit (`s = 4`) Multiplicative-Dlog `Mod 531441` (`3^12`) Bottom
     Collision Certificate (`stride = 81`):**
     For EVERY `k < 354294`, `(e_4, e_3, e_2, e_1)` from `bottom4BitBucket531441 (k / 81) + k % 81`
     satisfies `9 ≤ e_4 < e_3 < e_2 < e_1 ≤ 181` and
     `(2 ^ e_1 + 3 * 2 ^ e_2 + 9 * 2 ^ e_3 + 27 * 2 ^ e_4) % 531441 = 2 ^ k % 531441`!
  2. **Unconditional Sub-`250` Threshold (`M_0 = 210 ≤ 250`, Down from `360`!) & Strictly Steeper-Slope
     (`c = 5 ≤ 5`, Beating `c = 6`!) Exponential Surviving-Leaf Dyadic-Window Occupancy:**
     Across ALL `B ≥ 1` and ALL `M ≥ dyadicExpWindowMinM18Low B` (`= 210 + 5 * B`), `uWinExp18Low B M`
     maps `0 .. 2^B - 1` injectively into surviving `Mod373248` first-hit `q = 0` leaves inside
     `[2^M, 2^(M+1))` at linear length `L = M - delta3 ≤ M`; hence for ALL `M ≥ 215` and ALL `L_max ≥ M`,
     `(dyadicWindowSurvivingQ0Leaves L_max M).length ≥ 2 ^ ((M - 210) / 5)` (`Branches P2.2 & P5.3`, `W18_H4`)!
-/
theorem dyadic_window_sub250_4bit_collision_slope5_exponential_occupancy :
    (∀ k : Nat, k < 354294 ->
      let b := bottom4BitBucket531441 (k / 81)
      let t := k % 81
      9 ≤ b.2.2.2 + t ∧
      b.2.2.2 + t < b.2.2.1 + t ∧
      b.2.2.1 + t < b.2.1 + t ∧
      b.2.1 + t < b.1 + t ∧
      b.1 + t ≤ 181 ∧
      (2 ^ (b.1 + t) + 3 * 2 ^ (b.2.1 + t) + 9 * 2 ^ (b.2.2.1 + t) +
        27 * 2 ^ (b.2.2.2 + t)) % 531441 = 2 ^ k % 531441) ∧
    (∀ (B M : Nat), B ≥ 1 -> M ≥ dyadicExpWindowMinM18Low B ->
      let k4 := (B + 3) / 4
      let w := 4 * k4 + 11
      let b0 := binBitLength (3 ^ w)
      let delta3 := 3 + dyadicPolyShiftDelta (b0 + 3)
      (∀ mask : Nat, mask < 2 ^ B ->
        let u := uWinExp18Low B M mask
        let y := exactBackwardQuotient 1 u 0
        IsFirstHitOnePair u 0 ∧
        u.length = M - delta3 ∧
        u.length ≤ M ∧
        parityWeight u = w ∧
        canonicalSuffixShift u 1 = b0 + delta3 ∧
        y % 512 = 507 ∧
        y % 9 = 7 ∧
        IsSurvivingMod373248Class y ∧
        2 ^ M ≤ y ∧ y < 2 ^ (M + 1) ∧
        y ∈ dyadicWindowSurvivingQ0Leaves M M ∧
        (∀ L_max : Nat, L_max ≥ M -> y ∈ dyadicWindowSurvivingQ0Leaves L_max M)) ∧
      (∀ m1 m2 : Nat, m1 < 2 ^ B -> m2 < 2 ^ B ->
        exactBackwardQuotient 1 (uWinExp18Low B M m1) 0 =
          exactBackwardQuotient 1 (uWinExp18Low B M m2) 0 ->
        m1 = m2) ∧
      ((dyadicWindowSurvivingQ0Leaves M M).length ≥ 2 ^ B ∧
       ∀ L_max : Nat, L_max ≥ M ->
         (dyadicWindowSurvivingQ0Leaves L_max M).length ≥ 2 ^ B)) ∧
    (∀ (M L_max : Nat), M ≥ 215 -> L_max ≥ M ->
      (dyadicWindowSurvivingQ0Leaves L_max M).length ≥ 2 ^ ((M - 210) / 5)) := by
  have hmain : ∀ (B M : Nat), B ≥ 1 -> M ≥ dyadicExpWindowMinM18Low B ->
      let k4 := (B + 3) / 4
      let w := 4 * k4 + 11
      let b0 := binBitLength (3 ^ w)
      let delta3 := 3 + dyadicPolyShiftDelta (b0 + 3)
      (∀ mask : Nat, mask < 2 ^ B ->
        let u := uWinExp18Low B M mask
        let y := exactBackwardQuotient 1 u 0
        IsFirstHitOnePair u 0 ∧
        u.length = M - delta3 ∧
        u.length ≤ M ∧
        parityWeight u = w ∧
        canonicalSuffixShift u 1 = b0 + delta3 ∧
        y % 512 = 507 ∧
        y % 9 = 7 ∧
        IsSurvivingMod373248Class y ∧
        2 ^ M ≤ y ∧ y < 2 ^ (M + 1) ∧
        y ∈ dyadicWindowSurvivingQ0Leaves M M ∧
        (∀ L_max : Nat, L_max ≥ M -> y ∈ dyadicWindowSurvivingQ0Leaves L_max M)) ∧
      (∀ m1 m2 : Nat, m1 < 2 ^ B -> m2 < 2 ^ B ->
        exactBackwardQuotient 1 (uWinExp18Low B M m1) 0 =
          exactBackwardQuotient 1 (uWinExp18Low B M m2) 0 ->
        m1 = m2) ∧
      ((dyadicWindowSurvivingQ0Leaves M M).length ≥ 2 ^ B ∧
       ∀ L_max : Nat, L_max ≥ M ->
         (dyadicWindowSurvivingQ0Leaves L_max M).length ≥ 2 ^ B) := by
    intro B M hB hM; dsimp only
    refine ⟨?_, fun m1 m2 h1 h2 heq => uWinExp18Low_inj_mask_w18 B M m1 m2 hB hM h1 h2 heq, ?_⟩
    · intro mask hmask
      rcases uWinExp18Low_per_mask_leaf_spec_w18 B M mask hB hM hmask with
        ⟨hfh, hlen, hle_M, hwt, hsh, h512, h9, _, hcls, hlo, hhi, hmem⟩
      exact ⟨hfh, hlen, hle_M, hwt, hsh, h512, h9, hcls, hlo, hhi, hmem M (Nat.le_refl M), hmem⟩
    · rcases descIdxListW18_spec (2 ^ B) with ⟨hd_len, hd_nd, hd_lt⟩
      let fnLeaf : Nat -> Nat := fun mask => exactBackwardQuotient 1 (uWinExp18Low B M mask) 0
      let leaves2B := (descIdxListW18 (2 ^ B)).map fnLeaf
      have hnd_2B : NoDupNat leaves2B :=
        noDupNat_map_inj_on_cf_w18 fnLeaf (descIdxListW18 (2 ^ B)) hd_nd
          (fun a ha b hb heq => uWinExp18Low_inj_mask_w18 B M a b hB hM (hd_lt a ha) (hd_lt b hb) heq)
      have hlen_2B : leaves2B.length = 2 ^ B := by
        dsimp only [leaves2B]; rw [List.length_map, hd_len]
      have hall_L : ∀ L_max : Nat, L_max ≥ M ->
          (dyadicWindowSurvivingQ0Leaves L_max M).length ≥ 2 ^ B := by
        intro L_max hL_max
        have hsub_2B : ∀ y ∈ leaves2B, y ∈ dyadicWindowSurvivingQ0Leaves L_max M := by
          intro y hy
          rcases List.mem_map.mp hy with ⟨mask, hmask, rfl⟩
          exact (uWinExp18Low_per_mask_leaf_spec_w18 B M mask hB hM (hd_lt mask hmask)).2.2.2.2.2.2.2.2.2.2.2 L_max hL_max
        have hle := noDupNat_length_le_of_subset_cf_w18
          (dyadicWindowSurvivingQ0Leaves L_max M) leaves2B hnd_2B hsub_2B
        omega
      exact ⟨hall_L M (Nat.le_refl M), hall_L⟩
  refine ⟨bottom4BitBucket531441_mod_spec, hmain, ?_⟩
  intro M L_max hM hL_max
  let B := (M - 210) / 5
  have hB1 : B ≥ 1 := by dsimp [B]; omega
  have hM_min : M ≥ dyadicExpWindowMinM18Low B := by
    dsimp [B]; unfold dyadicExpWindowMinM18Low; omega
  exact (hmain B M hB1 hM_min).2.2.2 L_max hL_max


-- ============================================================================
-- SECTION 4: Front A Part 3 & Front B Part 3 (Branches P4.3 & P3.4) —
--            Unconditional `1..25`-Cycle Freedom Across ALL `DP2` Words,
--            Universal Symbolic All-`m` (`∀ m ≥ 2`) `(m - 1)`-Pivot Closed-Form
--            Geometric Identity & Parametric `(m, w, a, a_tail, d_a, d_mult)`
--            Brox / `DP2` Infinite-Family Exclusions, & `m = 7` Benchmarks
-- ============================================================================

-- Section 1C: Unconditional `1..25`-Cycle Freedom Across ALL `DP2` Words &
--             Universal Symbolic All-`m` (`∀ m ≥ 2`) Infinite Parametric `m`-Block
--             `.R`-Carrying `leftAnchoredDP2Step` Cycle Exclusions (`W18_H1`)
-- ----------------------------------------------------------------------------

private def syrStepW18 (n : Nat) : Nat := core2 (3 * n + 1)

private def syrIterW18 : Nat -> Nat -> Nat
  | 0, n => n
  | k + 1, n => syrIterW18 k (syrStepW18 n)

private theorem syrIterW18_add :
    ∀ (a b n : Nat), syrIterW18 (a + b) n = syrIterW18 b (syrIterW18 a n)
  | 0, _, _ => by rw [Nat.zero_add]; rfl
  | a + 1, b, n => by rw [Nat.succ_add]; exact syrIterW18_add a b (syrStepW18 n)

set_option maxRecDepth 65536 in
private theorem no_small_odd_syr_cycles_21_to_25_w18 :
    ∀ (r : Fin 26) (k : Fin 72),
      21 ≤ r.val -> syrIterW18 r.val (2 * k.val + 3) ≠ 2 * k.val + 3 := by decide

private theorem dp2AnnotatedChain_syr_and_ge147_bound_w18 :
    ∀ (shifts : List Nat) (u0 ur : List MixedSRSSym),
      dp2AnnotatedChain u0 shifts ur ->
      dp2GlobalOddVal ur = syrIterW18 shifts.length (dp2GlobalOddVal u0) ∧
      ((∃ n : Nat, 3 ≤ n ∧ n ≤ 145 ∧ n % 2 = 1 ∧
          ∃ i : Nat, i ≤ shifts.length ∧
            syrIterW18 i (dp2GlobalOddVal u0) = n ∧
            dp2GlobalOddVal ur = syrIterW18 (shifts.length - i) n) ∨
       147 ^ shifts.length * 2 ^ dp2ShiftSum shifts * dp2GlobalOddVal ur ≤
         442 ^ shifts.length * dp2GlobalOddVal u0)
  | [], u0, ur, heq => by
    subst heq; exact ⟨rfl, Or.inr (by simp [dp2ShiftSum])⟩
  | a :: rest, u0, ur, ⟨_, w, _, hsyr_step, htl⟩ => by
    have hNw_pos : dp2GlobalOddVal w > 0 := by unfold dp2GlobalOddVal; omega
    have hNw_odd : dp2GlobalOddVal w % 2 = 1 := by unfold dp2GlobalOddVal; omega
    have hNu_ge3 : dp2GlobalOddVal u0 ≥ 3 := by unfold dp2GlobalOddVal; omega
    have hNu_odd : dp2GlobalOddVal u0 % 2 = 1 := by unfold dp2GlobalOddVal; omega
    have hsyr_eq : syrStepW18 (dp2GlobalOddVal u0) = dp2GlobalOddVal w := by
      unfold syrStepW18
      rw [← hsyr_step, core2_pow2_mul a (dp2GlobalOddVal w) hNw_pos hNw_odd]
    rcases dp2AnnotatedChain_syr_and_ge147_bound_w18 rest w ur htl with ⟨ih_syr, ih_disj⟩
    have hiter_tot : dp2GlobalOddVal ur = syrIterW18 (rest.length + 1) (dp2GlobalOddVal u0) := by
      simp only [syrIterW18, hsyr_eq]; exact ih_syr
    simp only [List.length_cons, dp2ShiftSum]
    refine ⟨hiter_tot, ?_⟩
    by_cases hle145 : dp2GlobalOddVal u0 ≤ 145
    · left
      exact ⟨dp2GlobalOddVal u0, hNu_ge3, hle145, hNu_odd, 0, Nat.zero_le _, rfl, hiter_tot⟩
    · rcases ih_disj with ⟨n, hn3, hn145, hno, i, hi_le, hi_eq, hur_eq⟩ | ih_ge147
      · left
        refine ⟨n, hn3, hn145, hno, i + 1, Nat.succ_le_succ hi_le, ?_, ?_⟩
        · simp only [syrIterW18, hsyr_eq]; exact hi_eq
        · rw [Nat.succ_sub_succ]; exact hur_eq
      · right
        have hstep147 : 147 * (2 ^ a * dp2GlobalOddVal w) ≤ 442 * dp2GlobalOddVal u0 := by
          rw [hsyr_step]; omega
        rw [Nat.pow_succ 147 rest.length, Nat.pow_add 2 a (dp2ShiftSum rest),
            Nat.pow_succ 442 rest.length]
        calc
          ((147 ^ rest.length * 147) * (2 ^ a * 2 ^ dp2ShiftSum rest)) * dp2GlobalOddVal ur
              = 2 ^ a * (147 * (147 ^ rest.length * 2 ^ dp2ShiftSum rest * dp2GlobalOddVal ur)) := by ac_rfl
          _ ≤ 2 ^ a * (147 * (442 ^ rest.length * dp2GlobalOddVal w)) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 147 ih_ge147)
          _ = 442 ^ rest.length * (147 * (2 ^ a * dp2GlobalOddVal w)) := by ac_rfl
          _ ≤ 442 ^ rest.length * (442 * dp2GlobalOddVal u0) :=
                Nat.mul_le_mul_left _ hstep147
          _ = (442 ^ rest.length * 442) * dp2GlobalOddVal u0 := by ac_rfl

/-- Shared symbolic all-`m` (`∀ m ≥ 2`) closed-form `(m - 1)`-pivot upper bound AND strict `< 3 * D`
    Archimedean elimination helper for balanced/tail-heavy tuples `[(w, a)^(m - 1), (w, a_tail)]`. -/
private theorem all_m_balanced_pivot_ub_closed_w18
    (m w a a_tail : Nat) (hm : m ≥ 2) (hw : w ≥ 1) (ha : a ≥ 1) (hat : a_tail ≥ 1)
    (hrate : 2 * 2 ^ (w + a) ≤ 3 ^ w) :
    let pivots := List.replicate (m - 2) (w, a)
    let blocks := List.replicate (m - 1) (w, a) ++ [(w, a_tail)]
    let W := blockWeightSum blocks
    let K := blockStepSum blocks
    pivots ++ ((w, a) :: [(w, a_tail)]) = blocks ∧
    W = m * w ∧
    K = (m - 1) * (w + a) + (w + a_tail) ∧
    multiPivotCarryUB pivots (w, a) [(w, a_tail)] ≤
      2 * (2 ^ a - 1) * 3 ^ ((m - 1) * w) +
        2 ^ ((m - 2) * (w + a)) * 3 ^ w * (2 ^ (a + a_tail) - 1) ∧
    (2 * 3 ^ W ≤ 2 ^ K ->
      multiPivotCarryUB pivots (w, a) [(w, a_tail)] < 3 * (2 ^ K - 3 ^ W)) := by
  dsimp only
  have hrep_wt : ∀ k : Nat,
      blockWeightSum (List.replicate k (w, a)) = k * w ∧
      blockStepSum (List.replicate k (w, a)) = k * (w + a) := by
    intro k; induction k with
    | zero => simp [blockWeightSum, blockStepSum]
    | succ k' ih =>
      simp only [List.replicate_succ, blockWeightSum, blockStepSum, ih.1, ih.2, Nat.succ_mul]
      omega
  have hwt_app : ∀ xs ys : List (Nat × Nat),
      blockWeightSum (xs ++ ys) = blockWeightSum xs + blockWeightSum ys ∧
      blockStepSum (xs ++ ys) = blockStepSum xs + blockStepSum ys := by
    intro xs ys; induction xs with
    | nil => simp [blockWeightSum, blockStepSum]
    | cons x xtl ih => simp only [List.cons_append, blockWeightSum, blockStepSum, ih.1, ih.2]; omega
  have hrep_add : ∀ {α : Type} (c1 c2 : Nat) (x : α),
      List.replicate (c1 + c2) x = List.replicate c1 x ++ List.replicate c2 x := by
    intro α c1 c2 x; induction c1 with
    | zero => simp [List.replicate]
    | succ k' ih => rw [Nat.succ_add, List.replicate_succ, List.replicate_succ, ih, List.cons_append]
  have hsplit_blk : List.replicate (m - 2) (w, a) ++ ((w, a) :: [(w, a_tail)]) =
      List.replicate (m - 1) (w, a) ++ [(w, a_tail)] := by
    have hm1 : m - 1 = (m - 2) + 1 := by omega
    rw [hm1, hrep_add]
    simp [List.replicate, List.append_assoc]
  have hW_eq : blockWeightSum (List.replicate (m - 1) (w, a) ++ [(w, a_tail)]) = m * w := by
    rw [(hwt_app _ _).1, (hrep_wt (m - 1)).1]
    simp only [blockWeightSum, Nat.add_zero]
    have hm1 : (m - 1) * w + w = ((m - 1) + 1) * w := by rw [Nat.add_mul, Nat.one_mul]
    rw [hm1, show (m - 1) + 1 = m by omega]
  have hK_eq : blockStepSum (List.replicate (m - 1) (w, a) ++ [(w, a_tail)]) =
      (m - 1) * (w + a) + (w + a_tail) := by
    rw [(hwt_app _ _).2, (hrep_wt (m - 1)).2]
    simp [blockStepSum]
  have hind : ∀ k : Nat,
      multiPivotCarryUB (List.replicate k (w, a)) (w, a) [(w, a_tail)] ≤
        2 * (2 ^ a - 1) * 3 ^ ((k + 1) * w) +
          2 ^ (k * (w + a)) * 3 ^ w * (2 ^ (a + a_tail) - 1) := by
    intro k; induction k with
    | zero =>
      simp only [List.replicate, multiPivotCarryUB, blockWeightSum, blockStepSum,
                 Nat.zero_mul, Nat.one_mul, Nat.pow_zero, Nat.add_zero]
      have hexp_sub : (w + a + (w + a_tail)) - (w + w) = a + a_tail := by omega
      rw [hexp_sub]
      omega
    | succ k' ih =>
      have hsub_wt : blockWeightSum (List.replicate k' (w, a) ++ [(w, a), (w, a_tail)]) = (k' + 2) * w := by
        rw [(hwt_app _ _).1, (hrep_wt k').1]
        simp only [blockWeightSum, Nat.add_zero]
        have : k' * w + (w + w) = (k' + 2) * w := by simp only [Nat.add_mul]; omega
        exact this
      have hstep_ub : multiPivotCarryUB (List.replicate (k' + 1) (w, a)) (w, a) [(w, a_tail)] =
          3 ^ ((k' + 2) * w) * (2 ^ a - 1) +
            2 ^ (w + a) * multiPivotCarryUB (List.replicate k' (w, a)) (w, a) [(w, a_tail)] := by
        conv => lhs; rw [List.replicate_succ]; unfold multiPivotCarryUB
        dsimp only
        rw [hsub_wt]
        cases k' <;> simp only [List.replicate, Nat.add_comm a w]
      rw [hstep_ub]
      have hm_ih := Nat.mul_le_mul_left (2 ^ (w + a)) ih
      rw [Nat.mul_add (2 ^ (w + a))] at hm_ih
      have ht1 : 2 ^ (w + a) * (2 * (2 ^ a - 1) * 3 ^ ((k' + 1) * w)) ≤
          3 ^ w * ((2 ^ a - 1) * 3 ^ ((k' + 1) * w)) := by
        calc 2 ^ (w + a) * (2 * (2 ^ a - 1) * 3 ^ ((k' + 1) * w))
            = (2 * 2 ^ (w + a)) * ((2 ^ a - 1) * 3 ^ ((k' + 1) * w)) := by ac_rfl
          _ ≤ 3 ^ w * ((2 ^ a - 1) * 3 ^ ((k' + 1) * w)) := Nat.mul_le_mul_right _ hrate
      have ht1_pow : 3 ^ w * ((2 ^ a - 1) * 3 ^ ((k' + 1) * w)) =
          (2 ^ a - 1) * 3 ^ ((k' + 2) * w) := by
        calc 3 ^ w * ((2 ^ a - 1) * 3 ^ ((k' + 1) * w))
            = (2 ^ a - 1) * (3 ^ w * 3 ^ ((k' + 1) * w)) := by ac_rfl
          _ = (2 ^ a - 1) * 3 ^ (w + (k' + 1) * w) := by rw [← Nat.pow_add]
          _ = (2 ^ a - 1) * 3 ^ ((k' + 2) * w) := by
              congr 2; simp only [Nat.add_mul, Nat.one_mul]; omega
      have ht2 : 2 ^ (w + a) * (2 ^ (k' * (w + a)) * 3 ^ w * (2 ^ (a + a_tail) - 1)) =
          2 ^ ((k' + 1) * (w + a)) * 3 ^ w * (2 ^ (a + a_tail) - 1) := by
        calc 2 ^ (w + a) * (2 ^ (k' * (w + a)) * 3 ^ w * (2 ^ (a + a_tail) - 1))
            = (2 ^ (w + a) * 2 ^ (k' * (w + a))) * 3 ^ w * (2 ^ (a + a_tail) - 1) := by ac_rfl
          _ = 2 ^ ((w + a) + k' * (w + a)) * 3 ^ w * (2 ^ (a + a_tail) - 1) := by rw [← Nat.pow_add]
          _ = 2 ^ ((k' + 1) * (w + a)) * 3 ^ w * (2 ^ (a + a_tail) - 1) := by
              congr 3; rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      rw [ht1_pow] at ht1
      rw [ht2] at hm_ih
      have hcomm1 : 3 ^ ((k' + 2) * w) * (2 ^ a - 1) = (2 ^ a - 1) * 3 ^ ((k' + 2) * w) := Nat.mul_comm _ _
      rw [hcomm1, show 2 * (2 ^ a - 1) * 3 ^ ((k' + 1 + 1) * w) = 2 * ((2 ^ a - 1) * 3 ^ ((k' + 2) * w)) from
        Nat.mul_assoc 2 (2 ^ a - 1) (3 ^ ((k' + 2) * w))]
      generalize (2 ^ a - 1) * 3 ^ ((k' + 2) * w) = P1,
        2 ^ ((k' + 1) * (w + a)) * 3 ^ w * (2 ^ (a + a_tail) - 1) = P2,
        2 ^ (w + a) * multiPivotCarryUB (List.replicate k' (w, a)) (w, a) [(w, a_tail)] = LHS_M,
        2 ^ (w + a) * (2 * (2 ^ a - 1) * 3 ^ ((k' + 1) * w)) = MID_M at hm_ih ht1 ⊢
      omega
  have hub_m := hind (m - 2)
  rw [show (m - 2) + 1 = m - 1 by omega] at hub_m
  refine ⟨hsplit_blk, hW_eq, hK_eq, hub_m, ?_⟩
  intro h2_3W
  rw [hW_eq, hK_eq] at h2_3W ⊢
  -- Bound Term 1: `2 * (2^a - 1) * 3^((m - 1)*w) < 3^(m*w)`:
  have h2a_lt_3w : 2 * (2 ^ a - 1) < 3 ^ w := by
    have hp_w : 2 ^ w ≥ 2 := by simpa using pow2_mono_nat hw
    have hp_a : 2 ^ a ≥ 2 := by simpa using pow2_mono_nat ha
    have h1 : 2 * (2 ^ a - 1) < 2 * (2 ^ w * 2 ^ a) := by
      have : 2 ^ a - 1 < 1 * 2 ^ a := by omega
      have hle_wa : 1 * 2 ^ a ≤ 2 ^ w * 2 ^ a := Nat.mul_le_mul_right _ (by omega)
      omega
    rw [← Nat.pow_add 2 w a] at h1
    exact Nat.lt_of_lt_of_le h1 hrate
  have hterm1_lt : 2 * (2 ^ a - 1) * 3 ^ ((m - 1) * w) < 3 ^ (m * w) := by
    have hp3_pos : 3 ^ ((m - 1) * w) > 0 := pow3_pos_nat _
    have hm_lt := Nat.mul_lt_mul_of_pos_right h2a_lt_3w hp3_pos
    have hexp_m : w + (m - 1) * w = m * w := by
      have : (1 + (m - 1)) * w = m * w := by rw [show 1 + (m - 1) = m by omega]
      rwa [Nat.add_mul, Nat.one_mul] at this
    rwa [← Nat.pow_add 3 w ((m - 1) * w), hexp_m] at hm_lt
  -- Bound Term 2: `2^((m - 2)*(w + a)) * 3^w * (2^(a + a_tail) - 1) < 2^((m - 1)*(w + a) + (w + a_tail))`:
  have h3w_lt_4w : 3 ^ w < 2 ^ (2 * w) := by
    have h4 : 2 ^ (2 * w) = 4 ^ w := (pow_pow_eq_mul_w5 2 2 w).symm
    rw [h4]
    have hst : ∀ n : Nat, n ≥ 1 -> 3 ^ n < 4 ^ n := by
      intro n hn; induction n with
      | zero => omega
      | succ n' ihn =>
        cases n' with
        | zero => decide
        | succ q =>
          have ihq := ihn (by omega)
          rw [Nat.pow_succ 3, Nat.pow_succ 4]
          have hpos4 : 4 ^ (q + 1) > 0 := nat_pow_pos_of_pos 4 (by decide) _
          calc 3 ^ (q + 1) * 3 < 4 ^ (q + 1) * 3 := Nat.mul_lt_mul_of_pos_right ihq (by decide)
            _ < 4 ^ (q + 1) * 4 := Nat.mul_lt_mul_of_pos_left (by decide) hpos4
    exact hst w hw
  have hterm2_lt : 2 ^ ((m - 2) * (w + a)) * 3 ^ w * (2 ^ (a + a_tail) - 1) <
      2 ^ ((m - 1) * (w + a) + (w + a_tail)) := by
    have hp_at_pos : 2 ^ (a + a_tail) ≥ 2 := by simpa using pow2_mono_nat (by omega : 1 ≤ a + a_tail)
    have hp_le : 2 ^ (a + a_tail) - 1 ≤ 2 ^ (a + a_tail) := by omega
    have hle1 : 2 ^ ((m - 2) * (w + a)) * 3 ^ w * (2 ^ (a + a_tail) - 1) ≤
        (2 ^ ((m - 2) * (w + a)) * 2 ^ (a + a_tail)) * 3 ^ w := by
      calc 2 ^ ((m - 2) * (w + a)) * 3 ^ w * (2 ^ (a + a_tail) - 1)
          ≤ 2 ^ ((m - 2) * (w + a)) * 3 ^ w * 2 ^ (a + a_tail) := Nat.mul_le_mul_left _ hp_le
        _ = (2 ^ ((m - 2) * (w + a)) * 2 ^ (a + a_tail)) * 3 ^ w := by ac_rfl
    have hp_prod_pos : 2 ^ ((m - 2) * (w + a)) * 2 ^ (a + a_tail) > 0 :=
      Nat.mul_pos (nat_pow_pos_of_pos 2 (by decide) _) (nat_pow_pos_of_pos 2 (by decide) _)
    have hlt2 := Nat.mul_lt_mul_of_pos_left h3w_lt_4w hp_prod_pos
    have hexp_tot : (m - 2) * (w + a) + (a + a_tail) + 2 * w = (m - 1) * (w + a) + (w + a_tail) := by
      have hm1 : (m - 1) * (w + a) = (m - 2) * (w + a) + (w + a) := by
        conv => lhs; rw [show m - 1 = (m - 2) + 1 by omega, Nat.add_mul, Nat.one_mul]
      omega
    have htot := Nat.lt_of_le_of_lt hle1 hlt2
    rwa [← Nat.pow_add, ← Nat.pow_add, hexp_tot] at htot
  generalize multiPivotCarryUB (List.replicate (m - 2) (w, a)) (w, a) [(w, a_tail)] = UB,
    2 * (2 ^ a - 1) * 3 ^ ((m - 1) * w) = T1,
    2 ^ ((m - 2) * (w + a)) * 3 ^ w * (2 ^ (a + a_tail) - 1) = T2,
    3 ^ (m * w) = P3W,
    2 ^ ((m - 1) * (w + a) + (w + a_tail)) = P2K at hub_m hterm1_lt hterm2_lt h2_3W ⊢
  omega

-- Exact closed-form geometric `(m - 1)`-pivot identity across ALL `m ≥ 2` when `2^(w + a) ≤ 3^w`:
private theorem all_m_balanced_pivot_exact_geom_w18
    (m w a a_tail : Nat) (_hm : m ≥ 2) (hle : 2 ^ (w + a) ≤ 3 ^ w) :
    (3 ^ w - 2 ^ (w + a)) *
        multiPivotCarryUB (List.replicate (m - 2) (w, a)) (w, a) [(w, a_tail)] =
      (3 ^ ((m - 2) * w) - 2 ^ ((m - 2) * (w + a))) * 3 ^ (2 * w) * (2 ^ a - 1) +
        (3 ^ w - 2 ^ (w + a)) * 2 ^ ((m - 2) * (w + a)) * 3 ^ w * (2 ^ (a + a_tail) - 1) := by
  have hrep_wt : ∀ k : Nat, blockWeightSum (List.replicate k (w, a)) = k * w := by
    intro k; induction k with
    | zero => simp [blockWeightSum]
    | succ k' ih => simp only [List.replicate_succ, blockWeightSum, ih, Nat.succ_mul]; omega
  have hwt_app : ∀ xs ys : List (Nat × Nat),
      blockWeightSum (xs ++ ys) = blockWeightSum xs + blockWeightSum ys := by
    intro xs ys; induction xs with
    | nil => simp [blockWeightSum]
    | cons x xtl ih => simp only [List.cons_append, blockWeightSum, ih]; omega
  have hpow_le : ∀ k : Nat, 2 ^ (k * (w + a)) ≤ 3 ^ (k * w) := by
    intro k; induction k with
    | zero => simp
    | succ k' ih =>
      rw [Nat.succ_mul k' (w + a), Nat.succ_mul k' w,
          Nat.pow_add 2 (k' * (w + a)) (w + a), Nat.pow_add 3 (k' * w) w]
      exact Nat.mul_le_mul ih hle
  have hind : ∀ k : Nat,
      (3 ^ w - 2 ^ (w + a)) * multiPivotCarryUB (List.replicate k (w, a)) (w, a) [(w, a_tail)] =
        (3 ^ (k * w) - 2 ^ (k * (w + a))) * 3 ^ (2 * w) * (2 ^ a - 1) +
          (3 ^ w - 2 ^ (w + a)) * 2 ^ (k * (w + a)) * 3 ^ w * (2 ^ (a + a_tail) - 1) := by
    intro k; induction k with
    | zero =>
      simp only [List.replicate, multiPivotCarryUB, blockWeightSum, blockStepSum,
                 Nat.zero_mul, Nat.pow_zero, Nat.sub_self, Nat.zero_add, Nat.add_zero]
      rw [show (w + a + (w + a_tail)) - (w + w) = a + a_tail by omega]
      ac_rfl
    | succ k' ih =>
      have hsub_wt : blockWeightSum (List.replicate k' (w, a) ++ [(w, a), (w, a_tail)]) =
          (k' + 2) * w := by
        rw [hwt_app, hrep_wt k']
        simp only [blockWeightSum, Nat.add_zero, Nat.add_mul]
        omega
      have hstep_ub : multiPivotCarryUB (List.replicate (k' + 1) (w, a)) (w, a) [(w, a_tail)] =
          3 ^ ((k' + 2) * w) * (2 ^ a - 1) +
            2 ^ (w + a) * multiPivotCarryUB (List.replicate k' (w, a)) (w, a) [(w, a_tail)] := by
        conv => lhs; rw [List.replicate_succ]; unfold multiPivotCarryUB
        dsimp only
        rw [hsub_wt]
        cases k' <;> simp only [List.replicate, Nat.add_comm a w]
      rw [hstep_ub, Nat.mul_add (3 ^ w - 2 ^ (w + a)),
          Nat.mul_left_comm (3 ^ w - 2 ^ (w + a)) (2 ^ (w + a)),
          ih, Nat.mul_add (2 ^ (w + a))]
      have h3_split : 3 ^ ((k' + 2) * w) = 3 ^ (k' * w) * 3 ^ (2 * w) := by
        rw [← Nat.pow_add, show k' * w + 2 * w = (k' + 2) * w by simp [Nat.add_mul]]
      have ht1_id : (3 ^ w - 2 ^ (w + a)) * 3 ^ (k' * w) +
          2 ^ (w + a) * (3 ^ (k' * w) - 2 ^ (k' * (w + a))) =
          3 ^ ((k' + 1) * w) - 2 ^ ((k' + 1) * (w + a)) := by
        have hk_le := hpow_le k'
        have hm1 : 2 ^ (w + a) * 2 ^ (k' * (w + a)) ≤ 2 ^ (w + a) * 3 ^ (k' * w) :=
          Nat.mul_le_mul_left _ hk_le
        have hm2 : 2 ^ (w + a) * 3 ^ (k' * w) ≤ 3 ^ w * 3 ^ (k' * w) :=
          Nat.mul_le_mul_right _ hle
        have hp3_s : 3 ^ ((k' + 1) * w) = 3 ^ w * 3 ^ (k' * w) := by
          rw [← Nat.pow_add, show w + k' * w = (k' + 1) * w by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]]
        have hp2_s : 2 ^ ((k' + 1) * (w + a)) = 2 ^ (w + a) * 2 ^ (k' * (w + a)) := by
          rw [← Nat.pow_add, show (w + a) + k' * (w + a) = (k' + 1) * (w + a) by
            rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]]
        rw [Nat.sub_mul, Nat.mul_sub, hp3_s, hp2_s]
        generalize 3 ^ w * 3 ^ (k' * w) = A1,
                   2 ^ (w + a) * 3 ^ (k' * w) = A2,
                   2 ^ (w + a) * 2 ^ (k' * (w + a)) = A3 at hm1 hm2 ⊢
        omega
      have ht2_id : 2 ^ (w + a) *
          ((3 ^ w - 2 ^ (w + a)) * 2 ^ (k' * (w + a)) * 3 ^ w * (2 ^ (a + a_tail) - 1)) =
          (3 ^ w - 2 ^ (w + a)) * 2 ^ ((k' + 1) * (w + a)) * 3 ^ w * (2 ^ (a + a_tail) - 1) := by
        have hp2_s : 2 ^ (w + a) * 2 ^ (k' * (w + a)) = 2 ^ ((k' + 1) * (w + a)) := by
          rw [← Nat.pow_add, show (w + a) + k' * (w + a) = (k' + 1) * (w + a) by
            rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]]
        calc 2 ^ (w + a) *
               ((3 ^ w - 2 ^ (w + a)) * 2 ^ (k' * (w + a)) * 3 ^ w * (2 ^ (a + a_tail) - 1))
            = (3 ^ w - 2 ^ (w + a)) * (2 ^ (w + a) * 2 ^ (k' * (w + a))) *
                3 ^ w * (2 ^ (a + a_tail) - 1) := by ac_rfl
          _ = (3 ^ w - 2 ^ (w + a)) * 2 ^ ((k' + 1) * (w + a)) *
                3 ^ w * (2 ^ (a + a_tail) - 1) := by rw [hp2_s]
      rw [h3_split, ht2_id]
      have hcomb1 : (3 ^ w - 2 ^ (w + a)) * (3 ^ (k' * w) * 3 ^ (2 * w) * (2 ^ a - 1)) +
          2 ^ (w + a) * ((3 ^ (k' * w) - 2 ^ (k' * (w + a))) * 3 ^ (2 * w) * (2 ^ a - 1)) =
          ((3 ^ w - 2 ^ (w + a)) * 3 ^ (k' * w) +
            2 ^ (w + a) * (3 ^ (k' * w) - 2 ^ (k' * (w + a)))) * 3 ^ (2 * w) * (2 ^ a - 1) := by
        simp only [Nat.add_mul]; ac_rfl
      rw [← Nat.add_assoc, hcomb1, ht1_id]
  exact hind (m - 2)

-- General parametric `(m, w, a, a_tail, d_a, d_mult)` Brox & `.R`-carrying `DP2` elimination across `∀ m ≥ 2`:
private theorem all_m_parametric_da_dmult_elim_w18
    (m w a a_tail d_a d_mult : Nat)
    (hm : m ≥ 2) (hw : w ≥ 1) (ha : a ≥ 1) (hat : a_tail ≥ 1) (hda : d_a ≥ 1)
    (hd_a : d_a ∣ a) (hd_at : d_a ∣ a_tail)
    (hd_mult : d_mult ∣ (2 ^ d_a - 1)) :
    let pivots := List.replicate (m - 2) (w, a)
    let blocks := List.replicate (m - 1) (w, a) ++ [(w, a_tail)]
    let W := blockWeightSum blocks
    let K := blockStepSum blocks
    let D := 2 ^ K - 3 ^ W
    3 ^ W < 2 ^ K ->
    Nat.Coprime d_mult D ->
    multiPivotCarryUB pivots (w, a) [(w, a_tail)] < d_mult * D ->
    (¬ ∃ qs : List Nat,
        qs.length = blocks.length ∧
        ∀ j : Nat, j < blocks.length -> D * natAt qs j = broxSpiralCarry (rotBlocks j blocks)) ∧
    (∀ u0 : List MixedSRSSym, ¬ dp2AnnotatedChain u0 (dp2BlocksToShifts blocks) u0) := by
  dsimp only
  intro hlt_WK hcop_d hub_lt
  have hw17_brox := m_block_all_rotation_cyclic_brox_and_multiprime_elimination
  have hm1_succ : m - 1 = 1 + (m - 2) := by omega
  have hblk_cons : List.replicate (m - 1) (w, a) ++ [(w, a_tail)] =
      (w, a) :: (List.replicate (m - 2) (w, a) ++ [(w, a_tail)]) := by
    rw [hm1_succ, Nat.add_comm 1, List.replicate_succ, List.cons_append]
  have hrep_add : ∀ {α : Type} (c1 c2 : Nat) (x : α),
      List.replicate (c1 + c2) x = List.replicate c1 x ++ List.replicate c2 x := by
    intro α c1 c2 x; induction c1 with
    | zero => simp [List.replicate]
    | succ k' ih => rw [Nat.succ_add, List.replicate_succ, List.replicate_succ, ih, List.cons_append]
  have hsplit : List.replicate (m - 2) (w, a) ++ ((w, a) :: [(w, a_tail)]) =
      List.replicate (m - 1) (w, a) ++ [(w, a_tail)] := by
    rw [show m - 1 = (m - 2) + 1 by omega, hrep_add]
    simp [List.replicate, List.append_assoc]
  have hpos_all : ∀ b ∈ (w, a) :: (List.replicate (m - 2) (w, a) ++ [(w, a_tail)]),
      b.1 ≥ 1 ∧ b.2 ≥ 1 ∧ d_a ∣ b.2 := by
    intro b hb
    cases hb with
    | head => exact ⟨hw, ha, hd_a⟩
    | tail _ htl =>
      rcases List.mem_append.mp htl with hrep | hsing
      · rw [List.eq_of_mem_replicate hrep]; exact ⟨hw, ha, hd_a⟩
      · simp at hsing; rw [hsing]; exact ⟨hw, hat, hd_at⟩
  have hno_qs : ¬ (∃ qs : List Nat,
      qs.length = (List.replicate (m - 1) (w, a) ++ [(w, a_tail)]).length ∧
      ∀ j : Nat, j < (List.replicate (m - 1) (w, a) ++ [(w, a_tail)]).length ->
        (2 ^ blockStepSum (List.replicate (m - 1) (w, a) ++ [(w, a_tail)]) -
          3 ^ blockWeightSum (List.replicate (m - 1) (w, a) ++ [(w, a_tail)])) * natAt qs j =
          broxSpiralCarry (rotBlocks j (List.replicate (m - 1) (w, a) ++ [(w, a_tail)]))) := by
    rintro ⟨qs, hqs_len, hqs_spec⟩
    rw [hblk_cons] at hqs_len hqs_spec hlt_WK hcop_d
    have hd_gcd : d_mult ∣ natListGcd qs :=
      (hw17_brox.1.2 (w, a) (List.replicate (m - 2) (w, a) ++ [(w, a_tail)]) qs d_a d_mult
        (fun b hb => ⟨(hpos_all b hb).1, (hpos_all b hb).2.1⟩) hlt_WK hqs_len hqs_spec).2
        hda (fun b hb => (hpos_all b hb).2.2) hd_mult hcop_d
    have hrot0 : rotBlocks 0 ((w, a) :: (List.replicate (m - 2) (w, a) ++ [(w, a_tail)])) =
        List.replicate (m - 2) (w, a) ++ ((w, a) :: [(w, a_tail)]) := by
      simp only [rotBlocks, List.drop, List.take, List.append_nil, ← hblk_cons, hsplit]
    have hdD_le := hw17_brox.2.1 ((w, a) :: (List.replicate (m - 2) (w, a) ++ [(w, a_tail)])) qs 0
      (List.replicate (m - 2) (w, a)) (w, a) [(w, a_tail)] d_mult
      (fun b hb => ⟨(hpos_all b hb).1, (hpos_all b hb).2.1⟩) hlt_WK hqs_len hqs_spec (by simp) hrot0 hd_gcd
    rw [← hblk_cons] at hdD_le
    omega
  refine ⟨hno_qs, fun u0 hann => ?_⟩
  rw [hblk_cons] at hann
  rcases (leftAnchoredDP2_no_1_to_20_cycles_and_all_m_block_locks.2.2
    (w, a) (List.replicate (m - 2) (w, a) ++ [(w, a_tail)]) u0
    (fun b hb => ⟨(hpos_all b hb).1, (hpos_all b hb).2.1⟩) hann).2.2 with
    ⟨ws, qs, _, hqs_len, _, hrot_q, _, _, _, _⟩
  exact hno_qs ⟨qs, by rwa [hblk_cons], fun j hj => by
    rw [hblk_cons] at hj ⊢
    have hrj := hrot_q j hj
    cases hd_u : ws.drop j with
    | nil => rw [hd_u] at hrj; exact False.elim hrj
    | cons _ _ => rw [hd_u] at hrj; exact hrj.2.2.2.2⟩

-- Unconditional zero-side-hypothesis elimination of `[(17, 2)^(m - 1), (17, 8 * m + 2)]` across ALL `m ≥ 2`
-- (unifying Wave 14 `m = 3`, Wave 15 `m = 4`, Wave 16 `m = 5`, Wave 17 `m = 6`, Wave 18 `m = 7`, and ALL `m ≥ 8`!):
private theorem all_m_bal17_8m2_unconditional_elim_w18 (m : Nat) (hm : m ≥ 2) :
    let pivots := List.replicate (m - 2) (17, 2)
    let blocks := List.replicate (m - 1) (17, 2) ++ [(17, 8 * m + 2)]
    let W := blockWeightSum blocks
    let K := blockStepSum blocks
    let D := 2 ^ K - 3 ^ W
    W = 17 * m ∧
    K = 27 * m ∧
    3 ^ W < 2 ^ K ∧
    15 * multiPivotCarryUB pivots (17, 2) [(17, 8 * m + 2)] < 3 * D ∧
    (¬ ∃ qs : List Nat,
        qs.length = blocks.length ∧
        ∀ j : Nat, j < blocks.length -> D * natAt qs j = broxSpiralCarry (rotBlocks j blocks)) ∧
    (∀ u0 : List MixedSRSSym, ¬ dp2AnnotatedChain u0 (dp2BlocksToShifts blocks) u0) := by
  dsimp only
  rcases all_m_balanced_pivot_ub_closed_w18 m 17 2 (8 * m + 2) hm (by decide) (by decide)
    (by omega) (by decide) with ⟨_, hW_raw, hK_raw, hub_m, _⟩
  have hW_eq : blockWeightSum (List.replicate (m - 1) (17, 2) ++ [(17, 8 * m + 2)]) = 17 * m := by
    rw [hW_raw, Nat.mul_comm]
  have hK_eq : blockStepSum (List.replicate (m - 1) (17, 2) ++ [(17, 8 * m + 2)]) = 27 * m := by
    rw [hK_raw]; omega
  have hpow_le_base : ∀ (X Y k : Nat), X ≤ Y -> X ^ k ≤ Y ^ k := by
    intro X Y k hXY; induction k with
    | zero => exact Nat.le_refl 1
    | succ k' ih => rw [Nat.pow_succ X, Nat.pow_succ Y]; exact Nat.mul_le_mul ih hXY
  have hgeom_lower : ∀ (X Y k : Nat), Y ≤ X -> (X - Y) * X ^ k ≤ X ^ (k + 1) - Y ^ (k + 1) := by
    intro X Y k hYX
    rw [Nat.pow_succ X k, Nat.pow_succ Y k]
    have hm1 := Nat.mul_le_mul_right Y (hpow_le_base Y X k hYX)
    have hm2 := Nat.mul_le_mul_left (X ^ k) hYX
    have hsub : X ^ k * X - X ^ k * Y = (X - Y) * X ^ k := by
      rw [Nat.mul_comm (X ^ k) X, Nat.mul_comm (X ^ k) Y, ← Nat.sub_mul]
    rw [← hsub]
    generalize X ^ k * X = P1, X ^ k * Y = P2, Y ^ k * Y = P3 at hm1 hm2 ⊢
    omega
  have hA_pos : 2 ^ (27 * (m - 1)) ≥ 1 := nat_pow_pos_of_pos 2 (by decide) _
  have hD_ge : 5077565 * 2 ^ (27 * (m - 1)) ≤ 2 ^ (27 * m) - 3 ^ (17 * m) := by
    have hstep := hgeom_lower (2 ^ 27) (3 ^ 17) (m - 1) (by decide)
    rw [show 2 ^ 27 - 3 ^ 17 = 5077565 by decide,
        pow_pow_eq_mul_w5 2 27 (m - 1),
        pow_pow_eq_mul_w5 2 27 (m - 1 + 1),
        pow_pow_eq_mul_w5 3 17 (m - 1 + 1),
        show m - 1 + 1 = m by omega] at hstep
    exact hstep
  have hlt_WK : 3 ^ blockWeightSum (List.replicate (m - 1) (17, 2) ++ [(17, 8 * m + 2)]) <
      2 ^ blockStepSum (List.replicate (m - 1) (17, 2) ++ [(17, 8 * m + 2)]) := by
    rw [hW_eq, hK_eq]
    have hp3 : 3 ^ (17 * m) ≥ 1 := pow3_pos_nat _
    generalize 2 ^ (27 * m) = P2K, 3 ^ (17 * m) = P3W, 2 ^ (27 * (m - 1)) = AM at hD_ge hA_pos hp3 ⊢
    omega
  have ht1_le : 2 * (2 ^ 2 - 1) * 3 ^ ((m - 1) * 17) ≤ 6 * 2 ^ (27 * (m - 1)) := by
    rw [show 2 * (2 ^ 2 - 1) = 6 by decide, Nat.mul_comm (m - 1) 17,
        ← pow_pow_eq_mul_w5 3 17 (m - 1), ← pow_pow_eq_mul_w5 2 27 (m - 1)]
    exact Nat.mul_le_mul_left 6 (hpow_le_base (3 ^ 17) (2 ^ 27) (m - 1) (by decide))
  have ht2_lt : 2 ^ ((m - 2) * (17 + 2)) * 3 ^ 17 * (2 ^ (2 + (8 * m + 2)) - 1) <
      1008908 * 2 ^ (27 * (m - 1)) := by
    have hp_pos : 2 ^ (2 + (8 * m + 2)) ≥ 2 := by simpa using pow2_mono_nat (by omega : 1 ≤ 2 + (8 * m + 2))
    have h128_mul : 128 * (2 ^ ((m - 2) * (17 + 2)) * 3 ^ 17 * (2 ^ (2 + (8 * m + 2)) - 1)) <
        3 ^ 17 * (128 * 2 ^ ((m - 2) * (17 + 2)) * 2 ^ (2 + (8 * m + 2))) := by
      have hp_prod : 128 * 2 ^ ((m - 2) * (17 + 2)) * 3 ^ 17 > 0 :=
        Nat.mul_pos (Nat.mul_pos (by decide) (nat_pow_pos_of_pos 2 (by decide) _)) (by decide)
      calc 128 * (2 ^ ((m - 2) * (17 + 2)) * 3 ^ 17 * (2 ^ (2 + (8 * m + 2)) - 1))
          = (128 * 2 ^ ((m - 2) * (17 + 2)) * 3 ^ 17) * (2 ^ (2 + (8 * m + 2)) - 1) := by ac_rfl
        _ < (128 * 2 ^ ((m - 2) * (17 + 2)) * 3 ^ 17) * 2 ^ (2 + (8 * m + 2)) :=
            Nat.mul_lt_mul_of_pos_left (by omega) hp_prod
        _ = 3 ^ 17 * (128 * 2 ^ ((m - 2) * (17 + 2)) * 2 ^ (2 + (8 * m + 2))) := by ac_rfl
    have hexp_128 : 128 * 2 ^ ((m - 2) * (17 + 2)) * 2 ^ (2 + (8 * m + 2)) = 2 ^ (27 * (m - 1)) := by
      rw [show (128 : Nat) = 2 ^ 7 by decide, ← Nat.pow_add, ← Nat.pow_add]
      congr 1; omega
    rw [hexp_128] at h128_mul
    have h3_17_le : 3 ^ 17 * 2 ^ (27 * (m - 1)) ≤ (128 * 1008908) * 2 ^ (27 * (m - 1)) :=
      Nat.mul_le_mul_right _ (by decide : 3 ^ 17 ≤ 128 * 1008908)
    have h128_tot := Nat.lt_of_lt_of_le h128_mul h3_17_le
    rw [Nat.mul_assoc 128 1008908] at h128_tot
    generalize 2 ^ ((m - 2) * (17 + 2)) * 3 ^ 17 * (2 ^ (2 + (8 * m + 2)) - 1) = T2,
               1008908 * 2 ^ (27 * (m - 1)) = RHS2 at h128_tot ⊢
    omega
  have h15_lt : 15 * multiPivotCarryUB (List.replicate (m - 2) (17, 2)) (17, 2) [(17, 8 * m + 2)] <
      3 * (2 ^ blockStepSum (List.replicate (m - 1) (17, 2) ++ [(17, 8 * m + 2)]) -
        3 ^ blockWeightSum (List.replicate (m - 1) (17, 2) ++ [(17, 8 * m + 2)])) := by
    rw [hW_eq, hK_eq]
    generalize multiPivotCarryUB (List.replicate (m - 2) (17, 2)) (17, 2) [(17, 8 * m + 2)] = UB,
               2 * (2 ^ 2 - 1) * 3 ^ ((m - 1) * 17) = T1,
               2 ^ ((m - 2) * (17 + 2)) * 3 ^ 17 * (2 ^ (2 + (8 * m + 2)) - 1) = T2,
               2 ^ (27 * m) - 3 ^ (17 * m) = DG,
               2 ^ (27 * (m - 1)) = AM at hub_m ht1_le ht2_lt hD_ge hA_pos ⊢
    omega
  have hcop3 : Nat.Coprime 3
      (2 ^ blockStepSum (List.replicate (m - 1) (17, 2) ++ [(17, 8 * m + 2)]) -
        3 ^ blockWeightSum (List.replicate (m - 1) (17, 2) ++ [(17, 8 * m + 2)])) := by
    rw [hW_eq, hK_eq]
    rw [Nat.coprime_iff_gcd_eq_one]
    let DG := 2 ^ (27 * m) - 3 ^ (17 * m)
    have hg_le : Nat.gcd 3 DG ≤ 3 := Nat.le_of_dvd (by decide) (Nat.gcd_dvd_left 3 DG)
    have hg_pos : Nat.gcd 3 DG ≥ 1 := Nat.gcd_pos_of_pos_left DG (by decide)
    have hg1 := Nat.gcd_dvd_left 3 DG
    have hg2 := Nat.gcd_dvd_right 3 DG
    by_cases h1 : Nat.gcd 3 DG = 1
    · exact h1
    · exfalso
      have hg3 : Nat.gcd 3 DG = 3 := by
        rcases hg1 with ⟨q, hq⟩
        rcases (by omega : Nat.gcd 3 DG = 2 ∨ Nat.gcd 3 DG = 3) with h2 | h3
        · rw [h2] at hq; omega
        · exact h3
      rw [hg3] at hg2
      rcases hg2 with ⟨q_d, hq_d⟩
      have hp2_n3 : 2 ^ (27 * m) % 3 ≠ 0 := pow2_mod3_nonzero_w5 (27 * m)
      have hp3_m3 : 3 ^ (17 * m) % 3 = 0 := by
        rw [show 17 * m = 1 + (17 * m - 1) by omega, Nat.pow_add, Nat.pow_one]
        exact Nat.mul_mod_right 3 _
      have hsum : DG + 3 ^ (17 * m) = 2 ^ (27 * m) := by
        dsimp [DG]; have := hlt_WK; rw [hW_eq, hK_eq] at this; omega
      have hm_eq := congrArg (· % 3) hsum
      rw [hq_d, Nat.add_mod, Nat.mul_mod_right, hp3_m3] at hm_eq
      exact hp2_n3 hm_eq.symm
  rcases all_m_parametric_da_dmult_elim_w18 m 17 2 (8 * m + 2) 2 3
    hm (by decide) (by decide) (by omega) (by decide)
    (by decide) ⟨4 * m + 1, by omega⟩ (by decide)
    hlt_WK hcop3 (by omega) with ⟨hno_qs, hno_dp2⟩
  exact ⟨hW_eq, hK_eq, hlt_WK, h15_lt, hno_qs, hno_dp2⟩

-- Parametric `d_a = 3, d_mult = 7` infinite-`m` family `[(11, 3)^(m - 1), (11, 6 * m + 3)]` (`m ≥ 2, m % 6 ≠ 0`):
private theorem all_m_bal11_3_6m3_dmult7_elim_w18 (m : Nat) (hm : m ≥ 2) (hm6 : m % 6 ≠ 0) :
    let pivots := List.replicate (m - 2) (11, 3)
    let blocks := List.replicate (m - 1) (11, 3) ++ [(11, 6 * m + 3)]
    let W := blockWeightSum blocks
    let K := blockStepSum blocks
    let D := 2 ^ K - 3 ^ W
    W = 11 * m ∧
    K = 20 * m ∧
    Nat.Coprime 7 D ∧
    multiPivotCarryUB pivots (11, 3) [(11, 6 * m + 3)] < 7 * D ∧
    (¬ ∃ qs : List Nat,
        qs.length = blocks.length ∧
        ∀ j : Nat, j < blocks.length -> D * natAt qs j = broxSpiralCarry (rotBlocks j blocks)) ∧
    (∀ u0 : List MixedSRSSym, ¬ dp2AnnotatedChain u0 (dp2BlocksToShifts blocks) u0) := by
  dsimp only
  rcases all_m_balanced_pivot_ub_closed_w18 m 11 3 (6 * m + 3) hm (by decide) (by decide)
    (by omega) (by decide) with ⟨_, hW_raw, hK_raw, _, hub_lt_3D⟩
  have hW_eq : blockWeightSum (List.replicate (m - 1) (11, 3) ++ [(11, 6 * m + 3)]) = 11 * m := by
    rw [hW_raw, Nat.mul_comm]
  have hK_eq : blockStepSum (List.replicate (m - 1) (11, 3) ++ [(11, 6 * m + 3)]) = 20 * m := by
    rw [hK_raw]; omega
  have h2_3W : 2 * 3 ^ blockWeightSum (List.replicate (m - 1) (11, 3) ++ [(11, 6 * m + 3)]) ≤
      2 ^ blockStepSum (List.replicate (m - 1) (11, 3) ++ [(11, 6 * m + 3)]) := by
    rw [hW_eq, hK_eq, ← pow_pow_eq_mul_w5 3 11 m]
    have hp_19 : ∀ k : Nat, (3 ^ 11) ^ k ≤ (2 ^ 19) ^ k := by
      intro k; induction k with
      | zero => decide
      | succ k' ih =>
        rw [Nat.pow_succ (3 ^ 11), Nat.pow_succ (2 ^ 19)]
        exact Nat.mul_le_mul ih (by decide : 3 ^ 11 ≤ 2 ^ 19)
    have h1 := Nat.mul_le_mul_left 2 (hp_19 m)
    rw [pow_pow_eq_mul_w5 2 19 m, ← Nat.pow_succ'] at h1
    exact Nat.le_trans h1 (pow2_mono_nat (by omega : (19 * m).succ ≤ 20 * m))
  have hlt_WK : 3 ^ blockWeightSum (List.replicate (m - 1) (11, 3) ++ [(11, 6 * m + 3)]) <
      2 ^ blockStepSum (List.replicate (m - 1) (11, 3) ++ [(11, 6 * m + 3)]) := by
    have hp3 : 3 ^ blockWeightSum (List.replicate (m - 1) (11, 3) ++ [(11, 6 * m + 3)]) ≥ 1 := pow3_pos_nat _
    omega
  have hlt_3D := hub_lt_3D h2_3W
  have hD_pos : 2 ^ blockStepSum (List.replicate (m - 1) (11, 3) ++ [(11, 6 * m + 3)]) -
      3 ^ blockWeightSum (List.replicate (m - 1) (11, 3) ++ [(11, 6 * m + 3)]) ≥ 1 := by omega
  have hlt_7D : multiPivotCarryUB (List.replicate (m - 2) (11, 3)) (11, 3) [(11, 6 * m + 3)] <
      7 * (2 ^ blockStepSum (List.replicate (m - 1) (11, 3) ++ [(11, 6 * m + 3)]) -
        3 ^ blockWeightSum (List.replicate (m - 1) (11, 3) ++ [(11, 6 * m + 3)])) := by
    generalize 2 ^ blockStepSum (List.replicate (m - 1) (11, 3) ++ [(11, 6 * m + 3)]) -
      3 ^ blockWeightSum (List.replicate (m - 1) (11, 3) ++ [(11, 6 * m + 3)]) = DG at hlt_3D hD_pos ⊢
    omega
  have hp6_mod7 : ∀ (b c : Nat), b ^ 6 % 7 = 1 -> b ^ (6 * c) % 7 = 1 := by
    intro b c hb6; induction c with
    | zero => rfl
    | succ c' ih => rw [Nat.mul_succ, Nat.pow_add, Nat.mul_mod, ih, hb6]
  have hcop7 : Nat.Coprime 7
      (2 ^ blockStepSum (List.replicate (m - 1) (11, 3) ++ [(11, 6 * m + 3)]) -
        3 ^ blockWeightSum (List.replicate (m - 1) (11, 3) ++ [(11, 6 * m + 3)])) := by
    rw [hW_eq, hK_eq, Nat.coprime_iff_gcd_eq_one]
    let DG := 2 ^ (20 * m) - 3 ^ (11 * m)
    have hg_le : Nat.gcd 7 DG ≤ 7 := Nat.le_of_dvd (by decide) (Nat.gcd_dvd_left 7 DG)
    have hg_pos : Nat.gcd 7 DG ≥ 1 := Nat.gcd_pos_of_pos_left DG (by decide)
    have hg1 := Nat.gcd_dvd_left 7 DG
    have hg2 := Nat.gcd_dvd_right 7 DG
    by_cases h1 : Nat.gcd 7 DG = 1
    · exact h1
    · exfalso
      have hg7 : Nat.gcd 7 DG = 7 := by
        rcases hg1 with ⟨q, hq⟩
        rcases (by omega : Nat.gcd 7 DG = 2 ∨ Nat.gcd 7 DG = 3 ∨ Nat.gcd 7 DG = 4 ∨
            Nat.gcd 7 DG = 5 ∨ Nat.gcd 7 DG = 6 ∨ Nat.gcd 7 DG = 7) with h | h | h | h | h | h <;>
          (try rw [h] at hq; omega)
      rw [hg7] at hg2
      rcases hg2 with ⟨q_d, hq_d⟩
      let q6 := m / 6
      let r6 := m % 6
      have hm_div : m = 6 * q6 + r6 := (Nat.div_add_mod m 6).symm
      have hp2_r : 2 ^ (20 * m) % 7 = 2 ^ (20 * r6) % 7 := by
        rw [hm_div, Nat.mul_add, show 20 * (6 * q6) = 6 * (20 * q6) by ac_rfl,
            Nat.pow_add, Nat.mul_mod, hp6_mod7 2 (20 * q6) (by decide), Nat.one_mul, Nat.mod_mod]
      have hp3_r : 3 ^ (11 * m) % 7 = 3 ^ (11 * r6) % 7 := by
        rw [hm_div, Nat.mul_add, show 11 * (6 * q6) = 6 * (11 * q6) by ac_rfl,
            Nat.pow_add, Nat.mul_mod, hp6_mod7 3 (11 * q6) (by decide), Nat.one_mul, Nat.mod_mod]
      have hsum : DG + 3 ^ (11 * m) = 2 ^ (20 * m) := by
        dsimp [DG]; have := hlt_WK; rw [hW_eq, hK_eq] at this; omega
      have hm_eq := congrArg (· % 7) hsum
      rw [hq_d, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod, hp3_r, hp2_r] at hm_eq
      have hr6_lt : r6 < 6 := Nat.mod_lt m (by decide)
      have hr6_ne0 : r6 ≠ 0 := hm6
      rcases (by omega : r6 = 1 ∨ r6 = 2 ∨ r6 = 3 ∨ r6 = 4 ∨ r6 = 5) with hr | hr | hr | hr | hr <;>
        (rw [hr] at hm_eq; exact absurd hm_eq (by decide))
  rcases all_m_parametric_da_dmult_elim_w18 m 11 3 (6 * m + 3) 3 7
    hm (by decide) (by decide) (by omega) (by decide)
    (by decide) ⟨2 * m + 1, by omega⟩ (by decide)
    hlt_WK hcop7 hlt_7D with ⟨hno_qs, hno_dp2⟩
  exact ⟨hW_eq, hK_eq, hcop7, hlt_7D, hno_qs, hno_dp2⟩

/--
  Theorem W18.1c (`leftAnchoredDP2_no_1_to_25_cycles_and_infinite_m_block_exclusions`,
  `zero custom axioms`):
  Unconditional `1..25`-Cycle Freedom Across ALL `DP2` Words (`N_cut = 147`), `M1`
  `31376865305 / 2978678759` `(r = 22, A = 35)` Carry Separation, `W ≥ 26` Floor on `.R`-Carrying
  `m`-Block `DP2` Cycles, & Infinite Parametric `m`-Block (`∀ m ≥ 2`) `.R`-Carrying `DP2` Cycle
  Exclusion Ruling Out `(m, w, a, a_tail, d_a, d_mult)` Families, Unconditional All-`m ≥ 2`
  `[(17, 2)^(m - 1), (17, 8 * m + 2)]`, & `d_a = 3, d_mult = 7` `[(11, 3)^(m - 1), (11, 6 * m + 3)]`
  (`Branch P4.3`, witness `M1_DP2_22CYCLE_31376865305_OVER_2978678759`, `W18_H1`).
-/
theorem leftAnchoredDP2_no_1_to_25_cycles_and_infinite_m_block_exclusions :
    ((∀ (r : Nat) (u : List MixedSRSSym),
        1 ≤ r -> r ≤ 25 -> ¬ dp2StepIter r u u) ∧
     (dp2IterCarry (List.replicate 21 1 ++ [14]) = 31376865305 ∧
      2 ^ 35 - 3 ^ 22 = 2978678759 ∧
      31376865305 % 2978678759 = 1590077715)) ∧
    (∀ (b0 : Nat × Nat) (rest : List (Nat × Nat)) (u0 : List MixedSRSSym),
      let blocks := b0 :: rest
      (∀ b ∈ blocks, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      dp2AnnotatedChain u0 (dp2BlocksToShifts blocks) u0 ->
      blockWeightSum blocks ≥ 26) ∧
    (∀ (m w a a_tail d_a d_mult : Nat) (u0 : List MixedSRSSym),
      let pivots := List.replicate (m - 2) (w, a)
      let blocks := List.replicate (m - 1) (w, a) ++ [(w, a_tail)]
      let W := blockWeightSum blocks
      let K := blockStepSum blocks
      let D := 2 ^ K - 3 ^ W
      m ≥ 2 -> w ≥ 1 -> a ≥ 1 -> a_tail ≥ 1 -> d_a ≥ 1 ->
      d_a ∣ a -> d_a ∣ a_tail ->
      d_mult ∣ (2 ^ d_a - 1) ->
      3 ^ W < 2 ^ K ->
      Nat.Coprime d_mult D ->
      multiPivotCarryUB pivots (w, a) [(w, a_tail)] < d_mult * D ->
      ¬ dp2AnnotatedChain u0 (dp2BlocksToShifts blocks) u0) ∧
    ((∀ (m : Nat) (u0 : List MixedSRSSym),
        m ≥ 2 ->
        ¬ dp2AnnotatedChain u0
            (dp2BlocksToShifts (List.replicate (m - 1) (17, 2) ++ [(17, 8 * m + 2)])) u0) ∧
     (∀ (m : Nat) (u0 : List MixedSRSSym),
        m ≥ 2 -> m % 6 ≠ 0 ->
        ¬ dp2AnnotatedChain u0
            (dp2BlocksToShifts (List.replicate (m - 1) (11, 3) ++ [(11, 6 * m + 3)])) u0) ∧
     (∀ (m a_tail : Nat) (u0 : List MixedSRSSym),
        let blocks := List.replicate (m - 1) (17, 2) ++ [(17, a_tail)]
        m ≥ 2 -> a_tail ≥ 2 -> 2 ∣ a_tail ->
        2 * 3 ^ (17 * m) ≤ 2 ^ (19 * (m - 1) + (17 + a_tail)) ->
        ¬ dp2AnnotatedChain u0 (dp2BlocksToShifts blocks) u0)) := by
  have hno_1_20 := leftAnchoredDP2_no_1_to_20_cycles_and_all_m_block_locks.1.1
  have hno_1_25 : ∀ (r : Nat) (u : List MixedSRSSym),
      1 ≤ r -> r ≤ 25 -> ¬ dp2StepIter r u u := by
    intro r u hr1 hr25 hiter
    by_cases hr20 : r ≤ 20
    · exact hno_1_20 r u hr1 hr20 hiter
    · rcases (leftAnchoredDP2_iterated_affine_carry_and_cycle_laws.1 r u u hiter).2 with
        ⟨shifts, hlen, _, hann, _, _⟩
      rcases leftAnchoredDP2_iterated_affine_carry_and_cycle_laws.2.1.1 shifts u (by omega) hann with
        ⟨hlt, _, _, _⟩
      rw [hlen] at hlt
      rcases dp2AnnotatedChain_syr_and_ge147_bound_w18 shifts u u hann with ⟨_, hsmall | hge147⟩
      · rcases hsmall with ⟨n, hn3, hn145, hno, i, hi_le, hi_eq, hur_eq⟩
        rw [hlen] at hi_le hur_eq
        have hcyc_n : syrIterW18 r n = n := by
          rw [show r = (r - i) + i by omega, syrIterW18_add (r - i) i n, ← hur_eq, hi_eq]
        let k := (n - 3) / 2
        have hk_lt : k < 72 := by dsimp [k]; omega
        have hn_eq : n = 2 * k + 3 := by dsimp [k]; omega
        rw [hn_eq] at hcyc_n
        exact no_small_odd_syr_cycles_21_to_25_w18 ⟨r, by omega⟩ ⟨k, hk_lt⟩ (by dsimp; omega) hcyc_n
      · rw [hlen] at hge147
        have hNu_pos : dp2GlobalOddVal u > 0 := by unfold dp2GlobalOddVal; omega
        have h147_le : 147 ^ r * 2 ^ dp2ShiftSum shifts ≤ 442 ^ r :=
          nat_mul_le_cancel_right_w5 (dp2GlobalOddVal u) _ _ hNu_pos hge147
        let A := dp2ShiftSum shifts
        change 3 ^ r < 2 ^ A at hlt
        change 147 ^ r * 2 ^ A ≤ 442 ^ r at h147_le
        rcases (by omega : r = 21 ∨ r = 22 ∨ r = 23 ∨ r = 24 ∨ r = 25) with
          rfl | rfl | rfl | rfl | rfl
        · by_cases hA : A ≤ 33
          · exact absurd (Nat.lt_of_lt_of_le hlt (nat_pow_mono_exp_pos 2 A 33 (by decide) hA)) (by decide)
          · have hp := Nat.mul_le_mul_left (147 ^ 21) (nat_pow_mono_exp_pos 2 34 A (by decide) (by omega))
            exact absurd (Nat.le_trans hp h147_le) (by decide)
        · by_cases hA : A ≤ 34
          · exact absurd (Nat.lt_of_lt_of_le hlt (nat_pow_mono_exp_pos 2 A 34 (by decide) hA)) (by decide)
          · have hp := Nat.mul_le_mul_left (147 ^ 22) (nat_pow_mono_exp_pos 2 35 A (by decide) (by omega))
            exact absurd (Nat.le_trans hp h147_le) (by decide)
        · by_cases hA : A ≤ 36
          · exact absurd (Nat.lt_of_lt_of_le hlt (nat_pow_mono_exp_pos 2 A 36 (by decide) hA)) (by decide)
          · have hp := Nat.mul_le_mul_left (147 ^ 23) (nat_pow_mono_exp_pos 2 37 A (by decide) (by omega))
            exact absurd (Nat.le_trans hp h147_le) (by decide)
        · by_cases hA : A ≤ 38
          · exact absurd (Nat.lt_of_lt_of_le hlt (nat_pow_mono_exp_pos 2 A 38 (by decide) hA)) (by decide)
          · have hp := Nat.mul_le_mul_left (147 ^ 24) (nat_pow_mono_exp_pos 2 39 A (by decide) (by omega))
            exact absurd (Nat.le_trans hp h147_le) (by decide)
        · by_cases hA : A ≤ 39
          · exact absurd (Nat.lt_of_lt_of_le hlt (nat_pow_mono_exp_pos 2 A 39 (by decide) hA)) (by decide)
          · have hp := Nat.mul_le_mul_left (147 ^ 25) (nat_pow_mono_exp_pos 2 40 A (by decide) (by omega))
            exact absurd (Nat.le_trans hp h147_le) (by decide)
  have hann_to_iter : ∀ (sh : List Nat) (x y : List MixedSRSSym),
      dp2AnnotatedChain x sh y -> dp2StepIter sh.length x y := by
    intro sh; induction sh with
    | nil => intro x y h0; exact h0
    | cons s stl ih => intro x y ⟨_, z, hst, _, htl⟩; exact ⟨z, hst, ih z y htl⟩
  have hfloor26 : ∀ (b0 : Nat × Nat) (rest : List (Nat × Nat)) (u0 : List MixedSRSSym),
      (∀ b ∈ b0 :: rest, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      dp2AnnotatedChain u0 (dp2BlocksToShifts (b0 :: rest)) u0 ->
      blockWeightSum (b0 :: rest) ≥ 26 := by
    intro b0 rest u0 hpos hann
    by_cases hle25 : blockWeightSum (b0 :: rest) ≤ 25
    · exfalso
      have hlen := (leftAnchoredDP2_no_1_to_20_cycles_and_all_m_block_locks.2.1 b0 rest hpos).1
      have hit := hann_to_iter (dp2BlocksToShifts (b0 :: rest)) u0 u0 hann
      rw [hlen] at hit
      have hge1 : blockWeightSum (b0 :: rest) ≥ 1 := by
        have := (hpos b0 (List.Mem.head _)).1; simp [blockWeightSum]; omega
      exact hno_1_25 (blockWeightSum (b0 :: rest)) u0 hge1 hle25 hit
    · omega
  have hparam_dp2 : ∀ (m w a a_tail d_a d_mult : Nat) (u0 : List MixedSRSSym),
      let pivots := List.replicate (m - 2) (w, a)
      let blocks := List.replicate (m - 1) (w, a) ++ [(w, a_tail)]
      let W := blockWeightSum blocks
      let K := blockStepSum blocks
      let D := 2 ^ K - 3 ^ W
      m ≥ 2 -> w ≥ 1 -> a ≥ 1 -> a_tail ≥ 1 -> d_a ≥ 1 ->
      d_a ∣ a -> d_a ∣ a_tail ->
      d_mult ∣ (2 ^ d_a - 1) ->
      3 ^ W < 2 ^ K ->
      Nat.Coprime d_mult D ->
      multiPivotCarryUB pivots (w, a) [(w, a_tail)] < d_mult * D ->
      ¬ dp2AnnotatedChain u0 (dp2BlocksToShifts blocks) u0 := by
    intro m w a a_tail d_a d_mult u0; dsimp only
    intro hm hw ha hat hda hd_a hd_at hd_m hlt hcop hub
    exact (all_m_parametric_da_dmult_elim_w18 m w a a_tail d_a d_mult
      hm hw ha hat hda hd_a hd_at hd_m hlt hcop hub).2 u0
  refine ⟨⟨hno_1_25, by decide⟩, hfloor26, hparam_dp2,
          ⟨fun m u0 hm => (all_m_bal17_8m2_unconditional_elim_w18 m hm).2.2.2.2.2 u0,
           fun m u0 hm hm6 => (all_m_bal11_3_6m3_dmult7_elim_w18 m hm hm6).2.2.2.2.2 u0,
           ?_⟩⟩
  intro m a_tail u0; dsimp only
  intro hm hat hat_ev h2_3W hann
  rcases all_m_balanced_pivot_ub_closed_w18 m 17 2 a_tail hm (by decide) (by decide)
    (by omega) (by decide) with ⟨_, hW17, hK17, _, hub_lt_3D⟩
  have hW_eq : blockWeightSum (List.replicate (m - 1) (17, 2) ++ [(17, a_tail)]) = 17 * m := by
    rw [hW17, Nat.mul_comm]
  have hK_eq : blockStepSum (List.replicate (m - 1) (17, 2) ++ [(17, a_tail)]) =
      19 * (m - 1) + (17 + a_tail) := by
    rw [hK17, show 17 + 2 = 19 from rfl, Nat.mul_comm (m - 1) 19]
  have h2_3W_blk : 2 * 3 ^ blockWeightSum (List.replicate (m - 1) (17, 2) ++ [(17, a_tail)]) ≤
      2 ^ blockStepSum (List.replicate (m - 1) (17, 2) ++ [(17, a_tail)]) := by
    rwa [hW_eq, hK_eq]
  have hlt_WK : 3 ^ blockWeightSum (List.replicate (m - 1) (17, 2) ++ [(17, a_tail)]) <
      2 ^ blockStepSum (List.replicate (m - 1) (17, 2) ++ [(17, a_tail)]) := by
    have hp3 := pow3_pos_nat (blockWeightSum (List.replicate (m - 1) (17, 2) ++ [(17, a_tail)]))
    omega
  have hm1_succ : m - 1 = 1 + (m - 2) := by omega
  have hblk_cons : List.replicate (m - 1) (17, 2) ++ [(17, a_tail)] =
      (17, 2) :: (List.replicate (m - 2) (17, 2) ++ [(17, a_tail)]) := by
    rw [hm1_succ, Nat.add_comm 1, List.replicate_succ, List.cons_append]
  have hpos_all : ∀ b ∈ (17, 2) :: (List.replicate (m - 2) (17, 2) ++ [(17, a_tail)]),
      b.1 ≥ 1 ∧ b.2 ≥ 1 := by
    intro b hb
    cases hb with
    | head => decide
    | tail _ htl =>
      rcases List.mem_append.mp htl with hrep | hsing
      · rw [List.eq_of_mem_replicate hrep]; decide
      · simp at hsing; rw [hsing]; dsimp only; exact ⟨by decide, by omega⟩
  rw [hblk_cons] at hann
  rcases (leftAnchoredDP2_no_1_to_20_cycles_and_all_m_block_locks.2.2
    (17, 2) (List.replicate (m - 2) (17, 2) ++ [(17, a_tail)]) u0 hpos_all hann).2.2 with
    ⟨ws, qs, _, hqs_len, _, hrot_q, _, hcasc, _, _⟩
  rw [← hblk_cons] at hcasc
  let D_cur := 2 ^ blockStepSum (List.replicate (m - 1) (17, 2) ++ [(17, a_tail)]) -
      3 ^ blockWeightSum (List.replicate (m - 1) (17, 2) ++ [(17, a_tail)])
  have hcop3_D : Nat.Coprime 3 D_cur := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hg_le : Nat.gcd 3 D_cur ≤ 3 := Nat.le_of_dvd (by decide) (Nat.gcd_dvd_left 3 D_cur)
    have hg_pos : Nat.gcd 3 D_cur ≥ 1 := Nat.gcd_pos_of_pos_left D_cur (by decide)
    have hg1 := Nat.gcd_dvd_left 3 D_cur
    have hg2 := Nat.gcd_dvd_right 3 D_cur
    by_cases h1 : Nat.gcd 3 D_cur = 1
    · exact h1
    · exfalso
      rcases hg1 with ⟨q, hq⟩
      have hg3 : Nat.gcd 3 D_cur = 3 := by
        rcases (by omega : Nat.gcd 3 D_cur = 2 ∨ Nat.gcd 3 D_cur = 3) with h2 | h3
        · rw [h2] at hq; omega
        · exact h3
      rw [hg3] at hg2
      exact hcasc.1 hg2
  exact hparam_dp2 m 17 2 a_tail 2 3 u0 hm (by decide) (by decide) (by omega) (by decide)
    (by decide) hat_ev (by decide) hlt_WK hcop3_D (hub_lt_3D h2_3W_blk)
    (by rwa [hblk_cons])


-- ============================================================================

-- Section 2C: Universal Symbolic All-`m` (`∀ m ≥ 2`) `(m - 1)`-Pivot Closed-Form
--             Brox Squeeze & `m = 7` Balanced + Convergent `(41, 65)` Eliminations
--             (`W18_H2`, Branch P3.4)
-- ----------------------------------------------------------------------------

private def blocksBal7W18 : List (Nat × Nat) :=
  [(17, 2), (17, 2), (17, 2), (17, 2), (17, 2), (17, 2), (17, 58)]

private def blocksMp7W18 : List (Nat × Nat) :=
  [(6, 3), (6, 3), (6, 6), (6, 3), (6, 3), (6, 3), (5, 3)]

set_option exponentiation.threshold 2048 in
private theorem bal7_rot5_escape_cert_w18 :
    [0, 1, 2, 3, 4, 5, 6].all (fun j =>
      match rotBlocks j blocksBal7W18 with
      | b0 :: b1 :: b2 :: b3 :: b4 :: rest =>
        decide (multiPivotCarryUB [b0, b1, b2, b3] b4 rest >
          3 * (2 ^ blockStepSum blocksBal7W18 - 3 ^ blockWeightSum blocksBal7W18))
      | _ => false) = true := by decide

set_option exponentiation.threshold 2048 in
private theorem bal7_6pivot_94x_cert_w18 :
    94 * multiPivotCarryUB [(17, 2), (17, 2), (17, 2), (17, 2), (17, 2)] (17, 2) [(17, 58)] <
      3 * (2 ^ blockStepSum blocksBal7W18 - 3 ^ blockWeightSum blocksBal7W18) ∧
    multiPivotCarryUB [(17, 2), (17, 2), (17, 2), (17, 2), (17, 2)] (17, 2) [(17, 58)] ≥ 1 := by decide

set_option exponentiation.threshold 2048 in
private theorem mp7_hensel_and_rot6_certs_w18 :
    Nat.Coprime 7 (2 ^ blockStepSum blocksMp7W18 - 3 ^ blockWeightSum blocksMp7W18) ∧
    ([0, 1, 2, 3, 4, 5, 6].all (fun j =>
      match rotBlocks j blocksMp7W18 with
      | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: rest =>
        decide (multiPivotCarryUB [b0, b1, b2, b3, b4] b5 rest >
          7 * (2 ^ blockStepSum blocksMp7W18 - 3 ^ blockWeightSum blocksMp7W18))
      | _ => false) = true) ∧
    henselOddInvModPow2 6 (3 ^ 6 * 7) * 7 = 105 ∧
    2 * multiPivotCarryUB [(6, 6), (6, 3), (6, 3), (6, 3), (5, 3)] (6, 3) [(6, 3)] <
      105 * (2 ^ blockStepSum blocksMp7W18 - 3 ^ blockWeightSum blocksMp7W18) ∧
    multiPivotCarryUB [(6, 6), (6, 3), (6, 3), (6, 3), (5, 3)] (6, 3) [(6, 3)] ≥ 1 := by decide

/--
  Theorem W18.2c (`m_block_all_m_parametric_pivot_brox_and_7block_elimination`,
  `zero custom axioms`):
  Universal Symbolic All-`m` (`∀ m ≥ 2`) Parametric `(m - 1)`-Pivot Closed-Form Geometric Identity,
  General `(m, w, a, a_tail, d_a, d_mult)` Brox & `DP2` Elimination, Unconditional All-`m ≥ 2`
  `[(17, 2)^(m - 1), (17, 8 * m + 2)]` (`> 15×`) & `d_a = 3` `[(11, 3)^(m - 1), (11, 6 * m + 3)]`
  Infinite-Family Eliminations, + Concrete `m = 7` Balanced (`> 94×`) & Convergent `(W = 41, K = 65)`
  `s = 6` Hensel (`105 * D`, `> 2×`) Eliminations:
  1. Exact geometric `(m - 1)`-pivot identity across ALL `m ≥ 2` when `2^(w + a) ≤ 3^w`:
     `(3^w - 2^(w + a)) * multiPivotCarryUB (replicate (m - 2) (w, a)) (w, a) [(w, a_tail)] = (3^((m - 2) * w) - 2^((m - 2) * (w + a))) * 3^(2 * w) * (2^a - 1) + (3^w - 2^(w + a)) * 2^((m - 2) * (w + a)) * 3^w * (2^(a + a_tail) - 1)`;
  2. Universal closed-form upper bound when `2 * 2^(w + a) ≤ 3^w` AND general parametric
     `(m, w, a, a_tail, d_a, d_mult)` Brox & `DP2` elimination across **ALL `m ≥ 2`**, instantiated
     unconditionally (zero side hypotheses!) to rule out **`[(17, 2)^(m - 1), (17, 8 * m + 2)]` across ALL `m ≥ 2`**
     (`15 * UB < 3 * D`) and **`[(11, 3)^(m - 1), (11, 6 * m + 3)]` (`d_a = 3, d_mult = 7`) across ALL `m ≥ 2, m % 6 ≠ 0`**;
  3. Concrete `m = 7` `[(17, 2)^6, (17, 58)]` escapes all `7` five-pivot rotations (`> 3 * D`) yet is
     crushed **`> 94×`** by 6-pivot telescoping (`94 * UB_6 < 3 * D`);
  4. Convergent `(W = 41, K = 65)` `m = 7` `[(6, 3), (6, 3), (6, 6), (6, 3)^3, (5, 3)]` escapes all `7`
     non-Hensel 6-pivot rotations (`> 7 * D`) yet is crushed **`> 2×`** at rotation `j = 2` via
     `henselOddInvModPow2 6 (3^6 * 7) * 7 = 105` (`Branch P3.4`, witness
     `M1_BALANCED_7BLOCK_FIVE_PIVOT_ESCAPE`, `W18_H2`).
-/
theorem m_block_all_m_parametric_pivot_brox_and_7block_elimination :
    ((∀ (m w a a_tail : Nat), m ≥ 2 -> 2 ^ (w + a) ≤ 3 ^ w ->
        (3 ^ w - 2 ^ (w + a)) *
            multiPivotCarryUB (List.replicate (m - 2) (w, a)) (w, a) [(w, a_tail)] =
          (3 ^ ((m - 2) * w) - 2 ^ ((m - 2) * (w + a))) * 3 ^ (2 * w) * (2 ^ a - 1) +
            (3 ^ w - 2 ^ (w + a)) * 2 ^ ((m - 2) * (w + a)) * 3 ^ w * (2 ^ (a + a_tail) - 1)) ∧
     (∀ (m w a a_tail : Nat), m ≥ 2 -> w ≥ 1 -> a ≥ 1 -> a_tail ≥ 1 ->
        2 * 2 ^ (w + a) ≤ 3 ^ w ->
        let pivots := List.replicate (m - 2) (w, a)
        let blocks := List.replicate (m - 1) (w, a) ++ [(w, a_tail)]
        let W := blockWeightSum blocks
        let K := blockStepSum blocks
        let D := 2 ^ K - 3 ^ W
        multiPivotCarryUB pivots (w, a) [(w, a_tail)] ≤
          2 * (2 ^ a - 1) * 3 ^ ((m - 1) * w) +
            2 ^ ((m - 2) * (w + a)) * 3 ^ w * (2 ^ (a + a_tail) - 1) ∧
        (∀ (d_a d_mult : Nat), d_a ≥ 1 -> d_a ∣ a -> d_a ∣ a_tail ->
          d_mult ∣ (2 ^ d_a - 1) -> 3 ^ W < 2 ^ K -> Nat.Coprime d_mult D ->
          2 * (2 ^ a - 1) * 3 ^ ((m - 1) * w) +
              2 ^ ((m - 2) * (w + a)) * 3 ^ w * (2 ^ (a + a_tail) - 1) < d_mult * D ->
          (¬ ∃ qs : List Nat,
              qs.length = blocks.length ∧
              ∀ j : Nat, j < blocks.length -> D * natAt qs j = broxSpiralCarry (rotBlocks j blocks)) ∧
          (∀ u0 : List MixedSRSSym, ¬ dp2AnnotatedChain u0 (dp2BlocksToShifts blocks) u0)) ∧
        (2 ∣ a -> 2 ∣ a_tail -> 2 * 3 ^ W ≤ 2 ^ K ->
          multiPivotCarryUB pivots (w, a) [(w, a_tail)] < 3 * D ∧
          ¬ (∃ qs : List Nat,
            qs.length = blocks.length ∧
            ∀ j : Nat, j < blocks.length -> D * natAt qs j = broxSpiralCarry (rotBlocks j blocks)))) ∧
     (∀ m : Nat, m ≥ 2 ->
        let pivots := List.replicate (m - 2) (17, 2)
        let blocks := List.replicate (m - 1) (17, 2) ++ [(17, 8 * m + 2)]
        let D := 2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks
        3 ^ blockWeightSum blocks < 2 ^ blockStepSum blocks ∧
        15 * multiPivotCarryUB pivots (17, 2) [(17, 8 * m + 2)] < 3 * D ∧
        (¬ ∃ qs : List Nat,
            qs.length = blocks.length ∧
            ∀ j : Nat, j < blocks.length -> D * natAt qs j = broxSpiralCarry (rotBlocks j blocks)) ∧
        (∀ u0 : List MixedSRSSym, ¬ dp2AnnotatedChain u0 (dp2BlocksToShifts blocks) u0)) ∧
     (∀ m : Nat, m ≥ 2 -> m % 6 ≠ 0 ->
        let pivots := List.replicate (m - 2) (11, 3)
        let blocks := List.replicate (m - 1) (11, 3) ++ [(11, 6 * m + 3)]
        let D := 2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks
        Nat.Coprime 7 D ∧
        multiPivotCarryUB pivots (11, 3) [(11, 6 * m + 3)] < 7 * D ∧
        (¬ ∃ qs : List Nat,
            qs.length = blocks.length ∧
            ∀ j : Nat, j < blocks.length -> D * natAt qs j = broxSpiralCarry (rotBlocks j blocks)) ∧
        (∀ u0 : List MixedSRSSym, ¬ dp2AnnotatedChain u0 (dp2BlocksToShifts blocks) u0))) ∧
    (let blocks_bal7 : List (Nat × Nat) := [(17, 2), (17, 2), (17, 2), (17, 2), (17, 2), (17, 2), (17, 58)]
     let D_bal7 := 2 ^ blockStepSum blocks_bal7 - 3 ^ blockWeightSum blocks_bal7
     let blocks_mp7 : List (Nat × Nat) := [(6, 3), (6, 3), (6, 6), (6, 3), (6, 3), (6, 3), (5, 3)]
     let D_mp7 := 2 ^ blockStepSum blocks_mp7 - 3 ^ blockWeightSum blocks_mp7
     (∀ j : Nat, j < 7 ->
       match rotBlocks j blocks_bal7 with
       | b0 :: b1 :: b2 :: b3 :: b4 :: rest => multiPivotCarryUB [b0, b1, b2, b3] b4 rest > 3 * D_bal7
       | _ => False) ∧
     94 * multiPivotCarryUB [(17, 2), (17, 2), (17, 2), (17, 2), (17, 2)] (17, 2) [(17, 58)] < 3 * D_bal7 ∧
     ¬ (∃ qs : List Nat,
       qs.length = 7 ∧
       ∀ j : Nat, j < 7 -> D_bal7 * natAt qs j = broxSpiralCarry (rotBlocks j blocks_bal7)) ∧
     ¬ (∃ u0 : List MixedSRSSym, dp2AnnotatedChain u0 (dp2BlocksToShifts blocks_bal7) u0) ∧
     Nat.Coprime 7 D_mp7 ∧
     (∀ j : Nat, j < 7 ->
       match rotBlocks j blocks_mp7 with
       | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: rest => multiPivotCarryUB [b0, b1, b2, b3, b4] b5 rest > 7 * D_mp7
       | _ => False) ∧
     henselOddInvModPow2 6 (3 ^ 6 * 7) * 7 = 105 ∧
     2 * multiPivotCarryUB [(6, 6), (6, 3), (6, 3), (6, 3), (5, 3)] (6, 3) [(6, 3)] < 105 * D_mp7 ∧
     ¬ (∃ qs : List Nat,
       qs.length = 7 ∧
       ∀ j : Nat, j < 7 -> D_mp7 * natAt qs j = broxSpiralCarry (rotBlocks j blocks_mp7)) ∧
     ¬ (∃ u0 : List MixedSRSSym, dp2AnnotatedChain u0 (dp2BlocksToShifts blocks_mp7) u0)) := by
  have hw17_brox := m_block_all_rotation_cyclic_brox_and_multiprime_elimination
  refine ⟨⟨all_m_balanced_pivot_exact_geom_w18, ?_,
           fun m hm => (all_m_bal17_8m2_unconditional_elim_w18 m hm).2.2,
           fun m hm hm6 => (all_m_bal11_3_6m3_dmult7_elim_w18 m hm hm6).2.2⟩, ?_⟩
  · -- Part 1: Universal symbolic all-`m` (`∀ m ≥ 2`) `(m - 1)`-pivot closed-form & parametric `(d_a, d_mult)` squeeze:
    intro m w a a_tail hm hw ha hat hrate; dsimp only
    rcases all_m_balanced_pivot_ub_closed_w18 m w a a_tail hm hw ha hat hrate with
      ⟨_, _, _, hub_closed, hub_lt_3D⟩
    refine ⟨hub_closed,
            fun d_a d_mult hda hd_a hd_at hd_m hlt_WK hcop_d hcl_lt =>
              all_m_parametric_da_dmult_elim_w18 m w a a_tail d_a d_mult
                hm hw ha hat hda hd_a hd_at hd_m hlt_WK hcop_d (Nat.lt_of_le_of_lt hub_closed hcl_lt),
            ?_⟩
    intro ha_ev hat_ev h2_3W
    have hlt3 := hub_lt_3D h2_3W
    refine ⟨hlt3, ?_⟩
    rintro ⟨qs, hqs_len, hqs_spec⟩
    have hm1_succ : m - 1 = 1 + (m - 2) := by omega
    have hblk_cons : List.replicate (m - 1) (w, a) ++ [(w, a_tail)] =
        (w, a) :: (List.replicate (m - 2) (w, a) ++ [(w, a_tail)]) := by
      rw [hm1_succ, Nat.add_comm 1, List.replicate_succ, List.cons_append]
    have hpos_all : ∀ b ∈ (w, a) :: (List.replicate (m - 2) (w, a) ++ [(w, a_tail)]),
        b.1 ≥ 1 ∧ b.2 ≥ 1 := by
      intro b hb
      cases hb with
      | head => exact ⟨hw, ha⟩
      | tail _ htl =>
        rcases List.mem_append.mp htl with hrep | hsing
        · rw [List.eq_of_mem_replicate hrep]; exact ⟨hw, ha⟩
        · simp at hsing; rw [hsing]; exact ⟨hw, hat⟩
    have hlt_WK : 3 ^ blockWeightSum (List.replicate (m - 1) (w, a) ++ [(w, a_tail)]) <
        2 ^ blockStepSum (List.replicate (m - 1) (w, a) ++ [(w, a_tail)]) := by
      have hp3_pos : 3 ^ blockWeightSum (List.replicate (m - 1) (w, a) ++ [(w, a_tail)]) > 0 := pow3_pos_nat _
      omega
    have hqs_c := hqs_len; have hsp_c := hqs_spec; have hwk_c := hlt_WK
    rw [hblk_cons] at hqs_c hsp_c hwk_c
    have hcop3 := (hw17_brox.1.2 (w, a) (List.replicate (m - 2) (w, a) ++ [(w, a_tail)]) qs 2 3
      hpos_all hwk_c hqs_c hsp_c).1
    rw [← hblk_cons] at hcop3
    exact (all_m_parametric_da_dmult_elim_w18 m w a a_tail 2 3
      hm hw ha hat (by decide) ha_ev hat_ev (by decide) hlt_WK hcop3 hlt3).1 ⟨qs, hqs_len, hqs_spec⟩
  · -- Part 2: `blocks_bal7` (`> 94×` 6-pivot) & `blocks_mp7` (`> 2×` rotation-2 `s = 6` Hensel `105 * D`):
    dsimp only
    rcases bal7_6pivot_94x_cert_w18 with ⟨h94_bal7, hpos_ub_bal7⟩
    rcases mp7_hensel_and_rot6_certs_w18 with ⟨hcop7_mp7, hrot6_fin, hinv_mp7, h2_mp7, hpos_ub_mp7⟩
    have hlt_bal7 : 3 ^ blockWeightSum blocksBal7W18 < 2 ^ blockStepSum blocksBal7W18 := by
      generalize 2 ^ blockStepSum blocksBal7W18 = P2, 3 ^ blockWeightSum blocksBal7W18 = P3 at h94_bal7 ⊢
      omega
    have hlt_mp7 : 3 ^ blockWeightSum blocksMp7W18 < 2 ^ blockStepSum blocksMp7W18 := by
      generalize 2 ^ blockStepSum blocksMp7W18 = P2, 3 ^ blockWeightSum blocksMp7W18 = P3 at h2_mp7 ⊢
      omega
    have hmem7 : ∀ j : Nat, j < 7 -> j ∈ [0, 1, 2, 3, 4, 5, 6] := by
      intro j hj
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hrot5_bal7 : ∀ j : Nat, j < 7 ->
        match rotBlocks j blocksBal7W18 with
        | b0 :: b1 :: b2 :: b3 :: b4 :: rest =>
          multiPivotCarryUB [b0, b1, b2, b3] b4 rest >
            3 * (2 ^ blockStepSum blocksBal7W18 - 3 ^ blockWeightSum blocksBal7W18)
        | _ => False := by
      intro j hj
      have hb := List.all_eq_true.mp bal7_rot5_escape_cert_w18 j (hmem7 j hj)
      split at hb
      · exact of_decide_eq_true hb
      · cases hb
    have hrot6_mp7 : ∀ j : Nat, j < 7 ->
        match rotBlocks j blocksMp7W18 with
        | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: rest =>
          multiPivotCarryUB [b0, b1, b2, b3, b4] b5 rest >
            7 * (2 ^ blockStepSum blocksMp7W18 - 3 ^ blockWeightSum blocksMp7W18)
        | _ => False := by
      intro j hj
      have hb := List.all_eq_true.mp hrot6_fin j (hmem7 j hj)
      split at hb
      · exact of_decide_eq_true hb
      · cases hb
    have hno_qs_bal7 : ¬ (∃ qs : List Nat,
        qs.length = 7 ∧
        ∀ j : Nat, j < 7 ->
          (2 ^ blockStepSum blocksBal7W18 - 3 ^ blockWeightSum blocksBal7W18) * natAt qs j =
            broxSpiralCarry (rotBlocks j blocksBal7W18)) := by
      rintro ⟨qs, hlen7, hspec7⟩
      rcases hw17_brox.1.2 (17, 2) [(17, 2), (17, 2), (17, 2), (17, 2), (17, 2), (17, 58)] qs 2 3
        (by decide) hlt_bal7 hlen7 hspec7 with ⟨hcop3, hcasc3⟩
      have h3_dvd : 3 ∣ natListGcd qs := hcasc3 (by decide) (by decide) (by decide) hcop3
      have h3D_le := hw17_brox.2.1 blocksBal7W18 qs 0
        [(17, 2), (17, 2), (17, 2), (17, 2), (17, 2)] (17, 2) [(17, 58)] 3
        (by decide) hlt_bal7 hlen7 hspec7 (by decide) rfl h3_dvd
      omega
    have hno_dp2_bal7 : ¬ (∃ u0 : List MixedSRSSym, dp2AnnotatedChain u0 (dp2BlocksToShifts blocksBal7W18) u0) := by
      rintro ⟨u0, hann⟩
      rcases (leftAnchoredDP2_no_1_to_20_cycles_and_all_m_block_locks.2.2
        (17, 2) [(17, 2), (17, 2), (17, 2), (17, 2), (17, 2), (17, 58)] u0 (by decide) hann).2.2 with
        ⟨ws, qs, _, hqs_len, _, hrot_q, _, _, _, _⟩
      exact hno_qs_bal7 ⟨qs, hqs_len, fun j hj => by
        have hrj := hrot_q j hj
        cases hd_u : ws.drop j with
        | nil => rw [hd_u] at hrj; exact False.elim hrj
        | cons _ _ => rw [hd_u] at hrj; exact hrj.2.2.2.2⟩
    have hno_qs_mp7 : ¬ (∃ qs : List Nat,
        qs.length = 7 ∧
        ∀ j : Nat, j < 7 ->
          (2 ^ blockStepSum blocksMp7W18 - 3 ^ blockWeightSum blocksMp7W18) * natAt qs j =
            broxSpiralCarry (rotBlocks j blocksMp7W18)) := by
      rintro ⟨qs, hlen7, hspec7⟩
      have h7_dvd : 7 ∣ natListGcd qs :=
        (hw17_brox.1.2 (6, 3) [(6, 3), (6, 6), (6, 3), (6, 3), (6, 3), (5, 3)] qs 3 7
          (by decide) hlt_mp7 hlen7 hspec7).2 (by decide) (by decide) (by decide) hcop7_mp7
      have h105_le := hw17_brox.2.2.1 blocksMp7W18 qs 2
        (6, 6) [(6, 3), (6, 3), (6, 3), (5, 3)] (6, 3) [(6, 3)] 6 7
        (by decide) (by decide) hlt_mp7 hlen7 hspec7 (by decide) rfl
        (by decide) (by decide) (by decide) h7_dvd
      rw [hinv_mp7] at h105_le
      omega
    have hno_dp2_mp7 : ¬ (∃ u0 : List MixedSRSSym, dp2AnnotatedChain u0 (dp2BlocksToShifts blocksMp7W18) u0) := by
      rintro ⟨u0, hann⟩
      rcases (leftAnchoredDP2_no_1_to_20_cycles_and_all_m_block_locks.2.2
        (6, 3) [(6, 3), (6, 6), (6, 3), (6, 3), (6, 3), (5, 3)] u0 (by decide) hann).2.2 with
        ⟨ws, qs, _, hqs_len, _, hrot_q, _, _, _, _⟩
      exact hno_qs_mp7 ⟨qs, hqs_len, fun j hj => by
        have hrj := hrot_q j hj
        cases hd_u : ws.drop j with
        | nil => rw [hd_u] at hrj; exact False.elim hrj
        | cons _ _ => rw [hd_u] at hrj; exact hrj.2.2.2.2⟩
    exact ⟨hrot5_bal7, h94_bal7, hno_qs_bal7, hno_dp2_bal7,
           hcop7_mp7, hrot6_mp7, hinv_mp7, h2_mp7, hno_qs_mp7, hno_dp2_mp7⟩


end CollatzFormal
