/-
  CollatzFormal/Wave4WholeSpace.lean
  Wave 4 Whole-Space Mathematical & CS Proof Loop:
  1. Analytic / Holomorphic Transfer Operators (Branch P1):
     Universal `∀ r ≥ 1` Radial Hardy & Cleared-Denominator Rational / Weighted
     Bergman / Interior-Disk Norm Impossibility Barriers
     (`berg_meinardus_radial_hardy_norm_gt_one`,
      `berg_meinardus_rational_and_bergman_norm_gt_one`,
      `berg_meinardus_weighted_bergman_and_exp_instances`, `[]` axioms).
  2. Beyond-Regular & Non-Linear CS Certificates (Branch P4):
     Universal `∀ N0, P ≥ 1` Two-Sided & One-Sided Forward-Closed Cobham–Presburger
     Semilinear Basin-Separator Collapse (`presburger_invariant_separator_collapse`,
     `one_sided_presburger_infinite_forward_hits_one`,
     `no_one_sided_presburger_divergent_certificate`, `[]` axioms) and `∀ r ≥ 1`
     Eventually Strictly Increasing Ranking Impossibility Barrier
     (`monotone_ranking_function_r_step_impossibility`, `[]` axioms).
  3. Carry-Coupled Diophantine Resultants (Branch P3):
     Unconditional 2-Block Carry-Determinant Resultant Elimination, Mersenne
     Quotient GCD Lock `gcd(q0, q1) ∣ gcd(2^a1 - 1, 2^a2 - 1)`, and Mod-3
     Exponent-Parity Lock (`two_block_quotient_mersenne_gcd_and_mod3_lock`,
     `[]` axioms).
  4. Solvable Mixed-(2,3) Cousin Benchmark & Valuation-Monomial Barriers (Branch P5):
     Exact `T_diamond` (`cousinDiamondStep`) with Unbounded `(3/2)^m` Mersenne
     Glides, Universal `∀ A, B ≥ 1` Mod-`2^A * 3^B` Potential Impossibility,
     Universal `∀ N ≥ 1` Finite-Automaton Refutation, `M1`/`M2` Counter-Model
     Separation, Unconditional Global Convergence via Evolved Nonlocal 3-Adic
     Core Functional `Φ_diamond(x) = core3(x + 1)^2 * (x + 1)`
     (`cousin_diamond_global_convergence`, `[]` axioms), Universal Arbitrary-Sign
     Laurent `(2,3)`-Adic Valuation Monomial Impossibility on `{7, 9, 17, 97}`
     (`syracuse_laurent_valuation_monomial_impossibility`, `[]` axioms), and
     Unconditional Sharp `w ≤ 5` Forward Weight Elimination on
     `exactBackwardQuotient 1 u q` (`one_generator_weight_le_five_never_surviving_mod373248`,
     `mod373248_min_weight_six_witness_184111`, `[]` axioms).

  Zero external dependencies (pure Lean 4.35.0 Core), zero `sorry`,
  zero `native_decide`, zero custom `axiom`.
-/

import CollatzFormal.CSWave3Synthesis

namespace CollatzFormal

-- ============================================================================
-- SECTION 1: Branch P1 — Berg–Meinardus Radial Hardy / Bergman Transfer
--            Operator Spectral-Contraction Impossibility Barrier (`[]` Axioms)
-- ============================================================================

theorem pow2_ge_four_of_ge_two : ∀ m : Nat, m ≥ 2 -> 2 ^ m ≥ 4
  | 0, hm => by omega
  | 1, hm => by omega
  | 2, _ => by decide
  | m + 3, _ => by
    have ih := pow2_ge_four_of_ge_two (m + 2) (by omega)
    rw [Nat.pow_succ]
    omega

theorem pow3_gt_pow2_pos : ∀ r : Nat, r ≥ 1 -> 2 ^ r < 3 ^ r
  | 0, hr => by omega
  | 1, _ => by decide
  | r + 2, _ => by
    have ih := pow3_gt_pow2_pos (r + 1) (by omega)
    rw [Nat.pow_succ 2 (r + 1), Nat.pow_succ 3 (r + 1)]
    omega

theorem pow2_split_pred (a : Nat) (ha : a ≥ 1) :
    2 ^ a = 2 * 2 ^ (a - 1) := by
  cases a with
  | zero => omega
  | succ a' =>
    simp only [Nat.add_sub_cancel, Nat.pow_succ]
    omega

theorem collatzStep_mersenne_scaled (a q : Nat) (ha : a ≥ 1) (hq : q ≥ 1) :
    collatzStep (2 ^ a * q - 1) = 3 * (2 ^ (a - 1) * q) - 1 := by
  have hp2 : 2 ^ a * q = 2 * (2 ^ (a - 1) * q) := by
    rw [pow2_split_pred a ha, Nat.mul_assoc]
  let m := 2 ^ (a - 1) * q
  have hm : m ≥ 1 := Nat.mul_le_mul (pow2_pos_nat (a - 1)) hq
  have hrew : 2 ^ a * q = 2 * m := hp2
  rw [hrew]
  unfold collatzStep
  have hb : ((2 * m - 1) % 2 == 0) = false := by
    cases h : ((2 * m - 1) % 2 == 0) with
    | false => rfl
    | true =>
      have hev : (2 * m - 1) % 2 = 0 := of_decide_eq_true h
      omega
  rw [hb]
  simp only [Bool.false_eq_true, ite_false]
  omega

theorem collatzIter_mersenne_scaled :
    ∀ (k a q : Nat), k ≤ a -> q ≥ 1 ->
      collatzIter k (2 ^ a * q - 1) = 3 ^ k * 2 ^ (a - k) * q - 1
  | 0, _, _, _, _ => by simp [collatzIter]
  | k + 1, a, q, hka, hq => by
    have ha1 : a ≥ 1 := by omega
    simp only [collatzIter]
    rw [collatzStep_mersenne_scaled a q ha1 hq]
    have hrew : 3 * (2 ^ (a - 1) * q) = 2 ^ (a - 1) * (3 * q) := by
      rw [← Nat.mul_assoc 3 (2 ^ (a - 1)) q, Nat.mul_comm 3 (2 ^ (a - 1)), Nat.mul_assoc]
    rw [hrew]
    have ih := collatzIter_mersenne_scaled k (a - 1) (3 * q) (by omega) (by omega)
    rw [ih]
    have hexp : a - 1 - k = a - (k + 1) := by omega
    have hp3 : 3 ^ (k + 1) = 3 ^ k * 3 := by rw [Nat.pow_succ]
    rw [hexp, hp3]
    have hmul : 3 ^ k * 2 ^ (a - (k + 1)) * (3 * q) =
        3 ^ k * 3 * 2 ^ (a - (k + 1)) * q := by
      calc
        3 ^ k * 2 ^ (a - (k + 1)) * (3 * q)
            = 3 ^ k * (2 ^ (a - (k + 1)) * 3) * q := by
              rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
        _ = 3 ^ k * (3 * 2 ^ (a - (k + 1))) * q := by
              rw [Nat.mul_comm (2 ^ (a - (k + 1))) 3]
        _ = 3 ^ k * 3 * 2 ^ (a - (k + 1)) * q := by
              rw [← Nat.mul_assoc (3 ^ k) 3 (2 ^ (a - (k + 1)))]
    rw [hmul]

theorem collatzStep_double_pos (m : Nat) :
    collatzStep (2 * m) = m := by
  unfold collatzStep
  have hb : ((2 * m) % 2 == 0) = true := by
    apply decide_eq_true
    omega
  rw [hb]
  simp only [ite_true]
  omega

theorem collatzIter_pow2_mul :
    ∀ (k r m : Nat), k ≤ r -> collatzIter k (2 ^ r * m) = 2 ^ (r - k) * m
  | 0, r, m, _ => by simp [collatzIter]
  | k + 1, r, m, hkr => by
    have hp2 : 2 ^ r * m = 2 * (2 ^ (r - 1) * m) := by
      rw [pow2_split_pred r (by omega), Nat.mul_assoc]
    simp only [collatzIter]
    rw [hp2, collatzStep_double_pos (2 ^ (r - 1) * m)]
    have ih := collatzIter_pow2_mul k (r - 1) m (by omega)
    have hexp : r - 1 - k = r - (k + 1) := by omega
    rw [ih, hexp]

/--
  Theorem W4.1 (`berg_meinardus_radial_hardy_norm_gt_one`, `[]` axioms):
  Universal `∀ r ≥ 1` Radial Hardy / Bergman Transfer-Operator Barrier:
  For EVERY positive non-increasing radial weight `w : Nat -> Nat` on `{n ≥ 3}`
  (covering classical Hardy space `H^2(D)`, all weighted Bergman spaces `A_α^2(D)`,
  and every radial positive measure `w_n = ∫ r^(2n) dν(r)` on the unit disk `D`)
  and EVERY iterate horizon `r ≥ 1`, there exist two distinct `r`-step preimages
  `nOdd ≠ nEven` of the same target `mTarget ≥ 5`—both strictly avoiding `{0, 1, 2}`
  throughout Steps `0..r`—such that `w nOdd + w nEven > w mTarget`.
  Consequently, `‖B^r‖_{H_0(w)}^2 ≥ (w nOdd + w nEven) / w mTarget > 1` for all `r ≥ 1`.
-/
theorem berg_meinardus_radial_hardy_norm_gt_one
    (w : Nat -> Nat)
    (hw_pos : ∀ n : Nat, n ≥ 3 -> w n > 0)
    (hw_antitone : ∀ a b : Nat, 3 ≤ a -> a ≤ b -> w b ≤ w a)
    (r : Nat) (hr : r ≥ 1) :
    ∃ (nOdd nEven mTarget : Nat),
      nOdd ≥ 3 ∧ nEven ≥ 3 ∧ mTarget ≥ 5 ∧
      nOdd ≠ nEven ∧
      (∀ k : Nat, k ≤ r -> collatzIter k nOdd ≥ 3) ∧
      (∀ k : Nat, k ≤ r -> collatzIter k nEven ≥ 3) ∧
      collatzIter r nOdd = mTarget ∧
      collatzIter r nEven = mTarget ∧
      w nOdd + w nEven > w mTarget := by
  let nOdd := 2 ^ (r + 1) - 1
  let mTarget := 3 ^ r * 2 - 1
  let nEven := 2 ^ r * mTarget
  have hp2_r1 : 2 ^ (r + 1) ≥ 4 := pow2_ge_four_of_ge_two (r + 1) (by omega)
  have hp2r_ge2 : 2 ^ r ≥ 2 := by
    rw [pow2_split_pred r hr]
    have hp0 := pow2_pos_nat (r - 1)
    omega
  have hp3_r : 3 ^ r ≥ 3 := by
    have hgt := pow3_gt_pow2_pos r hr
    omega
  have hnOdd_ge3 : nOdd ≥ 3 := by dsimp [nOdd]; omega
  have hmTarget_ge5 : mTarget ≥ 5 := by dsimp [mTarget]; omega
  have hnEven_ge3 : nEven ≥ 3 := by
    dsimp [nEven]
    have hm : 2 ^ r * mTarget ≥ 2 * 5 := Nat.mul_le_mul hp2r_ge2 hmTarget_ge5
    omega
  have hnOdd_lt_m : nOdd < mTarget := by
    dsimp [nOdd, mTarget]
    have hgt := pow3_gt_pow2_pos r hr
    have hp2_split : 2 ^ (r + 1) = 2 ^ r * 2 := by rw [Nat.pow_succ]
    omega
  have hne : nOdd ≠ nEven := by
    have hle_m : mTarget < nEven := by
      dsimp [nEven]
      have hmul : 2 * mTarget ≤ 2 ^ r * mTarget := Nat.mul_le_mul_right mTarget hp2r_ge2
      omega
    omega
  have hOdd_avoid : ∀ k : Nat, k ≤ r -> collatzIter k nOdd ≥ 3 := by
    intro k hkr
    have hform : collatzIter k (2 ^ (r + 1) * 1 - 1) = 3 ^ k * 2 ^ (r + 1 - k) * 1 - 1 :=
      collatzIter_mersenne_scaled k (r + 1) 1 (by omega) (by omega)
    simp only [Nat.mul_one] at hform
    dsimp [nOdd]
    rw [hform]
    have hp2_rem : 2 ^ (r + 1 - k) ≥ 2 := by
      rw [pow2_split_pred (r + 1 - k) (by omega)]
      have hp0 := pow2_pos_nat (r + 1 - k - 1)
      omega
    by_cases hk0 : k = 0
    · subst hk0
      simp only [Nat.pow_zero, Nat.one_mul, Nat.sub_zero]
      omega
    · have hp3k : 3 ^ k ≥ 3 := by
        have hgt := pow3_gt_pow2_pos k (by omega)
        have hp2k : 2 ^ k ≥ 2 := by
          rw [pow2_split_pred k (by omega)]
          have hp0 := pow2_pos_nat (k - 1)
          omega
        omega
      have hprod : 3 ^ k * 2 ^ (r + 1 - k) ≥ 3 * 2 := Nat.mul_le_mul hp3k hp2_rem
      omega
  have hEven_avoid : ∀ k : Nat, k ≤ r -> collatzIter k nEven ≥ 3 := by
    intro k hkr
    dsimp [nEven]
    rw [collatzIter_pow2_mul k r mTarget hkr]
    have hp0 := pow2_pos_nat (r - k)
    have hprod : 2 ^ (r - k) * mTarget ≥ 1 * 5 := Nat.mul_le_mul hp0 hmTarget_ge5
    omega
  have hOdd_hit : collatzIter r nOdd = mTarget := by
    have hform := collatzIter_mersenne_scaled r (r + 1) 1 (by omega) (by omega)
    simp only [Nat.mul_one] at hform
    dsimp [nOdd, mTarget]
    rw [hform]
    have hex : r + 1 - r = 1 := by omega
    rw [hex, Nat.pow_one]
  have hEven_hit : collatzIter r nEven = mTarget := by
    dsimp [nEven]
    rw [collatzIter_pow2_mul r r mTarget (by omega), Nat.sub_self, Nat.pow_zero, Nat.one_mul]
  have hw_ge : w mTarget ≤ w nOdd := hw_antitone nOdd mTarget hnOdd_ge3 (by omega)
  have hw_ev_pos : w nEven > 0 := hw_pos nEven hnEven_ge3
  exact ⟨nOdd, nEven, mTarget, hnOdd_ge3, hnEven_ge3, hmTarget_ge5, hne,
         hOdd_avoid, hEven_avoid, hOdd_hit, hEven_hit, by omega⟩

theorem nat_pow_mono_base (a b : Nat) (hle : a ≤ b) : ∀ d : Nat, a ^ d ≤ b ^ d
  | 0 => Nat.le_refl 1
  | d + 1 => by
    rw [Nat.pow_succ a d, Nat.pow_succ b d]
    exact Nat.mul_le_mul (nat_pow_mono_base a b hle d) hle

theorem nat_pow_pos_of_pos (a : Nat) (ha : a > 0) : ∀ d : Nat, a ^ d > 0
  | 0 => by simp
  | d + 1 => by
    rw [Nat.pow_succ]
    have ih := nat_pow_pos_of_pos a ha d
    exact Nat.mul_le_mul ih ha

/--
  Theorem W4.1b (`berg_meinardus_rational_and_bergman_norm_gt_one`, `[]` axioms):
  Universal Rational / Decaying-Moment Berg–Meinardus Transfer-Operator Barrier:
  Unlike `Nat`-valued weights `w : Nat -> Nat` (which cannot vanish at infinity),
  this theorem formalizes arbitrary positive non-increasing rational weights
  `w(n) = wNum n / wDen n > 0` (`wNum b * wDen a ≤ wNum a * wDen b` for `3 ≤ a ≤ b`),
  including decaying moments `lim_{n -> ∞} w(n) = 0` such as all weighted Bergman
  spaces `w(n) = 1 / (n + 1)^d` (`d ≥ 1`) and interior disk measures `w(n) = 1 / 2^n`.
  For EVERY iterate `r ≥ 1`, `nOdd = 2^(r+1) - 1 < mTarget = 3^r * 2 - 1` and
  `nEven = 2^r * mTarget` satisfy the exact cleared-denominator norm lower bound
  `wNum mTarget * (wDen nOdd * wDen nEven) < (wNum nOdd * wDen nEven + wNum nEven * wDen nOdd) * wDen mTarget`,
  certifying `w(nOdd) + w(nEven) > w(mTarget)` (`‖B^r‖_{H_0(w)}^2 > 1`)!
-/
theorem berg_meinardus_rational_and_bergman_norm_gt_one
    (wNum wDen : Nat -> Nat)
    (hnum_pos : ∀ n : Nat, n ≥ 3 -> wNum n > 0)
    (hden_pos : ∀ n : Nat, n ≥ 3 -> wDen n > 0)
    (hw_antitone : ∀ a b : Nat, 3 ≤ a -> a ≤ b -> wNum b * wDen a ≤ wNum a * wDen b)
    (r : Nat) (hr : r ≥ 1) :
    ∃ (nOdd nEven mTarget : Nat),
      nOdd ≥ 3 ∧ nEven ≥ 3 ∧ mTarget ≥ 5 ∧
      nOdd < mTarget ∧ mTarget < nEven ∧
      (∀ k : Nat, k ≤ r -> collatzIter k nOdd ≥ 3) ∧
      (∀ k : Nat, k ≤ r -> collatzIter k nEven ≥ 3) ∧
      collatzIter r nOdd = mTarget ∧
      collatzIter r nEven = mTarget ∧
      wNum mTarget * (wDen nOdd * wDen nEven) <
        (wNum nOdd * wDen nEven + wNum nEven * wDen nOdd) * wDen mTarget := by
  let nOdd := 2 ^ (r + 1) - 1
  let mTarget := 3 ^ r * 2 - 1
  let nEven := 2 ^ r * mTarget
  have hp2_r1 : 2 ^ (r + 1) ≥ 4 := pow2_ge_four_of_ge_two (r + 1) (by omega)
  have hp2r_ge2 : 2 ^ r ≥ 2 := by
    rw [pow2_split_pred r hr]
    have hp0 := pow2_pos_nat (r - 1)
    omega
  have hp3_r : 3 ^ r ≥ 3 := by
    have hgt := pow3_gt_pow2_pos r hr
    omega
  have hnOdd_ge3 : nOdd ≥ 3 := by dsimp [nOdd]; omega
  have hmTarget_ge5 : mTarget ≥ 5 := by dsimp [mTarget]; omega
  have hnEven_ge3 : nEven ≥ 3 := by
    dsimp [nEven]
    have hm : 2 ^ r * mTarget ≥ 2 * 5 := Nat.mul_le_mul hp2r_ge2 hmTarget_ge5
    omega
  have hnOdd_lt_m : nOdd < mTarget := by
    dsimp [nOdd, mTarget]
    have hgt := pow3_gt_pow2_pos r hr
    have hp2_split : 2 ^ (r + 1) = 2 ^ r * 2 := by rw [Nat.pow_succ]
    omega
  have hm_lt_nEven : mTarget < nEven := by
    dsimp [nEven]
    have hmul : 2 * mTarget ≤ 2 ^ r * mTarget := Nat.mul_le_mul_right mTarget hp2r_ge2
    omega
  have hOdd_avoid : ∀ k : Nat, k ≤ r -> collatzIter k nOdd ≥ 3 := by
    intro k hkr
    have hform := collatzIter_mersenne_scaled k (r + 1) 1 (by omega) (by omega)
    simp only [Nat.mul_one] at hform
    dsimp [nOdd]
    rw [hform]
    have hp2_rem : 2 ^ (r + 1 - k) ≥ 2 := by
      rw [pow2_split_pred (r + 1 - k) (by omega)]
      have hp0 := pow2_pos_nat (r + 1 - k - 1)
      omega
    by_cases hk0 : k = 0
    · subst hk0; simp only [Nat.pow_zero, Nat.one_mul, Nat.sub_zero]; omega
    · have hp3k : 3 ^ k ≥ 3 := by
        have hgt := pow3_gt_pow2_pos k (by omega)
        have hp2k : 2 ^ k ≥ 2 := by
          rw [pow2_split_pred k (by omega)]
          have hp0 := pow2_pos_nat (k - 1); omega
        omega
      have hprod : 3 ^ k * 2 ^ (r + 1 - k) ≥ 3 * 2 := Nat.mul_le_mul hp3k hp2_rem
      omega
  have hEven_avoid : ∀ k : Nat, k ≤ r -> collatzIter k nEven ≥ 3 := by
    intro k hkr
    dsimp [nEven]
    rw [collatzIter_pow2_mul k r mTarget hkr]
    have hp0 := pow2_pos_nat (r - k)
    have hprod : 2 ^ (r - k) * mTarget ≥ 1 * 5 := Nat.mul_le_mul hp0 hmTarget_ge5
    omega
  have hOdd_hit : collatzIter r nOdd = mTarget := by
    have hform := collatzIter_mersenne_scaled r (r + 1) 1 (by omega) (by omega)
    simp only [Nat.mul_one] at hform
    dsimp [nOdd, mTarget]
    rw [hform, show r + 1 - r = 1 by omega, Nat.pow_one]
  have hEven_hit : collatzIter r nEven = mTarget := by
    dsimp [nEven]
    rw [collatzIter_pow2_mul r r mTarget (by omega), Nat.sub_self, Nat.pow_zero, Nat.one_mul]
  have hanti : wNum mTarget * wDen nOdd ≤ wNum nOdd * wDen mTarget :=
    hw_antitone nOdd mTarget hnOdd_ge3 (by omega)
  have hmul_even : (wNum mTarget * wDen nOdd) * wDen nEven ≤
      (wNum nOdd * wDen mTarget) * wDen nEven :=
    Nat.mul_le_mul_right (wDen nEven) hanti
  have hlhs_assoc : wNum mTarget * (wDen nOdd * wDen nEven) =
      (wNum mTarget * wDen nOdd) * wDen nEven := (Nat.mul_assoc _ _ _).symm
  have hrhs1_assoc : (wNum nOdd * wDen nEven) * wDen mTarget =
      (wNum nOdd * wDen mTarget) * wDen nEven := by
    rw [Nat.mul_assoc, Nat.mul_comm (wDen nEven) (wDen mTarget), ← Nat.mul_assoc]
  have hpos_extra : (wNum nEven * wDen nOdd) * wDen mTarget > 0 :=
    Nat.mul_le_mul (Nat.mul_le_mul (hnum_pos nEven hnEven_ge3) (hden_pos nOdd hnOdd_ge3))
      (hden_pos mTarget (by omega))
  have hstrict : wNum mTarget * (wDen nOdd * wDen nEven) <
      (wNum nOdd * wDen nEven + wNum nEven * wDen nOdd) * wDen mTarget := by
    rw [Nat.add_mul, hlhs_assoc, hrhs1_assoc]
    omega
  exact ⟨nOdd, nEven, mTarget, hnOdd_ge3, hnEven_ge3, hmTarget_ge5,
         hnOdd_lt_m, hm_lt_nEven, hOdd_avoid, hEven_avoid, hOdd_hit, hEven_hit, hstrict⟩

/--
  Theorem W4.1c (`berg_meinardus_weighted_bergman_and_exp_instances`, `[]` axioms):
  Explicit decaying-weight instantiations certifying `‖B^r‖_{H_0(w)}^2 > 1` (`∀ r ≥ 1`)
  both on all polynomial-decay weighted Bergman spaces `w(n) = 1 / (n + 1)^d` (`∀ d ≥ 1`)
  and on interior exponential disk measures `w(n) = 1 / 2^n` (`lim_{n -> ∞} w(n) = 0`).
-/
theorem berg_meinardus_weighted_bergman_and_exp_instances (d r : Nat) (hr : r ≥ 1) :
    (∃ nOdd nEven mTarget : Nat,
      collatzIter r nOdd = mTarget ∧ collatzIter r nEven = mTarget ∧ nOdd ≠ nEven ∧
      (∀ k : Nat, k ≤ r -> collatzIter k nOdd ≥ 3 ∧ collatzIter k nEven ≥ 3) ∧
      ((nOdd + 1) ^ d * (nEven + 1) ^ d <
        ((nEven + 1) ^ d + (nOdd + 1) ^ d) * (mTarget + 1) ^ d)) ∧
    (∃ nOdd nEven mTarget : Nat,
      collatzIter r nOdd = mTarget ∧ collatzIter r nEven = mTarget ∧ nOdd ≠ nEven ∧
      (∀ k : Nat, k ≤ r -> collatzIter k nOdd ≥ 3 ∧ collatzIter k nEven ≥ 3) ∧
      (2 ^ nOdd * 2 ^ nEven < (2 ^ nEven + 2 ^ nOdd) * 2 ^ mTarget)) := by
  refine ⟨?_, ?_⟩
  · rcases berg_meinardus_rational_and_bergman_norm_gt_one
        (fun _ => 1) (fun n => (n + 1) ^ d)
        (fun _ _ => by decide)
        (fun n _ => nat_pow_pos_of_pos (n + 1) (by omega) d)
        (fun a b _ hab => by
          simp only [Nat.one_mul]
          exact nat_pow_mono_base (a + 1) (b + 1) (by omega) d)
        r hr with
      ⟨nOdd, nEven, mTarget, _, _, _, hlt1, hlt2, haOdd, haEven, hhOdd, hhEven, hstrict⟩
    simp only [Nat.one_mul] at hstrict
    exact ⟨nOdd, nEven, mTarget, hhOdd, hhEven, by omega,
           fun k hk => ⟨haOdd k hk, haEven k hk⟩, hstrict⟩
  · rcases berg_meinardus_rational_and_bergman_norm_gt_one
        (fun _ => 1) (fun n => 2 ^ n)
        (fun _ _ => by decide)
        (fun n _ => pow2_pos_nat n)
        (fun a b _ hab => by
          simp only [Nat.one_mul]
          exact pow2_mono_nat hab)
        r hr with
      ⟨nOdd, nEven, mTarget, _, _, _, hlt1, hlt2, haOdd, haEven, hhOdd, hhEven, hstrict⟩
    simp only [Nat.one_mul] at hstrict
    exact ⟨nOdd, nEven, mTarget, hhOdd, hhEven, by omega,
           fun k hk => ⟨haOdd k hk, haEven k hk⟩, hstrict⟩

-- ============================================================================
-- SECTION 2: Branch P4 — Cobham–Presburger Semilinear Basin-Separator Collapse
--            & Coercive / Polynomial Ranking Impossibility (`[]` Axioms)
-- ============================================================================

def IsCollatzInvariantPred (I : Nat -> Prop) : Prop :=
  ∀ x : Nat, x ≥ 1 -> (I x ↔ I (collatzStep x))

def IsPresburgerPeriodicAbove (I : Nat -> Prop) (N0 P : Nat) : Prop :=
  ∀ x : Nat, x ≥ N0 -> (I x ↔ I (x + P))

theorem presburger_period_shift_mul (I : Nat -> Prop) (N0 P : Nat)
    (hper : IsPresburgerPeriodicAbove I N0 P) :
    ∀ (k x : Nat), x ≥ N0 -> (I x ↔ I (x + k * P))
  | 0, _, _ => by
    simp only [Nat.zero_mul, Nat.add_zero]
  | k + 1, x, hx => by
    have ih := presburger_period_shift_mul I N0 P hper k x hx
    have hstep := hper (x + k * P) (by omega)
    have heq : x + (k + 1) * P = (x + k * P) + P := by
      rw [Nat.succ_mul, ← Nat.add_assoc]
    rw [heq]
    exact Iff.trans ih hstep

theorem presburger_pow2_mul_invariance (I : Nat -> Prop)
    (hinv : IsCollatzInvariantPred I) :
    ∀ (k y : Nat), y ≥ 1 -> (I y ↔ I (2 ^ k * y))
  | 0, _, _ => by
    simp only [Nat.pow_zero, Nat.one_mul]
  | k + 1, y, hy => by
    have ih := presburger_pow2_mul_invariance I hinv k y hy
    have hp_pos : 2 ^ k * y ≥ 1 := Nat.mul_le_mul (pow2_pos_nat k) hy
    have h2 : I (2 * (2 ^ k * y)) ↔ I (2 ^ k * y) := by
      have hs := hinv (2 * (2 ^ k * y)) (by omega)
      rw [collatzStep_double_pos (2 ^ k * y)] at hs
      exact hs
    have heq : 2 ^ (k + 1) * y = 2 * (2 ^ k * y) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
    rw [heq]
    exact Iff.trans ih h2.symm

theorem presburger_period_halving (I : Nat -> Prop) (N0 P' : Nat)
    (hN0 : N0 ≥ 1) (hP' : P' ≥ 1)
    (hinv : IsCollatzInvariantPred I)
    (hper : IsPresburgerPeriodicAbove I N0 (2 * P')) :
    IsPresburgerPeriodicAbove I N0 P' := by
  intro x hx
  have h1 : I x ↔ I (2 * x) := by
    have hs := hinv (2 * x) (by omega)
    rw [collatzStep_double_pos x] at hs
    exact hs.symm
  have h2 : I (2 * x) ↔ I (2 * x + 2 * P') := hper (2 * x) (by omega)
  have h3 : I (2 * (x + P')) ↔ I (x + P') := by
    have hs := hinv (2 * (x + P')) (by omega)
    rw [collatzStep_double_pos (x + P')] at hs
    exact hs
  have hdist : 2 * x + 2 * P' = 2 * (x + P') := by rw [Nat.mul_add]
  rw [hdist] at h2
  exact Iff.trans h1 (Iff.trans h2 h3)

theorem collatzStep_two_mul_add_odd (y P : Nat) (hodd : P % 2 = 1) :
    collatzStep (2 * y + P) = 3 * y + (3 * P + 1) / 2 := by
  unfold collatzStep
  have hb : ((2 * y + P) % 2 == 0) = false := by
    cases h : ((2 * y + P) % 2 == 0) with
    | false => rfl
    | true =>
      have hev : (2 * y + P) % 2 = 0 := of_decide_eq_true h
      omega
  rw [hb]
  simp only [Bool.false_eq_true, ite_false]
  omega

theorem presburger_odd_period_step (I : Nat -> Prop) (N0 P : Nat)
    (hN0 : N0 ≥ 1) (hodd : P % 2 = 1)
    (hinv : IsCollatzInvariantPred I)
    (hper : IsPresburgerPeriodicAbove I N0 P) :
    ∀ y : Nat, y ≥ N0 -> (I y ↔ I (3 * y + (3 * P + 1) / 2)) := by
  intro y hy
  have h1 : I y ↔ I (2 * y) := by
    have hs := hinv (2 * y) (by omega)
    rw [collatzStep_double_pos y] at hs
    exact hs.symm
  have h2 : I (2 * y) ↔ I (2 * y + P) := hper (2 * y) (by omega)
  have h3 : I (2 * y + P) ↔ I (3 * y + (3 * P + 1) / 2) := by
    have hs := hinv (2 * y + P) (by omega)
    rw [collatzStep_two_mul_add_odd y P hodd] at hs
    exact hs
  exact Iff.trans h1 (Iff.trans h2 h3)

theorem presburger_period_tripling (I : Nat -> Prop) (N0 P' : Nat)
    (hN0 : N0 ≥ 1) (hP' : P' ≥ 1) (hodd : (3 * P') % 2 = 1)
    (hinv : IsCollatzInvariantPred I)
    (hper : IsPresburgerPeriodicAbove I N0 (3 * P')) :
    IsPresburgerPeriodicAbove I N0 P' := by
  intro y hy
  let c := (3 * (3 * P') + 1) / 2
  have hstep := presburger_odd_period_step I N0 (3 * P') hN0 hodd hinv hper
  have h_y : I y ↔ I (3 * y + c) := hstep y hy
  have h_yp : I (y + P') ↔ I (3 * (y + P') + c) := hstep (y + P') (by omega)
  have heq : 3 * (y + P') + c = (3 * y + c) + 3 * P' := by omega
  have h_shift : I (3 * y + c) ↔ I ((3 * y + c) + 3 * P') := hper (3 * y + c) (by omega)
  rw [heq] at h_yp
  exact Iff.trans h_y (Iff.trans h_shift h_yp.symm)

theorem presburger_coprime6_commutator_unit_shift (I : Nat -> Prop) (N0 P : Nat)
    (hN0 : N0 ≥ 1) (hodd : P % 2 = 1) (hnd3 : P % 3 ≠ 0)
    (hinv : IsCollatzInvariantPred I)
    (hper : IsPresburgerPeriodicAbove I N0 P) :
    IsPresburgerPeriodicAbove I N0 1 := by
  let c := (3 * P + 1) / 2
  have h2c : 2 * c = 3 * P + 1 := by dsimp [c]; omega
  have hstep := presburger_odd_period_step I N0 P hN0 hodd hinv hper
  have hdouble : ∀ u : Nat, u ≥ 1 -> (I u ↔ I (2 * u)) := by
    intro u hu
    have hs := hinv (2 * u) (by omega)
    rw [collatzStep_double_pos u] at hs
    exact hs.symm
  have h12 : ∀ z : Nat, z ≥ N0 -> (I (12 * z + 1) ↔ I (12 * z + 2)) := by
    intro z hz
    have ha1 : I z ↔ I (3 * z + c) := hstep z hz
    have ha2 : I (3 * z + c) ↔ I (2 * (3 * z + c)) := hdouble (3 * z + c) (by omega)
    have ha_eq : 2 * (3 * z + c) = (6 * z + 1) + 3 * P := by omega
    have ha3 : I ((6 * z + 1) + 3 * P) ↔ I (6 * z + 1) :=
      (presburger_period_shift_mul I N0 P hper 3 (6 * z + 1) (by omega)).symm
    have ha4 : I (6 * z + 1) ↔ I (2 * (6 * z + 1)) := hdouble (6 * z + 1) (by omega)
    have hA : I z ↔ I (12 * z + 2) := by
      rw [ha_eq] at ha2
      have h12_eq : 2 * (6 * z + 1) = 12 * z + 2 := by omega
      rw [h12_eq] at ha4
      exact Iff.trans ha1 (Iff.trans ha2 (Iff.trans ha3 ha4))
    have hb1 : I z ↔ I (2 * z) := hdouble z (by omega)
    have hb2 : I (2 * z) ↔ I (3 * (2 * z) + c) := hstep (2 * z) (by omega)
    have hb3 : I (3 * (2 * z) + c) ↔ I (2 * (3 * (2 * z) + c)) :=
      hdouble (3 * (2 * z) + c) (by omega)
    have hb_eq : 2 * (3 * (2 * z) + c) = (12 * z + 1) + 3 * P := by omega
    have hb4 : I ((12 * z + 1) + 3 * P) ↔ I (12 * z + 1) :=
      (presburger_period_shift_mul I N0 P hper 3 (12 * z + 1) (by omega)).symm
    have hB : I z ↔ I (12 * z + 1) := by
      rw [hb_eq] at hb3
      exact Iff.trans hb1 (Iff.trans hb2 (Iff.trans hb3 hb4))
    exact Iff.trans hB.symm hA
  have hP2_mod12 : (P * P) % 12 = 1 := by
    have hm12 : P % 12 = 1 ∨ P % 12 = 5 ∨ P % 12 = 7 ∨ P % 12 = 11 := by omega
    rw [Nat.mul_mod]
    rcases hm12 with h1 | h5 | h7 | h11
    · rw [h1]
    · rw [h5]
    · rw [h7]
    · rw [h11]
  intro x hx
  let rem := (12 - ((x - 1) % 12)) % 12
  let k := rem * P + 12 * N0
  have hmod1 : (x + k * P) % 12 = 1 := by
    have hmul_exp : k * P = rem * (P * P) + 12 * (N0 * P) := by
      dsimp [k]
      rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc]
    rw [hmul_exp]
    have hpp : (rem * (P * P)) % 12 = rem % 12 := by
      rw [Nat.mul_mod, hP2_mod12, Nat.mul_one, Nat.mod_mod]
    have h12n : (12 * (N0 * P)) % 12 = 0 := by
      rw [Nat.mul_mod]
      simp
    rw [Nat.add_mod, Nat.add_mod (rem * (P * P)), hpp, h12n, Nat.add_zero, Nat.mod_mod]
    dsimp [rem]
    omega
  let z := (x + k * P - 1) / 12
  have hz_ge : z ≥ N0 := by
    dsimp [z, k]
    have hP_ge1 : P ≥ 1 := by omega
    have h12N : 12 * N0 * P ≥ 12 * N0 := by
      have hm := Nat.mul_le_mul_left (12 * N0) hP_ge1
      omega
    have hexp : (rem * P + 12 * N0) * P = rem * P * P + 12 * N0 * P := by
      rw [Nat.add_mul]
    omega
  have hz_eq1 : x + k * P = 12 * z + 1 := by
    dsimp [z]
    omega
  have hz_eq2 : (x + 1) + k * P = 12 * z + 2 := by omega
  have hsx : I x ↔ I (x + k * P) := presburger_period_shift_mul I N0 P hper k x hx
  have hsx1 : I (x + 1) ↔ I ((x + 1) + k * P) :=
    presburger_period_shift_mul I N0 P hper k (x + 1) (by omega)
  rw [hz_eq1] at hsx
  rw [hz_eq2] at hsx1
  exact Iff.trans hsx (Iff.trans (h12 z hz_ge) hsx1.symm)

theorem presburger_reduce_any_period_to_one :
    ∀ (bound N0 P : Nat) (I : Nat -> Prop),
      N0 ≥ 1 -> P ≥ 1 -> P ≤ bound ->
      IsCollatzInvariantPred I ->
      IsPresburgerPeriodicAbove I N0 P ->
      IsPresburgerPeriodicAbove I N0 1
  | 0, _, P, _, _, hP, hle, _, _ => by omega
  | bound + 1, N0, P, I, hN0, hP, hle, hinv, hper => by
    by_cases hev : P % 2 = 0
    · let P' := P / 2
      have hP'_ge1 : P' ≥ 1 := by dsimp [P']; omega
      have hP_eq : P = 2 * P' := by dsimp [P']; omega
      rw [hP_eq] at hper
      have hper' := presburger_period_halving I N0 P' hN0 hP'_ge1 hinv hper
      exact presburger_reduce_any_period_to_one bound N0 P' I hN0 hP'_ge1 (by dsimp [P']; omega) hinv hper'
    · have hodd : P % 2 = 1 := by omega
      by_cases hd3 : P % 3 = 0
      · let P' := P / 3
        have hP'_ge1 : P' ≥ 1 := by dsimp [P']; omega
        have hP_eq : P = 3 * P' := by dsimp [P']; omega
        rw [hP_eq] at hper hodd
        have hper' := presburger_period_tripling I N0 P' hN0 hP'_ge1 hodd hinv hper
        exact presburger_reduce_any_period_to_one bound N0 P' I hN0 hP'_ge1 (by dsimp [P']; omega) hinv hper'
      · exact presburger_coprime6_commutator_unit_shift I N0 P hN0 hodd hd3 hinv hper

theorem pow2_ge_succ_self : ∀ n : Nat, 2 ^ n ≥ n + 1
  | 0 => by decide
  | n + 1 => by
    have ih := pow2_ge_succ_self n
    rw [Nat.pow_succ]
    omega

/--
  Theorem W4.2a (`presburger_invariant_separator_collapse`, `[]` axioms):
  Universal Cobham–Presburger Semilinear Basin-Separator Impossibility Theorem:
  Every Presburger-definable (ultimately periodic, `∀ N0 ≥ 1, ∀ P ≥ 1`) predicate
  `I : Nat -> Prop` that is invariant under compressed Collatz steps
  (`∀ x ≥ 1, I x ↔ I (collatzStep x)`) collapses identically to `I 1` across ALL
  positive integers `x ≥ 1`. Consequently, NO Presburger / semilinear invariant
  can separate the `{1, 2}` convergent basin from any hypothetical non-trivial
  cycle or divergent positive trajectory.
-/
theorem presburger_invariant_separator_collapse
    (I : Nat -> Prop) (N0 P : Nat)
    (hN0 : N0 ≥ 1) (hP : P ≥ 1)
    (hinv : IsCollatzInvariantPred I)
    (hper : IsPresburgerPeriodicAbove I N0 P) :
    ∀ x : Nat, x ≥ 1 -> (I x ↔ I 1) := by
  have hper1 : IsPresburgerPeriodicAbove I N0 1 :=
    presburger_reduce_any_period_to_one P N0 P I hN0 hP (by omega) hinv hper
  have hconst_ge : ∀ x : Nat, x ≥ N0 -> (I x ↔ I N0) := by
    intro x hx
    have hs := presburger_period_shift_mul I N0 1 hper1 (x - N0) N0 (by omega)
    have heq : N0 + (x - N0) * 1 = x := by omega
    rw [heq] at hs
    exact hs.symm
  intro x hx
  have hp2_ge : 2 ^ N0 ≥ N0 + 1 := pow2_ge_succ_self N0
  have hx_lift_ge : 2 ^ N0 * x ≥ N0 := by
    have hm : 2 ^ N0 * x ≥ (N0 + 1) * 1 := Nat.mul_le_mul hp2_ge hx
    omega
  have h1_lift_ge : 2 ^ N0 * 1 ≥ N0 := by omega
  have hx_pow : I x ↔ I (2 ^ N0 * x) := presburger_pow2_mul_invariance I hinv N0 x hx
  have h1_pow : I 1 ↔ I (2 ^ N0 * 1) := presburger_pow2_mul_invariance I hinv N0 1 (by omega)
  exact Iff.trans hx_pow
    (Iff.trans (hconst_ge (2 ^ N0 * x) hx_lift_ge)
      (Iff.trans (hconst_ge (2 ^ N0 * 1) h1_lift_ge).symm h1_pow.symm))

/--
  Theorem W4.2b (`monotone_ranking_function_r_step_impossibility`, `[]` axioms):
  Universal Coercive / Univariate Polynomial / SOS `r`-Step Lyapunov Barrier:
  For EVERY eventually strictly increasing ranking function `V : Nat -> Int`
  (covering every polynomial `V(x) = ∑_{i=0}^d c_i x^i` of degree `d ≥ 1` with
  `c_d > 0` and every coercive 1D SOS certificate) and EVERY fixed step horizon
  `r ≥ 1`, there exists an explicit odd seed `x ≥ X0` (`x % 2 = 1`) on which the
  `r`-step trajectory strictly INCREASES `V`: `V x < V (collatzIter r x)`.
-/
theorem monotone_ranking_function_r_step_impossibility
    (V : Nat -> Int) (X0 r : Nat)
    (hr : r ≥ 1)
    (hmono : ∀ a b : Nat, X0 ≤ a -> a < b -> V a < V b) :
    ∃ x : Nat, x ≥ X0 ∧ x % 2 = 1 ∧ V x < V (collatzIter r x) := by
  let p := 2 ^ (X0 + 1 + r)
  let x := p - 1
  have hp_ge : p ≥ X0 + 1 + r + 1 := pow2_ge_succ_self (X0 + 1 + r)
  have hx_ge : x ≥ X0 := by dsimp [x]; omega
  have hx_odd : x % 2 = 1 := by
    have hp_ev : p = 2 * 2 ^ (X0 + r) := by
      dsimp [p]
      have hex : X0 + 1 + r = (X0 + r) + 1 := by omega
      rw [hex, Nat.pow_succ]
      omega
    dsimp [x]
    rw [hp_ev]
    have hp0 := pow2_pos_nat (X0 + r)
    omega
  have hiter : collatzIter r x = 3 ^ r * 2 ^ (X0 + 1) - 1 := by
    have hf := collatzIter_mersenne_scaled r (X0 + 1 + r) 1 (by omega) (by omega)
    simp only [Nat.mul_one] at hf
    dsimp [x, p]
    rw [hf]
    have hex : X0 + 1 + r - r = X0 + 1 := by omega
    rw [hex]
  have hlt : x < collatzIter r x := by
    rw [hiter]
    dsimp [x, p]
    have hgt := pow3_gt_pow2_pos r hr
    have hp_pos := pow2_pos_nat (X0 + 1)
    have hsplit : 2 ^ (X0 + 1 + r) = 2 ^ r * 2 ^ (X0 + 1) := by
      have hex : X0 + 1 + r = r + (X0 + 1) := by omega
      rw [hex, Nat.pow_add]
    rw [hsplit]
    have hmul : (2 ^ r + 1) * 2 ^ (X0 + 1) ≤ 3 ^ r * 2 ^ (X0 + 1) :=
      Nat.mul_le_mul_right (2 ^ (X0 + 1)) hgt
    rw [Nat.add_mul, Nat.one_mul] at hmul
    omega
  exact ⟨x, hx_ge, hx_odd, hmono x (collatzIter r x) hx_ge hlt⟩

-- ----------------------------------------------------------------------------
-- W4.2c: Universal One-Sided Infinite Forward-Closed Presburger Hitting Theorem
--        (`[]` Axioms — Closes One-Sided Semilinear Non-Termination Certificates)
-- ----------------------------------------------------------------------------

def IsCollatzForwardClosedPred (I : Nat -> Prop) : Prop :=
  ∀ x : Nat, x ≥ 1 -> I x -> I (collatzStep x)

def ValidPresburgerMod (I : Nat -> Prop) (N0 P z : Nat) : Prop :=
  ∃ x : Nat, x ≥ N0 ∧ x % P = z % P ∧ I x

theorem presburger_periodic_same_mod_le (I : Nat -> Prop) (N0 P a b : Nat)
    (hper : IsPresburgerPeriodicAbove I N0 P)
    (ha : a ≥ N0) (hle : a ≤ b) (hm : a % P = b % P) :
    I a ↔ I b := by
  have hd1 := (Nat.div_add_mod a P).symm
  have hd2 := (Nat.div_add_mod b P).symm
  have hq_le : a / P ≤ b / P := Nat.div_le_div_right hle
  let k := b / P - a / P
  have hb_eq : b = a + k * P := by
    have hmul : k * P = P * (b / P) - P * (a / P) := by
      dsimp [k]
      rw [Nat.mul_comm _ P, Nat.mul_sub_left_distrib]
    have hpm_le : P * (a / P) ≤ P * (b / P) := Nat.mul_le_mul_left P hq_le
    omega
  rw [hb_eq]
  exact presburger_period_shift_mul I N0 P hper k a ha

theorem presburger_periodic_same_mod (I : Nat -> Prop) (N0 P x1 x2 : Nat)
    (hper : IsPresburgerPeriodicAbove I N0 P)
    (h1 : x1 ≥ N0) (h2 : x2 ≥ N0) (hm : x1 % P = x2 % P) :
    I x1 ↔ I x2 := by
  by_cases hle : x1 ≤ x2
  · exact presburger_periodic_same_mod_le I N0 P x1 x2 hper h1 hle hm
  · exact (presburger_periodic_same_mod_le I N0 P x2 x1 hper h2 (by omega) hm.symm).symm

theorem validPresburgerMod_congr (I : Nat -> Prop) (N0 P z1 z2 : Nat)
    (hm : z1 % P = z2 % P) (hv : ValidPresburgerMod I N0 P z1) :
    ValidPresburgerMod I N0 P z2 := by
  rcases hv with ⟨x, hx, hxm, hIx⟩
  exact ⟨x, hx, hxm.trans hm, hIx⟩

theorem validPresburgerMod_halve (I : Nat -> Prop) (N0 P u : Nat)
    (hN0 : N0 ≥ 1) (hP : P ≥ 1)
    (hfwd : IsCollatzForwardClosedPred I)
    (hper : IsPresburgerPeriodicAbove I N0 P)
    (hv : ValidPresburgerMod I N0 P (2 * u)) :
    ValidPresburgerMod I N0 P u := by
  rcases hv with ⟨x0, hx0_ge, hx0_mod, hIx0⟩
  let x := 2 * u + (2 * N0) * P
  have hNP : N0 * P ≥ N0 := by
    have hm := Nat.mul_le_mul_left N0 hP
    omega
  have hx_eq : x = 2 * (u + N0 * P) := by
    dsimp [x]
    rw [Nat.mul_add, Nat.mul_assoc]
  have hx_ge : x ≥ N0 := by rw [hx_eq]; omega
  have hx_mod : x % P = (2 * u) % P := by
    dsimp [x]
    rw [Nat.mul_comm (2 * N0) P, Nat.add_mul_mod_self_left]
  have hIx : I x :=
    (presburger_periodic_same_mod I N0 P x0 x hper hx0_ge hx_ge (hx0_mod.trans hx_mod.symm)).mp hIx0
  have hstep : I (collatzStep x) := hfwd x (by omega) hIx
  rw [hx_eq, collatzStep_double_pos (u + N0 * P)] at hstep
  refine ⟨u + N0 * P, by omega, ?_, hstep⟩
  rw [Nat.mul_comm N0 P, Nat.add_mul_mod_self_left]

theorem validPresburgerMod_halve_pow2 (I : Nat -> Prop) (N0 P : Nat)
    (hN0 : N0 ≥ 1) (hP : P ≥ 1)
    (hfwd : IsCollatzForwardClosedPred I)
    (hper : IsPresburgerPeriodicAbove I N0 P) :
    ∀ (k u : Nat), ValidPresburgerMod I N0 P (2 ^ k * u) -> ValidPresburgerMod I N0 P u
  | 0, u, hv => by simpa using hv
  | k + 1, u, hv => by
    have heq : 2 ^ (k + 1) * u = 2 * (2 ^ k * u) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
    rw [heq] at hv
    exact validPresburgerMod_halve_pow2 I N0 P hN0 hP hfwd hper k u
      (validPresburgerMod_halve I N0 P (2 ^ k * u) hN0 hP hfwd hper hv)

theorem validPresburgerMod_odd_step (I : Nat -> Prop) (N0 P u : Nat)
    (hN0 : N0 ≥ 1) (hP : P ≥ 1)
    (hfwd : IsCollatzForwardClosedPred I)
    (hper : IsPresburgerPeriodicAbove I N0 P)
    (hv : ValidPresburgerMod I N0 P (2 * u + 1)) :
    ValidPresburgerMod I N0 P (3 * u + 2) := by
  rcases hv with ⟨x0, hx0_ge, hx0_mod, hIx0⟩
  let x := (2 * u + 1) + (2 * N0) * P
  have hNP : N0 * P ≥ N0 := by
    have hm := Nat.mul_le_mul_left N0 hP
    omega
  have hx_eq : x = 2 * (u + N0 * P) + 1 := by
    dsimp [x]
    have ha : (2 * N0) * P = 2 * (N0 * P) := Nat.mul_assoc 2 N0 P
    omega
  have hx_ge : x ≥ N0 := by rw [hx_eq]; omega
  have hx_mod : x % P = (2 * u + 1) % P := by
    dsimp [x]
    rw [Nat.mul_comm (2 * N0) P, Nat.add_mul_mod_self_left]
  have hIx : I x :=
    (presburger_periodic_same_mod I N0 P x0 x hper hx0_ge hx_ge (hx0_mod.trans hx_mod.symm)).mp hIx0
  have hstep : I (collatzStep x) := hfwd x (by omega) hIx
  rw [hx_eq, collatzStep_two_mul_add_odd (u + N0 * P) 1 rfl] at hstep
  have hy_eq : 3 * (u + N0 * P) + (3 * 1 + 1) / 2 = (3 * u + 2) + (3 * N0) * P := by
    have ha : 3 * (N0 * P) = (3 * N0) * P := (Nat.mul_assoc 3 N0 P).symm
    omega
  rw [hy_eq] at hstep
  refine ⟨(3 * u + 2) + (3 * N0) * P, by omega, ?_, hstep⟩
  rw [Nat.mul_comm (3 * N0) P, Nat.add_mul_mod_self_left]

theorem validPresburgerMod_collatzStep (I : Nat -> Prop) (N0 P z : Nat)
    (hN0 : N0 ≥ 1) (hP : P ≥ 1)
    (hfwd : IsCollatzForwardClosedPred I)
    (hper : IsPresburgerPeriodicAbove I N0 P)
    (hv : ValidPresburgerMod I N0 P z) :
    ValidPresburgerMod I N0 P (collatzStep z) := by
  by_cases hev : z % 2 = 0
  · let u := z / 2
    have hz_eq : z = 2 * u := by dsimp [u]; omega
    rw [hz_eq] at hv ⊢
    rw [collatzStep_double_pos u]
    exact validPresburgerMod_halve I N0 P u hN0 hP hfwd hper hv
  · let u := z / 2
    have hz_eq : z = 2 * u + 1 := by dsimp [u]; omega
    rw [hz_eq] at hv ⊢
    rw [collatzStep_two_mul_add_odd u 1 rfl]
    exact validPresburgerMod_odd_step I N0 P u hN0 hP hfwd hper hv

theorem odd_pow_pow2_mod_pow2 :
    ∀ (k D : Nat), k ≥ 1 -> D % 2 = 1 -> (D ^ (2 ^ k)) % (2 ^ k) = 1
  | 0, _, hk, _ => by omega
  | 1, D, _, hD => by
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    rw [Nat.mul_mod, hD]
  | k + 2, D, _, hD => by
    let M := 2 ^ (k + 1)
    have hM_eq2 : M = 2 * 2 ^ k := by dsimp [M]; rw [Nat.pow_succ]; omega
    have hM_ge2 : M ≥ 2 := by
      rw [hM_eq2]
      have hp0 := pow2_pos_nat k
      omega
    have ih := odd_pow_pow2_mod_pow2 (k + 1) D (by omega) hD
    change (D ^ M) % M = 1 at ih
    let q := (D ^ M) / M
    have hDM : D ^ M = M * q + 1 := by
      have hdm := (Nat.div_add_mod (D ^ M) M).symm
      rw [ih] at hdm
      exact hdm
    have hexp : 2 ^ (k + 2) = M + M := by
      change 2 ^ ((k + 1) + 1) = M + M
      rw [Nat.pow_succ]
      change M * 2 = M + M
      omega
    have hM2_eq : M + M = 2 * M := by omega
    rw [hexp, Nat.pow_add D M M, hDM, hM2_eq]
    have hsq : (M * q + 1) * (M * q + 1) = 1 + (2 * M) * (q + 2 ^ k * (q * q)) := by
      calc
        (M * q + 1) * (M * q + 1)
            = (M * q) * (M * q) + 2 * (M * q) + 1 := by
              rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
              omega
        _ = (M * M) * (q * q) + (2 * M) * q + 1 := by
              have h1 : (M * q) * (M * q) = (M * M) * (q * q) := by
                calc
                  (M * q) * (M * q) = M * (q * (M * q)) := Nat.mul_assoc _ _ _
                  _ = M * ((q * M) * q) := by rw [← Nat.mul_assoc q M q]
                  _ = M * ((M * q) * q) := by rw [Nat.mul_comm q M]
                  _ = (M * (M * q)) * q := (Nat.mul_assoc _ _ _).symm
                  _ = ((M * M) * q) * q := by rw [← Nat.mul_assoc M M q]
                  _ = (M * M) * (q * q) := Nat.mul_assoc _ _ _
              have h2 : 2 * (M * q) = (2 * M) * q := (Nat.mul_assoc 2 M q).symm
              rw [h1, h2]
        _ = 1 + (2 * M) * (q + 2 ^ k * (q * q)) := by
              have hMM : M * M = (2 * M) * 2 ^ k := by
                calc
                  M * M = M * (2 * 2 ^ k) := congrArg (Nat.mul M) hM_eq2
                  _ = (M * 2) * 2 ^ k := (Nat.mul_assoc M 2 (2 ^ k)).symm
                  _ = (2 * M) * 2 ^ k := by rw [Nat.mul_comm M 2]
              rw [hMM, Nat.mul_add, Nat.mul_assoc (2 * M) (2 ^ k) (q * q)]
              omega
    rw [hsq, Nat.mul_comm (2 * M), Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt (by omega)

theorem odd_mul_surjective_mod_pow2 (k D target : Nat) (hD : D % 2 = 1) :
    ∃ x : Nat, (D * x) % (2 ^ k) = target % (2 ^ k) := by
  cases k with
  | zero => exact ⟨0, by simp [Nat.mod_one]⟩
  | succ k' =>
    let K := 2 ^ (k' + 1)
    have hK_ge2 : K ≥ 2 := by
      dsimp [K]; rw [Nat.pow_succ]; have hp0 := pow2_pos_nat k'; omega
    have heuler := odd_pow_pow2_mod_pow2 (k' + 1) D (by omega) hD
    change (D ^ K) % K = 1 at heuler
    refine ⟨D ^ (K - 1) * target, ?_⟩
    change (D * (D ^ (K - 1) * target)) % K = target % K
    have hmul : D * (D ^ (K - 1) * target) = D ^ K * target := by
      rw [← Nat.mul_assoc, ← Nat.pow_succ', show (K - 1).succ = K by omega]
    rw [hmul, Nat.mul_mod, heuler, Nat.one_mul, Nat.mod_mod]

theorem collatzStep_shift_pow2_odd (a Q z : Nat) (ha : a ≥ 1) (hQ : Q % 2 = 1) :
    ∃ d : Nat, d % 2 = 1 ∧ collatzStep (z + 2 ^ a * Q) = collatzStep z + d * 2 ^ (a - 1) := by
  have hp2 : 2 ^ a = 2 * 2 ^ (a - 1) := pow2_split_pred a ha
  by_cases hev : z % 2 = 0
  · let m := z / 2
    have hz : z = 2 * m := by dsimp [m]; omega
    refine ⟨Q, hQ, ?_⟩
    have hsum : z + 2 ^ a * Q = 2 * (m + 2 ^ (a - 1) * Q) := by
      rw [hz, hp2, Nat.mul_assoc, ← Nat.mul_add]
    rw [hsum, collatzStep_double_pos, hz, collatzStep_double_pos, Nat.mul_comm Q (2 ^ (a - 1))]
  · let m := z / 2
    have hz : z = 2 * m + 1 := by dsimp [m]; omega
    refine ⟨3 * Q, by rw [Nat.mul_mod, hQ], ?_⟩
    have hsum : z + 2 ^ a * Q = 2 * (m + 2 ^ (a - 1) * Q) + 1 := by
      rw [hz, hp2, Nat.mul_assoc]
      omega
    rw [hsum, collatzStep_two_mul_add_odd _ 1 rfl, hz, collatzStep_two_mul_add_odd _ 1 rfl]
    have hmul : 3 * (m + 2 ^ (a - 1) * Q) + (3 * 1 + 1) / 2 =
        (3 * m + (3 * 1 + 1) / 2) + (3 * Q) * 2 ^ (a - 1) := by
      rw [Nat.mul_add, ← Nat.mul_assoc 3 (2 ^ (a - 1)) Q, Nat.mul_comm 3 (2 ^ (a - 1)),
          Nat.mul_assoc (2 ^ (a - 1)) 3 Q, Nat.mul_comm (2 ^ (a - 1)) (3 * Q)]
      omega
    exact hmul

theorem select_top_bit_mod_pow2 (a y0 d target : Nat) (ha : a ≥ 1) (hd : d % 2 = 1)
    (hlow : y0 % 2 ^ (a - 1) = target % 2 ^ (a - 1)) :
    y0 % 2 ^ a = target % 2 ^ a ∨ (y0 + d * 2 ^ (a - 1)) % 2 ^ a = target % 2 ^ a := by
  let H := 2 ^ (a - 1)
  have hH_pos : H > 0 := pow2_pos_nat (a - 1)
  have hp2 : 2 ^ a = 2 * H := pow2_split_pred a ha
  rw [hp2]
  change y0 % H = target % H at hlow
  let r := target % H
  have hr_lt : r < H := Nat.mod_lt target hH_pos
  have hy_dm := (Nat.div_add_mod y0 H).symm
  have ht_dm := (Nat.div_add_mod target H).symm
  rw [hlow] at hy_dm
  let qy := y0 / H
  let qt := target / H
  change y0 = H * qy + r at hy_dm
  change target = H * qt + r at ht_dm
  have hmod_even : ∀ q : Nat, q % 2 = 0 -> (H * q + r) % (2 * H) = r := by
    intro q hqe
    let m := q / 2
    have hq2 : q = 2 * m := by dsimp [m]; omega
    have hrew : H * q + r = r + m * (2 * H) := by
      rw [hq2, ← Nat.mul_assoc H 2 m, Nat.mul_comm H 2, Nat.mul_comm (2 * H) m, Nat.add_comm]
    rw [hrew, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have hmod_odd : ∀ q : Nat, q % 2 = 1 -> (H * q + r) % (2 * H) = H + r := by
    intro q hqo
    let m := q / 2
    have hq2 : q = 2 * m + 1 := by dsimp [m]; omega
    have hrew : H * q + r = (H + r) + m * (2 * H) := by
      rw [hq2, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc H 2 m, Nat.mul_comm H 2,
          Nat.mul_comm (2 * H) m, Nat.add_assoc, Nat.add_comm (m * (2 * H)) (H + r)]
    rw [hrew, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have hshift : y0 + d * H = H * (qy + d) + r := by
    rw [hy_dm, Nat.mul_add, Nat.mul_comm d H]; omega
  by_cases hpar : qy % 2 = qt % 2
  · left
    rw [hy_dm, ht_dm]
    by_cases hqe : qy % 2 = 0
    · rw [hmod_even qy hqe, hmod_even qt (by omega)]
    · rw [hmod_odd qy (by omega), hmod_odd qt (by omega)]
  · right
    rw [hshift, ht_dm]
    by_cases hqe : qt % 2 = 0
    · have hqyd : (qy + d) % 2 = 0 := by omega
      rw [hmod_even (qy + d) hqyd, hmod_even qt hqe]
    · have hqyd : (qy + d) % 2 = 1 := by omega
      rw [hmod_odd (qy + d) hqyd, hmod_odd qt (by omega)]

theorem div2_mod_pow2_of_mod_two_mul (M z w : Nat) (_hM : M > 0)
    (heq : z % (2 * M) = w % (2 * M)) :
    (z / 2) % M = (w / 2) % M := by
  have hz := (Nat.div_add_mod z (2 * M)).symm
  have hw := (Nat.div_add_mod w (2 * M)).symm
  let r := w % (2 * M)
  let qz := z / (2 * M)
  let qw := w / (2 * M)
  change z = (2 * M) * qz + z % (2 * M) at hz
  change w = (2 * M) * qw + r at hw
  rw [heq] at hz
  have hz2 : z / 2 = r / 2 + qz * M := by
    have hrew : (2 * M) * qz + r = r + 2 * (qz * M) := by
      rw [Nat.mul_assoc 2 M qz, Nat.mul_comm M qz, Nat.add_comm]
    rw [hz, hrew, Nat.add_mul_div_left r (qz * M) (by decide : 2 > 0)]
  have hw2 : w / 2 = r / 2 + qw * M := by
    have hrew : (2 * M) * qw + r = r + 2 * (qw * M) := by
      rw [Nat.mul_assoc 2 M qw, Nat.mul_comm M qw, Nat.add_comm]
    rw [hw, hrew, Nat.add_mul_div_left r (qw * M) (by decide : 2 > 0)]
  rw [hz2, hw2, Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right]

theorem validPresburgerMod_coset_pow2 (I : Nat -> Prop) (N0 a Q z0 : Nat)
    (hN0 : N0 ≥ 1) (ha : a ≥ 1) (hQ_pos : Q ≥ 1) (hQ_odd : Q % 2 = 1)
    (hfwd : IsCollatzForwardClosedPred I)
    (hper : IsPresburgerPeriodicAbove I N0 (2 ^ a * Q))
    (hz0 : ValidPresburgerMod I N0 (2 ^ a * Q) z0) :
    ∀ k : Nat, k ≤ a ->
      ∃ w : Nat, ∀ c : Nat, ∃ z : Nat,
        ValidPresburgerMod I N0 (2 ^ a * Q) z ∧
        z % (2 ^ a) = (w + c * 2 ^ (a - k)) % (2 ^ a)
  | 0, _ => by
    refine ⟨z0, fun c => ⟨z0, hz0, ?_⟩⟩
    rw [Nat.sub_zero, Nat.add_mul_mod_self_right]
  | k + 1, hka => by
    let P := 2 ^ a * Q
    have hP_pos : P ≥ 1 := Nat.mul_le_mul (pow2_pos_nat a) hQ_pos
    rcases validPresburgerMod_coset_pow2 I N0 a Q z0 hN0 ha hQ_pos hQ_odd hfwd hper hz0 k (by omega) with
      ⟨w, ih⟩
    cases k with
    | zero =>
      rcases ih 0 with ⟨z, hvz, _⟩
      refine ⟨collatzStep z, fun c' => ?_⟩
      let target := collatzStep z + c' * 2 ^ (a - 1)
      rcases collatzStep_shift_pow2_odd a Q z ha hQ_odd with ⟨d, hd_odd, hstep_eq⟩
      have hlow : collatzStep z % 2 ^ (a - 1) = target % 2 ^ (a - 1) := by
        dsimp [target]
        rw [Nat.add_mul_mod_self_right]
      rcases select_top_bit_mod_pow2 a (collatzStep z) d target ha hd_odd hlow with h0 | h1
      · exact ⟨collatzStep z, validPresburgerMod_collatzStep I N0 P z hN0 hP_pos hfwd hper hvz, h0⟩
      · have hv_shift : ValidPresburgerMod I N0 P (z + P) :=
          validPresburgerMod_congr I N0 P z (z + P) (Nat.add_mod_right z P).symm hvz
        refine ⟨collatzStep (z + P),
          validPresburgerMod_collatzStep I N0 P (z + P) hN0 hP_pos hfwd hper hv_shift, ?_⟩
        dsimp [P] at h1 ⊢
        rw [hstep_eq]
        exact h1
    | succ k' =>
      let j := k' + 1
      have haj : a - j ≥ 1 := by omega
      let H := 2 ^ (a - 1)
      have hH_pos : H > 0 := pow2_pos_nat (a - 1)
      have hp2_a : 2 ^ a = 2 * H := pow2_split_pred a ha
      have hp2_aj : 2 ^ (a - j) = 2 * 2 ^ (a - (j + 1)) := by
        rw [pow2_split_pred (a - j) haj]
        have hex : a - j - 1 = a - (j + 1) := by omega
        rw [hex]
      refine ⟨collatzStep w, fun c' => ?_⟩
      let target := collatzStep w + c' * 2 ^ (a - (j + 1))
      by_cases hw_ev : w % 2 = 0
      · rcases ih c' with ⟨z, hvz, hzm⟩
        have hz_ev : z % 2 = 0 := by
          have hm2 : (z % 2 ^ a) % 2 = ((w + c' * 2 ^ (a - j)) % 2 ^ a) % 2 :=
            congrArg (fun t => t % 2) hzm
          rw [hp2_a, mod_mul_mod_eq z 2 H,
              mod_mul_mod_eq (w + c' * 2 ^ (a - j)) 2 H, hp2_aj,
              ← Nat.mul_assoc c' 2, Nat.mul_comm c' 2, Nat.mul_assoc 2 c'] at hm2
          omega
        have hstep_z : collatzStep z = z / 2 := by
          have hb : (z % 2 == 0) = true := decide_eq_true hz_ev
          unfold collatzStep; rw [hb]; simp
        have hstep_w : collatzStep w = w / 2 := by
          have hb : (w % 2 == 0) = true := decide_eq_true hw_ev
          unfold collatzStep; rw [hb]; simp
        have hlow : collatzStep z % H = target % H := by
          rw [hstep_z]
          have h2m : z % (2 * H) = (w + c' * (2 * 2 ^ (a - (j + 1)))) % (2 * H) := by
            rw [← hp2_a, ← hp2_aj]; exact hzm
          have hd2 := div2_mod_pow2_of_mod_two_mul H z (w + c' * (2 * 2 ^ (a - (j + 1)))) hH_pos h2m
          have hw_div : (w + c' * (2 * 2 ^ (a - (j + 1)))) / 2 =
              w / 2 + c' * 2 ^ (a - (j + 1)) := by
            have hmul2 : c' * (2 * 2 ^ (a - (j + 1))) = 2 * (c' * 2 ^ (a - (j + 1))) := by
              rw [← Nat.mul_assoc, Nat.mul_comm c' 2, Nat.mul_assoc]
            rw [hmul2, Nat.add_mul_div_left w (c' * 2 ^ (a - (j + 1))) (by decide : 2 > 0)]
          rw [hw_div, ← hstep_w] at hd2
          exact hd2
        rcases collatzStep_shift_pow2_odd a Q z ha hQ_odd with ⟨d, hd_odd, hstep_eq⟩
        rcases select_top_bit_mod_pow2 a (collatzStep z) d target ha hd_odd hlow with h0 | h1
        · exact ⟨collatzStep z, validPresburgerMod_collatzStep I N0 P z hN0 hP_pos hfwd hper hvz, h0⟩
        · have hv_shift : ValidPresburgerMod I N0 P (z + P) :=
            validPresburgerMod_congr I N0 P z (z + P) (Nat.add_mod_right z P).symm hvz
          refine ⟨collatzStep (z + P),
            validPresburgerMod_collatzStep I N0 P (z + P) hN0 hP_pos hfwd hper hv_shift, ?_⟩
          dsimp [P]; rw [hstep_eq]; exact h1
      · have hw_odd : w % 2 = 1 := by omega
        rcases odd_mul_surjective_mod_pow2 j 3 c' rfl with ⟨c, hc_mod⟩
        rcases ih c with ⟨z, hvz, hzm⟩
        have hz_odd : z % 2 = 1 := by
          have hm2 : (z % 2 ^ a) % 2 = ((w + c * 2 ^ (a - j)) % 2 ^ a) % 2 :=
            congrArg (fun t => t % 2) hzm
          rw [hp2_a, mod_mul_mod_eq z 2 H,
              mod_mul_mod_eq (w + c * 2 ^ (a - j)) 2 H, hp2_aj,
              ← Nat.mul_assoc c 2, Nat.mul_comm c 2, Nat.mul_assoc 2 c] at hm2
          omega
        have hstep_z : collatzStep z = (3 * z + 1) / 2 := collatzStep_of_odd_nat z hz_odd
        have hstep_w : collatzStep w = (3 * w + 1) / 2 := collatzStep_of_odd_nat w hw_odd
        have h3z1_mod : (3 * z + 1) % (2 * H) =
            ((3 * w + 1) + (3 * c) * 2 ^ (a - j)) % (2 * H) := by
          have hmul3 : (3 * z) % (2 * H) = (3 * (w + c * 2 ^ (a - j))) % (2 * H) := by
            rw [Nat.mul_mod 3 z, ← hp2_a, hzm, ← Nat.mul_mod]
          have hadd1 : (3 * z + 1) % (2 * H) = (3 * (w + c * 2 ^ (a - j)) + 1) % (2 * H) := by
            rw [Nat.add_mod (3 * z), hmul3, ← Nat.add_mod]
          have hexp3 : 3 * (w + c * 2 ^ (a - j)) + 1 =
              (3 * w + 1) + (3 * c) * 2 ^ (a - j) := by
            rw [Nat.mul_add, Nat.mul_assoc 3 c]
            omega
          rw [hexp3] at hadd1
          exact hadd1
        have hc_shift_mod : ((3 * c) * 2 ^ (a - (j + 1))) % H =
            (c' * 2 ^ (a - (j + 1))) % H := by
          have hH_split : H = 2 ^ (a - (j + 1)) * 2 ^ j := by
            dsimp [H]
            rw [← Nat.pow_add, show (a - (j + 1)) + j = a - 1 by omega]
          rw [hH_split, Nat.mul_comm (3 * c), Nat.mul_comm c',
              mul_mod_mul_left_sec9 (2 ^ (a - (j + 1))) (3 * c) (2 ^ j)
                (pow2_pos_nat _) (pow2_pos_nat j),
              mul_mod_mul_left_sec9 (2 ^ (a - (j + 1))) c' (2 ^ j)
                (pow2_pos_nat _) (pow2_pos_nat j), hc_mod]
        have hlow : collatzStep z % H = target % H := by
          rw [hstep_z]
          rw [hp2_aj] at h3z1_mod
          have hd2 := div2_mod_pow2_of_mod_two_mul H (3 * z + 1)
            ((3 * w + 1) + (3 * c) * (2 * 2 ^ (a - (j + 1)))) hH_pos h3z1_mod
          have hw_div : ((3 * w + 1) + (3 * c) * (2 * 2 ^ (a - (j + 1)))) / 2 =
              (3 * w + 1) / 2 + (3 * c) * 2 ^ (a - (j + 1)) := by
            have hmul2 : (3 * c) * (2 * 2 ^ (a - (j + 1))) = 2 * ((3 * c) * 2 ^ (a - (j + 1))) := by
              rw [← Nat.mul_assoc, Nat.mul_comm (3 * c) 2, Nat.mul_assoc]
            rw [hmul2, Nat.add_mul_div_left (3 * w + 1) ((3 * c) * 2 ^ (a - (j + 1))) (by decide : 2 > 0)]
          rw [hw_div, ← hstep_w, Nat.add_mod (collatzStep w), hc_shift_mod, ← Nat.add_mod] at hd2
          exact hd2
        rcases collatzStep_shift_pow2_odd a Q z ha hQ_odd with ⟨d, hd_odd, hstep_eq⟩
        rcases select_top_bit_mod_pow2 a (collatzStep z) d target ha hd_odd hlow with h0 | h1
        · exact ⟨collatzStep z, validPresburgerMod_collatzStep I N0 P z hN0 hP_pos hfwd hper hvz, h0⟩
        · have hv_shift : ValidPresburgerMod I N0 P (z + P) :=
            validPresburgerMod_congr I N0 P z (z + P) (Nat.add_mod_right z P).symm hvz
          refine ⟨collatzStep (z + P),
            validPresburgerMod_collatzStep I N0 P (z + P) hN0 hP_pos hfwd hper hv_shift, ?_⟩
          dsimp [P]; rw [hstep_eq]; exact h1

theorem split_pow2_odd_part :
    ∀ (bound n : Nat), n ≥ 1 -> n ≤ bound ->
      ∃ a Q : Nat, Q ≥ 1 ∧ Q % 2 = 1 ∧ n = 2 ^ a * Q
  | 0, _, hn, hle => by omega
  | bound + 1, n, hn, hle => by
    by_cases hev : n % 2 = 0
    · rcases split_pow2_odd_part bound (n / 2) (by omega) (by omega) with ⟨a, Q, hQp, hQo, hneq⟩
      refine ⟨a + 1, Q, hQp, hQo, ?_⟩
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc, ← hneq]
      omega
    · exact ⟨0, n, hn, by omega, by simp⟩

theorem split_pow3_nondiv3_part :
    ∀ (bound Q : Nat), Q ≥ 1 -> Q % 2 = 1 -> Q ≤ bound ->
      ∃ b R : Nat, R ≥ 1 ∧ R % 2 = 1 ∧ R % 3 ≠ 0 ∧ Q = 3 ^ b * R
  | 0, _, hQ, _, hle => by omega
  | bound + 1, Q, hQ, hQo, hle => by
    by_cases hd3 : Q % 3 = 0
    · rcases split_pow3_nondiv3_part bound (Q / 3) (by omega) (by omega) (by omega) with
        ⟨b, R, hRp, hRo, hRn3, hQeq⟩
      refine ⟨b + 1, R, hRp, hRo, hRn3, ?_⟩
      rw [Nat.pow_succ, Nat.mul_comm (3 ^ b) 3, Nat.mul_assoc, ← hQeq]
      omega
    · exact ⟨0, Q, hQ, hQo, hd3, by simp⟩

theorem cancel_mul_mod_of_inv (M a invA x y : Nat)
    (hinv : (invA * a) % M = 1) (heq : (a * x) % M = (a * y) % M) :
    x % M = y % M := by
  have h1 : ∀ z : Nat, ((invA % M) * ((a * z) % M)) % M = z % M := by
    intro z
    calc
      ((invA % M) * ((a * z) % M)) % M
          = (invA * (a * z)) % M := (Nat.mul_mod invA (a * z) M).symm
      _ = ((invA * a) * z) % M := by rw [Nat.mul_assoc]
      _ = (((invA * a) % M) * (z % M)) % M := Nat.mul_mod _ _ _
      _ = (1 * (z % M)) % M := by rw [hinv]
      _ = z % M := by rw [Nat.one_mul, Nat.mod_mod]
  have hm := congrArg (fun t => ((invA % M) * t) % M) heq
  rwa [h1 x, h1 y] at hm

theorem pow2_order_exists_mod_odd (Q : Nat) (hQ_gt1 : Q > 1) (hQ_odd : Q % 2 = 1) :
    ∃ d : Nat, d ≥ 1 ∧ (2 ^ d) % Q = 1 := by
  let f : Fin (Q + 1) -> Fin Q := fun i => ⟨(2 ^ i.val) % Q, Nat.mod_lt _ (by omega)⟩
  rcases pigeonhole_fin_nat Q (Q + 1) (by omega) f with ⟨i1, i2, hne, hfeq⟩
  have hv_ne : i1.val ≠ i2.val := fun h => hne (Fin.eq_of_val_eq h)
  have hv_eq : (2 ^ i1.val) % Q = (2 ^ i2.val) % Q := congrArg Fin.val hfeq
  let inv2 := (Q + 1) / 2
  have hinv2 : (inv2 * 2) % Q = 1 := by
    have h2 : inv2 * 2 = 1 + 1 * Q := by dsimp [inv2]; omega
    rw [h2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hQ_gt1]
  have hcancel_pow2 : ∀ (k x y : Nat),
      (2 ^ k * x) % Q = (2 ^ k * y) % Q -> x % Q = y % Q := by
    intro k
    induction k with
    | zero => intro x y h; simpa using h
    | succ k' ihk =>
      intro x y h
      have hrew : ∀ z : Nat, 2 ^ (k' + 1) * z = 2 ^ k' * (2 * z) := by
        intro z; rw [Nat.pow_succ, Nat.mul_assoc]
      rw [hrew x, hrew y] at h
      exact cancel_mul_mod_of_inv Q 2 inv2 x y hinv2 (ihk (2 * x) (2 * y) h)
  by_cases hlt : i1.val < i2.val
  · let d := i2.val - i1.val
    refine ⟨d, by dsimp [d]; omega, ?_⟩
    have hexp : i2.val = i1.val + d := by dsimp [d]; omega
    rw [hexp, Nat.pow_add] at hv_eq
    have h1 : (2 ^ i1.val * 1) % Q = (2 ^ i1.val * 2 ^ d) % Q := by
      simpa using hv_eq
    exact (hcancel_pow2 i1.val 1 (2 ^ d) h1).symm.trans (Nat.mod_eq_of_lt hQ_gt1)
  · let d := i1.val - i2.val
    refine ⟨d, by dsimp [d]; omega, ?_⟩
    have hexp : i1.val = i2.val + d := by dsimp [d]; omega
    rw [hexp, Nat.pow_add] at hv_eq
    have h1 : (2 ^ i2.val * 2 ^ d) % Q = (2 ^ i2.val * 1) % Q := by
      simpa using hv_eq
    exact (hcancel_pow2 i2.val (2 ^ d) 1 h1).trans (Nat.mod_eq_of_lt hQ_gt1)

theorem pow_mul_mod_eq_one_of_mod_eq_one (Q base d : Nat) (hQ : Q > 1)
    (hd1 : (base ^ d) % Q = 1) :
    ∀ k : Nat, (base ^ (k * d)) % Q = 1
  | 0 => by simp [Nat.mod_eq_of_lt hQ]
  | k + 1 => by
    rw [Nat.succ_mul, Nat.pow_add, Nat.mul_mod,
        pow_mul_mod_eq_one_of_mod_eq_one Q base d hQ hd1 k, hd1,
        Nat.one_mul, Nat.mod_eq_of_lt hQ]

theorem pow3_dvd_pow2_pow3_add_one :
    ∀ m : Nat, (2 ^ (3 ^ m) + 1) % (3 ^ (m + 1)) = 0
  | 0 => by decide
  | m + 1 => by
    let A := 2 ^ (3 ^ m)
    let M := 3 ^ (m + 1)
    have hA_pos : A ≥ 1 := pow2_pos_nat (3 ^ m)
    have ih := pow3_dvd_pow2_pow3_add_one m
    change (A + 1) % M = 0 at ih
    let q := (A + 1) / M
    have hA1 : A + 1 = M * q := by
      have hdm := (Nat.div_add_mod (A + 1) M).symm
      rw [ih, Nat.add_zero] at hdm; exact hdm
    have hM_div3 : M % 3 = 0 := by dsimp [M]; rw [Nat.pow_succ]; omega
    let B := A - 1
    have hAB : A = B + 1 := by dsimp [B]; omega
    have hB_mod3 : B % 3 = 1 := by
      have hm3 : (A + 1) % 3 = 0 := by rw [hA1, Nat.mul_mod, hM_div3, Nat.zero_mul, Nat.zero_mod]
      omega
    have hcube : A ^ 3 + 1 = (A + 1) * (B * B + B + 1) := by
      rw [hAB]
      calc
        (B + 1) ^ 3 + 1
            = (B + 1) * (B + 1) * (B + 1) + 1 := by
              rw [show (3 : Nat) = 2 + 1 from rfl, Nat.pow_succ, Nat.pow_succ,
                  Nat.pow_one]
        _ = (B + 1 + 1) * (B * B + B + 1) := by
              simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul, ← Nat.mul_assoc]
              omega
    have hfac_mod3 : (B * B + B + 1) % 3 = 0 := by
      have hBB : (B * B) % 3 = 1 := by rw [Nat.mul_mod, hB_mod3]
      rw [Nat.add_mod, Nat.add_mod (B * B), hBB, hB_mod3]
    let k := (B * B + B + 1) / 3
    have hfac_eq : B * B + B + 1 = 3 * k := by dsimp [k]; omega
    have hexp : 2 ^ (3 ^ (m + 1)) = A ^ 3 := by
      dsimp [A]
      rw [Nat.pow_succ 3 m, Nat.pow_mul]
    rw [hexp, hcube, hA1, hfac_eq]
    have hprod : (M * q) * (3 * k) = 3 ^ (m + 2) * (q * k) := by
      have hM3 : M * 3 = 3 ^ (m + 2) := (Nat.pow_succ 3 (m + 1)).symm
      calc
        (M * q) * (3 * k) = M * (q * (3 * k)) := Nat.mul_assoc _ _ _
        _ = M * ((q * 3) * k) := by rw [← Nat.mul_assoc q 3 k]
        _ = M * ((3 * q) * k) := by rw [Nat.mul_comm q 3]
        _ = (M * 3) * (q * k) := by rw [← Nat.mul_assoc M (3 * q) k, ← Nat.mul_assoc M 3 q, Nat.mul_assoc (M * 3)]
        _ = 3 ^ (m + 2) * (q * k) := by rw [hM3]
    rw [hprod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]

def iter3x1Aux : Nat -> Nat -> Nat
  | 0, z => z
  | k + 1, z => 3 * iter3x1Aux k z + 1

theorem iter3x1Aux_closed_form :
    ∀ (k z : Nat), iter3x1Aux k z = 3 ^ k * z + (3 ^ k - 1) / 2
  | 0, z => by simp [iter3x1Aux]
  | k + 1, z => by
    simp only [iter3x1Aux, iter3x1Aux_closed_form k z]
    have hp3_odd : 3 ^ k % 2 = 1 := pow3_odd_nat_sec8 k
    have hp3_pos : 3 ^ k ≥ 1 := pow3_pos_nat k
    have hp3_succ : 3 ^ (k + 1) = 3 * 3 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [Nat.mul_add, ← Nat.mul_assoc 3 (3 ^ k) z, ← hp3_succ]
    omega

theorem injective_fin_periodic_preimage {R : Nat} (_hR : R ≥ 1)
    (f : Fin R -> Fin R)
    (hinj : ∀ x y : Fin R, f x = f y -> x = y)
    (P : Fin R -> Prop)
    (hfwd : ∀ x : Fin R, P x -> P (f x)) :
    ∀ x : Fin R, P (f x) -> P x := by
  let iterF : Nat -> Fin R -> Fin R :=
    fun n x => Nat.recOn n x (fun _ acc => f acc)
  have hiter_succ_r : ∀ (n : Nat) (x : Fin R), iterF (n + 1) x = iterF n (f x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n' ih =>
      intro x
      change f (iterF (n' + 1) x) = f (iterF n' (f x))
      rw [ih x]
  have hiter_add : ∀ (a b : Nat) (x : Fin R), iterF (a + b) x = iterF a (iterF b x) := by
    intro a b x
    induction a with
    | zero => rw [Nat.zero_add]; rfl
    | succ a' ih =>
      rw [Nat.succ_add]
      change f (iterF (a' + b) x) = f (iterF a' (iterF b x))
      rw [ih]
  have hiter_P : ∀ (n : Nat) (x : Fin R), P x -> P (iterF n x) := by
    intro n
    induction n with
    | zero => intro x hx; exact hx
    | succ n' ih =>
      intro x hx
      exact hfwd (iterF n' x) (ih x hx)
  have hcancel : ∀ (k : Nat) (x y : Fin R), iterF k x = iterF k y -> x = y := by
    intro k
    induction k with
    | zero => intro x y h; exact h
    | succ k' ih =>
      intro x y h
      rw [hiter_succ_r k' x, hiter_succ_r k' y] at h
      exact hinj x y (ih (f x) (f y) h)
  intro x hPfx
  let g : Fin (R + 1) -> Fin R := fun i => iterF i.val x
  rcases pigeonhole_fin_nat R (R + 1) (by omega) g with ⟨i1, i2, hne, hgeq⟩
  have hv_ne : i1.val ≠ i2.val := fun h => hne (Fin.eq_of_val_eq h)
  dsimp [g] at hgeq
  by_cases hlt : i1.val < i2.val
  · let d := i2.val - i1.val
    have hd_pos : d ≥ 1 := by dsimp [d]; omega
    have hsplit : iterF i2.val x = iterF i1.val (iterF d x) := by
      have hexp : i2.val = i1.val + d := by dsimp [d]; omega
      rw [hexp, hiter_add]
    rw [hsplit] at hgeq
    have hper : x = iterF d x := hcancel i1.val x (iterF d x) hgeq
    have hd_succ : d = (d - 1) + 1 := by omega
    rw [hd_succ, hiter_succ_r (d - 1) x] at hper
    rw [hper]
    exact hiter_P (d - 1) (f x) hPfx
  · let d := i1.val - i2.val
    have hd_pos : d ≥ 1 := by dsimp [d]; omega
    have hsplit : iterF i1.val x = iterF i2.val (iterF d x) := by
      have hexp : i1.val = i2.val + d := by dsimp [d]; omega
      rw [hexp, hiter_add]
    rw [hsplit] at hgeq
    have hper : x = iterF d x := (hcancel i2.val (iterF d x) x hgeq).symm
    have hd_succ : d = (d - 1) + 1 := by omega
    rw [hd_succ, hiter_succ_r (d - 1) x] at hper
    rw [hper]
    exact hiter_P (d - 1) (f x) hPfx

theorem mul_inv_pow_mod_eq_one (R a invA : Nat) (hR : R > 1)
    (h1 : (a * invA) % R = 1) :
    ∀ k : Nat, (a ^ k * invA ^ k) % R = 1
  | 0 => by simp [Nat.mod_eq_of_lt hR]
  | k + 1 => by
    have hprod : a ^ (k + 1) * invA ^ (k + 1) = (a ^ k * invA ^ k) * (a * invA) := by
      rw [Nat.pow_succ a k, Nat.pow_succ invA k]
      calc
        (a ^ k * a) * (invA ^ k * invA)
            = a ^ k * (a * (invA ^ k * invA)) := Nat.mul_assoc _ _ _
        _ = a ^ k * ((a * invA ^ k) * invA) := by rw [← Nat.mul_assoc a (invA ^ k) invA]
        _ = a ^ k * ((invA ^ k * a) * invA) := by rw [Nat.mul_comm a (invA ^ k)]
        _ = (a ^ k * invA ^ k) * (a * invA) := by
              rw [Nat.mul_assoc (invA ^ k) a invA, ← Nat.mul_assoc (a ^ k)]
    rw [hprod, Nat.mul_mod, mul_inv_pow_mod_eq_one R a invA hR h1 k, h1,
        Nat.one_mul, Nat.mod_eq_of_lt hR]

theorem crt_one_of_inv (A B invA x : Nat) (hA : A ≥ 2) (hB : B ≥ 1)
    (hinv : (A * invA) % B = 1 % B)
    (hxA : x % A = 1) (hxB : x % B = 1 % B) :
    x % (A * B) = 1 := by
  let q := x / A
  have hx_eq : x = A * q + 1 := by
    have hdm := (Nat.div_add_mod x A).symm
    rw [hxA] at hdm; exact hdm
  rw [hx_eq] at hxB
  have hAq0 : (A * q) % B = 0 :=
    add_right_cancel_mod_sec9 B (A * q) 0 1 hB (by simpa using hxB)
  have hqB : q % B = 0 := by
    by_cases hB1 : B = 1
    · subst hB1; exact Nat.mod_one q
    · have hB_gt1 : B > 1 := by omega
      have hinv1 : (invA * A) % B = 1 := by
        rw [Nat.mul_comm invA A, hinv, Nat.mod_eq_of_lt hB_gt1]
      have hmod0 : (A * q) % B = (A * 0) % B := by rw [hAq0, Nat.mul_zero, Nat.zero_mod]
      simpa using cancel_mul_mod_of_inv B A invA q 0 hinv1 hmod0
  let k := q / B
  have hq_eq : q = B * k := by
    have hdm := (Nat.div_add_mod q B).symm
    rw [hqB, Nat.add_zero] at hdm; exact hdm
  have hAB_ge2 : A * B ≥ 2 := by
    have hm := Nat.mul_le_mul hA hB
    omega
  rw [hx_eq, hq_eq, ← Nat.mul_assoc A B k, Nat.mul_comm (A * B) k]
  have h1 : 1 + k * (A * B) = k * (A * B) + 1 := Nat.add_comm _ _
  rw [← h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hAB_ge2]

/--
  Theorem W4.2c (`one_sided_presburger_infinite_forward_hits_one`, `[]` axioms):
  Universal One-Sided Infinite Forward-Closed Cobham–Presburger Hitting Theorem:
  Every predicate `I : Nat -> Prop` that is one-sided forward-closed under compressed
  Collatz steps (`∀ x ≥ 1, I x -> I (collatzStep x)`), ultimately periodic above `N0 ≥ 1`
  with ANY period `P ≥ 1` (`∀ x ≥ N0, I x ↔ I (x + P)`), and satisfied by at least one
  integer `x0 ≥ N0` (`∃ x0 ≥ N0, I x0`, i.e., `I` is infinite) MUST contain `1` (`I 1`)!
-/
theorem one_sided_presburger_infinite_forward_hits_one
    (I : Nat -> Prop) (N0 P : Nat)
    (hN0 : N0 ≥ 1) (hP : P ≥ 1)
    (hfwd : IsCollatzForwardClosedPred I)
    (hper : IsPresburgerPeriodicAbove I N0 P)
    (hinf : ∃ x0 : Nat, x0 ≥ N0 ∧ I x0) :
    I 1 := by
  rcases hinf with ⟨x0, hx0_ge, hIx0⟩
  have hv0 : ValidPresburgerMod I N0 P x0 := ⟨x0, hx0_ge, rfl, hIx0⟩
  rcases split_pow2_odd_part P P hP (Nat.le_refl P) with ⟨a, Q, hQ_pos, hQ_odd, hP_eq⟩
  -- Stage A: Reach `ValidPresburgerMod I N0 P (2 ^ a * u0)` for some `u0`:
  have hStageA : ∃ u0 : Nat, ValidPresburgerMod I N0 P (2 ^ a * u0) := by
    cases a with
    | zero => exact ⟨x0, by simpa using hv0⟩
    | succ a' =>
      have hv_rw : ValidPresburgerMod I N0 (2 ^ (a' + 1) * Q) x0 := by rwa [← hP_eq]
      have hper_rw : IsPresburgerPeriodicAbove I N0 (2 ^ (a' + 1) * Q) := by rwa [← hP_eq]
      rcases validPresburgerMod_coset_pow2 I N0 (a' + 1) Q x0 hN0 (by omega) hQ_pos hQ_odd
          hfwd hper_rw hv_rw (a' + 1) (Nat.le_refl _) with ⟨w, hcoset⟩
      let M2 := 2 ^ (a' + 1)
      have hM2_pos : M2 > 0 := pow2_pos_nat (a' + 1)
      rcases hcoset (M2 - w % M2) with ⟨z, hvz, hzm⟩
      rw [Nat.sub_self, Nat.pow_zero, Nat.mul_one] at hzm
      have hw_lt : w % M2 < M2 := Nat.mod_lt w hM2_pos
      have hsum_m : (w + (M2 - w % M2)) % M2 = 0 := by
        have hw_dm := (Nat.div_add_mod w M2).symm
        have hsum : w + (M2 - w % M2) = M2 * (w / M2) + M2 := by omega
        rw [hsum, ← Nat.mul_succ, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
      rw [hsum_m] at hzm
      have hz_eq : z = M2 * (z / M2) := by
        have hdm := (Nat.div_add_mod z M2).symm
        rw [hzm, Nat.add_zero] at hdm; exact hdm
      rw [hP_eq]
      rw [hz_eq] at hvz
      exact ⟨z / M2, hvz⟩
  rcases hStageA with ⟨u0, hu0⟩
  -- Stage B: On `U u := ValidPresburgerMod I N0 P (2 ^ a * u)`, reach `U 1`:
  let U : Nat -> Prop := fun u => ValidPresburgerMod I N0 P (2 ^ a * u)
  have hU_congr : ∀ u1 u2 : Nat, u1 % Q = u2 % Q -> U u1 -> U u2 := by
    intro u1 u2 hm hu1
    apply validPresburgerMod_congr I N0 P (2 ^ a * u1) (2 ^ a * u2) _ hu1
    rw [hP_eq,
        mul_mod_mul_left_sec9 (2 ^ a) u1 Q (pow2_pos_nat a) hQ_pos,
        mul_mod_mul_left_sec9 (2 ^ a) u2 Q (pow2_pos_nat a) hQ_pos, hm]
  have hU_halve : ∀ v : Nat, U (2 * v) -> U v := by
    intro v huv
    dsimp [U] at huv ⊢
    have heq : 2 ^ a * (2 * v) = 2 * (2 ^ a * v) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc]
    rw [heq] at huv
    exact validPresburgerMod_halve I N0 P (2 ^ a * v) hN0 hP hfwd hper huv
  have hU_dbl : ∀ u : Nat, U u -> U (2 * u) := by
    intro u hu
    by_cases hQ1 : Q = 1
    · exact hU_congr u (2 * u) (by rw [hQ1, Nat.mod_one, Nat.mod_one]) hu
    · have hQ_gt1 : Q > 1 := by omega
      rcases pow2_order_exists_mod_odd Q hQ_gt1 hQ_odd with ⟨d, hd_pos, hd1⟩
      let inv2 := (Q + 1) / 2
      have h2inv : 2 * inv2 = Q + 1 := by dsimp [inv2]; omega
      have hU_inv2 : ∀ w : Nat, U w -> U (inv2 * w) := by
        intro w hw
        have hm : w % Q = (2 * (inv2 * w)) % Q := by
          have heq : 2 * (inv2 * w) = w + w * Q := by
            rw [← Nat.mul_assoc, h2inv, Nat.add_mul, Nat.one_mul, Nat.mul_comm Q w, Nat.add_comm]
          rw [heq, Nat.add_mul_mod_self_right]
        exact hU_halve (inv2 * w) (hU_congr w (2 * (inv2 * w)) hm hw)
      have hU_inv2_iter : ∀ (k w : Nat), U w -> U (inv2 ^ k * w) := by
        intro k
        induction k with
        | zero => intro w hw; simpa using hw
        | succ k' ih =>
          intro w hw
          have hstep := hU_inv2 (inv2 ^ k' * w) (ih w hw)
          rwa [← Nat.mul_assoc, ← Nat.pow_succ'] at hstep
      have hmod1 : (2 * inv2) % Q = 1 := by
        rw [h2inv, show Q + 1 = 1 + 1 * Q by omega,
            Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hQ_gt1]
      have hinv_d : (2 ^ d * inv2 ^ d) % Q = 1 :=
        mul_inv_pow_mod_eq_one Q 2 inv2 hQ_gt1 hmod1 d
      have h1_inv : inv2 ^ d % Q = 1 := by
        calc
          inv2 ^ d % Q = (1 * (inv2 ^ d % Q)) % Q := by rw [Nat.one_mul, Nat.mod_mod]
          _ = ((2 ^ d % Q) * (inv2 ^ d % Q)) % Q := by rw [hd1]
          _ = (2 ^ d * inv2 ^ d) % Q := (Nat.mul_mod _ _ _).symm
          _ = 1 := hinv_d
      have hstep := hU_inv2_iter (d - 1) u hu
      have hm_dbl : (inv2 ^ (d - 1) * u) % Q = (2 * u) % Q := by
        apply cancel_mul_mod_of_inv Q inv2 2 _ _ hmod1
        have hl : (inv2 * (inv2 ^ (d - 1) * u)) % Q = u % Q := by
          have hpow : inv2 * (inv2 ^ (d - 1) * u) = inv2 ^ d * u := by
            rw [← Nat.mul_assoc, ← Nat.pow_succ', show (d - 1).succ = d by omega]
          rw [hpow, Nat.mul_mod, h1_inv, Nat.one_mul, Nat.mod_mod]
        have hr : (inv2 * (2 * u)) % Q = u % Q := by
          have hinv_comm : (inv2 * 2) % Q = 1 := by rw [Nat.mul_comm]; exact hmod1
          rw [← Nat.mul_assoc, Nat.mul_mod (inv2 * 2), hinv_comm, Nat.one_mul, Nat.mod_mod]
        rw [hl, hr]
      exact hU_congr (inv2 ^ (d - 1) * u) (2 * u) hm_dbl hstep
  have hU_pow2 : ∀ (k u : Nat), U u -> U (2 ^ k * u) := by
    intro k
    induction k with
    | zero => intro u hu; simpa using hu
    | succ k' ih =>
      intro u hu
      have hs := hU_dbl (2 ^ k' * u) (ih u hu)
      rwa [← Nat.mul_assoc, ← Nat.pow_succ'] at hs
  have hU_3x1 : ∀ u : Nat, U u -> U (3 * u + 1) := by
    intro u hu
    let K2 := 2 ^ (a + 1)
    have hK2_pos : K2 > 0 := pow2_pos_nat (a + 1)
    have h3Q_odd : (3 * Q) % 2 = 1 := by rw [Nat.mul_mod, hQ_odd]
    rcases odd_mul_surjective_mod_pow2 (a + 1) (3 * Q) (K2 - (3 * u + 1) % K2) h3Q_odd with
      ⟨m, hm_mod⟩
    let u' := u + m * Q
    have hu' : U u' :=
      hU_congr u u' (by dsimp [u']; rw [Nat.add_mul_mod_self_right]) hu
    have h3u'1_div : (3 * u' + 1) % K2 = 0 := by
      have hexp : 3 * u' + 1 = (3 * u + 1) + (3 * Q) * m := by
        dsimp [u']
        rw [Nat.mul_add, ← Nat.mul_assoc 3 m Q, Nat.mul_comm 3 m,
            Nat.mul_assoc m 3 Q, Nat.mul_comm m (3 * Q)]
        omega
      let r := (3 * u + 1) % K2
      have hlt_rem : r < K2 := Nat.mod_lt _ hK2_pos
      have hs : r + (K2 - r) = K2 := by omega
      change ((3 * Q) * m) % K2 = (K2 - r) % K2 at hm_mod
      calc
        (3 * u' + 1) % K2
            = ((3 * u + 1) + (3 * Q) * m) % K2 := by rw [hexp]
        _ = (r + ((3 * Q) * m) % K2) % K2 := Nat.add_mod _ _ _
        _ = (r + (K2 - r) % K2) % K2 := by rw [hm_mod]
        _ = (r % K2 + (K2 - r) % K2) % K2 := by rw [Nat.mod_eq_of_lt hlt_rem]
        _ = (r + (K2 - r)) % K2 := (Nat.add_mod r (K2 - r) K2).symm
        _ = K2 % K2 := by rw [hs]
        _ = 0 := Nat.mod_self K2
    let v := (3 * u' + 1) / K2
    have h3u'1_eq : 3 * u' + 1 = K2 * v := by
      have hdm := (Nat.div_add_mod (3 * u' + 1) K2).symm
      rw [h3u'1_div, Nat.add_zero] at hdm; exact hdm
    have hK2_split : K2 = 2 * 2 ^ a := by
      dsimp [K2]; rw [Nat.pow_succ, Nat.mul_comm]
    have hu'_odd : u' % 2 = 1 := by
      have hev : (3 * u' + 1) % 2 = 0 := by rw [h3u'1_eq, hK2_split, Nat.mul_assoc]; omega
      omega
    have hv_u' : ValidPresburgerMod I N0 P u' :=
      validPresburgerMod_halve_pow2 I N0 P hN0 hP hfwd hper a u' hu'
    have hv_step : ValidPresburgerMod I N0 P (collatzStep u') :=
      validPresburgerMod_collatzStep I N0 P u' hN0 hP hfwd hper hv_u'
    rw [collatzStep_of_odd_nat u' hu'_odd, h3u'1_eq, hK2_split, Nat.mul_assoc,
        Nat.mul_div_right _ (by decide)] at hv_step
    have hUv : U v := hv_step
    have hU_mul : U (K2 * v) := hU_pow2 (a + 1) v hUv
    rw [← h3u'1_eq] at hU_mul
    have hmQ : (3 * u' + 1) % Q = (3 * u + 1) % Q := by
      have hexp : 3 * u' + 1 = (3 * u + 1) + (3 * m) * Q := by
        dsimp [u']; rw [Nat.mul_add, ← Nat.mul_assoc]; omega
      rw [hexp, Nat.add_mul_mod_self_right]
    exact hU_congr (3 * u' + 1) (3 * u + 1) hmQ hU_mul
  have hU_iter3x1 : ∀ (k u : Nat), U u -> U (iter3x1Aux k u) := by
    intro k
    induction k with
    | zero => intro u hu; exact hu
    | succ k' ih => intro u hu; exact hU_3x1 (iter3x1Aux k' u) (ih u hu)
  -- Split `Q = 3 ^ b * R` with `gcd(R, 6) = 1`:
  rcases split_pow3_nondiv3_part Q Q hQ_pos hQ_odd (Nat.le_refl Q) with
    ⟨b, R, hR_pos, hR_odd, hR_nd3, hQ_eq⟩
  let UR : Nat -> Prop := fun r => ∃ u : Nat, U u ∧ u % R = r % R
  have hUR_congr : ∀ r1 r2 : Nat, r1 % R = r2 % R -> UR r1 -> UR r2 := by
    intro r1 r2 hm ⟨u, hu, hum⟩
    exact ⟨u, hu, hum.trans hm⟩
  have hUR_all : ∀ r : Nat, UR r := by
    by_cases hR1 : R = 1
    · intro r; refine ⟨u0, hu0, ?_⟩; rw [hR1, Nat.mod_one, Nat.mod_one]
    · have hR_gt1 : R > 1 := by omega
      let inv2R := (R + 1) / 2
      have h2invR : (2 * inv2R) % R = 1 := by
        have h2 : 2 * inv2R = 1 + 1 * R := by dsimp [inv2R]; omega
        rw [h2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hR_gt1]
      let inv3R := if R % 3 = 1 then (2 * R + 1) / 3 else (R + 1) / 3
      have h3invR : (3 * inv3R) % R = 1 := by
        dsimp [inv3R]
        by_cases h1 : R % 3 = 1
        · simp only [h1, ite_true]
          have h3 : 3 * ((2 * R + 1) / 3) = 1 + 2 * R := by omega
          rw [h3, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hR_gt1]
        · simp only [h1, ite_false]
          have h3 : 3 * ((R + 1) / 3) = 1 + 1 * R := by omega
          rw [h3, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hR_gt1]
      let fA : Fin R -> Fin R := fun x => ⟨(2 * x.val) % R, Nat.mod_lt _ hR_pos⟩
      let fB : Fin R -> Fin R := fun x => ⟨(3 * x.val + 1) % R, Nat.mod_lt _ hR_pos⟩
      have hinjA : ∀ x y : Fin R, fA x = fA y -> x = y := by
        intro x y h
        have hv : (2 * x.val) % R = (2 * y.val) % R := congrArg Fin.val h
        have hinv_c : (inv2R * 2) % R = 1 := by rw [Nat.mul_comm]; exact h2invR
        have heq_m := cancel_mul_mod_of_inv R 2 inv2R x.val y.val hinv_c hv
        rw [Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt] at heq_m
        exact Fin.eq_of_val_eq heq_m
      have hinjB : ∀ x y : Fin R, fB x = fB y -> x = y := by
        intro x y h
        have hv : (3 * x.val + 1) % R = (3 * y.val + 1) % R := congrArg Fin.val h
        have h3eq : (3 * x.val) % R = (3 * y.val) % R :=
          add_right_cancel_mod_sec9 R (3 * x.val) (3 * y.val) 1 hR_pos hv
        have hinv_c : (inv3R * 3) % R = 1 := by rw [Nat.mul_comm]; exact h3invR
        have heq_m := cancel_mul_mod_of_inv R 3 inv3R x.val y.val hinv_c h3eq
        rw [Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt] at heq_m
        exact Fin.eq_of_val_eq heq_m
      have hUR_dbl_fwd : ∀ z : Nat, UR z -> UR (2 * z) := by
        intro z ⟨u, hu, hum⟩
        refine ⟨2 * u, hU_dbl u hu, ?_⟩
        rw [Nat.mul_mod 2 u R, hum, ← Nat.mul_mod]
      have hUR_3x1_fwd : ∀ z : Nat, UR z -> UR (3 * z + 1) := by
        intro z ⟨u, hu, hum⟩
        refine ⟨3 * u + 1, hU_3x1 u hu, ?_⟩
        rw [Nat.add_mod (3 * u), Nat.mul_mod 3 u R, hum, ← Nat.mul_mod, ← Nat.add_mod]
      have hUR_dbl_iff : ∀ z : Nat, UR z ↔ UR (2 * z) := by
        intro z
        refine ⟨hUR_dbl_fwd z, fun h2 => ?_⟩
        let x : Fin R := ⟨z % R, Nat.mod_lt z hR_pos⟩
        have hfx : UR (fA x).val :=
          hUR_congr (2 * z) (fA x).val
            (by dsimp [fA, x]; rw [Nat.mod_mod, Nat.mul_mod 2 (z % R) R, Nat.mod_mod, ← Nat.mul_mod]) h2
        have hx := injective_fin_periodic_preimage hR_pos fA hinjA (fun w => UR w.val)
          (fun w hw => hUR_congr (2 * w.val) (fA w).val (Nat.mod_mod _ _).symm (hUR_dbl_fwd w.val hw)) x hfx
        exact hUR_congr x.val z (Nat.mod_mod z R) hx
      have hUR_3x1_iff : ∀ z : Nat, UR z ↔ UR (3 * z + 1) := by
        intro z
        refine ⟨hUR_3x1_fwd z, fun h3 => ?_⟩
        let x : Fin R := ⟨z % R, Nat.mod_lt z hR_pos⟩
        have hfx : UR (fB x).val :=
          hUR_congr (3 * z + 1) (fB x).val
            (by dsimp [fB, x]; rw [Nat.mod_mod, Nat.add_mod (3 * (z % R)),
                Nat.mul_mod 3 (z % R) R, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]) h3
        have hx := injective_fin_periodic_preimage hR_pos fB hinjB (fun w => UR w.val)
          (fun w hw => hUR_congr (3 * w.val + 1) (fB w).val (Nat.mod_mod _ _).symm (hUR_3x1_fwd w.val hw)) x hfx
        exact hUR_congr x.val z (Nat.mod_mod z R) hx
      have hUR_6z : ∀ z : Nat, UR (6 * z + 1) ↔ UR (6 * z + 2) := by
        intro z
        have h1 : UR z ↔ UR (6 * z + 1) :=
          Iff.trans (hUR_dbl_iff z) (hUR_3x1_iff (2 * z) |>.trans
            ⟨by rw [← Nat.mul_assoc]; exact id, by rw [← Nat.mul_assoc]; exact id⟩)
        have h2 : UR z ↔ UR (6 * z + 2) := by
          have hs := Iff.trans (hUR_3x1_iff z) (hUR_dbl_iff (3 * z + 1))
          have heq : 2 * (3 * z + 1) = 6 * z + 2 := by omega
          rwa [heq] at hs
        exact Iff.trans h1.symm h2
      let inv6R := inv2R * inv3R
      have h6invR : (6 * inv6R) % R = 1 := by
        have hprod : 6 * inv6R = (2 * inv2R) * (3 * inv3R) := by
          dsimp [inv6R]
          calc
            6 * (inv2R * inv3R) = (2 * 3) * (inv2R * inv3R) := rfl
            _ = 2 * (3 * (inv2R * inv3R)) := Nat.mul_assoc _ _ _
            _ = 2 * ((3 * inv2R) * inv3R) := by rw [← Nat.mul_assoc 3 inv2R inv3R]
            _ = 2 * ((inv2R * 3) * inv3R) := by rw [Nat.mul_comm 3 inv2R]
            _ = (2 * inv2R) * (3 * inv3R) := by
                  rw [Nat.mul_assoc inv2R 3 inv3R, ← Nat.mul_assoc 2 inv2R (3 * inv3R)]
        rw [hprod, Nat.mul_mod, h2invR, h3invR, Nat.one_mul, Nat.mod_eq_of_lt hR_gt1]
      have hUR_succ : ∀ w : Nat, UR w ↔ UR (w + 1) := by
        intro w
        let z := inv6R * (w + R - 1)
        have h6z1 : (6 * z + 1) % R = w % R := by
          dsimp [z]
          have hw1 : w + R - 1 + 1 = w + R := by omega
          have hmul : (6 * (inv6R * (w + R - 1))) % R = (w + R - 1) % R := by
            rw [← Nat.mul_assoc, Nat.mul_mod (6 * inv6R), h6invR, Nat.one_mul, Nat.mod_mod]
          rw [Nat.add_mod, hmul, ← Nat.add_mod, hw1, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
        have h6z2 : (6 * z + 2) % R = (w + 1) % R := by
          have heq : 6 * z + 2 = (6 * z + 1) + 1 := by omega
          rw [heq, Nat.add_mod, h6z1, ← Nat.add_mod]
        exact Iff.trans ⟨hUR_congr w (6 * z + 1) h6z1.symm, hUR_congr (6 * z + 1) w h6z1⟩
          (Iff.trans (hUR_6z z)
            ⟨hUR_congr (6 * z + 2) (w + 1) h6z2, hUR_congr (w + 1) (6 * z + 2) h6z2.symm⟩)
      have hUR_0 : UR 0 := by
        have hu0_R : UR u0 := ⟨u0, hu0, rfl⟩
        have hdown : ∀ k : Nat, UR k -> UR 0 := by
          intro k
          induction k with
          | zero => exact id
          | succ k' ih => intro hk; exact ih ((hUR_succ k').mpr hk)
        exact hdown u0 hu0_R
      intro r
      induction r with
      | zero => exact hUR_0
      | succ r' ih => exact (hUR_succ r').mp ih
  have hU1 : U 1 := by
    cases b with
    | zero =>
      have hQ_R : Q = R := by rw [hQ_eq]; simp
      rcases hUR_all 1 with ⟨u, hu, hum⟩
      rw [← hQ_R] at hum
      exact hU_congr u 1 hum hu
    | succ b' =>
      let B3 := 3 ^ (b' + 1)
      have hB3_ge3 : B3 ≥ 3 := by
        dsimp [B3]; rw [Nat.pow_succ]; have hp0 := pow3_pos_nat b'; omega
      let e := 1 + 3 ^ b'
      let cB := (B3 - 1) / 2
      have h2cB : 2 * cB = B3 - 1 := by
        dsimp [cB, B3]
        have ho := pow3_odd_nat_sec8 (b' + 1)
        omega
      have hmod_B3 : (2 ^ e * cB) % B3 = 1 := by
        let A2 := 2 ^ (3 ^ b')
        have he_pow : 2 ^ e * cB = A2 * (2 * cB) := by
          dsimp [e, A2]; rw [Nat.add_comm 1, Nat.pow_succ, Nat.mul_assoc]
        rw [he_pow, h2cB]
        have hdvd := pow3_dvd_pow2_pow3_add_one b'
        change (A2 + 1) % B3 = 0 at hdvd
        have hsum_eq : A2 * (B3 - 1) + (A2 + 1) = 1 + A2 * B3 := by
          rw [Nat.mul_sub_left_distrib, Nat.mul_one]
          have hle_B3 : A2 ≤ A2 * B3 := by
            have hm := Nat.mul_le_mul_left A2 (by omega : 1 ≤ B3)
            simpa using hm
          omega
        have hmod_sum : (A2 * (B3 - 1) + (A2 + 1)) % B3 = (1 + (A2 + 1)) % B3 := by
          rw [hsum_eq, Nat.add_mul_mod_self_right,
              Nat.add_mod 1 (A2 + 1) B3, hdvd, Nat.add_zero, Nat.mod_mod]
        exact (add_right_cancel_mod_sec9 B3 (A2 * (B3 - 1)) 1 (A2 + 1) (by omega) hmod_sum).trans
          (Nat.mod_eq_of_lt (by omega))
      by_cases hR1 : R = 1
      · rcases hUR_all 0 with ⟨u_st, hu_st, _⟩
        let u_fin := 2 ^ e * iter3x1Aux (b' + 1) u_st
        have hU_fin : U u_fin := hU_pow2 e _ (hU_iter3x1 (b' + 1) u_st hu_st)
        have hQ_B3 : Q = B3 := by rw [hQ_eq, hR1, Nat.mul_one]
        have hfin_mod : u_fin % B3 = 1 := by
          dsimp [u_fin]
          rw [iter3x1Aux_closed_form (b' + 1) u_st]
          change (2 ^ e * (B3 * u_st + cB)) % B3 = 1
          rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (2 ^ e) B3, Nat.mul_assoc B3,
              Nat.mul_comm B3 (2 ^ e * u_st), Nat.add_comm, Nat.add_mul_mod_self_right]
          exact hmod_B3
        rw [← hQ_B3] at hfin_mod
        exact hU_congr u_fin 1 (hfin_mod.trans (Nat.mod_eq_of_lt (by omega)).symm) hU_fin
      · have hR_gt1 : R > 1 := by omega
        let inv2R := (R + 1) / 2
        have h2invR : (2 * inv2R) % R = 1 := by
          have h2 : 2 * inv2R = 1 + 1 * R := by dsimp [inv2R]; omega
          rw [h2, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hR_gt1]
        let inv3R := if R % 3 = 1 then (2 * R + 1) / 3 else (R + 1) / 3
        have h3invR : (3 * inv3R) % R = 1 := by
          dsimp [inv3R]
          by_cases h1 : R % 3 = 1
          · simp only [h1, ite_true]
            have h3 : 3 * ((2 * R + 1) / 3) = 1 + 2 * R := by omega
            rw [h3, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hR_gt1]
          · simp only [h1, ite_false]
            have h3 : 3 * ((R + 1) / 3) = 1 + 1 * R := by omega
            rw [h3, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hR_gt1]
        let invB3 := inv3R ^ (b' + 1)
        have hB3inv : (B3 * invB3) % R = 1 :=
          mul_inv_pow_mod_eq_one R 3 inv3R hR_gt1 h3invR (b' + 1)
        let inv2e := inv2R ^ e
        have h2einv : (2 ^ e * inv2e) % R = 1 :=
          mul_inv_pow_mod_eq_one R 2 inv2R hR_gt1 h2invR e
        let target_r := invB3 * (inv2e + (R - cB % R))
        rcases hUR_all target_r with ⟨u_st, hu_st, hu_st_mod⟩
        let u_fin := 2 ^ e * iter3x1Aux (b' + 1) u_st
        have hU_fin : U u_fin := hU_pow2 e _ (hU_iter3x1 (b' + 1) u_st hu_st)
        have hfin_B3 : u_fin % B3 = 1 := by
          dsimp [u_fin]
          rw [iter3x1Aux_closed_form (b' + 1) u_st]
          change (2 ^ e * (B3 * u_st + cB)) % B3 = 1
          rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (2 ^ e) B3, Nat.mul_assoc B3,
              Nat.mul_comm B3 (2 ^ e * u_st), Nat.add_comm, Nat.add_mul_mod_self_right]
          exact hmod_B3
        have hfin_R : u_fin % R = 1 % R := by
          rw [Nat.mod_eq_of_lt hR_gt1]
          dsimp [u_fin]
          rw [iter3x1Aux_closed_form (b' + 1) u_st]
          change (2 ^ e * (B3 * u_st + cB)) % R = 1
          have hiter_R : (B3 * u_st + cB) % R = inv2e % R := by
            have hmul_B3 : (B3 * u_st) % R = (inv2e + (R - cB % R)) % R := by
              calc
                (B3 * u_st) % R = ((B3 % R) * (u_st % R)) % R := Nat.mul_mod _ _ _
                _ = ((B3 % R) * (target_r % R)) % R := by rw [hu_st_mod]
                _ = (B3 * target_r) % R := (Nat.mul_mod _ _ _).symm
                _ = ((B3 * invB3) * (inv2e + (R - cB % R))) % R := by
                      dsimp [target_r]; rw [Nat.mul_assoc]
                _ = (((B3 * invB3) % R) * ((inv2e + (R - cB % R)) % R)) % R := Nat.mul_mod _ _ _
                _ = (inv2e + (R - cB % R)) % R := by rw [hB3inv, Nat.one_mul, Nat.mod_mod]
            have hcB_lt : cB % R < R := Nat.mod_lt cB hR_pos
            have hsum_R : (inv2e + (R - cB % R) + cB % R) % R = inv2e % R := by
              have hs : inv2e + (R - cB % R) + cB % R = inv2e + 1 * R := by omega
              rw [hs, Nat.add_mul_mod_self_right]
            rw [Nat.add_mod, hmul_B3, Nat.mod_add_mod, hsum_R]
          rw [Nat.mul_mod, hiter_R, ← Nat.mul_mod, h2einv]
        have hcrt := crt_one_of_inv B3 R invB3 u_fin (by omega) hR_pos
          (by rw [Nat.mod_eq_of_lt hR_gt1]; exact hB3inv) hfin_B3 hfin_R
        rw [← hQ_eq] at hcrt
        have hQ_gt1 : Q > 1 := by
          have hm : 3 ≤ B3 * R := by simpa using Nat.mul_le_mul hB3_ge3 hR_pos
          have hgt : B3 * R > 1 := by omega
          rwa [hQ_eq]
        exact hU_congr u_fin 1 (hcrt.trans (Nat.mod_eq_of_lt hQ_gt1).symm) hU_fin
  -- Finally, extract an explicit power of two `2 ^ M ≥ N0` with `(2 ^ M) % P = (2 ^ a) % P`
  -- and walk `2 ^ M -> 2 ^ (M - 1) -> ... -> 1`:
  have hv_2a : ValidPresburgerMod I N0 P (2 ^ a) := by
    have h := hU1; dsimp [U] at h; rwa [Nat.mul_one] at h
  rcases hv_2a with ⟨x_hit, hx_hit_ge, hx_hit_mod, hIx_hit⟩
  have hpow2_hit : ∃ M : Nat, 2 ^ M ≥ N0 ∧ (2 ^ M) % P = (2 ^ a) % P := by
    by_cases hQ1 : Q = 1
    · refine ⟨a + N0, ?_, ?_⟩
      · have hp := pow2_ge_succ_self (a + N0); omega
      · have hP2a : P = 2 ^ a := by rw [hP_eq, hQ1, Nat.mul_one]
        rw [hP2a, Nat.pow_add, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
    · have hQ_gt1 : Q > 1 := by omega
      rcases pow2_order_exists_mod_odd Q hQ_gt1 hQ_odd with ⟨d, hd_pos, hd1⟩
      let M := a + N0 * d
      refine ⟨M, ?_, ?_⟩
      · have hM_ge : M ≥ N0 := by
          dsimp [M]; have hm := Nat.mul_le_mul_left N0 hd_pos; omega
        have hp := pow2_ge_succ_self M; omega
      · have hmQ : (2 ^ (N0 * d)) % Q = 1 % Q := by
          rw [pow_mul_mod_eq_one_of_mod_eq_one Q 2 d hQ_gt1 hd1 N0, Nat.mod_eq_of_lt hQ_gt1]
        dsimp [M]
        rw [hP_eq, Nat.pow_add,
            mul_mod_mul_left_sec9 (2 ^ a) (2 ^ (N0 * d)) Q (pow2_pos_nat a) hQ_pos,
            hmQ, ← mul_mod_mul_left_sec9 (2 ^ a) 1 Q (pow2_pos_nat a) hQ_pos, Nat.mul_one]
  rcases hpow2_hit with ⟨M, h2M_ge, h2M_mod⟩
  have hI_2M : I (2 ^ M) :=
    (presburger_periodic_same_mod I N0 P x_hit (2 ^ M) hper hx_hit_ge h2M_ge
      (hx_hit_mod.trans h2M_mod.symm)).mp hIx_hit
  have hwalk_pow2 : ∀ m : Nat, I (2 ^ m) -> I 1 := by
    intro m
    induction m with
    | zero => exact id
    | succ m' ih =>
      intro hm'
      have heq : 2 ^ (m' + 1) = 2 * 2 ^ m' := by rw [Nat.pow_succ, Nat.mul_comm]
      have hpos : 2 * 2 ^ m' ≥ 1 := by have hp := pow2_pos_nat m'; omega
      rw [heq] at hm'
      have hs := hfwd (2 * 2 ^ m') hpos hm'
      rw [collatzStep_double_pos (2 ^ m')] at hs
      exact ih hs
  exact hwalk_pow2 M hI_2M

/--
  Corollary W4.2d (`no_one_sided_presburger_divergent_certificate`, `[]` axioms):
  No one-sided forward-closed Presburger / semilinear invariant `I` can separate an
  unbounded/divergent positive orbit (`∀ B, ∃ k, collatzIter k xStart ≥ B`) from `1`.
-/
theorem no_one_sided_presburger_divergent_certificate
    (I : Nat -> Prop) (N0 P xStart : Nat)
    (hN0 : N0 ≥ 1) (hP : P ≥ 1) (hxStart : xStart ≥ 1)
    (hfwd : IsCollatzForwardClosedPred I)
    (hper : IsPresburgerPeriodicAbove I N0 P)
    (hStart : I xStart)
    (hunbounded : ∃ k : Nat, collatzIter k xStart ≥ N0) :
    I 1 := by
  rcases hunbounded with ⟨k, hk_ge⟩
  have hiter_pos_and_I : ∀ (j y : Nat), y ≥ 1 -> I y -> collatzIter j y ≥ 1 ∧ I (collatzIter j y) := by
    intro j
    induction j with
    | zero => intro y hy hIy; exact ⟨hy, hIy⟩
    | succ j' ih =>
      intro y hy hIy
      have hstep_pos : collatzStep y ≥ 1 := by
        unfold collatzStep
        cases hb : (y % 2 == 0) with
        | true =>
          have hev : y % 2 = 0 := of_decide_eq_true hb
          simp only [ite_true]; omega
        | false =>
          have hodd : y % 2 ≠ 0 := of_decide_eq_false hb
          simp only [Bool.false_eq_true, ite_false]; omega
      exact ih (collatzStep y) hstep_pos (hfwd y hy hIy)
  have hIk := (hiter_pos_and_I k xStart hxStart hStart).2
  exact one_sided_presburger_infinite_forward_hits_one I N0 P hN0 hP hfwd hper
    ⟨collatzIter k xStart, hk_ge, hIk⟩

-- ============================================================================
-- SECTION 3: Branch P3 — Carry-Coupled 2-Block Resultant Elimination &
--            Mersenne Quotient GCD / Mod-3 Parity Lock (`[]` Axioms)
-- ============================================================================

/--
  Theorem W4.3a (`two_block_brox_resultant_identities`, `[]` axioms):
  Exact elimination of `(2^a2 - 1)` and `(2^a1 - 1)` between the 2-block Brox
  carries `H0 = twoBlockBroxCarry w1 a1 w2 a2`, `H1 = twoBlockBroxCarry w2 a2 w1 a1`,
  and the positive cycle determinant `D = 2^(w1 + a1 + w2 + a2) - 3^(w1 + w2)`.
-/
theorem two_block_brox_resultant_identities (w1 a1 w2 a2 : Nat)
    (ha1 : a1 ≥ 1) (ha2 : a2 ≥ 1)
    (hgt : 3 ^ (w1 + w2) < 2 ^ (w1 + a1 + w2 + a2)) :
    let D := 2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)
    let H0 := twoBlockBroxCarry w1 a1 w2 a2
    let H1 := twoBlockBroxCarry w2 a2 w1 a1
    2 ^ (a1 + w2) * H1 = 3 ^ w1 * H0 + D * (2 ^ a1 - 1) ∧
    2 ^ (a2 + w1) * H0 = 3 ^ w2 * H1 + D * (2 ^ a2 - 1) := by
  dsimp only [twoBlockBroxCarry]
  have hp2_a1 : 2 ^ a1 ≥ 2 := by
    rw [pow2_split_pred a1 ha1]
    have hp0 := pow2_pos_nat (a1 - 1)
    omega
  have hp2_a2 : 2 ^ a2 ≥ 2 := by
    rw [pow2_split_pred a2 ha2]
    have hp0 := pow2_pos_nat (a2 - 1)
    omega
  have hp3_sum : 3 ^ (w1 + w2) = 3 ^ w1 * 3 ^ w2 := Nat.pow_add 3 w1 w2
  have hp2_sum1 : 2 ^ (w1 + a1 + w2 + a2) = 2 ^ (a1 + w2) * 2 ^ (a2 + w1) := by
    rw [← Nat.pow_add]
    have hex : w1 + a1 + w2 + a2 = (a1 + w2) + (a2 + w1) := by omega
    rw [hex]
  refine ⟨?_, ?_⟩
  · calc
      2 ^ (a1 + w2) * (3 ^ w1 * (2 ^ a2 - 1) + 2 ^ (a2 + w1) * (2 ^ a1 - 1))
          = 2 ^ (a1 + w2) * (3 ^ w1 * (2 ^ a2 - 1)) +
              (2 ^ (a1 + w2) * 2 ^ (a2 + w1)) * (2 ^ a1 - 1) := by
            rw [Nat.mul_add, Nat.mul_assoc]
      _ = 3 ^ w1 * (2 ^ (a1 + w2) * (2 ^ a2 - 1)) +
              2 ^ (w1 + a1 + w2 + a2) * (2 ^ a1 - 1) := by
            rw [← Nat.mul_assoc (2 ^ (a1 + w2)) (3 ^ w1),
                Nat.mul_comm (2 ^ (a1 + w2)) (3 ^ w1), Nat.mul_assoc, ← hp2_sum1]
      _ = 3 ^ w1 * (2 ^ (a1 + w2) * (2 ^ a2 - 1)) +
              (3 ^ (w1 + w2) + (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2))) * (2 ^ a1 - 1) := by
            have hsub : 3 ^ (w1 + w2) + (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)) =
                2 ^ (w1 + a1 + w2 + a2) := by omega
            rw [hsub]
      _ = 3 ^ w1 * (3 ^ w2 * (2 ^ a1 - 1) + 2 ^ (a1 + w2) * (2 ^ a2 - 1)) +
              (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)) * (2 ^ a1 - 1) := by
            rw [Nat.add_mul, hp3_sum, Nat.mul_assoc (3 ^ w1) (3 ^ w2), Nat.mul_add]
            omega
  · calc
      2 ^ (a2 + w1) * (3 ^ w2 * (2 ^ a1 - 1) + 2 ^ (a1 + w2) * (2 ^ a2 - 1))
          = 2 ^ (a2 + w1) * (3 ^ w2 * (2 ^ a1 - 1)) +
              (2 ^ (a1 + w2) * 2 ^ (a2 + w1)) * (2 ^ a2 - 1) := by
            rw [Nat.mul_add, ← Nat.mul_assoc (2 ^ (a2 + w1)) (2 ^ (a1 + w2)),
                Nat.mul_comm (2 ^ (a2 + w1)) (2 ^ (a1 + w2))]
      _ = 3 ^ w2 * (2 ^ (a2 + w1) * (2 ^ a1 - 1)) +
              2 ^ (w1 + a1 + w2 + a2) * (2 ^ a2 - 1) := by
            rw [← Nat.mul_assoc (2 ^ (a2 + w1)) (3 ^ w2),
                Nat.mul_comm (2 ^ (a2 + w1)) (3 ^ w2), Nat.mul_assoc, ← hp2_sum1]
      _ = 3 ^ w2 * (2 ^ (a2 + w1) * (2 ^ a1 - 1)) +
              (3 ^ (w1 + w2) + (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2))) * (2 ^ a2 - 1) := by
            have hsub : 3 ^ (w1 + w2) + (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)) =
                2 ^ (w1 + a1 + w2 + a2) := by omega
            rw [hsub]
      _ = 3 ^ w2 * (3 ^ w1 * (2 ^ a2 - 1) + 2 ^ (a2 + w1) * (2 ^ a1 - 1)) +
              (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)) * (2 ^ a2 - 1) := by
            rw [Nat.add_mul, hp3_sum, Nat.mul_comm (3 ^ w1) (3 ^ w2),
                Nat.mul_assoc (3 ^ w2) (3 ^ w1), Nat.mul_add]
            omega

theorem pow2_sub_one_div3_iff_even : ∀ a : Nat,
    ((2 ^ a - 1) % 3 = 0 -> a % 2 = 0)
  | 0 => fun _ => rfl
  | 1 => fun h => by omega
  | a + 2 => fun h => by
    have hp : 2 ^ (a + 2) = 4 * 2 ^ a := by
      rw [Nat.pow_succ, Nat.pow_succ]
      omega
    have hp0 := pow2_pos_nat a
    have hrem : (2 ^ a - 1) % 3 = 0 := by omega
    have ih := pow2_sub_one_div3_iff_even a hrem
    omega

/--
  Theorem W4.3b (`two_block_quotient_mersenne_gcd_and_mod3_lock`, `[]` axioms):
  Unconditional Forward Diophantine Quotient-GCD & Mod-3 Exponent-Parity Lock
  for 2-Block Positive Collatz Cycles:
  Whenever `D * q0 = H0` and `D * q1 = H1` (`D = 2^K - 3^W > 0`),
  1. `2^(a1 + w2) * q1 = 3^w1 * q0 + (2^a1 - 1)` and `2^(a2 + w1) * q0 = 3^w2 * q1 + (2^a2 - 1)`;
  2. `Nat.gcd q0 q1 ∣ Nat.gcd (2^a1 - 1) (2^a2 - 1)` (so `a1 = 1 ∨ a2 = 1 -> Nat.gcd q0 q1 = 1`);
  3. `q0 % 3 = 0 -> a2 % 2 = 0` and `q1 % 3 = 0 -> a1 % 2 = 0`.
-/
theorem two_block_quotient_mersenne_gcd_and_mod3_lock
    (w1 a1 w2 a2 q0 q1 : Nat)
    (hw1 : w1 ≥ 1) (ha1 : a1 ≥ 1) (hw2 : w2 ≥ 1) (ha2 : a2 ≥ 1)
    (hgt : 3 ^ (w1 + w2) < 2 ^ (w1 + a1 + w2 + a2))
    (hq0 : (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)) * q0 = twoBlockBroxCarry w1 a1 w2 a2)
    (hq1 : (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)) * q1 = twoBlockBroxCarry w2 a2 w1 a1) :
    2 ^ (a1 + w2) * q1 = 3 ^ w1 * q0 + (2 ^ a1 - 1) ∧
    2 ^ (a2 + w1) * q0 = 3 ^ w2 * q1 + (2 ^ a2 - 1) ∧
    Nat.gcd q0 q1 ∣ Nat.gcd (2 ^ a1 - 1) (2 ^ a2 - 1) ∧
    ((a1 = 1 ∨ a2 = 1) -> Nat.gcd q0 q1 = 1) ∧
    (q0 % 3 = 0 -> a2 % 2 = 0) ∧
    (q1 % 3 = 0 -> a1 % 2 = 0) := by
  let D := 2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)
  have hD_pos : D > 0 := by dsimp [D]; omega
  rcases two_block_brox_resultant_identities w1 a1 w2 a2 ha1 ha2 hgt with ⟨hr1, hr2⟩
  rw [← hq0, ← hq1] at hr1 hr2
  have hmul1 : D * (2 ^ (a1 + w2) * q1) = D * (3 ^ w1 * q0 + (2 ^ a1 - 1)) := by
    calc
      D * (2 ^ (a1 + w2) * q1)
          = 2 ^ (a1 + w2) * (D * q1) := by
            rw [← Nat.mul_assoc, Nat.mul_comm D (2 ^ (a1 + w2)), Nat.mul_assoc]
      _ = 3 ^ w1 * (D * q0) + D * (2 ^ a1 - 1) := hr1
      _ = D * (3 ^ w1 * q0) + D * (2 ^ a1 - 1) := by
            rw [← Nat.mul_assoc (3 ^ w1) D q0, Nat.mul_comm (3 ^ w1) D, Nat.mul_assoc]
      _ = D * (3 ^ w1 * q0 + (2 ^ a1 - 1)) := by rw [← Nat.mul_add]
  have hmul2 : D * (2 ^ (a2 + w1) * q0) = D * (3 ^ w2 * q1 + (2 ^ a2 - 1)) := by
    calc
      D * (2 ^ (a2 + w1) * q0)
          = 2 ^ (a2 + w1) * (D * q0) := by
            rw [← Nat.mul_assoc, Nat.mul_comm D (2 ^ (a2 + w1)), Nat.mul_assoc]
      _ = 3 ^ w2 * (D * q1) + D * (2 ^ a2 - 1) := hr2
      _ = D * (3 ^ w2 * q1) + D * (2 ^ a2 - 1) := by
            rw [← Nat.mul_assoc (3 ^ w2) D q1, Nat.mul_comm (3 ^ w2) D, Nat.mul_assoc]
      _ = D * (3 ^ w2 * q1 + (2 ^ a2 - 1)) := by rw [← Nat.mul_add]
  have heq1 : 2 ^ (a1 + w2) * q1 = 3 ^ w1 * q0 + (2 ^ a1 - 1) :=
    nat_mul_left_cancel_pos D _ _ hD_pos hmul1
  have heq2 : 2 ^ (a2 + w1) * q0 = 3 ^ w2 * q1 + (2 ^ a2 - 1) :=
    nat_mul_left_cancel_pos D _ _ hD_pos hmul2
  let g := Nat.gcd q0 q1
  have hg0 : g ∣ q0 := Nat.gcd_dvd_left q0 q1
  have hg1 : g ∣ q1 := Nat.gcd_dvd_right q0 q1
  have hdvd_a1 : g ∣ (2 ^ a1 - 1) := by
    have hsub : 2 ^ a1 - 1 = 2 ^ (a1 + w2) * q1 - 3 ^ w1 * q0 := by omega
    rw [hsub]
    apply Nat.dvd_sub
    · rcases hg1 with ⟨k1, hk1⟩
      exact ⟨2 ^ (a1 + w2) * k1, by rw [hk1, ← Nat.mul_assoc, Nat.mul_comm (2 ^ (a1 + w2)) g, Nat.mul_assoc]⟩
    · rcases hg0 with ⟨k0, hk0⟩
      exact ⟨3 ^ w1 * k0, by rw [hk0, ← Nat.mul_assoc, Nat.mul_comm (3 ^ w1) g, Nat.mul_assoc]⟩
  have hdvd_a2 : g ∣ (2 ^ a2 - 1) := by
    have hsub : 2 ^ a2 - 1 = 2 ^ (a2 + w1) * q0 - 3 ^ w2 * q1 := by omega
    rw [hsub]
    apply Nat.dvd_sub
    · rcases hg0 with ⟨k0, hk0⟩
      exact ⟨2 ^ (a2 + w1) * k0, by rw [hk0, ← Nat.mul_assoc, Nat.mul_comm (2 ^ (a2 + w1)) g, Nat.mul_assoc]⟩
    · rcases hg1 with ⟨k1, hk1⟩
      exact ⟨3 ^ w2 * k1, by rw [hk1, ← Nat.mul_assoc, Nat.mul_comm (3 ^ w2) g, Nat.mul_assoc]⟩
  have hg_both : g ∣ Nat.gcd (2 ^ a1 - 1) (2 ^ a2 - 1) := Nat.dvd_gcd hdvd_a1 hdvd_a2
  have hunit : (a1 = 1 ∨ a2 = 1) -> g = 1 := by
    intro hor
    rcases hor with rfl | rfl
    · simp only [Nat.pow_one] at hdvd_a1
      exact Nat.eq_one_of_dvd_one hdvd_a1
    · simp only [Nat.pow_one] at hdvd_a2
      exact Nat.eq_one_of_dvd_one hdvd_a2
  have hmod3_q0 : q0 % 3 = 0 -> a2 % 2 = 0 := by
    intro hq0_3
    have hp3_w2 : (3 ^ w2) % 3 = 0 := by
      cases w2 with
      | zero => omega
      | succ w2' => rw [Nat.pow_succ]; omega
    have hlhs3 : (2 ^ (a2 + w1) * q0) % 3 = 0 := by
      rw [Nat.mul_mod, hq0_3, Nat.mul_zero, Nat.zero_mod]
    have hrhs3 : (3 ^ w2 * q1) % 3 = 0 := by
      rw [Nat.mul_mod, hp3_w2, Nat.zero_mul, Nat.zero_mod]
    have ha2_3 : (2 ^ a2 - 1) % 3 = 0 := by
      have hmod := congrArg (fun z => z % 3) heq2
      rw [hlhs3, Nat.add_mod, hrhs3, Nat.zero_add, Nat.mod_mod] at hmod
      exact hmod.symm
    exact pow2_sub_one_div3_iff_even a2 ha2_3
  have hmod3_q1 : q1 % 3 = 0 -> a1 % 2 = 0 := by
    intro hq1_3
    have hp3_w1 : (3 ^ w1) % 3 = 0 := by
      cases w1 with
      | zero => omega
      | succ w1' => rw [Nat.pow_succ]; omega
    have hlhs3 : (2 ^ (a1 + w2) * q1) % 3 = 0 := by
      rw [Nat.mul_mod, hq1_3, Nat.mul_zero, Nat.zero_mod]
    have hrhs3 : (3 ^ w1 * q0) % 3 = 0 := by
      rw [Nat.mul_mod, hp3_w1, Nat.zero_mul, Nat.zero_mod]
    have ha1_3 : (2 ^ a1 - 1) % 3 = 0 := by
      have hmod := congrArg (fun z => z % 3) heq1
      rw [hlhs3, Nat.add_mod, hrhs3, Nat.zero_add, Nat.mod_mod] at hmod
      exact hmod.symm
    exact pow2_sub_one_div3_iff_even a1 ha1_3
  exact ⟨heq1, heq2, hg_both, hunit, hmod3_q0, hmod3_q1⟩

-- ============================================================================
-- SECTION 4: Branch P5 — Solvable Mixed-(2,3) Cousin Benchmark `T_diamond`,
--            DFA & Mod-`2^A * 3^B` Barriers, Counter-Model Separation, &
--            Global Convergence via Evolved Nonlocal Invariant `Φ_diamond`
-- ============================================================================

/--
  Non-trivial solvable mixed-(2,3) Collatz cousin `T_diamond` on `Nat`:
  - Odd `x`: `(3 * x + 1) / 2` (100% identical to compressed Collatz on all odd `x`!)
  - Even `x > 2` with `x % 6 = 2`: `(x - 2) / 3`
  - All other even `x` (`x % 6 ∈ {0, 4}` or `x ≤ 2`): `x / 2`
-/
def cousinDiamondStep (x : Nat) : Nat :=
  if x % 2 = 1 then (3 * x + 1) / 2
  else if x > 2 ∧ x % 6 = 2 then (x - 2) / 3
  else x / 2

def cousinDiamondIter : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamondIter k (cousinDiamondStep x)

/-- Signed extension of `T_diamond` to `Int` (for Counter-Model `M2 = Z^-`) -/
def cousinDiamondStepInt (x : Int) : Int :=
  if x % 2 ≠ 0 then (3 * x + 1) / 2
  else if x > 2 ∧ x % 6 = 2 then (x - 2) / 3
  else x / 2

def cousinDiamondIterInt : Nat -> Int -> Int
  | 0, x => x
  | k + 1, x => cousinDiamondIterInt k (cousinDiamondStepInt x)

/-- Fuel-bounded structural 3-adic core stripping `3^{v_3(n)}` from `n > 0` (`[]` axioms) -/
def core3Aux : Nat -> Nat -> Nat
  | 0, n => n
  | fuel + 1, n =>
    if n > 0 ∧ n % 3 = 0 then core3Aux fuel (n / 3) else n

def core3 (n : Nat) : Nat :=
  core3Aux n n

/--
  Evolutionarily synthesized nonlocal 3-adic valuation Lyapunov invariant:
    `Φ_diamond(x) := core3(x + 1)^2 * (x + 1)`.
-/
def cousinDiamondPhi (x : Nat) : Nat :=
  let c := core3 (x + 1)
  c * c * (x + 1)

theorem core3Aux_eq_of_ge :
    ∀ (f1 f2 n : Nat), n ≤ f1 -> n ≤ f2 -> core3Aux f1 n = core3Aux f2 n
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, n, h1, _ => by
    have hn0 : n = 0 := by omega
    subst hn0
    rfl
  | _ + 1, 0, n, _, h2 => by
    have hn0 : n = 0 := by omega
    subst hn0
    rfl
  | f1 + 1, f2 + 1, n, h1, h2 => by
    simp only [core3Aux]
    by_cases hc : n > 0 ∧ n % 3 = 0
    · simp only [hc, and_self, ite_true]
      exact core3Aux_eq_of_ge f1 f2 (n / 3) (by omega) (by omega)
    · simp only [hc, ite_false]

theorem core3_mul3 (m : Nat) (hm : m > 0) :
    core3 (3 * m) = core3 m := by
  unfold core3
  cases hfuel : 3 * m with
  | zero => omega
  | succ f =>
    have hm_eq : 3 * m = f + 1 := hfuel
    have hc : f + 1 > 0 ∧ (f + 1) % 3 = 0 := by omega
    simp only [core3Aux, hc, and_self, ite_true]
    have hdiv : (f + 1) / 3 = m := by omega
    rw [hdiv]
    exact core3Aux_eq_of_ge f m m (by omega) (by omega)

theorem core3_not_div3 (n : Nat) (hnd : n % 3 ≠ 0) :
    core3 n = n := by
  unfold core3
  cases n with
  | zero => omega
  | succ m =>
    have hnc : ¬ (m + 1 > 0 ∧ (m + 1) % 3 = 0) := fun hc => hnd hc.2
    simp only [core3Aux, hnc, ite_false]

theorem core3_mul2_aux :
    ∀ (bound m : Nat), m > 0 -> m ≤ bound -> core3 (2 * m) = 2 * core3 m
  | 0, _, hm, hle => by omega
  | bound + 1, m, hm, hle => by
    by_cases hd3 : m % 3 = 0
    · let k := m / 3
      have hk_pos : k > 0 := by dsimp [k]; omega
      have hm_eq : m = 3 * k := by dsimp [k]; omega
      have h23 : 2 * (3 * k) = 3 * (2 * k) := by omega
      rw [hm_eq, h23, core3_mul3 (2 * k) (by omega), core3_mul3 k hk_pos]
      exact core3_mul2_aux bound k hk_pos (by dsimp [k]; omega)
    · have h2nd : (2 * m) % 3 ≠ 0 := by omega
      rw [core3_not_div3 (2 * m) h2nd, core3_not_div3 m hd3]

theorem core3_mul2 (m : Nat) (hm : m > 0) :
    core3 (2 * m) = 2 * core3 m :=
  core3_mul2_aux m m hm (by omega)

theorem core3_bounds_aux :
    ∀ (bound n : Nat), n > 0 -> n ≤ bound -> 1 ≤ core3 n ∧ core3 n ≤ n
  | 0, _, hn, hle => by omega
  | bound + 1, n, hn, hle => by
    by_cases hd3 : n % 3 = 0
    · let k := n / 3
      have hk_pos : k > 0 := by dsimp [k]; omega
      have hn_eq : n = 3 * k := by dsimp [k]; omega
      rw [hn_eq, core3_mul3 k hk_pos]
      rcases core3_bounds_aux bound k hk_pos (by dsimp [k]; omega) with ⟨h1, h2⟩
      exact ⟨h1, by omega⟩
    · rw [core3_not_div3 n hd3]
      exact ⟨by omega, by omega⟩

theorem core3_pos_and_le (n : Nat) (hn : n > 0) :
    1 ≤ core3 n ∧ core3 n ≤ n :=
  core3_bounds_aux n n hn (by omega)

theorem nat_cube_strict_mono (a b : Nat) (hlt : a < b) :
    a * a * a < b * b * b := by
  have hab1 : a + 1 ≤ b := by omega
  have hb_pos : b ≥ 1 := by omega
  have hsq : a * a < b * b := by
    have h1 : a * a ≤ a * b := Nat.mul_le_mul_left a (by omega)
    have h2 : a * b < b * b := by
      have hm : (a + 1) * b ≤ b * b := Nat.mul_le_mul_right b hab1
      rw [Nat.add_mul, Nat.one_mul] at hm
      omega
    omega
  have h3 : a * a * a ≤ b * b * a := Nat.mul_le_mul_right a (by omega)
  have h4 : b * b * a < b * b * b := by
    have hbb_pos : b * b ≥ 1 := Nat.mul_le_mul hb_pos hb_pos
    have hm : b * b * (a + 1) ≤ b * b * b := Nat.mul_le_mul_left (b * b) hab1
    rw [Nat.mul_add, Nat.mul_one] at hm
    omega
  omega

theorem cousinDiamondStep_odd (x : Nat) (hodd : x % 2 = 1) :
    cousinDiamondStep x = (3 * x + 1) / 2 := by
  unfold cousinDiamondStep
  simp only [hodd, ite_true]

theorem cousinDiamondStep_even_mod6_2 (x : Nat) (hgt2 : x > 2) (h6 : x % 6 = 2) :
    cousinDiamondStep x = (x - 2) / 3 := by
  unfold cousinDiamondStep
  have hno : ¬ (x % 2 = 1) := by omega
  simp only [hno, hgt2, h6, and_self, ite_true, ite_false]

theorem cousinDiamondStep_even_half (x : Nat) (hev : x % 2 = 0)
    (hnot : ¬ (x > 2 ∧ x % 6 = 2)) :
    cousinDiamondStep x = x / 2 := by
  unfold cousinDiamondStep
  have hno : ¬ (x % 2 = 1) := by omega
  simp only [hno, hnot, ite_false]

theorem cousinDiamondStep_pos (x : Nat) (hx : x > 0) :
    cousinDiamondStep x > 0 := by
  by_cases hodd : x % 2 = 1
  · rw [cousinDiamondStep_odd x hodd]
    omega
  · have hev : x % 2 = 0 := by omega
    by_cases h6 : x > 2 ∧ x % 6 = 2
    · rw [cousinDiamondStep_even_mod6_2 x h6.1 h6.2]
      omega
    · rw [cousinDiamondStep_even_half x hev h6]
      omega

/--
  Theorem W4.4a (`cousin_diamond_phi_strict_descent`, `[]` axioms):
  Every state `x > 2` strictly decreases the nonlocal 3-adic core potential
  `Φ_diamond(x) = core3(x + 1)^2 * (x + 1)` in a single step of `T_diamond`,
  EVEN along arbitrarily long `(3/2)^m` upward Mersenne glides!
-/
theorem cousin_diamond_phi_strict_descent (x : Nat) (hx : x > 2) :
    cousinDiamondPhi (cousinDiamondStep x) < cousinDiamondPhi x := by
  by_cases hodd : x % 2 = 1
  · let m := (x + 1) / 2
    have hm_ge2 : m ≥ 2 := by dsimp [m]; omega
    have hxp1 : x + 1 = 2 * m := by dsimp [m]; omega
    have htx : cousinDiamondStep x + 1 = 3 * m := by
      rw [cousinDiamondStep_odd x hodd]
      dsimp [m]
      omega
    unfold cousinDiamondPhi
    dsimp only
    rw [htx, hxp1, core3_mul3 m (by omega), core3_mul2 m (by omega)]
    let c := core3 m
    have hc_pos : c ≥ 1 := (core3_pos_and_le m (by omega)).1
    have hcc_pos : c * c ≥ 1 := Nat.mul_le_mul hc_pos hc_pos
    have hcm_pos : c * c * m ≥ 2 := Nat.mul_le_mul hcc_pos hm_ge2
    have hlhs : c * c * (3 * m) = 3 * (c * c * m) := by
      rw [← Nat.mul_assoc (c * c) 3 m, Nat.mul_comm (c * c) 3, Nat.mul_assoc]
    have hrhs : (2 * c) * (2 * c) * (2 * m) = 8 * (c * c * m) := by
      calc
        (2 * c) * (2 * c) * (2 * m)
            = (4 * (c * c)) * (2 * m) := by
              have h4 : (2 * c) * (2 * c) = 4 * (c * c) := by
                calc
                  (2 * c) * (2 * c) = 2 * (c * (2 * c)) := by rw [Nat.mul_assoc]
                  _ = 2 * (2 * (c * c)) := by
                    rw [← Nat.mul_assoc c 2 c, Nat.mul_comm c 2, Nat.mul_assoc]
                  _ = 4 * (c * c) := by rw [← Nat.mul_assoc]
              rw [h4]
        _ = 8 * (c * c * m) := by
              calc
                (4 * (c * c)) * (2 * m)
                    = 4 * ((c * c) * (2 * m)) := by rw [Nat.mul_assoc]
                _ = 4 * (2 * (c * c * m)) := by
                    rw [← Nat.mul_assoc (c * c) 2 m, Nat.mul_comm (c * c) 2, Nat.mul_assoc]
                _ = 8 * (c * c * m) := by rw [← Nat.mul_assoc]
    change c * c * (3 * m) < (2 * c) * (2 * c) * (2 * m)
    rw [hlhs, hrhs]
    omega
  · have hev : x % 2 = 0 := by omega
    by_cases h6 : x % 6 = 2
    · let m := (x + 1) / 3
      have hm_ge3 : m ≥ 3 := by dsimp [m]; omega
      have hxp1 : x + 1 = 3 * m := by dsimp [m]; omega
      have htx : cousinDiamondStep x + 1 = m := by
        rw [cousinDiamondStep_even_mod6_2 x hx h6]
        dsimp [m]
        omega
      unfold cousinDiamondPhi
      dsimp only
      rw [htx, hxp1, core3_mul3 m (by omega)]
      let c := core3 m
      have hc_pos : c ≥ 1 := (core3_pos_and_le m (by omega)).1
      have hcc_pos : c * c ≥ 1 := Nat.mul_le_mul hc_pos hc_pos
      have hcm_pos : c * c * m ≥ 3 := Nat.mul_le_mul hcc_pos hm_ge3
      have hrhs : c * c * (3 * m) = 3 * (c * c * m) := by
        rw [← Nat.mul_assoc (c * c) 3 m, Nat.mul_comm (c * c) 3, Nat.mul_assoc]
      change c * c * m < c * c * (3 * m)
      rw [hrhs]
      omega
    · have hnot : ¬ (x > 2 ∧ x % 6 = 2) := fun hp => h6 hp.2
      have hnd3 : (x + 1) % 3 ≠ 0 := by omega
      have htx : cousinDiamondStep x = x / 2 := cousinDiamondStep_even_half x hev hnot
      unfold cousinDiamondPhi
      dsimp only
      rw [htx, core3_not_div3 (x + 1) hnd3]
      let y := x / 2 + 1
      have hy_pos : y > 0 := by dsimp [y]; omega
      have hy_lt : y < x + 1 := by dsimp [y]; omega
      have hc_le : core3 y ≤ y := (core3_pos_and_le y hy_pos).2
      have hle_cube : core3 y * core3 y * y ≤ y * y * y :=
        Nat.mul_le_mul_right y (Nat.mul_le_mul hc_le hc_le)
      have hlt_cube : y * y * y < (x + 1) * (x + 1) * (x + 1) :=
        nat_cube_strict_mono y (x + 1) hy_lt
      change core3 y * core3 y * y < (x + 1) * (x + 1) * (x + 1)
      omega

theorem cousin_diamond_reaches_one_by_phi_bound :
    ∀ (B x : Nat), x > 0 -> cousinDiamondPhi x ≤ B -> ∃ k : Nat, cousinDiamondIter k x = 1
  | 0, x, hx, hB => by
    unfold cousinDiamondPhi at hB
    dsimp only at hB
    have hc_pos : core3 (x + 1) ≥ 1 := (core3_pos_and_le (x + 1) (by omega)).1
    have hphi_pos : core3 (x + 1) * core3 (x + 1) * (x + 1) ≥ 1 * 1 * 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul hc_pos hc_pos) (by omega)
    omega
  | B + 1, x, hx, hB => by
    by_cases hx1 : x = 1
    · subst hx1
      exact ⟨0, rfl⟩
    · by_cases hx2 : x = 2
      · subst hx2
        exact ⟨1, rfl⟩
      · have hx_gt2 : x > 2 := by omega
        have hdesc := cousin_diamond_phi_strict_descent x hx_gt2
        have hpos := cousinDiamondStep_pos x hx
        rcases cousin_diamond_reaches_one_by_phi_bound B (cousinDiamondStep x) hpos (by omega) with
          ⟨k, hk⟩
        exact ⟨k + 1, hk⟩

/--
  Theorem W4.4b (`cousin_diamond_global_convergence`, `[]` axioms):
  Unconditional Global Convergence of the Mixed-(2,3) Cousin `T_diamond` on `Z^+`:
  For EVERY positive integer `x > 0`, some iterate of `cousinDiamondStep` reaches `1`.
-/
theorem cousin_diamond_global_convergence :
    ∀ x : Nat, x > 0 -> ∃ k : Nat, cousinDiamondIter k x = 1 :=
  fun x hx => cousin_diamond_reaches_one_by_phi_bound (cousinDiamondPhi x) x hx (by omega)

theorem cousinDiamondStep_mersenne_scaled (a q : Nat) (ha : a ≥ 1) (hq : q ≥ 1) :
    cousinDiamondStep (2 ^ a * q - 1) = 2 ^ (a - 1) * (3 * q) - 1 := by
  have hp2 : 2 ^ a * q = 2 * (2 ^ (a - 1) * q) := by
    rw [pow2_split_pred a ha, Nat.mul_assoc]
  let m := 2 ^ (a - 1) * q
  have hm : m ≥ 1 := Nat.mul_le_mul (pow2_pos_nat (a - 1)) hq
  have hodd : (2 * m - 1) % 2 = 1 := by omega
  have hrew : 2 ^ a * q = 2 * m := hp2
  rw [hrew, cousinDiamondStep_odd (2 * m - 1) hodd]
  have h3m : (3 * (2 * m - 1) + 1) / 2 = 3 * m - 1 := by omega
  rw [h3m]
  have hcomm : 3 * m = 2 ^ (a - 1) * (3 * q) := by
    dsimp [m]
    rw [← Nat.mul_assoc 3 (2 ^ (a - 1)) q, Nat.mul_comm 3 (2 ^ (a - 1)), Nat.mul_assoc]
  rw [hcomm]

theorem cousin_diamond_mersenne_scaled :
    ∀ (k a q : Nat), k ≤ a -> q ≥ 1 ->
      cousinDiamondIter k (2 ^ a * q - 1) = 3 ^ k * 2 ^ (a - k) * q - 1
  | 0, _, _, _, _ => by simp [cousinDiamondIter]
  | k + 1, a, q, hka, hq => by
    simp only [cousinDiamondIter]
    rw [cousinDiamondStep_mersenne_scaled a q (by omega) hq]
    have ih := cousin_diamond_mersenne_scaled k (a - 1) (3 * q) (by omega) (by omega)
    rw [ih]
    have hexp : a - 1 - k = a - (k + 1) := by omega
    have hp3 : 3 ^ (k + 1) = 3 ^ k * 3 := by rw [Nat.pow_succ]
    rw [hexp, hp3]
    have hmul : 3 ^ k * 2 ^ (a - (k + 1)) * (3 * q) =
        3 ^ k * 3 * 2 ^ (a - (k + 1)) * q := by
      calc
        3 ^ k * 2 ^ (a - (k + 1)) * (3 * q)
            = 3 ^ k * (2 ^ (a - (k + 1)) * 3) * q := by
              rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
        _ = 3 ^ k * (3 * 2 ^ (a - (k + 1))) * q := by
              rw [Nat.mul_comm (2 ^ (a - (k + 1))) 3]
        _ = 3 ^ k * 3 * 2 ^ (a - (k + 1)) * q := by
              rw [← Nat.mul_assoc (3 ^ k) 3 (2 ^ (a - (k + 1)))]
    rw [hmul]

/--
  Theorem W4.4c (`cousin_diamond_unbounded_mersenne_glide`, `[]` axioms):
  `T_diamond` exhibits arbitrarily long `(3/2)^K` upward Mersenne glides: for EVERY
  horizon `K ≥ 1`, `x0 = 2^(K + 1) - 1` strictly grows across Steps `1..K`, proving
  no fixed-horizon `T_diamond^K(x) < x` ranking bound exists.
-/
theorem cousin_diamond_unbounded_mersenne_glide (K : Nat) (hK : K ≥ 1) :
    let x0 := 2 ^ (K + 1) - 1
    cousinDiamondIter K x0 = 3 ^ K * 2 - 1 ∧ x0 < cousinDiamondIter K x0 := by
  dsimp only
  have hf := cousin_diamond_mersenne_scaled K (K + 1) 1 (by omega) (by omega)
  simp only [Nat.mul_one] at hf
  have hex : K + 1 - K = 1 := by omega
  rw [hex, Nat.pow_one] at hf
  have hgt := pow3_gt_pow2_pos K hK
  have hsplit : 2 ^ (K + 1) = 2 ^ K * 2 := by rw [Nat.pow_succ]
  exact ⟨hf, by rw [hf, hsplit]; omega⟩

/--
  Theorem W4.4d (`cousin_diamond_mod_pow2_pow3_potential_impossibility`, `[]` axioms):
  Universal `∀ A, B ≥ 1` Bounded-Modulus `mod (2^A * 3^B)` Potential Impossibility on `T_diamond`:
  Even though `T_diamond` is globally convergent on `Z^+`, for EVERY `A, B ≥ 1` and EVERY
  monotone-per-residue potential `Φ(x, x % (2^A * 3^B))` (`∀ r a b, a < b -> Φ a r < Φ b r`),
  `x0 = 2^(A + 1) * 3^B - 1` strictly INCREASES `Φ` in one step!
-/
theorem cousin_diamond_mod_pow2_pow3_potential_impossibility
    (A B : Nat) (_hA : A ≥ 1) (_hB : B ≥ 1)
    (Phi : Nat -> Nat -> Int)
    (hmono : ∀ (r a b : Nat), a < b -> Phi a r < Phi b r) :
    let M := 2 ^ A * 3 ^ B
    let x0 := 2 * M - 1
    x0 > 2 ∧
    cousinDiamondStep x0 % M = x0 % M ∧
    Phi x0 (x0 % M) < Phi (cousinDiamondStep x0) (cousinDiamondStep x0 % M) := by
  dsimp only
  let M := 2 ^ A * 3 ^ B
  have hp2 : 2 ^ A ≥ 2 := by
    rw [pow2_split_pred A _hA]
    have hp0 := pow2_pos_nat (A - 1)
    omega
  have hp3 : 3 ^ B ≥ 3 := by
    have hgt := pow3_gt_pow2_pos B _hB
    have hp2B : 2 ^ B ≥ 2 := by
      rw [pow2_split_pred B _hB]
      have hp0 := pow2_pos_nat (B - 1)
      omega
    omega
  have hM_ge6 : M ≥ 6 := Nat.mul_le_mul hp2 hp3
  let x0 := 2 * M - 1
  have hx0_odd : x0 % 2 = 1 := by dsimp [x0]; omega
  have htx0 : cousinDiamondStep x0 = 3 * M - 1 := by
    rw [cousinDiamondStep_odd x0 hx0_odd]
    dsimp [x0]
    omega
  have hmod_x0 : x0 % M = M - 1 := by
    dsimp [x0]
    have heq : 2 * M - 1 = (M - 1) + M * 1 := by omega
    rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hmod_tx0 : cousinDiamondStep x0 % M = M - 1 := by
    rw [htx0]
    have heq : 3 * M - 1 = (M - 1) + M * 2 := by omega
    rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hres_eq : cousinDiamondStep x0 % M = x0 % M := by rw [hmod_tx0, hmod_x0]
  have hlt : x0 < cousinDiamondStep x0 := by rw [htx0]; dsimp [x0]; omega
  refine ⟨by omega, hres_eq, ?_⟩
  rw [hres_eq]
  exact hmono (x0 % M) x0 (cousinDiamondStep x0) hlt

/-- 3-symbol branch trace alphabet for `T_diamond` DFA state-complexity analysis -/
inductive CousinBranch where
  | half : CousinBranch
  | odd3x1 : CousinBranch
  | sub2div3 : CousinBranch
  deriving DecidableEq, Repr

def cousinBranchOf (x : Nat) : CousinBranch :=
  if x % 2 = 1 then CousinBranch.odd3x1
  else if x > 2 ∧ x % 6 = 2 then CousinBranch.sub2div3
  else CousinBranch.half

def matchesCousinFirstHitTrace : List CousinBranch -> Nat -> Prop
  | [], x => x = 1
  | b :: rest, x =>
    x > 1 ∧ cousinBranchOf x = b ∧ matchesCousinFirstHitTrace rest (cousinDiamondStep x)

def IsValidCousinFirstHitTrace (w : List CousinBranch) : Prop :=
  ∃ x : Nat, x > 1 ∧ matchesCousinFirstHitTrace w x

def cousinDfaRun {N : Nat} (delta : Fin N -> CousinBranch -> Fin N) :
    Fin N -> List CousinBranch -> Fin N
  | q, [] => q
  | q, b :: rest => cousinDfaRun delta (delta q b) rest

theorem cousinDfaRun_append {N : Nat} (delta : Fin N -> CousinBranch -> Fin N) :
    ∀ (u v : List CousinBranch) (q : Fin N),
      cousinDfaRun delta q (u ++ v) = cousinDfaRun delta (cousinDfaRun delta q u) v
  | [], _, _ => rfl
  | b :: rest, v, q => cousinDfaRun_append delta rest v (delta q b)

theorem matches_cousin_odd_run_scaled :
    ∀ (j c q : Nat) (suf : List CousinBranch),
      j ≤ c -> q ≥ 1 -> (c ≥ 2 ∨ q ≥ 3) ->
      matchesCousinFirstHitTrace suf (3 ^ j * 2 ^ (c - j) * q - 1) ->
      matchesCousinFirstHitTrace (List.replicate j CousinBranch.odd3x1 ++ suf) (2 ^ c * q - 1)
  | 0, _, _, suf, _, _, _, hs => by
    simp only [List.replicate_zero, List.nil_append, Nat.pow_zero, Nat.one_mul, Nat.sub_zero] at hs ⊢
    exact hs
  | j + 1, c, q, suf, hjc, hq, hgt1, hs => by
    have hc1 : c ≥ 1 := by omega
    have hp2c : 2 ^ c * q = 2 * (2 ^ (c - 1) * q) := by
      rw [pow2_split_pred c hc1, Nat.mul_assoc]
    let m := 2 ^ (c - 1) * q
    have hm : m ≥ 1 := Nat.mul_le_mul (pow2_pos_nat (c - 1)) hq
    have hx_gt1 : 2 ^ c * q - 1 > 1 := by
      rcases hgt1 with hc2 | hq3
      · have hp4 := pow2_ge_four_of_ge_two c hc2
        have hmul := Nat.mul_le_mul hp4 hq
        omega
      · rw [hp2c]
        have hm3 : m ≥ 3 := by
          dsimp [m]
          have hp0 := pow2_pos_nat (c - 1)
          have hmul := Nat.mul_le_mul hp0 hq3
          omega
        omega
    have hodd_cq : (2 ^ c * q - 1) % 2 = 1 := by
      have hrw : 2 ^ c * q = 2 * m := hp2c
      rw [hrw]
      omega
    have hbr_cq : cousinBranchOf (2 ^ c * q - 1) = CousinBranch.odd3x1 := by
      unfold cousinBranchOf
      simp only [hodd_cq, ite_true]
    simp only [List.replicate_succ, List.cons_append, matchesCousinFirstHitTrace]
    refine ⟨hx_gt1, hbr_cq, ?_⟩
    rw [cousinDiamondStep_mersenne_scaled c q hc1 hq]
    apply matches_cousin_odd_run_scaled j (c - 1) (3 * q) suf (by omega) (by omega) (Or.inr (by omega))
    have hexp : c - 1 - j = c - (j + 1) := by omega
    have hmul : 3 ^ j * 2 ^ (c - (j + 1)) * (3 * q) =
        3 ^ (j + 1) * 2 ^ (c - (j + 1)) * q := by
      rw [Nat.pow_succ 3 j]
      calc
        3 ^ j * 2 ^ (c - (j + 1)) * (3 * q)
            = 3 ^ j * (2 ^ (c - (j + 1)) * 3) * q := by
              rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
        _ = 3 ^ j * (3 * 2 ^ (c - (j + 1))) * q := by
              rw [Nat.mul_comm (2 ^ (c - (j + 1))) 3]
        _ = 3 ^ j * 3 * 2 ^ (c - (j + 1)) * q := by
              rw [← Nat.mul_assoc (3 ^ j) 3]
    rw [hexp, hmul]
    exact hs

theorem matches_cousin_sub2div3_pow3 :
    ∀ m : Nat,
      matchesCousinFirstHitTrace
        (List.replicate m CousinBranch.sub2div3 ++ [CousinBranch.half])
        (3 ^ (m + 1) - 1)
  | 0 => by
    simp [matchesCousinFirstHitTrace, cousinBranchOf, cousinDiamondStep]
  | m + 1 => by
    simp only [List.replicate_succ, List.cons_append, matchesCousinFirstHitTrace]
    have hp3_ge3 : 3 ^ (m + 1) ≥ 3 := by
      have hgt := pow3_gt_pow2_pos (m + 1) (by omega)
      have hp2 : 2 ^ (m + 1) ≥ 2 := by
        rw [Nat.pow_succ]
        have hp0 := pow2_pos_nat m
        omega
      omega
    have hp3_next : 3 ^ (m + 2) = 3 * 3 ^ (m + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm]
    have hp3_odd : 3 ^ (m + 1) % 2 = 1 := by
      clear hp3_ge3 hp3_next
      induction m with
      | zero => rfl
      | succ k ih => rw [Nat.pow_succ]; omega
    let k3 := 3 ^ (m + 1)
    have hk3_ge3 : k3 ≥ 3 := hp3_ge3
    have hk3_odd : k3 % 2 = 1 := hp3_odd
    have hrw : 3 ^ (m + 2) = 3 * k3 := hp3_next
    have hx_gt2 : 3 ^ (m + 2) - 1 > 2 := by rw [hrw]; omega
    have hx_nodd : ¬ ((3 ^ (m + 2) - 1) % 2 = 1) := by rw [hrw]; omega
    have hx_mod6 : (3 ^ (m + 2) - 1) % 6 = 2 := by rw [hrw]; omega
    have hbr : cousinBranchOf (3 ^ (m + 2) - 1) = CousinBranch.sub2div3 := by
      unfold cousinBranchOf
      simp only [hx_nodd, hx_gt2, hx_mod6, and_self, ite_true, ite_false]
    have hst : cousinDiamondStep (3 ^ (m + 2) - 1) = 3 ^ (m + 1) - 1 := by
      rw [cousinDiamondStep_even_mod6_2 (3 ^ (m + 2) - 1) hx_gt2 hx_mod6, hrw]
      dsimp [k3]
      omega
    refine ⟨by omega, hbr, ?_⟩
    rw [hst]
    exact matches_cousin_sub2div3_pow3 m

theorem cousin_mersenne_trace_valid (m : Nat) (hm : m ≥ 1) :
    IsValidCousinFirstHitTrace
      (List.replicate (m + 1) CousinBranch.odd3x1 ++
        (List.replicate m CousinBranch.sub2div3 ++ [CousinBranch.half])) := by
  refine ⟨2 ^ (m + 1) - 1, ?_, ?_⟩
  · have hp4 := pow2_ge_four_of_ge_two (m + 1) (by omega)
    omega
  · have hm1 := matches_cousin_odd_run_scaled (m + 1) (m + 1) 1
      (List.replicate m CousinBranch.sub2div3 ++ [CousinBranch.half])
      (by omega) (by omega) (Or.inl (by omega))
    simp only [Nat.mul_one, Nat.sub_self, Nat.pow_zero] at hm1
    exact hm1 (matches_cousin_sub2div3_pow3 m)

theorem odd_trace_builds_pow3_div :
    ∀ (j : Nat) (suf : List CousinBranch) (x d : Nat),
      d % 2 = 1 ->
      d ∣ (x + 1) ->
      matchesCousinFirstHitTrace (List.replicate j CousinBranch.odd3x1 ++ suf) x ->
      ∃ y : Nat, (3 ^ j * d) ∣ (y + 1) ∧ matchesCousinFirstHitTrace suf y
  | 0, suf, x, d, _, hd, hm => by
    simp only [List.replicate_zero, List.nil_append, Nat.pow_zero, Nat.one_mul] at hm ⊢
    exact ⟨x, hd, hm⟩
  | j + 1, suf, x, d, hd_odd, hd, hm => by
    simp only [List.replicate_succ, List.cons_append, matchesCousinFirstHitTrace] at hm
    rcases hm with ⟨_, hbr, hrest⟩
    have hodd : x % 2 = 1 := by
      unfold cousinBranchOf at hbr
      by_cases ho : x % 2 = 1
      · exact ho
      · simp only [ho, ite_false] at hbr
        by_cases h6 : x > 2 ∧ x % 6 = 2
        · simp only [h6, and_self, ite_true] at hbr; cases hbr
        · simp only [h6, ite_false] at hbr; cases hbr
    have htx : 2 * (cousinDiamondStep x + 1) = 3 * (x + 1) := by
      rw [cousinDiamondStep_odd x hodd]
      omega
    rcases hd with ⟨q, hq⟩
    have hxp1_ev : (d * q) % 2 = 0 := by rw [← hq]; omega
    have hq_ev : q % 2 = 0 := by
      rw [Nat.mul_mod, hd_odd, Nat.one_mul, Nat.mod_mod] at hxp1_ev
      exact hxp1_ev
    let q2 := q / 2
    have hq_eq : q = 2 * q2 := by dsimp [q2]; omega
    have hd_next : (3 * d) ∣ (cousinDiamondStep x + 1) := by
      refine ⟨q2, ?_⟩
      have hmul : 2 * (cousinDiamondStep x + 1) = 2 * ((3 * d) * q2) := by
        rw [htx, hq, hq_eq]
        calc
          3 * (d * (2 * q2)) = (3 * d) * (2 * q2) := by rw [← Nat.mul_assoc]
          _ = ((3 * d) * 2) * q2 := by rw [← Nat.mul_assoc]
          _ = (2 * (3 * d)) * q2 := by rw [Nat.mul_comm (3 * d) 2]
          _ = 2 * ((3 * d) * q2) := by rw [Nat.mul_assoc]
      exact nat_mul_left_cancel_pos 2 _ _ (by omega) hmul
    have hd3_odd : (3 * d) % 2 = 1 := by
      rw [Nat.mul_mod, hd_odd]
    rcases odd_trace_builds_pow3_div j suf (cousinDiamondStep x) (3 * d) hd3_odd hd_next hrest with
      ⟨y, hy_dvd, hy_m⟩
    have hp3_assoc : 3 ^ j * (3 * d) = 3 ^ (j + 1) * d := by
      rw [← Nat.mul_assoc, ← Nat.pow_succ]
    rw [hp3_assoc] at hy_dvd
    exact ⟨y, hy_dvd, hy_m⟩

theorem sub2div3_trace_consumes_pow3_div :
    ∀ (m : Nat) (suf : List CousinBranch) (y d : Nat),
      (3 ^ m * d) ∣ (y + 1) ->
      matchesCousinFirstHitTrace (List.replicate m CousinBranch.sub2div3 ++ suf) y ->
      ∃ z : Nat, d ∣ (z + 1) ∧ matchesCousinFirstHitTrace suf z
  | 0, suf, y, d, hd, hm => by
    simp only [List.replicate_zero, List.nil_append, Nat.pow_zero, Nat.one_mul] at hd hm
    exact ⟨y, hd, hm⟩
  | m + 1, suf, y, d, hd, hm => by
    simp only [List.replicate_succ, List.cons_append, matchesCousinFirstHitTrace] at hm
    rcases hm with ⟨_, hbr, hrest⟩
    have h6 : y > 2 ∧ y % 6 = 2 := by
      unfold cousinBranchOf at hbr
      by_cases ho : y % 2 = 1
      · simp only [ho, ite_true] at hbr; cases hbr
      · simp only [ho, ite_false] at hbr
        by_cases hc6 : y > 2 ∧ y % 6 = 2
        · exact hc6
        · simp only [hc6, ite_false] at hbr; cases hbr
    have hty : 3 * (cousinDiamondStep y + 1) = y + 1 := by
      rw [cousinDiamondStep_even_mod6_2 y h6.1 h6.2]
      omega
    rcases hd with ⟨q, hq⟩
    have hd_next : (3 ^ m * d) ∣ (cousinDiamondStep y + 1) := by
      refine ⟨q, ?_⟩
      have hmul : 3 * (cousinDiamondStep y + 1) = 3 * ((3 ^ m * d) * q) := by
        rw [hty, hq]
        calc
          3 ^ (m + 1) * d * q
              = (3 ^ m * 3) * d * q := by rw [Nat.pow_succ]
          _ = (3 * 3 ^ m) * d * q := by rw [Nat.mul_comm (3 ^ m) 3]
          _ = (3 * (3 ^ m * d)) * q := by rw [Nat.mul_assoc 3 (3 ^ m) d]
          _ = 3 * ((3 ^ m * d) * q) := by rw [Nat.mul_assoc 3 (3 ^ m * d) q]
      exact nat_mul_left_cancel_pos 3 _ _ (by omega) hmul
    exact sub2div3_trace_consumes_pow3_div m suf (cousinDiamondStep y) d hd_next hrest

theorem cousin_mismatched_mersenne_trace_invalid (m1 m2 : Nat) (hlt : m1 < m2) :
    ¬ IsValidCousinFirstHitTrace
      (List.replicate (m2 + 1) CousinBranch.odd3x1 ++
        (List.replicate m1 CousinBranch.sub2div3 ++ [CousinBranch.half])) := by
  intro ⟨x, _, hmatch⟩
  rcases odd_trace_builds_pow3_div (m2 + 1)
      (List.replicate m1 CousinBranch.sub2div3 ++ [CousinBranch.half])
      x 1 rfl ⟨x + 1, by simp⟩ hmatch with ⟨y, hy_dvd, hy_m⟩
  rw [Nat.mul_one] at hy_dvd
  have hexp : 3 ^ (m2 + 1) = 3 ^ m1 * (9 * 3 ^ (m2 - 1 - m1)) := by
    have hsum : m2 + 1 = m1 + (2 + (m2 - 1 - m1)) := by omega
    rw [hsum, Nat.pow_add, Nat.pow_add]
  rw [hexp] at hy_dvd
  rcases sub2div3_trace_consumes_pow3_div m1 [CousinBranch.half] y
      (9 * 3 ^ (m2 - 1 - m1)) hy_dvd hy_m with ⟨z, hz_dvd, hz_m⟩
  simp only [matchesCousinFirstHitTrace] at hz_m
  rcases hz_m with ⟨_, hz_br, hz_end⟩
  have hnot_odd : z % 2 = 0 := by
    unfold cousinBranchOf at hz_br
    by_cases ho : z % 2 = 1
    · simp only [ho, ite_true] at hz_br; cases hz_br
    · omega
  have hnot_mod6 : ¬ (z > 2 ∧ z % 6 = 2) := by
    intro hp
    unfold cousinBranchOf at hz_br
    have hno : ¬ (z % 2 = 1) := by omega
    simp only [hno, hp, and_self, ite_true, ite_false] at hz_br
    cases hz_br
  have hz_eq2 : z = 2 := by
    rw [cousinDiamondStep_even_half z hnot_odd hnot_mod6] at hz_end
    omega
  subst hz_eq2
  rcases hz_dvd with ⟨q, hq⟩
  have hp0 : 3 ^ (m2 - 1 - m1) ≥ 1 := by
    clear hmatch hy_m hz_br hz_end hq
    induction (m2 - 1 - m1) with
    | zero => decide
    | succ k ih => rw [Nat.pow_succ]; omega
  by_cases hq0 : q = 0
  · subst hq0; simp at hq
  · have hge9 : 9 * 3 ^ (m2 - 1 - m1) * q ≥ 9 * 1 * 1 :=
      Nat.mul_le_mul (Nat.mul_le_mul (by omega) hp0) (by omega)
    omega

/--
  Theorem W4.4e (`cousin_diamond_no_finite_dfa_trace_language`, `[]` axioms):
  Universal `∀ N ≥ 1` Finite-Automaton Impossibility on `T_diamond`:
  For EVERY state count `N ≥ 1` and EVERY DFA `(delta, q0, accept)` over `CousinBranch`,
  there exists an explicit branch word `w` misclassified by the DFA:
  `(accept (cousinDfaRun delta q0 w) = true) ↔ ¬ IsValidCousinFirstHitTrace w`.
-/
theorem cousin_diamond_no_finite_dfa_trace_language (N : Nat) (_hN : N ≥ 1)
    (delta : Fin N -> CousinBranch -> Fin N) (q0 : Fin N) (accept : Fin N -> Bool) :
    ∃ w : List CousinBranch,
      (accept (cousinDfaRun delta q0 w) = true) ↔ ¬ IsValidCousinFirstHitTrace w := by
  let f : Fin (N + 1) -> Fin N :=
    fun i => cousinDfaRun delta q0 (List.replicate (i.val + 2) CousinBranch.odd3x1)
  rcases pigeonhole_fin_nat N (N + 1) (by omega) f with ⟨i1, i2, hi_ne, hst_eq⟩
  have hval_ne : i1.val ≠ i2.val := fun h => hi_ne (Fin.eq_of_val_eq h)
  have hor : i1.val < i2.val ∨ i2.val < i1.val := by omega
  rcases hor with hlt | hgt
  · let m1 := i1.val + 1
    let m2 := i2.val + 1
    let suf := List.replicate m1 CousinBranch.sub2div3 ++ [CousinBranch.half]
    let w1 := List.replicate (m1 + 1) CousinBranch.odd3x1 ++ suf
    let w2 := List.replicate (m2 + 1) CousinBranch.odd3x1 ++ suf
    have hrun : cousinDfaRun delta q0 w1 = cousinDfaRun delta q0 w2 := by
      have ha1 := cousinDfaRun_append delta (List.replicate (m1 + 1) CousinBranch.odd3x1) suf q0
      have ha2 := cousinDfaRun_append delta (List.replicate (m2 + 1) CousinBranch.odd3x1) suf q0
      dsimp [w1, w2]
      rw [ha1, ha2]
      have heq_f : cousinDfaRun delta q0 (List.replicate (i1.val + 2) CousinBranch.odd3x1) =
          cousinDfaRun delta q0 (List.replicate (i2.val + 2) CousinBranch.odd3x1) := hst_eq
      have h1 : m1 + 1 = i1.val + 2 := rfl
      have h2 : m2 + 1 = i2.val + 2 := rfl
      rw [h1, h2, heq_f]
    have hv1 : IsValidCousinFirstHitTrace w1 := cousin_mersenne_trace_valid m1 (by dsimp [m1]; omega)
    have hnv2 : ¬ IsValidCousinFirstHitTrace w2 :=
      cousin_mismatched_mersenne_trace_invalid m1 m2 (by dsimp [m1, m2]; omega)
    cases hacc : accept (cousinDfaRun delta q0 w1) with
    | true =>
      refine ⟨w2, ?_⟩
      rw [← hrun, hacc]
      exact ⟨fun _ => hnv2, fun _ => rfl⟩
    | false =>
      refine ⟨w1, ?_⟩
      rw [hacc]
      exact ⟨fun ht => Bool.noConfusion ht, fun hnv => False.elim (hnv hv1)⟩
  · let m1 := i2.val + 1
    let m2 := i1.val + 1
    let suf := List.replicate m1 CousinBranch.sub2div3 ++ [CousinBranch.half]
    let w1 := List.replicate (m1 + 1) CousinBranch.odd3x1 ++ suf
    let w2 := List.replicate (m2 + 1) CousinBranch.odd3x1 ++ suf
    have hrun : cousinDfaRun delta q0 w1 = cousinDfaRun delta q0 w2 := by
      have ha1 := cousinDfaRun_append delta (List.replicate (m1 + 1) CousinBranch.odd3x1) suf q0
      have ha2 := cousinDfaRun_append delta (List.replicate (m2 + 1) CousinBranch.odd3x1) suf q0
      dsimp [w1, w2]
      rw [ha1, ha2]
      have heq_f : cousinDfaRun delta q0 (List.replicate (i2.val + 2) CousinBranch.odd3x1) =
          cousinDfaRun delta q0 (List.replicate (i1.val + 2) CousinBranch.odd3x1) := hst_eq.symm
      have h1 : m1 + 1 = i2.val + 2 := rfl
      have h2 : m2 + 1 = i1.val + 2 := rfl
      rw [h1, h2, heq_f]
    have hv1 : IsValidCousinFirstHitTrace w1 := cousin_mersenne_trace_valid m1 (by dsimp [m1]; omega)
    have hnv2 : ¬ IsValidCousinFirstHitTrace w2 :=
      cousin_mismatched_mersenne_trace_invalid m1 m2 (by dsimp [m1, m2]; omega)
    cases hacc : accept (cousinDfaRun delta q0 w1) with
    | true =>
      refine ⟨w2, ?_⟩
      rw [← hrun, hacc]
      exact ⟨fun _ => hnv2, fun _ => rfl⟩
    | false =>
      refine ⟨w1, ?_⟩
      rw [hacc]
      exact ⟨fun ht => Bool.noConfusion ht, fun hnv => False.elim (hnv hv1)⟩

/--
  Theorem W4.4f (`cousin_diamond_counter_model_and_antagonism_witnesses`, `[]` axioms):
  1. Counter-Model `M2 = Z^-` fails on `T_diamond`: `-1` is a fixed point and `-5`
     lies on the 3-cycle `-5 -> -7 -> -10 -> -5`.
  2. Counter-Model `M1 = Q_(6)^+` fails on `T_diamond`: `1/7 -> 5/7 -> 11/7 -> 20/7 -> 2/7 -> 1/7`
     closes a strictly positive non-integer 5-cycle (certified in cleared-denominator
     `d = 7` arithmetic where `20 > 2*7` takes `(20 - 2*7)/3 = 2` and `2 ≤ 2*7` takes `2/2 = 1`).
  3. Valuation-Archimedean Antagonism on True `3x + 1`: at the minimal evolutionary
     red-team falsifier `x = 17 -> 13` (`collatzIter 2 17 = 13 < 17`), `core3 (17 + 1) = 2`
     explodes to `core3 (13 + 1) = 14`, causing `cousinDiamondPhi 13 = 2744 > 72 = cousinDiamondPhi 17`!
-/
theorem cousin_diamond_counter_model_and_antagonism_witnesses :
    cousinDiamondStepInt (-1) = -1 ∧
    cousinDiamondIterInt 3 (-5) = -5 ∧
    ((3 * 1 + 7) / 2 = 5 ∧ (3 * 5 + 7) / 2 = 11 ∧ (3 * 11 + 7) / 2 = 20 ∧
      (20 - 2 * 7) / 3 = 2 ∧ 2 / 2 = 1) ∧
    collatzIter 2 17 = 13 ∧
    core3 (17 + 1) = 2 ∧
    core3 (13 + 1) = 14 ∧
    cousinDiamondPhi 17 = 72 ∧
    cousinDiamondPhi 13 = 2744 := by
  decide

-- ============================================================================
-- SECTION 5: Universal `(2, 3)`-Adic Laurent Valuation Monomial Impossibility
--            (`{7, 9, 17, 97}` Cycle) & Sharp `w ≥ 6` First-Hit Weight Barrier
--            on `Mod373248UniqueFirstHitRangeProp` (`[]` Axioms)
-- ============================================================================

def core2Aux : Nat -> Nat -> Nat
  | 0, n => n
  | fuel + 1, n =>
    if n > 0 ∧ n % 2 = 0 then core2Aux fuel (n / 2) else n

def core2 (n : Nat) : Nat :=
  core2Aux n n

def v2PowAux : Nat -> Nat -> Nat
  | 0, _ => 1
  | fuel + 1, n =>
    if n > 0 ∧ n % 2 = 0 then 2 * v2PowAux fuel (n / 2) else 1

def v2Pow (n : Nat) : Nat :=
  v2PowAux n n

def v3PowAux : Nat -> Nat -> Nat
  | 0, _ => 1
  | fuel + 1, n =>
    if n > 0 ∧ n % 3 = 0 then 3 * v3PowAux fuel (n / 3) else 1

def v3Pow (n : Nat) : Nat :=
  v3PowAux n n

def coprime23Core (n : Nat) : Nat :=
  core2 (core3 n)

def syracuseOddStep (x : Nat) : Nat :=
  core2 (3 * x + 1)

def laurentValNum (aPos bPos cPos x : Nat) : Nat :=
  (v2Pow (x + 1)) ^ aPos * (v3Pow (x + 1)) ^ bPos * (coprime23Core (x + 1)) ^ cPos

def laurentValDen (aNeg bNeg cNeg x : Nat) : Nat :=
  (v2Pow (x + 1)) ^ aNeg * (v3Pow (x + 1)) ^ bNeg * (coprime23Core (x + 1)) ^ cNeg

theorem mul_pow_local (a b : Nat) : ∀ m : Nat, (a * b) ^ m = a ^ m * b ^ m
  | 0 => rfl
  | m + 1 => by
    rw [Nat.pow_succ (a * b) m, Nat.pow_succ a m, Nat.pow_succ b m, mul_pow_local a b m]
    calc
      (a ^ m * b ^ m) * (a * b)
          = a ^ m * (b ^ m * (a * b)) := Nat.mul_assoc _ _ _
      _ = a ^ m * ((b ^ m * a) * b) := by rw [← Nat.mul_assoc (b ^ m) a b]
      _ = a ^ m * ((a * b ^ m) * b) := by rw [Nat.mul_comm (b ^ m) a]
      _ = (a ^ m * a) * (b ^ m * b) := by
            rw [Nat.mul_assoc a (b ^ m) b, ← Nat.mul_assoc (a ^ m) a (b ^ m * b)]

theorem nat_mul_lt_cancel_left (k a b : Nat) (_hk : k > 0) (hlt : k * a < k * b) : a < b := by
  by_cases h : a < b
  · exact h
  · have hm := Nat.mul_le_mul_left k (by omega : b ≤ a)
    omega

theorem nat_mul_lt_mul_pos (a1 b1 a2 b2 : Nat) (h1 : a1 < b1) (h2 : a2 < b2) :
    a1 * a2 < b1 * b2 := by
  have hb2_pos : b2 > 0 := by omega
  have hle1 : a1 * a2 ≤ a1 * b2 := Nat.mul_le_mul_left a1 (by omega)
  have hlt2 : a1 * b2 < b1 * b2 := Nat.mul_lt_mul_of_pos_right h1 hb2_pos
  omega

theorem syracuse_four_witness_valuations :
    syracuseOddStep 7 = 11 ∧
    syracuseOddStep 9 = 7 ∧
    syracuseOddStep 17 = 13 ∧
    syracuseOddStep 97 = 73 ∧
    (v2Pow 8 = 8 ∧ v3Pow 8 = 1 ∧ coprime23Core 8 = 1) ∧
    (v2Pow 12 = 4 ∧ v3Pow 12 = 3 ∧ coprime23Core 12 = 1) ∧
    (v2Pow 10 = 2 ∧ v3Pow 10 = 1 ∧ coprime23Core 10 = 5) ∧
    (v2Pow 18 = 2 ∧ v3Pow 18 = 9 ∧ coprime23Core 18 = 1) ∧
    (v2Pow 14 = 2 ∧ v3Pow 14 = 1 ∧ coprime23Core 14 = 7) ∧
    (v2Pow 98 = 2 ∧ v3Pow 98 = 1 ∧ coprime23Core 98 = 49) ∧
    (v2Pow 74 = 2 ∧ v3Pow 74 = 1 ∧ coprime23Core 74 = 37) := by
  decide

/--
  Theorem W4.5a (`syracuse_laurent_valuation_monomial_impossibility`, `[]` axioms):
  Universal `(2, 3)`-Adic Rational / Laurent Valuation Monomial Impossibility Theorem:
  For EVERY 6-tuple of nonnegative exponents `(aPos aNeg bPos bNeg cPos cNeg : Nat)`
  (representing ANY positive, zero, or negative rational-exponent Laurent monomial
  `Ψ(x) = (2^{v_2(x+1)})^(aPos - aNeg) * (3^{v_3(x+1)})^(bPos - bNeg) * core_{2,3}(x+1)^(cPos - cNeg)`,
  including both coercive non-monotone valuation potentials like `4^{v_2(x+1)} * (x+1)`
  that evade `W4.2b` on Mersenne glides AND non-coercive reciprocal potentials),
  strict cleared-denominator Syracuse descent `Num(S(x)) * Den(x) < Num(x) * Den(S(x))`
  CANNOT hold simultaneously across the 4-witness set `{7, 9, 17, 97}`!
-/
theorem syracuse_laurent_valuation_monomial_impossibility
    (aPos aNeg bPos bNeg cPos cNeg : Nat) :
    ¬ (∀ x : Nat, (x = 7 ∨ x = 9 ∨ x = 17 ∨ x = 97) ->
        laurentValNum aPos bPos cPos (syracuseOddStep x) * laurentValDen aNeg bNeg cNeg x <
          laurentValNum aPos bPos cPos x * laurentValDen aNeg bNeg cNeg (syracuseOddStep x)) := by
  intro hdesc
  rcases syracuse_four_witness_valuations with
    ⟨hs7, hs9, hs17, hs97,
     ⟨hv2_8, hv3_8, hg_8⟩,
     ⟨hv2_12, hv3_12, hg_12⟩,
     ⟨hv2_10, hv3_10, hg_10⟩,
     ⟨hv2_18, hv3_18, hg_18⟩,
     ⟨hv2_14, hv3_14, hg_14⟩,
     ⟨hv2_98, hv3_98, hg_98⟩,
     ⟨hv2_74, hv3_74, hg_74⟩⟩
  have h7 := hdesc 7 (Or.inl rfl)
  have h9 := hdesc 9 (Or.inr (Or.inl rfl))
  have h17 := hdesc 17 (Or.inr (Or.inr (Or.inl rfl)))
  have h97 := hdesc 97 (Or.inr (Or.inr (Or.inr rfl)))
  unfold laurentValNum laurentValDen at h7 h9 h17 h97
  rw [hs7] at h7
  rw [hs9] at h9
  rw [hs17] at h17
  rw [hs97] at h97
  simp only [show 7 + 1 = 8 from rfl, show 11 + 1 = 12 from rfl,
             show 9 + 1 = 10 from rfl, show 17 + 1 = 18 from rfl,
             show 13 + 1 = 14 from rfl, show 97 + 1 = 98 from rfl,
             show 73 + 1 = 74 from rfl,
             hv2_8, hv3_8, hg_8, hv2_12, hv3_12, hg_12, hv2_10, hv3_10, hg_10,
             hv2_18, hv3_18, hg_18, hv2_14, hv3_14, hg_14,
             hv2_98, hv3_98, hg_98, hv2_74, hv3_74, hg_74,
             Nat.one_pow, Nat.mul_one] at h7 h9 h17 h97
  -- 1. From `7 -> 11`: `4^aPos * 3^bPos * 8^aNeg < 8^aPos * (4^aNeg * 3^bNeg)` -> `9^bPos * 4^aNeg < 4^aPos * 9^bNeg`:
  have h8_pos : 8 ^ aPos = 4 ^ aPos * 2 ^ aPos := mul_pow_local 4 2 aPos
  have h8_neg : 8 ^ aNeg = 4 ^ aNeg * 2 ^ aNeg := mul_pow_local 4 2 aNeg
  rw [h8_pos, h8_neg] at h7
  have h7_rearr : (4 ^ aPos * 4 ^ aNeg) * (3 ^ bPos * 2 ^ aNeg) <
      (4 ^ aPos * 4 ^ aNeg) * (2 ^ aPos * 3 ^ bNeg) := by
    have hl : (4 ^ aPos * 3 ^ bPos) * (4 ^ aNeg * 2 ^ aNeg) =
        (4 ^ aPos * 4 ^ aNeg) * (3 ^ bPos * 2 ^ aNeg) := by
      calc
        (4 ^ aPos * 3 ^ bPos) * (4 ^ aNeg * 2 ^ aNeg)
            = 4 ^ aPos * (3 ^ bPos * (4 ^ aNeg * 2 ^ aNeg)) := Nat.mul_assoc _ _ _
        _ = 4 ^ aPos * ((3 ^ bPos * 4 ^ aNeg) * 2 ^ aNeg) := by rw [← Nat.mul_assoc (3 ^ bPos)]
        _ = 4 ^ aPos * ((4 ^ aNeg * 3 ^ bPos) * 2 ^ aNeg) := by rw [Nat.mul_comm (3 ^ bPos) (4 ^ aNeg)]
        _ = (4 ^ aPos * 4 ^ aNeg) * (3 ^ bPos * 2 ^ aNeg) := by
              rw [Nat.mul_assoc (4 ^ aNeg), ← Nat.mul_assoc (4 ^ aPos)]
    have hr : (4 ^ aPos * 2 ^ aPos) * (4 ^ aNeg * 3 ^ bNeg) =
        (4 ^ aPos * 4 ^ aNeg) * (2 ^ aPos * 3 ^ bNeg) := by
      calc
        (4 ^ aPos * 2 ^ aPos) * (4 ^ aNeg * 3 ^ bNeg)
            = 4 ^ aPos * (2 ^ aPos * (4 ^ aNeg * 3 ^ bNeg)) := Nat.mul_assoc _ _ _
        _ = 4 ^ aPos * ((2 ^ aPos * 4 ^ aNeg) * 3 ^ bNeg) := by rw [← Nat.mul_assoc (2 ^ aPos)]
        _ = 4 ^ aPos * ((4 ^ aNeg * 2 ^ aPos) * 3 ^ bNeg) := by rw [Nat.mul_comm (2 ^ aPos) (4 ^ aNeg)]
        _ = (4 ^ aPos * 4 ^ aNeg) * (2 ^ aPos * 3 ^ bNeg) := by
              rw [Nat.mul_assoc (4 ^ aNeg), ← Nat.mul_assoc (4 ^ aPos)]
    rw [← hl, ← hr]
    exact h7
  have h1_base : 3 ^ bPos * 2 ^ aNeg < 2 ^ aPos * 3 ^ bNeg :=
    nat_mul_lt_cancel_left (4 ^ aPos * 4 ^ aNeg) _ _
      (Nat.mul_le_mul (nat_pow_pos_of_pos 4 (by decide) aPos) (nat_pow_pos_of_pos 4 (by decide) aNeg))
      h7_rearr
  have h1_sq : 9 ^ bPos * 4 ^ aNeg < 4 ^ aPos * 9 ^ bNeg := by
    have hsq := nat_mul_lt_mul_pos _ _ _ _ h1_base h1_base
    have hl : (3 ^ bPos * 2 ^ aNeg) * (3 ^ bPos * 2 ^ aNeg) = 9 ^ bPos * 4 ^ aNeg := by
      rw [show (9 : Nat) = 3 * 3 from rfl, show (4 : Nat) = 2 * 2 from rfl,
          mul_pow_local 3 3, mul_pow_local 2 2]
      calc
        (3 ^ bPos * 2 ^ aNeg) * (3 ^ bPos * 2 ^ aNeg)
            = 3 ^ bPos * (2 ^ aNeg * (3 ^ bPos * 2 ^ aNeg)) := Nat.mul_assoc _ _ _
        _ = 3 ^ bPos * ((2 ^ aNeg * 3 ^ bPos) * 2 ^ aNeg) := by rw [← Nat.mul_assoc (2 ^ aNeg)]
        _ = 3 ^ bPos * ((3 ^ bPos * 2 ^ aNeg) * 2 ^ aNeg) := by rw [Nat.mul_comm (2 ^ aNeg) (3 ^ bPos)]
        _ = (3 ^ bPos * 3 ^ bPos) * (2 ^ aNeg * 2 ^ aNeg) := by
              rw [Nat.mul_assoc (3 ^ bPos), ← Nat.mul_assoc (3 ^ bPos)]
    have hr : (2 ^ aPos * 3 ^ bNeg) * (2 ^ aPos * 3 ^ bNeg) = 4 ^ aPos * 9 ^ bNeg := by
      rw [show (9 : Nat) = 3 * 3 from rfl, show (4 : Nat) = 2 * 2 from rfl,
          mul_pow_local 3 3, mul_pow_local 2 2]
      calc
        (2 ^ aPos * 3 ^ bNeg) * (2 ^ aPos * 3 ^ bNeg)
            = 2 ^ aPos * (3 ^ bNeg * (2 ^ aPos * 3 ^ bNeg)) := Nat.mul_assoc _ _ _
        _ = 2 ^ aPos * ((3 ^ bNeg * 2 ^ aPos) * 3 ^ bNeg) := by rw [← Nat.mul_assoc (3 ^ bNeg)]
        _ = 2 ^ aPos * ((2 ^ aPos * 3 ^ bNeg) * 3 ^ bNeg) := by rw [Nat.mul_comm (3 ^ bNeg) (2 ^ aPos)]
        _ = (2 ^ aPos * 2 ^ aPos) * (3 ^ bNeg * 3 ^ bNeg) := by
              rw [Nat.mul_assoc (2 ^ aPos), ← Nat.mul_assoc (2 ^ aPos)]
    rwa [hl, hr] at hsq
  -- 2. From `9 -> 7`: `4^aPos * 5^cNeg < 5^cPos * 4^aNeg`:
  have h8_pos2 : 8 ^ aPos = 2 ^ aPos * 4 ^ aPos := mul_pow_local 2 4 aPos
  have h8_neg2 : 8 ^ aNeg = 2 ^ aNeg * 4 ^ aNeg := mul_pow_local 2 4 aNeg
  rw [h8_pos2, h8_neg2] at h9
  have h2_ineq : 4 ^ aPos * 5 ^ cNeg < 5 ^ cPos * 4 ^ aNeg := by
    apply nat_mul_lt_cancel_left (2 ^ aPos * 2 ^ aNeg) _ _
      (Nat.mul_le_mul (pow2_pos_nat aPos) (pow2_pos_nat aNeg))
    have hl : (2 ^ aPos * 2 ^ aNeg) * (4 ^ aPos * 5 ^ cNeg) =
        (2 ^ aPos * 4 ^ aPos) * (2 ^ aNeg * 5 ^ cNeg) := by
      calc
        (2 ^ aPos * 2 ^ aNeg) * (4 ^ aPos * 5 ^ cNeg)
            = 2 ^ aPos * (2 ^ aNeg * (4 ^ aPos * 5 ^ cNeg)) := Nat.mul_assoc _ _ _
        _ = 2 ^ aPos * ((2 ^ aNeg * 4 ^ aPos) * 5 ^ cNeg) := by rw [← Nat.mul_assoc (2 ^ aNeg)]
        _ = 2 ^ aPos * ((4 ^ aPos * 2 ^ aNeg) * 5 ^ cNeg) := by rw [Nat.mul_comm (2 ^ aNeg) (4 ^ aPos)]
        _ = (2 ^ aPos * 4 ^ aPos) * (2 ^ aNeg * 5 ^ cNeg) := by
              rw [Nat.mul_assoc (4 ^ aPos), ← Nat.mul_assoc (2 ^ aPos)]
    have hr : (2 ^ aPos * 2 ^ aNeg) * (5 ^ cPos * 4 ^ aNeg) =
        (2 ^ aPos * 5 ^ cPos) * (2 ^ aNeg * 4 ^ aNeg) := by
      calc
        (2 ^ aPos * 2 ^ aNeg) * (5 ^ cPos * 4 ^ aNeg)
            = 2 ^ aPos * (2 ^ aNeg * (5 ^ cPos * 4 ^ aNeg)) := Nat.mul_assoc _ _ _
        _ = 2 ^ aPos * ((2 ^ aNeg * 5 ^ cPos) * 4 ^ aNeg) := by rw [← Nat.mul_assoc (2 ^ aNeg)]
        _ = 2 ^ aPos * ((5 ^ cPos * 2 ^ aNeg) * 4 ^ aNeg) := by rw [Nat.mul_comm (2 ^ aNeg) (5 ^ cPos)]
        _ = (2 ^ aPos * 5 ^ cPos) * (2 ^ aNeg * 4 ^ aNeg) := by
              rw [Nat.mul_assoc (5 ^ cPos), ← Nat.mul_assoc (2 ^ aPos)]
    rw [hl, hr]; exact h9
  -- 3. From `17 -> 13`: `7^cPos * 9^bNeg < 9^bPos * 7^cNeg`:
  have h3_ineq : 7 ^ cPos * 9 ^ bNeg < 9 ^ bPos * 7 ^ cNeg := by
    apply nat_mul_lt_cancel_left (2 ^ aPos * 2 ^ aNeg) _ _
      (Nat.mul_le_mul (pow2_pos_nat aPos) (pow2_pos_nat aNeg))
    have hl : (2 ^ aPos * 2 ^ aNeg) * (7 ^ cPos * 9 ^ bNeg) =
        (2 ^ aPos * 7 ^ cPos) * (2 ^ aNeg * 9 ^ bNeg) := by
      calc
        (2 ^ aPos * 2 ^ aNeg) * (7 ^ cPos * 9 ^ bNeg)
            = 2 ^ aPos * (2 ^ aNeg * (7 ^ cPos * 9 ^ bNeg)) := Nat.mul_assoc _ _ _
        _ = 2 ^ aPos * ((2 ^ aNeg * 7 ^ cPos) * 9 ^ bNeg) := by rw [← Nat.mul_assoc (2 ^ aNeg)]
        _ = 2 ^ aPos * ((7 ^ cPos * 2 ^ aNeg) * 9 ^ bNeg) := by rw [Nat.mul_comm (2 ^ aNeg) (7 ^ cPos)]
        _ = (2 ^ aPos * 7 ^ cPos) * (2 ^ aNeg * 9 ^ bNeg) := by
              rw [Nat.mul_assoc (7 ^ cPos), ← Nat.mul_assoc (2 ^ aPos)]
    have hr : (2 ^ aPos * 2 ^ aNeg) * (9 ^ bPos * 7 ^ cNeg) =
        (2 ^ aPos * 9 ^ bPos) * (2 ^ aNeg * 7 ^ cNeg) := by
      calc
        (2 ^ aPos * 2 ^ aNeg) * (9 ^ bPos * 7 ^ cNeg)
            = 2 ^ aPos * (2 ^ aNeg * (9 ^ bPos * 7 ^ cNeg)) := Nat.mul_assoc _ _ _
        _ = 2 ^ aPos * ((2 ^ aNeg * 9 ^ bPos) * 7 ^ cNeg) := by rw [← Nat.mul_assoc (2 ^ aNeg)]
        _ = 2 ^ aPos * ((9 ^ bPos * 2 ^ aNeg) * 7 ^ cNeg) := by rw [Nat.mul_comm (2 ^ aNeg) (9 ^ bPos)]
        _ = (2 ^ aPos * 9 ^ bPos) * (2 ^ aNeg * 7 ^ cNeg) := by
              rw [Nat.mul_assoc (9 ^ bPos), ← Nat.mul_assoc (2 ^ aPos)]
    rw [hl, hr]; exact h17
  -- 4. From `97 -> 73`: `37^cPos * 49^cNeg < 49^cPos * 37^cNeg`, forcing `cNeg < cPos`:
  have h4_ineq : 37 ^ cPos * 49 ^ cNeg < 49 ^ cPos * 37 ^ cNeg := by
    apply nat_mul_lt_cancel_left (2 ^ aPos * 2 ^ aNeg) _ _
      (Nat.mul_le_mul (pow2_pos_nat aPos) (pow2_pos_nat aNeg))
    have hl : (2 ^ aPos * 2 ^ aNeg) * (37 ^ cPos * 49 ^ cNeg) =
        (2 ^ aPos * 37 ^ cPos) * (2 ^ aNeg * 49 ^ cNeg) := by
      calc
        (2 ^ aPos * 2 ^ aNeg) * (37 ^ cPos * 49 ^ cNeg)
            = 2 ^ aPos * (2 ^ aNeg * (37 ^ cPos * 49 ^ cNeg)) := Nat.mul_assoc _ _ _
        _ = 2 ^ aPos * ((2 ^ aNeg * 37 ^ cPos) * 49 ^ cNeg) := by rw [← Nat.mul_assoc (2 ^ aNeg)]
        _ = 2 ^ aPos * ((37 ^ cPos * 2 ^ aNeg) * 49 ^ cNeg) := by rw [Nat.mul_comm (2 ^ aNeg) (37 ^ cPos)]
        _ = (2 ^ aPos * 37 ^ cPos) * (2 ^ aNeg * 49 ^ cNeg) := by
              rw [Nat.mul_assoc (37 ^ cPos), ← Nat.mul_assoc (2 ^ aPos)]
    have hr : (2 ^ aPos * 2 ^ aNeg) * (49 ^ cPos * 37 ^ cNeg) =
        (2 ^ aPos * 49 ^ cPos) * (2 ^ aNeg * 37 ^ cNeg) := by
      calc
        (2 ^ aPos * 2 ^ aNeg) * (49 ^ cPos * 37 ^ cNeg)
            = 2 ^ aPos * (2 ^ aNeg * (49 ^ cPos * 37 ^ cNeg)) := Nat.mul_assoc _ _ _
        _ = 2 ^ aPos * ((2 ^ aNeg * 49 ^ cPos) * 37 ^ cNeg) := by rw [← Nat.mul_assoc (2 ^ aNeg)]
        _ = 2 ^ aPos * ((49 ^ cPos * 2 ^ aNeg) * 37 ^ cNeg) := by rw [Nat.mul_comm (2 ^ aNeg) (49 ^ cPos)]
        _ = (2 ^ aPos * 49 ^ cPos) * (2 ^ aNeg * 37 ^ cNeg) := by
              rw [Nat.mul_assoc (49 ^ cPos), ← Nat.mul_assoc (2 ^ aPos)]
    rw [hl, hr]; exact h97
  have hc_lt : cNeg < cPos := by
    by_cases h : cNeg < cPos
    · exact h
    · let d := cNeg - cPos
      have hd_eq : cNeg = cPos + d := by dsimp [d]; omega
      rw [hd_eq, Nat.pow_add 49 cPos d, Nat.pow_add 37 cPos d] at h4_ineq
      have hge_d : 37 ^ d ≤ 49 ^ d := nat_pow_mono_base 37 49 (by decide) d
      have hge_tot : 49 ^ cPos * (37 ^ cPos * 37 ^ d) ≤ 37 ^ cPos * (49 ^ cPos * 49 ^ d) := by
        have hcomm : 49 ^ cPos * (37 ^ cPos * 37 ^ d) = (37 ^ cPos * 49 ^ cPos) * 37 ^ d := by
          rw [← Nat.mul_assoc, Nat.mul_comm (49 ^ cPos) (37 ^ cPos)]
        have hcomm2 : 37 ^ cPos * (49 ^ cPos * 49 ^ d) = (37 ^ cPos * 49 ^ cPos) * 49 ^ d :=
          (Nat.mul_assoc _ _ _).symm
        rw [hcomm, hcomm2]
        exact Nat.mul_le_mul_left _ hge_d
      omega
  -- Chain `h1_sq` & `h2_ineq` -> `9^bPos * 5^cNeg < 9^bNeg * 5^cPos`, then with `h3_ineq` -> `7^cPos * 5^cNeg < 5^cPos * 7^cNeg`:
  have h12 : 9 ^ bPos * 5 ^ cNeg < 9 ^ bNeg * 5 ^ cPos := by
    have hp := nat_mul_lt_mul_pos _ _ _ _ h1_sq h2_ineq
    apply nat_mul_lt_cancel_left (4 ^ aPos * 4 ^ aNeg) _ _
      (Nat.mul_le_mul (nat_pow_pos_of_pos 4 (by decide) aPos) (nat_pow_pos_of_pos 4 (by decide) aNeg))
    have hl : (4 ^ aPos * 4 ^ aNeg) * (9 ^ bPos * 5 ^ cNeg) =
        (9 ^ bPos * 4 ^ aNeg) * (4 ^ aPos * 5 ^ cNeg) := by
      calc
        (4 ^ aPos * 4 ^ aNeg) * (9 ^ bPos * 5 ^ cNeg)
            = 4 ^ aPos * (4 ^ aNeg * (9 ^ bPos * 5 ^ cNeg)) := Nat.mul_assoc _ _ _
        _ = 4 ^ aPos * ((4 ^ aNeg * 9 ^ bPos) * 5 ^ cNeg) := by rw [← Nat.mul_assoc (4 ^ aNeg)]
        _ = 4 ^ aPos * ((9 ^ bPos * 4 ^ aNeg) * 5 ^ cNeg) := by rw [Nat.mul_comm (4 ^ aNeg) (9 ^ bPos)]
        _ = (4 ^ aPos * (9 ^ bPos * 4 ^ aNeg)) * 5 ^ cNeg := by rw [← Nat.mul_assoc (4 ^ aPos)]
        _ = ((9 ^ bPos * 4 ^ aNeg) * 4 ^ aPos) * 5 ^ cNeg := by rw [Nat.mul_comm (4 ^ aPos) (9 ^ bPos * 4 ^ aNeg)]
        _ = (9 ^ bPos * 4 ^ aNeg) * (4 ^ aPos * 5 ^ cNeg) := Nat.mul_assoc _ _ _
    have hr : (4 ^ aPos * 4 ^ aNeg) * (9 ^ bNeg * 5 ^ cPos) =
        (4 ^ aPos * 9 ^ bNeg) * (5 ^ cPos * 4 ^ aNeg) := by
      calc
        (4 ^ aPos * 4 ^ aNeg) * (9 ^ bNeg * 5 ^ cPos)
            = 4 ^ aPos * (4 ^ aNeg * (9 ^ bNeg * 5 ^ cPos)) := Nat.mul_assoc _ _ _
        _ = 4 ^ aPos * (9 ^ bNeg * (4 ^ aNeg * 5 ^ cPos)) := by
              rw [← Nat.mul_assoc (4 ^ aNeg), Nat.mul_comm (4 ^ aNeg) (9 ^ bNeg), Nat.mul_assoc (9 ^ bNeg)]
        _ = 4 ^ aPos * (9 ^ bNeg * (5 ^ cPos * 4 ^ aNeg)) := by rw [Nat.mul_comm (4 ^ aNeg) (5 ^ cPos)]
        _ = (4 ^ aPos * 9 ^ bNeg) * (5 ^ cPos * 4 ^ aNeg) := (Nat.mul_assoc _ _ _).symm
    rw [hl, hr]; exact hp
  have h123 : 7 ^ cPos * 5 ^ cNeg < 5 ^ cPos * 7 ^ cNeg := by
    have hp := nat_mul_lt_mul_pos _ _ _ _ h12 h3_ineq
    apply nat_mul_lt_cancel_left (9 ^ bPos * 9 ^ bNeg) _ _
      (Nat.mul_le_mul (nat_pow_pos_of_pos 9 (by decide) bPos) (nat_pow_pos_of_pos 9 (by decide) bNeg))
    have hl : (9 ^ bPos * 9 ^ bNeg) * (7 ^ cPos * 5 ^ cNeg) =
        (9 ^ bPos * 5 ^ cNeg) * (7 ^ cPos * 9 ^ bNeg) := by
      calc
        (9 ^ bPos * 9 ^ bNeg) * (7 ^ cPos * 5 ^ cNeg)
            = 9 ^ bPos * (9 ^ bNeg * (7 ^ cPos * 5 ^ cNeg)) := Nat.mul_assoc _ _ _
        _ = 9 ^ bPos * ((7 ^ cPos * 9 ^ bNeg) * 5 ^ cNeg) := by
              rw [← Nat.mul_assoc (9 ^ bNeg), Nat.mul_comm (9 ^ bNeg) (7 ^ cPos)]
        _ = 9 ^ bPos * (5 ^ cNeg * (7 ^ cPos * 9 ^ bNeg)) := by rw [Nat.mul_comm _ (5 ^ cNeg)]
        _ = (9 ^ bPos * 5 ^ cNeg) * (7 ^ cPos * 9 ^ bNeg) := (Nat.mul_assoc _ _ _).symm
    have hr : (9 ^ bPos * 9 ^ bNeg) * (5 ^ cPos * 7 ^ cNeg) =
        (9 ^ bNeg * 5 ^ cPos) * (9 ^ bPos * 7 ^ cNeg) := by
      calc
        (9 ^ bPos * 9 ^ bNeg) * (5 ^ cPos * 7 ^ cNeg)
            = (9 ^ bNeg * 9 ^ bPos) * (5 ^ cPos * 7 ^ cNeg) := by rw [Nat.mul_comm (9 ^ bPos)]
        _ = 9 ^ bNeg * (9 ^ bPos * (5 ^ cPos * 7 ^ cNeg)) := Nat.mul_assoc _ _ _
        _ = 9 ^ bNeg * (5 ^ cPos * (9 ^ bPos * 7 ^ cNeg)) := by
              rw [← Nat.mul_assoc (9 ^ bPos), Nat.mul_comm (9 ^ bPos) (5 ^ cPos), Nat.mul_assoc (5 ^ cPos)]
        _ = (9 ^ bNeg * 5 ^ cPos) * (9 ^ bPos * 7 ^ cNeg) := (Nat.mul_assoc _ _ _).symm
    rw [hl, hr]; exact hp
  let d := cPos - cNeg
  have hd_eq : cPos = cNeg + d := by dsimp [d]; omega
  rw [hd_eq, Nat.pow_add 7 cNeg d, Nat.pow_add 5 cNeg d] at h123
  have h5_le_7 : 5 ^ d ≤ 7 ^ d := nat_pow_mono_base 5 7 (by decide) d
  have hge_57 : (5 ^ cNeg * 5 ^ d) * 7 ^ cNeg ≤ (7 ^ cNeg * 7 ^ d) * 5 ^ cNeg := by
    have hc1 : (5 ^ cNeg * 5 ^ d) * 7 ^ cNeg = (5 ^ cNeg * 7 ^ cNeg) * 5 ^ d := by
      rw [Nat.mul_assoc, Nat.mul_comm (5 ^ d) (7 ^ cNeg), ← Nat.mul_assoc]
    have hc2 : (7 ^ cNeg * 7 ^ d) * 5 ^ cNeg = (5 ^ cNeg * 7 ^ cNeg) * 7 ^ d := by
      rw [Nat.mul_comm _ (5 ^ cNeg), ← Nat.mul_assoc]
    rw [hc1, hc2]
    exact Nat.mul_le_mul_left _ h5_le_7
  omega

-- ----------------------------------------------------------------------------
-- W4.5b: Sharp `w ≥ 6` Weight Floor on `exactBackwardQuotient 1 u q` Inside
--        `IsSurvivingMod373248Class` + `y = 184,111` Sharpness Certificate
-- ----------------------------------------------------------------------------

theorem parityOfIter_mod_pow2_shift :
    ∀ (k y m : Nat), parityOfIter k (y + 2 ^ k * m) = parityOfIter k y
  | 0, _, _ => rfl
  | k + 1, y, m => by
    have hp : 2 ^ (k + 1) * m = 2 * (2 ^ k * m) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
    rw [hp]
    simp only [parityOfIter]
    by_cases hev : y % 2 = 0
    · have hb_y : (y % 2 == 0) = true := decide_eq_true hev
      have hb_ym : ((y + 2 * (2 ^ k * m)) % 2 == 0) = true := decide_eq_true (by omega)
      rw [hb_y, hb_ym]
      simp only [ite_true, List.cons.injEq, true_and]
      have hstep : collatzStep (y + 2 * (2 ^ k * m)) = collatzStep y + 2 ^ k * m := by
        unfold collatzStep
        rw [hb_y, hb_ym]
        simp only [ite_true]
        omega
      rw [hstep]
      exact parityOfIter_mod_pow2_shift k (collatzStep y) m
    · have hb_y : (y % 2 == 0) = false := decide_eq_false hev
      have hb_ym : ((y + 2 * (2 ^ k * m)) % 2 == 0) = false := decide_eq_false (by omega)
      rw [hb_y, hb_ym]
      simp only [Bool.false_eq_true, ite_false, List.cons.injEq, true_and]
      have hstep : collatzStep (y + 2 * (2 ^ k * m)) = collatzStep y + 2 ^ k * (3 * m) := by
        unfold collatzStep
        rw [hb_y, hb_ym]
        simp only [Bool.false_eq_true, ite_false]
        have hmul : 3 * (2 * (2 ^ k * m)) = 2 * (2 ^ k * (3 * m)) := by
          calc
            3 * (2 * (2 ^ k * m)) = 2 * (3 * (2 ^ k * m)) := by
              rw [← Nat.mul_assoc, Nat.mul_comm 3 2, Nat.mul_assoc]
            _ = 2 * (2 ^ k * (3 * m)) := by
              rw [← Nat.mul_assoc 3 (2 ^ k) m, Nat.mul_comm 3 (2 ^ k), Nat.mul_assoc]
        omega
      rw [hstep]
      exact parityOfIter_mod_pow2_shift k (collatzStep y) (3 * m)

theorem survivingMod512_imp_bool_true (r : Nat) (h : IsSurvivingMod512Residue r) :
    isSurvivingMod512Bool r = true := by
  rcases h with ⟨hlt, h64, h128_7, h128_59, h128_95,
    h256_39, h256_63, h256_123, h256_175, h256_199, h256_219,
    h287, h367, h383, h411, h487⟩
  unfold isSurvivingMod512Bool
  have hb64 : isSurvivingMod64Bool (r % 64) = true := by
    unfold IsSurvivingMod64Residue at h64
    unfold isSurvivingMod64Bool
    rcases h64 with h | h | h | h | h | h | h <;> simp [h]
  simp [hlt, hb64, h128_7, h128_59, h128_95,
        h256_39, h256_63, h256_123, h256_175, h256_199, h256_219,
        h287, h367, h383, h411, h487]

theorem survivingMod512Bool_nine_step_weight_ge_six_grid :
    ∀ (i : Fin 16) (j : Fin 32),
      isSurvivingMod512Bool (32 * i.val + j.val) = true ->
      parityWeight (parityOfIter 9 (32 * i.val + j.val)) ≥ 6 := by
  decide

theorem survivingMod512Bool_nine_step_weight_ge_six (r : Nat) (hr : r < 512)
    (hb : isSurvivingMod512Bool r = true) :
    parityWeight (parityOfIter 9 r) ≥ 6 := by
  have hi : r / 32 < 16 := by omega
  have hj : r % 32 < 32 := Nat.mod_lt r (by decide)
  have hsplit : 32 * (r / 32) + r % 32 = r := Nat.div_add_mod r 32
  have hg := survivingMod512Bool_nine_step_weight_ge_six_grid ⟨r / 32, hi⟩ ⟨r % 32, hj⟩
  dsimp only at hg
  rw [hsplit] at hg
  exact hg hb

/--
  Theorem W4.5b (`one_generator_weight_le_five_never_surviving_mod373248`, `[]` axioms):
  Unconditional Sharp Forward Weight Elimination on `exactBackwardQuotient 1 u q`:
  Strengthening Wave 3's `w ≤ 2` bound (`one_generator_weight_le_two_never_surviving_mod1296`),
  EVERY core parity word `u` with `parityWeight u ≤ 5` has `exactBackwardQuotient 1 u q`
  universally disjoint from `IsSurvivingMod373248Class` across ALL `q : Nat`!
-/
theorem one_generator_weight_le_five_never_surviving_mod373248
    (u : List Bool) (q : Nat)
    (hu : IsCoreParityWord u) (hw : parityWeight u ≤ 5) :
    ¬ IsSurvivingMod373248Class (exactBackwardQuotient 1 u q) := by
  intro hs
  by_cases hw2 : parityWeight u ≤ 2
  · exact (one_generator_weight_le_two_never_surviving_mod1296 u q hu (Or.inl hw2)).2.2.2.2 hs
  · have hw_ge3 : parityWeight u ≥ 3 := by omega
    let y := exactBackwardQuotient 1 u q
    let K := backwardOneTotalSteps u q
    have hy_ge27 : y ≥ 27 := survivingMod373248_ge_27 y hs
    rcases one_generator_pos_odd_and_reaches_one u q hu with ⟨_, _, heq, _⟩
    change 2 ^ K = 3 ^ parityWeight u * y + affineCarry u at heq
    have hp3_ge27 : 3 ^ parityWeight u ≥ 27 := by
      have hsplit : parityWeight u = 3 + (parityWeight u - 3) := by omega
      rw [hsplit, Nat.pow_add]
      have hp0 := pow3_pos_nat (parityWeight u - 3)
      have h27 : (3 : Nat) ^ 3 = 27 := rfl
      rw [h27]
      have hm := Nat.mul_le_mul_left 27 hp0
      omega
    have h2K_ge : 2 ^ K ≥ 729 := by
      have hm := Nat.mul_le_mul hp3_ge27 hy_ge27
      omega
    have hK_ge9 : K ≥ 9 := by
      by_cases hlt9 : K < 9
      · have hle8 : 2 ^ K ≤ 2 ^ 8 := pow2_mono_nat (by omega : K ≤ 8)
        have h256 : (2 : Nat) ^ 8 = 256 := rfl
        rw [h256] at hle8
        omega
      · omega
    let shift := canonicalSuffixShift u 1 + q * (2 * 3 ^ (parityWeight u - 1))
    let v := u ++ List.replicate shift false
    have hv_len : v.length = K := by
      dsimp [v, K]; unfold backwardOneTotalSteps; rw [List.length_append, List.length_replicate]
    rcases affineCarry_append_replicate_false u shift with ⟨hwt_v, hcar_v⟩
    have hv_aff : 2 ^ v.length * 1 = 3 ^ parityWeight v * y + affineCarry v := by
      rw [Nat.mul_one, hv_len, hwt_v, hcar_v]; exact heq
    have hv_par := eq_parityOfIter_of_nat_affine v y 1 hv_aff
    rw [hv_len] at hv_par
    have hwt_K : parityWeight (parityOfIter K y) = parityWeight u := by
      rw [← hv_par, hwt_v]
    have hK_split : K = 9 + (K - 9) := by omega
    have hpar_split : parityOfIter K y =
        parityOfIter 9 y ++ parityOfIter (K - 9) (collatzIter 9 y) := by
      conv => lhs; rw [hK_split]
      exact parityOfIter_append_split 9 (K - 9) y
    have hwt_ge_9 : parityWeight (parityOfIter 9 y) ≤ parityWeight u := by
      rw [← hwt_K, hpar_split, parityWeight_append]
      omega
    have hy_div : y = y % 512 + 2 ^ 9 * (y / 512) := by
      have hdm := (Nat.div_add_mod y 512).symm
      have h512 : (2 : Nat) ^ 9 = 512 := rfl
      rw [h512]; omega
    have hpar9_mod : parityOfIter 9 y = parityOfIter 9 (y % 512) := by
      conv => lhs; rw [hy_div]
      exact parityOfIter_mod_pow2_shift 9 (y % 512) (y / 512)
    have hb512 : isSurvivingMod512Bool (y % 512) = true :=
      survivingMod512_imp_bool_true (y % 512) hs.1
    have hw9_ge6 : parityWeight (parityOfIter 9 (y % 512)) ≥ 6 :=
      survivingMod512Bool_nine_step_weight_ge_six (y % 512) (Nat.mod_lt y (by decide)) hb512
    rw [← hpar9_mod] at hw9_ge6
    omega

/--
  Sharpened Unique First-Hit Range Target (`Mod373248UniqueFirstHitWeightGeSixProp`):
  Discharges the entire `w ∈ {3, 4, 5}` sector of `Mod373248UniqueFirstHitRangeProp`
  unconditionally via `W4.5b` (`one_generator_weight_le_five_never_surviving_mod373248`).
-/
def Mod373248UniqueFirstHitWeightGeSixProp : Prop :=
  ∀ n : Nat, IsSurvivingMod373248Class n ->
    ∃ (tail : List Bool) (q : Nat),
      IsFirstHitOnePair (true :: true :: tail) q ∧
      parityWeight (true :: true :: tail) ≥ 6 ∧
      exactBackwardQuotient 1 (true :: true :: tail) q = n

/--
  Theorem W4.5c (`collatz_standard_iff_mod373248_unique_first_hit_weight_ge_six`, `[]` axioms):
  Upgrades `T3.16b` (`collatz_standard_iff_mod373248_unique_first_hit_range`) from `w ≥ 3`
  to the sharp weight floor `w ≥ 6` using the unconditional forward elimination `W4.5b`.
-/
theorem collatz_standard_iff_mod373248_unique_first_hit_weight_ge_six :
    CollatzConjectureStandard ↔ Mod373248UniqueFirstHitWeightGeSixProp := by
  rw [collatz_standard_iff_mod373248_unique_first_hit_range]
  constructor
  · intro hprop n hs
    rcases hprop n hs with ⟨tail, q, hfh, _, hy_eq⟩
    have hw_ge6 : parityWeight (true :: true :: tail) ≥ 6 := by
      by_cases hge : parityWeight (true :: true :: tail) ≥ 6
      · exact hge
      · have hdisj := one_generator_weight_le_five_never_surviving_mod373248
            (true :: true :: tail) q hfh.1 (by omega)
        rw [hy_eq] at hdisj
        exact False.elim (hdisj hs)
    exact ⟨tail, q, hfh, hw_ge6, hy_eq⟩
  · intro hprop n hs
    rcases hprop n hs with ⟨tail, q, hfh, hw_ge6, hy_eq⟩
    exact ⟨tail, q, hfh, by omega, hy_eq⟩

/--
  Theorem W4.5d (`mod373248_min_weight_six_witness_184111`, `[]` axioms):
  Sharpness Certificate for `W4.5b`–`W4.5c`: at
  `u = [true, true, true, true, false, true, false, true]` and `q = 0`,
  `parityWeight u = 6`, `backwardOneTotalSteps u 0 = 27`, and
  `exactBackwardQuotient 1 u 0 = 184111` IS a valid unique first-hit pair lying
  inside `IsSurvivingMod373248Class`, proving `w ≥ 6` is exact!
-/
theorem mod373248_min_weight_six_witness_184111 :
    let u := [true, true, true, true, false, true, false, true]
    parityWeight u = 6 ∧
    exactBackwardQuotient 1 u 0 = 184111 ∧
    backwardOneTotalSteps u 0 = 27 ∧
    isSurvivingMod512Bool (184111 % 512) = true ∧
    isSurvivingMod729Bool (184111 % 729) = true ∧
    IsSurvivingMod373248Class 184111 ∧
    IsFirstHitOnePair u 0 := by
  dsimp only
  refine ⟨rfl, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · unfold IsSurvivingMod512Residue IsSurvivingMod64Residue
      decide
    · unfold IsSurvivingMod729Residue
      decide
  · refine ⟨⟨rfl, rfl⟩, ?_⟩
    have hsteps : backwardOneTotalSteps [true, true, true, true, false, true, false, true] 0 = 27 := by
      decide
    have hquot : exactBackwardQuotient 1 [true, true, true, true, false, true, false, true] 0 = 184111 := by
      decide
    rw [hsteps, hquot]
    have hall : ∀ k : Fin 27, collatzIter k.val 184111 ≠ 1 := by decide
    intro k hk
    exact hall ⟨k, hk⟩

end CollatzFormal
