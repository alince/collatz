/-
  CollatzFormal/Wave5WholeSpace.lean
  Wave 5 Whole-Space Mathematical & CS Proof Loop:
  1. Front A — Non-Radial Berg–Meinardus Preimage Superharmonicity (Branch P1.2):
     - `nat_valued_preimage_weight_impossibility` (zero custom axioms): refutes all positive
       `Nat`-valued preimage weights via `4^(k+1)` spine drain.
     - `preimage_superharmonic_rational_eliminates_all_cycles` &
       `strictly_contractive_bounded_preimage_weight_implies_collatz_standard` (zero custom axioms):
       exact cleared-denominator rational meta-theorems discharging `NoNontrivialPositiveCycles`
       across ALL `m`-block cycles (`∀ m ≥ 1`) at `θ ≤ 1`, and `CollatzConjectureStandard`
       under bounded strict contraction `θ < 1`.
     - `berg_meinardus_periodic_valuation_weight_impossibility` &
       `berg_meinardus_reciprocal_multiterm_laurent_impossibility` (zero custom axioms): universal
       non-radial barriers refuting all `(v_2(n), v_3(n), v_2(n+1), v_3(n+1), n % P)`
       rational preimage weights (`∀ P ≥ 1`) and all reciprocal `L`-term Laurent valuation sums.
  2. Front B — Solvable Cousin `T_diamond2`, Non-Upper-Triangular Matrix Collapse, &
     Universal Multi-Term Laurent Valuation Impossibility (Branches P4.2, P4.3, P5.4):
     - `all_dim_coord_monotone_non_triangular_impossibility` (zero custom axioms): drops
       upper-triangularity completely across ALL dimensions `∀ d ≥ 1` via `L * (·) * R`
       sandwiching on `{R2, R5, R7, R8, R9, R11}`.
     - `cousin_diamond2_global_convergence`, `cousin_diamond2_single_laurent_monomial_impossibility`,
       `cousinDiamond2StepInt_ofNat_eq`, & `cousin_diamond2_counter_model_separation` (zero custom axioms).
     - `two_term_valuation_sum_survives_w4_witnesses_yet_fails_syracuse` &
       `syracuse_multiterm_laurent_valuation_impossibility` (`∀ L ≥ 1`, zero custom axioms).
  3. Front C — General `∀ m ≥ 1` `m`-Block Spiral Resultants & Antipodal Divisor Exclusion
     (Branches P3.2, P3.3, P3.4):
     - `broxSpiralCarry_eq_affineCarry_universal`, `m_block_brox_resultant_and_quotient_locks`,
       & `m_block_cycle_induces_brox_quotients` (zero custom axioms).
     - `one_block_even_even_impossibility`, `one_block_antipodal_order_divisor_exclusion`, &
       `one_block_antipodal_prime_instances_and_m1_separation` (zero custom axioms).
  4. Front D — Coupled `q`-Ray Covering, Sharp `|u| ≥ 8` Floor, & `Π₂⁰` Skolem Calibration
     (Branches P5.3 & P4.4):
     - `exactBackwardQuotient_one_ray_step_law`, `one_generator_q_pos_always_first_hit`, &
       `mod373248_ray_dyadic_pinning_and_triadic_bijection` (zero custom axioms).
     - `one_generator_length_le_seven_never_surviving_mod373248`,
       `collatz_standard_iff_mod373248_unique_first_hit_len_ge_eight`, &
       `pi2_skolem_box_equivalence_and_cousin_polynomial_stopping_bound` (zero custom axioms).

  Zero external dependencies (pure Lean 4.35.0 Core), zero `sorry`,
  zero `native_decide`, zero custom `axiom`.
-/

import CollatzFormal.Wave4WholeSpace

namespace CollatzFormal

-- ============================================================================
-- SECTION 1: Front A — Non-Radial Berg–Meinardus Preimage Superharmonicity
--            Meta-Theorems & Periodic-Valuation Barrier (Zero Custom Axioms)
-- ============================================================================

theorem pow4_ge_four_and_mod3_w5 : ∀ k : Nat, 4 ^ (k + 1) ≥ 4 ∧ 4 ^ (k + 1) % 3 = 1
  | 0 => ⟨by decide, by decide⟩
  | k + 1 => by
    rcases pow4_ge_four_and_mod3_w5 k with ⟨hge, hm3⟩
    rw [Nat.pow_succ]
    refine ⟨by omega, ?_⟩
    rw [Nat.mul_mod, hm3]

/--
  Theorem W5.1a (`nat_valued_preimage_weight_impossibility`, zero custom axioms):
  No strictly positive `Nat`-valued weight `w : Nat -> Nat` (`∀ n ≥ 3, w n > 0`)
  can satisfy Berg–Meinardus preimage subadditivity on `{m ≥ 3}`, because along
  the 4-adic spine `m_k = 4^(k + 1)`, every `2 * m_k ≡ 2 (mod 3)` drains at least
  `w ((4^(k+2) - 1) / 3) ≥ 1`, forcing `w (4^(k+1)) + k ≤ w 4` for all `k`.
  This justifies formalizing preimage weights via cleared-denominator rationals `(wNum, wDen)`.
-/
theorem nat_valued_preimage_weight_impossibility
    (w : Nat -> Nat)
    (hw_pos : ∀ n : Nat, n ≥ 3 -> w n > 0)
    (hpre : ∀ m : Nat, m ≥ 3 ->
      w (2 * m) + (if m % 3 = 2 then w ((2 * m - 1) / 3) else 0) ≤ w m) :
    False := by
  have hstep : ∀ k : Nat, w (4 ^ (k + 2)) + 1 ≤ w (4 ^ (k + 1)) := by
    intro k
    rcases pow4_ge_four_and_mod3_w5 k with ⟨hge, hm3⟩
    let mk := 4 ^ (k + 1)
    have hmk_ge : mk ≥ 4 := hge
    have hmk_m3 : mk % 3 = 1 := hm3
    have h1 := hpre mk (by omega)
    have h2 := hpre (2 * mk) (by omega)
    have hm2_mod3 : (2 * mk) % 3 = 2 := by omega
    simp only [hm2_mod3, ite_true] at h2
    have hnodd_ge3 : (2 * (2 * mk) - 1) / 3 ≥ 3 := by omega
    have hw_odd : w ((2 * (2 * mk) - 1) / 3) ≥ 1 := hw_pos _ hnodd_ge3
    have h4mk : 2 * (2 * mk) = 4 ^ (k + 2) := by
      dsimp [mk]
      rw [Nat.pow_succ 4 (k + 1)]
      omega
    rw [h4mk] at h2 hw_odd
    change w (4 ^ (k + 2)) + 1 ≤ w mk
    omega
  have hind : ∀ k : Nat, w (4 ^ (k + 1)) + k ≤ w 4 := by
    intro k
    induction k with
    | zero => simp
    | succ k' ih =>
      have hs := hstep k'
      have hexp : k' + 1 + 1 = k' + 2 := rfl
      rw [hexp]
      omega
  have hbad := hind (w 4 + 1)
  omega

/--
  Positive cleared-denominator rational Berg–Meinardus preimage weight
  `w(n) = wNum n / wDen n > 0` on `n ≥ 3` with contraction factor `θ = pTheta / qTheta ≤ 1`:
  `w(2m) + 1_{m ≡ 2 mod 3} * w((2m - 1) / 3) ≤ (pTheta / qTheta) * w(m)` for all `m ≥ 3`.
-/
def IsPositiveRationalPreimageWeight
    (wNum wDen : Nat -> Nat) (pTheta qTheta : Nat) : Prop :=
  0 < pTheta ∧ pTheta ≤ qTheta ∧
  (∀ n : Nat, n ≥ 3 -> wNum n > 0 ∧ wDen n > 0) ∧
  (∀ m : Nat, m ≥ 3 -> m % 3 ≠ 2 ->
    qTheta * (wNum (2 * m) * wDen m) ≤ pTheta * (wNum m * wDen (2 * m))) ∧
  (∀ m : Nat, m ≥ 3 -> m % 3 = 2 ->
    let nOdd := (2 * m - 1) / 3
    qTheta * ((wNum (2 * m) * wDen nOdd + wNum nOdd * wDen (2 * m)) * wDen m) ≤
      pTheta * (wNum m * (wDen (2 * m) * wDen nOdd)))

theorem nat_mul_le_cancel_left_w5 (k a b : Nat) (_hk : k > 0) (hle : k * a ≤ k * b) : a ≤ b := by
  by_cases h : a ≤ b
  · exact h
  · have hm := Nat.mul_lt_mul_of_pos_left (by omega : b < a) _hk
    omega

theorem nat_mul_le_cancel_right_w5 (k a b : Nat) (hk : k > 0) (hle : a * k ≤ b * k) : a ≤ b := by
  rw [Nat.mul_comm a k, Nat.mul_comm b k] at hle
  exact nat_mul_le_cancel_left_w5 k a b hk hle

theorem nat_mul_lt_cancel_right_w5 (k a b : Nat) (hk : k > 0) (hlt : a * k < b * k) : a < b := by
  rw [Nat.mul_comm a k, Nat.mul_comm b k] at hlt
  exact nat_mul_lt_cancel_left k a b hk hlt

theorem preimage_rational_forward_step_laws
    (wNum wDen : Nat -> Nat) (pTheta qTheta x : Nat)
    (hw : IsPositiveRationalPreimageWeight wNum wDen pTheta qTheta)
    (hx : x ≥ 3) (htx : collatzStep x ≥ 3) :
    let m := collatzStep x
    qTheta * (wNum x * wDen m) ≤ pTheta * (wNum m * wDen x) ∧
    wNum x * wDen m ≤ wNum m * wDen x ∧
    (x % 2 = 1 -> wNum x * wDen m < wNum m * wDen x) := by
  dsimp only
  rcases hw with ⟨hp_pos, hpq_le, hpos, hnot2, heq2⟩
  let m := collatzStep x
  change m ≥ 3 at htx
  by_cases hev : x % 2 = 0
  · have hb : (x % 2 == 0) = true := decide_eq_true hev
    have hm_eq : m = x / 2 := by dsimp [m]; unfold collatzStep; rw [hb]; simp
    have hx_2m : x = 2 * m := by omega
    have hq_ineq : qTheta * (wNum x * wDen m) ≤ pTheta * (wNum m * wDen x) := by
      by_cases hm3 : m % 3 = 2
      · have h2 := heq2 m htx hm3
        dsimp only at h2
        rw [← hx_2m] at h2
        let nOdd := (x - 1) / 3
        change qTheta * ((wNum x * wDen nOdd + wNum nOdd * wDen x) * wDen m) ≤
          pTheta * (wNum m * (wDen x * wDen nOdd)) at h2
        have hnOdd_ge3 : nOdd ≥ 3 := by dsimp [nOdd]; omega
        have hd_pos : wDen nOdd > 0 := (hpos nOdd hnOdd_ge3).2
        have hdrop : qTheta * ((wNum x * wDen nOdd) * wDen m) ≤
            pTheta * (wNum m * (wDen x * wDen nOdd)) := by
          rw [Nat.add_mul, Nat.mul_add] at h2
          omega
        have hl : qTheta * ((wNum x * wDen nOdd) * wDen m) =
            (qTheta * (wNum x * wDen m)) * wDen nOdd := by
          calc
            qTheta * ((wNum x * wDen nOdd) * wDen m)
                = qTheta * (wNum x * (wDen nOdd * wDen m)) := by rw [Nat.mul_assoc (wNum x)]
            _ = qTheta * (wNum x * (wDen m * wDen nOdd)) := by rw [Nat.mul_comm (wDen nOdd)]
            _ = qTheta * ((wNum x * wDen m) * wDen nOdd) := by rw [← Nat.mul_assoc (wNum x)]
            _ = (qTheta * (wNum x * wDen m)) * wDen nOdd := (Nat.mul_assoc _ _ _).symm
        have hr : pTheta * (wNum m * (wDen x * wDen nOdd)) =
            (pTheta * (wNum m * wDen x)) * wDen nOdd := by
          rw [← Nat.mul_assoc (wNum m), ← Nat.mul_assoc pTheta]
        rw [hl, hr] at hdrop
        exact nat_mul_le_cancel_right_w5 (wDen nOdd) _ _ hd_pos hdrop
      · have h1 := hnot2 m htx hm3
        rwa [← hx_2m] at h1
    have hle_p : pTheta * (wNum m * wDen x) ≤ qTheta * (wNum m * wDen x) :=
      Nat.mul_le_mul_right _ hpq_le
    have hbase : wNum x * wDen m ≤ wNum m * wDen x :=
      nat_mul_le_cancel_left_w5 qTheta _ _ (by omega) (Nat.le_trans hq_ineq hle_p)
    exact ⟨hq_ineq, hbase, fun hodd => by omega⟩
  · have hb : (x % 2 == 0) = false := decide_eq_false hev
    have hm_eq : m = (3 * x + 1) / 2 := by dsimp [m]; unfold collatzStep; rw [hb]; simp
    have h2m : 2 * m = 3 * x + 1 := by omega
    have hm3 : m % 3 = 2 := by omega
    have hnOdd_eq : (2 * m - 1) / 3 = x := by omega
    have h2 := heq2 m htx hm3
    dsimp only at h2
    rw [hnOdd_eq] at h2
    have h2m_ge3 : 2 * m ≥ 3 := by omega
    have hnum_2m : wNum (2 * m) > 0 := (hpos (2 * m) h2m_ge3).1
    have hden_2m : wDen (2 * m) > 0 := (hpos (2 * m) h2m_ge3).2
    have hden_x : wDen x > 0 := (hpos x hx).2
    have hden_m : wDen m > 0 := (hpos m htx).2
    have hextra_pos : qTheta * ((wNum (2 * m) * wDen x) * wDen m) > 0 :=
      Nat.mul_pos (by omega) (Nat.mul_pos (Nat.mul_pos hnum_2m hden_x) hden_m)
    have hstrict_mul : (qTheta * (wNum x * wDen m)) * wDen (2 * m) <
        (pTheta * (wNum m * wDen x)) * wDen (2 * m) := by
      have hexp : qTheta * ((wNum (2 * m) * wDen x + wNum x * wDen (2 * m)) * wDen m) =
          qTheta * ((wNum (2 * m) * wDen x) * wDen m) +
            qTheta * ((wNum x * wDen (2 * m)) * wDen m) := by
        rw [Nat.add_mul, Nat.mul_add]
      have hl : qTheta * ((wNum x * wDen (2 * m)) * wDen m) =
          (qTheta * (wNum x * wDen m)) * wDen (2 * m) := by
        calc
          qTheta * ((wNum x * wDen (2 * m)) * wDen m)
              = qTheta * (wNum x * (wDen (2 * m) * wDen m)) := by rw [Nat.mul_assoc (wNum x)]
          _ = qTheta * (wNum x * (wDen m * wDen (2 * m))) := by rw [Nat.mul_comm (wDen (2 * m))]
          _ = qTheta * ((wNum x * wDen m) * wDen (2 * m)) := by rw [← Nat.mul_assoc (wNum x)]
          _ = (qTheta * (wNum x * wDen m)) * wDen (2 * m) := (Nat.mul_assoc _ _ _).symm
      have hr : pTheta * (wNum m * (wDen (2 * m) * wDen x)) =
          (pTheta * (wNum m * wDen x)) * wDen (2 * m) := by
        calc
          pTheta * (wNum m * (wDen (2 * m) * wDen x))
              = pTheta * (wNum m * (wDen x * wDen (2 * m))) := by rw [Nat.mul_comm (wDen (2 * m))]
          _ = pTheta * ((wNum m * wDen x) * wDen (2 * m)) := by rw [← Nat.mul_assoc (wNum m)]
          _ = (pTheta * (wNum m * wDen x)) * wDen (2 * m) := (Nat.mul_assoc _ _ _).symm
      rw [hexp, hl, hr] at h2
      omega
    have hq_lt_p : qTheta * (wNum x * wDen m) < pTheta * (wNum m * wDen x) :=
      nat_mul_lt_cancel_right_w5 (wDen (2 * m)) _ _ hden_2m hstrict_mul
    have hle_p : pTheta * (wNum m * wDen x) ≤ qTheta * (wNum m * wDen x) :=
      Nat.mul_le_mul_right _ hpq_le
    have hlt_base : wNum x * wDen m < wNum m * wDen x :=
      nat_mul_lt_cancel_left qTheta _ _ (by omega) (Nat.lt_of_lt_of_le hq_lt_p hle_p)
    exact ⟨Nat.le_of_lt hq_lt_p, Nat.le_of_lt hlt_base, fun _ => hlt_base⟩

theorem rat_le_trans_pos_w5 (a1 b1 a2 b2 a3 b3 : Nat)
    (hb2 : b2 > 0)
    (h12 : a1 * b2 ≤ a2 * b1) (h23 : a2 * b3 ≤ a3 * b2) :
    a1 * b3 ≤ a3 * b1 := by
  apply nat_mul_le_cancel_right_w5 b2 _ _ hb2
  have hl : (a1 * b3) * b2 = (a1 * b2) * b3 := by
    rw [Nat.mul_assoc, Nat.mul_comm b3 b2, ← Nat.mul_assoc]
  have hr : (a3 * b1) * b2 = (a3 * b2) * b1 := by
    rw [Nat.mul_assoc, Nat.mul_comm b1 b2, ← Nat.mul_assoc]
  have hm1 : (a1 * b2) * b3 ≤ (a2 * b1) * b3 := Nat.mul_le_mul_right b3 h12
  have hm2 : (a2 * b1) * b3 = (a2 * b3) * b1 := by
    rw [Nat.mul_assoc, Nat.mul_comm b1 b3, ← Nat.mul_assoc]
  have hm3 : (a2 * b3) * b1 ≤ (a3 * b2) * b1 := Nat.mul_le_mul_right b1 h23
  rw [hl, hr]
  omega

theorem rat_lt_le_trans_pos_w5 (a1 b1 a2 b2 a3 b3 : Nat)
    (hb2 : b2 > 0) (hb3 : b3 > 0)
    (h12 : a1 * b2 < a2 * b1) (h23 : a2 * b3 ≤ a3 * b2) :
    a1 * b3 < a3 * b1 := by
  apply nat_mul_lt_cancel_right_w5 b2 _ _ hb2
  have hl : (a1 * b3) * b2 = (a1 * b2) * b3 := by
    rw [Nat.mul_assoc, Nat.mul_comm b3 b2, ← Nat.mul_assoc]
  have hr : (a3 * b1) * b2 = (a3 * b2) * b1 := by
    rw [Nat.mul_assoc, Nat.mul_comm b1 b2, ← Nat.mul_assoc]
  have hm1 : (a1 * b2) * b3 < (a2 * b1) * b3 := Nat.mul_lt_mul_of_pos_right h12 hb3
  have hm2 : (a2 * b1) * b3 = (a2 * b3) * b1 := by
    rw [Nat.mul_assoc, Nat.mul_comm b1 b3, ← Nat.mul_assoc]
  have hm3 : (a2 * b3) * b1 ≤ (a3 * b2) * b1 := Nat.mul_le_mul_right b1 h23
  rw [hl, hr]
  omega

theorem rat_le_lt_trans_pos_w5 (a1 b1 a2 b2 a3 b3 : Nat)
    (hb1 : b1 > 0) (hb2 : b2 > 0)
    (h12 : a1 * b2 ≤ a2 * b1) (h23 : a2 * b3 < a3 * b2) :
    a1 * b3 < a3 * b1 := by
  apply nat_mul_lt_cancel_right_w5 b2 _ _ hb2
  have hl : (a1 * b3) * b2 = (a1 * b2) * b3 := by
    rw [Nat.mul_assoc, Nat.mul_comm b3 b2, ← Nat.mul_assoc]
  have hr : (a3 * b1) * b2 = (a3 * b2) * b1 := by
    rw [Nat.mul_assoc, Nat.mul_comm b1 b2, ← Nat.mul_assoc]
  have hm1 : (a1 * b2) * b3 ≤ (a2 * b1) * b3 := Nat.mul_le_mul_right b3 h12
  have hm2 : (a2 * b1) * b3 = (a2 * b3) * b1 := by
    rw [Nat.mul_assoc, Nat.mul_comm b1 b3, ← Nat.mul_assoc]
  have hm3 : (a2 * b3) * b1 < (a3 * b2) * b1 := Nat.mul_lt_mul_of_pos_right h23 hb1
  rw [hl, hr]
  omega

theorem collatzIter_pos_w5 : ∀ (k x : Nat), x ≥ 1 -> collatzIter k x ≥ 1
  | 0, _, hx => hx
  | k + 1, x, hx => by
    have hstep : collatzStep x ≥ 1 := by
      unfold collatzStep
      cases hb : (x % 2 == 0) with
      | true =>
        have hev : x % 2 = 0 := of_decide_eq_true hb
        simp only [ite_true]; omega
      | false =>
        have hodd : x % 2 ≠ 0 := of_decide_eq_false hb
        simp only [Bool.false_eq_true, ite_false]; omega
    exact collatzIter_pos_w5 k (collatzStep x) hstep

theorem preimage_iter_monotone_and_odd_strict_w5
    (wNum wDen : Nat -> Nat) (pTheta qTheta : Nat)
    (hw : IsPositiveRationalPreimageWeight wNum wDen pTheta qTheta) :
    ∀ (k x : Nat),
      (∀ j : Nat, j ≤ k -> collatzIter j x ≥ 3) ->
      wNum x * wDen (collatzIter k x) ≤ wNum (collatzIter k x) * wDen x ∧
      ((∃ j : Nat, j < k ∧ collatzIter j x % 2 = 1) ->
        wNum x * wDen (collatzIter k x) < wNum (collatzIter k x) * wDen x)
  | 0, x, _ => by
    simp only [collatzIter]
    exact ⟨Nat.le_refl _, fun ⟨_, hj, _⟩ => by omega⟩
  | k + 1, x, hall => by
    have hx3 : x ≥ 3 := hall 0 (by omega)
    have htx3 : collatzStep x ≥ 3 := by
      simpa [collatzIter] using hall 1 (by omega)
    rcases preimage_rational_forward_step_laws wNum wDen pTheta qTheta x hw hx3 htx3 with
      ⟨_, hle1, hlt1_odd⟩
    have hall_next : ∀ j : Nat, j ≤ k -> collatzIter j (collatzStep x) ≥ 3 := by
      intro j hj
      simpa [collatzIter] using hall (j + 1) (by omega)
    rcases preimage_iter_monotone_and_odd_strict_w5 wNum wDen pTheta qTheta hw
        k (collatzStep x) hall_next with ⟨hle_k, hlt_k⟩
    have hden_x : wDen x > 0 := (hw.2.2.1 x hx3).2
    have hden_tx : wDen (collatzStep x) > 0 := (hw.2.2.1 (collatzStep x) htx3).2
    have hden_end : wDen (collatzIter k (collatzStep x)) > 0 :=
      (hw.2.2.1 _ (hall_next k (Nat.le_refl k))).2
    change wNum x * wDen (collatzIter k (collatzStep x)) ≤
        wNum (collatzIter k (collatzStep x)) * wDen x ∧ _
    refine ⟨rat_le_trans_pos_w5 _ _ _ _ _ _ hden_tx hle1 hle_k, ?_⟩
    rintro ⟨j, hj_lt, hj_odd⟩
    cases j with
    | zero =>
      simp only [collatzIter] at hj_odd
      exact rat_lt_le_trans_pos_w5 _ _ _ _ _ _ hden_tx hden_end (hlt1_odd hj_odd) hle_k
    | succ j' =>
      have hj'_odd : collatzIter j' (collatzStep x) % 2 = 1 := by
        simpa [collatzIter] using hj_odd
      exact rat_le_lt_trans_pos_w5 _ _ _ _ _ _ hden_x hden_tx hle1
        (hlt_k ⟨j', by omega, hj'_odd⟩)

theorem all_even_steps_strictly_shrink_w5 :
    ∀ (p x : Nat), p ≥ 1 ->
      (∀ j : Nat, j ≤ p -> collatzIter j x ≥ 3) ->
      (∀ j : Nat, j < p -> collatzIter j x % 2 = 0) ->
      collatzIter p x < x
  | 0, _, hp, _, _ => by omega
  | 1, x, _, hall, hev => by
    have hx3 : x ≥ 3 := by simpa [collatzIter] using hall 0 (by omega)
    have hx_ev : x % 2 = 0 := by simpa [collatzIter] using hev 0 (by omega)
    have hb : (x % 2 == 0) = true := decide_eq_true hx_ev
    change collatzStep x < x
    unfold collatzStep
    rw [hb]
    simp only [ite_true]
    omega
  | p' + 2, x, _, hall, hev => by
    have hx3 : x ≥ 3 := by simpa [collatzIter] using hall 0 (by omega)
    have hx_ev : x % 2 = 0 := by simpa [collatzIter] using hev 0 (by omega)
    have hb : (x % 2 == 0) = true := decide_eq_true hx_ev
    have hstep_lt : collatzStep x < x := by
      unfold collatzStep; rw [hb]; simp only [ite_true]; omega
    have hall_next : ∀ j : Nat, j ≤ p' + 1 -> collatzIter j (collatzStep x) ≥ 3 := by
      intro j hj; simpa [collatzIter] using hall (j + 1) (by omega)
    have hev_next : ∀ j : Nat, j < p' + 1 -> collatzIter j (collatzStep x) % 2 = 0 := by
      intro j hj; simpa [collatzIter] using hev (j + 1) (by omega)
    have ih := all_even_steps_strictly_shrink_w5 (p' + 1) (collatzStep x) (by omega)
      hall_next hev_next
    change collatzIter (p' + 1) (collatzStep x) < x
    omega

def hasOddIterUpTo (x : Nat) : Nat -> Bool
  | 0 => false
  | n + 1 => hasOddIterUpTo x n || decide (collatzIter n x % 2 = 1)

theorem hasOddIterUpTo_spec (x : Nat) :
    ∀ n : Nat,
      (hasOddIterUpTo x n = true -> ∃ j : Nat, j < n ∧ collatzIter j x % 2 = 1) ∧
      (hasOddIterUpTo x n = false -> ∀ j : Nat, j < n -> collatzIter j x % 2 = 0)
  | 0 => ⟨fun h => Bool.noConfusion h, fun _ _ hj => by omega⟩
  | n + 1 => by
    simp only [hasOddIterUpTo]
    rcases hasOddIterUpTo_spec x n with ⟨ih_t, ih_f⟩
    cases hacc : hasOddIterUpTo x n with
    | true =>
      simp only [Bool.true_or]
      refine ⟨fun _ => ?_, fun h => Bool.noConfusion h⟩
      rcases ih_t hacc with ⟨j, hj, ho⟩
      exact ⟨j, by omega, ho⟩
    | false =>
      simp only [Bool.false_or]
      cases hd : decide (collatzIter n x % 2 = 1) with
      | true =>
        refine ⟨fun _ => ⟨n, by omega, of_decide_eq_true hd⟩, fun h => Bool.noConfusion h⟩
      | false =>
        have hnot1 : collatzIter n x % 2 ≠ 1 := of_decide_eq_false hd
        refine ⟨fun h => Bool.noConfusion h, fun _ j hj => ?_⟩
        by_cases hjn : j = n
        · subst hjn; omega
        · exact ih_f hacc j (by omega)

/--
  Theorem W5.1b (`preimage_superharmonic_rational_eliminates_all_cycles`, zero custom axioms):
  General Berg–Meinardus Preimage Meta-Theorem (Part 1 — Universal Cycle Elimination):
  Existence of ANY positive rational preimage-superharmonic weight `(wNum, wDen)` on `{n ≥ 3}`
  with `θ = pTheta / qTheta ≤ 1` (requiring NO upper bound on `w` and NO strict contraction
  `θ < 1`!) immediately discharges `NoNontrivialPositiveCycles` across ALL `m`-block positive
  cycles (`∀ m ≥ 1`), because off-cycle mass `w(2 * T(x_i)) > 0` at any odd cycle vertex
  forces strict forward weight growth around the cycle.
-/
theorem preimage_superharmonic_rational_eliminates_all_cycles
    (wNum wDen : Nat -> Nat) (pTheta qTheta : Nat)
    (hw : IsPositiveRationalPreimageWeight wNum wDen pTheta qTheta) :
    NoNontrivialPositiveCycles := by
  intro x p hx hp hcyc
  by_cases htriv : x = 1 ∨ x = 2
  · exact htriv
  · exfalso
    have hall_ge3 : ∀ j : Nat, j ≤ p -> collatzIter j x ≥ 3 := by
      intro j _
      have hj_pos := collatzIter_pos_w5 j x hx
      by_cases hj3 : collatzIter j x ≥ 3
      · exact hj3
      · exfalso
        have h12 : collatzIter j x = 1 ∨ collatzIter j x = 2 := by omega
        have hper := collatzIter_mul_period (j + 1) p x hcyc
        have hgt : (j + 1) * p ≥ j := by
          have hm := Nat.mul_le_mul_left (j + 1) (by omega : 1 ≤ p)
          omega
        let rem := (j + 1) * p - j
        have hsplit : (j + 1) * p = j + rem := by dsimp [rem]; omega
        rw [hsplit, collatzIter_add j rem x] at hper
        have htr := collatzIter_trivial_cycle rem (collatzIter j x) h12
        rw [hper] at htr
        exact htriv htr
    have hex_odd : ∃ j : Nat, j < p ∧ collatzIter j x % 2 = 1 := by
      cases hb : hasOddIterUpTo x p with
      | true => exact (hasOddIterUpTo_spec x p).1 hb
      | false =>
        have hlt := all_even_steps_strictly_shrink_w5 p x hp hall_ge3
          ((hasOddIterUpTo_spec x p).2 hb)
        omega
    have hstrict := (preimage_iter_monotone_and_odd_strict_w5 wNum wDen pTheta qTheta hw
      p x hall_ge3).2 hex_odd
    rw [hcyc] at hstrict
    omega

theorem bernoulli_succ_pow_w5 (p : Nat) :
    ∀ m : Nat, (p + 1) ^ (m + 1) ≥ p ^ (m + 1) + (m + 1) * p ^ m
  | 0 => by simp
  | m + 1 => by
    have ih := bernoulli_succ_pow_w5 p m
    have h1 : (p + 1) ^ (m + 2) = (p + 1) ^ (m + 1) * (p + 1) := Nat.pow_succ (p + 1) (m + 1)
    have h2 : (p ^ (m + 1) + (m + 1) * p ^ m) * (p + 1) ≤ (p + 1) ^ (m + 1) * (p + 1) :=
      Nat.mul_le_mul_right (p + 1) ih
    have hexp : (p ^ (m + 1) + (m + 1) * p ^ m) * (p + 1) =
        p ^ (m + 2) + (m + 2) * p ^ (m + 1) + (m + 1) * p ^ m := by
      calc
        (p ^ (m + 1) + (m + 1) * p ^ m) * (p + 1)
            = p ^ (m + 1) * (p + 1) + ((m + 1) * p ^ m) * (p + 1) := Nat.add_mul _ _ _
        _ = (p ^ (m + 1) * p + p ^ (m + 1)) +
              (((m + 1) * p ^ m) * p + (m + 1) * p ^ m) := by
              rw [Nat.mul_add, Nat.mul_one, Nat.mul_add, Nat.mul_one]
        _ = (p ^ (m + 2) + p ^ (m + 1)) +
              ((m + 1) * p ^ (m + 1) + (m + 1) * p ^ m) := by
              rw [← Nat.pow_succ p (m + 1), Nat.mul_assoc (m + 1) (p ^ m) p, ← Nat.pow_succ p m]
        _ = p ^ (m + 2) + (p ^ (m + 1) + (m + 1) * p ^ (m + 1)) + (m + 1) * p ^ m := by omega
        _ = p ^ (m + 2) + (m + 2) * p ^ (m + 1) + (m + 1) * p ^ m := by
              have hs : p ^ (m + 1) + (m + 1) * p ^ (m + 1) = (m + 2) * p ^ (m + 1) := by
                rw [show m + 2 = 1 + (m + 1) by omega, Nat.add_mul 1 (m + 1) (p ^ (m + 1)), Nat.one_mul]
              rw [hs]
    change (p + 1) ^ (m + 2) ≥ p ^ (m + 2) + (m + 2) * p ^ (m + 1)
    rw [h1]
    omega

theorem pow_double_ratio_w5 (p q : Nat) (hp : p ≥ 1) (hpq : p + 1 ≤ q) :
    ∀ m : Nat, q ^ (p * m) ≥ 2 ^ m * p ^ (p * m)
  | 0 => by simp
  | m + 1 => by
    have ih := pow_double_ratio_w5 p q hp hpq m
    have hqp : q ^ p ≥ 2 * p ^ p := by
      cases p with
      | zero => omega
      | succ p' =>
        have hbern := bernoulli_succ_pow_w5 (p' + 1) p'
        have hp_pow : (p' + 1) * (p' + 1) ^ p' = (p' + 1) ^ (p' + 1) := by
          rw [Nat.pow_succ (p' + 1) p', Nat.mul_comm]
        have hp2_eq : p' + 1 + 1 = p' + 2 := rfl
        rw [hp_pow, hp2_eq] at hbern
        have hmono := nat_pow_mono_base (p' + 2) q hpq (p' + 1)
        omega
    have hexp : p * (m + 1) = p * m + p := by rw [Nat.mul_add, Nat.mul_one]
    rw [hexp, Nat.pow_add q (p * m) p, Nat.pow_add p (p * m) p, Nat.pow_succ 2 m]
    have hm := Nat.mul_le_mul ih hqp
    have hrhs : (2 ^ m * p ^ (p * m)) * (2 * p ^ p) =
        (2 ^ m * 2) * (p ^ (p * m) * p ^ p) := by
      calc
        (2 ^ m * p ^ (p * m)) * (2 * p ^ p)
            = 2 ^ m * (p ^ (p * m) * (2 * p ^ p)) := Nat.mul_assoc _ _ _
        _ = 2 ^ m * ((p ^ (p * m) * 2) * p ^ p) := by rw [← Nat.mul_assoc (p ^ (p * m))]
        _ = 2 ^ m * ((2 * p ^ (p * m)) * p ^ p) := by rw [Nat.mul_comm (p ^ (p * m)) 2]
        _ = (2 ^ m * 2) * (p ^ (p * m) * p ^ p) := by
              rw [Nat.mul_assoc 2, ← Nat.mul_assoc (2 ^ m)]
    rwa [hrhs] at hm

theorem contractive_iter_bound_w5
    (wNum wDen : Nat -> Nat) (pTheta qTheta : Nat)
    (hw : IsPositiveRationalPreimageWeight wNum wDen pTheta qTheta) :
    ∀ (k x : Nat),
      (∀ j : Nat, j ≤ k -> collatzIter j x ≥ 3) ->
      qTheta ^ k * (wNum x * wDen (collatzIter k x)) ≤
        pTheta ^ k * (wNum (collatzIter k x) * wDen x)
  | 0, _, _ => by simp [collatzIter]
  | k + 1, x, hall => by
    have hx3 : x ≥ 3 := hall 0 (by omega)
    have htx3 : collatzStep x ≥ 3 := by simpa [collatzIter] using hall 1 (by omega)
    have h1 := (preimage_rational_forward_step_laws wNum wDen pTheta qTheta x hw hx3 htx3).1
    have hall_next : ∀ j : Nat, j ≤ k -> collatzIter j (collatzStep x) ≥ 3 := by
      intro j hj; simpa [collatzIter] using hall (j + 1) (by omega)
    have ih := contractive_iter_bound_w5 wNum wDen pTheta qTheta hw k (collatzStep x) hall_next
    let y := collatzStep x
    let z := collatzIter k y
    have hden_y : wDen y > 0 := (hw.2.2.1 y htx3).2
    change qTheta ^ (k + 1) * (wNum x * wDen z) ≤ pTheta ^ (k + 1) * (wNum z * wDen x)
    apply nat_mul_le_cancel_right_w5 (wDen y) _ _ hden_y
    have hm1 : (qTheta ^ k * (qTheta * (wNum x * wDen y))) * wDen z ≤
        (qTheta ^ k * (pTheta * (wNum y * wDen x))) * wDen z :=
      Nat.mul_le_mul_right (wDen z) (Nat.mul_le_mul_left (qTheta ^ k) h1)
    have hm2 : (pTheta * wDen x) * (qTheta ^ k * (wNum y * wDen z)) ≤
        (pTheta * wDen x) * (pTheta ^ k * (wNum z * wDen y)) :=
      Nat.mul_le_mul_left (pTheta * wDen x) ih
    have hl_eq : (qTheta ^ (k + 1) * (wNum x * wDen z)) * wDen y =
        (qTheta ^ k * (qTheta * (wNum x * wDen y))) * wDen z := by
      rw [Nat.pow_succ qTheta k]
      calc
        ((qTheta ^ k * qTheta) * (wNum x * wDen z)) * wDen y
            = (qTheta ^ k * qTheta) * ((wNum x * wDen z) * wDen y) := Nat.mul_assoc _ _ _
        _ = (qTheta ^ k * qTheta) * (wNum x * (wDen y * wDen z)) := by
              rw [Nat.mul_assoc (wNum x), Nat.mul_comm (wDen z) (wDen y)]
        _ = (qTheta ^ k * qTheta) * ((wNum x * wDen y) * wDen z) := by rw [← Nat.mul_assoc (wNum x)]
        _ = ((qTheta ^ k * qTheta) * (wNum x * wDen y)) * wDen z := (Nat.mul_assoc _ _ _).symm
        _ = (qTheta ^ k * (qTheta * (wNum x * wDen y))) * wDen z := by rw [Nat.mul_assoc (qTheta ^ k)]
    have hmid_eq : (qTheta ^ k * (pTheta * (wNum y * wDen x))) * wDen z =
        (pTheta * wDen x) * (qTheta ^ k * (wNum y * wDen z)) := by
      calc
        (qTheta ^ k * (pTheta * (wNum y * wDen x))) * wDen z
            = qTheta ^ k * ((pTheta * (wNum y * wDen x)) * wDen z) := Nat.mul_assoc _ _ _
        _ = qTheta ^ k * ((pTheta * wDen x) * (wNum y * wDen z)) := by
              have hinner : (pTheta * (wNum y * wDen x)) * wDen z =
                  (pTheta * wDen x) * (wNum y * wDen z) := by
                calc
                  (pTheta * (wNum y * wDen x)) * wDen z
                      = pTheta * ((wNum y * wDen x) * wDen z) := Nat.mul_assoc _ _ _
                  _ = pTheta * ((wDen x * wNum y) * wDen z) := by rw [Nat.mul_comm (wNum y) (wDen x)]
                  _ = pTheta * (wDen x * (wNum y * wDen z)) := by rw [Nat.mul_assoc (wDen x)]
                  _ = (pTheta * wDen x) * (wNum y * wDen z) := (Nat.mul_assoc _ _ _).symm
              rw [hinner]
        _ = (qTheta ^ k * (pTheta * wDen x)) * (wNum y * wDen z) := (Nat.mul_assoc _ _ _).symm
        _ = ((pTheta * wDen x) * qTheta ^ k) * (wNum y * wDen z) := by rw [Nat.mul_comm (qTheta ^ k)]
        _ = (pTheta * wDen x) * (qTheta ^ k * (wNum y * wDen z)) := Nat.mul_assoc _ _ _
    have hr_eq : (pTheta * wDen x) * (pTheta ^ k * (wNum z * wDen y)) =
        (pTheta ^ (k + 1) * (wNum z * wDen x)) * wDen y := by
      rw [Nat.pow_succ pTheta k, Nat.mul_comm (pTheta ^ k) pTheta]
      calc
        (pTheta * wDen x) * (pTheta ^ k * (wNum z * wDen y))
            = pTheta * (wDen x * (pTheta ^ k * (wNum z * wDen y))) := Nat.mul_assoc _ _ _
        _ = pTheta * ((wDen x * pTheta ^ k) * (wNum z * wDen y)) := by rw [← Nat.mul_assoc (wDen x)]
        _ = pTheta * ((pTheta ^ k * wDen x) * (wNum z * wDen y)) := by rw [Nat.mul_comm (wDen x)]
        _ = (pTheta * pTheta ^ k) * (wDen x * (wNum z * wDen y)) := by
              rw [Nat.mul_assoc (pTheta ^ k), ← Nat.mul_assoc pTheta]
        _ = (pTheta * pTheta ^ k) * ((wNum z * wDen x) * wDen y) := by
              rw [← Nat.mul_assoc (wDen x), Nat.mul_comm (wDen x) (wNum z)]
        _ = ((pTheta * pTheta ^ k) * (wNum z * wDen x)) * wDen y := (Nat.mul_assoc _ _ _).symm
    rw [hl_eq]
    rw [hmid_eq] at hm1
    rw [hr_eq] at hm2
    exact Nat.le_trans hm1 hm2

def hitTrivIterUpTo (x : Nat) : Nat -> Bool
  | 0 => false
  | n + 1 => hitTrivIterUpTo x n || decide (collatzIter n x ≤ 2)

theorem hitTrivIterUpTo_spec (x : Nat) :
    ∀ n : Nat,
      (hitTrivIterUpTo x n = true -> ∃ j : Nat, j < n ∧ collatzIter j x ≤ 2) ∧
      (hitTrivIterUpTo x n = false -> ∀ j : Nat, j < n -> collatzIter j x ≥ 3)
  | 0 => ⟨fun h => Bool.noConfusion h, fun _ _ hj => by omega⟩
  | n + 1 => by
    simp only [hitTrivIterUpTo]
    rcases hitTrivIterUpTo_spec x n with ⟨ih_t, ih_f⟩
    cases hacc : hitTrivIterUpTo x n with
    | true =>
      simp only [Bool.true_or]
      refine ⟨fun _ => ?_, fun h => Bool.noConfusion h⟩
      rcases ih_t hacc with ⟨j, hj, hle⟩
      exact ⟨j, by omega, hle⟩
    | false =>
      simp only [Bool.false_or]
      cases hd : decide (collatzIter n x ≤ 2) with
      | true =>
        refine ⟨fun _ => ⟨n, by omega, of_decide_eq_true hd⟩, fun h => Bool.noConfusion h⟩
      | false =>
        have hgt2 : ¬ (collatzIter n x ≤ 2) := of_decide_eq_false hd
        refine ⟨fun h => Bool.noConfusion h, fun _ j hj => ?_⟩
        by_cases hjn : j = n
        · subst hjn; omega
        · exact ih_f hacc j (by omega)

/--
  Theorem W5.1c (`strictly_contractive_bounded_preimage_weight_implies_collatz_standard`, zero custom axioms):
  General Berg–Meinardus Preimage Meta-Theorem (Part 2 — Unconditional Global Convergence):
  If a positive rational preimage weight `(wNum, wDen)` on `{n ≥ 3}` is strictly contractive
  (`0 < pTheta < qTheta`, i.e. `θ < 1`) and uniformly bounded above (`∀ n ≥ 3, wNum n ≤ B * wDen n`),
  then EVERY positive integer reaches `1` (`CollatzConjectureStandard`) within an explicit
  computable horizon `k ≤ pTheta * (B * wDen n) + 1`!
-/
theorem strictly_contractive_bounded_preimage_weight_implies_collatz_standard
    (wNum wDen : Nat -> Nat) (pTheta qTheta B : Nat)
    (hw : IsPositiveRationalPreimageWeight wNum wDen pTheta qTheta)
    (hstrict : pTheta < qTheta)
    (_hB_pos : B ≥ 1)
    (hbdd : ∀ n : Nat, n ≥ 3 -> wNum n ≤ B * wDen n) :
    CollatzConjectureStandard := by
  rw [collatz_standard_iff_compressed]
  intro n hn
  by_cases hn2 : n ≤ 2
  · have hc : n = 1 ∨ n = 2 := by omega
    rcases hc with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, by decide⟩
  · have hn3 : n ≥ 3 := by omega
    let M := B * wDen n
    let K := pTheta * M
    cases hb : hitTrivIterUpTo n (K + 1) with
    | true =>
      rcases (hitTrivIterUpTo_spec n (K + 1)).1 hb with ⟨j, _, hj_le2⟩
      have hj_pos := collatzIter_pos_w5 j n hn
      have hc : collatzIter j n = 1 ∨ collatzIter j n = 2 := by omega
      rcases hc with h1 | h2
      · exact ⟨j, h1⟩
      · refine ⟨j + 1, ?_⟩
        rw [collatzIter_add j 1 n, h2]
        decide
    | false =>
      exfalso
      have hall : ∀ j : Nat, j ≤ K -> collatzIter j n ≥ 3 :=
        fun j hj => (hitTrivIterUpTo_spec n (K + 1)).2 hb j (by omega)
      have hiter := contractive_iter_bound_w5 wNum wDen pTheta qTheta hw K n hall
      let z := collatzIter K n
      have hz3 : z ≥ 3 := hall K (Nat.le_refl K)
      have hden_z : wDen z > 0 := (hw.2.2.1 z hz3).2
      have hnum_n : wNum n ≥ 1 := (hw.2.2.1 n hn3).1
      have hz_bdd : wNum z ≤ B * wDen z := hbdd z hz3
      have hrhs_bdd : pTheta ^ K * (wNum z * wDen n) ≤ (pTheta ^ K * M) * wDen z := by
        dsimp [M]
        have hm : wNum z * wDen n ≤ (B * wDen z) * wDen n := Nat.mul_le_mul_right (wDen n) hz_bdd
        have heq : pTheta ^ K * ((B * wDen z) * wDen n) = (pTheta ^ K * (B * wDen n)) * wDen z := by
          calc
            pTheta ^ K * ((B * wDen z) * wDen n)
                = pTheta ^ K * (B * (wDen z * wDen n)) := by rw [Nat.mul_assoc B]
            _ = pTheta ^ K * (B * (wDen n * wDen z)) := by rw [Nat.mul_comm (wDen z)]
            _ = pTheta ^ K * ((B * wDen n) * wDen z) := by rw [← Nat.mul_assoc B]
            _ = (pTheta ^ K * (B * wDen n)) * wDen z := (Nat.mul_assoc _ _ _).symm
        rw [← heq]
        exact Nat.mul_le_mul_left _ hm
      have hlhs_assoc : qTheta ^ K * (wNum n * wDen z) = (qTheta ^ K * wNum n) * wDen z :=
        (Nat.mul_assoc _ _ _).symm
      rw [hlhs_assoc] at hiter
      have hcanc := nat_mul_le_cancel_right_w5 (wDen z) _ _ hden_z (Nat.le_trans hiter hrhs_bdd)
      have hdoub := pow_double_ratio_w5 pTheta qTheta hw.1 (by omega) M
      change qTheta ^ K ≥ 2 ^ M * pTheta ^ K at hdoub
      have hp2M : 2 ^ M ≥ M + 1 := pow2_ge_succ_self M
      have hpK_pos : pTheta ^ K ≥ 1 := nat_pow_pos_of_pos pTheta hw.1 K
      have hgt_M : 2 ^ M * pTheta ^ K > M * pTheta ^ K := by
        have hm := Nat.mul_le_mul_right (pTheta ^ K) hp2M
        rw [Nat.add_mul, Nat.one_mul] at hm
        omega
      have hnum_ge : qTheta ^ K * wNum n ≥ qTheta ^ K := by
        have hm := Nat.mul_le_mul_left (qTheta ^ K) hnum_n
        simpa using hm
      have hcomm_M : M * pTheta ^ K = pTheta ^ K * M := Nat.mul_comm _ _
      omega

-- ----------------------------------------------------------------------------
-- Reusable `(2, 3)`-Adic Valuation & Core Algebra Lemmas (Zero Custom Axioms)
-- ----------------------------------------------------------------------------

theorem v2PowAux_eq_of_ge :
    ∀ (f1 f2 n : Nat), n ≤ f1 -> n ≤ f2 -> v2PowAux f1 n = v2PowAux f2 n
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, n, h1, _ => by
    have hn0 : n = 0 := by omega
    subst hn0; rfl
  | _ + 1, 0, n, _, h2 => by
    have hn0 : n = 0 := by omega
    subst hn0; rfl
  | f1 + 1, f2 + 1, n, h1, h2 => by
    simp only [v2PowAux]
    by_cases hc : n > 0 ∧ n % 2 = 0
    · simp only [hc, and_self, ite_true]
      rw [v2PowAux_eq_of_ge f1 f2 (n / 2) (by omega) (by omega)]
    · simp only [hc, ite_false]

theorem v2Pow_of_odd (n : Nat) (hodd : n % 2 = 1) : v2Pow n = 1 := by
  unfold v2Pow
  cases n with
  | zero => omega
  | succ m =>
    have hnc : ¬ (m + 1 > 0 ∧ (m + 1) % 2 = 0) := by omega
    simp only [v2PowAux, hnc, ite_false]

theorem v2Pow_mul2 (m : Nat) (hm : m > 0) : v2Pow (2 * m) = 2 * v2Pow m := by
  unfold v2Pow
  cases hfuel : 2 * m with
  | zero => omega
  | succ f =>
    have hc : f + 1 > 0 ∧ (f + 1) % 2 = 0 := by omega
    simp only [v2PowAux, hc, and_self, ite_true]
    have hdiv : (f + 1) / 2 = m := by omega
    rw [hdiv, v2PowAux_eq_of_ge f m m (by omega) (by omega)]

theorem v2Pow_mul3_aux :
    ∀ (bound m : Nat), m > 0 -> m ≤ bound -> v2Pow (3 * m) = v2Pow m
  | 0, _, hm, hle => by omega
  | bound + 1, m, hm, hle => by
    by_cases hev : m % 2 = 0
    · let k := m / 2
      have hk_pos : k > 0 := by dsimp [k]; omega
      have hm_eq : m = 2 * k := by dsimp [k]; omega
      have h32 : 3 * (2 * k) = 2 * (3 * k) := by omega
      rw [hm_eq, h32, v2Pow_mul2 (3 * k) (by omega), v2Pow_mul2 k hk_pos,
          v2Pow_mul3_aux bound k hk_pos (by dsimp [k]; omega)]
    · have h3odd : (3 * m) % 2 = 1 := by omega
      rw [v2Pow_of_odd (3 * m) h3odd, v2Pow_of_odd m (by omega)]

theorem v2Pow_mul3 (m : Nat) (hm : m > 0) : v2Pow (3 * m) = v2Pow m :=
  v2Pow_mul3_aux m m hm (Nat.le_refl m)

theorem v3PowAux_eq_of_ge :
    ∀ (f1 f2 n : Nat), n ≤ f1 -> n ≤ f2 -> v3PowAux f1 n = v3PowAux f2 n
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, n, h1, _ => by
    have hn0 : n = 0 := by omega
    subst hn0; rfl
  | _ + 1, 0, n, _, h2 => by
    have hn0 : n = 0 := by omega
    subst hn0; rfl
  | f1 + 1, f2 + 1, n, h1, h2 => by
    simp only [v3PowAux]
    by_cases hc : n > 0 ∧ n % 3 = 0
    · simp only [hc, and_self, ite_true]
      rw [v3PowAux_eq_of_ge f1 f2 (n / 3) (by omega) (by omega)]
    · simp only [hc, ite_false]

theorem v3Pow_of_not_div3 (n : Nat) (hnd : n % 3 ≠ 0) : v3Pow n = 1 := by
  unfold v3Pow
  cases n with
  | zero => omega
  | succ m =>
    have hnc : ¬ (m + 1 > 0 ∧ (m + 1) % 3 = 0) := fun hc => hnd hc.2
    simp only [v3PowAux, hnc, ite_false]

theorem v3Pow_mul3 (m : Nat) (hm : m > 0) : v3Pow (3 * m) = 3 * v3Pow m := by
  unfold v3Pow
  cases hfuel : 3 * m with
  | zero => omega
  | succ f =>
    have hc : f + 1 > 0 ∧ (f + 1) % 3 = 0 := by omega
    simp only [v3PowAux, hc, and_self, ite_true]
    have hdiv : (f + 1) / 3 = m := by omega
    rw [hdiv, v3PowAux_eq_of_ge f m m (by omega) (by omega)]

theorem v3Pow_mul2_aux :
    ∀ (bound m : Nat), m > 0 -> m ≤ bound -> v3Pow (2 * m) = v3Pow m
  | 0, _, hm, hle => by omega
  | bound + 1, m, hm, hle => by
    by_cases hd3 : m % 3 = 0
    · let k := m / 3
      have hk_pos : k > 0 := by dsimp [k]; omega
      have hm_eq : m = 3 * k := by dsimp [k]; omega
      have h23 : 2 * (3 * k) = 3 * (2 * k) := by omega
      rw [hm_eq, h23, v3Pow_mul3 (2 * k) (by omega), v3Pow_mul3 k hk_pos,
          v3Pow_mul2_aux bound k hk_pos (by dsimp [k]; omega)]
    · have h2nd : (2 * m) % 3 ≠ 0 := by omega
      rw [v3Pow_of_not_div3 (2 * m) h2nd, v3Pow_of_not_div3 m hd3]

theorem v3Pow_mul2 (m : Nat) (hm : m > 0) : v3Pow (2 * m) = v3Pow m :=
  v3Pow_mul2_aux m m hm (Nat.le_refl m)

-- ----------------------------------------------------------------------------
-- W5.1d: Universal Non-Radial Periodic-Valuation Berg–Meinardus Barrier (Zero Custom Axioms)
-- ----------------------------------------------------------------------------

def geomSpineEntry (j : Nat) : Nat :=
  (4 ^ (3 * j + 4) - 1) / 3

theorem pow64_mod9_eq_one_w5 : ∀ j : Nat, 64 ^ j % 9 = 1
  | 0 => rfl
  | j + 1 => by rw [Nat.pow_succ, Nat.mul_mod, pow64_mod9_eq_one_w5 j]

theorem pow4_triple_eq_pow64_w5 : ∀ j : Nat, 4 ^ (3 * j) = 64 ^ j
  | 0 => rfl
  | j + 1 => by
    rw [show 3 * (j + 1) = 3 * j + 3 by omega, Nat.pow_add, pow4_triple_eq_pow64_w5 j,
        Nat.pow_succ 64 j]

theorem geomSpineEntry_valuations_constant (j : Nat) :
    let z := geomSpineEntry j
    3 * z + 1 = 4 ^ (3 * j + 4) ∧
    z ≥ 85 ∧
    v2Pow z = 1 ∧ v3Pow z = 1 ∧
    v2Pow (z + 1) = 2 ∧ v3Pow (z + 1) = 1 := by
  dsimp only
  let z := geomSpineEntry j
  have hp4_m3 : 4 ^ (3 * j + 4) % 3 = 1 := (pow4_ge_four_and_mod3_w5 (3 * j + 3)).2
  have hge256 : 4 ^ (3 * j + 4) ≥ 256 := by
    rw [Nat.pow_add 4 (3 * j) 4]
    have hp0 := nat_pow_pos_of_pos 4 (by decide) (3 * j)
    have h44 : (4 : Nat) ^ 4 = 256 := rfl
    rw [h44]
    have hm := Nat.mul_le_mul_right 256 hp0
    omega
  have h3z1 : 3 * z + 1 = 4 ^ (3 * j + 4) := by
    dsimp [z, geomSpineEntry]
    omega
  have hz_ge85 : z ≥ 85 := by omega
  have hp4_m9 : 4 ^ (3 * j + 4) % 9 = 4 := by
    rw [Nat.pow_add 4 (3 * j) 4, pow4_triple_eq_pow64_w5 j,
        Nat.mul_mod, pow64_mod9_eq_one_w5 j]
  have hz_odd : z % 2 = 1 := by
    have hev : (3 * z + 1) % 2 = 0 := by
      rw [h3z1, show 3 * j + 4 = (3 * j + 3) + 1 by omega, Nat.pow_succ]; omega
    omega
  have hz_mod3 : z % 3 = 1 := by omega
  let u := (z + 1) / 2
  have hzp1 : z + 1 = 2 * u := by dsimp [u]; omega
  have h3u : 3 * (2 * u) = 4 ^ (3 * j + 4) + 2 := by omega
  have hu_odd : u % 2 = 1 := by
    have hmod4 : (4 ^ (3 * j + 4) + 2) % 4 = 2 := by
      rw [show 3 * j + 4 = (3 * j + 3) + 1 by omega, Nat.pow_succ]
      omega
    omega
  have hv2_zp1 : v2Pow (z + 1) = 2 := by
    rw [hzp1, v2Pow_mul2 u (by omega), v2Pow_of_odd u hu_odd]
  exact ⟨h3z1, hz_ge85, v2Pow_of_odd z hz_odd, v3Pow_of_not_div3 z (by omega),
         hv2_zp1, v3Pow_of_not_div3 (z + 1) (by omega)⟩

def maxOverModRangeAux (g : Nat -> Nat) : Nat -> Nat
  | 0 => 1
  | r + 1 => Nat.max (maxOverModRangeAux g r) (g r)

theorem le_maxOverModRangeAux (g : Nat -> Nat) :
    ∀ (P r : Nat), r < P -> g r ≤ maxOverModRangeAux g P
  | 0, _, hr => by omega
  | P + 1, r, hr => by
    simp only [maxOverModRangeAux]
    by_cases heq : r = P
    · subst heq; exact Nat.le_max_right _ _
    · exact Nat.le_trans (le_maxOverModRangeAux g P r (by omega)) (Nat.le_max_left _ _)

theorem maxOverModRangeAux_pos (g : Nat -> Nat) : ∀ P : Nat, maxOverModRangeAux g P ≥ 1
  | 0 => Nat.le_refl 1
  | P + 1 => Nat.le_trans (maxOverModRangeAux_pos g P) (Nat.le_max_left _ _)

/--
  Theorem W5.1d (`berg_meinardus_periodic_valuation_weight_impossibility`, zero custom axioms):
  Universal Non-Radial Periodic-Valuation Berg–Meinardus Barrier:
  For EVERY period `P ≥ 1` and EVERY positive rational weight `(wNum, wDen)` whose values
  depend arbitrarily (with ZERO radial monotonicity requirement!) on the 5-tuple
  `(v2Pow n, v3Pow n, v2Pow (n + 1), v3Pow (n + 1), n % P)`, preimage superharmonicity
  `IsPositiveRationalPreimageWeight wNum wDen pTheta qTheta` is UNIVERSALLY IMPOSSIBLE!
-/
theorem berg_meinardus_periodic_valuation_weight_impossibility
    (P pTheta qTheta : Nat) (hP : P ≥ 1)
    (fNum fDen : Nat -> Nat -> Nat -> Nat -> Nat -> Nat)
    (hw : IsPositiveRationalPreimageWeight
      (fun n => fNum (v2Pow n) (v3Pow n) (v2Pow (n + 1)) (v3Pow (n + 1)) (n % P))
      (fun n => fDen (v2Pow n) (v3Pow n) (v2Pow (n + 1)) (v3Pow (n + 1)) (n % P))
      pTheta qTheta) :
    False := by
  let wNum : Nat -> Nat :=
    fun n => fNum (v2Pow n) (v3Pow n) (v2Pow (n + 1)) (v3Pow (n + 1)) (n % P)
  let wDen : Nat -> Nat :=
    fun n => fDen (v2Pow n) (v3Pow n) (v2Pow (n + 1)) (v3Pow (n + 1)) (n % P)
  change IsPositiveRationalPreimageWeight wNum wDen pTheta qTheta at hw
  let dMax := maxOverModRangeAux (fun r => fDen 1 1 2 1 r) P
  have hdMax_pos : dMax ≥ 1 := maxOverModRangeAux_pos _ P
  let S : Nat -> Nat := fun j => 4 ^ (3 * j + 1)
  have hS_ge4 : ∀ j : Nat, S j ≥ 4 := fun j => (pow4_ge_four_and_mod3_w5 (3 * j)).1
  have hdouble_le : ∀ m : Nat, m ≥ 3 -> wNum (2 * m) * wDen m ≤ wNum m * wDen (2 * m) := by
    intro m hm
    have hstep := preimage_rational_forward_step_laws wNum wDen pTheta qTheta (2 * m) hw
      (by omega) (by rw [collatzStep_double_pos m]; omega)
    simpa [collatzStep_double_pos m] using hstep.2.1
  have hstep_S : ∀ j : Nat,
      (dMax * wNum (S (j + 1)) + wDen (S (j + 1))) * wDen (S j) ≤
        dMax * wNum (S j) * wDen (S (j + 1)) := by
    intro j
    let s0 := S j
    have hs0 : s0 ≥ 4 := hS_ge4 j
    have hs0_m3 : s0 % 3 = 1 := (pow4_ge_four_and_mod3_w5 (3 * j)).2
    have hd1 := hdouble_le s0 (by omega)
    have hd2 := hdouble_le (2 * s0) (by omega)
    have hd3 := hdouble_le (4 * s0) (by omega)
    have hd4 := hdouble_le (8 * s0) (by omega)
    have hd5 := hdouble_le (16 * s0) (by omega)
    rw [show 2 * (2 * s0) = 4 * s0 by omega] at hd2
    rw [show 2 * (4 * s0) = 8 * s0 by omega] at hd3
    rw [show 2 * (8 * s0) = 16 * s0 by omega] at hd4
    rw [show 2 * (16 * s0) = 32 * s0 by omega] at hd5
    have hc12 := rat_le_trans_pos_w5 _ _ _ _ _ _ (hw.2.2.1 (2 * s0) (by omega)).2 hd2 hd1
    have hc13 := rat_le_trans_pos_w5 _ _ _ _ _ _ (hw.2.2.1 (4 * s0) (by omega)).2 hd3 hc12
    have hc14 := rat_le_trans_pos_w5 _ _ _ _ _ _ (hw.2.2.1 (8 * s0) (by omega)).2 hd4 hc13
    have hc15 := rat_le_trans_pos_w5 _ _ _ _ _ _ (hw.2.2.1 (16 * s0) (by omega)).2 hd5 hc14
    let mj := 32 * s0
    have h2mj : 2 * mj = S (j + 1) := by
      have hp : S (j + 1) = s0 * 4 ^ 3 := by
        dsimp [S, s0]
        rw [show 3 * (j + 1) + 1 = (3 * j + 1) + 3 by omega, Nat.pow_add 4 (3 * j + 1) 3]
      have h43 : (4 : Nat) ^ 3 = 64 := rfl
      rw [hp, h43]
      dsimp [mj]; omega
    have hmj_mod3 : mj % 3 = 2 := by dsimp [mj]; omega
    have hpre_mj := hw.2.2.2.2 mj (by dsimp [mj]; omega) hmj_mod3
    dsimp only at hpre_mj
    rw [h2mj] at hpre_mj
    let zj := geomSpineEntry j
    have hzj_def : (S (j + 1) - 1) / 3 = zj := rfl
    rw [hzj_def] at hpre_mj
    rcases geomSpineEntry_valuations_constant j with ⟨_, hzj_ge, hv2z, hv3z, hv2zp1, hv3zp1⟩
    change zj ≥ 85 at hzj_ge
    have hle_pq : pTheta * (wNum mj * (wDen (S (j + 1)) * wDen zj)) ≤
        qTheta * (wNum mj * (wDen (S (j + 1)) * wDen zj)) :=
      Nat.mul_le_mul_right _ hw.2.1
    have hsplit_mj : (wNum (S (j + 1)) * wDen zj + wNum zj * wDen (S (j + 1))) * wDen mj ≤
        wNum mj * (wDen (S (j + 1)) * wDen zj) :=
      nat_mul_le_cancel_left_w5 qTheta _ _ (Nat.lt_of_lt_of_le hw.1 hw.2.1) (Nat.le_trans hpre_mj hle_pq)
    have hwDen_zj_eq : wDen zj = fDen 1 1 2 1 (zj % P) := by
      dsimp [wDen, zj]
      change fDen (v2Pow (geomSpineEntry j)) (v3Pow (geomSpineEntry j))
        (v2Pow (geomSpineEntry j + 1)) (v3Pow (geomSpineEntry j + 1)) (geomSpineEntry j % P) = _
      rw [hv2z, hv3z, hv2zp1, hv3zp1]
    have hwDen_zj_le : wDen zj ≤ dMax := by
      rw [hwDen_zj_eq]
      exact le_maxOverModRangeAux (fun r => fDen 1 1 2 1 r) P (zj % P) (Nat.mod_lt zj hP)
    have hwNum_zj_pos : wNum zj ≥ 1 := (hw.2.2.1 zj (by omega)).1
    have hden_zj_pos : wDen zj > 0 := (hw.2.2.1 zj (by omega)).2
    have hden_mj_pos : wDen mj > 0 := (hw.2.2.1 mj (by dsimp [mj]; omega)).2
    have hzj_ratio : wDen zj ≤ dMax * wNum zj := by
      have hm := Nat.mul_le_mul_left dMax hwNum_zj_pos
      omega
    have hd_mul : (dMax * wNum (S (j + 1)) + wDen (S (j + 1))) * wDen mj ≤
        dMax * wNum mj * wDen (S (j + 1)) := by
      apply nat_mul_le_cancel_right_w5 (wDen zj) _ _ hden_zj_pos
      have hm1 := Nat.mul_le_mul_left dMax hsplit_mj
      have hl : ((dMax * wNum (S (j + 1)) + wDen (S (j + 1))) * wDen mj) * wDen zj ≤
          dMax * ((wNum (S (j + 1)) * wDen zj + wNum zj * wDen (S (j + 1))) * wDen mj) := by
        have hinner : (dMax * wNum (S (j + 1)) + wDen (S (j + 1))) * wDen zj ≤
            dMax * (wNum (S (j + 1)) * wDen zj + wNum zj * wDen (S (j + 1))) := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_assoc dMax (wNum (S (j + 1))) (wDen zj)]
          have h2 : wDen (S (j + 1)) * wDen zj ≤ dMax * (wNum zj * wDen (S (j + 1))) := by
            have hm := Nat.mul_le_mul_right (wDen (S (j + 1))) hzj_ratio
            rw [Nat.mul_comm (wDen (S (j + 1))) (wDen zj)]
            rwa [Nat.mul_assoc] at hm
          omega
        have hrw : ((dMax * wNum (S (j + 1)) + wDen (S (j + 1))) * wDen mj) * wDen zj =
            ((dMax * wNum (S (j + 1)) + wDen (S (j + 1))) * wDen zj) * wDen mj := by
          rw [Nat.mul_assoc, Nat.mul_comm (wDen mj) (wDen zj), ← Nat.mul_assoc]
        have hrw2 : dMax * ((wNum (S (j + 1)) * wDen zj + wNum zj * wDen (S (j + 1))) * wDen mj) =
            (dMax * (wNum (S (j + 1)) * wDen zj + wNum zj * wDen (S (j + 1)))) * wDen mj :=
          (Nat.mul_assoc _ _ _).symm
        rw [hrw, hrw2]
        exact Nat.mul_le_mul_right (wDen mj) hinner
      have hr : dMax * (wNum mj * (wDen (S (j + 1)) * wDen zj)) =
          (dMax * wNum mj * wDen (S (j + 1))) * wDen zj := by
        rw [← Nat.mul_assoc (wNum mj), ← Nat.mul_assoc dMax, ← Nat.mul_assoc]
      rw [hr] at hm1
      exact Nat.le_trans hl hm1
    apply nat_mul_le_cancel_right_w5 (wDen mj) _ _ hden_mj_pos
    have hm_left : ((dMax * wNum (S (j + 1)) + wDen (S (j + 1))) * wDen s0) * wDen mj =
        ((dMax * wNum (S (j + 1)) + wDen (S (j + 1))) * wDen mj) * wDen s0 := by
      rw [Nat.mul_assoc, Nat.mul_comm (wDen s0) (wDen mj), ← Nat.mul_assoc]
    have hm_mid : ((dMax * wNum (S (j + 1)) + wDen (S (j + 1))) * wDen mj) * wDen s0 ≤
        (dMax * wNum mj * wDen (S (j + 1))) * wDen s0 :=
      Nat.mul_le_mul_right (wDen s0) hd_mul
    have hm_right : (dMax * wNum mj * wDen (S (j + 1))) * wDen s0 ≤
        (dMax * wNum s0 * wDen (S (j + 1))) * wDen mj := by
      have hc : (dMax * wNum mj * wDen (S (j + 1))) * wDen s0 =
          (dMax * wDen (S (j + 1))) * (wNum mj * wDen s0) := by
        calc
          (dMax * wNum mj * wDen (S (j + 1))) * wDen s0
              = dMax * (wNum mj * wDen (S (j + 1))) * wDen s0 := by rw [Nat.mul_assoc dMax]
          _ = dMax * (wDen (S (j + 1)) * wNum mj) * wDen s0 := by rw [Nat.mul_comm (wNum mj)]
          _ = (dMax * wDen (S (j + 1))) * (wNum mj * wDen s0) := by
                rw [← Nat.mul_assoc dMax, Nat.mul_assoc (dMax * wDen (S (j + 1)))]
      have hc2 : (dMax * wNum s0 * wDen (S (j + 1))) * wDen mj =
          (dMax * wDen (S (j + 1))) * (wNum s0 * wDen mj) := by
        calc
          (dMax * wNum s0 * wDen (S (j + 1))) * wDen mj
              = dMax * (wNum s0 * wDen (S (j + 1))) * wDen mj := by rw [Nat.mul_assoc dMax]
          _ = dMax * (wDen (S (j + 1)) * wNum s0) * wDen mj := by rw [Nat.mul_comm (wNum s0)]
          _ = (dMax * wDen (S (j + 1))) * (wNum s0 * wDen mj) := by
                rw [← Nat.mul_assoc dMax, Nat.mul_assoc (dMax * wDen (S (j + 1)))]
      rw [hc, hc2]
      exact Nat.mul_le_mul_left _ hc15
    rw [hm_left]
    exact Nat.le_trans hm_mid hm_right
  have hind_J : ∀ J : Nat,
      (dMax * wNum (S J) + J * wDen (S J)) * wDen 4 ≤ dMax * wNum 4 * wDen (S J) := by
    intro J
    induction J with
    | zero =>
      have hs0 : S 0 = 4 := rfl
      rw [hs0]; simp
    | succ J' ih =>
      have hs := hstep_S J'
      have hden_SJ : wDen (S J') > 0 := (hw.2.2.1 (S J') (by have := hS_ge4 J'; omega)).2
      apply nat_mul_le_cancel_right_w5 (wDen (S J')) _ _ hden_SJ
      have hl : ((dMax * wNum (S (J' + 1)) + (J' + 1) * wDen (S (J' + 1))) * wDen 4) * wDen (S J') =
          ((dMax * wNum (S (J' + 1)) + wDen (S (J' + 1))) * wDen (S J')) * wDen 4 +
            (J' * wDen (S J')) * wDen 4 * wDen (S (J' + 1)) := by
        have hsplit : dMax * wNum (S (J' + 1)) + (J' + 1) * wDen (S (J' + 1)) =
            (dMax * wNum (S (J' + 1)) + wDen (S (J' + 1))) + J' * wDen (S (J' + 1)) := by
          rw [Nat.succ_mul]; omega
        rw [hsplit,
            Nat.add_mul (dMax * wNum (S (J' + 1)) + wDen (S (J' + 1)))
              (J' * wDen (S (J' + 1))) (wDen 4),
            Nat.add_mul _ _ (wDen (S J'))]
        have h1 : ((dMax * wNum (S (J' + 1)) + wDen (S (J' + 1))) * wDen 4) * wDen (S J') =
            ((dMax * wNum (S (J' + 1)) + wDen (S (J' + 1))) * wDen (S J')) * wDen 4 := by
          rw [Nat.mul_assoc, Nat.mul_comm (wDen 4), ← Nat.mul_assoc]
        have h2 : ((J' * wDen (S (J' + 1))) * wDen 4) * wDen (S J') =
            (J' * wDen (S J')) * wDen 4 * wDen (S (J' + 1)) := by
          calc
            ((J' * wDen (S (J' + 1))) * wDen 4) * wDen (S J')
                = J' * (wDen (S (J' + 1)) * (wDen 4 * wDen (S J'))) := by
                  rw [Nat.mul_assoc, Nat.mul_assoc]
            _ = J' * ((wDen (S J') * wDen 4) * wDen (S (J' + 1))) := by
                  rw [Nat.mul_comm (wDen 4) (wDen (S J')),
                      Nat.mul_comm (wDen (S (J' + 1)))]
            _ = (J' * wDen (S J')) * wDen 4 * wDen (S (J' + 1)) := by
                  rw [← Nat.mul_assoc J', ← Nat.mul_assoc J']
        rw [h1, h2]
      have hm1 : ((dMax * wNum (S (J' + 1)) + wDen (S (J' + 1))) * wDen (S J')) * wDen 4 ≤
          (dMax * wNum (S J') * wDen (S (J' + 1))) * wDen 4 :=
        Nat.mul_le_mul_right (wDen 4) hs
      have hcomb : (dMax * wNum (S J') * wDen (S (J' + 1))) * wDen 4 +
          (J' * wDen (S J')) * wDen 4 * wDen (S (J' + 1)) =
          ((dMax * wNum (S J') + J' * wDen (S J')) * wDen 4) * wDen (S (J' + 1)) := by
        rw [Nat.add_mul (dMax * wNum (S J')), Nat.add_mul]
        have hc : (dMax * wNum (S J') * wDen (S (J' + 1))) * wDen 4 =
            (dMax * wNum (S J') * wDen 4) * wDen (S (J' + 1)) := by
          rw [Nat.mul_assoc (dMax * wNum (S J')), Nat.mul_comm (wDen (S (J' + 1))) (wDen 4),
              ← Nat.mul_assoc (dMax * wNum (S J'))]
        rw [hc]
      have hm2 : ((dMax * wNum (S J') + J' * wDen (S J')) * wDen 4) * wDen (S (J' + 1)) ≤
          (dMax * wNum 4 * wDen (S J')) * wDen (S (J' + 1)) :=
        Nat.mul_le_mul_right (wDen (S (J' + 1))) ih
      have hr : (dMax * wNum 4 * wDen (S J')) * wDen (S (J' + 1)) =
          (dMax * wNum 4 * wDen (S (J' + 1))) * wDen (S J') := by
        rw [Nat.mul_assoc (dMax * wNum 4), Nat.mul_comm (wDen (S J')), ← Nat.mul_assoc]
      rw [hl]
      have hsum_le := Nat.add_le_add_right hm1 ((J' * wDen (S J')) * wDen 4 * wDen (S (J' + 1)))
      rw [hcomb] at hsum_le
      rw [← hr]
      exact Nat.le_trans hsum_le hm2
  let Jbad := dMax * wNum 4 + 1
  have hbad := hind_J Jbad
  have hden_SJbad : wDen (S Jbad) > 0 := (hw.2.2.1 (S Jbad) (by have := hS_ge4 Jbad; omega)).2
  have hden4 : wDen 4 ≥ 1 := (hw.2.2.1 4 (by decide)).2
  have hdrop : (Jbad * wDen 4) * wDen (S Jbad) ≤ (dMax * wNum 4) * wDen (S Jbad) := by
    have h1 : (Jbad * wDen 4) * wDen (S Jbad) ≤
        (dMax * wNum (S Jbad) + Jbad * wDen (S Jbad)) * wDen 4 := by
      have hc : (Jbad * wDen 4) * wDen (S Jbad) = (Jbad * wDen (S Jbad)) * wDen 4 := by
        rw [Nat.mul_assoc, Nat.mul_comm (wDen 4) (wDen (S Jbad)), ← Nat.mul_assoc]
      rw [hc, Nat.add_mul (dMax * wNum (S Jbad)) (Jbad * wDen (S Jbad)) (wDen 4)]
      exact Nat.le_add_left ((Jbad * wDen (S Jbad)) * wDen 4) ((dMax * wNum (S Jbad)) * wDen 4)
    exact Nat.le_trans h1 hbad
  have hfin := nat_mul_le_cancel_right_w5 (wDen (S Jbad)) _ _ hden_SJbad hdrop
  have hm4 : Jbad ≤ Jbad * wDen 4 := by
    have h := Nat.mul_le_mul_left Jbad hden4
    simpa using h
  dsimp [Jbad] at hm4 hfin
  omega

-- ============================================================================
-- SECTION 2A: Front B (Branch P4.3) — Universal All-Dimension `∀ d ≥ 1`
--             Non-Upper-Triangular Coordinatewise-Monotone Matrix Collapse
-- ============================================================================

theorem natSumPrefix_mono_w5 (d : Nat) (f g : Fin d -> Nat)
    (hfg : ∀ k : Fin d, f k ≤ g k) :
    ∀ n : Nat, natSumPrefix d f n ≤ natSumPrefix d g n
  | 0 => Nat.le_refl 0
  | n + 1 => by
    simp only [natSumPrefix]
    by_cases hn : n < d
    · simp only [hn, dite_true]
      exact Nat.add_le_add (natSumPrefix_mono_w5 d f g hfg n) (hfg ⟨n, hn⟩)
    · simp only [hn, dite_false]
      exact natSumPrefix_mono_w5 d f g hfg n

theorem natSumPrefix_ge_at_w5 (d : Nat) (f : Fin d -> Nat) (k0 : Fin d) :
    ∀ n : Nat, k0.val < n -> f k0 ≤ natSumPrefix d f n
  | 0, hk => by omega
  | n + 1, hk => by
    simp only [natSumPrefix]
    by_cases hn : n < d
    · simp only [hn, dite_true]
      by_cases heq : k0.val = n
      · have hfin : (⟨n, hn⟩ : Fin d) = k0 := Fin.eq_of_val_eq heq.symm
        rw [hfin]; omega
      · have ih := natSumPrefix_ge_at_w5 d f k0 n (by omega)
        omega
    · simp only [hn, dite_false]
      exact natSumPrefix_ge_at_w5 d f k0 n (by have := k0.isLt; omega)

theorem natSumFin_ge_at_w5 (d : Nat) (f : Fin d -> Nat) (k0 : Fin d) :
    f k0 ≤ natSumFin d f :=
  natSumPrefix_ge_at_w5 d f k0 d k0.isLt

theorem natMatMul_mono_left_w5 (d : Nat) (A1 A2 B : Fin d -> Fin d -> Nat)
    (hge : ∀ i j : Fin d, A1 i j ≥ A2 i j) :
    ∀ i j : Fin d, natMatMul d A1 B i j ≥ natMatMul d A2 B i j := by
  intro i j
  exact natSumPrefix_mono_w5 d _ _ (fun k => Nat.mul_le_mul_right (B k j) (hge i k)) d

theorem natMatMul_mono_right_w5 (d : Nat) (A B1 B2 : Fin d -> Fin d -> Nat)
    (hge : ∀ i j : Fin d, B1 i j ≥ B2 i j) :
    ∀ i j : Fin d, natMatMul d A B1 i j ≥ natMatMul d A B2 i j := by
  intro i j
  exact natSumPrefix_mono_w5 d _ _ (fun k => Nat.mul_le_mul_left (A i k) (hge k j)) d

theorem natMatMul_excess_right_w5 (d : Nat) (P Q : Fin d -> Fin d -> Nat)
    (hP_diag : ∀ i : Fin d, P i i ≥ 1)
    (hQ_diag : ∀ i : Fin d, Q i i ≥ 1)
    (i j : Fin d) :
    natMatMul d P Q i j ≥ P i j + (Q i j - natMatId d i j) := by
  unfold natMatMul
  by_cases hij : i.val = j.val
  · have hfin : j = i := Fin.eq_of_val_eq hij.symm
    rw [hfin]
    have hterm := natSumFin_ge_at_w5 d (fun k => P i k * Q k i) i
    change P i i * Q i i ≤ natSumFin d (fun k => P i k * Q k i) at hterm
    have hp1 : P i i ≥ 1 := hP_diag i
    have hq1 : Q i i ≥ 1 := hQ_diag i
    have hmul_ge : P i i * Q i i ≥ P i i + (Q i i - 1) := by
      have hexp : P i i * Q i i = (P i i - 1) * (Q i i - 1) + P i i + Q i i - 1 := by
        have h1 : P i i = (P i i - 1) + 1 := by omega
        have h2 : Q i i = (Q i i - 1) + 1 := by omega
        conv => lhs; rw [h1, h2]
        rw [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
        omega
      omega
    have hid_ii : natMatId d i i = 1 := by simp [natMatId]
    rw [hid_ii]
    omega
  · have hid_ij : natMatId d i j = 0 := by simp [natMatId, hij]
    rw [hid_ij, Nat.sub_zero]
    let twoTerms : Fin d -> Nat := fun k =>
      if k.val = i.val then P i i * Q i j
      else if k.val = j.val then P i j * Q j j
      else 0
    have hle_two : ∀ k : Fin d, twoTerms k ≤ P i k * Q k j := by
      intro k; dsimp [twoTerms]
      by_cases hki : k.val = i.val
      · rw [Fin.eq_of_val_eq hki]; simp
      · simp only [hki, ite_false]
        by_cases hkj : k.val = j.val
        · rw [Fin.eq_of_val_eq hkj]; simp
        · simp only [hkj, ite_false]; omega
    have hsum_ge := natSumPrefix_mono_w5 d twoTerms (fun k => P i k * Q k j) hle_two d
    have htwo_eq : natSumFin d twoTerms = twoTerms i + twoTerms j := by
      apply natSumFin_eq_pair d twoTerms i j hij
      intro k hki hkj; dsimp [twoTerms]; simp [hki, hkj]
    change natSumFin d twoTerms ≤ natSumFin d (fun k => P i k * Q k j) at hsum_ge
    rw [htwo_eq] at hsum_ge
    have hti : twoTerms i = P i i * Q i j := by dsimp [twoTerms]; simp
    have htj : twoTerms j = P i j * Q j j := by
      have hne' : j.val ≠ i.val := fun h => hij h.symm
      dsimp [twoTerms]; simp [hne']
    rw [hti, htj] at hsum_ge
    have hp_q : Q i j ≤ P i i * Q i j := by
      have hm := Nat.mul_le_mul_right (Q i j) (hP_diag i); simpa using hm
    have hp_p : P i j ≤ P i j * Q j j := by
      have hm := Nat.mul_le_mul_left (P i j) (hQ_diag j); simpa using hm
    omega

theorem natMatMul_excess_left_w5 (d : Nat) (P Q : Fin d -> Fin d -> Nat)
    (hP_diag : ∀ i : Fin d, P i i ≥ 1)
    (hQ_diag : ∀ i : Fin d, Q i i ≥ 1)
    (i j : Fin d) :
    natMatMul d P Q i j ≥ Q i j + (P i j - natMatId d i j) := by
  unfold natMatMul
  by_cases hij : i.val = j.val
  · have hfin : j = i := Fin.eq_of_val_eq hij.symm
    rw [hfin]
    have hterm := natSumFin_ge_at_w5 d (fun k => P i k * Q k i) i
    change P i i * Q i i ≤ natSumFin d (fun k => P i k * Q k i) at hterm
    have hp1 : P i i ≥ 1 := hP_diag i
    have hq1 : Q i i ≥ 1 := hQ_diag i
    have hmul_ge : P i i * Q i i ≥ Q i i + (P i i - 1) := by
      have h1 : P i i = (P i i - 1) + 1 := by omega
      have h2 : Q i i = (Q i i - 1) + 1 := by omega
      have hexp : P i i * Q i i = (P i i - 1) * (Q i i - 1) + P i i + Q i i - 1 := by
        conv => lhs; rw [h1, h2]
        rw [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
        omega
      omega
    have hid_ii : natMatId d i i = 1 := by simp [natMatId]
    rw [hid_ii]
    omega
  · have hid_ij : natMatId d i j = 0 := by simp [natMatId, hij]
    rw [hid_ij, Nat.sub_zero]
    let twoTerms : Fin d -> Nat := fun k =>
      if k.val = i.val then P i i * Q i j
      else if k.val = j.val then P i j * Q j j
      else 0
    have hle_two : ∀ k : Fin d, twoTerms k ≤ P i k * Q k j := by
      intro k; dsimp [twoTerms]
      by_cases hki : k.val = i.val
      · rw [Fin.eq_of_val_eq hki]; simp
      · simp only [hki, ite_false]
        by_cases hkj : k.val = j.val
        · rw [Fin.eq_of_val_eq hkj]; simp
        · simp only [hkj, ite_false]; omega
    have hsum_ge := natSumPrefix_mono_w5 d twoTerms (fun k => P i k * Q k j) hle_two d
    have htwo_eq : natSumFin d twoTerms = twoTerms i + twoTerms j := by
      apply natSumFin_eq_pair d twoTerms i j hij
      intro k hki hkj; dsimp [twoTerms]; simp [hki, hkj]
    change natSumFin d twoTerms ≤ natSumFin d (fun k => P i k * Q k j) at hsum_ge
    rw [htwo_eq] at hsum_ge
    have hti : twoTerms i = P i i * Q i j := by dsimp [twoTerms]; simp
    have htj : twoTerms j = P i j * Q j j := by
      have hne' : j.val ≠ i.val := fun h => hij h.symm
      dsimp [twoTerms]; simp [hne']
    rw [hti, htj] at hsum_ge
    have hp_q : Q i j ≤ P i i * Q i j := by
      have hm := Nat.mul_le_mul_right (Q i j) (hP_diag i); simpa using hm
    have hp_p : P i j ≤ P i j * Q j j := by
      have hm := Nat.mul_le_mul_left (P i j) (hQ_diag j); simpa using hm
    omega

theorem natMatMul_left_id_w5 (d : Nat) (B : Fin d -> Fin d -> Nat) (i j : Fin d) :
    natMatMul d (natMatId d) B i j = B i j := by
  unfold natMatMul
  rw [natSumFin_eq_single d _ i]
  · simp [natMatId]
  · intro k hk
    have hne : i.val ≠ k.val := fun h => hk h.symm
    simp [natMatId, hne]

theorem natMatMul_diag_ge_one_w5 (d : Nat) (A B : Fin d -> Fin d -> Nat)
    (hA : ∀ i : Fin d, A i i ≥ 1) (hB : ∀ i : Fin d, B i i ≥ 1) (i : Fin d) :
    natMatMul d A B i i ≥ 1 := by
  have hterm := natSumFin_ge_at_w5 d (fun k => A i k * B k i) i
  change A i i * B i i ≤ natMatMul d A B i i at hterm
  have hm := Nat.mul_le_mul (hA i) (hB i)
  omega

theorem natMatMul_assoc_w5 (d : Nat) (A B C : Fin d -> Fin d -> Nat) (i j : Fin d) :
    natMatMul d (natMatMul d A B) C i j = natMatMul d A (natMatMul d B C) i j := by
  have hzero_sum : ∀ m : Nat, natSumPrefix d (fun _ => 0) m = 0 := by
    intro m
    induction m with
    | zero => rfl
    | succ m' ihm =>
      simp only [natSumPrefix]
      by_cases hm : m' < d
      · simp only [hm, dite_true, Nat.add_zero, ihm]
      · simp only [hm, dite_false, Nat.add_zero, ihm]
  have hmul_sum_r : ∀ (f : Fin d -> Nat) (c n : Nat),
      natSumPrefix d f n * c = natSumPrefix d (fun k => f k * c) n := by
    intro f c n
    induction n with
    | zero => simp [natSumPrefix]
    | succ n' ih =>
      simp only [natSumPrefix]
      by_cases hn : n' < d
      · simp only [hn, dite_true, Nat.add_mul, ih]
      · simp only [hn, dite_false, Nat.add_zero, ih]
  have hmul_sum_l : ∀ (c : Nat) (f : Fin d -> Nat) (n : Nat),
      c * natSumPrefix d f n = natSumPrefix d (fun k => c * f k) n := by
    intro c f n
    induction n with
    | zero => simp [natSumPrefix]
    | succ n' ih =>
      simp only [natSumPrefix]
      by_cases hn : n' < d
      · simp only [hn, dite_true, Nat.mul_add, ih]
      · simp only [hn, dite_false, Nat.add_zero, ih]
  have hswap : ∀ (F : Fin d -> Fin d -> Nat) (m n : Nat),
      natSumPrefix d (fun q => natSumPrefix d (fun p => F p q) m) n =
        natSumPrefix d (fun p => natSumPrefix d (fun q => F p q) n) m := by
    intro F m n
    induction n with
    | zero =>
      simp only [natSumPrefix]
      exact (hzero_sum m).symm
    | succ n' ihn =>
      simp only [natSumPrefix]
      by_cases hn : n' < d
      · simp only [hn, dite_true, ihn, ← natSumPrefix_add]
      · simp only [hn, dite_false, Nat.add_zero, ihn]
  unfold natMatMul natSumFin
  have hl : natSumPrefix d (fun q => natSumPrefix d (fun p => A i p * B p q) d * C q j) d =
      natSumPrefix d (fun q => natSumPrefix d (fun p => A i p * B p q * C q j) d) d :=
    natSumPrefix_congr d _ _ (fun q => hmul_sum_r (fun p => A i p * B p q) (C q j) d) d
  have hr : natSumPrefix d (fun p => A i p * natSumPrefix d (fun q => B p q * C q j) d) d =
      natSumPrefix d (fun p => natSumPrefix d (fun q => A i p * B p q * C q j) d) d :=
    natSumPrefix_congr d _ _ (fun p =>
      (hmul_sum_l (A i p) (fun q => B p q * C q j) d).trans
        (natSumPrefix_congr d _ _ (fun q => (Nat.mul_assoc _ _ _).symm) d)) d
  rw [hl, hr, hswap]

theorem natMatMul_sandwich_excess_w5 (d : Nat) (Y Q MR : Fin d -> Fin d -> Nat)
    (hY : ∀ i : Fin d, Y i i ≥ 1)
    (hQ : ∀ i : Fin d, Q i i ≥ 1)
    (hR : ∀ i : Fin d, MR i i ≥ 1)
    (i j : Fin d) :
    natMatMul d (natMatMul d Y Q) MR i j ≥
      natMatMul d Y MR i j + (Q i j - natMatId d i j) := by
  have hk_ge : ∀ k : Fin d,
      natMatMul d Y Q i k * MR k j ≥
        Y i k * MR k j + (if k.val = j.val then Q i j - natMatId d i j else 0) := by
    intro k
    have hxy := natMatMul_excess_right_w5 d Y Q hY hQ i k
    by_cases hkj : k.val = j.val
    · rw [Fin.eq_of_val_eq hkj] at hxy ⊢
      simp only [ite_true]
      have hm := Nat.mul_le_mul_right (MR j j) hxy
      rw [Nat.add_mul] at hm
      have hd_mr : (Q i j - natMatId d i j) ≤ (Q i j - natMatId d i j) * MR j j := by
        have h := Nat.mul_le_mul_left (Q i j - natMatId d i j) (hR j); simpa using h
      exact Nat.le_trans (Nat.add_le_add_left hd_mr (Y i j * MR j j)) hm
    · simp only [hkj, ite_false, Nat.add_zero]
      exact Nat.mul_le_mul_right (MR k j) (Nat.le_trans (Nat.le_add_right (Y i k) _) hxy)
  have hsum_le := natSumPrefix_mono_w5 d
    (fun k => Y i k * MR k j + (if k.val = j.val then Q i j - natMatId d i j else 0))
    (fun k => natMatMul d Y Q i k * MR k j) hk_ge d
  have hjl : j.val < d := j.isLt
  rw [natSumPrefix_add d (fun k => Y i k * MR k j)
        (fun k => if k.val = j.val then Q i j - natMatId d i j else 0) d,
      natSumPrefix_single d j (Q i j - natMatId d i j) d] at hsum_le
  simp only [hjl, ite_true] at hsum_le
  exact hsum_le

/--
  Theorem W5.2a (`all_dim_coord_monotone_non_triangular_impossibility`, zero custom axioms):
  Universal All-Dimension (`∀ d ≥ 1`) Full Non-Triangular Matrix Collapse:
  Completely dropping Wave 3's upper-triangularity hypothesis `IsUpperTriMat`, ANY
  coordinatewise-monotone (`∀ s i, (interp s).M i i ≥ 1`) Natural Matrix Interpretation
  `interp : MixedSRSSym -> NatAffineDim d` orienting `{R2, R5, R7, R8, R9, R11}` collapses
  to `M_s = I_d` across `{B0, B1, T0, T1, T2}` via `L * (·) * R` sandwiching and fails `R8`!
-/
theorem all_dim_coord_monotone_non_triangular_impossibility (d : Nat) (hd : 0 < d)
    (interp : MixedSRSSym -> NatAffineDim d)
    (hdiag_pos : ∀ (s : MixedSRSSym) (i : Fin d), (interp s).M i i ≥ 1)
    (hR2  : orientsNatAffineDim d hd (evalWordNatAffineDim d interp [.L, .B1])
              (evalWordNatAffineDim d interp [.L, .T2]))
    (hR5  : orientsNatAffineDim d hd (evalWordNatAffineDim d interp [.T1, .B0])
              (evalWordNatAffineDim d interp [.B1, .T0]))
    (hR7  : orientsNatAffineDim d hd (evalWordNatAffineDim d interp [.T2, .B0])
              (evalWordNatAffineDim d interp [.B0, .T1]))
    (hR8  : orientsNatAffineDim d hd (evalWordNatAffineDim d interp [.T2, .B1])
              (evalWordNatAffineDim d interp [.B1, .T2]))
    (hR9  : orientsNatAffineDim d hd (evalWordNatAffineDim d interp [.T0, .R])
              (evalWordNatAffineDim d interp [.B1, .R]))
    (hR11 : orientsNatAffineDim d hd (evalWordNatAffineDim d interp [.T2, .R])
              (evalWordNatAffineDim d interp [.B1, .B0, .R])) :
    False := by
  let ML := (interp .L).M
  let MR := (interp .R).M
  let MB0 := (interp .B0).M
  let MB1 := (interp .B1).M
  let MT0 := (interp .T0).M
  let MT1 := (interp .T1).M
  let MT2 := (interp .T2).M
  have hr2_m : ∀ i j : Fin d, natMatMul d ML MB1 i j ≥ natMatMul d ML MT2 i j := by
    intro i j; have h := hR2.1 i j; rwa [evalWord2_M, evalWord2_M] at h
  have hr5_m : ∀ i j : Fin d, natMatMul d MT1 MB0 i j ≥ natMatMul d MB1 MT0 i j := by
    intro i j; have h := hR5.1 i j; rwa [evalWord2_M, evalWord2_M] at h
  have hr7_m : ∀ i j : Fin d, natMatMul d MT2 MB0 i j ≥ natMatMul d MB0 MT1 i j := by
    intro i j; have h := hR7.1 i j; rwa [evalWord2_M, evalWord2_M] at h
  have hr9_m : ∀ i j : Fin d, natMatMul d MT0 MR i j ≥ natMatMul d MB1 MR i j := by
    intro i j; have h := hR9.1 i j; rwa [evalWord2_M, evalWord2_M] at h
  have hr11_m : ∀ i j : Fin d,
      natMatMul d MT2 MR i j ≥ natMatMul d MB1 (natMatMul d MB0 MR) i j := by
    intro i j; have h := hR11.1 i j; rwa [evalWord2_M, evalWord3_M] at h
  have hLB1R_ge_LT2R : ∀ i j : Fin d,
      natMatMul d (natMatMul d ML MB1) MR i j ≥ natMatMul d (natMatMul d ML MT2) MR i j :=
    natMatMul_mono_left_w5 d _ _ MR hr2_m
  have hLT2R_ge_LB1B0R : ∀ i j : Fin d,
      natMatMul d (natMatMul d ML MT2) MR i j ≥
        natMatMul d (natMatMul d (natMatMul d ML MB1) MB0) MR i j := by
    intro i j
    rw [natMatMul_assoc_w5 d ML MT2 MR i j,
        natMatMul_assoc_w5 d (natMatMul d ML MB1) MB0 MR i j,
        natMatMul_assoc_w5 d ML MB1 (natMatMul d MB0 MR) i j]
    exact natMatMul_mono_right_w5 d ML _ _ hr11_m i j
  have hLB1_diag : ∀ i : Fin d, natMatMul d ML MB1 i i ≥ 1 :=
    natMatMul_diag_ge_one_w5 d ML MB1 (hdiag_pos .L) (hdiag_pos .B1)
  have hMB0_id : ∀ i j : Fin d, MB0 i j = natMatId d i j := by
    intro i j
    have h1 := hLB1R_ge_LT2R i j
    have h2 := hLT2R_ge_LB1B0R i j
    have hprop_r := natMatMul_sandwich_excess_w5 d (natMatMul d ML MB1) MB0 MR
      hLB1_diag (hdiag_pos .B0) (hdiag_pos .R) i j
    by_cases hij : i.val = j.val
    · rw [Fin.eq_of_val_eq hij] at h1 h2 hprop_r ⊢
      have hid1 : natMatId d j j = 1 := by simp [natMatId]
      have hd1 : MB0 j j ≥ 1 := hdiag_pos .B0 j
      rw [hid1] at hprop_r ⊢
      omega
    · have hid0 : natMatId d i j = 0 := by simp [natMatId, hij]
      rw [hid0] at hprop_r ⊢
      omega
  have hLB1R_eq_LT2R : ∀ i j : Fin d,
      natMatMul d (natMatMul d ML MB1) MR i j = natMatMul d (natMatMul d ML MT2) MR i j := by
    intro i j
    have h1 := hLB1R_ge_LT2R i j
    have h2 := hLT2R_ge_LB1B0R i j
    have hB0_eq : ∀ p q : Fin d, natMatMul d (natMatMul d ML MB1) MB0 p q = natMatMul d ML MB1 p q := by
      intro p q
      have hc : ∀ k : Fin d, natMatMul d ML MB1 p k * MB0 k q =
          natMatMul d ML MB1 p k * natMatId d k q := fun k => by rw [hMB0_id]
      exact (natSumPrefix_congr d _ _ hc d).trans (natMatMul_right_id d _ p q)
    have h3 : natMatMul d (natMatMul d (natMatMul d ML MB1) MB0) MR i j =
        natMatMul d (natMatMul d ML MB1) MR i j :=
      natSumPrefix_congr d _ _ (fun k => by rw [hB0_eq]) d
    omega
  have hMT2_ge_MT1 : ∀ i j : Fin d, MT2 i j ≥ MT1 i j := by
    intro i j
    have h7 := hr7_m i j
    have hl : natMatMul d MT2 MB0 i j = MT2 i j :=
      (natSumPrefix_congr d _ _ (fun k => by rw [hMB0_id]) d).trans (natMatMul_right_id d MT2 i j)
    have hr : natMatMul d MB0 MT1 i j = MT1 i j :=
      (natSumPrefix_congr d _ _ (fun k => by rw [hMB0_id]) d).trans (natMatMul_left_id_w5 d MT1 i j)
    rwa [hl, hr] at h7
  have hMT1_ge_MB1T0 : ∀ i j : Fin d, MT1 i j ≥ natMatMul d MB1 MT0 i j := by
    intro i j
    have h5 := hr5_m i j
    have hl : natMatMul d MT1 MB0 i j = MT1 i j :=
      (natSumPrefix_congr d _ _ (fun k => by rw [hMB0_id]) d).trans (natMatMul_right_id d MT1 i j)
    rwa [hl] at h5
  have hMT2_ge_MB1T0 : ∀ i j : Fin d, MT2 i j ≥ natMatMul d MB1 MT0 i j :=
    fun i j => Nat.le_trans (hMT1_ge_MB1T0 i j) (hMT2_ge_MT1 i j)
  have hMT0_id : ∀ i j : Fin d, MT0 i j = natMatId d i j := by
    intro i j
    have hlt2_ge : natMatMul d (natMatMul d ML MT2) MR i j ≥
        natMatMul d (natMatMul d (natMatMul d ML MB1) MT0) MR i j := by
      have hm1 := natMatMul_mono_left_w5 d _ _ MR
        (natMatMul_mono_right_w5 d ML MT2 (natMatMul d MB1 MT0) hMT2_ge_MB1T0) i j
      have hassoc : natMatMul d (natMatMul d ML (natMatMul d MB1 MT0)) MR i j =
          natMatMul d (natMatMul d (natMatMul d ML MB1) MT0) MR i j :=
        natSumPrefix_congr d _ _ (fun k => by rw [← natMatMul_assoc_w5 d ML MB1 MT0 i k]) d
      rwa [hassoc] at hm1
    rw [← hLB1R_eq_LT2R i j] at hlt2_ge
    have hsum_le := natMatMul_sandwich_excess_w5 d (natMatMul d ML MB1) MT0 MR
      hLB1_diag (hdiag_pos .T0) (hdiag_pos .R) i j
    by_cases hij : i.val = j.val
    · rw [Fin.eq_of_val_eq hij] at hlt2_ge hsum_le ⊢
      have hid1 : natMatId d j j = 1 := by simp [natMatId]
      have hd1 : MT0 j j ≥ 1 := hdiag_pos .T0 j
      rw [hid1] at hsum_le ⊢
      omega
    · have hid0 : natMatId d i j = 0 := by simp [natMatId, hij]
      rw [hid0] at hsum_le ⊢
      omega
  have hMB1_id : ∀ i j : Fin d, MB1 i j = natMatId d i j := by
    intro i j
    have h9 := hr9_m i j
    have hl : natMatMul d MT0 MR i j = MR i j :=
      (natSumPrefix_congr d _ _ (fun k => by rw [hMT0_id]) d).trans (natMatMul_left_id_w5 d MR i j)
    rw [hl] at h9
    have hex := natMatMul_excess_left_w5 d MB1 MR (hdiag_pos .B1) (hdiag_pos .R) i j
    by_cases hij : i.val = j.val
    · rw [Fin.eq_of_val_eq hij] at h9 hex ⊢
      have hid1 : natMatId d j j = 1 := by simp [natMatId]
      have hd1 : MB1 j j ≥ 1 := hdiag_pos .B1 j
      rw [hid1] at hex ⊢; omega
    · have hid0 : natMatId d i j = 0 := by simp [natMatId, hij]
      rw [hid0] at hex ⊢; omega
  have hMT2_id : ∀ i j : Fin d, MT2 i j = natMatId d i j := by
    intro i j
    have h2 := hr2_m i j
    have hl : natMatMul d ML MB1 i j = ML i j :=
      (natSumPrefix_congr d _ _ (fun k => by rw [hMB1_id]) d).trans (natMatMul_right_id d ML i j)
    rw [hl] at h2
    have hex := natMatMul_excess_right_w5 d ML MT2 (hdiag_pos .L) (hdiag_pos .T2) i j
    by_cases hij : i.val = j.val
    · rw [Fin.eq_of_val_eq hij] at h2 hex ⊢
      have hid1 : natMatId d j j = 1 := by simp [natMatId]
      have hd1 : MT2 j j ≥ 1 := hdiag_pos .T2 j
      rw [hid1] at hex ⊢; omega
    · have hid0 : natMatId d i j = 0 := by simp [natMatId, hij]
      rw [hid0] at hex ⊢; omega
  have heval_v2 : ∀ (s1 s2 : MixedSRSSym),
      (∀ i j : Fin d, (interp s1).M i j = natMatId d i j) ->
      (∀ i j : Fin d, (interp s2).M i j = natMatId d i j) ->
      (evalWordNatAffineDim d interp [s1, s2]).v ⟨0, hd⟩ =
        (interp s2).v ⟨0, hd⟩ + (interp s1).v ⟨0, hd⟩ := by
    intro s1 s2 hs1 _
    simp only [evalWordNatAffineDim, compNatAffineDim]
    have hv_zero : natMatVec d (interp s2).M (fun _ => 0) = fun _ => 0 := by
      funext p; unfold natMatVec
      rw [natSumFin_eq_single d _ p]
      · simp
      · intro _ _; simp
    rw [hv_zero]
    simp only [Nat.zero_add]
    have hmv : natMatVec d (interp s1).M (interp s2).v ⟨0, hd⟩ = (interp s2).v ⟨0, hd⟩ := by
      unfold natMatVec natSumFin
      have hc : ∀ k : Fin d, (interp s1).M ⟨0, hd⟩ k * (interp s2).v k =
          natMatId d ⟨0, hd⟩ k * (interp s2).v k := fun k => by rw [hs1]
      rw [natSumPrefix_congr d _ _ hc d]
      exact natMatVec_id d (interp s2).v ⟨0, hd⟩
    rw [hmv]
  have hstrict := hR8.2.2
  rw [heval_v2 .T2 .B1 hMT2_id hMB1_id, heval_v2 .B1 .T2 hMB1_id hMT2_id] at hstrict
  omega

-- ============================================================================
-- SECTION 2B: Front B (Branch P5) — Closer Solvable `(3x+1)` Cousin `T_diamond2`
--             (Unbounded Glides + Genuine `v_2 ≥ 2` Syracuse Jumps), 1-Term
--             Monomial Impossibility, & Global Convergence via 2-Term `Φ_diamond2`
-- ============================================================================

theorem core2Aux_eq_of_ge :
    ∀ (f1 f2 n : Nat), n ≤ f1 -> n ≤ f2 -> core2Aux f1 n = core2Aux f2 n
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
    simp only [core2Aux]
    by_cases hc : n > 0 ∧ n % 2 = 0
    · simp only [hc, and_self, ite_true]
      exact core2Aux_eq_of_ge f1 f2 (n / 2) (by omega) (by omega)
    · simp only [hc, ite_false]

theorem core2_of_odd (n : Nat) (hodd : n % 2 = 1) : core2 n = n := by
  unfold core2
  cases n with
  | zero => omega
  | succ m =>
    have hnc : ¬ (m + 1 > 0 ∧ (m + 1) % 2 = 0) := by omega
    simp only [core2Aux, hnc, ite_false]

theorem core2_mul2 (m : Nat) (hm : m > 0) : core2 (2 * m) = core2 m := by
  unfold core2
  cases hfuel : 2 * m with
  | zero => omega
  | succ f =>
    have hc : f + 1 > 0 ∧ (f + 1) % 2 = 0 := by omega
    simp only [core2Aux, hc, and_self, ite_true]
    have hdiv : (f + 1) / 2 = m := by omega
    rw [hdiv]
    exact core2Aux_eq_of_ge f m m (by omega) (by omega)

theorem core2_decomp_aux :
    ∀ (bound n : Nat), n > 0 -> n ≤ bound ->
      1 ≤ v2Pow n ∧ 1 ≤ core2 n ∧ core2 n % 2 = 1 ∧ v2Pow n * core2 n = n
  | 0, _, hn, hle => by omega
  | bound + 1, n, hn, hle => by
    by_cases hev : n % 2 = 0
    · let k := n / 2
      have hk_pos : k > 0 := by dsimp [k]; omega
      have hn_eq : n = 2 * k := by dsimp [k]; omega
      rw [hn_eq, v2Pow_mul2 k hk_pos, core2_mul2 k hk_pos]
      rcases core2_decomp_aux bound k hk_pos (by dsimp [k]; omega) with ⟨h1, h2, hodd, hmul⟩
      refine ⟨by omega, h2, hodd, ?_⟩
      rw [Nat.mul_assoc, hmul]
    · have hodd : n % 2 = 1 := by omega
      rw [v2Pow_of_odd n hodd, core2_of_odd n hodd, Nat.one_mul]
      exact ⟨Nat.le_refl 1, by omega, hodd, rfl⟩

theorem core2_decomp (n : Nat) (hn : n > 0) :
    1 ≤ v2Pow n ∧ 1 ≤ core2 n ∧ core2 n % 2 = 1 ∧ v2Pow n * core2 n = n :=
  core2_decomp_aux n n hn (Nat.le_refl n)

theorem core3_decomp_aux :
    ∀ (bound n : Nat), n > 0 -> n ≤ bound ->
      1 ≤ v3Pow n ∧ 1 ≤ core3 n ∧ core3 n % 3 ≠ 0 ∧
      (v3Pow n % 8 = 1 ∨ v3Pow n % 8 = 3) ∧
      v3Pow n * core3 n = n
  | 0, _, hn, hle => by omega
  | bound + 1, n, hn, hle => by
    by_cases hd3 : n % 3 = 0
    · let k := n / 3
      have hk_pos : k > 0 := by dsimp [k]; omega
      have hn_eq : n = 3 * k := by dsimp [k]; omega
      rw [hn_eq, v3Pow_mul3 k hk_pos, core3_mul3 k hk_pos]
      rcases core3_decomp_aux bound k hk_pos (by dsimp [k]; omega) with
        ⟨h1, h2, hnd3, hm8, hmul⟩
      refine ⟨by omega, h2, hnd3, ?_, ?_⟩
      · rcases hm8 with hm1 | hm3
        · right; omega
        · left; omega
      · rw [Nat.mul_assoc, hmul]
    · rw [v3Pow_of_not_div3 n hd3, core3_not_div3 n hd3, Nat.one_mul]
      exact ⟨Nat.le_refl 1, by omega, hd3, Or.inl rfl, rfl⟩

theorem core3_decomp (n : Nat) (hn : n > 0) :
    1 ≤ v3Pow n ∧ 1 ≤ core3 n ∧ core3 n % 3 ≠ 0 ∧
    (v3Pow n % 8 = 1 ∨ v3Pow n % 8 = 3) ∧
    v3Pow n * core3 n = n :=
  core3_decomp_aux n n hn (Nat.le_refl n)

theorem v2Pow_core3_eq_aux :
    ∀ (bound n : Nat), n > 0 -> n ≤ bound -> v2Pow (core3 n) = v2Pow n
  | 0, _, hn, hle => by omega
  | bound + 1, n, hn, hle => by
    by_cases hd3 : n % 3 = 0
    · let k := n / 3
      have hk_pos : k > 0 := by dsimp [k]; omega
      have hn_eq : n = 3 * k := by dsimp [k]; omega
      rw [hn_eq, core3_mul3 k hk_pos, v2Pow_mul3 k hk_pos]
      exact v2Pow_core3_eq_aux bound k hk_pos (by dsimp [k]; omega)
    · rw [core3_not_div3 n hd3]

theorem decomp_2_3_exact (n : Nat) (hn : n > 0) :
    1 ≤ v2Pow n ∧ 1 ≤ v3Pow n ∧ 1 ≤ coprime23Core n ∧
    coprime23Core n % 2 = 1 ∧
    (v3Pow n % 8 = 1 ∨ v3Pow n % 8 = 3) ∧
    v2Pow n * v3Pow n * coprime23Core n = n := by
  rcases core3_decomp n hn with ⟨hv3, hc3, _, hm8, hm3⟩
  rcases core2_decomp (core3 n) hc3 with ⟨_, hcc, hcc_odd, hm2⟩
  have hv2_eq : v2Pow (core3 n) = v2Pow n := v2Pow_core3_eq_aux n n hn (Nat.le_refl n)
  rw [hv2_eq] at hm2
  unfold coprime23Core
  refine ⟨(core2_decomp n hn).1, hv3, hcc, hcc_odd, hm8, ?_⟩
  calc
    v2Pow n * v3Pow n * core2 (core3 n)
        = v3Pow n * (v2Pow n * core2 (core3 n)) := by
          rw [Nat.mul_comm (v2Pow n) (v3Pow n), Nat.mul_assoc]
    _ = v3Pow n * core3 n := by rw [hm2]
    _ = n := hm3

theorem coprime23Core_mul2 (m : Nat) (hm : m > 0) :
    coprime23Core (2 * m) = coprime23Core m := by
  unfold coprime23Core
  rw [core3_mul2 m hm, core2_mul2 (core3 m) (core3_decomp m hm).2.1]

theorem coprime23Core_mul3 (m : Nat) (hm : m > 0) :
    coprime23Core (3 * m) = coprime23Core m := by
  unfold coprime23Core
  rw [core3_mul3 m hm]

theorem coprime23Core_of_coprime (n : Nat) (hodd : n % 2 = 1) (hnd3 : n % 3 ≠ 0) :
    coprime23Core n = n := by
  unfold coprime23Core
  rw [core3_not_div3 n hnd3, core2_of_odd n hodd]

/--
  Closer solvable mixed-(2,3) Collatz cousin `T_diamond2` on `Nat`:
  - Odd `x` in any of the three `v_2(3x + 1) ≥ 2` Syracuse jump cones: `(3 * x + 1) / 4`;
  - All other odd `x` (including all `x % 4 = 3` unbounded Mersenne glides): `(3 * x + 1) / 2`;
  - Even `x > 2` with `x % 6 = 2`: `(x - 2) / 3`;
  - Even `x > 2` with `x % 8 = 6` (`x % 6 ≠ 2`): `(x - 2) / 2`;
  - All other even `x`: `x / 2`.
-/
def cousinDiamond2Step (x : Nat) : Nat :=
  if x % 2 = 1 then
    if (x > 1 ∧ x % 16 = 1 ∧ x % 3 ≠ 2) ∨
       (x ≥ 73 ∧ x % 64 = 9 ∧ x % 3 ≠ 2) ∨
       (x ≥ 17 ∧ core3 (x + 1) = 2)
    then (3 * x + 1) / 4
    else (3 * x + 1) / 2
  else if x > 2 ∧ x % 6 = 2 then (x - 2) / 3
  else if x > 2 ∧ x % 8 = 6 then (x - 2) / 2
  else x / 2

def cousinDiamond2Iter : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamond2Iter k (cousinDiamond2Step x)

/-- Signed extension of `T_diamond2` (`q = 3`) to `Int` for `M2 = Z^-` separation -/
def cousinDiamond2StepInt (x : Int) : Int :=
  if x % 2 ≠ 0 then
    if (x > 1 ∧ x % 16 = 1 ∧ x % 3 ≠ 2) ∨
       (x ≥ 73 ∧ x % 64 = 9 ∧ x % 3 ≠ 2) ∨
       (x ≥ 17 ∧ core3 (x.toNat + 1) = 2)
    then (3 * x + 1) / 4
    else (3 * x + 1) / 2
  else if x > 2 ∧ x % 6 = 2 then (x - 2) / 3
  else if x > 2 ∧ x % 8 = 6 then (x - 2) / 2
  else x / 2

def cousinDiamond2IterInt : Nat -> Int -> Int
  | 0, x => x
  | k + 1, x => cousinDiamond2IterInt k (cousinDiamond2StepInt x)

theorem cousinDiamond2StepInt_ofNat_eq (x : Nat) :
    cousinDiamond2StepInt (x : Int) = (cousinDiamond2Step x : Int) := by
  unfold cousinDiamond2StepInt cousinDiamond2Step
  have htoNat : (x : Int).toNat = x := rfl
  rw [htoNat]
  by_cases hodd : x % 2 = 1
  · have hodd_i : (x : Int) % 2 ≠ 0 := by omega
    simp only [hodd_i, hodd, ne_eq, not_false_eq_true, ite_true]
    have hcond_iff :
        (((x : Int) > 1 ∧ (x : Int) % 16 = 1 ∧ (x : Int) % 3 ≠ 2) ∨
         ((x : Int) ≥ 73 ∧ (x : Int) % 64 = 9 ∧ (x : Int) % 3 ≠ 2) ∨
         ((x : Int) ≥ 17 ∧ core3 (x + 1) = 2)) ↔
        ((x > 1 ∧ x % 16 = 1 ∧ x % 3 ≠ 2) ∨
         (x ≥ 73 ∧ x % 64 = 9 ∧ x % 3 ≠ 2) ∨
         (x ≥ 17 ∧ core3 (x + 1) = 2)) := by
      generalize core3 (x + 1) = c
      omega
    by_cases hq : (x > 1 ∧ x % 16 = 1 ∧ x % 3 ≠ 2) ∨
        (x ≥ 73 ∧ x % 64 = 9 ∧ x % 3 ≠ 2) ∨
        (x ≥ 17 ∧ core3 (x + 1) = 2)
    · have hq_i := hcond_iff.mpr hq
      simp only [hq_i, hq, ite_true]
      omega
    · have hnq_i : ¬ (((x : Int) > 1 ∧ (x : Int) % 16 = 1 ∧ (x : Int) % 3 ≠ 2) ∨
          ((x : Int) ≥ 73 ∧ (x : Int) % 64 = 9 ∧ (x : Int) % 3 ≠ 2) ∨
          ((x : Int) ≥ 17 ∧ core3 (x + 1) = 2)) := fun hi => hq (hcond_iff.mp hi)
      simp only [hnq_i, hq, ite_false]
      omega
  · have hev_i : (x : Int) % 2 = 0 := by omega
    simp only [hev_i, hodd, ne_eq, not_true_eq_false, ite_false]
    by_cases h6 : x > 2 ∧ x % 6 = 2
    · have h6_i : (x : Int) > 2 ∧ (x : Int) % 6 = 2 := by omega
      simp only [h6_i, h6, and_self, ite_true]
      omega
    · have hn6_i : ¬ ((x : Int) > 2 ∧ (x : Int) % 6 = 2) := by omega
      simp only [hn6_i, h6, ite_false]
      by_cases h8 : x > 2 ∧ x % 8 = 6
      · have h8_i : (x : Int) > 2 ∧ (x : Int) % 8 = 6 := by omega
        simp only [h8_i, h8, and_self, ite_true]
        omega
      · have hn8_i : ¬ ((x : Int) > 2 ∧ (x : Int) % 8 = 6) := by omega
        simp only [hn8_i, h8, ite_false]
        omega

/-- Quadratic Hensel inverse modulo `64` for odd `d : Nat` -/
def invMod64Odd (d : Nat) : Nat :=
  let r := d % 64
  let i1 := (66 - r) % 64
  let i2 := (i1 * (66 - (r * i1) % 64)) % 64
  (i2 * (66 - (r * i2) % 64)) % 64

def reduceRatPair (n d : Nat) : Nat × Nat :=
  let g := Nat.gcd n d
  (n / g, d / g)

/-- Canonical reduced-pair extension of `T_diamond2` (`q = 3`) to positive `Q_(6)^+` -/
def cousinDiamond2StepQ6 (p : Nat × Nat) : Nat × Nat :=
  let num := p.1
  let den := p.2
  let r64 := (num * invMod64Odd den) % 64
  let r3 := (num * (den % 3)) % 3
  if r64 % 2 = 1 then
    if (num > den ∧ r64 % 16 = 1 ∧ r3 ≠ 2) ∨
       (num ≥ 73 * den ∧ r64 = 9 ∧ r3 ≠ 2) ∨
       (num ≥ 17 * den ∧ core3 (num + den) = 2 * den)
    then reduceRatPair (3 * num + den) (4 * den)
    else reduceRatPair (3 * num + den) (2 * den)
  else if num > 2 * den ∧ r3 = 2 then reduceRatPair (num - 2 * den) (3 * den)
  else if num > 2 * den ∧ r64 % 8 = 6 then reduceRatPair (num - 2 * den) (2 * den)
  else reduceRatPair num (2 * den)

def cousinDiamond2IterQ6 : Nat -> (Nat × Nat) -> (Nat × Nat)
  | 0, p => p
  | k + 1, p => cousinDiamond2IterQ6 k (cousinDiamond2StepQ6 p)

/-- Generalized odd-multiplier `q` step of `T_diamond2` on `Nat` for `M3` (`q = 7`) separation -/
def cousinDiamond2StepParam (q x : Nat) : Nat :=
  if x % 2 = 1 then
    if (x > 1 ∧ x % 16 = 1 ∧ x % 3 ≠ 2) ∨
       (x ≥ 73 ∧ x % 64 = 9 ∧ x % 3 ≠ 2) ∨
       (x ≥ 17 ∧ core3 (x + 1) = 2)
    then (q * x + 1) / 4
    else (q * x + 1) / 2
  else if x > 2 ∧ x % 6 = 2 then (x - 2) / 3
  else if x > 2 ∧ x % 8 = 6 then (x - 2) / 2
  else x / 2

def cousinDiamond2IterParam (q : Nat) : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamond2IterParam q k (cousinDiamond2StepParam q x)

/--
  2-term positive-integer `(2, 3)`-adic valuation Lyapunov invariant for `T_diamond2`:
    `Φ_diamond2(x) := v2Pow (x + 1) * (coprime23Core (x + 1)) ^ 3 + (v2Pow (x + 1)) ^ 5 * (v3Pow (x + 1)) ^ 3`.
-/
def cousinDiamond2Phi (x : Nat) : Nat :=
  v2Pow (x + 1) * (coprime23Core (x + 1)) ^ 3 + (v2Pow (x + 1)) ^ 5 * (v3Pow (x + 1)) ^ 3

theorem sum_cubes_le_prod_cube_succ (u v : Nat) (hu : u ≥ 1) (hv : v ≥ 1) :
    u ^ 3 + v ^ 3 ≤ (u * v) ^ 3 + 1 := by
  have hu3 : u ^ 3 ≥ 1 := nat_pow_pos_of_pos u hu 3
  have hv3 : v ^ 3 ≥ 1 := nat_pow_pos_of_pos v hv 3
  have h1 : u ^ 3 = (u ^ 3 - 1) + 1 := by omega
  have h2 : v ^ 3 = (v ^ 3 - 1) + 1 := by omega
  rw [mul_pow_local u v 3]
  have hexp : u ^ 3 * v ^ 3 = (u ^ 3 - 1) * (v ^ 3 - 1) + (u ^ 3 - 1) + (v ^ 3 - 1) + 1 := by
    conv => lhs; rw [h1, h2]
    rw [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega
  omega

theorem pow3_strict_mono_w5 (a b : Nat) (hlt : a < b) : a ^ 3 < b ^ 3 := by
  have hc := nat_cube_strict_mono a b hlt
  have ha : a ^ 3 = a * a * a := by
    rw [show (3 : Nat) = 2 + 1 from rfl, Nat.pow_succ, show (2 : Nat) = 1 + 1 from rfl,
        Nat.pow_succ, Nat.pow_one]
  have hb : b ^ 3 = b * b * b := by
    rw [show (3 : Nat) = 2 + 1 from rfl, Nat.pow_succ, show (2 : Nat) = 1 + 1 from rfl,
        Nat.pow_succ, Nat.pow_one]
  rw [ha, hb]; exact hc

theorem cube_3n_plus_1_w5 (n : Nat) :
    (3 * n + 1) ^ 3 = 27 * n ^ 3 + 27 * n ^ 2 + 9 * n + 1 := by
  have h3 : (3 * n + 1) ^ 3 = (3 * n + 1) * (3 * n + 1) * (3 * n + 1) := by
    rw [show (3 : Nat) = 2 + 1 from rfl, Nat.pow_succ, show (2 : Nat) = 1 + 1 from rfl,
        Nat.pow_succ, Nat.pow_one]
  have hn3 : n ^ 3 = n * n * n := by
    rw [show (3 : Nat) = 2 + 1 from rfl, Nat.pow_succ, show (2 : Nat) = 1 + 1 from rfl,
        Nat.pow_succ, Nat.pow_one]
  have hn2 : n ^ 2 = n * n := by
    rw [show (2 : Nat) = 1 + 1 from rfl, Nat.pow_succ, Nat.pow_one]
  rw [h3, hn3, hn2]
  calc
    (3 * n + 1) * (3 * n + 1) * (3 * n + 1)
        = (9 * (n * n) + 6 * n + 1) * (3 * n + 1) := by
          have hsq : (3 * n + 1) * (3 * n + 1) = 9 * (n * n) + 6 * n + 1 := by
            rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.one_mul, Nat.mul_one]
            have h9 : (3 * n) * (3 * n) = 9 * (n * n) := by
              calc
                (3 * n) * (3 * n) = 3 * (n * (3 * n)) := Nat.mul_assoc _ _ _
                _ = 3 * (3 * (n * n)) := by rw [← Nat.mul_assoc n 3 n, Nat.mul_comm n 3, Nat.mul_assoc]
                _ = 9 * (n * n) := (Nat.mul_assoc 3 3 _).symm
            rw [h9]; omega
          rw [hsq]
    _ = 27 * (n * n * n) + 27 * (n * n) + 9 * n + 1 := by
          rw [Nat.add_mul, Nat.add_mul, Nat.one_mul,
              Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_one]
          have h27 : (9 * (n * n)) * (3 * n) = 27 * (n * n * n) := by
            calc
              (9 * (n * n)) * (3 * n) = 9 * ((n * n) * (3 * n)) := Nat.mul_assoc _ _ _
              _ = 9 * (3 * (n * n * n)) := by
                    rw [← Nat.mul_assoc (n * n) 3 n, Nat.mul_comm (n * n) 3, Nat.mul_assoc]
              _ = 27 * (n * n * n) := (Nat.mul_assoc 9 3 _).symm
          have h18 : (6 * n) * (3 * n) = 18 * (n * n) := by
            calc
              (6 * n) * (3 * n) = 6 * (n * (3 * n)) := Nat.mul_assoc _ _ _
              _ = 6 * (3 * (n * n)) := by rw [← Nat.mul_assoc n 3 n, Nat.mul_comm n 3, Nat.mul_assoc]
              _ = 18 * (n * n) := (Nat.mul_assoc 6 3 _).symm
          rw [h27, h18]; omega

theorem cousinDiamond2Step_pos (x : Nat) (hx : x > 0) : cousinDiamond2Step x > 0 := by
  unfold cousinDiamond2Step
  by_cases hodd : x % 2 = 1
  · simp only [hodd, ite_true]
    by_cases hq : (x > 1 ∧ x % 16 = 1 ∧ x % 3 ≠ 2) ∨
        (x ≥ 73 ∧ x % 64 = 9 ∧ x % 3 ≠ 2) ∨ (x ≥ 17 ∧ core3 (x + 1) = 2)
    · simp only [hq, ite_true]
      rcases hq with h1 | h2 | h3 <;> omega
    · simp only [hq, ite_false]; omega
  · simp only [hodd, ite_false]
    by_cases h6 : x > 2 ∧ x % 6 = 2
    · simp only [h6, and_self, ite_true]; omega
    · simp only [h6, ite_false]
      by_cases h8 : x > 2 ∧ x % 8 = 6
      · simp only [h8, and_self, ite_true]; omega
      · simp only [h8, ite_false]; omega

theorem poly_bound_k3_4k11_w5 (u : Nat) :
    32 * (u + 3) ^ 3 + 32 < (4 * u + 11) ^ 3 + 1 := by
  have hl : (u + 3) ^ 3 = u * u * u + 9 * (u * u) + 27 * u + 27 := by
    rw [Nat.pow_succ (u + 3) 2, Nat.pow_succ (u + 3) 1, Nat.pow_one (u + 3)]
    have hsq : (u + 3) * (u + 3) = u * u + 6 * u + 9 := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
      have h3a : u * 3 = 3 * u := Nat.mul_comm u 3
      rw [h3a]; omega
    rw [hsq, Nat.add_mul, Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_add]
    have h1 : (u * u) * 3 = 3 * (u * u) := Nat.mul_comm _ 3
    have h2 : (6 * u) * u = 6 * (u * u) := Nat.mul_assoc 6 u u
    have h3 : (6 * u) * 3 = 18 * u := by
      rw [Nat.mul_assoc, Nat.mul_comm u 3, ← Nat.mul_assoc]
    rw [h1, h2, h3]; omega
  have hr : (4 * u + 11) ^ 3 = 64 * (u * u * u) + 528 * (u * u) + 1452 * u + 1331 := by
    rw [show (3 : Nat) = 2 + 1 from rfl, Nat.pow_succ,
        show (2 : Nat) = 1 + 1 from rfl, Nat.pow_succ, Nat.pow_one]
    have hsq : (4 * u + 11) * (4 * u + 11) = 16 * (u * u) + 88 * u + 121 := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
      have h16 : (4 * u) * (4 * u) = 16 * (u * u) := by
        calc
          (4 * u) * (4 * u) = 4 * (u * (4 * u)) := Nat.mul_assoc _ _ _
          _ = 4 * (4 * (u * u)) := by
                rw [← Nat.mul_assoc u 4 u, Nat.mul_comm u 4, Nat.mul_assoc]
          _ = 16 * (u * u) := (Nat.mul_assoc 4 4 _).symm
      have h44a : (4 * u) * 11 = 44 * u := by
        rw [Nat.mul_assoc, Nat.mul_comm u 11, ← Nat.mul_assoc]
      have h44b : 11 * (4 * u) = 44 * u := (Nat.mul_assoc 11 4 u).symm
      rw [h16, h44a, h44b]; omega
    rw [hsq, Nat.add_mul, Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_add]
    have h64 : (16 * (u * u)) * (4 * u) = 64 * (u * u * u) := by
      calc
        (16 * (u * u)) * (4 * u) = 16 * ((u * u) * (4 * u)) := Nat.mul_assoc _ _ _
        _ = 16 * (4 * (u * u * u)) := by
              rw [← Nat.mul_assoc (u * u) 4 u, Nat.mul_comm (u * u) 4, Nat.mul_assoc]
        _ = 64 * (u * u * u) := (Nat.mul_assoc 16 4 _).symm
    have h176 : (16 * (u * u)) * 11 = 176 * (u * u) := by
      rw [Nat.mul_assoc, Nat.mul_comm (u * u) 11, ← Nat.mul_assoc]
    have h352 : (88 * u) * (4 * u) = 352 * (u * u) := by
      calc
        (88 * u) * (4 * u) = 88 * (u * (4 * u)) := Nat.mul_assoc _ _ _
        _ = 88 * (4 * (u * u)) := by
              rw [← Nat.mul_assoc u 4 u, Nat.mul_comm u 4, Nat.mul_assoc]
        _ = 352 * (u * u) := (Nat.mul_assoc 88 4 _).symm
    have h968 : (88 * u) * 11 = 968 * u := by
      rw [Nat.mul_assoc, Nat.mul_comm u 11, ← Nat.mul_assoc]
    have h484 : 121 * (4 * u) = 484 * u := (Nat.mul_assoc 121 4 u).symm
    rw [h64, h176, h352, h968, h484]; omega
  rw [hl, hr]
  omega

/--
  Theorem W5.2b (`cousin_diamond2_phi_strict_descent`, zero custom axioms):
  Every integer `x > 2` strictly decreases the 2-term `(2, 3)`-adic valuation sum
  `Φ_diamond2(x) = v2Pow(x+1)*coprime23Core(x+1)^3 + v2Pow(x+1)^5*v3Pow(x+1)^3`
  in a single step of `T_diamond2` — across BOTH unbounded `(3/2)^K` Mersenne glides
  AND all three `v_2 ≥ 2` Syracuse jump cones (`17->13, 97->73, 73->55, ...`)!
-/
theorem cousin_diamond2_phi_strict_descent (x : Nat) (hx : x > 2) :
    cousinDiamond2Phi (cousinDiamond2Step x) < cousinDiamond2Phi x := by
  by_cases hodd : x % 2 = 1
  · by_cases hq : (x > 1 ∧ x % 16 = 1 ∧ x % 3 ≠ 2) ∨
        (x ≥ 73 ∧ x % 64 = 9 ∧ x % 3 ≠ 2) ∨
        (x ≥ 17 ∧ core3 (x + 1) = 2)
    · have hstep : cousinDiamond2Step x = (3 * x + 1) / 4 := by
        unfold cousinDiamond2Step; simp only [hodd, hq, ite_true]
      rw [hstep]
      let y := (3 * x + 1) / 4
      change cousinDiamond2Phi y < cousinDiamond2Phi x
      rcases hq with ⟨_, hm16, hnd3x⟩ | ⟨hx73, hm64, hnd3x⟩ | ⟨hx17, hc3_2⟩
      · -- Sub-cone 2a: `x % 16 = 1 ∧ x % 3 ≠ 2` (`x ≥ 17`)
        have hx17 : x ≥ 17 := by omega
        let g := (x + 1) / 2
        have hg_ge9 : g ≥ 9 := by dsimp [g]; omega
        have hxp1 : x + 1 = 2 * g := by dsimp [g]; omega
        have hg_odd : g % 2 = 1 := by dsimp [g]; omega
        have hg_nd3 : g % 3 ≠ 0 := by dsimp [g]; omega
        have hphix : cousinDiamond2Phi x = 2 * g ^ 3 + 32 := by
          unfold cousinDiamond2Phi
          rw [hxp1, v2Pow_mul2 g (by omega), v2Pow_of_odd g hg_odd,
              v3Pow_mul2 g (by omega), v3Pow_of_not_div3 g hg_nd3,
              coprime23Core_mul2 g (by omega), coprime23Core_of_coprime g hg_odd hg_nd3]
        let gy := (y + 1) / 2
        have h4y : 4 * (y + 1) = 3 * x + 5 := by dsimp [y]; omega
        have hyp1 : y + 1 = 2 * gy := by dsimp [gy]; omega
        have hgy_pos : gy ≥ 1 := by omega
        have hgy_odd : gy % 2 = 1 := by dsimp [gy]; omega
        have hgy_nd3 : gy % 3 ≠ 0 := by omega
        have hphiy : cousinDiamond2Phi y = 2 * gy ^ 3 + 32 := by
          unfold cousinDiamond2Phi
          rw [hyp1, v2Pow_mul2 gy hgy_pos, v2Pow_of_odd gy hgy_odd,
              v3Pow_mul2 gy hgy_pos, v3Pow_of_not_div3 gy hgy_nd3,
              coprime23Core_mul2 gy hgy_pos, coprime23Core_of_coprime gy hgy_odd hgy_nd3]
        have hgy_lt : gy < g := by omega
        have hcube := pow3_strict_mono_w5 gy g hgy_lt
        rw [hphiy, hphix]; omega
      · -- Sub-cone 2b: `x ≥ 73 ∧ x % 64 = 9 ∧ x % 3 ≠ 2`
        let g := (x + 1) / 2
        have hg_ge37 : g ≥ 37 := by dsimp [g]; omega
        have hxp1 : x + 1 = 2 * g := by dsimp [g]; omega
        have hg_odd : g % 2 = 1 := by dsimp [g]; omega
        have hg_nd3 : g % 3 ≠ 0 := by dsimp [g]; omega
        have hphix : cousinDiamond2Phi x = 2 * g ^ 3 + 32 := by
          unfold cousinDiamond2Phi
          rw [hxp1, v2Pow_mul2 g (by omega), v2Pow_of_odd g hg_odd,
              v3Pow_mul2 g (by omega), v3Pow_of_not_div3 g hg_nd3,
              coprime23Core_mul2 g (by omega), coprime23Core_of_coprime g hg_odd hg_nd3]
        have h4y : 4 * (y + 1) = 3 * x + 5 := by dsimp [y]; omega
        let gy := (y + 1) / 8
        have hyp1 : y + 1 = 2 * (2 * (2 * gy)) := by dsimp [gy]; omega
        have hgy_pos : gy ≥ 1 := by omega
        have hgy_odd : gy % 2 = 1 := by dsimp [gy]; omega
        have hgy_nd3 : gy % 3 ≠ 0 := by omega
        have hphiy : cousinDiamond2Phi y = 8 * gy ^ 3 + 32768 := by
          unfold cousinDiamond2Phi
          rw [hyp1,
              v2Pow_mul2 (2 * (2 * gy)) (by omega),
              v2Pow_mul2 (2 * gy) (by omega),
              v2Pow_mul2 gy hgy_pos, v2Pow_of_odd gy hgy_odd,
              v3Pow_mul2 (2 * (2 * gy)) (by omega),
              v3Pow_mul2 (2 * gy) (by omega),
              v3Pow_mul2 gy hgy_pos, v3Pow_of_not_div3 gy hgy_nd3,
              coprime23Core_mul2 (2 * (2 * gy)) (by omega),
              coprime23Core_mul2 (2 * gy) (by omega),
              coprime23Core_mul2 gy hgy_pos,
              coprime23Core_of_coprime gy hgy_odd hgy_nd3]
        have h16gy : 16 * gy = 3 * g + 1 := by omega
        apply nat_mul_lt_cancel_left 512 _ _ (by decide)
        rw [hphiy, hphix, Nat.mul_add, Nat.mul_add]
        have h4096 : 512 * (8 * gy ^ 3) = (16 * gy) ^ 3 := by
          rw [mul_pow_local 16 gy 3]
          have h16_3 : (16 : Nat) ^ 3 = 4096 := rfl
          rw [h16_3, ← Nat.mul_assoc 512 8]
        rw [h4096, h16gy, cube_3n_plus_1_w5 g]
        have hg3_ge : g ^ 3 ≥ 50653 := by
          have hm := nat_pow_mono_base 37 g hg_ge37 3
          have h37 : (37 : Nat) ^ 3 = 50653 := rfl
          rwa [h37] at hm
        have hg2_le : 27 * g ^ 2 < g ^ 3 := by
          rw [show (3 : Nat) = 2 + 1 from rfl, Nat.pow_succ g 2, Nat.mul_comm (g ^ 2) g]
          exact Nat.mul_lt_mul_of_pos_right (by omega : 27 < g)
            (nat_pow_pos_of_pos g (by omega) 2)
        have hg1_le : 9 * g < g ^ 3 := by
          have hg2_ge : g ^ 2 ≥ 1369 := by
            have hm := nat_pow_mono_base 37 g hg_ge37 2
            simpa using hm
          rw [show (3 : Nat) = 2 + 1 from rfl, Nat.pow_succ g 2]
          have hm := Nat.mul_le_mul_right g hg2_ge
          omega
        omega
      · -- Sub-cone 2c: `x ≥ 17 ∧ core3 (x + 1) = 2`
        rcases core3_decomp (x + 1) (by omega) with ⟨hb_pos, _, _, hb_m8, hb_mul⟩
        let b := v3Pow (x + 1)
        change b * core3 (x + 1) = x + 1 at hb_mul
        rw [hc3_2] at hb_mul
        have hb_ge9 : b ≥ 9 := by omega
        have hb_odd : b % 2 = 1 := by rcases hb_m8 with h1 | h3 <;> omega
        have hxp1 : x + 1 = 2 * b := by omega
        have hphix : cousinDiamond2Phi x = 2 + 32 * b ^ 3 := by
          unfold cousinDiamond2Phi
          have hg1 : coprime23Core (x + 1) = 1 := by
            unfold coprime23Core; rw [hc3_2]; decide
          have hv2_2 : v2Pow (x + 1) = 2 := by
            rw [hxp1, v2Pow_mul2 b (by omega), v2Pow_of_odd b hb_odd]
          rw [hv2_2, hg1]
        have h2y : 2 * (y + 1) = 3 * b + 1 := by dsimp [y]; omega
        have hyp1_nd3 : (y + 1) % 3 ≠ 0 := by omega
        have hb3_ge : b ^ 3 ≥ 729 := by
          have hm := nat_pow_mono_base 9 b hb_ge9 3
          simpa using hm
        have hb2_lt : 27 * b ^ 2 ≤ 3 * b ^ 3 := by
          have h1 : 3 * (9 * b ^ 2) ≤ 3 * (b * b ^ 2) :=
            Nat.mul_le_mul_left 3 (Nat.mul_le_mul_right (b ^ 2) hb_ge9)
          rw [← Nat.mul_assoc 3 9, show 3 * 9 = 27 from rfl,
              Nat.mul_comm b (b ^ 2), ← Nat.pow_succ b 2] at h1
          exact h1
        have hb1_lt : 9 * b ≤ b ^ 3 := by
          have hb2_ge : b ^ 2 ≥ 81 := by
            have hm := nat_pow_mono_base 9 b hb_ge9 2
            simpa using hm
          rw [show (3 : Nat) = 2 + 1 from rfl, Nat.pow_succ b 2]
          exact Nat.mul_le_mul_right b (by omega)
        rcases hb_m8 with hm1 | hm3
        · -- `b % 8 = 1` -> `y + 1 = 2 * gy` with `gy` odd (`4 * gy = 3 * b + 1`)
          let gy := (y + 1) / 2
          have hyp1 : y + 1 = 2 * gy := by dsimp [gy]; omega
          have hgy_pos : gy ≥ 1 := by omega
          have hgy_odd : gy % 2 = 1 := by dsimp [gy]; omega
          have hgy_nd3 : gy % 3 ≠ 0 := by omega
          have hphiy : cousinDiamond2Phi y = 2 * gy ^ 3 + 32 := by
            unfold cousinDiamond2Phi
            rw [hyp1, v2Pow_mul2 gy hgy_pos, v2Pow_of_odd gy hgy_odd,
                v3Pow_mul2 gy hgy_pos, v3Pow_of_not_div3 gy hgy_nd3,
                coprime23Core_mul2 gy hgy_pos, coprime23Core_of_coprime gy hgy_odd hgy_nd3]
          have h4gy : 4 * gy = 3 * b + 1 := by omega
          apply nat_mul_lt_cancel_left 32 _ _ (by decide)
          rw [hphiy, hphix, Nat.mul_add, Nat.mul_add]
          have h64 : 32 * (2 * gy ^ 3) = (4 * gy) ^ 3 := by
            rw [mul_pow_local 4 gy 3, ← Nat.mul_assoc 32 2]
          rw [h64, h4gy, cube_3n_plus_1_w5 b]
          omega
        · -- `b % 8 = 3` -> `y + 1 = gy` odd (`2 * gy = 3 * b + 1`)
          have hyp1_odd : (y + 1) % 2 = 1 := by omega
          have hphiy : cousinDiamond2Phi y = (y + 1) ^ 3 + 1 := by
            unfold cousinDiamond2Phi
            rw [v2Pow_of_odd (y + 1) hyp1_odd, v3Pow_of_not_div3 (y + 1) hyp1_nd3,
                coprime23Core_of_coprime (y + 1) hyp1_odd hyp1_nd3]
            simp
          apply nat_mul_lt_cancel_left 8 _ _ (by decide)
          rw [hphiy, hphix, Nat.mul_add, Nat.mul_add]
          have h8 : 8 * (y + 1) ^ 3 = (2 * (y + 1)) ^ 3 := (mul_pow_local 2 (y + 1) 3).symm
          rw [h8, h2y, cube_3n_plus_1_w5 b]
          omega
    · -- General odd step: `cousinDiamond2Step x = (3 * x + 1) / 2`
      have hstep : cousinDiamond2Step x = (3 * x + 1) / 2 := by
        unfold cousinDiamond2Step; simp only [hodd, hq, ite_true, ite_false]
      let m := (x + 1) / 2
      have hm_ge2 : m ≥ 2 := by dsimp [m]; omega
      have hxp1 : x + 1 = 2 * m := by dsimp [m]; omega
      have hyp1 : cousinDiamond2Step x + 1 = 3 * m := by rw [hstep]; dsimp [m]; omega
      unfold cousinDiamond2Phi
      rw [hyp1, hxp1,
          v2Pow_mul3 m (by omega), v3Pow_mul3 m (by omega), coprime23Core_mul3 m (by omega),
          v2Pow_mul2 m (by omega), v3Pow_mul2 m (by omega), coprime23Core_mul2 m (by omega),
          mul_pow_local 3 (v3Pow m) 3, mul_pow_local 2 (v2Pow m) 5]
      rcases decomp_2_3_exact m (by omega) with ⟨ha_pos, hb_pos, hg_pos, _, _, _⟩
      have hag_pos : v2Pow m * (coprime23Core m) ^ 3 ≥ 1 :=
        Nat.mul_le_mul ha_pos (nat_pow_pos_of_pos _ hg_pos 3)
      have hab_pos : (v2Pow m) ^ 5 * (v3Pow m) ^ 3 ≥ 1 :=
        Nat.mul_le_mul (nat_pow_pos_of_pos _ ha_pos 5) (nat_pow_pos_of_pos _ hb_pos 3)
      have ht1 : v2Pow m * (coprime23Core m) ^ 3 < (2 * v2Pow m) * (coprime23Core m) ^ 3 := by
        rw [Nat.mul_assoc 2]; omega
      have ht2 : (v2Pow m) ^ 5 * (3 ^ 3 * (v3Pow m) ^ 3) <
          (2 ^ 5 * (v2Pow m) ^ 5) * (v3Pow m) ^ 3 := by
        have hl : (v2Pow m) ^ 5 * (3 ^ 3 * (v3Pow m) ^ 3) =
            27 * ((v2Pow m) ^ 5 * (v3Pow m) ^ 3) := by
          have h27 : (3 : Nat) ^ 3 = 27 := rfl
          rw [h27, ← Nat.mul_assoc, Nat.mul_comm ((v2Pow m) ^ 5) 27, Nat.mul_assoc]
        have hr : (2 ^ 5 * (v2Pow m) ^ 5) * (v3Pow m) ^ 3 =
            32 * ((v2Pow m) ^ 5 * (v3Pow m) ^ 3) := by
          have h32 : (2 : Nat) ^ 5 = 32 := rfl
          rw [h32, Nat.mul_assoc]
        rw [hl, hr]; omega
      omega
  · -- Even branches: `x % 2 = 0` (`x + 1` is odd -> `v2Pow (x + 1) = 1`)
    have hev : x % 2 = 0 := by omega
    have hxp1_odd : (x + 1) % 2 = 1 := by omega
    by_cases h6 : x > 2 ∧ x % 6 = 2
    · -- Even drain `(x - 2) / 3`
      have hstep : cousinDiamond2Step x = (x - 2) / 3 := by
        unfold cousinDiamond2Step; simp only [hodd, h6, and_self, ite_true, ite_false]
      let m := (x + 1) / 3
      have hm_pos : m ≥ 3 := by dsimp [m]; omega
      have hm_odd : m % 2 = 1 := by dsimp [m]; omega
      have hxp1 : x + 1 = 3 * m := by dsimp [m]; omega
      have hyp1 : cousinDiamond2Step x + 1 = m := by rw [hstep]; dsimp [m]; omega
      unfold cousinDiamond2Phi
      rw [hyp1, hxp1,
          v2Pow_of_odd m hm_odd, v2Pow_mul3 m (by omega), v2Pow_of_odd m hm_odd,
          v3Pow_mul3 m (by omega), coprime23Core_mul3 m (by omega),
          mul_pow_local 3 (v3Pow m) 3]
      simp only [Nat.one_pow, Nat.one_mul]
      have hb3_pos : (v3Pow m) ^ 3 ≥ 1 :=
        nat_pow_pos_of_pos _ (decomp_2_3_exact m (by omega)).2.1 3
      have h27 : (3 : Nat) ^ 3 = 27 := rfl
      rw [h27]; omega
    · have hnd3_xp1 : (x + 1) % 3 ≠ 0 := by omega
      have hphix : cousinDiamond2Phi x = (x + 1) ^ 3 + 1 := by
        unfold cousinDiamond2Phi
        rw [v2Pow_of_odd (x + 1) hxp1_odd, v3Pow_of_not_div3 (x + 1) hnd3_xp1,
            coprime23Core_of_coprime (x + 1) hxp1_odd hnd3_xp1]
        simp
      by_cases h8 : x > 2 ∧ x % 8 = 6
      · -- Even drain `(x - 2) / 2` (`x = 8*q + 6` -> `y + 1` is odd!)
        have hstep : cousinDiamond2Step x = (x - 2) / 2 := by
          unfold cousinDiamond2Step
          have hn6 : ¬ (x % 6 = 2) := fun hc => h6 ⟨hx, hc⟩
          simp only [hodd, hx, hn6, h8.2, and_self, and_false, ite_true, ite_false]
        let y := (x - 2) / 2
        have hyp1_odd : (y + 1) % 2 = 1 := by dsimp [y]; omega
        have hyp1_pos : y + 1 ≥ 3 := by dsimp [y]; omega
        rcases decomp_2_3_exact (y + 1) (by omega) with ⟨_, hby_pos, hgy_pos, _, _, hy_mul⟩
        have hv2_y : v2Pow (y + 1) = 1 := v2Pow_of_odd (y + 1) hyp1_odd
        rw [hv2_y, Nat.one_mul] at hy_mul
        have hphiy_le : cousinDiamond2Phi y ≤ (y + 1) ^ 3 + 1 := by
          unfold cousinDiamond2Phi
          rw [hv2_y]
          simp only [Nat.one_pow, Nat.one_mul]
          have hsc := sum_cubes_le_prod_cube_succ (v3Pow (y + 1)) (coprime23Core (y + 1)) hby_pos hgy_pos
          rw [hy_mul] at hsc
          omega
        have hlt_y : y + 1 < x + 1 := by dsimp [y]; omega
        have hcube := pow3_strict_mono_w5 (y + 1) (x + 1) hlt_y
        rw [hstep, hphix]
        change cousinDiamond2Phi y < (x + 1) ^ 3 + 1
        omega
      · -- Standard halving `x / 2` (`x ≥ 4`, `x % 8 ∈ {0, 2, 4}`)
        have hstep : cousinDiamond2Step x = x / 2 := by
          unfold cousinDiamond2Step; simp only [hodd, h6, h8, ite_false]
        let y := x / 2
        by_cases hx4 : x % 4 = 0
        · -- `x % 4 = 0` -> `y + 1` is odd!
          have hyp1_odd : (y + 1) % 2 = 1 := by dsimp [y]; omega
          rcases decomp_2_3_exact (y + 1) (by dsimp [y]; omega) with
            ⟨_, hby_pos, hgy_pos, _, _, hy_mul⟩
          have hv2_y : v2Pow (y + 1) = 1 := v2Pow_of_odd (y + 1) hyp1_odd
          rw [hv2_y, Nat.one_mul] at hy_mul
          have hphiy_le : cousinDiamond2Phi y ≤ (y + 1) ^ 3 + 1 := by
            unfold cousinDiamond2Phi
            rw [hv2_y]
            simp only [Nat.one_pow, Nat.one_mul]
            have hsc := sum_cubes_le_prod_cube_succ (v3Pow (y + 1)) (coprime23Core (y + 1)) hby_pos hgy_pos
            rw [hy_mul] at hsc
            omega
          have hlt_y : y + 1 < x + 1 := by dsimp [y]; omega
          have hcube := pow3_strict_mono_w5 (y + 1) (x + 1) hlt_y
          rw [hstep, hphix]
          change cousinDiamond2Phi y < (x + 1) ^ 3 + 1
          omega
        · -- `x % 8 = 2` (`x ≥ 10`, `x = 4 * m - 2` with `m = (x + 2) / 4 ≥ 3`)
          have hx8_2 : x % 8 = 2 := by omega
          have hx_ge10 : x ≥ 10 := by omega
          let m := (x + 2) / 4
          have hm_ge3 : m ≥ 3 := by dsimp [m]; omega
          have hm_odd : m % 2 = 1 := by dsimp [m]; omega
          have hyp1 : y + 1 = 2 * m := by dsimp [y, m]; omega
          rcases decomp_2_3_exact m (by omega) with ⟨_, hbm_pos, hgm_pos, _, _, hm_mul⟩
          have hv2_m : v2Pow m = 1 := v2Pow_of_odd m hm_odd
          rw [hv2_m, Nat.one_mul] at hm_mul
          have hphiy_le : cousinDiamond2Phi y ≤ 32 * m ^ 3 + 32 := by
            unfold cousinDiamond2Phi
            rw [hyp1, v2Pow_mul2 m (by omega), hv2_m, Nat.mul_one,
                v3Pow_mul2 m (by omega), coprime23Core_mul2 m (by omega)]
            have h25 : (2 : Nat) ^ 5 = 32 := rfl
            rw [h25]
            have hsc := sum_cubes_le_prod_cube_succ (v3Pow m) (coprime23Core m) hbm_pos hgm_pos
            rw [hm_mul] at hsc
            have h32 := Nat.mul_le_mul_left 32 hsc
            rw [Nat.mul_add, Nat.mul_add, Nat.mul_one] at h32
            omega
          let k := m - 3
          have hm_eq : m = k + 3 := by dsimp [k]; omega
          have hxp1_eq : x + 1 = 4 * k + 11 := by dsimp [m, k] at hm_eq ⊢; omega
          have hpk := poly_bound_k3_4k11_w5 k
          rw [hm_eq] at hphiy_le
          rw [hstep, hphix, hxp1_eq]
          change cousinDiamond2Phi y < (4 * k + 11) ^ 3 + 1
          omega

theorem cousinDiamond2Phi_upper_poly_bound (x : Nat) :
    cousinDiamond2Phi x ≤ (x + 1) ^ 3 + (x + 1) ^ 5 := by
  rcases decomp_2_3_exact (x + 1) (by omega) with ⟨ha_pos, hb_pos, hg_pos, _, _, hmul⟩
  let a := v2Pow (x + 1)
  let b := v3Pow (x + 1)
  let g := coprime23Core (x + 1)
  change a * b * g = x + 1 at hmul
  have hag_le : a * g ≤ x + 1 := by
    have hm := Nat.mul_le_mul_right g (Nat.mul_le_mul_left a hb_pos)
    rwa [Nat.mul_one, hmul] at hm
  have hg_le : g ≤ x + 1 := by
    have hm := Nat.mul_le_mul_right g (Nat.mul_le_mul ha_pos hb_pos)
    rwa [Nat.mul_one, Nat.one_mul, hmul] at hm
  have hab_le : a * b ≤ x + 1 := by
    have hm := Nat.mul_le_mul_left (a * b) hg_pos
    rwa [Nat.mul_one, hmul] at hm
  have ht1 : a * g ^ 3 ≤ (x + 1) ^ 3 := by
    have hsplit : a * g ^ 3 = (a * g) * g ^ 2 := by
      rw [show (3 : Nat) = 2 + 1 from rfl, Nat.pow_succ, Nat.mul_comm (g ^ 2) g,
          ← Nat.mul_assoc a g (g ^ 2)]
    have hxp3 : (x + 1) ^ 3 = (x + 1) * (x + 1) ^ 2 := by
      rw [show (3 : Nat) = 2 + 1 from rfl, Nat.pow_succ, Nat.mul_comm]
    rw [hsplit, hxp3]
    exact Nat.mul_le_mul hag_le (nat_pow_mono_base g (x + 1) hg_le 2)
  have ht2 : a ^ 5 * b ^ 3 ≤ (x + 1) ^ 5 := by
    have hb35 : b ^ 3 ≤ b ^ 5 := by
      rw [show (5 : Nat) = 3 + 2 from rfl, Nat.pow_add]
      have hp2 := nat_pow_pos_of_pos b hb_pos 2
      have hm := Nat.mul_le_mul_left (b ^ 3) hp2
      simpa using hm
    have hab5 : a ^ 5 * b ^ 3 ≤ (a * b) ^ 5 := by
      rw [mul_pow_local a b 5]
      exact Nat.mul_le_mul_left (a ^ 5) hb35
    exact Nat.le_trans hab5 (nat_pow_mono_base (a * b) (x + 1) hab_le 5)
  unfold cousinDiamond2Phi
  exact Nat.add_le_add ht1 ht2

theorem cousin_diamond2_reaches_one_within_phi :
    ∀ (B x : Nat), x > 0 -> cousinDiamond2Phi x ≤ B ->
      ∃ k : Nat, k ≤ B ∧ cousinDiamond2Iter k x = 1
  | 0, x, _, hB => by
    rcases decomp_2_3_exact (x + 1) (by omega) with ⟨ha_pos, hb_pos, hg_pos, _, _, _⟩
    unfold cousinDiamond2Phi at hB
    have h1 : v2Pow (x + 1) * (coprime23Core (x + 1)) ^ 3 ≥ 1 :=
      Nat.mul_le_mul ha_pos (nat_pow_pos_of_pos _ hg_pos 3)
    omega
  | B + 1, x, hx, hB => by
    by_cases hx1 : x = 1
    · subst hx1; exact ⟨0, by omega, rfl⟩
    · by_cases hx2 : x = 2
      · subst hx2
        have hphi2 : cousinDiamond2Phi 2 = 28 := by decide
        rw [hphi2] at hB
        exact ⟨1, by omega, by decide⟩
      · have hx_gt2 : x > 2 := by omega
        have hdesc := cousin_diamond2_phi_strict_descent x hx_gt2
        have hpos := cousinDiamond2Step_pos x hx
        rcases cousin_diamond2_reaches_one_within_phi B (cousinDiamond2Step x) hpos (by omega) with
          ⟨k, hk_le, hk_eq⟩
        exact ⟨k + 1, by omega, hk_eq⟩

/--
  Theorem W5.2c (`cousin_diamond2_global_convergence`, zero custom axioms):
  Unconditional Global Convergence & Polynomial Stopping Bound for `T_diamond2` on `Z^+`:
  For EVERY `x > 0`, `cousinDiamond2Iter` reaches `1` within `k ≤ (x + 1)^3 + (x + 1)^5` steps!
-/
theorem cousin_diamond2_global_convergence (x : Nat) (hx : x > 0) :
    ∃ k : Nat, k ≤ (x + 1) ^ 3 + (x + 1) ^ 5 ∧ cousinDiamond2Iter k x = 1 := by
  rcases cousin_diamond2_reaches_one_within_phi (cousinDiamond2Phi x) x hx (Nat.le_refl _) with
    ⟨k, hk_phi, hk1⟩
  exact ⟨k, Nat.le_trans hk_phi (cousinDiamond2Phi_upper_poly_bound x), hk1⟩

theorem cousinDiamond2Step_mod4_eq_3 (z : Nat) (hz4 : z % 4 = 3) :
    cousinDiamond2Step z = (3 * z + 1) / 2 := by
  have hodd : z % 2 = 1 := by omega
  have hnq : ¬ ((z > 1 ∧ z % 16 = 1 ∧ z % 3 ≠ 2) ∨
      (z ≥ 73 ∧ z % 64 = 9 ∧ z % 3 ≠ 2) ∨
      (z ≥ 17 ∧ core3 (z + 1) = 2)) := by
    rintro (⟨_, h16, _⟩ | ⟨_, h64, _⟩ | ⟨_, hc3⟩)
    · omega
    · omega
    · rcases core3_decomp (z + 1) (by omega) with ⟨_, _, _, hm8, hmul⟩
      rw [hc3] at hmul
      rcases hm8 with h1 | h3 <;> omega
  unfold cousinDiamond2Step
  simp only [hodd, hnq, ite_true, ite_false]

theorem cousin_diamond2_mersenne_scaled :
    ∀ (k a q : Nat), k + 1 ≤ a -> q ≥ 1 ->
      cousinDiamond2Iter k (2 ^ a * q - 1) = 3 ^ k * 2 ^ (a - k) * q - 1
  | 0, _, _, _, _ => by simp [cousinDiamond2Iter]
  | k + 1, a, q, hka, hq => by
    have ha2 : a ≥ 2 := by omega
    have hp4 : 2 ^ a * q = 4 * (2 ^ (a - 2) * q) := by
      have hsp : a = (a - 2) + 2 := by omega
      conv => lhs; rw [hsp]
      rw [Nat.pow_add 2 (a - 2) 2, show (2 : Nat) ^ 2 = 4 from rfl, Nat.mul_comm (2 ^ (a - 2)) 4,
          Nat.mul_assoc]
    have hm_pos : 2 ^ (a - 2) * q ≥ 1 := Nat.mul_le_mul (pow2_pos_nat (a - 2)) hq
    have hz4 : (2 ^ a * q - 1) % 4 = 3 := by omega
    simp only [cousinDiamond2Iter]
    rw [cousinDiamond2Step_mod4_eq_3 (2 ^ a * q - 1) hz4]
    have hp2 : 2 ^ a * q = 2 * (2 ^ (a - 1) * q) := by
      rw [pow2_split_pred a (by omega), Nat.mul_assoc]
    have hstep_eq : (3 * (2 ^ a * q - 1) + 1) / 2 = 2 ^ (a - 1) * (3 * q) - 1 := by
      have hm2_pos : 2 ^ (a - 1) * q ≥ 1 := Nat.mul_le_mul (pow2_pos_nat (a - 1)) hq
      have hcomm : 3 * (2 ^ (a - 1) * q) = 2 ^ (a - 1) * (3 * q) := by
        rw [← Nat.mul_assoc 3, Nat.mul_comm 3 (2 ^ (a - 1)), Nat.mul_assoc]
      omega
    rw [hstep_eq, cousin_diamond2_mersenne_scaled k (a - 1) (3 * q) (by omega) (by omega)]
    have hexp : a - 1 - k = a - (k + 1) := by omega
    rw [hexp, Nat.pow_succ 3 k]
    have hmul : 3 ^ k * 2 ^ (a - (k + 1)) * (3 * q) = 3 ^ k * 3 * 2 ^ (a - (k + 1)) * q := by
      calc
        3 ^ k * 2 ^ (a - (k + 1)) * (3 * q)
            = 3 ^ k * (2 ^ (a - (k + 1)) * 3) * q := by
              rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
        _ = 3 ^ k * (3 * 2 ^ (a - (k + 1))) * q := by rw [Nat.mul_comm (2 ^ (a - (k + 1))) 3]
        _ = 3 ^ k * 3 * 2 ^ (a - (k + 1)) * q := by rw [← Nat.mul_assoc (3 ^ k) 3]
    rw [hmul]

/--
  Theorem W5.2d (`cousin_diamond2_unbounded_glide_and_mod_barrier`, zero custom axioms):
  `T_diamond2` preserves BOTH arbitrarily long `(3/2)^K` upward Mersenne glides (`∀ K ≥ 1`)
  AND the universal `∀ A, B ≥ 1` bounded-modulus `mod (2^A * 3^B)` monotone potential barrier!
-/
theorem cousin_diamond2_unbounded_glide_and_mod_barrier :
    (∀ K : Nat, K ≥ 1 ->
      cousinDiamond2Iter K (2 ^ (K + 1) - 1) = 3 ^ K * 2 - 1 ∧
      2 ^ (K + 1) - 1 < cousinDiamond2Iter K (2 ^ (K + 1) - 1)) ∧
    (∀ (A B : Nat), A ≥ 1 -> B ≥ 1 ->
      ∀ (Phi : Nat -> Nat -> Int),
        (∀ r a b : Nat, a < b -> Phi a r < Phi b r) ->
        let M := 2 ^ A * 3 ^ B
        let x0 := 2 * M - 1
        cousinDiamond2Step x0 % M = x0 % M ∧
        Phi x0 (x0 % M) < Phi (cousinDiamond2Step x0) (cousinDiamond2Step x0 % M)) := by
  refine ⟨?_, ?_⟩
  · intro K hK
    have hf := cousin_diamond2_mersenne_scaled K (K + 1) 1 (by omega) (by omega)
    simp only [Nat.mul_one, show K + 1 - K = 1 by omega, Nat.pow_one] at hf
    have hgt := pow3_gt_pow2_pos K hK
    have hsp : 2 ^ (K + 1) = 2 ^ K * 2 := Nat.pow_succ 2 K
    exact ⟨hf, by rw [hf, hsp]; omega⟩
  · intro A B hA hB Phi hmono
    dsimp only
    let M := 2 ^ A * 3 ^ B
    have hp2 : 2 ^ A = 2 * 2 ^ (A - 1) := pow2_split_pred A hA
    have hp3 : 3 ^ B ≥ 3 := by
      have hgt := pow3_gt_pow2_pos B hB
      have hp2B := pow2_pos_nat (B - 1)
      have hsp := pow2_split_pred B hB
      omega
    have hM_div2 : M = 2 * (2 ^ (A - 1) * 3 ^ B) := by
      dsimp [M]; rw [hp2, Nat.mul_assoc]
    have hpos_m : 2 ^ (A - 1) * 3 ^ B ≥ 3 :=
      Nat.mul_le_mul (pow2_pos_nat (A - 1)) hp3
    let x0 := 2 * M - 1
    have hx0_m4 : x0 % 4 = 3 := by dsimp [x0]; rw [hM_div2]; omega
    have htx0 : cousinDiamond2Step x0 = 3 * M - 1 := by
      rw [cousinDiamond2Step_mod4_eq_3 x0 hx0_m4]
      dsimp [x0]; omega
    have hM_ge6 : M ≥ 6 := by omega
    have hmod_x0 : x0 % M = M - 1 := by
      dsimp [x0]
      rw [show 2 * M - 1 = (M - 1) + M * 1 by omega, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (by omega)]
    have hmod_tx0 : cousinDiamond2Step x0 % M = M - 1 := by
      rw [htx0, show 3 * M - 1 = (M - 1) + M * 2 by omega, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (by omega)]
    have hres : cousinDiamond2Step x0 % M = x0 % M := by rw [hmod_tx0, hmod_x0]
    refine ⟨hres, ?_⟩
    rw [hres]
    exact hmono (x0 % M) x0 (cousinDiamond2Step x0) (by rw [htx0]; dsimp [x0]; omega)

theorem cousin_diamond2_four_witness_valuations :
    cousinDiamond2Step 7 = 11 ∧
    cousinDiamond2Step 17 = 13 ∧
    cousinDiamond2Step 73 = 55 ∧
    cousinDiamond2Step 97 = 73 ∧
    (v2Pow 56 = 8 ∧ v3Pow 56 = 1 ∧ coprime23Core 56 = 7) := by
  decide

/--
  Theorem W5.2e (`cousin_diamond2_single_laurent_monomial_impossibility`, zero custom axioms):
  Even though `T_diamond2` IS globally convergent on `Z^+` via the 2-term sum `Φ_diamond2`,
  EVERY single arbitrary-sign Laurent valuation monomial `(aPos, aNeg, bPos, bNeg, cPos, cNeg)`
  FAILS on the 4-witness set `{7, 17, 73, 97}` under `cousinDiamond2Step`!
  This proves a strict expressibility separation between 1-term and 2-term valuation invariants.
-/
theorem cousin_diamond2_single_laurent_monomial_impossibility
    (aPos aNeg bPos bNeg cPos cNeg : Nat) :
    ¬ (∀ x : Nat, (x = 7 ∨ x = 17 ∨ x = 73 ∨ x = 97) ->
        laurentValNum aPos bPos cPos (cousinDiamond2Step x) * laurentValDen aNeg bNeg cNeg x <
          laurentValNum aPos bPos cPos x * laurentValDen aNeg bNeg cNeg (cousinDiamond2Step x)) := by
  intro hdesc
  rcases syracuse_four_witness_valuations with
    ⟨_, _, _, _,
     ⟨hv2_8, hv3_8, hg_8⟩,
     ⟨hv2_12, hv3_12, hg_12⟩,
     _,
     ⟨hv2_18, hv3_18, hg_18⟩,
     ⟨hv2_14, hv3_14, hg_14⟩,
     ⟨hv2_98, hv3_98, hg_98⟩,
     ⟨hv2_74, hv3_74, hg_74⟩⟩
  rcases cousin_diamond2_four_witness_valuations with
    ⟨hs7, hs17, hs73, hs97, ⟨hv2_56, hv3_56, hg_56⟩⟩
  have h7 := hdesc 7 (Or.inl rfl)
  have h17 := hdesc 17 (Or.inr (Or.inl rfl))
  have h73 := hdesc 73 (Or.inr (Or.inr (Or.inl rfl)))
  have h97 := hdesc 97 (Or.inr (Or.inr (Or.inr rfl)))
  unfold laurentValNum laurentValDen at h7 h17 h73 h97
  rw [hs7] at h7; rw [hs17] at h17; rw [hs73] at h73; rw [hs97] at h97
  simp only [show 7 + 1 = 8 from rfl, show 11 + 1 = 12 from rfl,
             show 17 + 1 = 18 from rfl, show 13 + 1 = 14 from rfl,
             show 73 + 1 = 74 from rfl, show 55 + 1 = 56 from rfl,
             show 97 + 1 = 98 from rfl,
             hv2_8, hv3_8, hg_8, hv2_12, hv3_12, hg_12,
             hv2_18, hv3_18, hg_18, hv2_14, hv3_14, hg_14,
             hv2_74, hv3_74, hg_74, hv2_56, hv3_56, hg_56,
             hv2_98, hv3_98, hg_98,
             Nat.one_pow, Nat.mul_one] at h7 h17 h73 h97
  -- 1. `7 -> 11`: `9^bPos * 4^aNeg < 4^aPos * 9^bNeg`
  rw [mul_pow_local 4 2 aPos, mul_pow_local 4 2 aNeg] at h7
  have h1_base : 3 ^ bPos * 2 ^ aNeg < 2 ^ aPos * 3 ^ bNeg := by
    apply nat_mul_lt_cancel_left (4 ^ aPos * 4 ^ aNeg) _ _
      (Nat.mul_le_mul (nat_pow_pos_of_pos 4 (by decide) aPos) (nat_pow_pos_of_pos 4 (by decide) aNeg))
    have hl : (4 ^ aPos * 4 ^ aNeg) * (3 ^ bPos * 2 ^ aNeg) =
        (4 ^ aPos * 3 ^ bPos) * (4 ^ aNeg * 2 ^ aNeg) := by
      calc
        (4 ^ aPos * 4 ^ aNeg) * (3 ^ bPos * 2 ^ aNeg)
            = 4 ^ aPos * (4 ^ aNeg * (3 ^ bPos * 2 ^ aNeg)) := Nat.mul_assoc _ _ _
        _ = 4 ^ aPos * ((3 ^ bPos * 4 ^ aNeg) * 2 ^ aNeg) := by
              rw [← Nat.mul_assoc (4 ^ aNeg), Nat.mul_comm (4 ^ aNeg) (3 ^ bPos)]
        _ = (4 ^ aPos * 3 ^ bPos) * (4 ^ aNeg * 2 ^ aNeg) := by
              rw [Nat.mul_assoc (3 ^ bPos), ← Nat.mul_assoc (4 ^ aPos)]
    have hr : (4 ^ aPos * 4 ^ aNeg) * (2 ^ aPos * 3 ^ bNeg) =
        (4 ^ aPos * 2 ^ aPos) * (4 ^ aNeg * 3 ^ bNeg) := by
      calc
        (4 ^ aPos * 4 ^ aNeg) * (2 ^ aPos * 3 ^ bNeg)
            = 4 ^ aPos * (4 ^ aNeg * (2 ^ aPos * 3 ^ bNeg)) := Nat.mul_assoc _ _ _
        _ = 4 ^ aPos * ((2 ^ aPos * 4 ^ aNeg) * 3 ^ bNeg) := by
              rw [← Nat.mul_assoc (4 ^ aNeg), Nat.mul_comm (4 ^ aNeg) (2 ^ aPos)]
        _ = (4 ^ aPos * 2 ^ aPos) * (4 ^ aNeg * 3 ^ bNeg) := by
              rw [Nat.mul_assoc (2 ^ aPos), ← Nat.mul_assoc (4 ^ aPos)]
    rw [hl, hr]; exact h7
  have h1_sq : 9 ^ bPos * 4 ^ aNeg < 4 ^ aPos * 9 ^ bNeg := by
    have hsq := nat_mul_lt_mul_pos _ _ _ _ h1_base h1_base
    have hl : (3 ^ bPos * 2 ^ aNeg) * (3 ^ bPos * 2 ^ aNeg) = 9 ^ bPos * 4 ^ aNeg := by
      rw [show (9 : Nat) = 3 * 3 from rfl, show (4 : Nat) = 2 * 2 from rfl,
          mul_pow_local 3 3, mul_pow_local 2 2]
      calc
        (3 ^ bPos * 2 ^ aNeg) * (3 ^ bPos * 2 ^ aNeg)
            = 3 ^ bPos * (2 ^ aNeg * (3 ^ bPos * 2 ^ aNeg)) := Nat.mul_assoc _ _ _
        _ = 3 ^ bPos * ((3 ^ bPos * 2 ^ aNeg) * 2 ^ aNeg) := by
              rw [← Nat.mul_assoc (2 ^ aNeg), Nat.mul_comm (2 ^ aNeg) (3 ^ bPos)]
        _ = (3 ^ bPos * 3 ^ bPos) * (2 ^ aNeg * 2 ^ aNeg) := by
              rw [Nat.mul_assoc (3 ^ bPos), ← Nat.mul_assoc (3 ^ bPos)]
    have hr : (2 ^ aPos * 3 ^ bNeg) * (2 ^ aPos * 3 ^ bNeg) = 4 ^ aPos * 9 ^ bNeg := by
      rw [show (9 : Nat) = 3 * 3 from rfl, show (4 : Nat) = 2 * 2 from rfl,
          mul_pow_local 3 3, mul_pow_local 2 2]
      calc
        (2 ^ aPos * 3 ^ bNeg) * (2 ^ aPos * 3 ^ bNeg)
            = 2 ^ aPos * (3 ^ bNeg * (2 ^ aPos * 3 ^ bNeg)) := Nat.mul_assoc _ _ _
        _ = 2 ^ aPos * ((2 ^ aPos * 3 ^ bNeg) * 3 ^ bNeg) := by
              rw [← Nat.mul_assoc (3 ^ bNeg), Nat.mul_comm (3 ^ bNeg) (2 ^ aPos)]
        _ = (2 ^ aPos * 2 ^ aPos) * (3 ^ bNeg * 3 ^ bNeg) := by
              rw [Nat.mul_assoc (2 ^ aPos), ← Nat.mul_assoc (2 ^ aPos)]
    rwa [hl, hr] at hsq
  -- 2. `17 -> 13`: `7^cPos * 9^bNeg < 9^bPos * 7^cNeg`
  have h17_ineq : 7 ^ cPos * 9 ^ bNeg < 9 ^ bPos * 7 ^ cNeg := by
    apply nat_mul_lt_cancel_left (2 ^ aPos * 2 ^ aNeg) _ _
      (Nat.mul_le_mul (pow2_pos_nat aPos) (pow2_pos_nat aNeg))
    have hl : (2 ^ aPos * 2 ^ aNeg) * (7 ^ cPos * 9 ^ bNeg) =
        (2 ^ aPos * 7 ^ cPos) * (2 ^ aNeg * 9 ^ bNeg) := by
      calc
        (2 ^ aPos * 2 ^ aNeg) * (7 ^ cPos * 9 ^ bNeg)
            = 2 ^ aPos * (2 ^ aNeg * (7 ^ cPos * 9 ^ bNeg)) := Nat.mul_assoc _ _ _
        _ = 2 ^ aPos * ((7 ^ cPos * 2 ^ aNeg) * 9 ^ bNeg) := by
              rw [← Nat.mul_assoc (2 ^ aNeg), Nat.mul_comm (2 ^ aNeg) (7 ^ cPos)]
        _ = (2 ^ aPos * 7 ^ cPos) * (2 ^ aNeg * 9 ^ bNeg) := by
              rw [Nat.mul_assoc (7 ^ cPos), ← Nat.mul_assoc (2 ^ aPos)]
    have hr : (2 ^ aPos * 2 ^ aNeg) * (9 ^ bPos * 7 ^ cNeg) =
        (2 ^ aPos * 9 ^ bPos) * (2 ^ aNeg * 7 ^ cNeg) := by
      calc
        (2 ^ aPos * 2 ^ aNeg) * (9 ^ bPos * 7 ^ cNeg)
            = 2 ^ aPos * (2 ^ aNeg * (9 ^ bPos * 7 ^ cNeg)) := Nat.mul_assoc _ _ _
        _ = 2 ^ aPos * ((9 ^ bPos * 2 ^ aNeg) * 7 ^ cNeg) := by
              rw [← Nat.mul_assoc (2 ^ aNeg), Nat.mul_comm (2 ^ aNeg) (9 ^ bPos)]
        _ = (2 ^ aPos * 9 ^ bPos) * (2 ^ aNeg * 7 ^ cNeg) := by
              rw [Nat.mul_assoc (9 ^ bPos), ← Nat.mul_assoc (2 ^ aPos)]
    rw [hl, hr]; exact h17
  -- 3. `73 -> 55`: `(4^aPos * 7^cPos) * 37^cNeg < 37^cPos * (4^aNeg * 7^cNeg)`
  rw [mul_pow_local 2 4 aPos, mul_pow_local 2 4 aNeg] at h73
  have h73_ineq : (4 ^ aPos * 7 ^ cPos) * 37 ^ cNeg < 37 ^ cPos * (4 ^ aNeg * 7 ^ cNeg) := by
    apply nat_mul_lt_cancel_left (2 ^ aPos * 2 ^ aNeg) _ _
      (Nat.mul_le_mul (pow2_pos_nat aPos) (pow2_pos_nat aNeg))
    have hl : (2 ^ aPos * 2 ^ aNeg) * ((4 ^ aPos * 7 ^ cPos) * 37 ^ cNeg) =
        (2 ^ aPos * 4 ^ aPos * 7 ^ cPos) * (2 ^ aNeg * 37 ^ cNeg) := by
      calc
        (2 ^ aPos * 2 ^ aNeg) * ((4 ^ aPos * 7 ^ cPos) * 37 ^ cNeg)
            = 2 ^ aPos * (2 ^ aNeg * ((4 ^ aPos * 7 ^ cPos) * 37 ^ cNeg)) := Nat.mul_assoc _ _ _
        _ = 2 ^ aPos * (((4 ^ aPos * 7 ^ cPos) * 2 ^ aNeg) * 37 ^ cNeg) := by
              rw [← Nat.mul_assoc (2 ^ aNeg), Nat.mul_comm (2 ^ aNeg) (4 ^ aPos * 7 ^ cPos)]
        _ = (2 ^ aPos * 4 ^ aPos * 7 ^ cPos) * (2 ^ aNeg * 37 ^ cNeg) := by
              rw [Nat.mul_assoc (4 ^ aPos * 7 ^ cPos), ← Nat.mul_assoc (2 ^ aPos),
                  ← Nat.mul_assoc (2 ^ aPos) (4 ^ aPos) (7 ^ cPos)]
    have hr : (2 ^ aPos * 2 ^ aNeg) * (37 ^ cPos * (4 ^ aNeg * 7 ^ cNeg)) =
        (2 ^ aPos * 37 ^ cPos) * (2 ^ aNeg * 4 ^ aNeg * 7 ^ cNeg) := by
      calc
        (2 ^ aPos * 2 ^ aNeg) * (37 ^ cPos * (4 ^ aNeg * 7 ^ cNeg))
            = 2 ^ aPos * (2 ^ aNeg * (37 ^ cPos * (4 ^ aNeg * 7 ^ cNeg))) := Nat.mul_assoc _ _ _
        _ = 2 ^ aPos * ((37 ^ cPos * 2 ^ aNeg) * (4 ^ aNeg * 7 ^ cNeg)) := by
              rw [← Nat.mul_assoc (2 ^ aNeg), Nat.mul_comm (2 ^ aNeg) (37 ^ cPos)]
        _ = (2 ^ aPos * 37 ^ cPos) * (2 ^ aNeg * 4 ^ aNeg * 7 ^ cNeg) := by
              rw [Nat.mul_assoc (37 ^ cPos), ← Nat.mul_assoc (2 ^ aPos),
                  Nat.mul_assoc (2 ^ aNeg) (4 ^ aNeg) (7 ^ cNeg)]
    rw [hl, hr]; exact h73
  -- 4. `97 -> 73`: `37^cPos * 49^cNeg < 49^cPos * 37^cNeg`
  have h97_ineq : 37 ^ cPos * 49 ^ cNeg < 49 ^ cPos * 37 ^ cNeg := by
    apply nat_mul_lt_cancel_left (2 ^ aPos * 2 ^ aNeg) _ _
      (Nat.mul_le_mul (pow2_pos_nat aPos) (pow2_pos_nat aNeg))
    have hl : (2 ^ aPos * 2 ^ aNeg) * (37 ^ cPos * 49 ^ cNeg) =
        (2 ^ aPos * 37 ^ cPos) * (2 ^ aNeg * 49 ^ cNeg) := by
      calc
        (2 ^ aPos * 2 ^ aNeg) * (37 ^ cPos * 49 ^ cNeg)
            = 2 ^ aPos * (2 ^ aNeg * (37 ^ cPos * 49 ^ cNeg)) := Nat.mul_assoc _ _ _
        _ = 2 ^ aPos * ((37 ^ cPos * 2 ^ aNeg) * 49 ^ cNeg) := by
              rw [← Nat.mul_assoc (2 ^ aNeg), Nat.mul_comm (2 ^ aNeg) (37 ^ cPos)]
        _ = (2 ^ aPos * 37 ^ cPos) * (2 ^ aNeg * 49 ^ cNeg) := by
              rw [Nat.mul_assoc (37 ^ cPos), ← Nat.mul_assoc (2 ^ aPos)]
    have hr : (2 ^ aPos * 2 ^ aNeg) * (49 ^ cPos * 37 ^ cNeg) =
        (2 ^ aPos * 49 ^ cPos) * (2 ^ aNeg * 37 ^ cNeg) := by
      calc
        (2 ^ aPos * 2 ^ aNeg) * (49 ^ cPos * 37 ^ cNeg)
            = 2 ^ aPos * (2 ^ aNeg * (49 ^ cPos * 37 ^ cNeg)) := Nat.mul_assoc _ _ _
        _ = 2 ^ aPos * ((49 ^ cPos * 2 ^ aNeg) * 37 ^ cNeg) := by
              rw [← Nat.mul_assoc (2 ^ aNeg), Nat.mul_comm (2 ^ aNeg) (49 ^ cPos)]
        _ = (2 ^ aPos * 49 ^ cPos) * (2 ^ aNeg * 37 ^ cNeg) := by
              rw [Nat.mul_assoc (49 ^ cPos), ← Nat.mul_assoc (2 ^ aPos)]
    rw [hl, hr]; exact h97
  -- Chain `h17_ineq` & `h1_sq` -> `7^cPos * 4^aNeg < 4^aPos * 7^cNeg`:
  have h7_4 : 7 ^ cPos * 4 ^ aNeg < 4 ^ aPos * 7 ^ cNeg := by
    have hp := nat_mul_lt_mul_pos _ _ _ _ h17_ineq h1_sq
    apply nat_mul_lt_cancel_left (9 ^ bPos * 9 ^ bNeg) _ _
      (Nat.mul_le_mul (nat_pow_pos_of_pos 9 (by decide) bPos) (nat_pow_pos_of_pos 9 (by decide) bNeg))
    have hl : (9 ^ bPos * 9 ^ bNeg) * (7 ^ cPos * 4 ^ aNeg) =
        (7 ^ cPos * 9 ^ bNeg) * (9 ^ bPos * 4 ^ aNeg) := by
      calc
        (9 ^ bPos * 9 ^ bNeg) * (7 ^ cPos * 4 ^ aNeg)
            = (9 ^ bNeg * 9 ^ bPos) * (7 ^ cPos * 4 ^ aNeg) := by rw [Nat.mul_comm (9 ^ bPos)]
        _ = 9 ^ bNeg * (9 ^ bPos * (7 ^ cPos * 4 ^ aNeg)) := Nat.mul_assoc _ _ _
        _ = 9 ^ bNeg * (7 ^ cPos * (9 ^ bPos * 4 ^ aNeg)) := by
              rw [← Nat.mul_assoc (9 ^ bPos), Nat.mul_comm (9 ^ bPos) (7 ^ cPos), Nat.mul_assoc (7 ^ cPos)]
        _ = (7 ^ cPos * 9 ^ bNeg) * (9 ^ bPos * 4 ^ aNeg) := by
              rw [← Nat.mul_assoc (9 ^ bNeg), Nat.mul_comm (9 ^ bNeg) (7 ^ cPos)]
    have hr : (9 ^ bPos * 9 ^ bNeg) * (4 ^ aPos * 7 ^ cNeg) =
        (9 ^ bPos * 7 ^ cNeg) * (4 ^ aPos * 9 ^ bNeg) := by
      calc
        (9 ^ bPos * 9 ^ bNeg) * (4 ^ aPos * 7 ^ cNeg)
            = 9 ^ bPos * (9 ^ bNeg * (4 ^ aPos * 7 ^ cNeg)) := Nat.mul_assoc _ _ _
        _ = 9 ^ bPos * ((4 ^ aPos * 9 ^ bNeg) * 7 ^ cNeg) := by
              rw [← Nat.mul_assoc (9 ^ bNeg), Nat.mul_comm (9 ^ bNeg) (4 ^ aPos)]
        _ = 9 ^ bPos * (7 ^ cNeg * (4 ^ aPos * 9 ^ bNeg)) := by rw [Nat.mul_comm _ (7 ^ cNeg)]
        _ = (9 ^ bPos * 7 ^ cNeg) * (4 ^ aPos * 9 ^ bNeg) := (Nat.mul_assoc _ _ _).symm
    rw [hl, hr]; exact hp
  -- Chain `h7_4` & `h73_ineq` -> `49^cPos * 37^cNeg < 37^cPos * 49^cNeg`, contradicting `h97_ineq`:
  have h49_37 : 49 ^ cPos * 37 ^ cNeg < 37 ^ cPos * 49 ^ cNeg := by
    have hp := nat_mul_lt_mul_pos _ _ _ _ h7_4 h73_ineq
    apply nat_mul_lt_cancel_left (4 ^ aPos * 4 ^ aNeg) _ _
      (Nat.mul_le_mul (nat_pow_pos_of_pos 4 (by decide) aPos) (nat_pow_pos_of_pos 4 (by decide) aNeg))
    have h49p : 49 ^ cPos = 7 ^ cPos * 7 ^ cPos := mul_pow_local 7 7 cPos
    have h49n : 49 ^ cNeg = 7 ^ cNeg * 7 ^ cNeg := mul_pow_local 7 7 cNeg
    have hl : (4 ^ aPos * 4 ^ aNeg) * (49 ^ cPos * 37 ^ cNeg) =
        (7 ^ cPos * 4 ^ aNeg) * ((4 ^ aPos * 7 ^ cPos) * 37 ^ cNeg) := by
      rw [h49p]
      calc
        (4 ^ aPos * 4 ^ aNeg) * ((7 ^ cPos * 7 ^ cPos) * 37 ^ cNeg)
            = (4 ^ aNeg * 4 ^ aPos) * (7 ^ cPos * (7 ^ cPos * 37 ^ cNeg)) := by
              rw [Nat.mul_comm (4 ^ aPos), Nat.mul_assoc (7 ^ cPos)]
        _ = 4 ^ aNeg * (4 ^ aPos * (7 ^ cPos * (7 ^ cPos * 37 ^ cNeg))) := Nat.mul_assoc _ _ _
        _ = 4 ^ aNeg * (7 ^ cPos * ((4 ^ aPos * 7 ^ cPos) * 37 ^ cNeg)) := by
              have hmid : 4 ^ aPos * (7 ^ cPos * (7 ^ cPos * 37 ^ cNeg)) =
                  7 ^ cPos * ((4 ^ aPos * 7 ^ cPos) * 37 ^ cNeg) := by
                calc
                  4 ^ aPos * (7 ^ cPos * (7 ^ cPos * 37 ^ cNeg))
                      = (4 ^ aPos * 7 ^ cPos) * (7 ^ cPos * 37 ^ cNeg) := (Nat.mul_assoc _ _ _).symm
                  _ = (7 ^ cPos * 4 ^ aPos) * (7 ^ cPos * 37 ^ cNeg) := by rw [Nat.mul_comm (4 ^ aPos)]
                  _ = 7 ^ cPos * (4 ^ aPos * (7 ^ cPos * 37 ^ cNeg)) := Nat.mul_assoc _ _ _
                  _ = 7 ^ cPos * ((4 ^ aPos * 7 ^ cPos) * 37 ^ cNeg) := by rw [Nat.mul_assoc (4 ^ aPos)]
              rw [hmid]
        _ = (7 ^ cPos * 4 ^ aNeg) * ((4 ^ aPos * 7 ^ cPos) * 37 ^ cNeg) := by
              rw [← Nat.mul_assoc (4 ^ aNeg), Nat.mul_comm (4 ^ aNeg) (7 ^ cPos)]
    have hr : (4 ^ aPos * 4 ^ aNeg) * (37 ^ cPos * 49 ^ cNeg) =
        (4 ^ aPos * 7 ^ cNeg) * (37 ^ cPos * (4 ^ aNeg * 7 ^ cNeg)) := by
      rw [h49n]
      calc
        (4 ^ aPos * 4 ^ aNeg) * (37 ^ cPos * (7 ^ cNeg * 7 ^ cNeg))
            = 4 ^ aPos * (4 ^ aNeg * (37 ^ cPos * (7 ^ cNeg * 7 ^ cNeg))) := Nat.mul_assoc _ _ _
        _ = 4 ^ aPos * (7 ^ cNeg * (37 ^ cPos * (4 ^ aNeg * 7 ^ cNeg))) := by
              have hmid : 4 ^ aNeg * (37 ^ cPos * (7 ^ cNeg * 7 ^ cNeg)) =
                  7 ^ cNeg * (37 ^ cPos * (4 ^ aNeg * 7 ^ cNeg)) := by
                calc
                  4 ^ aNeg * (37 ^ cPos * (7 ^ cNeg * 7 ^ cNeg))
                      = (37 ^ cPos * 4 ^ aNeg) * (7 ^ cNeg * 7 ^ cNeg) := by
                        rw [← Nat.mul_assoc, Nat.mul_comm (4 ^ aNeg) (37 ^ cPos)]
                  _ = 37 ^ cPos * ((4 ^ aNeg * 7 ^ cNeg) * 7 ^ cNeg) := by
                        rw [Nat.mul_assoc, ← Nat.mul_assoc (4 ^ aNeg)]
                  _ = 37 ^ cPos * (7 ^ cNeg * (4 ^ aNeg * 7 ^ cNeg)) := by
                        rw [Nat.mul_comm (4 ^ aNeg * 7 ^ cNeg) (7 ^ cNeg)]
                  _ = 7 ^ cNeg * (37 ^ cPos * (4 ^ aNeg * 7 ^ cNeg)) := by
                        rw [← Nat.mul_assoc, Nat.mul_comm (37 ^ cPos) (7 ^ cNeg), Nat.mul_assoc]
              rw [hmid]
        _ = (4 ^ aPos * 7 ^ cNeg) * (37 ^ cPos * (4 ^ aNeg * 7 ^ cNeg)) := (Nat.mul_assoc _ _ _).symm
    rw [hl, hr]; exact hp
  omega

/--
  Theorem W5.2f (`cousin_diamond2_counter_model_separation`, `[]` axioms):
  `T_diamond2` rejects ALL three Counter-Models (`M1 = Q_(6)^+` 5-cycle
  `(1, 7) -> (5, 7) -> (11, 7) -> (20, 7) -> (2, 7) -> (1, 7)` via `cousinDiamond2IterQ6`,
  `M2 = Z^-` cycles `-1` and `-5 -> -7 -> -10 -> -5`, and `M3` supercritical `q = 7`
  5-cycle `5 -> 18 -> 9 -> 32 -> 10 -> 5`), verifies exact `Nat`/`Int`/`Q_(6)` agreement
  at the odd-power-of-3 Syracuse jump `x = 53 -> 40`, AND defeats Wave 4's 1-term `Φ_diamond`
  at `17 -> 13` (`Φ_diamond 13 = 2744 > 72 = Φ_diamond 17`) while `Φ_diamond2 13 = 718 < 23330 = Φ_diamond2 17`!
-/
theorem cousin_diamond2_counter_model_separation :
    cousinDiamond2StepInt (-1) = -1 ∧
    cousinDiamond2IterInt 3 (-5) = -5 ∧
    cousinDiamond2IterParam 7 5 5 = 5 ∧
    (∀ k : Fin 32, ((2 * k.val + 1) * invMod64Odd (2 * k.val + 1)) % 64 = 1) ∧
    cousinDiamond2StepQ6 (1, 7) = (5, 7) ∧
    cousinDiamond2IterQ6 5 (1, 7) = (1, 7) ∧
    cousinDiamond2Step 53 = 40 ∧
    cousinDiamond2StepInt 53 = 40 ∧
    cousinDiamond2StepQ6 (53, 1) = (40, 1) ∧
    cousinDiamond2Step 17 = 13 ∧
    cousinDiamondPhi 17 = 72 ∧
    cousinDiamondPhi 13 = 2744 ∧
    cousinDiamond2Phi 17 = 23330 ∧
    cousinDiamond2Phi 13 = 718 := by
  decide

-- ============================================================================
-- SECTION 2C: Front B — Universal All-Length (`∀ L ≥ 1`) Multi-Term Laurent
--             Valuation Impossibility on True `(3x+1)` & Reciprocal Corollary
-- ============================================================================

/--
  Theorem W5.2g (`two_term_valuation_sum_survives_w4_witnesses_yet_fails_syracuse`, `[]` axioms):
  A 2-term positive valuation sum `Ψ₂(x) = 5 * v3Pow(x+1) + 3 * v2Pow(x+1) * coprime23Core(x+1)`
  STRICTLY DECREASES on ALL FOUR Wave 4 antagonism witnesses `{7, 9, 17, 97}`, yet FAILS
  on true `(3x+1)` at the minimal witness `x = 3 -> 5` (`Ψ₂(3) = 17 < 21 = Ψ₂(5)`)!
-/
theorem two_term_valuation_sum_survives_w4_witnesses_yet_fails_syracuse :
    let psi2 := fun x : Nat => 5 * v3Pow (x + 1) + 3 * v2Pow (x + 1) * coprime23Core (x + 1)
    (∀ x : Nat, (x = 7 ∨ x = 9 ∨ x = 17 ∨ x = 97) -> psi2 (syracuseOddStep x) < psi2 x) ∧
    syracuseOddStep 3 = 5 ∧
    psi2 3 = 17 ∧
    psi2 5 = 21 ∧
    psi2 3 < psi2 5 := by
  dsimp only
  refine ⟨?_, by decide, by decide, by decide, by decide⟩
  rintro x (rfl | rfl | rfl | rfl) <;> decide

structure LaurentTerm where
  coeff : Nat
  aExp  : Nat
  bExp  : Nat
  cExp  : Nat
  deriving DecidableEq, Repr

def evalLaurentSumNum : List LaurentTerm -> Nat -> Nat
  | [], _ => 0
  | t :: rest, x =>
    t.coeff * laurentValNum t.aExp t.bExp t.cExp x + evalLaurentSumNum rest x

def sumLaurentCoeffs : List LaurentTerm -> Nat
  | [] => 0
  | t :: rest => t.coeff + sumLaurentCoeffs rest

def maxActiveA : List LaurentTerm -> Nat
  | [] => 0
  | t :: rest => if t.coeff > 0 then Nat.max t.aExp (maxActiveA rest) else maxActiveA rest

def maxActiveB : List LaurentTerm -> Nat
  | [] => 0
  | t :: rest => if t.coeff > 0 then Nat.max t.bExp (maxActiveB rest) else maxActiveB rest

def maxActiveC : List LaurentTerm -> Nat
  | [] => 0
  | t :: rest => if t.coeff > 0 then Nat.max t.cExp (maxActiveC rest) else maxActiveC rest

theorem active_exps_le_max :
    ∀ (terms : List LaurentTerm) (t : LaurentTerm),
      t ∈ terms -> t.coeff > 0 ->
      t.aExp ≤ maxActiveA terms ∧ t.bExp ≤ maxActiveB terms ∧ t.cExp ≤ maxActiveC terms
  | [], _, hmem, _ => by cases hmem
  | hd :: rest, t, hmem, hpos => by
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hrest
    · simp only [maxActiveA, maxActiveB, maxActiveC, hpos, ite_true]
      exact ⟨Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _⟩
    · rcases active_exps_le_max rest t hrest hpos with ⟨ha, hb, hc⟩
      simp only [maxActiveA, maxActiveB, maxActiveC]
      by_cases hhd : hd.coeff > 0
      · simp only [hhd, ite_true]
        exact ⟨Nat.le_trans ha (Nat.le_max_right _ _),
               Nat.le_trans hb (Nat.le_max_right _ _),
               Nat.le_trans hc (Nat.le_max_right _ _)⟩
      · simp only [hhd, ite_false]
        exact ⟨ha, hb, hc⟩

theorem exists_active_achieving_max :
    ∀ (terms : List LaurentTerm),
      (∃ t ∈ terms, t.coeff > 0) ->
      (∃ tA ∈ terms, tA.coeff > 0 ∧ tA.aExp = maxActiveA terms) ∧
      (∃ tB ∈ terms, tB.coeff > 0 ∧ tB.bExp = maxActiveB terms) ∧
      (∃ tC ∈ terms, tC.coeff > 0 ∧ tC.cExp = maxActiveC terms)
  | [], ⟨_, hmem, _⟩ => by cases hmem
  | hd :: rest, hex => by
    by_cases hrest_ex : ∃ t ∈ rest, t.coeff > 0
    · rcases exists_active_achieving_max rest hrest_ex with
        ⟨⟨tA, hmA, hpA, heA⟩, ⟨tB, hmB, hpB, heB⟩, ⟨tC, hmC, hpC, heC⟩⟩
      simp only [maxActiveA, maxActiveB, maxActiveC]
      if hhd : hd.coeff > 0 then
        simp only [hhd, ite_true]
        refine ⟨?_, ?_, ?_⟩
        · by_cases hge : maxActiveA rest ≤ hd.aExp
          · exact ⟨hd, List.Mem.head _, hhd, (Nat.max_eq_left hge).symm⟩
          · exact ⟨tA, List.mem_cons_of_mem _ hmA, hpA, heA.trans (Nat.max_eq_right (by omega)).symm⟩
        · by_cases hge : maxActiveB rest ≤ hd.bExp
          · exact ⟨hd, List.Mem.head _, hhd, (Nat.max_eq_left hge).symm⟩
          · exact ⟨tB, List.mem_cons_of_mem _ hmB, hpB, heB.trans (Nat.max_eq_right (by omega)).symm⟩
        · by_cases hge : maxActiveC rest ≤ hd.cExp
          · exact ⟨hd, List.Mem.head _, hhd, (Nat.max_eq_left hge).symm⟩
          · exact ⟨tC, List.mem_cons_of_mem _ hmC, hpC, heC.trans (Nat.max_eq_right (by omega)).symm⟩
      else
        simp only [hhd, ite_false]
        exact ⟨⟨tA, List.mem_cons_of_mem _ hmA, hpA, heA⟩,
               ⟨tB, List.mem_cons_of_mem _ hmB, hpB, heB⟩,
               ⟨tC, List.mem_cons_of_mem _ hmC, hpC, heC⟩⟩
    · rcases hex with ⟨t0, hmem0, hp0⟩
      simp only [List.mem_cons] at hmem0
      rcases hmem0 with rfl | hr0
      · have hzero : ∀ (r : List LaurentTerm), (¬ ∃ t ∈ r, t.coeff > 0) ->
            maxActiveA r = 0 ∧ maxActiveB r = 0 ∧ maxActiveC r = 0 := by
          intro r hnr
          induction r with
          | nil => exact ⟨rfl, rfl, rfl⟩
          | cons u ur ih =>
            have hu0 : ¬ (u.coeff > 0) := fun hp => hnr ⟨u, List.Mem.head _, hp⟩
            have hnur : ¬ (∃ t ∈ ur, t.coeff > 0) :=
              fun ⟨t, hm, hp⟩ => hnr ⟨t, List.mem_cons_of_mem _ hm, hp⟩
            simp only [maxActiveA, maxActiveB, maxActiveC, hu0, ite_false]
            exact ih hnur
        rcases hzero rest hrest_ex with ⟨ha0, hb0, hc0⟩
        simp only [maxActiveA, maxActiveB, maxActiveC, hp0, ite_true, ha0, hb0, hc0, Nat.max_zero]
        exact ⟨⟨t0, List.Mem.head _, hp0, rfl⟩,
               ⟨t0, List.Mem.head _, hp0, rfl⟩,
               ⟨t0, List.Mem.head _, hp0, rfl⟩⟩
      · exact False.elim (hrest_ex ⟨t0, hr0, hp0⟩)

theorem evalLaurentSumNum_ge_active_term :
    ∀ (terms : List LaurentTerm) (t : LaurentTerm) (x : Nat),
      t ∈ terms -> t.coeff > 0 ->
      laurentValNum t.aExp t.bExp t.cExp x ≤ evalLaurentSumNum terms x
  | [], _, _, hmem, _ => by cases hmem
  | hd :: rest, t, x, hmem, hpos => by
    simp only [List.mem_cons] at hmem
    simp only [evalLaurentSumNum]
    rcases hmem with rfl | hrest
    · have hm : 1 * laurentValNum t.aExp t.bExp t.cExp x ≤
          t.coeff * laurentValNum t.aExp t.bExp t.cExp x :=
        Nat.mul_le_mul_right _ hpos
      rw [Nat.one_mul] at hm
      omega
    · have ih := evalLaurentSumNum_ge_active_term rest t x hrest hpos
      omega

theorem evalLaurentSumNum_le_sumCoeffs_mul :
    ∀ (terms : List LaurentTerm) (x M : Nat),
      (∀ t ∈ terms, t.coeff > 0 -> laurentValNum t.aExp t.bExp t.cExp x ≤ M) ->
      evalLaurentSumNum terms x ≤ sumLaurentCoeffs terms * M
  | [], _, _, _ => by simp [evalLaurentSumNum, sumLaurentCoeffs]
  | hd :: rest, x, M, hbdd => by
    simp only [evalLaurentSumNum, sumLaurentCoeffs, Nat.add_mul]
    have ih := evalLaurentSumNum_le_sumCoeffs_mul rest x M
      (fun t hm hp => hbdd t (List.mem_cons_of_mem _ hm) hp)
    by_cases hhd : hd.coeff > 0
    · have h1 := Nat.mul_le_mul_left hd.coeff (hbdd hd (List.Mem.head _) hhd)
      exact Nat.add_le_add h1 ih
    · have hc0 : hd.coeff = 0 := by omega
      rw [hc0]
      simp only [Nat.zero_mul, Nat.zero_add]
      exact ih

theorem pow9_mod8_eq_one_w5 : ∀ k : Nat, 9 ^ k % 8 = 1
  | 0 => rfl
  | k + 1 => by rw [Nat.pow_succ, Nat.mul_mod, pow9_mod8_eq_one_w5 k]

theorem pow9_eq_v3Pow_w5 : ∀ k : Nat, v3Pow (9 ^ k) = 9 ^ k ∧ core3 (9 ^ k) = 1
  | 0 => ⟨by decide, by decide⟩
  | k + 1 => by
    rcases pow9_eq_v3Pow_w5 k with ⟨hv, hc⟩
    have hp_pos : 9 ^ k > 0 := nat_pow_pos_of_pos 9 (by decide) k
    have h9 : 9 ^ (k + 1) = 3 * (3 * 9 ^ k) := by rw [Nat.pow_succ]; omega
    rw [h9, v3Pow_mul3 (3 * 9 ^ k) (by omega), v3Pow_mul3 (9 ^ k) hp_pos, hv,
        core3_mul3 (3 * 9 ^ k) (by omega), core3_mul3 (9 ^ k) hp_pos, hc]
    exact ⟨rfl, rfl⟩

theorem pow3_eq_v3Pow_w5 : ∀ k : Nat, v3Pow (3 ^ k) = 3 ^ k ∧ core3 (3 ^ k) = 1
  | 0 => ⟨by decide, by decide⟩
  | k + 1 => by
    rcases pow3_eq_v3Pow_w5 k with ⟨hv, hc⟩
    have hp_pos : 3 ^ k > 0 := pow3_pos_nat k
    have h3 : 3 ^ (k + 1) = 3 * 3 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [h3, v3Pow_mul3 (3 ^ k) hp_pos, hv, core3_mul3 (3 ^ k) hp_pos, hc]
    exact ⟨rfl, rfl⟩

theorem pow2_eq_v2Pow_w5 : ∀ k : Nat, v2Pow (2 ^ k) = 2 ^ k ∧ v3Pow (2 ^ k) = 1 ∧ coprime23Core (2 ^ k) = 1
  | 0 => ⟨by decide, by decide, by decide⟩
  | k + 1 => by
    rcases pow2_eq_v2Pow_w5 k with ⟨hv2, hv3, hg⟩
    have hp_pos : 2 ^ k > 0 := pow2_pos_nat k
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [h2, v2Pow_mul2 (2 ^ k) hp_pos, hv2,
        v3Pow_mul2 (2 ^ k) hp_pos, hv3,
        coprime23Core_mul2 (2 ^ k) hp_pos, hg]
    exact ⟨rfl, rfl, rfl⟩

theorem pow_pow_eq_mul_w5 (b m : Nat) : ∀ n : Nat, (b ^ m) ^ n = b ^ (m * n)
  | 0 => by simp
  | n + 1 => by
    rw [Nat.pow_succ (b ^ m) n, pow_pow_eq_mul_w5 b m n, ← Nat.pow_add,
        Nat.mul_add, Nat.mul_one]

/--
  Theorem W5.2h (`syracuse_multiterm_laurent_valuation_impossibility`, zero custom axioms):
  Universal All-Length (`∀ L ≥ 1`) Multi-Term `(2, 3)`-Adic Laurent Valuation Impossibility:
  For EVERY finite list `terms : List LaurentTerm` containing at least one positive coefficient
  (`∃ t ∈ terms, t.coeff > 0`) and EVERY denominator shift `(A0 B0 C0 : Nat)`, there exists an
  explicit odd integer `x ≥ 3` (`x % 2 = 1`, `syracuseOddStep x ≥ 3`) on which strict
  cleared-denominator Syracuse descent FAILS!
-/
theorem syracuse_multiterm_laurent_valuation_impossibility
    (terms : List LaurentTerm) (A0 B0 C0 : Nat)
    (hnonempty : ∃ t ∈ terms, t.coeff > 0) :
    ∃ x : Nat,
      x ≥ 3 ∧ x % 2 = 1 ∧ syracuseOddStep x ≥ 3 ∧
      ¬ (evalLaurentSumNum terms (syracuseOddStep x) * laurentValDen A0 B0 C0 x <
          evalLaurentSumNum terms x * laurentValDen A0 B0 C0 (syracuseOddStep x)) := by
  let aMax := maxActiveA terms
  let bMax := maxActiveB terms
  let cMax := maxActiveC terms
  rcases exists_active_achieving_max terms hnonempty with
    ⟨⟨tA, hmA, hpA, heA⟩, ⟨tB, hmB, hpB, heB⟩, ⟨tC, hmC, hpC, heC⟩⟩
  change tA.aExp = aMax at heA
  change tB.bExp = bMax at heB
  change tC.cExp = cMax at heC
  -- Constructive witness 1: `x1 = 97 -> 73`
  if h97_desc : evalLaurentSumNum terms (syracuseOddStep 97) * laurentValDen A0 B0 C0 97 <
      evalLaurentSumNum terms 97 * laurentValDen A0 B0 C0 (syracuseOddStep 97) then
    have hC0_lt_cMax : C0 < cMax := by
      if hlt : C0 < cMax then exact hlt
      else
        exfalso
        have h97 := h97_desc
        rcases syracuse_four_witness_valuations with
          ⟨_, _, _, hs97, _, _, _, _, _, ⟨hv2_98, hv3_98, hg_98⟩, ⟨hv2_74, hv3_74, hg_74⟩⟩
        rw [hs97] at h97
        have hterm_ge : ∀ (ts : List LaurentTerm),
            (∀ t ∈ ts, t.coeff > 0 -> t.cExp ≤ C0) ->
            evalLaurentSumNum ts 97 * laurentValDen A0 B0 C0 73 ≤
              evalLaurentSumNum ts 73 * laurentValDen A0 B0 C0 97 := by
          intro ts hts
          induction ts with
          | nil => simp [evalLaurentSumNum]
          | cons hd rest ih =>
            simp only [evalLaurentSumNum, Nat.add_mul]
            have ih_r := ih (fun t hm hp => hts t (List.mem_cons_of_mem _ hm) hp)
            if hhd : hd.coeff > 0 then
              have hc_le : hd.cExp ≤ C0 := hts hd (List.Mem.head _) hhd
              let d := C0 - hd.cExp
              have hd_eq : C0 = hd.cExp + d := by dsimp [d]; omega
              have hval97 : laurentValNum hd.aExp hd.bExp hd.cExp 97 * laurentValDen A0 B0 C0 73 =
                  (2 ^ hd.aExp * 2 ^ A0) * (49 ^ hd.cExp * 37 ^ C0) := by
                unfold laurentValNum laurentValDen
                simp only [show 97 + 1 = 98 from rfl, show 73 + 1 = 74 from rfl,
                           hv2_98, hv3_98, hg_98, hv2_74, hv3_74, hg_74,
                           Nat.one_pow, Nat.mul_one]
                calc
                  (2 ^ hd.aExp * 49 ^ hd.cExp) * (2 ^ A0 * 37 ^ C0)
                      = 2 ^ hd.aExp * (49 ^ hd.cExp * (2 ^ A0 * 37 ^ C0)) := Nat.mul_assoc _ _ _
                  _ = 2 ^ hd.aExp * ((2 ^ A0 * 49 ^ hd.cExp) * 37 ^ C0) := by
                        rw [← Nat.mul_assoc (49 ^ hd.cExp), Nat.mul_comm (49 ^ hd.cExp) (2 ^ A0)]
                  _ = (2 ^ hd.aExp * 2 ^ A0) * (49 ^ hd.cExp * 37 ^ C0) := by
                        rw [Nat.mul_assoc (2 ^ A0), ← Nat.mul_assoc (2 ^ hd.aExp)]
              have hval73 : laurentValNum hd.aExp hd.bExp hd.cExp 73 * laurentValDen A0 B0 C0 97 =
                  (2 ^ hd.aExp * 2 ^ A0) * (37 ^ hd.cExp * 49 ^ C0) := by
                unfold laurentValNum laurentValDen
                simp only [show 97 + 1 = 98 from rfl, show 73 + 1 = 74 from rfl,
                           hv2_98, hv3_98, hg_98, hv2_74, hv3_74, hg_74,
                           Nat.one_pow, Nat.mul_one]
                calc
                  (2 ^ hd.aExp * 37 ^ hd.cExp) * (2 ^ A0 * 49 ^ C0)
                      = 2 ^ hd.aExp * (37 ^ hd.cExp * (2 ^ A0 * 49 ^ C0)) := Nat.mul_assoc _ _ _
                  _ = 2 ^ hd.aExp * ((2 ^ A0 * 37 ^ hd.cExp) * 49 ^ C0) := by
                        rw [← Nat.mul_assoc (37 ^ hd.cExp), Nat.mul_comm (37 ^ hd.cExp) (2 ^ A0)]
                  _ = (2 ^ hd.aExp * 2 ^ A0) * (37 ^ hd.cExp * 49 ^ C0) := by
                        rw [Nat.mul_assoc (2 ^ A0), ← Nat.mul_assoc (2 ^ hd.aExp)]
              have hc_ineq : 49 ^ hd.cExp * 37 ^ C0 ≤ 37 ^ hd.cExp * 49 ^ C0 := by
                rw [hd_eq, Nat.pow_add 37 hd.cExp d, Nat.pow_add 49 hd.cExp d]
                have hd37 : 37 ^ d ≤ 49 ^ d := nat_pow_mono_base 37 49 (by decide) d
                have hc1 : 49 ^ hd.cExp * (37 ^ hd.cExp * 37 ^ d) =
                    (37 ^ hd.cExp * 49 ^ hd.cExp) * 37 ^ d := by
                  rw [← Nat.mul_assoc, Nat.mul_comm (49 ^ hd.cExp) (37 ^ hd.cExp)]
                have hc2 : 37 ^ hd.cExp * (49 ^ hd.cExp * 49 ^ d) =
                    (37 ^ hd.cExp * 49 ^ hd.cExp) * 49 ^ d := (Nat.mul_assoc _ _ _).symm
                rw [hc1, hc2]
                exact Nat.mul_le_mul_left _ hd37
              have hhd_le : hd.coeff * laurentValNum hd.aExp hd.bExp hd.cExp 97 *
                  laurentValDen A0 B0 C0 73 ≤
                  hd.coeff * laurentValNum hd.aExp hd.bExp hd.cExp 73 *
                    laurentValDen A0 B0 C0 97 := by
                rw [Nat.mul_assoc hd.coeff, Nat.mul_assoc hd.coeff, hval97, hval73]
                exact Nat.mul_le_mul_left hd.coeff (Nat.mul_le_mul_left _ hc_ineq)
              exact Nat.add_le_add hhd_le ih_r
            else
              have hc0 : hd.coeff = 0 := by omega
              simp only [hc0, Nat.zero_mul, Nat.zero_add]
              exact ih_r
        have hge_all := hterm_ge terms (fun t hm hp =>
          Nat.le_trans (active_exps_le_max terms t hm hp).2.2 (by omega))
        omega
    -- Constructive witness 2: `xk2 = 2 * 9^k2 - 1`
    let dc := cMax - C0
    let k2 := 4 ^ dc * (sumLaurentCoeffs terms * 2 ^ aMax * 2 ^ A0) + 1
    have hp9_ge9 : 9 ^ k2 ≥ 9 := by
      have hk2_pos : k2 ≥ 1 := by dsimp [k2]; omega
      rw [show k2 = (k2 - 1) + 1 by omega, Nat.pow_succ]
      have hp0 := nat_pow_pos_of_pos 9 (by decide) (k2 - 1); omega
    have hp9_m8 : 9 ^ k2 % 8 = 1 := pow9_mod8_eq_one_w5 k2
    let xk2 := 2 * 9 ^ k2 - 1
    let yk2 := (3 * 9 ^ k2 - 1) / 2
    have hxk2_ge3 : xk2 ≥ 3 := by dsimp [xk2]; omega
    have hxk2_odd : xk2 % 2 = 1 := by dsimp [xk2]; omega
    have hyk2_odd : yk2 % 2 = 1 := by dsimp [yk2]; omega
    have hyk2_ge3 : yk2 ≥ 3 := by dsimp [yk2]; omega
    have hsyr_xk2 : syracuseOddStep xk2 = yk2 := by
      unfold syracuseOddStep
      have h3x1 : 3 * xk2 + 1 = 2 * (2 * yk2) := by dsimp [xk2, yk2]; omega
      rw [h3x1, core2_mul2 (2 * yk2) (by omega), core2_mul2 yk2 (by omega), core2_of_odd yk2 hyk2_odd]
    if hxk2_desc : evalLaurentSumNum terms (syracuseOddStep xk2) * laurentValDen A0 B0 C0 xk2 <
        evalLaurentSumNum terms xk2 * laurentValDen A0 B0 C0 (syracuseOddStep xk2) then
      have hcB_le_bC : cMax + B0 ≤ bMax + C0 := by
        if hle : cMax + B0 ≤ bMax + C0 then exact hle
        else
          exfalso
          have hdc_pos : dc ≥ 1 := by dsimp [dc]; omega
          have hcMax_eq : cMax = C0 + dc := by dsimp [dc]; omega
          let gk := (3 * 9 ^ k2 + 1) / 4
          have hdesc_k := hxk2_desc
          rw [hsyr_xk2] at hdesc_k
          have hxkp1 : xk2 + 1 = 2 * 9 ^ k2 := by dsimp [xk2]; omega
          rcases pow9_eq_v3Pow_w5 k2 with ⟨hv3_9k, hc3_9k⟩
          have hv2_xk : v2Pow (xk2 + 1) = 2 := by
            rw [hxkp1, v2Pow_mul2 (9 ^ k2) (by omega), v2Pow_of_odd (9 ^ k2) (by omega)]
          have hv3_xk : v3Pow (xk2 + 1) = 9 ^ k2 := by
            rw [hxkp1, v3Pow_mul2 (9 ^ k2) (by omega), hv3_9k]
          have hg_xk : coprime23Core (xk2 + 1) = 1 := by
            rw [hxkp1, coprime23Core_mul2 (9 ^ k2) (by omega)]
            unfold coprime23Core; rw [hc3_9k]; decide
          have hykp1 : yk2 + 1 = 2 * gk := by dsimp [yk2, gk]; omega
          have hgk_pos : gk ≥ 7 := by dsimp [gk]; omega
          have hgk_odd : gk % 2 = 1 := by dsimp [gk]; omega
          have hgk_nd3 : gk % 3 ≠ 0 := by dsimp [gk]; omega
          have hv2_yk : v2Pow (yk2 + 1) = 2 := by
            rw [hykp1, v2Pow_mul2 gk (by omega), v2Pow_of_odd gk hgk_odd]
          have hv3_yk : v3Pow (yk2 + 1) = 1 := by
            rw [hykp1, v3Pow_mul2 gk (by omega), v3Pow_of_not_div3 gk hgk_nd3]
          have hg_yk : coprime23Core (yk2 + 1) = gk := by
            rw [hykp1, coprime23Core_mul2 gk (by omega), coprime23Core_of_coprime gk hgk_odd hgk_nd3]
          have hlhs_ge : gk ^ cMax * 9 ^ (k2 * B0) ≤
              evalLaurentSumNum terms yk2 * laurentValDen A0 B0 C0 xk2 := by
            have htC_ge := evalLaurentSumNum_ge_active_term terms tC yk2 hmC hpC
            unfold laurentValNum at htC_ge
            rw [hv2_yk, hv3_yk, hg_yk, heC, Nat.one_pow, Nat.mul_one] at htC_ge
            have hnum_ge : gk ^ cMax ≤ evalLaurentSumNum terms yk2 := by
              have hp2 := pow2_pos_nat tC.aExp
              have hm := Nat.mul_le_mul_right (gk ^ cMax) hp2
              rw [Nat.one_mul] at hm; exact Nat.le_trans hm htC_ge
            have hden_ge : 9 ^ (k2 * B0) ≤ laurentValDen A0 B0 C0 xk2 := by
              unfold laurentValDen
              rw [hv2_xk, hv3_xk, hg_xk, Nat.one_pow, Nat.mul_one, pow_pow_eq_mul_w5 9 k2 B0]
              have hm := Nat.mul_le_mul_right (9 ^ (k2 * B0)) (pow2_pos_nat A0)
              simpa using hm
            exact Nat.mul_le_mul hnum_ge hden_ge
          have hrhs_le : evalLaurentSumNum terms xk2 * laurentValDen A0 B0 C0 yk2 ≤
              (sumLaurentCoeffs terms * 2 ^ aMax * 2 ^ A0) * 9 ^ (k2 * bMax) * gk ^ C0 := by
            have hnum_le : evalLaurentSumNum terms xk2 ≤
                sumLaurentCoeffs terms * (2 ^ aMax * 9 ^ (k2 * bMax)) := by
              apply evalLaurentSumNum_le_sumCoeffs_mul
              intro t hm hp
              rcases active_exps_le_max terms t hm hp with ⟨ha_le, hb_le, _⟩
              unfold laurentValNum
              rw [hv2_xk, hv3_xk, hg_xk, Nat.one_pow, Nat.mul_one, pow_pow_eq_mul_w5 9 k2 t.bExp]
              exact Nat.mul_le_mul (pow2_mono_nat ha_le)
                (by
                  have hexp_le : k2 * t.bExp ≤ k2 * bMax := Nat.mul_le_mul_left k2 hb_le
                  have hdiff : k2 * bMax = k2 * t.bExp + (k2 * bMax - k2 * t.bExp) := by omega
                  rw [hdiff, Nat.pow_add]
                  have hm9 := Nat.mul_le_mul_left (9 ^ (k2 * t.bExp))
                    (nat_pow_pos_of_pos 9 (by decide) (k2 * bMax - k2 * t.bExp))
                  simpa using hm9)
            have hden_eq : laurentValDen A0 B0 C0 yk2 = 2 ^ A0 * gk ^ C0 := by
              unfold laurentValDen
              rw [hv2_yk, hv3_yk, hg_yk, Nat.one_pow, Nat.mul_one]
            rw [hden_eq]
            have hm := Nat.mul_le_mul_right (2 ^ A0 * gk ^ C0) hnum_le
            have hrw : (sumLaurentCoeffs terms * (2 ^ aMax * 9 ^ (k2 * bMax))) * (2 ^ A0 * gk ^ C0) =
                (sumLaurentCoeffs terms * 2 ^ aMax * 2 ^ A0) * 9 ^ (k2 * bMax) * gk ^ C0 := by
              calc
                (sumLaurentCoeffs terms * (2 ^ aMax * 9 ^ (k2 * bMax))) * (2 ^ A0 * gk ^ C0)
                    = (sumLaurentCoeffs terms * 2 ^ aMax) * (9 ^ (k2 * bMax) * (2 ^ A0 * gk ^ C0)) := by
                      rw [← Nat.mul_assoc (sumLaurentCoeffs terms) (2 ^ aMax), Nat.mul_assoc]
                _ = (sumLaurentCoeffs terms * 2 ^ aMax) * ((2 ^ A0 * 9 ^ (k2 * bMax)) * gk ^ C0) := by
                      rw [← Nat.mul_assoc (9 ^ (k2 * bMax)), Nat.mul_comm (9 ^ (k2 * bMax)) (2 ^ A0)]
                _ = (sumLaurentCoeffs terms * 2 ^ aMax * 2 ^ A0) * 9 ^ (k2 * bMax) * gk ^ C0 := by
                      rw [← Nat.mul_assoc, ← Nat.mul_assoc]
            rwa [hrw] at hm
          have hcomb : gk ^ cMax * 9 ^ (k2 * B0) <
              (sumLaurentCoeffs terms * 2 ^ aMax * 2 ^ A0) * 9 ^ (k2 * bMax) * gk ^ C0 :=
            Nat.lt_of_le_of_lt hlhs_ge (Nat.lt_of_lt_of_le hdesc_k hrhs_le)
          rw [hcMax_eq, Nat.pow_add gk C0 dc] at hcomb
          have hgkC0_pos : gk ^ C0 > 0 := nat_pow_pos_of_pos gk (by omega) C0
          have hcanc_gk : gk ^ dc * 9 ^ (k2 * B0) <
              (sumLaurentCoeffs terms * 2 ^ aMax * 2 ^ A0) * 9 ^ (k2 * bMax) := by
            apply nat_mul_lt_cancel_right_w5 (gk ^ C0) _ _ hgkC0_pos
            have hl : (gk ^ dc * 9 ^ (k2 * B0)) * gk ^ C0 = (gk ^ C0 * gk ^ dc) * 9 ^ (k2 * B0) := by
              rw [Nat.mul_assoc, Nat.mul_comm (9 ^ (k2 * B0)), ← Nat.mul_assoc, Nat.mul_comm (gk ^ dc)]
            rwa [hl]
          have h4gk : 9 ^ k2 ≤ 4 * gk := by dsimp [gk]; omega
          have h4dc_pos : 4 ^ dc > 0 := nat_pow_pos_of_pos 4 (by decide) dc
          have hm4 := Nat.mul_lt_mul_of_pos_left hcanc_gk h4dc_pos
          have hpow_gk : 9 ^ (k2 * dc) ≤ 4 ^ dc * gk ^ dc := by
            rw [← pow_pow_eq_mul_w5 9 k2 dc, ← mul_pow_local 4 gk dc]
            exact nat_pow_mono_base (9 ^ k2) (4 * gk) h4gk dc
          have hexp_ge : k2 * bMax + k2 ≤ k2 * dc + k2 * B0 := by
            have hd_gt : bMax + 1 ≤ dc + B0 := by dsimp [dc]; omega
            have hm := Nat.mul_le_mul_left k2 hd_gt
            rw [Nat.mul_add, Nat.mul_one, Nat.mul_add] at hm; exact hm
          have hp9_split : 9 ^ k2 * 9 ^ (k2 * bMax) ≤ 9 ^ (k2 * dc) * 9 ^ (k2 * B0) := by
            rw [← Nat.pow_add 9 (k2 * dc) (k2 * B0)]
            have hdiff : k2 * dc + k2 * B0 =
                (k2 + k2 * bMax) + (k2 * dc + k2 * B0 - (k2 + k2 * bMax)) := by omega
            rw [hdiff, Nat.pow_add 9 (k2 + k2 * bMax), Nat.pow_add 9 k2 (k2 * bMax)]
            have hm9 := Nat.mul_le_mul_left (9 ^ k2 * 9 ^ (k2 * bMax))
              (nat_pow_pos_of_pos 9 (by decide) (k2 * dc + k2 * B0 - (k2 + k2 * bMax)))
            simpa using hm9
          have hlhs_chain : 9 ^ k2 * 9 ^ (k2 * bMax) <
              (4 ^ dc * (sumLaurentCoeffs terms * 2 ^ aMax * 2 ^ A0)) * 9 ^ (k2 * bMax) := by
            have h1 : 9 ^ (k2 * dc) * 9 ^ (k2 * B0) ≤ 4 ^ dc * (gk ^ dc * 9 ^ (k2 * B0)) := by
              rw [← Nat.mul_assoc (4 ^ dc)]
              exact Nat.mul_le_mul_right _ hpow_gk
            rw [Nat.mul_assoc (4 ^ dc)]
            exact Nat.lt_of_le_of_lt (Nat.le_trans hp9_split h1) hm4
          have hcanc9 := nat_mul_lt_cancel_right_w5 (9 ^ (k2 * bMax)) _ _
            (nat_pow_pos_of_pos 9 (by decide) _) hlhs_chain
          have hp9_gt_k : 9 ^ k2 ≥ k2 + 1 :=
            Nat.le_trans (pow2_ge_succ_self k2) (nat_pow_mono_base 2 9 (by decide) k2)
          dsimp [k2] at hcanc9 hp9_gt_k
          omega
      have hB0_lt_bMax : B0 < bMax := by omega
      -- Constructive witness 3: `xj3 = 2 * geomSpineEntry j3 - 1`
      let j3 := sumLaurentCoeffs terms * 2 ^ aMax * 2 ^ (8 * cMax + 7 * A0) + 1
      let zj := geomSpineEntry j3
      rcases geomSpineEntry_valuations_constant j3 with ⟨h3zj1, hzj_ge, hv2_zj, hv3_zj, _, _⟩
      change 3 * zj + 1 = 4 ^ (3 * j3 + 4) at h3zj1
      change zj ≥ 85 at hzj_ge
      have h4_pow2 : ∀ m : Nat, 4 ^ m = 2 ^ (2 * m) := by
        intro m; induction m with
        | zero => rfl
        | succ m' ih =>
          rw [Nat.pow_succ, ih, show 2 * (m' + 1) = 2 * m' + 2 by omega, Nat.pow_add]
      have h3zj1_pow2 : 3 * zj + 1 = 2 ^ (6 * j3 + 8) := by
        rw [h3zj1, h4_pow2 (3 * j3 + 4), show 2 * (3 * j3 + 4) = 6 * j3 + 8 by omega]
      let xj3 := 2 * zj - 1
      let yj3 := 2 ^ (6 * j3 + 7) - 1
      have hp2_6j7 : 2 ^ (6 * j3 + 7) ≥ 128 := by
        rw [Nat.pow_add 2 (6 * j3) 7]
        have hm := Nat.mul_le_mul_right (2 ^ 7) (pow2_pos_nat (6 * j3))
        simpa using hm
      have hxj3_ge3 : xj3 ≥ 3 := by dsimp [xj3]; omega
      have hxj3_odd : xj3 % 2 = 1 := by dsimp [xj3]; omega
      have hyj3_odd : yj3 % 2 = 1 := by
        dsimp [yj3]
        rw [show 6 * j3 + 7 = (6 * j3 + 6) + 1 by omega, Nat.pow_succ]
        have hp0 := pow2_pos_nat (6 * j3 + 6); omega
      have hyj3_ge3 : yj3 ≥ 3 := by dsimp [yj3]; omega
      have hsyr_xj3 : syracuseOddStep xj3 = yj3 := by
        unfold syracuseOddStep
        have h3xj : 3 * xj3 + 1 = 2 * (2 * yj3) := by
          dsimp [xj3, yj3]
          have hsp : 2 ^ (6 * j3 + 8) = 2 * 2 ^ (6 * j3 + 7) := by
            rw [show 6 * j3 + 8 = (6 * j3 + 7) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
          omega
        rw [h3xj, core2_mul2 (2 * yj3) (by omega), core2_mul2 yj3 (by omega), core2_of_odd yj3 hyj3_odd]
      if hxj3_desc : evalLaurentSumNum terms (syracuseOddStep xj3) * laurentValDen A0 B0 C0 xj3 <
          evalLaurentSumNum terms xj3 * laurentValDen A0 B0 C0 (syracuseOddStep xj3) then
        have haC_le_cA : aMax + C0 ≤ cMax + A0 := by
          if hle : aMax + C0 ≤ cMax + A0 then exact hle
          else
            exfalso
            have hdesc_j := hxj3_desc
            rw [hsyr_xj3] at hdesc_j
            have hxjp1 : xj3 + 1 = 2 * zj := by dsimp [xj3]; omega
            have hyjp1 : yj3 + 1 = 2 ^ (6 * j3 + 7) := by dsimp [yj3]; omega
            have hzj_odd : zj % 2 = 1 := by
              rcases core2_decomp zj (by omega) with ⟨_, _, hco, hcm⟩
              change v2Pow (geomSpineEntry j3) * core2 zj = zj at hcm
              rw [hv2_zj, Nat.one_mul] at hcm
              rwa [← hcm]
            have hzj_nd3 : zj % 3 ≠ 0 := by
              rcases core3_decomp zj (by omega) with ⟨_, _, hcnd, _, hcm⟩
              change v3Pow (geomSpineEntry j3) * core3 zj = zj at hcm
              rw [hv3_zj, Nat.one_mul] at hcm
              rwa [← hcm]
            have hv2_xj : v2Pow (xj3 + 1) = 2 := by
              rw [hxjp1, v2Pow_mul2 zj (by omega)]
              change 2 * v2Pow (geomSpineEntry j3) = 2; rw [hv2_zj]
            have hv3_xj : v3Pow (xj3 + 1) = 1 := by
              rw [hxjp1, v3Pow_mul2 zj (by omega)]; exact hv3_zj
            have hg_xj : coprime23Core (xj3 + 1) = zj := by
              rw [hxjp1, coprime23Core_mul2 zj (by omega), coprime23Core_of_coprime zj hzj_odd hzj_nd3]
            rcases pow2_eq_v2Pow_w5 (6 * j3 + 7) with ⟨hv2_2k, hv3_2k, hg_2k⟩
            have hzj_gt : 2 ^ (6 * j3 + 6) ≤ zj := by
              have hsp : 2 ^ (6 * j3 + 8) = 4 * 2 ^ (6 * j3 + 6) := by
                rw [show 6 * j3 + 8 = (6 * j3 + 6) + 2 by omega, Nat.pow_add, Nat.mul_comm]
              have hp6 := pow2_pos_nat (6 * j3 + 6)
              omega
            have hzj_le : zj ≤ 2 ^ (6 * j3 + 8) := by omega
            have hlhs_j : 2 ^ (6 * j3 * (aMax + C0)) ≤
                evalLaurentSumNum terms yj3 * laurentValDen A0 B0 C0 xj3 := by
              have htA_ge := evalLaurentSumNum_ge_active_term terms tA yj3 hmA hpA
              unfold laurentValNum at htA_ge
              rw [hyjp1, hv2_2k, hv3_2k, hg_2k, heA, pow_pow_eq_mul_w5 2 (6 * j3 + 7) aMax] at htA_ge
              simp only [Nat.one_pow, Nat.mul_one] at htA_ge
              have hden_ge : 2 ^ ((6 * j3 + 6) * C0) ≤ laurentValDen A0 B0 C0 xj3 := by
                unfold laurentValDen
                rw [hv2_xj, hv3_xj, hg_xj, Nat.one_pow, Nat.mul_one]
                have hzC0 : 2 ^ ((6 * j3 + 6) * C0) ≤ zj ^ C0 := by
                  rw [← pow_pow_eq_mul_w5 2 (6 * j3 + 6) C0]
                  exact nat_pow_mono_base _ zj hzj_gt C0
                have hm := Nat.mul_le_mul (pow2_pos_nat A0) hzC0
                simpa using hm
              have hmul_ge := Nat.mul_le_mul htA_ge hden_ge
              rw [← Nat.pow_add 2 ((6 * j3 + 7) * aMax) ((6 * j3 + 6) * C0)] at hmul_ge
              have hexp_ge : 6 * j3 * (aMax + C0) ≤ (6 * j3 + 7) * aMax + (6 * j3 + 6) * C0 := by
                rw [Nat.mul_add (6 * j3) aMax C0, Nat.add_mul (6 * j3) 7 aMax,
                    Nat.add_mul (6 * j3) 6 C0]
                omega
              exact Nat.le_trans (pow2_mono_nat hexp_ge) hmul_ge
            have hrhs_j : evalLaurentSumNum terms xj3 * laurentValDen A0 B0 C0 yj3 ≤
                (sumLaurentCoeffs terms * 2 ^ aMax * 2 ^ (8 * cMax + 7 * A0)) *
                  2 ^ (6 * j3 * (cMax + A0)) := by
              have hnum_le : evalLaurentSumNum terms xj3 ≤
                  sumLaurentCoeffs terms * (2 ^ aMax * 2 ^ ((6 * j3 + 8) * cMax)) := by
                apply evalLaurentSumNum_le_sumCoeffs_mul
                intro t hm hp
                rcases active_exps_le_max terms t hm hp with ⟨ha_le, _, hc_le⟩
                unfold laurentValNum
                rw [hv2_xj, hv3_xj, hg_xj, Nat.one_pow, Nat.mul_one]
                have hzc : zj ^ t.cExp ≤ 2 ^ ((6 * j3 + 8) * cMax) := by
                  have h1 : zj ^ t.cExp ≤ (2 ^ (6 * j3 + 8)) ^ t.cExp :=
                    nat_pow_mono_base zj _ hzj_le t.cExp
                  rw [pow_pow_eq_mul_w5 2 (6 * j3 + 8) t.cExp] at h1
                  exact Nat.le_trans h1 (pow2_mono_nat (Nat.mul_le_mul_left _ hc_le))
                exact Nat.mul_le_mul (pow2_mono_nat ha_le) hzc
              have hden_eq : laurentValDen A0 B0 C0 yj3 = 2 ^ ((6 * j3 + 7) * A0) := by
                unfold laurentValDen
                rw [hyjp1, hv2_2k, hv3_2k, hg_2k, pow_pow_eq_mul_w5 2 (6 * j3 + 7) A0]
                simp only [Nat.one_pow, Nat.mul_one]
              rw [hden_eq]
              have hm := Nat.mul_le_mul_right (2 ^ ((6 * j3 + 7) * A0)) hnum_le
              have hrw : (sumLaurentCoeffs terms * (2 ^ aMax * 2 ^ ((6 * j3 + 8) * cMax))) *
                  2 ^ ((6 * j3 + 7) * A0) =
                  (sumLaurentCoeffs terms * 2 ^ aMax * 2 ^ (8 * cMax + 7 * A0)) *
                    2 ^ (6 * j3 * (cMax + A0)) := by
                have hexp : (6 * j3 + 8) * cMax + (6 * j3 + 7) * A0 =
                    (8 * cMax + 7 * A0) + 6 * j3 * (cMax + A0) := by
                  rw [Nat.add_mul (6 * j3) 8 cMax, Nat.add_mul (6 * j3) 7 A0,
                      Nat.mul_add (6 * j3) cMax A0]
                  omega
                calc
                  (sumLaurentCoeffs terms * (2 ^ aMax * 2 ^ ((6 * j3 + 8) * cMax))) *
                      2 ^ ((6 * j3 + 7) * A0)
                      = (sumLaurentCoeffs terms * 2 ^ aMax) *
                          (2 ^ ((6 * j3 + 8) * cMax) * 2 ^ ((6 * j3 + 7) * A0)) := by
                        rw [← Nat.mul_assoc (sumLaurentCoeffs terms), Nat.mul_assoc]
                  _ = (sumLaurentCoeffs terms * 2 ^ aMax) *
                          (2 ^ (8 * cMax + 7 * A0) * 2 ^ (6 * j3 * (cMax + A0))) := by
                        rw [← Nat.pow_add, hexp, Nat.pow_add]
                  _ = (sumLaurentCoeffs terms * 2 ^ aMax * 2 ^ (8 * cMax + 7 * A0)) *
                          2 ^ (6 * j3 * (cMax + A0)) := (Nat.mul_assoc _ _ _).symm
              rwa [hrw] at hm
            have hcomb_j : 2 ^ (6 * j3 * (aMax + C0)) <
                (sumLaurentCoeffs terms * 2 ^ aMax * 2 ^ (8 * cMax + 7 * A0)) *
                  2 ^ (6 * j3 * (cMax + A0)) :=
              Nat.lt_of_le_of_lt hlhs_j (Nat.lt_of_lt_of_le hdesc_j hrhs_j)
            have hexp_split : 6 * j3 + 6 * j3 * (cMax + A0) ≤ 6 * j3 * (aMax + C0) := by
              have hd1 : cMax + A0 + 1 ≤ aMax + C0 := by omega
              have hm := Nat.mul_le_mul_left (6 * j3) hd1
              rw [Nat.mul_add, Nat.mul_one] at hm; omega
            have hp2_split : 2 ^ j3 * 2 ^ (6 * j3 * (cMax + A0)) ≤ 2 ^ (6 * j3 * (aMax + C0)) := by
              have h1 : 2 ^ j3 ≤ 2 ^ (6 * j3) := pow2_mono_nat (by omega)
              have h2 : 2 ^ (6 * j3) * 2 ^ (6 * j3 * (cMax + A0)) ≤ 2 ^ (6 * j3 * (aMax + C0)) := by
                rw [← Nat.pow_add]; exact pow2_mono_nat hexp_split
              exact Nat.le_trans (Nat.mul_le_mul_right _ h1) h2
            have hcanc2 := nat_mul_lt_cancel_right_w5 (2 ^ (6 * j3 * (cMax + A0))) _ _
              (pow2_pos_nat _) (Nat.lt_of_le_of_lt hp2_split hcomb_j)
            have hp2_gt : 2 ^ j3 ≥ j3 + 1 := pow2_ge_succ_self j3
            dsimp [j3] at hcanc2 hp2_gt
            omega
        -- Constructive witness 4: `zk = 8 * 3^k - 1 -> wk = 4 * 3^(k + 1) - 1`
        let db := bMax - B0
        have hdb_pos : db ≥ 1 := by dsimp [db]; omega
        have hbMax_eq : bMax = B0 + db := by dsimp [db]; omega
        have haMax_le : aMax ≤ A0 + db := by omega
        let Clow := sumLaurentCoeffs terms * (8 ^ aMax * 4 ^ A0 * 3 ^ B0)
        let k := Clow + 1
        have hk_pos : k ≥ 1 := by dsimp [k]; omega
        let zk := 8 * 3 ^ k - 1
        let wk := 4 * 3 ^ (k + 1) - 1
        have hp3k_ge3 : 3 ^ k ≥ 3 := by
          rw [show k = (k - 1) + 1 by omega, Nat.pow_succ]
          have hp0 := pow3_pos_nat (k - 1); omega
        have hzk_ge3 : zk ≥ 3 := by dsimp [zk]; omega
        have hzk_odd : zk % 2 = 1 := by dsimp [zk]; omega
        have hwk_odd : wk % 2 = 1 := by dsimp [wk]; omega
        have hwk_ge3 : wk ≥ 3 := by dsimp [wk]; rw [Nat.pow_succ]; omega
        have hsyr_zk : syracuseOddStep zk = wk := by
          unfold syracuseOddStep
          have h3zk : 3 * zk + 1 = 2 * wk := by dsimp [zk, wk]; rw [Nat.pow_succ 3 k]; omega
          rw [h3zk, core2_mul2 wk (by omega), core2_of_odd wk hwk_odd]
        if hzk_desc : evalLaurentSumNum terms (syracuseOddStep zk) * laurentValDen A0 B0 C0 zk <
            evalLaurentSumNum terms zk * laurentValDen A0 B0 C0 (syracuseOddStep zk) then
          exfalso
          have hdesc_z := hzk_desc
          rw [hsyr_zk] at hdesc_z
          have hzkp1 : zk + 1 = 2 * (2 * (2 * 3 ^ k)) := by dsimp [zk]; omega
          have hwkp1 : wk + 1 = 2 * (2 * 3 ^ (k + 1)) := by dsimp [wk]; omega
          rcases pow3_eq_v3Pow_w5 k with ⟨hv3_3k, hc3_3k⟩
          rcases pow3_eq_v3Pow_w5 (k + 1) with ⟨hv3_3k1, hc3_3k1⟩
          have hv2_zk : v2Pow (zk + 1) = 8 := by
            rw [hzkp1, v2Pow_mul2 _ (by omega), v2Pow_mul2 _ (by omega),
                v2Pow_mul2 (3 ^ k) (by omega), v2Pow_of_odd (3 ^ k) (pow3_odd_nat_sec8 k)]
          have hv3_zk : v3Pow (zk + 1) = 3 ^ k := by
            rw [hzkp1, v3Pow_mul2 _ (by omega), v3Pow_mul2 _ (by omega),
                v3Pow_mul2 (3 ^ k) (by omega), hv3_3k]
          have hg_zk : coprime23Core (zk + 1) = 1 := by
            rw [hzkp1, coprime23Core_mul2 _ (by omega), coprime23Core_mul2 _ (by omega),
                coprime23Core_mul2 (3 ^ k) (by omega)]
            unfold coprime23Core; rw [hc3_3k]; decide
          have hv2_wk : v2Pow (wk + 1) = 4 := by
            rw [hwkp1, v2Pow_mul2 _ (by omega), v2Pow_mul2 (3 ^ (k + 1)) (pow3_pos_nat _),
                v2Pow_of_odd (3 ^ (k + 1)) (pow3_odd_nat_sec8 (k + 1))]
          have hv3_wk : v3Pow (wk + 1) = 3 ^ (k + 1) := by
            rw [hwkp1, v3Pow_mul2 _ (by omega), v3Pow_mul2 (3 ^ (k + 1)) (pow3_pos_nat _), hv3_3k1]
          have hg_wk : coprime23Core (wk + 1) = 1 := by
            rw [hwkp1, coprime23Core_mul2 _ (by omega),
                coprime23Core_mul2 (3 ^ (k + 1)) (pow3_pos_nat _)]
            unfold coprime23Core; rw [hc3_3k1]; decide
          let Mtop := bMax + B0
          -- Decide existence of `t ∈ ts` with `t.coeff > 0 ∧ t.bExp = bMax` via Bool helper:
          let hasTopB : List LaurentTerm -> Bool := fun ts =>
            ts.any (fun t => decide (t.coeff > 0 ∧ t.bExp = bMax))
          have hterm_dom : ∀ (ts : List LaurentTerm),
              (∀ t ∈ ts, t.coeff > 0 -> t.aExp ≤ aMax ∧ t.bExp ≤ bMax) ->
              (evalLaurentSumNum ts wk * laurentValDen A0 B0 C0 zk) * 3 ^ k +
                sumLaurentCoeffs ts * (8 ^ aMax * 4 ^ A0 * 3 ^ B0) * 3 ^ (k * Mtop) ≥
                (evalLaurentSumNum ts zk * laurentValDen A0 B0 C0 wk) * 3 ^ k +
                  (if hasTopB ts = true then 3 ^ k * 3 ^ (k * Mtop) else 0) := by
            intro ts hts
            induction ts with
            | nil => simp [evalLaurentSumNum, sumLaurentCoeffs, hasTopB]
            | cons hd rest ih =>
              have ih_r := ih (fun t hm hp => hts t (List.mem_cons_of_mem _ hm) hp)
              simp only [evalLaurentSumNum, sumLaurentCoeffs, Nat.add_mul, hasTopB, List.any_cons]
              if hhd : hd.coeff > 0 then
                rcases hts hd (List.Mem.head _) hhd with ⟨hhd_a, hhd_b⟩
                if htop : hd.bExp = bMax then
                  have hdec_t : decide (hd.coeff > 0 ∧ hd.bExp = bMax) = true :=
                    decide_eq_true ⟨hhd, htop⟩
                  simp only [hdec_t, Bool.true_or, ite_true]
                  have hl_hd : laurentValNum hd.aExp hd.bExp hd.cExp wk * laurentValDen A0 B0 C0 zk =
                      (4 ^ hd.aExp * 4 ^ A0 * 2 ^ A0 * 3 ^ B0) * 3 ^ db * 3 ^ (k * Mtop) := by
                    unfold laurentValNum laurentValDen
                    rw [hv2_wk, hv3_wk, hg_wk, hv2_zk, hv3_zk, hg_zk, htop,
                        Nat.one_pow, Nat.mul_one, Nat.one_pow, Nat.mul_one,
                        pow_pow_eq_mul_w5 3 (k + 1) bMax, pow_pow_eq_mul_w5 3 k B0,
                        mul_pow_local 4 2 A0]
                    have hexp3 : (k + 1) * bMax + k * B0 = B0 + db + k * Mtop := by
                      dsimp [Mtop]; rw [Nat.add_mul k 1 bMax, Nat.one_mul, Nat.mul_add k bMax B0]
                      omega
                    calc
                      (4 ^ hd.aExp * 3 ^ ((k + 1) * bMax)) * ((4 ^ A0 * 2 ^ A0) * 3 ^ (k * B0))
                          = (4 ^ hd.aExp * (4 ^ A0 * 2 ^ A0)) * (3 ^ ((k + 1) * bMax) * 3 ^ (k * B0)) := by
                            calc
                              (4 ^ hd.aExp * 3 ^ ((k + 1) * bMax)) * ((4 ^ A0 * 2 ^ A0) * 3 ^ (k * B0))
                                  = 4 ^ hd.aExp * (3 ^ ((k + 1) * bMax) * ((4 ^ A0 * 2 ^ A0) * 3 ^ (k * B0))) :=
                                    Nat.mul_assoc _ _ _
                              _ = 4 ^ hd.aExp * (((4 ^ A0 * 2 ^ A0) * 3 ^ ((k + 1) * bMax)) * 3 ^ (k * B0)) := by
                                    rw [← Nat.mul_assoc (3 ^ ((k + 1) * bMax)),
                                        Nat.mul_comm (3 ^ ((k + 1) * bMax)) (4 ^ A0 * 2 ^ A0)]
                              _ = (4 ^ hd.aExp * (4 ^ A0 * 2 ^ A0)) * (3 ^ ((k + 1) * bMax) * 3 ^ (k * B0)) := by
                                    rw [Nat.mul_assoc (4 ^ A0 * 2 ^ A0), ← Nat.mul_assoc (4 ^ hd.aExp)]
                      _ = (4 ^ hd.aExp * 4 ^ A0 * 2 ^ A0) * (3 ^ B0 * (3 ^ db * 3 ^ (k * Mtop))) := by
                            rw [← Nat.mul_assoc (4 ^ hd.aExp), ← Nat.pow_add 3, hexp3,
                                Nat.pow_add 3 (B0 + db), Nat.pow_add 3 B0 db, Nat.mul_assoc (3 ^ B0)]
                      _ = (4 ^ hd.aExp * 4 ^ A0 * 2 ^ A0 * 3 ^ B0) * 3 ^ db * 3 ^ (k * Mtop) := by
                            rw [← Nat.mul_assoc, ← Nat.mul_assoc]
                  have hr_hd : laurentValNum hd.aExp hd.bExp hd.cExp zk * laurentValDen A0 B0 C0 wk =
                      (4 ^ hd.aExp * 4 ^ A0 * 3 ^ B0) * 2 ^ hd.aExp * 3 ^ (k * Mtop) := by
                    unfold laurentValNum laurentValDen
                    rw [hv2_wk, hv3_wk, hg_wk, hv2_zk, hv3_zk, hg_zk, htop,
                        Nat.one_pow, Nat.mul_one, Nat.one_pow, Nat.mul_one,
                        pow_pow_eq_mul_w5 3 k bMax, pow_pow_eq_mul_w5 3 (k + 1) B0,
                        mul_pow_local 4 2 hd.aExp]
                    have hexp3 : k * bMax + (k + 1) * B0 = B0 + k * Mtop := by
                      dsimp [Mtop]; rw [Nat.add_mul k 1 B0, Nat.one_mul, Nat.mul_add k bMax B0]
                      omega
                    calc
                      ((4 ^ hd.aExp * 2 ^ hd.aExp) * 3 ^ (k * bMax)) * (4 ^ A0 * 3 ^ ((k + 1) * B0))
                          = ((4 ^ hd.aExp * 4 ^ A0) * 2 ^ hd.aExp) * (3 ^ (k * bMax) * 3 ^ ((k + 1) * B0)) := by
                            calc
                              ((4 ^ hd.aExp * 2 ^ hd.aExp) * 3 ^ (k * bMax)) * (4 ^ A0 * 3 ^ ((k + 1) * B0))
                                  = (4 ^ hd.aExp * 2 ^ hd.aExp) * (3 ^ (k * bMax) * (4 ^ A0 * 3 ^ ((k + 1) * B0))) :=
                                    Nat.mul_assoc _ _ _
                              _ = (4 ^ hd.aExp * 2 ^ hd.aExp) * ((4 ^ A0 * 3 ^ (k * bMax)) * 3 ^ ((k + 1) * B0)) := by
                                    rw [← Nat.mul_assoc (3 ^ (k * bMax)), Nat.mul_comm (3 ^ (k * bMax)) (4 ^ A0)]
                              _ = ((4 ^ hd.aExp * 4 ^ A0) * 2 ^ hd.aExp) * (3 ^ (k * bMax) * 3 ^ ((k + 1) * B0)) := by
                                    rw [Nat.mul_assoc (4 ^ A0), ← Nat.mul_assoc (4 ^ hd.aExp * 2 ^ hd.aExp),
                                        Nat.mul_assoc (4 ^ hd.aExp) (2 ^ hd.aExp) (4 ^ A0),
                                        Nat.mul_comm (2 ^ hd.aExp) (4 ^ A0),
                                        ← Nat.mul_assoc (4 ^ hd.aExp) (4 ^ A0)]
                      _ = ((4 ^ hd.aExp * 4 ^ A0) * 2 ^ hd.aExp) * (3 ^ B0 * 3 ^ (k * Mtop)) := by
                            rw [← Nat.pow_add 3, hexp3, Nat.pow_add 3 B0 (k * Mtop)]
                      _ = (4 ^ hd.aExp * 4 ^ A0 * 3 ^ B0) * 2 ^ hd.aExp * 3 ^ (k * Mtop) := by
                            calc
                              ((4 ^ hd.aExp * 4 ^ A0) * 2 ^ hd.aExp) * (3 ^ B0 * 3 ^ (k * Mtop))
                                  = (((4 ^ hd.aExp * 4 ^ A0) * 2 ^ hd.aExp) * 3 ^ B0) * 3 ^ (k * Mtop) :=
                                    (Nat.mul_assoc _ _ _).symm
                              _ = ((4 ^ hd.aExp * 4 ^ A0) * (3 ^ B0 * 2 ^ hd.aExp)) * 3 ^ (k * Mtop) := by
                                    rw [Nat.mul_assoc (4 ^ hd.aExp * 4 ^ A0), Nat.mul_comm (2 ^ hd.aExp) (3 ^ B0)]
                              _ = (4 ^ hd.aExp * 4 ^ A0 * 3 ^ B0) * 2 ^ hd.aExp * 3 ^ (k * Mtop) := by
                                    rw [← Nat.mul_assoc (4 ^ hd.aExp * 4 ^ A0)]
                  have hhd_gap : hd.coeff * laurentValNum hd.aExp hd.bExp hd.cExp zk * laurentValDen A0 B0 C0 wk +
                      3 ^ (k * Mtop) ≤
                      hd.coeff * laurentValNum hd.aExp hd.bExp hd.cExp wk * laurentValDen A0 B0 C0 zk := by
                    rw [Nat.mul_assoc hd.coeff, Nat.mul_assoc hd.coeff, hl_hd, hr_hd]
                    have ha_le_db : 2 ^ hd.aExp ≤ 2 ^ A0 * 2 ^ db := by
                      rw [← Nat.pow_add]; exact pow2_mono_nat (Nat.le_trans hhd_a haMax_le)
                    have h3_gt_2 : 2 ^ db + 1 ≤ 3 ^ db := pow3_gt_pow2_pos db hdb_pos
                    let Kbase := 4 ^ hd.aExp * 4 ^ A0 * 2 ^ A0 * 3 ^ B0
                    have hKbase_pos : Kbase ≥ 1 :=
                      Nat.mul_le_mul
                        (Nat.mul_le_mul
                          (Nat.mul_le_mul (nat_pow_pos_of_pos 4 (by decide) _)
                                          (nat_pow_pos_of_pos 4 (by decide) _))
                          (pow2_pos_nat A0))
                        (pow3_pos_nat B0)
                    have hr_le : (4 ^ hd.aExp * 4 ^ A0 * 3 ^ B0) * 2 ^ hd.aExp ≤ Kbase * 2 ^ db := by
                      have hm := Nat.mul_le_mul_left (4 ^ hd.aExp * 4 ^ A0 * 3 ^ B0) ha_le_db
                      have hrw : (4 ^ hd.aExp * 4 ^ A0 * 3 ^ B0) * (2 ^ A0 * 2 ^ db) = Kbase * 2 ^ db := by
                        dsimp [Kbase]
                        calc
                          (4 ^ hd.aExp * 4 ^ A0 * 3 ^ B0) * (2 ^ A0 * 2 ^ db)
                              = ((4 ^ hd.aExp * 4 ^ A0) * (3 ^ B0 * 2 ^ A0)) * 2 ^ db := by
                                rw [← Nat.mul_assoc, Nat.mul_assoc (4 ^ hd.aExp * 4 ^ A0)]
                          _ = (4 ^ hd.aExp * 4 ^ A0 * 2 ^ A0 * 3 ^ B0) * 2 ^ db := by
                                rw [Nat.mul_comm (3 ^ B0) (2 ^ A0), ← Nat.mul_assoc (4 ^ hd.aExp * 4 ^ A0)]
                      rwa [hrw] at hm
                    have hstep_k : hd.coeff * (Kbase * 2 ^ db * 3 ^ (k * Mtop)) + 3 ^ (k * Mtop) ≤
                        hd.coeff * (Kbase * 3 ^ db * 3 ^ (k * Mtop)) := by
                      have hm1 : Kbase * (2 ^ db + 1) ≤ Kbase * 3 ^ db := Nat.mul_le_mul_left Kbase h3_gt_2
                      rw [Nat.mul_add, Nat.mul_one] at hm1
                      have hm2 := Nat.mul_le_mul_left hd.coeff (Nat.mul_le_mul_right (3 ^ (k * Mtop)) hm1)
                      rw [Nat.add_mul, Nat.mul_add] at hm2
                      have hextra : 3 ^ (k * Mtop) ≤ hd.coeff * (Kbase * 3 ^ (k * Mtop)) := by
                        have hk1 : 1 ≤ hd.coeff * Kbase := Nat.mul_le_mul hhd hKbase_pos
                        have hm3 := Nat.mul_le_mul_right (3 ^ (k * Mtop)) hk1
                        rwa [Nat.one_mul, Nat.mul_assoc] at hm3
                      exact Nat.le_trans (Nat.add_le_add_left hextra _) hm2
                    have hr_mul := Nat.mul_le_mul_left hd.coeff (Nat.mul_le_mul_right (3 ^ (k * Mtop)) hr_le)
                    exact Nat.le_trans (Nat.add_le_add_right hr_mul _) hstep_k
                  have hmul3k := Nat.mul_le_mul_right (3 ^ k) hhd_gap
                  rw [Nat.add_mul, Nat.mul_comm (3 ^ (k * Mtop)) (3 ^ k)] at hmul3k
                  cases hb_r : List.any rest (fun t => decide (t.coeff > 0 ∧ t.bExp = bMax)) with
                  | true =>
                    simp only [hasTopB, hb_r, ite_true] at ih_r
                    have hdrop : (evalLaurentSumNum rest zk * laurentValDen A0 B0 C0 wk) * 3 ^ k ≤
                        (evalLaurentSumNum rest wk * laurentValDen A0 B0 C0 zk) * 3 ^ k +
                          sumLaurentCoeffs rest * (8 ^ aMax * 4 ^ A0 * 3 ^ B0) * 3 ^ (k * Mtop) :=
                      Nat.le_trans (Nat.le_add_right _ _) ih_r
                    have hsum := Nat.add_le_add hmul3k hdrop
                    have h1 : (hd.coeff * laurentValNum hd.aExp hd.bExp hd.cExp zk *
                        laurentValDen A0 B0 C0 wk * 3 ^ k + 3 ^ k * 3 ^ (k * Mtop)) +
                        evalLaurentSumNum rest zk * laurentValDen A0 B0 C0 wk * 3 ^ k =
                        (hd.coeff * laurentValNum hd.aExp hd.bExp hd.cExp zk *
                          laurentValDen A0 B0 C0 wk * 3 ^ k +
                          evalLaurentSumNum rest zk * laurentValDen A0 B0 C0 wk * 3 ^ k) +
                          3 ^ k * 3 ^ (k * Mtop) := by
                      rw [Nat.add_assoc, Nat.add_comm (3 ^ k * 3 ^ (k * Mtop)), ← Nat.add_assoc]
                    rw [h1] at hsum
                    have h2 : hd.coeff * laurentValNum hd.aExp hd.bExp hd.cExp wk *
                        laurentValDen A0 B0 C0 zk * 3 ^ k +
                        (evalLaurentSumNum rest wk * laurentValDen A0 B0 C0 zk * 3 ^ k +
                          sumLaurentCoeffs rest * (8 ^ aMax * 4 ^ A0 * 3 ^ B0) * 3 ^ (k * Mtop)) ≤
                        (hd.coeff * laurentValNum hd.aExp hd.bExp hd.cExp wk *
                          laurentValDen A0 B0 C0 zk * 3 ^ k +
                          evalLaurentSumNum rest wk * laurentValDen A0 B0 C0 zk * 3 ^ k) +
                          (hd.coeff * (8 ^ aMax * 4 ^ A0 * 3 ^ B0) * 3 ^ (k * Mtop) +
                            sumLaurentCoeffs rest * (8 ^ aMax * 4 ^ A0 * 3 ^ B0) * 3 ^ (k * Mtop)) := by
                      rw [← Nat.add_assoc]
                      exact Nat.add_le_add_left (Nat.le_add_left _ _) _
                    exact Nat.le_trans hsum h2
                  | false =>
                    simp only [hasTopB, hb_r, Bool.false_eq_true, ite_false, Nat.add_zero] at ih_r
                    have hsum := Nat.add_le_add hmul3k ih_r
                    have h1 : (hd.coeff * laurentValNum hd.aExp hd.bExp hd.cExp zk *
                        laurentValDen A0 B0 C0 wk * 3 ^ k + 3 ^ k * 3 ^ (k * Mtop)) +
                        evalLaurentSumNum rest zk * laurentValDen A0 B0 C0 wk * 3 ^ k =
                        (hd.coeff * laurentValNum hd.aExp hd.bExp hd.cExp zk *
                          laurentValDen A0 B0 C0 wk * 3 ^ k +
                          evalLaurentSumNum rest zk * laurentValDen A0 B0 C0 wk * 3 ^ k) +
                          3 ^ k * 3 ^ (k * Mtop) := by
                      rw [Nat.add_assoc, Nat.add_comm (3 ^ k * 3 ^ (k * Mtop)), ← Nat.add_assoc]
                    rw [h1] at hsum
                    have h2 : hd.coeff * laurentValNum hd.aExp hd.bExp hd.cExp wk *
                        laurentValDen A0 B0 C0 zk * 3 ^ k +
                        (evalLaurentSumNum rest wk * laurentValDen A0 B0 C0 zk * 3 ^ k +
                          sumLaurentCoeffs rest * (8 ^ aMax * 4 ^ A0 * 3 ^ B0) * 3 ^ (k * Mtop)) ≤
                        (hd.coeff * laurentValNum hd.aExp hd.bExp hd.cExp wk *
                          laurentValDen A0 B0 C0 zk * 3 ^ k +
                          evalLaurentSumNum rest wk * laurentValDen A0 B0 C0 zk * 3 ^ k) +
                          (hd.coeff * (8 ^ aMax * 4 ^ A0 * 3 ^ B0) * 3 ^ (k * Mtop) +
                            sumLaurentCoeffs rest * (8 ^ aMax * 4 ^ A0 * 3 ^ B0) * 3 ^ (k * Mtop)) := by
                      rw [← Nat.add_assoc]
                      exact Nat.add_le_add_left (Nat.le_add_left _ _) _
                    exact Nat.le_trans hsum h2
                else
                  have hdec_f : decide (hd.coeff > 0 ∧ hd.bExp = bMax) = false :=
                    decide_eq_false (fun hc => htop hc.2)
                  simp only [hdec_f, Bool.false_or]
                  have hlt_b : hd.bExp + 1 ≤ bMax := by omega
                  have hr_sub : (hd.coeff * laurentValNum hd.aExp hd.bExp hd.cExp zk *
                      laurentValDen A0 B0 C0 wk) * 3 ^ k ≤
                      hd.coeff * (8 ^ aMax * 4 ^ A0 * 3 ^ B0) * 3 ^ (k * Mtop) := by
                    unfold laurentValNum laurentValDen
                    rw [hv2_wk, hv3_wk, hg_wk, hv2_zk, hv3_zk, hg_zk,
                        Nat.one_pow, Nat.mul_one, Nat.one_pow, Nat.mul_one,
                        pow_pow_eq_mul_w5 3 k hd.bExp, pow_pow_eq_mul_w5 3 (k + 1) B0]
                    have hexp_le : k * hd.bExp + (k + 1) * B0 + k ≤ B0 + k * Mtop := by
                      dsimp [Mtop]
                      have hm := Nat.mul_le_mul_left k hlt_b
                      rw [Nat.mul_add, Nat.mul_one] at hm
                      rw [Nat.add_mul k 1 B0, Nat.one_mul, Nat.mul_add k bMax B0]
                      omega
                    have hp3_le : 3 ^ (k * hd.bExp) * 3 ^ ((k + 1) * B0) * 3 ^ k ≤
                        3 ^ B0 * 3 ^ (k * Mtop) := by
                      rw [← Nat.pow_add 3 (k * hd.bExp) ((k + 1) * B0),
                          ← Nat.pow_add 3 (k * hd.bExp + (k + 1) * B0) k,
                          ← Nat.pow_add 3 B0 (k * Mtop)]
                      have hdiff : B0 + k * Mtop =
                          (k * hd.bExp + (k + 1) * B0 + k) +
                            (B0 + k * Mtop - (k * hd.bExp + (k + 1) * B0 + k)) := by omega
                      rw [hdiff, Nat.pow_add 3 (k * hd.bExp + (k + 1) * B0 + k)]
                      have hm3 := Nat.mul_le_mul_left (3 ^ (k * hd.bExp + (k + 1) * B0 + k))
                        (pow3_pos_nat (B0 + k * Mtop - (k * hd.bExp + (k + 1) * B0 + k)))
                      simpa using hm3
                    have h8_le : 8 ^ hd.aExp ≤ 8 ^ aMax := by
                      have hd_a : aMax = hd.aExp + (aMax - hd.aExp) := by omega
                      rw [hd_a, Nat.pow_add]
                      have hm8 := Nat.mul_le_mul_left (8 ^ hd.aExp)
                        (nat_pow_pos_of_pos 8 (by decide) (aMax - hd.aExp))
                      simpa using hm8
                    have hrw : (hd.coeff * (8 ^ hd.aExp * 3 ^ (k * hd.bExp)) *
                        (4 ^ A0 * 3 ^ ((k + 1) * B0))) * 3 ^ k =
                        (hd.coeff * (8 ^ hd.aExp * 4 ^ A0)) *
                          (3 ^ (k * hd.bExp) * 3 ^ ((k + 1) * B0) * 3 ^ k) := by
                      calc
                        (hd.coeff * (8 ^ hd.aExp * 3 ^ (k * hd.bExp)) *
                            (4 ^ A0 * 3 ^ ((k + 1) * B0))) * 3 ^ k
                            = hd.coeff * ((8 ^ hd.aExp * 3 ^ (k * hd.bExp)) *
                                (4 ^ A0 * 3 ^ ((k + 1) * B0))) * 3 ^ k := by rw [Nat.mul_assoc hd.coeff]
                        _ = hd.coeff * ((8 ^ hd.aExp * 4 ^ A0) *
                                (3 ^ (k * hd.bExp) * 3 ^ ((k + 1) * B0))) * 3 ^ k := by
                              have hmid : (8 ^ hd.aExp * 3 ^ (k * hd.bExp)) * (4 ^ A0 * 3 ^ ((k + 1) * B0)) =
                                  (8 ^ hd.aExp * 4 ^ A0) * (3 ^ (k * hd.bExp) * 3 ^ ((k + 1) * B0)) := by
                                calc
                                  (8 ^ hd.aExp * 3 ^ (k * hd.bExp)) * (4 ^ A0 * 3 ^ ((k + 1) * B0))
                                      = 8 ^ hd.aExp * (3 ^ (k * hd.bExp) * (4 ^ A0 * 3 ^ ((k + 1) * B0))) :=
                                        Nat.mul_assoc _ _ _
                                  _ = 8 ^ hd.aExp * ((4 ^ A0 * 3 ^ (k * hd.bExp)) * 3 ^ ((k + 1) * B0)) := by
                                        rw [← Nat.mul_assoc (3 ^ (k * hd.bExp)),
                                            Nat.mul_comm (3 ^ (k * hd.bExp)) (4 ^ A0)]
                                  _ = (8 ^ hd.aExp * 4 ^ A0) * (3 ^ (k * hd.bExp) * 3 ^ ((k + 1) * B0)) := by
                                        rw [Nat.mul_assoc (4 ^ A0), ← Nat.mul_assoc (8 ^ hd.aExp)]
                              rw [hmid]
                        _ = (hd.coeff * (8 ^ hd.aExp * 4 ^ A0)) *
                              (3 ^ (k * hd.bExp) * 3 ^ ((k + 1) * B0) * 3 ^ k) := by
                              rw [← Nat.mul_assoc hd.coeff (8 ^ hd.aExp * 4 ^ A0),
                                  Nat.mul_assoc (hd.coeff * (8 ^ hd.aExp * 4 ^ A0))]
                    rw [hrw]
                    have hm_tot := Nat.mul_le_mul
                      (Nat.mul_le_mul_left hd.coeff (Nat.mul_le_mul_right (4 ^ A0) h8_le))
                      hp3_le
                    have hrw2 : (hd.coeff * (8 ^ aMax * 4 ^ A0)) * (3 ^ B0 * 3 ^ (k * Mtop)) =
                        hd.coeff * (8 ^ aMax * 4 ^ A0 * 3 ^ B0) * 3 ^ (k * Mtop) := by
                      rw [← Nat.mul_assoc (hd.coeff * (8 ^ aMax * 4 ^ A0)),
                          Nat.mul_assoc hd.coeff (8 ^ aMax * 4 ^ A0) (3 ^ B0)]
                    rwa [hrw2] at hm_tot
                  have hsum := Nat.add_le_add hr_sub ih_r
                  have hlhs_ge : (hd.coeff * laurentValNum hd.aExp hd.bExp hd.cExp zk *
                      laurentValDen A0 B0 C0 wk * 3 ^ k +
                      evalLaurentSumNum rest zk * laurentValDen A0 B0 C0 wk * 3 ^ k) +
                      (if List.any rest (fun t => decide (t.coeff > 0 ∧ t.bExp = bMax)) = true
                       then 3 ^ k * 3 ^ (k * Mtop) else 0) =
                      hd.coeff * laurentValNum hd.aExp hd.bExp hd.cExp zk *
                        laurentValDen A0 B0 C0 wk * 3 ^ k +
                      (evalLaurentSumNum rest zk * laurentValDen A0 B0 C0 wk * 3 ^ k +
                        if hasTopB rest = true then 3 ^ k * 3 ^ (k * Mtop) else 0) :=
                    Nat.add_assoc _ _ _
                  have hrhs_le2 : hd.coeff * (8 ^ aMax * 4 ^ A0 * 3 ^ B0) * 3 ^ (k * Mtop) +
                      (evalLaurentSumNum rest wk * laurentValDen A0 B0 C0 zk * 3 ^ k +
                        sumLaurentCoeffs rest * (8 ^ aMax * 4 ^ A0 * 3 ^ B0) * 3 ^ (k * Mtop)) ≤
                      (hd.coeff * laurentValNum hd.aExp hd.bExp hd.cExp wk *
                        laurentValDen A0 B0 C0 zk * 3 ^ k +
                        evalLaurentSumNum rest wk * laurentValDen A0 B0 C0 zk * 3 ^ k) +
                        (hd.coeff * (8 ^ aMax * 4 ^ A0 * 3 ^ B0) * 3 ^ (k * Mtop) +
                          sumLaurentCoeffs rest * (8 ^ aMax * 4 ^ A0 * 3 ^ B0) * 3 ^ (k * Mtop)) := by
                    have hswap_r : hd.coeff * (8 ^ aMax * 4 ^ A0 * 3 ^ B0) * 3 ^ (k * Mtop) +
                        (evalLaurentSumNum rest wk * laurentValDen A0 B0 C0 zk * 3 ^ k +
                          sumLaurentCoeffs rest * (8 ^ aMax * 4 ^ A0 * 3 ^ B0) * 3 ^ (k * Mtop)) =
                        evalLaurentSumNum rest wk * laurentValDen A0 B0 C0 zk * 3 ^ k +
                          (hd.coeff * (8 ^ aMax * 4 ^ A0 * 3 ^ B0) * 3 ^ (k * Mtop) +
                            sumLaurentCoeffs rest * (8 ^ aMax * 4 ^ A0 * 3 ^ B0) * 3 ^ (k * Mtop)) := by
                      rw [← Nat.add_assoc,
                          Nat.add_comm (hd.coeff * (8 ^ aMax * 4 ^ A0 * 3 ^ B0) * 3 ^ (k * Mtop)),
                          Nat.add_assoc]
                    rw [hswap_r]
                    exact Nat.add_le_add_right (Nat.le_add_left _ _) _
                  rw [← hlhs_ge] at hsum
                  exact Nat.le_trans hsum hrhs_le2
              else
                have hc0 : hd.coeff = 0 := by omega
                have hdec_f : decide (hd.coeff > 0 ∧ hd.bExp = bMax) = false :=
                  decide_eq_false (fun hc => hhd hc.1)
                simp only [hdec_f, Bool.false_or]
                simp only [hc0, Nat.zero_mul, Nat.zero_add]
                exact ih_r
          have hdom_all := hterm_dom terms (fun t hm hp =>
            ⟨(active_exps_le_max terms t hm hp).1, (active_exps_le_max terms t hm hp).2.1⟩)
          have htop_true : hasTopB terms = true := by
            dsimp [hasTopB]
            exact List.any_eq_true.mpr ⟨tB, hmB, decide_eq_true ⟨hpB, heB⟩⟩
          rw [htop_true] at hdom_all
          simp only [ite_true] at hdom_all
          have h3k_gt_Clow : Clow < 3 ^ k := by
            have hp3_ge : 3 ^ k ≥ k + 1 :=
              Nat.le_trans (pow2_ge_succ_self k) (nat_pow_mono_base 2 3 (by decide) k)
            exact Nat.lt_of_lt_of_le
              (Nat.lt_trans (Nat.lt_succ_self Clow) (Nat.lt_succ_self (Clow + 1))) hp3_ge
          have hextra_lt : Clow * 3 ^ (k * Mtop) < 3 ^ k * 3 ^ (k * Mtop) :=
            Nat.mul_lt_mul_of_pos_right h3k_gt_Clow (pow3_pos_nat _)
          have hstrict_mul : (evalLaurentSumNum terms wk * laurentValDen A0 B0 C0 zk) * 3 ^ k <
              (evalLaurentSumNum terms zk * laurentValDen A0 B0 C0 wk) * 3 ^ k :=
            Nat.mul_lt_mul_of_pos_right hdesc_z (pow3_pos_nat k)
          change (evalLaurentSumNum terms wk * laurentValDen A0 B0 C0 zk) * 3 ^ k +
              Clow * 3 ^ (k * Mtop) ≥ _ at hdom_all
          exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hdom_all (Nat.add_lt_add hstrict_mul hextra_lt))
        else
          exact ⟨zk, hzk_ge3, hzk_odd, by rw [hsyr_zk]; exact hwk_ge3, hzk_desc⟩
      else
        exact ⟨xj3, hxj3_ge3, hxj3_odd, by rw [hsyr_xj3]; exact hyj3_ge3, hxj3_desc⟩
    else
      exact ⟨xk2, hxk2_ge3, hxk2_odd, by rw [hsyr_xk2]; exact hyk2_ge3, hxk2_desc⟩
  else
    exact ⟨97, by decide, by decide, by decide, h97_desc⟩

theorem core2_reaches_by_halving_aux :
    ∀ (bound m : Nat), m > 0 -> m ≤ bound -> core2 m ≥ 3 ->
      ∃ r : Nat, collatzIter r m = core2 m ∧ (∀ j : Nat, j ≤ r -> collatzIter j m ≥ 3)
  | 0, _, hm, hle, _ => by omega
  | bound + 1, m, hm, hle, hc3 => by
    if hev : m % 2 = 0 then
      let k := m / 2
      have hk_pos : k > 0 := by dsimp [k]; omega
      have hm_eq : m = 2 * k := by dsimp [k]; omega
      have hck : core2 k ≥ 3 := by rw [hm_eq, core2_mul2 k hk_pos] at hc3; exact hc3
      rcases core2_reaches_by_halving_aux bound k hk_pos (by dsimp [k]; omega) hck with
        ⟨r, hr_eq, hall⟩
      refine ⟨r + 1, ?_, ?_⟩
      · simp only [collatzIter]
        rw [hm_eq, collatzStep_double_pos k, hr_eq, core2_mul2 k hk_pos]
      · intro j hj
        cases j with
        | zero =>
          simp only [collatzIter]
          have hk3 : k ≥ 3 := hall 0 (by omega)
          omega
        | succ j' =>
          simp only [collatzIter]
          rw [hm_eq, collatzStep_double_pos k]
          exact hall j' (by omega)
    else
      have hodd : m % 2 = 1 := by omega
      rw [core2_of_odd m hodd] at hc3 ⊢
      refine ⟨0, rfl, ?_⟩
      intro j hj
      have hj0 : j = 0 := by omega
      subst hj0
      exact hc3

/--
  Theorem W5.2i (`preimage_weight_induces_strict_syracuse_lyapunov` &
  `berg_meinardus_reciprocal_multiterm_laurent_impossibility`, zero custom axioms):
  1. Every positive rational Berg–Meinardus preimage weight `(wNum, wDen)` (`θ ≤ 1`)
     induces strict forward growth `wNum x * wDen (syracuseOddStep x) < wNum (syracuseOddStep x) * wDen x`
     (equivalently, strict Syracuse Lyapunov descent of `V(x) = wDen x / wNum x`) across
     ALL odd `x ≥ 3` with `syracuseOddStep x ≥ 3`.
  2. Consequently, NO reciprocal multi-term `(2, 3)`-adic Laurent valuation sum
     `w(x) = laurentValDen A0 B0 C0 x / evalLaurentSumNum terms x` (`∀ L ≥ 1`) can satisfy
     `IsPositiveRationalPreimageWeight`!
-/
theorem preimage_weight_induces_strict_syracuse_lyapunov
    (wNum wDen : Nat -> Nat) (pTheta qTheta x : Nat)
    (hw : IsPositiveRationalPreimageWeight wNum wDen pTheta qTheta)
    (hx3 : x ≥ 3) (hodd : x % 2 = 1) (hsyr3 : syracuseOddStep x ≥ 3) :
    wNum x * wDen (syracuseOddStep x) < wNum (syracuseOddStep x) * wDen x := by
  let m1 := (3 * x + 1) / 2
  have hm1_pos : m1 > 0 := by dsimp [m1]; omega
  have hstep_x : collatzStep x = m1 := collatzStep_of_odd_nat x hodd
  have hc2_m1 : core2 m1 = syracuseOddStep x := by
    unfold syracuseOddStep
    have h3x : 3 * x + 1 = 2 * m1 := by dsimp [m1]; omega
    rw [h3x, core2_mul2 m1 hm1_pos]
  rcases core2_reaches_by_halving_aux m1 m1 hm1_pos (Nat.le_refl m1) (by rw [hc2_m1]; exact hsyr3) with
    ⟨r, hr_eq, hall_m1⟩
  have hiter_tot : collatzIter (r + 1) x = syracuseOddStep x := by
    simp only [collatzIter]; rw [hstep_x, hr_eq, hc2_m1]
  have hall_x : ∀ j : Nat, j ≤ r + 1 -> collatzIter j x ≥ 3 := by
    intro j hj
    cases j with
    | zero => exact hx3
    | succ j' =>
      simp only [collatzIter]; rw [hstep_x]
      exact hall_m1 j' (by omega)
  have hstrict := (preimage_iter_monotone_and_odd_strict_w5 wNum wDen pTheta qTheta hw
    (r + 1) x hall_x).2 ⟨0, by omega, hodd⟩
  rwa [hiter_tot] at hstrict

theorem berg_meinardus_reciprocal_multiterm_laurent_impossibility
    (terms : List LaurentTerm) (A0 B0 C0 pTheta qTheta : Nat)
    (hnonempty : ∃ t ∈ terms, t.coeff > 0)
    (hw : IsPositiveRationalPreimageWeight
      (laurentValDen A0 B0 C0) (evalLaurentSumNum terms) pTheta qTheta) :
    False := by
  rcases syracuse_multiterm_laurent_valuation_impossibility terms A0 B0 C0 hnonempty with
    ⟨x, hx3, hodd, hsyr3, hnot_desc⟩
  have hstrict := preimage_weight_induces_strict_syracuse_lyapunov
    (laurentValDen A0 B0 C0) (evalLaurentSumNum terms) pTheta qTheta x hw hx3 hodd hsyr3
  rw [Nat.mul_comm (laurentValDen A0 B0 C0 x),
      Nat.mul_comm (laurentValDen A0 B0 C0 (syracuseOddStep x))] at hstrict
  exact hnot_desc hstrict

-- ============================================================================
-- SECTION 3: Front C (`Branch P3.2`, `P3.3`, `P3.4`) — General `∀ m ≥ 1`
--            `m`-Block Brox Spiral Resultants, Global Quotient Mersenne GCD &
--            Mod-3 Parity Bi-Implication, 1-Block Even-Even Impossibility, &
--            Universal Antipodal-Order Divisor Exclusion (Zero Custom Axioms)
-- ============================================================================

def blockWeightSum : List (Nat × Nat) -> Nat
  | [] => 0
  | b :: rest => b.1 + blockWeightSum rest

def blockStepSum : List (Nat × Nat) -> Nat
  | [] => 0
  | b :: rest => (b.1 + b.2) + blockStepSum rest

/--
  General `m`-block (`m ≥ 1`) Brox spiral carry `H_0(blocks)`:
  - `m = 1`: `broxSpiralCarry [(w1, a1)] = 2 ^ a1 - 1`
  - `m = 2`: `broxSpiralCarry [(w1, a1), (w2, a2)] = twoBlockBroxCarry w1 a1 w2 a2`
  - `m ≥ 2`: `broxSpiralCarry (b0 :: b1 :: tail) = 3 ^ W_rest * (2 ^ a0 - 1) + 2 ^ (a0 + w1) * broxSpiralCarry (b1 :: tail)`
-/
def broxSpiralCarry : List (Nat × Nat) -> Nat
  | [] => 0
  | [b0] => 2 ^ b0.2 - 1
  | b0 :: b1 :: tail =>
    3 ^ blockWeightSum (b1 :: tail) * (2 ^ b0.2 - 1) +
      2 ^ (b0.2 + b1.1) * broxSpiralCarry (b1 :: tail)

def rotBlocks (j : Nat) (blocks : List (Nat × Nat)) : List (Nat × Nat) :=
  blocks.drop j ++ blocks.take j

def blockAt (blocks : List (Nat × Nat)) (j : Nat) : Nat × Nat :=
  match blocks.drop j with
  | b :: _ => b
  | [] => (0, 0)

def natAt (xs : List Nat) (j : Nat) : Nat :=
  match xs.drop j with
  | x :: _ => x
  | [] => 0

def natListGcd : List Nat -> Nat
  | [] => 0
  | x :: xs => Nat.gcd x (natListGcd xs)

theorem broxSpiralCarry_singleton (w1 a1 : Nat) :
    broxSpiralCarry [(w1, a1)] = 2 ^ a1 - 1 := rfl

theorem broxSpiralCarry_pair_eq_twoBlock (w1 a1 w2 a2 : Nat) :
    broxSpiralCarry [(w1, a1), (w2, a2)] = twoBlockBroxCarry w1 a1 w2 a2 := by
  simp [broxSpiralCarry, blockWeightSum, twoBlockBroxCarry]

theorem blockWeightSum_append :
    ∀ (xs ys : List (Nat × Nat)),
      blockWeightSum (xs ++ ys) = blockWeightSum xs + blockWeightSum ys
  | [], _ => by simp [blockWeightSum]
  | b :: rest, ys => by
    simp only [List.cons_append, blockWeightSum, blockWeightSum_append rest ys, Nat.add_assoc]

theorem blockStepSum_append :
    ∀ (xs ys : List (Nat × Nat)),
      blockStepSum (xs ++ ys) = blockStepSum xs + blockStepSum ys
  | [], _ => by simp [blockStepSum]
  | b :: rest, ys => by
    simp only [List.cons_append, blockStepSum, blockStepSum_append rest ys, Nat.add_assoc]

theorem blockSums_rotBlocks (j : Nat) (blocks : List (Nat × Nat)) :
    blockWeightSum (rotBlocks j blocks) = blockWeightSum blocks ∧
    blockStepSum (rotBlocks j blocks) = blockStepSum blocks := by
  unfold rotBlocks
  have hsplit : blocks.take j ++ blocks.drop j = blocks := List.take_append_drop j blocks
  have hw := blockWeightSum_append (blocks.take j) (blocks.drop j)
  have hs := blockStepSum_append (blocks.take j) (blocks.drop j)
  rw [hsplit] at hw hs
  rw [blockWeightSum_append, blockStepSum_append]
  exact ⟨by omega, by omega⟩

theorem broxSpiralCarry_append_singleton (b0 : Nat × Nat) :
    ∀ (b1 : Nat × Nat) (tail : List (Nat × Nat)),
      broxSpiralCarry ((b1 :: tail) ++ [b0]) =
        3 ^ b0.1 * broxSpiralCarry (b1 :: tail) +
          2 ^ (b1.2 + blockStepSum tail + b0.1) * (2 ^ b0.2 - 1)
  | b1, [] => by
    simp [broxSpiralCarry, blockWeightSum, blockStepSum]
  | b1, b2 :: rest => by
    have hcons : ((b1 :: b2 :: rest) ++ [b0]) = b1 :: b2 :: (rest ++ [b0]) := rfl
    rw [hcons]
    simp only [broxSpiralCarry]
    have hw_app : blockWeightSum (b2 :: (rest ++ [b0])) =
        b0.1 + blockWeightSum (b2 :: rest) := by
      change blockWeightSum ((b2 :: rest) ++ [b0]) = _
      rw [blockWeightSum_append]
      simp only [blockWeightSum, Nat.add_zero]
      omega
    have ih := broxSpiralCarry_append_singleton b0 b2 rest
    change broxSpiralCarry (b2 :: (rest ++ [b0])) = _ at ih
    rw [hw_app, Nat.pow_add 3 b0.1, ih, Nat.mul_add]
    have h1 : (3 ^ b0.1 * 3 ^ blockWeightSum (b2 :: rest)) * (2 ^ b1.2 - 1) =
        3 ^ b0.1 * (3 ^ blockWeightSum (b2 :: rest) * (2 ^ b1.2 - 1)) :=
      Nat.mul_assoc _ _ _
    have h2 : 2 ^ (b1.2 + b2.1) * (3 ^ b0.1 * broxSpiralCarry (b2 :: rest)) =
        3 ^ b0.1 * (2 ^ (b1.2 + b2.1) * broxSpiralCarry (b2 :: rest)) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ (b1.2 + b2.1)) (3 ^ b0.1), Nat.mul_assoc]
    have h3 : 2 ^ (b1.2 + b2.1) * (2 ^ (b2.2 + blockStepSum rest + b0.1) * (2 ^ b0.2 - 1)) =
        2 ^ (b1.2 + blockStepSum (b2 :: rest) + b0.1) * (2 ^ b0.2 - 1) := by
      rw [← Nat.mul_assoc, ← Nat.pow_add]
      have hexp : (b1.2 + b2.1) + (b2.2 + blockStepSum rest + b0.1) =
          b1.2 + blockStepSum (b2 :: rest) + b0.1 := by
        simp only [blockStepSum]; omega
      rw [hexp]
    rw [h1, h2, h3, ← Nat.add_assoc, ← Nat.mul_add (3 ^ b0.1)]

def nextBlockWeight (b0 : Nat × Nat) : List (Nat × Nat) -> Nat
  | [] => b0.1
  | b1 :: _ => b1.1

theorem broxSpiralCarry_head_resultant (b0 : Nat × Nat) (rest : List (Nat × Nat))
    (hgt : 3 ^ blockWeightSum (b0 :: rest) < 2 ^ blockStepSum (b0 :: rest)) :
    let D := 2 ^ blockStepSum (b0 :: rest) - 3 ^ blockWeightSum (b0 :: rest)
    2 ^ (b0.2 + nextBlockWeight b0 rest) * broxSpiralCarry (rest ++ [b0]) =
      3 ^ b0.1 * broxSpiralCarry (b0 :: rest) + D * (2 ^ b0.2 - 1) := by
  dsimp only
  cases rest with
  | nil =>
    simp only [nextBlockWeight, List.nil_append, broxSpiralCarry, blockWeightSum, blockStepSum,
               Nat.add_zero] at hgt ⊢
    have hcomm : b0.2 + b0.1 = b0.1 + b0.2 := Nat.add_comm _ _
    rw [hcomm, ← Nat.add_mul (3 ^ b0.1) (2 ^ (b0.1 + b0.2) - 3 ^ b0.1)]
    have hsub : 3 ^ b0.1 + (2 ^ (b0.1 + b0.2) - 3 ^ b0.1) = 2 ^ (b0.1 + b0.2) := by omega
    rw [hsub]
  | cons b1 tail =>
    simp only [nextBlockWeight]
    rw [broxSpiralCarry_append_singleton b0 b1 tail, Nat.mul_add]
    have h1 : 2 ^ (b0.2 + b1.1) * (3 ^ b0.1 * broxSpiralCarry (b1 :: tail)) =
        3 ^ b0.1 * (2 ^ (b0.2 + b1.1) * broxSpiralCarry (b1 :: tail)) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ (b0.2 + b1.1)) (3 ^ b0.1), Nat.mul_assoc]
    have h2 : 2 ^ (b0.2 + b1.1) * (2 ^ (b1.2 + blockStepSum tail + b0.1) * (2 ^ b0.2 - 1)) =
        2 ^ blockStepSum (b0 :: b1 :: tail) * (2 ^ b0.2 - 1) := by
      rw [← Nat.mul_assoc, ← Nat.pow_add]
      have hexp : (b0.2 + b1.1) + (b1.2 + blockStepSum tail + b0.1) =
          blockStepSum (b0 :: b1 :: tail) := by
        simp only [blockStepSum]; omega
      rw [hexp]
    rw [h1, h2]
    have hsplit_2K : 2 ^ blockStepSum (b0 :: b1 :: tail) =
        3 ^ blockWeightSum (b0 :: b1 :: tail) +
          (2 ^ blockStepSum (b0 :: b1 :: tail) - 3 ^ blockWeightSum (b0 :: b1 :: tail)) := by
      omega
    conv => lhs; rhs; rw [hsplit_2K]
    rw [Nat.add_mul]
    have hp3 : 3 ^ blockWeightSum (b0 :: b1 :: tail) * (2 ^ b0.2 - 1) =
        3 ^ b0.1 * (3 ^ blockWeightSum (b1 :: tail) * (2 ^ b0.2 - 1)) := by
      simp only [blockWeightSum]
      rw [Nat.pow_add 3 b0.1, Nat.mul_assoc]
    rw [hp3]
    simp only [broxSpiralCarry]
    rw [Nat.mul_add (3 ^ b0.1)]
    omega

theorem drop_eq_cons_blockAt :
    ∀ (blocks : List (Nat × Nat)) (j : Nat),
      j < blocks.length ->
      blocks.drop j = blockAt blocks j :: blocks.drop (j + 1)
  | [], _, hj => by simp at hj
  | b :: _, 0, _ => by simp [blockAt]
  | _ :: rest, j + 1, hj => by
    simp only [List.length_cons] at hj
    have ih := drop_eq_cons_blockAt rest j (by omega)
    simpa [blockAt] using ih

theorem take_succ_eq_append_blockAt :
    ∀ (blocks : List (Nat × Nat)) (j : Nat),
      j < blocks.length ->
      blocks.take (j + 1) = blocks.take j ++ [blockAt blocks j]
  | [], _, hj => by simp at hj
  | b :: _, 0, _ => by simp [blockAt]
  | b :: rest, j + 1, hj => by
    simp only [List.length_cons] at hj
    simp only [List.take_succ_cons, List.cons_append]
    exact congrArg (List.cons b) (take_succ_eq_append_blockAt rest j (by omega))

theorem rotBlocks_step_decomp (blocks : List (Nat × Nat)) (j : Nat)
    (hj : j < blocks.length) :
    let m := blocks.length
    let jNext := (j + 1) % m
    let bj := blockAt blocks j
    let rest := blocks.drop (j + 1) ++ blocks.take j
    rotBlocks j blocks = bj :: rest ∧
    rotBlocks jNext blocks = rest ++ [bj] ∧
    nextBlockWeight bj rest = (blockAt blocks jNext).1 := by
  dsimp only
  let m := blocks.length
  have hm_pos : m ≥ 1 := by dsimp [m]; omega
  have hrot_j : rotBlocks j blocks = blockAt blocks j :: (blocks.drop (j + 1) ++ blocks.take j) := by
    unfold rotBlocks
    rw [drop_eq_cons_blockAt blocks j hj, List.cons_append]
  by_cases hlt : j + 1 < m
  · have hmod : (j + 1) % m = j + 1 := Nat.mod_eq_of_lt hlt
    rw [hmod]
    have hrot_next : rotBlocks (j + 1) blocks =
        (blocks.drop (j + 1) ++ blocks.take j) ++ [blockAt blocks j] := by
      unfold rotBlocks
      rw [take_succ_eq_append_blockAt blocks j hj, List.append_assoc]
    have hhead : nextBlockWeight (blockAt blocks j) (blocks.drop (j + 1) ++ blocks.take j) =
        (blockAt blocks (j + 1)).1 := by
      rw [drop_eq_cons_blockAt blocks (j + 1) hlt, List.cons_append]
      rfl
    exact ⟨hrot_j, hrot_next, hhead⟩
  · have heq_m : j + 1 = m := by dsimp [m] at hlt ⊢; omega
    have hmod : (j + 1) % m = 0 := by rw [heq_m, Nat.mod_self]
    rw [hmod]
    have hdrop_nil : blocks.drop (j + 1) = [] := by
      rw [heq_m]; exact List.drop_length
    have htake_full : blocks.take (j + 1) = blocks := by
      rw [heq_m]; exact List.take_length
    have hblocks_eq : blocks = blocks.take j ++ [blockAt blocks j] := by
      exact htake_full.symm.trans (take_succ_eq_append_blockAt blocks j hj)
    have hrot0 : rotBlocks 0 blocks = (blocks.drop (j + 1) ++ blocks.take j) ++ [blockAt blocks j] := by
      rw [hdrop_nil, List.nil_append]
      unfold rotBlocks
      simp only [List.drop_zero, List.take_zero, List.append_nil]
      exact hblocks_eq
    have hhead : nextBlockWeight (blockAt blocks j) (blocks.drop (j + 1) ++ blocks.take j) =
        (blockAt blocks 0).1 := by
      rw [hdrop_nil, List.nil_append]
      conv => rhs; unfold blockAt; simp only [List.drop_zero]; rw [hblocks_eq]
      cases blocks.take j with
      | nil => rfl
      | cons b1 _ => rfl
    exact ⟨hrot_j, hrot0, hhead⟩

theorem natListGcd_dvd_mem :
    ∀ (xs : List Nat) (x : Nat), x ∈ xs -> natListGcd xs ∣ x
  | [], _, hm => by cases hm
  | y :: ys, x, hm => by
    simp only [natListGcd]
    cases hm with
    | head _ => exact Nat.gcd_dvd_left y (natListGcd ys)
    | tail _ hmem => exact Nat.dvd_trans (Nat.gcd_dvd_right y (natListGcd ys)) (natListGcd_dvd_mem ys x hmem)

theorem natListGcd_dvd_natAt :
    ∀ (xs : List Nat) (j : Nat), j < xs.length -> natListGcd xs ∣ natAt xs j
  | [], _, hj => by simp at hj
  | x :: _, 0, _ => by simp [natAt, natListGcd, Nat.gcd_dvd_left]
  | x :: xs, j + 1, hj => by
    simp only [List.length_cons] at hj
    simp only [natAt, List.drop_succ_cons, natListGcd]
    exact Nat.dvd_trans (Nat.gcd_dvd_right x (natListGcd xs)) (natListGcd_dvd_natAt xs j (by omega))

theorem dvd_natListGcd_of_forall :
    ∀ (g : Nat) (xs : List Nat), (∀ x ∈ xs, g ∣ x) -> g ∣ natListGcd xs
  | _, [], _ => Nat.dvd_zero _
  | g, x :: xs, hall => by
    simp only [natListGcd]
    exact Nat.dvd_gcd (hall x (List.Mem.head _))
      (dvd_natListGcd_of_forall g xs (fun y hy => hall y (List.mem_cons_of_mem _ hy)))

theorem mem_iff_exists_blockAt :
    ∀ (blocks : List (Nat × Nat)) (b : Nat × Nat),
      b ∈ blocks -> ∃ j : Nat, j < blocks.length ∧ blockAt blocks j = b
  | [], _, hm => by cases hm
  | hd :: rest, b, hm => by
    cases hm with
    | head _ => exact ⟨0, by simp, rfl⟩
    | tail _ hmem =>
      rcases mem_iff_exists_blockAt rest b hmem with ⟨j, hj, hbj⟩
      exact ⟨j + 1, by simp; omega, hbj⟩

theorem pow2_sub_one_div3_iff_even_full : ∀ a : Nat,
    (2 ^ a - 1) % 3 = 0 ↔ a % 2 = 0
  | 0 => ⟨fun _ => rfl, fun _ => rfl⟩
  | 1 => ⟨fun h => by omega, fun h => by omega⟩
  | a + 2 => by
    have hp : 2 ^ (a + 2) = 4 * 2 ^ a := by
      rw [Nat.pow_succ, Nat.pow_succ]; omega
    have hp0 := pow2_pos_nat a
    have ih := pow2_sub_one_div3_iff_even_full a
    constructor
    · intro h
      have hrem : (2 ^ a - 1) % 3 = 0 := by omega
      have ha_ev := ih.mp hrem
      omega
    · intro hev
      have ha_ev : a % 2 = 0 := by omega
      have hrem := ih.mpr ha_ev
      omega

theorem pow2_mul_div3_imp_div3 : ∀ (e q : Nat),
    (2 ^ e * q) % 3 = 0 -> q % 3 = 0
  | 0, q, h => by simpa using h
  | e + 1, q, h => by
    have hmul : 2 ^ (e + 1) * q = 2 ^ e * (2 * q) := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    rw [hmul] at h
    have h2q := pow2_mul_div3_imp_div3 e (2 * q) h
    omega

/--
  Theorem W5.3a (`m_block_brox_resultant_and_quotient_locks`, zero custom axioms):
  Universal `∀ m ≥ 1` `m`-Block Brox Spiral Resultant Identity, Global Quotient
  Mersenne GCD Lock, & Exact Cyclic Mod-3 Parity Bi-Implication (generalizing
  Wave 4 Theorems `W4.3a` and `W4.3b` from `m = 2` to ALL `m ≥ 1`):
  For EVERY nonempty list `blocks` of `m = blocks.length ≥ 1` blocks `(w_j, a_j)`
  with `w_j ≥ 1, a_j ≥ 1` and `3 ^ W < 2 ^ K` (`D := 2 ^ K - 3 ^ W`):
  1. Universal adjacent resultant elimination (`∀ j < m`, `jNext := (j + 1) % m`):
     `2 ^ (a_j + w_{jNext}) * H_{jNext} = 3 ^ w_j * H_j + D * (2 ^ a_j - 1)`.
  2. Whenever `qs : List Nat` (`qs.length = m`) satisfies `∀ j < m, D * qs[j] = H_j`:
     - Exact linear quotient recurrence: `2 ^ (a_j + w_{jNext}) * qs[jNext] = 3 ^ w_j * qs[j] + (2 ^ a_j - 1)`;
     - Global Mersenne GCD lock: `natListGcd qs ∣ natListGcd (blocks.map (fun b => 2 ^ b.2 - 1))`;
     - Unit-even-run primitivity: `(∃ b ∈ blocks, b.2 = 1) -> natListGcd qs = 1`;
     - Exact cyclic mod-3 bi-implication: `∀ j < m, (qs[jNext] % 3 = 0 ↔ a_j % 2 = 0)`.
-/
theorem m_block_brox_resultant_and_quotient_locks
    (blocks : List (Nat × Nat))
    (hm_pos : blocks.length ≥ 1)
    (hblocks_pos : ∀ b ∈ blocks, b.1 ≥ 1 ∧ b.2 ≥ 1)
    (hgt : 3 ^ blockWeightSum blocks < 2 ^ blockStepSum blocks) :
    let m := blocks.length
    let D := 2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks
    (∀ j : Nat, j < m ->
      let jNext := (j + 1) % m
      let bj := blockAt blocks j
      let bNext := blockAt blocks jNext
      2 ^ (bj.2 + bNext.1) * broxSpiralCarry (rotBlocks jNext blocks) =
        3 ^ bj.1 * broxSpiralCarry (rotBlocks j blocks) + D * (2 ^ bj.2 - 1)) ∧
    (∀ qs : List Nat,
      qs.length = m ->
      (∀ j : Nat, j < m -> D * natAt qs j = broxSpiralCarry (rotBlocks j blocks)) ->
      (∀ j : Nat, j < m ->
        let jNext := (j + 1) % m
        let bj := blockAt blocks j
        let bNext := blockAt blocks jNext
        2 ^ (bj.2 + bNext.1) * natAt qs jNext = 3 ^ bj.1 * natAt qs j + (2 ^ bj.2 - 1)) ∧
      natListGcd qs ∣ natListGcd (blocks.map (fun b => 2 ^ b.2 - 1)) ∧
      ((∃ b ∈ blocks, b.2 = 1) -> natListGcd qs = 1) ∧
      (∀ j : Nat, j < m -> (natAt qs ((j + 1) % m) % 3 = 0 ↔ (blockAt blocks j).2 % 2 = 0))) := by
  dsimp only
  let m := blocks.length
  let D := 2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks
  have hD_pos : D > 0 := by dsimp [D]; omega
  have hblockAt_mem : ∀ j : Nat, j < m -> blockAt blocks j ∈ blocks := by
    have haux : ∀ (bs : List (Nat × Nat)) (i : Nat), i < bs.length -> blockAt bs i ∈ bs := by
      intro bs
      induction bs with
      | nil => intro _ hi; simp at hi
      | cons hd tl ih =>
        intro i hi
        cases i with
        | zero => exact List.Mem.head _
        | succ i' =>
          simp only [List.length_cons] at hi
          exact List.mem_cons_of_mem _ (ih i' (by omega))
    exact fun j hj => haux blocks j hj
  have hres : ∀ j : Nat, j < m ->
      2 ^ ((blockAt blocks j).2 + (blockAt blocks ((j + 1) % m)).1) *
        broxSpiralCarry (rotBlocks ((j + 1) % m) blocks) =
      3 ^ (blockAt blocks j).1 * broxSpiralCarry (rotBlocks j blocks) +
        D * (2 ^ (blockAt blocks j).2 - 1) := by
    intro j hj
    rcases rotBlocks_step_decomp blocks j hj with ⟨hrot_j, hrot_next, hhead⟩
    rcases blockSums_rotBlocks j blocks with ⟨hw_rot, hs_rot⟩
    rw [hrot_j] at hw_rot hs_rot
    have hgt_rot : 3 ^ blockWeightSum (blockAt blocks j :: (blocks.drop (j + 1) ++ blocks.take j)) <
        2 ^ blockStepSum (blockAt blocks j :: (blocks.drop (j + 1) ++ blocks.take j)) := by
      rwa [hw_rot, hs_rot]
    have hhr := broxSpiralCarry_head_resultant (blockAt blocks j)
      (blocks.drop (j + 1) ++ blocks.take j) hgt_rot
    dsimp only at hhr
    rw [hw_rot, hs_rot, hhead, ← hrot_j, ← hrot_next] at hhr
    exact hhr
  refine ⟨hres, ?_⟩
  intro qs hq_len hqs_eq
  have hq_rec : ∀ j : Nat, j < m ->
      2 ^ ((blockAt blocks j).2 + (blockAt blocks ((j + 1) % m)).1) * natAt qs ((j + 1) % m) =
        3 ^ (blockAt blocks j).1 * natAt qs j + (2 ^ (blockAt blocks j).2 - 1) := by
    intro j hj
    have hjNext : (j + 1) % m < m := Nat.mod_lt (j + 1) hm_pos
    have hr := hres j hj
    rw [← hqs_eq j hj, ← hqs_eq ((j + 1) % m) hjNext] at hr
    apply nat_mul_left_cancel_pos D _ _ hD_pos
    calc
      D * (2 ^ ((blockAt blocks j).2 + (blockAt blocks ((j + 1) % m)).1) * natAt qs ((j + 1) % m))
          = 2 ^ ((blockAt blocks j).2 + (blockAt blocks ((j + 1) % m)).1) *
              (D * natAt qs ((j + 1) % m)) := by
            rw [← Nat.mul_assoc, Nat.mul_comm D, Nat.mul_assoc]
      _ = 3 ^ (blockAt blocks j).1 * (D * natAt qs j) + D * (2 ^ (blockAt blocks j).2 - 1) := hr
      _ = D * (3 ^ (blockAt blocks j).1 * natAt qs j + (2 ^ (blockAt blocks j).2 - 1)) := by
            rw [← Nat.mul_assoc (3 ^ (blockAt blocks j).1) D,
                Nat.mul_comm (3 ^ (blockAt blocks j).1) D, Nat.mul_assoc, ← Nat.mul_add]
  have hdvd_each : ∀ j : Nat, j < m -> natListGcd qs ∣ (2 ^ (blockAt blocks j).2 - 1) := by
    intro j hj
    have hjNext : (j + 1) % m < m := Nat.mod_lt (j + 1) hm_pos
    have hg_j : natListGcd qs ∣ natAt qs j :=
      natListGcd_dvd_natAt qs j (by omega)
    have hg_next : natListGcd qs ∣ natAt qs ((j + 1) % m) :=
      natListGcd_dvd_natAt qs ((j + 1) % m) (by omega)
    have hrec_j := hq_rec j hj
    have hsub : 2 ^ (blockAt blocks j).2 - 1 =
        2 ^ ((blockAt blocks j).2 + (blockAt blocks ((j + 1) % m)).1) * natAt qs ((j + 1) % m) -
          3 ^ (blockAt blocks j).1 * natAt qs j := by omega
    rw [hsub]
    apply Nat.dvd_sub
    · rcases hg_next with ⟨k1, hk1⟩
      exact ⟨2 ^ ((blockAt blocks j).2 + (blockAt blocks ((j + 1) % m)).1) * k1,
        by rw [hk1, ← Nat.mul_assoc, Nat.mul_comm _ (natListGcd qs), Nat.mul_assoc]⟩
    · rcases hg_j with ⟨k0, hk0⟩
      exact ⟨3 ^ (blockAt blocks j).1 * k0,
        by rw [hk0, ← Nat.mul_assoc, Nat.mul_comm _ (natListGcd qs), Nat.mul_assoc]⟩
  have hg_mersenne : natListGcd qs ∣ natListGcd (blocks.map (fun b => 2 ^ b.2 - 1)) := by
    apply dvd_natListGcd_of_forall
    intro x hx
    rcases List.mem_map.mp hx with ⟨b, hb_mem, rfl⟩
    rcases mem_iff_exists_blockAt blocks b hb_mem with ⟨j, hj, hbj⟩
    rw [← hbj]
    exact hdvd_each j hj
  have hunit : (∃ b ∈ blocks, b.2 = 1) -> natListGcd qs = 1 := by
    rintro ⟨b, hb_mem, hb1⟩
    rcases mem_iff_exists_blockAt blocks b hb_mem with ⟨j, hj, hbj⟩
    have hd := hdvd_each j hj
    rw [hbj, hb1, Nat.pow_one] at hd
    exact Nat.eq_one_of_dvd_one hd
  have hmod3_iff : ∀ j : Nat, j < m ->
      (natAt qs ((j + 1) % m) % 3 = 0 ↔ (blockAt blocks j).2 % 2 = 0) := by
    intro j hj
    have hrec_j := hq_rec j hj
    have hbj_pos := hblocks_pos (blockAt blocks j) (hblockAt_mem j hj)
    have hp3_div3 : (3 ^ (blockAt blocks j).1 * natAt qs j) % 3 = 0 := by
      cases hw_c : (blockAt blocks j).1 with
      | zero => omega
      | succ w' =>
        rw [Nat.pow_succ, Nat.mul_comm (3 ^ w') 3, Nat.mul_assoc, Nat.mul_mod,
            Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
    constructor
    · intro hq3
      have hlhs3 : (2 ^ ((blockAt blocks j).2 + (blockAt blocks ((j + 1) % m)).1) *
          natAt qs ((j + 1) % m)) % 3 = 0 := by
        rw [Nat.mul_mod, hq3, Nat.mul_zero, Nat.zero_mod]
      have ha3 : (2 ^ (blockAt blocks j).2 - 1) % 3 = 0 := by
        have hm3 := congrArg (fun z => z % 3) hrec_j
        rw [hlhs3, Nat.add_mod, hp3_div3, Nat.zero_add, Nat.mod_mod] at hm3
        exact hm3.symm
      exact (pow2_sub_one_div3_iff_even_full (blockAt blocks j).2).mp ha3
    · intro ha_ev
      have ha3 : (2 ^ (blockAt blocks j).2 - 1) % 3 = 0 :=
        (pow2_sub_one_div3_iff_even_full (blockAt blocks j).2).mpr ha_ev
      have hlhs3 : (2 ^ ((blockAt blocks j).2 + (blockAt blocks ((j + 1) % m)).1) *
          natAt qs ((j + 1) % m)) % 3 = 0 := by
        rw [hrec_j, Nat.add_mod, hp3_div3, ha3]
      exact pow2_mul_div3_imp_div3 _ _ hlhs3
  exact ⟨hq_rec, hg_mersenne, hunit, hmod3_iff⟩

/-- Parity word `1^{w_0} 0^{a_0} ... 1^{w_{m-1}} 0^{a_{m-1}}` of an `m`-block spiral tuple -/
def spiralBlocksToParity : List (Nat × Nat) -> List Bool
  | [] => []
  | b :: rest => (List.replicate b.1 true ++ List.replicate b.2 false) ++ spiralBlocksToParity rest

theorem spiralBlocksToParity_len_and_weight :
    ∀ blocks : List (Nat × Nat),
      (spiralBlocksToParity blocks).length = blockStepSum blocks ∧
      parityWeight (spiralBlocksToParity blocks) = blockWeightSum blocks
  | [] => ⟨rfl, rfl⟩
  | b :: rest => by
    rcases spiralBlocksToParity_len_and_weight rest with ⟨hl, hw⟩
    dsimp only [spiralBlocksToParity, blockStepSum, blockWeightSum]
    rw [List.length_append, List.length_append, List.length_replicate, List.length_replicate,
        parityWeight_append, parityWeight_append, parityWeight_replicate_true_local,
        parityWeight_replicate_false, Nat.add_zero, hl, hw]
    exact ⟨rfl, rfl⟩

theorem affineCarry_single_spiral_block (w a : Nat) :
    affineCarry (List.replicate w true ++ List.replicate a false) = 3 ^ w - 2 ^ w := by
  rw [(affineCarry_append_replicate_false (List.replicate w true) a).2]
  have hc := affineCarry_replicate_true_local w
  omega

/--
  Theorem W5.3a' (`broxSpiralCarry_eq_affineCarry_universal`, zero custom axioms):
  Universal `∀ m ≥ 1` Exact Algebraic Bridge from `broxSpiralCarry` to `affineCarry`:
  For EVERY head block `b0 = (w0, a0)` and tail `rest : List (Nat × Nat)` (`m = rest.length + 1 ≥ 1`),
    `2 ^ w0 * broxSpiralCarry (b0 :: rest) + 3 ^ W = 2 ^ K + affineCarry (spiralBlocksToParity (b0 :: rest))`.
-/
theorem broxSpiralCarry_eq_affineCarry_universal :
    ∀ (b0 : Nat × Nat) (rest : List (Nat × Nat)),
      2 ^ b0.1 * broxSpiralCarry (b0 :: rest) + 3 ^ blockWeightSum (b0 :: rest) =
        2 ^ blockStepSum (b0 :: rest) + affineCarry (spiralBlocksToParity (b0 :: rest))
  | b0, [] => by
    simp only [broxSpiralCarry, blockWeightSum, blockStepSum, spiralBlocksToParity,
               List.append_nil, Nat.add_zero]
    rw [affineCarry_single_spiral_block b0.1 b0.2]
    have h2le3 : 2 ^ b0.1 ≤ 3 ^ b0.1 := pow2_le_pow3 b0.1
    have hp2a : 2 ^ b0.2 ≥ 1 := pow2_pos_nat b0.2
    have hmul : 2 ^ b0.1 * (2 ^ b0.2 - 1) + 2 ^ b0.1 = 2 ^ (b0.1 + b0.2) := by
      calc
        2 ^ b0.1 * (2 ^ b0.2 - 1) + 2 ^ b0.1
            = 2 ^ b0.1 * ((2 ^ b0.2 - 1) + 1) := by
              conv => lhs; rhs; rw [← Nat.mul_one (2 ^ b0.1)]
              rw [← Nat.mul_add]
        _ = 2 ^ (b0.1 + b0.2) := by rw [Nat.sub_add_cancel hp2a, Nat.pow_add]
    omega
  | b0, b1 :: tail => by
    have ih := broxSpiralCarry_eq_affineCarry_universal b1 tail
    let rest := b1 :: tail
    let W_rest := blockWeightSum rest
    let K_rest := blockStepSum rest
    let v_rest := spiralBlocksToParity rest
    change 2 ^ b1.1 * broxSpiralCarry rest + 3 ^ W_rest = 2 ^ K_rest + affineCarry v_rest at ih
    have hpar_eq : spiralBlocksToParity (b0 :: rest) =
        (List.replicate b0.1 true ++ List.replicate b0.2 false) ++ v_rest := rfl
    rw [hpar_eq, affineCarry_append]
    have hw_rest_eq : parityWeight v_rest = W_rest :=
      (spiralBlocksToParity_len_and_weight rest).2
    have hlen_b0 : (List.replicate b0.1 true ++ List.replicate b0.2 false).length =
        b0.1 + b0.2 := by rw [List.length_append, List.length_replicate, List.length_replicate]
    rw [hw_rest_eq, hlen_b0, affineCarry_single_spiral_block b0.1 b0.2]
    simp only [broxSpiralCarry]
    have hw_tot : blockWeightSum (b0 :: rest) = b0.1 + W_rest := rfl
    have hk_tot : blockStepSum (b0 :: rest) = (b0.1 + b0.2) + K_rest := rfl
    rw [hw_tot, hk_tot, Nat.pow_add 3 b0.1 W_rest, Nat.pow_add 2 (b0.1 + b0.2) K_rest]
    have h2le3 : 2 ^ b0.1 ≤ 3 ^ b0.1 := pow2_le_pow3 b0.1
    have hp2a : 2 ^ b0.2 ≥ 1 := pow2_pos_nat b0.2
    have hlhs1 : 2 ^ b0.1 * (3 ^ W_rest * (2 ^ b0.2 - 1) + 2 ^ (b0.2 + b1.1) * broxSpiralCarry rest) =
        (2 ^ b0.1 * (2 ^ b0.2 - 1)) * 3 ^ W_rest +
          2 ^ (b0.1 + b0.2) * (2 ^ b1.1 * broxSpiralCarry rest) := by
      rw [Nat.mul_add]
      have t1 : 2 ^ b0.1 * (3 ^ W_rest * (2 ^ b0.2 - 1)) =
          (2 ^ b0.1 * (2 ^ b0.2 - 1)) * 3 ^ W_rest := by
        rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ b0.1) (3 ^ W_rest),
            Nat.mul_assoc, Nat.mul_comm (3 ^ W_rest)]
      have t2 : 2 ^ b0.1 * (2 ^ (b0.2 + b1.1) * broxSpiralCarry rest) =
          2 ^ (b0.1 + b0.2) * (2 ^ b1.1 * broxSpiralCarry rest) := by
        rw [Nat.pow_add 2 b0.2 b1.1, Nat.mul_assoc (2 ^ b0.2) (2 ^ b1.1),
            ← Nat.mul_assoc (2 ^ b0.1) (2 ^ b0.2), ← Nat.pow_add 2 b0.1 b0.2]
      rw [t1, t2]
    have h2a_sub : 2 ^ b0.1 * (2 ^ b0.2 - 1) + 2 ^ b0.1 = 2 ^ (b0.1 + b0.2) := by
      calc
        2 ^ b0.1 * (2 ^ b0.2 - 1) + 2 ^ b0.1
            = 2 ^ b0.1 * ((2 ^ b0.2 - 1) + 1) := by
              conv => lhs; rhs; rw [← Nat.mul_one (2 ^ b0.1)]
              rw [← Nat.mul_add]
        _ = 2 ^ (b0.1 + b0.2) := by rw [Nat.sub_add_cancel hp2a, Nat.pow_add]
    have hsub3 : 3 ^ W_rest * (3 ^ b0.1 - 2 ^ b0.1) + 2 ^ b0.1 * 3 ^ W_rest =
        3 ^ b0.1 * 3 ^ W_rest := by
      rw [Nat.mul_comm (2 ^ b0.1) (3 ^ W_rest), ← Nat.mul_add,
          Nat.sub_add_cancel h2le3, Nat.mul_comm]
    have hmul_a : (2 ^ b0.1 * (2 ^ b0.2 - 1)) * 3 ^ W_rest + 2 ^ b0.1 * 3 ^ W_rest =
        2 ^ (b0.1 + b0.2) * 3 ^ W_rest := by
      rw [← Nat.add_mul, h2a_sub]
    have hmul_ih : 2 ^ (b0.1 + b0.2) * (2 ^ b1.1 * broxSpiralCarry rest + 3 ^ W_rest) =
        2 ^ (b0.1 + b0.2) * 2 ^ K_rest + 2 ^ (b0.1 + b0.2) * affineCarry v_rest := by
      rw [ih, Nat.mul_add]
    rw [Nat.mul_add (2 ^ (b0.1 + b0.2))] at hmul_ih
    rw [hlhs1]
    omega

theorem odd_dvd_pow2_mul_cancel_w5 (D : Nat) (hodd : D % 2 = 1) :
    ∀ (e H : Nat), D ∣ (2 ^ e * H) -> D ∣ H
  | 0, H, hdvd => by simpa using hdvd
  | e + 1, H, hdvd => by
    have hmul : 2 ^ (e + 1) * H = 2 ^ e * (2 * H) := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    rw [hmul] at hdvd
    rcases odd_dvd_pow2_mul_cancel_w5 D hodd e (2 * H) hdvd with ⟨k, hk⟩
    have hk_ev : k % 2 = 0 := by
      have hm2 := congrArg (fun z => z % 2) hk
      rw [Nat.mul_mod D k 2, hodd, Nat.one_mul, Nat.mod_mod] at hm2
      omega
    have hk2 : k = 2 * (k / 2) := by omega
    rw [hk2, ← Nat.mul_assoc D 2 (k / 2), Nat.mul_comm D 2, Nat.mul_assoc 2 D (k / 2)] at hk
    exact ⟨k / 2, by omega⟩

def buildBroxQuotientsAux (D : Nat) (blocks : List (Nat × Nat)) : Nat -> Nat -> List Nat
  | _, 0 => []
  | i, rem + 1 =>
    (broxSpiralCarry (rotBlocks i blocks) / D) :: buildBroxQuotientsAux D blocks (i + 1) rem

theorem buildBroxQuotientsAux_spec (D : Nat) (blocks : List (Nat × Nat)) :
    ∀ (rem i : Nat),
      (buildBroxQuotientsAux D blocks i rem).length = rem ∧
      (∀ j : Nat, j < rem ->
        natAt (buildBroxQuotientsAux D blocks i rem) j =
          broxSpiralCarry (rotBlocks (i + j) blocks) / D)
  | 0, _ => ⟨rfl, fun _ hj => by omega⟩
  | rem + 1, i => by
    rcases buildBroxQuotientsAux_spec D blocks rem (i + 1) with ⟨hlen, hat⟩
    dsimp only [buildBroxQuotientsAux]
    rw [List.length_cons, hlen]
    refine ⟨rfl, ?_⟩
    intro j hj
    cases j with
    | zero => simp [natAt]
    | succ j' =>
      change natAt (buildBroxQuotientsAux D blocks (i + 1) rem) j' = _
      rw [hat j' (by omega), show i + 1 + j' = i + (j' + 1) by omega]

/--
  Theorem W5.3a'' (`m_block_cycle_induces_brox_quotients`, zero custom axioms):
  1. Single-Vertex Divisibility Propagation (`∀ m ≥ 1`): Whenever `D := 2^K - 3^W > 0`
     divides JUST `H_0 = broxSpiralCarry blocks`, `D` (being odd!) automatically divides
     `broxSpiralCarry (rotBlocks j blocks)` across ALL `0 ≤ j < m`, constructing the exact
     `m`-tuple `qs : List Nat` satisfying ALL four resultant/GCD/mod-3 locks of `W5.3a`!
  2. True Collatz Cycle Bridge (`∀ m ≥ 1`): Whenever any integer `x0 : Nat` satisfies the
     Böhm–Sontacchi `m`-block cycle equation `(2^K - 3^W) * x0 = affineCarry (spiralBlocksToParity blocks)`
     (in particular, whenever `matchesParity (spiralBlocksToParity blocks) (Int.ofNat x0)` and
     `collatzIter K x0 = x0`), `D` automatically divides `broxSpiralCarry blocks`!
-/
theorem m_block_cycle_induces_brox_quotients
    (b0 : Nat × Nat) (rest : List (Nat × Nat))
    (hblocks_pos : ∀ b ∈ (b0 :: rest), b.1 ≥ 1 ∧ b.2 ≥ 1)
    (hgt : 3 ^ blockWeightSum (b0 :: rest) < 2 ^ blockStepSum (b0 :: rest)) :
    let blocks := b0 :: rest
    let m := blocks.length
    let D := 2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks
    ((∀ x0 : Nat,
        D * x0 = affineCarry (spiralBlocksToParity blocks) ->
        D ∣ broxSpiralCarry blocks) ∧
     (D ∣ broxSpiralCarry blocks ->
      ∃ qs : List Nat,
        qs.length = m ∧
        (∀ j : Nat, j < m -> D * natAt qs j = broxSpiralCarry (rotBlocks j blocks)) ∧
        natListGcd qs ∣ natListGcd (blocks.map (fun b => 2 ^ b.2 - 1)) ∧
        (∀ j : Nat, j < m -> (natAt qs ((j + 1) % m) % 3 = 0 ↔ (blockAt blocks j).2 % 2 = 0)))) := by
  dsimp only
  let blocks := b0 :: rest
  let m := blocks.length
  let W := blockWeightSum blocks
  let K := blockStepSum blocks
  let D := 2 ^ K - 3 ^ W
  change 3 ^ W < 2 ^ K at hgt
  have hm_pos : m ≥ 1 := by simp [m, blocks]
  have hD_pos : D > 0 := by dsimp [D]; omega
  have hb0_pos : b0.1 ≥ 1 ∧ b0.2 ≥ 1 := hblocks_pos b0 (List.Mem.head _)
  have hK_pos : K ≥ 1 := by dsimp [K, blocks, blockStepSum]; omega
  have hD_odd : D % 2 = 1 := by
    have hp2_ev : (2 ^ K) % 2 = 0 := by
      rw [show K = (K - 1) + 1 by omega, Nat.pow_succ]; omega
    have hp3_odd : (3 ^ W) % 2 = 1 := pow3_odd_nat_sec8 W
    have hlt_kw : 3 ^ W < 2 ^ K := hgt
    dsimp [D]
    generalize 2 ^ K = p2k, 3 ^ W = p3w at hp2_ev hp3_odd hlt_kw
    omega
  refine ⟨?_, ?_⟩
  · intro x0 hcyc
    change D * x0 = affineCarry (spiralBlocksToParity blocks) at hcyc
    have hbridge := broxSpiralCarry_eq_affineCarry_universal b0 rest
    change 2 ^ b0.1 * broxSpiralCarry blocks + 3 ^ W =
      2 ^ K + affineCarry (spiralBlocksToParity blocks) at hbridge
    have h2K_eq : 2 ^ K = D + 3 ^ W := by dsimp [D]; omega
    rw [← hcyc, h2K_eq] at hbridge
    have hmul_eq : 2 ^ b0.1 * broxSpiralCarry blocks = D * (x0 + 1) := by
      rw [Nat.mul_add D x0 1, Nat.mul_one]
      omega
    exact odd_dvd_pow2_mul_cancel_w5 D hD_odd b0.1 (broxSpiralCarry blocks) ⟨x0 + 1, hmul_eq⟩
  · intro hdvd0
    rcases m_block_brox_resultant_and_quotient_locks blocks hm_pos hblocks_pos hgt with
      ⟨hres, hlocks⟩
    have hdvd_all : ∀ j : Nat, j < m -> D ∣ broxSpiralCarry (rotBlocks j blocks) := by
      intro j
      induction j with
      | zero =>
        intro _
        have hr0 : rotBlocks 0 blocks = blocks := by
          unfold rotBlocks; simp
        rwa [hr0]
      | succ j' ih =>
        intro hj1
        rcases ih (by omega) with ⟨qj, hqj⟩
        have hr := hres j' (by omega)
        dsimp only at hr
        have hmod : (j' + 1) % m = j' + 1 := Nat.mod_eq_of_lt hj1
        rw [hmod, hqj] at hr
        have hrhs : 3 ^ (blockAt blocks j').1 * (D * qj) + D * (2 ^ (blockAt blocks j').2 - 1) =
            D * (3 ^ (blockAt blocks j').1 * qj + (2 ^ (blockAt blocks j').2 - 1)) := by
          rw [← Nat.mul_assoc (3 ^ (blockAt blocks j').1) D qj,
              Nat.mul_comm (3 ^ (blockAt blocks j').1) D,
              Nat.mul_assoc D, ← Nat.mul_add]
        rw [hrhs] at hr
        exact odd_dvd_pow2_mul_cancel_w5 D hD_odd _ _ ⟨_, hr⟩
    let qs := buildBroxQuotientsAux D blocks 0 m
    rcases buildBroxQuotientsAux_spec D blocks m 0 with ⟨hq_len, hq_at⟩
    have hqs_eq : ∀ j : Nat, j < m -> D * natAt qs j = broxSpiralCarry (rotBlocks j blocks) := by
      intro j hj
      dsimp [qs]
      rw [hq_at j hj, Nat.zero_add]
      rcases hdvd_all j hj with ⟨q, hq⟩
      rw [hq, Nat.mul_comm D q, Nat.mul_div_cancel q hD_pos, Nat.mul_comm]
    rcases hlocks qs hq_len hqs_eq with ⟨_, hg_mers, _, hmod3⟩
    exact ⟨qs, hq_len, hqs_eq, hg_mers, hmod3⟩

-- ----------------------------------------------------------------------------
-- W5.3b & W5.3c: 1-Block Even-Even Impossibility & Universal Antipodal-Order
--                Divisor Exclusion (Zero Custom Axioms)
-- ----------------------------------------------------------------------------

theorem diff_of_squares_nat (A B : Nat) (hBA : B ≤ A) :
    A * A - B * B = (A - B) * (A + B) := by
  have h1 : (A - B) * (A + B) + B * B = A * A := by
    rw [Nat.mul_add, Nat.sub_mul, Nat.sub_mul]
    have hAB : B * A = A * B := Nat.mul_comm B A
    rw [hAB]
    have hle1 : B * A ≤ A * A := Nat.mul_le_mul_right A hBA
    have hle1' : A * B ≤ A * A := by rwa [← hAB]
    have hle2 : B * B ≤ A * B := Nat.mul_le_mul_right B hBA
    omega
  omega

/--
  Theorem W5.3b (`one_block_even_even_impossibility`, zero custom axioms):
  Universal 1-Block Even-Even Impossibility Theorem:
  Whenever `w1 ≥ 2` and `a1 ≥ 2` are BOTH EVEN (`w1 % 2 = 0 ∧ a1 % 2 = 0`) and
  `3 ^ w1 < 2 ^ (w1 + a1)`, the positive cycle determinant strictly exceeds the
  1-block Mersenne carry:
    `2 ^ (w1 + a1) - 3 ^ w1 > 2 ^ a1 - 1`,
  and hence NO positive integer `q0` can satisfy `(2 ^ (w1 + a1) - 3 ^ w1) * q0 = 2 ^ a1 - 1`!
-/
theorem one_block_even_even_impossibility (w1 a1 : Nat)
    (hw1 : w1 ≥ 2) (ha1 : a1 ≥ 2)
    (hw_ev : w1 % 2 = 0) (ha_ev : a1 % 2 = 0)
    (hgt : 3 ^ w1 < 2 ^ (w1 + a1)) :
    2 ^ a1 - 1 < 2 ^ (w1 + a1) - 3 ^ w1 ∧
    ∀ q0 : Nat, (2 ^ (w1 + a1) - 3 ^ w1) * q0 ≠ 2 ^ a1 - 1 := by
  let v := w1 / 2
  let u := a1 / 2
  have hv_pos : v ≥ 1 := by dsimp [v]; omega
  have hu_pos : u ≥ 1 := by dsimp [u]; omega
  have hw_eq : w1 = v + v := by dsimp [v]; omega
  have ha_eq : a1 = u + u := by dsimp [u]; omega
  have hwa_eq : w1 + a1 = (v + u) + (v + u) := by omega
  let A := 2 ^ (v + u)
  let B := 3 ^ v
  have hAA : A * A = 2 ^ (w1 + a1) := by
    dsimp [A]; rw [← Nat.pow_add, ← hwa_eq]
  have hBB : B * B = 3 ^ w1 := by
    dsimp [B]; rw [← Nat.pow_add, ← hw_eq]
  have hB_lt_A : B < A := by
    by_cases h : B < A
    · exact h
    · have hm : A * A ≤ B * B := Nat.mul_le_mul (by omega : A ≤ B) (by omega : A ≤ B)
      rw [hAA, hBB] at hm; omega
  have hfactor : 2 ^ (w1 + a1) - 3 ^ w1 = (A - B) * (A + B) := by
    rw [← hAA, ← hBB]
    exact diff_of_squares_nat A B (Nat.le_of_lt hB_lt_A)
  have hB_ge3 : B ≥ 3 := by
    dsimp [B]
    have hsplit : v = 1 + (v - 1) := by omega
    rw [hsplit, Nat.pow_add, Nat.pow_one]
    have hp0 := pow3_pos_nat (v - 1)
    have hm := Nat.mul_le_mul_left 3 hp0
    omega
  have hgt_carry : 2 ^ a1 - 1 < (A - B) * (A + B) := by
    by_cases huv : u ≤ v
    · have h2a_le_A : 2 ^ a1 ≤ A := by
        dsimp [A]; rw [ha_eq]; exact pow2_mono_nat (by omega)
      have hdiff_ge1 : A - B ≥ 1 := by omega
      have hsum_gt : A + B > 2 ^ a1 - 1 := by omega
      have hm := Nat.mul_le_mul hdiff_ge1 (Nat.le_refl (A + B))
      rw [Nat.one_mul] at hm
      omega
    · -- `u ≥ v + 1`: `A = 2 * 2 ^ (2 * v + (u - v - 1)) ≥ 2 * B` and `2 ^ (2 * v + (u - v - 1)) ≥ 2 ^ u`:
      let d := u - v - 1
      have hvu_split : v + u = 1 + ((v + v) + d) := by dsimp [d]; omega
      have hA_eq : A = 2 * (4 ^ v * 2 ^ d) := by
        dsimp [A]
        rw [hvu_split, Nat.pow_add 2 1, Nat.pow_one, Nat.pow_add 2 (v + v) d]
        have h4v : 2 ^ (v + v) = 4 ^ v := by
          rw [Nat.pow_add 2 v v, show (4 : Nat) = 2 * 2 from rfl, mul_pow_local 2 2 v]
        rw [h4v]
      have hB_le : B ≤ 4 ^ v * 2 ^ d := by
        dsimp [B]
        have h34 : 3 ^ v ≤ 4 ^ v := nat_pow_mono_base 3 4 (by decide) v
        have hm := Nat.mul_le_mul h34 (pow2_pos_nat d)
        simpa using hm
      have hdiff_ge : A - B ≥ 2 ^ u := by
        have h1 : A - B ≥ 4 ^ v * 2 ^ d := by omega
        have h2u_le : 2 ^ u ≤ 4 ^ v * 2 ^ d := by
          have h4v : 4 ^ v = 2 ^ (v + v) := by
            rw [Nat.pow_add 2 v v, show (4 : Nat) = 2 * 2 from rfl, mul_pow_local 2 2 v]
          rw [h4v, ← Nat.pow_add 2 (v + v) d]
          exact pow2_mono_nat (by dsimp [d]; omega)
        omega
      have hsum_gt : A + B > 2 ^ u := by
        have h1 : A ≥ 2 ^ u := by omega
        omega
      have hm := Nat.mul_le_mul hdiff_ge (by omega : 2 ^ u + 1 ≤ A + B)
      rw [Nat.mul_add, Nat.mul_one, ← Nat.pow_add 2 u u, ← ha_eq] at hm
      have hp2u : 2 ^ u ≥ 2 := by
        have hs : u = 1 + (u - 1) := by omega
        rw [hs, Nat.pow_add, Nat.pow_one]
        have hp := pow2_pos_nat (u - 1); omega
      omega
  rw [← hfactor] at hgt_carry
  refine ⟨hgt_carry, ?_⟩
  intro q0 hbrox
  cases q0 with
  | zero =>
    rw [Nat.mul_zero] at hbrox
    have hp2a : 2 ^ a1 ≥ 4 := by simpa using pow2_mono_nat ha1
    omega
  | succ q' =>
    have hm := Nat.mul_le_mul_left (2 ^ (w1 + a1) - 3 ^ w1) (by omega : 1 ≤ q' + 1)
    rw [Nat.mul_one, hbrox] at hm
    omega

theorem pow_mod_eq_of_mod_eq_w5 (p a b : Nat) (h : a % p = b % p) :
    ∀ n : Nat, (a ^ n) % p = (b ^ n) % p
  | 0 => rfl
  | n + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, Nat.mul_mod (b ^ n),
        pow_mod_eq_of_mod_eq_w5 p a b h n, h]

theorem neg_one_pow_mod_w5 (p x : Nat) (hp : p ≥ 3) (hx : x % p = p - 1) :
    ∀ n : Nat,
      (n % 2 = 0 -> (x ^ n) % p = 1) ∧
      (n % 2 = 1 -> (x ^ n) % p = p - 1)
  | 0 => ⟨fun _ => by rw [Nat.pow_zero]; exact Nat.mod_eq_of_lt (by omega), fun h => by omega⟩
  | n + 1 => by
    rcases neg_one_pow_mod_w5 p x hp hx n with ⟨hev, hodd⟩
    refine ⟨?_, ?_⟩
    · intro h0
      have hn_odd : n % 2 = 1 := by omega
      rw [Nat.pow_succ, Nat.mul_mod, hodd hn_odd, hx]
      have hsq : (p - 1) * (p - 1) = 1 + p * (p - 2) := by
        have h1 : (p - 1) * (p - 1) + (p - 1) = (p - 1) * p := by
          conv => lhs; rhs; rw [← Nat.mul_one (p - 1)]
          rw [← Nat.mul_add, show p - 1 + 1 = p by omega]
        have h2 : (p - 1) * p = p * (p - 2) + p := by
          have hs : p - 1 = (p - 2) + 1 := by omega
          rw [hs, Nat.add_mul, Nat.one_mul, Nat.mul_comm (p - 2) p]
        omega
      rw [hsq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    · intro h1
      have hn_ev : n % 2 = 0 := by omega
      rw [Nat.pow_succ, Nat.mul_mod, hev hn_ev, hx, Nat.one_mul,
          Nat.mod_eq_of_lt (by omega)]

theorem sum_zero_mod_pow_parity_w5 (p A B : Nat) (hp : p ≥ 3) (hsum : (A + B) % p = 0) :
    ∀ n : Nat,
      (n % 2 = 0 -> (B ^ n) % p = (A ^ n) % p) ∧
      (n % 2 = 1 -> (A ^ n + B ^ n) % p = 0)
  | 0 => ⟨fun _ => rfl, fun h => by omega⟩
  | 1 => ⟨fun h => by omega, fun _ => by simpa using hsum⟩
  | n + 2 => by
    rcases sum_zero_mod_pow_parity_w5 p A B hp hsum n with ⟨hev, hodd⟩
    have hsq_eq : (B * B) % p = (A * A) % p := by
      have h1 : (B * B + A * B) % p = 0 := by
        rw [← Nat.add_mul B A B, Nat.add_comm B A, Nat.mul_mod, hsum, Nat.zero_mul, Nat.zero_mod]
      have h2 : (A * A + A * B) % p = 0 := by
        rw [← Nat.mul_add A A B, Nat.mul_mod, hsum, Nat.mul_zero, Nat.zero_mod]
      exact add_right_cancel_mod_sec9 p (B * B) (A * A) (A * B) (by omega) (h1.trans h2.symm)
    refine ⟨?_, ?_⟩
    · intro h0
      have hn_ev : n % 2 = 0 := by omega
      have hBn : B ^ (n + 2) = B ^ n * (B * B) := by
        rw [Nat.pow_add, Nat.pow_succ B 1, Nat.pow_one]
      have hAn : A ^ (n + 2) = A ^ n * (A * A) := by
        rw [Nat.pow_add, Nat.pow_succ A 1, Nat.pow_one]
      rw [hBn, hAn, Nat.mul_mod, Nat.mul_mod (A ^ n), hev hn_ev, hsq_eq]
    · intro h1
      have hn_odd : n % 2 = 1 := by omega
      have hstep_ev : (B ^ (n + 1)) % p = (A ^ (n + 1)) % p := by
        have h1_sum := hodd hn_odd
        have hb1 : (B ^ n * B + A ^ n * B) % p = 0 := by
          rw [← Nat.add_mul, Nat.add_comm (B ^ n) (A ^ n), Nat.mul_mod, h1_sum,
              Nat.zero_mul, Nat.zero_mod]
        have ha1 : (A ^ n * A + A ^ n * B) % p = 0 := by
          rw [← Nat.mul_add, Nat.mul_mod, hsum, Nat.mul_zero, Nat.zero_mod]
        have hc := add_right_cancel_mod_sec9 p (B ^ n * B) (A ^ n * A) (A ^ n * B)
          (by omega) (hb1.trans ha1.symm)
        rwa [← Nat.pow_succ B n, ← Nat.pow_succ A n] at hc
      rw [Nat.pow_succ A (n + 1), Nat.pow_succ B (n + 1),
          Nat.add_mod, Nat.mul_mod (B ^ (n + 1)) B p, hstep_ev,
          ← Nat.mul_mod (A ^ (n + 1)) B p, ← Nat.add_mod,
          ← Nat.mul_add (A ^ (n + 1)) A B, Nat.mul_mod, hsum, Nat.mul_zero, Nat.zero_mod]

theorem odd_mod_pow2_nonzero_w5 (p : Nat) (hp3 : p ≥ 3) (hodd : p % 2 = 1) :
    ∀ e : Nat, (2 ^ e) % p ≠ 0
  | 0 => by rw [Nat.pow_zero, Nat.mod_eq_of_lt (by omega)]; omega
  | e + 1 => by
    intro h0
    have ih := odd_mod_pow2_nonzero_w5 p hp3 hodd e
    let k := (p + 1) / 2
    have h2k : 2 * k = 1 + p := by dsimp [k]; omega
    have hmul : (k * (2 ^ e * 2)) % p = 0 := by
      rw [← Nat.pow_succ 2 e, Nat.mul_mod, h0, Nat.mul_zero, Nat.zero_mod]
    have hswap : k * (2 ^ e * 2) = 2 ^ e + p * 2 ^ e := by
      calc
        k * (2 ^ e * 2) = (2 * k) * 2 ^ e := by
          rw [← Nat.mul_assoc k (2 ^ e) 2, Nat.mul_comm (k * 2 ^ e) 2,
              ← Nat.mul_assoc 2 k (2 ^ e)]
        _ = (1 + p) * 2 ^ e := by rw [h2k]
        _ = 2 ^ e + p * 2 ^ e := by rw [Nat.add_mul, Nat.one_mul]
    rw [hswap, Nat.add_mul_mod_self_left] at hmul
    exact ih hmul

/--
  Theorem W5.3c (`one_block_antipodal_order_divisor_exclusion`, zero custom axioms):
  Universal Antipodal-Order Divisor Exclusion on 1-Block Positive Cycles:
  For EVERY odd integer `p ≥ 3` admitting exponents `m1, m2 ≥ 1` such that
    `2 ^ m1 % p = p - 1`  AND  `(2 ^ m2 + 3 ^ m2) % p = 0`,
  `p` CANNOT divide `D = 2 ^ (w1 + a1) - 3 ^ w1` on ANY 1-block positive integer
  cycle `(w1, a1, q0)` (`w1 ≥ 2, a1 ≥ 1, (2^(w1+a1) - 3^w1) * q0 = 2^a1 - 1`)!
-/
theorem one_block_antipodal_order_divisor_exclusion
    (p m1 m2 w1 a1 q0 : Nat)
    (hp3 : p ≥ 3) (hp_odd : p % 2 = 1)
    (_hm1 : m1 ≥ 1) (_hm2 : m2 ≥ 1)
    (hant1 : 2 ^ m1 % p = p - 1)
    (hant2 : (2 ^ m2 + 3 ^ m2) % p = 0)
    (hw1 : w1 ≥ 2) (ha1 : a1 ≥ 1) (hgt : 3 ^ w1 < 2 ^ (w1 + a1))
    (hbrox : (2 ^ (w1 + a1) - 3 ^ w1) * q0 = 2 ^ a1 - 1) :
    ¬ (p ∣ (2 ^ (w1 + a1) - 3 ^ w1)) := by
  intro hp_dvd_D
  let D := 2 ^ (w1 + a1) - 3 ^ w1
  rcases one_block_gcd_and_congruence_lock w1 a1 q0 hw1 ha1 hgt hbrox with
    ⟨_, _, hcarry_eq, _, _, _, _⟩
  have hp_dvd_2a1 : p ∣ (2 ^ a1 - 1) :=
    Nat.dvd_trans hp_dvd_D ⟨q0, hbrox.symm⟩
  have hp_dvd_3w2w : p ∣ (3 ^ w1 - 2 ^ w1) :=
    Nat.dvd_trans hp_dvd_D ⟨2 ^ w1 * q0 - 1, hcarry_eq⟩
  -- 1. `2 ^ a1 % p = 1` vs `2 ^ m1 % p = p - 1` forces `a1 % 2 = 0`:
  have h2a1_mod : 2 ^ a1 % p = 1 := by
    rcases hp_dvd_2a1 with ⟨k, hk⟩
    have hp2a : 2 ^ a1 ≥ 2 := by simpa using pow2_mono_nat ha1
    have hrew : 2 ^ a1 = 1 + p * k := by omega
    rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have ha1_ev : a1 % 2 = 0 := by
    by_cases hev : a1 % 2 = 0
    · exact hev
    · have ha1_odd : a1 % 2 = 1 := by omega
      have h1 : ((2 ^ a1) ^ m1) % p = 1 := by
        rw [pow_mod_eq_of_mod_eq_w5 p (2 ^ a1) 1
          (by rw [h2a1_mod, Nat.mod_eq_of_lt (by omega)]) m1,
          Nat.one_pow, Nat.mod_eq_of_lt (by omega)]
      have h2 : ((2 ^ m1) ^ a1) % p = p - 1 :=
        (neg_one_pow_mod_w5 p (2 ^ m1) hp3 hant1 a1).2 ha1_odd
      rw [pow_pow_eq_mul_w5 2 a1 m1] at h1
      rw [pow_pow_eq_mul_w5 2 m1 a1, Nat.mul_comm m1 a1] at h2
      rw [h1] at h2
      omega
  -- 2. `3 ^ w1 % p = 2 ^ w1 % p` vs `(2 ^ m2 + 3 ^ m2) % p = 0` forces `w1 % 2 = 0`:
  have h3w_eq_2w : 3 ^ w1 % p = 2 ^ w1 % p := by
    rcases hp_dvd_3w2w with ⟨k, hk⟩
    have h2lt3 : 2 ^ w1 < 3 ^ w1 := by
      have hp := pow2_succ_lt_pow3 w1 hw1
      have hle := pow2_mono_nat (by omega : w1 ≤ w1 + 1)
      omega
    have hrew : 3 ^ w1 = 2 ^ w1 + p * k := by omega
    rw [hrew, Nat.add_mul_mod_self_left]
  have hw1_ev : w1 % 2 = 0 := by
    by_cases hev : w1 % 2 = 0
    · exact hev
    · have hw1_odd : w1 % 2 = 1 := by omega
      have hpow_eq : ((3 ^ m2) ^ w1) % p = ((2 ^ m2) ^ w1) % p := by
        rw [pow_pow_eq_mul_w5 3 m2 w1, pow_pow_eq_mul_w5 2 m2 w1,
            Nat.mul_comm m2 w1, ← pow_pow_eq_mul_w5 3 w1 m2, ← pow_pow_eq_mul_w5 2 w1 m2]
        exact pow_mod_eq_of_mod_eq_w5 p (3 ^ w1) (2 ^ w1) h3w_eq_2w m2
      have hsum0 : ((2 ^ m2) ^ w1 + (3 ^ m2) ^ w1) % p = 0 :=
        (sum_zero_mod_pow_parity_w5 p (2 ^ m2) (3 ^ m2) hp3 hant2 w1).2 hw1_odd
      rw [Nat.add_mod, hpow_eq, ← Nat.add_mod] at hsum0
      have h2pow : (2 ^ m2) ^ w1 + (2 ^ m2) ^ w1 = 2 ^ (m2 * w1 + 1) := by
        rw [pow_pow_eq_mul_w5 2 m2 w1, Nat.pow_succ 2 (m2 * w1)]
        omega
      rw [h2pow] at hsum0
      exact False.elim (odd_mod_pow2_nonzero_w5 p hp3 hp_odd (m2 * w1 + 1) hsum0)
  -- 3. `w1 % 2 = 0 ∧ a1 % 2 = 0` (`a1 ≥ 2`) contradicts `one_block_even_even_impossibility`:
  have ha1_ge2 : a1 ≥ 2 := by omega
  exact (one_block_even_even_impossibility w1 a1 hw1 ha1_ge2 hw1_ev ha1_ev hgt).2 q0 hbrox

/--
  Corollary W5.3d (`one_block_antipodal_prime_instances_and_m1_separation`, zero custom axioms):
  1. Every prime `p ∈ [5, 11, 13, 17, 37, 41, 59, 61, 83, 97]` is unconditionally
     excluded from dividing `2 ^ (w1 + a1) - 3 ^ w1` on any 1-block positive integer cycle!
  2. Counter-Model `M1 = Q_(2)^+` Separation: in `Q_(2)^+`, `p = 5` (`w1 = 3, a1 = 2`,
     `x0 = 19/5`, `D = 2^5 - 3^3 = 5`) and `p = 13` (`w1 = 5, a1 = 3`, `x0 = 211/13`,
     `D = 2^8 - 3^5 = 13`) DO occur as exact 1-block positive rational cycle denominators!
-/
theorem one_block_antipodal_prime_instances_and_m1_separation :
    (∀ (w1 a1 q0 : Nat),
      w1 ≥ 2 -> a1 ≥ 1 -> 3 ^ w1 < 2 ^ (w1 + a1) ->
      (2 ^ (w1 + a1) - 3 ^ w1) * q0 = 2 ^ a1 - 1 ->
      ∀ p ∈ ([5, 11, 13, 17, 37, 41, 59, 61, 83, 97] : List Nat),
        ¬ (p ∣ (2 ^ (w1 + a1) - 3 ^ w1))) ∧
    (2 ^ (3 + 2) - 3 ^ 3 = 5 ∧ 3 ^ 3 - 2 ^ 3 = 19) ∧
    (2 ^ (5 + 3) - 3 ^ 5 = 13 ∧ 3 ^ 5 - 2 ^ 5 = 211) := by
  refine ⟨?_, by decide, by decide⟩
  intro w1 a1 q0 hw1 ha1 hgt hbrox p hp_mem
  have hex : ∃ m1 m2 : Nat, p ≥ 3 ∧ p % 2 = 1 ∧ m1 ≥ 1 ∧ m2 ≥ 1 ∧
      2 ^ m1 % p = p - 1 ∧ (2 ^ m2 + 3 ^ m2) % p = 0 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp_mem
    rcases hp_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨2, 1, by decide, by decide, by decide, by decide, by decide, by decide⟩
    · exact ⟨5, 5, by decide, by decide, by decide, by decide, by decide, by decide⟩
    · exact ⟨6, 2, by decide, by decide, by decide, by decide, by decide, by decide⟩
    · exact ⟨4, 8, by decide, by decide, by decide, by decide, by decide, by decide⟩
    · exact ⟨18, 18, by decide, by decide, by decide, by decide, by decide, by decide⟩
    · exact ⟨10, 20, by decide, by decide, by decide, by decide, by decide, by decide⟩
    · exact ⟨29, 29, by decide, by decide, by decide, by decide, by decide, by decide⟩
    · exact ⟨30, 6, by decide, by decide, by decide, by decide, by decide, by decide⟩
    · exact ⟨41, 41, by decide, by decide, by decide, by decide, by decide, by decide⟩
    · exact ⟨24, 4, by decide, by decide, by decide, by decide, by decide, by decide⟩
  rcases hex with ⟨m1, m2, hp3, hp_odd, hm1, hm2, hant1, hant2⟩
  exact one_block_antipodal_order_divisor_exclusion p m1 m2 w1 a1 q0
    hp3 hp_odd hm1 hm2 hant1 hant2 hw1 ha1 hgt hbrox

-- ============================================================================
-- SECTION 4: Front D (`Branch P5.3` & `P4.4`) — Coupled `q`-Ray Step Laws,
--            Automatic `q ≥ 1` First-Hit Theorem, Dyadic Pinning & Triadic
--            Bijection on `Mod373248`, Sharp `|u| ≥ 8` Floor, & `Π₂⁰`
--            Skolem Box / Polynomial Stopping-Time Calibration (Zero Custom Axioms)
-- ============================================================================

def rayStepFactor (w : Nat) : Nat :=
  (2 ^ (2 * 3 ^ (w - 1)) - 1) / 3 ^ w

theorem cube_add_one_w5 (X : Nat) :
    (X + 1) ^ 3 = X * X * X + 3 * (X * X) + 3 * X + 1 := by
  rw [Nat.pow_succ (X + 1) 2, Nat.pow_succ (X + 1) 1, Nat.pow_one (X + 1)]
  have hsq : (X + 1) * (X + 1) = X * X + 2 * X + 1 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    omega
  rw [hsq, Nat.add_mul, Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_add]
  have h2x : (2 * X) * X = 2 * (X * X) := Nat.mul_assoc 2 X X
  rw [h2x]
  omega

theorem rayStepFactor_spec_and_mod3 :
    ∀ k : Nat,
      3 ^ (k + 1) * rayStepFactor (k + 1) + 1 = 2 ^ (2 * 3 ^ k) ∧
      rayStepFactor (k + 1) % 3 = 1
  | 0 => ⟨by decide, by decide⟩
  | k + 1 => by
    rcases rayStepFactor_spec_and_mod3 k with ⟨hspec, hmod3⟩
    let M := 3 ^ (k + 1)
    let R := rayStepFactor (k + 1)
    change M * R + 1 = 2 ^ (2 * 3 ^ k) at hspec
    change R % 3 = 1 at hmod3
    have hM_eq : M = 3 * 3 ^ k := by
      dsimp [M]; rw [Nat.pow_succ 3 k, Nat.mul_comm]
    have hM_next : 3 ^ (k + 2) = 3 * M := by
      dsimp [M]; rw [Nat.pow_succ 3 (k + 1), Nat.mul_comm]
    have hexp_pow : 2 ^ (2 * 3 ^ (k + 1)) = (2 ^ (2 * 3 ^ k)) ^ 3 := by
      rw [Nat.pow_succ 3 k, ← Nat.mul_assoc 2 (3 ^ k) 3,
          ← pow_pow_eq_mul_w5 2 (2 * 3 ^ k) 3]
    let Rnext := R + 3 * (3 ^ k * 3 ^ k * (R * R * R) + 3 ^ k * (R * R))
    have hcube_eq : (M * R + 1) ^ 3 = (3 * M) * Rnext + 1 := by
      rw [cube_add_one_w5 (M * R)]
      have ht1 : (M * R) * (M * R) * (M * R) =
          (3 * M) * (3 * (3 ^ k * 3 ^ k * (R * R * R))) := by
        have hm3_cube : (M * R) * (M * R) * (M * R) = (M * M * M) * (R * R * R) := by
          have hp3 := mul_pow_local M R 3
          simpa only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul] using hp3
        have hMMM : M * M * M = (3 * M) * (3 * (3 ^ k * 3 ^ k)) := by
          conv => lhs; lhs; rhs; rw [hM_eq]
          conv => lhs; rhs; rw [hM_eq]
          calc
            (M * (3 * 3 ^ k)) * (3 * 3 ^ k)
                = (3 * M) * (3 ^ k * (3 * 3 ^ k)) := by
                  rw [← Nat.mul_assoc M 3 (3 ^ k), Nat.mul_comm M 3,
                      Nat.mul_assoc (3 * M) (3 ^ k) (3 * 3 ^ k)]
            _ = (3 * M) * (3 * (3 ^ k * 3 ^ k)) := by
                  rw [← Nat.mul_assoc (3 ^ k) 3 (3 ^ k), Nat.mul_comm (3 ^ k) 3,
                      Nat.mul_assoc 3 (3 ^ k) (3 ^ k)]
        rw [hm3_cube, hMMM, Nat.mul_assoc (3 * M), Nat.mul_assoc 3 (3 ^ k * 3 ^ k)]
      have ht2 : 3 * ((M * R) * (M * R)) = (3 * M) * (3 * (3 ^ k * (R * R))) := by
        have hMR2 : (M * R) * (M * R) = (M * M) * (R * R) := by
          rw [Nat.mul_assoc M R (M * R), ← Nat.mul_assoc R M R, Nat.mul_comm R M,
              Nat.mul_assoc M R R, ← Nat.mul_assoc M M (R * R)]
        have hMM : 3 * (M * M) = (3 * M) * (3 * 3 ^ k) := by
          conv => lhs; rhs; rhs; rw [hM_eq]
          rw [← Nat.mul_assoc 3 M (3 * 3 ^ k)]
        rw [hMR2, ← Nat.mul_assoc 3 (M * M) (R * R), hMM,
            Nat.mul_assoc (3 * M) (3 * 3 ^ k) (R * R), Nat.mul_assoc 3 (3 ^ k) (R * R)]
      have ht3 : 3 * (M * R) = (3 * M) * R := (Nat.mul_assoc 3 M R).symm
      rw [ht1, ht2, ht3]
      dsimp [Rnext]
      rw [Nat.mul_add (3 * M), Nat.mul_add 3, Nat.mul_add (3 * M)]
      omega
    have hpow_eq : 2 ^ (2 * 3 ^ (k + 1)) = 3 ^ (k + 2) * Rnext + 1 := by
      rw [hexp_pow, ← hspec, hcube_eq, ← hM_next]
    have hdiv_eq : rayStepFactor (k + 2) = Rnext := by
      unfold rayStepFactor
      rw [show k + 2 - 1 = k + 1 from rfl, hpow_eq, Nat.add_sub_cancel,
          Nat.mul_comm (3 ^ (k + 2)) Rnext,
          Nat.mul_div_cancel Rnext (pow3_pos_nat (k + 2))]
    refine ⟨?_, ?_⟩
    · rw [hdiv_eq]
      exact hpow_eq.symm
    · rw [hdiv_eq]
      dsimp [Rnext]
      rw [Nat.add_mul_mod_self_left]
      exact hmod3

theorem coreWord_weight_pos_w5 (u : List Bool) (hu : IsCoreParityWord u) :
    parityWeight u ≥ 1 ∧ u.length ≥ 1 := by
  cases u with
  | nil => have hh := hu.1; simp at hh
  | cons b rest =>
    have hb : b = true := by have hh := hu.1; simp at hh; exact hh
    subst hb
    simp [parityWeight]

/--
  Theorem W5.4a (`exactBackwardQuotient_one_ray_step_law`, zero custom axioms):
  Universal Coupled `q`-Ray Step & Affine Recurrence Law:
  For EVERY core parity word `u` (`w := parityWeight u ≥ 1`) and EVERY `q : Nat`:
  1. `backwardOneTotalSteps u (q + 1) = backwardOneTotalSteps u q + 2 * 3 ^ (w - 1)`;
  2. Pure dyadic `2^L`-ray step:
     `exactBackwardQuotient 1 u (q + 1) = exactBackwardQuotient 1 u q + 2 ^ (backwardOneTotalSteps u q) * rayStepFactor w`;
  3. Coupled `2^P`-affine recurrence:
     `exactBackwardQuotient 1 u (q + 1) = 2 ^ (2 * 3 ^ (w - 1)) * exactBackwardQuotient 1 u q + rayStepFactor w * affineCarry u`.
-/
theorem exactBackwardQuotient_one_ray_step_law (u : List Bool) (q : Nat)
    (hu : IsCoreParityWord u) :
    let w := parityWeight u
    let P := 2 * 3 ^ (w - 1)
    let L := backwardOneTotalSteps u q
    backwardOneTotalSteps u (q + 1) = L + P ∧
    exactBackwardQuotient 1 u (q + 1) =
      exactBackwardQuotient 1 u q + 2 ^ L * rayStepFactor w ∧
    exactBackwardQuotient 1 u (q + 1) =
      2 ^ P * exactBackwardQuotient 1 u q + rayStepFactor w * affineCarry u := by
  dsimp only
  let w := parityWeight u
  let P := 2 * 3 ^ (w - 1)
  let M := 3 ^ w
  let L := backwardOneTotalSteps u q
  have hw_pos : w ≥ 1 := (coreWord_weight_pos_w5 u hu).1
  have hM_pos : M > 0 := pow3_pos_nat w
  have hray : M * rayStepFactor w + 1 = 2 ^ P := by
    have hsp := (rayStepFactor_spec_and_mod3 (w - 1)).1
    have hw_eq : w - 1 + 1 = w := by omega
    rw [hw_eq] at hsp
    exact hsp
  have hsteps : backwardOneTotalSteps u (q + 1) = L + P := by
    dsimp [L, P, w]
    unfold backwardOneTotalSteps
    rw [Nat.add_mul q 1, Nat.one_mul]
    omega
  rcases one_generator_pos_odd_and_reaches_one u q hu with ⟨_, _, heq0, _⟩
  rcases one_generator_pos_odd_and_reaches_one u (q + 1) hu with ⟨_, _, heq1, _⟩
  change 2 ^ L = M * exactBackwardQuotient 1 u q + affineCarry u at heq0
  rw [hsteps] at heq1
  change 2 ^ (L + P) = M * exactBackwardQuotient 1 u (q + 1) + affineCarry u at heq1
  have hstep_dyadic : exactBackwardQuotient 1 u (q + 1) =
      exactBackwardQuotient 1 u q + 2 ^ L * rayStepFactor w := by
    apply nat_mul_left_cancel_pos M _ _ hM_pos
    have hlhs : M * exactBackwardQuotient 1 u (q + 1) + affineCarry u =
        M * (exactBackwardQuotient 1 u q + 2 ^ L * rayStepFactor w) + affineCarry u := by
      rw [← heq1, Nat.pow_add 2 L P, ← hray, Nat.mul_add (2 ^ L), Nat.mul_one]
      have hcomm : 2 ^ L * (M * rayStepFactor w) = M * (2 ^ L * rayStepFactor w) := by
        rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ L) M, Nat.mul_assoc]
      rw [hcomm, heq0, Nat.mul_add M]
      omega
    omega
  have hstep_aff : exactBackwardQuotient 1 u (q + 1) =
      2 ^ P * exactBackwardQuotient 1 u q + rayStepFactor w * affineCarry u := by
    apply nat_mul_left_cancel_pos M _ _ hM_pos
    have hlhs : M * exactBackwardQuotient 1 u (q + 1) + affineCarry u =
        M * (2 ^ P * exactBackwardQuotient 1 u q + rayStepFactor w * affineCarry u) + affineCarry u := by
      rw [← heq1, Nat.pow_add 2 L P, heq0, Nat.add_mul]
      have h1 : M * exactBackwardQuotient 1 u q * 2 ^ P =
          M * (2 ^ P * exactBackwardQuotient 1 u q) := by
        rw [Nat.mul_assoc M, Nat.mul_comm (exactBackwardQuotient 1 u q) (2 ^ P)]
      have h2 : affineCarry u * 2 ^ P = M * (rayStepFactor w * affineCarry u) + affineCarry u := by
        rw [← hray, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc,
            Nat.mul_comm (affineCarry u) M, Nat.mul_assoc M (affineCarry u) (rayStepFactor w),
            Nat.mul_comm (affineCarry u) (rayStepFactor w)]
      rw [h1, h2, Nat.mul_add M, Nat.add_assoc]
    omega
  exact ⟨hsteps, hstep_dyadic, hstep_aff⟩

theorem collatzIter_triv_one_two_w5 :
    ∀ (d x : Nat), (x = 1 ∨ x = 2) -> collatzIter d x = 1 ∨ collatzIter d x = 2
  | 0, x, hx => hx
  | d + 1, x, hx => by
    simp only [collatzIter]
    rcases hx with rfl | rfl
    · exact collatzIter_triv_one_two_w5 d (collatzStep 1) (Or.inr (by decide))
    · exact collatzIter_triv_one_two_w5 d (collatzStep 2) (Or.inl (by decide))

theorem list_append_right_eq_of_eq_len_w5 :
    ∀ (a1 a2 b1 b2 : List Bool),
      a1.length = a2.length -> a1 ++ b1 = a2 ++ b2 -> b1 = b2
  | [], [], _, _, _, h => h
  | [], _ :: _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, hlen, _ => by simp at hlen
  | _ :: r1, _ :: r2, b1, b2, hlen, h => by
    simp only [List.length_cons, List.cons_append, List.cons.injEq] at hlen h
    exact list_append_right_eq_of_eq_len_w5 r1 r2 b1 b2 (by omega) h.2

/--
  Theorem W5.4b (`one_generator_q_pos_always_first_hit`, zero custom axioms):
  Universal `q ≥ 1` First-Hit Automaticity Theorem:
  For EVERY core parity word `u` with `parityWeight u ≥ 2` and EVERY `q ≥ 1`,
  `(u, q)` is AUTOMATICALLY a genuine first-hit pair (`IsFirstHitOnePair u q`) —
  even when `q = 0` wraps around the `{1, 2}` trivial loop and fails `IsFirstHitOnePair`!
-/
theorem one_generator_q_pos_always_first_hit
    (u : List Bool) (q : Nat)
    (hu : IsCoreParityWord u) (hw : parityWeight u ≥ 2) (hq : q ≥ 1) :
    IsFirstHitOnePair u q := by
  refine ⟨hu, ?_⟩
  let y := exactBackwardQuotient 1 u q
  let L := backwardOneTotalSteps u q
  let shift := canonicalSuffixShift u 1 + q * (2 * 3 ^ (parityWeight u - 1))
  have hshift_ge6 : shift ≥ 6 := by
    dsimp [shift]
    have hp3 : 3 ^ (parityWeight u - 1) ≥ 3 := by
      have hs : parityWeight u - 1 = 1 + (parityWeight u - 2) := by omega
      rw [hs, Nat.pow_add, Nat.pow_one]
      have hp0 := pow3_pos_nat (parityWeight u - 2)
      have hm := Nat.mul_le_mul_left 3 hp0; omega
    have hm := Nat.mul_le_mul hq (by omega : 6 ≤ 2 * 3 ^ (parityWeight u - 1))
    omega
  have hL_eq : L = u.length + shift := rfl
  have hL_ge6 : L ≥ 6 := by omega
  rcases one_generator_pos_odd_and_reaches_one u q hu with ⟨_, _, heq, hiterL⟩
  change 2 ^ L = 3 ^ parityWeight u * y + affineCarry u at heq
  change collatzIter L y = 1 at hiterL
  let v := u ++ List.replicate shift false
  have hv_len : v.length = L := by
    dsimp [v, L]; unfold backwardOneTotalSteps; rw [List.length_append, List.length_replicate]
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
    rw [hs1] at hiterL
    omega
  · have hj_le2 : j ≤ L - 2 := by omega
    have hsplit_j : L - 2 = j + (L - 2 - j) := by omega
    have htriv : collatzIter (L - 2) y = 1 ∨ collatzIter (L - 2) y = 2 := by
      rw [hsplit_j, collatzIter_add]
      exact collatzIter_triv_one_two_w5 (L - 2 - j) (collatzIter j y) (Or.inl hj1)
    rcases htriv with h_eq1 | h_eq2
    · -- `collatzIter (L - 2) y = 1` forces suffix `[true, false]`, contradicting `[false, false]`:
      have hpar_split : parityOfIter L y = parityOfIter (L - 2) y ++ [true, false] := by
        have hLs : L = (L - 2) + 2 := by omega
        conv => lhs; rw [hLs]
        rw [parityOfIter_append_split (L - 2) 2 y, h_eq1]
        rfl
      have hv_split : v = (u ++ List.replicate (shift - 2) false) ++ [false, false] := by
        dsimp [v]
        have hs2 : shift = (shift - 2) + 2 := by omega
        conv => lhs; rhs; rw [hs2]
        have hrep2 : List.replicate ((shift - 2) + 2) false =
            List.replicate (shift - 2) false ++ [false, false] := by
          clear hv_par hv_aff hwt_v hcar_v hv_len hL_eq hshift_ge6
          induction (shift - 2) with
          | zero => rfl
          | succ k ih =>
            rw [Nat.succ_add, List.replicate_succ, ih, List.replicate_succ, List.cons_append]
        rw [hrep2, ← List.append_assoc]
      rw [hv_split, hpar_split] at hv_par
      have hlen_pre : (u ++ List.replicate (shift - 2) false).length =
          (parityOfIter (L - 2) y).length := by
        rw [List.length_append, List.length_replicate, parityOfIter_length]; omega
      have hsuf := list_append_right_eq_of_eq_len_w5 _ _ [false, false] [true, false]
        hlen_pre hv_par
      simp at hsuf
    · -- `collatzIter (L - 2) y = 2` -> `collatzIter L y = collatzIter 2 2 = 2 ≠ 1`:
      have hLs : L = (L - 2) + 2 := by omega
      rw [hLs, collatzIter_add (L - 2) 2 y, h_eq2] at hiterL
      have hs2 : collatzIter 2 2 = 2 := by decide
      rw [hs2] at hiterL
      omega

theorem quad_hensel_inv_lift_w5 (M s inv : Nat) (hM : M ≥ 2)
    (hinv : (s * inv) % M = 1) :
    let u := (s * inv) / M
    let inv' := inv * (1 + M * (M - u % M))
    (s * inv') % (M * M) = 1 := by
  dsimp only
  let u := (s * inv) / M
  let v := M - u % M
  have hsi : s * inv = 1 + M * u := by
    have hdm := (Nat.div_add_mod (s * inv) M).symm
    rw [hinv] at hdm
    dsimp [u]
    omega
  have huv : u + v = M * (u / M + 1) := by
    have hdm := (Nat.div_add_mod u M).symm
    have hlt : u % M < M := Nat.mod_lt u (by omega)
    dsimp [v]
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hprod : s * (inv * (1 + M * v)) = 1 + (M * M) * (u / M + 1 + u * v) := by
    rw [← Nat.mul_assoc s inv, hsi, Nat.add_mul 1 (M * u), Nat.one_mul,
        Nat.mul_add (M * u) 1 (M * v), Nat.mul_one]
    have hmuv : (M * u) * (M * v) = (M * M) * (u * v) := by
      calc
        (M * u) * (M * v) = M * (u * (M * v)) := Nat.mul_assoc _ _ _
        _ = M * ((u * M) * v) := by rw [← Nat.mul_assoc u M v]
        _ = M * ((M * u) * v) := by rw [Nat.mul_comm u M]
        _ = (M * M) * (u * v) := by rw [Nat.mul_assoc M u v, ← Nat.mul_assoc M M]
    have hsum_mid : M * v + M * u = (M * M) * (u / M + 1) := by
      rw [Nat.add_comm (M * v), ← Nat.mul_add M u v, huv, ← Nat.mul_assoc M M]
    rw [hmuv, Nat.add_assoc 1 (M * v), ← Nat.add_assoc (M * v) (M * u),
        hsum_mid, ← Nat.mul_add (M * M)]
  have hMM_gt1 : M * M > 1 := by
    have hm := Nat.mul_le_mul hM hM
    omega
  rw [hprod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hMM_gt1]

theorem mod729_unit_has_inverse_w5 (s : Nat) (hs : s % 3 ≠ 0) :
    ∃ inv : Nat, (s * inv) % 729 = 1 := by
  let inv0 := if s % 3 = 1 then 1 else 2
  have h0 : (s * inv0) % 3 = 1 := by
    dsimp [inv0]
    by_cases h1 : s % 3 = 1
    · simp only [h1, ite_true, Nat.mul_one]
    · simp only [h1, ite_false]
      have h2 : s % 3 = 2 := by omega
      rw [Nat.mul_mod, h2]
  let inv1 := inv0 * (1 + 3 * (3 - ((s * inv0) / 3) % 3))
  have h1 : (s * inv1) % 9 = 1 := quad_hensel_inv_lift_w5 3 s inv0 (by decide) h0
  let inv2 := inv1 * (1 + 9 * (9 - ((s * inv1) / 9) % 9))
  have h2 : (s * inv2) % 81 = 1 := quad_hensel_inv_lift_w5 9 s inv1 (by decide) h1
  let inv3 := inv2 * (1 + 81 * (81 - ((s * inv2) / 81) % 81))
  have h3 : (s * inv3) % 6561 = 1 := quad_hensel_inv_lift_w5 81 s inv2 (by decide) h2
  refine ⟨inv3, ?_⟩
  have h6561 : (6561 : Nat) = 729 * 9 := rfl
  have hm := mod_mul_mod_eq (s * inv3) 729 9
  rw [← h6561, h3] at hm
  exact hm.symm

theorem pow2_mod3_nonzero_w5 : ∀ e : Nat, (2 ^ e) % 3 ≠ 0 :=
  odd_mod_pow2_nonzero_w5 3 (by decide) (by decide)

/--
  Theorem W5.4c (`mod373248_ray_dyadic_pinning_and_triadic_bijection`, zero custom axioms):
  Universal Dyadic `mod 512` Pinning & Triadic `mod 729` Bijection on `w ≥ 6` `q`-Rays:
  For EVERY core parity word `u` with `w := parityWeight u ≥ 6`:
  1. `L0 := backwardOneTotalSteps u 0 ≥ 10`;
  2. Universal `mod 512` Pinning: `∀ q : Nat, exactBackwardQuotient 1 u q % 512 = exactBackwardQuotient 1 u 0 % 512`;
  3. Universal `mod 729` Linear Progression: with `step729 := (2 ^ L0 * rayStepFactor w) % 729`,
     `step729 % 3 ≠ 0` and `∀ q : Nat, exactBackwardQuotient 1 u q % 729 = (exactBackwardQuotient 1 u 0 + q * step729) % 729`;
  4. Exact Bijection on `Fin 729`: `q ↦ exactBackwardQuotient 1 u q % 729` is BOTH injective
     and surjective across `Fin 729` (visiting all `729` triadic residues — and hence all `382`
     surviving `mod 729` classes — once per period of `729` consecutive `q` values!).
-/
theorem mod373248_ray_dyadic_pinning_and_triadic_bijection
    (u : List Bool) (hu : IsCoreParityWord u) (hw : parityWeight u ≥ 6) :
    let w := parityWeight u
    let L0 := backwardOneTotalSteps u 0
    let step729 := (2 ^ L0 * rayStepFactor w) % 729
    L0 ≥ 10 ∧
    (∀ q : Nat, exactBackwardQuotient 1 u q % 512 = exactBackwardQuotient 1 u 0 % 512) ∧
    step729 % 3 ≠ 0 ∧
    (∀ q : Nat, exactBackwardQuotient 1 u q % 729 =
      (exactBackwardQuotient 1 u 0 + q * step729) % 729) ∧
    (∀ q1 q2 : Fin 729,
      exactBackwardQuotient 1 u q1.val % 729 = exactBackwardQuotient 1 u q2.val % 729 ->
      q1 = q2) ∧
    (∀ r : Fin 729, ∃ q : Fin 729, exactBackwardQuotient 1 u q.val % 729 = r.val) := by
  dsimp only
  let w := parityWeight u
  let L0 := backwardOneTotalSteps u 0
  let step729 := (2 ^ L0 * rayStepFactor w) % 729
  rcases one_generator_pos_odd_and_reaches_one u 0 hu with ⟨hy0_pos, _, heq0, _⟩
  change 2 ^ L0 = 3 ^ w * exactBackwardQuotient 1 u 0 + affineCarry u at heq0
  have hp3_ge729 : 3 ^ w ≥ 729 := by
    have hs : w = 6 + (w - 6) := by omega
    rw [hs, Nat.pow_add]
    have hp0 := pow3_pos_nat (w - 6)
    have h729 : (3 : Nat) ^ 6 = 729 := rfl
    rw [h729]
    have hm := Nat.mul_le_mul_left 729 hp0; omega
  have hcar_pos : affineCarry u ≥ 1 := by
    cases u with
    | nil => have hh := hu.1; simp at hh
    | cons b rest =>
      have hb : b = true := by have hh := hu.1; simp at hh; exact hh
      subst hb
      have hcar : affineCarry (true :: rest) = 3 ^ parityWeight rest + 2 * affineCarry rest := by
        change affineCarry ([true] ++ rest) = _
        rw [affineCarry_append]
        have hc1 : affineCarry [true] = 1 := rfl
        have hl1 : [true].length = 1 := rfl
        rw [hc1, hl1, Nat.mul_one, Nat.pow_one]
      rw [hcar]
      have hp0 := pow3_pos_nat (parityWeight rest); omega
  have h2L0_ge730 : 2 ^ L0 ≥ 730 := by
    have hm := Nat.mul_le_mul hp3_ge729 hy0_pos; omega
  have hL0_ge10 : L0 ≥ 10 := by
    by_cases hlt10 : L0 < 10
    · have hle9 : 2 ^ L0 ≤ 2 ^ 9 := pow2_mono_nat (by omega : L0 ≤ 9)
      have h512 : (2 : Nat) ^ 9 = 512 := rfl
      rw [h512] at hle9; omega
    · omega
  have hL_ge_L0 : ∀ q : Nat, backwardOneTotalSteps u q = L0 + q * (2 * 3 ^ (w - 1)) := by
    intro q; dsimp [L0, w]; unfold backwardOneTotalSteps; omega
  -- 1. `mod 512` pinning across all `q`:
  have hmod512 : ∀ q : Nat, exactBackwardQuotient 1 u q % 512 = exactBackwardQuotient 1 u 0 % 512 := by
    intro q
    induction q with
    | zero => rfl
    | succ q' ih =>
      rcases exactBackwardQuotient_one_ray_step_law u q' hu with ⟨_, hdyad, _⟩
      have hLq_ge9 : backwardOneTotalSteps u q' ≥ 9 := by
        rw [hL_ge_L0 q']; omega
      have hdiv512 : (2 ^ backwardOneTotalSteps u q' * rayStepFactor w) % 512 = 0 := by
        have hs : backwardOneTotalSteps u q' = 9 + (backwardOneTotalSteps u q' - 9) := by omega
        rw [hs, Nat.pow_add, show (2 : Nat) ^ 9 = 512 from rfl,
            Nat.mul_assoc, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
      rw [hdyad, Nat.add_mod, hdiv512, Nat.add_zero, Nat.mod_mod, ih]
  -- 2. `step729 % 3 ≠ 0`:
  have hstep729_n3 : step729 % 3 ≠ 0 := by
    dsimp [step729]
    have hm3 : ((2 ^ L0 * rayStepFactor w) % 729) % 3 = (2 ^ L0 * rayStepFactor w) % 3 :=
      mod_mul_mod_eq (2 ^ L0 * rayStepFactor w) 3 243
    rw [hm3]
    have hr_mod3 : rayStepFactor w % 3 = 1 := by
      have hm := (rayStepFactor_spec_and_mod3 (w - 1)).2
      have hw_eq : w - 1 + 1 = w := by omega
      rwa [hw_eq] at hm
    rw [Nat.mul_mod, hr_mod3, Nat.mul_one, Nat.mod_mod]
    exact pow2_mod3_nonzero_w5 L0
  -- 3. `mod 729` linear progression across all `q`:
  have hP_486 : 2 * 3 ^ (w - 1) = 3 ^ (w - 6) * (2 * 3 ^ (6 - 1)) := by
    have hs : w - 1 = (w - 6) + 5 := by omega
    rw [hs, Nat.pow_add 3 (w - 6) 5, show 6 - 1 = 5 from rfl,
        ← Nat.mul_assoc, Nat.mul_comm 2 (3 ^ (w - 6)), Nat.mul_assoc]
  have hmod729_prog : ∀ q : Nat, exactBackwardQuotient 1 u q % 729 =
      (exactBackwardQuotient 1 u 0 + q * step729) % 729 := by
    intro q
    induction q with
    | zero => simp
    | succ q' ih =>
      rcases exactBackwardQuotient_one_ray_step_law u q' hu with ⟨_, hdyad, _⟩
      have h2Lq_729 : (2 ^ backwardOneTotalSteps u q') % 729 = (2 ^ L0) % 729 := by
        have hp6 := pow2_period_mul_mod_pow3 6 (by decide) (q' * 3 ^ (w - 6))
        rw [show (3 : Nat) ^ 6 = 729 from rfl] at hp6
        rw [hL_ge_L0 q', hP_486, ← Nat.mul_assoc q' (3 ^ (w - 6)) (2 * 3 ^ (6 - 1)),
            Nat.pow_add 2 L0, Nat.mul_mod, hp6,
            Nat.mul_one, Nat.mod_mod]
      have hterm_729 : (2 ^ backwardOneTotalSteps u q' * rayStepFactor w) % 729 = step729 := by
        dsimp [step729]
        rw [Nat.mul_mod, h2Lq_729, ← Nat.mul_mod]
      rw [hdyad, Nat.add_mod, ih, hterm_729, Nat.mod_add_mod,
          Nat.add_assoc (exactBackwardQuotient 1 u 0), Nat.add_mul q' 1 step729, Nat.one_mul]
  -- 4. Injectivity & Surjectivity on `Fin 729` via `mod729_unit_has_inverse_w5`:
  rcases mod729_unit_has_inverse_w5 step729 hstep729_n3 with ⟨invS, hinvS⟩
  have hinj : ∀ q1 q2 : Fin 729,
      exactBackwardQuotient 1 u q1.val % 729 = exactBackwardQuotient 1 u q2.val % 729 ->
      q1 = q2 := by
    intro q1 q2 heq_mod
    rw [hmod729_prog q1.val, hmod729_prog q2.val] at heq_mod
    have hcancel_y0 := add_right_cancel_mod_sec9 729
      (q1.val * step729) (q2.val * step729) (exactBackwardQuotient 1 u 0)
      (by decide)
      (by rw [Nat.add_comm (q1.val * step729), Nat.add_comm (q2.val * step729)]; exact heq_mod)
    have hmul_inv : ((q1.val * step729) * invS) % 729 = ((q2.val * step729) * invS) % 729 := by
      rw [Nat.mul_mod (q1.val * step729), hcancel_y0, ← Nat.mul_mod]
    have hsimp_q : ∀ z : Nat, z < 729 -> ((z * step729) * invS) % 729 = z := by
      intro z hz
      rw [Nat.mul_assoc z step729 invS, Nat.mul_mod, hinvS, Nat.mul_one,
          Nat.mod_mod, Nat.mod_eq_of_lt hz]
    rw [hsimp_q q1.val q1.isLt, hsimp_q q2.val q2.isLt] at hmul_inv
    exact Fin.eq_of_val_eq hmul_inv
  have hsurj : ∀ r : Fin 729, ∃ q : Fin 729, exactBackwardQuotient 1 u q.val % 729 = r.val := by
    intro r
    let y0_m := exactBackwardQuotient 1 u 0 % 729
    have hy0_lt : y0_m < 729 := Nat.mod_lt _ (by decide)
    let diff := r.val + 729 - y0_m
    let qv := (diff * invS) % 729
    refine ⟨⟨qv, Nat.mod_lt _ (by decide)⟩, ?_⟩
    dsimp only
    rw [hmod729_prog qv]
    have hqs : (qv * step729) % 729 = diff % 729 := by
      dsimp [qv]
      rw [Nat.mod_mul_mod, Nat.mul_assoc diff invS step729, Nat.mul_comm invS step729,
          Nat.mul_mod diff, hinvS, Nat.mul_one, Nat.mod_mod]
    have hsum_r : (exactBackwardQuotient 1 u 0 + diff) % 729 = r.val := by
      have hy0_div : exactBackwardQuotient 1 u 0 = 729 * (exactBackwardQuotient 1 u 0 / 729) + y0_m :=
        (Nat.div_add_mod _ 729).symm
      have htot : exactBackwardQuotient 1 u 0 + diff =
          r.val + 729 * (exactBackwardQuotient 1 u 0 / 729 + 1) := by
        dsimp [diff]; omega
      rw [htot, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt]
    rw [Nat.add_mod, hqs, ← Nat.add_mod, hsum_r]
  exact ⟨hL0_ge10, hmod512, hstep729_n3, hmod729_prog, hinj, hsurj⟩

-- ----------------------------------------------------------------------------
-- W5.4d & W5.4e: Unconditional `|u| ≤ 7` Elimination (`|u| ≥ 8` Sharp Floor)
--                & Forward-Upgraded Equivalence (Zero Custom Axioms)
-- ----------------------------------------------------------------------------

theorem survivingMod512Bool_nine_gt_seven_weight_grid :
    ∀ (i : Fin 16) (j : Fin 32),
      isSurvivingMod512Bool (32 * i.val + j.val) = true ->
      parityWeight (parityOfIter 7 (32 * i.val + j.val)) <
        parityWeight (parityOfIter 9 (32 * i.val + j.val)) := by
  decide

theorem survivingMod512Bool_nine_gt_seven_weight (r : Nat) (hr : r < 512)
    (hb : isSurvivingMod512Bool r = true) :
    parityWeight (parityOfIter 7 r) < parityWeight (parityOfIter 9 r) := by
  have hi : r / 32 < 16 := by omega
  have hj : r % 32 < 32 := Nat.mod_lt r (by decide)
  have hsplit : 32 * (r / 32) + r % 32 = r := Nat.div_add_mod r 32
  have hg := survivingMod512Bool_nine_gt_seven_weight_grid ⟨r / 32, hi⟩ ⟨r % 32, hj⟩
  dsimp only at hg
  rw [hsplit] at hg
  exact hg hb

theorem replicate_false_split_w5 (a b : Nat) :
    List.replicate (a + b) false = List.replicate a false ++ List.replicate b false := by
  induction a with
  | zero => simp
  | succ a' ih => simp only [Nat.succ_add, List.replicate_succ, List.cons_append, ih]

/--
  Theorem W5.4d (`one_generator_length_le_seven_never_surviving_mod373248`, zero custom axioms):
  Unconditional Sharp Forward Core-Length Elimination (`|u| ≥ 8` Floor):
  Strengthening `W4.5b` (`parityWeight u ≤ 5`), EVERY core parity word `u` with
  `u.length ≤ 7` (including `[true, true, true, true, true, true]` of weight `6`
  and all length-`7` core words of weight `6` or `7`) has `exactBackwardQuotient 1 u q`
  universally disjoint from `IsSurvivingMod373248Class` across ALL `q : Nat`!
  Sharpness: `y = 184111` (`W4.5d`) has `u.length = 8` and `parityWeight u = 6`!
-/
theorem one_generator_length_le_seven_never_surviving_mod373248
    (u : List Bool) (q : Nat)
    (hu : IsCoreParityWord u) (hlen : u.length ≤ 7) :
    ¬ IsSurvivingMod373248Class (exactBackwardQuotient 1 u q) := by
  intro hs
  by_cases hw5 : parityWeight u ≤ 5
  · exact one_generator_weight_le_five_never_surviving_mod373248 u q hu hw5 hs
  · have hw_ge6 : parityWeight u ≥ 6 := by omega
    let y := exactBackwardQuotient 1 u q
    let K := backwardOneTotalSteps u q
    have hL0_ge10 : backwardOneTotalSteps u 0 ≥ 10 :=
      (mod373248_ray_dyadic_pinning_and_triadic_bijection u hu hw_ge6).1
    have hK_ge10 : K ≥ 10 := by
      dsimp [K]
      unfold backwardOneTotalSteps at hL0_ge10 ⊢
      omega
    let shift := canonicalSuffixShift u 1 + q * (2 * 3 ^ (parityWeight u - 1))
    have hK_eq : K = u.length + shift := rfl
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
    -- Extract `parityOfIter 7 y = u ++ List.replicate (7 - u.length) false`:
    have hp7 : parityOfIter 7 y = u ++ List.replicate (7 - u.length) false := by
      have hKs7 : K = 7 + (K - 7) := by omega
      have hpar7 := parityOfIter_append_split 7 (K - 7) y
      rw [← hKs7, ← hv_par] at hpar7
      have hsh7 : shift = (7 - u.length) + (K - 7) := by omega
      dsimp [v] at hpar7
      rw [hsh7, replicate_false_split_w5, ← List.append_assoc] at hpar7
      have hlen7 : (u ++ List.replicate (7 - u.length) false).length =
          (parityOfIter 7 y).length := by
        rw [List.length_append, List.length_replicate, parityOfIter_length]; omega
      exact (list_append_inj_left_eq_len _ _ _ _ hlen7 hpar7).1.symm
    -- Extract `parityOfIter 9 y = u ++ List.replicate (9 - u.length) false`:
    have hp9 : parityOfIter 9 y = u ++ List.replicate (9 - u.length) false := by
      have hKs9 : K = 9 + (K - 9) := by omega
      have hpar9 := parityOfIter_append_split 9 (K - 9) y
      rw [← hKs9, ← hv_par] at hpar9
      have hsh9 : shift = (9 - u.length) + (K - 9) := by omega
      dsimp [v] at hpar9
      rw [hsh9, replicate_false_split_w5, ← List.append_assoc] at hpar9
      have hlen9 : (u ++ List.replicate (9 - u.length) false).length =
          (parityOfIter 9 y).length := by
        rw [List.length_append, List.length_replicate, parityOfIter_length]; omega
      exact (list_append_inj_left_eq_len _ _ _ _ hlen9 hpar9).1.symm
    have hw7 : parityWeight (parityOfIter 7 y) = parityWeight u := by
      rw [hp7, (affineCarry_append_replicate_false u (7 - u.length)).1]
    have hw9 : parityWeight (parityOfIter 9 y) = parityWeight u := by
      rw [hp9, (affineCarry_append_replicate_false u (9 - u.length)).1]
    -- Reduce both `parityOfIter 7 y` and `parityOfIter 9 y` to `y % 512`:
    have hy_div9 : y = y % 512 + 2 ^ 9 * (y / 512) := by
      have hdm := (Nat.div_add_mod y 512).symm
      have h512 : (2 : Nat) ^ 9 = 512 := rfl
      rw [h512]; omega
    have hy_div7 : y = y % 512 + 2 ^ 7 * (4 * (y / 512)) := by
      have hdm := (Nat.div_add_mod y 512).symm
      have h128 : (2 : Nat) ^ 7 = 128 := rfl
      rw [h128]; omega
    have hpar9_mod : parityOfIter 9 y = parityOfIter 9 (y % 512) := by
      conv => lhs; rw [hy_div9]
      exact parityOfIter_mod_pow2_shift 9 (y % 512) (y / 512)
    have hpar7_mod : parityOfIter 7 y = parityOfIter 7 (y % 512) := by
      conv => lhs; rw [hy_div7]
      exact parityOfIter_mod_pow2_shift 7 (y % 512) (4 * (y / 512))
    have hb512 : isSurvivingMod512Bool (y % 512) = true :=
      survivingMod512_imp_bool_true (y % 512) hs.1
    have hlt_wt := survivingMod512Bool_nine_gt_seven_weight
      (y % 512) (Nat.mod_lt y (by decide)) hb512
    rw [← hpar7_mod, ← hpar9_mod, hw7, hw9] at hlt_wt
    omega

/--
  Sharpened Unique First-Hit Range Target (`Mod373248UniqueFirstHitLenGeEightProp`):
  Upgrades `Mod373248UniqueFirstHitWeightGeSixProp` (`W4.5c`) with the sharp core-length
  floor `tail.length ≥ 6` (`(true :: true :: tail).length ≥ 8`) established by `W5.4d`.
-/
def Mod373248UniqueFirstHitLenGeEightProp : Prop :=
  ∀ n : Nat, IsSurvivingMod373248Class n ->
    ∃ (tail : List Bool) (q : Nat),
      IsFirstHitOnePair (true :: true :: tail) q ∧
      parityWeight (true :: true :: tail) ≥ 6 ∧
      tail.length ≥ 6 ∧
      exactBackwardQuotient 1 (true :: true :: tail) q = n

/--
  Theorem W5.4e (`collatz_standard_iff_mod373248_unique_first_hit_len_ge_eight`, zero custom axioms):
  Upgrades `W4.5c` (`collatz_standard_iff_mod373248_unique_first_hit_weight_ge_six`) with
  the unconditional forward core-length bound `tail.length ≥ 6` (`|u| ≥ 8`, sharp at `184111`).
-/
theorem collatz_standard_iff_mod373248_unique_first_hit_len_ge_eight :
    CollatzConjectureStandard ↔ Mod373248UniqueFirstHitLenGeEightProp := by
  rw [collatz_standard_iff_mod373248_unique_first_hit_weight_ge_six]
  constructor
  · intro hprop n hs
    rcases hprop n hs with ⟨tail, q, hfh, hw6, hy_eq⟩
    have hlen6 : tail.length ≥ 6 := by
      by_cases hge : tail.length ≥ 6
      · exact hge
      · have hlen_u : (true :: true :: tail).length ≤ 7 := by
          simp only [List.length_cons]; omega
        have hdisj := one_generator_length_le_seven_never_surviving_mod373248
          (true :: true :: tail) q hfh.1 hlen_u
        rw [hy_eq] at hdisj
        exact False.elim (hdisj hs)
    exact ⟨tail, q, hfh, hw6, hlen6, hy_eq⟩
  · intro hprop n hs
    rcases hprop n hs with ⟨tail, q, hfh, hw6, _, hy_eq⟩
    exact ⟨tail, q, hfh, hw6, hy_eq⟩

-- ----------------------------------------------------------------------------
-- W5.4f: `Π₂⁰` Skolem Box Calibration (`Branch P4.4`) & Polynomial Stopping-Time
--        Contrast on Closer Cousin `T_diamond2` (Zero Custom Axioms)
-- ----------------------------------------------------------------------------

def Mod373248BoundedSkolemWitnessProp (B : Nat -> Nat) : Prop :=
  ∀ n : Nat, IsSurvivingMod373248Class n ->
    ∃ (tail : List Bool) (q : Nat),
      IsFirstHitOnePair (true :: true :: tail) q ∧
      parityWeight (true :: true :: tail) ≥ 6 ∧
      tail.length ≥ 6 ∧
      tail.length ≤ B n ∧
      486 * q ≤ B n ∧
      exactBackwardQuotient 1 (true :: true :: tail) q = n

theorem parityWeight_le_length_w5 : ∀ v : List Bool, parityWeight v ≤ v.length
  | [] => Nat.le_refl 0
  | false :: rest => by
    simp only [parityWeight, List.length_cons]
    have ih := parityWeight_le_length_w5 rest; omega
  | true :: rest => by
    simp only [parityWeight, List.length_cons]
    have ih := parityWeight_le_length_w5 rest; omega

/--
  Theorem W5.4f (`pi2_skolem_box_equivalence_and_cousin_polynomial_stopping_bound`, zero custom axioms):
  `Π₂⁰` Proof-Complexity / Skolem-Function Calibration (`Branch P4.4`):
  1. Any total Skolem box `B : Nat -> Nat` bounding `(tail.length, 486 * q)` on
     `IsSurvivingMod373248Class` unconditionally implies `CollatzConjectureStandard`.
  2. Exact Constructive Skolem Equivalence: a total Skolem box `B` satisfying
     `Mod373248BoundedSkolemWitnessProp B` exists IF AND ONLY IF a total compressed
     stopping-time bound `S : Nat -> Nat` exists on `IsSurvivingMod373248Class`
     (`∀ n, IsSurvivingMod373248Class n -> ∃ k ≤ S n, collatzIter k n = 1`), with
     explicit elementary-recursive mutual bounds (`B = S` forward, and
     `S n = (B n + 2) + (B n + 1) * (2 * 3 ^ (B n + 1))` backward). Thus any totality
     proof of `Mod373248UniqueFirstHitLenGeEightProp` in an arithmetic theory `T` requires
     exact fast-growing-hierarchy strength matching the worst-case compressed stopping time!
  3. Contrast with Closer Cousin `T_diamond2`: even though `T_diamond2` exhibits unbounded
     `(3/2)^K` Mersenne glides and defeats all single valuation monomials and all bounded-
     modulus potentials, its stopping time satisfies the explicit degree-5 polynomial bound
     `∀ x > 0, ∃ k ≤ (x + 1)^3 + (x + 1)^5, cousinDiamond2Iter k x = 1` (provably total
     already in polynomial-exponentiation arithmetic `IΔ₀ + exp` / `PRA`!).
-/
theorem pi2_skolem_box_equivalence_and_cousin_polynomial_stopping_bound :
    ((∃ B : Nat -> Nat, Mod373248BoundedSkolemWitnessProp B) -> CollatzConjectureStandard) ∧
    ((∃ S : Nat -> Nat, ∀ n : Nat, IsSurvivingMod373248Class n ->
        ∃ k : Nat, k ≤ S n ∧ collatzIter k n = 1) ↔
      (∃ B : Nat -> Nat, Mod373248BoundedSkolemWitnessProp B)) ∧
    (∀ x : Nat, x > 0 ->
      ∃ k : Nat, k ≤ (x + 1) ^ 3 + (x + 1) ^ 5 ∧ cousinDiamond2Iter k x = 1) := by
  refine ⟨?_, ?_, cousin_diamond2_global_convergence⟩
  · rintro ⟨B, hB⟩
    apply collatz_standard_iff_mod373248_unique_first_hit_len_ge_eight.mpr
    intro n hs
    rcases hB n hs with ⟨tail, q, hfh, hw6, hlen6, _, _, hy_eq⟩
    exact ⟨tail, q, hfh, hw6, hlen6, hy_eq⟩
  · constructor
    · rintro ⟨S, hS⟩
      refine ⟨S, ?_⟩
      intro n hs
      have hn27 : n ≥ 27 := survivingMod373248_ge_27 n hs
      have hs1296 : IsSurvivingMod1296Class n :=
        (survivingMod46656_imp_mod1296 n (survivingMod373248_imp_mod46656 n hs)).1
      have hn_odd : n % 2 = 1 := by rcases hs1296 with ⟨h16, _, _, _, _⟩; omega
      rcases hS n hs with ⟨k, hk_le, hk1⟩
      rcases firstHitStepsAux_spec k n hk1 with ⟨hk0_le, hk0_eq1, hk0_min⟩
      let k0 := firstHitStepsAux k n
      change k0 ≤ k at hk0_le
      change collatzIter k0 n = 1 at hk0_eq1
      rcases (convergent_odd_gt1_iff_unique_first_hit_pair n).mp ⟨by omega, hn_odd, ⟨k0, hk0_eq1⟩⟩ with
        ⟨u, q, hfh, hy_eq, _⟩
      -- Verify `backwardOneTotalSteps u q = k0`:
      have hsteps_eq : backwardOneTotalSteps u q = k0 := by
        rcases one_generator_pos_odd_and_reaches_one u q hfh.1 with ⟨_, _, _, hiter_u⟩
        rw [hy_eq] at hiter_u
        by_cases hlt1 : backwardOneTotalSteps u q < k0
        · exact False.elim (hk0_min (backwardOneTotalSteps u q) hlt1 hiter_u)
        · by_cases hlt2 : k0 < backwardOneTotalSteps u q
          · have hne := hfh.2 k0 hlt2
            rw [hy_eq] at hne
            exact False.elim (hne hk0_eq1)
          · omega
      have hw_ge6 : parityWeight u ≥ 6 := by
        by_cases hge : parityWeight u ≥ 6
        · exact hge
        · have hdisj := one_generator_weight_le_five_never_surviving_mod373248 u q hfh.1 (by omega)
          rw [hy_eq] at hdisj
          exact False.elim (hdisj hs)
      have hlen_ge8 : u.length ≥ 8 := by
        by_cases hge : u.length ≥ 8
        · exact hge
        · have hdisj := one_generator_length_le_seven_never_surviving_mod373248 u q hfh.1 (by omega)
          rw [hy_eq] at hdisj
          exact False.elim (hdisj hs)
      -- Decompose `u = true :: true :: tail`:
      cases hu_def : u with
      | nil => have hh := hfh.1.1; rw [hu_def] at hh; simp at hh
      | cons b0 t1 =>
        have hb0 : b0 = true := by have hh := hfh.1.1; rw [hu_def] at hh; simp at hh; exact hh
        subst hb0
        cases t1 with
        | nil => subst hu_def; simp at hlen_ge8
        | cons b1 tail =>
          cases b1 with
          | false =>
            subst hu_def
            have hdisj := (one_generator_weight_le_two_never_surviving_mod1296
              (true :: false :: tail) q hfh.1 (Or.inr ⟨tail, rfl⟩)).2.2.2.2
            rw [hy_eq] at hdisj
            exact False.elim (hdisj hs)
          | true =>
            subst hu_def
            have htail_ge6 : tail.length ≥ 6 := by
              simp only [List.length_cons] at hlen_ge8; omega
            have hp3_ge243 : 3 ^ (parityWeight (true :: true :: tail) - 1) ≥ 243 := by
              have hs_w : parityWeight (true :: true :: tail) - 1 =
                  5 + (parityWeight (true :: true :: tail) - 6) := by omega
              rw [hs_w, Nat.pow_add]
              have hp0 := pow3_pos_nat (parityWeight (true :: true :: tail) - 6)
              have h243 : (3 : Nat) ^ 5 = 243 := rfl
              rw [h243]
              have hm := Nat.mul_le_mul_left 243 hp0; omega
            have h486_le : 486 * q ≤ q * (2 * 3 ^ (parityWeight (true :: true :: tail) - 1)) := by
              rw [Nat.mul_comm 486 q]
              exact Nat.mul_le_mul_left q (by omega)
            unfold backwardOneTotalSteps at hsteps_eq
            simp only [List.length_cons] at hsteps_eq
            refine ⟨tail, q, hfh, hw_ge6, htail_ge6, by omega, by omega, hy_eq⟩
    · rintro ⟨B, hB⟩
      refine ⟨fun n => (B n + 2) + (B n + 1) * (2 * 3 ^ (B n + 1)), ?_⟩
      intro n hs
      rcases hB n hs with ⟨tail, q, hfh, hw6, _, htail_le, hq_le, hy_eq⟩
      let u := true :: true :: tail
      rcases one_generator_pos_odd_and_reaches_one u q hfh.1 with ⟨_, _, _, hiter1⟩
      rw [hy_eq] at hiter1
      refine ⟨backwardOneTotalSteps u q, ?_, hiter1⟩
      dsimp only
      unfold backwardOneTotalSteps
      have hu_len : u.length ≤ B n + 2 := by
        change tail.length + 2 ≤ B n + 2; omega
      have hw_le : parityWeight u ≤ B n + 2 :=
        Nat.le_trans (parityWeight_le_length_w5 u) hu_len
      have hp3_le : 3 ^ (parityWeight u - 1) ≤ 3 ^ (B n + 1) := by
        have hd : B n + 1 = (parityWeight u - 1) + ((B n + 1) - (parityWeight u - 1)) := by omega
        rw [hd, Nat.pow_add]
        have hm := Nat.mul_le_mul_left (3 ^ (parityWeight u - 1))
          (pow3_pos_nat ((B n + 1) - (parityWeight u - 1)))
        simpa using hm
      have hcs_lt : canonicalSuffixShift u 1 < 2 * 3 ^ (parityWeight u - 1) :=
        (canonicalSuffixShift_spec_unique u 1 (by dsimp [u]; omega) (by decide)).1
      have hq_le_B : q ≤ B n := by omega
      have hshift_le : canonicalSuffixShift u 1 + q * (2 * 3 ^ (parityWeight u - 1)) ≤
          (B n + 1) * (2 * 3 ^ (B n + 1)) := by
        have h1 : canonicalSuffixShift u 1 ≤ 2 * 3 ^ (B n + 1) := by omega
        have h2 : q * (2 * 3 ^ (parityWeight u - 1)) ≤ B n * (2 * 3 ^ (B n + 1)) :=
          Nat.mul_le_mul hq_le_B (Nat.mul_le_mul_left 2 hp3_le)
        rw [Nat.add_mul (B n) 1, Nat.one_mul, Nat.add_comm (B n * (2 * 3 ^ (B n + 1)))]
        exact Nat.add_le_add h1 h2
      exact Nat.add_le_add hu_len hshift_le

end CollatzFormal
