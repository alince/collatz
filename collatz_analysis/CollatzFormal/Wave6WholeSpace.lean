/-
  CollatzFormal/Wave6WholeSpace.lean
  Wave 6 Whole-Space Mathematical & CS Proof Loop:
  1. Front A — Coupled-Core Non-Periodic Berg–Meinardus Preimage Weights (Branches P1.2 & P1.3):
     - `coupled_core_weight_survives_spine_and_17_yet_fails_mersenne` (zero custom axioms): explicit
       coupled-core weight `w_core(n) = v2Pow(n+1)^2 / (coprime23Core(n)^2 + v3Pow(n+1)^3)`
       decays quadratically along `geomSpineEntry j` and passes `{17->13, 97->73, 169->127}`,
       yet fails on Mersenne glide `7 -> 11`.
     - `berg_meinardus_coupled_core_rational_weight_impossibility` (zero custom axioms): universal
       6-variable barrier refuting ALL positive rational preimage weights built from arbitrary
       multi-term positive polynomials in `(v2Pow n, v3Pow n, coprime23Core n, v2Pow (n+1),
       v3Pow (n+1), coprime23Core (n+1))`.
  2. Front B — Zero-Diagonal 2D Spectral-Cone Matrices, Variable-Horizon Spiral Block-Return
     Barriers, & 3rd Solvable Cousin `T_diamond3` (Branches P4.3 & P5):
     - `sub6_upper_tri_2d_forces_zero_diag_B0`, `zero_diag_upper_tri_2d_r1_sub6_impossibility`,
       `zero_top_left_breaks_left_context_monotonicity_2d` (choice-free),
       `bipartite_zero_diag_swap_r1_impossibility_all_dim`, & `antidiag_swap_2d_r1_impossibility`
       (zero custom axioms): proves zero diagonal `(interp .B0).n = 0` is forced on `{R2, R5, R7,
       R9, R11}`, adding `R1_even` (`[L, B0] -> [L]`) to `{R2, R5, R7, R8, R9, R11}` collapses
       universally across `UpperTri2D`, dropping `(M_s)_{0,0} ≥ 1` breaks left-context rewrite
       monotonicity, and ALL bipartite/antidiagonal swap zero-diagonal matrices (`∀ d ≥ 1`,
       `[[0, P], [Q, 0]]`) collapse unconditionally on `R1_even`.
     - `spiral_block_return_unbounded_climb` & `spiral_block_return_multiterm_laurent_impossibility`
       (zero custom axioms): variable-horizon spiral block-return climbs strictly for `r` blocks
       on `4 * 16^r - 5 -> 4 * 18^r - 5` (`∀ r ≥ 1`) and defeats ALL `L`-term Laurent valuation sums.
     - `cousin_diamond3_outside_cone4_strict_descent`, `cousin_diamond3_cone4_reaches_one_exact`,
       `cousin_diamond3_global_convergence`, `cousin_diamond3_multiterm_laurent_impossibility`,
       `cousinDiamond3StepInt_ofNat_eq` (zero custom axioms), & `cousin_diamond3_counter_model_separation` (`[]` axioms).
  3. Front C — Multiplicative Schneider–Laurent Integer Determinants & 2-Block / `m`-Block
     Multiplicative-Order & Equal-Even-Run Locks (Branches P3.2, P3.3, P3.4):
     - `laurent_interp_2x2_5_8_and_3x3_determinant_cert` (`[]` axioms) &
       `laurent_interp_resonant_row_collapse_and_gap_divisibility` (zero custom axioms).
     - `m_block_antipodal_shared_mersenne_parity_and_mod3_lock` &
       `two_block_shared_mersenne_propagation_and_equal_even_exclusion` (zero custom axioms).
  4. Front D — Cross-Ray Disjointness, `11 + 16 = 27` Prefix Partition & Uniform Fibers, &
     Bounded-Length Exponential Sparsity / Non-Covering (Branch P5.3):
     - `first_hit_ray_global_disjointness_and_q0_necessity` (zero custom axioms).
     - `mod512_surviving_prefix_partition_cert` (choice-free),
       `mod512_surviving_prefix_uniform_fibers`, &
       `surviving_mod512_nine_prefix_auto_weight_and_characterization` (zero custom axioms).
     - `bounded_length_ray_exponential_sparsity_and_noncovering` &
       `bounded_length_ray_logarithmic_counting_zero_density` (zero custom axioms).

  Zero external dependencies (pure Lean 4.35.0 Core), zero `sorry`,
  zero `native_decide`, zero custom `axiom`.
-/

import CollatzFormal.Wave5WholeSpace

namespace CollatzFormal

-- ============================================================================
-- SECTION 1: Front A — Coupled-Core Non-Periodic Berg–Meinardus Preimage
--            Weights & Universal 6-Variable Rational Barrier (Zero Custom Axioms)
-- ============================================================================

def coupledCoreSampleNum (n : Nat) : Nat :=
  (v2Pow (n + 1)) ^ 2

def coupledCoreSampleDen (n : Nat) : Nat :=
  (coprime23Core n) ^ 2 + (v3Pow (n + 1)) ^ 3

/--
  Theorem W6.1a (`coupled_core_weight_survives_spine_and_17_yet_fails_mersenne`, zero custom axioms):
  Coupling `coprime23Core n` with `(v2Pow (n + 1), v3Pow (n + 1))` in
    `w_core(n) = v2Pow(n + 1)^2 / (coprime23Core(n)^2 + v3Pow(n + 1)^3)`
  genuinely cures Wave 5's 4-adic spine divergence (`w_core(geomSpineEntry j) = 4 / (z_j^2 + 1)`)
  AND satisfies strict forward Syracuse growth `w_core(x) < w_core(syracuseOddStep x)` across
  all three dyadic/3-core/coprime-core jump witnesses `{17 -> 13, 97 -> 73, 169 -> 127}`,
  yet FAILS on the Mersenne glide `7 -> 11`!
-/
theorem coupled_core_weight_survives_spine_and_17_yet_fails_mersenne :
    (∀ j : Nat,
      let z := geomSpineEntry j
      coupledCoreSampleNum z = 4 ∧ coupledCoreSampleDen z = z ^ 2 + 1) ∧
    (∀ x : Nat, (x = 17 ∨ x = 97 ∨ x = 169) ->
      coupledCoreSampleNum x * coupledCoreSampleDen (syracuseOddStep x) <
        coupledCoreSampleNum (syracuseOddStep x) * coupledCoreSampleDen x) ∧
    syracuseOddStep 7 = 11 ∧
    coupledCoreSampleNum 7 * coupledCoreSampleDen 11 >
      coupledCoreSampleNum 11 * coupledCoreSampleDen 7 := by
  refine ⟨?_, ?_, by decide, by decide⟩
  · intro j
    dsimp only
    rcases geomSpineEntry_valuations_constant j with ⟨_, _, hv2z, hv3z, hv2zp1, hv3zp1⟩
    let z := geomSpineEntry j
    change v2Pow z = 1 at hv2z
    change v3Pow z = 1 at hv3z
    change v2Pow (z + 1) = 2 at hv2zp1
    change v3Pow (z + 1) = 1 at hv3zp1
    rcases decomp_2_3_exact z (by have := (geomSpineEntry_valuations_constant j).2.1; omega) with
      ⟨_, _, _, _, _, hz_mul⟩
    simp only [hv2z, hv3z, Nat.one_mul, Nat.mul_one] at hz_mul
    unfold coupledCoreSampleNum coupledCoreSampleDen
    rw [hv2zp1, hv3zp1, hz_mul]
    exact ⟨rfl, rfl⟩
  · rintro x (rfl | rfl | rfl) <;> decide

/--
  Reusable 4-adic spine bounded-ratio impossibility lemma (`zero custom axioms`):
  If ANY positive rational preimage weight `(wNum, wDen)` satisfies a uniform bound
  `wDen (geomSpineEntry j) ≤ dMax * wNum (geomSpineEntry j)` (`dMax ≥ 1`) along the
  4-adic spine preimages `z_j = (4^(3*j+4) - 1) / 3`, then `S_j = 4^(3*j + 1)` drains
  at least `1 / dMax` at every `j` and contradicts positivity at `J = dMax * wNum 4 + 1`.
-/
theorem spine_bounded_ratio_preimage_impossibility
    (wNum wDen : Nat -> Nat) (pTheta qTheta dMax : Nat)
    (_hdMax_pos : dMax ≥ 1)
    (hw : IsPositiveRationalPreimageWeight wNum wDen pTheta qTheta)
    (hratio : ∀ j : Nat, wDen (geomSpineEntry j) ≤ dMax * wNum (geomSpineEntry j)) :
    False := by
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
    have hzj_ge : zj ≥ 85 := (geomSpineEntry_valuations_constant j).2.1
    have hle_pq : pTheta * (wNum mj * (wDen (S (j + 1)) * wDen zj)) ≤
        qTheta * (wNum mj * (wDen (S (j + 1)) * wDen zj)) :=
      Nat.mul_le_mul_right _ hw.2.1
    have hsplit_mj : (wNum (S (j + 1)) * wDen zj + wNum zj * wDen (S (j + 1))) * wDen mj ≤
        wNum mj * (wDen (S (j + 1)) * wDen zj) :=
      nat_mul_le_cancel_left_w5 qTheta _ _ (Nat.lt_of_lt_of_le hw.1 hw.2.1) (Nat.le_trans hpre_mj hle_pq)
    have hden_zj_pos : wDen zj > 0 := (hw.2.2.1 zj (by omega)).2
    have hden_mj_pos : wDen mj > 0 := (hw.2.2.1 mj (by dsimp [mj]; omega)).2
    have hzj_ratio : wDen zj ≤ dMax * wNum zj := hratio j
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

/--
  6-variable coupled valuation/core monomial term in
  `(v2Pow n, v3Pow n, coprime23Core n, v2Pow (n+1), v3Pow (n+1), coprime23Core (n+1))`.
  Note: Clearing any negative exponents `(A0, B0, G0, A1, B1, G1)` into both numerator and
  denominator reduces EVERY rational function of arbitrary-sign 6-variable Laurent valuation/core
  combinations to `evalCoupledCorePoly pTerms n / evalCoupledCorePoly qTerms n`.
-/
structure CoupledCoreTerm where
  coeff : Nat
  a0Exp : Nat
  b0Exp : Nat
  g0Exp : Nat
  a1Exp : Nat
  b1Exp : Nat
  g1Exp : Nat
  deriving DecidableEq, Repr

def evalCoupledCoreMono (t : CoupledCoreTerm) (n : Nat) : Nat :=
  (v2Pow n) ^ t.a0Exp * (v3Pow n) ^ t.b0Exp * (coprime23Core n) ^ t.g0Exp *
    ((v2Pow (n + 1)) ^ t.a1Exp * (v3Pow (n + 1)) ^ t.b1Exp * (coprime23Core (n + 1)) ^ t.g1Exp)

def evalCoupledCorePoly : List CoupledCoreTerm -> Nat -> Nat
  | [], _ => 0
  | t :: rest, n => t.coeff * evalCoupledCoreMono t n + evalCoupledCorePoly rest n

def sumCoupledCoeffs : List CoupledCoreTerm -> Nat
  | [] => 0
  | t :: rest => t.coeff + sumCoupledCoeffs rest

def maxCoupledAlpha : List CoupledCoreTerm -> Nat
  | [] => 0
  | t :: rest =>
    if t.coeff > 0 then Nat.max (t.a1Exp + t.g0Exp) (maxCoupledAlpha rest)
    else maxCoupledAlpha rest

def maxCoupledBeta : List CoupledCoreTerm -> Nat
  | [] => 0
  | t :: rest =>
    if t.coeff > 0 then Nat.max (t.b1Exp + t.g0Exp) (maxCoupledBeta rest)
    else maxCoupledBeta rest

def maxCoupledGamma : List CoupledCoreTerm -> Nat
  | [] => 0
  | t :: rest =>
    if t.coeff > 0 then Nat.max (t.g1Exp + t.g0Exp) (maxCoupledGamma rest)
    else maxCoupledGamma rest

theorem active_coupled_le_max :
    ∀ (ts : List CoupledCoreTerm) (t : CoupledCoreTerm),
      t ∈ ts -> t.coeff > 0 ->
      t.a1Exp + t.g0Exp ≤ maxCoupledAlpha ts ∧
      t.b1Exp + t.g0Exp ≤ maxCoupledBeta ts ∧
      t.g1Exp + t.g0Exp ≤ maxCoupledGamma ts
  | [], _, hm, _ => by cases hm
  | hd :: rest, t, hm, hp => by
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hrest
    · simp only [maxCoupledAlpha, maxCoupledBeta, maxCoupledGamma, hp, ite_true]
      exact ⟨Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _⟩
    · rcases active_coupled_le_max rest t hrest hp with ⟨ha, hb, hg⟩
      simp only [maxCoupledAlpha, maxCoupledBeta, maxCoupledGamma]
      by_cases hhd : hd.coeff > 0
      · simp only [hhd, ite_true]
        exact ⟨Nat.le_trans ha (Nat.le_max_right _ _),
               Nat.le_trans hb (Nat.le_max_right _ _),
               Nat.le_trans hg (Nat.le_max_right _ _)⟩
      · simp only [hhd, ite_false]
        exact ⟨ha, hb, hg⟩

theorem exists_active_coupled_achieving_max :
    ∀ (ts : List CoupledCoreTerm),
      (∃ t ∈ ts, t.coeff > 0) ->
      sumCoupledCoeffs ts ≥ 1 ∧
      (∃ tA ∈ ts, tA.coeff > 0 ∧ tA.a1Exp + tA.g0Exp = maxCoupledAlpha ts) ∧
      (∃ tB ∈ ts, tB.coeff > 0 ∧ tB.b1Exp + tB.g0Exp = maxCoupledBeta ts) ∧
      (∃ tG ∈ ts, tG.coeff > 0 ∧ tG.g1Exp + tG.g0Exp = maxCoupledGamma ts)
  | [], ⟨_, hm, _⟩ => by cases hm
  | hd :: rest, hex => by
    by_cases hrest_ex : ∃ t ∈ rest, t.coeff > 0
    · rcases exists_active_coupled_achieving_max rest hrest_ex with
        ⟨hsum_r, ⟨tA, hmA, hpA, heA⟩, ⟨tB, hmB, hpB, heB⟩, ⟨tG, hmG, hpG, heG⟩⟩
      simp only [sumCoupledCoeffs, maxCoupledAlpha, maxCoupledBeta, maxCoupledGamma]
      refine ⟨by omega, ?_⟩
      if hhd : hd.coeff > 0 then
        simp only [hhd, ite_true]
        refine ⟨?_, ?_, ?_⟩
        · by_cases hge : maxCoupledAlpha rest ≤ hd.a1Exp + hd.g0Exp
          · exact ⟨hd, List.Mem.head _, hhd, (Nat.max_eq_left hge).symm⟩
          · exact ⟨tA, List.mem_cons_of_mem _ hmA, hpA, heA.trans (Nat.max_eq_right (by omega)).symm⟩
        · by_cases hge : maxCoupledBeta rest ≤ hd.b1Exp + hd.g0Exp
          · exact ⟨hd, List.Mem.head _, hhd, (Nat.max_eq_left hge).symm⟩
          · exact ⟨tB, List.mem_cons_of_mem _ hmB, hpB, heB.trans (Nat.max_eq_right (by omega)).symm⟩
        · by_cases hge : maxCoupledGamma rest ≤ hd.g1Exp + hd.g0Exp
          · exact ⟨hd, List.Mem.head _, hhd, (Nat.max_eq_left hge).symm⟩
          · exact ⟨tG, List.mem_cons_of_mem _ hmG, hpG, heG.trans (Nat.max_eq_right (by omega)).symm⟩
      else
        simp only [hhd, ite_false]
        exact ⟨⟨tA, List.mem_cons_of_mem _ hmA, hpA, heA⟩,
               ⟨tB, List.mem_cons_of_mem _ hmB, hpB, heB⟩,
               ⟨tG, List.mem_cons_of_mem _ hmG, hpG, heG⟩⟩
    · rcases hex with ⟨t0, hm0, hp0⟩
      simp only [List.mem_cons] at hm0
      rcases hm0 with rfl | hr0
      · have hzero : ∀ (r : List CoupledCoreTerm), (¬ ∃ t ∈ r, t.coeff > 0) ->
            maxCoupledAlpha r = 0 ∧ maxCoupledBeta r = 0 ∧ maxCoupledGamma r = 0 := by
          intro r hnr
          induction r with
          | nil => exact ⟨rfl, rfl, rfl⟩
          | cons u ur ih =>
            have hu0 : ¬ (u.coeff > 0) := fun hp => hnr ⟨u, List.Mem.head _, hp⟩
            have hnur : ¬ (∃ t ∈ ur, t.coeff > 0) :=
              fun ⟨t, hm, hp⟩ => hnr ⟨t, List.mem_cons_of_mem _ hm, hp⟩
            simp only [maxCoupledAlpha, maxCoupledBeta, maxCoupledGamma, hu0, ite_false]
            exact ih hnur
        rcases hzero rest hrest_ex with ⟨ha0, hb0, hg0⟩
        simp only [sumCoupledCoeffs, maxCoupledAlpha, maxCoupledBeta, maxCoupledGamma,
                   hp0, ite_true, ha0, hb0, hg0, Nat.max_zero]
        exact ⟨by omega,
               ⟨t0, List.Mem.head _, hp0, rfl⟩,
               ⟨t0, List.Mem.head _, hp0, rfl⟩,
               ⟨t0, List.Mem.head _, hp0, rfl⟩⟩
      · exact False.elim (hrest_ex ⟨t0, hr0, hp0⟩)

theorem evalCoupledCorePoly_ge_active :
    ∀ (ts : List CoupledCoreTerm) (t : CoupledCoreTerm) (n : Nat),
      t ∈ ts -> t.coeff > 0 -> evalCoupledCoreMono t n ≤ evalCoupledCorePoly ts n
  | [], _, _, hm, _ => by cases hm
  | hd :: rest, t, n, hm, hp => by
    simp only [List.mem_cons] at hm
    simp only [evalCoupledCorePoly]
    rcases hm with rfl | hrest
    · have h1 : 1 * evalCoupledCoreMono t n ≤ t.coeff * evalCoupledCoreMono t n :=
        Nat.mul_le_mul_right _ hp
      rw [Nat.one_mul] at h1; omega
    · have ih := evalCoupledCorePoly_ge_active rest t n hrest hp
      omega

theorem evalCoupledCorePoly_le_sum_mul :
    ∀ (ts : List CoupledCoreTerm) (n M : Nat),
      (∀ t ∈ ts, t.coeff > 0 -> evalCoupledCoreMono t n ≤ M) ->
      evalCoupledCorePoly ts n ≤ sumCoupledCoeffs ts * M
  | [], _, _, _ => by simp [evalCoupledCorePoly, sumCoupledCoeffs]
  | hd :: rest, n, M, hbdd => by
    simp only [evalCoupledCorePoly, sumCoupledCoeffs, Nat.add_mul]
    have ih := evalCoupledCorePoly_le_sum_mul rest n M
      (fun t hm hp => hbdd t (List.mem_cons_of_mem _ hm) hp)
    by_cases hhd : hd.coeff > 0
    · exact Nat.add_le_add (Nat.mul_le_mul_left hd.coeff (hbdd hd (List.Mem.head _) hhd)) ih
    · have hc0 : hd.coeff = 0 := by omega
      rw [hc0]; simp only [Nat.zero_mul, Nat.zero_add]; exact ih

theorem nat_pow_mono_exp_pos (b e1 e2 : Nat) (hb : b ≥ 1) (hle : e1 ≤ e2) :
    b ^ e1 ≤ b ^ e2 := by
  have hd : e2 = e1 + (e2 - e1) := by omega
  rw [hd, Nat.pow_add]
  have hm := Nat.mul_le_mul_left (b ^ e1) (nat_pow_pos_of_pos b hb (e2 - e1))
  simpa using hm

/--
  Unified valuation/core polynomial sandwich at any odd `x ≥ 3` with `x % 3 ≠ 0`:
  1. When `x + 1 = 2 * U` with `U ≥ 1` odd and `U % 3 ≠ 0` (`(a1, b1, g1) = (2, 1, U)`):
     `U ^ (maxCoupledGamma ts) ≤ evalCoupledCorePoly ts x ≤ sumCoupledCoeffs ts * 2 ^ (maxCoupledAlpha ts) * U ^ (maxCoupledGamma ts)`.
  2. When `x + 1 = 2 * 9^k` (`k ≥ 1`, `(a1, b1, g1) = (2, 9^k, 1)`):
     `9 ^ (k * maxCoupledBeta ts) ≤ evalCoupledCorePoly ts x ≤ sumCoupledCoeffs ts * 2 ^ (maxCoupledAlpha ts) * 9 ^ (k * maxCoupledBeta ts)`.
  3. When `x + 1 = 2 * M` with `M = 2 ^ m` (`m ≥ 1`, `(a1, b1, g1) = (2 * M, 1, 1)`):
     `M ^ (maxCoupledAlpha ts) ≤ evalCoupledCorePoly ts x ≤ sumCoupledCoeffs ts * 2 ^ (maxCoupledAlpha ts) * M ^ (maxCoupledAlpha ts)`.
-/
theorem evalCoupledCorePoly_two_mul_coprime_bounds
    (ts : List CoupledCoreTerm) (x U : Nat)
    (hne : ∃ t ∈ ts, t.coeff > 0)
    (hx_odd : x % 2 = 1) (hx_nd3 : x % 3 ≠ 0)
    (hU_pos : U ≥ 1) (hU_odd : U % 2 = 1) (hU_nd3 : U % 3 ≠ 0)
    (hxp1 : x + 1 = 2 * U) :
    U ^ (maxCoupledGamma ts) ≤ evalCoupledCorePoly ts x ∧
    evalCoupledCorePoly ts x ≤
      (sumCoupledCoeffs ts * 2 ^ (maxCoupledAlpha ts)) * U ^ (maxCoupledGamma ts) := by
  rcases exists_active_coupled_achieving_max ts hne with
    ⟨_, _, _, ⟨tG, hmG, hpG, heG⟩⟩
  have hv2x : v2Pow x = 1 := v2Pow_of_odd x hx_odd
  have hv3x : v3Pow x = 1 := v3Pow_of_not_div3 x hx_nd3
  have hgx : coprime23Core x = x := coprime23Core_of_coprime x hx_odd hx_nd3
  have hv2_1 : v2Pow (x + 1) = 2 := by rw [hxp1, v2Pow_mul2 U hU_pos, v2Pow_of_odd U hU_odd]
  have hv3_1 : v3Pow (x + 1) = 1 := by rw [hxp1, v3Pow_mul2 U hU_pos, v3Pow_of_not_div3 U hU_nd3]
  have hg_1 : coprime23Core (x + 1) = U := by
    rw [hxp1, coprime23Core_mul2 U hU_pos, coprime23Core_of_coprime U hU_odd hU_nd3]
  have hx_ge_U : U ≤ x := by omega
  have hx_le_2U : x ≤ 2 * U := by omega
  refine ⟨?_, ?_⟩
  · have hge := evalCoupledCorePoly_ge_active ts tG x hmG hpG
    unfold evalCoupledCoreMono at hge
    simp only [hv2x, hv3x, hgx, hv2_1, hv3_1, hg_1,
               Nat.one_pow, Nat.one_mul, Nat.mul_one] at hge
    have h1 : U ^ tG.g0Exp * (1 * U ^ tG.g1Exp) ≤
        x ^ tG.g0Exp * (2 ^ tG.a1Exp * U ^ tG.g1Exp) :=
      Nat.mul_le_mul (nat_pow_mono_base U x hx_ge_U tG.g0Exp)
        (Nat.mul_le_mul_right _ (pow2_pos_nat tG.a1Exp))
    rw [Nat.one_mul, ← Nat.pow_add U tG.g0Exp tG.g1Exp, Nat.add_comm tG.g0Exp tG.g1Exp, heG] at h1
    exact Nat.le_trans h1 hge
  · rw [Nat.mul_assoc]
    apply evalCoupledCorePoly_le_sum_mul
    intro t hm hp
    rcases active_coupled_le_max ts t hm hp with ⟨ha_le, _, hg_le⟩
    unfold evalCoupledCoreMono
    simp only [hv2x, hv3x, hgx, hv2_1, hv3_1, hg_1,
               Nat.one_pow, Nat.one_mul, Nat.mul_one]
    have hx_ub : x ^ t.g0Exp ≤ 2 ^ t.g0Exp * U ^ t.g0Exp := by
      rw [← mul_pow_local 2 U t.g0Exp]; exact nat_pow_mono_base x (2 * U) hx_le_2U t.g0Exp
    have hm1 := Nat.mul_le_mul_right (2 ^ t.a1Exp * U ^ t.g1Exp) hx_ub
    have hrw : (2 ^ t.g0Exp * U ^ t.g0Exp) * (2 ^ t.a1Exp * U ^ t.g1Exp) =
        2 ^ (t.a1Exp + t.g0Exp) * U ^ (t.g1Exp + t.g0Exp) := by
      calc
        (2 ^ t.g0Exp * U ^ t.g0Exp) * (2 ^ t.a1Exp * U ^ t.g1Exp)
            = 2 ^ t.g0Exp * (U ^ t.g0Exp * (2 ^ t.a1Exp * U ^ t.g1Exp)) := Nat.mul_assoc _ _ _
        _ = 2 ^ t.g0Exp * (2 ^ t.a1Exp * (U ^ t.g0Exp * U ^ t.g1Exp)) := by
              rw [← Nat.mul_assoc (U ^ t.g0Exp), Nat.mul_comm (U ^ t.g0Exp) (2 ^ t.a1Exp), Nat.mul_assoc]
        _ = (2 ^ t.a1Exp * 2 ^ t.g0Exp) * (U ^ t.g1Exp * U ^ t.g0Exp) := by
              rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ t.g0Exp) (2 ^ t.a1Exp),
                  Nat.mul_comm (U ^ t.g0Exp) (U ^ t.g1Exp)]
        _ = 2 ^ (t.a1Exp + t.g0Exp) * U ^ (t.g1Exp + t.g0Exp) := by rw [← Nat.pow_add, ← Nat.pow_add]
    rw [hrw] at hm1
    exact Nat.le_trans hm1
      (Nat.mul_le_mul (pow2_mono_nat ha_le) (nat_pow_mono_exp_pos U _ _ hU_pos hg_le))

theorem evalCoupledCorePoly_two_mul_pow9_bounds
    (ts : List CoupledCoreTerm) (k : Nat)
    (hne : ∃ t ∈ ts, t.coeff > 0) (hk : k ≥ 1) :
    let x := 2 * 9 ^ k - 1
    9 ^ (k * maxCoupledBeta ts) ≤ evalCoupledCorePoly ts x ∧
    evalCoupledCorePoly ts x ≤
      (sumCoupledCoeffs ts * 2 ^ (maxCoupledAlpha ts)) * 9 ^ (k * maxCoupledBeta ts) := by
  dsimp only
  let x := 2 * 9 ^ k - 1
  rcases exists_active_coupled_achieving_max ts hne with
    ⟨_, _, ⟨tB, hmB, hpB, heB⟩, _⟩
  have hp9_ge9 : 9 ^ k ≥ 9 := by
    rw [show k = (k - 1) + 1 by omega, Nat.pow_succ]
    have hp0 := nat_pow_pos_of_pos 9 (by decide) (k - 1); omega
  have hp9_m8 : 9 ^ k % 8 = 1 := pow9_mod8_eq_one_w5 k
  have hp9_div3 : 9 ^ k % 3 = 0 := by
    rw [show k = (k - 1) + 1 by omega, Nat.pow_succ]; omega
  have hx_odd : x % 2 = 1 := by dsimp [x]; omega
  have hx_nd3 : x % 3 ≠ 0 := by dsimp [x]; omega
  have hxp1 : x + 1 = 2 * 9 ^ k := by dsimp [x]; omega
  rcases pow9_eq_v3Pow_w5 k with ⟨hv3_9k, hc3_9k⟩
  have hv2x : v2Pow x = 1 := v2Pow_of_odd x hx_odd
  have hv3x : v3Pow x = 1 := v3Pow_of_not_div3 x hx_nd3
  have hgx : coprime23Core x = x := coprime23Core_of_coprime x hx_odd hx_nd3
  have hv2_1 : v2Pow (x + 1) = 2 := by
    rw [hxp1, v2Pow_mul2 (9 ^ k) (by omega), v2Pow_of_odd (9 ^ k) (by omega)]
  have hv3_1 : v3Pow (x + 1) = 9 ^ k := by rw [hxp1, v3Pow_mul2 (9 ^ k) (by omega), hv3_9k]
  have hg_1 : coprime23Core (x + 1) = 1 := by
    rw [hxp1, coprime23Core_mul2 (9 ^ k) (by omega)]
    unfold coprime23Core; rw [hc3_9k]; decide
  have hx_ge : 9 ^ k ≤ x := by dsimp [x]; omega
  have hx_le : x ≤ 2 * 9 ^ k := by dsimp [x]; omega
  refine ⟨?_, ?_⟩
  · have hge := evalCoupledCorePoly_ge_active ts tB x hmB hpB
    unfold evalCoupledCoreMono at hge
    simp only [hv2x, hv3x, hgx, hv2_1, hv3_1, hg_1,
               Nat.one_pow, Nat.one_mul, Nat.mul_one] at hge
    have h1 : (9 ^ k) ^ tB.g0Exp * (1 * (9 ^ k) ^ tB.b1Exp) ≤
        x ^ tB.g0Exp * (2 ^ tB.a1Exp * (9 ^ k) ^ tB.b1Exp) :=
      Nat.mul_le_mul (nat_pow_mono_base (9 ^ k) x hx_ge tB.g0Exp)
        (Nat.mul_le_mul_right _ (pow2_pos_nat tB.a1Exp))
    rw [Nat.one_mul, ← Nat.pow_add (9 ^ k) tB.g0Exp tB.b1Exp,
        Nat.add_comm tB.g0Exp tB.b1Exp, heB, pow_pow_eq_mul_w5 9 k] at h1
    exact Nat.le_trans h1 hge
  · rw [Nat.mul_assoc]
    apply evalCoupledCorePoly_le_sum_mul
    intro t hm hp
    rcases active_coupled_le_max ts t hm hp with ⟨ha_le, hb_le, _⟩
    change evalCoupledCoreMono t x ≤ _
    unfold evalCoupledCoreMono
    simp only [hv2x, hv3x, hgx, hv2_1, hv3_1, hg_1,
               Nat.one_pow, Nat.one_mul, Nat.mul_one]
    have hx_ub : x ^ t.g0Exp ≤ 2 ^ t.g0Exp * (9 ^ k) ^ t.g0Exp := by
      rw [← mul_pow_local 2 (9 ^ k) t.g0Exp]; exact nat_pow_mono_base x (2 * 9 ^ k) hx_le t.g0Exp
    have hm1 := Nat.mul_le_mul_right (2 ^ t.a1Exp * (9 ^ k) ^ t.b1Exp) hx_ub
    have hrw : (2 ^ t.g0Exp * (9 ^ k) ^ t.g0Exp) * (2 ^ t.a1Exp * (9 ^ k) ^ t.b1Exp) =
        2 ^ (t.a1Exp + t.g0Exp) * 9 ^ (k * (t.b1Exp + t.g0Exp)) := by
      calc
        (2 ^ t.g0Exp * (9 ^ k) ^ t.g0Exp) * (2 ^ t.a1Exp * (9 ^ k) ^ t.b1Exp)
            = 2 ^ t.g0Exp * ((9 ^ k) ^ t.g0Exp * (2 ^ t.a1Exp * (9 ^ k) ^ t.b1Exp)) := Nat.mul_assoc _ _ _
        _ = 2 ^ t.g0Exp * (2 ^ t.a1Exp * ((9 ^ k) ^ t.g0Exp * (9 ^ k) ^ t.b1Exp)) := by
              rw [← Nat.mul_assoc ((9 ^ k) ^ t.g0Exp),
                  Nat.mul_comm ((9 ^ k) ^ t.g0Exp) (2 ^ t.a1Exp), Nat.mul_assoc]
        _ = (2 ^ t.a1Exp * 2 ^ t.g0Exp) * ((9 ^ k) ^ t.b1Exp * (9 ^ k) ^ t.g0Exp) := by
              rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ t.g0Exp) (2 ^ t.a1Exp),
                  Nat.mul_comm ((9 ^ k) ^ t.g0Exp) ((9 ^ k) ^ t.b1Exp)]
        _ = 2 ^ (t.a1Exp + t.g0Exp) * 9 ^ (k * (t.b1Exp + t.g0Exp)) := by
              rw [← Nat.pow_add, ← Nat.pow_add, pow_pow_eq_mul_w5 9 k]
    rw [hrw] at hm1
    exact Nat.le_trans hm1
      (Nat.mul_le_mul (pow2_mono_nat ha_le)
        (nat_pow_mono_exp_pos 9 _ _ (by decide) (Nat.mul_le_mul_left k hb_le)))

theorem evalCoupledCorePoly_odd_pow2_bounds
    (ts : List CoupledCoreTerm) (e : Nat)
    (hne : ∃ t ∈ ts, t.coeff > 0) (he : e ≥ 1) :
    let M := 4 ^ e
    let x := 2 * M - 1
    M ^ (maxCoupledAlpha ts) ≤ evalCoupledCorePoly ts x ∧
    evalCoupledCorePoly ts x ≤
      (sumCoupledCoeffs ts * 2 ^ (maxCoupledAlpha ts)) * M ^ (maxCoupledAlpha ts) := by
  dsimp only
  let M := 4 ^ e
  let x := 2 * M - 1
  rcases exists_active_coupled_achieving_max ts hne with
    ⟨_, ⟨tA, hmA, hpA, heA⟩, _, _⟩
  have hM_ge4 : M ≥ 4 := (pow4_ge_four_and_mod3_w5 (e - 1)).1 |> fun h => by
    have heq : e - 1 + 1 = e := by omega
    dsimp [M]; rwa [heq] at h
  have hM_m3 : M % 3 = 1 := by
    have hm := (pow4_ge_four_and_mod3_w5 (e - 1)).2
    have heq : e - 1 + 1 = e := by omega
    dsimp [M]; rwa [heq] at hm
  have hM_pow2 : M = 2 ^ (2 * e) := pow4_eq_pow2_even e
  have hxp1 : x + 1 = 2 ^ (2 * e + 1) := by
    dsimp [x]; rw [hM_pow2, Nat.pow_succ, Nat.mul_comm]
    have hp := pow2_pos_nat (2 * e); omega
  have hx_odd : x % 2 = 1 := by dsimp [x]; omega
  have hx_nd3 : x % 3 ≠ 0 := by dsimp [x]; omega
  rcases pow2_eq_v2Pow_w5 (2 * e + 1) with ⟨hv2_raw, hv3_raw, hg_raw⟩
  have h2M_eq : 2 ^ (2 * e + 1) = 2 * M := by rw [hM_pow2, Nat.pow_succ, Nat.mul_comm]
  have hv2_1 : v2Pow (x + 1) = 2 * M := by rw [hxp1, hv2_raw, h2M_eq]
  have hv3_1 : v3Pow (x + 1) = 1 := by rw [hxp1, hv3_raw]
  have hg_1 : coprime23Core (x + 1) = 1 := by rw [hxp1, hg_raw]
  have hv2x : v2Pow x = 1 := v2Pow_of_odd x hx_odd
  have hv3x : v3Pow x = 1 := v3Pow_of_not_div3 x hx_nd3
  have hgx : coprime23Core x = x := coprime23Core_of_coprime x hx_odd hx_nd3
  have hx_ge_M : M ≤ x := by dsimp [x]; omega
  have hx_le_2M : x ≤ 2 * M := by dsimp [x]; omega
  refine ⟨?_, ?_⟩
  · have hge := evalCoupledCorePoly_ge_active ts tA x hmA hpA
    unfold evalCoupledCoreMono at hge
    simp only [hv2x, hv3x, hgx, hv2_1, hv3_1, hg_1,
               Nat.one_pow, Nat.one_mul, Nat.mul_one] at hge
    have h1 : M ^ tA.g0Exp * M ^ tA.a1Exp ≤ x ^ tA.g0Exp * (2 * M) ^ tA.a1Exp :=
      Nat.mul_le_mul (nat_pow_mono_base M x hx_ge_M tA.g0Exp)
        (nat_pow_mono_base M (2 * M) (by omega) tA.a1Exp)
    rw [← Nat.pow_add M tA.g0Exp tA.a1Exp, Nat.add_comm tA.g0Exp tA.a1Exp, heA] at h1
    exact Nat.le_trans h1 hge
  · rw [Nat.mul_assoc]
    apply evalCoupledCorePoly_le_sum_mul
    intro t hm hp
    rcases active_coupled_le_max ts t hm hp with ⟨ha_le, _, _⟩
    change evalCoupledCoreMono t x ≤ _
    unfold evalCoupledCoreMono
    simp only [hv2x, hv3x, hgx, hv2_1, hv3_1, hg_1,
               Nat.one_pow, Nat.one_mul, Nat.mul_one]
    have hx_ub : x ^ t.g0Exp ≤ (2 * M) ^ t.g0Exp := nat_pow_mono_base x (2 * M) hx_le_2M t.g0Exp
    have hm1 := Nat.mul_le_mul_right ((2 * M) ^ t.a1Exp) hx_ub
    rw [← Nat.pow_add (2 * M) t.g0Exp t.a1Exp, Nat.add_comm t.g0Exp t.a1Exp,
        mul_pow_local 2 M (t.a1Exp + t.g0Exp)] at hm1
    exact Nat.le_trans hm1
      (Nat.mul_le_mul (pow2_mono_nat ha_le) (nat_pow_mono_exp_pos M _ _ (by omega) ha_le))

/--
  Theorem W6.1b (`berg_meinardus_coupled_core_rational_weight_impossibility`, zero custom axioms):
  Universal 6-Variable Coupled-Core Berg–Meinardus Impossibility Barrier:
  NO positive rational weight `w(n) = evalCoupledCorePoly pTerms n / evalCoupledCorePoly qTerms n`
  built from multi-term positive polynomials in all six `(2, 3)`-adic valuation and coprime-core
  coordinates `(v2Pow n, v3Pow n, coprime23Core n, v2Pow (n+1), v3Pow (n+1), coprime23Core (n+1))`
  can satisfy `IsPositiveRationalPreimageWeight` (`θ = pTheta / qTheta ≤ 1`)!
-/
theorem berg_meinardus_coupled_core_rational_weight_impossibility
    (pTerms qTerms : List CoupledCoreTerm) (pTheta qTheta : Nat)
    (hp_ne : ∃ t ∈ pTerms, t.coeff > 0)
    (hq_ne : ∃ t ∈ qTerms, t.coeff > 0)
    (hw : IsPositiveRationalPreimageWeight
      (evalCoupledCorePoly pTerms) (evalCoupledCorePoly qTerms) pTheta qTheta) :
    False := by
  let P := evalCoupledCorePoly pTerms
  let Q := evalCoupledCorePoly qTerms
  change IsPositiveRationalPreimageWeight P Q pTheta qTheta at hw
  let aP := maxCoupledAlpha pTerms
  let bP := maxCoupledBeta pTerms
  let gP := maxCoupledGamma pTerms
  let aQ := maxCoupledAlpha qTerms
  let bQ := maxCoupledBeta qTerms
  let gQ := maxCoupledGamma qTerms
  have hsumP_pos : sumCoupledCoeffs pTerms ≥ 1 := (exists_active_coupled_achieving_max pTerms hp_ne).1
  have hsumQ_pos : sumCoupledCoeffs qTerms ≥ 1 := (exists_active_coupled_achieving_max qTerms hq_ne).1
  -- Step 1: 4-adic spine `z_j = geomSpineEntry j` forces `gP + 1 ≤ gQ`:
  have hgP_lt_gQ : gP + 1 ≤ gQ := by
    by_cases hlt : gP + 1 ≤ gQ
    · exact hlt
    · exfalso
      have hgQ_le : gQ ≤ gP := by omega
      let dMax := sumCoupledCoeffs qTerms * 2 ^ aQ
      have hdMax_pos : dMax ≥ 1 := Nat.mul_le_mul hsumQ_pos (pow2_pos_nat aQ)
      apply spine_bounded_ratio_preimage_impossibility P Q pTheta qTheta dMax hdMax_pos hw
      intro j
      let z := geomSpineEntry j
      rcases geomSpineEntry_valuations_constant j with ⟨h3z1, hz_ge85, _, _, _, _⟩
      change 3 * z + 1 = 4 ^ (3 * j + 4) at h3z1
      change z ≥ 85 at hz_ge85
      have hp4_m3 : 4 ^ (3 * j + 4) % 3 = 1 := (pow4_ge_four_and_mod3_w5 (3 * j + 3)).2
      have hp4_m9 : 4 ^ (3 * j + 4) % 9 = 4 := by
        rw [Nat.pow_add 4 (3 * j) 4, pow4_triple_eq_pow64_w5 j,
            Nat.mul_mod, pow64_mod9_eq_one_w5 j]
      have hz_odd : z % 2 = 1 := by
        have hev : (3 * z + 1) % 2 = 0 := by
          rw [h3z1, show 3 * j + 4 = (3 * j + 3) + 1 by omega, Nat.pow_succ]; omega
        omega
      have hz_m3 : z % 3 = 1 := by omega
      let u := (z + 1) / 2
      have hzp1 : z + 1 = 2 * u := by dsimp [u]; omega
      have hu_pos : u ≥ 43 := by dsimp [u]; omega
      have hu_odd : u % 2 = 1 := by
        have h3u : 6 * u = 4 ^ (3 * j + 4) + 2 := by omega
        have hm4 : (4 ^ (3 * j + 4) + 2) % 4 = 2 := by
          rw [show 3 * j + 4 = (3 * j + 3) + 1 by omega, Nat.pow_succ]; omega
        omega
      have hu_nd3 : u % 3 ≠ 0 := by omega
      have hP_lo := (evalCoupledCorePoly_two_mul_coprime_bounds pTerms z u hp_ne
        hz_odd (by omega) (by omega) hu_odd hu_nd3 hzp1).1
      have hQ_hi := (evalCoupledCorePoly_two_mul_coprime_bounds qTerms z u hq_ne
        hz_odd (by omega) (by omega) hu_odd hu_nd3 hzp1).2
      change u ^ gP ≤ P z at hP_lo
      change Q z ≤ dMax * u ^ gQ at hQ_hi
      have hu_mono : u ^ gQ ≤ u ^ gP := nat_pow_mono_exp_pos u gQ gP (by omega) hgQ_le
      exact Nat.le_trans hQ_hi (Nat.mul_le_mul_left dMax (Nat.le_trans hu_mono hP_lo))
  let dg := gQ - gP
  have hdg_pos : dg ≥ 1 := by dsimp [dg]; omega
  have hgQ_eq : gQ = gP + dg := by dsimp [dg]; omega
  -- Step 2: `x_k = 2 * 9^k - 1 -> y_k = (3 * 9^k - 1) / 2` forces `bP + dg ≤ bQ`:
  have hbP_dg_le_bQ : bP + dg ≤ bQ := by
    by_cases hle : bP + dg ≤ bQ
    · exact hle
    · exfalso
      let C2 := (sumCoupledCoeffs pTerms * 2 ^ aP) * (sumCoupledCoeffs qTerms * 2 ^ aQ)
      let k := 4 ^ dg * C2 + 1
      have hk_pos : k ≥ 1 := by dsimp [k]; omega
      let xk := 2 * 9 ^ k - 1
      let yk := (3 * 9 ^ k - 1) / 2
      let gk := (3 * 9 ^ k + 1) / 4
      have hp9_ge9 : 9 ^ k ≥ 9 := by
        rw [show k = (k - 1) + 1 by omega, Nat.pow_succ]
        have hp0 := nat_pow_pos_of_pos 9 (by decide) (k - 1); omega
      have hp9_m8 : 9 ^ k % 8 = 1 := pow9_mod8_eq_one_w5 k
      have hp9_m3 : 9 ^ k % 3 = 0 := by
        rw [show k = (k - 1) + 1 by omega, Nat.pow_succ]; omega
      have hxk_ge3 : xk ≥ 3 := by dsimp [xk]; omega
      have hxk_odd : xk % 2 = 1 := by dsimp [xk]; omega
      have hyk_ge3 : yk ≥ 3 := by dsimp [yk]; omega
      have hyk_odd : yk % 2 = 1 := by dsimp [yk]; omega
      have hyk_nd3 : yk % 3 ≠ 0 := by dsimp [yk]; omega
      have hykp1 : yk + 1 = 2 * gk := by dsimp [yk, gk]; omega
      have hgk_pos : gk ≥ 7 := by dsimp [gk]; omega
      have hgk_odd : gk % 2 = 1 := by dsimp [gk]; omega
      have hgk_nd3 : gk % 3 ≠ 0 := by dsimp [gk]; omega
      have hsyr : syracuseOddStep xk = yk := by
        unfold syracuseOddStep
        have h3x : 3 * xk + 1 = 2 * (2 * yk) := by dsimp [xk, yk]; omega
        rw [h3x, core2_mul2 (2 * yk) (by omega), core2_mul2 yk (by omega), core2_of_odd yk hyk_odd]
      have hstrict := preimage_weight_induces_strict_syracuse_lyapunov P Q pTheta qTheta xk
        hw hxk_ge3 hxk_odd (by rw [hsyr]; exact hyk_ge3)
      rw [hsyr] at hstrict
      have hP_xk := (evalCoupledCorePoly_two_mul_pow9_bounds pTerms k hp_ne hk_pos).1
      have hQ_xk := (evalCoupledCorePoly_two_mul_pow9_bounds qTerms k hq_ne hk_pos).2
      have hQ_yk := (evalCoupledCorePoly_two_mul_coprime_bounds qTerms yk gk hq_ne
        hyk_odd hyk_nd3 (by omega) hgk_odd hgk_nd3 hykp1).1
      have hP_yk := (evalCoupledCorePoly_two_mul_coprime_bounds pTerms yk gk hp_ne
        hyk_odd hyk_nd3 (by omega) hgk_odd hgk_nd3 hykp1).2
      change 9 ^ (k * bP) ≤ P xk at hP_xk
      change Q xk ≤ (sumCoupledCoeffs qTerms * 2 ^ aQ) * 9 ^ (k * bQ) at hQ_xk
      change gk ^ gQ ≤ Q yk at hQ_yk
      change P yk ≤ (sumCoupledCoeffs pTerms * 2 ^ aP) * gk ^ gP at hP_yk
      have hlhs : 9 ^ (k * bP) * gk ^ gQ ≤ P xk * Q yk := Nat.mul_le_mul hP_xk hQ_yk
      have hrhs : P yk * Q xk ≤ C2 * gk ^ gP * 9 ^ (k * bQ) := by
        have hm := Nat.mul_le_mul hP_yk hQ_xk
        have hrw : ((sumCoupledCoeffs pTerms * 2 ^ aP) * gk ^ gP) *
            ((sumCoupledCoeffs qTerms * 2 ^ aQ) * 9 ^ (k * bQ)) =
            C2 * gk ^ gP * 9 ^ (k * bQ) := by
          dsimp [C2]
          calc
            ((sumCoupledCoeffs pTerms * 2 ^ aP) * gk ^ gP) *
                ((sumCoupledCoeffs qTerms * 2 ^ aQ) * 9 ^ (k * bQ))
                = (sumCoupledCoeffs pTerms * 2 ^ aP) *
                    (gk ^ gP * ((sumCoupledCoeffs qTerms * 2 ^ aQ) * 9 ^ (k * bQ))) := Nat.mul_assoc _ _ _
            _ = (sumCoupledCoeffs pTerms * 2 ^ aP) *
                    (((sumCoupledCoeffs qTerms * 2 ^ aQ) * gk ^ gP) * 9 ^ (k * bQ)) := by
                  rw [← Nat.mul_assoc (gk ^ gP), Nat.mul_comm (gk ^ gP)]
            _ = (sumCoupledCoeffs pTerms * 2 ^ aP) * (sumCoupledCoeffs qTerms * 2 ^ aQ) *
                    gk ^ gP * 9 ^ (k * bQ) := by rw [← Nat.mul_assoc, ← Nat.mul_assoc]
        rwa [hrw] at hm
      have hcomb : 9 ^ (k * bP) * gk ^ gQ < C2 * gk ^ gP * 9 ^ (k * bQ) :=
        Nat.lt_of_le_of_lt hlhs (Nat.lt_of_lt_of_le hstrict hrhs)
      rw [hgQ_eq, Nat.pow_add gk gP dg] at hcomb
      have hcanc_gk : 9 ^ (k * bP) * gk ^ dg < C2 * 9 ^ (k * bQ) := by
        apply nat_mul_lt_cancel_right_w5 (gk ^ gP) _ _ (nat_pow_pos_of_pos gk (by omega) gP)
        have hl : (9 ^ (k * bP) * gk ^ dg) * gk ^ gP = 9 ^ (k * bP) * (gk ^ gP * gk ^ dg) := by
          rw [Nat.mul_assoc, Nat.mul_comm (gk ^ dg)]
        have hr : (C2 * 9 ^ (k * bQ)) * gk ^ gP = C2 * gk ^ gP * 9 ^ (k * bQ) := by
          rw [Nat.mul_assoc, Nat.mul_comm (9 ^ (k * bQ)), ← Nat.mul_assoc]
        rw [hl, hr]; exact hcomb
      have h4gk : 9 ^ k ≤ 4 * gk := by dsimp [gk]; omega
      have hm4 := Nat.mul_lt_mul_of_pos_left hcanc_gk (nat_pow_pos_of_pos 4 (by decide) dg)
      have hpow_gk : 9 ^ (k * dg) ≤ 4 ^ dg * gk ^ dg := by
        rw [← pow_pow_eq_mul_w5 9 k dg, ← mul_pow_local 4 gk dg]
        exact nat_pow_mono_base (9 ^ k) (4 * gk) h4gk dg
      have hl9 : 9 ^ (k * (bP + dg)) ≤ 4 ^ dg * (9 ^ (k * bP) * gk ^ dg) := by
        rw [Nat.mul_add k bP dg, Nat.pow_add 9,
            ← Nat.mul_assoc (4 ^ dg), Nat.mul_comm (4 ^ dg) (9 ^ (k * bP)), Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ hpow_gk
      have hlt9 : 9 ^ (k * (bP + dg)) < (4 ^ dg * C2) * 9 ^ (k * bQ) := by
        rw [Nat.mul_assoc (4 ^ dg)]; exact Nat.lt_of_le_of_lt hl9 hm4
      have hexp_ge : k + k * bQ ≤ k * (bP + dg) := by
        have hd_gt : 1 + bQ ≤ bP + dg := by omega
        have hm := Nat.mul_le_mul_left k hd_gt
        rwa [Nat.mul_add k 1 bQ, Nat.mul_one] at hm
      have hp9_split : 9 ^ k * 9 ^ (k * bQ) ≤ 9 ^ (k * (bP + dg)) := by
        rw [← Nat.pow_add 9 k (k * bQ)]
        exact nat_pow_mono_exp_pos 9 _ _ (by decide) hexp_ge
      have hcanc9 := nat_mul_lt_cancel_right_w5 (9 ^ (k * bQ)) _ _
        (nat_pow_pos_of_pos 9 (by decide) _) (Nat.lt_of_le_of_lt hp9_split hlt9)
      have hp9_gt_k : 9 ^ k ≥ k + 1 :=
        Nat.le_trans (pow2_ge_succ_self k) (nat_pow_mono_base 2 9 (by decide) k)
      dsimp [k] at hcanc9 hp9_gt_k
      omega
  let db := bQ - bP
  have hdb_pos : db ≥ 1 := by dsimp [db]; omega
  have hbQ_eq : bQ = bP + db := by dsimp [db]; omega
  -- Step 3: `xj = 2 * z_j - 1 -> yj = 2 ^ (6*j + 7) - 1` forces `gP + aQ ≤ aP + gQ`, hence `aQ ≤ aP + db`:
  have haQ_le : aQ ≤ aP + db := by
    have hgP_aQ_le : gP + aQ ≤ aP + gQ := by
      by_cases hle : gP + aQ ≤ aP + gQ
      · exact hle
      · exfalso
        let C3 := (sumCoupledCoeffs pTerms * 2 ^ aP) * (sumCoupledCoeffs qTerms * 2 ^ aQ * 2 ^ gQ)
        let j := C3 + 1
        let zj := geomSpineEntry j
        rcases geomSpineEntry_valuations_constant j with ⟨h3zj1, hzj_ge, _, _, _, _⟩
        change 3 * zj + 1 = 4 ^ (3 * j + 4) at h3zj1
        change zj ≥ 85 at hzj_ge
        let Mj := 4 ^ (3 * j + 3)
        have hMj_ge64 : Mj ≥ 64 := by
          dsimp [Mj]
          rw [Nat.pow_add 4 (3 * j) 3]
          have hm := Nat.mul_le_mul_right 64 (nat_pow_pos_of_pos 4 (by decide) (3 * j))
          simpa using hm
        have h3zj1_M : 3 * zj + 1 = 4 * Mj := by
          rw [h3zj1]; dsimp [Mj]
          rw [show 3 * j + 4 = (3 * j + 3) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
        have hzj_odd : zj % 2 = 1 := by omega
        have hzj_m3 : zj % 3 = 1 := by
          have hp4_m9 : 4 ^ (3 * j + 4) % 9 = 4 := by
            rw [Nat.pow_add 4 (3 * j) 4, pow4_triple_eq_pow64_w5 j,
                Nat.mul_mod, pow64_mod9_eq_one_w5 j]
          rw [← h3zj1] at hp4_m9
          generalize zj = z at hp4_m9 ⊢
          omega
        let xj := 2 * zj - 1
        let yj := 2 * Mj - 1
        have hxj_odd : xj % 2 = 1 := by dsimp [xj]; omega
        have hxj_nd3 : xj % 3 ≠ 0 := by dsimp [xj]; omega
        have hxjp1 : xj + 1 = 2 * zj := by dsimp [xj]; omega
        have hyj_odd : yj % 2 = 1 := by dsimp [yj]; omega
        have hsyr : syracuseOddStep xj = yj := by
          unfold syracuseOddStep
          have h3x : 3 * xj + 1 = 2 * (2 * yj) := by dsimp [xj, yj]; omega
          rw [h3x, core2_mul2 (2 * yj) (by omega), core2_mul2 yj (by omega), core2_of_odd yj hyj_odd]
        have hstrict := preimage_weight_induces_strict_syracuse_lyapunov P Q pTheta qTheta xj
          hw (by dsimp [xj]; omega) hxj_odd (by rw [hsyr]; dsimp [yj]; omega)
        rw [hsyr] at hstrict
        have hP_xj := (evalCoupledCorePoly_two_mul_coprime_bounds pTerms xj zj hp_ne
          hxj_odd hxj_nd3 (by omega) hzj_odd (by omega) hxjp1).1
        have hQ_xj := (evalCoupledCorePoly_two_mul_coprime_bounds qTerms xj zj hq_ne
          hxj_odd hxj_nd3 (by omega) hzj_odd (by omega) hxjp1).2
        have hQ_yj := (evalCoupledCorePoly_odd_pow2_bounds qTerms (3 * j + 3) hq_ne (by omega)).1
        have hP_yj := (evalCoupledCorePoly_odd_pow2_bounds pTerms (3 * j + 3) hp_ne (by omega)).2
        change zj ^ gP ≤ P xj at hP_xj
        change Q xj ≤ (sumCoupledCoeffs qTerms * 2 ^ aQ) * zj ^ gQ at hQ_xj
        change Mj ^ aQ ≤ Q yj at hQ_yj
        change P yj ≤ (sumCoupledCoeffs pTerms * 2 ^ aP) * Mj ^ aP at hP_yj
        have hMj_le_zj : Mj ≤ zj := by omega
        have hzj_le_2Mj : zj ≤ 2 * Mj := by omega
        have hlhs : Mj ^ (gP + aQ) ≤ P xj * Q yj := by
          rw [Nat.pow_add Mj gP aQ]
          exact Nat.mul_le_mul (Nat.le_trans (nat_pow_mono_base Mj zj hMj_le_zj gP) hP_xj) hQ_yj
        have hrhs : P yj * Q xj ≤ C3 * Mj ^ (aP + gQ) := by
          have hz_ub : zj ^ gQ ≤ 2 ^ gQ * Mj ^ gQ := by
            rw [← mul_pow_local 2 Mj gQ]; exact nat_pow_mono_base zj (2 * Mj) hzj_le_2Mj gQ
          have hQ_ub : Q xj ≤ (sumCoupledCoeffs qTerms * 2 ^ aQ * 2 ^ gQ) * Mj ^ gQ := by
            rw [Nat.mul_assoc (sumCoupledCoeffs qTerms * 2 ^ aQ)]
            exact Nat.le_trans hQ_xj (Nat.mul_le_mul_left _ hz_ub)
          have hm := Nat.mul_le_mul hP_yj hQ_ub
          have hrw : ((sumCoupledCoeffs pTerms * 2 ^ aP) * Mj ^ aP) *
              ((sumCoupledCoeffs qTerms * 2 ^ aQ * 2 ^ gQ) * Mj ^ gQ) =
              C3 * Mj ^ (aP + gQ) := by
            dsimp [C3]
            calc
              ((sumCoupledCoeffs pTerms * 2 ^ aP) * Mj ^ aP) *
                  ((sumCoupledCoeffs qTerms * 2 ^ aQ * 2 ^ gQ) * Mj ^ gQ)
                  = (sumCoupledCoeffs pTerms * 2 ^ aP) *
                      (Mj ^ aP * ((sumCoupledCoeffs qTerms * 2 ^ aQ * 2 ^ gQ) * Mj ^ gQ)) := Nat.mul_assoc _ _ _
              _ = (sumCoupledCoeffs pTerms * 2 ^ aP) *
                      ((sumCoupledCoeffs qTerms * 2 ^ aQ * 2 ^ gQ) * (Mj ^ aP * Mj ^ gQ)) := by
                    rw [← Nat.mul_assoc (Mj ^ aP),
                        Nat.mul_comm (Mj ^ aP) (sumCoupledCoeffs qTerms * 2 ^ aQ * 2 ^ gQ),
                        Nat.mul_assoc (sumCoupledCoeffs qTerms * 2 ^ aQ * 2 ^ gQ)]
              _ = C3 * Mj ^ (aP + gQ) := by rw [← Nat.mul_assoc, ← Nat.pow_add]
          rwa [hrw] at hm
        have hcomb : Mj ^ (gP + aQ) < C3 * Mj ^ (aP + gQ) :=
          Nat.lt_of_le_of_lt hlhs (Nat.lt_of_lt_of_le hstrict hrhs)
        have hexp_ge : 1 + (aP + gQ) ≤ gP + aQ := by omega
        have hM_split : Mj * Mj ^ (aP + gQ) ≤ Mj ^ (gP + aQ) := by
          have hm := nat_pow_mono_exp_pos Mj _ _ (by omega) hexp_ge
          rwa [Nat.pow_add Mj 1, Nat.pow_one] at hm
        have hcancM := nat_mul_lt_cancel_right_w5 (Mj ^ (aP + gQ)) _ _
          (nat_pow_pos_of_pos Mj (by omega) _) (Nat.lt_of_le_of_lt hM_split hcomb)
        have hMj_gt_j : Mj ≥ j + 1 := by
          dsimp [Mj]
          have h1 : 4 ^ (3 * j + 3) ≥ 2 ^ j :=
            Nat.le_trans (pow2_mono_nat (by omega : j ≤ 3 * j + 3))
              (nat_pow_mono_base 2 4 (by decide) (3 * j + 3))
          exact Nat.le_trans (pow2_ge_succ_self j) h1
        dsimp [j] at hcancM hMj_gt_j
        omega
    omega
  -- Step 4: `2r`-step Mersenne glide `X0(r) = 2^(2r+1) - 1 -> X_{2r}(r) = 2 * 9^r - 1` pits `9^(r*db)` vs `4^(r*db)`:
  let C4 := (sumCoupledCoeffs pTerms * 2 ^ aP) * (sumCoupledCoeffs qTerms * 2 ^ aQ)
  let r := C4 + 1
  have hr_pos : r ≥ 1 := by dsimp [r]; omega
  let x0 := 2 * 4 ^ r - 1
  let xEnd := 2 * 9 ^ r - 1
  have hx0_eq_pow2 : x0 = 2 ^ (2 * r) * 2 - 1 := by
    dsimp [x0]; rw [pow4_eq_pow2_even r, Nat.mul_comm]
  have hiter_end : collatzIter (2 * r) x0 = xEnd := by
    rw [hx0_eq_pow2, odd_run_iter (2 * r) 2 (by decide),
        show 3 ^ (2 * r) = 9 ^ r by rw [pow9_eq_pow3_double r], Nat.mul_comm]
  have hall_ge3 : ∀ j : Nat, j ≤ 2 * r -> collatzIter j x0 ≥ 3 := by
    intro j hj
    have hsplit_x0 : x0 = 2 ^ j * (2 ^ (2 * r + 1 - j)) - 1 := by
      have hp : 2 ^ j * 2 ^ (2 * r + 1 - j) = 2 * 4 ^ r := by
        rw [← Nat.pow_add, show j + (2 * r + 1 - j) = 2 * r + 1 by omega,
            Nat.pow_succ, pow4_eq_pow2_even r, Nat.mul_comm]
      dsimp [x0]; rw [hp]
    have hu_ge2 : 2 ^ (2 * r + 1 - j) ≥ 2 := by
      have hs : 2 * r + 1 - j = 1 + (2 * r - j) := by omega
      rw [hs, Nat.pow_add, Nat.pow_one]
      have hm := Nat.mul_le_mul_left 2 (pow2_pos_nat (2 * r - j)); omega
    rw [hsplit_x0, odd_run_iter j (2 ^ (2 * r + 1 - j)) (by omega)]
    have h32 : 2 ^ j ≤ 3 ^ j := pow2_le_pow3 j
    have hm := Nat.mul_le_mul_right (2 ^ (2 * r + 1 - j)) h32
    have hp : 2 ^ j * 2 ^ (2 * r + 1 - j) ≥ 8 := by
      rw [← Nat.pow_add, show j + (2 * r + 1 - j) = 2 * r + 1 by omega]
      have hm2 := pow2_mono_nat (by omega : 3 ≤ 2 * r + 1)
      simpa using hm2
    omega
  have hx0_odd : collatzIter 0 x0 % 2 = 1 := by
    simp only [collatzIter]
    have hm4 : 4 ^ r ≥ 4 := by
      have hm := (pow4_ge_four_and_mod3_w5 (r - 1)).1
      rwa [show r - 1 + 1 = r by omega] at hm
    dsimp [x0]; omega
  have hglide_strict := (preimage_iter_monotone_and_odd_strict_w5 P Q pTheta qTheta hw
    (2 * r) x0 hall_ge3).2 ⟨0, by omega, hx0_odd⟩
  rw [hiter_end] at hglide_strict
  have hP_x0 := (evalCoupledCorePoly_odd_pow2_bounds pTerms r hp_ne hr_pos).1
  have hQ_x0 := (evalCoupledCorePoly_odd_pow2_bounds qTerms r hq_ne hr_pos).2
  have hQ_xE := (evalCoupledCorePoly_two_mul_pow9_bounds qTerms r hq_ne hr_pos).1
  have hP_xE := (evalCoupledCorePoly_two_mul_pow9_bounds pTerms r hp_ne hr_pos).2
  change (4 ^ r) ^ aP ≤ P x0 at hP_x0
  change Q x0 ≤ (sumCoupledCoeffs qTerms * 2 ^ aQ) * (4 ^ r) ^ aQ at hQ_x0
  change 9 ^ (r * bQ) ≤ Q xEnd at hQ_xE
  change P xEnd ≤ (sumCoupledCoeffs pTerms * 2 ^ aP) * 9 ^ (r * bP) at hP_xE
  rw [pow_pow_eq_mul_w5 4 r aP] at hP_x0
  rw [pow_pow_eq_mul_w5 4 r aQ] at hQ_x0
  have hlhs4 : 4 ^ (r * aP) * 9 ^ (r * bQ) ≤ P x0 * Q xEnd := Nat.mul_le_mul hP_x0 hQ_xE
  have hrhs4 : P xEnd * Q x0 ≤ C4 * 9 ^ (r * bP) * 4 ^ (r * (aP + db)) := by
    have h4_le : 4 ^ (r * aQ) ≤ 4 ^ (r * (aP + db)) :=
      nat_pow_mono_exp_pos 4 _ _ (by decide) (Nat.mul_le_mul_left r haQ_le)
    have hQ_ub : Q x0 ≤ (sumCoupledCoeffs qTerms * 2 ^ aQ) * 4 ^ (r * (aP + db)) :=
      Nat.le_trans hQ_x0 (Nat.mul_le_mul_left _ h4_le)
    have hm := Nat.mul_le_mul hP_xE hQ_ub
    have hrw : ((sumCoupledCoeffs pTerms * 2 ^ aP) * 9 ^ (r * bP)) *
        ((sumCoupledCoeffs qTerms * 2 ^ aQ) * 4 ^ (r * (aP + db))) =
        C4 * 9 ^ (r * bP) * 4 ^ (r * (aP + db)) := by
      dsimp [C4]
      calc
        ((sumCoupledCoeffs pTerms * 2 ^ aP) * 9 ^ (r * bP)) *
            ((sumCoupledCoeffs qTerms * 2 ^ aQ) * 4 ^ (r * (aP + db)))
            = (sumCoupledCoeffs pTerms * 2 ^ aP) *
                (9 ^ (r * bP) * ((sumCoupledCoeffs qTerms * 2 ^ aQ) * 4 ^ (r * (aP + db)))) :=
              Nat.mul_assoc _ _ _
        _ = (sumCoupledCoeffs pTerms * 2 ^ aP) *
                ((sumCoupledCoeffs qTerms * 2 ^ aQ) * (9 ^ (r * bP) * 4 ^ (r * (aP + db)))) := by
              rw [← Nat.mul_assoc (9 ^ (r * bP)),
                  Nat.mul_comm (9 ^ (r * bP)) (sumCoupledCoeffs qTerms * 2 ^ aQ),
                  Nat.mul_assoc (sumCoupledCoeffs qTerms * 2 ^ aQ)]
        _ = C4 * 9 ^ (r * bP) * 4 ^ (r * (aP + db)) := by rw [← Nat.mul_assoc, ← Nat.mul_assoc]
    rwa [hrw] at hm
  have hcomb4 : 4 ^ (r * aP) * 9 ^ (r * bQ) < C4 * 9 ^ (r * bP) * 4 ^ (r * (aP + db)) :=
    Nat.lt_of_le_of_lt hlhs4 (Nat.lt_of_lt_of_le hglide_strict hrhs4)
  rw [hbQ_eq, Nat.mul_add r bP db, Nat.pow_add 9 (r * bP) (r * db),
      Nat.mul_add r aP db, Nat.pow_add 4 (r * aP) (r * db)] at hcomb4
  have hcanc_base : 9 ^ (r * db) < C4 * 4 ^ (r * db) := by
    apply nat_mul_lt_cancel_left (4 ^ (r * aP) * 9 ^ (r * bP)) _ _
      (Nat.mul_le_mul (nat_pow_pos_of_pos 4 (by decide) _) (nat_pow_pos_of_pos 9 (by decide) _))
    have hl : (4 ^ (r * aP) * 9 ^ (r * bP)) * 9 ^ (r * db) =
        4 ^ (r * aP) * (9 ^ (r * bP) * 9 ^ (r * db)) := Nat.mul_assoc _ _ _
    have hr : (4 ^ (r * aP) * 9 ^ (r * bP)) * (C4 * 4 ^ (r * db)) =
        C4 * 9 ^ (r * bP) * (4 ^ (r * aP) * 4 ^ (r * db)) := by
      calc
        (4 ^ (r * aP) * 9 ^ (r * bP)) * (C4 * 4 ^ (r * db))
            = (9 ^ (r * bP) * 4 ^ (r * aP)) * (C4 * 4 ^ (r * db)) := by rw [Nat.mul_comm (4 ^ (r * aP))]
        _ = 9 ^ (r * bP) * (4 ^ (r * aP) * (C4 * 4 ^ (r * db))) := Nat.mul_assoc _ _ _
        _ = 9 ^ (r * bP) * (C4 * (4 ^ (r * aP) * 4 ^ (r * db))) := by
              rw [← Nat.mul_assoc (4 ^ (r * aP)), Nat.mul_comm (4 ^ (r * aP)) C4, Nat.mul_assoc]
        _ = C4 * 9 ^ (r * bP) * (4 ^ (r * aP) * 4 ^ (r * db)) := by
              rw [← Nat.mul_assoc (9 ^ (r * bP)) C4, Nat.mul_comm (9 ^ (r * bP)) C4]
    rw [hl, hr]; exact hcomb4
  let E := r * db
  have hr_le_E : r ≤ E := by
    dsimp [E]; have hm := Nat.mul_le_mul_left r hdb_pos; simpa using hm
  have h8_le_9 : 2 ^ E * 4 ^ E ≤ 9 ^ E := by
    rw [← mul_pow_local 2 4 E]
    exact nat_pow_mono_base 8 9 (by decide) E
  have h2E_ge : r + 1 ≤ 2 ^ E :=
    Nat.le_trans (pow2_ge_succ_self r) (pow2_mono_nat hr_le_E)
  have hl_ge : (r + 1) * 4 ^ E ≤ 9 ^ E :=
    Nat.le_trans (Nat.mul_le_mul_right (4 ^ E) h2E_ge) h8_le_9
  have hcanc4 := nat_mul_lt_cancel_right_w5 (4 ^ E) _ _
    (nat_pow_pos_of_pos 4 (by decide) E) (Nat.lt_of_le_of_lt hl_ge hcanc_base)
  dsimp [r] at hcanc4
  omega

-- ============================================================================
-- SECTION 2A: Front B (Branch P4.3) — Zero-Diagonal 2D Upper-Triangular
--             Matrix Necessity (`n_B0 = 0`) & Sharp `R1 + Sub6` Impossibility
-- ============================================================================

/--
  Theorem W6.2a (`sub6_upper_tri_2d_forces_zero_diag_B0`, zero custom axioms):
  Every top-left-monotone (`∀ s, (interp s).m ≥ 1`) 2D upper-triangular Natural Matrix
  Interpretation orienting `{R2, R5, R7, R9, R11}` MUST satisfy:
  - `(interp s).m = 1` for all `s ∈ {B0, B1, T0, T1, T2}`,
  - `(interp .R).d ≥ 1`, AND
  - ZERO bottom-right diagonal `(interp .B0).n = 0`!
  This explains algebraically why `sub6UpperTri2DCert` (`T2.8b`) had to set `n_B0 = 0` to
  bypass `all_dim_coord_monotone_upper_triangular_impossibility` (`T2.8a`).
-/
theorem sub6_upper_tri_2d_forces_zero_diag_B0
    (interp : MixedSRSSym -> UpperTri2D)
    (hm_pos : ∀ s : MixedSRSSym, (interp s).m ≥ 1)
    (hR2  : orientsUpperTri2D (evalWordUpperTri2D interp [.L, .B1])
              (evalWordUpperTri2D interp [.L, .T2]))
    (hR5  : orientsUpperTri2D (evalWordUpperTri2D interp [.T1, .B0])
              (evalWordUpperTri2D interp [.B1, .T0]))
    (hR7  : orientsUpperTri2D (evalWordUpperTri2D interp [.T2, .B0])
              (evalWordUpperTri2D interp [.B0, .T1]))
    (hR9  : orientsUpperTri2D (evalWordUpperTri2D interp [.T0, .R])
              (evalWordUpperTri2D interp [.B1, .R]))
    (hR11 : orientsUpperTri2D (evalWordUpperTri2D interp [.T2, .R])
              (evalWordUpperTri2D interp [.B1, .B0, .R])) :
    (interp .B0).m = 1 ∧ (interp .B1).m = 1 ∧
    (interp .T0).m = 1 ∧ (interp .T1).m = 1 ∧ (interp .T2).m = 1 ∧
    (interp .B0).n = 0 ∧ (interp .R).d ≥ 1 := by
  have hr2_m : (interp .L).m * (interp .B1).m ≥ (interp .L).m * (interp .T2).m := by
    simpa [evalWordUpperTri2D, compUpperTri2D] using hR2.1
  have hr5_m : (interp .T1).m * (interp .B0).m ≥ (interp .B1).m * (interp .T0).m := by
    simpa [evalWordUpperTri2D, compUpperTri2D] using hR5.1
  have hr7_m : (interp .T2).m * (interp .B0).m ≥ (interp .B0).m * (interp .T1).m := by
    simpa [evalWordUpperTri2D, compUpperTri2D] using hR7.1
  have hr9_m : (interp .T0).m * (interp .R).m ≥ (interp .B1).m * (interp .R).m := by
    simpa [evalWordUpperTri2D, compUpperTri2D] using hR9.1
  have hr11_m : (interp .T2).m * (interp .R).m ≥
      (interp .B1).m * (interp .B0).m * (interp .R).m := by
    have h := hR11.1
    simp only [evalWordUpperTri2D, compUpperTri2D, Nat.mul_one] at h
    rwa [← Nat.mul_assoc] at h
  rcases upper_triangular_top_left_unit_collapse_any_dim
    (interp .L).m (interp .R).m (interp .B0).m (interp .B1).m
    (interp .T0).m (interp .T1).m (interp .T2).m
    (hm_pos .L) (hm_pos .R) (hm_pos .B0) (hm_pos .B1)
    (hm_pos .T0) (hm_pos .T1) (hm_pos .T2)
    hr2_m hr5_m hr7_m hr9_m hr11_m with ⟨hmB0, hmB1, hmT0, hmT1, hmT2⟩
  have hr2_p := hR2.2.1
  have hr2_c := hR2.2.2.2.1
  have hr11_c := hR11.2.2.2.1
  have hr11_d := hR11.2.2.2.2
  simp only [evalWordUpperTri2D, compUpperTri2D, hmB0, hmB1, hmT2,
             Nat.one_mul, Nat.mul_one, Nat.mul_zero,
             Nat.zero_add, Nat.add_zero] at hr2_p hr2_c hr11_c hr11_d
  let mL := (interp .L).m
  let pL := (interp .L).p
  let dR := (interp .R).d
  let pB0 := (interp .B0).p
  let nB0 := (interp .B0).n
  let cB0 := (interp .B0).c
  let dB0 := (interp .B0).d
  let pB1 := (interp .B1).p
  let nB1 := (interp .B1).n
  let cB1 := (interp .B1).c
  let dB1 := (interp .B1).d
  let pT2 := (interp .T2).p
  let nT2 := (interp .T2).n
  let cT2 := (interp .T2).c
  let dT2 := (interp .T2).d
  have hmL_pos : mL ≥ 1 := hm_pos .L
  change mL * pB1 + pL * nB1 ≥ mL * pT2 + pL * nT2 at hr2_p
  have hr2_c' : mL * cB1 + pL * dB1 > mL * cT2 + pL * dT2 := by
    dsimp [mL, pL, cB1, dB1, cT2, dT2]; omega
  have hr11_c' : pT2 * dR + cT2 > pB0 * dR + cB0 + pB1 * (nB0 * dR + dB0) + cB1 := by
    dsimp [pT2, dR, cT2, pB0, cB0, pB1, nB0, dB0, cB1]; omega
  change nT2 * dR + dT2 ≥ nB1 * (nB0 * dR + dB0) + dB1 at hr11_d
  have hm11 := Nat.mul_lt_mul_of_pos_left hr11_c' hmL_pos
  have hp11 := Nat.mul_le_mul_left pL hr11_d
  -- Expand `(mL * pT2 + pL * nT2) * dR > (mL * pB1 + pL * nB1) * nB0 * dR`:
  have hstar : (mL * pT2 + pL * nT2) * dR > (mL * pB1 + pL * nB1) * (nB0 * dR) := by
    rw [Nat.add_mul (mL * pT2) (pL * nT2) dR,
        Nat.add_mul (mL * pB1) (pL * nB1) (nB0 * dR)]
    have hl1 : mL * (pT2 * dR + cT2) = (mL * pT2) * dR + mL * cT2 := by
      rw [Nat.mul_add, Nat.mul_assoc]
    have hr1 : mL * (pB0 * dR + cB0 + pB1 * (nB0 * dR + dB0) + cB1) =
        mL * (pB0 * dR + cB0) + (mL * pB1) * (nB0 * dR) + (mL * pB1) * dB0 + mL * cB1 := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc mL pB1,
          Nat.mul_add (mL * pB1)]
      omega
    have hl2 : pL * (nT2 * dR + dT2) = (pL * nT2) * dR + pL * dT2 := by
      rw [Nat.mul_add, Nat.mul_assoc]
    have hr2 : pL * (nB1 * (nB0 * dR + dB0) + dB1) =
        (pL * nB1) * (nB0 * dR) + (pL * nB1) * dB0 + pL * dB1 := by
      rw [Nat.mul_add, ← Nat.mul_assoc pL nB1, Nat.mul_add (pL * nB1)]
    rw [hl1, hr1] at hm11
    rw [hl2, hr2] at hp11
    omega
  have hdR_pos : dR ≥ 1 := by
    cases hd : dR with
    | zero => rw [hd] at hstar; simp at hstar
    | succ _ => omega
  have hnB0_zero : nB0 = 0 := by
    cases hn : nB0 with
    | zero => rfl
    | succ k =>
      rw [hn] at hstar
      have hge1 : (mL * pB1 + pL * nB1) * (1 * dR) ≤
          (mL * pB1 + pL * nB1) * ((k + 1) * dR) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right dR (by omega : 1 ≤ k + 1))
      rw [Nat.one_mul] at hge1
      have hge2 : (mL * pT2 + pL * nT2) * dR ≤ (mL * pB1 + pL * nB1) * dR :=
        Nat.mul_le_mul_right dR hr2_p
      omega
  exact ⟨hmB0, hmB1, hmT0, hmT1, hmT2, hnB0_zero, hdR_pos⟩

/--
  Theorem W6.2b (`zero_diag_upper_tri_2d_r1_sub6_impossibility`, zero custom axioms):
  Sharp Zero-Diagonal 2D Upper-Triangular Impossibility Theorem:
  Although `sub6UpperTri2DCert` (`T2.8b`) orients the 7-rule subset `{R2, R5, R7, R8, R9, R10, R11}`
  by exploiting zero diagonals `(M_s)_{1,1} = 0`, adding JUST `R1_even` (`[L, B0] -> [L]`) to
  `{R2, R5, R7, R8, R9, R11}` (7 rules total, without `R3, R4, R6, R10`) is UNIVERSALLY IMPOSSIBLE
  across ALL `UpperTri2D` interpretations with `m_s ≥ 1` (arbitrary zero diagonals `n_s = 0` and
  unbounded entries allowed)!
-/
theorem zero_diag_upper_tri_2d_r1_sub6_impossibility
    (interp : MixedSRSSym -> UpperTri2D)
    (hm_pos : ∀ s : MixedSRSSym, (interp s).m ≥ 1)
    (hR1  : orientsUpperTri2D (evalWordUpperTri2D interp [.L, .B0])
              (evalWordUpperTri2D interp [.L]))
    (hR2  : orientsUpperTri2D (evalWordUpperTri2D interp [.L, .B1])
              (evalWordUpperTri2D interp [.L, .T2]))
    (hR5  : orientsUpperTri2D (evalWordUpperTri2D interp [.T1, .B0])
              (evalWordUpperTri2D interp [.B1, .T0]))
    (hR7  : orientsUpperTri2D (evalWordUpperTri2D interp [.T2, .B0])
              (evalWordUpperTri2D interp [.B0, .T1]))
    (hR8  : orientsUpperTri2D (evalWordUpperTri2D interp [.T2, .B1])
              (evalWordUpperTri2D interp [.B1, .T2]))
    (hR9  : orientsUpperTri2D (evalWordUpperTri2D interp [.T0, .R])
              (evalWordUpperTri2D interp [.B1, .R]))
    (hR11 : orientsUpperTri2D (evalWordUpperTri2D interp [.T2, .R])
              (evalWordUpperTri2D interp [.B1, .B0, .R])) :
    False := by
  rcases sub6_upper_tri_2d_forces_zero_diag_B0 interp hm_pos hR2 hR5 hR7 hR9 hR11 with
    ⟨hmB0, hmB1, hmT0, hmT1, hmT2, hnB0, hdR_pos⟩
  let mL := (interp .L).m
  let pL := (interp .L).p
  let dR := (interp .R).d
  let pB0 := (interp .B0).p
  let cB0 := (interp .B0).c
  let dB0 := (interp .B0).d
  let pB1 := (interp .B1).p
  let nB1 := (interp .B1).n
  let cB1 := (interp .B1).c
  let dB1 := (interp .B1).d
  let pT0 := (interp .T0).p
  let nT0 := (interp .T0).n
  let cT0 := (interp .T0).c
  let dT0 := (interp .T0).d
  let pT1 := (interp .T1).p
  let nT1 := (interp .T1).n
  let cT1 := (interp .T1).c
  let dT1 := (interp .T1).d
  let pT2 := (interp .T2).p
  let nT2 := (interp .T2).n
  let cT2 := (interp .T2).c
  let dT2 := (interp .T2).d
  have hmL_pos : mL ≥ 1 := hm_pos .L
  change dR ≥ 1 at hdR_pos
  -- Extract simplified component inequalities:
  have hr1_p : mL * pB0 ≥ pL := by
    have h := hR1.2.1
    simp only [evalWordUpperTri2D, compUpperTri2D, hmB0, hnB0,
               Nat.mul_one, Nat.mul_zero,
               Nat.zero_add, Nat.add_zero] at h
    exact h
  have hr2_p : mL * pB1 + pL * nB1 ≥ mL * pT2 + pL * nT2 := by
    have h := hR2.2.1
    simp only [evalWordUpperTri2D, compUpperTri2D, hmB1, hmT2,
               Nat.mul_one, Nat.mul_zero,
               Nat.zero_add, Nat.add_zero] at h
    exact h
  have hr5_p : pB0 ≥ pT0 + pB1 * nT0 := by
    have h := hR5.2.1
    simp only [evalWordUpperTri2D, compUpperTri2D, hmB0, hmB1, hmT0, hmT1, hnB0,
               Nat.one_mul, Nat.mul_one, Nat.mul_zero,
               Nat.zero_add, Nat.add_zero] at h
    exact h
  have hr5_n : 0 ≥ nB1 * nT0 := by
    have h := hR5.2.2.1
    simp only [evalWordUpperTri2D, compUpperTri2D, hnB0,
               Nat.mul_one, Nat.mul_zero] at h
    exact h
  have hr7_p : pB0 ≥ pT1 + pB0 * nT1 := by
    have h := hR7.2.1
    simp only [evalWordUpperTri2D, compUpperTri2D, hmB0, hmT1, hmT2, hnB0,
               Nat.one_mul, Nat.mul_one, Nat.mul_zero,
               Nat.zero_add, Nat.add_zero] at h
    exact h
  have hr8_p : pB1 + pT2 * nB1 ≥ pT2 + pB1 * nT2 := by
    have h := hR8.2.1
    simp only [evalWordUpperTri2D, compUpperTri2D, hmB1, hmT2,
               Nat.one_mul, Nat.mul_one, Nat.mul_zero,
               Nat.zero_add, Nat.add_zero] at h
    exact h
  have hr8_c : pT2 * dB1 > pB1 * dT2 := by
    have h := hR8.2.2.2.1
    simp only [evalWordUpperTri2D, compUpperTri2D, hmB1, hmT2,
               Nat.one_mul, Nat.mul_zero,
               Nat.zero_add, Nat.add_zero] at h
    dsimp [pT2, dB1, pB1, dT2]; omega
  have hr8_d : nT2 * dB1 + dT2 ≥ nB1 * dT2 + dB1 := by
    have h := hR8.2.2.2.2
    simp only [evalWordUpperTri2D, compUpperTri2D,
               Nat.mul_zero, Nat.zero_add, Nat.add_zero] at h
    exact h
  have hr5_d : nT1 * dB0 + dT1 ≥ nB1 * dT0 + dB1 := by
    have h := hR5.2.2.2.2
    simp only [evalWordUpperTri2D, compUpperTri2D,
               Nat.mul_zero, Nat.zero_add, Nat.add_zero] at h
    exact h
  have hr9_d : nT0 * dR + dT0 ≥ nB1 * dR + dB1 := by
    have h := hR9.2.2.2.2
    simp only [evalWordUpperTri2D, compUpperTri2D,
               Nat.mul_zero, Nat.zero_add, Nat.add_zero] at h
    exact h
  have hr11_d : nT2 * dR + dT2 ≥ nB1 * dB0 + dB1 := by
    have h := hR11.2.2.2.2
    simp only [evalWordUpperTri2D, compUpperTri2D, hnB0,
               Nat.zero_mul, Nat.mul_zero, Nat.zero_add, Nat.add_zero] at h
    exact h
  -- 1. `pT2 ≥ 1` and `dB1 ≥ 1` from `hr8_c`:
  have hpT2_pos : pT2 ≥ 1 := by
    cases hp : pT2 with
    | zero => rw [hp] at hr8_c; simp at hr8_c
    | succ _ => omega
  have hdB1_pos : dB1 ≥ 1 := by
    cases hd : dB1 with
    | zero => rw [hd] at hr8_c; simp at hr8_c
    | succ _ => omega
  -- 2. `nB1 ≥ 1` from `hr8_p, hr8_c, hr8_d`:
  have hnB1_pos : nB1 ≥ 1 := by
    cases hn : nB1 with
    | zero =>
      rw [hn] at hr8_p hr8_d
      simp only [Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add] at hr8_p hr8_d
      cases hn2 : nT2 with
      | zero =>
        rw [hn2, Nat.mul_zero, Nat.add_zero] at hr8_p
        rw [hn2, Nat.zero_mul, Nat.zero_add] at hr8_d
        have hm := Nat.mul_le_mul hr8_p hr8_d
        omega
      | succ k =>
        have hm : pB1 * 1 ≤ pB1 * (k + 1) := Nat.mul_le_mul_left pB1 (by omega)
        rw [Nat.mul_one] at hm
        rw [hn2] at hr8_p
        omega
    | succ _ => omega
  -- 3. `nT0 = 0` from `hr5_n` + `nB1 ≥ 1`:
  have hnT0_zero : nT0 = 0 := by
    cases hn0 : nT0 with
    | zero => rfl
    | succ k =>
      rw [hn0] at hr5_n
      have hm := Nat.mul_le_mul hnB1_pos (by omega : 1 ≤ k + 1)
      omega
  rw [hnT0_zero, Nat.zero_mul, Nat.zero_add] at hr9_d
  -- 4. `1 ≤ nT2 ≤ nB1` from `hr8_d` + `hr2_p` + `hr8_p`:
  have hnT2_pos : nT2 ≥ 1 := by
    cases hn : nT2 with
    | zero =>
      rw [hn, Nat.zero_mul, Nat.zero_add] at hr8_d
      have hm : 1 * dT2 ≤ nB1 * dT2 := Nat.mul_le_mul_right dT2 hnB1_pos
      rw [Nat.one_mul] at hm
      omega
    | succ _ => omega
  have hnT2_le_nB1 : nT2 ≤ nB1 := by
    by_cases hle : nT2 ≤ nB1
    · exact hle
    · have hgt : nB1 < nT2 := by omega
      have hpL_le : pL * nB1 ≤ pL * nT2 := Nat.mul_le_mul_left pL (Nat.le_of_lt hgt)
      have hmL_p : mL * pT2 ≤ mL * pB1 := by omega
      have hpT2_le_pB1 : pT2 ≤ pB1 := nat_mul_le_cancel_left_w5 mL _ _ hmL_pos hmL_p
      have hsub1 : pT2 * (nB1 - 1) ≥ pB1 * (nT2 - 1) := by
        have h1 : pT2 * nB1 = pT2 * (nB1 - 1) + pT2 := by
          conv => lhs; rw [show nB1 = (nB1 - 1) + 1 by omega]
          rw [Nat.mul_add, Nat.mul_one]
        have h2 : pB1 * nT2 = pB1 * (nT2 - 1) + pB1 := by
          conv => lhs; rw [show nT2 = (nT2 - 1) + 1 by omega]
          rw [Nat.mul_add, Nat.mul_one]
        omega
      have hstrict : pT2 * (nB1 - 1) < pB1 * (nT2 - 1) := by
        have hm1 : pT2 * (nB1 - 1) < pT2 * (nT2 - 1) :=
          Nat.mul_lt_mul_of_pos_left (by omega : nB1 - 1 < nT2 - 1) hpT2_pos
        have hm2 : pT2 * (nT2 - 1) ≤ pB1 * (nT2 - 1) :=
          Nat.mul_le_mul_right (nT2 - 1) hpT2_le_pB1
        omega
      omega
  -- 5. `dT2 ≤ dB1` and `dB0 ≤ dR`:
  have hdT2_le_dB1 : dT2 ≤ dB1 := by
    by_cases h1 : nB1 = 1
    · have hn2_1 : nT2 = 1 := by omega
      rw [h1, hn2_1] at hr2_p
      have hmL_p : mL * pT2 ≤ mL * pB1 := by omega
      have hp_le : pT2 ≤ pB1 := nat_mul_le_cancel_left_w5 mL _ _ hmL_pos hmL_p
      by_cases hd_le : dT2 ≤ dB1
      · exact hd_le
      · have hm := Nat.mul_le_mul hp_le (by omega : dB1 ≤ dT2)
        omega
    · have hn1_ge2 : nB1 - 1 ≥ 1 := by omega
      have hrew : (nB1 - 1) * dT2 ≤ (nT2 - 1) * dB1 := by
        have ha : nT2 * dB1 = (nT2 - 1) * dB1 + dB1 := by
          conv => lhs; rw [show nT2 = (nT2 - 1) + 1 by omega]
          rw [Nat.add_mul, Nat.one_mul]
        have hb : nB1 * dT2 = (nB1 - 1) * dT2 + dT2 := by
          conv => lhs; rw [show nB1 = (nB1 - 1) + 1 by omega]
          rw [Nat.add_mul, Nat.one_mul]
        omega
      have hm_le : (nT2 - 1) * dB1 ≤ (nB1 - 1) * dB1 :=
        Nat.mul_le_mul_right dB1 (by omega)
      exact nat_mul_le_cancel_left_w5 (nB1 - 1) _ _ hn1_ge2 (Nat.le_trans hrew hm_le)
  have hdB0_le_dR : dB0 ≤ dR := by
    have h1 : nB1 * dB0 + dB1 ≤ nB1 * dR + dB1 :=
      Nat.le_trans hr11_d (Nat.add_le_add (Nat.mul_le_mul_right dR hnT2_le_nB1) hdT2_le_dB1)
    exact nat_mul_le_cancel_left_w5 nB1 _ _ hnB1_pos (by omega)
  -- 6. Eliminate all `c` variables via `mL * (R5.c + R7.c + R9.c + R11.c) + 2 * R2.c`:
  have hr2_c : mL * cB1 + pL * dB1 > mL * cT2 + pL * dT2 := by
    have h := hR2.2.2.2.1
    simp only [evalWordUpperTri2D, compUpperTri2D, hmB1, hmT2,
               Nat.mul_zero, Nat.zero_add, Nat.add_zero] at h
    dsimp [mL, cB1, pL, dB1, cT2, dT2]; omega
  have hr5_c : cB0 + pT1 * dB0 + cT1 > cT0 + pB1 * dT0 + cB1 := by
    have h := hR5.2.2.2.1
    simp only [evalWordUpperTri2D, compUpperTri2D, hmB1, hmT1,
               Nat.one_mul, Nat.mul_zero, Nat.zero_add, Nat.add_zero] at h
    dsimp [cB0, pT1, dB0, cT1, cT0, pB1, dT0, cB1]; omega
  have hr7_c : pT2 * dB0 + cT2 > cT1 + pB0 * dT1 := by
    have h := hR7.2.2.2.1
    simp only [evalWordUpperTri2D, compUpperTri2D, hmB0, hmT2,
               Nat.one_mul, Nat.mul_zero, Nat.zero_add, Nat.add_zero] at h
    dsimp [pT2, dB0, cT2, cT1, pB0, dT1]; omega
  have hr9_c : pT0 * dR + cT0 > pB1 * dR + cB1 := by
    have h := hR9.2.2.2.1
    simp only [evalWordUpperTri2D, compUpperTri2D, hmB1, hmT0,
               Nat.one_mul, Nat.mul_zero, Nat.zero_add, Nat.add_zero] at h
    dsimp [pT0, dR, cT0, pB1, cB1]; omega
  have hr11_c : pT2 * dR + cT2 > pB0 * dR + cB0 + pB1 * dB0 + cB1 := by
    have h := hR11.2.2.2.1
    simp only [evalWordUpperTri2D, compUpperTri2D, hmB0, hmB1, hmT2, hnB0,
               Nat.one_mul, Nat.zero_mul, Nat.mul_zero, Nat.zero_add, Nat.add_zero] at h
    dsimp [pT2, dR, cT2, pB0, cB0, pB1, dB0, cB1]; omega
  have hsum4_c : (pT0 + pT2) * dR + (pT1 + pT2) * dB0 + 2 * cT2 >
      (pB0 + pB1) * dR + pB1 * dB0 + pB1 * dT0 + pB0 * dT1 + 3 * cB1 := by
    rw [Nat.add_mul pT0 pT2 dR, Nat.add_mul pT1 pT2 dB0, Nat.add_mul pB0 pB1 dR]
    omega
  have hm4_c := Nat.mul_lt_mul_of_pos_left hsum4_c hmL_pos
  have hc_elim : mL * ((pT0 + pT2) * dR) + mL * ((pT1 + pT2) * dB0) + 2 * (pL * dB1) >
      mL * ((pB0 + pB1) * dR) + mL * (pB1 * dB0) + mL * (pB1 * dT0) + mL * (pB0 * dT1) := by
    have h1 : mL * ((pT0 + pT2) * dR + (pT1 + pT2) * dB0 + 2 * cT2) =
        mL * ((pT0 + pT2) * dR) + mL * ((pT1 + pT2) * dB0) + 2 * (mL * cT2) := by
      rw [Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc mL 2 cT2,
          Nat.mul_comm mL 2, Nat.mul_assoc 2 mL cT2]
    have h2 : mL * ((pB0 + pB1) * dR + pB1 * dB0 + pB1 * dT0 + pB0 * dT1 + 3 * cB1) =
        mL * ((pB0 + pB1) * dR) + mL * (pB1 * dB0) + mL * (pB1 * dT0) +
          mL * (pB0 * dT1) + 2 * (mL * cB1) + mL * cB1 := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add]
      have h3m : mL * (3 * cB1) = 3 * (mL * cB1) := by
        rw [← Nat.mul_assoc mL 3 cB1, Nat.mul_comm mL 3, Nat.mul_assoc]
      rw [h3m]; omega
    rw [h1, h2] at hm4_c
    omega
  -- 7. Bound `pT0`, `pT1`, `pT2` and pit `(2 * nB1 - 1) * dR` against `nB1 ^ 2 * dR`:
  have hpT0_le : pT0 ≤ pB0 := by omega
  have hdT1_chain : nB1 * nB1 * dR + (nB1 + 1) * dB1 ≤ nT1 * dB0 + dT1 := by
    have hm9 := Nat.mul_le_mul_left nB1 hr9_d
    rw [Nat.mul_add, ← Nat.mul_assoc nB1 nB1 dR] at hm9
    have hadd := Nat.add_le_add_right hm9 dB1
    have hrw : nB1 * dB1 + dB1 = (nB1 + 1) * dB1 := by rw [Nat.add_mul, Nat.one_mul]
    rw [Nat.add_assoc (nB1 * nB1 * dR), hrw] at hadd
    exact Nat.le_trans hadd hr5_d
  have h1_ineq : mL * (pT1 * dB0) + mL * pB0 * (nB1 * nB1 * dR + (nB1 + 1) * dB1) ≤
      mL * (pB0 * dT1) + mL * pB0 * dB0 := by
    have hm_d := Nat.mul_le_mul_left (mL * pB0) hdT1_chain
    have hm_p := Nat.mul_le_mul_left mL (Nat.mul_le_mul_right dB0 hr7_p)
    rw [Nat.mul_add (mL * pB0) (nT1 * dB0) dT1, Nat.mul_assoc mL pB0 dT1] at hm_d
    rw [Nat.add_mul pT1 (pB0 * nT1) dB0, Nat.mul_add mL,
        Nat.mul_assoc pB0 nT1 dB0, ← Nat.mul_assoc mL pB0 (nT1 * dB0),
        ← Nat.mul_assoc mL pB0 dB0] at hm_p
    omega
  have hm_pT2 : mL * pT2 ≤ mL * pB1 + pL * (nB1 - 1) := by
    have hdiff : nB1 - nT2 ≤ nB1 - 1 := by omega
    have h1 : mL * pT2 ≤ mL * pB1 + pL * (nB1 - nT2) := by
      have hp_sp : pL * nB1 = pL * nT2 + pL * (nB1 - nT2) := by
        conv => lhs; rw [show nB1 = nT2 + (nB1 - nT2) by omega]
        rw [Nat.mul_add]
      omega
    exact Nat.le_trans h1 (Nat.add_le_add_left (Nat.mul_le_mul_left pL hdiff) _)
  have h3_ineq : mL * (pT2 * (dR + dB0)) ≤
      mL * (pB1 * (dR + dB0)) + (mL * pB0) * ((nB1 - 1) * (2 * dR)) := by
    have hm1 := Nat.mul_le_mul_right (dR + dB0) hm_pT2
    rw [Nat.mul_assoc mL pT2, Nat.add_mul, Nat.mul_assoc mL pB1] at hm1
    have hm2 : pL * (nB1 - 1) * (dR + dB0) ≤ (mL * pB0) * ((nB1 - 1) * (2 * dR)) := by
      rw [Nat.mul_assoc pL]
      exact Nat.mul_le_mul hr1_p (Nat.mul_le_mul_left (nB1 - 1) (by omega))
    exact Nat.le_trans hm1 (Nat.add_le_add_left hm2 _)
  have h2_ineq : mL * (pT0 * dR) ≤ mL * (pB0 * dR) :=
    Nat.mul_le_mul_left mL (Nat.mul_le_mul_right dR hpT0_le)
  have h4_ineq : 2 * (pL * dB1) ≤ (mL * pB0) * ((nB1 + 1) * dB1) := by
    have hm1 : 2 * (pL * dB1) = pL * (2 * dB1) := by
      rw [← Nat.mul_assoc 2 pL dB1, Nat.mul_comm 2 pL, Nat.mul_assoc]
    rw [hm1]
    exact Nat.mul_le_mul hr1_p (Nat.mul_le_mul_right dB1 (by omega : 2 ≤ nB1 + 1))
  -- Combine `hc_elim` with `h1_ineq`, `h2_ineq`, `h3_ineq`, `h4_ineq`:
  have hlhs_split : mL * ((pT0 + pT2) * dR) + mL * ((pT1 + pT2) * dB0) =
      mL * (pT0 * dR) + mL * (pT1 * dB0) + mL * (pT2 * (dR + dB0)) := by
    rw [Nat.add_mul pT0 pT2 dR, Nat.add_mul pT1 pT2 dB0,
        Nat.mul_add mL, Nat.mul_add mL, Nat.mul_add pT2 dR dB0, Nat.mul_add mL]
    omega
  have hrhs_split : mL * ((pB0 + pB1) * dR) + mL * (pB1 * dB0) =
      mL * (pB0 * dR) + mL * (pB1 * (dR + dB0)) := by
    rw [Nat.add_mul pB0 pB1 dR, Nat.mul_add mL, Nat.mul_add pB1 dR dB0, Nat.mul_add mL]
    omega
  rw [hlhs_split, hrhs_split] at hc_elim
  have hquad_strict : (mL * pB0) * ((nB1 - 1) * (2 * dR)) + (mL * pB0) * dB0 >
      (mL * pB0) * (nB1 * nB1 * dR) := by
    rw [Nat.mul_add (mL * pB0) (nB1 * nB1 * dR) ((nB1 + 1) * dB1)] at h1_ineq
    omega
  have hquad_le : (mL * pB0) * ((nB1 - 1) * (2 * dR)) + (mL * pB0) * dB0 ≤
      (mL * pB0) * (nB1 * nB1 * dR) := by
    rw [← Nat.mul_add (mL * pB0)]
    apply Nat.mul_le_mul_left (mL * pB0)
    have hd1 : (nB1 - 1) * (2 * dR) + dB0 ≤ ((nB1 - 1) * 2 + 1) * dR := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc (nB1 - 1) 2 dR]
      exact Nat.add_le_add_left hdB0_le_dR _
    have hsq : (nB1 - 1) * 2 + 1 ≤ nB1 * nB1 := by
      let u := nB1 - 1
      have hn_eq : nB1 = u + 1 := by dsimp [u]; omega
      rw [hn_eq, Nat.add_mul u 1 (u + 1), Nat.one_mul, Nat.mul_add u u 1, Nat.mul_one]
      have hu2 : 0 ≤ u * u := Nat.zero_le _
      omega
    exact Nat.le_trans hd1 (Nat.mul_le_mul_right dR hsq)
  omega

def zeroTopLeftCounterCert : MixedSRSSym -> NatAffineDim 2
  | .B0 =>
      { M := fun i j => if i.val = 1 ∧ j.val = 1 then 1 else 0
        v := fun _ => 0 }
  | .B1 =>
      { M := natMatId 2
        v := fun i => if i.val = 1 then 1 else 0 }
  | .T2 =>
      { M := fun i j => if i.val = 0 ∨ j.val = 1 then 1 else 0
        v := fun _ => 0 }
  | _ =>
      { M := natMatId 2
        v := fun _ => 0 }

/--
  Theorem W6.2b' (`zero_top_left_breaks_left_context_monotonicity_2d`, choice-free, zero custom axioms):
  Necessity of Hofbauer–Waldmann Top-Left Monotonicity `(M_s)_{0,0} ≥ 1`:
  When `(M_{B0})_{0,0} = 0` is allowed (`zeroTopLeftCounterCert`), `R8` (`[T2, B1] -> [B1, T2]`)
  is strictly oriented on bare LHS/RHS words, yet prepending the single left context symbol `B0`
  (`[B0, T2, B1] -> [B0, B1, T2]`) annihilates coordinate `0` (`0 > 0` fails) and destroys
  rewrite step orientation!
-/
theorem zero_top_left_breaks_left_context_monotonicity_2d :
    (zeroTopLeftCounterCert .B0).M ⟨0, by decide⟩ ⟨0, by decide⟩ = 0 ∧
    orientsNatAffineDim 2 (by decide)
      (evalWordNatAffineDim 2 zeroTopLeftCounterCert [.T2, .B1])
      (evalWordNatAffineDim 2 zeroTopLeftCounterCert [.B1, .T2]) ∧
    ¬ orientsNatAffineDim 2 (by decide)
      (evalWordNatAffineDim 2 zeroTopLeftCounterCert [.B0, .T2, .B1])
      (evalWordNatAffineDim 2 zeroTopLeftCounterCert [.B0, .B1, .T2]) := by
  refine ⟨rfl, ⟨?_, ?_, by decide⟩, ?_⟩
  · intro ⟨i, hi⟩ ⟨j, hj⟩
    match i, j with
    | 0, 0 => revert hi hj; decide
    | 0, 1 => revert hi hj; decide
    | 1, 0 => revert hi hj; decide
    | 1, 1 => revert hi hj; decide
    | k + 2, _ => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 2 k) hi)
    | _, k + 2 => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 2 k) hj)
  · intro ⟨i, hi⟩
    match i with
    | 0 => revert hi; decide
    | 1 => revert hi; decide
    | k + 2 => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 2 k) hi)
  · intro hctx
    have hv0 := hctx.2.2
    revert hv0
    decide

theorem natSumPrefix_zero_w6 (d : Nat) :
    ∀ n : Nat, natSumPrefix d (fun _ => 0) n = 0
  | 0 => rfl
  | n + 1 => by
    simp only [natSumPrefix, natSumPrefix_zero_w6 d n, Nat.zero_add]
    by_cases hn : n < d <;> simp [hn]

/--
  Theorem W6.2b'' (`bipartite_zero_diag_swap_r1_impossibility_all_dim`, zero custom axioms):
  Universal All-Dimension (`∀ d ≥ 1`) Bipartite Zero-Diagonal Block-Swap Impossibility:
  For EVERY dimension `d ≥ 1` and EVERY 2-block coordinate partition `part : Fin d -> Bool`,
  NO bipartite zero-diagonal block-swap matrix interpretation (`part i = part j -> M_L i j = 0 ∧
  M_{B0} i j = 0`, i.e., `M_s = [[0, P_s], [Q_s, 0]]` with all diagonal blocks zero!) can orient
  even `R1_even` (`[L, B0] -> [L]`), because `M_L * M_{B0}` lives strictly on diagonal blocks
  while `M_L` lives on off-diagonal blocks, forcing `M_L = 0` and `(evalWord [L, B0]).v 0 = v_L 0`!
-/
theorem bipartite_zero_diag_swap_r1_impossibility_all_dim
    (d : Nat) (hd : 0 < d)
    (interp : MixedSRSSym -> NatAffineDim d)
    (part : Fin d -> Bool)
    (hswap : ∀ i j : Fin d, part i = part j ->
      (interp .L).M i j = 0 ∧ (interp .B0).M i j = 0)
    (hR1 : orientsNatAffineDim d hd
      (evalWordNatAffineDim d interp [.L, .B0])
      (evalWordNatAffineDim d interp [.L])) :
    False := by
  have hML_zero : ∀ i j : Fin d, (interp .L).M i j = 0 := by
    intro i j
    by_cases hp_eq : part i = part j
    · exact (hswap i j hp_eq).1
    · have hm_ge := hR1.1 i j
      rw [evalWord2_M d interp .L .B0 i j] at hm_ge
      have hr_id : (evalWordNatAffineDim d interp [.L]).M i j = (interp .L).M i j :=
        natMatMul_right_id d (interp .L).M i j
      rw [hr_id] at hm_ge
      have hprod_zero : natMatMul d (interp .L).M (interp .B0).M i j = 0 := by
        unfold natMatMul natSumFin
        have hterm0 : ∀ k : Fin d, (interp .L).M i k * (interp .B0).M k j = 0 := by
          intro k
          by_cases hik : part i = part k
          · rw [(hswap i k hik).1, Nat.zero_mul]
          · have hkj : part k = part j := by
              cases hpi : part i <;> cases hpj : part j <;> cases hpk : part k
              · exact False.elim (hp_eq (hpi.trans hpj.symm))
              · exact False.elim (hp_eq (hpi.trans hpj.symm))
              · exact False.elim (hik (hpi.trans hpk.symm))
              · rfl
              · rfl
              · exact False.elim (hik (hpi.trans hpk.symm))
              · exact False.elim (hp_eq (hpi.trans hpj.symm))
              · exact False.elim (hp_eq (hpi.trans hpj.symm))
            rw [(hswap k j hkj).2, Nat.mul_zero]
        rw [natSumPrefix_congr d _ (fun _ => 0) hterm0 d]
        exact natSumPrefix_zero_w6 d d
      rw [hprod_zero] at hm_ge
      omega
  have hv_zero_vec : ∀ v : Fin d -> Nat,
      natMatVec d (interp .L).M v ⟨0, hd⟩ = 0 := by
    intro v
    unfold natMatVec natSumFin
    have ht0 : ∀ k : Fin d, (interp .L).M ⟨0, hd⟩ k * v k = 0 := by
      intro k; rw [hML_zero ⟨0, hd⟩ k, Nat.zero_mul]
    rw [natSumPrefix_congr d _ (fun _ => 0) ht0 d]
    exact natSumPrefix_zero_w6 d d
  have hlhs_v0 : (evalWordNatAffineDim d interp [.L, .B0]).v ⟨0, hd⟩ = (interp .L).v ⟨0, hd⟩ := by
    simp only [evalWordNatAffineDim, compNatAffineDim]
    rw [hv_zero_vec, Nat.zero_add]
  have hrhs_v0 : (evalWordNatAffineDim d interp [.L]).v ⟨0, hd⟩ = (interp .L).v ⟨0, hd⟩ := by
    simp only [evalWordNatAffineDim, compNatAffineDim]
    rw [hv_zero_vec, Nat.zero_add]
  have hstrict := hR1.2.2
  rw [hlhs_v0, hrhs_v0] at hstrict
  exact Nat.lt_irrefl _ hstrict

/--
  Corollary (`antidiag_swap_2d_r1_impossibility`, zero custom axioms):
  Every `2 x 2` zero-diagonal permutation/swap matrix interpretation
  (`M_L = [[0, p_L], [q_L, 0]]`, `M_{B0} = [[0, p_{B0}], [q_{B0}, 0]]`) collapses unconditionally
  on `R1_even` (`[L, B0] -> [L]`), closing the `d = 2` antidiagonal swap escape hatch!
-/
theorem antidiag_swap_2d_r1_impossibility
    (interp : MixedSRSSym -> NatAffineDim 2)
    (hL00  : (interp .L).M ⟨0, by decide⟩ ⟨0, by decide⟩ = 0)
    (hL11  : (interp .L).M ⟨1, by decide⟩ ⟨1, by decide⟩ = 0)
    (hB000 : (interp .B0).M ⟨0, by decide⟩ ⟨0, by decide⟩ = 0)
    (hB011 : (interp .B0).M ⟨1, by decide⟩ ⟨1, by decide⟩ = 0)
    (hR1 : orientsNatAffineDim 2 (by decide)
      (evalWordNatAffineDim 2 interp [.L, .B0])
      (evalWordNatAffineDim 2 interp [.L])) :
    False := by
  apply bipartite_zero_diag_swap_r1_impossibility_all_dim 2 (by decide) interp
    (fun i => decide (i.val = 1)) _ hR1
  intro ⟨i, hi⟩ ⟨j, hj⟩ heq
  match i, j with
  | 0, 0 => exact ⟨hL00, hB000⟩
  | 1, 1 => exact ⟨hL11, hB011⟩
  | 0, 1 => simp at heq
  | 1, 0 => simp at heq
  | k + 2, _ => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 2 k) hi)
  | _, k + 2 => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 2 k) hj)

-- ============================================================================
-- SECTION 2B: Front B (Branch P5.5) — Variable-Horizon Spiral Block-Return
--             Map on True `(3x+1)`: Unbounded `r`-Block Climb & Universal
--             `∀ L ≥ 1` Multi-Term Laurent Valuation Impossibility
-- ============================================================================

def spiralPow3Aux : Nat -> Nat -> Nat
  | 0, _ => 1
  | fuel + 1, n => if n > 0 ∧ n % 2 = 0 then 3 * spiralPow3Aux fuel (n / 2) else 1

/-- `3 ^ v_2(n)` for `n > 0` (replacing each factor of `2` in `n` by `3`). -/
def spiralPow3 (n : Nat) : Nat :=
  spiralPow3Aux n n

/--
  Variable-horizon spiral block-return map on odd `x ≥ 1`:
  Writing `x + 1 = 2^w * u` (`u = core2 (x + 1)` odd), steps across the entire `w`-step
  odd glide (`x -> 3^w * u - 1`) plus `a = v_2(3^w * u - 1)` halving steps to the next
  odd iterate `core2 (3^w * u - 1)`.
-/
def spiralBlockReturn (x : Nat) : Nat :=
  core2 (spiralPow3 (x + 1) * core2 (x + 1) - 1)

def spiralBlockReturnIter : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => spiralBlockReturnIter k (spiralBlockReturn x)

theorem spiralPow3Aux_eq_of_ge :
    ∀ (f1 f2 n : Nat), n ≤ f1 -> n ≤ f2 -> spiralPow3Aux f1 n = spiralPow3Aux f2 n
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, n, h1, _ => by
    have hn0 : n = 0 := by omega
    rw [hn0]; simp [spiralPow3Aux]
  | _ + 1, 0, n, _, h2 => by
    have hn0 : n = 0 := by omega
    rw [hn0]; simp [spiralPow3Aux]
  | f1 + 1, f2 + 1, n, h1, h2 => by
    simp only [spiralPow3Aux]
    by_cases hc : n > 0 ∧ n % 2 = 0
    · simp only [hc, and_self, ite_true]
      rw [spiralPow3Aux_eq_of_ge f1 f2 (n / 2) (by omega) (by omega)]
    · simp only [hc, ite_false]

theorem spiralPow3_of_odd (n : Nat) (hodd : n % 2 = 1) : spiralPow3 n = 1 := by
  unfold spiralPow3
  cases n with
  | zero => omega
  | succ m =>
    have hnc : ¬ (m + 1 > 0 ∧ (m + 1) % 2 = 0) := by omega
    simp only [spiralPow3Aux, hnc, ite_false]

theorem spiralPow3_mul2 (m : Nat) (hm : m > 0) : spiralPow3 (2 * m) = 3 * spiralPow3 m := by
  unfold spiralPow3
  cases hfuel : 2 * m with
  | zero => omega
  | succ f =>
    have hc : f + 1 > 0 ∧ (f + 1) % 2 = 0 := by omega
    simp only [spiralPow3Aux, hc, and_self, ite_true]
    have hdiv : (f + 1) / 2 = m := by omega
    rw [hdiv, spiralPow3Aux_eq_of_ge f m m (by omega) (by omega)]

theorem spiralPow3_pow2 : ∀ (w u : Nat), u > 0 -> u % 2 = 1 -> spiralPow3 (2 ^ w * u) = 3 ^ w
  | 0, u, _, hodd => by simp [spiralPow3_of_odd u hodd]
  | w + 1, u, hu, hodd => by
    have hmul : 2 ^ (w + 1) * u = 2 * (2 ^ w * u) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ w) 2, Nat.mul_assoc]
    have hpos : 2 ^ w * u > 0 := Nat.mul_pos (pow2_pos_nat w) hu
    rw [hmul, spiralPow3_mul2 (2 ^ w * u) hpos, spiralPow3_pow2 w u hu hodd,
        Nat.pow_succ 3 w, Nat.mul_comm]

theorem core2_pow2_mul : ∀ (w u : Nat), u > 0 -> u % 2 = 1 -> core2 (2 ^ w * u) = u
  | 0, u, _, hodd => by simp [core2_of_odd u hodd]
  | w + 1, u, hu, hodd => by
    have hmul : 2 ^ (w + 1) * u = 2 * (2 ^ w * u) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ w) 2, Nat.mul_assoc]
    have hpos : 2 ^ w * u > 0 := Nat.mul_pos (pow2_pos_nat w) hu
    rw [hmul, core2_mul2 (2 ^ w * u) hpos, core2_pow2_mul w u hu hodd]

theorem spiralBlockReturn_of_pow2_decomp (x w u : Nat)
    (hu_pos : u ≥ 1) (hu_odd : u % 2 = 1) (hxp1 : x + 1 = 2 ^ w * u) :
    spiralBlockReturn x = core2 (3 ^ w * u - 1) ∧
    ∃ K : Nat, K ≥ w ∧ collatzIter K x = spiralBlockReturn x := by
  have hsp : spiralPow3 (x + 1) = 3 ^ w := by rw [hxp1]; exact spiralPow3_pow2 w u hu_pos hu_odd
  have hc2 : core2 (x + 1) = u := by rw [hxp1]; exact core2_pow2_mul w u hu_pos hu_odd
  have hret : spiralBlockReturn x = core2 (3 ^ w * u - 1) := by
    unfold spiralBlockReturn; rw [hsp, hc2]
  refine ⟨hret, ?_⟩
  have hx_eq : x = 2 ^ w * u - 1 := by omega
  have hiter_w : collatzIter w x = 3 ^ w * u - 1 := by
    rw [hx_eq]; exact odd_run_iter w u hu_pos
  have hreach_core2 : ∀ (bound m : Nat), m > 0 -> m ≤ bound -> ∃ a : Nat, collatzIter a m = core2 m := by
    intro bound
    induction bound with
    | zero => intro _ hm hle; omega
    | succ b ih =>
      intro m hm hle
      by_cases hev : m % 2 = 0
      · let k := m / 2
        have hk_pos : k > 0 := by dsimp [k]; omega
        have hm2 : m = 2 * k := by dsimp [k]; omega
        rcases ih k hk_pos (by dsimp [k]; omega) with ⟨a, ha⟩
        refine ⟨a + 1, ?_⟩
        have hstep_m : collatzStep m = k := by
          rw [hm2, collatzStep_double_pos k]
        simp only [collatzIter, hstep_m, ha]
        rw [hm2, core2_mul2 k hk_pos]
      · exact ⟨0, (core2_of_odd m (by omega)).symm⟩
  by_cases h0 : w = 0
  · subst h0
    simp only [Nat.pow_zero, Nat.one_mul] at hxp1 hiter_w hret
    have hx_eq_u : x = u - 1 := by omega
    by_cases hu1 : u = 1
    · have hx0 : x = 0 := by omega
      subst hu1 hx0
      exact ⟨0, Nat.le_refl 0, by rw [hret]; decide⟩
    · rcases hreach_core2 (u - 1) (u - 1) (by omega) (Nat.le_refl _) with ⟨a, ha⟩
      refine ⟨a, by omega, ?_⟩
      rw [hret, hx_eq_u]
      exact ha
  · have hw_pos : w ≥ 1 := by omega
    have h3w_ge3 : 3 ^ w * u ≥ 3 := by
      have hp3 : 3 ^ w ≥ 3 := by
        rw [show w = (w - 1) + 1 by omega, Nat.pow_succ]
        have hp := pow3_pos_nat (w - 1); omega
      have hm := Nat.mul_le_mul hp3 hu_pos; omega
    rcases hreach_core2 (3 ^ w * u - 1) (3 ^ w * u - 1) (by omega) (Nat.le_refl _) with ⟨a, ha⟩
    refine ⟨w + a, by omega, ?_⟩
    rw [collatzIter_add w a x, hiter_w, ha, hret]

theorem spiralBlockReturn_eq_syracuse_of_mod4_eq_1 (x : Nat) (hm4 : x % 4 = 1) :
    spiralBlockReturn x = syracuseOddStep x := by
  let u := (x + 1) / 2
  have hu_pos : u ≥ 1 := by dsimp [u]; omega
  have hu_odd : u % 2 = 1 := by dsimp [u]; omega
  have hxp1 : x + 1 = 2 ^ 1 * u := by simp only [Nat.pow_one]; dsimp [u]; omega
  have hret := (spiralBlockReturn_of_pow2_decomp x 1 u hu_pos hu_odd hxp1).1
  rw [Nat.pow_one] at hret
  let k := (3 * x + 1) / 2
  have hk_pos : k > 0 := by dsimp [k]; omega
  have h3u : 3 * u - 1 = k := by dsimp [u, k]; omega
  have h2k : 3 * x + 1 = 2 * k := by dsimp [k]; omega
  unfold syracuseOddStep
  rw [hret, h3u, h2k, core2_mul2 k hk_pos]

/--
  Theorem W6.2c (`spiral_block_return_unbounded_climb`, zero custom axioms):
  1. For EVERY `r ≥ 1`, `x_0(r) = 4 * 16^r - 5` climbs strictly across `r` consecutive
     variable-horizon spiral block-return steps (`spiralBlockReturnIter j x_0(r) = 4 * 16^(r-j) * 18^j - 5`,
     all odd and `≢ 0 (mod 3)`, reaching `4 * 18^r - 5 > x_0(r)` at `j = r`; minimal `r = 2`
     witness `1019 -> 1147 -> 1291`).
  2. Consequently, NO eventually strictly increasing univariate ranking `V : Nat -> Nat`
     can decrease across `r` spiral block-return steps (`∀ r ≥ 1`)!
-/
theorem spiral_block_return_unbounded_climb :
    spiralBlockReturn 1019 = 1147 ∧
    spiralBlockReturn 1147 = 1291 ∧
    (∀ (j k A : Nat), A ≥ 1 -> j ≤ k ->
      spiralBlockReturnIter j (4 * 16 ^ k * A - 5) = 4 * 16 ^ (k - j) * (18 ^ j * A) - 5) ∧
    (∀ (r xFloor : Nat) (V : Nat -> Nat), r ≥ 1 ->
      (∀ x y : Nat, x ≥ xFloor -> x < y -> V x < V y) ->
      ∃ x : Nat, x ≥ xFloor ∧ x % 2 = 1 ∧ x % 3 ≠ 0 ∧
        ¬ (V (spiralBlockReturnIter r x) < V x)) := by
  have hstep_16 : ∀ (m B : Nat), B ≥ 1 ->
      spiralBlockReturn (4 * 16 ^ (m + 1) * B - 5) = 4 * 16 ^ m * (18 * B) - 5 := by
    intro m B hB_pos
    let u := 16 * (16 ^ m * B) - 1
    have hp16_pos : 16 ^ m ≥ 1 := nat_pow_pos_of_pos 16 (by decide) m
    have hmB_pos : 16 ^ m * B ≥ 1 := Nat.mul_le_mul hp16_pos hB_pos
    have h16mB : 16 * (16 ^ m * B) ≥ 16 := Nat.mul_le_mul_left 16 hmB_pos
    have hu_pos : u ≥ 15 := by dsimp [u]; omega
    have hu_odd : u % 2 = 1 := by dsimp [u]; omega
    have hxp1 : (4 * 16 ^ (m + 1) * B - 5) + 1 = 2 ^ 2 * u := by
      dsimp [u]
      have hrw : 4 * 16 ^ (m + 1) * B = 4 * (16 * (16 ^ m * B)) := by
        rw [Nat.pow_succ 16 m, Nat.mul_comm (16 ^ m) 16,
            Nat.mul_assoc 4 (16 * 16 ^ m) B, Nat.mul_assoc 16 (16 ^ m) B]
      rw [hrw]
      change (4 * (16 * (16 ^ m * B)) - 5) + 1 = 4 * (16 * (16 ^ m * B) - 1)
      omega
    have hret := (spiralBlockReturn_of_pow2_decomp _ 2 u (by omega) hu_odd hxp1).1
    let y := 4 * 16 ^ m * (18 * B) - 5
    have h4y : 4 * (16 ^ m * (18 * B)) ≥ 72 := by
      have h18 : 16 ^ m * (18 * B) = 18 * (16 ^ m * B) := by
        rw [← Nat.mul_assoc (16 ^ m) 18 B, Nat.mul_comm (16 ^ m) 18, Nat.mul_assoc]
      rw [h18, ← Nat.mul_assoc 4 18]
      exact Nat.mul_le_mul_left 72 hmB_pos
    have hy_odd : y % 2 = 1 := by
      dsimp [y]; rw [Nat.mul_assoc 4 (16 ^ m) (18 * B)]; omega
    have hy_pos : y > 0 := by
      dsimp [y]; rw [Nat.mul_assoc 4 (16 ^ m) (18 * B)]; omega
    have h9u : 3 ^ 2 * u - 1 = 2 * y := by
      dsimp [u, y]
      have h72 : 9 * (16 * (16 ^ m * B)) = 2 * (4 * (16 ^ m * (18 * B))) := by
        calc
          9 * (16 * (16 ^ m * B)) = 144 * (16 ^ m * B) := by rw [← Nat.mul_assoc 9 16]
          _ = (2 * (4 * 18)) * (16 ^ m * B) := rfl
          _ = 2 * (4 * (18 * (16 ^ m * B))) := by rw [Nat.mul_assoc 2, Nat.mul_assoc 4]
          _ = 2 * (4 * (16 ^ m * (18 * B))) := by
                rw [← Nat.mul_assoc 18 (16 ^ m) B, Nat.mul_comm 18 (16 ^ m), Nat.mul_assoc (16 ^ m)]
      rw [Nat.mul_assoc 4 (16 ^ m) (18 * B)]
      change 9 * (16 * (16 ^ m * B) - 1) - 1 = 2 * (4 * (16 ^ m * (18 * B)) - 5)
      omega
    rw [hret, h9u, core2_mul2 y hy_pos, core2_of_odd y hy_odd]
  have hind : ∀ (j k A : Nat), A ≥ 1 -> j ≤ k ->
      spiralBlockReturnIter j (4 * 16 ^ k * A - 5) = 4 * 16 ^ (k - j) * (18 ^ j * A) - 5 := by
    intro j
    induction j with
    | zero => intro k A _ _; simp [spiralBlockReturnIter]
    | succ j' ih =>
      intro k A hA_pos hj
      cases k with
      | zero => omega
      | succ k' =>
        simp only [spiralBlockReturnIter]
        rw [hstep_16 k' A hA_pos, ih k' (18 * A) (by omega) (by omega)]
        have hsub : k' + 1 - (j' + 1) = k' - j' := by omega
        have hp18 : 18 ^ (j' + 1) * A = 18 ^ j' * (18 * A) := by
          rw [Nat.pow_succ 18 j', Nat.mul_assoc]
        rw [hsub, hp18]
  refine ⟨by decide, by decide, hind, ?_⟩
  intro r xFloor V hr_pos hmono
  let A := xFloor + 2
  let x := 4 * 16 ^ r * A - 5
  have hp16_ge : 16 ^ r ≥ 16 := by
    rw [show r = (r - 1) + 1 by omega, Nat.pow_succ]
    have hp := nat_pow_pos_of_pos 16 (by decide) (r - 1); omega
  have h16_m3 : ∀ m : Nat, 16 ^ m % 3 = 1 := by
    intro m; induction m with
    | zero => rfl
    | succ m' ihm => rw [Nat.pow_succ, Nat.mul_mod, ihm]
  -- Pick `B` not divisible by 3: `B := 3 * xFloor + 4` (`≥ 4`, `B % 3 = 1`):
  let B := 3 * xFloor + 4
  let xb := 4 * 16 ^ r * B - 5
  have h4_16B : 4 * 16 ^ r * B ≥ 64 * B := by
    have hm := Nat.mul_le_mul_left 4 hp16_ge
    exact Nat.mul_le_mul_right B hm
  have hxb_ge : xb ≥ xFloor := by dsimp [xb, B] at h4_16B ⊢; omega
  have hxb_odd : xb % 2 = 1 := by
    have h16B_ge : 16 ^ r * B ≥ 16 := Nat.mul_le_mul hp16_ge (by dsimp [B]; omega : 1 ≤ B)
    dsimp [xb]; rw [Nat.mul_assoc 4 (16 ^ r) B]; omega
  have hxb_nd3 : xb % 3 ≠ 0 := by
    have hm16 := h16_m3 r
    have hBm3 : B % 3 = 1 := by dsimp [B]; omega
    have hprod_m3 : (4 * 16 ^ r * B) % 3 = 1 := by
      rw [Nat.mul_mod, Nat.mul_mod 4 (16 ^ r) 3, hm16, hBm3]
    dsimp [xb]; omega
  have hiter_r := hind r r B (by dsimp [B]; omega) (Nat.le_refl r)
  rw [Nat.sub_self, Nat.pow_zero, Nat.mul_one] at hiter_r
  have h16_lt_18 : 16 ^ r < 18 ^ r := by
    rw [show r = (r - 1) + 1 by omega, Nat.pow_succ 16, Nat.pow_succ 18]
    have hle := nat_pow_mono_base 16 18 (by decide) (r - 1)
    have hpos := nat_pow_pos_of_pos 16 (by decide) (r - 1)
    have hm1 : 16 ^ (r - 1) * 16 < 16 ^ (r - 1) * 18 :=
      Nat.mul_lt_mul_of_pos_left (by decide : 16 < 18) hpos
    have hm2 : 16 ^ (r - 1) * 18 ≤ 18 ^ (r - 1) * 18 :=
      Nat.mul_le_mul_right 18 hle
    omega
  have hxb_lt_end : xb < spiralBlockReturnIter r xb := by
    rw [hiter_r]; dsimp [xb]
    have hm1 := Nat.mul_lt_mul_of_pos_right
      (Nat.mul_lt_mul_of_pos_left h16_lt_18 (by decide : 0 < 4)) (by dsimp [B]; omega : 0 < B)
    rw [Nat.mul_assoc 4 (18 ^ r) B] at hm1
    omega
  have hV_lt := hmono xb (spiralBlockReturnIter r xb) hxb_ge hxb_lt_end
  exact ⟨xb, hxb_ge, hxb_odd, hxb_nd3, by omega⟩

def laurentDescProp (terms : List LaurentTerm) (A0 B0 C0 x y : Nat) : Prop :=
  evalLaurentSumNum terms y * laurentValDen A0 B0 C0 x <
    evalLaurentSumNum terms x * laurentValDen A0 B0 C0 y

instance (terms : List LaurentTerm) (A0 B0 C0 x y : Nat) :
    Decidable (laurentDescProp terms A0 B0 C0 x y) :=
  inferInstanceAs (Decidable (_ < _))

/--
  Reusable 3-Family Multi-Term Laurent Obstruction (zero custom axioms):
  Across `{97 -> 73}`, `{2 * geomSpineEntry j2 - 1 -> 2 * 4^(3*j2 + 3) - 1}`, and
  `{2 * 4^r - 1 -> (3 * 9^r - 1) / 2}`, NO `L`-term `(2, 3)`-adic Laurent valuation sum
  (`∀ L ≥ 1`) can strictly decrease on all three transitions simultaneously!
-/
theorem three_family_multiterm_laurent_obstruction
    (terms : List LaurentTerm) (A0 B0 C0 : Nat)
    (hnonempty : ∃ t ∈ terms, t.coeff > 0) :
    (¬ laurentDescProp terms A0 B0 C0 97 73) ∨
    (∃ j2 : Nat,
      ¬ laurentDescProp terms A0 B0 C0 (2 * geomSpineEntry j2 - 1) (2 * 4 ^ (3 * j2 + 3) - 1)) ∨
    (∃ r : Nat, r ≥ 1 ∧
      ¬ laurentDescProp terms A0 B0 C0 (2 * 4 ^ r - 1) ((3 * 9 ^ r - 1) / 2)) := by
  let aMax := maxActiveA terms
  let cMax := maxActiveC terms
  rcases exists_active_achieving_max terms hnonempty with
    ⟨⟨tA, hmA, hpA, heA⟩, _, ⟨tC, hmC, hpC, heC⟩⟩
  change tA.aExp = aMax at heA
  change tC.cExp = cMax at heC
  if h97_desc : laurentDescProp terms A0 B0 C0 97 73 then
    have hC0_lt_cMax : C0 < cMax := by
      if hlt : C0 < cMax then exact hlt
      else
        exfalso
        have h97 : evalLaurentSumNum terms 73 * laurentValDen A0 B0 C0 97 <
            evalLaurentSumNum terms 97 * laurentValDen A0 B0 C0 73 := h97_desc
        rcases syracuse_four_witness_valuations with
          ⟨_, _, _, _, _, _, _, _, _, ⟨hv2_98, hv3_98, hg_98⟩, ⟨hv2_74, hv3_74, hg_74⟩⟩
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
              simp only [hc0, Nat.zero_mul, Nat.zero_add]; exact ih_r
        have hge_all := hterm_ge terms (fun t hm hp =>
          Nat.le_trans (active_exps_le_max terms t hm hp).2.2 (by omega))
        omega
    let dc := cMax - C0
    have hdc_pos : dc ≥ 1 := by dsimp [dc]; omega
    have hcMax_eq : cMax = C0 + dc := by dsimp [dc]; omega
    -- Witness 2: `xj2 = 2 * geomSpineEntry j2 - 1 -> yj2 = 2 ^ (6 * j2 + 7) - 1` (`xj2 % 4 = 1`)
    let C2 := sumLaurentCoeffs terms * 2 ^ aMax * 2 ^ cMax * 2 ^ A0
    let j2 := C2 + 1
    let zj := geomSpineEntry j2
    rcases geomSpineEntry_valuations_constant j2 with ⟨h3zj1, hzj_ge, _, _, _, _⟩
    change 3 * zj + 1 = 4 ^ (3 * j2 + 4) at h3zj1
    change zj ≥ 85 at hzj_ge
    let Mj := 4 ^ (3 * j2 + 3)
    have hMj_ge64 : Mj ≥ 64 := by
      dsimp [Mj]; rw [Nat.pow_add 4 (3 * j2) 3]
      have hm := Nat.mul_le_mul_right 64 (nat_pow_pos_of_pos 4 (by decide) (3 * j2))
      simpa using hm
    have h3zj1_M : 3 * zj + 1 = 4 * Mj := by
      rw [h3zj1]; dsimp [Mj]
      rw [show 3 * j2 + 4 = (3 * j2 + 3) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    have hzj_odd : zj % 2 = 1 := by omega
    have hzj_nd3 : zj % 3 ≠ 0 := by
      have hp4_m9 : 4 ^ (3 * j2 + 4) % 9 = 4 := by
        rw [Nat.pow_add 4 (3 * j2) 4, pow4_triple_eq_pow64_w5 j2,
            Nat.mul_mod, pow64_mod9_eq_one_w5 j2]
      rw [← h3zj1] at hp4_m9
      generalize zj = z at hp4_m9 ⊢
      omega
    let xj2 := 2 * zj - 1
    let yj2 := 2 * Mj - 1
    if hxj2_desc : laurentDescProp terms A0 B0 C0 xj2 yj2 then
      have haMax_le : aMax ≤ A0 + dc := by
        if hle : aMax ≤ A0 + dc then exact hle
        else
          exfalso
          have hdesc2 : evalLaurentSumNum terms yj2 * laurentValDen A0 B0 C0 xj2 <
              evalLaurentSumNum terms xj2 * laurentValDen A0 B0 C0 yj2 := hxj2_desc
          have hxjp1 : xj2 + 1 = 2 * zj := by dsimp [xj2]; omega
          have hv2_xj : v2Pow (xj2 + 1) = 2 := by
            rw [hxjp1, v2Pow_mul2 zj (by omega), v2Pow_of_odd zj hzj_odd]
          have hv3_xj : v3Pow (xj2 + 1) = 1 := by
            rw [hxjp1, v3Pow_mul2 zj (by omega), v3Pow_of_not_div3 zj hzj_nd3]
          have hg_xj : coprime23Core (xj2 + 1) = zj := by
            rw [hxjp1, coprime23Core_mul2 zj (by omega), coprime23Core_of_coprime zj hzj_odd hzj_nd3]
          have h2Mj_eq : 2 ^ (6 * j2 + 7) = 2 * Mj := by
            dsimp [Mj]
            rw [pow4_eq_pow2_even (3 * j2 + 3),
                show 2 * (3 * j2 + 3) = 6 * j2 + 6 by omega,
                show 6 * j2 + 7 = (6 * j2 + 6) + 1 by omega,
                Nat.pow_succ, Nat.mul_comm]
          have hyjp1 : yj2 + 1 = 2 ^ (6 * j2 + 7) := by
            rw [h2Mj_eq]; dsimp [yj2]; omega
          rcases pow2_eq_v2Pow_w5 (6 * j2 + 7) with ⟨hv2_raw, hv3_raw, hg_raw⟩
          have hv2_yj : v2Pow (yj2 + 1) = 2 * Mj := by rw [hyjp1, hv2_raw, h2Mj_eq]
          have hv3_yj : v3Pow (yj2 + 1) = 1 := by rw [hyjp1, hv3_raw]
          have hg_yj : coprime23Core (yj2 + 1) = 1 := by rw [hyjp1, hg_raw]
          have hMj_le_zj : Mj ≤ zj := by omega
          have hzj_le_2Mj : zj ≤ 2 * Mj := by omega
          have hlhs2 : Mj ^ (aMax + C0) ≤ evalLaurentSumNum terms yj2 * laurentValDen A0 B0 C0 xj2 := by
            have htA := evalLaurentSumNum_ge_active_term terms tA yj2 hmA hpA
            unfold laurentValNum at htA
            rw [hv2_yj, hv3_yj, hg_yj, heA, Nat.one_pow, Nat.mul_one, Nat.one_pow, Nat.mul_one] at htA
            have hnum_ge : Mj ^ aMax ≤ evalLaurentSumNum terms yj2 :=
              Nat.le_trans (nat_pow_mono_base Mj (2 * Mj) (by omega) aMax) htA
            have hden_ge : Mj ^ C0 ≤ laurentValDen A0 B0 C0 xj2 := by
              unfold laurentValDen
              rw [hv2_xj, hv3_xj, hg_xj, Nat.one_pow, Nat.mul_one]
              have hm := Nat.mul_le_mul (pow2_pos_nat A0) (nat_pow_mono_base Mj zj hMj_le_zj C0)
              simpa using hm
            rw [Nat.pow_add Mj aMax C0]
            exact Nat.mul_le_mul hnum_ge hden_ge
          have hrhs2 : evalLaurentSumNum terms xj2 * laurentValDen A0 B0 C0 yj2 ≤
              C2 * Mj ^ (cMax + A0) := by
            have hnum_le : evalLaurentSumNum terms xj2 ≤
                sumLaurentCoeffs terms * (2 ^ aMax * (2 ^ cMax * Mj ^ cMax)) := by
              apply evalLaurentSumNum_le_sumCoeffs_mul
              intro t hm hp
              rcases active_exps_le_max terms t hm hp with ⟨ha_le, _, hc_le⟩
              unfold laurentValNum
              rw [hv2_xj, hv3_xj, hg_xj, Nat.one_pow, Nat.mul_one]
              have hz_ub : zj ^ t.cExp ≤ 2 ^ cMax * Mj ^ cMax := by
                have h1 : zj ^ t.cExp ≤ (2 * Mj) ^ cMax :=
                  Nat.le_trans (nat_pow_mono_base zj (2 * Mj) hzj_le_2Mj t.cExp)
                    (nat_pow_mono_exp_pos (2 * Mj) t.cExp cMax (by omega) hc_le)
                rwa [mul_pow_local 2 Mj cMax] at h1
              exact Nat.mul_le_mul (pow2_mono_nat ha_le) hz_ub
            have hden_eq : laurentValDen A0 B0 C0 yj2 = 2 ^ A0 * Mj ^ A0 := by
              unfold laurentValDen
              rw [hv2_yj, hv3_yj, hg_yj, Nat.one_pow, Nat.mul_one, Nat.one_pow, Nat.mul_one,
                  mul_pow_local 2 Mj A0]
            rw [hden_eq]
            have hm := Nat.mul_le_mul_right (2 ^ A0 * Mj ^ A0) hnum_le
            have hrw : (sumLaurentCoeffs terms * (2 ^ aMax * (2 ^ cMax * Mj ^ cMax))) *
                (2 ^ A0 * Mj ^ A0) = C2 * Mj ^ (cMax + A0) := by
              dsimp [C2]
              calc
                (sumLaurentCoeffs terms * (2 ^ aMax * (2 ^ cMax * Mj ^ cMax))) * (2 ^ A0 * Mj ^ A0)
                    = (sumLaurentCoeffs terms * 2 ^ aMax * 2 ^ cMax) *
                        (Mj ^ cMax * (2 ^ A0 * Mj ^ A0)) := by
                      rw [← Nat.mul_assoc (sumLaurentCoeffs terms) (2 ^ aMax),
                          ← Nat.mul_assoc (sumLaurentCoeffs terms * 2 ^ aMax) (2 ^ cMax),
                          Nat.mul_assoc (sumLaurentCoeffs terms * 2 ^ aMax * 2 ^ cMax)]
                _ = (sumLaurentCoeffs terms * 2 ^ aMax * 2 ^ cMax) *
                        (2 ^ A0 * (Mj ^ cMax * Mj ^ A0)) := by
                      rw [← Nat.mul_assoc (Mj ^ cMax) (2 ^ A0),
                          Nat.mul_comm (Mj ^ cMax) (2 ^ A0),
                          Nat.mul_assoc (2 ^ A0) (Mj ^ cMax)]
                _ = C2 * Mj ^ (cMax + A0) := by
                      dsimp [C2]; rw [← Nat.mul_assoc, ← Nat.pow_add]
            rwa [hrw] at hm
          have hcomb2 : Mj ^ (aMax + C0) < C2 * Mj ^ (cMax + A0) :=
            Nat.lt_of_le_of_lt hlhs2 (Nat.lt_of_lt_of_le hdesc2 hrhs2)
          have hexp_ge : 1 + (cMax + A0) ≤ aMax + C0 := by dsimp [dc] at hle; omega
          have hM_split : Mj * Mj ^ (cMax + A0) ≤ Mj ^ (aMax + C0) := by
            have hm := nat_pow_mono_exp_pos Mj _ _ (by omega) hexp_ge
            rwa [Nat.pow_add Mj 1, Nat.pow_one] at hm
          have hcancM := nat_mul_lt_cancel_right_w5 (Mj ^ (cMax + A0)) _ _
            (nat_pow_pos_of_pos Mj (by omega) _) (Nat.lt_of_le_of_lt hM_split hcomb2)
          have hMj_gt_j : Mj ≥ j2 + 1 := by
            dsimp [Mj]
            have h1 : 4 ^ (3 * j2 + 3) ≥ 2 ^ j2 :=
              Nat.le_trans (pow2_mono_nat (by omega : j2 ≤ 3 * j2 + 3))
                (nat_pow_mono_base 2 4 (by decide) (3 * j2 + 3))
            exact Nat.le_trans (pow2_ge_succ_self j2) h1
          dsimp [j2] at hcancM hMj_gt_j
          omega
      -- Witness 3: `xr3 = 2 ^ (2 * r + 1) - 1 -> yr3 = (3 * 9^r - 1) / 2` in ONE spiral block!
      let C3 := sumLaurentCoeffs terms * 2 ^ aMax * 2 ^ A0
      let r := 4 ^ dc * C3 + 1
      have hr_pos : r ≥ 1 := by dsimp [r]; omega
      let xr3 := 2 * 4 ^ r - 1
      let yr3 := (3 * 9 ^ r - 1) / 2
      let gr := (3 * 9 ^ r + 1) / 4
      have hp4_ge4 : 4 ^ r ≥ 4 := by
        have hm := (pow4_ge_four_and_mod3_w5 (r - 1)).1
        rwa [show r - 1 + 1 = r by omega] at hm
      have hp9_ge9 : 9 ^ r ≥ 9 := by
        rw [show r = (r - 1) + 1 by omega, Nat.pow_succ]
        have hp := nat_pow_pos_of_pos 9 (by decide) (r - 1); omega
      have hp9_m8 : 9 ^ r % 8 = 1 := pow9_mod8_eq_one_w5 r
      have hp9_m3 : 9 ^ r % 3 = 0 := by
        rw [show r = (r - 1) + 1 by omega, Nat.pow_succ]; omega
      have hxr3_ge3 : xr3 ≥ 3 := by dsimp [xr3]; omega
      have hxr3_odd : xr3 % 2 = 1 := by dsimp [xr3]; omega
      have hyr3_ge3 : yr3 ≥ 3 := by dsimp [yr3]; omega
      have hyr3_odd : yr3 % 2 = 1 := by dsimp [yr3]; omega
      have hxrp1_pow2 : xr3 + 1 = 2 ^ (2 * r + 1) := by
        dsimp [xr3]; rw [pow4_eq_pow2_even r, Nat.pow_succ, Nat.mul_comm]
        have hp := pow2_pos_nat (2 * r); omega
      if hxr3_desc : laurentDescProp terms A0 B0 C0 xr3 yr3 then
        exfalso
        rcases pow2_eq_v2Pow_w5 (2 * r + 1) with ⟨hv2_raw, hv3_raw, hg_raw⟩
        have h2_4r : 2 ^ (2 * r + 1) = 2 * 4 ^ r := by
          rw [pow4_eq_pow2_even r, Nat.pow_succ, Nat.mul_comm]
        have hv2_xr : v2Pow (xr3 + 1) = 2 * 4 ^ r := by rw [hxrp1_pow2, hv2_raw, h2_4r]
        have hv3_xr : v3Pow (xr3 + 1) = 1 := by rw [hxrp1_pow2, hv3_raw]
        have hg_xr : coprime23Core (xr3 + 1) = 1 := by rw [hxrp1_pow2, hg_raw]
        have hyrp1 : yr3 + 1 = 2 * gr := by dsimp [yr3, gr]; omega
        have hgr_pos : gr ≥ 7 := by dsimp [gr]; omega
        have hgr_odd : gr % 2 = 1 := by dsimp [gr]; omega
        have hgr_nd3 : gr % 3 ≠ 0 := by dsimp [gr]; omega
        have hv2_yr : v2Pow (yr3 + 1) = 2 := by
          rw [hyrp1, v2Pow_mul2 gr (by omega), v2Pow_of_odd gr hgr_odd]
        have hv3_yr : v3Pow (yr3 + 1) = 1 := by
          rw [hyrp1, v3Pow_mul2 gr (by omega), v3Pow_of_not_div3 gr hgr_nd3]
        have hg_yr : coprime23Core (yr3 + 1) = gr := by
          rw [hyrp1, coprime23Core_mul2 gr (by omega), coprime23Core_of_coprime gr hgr_odd hgr_nd3]
        have hlhs3 : gr ^ cMax * 4 ^ (r * A0) ≤
            evalLaurentSumNum terms yr3 * laurentValDen A0 B0 C0 xr3 := by
          have htC := evalLaurentSumNum_ge_active_term terms tC yr3 hmC hpC
          unfold laurentValNum at htC
          rw [hv2_yr, hv3_yr, hg_yr, heC, Nat.one_pow, Nat.mul_one] at htC
          have hnum_ge : gr ^ cMax ≤ evalLaurentSumNum terms yr3 := by
            have hm := Nat.mul_le_mul_right (gr ^ cMax) (pow2_pos_nat tC.aExp)
            rw [Nat.one_mul] at hm; exact Nat.le_trans hm htC
          have hden_ge : 4 ^ (r * A0) ≤ laurentValDen A0 B0 C0 xr3 := by
            unfold laurentValDen
            rw [hv2_xr, hv3_xr, hg_xr, Nat.one_pow, Nat.mul_one, Nat.one_pow, Nat.mul_one,
                mul_pow_local 2 (4 ^ r) A0, pow_pow_eq_mul_w5 4 r A0]
            have hm := Nat.mul_le_mul_right (4 ^ (r * A0)) (pow2_pos_nat A0)
            simpa using hm
          exact Nat.mul_le_mul hnum_ge hden_ge
        have hrhs3 : evalLaurentSumNum terms xr3 * laurentValDen A0 B0 C0 yr3 ≤
            C3 * 4 ^ (r * (A0 + dc)) * gr ^ C0 := by
          have hnum_le : evalLaurentSumNum terms xr3 ≤
              sumLaurentCoeffs terms * (2 ^ aMax * 4 ^ (r * (A0 + dc))) := by
            apply evalLaurentSumNum_le_sumCoeffs_mul
            intro t hm hp
            rcases active_exps_le_max terms t hm hp with ⟨ha_le, _, _⟩
            unfold laurentValNum
            rw [hv2_xr, hv3_xr, hg_xr, Nat.one_pow, Nat.mul_one, Nat.one_pow, Nat.mul_one,
                mul_pow_local 2 (4 ^ r) t.aExp, pow_pow_eq_mul_w5 4 r t.aExp]
            exact Nat.mul_le_mul (pow2_mono_nat ha_le)
              (nat_pow_mono_exp_pos 4 _ _ (by decide)
                (Nat.mul_le_mul_left r (Nat.le_trans ha_le haMax_le)))
          have hden_eq : laurentValDen A0 B0 C0 yr3 = 2 ^ A0 * gr ^ C0 := by
            unfold laurentValDen; rw [hv2_yr, hv3_yr, hg_yr, Nat.one_pow, Nat.mul_one]
          rw [hden_eq]
          have hm := Nat.mul_le_mul_right (2 ^ A0 * gr ^ C0) hnum_le
          have hrw : (sumLaurentCoeffs terms * (2 ^ aMax * 4 ^ (r * (A0 + dc)))) *
              (2 ^ A0 * gr ^ C0) = C3 * 4 ^ (r * (A0 + dc)) * gr ^ C0 := by
            dsimp [C3]
            calc
              (sumLaurentCoeffs terms * (2 ^ aMax * 4 ^ (r * (A0 + dc)))) * (2 ^ A0 * gr ^ C0)
                  = (sumLaurentCoeffs terms * 2 ^ aMax) *
                      (4 ^ (r * (A0 + dc)) * (2 ^ A0 * gr ^ C0)) := by
                    rw [← Nat.mul_assoc (sumLaurentCoeffs terms) (2 ^ aMax), Nat.mul_assoc]
              _ = (sumLaurentCoeffs terms * 2 ^ aMax) *
                      ((2 ^ A0 * 4 ^ (r * (A0 + dc))) * gr ^ C0) := by
                    rw [← Nat.mul_assoc (4 ^ (r * (A0 + dc))),
                        Nat.mul_comm (4 ^ (r * (A0 + dc))) (2 ^ A0)]
              _ = C3 * 4 ^ (r * (A0 + dc)) * gr ^ C0 := by rw [← Nat.mul_assoc, ← Nat.mul_assoc]
          rwa [hrw] at hm
        have hcomb3 : gr ^ cMax * 4 ^ (r * A0) < C3 * 4 ^ (r * (A0 + dc)) * gr ^ C0 :=
          Nat.lt_of_le_of_lt hlhs3 (Nat.lt_of_lt_of_le hxr3_desc hrhs3)
        rw [hcMax_eq, Nat.pow_add gr C0 dc, Nat.mul_add r A0 dc, Nat.pow_add 4 (r * A0) (r * dc)] at hcomb3
        have hcanc_base : gr ^ dc < C3 * 4 ^ (r * dc) := by
          apply nat_mul_lt_cancel_right_w5 (4 ^ (r * A0) * gr ^ C0) _ _
            (Nat.mul_pos (nat_pow_pos_of_pos 4 (by decide) _) (nat_pow_pos_of_pos gr (by omega) C0))
          have hl : gr ^ dc * (4 ^ (r * A0) * gr ^ C0) = (gr ^ C0 * gr ^ dc) * 4 ^ (r * A0) := by
            calc
              gr ^ dc * (4 ^ (r * A0) * gr ^ C0)
                  = (gr ^ dc * 4 ^ (r * A0)) * gr ^ C0 := (Nat.mul_assoc _ _ _).symm
              _ = (4 ^ (r * A0) * gr ^ dc) * gr ^ C0 := by rw [Nat.mul_comm (gr ^ dc) (4 ^ (r * A0))]
              _ = 4 ^ (r * A0) * (gr ^ C0 * gr ^ dc) := by
                    rw [Nat.mul_assoc (4 ^ (r * A0)), Nat.mul_comm (gr ^ dc) (gr ^ C0)]
              _ = (gr ^ C0 * gr ^ dc) * 4 ^ (r * A0) := Nat.mul_comm _ _
          have hr : (C3 * 4 ^ (r * dc)) * (4 ^ (r * A0) * gr ^ C0) =
              C3 * (4 ^ (r * A0) * 4 ^ (r * dc)) * gr ^ C0 := by
            calc
              (C3 * 4 ^ (r * dc)) * (4 ^ (r * A0) * gr ^ C0)
                  = C3 * (4 ^ (r * dc) * (4 ^ (r * A0) * gr ^ C0)) := Nat.mul_assoc _ _ _
              _ = C3 * ((4 ^ (r * A0) * 4 ^ (r * dc)) * gr ^ C0) := by
                    rw [← Nat.mul_assoc (4 ^ (r * dc)), Nat.mul_comm (4 ^ (r * dc)) (4 ^ (r * A0))]
              _ = C3 * (4 ^ (r * A0) * 4 ^ (r * dc)) * gr ^ C0 := (Nat.mul_assoc _ _ _).symm
          rw [hl, hr]; exact hcomb3
        have hm4 := Nat.mul_lt_mul_of_pos_left hcanc_base (nat_pow_pos_of_pos 4 (by decide) dc)
        have h4gr : 9 ^ r ≤ 4 * gr := by dsimp [gr]; omega
        have hpow_gr : 9 ^ (r * dc) ≤ 4 ^ dc * gr ^ dc := by
          rw [← pow_pow_eq_mul_w5 9 r dc, ← mul_pow_local 4 gr dc]
          exact nat_pow_mono_base (9 ^ r) (4 * gr) h4gr dc
        have hlt_9_4 : 9 ^ (r * dc) < (4 ^ dc * C3) * 4 ^ (r * dc) := by
          rw [Nat.mul_assoc (4 ^ dc)]; exact Nat.lt_of_le_of_lt hpow_gr hm4
        let E := r * dc
        have hr_le_E : r ≤ E := by
          dsimp [E]; have hm := Nat.mul_le_mul_left r hdc_pos; simpa using hm
        have h8_le_9 : 2 ^ E * 4 ^ E ≤ 9 ^ E := by
          rw [← mul_pow_local 2 4 E]; exact nat_pow_mono_base 8 9 (by decide) E
        have h2E_ge : r + 1 ≤ 2 ^ E := Nat.le_trans (pow2_ge_succ_self r) (pow2_mono_nat hr_le_E)
        have hl_ge : (r + 1) * 4 ^ E ≤ 9 ^ E :=
          Nat.le_trans (Nat.mul_le_mul_right (4 ^ E) h2E_ge) h8_le_9
        have hcanc4 := nat_mul_lt_cancel_right_w5 (4 ^ E) _ _
          (nat_pow_pos_of_pos 4 (by decide) E) (Nat.lt_of_le_of_lt hl_ge hlt_9_4)
        dsimp [r] at hcanc4
        omega
      else
        exact Or.inr (Or.inr ⟨r, hr_pos, hxr3_desc⟩)
    else
      exact Or.inr (Or.inl ⟨j2, hxj2_desc⟩)
  else
    exact Or.inl h97_desc

/--
  Theorem W6.2d (`spiral_block_return_multiterm_laurent_impossibility`, zero custom axioms):
  Universal All-Length (`∀ L ≥ 1`) Multi-Term Laurent Valuation Impossibility on `spiralBlockReturn`:
  Stepping across variable-horizon spiral blocks does NOT rescue `L`-term `(2, 3)`-adic Laurent
  valuation sums: for EVERY `terms : List LaurentTerm` with `∃ t ∈ terms, t.coeff > 0` and EVERY
  denominator shift `(A0 B0 C0 : Nat)`, there exists an explicit odd `x ≥ 3` (`spiralBlockReturn x ≥ 3`)
  where strict spiral block-return descent FAILS!
-/
theorem spiral_block_return_multiterm_laurent_impossibility
    (terms : List LaurentTerm) (A0 B0 C0 : Nat)
    (hnonempty : ∃ t ∈ terms, t.coeff > 0) :
    ∃ x : Nat,
      x ≥ 3 ∧ x % 2 = 1 ∧ spiralBlockReturn x ≥ 3 ∧
      ¬ (evalLaurentSumNum terms (spiralBlockReturn x) * laurentValDen A0 B0 C0 x <
          evalLaurentSumNum terms x * laurentValDen A0 B0 C0 (spiralBlockReturn x)) := by
  rcases three_family_multiterm_laurent_obstruction terms A0 B0 C0 hnonempty with
    h97 | ⟨j2, hj2⟩ | ⟨r, hr_pos, hr3⟩
  · have hsb97 : spiralBlockReturn 97 = 73 := by decide
    refine ⟨97, by decide, by decide, by rw [hsb97]; decide, ?_⟩
    rw [hsb97]; exact h97
  · let zj := geomSpineEntry j2
    let Mj := 4 ^ (3 * j2 + 3)
    rcases geomSpineEntry_valuations_constant j2 with ⟨h3zj1, hzj_ge, _, _, _, _⟩
    change 3 * zj + 1 = 4 ^ (3 * j2 + 4) at h3zj1
    change zj ≥ 85 at hzj_ge
    have hMj_ge64 : Mj ≥ 64 := by
      dsimp [Mj]; rw [Nat.pow_add 4 (3 * j2) 3]
      have hm := Nat.mul_le_mul_right 64 (nat_pow_pos_of_pos 4 (by decide) (3 * j2))
      simpa using hm
    have h3zj1_M : 3 * zj + 1 = 4 * Mj := by
      rw [h3zj1]; dsimp [Mj]
      rw [show 3 * j2 + 4 = (3 * j2 + 3) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    have hzj_odd : zj % 2 = 1 := by omega
    let xj2 := 2 * zj - 1
    let yj2 := 2 * Mj - 1
    have hxj2_m4 : xj2 % 4 = 1 := by dsimp [xj2]; omega
    have hyj2_odd : yj2 % 2 = 1 := by dsimp [yj2]; omega
    have hsyr_xj2 : syracuseOddStep xj2 = yj2 := by
      unfold syracuseOddStep
      have h3x : 3 * xj2 + 1 = 2 * (2 * yj2) := by dsimp [xj2, yj2]; omega
      rw [h3x, core2_mul2 (2 * yj2) (by omega), core2_mul2 yj2 (by omega), core2_of_odd yj2 hyj2_odd]
    have hsb_xj2 : spiralBlockReturn xj2 = yj2 :=
      (spiralBlockReturn_eq_syracuse_of_mod4_eq_1 xj2 hxj2_m4).trans hsyr_xj2
    refine ⟨xj2, by dsimp [xj2]; omega, by dsimp [xj2]; omega, by rw [hsb_xj2]; dsimp [yj2]; omega, ?_⟩
    rw [hsb_xj2]; exact hj2
  · let xr3 := 2 * 4 ^ r - 1
    let yr3 := (3 * 9 ^ r - 1) / 2
    have hp4_ge4 : 4 ^ r ≥ 4 := by
      have hm := (pow4_ge_four_and_mod3_w5 (r - 1)).1
      rwa [show r - 1 + 1 = r by omega] at hm
    have hp9_ge9 : 9 ^ r ≥ 9 := by
      rw [show r = (r - 1) + 1 by omega, Nat.pow_succ]
      have hp := nat_pow_pos_of_pos 9 (by decide) (r - 1); omega
    have hp9_m8 : 9 ^ r % 8 = 1 := pow9_mod8_eq_one_w5 r
    have hyr3_odd : yr3 % 2 = 1 := by dsimp [yr3]; omega
    have hxrp1_pow2 : xr3 + 1 = 2 ^ (2 * r + 1) * 1 := by
      dsimp [xr3]; rw [Nat.mul_one, pow4_eq_pow2_even r, Nat.pow_succ, Nat.mul_comm]
      have hp := pow2_pos_nat (2 * r); omega
    have hsb_xr3 : spiralBlockReturn xr3 = yr3 := by
      have hret := (spiralBlockReturn_of_pow2_decomp xr3 (2 * r + 1) 1 (by decide) (by decide) hxrp1_pow2).1
      have h3_2r1 : 3 ^ (2 * r + 1) * 1 - 1 = 2 * yr3 := by
        rw [Nat.mul_one, Nat.pow_succ 3 (2 * r), Nat.mul_comm (3 ^ (2 * r)) 3,
            ← pow9_eq_pow3_double r]
        dsimp [yr3]; omega
      rw [hret, h3_2r1, core2_mul2 yr3 (by omega), core2_of_odd yr3 hyr3_odd]
    refine ⟨xr3, by dsimp [xr3]; omega, by dsimp [xr3]; omega, by rw [hsb_xr3]; dsimp [yr3]; omega, ?_⟩
    rw [hsb_xr3]; exact hr3

-- ============================================================================
-- SECTION 2C: Front B — 3rd Solvable Mixed-(2,3) Cousin `T_diamond3`:
--             Defeats ALL `L`-Term Laurent Valuation Sums Yet Solved Globally
--             via Variable-Horizon Block-Return / Counter Ranking (Zero Custom Axioms)
-- ============================================================================

/-- Cone 4 of `T_diamond3`: `3 * x + 5 = 2 ^ (2 * r + 3)` (`r ≥ 3`, starting at `x = 169 -> 127`). -/
def isDiamond3Cone4 (x : Nat) : Prop :=
  x ≥ 169 ∧ x % 8 = 1 ∧ core2 (3 * x + 5) = 1

instance (x : Nat) : Decidable (isDiamond3Cone4 x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/--
  3rd solvable mixed-(2,3) Collatz cousin `T_diamond3` on `Nat`:
  - Odd `x`:
    * Cone 4 (`isDiamond3Cone4 x`): `(3 * x + 1) / 4`;
    * Cone 1 (`x > 1 ∧ x % 16 = 1 ∧ x % 3 ≠ 2 ∧ core3 (2 * x + 1) ≠ 1`): `(3 * x + 1) / 4`;
    * Cone 2 (`x ≥ 73 ∧ x % 64 = 9 ∧ x % 3 ≠ 2 ∧ core3 (2 * x + 1) ≠ 1`): `(3 * x + 1) / 4`;
    * Cone 3 (`x ≥ 17 ∧ core3 (x + 1) = 2`): `(3 * x + 1) / 4`;
    * All other odd `x` (including all `x % 4 = 3` Mersenne glides and `y_r = (3 * 9^r - 1)/2`):
      `(3 * x + 1) / 2`;
  - Even `x`:
    * `x ≥ 20 ∧ x % 18 = 2`: `(x - 2) / 9` (draining `e_{j+1} = (9^(j+1) - 1) / 4 -> e_j`);
    * `x > 2 ∧ x % 6 = 2`: `(x - 2) / 3`;
    * `x > 2 ∧ x % 8 = 6`: `(x - 2) / 2`;
    * All other even `x`: `x / 2`.
-/
def cousinDiamond3Step (x : Nat) : Nat :=
  if x % 2 = 1 then
    if isDiamond3Cone4 x ∨
       (x > 1 ∧ x % 16 = 1 ∧ x % 3 ≠ 2 ∧ core3 (2 * x + 1) ≠ 1) ∨
       (x ≥ 73 ∧ x % 64 = 9 ∧ x % 3 ≠ 2 ∧ core3 (2 * x + 1) ≠ 1) ∨
       (x ≥ 17 ∧ core3 (x + 1) = 2)
    then (3 * x + 1) / 4
    else (3 * x + 1) / 2
  else if x ≥ 20 ∧ x % 18 = 2 then (x - 2) / 9
  else if x > 2 ∧ x % 6 = 2 then (x - 2) / 3
  else if x > 2 ∧ x % 8 = 6 then (x - 2) / 2
  else x / 2

def cousinDiamond3Iter : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamond3Iter k (cousinDiamond3Step x)

theorem cousinDiamond3Iter_add : ∀ (a b x : Nat),
    cousinDiamond3Iter (a + b) x = cousinDiamond3Iter b (cousinDiamond3Iter a x)
  | 0, _, _ => by simp [cousinDiamond3Iter]
  | a + 1, b, x => by
    rw [Nat.succ_add]
    exact cousinDiamond3Iter_add a b (cousinDiamond3Step x)

/-- Signed extension of `T_diamond3` (`q = 3`) to `Int` for `M2 = Z^-` separation -/
def cousinDiamond3StepInt (x : Int) : Int :=
  if x % 2 ≠ 0 then
    if (x ≥ 169 ∧ x % 8 = 1 ∧ core2 (3 * x.toNat + 5) = 1) ∨
       (x > 1 ∧ x % 16 = 1 ∧ x % 3 ≠ 2 ∧ core3 (2 * x.toNat + 1) ≠ 1) ∨
       (x ≥ 73 ∧ x % 64 = 9 ∧ x % 3 ≠ 2 ∧ core3 (2 * x.toNat + 1) ≠ 1) ∨
       (x ≥ 17 ∧ core3 (x.toNat + 1) = 2)
    then (3 * x + 1) / 4
    else (3 * x + 1) / 2
  else if x ≥ 20 ∧ x % 18 = 2 then (x - 2) / 9
  else if x > 2 ∧ x % 6 = 2 then (x - 2) / 3
  else if x > 2 ∧ x % 8 = 6 then (x - 2) / 2
  else x / 2

def cousinDiamond3IterInt : Nat -> Int -> Int
  | 0, x => x
  | k + 1, x => cousinDiamond3IterInt k (cousinDiamond3StepInt x)

/-- Canonical reduced-pair extension of `T_diamond3` (`q = 3`) to positive `Q_(6)^+` -/
def cousinDiamond3StepQ6 (p : Nat × Nat) : Nat × Nat :=
  let num := p.1
  let den := p.2
  let r64 := (num * invMod64Odd den) % 64
  let r3 := (num * (den % 3)) % 3
  if r64 % 2 = 1 then
    if (num ≥ 169 * den ∧ r64 % 8 = 1 ∧ core2 (3 * num + 5 * den) = den) ∨
       (num > den ∧ r64 % 16 = 1 ∧ r3 ≠ 2 ∧ core3 (2 * num + den) ≠ den) ∨
       (num ≥ 73 * den ∧ r64 = 9 ∧ r3 ≠ 2 ∧ core3 (2 * num + den) ≠ den) ∨
       (num ≥ 17 * den ∧ core3 (num + den) = 2 * den)
    then reduceRatPair (3 * num + den) (4 * den)
    else reduceRatPair (3 * num + den) (2 * den)
  else if num ≥ 20 * den ∧ num % 18 = (2 * den) % 18 then reduceRatPair (num - 2 * den) (9 * den)
  else if num > 2 * den ∧ r3 = 2 then reduceRatPair (num - 2 * den) (3 * den)
  else if num > 2 * den ∧ r64 % 8 = 6 then reduceRatPair (num - 2 * den) (2 * den)
  else reduceRatPair num (2 * den)

def cousinDiamond3IterQ6 : Nat -> (Nat × Nat) -> (Nat × Nat)
  | 0, p => p
  | k + 1, p => cousinDiamond3IterQ6 k (cousinDiamond3StepQ6 p)

/-- Generalized odd-multiplier `q` step of `T_diamond3` on `Nat` for `M3` (`q = 7`) separation -/
def cousinDiamond3StepParam (q x : Nat) : Nat :=
  if x % 2 = 1 then
    if isDiamond3Cone4 x ∨
       (x > 1 ∧ x % 16 = 1 ∧ x % 3 ≠ 2 ∧ core3 (2 * x + 1) ≠ 1) ∨
       (x ≥ 73 ∧ x % 64 = 9 ∧ x % 3 ≠ 2 ∧ core3 (2 * x + 1) ≠ 1) ∨
       (x ≥ 17 ∧ core3 (x + 1) = 2)
    then (q * x + 1) / 4
    else (q * x + 1) / 2
  else if x ≥ 20 ∧ x % 18 = 2 then (x - 2) / 9
  else if x > 2 ∧ x % 6 = 2 then (x - 2) / 3
  else if x > 2 ∧ x % 8 = 6 then (x - 2) / 2
  else x / 2

def cousinDiamond3IterParam (q : Nat) : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamond3IterParam q k (cousinDiamond3StepParam q x)

/--
  Exact `Nat`/`Int` step agreement for `T_diamond3` (zero custom axioms).
-/
theorem cousinDiamond3StepInt_ofNat_eq (x : Nat) :
    cousinDiamond3StepInt (x : Int) = (cousinDiamond3Step x : Int) := by
  unfold cousinDiamond3StepInt cousinDiamond3Step isDiamond3Cone4
  have htoNat : (x : Int).toNat = x := rfl
  rw [htoNat]
  by_cases hodd : x % 2 = 1
  · have hodd_i : (x : Int) % 2 ≠ 0 := by omega
    simp only [hodd_i, hodd, ne_eq, not_false_eq_true, ite_true]
    have hcond_iff :
        (((x : Int) ≥ 169 ∧ (x : Int) % 8 = 1 ∧ core2 (3 * x + 5) = 1) ∨
         ((x : Int) > 1 ∧ (x : Int) % 16 = 1 ∧ (x : Int) % 3 ≠ 2 ∧ core3 (2 * x + 1) ≠ 1) ∨
         ((x : Int) ≥ 73 ∧ (x : Int) % 64 = 9 ∧ (x : Int) % 3 ≠ 2 ∧ core3 (2 * x + 1) ≠ 1) ∨
         ((x : Int) ≥ 17 ∧ core3 (x + 1) = 2)) ↔
        ((x ≥ 169 ∧ x % 8 = 1 ∧ core2 (3 * x + 5) = 1) ∨
         (x > 1 ∧ x % 16 = 1 ∧ x % 3 ≠ 2 ∧ core3 (2 * x + 1) ≠ 1) ∨
         (x ≥ 73 ∧ x % 64 = 9 ∧ x % 3 ≠ 2 ∧ core3 (2 * x + 1) ≠ 1) ∨
         (x ≥ 17 ∧ core3 (x + 1) = 2)) := by
      generalize core2 (3 * x + 5) = c1, core3 (2 * x + 1) = c2, core3 (x + 1) = c3
      omega
    by_cases hq : (x ≥ 169 ∧ x % 8 = 1 ∧ core2 (3 * x + 5) = 1) ∨
        (x > 1 ∧ x % 16 = 1 ∧ x % 3 ≠ 2 ∧ core3 (2 * x + 1) ≠ 1) ∨
        (x ≥ 73 ∧ x % 64 = 9 ∧ x % 3 ≠ 2 ∧ core3 (2 * x + 1) ≠ 1) ∨
        (x ≥ 17 ∧ core3 (x + 1) = 2)
    · have hq_i := hcond_iff.mpr hq
      simp only [hq_i, hq, ite_true]; omega
    · have hnq_i : ¬ (((x : Int) ≥ 169 ∧ (x : Int) % 8 = 1 ∧ core2 (3 * x + 5) = 1) ∨
          ((x : Int) > 1 ∧ (x : Int) % 16 = 1 ∧ (x : Int) % 3 ≠ 2 ∧ core3 (2 * x + 1) ≠ 1) ∨
          ((x : Int) ≥ 73 ∧ (x : Int) % 64 = 9 ∧ (x : Int) % 3 ≠ 2 ∧ core3 (2 * x + 1) ≠ 1) ∨
          ((x : Int) ≥ 17 ∧ core3 (x + 1) = 2)) := fun hi => hq (hcond_iff.mp hi)
      simp only [hnq_i, hq, ite_false]; omega
  · have hev_i : (x : Int) % 2 = 0 := by omega
    simp only [hev_i, hodd, ne_eq, not_true_eq_false, ite_false]
    by_cases h18 : x ≥ 20 ∧ x % 18 = 2
    · have h18_i : (x : Int) ≥ 20 ∧ (x : Int) % 18 = 2 := by omega
      simp only [h18_i, h18, and_self, ite_true]; omega
    · have hn18_i : ¬ ((x : Int) ≥ 20 ∧ (x : Int) % 18 = 2) := by omega
      simp only [hn18_i, h18, ite_false]
      by_cases h6 : x > 2 ∧ x % 6 = 2
      · have h6_i : (x : Int) > 2 ∧ (x : Int) % 6 = 2 := by omega
        simp only [h6_i, h6, and_self, ite_true]; omega
      · have hn6_i : ¬ ((x : Int) > 2 ∧ (x : Int) % 6 = 2) := by omega
        simp only [hn6_i, h6, ite_false]
        by_cases h8 : x > 2 ∧ x % 8 = 6
        · have h8_i : (x : Int) > 2 ∧ (x : Int) % 8 = 6 := by omega
          simp only [h8_i, h8, and_self, ite_true]; omega
        · have hn8_i : ¬ ((x : Int) > 2 ∧ (x : Int) % 8 = 6) := by omega
          simp only [hn8_i, h8, ite_false]; omega

theorem cousinDiamond3Step_pos (x : Nat) (hx : x > 0) : cousinDiamond3Step x > 0 := by
  unfold cousinDiamond3Step
  by_cases hodd : x % 2 = 1
  · simp only [hodd, ite_true]
    by_cases hq : isDiamond3Cone4 x ∨
        (x > 1 ∧ x % 16 = 1 ∧ x % 3 ≠ 2 ∧ core3 (2 * x + 1) ≠ 1) ∨
        (x ≥ 73 ∧ x % 64 = 9 ∧ x % 3 ≠ 2 ∧ core3 (2 * x + 1) ≠ 1) ∨
        (x ≥ 17 ∧ core3 (x + 1) = 2)
    · simp only [hq, ite_true]
      rcases hq with ⟨_, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _⟩ <;> omega
    · simp only [hq, ite_false]; omega
  · simp only [hodd, ite_false]
    by_cases h18 : x ≥ 20 ∧ x % 18 = 2
    · simp only [h18, and_self, ite_true]; omega
    · simp only [h18, ite_false]
      by_cases h6 : x > 2 ∧ x % 6 = 2
      · simp only [h6, and_self, ite_true]; omega
      · simp only [h6, ite_false]
        by_cases h8 : x > 2 ∧ x % 8 = 6
        · simp only [h8, and_self, ite_true]; omega
        · simp only [h8, ite_false]; omega

/--
  Theorem W6.2e (`cousin_diamond3_outside_cone4_strict_descent`, zero custom axioms):
  Outside Cone 4 (`¬ isDiamond3Cone4 x`), EVERY `x > 2` strictly decreases `cousinDiamond2Phi`
  in a single step of `cousinDiamond3Step`!
-/
theorem cousin_diamond3_outside_cone4_strict_descent
    (x : Nat) (hx : x > 2) (hnc4 : ¬ isDiamond3Cone4 x) :
    cousinDiamond2Phi (cousinDiamond3Step x) < cousinDiamond2Phi x := by
  by_cases hodd : x % 2 = 1
  · by_cases hq3 : isDiamond3Cone4 x ∨
        (x > 1 ∧ x % 16 = 1 ∧ x % 3 ≠ 2 ∧ core3 (2 * x + 1) ≠ 1) ∨
        (x ≥ 73 ∧ x % 64 = 9 ∧ x % 3 ≠ 2 ∧ core3 (2 * x + 1) ≠ 1) ∨
        (x ≥ 17 ∧ core3 (x + 1) = 2)
    · have hq2 : (x > 1 ∧ x % 16 = 1 ∧ x % 3 ≠ 2) ∨
          (x ≥ 73 ∧ x % 64 = 9 ∧ x % 3 ≠ 2) ∨
          (x ≥ 17 ∧ core3 (x + 1) = 2) := by
        rcases hq3 with hc4 | ⟨h1, h2, h3, _⟩ | ⟨h1, h2, h3, _⟩ | hc3
        · exact False.elim (hnc4 hc4)
        · exact Or.inl ⟨h1, h2, h3⟩
        · exact Or.inr (Or.inl ⟨h1, h2, h3⟩)
        · exact Or.inr (Or.inr hc3)
      have hstep_eq : cousinDiamond3Step x = cousinDiamond2Step x := by
        unfold cousinDiamond3Step cousinDiamond2Step
        simp only [hodd, hq3, hq2, ite_true]
      rw [hstep_eq]
      exact cousin_diamond2_phi_strict_descent x hx
    · -- General odd step `(3 * x + 1) / 2` ALWAYS strictly decreases `cousinDiamond2Phi`!
      have hstep : cousinDiamond3Step x = (3 * x + 1) / 2 := by
        unfold cousinDiamond3Step; simp only [hodd, hq3, ite_true, ite_false]
      let m := (x + 1) / 2
      have hm_ge2 : m ≥ 2 := by dsimp [m]; omega
      have hxp1 : x + 1 = 2 * m := by dsimp [m]; omega
      have hyp1 : cousinDiamond3Step x + 1 = 3 * m := by rw [hstep]; dsimp [m]; omega
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
  · by_cases h18 : x ≥ 20 ∧ x % 18 = 2
    · have hstep : cousinDiamond3Step x = (x - 2) / 9 := by
        unfold cousinDiamond3Step; simp only [hodd, h18, and_self, ite_true, ite_false]
      let k := (x - 2) / 18
      have hk_pos : k ≥ 1 := by dsimp [k]; omega
      let g := 6 * k + 1
      have hg_pos : g ≥ 7 := by dsimp [g]; omega
      have hg_odd : g % 2 = 1 := by dsimp [g]; omega
      have hg_nd3 : g % 3 ≠ 0 := by dsimp [g]; omega
      have hxp1 : x + 1 = 3 * g := by dsimp [g, k]; omega
      let y := (x - 2) / 9
      have hyp1 : y + 1 = 2 * k + 1 := by dsimp [y, k]; omega
      have hyp1_odd : (y + 1) % 2 = 1 := by omega
      have hphix : cousinDiamond2Phi x = g ^ 3 + 27 := by
        unfold cousinDiamond2Phi
        rw [hxp1, v2Pow_mul3 g (by omega), v2Pow_of_odd g hg_odd,
            v3Pow_mul3 g (by omega), v3Pow_of_not_div3 g hg_nd3,
            coprime23Core_mul3 g (by omega), coprime23Core_of_coprime g hg_odd hg_nd3]
        simp
      rcases decomp_2_3_exact (y + 1) (by omega) with ⟨_, hby_pos, hgy_pos, _, _, hy_mul⟩
      have hv2_y : v2Pow (y + 1) = 1 := v2Pow_of_odd (y + 1) hyp1_odd
      rw [hv2_y, Nat.one_mul] at hy_mul
      have hphiy_le : cousinDiamond2Phi y ≤ (y + 1) ^ 3 + 1 := by
        unfold cousinDiamond2Phi
        rw [hv2_y]
        simp only [Nat.one_pow, Nat.one_mul]
        have hsc := sum_cubes_le_prod_cube_succ (v3Pow (y + 1)) (coprime23Core (y + 1)) hby_pos hgy_pos
        rw [hy_mul] at hsc; omega
      have hlt_yg : y + 1 < g := by dsimp [g]; omega
      have hcube := pow3_strict_mono_w5 (y + 1) g hlt_yg
      rw [hstep, hphix]
      change cousinDiamond2Phi y < g ^ 3 + 27
      omega
    · have hstep_eq : cousinDiamond3Step x = cousinDiamond2Step x := by
        unfold cousinDiamond3Step cousinDiamond2Step
        simp only [hodd, h18, ite_false]
      rw [hstep_eq]
      exact cousin_diamond2_phi_strict_descent x hx

theorem eq_pow2_of_core2_eq_one_aux :
    ∀ (bound n : Nat), n > 0 -> n ≤ bound -> core2 n = 1 -> ∃ e : Nat, n = 2 ^ e
  | 0, _, hn, hle, _ => by omega
  | b + 1, n, hn, hle, hc2 => by
    by_cases hev : n % 2 = 0
    · let k := n / 2
      have hk_pos : k > 0 := by dsimp [k]; omega
      have hn2 : n = 2 * k := by dsimp [k]; omega
      rw [hn2, core2_mul2 k hk_pos] at hc2
      rcases eq_pow2_of_core2_eq_one_aux b k hk_pos (by dsimp [k]; omega) hc2 with ⟨e, he⟩
      exact ⟨e + 1, by rw [hn2, he, Nat.pow_succ, Nat.mul_comm]⟩
    · have hod := core2_of_odd n (by omega)
      rw [hc2] at hod
      exact ⟨0, hod.symm⟩

theorem eq_pow2_of_core2_eq_one (n : Nat) (hn : n > 0) (hc2 : core2 n = 1) :
    ∃ e : Nat, n = 2 ^ e :=
  eq_pow2_of_core2_eq_one_aux n n hn (Nat.le_refl n) hc2

theorem pow_mod_period_w6 (b P m : Nat) (hm : m ≥ 2) (_hP : P > 0)
    (hper : b ^ P % m = 1) (e : Nat) :
    b ^ e % m = b ^ (e % P) % m := by
  have hdm := (Nat.div_add_mod e P).symm
  conv => lhs; rw [hdm]
  rw [Nat.pow_add, ← pow_pow_eq_mul_w5 b P (e / P), Nat.mul_mod]
  have hp1 : (b ^ P) ^ (e / P) % m = 1 := by
    rw [pow_mod_eq_of_mod_eq_w5 m (b ^ P) 1 (by rw [hper, Nat.mod_eq_of_lt hm]) (e / P),
        Nat.one_pow, Nat.mod_eq_of_lt hm]
  rw [hp1, Nat.one_mul, Nat.mod_mod]

/--
  Exact Exponential Diophantine Exclusion (`pow9_succ_add_seven_ne_pow2`, zero custom axioms):
  For ALL `r ≥ 2` and ALL `M : Nat`, `9 ^ (r + 1) + 7 ≠ 2 ^ M`!
  Proved via coupled congruences `mod 27` (`M % 18 = 16`), `mod 7` (`(r + 1) % 3 = 1`),
  and `mod 19` (`(r + 1) % 9 = 8`).
-/
theorem pow9_succ_add_seven_ne_pow2 (r M : Nat) (hr : r ≥ 2) :
    9 ^ (r + 1) + 7 ≠ 2 ^ M := by
  intro heq
  -- 1. Modulo `27`: `9 ^ (r + 1) = 729 * 9 ^ (r - 2) = 27 * (27 * 9 ^ (r - 2))`:
  have hm27_lhs : (9 ^ (r + 1) + 7) % 27 = 7 := by
    have hs : r + 1 = 3 + (r - 2) := by omega
    rw [hs, Nat.pow_add 9 3 (r - 2), show (9 : Nat) ^ 3 = 27 * 27 from rfl,
        Nat.mul_assoc 27 27, Nat.add_comm _ 7, Nat.add_mul_mod_self_left]
  have hm27_rhs : 2 ^ M % 27 = 2 ^ (M % 18) % 27 :=
    pow_mod_period_w6 2 18 27 (by decide) (by decide) (by decide) M
  have hm27_eq : 2 ^ (M % 18) % 27 = 7 := by rw [← hm27_rhs, ← heq, hm27_lhs]
  have h27_grid : ∀ q : Fin 18, 2 ^ q.val % 27 = 7 -> q.val = 16 := by decide
  have hM18 : M % 18 = 16 := h27_grid ⟨M % 18, Nat.mod_lt M (by decide)⟩ hm27_eq
  have hM3 : M % 3 = 1 := by omega
  -- 2. Modulo `7`:
  have hm7_eq : 9 ^ ((r + 1) % 3) % 7 = 2 := by
    have hl : (9 ^ (r + 1) + 7) % 7 = 9 ^ ((r + 1) % 3) % 7 := by
      rw [show 9 ^ (r + 1) + 7 = 9 ^ (r + 1) + 7 * 1 by omega, Nat.add_mul_mod_self_left]
      exact pow_mod_period_w6 9 3 7 (by decide) (by decide) (by decide) (r + 1)
    have hr7 : 2 ^ M % 7 = 2 := by
      rw [pow_mod_period_w6 2 3 7 (by decide) (by decide) (by decide) M, hM3]
    rw [← hl, heq, hr7]
  have h7_grid : ∀ a : Fin 3, 9 ^ a.val % 7 = 2 -> a.val = 1 := by decide
  have hr3_1 : (r + 1) % 3 = 1 := h7_grid ⟨(r + 1) % 3, Nat.mod_lt _ (by decide)⟩ hm7_eq
  -- 3. Modulo `19`:
  have hm19_eq : (9 ^ ((r + 1) % 9) + 7) % 19 = 5 := by
    have hl : (9 ^ (r + 1) + 7) % 19 = (9 ^ ((r + 1) % 9) + 7) % 19 := by
      rw [Nat.add_mod, pow_mod_period_w6 9 9 19 (by decide) (by decide) (by decide) (r + 1),
          ← Nat.add_mod]
    have hr19 : 2 ^ M % 19 = 5 := by
      rw [pow_mod_period_w6 2 18 19 (by decide) (by decide) (by decide) M, hM18]
    rw [← hl, heq, hr19]
  have h19_grid : ∀ b : Fin 9, (9 ^ b.val + 7) % 19 = 5 -> b.val = 8 := by decide
  have hr9_8 : (r + 1) % 9 = 8 := h19_grid ⟨(r + 1) % 9, Nat.mod_lt _ (by decide)⟩ hm19_eq
  omega

theorem cousinDiamond3Step_mod4_eq_3 (z : Nat) (hz4 : z % 4 = 3) :
    cousinDiamond3Step z = (3 * z + 1) / 2 := by
  have hodd : z % 2 = 1 := by omega
  have hnq : ¬ (isDiamond3Cone4 z ∨
      (z > 1 ∧ z % 16 = 1 ∧ z % 3 ≠ 2 ∧ core3 (2 * z + 1) ≠ 1) ∨
      (z ≥ 73 ∧ z % 64 = 9 ∧ z % 3 ≠ 2 ∧ core3 (2 * z + 1) ≠ 1) ∨
      (z ≥ 17 ∧ core3 (z + 1) = 2)) := by
    rintro (⟨_, h8, _⟩ | ⟨_, h16, _, _⟩ | ⟨_, h64, _, _⟩ | ⟨_, hc3⟩)
    · omega
    · omega
    · omega
    · rcases core3_decomp (z + 1) (by omega) with ⟨_, _, _, hm8, hmul⟩
      rw [hc3] at hmul
      rcases hm8 with h1 | h3 <;> omega
  unfold cousinDiamond3Step
  simp only [hodd, hnq, ite_true, ite_false]

theorem cousin_diamond3_mersenne_scaled :
    ∀ (k a q : Nat), k + 1 ≤ a -> q ≥ 1 ->
      cousinDiamond3Iter k (2 ^ a * q - 1) = 3 ^ k * 2 ^ (a - k) * q - 1
  | 0, _, _, _, _ => by simp [cousinDiamond3Iter]
  | k + 1, a, q, hka, hq => by
    have ha2 : a ≥ 2 := by omega
    have hp4 : 2 ^ a * q = 4 * (2 ^ (a - 2) * q) := by
      have hsp : a = (a - 2) + 2 := by omega
      conv => lhs; rw [hsp]
      rw [Nat.pow_add 2 (a - 2) 2, show (2 : Nat) ^ 2 = 4 from rfl,
          Nat.mul_comm (2 ^ (a - 2)) 4, Nat.mul_assoc]
    have hm_pos : 2 ^ (a - 2) * q ≥ 1 := Nat.mul_le_mul (pow2_pos_nat (a - 2)) hq
    have hz4 : (2 ^ a * q - 1) % 4 = 3 := by omega
    simp only [cousinDiamond3Iter]
    rw [cousinDiamond3Step_mod4_eq_3 (2 ^ a * q - 1) hz4]
    have hp2 : 2 ^ a * q = 2 * (2 ^ (a - 1) * q) := by
      rw [pow2_split_pred a (by omega), Nat.mul_assoc]
    have hstep_eq : (3 * (2 ^ a * q - 1) + 1) / 2 = 2 ^ (a - 1) * (3 * q) - 1 := by
      have hm2_pos : 2 ^ (a - 1) * q ≥ 1 := Nat.mul_le_mul (pow2_pos_nat (a - 1)) hq
      have hcomm : 3 * (2 ^ (a - 1) * q) = 2 ^ (a - 1) * (3 * q) := by
        rw [← Nat.mul_assoc 3, Nat.mul_comm 3 (2 ^ (a - 1)), Nat.mul_assoc]
      omega
    rw [hstep_eq, cousin_diamond3_mersenne_scaled k (a - 1) (3 * q) (by omega) (by omega)]
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

theorem cousinDiamond2Phi_ge_succ (x : Nat) : x + 1 ≤ cousinDiamond2Phi x := by
  rcases decomp_2_3_exact (x + 1) (by omega) with ⟨ha_pos, hb_pos, hg_pos, _, _, hmul⟩
  let a := v2Pow (x + 1)
  let b := v3Pow (x + 1)
  let g := coprime23Core (x + 1)
  change a * b * g = x + 1 at hmul
  unfold cousinDiamond2Phi
  change x + 1 ≤ a * g ^ 3 + a ^ 5 * b ^ 3
  rw [← hmul]
  by_cases hbg : b ≤ g
  · have hg3 : b * g ≤ g ^ 3 := by
      rw [show (3 : Nat) = 2 + 1 from rfl, Nat.pow_succ, show (2 : Nat) = 1 + 1 from rfl,
          Nat.pow_succ, Nat.pow_one]
      have h1 : b * g ≤ g * g := Nat.mul_le_mul_right g hbg
      have h2 : (g * g) * 1 ≤ (g * g) * g := Nat.mul_le_mul_left (g * g) hg_pos
      rw [Nat.mul_one] at h2
      exact Nat.le_trans h1 h2
    have hm := Nat.mul_le_mul_left a hg3
    rw [← Nat.mul_assoc a b g] at hm
    omega
  · have hgb : g ≤ b := by omega
    have hb3 : b * g ≤ b ^ 3 := by
      rw [show (3 : Nat) = 2 + 1 from rfl, Nat.pow_succ, show (2 : Nat) = 1 + 1 from rfl,
          Nat.pow_succ, Nat.pow_one]
      have h1 : b * g ≤ b * b := Nat.mul_le_mul_left b hgb
      have h2 : (b * b) * 1 ≤ (b * b) * b := Nat.mul_le_mul_left (b * b) hb_pos
      rw [Nat.mul_one] at h2
      exact Nat.le_trans h1 h2
    have ha5 : a ≤ a ^ 5 := by
      rw [show (5 : Nat) = 1 + 4 from rfl, Nat.pow_add, Nat.pow_one]
      have hm := Nat.mul_le_mul_left a (nat_pow_pos_of_pos a ha_pos 4)
      simpa using hm
    have hm := Nat.mul_le_mul ha5 hb3
    rw [← Nat.mul_assoc a b g] at hm
    omega

/--
  Theorem W6.2f (`cousin_diamond3_cone4_reaches_one_exact`, zero custom axioms):
  Every `x` in Cone 4 (`isDiamond3Cone4 x`) satisfies `3 * x + 5 = 2 ^ (2 * r + 3)` for an
  exact `r ≥ 3` and reaches `1` in `3 * r + 4 ≤ cousinDiamond2Phi x` steps of `cousinDiamond3Iter`
  (via `x -> 2^(2r+1)-1 ->^{2r} 2*9^r - 1 -> (3*9^r - 1)/2 -> (9^(r+1)-1)/4 ->^r 2 -> 1`),
  even though the first step `x -> 2^(2r+1) - 1` blows up `cousinDiamond2Phi`!
-/
theorem cousin_diamond3_cone4_reaches_one_exact
    (x : Nat) (hc4 : isDiamond3Cone4 x) :
    ∃ r : Nat, r ≥ 3 ∧
      3 * x + 5 = 2 ^ (2 * r + 3) ∧
      cousinDiamond3Iter (3 * r + 4) x = 1 ∧
      3 * r + 4 ≤ cousinDiamond2Phi x := by
  rcases hc4 with ⟨hx_ge, hx_m8, hc2_one⟩
  rcases eq_pow2_of_core2_eq_one (3 * x + 5) (by omega) hc2_one with ⟨E, hE⟩
  have hE_ge9 : E ≥ 9 := by
    by_cases hlt : E < 9
    · have hle8 : 2 ^ E ≤ 2 ^ 8 := pow2_mono_nat (by omega : E ≤ 8)
      rw [← hE, show (2 : Nat) ^ 8 = 256 from rfl] at hle8
      omega
    · omega
  have hE_odd : E % 2 = 1 := by
    by_cases hod : E % 2 = 1
    · exact hod
    · have hev : E = 2 * (E / 2) := by omega
      have hm4 : 4 ^ (E / 2) % 3 = 1 := by
        have hm := (pow4_ge_four_and_mod3_w5 (E / 2 - 1)).2
        rwa [show E / 2 - 1 + 1 = E / 2 by omega] at hm
      have h2E_m3 : 2 ^ E % 3 = 1 := by
        rw [hev, ← pow4_eq_pow2_even (E / 2)]; exact hm4
      rw [← hE] at h2E_m3; omega
  let r := (E - 3) / 2
  have hr_ge3 : r ≥ 3 := by dsimp [r]; omega
  have hE_eq : E = 2 * r + 3 := by dsimp [r]; omega
  rw [hE_eq] at hE
  -- 1. Step 1: `x -> 2 ^ (2 * r + 1) - 1`
  have hx_odd : x % 2 = 1 := by omega
  have hc4_hold : isDiamond3Cone4 x := ⟨hx_ge, hx_m8, hc2_one⟩
  have hstep1 : cousinDiamond3Step x = 2 ^ (2 * r + 1) - 1 := by
    unfold cousinDiamond3Step
    have hcond : isDiamond3Cone4 x ∨
        (x > 1 ∧ x % 16 = 1 ∧ x % 3 ≠ 2 ∧ core3 (2 * x + 1) ≠ 1) ∨
        (x ≥ 73 ∧ x % 64 = 9 ∧ x % 3 ≠ 2 ∧ core3 (2 * x + 1) ≠ 1) ∨
        (x ≥ 17 ∧ core3 (x + 1) = 2) := Or.inl hc4_hold
    simp only [hx_odd, hcond, ite_true]
    have hp4 : 2 ^ (2 * r + 3) = 4 * 2 ^ (2 * r + 1) := by
      rw [show 2 * r + 3 = (2 * r + 1) + 2 by omega, Nat.pow_add,
          show (2 : Nat) ^ 2 = 4 from rfl, Nat.mul_comm]
    have hp_pos := pow2_pos_nat (2 * r + 1)
    omega
  -- 2. Next `2 * r` Mersenne glide steps: `2 ^ (2 * r + 1) - 1 -> 2 * 9 ^ r - 1`
  let zr := 2 * 9 ^ r - 1
  have hglide : cousinDiamond3Iter (2 * r) (2 ^ (2 * r + 1) - 1) = zr := by
    have hf := cousin_diamond3_mersenne_scaled (2 * r) (2 * r + 1) 1 (by omega) (by decide)
    simp only [Nat.mul_one, show 2 * r + 1 - 2 * r = 1 by omega, Nat.pow_one] at hf
    rw [hf, ← pow9_eq_pow3_double r, Nat.mul_comm]
  -- 3. Cone-3 step: `zr = 2 * 9 ^ r - 1 -> yr = (3 * 9 ^ r - 1) / 2`
  let yr := (3 * 9 ^ r - 1) / 2
  have hp9_ge729 : 9 ^ r ≥ 729 := by
    have hm := nat_pow_mono_exp_pos 9 3 r (by decide) hr_ge3
    simpa using hm
  have hp9_m8 : 9 ^ r % 8 = 1 := pow9_mod8_eq_one_w5 r
  have hstep_zr : cousinDiamond3Step zr = yr := by
    have hzr_odd : zr % 2 = 1 := by dsimp [zr]; omega
    have hzr_ge17 : zr ≥ 17 := by dsimp [zr]; omega
    have hc3_zr : core3 (zr + 1) = 2 := by
      have hzrp1 : zr + 1 = 2 * 9 ^ r := by dsimp [zr]; omega
      rw [hzrp1, core3_mul2 (9 ^ r) (by omega), (pow9_eq_v3Pow_w5 r).2]
    have hcond : isDiamond3Cone4 zr ∨
        (zr > 1 ∧ zr % 16 = 1 ∧ zr % 3 ≠ 2 ∧ core3 (2 * zr + 1) ≠ 1) ∨
        (zr ≥ 73 ∧ zr % 64 = 9 ∧ zr % 3 ≠ 2 ∧ core3 (2 * zr + 1) ≠ 1) ∨
        (zr ≥ 17 ∧ core3 (zr + 1) = 2) := Or.inr (Or.inr (Or.inr ⟨hzr_ge17, hc3_zr⟩))
    unfold cousinDiamond3Step
    simp only [hzr_odd, hcond, ite_true]
    dsimp [zr, yr]; omega
  -- 4. General-odd step: `yr = (3 * 9 ^ r - 1) / 2 -> e_{r+1} = (9 ^ (r + 1) - 1) / 4`
  let evenSpine : Nat -> Nat := fun m => (9 ^ m - 1) / 4
  have hstep_yr : cousinDiamond3Step yr = evenSpine (r + 1) := by
    have hyr_odd : yr % 2 = 1 := by dsimp [yr]; omega
    have h2yrp1 : 2 * yr + 1 = 3 * 9 ^ r := by dsimp [yr]; omega
    have hc3_2yr : core3 (2 * yr + 1) = 1 := by
      rw [h2yrp1, core3_mul3 (9 ^ r) (by omega), (pow9_eq_v3Pow_w5 r).2]
    have hc3_yrp1 : core3 (yr + 1) ≠ 2 := by
      have h2_yrp1 : 2 * (yr + 1) = 3 * 9 ^ r + 1 := by dsimp [yr]; omega
      have hnd3 : (yr + 1) % 3 ≠ 0 := by omega
      rw [core3_not_div3 (yr + 1) hnd3]
      dsimp [yr]; omega
    have hnc4_yr : ¬ isDiamond3Cone4 yr := by
      rintro ⟨_, _, hc2_yr⟩
      rcases eq_pow2_of_core2_eq_one (3 * yr + 5) (by dsimp [yr]; omega) hc2_yr with ⟨M0, hM0⟩
      have h9_eq : 9 ^ (r + 1) + 7 = 2 ^ (M0 + 1) := by
        have h2mul : 2 * (3 * yr + 5) = 9 ^ (r + 1) + 7 := by
          rw [Nat.pow_succ 9 r, Nat.mul_comm (9 ^ r) 9]
          dsimp [yr]; omega
        rw [← h2mul, hM0, Nat.pow_succ 2 M0, Nat.mul_comm]
      exact pow9_succ_add_seven_ne_pow2 r (M0 + 1) (by omega) h9_eq
    have hnq : ¬ (isDiamond3Cone4 yr ∨
        (yr > 1 ∧ yr % 16 = 1 ∧ yr % 3 ≠ 2 ∧ core3 (2 * yr + 1) ≠ 1) ∨
        (yr ≥ 73 ∧ yr % 64 = 9 ∧ yr % 3 ≠ 2 ∧ core3 (2 * yr + 1) ≠ 1) ∨
        (yr ≥ 17 ∧ core3 (yr + 1) = 2)) := by
      rintro (hc4_y | ⟨_, _, _, hc1⟩ | ⟨_, _, _, hc2⟩ | ⟨_, hc3⟩)
      · exact hnc4_yr hc4_y
      · exact hc1 hc3_2yr
      · exact hc2 hc3_2yr
      · exact hc3_yrp1 hc3
    unfold cousinDiamond3Step
    simp only [hyr_odd, hnq, ite_true, ite_false]
    dsimp [evenSpine, yr]
    rw [Nat.pow_succ 9 r]
    omega
  -- 5. `r` even `(x - 2) / 9` steps: `evenSpine (r + 1) ->^r evenSpine 1 = 2`
  have heven_step : ∀ j : Nat, j ≥ 1 -> cousinDiamond3Step (evenSpine (j + 1)) = evenSpine j := by
    intro j hj
    have hp9j_ge9 : 9 ^ j ≥ 9 := by
      rw [show j = (j - 1) + 1 by omega, Nat.pow_succ]
      have hp := nat_pow_pos_of_pos 9 (by decide) (j - 1); omega
    have hp9j_m8 : 9 ^ j % 8 = 1 := pow9_mod8_eq_one_w5 j
    let q := (9 ^ j - 1) / 8
    have hq_pos : q ≥ 1 := by dsimp [q]; omega
    have hp9j_eq : 9 ^ j = 8 * q + 1 := by dsimp [q]; omega
    have he_j1 : evenSpine (j + 1) = 18 * q + 2 := by
      dsimp [evenSpine]; rw [Nat.pow_succ 9 j, hp9j_eq]; omega
    have he_j : evenSpine j = 2 * q := by
      dsimp [evenSpine]; rw [hp9j_eq]; omega
    rw [he_j1, he_j]
    have hodd_f : ¬ ((18 * q + 2) % 2 = 1) := by omega
    have h18_t : 18 * q + 2 ≥ 20 ∧ (18 * q + 2) % 18 = 2 := ⟨by omega, by omega⟩
    unfold cousinDiamond3Step
    simp only [hodd_f, h18_t, and_self, ite_true, ite_false]
    omega
  have heven_drain : ∀ k : Nat, cousinDiamond3Iter k (evenSpine (k + 1)) = evenSpine 1 := by
    intro k
    induction k with
    | zero => rfl
    | succ k' ih =>
      simp only [cousinDiamond3Iter]
      rw [heven_step (k' + 1) (by omega), ih]
  -- 6. Assemble all `3 * r + 4` steps and bound `3 * r + 4 ≤ x + 1 ≤ cousinDiamond2Phi x`:
  have htot : cousinDiamond3Iter (3 * r + 4) x = 1 := by
    have hsplit : 3 * r + 4 = 1 + 2 * r + 1 + 1 + r + 1 := by omega
    rw [hsplit,
        cousinDiamond3Iter_add (1 + 2 * r + 1 + 1 + r) 1 x,
        cousinDiamond3Iter_add (1 + 2 * r + 1 + 1) r x,
        cousinDiamond3Iter_add (1 + 2 * r + 1) 1 x,
        cousinDiamond3Iter_add (1 + 2 * r) 1 x,
        cousinDiamond3Iter_add 1 (2 * r) x]
    have hi1 : cousinDiamond3Iter 1 x = 2 ^ (2 * r + 1) - 1 := hstep1
    rw [hi1, hglide]
    have hi_zr : cousinDiamond3Iter 1 zr = yr := hstep_zr
    rw [hi_zr]
    have hi_yr : cousinDiamond3Iter 1 yr = evenSpine (r + 1) := hstep_yr
    rw [hi_yr, heven_drain r]
    decide
  have hphi_ge : 3 * r + 4 ≤ cousinDiamond2Phi x := by
    have h2_ge : 2 ^ (2 * r + 3) ≥ 16 * r + 8 := by
      have hp4 : 2 ^ (2 * r + 3) = 8 * 4 ^ r := by
        rw [show 2 * r + 3 = 3 + 2 * r by omega, Nat.pow_add,
            ← pow4_eq_pow2_even r]
      have h4r : 4 ^ r ≥ 2 * r + 1 := by
        have h1 : 2 ^ (2 * r) ≥ 2 * r + 1 := pow2_ge_succ_self (2 * r)
        rwa [← pow4_eq_pow2_even r] at h1
      rw [hp4]; omega
    rw [← hE] at h2_ge
    have hx1 : 3 * r + 4 ≤ x + 1 := by omega
    exact Nat.le_trans hx1 (cousinDiamond2Phi_ge_succ x)
  exact ⟨r, hr_ge3, hE, htot, hphi_ge⟩

theorem cousin_diamond3_reaches_one_within_phi :
    ∀ (B x : Nat), x > 0 -> cousinDiamond2Phi x ≤ B ->
      ∃ k : Nat, k ≤ B ∧ cousinDiamond3Iter k x = 1
  | 0, x, _, hB => by
    have hge := cousinDiamond2Phi_ge_succ x; omega
  | B + 1, x, hx, hB => by
    by_cases hx1 : x = 1
    · subst hx1; exact ⟨0, by omega, rfl⟩
    · by_cases hx2 : x = 2
      · subst hx2
        have hphi2 : cousinDiamond2Phi 2 = 28 := by decide
        rw [hphi2] at hB
        exact ⟨1, by omega, by decide⟩
      · by_cases hc4 : isDiamond3Cone4 x
        · rcases cousin_diamond3_cone4_reaches_one_exact x hc4 with ⟨r, _, _, hiter1, hle_phi⟩
          exact ⟨3 * r + 4, Nat.le_trans hle_phi hB, hiter1⟩
        · have hdesc := cousin_diamond3_outside_cone4_strict_descent x (by omega) hc4
          have hpos := cousinDiamond3Step_pos x hx
          rcases cousin_diamond3_reaches_one_within_phi B (cousinDiamond3Step x) hpos (by omega) with
            ⟨k, hk_le, hk_eq⟩
          exact ⟨k + 1, by omega, hk_eq⟩

/--
  Theorem W6.2g (`cousin_diamond3_global_convergence`, zero custom axioms):
  Unconditional Global Convergence & Degree-5 Polynomial Stopping Bound for `T_diamond3`:
  For EVERY `x > 0`, `cousinDiamond3Iter` reaches `1` within `k ≤ (x + 1)^3 + (x + 1)^5` steps!
-/
theorem cousin_diamond3_global_convergence (x : Nat) (hx : x > 0) :
    ∃ k : Nat, k ≤ (x + 1) ^ 3 + (x + 1) ^ 5 ∧ cousinDiamond3Iter k x = 1 := by
  rcases cousin_diamond3_reaches_one_within_phi (cousinDiamond2Phi x) x hx (Nat.le_refl _) with
    ⟨k, hk_phi, hk1⟩
  exact ⟨k, Nat.le_trans hk_phi (cousinDiamond2Phi_upper_poly_bound x), hk1⟩

theorem laurentDescProp_trans (terms : List LaurentTerm) (A0 B0 C0 x y w : Nat)
    (hxy : laurentDescProp terms A0 B0 C0 x y)
    (hyw : laurentDescProp terms A0 B0 C0 y w) :
    laurentDescProp terms A0 B0 C0 x w := by
  unfold laurentDescProp at hxy hyw ⊢
  rcases decomp_2_3_exact (x + 1) (by omega) with ⟨hax, hbx, hgx, _, _, _⟩
  rcases decomp_2_3_exact (y + 1) (by omega) with ⟨hay, hby, hgy, _, _, _⟩
  have hDx_pos : laurentValDen A0 B0 C0 x > 0 :=
    Nat.mul_pos (Nat.mul_pos (nat_pow_pos_of_pos _ hax A0) (nat_pow_pos_of_pos _ hbx B0))
      (nat_pow_pos_of_pos _ hgx C0)
  have hDy_pos : laurentValDen A0 B0 C0 y > 0 :=
    Nat.mul_pos (Nat.mul_pos (nat_pow_pos_of_pos _ hay A0) (nat_pow_pos_of_pos _ hby B0))
      (nat_pow_pos_of_pos _ hgy C0)
  apply nat_mul_lt_cancel_right_w5 (laurentValDen A0 B0 C0 y) _ _ hDy_pos
  have hm1 := Nat.mul_lt_mul_of_pos_right hyw hDx_pos
  have hm2 := Nat.mul_le_mul_left (laurentValDen A0 B0 C0 w) (Nat.le_of_lt hxy)
  have hl : (evalLaurentSumNum terms w * laurentValDen A0 B0 C0 x) * laurentValDen A0 B0 C0 y =
      (evalLaurentSumNum terms w * laurentValDen A0 B0 C0 y) * laurentValDen A0 B0 C0 x := by
    rw [Nat.mul_assoc, Nat.mul_comm (laurentValDen A0 B0 C0 x), ← Nat.mul_assoc]
  have hm : (evalLaurentSumNum terms y * laurentValDen A0 B0 C0 w) * laurentValDen A0 B0 C0 x =
      laurentValDen A0 B0 C0 w * (evalLaurentSumNum terms y * laurentValDen A0 B0 C0 x) := by
    rw [Nat.mul_comm (evalLaurentSumNum terms y) (laurentValDen A0 B0 C0 w), Nat.mul_assoc]
  have hr : laurentValDen A0 B0 C0 w * (evalLaurentSumNum terms x * laurentValDen A0 B0 C0 y) =
      (evalLaurentSumNum terms x * laurentValDen A0 B0 C0 w) * laurentValDen A0 B0 C0 y := by
    rw [← Nat.mul_assoc, Nat.mul_comm (laurentValDen A0 B0 C0 w) (evalLaurentSumNum terms x)]
  rw [hl]
  rw [hm] at hm1
  rw [hr] at hm2
  exact Nat.lt_of_lt_of_le hm1 hm2

theorem exists_non_desc_along_diamond3_iter :
    ∀ (terms : List LaurentTerm) (A0 B0 C0 N z : Nat),
      N ≥ 1 ->
      (∀ i : Nat, i < N ->
        cousinDiamond3Iter i z ≥ 3 ∧
        (cousinDiamond3Iter i z) % 2 = 1 ∧
        cousinDiamond3Step (cousinDiamond3Iter i z) ≥ 3) ->
      ¬ laurentDescProp terms A0 B0 C0 z (cousinDiamond3Iter N z) ->
      ∃ x : Nat,
        x ≥ 3 ∧ x % 2 = 1 ∧ cousinDiamond3Step x ≥ 3 ∧
        ¬ laurentDescProp terms A0 B0 C0 x (cousinDiamond3Step x)
  | _, _, _, _, 0, _, hN, _, _ => by omega
  | terms, A0, B0, C0, 1, z, _, hall, hnd => by
    rcases hall 0 (by decide) with ⟨hz3, hzo, hsz3⟩
    exact ⟨z, hz3, hzo, hsz3, hnd⟩
  | terms, A0, B0, C0, m + 2, z, _, hall, hnd => by
    if h0 : laurentDescProp terms A0 B0 C0 z (cousinDiamond3Step z) then
      have hnd_next : ¬ laurentDescProp terms A0 B0 C0 (cousinDiamond3Step z)
          (cousinDiamond3Iter (m + 1) (cousinDiamond3Step z)) :=
        fun hrest => hnd (laurentDescProp_trans terms A0 B0 C0 z (cousinDiamond3Step z) _ h0 hrest)
      exact exists_non_desc_along_diamond3_iter terms A0 B0 C0 (m + 1) (cousinDiamond3Step z)
        (by omega)
        (fun i hi => hall (i + 1) (by omega))
        hnd_next
    else
      rcases hall 0 (by omega) with ⟨hz3, hzo, hsz3⟩
      exact ⟨z, hz3, hzo, hsz3, h0⟩

/--
  Theorem W6.2h (`cousin_diamond3_multiterm_laurent_impossibility`, zero custom axioms):
  Even though `T_diamond3` IS globally convergent on `Z^+` (`W6.2g`), EVERY finite `L`-term
  (`∀ L ≥ 1`) arbitrary-sign `(2, 3)`-adic Laurent valuation sum FAILS strict odd-step descent
  on `cousinDiamond3Step`!
-/
theorem cousin_diamond3_multiterm_laurent_impossibility
    (terms : List LaurentTerm) (A0 B0 C0 : Nat)
    (hnonempty : ∃ t ∈ terms, t.coeff > 0) :
    ∃ x : Nat,
      x ≥ 3 ∧ x % 2 = 1 ∧ cousinDiamond3Step x ≥ 3 ∧
      ¬ (evalLaurentSumNum terms (cousinDiamond3Step x) * laurentValDen A0 B0 C0 x <
          evalLaurentSumNum terms x * laurentValDen A0 B0 C0 (cousinDiamond3Step x)) := by
  rcases three_family_multiterm_laurent_obstruction terms A0 B0 C0 hnonempty with
    h97 | ⟨j2, hj2⟩ | ⟨r, hr_pos, hr3⟩
  · have hs97 : cousinDiamond3Step 97 = 73 := by decide
    refine ⟨97, by decide, by decide, by rw [hs97]; decide, ?_⟩
    rw [hs97]; exact h97
  · let zj := geomSpineEntry j2
    let Mj := 4 ^ (3 * j2 + 3)
    rcases geomSpineEntry_valuations_constant j2 with ⟨h3zj1, hzj_ge, _, _, _, _⟩
    change 3 * zj + 1 = 4 ^ (3 * j2 + 4) at h3zj1
    change zj ≥ 85 at hzj_ge
    have hMj_ge64 : Mj ≥ 64 := by
      dsimp [Mj]; rw [Nat.pow_add 4 (3 * j2) 3]
      have hm := Nat.mul_le_mul_right 64 (nat_pow_pos_of_pos 4 (by decide) (3 * j2))
      simpa using hm
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
    have hstep_xj2 : cousinDiamond3Step xj2 = yj2 := by
      unfold cousinDiamond3Step
      have hcond : isDiamond3Cone4 xj2 ∨
          (xj2 > 1 ∧ xj2 % 16 = 1 ∧ xj2 % 3 ≠ 2 ∧ core3 (2 * xj2 + 1) ≠ 1) ∨
          (xj2 ≥ 73 ∧ xj2 % 64 = 9 ∧ xj2 % 3 ≠ 2 ∧ core3 (2 * xj2 + 1) ≠ 1) ∨
          (xj2 ≥ 17 ∧ core3 (xj2 + 1) = 2) := Or.inl hc4_xj2
      simp only [hxj2_odd, hcond, ite_true]
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
        cousinDiamond3Iter i xr3 = 3 ^ i * 2 ^ (2 * r + 1 - i) - 1 ∧
        cousinDiamond3Iter i xr3 ≥ 7 ∧
        (cousinDiamond3Iter i xr3) % 2 = 1 := by
      intro i hi
      have hf := cousin_diamond3_mersenne_scaled i (2 * r + 1) 1 (by omega) (by decide)
      rw [← hxr3_pow, Nat.mul_one] at hf
      have hp2_pos : 2 ^ (2 * r + 1 - i) ≥ 2 := by
        rw [show 2 * r + 1 - i = 1 + (2 * r - i) by omega, Nat.pow_add, Nat.pow_one]
        have hm := Nat.mul_le_mul_left 2 (pow2_pos_nat (2 * r - i)); omega
      have hprod_ge8 : 3 ^ i * 2 ^ (2 * r + 1 - i) ≥ 8 := by
        have h1 : 2 ^ i * 2 ^ (2 * r + 1 - i) ≤ 3 ^ i * 2 ^ (2 * r + 1 - i) :=
          Nat.mul_le_mul_right _ (pow2_le_pow3 i)
        rw [← Nat.pow_add, show i + (2 * r + 1 - i) = 2 * r + 1 by omega] at h1
        have h2 : 2 ^ 3 ≤ 2 ^ (2 * r + 1) := pow2_mono_nat (by omega)
        exact Nat.le_trans h2 h1
      have hprod_ev : (3 ^ i * 2 ^ (2 * r + 1 - i)) % 2 = 0 := by
        rw [show 2 * r + 1 - i = (2 * r - i) + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc]; omega
      exact ⟨hf, by rw [hf]; omega, by rw [hf]; omega⟩
    have hiter_2r : cousinDiamond3Iter (2 * r) xr3 = zr := by
      have hf := (hglide_i (2 * r) (Nat.le_refl _)).1
      rw [hf, show 2 * r + 1 - 2 * r = 1 by omega, Nat.pow_one,
          ← pow9_eq_pow3_double r, Nat.mul_comm]
    have hstep_zr : cousinDiamond3Step zr = yr3 := by
      have hzr_odd : zr % 2 = 1 := by dsimp [zr]; omega
      have hzr_ge17 : zr ≥ 17 := by dsimp [zr]; omega
      have hc3_zr : core3 (zr + 1) = 2 := by
        have hzrp1 : zr + 1 = 2 * 9 ^ r := by dsimp [zr]; omega
        rw [hzrp1, core3_mul2 (9 ^ r) (by omega), (pow9_eq_v3Pow_w5 r).2]
      have hcond : isDiamond3Cone4 zr ∨
          (zr > 1 ∧ zr % 16 = 1 ∧ zr % 3 ≠ 2 ∧ core3 (2 * zr + 1) ≠ 1) ∨
          (zr ≥ 73 ∧ zr % 64 = 9 ∧ zr % 3 ≠ 2 ∧ core3 (2 * zr + 1) ≠ 1) ∨
          (zr ≥ 17 ∧ core3 (zr + 1) = 2) := Or.inr (Or.inr (Or.inr ⟨hzr_ge17, hc3_zr⟩))
      unfold cousinDiamond3Step
      simp only [hzr_odd, hcond, ite_true]
      dsimp [zr, yr3]; omega
    have hiter_2r1 : cousinDiamond3Iter (2 * r + 1) xr3 = yr3 := by
      rw [cousinDiamond3Iter_add (2 * r) 1 xr3, hiter_2r]
      exact hstep_zr
    have hall : ∀ i : Nat, i < 2 * r + 1 ->
        cousinDiamond3Iter i xr3 ≥ 3 ∧
        (cousinDiamond3Iter i xr3) % 2 = 1 ∧
        cousinDiamond3Step (cousinDiamond3Iter i xr3) ≥ 3 := by
      intro i hi
      by_cases hlt : i < 2 * r
      · rcases hglide_i i (by omega) with ⟨_, hge7, hodd_i⟩
        have hnext : cousinDiamond3Step (cousinDiamond3Iter i xr3) =
            cousinDiamond3Iter (i + 1) xr3 :=
          (cousinDiamond3Iter_add i 1 xr3).symm
        rcases hglide_i (i + 1) (by omega) with ⟨_, hge7_n, _⟩
        exact ⟨by omega, hodd_i, by rw [hnext]; omega⟩
      · have hi_eq : i = 2 * r := by omega
        rw [hi_eq, hiter_2r, hstep_zr]
        exact ⟨by dsimp [zr]; omega, by dsimp [zr]; omega, by dsimp [yr3]; omega⟩
    change ¬ laurentDescProp terms A0 B0 C0 xr3 yr3 at hr3
    rw [← hiter_2r1] at hr3
    exact exists_non_desc_along_diamond3_iter terms A0 B0 C0 (2 * r + 1) xr3 (by omega) hall hr3

/--
  Theorem W6.2i (`cousin_diamond3_counter_model_separation`, `[]` axioms):
  `T_diamond3` rejects ALL three Counter-Models (`M1 = Q_(6)^+` 5-cycle `(1, 7) -> (5, 7) -> (11, 7) -> (20, 7) -> (2, 7) -> (1, 7)`,
  `M2 = Z^-` cycles `-1` and `-5 -> -7 -> -10 -> -5`, and `M3` supercritical `q = 7` 5-cycle
  `5 -> 18 -> 9 -> 32 -> 10 -> 5`), AND at the minimal Cone-4 dyadic jump `169 -> 127`
  defeats Wave 5's `Φ_diamond2` (`1228282 -> 34359738496`) while reaching `1` in `13` steps!
-/
theorem cousin_diamond3_counter_model_separation :
    cousinDiamond3StepInt (-1) = -1 ∧
    cousinDiamond3IterInt 3 (-5) = -5 ∧
    cousinDiamond3IterParam 7 5 5 = 5 ∧
    cousinDiamond3StepQ6 (1, 7) = (5, 7) ∧
    cousinDiamond3IterQ6 5 (1, 7) = (1, 7) ∧
    cousinDiamond3Step 169 = 127 ∧
    cousinDiamond3StepInt 169 = 127 ∧
    cousinDiamond3StepQ6 (169, 1) = (127, 1) ∧
    cousinDiamond2Phi 169 = 1228282 ∧
    cousinDiamond2Phi 127 = 34359738496 ∧
    cousinDiamond3Iter 13 169 = 1 := by
  decide

-- ============================================================================
-- SECTION 3: Front C — Multiplicative Schneider–Laurent Integer Determinants &
--            `m`-Block / 2-Block Multiplicative-Order & Sub-Exponent Locks
-- ============================================================================

def laurentInterpBinom : Nat -> Nat -> Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => laurentInterpBinom n k + laurentInterpBinom n (k + 1)

/--
  Schneider–Laurent 2-logarithm multiplicative integer matrix entry:
    `M[(r, s), (t, u)] = binom(r * W + s * K, t) * 2 ^ (r * u) * 3 ^ (s * u) ∈ Nat`
  (zero `lcm` integration denominators!).
-/
def laurentInterpEntry (W K r s t u : Nat) : Nat :=
  laurentInterpBinom (r * W + s * K) t * 2 ^ (r * u) * 3 ^ (s * u)

/--
  Theorem W6.3a' (`laurent_interp_2x2_5_8_and_3x3_determinant_cert`, `[]` axioms):
  Exact integer Schneider–Laurent determinant non-vanishing (`det ≠ 0`, zero `lcm` denominators)
  at convergents `(W, K) = (5, 8)` (`2^8 - 3^5 = 13`) and `(W, K) = (12, 19)` (`2^19 - 3^12 = 7153`),
  including resonant-row gap extraction `M[(8,0),(1,1)] - M[(0,5),(1,1)] = 40 * 13 = 520`
  and `M[(19,0),(0,1)] - M[(0,12),(0,1)] = 2^19 - 3^12 = 7153`!
-/
theorem laurent_interp_2x2_5_8_and_3x3_determinant_cert :
    -- 1. `2 x 2` integer determinant at `(W, K) = (5, 8)` on rows `{(0,0), (1,1)}` and cols `{(0,0), (1,1)}`:
    laurentInterpEntry 5 8 0 0 0 0 * laurentInterpEntry 5 8 1 1 1 1 ≠
      laurentInterpEntry 5 8 0 0 1 1 * laurentInterpEntry 5 8 1 1 0 0 ∧
    -- 2. Resonant rows `(8, 0)` vs `(0, 5)` collapse at `u = 0` yet split by `40 * (2^8 - 3^5) = 520` at `(t, u) = (1, 1)`:
    laurentInterpEntry 5 8 8 0 1 0 = laurentInterpEntry 5 8 0 5 1 0 ∧
    laurentInterpEntry 5 8 8 0 1 1 - laurentInterpEntry 5 8 0 5 1 1 = 40 * (2 ^ 8 - 3 ^ 5) ∧
    -- 3. Resonant rows `(19, 0)` vs `(0, 12)` at `(W, K) = (12, 19)` split by `2^19 - 3^12 = 7153` at `(t, u) = (0, 1)`:
    laurentInterpEntry 12 19 19 0 0 1 - laurentInterpEntry 12 19 0 12 0 1 = 2 ^ 19 - 3 ^ 12 := by
  decide

theorem laurentInterpBinom_pos : ∀ (n k : Nat), k ≤ n -> laurentInterpBinom n k ≥ 1
  | 0, 0, _ => by decide
  | 0, _ + 1, hle => by omega
  | _ + 1, 0, _ => by simp [laurentInterpBinom]
  | n + 1, k + 1, hle => by
    simp only [laurentInterpBinom]
    have ih := laurentInterpBinom_pos n k (by omega)
    omega

theorem pow_sub_pow_dvd_w6 (A B : Nat) (hBA : B ≤ A) :
    ∀ n : Nat, (A - B) ∣ (A ^ n - B ^ n)
  | 0 => by simp
  | n + 1 => by
    have hBnAn : B ^ n ≤ A ^ n := nat_pow_mono_base B A hBA n
    have hsplit : A ^ (n + 1) - B ^ (n + 1) = A ^ n * (A - B) + B * (A ^ n - B ^ n) := by
      have h1 : B * (A ^ n - B ^ n) + B ^ (n + 1) = A ^ n * B := by
        rw [Nat.pow_succ B n, Nat.mul_comm (B ^ n) B, ← Nat.mul_add B,
            Nat.sub_add_cancel hBnAn, Nat.mul_comm B (A ^ n)]
      have h2 : A ^ n * (A - B) + A ^ n * B = A ^ (n + 1) := by
        rw [← Nat.mul_add (A ^ n), Nat.sub_add_cancel hBA, ← Nat.pow_succ A n]
      omega
    rw [hsplit]
    apply Nat.dvd_add
    · exact ⟨A ^ n, Nat.mul_comm _ _⟩
    · rcases pow_sub_pow_dvd_w6 A B hBA n with ⟨q, hq⟩
      exact ⟨B * q, by rw [hq, ← Nat.mul_assoc, Nat.mul_comm B (A - B), Nat.mul_assoc]⟩

/--
  Theorem W6.3a (`laurent_interp_resonant_row_collapse_and_gap_divisibility`, zero custom axioms):
  Universal Algebraic Structure of Schneider–Laurent Integer Determinants:
  1. Every in-range entry `t ≤ r * W + s * K` is a strictly positive integer (`≥ 1`, zero `lcm`).
  2. At `u = 0` (`U = 1`, pure polynomial columns without exponential powers), resonant rows
     `(m * K, 0)` and `(0, m * W)` are IDENTICAL across all `t : Nat` (forcing `det = 0` if `U = 1`).
  3. Across ALL exponential columns `u ≥ 0` (`U ≥ 2`), whenever `3 ^ W ≤ 2 ^ K`, the cycle-gap
     determinant `(2 ^ K - 3 ^ W)` EXACTLY DIVIDES the resonant-row difference
     `laurentInterpEntry W K (m * K) 0 t u - laurentInterpEntry W K 0 (m * W) t u`!
-/
theorem laurent_interp_resonant_row_collapse_and_gap_divisibility :
    (∀ (W K r s t u : Nat), t ≤ r * W + s * K -> laurentInterpEntry W K r s t u ≥ 1) ∧
    (∀ (W K m t : Nat),
      laurentInterpEntry W K (m * K) 0 t 0 = laurentInterpEntry W K 0 (m * W) t 0) ∧
    (∀ (W K m t u : Nat), 3 ^ W ≤ 2 ^ K ->
      (2 ^ K - 3 ^ W) ∣
        (laurentInterpEntry W K (m * K) 0 t u - laurentInterpEntry W K 0 (m * W) t u)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro W K r s t u hle
    unfold laurentInterpEntry
    exact Nat.mul_le_mul
      (Nat.mul_le_mul (laurentInterpBinom_pos _ t hle) (pow2_pos_nat (r * u)))
      (pow3_pos_nat (s * u))
  · intro W K m t
    unfold laurentInterpEntry
    have harg : m * K * W + 0 * K = 0 * W + m * W * K := by
      simp only [Nat.zero_mul, Nat.add_zero, Nat.zero_add,
                 Nat.mul_assoc m K W, Nat.mul_assoc m W K, Nat.mul_comm K W]
    simp only [harg, Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
  · intro W K m t u hle
    unfold laurentInterpEntry
    have harg : 0 * W + m * W * K = m * K * W + 0 * K := by
      simp only [Nat.zero_mul, Nat.add_zero, Nat.zero_add,
                 Nat.mul_assoc m K W, Nat.mul_assoc m W K, Nat.mul_comm W K]
    rw [harg]
    simp only [Nat.zero_mul, Nat.add_zero, Nat.pow_zero, Nat.mul_one]
    let B0 := laurentInterpBinom (m * K * W) t
    have hp2 : 2 ^ (m * K * u) = (2 ^ K) ^ (m * u) := by
      rw [pow_pow_eq_mul_w5 2 K (m * u), ← Nat.mul_assoc K m u, Nat.mul_comm K m]
    have hp3 : 3 ^ (m * W * u) = (3 ^ W) ^ (m * u) := by
      rw [pow_pow_eq_mul_w5 3 W (m * u), ← Nat.mul_assoc W m u, Nat.mul_comm W m]
    change (2 ^ K - 3 ^ W) ∣ (B0 * 2 ^ (m * K * u) - B0 * 3 ^ (m * W * u))
    rw [hp2, hp3, ← Nat.mul_sub_left_distrib B0]
    rcases pow_sub_pow_dvd_w6 (2 ^ K) (3 ^ W) hle (m * u) with ⟨q, hq⟩
    exact ⟨B0 * q, by rw [hq, ← Nat.mul_assoc, Nat.mul_comm B0 (2 ^ K - 3 ^ W), Nat.mul_assoc]⟩

theorem pow2_stepSum_mod_eq_weightSum_mod_w6 (p : Nat) (hp : p ≥ 2) :
    ∀ (bs : List (Nat × Nat)),
      (∀ b ∈ bs, 2 ^ b.2 % p = 1) ->
      2 ^ (blockStepSum bs) % p = 2 ^ (blockWeightSum bs) % p
  | [], _ => rfl
  | b :: rest, hall => by
    have hb := hall b (List.Mem.head _)
    have ih := pow2_stepSum_mod_eq_weightSum_mod_w6 p hp rest
      (fun x hx => hall x (List.mem_cons_of_mem _ hx))
    simp only [blockStepSum, blockWeightSum]
    rw [Nat.add_assoc b.1 b.2 (blockStepSum rest),
        Nat.pow_add 2 b.1 (b.2 + blockStepSum rest),
        Nat.pow_add 2 b.2 (blockStepSum rest),
        Nat.mul_mod (2 ^ b.1), Nat.mul_mod (2 ^ b.2),
        hb, ih, Nat.one_mul, Nat.mod_mod,
        ← Nat.mul_mod (2 ^ b.1), ← Nat.pow_add 2 b.1]

theorem stepSum_mod2_eq_weightSum_mod2_w6 :
    ∀ (bs : List (Nat × Nat)),
      (∀ b ∈ bs, b.2 % 2 = 0) ->
      blockStepSum bs % 2 = blockWeightSum bs % 2
  | [], _ => rfl
  | b :: rest, hall => by
    have hb := hall b (List.Mem.head _)
    have ih := stepSum_mod2_eq_weightSum_mod2_w6 rest
      (fun x hx => hall x (List.mem_cons_of_mem _ hx))
    simp only [blockStepSum, blockWeightSum]
    omega

theorem mem_imp_exists_natAt_w6 :
    ∀ (xs : List Nat) (x : Nat), x ∈ xs -> ∃ i : Nat, i < xs.length ∧ natAt xs i = x
  | [], _, hm => by cases hm
  | hd :: tl, x, hm => by
    simp only [List.mem_cons] at hm
    rcases hm with rfl | htl
    · exact ⟨0, by simp, rfl⟩
    · rcases mem_imp_exists_natAt_w6 tl x htl with ⟨i, hi, heq⟩
      exact ⟨i + 1, by simp; omega, heq⟩

/--
  Theorem W6.3b (`m_block_antipodal_shared_mersenne_parity_and_mod3_lock`, zero custom axioms):
  Universal `∀ m ≥ 1` Antipodal-Order Parity & Mod-3 Quotient Lock:
  Generalizing `one_block_antipodal_order_divisor_exclusion` (`W5.3c`) to arbitrary block count
  `m = (b0 :: rest).length ≥ 1`: whenever `D := 2^K - 3^W > 0` divides `broxSpiralCarry blocks`
  and an odd integer `p ≥ 3` admitting antipodal exponents `(m1, m2)` (`2^m1 % p = p - 1`,
  `(2^m2 + 3^m2) % p = 0`) divides BOTH `D` and every block Mersenne factor `2 ^ b.2 - 1`
  (`b ∈ blocks`), ALL of the following hold unconditionally:
  1. Every even-run length is even (`∀ b ∈ blocks, b.2 % 2 = 0`);
  2. Both total weight `W` and total step length `K` are even (`W % 2 = 0 ∧ K % 2 = 0`);
  3. All `m` Brox cycle quotients `qs` are divisible by `3` (`3 ∣ natListGcd qs`)!
-/
theorem m_block_antipodal_shared_mersenne_parity_and_mod3_lock
    (b0 : Nat × Nat) (rest : List (Nat × Nat))
    (p m1 m2 : Nat)
    (hp3 : p ≥ 3) (hp_odd : p % 2 = 1)
    (_hm1 : m1 ≥ 1) (_hm2 : m2 ≥ 1)
    (hant1 : 2 ^ m1 % p = p - 1)
    (hant2 : (2 ^ m2 + 3 ^ m2) % p = 0)
    (hblocks_pos : ∀ b ∈ (b0 :: rest), b.1 ≥ 1 ∧ b.2 ≥ 1)
    (hgt : 3 ^ blockWeightSum (b0 :: rest) < 2 ^ blockStepSum (b0 :: rest))
    (hdvd_H0 : (2 ^ blockStepSum (b0 :: rest) - 3 ^ blockWeightSum (b0 :: rest)) ∣
      broxSpiralCarry (b0 :: rest))
    (hp_D : p ∣ (2 ^ blockStepSum (b0 :: rest) - 3 ^ blockWeightSum (b0 :: rest)))
    (hp_mers : ∀ b ∈ (b0 :: rest), p ∣ (2 ^ b.2 - 1)) :
    let blocks := b0 :: rest
    let D := 2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks
    (∀ b ∈ blocks, b.2 % 2 = 0) ∧
    blockWeightSum blocks % 2 = 0 ∧
    blockStepSum blocks % 2 = 0 ∧
    (∃ qs : List Nat,
      qs.length = blocks.length ∧
      (∀ j : Nat, j < blocks.length -> D * natAt qs j = broxSpiralCarry (rotBlocks j blocks)) ∧
      3 ∣ natListGcd qs) := by
  dsimp only
  let blocks := b0 :: rest
  let W := blockWeightSum blocks
  let K := blockStepSum blocks
  let D := 2 ^ K - 3 ^ W
  -- 1. `2 ^ b.2 % p = 1` and `b.2 % 2 = 0` for all `b ∈ blocks`:
  have h2b_mod1 : ∀ b ∈ blocks, 2 ^ b.2 % p = 1 := by
    intro b hb
    rcases hp_mers b hb with ⟨k, hk⟩
    have ha_pos : b.2 ≥ 1 := (hblocks_pos b hb).2
    have hp2a : 2 ^ b.2 ≥ 2 := by simpa using pow2_mono_nat ha_pos
    have hrew : 2 ^ b.2 = 1 + p * k := by omega
    rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have ha_even : ∀ b ∈ blocks, b.2 % 2 = 0 := by
    intro b hb
    have hmod1 := h2b_mod1 b hb
    by_cases hev : b.2 % 2 = 0
    · exact hev
    · have hodd_b : b.2 % 2 = 1 := by omega
      have h1 : ((2 ^ b.2) ^ m1) % p = 1 := by
        rw [pow_mod_eq_of_mod_eq_w5 p (2 ^ b.2) 1
          (by rw [hmod1, Nat.mod_eq_of_lt (by omega)]) m1,
          Nat.one_pow, Nat.mod_eq_of_lt (by omega)]
      have h2 : ((2 ^ m1) ^ b.2) % p = p - 1 :=
        (neg_one_pow_mod_w5 p (2 ^ m1) hp3 hant1 b.2).2 hodd_b
      rw [pow_pow_eq_mul_w5 2 b.2 m1] at h1
      rw [pow_pow_eq_mul_w5 2 m1 b.2, Nat.mul_comm m1 b.2, h1] at h2
      omega
  -- 2. `3 ^ W % p = 2 ^ W % p`, forcing `W % 2 = 0` and `K % 2 = 0`:
  have h2K_2W : 2 ^ K % p = 2 ^ W % p :=
    pow2_stepSum_mod_eq_weightSum_mod_w6 p (by omega) blocks h2b_mod1
  have h2K_3W : 2 ^ K % p = 3 ^ W % p := by
    rcases hp_D with ⟨k, hk⟩
    change 2 ^ K - 3 ^ W = p * k at hk
    have hlt_kw : 3 ^ W < 2 ^ K := hgt
    have hrew : 2 ^ K = 3 ^ W + p * k := by
      generalize 2 ^ K = p2k, 3 ^ W = p3w at hk hlt_kw ⊢
      omega
    rw [hrew, Nat.add_mul_mod_self_left]
  have h3W_2W : 3 ^ W % p = 2 ^ W % p := h2K_3W.symm.trans h2K_2W
  have hW_ev : W % 2 = 0 := by
    by_cases hev : W % 2 = 0
    · exact hev
    · have hW_odd : W % 2 = 1 := by omega
      have hpow_eq : ((3 ^ m2) ^ W) % p = ((2 ^ m2) ^ W) % p := by
        rw [pow_pow_eq_mul_w5 3 m2 W, pow_pow_eq_mul_w5 2 m2 W,
            Nat.mul_comm m2 W, ← pow_pow_eq_mul_w5 3 W m2, ← pow_pow_eq_mul_w5 2 W m2]
        exact pow_mod_eq_of_mod_eq_w5 p (3 ^ W) (2 ^ W) h3W_2W m2
      have hsum0 : ((2 ^ m2) ^ W + (3 ^ m2) ^ W) % p = 0 :=
        (sum_zero_mod_pow_parity_w5 p (2 ^ m2) (3 ^ m2) hp3 hant2 W).2 hW_odd
      rw [Nat.add_mod, hpow_eq, ← Nat.add_mod] at hsum0
      have h2pow : (2 ^ m2) ^ W + (2 ^ m2) ^ W = 2 ^ (m2 * W + 1) := by
        rw [pow_pow_eq_mul_w5 2 m2 W, Nat.pow_succ 2 (m2 * W)]; omega
      rw [h2pow] at hsum0
      exact False.elim (odd_mod_pow2_nonzero_w5 p hp3 hp_odd (m2 * W + 1) hsum0)
  have hK_ev : K % 2 = 0 := by
    have hsk := stepSum_mod2_eq_weightSum_mod2_w6 blocks ha_even
    change K % 2 = W % 2 at hsk
    rw [hsk, hW_ev]
  -- 3. Construct `qs` and deduce `3 ∣ natListGcd qs`:
  rcases (m_block_cycle_induces_brox_quotients b0 rest hblocks_pos hgt).2 hdvd_H0 with
    ⟨qs, hq_len, hqs_eq, _, hmod3⟩
  have hblockAt_mem : ∀ j : Nat, j < blocks.length -> blockAt blocks j ∈ blocks := by
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
  have h3_dvd_qs : 3 ∣ natListGcd qs := by
    apply dvd_natListGcd_of_forall
    intro x hx
    rcases mem_imp_exists_natAt_w6 qs x hx with ⟨i, hi, hxi⟩
    rw [hq_len] at hi
    let m := blocks.length
    change i < m at hi
    have hm_pos : m ≥ 1 := by simp [m, blocks]
    let j := if i = 0 then m - 1 else i - 1
    have hj_lt : j < m := by
      dsimp [j]
      by_cases hi0 : i = 0
      · simp only [hi0, ite_true]; omega
      · simp only [hi0, ite_false]; omega
    have hj_next : (j + 1) % m = i := by
      dsimp [j]
      by_cases hi0 : i = 0
      · simp only [hi0, ite_true, show m - 1 + 1 = m by omega, Nat.mod_self]
      · simp only [hi0, ite_false]
        rw [show i - 1 + 1 = i by omega]
        exact Nat.mod_eq_of_lt hi
    have ha_j_ev : (blockAt blocks j).2 % 2 = 0 := ha_even _ (hblockAt_mem j hj_lt)
    have hq_div3 := (hmod3 j hj_lt).mpr ha_j_ev
    rw [hj_next, hxi] at hq_div3
    exact Nat.dvd_of_mod_eq_zero hq_div3
  exact ⟨ha_even, hW_ev, hK_ev, ⟨qs, hq_len, hqs_eq, h3_dvd_qs⟩⟩

theorem not_div3_dvd_pow3_mul_cancel_w6 (D : Nat) (hnd3 : D % 3 ≠ 0) :
    ∀ (e X : Nat), D ∣ (3 ^ e * X) -> D ∣ X
  | 0, X, hdvd => by simpa using hdvd
  | e + 1, X, hdvd => by
    have hmul : 3 ^ (e + 1) * X = 3 ^ e * (3 * X) := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    rw [hmul] at hdvd
    rcases not_div3_dvd_pow3_mul_cancel_w6 D hnd3 e (3 * X) hdvd with ⟨k, hk⟩
    have hk_m3 : k % 3 = 0 := by
      have hm := congrArg (fun z => z % 3) hk
      rw [Nat.mul_mod D k 3] at hm
      by_cases hD1 : D % 3 = 1
      · rw [hD1, Nat.one_mul, Nat.mod_mod] at hm; omega
      · have hD2 : D % 3 = 2 := by omega
        rw [hD2] at hm; omega
    have hk3 : k = 3 * (k / 3) := by omega
    rw [hk3, ← Nat.mul_assoc D 3 (k / 3), Nat.mul_comm D 3, Nat.mul_assoc 3 D (k / 3)] at hk
    exact ⟨k / 3, by omega⟩

/--
  Theorem W6.3c (`two_block_shared_mersenne_propagation_and_equal_even_exclusion`, zero custom axioms):
  2-Block Single-Mersenne Divisor Propagation, Equal-Even-Run Sub-Exponent Lock, &
  Unconditional Cone Exclusion (`m = 2`):
  Let `w1, a1, w2, a2 ≥ 1` with `W := w1 + w2`, `K := w1 + a1 + w2 + a2`, `3 ^ W < 2 ^ K`,
  and `D := 2 ^ K - 3 ^ W`.
  1. Single-Mersenne Propagation: Whenever `D ∣ broxSpiralCarry [(w1, a1), (w2, a2)]`, for EVERY
     divisor `p ∣ D` (`p ≥ 2`), `p ∣ (2 ^ a1 - 1) ↔ p ∣ (2 ^ a2 - 1)`, and `p ∣ (2 ^ a1 - 1)`
     implies `p ∣ (3 ^ (w1 + w2) - 2 ^ (w1 + w2))`!
  2. Equal-Even-Run Sub-Exponent Lock: When `a1 = a2` and `w2 ≤ w1`,
     `D ∣ broxSpiralCarry [(w1, a1), (w2, a1)]` forces
       `D ∣ ((2 ^ a1 - 1) * (3 ^ (w1 - w2) - 2 ^ (w1 - w2)))`!
  3. Unconditional Infinite Cone Exclusion: Whenever `a1 = a2`, `w2 < w1`, `(w1 + w2) % 2 = 0`,
     and `3 * w1 ≤ 5 * w2`, `D > (2 ^ a1 - 1) * (3 ^ (w1 - w2) - 2 ^ (w1 - w2))`, so
     `¬ (D ∣ broxSpiralCarry [(w1, a1), (w2, a1)])` and NO `x0 : Nat` can satisfy the 2-block
     Collatz cycle equation `D * x0 = affineCarry (spiralBlocksToParity [(w1, a1), (w2, a1)])`!
-/
theorem two_block_shared_mersenne_propagation_and_equal_even_exclusion
    (w1 a1 w2 a2 : Nat)
    (hw1 : w1 ≥ 1) (ha1 : a1 ≥ 1) (hw2 : w2 ≥ 1) (ha2 : a2 ≥ 1)
    (hgt : 3 ^ (w1 + w2) < 2 ^ (w1 + a1 + w2 + a2)) :
    let blocks := [(w1, a1), (w2, a2)]
    let D := 2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)
    ((D ∣ broxSpiralCarry blocks ->
      ∀ p : Nat, p ≥ 2 -> p ∣ D ->
        (p ∣ (2 ^ a1 - 1) ↔ p ∣ (2 ^ a2 - 1)) ∧
        (p ∣ (2 ^ a1 - 1) -> p ∣ (3 ^ (w1 + w2) - 2 ^ (w1 + w2)))) ∧
     (a1 = a2 -> w2 ≤ w1 -> D ∣ broxSpiralCarry blocks ->
        D ∣ ((2 ^ a1 - 1) * (3 ^ (w1 - w2) - 2 ^ (w1 - w2)))) ∧
     (a1 = a2 -> w2 < w1 -> (w1 + w2) % 2 = 0 -> 3 * w1 ≤ 5 * w2 ->
        ¬ (D ∣ broxSpiralCarry blocks) ∧
        ∀ x0 : Nat, D * x0 ≠ affineCarry (spiralBlocksToParity blocks))) := by
  dsimp only
  let blocks := [(w1, a1), (w2, a2)]
  let W := w1 + w2
  let K := w1 + a1 + w2 + a2
  let D := 2 ^ K - 3 ^ W
  have hW_eq : blockWeightSum blocks = W := by simp [blocks, W, blockWeightSum]
  have hK_eq : blockStepSum blocks = K := by simp [blocks, K, blockStepSum]; omega
  have hblocks_pos : ∀ b ∈ blocks, b.1 ≥ 1 ∧ b.2 ≥ 1 := by
    intro b hb
    simp only [blocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact ⟨hw1, ha1⟩
    · exact ⟨hw2, ha2⟩
  have hgt_b : 3 ^ blockWeightSum blocks < 2 ^ blockStepSum blocks := by
    rwa [hW_eq, hK_eq]
  have hH0_eq : broxSpiralCarry blocks =
      3 ^ w2 * (2 ^ a1 - 1) + 2 ^ (a1 + w2) * (2 ^ a2 - 1) := by
    simp [blocks, broxSpiralCarry, blockWeightSum]
  have hH1_eq : broxSpiralCarry (rotBlocks 1 blocks) =
      3 ^ w1 * (2 ^ a2 - 1) + 2 ^ (a2 + w1) * (2 ^ a1 - 1) := by
    simp [blocks, rotBlocks, broxSpiralCarry, blockWeightSum]
  have hD_odd : D % 2 = 1 := by
    have hp2_ev : (2 ^ K) % 2 = 0 := by
      rw [show K = (K - 1) + 1 by dsimp [K]; omega, Nat.pow_succ]; omega
    have hp3_odd : (3 ^ W) % 2 = 1 := pow3_odd_nat_sec8 W
    have hlt_kw : 3 ^ W < 2 ^ K := hgt
    dsimp [D]
    generalize 2 ^ K = p2k, 3 ^ W = p3w at hp2_ev hp3_odd hlt_kw
    omega
  have hD_nd3 : D % 3 ≠ 0 := by
    have hp3_0 : (3 ^ W) % 3 = 0 := by
      rw [show W = (W - 1) + 1 by dsimp [W]; omega, Nat.pow_succ]; omega
    have hp2_n0 : (2 ^ K) % 3 ≠ 0 := pow2_mod3_nonzero_w5 K
    have hlt_kw : 3 ^ W < 2 ^ K := hgt
    dsimp [D]
    generalize 2 ^ K = p2k, 3 ^ W = p3w at hp3_0 hp2_n0 hlt_kw
    omega
  have hdvd_H1_of_H0 : D ∣ broxSpiralCarry blocks -> D ∣ broxSpiralCarry (rotBlocks 1 blocks) := by
    intro hdvd0
    have hdvd0' : (2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks) ∣ broxSpiralCarry blocks := by
      rwa [hK_eq, hW_eq]
    rcases (m_block_cycle_induces_brox_quotients (w1, a1) [(w2, a2)] hblocks_pos hgt_b).2 hdvd0' with
      ⟨qs, _, hqs_eq, _, _⟩
    have h1 := hqs_eq 1 (by simp)
    rw [hK_eq, hW_eq] at h1
    exact ⟨natAt qs 1, h1.symm⟩
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: Single-Mersenne propagation across `m = 2`
    intro hdvd0 p _ hp_D
    have hp_odd : p % 2 = 1 := by
      rcases hp_D with ⟨q, hq⟩
      change D = p * q at hq
      have hm := congrArg (fun z => z % 2) hq
      rw [hD_odd, Nat.mul_mod] at hm
      by_cases hp0 : p % 2 = 0
      · rw [hp0, Nat.zero_mul] at hm; simp at hm
      · omega
    have hp_H0 : p ∣ broxSpiralCarry blocks := Nat.dvd_trans hp_D hdvd0
    have hp_H1 : p ∣ broxSpiralCarry (rotBlocks 1 blocks) :=
      Nat.dvd_trans hp_D (hdvd_H1_of_H0 hdvd0)
    have hiff : p ∣ (2 ^ a1 - 1) ↔ p ∣ (2 ^ a2 - 1) := by
      constructor
      · intro hp_a1
        have hsub : 2 ^ (a1 + w2) * (2 ^ a2 - 1) =
            broxSpiralCarry blocks - 3 ^ w2 * (2 ^ a1 - 1) := by rw [hH0_eq]; omega
        have hp_3a1 : p ∣ (3 ^ w2 * (2 ^ a1 - 1)) := by
          rcases hp_a1 with ⟨k, hk⟩
          exact ⟨3 ^ w2 * k, by rw [hk, ← Nat.mul_assoc, Nat.mul_comm (3 ^ w2) p, Nat.mul_assoc]⟩
        have hp_prod : p ∣ (2 ^ (a1 + w2) * (2 ^ a2 - 1)) := by
          rw [hsub]; exact Nat.dvd_sub hp_H0 hp_3a1
        exact odd_dvd_pow2_mul_cancel_w5 p hp_odd (a1 + w2) (2 ^ a2 - 1) hp_prod
      · intro hp_a2
        have hsub : 2 ^ (a2 + w1) * (2 ^ a1 - 1) =
            broxSpiralCarry (rotBlocks 1 blocks) - 3 ^ w1 * (2 ^ a2 - 1) := by rw [hH1_eq]; omega
        have hp_3a2 : p ∣ (3 ^ w1 * (2 ^ a2 - 1)) := by
          rcases hp_a2 with ⟨k, hk⟩
          exact ⟨3 ^ w1 * k, by rw [hk, ← Nat.mul_assoc, Nat.mul_comm (3 ^ w1) p, Nat.mul_assoc]⟩
        have hp_prod : p ∣ (2 ^ (a2 + w1) * (2 ^ a1 - 1)) := by
          rw [hsub]; exact Nat.dvd_sub hp_H1 hp_3a2
        exact odd_dvd_pow2_mul_cancel_w5 p hp_odd (a2 + w1) (2 ^ a1 - 1) hp_prod
    refine ⟨hiff, ?_⟩
    intro hp_a1
    have hp_a2 := hiff.mp hp_a1
    have hp_a12 : p ∣ (2 ^ (a1 + a2) - 1) := by
      have hp2_a1 : 2 ^ a1 ≥ 1 := pow2_pos_nat a1
      have hp2_a2 : 2 ^ a2 ≥ 1 := pow2_pos_nat a2
      have hid : 2 ^ (a1 + a2) - 1 = 2 ^ a2 * (2 ^ a1 - 1) + (2 ^ a2 - 1) := by
        rw [Nat.pow_add 2 a1 a2, Nat.mul_comm (2 ^ a1) (2 ^ a2)]
        have hm : 2 ^ a2 * (2 ^ a1 - 1) + 2 ^ a2 = 2 ^ a2 * 2 ^ a1 := by
          conv => lhs; rhs; rw [← Nat.mul_one (2 ^ a2)]
          rw [← Nat.mul_add, Nat.sub_add_cancel hp2_a1]
        omega
      rw [hid]
      apply Nat.dvd_add
      · rcases hp_a1 with ⟨k, hk⟩
        exact ⟨2 ^ a2 * k, by rw [hk, ← Nat.mul_assoc, Nat.mul_comm (2 ^ a2) p, Nat.mul_assoc]⟩
      · exact hp_a2
    have h2K_sub_2W : 2 ^ K - 2 ^ W = 2 ^ W * (2 ^ (a1 + a2) - 1) := by
      have hKW : K = W + (a1 + a2) := by dsimp [K, W]; omega
      have hp2_a12 : 2 ^ (a1 + a2) ≥ 1 := pow2_pos_nat (a1 + a2)
      rw [hKW, Nat.pow_add 2 W (a1 + a2)]
      have hm : 2 ^ W * (2 ^ (a1 + a2) - 1) + 2 ^ W = 2 ^ W * 2 ^ (a1 + a2) := by
        conv => lhs; rhs; rw [← Nat.mul_one (2 ^ W)]
        rw [← Nat.mul_add, Nat.sub_add_cancel hp2_a12]
      omega
    have hp_2K2W : p ∣ (2 ^ K - 2 ^ W) := by
      rw [h2K_sub_2W]
      rcases hp_a12 with ⟨k, hk⟩
      exact ⟨2 ^ W * k, by rw [hk, ← Nat.mul_assoc, Nat.mul_comm (2 ^ W) p, Nat.mul_assoc]⟩
    have h3W2W_eq : 3 ^ W - 2 ^ W = (2 ^ K - 2 ^ W) - D := by
      have h2le3 : 2 ^ W ≤ 3 ^ W := pow2_le_pow3 W
      have hlt_kw : 3 ^ W < 2 ^ K := hgt
      dsimp [D]; omega
    rw [h3W2W_eq]
    exact Nat.dvd_sub hp_2K2W hp_D
  · -- Part 2: Equal-even-run sub-exponent lock (`a1 = a2`, `w2 ≤ w1`)
    intro ha_eq hw_le hdvd0
    have hdvd1 := hdvd_H1_of_H0 hdvd0
    let d := w1 - w2
    have hw1_eq : w1 = w2 + d := by dsimp [d]; omega
    have h2le3_d : 2 ^ d ≤ 3 ^ d := pow2_le_pow3 d
    have hp2_a1 : 2 ^ a1 ≥ 2 := by simpa using pow2_mono_nat ha1
    have hlin : broxSpiralCarry (rotBlocks 1 blocks) =
        2 ^ d * broxSpiralCarry blocks + 3 ^ w2 * ((2 ^ a1 - 1) * (3 ^ d - 2 ^ d)) := by
      rw [hH0_eq, hH1_eq, ← ha_eq]
      have hf0 : 3 ^ w2 * (2 ^ a1 - 1) + 2 ^ (a1 + w2) * (2 ^ a1 - 1) =
          (3 ^ w2 + 2 ^ (a1 + w2)) * (2 ^ a1 - 1) := (Nat.add_mul _ _ _).symm
      have hf1 : 3 ^ w1 * (2 ^ a1 - 1) + 2 ^ (a1 + w1) * (2 ^ a1 - 1) =
          (3 ^ w1 + 2 ^ (a1 + w1)) * (2 ^ a1 - 1) := (Nat.add_mul _ _ _).symm
      rw [hf0, hf1]
      have hsum_coeff : 3 ^ w1 + 2 ^ (a1 + w1) =
          2 ^ d * (3 ^ w2 + 2 ^ (a1 + w2)) + 3 ^ w2 * (3 ^ d - 2 ^ d) := by
        rw [hw1_eq, Nat.pow_add 3 w2 d,
            show a1 + (w2 + d) = d + (a1 + w2) by omega,
            Nat.pow_add 2 d (a1 + w2), Nat.mul_add (2 ^ d)]
        have h3sub : 2 ^ d * 3 ^ w2 + 3 ^ w2 * (3 ^ d - 2 ^ d) = 3 ^ w2 * 3 ^ d := by
          rw [Nat.mul_comm (2 ^ d) (3 ^ w2), ← Nat.mul_add (3 ^ w2),
              Nat.add_comm (2 ^ d), Nat.sub_add_cancel h2le3_d]
        omega
      rw [hsum_coeff, Nat.add_mul, Nat.mul_assoc (2 ^ d),
          Nat.mul_assoc (3 ^ w2), Nat.mul_comm (3 ^ d - 2 ^ d) (2 ^ a1 - 1)]
    have hdvd_3w2 : D ∣ (3 ^ w2 * ((2 ^ a1 - 1) * (3 ^ d - 2 ^ d))) := by
      have hsub : 3 ^ w2 * ((2 ^ a1 - 1) * (3 ^ d - 2 ^ d)) =
          broxSpiralCarry (rotBlocks 1 blocks) - 2 ^ d * broxSpiralCarry blocks := by omega
      rw [hsub]
      apply Nat.dvd_sub hdvd1
      rcases hdvd0 with ⟨q0, hq0⟩
      exact ⟨2 ^ d * q0, by rw [hq0, ← Nat.mul_assoc, Nat.mul_comm (2 ^ d) D, Nat.mul_assoc]⟩
    exact not_div3_dvd_pow3_mul_cancel_w6 D hD_nd3 w2 _ hdvd_3w2
  · -- Part 3: Unconditional infinite cone exclusion (`a1 = a2`, `w2 < w1`, `W % 2 = 0`, `3*w1 ≤ 5*w2`)
    intro ha_eq hw_lt hW_ev hcone
    have hnot_dvd : ¬ (D ∣ broxSpiralCarry blocks) := by
      intro hdvd0
      -- Re-use Part 2 to get `D ∣ (2 ^ a1 - 1) * (3 ^ d - 2 ^ d)`:
      let d := w1 - w2
      have hd_pos : d ≥ 1 := by dsimp [d]; omega
      have h2le3_d : 2 ^ d ≤ 3 ^ d := pow2_le_pow3 d
      have hp2_a1 : 2 ^ a1 ≥ 2 := by simpa using pow2_mono_nat ha1
      -- Derive `D ∣ R` via same sub-exponent lock:
      have hdvd1 := hdvd_H1_of_H0 hdvd0
      have hw1_eq : w1 = w2 + d := by dsimp [d]; omega
      have hlin : broxSpiralCarry (rotBlocks 1 blocks) =
          2 ^ d * broxSpiralCarry blocks + 3 ^ w2 * ((2 ^ a1 - 1) * (3 ^ d - 2 ^ d)) := by
        rw [hH0_eq, hH1_eq, ← ha_eq]
        have hf0 : 3 ^ w2 * (2 ^ a1 - 1) + 2 ^ (a1 + w2) * (2 ^ a1 - 1) =
            (3 ^ w2 + 2 ^ (a1 + w2)) * (2 ^ a1 - 1) := (Nat.add_mul _ _ _).symm
        have hf1 : 3 ^ w1 * (2 ^ a1 - 1) + 2 ^ (a1 + w1) * (2 ^ a1 - 1) =
            (3 ^ w1 + 2 ^ (a1 + w1)) * (2 ^ a1 - 1) := (Nat.add_mul _ _ _).symm
        rw [hf0, hf1]
        have hsum_coeff : 3 ^ w1 + 2 ^ (a1 + w1) =
            2 ^ d * (3 ^ w2 + 2 ^ (a1 + w2)) + 3 ^ w2 * (3 ^ d - 2 ^ d) := by
          rw [hw1_eq, Nat.pow_add 3 w2 d,
              show a1 + (w2 + d) = d + (a1 + w2) by omega,
              Nat.pow_add 2 d (a1 + w2), Nat.mul_add (2 ^ d)]
          have h3sub : 2 ^ d * 3 ^ w2 + 3 ^ w2 * (3 ^ d - 2 ^ d) = 3 ^ w2 * 3 ^ d := by
            rw [Nat.mul_comm (2 ^ d) (3 ^ w2), ← Nat.mul_add (3 ^ w2),
                Nat.add_comm (2 ^ d), Nat.sub_add_cancel h2le3_d]
          omega
        rw [hsum_coeff, Nat.add_mul, Nat.mul_assoc (2 ^ d),
            Nat.mul_assoc (3 ^ w2), Nat.mul_comm (3 ^ d - 2 ^ d) (2 ^ a1 - 1)]
      have hdvd_3w2 : D ∣ (3 ^ w2 * ((2 ^ a1 - 1) * (3 ^ d - 2 ^ d))) := by
        have hsub : 3 ^ w2 * ((2 ^ a1 - 1) * (3 ^ d - 2 ^ d)) =
            broxSpiralCarry (rotBlocks 1 blocks) - 2 ^ d * broxSpiralCarry blocks := by omega
        rw [hsub]
        apply Nat.dvd_sub hdvd1
        rcases hdvd0 with ⟨q0, hq0⟩
        exact ⟨2 ^ d * q0, by rw [hq0, ← Nat.mul_assoc, Nat.mul_comm (2 ^ d) D, Nat.mul_assoc]⟩
      have hdvd_R := not_div3_dvd_pow3_mul_cancel_w6 D hD_nd3 w2 _ hdvd_3w2
      -- Prove `1 ≤ R < D` via difference of squares `D = (2^(V+a1) - 3^V) * (2^(V+a1) + 3^V)`:
      let V := W / 2
      have hW_2V : W = V + V := by dsimp [V, W] at hW_ev ⊢; omega
      have hK_2Va : K = (V + a1) + (V + a1) := by dsimp [K, W, V] at hW_ev ⊢; omega
      let A := 2 ^ (V + a1)
      let B := 3 ^ V
      have hAA : A * A = 2 ^ K := by dsimp [A]; rw [← Nat.pow_add, ← hK_2Va]
      have hBB : B * B = 3 ^ W := by dsimp [B]; rw [← Nat.pow_add, ← hW_2V]
      have hB_lt_A : B < A := by
        by_cases h : B < A
        · exact h
        · have hm : A * A ≤ B * B := Nat.mul_le_mul (by omega) (by omega)
          rw [hAA, hBB] at hm; omega
      have hD_fac : D = (A - B) * (A + B) := by
        dsimp [D]; rw [← hAA, ← hBB]
        exact diff_of_squares_nat A B (Nat.le_of_lt hB_lt_A)
      have hD_gt_A : A < D := by
        have hB_pos : B ≥ 1 := pow3_pos_nat V
        have hm := Nat.mul_le_mul (by omega : 1 ≤ A - B) (Nat.le_refl (A + B))
        rw [Nat.one_mul, ← hD_fac] at hm
        omega
      have h2d_le_V : 2 * d ≤ V := by dsimp [d, V, W]; omega
      have h3d_le_2V : 3 ^ d ≤ 2 ^ V := by
        have h1 : 3 ^ d ≤ 4 ^ d := nat_pow_mono_base 3 4 (by decide) d
        have h2 : 4 ^ d = 2 ^ (2 * d) := pow4_eq_pow2_even d
        rw [h2] at h1
        exact Nat.le_trans h1 (pow2_mono_nat h2d_le_V)
      have hA_eq : A = 2 ^ a1 * 2 ^ V := by
        dsimp [A]; rw [Nat.add_comm V a1, Nat.pow_add]
      have h3d_gt_2d : 3 ^ d - 2 ^ d ≥ 1 := by
        have hg := pow3_gt_pow2_pos d hd_pos; omega
      let R := (2 ^ a1 - 1) * (3 ^ d - 2 ^ d)
      have hR_pos : R ≥ 1 := Nat.mul_le_mul (by omega : 1 ≤ 2 ^ a1 - 1) h3d_gt_2d
      have hR_lt_A : R < A := by
        dsimp [R]; rw [hA_eq]
        have hlt1 : 2 ^ a1 - 1 < 2 ^ a1 := by omega
        have hlt2 : 3 ^ d - 2 ^ d ≤ 2 ^ V := by
          have hp2d := pow2_pos_nat d; omega
        have hm1 : (2 ^ a1 - 1) * (3 ^ d - 2 ^ d) ≤ (2 ^ a1 - 1) * 2 ^ V :=
          Nat.mul_le_mul_left _ hlt2
        have hm2 : (2 ^ a1 - 1) * 2 ^ V < 2 ^ a1 * 2 ^ V :=
          Nat.mul_lt_mul_of_pos_right hlt1 (pow2_pos_nat V)
        omega
      have hR_lt_D : R < D := Nat.lt_trans hR_lt_A hD_gt_A
      rcases hdvd_R with ⟨k, hk⟩
      change R = D * k at hk
      cases k with
      | zero => rw [Nat.mul_zero] at hk; omega
      | succ k' =>
        have hm := Nat.mul_le_mul_left D (by omega : 1 ≤ k' + 1)
        rw [Nat.mul_one, ← hk] at hm
        omega
    refine ⟨hnot_dvd, ?_⟩
    intro x0 hcyc
    have hcyc' : (2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks) * x0 =
        affineCarry (spiralBlocksToParity blocks) := by
      rwa [hK_eq, hW_eq]
    have hdvd0' := (m_block_cycle_induces_brox_quotients (w1, a1) [(w2, a2)] hblocks_pos hgt_b).1
      x0 hcyc'
    rw [hK_eq, hW_eq] at hdvd0'
    exact hnot_dvd hdvd0'

-- ============================================================================
-- SECTION 4: Front D — Cross-Ray Disjointness, `11 + 16 = 27` Prefix Partition
--            & Uniform Free-Bit Fibers, & Bounded-Length Sparsity / Non-Covering
-- ============================================================================

/--
  Theorem W6.4a (`first_hit_ray_global_disjointness_and_q0_necessity`, zero custom axioms):
  1. Global Cross-Ray Disjointness on `IsFirstHitOnePair`: ANY two first-hit pairs `(u1, q1)`
     and `(u2, q2)` with `exactBackwardQuotient 1 u1 q1 = exactBackwardQuotient 1 u2 q2` satisfy
     `u1 = u2 ∧ q1 = q2`!
  2. Automatic `q ≥ 1` Cross-Ray Disjointness: For ALL core words `u1, u2` with
     `parityWeight u1 ≥ 2, parityWeight u2 ≥ 2` and ALL `q1 ≥ 1, q2 ≥ 1`,
     `exactBackwardQuotient 1 u1 q1 = exactBackwardQuotient 1 u2 q2 -> u1 = u2 ∧ q1 = q2`!
  3. Sharpness of `IsFirstHitOnePair` at `q = 0` inside `IsSurvivingMod373248Class`:
     `uBase = [true, true, true, true, false, true, false, true]` and
     `uLoop = uBase ++ List.replicate 19 false ++ [true]` (`uBase ≠ uLoop`) BOTH map `(·, 0)`
     to the surviving residue `184111 ∈ IsSurvivingMod373248Class` because `uLoop` wraps once
     around the trivial `{1, 2}` loop (`¬ IsFirstHitOnePair uLoop 0`)!
-/
theorem first_hit_ray_global_disjointness_and_q0_necessity :
    (∀ (u1 u2 : List Bool) (q1 q2 : Nat),
      IsFirstHitOnePair u1 q1 -> IsFirstHitOnePair u2 q2 ->
      exactBackwardQuotient 1 u1 q1 = exactBackwardQuotient 1 u2 q2 ->
      u1 = u2 ∧ q1 = q2) ∧
    (∀ (u1 u2 : List Bool) (q1 q2 : Nat),
      IsCoreParityWord u1 -> IsCoreParityWord u2 ->
      parityWeight u1 ≥ 2 -> parityWeight u2 ≥ 2 ->
      q1 ≥ 1 -> q2 ≥ 1 ->
      exactBackwardQuotient 1 u1 q1 = exactBackwardQuotient 1 u2 q2 ->
      u1 = u2 ∧ q1 = q2) ∧
    (let uBase := [true, true, true, true, false, true, false, true]
     let uLoop := uBase ++ List.replicate 19 false ++ [true]
     IsCoreParityWord uBase ∧
     IsCoreParityWord uLoop ∧
     uBase ≠ uLoop ∧
     exactBackwardQuotient 1 uBase 0 = 184111 ∧
     exactBackwardQuotient 1 uLoop 0 = 184111 ∧
     IsSurvivingMod373248Class 184111 ∧
     IsFirstHitOnePair uBase 0 ∧
     ¬ IsFirstHitOnePair uLoop 0) := by
  have hinj : ∀ (u1 u2 : List Bool) (q1 q2 : Nat),
      IsFirstHitOnePair u1 q1 -> IsFirstHitOnePair u2 q2 ->
      exactBackwardQuotient 1 u1 q1 = exactBackwardQuotient 1 u2 q2 ->
      u1 = u2 ∧ q1 = q2 := by
    intro u1 u2 q1 q2 hfh1 hfh2 heq
    let y := exactBackwardQuotient 1 u1 q1
    rcases one_generator_pos_odd_and_reaches_one u1 q1 hfh1.1 with ⟨hy_pos, hy_odd, _, hiter1⟩
    change y ≥ 1 at hy_pos
    change y % 2 = 1 at hy_odd
    change collatzIter (backwardOneTotalSteps u1 q1) y = 1 at hiter1
    have hu1_len : u1.length ≥ 1 := by
      cases u1 with
      | nil => have hh := hfh1.1.1; simp at hh
      | cons _ _ => simp
    have hsteps_pos : backwardOneTotalSteps u1 q1 ≥ 1 := by
      unfold backwardOneTotalSteps; omega
    have hy_ne1 : y ≠ 1 := hfh1.2 0 hsteps_pos
    have hy_gt1 : y > 1 := by omega
    rcases (convergent_odd_gt1_iff_unique_first_hit_pair y).mp ⟨hy_gt1, hy_odd, ⟨_, hiter1⟩⟩ with
      ⟨u0, q0, _, _, huniq⟩
    rcases huniq u1 q1 hfh1 rfl with ⟨hu1_eq, hq1_eq⟩
    rcases huniq u2 q2 hfh2 heq.symm with ⟨hu2_eq, hq2_eq⟩
    exact ⟨hu1_eq.trans hu2_eq.symm, hq1_eq.trans hq2_eq.symm⟩
  refine ⟨hinj, ?_, ?_⟩
  · intro u1 u2 q1 q2 hu1 hu2 hw1 hw2 hq1 hq2 heq
    exact hinj u1 u2 q1 q2
      (one_generator_q_pos_always_first_hit u1 q1 hu1 hw1 hq1)
      (one_generator_q_pos_always_first_hit u2 q2 hu2 hw2 hq2)
      heq
  · dsimp only
    let uBase := [true, true, true, true, false, true, false, true]
    let uLoop := uBase ++ List.replicate 19 false ++ [true]
    rcases mod373248_min_weight_six_witness_184111 with ⟨_, hq_base, _, _, _, hs_184, hfh_base⟩
    have hcore_base : IsCoreParityWord uBase := hfh_base.1
    have hcore_loop : IsCoreParityWord uLoop := ⟨rfl, rfl⟩
    have hne_u : uBase ≠ uLoop := by decide
    have hq_loop : exactBackwardQuotient 1 uLoop 0 = 184111 := by decide
    have hn_fh_loop : ¬ IsFirstHitOnePair uLoop 0 := by
      intro hfh_loop
      have heq_u := (hinj uBase uLoop 0 0 hfh_base hfh_loop (hq_base.trans hq_loop.symm)).1
      exact hne_u heq_u
    exact ⟨hcore_base, hcore_loop, hne_u, hq_base, hq_loop, hs_184, hfh_base, hn_fh_loop⟩

def decodeLsbBits : Nat -> Nat -> List Bool
  | 0, _ => []
  | k + 1, mask => (mask % 2 == 1) :: decodeLsbBits k (mask / 2)

def coreWordLen8 (m : Nat) : List Bool :=
  [true, true] ++ decodeLsbBits 5 m ++ [true]

def coreWordLen9 (m : Nat) : List Bool :=
  [true, true] ++ decodeLsbBits 6 m ++ [true]

/-- Quadratic Hensel inverse modulo `512` (`2^9`) lifted from `invMod64Odd` (`2^6 -> 2^12`). -/
def invMod512Odd (d : Nat) : Nat :=
  let r := d % 512
  let i64 := invMod64Odd r
  (i64 * (514 - (r * i64) % 512)) % 512

/--
  Fast `O(|u|)` dyadic `mod 512` residue of `exactBackwardQuotient 1 u q` for any `w(u) ≥ 6`
  core word (`2^L ≡ 0 mod 512` since `L ≥ 10`):
    `coreWordMod512 u := ((512 - affineCarry u % 512) * invMod512Odd (3 ^ parityWeight u)) % 512`.
-/
def coreWordMod512 (u : List Bool) : Nat :=
  ((512 - affineCarry u % 512) * invMod512Odd (3 ^ parityWeight u)) % 512

def countFinBool : Nat -> (Nat -> Bool) -> Nat
  | 0, _ => 0
  | k + 1, p => (if p k then 1 else 0) + countFinBool k p

/--
  Theorem W6.4b' (`mod512_surviving_prefix_partition_cert`, choice-free, zero custom axioms):
  Exact `11 + 16 = 27` Surviving `mod 512` Core-Prefix Partition (zero large exponents):
  - `invMod512Odd` is verified across all `256` odd `mod 512` residues (`Fin 16 × Fin 16`);
  - Among the `32` core words `true :: true :: b2..b6 :: [true]` of length `8` (`w ≥ 6`),
    EXACTLY `11` land in `isSurvivingMod512Bool` via `coreWordMod512`;
  - Among the `64` core words `true :: true :: b2..b7 :: [true]` of length `9` (`w ≥ 6`),
    EXACTLY `16` land in `isSurvivingMod512Bool` via `coreWordMod512`;
  - The `11` length-`8` surviving classes and `16` length-`9` surviving classes are
    COMPLETELY DISJOINT and partition all `27` surviving `mod 512` classes (`11 + 16 = 27`)!
-/
theorem mod512_surviving_prefix_partition_cert :
    (∀ (a : Fin 16) (b : Fin 16),
      let d := 2 * (16 * a.val + b.val) + 1
      (d * invMod512Odd d) % 512 = 1) ∧
    countFinBool 32 (fun m =>
      decide (parityWeight (coreWordLen8 m) ≥ 6) &&
        isSurvivingMod512Bool (coreWordMod512 (coreWordLen8 m))) = 11 ∧
    countFinBool 64 (fun m =>
      decide (parityWeight (coreWordLen9 m) ≥ 6) &&
        isSurvivingMod512Bool (coreWordMod512 (coreWordLen9 m))) = 16 ∧
    (∀ (m8 : Fin 32) (m9 : Fin 64),
      parityWeight (coreWordLen8 m8.val) ≥ 6 ->
      parityWeight (coreWordLen9 m9.val) ≥ 6 ->
      isSurvivingMod512Bool (coreWordMod512 (coreWordLen8 m8.val)) = true ->
      isSurvivingMod512Bool (coreWordMod512 (coreWordLen9 m9.val)) = true ->
      coreWordMod512 (coreWordLen8 m8.val) ≠ coreWordMod512 (coreWordLen9 m9.val)) ∧
    (∀ (i : Fin 16) (j : Fin 32),
      isSurvivingMod512Bool (32 * i.val + j.val) = true ->
      (∃ m8 : Fin 32, parityWeight (coreWordLen8 m8.val) ≥ 6 ∧
        coreWordMod512 (coreWordLen8 m8.val) = 32 * i.val + j.val) ∨
      (∃ m9 : Fin 64, parityWeight (coreWordLen9 m9.val) ≥ 6 ∧
        coreWordMod512 (coreWordLen9 m9.val) = 32 * i.val + j.val)) := by
  decide

theorem odd_mul_mod_pow2_cancel_w6 (s : Nat) (hodd : s % 2 = 1) :
    ∀ (k a b : Nat), (s * a) % (2 ^ k) = (s * b) % (2 ^ k) -> a % (2 ^ k) = b % (2 ^ k)
  | 0, _, _, _ => by rw [Nat.pow_zero, Nat.mod_one, Nat.mod_one]
  | k + 1, a, b, heq => by
    have h2pow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [h2pow] at heq ⊢
    have hm2 : (s * a) % 2 = (s * b) % 2 := by
      have h1 := mod_mul_mod_eq (s * a) 2 (2 ^ k)
      have h2 := mod_mul_mod_eq (s * b) 2 (2 ^ k)
      rw [← h1, ← h2, heq]
    have hab2 : a % 2 = b % 2 := by
      rw [Nat.mul_mod s a 2, Nat.mul_mod s b 2, hodd, Nat.one_mul, Nat.one_mul,
          Nat.mod_mod, Nat.mod_mod] at hm2
      exact hm2
    let r0 := a % 2
    have hr0_lt2 : r0 < 2 := Nat.mod_lt a (by decide)
    let qa := a / 2
    let qb := b / 2
    have ha_eq : a = 2 * qa + r0 := (Nat.div_add_mod a 2).symm
    have hb_eq : b = 2 * qb + r0 := by
      have hdm := (Nat.div_add_mod b 2).symm
      dsimp [qb, r0]; omega
    have hsa : s * a = 2 * (s * qa) + s * r0 := by
      rw [ha_eq, Nat.mul_add, ← Nat.mul_assoc s 2 qa, Nat.mul_comm s 2, Nat.mul_assoc]
    have hsb : s * b = 2 * (s * qb) + s * r0 := by
      rw [hb_eq, Nat.mul_add, ← Nat.mul_assoc s 2 qb, Nat.mul_comm s 2, Nat.mul_assoc]
    rw [hsa, hsb] at heq
    have hcanc := add_right_cancel_mod_sec9 (2 * 2 ^ k)
      (2 * (s * qa)) (2 * (s * qb)) (s * r0)
      (Nat.mul_pos (by decide) (pow2_pos_nat k)) heq
    rw [Nat.mul_mod_mul_left 2 (s * qa) (2 ^ k),
        Nat.mul_mod_mul_left 2 (s * qb) (2 ^ k)] at hcanc
    have hsq : (s * qa) % (2 ^ k) = (s * qb) % (2 ^ k) := by omega
    have ih := odd_mul_mod_pow2_cancel_w6 s hodd k qa qb hsq
    have hmod_step : ∀ q : Nat, (2 * q + r0) % (2 * 2 ^ k) = 2 * (q % 2 ^ k) + r0 := by
      intro q
      have hqdm := (Nat.div_add_mod q (2 ^ k)).symm
      have hql : q % 2 ^ k < 2 ^ k := Nat.mod_lt q (pow2_pos_nat k)
      have hrew : 2 * q + r0 = (2 * (q % 2 ^ k) + r0) + (2 * 2 ^ k) * (q / 2 ^ k) := by
        conv => lhs; lhs; rhs; rw [hqdm]
        rw [Nat.mul_add 2, ← Nat.mul_assoc 2 (2 ^ k)]
        omega
      rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [ha_eq, hb_eq, hmod_step qa, hmod_step qb, ih]

/--
  Bridge Theorem (`exactBackwardQuotient_mod512_eq_coreWordMod512`, zero custom axioms):
  For EVERY core parity word `u` with `parityWeight u ≥ 6` and EVERY `q : Nat`,
  `exactBackwardQuotient 1 u q % 512 = coreWordMod512 u` — formally linking the fast `O(|u|)`
  `coreWordMod512` operator in `mod512_surviving_prefix_partition_cert` to `exactBackwardQuotient`.
-/
theorem exactBackwardQuotient_mod512_eq_coreWordMod512
    (u : List Bool) (q : Nat) (hu : IsCoreParityWord u) (hw : parityWeight u ≥ 6) :
    exactBackwardQuotient 1 u q % 512 = coreWordMod512 u := by
  let w := parityWeight u
  let y0 := exactBackwardQuotient 1 u 0
  let L0 := backwardOneTotalSteps u 0
  rcases mod373248_ray_dyadic_pinning_and_triadic_bijection u hu hw with ⟨hL0_ge10, hpin512, _⟩
  rcases one_generator_pos_odd_and_reaches_one u 0 hu with ⟨_, _, heq0, _⟩
  change 2 ^ L0 = 3 ^ w * y0 + affineCarry u at heq0
  have h2L0_mod : (2 ^ L0) % 512 = 0 := by
    have hs : L0 = 9 + (L0 - 9) := by omega
    rw [hs, Nat.pow_add, show (2 : Nat) ^ 9 = 512 from rfl, Nat.mul_mod_right]
  have hy0_eq : (3 ^ w * y0 + affineCarry u) % 512 = 0 := by
    rw [← heq0, h2L0_mod]
  let s := (3 ^ w) % 512
  have hs_lt : s < 512 := Nat.mod_lt (3 ^ w) (by decide)
  have hs_odd : s % 2 = 1 := by
    dsimp [s]
    rw [show (512 : Nat) = 2 * 256 from rfl, mod_mul_mod_eq (3 ^ w) 2 256]
    exact pow3_odd_nat_sec8 w
  let m := s / 2
  have hm_lt : m < 256 := by dsimp [m]; omega
  let a : Fin 16 := ⟨m / 16, by omega⟩
  let b : Fin 16 := ⟨m % 16, Nat.mod_lt m (by decide)⟩
  have hd_eq : 2 * (16 * a.val + b.val) + 1 = s := by
    dsimp [a, b, m]; omega
  have hinv_s : (s * invMod512Odd s) % 512 = 1 := by
    have hc := mod512_surviving_prefix_partition_cert.1 a b
    dsimp only at hc
    rwa [hd_eq] at hc
  have hinv_eq : invMod512Odd (3 ^ w) = invMod512Odd s := by
    unfold invMod512Odd
    dsimp [s]
    rw [Nat.mod_mod]
  have hinv_3w : (3 ^ w * invMod512Odd (3 ^ w)) % 512 = 1 := by
    have hm1 : (3 ^ w * invMod512Odd s) % 512 = ((3 ^ w % 512) * (invMod512Odd s % 512)) % 512 :=
      Nat.mul_mod (3 ^ w) (invMod512Odd s) 512
    have hm2 : (s * invMod512Odd s) % 512 = ((s % 512) * (invMod512Odd s % 512)) % 512 :=
      Nat.mul_mod s (invMod512Odd s) 512
    have hs_mod : s % 512 = 3 ^ w % 512 := Nat.mod_mod (3 ^ w) 512
    rw [hinv_eq, hm1, ← hs_mod, ← hm2]
    exact hinv_s
  let cMod := affineCarry u % 512
  have hc_lt : cMod < 512 := Nat.mod_lt (affineCarry u) (by decide)
  have hcore_mul : (3 ^ w * coreWordMod512 u) % 512 = (512 - cMod) % 512 := by
    unfold coreWordMod512
    change (3 ^ w * (((512 - cMod) * invMod512Odd (3 ^ w)) % 512)) % 512 = _
    rw [Nat.mul_mod (3 ^ w), Nat.mod_mod, ← Nat.mul_mod,
        Nat.mul_comm (512 - cMod) (invMod512Odd (3 ^ w)),
        ← Nat.mul_assoc (3 ^ w) (invMod512Odd (3 ^ w)) (512 - cMod),
        Nat.mul_mod (3 ^ w * invMod512Odd (3 ^ w)) (512 - cMod) 512,
        hinv_3w, Nat.one_mul, Nat.mod_mod]
  have hcore_eq : (3 ^ w * coreWordMod512 u + affineCarry u) % 512 = 0 := by
    rw [Nat.add_mod, hcore_mul, show affineCarry u % 512 = cMod from rfl,
        Nat.mod_add_mod, show 512 - cMod + cMod = 512 by omega, Nat.mod_self]
  have hcanc := add_right_cancel_mod_sec9 512
    (3 ^ w * y0) (3 ^ w * coreWordMod512 u) (affineCarry u)
    (by decide) (hy0_eq.trans hcore_eq.symm)
  have hy0_core := odd_mul_mod_pow2_cancel_w6 (3 ^ w) (pow3_odd_nat_sec8 w) 9 y0 (coreWordMod512 u)
    (by rw [show (2 : Nat) ^ 9 = 512 from rfl]; exact hcanc)
  rw [show (2 : Nat) ^ 9 = 512 from rfl] at hy0_core
  have hcore_lt : coreWordMod512 u < 512 := by
    unfold coreWordMod512; exact Nat.mod_lt _ (by decide)
  rw [hpin512 q, hy0_core, Nat.mod_eq_of_lt hcore_lt]

theorem parityOfIter_inj_mod_pow2_w6 (k x1 x2 : Nat)
    (heq : parityOfIter k x1 = parityOfIter k x2) :
    x1 % (2 ^ k) = x2 % (2 ^ k) := by
  let v := parityOfIter k x1
  have h1 := nat_affine_of_parityOfIter k x1
  have h2 := nat_affine_of_parityOfIter k x2
  rw [← heq] at h2
  change 2 ^ k * collatzIter k x1 = 3 ^ parityWeight v * x1 + affineCarry v at h1
  change 2 ^ k * collatzIter k x2 = 3 ^ parityWeight v * x2 + affineCarry v at h2
  have hm1 : (3 ^ parityWeight v * x1 + affineCarry v) % (2 ^ k) = 0 := by
    rw [← h1, Nat.mul_mod_right]
  have hm2 : (3 ^ parityWeight v * x2 + affineCarry v) % (2 ^ k) = 0 := by
    rw [← h2, Nat.mul_mod_right]
  have hcanc := add_right_cancel_mod_sec9 (2 ^ k)
    (3 ^ parityWeight v * x1) (3 ^ parityWeight v * x2) (affineCarry v)
    (pow2_pos_nat k) (hm1.trans hm2.symm)
  exact odd_mul_mod_pow2_cancel_w6 (3 ^ parityWeight v)
    (pow3_odd_nat_sec8 (parityWeight v)) k x1 x2 hcanc

/--
  Theorem W6.4b (`mod512_surviving_prefix_uniform_fibers`, zero custom axioms):
  Universal Length-`L ≥ 10` Free-Bit Fiber Uniformity Modulo `512`:
  For EVERY 9-bit prefix `p9 : List Bool` (`p9.length = 9`, `p9.head? = some true`),
  EVERY free middle word `freeBits : List Bool` (`u = p9 ++ freeBits ++ [true]`, `|u| = L ≥ 10`),
  and EVERY `q : Nat` with `parityWeight u ≥ 6`:
  1. `IsCoreParityWord (p9 ++ freeBits ++ [true])` holds unconditionally;
  2. `parityOfIter 9 (exactBackwardQuotient 1 (p9 ++ freeBits ++ [true]) q % 512) = p9`;
  3. Across ALL `2 ^ (L - 10)` choices of `freeBits` (`fb1, fb2`) and ALL `q1, q2 : Nat`
     with weight `≥ 6`, `exactBackwardQuotient 1 (p9 ++ fb1 ++ [true]) q1 % 512 =
     exactBackwardQuotient 1 (p9 ++ fb2 ++ [true]) q2 % 512` (so each of the `27` surviving
     9-bit prefixes generates an exact uniform fiber of `2 ^ (L - 10)` length-`L` core words)!
-/
theorem mod512_surviving_prefix_uniform_fibers
    (p9 : List Bool) (hp9_len : p9.length = 9) (hp9_head : p9.head? = some true) :
    (∀ freeBits : List Bool, IsCoreParityWord (p9 ++ freeBits ++ [true])) ∧
    (∀ (freeBits : List Bool) (q : Nat),
      let u := p9 ++ freeBits ++ [true]
      parityWeight u ≥ 6 ->
      parityOfIter 9 (exactBackwardQuotient 1 u q % 512) = p9) ∧
    (∀ (fb1 fb2 : List Bool) (q1 q2 : Nat),
      parityWeight (p9 ++ fb1 ++ [true]) ≥ 6 ->
      parityWeight (p9 ++ fb2 ++ [true]) ≥ 6 ->
      exactBackwardQuotient 1 (p9 ++ fb1 ++ [true]) q1 % 512 =
        exactBackwardQuotient 1 (p9 ++ fb2 ++ [true]) q2 % 512) := by
  have hcore : ∀ freeBits : List Bool, IsCoreParityWord (p9 ++ freeBits ++ [true]) := by
    intro freeBits
    refine ⟨?_, ?_⟩
    · cases hp : p9 with
      | nil => rw [hp] at hp9_head; simp at hp9_head
      | cons b rest =>
        rw [hp] at hp9_head; simp only [List.head?_cons] at hp9_head
        simp [hp9_head]
    · rw [List.reverse_append]
      rfl
  have hpar9 : ∀ (freeBits : List Bool) (q : Nat),
      parityWeight (p9 ++ freeBits ++ [true]) ≥ 6 ->
      parityOfIter 9 (exactBackwardQuotient 1 (p9 ++ freeBits ++ [true]) q % 512) = p9 := by
    intro freeBits q hw6
    let u := p9 ++ freeBits ++ [true]
    have hu : IsCoreParityWord u := hcore freeBits
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
  refine ⟨hcore, hpar9, ?_⟩
  intro fb1 fb2 q1 q2 hw1 hw2
  have hp1 := hpar9 fb1 q1 hw1
  have hp2 := hpar9 fb2 q2 hw2
  have hinj := parityOfIter_inj_mod_pow2_w6 9
    (exactBackwardQuotient 1 (p9 ++ fb1 ++ [true]) q1 % 512)
    (exactBackwardQuotient 1 (p9 ++ fb2 ++ [true]) q2 % 512)
    (hp1.trans hp2.symm)
  rw [show (2 : Nat) ^ 9 = 512 from rfl, Nat.mod_mod, Nat.mod_mod] at hinj
  exact hinj

theorem parityWeight_append_w6 :
    ∀ (u v : List Bool), parityWeight (u ++ v) = parityWeight u + parityWeight v
  | [], _ => by simp [parityWeight]
  | false :: rest, v => parityWeight_append_w6 rest v
  | true :: rest, v => by
    change 1 + parityWeight (rest ++ v) = 1 + parityWeight rest + parityWeight v
    rw [parityWeight_append_w6 rest v, Nat.add_assoc]

theorem survivingMod512Bool_nine_prefix_head_two_true_grid :
    ∀ (i : Fin 16) (j : Fin 32),
      isSurvivingMod512Bool (32 * i.val + j.val) = true ->
      (parityOfIter 9 (32 * i.val + j.val)).take 2 = [true, true] := by
  decide

theorem survivingMod512Bool_nine_prefix_head_two_true (r : Nat) (hr : r < 512)
    (hb : isSurvivingMod512Bool r = true) :
    (parityOfIter 9 r).take 2 = [true, true] := by
  have hi : r / 32 < 16 := by omega
  have hj : r % 32 < 32 := Nat.mod_lt r (by decide)
  have hsplit : 32 * (r / 32) + r % 32 = r := Nat.div_add_mod r 32
  have hg := survivingMod512Bool_nine_prefix_head_two_true_grid ⟨r / 32, hi⟩ ⟨r % 32, hj⟩
  dsimp only at hg
  rw [hsplit] at hg
  exact hg hb

/--
  Theorem W6.4b'' (`surviving_mod512_nine_prefix_auto_weight_and_characterization`, zero custom axioms):
  Complete 9-Bit Surviving Core-Prefix Biconditional & Automatic `w ≥ 7` Fiber Theorem (`|u| ≥ 10`):
  1. Automatic Weight `≥ 7` & Mod-`512` Pinning on ALL `2^(L - 10)` Free-Bit Extensions:
     For EVERY surviving residue `r < 512` (`isSurvivingMod512Bool r = true`), its 9-step parity
     prefix `p9 := parityOfIter 9 r` satisfies `p9.length = 9`, `p9.take 2 = [true, true]`, and
     `parityWeight p9 ≥ 6`, so for EVERY `freeBits : List Bool` (with ZERO external weight side-condition!)
     and EVERY `q : Nat`, `u := p9 ++ freeBits ++ [true]` automatically satisfies:
       `IsCoreParityWord u ∧ parityWeight u ≥ 7 ∧ exactBackwardQuotient 1 u q % 512 = r`!
  2. Exact Necessary Condition on `IsSurvivingMod373248Class` (`|u| ≥ 10`):
     Conversely, for ANY 9-bit prefix `p9` (`p9.length = 9`), ANY `freeBits : List Bool`, and ANY
     `q : Nat`, if `IsCoreParityWord (p9 ++ freeBits ++ [true])` and
     `IsSurvivingMod373248Class (exactBackwardQuotient 1 (p9 ++ freeBits ++ [true]) q)`, then
     `p9` MUST equal `parityOfIter 9 r` for one of the `27` surviving `mod 512` classes `r < 512`!
-/
theorem surviving_mod512_nine_prefix_auto_weight_and_characterization :
    (∀ (r : Nat), r < 512 -> isSurvivingMod512Bool r = true ->
      let p9 := parityOfIter 9 r
      p9.length = 9 ∧
      p9.take 2 = [true, true] ∧
      parityWeight p9 ≥ 6 ∧
      (∀ (freeBits : List Bool) (q : Nat),
        let u := p9 ++ freeBits ++ [true]
        IsCoreParityWord u ∧
        parityWeight u ≥ 7 ∧
        exactBackwardQuotient 1 u q % 512 = r ∧
        isSurvivingMod512Bool (exactBackwardQuotient 1 u q % 512) = true)) ∧
    (∀ (p9 freeBits : List Bool) (q : Nat),
      p9.length = 9 ->
      IsCoreParityWord (p9 ++ freeBits ++ [true]) ->
      IsSurvivingMod373248Class (exactBackwardQuotient 1 (p9 ++ freeBits ++ [true]) q) ->
      ∃ r : Nat, r < 512 ∧ isSurvivingMod512Bool r = true ∧ p9 = parityOfIter 9 r) := by
  refine ⟨?_, ?_⟩
  · intro r hr_lt hb
    dsimp only
    let p9 := parityOfIter 9 r
    have hp9_len : p9.length = 9 := parityOfIter_length 9 r
    have hp9_t2 : p9.take 2 = [true, true] :=
      survivingMod512Bool_nine_prefix_head_two_true r hr_lt hb
    have hp9_wt : parityWeight p9 ≥ 6 :=
      survivingMod512Bool_nine_step_weight_ge_six r hr_lt hb
    have hp9_head : p9.head? = some true := by
      cases hp : p9 with
      | nil => rw [hp] at hp9_t2; simp at hp9_t2
      | cons b rest =>
        rw [hp] at hp9_t2
        cases rest with
        | nil => simp at hp9_t2
        | cons b2 _ =>
          simp only [List.take] at hp9_t2
          injection hp9_t2 with hb1 _
          simp [hb1]
    rcases mod512_surviving_prefix_uniform_fibers p9 hp9_len hp9_head with ⟨hcore, hpar9, _⟩
    refine ⟨hp9_len, hp9_t2, hp9_wt, ?_⟩
    intro freeBits q
    let u := p9 ++ freeBits ++ [true]
    have hwt_u : parityWeight u ≥ 7 := by
      dsimp [u]
      rw [parityWeight_append_w6 (p9 ++ freeBits) [true],
          parityWeight_append_w6 p9 freeBits]
      have hwt1 : parityWeight [true] = 1 := rfl
      rw [hwt1]
      omega
    have hpar_eq : parityOfIter 9 (exactBackwardQuotient 1 u q % 512) = parityOfIter 9 r :=
      hpar9 freeBits q (Nat.le_trans (by decide : 6 ≤ 7) hwt_u)
    have hmod_eq := parityOfIter_inj_mod_pow2_w6 9
      (exactBackwardQuotient 1 u q % 512) r hpar_eq
    rw [show (2 : Nat) ^ 9 = 512 from rfl, Nat.mod_mod, Nat.mod_eq_of_lt hr_lt] at hmod_eq
    refine ⟨hcore freeBits, hwt_u, hmod_eq, ?_⟩
    rw [hmod_eq]; exact hb
  · intro p9 freeBits q hp9_len hcore hs373
    let u := p9 ++ freeBits ++ [true]
    have hw6 : parityWeight u ≥ 6 := by
      by_cases hw5 : parityWeight u ≤ 5
      · exact False.elim (one_generator_weight_le_five_never_surviving_mod373248 u q hcore hw5 hs373)
      · omega
    have hp9_head : p9.head? = some true := by
      cases hp : p9 with
      | nil => rw [hp] at hp9_len; simp at hp9_len
      | cons b rest =>
        have hh := hcore.1
        rw [hp] at hh
        simpa using hh
    let r := exactBackwardQuotient 1 u q % 512
    have hr_lt : r < 512 := Nat.mod_lt _ (by decide)
    have hr_bool : isSurvivingMod512Bool r = true :=
      survivingMod512_imp_bool_true r hs373.1
    have hp9_eq : parityOfIter 9 r = p9 :=
      (mod512_surviving_prefix_uniform_fibers p9 hp9_len hp9_head).2.1 freeBits q hw6
    exact ⟨r, hr_lt, hr_bool, hp9_eq.symm⟩

-- ----------------------------------------------------------------------------
-- W6.4c: Exponential `q`-Growth (`≥ 2^(486*q)`) & Universal Anti-Cutoff
--        Bounded-Length Non-Covering Theorem on `IsSurvivingMod373248Class`
-- ----------------------------------------------------------------------------

inductive NoDupNat : List Nat -> Prop where
  | nil : NoDupNat []
  | cons (x : Nat) (xs : List Nat) : x ∉ xs -> NoDupNat xs -> NoDupNat (x :: xs)

def eraseAllNat (b : Nat) : List Nat -> List Nat
  | [] => []
  | x :: xs => if x = b then eraseAllNat b xs else x :: eraseAllNat b xs

theorem mem_eraseAllNat_iff (b : Nat) :
    ∀ (xs : List Nat) (y : Nat), y ∈ eraseAllNat b xs ↔ (y ∈ xs ∧ y ≠ b)
  | [], y => by simp [eraseAllNat]
  | x :: xs, y => by
    simp only [eraseAllNat]
    by_cases hxb : x = b
    · simp only [hxb, ite_true, mem_eraseAllNat_iff b xs y, List.mem_cons]
      constructor
      · rintro ⟨hm, hne⟩; exact ⟨Or.inr hm, hne⟩
      · rintro ⟨ rfl | hm, hne⟩
        · exact False.elim (hne rfl)
        · exact ⟨hm, hne⟩
    · simp only [hxb, ite_false, List.mem_cons, mem_eraseAllNat_iff b xs y]
      constructor
      · rintro (rfl | ⟨hm, hne⟩)
        · exact ⟨Or.inl rfl, hxb⟩
        · exact ⟨Or.inr hm, hne⟩
      · rintro ⟨rfl | hm, hne⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hm, hne⟩

theorem eraseAllNat_of_not_mem (b : Nat) :
    ∀ (xs : List Nat), b ∉ xs -> eraseAllNat b xs = xs
  | [], _ => rfl
  | x :: xs, hnm => by
    have hxb : x ≠ b := fun h => hnm (h ▸ List.Mem.head _)
    have hnm_xs : b ∉ xs := fun hm => hnm (List.mem_cons_of_mem _ hm)
    simp only [eraseAllNat, hxb, ite_false, eraseAllNat_of_not_mem b xs hnm_xs]

theorem nodup_eraseAllNat_and_len (b : Nat) :
    ∀ (cands : List Nat),
      NoDupNat cands ->
      NoDupNat (eraseAllNat b cands) ∧ cands.length ≤ (eraseAllNat b cands).length + 1
  | [], _ => ⟨NoDupNat.nil, by simp [eraseAllNat]⟩
  | x :: xs, NoDupNat.cons _ _ hnx hnd_xs => by
    by_cases hxb : x = b
    · subst hxb
      simp only [eraseAllNat, ite_true, eraseAllNat_of_not_mem x xs hnx, List.length_cons]
      exact ⟨hnd_xs, Nat.le_refl _⟩
    · rcases nodup_eraseAllNat_and_len b xs hnd_xs with ⟨hnd_er, hlen_er⟩
      simp only [eraseAllNat, hxb, ite_false, List.length_cons]
      have hnx_er : x ∉ eraseAllNat b xs := fun hm => hnx ((mem_eraseAllNat_iff b xs x).mp hm).1
      exact ⟨NoDupNat.cons x _ hnx_er hnd_er, by omega⟩

theorem exists_nodup_not_mem :
    ∀ (bad cands : List Nat),
      NoDupNat cands -> bad.length < cands.length ->
      ∃ y : Nat, y ∈ cands ∧ y ∉ bad
  | [], [], _, hlt => by simp at hlt
  | [], c0 :: _, _, _ => ⟨c0, List.Mem.head _, by simp⟩
  | b :: bs, cands, hnd, hlt => by
    rcases nodup_eraseAllNat_and_len b cands hnd with ⟨hnd', hlen'⟩
    simp only [List.length_cons] at hlt
    rcases exists_nodup_not_mem bs (eraseAllNat b cands) hnd' (by omega) with ⟨y, hy_er, hy_nbs⟩
    rcases (mem_eraseAllNat_iff b cands y).mp hy_er with ⟨hy_c, hy_neb⟩
    refine ⟨y, hy_c, ?_⟩
    simp only [List.mem_cons]
    rintro (rfl | hm)
    · exact hy_neb rfl
    · exact hy_nbs hm

def allBoolWordsOfLen : Nat -> List (List Bool)
  | 0 => [[]]
  | k + 1 => (allBoolWordsOfLen k).map (false :: ·) ++ (allBoolWordsOfLen k).map (true :: ·)

def allBoolWordsUpTo : Nat -> List (List Bool)
  | 0 => [[]]
  | k + 1 => allBoolWordsUpTo k ++ allBoolWordsOfLen (k + 1)

theorem allBoolWordsOfLen_spec :
    ∀ k : Nat,
      (allBoolWordsOfLen k).length = 2 ^ k ∧
      (∀ v : List Bool, v.length = k -> v ∈ allBoolWordsOfLen k)
  | 0 => ⟨rfl, fun v hv => by cases v with | nil => exact List.Mem.head _ | cons _ _ => simp at hv⟩
  | k + 1 => by
    rcases allBoolWordsOfLen_spec k with ⟨hlen, hmem⟩
    refine ⟨?_, ?_⟩
    · simp only [allBoolWordsOfLen, List.length_append, List.length_map, hlen, Nat.pow_succ]
      omega
    · intro v hv
      cases v with
      | nil => simp at hv
      | cons b rest =>
        simp only [List.length_cons] at hv
        have hr_mem := hmem rest (by omega)
        simp only [allBoolWordsOfLen, List.mem_append]
        cases b with
        | false => exact Or.inl (List.mem_map.mpr ⟨rest, hr_mem, rfl⟩)
        | true => exact Or.inr (List.mem_map.mpr ⟨rest, hr_mem, rfl⟩)

theorem allBoolWordsUpTo_spec :
    ∀ L : Nat,
      (allBoolWordsUpTo L).length < 2 ^ (L + 1) ∧
      (∀ u : List Bool, u.length ≤ L -> u ∈ allBoolWordsUpTo L)
  | 0 => ⟨by decide, fun u hu => (allBoolWordsOfLen_spec 0).2 u (by omega)⟩
  | k + 1 => by
    rcases allBoolWordsUpTo_spec k with ⟨hlen_u, hmem_u⟩
    rcases allBoolWordsOfLen_spec (k + 1) with ⟨hlen_e, hmem_e⟩
    refine ⟨?_, ?_⟩
    · simp only [allBoolWordsUpTo, List.length_append, hlen_e, Nat.pow_succ 2 (k + 1)]
      omega
    · intro u hu
      simp only [allBoolWordsUpTo, List.mem_append]
      by_cases hle : u.length ≤ k
      · exact Or.inl (hmem_u u hle)
      · exact Or.inr (hmem_e u (by omega))

def rayHitsForWord : List Bool -> Nat -> List Nat
  | _, 0 => []
  | u, q + 1 => exactBackwardQuotient 1 u q :: rayHitsForWord u q

def boundedRayHits : List (List Bool) -> Nat -> List Nat
  | [], _ => []
  | u :: us, Q => rayHitsForWord u Q ++ boundedRayHits us Q

theorem rayHitsForWord_spec (u : List Bool) :
    ∀ Q : Nat,
      (rayHitsForWord u Q).length = Q ∧
      (∀ q : Nat, q < Q -> exactBackwardQuotient 1 u q ∈ rayHitsForWord u Q)
  | 0 => ⟨rfl, fun _ hq => by omega⟩
  | Q' + 1 => by
    rcases rayHitsForWord_spec u Q' with ⟨hlen, hmem⟩
    refine ⟨by simp only [rayHitsForWord, List.length_cons, hlen], ?_⟩
    intro q hq
    simp only [rayHitsForWord]
    by_cases hq_eq : q = Q'
    · subst hq_eq; exact List.Mem.head _
    · exact List.mem_cons_of_mem _ (hmem q (by omega))

theorem boundedRayHits_spec :
    ∀ (words : List (List Bool)) (Q : Nat),
      (boundedRayHits words Q).length = words.length * Q ∧
      (∀ u ∈ words, ∀ q : Nat, q < Q -> exactBackwardQuotient 1 u q ∈ boundedRayHits words Q)
  | [], _ => ⟨by simp [boundedRayHits], fun _ hm _ _ => by cases hm⟩
  | u :: us, Q => by
    rcases rayHitsForWord_spec u Q with ⟨hl_u, hm_u⟩
    rcases boundedRayHits_spec us Q with ⟨hl_us, hm_us⟩
    simp only [boundedRayHits, List.length_append, List.length_cons, hl_u, hl_us, Nat.add_mul, Nat.one_mul]
    refine ⟨by omega, ?_⟩
    intro w hw q hq
    simp only [List.mem_cons] at hw
    simp only [List.mem_append]
    rcases hw with rfl | hw_us
    · exact Or.inl (hm_u q hq)
    · exact Or.inr (hm_us w hw_us q hq)

def survivingCand373248 (m : Nat) : Nat :=
  373248 * m + 184111

def survivingCandList : Nat -> List Nat
  | 0 => []
  | k + 1 => survivingCand373248 k :: survivingCandList k

theorem survivingCandList_spec :
    ∀ K : Nat,
      (survivingCandList K).length = K ∧
      NoDupNat (survivingCandList K) ∧
      (∀ y ∈ survivingCandList K, ∃ m : Nat, m < K ∧ y = survivingCand373248 m)
  | 0 => ⟨rfl, NoDupNat.nil, fun _ hm => by cases hm⟩
  | k + 1 => by
    rcases survivingCandList_spec k with ⟨hlen, hnd, hmem⟩
    have hnot_mem : survivingCand373248 k ∉ survivingCandList k := by
      intro hm
      rcases hmem _ hm with ⟨m, hm_lt, heq⟩
      unfold survivingCand373248 at heq
      omega
    refine ⟨by simp only [survivingCandList, List.length_cons, hlen],
            NoDupNat.cons _ _ hnot_mem hnd, ?_⟩
    intro y hy
    simp only [survivingCandList, List.mem_cons] at hy
    rcases hy with rfl | hy_k
    · exact ⟨k, by omega, rfl⟩
    · rcases hmem y hy_k with ⟨m, hm_lt, heq⟩
      exact ⟨m, by omega, heq⟩

/--
  Theorem W6.4c (`bounded_length_ray_exponential_sparsity_and_noncovering`, zero custom axioms):
  1. Universal Exponential `q`-Growth (`w ≥ 6`): For EVERY core word `u` with `parityWeight u ≥ 6`
     and EVERY `q : Nat`, `exactBackwardQuotient 1 u q ≥ 2 ^ (486 * q)`!
  2. Universal Anti-Cutoff / Bounded-Length Non-Covering Theorem: For EVERY finite core-length
     cutoff `L_max : Nat`, there exists an explicit surviving target `n ∈ IsSurvivingMod373248Class`
     missed by EVERY `(u, q)` with `IsCoreParityWord u` and `u.length ≤ L_max` (`∀ q : Nat`)!
     Thus NO finite core-word family (`|u| ≤ L_max`, even summed over all `q ∈ Nat`) can ever
     cover `IsSurvivingMod373248Class` — asymptotic natural density is identically `0`
     (`O_{L_max}(log X / X) -> 0` across ALL `q ∈ Nat`)!
-/
theorem bounded_length_ray_exponential_sparsity_and_noncovering :
    (∀ (u : List Bool) (q : Nat),
      IsCoreParityWord u -> parityWeight u ≥ 6 ->
      exactBackwardQuotient 1 u q ≥ 2 ^ (486 * q)) ∧
    (∀ L_max : Nat,
      ∃ n : Nat,
        IsSurvivingMod373248Class n ∧
        ∀ (u : List Bool) (q : Nat),
          IsCoreParityWord u -> u.length ≤ L_max ->
          exactBackwardQuotient 1 u q ≠ n) := by
  have hexp_q : ∀ (u : List Bool) (q : Nat),
      IsCoreParityWord u -> parityWeight u ≥ 6 ->
      exactBackwardQuotient 1 u q ≥ 2 ^ (486 * q) := by
    intro u q hu hw6
    have hp3_ge243 : 3 ^ (parityWeight u - 1) ≥ 243 := by
      have hs : parityWeight u - 1 = 5 + (parityWeight u - 6) := by omega
      rw [hs, Nat.pow_add, show (3 : Nat) ^ 5 = 243 from rfl]
      have hm := Nat.mul_le_mul_left 243 (pow3_pos_nat (parityWeight u - 6))
      omega
    have hP_ge486 : 2 * 3 ^ (parityWeight u - 1) ≥ 486 := by omega
    let stepExp := 486
    have hP_ge_step : stepExp ≤ 2 * 3 ^ (parityWeight u - 1) := hP_ge486
    change exactBackwardQuotient 1 u q ≥ 2 ^ (stepExp * q)
    induction q with
    | zero =>
      rw [Nat.mul_zero, Nat.pow_zero]
      exact (one_generator_pos_odd_and_reaches_one u 0 hu).1
    | succ q' ih =>
      rcases exactBackwardQuotient_one_ray_step_law u q' hu with ⟨_, _, haff⟩
      have hp2_ge : 2 ^ stepExp ≤ 2 ^ (2 * 3 ^ (parityWeight u - 1)) :=
        pow2_mono_nat hP_ge_step
      have hm := Nat.mul_le_mul hp2_ge ih
      have hexp_add : stepExp + stepExp * q' = stepExp * (q' + 1) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      rw [← Nat.pow_add 2 stepExp (stepExp * q'), hexp_add] at hm
      rw [haff]
      exact Nat.le_trans hm (Nat.le_add_right _ _)
  refine ⟨hexp_q, ?_⟩
  intro L_max
  let words := allBoolWordsUpTo L_max
  let Q := L_max + 1
  let bad := boundedRayHits words Q
  let M := bad.length
  let cands := survivingCandList (M + 1)
  rcases allBoolWordsUpTo_spec L_max with ⟨hwords_len, hwords_mem⟩
  rcases boundedRayHits_spec words Q with ⟨hbad_len, hbad_mem⟩
  rcases survivingCandList_spec (M + 1) with ⟨hcands_len, hcands_nd, hcands_mem⟩
  have hlt_bc : bad.length < cands.length := by
    rw [hcands_len]; dsimp [M]; omega
  rcases exists_nodup_not_mem bad cands hcands_nd hlt_bc with ⟨n, hn_cands, hn_nbad⟩
  rcases hcands_mem n hn_cands with ⟨m, hm_lt, hn_eq⟩
  -- 1. `IsSurvivingMod373248Class n` (`n ≡ 184111 mod 373248`):
  have hs_184 : IsSurvivingMod373248Class 184111 :=
    mod373248_min_weight_six_witness_184111.2.2.2.2.2.1
  have hn_surv : IsSurvivingMod373248Class n := by
    rw [hn_eq]
    unfold survivingCand373248 IsSurvivingMod373248Class at *
    have hm512 : (373248 * m + 184111) % 512 = 184111 % 512 := by
      rw [show 373248 * m + 184111 = 184111 + 512 * (729 * m) by omega,
          Nat.add_mul_mod_self_left]
    have hm729 : (373248 * m + 184111) % 729 = 184111 % 729 := by
      rw [show 373248 * m + 184111 = 184111 + 729 * (512 * m) by omega,
          Nat.add_mul_mod_self_left]
    rw [hm512, hm729]
    exact hs_184
  refine ⟨n, hn_surv, ?_⟩
  intro u q hu hlen_u heq_y
  by_cases hw5 : parityWeight u ≤ 5
  · have hdisj := one_generator_weight_le_five_never_surviving_mod373248 u q hu hw5
    rw [heq_y] at hdisj
    exact hdisj hn_surv
  · have hw6 : parityWeight u ≥ 6 := by omega
    by_cases hq_lt : q < Q
    · have hu_mem : u ∈ words := hwords_mem u hlen_u
      have hy_bad : exactBackwardQuotient 1 u q ∈ bad := hbad_mem u hu_mem q hq_lt
      rw [heq_y] at hy_bad
      exact hn_nbad hy_bad
    · -- `q ≥ L_max + 1`: `exactBackwardQuotient 1 u q ≥ 2 ^ (486 * (L_max + 1)) > n`!
      have hq_ge : q ≥ L_max + 1 := by dsimp [Q] at hq_lt; omega
      have hy_ge : exactBackwardQuotient 1 u q ≥ 2 ^ (486 * (L_max + 1)) :=
        Nat.le_trans (pow2_mono_nat (Nat.mul_le_mul_left 486 hq_ge)) (hexp_q u q hu hw6)
      have hM_le : M ≤ 2 ^ (2 * L_max + 1) := by
        dsimp [M]; rw [hbad_len]
        have hQ_le : Q ≤ 2 ^ L_max := pow2_ge_succ_self L_max
        have hm1 : words.length * Q ≤ 2 ^ (L_max + 1) * 2 ^ L_max :=
          Nat.mul_le_mul (Nat.le_of_lt hwords_len) hQ_le
        rwa [← Nat.pow_add, show (L_max + 1) + L_max = 2 * L_max + 1 by omega] at hm1
      have hm_le_M : m ≤ M := by omega
      have hn_lt_p2 : n < 2 ^ (2 * L_max + 22) := by
        rw [hn_eq]; unfold survivingCand373248
        have h373 : 373248 < 2 ^ 19 := by decide
        have h184 : 184111 < 2 ^ 19 := by decide
        have hm_ub : m ≤ 2 ^ (2 * L_max + 1) := Nat.le_trans hm_le_M hM_le
        have hprod : 373248 * m < 2 ^ 19 * 2 ^ (2 * L_max + 1) := by
          by_cases hm0 : m = 0
          · rw [hm0, Nat.mul_zero]
            exact Nat.mul_pos (pow2_pos_nat 19) (pow2_pos_nat (2 * L_max + 1))
          · exact Nat.lt_of_lt_of_le
              (Nat.mul_lt_mul_of_pos_right h373 (by omega))
              (Nat.mul_le_mul_left (2 ^ 19) hm_ub)
        rw [← Nat.pow_add 2 19 (2 * L_max + 1),
            show 19 + (2 * L_max + 1) = 2 * L_max + 20 by omega] at hprod
        have hp20_ge : 2 ^ 19 ≤ 2 ^ (2 * L_max + 20) := pow2_mono_nat (by omega)
        have hp22 : 2 ^ (2 * L_max + 22) = 4 * 2 ^ (2 * L_max + 20) := by
          rw [show 2 * L_max + 22 = (2 * L_max + 20) + 2 by omega, Nat.pow_add,
              show (2 : Nat) ^ 2 = 4 from rfl, Nat.mul_comm]
        rw [hp22]; omega
      have hp22_le_486 : 2 ^ (2 * L_max + 22) ≤ 2 ^ (486 * (L_max + 1)) :=
        pow2_mono_nat (by omega)
      have hn_lt_y : n < exactBackwardQuotient 1 u q :=
        Nat.lt_of_lt_of_le hn_lt_p2 (Nat.le_trans hp22_le_486 hy_ge)
      rw [heq_y] at hn_lt_y
      exact Nat.lt_irrefl n hn_lt_y

/--
  Theorem W6.4d (`bounded_length_ray_logarithmic_counting_zero_density`, zero custom axioms):
  Quantitative Logarithmic Counting Formula & Exact Zero Natural Density for Bounded-Length Rays:
  1. For EVERY core-length cutoff `L_max : Nat` and EVERY dyadic scale `Q ≥ 1` (`X = 2 ^ (486 * Q)`),
     the explicit finite list `hits := boundedRayHits (allBoolWordsUpTo L_max) Q` has length
     strictly `< 2 ^ (L_max + 1) * Q` (`O_{L_max}(log X)` elements!) and contains EVERY surviving
     ray value `exactBackwardQuotient 1 u q < 2 ^ (486 * Q)` across ALL `IsCoreParityWord u` with
     `u.length ≤ L_max` and ALL `q : Nat`!
  2. Quantitative Zero-Density Limit (`∀ D ≥ 1, hits.length / X < 1 / D`): for EVERY integer
     `D ≥ 1`, at scale `Q := D + L_max + 2` (`Q ≥ 3`), `D * hits.length < 2 ^ (486 * Q)`, proving
     constructively in pure `Nat` arithmetic that the natural density of bounded-length ray
     families (`|u| ≤ L_max`, summed over all `q ∈ Nat`) is identically `0`!
-/
theorem bounded_length_ray_logarithmic_counting_zero_density :
    (∀ (L_max Q : Nat), Q ≥ 1 ->
      let hits := boundedRayHits (allBoolWordsUpTo L_max) Q
      hits.length < 2 ^ (L_max + 1) * Q ∧
      (∀ (u : List Bool) (q : Nat),
        IsCoreParityWord u -> u.length ≤ L_max ->
        IsSurvivingMod373248Class (exactBackwardQuotient 1 u q) ->
        exactBackwardQuotient 1 u q < 2 ^ (486 * Q) ->
        parityWeight u ≥ 6 ∧ q < Q ∧ exactBackwardQuotient 1 u q ∈ hits)) ∧
    (∀ (L_max D : Nat), D ≥ 1 ->
      let Q := D + L_max + 2
      let hits := boundedRayHits (allBoolWordsUpTo L_max) Q
      Q ≥ 3 ∧ D * hits.length < 2 ^ (486 * Q)) := by
  have hcount : ∀ (L_max Q : Nat), Q ≥ 1 ->
      let hits := boundedRayHits (allBoolWordsUpTo L_max) Q
      hits.length < 2 ^ (L_max + 1) * Q ∧
      (∀ (u : List Bool) (q : Nat),
        IsCoreParityWord u -> u.length ≤ L_max ->
        IsSurvivingMod373248Class (exactBackwardQuotient 1 u q) ->
        exactBackwardQuotient 1 u q < 2 ^ (486 * Q) ->
        parityWeight u ≥ 6 ∧ q < Q ∧ exactBackwardQuotient 1 u q ∈ hits) := by
    intro L_max Q hQ_pos
    dsimp only
    let words := allBoolWordsUpTo L_max
    let hits := boundedRayHits words Q
    rcases allBoolWordsUpTo_spec L_max with ⟨hwords_lt, hwords_mem⟩
    rcases boundedRayHits_spec words Q with ⟨hhits_len, hhits_mem⟩
    have hlen_lt : hits.length < 2 ^ (L_max + 1) * Q := by
      dsimp [hits]
      rw [hhits_len]
      exact Nat.mul_lt_mul_of_pos_right hwords_lt hQ_pos
    refine ⟨hlen_lt, ?_⟩
    intro u q hu hlen_u hsurv hlt_X
    have hw6 : parityWeight u ≥ 6 := by
      by_cases hw5 : parityWeight u ≤ 5
      · exact False.elim (one_generator_weight_le_five_never_surviving_mod373248 u q hu hw5 hsurv)
      · omega
    have hq_lt : q < Q := by
      by_cases hlt_q : q < Q
      · exact hlt_q
      · have hq_ge : Q ≤ q := by omega
        have hy_ge : 2 ^ (486 * Q) ≤ exactBackwardQuotient 1 u q :=
          Nat.le_trans
            (pow2_mono_nat (Nat.mul_le_mul_left 486 hq_ge))
            (bounded_length_ray_exponential_sparsity_and_noncovering.1 u q hu hw6)
        omega
    exact ⟨hw6, hq_lt, hhits_mem u (hwords_mem u hlen_u) q hq_lt⟩
  refine ⟨hcount, ?_⟩
  intro L_max D hD_pos
  dsimp only
  let Q := D + L_max + 2
  have hQ_ge3 : Q ≥ 3 := by dsimp [Q]; omega
  have hlt_hits := (hcount L_max Q (by omega)).1
  let hits := boundedRayHits (allBoolWordsUpTo L_max) Q
  change hits.length < 2 ^ (L_max + 1) * Q at hlt_hits
  have hD_le : D ≤ 2 ^ D := Nat.le_trans (by omega : D ≤ D + 1) (pow2_ge_succ_self D)
  have hQ_le : Q ≤ 2 ^ Q := Nat.le_trans (by omega : Q ≤ Q + 1) (pow2_ge_succ_self Q)
  have hmul1 : D * hits.length < D * (2 ^ (L_max + 1) * Q) :=
    Nat.mul_lt_mul_of_pos_left hlt_hits hD_pos
  have hmul2 : D * (2 ^ (L_max + 1) * Q) ≤ 2 ^ D * (2 ^ (L_max + 1) * 2 ^ Q) :=
    Nat.mul_le_mul hD_le (Nat.mul_le_mul_left _ hQ_le)
  have hpow_comb : 2 ^ D * (2 ^ (L_max + 1) * 2 ^ Q) = 2 ^ (D + (L_max + 1) + Q) := by
    rw [← Nat.pow_add 2 (L_max + 1) Q, ← Nat.pow_add 2 D]
    exact congrArg (fun e => 2 ^ e) (by omega)
  rw [hpow_comb] at hmul2
  have hexp_le : D + (L_max + 1) + Q ≤ 486 * Q := by dsimp [Q]; omega
  have hpow_le : 2 ^ (D + (L_max + 1) + Q) ≤ 2 ^ (486 * Q) := pow2_mono_nat hexp_le
  exact ⟨hQ_ge3, Nat.lt_of_lt_of_le hmul1 (Nat.le_trans hmul2 hpow_le)⟩

end CollatzFormal
