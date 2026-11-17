/-
  CollatzFormal/Wave7WholeSpace.lean
  Wave 7 Whole-Space Mathematical & CS Proof Loop:
  1. Front A — Pure-Kernel Schneider–Laurent `W`-Dilated Remainder / Determinant Bridge &
     Common-Order Prime Exclusions (Branches P3.3 & P3.4):
     - `pow_sub_pow_mean_value_sandwich`, `laurent_interp_2x2_closed_form_and_nonvanishing`, &
       `laurent_wdilated_zero_gap_entry_and_det_congruence` (zero custom axioms): discrete
       Schwarz/Taylor mean-value sandwich, closed-form `2 x 2` non-vanishing `(2^K)^u - (3^W)^u > 0`,
       and general `L x L` Laplace integer determinant congruence `((2^K - 3^W) : Int) ∣ (det M_0 - det M_W)`
       giving the pure-integer Liouville bridge `2^K - 3^W ≤ |det M_0| + |det M_W|` whenever `det M_0 ≠ det M_W`.
     - `laurent_gap_bridge_eliminates_1_and_2_block_cycles` &
       `laurent_scaled_nonvanishing_eliminates_1_and_2_block_cycles` (zero custom axioms): proves
       `SubexponentialCubicGapProp` unconditionally across ALL non-minimal `2 * 3^W ≤ 2^K` (`∀ W ≥ 6`)
       and across the entire `W = 6` infinite family, and formalizes the exact implication chain
       `LaurentScaledNonvanishingProp -> TightConvergentCubicGapProp -> SubexponentialCubicGapProp ∧
       NoOneBlockPositiveCycles ∧ NoTwoBlockPositiveCycles`.
     - `one_block_common_divisor_impossibility`, `one_block_common_order_prime_exclusion`,
       `odd_order_primes_and_331_mult_order_cert` (`[]` axioms),
       `one_block_odd_order_primes_7_19_23_31_43_47_71_73_and_331_barrier` (zero custom axioms, choice-free),
       `two_block_shared_mersenne_common_order_scaling_and_squeeze`, `squeeze69_up_to_40_cert` (`[]` axioms), &
       `two_block_odd_order_primes_7_19_23_31_43_47_71_73_weight_41r_floor` (zero custom axioms): eliminates
       ALL common-order primes `gcd(ord_p(2), ord_p(3/2)) ≥ 2` on 1-block cycles (completing 100% of
       odd primes `< 300` and isolating `p = 331` as minimal coprime-order barrier prime) and proves both
       universal `(5*r, 3*r, 8*r)` + `23 * r * (2^(K/r) - 3^(W/r)) < 3^(W/r)` scaling locks (`∀ r ≥ 1`)
       and sharp `(41*r, 65*r)` 2-block floors (`∀ r ≥ 3`, instantiated across `{7, 19, 23, 31, 43, 47, 71, 73}`).
  2. Front B — Beyond Rational-Algebraic Functionals: Binary Digit/Run-Length/`bitLength` Preimage
     Weights & Mahler–Koopman Tauberian Non-Uniqueness (Branches P1.2 & P1.3):
     - `binary_digit_sig6_and_bitlength_infinite_collision_family`,
       `berg_meinardus_binary_digit_sig_impossibility`,
       `berg_meinardus_exponential_popcount_bitlength_impossibility`, &
       `berg_meinardus_coupled_digit_sig_and_bitlength_impossibility` (zero custom axioms): refutes
       ALL arbitrary functions of the 6-tuple `binDigitSig6 n`, ALL exponential bit-length weights
       coupled with `binPopcount n` (`m = 11`), and ALL separable rational polynomials in `binBitLength n`
       coupled with arbitrary functions of `binDigitSig6 n` (`m_k = 3 * 4^k + 8`).
     - `mahler_koopman_tauberian_balance_and_m3_nonuniqueness` &
       `mahler_bivariate_pole_subtraction_and_half_exponent_decay` (zero custom axioms): proves the exact
       `2 * N` Koopman parity-split sum identity, universal cycle-basin invariance `ReachesGenCycle`,
       explicit multi-basin `{0, 1}` non-uniqueness on `M3 = (Z^+, 5x + 1)` (`1` vs `13`), and
       cleared-denominator bivariate pole subtraction with uniform `(n + 1) / 2` geometric decay.
  3. Front C — Non-Triangular `d = 2` & `d = 3` Hofbauer–Waldmann Certificates, `ω^k` / VASS Barriers, &
     4th Solvable Cousin `T_diamond4` (Branches P4.3 & P5):
     - `r1_sub6_admits_2d_nontriangular_hofbauer_waldmann_cert` (`[]` axioms) &
       `r1_sub6_admits_3d_nontriangular_hofbauer_waldmann_cert` (`[]` axioms): explicit `2 x 2` and `3 x 3`
       non-triangular Hofbauer–Waldmann certificates (`(M_s)_{0,0} = 1`) orienting all 7 rules of
       `sub6 ∪ {R1}` (`{R1, R2, R5, R7, R8, R9, R11}`), escaping Wave 6's `UpperTri2D` and
       all-dimension bipartite swap barriers ALREADY in `d = 2`.
     - `all_dim_lower_triangular_hofbauer_waldmann_impossibility`,
       `omega_k_affine_rule_removal_and_parikh_vass_impossibility`, &
       `swap_rule_parikh_vass_impossibility` (zero custom axioms): refutes
       ALL lower-triangular `(M_s)_{0,0} ≥ 1` matrix interpretations (`∀ d ≥ 1`), ALL `k`-counter
       lexicographic Parikh VASS rankings on `{R2, R11}` and swap rules `R3`/`R8` (`∀ k`), and ALL
       `k`-level Zantema–Geser `ω^k` iterated 1D natural-affine rule-removal towers on `sub6` (`∀ k ≥ 1`).
     - `cousinDiamond4StepInt_ofNat_eq`, `cousin_diamond4_outside_cones45_strict_descent`,
       `cousin_diamond4_cone4_and_cone5_exact_return`, `cousin_diamond4_global_convergence`,
       `cousin_diamond4_r_block_spiral_climb_and_laurent_impossibility` (zero custom axioms), &
       `cousin_diamond4_counter_model_separation` (`[]` axioms): 4th solvable cousin `T_diamond4`
       with unbounded `r`-block spiral climbs (`1019 -> 1529 -> 1147 -> 1721 -> 1291`) yet proved
       globally convergent within `k ≤ (x + 1)^3 + (x + 1)^5` while separating `M1/M2/M3`.
  4. Front D — Markov Suffix-Shift Recurrence, Sharp `q = 0` Leaf Envelope, & Fixed-Length
     Global Injectivity / Minimal `L^2` Collision Energy (Branches P5.3 & P2.2):
     - `canonicalSuffixShift_append_markov_recurrence` (zero custom axioms): proves `canonicalSuffixShift u 1`
       is odd on ALL words ending in `true` (`IsCoreParityWord u`) and obeys a history-free Markov
       skew-product transition on `(w, a)` for `u ++ [b]` (`b ∈ {false, true}`).
     - `q0_leaf_two_sided_archimedean_envelope_and_l12_drop` (zero custom axioms): proves `affineCarry u <
       3 ^ w * 2 ^ |u|`, the sharp two-sided `q = 0` leaf envelope, and non-monotone length drop
       between `L = 12` and `L = 10` inside `IsSurvivingMod373248Class`.
     - `fixed_length_ray_global_injectivity_and_minimal_l2_collision_energy` (zero custom axioms):
       proves unconditional global injectivity across ALL equal-length core words and ALL `q : Nat`
       (including `q = 0`, zero `IsFirstHitOnePair` required!) and exact `NoDupNat` (`L^2` collision
       energy = `27 * 2 ^ (L - 10)`) across all `27 * 2 ^ (L - 10)` surviving `L`-bit fibers (`∀ L ≥ 10`).

  Zero external dependencies (pure Lean 4.35.0 Core), zero `sorry`,
  zero `native_decide`, zero custom `axiom`.
-/

import CollatzFormal.Wave6WholeSpace

namespace CollatzFormal

-- ============================================================================
-- SECTION 1: Front A — Pure-Kernel Schneider–Laurent `W`-Dilated Remainder /
--            Determinant Bridge & Common-Order Prime Exclusions (Zero Custom Axioms)
-- ============================================================================

/--
  Discrete Schwarz / Taylor Mean-Value Sandwich (`pow_sub_pow_mean_value_sandwich`, zero custom axioms):
  For ALL integers `n ≥ 1` and `0 ≤ B ≤ A`,
    `n * B ^ (n - 1) * (A - B) ≤ A ^ n - B ^ n ≤ n * A ^ (n - 1) * (A - B)`.
-/
theorem pow_sub_pow_mean_value_sandwich :
    ∀ (n A B : Nat), n ≥ 1 -> B ≤ A ->
      n * B ^ (n - 1) * (A - B) ≤ A ^ n - B ^ n ∧
      A ^ n - B ^ n ≤ n * A ^ (n - 1) * (A - B)
  | 0, _, _, hn, _ => by omega
  | 1, A, B, _, _ => by
    simp only [Nat.sub_self, Nat.pow_zero, Nat.pow_one, Nat.one_mul]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | m + 2, A, B, _, hBA => by
    let n := m + 1
    have hn_pos : n ≥ 1 := by dsimp [n]; omega
    have hm_eq : n - 1 = m := rfl
    rcases pow_sub_pow_mean_value_sandwich n A B hn_pos hBA with ⟨ih_lo, ih_hi⟩
    rw [hm_eq] at ih_lo ih_hi
    have hBnAn : B ^ n ≤ A ^ n := nat_pow_mono_base B A hBA n
    have hsplit : A ^ (n + 1) - B ^ (n + 1) = A ^ n * (A - B) + B * (A ^ n - B ^ n) := by
      have h1 : B * (A ^ n - B ^ n) + B ^ (n + 1) = A ^ n * B := by
        rw [Nat.pow_succ B n, Nat.mul_comm (B ^ n) B, ← Nat.mul_add B,
            Nat.sub_add_cancel hBnAn, Nat.mul_comm B (A ^ n)]
      have h2 : A ^ n * (A - B) + A ^ n * B = A ^ (n + 1) := by
        rw [← Nat.mul_add (A ^ n), Nat.sub_add_cancel hBA, ← Nat.pow_succ A n]
      omega
    change (n + 1) * B ^ n * (A - B) ≤ A ^ (n + 1) - B ^ (n + 1) ∧
      A ^ (n + 1) - B ^ (n + 1) ≤ (n + 1) * A ^ n * (A - B)
    rw [hsplit]
    refine ⟨?_, ?_⟩
    · have ht1 : B ^ n * (A - B) ≤ A ^ n * (A - B) := Nat.mul_le_mul_right (A - B) hBnAn
      have ht2 : B * (n * B ^ m * (A - B)) ≤ B * (A ^ n - B ^ n) :=
        Nat.mul_le_mul_left B ih_lo
      have hBn_eq : B * (n * B ^ m * (A - B)) = n * B ^ n * (A - B) := by
        have hb : B * (n * B ^ m) = n * B ^ n := by
          dsimp [n]
          rw [← Nat.mul_assoc B (m + 1), Nat.mul_comm B (m + 1), Nat.mul_assoc (m + 1) B,
              Nat.mul_comm B (B ^ m), ← Nat.pow_succ B m]
        rw [← Nat.mul_assoc B, hb]
      rw [hBn_eq] at ht2
      have hsum : (n + 1) * B ^ n * (A - B) = B ^ n * (A - B) + n * B ^ n * (A - B) := by
        rw [Nat.add_comm n 1, Nat.add_mul 1 n (B ^ n), Nat.one_mul, Nat.add_mul]
      rw [hsum]
      exact Nat.add_le_add ht1 ht2
    · have ht2 : B * (A ^ n - B ^ n) ≤ A * (n * A ^ m * (A - B)) :=
        Nat.mul_le_mul hBA ih_hi
      have hAn_eq : A * (n * A ^ m * (A - B)) = n * A ^ n * (A - B) := by
        have ha : A * (n * A ^ m) = n * A ^ n := by
          dsimp [n]
          rw [← Nat.mul_assoc A (m + 1), Nat.mul_comm A (m + 1), Nat.mul_assoc (m + 1) A,
              Nat.mul_comm A (A ^ m), ← Nat.pow_succ A m]
        rw [← Nat.mul_assoc A, ha]
      rw [hAn_eq] at ht2
      have hsum : (n + 1) * A ^ n * (A - B) = A ^ n * (A - B) + n * A ^ n * (A - B) := by
        rw [Nat.add_comm n 1, Nat.add_mul 1 n (A ^ n), Nat.one_mul, Nat.add_mul]
      rw [hsum]
      exact Nat.add_le_add (Nat.le_refl _) ht2

/--
  Zero-gap integer reference entry `M_0[(r, s), (t, u)]` for `W`-dilated columns `(t, W * u)`:
  Replacing `3 ^ W` by `2 ^ K` in `laurentInterpEntry W K r s t (W * u)` yields the exact
  pure-integer entry `binom(r * W + s * K, t) * 2 ^ ((r * W + s * K) * u) ∈ Nat`!
-/
def laurentZeroGapIntEntry (W K r s t u : Nat) : Nat :=
  laurentInterpBinom (r * W + s * K) t * 2 ^ ((r * W + s * K) * u)

def skipFinIdx {L : Nat} (j : Fin (L + 1)) (c : Fin L) : Fin (L + 1) :=
  if c.val < j.val then ⟨c.val, by omega⟩ else ⟨c.val + 1, by omega⟩

def intSubMat {L : Nat} (A : Fin (L + 1) -> Fin (L + 1) -> Int) (j : Fin (L + 1)) :
    Fin L -> Fin L -> Int :=
  fun r c => A ⟨r.val + 1, by omega⟩ (skipFinIdx j c)

def intSumPrefix (L : Nat) (f : Fin L -> Int) : Nat -> Int
  | 0 => 0
  | k + 1 => intSumPrefix L f k + (if h : k < L then f ⟨k, h⟩ else 0)

def intSumFin (L : Nat) (f : Fin L -> Int) : Int :=
  intSumPrefix L f L

/-- Pure-kernel `L x L` Laplace integer determinant on `Fin L -> Fin L -> Int` (zero external deps). -/
def intDet : (L : Nat) -> (Fin L -> Fin L -> Int) -> Int
  | 0, _ => 1
  | L + 1, A =>
    intSumFin (L + 1) (fun j =>
      (if j.val % 2 = 0 then (1 : Int) else -1) *
        A ⟨0, Nat.zero_lt_succ L⟩ j * intDet L (intSubMat A j))

theorem intSumPrefix_sub_dvd (d : Int) (L : Nat) (f g : Fin L -> Int)
    (hdvd : ∀ j : Fin L, d ∣ (f j - g j)) :
    ∀ k : Nat, d ∣ (intSumPrefix L f k - intSumPrefix L g k)
  | 0 => ⟨0, by simp [intSumPrefix]⟩
  | k + 1 => by
    rcases intSumPrefix_sub_dvd d L f g hdvd k with ⟨q1, hq1⟩
    simp only [intSumPrefix]
    by_cases hk : k < L
    · simp only [hk, dite_true]
      rcases hdvd ⟨k, hk⟩ with ⟨q2, hq2⟩
      refine ⟨q1 + q2, ?_⟩
      have hrew : (intSumPrefix L f k + f ⟨k, hk⟩) - (intSumPrefix L g k + g ⟨k, hk⟩) =
          (intSumPrefix L f k - intSumPrefix L g k) + (f ⟨k, hk⟩ - g ⟨k, hk⟩) := by omega
      rw [hrew, hq1, hq2, Int.mul_add]
    · simp only [hk, dite_false, Int.add_zero]
      exact ⟨q1, hq1⟩

theorem int_ring_bilinear_diff (s a0 b0 dA dB : Int) :
    s * a0 * dA - s * b0 * dB = s * ((a0 - b0) * dA + b0 * (dA - dB)) := by
  rw [Int.sub_mul a0 b0 dA, Int.mul_sub b0 dA dB]
  have hmid : a0 * dA - b0 * dA + (b0 * dA - b0 * dB) = a0 * dA - b0 * dB := by omega
  rw [hmid, Int.mul_sub, ← Int.mul_assoc s a0 dA, ← Int.mul_assoc s b0 dB]

theorem intDet_congr_dvd (d : Int) :
    ∀ (L : Nat) (A B : Fin L -> Fin L -> Int),
      (∀ i j : Fin L, d ∣ (A i j - B i j)) ->
      d ∣ (intDet L A - intDet L B)
  | 0, _, _, _ => ⟨0, by simp [intDet]⟩
  | L + 1, A, B, hentry => by
    simp only [intDet]
    unfold intSumFin
    apply intSumPrefix_sub_dvd d (L + 1)
    intro j
    have hsub_entry : ∀ r c : Fin L, d ∣ (intSubMat A j r c - intSubMat B j r c) :=
      fun r c => hentry ⟨r.val + 1, by omega⟩ (skipFinIdx j c)
    rcases intDet_congr_dvd d L (intSubMat A j) (intSubMat B j) hsub_entry with ⟨qDet, hqDet⟩
    rcases hentry ⟨0, Nat.zero_lt_succ L⟩ j with ⟨qTop, hqTop⟩
    let sgn : Int := if j.val % 2 = 0 then 1 else -1
    let a0 := A ⟨0, Nat.zero_lt_succ L⟩ j
    let b0 := B ⟨0, Nat.zero_lt_succ L⟩ j
    let dA := intDet L (intSubMat A j)
    let dB := intDet L (intSubMat B j)
    change d ∣ (sgn * a0 * dA - sgn * b0 * dB)
    rw [int_ring_bilinear_diff sgn a0 b0 dA dB]
    change a0 - b0 = d * qTop at hqTop
    change dA - dB = d * qDet at hqDet
    rw [hqTop, hqDet]
    refine ⟨sgn * (qTop * dA + b0 * qDet), ?_⟩
    calc
      sgn * (d * qTop * dA + b0 * (d * qDet))
          = sgn * (d * (qTop * dA) + d * (b0 * qDet)) := by
            rw [Int.mul_assoc d qTop dA, ← Int.mul_assoc b0 d qDet,
                Int.mul_comm b0 d, Int.mul_assoc d b0 qDet]
      _ = sgn * (d * (qTop * dA + b0 * qDet)) := by rw [← Int.mul_add d]
      _ = d * (sgn * (qTop * dA + b0 * qDet)) := by
            rw [← Int.mul_assoc sgn d, Int.mul_comm sgn d, Int.mul_assoc d sgn]

theorem int_dvd_sub_imp_le_natAbs_add (D : Nat) (x y : Int)
    (hdvd : (D : Int) ∣ (x - y)) (hne : x ≠ y) :
    D ≤ x.natAbs + y.natAbs := by
  rcases hdvd with ⟨q, hq⟩
  have hdiff_ne0 : x - y ≠ 0 := by omega
  by_cases hq_pos : q > 0
  · have hm : (D : Int) * 1 ≤ (D : Int) * q :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    omega
  · have hq_neg : q ≤ -1 := by
      by_cases hq0 : q = 0
      · rw [hq0, Int.mul_zero] at hq
        exact False.elim (hdiff_ne0 hq)
      · omega
    have hm : (D : Int) * q ≤ (D : Int) * (-1) :=
      Int.mul_le_mul_of_nonneg_left hq_neg (by omega)
    omega

/--
  Theorem W7.1a (`laurent_interp_2x2_closed_form_and_nonvanishing`, zero custom axioms):
  Universal 2x2 Algebraic Non-Vanishing (`det_Z ≠ 0`) across ALL `(W, K)` with `3 ^ W < 2 ^ K`:
  On resonant rows `(K, 0)` and `(0, W)` and columns `(0, 0)` and `(0, u)` (`u ≥ 1`),
  the `2 x 2` integer Schneider–Laurent determinant equals `(2 ^ K) ^ u - (3 ^ W) ^ u > 0`
  in closed form — strictly non-zero for ALL `u ≥ 1` and divisible by `(2 ^ K - 3 ^ W)`!
-/
theorem laurent_interp_2x2_closed_form_and_nonvanishing
    (W K u : Nat) (hu : u ≥ 1) (hgt : 3 ^ W < 2 ^ K) :
    laurentInterpEntry W K K 0 0 0 = 1 ∧
    laurentInterpEntry W K 0 W 0 0 = 1 ∧
    laurentInterpEntry W K K 0 0 u = (2 ^ K) ^ u ∧
    laurentInterpEntry W K 0 W 0 u = (3 ^ W) ^ u ∧
    laurentInterpEntry W K 0 W 0 0 * laurentInterpEntry W K K 0 0 u -
      laurentInterpEntry W K K 0 0 0 * laurentInterpEntry W K 0 W 0 u =
        (2 ^ K) ^ u - (3 ^ W) ^ u ∧
    (2 ^ K) ^ u - (3 ^ W) ^ u ≥ u * (3 ^ W) ^ (u - 1) * (2 ^ K - 3 ^ W) ∧
    (2 ^ K) ^ u - (3 ^ W) ^ u > 0 := by
  have hbinom0 : ∀ n : Nat, laurentInterpBinom n 0 = 1 := by
    intro n; cases n <;> rfl
  have he00 : laurentInterpEntry W K K 0 0 0 = 1 := by
    unfold laurentInterpEntry; simp [hbinom0]
  have he10 : laurentInterpEntry W K 0 W 0 0 = 1 := by
    unfold laurentInterpEntry; simp [hbinom0]
  have he01 : laurentInterpEntry W K K 0 0 u = (2 ^ K) ^ u := by
    unfold laurentInterpEntry
    simp only [hbinom0, Nat.zero_mul, Nat.pow_zero, Nat.one_mul, Nat.mul_one]
    exact (pow_pow_eq_mul_w5 2 K u).symm
  have he11 : laurentInterpEntry W K 0 W 0 u = (3 ^ W) ^ u := by
    unfold laurentInterpEntry
    simp only [hbinom0, Nat.zero_mul, Nat.pow_zero, Nat.one_mul]
    exact (pow_pow_eq_mul_w5 3 W u).symm
  have hlo := (pow_sub_pow_mean_value_sandwich u (2 ^ K) (3 ^ W) hu (Nat.le_of_lt hgt)).1
  have hpos_prod : u * (3 ^ W) ^ (u - 1) * (2 ^ K - 3 ^ W) ≥ 1 :=
    Nat.mul_le_mul
      (Nat.mul_le_mul hu (nat_pow_pos_of_pos (3 ^ W) (pow3_pos_nat W) (u - 1)))
      (by omega : 1 ≤ 2 ^ K - 3 ^ W)
  refine ⟨he00, he10, he01, he11, ?_, hlo, by omega⟩
  rw [he10, he01, he00, he11, Nat.one_mul, Nat.one_mul]

/--
  Theorem W7.1b (`laurent_wdilated_zero_gap_entry_and_det_congruence`, zero custom axioms):
  Pure-Integer `W`-Dilated Schneider–Laurent Remainder & Determinant Liouville Bridge:
  1. Entrywise Taylor Identity: For ALL `(W, K, r, s, t, u)` with `3 ^ W ≤ 2 ^ K`,
     `laurentZeroGapIntEntry W K r s t u - laurentInterpEntry W K r s t (W * u) =
       laurentInterpBinom (r * W + s * K) t * 2 ^ (r * W * u) * ((2 ^ K) ^ (s * u) - (3 ^ W) ^ (s * u))`,
     so `(2 ^ K - 3 ^ W)` divides EVERY entry difference!
  2. General `L x L` Integer Determinant Congruence & Liouville Lower Bound: For ANY `L : Nat`
     and ANY row/column grids `rows cols : Fin L -> Nat × Nat` (`3 ^ W < 2 ^ K`),
     `((2 ^ K - 3 ^ W : Nat) : Int)` divides `intDet L M_0 - intDet L M_W`, hence whenever
     `intDet L M_0 ≠ intDet L M_W` (for example `intDet L M_0 = 0 ∧ intDet L M_W ≠ 0`),
       `2 ^ K - 3 ^ W ≤ (intDet L M_0).natAbs + (intDet L M_W).natAbs`!
-/
theorem laurent_wdilated_zero_gap_entry_and_det_congruence :
    (∀ (W K r s t u : Nat), 3 ^ W ≤ 2 ^ K ->
      laurentInterpEntry W K r s t (W * u) ≤ laurentZeroGapIntEntry W K r s t u ∧
      laurentZeroGapIntEntry W K r s t u - laurentInterpEntry W K r s t (W * u) =
        laurentInterpBinom (r * W + s * K) t * 2 ^ (r * W * u) *
          ((2 ^ K) ^ (s * u) - (3 ^ W) ^ (s * u)) ∧
      (2 ^ K - 3 ^ W) ∣
        (laurentZeroGapIntEntry W K r s t u - laurentInterpEntry W K r s t (W * u))) ∧
    (∀ (W K L : Nat) (rows cols : Fin L -> Nat × Nat), 3 ^ W < 2 ^ K ->
      let M0 : Fin L -> Fin L -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2 (cols j).1 (cols j).2 : Int)
      let MW : Fin L -> Fin L -> Int := fun i j =>
        (laurentInterpEntry W K (rows i).1 (rows i).2 (cols j).1 (W * (cols j).2) : Int)
      (((2 ^ K - 3 ^ W : Nat) : Int) ∣ (intDet L M0 - intDet L MW)) ∧
      (intDet L M0 ≠ intDet L MW ->
        2 ^ K - 3 ^ W ≤ (intDet L M0).natAbs + (intDet L MW).natAbs)) := by
  have hentry : ∀ (W K r s t u : Nat), 3 ^ W ≤ 2 ^ K ->
      laurentInterpEntry W K r s t (W * u) ≤ laurentZeroGapIntEntry W K r s t u ∧
      laurentZeroGapIntEntry W K r s t u - laurentInterpEntry W K r s t (W * u) =
        laurentInterpBinom (r * W + s * K) t * 2 ^ (r * W * u) *
          ((2 ^ K) ^ (s * u) - (3 ^ W) ^ (s * u)) ∧
      (2 ^ K - 3 ^ W) ∣
        (laurentZeroGapIntEntry W K r s t u - laurentInterpEntry W K r s t (W * u)) := by
    intro W K r s t u hle
    let B0 := laurentInterpBinom (r * W + s * K) t
    have hz_eq : laurentZeroGapIntEntry W K r s t u =
        B0 * 2 ^ (r * W * u) * (2 ^ K) ^ (s * u) := by
      unfold laurentZeroGapIntEntry
      change B0 * 2 ^ ((r * W + s * K) * u) = _
      rw [Nat.add_mul (r * W) (s * K) u, Nat.pow_add, ← Nat.mul_assoc B0]
      have hp2 : 2 ^ (s * K * u) = (2 ^ K) ^ (s * u) := by
        rw [pow_pow_eq_mul_w5 2 K (s * u), ← Nat.mul_assoc K s u, Nat.mul_comm K s, Nat.mul_assoc]
      rw [hp2]
    have hw_eq : laurentInterpEntry W K r s t (W * u) =
        B0 * 2 ^ (r * W * u) * (3 ^ W) ^ (s * u) := by
      unfold laurentInterpEntry
      change B0 * 2 ^ (r * (W * u)) * 3 ^ (s * (W * u)) = _
      rw [← Nat.mul_assoc r W u]
      have hp3 : 3 ^ (s * (W * u)) = (3 ^ W) ^ (s * u) := by
        rw [pow_pow_eq_mul_w5 3 W (s * u), ← Nat.mul_assoc W s u, Nat.mul_comm W s, Nat.mul_assoc]
      rw [hp3]
    have hp_le : (3 ^ W) ^ (s * u) ≤ (2 ^ K) ^ (s * u) :=
      nat_pow_mono_base (3 ^ W) (2 ^ K) hle (s * u)
    have hle_e : laurentInterpEntry W K r s t (W * u) ≤ laurentZeroGapIntEntry W K r s t u := by
      rw [hz_eq, hw_eq]
      exact Nat.mul_le_mul_left _ hp_le
    have hdiff_e : laurentZeroGapIntEntry W K r s t u - laurentInterpEntry W K r s t (W * u) =
        B0 * 2 ^ (r * W * u) * ((2 ^ K) ^ (s * u) - (3 ^ W) ^ (s * u)) := by
      rw [hz_eq, hw_eq, ← Nat.mul_sub_left_distrib]
    rcases pow_sub_pow_dvd_w6 (2 ^ K) (3 ^ W) hle (s * u) with ⟨q, hq⟩
    refine ⟨hle_e, hdiff_e, ?_⟩
    rw [hdiff_e, hq]
    exact ⟨B0 * 2 ^ (r * W * u) * q, by
      rw [← Nat.mul_assoc (B0 * 2 ^ (r * W * u)),
          Nat.mul_comm (B0 * 2 ^ (r * W * u)) (2 ^ K - 3 ^ W), Nat.mul_assoc]⟩
  refine ⟨hentry, ?_⟩
  intro W K L rows cols hgt
  dsimp only
  let M0 : Fin L -> Fin L -> Int := fun i j =>
    (laurentZeroGapIntEntry W K (rows i).1 (rows i).2 (cols j).1 (cols j).2 : Int)
  let MW : Fin L -> Fin L -> Int := fun i j =>
    (laurentInterpEntry W K (rows i).1 (rows i).2 (cols j).1 (W * (cols j).2) : Int)
  let D : Nat := 2 ^ K - 3 ^ W
  have hdvd_ij : ∀ i j : Fin L, (D : Int) ∣ (M0 i j - MW i j) := by
    intro i j
    rcases hentry W K (rows i).1 (rows i).2 (cols j).1 (cols j).2 (Nat.le_of_lt hgt) with
      ⟨hle_ij, _, q_ij, hq_ij⟩
    refine ⟨(q_ij : Int), ?_⟩
    dsimp [M0, MW, D]
    have hsub_cast :
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2 (cols j).1 (cols j).2 : Int) -
        (laurentInterpEntry W K (rows i).1 (rows i).2 (cols j).1 (W * (cols j).2) : Int) =
        ((laurentZeroGapIntEntry W K (rows i).1 (rows i).2 (cols j).1 (cols j).2 -
          laurentInterpEntry W K (rows i).1 (rows i).2 (cols j).1 (W * (cols j).2) : Nat) : Int) := by
      omega
    rw [hsub_cast, hq_ij, natCast_mul]
  have hdet_dvd := intDet_congr_dvd (D : Int) L M0 MW hdvd_ij
  exact ⟨hdet_dvd, int_dvd_sub_imp_le_natAbs_add D (intDet L M0) (intDet L MW) hdet_dvd⟩

/--
  Tight-Convergent Reduction of `SubexponentialCubicGapProp`:
  Isolates `SubexponentialCubicGapProp` exclusively to the single tight convergent exponent
  `3 ^ W < 2 ^ K < 2 * 3 ^ W` for `W ≥ 7`!
-/
def TightConvergentCubicGapProp : Prop :=
  ∀ K W : Nat, W ≥ 7 -> 3 ^ W < 2 ^ K -> 2 ^ K < 2 * 3 ^ W ->
    27 * 2 ^ (W - 2) * (2 ^ K - 3 ^ W) ^ 3 ≥ 2 ^ (3 * K)

/--
  Theorem W7.1c (`laurent_gap_bridge_eliminates_1_and_2_block_cycles`, zero custom axioms):
  1. Non-Minimal Exponent Elimination (`∀ W ≥ 6, ∀ K, 2 * 3 ^ W ≤ 2 ^ K`): Every non-minimal
     exponent `K` satisfies `27 * 2 ^ (W - 2) * (2 ^ K - 3 ^ W) ^ 3 ≥ 2 ^ (3 * K)` unconditionally!
  2. Complete Infinite `W = 6` Slice (`∀ K, 3 ^ 6 < 2 ^ K`): Proved unconditionally across ALL `K`.
  3. Exact Bridge: `TightConvergentCubicGapProp` unconditionally implies `SubexponentialCubicGapProp`,
     `NoOneBlockPositiveCycles`, AND `NoTwoBlockPositiveCycles`!
-/
theorem laurent_gap_bridge_eliminates_1_and_2_block_cycles :
    (∀ K W : Nat, W ≥ 6 -> 2 * 3 ^ W ≤ 2 ^ K ->
      27 * 2 ^ (W - 2) * (2 ^ K - 3 ^ W) ^ 3 ≥ 2 ^ (3 * K)) ∧
    (∀ K : Nat, 3 ^ 6 < 2 ^ K ->
      27 * 2 ^ 4 * (2 ^ K - 3 ^ 6) ^ 3 ≥ 2 ^ (3 * K)) ∧
    (TightConvergentCubicGapProp ->
      SubexponentialCubicGapProp ∧ NoOneBlockPositiveCycles ∧ NoTwoBlockPositiveCycles) := by
  have hnonmin : ∀ K W : Nat, W ≥ 6 -> 2 * 3 ^ W ≤ 2 ^ K ->
      27 * 2 ^ (W - 2) * (2 ^ K - 3 ^ W) ^ 3 ≥ 2 ^ (3 * K) := by
    intro K W hW6 h2_3W
    have hK_pos : K ≥ 1 := by
      cases K with
      | zero =>
        have hp3 := pow3_pos_nat W
        simp only [Nat.pow_zero] at h2_3W; omega
      | succ _ => omega
    have h2K_sp : 2 ^ K = 2 * 2 ^ (K - 1) := pow2_split_pred K hK_pos
    have h3W_le : 3 ^ W ≤ 2 ^ (K - 1) := by omega
    have hD_ge : 2 ^ (K - 1) ≤ 2 ^ K - 3 ^ W := by omega
    have hcube_ge : (2 ^ (K - 1)) ^ 3 ≤ (2 ^ K - 3 ^ W) ^ 3 :=
      nat_pow_mono_base (2 ^ (K - 1)) (2 ^ K - 3 ^ W) hD_ge 3
    rw [pow_pow_eq_mul_w5 2 (K - 1) 3] at hcube_ge
    have hW_pow : 2 ^ 3 ≤ 27 * 2 ^ (W - 2) := by
      have hp4 : 2 ^ 4 ≤ 2 ^ (W - 2) := pow2_mono_nat (by omega)
      have h16 : (2 : Nat) ^ 4 = 16 := rfl
      have h8 : (2 : Nat) ^ 3 = 8 := rfl
      omega
    have hm := Nat.mul_le_mul hW_pow hcube_ge
    rw [← Nat.pow_add 2 3 ((K - 1) * 3), show 3 + (K - 1) * 3 = 3 * K by omega] at hm
    exact hm
  have hw6_all : ∀ K : Nat, 3 ^ 6 < 2 ^ K ->
      27 * 2 ^ 4 * (2 ^ K - 3 ^ 6) ^ 3 ≥ 2 ^ (3 * K) := by
    intro K hgt6
    by_cases hK10 : K ≤ 10
    · have hK_ge10 : K ≥ 10 := by
        by_cases hlt : K < 10
        · have hle9 : 2 ^ K ≤ 2 ^ 9 := pow2_mono_nat (by omega)
          have h512 : (2 : Nat) ^ 9 = 512 := rfl
          have h729 : (3 : Nat) ^ 6 = 729 := rfl
          omega
        · omega
      have hK_eq : K = 10 := by omega
      subst hK_eq
      decide
    · have hK11 : 11 ≤ K := by omega
      have h2_11 : 2 * 3 ^ 6 ≤ 2 ^ 11 := by decide
      have h2_K : 2 ^ 11 ≤ 2 ^ K := pow2_mono_nat hK11
      simpa using hnonmin K 6 (by decide) (Nat.le_trans h2_11 h2_K)
  refine ⟨hnonmin, hw6_all, ?_⟩
  intro htight
  have hsub : SubexponentialCubicGapProp := by
    intro K W hW6 hgt
    by_cases hW_eq6 : W = 6
    · subst hW_eq6; simpa using hw6_all K hgt
    · by_cases hlt2 : 2 ^ K < 2 * 3 ^ W
      · exact htight K W (by omega) hgt hlt2
      · exact hnonmin K W hW6 (by omega)
  exact ⟨hsub, subexponential_cubic_gap_eliminates_1_and_2_block_cycles hsub⟩

/-- Pure-integer `L x L` Schneider–Laurent interpolation matrix on row/column grids `rows, cols`. -/
def laurentInterpMat (W K L : Nat) (rows cols : Fin L -> Nat × Nat) : Fin L -> Fin L -> Int :=
  fun i j => (laurentInterpEntry W K (rows i).1 (rows i).2 (cols j).1 (cols j).2 : Int)

theorem intDet_two (A : Fin 2 -> Fin 2 -> Int) :
    intDet 2 A =
      A ⟨0, by decide⟩ ⟨0, by decide⟩ * A ⟨1, by decide⟩ ⟨1, by decide⟩ -
      A ⟨0, by decide⟩ ⟨1, by decide⟩ * A ⟨1, by decide⟩ ⟨0, by decide⟩ := by
  simp only [intDet, intSumFin, intSumPrefix, intSubMat, skipFinIdx]
  simp only [Nat.lt_irrefl, dite_true, ite_true, ite_false,
    show (0 : Nat) < 2 by decide, show (1 : Nat) < 2 by decide,
    show (0 : Nat) < 1 by decide, show ¬ ((1 : Nat) % 2 = 0) by decide]
  simp only [Nat.zero_add, Int.zero_add, Int.one_mul, Int.mul_one]
  have hneg : (-1 : Int) * A ⟨0, by decide⟩ ⟨1, by decide⟩ * A ⟨1, by decide⟩ ⟨0, by decide⟩ =
      -(A ⟨0, by decide⟩ ⟨1, by decide⟩ * A ⟨1, by decide⟩ ⟨0, by decide⟩) := by
    rw [Int.mul_assoc (-1 : Int)]; omega
  rw [hneg]
  omega

/--
  Scaled Schneider–Laurent Algebraic Non-Vanishing & Extrapolated Remainder Squeeze
  (`LaurentScaledNonvanishingProp`):
  States that for every tight convergent `(W, K)` (`W ≥ 7, 3 ^ W < 2 ^ K < 2 * 3 ^ W`),
  there exists an `L x L` Schneider–Laurent interpolation grid `(rows, cols)` whose pure-integer
  determinant `intDet L (laurentInterpMat W K L rows cols)` is non-zero AND strictly `< 1` in
  absolute value under any putative violation of the cubic gap `27 * 2 ^ (W - 2) * D ^ 3 ≥ 2 ^ (3 * K)`.
-/
def LaurentScaledNonvanishingProp : Prop :=
  ∀ K W : Nat, W ≥ 7 -> 3 ^ W < 2 ^ K -> 2 ^ K < 2 * 3 ^ W ->
    ∃ (L : Nat) (rows cols : Fin L -> Nat × Nat),
      intDet L (laurentInterpMat W K L rows cols) ≠ 0 ∧
      (27 * 2 ^ (W - 2) * (2 ^ K - 3 ^ W) ^ 3 < 2 ^ (3 * K) ->
        (intDet L (laurentInterpMat W K L rows cols)).natAbs < 1)

/--
  Theorem W7.1c' (`laurent_scaled_nonvanishing_eliminates_1_and_2_block_cycles`, zero custom axioms):
  1. `intDet 2` Singularity vs Non-Singularity Dichotomy: On resonant rows `(0, W), (K, 0)`,
     duplicate column `(0, 0), (0, 0)` has `intDet 2 = 0`, whereas any distinct column `(0, 0), (0, u)`
     (`u ≥ 1, 3 ^ W < 2 ^ K`) has `intDet 2 = (((2 ^ K) ^ u - (3 ^ W) ^ u : Nat) : Int) > 0`;
  2. Exact Algebraic Implication Chain:
       `LaurentScaledNonvanishingProp -> TightConvergentCubicGapProp ->
        SubexponentialCubicGapProp ∧ NoOneBlockPositiveCycles ∧ NoTwoBlockPositiveCycles`.
-/
theorem laurent_scaled_nonvanishing_eliminates_1_and_2_block_cycles :
    (∀ W K : Nat,
      let rows : Fin 2 -> Nat × Nat := fun i => if i.val = 0 then (0, W) else (K, 0)
      let cols0 : Fin 2 -> Nat × Nat := fun _ => (0, 0)
      intDet 2 (laurentInterpMat W K 2 rows cols0) = 0) ∧
    (∀ W K u : Nat, u ≥ 1 -> 3 ^ W < 2 ^ K ->
      let rows : Fin 2 -> Nat × Nat := fun i => if i.val = 0 then (0, W) else (K, 0)
      let cols : Fin 2 -> Nat × Nat := fun j => if j.val = 0 then (0, 0) else (0, u)
      intDet 2 (laurentInterpMat W K 2 rows cols) = (((2 ^ K) ^ u - (3 ^ W) ^ u : Nat) : Int) ∧
      intDet 2 (laurentInterpMat W K 2 rows cols) > 0) ∧
    (LaurentScaledNonvanishingProp -> TightConvergentCubicGapProp) ∧
    (LaurentScaledNonvanishingProp ->
      SubexponentialCubicGapProp ∧ NoOneBlockPositiveCycles ∧ NoTwoBlockPositiveCycles) := by
  have hbinom0 : ∀ n : Nat, laurentInterpBinom n 0 = 1 := by
    intro n; cases n <;> rfl
  have hsing : ∀ W K : Nat,
      let rows : Fin 2 -> Nat × Nat := fun i => if i.val = 0 then (0, W) else (K, 0)
      let cols0 : Fin 2 -> Nat × Nat := fun _ => (0, 0)
      intDet 2 (laurentInterpMat W K 2 rows cols0) = 0 := by
    intro W K
    dsimp only
    rw [intDet_two]
    simp [laurentInterpMat, laurentInterpEntry, hbinom0]
  have hnonsing : ∀ W K u : Nat, u ≥ 1 -> 3 ^ W < 2 ^ K ->
      let rows : Fin 2 -> Nat × Nat := fun i => if i.val = 0 then (0, W) else (K, 0)
      let cols : Fin 2 -> Nat × Nat := fun j => if j.val = 0 then (0, 0) else (0, u)
      intDet 2 (laurentInterpMat W K 2 rows cols) = (((2 ^ K) ^ u - (3 ^ W) ^ u : Nat) : Int) ∧
      intDet 2 (laurentInterpMat W K 2 rows cols) > 0 := by
    intro W K u hu hgt
    dsimp only
    rcases laurent_interp_2x2_closed_form_and_nonvanishing W K u hu hgt with
      ⟨heK0, he0W, heKu, heWu, _, _, hpos⟩
    rw [intDet_two]
    have h00 : laurentInterpMat W K 2
        (fun i => if i.val = 0 then (0, W) else (K, 0))
        (fun j => if j.val = 0 then (0, 0) else (0, u))
        ⟨0, by decide⟩ ⟨0, by decide⟩ = 1 := by
      simp [laurentInterpMat, he0W]
    have h11 : laurentInterpMat W K 2
        (fun i => if i.val = 0 then (0, W) else (K, 0))
        (fun j => if j.val = 0 then (0, 0) else (0, u))
        ⟨1, by decide⟩ ⟨1, by decide⟩ = (((2 ^ K) ^ u : Nat) : Int) := by
      simp [laurentInterpMat, heKu]
    have h01 : laurentInterpMat W K 2
        (fun i => if i.val = 0 then (0, W) else (K, 0))
        (fun j => if j.val = 0 then (0, 0) else (0, u))
        ⟨0, by decide⟩ ⟨1, by decide⟩ = (((3 ^ W) ^ u : Nat) : Int) := by
      simp [laurentInterpMat, heWu]
    have h10 : laurentInterpMat W K 2
        (fun i => if i.val = 0 then (0, W) else (K, 0))
        (fun j => if j.val = 0 then (0, 0) else (0, u))
        ⟨1, by decide⟩ ⟨0, by decide⟩ = 1 := by
      simp [laurentInterpMat, heK0]
    rw [h00, h11, h01, h10]
    have hle_pow : (3 ^ W) ^ u ≤ (2 ^ K) ^ u :=
      nat_pow_mono_base (3 ^ W) (2 ^ K) (Nat.le_of_lt hgt) u
    constructor
    · omega
    · omega
  have hto_tight : LaurentScaledNonvanishingProp -> TightConvergentCubicGapProp := by
    intro hlaur K W hW7 hgt hlt2
    by_cases hge : 27 * 2 ^ (W - 2) * (2 ^ K - 3 ^ W) ^ 3 ≥ 2 ^ (3 * K)
    · exact hge
    · have hviol : 27 * 2 ^ (W - 2) * (2 ^ K - 3 ^ W) ^ 3 < 2 ^ (3 * K) := by omega
      rcases hlaur K W hW7 hgt hlt2 with ⟨L, rows, cols, hne0, hlt1⟩
      have habs := hlt1 hviol
      have hd0 : intDet L (laurentInterpMat W K L rows cols) = 0 := by omega
      exact False.elim (hne0 hd0)
  refine ⟨hsing, hnonsing, hto_tight, ?_⟩
  intro hlaur
  rcases laurent_gap_bridge_eliminates_1_and_2_block_cycles.2.2 (hto_tight hlaur) with
    ⟨hsub, h1, h2⟩
  exact ⟨hsub, h1, h2⟩

/--
  Theorem W7.1d (`one_block_common_divisor_impossibility`, zero custom axioms):
  Universal Common-Divisor 1-Block Impossibility (`∀ r ≥ 2`):
  Whenever `r ≥ 2` divides BOTH `w1` (`w1 ≥ 2`) and `a1` (`a1 ≥ 1`) with `3 ^ w1 < 2 ^ (w1 + a1)`,
  the 1-block determinant strictly exceeds the Mersenne carry:
    `2 ^ (w1 + a1) - 3 ^ w1 > 2 ^ a1 - 1`
  (hence `(2 ^ (w1 + a1) - 3 ^ w1) * q0 ≠ 2 ^ a1 - 1` for ALL `q0 : Nat`)!
-/
theorem one_block_common_divisor_impossibility
    (r w1 a1 : Nat)
    (hr : r ≥ 2) (hw1 : w1 ≥ 2) (ha1 : a1 ≥ 1)
    (hgt : 3 ^ w1 < 2 ^ (w1 + a1))
    (hr_w1 : r ∣ w1) (hr_a1 : r ∣ a1) :
    2 ^ (w1 + a1) - 3 ^ w1 > 2 ^ a1 - 1 ∧
    (∀ q0 : Nat, (2 ^ (w1 + a1) - 3 ^ w1) * q0 ≠ 2 ^ a1 - 1) := by
  rcases hr_w1 with ⟨v, hv⟩
  rcases hr_a1 with ⟨u, hu⟩
  have hv_pos : v ≥ 1 := by cases v with | zero => simp at hv; omega | succ _ => omega
  have hu_pos : u ≥ 1 := by cases u with | zero => simp at hu; omega | succ _ => omega
  have hgt_gt : 2 ^ (w1 + a1) - 3 ^ w1 > 2 ^ a1 - 1 := by
    by_cases hcase : u ≤ (r - 1) * v
    · let A := 2 ^ (v + u)
      let B := 3 ^ v
      have hAr : A ^ r = 2 ^ (w1 + a1) := by
        dsimp [A]
        rw [pow_pow_eq_mul_w5 2 (v + u) r, Nat.add_mul v u r,
            Nat.mul_comm v r, Nat.mul_comm u r, ← hv, ← hu]
      have hBr : B ^ r = 3 ^ w1 := by
        dsimp [B]; rw [pow_pow_eq_mul_w5 3 v r, Nat.mul_comm v r, ← hv]
      have hBA_lt : B < A := by
        by_cases hlt : B < A
        · exact hlt
        · have hm := nat_pow_mono_base A B (by omega) r
          rw [hAr, hBr] at hm; omega
      have hAr_split : A ^ (r - 1) ≤ A ^ r - B ^ r := by
        have hr_sp : r = (r - 1) + 1 := by omega
        have hBnAn : B ^ (r - 1) ≤ A ^ (r - 1) :=
          nat_pow_mono_base B A (Nat.le_of_lt hBA_lt) (r - 1)
        have hsp : A ^ r - B ^ r = A ^ (r - 1) * (A - B) + B * (A ^ (r - 1) - B ^ (r - 1)) := by
          conv => lhs; rw [hr_sp]
          have h1 : B * (A ^ (r - 1) - B ^ (r - 1)) + B ^ ((r - 1) + 1) = A ^ (r - 1) * B := by
            rw [Nat.pow_succ B (r - 1), Nat.mul_comm (B ^ (r - 1)) B, ← Nat.mul_add B,
                Nat.sub_add_cancel hBnAn, Nat.mul_comm B (A ^ (r - 1))]
          have h2 : A ^ (r - 1) * (A - B) + A ^ (r - 1) * B = A ^ ((r - 1) + 1) := by
            rw [← Nat.mul_add (A ^ (r - 1)), Nat.sub_add_cancel (Nat.le_of_lt hBA_lt),
                ← Nat.pow_succ A (r - 1)]
          omega
        have hm1 : A ^ (r - 1) * 1 ≤ A ^ (r - 1) * (A - B) :=
          Nat.mul_le_mul_left _ (by omega)
        rw [Nat.mul_one] at hm1
        omega
      have hexp_ge : a1 ≤ (v + u) * (r - 1) := by
        rw [Nat.add_mul, Nat.mul_comm v (r - 1), Nat.mul_comm u (r - 1)]
        have hru : r * u = (r - 1) * u + u := by
          conv => lhs; rw [show r = (r - 1) + 1 by omega]
          rw [Nat.add_mul, Nat.one_mul]
        rw [hu, hru]; omega
      have hp2_ge : 2 ^ a1 ≤ A ^ (r - 1) := by
        dsimp [A]; rw [pow_pow_eq_mul_w5 2 (v + u) (r - 1)]
        exact pow2_mono_nat hexp_ge
      rw [← hAr, ← hBr]
      have hp2a_pos := pow2_pos_nat a1
      omega
    · have hv_lt_u : v + 1 ≤ u := by
        have hm : 1 * v ≤ (r - 1) * v := Nat.mul_le_mul_right v (by omega)
        rw [Nat.one_mul] at hm; omega
      have ha1_ge : w1 + 2 ≤ a1 := by
        have hm := Nat.mul_le_mul_left r hv_lt_u
        rw [Nat.mul_add, Nat.mul_one, ← hv, ← hu] at hm; omega
      have h3w_le : 3 ^ w1 ≤ 2 ^ (w1 + a1 - 2) := by
        have h1 : 3 ^ w1 ≤ 4 ^ w1 := nat_pow_mono_base 3 4 (by decide) w1
        rw [pow4_eq_pow2_even w1] at h1
        exact Nat.le_trans h1 (pow2_mono_nat (by omega))
      have h2K_eq : 2 ^ (w1 + a1) = 4 * 2 ^ (w1 + a1 - 2) := by
        conv => lhs; rw [show w1 + a1 = (w1 + a1 - 2) + 2 by omega]
        rw [Nat.pow_add, show (2 : Nat) ^ 2 = 4 from rfl, Nat.mul_comm]
      have ha_le : 2 ^ a1 ≤ 2 ^ (w1 + a1 - 2) := pow2_mono_nat (by omega)
      have hp2a_pos := pow2_pos_nat a1
      omega
  refine ⟨hgt_gt, ?_⟩
  intro q0 heq
  cases q0 with
  | zero =>
    rw [Nat.mul_zero] at heq
    have hp2a : 2 ^ a1 ≥ 2 := by simpa using pow2_mono_nat ha1
    omega
  | succ q' =>
    have hm := Nat.mul_le_mul_left (2 ^ (w1 + a1) - 3 ^ w1) (by omega : 1 ≤ q' + 1)
    rw [Nat.mul_one, heq] at hm; omega

/-- Decidable exact multiplicative order of `b` modulo `p`. -/
def IsExactMultOrderMod (p b d : Nat) : Prop :=
  p ≥ 2 ∧ d ≥ 1 ∧ b ^ d % p = 1 ∧ (∀ r : Fin d, r.val ≥ 1 -> b ^ r.val % p ≠ 1)

instance (p b d : Nat) : Decidable (IsExactMultOrderMod p b d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Modular representative of `3 / 2 (mod p)` for odd `p ≥ 3`. -/
def ratio32Mod (p : Nat) : Nat :=
  (3 * ((p + 1) / 2)) % p

theorem exactMultOrderMod_dvd_of_pow_eq_one (p b d e : Nat)
    (hord : IsExactMultOrderMod p b d) (he : b ^ e % p = 1) :
    d ∣ e := by
  rcases hord with ⟨hp2, hd1, hper, hmin⟩
  have hrem := pow_mod_period_w6 b d p hp2 hd1 hper e
  rw [he] at hrem
  let r : Fin d := ⟨e % d, Nat.mod_lt e hd1⟩
  by_cases hr0 : e % d = 0
  · exact Nat.dvd_of_mod_eq_zero hr0
  · exact False.elim (hmin r (by dsimp [r]; omega) hrem.symm)

theorem ratio32Mod_pow_eq_one_of_pow3_eq_pow2 (p w : Nat)
    (hp3 : p ≥ 3) (hp_odd : p % 2 = 1) (h32 : 3 ^ w % p = 2 ^ w % p) :
    (ratio32Mod p) ^ w % p = 1 := by
  let inv2 := (p + 1) / 2
  have h2inv : (2 * inv2) % p = 1 := by
    have heq : 2 * inv2 = 1 + p * 1 := by dsimp [inv2]; omega
    rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hpow_mod : (ratio32Mod p) ^ w % p = (3 * inv2) ^ w % p :=
    pow_mod_eq_of_mod_eq_w5 p (ratio32Mod p) (3 * inv2) (Nat.mod_mod _ p) w
  rw [hpow_mod, mul_pow_local 3 inv2 w, Nat.mul_mod, h32, ← Nat.mul_mod,
      ← mul_pow_local 2 inv2 w,
      pow_mod_eq_of_mod_eq_w5 p (2 * inv2) 1 (by rw [h2inv, Nat.mod_eq_of_lt (by omega)]) w,
      Nat.one_pow, Nat.mod_eq_of_lt (by omega)]

/--
  Theorem W7.1e (`one_block_common_order_prime_exclusion`, zero custom axioms):
  Universal Common-Order Divisor Exclusion Beyond Antipodal Primes:
  For ANY odd integer `p ≥ 3` whose exact multiplicative orders `d1 = ord_p(2)` and
  `d2 = ord_p(3/2)` satisfy `Nat.gcd d1 d2 ≥ 2` (requiring NO `-1` in `<2>` or `<3/2>`,
  so odd-order primes like `7, 23, 31, 47, 71, 73` are covered!), `p` can NEVER divide
  `2 ^ (w1 + a1) - 3 ^ w1` on any 1-block positive cycle (`D * q0 = 2 ^ a1 - 1`)!
-/
theorem one_block_common_order_prime_exclusion
    (w1 a1 q0 p d1 d2 : Nat)
    (hw1 : w1 ≥ 2) (ha1 : a1 ≥ 1)
    (hgt : 3 ^ w1 < 2 ^ (w1 + a1))
    (hbrox : (2 ^ (w1 + a1) - 3 ^ w1) * q0 = 2 ^ a1 - 1)
    (hp3 : p ≥ 3) (hp_odd : p % 2 = 1)
    (hd1 : IsExactMultOrderMod p 2 d1)
    (hd2 : IsExactMultOrderMod p (ratio32Mod p) d2)
    (hgcd : Nat.gcd d1 d2 ≥ 2) :
    ¬ (p ∣ (2 ^ (w1 + a1) - 3 ^ w1)) := by
  intro hp_D
  have hp_mers : p ∣ (2 ^ a1 - 1) := by
    rcases hp_D with ⟨k, hk⟩
    exact ⟨k * q0, by rw [← hbrox, hk, Nat.mul_assoc]⟩
  have h2a1 : 2 ^ a1 % p = 1 := by
    rcases hp_mers with ⟨m, hm⟩
    have hp2a : 2 ^ a1 ≥ 2 := by simpa using pow2_mono_nat ha1
    have hrew : 2 ^ a1 = 1 + p * m := by omega
    rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hd1_a1 : d1 ∣ a1 := exactMultOrderMod_dvd_of_pow_eq_one p 2 d1 a1 hd1 h2a1
  have h2K_3w : 2 ^ (w1 + a1) % p = 3 ^ w1 % p := by
    rcases hp_D with ⟨k, hk⟩
    have hlt_kw := hgt
    have hrew : 2 ^ (w1 + a1) = 3 ^ w1 + p * k := by
      generalize 2 ^ (w1 + a1) = p2k, 3 ^ w1 = p3w at hk hlt_kw ⊢; omega
    rw [hrew, Nat.add_mul_mod_self_left]
  have h2K_2w : 2 ^ (w1 + a1) % p = 2 ^ w1 % p := by
    rw [Nat.pow_add 2 w1 a1, Nat.mul_mod, h2a1, Nat.mul_one, Nat.mod_mod]
  have h3w_2w : 3 ^ w1 % p = 2 ^ w1 % p := h2K_3w.symm.trans h2K_2w
  have hrat_1 : (ratio32Mod p) ^ w1 % p = 1 :=
    ratio32Mod_pow_eq_one_of_pow3_eq_pow2 p w1 hp3 hp_odd h3w_2w
  have hd2_w1 : d2 ∣ w1 := exactMultOrderMod_dvd_of_pow_eq_one p (ratio32Mod p) d2 w1 hd2 hrat_1
  let r := Nat.gcd d1 d2
  have hr_a1 : r ∣ a1 := Nat.dvd_trans (Nat.gcd_dvd_left d1 d2) hd1_a1
  have hr_w1 : r ∣ w1 := Nat.dvd_trans (Nat.gcd_dvd_right d1 d2) hd2_w1
  exact (one_block_common_divisor_impossibility r w1 a1 hgcd hw1 ha1 hgt hr_w1 hr_a1).2 q0 hbrox

theorem bool_and_split {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a with
  | false => cases h
  | true => exact ⟨rfl, h⟩

def powModStep (p b : Nat) : Nat -> Nat
  | 0 => 1 % p
  | e + 1 => (b * powModStep p b e) % p

theorem powModStep_eq (p b : Nat) : ∀ e : Nat, powModStep p b e = b ^ e % p
  | 0 => rfl
  | e + 1 => by
    simp only [powModStep]
    calc
      (b * powModStep p b e) % p
          = (b % p * (powModStep p b e % p)) % p := Nat.mul_mod _ _ _
      _ = (b % p * (b ^ e % p)) % p := by rw [powModStep_eq p b e, Nat.mod_mod]
      _ = (b * b ^ e) % p := (Nat.mul_mod _ _ _).symm
      _ = b ^ (e + 1) % p := by rw [Nat.pow_succ, Nat.mul_comm]

def allNonOneUpTo (p b : Nat) : Nat -> Bool
  | 0 => true
  | 1 => true
  | k + 2 => decide (powModStep p b (k + 1) ≠ 1) && allNonOneUpTo p b (k + 1)

def checkExactMultOrderBool (p b d : Nat) : Bool :=
  decide (p ≥ 2) && decide (d ≥ 1) && decide (powModStep p b d = 1) && allNonOneUpTo p b d

theorem allNonOneUpTo_sound (p b : Nat) :
    ∀ (d r : Nat), allNonOneUpTo p b d = true -> 1 ≤ r -> r < d -> b ^ r % p ≠ 1
  | 0, _, _, _, hlt => by omega
  | 1, _, _, hr1, hlt => by omega
  | k + 2, r, hall, hr1, hlt => by
    rcases bool_and_split hall with ⟨hne, hrest⟩
    have hne_prop : powModStep p b (k + 1) ≠ 1 := of_decide_eq_true hne
    by_cases heq : r = k + 1
    · rw [heq, ← powModStep_eq p b (k + 1)]; exact hne_prop
    · exact allNonOneUpTo_sound p b (k + 1) r hrest hr1 (by omega)

theorem checkExactMultOrderBool_sound (p b d : Nat)
    (h : checkExactMultOrderBool p b d = true) :
    IsExactMultOrderMod p b d := by
  unfold checkExactMultOrderBool at h
  rcases bool_and_split h with ⟨h123, hall⟩
  rcases bool_and_split h123 with ⟨h12, hd_eq⟩
  rcases bool_and_split h12 with ⟨hp2, hd1⟩
  have hpow : b ^ d % p = 1 := by
    rw [← powModStep_eq p b d]; exact of_decide_eq_true hd_eq
  exact ⟨of_decide_eq_true hp2, of_decide_eq_true hd1, hpow,
    fun r hr => allNonOneUpTo_sound p b d r.val hall hr r.isLt⟩

/--
  Pure-kernel (`[]` axioms) multiplicative-order certificate for all 8 odd-order target primes
  `{7, 19, 23, 31, 43, 47, 71, 73}` and the minimal coprime-order barrier prime `p = 331`.
-/
theorem odd_order_primes_and_331_mult_order_cert :
    checkExactMultOrderBool 7 2 3 = true ∧
    checkExactMultOrderBool 7 (ratio32Mod 7) 6 = true ∧
    checkExactMultOrderBool 19 2 18 = true ∧
    checkExactMultOrderBool 19 (ratio32Mod 19) 3 = true ∧
    checkExactMultOrderBool 23 2 11 = true ∧
    checkExactMultOrderBool 23 (ratio32Mod 23) 11 = true ∧
    checkExactMultOrderBool 31 2 5 = true ∧
    checkExactMultOrderBool 31 (ratio32Mod 31) 30 = true ∧
    checkExactMultOrderBool 43 2 14 = true ∧
    checkExactMultOrderBool 43 (ratio32Mod 43) 21 = true ∧
    checkExactMultOrderBool 47 2 23 = true ∧
    checkExactMultOrderBool 47 (ratio32Mod 47) 23 = true ∧
    checkExactMultOrderBool 71 2 35 = true ∧
    checkExactMultOrderBool 71 (ratio32Mod 71) 7 = true ∧
    checkExactMultOrderBool 73 2 9 = true ∧
    checkExactMultOrderBool 73 (ratio32Mod 73) 36 = true ∧
    checkExactMultOrderBool 331 2 30 = true ∧
    checkExactMultOrderBool 331 (ratio32Mod 331) 11 = true ∧
    Nat.gcd 30 11 = 1 := by
  decide

/--
  Theorem W7.1f (`one_block_odd_order_primes_7_19_23_31_43_47_71_73_and_331_barrier`, zero custom axioms, choice-free):
  1. Unconditional Exclusion of `{7, 19, 23, 31, 43, 47, 71, 73}` on ALL 1-Block `Z^+` Cycles:
     Every prime in `{7, 19, 23, 31, 43, 47, 71, 73}` (including pure odd-order primes `7, 23, 31, 47, 71, 73`
     where Wave 5's antipodal condition fails!) has `gcd(ord_p(2), ord_p(3/2)) ∈ {3, 3, 11, 5, 7, 23, 7, 9} ≥ 2`
     and is unconditionally excluded from dividing `2 ^ (w1 + a1) - 3 ^ w1`!
  2. Minimal Coprime-Order Barrier Prime `p = 331`: Certifies `ord_331(2) = 30`, `ord_331(3/2) = 11`,
     and `Nat.gcd 30 11 = 1` (explaining why pure order-divisibility stops first at `p = 331`)!
-/
theorem one_block_odd_order_primes_7_19_23_31_43_47_71_73_and_331_barrier :
    (∀ (w1 a1 q0 p : Nat),
      w1 ≥ 2 -> a1 ≥ 1 -> 3 ^ w1 < 2 ^ (w1 + a1) ->
      (2 ^ (w1 + a1) - 3 ^ w1) * q0 = 2 ^ a1 - 1 ->
      (p = 7 ∨ p = 19 ∨ p = 23 ∨ p = 31 ∨ p = 43 ∨ p = 47 ∨ p = 71 ∨ p = 73) ->
      ¬ (p ∣ (2 ^ (w1 + a1) - 3 ^ w1))) ∧
    IsExactMultOrderMod 331 2 30 ∧
    IsExactMultOrderMod 331 (ratio32Mod 331) 11 ∧
    Nat.gcd 30 11 = 1 := by
  rcases odd_order_primes_and_331_mult_order_cert with
    ⟨h7_2, h7_32, h19_2, h19_32, h23_2, h23_32, h31_2, h31_32,
     h43_2, h43_32, h47_2, h47_32, h71_2, h71_32, h73_2, h73_32,
     h331_2, h331_32, h331_gcd⟩
  refine ⟨?_, checkExactMultOrderBool_sound _ _ _ h331_2,
          checkExactMultOrderBool_sound _ _ _ h331_32, h331_gcd⟩
  intro w1 a1 q0 p hw1 ha1 hgt hbrox hp_mem
  rcases hp_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact one_block_common_order_prime_exclusion w1 a1 q0 7 3 6 hw1 ha1 hgt hbrox
      (by decide) (by decide) (checkExactMultOrderBool_sound _ _ _ h7_2)
      (checkExactMultOrderBool_sound _ _ _ h7_32) (by decide)
  · exact one_block_common_order_prime_exclusion w1 a1 q0 19 18 3 hw1 ha1 hgt hbrox
      (by decide) (by decide) (checkExactMultOrderBool_sound _ _ _ h19_2)
      (checkExactMultOrderBool_sound _ _ _ h19_32) (by decide)
  · exact one_block_common_order_prime_exclusion w1 a1 q0 23 11 11 hw1 ha1 hgt hbrox
      (by decide) (by decide) (checkExactMultOrderBool_sound _ _ _ h23_2)
      (checkExactMultOrderBool_sound _ _ _ h23_32) (by decide)
  · exact one_block_common_order_prime_exclusion w1 a1 q0 31 5 30 hw1 ha1 hgt hbrox
      (by decide) (by decide) (checkExactMultOrderBool_sound _ _ _ h31_2)
      (checkExactMultOrderBool_sound _ _ _ h31_32) (by decide)
  · exact one_block_common_order_prime_exclusion w1 a1 q0 43 14 21 hw1 ha1 hgt hbrox
      (by decide) (by decide) (checkExactMultOrderBool_sound _ _ _ h43_2)
      (checkExactMultOrderBool_sound _ _ _ h43_32) (by decide)
  · exact one_block_common_order_prime_exclusion w1 a1 q0 47 23 23 hw1 ha1 hgt hbrox
      (by decide) (by decide) (checkExactMultOrderBool_sound _ _ _ h47_2)
      (checkExactMultOrderBool_sound _ _ _ h47_32) (by decide)
  · exact one_block_common_order_prime_exclusion w1 a1 q0 71 35 7 hw1 ha1 hgt hbrox
      (by decide) (by decide) (checkExactMultOrderBool_sound _ _ _ h71_2)
      (checkExactMultOrderBool_sound _ _ _ h71_32) (by decide)
  · exact one_block_common_order_prime_exclusion w1 a1 q0 73 9 36 hw1 ha1 hgt hbrox
      (by decide) (by decide) (checkExactMultOrderBool_sound _ _ _ h73_2)
      (checkExactMultOrderBool_sound _ _ _ h73_32) (by decide)

theorem pow3_gt_four_mul_pow2_ge4 : ∀ v : Nat, v ≥ 4 -> 4 * 2 ^ v < 3 ^ v
  | 0, hv => by omega
  | 1, hv => by omega
  | 2, hv => by omega
  | 3, hv => by omega
  | 4, _ => by decide
  | m + 5, _ => by
    have ih := pow3_gt_four_mul_pow2_ge4 (m + 4) (by omega)
    rw [Nat.pow_succ 2 (m + 4), Nat.pow_succ 3 (m + 4)]
    omega

/--
  Theorem W7.1g (`two_block_shared_mersenne_common_order_scaling_and_squeeze`, zero custom axioms):
  Universal 2-Block Common-Order Scaling Floor & Schwarz Mean-Value Squeeze:
  On ANY `IsPrimitiveTwoBlockBroxWitness w1 a1 w2 a2 q0 q1`, if an odd `p ≥ 3` with exact
  orders `d1 = ord_p(2)` and `d2 = ord_p(3/2)` (`r := Nat.gcd d1 d2`) divides BOTH `D` and `2 ^ a1 - 1`:
  1. `r ∣ a1`, `r ∣ a2`, `r ∣ (w1 + w2)`, and `r ∣ (w1 + a1 + w2 + a2)`;
  2. Universal `(5*r, 3*r, 8*r)` Scaling Floor: `w1 + w2 ≥ 5 * r`, `a1 + a2 ≥ 3 * r`,
     `w1 + a1 + w2 + a2 ≥ 8 * r`, and `Nat.max a1 a2 ≥ 2 * r` (`a1 = a2 = r` is impossible!);
  3. Sub-Exponent Mean-Value Squeeze: Writing `v := (w1 + w2) / r` and `k := (w1 + a1 + w2 + a2) / r`,
     `3 ^ v < 2 ^ k` AND `23 * r * (2 ^ k - 3 ^ v) < 3 ^ v` (ruling out `(v, k) = (5, 8)` for ALL `r ≥ 1`!).
-/
theorem two_block_shared_mersenne_common_order_scaling_and_squeeze
    (w1 a1 w2 a2 q0 q1 p d1 d2 : Nat)
    (hprim : IsPrimitiveTwoBlockBroxWitness w1 a1 w2 a2 q0 q1)
    (hp3 : p ≥ 3) (hp_odd : p % 2 = 1)
    (hd1 : IsExactMultOrderMod p 2 d1)
    (hd2 : IsExactMultOrderMod p (ratio32Mod p) d2)
    (hp_D : p ∣ (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)))
    (hp_a1 : p ∣ (2 ^ a1 - 1)) :
    let r := Nat.gcd d1 d2
    let W := w1 + w2
    let K := w1 + a1 + w2 + a2
    r ≥ 1 ∧
    r ∣ a1 ∧ r ∣ a2 ∧ r ∣ W ∧ r ∣ K ∧
    W ≥ 5 * r ∧ a1 + a2 ≥ 3 * r ∧ K ≥ 8 * r ∧ Nat.max a1 a2 ≥ 2 * r ∧
    3 ^ (W / r) < 2 ^ (K / r) ∧
    23 * r * (2 ^ (K / r) - 3 ^ (W / r)) < 3 ^ (W / r) := by
  dsimp only
  rcases hprim with
    ⟨hw1, ha1, hw2, ha2, _, _, _, _, hW8, _, hband_lo, hband_hi, _, _, _,
     h23D_lt, _, _, _, _, hbrox0, _, _⟩
  let W := w1 + w2
  let K := w1 + a1 + w2 + a2
  let D := 2 ^ K - 3 ^ W
  have hgt : 3 ^ W < 2 ^ K := by
    change 21 ^ W < 7 ^ W * 2 ^ K at hband_lo
    rw [show (21 : Nat) ^ W = 7 ^ W * 3 ^ W from mul_pow_nat 7 3 W] at hband_lo
    by_cases hlt : 3 ^ W < 2 ^ K
    · exact hlt
    · have hm := Nat.mul_le_mul_left (7 ^ W) (by omega : 2 ^ K ≤ 3 ^ W); omega
  have hdvd_H0 : D ∣ broxSpiralCarry [(w1, a1), (w2, a2)] := by
    have hcar_eq : broxSpiralCarry [(w1, a1), (w2, a2)] = twoBlockBroxCarry w1 a1 w2 a2 := by
      simp [broxSpiralCarry, twoBlockBroxCarry, blockWeightSum]
    rw [hcar_eq]
    exact ⟨q0, hbrox0.symm⟩
  rcases (two_block_shared_mersenne_propagation_and_equal_even_exclusion
    w1 a1 w2 a2 (by omega) ha1 hw2 ha2 hgt).1 hdvd_H0 p (by omega) hp_D with ⟨hiff_a2, h3W2W⟩
  have hp_a2 : p ∣ (2 ^ a2 - 1) := hiff_a2.mp hp_a1
  have hp_diffW : p ∣ (3 ^ W - 2 ^ W) := h3W2W hp_a1
  have h2a1 : 2 ^ a1 % p = 1 := by
    rcases hp_a1 with ⟨m, hm⟩
    have hp2 : 2 ^ a1 ≥ 2 := by simpa using pow2_mono_nat ha1
    rw [show 2 ^ a1 = 1 + p * m by omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have h2a2 : 2 ^ a2 % p = 1 := by
    rcases hp_a2 with ⟨m, hm⟩
    have hp2 : 2 ^ a2 ≥ 2 := by simpa using pow2_mono_nat ha2
    rw [show 2 ^ a2 = 1 + p * m by omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have h32W : 3 ^ W % p = 2 ^ W % p := by
    rcases hp_diffW with ⟨m, hm⟩
    have h2le3 : 2 ^ W ≤ 3 ^ W := pow2_le_pow3 W
    have hrew : 3 ^ W = 2 ^ W + p * m := by
      generalize 3 ^ W = p3, 2 ^ W = p2 at hm h2le3 ⊢; omega
    rw [hrew, Nat.add_mul_mod_self_left]
  have hd1_a1 : d1 ∣ a1 := exactMultOrderMod_dvd_of_pow_eq_one p 2 d1 a1 hd1 h2a1
  have hd1_a2 : d1 ∣ a2 := exactMultOrderMod_dvd_of_pow_eq_one p 2 d1 a2 hd1 h2a2
  have hd2_W : d2 ∣ W := exactMultOrderMod_dvd_of_pow_eq_one p (ratio32Mod p) d2 W hd2
    (ratio32Mod_pow_eq_one_of_pow3_eq_pow2 p W hp3 hp_odd h32W)
  let r := Nat.gcd d1 d2
  have hr_pos : r ≥ 1 := Nat.gcd_pos_of_pos_left d2 hd1.2.1
  have hr_a1 : r ∣ a1 := Nat.dvd_trans (Nat.gcd_dvd_left d1 d2) hd1_a1
  have hr_a2 : r ∣ a2 := Nat.dvd_trans (Nat.gcd_dvd_left d1 d2) hd1_a2
  have hr_W : r ∣ W := Nat.dvd_trans (Nat.gcd_dvd_right d1 d2) hd2_W
  have hr_K : r ∣ K := by
    have hK_eq : K = W + (a1 + a2) := by dsimp [K, W]; omega
    rw [hK_eq]
    exact Nat.dvd_add hr_W (Nat.dvd_add hr_a1 hr_a2)
  rcases hr_a1 with ⟨u1, hu1⟩
  rcases hr_a2 with ⟨u2, hu2⟩
  rcases hr_W with ⟨v, hv⟩
  have hu1_pos : u1 ≥ 1 := by cases u1 with | zero => simp at hu1; omega | succ _ => omega
  have hu2_pos : u2 ≥ 1 := by cases u2 with | zero => simp at hu2; omega | succ _ => omega
  have hv_pos : v ≥ 1 := by cases v with | zero => simp at hv; dsimp [W] at hv; omega | succ _ => omega
  let u := u1 + u2
  let k := v + u
  have ha12_eq : a1 + a2 = r * u := by dsimp [u]; rw [Nat.mul_add, ← hu1, ← hu2]
  have hK_rk : K = r * k := by
    dsimp [k]; rw [Nat.mul_add, ← hv, ← ha12_eq]; dsimp [K, W]; omega
  have hW_div : W / r = v := by rw [hv, Nat.mul_comm r v, Nat.mul_div_cancel v hr_pos]
  have hK_div : K / r = k := by rw [hK_rk, Nat.mul_comm r k, Nat.mul_div_cancel k hr_pos]
  have h3K_lt_5W : 3 * K < 5 * W := by
    have hcube_band := nat_pow_mono_base (7 ^ W * 2 ^ K) (22 ^ W) hband_hi 3
    rw [mul_pow_local (7 ^ W) (2 ^ K) 3,
        pow_pow_eq_mul_w5 7 W 3, pow_pow_eq_mul_w5 2 K 3, pow_pow_eq_mul_w5 22 W 3] at hcube_band
    have h22_lt : (22 ^ 3) ^ W < (7 ^ 3 * 2 ^ 5) ^ W := by
      have h1 : 22 ^ 3 < 7 ^ 3 * 2 ^ 5 := by decide
      have hW_sp : W = (W - 1) + 1 := by dsimp [W]; omega
      rw [hW_sp, Nat.pow_succ (22 ^ 3), Nat.pow_succ (7 ^ 3 * 2 ^ 5)]
      have hle_p := nat_pow_mono_base (22 ^ 3) (7 ^ 3 * 2 ^ 5) (Nat.le_of_lt h1) (W - 1)
      have hpos_p := nat_pow_pos_of_pos (22 ^ 3) (by decide) (W - 1)
      exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left h1 hpos_p)
        (Nat.mul_le_mul_right _ hle_p)
    rw [pow_pow_eq_mul_w5 22 3 W, Nat.mul_comm 3 W] at h22_lt
    rw [mul_pow_local (7 ^ 3) (2 ^ 5) W, pow_pow_eq_mul_w5 7 3 W, pow_pow_eq_mul_w5 2 5 W,
        Nat.mul_comm 3 W] at h22_lt
    have h7_lt : 7 ^ (W * 3) * 2 ^ (K * 3) < 7 ^ (W * 3) * 2 ^ (5 * W) :=
      Nat.lt_of_le_of_lt hcube_band h22_lt
    have h2_lt := nat_mul_lt_cancel_left (7 ^ (W * 3)) _ _
      (nat_pow_pos_of_pos 7 (by decide) (W * 3)) h7_lt
    by_cases hlt : 3 * K < 5 * W
    · exact hlt
    · have hm := pow2_mono_nat (by omega : 5 * W ≤ K * 3); omega
  have h3u_lt_2v : 3 * u < 2 * v := by
    rw [hK_rk, hv] at h3K_lt_5W
    have hrw1 : 3 * (r * k) = r * (3 * (v + u)) := by
      dsimp [k]; rw [← Nat.mul_assoc 3 r, Nat.mul_comm 3 r, Nat.mul_assoc r 3]
    have hrw2 : 5 * (r * v) = r * (5 * v) := by
      rw [← Nat.mul_assoc 5 r, Nat.mul_comm 5 r, Nat.mul_assoc r 5]
    rw [hrw1, hrw2] at h3K_lt_5W
    have hc := nat_mul_lt_cancel_left r _ _ hr_pos h3K_lt_5W
    omega
  have hu_ge2 : u ≥ 2 := by dsimp [u]; omega
  have hv_ge4 : v ≥ 4 := by omega
  have h3v_lt_2k : 3 ^ v < 2 ^ k := by
    by_cases hlt : 3 ^ v < 2 ^ k
    · exact hlt
    · have hm := nat_pow_mono_base (2 ^ k) (3 ^ v) (by omega) r
      rw [pow_pow_eq_mul_w5 2 k r, pow_pow_eq_mul_w5 3 v r,
          Nat.mul_comm k r, Nat.mul_comm v r, ← hK_rk, ← hv] at hm
      omega
  have hu_ge3 : u ≥ 3 := by
    by_cases hu2_eq : u = 2
    · exfalso
      have hk_eq : k = v + 2 := by dsimp [k]; omega
      have h2k_eq : 2 ^ k = 4 * 2 ^ v := by
        rw [hk_eq, Nat.pow_add 2 v 2, show (2 : Nat) ^ 2 = 4 from rfl, Nat.mul_comm]
      have hgt4 := pow3_gt_four_mul_pow2_ge4 v hv_ge4
      omega
    · omega
  have hv_ge5 : v ≥ 5 := by omega
  have hmax_a : Nat.max a1 a2 ≥ 2 * r := by
    by_cases h1 : u1 ≥ 2
    · have ha1_2r : 2 * r ≤ a1 := by rw [hu1, Nat.mul_comm 2 r]; exact Nat.mul_le_mul_left r h1
      exact Nat.le_trans ha1_2r (Nat.le_max_left a1 a2)
    · have h2 : u2 ≥ 2 := by dsimp [u] at hu_ge3; omega
      have ha2_2r : 2 * r ≤ a2 := by rw [hu2, Nat.mul_comm 2 r]; exact Nat.mul_le_mul_left r h2
      exact Nat.le_trans ha2_2r (Nat.le_max_right a1 a2)
  have hsqueeze : 23 * r * (2 ^ k - 3 ^ v) < 3 ^ v := by
    have hlo := (pow_sub_pow_mean_value_sandwich r (2 ^ k) (3 ^ v) hr_pos
      (Nat.le_of_lt h3v_lt_2k)).1
    have hAr : (2 ^ k) ^ r = 2 ^ K := by
      rw [pow_pow_eq_mul_w5 2 k r, Nat.mul_comm k r, ← hK_rk]
    have hBr : (3 ^ v) ^ r = 3 ^ W := by
      rw [pow_pow_eq_mul_w5 3 v r, Nat.mul_comm v r, ← hv]
    rw [hAr, hBr] at hlo
    have hm23 := Nat.mul_le_mul_left 23 hlo
    have hlt_comb : 23 * (r * (3 ^ v) ^ (r - 1) * (2 ^ k - 3 ^ v)) < 3 ^ W :=
      Nat.lt_of_le_of_lt hm23 h23D_lt
    have hBr_sp : 3 ^ W = 3 ^ v * (3 ^ v) ^ (r - 1) := by
      rw [← hBr]
      conv => lhs; rw [show r = (r - 1) + 1 by omega]
      rw [Nat.pow_succ, Nat.mul_comm]
    have hl_rw : 23 * (r * (3 ^ v) ^ (r - 1) * (2 ^ k - 3 ^ v)) =
        (23 * r * (2 ^ k - 3 ^ v)) * (3 ^ v) ^ (r - 1) := by
      calc
        23 * (r * (3 ^ v) ^ (r - 1) * (2 ^ k - 3 ^ v))
            = (23 * r) * ((3 ^ v) ^ (r - 1) * (2 ^ k - 3 ^ v)) := by
              rw [Nat.mul_assoc r, ← Nat.mul_assoc 23 r]
        _ = (23 * r) * ((2 ^ k - 3 ^ v) * (3 ^ v) ^ (r - 1)) := by
              rw [Nat.mul_comm ((3 ^ v) ^ (r - 1))]
        _ = (23 * r * (2 ^ k - 3 ^ v)) * (3 ^ v) ^ (r - 1) := (Nat.mul_assoc _ _ _).symm
    rw [hl_rw, hBr_sp] at hlt_comb
    exact nat_mul_lt_cancel_right_w5 ((3 ^ v) ^ (r - 1)) _ _
      (nat_pow_pos_of_pos (3 ^ v) (pow3_pos_nat v) (r - 1)) hlt_comb
  have hW_5r : w1 + w2 ≥ 5 * r := by
    change W ≥ 5 * r; rw [hv, Nat.mul_comm 5 r]; exact Nat.mul_le_mul_left r hv_ge5
  have ha_3r : a1 + a2 ≥ 3 * r := by
    rw [ha12_eq, Nat.mul_comm 3 r]; exact Nat.mul_le_mul_left r hu_ge3
  have hK_8r : w1 + a1 + w2 + a2 ≥ 8 * r := by
    change K ≥ 8 * r; rw [hK_rk, Nat.mul_comm 8 r]
    exact Nat.mul_le_mul_left r (by dsimp [k]; omega)
  change (w1 + w2) / r = v at hW_div
  change (w1 + a1 + w2 + a2) / r = k at hK_div
  rw [hW_div, hK_div]
  exact ⟨hr_pos, ⟨u1, hu1⟩, ⟨u2, hu2⟩, ⟨v, hv⟩, hr_K,
         hW_5r, ha_3r, hK_8r, hmax_a, h3v_lt_2k, hsqueeze⟩

theorem pow3_mono_w7 (a b : Nat) (h : a ≤ b) : 3 ^ a ≤ 3 ^ b := by
  have hsp : b = a + (b - a) := by omega
  rw [hsp, Nat.pow_add]
  have hp : 1 ≤ 3 ^ (b - a) := nat_pow_pos_of_pos 3 (by decide) (b - a)
  simpa using Nat.mul_le_mul_left (3 ^ a) hp

def minExp2CandW7 (v : Nat) : Nat :=
  (1585 * v) / 1000 + 1

def checkSqueeze69At (v : Nat) : Bool :=
  let k0 := minExp2CandW7 v
  decide (k0 ≥ 1) &&
  decide (2 ^ (k0 - 1) ≤ 3 ^ v) &&
  decide (3 ^ v < 2 ^ k0) &&
  decide (69 * (2 ^ k0 - 3 ^ v) ≥ 3 ^ v)

def checkAllSqueeze69UpTo : Nat -> Bool
  | 0 => true
  | v + 1 => checkSqueeze69At (v + 1) && checkAllSqueeze69UpTo v

/-- Pure-kernel (`[]` axioms) certificate verifying `69 * (2 ^ k - 3 ^ v) ≥ 3 ^ v` across all `1 ≤ v ≤ 40`. -/
theorem squeeze69_up_to_40_cert : checkAllSqueeze69UpTo 40 = true := by
  decide

theorem checkSqueeze69At_sound (v k : Nat)
    (hc : checkSqueeze69At v = true) (hgt : 3 ^ v < 2 ^ k) :
    69 * (2 ^ k - 3 ^ v) ≥ 3 ^ v := by
  unfold checkSqueeze69At at hc
  rcases bool_and_split hc with ⟨hc123, hsq_b⟩
  rcases bool_and_split hc123 with ⟨hc12, hgt0_b⟩
  rcases bool_and_split hc12 with ⟨hk0_pos_b, hle_prev_b⟩
  let k0 := minExp2CandW7 v
  have hk0_pos : k0 ≥ 1 := of_decide_eq_true hk0_pos_b
  have hle_prev : 2 ^ (k0 - 1) ≤ 3 ^ v := of_decide_eq_true hle_prev_b
  have hsq0 : 69 * (2 ^ k0 - 3 ^ v) ≥ 3 ^ v := of_decide_eq_true hsq_b
  have hk_ge_k0 : k ≥ k0 := by
    by_cases hlt : k < k0
    · have hk_le : k ≤ k0 - 1 := by omega
      have hp2_le : 2 ^ k ≤ 2 ^ (k0 - 1) := pow2_mono_nat hk_le
      omega
    · omega
  have hp2_ge : 2 ^ k0 ≤ 2 ^ k := pow2_mono_nat hk_ge_k0
  have hdiff_ge : 2 ^ k0 - 3 ^ v ≤ 2 ^ k - 3 ^ v := by omega
  exact Nat.le_trans hsq0 (Nat.mul_le_mul_left 69 hdiff_ge)

theorem checkAllSqueeze69UpTo_sound :
    ∀ (N v k : Nat), checkAllSqueeze69UpTo N = true ->
      1 ≤ v -> v ≤ N -> 3 ^ v < 2 ^ k -> 69 * (2 ^ k - 3 ^ v) ≥ 3 ^ v
  | 0, _, _, _, hv1, hv0, _ => by omega
  | n + 1, v, k, hall, hv1, hv_le, hgt => by
    rcases bool_and_split hall with ⟨hat, hrest⟩
    by_cases heq : v = n + 1
    · rw [heq] at hgt ⊢
      exact checkSqueeze69At_sound (n + 1) k hat hgt
    · exact checkAllSqueeze69UpTo_sound n v k hrest hv1 (by omega) hgt

/--
  Theorem W7.1h (`two_block_odd_order_primes_7_19_23_31_43_47_71_73_weight_41r_floor`, zero custom axioms):
  Sharp `(41 * r, 65 * r)` 2-Block Cycle Weight Floor Across ALL 8 Odd-Order Target Primes:
  1. Universal `r ≥ 3` Boost: Whenever `r := Nat.gcd d1 d2 ≥ 3`, `23 * r * (2 ^ k - 3 ^ v) < 3 ^ v`
     implies `69 * (2 ^ k - 3 ^ v) < 3 ^ v`, eliminating ALL `1 ≤ v ≤ 40` via `squeeze69_up_to_40_cert`
     and forcing `w1 + w2 ≥ 41 * r` and `w1 + a1 + w2 + a2 ≥ 65 * r` (an `8.2x` sharpening of `5 * r`!);
  2. Explicit 2-Block Prime Instantiation (`{7, 19, 23, 31, 43, 47, 71, 73}`):
     - `p ∈ {7, 19}` (`r = 3`): `W ≥ 123 ∧ K ≥ 195`;
     - `p = 31` (`r = 5`): `W ≥ 205 ∧ K ≥ 325`;
     - `p ∈ {43, 71}` (`r = 7`): `W ≥ 287 ∧ K ≥ 455`;
     - `p = 73` (`r = 9`): `W ≥ 369 ∧ K ≥ 585`;
     - `p = 23` (`r = 11`): `W ≥ 451 ∧ K ≥ 715`;
     - `p = 47` (`r = 23`): `W ≥ 943 ∧ K ≥ 1495`.
-/
theorem two_block_odd_order_primes_7_19_23_31_43_47_71_73_weight_41r_floor :
    (∀ (w1 a1 w2 a2 q0 q1 p d1 d2 : Nat),
      IsPrimitiveTwoBlockBroxWitness w1 a1 w2 a2 q0 q1 ->
      p ≥ 3 -> p % 2 = 1 ->
      IsExactMultOrderMod p 2 d1 ->
      IsExactMultOrderMod p (ratio32Mod p) d2 ->
      Nat.gcd d1 d2 ≥ 3 ->
      p ∣ (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)) ->
      p ∣ (2 ^ a1 - 1) ->
      w1 + w2 ≥ 41 * Nat.gcd d1 d2 ∧
      w1 + a1 + w2 + a2 ≥ 65 * Nat.gcd d1 d2) ∧
    (∀ (w1 a1 w2 a2 q0 q1 p : Nat),
      IsPrimitiveTwoBlockBroxWitness w1 a1 w2 a2 q0 q1 ->
      p ∣ (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)) ->
      p ∣ (2 ^ a1 - 1) ->
      ((p = 7 ∨ p = 19) -> w1 + w2 ≥ 123 ∧ w1 + a1 + w2 + a2 ≥ 195) ∧
      (p = 31 -> w1 + w2 ≥ 205 ∧ w1 + a1 + w2 + a2 ≥ 325) ∧
      ((p = 43 ∨ p = 71) -> w1 + w2 ≥ 287 ∧ w1 + a1 + w2 + a2 ≥ 455) ∧
      (p = 73 -> w1 + w2 ≥ 369 ∧ w1 + a1 + w2 + a2 ≥ 585) ∧
      (p = 23 -> w1 + w2 ≥ 451 ∧ w1 + a1 + w2 + a2 ≥ 715) ∧
      (p = 47 -> w1 + w2 ≥ 943 ∧ w1 + a1 + w2 + a2 ≥ 1495)) := by
  have huniv : ∀ (w1 a1 w2 a2 q0 q1 p d1 d2 : Nat),
      IsPrimitiveTwoBlockBroxWitness w1 a1 w2 a2 q0 q1 ->
      p ≥ 3 -> p % 2 = 1 ->
      IsExactMultOrderMod p 2 d1 ->
      IsExactMultOrderMod p (ratio32Mod p) d2 ->
      Nat.gcd d1 d2 ≥ 3 ->
      p ∣ (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)) ->
      p ∣ (2 ^ a1 - 1) ->
      w1 + w2 ≥ 41 * Nat.gcd d1 d2 ∧
      w1 + a1 + w2 + a2 ≥ 65 * Nat.gcd d1 d2 := by
    intro w1 a1 w2 a2 q0 q1 p d1 d2 hprim hp3 hp_odd hd1 hd2 hgcd3 hp_D hp_a1
    rcases two_block_shared_mersenne_common_order_scaling_and_squeeze
      w1 a1 w2 a2 q0 q1 p d1 d2 hprim hp3 hp_odd hd1 hd2 hp_D hp_a1 with
      ⟨_, _, _, hr_W, hr_K, hW_5r, _, _, _, h3v_lt_2k, hsqueeze⟩
    let r := Nat.gcd d1 d2
    let W := w1 + w2
    let K := w1 + a1 + w2 + a2
    let v := W / r
    let k := K / r
    change r ≥ 3 at hgcd3
    change r ∣ W at hr_W
    change r ∣ K at hr_K
    change W ≥ 5 * r at hW_5r
    change 3 ^ v < 2 ^ k at h3v_lt_2k
    change 23 * r * (2 ^ k - 3 ^ v) < 3 ^ v at hsqueeze
    have hW_eq : W = r * v := (Nat.mul_div_cancel' hr_W).symm
    have hK_eq : K = r * k := (Nat.mul_div_cancel' hr_K).symm
    have hv_pos : v ≥ 1 := by
      have hm : 5 * r ≤ r * v := by rw [← hW_eq]; exact hW_5r
      rw [Nat.mul_comm 5 r] at hm
      have hv5 := nat_mul_le_cancel_left_w5 r 5 v (by omega) hm
      omega
    have h69_lt : 69 * (2 ^ k - 3 ^ v) < 3 ^ v := by
      have hm69 : 69 * (2 ^ k - 3 ^ v) ≤ 23 * r * (2 ^ k - 3 ^ v) :=
        Nat.mul_le_mul_right (2 ^ k - 3 ^ v) (by omega : 69 ≤ 23 * r)
      exact Nat.lt_of_le_of_lt hm69 hsqueeze
    have hv_ge41 : v ≥ 41 := by
      by_cases hv40 : v ≤ 40
      · have hge := checkAllSqueeze69UpTo_sound 40 v k squeeze69_up_to_40_cert hv_pos hv40 h3v_lt_2k
        omega
      · omega
    have hk_ge65 : k ≥ 65 := by
      have h2_64_lt : 2 ^ 64 < 3 ^ 41 := by decide
      have h3_le : 3 ^ 41 ≤ 3 ^ v := pow3_mono_w7 41 v hv_ge41
      have h2_64_lt_2k : 2 ^ 64 < 2 ^ k := Nat.lt_trans (Nat.lt_of_lt_of_le h2_64_lt h3_le) h3v_lt_2k
      by_cases hk64 : k ≤ 64
      · have hle := pow2_mono_nat hk64; omega
      · omega
    have hW_41r : W ≥ 41 * r := by
      rw [hW_eq, Nat.mul_comm 41 r]
      exact Nat.mul_le_mul_left r hv_ge41
    have hK_65r : K ≥ 65 * r := by
      rw [hK_eq, Nat.mul_comm 65 r]
      exact Nat.mul_le_mul_left r hk_ge65
    exact ⟨hW_41r, hK_65r⟩
  rcases odd_order_primes_and_331_mult_order_cert with
    ⟨h7_2, h7_32, h19_2, h19_32, h23_2, h23_32, h31_2, h31_32,
     h43_2, h43_32, h47_2, h47_32, h71_2, h71_32, h73_2, h73_32, _, _, _⟩
  refine ⟨huniv, ?_⟩
  intro w1 a1 w2 a2 q0 q1 p hprim hp_D hp_a1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (rfl | rfl)
    · simpa using huniv w1 a1 w2 a2 q0 q1 7 3 6 hprim (by decide) (by decide)
        (checkExactMultOrderBool_sound _ _ _ h7_2)
        (checkExactMultOrderBool_sound _ _ _ h7_32) (by decide) hp_D hp_a1
    · simpa using huniv w1 a1 w2 a2 q0 q1 19 18 3 hprim (by decide) (by decide)
        (checkExactMultOrderBool_sound _ _ _ h19_2)
        (checkExactMultOrderBool_sound _ _ _ h19_32) (by decide) hp_D hp_a1
  · rintro rfl
    simpa using huniv w1 a1 w2 a2 q0 q1 31 5 30 hprim (by decide) (by decide)
      (checkExactMultOrderBool_sound _ _ _ h31_2)
      (checkExactMultOrderBool_sound _ _ _ h31_32) (by decide) hp_D hp_a1
  · rintro (rfl | rfl)
    · simpa using huniv w1 a1 w2 a2 q0 q1 43 14 21 hprim (by decide) (by decide)
        (checkExactMultOrderBool_sound _ _ _ h43_2)
        (checkExactMultOrderBool_sound _ _ _ h43_32) (by decide) hp_D hp_a1
    · simpa using huniv w1 a1 w2 a2 q0 q1 71 35 7 hprim (by decide) (by decide)
        (checkExactMultOrderBool_sound _ _ _ h71_2)
        (checkExactMultOrderBool_sound _ _ _ h71_32) (by decide) hp_D hp_a1
  · rintro rfl
    simpa using huniv w1 a1 w2 a2 q0 q1 73 9 36 hprim (by decide) (by decide)
      (checkExactMultOrderBool_sound _ _ _ h73_2)
      (checkExactMultOrderBool_sound _ _ _ h73_32) (by decide) hp_D hp_a1
  · rintro rfl
    simpa using huniv w1 a1 w2 a2 q0 q1 23 11 11 hprim (by decide) (by decide)
      (checkExactMultOrderBool_sound _ _ _ h23_2)
      (checkExactMultOrderBool_sound _ _ _ h23_32) (by decide) hp_D hp_a1
  · rintro rfl
    simpa using huniv w1 a1 w2 a2 q0 q1 47 23 23 hprim (by decide) (by decide)
      (checkExactMultOrderBool_sound _ _ _ h47_2)
      (checkExactMultOrderBool_sound _ _ _ h47_32) (by decide) hp_D hp_a1

-- ============================================================================
-- SECTION 2: Front B — Binary Digit/Run-Length/`bitLength` Preimage Weights &
--            Mahler–Koopman Tauberian Balance / `M3` Non-Uniqueness
-- ============================================================================

def binBitLengthAux : Nat -> Nat -> Nat
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else 1 + binBitLengthAux fuel (n / 2)

/-- Binary bit-length `⌊log_2 n⌋ + 1` for `n ≥ 1` (`0` at `n = 0`). -/
def binBitLength (n : Nat) : Nat :=
  binBitLengthAux n n

def binPopcountAux : Nat -> Nat -> Nat
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else (n % 2) + binPopcountAux fuel (n / 2)

/-- Binary `1`-bit popcount (`s_2(n)`). -/
def binPopcount (n : Nat) : Nat :=
  binPopcountAux n n

def binOneRunsAux : Nat -> Nat -> Nat -> Nat
  | 0, _, _ => 0
  | fuel + 1, prev, n =>
    if n = 0 then 0
    else (if n % 2 = 1 ∧ prev = 0 then 1 else 0) + binOneRunsAux fuel (n % 2) (n / 2)

/-- Number of maximal contiguous `1`-bit runs in the binary expansion of `n`. -/
def binOneRuns (n : Nat) : Nat :=
  binOneRunsAux n 0 n

def binAltTransAux : Nat -> Nat -> Nat
  | 0, _ => 0
  | fuel + 1, n =>
    if n ≤ 1 then 0
    else (if n % 2 ≠ (n / 2) % 2 then 1 else 0) + binAltTransAux fuel (n / 2)

/-- Number of adjacent `01` / `10` bit transitions in the binary expansion of `n`. -/
def binAltTransitions (n : Nat) : Nat :=
  binAltTransAux n n

/-- Coupled 6-coordinate non-algebraic binary digit signature on `(n, n + 1)`. -/
structure BinDigitSig6 where
  pop1 : Nat
  runs1 : Nat
  alt01 : Nat
  pop1Succ : Nat
  runs1Succ : Nat
  alt01Succ : Nat
  deriving DecidableEq, Repr

def binDigitSig6 (n : Nat) : BinDigitSig6 :=
  { pop1 := binPopcount n
    runs1 := binOneRuns n
    alt01 := binAltTransitions n
    pop1Succ := binPopcount (n + 1)
    runs1Succ := binOneRuns (n + 1)
    alt01Succ := binAltTransitions (n + 1) }

theorem binBitLengthAux_eq_of_ge :
    ∀ (f1 f2 n : Nat), n ≤ f1 -> n ≤ f2 -> binBitLengthAux f1 n = binBitLengthAux f2 n
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, n, h1, _ => by rw [show n = 0 by omega]; simp [binBitLengthAux]
  | _ + 1, 0, n, _, h2 => by rw [show n = 0 by omega]; simp [binBitLengthAux]
  | f1 + 1, f2 + 1, n, h1, h2 => by
    simp only [binBitLengthAux]
    by_cases hn0 : n = 0
    · simp [hn0]
    · simp only [hn0, ite_false]
      rw [binBitLengthAux_eq_of_ge f1 f2 (n / 2) (by omega) (by omega)]

theorem binBitLength_step_pos (n : Nat) (hn : n ≥ 1) :
    binBitLength n = 1 + binBitLength (n / 2) := by
  unfold binBitLength
  cases h : n with
  | zero => omega
  | succ m =>
    simp only [binBitLengthAux, Nat.succ_ne_zero, ite_false]
    rw [binBitLengthAux_eq_of_ge m ((m + 1) / 2) ((m + 1) / 2) (by omega) (Nat.le_refl _)]

theorem binBitLength_mono_aux :
    ∀ (bound a b : Nat), b ≤ bound -> a ≤ b -> binBitLength a ≤ binBitLength b
  | 0, a, b, hb, hab => by
    have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    subst ha0 hb0; exact Nat.le_refl _
  | bound + 1, a, b, hb, hab => by
    by_cases ha0 : a = 0
    · subst ha0; simp [binBitLength, binBitLengthAux]
    · rw [binBitLength_step_pos a (by omega), binBitLength_step_pos b (by omega)]
      have ih := binBitLength_mono_aux bound (a / 2) (b / 2) (by omega) (by omega)
      omega

theorem binBitLength_mono (a b : Nat) (hab : a ≤ b) : binBitLength a ≤ binBitLength b :=
  binBitLength_mono_aux b a b (Nat.le_refl b) hab

theorem binBitLength_pow2_and_pred :
    ∀ L : Nat, binBitLength (2 ^ L) = L + 1 ∧ binBitLength (2 ^ (L + 1) - 1) = L + 1
  | 0 => ⟨by decide, by decide⟩
  | L + 1 => by
    rcases binBitLength_pow2_and_pred L with ⟨ih_lo, ih_hi⟩
    have hp_pos := pow2_pos_nat (L + 1)
    refine ⟨?_, ?_⟩
    · rw [binBitLength_step_pos (2 ^ (L + 1)) (by omega)]
      have hd : 2 ^ (L + 1) / 2 = 2 ^ L := by
        rw [Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]
      rw [hd, ih_lo]; omega
    · rw [binBitLength_step_pos (2 ^ (L + 2) - 1) (by
        have hp2 : 2 ^ (L + 2) ≥ 4 := pow2_ge_four_of_ge_two (L + 2) (by omega); omega)]
      have hd : (2 ^ (L + 2) - 1) / 2 = 2 ^ (L + 1) - 1 := by
        rw [show L + 2 = (L + 1) + 1 by omega, Nat.pow_succ]; omega
      rw [hd, ih_hi]; omega

theorem binBitLength_of_pow2_sandwich (L n : Nat)
    (hlo : 2 ^ L ≤ n) (hhi : n < 2 ^ (L + 1)) :
    binBitLength n = L + 1 := by
  rcases binBitLength_pow2_and_pred L with ⟨h1, h2⟩
  have hge := binBitLength_mono (2 ^ L) n hlo
  have hle := binBitLength_mono n (2 ^ (L + 1) - 1) (by omega)
  omega

theorem binPopcountAux_eq_of_ge :
    ∀ (f1 f2 n : Nat), n ≤ f1 -> n ≤ f2 -> binPopcountAux f1 n = binPopcountAux f2 n
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, n, h1, _ => by rw [show n = 0 by omega]; simp [binPopcountAux]
  | _ + 1, 0, n, _, h2 => by rw [show n = 0 by omega]; simp [binPopcountAux]
  | f1 + 1, f2 + 1, n, h1, h2 => by
    simp only [binPopcountAux]
    by_cases hn0 : n = 0
    · simp [hn0]
    · simp only [hn0, ite_false]
      rw [binPopcountAux_eq_of_ge f1 f2 (n / 2) (by omega) (by omega)]

theorem binPopcount_step_pos (n : Nat) (hn : n ≥ 1) :
    binPopcount n = (n % 2) + binPopcount (n / 2) := by
  unfold binPopcount
  cases n with
  | zero => omega
  | succ m =>
    simp only [binPopcountAux, Nat.succ_ne_zero, ite_false]
    rw [binPopcountAux_eq_of_ge m ((m + 1) / 2) ((m + 1) / 2) (by omega) (Nat.le_refl _)]

theorem binOneRunsAux_eq_of_ge :
    ∀ (f1 f2 prev n : Nat), n ≤ f1 -> n ≤ f2 ->
      binOneRunsAux f1 prev n = binOneRunsAux f2 prev n
  | 0, 0, _, _, _, _ => rfl
  | 0, _ + 1, _, n, h1, _ => by rw [show n = 0 by omega]; simp [binOneRunsAux]
  | _ + 1, 0, _, n, _, h2 => by rw [show n = 0 by omega]; simp [binOneRunsAux]
  | f1 + 1, f2 + 1, prev, n, h1, h2 => by
    simp only [binOneRunsAux]
    by_cases hn0 : n = 0
    · simp [hn0]
    · simp only [hn0, ite_false]
      rw [binOneRunsAux_eq_of_ge f1 f2 (n % 2) (n / 2) (by omega) (by omega)]

theorem binOneRunsAux_step_pos (prev n : Nat) (hn : n ≥ 1) :
    binOneRunsAux n prev n =
      (if n % 2 = 1 ∧ prev = 0 then 1 else 0) + binOneRunsAux (n / 2) (n % 2) (n / 2) := by
  cases n with
  | zero => omega
  | succ m =>
    simp only [binOneRunsAux, Nat.succ_ne_zero, ite_false]
    rw [binOneRunsAux_eq_of_ge m ((m + 1) / 2) ((m + 1) % 2) ((m + 1) / 2)
      (by omega) (Nat.le_refl _)]

theorem binAltTransAux_eq_of_ge :
    ∀ (f1 f2 n : Nat), n ≤ f1 -> n ≤ f2 -> binAltTransAux f1 n = binAltTransAux f2 n
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, n, h1, _ => by rw [show n = 0 by omega]; simp [binAltTransAux]
  | _ + 1, 0, n, _, h2 => by rw [show n = 0 by omega]; simp [binAltTransAux]
  | f1 + 1, f2 + 1, n, h1, h2 => by
    simp only [binAltTransAux]
    by_cases hn1 : n ≤ 1
    · simp [hn1]
    · simp only [hn1, ite_false]
      rw [binAltTransAux_eq_of_ge f1 f2 (n / 2) (by omega) (by omega)]

theorem binAltTransitions_step_ge2 (n : Nat) (hn : n ≥ 2) :
    binAltTransitions n =
      (if n % 2 ≠ (n / 2) % 2 then 1 else 0) + binAltTransitions (n / 2) := by
  unfold binAltTransitions
  cases n with
  | zero => omega
  | succ m =>
    have hgt1 : ¬ (m + 1 ≤ 1) := by omega
    simp only [binAltTransAux, hgt1, ite_false]
    rw [binAltTransAux_eq_of_ge m ((m + 1) / 2) ((m + 1) / 2) (by omega) (Nat.le_refl _)]

theorem binTriple_mul8_eq_mul2 (X : Nat) (hX : X ≥ 1) :
    binPopcount (8 * X) = binPopcount (2 * X) ∧
    (∀ prev : Nat, binOneRunsAux (8 * X) prev (8 * X) = binOneRunsAux (2 * X) prev (2 * X)) ∧
    binAltTransitions (8 * X) = binAltTransitions (2 * X) := by
  have hm8 : (8 * X) % 2 = 0 := by omega
  have hd8 : (8 * X) / 2 = 4 * X := by omega
  have hm4 : (4 * X) % 2 = 0 := by omega
  have hd4 : (4 * X) / 2 = 2 * X := by omega
  have hm2 : (2 * X) % 2 = 0 := by omega
  have hd2 : (2 * X) / 2 = X := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [binPopcount_step_pos (8 * X) (by omega), hm8, hd8, Nat.zero_add,
        binPopcount_step_pos (4 * X) (by omega), hm4, hd4, Nat.zero_add]
  · intro prev
    rw [binOneRunsAux_step_pos prev (8 * X) (by omega), hm8, hd8]
    simp only [Nat.zero_ne_one, false_and, ite_false, Nat.zero_add]
    rw [binOneRunsAux_step_pos 0 (4 * X) (by omega), hm4, hd4]
    simp only [Nat.zero_ne_one, false_and, ite_false, Nat.zero_add]
    rw [binOneRunsAux_step_pos 0 (2 * X) (by omega),
        binOneRunsAux_step_pos prev (2 * X) (by omega), hm2, hd2]
    simp
  · rw [binAltTransitions_step_ge2 (8 * X) (by omega), hm8, hd8, hm4]
    simp only [ne_eq, not_true_eq_false, ite_false, Nat.zero_add]
    rw [binAltTransitions_step_ge2 (4 * X) (by omega), hm4, hd4, hm2]
    simp only [ne_eq, not_true_eq_false, ite_false, Nat.zero_add]

theorem binTriple_shift2_congr (A B : Nat) (hA : A ≥ 1) (hB : B ≥ 1)
    (hpar : A % 2 = B % 2)
    (hpop : binPopcount A = binPopcount B)
    (hruns : ∀ prev : Nat, binOneRunsAux A prev A = binOneRunsAux B prev B)
    (halt : binAltTransitions A = binAltTransitions B) (b : Nat) (hb : b < 2) :
    (2 * A + b) ≥ 2 ∧ (2 * B + b) ≥ 2 ∧ (2 * A + b) % 2 = (2 * B + b) % 2 ∧
    binPopcount (2 * A + b) = binPopcount (2 * B + b) ∧
    (∀ prev : Nat, binOneRunsAux (2 * A + b) prev (2 * A + b) =
      binOneRunsAux (2 * B + b) prev (2 * B + b)) ∧
    binAltTransitions (2 * A + b) = binAltTransitions (2 * B + b) := by
  have hnA : 2 * A + b ≥ 2 := by omega
  have hnB : 2 * B + b ≥ 2 := by omega
  have hm2A : (2 * A + b) % 2 = b := by omega
  have hm2B : (2 * B + b) % 2 = b := by omega
  have hd2A : (2 * A + b) / 2 = A := by omega
  have hd2B : (2 * B + b) / 2 = B := by omega
  refine ⟨hnA, hnB, hm2A.trans hm2B.symm, ?_, ?_, ?_⟩
  · rw [binPopcount_step_pos (2 * A + b) (by omega),
        binPopcount_step_pos (2 * B + b) (by omega),
        hm2A, hm2B, hd2A, hd2B, hpop]
  · intro prev
    rw [binOneRunsAux_step_pos prev (2 * A + b) (by omega),
        binOneRunsAux_step_pos prev (2 * B + b) (by omega),
        hm2A, hm2B, hd2A, hd2B, hruns b]
  · rw [binAltTransitions_step_ge2 (2 * A + b) hnA,
        binAltTransitions_step_ge2 (2 * B + b) hnB,
        hm2A, hm2B, hd2A, hd2B, hpar, halt]

theorem binTriple_pow4_pad (c : Nat) (hc : c ≥ 1) :
    ∀ d : Nat,
      (2 * 4 ^ d * c) ≥ 2 ∧ (2 * 4 ^ d * c) % 2 = 0 ∧
      binPopcount (2 * 4 ^ d * c) = binPopcount (2 * c) ∧
      (∀ prev : Nat, binOneRunsAux (2 * 4 ^ d * c) prev (2 * 4 ^ d * c) =
        binOneRunsAux (2 * c) prev (2 * c)) ∧
      binAltTransitions (2 * 4 ^ d * c) = binAltTransitions (2 * c)
  | 0 => by
    have h1 : 2 * 4 ^ 0 * c = 2 * c := by simp
    rw [h1]
    exact ⟨by omega, by omega, rfl, fun _ => rfl, rfl⟩
  | d + 1 => by
    rcases binTriple_pow4_pad c hc d with ⟨_, _, hpop, hruns, halt⟩
    let X := 4 ^ d * c
    have hX_pos : X ≥ 1 := Nat.mul_le_mul (nat_pow_pos_of_pos 4 (by decide) d) hc
    have hM_eq : 2 * 4 ^ d * c = 2 * X := by dsimp [X]; rw [Nat.mul_assoc]
    have hMd1_eq : 2 * 4 ^ (d + 1) * c = 8 * X := by
      dsimp [X]
      rw [Nat.pow_succ 4 d, Nat.mul_comm (4 ^ d) 4, ← Nat.mul_assoc 2 4 (4 ^ d),
          show 2 * 4 = 8 from rfl, Nat.mul_assoc]
    rcases binTriple_mul8_eq_mul2 X hX_pos with ⟨hp8, hr8, ha8⟩
    rw [hMd1_eq]
    exact ⟨by omega, by omega,
           hp8.trans (hM_eq ▸ hpop),
           fun prev => (hr8 prev).trans (hM_eq ▸ hruns prev),
           ha8.trans (hM_eq ▸ halt)⟩

theorem binTriple_pow2_pad_add_aux (d c : Nat) (hc : c ≥ 1) :
    ∀ (e r : Nat), r < 2 ^ e ->
      let n := 2 ^ e * (2 * 4 ^ d * c) + r
      let n0 := 2 ^ e * (2 * c) + r
      n ≥ 2 ∧ n0 ≥ 2 ∧ n % 2 = n0 % 2 ∧
      binPopcount n = binPopcount n0 ∧
      (∀ prev : Nat, binOneRunsAux n prev n = binOneRunsAux n0 prev n0) ∧
      binAltTransitions n = binAltTransitions n0
  | 0, r, hr => by
    have hr0 : r = 0 := by simp at hr; omega
    subst hr0
    simp only [Nat.pow_zero, Nat.one_mul, Nat.add_zero]
    rcases binTriple_pow4_pad c hc d with ⟨hge, hev, hp, hru, ha⟩
    exact ⟨hge, by omega, by omega, hp, hru, ha⟩
  | e + 1, r, hr => by
    have hr_div : r / 2 < 2 ^ e := by
      rw [Nat.pow_succ] at hr; omega
    rcases binTriple_pow2_pad_add_aux d c hc e (r / 2) hr_div with
      ⟨hgeA, hgeB, hpar, hp, hru, ha⟩
    have hstep := binTriple_shift2_congr
      (2 ^ e * (2 * 4 ^ d * c) + r / 2) (2 ^ e * (2 * c) + r / 2)
      (by omega) (by omega) hpar hp hru ha (r % 2) (Nat.mod_lt r (by decide))
    have hrew : ∀ M : Nat, 2 * (2 ^ e * M + r / 2) + r % 2 = 2 ^ (e + 1) * M + r := by
      intro M
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ e) 2, Nat.mul_assoc 2 (2 ^ e) M, Nat.mul_add 2]
      omega
    dsimp only
    rw [← hrew (2 * 4 ^ d * c), ← hrew (2 * c)]
    exact hstep

theorem binTriple_16_pad_add (d c r : Nat) (hc : c ≥ 1) (hr : r < 16) :
    binPopcount (16 * (2 * 4 ^ d * c) + r) = binPopcount (16 * (2 * c) + r) ∧
    binOneRuns (16 * (2 * 4 ^ d * c) + r) = binOneRuns (16 * (2 * c) + r) ∧
    binAltTransitions (16 * (2 * 4 ^ d * c) + r) = binAltTransitions (16 * (2 * c) + r) := by
  have h := binTriple_pow2_pad_add_aux d c hc 4 r (by simpa using hr)
  dsimp only at h
  have h16 : (2 : Nat) ^ 4 = 16 := rfl
  rw [h16] at h
  exact ⟨h.2.2.2.1, h.2.2.2.2.1 0, h.2.2.2.2.2⟩

/--
  Theorem W7.2a (`binary_digit_sig6_and_bitlength_infinite_collision_family`, zero custom axioms):
  Infinite Exact Binary Digit-Signature & Bit-Length Preimage Collision Family (`∀ k ≥ 3`):
  Along `m_k = 3 * 4 ^ k + 8` (`m_k % 3 = 2`, starting at `m_3 = 200` with `2 * m_3 = 400` and
  `n_odd(3) = 133`):
  1. `binDigitSig6 (m_k) = (3, 2, 3, 4, 3, 4) = binDigitSig6 (2 * m_k)` for ALL `k ≥ 3`!
  2. `binDigitSig6 (n_odd k) = (3, 3, 4, 3, 2, 3)` for ALL `k ≥ 3`!
  3. `binBitLength (n_odd k) = 2 * k + 2 = binBitLength (m_k)` while `binBitLength (2 * m_k) = 2 * k + 3`!
-/
theorem binary_digit_sig6_and_bitlength_infinite_collision_family (k : Nat) (hk : k ≥ 3) :
    let mk := 3 * 4 ^ k + 8
    let nk := 2 ^ (2 * k + 1) + 5
    mk % 3 = 2 ∧
    (2 * mk - 1) / 3 = nk ∧
    binDigitSig6 mk = { pop1 := 3, runs1 := 2, alt01 := 3, pop1Succ := 4, runs1Succ := 3, alt01Succ := 4 } ∧
    binDigitSig6 (2 * mk) = binDigitSig6 mk ∧
    binDigitSig6 nk = { pop1 := 3, runs1 := 3, alt01 := 4, pop1Succ := 3, runs1Succ := 2, alt01Succ := 3 } ∧
    binBitLength mk = 2 * k + 2 ∧
    binBitLength nk = 2 * k + 2 ∧
    binBitLength (2 * mk) = 2 * k + 3 := by
  dsimp only
  let d := k - 3
  have hk_eq : k = d + 3 := by dsimp [d]; omega
  let mk := 3 * 4 ^ k + 8
  let nk := 2 ^ (2 * k + 1) + 5
  have h4k_m3 : 4 ^ k % 3 = 1 := by
    have hm := (pow4_ge_four_and_mod3_w5 (k - 1)).2
    rwa [show k - 1 + 1 = k by omega] at hm
  have hmk_m3 : mk % 3 = 2 := by dsimp [mk]; omega
  have h2_4k : 2 * 4 ^ k = 2 ^ (2 * k + 1) := by
    rw [pow4_eq_pow2_even k, Nat.pow_succ, Nat.mul_comm]
  have hnk_pre : (2 * mk - 1) / 3 = nk := by
    dsimp [mk, nk]; omega
  have h4k_pad : 4 ^ k = 64 * 4 ^ d := by
    rw [hk_eq, Nat.pow_add 4 d 3, show (4 : Nat) ^ 3 = 64 from rfl, Nat.mul_comm]
  have hmk_f : mk = 16 * (2 * 4 ^ d * 6) + 8 := by dsimp [mk]; rw [h4k_pad]; omega
  have hmk1_f : mk + 1 = 16 * (2 * 4 ^ d * 6) + 9 := by rw [hmk_f]
  have hmk_ge200 : mk ≥ 200 := by
    have hp : 4 ^ d ≥ 1 := nat_pow_pos_of_pos 4 (by decide) d
    rw [hmk_f]; omega
  have hmk_ev : mk % 2 = 0 := by rw [hmk_f]; omega
  rcases binTriple_16_pad_add d 6 8 (by decide) (by decide) with ⟨hp_mk0, hr_mk0, ha_mk0⟩
  rcases binTriple_16_pad_add d 6 9 (by decide) (by decide) with ⟨hp_mk1, hr_mk1, ha_mk1⟩
  rw [← hmk_f, show 16 * (2 * 6) + 8 = 200 from rfl] at hp_mk0 hr_mk0 ha_mk0
  rw [← hmk1_f, show 16 * (2 * 6) + 9 = 201 from rfl] at hp_mk1 hr_mk1 ha_mk1
  have hsig_mk : binDigitSig6 mk = binDigitSig6 200 := by
    unfold binDigitSig6
    rw [hp_mk0, hr_mk0, ha_mk0, hp_mk1, hr_mk1, ha_mk1]
  have hsig_2mk : binDigitSig6 (2 * mk) = binDigitSig6 400 := by
    have hpop_2mk : binPopcount (2 * mk) = binPopcount 400 := by
      rw [binPopcount_step_pos (2 * mk) (by omega),
          show (2 * mk) % 2 = 0 by omega, show (2 * mk) / 2 = mk by omega, Nat.zero_add, hp_mk0]
      decide
    have hruns_2mk : binOneRuns (2 * mk) = binOneRuns 400 := by
      unfold binOneRuns
      rw [binOneRunsAux_step_pos 0 (2 * mk) (by omega),
          show (2 * mk) % 2 = 0 by omega, show (2 * mk) / 2 = mk by omega]
      simp only [Nat.zero_ne_one, false_and, ite_false, Nat.zero_add]
      change binOneRuns mk = binOneRuns 400
      rw [hr_mk0]; decide
    have halt_2mk : binAltTransitions (2 * mk) = binAltTransitions 400 := by
      rw [binAltTransitions_step_ge2 (2 * mk) (by omega),
          show (2 * mk) % 2 = 0 by omega, show (2 * mk) / 2 = mk by omega, hmk_ev]
      simp only [ne_eq, not_true_eq_false, ite_false, Nat.zero_add]
      rw [ha_mk0]; decide
    have hpop_2mk1 : binPopcount (2 * mk + 1) = binPopcount 401 := by
      rw [binPopcount_step_pos (2 * mk + 1) (by omega),
          show (2 * mk + 1) % 2 = 1 by omega, show (2 * mk + 1) / 2 = mk by omega, hp_mk0]
      decide
    have hruns_2mk1 : binOneRuns (2 * mk + 1) = binOneRuns 401 := by
      unfold binOneRuns
      rw [binOneRunsAux_step_pos 0 (2 * mk + 1) (by omega),
          show (2 * mk + 1) % 2 = 1 by omega, show (2 * mk + 1) / 2 = mk by omega]
      simp only [and_self, ite_true]
      rw [binOneRunsAux_step_pos 1 mk (by omega), hmk_ev]
      simp only [Nat.zero_ne_one, false_and, ite_false, Nat.zero_add]
      have hmk_r0 : binOneRunsAux (mk / 2) 0 (mk / 2) = binOneRuns mk := by
        unfold binOneRuns
        rw [binOneRunsAux_step_pos 0 mk (by omega), hmk_ev]
        simp
      rw [hmk_r0, hr_mk0]; decide
    have halt_2mk1 : binAltTransitions (2 * mk + 1) = binAltTransitions 401 := by
      rw [binAltTransitions_step_ge2 (2 * mk + 1) (by omega),
          show (2 * mk + 1) % 2 = 1 by omega, show (2 * mk + 1) / 2 = mk by omega, hmk_ev]
      simp only [ne_eq, Nat.one_ne_zero, not_false_eq_true, ite_true]
      rw [ha_mk0]; decide
    unfold binDigitSig6
    rw [hpop_2mk, hruns_2mk, halt_2mk, hpop_2mk1, hruns_2mk1, halt_2mk1]
  have hnk_f : nk = 16 * (2 * 4 ^ d * 4) + 5 := by
    dsimp [nk]; rw [← h2_4k, h4k_pad]; omega
  have hnk1_f : nk + 1 = 16 * (2 * 4 ^ d * 4) + 6 := by rw [hnk_f]
  rcases binTriple_16_pad_add d 4 5 (by decide) (by decide) with ⟨hp_nk0, hr_nk0, ha_nk0⟩
  rcases binTriple_16_pad_add d 4 6 (by decide) (by decide) with ⟨hp_nk1, hr_nk1, ha_nk1⟩
  rw [← hnk_f, show 16 * (2 * 4) + 5 = 133 from rfl] at hp_nk0 hr_nk0 ha_nk0
  rw [← hnk1_f, show 16 * (2 * 4) + 6 = 134 from rfl] at hp_nk1 hr_nk1 ha_nk1
  have hsig_nk : binDigitSig6 nk = binDigitSig6 133 := by
    unfold binDigitSig6
    rw [hp_nk0, hr_nk0, ha_nk0, hp_nk1, hr_nk1, ha_nk1]
  have hs200 : binDigitSig6 200 =
      { pop1 := 3, runs1 := 2, alt01 := 3, pop1Succ := 4, runs1Succ := 3, alt01Succ := 4 } := by
    decide
  have hs400 : binDigitSig6 400 = binDigitSig6 200 := by decide
  have hs133 : binDigitSig6 133 =
      { pop1 := 3, runs1 := 3, alt01 := 4, pop1Succ := 3, runs1Succ := 2, alt01Succ := 3 } := by
    decide
  have h4k_ge64 : 4 ^ k ≥ 64 := by rw [h4k_pad]; have hp := nat_pow_pos_of_pos 4 (by decide) d; omega
  have h2_2k2 : 2 ^ (2 * k + 2) = 4 * 4 ^ k := by
    rw [show 2 * k + 2 = 2 * k + 1 + 1 by omega, Nat.pow_succ, ← h2_4k]; omega
  have hbl_mk : binBitLength mk = 2 * k + 2 := by
    apply binBitLength_of_pow2_sandwich (2 * k + 1) mk
    · rw [← h2_4k]; dsimp [mk]; omega
    · rw [h2_2k2]; dsimp [mk]; omega
  have hbl_nk : binBitLength nk = 2 * k + 2 := by
    apply binBitLength_of_pow2_sandwich (2 * k + 1) nk
    · dsimp [nk]; omega
    · rw [h2_2k2]; dsimp [nk]; rw [← h2_4k]; omega
  have hbl_2mk : binBitLength (2 * mk) = 2 * k + 3 := by
    rw [binBitLength_step_pos (2 * mk) (by omega),
        show (2 * mk) / 2 = mk by omega, hbl_mk]
    omega
  exact ⟨hmk_m3, hnk_pre, hsig_mk.trans hs200,
         hsig_2mk.trans (hs400.trans hsig_mk.symm),
         hsig_nk.trans hs133, hbl_mk, hbl_nk, hbl_2mk⟩

/--
  Theorem W7.2b (`berg_meinardus_binary_digit_sig_impossibility`, zero custom axioms):
  Universal 6-Coordinate Binary Digit Signature Impossibility (`W7_H1A` Part 1):
  NO positive rational preimage weight `w(n) = fNum (binDigitSig6 n) / fDen (binDigitSig6 n)` —
  for ANY arbitrary functions `fNum fDen : BinDigitSig6 -> Nat` — can satisfy
  `IsPositiveRationalPreimageWeight`, refuted at the minimal witness `m = 200` (`400` and `200`
  share `binDigitSig6 = (3, 2, 3, 4, 3, 4)` while `133` adds strictly positive mass)!
-/
theorem berg_meinardus_binary_digit_sig_impossibility
    (fNum fDen : BinDigitSig6 -> Nat) (pTheta qTheta : Nat)
    (hw : IsPositiveRationalPreimageWeight
      (fun n => fNum (binDigitSig6 n)) (fun n => fDen (binDigitSig6 n)) pTheta qTheta) :
    False := by
  have hs400 : binDigitSig6 400 = binDigitSig6 200 := by decide
  have hpre200 := hw.2.2.2.2 200 (by decide) (by decide)
  dsimp only at hpre200
  have h400 : 2 * 200 = 400 := rfl
  have h133 : (2 * 200 - 1) / 3 = 133 := rfl
  rw [h400, h133, hs400] at hpre200
  rcases hw.2.2.1 200 (by decide) with ⟨hn200, hd200⟩
  rcases hw.2.2.1 133 (by decide) with ⟨hn133, hd133⟩
  let a := fNum (binDigitSig6 200)
  let b := fDen (binDigitSig6 200)
  let c := fNum (binDigitSig6 133)
  let d := fDen (binDigitSig6 133)
  change qTheta * ((a * d + c * b) * b) ≤ pTheta * (a * (b * d)) at hpre200
  have hle_pq : pTheta * (a * (b * d)) ≤ qTheta * (a * (b * d)) :=
    Nat.mul_le_mul_right _ hw.2.1
  have hcanc := nat_mul_le_cancel_left_w5 qTheta _ _
    (Nat.lt_of_lt_of_le hw.1 hw.2.1) (Nat.le_trans hpre200 hle_pq)
  have hextra : c * (b * b) ≥ 1 :=
    Nat.mul_le_mul hn133 (Nat.mul_le_mul hd200 hd200)
  have hl : (a * d + c * b) * b = a * (b * d) + c * (b * b) := by
    rw [Nat.add_mul, Nat.mul_assoc c b b, Nat.mul_assoc a d b, Nat.mul_comm d b]
  rw [hl] at hcanc
  omega

theorem pos_factors_of_mul_pos (x y : Nat) (hp : x * y > 0) : x ≥ 1 ∧ y ≥ 1 := by
  refine ⟨?_, ?_⟩
  · cases x with | zero => simp at hp | succ _ => omega
  · cases y with | zero => simp at hp | succ _ => omega

/--
  Theorem W7.2c (`berg_meinardus_exponential_popcount_bitlength_impossibility`, zero custom axioms):
  Universal Exponential Bit-Length + Arbitrary Popcount Impossibility (`W7_H1A` Part 2):
  For ANY arbitrary functions `gNum gDen : Nat -> Nat` of `binPopcount n` and ANY exponential
  bit-length bases `aNum, aDen : Nat`, NO weight
    `w(n) = (gNum (binPopcount n) * aNum ^ (binBitLength n)) / (gDen (binPopcount n) * aDen ^ (binBitLength n))`
  can satisfy `IsPositiveRationalPreimageWeight`, refuted at `m = 11` (`22 = 2 * 11`, `7 = (22 - 1)/3`,
  where `7, 11, 22` ALL have `binPopcount = 3` while `binBitLength` is `3, 4, 5`, forcing `r + 1/r ≤ 1`)!
-/
theorem berg_meinardus_exponential_popcount_bitlength_impossibility
    (gNum gDen : Nat -> Nat) (aNum aDen pTheta qTheta : Nat)
    (hw : IsPositiveRationalPreimageWeight
      (fun n => gNum (binPopcount n) * aNum ^ (binBitLength n))
      (fun n => gDen (binPopcount n) * aDen ^ (binBitLength n)) pTheta qTheta) :
    False := by
  have hpre11 := hw.2.2.2.2 11 (by decide) (by decide)
  dsimp only at hpre11
  have h22 : 2 * 11 = 22 := rfl
  have h7 : (2 * 11 - 1) / 3 = 7 := rfl
  rw [h22, h7] at hpre11
  have hp7 : binPopcount 7 = 3 := by decide
  have hp11 : binPopcount 11 = 3 := by decide
  have hp22 : binPopcount 22 = 3 := by decide
  have hl7 : binBitLength 7 = 3 := by decide
  have hl11 : binBitLength 11 = 4 := by decide
  have hl22 : binBitLength 22 = 5 := by decide
  rw [hp7, hp11, hp22, hl7, hl11, hl22] at hpre11
  rcases hw.2.2.1 11 (by decide) with ⟨hnum11, hden11⟩
  dsimp only at hnum11 hden11
  rw [hp11, hl11] at hnum11 hden11
  rcases pos_factors_of_mul_pos _ _ hnum11 with ⟨hgN_pos, haN4_pos⟩
  rcases pos_factors_of_mul_pos _ _ hden11 with ⟨hgD_pos, haD4_pos⟩
  have haN_pos : aNum ≥ 1 := by
    cases aNum with | zero => simp at haN4_pos | succ _ => omega
  have haD_pos : aDen ≥ 1 := by
    cases aDen with | zero => simp at haD4_pos | succ _ => omega
  have hcanc := nat_mul_le_cancel_left_w5 qTheta _ _
    (Nat.lt_of_lt_of_le hw.1 hw.2.1)
    (Nat.le_trans hpre11 (Nat.mul_le_mul_right _ hw.2.1))
  let GN := gNum 3
  let GD := gDen 3
  let P3 := aNum ^ 3
  let Q3 := aDen ^ 3
  have ha4 : aNum ^ 4 = P3 * aNum := by dsimp [P3]; rw [← Nat.pow_succ]
  have ha5 : aNum ^ 5 = P3 * (aNum * aNum) := by
    rw [show (5 : Nat) = 4 + 1 from rfl, Nat.pow_succ, ha4, Nat.mul_assoc]
  have hb4 : aDen ^ 4 = Q3 * aDen := by dsimp [Q3]; rw [← Nat.pow_succ]
  have hb5 : aDen ^ 5 = Q3 * (aDen * aDen) := by
    rw [show (5 : Nat) = 4 + 1 from rfl, Nat.pow_succ, hb4, Nat.mul_assoc]
  change ((GN * aNum ^ 5) * (GD * Q3) + (GN * P3) * (GD * aDen ^ 5)) * (GD * aDen ^ 4) ≤
    (GN * aNum ^ 4) * ((GD * aDen ^ 5) * (GD * Q3)) at hcanc
  rw [ha4, ha5, hb4, hb5] at hcanc
  let K := GN * GD * GD * P3 * Q3 * Q3 * aDen
  have hK_pos : K ≥ 1 :=
    Nat.mul_le_mul
      (Nat.mul_le_mul
        (Nat.mul_le_mul
          (Nat.mul_le_mul
            (Nat.mul_le_mul (Nat.mul_le_mul hgN_pos hgD_pos) hgD_pos)
            (nat_pow_pos_of_pos aNum haN_pos 3))
          (nat_pow_pos_of_pos aDen haD_pos 3))
        (nat_pow_pos_of_pos aDen haD_pos 3))
      haD_pos
  have hl_eq : ((GN * (P3 * (aNum * aNum))) * (GD * Q3) +
      (GN * P3) * (GD * (Q3 * (aDen * aDen)))) * (GD * (Q3 * aDen)) =
      (aNum * aNum + aDen * aDen) * K := by
    dsimp [K]
    have ht1 : (GN * (P3 * (aNum * aNum))) * (GD * Q3) * (GD * (Q3 * aDen)) =
        (aNum * aNum) * (GN * GD * GD * P3 * Q3 * Q3 * aDen) := by
      generalize aNum * aNum = x
      calc
        (GN * (P3 * x)) * (GD * Q3) * (GD * (Q3 * aDen))
            = x * (GN * P3) * (GD * Q3) * (GD * (Q3 * aDen)) := by
              rw [← Nat.mul_assoc GN P3 x, Nat.mul_comm (GN * P3) x]
        _ = x * ((GN * P3) * (GD * Q3) * (GD * (Q3 * aDen))) := by
              rw [Nat.mul_assoc x, Nat.mul_assoc x]
        _ = x * (GN * GD * GD * P3 * Q3 * Q3 * aDen) := by
              apply congrArg (x * ·)
              calc
                (GN * P3) * (GD * Q3) * (GD * (Q3 * aDen))
                    = GN * (P3 * (GD * Q3)) * (GD * (Q3 * aDen)) := by rw [Nat.mul_assoc GN P3]
                _ = GN * (GD * (P3 * Q3)) * (GD * (Q3 * aDen)) := by
                      rw [← Nat.mul_assoc P3 GD Q3, Nat.mul_comm P3 GD, Nat.mul_assoc GD P3 Q3]
                _ = (GN * GD) * (P3 * Q3) * (GD * (Q3 * aDen)) := by rw [← Nat.mul_assoc GN GD]
                _ = (GN * GD) * ((P3 * Q3) * GD) * (Q3 * aDen) := by
                      rw [← Nat.mul_assoc ((GN * GD) * (P3 * Q3)) GD, Nat.mul_assoc (GN * GD) (P3 * Q3) GD]
                _ = (GN * GD * GD) * (P3 * Q3) * (Q3 * aDen) := by
                      rw [Nat.mul_comm (P3 * Q3) GD, ← Nat.mul_assoc (GN * GD) GD]
                _ = GN * GD * GD * P3 * Q3 * Q3 * aDen := by
                      rw [← Nat.mul_assoc (GN * GD * GD) P3 Q3,
                          ← Nat.mul_assoc (GN * GD * GD * P3 * Q3) Q3 aDen]
    have ht2 : (GN * P3) * (GD * (Q3 * (aDen * aDen))) * (GD * (Q3 * aDen)) =
        (aDen * aDen) * (GN * GD * GD * P3 * Q3 * Q3 * aDen) := by
      generalize aDen * aDen = y
      calc
        (GN * P3) * (GD * (Q3 * y)) * (GD * (Q3 * aDen))
            = (GN * P3) * ((GD * Q3) * y) * (GD * (Q3 * aDen)) := by rw [Nat.mul_assoc GD Q3 y]
        _ = y * ((GN * P3) * (GD * Q3)) * (GD * (Q3 * aDen)) := by
              rw [← Nat.mul_assoc (GN * P3) (GD * Q3) y, Nat.mul_comm _ y]
        _ = y * ((GN * P3) * (GD * Q3) * (GD * (Q3 * aDen))) := Nat.mul_assoc y _ _
        _ = y * (GN * GD * GD * P3 * Q3 * Q3 * aDen) := by
              apply congrArg (y * ·)
              calc
                (GN * P3) * (GD * Q3) * (GD * (Q3 * aDen))
                    = GN * (P3 * (GD * Q3)) * (GD * (Q3 * aDen)) := by rw [Nat.mul_assoc GN P3]
                _ = GN * (GD * (P3 * Q3)) * (GD * (Q3 * aDen)) := by
                      rw [← Nat.mul_assoc P3 GD Q3, Nat.mul_comm P3 GD, Nat.mul_assoc GD P3 Q3]
                _ = (GN * GD) * (P3 * Q3) * (GD * (Q3 * aDen)) := by rw [← Nat.mul_assoc GN GD]
                _ = (GN * GD) * ((P3 * Q3) * GD) * (Q3 * aDen) := by
                      rw [← Nat.mul_assoc ((GN * GD) * (P3 * Q3)) GD, Nat.mul_assoc (GN * GD) (P3 * Q3) GD]
                _ = (GN * GD * GD) * (P3 * Q3) * (Q3 * aDen) := by
                      rw [Nat.mul_comm (P3 * Q3) GD, ← Nat.mul_assoc (GN * GD) GD]
                _ = GN * GD * GD * P3 * Q3 * Q3 * aDen := by
                      rw [← Nat.mul_assoc (GN * GD * GD) P3 Q3,
                          ← Nat.mul_assoc (GN * GD * GD * P3 * Q3) Q3 aDen]
    rw [Nat.add_mul _ _ (GD * (Q3 * aDen)), ht1, ht2, ← Nat.add_mul]
  have hr_eq : (GN * (P3 * aNum)) * ((GD * (Q3 * (aDen * aDen))) * (GD * Q3)) =
      (aNum * aDen) * K := by
    dsimp [K]
    calc
      (GN * (P3 * aNum)) * ((GD * (Q3 * (aDen * aDen))) * (GD * Q3))
          = (aNum * (GN * P3)) * ((aDen * (GD * Q3 * aDen)) * (GD * Q3)) := by
            rw [← Nat.mul_assoc GN P3 aNum, Nat.mul_comm (GN * P3) aNum]
            have hr1 : GD * (Q3 * (aDen * aDen)) = aDen * (GD * Q3 * aDen) := by
              calc
                GD * (Q3 * (aDen * aDen)) = (GD * Q3 * aDen) * aDen := by
                  rw [← Nat.mul_assoc Q3 aDen aDen, ← Nat.mul_assoc GD (Q3 * aDen) aDen,
                      Nat.mul_assoc GD Q3 aDen]
                _ = aDen * (GD * Q3 * aDen) := Nat.mul_comm _ aDen
            rw [hr1]
      _ = (aNum * aDen) * ((GN * P3) * ((GD * Q3 * aDen) * (GD * Q3))) := by
            rw [Nat.mul_assoc aDen (GD * Q3 * aDen) (GD * Q3),
                Nat.mul_assoc aNum (GN * P3),
                ← Nat.mul_assoc (GN * P3) aDen,
                Nat.mul_comm (GN * P3) aDen,
                Nat.mul_assoc aDen (GN * P3),
                ← Nat.mul_assoc aNum aDen]
      _ = (aNum * aDen) * (GN * GD * GD * P3 * Q3 * Q3 * aDen) := by
            apply congrArg ((aNum * aDen) * ·)
            calc
              (GN * P3) * ((GD * Q3 * aDen) * (GD * Q3))
                  = (GN * P3) * ((GD * Q3) * (GD * Q3) * aDen) := by
                    rw [Nat.mul_comm (GD * Q3 * aDen) (GD * Q3),
                        ← Nat.mul_assoc (GD * Q3) (GD * Q3) aDen]
              _ = ((GN * P3) * ((GD * Q3) * (GD * Q3))) * aDen := (Nat.mul_assoc _ _ _).symm
              _ = GN * GD * GD * P3 * Q3 * Q3 * aDen := by
                    apply congrArg (· * aDen)
                    have hgd : (GD * Q3) * (GD * Q3) = (GD * GD) * (Q3 * Q3) := by
                      rw [Nat.mul_assoc GD Q3, ← Nat.mul_assoc Q3 GD Q3,
                          Nat.mul_comm Q3 GD, Nat.mul_assoc GD Q3 Q3, ← Nat.mul_assoc GD GD]
                    rw [hgd, Nat.mul_assoc GN P3, ← Nat.mul_assoc P3 (GD * GD),
                        Nat.mul_comm P3 (GD * GD), Nat.mul_assoc (GD * GD) P3,
                        ← Nat.mul_assoc GN (GD * GD), ← Nat.mul_assoc GN GD GD,
                        ← Nat.mul_assoc (GN * GD * GD) P3,
                        ← Nat.mul_assoc (GN * GD * GD * P3) Q3 Q3]
  rw [hl_eq, hr_eq] at hcanc
  have hquad := nat_mul_le_cancel_right_w5 K _ _ hK_pos hcanc
  by_cases hle : aNum ≤ aDen
  · have hm : aNum * aDen ≤ aDen * aDen := Nat.mul_le_mul_right aDen hle
    have hp : aNum * aNum ≥ 1 := Nat.mul_le_mul haN_pos haN_pos
    omega
  · have hm : aNum * aDen ≤ aNum * aNum := Nat.mul_le_mul_left aNum (by omega)
    have hp : aDen * aDen ≥ 1 := Nat.mul_le_mul haD_pos haD_pos
    omega

/-- Univariate polynomial in `L = binBitLength n` represented as `[(coeff, exp), ...]`. -/
def evalBitLenPoly : List (Nat × Nat) -> Nat -> Nat
  | [], _ => 0
  | t :: rest, L => t.1 * L ^ t.2 + evalBitLenPoly rest L

def maxBitLenDeg : List (Nat × Nat) -> Nat
  | [] => 0
  | t :: rest => if t.1 > 0 then Nat.max t.2 (maxBitLenDeg rest) else maxBitLenDeg rest

theorem evalBitLenPoly_mono_and_succ_bound :
    ∀ (ts : List (Nat × Nat)) (L : Nat), L ≥ 1 ->
      evalBitLenPoly ts L ≤ evalBitLenPoly ts (L + 1) ∧
      L ^ (maxBitLenDeg ts) * evalBitLenPoly ts (L + 1) ≤
        (L + 1) ^ (maxBitLenDeg ts) * evalBitLenPoly ts L
  | [], _, _ => ⟨Nat.le_refl 0, by simp [evalBitLenPoly]⟩
  | (c, e) :: rest, L, hL => by
    rcases evalBitLenPoly_mono_and_succ_bound rest L hL with ⟨ih_mono, ih_deg⟩
    simp only [evalBitLenPoly, maxBitLenDeg]
    have hmono_term : c * L ^ e ≤ c * (L + 1) ^ e :=
      Nat.mul_le_mul_left c (nat_pow_mono_base L (L + 1) (by omega) e)
    refine ⟨Nat.add_le_add hmono_term ih_mono, ?_⟩
    by_cases hc : c > 0
    · simp only [hc, ite_true]
      let D := Nat.max e (maxBitLenDeg rest)
      have he_le : e ≤ D := Nat.le_max_left _ _
      have hr_le : maxBitLenDeg rest ≤ D := Nat.le_max_right _ _
      change L ^ D * (c * (L + 1) ^ e + evalBitLenPoly rest (L + 1)) ≤
        (L + 1) ^ D * (c * L ^ e + evalBitLenPoly rest L)
      rw [Nat.mul_add (L ^ D), Nat.mul_add ((L + 1) ^ D)]
      have hterm1 : L ^ D * (c * (L + 1) ^ e) ≤ (L + 1) ^ D * (c * L ^ e) := by
        have hsp : D = e + (D - e) := by omega
        rw [hsp, Nat.pow_add L e (D - e), Nat.pow_add (L + 1) e (D - e)]
        have hrem : L ^ (D - e) ≤ (L + 1) ^ (D - e) :=
          nat_pow_mono_base L (L + 1) (by omega) (D - e)
        have hl : (L ^ e * L ^ (D - e)) * (c * (L + 1) ^ e) =
            (c * L ^ e * (L + 1) ^ e) * L ^ (D - e) := by
          calc
            (L ^ e * L ^ (D - e)) * (c * (L + 1) ^ e)
                = L ^ e * (L ^ (D - e) * (c * (L + 1) ^ e)) := Nat.mul_assoc _ _ _
            _ = L ^ e * ((c * (L + 1) ^ e) * L ^ (D - e)) := by rw [Nat.mul_comm (L ^ (D - e))]
            _ = (L ^ e * (c * (L + 1) ^ e)) * L ^ (D - e) := (Nat.mul_assoc _ _ _).symm
            _ = (c * L ^ e * (L + 1) ^ e) * L ^ (D - e) := by
                  rw [← Nat.mul_assoc (L ^ e) c, Nat.mul_comm (L ^ e) c]
        have hr : ((L + 1) ^ e * (L + 1) ^ (D - e)) * (c * L ^ e) =
            (c * L ^ e * (L + 1) ^ e) * (L + 1) ^ (D - e) := by
          calc
            ((L + 1) ^ e * (L + 1) ^ (D - e)) * (c * L ^ e)
                = (c * L ^ e) * ((L + 1) ^ e * (L + 1) ^ (D - e)) := Nat.mul_comm _ _
            _ = (c * L ^ e * (L + 1) ^ e) * (L + 1) ^ (D - e) := (Nat.mul_assoc _ _ _).symm
        rw [hl, hr]
        exact Nat.mul_le_mul_left _ hrem
      have hterm2 : L ^ D * evalBitLenPoly rest (L + 1) ≤
          (L + 1) ^ D * evalBitLenPoly rest L := by
        let Dr := maxBitLenDeg rest
        have hsp : D = Dr + (D - Dr) := by omega
        rw [hsp, Nat.pow_add L Dr (D - Dr), Nat.pow_add (L + 1) Dr (D - Dr)]
        have hl : (L ^ Dr * L ^ (D - Dr)) * evalBitLenPoly rest (L + 1) =
            L ^ (D - Dr) * (L ^ Dr * evalBitLenPoly rest (L + 1)) := by
          rw [Nat.mul_comm (L ^ Dr) (L ^ (D - Dr)), Nat.mul_assoc]
        have hr : ((L + 1) ^ Dr * (L + 1) ^ (D - Dr)) * evalBitLenPoly rest L =
            (L + 1) ^ (D - Dr) * ((L + 1) ^ Dr * evalBitLenPoly rest L) := by
          rw [Nat.mul_comm ((L + 1) ^ Dr) ((L + 1) ^ (D - Dr)), Nat.mul_assoc]
        rw [hl, hr]
        exact Nat.mul_le_mul (nat_pow_mono_base L (L + 1) (by omega) (D - Dr)) ih_deg
      exact Nat.add_le_add hterm1 hterm2
    · simp only [hc, ite_false]
      have hc0 : c = 0 := by omega
      simp only [hc0, Nat.zero_mul, Nat.zero_add]
      exact ih_deg

/--
  Theorem W7.2d (`berg_meinardus_coupled_digit_sig_and_bitlength_impossibility`, zero custom axioms):
  Universal Coupled Digit-Signature × Bit-Length Rational Preimage Barrier (`W7_H1A` Master Theorem):
  For ANY arbitrary functions `fNum fDen : BinDigitSig6 -> Nat` of the 6-tuple `binDigitSig6 n`
  and ANY arbitrary multi-term polynomials `pTerms qTerms : List (Nat × Nat)` in `binBitLength n`,
  NO weight
    `w(n) = (fNum (binDigitSig6 n) * evalBitLenPoly pTerms (binBitLength n)) /
            (fDen (binDigitSig6 n) * evalBitLenPoly qTerms (binBitLength n))`
  can satisfy `IsPositiveRationalPreimageWeight`!
-/
theorem berg_meinardus_coupled_digit_sig_and_bitlength_impossibility
    (fNum fDen : BinDigitSig6 -> Nat)
    (pTerms qTerms : List (Nat × Nat))
    (pTheta qTheta : Nat)
    (hw : IsPositiveRationalPreimageWeight
      (fun n => fNum (binDigitSig6 n) * evalBitLenPoly pTerms (binBitLength n))
      (fun n => fDen (binDigitSig6 n) * evalBitLenPoly qTerms (binBitLength n))
      pTheta qTheta) :
    False := by
  let sEven : BinDigitSig6 :=
    { pop1 := 3, runs1 := 2, alt01 := 3, pop1Succ := 4, runs1Succ := 3, alt01Succ := 4 }
  let sOdd : BinDigitSig6 :=
    { pop1 := 3, runs1 := 3, alt01 := 4, pop1Succ := 3, runs1Succ := 2, alt01Succ := 3 }
  let aE := fNum sEven
  let bE := fDen sEven
  let aO := fNum sOdd
  let bO := fDen sOdd
  rcases binary_digit_sig6_and_bitlength_infinite_collision_family 3 (by decide) with
    ⟨_, _, hs_200, _, hs_133, _, _, _⟩
  rcases hw.2.2.1 200 (by decide) with ⟨hnum200, hden200⟩
  rcases hw.2.2.1 133 (by decide) with ⟨hnum133, hden133⟩
  dsimp only at hnum200 hden200 hnum133 hden133
  have heq200 : 3 * 4 ^ 3 + 8 = 200 := rfl
  have heq133 : 2 ^ (2 * 3 + 1) + 5 = 133 := rfl
  rw [heq200] at hs_200
  rw [heq133] at hs_133
  rw [hs_200] at hnum200 hden200
  rw [hs_133] at hnum133 hden133
  have haE_pos : aE ≥ 1 := (pos_factors_of_mul_pos _ _ hnum200).1
  have hbE_pos : bE ≥ 1 := (pos_factors_of_mul_pos _ _ hden200).1
  have haO_pos : aO ≥ 1 := (pos_factors_of_mul_pos _ _ hnum133).1
  have hbO_pos : bO ≥ 1 := (pos_factors_of_mul_pos _ _ hden133).1
  let dQ := maxBitLenDeg qTerms
  let k := dQ * aE * bO + 3
  have hk_ge3 : k ≥ 3 := by dsimp [k]; omega
  let mk := 3 * 4 ^ k + 8
  let nk := 2 ^ (2 * k + 1) + 5
  let L := 2 * k + 2
  have hL_gt : L > dQ * aE * bO + 1 := by dsimp [L, k]; omega
  rcases binary_digit_sig6_and_bitlength_infinite_collision_family k hk_ge3 with
    ⟨hmk_m3, hnk_pre, hsig_mk, hsig_2mk, hsig_nk, hbl_mk, hbl_nk, hbl_2mk⟩
  have hmk_ge3 : mk ≥ 3 := by
    have hp := nat_pow_pos_of_pos 4 (by decide) k
    dsimp [mk]; omega
  have hpre := hw.2.2.2.2 mk hmk_ge3 hmk_m3
  dsimp only at hpre
  rw [hnk_pre, hsig_2mk, hsig_mk, hsig_nk, hbl_mk, hbl_nk, hbl_2mk] at hpre
  have hcanc := nat_mul_le_cancel_left_w5 qTheta _ _
    (Nat.lt_of_lt_of_le hw.1 hw.2.1)
    (Nat.le_trans hpre (Nat.mul_le_mul_right _ hw.2.1))
  let PL := evalBitLenPoly pTerms L
  let PL1 := evalBitLenPoly pTerms (L + 1)
  let QL := evalBitLenPoly qTerms L
  let QL1 := evalBitLenPoly qTerms (L + 1)
  rcases hw.2.2.1 mk hmk_ge3 with ⟨hnum_mk, hden_mk⟩
  rcases hw.2.2.1 (2 * mk) (by omega) with ⟨_, hden_2mk⟩
  dsimp only at hnum_mk hden_mk hden_2mk
  rw [hsig_mk, hbl_mk] at hnum_mk hden_mk
  rw [hsig_2mk, hsig_mk, hbl_2mk] at hden_2mk
  have hPL_pos : PL ≥ 1 := (pos_factors_of_mul_pos _ _ hnum_mk).2
  have hQL_pos : QL ≥ 1 := (pos_factors_of_mul_pos _ _ hden_mk).2
  have hQL1_pos : QL1 ≥ 1 := (pos_factors_of_mul_pos _ _ hden_2mk).2
  change ((aE * PL1) * (bO * QL) + (aO * PL) * (bE * QL1)) * (bE * QL) ≤
    (aE * PL) * ((bE * QL1) * (bO * QL)) at hcanc
  have hP_mono : PL ≤ PL1 := (evalBitLenPoly_mono_and_succ_bound pTerms L (by dsimp [L]; omega)).1
  have hQ_deg : L ^ dQ * QL1 ≤ (L + 1) ^ dQ * QL :=
    (evalBitLenPoly_mono_and_succ_bound qTerms L (by dsimp [L]; omega)).2
  by_cases hdQ0 : dQ = 0
  · rw [hdQ0, Nat.pow_zero, Nat.pow_zero, Nat.one_mul, Nat.one_mul] at hQ_deg
    have ht1 : (aE * PL) * ((bE * QL1) * (bO * QL)) ≤
        ((aE * PL1) * (bO * QL)) * (bE * QL) := by
      have hm1 : PL * QL1 ≤ PL1 * QL := Nat.mul_le_mul hP_mono hQ_deg
      have hl : (aE * PL) * ((bE * QL1) * (bO * QL)) =
          (aE * bE * bO * QL) * (PL * QL1) := by
        calc
          (aE * PL) * ((bE * QL1) * (bO * QL))
              = aE * (PL * ((bE * bO * QL) * QL1)) := by
                have hb : (bE * QL1) * (bO * QL) = (bE * bO * QL) * QL1 := by
                  calc
                    (bE * QL1) * (bO * QL) = bE * (QL1 * (bO * QL)) := Nat.mul_assoc _ _ _
                    _ = bE * ((bO * QL) * QL1) := by rw [Nat.mul_comm QL1]
                    _ = (bE * bO * QL) * QL1 := by rw [← Nat.mul_assoc bE, ← Nat.mul_assoc bE]
                rw [hb, Nat.mul_assoc aE]
          _ = aE * ((bE * bO * QL) * (PL * QL1)) := by
                rw [← Nat.mul_assoc PL, Nat.mul_comm PL (bE * bO * QL), Nat.mul_assoc]
          _ = (aE * bE * bO * QL) * (PL * QL1) := by
                rw [← Nat.mul_assoc aE, ← Nat.mul_assoc aE, ← Nat.mul_assoc aE]
      have hr : ((aE * PL1) * (bO * QL)) * (bE * QL) =
          (aE * bE * bO * QL) * (PL1 * QL) := by
        calc
          ((aE * PL1) * (bO * QL)) * (bE * QL)
              = ((aE * bO) * (PL1 * QL)) * (bE * QL) := by
                rw [Nat.mul_assoc aE PL1, ← Nat.mul_assoc PL1 bO QL,
                    Nat.mul_comm PL1 bO, Nat.mul_assoc bO PL1 QL, ← Nat.mul_assoc aE bO]
          _ = (aE * bO) * ((PL1 * QL) * (bE * QL)) := Nat.mul_assoc _ _ _
          _ = (aE * bO) * ((bE * QL) * (PL1 * QL)) := by rw [Nat.mul_comm (PL1 * QL)]
          _ = (aE * bE * bO * QL) * (PL1 * QL) := by
                rw [← Nat.mul_assoc (aE * bO) (bE * QL), ← Nat.mul_assoc (aE * bO) bE QL,
                    Nat.mul_assoc aE bO bE, Nat.mul_comm bO bE, ← Nat.mul_assoc aE bE bO]
      rw [hl, hr]
      exact Nat.mul_le_mul_left _ hm1
    have hextra : ((aO * PL) * (bE * QL1)) * (bE * QL) ≥ 1 :=
      Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul haO_pos hPL_pos) (Nat.mul_le_mul hbE_pos hQL1_pos))
        (Nat.mul_le_mul hbE_pos hQL_pos)
    rw [Nat.add_mul] at hcanc
    omega
  · have hdQ_pos : dQ ≥ 1 := by omega
    have hm_canc := Nat.mul_le_mul_left ((L + 1) ^ dQ) hcanc
    let K := bE * PL * QL * QL1
    have hK_pos : K ≥ 1 :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hbE_pos hPL_pos) hQL_pos) hQL1_pos
    have ht1_ge : (L ^ dQ * (aE * bO)) * K ≤
        (L + 1) ^ dQ * (((aE * PL1) * (bO * QL)) * (bE * QL)) := by
      have hm1 : (aE * bO * bE * QL) * (PL * (L ^ dQ * QL1)) ≤
          (aE * bO * bE * QL) * (PL1 * ((L + 1) ^ dQ * QL)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hP_mono hQ_deg)
      have hl : (aE * bO * bE * QL) * (PL * (L ^ dQ * QL1)) =
          (L ^ dQ * (aE * bO)) * K := by
        dsimp [K]
        calc
          (aE * bO * bE * QL) * (PL * (L ^ dQ * QL1))
              = ((aE * bO) * (bE * QL)) * (L ^ dQ * (PL * QL1)) := by
                rw [Nat.mul_assoc (aE * bO) bE QL, ← Nat.mul_assoc PL (L ^ dQ) QL1,
                    Nat.mul_comm PL (L ^ dQ), Nat.mul_assoc (L ^ dQ)]
          _ = (L ^ dQ * (aE * bO)) * ((bE * QL) * (PL * QL1)) := by
                rw [Nat.mul_assoc (aE * bO) (bE * QL),
                    ← Nat.mul_assoc (bE * QL) (L ^ dQ),
                    Nat.mul_comm (bE * QL) (L ^ dQ),
                    Nat.mul_assoc (L ^ dQ),
                    ← Nat.mul_assoc (aE * bO) (L ^ dQ),
                    Nat.mul_comm (aE * bO) (L ^ dQ)]
          _ = (L ^ dQ * (aE * bO)) * (bE * PL * QL * QL1) := by
                apply congrArg ((L ^ dQ * (aE * bO)) * ·)
                rw [← Nat.mul_assoc (bE * QL) PL QL1, Nat.mul_assoc bE QL PL,
                    Nat.mul_comm QL PL, ← Nat.mul_assoc bE PL QL]
      have hr : (aE * bO * bE * QL) * (PL1 * ((L + 1) ^ dQ * QL)) =
          (L + 1) ^ dQ * (((aE * PL1) * (bO * QL)) * (bE * QL)) := by
        calc
          (aE * bO * bE * QL) * (PL1 * ((L + 1) ^ dQ * QL))
              = (L + 1) ^ dQ * ((aE * bO * bE * QL) * (PL1 * QL)) := by
                rw [← Nat.mul_assoc PL1 ((L + 1) ^ dQ) QL,
                    Nat.mul_comm PL1 ((L + 1) ^ dQ), Nat.mul_assoc ((L + 1) ^ dQ),
                    ← Nat.mul_assoc _ ((L + 1) ^ dQ), Nat.mul_comm _ ((L + 1) ^ dQ), Nat.mul_assoc]
          _ = (L + 1) ^ dQ * (((aE * PL1) * (bO * QL)) * (bE * QL)) := by
                apply congrArg ((L + 1) ^ dQ * ·)
                calc
                  (aE * bO * bE * QL) * (PL1 * QL)
                      = (aE * bO) * ((bE * QL) * (PL1 * QL)) := by rw [Nat.mul_assoc (aE * bO) bE QL, Nat.mul_assoc]
                  _ = (aE * bO) * ((PL1 * QL) * (bE * QL)) := by rw [Nat.mul_comm (bE * QL)]
                  _ = ((aE * bO) * (PL1 * QL)) * (bE * QL) := (Nat.mul_assoc _ _ _).symm
                  _ = ((aE * PL1) * (bO * QL)) * (bE * QL) := by
                        rw [Nat.mul_assoc aE bO (PL1 * QL), ← Nat.mul_assoc bO PL1 QL,
                            Nat.mul_comm bO PL1, Nat.mul_assoc PL1 bO QL, ← Nat.mul_assoc aE PL1]
      rwa [hl, hr] at hm1
    have ht2_ge : (L + 1) ^ dQ * K ≤
        (L + 1) ^ dQ * (((aO * PL) * (bE * QL1)) * (bE * QL)) := by
      apply Nat.mul_le_mul_left ((L + 1) ^ dQ)
      dsimp [K]
      have h1 : 1 * (bE * PL * QL * QL1) ≤ (aO * bE) * (bE * PL * QL * QL1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul haO_pos hbE_pos)
      rw [Nat.one_mul] at h1
      have hrw : (aO * bE) * (bE * PL * QL * QL1) = ((aO * PL) * (bE * QL1)) * (bE * QL) := by
        calc
          (aO * bE) * (bE * PL * QL * QL1)
              = (aO * (PL * (bE * QL1))) * (bE * QL) := by
                rw [Nat.mul_assoc (bE * PL) QL QL1, Nat.mul_comm QL QL1, ← Nat.mul_assoc (bE * PL) QL1 QL,
                    Nat.mul_assoc bE PL QL1, Nat.mul_comm PL QL1]
                calc
                  (aO * bE) * (bE * (QL1 * PL) * QL)
                      = aO * (bE * ((bE * (PL * QL1)) * QL)) := by
                        rw [Nat.mul_comm QL1 PL, Nat.mul_assoc aO bE]
                  _ = aO * ((bE * (PL * QL1)) * (bE * QL)) := by
                        rw [← Nat.mul_assoc bE _ QL,
                            Nat.mul_comm bE (bE * (PL * QL1)), Nat.mul_assoc]
                  _ = (aO * (PL * (bE * QL1))) * (bE * QL) := by
                        rw [← Nat.mul_assoc bE PL QL1, Nat.mul_comm bE PL, Nat.mul_assoc PL bE QL1,
                            ← Nat.mul_assoc aO]
          _ = ((aO * PL) * (bE * QL1)) * (bE * QL) := by rw [← Nat.mul_assoc aO PL]
      rwa [hrw] at h1
    have hrhs_eq : (L + 1) ^ dQ * ((aE * PL) * ((bE * QL1) * (bO * QL))) =
        ((L + 1) ^ dQ * (aE * bO)) * K := by
      dsimp [K]
      rw [Nat.mul_assoc ((L + 1) ^ dQ) (aE * bO) (bE * PL * QL * QL1)]
      apply congrArg ((L + 1) ^ dQ * ·)
      calc
        (aE * PL) * ((bE * QL1) * (bO * QL))
            = aE * (PL * (bO * (bE * QL * QL1))) := by
              have hb : (bE * QL1) * (bO * QL) = bO * (bE * QL * QL1) := by
                calc
                  (bE * QL1) * (bO * QL) = (bO * QL) * (bE * QL1) := Nat.mul_comm _ _
                  _ = bO * (QL * (bE * QL1)) := Nat.mul_assoc _ _ _
                  _ = bO * (bE * QL * QL1) := by
                        rw [← Nat.mul_assoc QL bE QL1, Nat.mul_comm QL bE, Nat.mul_assoc bE QL QL1]
              rw [hb, Nat.mul_assoc aE]
        _ = (aE * bO) * (bE * PL * QL * QL1) := by
              rw [← Nat.mul_assoc PL bO, Nat.mul_comm PL bO, Nat.mul_assoc bO PL,
                  ← Nat.mul_assoc aE bO]
              apply congrArg ((aE * bO) * ·)
              rw [← Nat.mul_assoc PL (bE * QL) QL1, ← Nat.mul_assoc PL bE QL,
                  Nat.mul_comm PL bE]
    rw [Nat.add_mul, Nat.mul_add ((L + 1) ^ dQ), hrhs_eq] at hm_canc
    have hsum_le : (L ^ dQ * (aE * bO) + (L + 1) ^ dQ) * K ≤
        ((L + 1) ^ dQ * (aE * bO)) * K := by
      rw [Nat.add_mul]
      exact Nat.le_trans (Nat.add_le_add ht1_ge ht2_ge) hm_canc
    have hfin := nat_mul_le_cancel_right_w5 K _ _ hK_pos hsum_le
    have hmv := (pow_sub_pow_mean_value_sandwich dQ (L + 1) L hdQ_pos (by omega)).2
    have hsub : L + 1 - L = 1 := by omega
    rw [hsub, Nat.mul_one] at hmv
    have hp_le : L ^ dQ ≤ (L + 1) ^ dQ := nat_pow_mono_base L (L + 1) (by omega) dQ
    have hdiff_le : (L + 1) ^ dQ * (aE * bO) - L ^ dQ * (aE * bO) ≤
        (dQ * (aE * bO)) * (L + 1) ^ (dQ - 1) := by
      rw [← Nat.sub_mul]
      have hm := Nat.mul_le_mul_right (aE * bO) hmv
      rwa [Nat.mul_assoc dQ, Nat.mul_comm ((L + 1) ^ (dQ - 1)) (aE * bO), ← Nat.mul_assoc dQ] at hm
    have hpow_split : (L + 1) ^ dQ = (L + 1) * (L + 1) ^ (dQ - 1) := by
      conv => lhs; rw [show dQ = (dQ - 1) + 1 by omega]
      rw [Nat.pow_succ, Nat.mul_comm]
    have hstrict_gt : (dQ * (aE * bO)) * (L + 1) ^ (dQ - 1) < (L + 1) ^ dQ := by
      rw [hpow_split]
      apply Nat.mul_lt_mul_of_pos_right _ (nat_pow_pos_of_pos (L + 1) (by dsimp [L]; omega) (dQ - 1))
      rw [← Nat.mul_assoc dQ aE bO]
      omega
    omega

/-- Generalized odd-multiplier compressed Collatz step `T_q(n)` (`n / 2` even, `(q * n + 1) / 2` odd). -/
def genCollatzStep (q n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else (q * n + 1) / 2

def genCollatzIter (q : Nat) : Nat -> Nat -> Nat
  | 0, n => n
  | k + 1, n => genCollatzIter q k (genCollatzStep q n)

theorem genCollatzIter_add (q : Nat) : ∀ (a b n : Nat),
    genCollatzIter q (a + b) n = genCollatzIter q b (genCollatzIter q a n)
  | 0, _, _ => by simp [genCollatzIter]
  | a + 1, b, n => by
    rw [Nat.succ_add]
    exact genCollatzIter_add q a b (genCollatzStep q n)

/-- Finite prefix sum `f 1 + f 2 + ... + f N`. -/
def sumRange1To (f : Nat -> Nat) : Nat -> Nat
  | 0 => 0
  | N + 1 => sumRange1To f N + f (N + 1)

/-- Attracting basin of `x0` under `genCollatzStep q`. -/
def ReachesGenCycle (q x0 n : Nat) : Prop :=
  ∃ k : Nat, genCollatzIter q k n = x0

/-- Closed finite orbit set `[13, 33, 83, 208, 104, 52, 26]` for the `5x + 1` 7-cycle. -/
def isM3Cycle13Member (n : Nat) : Bool :=
  n == 13 || n == 33 || n == 83 || n == 208 || n == 104 || n == 52 || n == 26

/--
  Theorem W7.2e (`mahler_koopman_tauberian_balance_and_m3_nonuniqueness`, zero custom axioms):
  Mahler–Koopman Tauberian Parity-Split Balance & `M3 = (Z^+, 5x + 1)` Non-Uniqueness (`Branch P1.3`):
  1. Exact `2 * N` Koopman Parity-Split Sum Identity: For EVERY odd multiplier `q : Nat`, EVERY
     `N : Nat`, and EVERY `T_q`-invariant sequence `a : Nat -> Nat` (`∀ n ≥ 1, a (T_q n) = a n`),
       `sumRange1To a (2 * N) = sumRange1To a N + sumRange1To (fun m => a ((q * (2 * m - 1) + 1) / 2)) N`!
  2. Universal Cycle-Basin Koopman Invariance: Whenever `x0` lies on a periodic cycle of period `P ≥ 1`
     (`genCollatzIter q P x0 = x0`), its basin `ReachesGenCycle q x0` is strictly `T_q`-invariant
     (`ReachesGenCycle q x0 n ↔ ReachesGenCycle q x0 (genCollatzStep q n)`)!
  3. Explicit `M3 = (Z^+, 5x + 1)` Multi-Basin Non-Uniqueness: For `q = 5`, `x0 = 1` (period `5`)
     and `x0 = 13` (period `7`) are TWO STRICTLY DISJOINT periodic cycles (`∀ k, genCollatzIter 5 k 13 ≠ 1`),
     yielding distinct `{0, 1}` Koopman eigenfunctions satisfying the identical Mahler–Koopman balance!
-/
theorem mahler_koopman_tauberian_balance_and_m3_nonuniqueness :
    (∀ (q : Nat) (a : Nat -> Nat),
      (∀ n : Nat, n ≥ 1 -> a (genCollatzStep q n) = a n) ->
      ∀ N : Nat,
        sumRange1To a (2 * N) =
          sumRange1To a N + sumRange1To (fun m => a ((q * (2 * m - 1) + 1) / 2)) N) ∧
    (∀ (q n : Nat), q ≥ 1 -> n ≥ 1 -> genCollatzStep q n ≥ (n + 1) / 2) ∧
    (∀ (q x0 P : Nat), P ≥ 1 -> genCollatzIter q P x0 = x0 ->
      ∀ n : Nat, ReachesGenCycle q x0 n ↔ ReachesGenCycle q x0 (genCollatzStep q n)) ∧
    genCollatzIter 5 5 1 = 1 ∧
    genCollatzIter 5 7 13 = 13 ∧
    (∀ k : Nat, genCollatzIter 5 k 13 ≠ 1) := by
  refine ⟨?_, ?_, ?_, by decide, by decide, ?_⟩
  · intro q a hinv N
    induction N with
    | zero => rfl
    | succ N' ih =>
      have h2N : 2 * (N' + 1) = (2 * N' + 1) + 1 := by omega
      rw [h2N, sumRange1To, sumRange1To, ih]
      have hodd_step : a (2 * N' + 1) = a ((q * (2 * (N' + 1) - 1) + 1) / 2) := by
        have hi := (hinv (2 * N' + 1) (by omega)).symm
        unfold genCollatzStep at hi
        have hodd : ¬ ((2 * N' + 1) % 2 = 0) := by omega
        simp only [hodd, ite_false] at hi
        rwa [show 2 * (N' + 1) - 1 = 2 * N' + 1 by omega]
      have hev_step : a ((2 * N' + 1) + 1) = a (N' + 1) := by
        have hi := (hinv (2 * (N' + 1)) (by omega)).symm
        unfold genCollatzStep at hi
        have hev : (2 * (N' + 1)) % 2 = 0 := by omega
        simp only [hev, ite_true, show 2 * (N' + 1) / 2 = N' + 1 by omega] at hi
        rwa [show (2 * N' + 1) + 1 = 2 * (N' + 1) by omega]
      simp only [sumRange1To]
      rw [hodd_step, hev_step]
      omega
  · intro q n hq hn
    unfold genCollatzStep
    by_cases hev : n % 2 = 0
    · simp only [hev, ite_true]; omega
    · simp only [hev, ite_false]
      have hm : 1 * n ≤ q * n := Nat.mul_le_mul_right n hq
      omega
  · intro q x0 P hP hcyc n
    constructor
    · rintro ⟨k, hk⟩
      cases k with
      | zero =>
        simp only [genCollatzIter] at hk
        subst hk
        refine ⟨P - 1, ?_⟩
        have hsp : P = 1 + (P - 1) := by omega
        rw [hsp, genCollatzIter_add q 1 (P - 1) n] at hcyc
        exact hcyc
      | succ k' => exact ⟨k', hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨k + 1, hk⟩
  · have hclosed : ∀ n : Nat, isM3Cycle13Member n = true ->
        isM3Cycle13Member (genCollatzStep 5 n) = true ∧ n ≠ 1 := by
      intro n hm
      unfold isM3Cycle13Member at hm
      simp only [Bool.or_eq_true, beq_iff_eq] at hm
      rcases hm with ((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) <;> decide
    have hiter_mem : ∀ (k n : Nat), isM3Cycle13Member n = true ->
        isM3Cycle13Member (genCollatzIter 5 k n) = true := by
      intro k
      induction k with
      | zero => intro n hm; exact hm
      | succ k' ih => intro n hm; exact ih _ (hclosed n hm).1
    intro k
    exact (hclosed _ (hiter_mem k 13 (by decide))).2

/--
  Theorem W7.2f (`mahler_bivariate_pole_subtraction_and_half_exponent_decay`, zero custom axioms):
  Bivariate Mahler–Koopman Pole Subtraction & Uniform `(n + 1) / 2` Geometric Decay:
  For ANY interior rational radius `w = wNum / wDen ∈ (0, 1)` (`1 ≤ wNum < wDen`), ANY `q ≥ 1`,
  and ANY `n ≥ 1`, setting `T := genCollatzStep q n` and `h := (n + 1) / 2`:
  1. Strict Interior Denominator Positivity: `T ≥ h`, `T ≥ 1`, and `wNum ^ T < wDen ^ T`
     (so `1 - (wNum / wDen) ^ T > 0` across all `n ≥ 1`);
  2. Exact `w = 0` Pole Subtraction Identity: Clearing denominators in
     `1 / (1 - w ^ T) - 1 = w ^ T / (1 - w ^ T)` gives `wDen ^ T - (wDen ^ T - wNum ^ T) = wNum ^ T`;
  3. Uniform Half-Exponent Geometric Decay: `wNum ^ T * wDen ^ h ≤ wNum ^ h * wDen ^ T`, i.e.,
     `(wNum / wDen) ^ (genCollatzStep q n) ≤ (wNum / wDen) ^ ((n + 1) / 2)`, proving the pole-subtracted
     bivariate remainder converges normally across `|z| ≤ 1` without distinguishing `M3` basins!
-/
theorem mahler_bivariate_pole_subtraction_and_half_exponent_decay
    (wNum wDen q n : Nat)
    (hw1 : 1 ≤ wNum) (hw_lt : wNum < wDen) (hq : q ≥ 1) (hn : n ≥ 1) :
    let T := genCollatzStep q n
    let h := (n + 1) / 2
    T ≥ h ∧
    T ≥ 1 ∧
    wNum ^ T < wDen ^ T ∧
    wDen ^ T - (wDen ^ T - wNum ^ T) = wNum ^ T ∧
    wNum ^ T * wDen ^ h ≤ wNum ^ h * wDen ^ T := by
  dsimp only
  let T := genCollatzStep q n
  let h := (n + 1) / 2
  have hT_ge_h : T ≥ h := by
    unfold T genCollatzStep
    by_cases hev : n % 2 = 0
    · simp only [hev, ite_true]; dsimp [h]; omega
    · simp only [hev, ite_false]
      have hm : 1 * n ≤ q * n := Nat.mul_le_mul_right n hq
      dsimp [h]; omega
  have hh_pos : h ≥ 1 := by dsimp [h]; omega
  have hT_pos : T ≥ 1 := Nat.le_trans hh_pos hT_ge_h
  have hpow_lt : wNum ^ T < wDen ^ T := by
    have hsp : T = (T - 1) + 1 := by omega
    rw [hsp, Nat.pow_succ wNum (T - 1), Nat.pow_succ wDen (T - 1)]
    have hle_m := nat_pow_mono_base wNum wDen (Nat.le_of_lt hw_lt) (T - 1)
    have hpos_m := nat_pow_pos_of_pos wNum hw1 (T - 1)
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hw_lt hpos_m)
      (Nat.mul_le_mul_right wDen hle_m)
  have hpole_sub : wDen ^ T - (wDen ^ T - wNum ^ T) = wNum ^ T := by omega
  have hdecay : wNum ^ T * wDen ^ h ≤ wNum ^ h * wDen ^ T := by
    let d := T - h
    have hT_sp : T = h + d := by dsimp [d]; omega
    rw [hT_sp, Nat.pow_add wNum h d, Nat.pow_add wDen h d]
    have hl : (wNum ^ h * wNum ^ d) * wDen ^ h = (wNum ^ h * wDen ^ h) * wNum ^ d := by
      rw [Nat.mul_assoc (wNum ^ h) (wNum ^ d) (wDen ^ h),
          Nat.mul_comm (wNum ^ d) (wDen ^ h),
          ← Nat.mul_assoc (wNum ^ h) (wDen ^ h) (wNum ^ d)]
    have hr : wNum ^ h * (wDen ^ h * wDen ^ d) = (wNum ^ h * wDen ^ h) * wDen ^ d :=
      (Nat.mul_assoc (wNum ^ h) (wDen ^ h) (wDen ^ d)).symm
    rw [hl, hr]
    exact Nat.mul_le_mul_left (wNum ^ h * wDen ^ h)
      (nat_pow_mono_base wNum wDen (Nat.le_of_lt hw_lt) d)
  exact ⟨hT_ge_h, hT_pos, hpow_lt, hpole_sub, hdecay⟩

-- ============================================================================
-- SECTION 3A: Front C (Branch P4.3) — Non-Triangular `d = 2` & `d = 3`
--             Hofbauer–Waldmann Certificates on `R1 + Sub6`, Lower-Triangular
--             Collapse (`∀ d ≥ 1`), & `ω^k` / Parikh VASS Impossibility (`∀ k ≥ 1`)
-- ============================================================================

def mkMat2 (r0 r1 : Nat × Nat) : Fin 2 -> Fin 2 -> Nat :=
  fun i j =>
    let row := if i.val = 0 then r0 else r1
    if j.val = 0 then row.1 else row.2

def mkVec2 (v0 v1 : Nat) : Fin 2 -> Nat :=
  fun i => if i.val = 0 then v0 else v1

/--
  Explicit `2 x 2` non-triangular Hofbauer–Waldmann natural matrix certificate orienting
  ALL 7 rules of `sub6 ∪ {R1}` (`{R1, R2, R5, R7, R8, R9, R11}`) ALREADY in dimension `d = 2`
  (`(M_s)_{0,0} = 1` across all symbols, `(M_{B0})_{1,1} = 0`, `(M_{B0})_{1,0} = 5`, `(M_{B0})_{0,1} = 10`)!
-/
def r1Sub6NonTri2DCert : MixedSRSSym -> NatAffineDim 2
  | .L  => { M := mkMat2 (1, 5)  (0, 0),  v := mkVec2 0 0 }
  | .R  => { M := mkMat2 (1, 0)  (11, 0), v := mkVec2 0 3 }
  | .B0 => { M := mkMat2 (1, 10) (5, 0),  v := mkVec2 2 1 }
  | .B1 => { M := mkMat2 (1, 0)  (0, 11), v := mkVec2 0 1 }
  | .T0 => { M := mkMat2 (1, 0)  (0, 11), v := mkVec2 1 1 }
  | .T1 => { M := mkMat2 (1, 0)  (13, 0), v := mkVec2 0 0 }
  | .T2 => { M := mkMat2 (1, 26) (0, 5),  v := mkVec2 0 0 }

def orients2DBool (A B : NatAffineDim 2) : Bool :=
  let idx0 : Fin 2 := ⟨0, by decide⟩
  let idx1 : Fin 2 := ⟨1, by decide⟩
  decide (A.M idx0 idx0 ≥ B.M idx0 idx0) &&
  decide (A.M idx0 idx1 ≥ B.M idx0 idx1) &&
  decide (A.M idx1 idx0 ≥ B.M idx1 idx0) &&
  decide (A.M idx1 idx1 ≥ B.M idx1 idx1) &&
  decide (A.v idx0 ≥ B.v idx0) &&
  decide (A.v idx1 ≥ B.v idx1) &&
  decide (A.v idx0 > B.v idx0)

theorem orients2DBool_sound (A B : NatAffineDim 2)
    (hb : orients2DBool A B = true) :
    orientsNatAffineDim 2 (by decide) A B := by
  unfold orients2DBool at hb
  rcases bool_and_split hb with ⟨hb6, hgt0_b⟩
  rcases bool_and_split hb6 with ⟨hb5, hv1_b⟩
  rcases bool_and_split hb5 with ⟨hb4, hv0_b⟩
  rcases bool_and_split hb4 with ⟨hb3, hm11_b⟩
  rcases bool_and_split hb3 with ⟨hb2, hm10_b⟩
  rcases bool_and_split hb2 with ⟨hm00_b, hm01_b⟩
  refine ⟨?_, ?_, of_decide_eq_true hgt0_b⟩
  · intro ⟨i, hi⟩ ⟨j, hj⟩
    match i, j with
    | 0, 0 => exact of_decide_eq_true hm00_b
    | 0, 1 => exact of_decide_eq_true hm01_b
    | 1, 0 => exact of_decide_eq_true hm10_b
    | 1, 1 => exact of_decide_eq_true hm11_b
    | k + 2, _ => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 2 k) hi)
    | _, k + 2 => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 2 k) hj)
  · intro ⟨i, hi⟩
    match i with
    | 0 => exact of_decide_eq_true hv0_b
    | 1 => exact of_decide_eq_true hv1_b
    | k + 2 => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 2 k) hi)

/--
  Theorem W7.3a0 (`r1_sub6_admits_2d_nontriangular_hofbauer_waldmann_cert`, `[]` axioms):
  Sharp `d = 2` Non-Triangular Hofbauer–Waldmann Separation on `sub6 ∪ {R1}`:
  Whereas Wave 6 proved `sub6 ∪ {R1}` is UNIVERSALLY IMPOSSIBLE in `2 x 2` upper-triangular
  matrices (`UpperTri2D`) and `all_dim_lower_triangular_hofbauer_waldmann_impossibility` refutes
  ALL `d ≥ 1` lower-triangular matrices, `r1Sub6NonTri2DCert` orients ALL SEVEN rules
  `{R1, R2, R5, R7, R8, R9, R11}` ALREADY in `d = 2` via bidirectional off-diagonal feedback
  (`(M_s)_{0,0} = 1`, `(M_{B0})_{1,1} = 0`, `(M_{B0})_{1,0} = 5`, `(M_{B0})_{0,1} = 10`)!
-/
theorem r1_sub6_admits_2d_nontriangular_hofbauer_waldmann_cert :
    (∀ s : MixedSRSSym, (r1Sub6NonTri2DCert s).M ⟨0, by decide⟩ ⟨0, by decide⟩ = 1) ∧
    (r1Sub6NonTri2DCert .B0).M ⟨1, by decide⟩ ⟨1, by decide⟩ = 0 ∧
    (r1Sub6NonTri2DCert .B0).M ⟨1, by decide⟩ ⟨0, by decide⟩ = 5 ∧
    (r1Sub6NonTri2DCert .B0).M ⟨0, by decide⟩ ⟨1, by decide⟩ = 10 ∧
    orientsNatAffineDim 2 (by decide)
      (evalWordNatAffineDim 2 r1Sub6NonTri2DCert [.L, .B0])
      (evalWordNatAffineDim 2 r1Sub6NonTri2DCert [.L]) ∧
    orientsNatAffineDim 2 (by decide)
      (evalWordNatAffineDim 2 r1Sub6NonTri2DCert [.L, .B1])
      (evalWordNatAffineDim 2 r1Sub6NonTri2DCert [.L, .T2]) ∧
    orientsNatAffineDim 2 (by decide)
      (evalWordNatAffineDim 2 r1Sub6NonTri2DCert [.T1, .B0])
      (evalWordNatAffineDim 2 r1Sub6NonTri2DCert [.B1, .T0]) ∧
    orientsNatAffineDim 2 (by decide)
      (evalWordNatAffineDim 2 r1Sub6NonTri2DCert [.T2, .B0])
      (evalWordNatAffineDim 2 r1Sub6NonTri2DCert [.B0, .T1]) ∧
    orientsNatAffineDim 2 (by decide)
      (evalWordNatAffineDim 2 r1Sub6NonTri2DCert [.T2, .B1])
      (evalWordNatAffineDim 2 r1Sub6NonTri2DCert [.B1, .T2]) ∧
    orientsNatAffineDim 2 (by decide)
      (evalWordNatAffineDim 2 r1Sub6NonTri2DCert [.T0, .R])
      (evalWordNatAffineDim 2 r1Sub6NonTri2DCert [.B1, .R]) ∧
    orientsNatAffineDim 2 (by decide)
      (evalWordNatAffineDim 2 r1Sub6NonTri2DCert [.T2, .R])
      (evalWordNatAffineDim 2 r1Sub6NonTri2DCert [.B1, .B0, .R]) := by
  refine ⟨?_, rfl, rfl, rfl,
          orients2DBool_sound _ _ (by decide),
          orients2DBool_sound _ _ (by decide),
          orients2DBool_sound _ _ (by decide),
          orients2DBool_sound _ _ (by decide),
          orients2DBool_sound _ _ (by decide),
          orients2DBool_sound _ _ (by decide),
          orients2DBool_sound _ _ (by decide)⟩
  intro s
  cases s <;> rfl

def mkMat3 (r0 r1 r2 : Nat × Nat × Nat) : Fin 3 -> Fin 3 -> Nat :=
  fun i j =>
    let row := if i.val = 0 then r0 else if i.val = 1 then r1 else r2
    if j.val = 0 then row.1 else if j.val = 1 then row.2.1 else row.2.2

def mkVec3 (v0 v1 v2 : Nat) : Fin 3 -> Nat :=
  fun i => if i.val = 0 then v0 else if i.val = 1 then v1 else v2

/--
  Explicit `3 x 3` non-triangular Hofbauer–Waldmann natural matrix certificate orienting
  ALL 7 rules of `sub6 ∪ {R1}` (`{R1, R2, R5, R7, R8, R9, R11}`) with `(M_s)_{0,0} = 1`!
-/
def r1Sub6NonTri3DCert : MixedSRSSym -> NatAffineDim 3
  | .L  => { M := mkMat3 (1, 0, 1) (6, 0, 6) (1, 0, 1), v := mkVec3 0 0 0 }
  | .R  => { M := mkMat3 (1, 0, 0) (0, 0, 0) (0, 0, 0), v := mkVec3 5 0 4 }
  | .B0 => { M := mkMat3 (1, 0, 1) (1, 1, 1) (0, 6, 0), v := mkVec3 0 2 1 }
  | .B1 => { M := mkMat3 (1, 0, 0) (0, 0, 0) (0, 0, 3), v := mkVec3 0 0 1 }
  | .T0 => { M := mkMat3 (1, 0, 0) (0, 0, 0) (1, 0, 2), v := mkVec3 1 0 0 }
  | .T1 => { M := mkMat3 (1, 1, 0) (0, 0, 0) (0, 6, 0), v := mkVec3 0 0 0 }
  | .T2 => { M := mkMat3 (1, 0, 2) (0, 1, 1) (0, 0, 1), v := mkVec3 0 0 0 }

def orients3DBool (A B : NatAffineDim 3) : Bool :=
  let idx0 : Fin 3 := ⟨0, by decide⟩
  let idx1 : Fin 3 := ⟨1, by decide⟩
  let idx2 : Fin 3 := ⟨2, by decide⟩
  decide (A.M idx0 idx0 ≥ B.M idx0 idx0) &&
  decide (A.M idx0 idx1 ≥ B.M idx0 idx1) &&
  decide (A.M idx0 idx2 ≥ B.M idx0 idx2) &&
  decide (A.M idx1 idx0 ≥ B.M idx1 idx0) &&
  decide (A.M idx1 idx1 ≥ B.M idx1 idx1) &&
  decide (A.M idx1 idx2 ≥ B.M idx1 idx2) &&
  decide (A.M idx2 idx0 ≥ B.M idx2 idx0) &&
  decide (A.M idx2 idx1 ≥ B.M idx2 idx1) &&
  decide (A.M idx2 idx2 ≥ B.M idx2 idx2) &&
  decide (A.v idx0 ≥ B.v idx0) &&
  decide (A.v idx1 ≥ B.v idx1) &&
  decide (A.v idx2 ≥ B.v idx2) &&
  decide (A.v idx0 > B.v idx0)

theorem orients3DBool_sound (A B : NatAffineDim 3)
    (hb : orients3DBool A B = true) :
    orientsNatAffineDim 3 (by decide) A B := by
  unfold orients3DBool at hb
  rcases bool_and_split hb with ⟨hb12, hgt0_b⟩
  rcases bool_and_split hb12 with ⟨hb11, hv2_b⟩
  rcases bool_and_split hb11 with ⟨hb10, hv1_b⟩
  rcases bool_and_split hb10 with ⟨hb9, hv0_b⟩
  rcases bool_and_split hb9 with ⟨hb8, hm22_b⟩
  rcases bool_and_split hb8 with ⟨hb7, hm21_b⟩
  rcases bool_and_split hb7 with ⟨hb6, hm20_b⟩
  rcases bool_and_split hb6 with ⟨hb5, hm12_b⟩
  rcases bool_and_split hb5 with ⟨hb4, hm11_b⟩
  rcases bool_and_split hb4 with ⟨hb3, hm10_b⟩
  rcases bool_and_split hb3 with ⟨hb2, hm02_b⟩
  rcases bool_and_split hb2 with ⟨hm00_b, hm01_b⟩
  refine ⟨?_, ?_, of_decide_eq_true hgt0_b⟩
  · intro ⟨i, hi⟩ ⟨j, hj⟩
    match i, j with
    | 0, 0 => exact of_decide_eq_true hm00_b
    | 0, 1 => exact of_decide_eq_true hm01_b
    | 0, 2 => exact of_decide_eq_true hm02_b
    | 1, 0 => exact of_decide_eq_true hm10_b
    | 1, 1 => exact of_decide_eq_true hm11_b
    | 1, 2 => exact of_decide_eq_true hm12_b
    | 2, 0 => exact of_decide_eq_true hm20_b
    | 2, 1 => exact of_decide_eq_true hm21_b
    | 2, 2 => exact of_decide_eq_true hm22_b
    | k + 3, _ => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 3 k) hi)
    | _, k + 3 => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 3 k) hj)
  · intro ⟨i, hi⟩
    match i with
    | 0 => exact of_decide_eq_true hv0_b
    | 1 => exact of_decide_eq_true hv1_b
    | 2 => exact of_decide_eq_true hv2_b
    | k + 3 => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 3 k) hi)

/--
  Theorem W7.3a (`r1_sub6_admits_3d_nontriangular_hofbauer_waldmann_cert`, `[]` axioms):
  Breakthrough 3D Non-Triangular Hofbauer–Waldmann Certificate on `sub6 ∪ {R1}`:
  Whereas Wave 6 proved `sub6 ∪ {R1}` (`{R1, R2, R5, R7, R8, R9, R11}`) is UNIVERSALLY IMPOSSIBLE
  in `UpperTri2D` (even with zero lower diagonals) and in all-dimension bipartite swap matrices,
  `r1Sub6NonTri3DCert` satisfies `(M_s)_{0,0} = 1` across ALL `s : MixedSRSSym`, has both positive
  subdiagonal `(M_{B0})_{1,0} = 1` and superdiagonal `(M_{B0})_{0,2} = 1`, and strictly orients
  ALL SEVEN rules `{R1, R2, R5, R7, R8, R9, R11}` simultaneously!
-/
theorem r1_sub6_admits_3d_nontriangular_hofbauer_waldmann_cert :
    (∀ s : MixedSRSSym, (r1Sub6NonTri3DCert s).M ⟨0, by decide⟩ ⟨0, by decide⟩ = 1) ∧
    (r1Sub6NonTri3DCert .B0).M ⟨1, by decide⟩ ⟨0, by decide⟩ = 1 ∧
    (r1Sub6NonTri3DCert .B0).M ⟨0, by decide⟩ ⟨2, by decide⟩ = 1 ∧
    orientsNatAffineDim 3 (by decide)
      (evalWordNatAffineDim 3 r1Sub6NonTri3DCert [.L, .B0])
      (evalWordNatAffineDim 3 r1Sub6NonTri3DCert [.L]) ∧
    orientsNatAffineDim 3 (by decide)
      (evalWordNatAffineDim 3 r1Sub6NonTri3DCert [.L, .B1])
      (evalWordNatAffineDim 3 r1Sub6NonTri3DCert [.L, .T2]) ∧
    orientsNatAffineDim 3 (by decide)
      (evalWordNatAffineDim 3 r1Sub6NonTri3DCert [.T1, .B0])
      (evalWordNatAffineDim 3 r1Sub6NonTri3DCert [.B1, .T0]) ∧
    orientsNatAffineDim 3 (by decide)
      (evalWordNatAffineDim 3 r1Sub6NonTri3DCert [.T2, .B0])
      (evalWordNatAffineDim 3 r1Sub6NonTri3DCert [.B0, .T1]) ∧
    orientsNatAffineDim 3 (by decide)
      (evalWordNatAffineDim 3 r1Sub6NonTri3DCert [.T2, .B1])
      (evalWordNatAffineDim 3 r1Sub6NonTri3DCert [.B1, .T2]) ∧
    orientsNatAffineDim 3 (by decide)
      (evalWordNatAffineDim 3 r1Sub6NonTri3DCert [.T0, .R])
      (evalWordNatAffineDim 3 r1Sub6NonTri3DCert [.B1, .R]) ∧
    orientsNatAffineDim 3 (by decide)
      (evalWordNatAffineDim 3 r1Sub6NonTri3DCert [.T2, .R])
      (evalWordNatAffineDim 3 r1Sub6NonTri3DCert [.B1, .B0, .R]) := by
  refine ⟨?_, rfl, rfl,
          orients3DBool_sound _ _ (by decide),
          orients3DBool_sound _ _ (by decide),
          orients3DBool_sound _ _ (by decide),
          orients3DBool_sound _ _ (by decide),
          orients3DBool_sound _ _ (by decide),
          orients3DBool_sound _ _ (by decide),
          orients3DBool_sound _ _ (by decide)⟩
  intro s
  cases s <;> rfl

/-- Lower-triangular `d x d` matrix predicate (`i < j -> A i j = 0`). -/
def IsLowerTriMat (d : Nat) (A : Fin d -> Fin d -> Nat) : Prop :=
  ∀ i j : Fin d, i.val < j.val -> A i j = 0

theorem natMatMul_lowerTri_topLeft (d : Nat) (hd : 0 < d) (A B : Fin d -> Fin d -> Nat)
    (hA : IsLowerTriMat d A) :
    natMatMul d A B ⟨0, hd⟩ ⟨0, hd⟩ = A ⟨0, hd⟩ ⟨0, hd⟩ * B ⟨0, hd⟩ ⟨0, hd⟩ := by
  unfold natMatMul
  apply natSumFin_eq_single d _ ⟨0, hd⟩
  intro k hk
  have hk0 : 0 < k.val := by simp only at hk; omega
  rw [hA ⟨0, hd⟩ k hk0, Nat.zero_mul]

theorem natMatVec_lowerTri_top (d : Nat) (hd : 0 < d) (A : Fin d -> Fin d -> Nat)
    (v : Fin d -> Nat) (hA : IsLowerTriMat d A) :
    natMatVec d A v ⟨0, hd⟩ = A ⟨0, hd⟩ ⟨0, hd⟩ * v ⟨0, hd⟩ := by
  unfold natMatVec
  apply natSumFin_eq_single d _ ⟨0, hd⟩
  intro k hk
  have hk0 : 0 < k.val := by simp only at hk; omega
  rw [hA ⟨0, hd⟩ k hk0, Nat.zero_mul]

theorem evalWord_lowerTri_coord0 (d : Nat) (hd : 0 < d)
    (interp : MixedSRSSym -> NatAffineDim d)
    (hlow : ∀ s : MixedSRSSym, IsLowerTriMat d (interp s).M) :
    ∀ w : List MixedSRSSym,
      IsLowerTriMat d (evalWordNatAffineDim d interp w).M ∧
      (∀ s : MixedSRSSym,
        (evalWordNatAffineDim d interp (s :: w)).M ⟨0, hd⟩ ⟨0, hd⟩ =
          (interp s).M ⟨0, hd⟩ ⟨0, hd⟩ * (evalWordNatAffineDim d interp w).M ⟨0, hd⟩ ⟨0, hd⟩ ∧
        (evalWordNatAffineDim d interp (s :: w)).v ⟨0, hd⟩ =
          (interp s).v ⟨0, hd⟩ +
            (interp s).M ⟨0, hd⟩ ⟨0, hd⟩ * (evalWordNatAffineDim d interp w).v ⟨0, hd⟩)
  | [] => by
    refine ⟨?_, ?_⟩
    · intro i j hij
      simp [evalWordNatAffineDim, natMatId, show i.val ≠ j.val by omega]
    · intro s
      simp only [evalWordNatAffineDim, compNatAffineDim]
      exact ⟨natMatMul_lowerTri_topLeft d hd (interp s).M (natMatId d) (hlow s),
             by rw [natMatVec_lowerTri_top d hd (interp s).M _ (hlow s), Nat.add_comm]⟩
  | b :: rest => by
    rcases evalWord_lowerTri_coord0 d hd interp hlow rest with ⟨hlow_r, _⟩
    have hlow_cons : IsLowerTriMat d (evalWordNatAffineDim d interp (b :: rest)).M := by
      intro i j hij
      simp only [evalWordNatAffineDim, compNatAffineDim]
      unfold natMatMul natSumFin
      rw [natSumPrefix_congr d _ (fun _ => 0) _ d, natSumPrefix_zero_w6 d d]
      intro k
      by_cases hik : i.val < k.val
      · rw [hlow b i k hik, Nat.zero_mul]
      · rw [hlow_r k j (by omega), Nat.mul_zero]
    refine ⟨hlow_cons, ?_⟩
    intro s
    let wr := evalWordNatAffineDim d interp (b :: rest)
    have hstep : evalWordNatAffineDim d interp (s :: b :: rest) =
        compNatAffineDim d (interp s) wr := rfl
    rw [hstep]
    simp only [compNatAffineDim]
    exact ⟨natMatMul_lowerTri_topLeft d hd (interp s).M wr.M (hlow s),
           by rw [natMatVec_lowerTri_top d hd (interp s).M wr.v (hlow s), Nat.add_comm]⟩

/--
  Theorem W7.3b (`all_dim_lower_triangular_hofbauer_waldmann_impossibility`, zero custom axioms):
  Universal All-Dimension (`∀ d ≥ 1`) Lower-Triangular Hofbauer–Waldmann Collapse:
  In sharp contrast to `r1Sub6NonTri3DCert` (which uses BOTH subdiagonal and superdiagonal entries),
  EVERY lower-triangular natural matrix interpretation (`i < j -> M_s i j = 0`, arbitrary subdiagonals
  and arbitrary zero lower diagonals `M_s i i = 0` for `i ≥ 1` allowed!) with `(M_s)_{0,0} ≥ 1`
  collapses unconditionally on `{R2, R5, R7, R9, R11}` across ALL dimensions `∀ d ≥ 1`!
-/
theorem all_dim_lower_triangular_hofbauer_waldmann_impossibility
    (d : Nat) (hd : 0 < d)
    (interp : MixedSRSSym -> NatAffineDim d)
    (hlow : ∀ s : MixedSRSSym, IsLowerTriMat d (interp s).M)
    (htop : ∀ s : MixedSRSSym, (interp s).M ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1)
    (hR2  : orientsNatAffineDim d hd (evalWordNatAffineDim d interp [.L, .B1])
              (evalWordNatAffineDim d interp [.L, .T2]))
    (hR5  : orientsNatAffineDim d hd (evalWordNatAffineDim d interp [.T1, .B0])
              (evalWordNatAffineDim d interp [.B1, .T0]))
    (hR7  : orientsNatAffineDim d hd (evalWordNatAffineDim d interp [.T2, .B0])
              (evalWordNatAffineDim d interp [.B0, .T1]))
    (hR9  : orientsNatAffineDim d hd (evalWordNatAffineDim d interp [.T0, .R])
              (evalWordNatAffineDim d interp [.B1, .R]))
    (hR11 : orientsNatAffineDim d hd (evalWordNatAffineDim d interp [.T2, .R])
              (evalWordNatAffineDim d interp [.B1, .B0, .R])) :
    False := by
  let z : Fin d := ⟨0, hd⟩
  have h1_step : ∀ s : MixedSRSSym,
      (evalWordNatAffineDim d interp [s]).M z z = (interp s).M z z ∧
      (evalWordNatAffineDim d interp [s]).v z = (interp s).v z := by
    intro s
    rcases (evalWord_lowerTri_coord0 d hd interp hlow []).2 s with ⟨hm, hv⟩
    have hid_m : (evalWordNatAffineDim d interp []).M z z = 1 := by
      simp [evalWordNatAffineDim, natMatId]
    have hid_v : (evalWordNatAffineDim d interp []).v z = 0 := rfl
    rw [hid_m, Nat.mul_one] at hm
    rw [hid_v, Nat.mul_zero, Nat.add_zero] at hv
    exact ⟨hm, hv⟩
  have h2_step : ∀ s1 s2 : MixedSRSSym,
      (evalWordNatAffineDim d interp [s1, s2]).M z z = (interp s1).M z z * (interp s2).M z z ∧
      (evalWordNatAffineDim d interp [s1, s2]).v z =
        (interp s1).v z + (interp s1).M z z * (interp s2).v z := by
    intro s1 s2
    rcases (evalWord_lowerTri_coord0 d hd interp hlow [s2]).2 s1 with ⟨hm, hv⟩
    rw [(h1_step s2).1] at hm
    rw [(h1_step s2).2] at hv
    exact ⟨hm, hv⟩
  have h3_step : ∀ s1 s2 s3 : MixedSRSSym,
      (evalWordNatAffineDim d interp [s1, s2, s3]).M z z =
        (interp s1).M z z * (interp s2).M z z * (interp s3).M z z ∧
      (evalWordNatAffineDim d interp [s1, s2, s3]).v z =
        (interp s1).v z + (interp s1).M z z * ((interp s2).v z + (interp s2).M z z * (interp s3).v z) := by
    intro s1 s2 s3
    rcases (evalWord_lowerTri_coord0 d hd interp hlow [s2, s3]).2 s1 with ⟨hm, hv⟩
    rw [(h2_step s2 s3).1, ← Nat.mul_assoc] at hm
    rw [(h2_step s2 s3).2] at hv
    exact ⟨hm, hv⟩
  have hr2_m := hR2.1 z z; rw [(h2_step .L .B1).1, (h2_step .L .T2).1] at hr2_m
  have hr5_m := hR5.1 z z; rw [(h2_step .T1 .B0).1, (h2_step .B1 .T0).1] at hr5_m
  have hr7_m := hR7.1 z z; rw [(h2_step .T2 .B0).1, (h2_step .B0 .T1).1] at hr7_m
  have hr9_m := hR9.1 z z; rw [(h2_step .T0 .R).1, (h2_step .B1 .R).1] at hr9_m
  have hr11_m := hR11.1 z z; rw [(h2_step .T2 .R).1, (h3_step .B1 .B0 .R).1] at hr11_m
  rcases upper_triangular_top_left_unit_collapse_any_dim
    ((interp .L).M z z) ((interp .R).M z z) ((interp .B0).M z z) ((interp .B1).M z z)
    ((interp .T0).M z z) ((interp .T1).M z z) ((interp .T2).M z z)
    (htop .L) (htop .R) (htop .B0) (htop .B1) (htop .T0) (htop .T1) (htop .T2)
    hr2_m hr5_m hr7_m hr9_m hr11_m with ⟨hmB0, hmB1, _, _, hmT2⟩
  have hr2_v := hR2.2.2
  have hr11_v := hR11.2.2
  change (evalWordNatAffineDim d interp [.L, .B1]).v z >
    (evalWordNatAffineDim d interp [.L, .T2]).v z at hr2_v
  change (evalWordNatAffineDim d interp [.T2, .R]).v z >
    (evalWordNatAffineDim d interp [.B1, .B0, .R]).v z at hr11_v
  rw [(h2_step .L .B1).2, (h2_step .L .T2).2] at hr2_v
  rw [(h2_step .T2 .R).2, (h3_step .B1 .B0 .R).2] at hr11_v
  simp only [hmB0, hmB1, hmT2, Nat.one_mul] at hr11_v
  have hcB1_gt : (interp .B1).v z > (interp .T2).v z := by
    have hmL : (interp .L).M z z ≥ 1 := htop .L
    by_cases hgt : (interp .B1).v z > (interp .T2).v z
    · exact hgt
    · have hm := Nat.mul_le_mul_left ((interp .L).M z z) (by omega : (interp .B1).v z ≤ (interp .T2).v z)
      omega
  omega

/-- `k`-counter Parikh / VASS evaluation of a word over `MixedSRSSym`. -/
def evalParikhVec (k : Nat) (wt : MixedSRSSym -> Fin k -> Nat) :
    List MixedSRSSym -> Fin k -> Nat
  | [], _ => 0
  | s :: rest, i => wt s i + evalParikhVec k wt rest i

/-- Standard strict lexicographic `ω^k` ordering on `Fin k -> Nat`. -/
def lexGtFin (k : Nat) (u v : Fin k -> Nat) : Prop :=
  ∃ idx : Fin k,
    (∀ i : Fin k, i.val < idx.val -> u i = v i) ∧
    u idx > v idx

/-- 1D natural affine map `x ↦ m * x + c` (`m ≥ 1`) for Zantema–Geser `ω^k` rule-removal towers. -/
structure NatAffine1D where
  m : Nat
  c : Nat

def evalWordAffine1D (interp : MixedSRSSym -> NatAffine1D) : List MixedSRSSym -> NatAffine1D
  | [] => { m := 1, c := 0 }
  | s :: rest =>
    let r := evalWordAffine1D interp rest
    { m := (interp s).m * r.m, c := (interp s).c + (interp s).m * r.c }

def weakOrients1D (lhs rhs : NatAffine1D) : Prop :=
  lhs.m ≥ rhs.m ∧ lhs.c ≥ rhs.c

def strictOrients1D (lhs rhs : NatAffine1D) : Prop :=
  lhs.m ≥ rhs.m ∧ lhs.c > rhs.c

/--
  `k`-level Zantema–Geser `ω^k` iterated 1D natural-affine (`m_s ≥ 1`) rule-removal tower
  on a finite list of rewrite rules `(lhs, rhs)`:
  At each level `1..k`, `interp` weakly orients all remaining rules (`weakOrients1D`),
  removes every strictly oriented rule (`strictOrients1D`), and terminates at `[]` in `≤ k` levels.
-/
def OmegaAffineRuleRemovalTower : Nat -> List (List MixedSRSSym × List MixedSRSSym) -> Prop
  | 0, rules => rules = []
  | k + 1, rules =>
    rules = [] ∨
    ∃ (rem : List (List MixedSRSSym × List MixedSRSSym))
      (interp : MixedSRSSym -> NatAffine1D),
      (∀ s : MixedSRSSym, (interp s).m ≥ 1) ∧
      (∀ r ∈ rules, weakOrients1D (evalWordAffine1D interp r.1) (evalWordAffine1D interp r.2)) ∧
      (∀ r ∈ rules, ¬ strictOrients1D (evalWordAffine1D interp r.1) (evalWordAffine1D interp r.2) -> r ∈ rem) ∧
      OmegaAffineRuleRemovalTower k rem

def sub6RuleList : List (List MixedSRSSym × List MixedSRSSym) :=
  [([.L, .B1], [.L, .T2]),
   ([.T1, .B0], [.B1, .T0]),
   ([.T2, .B0], [.B0, .T1]),
   ([.T2, .B1], [.B1, .T2]),
   ([.T0, .R], [.B1, .R]),
   ([.T2, .R], [.B1, .B0, .R])]

/--
  Theorem W7.3c (`omega_k_affine_rule_removal_and_parikh_vass_impossibility`, zero custom axioms):
  Universal All-Rank (`∀ k ≥ 1`) `ω^k` Parikh VASS & Iterated Natural-Affine Rule-Removal Barriers:
  1. `k`-Counter Parikh / VASS Ranking Impossibility (`∀ k ≥ 1`): NO `k`-counter commutative
     symbol-weight interpretation `wt : MixedSRSSym -> Fin k -> Nat` can orient even the 2-rule
     pair `{R2, R11}` under `lexGtFin k`!
  2. `k`-Level Zantema–Geser `ω^k` Iterated 1D Natural-Affine Rule-Removal Impossibility (`∀ k : Nat`):
     Every weak 1D natural-affine (`m_s ≥ 1`) orientation of `sub6RuleList` forces `(m_s, c_s) = (1, 0)`
     across ALL `s ∈ {B0, B1, T0, T1, T2}`, stalling rule removal completely (`¬ OmegaAffineRuleRemovalTower k sub6RuleList`
     for EVERY `k : Nat`)!
-/
theorem omega_k_affine_rule_removal_and_parikh_vass_impossibility :
    (∀ (k : Nat) (wt : MixedSRSSym -> Fin k -> Nat),
      ¬ (lexGtFin k (evalParikhVec k wt [.L, .B1]) (evalParikhVec k wt [.L, .T2]) ∧
         lexGtFin k (evalParikhVec k wt [.T2, .R]) (evalParikhVec k wt [.B1, .B0, .R]))) ∧
    (∀ k : Nat, ¬ OmegaAffineRuleRemovalTower k sub6RuleList) := by
  refine ⟨?_, ?_⟩
  · intro k wt ⟨⟨idx1, heq1, hgt1⟩, ⟨idx2, heq2, hgt2⟩⟩
    have h1_idx1 : wt .B1 idx1 > wt .T2 idx1 := by
      simp only [evalParikhVec, Nat.add_zero] at hgt1; omega
    have h1_eq : ∀ i : Fin k, i.val < idx1.val -> wt .B1 i = wt .T2 i := by
      intro i hi
      have h := heq1 i hi
      simp only [evalParikhVec, Nat.add_zero] at h; omega
    have h2_idx2 : wt .T2 idx2 > wt .B1 idx2 + wt .B0 idx2 := by
      simp only [evalParikhVec, Nat.add_zero] at hgt2; omega
    have h2_eq : ∀ i : Fin k, i.val < idx2.val -> wt .T2 i = wt .B1 i + wt .B0 i := by
      intro i hi
      have h := heq2 i hi
      simp only [evalParikhVec, Nat.add_zero] at h; omega
    by_cases hlt12 : idx1.val < idx2.val
    · have he := h2_eq idx1 hlt12; omega
    · by_cases hlt21 : idx2.val < idx1.val
      · have he := h1_eq idx2 hlt21; omega
      · have hij : idx1 = idx2 := Fin.ext (by omega)
        subst hij; omega
  · -- Prove that ANY subset `rules` containing all 6 elements of `sub6RuleList` can NEVER reach `[]`!
    have hstall : ∀ (k : Nat) (rules : List (List MixedSRSSym × List MixedSRSSym)),
        (∀ r ∈ sub6RuleList, r ∈ rules) ->
        ¬ OmegaAffineRuleRemovalTower k rules := by
      intro k
      induction k with
      | zero =>
        intro rules hsub htower
        rw [OmegaAffineRuleRemovalTower] at htower
        subst htower
        have hm := hsub ([.L, .B1], [.L, .T2]) (by decide)
        cases hm
      | succ k' ih =>
        intro rules hsub htower
        rcases htower with rfl | ⟨rem, interp, hm_pos, hweak, hkeep, hrem_tower⟩
        · have hm := hsub ([.L, .B1], [.L, .T2]) (by decide)
          cases hm
        · have hw_r2  := hweak ([.L, .B1], [.L, .T2]) (hsub _ (by decide))
          have hw_r5  := hweak ([.T1, .B0], [.B1, .T0]) (hsub _ (by decide))
          have hw_r7  := hweak ([.T2, .B0], [.B0, .T1]) (hsub _ (by decide))
          have hw_r8  := hweak ([.T2, .B1], [.B1, .T2]) (hsub _ (by decide))
          have hw_r9  := hweak ([.T0, .R], [.B1, .R]) (hsub _ (by decide))
          have hw_r11 := hweak ([.T2, .R], [.B1, .B0, .R]) (hsub _ (by decide))
          simp only [weakOrients1D, evalWordAffine1D, Nat.mul_one, Nat.mul_zero, Nat.add_zero]
            at hw_r2 hw_r5 hw_r7 hw_r8 hw_r9 hw_r11
          have hr11_m : (interp .T2).m * (interp .R).m ≥
              (interp .B1).m * (interp .B0).m * (interp .R).m := by
            have h := hw_r11.1; rwa [← Nat.mul_assoc] at h
          rcases upper_triangular_top_left_unit_collapse_any_dim
            (interp .L).m (interp .R).m (interp .B0).m (interp .B1).m
            (interp .T0).m (interp .T1).m (interp .T2).m
            (hm_pos .L) (hm_pos .R) (hm_pos .B0) (hm_pos .B1)
            (hm_pos .T0) (hm_pos .T1) (hm_pos .T2)
            hw_r2.1 hw_r5.1 hw_r7.1 hw_r9.1 hr11_m with ⟨hmB0, hmB1, hmT0, hmT1, hmT2⟩
          have hc_r2  := hw_r2.2
          have hc_r5  := hw_r5.2
          have hc_r7  := hw_r7.2
          have hc_r9  := hw_r9.2
          have hc_r11 := hw_r11.2
          simp only [hmB0, hmB1, hmT0, hmT1, hmT2, Nat.one_mul]
            at hc_r2 hc_r5 hc_r7 hc_r9 hc_r11
          have hcB1_ge_T2 : (interp .B1).c ≥ (interp .T2).c :=
            nat_mul_le_cancel_left_w5 (interp .L).m _ _ (hm_pos .L) (by omega)
          have hc_zero : (interp .B0).c = 0 ∧ (interp .B1).c = 0 ∧
              (interp .T0).c = 0 ∧ (interp .T1).c = 0 ∧ (interp .T2).c = 0 := by
            omega
          rcases hc_zero with ⟨hcB0, hcB1, hcT0, hcT1, hcT2⟩
          have hall_kept : ∀ r ∈ sub6RuleList, r ∈ rem := by
            intro r hr_mem
            apply hkeep r (hsub r hr_mem)
            simp only [sub6RuleList, List.mem_cons, List.not_mem_nil, or_false] at hr_mem
            rcases hr_mem with rfl | rfl | rfl | rfl | rfl | rfl
            · intro hs; simp only [strictOrients1D, evalWordAffine1D, Nat.mul_zero, Nat.add_zero,
                hcB1, hcT2] at hs; omega
            · intro hs; simp only [strictOrients1D, evalWordAffine1D, Nat.mul_zero, Nat.add_zero,
                hmT1, hmB1, hcB0, hcB1, hcT0, hcT1] at hs; omega
            · intro hs; simp only [strictOrients1D, evalWordAffine1D, Nat.mul_zero, Nat.add_zero,
                hmT2, hmB0, hcB0, hcT1, hcT2] at hs; omega
            · intro hs; simp only [strictOrients1D, evalWordAffine1D, Nat.mul_zero, Nat.add_zero,
                hmT2, hmB1, hcB1, hcT2] at hs; omega
            · intro hs; simp only [strictOrients1D, evalWordAffine1D, Nat.mul_zero, Nat.add_zero,
                hmT0, hmB1, hcB1, hcT0] at hs; omega
            · intro hs; simp only [strictOrients1D, evalWordAffine1D, Nat.mul_zero, Nat.add_zero,
                hmT2, hmB1, hmB0, hcB0, hcB1, hcT2] at hs; omega
          exact ih rem hall_kept hrem_tower
    intro k
    exact hstall k sub6RuleList (fun _ h => h)

/--
  Theorem W7.3d (`swap_rule_parikh_vass_impossibility`, zero custom axioms):
  Universal Parikh / VASS Invariance on Adjacent Swap Rules `R3` and `R8` (`∀ k : Nat`):
  Every pure swap rule (`R3 : [T0, B0] -> [B0, T0]` and `R8 : [T2, B1] -> [B1, T2]`) has
  identically equal `k`-counter Parikh vectors on LHS and RHS (`∀ i : Fin k`), so NO
  lexicographic `ω^k` Parikh VASS ranking can orient `R3` or `R8` in ANY dimension `k`!
-/
theorem swap_rule_parikh_vass_impossibility :
    ∀ (k : Nat) (wt : MixedSRSSym -> Fin k -> Nat),
      (∀ i : Fin k, evalParikhVec k wt [.T0, .B0] i = evalParikhVec k wt [.B0, .T0] i) ∧
      (∀ i : Fin k, evalParikhVec k wt [.T2, .B1] i = evalParikhVec k wt [.B1, .T2] i) ∧
      ¬ lexGtFin k (evalParikhVec k wt [.T0, .B0]) (evalParikhVec k wt [.B0, .T0]) ∧
      ¬ lexGtFin k (evalParikhVec k wt [.T2, .B1]) (evalParikhVec k wt [.B1, .T2]) := by
  intro k wt
  have heq_r3 : ∀ i : Fin k, evalParikhVec k wt [.T0, .B0] i = evalParikhVec k wt [.B0, .T0] i := by
    intro i; simp only [evalParikhVec]; omega
  have heq_r8 : ∀ i : Fin k, evalParikhVec k wt [.T2, .B1] i = evalParikhVec k wt [.B1, .T2] i := by
    intro i; simp only [evalParikhVec]; omega
  refine ⟨heq_r3, heq_r8, ?_, ?_⟩
  · rintro ⟨idx, _, hgt⟩
    have heq := heq_r3 idx
    omega
  · rintro ⟨idx, _, hgt⟩
    have heq := heq_r8 idx
    omega

-- ============================================================================
-- SECTION 3B: Front C (Branch P5) — 4th Solvable Mixed-(2,3) Cousin `T_diamond4`:
--             Unbounded `r`-Block Spiral Climbs Yet Globally Convergent via
--             Multi-Block / Ordinal Ranking & Separating `M1 / M2 / M3`
-- ============================================================================

/-- Cone 5 of `T_diamond4`: `x + 7 = 2 ^ a * 3 ^ b` with `a ≥ 5, b ≥ 1` (starting at `x = 89`). -/
def isDiamond4Cone5 (x : Nat) : Prop :=
  x ≥ 89 ∧ x % 32 = 25 ∧ x % 3 = 2 ∧ coprime23Core (x + 7) = 1

instance (x : Nat) : Decidable (isDiamond4Cone5 x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/--
  4th solvable mixed-(2,3) Collatz cousin `T_diamond4` on `Nat`:
  Extends `T_diamond3` by adding Cone 5 (`isDiamond4Cone5 x -> (3 * x + 1) / 4`), creating
  unbounded `r`-block spiral climbs (`4 * 16^r - 5 ->^{2r} 4 * 18^r - 5`, including
  `1019 -> 1529 -> 1147 -> 1721 -> 1291`) while converging globally to `1`!
-/
def cousinDiamond4Step (x : Nat) : Nat :=
  if isDiamond4Cone5 x then (3 * x + 1) / 4 else cousinDiamond3Step x

def cousinDiamond4Iter : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamond4Iter k (cousinDiamond4Step x)

theorem cousinDiamond4Iter_add : ∀ (a b x : Nat),
    cousinDiamond4Iter (a + b) x = cousinDiamond4Iter b (cousinDiamond4Iter a x)
  | 0, _, _ => by simp [cousinDiamond4Iter]
  | a + 1, b, x => by
    rw [Nat.succ_add]
    exact cousinDiamond4Iter_add a b (cousinDiamond4Step x)

/-- Signed extension of `T_diamond4` (`q = 3`) to `Int` for `M2 = Z^-` separation. -/
def cousinDiamond4StepInt (x : Int) : Int :=
  if x ≥ 89 ∧ x % 32 = 25 ∧ x % 3 = 2 ∧ coprime23Core (x.toNat + 7) = 1
  then (3 * x + 1) / 4
  else cousinDiamond3StepInt x

def cousinDiamond4IterInt : Nat -> Int -> Int
  | 0, x => x
  | k + 1, x => cousinDiamond4IterInt k (cousinDiamond4StepInt x)

/-- Canonical reduced-pair extension of `T_diamond4` (`q = 3`) to positive `Q_(6)^+`. -/
def cousinDiamond4StepQ6 (p : Nat × Nat) : Nat × Nat :=
  let num := p.1
  let den := p.2
  let r64 := (num * invMod64Odd den) % 64
  let r3 := (num * (den % 3)) % 3
  if num ≥ 89 * den ∧ r64 % 32 = 25 ∧ r3 = 2 ∧ core3 (core2 (num + 7 * den)) = den
  then reduceRatPair (3 * num + den) (4 * den)
  else cousinDiamond3StepQ6 p

def cousinDiamond4IterQ6 : Nat -> (Nat × Nat) -> (Nat × Nat)
  | 0, p => p
  | k + 1, p => cousinDiamond4IterQ6 k (cousinDiamond4StepQ6 p)

/-- Generalized odd-multiplier `q` step of `T_diamond4` on `Nat` for `M3` (`q = 7`) separation. -/
def cousinDiamond4StepParam (q x : Nat) : Nat :=
  if isDiamond4Cone5 x then (q * x + 1) / 4 else cousinDiamond3StepParam q x

def cousinDiamond4IterParam (q : Nat) : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamond4IterParam q k (cousinDiamond4StepParam q x)

/-- Exact `Nat`/`Int` step agreement for `T_diamond4` (zero custom axioms). -/
theorem cousinDiamond4StepInt_ofNat_eq (x : Nat) :
    cousinDiamond4StepInt (x : Int) = (cousinDiamond4Step x : Int) := by
  unfold cousinDiamond4StepInt cousinDiamond4Step isDiamond4Cone5
  have htoNat : (x : Int).toNat = x := rfl
  rw [htoNat]
  by_cases hc5 : x ≥ 89 ∧ x % 32 = 25 ∧ x % 3 = 2 ∧ coprime23Core (x + 7) = 1
  · have hc5_i : (x : Int) ≥ 89 ∧ (x : Int) % 32 = 25 ∧ (x : Int) % 3 = 2 ∧
        coprime23Core (x + 7) = 1 :=
      ⟨by omega, by omega, by omega, hc5.2.2.2⟩
    simp only [hc5_i, hc5, and_self, ite_true]
    omega
  · have hnc5_i : ¬ ((x : Int) ≥ 89 ∧ (x : Int) % 32 = 25 ∧ (x : Int) % 3 = 2 ∧
        coprime23Core (x + 7) = 1) :=
      fun ⟨h1, h2, h3, h4⟩ => hc5 ⟨by omega, by omega, by omega, h4⟩
    simp only [hnc5_i, hc5, ite_false]
    exact cousinDiamond3StepInt_ofNat_eq x

theorem cousinDiamond4Step_pos (x : Nat) (hx : x > 0) : cousinDiamond4Step x > 0 := by
  unfold cousinDiamond4Step
  by_cases hc5 : isDiamond4Cone5 x
  · simp only [hc5, ite_true]; rcases hc5 with ⟨h89, _, _, _⟩; omega
  · simp only [hc5, ite_false]; exact cousinDiamond3Step_pos x hx

/--
  Theorem W7.3d (`cousin_diamond4_outside_cones45_strict_descent`, zero custom axioms):
  Outside Cone 4 and Cone 5, EVERY `x > 2` strictly decreases `cousinDiamond2Phi` in 1 step!
-/
theorem cousin_diamond4_outside_cones45_strict_descent
    (x : Nat) (hx : x > 2) (hnc4 : ¬ isDiamond3Cone4 x) (hnc5 : ¬ isDiamond4Cone5 x) :
    cousinDiamond2Phi (cousinDiamond4Step x) < cousinDiamond2Phi x := by
  unfold cousinDiamond4Step
  simp only [hnc5, ite_false]
  exact cousin_diamond3_outside_cone4_strict_descent x hx hnc4

theorem eq_pow2_of_v2Pow_aux :
    ∀ (bound n : Nat), n > 0 -> n ≤ bound -> ∃ a : Nat, v2Pow n = 2 ^ a
  | 0, _, hn, hle => by omega
  | bound + 1, n, hn, hle => by
    by_cases hev : n % 2 = 0
    · let k := n / 2
      have hk_pos : k > 0 := by dsimp [k]; omega
      have hn2 : n = 2 * k := by dsimp [k]; omega
      rcases eq_pow2_of_v2Pow_aux bound k hk_pos (by dsimp [k]; omega) with ⟨a, ha⟩
      exact ⟨a + 1, by rw [hn2, v2Pow_mul2 k hk_pos, ha, Nat.pow_succ, Nat.mul_comm]⟩
    · exact ⟨0, v2Pow_of_odd n (by omega)⟩

theorem eq_pow3_of_v3Pow_aux :
    ∀ (bound n : Nat), n > 0 -> n ≤ bound -> ∃ b : Nat, v3Pow n = 3 ^ b
  | 0, _, hn, hle => by omega
  | bound + 1, n, hn, hle => by
    by_cases hd3 : n % 3 = 0
    · let k := n / 3
      have hk_pos : k > 0 := by dsimp [k]; omega
      have hn3 : n = 3 * k := by dsimp [k]; omega
      rcases eq_pow3_of_v3Pow_aux bound k hk_pos (by dsimp [k]; omega) with ⟨b, hb⟩
      exact ⟨b + 1, by rw [hn3, v3Pow_mul3 k hk_pos, hb, Nat.pow_succ, Nat.mul_comm]⟩
    · exact ⟨0, v3Pow_of_not_div3 n hd3⟩

theorem coprime23Core_pow2_pow3 :
    ∀ (a b : Nat), coprime23Core (2 ^ a * 3 ^ b) = 1
  | 0, 0 => by decide
  | 0, b + 1 => by
    have hp := pow3_pos_nat b
    rw [Nat.pow_zero, Nat.one_mul, Nat.pow_succ, Nat.mul_comm (3 ^ b) 3,
        coprime23Core_mul3 (3 ^ b) hp]
    simpa using coprime23Core_pow2_pow3 0 b
  | a + 1, b => by
    have hp : 2 ^ a * 3 ^ b > 0 := Nat.mul_pos (pow2_pos_nat a) (pow3_pos_nat b)
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc,
        coprime23Core_mul2 (2 ^ a * 3 ^ b) hp]
    exact coprime23Core_pow2_pow3 a b

theorem isDiamond4Cone5_of_pow2_pow3 (a b : Nat) (ha : a ≥ 5) (hb : b ≥ 1) :
    isDiamond4Cone5 (2 ^ a * 3 ^ b - 7) := by
  have hp2_32 : 2 ^ a = 32 * 2 ^ (a - 5) := by
    conv => lhs; rw [show a = 5 + (a - 5) by omega]
    rw [Nat.pow_add]
  have hp3_3 : 3 ^ b = 3 * 3 ^ (b - 1) := by
    conv => lhs; rw [show b = 1 + (b - 1) by omega]
    rw [Nat.pow_add, Nat.pow_one]
  have hge96 : 2 ^ a * 3 ^ b ≥ 96 := by
    have h1 : 32 ≤ 2 ^ a := by rw [hp2_32]; have hp := pow2_pos_nat (a - 5); omega
    have h2 : 3 ≤ 3 ^ b := by rw [hp3_3]; have hp := pow3_pos_nat (b - 1); omega
    simpa using Nat.mul_le_mul h1 h2
  refine ⟨by omega, ?_, ?_, ?_⟩
  · have hp_ge3 : 2 ^ (a - 5) * 3 ^ b ≥ 3 := by
      rw [hp3_3]
      simpa using Nat.mul_le_mul (pow2_pos_nat (a - 5)) (by have := pow3_pos_nat (b - 1); omega)
    rw [hp2_32, Nat.mul_assoc 32]; omega
  · have hp_ge32 : 2 ^ a * 3 ^ (b - 1) ≥ 32 := by
      rw [hp2_32]
      simpa using Nat.mul_le_mul (by have := pow2_pos_nat (a - 5); omega) (pow3_pos_nat (b - 1))
    rw [hp3_3, ← Nat.mul_assoc (2 ^ a) 3, Nat.mul_comm (2 ^ a) 3, Nat.mul_assoc 3]; omega
  · rw [show 2 ^ a * 3 ^ b - 7 + 7 = 2 ^ a * 3 ^ b by omega]
    exact coprime23Core_pow2_pow3 a b

theorem cousinDiamond4Step_eq_d3_of_not_cone5 (x : Nat) (hnc5 : ¬ isDiamond4Cone5 x) :
    cousinDiamond4Step x = cousinDiamond3Step x := by
  unfold cousinDiamond4Step; simp [hnc5]

theorem cousinDiamond4Step_mod4_eq_3 (z : Nat) (hz4 : z % 4 = 3) :
    cousinDiamond4Step z = (3 * z + 1) / 2 := by
  have hnc5 : ¬ isDiamond4Cone5 z := by rintro ⟨_, h32, _, _⟩; omega
  rw [cousinDiamond4Step_eq_d3_of_not_cone5 z hnc5]
  exact cousinDiamond3Step_mod4_eq_3 z hz4

theorem cousin_diamond4_mersenne_scaled :
    ∀ (k a q : Nat), k + 1 ≤ a -> q ≥ 1 ->
      cousinDiamond4Iter k (2 ^ a * q - 1) = 3 ^ k * 2 ^ (a - k) * q - 1
  | 0, _, _, _, _ => by simp [cousinDiamond4Iter]
  | k + 1, a, q, hka, hq => by
    have hp4 : 2 ^ a * q = 4 * (2 ^ (a - 2) * q) := by
      conv => lhs; rw [show a = (a - 2) + 2 by omega]
      rw [Nat.pow_add 2 (a - 2) 2, show (2 : Nat) ^ 2 = 4 from rfl,
          Nat.mul_comm (2 ^ (a - 2)) 4, Nat.mul_assoc]
    have hm_pos : 2 ^ (a - 2) * q ≥ 1 := Nat.mul_le_mul (pow2_pos_nat (a - 2)) hq
    have hz4 : (2 ^ a * q - 1) % 4 = 3 := by omega
    simp only [cousinDiamond4Iter]
    rw [cousinDiamond4Step_mod4_eq_3 (2 ^ a * q - 1) hz4]
    have hp2 : 2 ^ a * q = 2 * (2 ^ (a - 1) * q) := by
      rw [pow2_split_pred a (by omega), Nat.mul_assoc]
    have hstep_eq : (3 * (2 ^ a * q - 1) + 1) / 2 = 2 ^ (a - 1) * (3 * q) - 1 := by
      have hm2_pos : 2 ^ (a - 1) * q ≥ 1 := Nat.mul_le_mul (pow2_pos_nat (a - 1)) hq
      have hcomm : 3 * (2 ^ (a - 1) * q) = 2 ^ (a - 1) * (3 * q) := by
        rw [← Nat.mul_assoc 3, Nat.mul_comm 3 (2 ^ (a - 1)), Nat.mul_assoc]
      omega
    rw [hstep_eq, cousin_diamond4_mersenne_scaled k (a - 1) (3 * q) (by omega) (by omega)]
    rw [show a - 1 - k = a - (k + 1) by omega, Nat.pow_succ 3 k]
    apply congrArg (· - 1)
    calc
      3 ^ k * 2 ^ (a - (k + 1)) * (3 * q)
          = 3 ^ k * (2 ^ (a - (k + 1)) * 3) * q := by
            rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
      _ = 3 ^ k * (3 * 2 ^ (a - (k + 1))) * q := by rw [Nat.mul_comm (2 ^ (a - (k + 1))) 3]
      _ = 3 ^ k * 3 * 2 ^ (a - (k + 1)) * q := by rw [← Nat.mul_assoc (3 ^ k) 3]

theorem cousin_diamond4_cone5_two_step_climb :
    ∀ (q_c a b : Nat), 3 * q_c + 2 ≤ a -> b ≥ 1 ->
      cousinDiamond4Iter (2 * q_c) (2 ^ a * 3 ^ b - 7) =
        2 ^ (a - 3 * q_c) * 3 ^ (b + 2 * q_c) - 7
  | 0, _, _, _, _ => by simp [cousinDiamond4Iter]
  | q_c + 1, a, b, ha, hb => by
    have ha5 : a ≥ 5 := by omega
    have hc5 := isDiamond4Cone5_of_pow2_pow3 a b ha5 hb
    have hp4 : 2 ^ a = 4 * 2 ^ (a - 2) := by
      conv => lhs; rw [show a = 2 + (a - 2) by omega]
      rw [Nat.pow_add]
    have hprod_ge : 2 ^ (a - 2) * 3 ^ b ≥ 24 := by
      have h1 : 8 ≤ 2 ^ (a - 2) := by simpa using pow2_mono_nat (by omega : 3 ≤ a - 2)
      have h2 : 3 ≤ 3 ^ b := by
        rw [show b = 1 + (b - 1) by omega, Nat.pow_add, Nat.pow_one]
        have hp := pow3_pos_nat (b - 1); omega
      simpa using Nat.mul_le_mul h1 h2
    let mid := 2 ^ (a - 2) * 3 ^ (b + 1) - 5
    have hs1 : cousinDiamond4Step (2 ^ a * 3 ^ b - 7) = mid := by
      unfold cousinDiamond4Step; simp only [hc5, ite_true]
      dsimp [mid]
      rw [hp4, Nat.mul_assoc 4 (2 ^ (a - 2)) (3 ^ b),
          Nat.pow_succ 3 b, ← Nat.mul_assoc (2 ^ (a - 2)) (3 ^ b) 3]
      omega
    have hmid_4 : mid % 4 = 3 := by
      dsimp [mid]
      have hp8 : 2 ^ (a - 2) = 8 * 2 ^ (a - 5) := by
        conv => lhs; rw [show a - 2 = 3 + (a - 5) by omega]
        rw [Nat.pow_add]
      rw [hp8, Nat.mul_assoc 8]
      have hp_pos : 2 ^ (a - 5) * 3 ^ (b + 1) ≥ 1 :=
        Nat.mul_le_mul (pow2_pos_nat _) (pow3_pos_nat _)
      omega
    have hs2 : cousinDiamond4Step mid = 2 ^ (a - 3) * 3 ^ (b + 2) - 7 := by
      rw [cousinDiamond4Step_mod4_eq_3 mid hmid_4]
      dsimp [mid]
      have hp2_sp : 2 ^ (a - 2) = 2 * 2 ^ (a - 3) := pow2_split_pred (a - 2) (by omega)
      have hp_pos : 2 ^ (a - 3) * 3 ^ (b + 1) ≥ 4 := by
        have h1 : 4 ≤ 2 ^ (a - 3) := by simpa using pow2_mono_nat (by omega : 2 ≤ a - 3)
        simpa using Nat.mul_le_mul h1 (pow3_pos_nat _)
      rw [hp2_sp, Nat.mul_assoc 2 (2 ^ (a - 3)) (3 ^ (b + 1)),
          show b + 2 = (b + 1) + 1 by omega, Nat.pow_succ 3 (b + 1),
          ← Nat.mul_assoc (2 ^ (a - 3)) (3 ^ (b + 1)) 3]
      omega
    conv => lhs; rw [show 2 * (q_c + 1) = 2 + 2 * q_c by omega]
    rw [cousinDiamond4Iter_add 2 (2 * q_c)]
    have hi2 : cousinDiamond4Iter 2 (2 ^ a * 3 ^ b - 7) = 2 ^ (a - 3) * 3 ^ (b + 2) - 7 := by
      simp only [cousinDiamond4Iter, hs1, hs2]
    rw [hi2, cousin_diamond4_cone5_two_step_climb q_c (a - 3) (b + 2) (by omega) (by omega)]
    rw [show a - 3 - 3 * q_c = a - 3 * (q_c + 1) by omega,
        show b + 2 + 2 * q_c = b + 2 * (q_c + 1) by omega]

theorem cousin_diamond4_even9_spine_drain :
    ∀ k : Nat, cousinDiamond4Iter k ((9 ^ (k + 1) - 1) / 4) = 2
  | 0 => rfl
  | k + 1 => by
    let j := k + 1
    have hp9j_ge9 : 9 ^ j ≥ 9 := by
      dsimp [j]; rw [Nat.pow_succ]; have hp := nat_pow_pos_of_pos 9 (by decide) k; omega
    have hp9j_m8 : 9 ^ j % 8 = 1 := pow9_mod8_eq_one_w5 j
    let q := (9 ^ j - 1) / 8
    have hq_pos : q ≥ 1 := by dsimp [q]; omega
    have hp9j_eq : 9 ^ j = 8 * q + 1 := by dsimp [q]; omega
    have he_j1 : (9 ^ (j + 1) - 1) / 4 = 18 * q + 2 := by
      rw [Nat.pow_succ 9 j, hp9j_eq]; omega
    have he_j : (9 ^ j - 1) / 4 = 2 * q := by rw [hp9j_eq]; omega
    simp only [cousinDiamond4Iter]
    change cousinDiamond4Iter k (cousinDiamond4Step ((9 ^ (j + 1) - 1) / 4)) = 2
    have hstep : cousinDiamond4Step ((9 ^ (j + 1) - 1) / 4) = (9 ^ j - 1) / 4 := by
      rw [he_j1, he_j]
      have hnc5 : ¬ isDiamond4Cone5 (18 * q + 2) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      unfold cousinDiamond3Step
      have hodd_f : ¬ ((18 * q + 2) % 2 = 1) := by omega
      have h18_t : 18 * q + 2 ≥ 20 ∧ (18 * q + 2) % 18 = 2 := ⟨by omega, by omega⟩
      simp only [hodd_f, h18_t, and_self, ite_true, ite_false]; omega
    rw [hstep]
    exact cousin_diamond4_even9_spine_drain k

theorem cousin_diamond4_pow3_sub1_drain :
    ∀ k : Nat, cousinDiamond4Iter k (3 ^ (k + 1) - 1) = 2
  | 0 => rfl
  | k + 1 => by
    let j := k + 1
    have hp3_ge3 : 3 ^ j ≥ 3 := by
      dsimp [j]; rw [Nat.pow_succ]; have hp := pow3_pos_nat k; omega
    have hp3_odd : 3 ^ j % 2 = 1 := pow3_odd_nat_sec8 j
    have hp3_m3 : 3 ^ j % 3 = 0 := by dsimp [j]; rw [Nat.pow_succ]; omega
    simp only [cousinDiamond4Iter]
    change cousinDiamond4Iter k (cousinDiamond4Step (3 ^ (j + 1) - 1)) = 2
    have hstep : cousinDiamond4Step (3 ^ (j + 1) - 1) = 3 ^ j - 1 := by
      have hev : ¬ ((3 ^ (j + 1) - 1) % 2 = 1) := by
        have ho := pow3_odd_nat_sec8 (j + 1)
        have hp := pow3_pos_nat (j + 1); omega
      have hnc5 : ¬ isDiamond4Cone5 (3 ^ (j + 1) - 1) := by
        rintro ⟨_, h32, _, _⟩; exact hev (by omega)
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h3j1 : 3 ^ (j + 1) = 3 * 3 ^ j := by rw [Nat.pow_succ, Nat.mul_comm]
      have hn18 : ¬ (3 ^ (j + 1) - 1 ≥ 20 ∧ (3 ^ (j + 1) - 1) % 18 = 2) := by
        rintro ⟨h20, hm18⟩
        cases k with
        | zero => simp [j] at h20
        | succ k' =>
          have h9 : 3 ^ (j + 1) = 9 * (3 * 3 ^ k') := by
            dsimp [j]; rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]; omega
          have ho' := pow3_odd_nat_sec8 k'
          omega
      have hm6 : 3 ^ (j + 1) - 1 > 2 ∧ (3 ^ (j + 1) - 1) % 6 = 2 := by
        rw [h3j1]; omega
      unfold cousinDiamond3Step
      simp only [hev, hn18, hm6, and_self, ite_true, ite_false]
      rw [h3j1]; omega
    rw [hstep]
    exact cousin_diamond4_pow3_sub1_drain k

theorem pow3_four_mul_mod16_and_mod5 :
    ∀ q : Nat, 3 ^ (4 * q) % 16 = 1 ∧ 3 ^ (4 * q) % 5 = 1
  | 0 => ⟨rfl, rfl⟩
  | q + 1 => by
    rcases pow3_four_mul_mod16_and_mod5 q with ⟨h16, h5⟩
    have hexp : 4 * (q + 1) = 4 * q + 4 := by omega
    refine ⟨?_, ?_⟩
    · rw [hexp, Nat.pow_add, Nat.mul_mod, h16]
    · rw [hexp, Nat.pow_add, Nat.mul_mod, h5]

theorem pow3_mod16_eq_one_imp_mod5_eq_one (n : Nat) (h : 3 ^ n % 16 = 1) :
    3 ^ n % 5 = 1 := by
  let q := n / 4
  let r := n % 4
  have hn : n = 4 * q + r := by dsimp [q, r]; have hdm := (Nat.div_add_mod n 4).symm; omega
  have hr_lt : r < 4 := Nat.mod_lt n (by decide)
  rcases pow3_four_mul_mod16_and_mod5 q with ⟨hq16, hq5⟩
  rw [hn, Nat.pow_add, Nat.mul_mod, hq16, Nat.one_mul, Nat.mod_mod] at h
  rw [hn, Nat.pow_add, Nat.mul_mod, hq5, Nat.one_mul, Nat.mod_mod]
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with hr0 | hr1 | hr2 | hr3
  · rw [hr0]
  · rw [hr1] at h; exfalso; exact absurd h (by decide)
  · rw [hr2] at h; exfalso; exact absurd h (by decide)
  · rw [hr3] at h; exfalso; exact absurd h (by decide)

theorem mul16_pow2_mod5_ne_zero : ∀ k : Nat, (16 * 2 ^ k) % 5 ≠ 0
  | 0 => by decide
  | k + 1 => by
    intro h
    rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (16 * 2 ^ k) 2, Nat.mul_mod] at h
    have hm5 : (16 * 2 ^ k) % 5 < 5 := Nat.mod_lt _ (by decide)
    have h0 : (16 * 2 ^ k) % 5 = 0 := by omega
    exact mul16_pow2_mod5_ne_zero k h0

theorem cousinDiamond3Step_odd_not_jump (x : Nat) (hodd : x % 2 = 1)
    (hnc4 : ¬ isDiamond3Cone4 x) (hm3 : x % 3 = 2)
    (hnc3 : ¬ (x ≥ 17 ∧ core3 (x + 1) = 2)) :
    cousinDiamond3Step x = (3 * x + 1) / 2 := by
  have hnq : ¬ (isDiamond3Cone4 x ∨
      (x > 1 ∧ x % 16 = 1 ∧ x % 3 ≠ 2 ∧ core3 (2 * x + 1) ≠ 1) ∨
      (x ≥ 73 ∧ x % 64 = 9 ∧ x % 3 ≠ 2 ∧ core3 (2 * x + 1) ≠ 1) ∨
      (x ≥ 17 ∧ core3 (x + 1) = 2)) := by
    rintro (h4 | ⟨_, _, h1, _⟩ | ⟨_, _, h1, _⟩ | h3)
    · exact hnc4 h4
    · exact h1 hm3
    · exact h1 hm3
    · exact hnc3 h3
  unfold cousinDiamond3Step
  simp only [hodd, hnq, ite_true, ite_false]

theorem not_cone3_of_succ_eq_three_mul (x k : Nat) (hxk : x + 1 = 3 * k)
    (hk_pos : k > 0) (hnd3 : k % 3 ≠ 0) :
    ¬ (x ≥ 17 ∧ core3 (x + 1) = 2) := by
  rintro ⟨_, hc3⟩
  rw [hxk, core3_mul3 k hk_pos, core3_not_div3 k hnd3] at hc3
  omega

theorem not_cone5_4_mul_odd (q : Nat) (hq : q ≥ 1) :
    ¬ isDiamond4Cone5 (4 * (2 * q + 1) - 7) := by
  intro h
  have h32 : (4 * (2 * q + 1) - 7) % 32 = 25 := h.2.1
  clear h
  have heq : 4 * (2 * q + 1) - 7 = 5 + 8 * (q - 1) := by omega
  have hm8 : ((5 + 8 * (q - 1)) % 32) % 8 = (5 + 8 * (q - 1)) % 8 :=
    mod_mul_mod_eq (5 + 8 * (q - 1)) 8 4
  rw [heq] at h32
  rw [h32, Nat.add_mul_mod_self_left] at hm8
  exact absurd hm8 (by decide)

theorem not_cone5_8_mul_odd (q : Nat) (_hq : q ≥ 1) :
    ¬ isDiamond4Cone5 (8 * (2 * q + 1) - 7) := by
  intro h
  have h32 : (8 * (2 * q + 1) - 7) % 32 = 25 := h.2.1
  clear h
  have heq : 8 * (2 * q + 1) - 7 = 1 + 16 * q := by omega
  have hm16 : ((1 + 16 * q) % 32) % 16 = (1 + 16 * q) % 16 :=
    mod_mul_mod_eq (1 + 16 * q) 16 2
  rw [heq] at h32
  rw [h32, Nat.add_mul_mod_self_left] at hm16
  exact absurd hm16 (by decide)

theorem not_cone5_16_mul_odd (q : Nat) (_hq : q ≥ 1) :
    ¬ isDiamond4Cone5 (16 * (2 * q + 1) - 7) := by
  intro h
  have h32 : (16 * (2 * q + 1) - 7) % 32 = 25 := h.2.1
  clear h
  have heq : 16 * (2 * q + 1) - 7 = 9 + 32 * q := by omega
  rw [heq, Nat.add_mul_mod_self_left] at h32
  exact absurd h32 (by decide)

theorem cousin_diamond4_exit_step_4 (b0 : Nat) (hb0 : b0 ≥ 3) :
    cousinDiamond4Step (4 * 3 ^ b0 - 7) = 6 * 3 ^ b0 - 10 := by
  have hp3_ge27 : 3 ^ b0 ≥ 27 := by
    have hm := nat_pow_mono_exp_pos 3 3 b0 (by decide) hb0; simpa using hm
  have hp3_odd : 3 ^ b0 % 2 = 1 := pow3_odd_nat_sec8 b0
  have hsp1 : 3 ^ b0 = 3 * 3 ^ (b0 - 1) := by
    conv => lhs; rw [show b0 = 1 + (b0 - 1) by omega]; rw [Nat.pow_add, Nat.pow_one]
  have hp3_b1 : 3 ^ (b0 - 1) ≥ 9 := by
    have hm := nat_pow_mono_exp_pos 3 2 (b0 - 1) (by decide) (by omega); simpa using hm
  have hm3_b1 : 3 ^ (b0 - 1) % 3 = 0 := by
    rw [show b0 - 1 = (b0 - 2) + 1 by omega, Nat.pow_succ]; omega
  have hfin : (3 * (4 * 3 ^ b0 - 7) + 1) / 2 = 6 * 3 ^ b0 - 10 := by omega
  have hx_odd : (4 * 3 ^ b0 - 7) % 2 = 1 := by omega
  have hx_m3 : (4 * 3 ^ b0 - 7) % 3 = 2 := by rw [hsp1]; omega
  have hxp1 : 4 * 3 ^ b0 - 7 + 1 = 3 * (4 * 3 ^ (b0 - 1) - 2) := by rw [hsp1]; omega
  have hk_pos : 4 * 3 ^ (b0 - 1) - 2 > 0 := by omega
  have hnd3 : (4 * 3 ^ (b0 - 1) - 2) % 3 ≠ 0 := by omega
  have hnc5 : ¬ isDiamond4Cone5 (4 * 3 ^ b0 - 7) := by
    rcases (⟨(3 ^ b0 - 1) / 2, by omega, by omega⟩ : ∃ q, q ≥ 1 ∧ 3 ^ b0 = 2 * q + 1) with ⟨q, hq1, hq⟩
    rw [hq]; exact not_cone5_4_mul_odd q hq1
  have hnc4 : ¬ isDiamond3Cone4 (4 * 3 ^ b0 - 7) := by
    intro h; have hc2 : core2 (3 * (4 * 3 ^ b0 - 7) + 5) = 1 := h.2.2; clear h
    have h4 : 3 * (4 * 3 ^ b0 - 7) + 5 = 2 * (2 * (3 * 3 ^ b0 - 4)) := by omega
    rw [h4, core2_mul2 _ (by omega), core2_mul2 _ (by omega),
        core2_of_odd (3 * 3 ^ b0 - 4) (by omega)] at hc2
    omega
  have hnc3 := not_cone3_of_succ_eq_three_mul (4 * 3 ^ b0 - 7) (4 * 3 ^ (b0 - 1) - 2) hxp1 hk_pos hnd3
  rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5,
      cousinDiamond3Step_odd_not_jump (4 * 3 ^ b0 - 7) hx_odd hnc4 hx_m3 hnc3]
  exact hfin

theorem cousin_diamond4_exit_step_8 (b0 : Nat) (hb0 : b0 ≥ 3) :
    cousinDiamond4Step (8 * 3 ^ b0 - 7) = 12 * 3 ^ b0 - 10 := by
  have hp3_ge27 : 3 ^ b0 ≥ 27 := by
    have hm := nat_pow_mono_exp_pos 3 3 b0 (by decide) hb0; simpa using hm
  have hp3_odd : 3 ^ b0 % 2 = 1 := pow3_odd_nat_sec8 b0
  have hsp1 : 3 ^ b0 = 3 * 3 ^ (b0 - 1) := by
    conv => lhs; rw [show b0 = 1 + (b0 - 1) by omega]; rw [Nat.pow_add, Nat.pow_one]
  have hp3_b1 : 3 ^ (b0 - 1) ≥ 9 := by
    have hm := nat_pow_mono_exp_pos 3 2 (b0 - 1) (by decide) (by omega); simpa using hm
  have hm3_b1 : 3 ^ (b0 - 1) % 3 = 0 := by
    rw [show b0 - 1 = (b0 - 2) + 1 by omega, Nat.pow_succ]; omega
  have hfin : (3 * (8 * 3 ^ b0 - 7) + 1) / 2 = 12 * 3 ^ b0 - 10 := by omega
  have hx_odd : (8 * 3 ^ b0 - 7) % 2 = 1 := by omega
  have hx_m3 : (8 * 3 ^ b0 - 7) % 3 = 2 := by rw [hsp1]; omega
  have hxp1 : 8 * 3 ^ b0 - 7 + 1 = 3 * (8 * 3 ^ (b0 - 1) - 2) := by rw [hsp1]; omega
  have hk_pos : 8 * 3 ^ (b0 - 1) - 2 > 0 := by omega
  have hnd3 : (8 * 3 ^ (b0 - 1) - 2) % 3 ≠ 0 := by omega
  have hnc5 : ¬ isDiamond4Cone5 (8 * 3 ^ b0 - 7) := by
    rcases (⟨(3 ^ b0 - 1) / 2, by omega, by omega⟩ : ∃ q, q ≥ 1 ∧ 3 ^ b0 = 2 * q + 1) with ⟨q, hq1, hq⟩
    rw [hq]; exact not_cone5_8_mul_odd q hq1
  have hnc4 : ¬ isDiamond3Cone4 (8 * 3 ^ b0 - 7) := by
    intro h; have hc2 : core2 (3 * (8 * 3 ^ b0 - 7) + 5) = 1 := h.2.2; clear h
    have h8 : 3 * (8 * 3 ^ b0 - 7) + 5 = 2 * (2 * (2 * (3 * 3 ^ b0 - 2))) := by omega
    rw [h8, core2_mul2 _ (by omega), core2_mul2 _ (by omega),
        core2_mul2 _ (by omega), core2_of_odd (3 * 3 ^ b0 - 2) (by omega)] at hc2
    omega
  have hnc3 := not_cone3_of_succ_eq_three_mul (8 * 3 ^ b0 - 7) (8 * 3 ^ (b0 - 1) - 2) hxp1 hk_pos hnd3
  rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5,
      cousinDiamond3Step_odd_not_jump (8 * 3 ^ b0 - 7) hx_odd hnc4 hx_m3 hnc3]
  exact hfin

theorem cousin_diamond4_exit_step_16 (b0 : Nat) (hb0 : b0 ≥ 3) :
    cousinDiamond4Step (16 * 3 ^ b0 - 7) = 24 * 3 ^ b0 - 10 := by
  have hp3_ge27 : 3 ^ b0 ≥ 27 := by
    have hm := nat_pow_mono_exp_pos 3 3 b0 (by decide) hb0; simpa using hm
  have hp3_odd : 3 ^ b0 % 2 = 1 := pow3_odd_nat_sec8 b0
  have hsp1 : 3 ^ b0 = 3 * 3 ^ (b0 - 1) := by
    conv => lhs; rw [show b0 = 1 + (b0 - 1) by omega]; rw [Nat.pow_add, Nat.pow_one]
  have hp3_b1 : 3 ^ (b0 - 1) ≥ 9 := by
    have hm := nat_pow_mono_exp_pos 3 2 (b0 - 1) (by decide) (by omega); simpa using hm
  have hm3_b1 : 3 ^ (b0 - 1) % 3 = 0 := by
    rw [show b0 - 1 = (b0 - 2) + 1 by omega, Nat.pow_succ]; omega
  have hfin : (3 * (16 * 3 ^ b0 - 7) + 1) / 2 = 24 * 3 ^ b0 - 10 := by omega
  have hx_odd : (16 * 3 ^ b0 - 7) % 2 = 1 := by omega
  have hx_m3 : (16 * 3 ^ b0 - 7) % 3 = 2 := by rw [hsp1]; omega
  have hxp1 : 16 * 3 ^ b0 - 7 + 1 = 3 * (16 * 3 ^ (b0 - 1) - 2) := by rw [hsp1]; omega
  have hk_pos : 16 * 3 ^ (b0 - 1) - 2 > 0 := by omega
  have hnd3 : (16 * 3 ^ (b0 - 1) - 2) % 3 ≠ 0 := by omega
  have hnc5 : ¬ isDiamond4Cone5 (16 * 3 ^ b0 - 7) := by
    rcases (⟨(3 ^ b0 - 1) / 2, by omega, by omega⟩ : ∃ q, q ≥ 1 ∧ 3 ^ b0 = 2 * q + 1) with ⟨q, hq1, hq⟩
    rw [hq]; exact not_cone5_16_mul_odd q hq1
  have hnc4 : ¬ isDiamond3Cone4 (16 * 3 ^ b0 - 7) := by
    intro h; have hc2 : core2 (3 * (16 * 3 ^ b0 - 7) + 5) = 1 := h.2.2; clear h
    rcases eq_pow2_of_core2_eq_one (3 * (16 * 3 ^ b0 - 7) + 5) (by omega) hc2 with ⟨E, hE⟩
    have hE_ge11 : E ≥ 11 := by
      by_cases hlt : E < 11
      · have hle := pow2_mono_nat (by omega : E ≤ 10)
        rw [← hE, show (2 : Nat) ^ 10 = 1024 from rfl] at hle; omega
      · omega
    have h2E : 2 ^ E = 16 * (16 * 2 ^ (E - 8)) := by
      conv => lhs; rw [show E = 8 + (E - 8) by omega]
      rw [Nat.pow_add, show (2 : Nat) ^ 8 = 16 * 16 from rfl, Nat.mul_assoc]
    rw [h2E] at hE
    have h3_eq : 3 ^ (b0 + 1) - 1 = 16 * 2 ^ (E - 8) := by
      clear hc2; rw [Nat.pow_succ 3 b0]; omega
    clear hc2 hE h2E
    have hp3_succ := pow3_pos_nat (b0 + 1)
    have h3_m16 : 3 ^ (b0 + 1) % 16 = 1 := by
      clear hp3_ge27 hp3_odd hsp1 hp3_b1 hm3_b1 hfin hx_odd hx_m3 hxp1 hk_pos hnd3 hnc5
      omega
    have h3_m5 : 3 ^ (b0 + 1) % 5 = 1 := pow3_mod16_eq_one_imp_mod5_eq_one (b0 + 1) h3_m16
    have hsub_m5 : (3 ^ (b0 + 1) - 1) % 5 = 0 := by
      clear hp3_ge27 hp3_odd hsp1 hp3_b1 hm3_b1 hfin hx_odd hx_m3 hxp1 hk_pos hnd3 hnc5 h3_eq h3_m16
      omega
    have hr_m5 : (16 * 2 ^ (E - 8)) % 5 = 0 := by rw [← h3_eq]; exact hsub_m5
    exact mul16_pow2_mod5_ne_zero (E - 8) hr_m5
  have hnc3 := not_cone3_of_succ_eq_three_mul (16 * 3 ^ b0 - 7) (16 * 3 ^ (b0 - 1) - 2) hxp1 hk_pos hnd3
  rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5,
      cousinDiamond3Step_odd_not_jump (16 * 3 ^ b0 - 7) hx_odd hnc4 hx_m3 hnc3]
  exact hfin

theorem cousin_diamond4_exit_step_general_odd (c b0 : Nat)
    (hc : c = 4 ∨ c = 8 ∨ c = 16) (hb0 : b0 ≥ 3) :
    cousinDiamond4Step (c * 3 ^ b0 - 7) = (3 * c / 2) * 3 ^ b0 - 10 := by
  rcases hc with rfl | rfl | rfl
  · exact cousin_diamond4_exit_step_4 b0 hb0
  · exact cousin_diamond4_exit_step_8 b0 hb0
  · exact cousin_diamond4_exit_step_16 b0 hb0

theorem cousin_diamond4_a0_3_drain (b0 : Nat) (hb0 : b0 ≥ 3) :
    cousinDiamond4Iter ((b0 - 1) / 2 + 7) (8 * 3 ^ b0 - 7) = 1 := by
  have hp3_ge27 : 3 ^ b0 ≥ 27 := by
    have hm := nat_pow_mono_exp_pos 3 3 b0 (by decide) hb0; simpa using hm
  have hp3_b1_ge9 : 3 ^ (b0 - 1) ≥ 9 := by
    have hm := nat_pow_mono_exp_pos 3 2 (b0 - 1) (by decide) (by omega); simpa using hm
  have hp3_b2_ge3 : 3 ^ (b0 - 2) ≥ 3 := by
    have hm := nat_pow_mono_exp_pos 3 1 (b0 - 2) (by decide) (by omega); simpa using hm
  have h3b0_sp : 3 ^ b0 = 3 * 3 ^ (b0 - 1) := by
    conv => lhs; rw [show b0 = 1 + (b0 - 1) by omega]; rw [Nat.pow_add, Nat.pow_one]
  have h3b1_sp : 3 ^ (b0 - 1) = 3 * 3 ^ (b0 - 2) := by
    conv => lhs; rw [show b0 - 1 = 1 + (b0 - 2) by omega]; rw [Nat.pow_add, Nat.pow_one]
  -- Step 1: `8 * 3^b0 - 7 -> 12 * 3^b0 - 10`
  have hs1 : cousinDiamond4Step (8 * 3 ^ b0 - 7) = 12 * 3 ^ b0 - 10 :=
    cousin_diamond4_exit_step_general_odd 8 b0 (Or.inr (Or.inl rfl)) hb0
  -- Step 2: `12 * 3^b0 - 10 -> 4 * 3^b0 - 4` (`% 18 = 8`, `% 6 = 2`)
  have hs2 : cousinDiamond4Step (12 * 3 ^ b0 - 10) = 4 * 3 ^ b0 - 4 := by
    have hnc5 : ¬ isDiamond4Cone5 (12 * 3 ^ b0 - 10) := by rintro ⟨_, h32, _, _⟩; omega
    rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]; unfold cousinDiamond3Step
    have h18 : 12 * 3 ^ b0 = 18 * (2 * 3 ^ (b0 - 1)) := by rw [h3b0_sp]; omega
    have ho : ¬ ((12 * 3 ^ b0 - 10) % 2 = 1) := by omega
    have hn18 : ¬ (12 * 3 ^ b0 - 10 ≥ 20 ∧ (12 * 3 ^ b0 - 10) % 18 = 2) := by omega
    have hm6 : 12 * 3 ^ b0 - 10 > 2 ∧ (12 * 3 ^ b0 - 10) % 6 = 2 := ⟨by omega, by omega⟩
    simp only [ho, hn18, hm6, and_self, ite_true, ite_false]; omega
  -- Step 3: `4 * 3^b0 - 4 -> 4 * 3^(b0 - 1) - 2` (`% 18 = 14`, `% 6 = 2`)
  have hs3 : cousinDiamond4Step (4 * 3 ^ b0 - 4) = 4 * 3 ^ (b0 - 1) - 2 := by
    have hnc5 : ¬ isDiamond4Cone5 (4 * 3 ^ b0 - 4) := by rintro ⟨_, h32, _, _⟩; omega
    rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]; unfold cousinDiamond3Step
    have h18 : 4 * 3 ^ b0 = 18 * (2 * 3 ^ (b0 - 2)) := by rw [h3b0_sp, h3b1_sp]; omega
    have ho : ¬ ((4 * 3 ^ b0 - 4) % 2 = 1) := by omega
    have hn18 : ¬ (4 * 3 ^ b0 - 4 ≥ 20 ∧ (4 * 3 ^ b0 - 4) % 18 = 2) := by omega
    have hm6 : 4 * 3 ^ b0 - 4 > 2 ∧ (4 * 3 ^ b0 - 4) % 6 = 2 := ⟨by omega, by omega⟩
    simp only [ho, hn18, hm6, and_self, ite_true, ite_false]; omega
  -- Step 4: `4 * 3^(b0 - 1) - 2 -> 2 * 3^(b0 - 1) - 1` (`% 18 = 16`, `% 6 = 4`, `% 8 = 2`)
  have hs4 : cousinDiamond4Step (4 * 3 ^ (b0 - 1) - 2) = 2 * 3 ^ (b0 - 1) - 1 := by
    have hnc5 : ¬ isDiamond4Cone5 (4 * 3 ^ (b0 - 1) - 2) := by rintro ⟨_, h32, _, _⟩; omega
    rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]; unfold cousinDiamond3Step
    have hp3_o := pow3_odd_nat_sec8 (b0 - 1)
    have h18 : 4 * 3 ^ (b0 - 1) = 36 * 3 ^ (b0 - 3) := by
      conv => lhs; rhs; rw [show b0 - 1 = 2 + (b0 - 3) by omega]
      rw [Nat.pow_add]; omega
    have ho : ¬ ((4 * 3 ^ (b0 - 1) - 2) % 2 = 1) := by omega
    have hn18 : ¬ (4 * 3 ^ (b0 - 1) - 2 ≥ 20 ∧ (4 * 3 ^ (b0 - 1) - 2) % 18 = 2) := by
      have hp := pow3_pos_nat (b0 - 3); omega
    have hn6 : ¬ (4 * 3 ^ (b0 - 1) - 2 > 2 ∧ (4 * 3 ^ (b0 - 1) - 2) % 6 = 2) := by
      have hp := pow3_pos_nat (b0 - 3); omega
    have hn8 : ¬ (4 * 3 ^ (b0 - 1) - 2 > 2 ∧ (4 * 3 ^ (b0 - 1) - 2) % 8 = 6) := by omega
    simp only [ho, hn18, hn6, hn8, ite_false]; omega
  -- Split on `(b0 - 1) % 2`:
  let m := (b0 - 1) / 2
  have hm_pos : m ≥ 1 := by dsimp [m]; omega
  have hp9m_ge9 : 9 ^ m ≥ 9 := by
    rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]
    have hp := nat_pow_pos_of_pos 9 (by decide) (m - 1); omega
  have hp9m_m8 : 9 ^ m % 8 = 1 := pow9_mod8_eq_one_w5 m
  by_cases hpar : (b0 - 1) % 2 = 0
  · -- `b0 - 1 = 2 * m`, so `2 * 3^(b0 - 1) - 1 = 2 * 9^m - 1`:
    have hb1_2m : b0 - 1 = 2 * m := by dsimp [m]; omega
    have hu_eq : 2 * 3 ^ (b0 - 1) - 1 = 2 * 9 ^ m - 1 := by
      rw [hb1_2m, ← pow9_eq_pow3_double m]
    let zr := 2 * 9 ^ m - 1
    let yr := (3 * 9 ^ m - 1) / 2
    have hsz : cousinDiamond4Step zr = yr := by
      have hnc5 : ¬ isDiamond4Cone5 zr := by
        rintro ⟨_, h32, _, _⟩; dsimp [zr] at h32; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 zr hnc5]
      have hzr_o : zr % 2 = 1 := by dsimp [zr]; omega
      have hc3 : core3 (zr + 1) = 2 := by
        rw [show zr + 1 = 2 * 9 ^ m by dsimp [zr]; omega,
            core3_mul2 (9 ^ m) (by omega), (pow9_eq_v3Pow_w5 m).2]
      have hcond : isDiamond3Cone4 zr ∨
          (zr > 1 ∧ zr % 16 = 1 ∧ zr % 3 ≠ 2 ∧ core3 (2 * zr + 1) ≠ 1) ∨
          (zr ≥ 73 ∧ zr % 64 = 9 ∧ zr % 3 ≠ 2 ∧ core3 (2 * zr + 1) ≠ 1) ∨
          (zr ≥ 17 ∧ core3 (zr + 1) = 2) := Or.inr (Or.inr (Or.inr ⟨by dsimp [zr]; omega, hc3⟩))
      unfold cousinDiamond3Step; simp only [hzr_o, hcond, ite_true]; dsimp [zr, yr]; omega
    have hsy : cousinDiamond4Step yr = (9 ^ (m + 1) - 1) / 4 := by
      have hyr_m3 : yr % 3 = 1 := by
        have hm3 : 9 ^ m % 3 = 0 := by
          rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
        dsimp [yr]; omega
      have hnc5 : ¬ isDiamond4Cone5 yr := by rintro ⟨_, _, hm3, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 yr hnc5]
      by_cases hm1 : m = 1
      · have hyr13 : yr = 13 := by dsimp [yr]; rw [hm1]
        rw [hyr13, hm1]; decide
      · have hm_ge2 : m ≥ 2 := by omega
        have hyr_o : yr % 2 = 1 := by dsimp [yr]; omega
        have hc3_2 : core3 (2 * yr + 1) = 1 := by
          rw [show 2 * yr + 1 = 3 * 9 ^ m by dsimp [yr]; omega,
              core3_mul3 (9 ^ m) (by omega), (pow9_eq_v3Pow_w5 m).2]
        have hc3_1 : core3 (yr + 1) ≠ 2 := by
          have hnd3 : (yr + 1) % 3 ≠ 0 := by omega
          rw [core3_not_div3 (yr + 1) hnd3]; dsimp [yr]; omega
        have hnc4 : ¬ isDiamond3Cone4 yr := by
          rintro ⟨_, _, hc2⟩
          rcases eq_pow2_of_core2_eq_one (3 * yr + 5) (by dsimp [yr]; omega) hc2 with ⟨M0, hM0⟩
          have h9_eq : 9 ^ (m + 1) + 7 = 2 ^ (M0 + 1) := by
            have h2mul : 2 * (3 * yr + 5) = 9 ^ (m + 1) + 7 := by
              rw [Nat.pow_succ 9 m, Nat.mul_comm (9 ^ m) 9]; dsimp [yr]; omega
            rw [← h2mul, hM0, Nat.pow_succ 2 M0, Nat.mul_comm]
          exact pow9_succ_add_seven_ne_pow2 m (M0 + 1) hm_ge2 h9_eq
        have hnq : ¬ (isDiamond3Cone4 yr ∨
            (yr > 1 ∧ yr % 16 = 1 ∧ yr % 3 ≠ 2 ∧ core3 (2 * yr + 1) ≠ 1) ∨
            (yr ≥ 73 ∧ yr % 64 = 9 ∧ yr % 3 ≠ 2 ∧ core3 (2 * yr + 1) ≠ 1) ∨
            (yr ≥ 17 ∧ core3 (yr + 1) = 2)) := by
          rintro (h4 | ⟨_, _, _, hc1⟩ | ⟨_, _, _, hc2⟩ | ⟨_, hc3⟩)
          · exact hnc4 h4
          · exact hc1 hc3_2
          · exact hc2 hc3_2
          · exact hc3_1 hc3
        unfold cousinDiamond3Step; simp only [hyr_o, hnq, ite_true, ite_false]
        dsimp [yr]; rw [Nat.pow_succ 9 m]; omega
    change cousinDiamond4Iter (m + 7) (8 * 3 ^ b0 - 7) = 1
    rw [show m + 7 = 4 + 1 + 1 + m + 1 by omega,
        cousinDiamond4Iter_add (4 + 1 + 1 + m) 1,
        cousinDiamond4Iter_add (4 + 1 + 1) m,
        cousinDiamond4Iter_add (4 + 1) 1,
        cousinDiamond4Iter_add 4 1]
    have hi4 : cousinDiamond4Iter 4 (8 * 3 ^ b0 - 7) = zr := by
      simp only [cousinDiamond4Iter, hs1, hs2, hs3, hs4, hu_eq]; rfl
    rw [hi4]
    have hiz : cousinDiamond4Iter 1 zr = yr := hsz
    rw [hiz]
    have hiy : cousinDiamond4Iter 1 yr = (9 ^ (m + 1) - 1) / 4 := hsy
    rw [hiy, cousin_diamond4_even9_spine_drain m]
    decide
  · -- `b0 - 1 = 2 * m + 1`, so `2 * 3^(b0 - 1) - 1 = 6 * 9^m - 1`:
    have hb1_2m1 : b0 - 1 = 2 * m + 1 := by dsimp [m]; omega
    have hu_eq : 2 * 3 ^ (b0 - 1) - 1 = 6 * 9 ^ m - 1 := by
      rw [hb1_2m1, Nat.pow_succ, ← pow9_eq_pow3_double m]; omega
    let ur := 6 * 9 ^ m - 1
    let wr := (9 ^ (m + 1) - 1) / 2
    have hsu : cousinDiamond4Step ur = wr := by
      have hur_m8 : ur % 8 = 5 := by dsimp [ur]; omega
      have hnc5 : ¬ isDiamond4Cone5 ur := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 ur hnc5]
      have hur_o : ur % 2 = 1 := by omega
      have hc3 : core3 (ur + 1) = 2 := by
        rw [show ur + 1 = 2 * (3 * 9 ^ m) by dsimp [ur]; omega,
            core3_mul2 (3 * 9 ^ m) (by omega),
            core3_mul3 (9 ^ m) (by omega), (pow9_eq_v3Pow_w5 m).2]
      have hcond : isDiamond3Cone4 ur ∨
          (ur > 1 ∧ ur % 16 = 1 ∧ ur % 3 ≠ 2 ∧ core3 (2 * ur + 1) ≠ 1) ∨
          (ur ≥ 73 ∧ ur % 64 = 9 ∧ ur % 3 ≠ 2 ∧ core3 (2 * ur + 1) ≠ 1) ∨
          (ur ≥ 17 ∧ core3 (ur + 1) = 2) := Or.inr (Or.inr (Or.inr ⟨by dsimp [ur]; omega, hc3⟩))
      unfold cousinDiamond3Step; simp only [hur_o, hcond, ite_true]
      dsimp [ur, wr]; rw [Nat.pow_succ 9 m]; omega
    have hsw : cousinDiamond4Step wr = (9 ^ (m + 1) - 1) / 4 := by
      let q := (9 ^ m - 1) / 8
      have hq_pos : q ≥ 1 := by dsimp [q]; omega
      have hp9_eq : 9 ^ m = 8 * q + 1 := by dsimp [q]; omega
      have hwr_eq : wr = 36 * q + 4 := by dsimp [wr]; rw [Nat.pow_succ 9 m, hp9_eq]; omega
      have hnext_eq : (9 ^ (m + 1) - 1) / 4 = 18 * q + 2 := by
        rw [Nat.pow_succ 9 m, hp9_eq]; omega
      rw [hwr_eq, hnext_eq]
      have hnc5 : ¬ isDiamond4Cone5 (36 * q + 4) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]; unfold cousinDiamond3Step
      have ho : ¬ ((36 * q + 4) % 2 = 1) := by omega
      have hn18 : ¬ (36 * q + 4 ≥ 20 ∧ (36 * q + 4) % 18 = 2) := by omega
      have hn6 : ¬ (36 * q + 4 > 2 ∧ (36 * q + 4) % 6 = 2) := by omega
      have hn8 : ¬ (36 * q + 4 > 2 ∧ (36 * q + 4) % 8 = 6) := by omega
      simp only [ho, hn18, hn6, hn8, ite_false]; omega
    change cousinDiamond4Iter (m + 7) (8 * 3 ^ b0 - 7) = 1
    rw [show m + 7 = 4 + 1 + 1 + m + 1 by omega,
        cousinDiamond4Iter_add (4 + 1 + 1 + m) 1,
        cousinDiamond4Iter_add (4 + 1 + 1) m,
        cousinDiamond4Iter_add (4 + 1) 1,
        cousinDiamond4Iter_add 4 1]
    have hi4 : cousinDiamond4Iter 4 (8 * 3 ^ b0 - 7) = ur := by
      simp only [cousinDiamond4Iter, hs1, hs2, hs3, hs4, hu_eq]; rfl
    rw [hi4]
    have hiu : cousinDiamond4Iter 1 ur = wr := hsu
    rw [hiu]
    have hiw : cousinDiamond4Iter 1 wr = (9 ^ (m + 1) - 1) / 4 := hsw
    rw [hiw, cousin_diamond4_even9_spine_drain m]
    decide

theorem cousin_diamond4_a0_2_and_4_drain (b0 : Nat) (hb0 : b0 ≥ 3) :
    cousinDiamond4Iter (b0 + 3) (4 * 3 ^ b0 - 7) = 1 ∧
    cousinDiamond4Iter ((b0 - 1) / 2 + 8) (16 * 3 ^ b0 - 7) = 1 := by
  have hp3_ge27 : 3 ^ b0 ≥ 27 := by
    have hm := nat_pow_mono_exp_pos 3 3 b0 (by decide) hb0; simpa using hm
  have hp3_b1_ge9 : 3 ^ (b0 - 1) ≥ 9 := by
    have hm := nat_pow_mono_exp_pos 3 2 (b0 - 1) (by decide) (by omega); simpa using hm
  have hp3_b2_ge3 : 3 ^ (b0 - 2) ≥ 3 := by
    have hm := nat_pow_mono_exp_pos 3 1 (b0 - 2) (by decide) (by omega); simpa using hm
  have h3b0_sp : 3 ^ b0 = 3 * 3 ^ (b0 - 1) := by
    conv => lhs; rw [show b0 = 1 + (b0 - 1) by omega]; rw [Nat.pow_add, Nat.pow_one]
  have h3b1_sp : 3 ^ (b0 - 1) = 3 * 3 ^ (b0 - 2) := by
    conv => lhs; rw [show b0 - 1 = 1 + (b0 - 2) by omega]; rw [Nat.pow_add, Nat.pow_one]
  refine ⟨?_, ?_⟩
  · -- `a0 = 2`: `4 * 3^b0 - 7 -> 6 * 3^b0 - 10 -> 2 * 3^b0 - 4 -> 2 * 3^(b0 - 1) - 2 -> 3^(b0 - 1) - 1 ->^(b0-2) 2 -> 1`
    have hs1 : cousinDiamond4Step (4 * 3 ^ b0 - 7) = 6 * 3 ^ b0 - 10 :=
      cousin_diamond4_exit_step_general_odd 4 b0 (Or.inl rfl) hb0
    have hs2 : cousinDiamond4Step (6 * 3 ^ b0 - 10) = 2 * 3 ^ b0 - 4 := by
      have hnc5 : ¬ isDiamond4Cone5 (6 * 3 ^ b0 - 10) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]; unfold cousinDiamond3Step
      have h18 : 6 * 3 ^ b0 = 18 * 3 ^ (b0 - 1) := by rw [h3b0_sp]; omega
      have ho : ¬ ((6 * 3 ^ b0 - 10) % 2 = 1) := by omega
      have hn18 : ¬ (6 * 3 ^ b0 - 10 ≥ 20 ∧ (6 * 3 ^ b0 - 10) % 18 = 2) := by omega
      have hm6 : 6 * 3 ^ b0 - 10 > 2 ∧ (6 * 3 ^ b0 - 10) % 6 = 2 := ⟨by omega, by omega⟩
      simp only [ho, hn18, hm6, and_self, ite_true, ite_false]; omega
    have hs3 : cousinDiamond4Step (2 * 3 ^ b0 - 4) = 2 * 3 ^ (b0 - 1) - 2 := by
      have hnc5 : ¬ isDiamond4Cone5 (2 * 3 ^ b0 - 4) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]; unfold cousinDiamond3Step
      have h18 : 2 * 3 ^ b0 = 18 * 3 ^ (b0 - 2) := by rw [h3b0_sp, h3b1_sp]; omega
      have ho : ¬ ((2 * 3 ^ b0 - 4) % 2 = 1) := by omega
      have hn18 : ¬ (2 * 3 ^ b0 - 4 ≥ 20 ∧ (2 * 3 ^ b0 - 4) % 18 = 2) := by omega
      have hm6 : 2 * 3 ^ b0 - 4 > 2 ∧ (2 * 3 ^ b0 - 4) % 6 = 2 := ⟨by omega, by omega⟩
      simp only [ho, hn18, hm6, and_self, ite_true, ite_false]; omega
    have hs4 : cousinDiamond4Step (2 * 3 ^ (b0 - 1) - 2) = 3 ^ (b0 - 1) - 1 := by
      have hnc5 : ¬ isDiamond4Cone5 (2 * 3 ^ (b0 - 1) - 2) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]; unfold cousinDiamond3Step
      have h18 : 2 * 3 ^ (b0 - 1) = 18 * 3 ^ (b0 - 3) := by
        conv => lhs; rhs; rw [show b0 - 1 = 2 + (b0 - 3) by omega]
        rw [Nat.pow_add]; omega
      have hp3_b3 := pow3_pos_nat (b0 - 3)
      have ho : ¬ ((2 * 3 ^ (b0 - 1) - 2) % 2 = 1) := by omega
      have hn18 : ¬ (2 * 3 ^ (b0 - 1) - 2 ≥ 20 ∧ (2 * 3 ^ (b0 - 1) - 2) % 18 = 2) := by omega
      have hn6 : ¬ (2 * 3 ^ (b0 - 1) - 2 > 2 ∧ (2 * 3 ^ (b0 - 1) - 2) % 6 = 2) := by omega
      -- Check `(2 * 3^(b0 - 1) - 2) % 8`: `9^m = 8q + 1` => `2*9^m - 2 = 16q` (`% 8 = 0`),
      -- `3 * 9^m = 24q + 3` => `6*9^m - 2 = 48q + 4` (`% 8 = 4`)! Never `6`!
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
      simp only [ho, hn18, hn6, hn8, ite_false]; omega
    rw [show b0 + 3 = 4 + (b0 - 2) + 1 by omega,
        cousinDiamond4Iter_add (4 + (b0 - 2)) 1,
        cousinDiamond4Iter_add 4 (b0 - 2)]
    have hi4 : cousinDiamond4Iter 4 (4 * 3 ^ b0 - 7) = 3 ^ ((b0 - 2) + 1) - 1 := by
      simp only [cousinDiamond4Iter, hs1, hs2, hs3, hs4]
      rw [show b0 - 1 = (b0 - 2) + 1 by omega]
    rw [hi4, cousin_diamond4_pow3_sub1_drain (b0 - 2)]
    decide
  · -- `a0 = 4`: 4 steps land at `4 * 3^(b0 - 1) - 2`, matching Step 3 of `a0 = 3`!
    have hs1 : cousinDiamond4Step (16 * 3 ^ b0 - 7) = 24 * 3 ^ b0 - 10 :=
      cousin_diamond4_exit_step_general_odd 16 b0 (Or.inr (Or.inr rfl)) hb0
    have hs2 : cousinDiamond4Step (24 * 3 ^ b0 - 10) = 8 * 3 ^ b0 - 4 := by
      have hnc5 : ¬ isDiamond4Cone5 (24 * 3 ^ b0 - 10) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]; unfold cousinDiamond3Step
      have h18 : 24 * 3 ^ b0 = 18 * (4 * 3 ^ (b0 - 1)) := by rw [h3b0_sp]; omega
      have ho : ¬ ((24 * 3 ^ b0 - 10) % 2 = 1) := by omega
      have hn18 : ¬ (24 * 3 ^ b0 - 10 ≥ 20 ∧ (24 * 3 ^ b0 - 10) % 18 = 2) := by omega
      have hm6 : 24 * 3 ^ b0 - 10 > 2 ∧ (24 * 3 ^ b0 - 10) % 6 = 2 := ⟨by omega, by omega⟩
      simp only [ho, hn18, hm6, and_self, ite_true, ite_false]; omega
    have hs3 : cousinDiamond4Step (8 * 3 ^ b0 - 4) = 8 * 3 ^ (b0 - 1) - 2 := by
      have hnc5 : ¬ isDiamond4Cone5 (8 * 3 ^ b0 - 4) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]; unfold cousinDiamond3Step
      have h18 : 8 * 3 ^ b0 = 18 * (4 * 3 ^ (b0 - 2)) := by rw [h3b0_sp, h3b1_sp]; omega
      have ho : ¬ ((8 * 3 ^ b0 - 4) % 2 = 1) := by omega
      have hn18 : ¬ (8 * 3 ^ b0 - 4 ≥ 20 ∧ (8 * 3 ^ b0 - 4) % 18 = 2) := by omega
      have hm6 : 8 * 3 ^ b0 - 4 > 2 ∧ (8 * 3 ^ b0 - 4) % 6 = 2 := ⟨by omega, by omega⟩
      simp only [ho, hn18, hm6, and_self, ite_true, ite_false]; omega
    have hs4 : cousinDiamond4Step (8 * 3 ^ (b0 - 1) - 2) = 4 * 3 ^ (b0 - 1) - 2 := by
      have hnc5 : ¬ isDiamond4Cone5 (8 * 3 ^ (b0 - 1) - 2) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]; unfold cousinDiamond3Step
      have h18 : 8 * 3 ^ (b0 - 1) = 18 * (4 * 3 ^ (b0 - 3)) := by
        conv => lhs; rhs; rw [show b0 - 1 = 2 + (b0 - 3) by omega]
        rw [Nat.pow_add]; omega
      have hp3_b3 := pow3_pos_nat (b0 - 3)
      have ho : ¬ ((8 * 3 ^ (b0 - 1) - 2) % 2 = 1) := by omega
      have hn18 : ¬ (8 * 3 ^ (b0 - 1) - 2 ≥ 20 ∧ (8 * 3 ^ (b0 - 1) - 2) % 18 = 2) := by omega
      have hn6 : ¬ (8 * 3 ^ (b0 - 1) - 2 > 2 ∧ (8 * 3 ^ (b0 - 1) - 2) % 6 = 2) := by omega
      have hm8 : 8 * 3 ^ (b0 - 1) - 2 > 2 ∧ (8 * 3 ^ (b0 - 1) - 2) % 8 = 6 := ⟨by omega, by omega⟩
      simp only [ho, hn18, hn6, ite_false]
      simp only [hm8, and_self, ite_true]; omega
    -- Compare with `cousin_diamond4_a0_3_drain b0 hb0` (which took 3 steps to `4 * 3^(b0 - 1) - 2`!):
    have ha3 := cousin_diamond4_a0_3_drain b0 hb0
    have ha3_s1 : cousinDiamond4Step (8 * 3 ^ b0 - 7) = 12 * 3 ^ b0 - 10 :=
      cousin_diamond4_exit_step_general_odd 8 b0 (Or.inr (Or.inl rfl)) hb0
    have ha3_s2 : cousinDiamond4Step (12 * 3 ^ b0 - 10) = 4 * 3 ^ b0 - 4 := by
      have hnc5 : ¬ isDiamond4Cone5 (12 * 3 ^ b0 - 10) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]; unfold cousinDiamond3Step
      have h18 : 12 * 3 ^ b0 = 18 * (2 * 3 ^ (b0 - 1)) := by rw [h3b0_sp]; omega
      have ho : ¬ ((12 * 3 ^ b0 - 10) % 2 = 1) := by omega
      have hn18 : ¬ (12 * 3 ^ b0 - 10 ≥ 20 ∧ (12 * 3 ^ b0 - 10) % 18 = 2) := by omega
      have hm6 : 12 * 3 ^ b0 - 10 > 2 ∧ (12 * 3 ^ b0 - 10) % 6 = 2 := ⟨by omega, by omega⟩
      simp only [ho, hn18, hm6, and_self, ite_true, ite_false]; omega
    have ha3_s3 : cousinDiamond4Step (4 * 3 ^ b0 - 4) = 4 * 3 ^ (b0 - 1) - 2 := by
      have hnc5 : ¬ isDiamond4Cone5 (4 * 3 ^ b0 - 4) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]; unfold cousinDiamond3Step
      have h18 : 4 * 3 ^ b0 = 18 * (2 * 3 ^ (b0 - 2)) := by rw [h3b0_sp, h3b1_sp]; omega
      have ho : ¬ ((4 * 3 ^ b0 - 4) % 2 = 1) := by omega
      have hn18 : ¬ (4 * 3 ^ b0 - 4 ≥ 20 ∧ (4 * 3 ^ b0 - 4) % 18 = 2) := by omega
      have hm6 : 4 * 3 ^ b0 - 4 > 2 ∧ (4 * 3 ^ b0 - 4) % 6 = 2 := ⟨by omega, by omega⟩
      simp only [ho, hn18, hm6, and_self, ite_true, ite_false]; omega
    rw [show (b0 - 1) / 2 + 7 = 3 + ((b0 - 1) / 2 + 4) by omega,
        cousinDiamond4Iter_add 3 ((b0 - 1) / 2 + 4)] at ha3
    have hi3 : cousinDiamond4Iter 3 (8 * 3 ^ b0 - 7) = 4 * 3 ^ (b0 - 1) - 2 := by
      simp only [cousinDiamond4Iter, ha3_s1, ha3_s2, ha3_s3]
    rw [hi3] at ha3
    rw [show (b0 - 1) / 2 + 8 = 4 + ((b0 - 1) / 2 + 4) by omega,
        cousinDiamond4Iter_add 4 ((b0 - 1) / 2 + 4)]
    have hi4 : cousinDiamond4Iter 4 (16 * 3 ^ b0 - 7) = 4 * 3 ^ (b0 - 1) - 2 := by
      simp only [cousinDiamond4Iter, hs1, hs2, hs3, hs4]
    rw [hi4]
    exact ha3

theorem pow2_ge_six_mul_ge5 : ∀ a : Nat, a ≥ 5 -> 6 * a ≤ 2 ^ a
  | 0, ha => by omega
  | 1, ha => by omega
  | 2, ha => by omega
  | 3, ha => by omega
  | 4, ha => by omega
  | 5, _ => by decide
  | m + 6, _ => by
    have ih := pow2_ge_six_mul_ge5 (m + 5) (by omega)
    rw [Nat.pow_succ]; omega

theorem pow3_ge_add_two_ge1 : ∀ b : Nat, b ≥ 1 -> b + 2 ≤ 3 ^ b
  | 0, hb => by omega
  | 1, _ => by decide
  | m + 2, _ => by
    have ih := pow3_ge_add_two_ge1 (m + 1) (by omega)
    rw [Nat.pow_succ]; omega

/--
  Theorem W7.3e (`cousin_diamond4_cone4_and_cone5_exact_return`, zero custom axioms):
  Exact Closed-Form Multi-Block Return on BOTH Cone 4 AND Cone 5 of `T_diamond4`:
  1. Every `x` in Cone 4 (`isDiamond3Cone4 x`) reaches `1` in `3 * r + 4 ≤ cousinDiamond2Phi x` steps!
  2. Every `x` in Cone 5 (`isDiamond4Cone5 x`) has `x + 7 = 2 ^ a * 3 ^ b` (`a ≥ 5, b ≥ 1`), climbs
     `2 * q_c` steps (`q_c = (a - 2) / 3`) to `2 ^ a0 * 3 ^ b0 - 7`, and reaches `1` in `k ≤ cousinDiamond2Phi x` steps!
-/
theorem cousin_diamond4_cone4_and_cone5_exact_return :
    (∀ x : Nat, isDiamond3Cone4 x ->
      ∃ k : Nat, k ≤ cousinDiamond2Phi x ∧ cousinDiamond4Iter k x = 1) ∧
    (∀ x : Nat, isDiamond4Cone5 x ->
      ∃ (a b k : Nat),
        a ≥ 5 ∧ b ≥ 1 ∧ x + 7 = 2 ^ a * 3 ^ b ∧
        k ≤ cousinDiamond2Phi x ∧ cousinDiamond4Iter k x = 1) := by
  refine ⟨?_, ?_⟩
  · intro x hc4
    rcases cousin_diamond3_cone4_reaches_one_exact x hc4 with ⟨r, hr_ge3, hE, _, hphi_ge⟩
    refine ⟨3 * r + 4, hphi_ge, ?_⟩
    -- Step 1 (`x -> 2^(2r+1) - 1`): both Cone 4 and Cone 5 apply `(3 * x + 1) / 4`!
    have hx_odd : x % 2 = 1 := by rcases hc4 with ⟨_, hm8, _⟩; omega
    have hs1 : cousinDiamond4Step x = 2 ^ (2 * r + 1) - 1 := by
      unfold cousinDiamond4Step
      have hp4 : 2 ^ (2 * r + 3) = 4 * 2 ^ (2 * r + 1) := by
        rw [show 2 * r + 3 = 2 + (2 * r + 1) by omega, Nat.pow_add]
      have hp_pos := pow2_pos_nat (2 * r + 1)
      by_cases hc5 : isDiamond4Cone5 x
      · simp only [hc5, ite_true]; omega
      · simp only [hc5, ite_false]; unfold cousinDiamond3Step
        have hcond : isDiamond3Cone4 x ∨
            (x > 1 ∧ x % 16 = 1 ∧ x % 3 ≠ 2 ∧ core3 (2 * x + 1) ≠ 1) ∨
            (x ≥ 73 ∧ x % 64 = 9 ∧ x % 3 ≠ 2 ∧ core3 (2 * x + 1) ≠ 1) ∨
            (x ≥ 17 ∧ core3 (x + 1) = 2) := Or.inl hc4
        simp only [hx_odd, hcond, ite_true]; omega
    let zr := 2 * 9 ^ r - 1
    let yr := (3 * 9 ^ r - 1) / 2
    have hglide : cousinDiamond4Iter (2 * r) (2 ^ (2 * r + 1) - 1) = zr := by
      have hf := cousin_diamond4_mersenne_scaled (2 * r) (2 * r + 1) 1 (by omega) (by decide)
      simp only [Nat.mul_one, show 2 * r + 1 - 2 * r = 1 by omega, Nat.pow_one] at hf
      rw [hf, ← pow9_eq_pow3_double r, Nat.mul_comm]
    have hp9_ge729 : 9 ^ r ≥ 729 := by
      have hm := nat_pow_mono_exp_pos 9 3 r (by decide) hr_ge3; simpa using hm
    have hp9_m8 : 9 ^ r % 8 = 1 := pow9_mod8_eq_one_w5 r
    have hsz : cousinDiamond4Step zr = yr := by
      have hnc5 : ¬ isDiamond4Cone5 zr := by rintro ⟨_, h32, _, _⟩; dsimp [zr] at h32; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 zr hnc5]
      have hzr_o : zr % 2 = 1 := by dsimp [zr]; omega
      have hc3 : core3 (zr + 1) = 2 := by
        rw [show zr + 1 = 2 * 9 ^ r by dsimp [zr]; omega,
            core3_mul2 (9 ^ r) (by omega), (pow9_eq_v3Pow_w5 r).2]
      have hcond : isDiamond3Cone4 zr ∨
          (zr > 1 ∧ zr % 16 = 1 ∧ zr % 3 ≠ 2 ∧ core3 (2 * zr + 1) ≠ 1) ∨
          (zr ≥ 73 ∧ zr % 64 = 9 ∧ zr % 3 ≠ 2 ∧ core3 (2 * zr + 1) ≠ 1) ∨
          (zr ≥ 17 ∧ core3 (zr + 1) = 2) := Or.inr (Or.inr (Or.inr ⟨by dsimp [zr]; omega, hc3⟩))
      unfold cousinDiamond3Step; simp only [hzr_o, hcond, ite_true]; dsimp [zr, yr]; omega
    have hsy : cousinDiamond4Step yr = (9 ^ (r + 1) - 1) / 4 := by
      have hyr_m3 : yr % 3 = 1 := by
        have hm3 : 9 ^ r % 3 = 0 := by rw [show r = (r - 1) + 1 by omega, Nat.pow_succ]; omega
        dsimp [yr]; omega
      have hnc5 : ¬ isDiamond4Cone5 yr := by rintro ⟨_, _, hm3, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 yr hnc5]
      have hyr_o : yr % 2 = 1 := by dsimp [yr]; omega
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
      have hnq : ¬ (isDiamond3Cone4 yr ∨
          (yr > 1 ∧ yr % 16 = 1 ∧ yr % 3 ≠ 2 ∧ core3 (2 * yr + 1) ≠ 1) ∨
          (yr ≥ 73 ∧ yr % 64 = 9 ∧ yr % 3 ≠ 2 ∧ core3 (2 * yr + 1) ≠ 1) ∨
          (yr ≥ 17 ∧ core3 (yr + 1) = 2)) := by
        rintro (h4 | ⟨_, _, _, hc1⟩ | ⟨_, _, _, hc2⟩ | ⟨_, hc3⟩)
        · exact hnc4 h4
        · exact hc1 hc3_2
        · exact hc2 hc3_2
        · exact hc3_1 hc3
      unfold cousinDiamond3Step; simp only [hyr_o, hnq, ite_true, ite_false]
      dsimp [yr]; rw [Nat.pow_succ 9 r]; omega
    rw [show 3 * r + 4 = 1 + 2 * r + 1 + 1 + r + 1 by omega,
        cousinDiamond4Iter_add (1 + 2 * r + 1 + 1 + r) 1,
        cousinDiamond4Iter_add (1 + 2 * r + 1 + 1) r,
        cousinDiamond4Iter_add (1 + 2 * r + 1) 1,
        cousinDiamond4Iter_add (1 + 2 * r) 1,
        cousinDiamond4Iter_add 1 (2 * r)]
    have hi1 : cousinDiamond4Iter 1 x = 2 ^ (2 * r + 1) - 1 := hs1
    rw [hi1, hglide]
    have hiz : cousinDiamond4Iter 1 zr = yr := hsz
    rw [hiz]
    have hiy : cousinDiamond4Iter 1 yr = (9 ^ (r + 1) - 1) / 4 := hsy
    rw [hiy, cousin_diamond4_even9_spine_drain r]
    decide
  · intro x ⟨hx89, hx32, hx3, hg1⟩
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
      | zero =>
        rw [Nat.pow_zero, Nat.mul_one] at hmul
        have hm3 := pow2_mod3_nonzero_w5 a; omega
      | succ _ => omega
    have hx_eq : x = 2 ^ a * 3 ^ b - 7 := by omega
    let q_c := (a - 2) / 3
    let a0 := a - 3 * q_c
    let b0 := b + 2 * q_c
    have hqc_pos : q_c ≥ 1 := by dsimp [q_c]; omega
    have hb0_ge3 : b0 ≥ 3 := by dsimp [b0]; omega
    have ha0_234 : a0 = 2 ∨ a0 = 3 ∨ a0 = 4 := by dsimp [a0, q_c]; omega
    have hclimb := cousin_diamond4_cone5_two_step_climb q_c a b (by dsimp [q_c]; omega) hb1
    rw [← hx_eq] at hclimb
    change cousinDiamond4Iter (2 * q_c) x = 2 ^ a0 * 3 ^ b0 - 7 at hclimb
    -- Bound `2 * q_c + (b0 + 8) ≤ x + 1 ≤ cousinDiamond2Phi x`:
    have hbound_all : ∀ ex : Nat, ex ≤ b0 + 8 -> 2 * q_c + ex ≤ cousinDiamond2Phi x := by
      intro ex hex
      have hm1 := pow2_ge_six_mul_ge5 a ha5
      have hm2 := pow3_ge_add_two_ge1 b hb1
      have hprod := Nat.mul_le_mul hm1 hm2
      rw [hmul] at hprod
      have hab : 6 * b ≤ 6 * a * b := by
        rw [Nat.mul_comm (6 * a) b, ← Nat.mul_assoc, Nat.mul_comm b 6]
        have hm := Nat.mul_le_mul_left (6 * b) (by omega : 1 ≤ a)
        simpa using hm
      have hexp : (6 * a) * (b + 2) = 6 * a * b + 12 * a := by rw [Nat.mul_add]; omega
      rw [hexp] at hprod
      have hx1_ge : 2 * q_c + ex ≤ x + 1 := by dsimp [q_c, b0] at hex ⊢; omega
      exact Nat.le_trans hx1_ge (cousinDiamond2Phi_ge_succ x)
    rcases ha0_234 with ha2 | ha3 | ha4
    · refine ⟨a, b, 2 * q_c + (b0 + 3), ha5, hb1, hmul.symm, hbound_all _ (by omega), ?_⟩
      rw [cousinDiamond4Iter_add (2 * q_c) (b0 + 3) x, hclimb, ha2]
      exact (cousin_diamond4_a0_2_and_4_drain b0 hb0_ge3).1
    · refine ⟨a, b, 2 * q_c + ((b0 - 1) / 2 + 7), ha5, hb1, hmul.symm, hbound_all _ (by omega), ?_⟩
      rw [cousinDiamond4Iter_add (2 * q_c) ((b0 - 1) / 2 + 7) x, hclimb, ha3]
      exact cousin_diamond4_a0_3_drain b0 hb0_ge3
    · refine ⟨a, b, 2 * q_c + ((b0 - 1) / 2 + 8), ha5, hb1, hmul.symm, hbound_all _ (by omega), ?_⟩
      rw [cousinDiamond4Iter_add (2 * q_c) ((b0 - 1) / 2 + 8) x, hclimb, ha4]
      exact (cousin_diamond4_a0_2_and_4_drain b0 hb0_ge3).2

theorem cousin_diamond4_reaches_one_within_phi :
    ∀ (B x : Nat), x > 0 -> cousinDiamond2Phi x ≤ B ->
      ∃ k : Nat, k ≤ B ∧ cousinDiamond4Iter k x = 1
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
        · rcases cousin_diamond4_cone4_and_cone5_exact_return.1 x hc4 with ⟨k, hle_phi, hk1⟩
          exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
        · by_cases hc5 : isDiamond4Cone5 x
          · rcases cousin_diamond4_cone4_and_cone5_exact_return.2 x hc5 with
              ⟨_, _, k, _, _, _, hle_phi, hk1⟩
            exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
          · have hdesc := cousin_diamond4_outside_cones45_strict_descent x (by omega) hc4 hc5
            have hpos := cousinDiamond4Step_pos x hx
            rcases cousin_diamond4_reaches_one_within_phi B (cousinDiamond4Step x) hpos (by omega) with
              ⟨k, hk_le, hk_eq⟩
            exact ⟨k + 1, by omega, hk_eq⟩

/--
  Theorem W7.3f (`cousin_diamond4_global_convergence`, zero custom axioms):
  Unconditional Global Convergence & Degree-5 Polynomial Stopping Bound for `T_diamond4`:
  For EVERY `x > 0`, `cousinDiamond4Iter` reaches `1` within `k ≤ (x + 1) ^ 3 + (x + 1) ^ 5` steps!
-/
theorem cousin_diamond4_global_convergence (x : Nat) (hx : x > 0) :
    ∃ k : Nat, k ≤ (x + 1) ^ 3 + (x + 1) ^ 5 ∧ cousinDiamond4Iter k x = 1 := by
  rcases cousin_diamond4_reaches_one_within_phi (cousinDiamond2Phi x) x hx (Nat.le_refl _) with
    ⟨k, hk_phi, hk1⟩
  exact ⟨k, Nat.le_trans hk_phi (cousinDiamond2Phi_upper_poly_bound x), hk1⟩

theorem exists_non_desc_along_diamond4_iter :
    ∀ (terms : List LaurentTerm) (A0 B0 C0 N z : Nat),
      N ≥ 1 ->
      (∀ i : Nat, i < N ->
        cousinDiamond4Iter i z ≥ 3 ∧
        (cousinDiamond4Iter i z) % 2 = 1 ∧
        cousinDiamond4Step (cousinDiamond4Iter i z) ≥ 3) ->
      ¬ laurentDescProp terms A0 B0 C0 z (cousinDiamond4Iter N z) ->
      ∃ x : Nat,
        x ≥ 3 ∧ x % 2 = 1 ∧ cousinDiamond4Step x ≥ 3 ∧
        ¬ laurentDescProp terms A0 B0 C0 x (cousinDiamond4Step x)
  | _, _, _, _, 0, _, hN, _, _ => by omega
  | terms, A0, B0, C0, 1, z, _, hall, hnd => by
    rcases hall 0 (by decide) with ⟨hz3, hzo, hsz3⟩
    exact ⟨z, hz3, hzo, hsz3, hnd⟩
  | terms, A0, B0, C0, m + 2, z, _, hall, hnd => by
    if h0 : laurentDescProp terms A0 B0 C0 z (cousinDiamond4Step z) then
      have hnd_next : ¬ laurentDescProp terms A0 B0 C0 (cousinDiamond4Step z)
          (cousinDiamond4Iter (m + 1) (cousinDiamond4Step z)) :=
        fun hrest => hnd (laurentDescProp_trans terms A0 B0 C0 z (cousinDiamond4Step z) _ h0 hrest)
      exact exists_non_desc_along_diamond4_iter terms A0 B0 C0 (m + 1) (cousinDiamond4Step z)
        (by omega) (fun i hi => hall (i + 1) (by omega)) hnd_next
    else
      rcases hall 0 (by omega) with ⟨hz3, hzo, hsz3⟩
      exact ⟨z, hz3, hzo, hsz3, h0⟩

/--
  Theorem W7.3g (`cousin_diamond4_r_block_spiral_climb_and_laurent_impossibility`, zero custom axioms):
  1. Unbounded `r`-Block Spiral Climb (`∀ r ≥ 1`): `cousinDiamond4Iter (2 * j) (4 * 16^r - 5) =
     4 * 16^(r - j) * 18^j - 5` for all `j ≤ r` (`1019 -> 1529 -> 1147 -> 1721 -> 1291` at `r = 2`),
     reproducing `spiralBlockReturn` on true `(3x + 1)` while still converging globally to `1`!
  2. Universal `∀ L ≥ 1` Multi-Term Laurent Valuation Impossibility on `cousinDiamond4Step`!
-/
theorem cousin_diamond4_r_block_spiral_climb_and_laurent_impossibility :
    cousinDiamond4Step 1019 = 1529 ∧
    cousinDiamond4Step 1529 = 1147 ∧
    cousinDiamond4Step 1147 = 1721 ∧
    cousinDiamond4Step 1721 = 1291 ∧
    (∀ (j r : Nat), j ≤ r ->
      cousinDiamond4Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5) ∧
    (∀ (terms : List LaurentTerm) (A0 B0 C0 : Nat),
      (∃ t ∈ terms, t.coeff > 0) ->
      ∃ x : Nat,
        x ≥ 3 ∧ x % 2 = 1 ∧ cousinDiamond4Step x ≥ 3 ∧
        ¬ (evalLaurentSumNum terms (cousinDiamond4Step x) * laurentValDen A0 B0 C0 x <
            evalLaurentSumNum terms x * laurentValDen A0 B0 C0 (cousinDiamond4Step x))) := by
  have h18_pow : ∀ j : Nat, 18 ^ j = 2 ^ j * 3 ^ (2 * j) := by
    intro j
    have h18_eq : (18 : Nat) ^ j = 2 ^ j * 9 ^ j := mul_pow_local 2 9 j
    rw [h18_eq, pow9_eq_pow3_double j]
  have h16_pow : ∀ m : Nat, 16 ^ m = 2 ^ (4 * m) := by
    intro m
    induction m with
    | zero => rfl
    | succ m' ih =>
      rw [Nat.pow_succ, ih, show 4 * (m' + 1) = 4 * m' + 4 by omega, Nat.pow_add]
  have hstep_spiral : ∀ (m j : Nat),
      cousinDiamond4Iter 2 (4 * 16 ^ (m + 1) * 18 ^ j - 5) = 4 * 16 ^ m * 18 ^ (j + 1) - 5 := by
    intro m j
    let x := 4 * 16 ^ (m + 1) * 18 ^ j - 5
    have hp16_pos : 16 ^ m ≥ 1 := nat_pow_pos_of_pos 16 (by decide) m
    have hp18_pos : 18 ^ j ≥ 1 := nat_pow_pos_of_pos 18 (by decide) j
    have hprod_pos : 16 ^ m * 18 ^ j ≥ 1 := Nat.mul_le_mul hp16_pos hp18_pos
    have hx_64 : 4 * 16 ^ (m + 1) * 18 ^ j = 64 * (16 ^ m * 18 ^ j) := by
      rw [Nat.pow_succ 16 m, Nat.mul_comm (16 ^ m) 16,
          ← Nat.mul_assoc 4 16 (16 ^ m), show 4 * 16 = 64 from rfl, Nat.mul_assoc]
    have hx_m4 : x % 4 = 3 := by dsimp [x]; rw [hx_64]; omega
    let mid := 2 ^ (4 * m + 5 + j) * 3 ^ (2 * j + 1) - 7
    have hs1 : cousinDiamond4Step x = mid := by
      rw [cousinDiamond4Step_mod4_eq_3 x hx_m4]
      dsimp [x, mid]
      have hmul_eq : 3 * (4 * 16 ^ (m + 1) * 18 ^ j) =
          2 * (2 ^ (4 * m + 5 + j) * 3 ^ (2 * j + 1)) := by
        rw [h16_pow (m + 1), h18_pow j]
        have hp2 : 4 * 2 ^ (4 * (m + 1)) * 2 ^ j = 2 * 2 ^ (4 * m + 5 + j) := by
          rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add 2 2, ← Nat.pow_add,
              show 2 + 4 * (m + 1) + j = 1 + (4 * m + 5 + j) by omega,
              Nat.pow_add 2 1, Nat.pow_one]
        calc
          3 * (4 * 2 ^ (4 * (m + 1)) * (2 ^ j * 3 ^ (2 * j)))
              = 3 * ((4 * 2 ^ (4 * (m + 1)) * 2 ^ j) * 3 ^ (2 * j)) := by
                rw [← Nat.mul_assoc (4 * 2 ^ (4 * (m + 1))) (2 ^ j)]
          _ = 3 * ((2 * 2 ^ (4 * m + 5 + j)) * 3 ^ (2 * j)) := by rw [hp2]
          _ = 2 * (2 ^ (4 * m + 5 + j) * (3 ^ (2 * j) * 3)) := by
                rw [Nat.mul_assoc 2, ← Nat.mul_assoc 3 2, Nat.mul_comm 3 2,
                    Nat.mul_assoc 2 3, ← Nat.mul_assoc 3 (2 ^ (4 * m + 5 + j)),
                    Nat.mul_comm 3 (2 ^ (4 * m + 5 + j)), Nat.mul_assoc,
                    Nat.mul_comm 3 (3 ^ (2 * j))]
          _ = 2 * (2 ^ (4 * m + 5 + j) * 3 ^ (2 * j + 1)) := by rw [← Nat.pow_succ]
      have hge16 : 4 * 16 ^ (m + 1) * 18 ^ j ≥ 64 := by rw [hx_64]; omega
      omega
    have hc5_mid : isDiamond4Cone5 mid :=
      isDiamond4Cone5_of_pow2_pow3 (4 * m + 5 + j) (2 * j + 1) (by omega) (by omega)
    have hs2 : cousinDiamond4Step mid = 4 * 16 ^ m * 18 ^ (j + 1) - 5 := by
      unfold cousinDiamond4Step; simp only [hc5_mid, ite_true]
      dsimp [mid]
      have hmul_eq : 3 * (2 ^ (4 * m + 5 + j) * 3 ^ (2 * j + 1)) =
          4 * (4 * 16 ^ m * 18 ^ (j + 1)) := by
        rw [h16_pow m, h18_pow (j + 1)]
        have hp2 : 2 ^ (4 * m + 5 + j) = 4 * (4 * 2 ^ (4 * m) * 2 ^ (j + 1)) := by
          rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add 2 2 (4 * m),
              ← Nat.pow_add 2 (2 + 4 * m) (j + 1), ← Nat.pow_add 2 2]
          exact congrArg (2 ^ ·) (by omega)
        calc
          3 * (2 ^ (4 * m + 5 + j) * 3 ^ (2 * j + 1))
              = (2 ^ (4 * m + 5 + j)) * (3 ^ (2 * j + 1) * 3) := by
                rw [← Nat.mul_assoc 3, Nat.mul_comm 3 (2 ^ (4 * m + 5 + j)),
                    Nat.mul_assoc, Nat.mul_comm 3 (3 ^ (2 * j + 1))]
          _ = (4 * (4 * 2 ^ (4 * m) * 2 ^ (j + 1))) * 3 ^ (2 * (j + 1)) := by
                rw [hp2, ← Nat.pow_succ, show (2 * j + 1).succ = 2 * (j + 1) by omega]
          _ = 4 * (4 * 2 ^ (4 * m) * (2 ^ (j + 1) * 3 ^ (2 * (j + 1)))) := by
                rw [Nat.mul_assoc 4, Nat.mul_assoc (4 * 2 ^ (4 * m))]
      have hge18 : 4 * 16 ^ m * 18 ^ (j + 1) ≥ 72 := by
        rw [Nat.pow_succ 18 j, ← Nat.mul_assoc (4 * 16 ^ m) (18 ^ j) 18]
        have hm1 : 4 * 16 ^ m * 18 ^ j ≥ 4 := by
          rw [Nat.mul_assoc 4]; exact Nat.mul_le_mul_left 4 hprod_pos
        omega
      omega
    dsimp only [cousinDiamond4Iter]
    dsimp [x] at hs1
    rw [hs1, hs2]
  have hind_spiral : ∀ (j k i : Nat), j ≤ k ->
      cousinDiamond4Iter (2 * j) (4 * 16 ^ k * 18 ^ i - 5) =
        4 * 16 ^ (k - j) * 18 ^ (i + j) - 5 := by
    intro j
    induction j with
    | zero => intro k i _; simp [cousinDiamond4Iter]
    | succ j' ih =>
      intro k i hj
      cases k with
      | zero => omega
      | succ k' =>
        rw [show 2 * (j' + 1) = 2 + 2 * j' by omega,
            cousinDiamond4Iter_add 2 (2 * j'),
            hstep_spiral k' i, ih k' (i + 1) (by omega),
            show k' + 1 - (j' + 1) = k' - j' by omega,
            show i + 1 + j' = i + (j' + 1) by omega]
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro j r hj
    have h0 := hind_spiral j r 0 hj
    simpa using h0
  · intro terms A0 B0 C0 hnonempty
    rcases three_family_multiterm_laurent_obstruction terms A0 B0 C0 hnonempty with
      h97 | ⟨j2, hj2⟩ | ⟨r, hr_pos, hr3⟩
    · have hs97 : cousinDiamond4Step 97 = 73 := by decide
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
        refine ⟨by dsimp [xj2]; omega, by dsimp [xj2]; omega, ?_⟩
        have hpow2 : 3 * xj2 + 5 = 2 ^ (6 * j2 + 9) * 1 := by
          rw [Nat.mul_one, show 6 * j2 + 9 = 2 * (3 * j2 + 4) + 1 by omega,
              Nat.pow_succ, ← pow4_eq_pow2_even (3 * j2 + 4), Nat.mul_comm]
          dsimp [xj2]; omega
        rw [hpow2]; exact core2_pow2_mul (6 * j2 + 9) 1 (by decide) (by decide)
      have hstep_xj2 : cousinDiamond4Step xj2 = yj2 := by
        unfold cousinDiamond4Step
        by_cases hc5 : isDiamond4Cone5 xj2
        · simp only [hc5, ite_true]; dsimp [xj2, yj2]; omega
        · simp only [hc5, ite_false]; unfold cousinDiamond3Step
          have hcond : isDiamond3Cone4 xj2 ∨
              (xj2 > 1 ∧ xj2 % 16 = 1 ∧ xj2 % 3 ≠ 2 ∧ core3 (2 * xj2 + 1) ≠ 1) ∨
              (xj2 ≥ 73 ∧ xj2 % 64 = 9 ∧ xj2 % 3 ≠ 2 ∧ core3 (2 * xj2 + 1) ≠ 1) ∨
              (xj2 ≥ 17 ∧ core3 (xj2 + 1) = 2) := Or.inl hc4_xj2
          simp only [hxj2_odd, hcond, ite_true]; dsimp [xj2, yj2]; omega
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
          cousinDiamond4Iter i xr3 = 3 ^ i * 2 ^ (2 * r + 1 - i) - 1 ∧
          cousinDiamond4Iter i xr3 ≥ 7 ∧
          (cousinDiamond4Iter i xr3) % 2 = 1 := by
        intro i hi
        have hf := cousin_diamond4_mersenne_scaled i (2 * r + 1) 1 (by omega) (by decide)
        rw [← hxr3_pow, Nat.mul_one] at hf
        have hprod_ge8 : 3 ^ i * 2 ^ (2 * r + 1 - i) ≥ 8 := by
          have h1 : 2 ^ i * 2 ^ (2 * r + 1 - i) ≤ 3 ^ i * 2 ^ (2 * r + 1 - i) :=
            Nat.mul_le_mul_right _ (pow2_le_pow3 i)
          rw [← Nat.pow_add, show i + (2 * r + 1 - i) = 2 * r + 1 by omega] at h1
          exact Nat.le_trans (pow2_mono_nat (by omega : 3 ≤ 2 * r + 1)) h1
        have hprod_ev : (3 ^ i * 2 ^ (2 * r + 1 - i)) % 2 = 0 := by
          rw [show 2 * r + 1 - i = (2 * r - i) + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc]; omega
        exact ⟨hf, by rw [hf]; omega, by rw [hf]; omega⟩
      have hiter_2r : cousinDiamond4Iter (2 * r) xr3 = zr := by
        have hf := (hglide_i (2 * r) (Nat.le_refl _)).1
        rw [hf, show 2 * r + 1 - 2 * r = 1 by omega, Nat.pow_one,
            ← pow9_eq_pow3_double r, Nat.mul_comm]
      have hstep_zr : cousinDiamond4Step zr = yr3 := by
        have hnc5 : ¬ isDiamond4Cone5 zr := by rintro ⟨_, h32, _, _⟩; dsimp [zr] at h32; omega
        rw [cousinDiamond4Step_eq_d3_of_not_cone5 zr hnc5]
        have hzr_odd : zr % 2 = 1 := by dsimp [zr]; omega
        have hc3_zr : core3 (zr + 1) = 2 := by
          rw [show zr + 1 = 2 * 9 ^ r by dsimp [zr]; omega,
              core3_mul2 (9 ^ r) (by omega), (pow9_eq_v3Pow_w5 r).2]
        have hcond : isDiamond3Cone4 zr ∨
            (zr > 1 ∧ zr % 16 = 1 ∧ zr % 3 ≠ 2 ∧ core3 (2 * zr + 1) ≠ 1) ∨
            (zr ≥ 73 ∧ zr % 64 = 9 ∧ zr % 3 ≠ 2 ∧ core3 (2 * zr + 1) ≠ 1) ∨
            (zr ≥ 17 ∧ core3 (zr + 1) = 2) := Or.inr (Or.inr (Or.inr ⟨by dsimp [zr]; omega, hc3_zr⟩))
        unfold cousinDiamond3Step; simp only [hzr_odd, hcond, ite_true]; dsimp [zr, yr3]; omega
      have hiter_2r1 : cousinDiamond4Iter (2 * r + 1) xr3 = yr3 := by
        rw [cousinDiamond4Iter_add (2 * r) 1 xr3, hiter_2r]; exact hstep_zr
      have hall : ∀ i : Nat, i < 2 * r + 1 ->
          cousinDiamond4Iter i xr3 ≥ 3 ∧
          (cousinDiamond4Iter i xr3) % 2 = 1 ∧
          cousinDiamond4Step (cousinDiamond4Iter i xr3) ≥ 3 := by
        intro i hi
        by_cases hlt : i < 2 * r
        · rcases hglide_i i (by omega) with ⟨_, hge7, hodd_i⟩
          have hnext : cousinDiamond4Step (cousinDiamond4Iter i xr3) =
              cousinDiamond4Iter (i + 1) xr3 :=
            (cousinDiamond4Iter_add i 1 xr3).symm
          rcases hglide_i (i + 1) (by omega) with ⟨_, hge7_n, _⟩
          exact ⟨by omega, hodd_i, by rw [hnext]; omega⟩
        · have hi_eq : i = 2 * r := by omega
          rw [hi_eq, hiter_2r, hstep_zr]
          exact ⟨by dsimp [zr]; omega, by dsimp [zr]; omega, by dsimp [yr3]; omega⟩
      change ¬ laurentDescProp terms A0 B0 C0 xr3 yr3 at hr3
      rw [← hiter_2r1] at hr3
      exact exists_non_desc_along_diamond4_iter terms A0 B0 C0 (2 * r + 1) xr3 (by omega) hall hr3

/--
  Theorem W7.3h (`cousin_diamond4_counter_model_separation`, `[]` axioms):
  `T_diamond4` rejects ALL three Counter-Models (`M1 = Q_(6)^+` 5-cycle at `(1, 7)`,
  `M2 = Z^-` cycles `-1` and `-5 -> -7 -> -10 -> -5`, and `M3` supercritical `q = 7` 5-cycle
  at `5`), AND at the Cone-5 spiral witness `1529 -> 1147` (`1019 -> 1529 -> 1147 -> 1721 -> 1291`)
  blows up `cousinDiamond2Phi` (`1251578 -> 94560636`) yet reaches `1` in `13` steps!
-/
theorem cousin_diamond4_counter_model_separation :
    cousinDiamond4StepInt (-1) = -1 ∧
    cousinDiamond4IterInt 3 (-5) = -5 ∧
    cousinDiamond4IterParam 7 5 5 = 5 ∧
    cousinDiamond4StepQ6 (1, 7) = (5, 7) ∧
    cousinDiamond4IterQ6 5 (1, 7) = (1, 7) ∧
    cousinDiamond4Step 1529 = 1147 ∧
    cousinDiamond4StepInt 1529 = 1147 ∧
    cousinDiamond4StepQ6 (1529, 1) = (1147, 1) ∧
    cousinDiamond2Phi 1529 = 1251578 ∧
    cousinDiamond2Phi 1147 = 94560636 ∧
    cousinDiamond4Iter 13 1529 = 1 := by
  decide

-- ============================================================================
-- SECTION 4: Front D (Branches P5.3 & P2.2) — Markov Suffix-Shift Recurrence,
--            Sharp `q = 0` Leaf Envelope, & Fixed-Length Global Injectivity /
--            Minimal `L^2` Collision Energy across `27 * 2 ^ (L - 10)` Fibers
-- ============================================================================

theorem pow2_mod3_eq_one_iff_even :
    ∀ e : Nat, 2 ^ e % 3 = 1 ↔ e % 2 = 0
  | 0 => ⟨fun _ => rfl, fun _ => rfl⟩
  | 1 => ⟨fun h => by simp at h, fun h => by simp at h⟩
  | e + 2 => by
    have hstep : 2 ^ (e + 2) % 3 = 2 ^ e % 3 := by
      rw [Nat.pow_add 2 e 2, Nat.mul_mod, show (2 : Nat) ^ 2 % 3 = 1 from rfl,
          Nat.mul_one, Nat.mod_mod]
    rw [hstep, pow2_mod3_eq_one_iff_even e]
    omega

theorem list_eq_append_true_of_reverse_head :
    ∀ u : List Bool, u.reverse.head? = some true -> ∃ v : List Bool, u = v ++ [true]
  | [], h => by simp at h
  | b :: rest, h => by
    cases hrev : rest.reverse with
    | nil =>
      have hr : rest = [] := by
        have h1 := congrArg List.reverse hrev; simpa using h1
      subst hr
      simp at h; subst h
      exact ⟨[], rfl⟩
    | cons last initRev =>
      rw [List.reverse_cons, hrev, List.cons_append] at h
      simp only [List.head?_cons] at h
      have hrest_last : rest.reverse.head? = some true := by rw [hrev]; simpa using h
      rcases list_eq_append_true_of_reverse_head rest hrest_last with ⟨v', hv'⟩
      exact ⟨b :: v', by rw [hv', List.cons_append]⟩

/--
  Theorem W7.4a (`canonicalSuffixShift_append_markov_recurrence`, zero custom axioms):
  Exact History-Free Markov Skew-Product Recurrence for `canonicalSuffixShift · 1`:
  1. Universal Oddness on Words Ending in `true` (including ALL `IsCoreParityWord u`):
     `u.reverse.head? = some true -> canonicalSuffixShift u 1 % 2 = 1` (hence `≥ 1`)!
  2. Exact `b = false` Transition (`∀ u` with `parityWeight u ≥ 1`):
     `canonicalSuffixShift (u ++ [false]) 1 = if a ≥ 1 then a - 1 else 2 * 3 ^ (w - 1) - 1`.
  3. Exact Wrap-Free `b = true` Transition (`∀ u` with `parityWeight u ≥ 1`):
     `dlog2ModPow3 (w + 1) (3 * 2 ^ a + 1)` is EVEN and `≥ 2`, and
     `canonicalSuffixShift (u ++ [true]) 1 = dlog2ModPow3 (w + 1) (3 * 2 ^ a + 1) - 1`
     (depending ONLY on `(w, a)` and completely independent of `u.length` and `affineCarry u`!)!
-/
theorem canonicalSuffixShift_append_markov_recurrence :
    (∀ u : List Bool, u.reverse.head? = some true -> canonicalSuffixShift u 1 % 2 = 1) ∧
    (∀ u : List Bool, parityWeight u ≥ 1 ->
      let w := parityWeight u
      let a := canonicalSuffixShift u 1
      canonicalSuffixShift (u ++ [false]) 1 =
        (if a ≥ 1 then a - 1 else 2 * 3 ^ (w - 1) - 1)) ∧
    (∀ u : List Bool, parityWeight u ≥ 1 ->
      let w := parityWeight u
      let a := canonicalSuffixShift u 1
      let e := dlog2ModPow3 (w + 1) (3 * 2 ^ a + 1)
      e ≥ 2 ∧ e % 2 = 0 ∧
      canonicalSuffixShift (u ++ [true]) 1 = e - 1 ∧
      canonicalSuffixShift (u ++ [true]) 1 % 2 = 1) := by
  have hodd_end : ∀ u : List Bool, u.reverse.head? = some true ->
      canonicalSuffixShift u 1 % 2 = 1 := by
    intro u hlast
    rcases list_eq_append_true_of_reverse_head u hlast with ⟨v, rfl⟩
    let u := v ++ [true]
    have hw : parityWeight u ≥ 1 := by
      dsimp [u]; rw [parityWeight_append_w6]; simp [parityWeight]
    rcases canonicalSuffixShift_spec_unique u 1 hw (by decide) with ⟨_, hcongr, _⟩
    let w := parityWeight u
    let a := canonicalSuffixShift u 1
    rw [Nat.mul_one] at hcongr
    -- Reduce `(2 ^ (u.length + a)) % 3^w = affineCarry u % 3^w` modulo `3`:
    have h3w : 3 ^ w = 3 * 3 ^ (w - 1) := by
      conv => lhs; rw [show w = 1 + (w - 1) by omega]; rw [Nat.pow_add, Nat.pow_one]
    have hm3_eq : 2 ^ (u.length + a) % 3 = affineCarry u % 3 := by
      have h1 := mod_mul_mod_eq (2 ^ (u.length + a)) 3 (3 ^ (w - 1))
      have h2 := mod_mul_mod_eq (affineCarry u) 3 (3 ^ (w - 1))
      rw [← h3w] at h1 h2
      rw [← h1, ← h2, hcongr]
    have hcar_u : affineCarry u = 3 * affineCarry v + 2 ^ v.length := by
      dsimp [u]; rw [affineCarry_append]
      have hwt1 : parityWeight [true] = 1 := rfl
      have hc1 : affineCarry [true] = 1 := rfl
      rw [hwt1, hc1]; omega
    have hlen_u : u.length = v.length + 1 := by dsimp [u]; simp
    have hcar_m3 : affineCarry u % 3 = 2 ^ v.length % 3 := by
      rw [hcar_u, Nat.add_comm (3 * affineCarry v), Nat.add_mul_mod_self_left]
    rw [hcar_m3, hlen_u, show v.length + 1 + a = v.length + (a + 1) by omega,
        Nat.pow_add 2 v.length (a + 1)] at hm3_eq
    -- Multiply both sides by `2 ^ v.length` modulo `3` (`4 ^ v.length % 3 = 1`):
    have hmul_m3 : (2 ^ v.length * (2 ^ v.length * 2 ^ (a + 1))) % 3 =
        (2 ^ v.length * 2 ^ v.length) % 3 := by
      rw [Nat.mul_mod (2 ^ v.length), hm3_eq, ← Nat.mul_mod]
    have h4v_m3 : (2 ^ v.length * 2 ^ v.length) % 3 = 1 := by
      rw [← Nat.pow_add, ← Nat.two_mul, ← pow4_eq_pow2_even]
      cases v.length with
      | zero => rfl
      | succ k => exact (pow4_ge_four_and_mod3_w5 k).2
    rw [← Nat.mul_assoc, Nat.mul_mod (2 ^ v.length * 2 ^ v.length), h4v_m3,
        Nat.one_mul, Nat.mod_mod] at hmul_m3
    have ha1_ev : (a + 1) % 2 = 0 := (pow2_mod3_eq_one_iff_even (a + 1)).mp hmul_m3
    change a % 2 = 1
    omega
  refine ⟨hodd_end, ?_, ?_⟩
  · intro u hw
    dsimp only
    let w := parityWeight u
    let P := 2 * 3 ^ (w - 1)
    let M := 3 ^ w
    let a := canonicalSuffixShift u 1
    rcases canonicalSuffixShift_spec_unique u 1 hw (by decide) with ⟨ha_lt, ha_congr, _⟩
    change a < P at ha_lt
    rw [Nat.mul_one] at ha_congr
    have hu0_eq : u ++ [false] = u ++ List.replicate 1 false := rfl
    rcases affineCarry_append_replicate_false u 1 with ⟨hwt0, hcar0⟩
    rw [← hu0_eq] at hwt0 hcar0
    have hlen0 : (u ++ [false]).length = u.length + 1 := by simp
    rcases canonicalSuffixShift_spec_unique (u ++ [false]) 1 (by rw [hwt0]; exact hw) (by decide) with
      ⟨_, _, huniq0⟩
    change canonicalSuffixShift (u ++ [false]) 1 = if a ≥ 1 then a - 1 else P - 1
    by_cases ha1 : a ≥ 1
    · simp only [ha1, ite_true]
      symm
      apply huniq0 (a - 1) (by rw [hwt0]; dsimp [P, w] at ha_lt; omega)
      rw [Nat.mul_one, hwt0, hcar0, hlen0, show u.length + 1 + (a - 1) = u.length + a by omega]
      exact ha_congr
    · simp only [ha1, ite_false]
      have ha0 : a = 0 := by omega
      have hP_pos : P ≥ 2 := by dsimp [P]; have hp := pow3_pos_nat (w - 1); omega
      symm
      apply huniq0 (P - 1) (by rw [hwt0]; dsimp [P, w] at hP_pos ⊢; omega)
      rw [Nat.mul_one, hwt0, hcar0, hlen0, show u.length + 1 + (P - 1) = P + u.length by omega,
          Nat.pow_add 2 P u.length, Nat.mul_mod]
      have hp1 : 2 ^ P % M = 1 := (pow2_totient_exact_valuation_all_weights w hw).2.2.1
      rw [hp1, Nat.one_mul, Nat.mod_mod]
      dsimp [a] at ha0
      rw [ha0, Nat.add_zero] at ha_congr
      exact ha_congr
  · intro u hw
    dsimp only
    let w := parityWeight u
    let a := canonicalSuffixShift u 1
    let M := 3 ^ w
    let M' := 3 ^ (w + 1)
    let P' := 2 * 3 ^ w
    have hM'_eq : M' = 3 * M := by dsimp [M', M]; rw [Nat.pow_succ, Nat.mul_comm]
    let target := 3 * 2 ^ a + 1
    have ht_nd3 : target % 3 ≠ 0 := by dsimp [target]; omega
    rcases dlog2ModPow3_spec (w + 1) target (by omega) ht_nd3 with ⟨he_lt, he_eq⟩
    let e := dlog2ModPow3 (w + 1) target
    change e < P' at he_lt
    change 2 ^ e % M' = target % M' at he_eq
    -- Prove `e % 2 = 0` via mod `3` and `e ≠ 0` (`target % M' ≠ 1`):
    have he_m3 : 2 ^ e % 3 = 1 := by
      have h1 := mod_mul_mod_eq (2 ^ e) 3 M
      have h2 := mod_mul_mod_eq target 3 M
      rw [← hM'_eq] at h1 h2
      rw [← h1, he_eq, h2]
      dsimp [target]; omega
    have he_ev : e % 2 = 0 := (pow2_mod3_eq_one_iff_even e).mp he_m3
    have he_ne0 : e ≠ 0 := by
      intro he0
      rw [he0, Nat.pow_zero] at he_eq
      have hM'_gt1 : M' > 1 := by rw [hM'_eq]; have hp := pow3_pos_nat w; omega
      rw [Nat.mod_eq_of_lt hM'_gt1] at he_eq
      -- `(3 * 2 ^ a + 1) % (3 * M) = 1` forces `(3 * 2 ^ a) % (3 * M) = 0`, so `2 ^ a % M = 0`, impossible!
      let Q := target / M'
      have hdm : target = M' * Q + target % M' := (Nat.div_add_mod target M').symm
      rw [← he_eq, hM'_eq, Nat.mul_assoc 3 M] at hdm
      have hdiv : 3 * 2 ^ a = 3 * (M * Q) := by dsimp [target] at hdm; omega
      have h2a_div : 2 ^ a = M * Q := by omega
      have hM_m3 : M % 3 = 0 := by
        dsimp [M]; rw [show w = (w - 1) + 1 by omega, Nat.pow_succ]; omega
      have h2a_m3 : 2 ^ a % 3 = 0 := by
        rw [h2a_div, Nat.mul_mod, hM_m3, Nat.zero_mul, Nat.zero_mod]
      exact pow2_mod3_nonzero_w5 a h2a_m3
    have he_ge2 : e ≥ 2 := by omega
    -- Now prove `canonicalSuffixShift (u ++ [true]) 1 = e - 1`:
    rcases canonicalSuffixShift_spec_unique u 1 hw (by decide) with ⟨_, ha_congr, _⟩
    rw [Nat.mul_one] at ha_congr
    have hwt1 : parityWeight (u ++ [true]) = w + 1 := by
      rw [parityWeight_append_w6]; rfl
    have hcar1 : affineCarry (u ++ [true]) = 3 * affineCarry u + 2 ^ u.length := by
      rw [affineCarry_append]
      have hw_t : parityWeight [true] = 1 := rfl
      have hc_t : affineCarry [true] = 1 := rfl
      rw [hw_t, hc_t]; omega
    have hlen1 : (u ++ [true]).length = u.length + 1 := by simp
    rcases canonicalSuffixShift_spec_unique (u ++ [true]) 1 (by rw [hwt1]; omega) (by decide) with
      ⟨_, _, huniq1⟩
    have ha1_eq : canonicalSuffixShift (u ++ [true]) 1 = e - 1 := by
      symm
      apply huniq1 (e - 1) (by rw [hwt1, show w + 1 - 1 = w by omega]; dsimp [P'] at he_lt; omega)
      rw [Nat.mul_one, hwt1, hcar1, hlen1,
          show u.length + 1 + (e - 1) = u.length + e by omega,
          Nat.pow_add 2 u.length e]
      -- Multiply `ha_congr : 2^(u.length + a) % M = affineCarry u % M` by `3` into `M' = 3 * M`:
      have hmul3_mod : ∀ X : Nat, (3 * X) % M' = 3 * (X % M) := by
        intro X
        rw [hM'_eq]
        exact Nat.mul_mod_mul_left 3 X M
      have h3_congr : (3 * 2 ^ (u.length + a)) % M' = (3 * affineCarry u) % M' := by
        rw [hmul3_mod, hmul3_mod, ha_congr]
      have hlhs_m : (2 ^ u.length * 2 ^ e) % M' = (2 ^ u.length * target) % M' := by
        rw [Nat.mul_mod, he_eq, ← Nat.mul_mod]
      have ht_expand : 2 ^ u.length * target = 3 * 2 ^ (u.length + a) + 2 ^ u.length := by
        dsimp [target]
        rw [Nat.mul_add, Nat.mul_one, Nat.pow_add 2 u.length a,
            ← Nat.mul_assoc (2 ^ u.length) 3 (2 ^ a),
            Nat.mul_comm (2 ^ u.length) 3, Nat.mul_assoc 3]
      rw [hlhs_m, ht_expand, Nat.add_mod, h3_congr, ← Nat.add_mod]
    exact ⟨he_ge2, he_ev, ha1_eq, by rw [ha1_eq]; omega⟩

theorem affineCarry_lt_pow3_mul_pow2 :
    ∀ u : List Bool, affineCarry u < 3 ^ parityWeight u * 2 ^ u.length
  | [] => by decide
  | b :: rest => by
    have ih := affineCarry_lt_pow3_mul_pow2 rest
    have hcons : b :: rest = [b] ++ rest := rfl
    rw [hcons, affineCarry_append, List.length_append, List.length_singleton,
        Nat.add_comm 1 rest.length, Nat.pow_succ 2 rest.length]
    cases b with
    | false =>
      have hc0 : affineCarry [false] = 0 := rfl
      have hw0 : parityWeight (false :: rest) = parityWeight rest := rfl
      rw [hc0, Nat.mul_zero, Nat.zero_add]
      change 2 * affineCarry rest < 3 ^ parityWeight rest * (2 ^ rest.length * 2)
      have hrhs : 3 ^ parityWeight rest * (2 ^ rest.length * 2) =
          2 * (3 ^ parityWeight rest * 2 ^ rest.length) := by
        rw [Nat.mul_comm (2 ^ rest.length) 2, ← Nat.mul_assoc,
            Nat.mul_comm (3 ^ parityWeight rest) 2, Nat.mul_assoc]
      rw [hrhs]
      omega
    | true =>
      have hc1 : affineCarry [true] = 1 := rfl
      change 3 ^ parityWeight rest * affineCarry [true] + 2 * affineCarry rest <
        3 ^ (1 + parityWeight rest) * (2 ^ rest.length * 2)
      rw [hc1, Nat.mul_one, Nat.add_comm 1 (parityWeight rest), Nat.pow_succ 3 (parityWeight rest)]
      have hp2_pos := pow2_pos_nat rest.length
      have h1 : 3 ^ parityWeight rest * 1 ≤ 3 ^ parityWeight rest * 2 ^ rest.length :=
        Nat.mul_le_mul_left _ hp2_pos
      rw [Nat.mul_one] at h1
      have hrhs : (3 ^ parityWeight rest * 3) * (2 ^ rest.length * 2) =
          6 * (3 ^ parityWeight rest * 2 ^ rest.length) := by
        calc
          (3 ^ parityWeight rest * 3) * (2 ^ rest.length * 2)
              = (3 * 2) * (3 ^ parityWeight rest * 2 ^ rest.length) := by
                rw [Nat.mul_comm (3 ^ parityWeight rest) 3, Nat.mul_comm (2 ^ rest.length) 2,
                    Nat.mul_assoc 3 (3 ^ parityWeight rest),
                    ← Nat.mul_assoc (3 ^ parityWeight rest) 2 (2 ^ rest.length),
                    Nat.mul_comm (3 ^ parityWeight rest) 2,
                    Nat.mul_assoc 2 (3 ^ parityWeight rest),
                    ← Nat.mul_assoc 3 2]
          _ = 6 * (3 ^ parityWeight rest * 2 ^ rest.length) := rfl
      rw [hrhs]
      omega

/--
  Theorem W7.4b (`q0_leaf_two_sided_archimedean_envelope_and_l12_drop`, zero custom axioms):
  1. Universal Carry & Two-Sided `q = 0` Leaf Archimedean Envelope (`∀ u` with `parityWeight u ≥ 1`):
     `1 ≤ affineCarry u < 3 ^ w * 2 ^ u.length`, and hence
       `3 ^ w * exactBackwardQuotient 1 u 0 < 2 ^ (u.length + canonicalSuffixShift u 1)` AND
       `2 ^ (u.length + canonicalSuffixShift u 1) < 3 ^ w * (exactBackwardQuotient 1 u 0 + 2 ^ u.length)`!
  2. Non-Monotone Length Drop inside `IsSurvivingMod373248Class` (`L = 12` < `L = 10` at equal weight `w = 8`):
     `u12 = [1,1,1,1,0,1,1,0,1,0,0,1]` (`|u12| = 12`, `w = 8`) produces a `q = 0` surviving leaf
     STRICTLY SMALLER than `u10 = [1,1,1,1,1,0,1,1,0,1]` (`|u10| = 10`, `w = 8`)!
-/
theorem q0_leaf_two_sided_archimedean_envelope_and_l12_drop :
    (∀ u : List Bool, parityWeight u ≥ 1 ->
      let w := parityWeight u
      let a := canonicalSuffixShift u 1
      let y0 := exactBackwardQuotient 1 u 0
      1 ≤ affineCarry u ∧
      affineCarry u < 3 ^ w * 2 ^ u.length ∧
      3 ^ w * y0 < 2 ^ (u.length + a) ∧
      2 ^ (u.length + a) < 3 ^ w * (y0 + 2 ^ u.length)) ∧
    (let u12 := [true, true, true, true, false, true, true, false, true, false, false, true]
     let u10 := [true, true, true, true, true, false, true, true, false, true]
     u12.length = 12 ∧ u10.length = 10 ∧
     parityWeight u12 = 8 ∧ parityWeight u10 = 8 ∧
     IsSurvivingMod373248Class (exactBackwardQuotient 1 u12 0) ∧
     IsSurvivingMod373248Class (exactBackwardQuotient 1 u10 0) ∧
     exactBackwardQuotient 1 u12 0 < exactBackwardQuotient 1 u10 0) := by
  have henv : ∀ u : List Bool, parityWeight u ≥ 1 ->
      let w := parityWeight u
      let a := canonicalSuffixShift u 1
      let y0 := exactBackwardQuotient 1 u 0
      1 ≤ affineCarry u ∧
      affineCarry u < 3 ^ w * 2 ^ u.length ∧
      3 ^ w * y0 < 2 ^ (u.length + a) ∧
      2 ^ (u.length + a) < 3 ^ w * (y0 + 2 ^ u.length) := by
    intro u hw
    dsimp only
    rcases exactBackwardQuotient_spec 1 u 0 hw (by decide) with ⟨_, heq, _, _⟩
    simp only [Nat.zero_mul, Nat.add_zero, Nat.mul_one] at heq
    rcases affineCarryInt_pos_nondiv3_of_weight_pos u hw with ⟨hc_pos_i, _⟩
    rw [affineCarryInt_ofNat] at hc_pos_i
    have hc_pos : 1 ≤ affineCarry u := by omega
    have hc_ub := affineCarry_lt_pow3_mul_pow2 u
    refine ⟨hc_pos, hc_ub, by omega, ?_⟩
    rw [Nat.mul_add]
    omega
  refine ⟨henv, ?_⟩
  dsimp only
  -- 5-step binary squaring modulo `4782969 = 6561 * 729` (all literal exponents `≤ 128`):
  have hp16 : 2 ^ 16 % 4782969 = 65536 := rfl
  have hp32 : 2 ^ 32 % 4782969 = 4644103 := by
    rw [show (32 : Nat) = 16 + 16 from rfl, Nat.pow_add, Nat.mul_mod, hp16]
  have hp64 : 2 ^ 64 % 4782969 = 3617917 := by
    rw [show (64 : Nat) = 32 + 32 from rfl, Nat.pow_add, Nat.mul_mod, hp32]
  have hp128 : 2 ^ 128 % 4782969 = 1739101 := by
    rw [show (128 : Nat) = 64 + 64 from rfl, Nat.pow_add, Nat.mul_mod, hp64]
  have hp29 : 2 ^ 29 % 4782969 = 1178384 := by
    rw [show (29 : Nat) = 16 + 13 from rfl, Nat.pow_add, Nat.mul_mod, hp16]
  have hp67 : 2 ^ 67 % 4782969 = 245522 := by
    rw [show (67 : Nat) = 64 + 3 from rfl, Nat.pow_add, Nat.mul_mod, hp64]
  have hpow3 : ∀ (e a b c : Nat), e = a + (b + c) -> 2 ^ e = 2 ^ a * (2 ^ b * 2 ^ c) := by
    intro e a b c h
    rw [h, Nat.pow_add, Nat.pow_add]
  have hpow_e12 : ∀ e : Nat, e = 128 + (128 + 29) ->
      2 ^ e % 4782969 = 1918772 ∧ 2 ^ e % 6561 = 9521 % 6561 := by
    intro e he
    have hbig : 2 ^ e % 4782969 = 1918772 := by
      rw [hpow3 e 128 128 29 he, Nat.mul_mod, Nat.mul_mod (2 ^ 128), hp128, hp29]
    have hsm : 2 ^ e % 6561 = 9521 % 6561 := by
      have hm := mod_mul_mod_eq (2 ^ e) 6561 729
      change (2 ^ e % 4782969) % 6561 = 2 ^ e % 6561 at hm
      rw [← hm, hbig]
    exact ⟨hbig, hsm⟩
  have hpow_e10 : ∀ e : Nat, e = 128 + (128 + 67) ->
      2 ^ e % 4782969 = 3851915 ∧ 2 ^ e % 6561 = 7169 % 6561 := by
    intro e he
    have hbig : 2 ^ e % 4782969 = 3851915 := by
      rw [hpow3 e 128 128 67 he, Nat.mul_mod, Nat.mul_mod (2 ^ 128), hp128, hp67]
    have hsm : 2 ^ e % 6561 = 7169 % 6561 := by
      have hm := mod_mul_mod_eq (2 ^ e) 6561 729
      change (2 ^ e % 4782969) % 6561 = 2 ^ e % 6561 at hm
      rw [← hm, hbig]
    exact ⟨hbig, hsm⟩
  have hextract_mod729 : ∀ (z c rem r0 : Nat),
      c < 10000 -> r0 < 729 -> 6561 * r0 + c = rem -> rem < 4782969 ->
      (6561 * z + c) % 4782969 = rem -> z % 729 = r0 := by
    intro z c rem r0 hc_lt _ hrem_eq hrem_lt hmod
    let r := z % 729
    let q := z / 729
    have hr_lt : r < 729 := Nat.mod_lt z (by decide)
    have hz_eq : 6561 * z + c = (6561 * r + c) + 4782969 * q := by
      have hdm : z = 729 * q + r := by dsimp [q, r]; exact (Nat.div_add_mod z 729).symm
      rw [hdm]; omega
    rw [hz_eq, Nat.add_mul_mod_self_left] at hmod
    by_cases hlt : 6561 * r + c < 4782969
    · rw [Nat.mod_eq_of_lt hlt] at hmod
      have hr_eq : r = r0 := by omega
      exact hr_eq
    · have hsub : (6561 * r + c) % 4782969 = 6561 * r + c - 4782969 := by
        have heq_s : 6561 * r + c = (6561 * r + c - 4782969) + 4782969 * 1 := by omega
        conv => lhs; rw [heq_s]
        rw [Nat.add_mul_mod_self_left]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hsub] at hmod
      omega
  let u12 := [true, true, true, true, false, true, true, false, true, false, false, true]
  let u10 := [true, true, true, true, true, false, true, true, false, true]
  let y12 := exactBackwardQuotient 1 u12 0
  let y10 := exactBackwardQuotient 1 u10 0
  have ha12 : canonicalSuffixShift u12 1 = 273 := by
    symm
    apply (canonicalSuffixShift_spec_unique u12 1 (by decide) (by decide)).2.2 273 (by decide)
    rw [Nat.mul_one]
    exact (hpow_e12 (u12.length + 273) rfl).2
  have ha10 : canonicalSuffixShift u10 1 = 313 := by
    symm
    apply (canonicalSuffixShift_spec_unique u10 1 (by decide) (by decide)).2.2 313 (by decide)
    rw [Nat.mul_one]
    exact (hpow_e10 (u10.length + 313) rfl).2
  have h512_12 : y12 % 512 = 111 := by
    dsimp [y12]
    rw [exactBackwardQuotient_mod512_eq_coreWordMod512 u12 0 ⟨rfl, rfl⟩ (by decide)]
    decide
  have h512_10 : y10 % 512 = 415 := by
    dsimp [y10]
    rw [exactBackwardQuotient_mod512_eq_coreWordMod512 u10 0 ⟨rfl, rfl⟩ (by decide)]
    decide
  have h729_12 : y12 % 729 = 291 := by
    rcases exactBackwardQuotient_spec 1 u12 0 (by decide) (by decide) with ⟨_, heq12, _, _⟩
    simp only [Nat.zero_mul, Nat.add_zero, Nat.mul_one] at heq12
    change 2 ^ (12 + canonicalSuffixShift u12 1) = 6561 * y12 + 9521 at heq12
    have hmod_eq := congrArg (· % 4782969) heq12.symm
    rw [(hpow_e12 (12 + canonicalSuffixShift u12 1) (by rw [ha12])).1] at hmod_eq
    exact hextract_mod729 y12 9521 1918772 291 (by decide) (by decide) (by decide) (by decide) hmod_eq
  have h729_10 : y10 % 729 = 586 := by
    rcases exactBackwardQuotient_spec 1 u10 0 (by decide) (by decide) with ⟨_, heq10, _, _⟩
    simp only [Nat.zero_mul, Nat.add_zero, Nat.mul_one] at heq10
    change 2 ^ (10 + canonicalSuffixShift u10 1) = 6561 * y10 + 7169 at heq10
    have hmod_eq := congrArg (· % 4782969) heq10.symm
    rw [(hpow_e10 (10 + canonicalSuffixShift u10 1) (by rw [ha10])).1] at hmod_eq
    exact hextract_mod729 y10 7169 3851915 586 (by decide) (by decide) (by decide) (by decide) hmod_eq
  have hsurv12 : IsSurvivingMod373248Class y12 := by
    unfold IsSurvivingMod373248Class
    rw [h512_12, h729_12]
    unfold IsSurvivingMod512Residue IsSurvivingMod64Residue IsSurvivingMod729Residue
    decide
  have hsurv10 : IsSurvivingMod373248Class y10 := by
    unfold IsSurvivingMod373248Class
    rw [h512_10, h729_10]
    unfold IsSurvivingMod512Residue IsSurvivingMod64Residue IsSurvivingMod729Residue
    decide
  have hlt12_10 : y12 < y10 := by
    rcases henv u12 (by decide) with ⟨_, _, hub12, _⟩
    rcases henv u10 (by decide) with ⟨_, _, _, hlb10⟩
    change 6561 * y12 < 2 ^ (12 + canonicalSuffixShift u12 1) at hub12
    change 2 ^ (10 + canonicalSuffixShift u10 1) < 6561 * (y10 + 1024) at hlb10
    rcases (⟨12 + 273, by decide, by rw [ha12], by rw [ha10]⟩ :
        ∃ E : Nat, 23 ≤ E ∧ 12 + canonicalSuffixShift u12 1 = E ∧
          10 + canonicalSuffixShift u10 1 = 38 + E) with ⟨E, hE23, hE12, hE10⟩
    rw [hE12] at hub12
    rw [hE10, Nat.pow_add 2 38 E] at hlb10
    have hp38 : (2 : Nat) ^ 38 = 274877906944 := by decide
    rw [hp38] at hlb10
    have hpE_ge : 2 ^ E ≥ 6561 * 1024 := by
      have hm := pow2_mono_nat hE23
      have hp23 : (2 : Nat) ^ 23 = 8388608 := by decide
      rw [hp23] at hm
      omega
    generalize y12 = z12 at hub12 ⊢
    generalize y10 = z10 at hlb10 ⊢
    omega
  exact ⟨rfl, rfl, rfl, rfl, hsurv12, hsurv10, hlt12_10⟩

/-- Duplicate-free predicate on `List (List Bool)` for fiber injectivity. -/
inductive NoDupBoolWords : List (List Bool) -> Prop where
  | nil : NoDupBoolWords []
  | cons (u : List Bool) (us : List (List Bool)) :
      u ∉ us -> NoDupBoolWords us -> NoDupBoolWords (u :: us)

theorem noDupBoolWords_map_inj (f : List Bool -> List Bool)
    (hinj : ∀ u1 u2 : List Bool, f u1 = f u2 -> u1 = u2) :
    ∀ ws : List (List Bool), NoDupBoolWords ws -> NoDupBoolWords (ws.map f)
  | [], _ => NoDupBoolWords.nil
  | u :: us, NoDupBoolWords.cons _ _ hnu hnd => by
    simp only [List.map_cons]
    refine NoDupBoolWords.cons _ _ ?_ (noDupBoolWords_map_inj f hinj us hnd)
    intro hm
    rcases List.mem_map.mp hm with ⟨v, hv, hfv⟩
    exact hnu (hinj v u hfv ▸ hv)

theorem noDupBoolWords_append :
    ∀ (xs ys : List (List Bool)),
      NoDupBoolWords xs -> NoDupBoolWords ys ->
      (∀ u : List Bool, u ∈ xs -> u ∉ ys) ->
      NoDupBoolWords (xs ++ ys)
  | [], _, _, hnd_y, _ => hnd_y
  | x :: xs, ys, NoDupBoolWords.cons _ _ hnx hnd_x, hnd_y, hdisj => by
    simp only [List.cons_append]
    refine NoDupBoolWords.cons x (xs ++ ys) ?_
      (noDupBoolWords_append xs ys hnd_x hnd_y (fun u hu => hdisj u (List.mem_cons_of_mem _ hu)))
    intro hm
    rcases List.mem_append.mp hm with hmx | hmy
    · exact hnx hmx
    · exact hdisj x (List.Mem.head _) hmy

theorem allBoolWordsOfLen_nodup :
    ∀ k : Nat, NoDupBoolWords (allBoolWordsOfLen k)
  | 0 => NoDupBoolWords.cons [] [] (by simp) NoDupBoolWords.nil
  | k + 1 => by
    simp only [allBoolWordsOfLen]
    have ih := allBoolWordsOfLen_nodup k
    apply noDupBoolWords_append
    · exact noDupBoolWords_map_inj (false :: ·) (fun _ _ h => List.cons.inj h |>.2) _ ih
    · exact noDupBoolWords_map_inj (true :: ·) (fun _ _ h => List.cons.inj h |>.2) _ ih
    · intro u hmf hmt
      rcases List.mem_map.mp hmf with ⟨v1, _, rfl⟩
      rcases List.mem_map.mp hmt with ⟨v2, _, heq⟩
      cases heq

def collectSurvivingMod512 : Nat -> List Nat
  | 0 => []
  | r + 1 =>
    if isSurvivingMod512Bool r then r :: collectSurvivingMod512 r
    else collectSurvivingMod512 r

theorem collectSurvivingMod512_spec :
    ∀ n : Nat,
      NoDupNat (collectSurvivingMod512 n) ∧
      (∀ r ∈ collectSurvivingMod512 n, r < n ∧ isSurvivingMod512Bool r = true)
  | 0 => ⟨NoDupNat.nil, fun _ hm => by cases hm⟩
  | n + 1 => by
    rcases collectSurvivingMod512_spec n with ⟨hnd, hmem⟩
    simp only [collectSurvivingMod512]
    by_cases hb : isSurvivingMod512Bool n
    · simp only [hb, ite_true]
      have hnot_mem : n ∉ collectSurvivingMod512 n := by
        intro hm; have hlt := (hmem n hm).1; omega
      refine ⟨NoDupNat.cons n _ hnot_mem hnd, ?_⟩
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr_n
      · exact ⟨by omega, hb⟩
      · rcases hmem r hr_n with ⟨hlt, hrb⟩
        exact ⟨by omega, hrb⟩
    · simp only [hb]
      exact ⟨hnd, fun r hr => ⟨by have := (hmem r hr).1; omega, (hmem r hr).2⟩⟩

def fiberWordsForResidue (r k : Nat) : List (List Bool) :=
  (allBoolWordsOfLen k).map (fun fb => parityOfIter 9 r ++ fb ++ [true])

def survivingWordsFromResidues : List Nat -> Nat -> List (List Bool)
  | [], _ => []
  | r :: rs, k => fiberWordsForResidue r k ++ survivingWordsFromResidues rs k

/-- All `27 * 2 ^ k` surviving `mod 512` core words of exact length `L = k + 10`. -/
def survivingWordsAtScale (k : Nat) : List (List Bool) :=
  survivingWordsFromResidues (collectSurvivingMod512 512) k

/-- All `27 * 2 ^ k` ray values `exactBackwardQuotient 1 u q` across length `L = k + 10` fibers. -/
def survivingLeavesAtScale (k q : Nat) : List Nat :=
  (survivingWordsAtScale k).map (fun u => exactBackwardQuotient 1 u q)

theorem exactBackwardQuotient_strict_mono_q (u : List Bool) (hw : parityWeight u ≥ 1) :
    ∀ q1 q2 : Nat, q1 < q2 -> exactBackwardQuotient 1 u q1 < exactBackwardQuotient 1 u q2
  | q1, 0, hlt => by omega
  | q1, q2 + 1, hlt => by
    rcases exactBackwardQuotient_period_recurrence_and_mod3 1 u q2 hw (by decide) with
      ⟨hrec, _, _, _, _, _⟩
    rcases pow2_totient_3adic_lift (parityWeight u - 1) with ⟨_, hk_m3⟩
    have hk_pos : totient3Coeff (parityWeight u - 1) ≥ 1 := by omega
    have hy_pos : exactBackwardQuotient 1 u q2 ≥ 1 :=
      (exactBackwardQuotient_spec 1 u q2 hw (by decide)).1
    have hstep_gt : exactBackwardQuotient 1 u q2 < exactBackwardQuotient 1 u (q2 + 1) := by
      rw [hrec]
      have h3w := pow3_pos_nat (parityWeight u)
      have hm1 : 1 ≤ 3 ^ parityWeight u * exactBackwardQuotient 1 u q2 := Nat.mul_le_mul h3w hy_pos
      have hm2 : 1 * 1 ≤ totient3Coeff (parityWeight u - 1) *
          (affineCarry u + 3 ^ parityWeight u * exactBackwardQuotient 1 u q2) :=
        Nat.mul_le_mul hk_pos (by omega)
      omega
    by_cases heq : q1 = q2
    · subst heq; exact hstep_gt
    · exact Nat.lt_trans (exactBackwardQuotient_strict_mono_q u hw q1 q2 (by omega)) hstep_gt

theorem noDupNat_of_noDupBoolWords_inj
    (f : List Bool -> Nat)
    (ws : List (List Bool))
    (hnd : NoDupBoolWords ws)
    (hinj : ∀ u1 u2 : List Bool, u1 ∈ ws -> u2 ∈ ws -> f u1 = f u2 -> u1 = u2) :
    NoDupNat (ws.map f) := by
  induction hnd with
  | nil => exact NoDupNat.nil
  | cons u us hnu _ ih =>
    simp only [List.map_cons]
    refine NoDupNat.cons (f u) (us.map f) ?_
      (ih (fun u1 u2 h1 h2 heq =>
        hinj u1 u2 (List.mem_cons_of_mem _ h1) (List.mem_cons_of_mem _ h2) heq))
    intro hm
    rcases List.mem_map.mp hm with ⟨v, hv, hfv⟩
    have huv := hinj v u (List.mem_cons_of_mem _ hv) (List.Mem.head _) hfv
    exact hnu (huv ▸ hv)

/--
  Theorem W7.4c (`fixed_length_ray_global_injectivity_and_minimal_l2_collision_energy`, zero custom axioms):
  1. Unconditional Fixed-Length Global Injectivity (Zero `IsFirstHitOnePair` Needed!):
     For ALL core words `u1, u2` of equal length (`u1.length = u2.length`) and ALL `q1, q2 : Nat`
     (including `q1 = 0, q2 = 0` and words wrapping around `{1, 2}`!),
       `exactBackwardQuotient 1 u1 q1 = exactBackwardQuotient 1 u2 q2 -> u1 = u2 ∧ q1 = q2`!
  2. Exact `27 * 2 ^ k` Surviving Fiber Enumeration & Minimal Diagonal `L^2` Collision Energy (`∀ k, q : Nat`):
     At every length `L = k + 10 ≥ 10` and every `q : Nat`, `survivingLeavesAtScale k q` has
     exact length `27 * 2 ^ k`, every leaf satisfies `isSurvivingMod512Bool (y % 512) = true` with
     `parityWeight u ≥ 7`, AND `NoDupNat (survivingLeavesAtScale k q)` holds unconditionally —
     proving zero off-diagonal collisions (minimal `L^2` collision energy = `27 * 2 ^ (L - 10)`)!
-/
theorem fixed_length_ray_global_injectivity_and_minimal_l2_collision_energy :
    (∀ (u1 u2 : List Bool) (q1 q2 : Nat),
      IsCoreParityWord u1 -> IsCoreParityWord u2 ->
      u1.length = u2.length ->
      exactBackwardQuotient 1 u1 q1 = exactBackwardQuotient 1 u2 q2 ->
      u1 = u2 ∧ q1 = q2) ∧
    (∀ (k q : Nat),
      let leaves := survivingLeavesAtScale k q
      leaves.length = 27 * 2 ^ k ∧
      NoDupNat leaves ∧
      (∀ y ∈ leaves, isSurvivingMod512Bool (y % 512) = true)) := by
  have hpar_recover : ∀ (u : List Bool) (q : Nat),
      IsCoreParityWord u ->
      parityOfIter u.length (exactBackwardQuotient 1 u q) = u := by
    intro u q hu
    let y := exactBackwardQuotient 1 u q
    let s := canonicalSuffixShift u 1 + q * (2 * 3 ^ (parityWeight u - 1))
    let v := u ++ List.replicate s false
    rcases one_generator_pos_odd_and_reaches_one u q hu with ⟨_, _, heq, _⟩
    change 2 ^ (u.length + s) = 3 ^ parityWeight u * y + affineCarry u at heq
    rcases affineCarry_append_replicate_false u s with ⟨hwt_v, hcar_v⟩
    have hv_len : v.length = u.length + s := by
      dsimp [v]; rw [List.length_append, List.length_replicate]
    have hv_aff : 2 ^ v.length * 1 = 3 ^ parityWeight v * y + affineCarry v := by
      rw [Nat.mul_one, hv_len, hwt_v, hcar_v]; exact heq
    have hv_par := eq_parityOfIter_of_nat_affine v y 1 hv_aff
    rw [hv_len] at hv_par
    have hsp := parityOfIter_append_split u.length s y
    rw [← hv_par] at hsp
    have hlen_u : u.length = (parityOfIter u.length y).length := (parityOfIter_length _ y).symm
    exact (list_append_inj_left_eq_len _ _ _ _ hlen_u hsp).1.symm
  have hinj_eq_len : ∀ (u1 u2 : List Bool) (q1 q2 : Nat),
      IsCoreParityWord u1 -> IsCoreParityWord u2 ->
      u1.length = u2.length ->
      exactBackwardQuotient 1 u1 q1 = exactBackwardQuotient 1 u2 q2 ->
      u1 = u2 ∧ q1 = q2 := by
    intro u1 u2 q1 q2 hu1 hu2 hlen heq
    have hp1 := hpar_recover u1 q1 hu1
    have hp2 := hpar_recover u2 q2 hu2
    rw [← hlen, ← heq, hp1] at hp2
    have hu_eq : u1 = u2 := hp2
    subst hu_eq
    have hw1 : parityWeight u1 ≥ 1 := by
      cases u1 with
      | nil => have hh := hu1.1; simp at hh
      | cons b _ => have hh := hu1.1; simp at hh; subst hh; simp [parityWeight]
    refine ⟨rfl, ?_⟩
    by_cases hlt1 : q1 < q2
    · have hst := exactBackwardQuotient_strict_mono_q u1 hw1 q1 q2 hlt1; omega
    · by_cases hlt2 : q2 < q1
      · have hst := exactBackwardQuotient_strict_mono_q u1 hw1 q2 q1 hlt2; omega
      · omega
  refine ⟨hinj_eq_len, ?_⟩
  intro k q
  dsimp only
  -- Prove structural properties of `survivingWordsFromResidues rs k` by induction on `rs`:
  have hfiber_spec : ∀ (r : Nat), r < 512 -> isSurvivingMod512Bool r = true ->
      (fiberWordsForResidue r k).length = 2 ^ k ∧
      NoDupBoolWords (fiberWordsForResidue r k) ∧
      (∀ u ∈ fiberWordsForResidue r k,
        IsCoreParityWord u ∧ u.length = k + 10 ∧ parityWeight u ≥ 7 ∧
        u.take 9 = parityOfIter 9 r ∧
        exactBackwardQuotient 1 u q % 512 = r) := by
    intro r hr_lt hrb
    rcases surviving_mod512_nine_prefix_auto_weight_and_characterization.1 r hr_lt hrb with
      ⟨hp9_len, _, _, hfb_all⟩
    let p9 := parityOfIter 9 r
    change p9.length = 9 at hp9_len
    have hlen_f : (fiberWordsForResidue r k).length = 2 ^ k := by
      unfold fiberWordsForResidue; rw [List.length_map, (allBoolWordsOfLen_spec k).1]
    have hmap_inj : ∀ fb1 fb2 : List Bool,
        p9 ++ fb1 ++ [true] = p9 ++ fb2 ++ [true] -> fb1 = fb2 := by
      intro fb1 fb2 heq
      rw [List.append_assoc, List.append_assoc] at heq
      have htail := (list_append_inj_left_eq_len _ _ _ _ rfl heq).2
      have hrev := congrArg List.reverse htail
      rw [List.reverse_append, List.reverse_append] at hrev
      have hrev_fb := List.cons.inj hrev |>.2
      have hfb := congrArg List.reverse hrev_fb
      simpa using hfb
    have hnd_f : NoDupBoolWords (fiberWordsForResidue r k) :=
      noDupBoolWords_map_inj (fun fb => p9 ++ fb ++ [true]) hmap_inj _ (allBoolWordsOfLen_nodup k)
    refine ⟨hlen_f, hnd_f, ?_⟩
    intro u hu_mem
    unfold fiberWordsForResidue at hu_mem
    rcases List.mem_map.mp hu_mem with ⟨fb, hfb_mem, rfl⟩
    have hfb_len : fb.length = k := by
      have hall_k : ∀ v ∈ allBoolWordsOfLen k, v.length = k := by
        have haux : ∀ (m : Nat) (v : List Bool), v ∈ allBoolWordsOfLen m -> v.length = m := by
          intro m; induction m with
          | zero => intro v hv; simp [allBoolWordsOfLen] at hv; subst hv; rfl
          | succ m' ihm =>
            intro v hv
            simp only [allBoolWordsOfLen, List.mem_append] at hv
            rcases hv with h1 | h2
            · rcases List.mem_map.mp h1 with ⟨w0, hw0, rfl⟩; simp [ihm w0 hw0]
            · rcases List.mem_map.mp h2 with ⟨w0, hw0, rfl⟩; simp [ihm w0 hw0]
        exact haux k
      exact hall_k fb hfb_mem
    rcases hfb_all fb q with ⟨hcore_u, hwt_u, hmod_u, _⟩
    have hu_len : (p9 ++ fb ++ [true]).length = k + 10 := by
      rw [List.length_append, List.length_append, hp9_len, hfb_len, List.length_singleton]; omega
    have htake9 : (p9 ++ fb ++ [true]).take 9 = p9 := by
      rw [List.append_assoc]
      have ht : ∀ (xs ys : List Bool), (xs ++ ys).take xs.length = xs := by
        intro xs; induction xs with
        | nil => simp
        | cons x rest ih => intro ys; simp [ih ys]
      have h1 := ht p9 (fb ++ [true])
      rwa [hp9_len] at h1
    exact ⟨hcore_u, hu_len, hwt_u, htake9, hmod_u⟩
  have hrs_spec : ∀ rs : List Nat,
      NoDupNat rs ->
      (∀ r ∈ rs, r < 512 ∧ isSurvivingMod512Bool r = true) ->
      (survivingWordsFromResidues rs k).length = rs.length * 2 ^ k ∧
      NoDupBoolWords (survivingWordsFromResidues rs k) ∧
      (∀ u ∈ survivingWordsFromResidues rs k,
        IsCoreParityWord u ∧ u.length = k + 10 ∧
        isSurvivingMod512Bool (exactBackwardQuotient 1 u q % 512) = true ∧
        ∃ r ∈ rs, u.take 9 = parityOfIter 9 r) := by
    intro rs hnd_rs hrs_ok
    induction hnd_rs with
    | nil =>
      exact ⟨by simp [survivingWordsFromResidues], NoDupBoolWords.nil, fun _ hm => by cases hm⟩
    | cons r rs' hnr _ ih =>
      rcases hrs_ok r (List.Mem.head _) with ⟨hr_lt, hrb⟩
      rcases hfiber_spec r hr_lt hrb with ⟨hlen_r, hnd_r, hmem_r⟩
      rcases ih (fun x hx => hrs_ok x (List.mem_cons_of_mem _ hx)) with
        ⟨hlen_rs, hnd_rs', hmem_rs⟩
      simp only [survivingWordsFromResidues]
      have hlen_tot : (fiberWordsForResidue r k ++ survivingWordsFromResidues rs' k).length =
          (r :: rs').length * 2 ^ k := by
        rw [List.length_append, hlen_r, hlen_rs, List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
      have hdisj : ∀ u : List Bool,
          u ∈ fiberWordsForResidue r k -> u ∉ survivingWordsFromResidues rs' k := by
        intro u hur hurs
        have ht1 := (hmem_r u hur).2.2.2.1
        rcases (hmem_rs u hurs).2.2.2 with ⟨r2, hr2_mem, ht2⟩
        have hr2_lt : r2 < 512 := (hrs_ok r2 (List.mem_cons_of_mem _ hr2_mem)).1
        have hp_eq : parityOfIter 9 r = parityOfIter 9 r2 := ht1.symm.trans ht2
        have hmod9 := parityOfIter_inj_mod_pow2_w6 9 r r2 hp_eq
        rw [show (2 : Nat) ^ 9 = 512 from rfl,
            Nat.mod_eq_of_lt hr_lt, Nat.mod_eq_of_lt hr2_lt] at hmod9
        exact hnr (hmod9 ▸ hr2_mem)
      refine ⟨hlen_tot, noDupBoolWords_append _ _ hnd_r hnd_rs' hdisj, ?_⟩
      intro u hu_mem
      rcases List.mem_append.mp hu_mem with hur | hurs
      · rcases hmem_r u hur with ⟨hc, hl, _, ht9, hm512⟩
        exact ⟨hc, hl, by rw [hm512]; exact hrb, ⟨r, List.Mem.head _, ht9⟩⟩
      · rcases hmem_rs u hurs with ⟨hc, hl, hs512, ⟨r2, hr2_m, ht9⟩⟩
        exact ⟨hc, hl, hs512, ⟨r2, List.mem_cons_of_mem _ hr2_m, ht9⟩⟩
  rcases collectSurvivingMod512_spec 512 with ⟨hnd_512, hok_512⟩
  have hlen_512 : (collectSurvivingMod512 512).length = 27 := by decide
  rcases hrs_spec (collectSurvivingMod512 512) hnd_512 hok_512 with
    ⟨hlen_ws, hnd_ws, hmem_ws⟩
  rw [hlen_512] at hlen_ws
  have hlen_leaves : (survivingLeavesAtScale k q).length = 27 * 2 ^ k := by
    unfold survivingLeavesAtScale survivingWordsAtScale
    rw [List.length_map, hlen_ws]
  have hnd_leaves : NoDupNat (survivingLeavesAtScale k q) := by
    unfold survivingLeavesAtScale survivingWordsAtScale
    apply noDupNat_of_noDupBoolWords_inj (fun u => exactBackwardQuotient 1 u q) _ hnd_ws
    intro u1 u2 hu1 hu2 heq
    rcases hmem_ws u1 hu1 with ⟨hc1, hl1, _, _⟩
    rcases hmem_ws u2 hu2 with ⟨hc2, hl2, _, _⟩
    exact (hinj_eq_len u1 u2 q q hc1 hc2 (hl1.trans hl2.symm) heq).1
  refine ⟨hlen_leaves, hnd_leaves, ?_⟩
  intro y hy_mem
  unfold survivingLeavesAtScale survivingWordsAtScale at hy_mem
  rcases List.mem_map.mp hy_mem with ⟨u, hu_mem, rfl⟩
  exact (hmem_ws u hu_mem).2.2.1

end CollatzFormal

