/-
  CollatzFormal/Wave15WholeSpaceCore.lean
  Wave 15 Whole-Space Mathematical & CS Proof Loop (Core — Fronts A & B):
  1. Front A — All-Dimension (`∀ d ≥ 1`) Active-Interior Top-Left Unit Lock
     (`(M_s)_{0,0} = 1` across all `21` active interior symbols of `c39` and all `42` active interior
     symbols of `c78`) vs `.R` Boundary Top-Left Growth (`(M_6)_{0,0} = (M_9)_{0,0} = k ≥ 2`),
     All-Dimension (`∀ d ≥ 1`) Non-Uniform Mixed Zero-Diagonal Binary-Top / Ternary-Subrow
     `ω^k` Matrix-Tower Collapse on `c39` & `c78` (with 24-Strict-Rule Non-Triangular `d = 2` Witness),
     Infinite 2-Parameter `.T`-Coupled `d = 2` Parameterized Farkas Syzygy Lock (`paramMat2DC39 α β`),
     & Unconditional `1..10`-Cycle Freedom + 2-Block `.R`-Carrying `leftAnchoredDP2Step`
     Cycle Locks (`W15_H1`, Branch P4.3)
  2. Front B — Unified Arbitrary-`U` `(U * T) × (U * T)` All-Block Confluent Laurent Divisibility
     (`confluentFactorAllU U T u ∣ intDet (U * T) M0` for `∀ U ≥ 2, ∀ T ≥ 1, ∀ u ≥ 1`), Quadratic
     `(2^u - 1)^((U*(U-1)/2)*T^2)` & Pairwise-Block `(2^((b - a)*u) - 1)^(T^2)` Divisibility,
     Confluent-Reduced Majorant Bound, Unit-Grid Exactness, & Universal Factorial Dominance
     (`confluentFactorAllU U T u > (U * T)!` for `∀ U ≥ 4, ∀ T ≥ 1, ∀ u ≥ 1`),
     Rank-3 Two-Base `9 × 9` `(T = 3, U = 3)` Global `u = 1..9` Non-Vanishing, Cone-Free `∀ u ≥ 1`
     Non-Vanishing Outside `(27 * w', 8 * k')`, Explicit Multi-`u` Zero-Multiplicity Ceiling &
     Asymptotic Sign Lock, + `(7, 11)` Double Sign-Flip (`u = 3, 4, 5`), & General
     `∀ s ≥ 4` Newton–Hensel Mod-`2^s` 2-Adic Inverse-Residue Quotient Boost + 3-Pivot Cross-Block
     Brox Squeeze Eliminating Balanced `m = 4` `[(17, 2), (17, 2), (17, 2), (17, 34)]` (`W15_H2`,
     Branches P3.3 & P3.4)

  Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

import CollatzFormal.Wave14WholeSpace

namespace CollatzFormal

-- ============================================================================
-- SECTION 1: Front A (Branch P4.3) — Active-Interior Top-Left Unit Lock vs
--            Boundary Growth, Non-Uniform Mixed Zero-Diagonal BT Matrix Collapse,
--            2-Parameter `.T`-Coupled Farkas Syzygy, & `1..10`-Cycle / 2-Block
--            `leftAnchoredDP2Step` Laws (`W15_H1`)
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Section 1A: All-Dimension (`∀ d ≥ 1`) Active-Interior Top-Left Unit Lock vs
--             `.R` Boundary Top-Left Growth (`{6, 9}`) on `c39` & `c78`
-- ----------------------------------------------------------------------------

private def prodFinWordW15 (N : Nat) (m : Fin N -> Nat) : List (Fin N) -> Nat
  | [] => 1
  | s :: rest => m s * prodFinWordW15 N m rest

private theorem mul_pow_w15c (a b : Nat) : ∀ n : Nat, (a * b) ^ n = a ^ n * b ^ n
  | 0 => rfl
  | n + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, mul_pow_w15c a b n]
    ac_rfl

private theorem pow_mono_base_w15c (a b : Nat) (hle : a ≤ b) : ∀ n : Nat, a ^ n ≤ b ^ n
  | 0 => Nat.le_refl 1
  | n + 1 => Nat.mul_le_mul (pow_mono_base_w15c a b hle n) hle

private theorem prodFinWordW15_pos (N : Nat) (m : Fin N -> Nat) (hm : ∀ s : Fin N, m s ≥ 1) :
    ∀ w : List (Fin N), prodFinWordW15 N m w ≥ 1
  | [] => Nat.le_refl 1
  | s :: rest => Nat.mul_le_mul (hm s) (prodFinWordW15_pos N m hm rest)

private def weightedProdLhsW15 (N : Nat) (m : Fin N -> Nat) :
    List (List (Fin N) × List (Fin N)) -> List Nat -> Nat
  | [], _ => 1
  | _, [] => 1
  | r :: rs, u :: us => (prodFinWordW15 N m r.1) ^ u * weightedProdLhsW15 N m rs us

private def weightedProdRhsW15 (N : Nat) (m : Fin N -> Nat) :
    List (List (Fin N) × List (Fin N)) -> List Nat -> Nat
  | [], _ => 1
  | _, [] => 1
  | r :: rs, u :: us => (prodFinWordW15 N m r.2) ^ u * weightedProdRhsW15 N m rs us

private theorem prodFinWordW15_eq_sym_pow_prefix (N : Nat) (m : Fin N -> Nat) :
    ∀ w : List (Fin N),
      prodFinWordW15 N m w = colBoundProdPrefix N (fun s => (m s) ^ countFinOcc N s w) N
  | [] => by
    have hz : ∀ k : Nat, k ≤ N ->
        colBoundProdPrefix N (fun s => (m s) ^ countFinOcc N s []) k = 1 := by
      intro k hk; induction k with
      | zero => rfl
      | succ k' ih =>
        have hk'_lt : k' < N := hk
        simp only [colBoundProdPrefix, hk'_lt, dite_true]
        rw [ih (Nat.le_of_lt hk)]
        simp [countFinOcc]
    exact (hz N (Nat.le_refl N)).symm
  | s0 :: rest => by
    simp only [prodFinWordW15, prodFinWordW15_eq_sym_pow_prefix N m rest]
    have hstep : ∀ k : Nat, k ≤ N ->
        (if s0.val < k then m s0 else 1) *
          colBoundProdPrefix N (fun s => (m s) ^ countFinOcc N s rest) k =
        colBoundProdPrefix N (fun s => (m s) ^ countFinOcc N s (s0 :: rest)) k := by
      intro k hk; induction k with
      | zero => simp [colBoundProdPrefix]
      | succ k' ih =>
        have hk'_lt : k' < N := hk
        simp only [colBoundProdPrefix, hk'_lt, dite_true]
        have hih := ih (Nat.le_of_lt hk)
        by_cases hlt : s0.val < k'
        · have hlt1 : s0.val < k' + 1 := by omega
          rw [ite_true_of_w10 hlt1]
          rw [ite_true_of_w10 hlt] at hih
          have hne_v : s0.val ≠ k' := by omega
          have hocc : countFinOcc N ⟨k', hk'_lt⟩ (s0 :: rest) = countFinOcc N ⟨k', hk'_lt⟩ rest := by
            simp [countFinOcc, hne_v]
          rw [hocc, ← Nat.mul_assoc, hih]
        · by_cases heq : s0.val = k'
          · have hlt1 : s0.val < k' + 1 := by omega
            have hsf : (⟨k', hk'_lt⟩ : Fin N) = s0 := Fin.ext heq.symm
            rw [ite_true_of_w10 hlt1, hsf]
            rw [ite_false_of_w10 hlt, Nat.one_mul] at hih
            have hocc : countFinOcc N s0 (s0 :: rest) = countFinOcc N s0 rest + 1 := by
              simp [countFinOcc]; omega
            rw [hocc, Nat.pow_succ, ← hih]
            ac_rfl
          · have hgt1 : ¬ (s0.val < k' + 1) := by omega
            rw [ite_false_of_w10 hgt1, Nat.one_mul]
            rw [ite_false_of_w10 hlt, Nat.one_mul] at hih
            have hne_v : s0.val ≠ k' := by omega
            have hocc : countFinOcc N ⟨k', hk'_lt⟩ (s0 :: rest) = countFinOcc N ⟨k', hk'_lt⟩ rest := by
              simp [countFinOcc, hne_v]
            rw [hocc, hih]
    have hfin := hstep N (Nat.le_refl N)
    rwa [ite_true_of_w10 s0.isLt] at hfin

private theorem colBoundProdPrefix_pow_mul_w15 (N : Nat) (m : Fin N -> Nat)
    (f g : Fin N -> Nat) (u : Nat) :
    ∀ k : Nat, k ≤ N ->
      (colBoundProdPrefix N (fun s => (m s) ^ f s) k) ^ u *
        colBoundProdPrefix N (fun s => (m s) ^ g s) k =
      colBoundProdPrefix N (fun s => (m s) ^ (u * f s + g s)) k
  | 0, _ => by simp [colBoundProdPrefix]
  | k + 1, hk => by
    have hk_lt : k < N := hk
    simp only [colBoundProdPrefix, hk_lt, dite_true]
    rw [mul_pow_w15c _ _ u,
        pow_pow_eq_mul_w5 (m ⟨k, hk_lt⟩) (f ⟨k, hk_lt⟩) u,
        Nat.mul_comm (f ⟨k, hk_lt⟩) u]
    have ih := colBoundProdPrefix_pow_mul_w15 N m f g u k (Nat.le_of_lt hk)
    calc
      ((colBoundProdPrefix N (fun s => (m s) ^ f s) k) ^ u * (m ⟨k, hk_lt⟩) ^ (u * f ⟨k, hk_lt⟩)) *
          (colBoundProdPrefix N (fun s => (m s) ^ g s) k * (m ⟨k, hk_lt⟩) ^ g ⟨k, hk_lt⟩)
          = ((colBoundProdPrefix N (fun s => (m s) ^ f s) k) ^ u *
              colBoundProdPrefix N (fun s => (m s) ^ g s) k) *
            ((m ⟨k, hk_lt⟩) ^ (u * f ⟨k, hk_lt⟩) * (m ⟨k, hk_lt⟩) ^ g ⟨k, hk_lt⟩) := by ac_rfl
      _ = colBoundProdPrefix N (fun s => (m s) ^ (u * f s + g s)) k *
            (m ⟨k, hk_lt⟩) ^ (u * f ⟨k, hk_lt⟩ + g ⟨k, hk_lt⟩) := by
            rw [ih, ← Nat.pow_add]

private theorem weightedProd_eq_sym_pow_w15 (N : Nat) (m : Fin N -> Nat) :
    ∀ (rules : List (List (Fin N) × List (Fin N))) (mults : List Nat),
      weightedProdLhsW15 N m rules mults =
        colBoundProdPrefix N (fun s => (m s) ^ weightedSymLhsSum N s rules mults) N ∧
      weightedProdRhsW15 N m rules mults =
        colBoundProdPrefix N (fun s => (m s) ^ weightedSymRhsSum N s rules mults) N
  | [], _ => by
    have hz : ∀ k : Nat, k ≤ N -> colBoundProdPrefix N (fun _ => 1) k = 1 := by
      intro k hk; induction k with
      | zero => rfl
      | succ k' ih =>
        have hk'_lt : k' < N := hk
        simp only [colBoundProdPrefix, hk'_lt, dite_true]
        rw [ih (Nat.le_of_lt hk), Nat.mul_one]
    refine ⟨?_, ?_⟩ <;> simpa [weightedProdLhsW15, weightedProdRhsW15, weightedSymLhsSum, weightedSymRhsSum]
      using (hz N (Nat.le_refl N)).symm
  | _ :: _, [] => by
    have hz : ∀ k : Nat, k ≤ N -> colBoundProdPrefix N (fun _ => 1) k = 1 := by
      intro k hk; induction k with
      | zero => rfl
      | succ k' ih =>
        have hk'_lt : k' < N := hk
        simp only [colBoundProdPrefix, hk'_lt, dite_true]
        rw [ih (Nat.le_of_lt hk), Nat.mul_one]
    refine ⟨?_, ?_⟩ <;> simpa [weightedProdLhsW15, weightedProdRhsW15, weightedSymLhsSum, weightedSymRhsSum]
      using (hz N (Nat.le_refl N)).symm
  | r0 :: rs, u0 :: us => by
    rcases weightedProd_eq_sym_pow_w15 N m rs us with ⟨hl, hr⟩
    refine ⟨?_, ?_⟩
    · simp only [weightedProdLhsW15, hl, prodFinWordW15_eq_sym_pow_prefix N m r0.1]
      exact colBoundProdPrefix_pow_mul_w15 N m _ _ u0 N (Nat.le_refl N)
    · simp only [weightedProdRhsW15, hr, prodFinWordW15_eq_sym_pow_prefix N m r0.2]
      exact colBoundProdPrefix_pow_mul_w15 N m _ _ u0 N (Nat.le_refl N)

private theorem colBoundProdPrefix_mono_pos_w15 (N : Nat) (f g : Fin N -> Nat)
    (hpos : ∀ s : Fin N, f s ≥ 1) (hle : ∀ s : Fin N, f s ≤ g s) :
    ∀ k : Nat, k ≤ N ->
      colBoundProdPrefix N f k ≥ 1 ∧
      colBoundProdPrefix N f k ≤ colBoundProdPrefix N g k ∧
      (colBoundProdPrefix N f k = colBoundProdPrefix N g k ->
        ∀ (s : Fin N), s.val < k -> f s = g s)
  | 0, _ => ⟨Nat.le_refl 1, Nat.le_refl 1, fun _ _ hs => by omega⟩
  | k + 1, hk => by
    have hk_lt : k < N := hk
    rcases colBoundProdPrefix_mono_pos_w15 N f g hpos hle k (Nat.le_of_lt hk) with ⟨hp, hm, heq_imp⟩
    simp only [colBoundProdPrefix, hk_lt, dite_true]
    have hfk := hpos ⟨k, hk_lt⟩
    have hle_k := hle ⟨k, hk_lt⟩
    refine ⟨Nat.mul_le_mul hp hfk, Nat.mul_le_mul hm hle_k, ?_⟩
    intro hmul_eq s hs_lt
    have ha1_eq : colBoundProdPrefix N f k = colBoundProdPrefix N g k := by
      by_cases hne : colBoundProdPrefix N f k = colBoundProdPrefix N g k
      · exact hne
      · exfalso
        have hlt1 : colBoundProdPrefix N f k < colBoundProdPrefix N g k := by omega
        have hm1 : colBoundProdPrefix N f k * f ⟨k, hk_lt⟩ < colBoundProdPrefix N g k * f ⟨k, hk_lt⟩ :=
          Nat.mul_lt_mul_of_pos_right hlt1 (by omega)
        have hm2 : colBoundProdPrefix N g k * f ⟨k, hk_lt⟩ ≤ colBoundProdPrefix N g k * g ⟨k, hk_lt⟩ :=
          Nat.mul_le_mul_left _ hle_k
        omega
    have ha2_eq : f ⟨k, hk_lt⟩ = g ⟨k, hk_lt⟩ := by
      rw [← ha1_eq] at hmul_eq
      exact Nat.eq_of_mul_eq_mul_left (by omega) hmul_eq
    by_cases hsk : s.val = k
    · have hif : s = ⟨k, hk_lt⟩ := Fin.ext hsk
      rwa [hif]
    · exact heq_imp ha1_eq s (by omega)

private theorem syzygy_forces_prod_eq_cf_w15
    (N : Nat) (rules : List (List (Fin N) × List (Fin N))) (mults : List Nat)
    (hsyz : checkPositiveParikhSyzygyFastBool N rules mults = true) :
    ∀ m : Fin N -> Nat,
      (∀ s : Fin N, m s ≥ 1) ->
      (∀ r ∈ rules, prodFinWordW15 N m r.1 ≥ prodFinWordW15 N m r.2) ->
      ∀ r ∈ rules, prodFinWordW15 N m r.1 = prodFinWordW15 N m r.2 := by
  unfold checkPositiveParikhSyzygyFastBool at hsyz
  rcases bool_and_split hsyz with ⟨hb1, hpairs⟩
  rcases bool_and_split hb1 with ⟨hb2, hpos_m⟩
  rcases bool_and_split hb2 with ⟨_, hlen_eq⟩
  have hlen : rules.length = mults.length := of_decide_eq_true hlen_eq
  rcases accumSymCountsW11_spec N rules mults with ⟨hacc_len, hacc_get⟩
  have hsym_le : ∀ s : Fin N, weightedSymLhsSum N s rules mults ≤ weightedSymRhsSum N s rules mults := by
    intro s
    have hle := checkPairsLeBoolW11_sound _ hpairs s.val (by rw [hacc_len]; exact s.isLt)
    rwa [hacc_get s] at hle
  intro m hm1 hweak
  have hprod_ge : ∀ (rs : List (List (Fin N) × List (Fin N))) (us : List Nat),
      rs.length = us.length ->
      checkAllPosNatList us = true ->
      (∀ r ∈ rs, prodFinWordW15 N m r.1 ≥ prodFinWordW15 N m r.2) ->
      weightedProdRhsW15 N m rs us ≥ 1 ∧
      weightedProdLhsW15 N m rs us ≥ weightedProdRhsW15 N m rs us ∧
      (weightedProdLhsW15 N m rs us = weightedProdRhsW15 N m rs us ->
        ∀ r ∈ rs, prodFinWordW15 N m r.1 = prodFinWordW15 N m r.2) := by
    intro rs; induction rs with
    | nil =>
      intro _ _ _ _
      exact ⟨by simp [weightedProdRhsW15], by simp [weightedProdLhsW15, weightedProdRhsW15],
             fun _ _ hr => by cases hr⟩
    | cons r0 rt ih =>
      intro us hl hp hw
      cases us with
      | nil => simp at hl
      | cons u0 ut =>
        rcases bool_and_split hp with ⟨hu0_b, hut_p⟩
        have hu0 : u0 ≥ 1 := of_decide_eq_true hu0_b
        rcases ih ut (by simp at hl; omega) hut_p (fun r hr => hw r (List.mem_cons_of_mem r0 hr)) with
          ⟨hr_pos, hge_tl, heq_tl⟩
        simp only [weightedProdLhsW15, weightedProdRhsW15]
        have hp_r2 := prodFinWordW15_pos N m hm1 r0.2
        have hpu_pos := nat_pow_pos_of_pos (prodFinWordW15 N m r0.2) hp_r2 u0
        have hw0 := hw r0 List.mem_cons_self
        have hpu_ge := pow_mono_base_w15c (prodFinWordW15 N m r0.2) (prodFinWordW15 N m r0.1) hw0 u0
        refine ⟨Nat.mul_le_mul hpu_pos hr_pos, Nat.mul_le_mul hpu_ge hge_tl, ?_⟩
        intro heq_mul r hr_mem
        have h1_eq : (prodFinWordW15 N m r0.1) ^ u0 = (prodFinWordW15 N m r0.2) ^ u0 := by
          by_cases hne : (prodFinWordW15 N m r0.1) ^ u0 = (prodFinWordW15 N m r0.2) ^ u0
          · exact hne
          · exfalso
            have hlt : (prodFinWordW15 N m r0.2) ^ u0 < (prodFinWordW15 N m r0.1) ^ u0 := by omega
            have hm1_lt := Nat.mul_lt_mul_of_pos_right hlt
              (Nat.lt_of_lt_of_le Nat.zero_lt_one hr_pos)
            have hm2_le := Nat.mul_le_mul_left ((prodFinWordW15 N m r0.1) ^ u0) hge_tl
            exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hm1_lt hm2_le) heq_mul.symm
        have h2_eq : weightedProdLhsW15 N m rt ut = weightedProdRhsW15 N m rt ut := by
          rw [h1_eq] at heq_mul
          exact Nat.eq_of_mul_eq_mul_left (by omega) heq_mul
        cases hr_mem with
        | head =>
          by_cases hbase : prodFinWordW15 N m r0.1 = prodFinWordW15 N m r0.2
          · exact hbase
          · exfalso
            have hgt : prodFinWordW15 N m r0.2 < prodFinWordW15 N m r0.1 := by omega
            have hpow_lt : (prodFinWordW15 N m r0.2) ^ u0 < (prodFinWordW15 N m r0.1) ^ u0 := by
              rw [show u0 = (u0 - 1) + 1 by omega, Nat.pow_succ, Nat.pow_succ]
              have hm_b := pow_mono_base_w15c _ _ hw0 (u0 - 1)
              have hm_p := nat_pow_pos_of_pos _ hp_r2 (u0 - 1)
              have h1 := Nat.mul_le_mul_right (prodFinWordW15 N m r0.2) hm_b
              have h2 := Nat.mul_lt_mul_of_pos_left hgt
                (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_trans hm_p hm_b))
              exact Nat.lt_of_le_of_lt h1 h2
            omega
        | tail _ htl => exact heq_tl h2_eq r htl
  rcases hprod_ge rules mults hlen hpos_m hweak with ⟨_, _, htot_imp⟩
  rcases weightedProd_eq_sym_pow_w15 N m rules mults with ⟨hl_sym, hr_sym⟩
  have hsym_pow_le : ∀ s : Fin N,
      (m s) ^ weightedSymLhsSum N s rules mults ≤ (m s) ^ weightedSymRhsSum N s rules mults :=
    fun s => nat_pow_mono_exp_pos (m s) _ _ (hm1 s) (hsym_le s)
  have hsym_pow_pos : ∀ s : Fin N, (m s) ^ weightedSymLhsSum N s rules mults ≥ 1 :=
    fun s => nat_pow_pos_of_pos (m s) (hm1 s) _
  rcases colBoundProdPrefix_mono_pos_w15 N _ _ hsym_pow_pos hsym_pow_le N (Nat.le_refl N) with
    ⟨_, htot_le_sym, _⟩
  rw [← hl_sym, ← hr_sym] at htot_le_sym
  exact htot_imp (by omega)

private def accumAllOnesW15 (N : Nat) : List (List (Fin N) × List (Fin N)) -> List (Nat × Nat)
  | [] => List.replicate N (0, 0)
  | (l, r) :: rs =>
    addRuleToCountsW11 1 (l.map Fin.val) (r.map Fin.val) 0 (accumAllOnesW15 N rs)

private theorem accumAllOnesW15_eq (N : Nat) :
    ∀ rules : List (List (Fin N) × List (Fin N)),
      accumAllOnesW15 N rules = accumSymCountsW11 N rules (List.replicate rules.length 1)
  | [] => rfl
  | (l, r) :: rs => by
    simp only [accumAllOnesW15, List.length_cons, List.replicate_succ, accumSymCountsW11,
               accumAllOnesW15_eq N rs]

private theorem symAppears_imp_ones_sum_pos_w15 (N : Nat) (s : Fin N) :
    ∀ rules : List (List (Fin N) × List (Fin N)),
      symAppearsInRulesBool N s.val rules = true ->
      weightedSymLhsSum N s rules (List.replicate rules.length 1) +
        weightedSymRhsSum N s rules (List.replicate rules.length 1) ≥ 1
  | [], h => by simp [symAppearsInRulesBool] at h
  | (l, r) :: rs, h => by
    unfold symAppearsInRulesBool at h
    simp only [List.length_cons, List.replicate_succ, weightedSymLhsSum, weightedSymRhsSum,
               Nat.one_mul]
    cases hcur : decide (countNatOccW11 s.val (l.map Fin.val) + countNatOccW11 s.val (r.map Fin.val) ≥ 1) with
    | true =>
      have hc : countNatOccW11 s.val (l.map Fin.val) + countNatOccW11 s.val (r.map Fin.val) ≥ 1 :=
        of_decide_eq_true hcur
      rw [countNatOccW11_map_val N s l, countNatOccW11_map_val N s r] at hc
      omega
    | false =>
      rw [hcur, Bool.false_or] at h
      have ih := symAppears_imp_ones_sum_pos_w15 N s rs h
      omega

private def checkFastIntAnnPairsAuxW15 (M : Nat) :
    Nat -> List (Nat × Nat) -> List (Nat × Nat) -> List (Nat × Nat) -> Bool
  | _, [], _, _ => true
  | _, _, [], _ => true
  | _, _, _, [] => true
  | idx, p :: ps, n :: ns, o :: os =>
    let a := p.1 + n.2
    let b := p.2 + n.1
    decide (a ≤ b) &&
    (if idx ≥ 4 * M && decide (o.1 + o.2 ≥ 1) then decide (a < b) else true) &&
    checkFastIntAnnPairsAuxW15 M (idx + 1) ps ns os

private def checkFastIntAnnBoolW15 (M : Nat)
    (rules : List (List (Fin (14 * M)) × List (Fin (14 * M))))
    (posMults negMults : List Nat) : Bool :=
  checkFastIntAnnPairsAuxW15 M 0
    (accumSymCountsW11 (14 * M) rules posMults)
    (accumSymCountsW11 (14 * M) rules negMults)
    (accumAllOnesW15 (14 * M) rules)

private theorem signed_annihilation_forces_int_one_cf_w15 (M : Nat)
    (rules : List (List (Fin (14 * M)) × List (Fin (14 * M))))
    (posMults negMults : List Nat)
    (hann : checkFastIntAnnBoolW15 M rules posMults negMults = true) :
    ∀ m : Fin (14 * M) -> Nat,
      (∀ s : Fin (14 * M), m s ≥ 1) ->
      (∀ r ∈ rules, prodFinWordW15 (14 * M) m r.1 = prodFinWordW15 (14 * M) m r.2) ->
      ∀ s : Fin (14 * M), s.val ≥ 4 * M -> symAppearsInRulesBool (14 * M) s.val rules = true ->
        m s = 1 := by
  rcases accumSymCountsW11_spec (14 * M) rules posMults with ⟨hlen_p, hget_p⟩
  rcases accumSymCountsW11_spec (14 * M) rules negMults with ⟨hlen_n, hget_n⟩
  rcases accumSymCountsW11_spec (14 * M) rules (List.replicate rules.length 1) with ⟨hlen_o, hget_o⟩
  let A_cnt : Fin (14 * M) -> Nat := fun s =>
    weightedSymLhsSum (14 * M) s rules posMults + weightedSymRhsSum (14 * M) s rules negMults
  let B_cnt : Fin (14 * M) -> Nat := fun s =>
    weightedSymRhsSum (14 * M) s rules posMults + weightedSymLhsSum (14 * M) s rules negMults
  have haux_snd : ∀ (ps ns os : List (Nat × Nat)) (idx : Nat),
      ps.length = ns.length -> ps.length = os.length ->
      checkFastIntAnnPairsAuxW15 M idx ps ns os = true ->
      ∀ k : Nat, k < ps.length ->
        let p := getPairAtW11 ps k
        let n := getPairAtW11 ns k
        let o := getPairAtW11 os k
        p.1 + n.2 ≤ p.2 + n.1 ∧
        (idx + k ≥ 4 * M -> o.1 + o.2 ≥ 1 -> p.1 + n.2 < p.2 + n.1) := by
    intro ps; induction ps with
    | nil => intros _ _ _ _ _ _ _ hk; simp at hk
    | cons p0 pst ih =>
      intro ns os idx hlen1 hlen2 hb k hk
      cases ns with
      | nil => simp at hlen1
      | cons n0 nst =>
        cases os with
        | nil => simp at hlen2
        | cons o0 ost =>
          unfold checkFastIntAnnPairsAuxW15 at hb
          rcases bool_and_split hb with ⟨hb1, hrest⟩
          rcases bool_and_split hb1 with ⟨hle_b, hlt_b⟩
          cases k with
          | zero =>
            simp only [getPairAtW11, Nat.add_zero]
            refine ⟨of_decide_eq_true hle_b, fun hge4 hact => ?_⟩
            have hc : (decide (idx ≥ 4 * M) && decide (o0.1 + o0.2 ≥ 1)) = true := by
              rw [decide_eq_true hge4, decide_eq_true hact]; rfl
            rw [hc] at hlt_b; exact of_decide_eq_true hlt_b
          | succ k' =>
            have ihk := ih nst ost (idx + 1) (by simp at hlen1; omega) (by simp at hlen2; omega)
              hrest k' (by simp at hk; omega)
            simpa [getPairAtW11, show idx + 1 + k' = idx + (k' + 1) by omega] using ihk
  have hAB : ∀ s : Fin (14 * M),
      A_cnt s ≤ B_cnt s ∧
      (s.val ≥ 4 * M -> symAppearsInRulesBool (14 * M) s.val rules = true -> A_cnt s < B_cnt s) := by
    intro s
    unfold checkFastIntAnnBoolW15 at hann
    rw [accumAllOnesW15_eq] at hann
    have hsnd := haux_snd
      (accumSymCountsW11 (14 * M) rules posMults)
      (accumSymCountsW11 (14 * M) rules negMults)
      (accumSymCountsW11 (14 * M) rules (List.replicate rules.length 1)) 0
      (hlen_p.trans hlen_n.symm) (hlen_p.trans hlen_o.symm) hann s.val (by rw [hlen_p]; exact s.isLt)
    simp only [Nat.zero_add, hget_p s, hget_n s, hget_o s] at hsnd
    exact ⟨hsnd.1, fun hge hact => hsnd.2 hge (symAppears_imp_ones_sum_pos_w15 (14 * M) s rules hact)⟩
  have hw_eq : ∀ (m : Fin (14 * M) -> Nat)
      (rs : List (List (Fin (14 * M)) × List (Fin (14 * M)))) (us : List Nat),
      (∀ r ∈ rs, prodFinWordW15 (14 * M) m r.1 = prodFinWordW15 (14 * M) m r.2) ->
      weightedProdLhsW15 (14 * M) m rs us = weightedProdRhsW15 (14 * M) m rs us := by
    intro m rs; induction rs with
    | nil => intros; rfl
    | cons r0 rt ih =>
      intro us heq
      cases us with
      | nil => rfl
      | cons u0 ut =>
        simp only [weightedProdLhsW15, weightedProdRhsW15, heq r0 List.mem_cons_self,
                   ih ut (fun r hr => heq r (List.mem_cons_of_mem r0 hr))]
  intro m hm1 heq s hs_ge hs_act
  have hp_eq := hw_eq m rules posMults heq
  have hn_eq := hw_eq m rules negMults heq
  rcases weightedProd_eq_sym_pow_w15 (14 * M) m rules posMults with ⟨hl_p, hr_p⟩
  rcases weightedProd_eq_sym_pow_w15 (14 * M) m rules negMults with ⟨hl_n, hr_n⟩
  have hprod_mul : ∀ (f g : Fin (14 * M) -> Nat) (k : Nat), k ≤ 14 * M ->
      colBoundProdPrefix (14 * M) (fun x => (m x) ^ f x) k *
        colBoundProdPrefix (14 * M) (fun x => (m x) ^ g x) k =
      colBoundProdPrefix (14 * M) (fun x => (m x) ^ (f x + g x)) k := by
    intro f g k hk
    simpa using colBoundProdPrefix_pow_mul_w15 (14 * M) m f g 1 k hk
  have htot_eq : colBoundProdPrefix (14 * M) (fun x => (m x) ^ A_cnt x) (14 * M) =
      colBoundProdPrefix (14 * M) (fun x => (m x) ^ B_cnt x) (14 * M) := by
    rw [← hprod_mul _ _ (14 * M) (Nat.le_refl _), ← hprod_mul _ _ (14 * M) (Nat.le_refl _),
        ← hl_p, ← hr_p, ← hl_n, ← hr_n, hp_eq, hn_eq]
  rcases colBoundProdPrefix_mono_pos_w15 (14 * M)
    (fun x => (m x) ^ A_cnt x) (fun x => (m x) ^ B_cnt x)
    (fun x => nat_pow_pos_of_pos (m x) (hm1 x) _)
    (fun x => nat_pow_mono_exp_pos (m x) _ _ (hm1 x) (hAB x).1) (14 * M) (Nat.le_refl _) with
    ⟨_, _, heq_imp⟩
  have hpow_eq : (m s) ^ A_cnt s = (m s) ^ B_cnt s := heq_imp htot_eq s s.isLt
  have hlt_s := (hAB s).2 hs_ge hs_act
  by_cases hm_eq1 : m s = 1
  · exact hm_eq1
  · exfalso
    have hm_ge2 : m s ≥ 2 := by have := hm1 s; omega
    have hexp : B_cnt s = A_cnt s + (B_cnt s - A_cnt s) := by omega
    have hpow_rhs : (m s) ^ B_cnt s = (m s) ^ A_cnt s * (m s) ^ (B_cnt s - A_cnt s) := by
      calc (m s) ^ B_cnt s
          = (m s) ^ (A_cnt s + (B_cnt s - A_cnt s)) := congrArg ((m s) ^ ·) hexp
        _ = (m s) ^ A_cnt s * (m s) ^ (B_cnt s - A_cnt s) := Nat.pow_add _ _ _
    rw [hpow_rhs] at hpow_eq
    have hp_ge2 : (m s) ^ (B_cnt s - A_cnt s) ≥ 2 := by
      rw [show B_cnt s - A_cnt s = (B_cnt s - A_cnt s - 1) + 1 by omega, Nat.pow_succ]
      have hp1 := nat_pow_pos_of_pos (m s) (hm1 s) (B_cnt s - A_cnt s - 1)
      have hm2 := Nat.mul_le_mul hp1 hm_ge2
      omega
    have hp_pos := nat_pow_pos_of_pos (m s) (hm1 s) (A_cnt s)
    have hmul_gt : (m s) ^ A_cnt s * 1 < (m s) ^ A_cnt s * (m s) ^ (B_cnt s - A_cnt s) :=
      Nat.mul_lt_mul_of_pos_left (by omega) hp_pos
    rw [Nat.mul_one] at hmul_gt
    exact Nat.ne_of_lt hmul_gt hpow_eq

private def addNatListsW15 : List Nat -> List Nat -> List Nat
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => (x + y) :: addNatListsW15 xs ys

/-- Boundary-growth witness on `c39` setting `(M_6)_{0,0} = (M_9)_{0,0} = k` (`k ≥ 1`),
    `(M_s)_{0,0} = 1` elsewhere, and `0` on all other `2 × 2` entries. -/
def bndTopLeftMat2DC39 (k : Nat) (s : Fin 42) (i j : Fin 2) : Nat :=
  if i.val == 0 && j.val == 0 then
    if s.val == 6 || s.val == 9 then k else 1
  else 0

def countActiveIntPairsAux (M : Nat) : Nat -> List (Nat × Nat) -> Nat
  | _, [] => 0
  | idx, p :: ps =>
    (if idx ≥ 4 * M && decide (p.1 + p.2 > 0) then 1 else 0) + countActiveIntPairsAux M (idx + 1) ps

def countActiveIntSymsBool (M N : Nat) (rules : List (List (Fin N) × List (Fin N))) : Nat :=
  countActiveIntPairsAux M 0 (accumAllOnesW15 N rules)

private theorem evalFinWordMat_col0_or_row0_prod (N d : Nat) (hd : d ≥ 1)
    (mat : Fin N -> Fin d -> Fin d -> Nat) :
    let z0 : Fin d := ⟨0, hd⟩
    ((∀ (s : Fin N) (i : Fin d), i.val ≥ 1 -> mat s i z0 = 0) ->
      ∀ w : List (Fin N),
        evalFinWordMat N d mat w z0 z0 = prodFinWordW15 N (fun s => mat s z0 z0) w ∧
        (∀ i : Fin d, i.val ≥ 1 -> evalFinWordMat N d mat w i z0 = 0)) ∧
    ((∀ (s : Fin N) (j : Fin d), j.val ≥ 1 -> mat s z0 j = 0) ->
      ∀ (w : List (Fin N)) (j : Fin d),
        evalFinWordMat N d mat w z0 j =
          if j.val = 0 then prodFinWordW15 N (fun s => mat s z0 z0) w else 0) := by
  dsimp only
  let z0 : Fin d := ⟨0, hd⟩
  have hsum_single0 : ∀ (f : Fin d -> Nat), (∀ k : Fin d, k.val ≥ 1 -> f k = 0) ->
      natSumPrefix d f d = f z0 := by
    intro f hz
    have hst : ∀ m : Nat, m ≤ d -> natSumPrefix d f m = (if 0 < m then f z0 else 0) := by
      intro m hm; induction m with
      | zero => rfl
      | succ m' ih =>
        have hm_lt : m' < d := hm
        simp only [natSumPrefix, hm_lt, dite_true, ih (Nat.le_of_lt hm)]
        cases m' with
        | zero =>
          have h0f : (⟨0, hm_lt⟩ : Fin d) = z0 := rfl
          rw [h0f]; simp
        | succ m'' =>
          rw [hz ⟨m'' + 1, hm_lt⟩ (by dsimp; omega), Nat.add_zero]
          simp
    rw [hst d (Nat.le_refl d), ite_true_of_w10 (by omega : 0 < d)]
  have hsum_zero : ∀ (f : Fin d -> Nat), (∀ k : Fin d, f k = 0) ->
      natSumPrefix d f d = 0 := by
    intro f hz
    have hst : ∀ m : Nat, natSumPrefix d f m = 0 := by
      intro m; induction m with
      | zero => rfl
      | succ m' ih =>
        simp only [natSumPrefix]
        by_cases hm : m' < d <;> simp [hm, ih, hz]
    exact hst d
  refine ⟨?_, ?_⟩
  · intro hcol0 w; induction w with
    | nil =>
      refine ⟨by simp [evalFinWordMat, prodFinWordW15, natMatId], ?_⟩
      intro i hi
      have hne : i.val ≠ 0 := by omega
      simp [evalFinWordMat, natMatId, hne]
    | cons s rest ih =>
      rcases ih with ⟨ih0, ih_gt⟩
      refine ⟨?_, ?_⟩
      · change natSumPrefix d (fun k => mat s z0 k * evalFinWordMat N d mat rest k z0) d =
          mat s z0 z0 * prodFinWordW15 N (fun x => mat x z0 z0) rest
        rw [hsum_single0 _ (fun k hk => by rw [ih_gt k hk, Nat.mul_zero]), ih0]
      · intro i hi
        change natSumPrefix d (fun k => mat s i k * evalFinWordMat N d mat rest k z0) d = 0
        exact hsum_zero _ (fun k => by
          by_cases hk0 : k.val = 0
          · have hkf : k = z0 := Fin.ext hk0
            rw [hkf, hcol0 s i hi, Nat.zero_mul]
          · rw [ih_gt k (by omega), Nat.mul_zero])
  · intro hrow0 w; induction w with
    | nil =>
      intro j
      by_cases hj0 : j.val = 0
      · have hjf : j = z0 := Fin.ext hj0
        rw [ite_true_of_w10 hj0, hjf]
        simp [evalFinWordMat, prodFinWordW15, natMatId, z0]
      · rw [ite_false_of_w10 hj0]
        have hne : (0 : Nat) ≠ j.val := fun h => hj0 h.symm
        simp [evalFinWordMat, natMatId, hne]
    | cons s rest ih =>
      intro j
      change natSumPrefix d (fun k => mat s z0 k * evalFinWordMat N d mat rest k j) d = _
      rw [hsum_single0 _ (fun k hk => by rw [hrow0 s k hk, Nat.zero_mul]), ih j]
      by_cases hj0 : j.val = 0
      · rw [ite_true_of_w10 hj0, ite_true_of_w10 hj0, prodFinWordW15]
      · rw [ite_false_of_w10 hj0, ite_false_of_w10 hj0, Nat.mul_zero]

private def toFinWordW15 (N : Nat) (hN : N ≥ 1) : List Nat -> List (Fin N)
  | [] => []
  | x :: xs => (if h : x < N then ⟨x, h⟩ else ⟨0, hN⟩) :: toFinWordW15 N hN xs

private def toFinRulesW15 (N : Nat) (hN : N ≥ 1) :
    List (List Nat × List Nat) -> List (List (Fin N) × List (Fin N))
  | [] => []
  | (l, r) :: rs => (toFinWordW15 N hN l, toFinWordW15 N hN r) :: toFinRulesW15 N hN rs

private def c39FastRules : List (List (Fin 42) × List (Fin 42)) :=
  toFinRulesW15 42 (by decide)
    [([1, 14], [2]), ([2, 13], [1]), ([4, 14], [5]), ([5, 13], [4]),
     ([2, 20], [2, 38]), ([1, 18], [2, 36]), ([5, 20], [5, 38]), ([4, 18], [5, 36]),
     ([29, 20], [22, 35]), ([28, 18], [22, 33]), ([31, 14], [18, 29]), ([32, 13], [18, 28]),
     ([35, 16], [21, 28]), ([32, 20], [14, 38]), ([31, 18], [14, 36]), ([35, 23], [17, 38]),
     ([33, 22], [17, 37]), ([37, 17], [13, 32]), ([38, 16], [13, 31]), ([40, 17], [16, 32]),
     ([41, 16], [16, 31]), ([38, 23], [20, 41]), ([36, 22], [20, 40]), ([37, 21], [20, 39]),
     ([41, 23], [23, 41]), ([39, 22], [23, 40]), ([40, 21], [23, 39]), ([28, 8], [22, 11]),
     ([28, 7], [22, 10]), ([28, 6], [22, 9]), ([31, 8], [14, 13, 8]), ([31, 7], [14, 13, 7]),
     ([31, 6], [14, 13, 6]), ([37, 11], [20, 16, 8]), ([37, 10], [20, 16, 7]), ([37, 9], [20, 16, 6]),
     ([40, 11], [23, 16, 8]), ([40, 10], [23, 16, 7]), ([40, 9], [23, 16, 6])]

private def c78FastRules : List (List (Fin 84) × List (Fin 84)) :=
  toFinRulesW15 84 (by decide)
    [([4, 29], [5]), ([2, 28], [4]), ([4, 26], [2]), ([2, 25], [1]),
     ([10, 29], [11]), ([8, 28], [10]), ([10, 26], [8]), ([8, 25], [7]),
     ([5, 41], [5, 77]), ([1, 39], [5, 75]), ([5, 38], [2, 74]), ([1, 36], [2, 72]),
     ([11, 41], [11, 77]), ([7, 39], [11, 75]), ([11, 38], [8, 74]), ([7, 36], [8, 72]),
     ([59, 41], [46, 71]), ([55, 39], [46, 69]), ([59, 38], [43, 68]), ([55, 36], [43, 66]),
     ([64, 29], [39, 59]), ([62, 28], [36, 58]), ([64, 26], [36, 56]), ([62, 25], [39, 55]),
     ([68, 34], [42, 58]), ([68, 31], [45, 55]), ([65, 41], [29, 77]), ([61, 39], [29, 75]),
     ([65, 38], [26, 74]), ([61, 36], [26, 72]), ([71, 47], [35, 77]), ([69, 46], [32, 76]),
     ([71, 44], [32, 74]), ([69, 43], [35, 73]), ([76, 35], [28, 65]), ([74, 34], [25, 64]),
     ([76, 32], [25, 62]), ([74, 31], [28, 61]), ([82, 35], [34, 65]), ([80, 34], [31, 64]),
     ([82, 32], [31, 62]), ([80, 31], [34, 61]), ([77, 47], [41, 83]), ([75, 46], [38, 82]),
     ([73, 45], [41, 81]), ([77, 44], [38, 80]), ([75, 43], [41, 79]), ([73, 42], [38, 78]),
     ([83, 47], [47, 83]), ([81, 46], [44, 82]), ([79, 45], [47, 81]), ([83, 44], [44, 80]),
     ([81, 43], [47, 79]), ([79, 42], [44, 78]), ([55, 17], [43, 23]), ([55, 16], [43, 22]),
     ([55, 15], [43, 21]), ([55, 14], [43, 20]), ([55, 13], [43, 19]), ([55, 12], [43, 18]),
     ([61, 17], [26, 25, 17]), ([61, 16], [26, 25, 16]), ([61, 15], [26, 25, 15]),
     ([61, 14], [26, 25, 14]), ([61, 13], [26, 25, 13]), ([61, 12], [26, 25, 12]),
     ([73, 23], [38, 31, 17]), ([73, 22], [38, 31, 16]), ([73, 21], [38, 31, 15]),
     ([73, 20], [38, 31, 14]), ([73, 19], [38, 31, 13]), ([73, 18], [38, 31, 12]),
     ([79, 23], [44, 31, 17]), ([79, 22], [44, 31, 16]), ([79, 21], [44, 31, 15]),
     ([79, 20], [44, 31, 14]), ([79, 19], [44, 31, 13]), ([79, 18], [44, 31, 12])]

set_option maxRecDepth 65536 in
private theorem c39_eq_fastRules :
    filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List) = c39FastRules := by decide

set_option maxRecDepth 65536 in
private theorem c78_eq_fastRules :
    filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List) = c78FastRules := by decide

set_option maxRecDepth 65536 in
private theorem c39_w15_syz_and_int_certs :
    countActiveIntSymsBool 3 42 c39FastRules = 21 ∧
    checkPositiveParikhSyzygyFastBool 42 c39FastRules syzTwoSidedMod3OmitR3Core39 = true ∧
    checkFastIntAnnBoolW15 3 c39FastRules posMultsC39 negMultsC39 = true := by decide

set_option maxRecDepth 65536 in
private theorem c78_w15_syz_and_act_certs :
    countActiveIntSymsBool 6 84 c78FastRules = 42 ∧
    checkPositiveParikhSyzygyFastBool 84 c78FastRules syzTwoSidedMod6OmitR3Core78 = true := by decide

set_option maxRecDepth 65536 in
private theorem c78_w15_int_ann_cert :
    checkFastIntAnnBoolW15 6 c78FastRules posMultsC78 negMultsC78 = true := by decide

/--
  Theorem W15.1a (`c39_c78_interior_topleft_unit_lock_and_boundary_growth`,
  `zero custom axioms`):
  Universal All-Dimension (`∀ d ≥ 1`) Active-Interior Top-Left Unit Lock (`(M_s)_{0,0} = 1`
  Across All `21` Active Interior Symbols of `c39` & All `42` Active Interior Symbols of `c78`)
  vs Arbitrary `.R`-Boundary Top-Left Growth `(M_6)_{0,0} = (M_9)_{0,0} = k ≥ 2` (`Branch P4.3`,
  witness `ZPOS_C39_BOUNDARY_TOPLEFT_GROWTH_VS_INTERIOR_UNIT_LOCK`, `W15_H1`).
-/
theorem c39_c78_interior_topleft_unit_lock_and_boundary_growth :
    let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
    let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
    (countActiveIntSymsBool 3 42 c39 = 21 ∧ countActiveIntSymsBool 6 84 c78 = 42) ∧
    (∀ (d : Nat) (hd : d ≥ 1) (mat : Fin 42 -> Fin d -> Fin d -> Nat),
      let z0 : Fin d := ⟨0, hd⟩
      (∀ s : Fin 42, mat s z0 z0 ≥ 1) ->
      ((∀ (s : Fin 42) (i : Fin d), i.val ≥ 1 -> mat s i z0 = 0) ∨
       (∀ (s : Fin 42) (j : Fin d), j.val ≥ 1 -> mat s z0 j = 0)) ->
      (∀ r ∈ c39, ∀ i j : Fin d,
        evalFinWordMat 42 d mat r.1 i j ≥ evalFinWordMat 42 d mat r.2 i j) ->
      ∀ s : Fin 42, s.val ≥ 12 -> symAppearsInRulesBool 42 s.val c39 = true ->
        mat s z0 z0 = 1) ∧
    (∀ (d : Nat) (hd : d ≥ 1) (mat : Fin 84 -> Fin d -> Fin d -> Nat),
      let z0 : Fin d := ⟨0, hd⟩
      (∀ s : Fin 84, mat s z0 z0 ≥ 1) ->
      ((∀ (s : Fin 84) (i : Fin d), i.val ≥ 1 -> mat s i z0 = 0) ∨
       (∀ (s : Fin 84) (j : Fin d), j.val ≥ 1 -> mat s z0 j = 0)) ->
      (∀ r ∈ c78, ∀ i j : Fin d,
        evalFinWordMat 84 d mat r.1 i j ≥ evalFinWordMat 84 d mat r.2 i j) ->
      ∀ s : Fin 84, s.val ≥ 24 -> symAppearsInRulesBool 84 s.val c78 = true ->
        mat s z0 z0 = 1) ∧
    (∀ k : Nat, k ≥ 2 ->
      bndTopLeftMat2DC39 k ⟨6, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩ = k ∧
      bndTopLeftMat2DC39 k ⟨9, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩ = k ∧
      ∀ r ∈ c39, ∀ i j : Fin 2,
        evalFinWordMat 42 2 (bndTopLeftMat2DC39 k) r.1 i j ≥
          evalFinWordMat 42 2 (bndTopLeftMat2DC39 k) r.2 i j) := by
  dsimp only
  rw [c39_eq_fastRules, c78_eq_fastRules]
  let c39 := c39FastRules
  let c78 := c78FastRules
  rcases c39_w15_syz_and_int_certs with ⟨hc39_act, hsyz39, hann39⟩
  rcases c78_w15_syz_and_act_certs with ⟨hc78_act, hsyz78⟩
  have hann78 := c78_w15_int_ann_cert
  have hlock_gen : ∀ (M_mod : Nat)
      (rules : List (List (Fin (14 * M_mod)) × List (Fin (14 * M_mod))))
      (syz posM negM : List Nat),
      checkPositiveParikhSyzygyFastBool (14 * M_mod) rules syz = true ->
      checkFastIntAnnBoolW15 M_mod rules posM negM = true ->
      ∀ (d : Nat) (hd : d ≥ 1) (mat : Fin (14 * M_mod) -> Fin d -> Fin d -> Nat),
        let z0 : Fin d := ⟨0, hd⟩
        (∀ s : Fin (14 * M_mod), mat s z0 z0 ≥ 1) ->
        ((∀ (s : Fin (14 * M_mod)) (i : Fin d), i.val ≥ 1 -> mat s i z0 = 0) ∨
         (∀ (s : Fin (14 * M_mod)) (j : Fin d), j.val ≥ 1 -> mat s z0 j = 0)) ->
        (∀ r ∈ rules, ∀ i j : Fin d,
          evalFinWordMat (14 * M_mod) d mat r.1 i j ≥ evalFinWordMat (14 * M_mod) d mat r.2 i j) ->
        ∀ s : Fin (14 * M_mod), s.val ≥ 4 * M_mod ->
          symAppearsInRulesBool (14 * M_mod) s.val rules = true -> mat s z0 z0 = 1 := by
    intro M_mod rules syz posM negM hsyz hann d hd mat; dsimp only
    intro hm1 htri hweak
    let z0 : Fin d := ⟨0, hd⟩
    rcases evalFinWordMat_col0_or_row0_prod (14 * M_mod) d hd mat with ⟨hc0_ev, hr0_ev⟩
    have hprod_ge : ∀ r ∈ rules,
        prodFinWordW15 (14 * M_mod) (fun s => mat s z0 z0) r.1 ≥
          prodFinWordW15 (14 * M_mod) (fun s => mat s z0 z0) r.2 := by
      intro r hr
      have hw00 := hweak r hr z0 z0
      rcases htri with hc0 | hr0
      · rwa [(hc0_ev hc0 r.1).1, (hc0_ev hc0 r.2).1] at hw00
      · have e1 := hr0_ev hr0 r.1 z0
        have e2 := hr0_ev hr0 r.2 z0
        simp only [z0, ite_true] at e1 e2
        rwa [e1, e2] at hw00
    have hprod_eq := syzygy_forces_prod_eq_cf_w15 (14 * M_mod) rules syz hsyz
      (fun s => mat s z0 z0) hm1 hprod_ge
    exact signed_annihilation_forces_int_one_cf_w15 M_mod rules posM negM hann
      (fun s => mat s z0 z0) hm1 hprod_eq
  refine ⟨⟨hc39_act, hc78_act⟩,
          hlock_gen 3 c39 _ _ _ hsyz39 hann39,
          hlock_gen 6 c78 _ _ _ hsyz78 hann78,
          ?_⟩
  intro k _hk2
  refine ⟨rfl, rfl, ?_⟩
  let z0 : Fin 2 := ⟨0, by decide⟩
  let z1 : Fin 2 := ⟨1, by decide⟩
  have hr0_z : ∀ (s : Fin 42) (j : Fin 2), j.val ≥ 1 -> bndTopLeftMat2DC39 k s z0 j = 0 := by
    intro s j hj1
    have hjv : j.val = 1 := by have := j.isLt; omega
    have hje : j = z1 := Fin.ext hjv
    subst hje; rfl
  have hr1_z : ∀ (w : List (Fin 42)) (j : Fin 2), w ≠ [] ->
      evalFinWordMat 42 2 (bndTopLeftMat2DC39 k) w z1 j = 0 := by
    intro w j hne
    cases w with
    | nil => exact False.elim (hne rfl)
    | cons s rest =>
      change (0 + bndTopLeftMat2DC39 k s z1 z0 * _) + bndTopLeftMat2DC39 k s z1 z1 * _ = 0
      have h10 : bndTopLeftMat2DC39 k s z1 z0 = 0 := rfl
      have h11 : bndTopLeftMat2DC39 k s z1 z1 = 0 := rfl
      rw [h10, h11]; simp
  have h69_eq : ∀ r ∈ c39,
      countFinOcc 42 ⟨6, by decide⟩ r.1 + countFinOcc 42 ⟨9, by decide⟩ r.1 =
        countFinOcc 42 ⟨6, by decide⟩ r.2 + countFinOcc 42 ⟨9, by decide⟩ r.2 ∧
      r.1 ≠ [] ∧ r.2 ≠ [] := by
    have hchk : c39.all (fun r =>
        decide (countFinOcc 42 ⟨6, by decide⟩ r.1 + countFinOcc 42 ⟨9, by decide⟩ r.1 =
                  countFinOcc 42 ⟨6, by decide⟩ r.2 + countFinOcc 42 ⟨9, by decide⟩ r.2 ∧
                r.1 ≠ [] ∧ r.2 ≠ [])) = true := by decide
    exact fun r hr => of_decide_eq_true (List.all_eq_true.mp hchk r hr)
  have hprod_k : ∀ w : List (Fin 42),
      prodFinWordW15 42 (fun s => bndTopLeftMat2DC39 k s z0 z0) w =
        k ^ (countFinOcc 42 ⟨6, by decide⟩ w + countFinOcc 42 ⟨9, by decide⟩ w) := by
    intro w; induction w with
    | nil => simp [prodFinWordW15, countFinOcc]
    | cons s rest ih =>
      simp only [prodFinWordW15, ih, countFinOcc]
      by_cases h6 : s.val = 6
      · have hs6 : s = ⟨6, by decide⟩ := Fin.ext h6
        subst hs6
        change k * k ^ (countFinOcc 42 ⟨6, by decide⟩ rest + countFinOcc 42 ⟨9, by decide⟩ rest) =
          k ^ ((1 + countFinOcc 42 ⟨6, by decide⟩ rest) + (0 + countFinOcc 42 ⟨9, by decide⟩ rest))
        rw [show (1 + countFinOcc 42 ⟨6, by decide⟩ rest) +
              (0 + countFinOcc 42 ⟨9, by decide⟩ rest) =
            (countFinOcc 42 ⟨6, by decide⟩ rest + countFinOcc 42 ⟨9, by decide⟩ rest) + 1 by omega,
            Nat.pow_succ, Nat.mul_comm]
      · by_cases h9 : s.val = 9
        · have hs9 : s = ⟨9, by decide⟩ := Fin.ext h9
          subst hs9
          change k * k ^ (countFinOcc 42 ⟨6, by decide⟩ rest + countFinOcc 42 ⟨9, by decide⟩ rest) =
            k ^ ((0 + countFinOcc 42 ⟨6, by decide⟩ rest) + (1 + countFinOcc 42 ⟨9, by decide⟩ rest))
          rw [show (0 + countFinOcc 42 ⟨6, by decide⟩ rest) +
                (1 + countFinOcc 42 ⟨9, by decide⟩ rest) =
              (countFinOcc 42 ⟨6, by decide⟩ rest + countFinOcc 42 ⟨9, by decide⟩ rest) + 1 by omega,
              Nat.pow_succ, Nat.mul_comm]
        · have hv6 : (s.val == 6) = false := beq_false_of_ne h6
          have hv9 : (s.val == 9) = false := beq_false_of_ne h9
          have hm1_s : bndTopLeftMat2DC39 k s z0 z0 = 1 := by
            unfold bndTopLeftMat2DC39; simp [z0, hv6, hv9]
          rw [hm1_s, Nat.one_mul, ite_false_of_w10 h6, ite_false_of_w10 h9,
              Nat.zero_add, Nat.zero_add]
  rcases evalFinWordMat_col0_or_row0_prod 42 2 (by decide) (bndTopLeftMat2DC39 k) with ⟨_, hr0_ev⟩
  intro r hr i j
  rcases h69_eq r hr with ⟨hcnt_eq, hne1, hne2⟩
  rcases (by have := i.isLt; omega : i.val = 0 ∨ i.val = 1) with hi0 | hi1
  · have hie : i = z0 := Fin.ext hi0; subst hie
    rw [hr0_ev hr0_z r.1 j, hr0_ev hr0_z r.2 j]
    by_cases hj0 : j.val = 0
    · rw [ite_true_of_w10 hj0, ite_true_of_w10 hj0, hprod_k r.1, hprod_k r.2, hcnt_eq]
      exact Nat.le_refl _
    · rw [ite_false_of_w10 hj0, ite_false_of_w10 hj0]; exact Nat.le_refl 0
  · have hie : i = z1 := Fin.ext hi1; subst hie
    rw [hr1_z r.1 j hne1, hr1_z r.2 j hne2]; exact Nat.le_refl 0

-- ----------------------------------------------------------------------------
-- Section 1B: Non-Uniform Mixed Zero-Diagonal Binary-Top / Ternary-Subrow `ω^k`
--             Matrix-Tower Impossibility (`∀ d ≥ 1`) & 24-Strict-Rule Witness
-- ----------------------------------------------------------------------------

/-- Explicit non-uniform mixed zero-diagonal non-triangular `d = 2` BT witness on `Fin 42`
    achieving `24` strict matrix inequalities across the `39` rules of `c39` (`(M_17)_{0,1} = 2,
    (M_17)_{1,1} = 0, (M_28)_{1,0} = 1, (M_28)_{1,1} = 3`, admitting no uniform column eigenweight). -/
def btWitnessMat2DC39 (s : Fin 42) (i j : Fin 2) : Nat :=
  match s.val with
  | 7 =>  match i.val, j.val with | 0, 0 => 1 | 0, 1 => 0 | 1, 0 => 1 | _, _ => 5
  | 8 =>  match i.val, j.val with | 0, 0 => 1 | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  | 11 => match i.val, j.val with | 0, 0 => 1 | 0, 1 => 1 | 1, 0 => 1 | _, _ => 3
  | 17 => match i.val, j.val with | 0, 0 => 1 | 0, 1 => 2 | _, _ => 0
  | 28 => match i.val, j.val with | 0, 0 => 1 | 0, 1 => 0 | 1, 0 => 1 | _, _ => 3
  | 31 => match i.val, j.val with | 0, 0 => 1 | 0, 1 => 0 | 1, 0 => 2 | _, _ => 3
  | 32 => match i.val, j.val with | 0, 0 => 1 | 0, 1 => 0 | 1, 0 => 1 | _, _ => 3
  | 33 => match i.val, j.val with | 0, 0 => 1 | 0, 1 => 0 | 1, 0 => 1 | _, _ => 3
  | 35 => match i.val, j.val with | 0, 0 => 1 | 0, 1 => 0 | 1, 0 => 2 | _, _ => 3
  | 36 => match i.val, j.val with | 0, 0 => 1 | 0, 1 => 0 | 1, 0 => 2 | _, _ => 3
  | 39 => match i.val, j.val with | 0, 0 => 1 | 0, 1 => 0 | 1, 0 => 2 | _, _ => 3
  | 40 => match i.val, j.val with | 0, 0 => 1 | 0, 1 => 0 | 1, 0 => 1 | _, _ => 3
  | 41 => match i.val, j.val with | 0, 0 => 1 | 0, 1 => 0 | 1, 0 => 2 | _, _ => 1
  | _ =>  if i.val == 0 && j.val == 0 then 1 else 0

/-- `k`-level `ω^k` Hofbauer–Waldmann natural matrix tower over `Fin (14 * M)` of dimension `d ≥ 1`
    in the non-uniform mixed zero-diagonal BT stratum:
    - `.L` (`s < 2 * M`) and `.T` (`s ≥ 8 * M`) have top row `[1, 0, ..., 0]` and **completely
      arbitrary** bottom `d - 1` rows (`i ≥ 1`),
    - `.B` (`4 * M ≤ s < 8 * M`) has `(M_s)_{0,0} ≥ 1` and **completely arbitrary** remaining
      `d^2 - 1` entries,
    - `.R` (`2 * M ≤ s < 4 * M`) has **completely arbitrary** `d × d` matrices! -/
def GenOmegaNonUniformMixedZeroDiagBTMatTower (M d : Nat) (hd : d ≥ 1) :
    Nat -> List (List (Fin (14 * M)) × List (Fin (14 * M))) -> Prop
  | 0, rules => rules = []
  | k + 1, rules =>
    rules = [] ∨
    ∃ (rem : List (List (Fin (14 * M)) × List (Fin (14 * M))))
      (mat : Fin (14 * M) -> Fin d -> Fin d -> Nat)
      (v : Fin (14 * M) -> Fin d -> Nat),
      (∀ s : Fin (14 * M), (s.val < 2 * M ∨ s.val ≥ 8 * M) ->
        mat s ⟨0, hd⟩ ⟨0, hd⟩ = 1 ∧ ∀ j : Fin d, j.val ≥ 1 -> mat s ⟨0, hd⟩ j = 0) ∧
      (∀ s : Fin (14 * M), 4 * M ≤ s.val -> s.val < 8 * M ->
        mat s ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1) ∧
      (∀ r ∈ rules,
        (∀ i j : Fin d, evalFinWordMat (14 * M) d mat r.1 i j ≥ evalFinWordMat (14 * M) d mat r.2 i j) ∧
        (∀ i : Fin d, evalFinWordVec (14 * M) d mat v r.1 i ≥ evalFinWordVec (14 * M) d mat v r.2 i)) ∧
      (∀ r ∈ rules,
        ¬ (evalFinWordVec (14 * M) d mat v r.1 ⟨0, hd⟩ >
           evalFinWordVec (14 * M) d mat v r.2 ⟨0, hd⟩) ->
        r ∈ rem) ∧
      GenOmegaNonUniformMixedZeroDiagBTMatTower M d hd k rem

private def checkBTRuleShapeBool (M : Nat) (r : List (Fin (14 * M)) × List (Fin (14 * M))) : Bool :=
  (match r.1 with
   | [s1, _] => decide (s1.val < 2 * M ∨ s1.val ≥ 8 * M)
   | _ => false) &&
  (let rec nonLastNoR : List (Fin (14 * M)) -> Bool
     | [] => true
     | [_] => true
     | s :: s2 :: tl => decide (s.val < 2 * M ∨ s.val ≥ 4 * M) && nonLastNoR (s2 :: tl)
   nonLastNoR r.2)

private def checkAllBTRuleShapeBool (M : Nat) :
    List (List (Fin (14 * M)) × List (Fin (14 * M))) -> Bool
  | [] => true
  | r :: rs => checkBTRuleShapeBool M r && checkAllBTRuleShapeBool M rs

set_option maxRecDepth 65536 in
private theorem bt_witness_and_shape_certs :
    checkAllWeakMat2DBool 42 btWitnessMat2DC39 c39FastRules = true ∧
    countStrictMat2DRules 42 btWitnessMat2DC39 c39FastRules = 24 ∧
    checkAllBTRuleShapeBool 3 c39FastRules = true ∧
    c39FastRules ≠ [] ∧
    checkAllBTRuleShapeBool 6 c78FastRules = true ∧
    c78FastRules ≠ [] := by decide

/--
  Theorem W15.1b (`twosided_c39_c78_nonuniform_mixed_zerodiag_bt_impossibility`,
  `zero custom axioms`):
  24-Strict-Rule Non-Uniform Mixed Zero-Diagonal BT Matrix Witness on `c39` & Universal
  All-Dimension (`∀ d ≥ 1`) Impossibility of `GenOmegaNonUniformMixedZeroDiagBTMatTower`
  Across `TwoSided(2 × 3)` `c39` & `TwoSided(2 × 6)` `c78` (`Branch P4.3`, `W15_H1`).
-/
theorem twosided_c39_c78_nonuniform_mixed_zerodiag_bt_impossibility :
    let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
    let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
    (btWitnessMat2DC39 ⟨17, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩ = 2 ∧
     btWitnessMat2DC39 ⟨17, by decide⟩ ⟨1, by decide⟩ ⟨1, by decide⟩ = 0 ∧
     btWitnessMat2DC39 ⟨28, by decide⟩ ⟨1, by decide⟩ ⟨0, by decide⟩ = 1 ∧
     btWitnessMat2DC39 ⟨28, by decide⟩ ⟨1, by decide⟩ ⟨1, by decide⟩ = 3 ∧
     checkAllWeakMat2DBool 42 btWitnessMat2DC39 c39 = true ∧
     countStrictMat2DRules 42 btWitnessMat2DC39 c39 = 24) ∧
    (∀ (d : Nat) (hd : d ≥ 1) (k : Nat),
      ¬ GenOmegaNonUniformMixedZeroDiagBTMatTower 3 d hd k c39 ∧
      ¬ GenOmegaNonUniformMixedZeroDiagBTMatTower 6 d hd k c78) := by
  dsimp only
  rw [c39_eq_fastRules, c78_eq_fastRules]
  let c39 := c39FastRules
  let c78 := c78FastRules
  rcases bt_witness_and_shape_certs with ⟨hw_bt, hcnt_bt, hsh39, hne39, hsh78, hne78⟩
  rcases c39_w15_syz_and_int_certs with ⟨_, hsyz39, _⟩
  rcases c78_w15_syz_and_act_certs with ⟨_, hsyz78⟩
  have hbt_master : ∀ (M : Nat)
      (core : List (List (Fin (14 * M)) × List (Fin (14 * M))))
      (syz : List Nat),
      checkAllBTRuleShapeBool M core = true ->
      core ≠ [] ->
      checkPositiveParikhSyzygyFastBool (14 * M) core syz = true ->
      ∀ (d : Nat) (hd : d ≥ 1) (k : Nat),
        ¬ GenOmegaNonUniformMixedZeroDiagBTMatTower M d hd k core := by
    intro M core syz hsh hne hsyz d hd
    let N := 14 * M
    let z0 : Fin d := ⟨0, hd⟩
    have hsyz_par : ∀ wt : Fin N -> Nat,
        (∀ r ∈ core, evalFinParikh N wt r.1 ≥ evalFinParikh N wt r.2) ->
        ∀ r ∈ core, evalFinParikh N wt r.1 = evalFinParikh N wt r.2 := by
      unfold checkPositiveParikhSyzygyFastBool at hsyz
      rcases bool_and_split hsyz with ⟨hb1, hpairs⟩
      rcases bool_and_split hb1 with ⟨hb2, hpos_m⟩
      rcases bool_and_split hb2 with ⟨_, hlen_eq⟩
      have hlen : core.length = syz.length := of_decide_eq_true hlen_eq
      rcases accumSymCountsW11_spec N core syz with ⟨hacc_len, hacc_get⟩
      have hsym_le : ∀ s : Fin N, weightedSymLhsSum N s core syz ≤ weightedSymRhsSum N s core syz := by
        intro s
        have hle := checkPairsLeBoolW11_sound _ hpairs s.val (by rw [hacc_len]; exact s.isLt)
        rwa [hacc_get s] at hle
      intro wt hweak
      rcases weightedParikh_eq_sum_sym N wt core syz with ⟨hl_sum, hr_sum⟩
      have htot_le : weightedParikhLhs N wt core syz ≤ weightedParikhRhs N wt core syz := by
        rw [hl_sum, hr_sum]
        exact natSumPrefix_mono_w5 N _ _ (fun s => Nat.mul_le_mul_left (wt s) (hsym_le s)) N
      exact weightedParikh_strict_of_mem N wt core syz hlen hpos_m hweak htot_le
    have hsh_mem : ∀ r ∈ core, checkBTRuleShapeBool M r = true := by
      have hlp : ∀ rs : List (List (Fin N) × List (Fin N)),
          checkAllBTRuleShapeBool M rs = true -> ∀ r ∈ rs, checkBTRuleShapeBool M r = true := by
        intro rs; induction rs with
        | nil => intros _ _ hr; cases hr
        | cons r0 rtl ih =>
          intro hb r hr
          rcases bool_and_split hb with ⟨h0, htl⟩
          cases hr with
          | head => exact h0
          | tail _ hm => exact ih htl r hm
      exact hlp core hsh
    have hno_strict : ∀ (mat : Fin N -> Fin d -> Fin d -> Nat) (v : Fin N -> Fin d -> Nat),
        (∀ s : Fin N, (s.val < 2 * M ∨ s.val ≥ 8 * M) ->
          mat s z0 z0 = 1 ∧ ∀ j : Fin d, j.val ≥ 1 -> mat s z0 j = 0) ->
        (∀ s : Fin N, 4 * M ≤ s.val -> s.val < 8 * M -> mat s z0 z0 ≥ 1) ->
        (∀ r ∈ core, evalFinWordVec N d mat v r.1 z0 ≥ evalFinWordVec N d mat v r.2 z0) ->
        ∀ r ∈ core, evalFinWordVec N d mat v r.1 z0 = evalFinWordVec N d mat v r.2 z0 := by
      intro mat v hLT hB hv0_ge
      have hsum_single0 : ∀ (f : Fin d -> Nat), (∀ j : Fin d, j.val ≥ 1 -> f j = 0) ->
          natSumPrefix d f d = f z0 := by
        intro f hz
        have hst : ∀ m : Nat, m ≤ d -> natSumPrefix d f m = (if 0 < m then f z0 else 0) := by
          intro m hm; induction m with
          | zero => rfl
          | succ m' ih =>
            have hm_lt : m' < d := hm
            simp only [natSumPrefix, hm_lt, dite_true, ih (Nat.le_of_lt hm)]
            cases m' with
            | zero => have h0f : (⟨0, hm_lt⟩ : Fin d) = z0 := rfl; rw [h0f]; simp
            | succ m'' => rw [hz ⟨m'' + 1, hm_lt⟩ (by dsimp; omega), Nat.add_zero]; simp
        rw [hst d (Nat.le_refl d), ite_true_of_w10 (by omega : 0 < d)]
      have hsum_ge0 : ∀ (f : Fin d -> Nat), natSumPrefix d f d ≥ f z0 := by
        intro f
        have hst : ∀ m : Nat, m ≤ d -> (0 < m -> natSumPrefix d f m ≥ f z0) := by
          intro m hm; induction m with
          | zero => intro h0; omega
          | succ m' ih =>
            have hm_lt : m' < d := hm
            intro _
            simp only [natSumPrefix, hm_lt, dite_true]
            cases m' with
            | zero => have h0f : (⟨0, hm_lt⟩ : Fin d) = z0 := rfl; rw [h0f]; omega
            | succ m'' => have hp := ih (Nat.le_of_lt hm) (by omega); omega
        exact hst d (Nat.le_refl d) hd
      have hlhs_eq : ∀ (s1 s2 : Fin N), (s1.val < 2 * M ∨ s1.val ≥ 8 * M) ->
          evalFinWordVec N d mat v [s1, s2] z0 =
            evalFinParikh N (fun s => v s z0) [s1, s2] := by
        intro s1 s2 hs1
        rcases hLT s1 hs1 with ⟨h00, h0j⟩
        have hv_s2 : ∀ j : Fin d, evalFinWordVec N d mat v [s2] j = v s2 j := by
          intro j
          change v s2 j + natSumPrefix d (fun k => mat s2 j k * (0 : Nat)) d = v s2 j
          have hz : ∀ m : Nat, natSumPrefix d (fun k => mat s2 j k * (0 : Nat)) m = 0 := by
            intro m; induction m with
            | zero => rfl
            | succ m' ihm =>
              simp only [natSumPrefix]
              by_cases hm : m' < d
              · simp only [hm, dite_true]; rw [ihm, Nat.mul_zero]
              · simp only [hm, dite_false]; rw [ihm]
          rw [hz d, Nat.add_zero]
        change v s1 z0 + natSumPrefix d (fun j => mat s1 z0 j * evalFinWordVec N d mat v [s2] j) d =
          v s1 z0 + (v s2 z0 + 0)
        rw [hsum_single0 _ (fun j hj => by rw [h0j j hj, Nat.zero_mul]), hv_s2 z0, h00,
            Nat.one_mul, Nat.add_zero]
      have hrhs_ge : ∀ w : List (Fin N),
          checkBTRuleShapeBool.nonLastNoR M w = true ->
          evalFinWordVec N d mat v w z0 ≥ evalFinParikh N (fun s => v s z0) w := by
        intro w; induction w with
        | nil => intros; exact Nat.le_refl 0
        | cons s rest ih =>
          cases rest with
          | nil =>
            intros
            change v s z0 + natSumPrefix d (fun k => mat s z0 k * (0 : Nat)) d ≥ v s z0 + 0
            omega
          | cons s2 tl =>
            intro hb
            rcases bool_and_split hb with ⟨hs_b, hrest⟩
            have ih_r := ih hrest
            have hs00_ge1 : mat s z0 z0 ≥ 1 := by
              rcases of_decide_eq_true hs_b with hlt2 | hge4
              · rw [(hLT s (Or.inl hlt2)).1]; exact Nat.le_refl 1
              · by_cases hlt8 : s.val < 8 * M
                · exact hB s hge4 hlt8
                · rw [(hLT s (Or.inr (by omega))).1]; exact Nat.le_refl 1
            change v s z0 + natSumPrefix d (fun j => mat s z0 j * evalFinWordVec N d mat v (s2 :: tl) j) d ≥
              v s z0 + evalFinParikh N (fun x => v x z0) (s2 :: tl)
            have hge_sum := hsum_ge0 (fun j => mat s z0 j * evalFinWordVec N d mat v (s2 :: tl) j)
            have hm_ge := Nat.mul_le_mul hs00_ge1 ih_r
            rw [Nat.one_mul] at hm_ge
            omega
      have hboth : ∀ r ∈ core,
          evalFinWordVec N d mat v r.1 z0 = evalFinParikh N (fun s => v s z0) r.1 ∧
          evalFinWordVec N d mat v r.2 z0 ≥ evalFinParikh N (fun s => v s z0) r.2 := by
        intro r hr
        have hsh_r := hsh_mem r hr
        unfold checkBTRuleShapeBool at hsh_r
        rcases bool_and_split hsh_r with ⟨hl_b, hr_b⟩
        cases hl_eq : r.1 with
        | nil => rw [hl_eq] at hl_b; cases hl_b
        | cons s1 t1 =>
          cases t1 with
          | nil => rw [hl_eq] at hl_b; cases hl_b
          | cons s2 t2 =>
            cases t2 with
            | cons _ _ => rw [hl_eq] at hl_b; cases hl_b
            | nil =>
              rw [hl_eq] at hl_b
              exact ⟨hlhs_eq s1 s2 (of_decide_eq_true hl_b), hrhs_ge r.2 hr_b⟩
      have hpar_ge : ∀ r ∈ core,
          evalFinParikh N (fun s => v s z0) r.1 ≥ evalFinParikh N (fun s => v s z0) r.2 := by
        intro r hr
        rcases hboth r hr with ⟨he1, hge2⟩
        have hv0 := hv0_ge r hr
        omega
      have hpar_eq := hsyz_par (fun s => v s z0) hpar_ge
      intro r hr
      rcases hboth r hr with ⟨he1, hge2⟩
      have hv0 := hv0_ge r hr
      have hpe := hpar_eq r hr
      omega
    cases hc_eq : core with
    | nil => exact False.elim (hne hc_eq)
    | cons r0 rs =>
      rw [← hc_eq]
      have hm0 : r0 ∈ core := hc_eq ▸ List.Mem.head _
      have himp : ∀ (k : Nat) (cur : List (List (Fin N) × List (Fin N))),
          (∀ r ∈ core, r ∈ cur) -> ¬ GenOmegaNonUniformMixedZeroDiagBTMatTower M d hd k cur := by
        intro k; induction k with
        | zero =>
          intro cur hsub h0; rw [GenOmegaNonUniformMixedZeroDiagBTMatTower] at h0; subst h0
          exact List.not_mem_nil (hsub r0 hm0)
        | succ k' ih =>
          intro cur hsub hsucc
          rcases hsucc with rfl | ⟨rem, mat, v, hLT, hB, hweak, hkeep, hrem⟩
          · exact List.not_mem_nil (hsub r0 hm0)
          · have heq := hno_strict mat v hLT hB (fun r hr => (hweak r (hsub r hr)).2 z0)
            exact ih rem (fun r hr => hkeep r (hsub r hr)
              (by rw [heq r hr]; exact Nat.lt_irrefl _)) hrem
      exact fun k => himp k core (fun _ hr => hr)
  exact ⟨⟨rfl, rfl, rfl, rfl, hw_bt, hcnt_bt⟩,
         fun d hd k =>
           ⟨hbt_master 3 c39 _ hsh39 hne39 hsyz39 d hd k,
            hbt_master 6 c78 _ hsh78 hne78 hsyz78 d hd k⟩⟩

-- ----------------------------------------------------------------------------
-- Section 1C: Infinite 2-Parameter `.T`-Coupled `d = 2` Cone `paramMat2DC39 α β`
--             & Parameterized Farkas Syzygy Lock (`∀ α ≥ 1, ∀ β ≥ 1`)
-- ----------------------------------------------------------------------------

/-- Infinite 2-parameter `.T`-coupled mixed zero-diagonal `d = 2` cone on `c39`
    generalizing `weakMat2DC39` (`paramMat2DC39 1 1 = weakMat2DC39`):
    `(M_37)_{0,1} = α`, `(M_20)_{0,1} = 6α`, `(M_22)_{0,1} = (M_23)_{0,1} = 5α`,
    `(M_28)_{1,0} = β`, `(M_31)_{1,0} = 7β`. -/
def paramMat2DC39 (alpha beta : Nat) (s : Fin 42) (i j : Fin 2) : Nat :=
  match i.val, j.val with
  | 0, 0 => 1
  | 0, 1 =>
    match s.val with
    | 20 => 6 * alpha | 22 => 5 * alpha | 23 => 5 * alpha | 37 => alpha | _ => 0
  | 1, 0 =>
    match s.val with
    | 28 => beta | 31 => 7 * beta | _ => 0
  | _, _ =>
    match s.val with
    | 6 => 5 | 7 => 3 | 14 => 3 | 17 => 1 | 23 => 1 | 28 => 5 | 31 => 1 | 32 => 1 | _ => 0

private def isAlphaSymBool (s : Fin 42) : Bool :=
  s.val == 20 || s.val == 22 || s.val == 23 || s.val == 37

private def isBetaSymBool (s : Fin 42) : Bool :=
  s.val == 28 || s.val == 31

private def wordNoBetaBool (w : List (Fin 42)) : Bool :=
  w.all (fun s => !isBetaSymBool s)

private def wordNoAlphaBool (w : List (Fin 42)) : Bool :=
  w.all (fun s => !isAlphaSymBool s)

private abbrev fin2Z0 : Fin 2 := ⟨0, by decide⟩
private abbrev fin2Z1 : Fin 2 := ⟨1, by decide⟩

private def farkasParamVecLhs42 (alpha beta : Nat) (v : Fin 42 -> Fin 2 -> Nat) :
    List (List (Fin 42) × List (Fin 42)) -> Nat
  | [] => 0
  | (l, _) :: rs =>
    farkasMu0C39 l * evalFinWordVec 42 2 (paramMat2DC39 alpha beta) v l fin2Z0 +
      (alpha * farkasMu1C39 l) * evalFinWordVec 42 2 (paramMat2DC39 alpha beta) v l fin2Z1 +
      farkasParamVecLhs42 alpha beta v rs

private def farkasParamVecRhs42 (alpha beta : Nat) (v : Fin 42 -> Fin 2 -> Nat) :
    List (List (Fin 42) × List (Fin 42)) -> Nat
  | [] => 0
  | (l, r) :: rs =>
    farkasMu0C39 l * evalFinWordVec 42 2 (paramMat2DC39 alpha beta) v r fin2Z0 +
      (alpha * farkasMu1C39 l) * evalFinWordVec 42 2 (paramMat2DC39 alpha beta) v r fin2Z1 +
      farkasParamVecRhs42 alpha beta v rs

private def farkasParamWeightedVecSum42 (alpha beta : Nat) (v : Fin 42 -> Fin 2 -> Nat)
    (rs : List (List (Fin 42) × List (Fin 42))) : (Nat × Nat) :=
  (farkasParamVecLhs42 alpha beta v rs, farkasParamVecRhs42 alpha beta v rs)

private def checkParamFarkasCoordBool (j0 : Fin 2)
    (rules : List (List (Fin 42) × List (Fin 42))) : Bool :=
  let rec loop : Nat -> Bool
    | 0 => true
    | k + 1 =>
      if h : k < 42 then
        let l0 := farkasParamVecLhs42 0 0 (basisVec2D 42 ⟨k, h⟩ j0) rules
        let r0 := farkasParamVecRhs42 0 0 (basisVec2D 42 ⟨k, h⟩ j0) rules
        let l1 := farkasParamVecLhs42 1 0 (basisVec2D 42 ⟨k, h⟩ j0) rules
        let r1 := farkasParamVecRhs42 1 0 (basisVec2D 42 ⟨k, h⟩ j0) rules
        decide (l0 ≤ r0 ∧ l1 - l0 ≤ r1 - r0) && loop k
      else loop k
  loop 42

private theorem paramMat_noBeta_or_noAlpha (alpha beta : Nat) :
    let z0 : Fin 2 := ⟨0, by decide⟩
    let z1 : Fin 2 := ⟨1, by decide⟩
    (∀ w : List (Fin 42), wordNoBetaBool w = true ->
      evalFinWordMat 42 2 (paramMat2DC39 alpha beta) w z0 z0 = 1 ∧
      evalFinWordMat 42 2 (paramMat2DC39 alpha beta) w z0 z1 =
        alpha * evalFinWordMat 42 2 (paramMat2DC39 1 0) w z0 z1 ∧
      evalFinWordMat 42 2 (paramMat2DC39 alpha beta) w z1 z0 = 0 ∧
      evalFinWordMat 42 2 (paramMat2DC39 alpha beta) w z1 z1 =
        evalFinWordMat 42 2 (paramMat2DC39 0 0) w z1 z1 ∧
      ∀ v : Fin 42 -> Fin 2 -> Nat,
        evalFinWordVec 42 2 (paramMat2DC39 alpha beta) v w z0 =
          evalFinWordVec 42 2 (paramMat2DC39 0 0) v w z0 +
            alpha * (evalFinWordVec 42 2 (paramMat2DC39 1 0) v w z0 -
                     evalFinWordVec 42 2 (paramMat2DC39 0 0) v w z0) ∧
        evalFinWordVec 42 2 (paramMat2DC39 alpha beta) v w z1 =
          evalFinWordVec 42 2 (paramMat2DC39 0 0) v w z1) ∧
    (∀ w : List (Fin 42), wordNoAlphaBool w = true ->
      evalFinWordMat 42 2 (paramMat2DC39 alpha beta) w z0 z0 = 1 ∧
      evalFinWordMat 42 2 (paramMat2DC39 alpha beta) w z0 z1 = 0 ∧
      evalFinWordMat 42 2 (paramMat2DC39 alpha beta) w z1 z0 =
        beta * evalFinWordMat 42 2 (paramMat2DC39 0 1) w z1 z0 ∧
      evalFinWordMat 42 2 (paramMat2DC39 alpha beta) w z1 z1 =
        evalFinWordMat 42 2 (paramMat2DC39 0 0) w z1 z1 ∧
      ∀ v : Fin 42 -> Fin 2 -> Nat,
        evalFinWordVec 42 2 (paramMat2DC39 alpha beta) v w z0 =
          evalFinWordVec 42 2 (paramMat2DC39 0 0) v w z0 ∧
        evalFinWordVec 42 2 (paramMat2DC39 alpha beta) v w z1 =
          evalFinWordVec 42 2 (paramMat2DC39 0 0) v w z1 +
            beta * (evalFinWordVec 42 2 (paramMat2DC39 0 1) v w z1 -
                    evalFinWordVec 42 2 (paramMat2DC39 0 0) v w z1)) := by
  dsimp only
  let z0 : Fin 2 := ⟨0, by decide⟩
  let z1 : Fin 2 := ⟨1, by decide⟩
  have hsym : ∀ s : Fin 42,
      (∀ a b : Nat, paramMat2DC39 a b s z0 z0 = 1) ∧
      (∀ a b : Nat, paramMat2DC39 a b s z0 z1 = a * paramMat2DC39 1 0 s z0 z1) ∧
      (∀ a b : Nat, paramMat2DC39 a b s z1 z0 = b * paramMat2DC39 0 1 s z1 z0) ∧
      (∀ a b : Nat, paramMat2DC39 a b s z1 z1 = paramMat2DC39 0 0 s z1 z1) ∧
      ((!isBetaSymBool s) = true -> ∀ a b : Nat, paramMat2DC39 a b s z1 z0 = 0) ∧
      ((!isAlphaSymBool s) = true -> ∀ a b : Nat, paramMat2DC39 a b s z0 z1 = 0) := by
    intro s
    unfold paramMat2DC39 isAlphaSymBool isBetaSymBool; dsimp only [z0, z1]
    by_cases h20 : s.val = 20
    · rw [h20]; simp [Nat.mul_comm]
    · by_cases h22 : s.val = 22
      · rw [h22]; simp [Nat.mul_comm]
      · by_cases h23 : s.val = 23
        · rw [h23]; simp [Nat.mul_comm]
        · by_cases h28 : s.val = 28
          · rw [h28]; simp
          · by_cases h31 : s.val = 31
            · rw [h31]; simp [Nat.mul_comm]
            · by_cases h37 : s.val = 37
              · rw [h37]; simp
              · simp [h20, h22, h23, h28, h31, h37]
  have hexp_m : ∀ (a b : Nat) (s : Fin 42) (u : List (Fin 42)) (i j : Fin 2),
      evalFinWordMat 42 2 (paramMat2DC39 a b) (s :: u) i j =
        paramMat2DC39 a b s i z0 * evalFinWordMat 42 2 (paramMat2DC39 a b) u z0 j +
        paramMat2DC39 a b s i z1 * evalFinWordMat 42 2 (paramMat2DC39 a b) u z1 j := by
    intro a b s u i j
    change (0 + paramMat2DC39 a b s i z0 * _) + paramMat2DC39 a b s i z1 * _ = _
    rw [Nat.zero_add]
  have hexp_v : ∀ (a b : Nat) (v : Fin 42 -> Fin 2 -> Nat) (s : Fin 42) (u : List (Fin 42)) (i : Fin 2),
      evalFinWordVec 42 2 (paramMat2DC39 a b) v (s :: u) i =
        v s i + paramMat2DC39 a b s i z0 * evalFinWordVec 42 2 (paramMat2DC39 a b) v u z0 +
        paramMat2DC39 a b s i z1 * evalFinWordVec 42 2 (paramMat2DC39 a b) v u z1 := by
    intro a b v s u i
    change v s i + ((0 + paramMat2DC39 a b s i z0 * _) + paramMat2DC39 a b s i z1 * _) = _
    rw [Nat.zero_add, Nat.add_assoc]
  have hnoB_gen : ∀ (a b : Nat) (w : List (Fin 42)), wordNoBetaBool w = true ->
      evalFinWordMat 42 2 (paramMat2DC39 a b) w z0 z0 = 1 ∧
      evalFinWordMat 42 2 (paramMat2DC39 a b) w z0 z1 =
        a * evalFinWordMat 42 2 (paramMat2DC39 1 0) w z0 z1 ∧
      evalFinWordMat 42 2 (paramMat2DC39 a b) w z1 z0 = 0 ∧
      evalFinWordMat 42 2 (paramMat2DC39 a b) w z1 z1 =
        evalFinWordMat 42 2 (paramMat2DC39 0 0) w z1 z1 ∧
      ∀ v : Fin 42 -> Fin 2 -> Nat,
        evalFinWordVec 42 2 (paramMat2DC39 0 0) v w z0 ≤
          evalFinWordVec 42 2 (paramMat2DC39 1 0) v w z0 ∧
        evalFinWordVec 42 2 (paramMat2DC39 a b) v w z0 =
          evalFinWordVec 42 2 (paramMat2DC39 0 0) v w z0 +
            a * (evalFinWordVec 42 2 (paramMat2DC39 1 0) v w z0 -
                 evalFinWordVec 42 2 (paramMat2DC39 0 0) v w z0) ∧
        evalFinWordVec 42 2 (paramMat2DC39 a b) v w z1 =
          evalFinWordVec 42 2 (paramMat2DC39 0 0) v w z1 := by
    intro a b w; induction w with
    | nil =>
      intros
      exact ⟨rfl, by simp [evalFinWordMat, natMatId, z0, z1], rfl, rfl,
             fun _ => ⟨Nat.le_refl 0, by simp [evalFinWordVec], rfl⟩⟩
    | cons s u ih =>
      intro hwb
      unfold wordNoBetaBool at hwb; simp only [List.all_cons] at hwb
      rcases bool_and_split hwb with ⟨hs_nb, hu_nb⟩
      rcases ih hu_nb with ⟨hm00, hm01, hm10, hm11, hv_u⟩
      rcases hsym s with ⟨hs00, hs01, _, hs11, hs_z10, _⟩
      -- Also instantiate `ih` at `(1, 0)` and `(0, 0)` to simplify RHS matrix products:
      have h10_z11 : evalFinWordMat 42 2 (paramMat2DC39 1 0) u z1 z1 =
          evalFinWordMat 42 2 (paramMat2DC39 0 0) u z1 z1 := by
        clear hwb ih hm00 hm01 hm10 hm11 hv_u
        induction u with
        | nil => rfl
        | cons x ut ihu =>
          simp only [List.all_cons] at hu_nb
          rcases bool_and_split hu_nb with ⟨hx_nb, hut_nb⟩
          rw [hexp_m 1 0 x ut z1 z1, hexp_m 0 0 x ut z1 z1,
              (hsym x).2.2.2.2.1 hx_nb 1 0, (hsym x).2.2.2.2.1 hx_nb 0 0,
              (hsym x).2.2.2.1 1 0, ihu hut_nb, Nat.zero_mul, Nat.zero_mul]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hexp_m, hs00, hm00, hm10, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
      · rw [hexp_m a b s u z0 z1, hexp_m 1 0 s u z0 z1,
            hs00 a b, hs00 1 0, hm01, hs01 a b, hm11, h10_z11,
            Nat.one_mul, Nat.one_mul, Nat.mul_add]
        ac_rfl
      · rw [hexp_m, hs_z10 hs_nb a b, hm10, Nat.zero_mul, Nat.mul_zero]
      · rw [hexp_m a b s u z1 z1, hexp_m 0 0 s u z1 z1,
            hs_z10 hs_nb a b, hs_z10 hs_nb 0 0, hs11 a b, hm11]
        simp only [Nat.zero_mul, Nat.zero_add]
      · intro v
        rcases hv_u v with ⟨hle_u, hv0_u, hv1_u⟩
        have hv0_00 : evalFinWordVec 42 2 (paramMat2DC39 0 0) v (s :: u) z0 =
            v s z0 + evalFinWordVec 42 2 (paramMat2DC39 0 0) v u z0 := by
          rw [hexp_v 0 0 v s u z0, hs00 0 0, hs01 0 0]; simp
        have hv1_10 : evalFinWordVec 42 2 (paramMat2DC39 1 0) v u z1 =
            evalFinWordVec 42 2 (paramMat2DC39 0 0) v u z1 := by
          clear hwb ih hm00 hm01 hm10 hm11 hv_u hle_u hv0_u hv1_u h10_z11 hv0_00
          induction u with
          | nil => rfl
          | cons x ut ihu =>
            simp only [List.all_cons] at hu_nb
            rcases bool_and_split hu_nb with ⟨hx_nb, hut_nb⟩
            rw [hexp_v 1 0 v x ut z1, hexp_v 0 0 v x ut z1,
                (hsym x).2.2.2.2.1 hx_nb 1 0, (hsym x).2.2.2.2.1 hx_nb 0 0,
                (hsym x).2.2.2.1 1 0, ihu hut_nb]
            simp only [Nat.zero_mul, Nat.add_zero]
        have hv0_10 : evalFinWordVec 42 2 (paramMat2DC39 1 0) v (s :: u) z0 =
            v s z0 + evalFinWordVec 42 2 (paramMat2DC39 1 0) v u z0 +
              paramMat2DC39 1 0 s z0 z1 * evalFinWordVec 42 2 (paramMat2DC39 0 0) v u z1 := by
          rw [hexp_v 1 0 v s u z0, hs00 1 0, Nat.one_mul, hv1_10]
        refine ⟨by rw [hv0_00, hv0_10]; omega, ?_, ?_⟩
        · rw [hexp_v a b v s u z0, hs00 a b, Nat.one_mul, hs01 a b, hv0_u, hv1_u, hv0_00, hv0_10]
          have hsub : (v s z0 + evalFinWordVec 42 2 (paramMat2DC39 1 0) v u z0 +
              paramMat2DC39 1 0 s z0 z1 * evalFinWordVec 42 2 (paramMat2DC39 0 0) v u z1) -
              (v s z0 + evalFinWordVec 42 2 (paramMat2DC39 0 0) v u z0) =
            (evalFinWordVec 42 2 (paramMat2DC39 1 0) v u z0 -
              evalFinWordVec 42 2 (paramMat2DC39 0 0) v u z0) +
              paramMat2DC39 1 0 s z0 z1 * evalFinWordVec 42 2 (paramMat2DC39 0 0) v u z1 := by omega
          rw [hsub, Nat.mul_add]; ac_rfl
        · rw [hexp_v a b v s u z1, hexp_v 0 0 v s u z1,
              hs_z10 hs_nb a b, hs_z10 hs_nb 0 0, hs11 a b, hv1_u]
          simp only [Nat.zero_mul, Nat.add_zero]
  have hnoA_gen : ∀ (a b : Nat) (w : List (Fin 42)), wordNoAlphaBool w = true ->
      evalFinWordMat 42 2 (paramMat2DC39 a b) w z0 z0 = 1 ∧
      evalFinWordMat 42 2 (paramMat2DC39 a b) w z0 z1 = 0 ∧
      evalFinWordMat 42 2 (paramMat2DC39 a b) w z1 z0 =
        b * evalFinWordMat 42 2 (paramMat2DC39 0 1) w z1 z0 ∧
      evalFinWordMat 42 2 (paramMat2DC39 a b) w z1 z1 =
        evalFinWordMat 42 2 (paramMat2DC39 0 0) w z1 z1 ∧
      ∀ v : Fin 42 -> Fin 2 -> Nat,
        evalFinWordVec 42 2 (paramMat2DC39 0 0) v w z1 ≤
          evalFinWordVec 42 2 (paramMat2DC39 0 1) v w z1 ∧
        evalFinWordVec 42 2 (paramMat2DC39 a b) v w z0 =
          evalFinWordVec 42 2 (paramMat2DC39 0 0) v w z0 ∧
        evalFinWordVec 42 2 (paramMat2DC39 a b) v w z1 =
          evalFinWordVec 42 2 (paramMat2DC39 0 0) v w z1 +
            b * (evalFinWordVec 42 2 (paramMat2DC39 0 1) v w z1 -
                 evalFinWordVec 42 2 (paramMat2DC39 0 0) v w z1) := by
    intro a b w; induction w with
    | nil =>
      intros
      exact ⟨rfl, rfl, by simp [evalFinWordMat, natMatId, z0, z1], rfl,
             fun _ => ⟨Nat.le_refl 0, rfl, by simp [evalFinWordVec]⟩⟩
    | cons s u ih =>
      intro hwa
      unfold wordNoAlphaBool at hwa; simp only [List.all_cons] at hwa
      rcases bool_and_split hwa with ⟨hs_na, hu_na⟩
      rcases ih hu_na with ⟨hm00, hm01, hm10, hm11, hv_u⟩
      rcases hsym s with ⟨hs00, _, hs10, hs11, _, hs_z01⟩
      have h01_z00 : evalFinWordMat 42 2 (paramMat2DC39 0 1) u z0 z0 = 1 := by
        clear hwa ih hm00 hm01 hm10 hm11 hv_u
        induction u with
        | nil => rfl
        | cons x ut ihu =>
          simp only [List.all_cons] at hu_na
          rcases bool_and_split hu_na with ⟨hx_na, hut_na⟩
          rw [hexp_m 0 1 x ut z0 z0, (hsym x).1 0 1, (hsym x).2.2.2.2.2 hx_na 0 1,
              ihu hut_na, Nat.zero_mul, Nat.add_zero, Nat.mul_one]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hexp_m, hs00, hm00, hs_z01 hs_na a b, Nat.zero_mul, Nat.add_zero, Nat.mul_one]
      · rw [hexp_m, hs_z01 hs_na a b, hm01, Nat.mul_zero, Nat.zero_mul]
      · rw [hexp_m a b s u z1 z0, hexp_m 0 1 s u z1 z0,
            hm00, h01_z00, hs10 a b, hm10, hs11 a b, hs11 0 1,
            Nat.mul_one, Nat.mul_one, Nat.mul_add]
        ac_rfl
      · rw [hexp_m a b s u z1 z1, hexp_m 0 0 s u z1 z1,
            hm01, hs11 a b, hm11]
        have h00_z01 : evalFinWordMat 42 2 (paramMat2DC39 0 0) u z0 z1 = 0 := by
          clear hwa ih hm00 hm01 hm10 hm11 hv_u h01_z00
          induction u with
          | nil => rfl
          | cons x ut ihu =>
            simp only [List.all_cons] at hu_na
            rcases bool_and_split hu_na with ⟨hx_na, hut_na⟩
            rw [hexp_m 0 0 x ut z0 z1, (hsym x).2.2.2.2.2 hx_na 0 0, ihu hut_na,
                Nat.mul_zero, Nat.zero_mul]
        rw [h00_z01]
        simp only [Nat.mul_zero, Nat.zero_add]
      · intro v
        rcases hv_u v with ⟨hle_u, hv0_u, hv1_u⟩
        have hv1_00 : evalFinWordVec 42 2 (paramMat2DC39 0 0) v (s :: u) z1 =
            v s z1 + paramMat2DC39 0 0 s z1 z1 * evalFinWordVec 42 2 (paramMat2DC39 0 0) v u z1 := by
          rw [hexp_v 0 0 v s u z1, hs10 0 0]; simp
        have hv0_01 : evalFinWordVec 42 2 (paramMat2DC39 0 1) v u z0 =
            evalFinWordVec 42 2 (paramMat2DC39 0 0) v u z0 := by
          clear hwa ih hm00 hm01 hm10 hm11 hv_u hle_u hv0_u hv1_u h01_z00 hv1_00
          induction u with
          | nil => rfl
          | cons x ut ihu =>
            simp only [List.all_cons] at hu_na
            rcases bool_and_split hu_na with ⟨hx_na, hut_na⟩
            rw [hexp_v 0 1 v x ut z0, hexp_v 0 0 v x ut z0,
                (hsym x).1 0 1, (hsym x).1 0 0,
                (hsym x).2.2.2.2.2 hx_na 0 1, (hsym x).2.2.2.2.2 hx_na 0 0,
                ihu hut_na]
            simp only [Nat.zero_mul, Nat.add_zero]
        have hv1_01 : evalFinWordVec 42 2 (paramMat2DC39 0 1) v (s :: u) z1 =
            v s z1 + paramMat2DC39 0 1 s z1 z0 * evalFinWordVec 42 2 (paramMat2DC39 0 0) v u z0 +
              paramMat2DC39 0 0 s z1 z1 * evalFinWordVec 42 2 (paramMat2DC39 0 1) v u z1 := by
          rw [hexp_v 0 1 v s u z1, hv0_01, hs11 0 1]
        have hm_le := Nat.mul_le_mul_left (paramMat2DC39 0 0 s z1 z1) hle_u
        refine ⟨by rw [hv1_00, hv1_01]; omega, ?_, ?_⟩
        · rw [hexp_v a b v s u z0, hexp_v 0 0 v s u z0,
              hs00 a b, hs00 0 0, hs_z01 hs_na a b, hs_z01 hs_na 0 0, hv0_u]
          simp only [Nat.zero_mul, Nat.add_zero]
        · rw [hexp_v a b v s u z1, hs10 a b, hs11 a b, hv0_u, hv1_u, hv1_00, hv1_01]
          have hsub : (v s z1 + paramMat2DC39 0 1 s z1 z0 * evalFinWordVec 42 2 (paramMat2DC39 0 0) v u z0 +
              paramMat2DC39 0 0 s z1 z1 * evalFinWordVec 42 2 (paramMat2DC39 0 1) v u z1) -
              (v s z1 + paramMat2DC39 0 0 s z1 z1 * evalFinWordVec 42 2 (paramMat2DC39 0 0) v u z1) =
            paramMat2DC39 0 1 s z1 z0 * evalFinWordVec 42 2 (paramMat2DC39 0 0) v u z0 +
              paramMat2DC39 0 0 s z1 z1 *
                (evalFinWordVec 42 2 (paramMat2DC39 0 1) v u z1 -
                 evalFinWordVec 42 2 (paramMat2DC39 0 0) v u z1) := by
            rw [Nat.mul_sub_left_distrib]; omega
          rw [hsub, Nat.mul_add, Nat.mul_add]; ac_rfl
  exact ⟨fun w hw =>
           let ⟨h1, h2, h3, h4, h5⟩ := hnoB_gen alpha beta w hw
           ⟨h1, h2, h3, h4, fun v => ⟨(h5 v).2.1, (h5 v).2.2⟩⟩,
         fun w hw =>
           let ⟨h1, h2, h3, h4, h5⟩ := hnoA_gen alpha beta w hw
           ⟨h1, h2, h3, h4, fun v => ⟨(h5 v).2.1, (h5 v).2.2⟩⟩⟩

set_option maxRecDepth 65536 in
private theorem param_c39_words_and_weak_certs :
    c39FastRules.all (fun r =>
      (wordNoBetaBool r.1 || wordNoAlphaBool r.1) &&
      (wordNoBetaBool r.2 || wordNoAlphaBool r.2) &&
      (if farkasMu1C39 r.1 > 0 then
        wordNoBetaBool r.1 &&
        decide (r.2 = [⟨17, by decide⟩, ⟨37, by decide⟩] ∨ r.2 = [⟨21, by decide⟩, ⟨28, by decide⟩])
       else true)) = true ∧
    c39FastRules.all (fun r => decide (farkasMu0C39 r.1 ≥ 1)) = true ∧
    checkAllWeakMat2DBool 42 (paramMat2DC39 0 0) c39FastRules = true ∧
    checkAllWeakMat2DBool 42 (paramMat2DC39 1 0) c39FastRules = true ∧
    checkAllWeakMat2DBool 42 (paramMat2DC39 0 1) c39FastRules = true ∧
    countStrictMat2DRules 42 (paramMat2DC39 2 3) c39FastRules = 20 := by decide

set_option maxRecDepth 131072 in
private theorem param_c39_farkas_b0_cert :
    checkParamFarkasCoordBool fin2Z0 c39FastRules = true := by decide

set_option maxRecDepth 131072 in
private theorem param_c39_farkas_b1_cert :
    checkParamFarkasCoordBool fin2Z1 c39FastRules = true := by decide

/--
  Theorem W15.1c (`param_mixed_zerodiag_t_coupled_d2_farkas_lock`,
  `zero custom axioms`):
  Infinite 2-Parameter `.T`-Coupled Mixed Zero-Diagonal `d = 2` Cone `paramMat2DC39 α β`
  (`∀ α ≥ 1, ∀ β ≥ 1`) & Parameterized Integral Farkas `(μ_0, α * μ_1)` Zero-Strict-Drop Lock
  Across ALL `v : Fin 42 -> Fin 2 -> Nat` (`Branch P4.3`, `W15_H1`).
-/
theorem param_mixed_zerodiag_t_coupled_d2_farkas_lock :
    let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
    (countStrictMat2DRules 42 (paramMat2DC39 2 3) c39 = 20) ∧
    (∀ alpha beta : Nat, alpha ≥ 1 -> beta ≥ 1 ->
      (∀ r ∈ c39, ∀ i j : Fin 2,
        evalFinWordMat 42 2 (paramMat2DC39 alpha beta) r.1 i j ≥
          evalFinWordMat 42 2 (paramMat2DC39 alpha beta) r.2 i j) ∧
      (∀ v : Fin 42 -> Fin 2 -> Nat,
        (∀ r ∈ c39, ∀ i : Fin 2,
          evalFinWordVec 42 2 (paramMat2DC39 alpha beta) v r.1 i ≥
            evalFinWordVec 42 2 (paramMat2DC39 alpha beta) v r.2 i) ->
        ∀ r ∈ c39,
          evalFinWordVec 42 2 (paramMat2DC39 alpha beta) v r.1 ⟨0, by decide⟩ =
            evalFinWordVec 42 2 (paramMat2DC39 alpha beta) v r.2 ⟨0, by decide⟩)) := by
  dsimp only
  rw [c39_eq_fastRules]
  let c39 := c39FastRules
  let z0 : Fin 2 := fin2Z0
  let z1 : Fin 2 := fin2Z1
  rcases param_c39_words_and_weak_certs with ⟨hwords_b, hmu0_all, hw00_b, hw10_b, hw01_b, hcnt23⟩
  have hfark_b0 := param_c39_farkas_b0_cert
  have hfark_b1 := param_c39_farkas_b1_cert
  have hcheck_snd : ∀ (M : Fin 42 -> Fin 2 -> Fin 2 -> Nat)
      (rs : List (List (Fin 42) × List (Fin 42))),
      checkAllWeakMat2DBool 42 M rs = true ->
      ∀ r ∈ rs, ∀ i j : Fin 2, evalFinWordMat 42 2 M r.1 i j ≥ evalFinWordMat 42 2 M r.2 i j := by
    intro M rs; induction rs with
    | nil => intros _ _ hr; cases hr
    | cons r0 rtl ih =>
      intro hb r hr
      rcases bool_and_split hb with ⟨hw0, htl⟩
      cases hr with
      | head =>
        unfold checkWeakMat2DRuleBool at hw0
        rcases bool_and_split hw0 with ⟨h3, h11⟩
        rcases bool_and_split h3 with ⟨h2, h10⟩
        rcases bool_and_split h2 with ⟨h00, h01⟩
        intro i j
        rcases (by have := i.isLt; omega : i.val = 0 ∨ i.val = 1) with hi | hi <;>
        rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1) with hj | hj
        · rw [show i = z0 from Fin.ext hi, show j = z0 from Fin.ext hj]; exact of_decide_eq_true h00
        · rw [show i = z0 from Fin.ext hi, show j = z1 from Fin.ext hj]; exact of_decide_eq_true h01
        · rw [show i = z1 from Fin.ext hi, show j = z0 from Fin.ext hj]; exact of_decide_eq_true h10
        · rw [show i = z1 from Fin.ext hi, show j = z1 from Fin.ext hj]; exact of_decide_eq_true h11
      | tail _ hm => exact ih htl r hm
  have hw00 := hcheck_snd _ c39 hw00_b
  have hw10 := hcheck_snd _ c39 hw10_b
  have hw01 := hcheck_snd _ c39 hw01_b
  refine ⟨hcnt23, ?_⟩
  intro alpha beta ha1 hb1
  rcases paramMat_noBeta_or_noAlpha alpha beta with ⟨hnoB_ab, hnoA_ab⟩
  rcases paramMat_noBeta_or_noAlpha 1 0 with ⟨hnoB_10, hnoA_10⟩
  rcases paramMat_noBeta_or_noAlpha 0 1 with ⟨hnoB_01, hnoA_01⟩
  have hmat_ev : ∀ w : List (Fin 42),
      (wordNoBetaBool w || wordNoAlphaBool w) = true ->
      evalFinWordMat 42 2 (paramMat2DC39 alpha beta) w z0 z0 = 1 ∧
      evalFinWordMat 42 2 (paramMat2DC39 alpha beta) w z0 z1 =
        alpha * evalFinWordMat 42 2 (paramMat2DC39 1 0) w z0 z1 ∧
      evalFinWordMat 42 2 (paramMat2DC39 alpha beta) w z1 z0 =
        beta * evalFinWordMat 42 2 (paramMat2DC39 0 1) w z1 z0 ∧
      evalFinWordMat 42 2 (paramMat2DC39 alpha beta) w z1 z1 =
        evalFinWordMat 42 2 (paramMat2DC39 0 0) w z1 z1 := by
    intro w hwa
    cases hb : wordNoBetaBool w with
    | true =>
      rcases hnoB_ab w hb with ⟨e1, e2, e3, e4, _⟩
      have e01 : evalFinWordMat 42 2 (paramMat2DC39 0 1) w z1 z0 = 0 := (hnoB_01 w hb).2.2.1
      exact ⟨e1, e2, by rw [e3, e01, Nat.mul_zero], e4⟩
    | false =>
      rw [hb, Bool.false_or] at hwa
      rcases hnoA_ab w hwa with ⟨e1, e2, e3, e4, _⟩
      have e10 : evalFinWordMat 42 2 (paramMat2DC39 1 0) w z0 z1 = 0 := (hnoA_10 w hwa).2.1
      exact ⟨e1, by rw [e2, e10, Nat.mul_zero], e3, e4⟩
  have hweak_ab : ∀ r ∈ c39, ∀ i j : Fin 2,
      evalFinWordMat 42 2 (paramMat2DC39 alpha beta) r.1 i j ≥
        evalFinWordMat 42 2 (paramMat2DC39 alpha beta) r.2 i j := by
    intro r hr i j
    have hwr := List.all_eq_true.mp hwords_b r hr
    rcases bool_and_split hwr with ⟨hw12, _⟩
    rcases bool_and_split hw12 with ⟨hw1, hw2⟩
    rcases hmat_ev r.1 hw1 with ⟨l00, l01, l10, l11⟩
    rcases hmat_ev r.2 hw2 with ⟨r00, r01, r10, r11⟩
    rcases (by have := i.isLt; omega : i.val = 0 ∨ i.val = 1) with hi | hi <;>
    rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1) with hj | hj
    · rw [show i = z0 from Fin.ext hi, show j = z0 from Fin.ext hj, l00, r00]; exact Nat.le_refl 1
    · rw [show i = z0 from Fin.ext hi, show j = z1 from Fin.ext hj, l01, r01]
      exact Nat.mul_le_mul_left alpha (hw10 r hr z0 z1)
    · rw [show i = z1 from Fin.ext hi, show j = z0 from Fin.ext hj, l10, r10]
      exact Nat.mul_le_mul_left beta (hw01 r hr z1 z0)
    · rw [show i = z1 from Fin.ext hi, show j = z1 from Fin.ext hj, l11, r11]
      exact hw00 r hr z1 z1
  refine ⟨hweak_ab, ?_⟩
  -- Parameterized Farkas lock: first show `farkasParamWeightedVecSum42 alpha beta v c39` equals
  -- `farkasParamWeightedVecSum42 alpha 0 v c39` and is affine in `alpha`:
  have hfark_aff : ∀ (v : Fin 42 -> Fin 2 -> Nat)
      (rs : List (List (Fin 42) × List (Fin 42))),
      rs.all (fun r =>
        (wordNoBetaBool r.1 || wordNoAlphaBool r.1) &&
        (wordNoBetaBool r.2 || wordNoAlphaBool r.2) &&
        (if farkasMu1C39 r.1 > 0 then
          wordNoBetaBool r.1 &&
          decide (r.2 = [⟨17, by decide⟩, ⟨37, by decide⟩] ∨ r.2 = [⟨21, by decide⟩, ⟨28, by decide⟩])
         else true)) = true ->
      let s0 := farkasParamWeightedVecSum42 0 0 v rs
      let s1 := farkasParamWeightedVecSum42 1 0 v rs
      let sab := farkasParamWeightedVecSum42 alpha beta v rs
      s0.1 ≤ s1.1 ∧ s0.2 ≤ s1.2 ∧
      sab.1 = s0.1 + alpha * (s1.1 - s0.1) ∧
      sab.2 = s0.2 + alpha * (s1.2 - s0.2) := by
    intro v rs; induction rs with
    | nil =>
      intros
      exact ⟨Nat.le_refl 0, Nat.le_refl 0,
             by change 0 = 0 + alpha * (0 - 0); omega,
             by change 0 = 0 + alpha * (0 - 0); omega⟩
    | cons r0 rtl ih =>
      rcases r0 with ⟨l0, r0_w⟩
      intro hall; simp only [List.all_cons] at hall
      rcases bool_and_split hall with ⟨hcur, htl_all⟩
      rcases ih htl_all with ⟨hle_t1, hle_t2, htl1, htl2⟩
      rcases bool_and_split hcur with ⟨hlr_b, hmu1_c⟩
      rcases bool_and_split hlr_b with ⟨hl_ba, hr_ba⟩
      have hv0_aff : ∀ w : List (Fin 42), (wordNoBetaBool w || wordNoAlphaBool w) = true ->
          evalFinWordVec 42 2 (paramMat2DC39 0 0) v w z0 ≤
            evalFinWordVec 42 2 (paramMat2DC39 1 0) v w z0 ∧
          evalFinWordVec 42 2 (paramMat2DC39 alpha beta) v w z0 =
            evalFinWordVec 42 2 (paramMat2DC39 0 0) v w z0 +
              alpha * (evalFinWordVec 42 2 (paramMat2DC39 1 0) v w z0 -
                       evalFinWordVec 42 2 (paramMat2DC39 0 0) v w z0) := by
        intro w hwa
        cases hb : wordNoBetaBool w with
        | true =>
          have e_ab := ((hnoB_ab w hb).2.2.2.2 v).1
          -- Monotonicity of `paramMat2DC39 0 0` vs `1 0` on `z0`:
          have hmono_w : ∀ u : List (Fin 42), ∀ j : Fin 2,
              evalFinWordVec 42 2 (paramMat2DC39 0 0) v u j ≤
                evalFinWordVec 42 2 (paramMat2DC39 1 0) v u j := by
            intro u; induction u with
            | nil => intro _; exact Nat.le_refl 0
            | cons x ut ihu =>
              intro j
              change v x j + ((0 + paramMat2DC39 0 0 x j z0 * _) + paramMat2DC39 0 0 x j z1 * _) ≤
                v x j + ((0 + paramMat2DC39 1 0 x j z0 * _) + paramMat2DC39 1 0 x j z1 * _)
              have hle0 := ihu z0
              have hle1 := ihu z1
              have hm0 : paramMat2DC39 0 0 x j z0 ≤ paramMat2DC39 1 0 x j z0 := by
                revert x j; decide
              have hm1 : paramMat2DC39 0 0 x j z1 ≤ paramMat2DC39 1 0 x j z1 := by
                revert x j; decide
              have p0 := Nat.mul_le_mul hm0 hle0
              have p1 := Nat.mul_le_mul hm1 hle1
              exact Nat.add_le_add_left (Nat.add_le_add (by rw [Nat.zero_add, Nat.zero_add]; exact p0) p1) (v x j)
          exact ⟨hmono_w w z0, e_ab⟩
        | false =>
          rw [hb, Bool.false_or] at hwa
          have e_ab := ((hnoA_ab w hwa).2.2.2.2 v).1
          have e_10 := ((hnoA_10 w hwa).2.2.2.2 v).1
          rw [e_ab, e_10, Nat.sub_self, Nat.mul_zero, Nat.add_zero]
          exact ⟨Nat.le_refl _, rfl⟩
      rcases hv0_aff l0 hl_ba with ⟨hle_l0, hl0_ab⟩
      rcases hv0_aff r0_w hr_ba with ⟨hle_r0, hr0_ab⟩
      have hm1_term :
          (alpha * farkasMu1C39 l0) * evalFinWordVec 42 2 (paramMat2DC39 alpha beta) v l0 z1 =
            alpha * (farkasMu1C39 l0 * evalFinWordVec 42 2 (paramMat2DC39 1 0) v l0 z1) ∧
          (alpha * farkasMu1C39 l0) * evalFinWordVec 42 2 (paramMat2DC39 alpha beta) v r0_w z1 =
            alpha * (farkasMu1C39 l0 * evalFinWordVec 42 2 (paramMat2DC39 1 0) v r0_w z1) := by
        by_cases hpos : farkasMu1C39 l0 > 0
        · simp only [hpos, ite_true] at hmu1_c
          rcases bool_and_split hmu1_c with ⟨hl_nb, hr_two⟩
          have hl1_ab := ((hnoB_ab l0 hl_nb).2.2.2.2 v).2
          have hl1_10 := ((hnoB_10 l0 hl_nb).2.2.2.2 v).2
          have hr1_eq : evalFinWordVec 42 2 (paramMat2DC39 alpha beta) v r0_w z1 =
              evalFinWordVec 42 2 (paramMat2DC39 1 0) v r0_w z1 := by
            rcases of_decide_eq_true hr_two with rfl | rfl
            · have hnb : wordNoBetaBool [⟨17, by decide⟩, ⟨37, by decide⟩] = true := by decide
              rw [((hnoB_ab _ hnb).2.2.2.2 v).2, ((hnoB_10 _ hnb).2.2.2.2 v).2]
            · change v ⟨21, by decide⟩ z1 +
                  ((0 + paramMat2DC39 alpha beta ⟨21, by decide⟩ z1 z0 * _) +
                   paramMat2DC39 alpha beta ⟨21, by decide⟩ z1 z1 * _) =
                v ⟨21, by decide⟩ z1 +
                  ((0 + paramMat2DC39 1 0 ⟨21, by decide⟩ z1 z0 * _) +
                   paramMat2DC39 1 0 ⟨21, by decide⟩ z1 z1 * _)
              have z10_a : paramMat2DC39 alpha beta ⟨21, by decide⟩ z1 z0 = 0 := rfl
              have z11_a : paramMat2DC39 alpha beta ⟨21, by decide⟩ z1 z1 = 0 := rfl
              have z10_1 : paramMat2DC39 1 0 ⟨21, by decide⟩ z1 z0 = 0 := rfl
              have z11_1 : paramMat2DC39 1 0 ⟨21, by decide⟩ z1 z1 = 0 := rfl
              rw [z10_a, z11_a, z10_1, z11_1]; simp
          rw [hl1_ab, hl1_10, hr1_eq]
          exact ⟨Nat.mul_assoc _ _ _, Nat.mul_assoc _ _ _⟩
        · have hz : farkasMu1C39 l0 = 0 := by omega
          simp [hz]
      dsimp only [farkasParamWeightedVecSum42] at hle_t1 hle_t2 htl1 htl2 ⊢
      simp only [farkasParamVecLhs42, farkasParamVecRhs42, Nat.zero_mul, Nat.one_mul, Nat.add_zero]
      dsimp only [z0, z1] at hl0_ab hr0_ab hm1_term hle_l0 hle_r0
      rw [hl0_ab, hr0_ab, hm1_term.1, hm1_term.2, htl1, htl2]
      have hm_l0 := Nat.mul_le_mul_left (farkasMu0C39 l0) hle_l0
      have hm_r0 := Nat.mul_le_mul_left (farkasMu0C39 l0) hle_r0
      refine ⟨by omega, by omega, ?_, ?_⟩
      · have hs1_sub :
            (farkasMu0C39 l0 * evalFinWordVec 42 2 (paramMat2DC39 1 0) v l0 fin2Z0 +
             farkasMu1C39 l0 * evalFinWordVec 42 2 (paramMat2DC39 1 0) v l0 fin2Z1 +
             farkasParamVecLhs42 1 0 v rtl) -
            (farkasMu0C39 l0 * evalFinWordVec 42 2 (paramMat2DC39 0 0) v l0 fin2Z0 +
             farkasParamVecLhs42 0 0 v rtl) =
            farkasMu0C39 l0 *
              (evalFinWordVec 42 2 (paramMat2DC39 1 0) v l0 fin2Z0 -
               evalFinWordVec 42 2 (paramMat2DC39 0 0) v l0 fin2Z0) +
            farkasMu1C39 l0 * evalFinWordVec 42 2 (paramMat2DC39 1 0) v l0 fin2Z1 +
            (farkasParamVecLhs42 1 0 v rtl -
             farkasParamVecLhs42 0 0 v rtl) := by
          rw [Nat.mul_sub_left_distrib]; omega
        rw [hs1_sub, Nat.mul_add (farkasMu0C39 l0), Nat.mul_add alpha, Nat.mul_add alpha,
            ← Nat.mul_assoc alpha (farkasMu0C39 l0), Nat.mul_comm alpha (farkasMu0C39 l0),
            Nat.mul_assoc (farkasMu0C39 l0) alpha]
        omega
      · have hs2_sub :
            (farkasMu0C39 l0 * evalFinWordVec 42 2 (paramMat2DC39 1 0) v r0_w fin2Z0 +
             farkasMu1C39 l0 * evalFinWordVec 42 2 (paramMat2DC39 1 0) v r0_w fin2Z1 +
             farkasParamVecRhs42 1 0 v rtl) -
            (farkasMu0C39 l0 * evalFinWordVec 42 2 (paramMat2DC39 0 0) v r0_w fin2Z0 +
             farkasParamVecRhs42 0 0 v rtl) =
            farkasMu0C39 l0 *
              (evalFinWordVec 42 2 (paramMat2DC39 1 0) v r0_w fin2Z0 -
               evalFinWordVec 42 2 (paramMat2DC39 0 0) v r0_w fin2Z0) +
            farkasMu1C39 l0 * evalFinWordVec 42 2 (paramMat2DC39 1 0) v r0_w fin2Z1 +
            (farkasParamVecRhs42 1 0 v rtl -
             farkasParamVecRhs42 0 0 v rtl) := by
          rw [Nat.mul_sub_left_distrib]; omega
        rw [hs2_sub, Nat.mul_add (farkasMu0C39 l0), Nat.mul_add alpha, Nat.mul_add alpha,
            ← Nat.mul_assoc alpha (farkasMu0C39 l0), Nat.mul_comm alpha (farkasMu0C39 l0),
            Nat.mul_assoc (farkasMu0C39 l0) alpha]
        omega
  -- Basis inequalities at `(0, 0)` and slope `(1, 0) - (0, 0)` imply `(alpha, beta)` basis inequalities:
  have hmu0_pos : ∀ r ∈ c39, farkasMu0C39 r.1 ≥ 1 :=
    fun r hr => of_decide_eq_true (List.all_eq_true.mp hmu0_all r hr)
  have hcoord_ab : ∀ (j0 : Fin 2), checkParamFarkasCoordBool j0 c39 = true ->
      ∀ s0 : Fin 42,
        let p := farkasParamWeightedVecSum42 alpha beta (basisVec2D 42 s0 j0) c39
        p.1 ≤ p.2 := by
    intro j0 hchk
    unfold checkParamFarkasCoordBool at hchk
    have hlp : ∀ n : Nat, n ≤ 42 -> checkParamFarkasCoordBool.loop j0 c39 n = true ->
        ∀ k : Nat, k < n -> (hk : k < 42) ->
          let p := farkasParamWeightedVecSum42 alpha beta (basisVec2D 42 ⟨k, hk⟩ j0) c39
          p.1 ≤ p.2 := by
      intro n; induction n with
      | zero => intros _ _ _ hlt; omega
      | succ n' ih =>
        intro hn_le hn k hkn hk42
        have hn42 : n' < 42 := hn_le
        unfold checkParamFarkasCoordBool.loop at hn
        simp only [hn42, dite_true] at hn
        rcases bool_and_split hn with ⟨hc, hprev⟩
        by_cases hkeq : k = n'
        · subst hkeq
          rcases hfark_aff (basisVec2D 42 ⟨k, hk42⟩ j0) c39 hwords_b with ⟨_, _, ha1, ha2⟩
          dsimp only [farkasParamWeightedVecSum42] at ha1 ha2 ⊢
          rw [ha1, ha2]
          rcases of_decide_eq_true hc with ⟨hb0, hsl⟩
          have hm := Nat.mul_le_mul_left alpha hsl
          omega
        · exact ih (Nat.le_of_lt hn_le) hprev k (by omega) hk42
    intro s0; exact hlp 42 (Nat.le_refl 42) hchk s0.val s0.isLt s0.isLt
  have hbasis_ab : ∀ s0 : Fin 42,
      let p0 := farkasParamWeightedVecSum42 alpha beta (basisVec2D 42 s0 z0) c39
      let p1 := farkasParamWeightedVecSum42 alpha beta (basisVec2D 42 s0 z1) c39
      p0.1 ≤ p0.2 ∧ p1.1 ≤ p1.2 :=
    fun s0 => ⟨hcoord_ab fin2Z0 hfark_b0 s0, hcoord_ab fin2Z1 hfark_b1 s0⟩
  -- Linearity of `evalFinWordVec 42 2 M v` in `v`:
  intro v hv_weak
  have hv_lin : ∀ (w : List (Fin 42)) (i : Fin 2),
      evalFinWordVec 42 2 (paramMat2DC39 alpha beta) v w i =
        natSumPrefix 42 (fun s0 =>
          v s0 z0 * evalFinWordVec 42 2 (paramMat2DC39 alpha beta) (basisVec2D 42 s0 z0) w i +
          v s0 z1 * evalFinWordVec 42 2 (paramMat2DC39 alpha beta) (basisVec2D 42 s0 z1) w i) 42 := by
    let M := paramMat2DC39 alpha beta
    have hsum_add : ∀ (f g : Fin 42 -> Nat) (m : Nat),
        natSumPrefix 42 (fun s => f s + g s) m = natSumPrefix 42 f m + natSumPrefix 42 g m := by
      intro f g m; induction m with
      | zero => rfl
      | succ m' ih => simp only [natSumPrefix]; by_cases hm : m' < 42 <;> simp [hm, ih]; omega
    have hsum_mul : ∀ (c : Nat) (f : Fin 42 -> Nat) (m : Nat),
        c * natSumPrefix 42 f m = natSumPrefix 42 (fun s => c * f s) m := by
      intro c f m; induction m with
      | zero => simp [natSumPrefix]
      | succ m' ih => simp only [natSumPrefix]; by_cases hm : m' < 42 <;> simp [hm, Nat.mul_add, ih]
    have hdelta : ∀ (s : Fin 42) (j : Fin 2),
        v s j = natSumPrefix 42 (fun s0 =>
          v s0 z0 * basisVec2D 42 s0 z0 s j + v s0 z1 * basisVec2D 42 s0 z1 s j) 42 := by
      intro s j
      have hst : ∀ m : Nat, m ≤ 42 ->
          natSumPrefix 42 (fun s0 =>
            v s0 z0 * basisVec2D 42 s0 z0 s j + v s0 z1 * basisVec2D 42 s0 z1 s j) m =
            if s.val < m then v s j else 0 := by
        intro m hm; induction m with
        | zero => simp [natSumPrefix]
        | succ m' ih =>
          have hm_lt : m' < 42 := hm
          simp only [natSumPrefix, hm_lt, dite_true, ih (Nat.le_of_lt hm)]
          by_cases heq : s.val = m'
          · have hsf : (⟨m', hm_lt⟩ : Fin 42) = s := Fin.ext heq.symm
            rw [hsf, ite_false_of_w10 (by omega : ¬ (s.val < m')),
                ite_true_of_w10 (by omega : s.val < m' + 1)]
            rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1) with hj | hj
            · rw [show j = z0 from Fin.ext hj]; simp [basisVec2D, z0, z1]
            · rw [show j = z1 from Fin.ext hj]; simp [basisVec2D, z0, z1]
          · have hne_b : (s.val == m') = false := beq_false_of_ne heq
            have hb0 : basisVec2D 42 ⟨m', hm_lt⟩ z0 s j = 0 := by simp [basisVec2D, hne_b]
            have hb1 : basisVec2D 42 ⟨m', hm_lt⟩ z1 s j = 0 := by simp [basisVec2D, hne_b]
            rw [hb0, hb1, Nat.mul_zero, Nat.mul_zero, Nat.add_zero, Nat.add_zero]
            by_cases hlt : s.val < m'
            · rw [ite_true_of_w10 hlt, ite_true_of_w10 (by omega)]
            · rw [ite_false_of_w10 hlt, ite_false_of_w10 (by omega)]
      rw [hst 42 (Nat.le_refl 42), ite_true_of_w10 s.isLt]
    intro w; induction w with
    | nil =>
      intro _
      have hz : ∀ m : Nat, natSumPrefix 42 (fun _ => (0 : Nat)) m = 0 := by
        intro m; induction m with
        | zero => rfl
        | succ m' ihm => simp only [natSumPrefix]; by_cases hm : m' < 42 <;> simp [hm, ihm]
      simpa [evalFinWordVec] using (hz 42).symm
    | cons s rest ih =>
      intro i
      change v s i + ((0 + M s i z0 * evalFinWordVec 42 2 M v rest z0) +
        M s i z1 * evalFinWordVec 42 2 M v rest z1) = _
      rw [Nat.zero_add, ih z0, ih z1]
      conv => lhs; lhs; rw [hdelta s i]
      rw [hsum_mul (M s i z0), hsum_mul (M s i z1), ← hsum_add, ← hsum_add]
      have hcg : ∀ (f1 f2 : Fin 42 -> Nat), (∀ x, f1 x = f2 x) ->
          ∀ m : Nat, natSumPrefix 42 f1 m = natSumPrefix 42 f2 m := by
        intro f1 f2 hf m; induction m with
        | zero => rfl
        | succ m' ihm => simp only [natSumPrefix]; by_cases hm : m' < 42 <;> simp [hm, ihm, hf]
      exact hcg _ _ (fun s0 => by
        change _ = v s0 z0 * (basisVec2D 42 s0 z0 s i +
          ((0 + M s i z0 * evalFinWordVec 42 2 M (basisVec2D 42 s0 z0) rest z0) +
           M s i z1 * evalFinWordVec 42 2 M (basisVec2D 42 s0 z0) rest z1)) +
          v s0 z1 * (basisVec2D 42 s0 z1 s i +
          ((0 + M s i z0 * evalFinWordVec 42 2 M (basisVec2D 42 s0 z1) rest z0) +
           M s i z1 * evalFinWordVec 42 2 M (basisVec2D 42 s0 z1) rest z1))
        simp only [Nat.zero_add, Nat.mul_add]; ac_rfl) 42
  have hsum_add42 : ∀ (f g : Fin 42 -> Nat) (m : Nat),
      natSumPrefix 42 (fun s => f s + g s) m = natSumPrefix 42 f m + natSumPrefix 42 g m := by
    intro f g m; induction m with
    | zero => rfl
    | succ m' ih => simp only [natSumPrefix]; by_cases hm : m' < 42 <;> simp [hm, ih]; omega
  have hsum_mul42 : ∀ (c : Nat) (f : Fin 42 -> Nat) (m : Nat),
      c * natSumPrefix 42 f m = natSumPrefix 42 (fun s => c * f s) m := by
    intro c f m; induction m with
    | zero => simp [natSumPrefix]
    | succ m' ih => simp only [natSumPrefix]; by_cases hm : m' < 42 <;> simp [hm, Nat.mul_add, ih]
  have hfark_lin : ∀ rs : List (List (Fin 42) × List (Fin 42)),
      (farkasParamWeightedVecSum42 alpha beta v rs).1 =
        natSumPrefix 42 (fun s0 =>
          v s0 z0 * (farkasParamWeightedVecSum42 alpha beta (basisVec2D 42 s0 z0) rs).1 +
          v s0 z1 * (farkasParamWeightedVecSum42 alpha beta (basisVec2D 42 s0 z1) rs).1) 42 ∧
      (farkasParamWeightedVecSum42 alpha beta v rs).2 =
        natSumPrefix 42 (fun s0 =>
          v s0 z0 * (farkasParamWeightedVecSum42 alpha beta (basisVec2D 42 s0 z0) rs).2 +
          v s0 z1 * (farkasParamWeightedVecSum42 alpha beta (basisVec2D 42 s0 z1) rs).2) 42 := by
    intro rs; induction rs with
    | nil =>
      have hz : ∀ m : Nat, natSumPrefix 42 (fun _ => (0 : Nat)) m = 0 := by
        intro m; induction m with
        | zero => rfl
        | succ m' ihm => simp only [natSumPrefix]; by_cases hm : m' < 42 <;> simp [hm, ihm]
      exact ⟨by simpa [farkasParamWeightedVecSum42, farkasParamVecLhs42] using (hz 42).symm,
             by simpa [farkasParamWeightedVecSum42, farkasParamVecRhs42] using (hz 42).symm⟩
    | cons r0 tl ih =>
      rcases r0 with ⟨l0, r0_w⟩
      dsimp only [farkasParamWeightedVecSum42] at ih ⊢
      simp only [farkasParamVecLhs42, farkasParamVecRhs42]
      rw [hv_lin l0 z0, hv_lin l0 z1, hv_lin r0_w z0, hv_lin r0_w z1, ih.1, ih.2,
          hsum_mul42 (farkasMu0C39 l0), hsum_mul42 (alpha * farkasMu1C39 l0),
          hsum_mul42 (farkasMu0C39 l0), hsum_mul42 (alpha * farkasMu1C39 l0),
          ← hsum_add42, ← hsum_add42, ← hsum_add42, ← hsum_add42]
      have hcg : ∀ (f1 f2 : Fin 42 -> Nat), (∀ s, f1 s = f2 s) ->
          ∀ m : Nat, natSumPrefix 42 f1 m = natSumPrefix 42 f2 m := by
        intro f1 f2 hf m; induction m with
        | zero => rfl
        | succ m' ihm => simp only [natSumPrefix]; by_cases hm : m' < 42 <;> simp [hm, ihm, hf]
      exact ⟨hcg _ _ (fun _ => by simp only [Nat.mul_add]; ac_rfl) 42,
             hcg _ _ (fun _ => by simp only [Nat.mul_add]; ac_rfl) 42⟩
  have hsum_le_v :
      (farkasParamWeightedVecSum42 alpha beta v c39).1 ≤
        (farkasParamWeightedVecSum42 alpha beta v c39).2 := by
    rcases hfark_lin c39 with ⟨h1, h2⟩
    rw [h1, h2]
    exact natSumPrefix_mono_w5 42 _ _ (fun s0 => by
      rcases hbasis_ab s0 with ⟨hb0, hb1_s⟩
      have m0 := Nat.mul_le_mul_left (v s0 z0) hb0
      have m1 := Nat.mul_le_mul_left (v s0 z1) hb1_s
      omega) 42
  have hsqueeze : ∀ rs : List (List (Fin 42) × List (Fin 42)),
      (∀ r ∈ rs, farkasMu0C39 r.1 ≥ 1) ->
      (∀ r ∈ rs, ∀ i : Fin 2,
        evalFinWordVec 42 2 (paramMat2DC39 alpha beta) v r.1 i ≥
          evalFinWordVec 42 2 (paramMat2DC39 alpha beta) v r.2 i) ->
      (farkasParamWeightedVecSum42 alpha beta v rs).1 ≥
        (farkasParamWeightedVecSum42 alpha beta v rs).2 ∧
      ((farkasParamWeightedVecSum42 alpha beta v rs).1 =
        (farkasParamWeightedVecSum42 alpha beta v rs).2 ->
        ∀ r ∈ rs,
          evalFinWordVec 42 2 (paramMat2DC39 alpha beta) v r.1 z0 =
            evalFinWordVec 42 2 (paramMat2DC39 alpha beta) v r.2 z0) := by
    intro rs; induction rs with
    | nil => intros; exact ⟨Nat.le_refl 0, fun _ _ hr => by cases hr⟩
    | cons r0 tl ih =>
      rcases r0 with ⟨l0, r0_w⟩
      intro hm_pos hw_rs
      rcases ih (fun r hr => hm_pos r (List.mem_cons_of_mem _ hr))
                (fun r hr => hw_rs r (List.mem_cons_of_mem _ hr)) with ⟨htl_ge, htl_eq⟩
      have hm0_ge1 : farkasMu0C39 l0 ≥ 1 := hm_pos (l0, r0_w) List.mem_cons_self
      have hm0_le := Nat.mul_le_mul_left (farkasMu0C39 l0) (hw_rs (l0, r0_w) List.mem_cons_self fin2Z0)
      have hm1_le := Nat.mul_le_mul_left (alpha * farkasMu1C39 l0) (hw_rs (l0, r0_w) List.mem_cons_self fin2Z1)
      dsimp only [farkasParamWeightedVecSum42] at htl_ge htl_eq ⊢
      simp only [farkasParamVecLhs42, farkasParamVecRhs42]
      dsimp only [z0, z1] at hm0_le hm1_le ⊢
      refine ⟨by omega, fun heq_tot r hr_m => ?_⟩
      have heq_m0 : farkasMu0C39 l0 * evalFinWordVec 42 2 (paramMat2DC39 alpha beta) v l0 fin2Z0 =
          farkasMu0C39 l0 * evalFinWordVec 42 2 (paramMat2DC39 alpha beta) v r0_w fin2Z0 := by omega
      have heq_tl : farkasParamVecLhs42 alpha beta v tl =
          farkasParamVecRhs42 alpha beta v tl := by omega
      cases hr_m with
      | head => exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < farkasMu0C39 l0) heq_m0
      | tail _ htl => exact htl_eq heq_tl r htl
  rcases hsqueeze c39 hmu0_pos hv_weak with ⟨hsum_ge_v, himp_eq⟩
  exact himp_eq (Nat.le_antisymm hsum_le_v hsum_ge_v)

-- ----------------------------------------------------------------------------
-- Section 1D: Unconditional `1..10`-Cycle Freedom Across ALL `DP2` Words,
--             `M1` `6305/1631` Carry Separation, & 2-Block `.R`-Carrying Locks
-- ----------------------------------------------------------------------------

private theorem dp2ShiftSum_append_w15 :
    ∀ (xs ys : List Nat), dp2ShiftSum (xs ++ ys) = dp2ShiftSum xs + dp2ShiftSum ys
  | [], _ => by simp [dp2ShiftSum]
  | a :: xs, ys => by simp only [List.cons_append, dp2ShiftSum, dp2ShiftSum_append_w15 xs ys]; omega

private theorem dp2IterCarry_append_w15 :
    ∀ (xs ys : List Nat),
      dp2IterCarry (xs ++ ys) =
        3 ^ ys.length * dp2IterCarry xs + 2 ^ dp2ShiftSum xs * dp2IterCarry ys
  | [], ys => by simp [dp2IterCarry, dp2ShiftSum]
  | a :: xs, ys => by
    simp only [List.cons_append, dp2IterCarry, List.length_append, dp2ShiftSum,
               dp2IterCarry_append_w15 xs ys]
    rw [Nat.pow_add 3 xs.length ys.length, Nat.mul_add (3 ^ ys.length),
        Nat.mul_add (2 ^ a), Nat.pow_add 2 a (dp2ShiftSum xs)]
    ac_rfl

private theorem dp2AnnotatedChain_split_w15 :
    ∀ (xs ys : List Nat) (u0 u2 : List MixedSRSSym),
      dp2AnnotatedChain u0 (xs ++ ys) u2 ->
      ∃ u1 : List MixedSRSSym, dp2AnnotatedChain u0 xs u1 ∧ dp2AnnotatedChain u1 ys u2
  | [], _, u0, u2, h => ⟨u0, rfl, h⟩
  | a :: xs, ys, u0, u2, ⟨ha1, w, hstep, hsyr, htl⟩ => by
    rcases dp2AnnotatedChain_split_w15 xs ys w u2 htl with ⟨u1, h1, h2⟩
    exact ⟨u1, ⟨ha1, w, hstep, hsyr, h1⟩, h2⟩

private def syrStepW15 (n : Nat) : Nat := core2 (3 * n + 1)

private def syrIterW15 : Nat -> Nat -> Nat
  | 0, n => n
  | k + 1, n => syrIterW15 k (syrStepW15 n)

private theorem syrIterW15_add :
    ∀ (a b n : Nat), syrIterW15 (a + b) n = syrIterW15 b (syrIterW15 a n)
  | 0, _, _ => by rw [Nat.zero_add]; rfl
  | a + 1, b, n => by rw [Nat.succ_add]; exact syrIterW15_add a b (syrStepW15 n)

set_option maxRecDepth 65536 in
private theorem no_small_odd_syr_cycles_6_to_10 :
    ∀ (r : Fin 11) (k : Fin 15),
      6 ≤ r.val -> syrIterW15 r.val (2 * k.val + 3) ≠ 2 * k.val + 3 := by
  decide

private theorem dp2AnnotatedChain_syr_and_ge33_bound :
    ∀ (shifts : List Nat) (u0 ur : List MixedSRSSym),
      dp2AnnotatedChain u0 shifts ur ->
      dp2GlobalOddVal ur = syrIterW15 shifts.length (dp2GlobalOddVal u0) ∧
      ((∃ n : Nat, 3 ≤ n ∧ n ≤ 31 ∧ n % 2 = 1 ∧
          ∃ i : Nat, i ≤ shifts.length ∧
            syrIterW15 i (dp2GlobalOddVal u0) = n ∧
            dp2GlobalOddVal ur = syrIterW15 (shifts.length - i) n) ∨
       33 ^ shifts.length * 2 ^ dp2ShiftSum shifts * dp2GlobalOddVal ur ≤
         100 ^ shifts.length * dp2GlobalOddVal u0)
  | [], u0, ur, heq => by
    subst heq
    exact ⟨rfl, Or.inr (by simp [dp2ShiftSum])⟩
  | a :: rest, u0, ur, ⟨_, w, _, hsyr_step, htl⟩ => by
    have hNw_pos : dp2GlobalOddVal w > 0 := by unfold dp2GlobalOddVal; omega
    have hNw_odd : dp2GlobalOddVal w % 2 = 1 := by unfold dp2GlobalOddVal; omega
    have hNu_ge3 : dp2GlobalOddVal u0 ≥ 3 := by unfold dp2GlobalOddVal; omega
    have hNu_odd : dp2GlobalOddVal u0 % 2 = 1 := by unfold dp2GlobalOddVal; omega
    have hsyr_eq : syrStepW15 (dp2GlobalOddVal u0) = dp2GlobalOddVal w := by
      unfold syrStepW15
      rw [← hsyr_step, core2_pow2_mul a (dp2GlobalOddVal w) hNw_pos hNw_odd]
    rcases dp2AnnotatedChain_syr_and_ge33_bound rest w ur htl with ⟨ih_syr, ih_disj⟩
    have hiter_tot : dp2GlobalOddVal ur = syrIterW15 (rest.length + 1) (dp2GlobalOddVal u0) := by
      simp only [syrIterW15, hsyr_eq]; exact ih_syr
    simp only [List.length_cons, dp2ShiftSum]
    refine ⟨hiter_tot, ?_⟩
    by_cases hle31 : dp2GlobalOddVal u0 ≤ 31
    · left
      exact ⟨dp2GlobalOddVal u0, hNu_ge3, hle31, hNu_odd, 0, Nat.zero_le _, rfl, hiter_tot⟩
    · rcases ih_disj with ⟨n, hn3, hn31, hno, i, hi_le, hi_eq, hur_eq⟩ | ih_ge33
      · left
        refine ⟨n, hn3, hn31, hno, i + 1, Nat.succ_le_succ hi_le, ?_, ?_⟩
        · simp only [syrIterW15, hsyr_eq]; exact hi_eq
        · rw [Nat.succ_sub_succ]; exact hur_eq
      · right
        have hstep33 : 33 * (2 ^ a * dp2GlobalOddVal w) ≤ 100 * dp2GlobalOddVal u0 := by
          rw [hsyr_step]; omega
        rw [Nat.pow_succ 33 rest.length, Nat.pow_add 2 a (dp2ShiftSum rest),
            Nat.pow_succ 100 rest.length]
        calc
          ((33 ^ rest.length * 33) * (2 ^ a * 2 ^ dp2ShiftSum rest)) * dp2GlobalOddVal ur
              = 2 ^ a * (33 * (33 ^ rest.length * 2 ^ dp2ShiftSum rest * dp2GlobalOddVal ur)) := by ac_rfl
          _ ≤ 2 ^ a * (33 * (100 ^ rest.length * dp2GlobalOddVal w)) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 33 ih_ge33)
          _ = 100 ^ rest.length * (33 * (2 ^ a * dp2GlobalOddVal w)) := by ac_rfl
          _ ≤ 100 ^ rest.length * (100 * dp2GlobalOddVal u0) :=
                Nat.mul_le_mul_left _ hstep33
          _ = (100 ^ rest.length * 100) * dp2GlobalOddVal u0 := by ac_rfl

/--
  Theorem W15.1d (`leftAnchoredDP2_no_1_to_10_cycles_and_two_block_locks`,
  `zero custom axioms`):
  Universal `dp2IterCarry` Append Law, Unconditional `1..10`-Cycle Freedom Across ALL `DP2`
  Words, `M1` `(r = 8, A = 13)` `6305 / 1631` Carry Separation, & 2-Block `.R`-Carrying
  `leftAnchoredDP2Step` Cycle Locks (`w_1 + w_2 ≥ 11`, Exact 2-Block Brox System, Unconditional
  Odd `q_0, q_1 ≥ 3` & `3 * 2^{w_1} - 1` / `3 * 2^{w_2} - 1` Exponential Minimum Floors, Equal-Even
  Sub-Exponent Lock & Infinite-Cone Exclusion, Symmetric `17 * 2^{w_1} - 1` Collapse, &
  `75 * 2^{w_1} - 1` Mod-4 Even-Shift Boost, `Branch P4.3`, witness
  `M1_DP2_8CYCLE_6305_OVER_1631`, `W15_H1`).
-/
theorem leftAnchoredDP2_no_1_to_10_cycles_and_two_block_locks :
    ((∀ xs ys : List Nat,
        dp2ShiftSum (xs ++ ys) = dp2ShiftSum xs + dp2ShiftSum ys ∧
        dp2IterCarry (xs ++ ys) =
          3 ^ ys.length * dp2IterCarry xs + 2 ^ dp2ShiftSum xs * dp2IterCarry ys) ∧
     (∀ w1 a1 w2 a2 : Nat, w1 ≥ 1 -> w2 ≥ 1 ->
        dp2IterCarry ((List.replicate (w1 - 1) 1 ++ [1 + a1]) ++
                      (List.replicate (w2 - 1) 1 ++ [1 + a2])) =
          3 ^ w2 * (3 ^ w1 - 2 ^ w1) + 2 ^ (w1 + a1) * (3 ^ w2 - 2 ^ w2))) ∧
    ((∀ (r : Nat) (u : List MixedSRSSym),
        1 ≤ r -> r ≤ 10 -> ¬ dp2StepIter r u u) ∧
     (dp2IterCarry (List.replicate 7 1 ++ [6]) = 6305 ∧
      2 ^ 13 - 3 ^ 8 = 1631 ∧
      6305 % 1631 = 1412)) ∧
    (∀ (w1 a1 w2 a2 : Nat) (u0 : List MixedSRSSym),
      w1 ≥ 1 -> a1 ≥ 1 -> w2 ≥ 1 -> a2 ≥ 1 ->
      dp2AnnotatedChain u0
        ((List.replicate (w1 - 1) 1 ++ [1 + a1]) ++
         (List.replicate (w2 - 1) 1 ++ [1 + a2])) u0 ->
      w1 + w2 ≥ 11 ∧
      3 ^ (w1 + w2) < 2 ^ (w1 + a1 + w2 + a2) ∧
      (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)) * dp2GlobalOddVal u0 =
        3 ^ w2 * (3 ^ w1 - 2 ^ w1) + 2 ^ (w1 + a1) * (3 ^ w2 - 2 ^ w2) ∧
      ∃ u1 : List MixedSRSSym,
        2 ^ w1 ∣ (dp2GlobalOddVal u0 + 1) ∧
        2 ^ w2 ∣ (dp2GlobalOddVal u1 + 1) ∧
        let q0 := (dp2GlobalOddVal u0 + 1) / 2 ^ w1
        let q1 := (dp2GlobalOddVal u1 + 1) / 2 ^ w2
        q0 % 2 = 1 ∧ q1 % 2 = 1 ∧ q0 ≥ 3 ∧ q1 ≥ 3 ∧
        dp2GlobalOddVal u0 ≥ 3 * 2 ^ w1 - 1 ∧
        dp2GlobalOddVal u1 ≥ 3 * 2 ^ w2 - 1 ∧
        2 ^ (a1 + w2) * q1 = 3 ^ w1 * q0 + (2 ^ a1 - 1) ∧
        2 ^ (a2 + w1) * q0 = 3 ^ w2 * q1 + (2 ^ a2 - 1) ∧
        (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)) * q0 =
          twoBlockBroxCarry w1 a1 w2 a2 ∧
        (a1 = a2 ∧ w2 ≤ w1 ->
          (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)) ∣
            ((2 ^ a1 - 1) * (3 ^ (w1 - w2) - 2 ^ (w1 - w2)))) ∧
        ¬ (a1 = a2 ∧ w2 < w1 ∧ (w1 + w2) % 2 = 0 ∧ 3 * w1 ≤ 5 * w2) ∧
        (w1 = w2 ∧ a1 = a2 ->
          w1 ≥ 13 ∧ a1 ≥ 8 ∧ q0 = q1 ∧ dp2GlobalOddVal u0 ≥ 17 * 2 ^ w1 - 1) ∧
        (2 ∣ a1 ∧ 2 ∣ a2 ->
          3 ∣ q0 ∧ 3 ∣ q1 ∧ dp2GlobalOddVal u0 ≥ 3 * 2 ^ w1 - 1) ∧
        ((w1 + w2) % 2 = 1 ∧ 4 ∣ a1 ∧ 4 ∣ a2 ->
          15 ∣ q0 ∧ 15 ∣ q1 ∧ dp2GlobalOddVal u0 ≥ 75 * 2 ^ w1 - 1)) := by
  have hsum_blk : ∀ (w a : Nat), w ≥ 1 ->
      (List.replicate (w - 1) 1 ++ [1 + a]).length = w ∧
      dp2ShiftSum (List.replicate (w - 1) 1 ++ [1 + a]) = w + a := by
    intro w a hw1
    have h1 : ∀ k : Nat, dp2ShiftSum (List.replicate k 1 ++ [1 + a]) = k + (1 + a) := by
      intro k; induction k with
      | zero => simp [dp2ShiftSum]
      | succ k' ih => simp only [List.replicate_succ, List.cons_append, dp2ShiftSum, ih]; omega
    refine ⟨by rw [List.length_append, List.length_replicate, List.length_singleton]; omega, ?_⟩
    rw [h1 (w - 1)]; omega
  have hcar_2blk : ∀ w1 a1 w2 a2 : Nat, w1 ≥ 1 -> w2 ≥ 1 ->
      dp2IterCarry ((List.replicate (w1 - 1) 1 ++ [1 + a1]) ++
                    (List.replicate (w2 - 1) 1 ++ [1 + a2])) =
        3 ^ w2 * (3 ^ w1 - 2 ^ w1) + 2 ^ (w1 + a1) * (3 ^ w2 - 2 ^ w2) := by
    intro w1 a1 w2 a2 hw1 hw2
    rw [dp2IterCarry_append_w15,
        (hsum_blk w2 a2 hw2).1, (hsum_blk w1 a1 hw1).2,
        (leftAnchoredDP2_iterated_affine_carry_and_cycle_laws.2.2.2 w1 (1 + a1) hw1).1,
        (leftAnchoredDP2_iterated_affine_carry_and_cycle_laws.2.2.2 w2 (1 + a2) hw2).1]
  have hno_6_10 : ∀ (r : Nat) (u : List MixedSRSSym),
      1 ≤ r -> r ≤ 10 -> ¬ dp2StepIter r u u := by
    intro r u hr1 hr10 hiter
    by_cases hr5 : r ≤ 5
    · exact leftAnchoredDP2_iterated_affine_carry_and_cycle_laws.2.2.1 r u hr1 hr5 hiter
    · rcases (leftAnchoredDP2_iterated_affine_carry_and_cycle_laws.1 r u u hiter).2 with
        ⟨shifts, hlen, _, hann, _, _⟩
      rcases leftAnchoredDP2_iterated_affine_carry_and_cycle_laws.2.1.1 shifts u (by omega) hann with
        ⟨hlt, _, _, _⟩
      rw [hlen] at hlt
      rcases dp2AnnotatedChain_syr_and_ge33_bound shifts u u hann with ⟨_, hsmall | hge33⟩
      · rcases hsmall with ⟨n, hn3, hn31, hno, i, hi_le, hi_eq, hur_eq⟩
        rw [hlen] at hi_le hur_eq
        have hcyc_n : syrIterW15 r n = n := by
          rw [show r = (r - i) + i by omega, syrIterW15_add (r - i) i n, ← hur_eq, hi_eq]
        let k := (n - 3) / 2
        have hk_lt : k < 15 := by dsimp [k]; omega
        have hn_eq : n = 2 * k + 3 := by dsimp [k]; omega
        rw [hn_eq] at hcyc_n
        exact no_small_odd_syr_cycles_6_to_10 ⟨r, by omega⟩ ⟨k, hk_lt⟩ (by dsimp; omega) hcyc_n
      · rw [hlen] at hge33
        have hNu_pos : dp2GlobalOddVal u > 0 := by unfold dp2GlobalOddVal; omega
        have h33_le : 33 ^ r * 2 ^ dp2ShiftSum shifts ≤ 100 ^ r :=
          nat_mul_le_cancel_right_w5 (dp2GlobalOddVal u) _ _ hNu_pos hge33
        let A := dp2ShiftSum shifts
        change 3 ^ r < 2 ^ A at hlt
        change 33 ^ r * 2 ^ A ≤ 100 ^ r at h33_le
        rcases (by omega : r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10) with rfl | rfl | rfl | rfl | rfl
        · by_cases hA : A ≤ 9
          · exact absurd (Nat.lt_of_lt_of_le hlt (nat_pow_mono_exp_pos 2 A 9 (by decide) hA)) (by decide)
          · have hp := Nat.mul_le_mul_left (33 ^ 6) (nat_pow_mono_exp_pos 2 10 A (by decide) (by omega))
            exact absurd (Nat.le_trans hp h33_le) (by decide)
        · by_cases hA : A ≤ 11
          · exact absurd (Nat.lt_of_lt_of_le hlt (nat_pow_mono_exp_pos 2 A 11 (by decide) hA)) (by decide)
          · have hp := Nat.mul_le_mul_left (33 ^ 7) (nat_pow_mono_exp_pos 2 12 A (by decide) (by omega))
            exact absurd (Nat.le_trans hp h33_le) (by decide)
        · by_cases hA : A ≤ 12
          · exact absurd (Nat.lt_of_lt_of_le hlt (nat_pow_mono_exp_pos 2 A 12 (by decide) hA)) (by decide)
          · have hp := Nat.mul_le_mul_left (33 ^ 8) (nat_pow_mono_exp_pos 2 13 A (by decide) (by omega))
            exact absurd (Nat.le_trans hp h33_le) (by decide)
        · by_cases hA : A ≤ 14
          · exact absurd (Nat.lt_of_lt_of_le hlt (nat_pow_mono_exp_pos 2 A 14 (by decide) hA)) (by decide)
          · have hp := Nat.mul_le_mul_left (33 ^ 9) (nat_pow_mono_exp_pos 2 15 A (by decide) (by omega))
            exact absurd (Nat.le_trans hp h33_le) (by decide)
        · by_cases hA : A ≤ 15
          · exact absurd (Nat.lt_of_lt_of_le hlt (nat_pow_mono_exp_pos 2 A 15 (by decide) hA)) (by decide)
          · have hp := Nat.mul_le_mul_left (33 ^ 10) (nat_pow_mono_exp_pos 2 16 A (by decide) (by omega))
            exact absurd (Nat.le_trans hp h33_le) (by decide)
  refine ⟨⟨fun xs ys => ⟨dp2ShiftSum_append_w15 xs ys, dp2IterCarry_append_w15 xs ys⟩, hcar_2blk⟩,
          ⟨hno_6_10, by decide⟩,
          ?_⟩
  -- 2-Block `.R`-carrying `leftAnchoredDP2Step` laws:
  intro w1 a1 w2 a2 u0 hw1 ha1 hw2 ha2 hann
  have hann_to_iter : ∀ (sh : List Nat) (x y : List MixedSRSSym),
      dp2AnnotatedChain x sh y -> dp2StepIter sh.length x y := by
    intro sh; induction sh with
    | nil => intro x y h0; exact h0
    | cons s stl ih =>
      intro x y ⟨_, z, hst, _, htl⟩
      exact ⟨z, hst, ih z y htl⟩
  let blk1 := List.replicate (w1 - 1) 1 ++ [1 + a1]
  let blk2 := List.replicate (w2 - 1) 1 ++ [1 + a2]
  have hlen12 : (blk1 ++ blk2).length = w1 + w2 := by
    rw [List.length_append, (hsum_blk w1 a1 hw1).1, (hsum_blk w2 a2 hw2).1]
  have hsum12 : dp2ShiftSum (blk1 ++ blk2) = w1 + a1 + w2 + a2 := by
    rw [dp2ShiftSum_append_w15, (hsum_blk w1 a1 hw1).2, (hsum_blk w2 a2 hw2).2]; omega
  have hw12_ge11 : w1 + w2 ≥ 11 := by
    by_cases hle10 : w1 + w2 ≤ 10
    · exfalso
      have hit := hann_to_iter (blk1 ++ blk2) u0 u0 hann
      rw [hlen12] at hit
      exact hno_6_10 (w1 + w2) u0 (by omega) hle10 hit
    · omega
  rcases leftAnchoredDP2_iterated_affine_carry_and_cycle_laws.2.1.1 (blk1 ++ blk2) u0
    (by rw [hlen12]; omega) hann with ⟨hlt, _, hsub_eq, _⟩
  rw [hlen12, hsum12] at hlt hsub_eq
  dsimp only [blk1, blk2] at hsub_eq
  rw [hcar_2blk w1 a1 w2 a2 hw1 hw2] at hsub_eq
  rcases dp2AnnotatedChain_split_w15 blk1 blk2 u0 u0 hann with ⟨u1, hann1, hann2⟩
  have hblock_step : ∀ (w a : Nat) (x y : List MixedSRSSym), w ≥ 1 ->
      dp2AnnotatedChain x (List.replicate (w - 1) 1 ++ [1 + a]) y ->
      2 ^ w ∣ (dp2GlobalOddVal x + 1) ∧
      2 ^ a * dp2GlobalOddVal y + 1 = 3 ^ w * ((dp2GlobalOddVal x + 1) / 2 ^ w) := by
    intro w a x y hw hch
    have hit_xy := hann_to_iter _ x y hch
    rw [(hsum_blk w a hw).1] at hit_xy
    have hhom : ∀ (sh : List Nat) (x0 y0 : List MixedSRSSym),
        dp2AnnotatedChain x0 sh y0 ->
        2 ^ dp2ShiftSum sh * dp2GlobalOddVal y0 =
          3 ^ sh.length * dp2GlobalOddVal x0 + dp2IterCarry sh := by
      intro sh; induction sh with
      | nil => intro x0 y0 he; subst he; simp [dp2ShiftSum, dp2IterCarry]
      | cons s stl ih =>
        intro x0 y0 ⟨_, z, _, hsyr, htl⟩
        have iht := ih z y0 htl
        simp only [dp2ShiftSum, dp2IterCarry, List.length_cons]
        calc 2 ^ (s + dp2ShiftSum stl) * dp2GlobalOddVal y0
            = 2 ^ s * (2 ^ dp2ShiftSum stl * dp2GlobalOddVal y0) := by rw [Nat.pow_add, Nat.mul_assoc]
          _ = 2 ^ s * (3 ^ stl.length * dp2GlobalOddVal z + dp2IterCarry stl) := by rw [iht]
          _ = 3 ^ stl.length * (2 ^ s * dp2GlobalOddVal z) + 2 ^ s * dp2IterCarry stl := by rw [Nat.mul_add]; ac_rfl
          _ = 3 ^ stl.length * (3 * dp2GlobalOddVal x0 + 1) + 2 ^ s * dp2IterCarry stl := by rw [hsyr]
          _ = 3 ^ (stl.length + 1) * dp2GlobalOddVal x0 + (3 ^ stl.length + 2 ^ s * dp2IterCarry stl) := by
                rw [Nat.pow_succ, Nat.mul_add, Nat.mul_one]; ac_rfl
    have heq := hhom _ x y hch
    rw [(hsum_blk w a hw).1, (hsum_blk w a hw).2,
        (leftAnchoredDP2_iterated_affine_carry_and_cycle_laws.2.2.2 w (1 + a) hw).1] at heq
    have h2_le_3 : 2 ^ w ≤ 3 ^ w := pow_mono_base_w15c 2 3 (by decide) w
    have hbal : 2 ^ w * (2 ^ a * dp2GlobalOddVal y + 1) = 3 ^ w * (dp2GlobalOddVal x + 1) := by
      rw [Nat.pow_add 2 w a, Nat.mul_assoc] at heq
      rw [Nat.mul_add (2 ^ w), Nat.mul_one, Nat.mul_add (3 ^ w), Nat.mul_one]
      omega
    have hcop : Nat.Coprime (2 ^ w) (3 ^ w) := ((by decide : Nat.Coprime 2 3).pow_left w).pow_right w
    have hdvd : 2 ^ w ∣ (dp2GlobalOddVal x + 1) :=
      hcop.dvd_of_dvd_mul_left ⟨2 ^ a * dp2GlobalOddVal y + 1, hbal.symm⟩
    rcases hdvd with ⟨q, hq⟩
    have hp2_pos : 0 < 2 ^ w := nat_pow_pos_of_pos 2 (by decide) w
    have hdiv : (dp2GlobalOddVal x + 1) / 2 ^ w = q := by
      rw [hq, Nat.mul_comm (2 ^ w) q, Nat.mul_div_cancel q hp2_pos]
    have hmul_q : 2 ^ w * (2 ^ a * dp2GlobalOddVal y + 1) = 2 ^ w * (3 ^ w * q) := by
      rw [hbal, hq]; ac_rfl
    exact ⟨⟨q, hq⟩, by rw [hdiv]; exact Nat.eq_of_mul_eq_mul_left hp2_pos hmul_q⟩
  rcases hblock_step w1 a1 u0 u1 hw1 hann1 with ⟨hdvd0, hsyr0⟩
  rcases hblock_step w2 a2 u1 u0 hw2 hann2 with ⟨hdvd1, hsyr1⟩
  let q0 := (dp2GlobalOddVal u0 + 1) / 2 ^ w1
  let q1 := (dp2GlobalOddVal u1 + 1) / 2 ^ w2
  have hN0_eq : dp2GlobalOddVal u0 + 1 = 2 ^ w1 * q0 := (Nat.mul_div_cancel' hdvd0).symm
  have hN1_eq : dp2GlobalOddVal u1 + 1 = 2 ^ w2 * q1 := (Nat.mul_div_cancel' hdvd1).symm
  have hq0_pos : q0 ≥ 1 := by
    cases hq : q0 with
    | zero => rw [hq, Nat.mul_zero] at hN0_eq; omega
    | succ _ => omega
  have hq1_pos : q1 ≥ 1 := by
    cases hq : q1 with
    | zero => rw [hq, Nat.mul_zero] at hN1_eq; omega
    | succ _ => omega
  have h2a1_pos : 2 ^ a1 ≥ 1 := nat_pow_pos_of_pos 2 (by decide) a1
  have h2a2_pos : 2 ^ a2 ≥ 1 := nat_pow_pos_of_pos 2 (by decide) a2
  have hbrox1 : 2 ^ (a1 + w2) * q1 = 3 ^ w1 * q0 + (2 ^ a1 - 1) := by
    have hm : 2 ^ a1 * (dp2GlobalOddVal u1 + 1) = 2 ^ (a1 + w2) * q1 := by
      rw [hN1_eq, Nat.pow_add]; ac_rfl
    rw [Nat.mul_add, Nat.mul_one] at hm
    change 2 ^ a1 * dp2GlobalOddVal u1 + 1 = 3 ^ w1 * q0 at hsyr0
    omega
  have hbrox2 : 2 ^ (a2 + w1) * q0 = 3 ^ w2 * q1 + (2 ^ a2 - 1) := by
    have hm : 2 ^ a2 * (dp2GlobalOddVal u0 + 1) = 2 ^ (a2 + w1) * q0 := by
      rw [hN0_eq, Nat.pow_add]; ac_rfl
    rw [Nat.mul_add, Nat.mul_one] at hm
    change 2 ^ a2 * dp2GlobalOddVal u0 + 1 = 3 ^ w2 * q1 at hsyr1
    omega
  have hq0_brox : (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)) * q0 =
      twoBlockBroxCarry w1 a1 w2 a2 := by
    unfold twoBlockBroxCarry; dsimp only
    have e1 : 2 ^ (w1 + a1 + w2 + a2) * q0 = 2 ^ (a1 + w2) * (2 ^ (a2 + w1) * q0) := by
      rw [← Nat.mul_assoc, ← Nat.pow_add, show a1 + w2 + (a2 + w1) = w1 + a1 + w2 + a2 by omega]
    have e2 : 2 ^ (a1 + w2) * (3 ^ w2 * q1) = 3 ^ w2 * (2 ^ (a1 + w2) * q1) := by ac_rfl
    have e3 : 3 ^ w2 * (3 ^ w1 * q0) = 3 ^ (w1 + w2) * q0 := by rw [Nat.pow_add]; ac_rfl
    rw [Nat.sub_mul, e1, hbrox2, Nat.mul_add (2 ^ (a1 + w2)), e2, hbrox1,
        Nat.mul_add (3 ^ w2), e3]
    have hle_mul : 3 ^ (w1 + w2) * q0 ≤ 2 ^ (w1 + a1 + w2 + a2) * q0 :=
      Nat.mul_le_mul_right q0 (Nat.le_of_lt hlt)
    omega
  have hq0_odd : q0 % 2 = 1 := by
    by_cases ho0 : q0 % 2 = 1
    · exact ho0
    · exfalso
      have he0 : q0 % 2 = 0 := by omega
      have hp2_lhs : (2 ^ (a1 + w2) * q1) % 2 = 0 := by
        rw [show a1 + w2 = (a1 + w2 - 1) + 1 by omega, Nat.pow_succ,
            Nat.mul_comm (2 ^ (a1 + w2 - 1)) 2, Nat.mul_assoc]; omega
      have hp2_a1 : (2 ^ a1 - 1) % 2 = 1 := by
        have h1 : 2 ^ a1 = 2 * 2 ^ (a1 - 1) := by
          conv => lhs; rw [show a1 = (a1 - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
        omega
      have hmul0 : (3 ^ w1 * q0) % 2 = 0 := by rw [Nat.mul_mod, he0, Nat.mul_zero]
      have hrhs : (3 ^ w1 * q0 + (2 ^ a1 - 1)) % 2 = 1 := by rw [Nat.add_mod, hmul0, hp2_a1]
      rw [← hbrox1] at hrhs; omega
  have hq1_odd : q1 % 2 = 1 := by
    by_cases ho1 : q1 % 2 = 1
    · exact ho1
    · exfalso
      have he1 : q1 % 2 = 0 := by omega
      have hp2_lhs : (2 ^ (a2 + w1) * q0) % 2 = 0 := by
        rw [show a2 + w1 = (a2 + w1 - 1) + 1 by omega, Nat.pow_succ,
            Nat.mul_comm (2 ^ (a2 + w1 - 1)) 2, Nat.mul_assoc]; omega
      have hp2_a2 : (2 ^ a2 - 1) % 2 = 1 := by
        have h1 : 2 ^ a2 = 2 * 2 ^ (a2 - 1) := by
          conv => lhs; rw [show a2 = (a2 - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
        omega
      have hmul1 : (3 ^ w2 * q1) % 2 = 0 := by rw [Nat.mul_mod, he1, Nat.mul_zero]
      have hrhs : (3 ^ w2 * q1 + (2 ^ a2 - 1)) % 2 = 1 := by rw [Nat.add_mod, hmul1, hp2_a2]
      rw [← hbrox2] at hrhs; omega
  have hx0_n3 : (2 ^ w1 * q0 - 1) % 3 ≠ 0 := by
    rw [show 2 ^ w1 * q0 - 1 = dp2GlobalOddVal u0 by omega]
    intro hm0
    have hlhs : (2 ^ a2 * dp2GlobalOddVal u0 + 1) % 3 = 1 := by
      rw [Nat.add_mod, Nat.mul_mod, hm0, Nat.mul_zero]
    have hrhs : (3 ^ w2 * q1) % 3 = 0 := by
      rw [show w2 = (w2 - 1) + 1 by omega, Nat.pow_succ,
          Nat.mul_comm (3 ^ (w2 - 1)) 3, Nat.mul_assoc]; omega
    change 2 ^ a2 * dp2GlobalOddVal u0 + 1 = 3 ^ w2 * q1 at hsyr1
    rw [hsyr1] at hlhs; omega
  have hx1_n3 : (2 ^ w2 * q1 - 1) % 3 ≠ 0 := by
    rw [show 2 ^ w2 * q1 - 1 = dp2GlobalOddVal u1 by omega]
    intro hm0
    have hlhs : (2 ^ a1 * dp2GlobalOddVal u1 + 1) % 3 = 1 := by
      rw [Nat.add_mod, Nat.mul_mod, hm0, Nat.mul_zero]
    have hrhs : (3 ^ w1 * q0) % 3 = 0 := by
      rw [show w1 = (w1 - 1) + 1 by omega, Nat.pow_succ,
          Nat.mul_comm (3 ^ (w1 - 1)) 3, Nat.mul_assoc]; omega
    change 2 ^ a1 * dp2GlobalOddVal u1 + 1 = 3 ^ w1 * q0 at hsyr0
    rw [hsyr0] at hlhs; omega
  have hsyr0_sub : 3 ^ w1 * q0 - 1 = 2 ^ a1 * (2 ^ w2 * q1 - 1) := by
    change 2 ^ a1 * dp2GlobalOddVal u1 + 1 = 3 ^ w1 * q0 at hsyr0
    rw [show 2 ^ w2 * q1 - 1 = dp2GlobalOddVal u1 by omega]; omega
  have hsyr1_sub : 3 ^ w2 * q1 - 1 = 2 ^ a2 * (2 ^ w1 * q0 - 1) := by
    change 2 ^ a2 * dp2GlobalOddVal u0 + 1 = 3 ^ w2 * q1 at hsyr1
    rw [show 2 ^ w1 * q0 - 1 = dp2GlobalOddVal u0 by omega]; omega
  have hq0_ne1 : q0 ≠ 1 := by
    intro hq0_1
    have hw1_ge2 : w1 ≥ 2 := by
      by_cases hw1_1 : w1 = 1
      · have hN0_ge3 : dp2GlobalOddVal u0 ≥ 3 := by unfold dp2GlobalOddVal; omega
        have heq0 : dp2GlobalOddVal u0 + 1 = 2 ^ w1 * q0 := hN0_eq
        rw [hw1_1, hq0_1] at heq0; simp at heq0; omega
      · omega
    exact two_block_q0_ne_one w1 a1 w2 a2 q0 q1 hw1_ge2 ha1 hw2 ha2 (by omega) hlt
      hx0_n3 hq1_pos hq1_odd hsyr0_sub hsyr1_sub hq0_1
  have hq1_ne1 : q1 ≠ 1 := by
    intro hq1_1
    have hw2_ge2 : w2 ≥ 2 := by
      by_cases hw2_1 : w2 = 1
      · have hN1_ge3 : dp2GlobalOddVal u1 ≥ 3 := by unfold dp2GlobalOddVal; omega
        have heq1 : dp2GlobalOddVal u1 + 1 = 2 ^ w2 * q1 := hN1_eq
        rw [hw2_1, hq1_1] at heq1; simp at heq1; omega
      · omega
    have hlt_sw : 3 ^ (w2 + w1) < 2 ^ (w2 + a2 + w1 + a1) := by
      rw [Nat.add_comm w2 w1, show w2 + a2 + w1 + a1 = w1 + a1 + w2 + a2 by omega]; exact hlt
    exact two_block_q0_ne_one w2 a2 w1 a1 q1 q0 hw2_ge2 ha2 hw1 ha1 (by omega) hlt_sw
      hx1_n3 hq0_pos hq0_odd hsyr1_sub hsyr0_sub hq1_1
  have hq0_ge3_all : q0 ≥ 3 := by omega
  have hq1_ge3_all : q1 ≥ 3 := by omega
  have hN0_floor3 : dp2GlobalOddVal u0 ≥ 3 * 2 ^ w1 - 1 := by
    have hm := Nat.mul_le_mul_left (2 ^ w1) hq0_ge3_all
    rw [← hN0_eq, Nat.mul_comm (2 ^ w1) 3] at hm; omega
  have hN1_floor3 : dp2GlobalOddVal u1 ≥ 3 * 2 ^ w2 - 1 := by
    have hm := Nat.mul_le_mul_left (2 ^ w2) hq1_ge3_all
    rw [← hN1_eq, Nat.mul_comm (2 ^ w2) 3] at hm; omega
  have hD_dvd_brox : (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)) ∣ broxSpiralCarry [(w1, a1), (w2, a2)] := by
    have hbe : broxSpiralCarry [(w1, a1), (w2, a2)] = twoBlockBroxCarry w1 a1 w2 a2 := by
      simp [broxSpiralCarry, blockWeightSum, twoBlockBroxCarry]
    rw [hbe]; exact ⟨q0, hq0_brox.symm⟩
  have hm_eq := two_block_shared_mersenne_propagation_and_equal_even_exclusion
    w1 a1 w2 a2 hw1 ha1 hw2 ha2 hlt
  refine ⟨hw12_ge11, hlt, hsub_eq, u1, hdvd0, hdvd1,
          hq0_odd, hq1_odd, hq0_ge3_all, hq1_ge3_all, hN0_floor3, hN1_floor3,
          hbrox1, hbrox2, hq0_brox,
          fun ⟨ha_eq, hw_le⟩ => hm_eq.2.1 ha_eq hw_le hD_dvd_brox,
          fun ⟨ha_eq, hw_lt, hev_w, hcone_w⟩ => (hm_eq.2.2 ha_eq hw_lt hev_w hcone_w).1 hD_dvd_brox,
          ?_, ?_, ?_⟩
  · -- Symmetric `w1 = w2 ∧ a1 = a2`:
    rintro ⟨hw_eq, ha_eq⟩
    subst hw_eq; subst ha_eq
    have hq_eq : q0 = q1 := by
      by_cases hle : q0 ≤ q1
      · by_cases hlt_q : q0 < q1
        · exfalso
          have h1 := Nat.add_le_add_right (Nat.mul_le_mul_left (3 ^ w1) hle) (2 ^ a1 - 1)
          rw [← hbrox1] at h1
          have h2 : 3 ^ w1 * q1 + (2 ^ a1 - 1) = 2 ^ (a1 + w1) * q0 := hbrox2.symm
          have hpos_p : 2 ^ (a1 + w1) ≥ 2 := by
            simpa using pow2_mono_nat (by omega : 1 ≤ a1 + w1)
          have hm_lt := Nat.mul_lt_mul_of_pos_left hlt_q (by omega : 0 < 2 ^ (a1 + w1))
          have hm_3 := Nat.mul_lt_mul_of_pos_left hlt_q (pow3_pos_nat w1)
          omega
        · omega
      · exfalso
        have hlt_q : q1 < q0 := by omega
        have h1 := Nat.add_le_add_right (Nat.mul_le_mul_left (3 ^ w1) (Nat.le_of_lt hlt_q)) (2 ^ a1 - 1)
        rw [← hbrox2] at h1
        have hm_lt := Nat.mul_lt_mul_of_pos_left hlt_q (nat_pow_pos_of_pos 2 (by decide) (a1 + w1))
        have hm_3 := Nat.mul_lt_mul_of_pos_left hlt_q (pow3_pos_nat w1)
        omega
    rw [← hq_eq, Nat.add_comm a1 w1] at hbrox1
    have hgt1 : 3 ^ w1 < 2 ^ (w1 + a1) := by
      by_cases hg : 3 ^ w1 < 2 ^ (w1 + a1)
      · exact hg
      · have hle_p : 2 ^ (w1 + a1) ≤ 3 ^ w1 := by omega
        have hm := Nat.mul_le_mul_right q0 hle_p
        have ha2_ge : 2 ^ a1 - 1 ≥ 1 := by
          have hp : 2 ≤ 2 ^ a1 := by simpa using pow2_mono_nat ha1
          omega
        omega
    have hw1_ge2 : w1 ≥ 2 := by omega
    have h1b : (2 ^ (w1 + a1) - 3 ^ w1) * q0 = 2 ^ a1 - 1 := by
      have hm_le : 3 ^ w1 * q0 ≤ 2 ^ (w1 + a1) * q0 :=
        Nat.mul_le_mul_right q0 (Nat.le_of_lt hgt1)
      rw [Nat.sub_mul, hbrox1]; omega
    have hD_le : 2 ^ (w1 + a1) - 3 ^ w1 ≤ 2 ^ a1 - 1 := by
      have hm := Nat.mul_le_mul_left (2 ^ (w1 + a1) - 3 ^ w1) hq0_pos
      rwa [Nat.mul_one, h1b] at hm
    rcases one_block_w1_ge_13_and_a1_ge_8 w1 a1 hw1_ge2 ha1 hgt1 hD_le with ⟨hw13, ha8⟩
    have hq0_ge17 : q0 ≥ 17 :=
      (one_block_no_pow3_quotient_and_q0_ge_17 w1 a1 q0 hw1_ge2 ha1 hgt1 h1b).2.2.2.2.1
    have hN0_17 : dp2GlobalOddVal u0 ≥ 17 * 2 ^ w1 - 1 := by
      have hm := Nat.mul_le_mul_left (2 ^ w1) hq0_ge17
      rw [← hN0_eq, Nat.mul_comm (2 ^ w1) 17] at hm; omega
    exact ⟨hw13, ha8, hq_eq, hN0_17⟩
  · -- `2 ∣ a1 ∧ 2 ∣ a2`:
    rintro ⟨⟨k1, hk1⟩, ⟨k2, hk2⟩⟩
    have h4_m3 : ∀ k : Nat, (2 ^ (2 * k) - 1) % 3 = 0 := by
      intro k; induction k with
      | zero => rfl
      | succ k' ih =>
        have hstep : 2 ^ (2 * (k' + 1)) - 1 = 4 * (2 ^ (2 * k') - 1) + 3 := by
          rw [show 2 * (k' + 1) = 2 * k' + 2 by omega, Nat.pow_add]
          have hp := nat_pow_pos_of_pos 2 (by decide) (2 * k')
          omega
        rw [hstep]; omega
    have hdvd3_1 : 3 ∣ (2 ^ a1 - 1) := Nat.dvd_of_mod_eq_zero (hk1 ▸ h4_m3 k1)
    have hdvd3_2 : 3 ∣ (2 ^ a2 - 1) := Nat.dvd_of_mod_eq_zero (hk2 ▸ h4_m3 k2)
    have h3_w1 : 3 ∣ 3 ^ w1 * q0 := by
      rw [show w1 = 1 + (w1 - 1) by omega, Nat.pow_add, Nat.pow_one, Nat.mul_assoc]
      exact ⟨3 ^ (w1 - 1) * q0, rfl⟩
    have h3_w2 : 3 ∣ 3 ^ w2 * q1 := by
      rw [show w2 = 1 + (w2 - 1) by omega, Nat.pow_add, Nat.pow_one, Nat.mul_assoc]
      exact ⟨3 ^ (w2 - 1) * q1, rfl⟩
    have hcop3_2 : ∀ n : Nat, Nat.Coprime 3 (2 ^ n) := fun n => (by decide : Nat.Coprime 3 2).pow_right n
    have h3_q1 : 3 ∣ q1 := (hcop3_2 (a1 + w2)).dvd_of_dvd_mul_left (by rw [hbrox1]; exact Nat.dvd_add h3_w1 hdvd3_1)
    have h3_q0 : 3 ∣ q0 := (hcop3_2 (a2 + w1)).dvd_of_dvd_mul_left (by rw [hbrox2]; exact Nat.dvd_add h3_w2 hdvd3_2)
    have hq0_ge3 : q0 ≥ 3 := by
      rcases h3_q0 with ⟨c, hc⟩
      cases c with
      | zero => rw [Nat.mul_zero] at hc; omega
      | succ _ => omega
    have hN0_3 : dp2GlobalOddVal u0 ≥ 3 * 2 ^ w1 - 1 := by
      have hm := Nat.mul_le_mul_left (2 ^ w1) hq0_ge3
      rw [← hN0_eq, Nat.mul_comm (2 ^ w1) 3] at hm; omega
    exact ⟨h3_q0, h3_q1, hN0_3⟩
  · -- `(w1 + w2) % 2 = 1 ∧ 4 ∣ a1 ∧ 4 ∣ a2`:
    rintro ⟨hw_odd, ⟨k1, hk1⟩, ⟨k2, hk2⟩⟩
    have ha1_ge4 : a1 ≥ 4 := by omega
    have h16_m15 : ∀ k : Nat, (2 ^ (4 * k) - 1) % 15 = 0 := by
      intro k; induction k with
      | zero => rfl
      | succ k' ih =>
        have hstep : 2 ^ (4 * (k' + 1)) - 1 = 16 * (2 ^ (4 * k') - 1) + 15 := by
          rw [show 4 * (k' + 1) = 4 * k' + 4 by omega, Nat.pow_add]
          have hp := nat_pow_pos_of_pos 2 (by decide) (4 * k')
          omega
        rw [hstep]; omega
    have hd15_1 : 15 ∣ (2 ^ a1 - 1) := Nat.dvd_of_mod_eq_zero (hk1 ▸ h16_m15 k1)
    have hd15_2 : 15 ∣ (2 ^ a2 - 1) := Nat.dvd_of_mod_eq_zero (hk2 ▸ h16_m15 k2)
    have h3_1 : 3 ∣ (2 ^ a1 - 1) := Nat.dvd_trans (by decide : 3 ∣ 15) hd15_1
    have h3_2 : 3 ∣ (2 ^ a2 - 1) := Nat.dvd_trans (by decide : 3 ∣ 15) hd15_2
    have h5_1 : 5 ∣ (2 ^ a1 - 1) := Nat.dvd_trans (by decide : 5 ∣ 15) hd15_1
    have h5_2 : 5 ∣ (2 ^ a2 - 1) := Nat.dvd_trans (by decide : 5 ∣ 15) hd15_2
    have h3_q0 : 3 ∣ q0 := ((by decide : Nat.Coprime 3 2).pow_right (a2 + w1)).dvd_of_dvd_mul_left (by
      rw [hbrox2]
      refine Nat.dvd_add ?_ h3_2
      rw [show w2 = 1 + (w2 - 1) by omega, Nat.pow_add, Nat.pow_one, Nat.mul_assoc]
      exact ⟨_, rfl⟩)
    have h3_q1 : 3 ∣ q1 := ((by decide : Nat.Coprime 3 2).pow_right (a1 + w2)).dvd_of_dvd_mul_left (by
      rw [hbrox1]
      refine Nat.dvd_add ?_ h3_1
      rw [show w1 = 1 + (w1 - 1) by omega, Nat.pow_add, Nat.pow_one, Nat.mul_assoc]
      exact ⟨_, rfl⟩)
    have hm5_1 : (2 ^ (a1 + w2) * q1) % 5 = (3 ^ w1 * q0) % 5 := by
      rw [hbrox1, Nat.add_mod, Nat.mod_eq_zero_of_dvd h5_1, Nat.add_zero, Nat.mod_mod]
    have hm5_2 : (2 ^ (a2 + w1) * q0) % 5 = (3 ^ w2 * q1) % 5 := by
      rw [hbrox2, Nat.add_mod, Nat.mod_eq_zero_of_dvd h5_2, Nat.add_zero, Nat.mod_mod]
    have hp16_m5 : ∀ k : Nat, 2 ^ (4 * k) % 5 = 1 := by
      intro k; induction k with
      | zero => rfl
      | succ k' ih =>
        rw [show 4 * (k' + 1) = 4 * k' + 4 by omega, Nat.pow_add, Nat.mul_mod, ih]
    have hprod5 : (2 ^ (w1 + a1 + w2 + a2) * q0) % 5 = (3 ^ (w1 + w2) * q0) % 5 := by
      have hm_mul5 : ∀ x y : Nat, (x * y) % 5 = (x * (y % 5)) % 5 := by
        intro x y; rw [Nat.mul_mod x (y % 5) 5, Nat.mod_mod, ← Nat.mul_mod]
      have s1 : (2 ^ (a1 + w2) * (3 ^ w2 * q1)) % 5 = (3 ^ (w1 + w2) * q0) % 5 := by
        calc (2 ^ (a1 + w2) * (3 ^ w2 * q1)) % 5
            = (3 ^ w2 * (2 ^ (a1 + w2) * q1)) % 5 := by ac_rfl
          _ = (3 ^ w2 * ((2 ^ (a1 + w2) * q1) % 5)) % 5 := hm_mul5 _ _
          _ = (3 ^ w2 * ((3 ^ w1 * q0) % 5)) % 5 := by rw [hm5_1]
          _ = (3 ^ w2 * (3 ^ w1 * q0)) % 5 := (hm_mul5 _ _).symm
          _ = (3 ^ (w1 + w2) * q0) % 5 := by rw [Nat.pow_add]; ac_rfl
      have s2 : (2 ^ (a1 + w2) * (3 ^ w2 * q1)) % 5 = (2 ^ (w1 + a1 + w2 + a2) * q0) % 5 := by
        calc (2 ^ (a1 + w2) * (3 ^ w2 * q1)) % 5
            = (2 ^ (a1 + w2) * ((3 ^ w2 * q1) % 5)) % 5 := hm_mul5 _ _
          _ = (2 ^ (a1 + w2) * ((2 ^ (a2 + w1) * q0) % 5)) % 5 := by rw [← hm5_2]
          _ = (2 ^ (a1 + w2) * (2 ^ (a2 + w1) * q0)) % 5 := (hm_mul5 _ _).symm
          _ = (2 ^ (w1 + a1 + w2 + a2) * q0) % 5 := by
                rw [← Nat.mul_assoc, ← Nat.pow_add, show a1 + w2 + (a2 + w1) = w1 + a1 + w2 + a2 by omega]
      exact s2.symm.trans s1
    have h23_odd : ∀ k : Nat,
        (2 ^ (2 * k + 1) % 5 = 2 ∧ 3 ^ (2 * k + 1) % 5 = 3) ∨
        (2 ^ (2 * k + 1) % 5 = 3 ∧ 3 ^ (2 * k + 1) % 5 = 2) := by
      intro k; induction k with
      | zero => exact Or.inl ⟨rfl, rfl⟩
      | succ k' ih =>
        rw [show 2 * (k' + 1) + 1 = (2 * k' + 1) + 2 by omega,
            Nat.pow_add 2 (2 * k' + 1) 2, Nat.pow_add 3 (2 * k' + 1) 2,
            Nat.mul_mod (2 ^ (2 * k' + 1)) (2 ^ 2) 5,
            Nat.mul_mod (3 ^ (2 * k' + 1)) (3 ^ 2) 5]
        rcases ih with ⟨h2, h3⟩ | ⟨h2, h3⟩
        · exact Or.inr ⟨by rw [h2], by rw [h3]⟩
        · exact Or.inl ⟨by rw [h2], by rw [h3]⟩
    have h2k_m5 : 2 ^ (w1 + a1 + w2 + a2) % 5 = 2 ^ (w1 + w2) % 5 := by
      rw [show w1 + a1 + w2 + a2 = (w1 + w2) + 4 * (k1 + k2) by omega,
          Nat.pow_add, Nat.mul_mod, hp16_m5 (k1 + k2), Nat.mul_one, Nat.mod_mod]
    have hq0_m5 : q0 % 5 = 0 := by
      rw [Nat.mul_mod, h2k_m5, Nat.mul_mod (3 ^ (w1 + w2))] at hprod5
      have hlt5 : q0 % 5 < 5 := Nat.mod_lt q0 (by decide)
      have hw_split : w1 + w2 = 2 * ((w1 + w2) / 2) + 1 := by omega
      rw [hw_split] at hprod5
      rcases h23_odd ((w1 + w2) / 2) with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> rw [h2, h3] at hprod5 <;> omega
    have hq1_m5 : q1 % 5 = 0 := by
      rw [Nat.mul_mod (3 ^ w1), hq0_m5, Nat.mul_zero, Nat.zero_mod] at hm5_1
      have hp2_nz : ∀ n : Nat, 2 ^ n % 5 = 1 ∨ 2 ^ n % 5 = 2 ∨ 2 ^ n % 5 = 4 ∨ 2 ^ n % 5 = 3 := by
        intro n; induction n with
        | zero => exact Or.inl rfl
        | succ n' ihn => rw [Nat.pow_succ, Nat.mul_mod]; rcases ihn with h | h | h | h <;> rw [h] <;> decide
      rw [Nat.mul_mod] at hm5_1
      have hlt5 : q1 % 5 < 5 := Nat.mod_lt q1 (by decide)
      rcases hp2_nz (a1 + w2) with h | h | h | h <;> rw [h] at hm5_1 <;> omega
    have h15_q0 : 15 ∣ q0 := (by decide : Nat.Coprime 3 5).mul_dvd_of_dvd_of_dvd h3_q0 (Nat.dvd_of_mod_eq_zero hq0_m5)
    have h15_q1 : 15 ∣ q1 := (by decide : Nat.Coprime 3 5).mul_dvd_of_dvd_of_dvd h3_q1 (Nat.dvd_of_mod_eq_zero hq1_m5)
    have hq0_75 : q0 ≥ 75 :=
      (m_block_two_pivot_telescoping_and_2adic_quotient_boost.2.1.2 w1 a1 w2 q0 q1 ha1_ge4 hbrox1).1 h15_q0
    have hN0_75 : dp2GlobalOddVal u0 ≥ 75 * 2 ^ w1 - 1 := by
      have hm := Nat.mul_le_mul_left (2 ^ w1) hq0_75
      rw [← hN0_eq, Nat.mul_comm (2 ^ w1) 75] at hm; omega
    exact ⟨h15_q0, h15_q1, hN0_75⟩

-- ============================================================================
-- SECTION 2: Front B (Branches P3.3 & P3.4) — Unified Arbitrary-`U` `(U*T) × (U*T)`
--            All-Block Confluent Laurent Divisibility & Asymptotic `(U*T)!` Dominance,
--            Rank-3 `9 × 9` `(T = 3, U = 3)` Global `u = 1..9` & Cone-Free `∀ u ≥ 1`
--            Non-Vanishing + Multi-`u` Zero Ceiling, & General Mod-`2^s` 2-Adic
--            Inverse-Residue Quotient Boost + 3-Pivot Cross-Block Brox Squeeze (`W15_H2`)
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Section 2A: Unified Arbitrary-`U` `(U * T) × (U * T)` All-Block Confluent
--             Laurent Divisibility, Pairwise/Quadratic Divisibility, Majorant,
--             Unit-Grid Sharpness, & Universal `U ≥ 4` Factorial Dominance
-- ----------------------------------------------------------------------------

/-- Arbitrary-block `(U * T)` column grid `(j % T, (j / T) * u)` on `(0, u, ..., (U - 1) * u)`. -/
def laurentColsAllU (U T u : Nat) (j : Fin (U * T)) : Nat × Nat :=
  let _ := U
  (j.val % T, (j.val / T) * u)

/-- Node value `P ^ (r / T)` at Hasse–Newton index `r` for block width `T ≥ 1`. -/
def mixedNodeAllU (T P r : Nat) : Nat :=
  P ^ (r / T)

/-- Mixed-node Hasse–Newton divided-difference coefficient `c_{x, r}` for arbitrary block count. -/
def mixedNewtonCoeffAllU (T P : Nat) : Nat -> Nat -> Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | x + 1, 0 => mixedNodeAllU T P 0 * mixedNewtonCoeffAllU T P x 0
  | x + 1, r + 1 =>
    mixedNewtonCoeffAllU T P x r + mixedNodeAllU T P (r + 1) * mixedNewtonCoeffAllU T P x (r + 1)

/-- Hasse derivative `D^t (∏_{j < r} (z - mixedNodeAllU T P j))` evaluated at `z = zv ≥ nodes`. -/
def hasseNodePolyAllU (T P : Nat) : Nat -> Nat -> Nat -> Nat
  | 0, _, 0 => 1
  | 0, _, _ + 1 => 0
  | r + 1, zv, 0 => (zv - mixedNodeAllU T P r) * hasseNodePolyAllU T P r zv 0
  | r + 1, zv, t + 1 =>
    hasseNodePolyAllU T P r zv t + (zv - mixedNodeAllU T P r) * hasseNodePolyAllU T P r zv (t + 1)

/-- Product `∏_{a < b} (P ^ m - P ^ a)` of inter-block differences up to block `b` against `P ^ m`. -/
def blockNodeDiffProd (P m : Nat) : Nat -> Nat
  | 0 => 1
  | b + 1 => blockNodeDiffProd P m b * (P ^ m - P ^ b)

/-- Confluent diagonal product contributed by the `T` columns of block `m`:
    `P ^ (m * T * (T - 1) / 2) * (∏_{a < m} (P ^ m - P ^ a)) ^ (T ^ 2)`. -/
def confluentBlockFactor (T P m : Nat) : Nat :=
  P ^ (m * triNumNat T) * (blockNodeDiffProd P m m) ^ (T * T)

/-- Prefix product `∏_{m < U} confluentBlockFactor T P m`. -/
def confluentFactorAllUAux (T P : Nat) : Nat -> Nat
  | 0 => 1
  | m + 1 => confluentFactorAllUAux T P m * confluentBlockFactor T P m

/-- Universal `U`-block confluent zero-gap Laurent factor on `(U * T) × (U * T)` at shift `u`. -/
def confluentFactorAllU (U T u : Nat) : Nat :=
  confluentFactorAllUAux T (2 ^ u) U

private theorem natSumUpTo_congr_w15 (n : Nat) (f g : Nat -> Nat)
    (hfg : ∀ r : Nat, r < n -> f r = g r) :
    natSumUpTo n f = natSumUpTo n g := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    simp only [natSumUpTo, ih (fun r hr => hfg r (by omega)), hfg n' (Nat.lt_succ_self n')]

private theorem natSumUpTo_mul_left_w15 (c : Nat) (n : Nat) (f : Nat -> Nat) :
    c * natSumUpTo n f = natSumUpTo n (fun r => c * f r) := by
  induction n with
  | zero => simp [natSumUpTo]
  | succ n' ih => simp only [natSumUpTo, Nat.mul_add, ih]

private def intDiagProdPrefix_def_w15 (N : Nat) (U : Fin N -> Fin N -> Int) : Nat -> Int
  | 0 => 1
  | k + 1 =>
    if h : k < N then intDiagProdPrefix_def_w15 N U k * U ⟨k, h⟩ ⟨k, h⟩
    else intDiagProdPrefix_def_w15 N U k

private theorem intDet_mul_upper_tri_w15 (N : Nat) (A U : Fin N -> Fin N -> Int)
    (hupper : ∀ r c : Fin N, c.val < r.val -> U r c = 0) :
    intDet N (fun i j => intSumPrefix N (fun r => A i r * U r j) N) =
      intDiagProdPrefix_def_w15 N U N * intDet N A := by
  have htrunc : ∀ (i j : Fin N) (m : Nat), j.val + 1 ≤ m -> m ≤ N ->
      intSumPrefix N (fun r => A i r * U r j) m =
        intSumPrefix N (fun r => A i r * U r j) (j.val + 1) := by
    intro i j m hge hle
    have hst : ∀ d : Nat, j.val + 1 + d ≤ N ->
        intSumPrefix N (fun r => A i r * U r j) (j.val + 1 + d) =
          intSumPrefix N (fun r => A i r * U r j) (j.val + 1) := by
      intro d hd; induction d with
      | zero => rfl
      | succ d' ih =>
        rw [Nat.add_succ]
        have hlt : j.val + 1 + d' < N := hd
        conv => lhs; unfold intSumPrefix
        simp only [hlt, dite_true]
        rw [ih (by omega), hupper ⟨j.val + 1 + d', hlt⟩ j (by dsimp; omega), Int.mul_zero, Int.add_zero]
    simpa [show j.val + 1 + (m - (j.val + 1)) = m by omega] using hst (m - (j.val + 1)) (by omega)
  let M_stage : Nat -> Fin N -> Fin N -> Int := fun k i j =>
    if j.val < k then A i j else intSumPrefix N (fun r => A i r * U r j) (j.val + 1)
  have h0_eq : (fun i j : Fin N => intSumPrefix N (fun r => A i r * U r j) N) = M_stage 0 := by
    funext i j; simp only [M_stage, Nat.not_lt_zero, ite_false]
    exact htrunc i j N (by omega) (Nat.le_refl N)
  have hN_eq : M_stage N = A := by
    funext i j; dsimp [M_stage]; rw [ite_true_of_w10 j.isLt]
  have hstep : ∀ k : Nat, k ≤ N ->
      intDet N (M_stage 0) = intDiagProdPrefix_def_w15 N U k * intDet N (M_stage k) := by
    intro k hk; induction k with
    | zero => simp [intDiagProdPrefix_def_w15]
    | succ k' ih =>
      have hk'_lt : k' < N := hk
      let jk : Fin N := ⟨k', hk'_lt⟩
      rw [ih (Nat.le_of_lt hk)]
      let idxC : Nat -> Fin N := fun r => if h : r < N then ⟨r, h⟩ else jk
      let coefC : Nat -> Int := fun r => if h : r < N then U ⟨r, h⟩ jk else 0
      have hneC : ∀ r : Nat, r < k' -> idxC r ≠ jk := by
        intro r hr; have hrN : r < N := by omega
        dsimp [idxC]; simp only [hrN, dite_true]
        intro heq; have hv := congrArg Fin.val heq; dsimp [jk] at hv; omega
      rw [intDet_sub_col_prefix_invariant N jk (M_stage k') k' idxC coefC hneC]
      have hcomb_eq : ∀ (i : Fin N) (q : Nat), q ≤ k' ->
          colPrefixComb (M_stage k') idxC coefC i q =
            intSumPrefix N (fun r => A i r * U r jk) q := by
        intro i q hq; induction q with
        | zero => rfl
        | succ q' ihq =>
          have hq'_lt : q' < k' := hq
          have hq'_N : q' < N := by omega
          simp only [colPrefixComb, intSumPrefix, hq'_N, dite_true]
          rw [ihq (Nat.le_of_lt hq)]
          have hi : idxC q' = ⟨q', hq'_N⟩ := by dsimp [idxC]; simp [hq'_N]
          have hc : coefC q' = U ⟨q', hq'_N⟩ jk := by dsimp [coefC]; simp [hq'_N]
          have hm : M_stage k' i ⟨q', hq'_N⟩ = A i ⟨q', hq'_N⟩ := by
            dsimp [M_stage]; rw [ite_true_of_w10 hq'_lt]
          rw [hi, hc, hm, Int.mul_comm]
      have hcol_rew :
          (fun i j : Fin N =>
            if j = jk then M_stage k' i jk - colPrefixComb (M_stage k') idxC coefC i k'
            else M_stage k' i j) =
          (fun i j : Fin N =>
            if j = jk then U jk jk * M_stage (k' + 1) i jk
            else M_stage (k' + 1) i j) := by
        funext i j
        by_cases hj : j = jk
        · subst hj
          rw [ite_true_of_w10 rfl, ite_true_of_w10 rfl, hcomb_eq i k' (Nat.le_refl k')]
          have hm_k : M_stage k' i jk = intSumPrefix N (fun r => A i r * U r jk) (k' + 1) := by
            dsimp [M_stage, jk]; rw [ite_false_of_w10 (Nat.lt_irrefl k')]
          have hm_k1 : M_stage (k' + 1) i jk = A i jk := by
            dsimp [M_stage, jk]; rw [ite_true_of_w10 (Nat.lt_succ_self k')]
          rw [hm_k, hm_k1]
          simp only [intSumPrefix, hk'_lt, dite_true]
          change (_ + A i jk * U jk jk) - _ = U jk jk * A i jk
          rw [Int.mul_comm (A i jk) (U jk jk)]; omega
        · rw [ite_false_of_w10 hj, ite_false_of_w10 hj]
          have hjv : j.val ≠ k' := fun hv => hj (Fin.ext hv)
          dsimp [M_stage]
          by_cases hlt : j.val < k'
          · rw [ite_true_of_w10 hlt, ite_true_of_w10 (by omega)]
          · rw [ite_false_of_w10 hlt, ite_false_of_w10 (by omega)]
      rw [hcol_rew, intDet_col_scale (U jk jk) N jk (M_stage (k' + 1))]
      simp only [intDiagProdPrefix_def_w15, hk'_lt, dite_true]
      exact (Int.mul_assoc (intDiagProdPrefix_def_w15 N U k') (U jk jk) _).symm
  rw [h0_eq, hstep N (Nat.le_refl N), hN_eq]

private theorem intDet_unit_lower_tri_w15 :
    ∀ (N : Nat) (A : Fin N -> Fin N -> Int),
      (∀ i : Fin N, A i i = 1) ->
      (∀ i j : Fin N, i.val < j.val -> A i j = 0) ->
      intDet N A = 1
  | 0, _, _, _ => rfl
  | L + 1, A, hdiag, hup => by
    rw [intDet_lower_triangular (L + 1) A hup]
    dsimp only
    rw [hdiag ⟨0, Nat.zero_lt_succ L⟩, Int.one_mul]
    exact intDet_unit_lower_tri_w15 L (intSubMat A ⟨0, Nat.zero_lt_succ L⟩)
      (fun i => by
        unfold intSubMat skipFinIdx; simp only [Nat.not_lt_zero, ite_false]
        exact hdiag ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (fun i j hij => by
        unfold intSubMat skipFinIdx; simp only [Nat.not_lt_zero, ite_false]
        exact hup ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ (by dsimp; omega))

private theorem hasseNodePolyAllU_equal_block (T P b0 zv : Nat)
    (heq_node : ∀ s : Nat, s < T -> mixedNodeAllU T P (b0 + s) = zv) :
    ∀ (s t : Nat), s ≤ T ->
      hasseNodePolyAllU T P (b0 + s) zv t =
        if s ≤ t then hasseNodePolyAllU T P b0 zv (t - s) else 0
  | 0, t, _ => by simp
  | s + 1, 0, hsT => by
    rw [Nat.add_succ]
    simp [hasseNodePolyAllU, heq_node s hsT]
  | s + 1, t + 1, hsT => by
    rw [Nat.add_succ]
    simp only [hasseNodePolyAllU, heq_node s hsT, Nat.sub_self, Nat.zero_mul, Nat.add_zero]
    rw [hasseNodePolyAllU_equal_block T P b0 zv heq_node s t (Nat.le_of_lt hsT)]
    by_cases hst : s ≤ t
    · rw [ite_true_of_w10 hst, ite_true_of_w10 (by omega : s + 1 ≤ t + 1),
          show t + 1 - (s + 1) = t - s by omega]
    · rw [ite_false_of_w10 hst, ite_false_of_w10 (by omega : ¬ (s + 1 ≤ t + 1))]

private theorem hasseNodePolyAllU_zero_after_block (T P b0 zv : Nat)
    (hz_base : ∀ t : Nat, t < T -> hasseNodePolyAllU T P (b0 + T) zv t = 0) :
    ∀ (q t : Nat), t < T -> hasseNodePolyAllU T P (b0 + T + q) zv t = 0
  | 0, t, ht => by simpa using hz_base t ht
  | q + 1, 0, ht => by
    rw [Nat.add_succ]
    simp [hasseNodePolyAllU, hasseNodePolyAllU_zero_after_block T P b0 zv hz_base q 0 ht]
  | q + 1, t + 1, ht => by
    rw [Nat.add_succ]
    simp [hasseNodePolyAllU,
          hasseNodePolyAllU_zero_after_block T P b0 zv hz_base q t (by omega),
          hasseNodePolyAllU_zero_after_block T P b0 zv hz_base q (t + 1) ht]

private theorem mixedNewtonAllU_hasse_col_identity (T P : Nat) (hT : T ≥ 1) (hP : P ≥ 1) :
    ∀ (m t : Nat), t < T ->
      let zv := P ^ m
      (∀ r : Nat, m * T + t < r -> hasseNodePolyAllU T P r zv t = 0) ∧
      hasseNodePolyAllU T P (m * T + t) zv t = (blockNodeDiffProd P m m) ^ T ∧
      (∀ x : Nat,
        zv ^ t * natSumUpTo (m * T + t + 1)
          (fun r => mixedNewtonCoeffAllU T P x r * hasseNodePolyAllU T P r zv t) =
        laurentInterpBinom x t * zv ^ x) := by
  intro m t htT; dsimp only
  let zv := P ^ m
  have heq_blk : ∀ (b s : Nat), s < T -> mixedNodeAllU T P (b * T + s) = P ^ b := by
    intro b s hsT
    unfold mixedNodeAllU
    have hd : (b * T + s) / T = b := by
      have h1 := Nat.add_mul_div_right s b hT
      rwa [Nat.add_comm s (b * T), Nat.div_eq_of_lt hsT, Nat.zero_add] at h1
    rw [hd]
  have hle_blk : ∀ r : Nat, r < m * T + T -> mixedNodeAllU T P r ≤ zv := by
    intro r hr_lt
    unfold mixedNodeAllU
    have hdiv_le : r / T ≤ m := by
      by_cases h : r / T ≤ m
      · exact h
      · exfalso
        have hm1 : T * (m + 1) ≤ T * (r / T) := Nat.mul_le_mul_left T (by omega)
        have hdm := Nat.div_add_mod r T
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm T m] at hm1
        omega
    exact nat_pow_mono_exp_pos P (r / T) m hP hdiv_le
  have hz_gt : ∀ r : Nat, m * T + t < r -> hasseNodePolyAllU T P r zv t = 0 := by
    have hz_in : ∀ s : Nat, t < s -> s ≤ T -> hasseNodePolyAllU T P (m * T + s) zv t = 0 := by
      intro s hts hsT
      rw [hasseNodePolyAllU_equal_block T P (m * T) zv (heq_blk m) s t hsT,
          ite_false_of_w10 (by omega : ¬ (s ≤ t))]
    have hz_end : ∀ t' : Nat, t' < T -> hasseNodePolyAllU T P (m * T + T) zv t' = 0 := by
      intro t' ht'
      rw [hasseNodePolyAllU_equal_block T P (m * T) zv (heq_blk m) T t' (Nat.le_refl T),
          ite_false_of_w10 (by omega : ¬ (T ≤ t'))]
    intro r hr_gt
    by_cases hle : r ≤ m * T + T
    · simpa [show m * T + (r - m * T) = r by omega] using hz_in (r - m * T) (by omega) (by omega)
    · simpa [show m * T + T + (r - (m * T + T)) = r by omega] using
        hasseNodePolyAllU_zero_after_block T P (m * T) zv hz_end (r - (m * T + T)) t htT
  have h0_blk : ∀ b : Nat, b ≤ m ->
      hasseNodePolyAllU T P (b * T) zv 0 = (blockNodeDiffProd P m b) ^ T := by
    intro b hb; induction b with
    | zero => simp [hasseNodePolyAllU, blockNodeDiffProd]
    | succ b' ih =>
      have hstep_s : ∀ s : Nat, s ≤ T ->
          hasseNodePolyAllU T P (b' * T + s) zv 0 =
            (zv - P ^ b') ^ s * hasseNodePolyAllU T P (b' * T) zv 0 := by
        intro s hs; induction s with
        | zero => simp
        | succ s' ihs =>
          rw [Nat.add_succ]
          simp only [hasseNodePolyAllU, heq_blk b' s' hs, ihs (Nat.le_of_lt hs), Nat.pow_succ]
          ac_rfl
      have hsT := hstep_s T (Nat.le_refl T)
      rw [show b' * T + T = (b' + 1) * T by rw [Nat.add_mul, Nat.one_mul]] at hsT
      rw [hsT, ih (Nat.le_of_lt hb), blockNodeDiffProd, mul_pow_w15c]
      ac_rfl
  have hdiag : hasseNodePolyAllU T P (m * T + t) zv t = (blockNodeDiffProd P m m) ^ T := by
    rw [hasseNodePolyAllU_equal_block T P (m * T) zv (heq_blk m) t t (Nat.le_of_lt htT),
        ite_true_of_w10 (Nat.le_refl t), Nat.sub_self, h0_blk m (Nat.le_refl m)]
  refine ⟨hz_gt, hdiag, ?_⟩
  have hall_t : ∀ (x t0 : Nat), t0 < T ->
      zv ^ t0 * natSumUpTo (m * T + t0 + 1)
        (fun r => mixedNewtonCoeffAllU T P x r * hasseNodePolyAllU T P r zv t0) =
      laurentInterpBinom x t0 * zv ^ x := by
    intro x; induction x with
    | zero =>
      intro t0 _
      have hsum0 : ∀ n : Nat,
          natSumUpTo (n + 1) (fun r => mixedNewtonCoeffAllU T P 0 r * hasseNodePolyAllU T P r zv t0) =
            hasseNodePolyAllU T P 0 zv t0 := by
        intro n; induction n with
        | zero => simp [natSumUpTo, mixedNewtonCoeffAllU]
        | succ n' ihn => conv => lhs; unfold natSumUpTo; rw [ihn]; simp [mixedNewtonCoeffAllU]
      rw [hsum0 (m * T + t0)]
      cases t0 <;> simp [hasseNodePolyAllU, laurentInterpBinom]
    | succ x' ihx =>
      intro t0 ht0
      have hsbp : ∀ (c : Nat) (g : Nat -> Nat),
          natSumUpTo (c + 1) (fun r => mixedNewtonCoeffAllU T P (x' + 1) r * g r) =
            natSumUpTo c (fun r =>
              mixedNewtonCoeffAllU T P x' r * (mixedNodeAllU T P r * g r + g (r + 1))) +
            mixedNewtonCoeffAllU T P x' c * (mixedNodeAllU T P c * g c) := by
        intro c g; induction c with
        | zero => simp only [natSumUpTo, mixedNewtonCoeffAllU, Nat.zero_add]; ac_rfl
        | succ c' ihc =>
          conv => lhs; unfold natSumUpTo
          rw [ihc]
          simp only [mixedNewtonCoeffAllU, Nat.add_mul]
          conv => rhs; lhs; unfold natSumUpTo
          dsimp only; simp only [Nat.mul_add]; ac_rfl
      cases t0 with
      | zero =>
        simp only [Nat.add_zero, Nat.pow_zero, Nat.one_mul, laurentInterpBinom_zero_right]
        rw [hsbp (m * T) (fun r => hasseNodePolyAllU T P r zv 0)]
        have hterm0 : ∀ r : Nat, r < m * T ->
            mixedNodeAllU T P r * hasseNodePolyAllU T P r zv 0 + hasseNodePolyAllU T P (r + 1) zv 0 =
              zv * hasseNodePolyAllU T P r zv 0 := by
          intro r hr_lt
          have hle := hle_blk r (by omega)
          simp only [hasseNodePolyAllU, ← Nat.add_mul]
          rw [show mixedNodeAllU T P r + (zv - mixedNodeAllU T P r) = zv by omega]
        have htop0 : mixedNodeAllU T P (m * T) = zv := by simpa [zv] using heq_blk m 0 hT
        have hrew_sum :
            natSumUpTo (m * T) (fun r =>
              mixedNewtonCoeffAllU T P x' r *
                (mixedNodeAllU T P r * hasseNodePolyAllU T P r zv 0 + hasseNodePolyAllU T P (r + 1) zv 0)) +
              mixedNewtonCoeffAllU T P x' (m * T) * (mixedNodeAllU T P (m * T) * hasseNodePolyAllU T P (m * T) zv 0) =
            zv * natSumUpTo (m * T + 1)
              (fun r => mixedNewtonCoeffAllU T P x' r * hasseNodePolyAllU T P r zv 0) := by
          rw [natSumUpTo_congr_w15 (m * T) _
              (fun r => zv * (mixedNewtonCoeffAllU T P x' r * hasseNodePolyAllU T P r zv 0))
              (fun r hr => by rw [hterm0 r hr]; ac_rfl),
              ← natSumUpTo_mul_left_w15 zv, htop0]
          conv => rhs; rhs; unfold natSumUpTo
          rw [Nat.mul_add]; congr 1; ac_rfl
        have ih0 := ihx 0 hT
        simp only [Nat.add_zero, Nat.pow_zero, Nat.one_mul, laurentInterpBinom_zero_right] at ih0
        rw [hrew_sum, ih0, Nat.pow_succ, Nat.mul_comm]
      | succ t' =>
        let c := m * T + (t' + 1)
        change zv ^ (t' + 1) * natSumUpTo (c + 1)
            (fun r => mixedNewtonCoeffAllU T P (x' + 1) r * hasseNodePolyAllU T P r zv (t' + 1)) =
          laurentInterpBinom (x' + 1) (t' + 1) * zv ^ (x' + 1)
        rw [hsbp c (fun r => hasseNodePolyAllU T P r zv (t' + 1))]
        have hterm_s : ∀ r : Nat, r < c ->
            mixedNodeAllU T P r * hasseNodePolyAllU T P r zv (t' + 1) +
              hasseNodePolyAllU T P (r + 1) zv (t' + 1) =
            hasseNodePolyAllU T P r zv t' + zv * hasseNodePolyAllU T P r zv (t' + 1) := by
          intro r hr_lt
          have hle := hle_blk r (by dsimp [c] at hr_lt; generalize m * T = MT at hr_lt ⊢; omega)
          simp only [hasseNodePolyAllU]
          have hcomb : mixedNodeAllU T P r * hasseNodePolyAllU T P r zv (t' + 1) +
              (zv - mixedNodeAllU T P r) * hasseNodePolyAllU T P r zv (t' + 1) =
            zv * hasseNodePolyAllU T P r zv (t' + 1) := by
            rw [← Nat.add_mul, show mixedNodeAllU T P r + (zv - mixedNodeAllU T P r) = zv by omega]
          calc
            mixedNodeAllU T P r * hasseNodePolyAllU T P r zv (t' + 1) +
                (hasseNodePolyAllU T P r zv t' + (zv - mixedNodeAllU T P r) * hasseNodePolyAllU T P r zv (t' + 1))
                = hasseNodePolyAllU T P r zv t' +
                    (mixedNodeAllU T P r * hasseNodePolyAllU T P r zv (t' + 1) +
                     (zv - mixedNodeAllU T P r) * hasseNodePolyAllU T P r zv (t' + 1)) := by ac_rfl
            _ = hasseNodePolyAllU T P r zv t' + zv * hasseNodePolyAllU T P r zv (t' + 1) := by rw [hcomb]
        have htop_c : mixedNodeAllU T P c = zv := by simpa [c, zv] using heq_blk m (t' + 1) ht0
        have hsplit_sum : ∀ (n : Nat) (f1 f2 : Nat -> Nat),
            natSumUpTo n (fun r => f1 r + f2 r) = natSumUpTo n f1 + natSumUpTo n f2 := by
          intro n f1 f2; induction n with
          | zero => rfl
          | succ n' ihn => simp only [natSumUpTo, ihn]; omega
        have hrew_sum :
            natSumUpTo c (fun r =>
              mixedNewtonCoeffAllU T P x' r *
                (mixedNodeAllU T P r * hasseNodePolyAllU T P r zv (t' + 1) +
                 hasseNodePolyAllU T P (r + 1) zv (t' + 1))) +
              mixedNewtonCoeffAllU T P x' c * (mixedNodeAllU T P c * hasseNodePolyAllU T P c zv (t' + 1)) =
            natSumUpTo c (fun r => mixedNewtonCoeffAllU T P x' r * hasseNodePolyAllU T P r zv t') +
              zv * natSumUpTo (c + 1)
                (fun r => mixedNewtonCoeffAllU T P x' r * hasseNodePolyAllU T P r zv (t' + 1)) := by
          rw [natSumUpTo_congr_w15 c _
              (fun r => mixedNewtonCoeffAllU T P x' r * hasseNodePolyAllU T P r zv t' +
                zv * (mixedNewtonCoeffAllU T P x' r * hasseNodePolyAllU T P r zv (t' + 1)))
              (fun r hr => by rw [hterm_s r hr, Nat.mul_add]; ac_rfl),
              hsplit_sum c, ← natSumUpTo_mul_left_w15 zv, htop_c]
          conv => rhs; rhs; rhs; unfold natSumUpTo
          rw [Nat.mul_add]
          have hc_mul : mixedNewtonCoeffAllU T P x' c * (zv * hasseNodePolyAllU T P c zv (t' + 1)) =
              zv * (mixedNewtonCoeffAllU T P x' c * hasseNodePolyAllU T P c zv (t' + 1)) := by ac_rfl
          rw [hc_mul, Nat.add_assoc]
        have hc_eq : c = m * T + t' + 1 := by dsimp [c]; omega
        have ih_t' := ihx t' (by omega)
        have ih_t1 := ihx (t' + 1) ht0
        rw [hrew_sum, Nat.mul_add (zv ^ (t' + 1))]
        have hp_t : zv ^ (t' + 1) * natSumUpTo c
              (fun r => mixedNewtonCoeffAllU T P x' r * hasseNodePolyAllU T P r zv t') =
            zv * (laurentInterpBinom x' t' * zv ^ x') := by
          rw [Nat.pow_succ zv t', Nat.mul_comm (zv ^ t') zv, Nat.mul_assoc zv, hc_eq, ih_t']
        have hp_t1 : zv ^ (t' + 1) * (zv * natSumUpTo (c + 1)
              (fun r => mixedNewtonCoeffAllU T P x' r * hasseNodePolyAllU T P r zv (t' + 1))) =
            zv * (laurentInterpBinom x' (t' + 1) * zv ^ x') := by
          calc
            zv ^ (t' + 1) * (zv * natSumUpTo (c + 1)
                (fun r => mixedNewtonCoeffAllU T P x' r * hasseNodePolyAllU T P r zv (t' + 1)))
                = zv * (zv ^ (t' + 1) * natSumUpTo (m * T + (t' + 1) + 1)
                    (fun r => mixedNewtonCoeffAllU T P x' r * hasseNodePolyAllU T P r zv (t' + 1))) := by
              dsimp [c]; ac_rfl
            _ = zv * (laurentInterpBinom x' (t' + 1) * zv ^ x') := by rw [ih_t1]
        rw [hp_t, hp_t1]
        have hpas : laurentInterpBinom (x' + 1) (t' + 1) =
            laurentInterpBinom x' t' + laurentInterpBinom x' (t' + 1) := by
          simp [laurentInterpBinom]
        rw [hpas, Nat.add_mul, Nat.pow_succ zv x']; ac_rfl
  exact fun x => hall_t x t htT

private theorem mixedNewtonCoeffAllU_mono_and_unit (T P : Nat) (_hT : T ≥ 1) (hP : P ≥ 1) :
    (∀ x y r : Nat, x ≤ y -> mixedNewtonCoeffAllU T P x r ≤ mixedNewtonCoeffAllU T P y r) ∧
    (∀ r x : Nat, r ≤ x -> mixedNewtonCoeffAllU T P x r ≥ 1) ∧
    (∀ x r : Nat, x < r -> mixedNewtonCoeffAllU T P x r = 0) ∧
    (∀ x : Nat, mixedNewtonCoeffAllU T P x x = 1) := by
  have hm_pos : ∀ r : Nat, mixedNodeAllU T P r ≥ 1 :=
    fun r => nat_pow_pos_of_pos P hP (r / T)
  have hstep : ∀ x r : Nat, mixedNewtonCoeffAllU T P x r ≤ mixedNewtonCoeffAllU T P (x + 1) r := by
    intro x r; cases r with
    | zero =>
      simp only [mixedNewtonCoeffAllU]
      simpa using Nat.mul_le_mul_right (mixedNewtonCoeffAllU T P x 0) (hm_pos 0)
    | succ r' =>
      simp only [mixedNewtonCoeffAllU]
      have hm := Nat.mul_le_mul_right (mixedNewtonCoeffAllU T P x (r' + 1)) (hm_pos (r' + 1))
      rw [Nat.one_mul] at hm; omega
  have hmono : ∀ x d r : Nat, mixedNewtonCoeffAllU T P x r ≤ mixedNewtonCoeffAllU T P (x + d) r := by
    intro x d r; induction d with
    | zero => exact Nat.le_refl _
    | succ d' ih => rw [Nat.add_succ]; exact Nat.le_trans ih (hstep (x + d') r)
  have hzero_diag : ∀ x : Nat,
      mixedNewtonCoeffAllU T P x x = 1 ∧ ∀ r : Nat, x < r -> mixedNewtonCoeffAllU T P x r = 0 := by
    intro x; induction x with
    | zero =>
      refine ⟨rfl, ?_⟩
      intro r hr; cases r with
      | zero => omega
      | succ _ => rfl
    | succ x' ih =>
      refine ⟨?_, ?_⟩
      · simp only [mixedNewtonCoeffAllU, ih.1, ih.2 (x' + 1) (Nat.lt_succ_self x'),
                   Nat.mul_zero, Nat.add_zero]
      · intro r hr; cases r with
        | zero => omega
        | succ r' =>
          simp only [mixedNewtonCoeffAllU, ih.2 r' (by omega), ih.2 (r' + 1) (by omega),
                     Nat.mul_zero, Nat.add_zero]
  refine ⟨fun x y r hle => by simpa [show x + (y - x) = y by omega] using hmono x (y - x) r,
          fun r x hle => by
            have h1 : mixedNewtonCoeffAllU T P r r = 1 := (hzero_diag r).1
            have hm := hmono r (x - r) r
            rw [h1, show r + (x - r) = x by omega] at hm; exact hm,
          fun x r hlt => (hzero_diag x).2 r hlt,
          fun x => (hzero_diag x).1⟩

/--
  Theorem W15.2a (`laurent_all_blocks_arbitrary_U_confluent_divisibility_and_majorant`,
  `zero custom axioms`):
  Unified Arbitrary-`U` (`∀ U ≥ 2, ∀ T ≥ 1, ∀ u ≥ 1`) All-Block Confluent Laurent Factorization
  & Divisibility on `(U * T) × (U * T)`, Pairwise `(2^((b - a)*u) - 1)^(T^2)` & Quadratic
  `(2^u - 1)^((U*(U-1)/2)*T^2)` Divisibility, Strict Confluent-Reduced Majorant Bound, Unit-Grid
  Exactness, & Universal `∀ U ≥ 4` Factorial Dominance (`confluentFactorAllU U T u > (U * T)!`,
  `Branch P3.3`, `W15_H2`).
-/
theorem laurent_all_blocks_arbitrary_U_confluent_divisibility_and_majorant :
    (∀ (U W K T u : Nat) (rows : Fin (U * T) -> Nat × Nat),
      U ≥ 2 -> T ≥ 1 -> u ≥ 1 ->
      let M0 : Fin (U * T) -> Fin (U * T) -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2
          (laurentColsAllU U T u j).1 (laurentColsAllU U T u j).2 : Int)
      let A_newton : Fin (U * T) -> Fin (U * T) -> Int := fun i j =>
        Int.ofNat (mixedNewtonCoeffAllU T (2 ^ u) ((rows i).1 * W + (rows i).2 * K) j.val)
      intDet (U * T) M0 = Int.ofNat (confluentFactorAllU U T u) * intDet (U * T) A_newton ∧
      ((confluentFactorAllU U T u : Nat) : Int) ∣ intDet (U * T) M0) ∧
    (∀ U T u : Nat, U ≥ 2 -> T ≥ 1 -> u ≥ 1 ->
      (∀ a b : Nat, a < b -> b < U ->
        (2 ^ ((b - a) * u) - 1) ^ (T * T) ∣ confluentFactorAllU U T u) ∧
      (2 ^ u - 1) ^ (triNumNat U * (T * T)) ∣ confluentFactorAllU U T u) ∧
    (∀ (U W K T u X_max : Nat) (rows : Fin (U * T) -> Nat × Nat),
      U ≥ 2 -> T ≥ 1 -> u ≥ 1 -> X_max ≥ U * T ->
      (∀ i : Fin (U * T), (rows i).1 * W + (rows i).2 * K ≤ X_max) ->
      let M0 : Fin (U * T) -> Fin (U * T) -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2
          (laurentColsAllU U T u j).1 (laurentColsAllU U T u j).2 : Int)
      let redProd := confluentFactorAllU U T u *
        colBoundProdPrefix (U * T) (fun j => mixedNewtonCoeffAllU T (2 ^ u) X_max j.val) (U * T)
      let rawProd := colBoundProdPrefix (U * T)
        (fun j => laurentInterpBinom X_max (laurentColsAllU U T u j).1 *
          2 ^ (X_max * (laurentColsAllU U T u j).2)) (U * T)
      (intDet (U * T) M0).natAbs ≤ natFact (U * T) * redProd ∧
      redProd < rawProd) ∧
    (∀ U T u : Nat, U ≥ 2 -> T ≥ 1 -> u ≥ 1 ->
      let M0_unit : Fin (U * T) -> Fin (U * T) -> Int := fun i j =>
        (laurentZeroGapIntEntry 1 1 i.val 0
          (laurentColsAllU U T u j).1 (laurentColsAllU U T u j).2 : Int)
      intDet (U * T) M0_unit = Int.ofNat (confluentFactorAllU U T u)) ∧
    (confluentFactorAllU 5 2 1 = 174624106178537853090728509440000 ∧
     natFact 10 = 3628800 ∧
     ∀ U T u : Nat, U ≥ 4 -> T ≥ 1 -> u ≥ 1 ->
       confluentFactorAllU U T u > natFact (U * T)) := by
  have hcoreU : ∀ (U T u : Nat), U ≥ 1 -> T ≥ 1 -> u ≥ 1 ->
      let P := 2 ^ u
      let U_nat : Fin (U * T) -> Fin (U * T) -> Nat := fun r c =>
        let m := c.val / T
        let t := c.val % T
        (P ^ m) ^ t * hasseNodePolyAllU T P r.val (P ^ m) t
      (∀ r c : Fin (U * T), c.val < r.val -> U_nat r c = 0) ∧
      colBoundProdPrefix (U * T) (fun c => U_nat c c) (U * T) = confluentFactorAllU U T u ∧
      (∀ (x : Nat) (c : Fin (U * T)),
        natSumUpTo (U * T) (fun r =>
          if hr : r < U * T then mixedNewtonCoeffAllU T P x r * U_nat ⟨r, hr⟩ c else 0) =
        laurentInterpBinom x (laurentColsAllU U T u c).1 *
          2 ^ (x * (laurentColsAllU U T u c).2)) := by
    intro U T u hU hT hu; dsimp only
    let P := 2 ^ u
    have hP_ge1 : P ≥ 1 := nat_pow_pos_of_pos 2 (by decide) u
    let U_nat : Fin (U * T) -> Fin (U * T) -> Nat := fun r c =>
      let m := c.val / T
      let t := c.val % T
      (P ^ m) ^ t * hasseNodePolyAllU T P r.val (P ^ m) t
    have hc_div : ∀ c : Fin (U * T),
        c.val % T < T ∧ (c.val / T) * T + c.val % T = c.val := by
      intro c
      exact ⟨Nat.mod_lt c.val hT, by rw [Nat.mul_comm]; exact Nat.div_add_mod c.val T⟩
    have hup_n : ∀ r c : Fin (U * T), c.val < r.val -> U_nat r c = 0 := by
      intro r c hlt
      rcases hc_div c with ⟨htT, hceq⟩
      rcases mixedNewtonAllU_hasse_col_identity T P hT hP_ge1 (c.val / T) (c.val % T) htT with ⟨hz, _, _⟩
      dsimp [U_nat]; rw [hz r.val (by omega), Nat.mul_zero]
    have hdiag_c : ∀ c : Fin (U * T),
        U_nat c c = P ^ ((c.val / T) * (c.val % T)) * (blockNodeDiffProd P (c.val / T) (c.val / T)) ^ T := by
      intro c
      rcases hc_div c with ⟨htT, hceq⟩
      rcases mixedNewtonAllU_hasse_col_identity T P hT hP_ge1 (c.val / T) (c.val % T) htT with ⟨_, hd, _⟩
      rw [hceq] at hd
      dsimp [U_nat]; rw [hd, pow_pow_eq_mul_w5 P (c.val / T) (c.val % T)]
    have hprod_blocks : ∀ m : Nat, m ≤ U ->
        colBoundProdPrefix (U * T) (fun c => U_nat c c) (m * T) = confluentFactorAllUAux T P m := by
      intro m hmU; induction m with
      | zero => simp [confluentFactorAllUAux, colBoundProdPrefix]
      | succ m' ih =>
        have hblk_step : ∀ k : Nat, k ≤ T ->
            colBoundProdPrefix (U * T) (fun c => U_nat c c) (m' * T + k) =
              confluentFactorAllUAux T P m' *
                (P ^ (m' * triNumNat k) * (blockNodeDiffProd P m' m') ^ (k * T)) := by
          intro k hkT; induction k with
          | zero => simp [triNumNat, ih (Nat.le_of_lt hmU)]
          | succ k' ihk =>
            rw [Nat.add_succ]
            have hlt_UT : m' * T + k' < U * T := by
              have hm1 : (m' + 1) * T ≤ U * T := Nat.mul_le_mul_right T hmU
              rw [Nat.add_mul, Nat.one_mul] at hm1; omega
            simp only [colBoundProdPrefix, hlt_UT, dite_true, ihk (Nat.le_of_lt hkT)]
            rw [hdiag_c ⟨m' * T + k', hlt_UT⟩]
            have hdm : (m' * T + k') / T = m' := by
              have h1 := Nat.add_mul_div_right k' m' hT
              rwa [Nat.add_comm k' (m' * T), Nat.div_eq_of_lt hkT, Nat.zero_add] at h1
            have hmm : (m' * T + k') % T = k' := by
              have h1 := Nat.div_add_mod (m' * T + k') T
              rw [hdm, Nat.mul_comm T m'] at h1; omega
            dsimp only; rw [hdm, hmm]
            simp only [triNumNat]
            rw [Nat.mul_add m' (triNumNat k') k',
                Nat.pow_add P (m' * triNumNat k') (m' * k'),
                show (k' + 1) * T = k' * T + T by rw [Nat.add_mul, Nat.one_mul],
                Nat.pow_add (blockNodeDiffProd P m' m') (k' * T) T]
            ac_rfl
        have hend := hblk_step T (Nat.le_refl T)
        rw [show m' * T + T = (m' + 1) * T by rw [Nat.add_mul, Nat.one_mul]] at hend
        simpa [confluentFactorAllUAux, confluentBlockFactor] using hend
    refine ⟨hup_n, hprod_blocks U (Nat.le_refl U), ?_⟩
    intro x c
    rcases hc_div c with ⟨htT, hceq⟩
    rcases mixedNewtonAllU_hasse_col_identity T P hT hP_ge1 (c.val / T) (c.val % T) htT with ⟨_, _, hsum_id⟩
    have htrunc_n : ∀ d : Nat, c.val + 1 + d ≤ U * T ->
        natSumUpTo (c.val + 1 + d) (fun r =>
          if hr : r < U * T then mixedNewtonCoeffAllU T P x r * U_nat ⟨r, hr⟩ c else 0) =
        natSumUpTo (c.val + 1) (fun r =>
          if hr : r < U * T then mixedNewtonCoeffAllU T P x r * U_nat ⟨r, hr⟩ c else 0) := by
      intro d hd; induction d with
      | zero => rfl
      | succ d' ih =>
        rw [Nat.add_succ]
        have hlt : c.val + 1 + d' < U * T := hd
        conv => lhs; unfold natSumUpTo
        simp only [hlt, dite_true]
        rw [ih (by omega), hup_n ⟨c.val + 1 + d', hlt⟩ c (by dsimp; omega), Nat.mul_zero, Nat.add_zero]
    have htr := htrunc_n (U * T - (c.val + 1)) (by have := c.isLt; omega)
    rw [show c.val + 1 + (U * T - (c.val + 1)) = U * T by have := c.isLt; omega] at htr
    rw [htr]
    have hcongr : natSumUpTo (c.val + 1) (fun r =>
          if hr : r < U * T then mixedNewtonCoeffAllU T P x r * U_nat ⟨r, hr⟩ c else 0) =
        (P ^ (c.val / T)) ^ (c.val % T) * natSumUpTo (c.val + 1)
          (fun r => mixedNewtonCoeffAllU T P x r * hasseNodePolyAllU T P r (P ^ (c.val / T)) (c.val % T)) := by
      rw [natSumUpTo_mul_left_w15 ((P ^ (c.val / T)) ^ (c.val % T))]
      apply natSumUpTo_congr_w15; intro r hr_lt
      have hrUT : r < U * T := by have := c.isLt; omega
      simp only [hrUT, dite_true]; dsimp [U_nat]; ac_rfl
    have hsum_c := hsum_id x
    rw [hceq] at hsum_c
    rw [hcongr, hsum_c]
    unfold laurentColsAllU; dsimp only [P]
    rw [pow_pow_eq_mul_w5 2 u (c.val / T), pow_pow_eq_mul_w5 2 (u * (c.val / T)) x,
        show u * (c.val / T) * x = x * (c.val / T * u) by ac_rfl]
  have hpart1 : ∀ (U W K T u : Nat) (rows : Fin (U * T) -> Nat × Nat),
      U ≥ 2 -> T ≥ 1 -> u ≥ 1 ->
      let M0 : Fin (U * T) -> Fin (U * T) -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2
          (laurentColsAllU U T u j).1 (laurentColsAllU U T u j).2 : Int)
      let A_newton : Fin (U * T) -> Fin (U * T) -> Int := fun i j =>
        Int.ofNat (mixedNewtonCoeffAllU T (2 ^ u) ((rows i).1 * W + (rows i).2 * K) j.val)
      intDet (U * T) M0 = Int.ofNat (confluentFactorAllU U T u) * intDet (U * T) A_newton ∧
      ((confluentFactorAllU U T u : Nat) : Int) ∣ intDet (U * T) M0 := by
    intro U W K T u rows hU2 hT hu; dsimp only
    rcases hcoreU U T u (by omega) hT hu with ⟨hup_n, hprod_n, hmat_n⟩
    let P := 2 ^ u
    let A_newton : Fin (U * T) -> Fin (U * T) -> Int := fun i j =>
      Int.ofNat (mixedNewtonCoeffAllU T P ((rows i).1 * W + (rows i).2 * K) j.val)
    let U_int : Fin (U * T) -> Fin (U * T) -> Int := fun r c =>
      Int.ofNat ((P ^ (c.val / T)) ^ (c.val % T) * hasseNodePolyAllU T P r.val (P ^ (c.val / T)) (c.val % T))
    have hup_i : ∀ r c : Fin (U * T), c.val < r.val -> U_int r c = 0 := by
      intro r c hlt
      have h0 := hup_n r c hlt; dsimp only at h0; dsimp only [U_int, P]; rw [h0]; rfl
    have hM0_eq : (fun i j : Fin (U * T) =>
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2
          (laurentColsAllU U T u j).1 (laurentColsAllU U T u j).2 : Int)) =
        (fun i j : Fin (U * T) => intSumPrefix (U * T) (fun r => A_newton i r * U_int r j) (U * T)) := by
      funext i j
      let x := (rows i).1 * W + (rows i).2 * K
      have hst : ∀ m : Nat, m ≤ U * T ->
          intSumPrefix (U * T) (fun r => A_newton i r * U_int r j) m =
            Int.ofNat (natSumUpTo m (fun r =>
              if hr : r < U * T then
                mixedNewtonCoeffAllU T P x r *
                  ((P ^ (j.val / T)) ^ (j.val % T) * hasseNodePolyAllU T P r (P ^ (j.val / T)) (j.val % T))
              else 0)) := by
        intro m hm; induction m with
        | zero => rfl
        | succ m' ih =>
          have hm_lt : m' < U * T := hm
          conv => lhs; unfold intSumPrefix
          conv => rhs; rhs; unfold natSumUpTo
          simp only [hm_lt, dite_true]; rw [ih (Nat.le_of_lt hm)]; rfl
      rw [hst (U * T) (Nat.le_refl _), hmat_n x j]; rfl
    have hdiag_i : ∀ m : Nat, m ≤ U * T ->
        intDiagProdPrefix_def_w15 (U * T) U_int m =
          Int.ofNat (colBoundProdPrefix (U * T) (fun c =>
            (P ^ (c.val / T)) ^ (c.val % T) *
              hasseNodePolyAllU T P c.val (P ^ (c.val / T)) (c.val % T)) m) := by
      intro m hm; induction m with
      | zero => rfl
      | succ m' ih =>
        have hm_lt : m' < U * T := hm
        conv => lhs; unfold intDiagProdPrefix_def_w15
        conv => rhs; rhs; unfold colBoundProdPrefix
        simp only [hm_lt, dite_true]; rw [ih (Nat.le_of_lt hm)]; rfl
    rw [hM0_eq, intDet_mul_upper_tri_w15 (U * T) A_newton U_int hup_i,
        hdiag_i (U * T) (Nat.le_refl _), hprod_n]
    exact ⟨rfl, ⟨intDet (U * T) A_newton, rfl⟩⟩
  refine ⟨hpart1, ?_, ?_, ?_, ?_⟩
  · -- Part 2: Pairwise `(2^((b - a)*u) - 1)^(T*T)` and quadratic `(2^u - 1)^(triNumNat U * (T*T))` divisibility
    intro U T u hU2 hT hu
    let P := 2 ^ u
    have hP_ge2 : P ≥ 2 := by dsimp [P]; simpa using pow2_mono_nat hu
    have hpow_dvd : ∀ x y k : Nat, x ∣ y -> x ^ k ∣ y ^ k := by
      intro x y k ⟨q, hq⟩
      rw [hq, mul_pow_w15c]
      exact ⟨q ^ k, rfl⟩
    have hsub_fact : ∀ a b : Nat, a ≤ b -> P ^ b - P ^ a = P ^ a * (P ^ (b - a) - 1) := by
      intro a b hab
      conv => lhs; lhs; rw [show b = a + (b - a) by omega, Nat.pow_add]
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    have hpm1_dvd_pow : ∀ d : Nat, P - 1 ∣ P ^ d - 1 := by
      intro d; induction d with
      | zero => exact ⟨0, by simp⟩
      | succ d' ih =>
        rcases ih with ⟨q, hq⟩
        have hstep : P ^ (d' + 1) - 1 = P * (P ^ d' - 1) + (P - 1) := by
          rw [Nat.pow_succ, Nat.mul_comm (P ^ d') P]
          have hp1 : P ^ d' ≥ 1 := nat_pow_pos_of_pos P (by omega) d'
          rw [Nat.mul_sub_left_distrib, Nat.mul_one]
          have hm : P ≤ P * P ^ d' := by simpa using Nat.mul_le_mul_left P hp1
          omega
        rw [hstep, hq]
        exact ⟨P * q + 1, by rw [Nat.mul_add, Nat.mul_one]; ac_rfl⟩
    refine ⟨?_, ?_⟩
    · intro a b hab hbU
      have ha_dvd_b : P ^ (b - a) - 1 ∣ blockNodeDiffProd P b b := by
        have hst : ∀ k : Nat, a < k -> k ≤ b -> P ^ (b - a) - 1 ∣ blockNodeDiffProd P b k := by
          intro k hak hkb; induction k with
          | zero => omega
          | succ k' ih =>
            simp only [blockNodeDiffProd]
            by_cases heq : a = k'
            · subst heq
              rw [hsub_fact a b (Nat.le_of_lt hab)]
              exact ⟨blockNodeDiffProd P b a * P ^ a, by ac_rfl⟩
            · rcases ih (by omega) (Nat.le_of_lt hkb) with ⟨q, hq⟩
              rw [hq]; exact ⟨q * (P ^ b - P ^ k'), by ac_rfl⟩
        exact hst b hab (Nat.le_refl b)
      have hb_dvd_blk : (P ^ (b - a) - 1) ^ (T * T) ∣ confluentBlockFactor T P b := by
        rcases hpow_dvd _ _ (T * T) ha_dvd_b with ⟨q, hq⟩
        unfold confluentBlockFactor; rw [hq]
        exact ⟨P ^ (b * triNumNat T) * q, by ac_rfl⟩
      have hblk_dvd_all : ∀ m : Nat, b < m -> confluentBlockFactor T P b ∣ confluentFactorAllUAux T P m := by
        intro m hbm; induction m with
        | zero => omega
        | succ m' ihm =>
          simp only [confluentFactorAllUAux]
          by_cases heq : b = m'
          · subst heq; exact ⟨confluentFactorAllUAux T P b, Nat.mul_comm _ _⟩
          · rcases ihm (by omega) with ⟨q, hq⟩
            rw [hq]; exact ⟨q * confluentBlockFactor T P m', by ac_rfl⟩
      have hd := Nat.dvd_trans hb_dvd_blk (hblk_dvd_all U hbU)
      have hexp : P ^ (b - a) = 2 ^ ((b - a) * u) := by
        dsimp [P]; rw [pow_pow_eq_mul_w5 2 u (b - a), Nat.mul_comm]
      rwa [hexp] at hd
    · have hdiff_pm1 : ∀ m k : Nat, k ≤ m -> (P - 1) ^ k ∣ blockNodeDiffProd P m k := by
        intro m k hkm; induction k with
        | zero => exact ⟨1, by simp [blockNodeDiffProd]⟩
        | succ k' ih =>
          rcases ih (Nat.le_of_lt hkm) with ⟨q1, hq1⟩
          have hd2 : P - 1 ∣ P ^ m - P ^ k' := by
            rw [hsub_fact k' m (Nat.le_of_lt hkm)]
            rcases hpm1_dvd_pow (m - k') with ⟨q2, hq2⟩
            rw [hq2]; exact ⟨P ^ k' * q2, by ac_rfl⟩
          rcases hd2 with ⟨q2, hq2⟩
          simp only [blockNodeDiffProd, Nat.pow_succ, hq1, hq2]
          exact ⟨q1 * q2, by ac_rfl⟩
      have hall_pm1 : ∀ m : Nat, (P - 1) ^ (triNumNat m * (T * T)) ∣ confluentFactorAllUAux T P m := by
        intro m; induction m with
        | zero => exact ⟨1, by simp [triNumNat, confluentFactorAllUAux]⟩
        | succ m' ih =>
          rcases ih with ⟨q1, hq1⟩
          rcases hpow_dvd _ _ (T * T) (hdiff_pm1 m' m' (Nat.le_refl m')) with ⟨q2, hq2⟩
          rw [pow_pow_eq_mul_w5 (P - 1) m' (T * T)] at hq2
          simp only [triNumNat, Nat.add_mul, confluentFactorAllUAux, confluentBlockFactor,
                     Nat.pow_add, hq1, hq2]
          exact ⟨q1 * P ^ (m' * triNumNat T) * q2, by ac_rfl⟩
      exact hall_pm1 U
  · -- Part 3: Strict confluent-reduced majorant bound
    intro U W K T u X_max rows hU2 hT hu hX hrows_le; dsimp only
    rcases hcoreU U T u (by omega) hT hu with ⟨_, hprod_n, hmat_n⟩
    let P := 2 ^ u
    have hP_ge2 : P ≥ 2 := by dsimp [P]; simpa using pow2_mono_nat hu
    have hP_ge1 : P ≥ 1 := by omega
    rcases mixedNewtonCoeffAllU_mono_and_unit T P hT hP_ge1 with ⟨hmono_c, hpos_c, _, _⟩
    have hdet_eq := (hpart1 U W K T u rows hU2 hT hu).1
    let A_newton : Fin (U * T) -> Fin (U * T) -> Int := fun i j =>
      Int.ofNat (mixedNewtonCoeffAllU T P ((rows i).1 * W + (rows i).2 * K) j.val)
    have hA_maj : (intDet (U * T) A_newton).natAbs ≤
        natFact (U * T) *
          colBoundProdPrefix (U * T) (fun j => mixedNewtonCoeffAllU T P X_max j.val) (U * T) :=
      intDet_natAbs_le_fact_mul_colProd (U * T) A_newton
        (fun j => mixedNewtonCoeffAllU T P X_max j.val)
        (fun i j => hmono_c _ X_max j.val (hrows_le i))
    have hbd_red :
        (intDet (U * T) (fun i j =>
          (laurentZeroGapIntEntry W K (rows i).1 (rows i).2
            (laurentColsAllU U T u j).1 (laurentColsAllU U T u j).2 : Int))).natAbs ≤
        natFact (U * T) * (confluentFactorAllU U T u *
          colBoundProdPrefix (U * T) (fun j => mixedNewtonCoeffAllU T P X_max j.val) (U * T)) := by
      rw [hdet_eq, Int.natAbs_mul]
      simp only [Int.ofNat_eq_natCast, Int.natAbs_natCast]
      have hm := Nat.mul_le_mul_left (confluentFactorAllU U T u) hA_maj
      rwa [show confluentFactorAllU U T u *
              (natFact (U * T) * colBoundProdPrefix (U * T) (fun j => mixedNewtonCoeffAllU T P X_max j.val) (U * T)) =
            natFact (U * T) * (confluentFactorAllU U T u *
              colBoundProdPrefix (U * T) (fun j => mixedNewtonCoeffAllU T P X_max j.val) (U * T)) by ac_rfl] at hm
    refine ⟨hbd_red, ?_⟩
    let U_nat : Fin (U * T) -> Fin (U * T) -> Nat := fun r c =>
      (P ^ (c.val / T)) ^ (c.val % T) * hasseNodePolyAllU T P r.val (P ^ (c.val / T)) (c.val % T)
    let f_red : Fin (U * T) -> Nat := fun c => U_nat c c * mixedNewtonCoeffAllU T P X_max c.val
    let f_raw : Fin (U * T) -> Nat := fun c =>
      laurentInterpBinom X_max (laurentColsAllU U T u c).1 *
        2 ^ (X_max * (laurentColsAllU U T u c).2)
    have hprod_mul : ∀ m : Nat, m ≤ U * T ->
        colBoundProdPrefix (U * T) (fun c => U_nat c c) m *
          colBoundProdPrefix (U * T) (fun c => mixedNewtonCoeffAllU T P X_max c.val) m =
        colBoundProdPrefix (U * T) f_red m := by
      intro m hm; induction m with
      | zero => rfl
      | succ m' ih =>
        have hm_lt : m' < U * T := hm
        simp only [colBoundProdPrefix, hm_lt, dite_true, ← ih (Nat.le_of_lt hm)]
        dsimp [f_red]; ac_rfl
    rw [← hprod_n, hprod_mul (U * T) (Nat.le_refl _)]
    have hdiff_pos : ∀ m k : Nat, k ≤ m -> blockNodeDiffProd P m k ≥ 1 := by
      intro m k hkm; induction k with
      | zero => exact Nat.le_refl 1
      | succ k' ih =>
        have hp_lt : P ^ k' < P ^ m := by
          have h1 : P ^ (k' + 1) ≤ P ^ m := nat_pow_mono_exp_pos P (k' + 1) m hP_ge1 hkm
          rw [Nat.pow_succ] at h1
          have hp_pos := nat_pow_pos_of_pos P hP_ge1 k'
          have hm2 := Nat.mul_le_mul_left (P ^ k') hP_ge2
          omega
        simp only [blockNodeDiffProd]
        exact Nat.mul_le_mul (ih (Nat.le_of_lt hkm)) (by omega : 1 ≤ P ^ m - P ^ k')
    have hcf_pos : ∀ m : Nat, confluentFactorAllUAux T P m ≥ 1 := by
      intro m; induction m with
      | zero => exact Nat.le_refl 1
      | succ m' ih =>
        exact Nat.mul_le_mul ih (Nat.mul_le_mul
          (nat_pow_pos_of_pos P hP_ge1 _)
          (nat_pow_pos_of_pos _ (hdiff_pos m' m' (Nat.le_refl m')) _))
    have hUcc_pos : ∀ c : Fin (U * T), U_nat c c ≥ 1 := by
      intro c
      by_cases hz : U_nat c c = 0
      · exfalso
        have hp0 : ∀ d : Nat, c.val + 1 + d ≤ U * T ->
            colBoundProdPrefix (U * T) (fun j => U_nat j j) (c.val + 1 + d) = 0 := by
          intro d hd; induction d with
          | zero => simp only [colBoundProdPrefix, c.isLt, dite_true, hz, Nat.mul_zero]
          | succ d' ih =>
            rw [Nat.add_succ]
            have hlt : c.val + 1 + d' < U * T := hd
            simp only [colBoundProdPrefix, hlt, dite_true, ih (by omega), Nat.zero_mul]
        have hbad := hp0 (U * T - (c.val + 1)) (by have := c.isLt; omega)
        rw [show c.val + 1 + (U * T - (c.val + 1)) = U * T by have := c.isLt; omega, hprod_n] at hbad
        have hcpos : confluentFactorAllU U T u ≥ 1 := hcf_pos U
        omega
      · omega
    have hfred_pos : ∀ c : Fin (U * T), f_red c ≥ 1 := fun c =>
      Nat.mul_le_mul (hUcc_pos c) (hpos_c c.val X_max (by have := c.isLt; omega))
    have hsum_ge_one : ∀ (n idx : Nat) (g : Nat -> Nat), idx < n -> g idx ≤ natSumUpTo n g := by
      intro n idx g hlt; induction n with
      | zero => omega
      | succ n' ih =>
        simp only [natSumUpTo]; by_cases heq : idx = n'
        · subst heq; omega
        · have := ih (by omega); omega
    have hsum_ge_two : ∀ (n idx : Nat) (g : Nat -> Nat), 0 < idx -> idx < n ->
        g 0 + g idx ≤ natSumUpTo n g := by
      intro n idx g hpos hlt; induction n with
      | zero => omega
      | succ m_n ih =>
        simp only [natSumUpTo]; by_cases heq : idx = m_n
        · rw [heq] at hpos ⊢; have hg0 := hsum_ge_one m_n 0 g hpos; omega
        · have := ih (by omega); omega
    have hfred_le : ∀ c : Fin (U * T), f_red c ≤ f_raw c := by
      intro c; dsimp [f_raw]; rw [← hmat_n X_max c]
      have h1 := hsum_ge_one (U * T) c.val
        (fun r => if hr : r < U * T then mixedNewtonCoeffAllU T P X_max r * U_nat ⟨r, hr⟩ c else 0)
        c.isLt
      simp only [c.isLt, dite_true] at h1; dsimp [f_red]; rwa [Nat.mul_comm]
    have hT_lt_UT : T < U * T := by
      have hm : 2 * T ≤ U * T := Nat.mul_le_mul_right T hU2; omega
    let cT : Fin (U * T) := ⟨T, hT_lt_UT⟩
    have hfred_lt_cT : f_red cT < f_raw cT := by
      dsimp [f_raw]; rw [← hmat_n X_max cT]
      have h2 := hsum_ge_two (U * T) T
        (fun r => if hr : r < U * T then mixedNewtonCoeffAllU T P X_max r * U_nat ⟨r, hr⟩ cT else 0)
        hT hT_lt_UT
      have h0_UT : 0 < U * T := by omega
      simp only [h0_UT, hT_lt_UT, dite_true] at h2
      have hU0T : U_nat ⟨0, h0_UT⟩ cT = 1 := by
        dsimp [U_nat, cT]
        rw [Nat.mod_self, Nat.pow_zero, Nat.one_mul]; rfl
      have hc0_pos : mixedNewtonCoeffAllU T P X_max 0 ≥ 1 := hpos_c 0 X_max (Nat.zero_le _)
      rw [hU0T, Nat.mul_one] at h2
      change U_nat cT cT * mixedNewtonCoeffAllU T P X_max T < _
      dsimp only [cT] at h2 ⊢
      rw [Nat.mul_comm (U_nat ⟨T, hT_lt_UT⟩ ⟨T, hT_lt_UT⟩)]
      exact Nat.lt_of_lt_of_le (by omega) h2
    rcases colBoundProdPrefix_mono_pos_w15 (U * T) f_red f_raw hfred_pos hfred_le (U * T) (Nat.le_refl _) with
      ⟨_, hle_prod, heq_imp⟩
    change colBoundProdPrefix (U * T) f_red (U * T) < colBoundProdPrefix (U * T) f_raw (U * T)
    by_cases heq_p : colBoundProdPrefix (U * T) f_red (U * T) = colBoundProdPrefix (U * T) f_raw (U * T)
    · exfalso; have := heq_imp heq_p cT cT.isLt; omega
    · omega
  · -- Part 4: Unit-grid exactness (`rows i = (i, 0)`, `W = K = 1`)
    intro U T u hU2 hT hu; dsimp only
    let P := 2 ^ u
    have hP_ge1 : P ≥ 1 := nat_pow_pos_of_pos 2 (by decide) u
    rcases mixedNewtonCoeffAllU_mono_and_unit T P hT hP_ge1 with ⟨_, _, hup0, hdiag1⟩
    have hdet_eq := (hpart1 U 1 1 T u (fun i => (i.val, 0)) hU2 hT hu).1
    dsimp only at hdet_eq
    have hunit : intDet (U * T) (fun i j : Fin (U * T) =>
        Int.ofNat (mixedNewtonCoeffAllU T P (i.val * 1 + 0 * 1) j.val)) = 1 :=
      intDet_unit_lower_tri_w15 (U * T) _
        (fun i => by simp [hdiag1 i.val])
        (fun i j hij => by simp [hup0 i.val j.val hij])
    rw [hdet_eq, hunit, Int.mul_one]
  · -- Part 5: `confluentFactorAllU 5 2 1 = 422865326938521600 > 10!` & universal `∀ U ≥ 4, ∀ T ≥ 1, ∀ u ≥ 1` dominance
    refine ⟨by decide, by decide, ?_⟩
    intro U T u hU4 hT hu
    -- Step 5a: Monotonicity of `confluentFactorAllUAux T P U` in `P ≥ 2` (`2^u ≥ 2`):
    have hdiff_mono : ∀ (P : Nat), P ≥ 2 -> ∀ m k : Nat, k ≤ m ->
        blockNodeDiffProd 2 m k ≤ blockNodeDiffProd P m k := by
      intro P hP2 m k hkm; induction k with
      | zero => exact Nat.le_refl 1
      | succ k' ih =>
        simp only [blockNodeDiffProd]
        apply Nat.mul_le_mul (ih (Nat.le_of_lt hkm))
        have hf2 : 2 ^ m - 2 ^ k' = 2 ^ k' * (2 ^ (m - k') - 1) := by
          conv => lhs; lhs; rw [show m = k' + (m - k') by omega, Nat.pow_add]
          rw [Nat.mul_sub_left_distrib, Nat.mul_one]
        have hfP : P ^ m - P ^ k' = P ^ k' * (P ^ (m - k') - 1) := by
          conv => lhs; lhs; rw [show m = k' + (m - k') by omega, Nat.pow_add]
          rw [Nat.mul_sub_left_distrib, Nat.mul_one]
        rw [hf2, hfP]
        have hp1 := pow_mono_base_w15c 2 P hP2 k'
        have hp2 := pow_mono_base_w15c 2 P hP2 (m - k')
        exact Nat.mul_le_mul hp1 (by omega)
    have haux_mono : ∀ (P : Nat), P ≥ 2 -> ∀ m : Nat,
        confluentFactorAllUAux T 2 m ≤ confluentFactorAllUAux T P m := by
      intro P hP2 m; induction m with
      | zero => exact Nat.le_refl 1
      | succ m' ih =>
        exact Nat.mul_le_mul ih (Nat.mul_le_mul
          (pow_mono_base_w15c 2 P hP2 _)
          (pow_mono_base_w15c _ _ (hdiff_mono P hP2 m' m' (Nat.le_refl m')) (T * T)))
    have hP2 : 2 ^ u ≥ 2 := by simpa using pow2_mono_nat hu
    have hge_u1 : confluentFactorAllU U T 1 ≤ confluentFactorAllU U T u := by
      simpa [confluentFactorAllU] using haux_mono (2 ^ u) hP2 U
    -- Step 5b: Prove `confluentFactorAllUAux T 2 U > natFact (U * T)` by induction on `U ≥ 4`:
    have hfact_le_pow : ∀ n : Nat, natFact n ≤ n ^ n := by
      intro n; induction n with
      | zero => decide
      | succ n' ih =>
        simp only [natFact, Nat.pow_succ]
        have h1 : natFact n' ≤ (n' + 1) ^ n' :=
          Nat.le_trans ih (pow_mono_base_w15c n' (n' + 1) (Nat.le_succ n') n')
        rw [Nat.mul_comm (n' + 1)]
        exact Nat.mul_le_mul_right (n' + 1) h1
    have hbase4 : confluentFactorAllUAux T 2 4 > natFact (4 * T) := by
      have hcf4 : confluentFactorAllUAux T 2 4 = 2 ^ (6 * triNumNat T) * 1008 ^ (T * T) := by
        have hb0 : confluentBlockFactor T 2 0 = 1 := by simp [confluentBlockFactor, blockNodeDiffProd]
        have hb1 : confluentBlockFactor T 2 1 = 2 ^ triNumNat T := by
          simp [confluentBlockFactor, blockNodeDiffProd]
        have hb2 : confluentBlockFactor T 2 2 = 2 ^ (2 * triNumNat T) * 6 ^ (T * T) := by
          unfold confluentBlockFactor
          have hd : blockNodeDiffProd 2 2 2 = 6 := rfl
          rw [hd]
        have hb3 : confluentBlockFactor T 2 3 = 2 ^ (3 * triNumNat T) * 168 ^ (T * T) := by
          unfold confluentBlockFactor
          have hd : blockNodeDiffProd 2 3 3 = 168 := rfl
          rw [hd]
        simp only [confluentFactorAllUAux, hb0, hb1, hb2, hb3, Nat.one_mul]
        have e2 : 2 ^ triNumNat T * 2 ^ (2 * triNumNat T) * 2 ^ (3 * triNumNat T) =
            2 ^ (6 * triNumNat T) := by
          rw [← Nat.pow_add, ← Nat.pow_add,
              show triNumNat T + 2 * triNumNat T + 3 * triNumNat T = 6 * triNumNat T by omega]
        have e1008 : 6 ^ (T * T) * 168 ^ (T * T) = 1008 ^ (T * T) := by
          rw [← mul_pow_w15c 6 168 (T * T)]
        calc
          2 ^ triNumNat T * (2 ^ (2 * triNumNat T) * 6 ^ (T * T)) *
              (2 ^ (3 * triNumNat T) * 168 ^ (T * T))
              = (2 ^ triNumNat T * 2 ^ (2 * triNumNat T) * 2 ^ (3 * triNumNat T)) *
                  (6 ^ (T * T) * 168 ^ (T * T)) := by ac_rfl
          _ = 2 ^ (6 * triNumNat T) * 1008 ^ (T * T) := by rw [e2, e1008]
      by_cases hT1 : T = 1
      · subst hT1; decide
      · have hT2 : T ≥ 2 := by omega
        have h256 : ∀ t : Nat, t ≥ 2 -> 256 * t ^ 4 < 1008 ^ t := by
          intro t ht; induction t with
          | zero => omega
          | succ t' iht =>
            by_cases ht1 : t' = 1
            · subst ht1; decide
            · have ih := iht (by omega)
              have ht4_step : (t' + 1) ^ 4 ≤ 16 * t' ^ 4 := by
                have h2t : t' + 1 ≤ 2 * t' := by omega
                calc (t' + 1) ^ 4 ≤ (2 * t') ^ 4 := pow_mono_base_w15c (t' + 1) (2 * t') h2t 4
                  _ = 16 * t' ^ 4 := by rw [mul_pow_w15c 2 t' 4]
              calc 256 * (t' + 1) ^ 4
                  ≤ 256 * (16 * t' ^ 4) := Nat.mul_le_mul_left 256 ht4_step
                _ = 16 * (256 * t' ^ 4) := by ac_rfl
                _ ≤ 1008 * (256 * t' ^ 4) := Nat.mul_le_mul_right _ (by decide)
                _ < 1008 * 1008 ^ t' := Nat.mul_lt_mul_of_pos_left ih (by decide)
                _ = 1008 ^ (t' + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
        have hpow_lt : ∀ (a b n : Nat), a < b -> a ^ (n + 1) < b ^ (n + 1) := by
          intro a b n hab; induction n with
          | zero => simpa using hab
          | succ n' ihn =>
            rw [Nat.pow_succ a (n' + 1), Nat.pow_succ b (n' + 1)]
            exact Nat.lt_of_le_of_lt
              (Nat.mul_le_mul_right a (Nat.le_of_lt ihn))
              (Nat.mul_lt_mul_of_pos_left hab (nat_pow_pos_of_pos b (by omega) (n' + 1)))
        have h4T_lt2 : (256 * T ^ 4) ^ T < (1008 ^ T) ^ T := by
          simpa [show (T - 1) + 1 = T by omega] using hpow_lt (256 * T ^ 4) (1008 ^ T) (T - 1) (h256 T hT2)
        have he1 : (4 * T) ^ (4 * T) = (256 * T ^ 4) ^ T := by
          rw [← pow_pow_eq_mul_w5 (4 * T) 4 T, mul_pow_w15c 4 T 4]
        have he2 : (1008 ^ T) ^ T = 1008 ^ (T * T) := pow_pow_eq_mul_w5 1008 T T
        have hle_f := hfact_le_pow (4 * T)
        have hp2_ge1 : 2 ^ (6 * triNumNat T) ≥ 1 := nat_pow_pos_of_pos 2 (by decide) _
        have hm_cf : 1008 ^ (T * T) ≤ 2 ^ (6 * triNumNat T) * 1008 ^ (T * T) := by
          simpa using Nat.mul_le_mul_right (1008 ^ (T * T)) hp2_ge1
        rw [hcf4]; omega
    have hfact_blk : ∀ (A k : Nat), k ≤ T ->
        natFact (A + k) ≤ natFact A * (A + T) ^ k := by
      intro A k hkT; induction k with
      | zero => simp
      | succ k' ih =>
        rw [Nat.add_succ]
        simp only [natFact, Nat.pow_succ]
        have h1 : A + k' + 1 ≤ A + T := by omega
        calc (A + k' + 1) * natFact (A + k')
            ≤ (A + T) * (natFact A * (A + T) ^ k') := Nat.mul_le_mul h1 (ih (Nat.le_of_lt hkT))
          _ = natFact A * ((A + T) ^ k' * (A + T)) := by ac_rfl
    have hind_U : ∀ d : Nat, confluentFactorAllUAux T 2 (4 + d) > natFact ((4 + d) * T) := by
      intro d; induction d with
      | zero => exact hbase4
      | succ d' ih =>
        let m := 4 + d'
        have hm4 : m ≥ 4 := by dsimp [m]; omega
        rw [show 4 + (d' + 1) = m + 1 by dsimp [m]; omega]
        simp only [confluentFactorAllUAux]
        have hdiff_lb : ∀ k : Nat, k ≤ m -> blockNodeDiffProd 2 m k ≥ (2 ^ (m - 1)) ^ k := by
          intro k hkm; induction k with
          | zero => exact Nat.le_refl 1
          | succ k' ihk =>
            simp only [blockNodeDiffProd, Nat.pow_succ]
            apply Nat.mul_le_mul (ihk (Nat.le_of_lt hkm))
            have hle_k : 2 ^ k' ≤ 2 ^ (m - 1) := nat_pow_mono_exp_pos 2 k' (m - 1) (by decide) (by omega)
            have he2 : 2 ^ m = 2 ^ (m - 1) + 2 ^ (m - 1) := by
              conv => lhs; rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]
              omega
            omega
        have hblk_lb : confluentBlockFactor T 2 m ≥ (2 ^ (m * (m - 1) * T)) ^ T := by
          unfold confluentBlockFactor
          have hp1 : 2 ^ (m * triNumNat T) ≥ 1 := nat_pow_pos_of_pos 2 (by decide) _
          have hd1 := pow_mono_base_w15c ((2 ^ (m - 1)) ^ m) (blockNodeDiffProd 2 m m)
            (hdiff_lb m (Nat.le_refl m)) (T * T)
          rw [pow_pow_eq_mul_w5 2 (m - 1) m, pow_pow_eq_mul_w5 2 ((m - 1) * m) (T * T),
              show (m - 1) * m * (T * T) = (m * (m - 1) * T) * T by ac_rfl,
              ← pow_pow_eq_mul_w5 2 (m * (m - 1) * T) T] at hd1
          exact Nat.le_trans hd1 (by simpa using Nat.mul_le_mul_right _ hp1)
        have h2m_gt : 2 ^ m > m + 1 := by
          have hst : ∀ q : Nat, 2 ^ (4 + q) > 5 + q := by
            intro q; induction q with
            | zero => decide
            | succ q' ihq =>
              rw [Nat.add_succ, Nat.pow_succ]
              have hp := nat_pow_pos_of_pos 2 (by decide) (4 + q')
              omega
          simpa [m, show 5 + d' = 4 + d' + 1 by omega] using hst d'
        have h2T_ge : 2 ^ T ≥ T := by
          have hst_t : ∀ t : Nat, 2 ^ t ≥ t := by
            intro t; induction t with
            | zero => decide
            | succ t' iht =>
              rw [Nat.pow_succ]
              have hp := nat_pow_pos_of_pos 2 (by decide) t'
              omega
          exact hst_t T
        have hexp_ge : m * (m - 1) * T ≥ m + T := by
          have hm3 : m * (m - 1) ≥ m + 8 := by
            have h1 : m - 1 ≥ 3 := by omega
            have h2 := Nat.mul_le_mul_left m h1
            omega
          have hmt := Nat.mul_le_mul_right T hm3
          rw [Nat.add_mul] at hmt
          have hmT : m * T ≥ m := by simpa using Nat.mul_le_mul_left m hT
          omega
        have hbase_gt : 2 ^ (m * (m - 1) * T) ≥ (m + 1) * T := by
          have hp_le := nat_pow_mono_exp_pos 2 (m + T) (m * (m - 1) * T) (by decide) hexp_ge
          rw [Nat.pow_add 2 m T] at hp_le
          have hm_gt := Nat.mul_le_mul (Nat.le_of_lt h2m_gt) h2T_ge
          omega
        have hblk_ge : confluentBlockFactor T 2 m ≥ ((m + 1) * T) ^ T :=
          Nat.le_trans (pow_mono_base_w15c ((m + 1) * T) _ hbase_gt T) hblk_lb
        have hcfb_pos : ((m + 1) * T) ^ T ≥ 1 :=
          nat_pow_pos_of_pos ((m + 1) * T) (Nat.mul_pos (by omega) hT) T
        have hf_step := hfact_blk (m * T) T (Nat.le_refl T)
        rw [← Nat.succ_mul m T] at hf_step
        have hm1_lt := Nat.mul_lt_mul_of_pos_right ih (by omega : 0 < ((m + 1) * T) ^ T)
        have hm2_le := Nat.mul_le_mul_left (confluentFactorAllUAux T 2 m) hblk_ge
        exact Nat.lt_of_le_of_lt hf_step (Nat.lt_of_lt_of_le hm1_lt hm2_le)
    have hu_gt := hind_U (U - 4)
    rw [show 4 + (U - 4) = U by omega] at hu_gt
    exact Nat.lt_of_lt_of_le hu_gt hge_u1

-- ----------------------------------------------------------------------------
-- Section 2B: Rank-3 `9 × 9` `(T = 3, U = 3)` Global `u = 1..9` Non-Vanishing,
--             Cone-Free `∀ u ≥ 1` Non-Vanishing Outside `(27 * w', 8 * k')`,
--             Multi-`u` Zero Ceiling & Asymptotic Sign Lock, + `(7, 11)` Double Flip
-- ----------------------------------------------------------------------------

private def slicePoly4CoeffInt (u k : Nat) : List Mono4 -> Int
  | [] => 0
  | (a, b, c, d, cf) :: tl =>
    (if a == 9 - k && b == k then cf * (((2 ^ c * 3 ^ d) ^ u : Nat) : Int) else 0) +
      slicePoly4CoeffInt u k tl

private abbrev slicePoly4CoeffFast (u k : Nat) (ms : List Mono4) : Int :=
  slicePoly4CoeffInt u k ms

private theorem slicePoly4CoeffFast_eq (u k : Nat) (_hu : u < 64) (ms : List Mono4) :
    slicePoly4CoeffFast u k ms = slicePoly4CoeffInt u k ms := rfl

private def evalSliceSum10Fast (W K u : Nat) : Int :=
  intSumPrefix 10 (fun k =>
    ((W ^ (9 - k.val) * K ^ k.val : Nat) : Int) * slicePoly4CoeffFast u k.val t3u3CorePoly) 10

/-- Non-leading `(c, d) ≠ (10, 10)` absolute magnitude sum `∑ |cf| * W^a * K^b` on `t3u3CorePoly`. -/
def t3u3RemAbsBound (W K : Nat) : Nat :=
  let rec aux : List Mono4 -> Nat
    | [] => 0
    | (a, b, c, d, cf) :: tl =>
      (if c == 10 && d == 10 then 0 else cf.natAbs * W ^ a * K ^ b) + aux tl
  aux t3u3CorePoly

/-- Explicit finite multi-`u` sign-lock & zero-multiplicity ceiling `U_max(W, K) ≥ 1` above which
    `intDet 9 (laurentTwoBaseT3U3Mat9 W K u)` is strictly positive (`W < K`), strictly negative
    (`K < W`), and non-zero across ALL `W, K ≥ 1` (including `W = K`). -/
def t3u3SignLockHorizon (W K : Nat) : Nat :=
  3 * (t3u3RemAbsBound W K + 1) + 1

private def evalP9ShapeNatW15 (c9 c6 c4 c2 : Nat) (W K : Nat) : Nat :=
  c9 * W ^ 9 + c6 * W ^ 6 * K ^ 3 + c4 * W ^ 4 * K ^ 5 + c2 * W ^ 2 * K ^ 7

private def evalN9ShapeNatW15 (c7 c5 c3 c0 : Nat) (W K : Nat) : Nat :=
  c7 * W ^ 7 * K ^ 2 + c5 * W ^ 5 * K ^ 4 + c3 * W ^ 3 * K ^ 6 + c0 * K ^ 9

private def powModSmallW15 (a : Nat) : Nat -> Nat -> Nat
  | 0, p => 1 % p
  | k + 1, p => (a * powModSmallW15 a k p) % p

private theorem powModSmallW15_eq (a : Nat) :
    ∀ (k p : Nat), powModSmallW15 a k p = a ^ k % p
  | 0, p => rfl
  | k + 1, p => by
    rw [powModSmallW15, powModSmallW15_eq a k p, Nat.pow_succ, Nat.mul_comm (a ^ k) a,
        Nat.mul_mod a (a ^ k % p) p, Nat.mod_mod, ← Nat.mul_mod a (a ^ k) p]

private def evalP9ModW15 (p r9 r6 r4 r2 a b : Nat) : Nat :=
  (r9 * powModSmallW15 a 9 p +
   ((r6 * powModSmallW15 a 6 p) % p) * powModSmallW15 b 3 p +
   ((r4 * powModSmallW15 a 4 p) % p) * powModSmallW15 b 5 p +
   ((r2 * powModSmallW15 a 2 p) % p) * powModSmallW15 b 7 p) % p

private def evalN9ModW15 (p r7 r5 r3 r0 a b : Nat) : Nat :=
  (((r7 * powModSmallW15 a 7 p) % p) * powModSmallW15 b 2 p +
   ((r5 * powModSmallW15 a 5 p) % p) * powModSmallW15 b 4 p +
   ((r3 * powModSmallW15 a 3 p) % p) * powModSmallW15 b 6 p +
   r0 * powModSmallW15 b 9 p) % p

private theorem pow_mod_eq_mod_pow_w15 (m a : Nat) :
    ∀ k : Nat, a ^ k % m = (a % m) ^ k % m
  | 0 => rfl
  | k + 1 => by
    rw [Nat.pow_succ a k, Nat.pow_succ (a % m) k,
        Nat.mul_mod (a ^ k) a m, pow_mod_eq_mod_pow_w15 m a k,
        Nat.mul_mod ((a % m) ^ k % m) (a % m) m, Nat.mod_mod, ← Nat.mul_mod]

private theorem p9Shape_nonzero_of_mod_p_w15
    (c9 c6 c4 c2 c7 c5 c3 c0 p : Nat) (hp2 : p ≥ 2)
    (honly0 : ∀ a b : Fin p,
      evalP9ModW15 p (c9 % p) (c6 % p) (c4 % p) (c2 % p) a.val b.val =
        evalN9ModW15 p (c7 % p) (c5 % p) (c3 % p) (c0 % p) a.val b.val ->
      a.val = 0 ∧ b.val = 0) :
    ∀ W K : Nat, W ≥ 1 -> K ≥ 1 ->
      evalP9ShapeNatW15 c9 c6 c4 c2 W K ≠ evalN9ShapeNatW15 c7 c5 c3 c0 W K := by
  have hhom : ∀ (c W K a b : Nat), a + b = 9 ->
      (c * W) ^ a * (c * K) ^ b = c ^ 9 * (W ^ a * K ^ b) := by
    intro c W K a b hab
    rw [mul_pow_w15c c W a, mul_pow_w15c c K b]
    calc (c ^ a * W ^ a) * (c ^ b * K ^ b)
        = (c ^ a * c ^ b) * (W ^ a * K ^ b) := by ac_rfl
      _ = c ^ (a + b) * (W ^ a * K ^ b) := by rw [← Nat.pow_add]
      _ = c ^ 9 * (W ^ a * K ^ b) := by rw [hab]
  have hscale : ∀ (c W K : Nat),
      evalP9ShapeNatW15 c9 c6 c4 c2 (c * W) (c * K) = c ^ 9 * evalP9ShapeNatW15 c9 c6 c4 c2 W K ∧
      evalN9ShapeNatW15 c7 c5 c3 c0 (c * W) (c * K) = c ^ 9 * evalN9ShapeNatW15 c7 c5 c3 c0 W K := by
    intro c W K
    unfold evalP9ShapeNatW15 evalN9ShapeNatW15
    have h90 := mul_pow_w15c c W 9
    have h63 := hhom c W K 6 3 rfl
    have h45 := hhom c W K 4 5 rfl
    have h27 := hhom c W K 2 7 rfl
    have h72 := hhom c W K 7 2 rfl
    have h54 := hhom c W K 5 4 rfl
    have h36 := hhom c W K 3 6 rfl
    have h09 := mul_pow_w15c c K 9
    have hm3 : ∀ (k x y : Nat), k * x * y = k * (x * y) := Nat.mul_assoc
    rw [hm3 c6, hm3 c4, hm3 c2, hm3 c7, hm3 c5, hm3 c3,
        hm3 c6 (W ^ 6), hm3 c4 (W ^ 4), hm3 c2 (W ^ 2),
        hm3 c7 (W ^ 7), hm3 c5 (W ^ 5), hm3 c3 (W ^ 3),
        h90, h63, h45, h27, h72, h54, h36, h09]
    refine ⟨?_, ?_⟩ <;> (simp only [Nat.mul_add]; ac_rfl)
  have hadd4 : ∀ (a b c d : Nat), (a + b + c + d) % p = (a % p + b % p + c % p + d % p) % p := by
    intro a b c d
    rw [Nat.add_mod (a + b + c) d, Nat.add_mod (a + b) c, Nat.add_mod a b]
    simp [Nat.add_mod]
  have ht3 : ∀ (cf W K a b : Nat),
      (cf * W ^ a * K ^ b) % p =
        (((cf % p) * powModSmallW15 (W % p) a p) % p * powModSmallW15 (K % p) b p) % p := by
    intro cf W K a b
    rw [powModSmallW15_eq, powModSmallW15_eq,
        Nat.mul_mod (cf * W ^ a) (K ^ b) p, Nat.mul_mod cf (W ^ a) p,
        pow_mod_eq_mod_pow_w15 p W a, pow_mod_eq_mod_pow_w15 p K b]
  have ht2 : ∀ (cf X a : Nat),
      (cf * X ^ a) % p = ((cf % p) * powModSmallW15 (X % p) a p) % p := by
    intro cf X a
    rw [powModSmallW15_eq, Nat.mul_mod cf (X ^ a) p, pow_mod_eq_mod_pow_w15 p X a]
  have hdesc : ∀ (fuel W K : Nat), W ≥ 1 -> K ≥ 1 -> W + K ≤ fuel ->
      evalP9ShapeNatW15 c9 c6 c4 c2 W K ≠ evalN9ShapeNatW15 c7 c5 c3 c0 W K := by
    intro fuel; induction fuel with
    | zero => intro W K hW _ hle; omega
    | succ fuel' ih =>
      intro W K hW hK hle heq
      have hp_mod : evalP9ShapeNatW15 c9 c6 c4 c2 W K % p =
          evalP9ModW15 p (c9 % p) (c6 % p) (c4 % p) (c2 % p) (W % p) (K % p) := by
        unfold evalP9ShapeNatW15 evalP9ModW15
        rw [hadd4, ht2 c9 W 9, ht3 c6 W K 6 3, ht3 c4 W K 4 5, ht3 c2 W K 2 7, ← hadd4]
      have hn_mod : evalN9ShapeNatW15 c7 c5 c3 c0 W K % p =
          evalN9ModW15 p (c7 % p) (c5 % p) (c3 % p) (c0 % p) (W % p) (K % p) := by
        unfold evalN9ShapeNatW15 evalN9ModW15
        rw [hadd4, ht3 c7 W K 7 2, ht3 c5 W K 5 4, ht3 c3 W K 3 6, ht2 c0 K 9, ← hadd4]
      have hm_eq : evalP9ModW15 p (c9 % p) (c6 % p) (c4 % p) (c2 % p) (W % p) (K % p) =
          evalN9ModW15 p (c7 % p) (c5 % p) (c3 % p) (c0 % p) (W % p) (K % p) := by
        rw [← hp_mod, ← hn_mod, heq]
      rcases honly0 ⟨W % p, Nat.mod_lt W (by omega)⟩ ⟨K % p, Nat.mod_lt K (by omega)⟩ hm_eq with ⟨hw0, hk0⟩
      dsimp only at hw0 hk0
      let W' := W / p
      let K' := K / p
      have hW_eq : W = p * W' := by have := Nat.div_add_mod W p; rw [hw0, Nat.add_zero] at this; exact this.symm
      have hK_eq : K = p * K' := by have := Nat.div_add_mod K p; rw [hk0, Nat.add_zero] at this; exact this.symm
      have hW'1 : W' ≥ 1 := Nat.pos_of_ne_zero (fun h0 => by
        have : W = 0 := by rw [hW_eq, h0, Nat.mul_zero]
        omega)
      have hK'1 : K' ≥ 1 := Nat.pos_of_ne_zero (fun h0 => by
        have : K = 0 := by rw [hK_eq, h0, Nat.mul_zero]
        omega)
      have hW'_lt : W' < W := by have := Nat.mul_le_mul_right W' hp2; omega
      have hK'_lt : K' < K := by have := Nat.mul_le_mul_right K' hp2; omega
      rw [hW_eq, hK_eq] at heq
      rcases hscale p W' K' with ⟨hs1, hs2⟩
      rw [hs1, hs2] at heq
      exact ih W' K' hW'1 hK'1 (by omega) (Nat.eq_of_mul_eq_mul_left (nat_pow_pos_of_pos p (by omega) 9) heq)
  exact fun W K hW hK => hdesc (W + K) W K hW hK (Nat.le_refl _)

private def uSliceShapePolyW15 (ms : List Mono4) (u g c9 c6 c4 c2 c7 c5 c3 c0 : Nat) (k : Fin 10) : Bool :=
  slicePoly4CoeffFast u k.val ms ==
    match k.val with
    | 0 => (g : Int) * (c9 : Int)
    | 1 => 0
    | 2 => -((g : Int) * (c7 : Int))
    | 3 => (g : Int) * (c6 : Int)
    | 4 => -((g : Int) * (c5 : Int))
    | 5 => (g : Int) * (c4 : Int)
    | 6 => -((g : Int) * (c3 : Int))
    | 7 => (g : Int) * (c2 : Int)
    | 8 => 0
    | _ => -((g : Int) * (c0 : Int))

private abbrev uSliceShapeW15 := uSliceShapePolyW15 t3u3CorePoly

private theorem uSliceShapePoly_imp_eqsW15
    (ms : List Mono4) (u g c9 c6 c4 c2 c7 c5 c3 c0 : Nat)
    (hsh : ∀ k : Fin 10, uSliceShapePolyW15 ms u g c9 c6 c4 c2 c7 c5 c3 c0 k = true) :
    slicePoly4CoeffInt u 0 ms = (g : Int) * (c9 : Int) ∧
    slicePoly4CoeffInt u 1 ms = 0 ∧
    slicePoly4CoeffInt u 2 ms = -((g : Int) * (c7 : Int)) ∧
    slicePoly4CoeffInt u 3 ms = (g : Int) * (c6 : Int) ∧
    slicePoly4CoeffInt u 4 ms = -((g : Int) * (c5 : Int)) ∧
    slicePoly4CoeffInt u 5 ms = (g : Int) * (c4 : Int) ∧
    slicePoly4CoeffInt u 6 ms = -((g : Int) * (c3 : Int)) ∧
    slicePoly4CoeffInt u 7 ms = (g : Int) * (c2 : Int) ∧
    slicePoly4CoeffInt u 8 ms = 0 ∧
    slicePoly4CoeffInt u 9 ms = -((g : Int) * (c0 : Int)) := by
  have h0 := hsh ⟨0, by decide⟩; dsimp only [uSliceShapePolyW15, slicePoly4CoeffFast] at h0
  have h1 := hsh ⟨1, by decide⟩; dsimp only [uSliceShapePolyW15, slicePoly4CoeffFast] at h1
  have h2 := hsh ⟨2, by decide⟩; dsimp only [uSliceShapePolyW15, slicePoly4CoeffFast] at h2
  have h3 := hsh ⟨3, by decide⟩; dsimp only [uSliceShapePolyW15, slicePoly4CoeffFast] at h3
  have h4 := hsh ⟨4, by decide⟩; dsimp only [uSliceShapePolyW15, slicePoly4CoeffFast] at h4
  have h5 := hsh ⟨5, by decide⟩; dsimp only [uSliceShapePolyW15, slicePoly4CoeffFast] at h5
  have h6 := hsh ⟨6, by decide⟩; dsimp only [uSliceShapePolyW15, slicePoly4CoeffFast] at h6
  have h7 := hsh ⟨7, by decide⟩; dsimp only [uSliceShapePolyW15, slicePoly4CoeffFast] at h7
  have h8 := hsh ⟨8, by decide⟩; dsimp only [uSliceShapePolyW15, slicePoly4CoeffFast] at h8
  have h9 := hsh ⟨9, by decide⟩; dsimp only [uSliceShapePolyW15, slicePoly4CoeffFast] at h9
  exact ⟨beq_iff_eq.mp h0, beq_iff_eq.mp h1, beq_iff_eq.mp h2, beq_iff_eq.mp h3, beq_iff_eq.mp h4,
         beq_iff_eq.mp h5, beq_iff_eq.mp h6, beq_iff_eq.mp h7, beq_iff_eq.mp h8, beq_iff_eq.mp h9⟩

private def p9DehomogModsBoolW15
    (p c9 c6 c4 c2 c7 c5 c3 c0 r9 r6 r4 r2 r7 r5 r3 r0 : Nat) : Bool :=
  (c9 % p == r9) && (c6 % p == r6) && (c4 % p == r4) && (c2 % p == r2) &&
  (c7 % p == r7) && (c5 % p == r5) && (c3 % p == r3) && (c0 % p == r0)

private theorem p9_only0_of_dehomog_w15
    (p c9 c6 c4 c2 c7 c5 c3 c0 r9 r6 r4 r2 r7 r5 r3 r0 : Nat)
    (hp2 : p ≥ 2)
    (hmods : p9DehomogModsBoolW15 p c9 c6 c4 c2 c7 c5 c3 c0 r9 r6 r4 r2 r7 r5 r3 r0 = true)
    (ha0 : ∀ a : Fin p, (r9 * powModSmallW15 a.val 9 p) % p = 0 -> a.val = 0)
    (hinv : ∀ b : Fin p, b.val ≠ 0 -> (b.val * fastPowMod28 p b.val (p - 2)) % p = 1)
    (ht1 : ∀ t : Fin p, evalP9ModW15 p r9 r6 r4 r2 t.val 1 ≠ evalN9ModW15 p r7 r5 r3 r0 t.val 1) :
    ∀ a b : Fin p,
      evalP9ModW15 p (c9 % p) (c6 % p) (c4 % p) (c2 % p) a.val b.val =
        evalN9ModW15 p (c7 % p) (c5 % p) (c3 % p) (c0 % p) a.val b.val ->
      a.val = 0 ∧ b.val = 0 := by
  unfold p9DehomogModsBoolW15 at hmods
  rcases bool_and_split hmods with ⟨hm1, hc0⟩
  rcases bool_and_split hm1 with ⟨hm2, hc3⟩
  rcases bool_and_split hm2 with ⟨hm3, hc5⟩
  rcases bool_and_split hm3 with ⟨hm4, hc7⟩
  rcases bool_and_split hm4 with ⟨hm5, hc2⟩
  rcases bool_and_split hm5 with ⟨hm6, hc4⟩
  rcases bool_and_split hm6 with ⟨hc9, hc6⟩
  have er9 : c9 % p = r9 := beq_iff_eq.mp hc9
  have er6 : c6 % p = r6 := beq_iff_eq.mp hc6
  have er4 : c4 % p = r4 := beq_iff_eq.mp hc4
  have er2 : c2 % p = r2 := beq_iff_eq.mp hc2
  have er7 : c7 % p = r7 := beq_iff_eq.mp hc7
  have er5 : c5 % p = r5 := beq_iff_eq.mp hc5
  have er3 : c3 % p = r3 := beq_iff_eq.mp hc3
  have er0 : c0 % p = r0 := beq_iff_eq.mp hc0
  rw [er9, er6, er4, er2, er7, er5, er3, er0]
  have hr9_lt : r9 < p := er9 ▸ Nat.mod_lt c9 (by omega)
  have hr6_lt : r6 < p := er6 ▸ Nat.mod_lt c6 (by omega)
  have hr4_lt : r4 < p := er4 ▸ Nat.mod_lt c4 (by omega)
  have hr2_lt : r2 < p := er2 ▸ Nat.mod_lt c2 (by omega)
  have hr7_lt : r7 < p := er7 ▸ Nat.mod_lt c7 (by omega)
  have hr5_lt : r5 < p := er5 ▸ Nat.mod_lt c5 (by omega)
  have hr3_lt : r3 < p := er3 ▸ Nat.mod_lt c3 (by omega)
  have hr0_lt : r0 < p := er0 ▸ Nat.mod_lt c0 (by omega)
  have hadd4 : ∀ (u v w z : Nat), (u + v + w + z) % p = (u % p + v % p + w % p + z % p) % p := by
    intro u v w z
    rw [Nat.add_mod (u + v + w) z, Nat.add_mod (u + v) w, Nat.add_mod u v]
    simp [Nat.add_mod]
  have ht3 : ∀ (cf X Y e1 e2 : Nat), cf < p ->
      (cf * X ^ e1 * Y ^ e2) % p =
        ((cf * powModSmallW15 (X % p) e1 p) % p * powModSmallW15 (Y % p) e2 p) % p := by
    intro cf X Y e1 e2 hcf
    rw [powModSmallW15_eq, powModSmallW15_eq,
        Nat.mul_mod (cf * X ^ e1) (Y ^ e2) p, Nat.mul_mod cf (X ^ e1) p,
        Nat.mod_eq_of_lt hcf, pow_mod_eq_mod_pow_w15 p X e1, pow_mod_eq_mod_pow_w15 p Y e2]
  have ht2 : ∀ (cf X e : Nat), cf < p ->
      (cf * X ^ e) % p = (cf * powModSmallW15 (X % p) e p) % p := by
    intro cf X e hcf
    rw [powModSmallW15_eq, Nat.mul_mod cf (X ^ e) p, Nat.mod_eq_of_lt hcf, pow_mod_eq_mod_pow_w15 p X e]
  have hP_eq : ∀ X Y : Nat,
      evalP9ModW15 p r9 r6 r4 r2 (X % p) (Y % p) = evalP9ShapeNatW15 r9 r6 r4 r2 X Y % p := by
    intro X Y
    have h : evalP9ShapeNatW15 r9 r6 r4 r2 X Y % p = evalP9ModW15 p r9 r6 r4 r2 (X % p) (Y % p) := by
      unfold evalP9ShapeNatW15 evalP9ModW15
      rw [hadd4, ht2 r9 X 9 hr9_lt, ht3 r6 X Y 6 3 hr6_lt, ht3 r4 X Y 4 5 hr4_lt, ht3 r2 X Y 2 7 hr2_lt, ← hadd4]
    exact h.symm
  have hN_eq : ∀ X Y : Nat,
      evalN9ModW15 p r7 r5 r3 r0 (X % p) (Y % p) = evalN9ShapeNatW15 r7 r5 r3 r0 X Y % p := by
    intro X Y
    have h : evalN9ShapeNatW15 r7 r5 r3 r0 X Y % p = evalN9ModW15 p r7 r5 r3 r0 (X % p) (Y % p) := by
      unfold evalN9ShapeNatW15 evalN9ModW15
      rw [hadd4, ht3 r7 X Y 7 2 hr7_lt, ht3 r5 X Y 5 4 hr5_lt, ht3 r3 X Y 3 6 hr3_lt, ht2 r0 Y 9 hr0_lt, ← hadd4]
    exact h.symm
  have hhom : ∀ (k X Y e1 e2 : Nat), e1 + e2 = 9 ->
      (k * X) ^ e1 * (k * Y) ^ e2 = k ^ 9 * (X ^ e1 * Y ^ e2) := by
    intro k X Y e1 e2 he
    rw [mul_pow_w15c k X e1, mul_pow_w15c k Y e2]
    calc (k ^ e1 * X ^ e1) * (k ^ e2 * Y ^ e2)
        = (k ^ e1 * k ^ e2) * (X ^ e1 * Y ^ e2) := by ac_rfl
      _ = k ^ 9 * (X ^ e1 * Y ^ e2) := by rw [← Nat.pow_add, he]
  have hscale : ∀ (k X Y : Nat),
      evalP9ShapeNatW15 r9 r6 r4 r2 (k * X) (k * Y) = k ^ 9 * evalP9ShapeNatW15 r9 r6 r4 r2 X Y ∧
      evalN9ShapeNatW15 r7 r5 r3 r0 (k * X) (k * Y) = k ^ 9 * evalN9ShapeNatW15 r7 r5 r3 r0 X Y := by
    intro k X Y; unfold evalP9ShapeNatW15 evalN9ShapeNatW15
    have hm3 : ∀ (q x y : Nat), q * x * y = q * (x * y) := Nat.mul_assoc
    rw [hm3 r6, hm3 r4, hm3 r2, hm3 r7, hm3 r5, hm3 r3,
        hm3 r6 (X ^ 6), hm3 r4 (X ^ 4), hm3 r2 (X ^ 2),
        hm3 r7 (X ^ 7), hm3 r5 (X ^ 5), hm3 r3 (X ^ 3),
        mul_pow_w15c k X 9, hhom k X Y 6 3 rfl, hhom k X Y 4 5 rfl, hhom k X Y 2 7 rfl,
        hhom k X Y 7 2 rfl, hhom k X Y 5 4 rfl, hhom k X Y 3 6 rfl, mul_pow_w15c k Y 9]
    refine ⟨?_, ?_⟩ <;> (simp only [Nat.mul_add]; ac_rfl)
  intro a b heq
  by_cases hb0 : b.val = 0
  · refine ⟨?_, hb0⟩
    rw [hb0] at heq
    have hp0 : powModSmallW15 0 3 p = 0 ∧ powModSmallW15 0 5 p = 0 ∧ powModSmallW15 0 7 p = 0 ∧
        powModSmallW15 0 2 p = 0 ∧ powModSmallW15 0 4 p = 0 ∧ powModSmallW15 0 6 p = 0 ∧
        powModSmallW15 0 9 p = 0 := by
      simp [powModSmallW15_eq]
    rcases hp0 with ⟨z3, z5, z7, z2, z4, z6, z9⟩
    unfold evalP9ModW15 evalN9ModW15 at heq
    rw [z3, z5, z7, z2, z4, z6, z9] at heq
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_mod] at heq
    exact ha0 a heq
  · exfalso
    let inv := fastPowMod28 p b.val (p - 2)
    have hbinv : (inv * b.val) % p = 1 := by rw [Nat.mul_comm]; exact hinv b hb0
    let t := (inv * a.val) % p
    have ht_lt : t < p := Nat.mod_lt _ (by omega)
    have h1_mod : 1 % p = 1 := Nat.mod_eq_of_lt hp2
    have ha_mod : a.val % p = a.val := Nat.mod_eq_of_lt a.isLt
    have hb_mod : b.val % p = b.val := Nat.mod_eq_of_lt b.isLt
    rcases hscale inv a.val b.val with ⟨hsP, hsN⟩
    have hPt : evalP9ModW15 p r9 r6 r4 r2 t 1 =
        (inv ^ 9 * evalP9ModW15 p r9 r6 r4 r2 a.val b.val) % p := by
      calc evalP9ModW15 p r9 r6 r4 r2 t 1
          = evalP9ModW15 p r9 r6 r4 r2 ((inv * a.val) % p) ((inv * b.val) % p) := by rw [hbinv]
        _ = evalP9ShapeNatW15 r9 r6 r4 r2 (inv * a.val) (inv * b.val) % p := hP_eq _ _
        _ = (inv ^ 9 * evalP9ShapeNatW15 r9 r6 r4 r2 a.val b.val) % p := by rw [hsP]
        _ = (inv ^ 9 * (evalP9ShapeNatW15 r9 r6 r4 r2 a.val b.val % p)) % p := by
              rw [Nat.mul_mod (inv ^ 9) (_ % p), Nat.mod_mod, ← Nat.mul_mod]
        _ = (inv ^ 9 * evalP9ModW15 p r9 r6 r4 r2 a.val b.val) % p := by
              rw [← hP_eq a.val b.val, ha_mod, hb_mod]
    have hNt : evalN9ModW15 p r7 r5 r3 r0 t 1 =
        (inv ^ 9 * evalN9ModW15 p r7 r5 r3 r0 a.val b.val) % p := by
      calc evalN9ModW15 p r7 r5 r3 r0 t 1
          = evalN9ModW15 p r7 r5 r3 r0 ((inv * a.val) % p) ((inv * b.val) % p) := by rw [hbinv]
        _ = evalN9ShapeNatW15 r7 r5 r3 r0 (inv * a.val) (inv * b.val) % p := hN_eq _ _
        _ = (inv ^ 9 * evalN9ShapeNatW15 r7 r5 r3 r0 a.val b.val) % p := by rw [hsN]
        _ = (inv ^ 9 * (evalN9ShapeNatW15 r7 r5 r3 r0 a.val b.val % p)) % p := by
              rw [Nat.mul_mod (inv ^ 9) (_ % p), Nat.mod_mod, ← Nat.mul_mod]
        _ = (inv ^ 9 * evalN9ModW15 p r7 r5 r3 r0 a.val b.val) % p := by
              rw [← hN_eq a.val b.val, ha_mod, hb_mod]
    exact ht1 ⟨t, ht_lt⟩ (by dsimp only; rw [hPt, heq, ← hNt])

set_option maxRecDepth 65536 in
private theorem t3u3_u5_mod13_cert :
    (∀ k : Fin 10, uSliceShapeW15 5 5324
      33360272332101457332377563527380992 878389490372262635507828585920266240
      1371519877801457284579464854867834112 125529503920054886720020212209005056
      236621853817747527134717832347910144 1501193671081056141264073588027097088
      651880523564828589149159296454876160 146979460948013690421348435933 k = true) ∧
    p9DehomogModsBoolW15 13
      33360272332101457332377563527380992 878389490372262635507828585920266240
      1371519877801457284579464854867834112 125529503920054886720020212209005056
      236621853817747527134717832347910144 1501193671081056141264073588027097088
      651880523564828589149159296454876160 146979460948013690421348435933
      12 6 12 0 7 0 3 5 = true ∧
    (∀ a : Fin 13, (12 * powModSmallW15 a.val 9 13) % 13 = 0 -> a.val = 0) ∧
    (∀ b : Fin 13, b.val ≠ 0 -> (b.val * fastPowMod28 13 b.val 11) % 13 = 1) ∧
    (∀ t : Fin 13, evalP9ModW15 13 12 6 12 0 t.val 1 ≠ evalN9ModW15 13 7 0 3 5 t.val 1) := by
  decide

set_option maxRecDepth 65536 in
private theorem t3u3_u6_mod53_cert :
    (∀ k : Fin 10, uSliceShapeW15 6 44328437289500
      138550599097096320707214696251392 6235207076150779090428088503238656
      10496056338164671218894932748140544 1003149385226047073263953429356544
      1533013597978362376363965407035392 11132543627597721323918786027323392
      5111421046354056827745463772971008 58149737003040059690390169 k = true) ∧
    p9DehomogModsBoolW15 53
      138550599097096320707214696251392 6235207076150779090428088503238656
      10496056338164671218894932748140544 1003149385226047073263953429356544
      1533013597978362376363965407035392 11132543627597721323918786027323392
      5111421046354056827745463772971008 58149737003040059690390169
      41 52 23 4 52 29 24 9 = true ∧
    (∀ a : Fin 53, (41 * powModSmallW15 a.val 9 53) % 53 = 0 -> a.val = 0) ∧
    (∀ b : Fin 53, b.val ≠ 0 -> (b.val * fastPowMod28 53 b.val 51) % 53 = 1) ∧
    (∀ t : Fin 53, evalP9ModW15 53 41 52 23 4 t.val 1 ≠ evalN9ModW15 53 52 29 24 9 t.val 1) := by
  decide

set_option maxRecDepth 65536 in
private theorem t3u3_u7_mod13_cert :
    (∀ k : Fin 10, uSliceShapeW15 7 4
      52511350701938559753667551233359238475106059139678208
      4073940070124592680352099875273877699133056384148439040
      7211742666972866869356631400188824390502456160938195968
      704835803495749956629595366430822379597094756292614144
      946100722037851609785752523566095095562896407198171136
      7498173378008048352196828174882899496205435658134618112
      3557528458348414188263099531221336193937097739338936320
      2018809397650780948200422292001579435976380887 k = true) ∧
    p9DehomogModsBoolW15 13
      52511350701938559753667551233359238475106059139678208
      4073940070124592680352099875273877699133056384148439040
      7211742666972866869356631400188824390502456160938195968
      704835803495749956629595366430822379597094756292614144
      946100722037851609785752523566095095562896407198171136
      7498173378008048352196828174882899496205435658134618112
      3557528458348414188263099531221336193937097739338936320
      2018809397650780948200422292001579435976380887
      5 9 5 0 4 0 11 1 = true ∧
    (∀ a : Fin 13, (5 * powModSmallW15 a.val 9 13) % 13 = 0 -> a.val = 0) ∧
    (∀ b : Fin 13, b.val ≠ 0 -> (b.val * fastPowMod28 13 b.val 11) % 13 = 1) ∧
    (∀ t : Fin 13, evalP9ModW15 13 5 9 5 0 t.val 1 ≠ evalN9ModW15 13 4 0 11 1 t.val 1) := by
  decide

set_option maxRecDepth 65536 in
private theorem t3u3_u8_mod31_cert :
    (∀ k : Fin 10, uSliceShapeW15 8 38382812500
      186468819435685014536356233840285386444733333635072
      25109605597616735782934420562378756870555448387829760
      46002067243475326210209617190224982751122399757860864
      4547400372864998361293283360227589394317275979841536
      5612211518716228291746207562851907986812318779441152
      47230293230417917151238388708952259967917039758082048
      22844108718751495603138856069956205120322532823531520
      643286470205519953670066396362044467304771 k = true) ∧
    p9DehomogModsBoolW15 31
      186468819435685014536356233840285386444733333635072
      25109605597616735782934420562378756870555448387829760
      46002067243475326210209617190224982751122399757860864
      4547400372864998361293283360227589394317275979841536
      5612211518716228291746207562851907986812318779441152
      47230293230417917151238388708952259967917039758082048
      22844108718751495603138856069956205120322532823531520
      643286470205519953670066396362044467304771
      2 20 7 8 23 17 16 30 = true ∧
    (∀ a : Fin 31, (2 * powModSmallW15 a.val 9 31) % 31 = 0 -> a.val = 0) ∧
    (∀ b : Fin 31, b.val ≠ 0 -> (b.val * fastPowMod28 31 b.val 29) % 31 = 1) ∧
    (∀ t : Fin 31, evalP9ModW15 31 2 20 7 8 t.val 1 ≠ evalN9ModW15 31 23 17 16 30 t.val 1) := by
  decide

set_option maxRecDepth 65536 in
private theorem t3u3_u9_mod83_cert :
    (∀ k : Fin 10, uSliceShapeW15 9 9410548
      25883795460833024500081486882325205817552300047611000778653696
      6082796594405700904202434380699136068703977754967255089466572800
      11413589698826189515877005021826601362432070687230851599525851136
      1134756712319222717025888598169378900348907198812838710768099328
      1322895569846472513198498956453021962858613263073358737521508352
      11623730346983932559403846921940250708370832009940854151414022144
      5687115667091841683689684921445093415892834192047251378948751360
      7927441183175322619488700456706149531039111397173299 k = true) ∧
    p9DehomogModsBoolW15 83
      25883795460833024500081486882325205817552300047611000778653696
      6082796594405700904202434380699136068703977754967255089466572800
      11413589698826189515877005021826601362432070687230851599525851136
      1134756712319222717025888598169378900348907198812838710768099328
      1322895569846472513198498956453021962858613263073358737521508352
      11623730346983932559403846921940250708370832009940854151414022144
      5687115667091841683689684921445093415892834192047251378948751360
      7927441183175322619488700456706149531039111397173299
      7 22 68 43 39 71 37 62 = true ∧
    (∀ a : Fin 83, (7 * powModSmallW15 a.val 9 83) % 83 = 0 -> a.val = 0) ∧
    (∀ b : Fin 83, b.val ≠ 0 -> (b.val * fastPowMod28 83 b.val 81) % 83 = 1) ∧
    (∀ t : Fin 83, evalP9ModW15 83 7 22 68 43 t.val 1 ≠ evalN9ModW15 83 39 71 37 62 t.val 1) := by
  decide

private def checkCorePolyValuationsAndLead : Bool :=
  t3u3CorePoly.all (fun m =>
    let a := m.1
    let b := m.2.1
    let c := m.2.2.1
    let d := m.2.2.2.1
    let cf := m.2.2.2.2
    decide (a + b = 9 ∧ b < 10) &&
    decide (b ≠ 1 ∧ b ≠ 8) &&
    (if b == 0 then decide ((d == 0 ∧ c == 6 ∧ cf == -4) ∨ (d ≥ 1 ∧ c ≥ 6)) else true) &&
    (if b == 2 || b == 3 || b == 4 then decide (d ≥ 1 ∧ c ≥ 2) else true) &&
    (if b == 5 || b == 7 then decide (d ≥ 2 ∧ (c ≥ 2 ∨ (c == 1 ∧ cf % 2 == 0))) else true) &&
    (if b == 6 then decide (d ≥ 2 ∧ (c ≥ 2 ∨ (c == 1 ∧ cf % 4 == 0))) else true) &&
    (if b == 9 then decide (d ≥ 6 ∧ ((c == 0 ∧ cf == 4) ∨ c ≥ 1)) else true) &&
    (if c == 10 && d == 10 then
      decide ((b == 2 ∧ cf == -1) ∨ (b == 3 ∧ cf == 5) ∨ (b == 4 ∧ cf == -10) ∨
              (b == 5 ∧ cf == 10) ∨ (b == 6 ∧ cf == -5) ∨ (b == 7 ∧ cf == 1))
     else decide (2 ^ c * 3 ^ d ≤ 45349632))) &&
  (t3u3CorePoly.filter (fun m => m.2.2.1 == 10 && m.2.2.2.1 == 10)).map
      (fun m => (m.1, m.2.1, m.2.2.2.2)) ==
    [(2, 7, 1), (3, 6, -5), (4, 5, 10), (5, 4, -10), (6, 3, 5), (7, 2, -1)]

set_option maxRecDepth 65536 in
private theorem t3u3_val_and_7_11_certs :
    checkCorePolyValuationsAndLead = true ∧
    evalSliceSum10Fast 7 11 3 > 0 ∧
    evalSliceSum10Fast 7 11 4 < 0 ∧
    evalSliceSum10Fast 7 11 5 > 0 := by decide

private theorem evalPoly4_eq_slice_sum10_w15 (W K u : Nat) :
    evalPoly4 (W : Int) (K : Int) ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int) t3u3CorePoly =
      intSumPrefix 10 (fun k =>
        ((W ^ (9 - k.val) * K ^ k.val : Nat) : Int) * slicePoly4CoeffInt u k.val t3u3CorePoly) 10 := by
  have hintPow_ev : ∀ (x d : Nat), intPowNat (x : Int) d = ((x ^ d : Nat) : Int) := by
    intro x d; induction d with
    | zero => rfl
    | succ d' ih => simp [intPowNat, ih, Nat.pow_succ, Int.natCast_mul, Int.mul_comm]
  have hsum_add10 : ∀ (f g : Fin 10 -> Int) (m : Nat), m ≤ 10 ->
      intSumPrefix 10 (fun i => f i + g i) m = intSumPrefix 10 f m + intSumPrefix 10 g m := by
    intro f g m hm; induction m with
    | zero => simp [intSumPrefix]
    | succ m' ih =>
      have hlt : m' < 10 := hm
      simp only [intSumPrefix, hlt, dite_true, ih (Nat.le_of_lt hm)]; omega
  have hsingle10 : ∀ (k0 : Fin 10) (val : Int),
      intSumPrefix 10 (fun k => if k.val = k0.val then val else 0) 10 = val := by
    intro k0 val
    have hst : ∀ m : Nat, m ≤ 10 ->
        intSumPrefix 10 (fun k => if k.val = k0.val then val else 0) m =
          if k0.val < m then val else 0 := by
      intro m hm; induction m with
      | zero => simp [intSumPrefix]
      | succ m' ih =>
        have hlt : m' < 10 := hm
        simp only [intSumPrefix, hlt, dite_true, ih (Nat.le_of_lt hm)]
        by_cases heq : m' = k0.val
        · rw [ite_false_of_w10 (by omega : ¬ (k0.val < m')),
              ite_true_of_w10 heq,
              ite_true_of_w10 (by omega : k0.val < m' + 1), Int.zero_add]
        · rw [ite_false_of_w10 heq, Int.add_zero]
          by_cases hklt : k0.val < m'
          · rw [ite_true_of_w10 hklt, ite_true_of_w10 (by omega)]
          · rw [ite_false_of_w10 hklt, ite_false_of_w10 (by omega)]
    rw [hst 10 (Nat.le_refl 10), ite_true_of_w10 k0.isLt]
  have hall_deg : ∀ m ∈ t3u3CorePoly, m.1 + m.2.1 = 9 ∧ m.2.1 < 10 := by
    rcases bool_and_split t3u3_val_and_7_11_certs.1 with ⟨hall, _⟩
    intro m hm
    have hb := List.all_eq_true.mp hall m hm
    rcases bool_and_split hb with ⟨hb1, _⟩
    rcases bool_and_split hb1 with ⟨hb2, _⟩
    rcases bool_and_split hb2 with ⟨hb3, _⟩
    rcases bool_and_split hb3 with ⟨hb4, _⟩
    rcases bool_and_split hb4 with ⟨hb5, _⟩
    rcases bool_and_split hb5 with ⟨hb6, _⟩
    rcases bool_and_split hb6 with ⟨hdeg, _⟩
    exact of_decide_eq_true hdeg
  have hgen : ∀ ms : List Mono4,
      (∀ m ∈ ms, m.1 + m.2.1 = 9 ∧ m.2.1 < 10) ->
      evalPoly4 (W : Int) (K : Int) ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int) ms =
        intSumPrefix 10 (fun k =>
          ((W ^ (9 - k.val) * K ^ k.val : Nat) : Int) * slicePoly4CoeffInt u k.val ms) 10 := by
    intro ms; induction ms with
    | nil =>
      intro _
      have hz : ∀ n : Nat, n ≤ 10 -> intSumPrefix 10 (fun _ => (0 : Int)) n = 0 := by
        intro n hn; induction n with
        | zero => rfl
        | succ n' ihn => simp [intSumPrefix, show n' < 10 by omega, ihn (Nat.le_of_lt hn)]
      simpa [evalPoly4, slicePoly4CoeffInt] using (hz 10 (Nat.le_refl 10)).symm
    | cons m0 tl ih =>
      rcases m0 with ⟨a, b, c, d, cf⟩
      intro hdeg
      rcases hdeg (a, b, c, d, cf) List.mem_cons_self with ⟨hab9, hb10⟩
      dsimp only at hab9 hb10
      have iht := ih (fun m hm => hdeg m (List.mem_cons_of_mem _ hm))
      simp only [evalPoly4, evalMono4, iht, slicePoly4CoeffInt]
      have hpq : intPowNat ((2 ^ u : Nat) : Int) c * intPowNat ((3 ^ u : Nat) : Int) d =
          (((2 ^ c * 3 ^ d) ^ u : Nat) : Int) := by
        rw [hintPow_ev, hintPow_ev, ← Int.natCast_mul]
        apply congrArg Nat.cast
        rw [pow_pow_eq_mul_w5 2 u c, pow_pow_eq_mul_w5 3 u d, Nat.mul_comm u c, Nat.mul_comm u d,
            ← pow_pow_eq_mul_w5 2 c u, ← pow_pow_eq_mul_w5 3 d u, ← mul_pow_w15c]
      have hwk : intPowNat (W : Int) a * intPowNat (K : Int) b =
          ((W ^ (9 - b) * K ^ b : Nat) : Int) := by
        rw [hintPow_ev, hintPow_ev, ← Int.natCast_mul, show a = 9 - b by omega]
      have hterm_eq : cf * (intPowNat (W : Int) a * (intPowNat (K : Int) b *
            (intPowNat ((2 ^ u : Nat) : Int) c * intPowNat ((3 ^ u : Nat) : Int) d))) =
          ((W ^ (9 - b) * K ^ b : Nat) : Int) * (cf * (((2 ^ c * 3 ^ d) ^ u : Nat) : Int)) := by
        rw [hpq, ← Int.mul_assoc (intPowNat (W : Int) a), hwk]; ac_rfl
      rw [hterm_eq]
      have hcg : (fun k : Fin 10 =>
            ((W ^ (9 - k.val) * K ^ k.val : Nat) : Int) *
              ((if a == 9 - k.val && b == k.val then cf * (((2 ^ c * 3 ^ d) ^ u : Nat) : Int) else 0) +
                slicePoly4CoeffInt u k.val tl)) =
          (fun k : Fin 10 =>
            (if k.val = b then ((W ^ (9 - b) * K ^ b : Nat) : Int) * (cf * (((2 ^ c * 3 ^ d) ^ u : Nat) : Int)) else 0) +
            ((W ^ (9 - k.val) * K ^ k.val : Nat) : Int) * slicePoly4CoeffInt u k.val tl) := by
        funext k; rw [Int.mul_add]
        congr 1
        by_cases hkb : k.val = b
        · have ha_eq : a = 9 - k.val := by omega
          have hb_eq : b = k.val := hkb.symm
          have ha_b : (a == 9 - k.val && b == k.val) = true := by simp [ha_eq, hb_eq]
          simp only [ha_b, ite_true]
          rw [ite_true_of_w10 hkb, ← hb_eq]
        · have hbf : (b == k.val) = false := beq_false_of_ne (fun h => hkb h.symm)
          simp only [hbf, Bool.and_false, Bool.false_eq_true, ite_false, Int.mul_zero]
          rw [ite_false_of_w10 hkb]
      rw [hcg, hsum_add10 _ _ 10 (Nat.le_refl 10), hsingle10 ⟨b, hb10⟩]
  exact hgen t3u3CorePoly hall_deg

private theorem t3u3_ten_sum_w15 (f : Fin 10 -> Int) :
    intSumPrefix 10 f 10 =
      f ⟨0, by decide⟩ + f ⟨1, by decide⟩ + f ⟨2, by decide⟩ + f ⟨3, by decide⟩ +
      f ⟨4, by decide⟩ + f ⟨5, by decide⟩ + f ⟨6, by decide⟩ + f ⟨7, by decide⟩ +
      f ⟨8, by decide⟩ + f ⟨9, by decide⟩ := by
  simp only [intSumPrefix, dite_true, Int.zero_add,
             (by decide : 0 < 10), (by decide : 1 < 10), (by decide : 2 < 10),
             (by decide : 3 < 10), (by decide : 4 < 10), (by decide : 5 < 10),
             (by decide : 6 < 10), (by decide : 7 < 10), (by decide : 8 < 10),
             (by decide : 9 < 10)]

private theorem t3u3_global_1_to_9_nonzero_w15 :
    ∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 -> 1 ≤ u -> u ≤ 9 ->
      intDet 9 (laurentTwoBaseT3U3Mat9 W K u) ≠ 0 := by
  have hclosed_u := laurent_9x9_t3u3_all_u_cone_positivity_and_multiu_nonvanishing.1
  have hu_kill : ∀ (W K u g c9 c6 c4 c2 c7 c5 c3 c0 p : Nat),
      W ≥ 1 -> K ≥ 1 -> 1 ≤ u -> g ≥ 1 -> p ≥ 2 ->
      (∀ k : Fin 10, uSliceShapeW15 u g c9 c6 c4 c2 c7 c5 c3 c0 k = true) ->
      (∀ a b : Fin p,
        evalP9ModW15 p (c9 % p) (c6 % p) (c4 % p) (c2 % p) a.val b.val =
          evalN9ModW15 p (c7 % p) (c5 % p) (c3 % p) (c0 % p) a.val b.val ->
        a.val = 0 ∧ b.val = 0) ->
      intDet 9 (laurentTwoBaseT3U3Mat9 W K u) ≠ 0 := by
    intro W K u g c9 c6 c4 c2 c7 c5 c3 c0 p hW hK hu1 hg1 hp2 hsh hm_p hz
    have hc := hclosed_u W K u hW hu1
    rw [hz, Int.mul_zero, evalPoly4_eq_slice_sum10_w15 W K u, t3u3_ten_sum_w15] at hc
    rcases uSliceShapePoly_imp_eqsW15 t3u3CorePoly u g c9 c6 c4 c2 c7 c5 c3 c0 hsh with
      ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩
    rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9] at hc
    dsimp only at hc
    rw [Nat.sub_zero 9, Nat.pow_zero K, Nat.mul_one (W ^ 9),
        show (9 : Nat) - 2 = 7 from rfl, show (9 : Nat) - 3 = 6 from rfl,
        show (9 : Nat) - 4 = 5 from rfl, show (9 : Nat) - 5 = 4 from rfl,
        show (9 : Nat) - 6 = 3 from rfl, show (9 : Nat) - 7 = 2 from rfl,
        Nat.sub_self 9, Nat.pow_zero W, Nat.one_mul (K ^ 9)] at hc
    repeat rw [Int.mul_zero] at hc
    repeat rw [Int.add_zero] at hc
    have h6u_pos : ((2 ^ (3 * u) * 3 ^ (3 * u) : Nat) : Int) > 0 := by
      have hp : 2 ^ (3 * u) * 3 ^ (3 * u) ≥ 1 :=
        Nat.mul_le_mul (nat_pow_pos_of_pos 2 (by decide) _) (pow3_pos_nat _)
      omega
    have hsum0 : (((W ^ 9 : Nat) : Int) * ((g : Int) * (c9 : Int)) +
        ((W ^ 7 * K ^ 2 : Nat) : Int) * -((g : Int) * (c7 : Int)) +
        ((W ^ 6 * K ^ 3 : Nat) : Int) * ((g : Int) * (c6 : Int)) +
        ((W ^ 5 * K ^ 4 : Nat) : Int) * -((g : Int) * (c5 : Int)) +
        ((W ^ 4 * K ^ 5 : Nat) : Int) * ((g : Int) * (c4 : Int)) +
        ((W ^ 3 * K ^ 6 : Nat) : Int) * -((g : Int) * (c3 : Int)) +
        ((W ^ 2 * K ^ 7 : Nat) : Int) * ((g : Int) * (c2 : Int)) +
        ((K ^ 9 : Nat) : Int) * -((g : Int) * (c0 : Int))) = 0 := by
      by_cases hs : (((W ^ 9 : Nat) : Int) * ((g : Int) * (c9 : Int)) +
          ((W ^ 7 * K ^ 2 : Nat) : Int) * -((g : Int) * (c7 : Int)) +
          ((W ^ 6 * K ^ 3 : Nat) : Int) * ((g : Int) * (c6 : Int)) +
          ((W ^ 5 * K ^ 4 : Nat) : Int) * -((g : Int) * (c5 : Int)) +
          ((W ^ 4 * K ^ 5 : Nat) : Int) * ((g : Int) * (c4 : Int)) +
          ((W ^ 3 * K ^ 6 : Nat) : Int) * -((g : Int) * (c3 : Int)) +
          ((W ^ 2 * K ^ 7 : Nat) : Int) * ((g : Int) * (c2 : Int)) +
          ((K ^ 9 : Nat) : Int) * -((g : Int) * (c0 : Int))) = 0
      · exact hs
      · exfalso
        rcases (by omega :
          (((W ^ 9 : Nat) : Int) * ((g : Int) * (c9 : Int)) +
           ((W ^ 7 * K ^ 2 : Nat) : Int) * -((g : Int) * (c7 : Int)) +
           ((W ^ 6 * K ^ 3 : Nat) : Int) * ((g : Int) * (c6 : Int)) +
           ((W ^ 5 * K ^ 4 : Nat) : Int) * -((g : Int) * (c5 : Int)) +
           ((W ^ 4 * K ^ 5 : Nat) : Int) * ((g : Int) * (c4 : Int)) +
           ((W ^ 3 * K ^ 6 : Nat) : Int) * -((g : Int) * (c3 : Int)) +
           ((W ^ 2 * K ^ 7 : Nat) : Int) * ((g : Int) * (c2 : Int)) +
           ((K ^ 9 : Nat) : Int) * -((g : Int) * (c0 : Int))) > 0 ∨
          (((W ^ 9 : Nat) : Int) * ((g : Int) * (c9 : Int)) +
           ((W ^ 7 * K ^ 2 : Nat) : Int) * -((g : Int) * (c7 : Int)) +
           ((W ^ 6 * K ^ 3 : Nat) : Int) * ((g : Int) * (c6 : Int)) +
           ((W ^ 5 * K ^ 4 : Nat) : Int) * -((g : Int) * (c5 : Int)) +
           ((W ^ 4 * K ^ 5 : Nat) : Int) * ((g : Int) * (c4 : Int)) +
           ((W ^ 3 * K ^ 6 : Nat) : Int) * -((g : Int) * (c3 : Int)) +
           ((W ^ 2 * K ^ 7 : Nat) : Int) * ((g : Int) * (c2 : Int)) +
           ((K ^ 9 : Nat) : Int) * -((g : Int) * (c0 : Int))) < 0) with hgt | hlt
        · have hm := Int.mul_pos h6u_pos hgt; omega
        · have hm := Int.mul_neg_of_pos_of_neg h6u_pos hlt; omega
    have hg_factor :
        (g : Int) * ((evalP9ShapeNatW15 c9 c6 c4 c2 W K : Int) -
                     (evalN9ShapeNatW15 c7 c5 c3 c0 W K : Int)) = 0 := by
      unfold evalP9ShapeNatW15 evalN9ShapeNatW15
      simp only [Int.natCast_add, Int.natCast_mul, Int.mul_sub, Int.mul_add]
      have t9 : (g : Int) * ((c9 : Int) * ((W ^ 9 : Nat) : Int)) = ((W ^ 9 : Nat) : Int) * ((g : Int) * (c9 : Int)) := by ac_rfl
      have t6 : (g : Int) * ((c6 : Int) * ((W ^ 6 : Nat) : Int) * ((K ^ 3 : Nat) : Int)) = ((W ^ 6 : Nat) : Int) * ((K ^ 3 : Nat) : Int) * ((g : Int) * (c6 : Int)) := by ac_rfl
      have t4 : (g : Int) * ((c4 : Int) * ((W ^ 4 : Nat) : Int) * ((K ^ 5 : Nat) : Int)) = ((W ^ 4 : Nat) : Int) * ((K ^ 5 : Nat) : Int) * ((g : Int) * (c4 : Int)) := by ac_rfl
      have t2 : (g : Int) * ((c2 : Int) * ((W ^ 2 : Nat) : Int) * ((K ^ 7 : Nat) : Int)) = ((W ^ 2 : Nat) : Int) * ((K ^ 7 : Nat) : Int) * ((g : Int) * (c2 : Int)) := by ac_rfl
      have t7 : (g : Int) * ((c7 : Int) * ((W ^ 7 : Nat) : Int) * ((K ^ 2 : Nat) : Int)) = ((W ^ 7 : Nat) : Int) * ((K ^ 2 : Nat) : Int) * ((g : Int) * (c7 : Int)) := by ac_rfl
      have t5 : (g : Int) * ((c5 : Int) * ((W ^ 5 : Nat) : Int) * ((K ^ 4 : Nat) : Int)) = ((W ^ 5 : Nat) : Int) * ((K ^ 4 : Nat) : Int) * ((g : Int) * (c5 : Int)) := by ac_rfl
      have t3 : (g : Int) * ((c3 : Int) * ((W ^ 3 : Nat) : Int) * ((K ^ 6 : Nat) : Int)) = ((W ^ 3 : Nat) : Int) * ((K ^ 6 : Nat) : Int) * ((g : Int) * (c3 : Int)) := by ac_rfl
      have t0 : (g : Int) * ((c0 : Int) * ((K ^ 9 : Nat) : Int)) = ((K ^ 9 : Nat) : Int) * ((g : Int) * (c0 : Int)) := by ac_rfl
      rw [t9, t6, t4, t2, t7, t5, t3, t0]
      simp only [Int.natCast_mul, Int.mul_neg] at hsum0
      omega
    have hg_nz : (g : Int) ≠ 0 := by omega
    have hdiff0 := Int.eq_of_mul_eq_mul_left hg_nz (hg_factor.trans (Int.mul_zero (g : Int)).symm)
    exact p9Shape_nonzero_of_mod_p_w15 c9 c6 c4 c2 c7 c5 c3 c0 p hp2 hm_p W K hW hK (by omega)
  intro W K u hW hK hu1 hu9
  by_cases hu4 : u ≤ 4
  · exact laurent_9x9_t3u3_all_u_cone_positivity_and_multiu_nonvanishing.2.2.1 W K u hW hK hu1 hu4
  · rcases (by omega : u = 5 ∨ u = 6 ∨ u = 7 ∨ u = 8 ∨ u = 9) with rfl | rfl | rfl | rfl | rfl
    · rcases t3u3_u5_mod13_cert with ⟨hsh, hm, ha0, hi, ht1⟩
      exact hu_kill W K 5 5324 _ _ _ _ _ _ _ _ 13 hW hK (by decide) (by decide) (by decide)
        hsh (p9_only0_of_dehomog_w15 13 _ _ _ _ _ _ _ _ 12 6 12 0 7 0 3 5 (by decide) hm ha0 hi ht1)
    · rcases t3u3_u6_mod53_cert with ⟨hsh, hm, ha0, hi, ht1⟩
      exact hu_kill W K 6 44328437289500 _ _ _ _ _ _ _ _ 53 hW hK (by decide) (by decide) (by decide)
        hsh (p9_only0_of_dehomog_w15 53 _ _ _ _ _ _ _ _ 41 52 23 4 52 29 24 9 (by decide) hm ha0 hi ht1)
    · rcases t3u3_u7_mod13_cert with ⟨hsh, hm, ha0, hi, ht1⟩
      exact hu_kill W K 7 4 _ _ _ _ _ _ _ _ 13 hW hK (by decide) (by decide) (by decide)
        hsh (p9_only0_of_dehomog_w15 13 _ _ _ _ _ _ _ _ 5 9 5 0 4 0 11 1 (by decide) hm ha0 hi ht1)
    · rcases t3u3_u8_mod31_cert with ⟨hsh, hm, ha0, hi, ht1⟩
      exact hu_kill W K 8 38382812500 _ _ _ _ _ _ _ _ 31 hW hK (by decide) (by decide) (by decide)
        hsh (p9_only0_of_dehomog_w15 31 _ _ _ _ _ _ _ _ 2 20 7 8 23 17 16 30 (by decide) hm ha0 hi ht1)
    · rcases t3u3_u9_mod83_cert with ⟨hsh, hm, ha0, hi, ht1⟩
      exact hu_kill W K 9 9410548 _ _ _ _ _ _ _ _ 83 hW hK (by decide) (by decide) (by decide)
        hsh (p9_only0_of_dehomog_w15 83 _ _ _ _ _ _ _ _ 7 22 68 43 39 71 37 62 (by decide) hm ha0 hi ht1)

private theorem p_val_decomp_w15 :
    ∀ (fuel p n : Nat), p ≥ 2 -> n ≥ 1 -> n ≤ fuel ->
      ∃ r m : Nat, n = p ^ r * m ∧ m ≥ 1 ∧ m % p ≠ 0
  | 0, _, n, _, hn1, hle => by omega
  | fuel + 1, p, n, hp, hn1, hle => by
    by_cases hm0 : n % p = 0
    · have hq_pos : n / p ≥ 1 := by
        rcases Nat.dvd_of_mod_eq_zero hm0 with ⟨q, hq⟩
        cases q with
        | zero => rw [Nat.mul_zero] at hq; omega
        | succ q' =>
          have hp0 : 0 < p := by omega
          rw [hq, Nat.mul_comm p (q' + 1), Nat.mul_div_cancel _ hp0]; omega
      have hq_lt : n / p < n := Nat.div_lt_self (by omega) hp
      rcases p_val_decomp_w15 fuel p (n / p) hp hq_pos (by omega) with ⟨r, m, hrm, hm1, hmp⟩
      refine ⟨r + 1, m, ?_, hm1, hmp⟩
      have hn_eq : n = p * (n / p) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hm0)).symm
      rw [hn_eq, hrm, Nat.pow_succ, Nat.mul_comm (p ^ r) p, Nat.mul_assoc]
    · exact ⟨0, n, by simp, hn1, hm0⟩

set_option maxRecDepth 65536 in
private theorem t3u3_u10_newton_divisibility_w15 :
    ∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 -> u ≥ 10 ->
      intDet 9 (laurentTwoBaseT3U3Mat9 W K u) = 0 ->
      3 ^ ((2 * u + 8) / 9) ∣ (W / Nat.gcd W K) ∧
      2 ^ ((u + 2) / 4) ∣ (K / Nat.gcd W K) := by
  have hclosed_u := laurent_9x9_t3u3_all_u_cone_positivity_and_multiu_nonvanishing.1
  intro W K u hW hK hu10 hz
  have hu1 : u ≥ 1 := by omega
  exact (by
      have hc := hclosed_u W K u hW hu1
      rw [hz, Int.mul_zero, evalPoly4_eq_slice_sum10_w15 W K u] at hc
      have h6u_pos : ((2 ^ (3 * u) * 3 ^ (3 * u) : Nat) : Int) > 0 := by
        have hp : 2 ^ (3 * u) * 3 ^ (3 * u) ≥ 1 :=
          Nat.mul_le_mul (nat_pow_pos_of_pos 2 (by decide) _) (pow3_pos_nat _)
        omega
      have hpoly0 : intSumPrefix 10 (fun k =>
          ((W ^ (9 - k.val) * K ^ k.val : Nat) : Int) * slicePoly4CoeffInt u k.val t3u3CorePoly) 10 = 0 := by
        by_cases h0 : intSumPrefix 10 (fun k =>
            ((W ^ (9 - k.val) * K ^ k.val : Nat) : Int) * slicePoly4CoeffInt u k.val t3u3CorePoly) 10 = 0
        · exact h0
        · exfalso
          rcases (by omega :
            intSumPrefix 10 (fun k => ((W ^ (9 - k.val) * K ^ k.val : Nat) : Int) * slicePoly4CoeffInt u k.val t3u3CorePoly) 10 > 0 ∨
            intSumPrefix 10 (fun k => ((W ^ (9 - k.val) * K ^ k.val : Nat) : Int) * slicePoly4CoeffInt u k.val t3u3CorePoly) 10 < 0) with hg | hl
          · have := Int.mul_pos h6u_pos hg; omega
          · have := Int.mul_neg_of_pos_of_neg h6u_pos hl; omega
      -- Factor out `g^9` where `g = Nat.gcd W K`:
      let g := Nat.gcd W K
      have hg_pos : g ≥ 1 := Nat.gcd_pos_of_pos_left K hW
      let w := W / g
      let kn := K / g
      have hW_g : W = g * w := (Nat.mul_div_cancel' (Nat.gcd_dvd_left W K)).symm
      have hK_g : K = g * kn := (Nat.mul_div_cancel' (Nat.gcd_dvd_right W K)).symm
      have hw_pos : w ≥ 1 := Nat.pos_of_ne_zero (fun h0 => by
        have : W = 0 := by rw [hW_g, h0, Nat.mul_zero]
        omega)
      have hkn_pos : kn ≥ 1 := Nat.pos_of_ne_zero (fun h0 => by
        have : K = 0 := by rw [hK_g, h0, Nat.mul_zero]
        omega)
      have hhom9 : ∀ k : Fin 10, W ^ (9 - k.val) * K ^ k.val = g ^ 9 * (w ^ (9 - k.val) * kn ^ k.val) := by
        intro k
        rw [hW_g, hK_g, mul_pow_w15c g w (9 - k.val), mul_pow_w15c g kn k.val]
        calc (g ^ (9 - k.val) * w ^ (9 - k.val)) * (g ^ k.val * kn ^ k.val)
            = (g ^ (9 - k.val) * g ^ k.val) * (w ^ (9 - k.val) * kn ^ k.val) := by ac_rfl
          _ = g ^ 9 * (w ^ (9 - k.val) * kn ^ k.val) := by
                rw [← Nat.pow_add, show 9 - k.val + k.val = 9 by have := k.isLt; omega]
      have hsum_mul10 : ∀ (c : Int) (f : Fin 10 -> Int) (m : Nat), m ≤ 10 ->
          intSumPrefix 10 (fun k => c * f k) m = c * intSumPrefix 10 f m := by
        intro c f m hm; induction m with
        | zero => simp [intSumPrefix]
        | succ m' ih =>
          have hlt : m' < 10 := hm
          simp only [intSumPrefix, hlt, dite_true, ih (Nat.le_of_lt hm), Int.mul_add]
      have hfg : (fun k : Fin 10 =>
            ((W ^ (9 - k.val) * K ^ k.val : Nat) : Int) * slicePoly4CoeffInt u k.val t3u3CorePoly) =
          (fun k : Fin 10 =>
            ((g ^ 9 : Nat) : Int) *
              (((w ^ (9 - k.val) * kn ^ k.val : Nat) : Int) * slicePoly4CoeffInt u k.val t3u3CorePoly)) := by
        funext k; rw [hhom9 k, Int.natCast_mul, Int.mul_assoc]
      rw [hfg, hsum_mul10 _ _ 10 (Nat.le_refl 10)] at hpoly0
      have hg9_nz : ((g ^ 9 : Nat) : Int) ≠ 0 := by
        have := nat_pow_pos_of_pos g hg_pos 9; omega
      have hprim0 := Int.eq_of_mul_eq_mul_left hg9_nz (hpoly0.trans (Int.mul_zero _).symm)
      rw [t3u3_ten_sum_w15] at hprim0
      dsimp only at hprim0
      rw [Nat.sub_zero 9, Nat.pow_zero kn, Nat.mul_one (w ^ 9),
          show (9 : Nat) - 2 = 7 from rfl, show (9 : Nat) - 3 = 6 from rfl,
          show (9 : Nat) - 4 = 5 from rfl, show (9 : Nat) - 5 = 4 from rfl,
          show (9 : Nat) - 6 = 3 from rfl, show (9 : Nat) - 7 = 2 from rfl,
          Nat.sub_self 9, Nat.pow_zero w, Nat.one_mul (kn ^ 9)] at hprim0
      -- Valuation lemmas on `S_k := slicePoly4CoeffInt u k t3u3CorePoly` for `u ≥ 10`:
      rcases bool_and_split t3u3_val_and_7_11_certs.1 with ⟨hall_m, _⟩
      have hm_props : ∀ m ∈ t3u3CorePoly,
          let b := m.2.1
          let c := m.2.2.1
          let d := m.2.2.2.1
          let cf := m.2.2.2.2
          (b ≠ 1 ∧ b ≠ 8) ∧
          (b = 0 -> (d = 0 ∧ c = 6 ∧ cf = -4) ∨ (d ≥ 1 ∧ c ≥ 6)) ∧
          ((b = 2 ∨ b = 3 ∨ b = 4) -> d ≥ 1 ∧ c ≥ 2) ∧
          ((b = 5 ∨ b = 7) -> d ≥ 2 ∧ (c ≥ 2 ∨ (c = 1 ∧ cf % 2 = 0))) ∧
          (b = 6 -> d ≥ 2 ∧ (c ≥ 2 ∨ (c = 1 ∧ cf % 4 = 0))) ∧
          (b = 9 -> d ≥ 6 ∧ ((c = 0 ∧ cf = 4) ∨ c ≥ 1)) := by
        intro m hm
        have hb := List.all_eq_true.mp hall_m m hm
        rcases bool_and_split hb with ⟨hb1, _⟩
        rcases bool_and_split hb1 with ⟨hb2, hp9⟩
        rcases bool_and_split hb2 with ⟨hb3, hp6⟩
        rcases bool_and_split hb3 with ⟨hb4, hp57⟩
        rcases bool_and_split hb4 with ⟨hb5, hp234⟩
        rcases bool_and_split hb5 with ⟨hb6, hp0⟩
        rcases bool_and_split hb6 with ⟨_, hne18⟩
        refine ⟨of_decide_eq_true hne18, ?_, ?_, ?_, ?_, ?_⟩
        · intro h; simp only [h, beq_self_eq_true, ite_true] at hp0
          rcases of_decide_eq_true hp0 with ⟨hd, hc_e, hcf⟩ | hr
          · exact Or.inl ⟨beq_iff_eq.mp hd, beq_iff_eq.mp hc_e, beq_iff_eq.mp hcf⟩
          · exact Or.inr hr
        · intro h
          have hc_or : (m.2.1 == 2 || m.2.1 == 3 || m.2.1 == 4) = true := by
            rcases h with h2 | h3 | h4
            · simp [h2]
            · simp [h3]
            · simp [h4]
          simp only [hc_or, ite_true] at hp234; exact of_decide_eq_true hp234
        · intro h
          have hc_or : (m.2.1 == 5 || m.2.1 == 7) = true := by
            rcases h with h5 | h7
            · simp [h5]
            · simp [h7]
          simp only [hc_or, ite_true] at hp57
          rcases of_decide_eq_true hp57 with ⟨hd2, hc2 | ⟨hc1, hcf2⟩⟩
          · exact ⟨hd2, Or.inl hc2⟩
          · exact ⟨hd2, Or.inr ⟨beq_iff_eq.mp hc1, beq_iff_eq.mp hcf2⟩⟩
        · intro h; simp only [h, beq_self_eq_true, ite_true] at hp6
          rcases of_decide_eq_true hp6 with ⟨hd2, hc2 | ⟨hc1, hcf4⟩⟩
          · exact ⟨hd2, Or.inl hc2⟩
          · exact ⟨hd2, Or.inr ⟨beq_iff_eq.mp hc1, beq_iff_eq.mp hcf4⟩⟩
        · intro h; simp only [h, beq_self_eq_true, ite_true] at hp9
          rcases of_decide_eq_true hp9 with ⟨hd6, ⟨hc0, hcf4⟩ | hc1⟩
          · exact ⟨hd6, Or.inl ⟨beq_iff_eq.mp hc0, beq_iff_eq.mp hcf4⟩⟩
          · exact ⟨hd6, Or.inr hc1⟩
      -- Generic slice divisibility helper:
      have hterm_23_dvd : ∀ (c d e2 e3 : Nat) (cf : Int),
          e2 ≤ c * u -> e3 ≤ d * u ->
          (((2 ^ e2 * 3 ^ e3 : Nat) : Int)) ∣ cf * (((2 ^ c * 3 ^ d) ^ u : Nat) : Int) := by
        intro c d e2 e3 cf he2 he3
        have hp_eq : (2 ^ c * 3 ^ d) ^ u = (2 ^ e2 * 3 ^ e3) * (2 ^ (c * u - e2) * 3 ^ (d * u - e3)) := by
          rw [mul_pow_w15c (2 ^ c) (3 ^ d) u, pow_pow_eq_mul_w5 2 c u, pow_pow_eq_mul_w5 3 d u]
          conv => lhs; lhs; rw [show c * u = e2 + (c * u - e2) by omega, Nat.pow_add]
          conv => lhs; rhs; rw [show d * u = e3 + (d * u - e3) by omega, Nat.pow_add]
          ac_rfl
        have hcast : (((2 ^ c * 3 ^ d) ^ u : Nat) : Int) =
            ((2 ^ e2 * 3 ^ e3 : Nat) : Int) * ((2 ^ (c * u - e2) * 3 ^ (d * u - e3) : Nat) : Int) := by
          rw [hp_eq, Int.natCast_mul]
        rw [hcast]
        exact ⟨cf * ((2 ^ (c * u - e2) * 3 ^ (d * u - e3) : Nat) : Int), by ac_rfl⟩
      have hslice_dvd : ∀ (k : Nat) (D : Int) (ms : List Mono4),
          (∀ m ∈ ms, m.2.1 = k -> D ∣ m.2.2.2.2 * (((2 ^ m.2.2.1 * 3 ^ m.2.2.2.1) ^ u : Nat) : Int)) ->
          D ∣ slicePoly4CoeffInt u k ms := by
        intro k D ms; induction ms with
        | nil => intro _; exact ⟨0, by simp [slicePoly4CoeffInt]⟩
        | cons m0 tl ih =>
          rcases m0 with ⟨a, b, c, d, cf⟩
          intro hd
          have iht := ih (fun m hm => hd m (List.mem_cons_of_mem _ hm))
          simp only [slicePoly4CoeffInt]
          by_cases hcond_b : (a == 9 - k && b == k) = true
          · rcases bool_and_split hcond_b with ⟨_, hbk⟩
            simp only [hcond_b, ite_true]
            exact Int.dvd_add (hd (a, b, c, d, cf) List.mem_cons_self (beq_iff_eq.mp hbk)) iht
          · simp only [hcond_b, Bool.false_eq_true, ite_false, Int.zero_add]; exact iht
      let S := fun k : Nat => slicePoly4CoeffInt u k t3u3CorePoly
      have hS1_0 : S 1 = 0 := by
        have h0 : ∀ ms : List Mono4, (∀ m ∈ ms, m.2.1 ≠ 1) -> slicePoly4CoeffInt u 1 ms = 0 := by
          intro ms; induction ms with
          | nil => intro _; rfl
          | cons m0 tl ih =>
            rcases m0 with ⟨a, b, c, d, cf⟩; intro hne
            have hbf : (b == 1) = false := beq_false_of_ne (hne _ List.mem_cons_self)
            simp [slicePoly4CoeffInt, hbf, ih (fun m hm => hne m (List.mem_cons_of_mem _ hm))]
        exact h0 t3u3CorePoly (fun m hm => (hm_props m hm).1.1)
      have hS8_0 : S 8 = 0 := by
        have h0 : ∀ ms : List Mono4, (∀ m ∈ ms, m.2.1 ≠ 8) -> slicePoly4CoeffInt u 8 ms = 0 := by
          intro ms; induction ms with
          | nil => intro _; rfl
          | cons m0 tl ih =>
            rcases m0 with ⟨a, b, c, d, cf⟩; intro hne
            have hbf : (b == 8) = false := beq_false_of_ne (hne _ List.mem_cons_self)
            simp [slicePoly4CoeffInt, hbf, ih (fun m hm => hne m (List.mem_cons_of_mem _ hm))]
        exact h0 t3u3CorePoly (fun m hm => (hm_props m hm).1.2)
      -- Symbolic 3-adic properties on `S_2..S_9` and `S_0`:
      have h3_u_S : ∀ k : Nat, (k = 2 ∨ k = 3 ∨ k = 4) ->
          ((3 ^ u : Nat) : Int) ∣ S k := by
        intro k hk
        rw [← show ((2 ^ 0 * 3 ^ u : Nat) : Int) = ((3 ^ u : Nat) : Int) by simp]
        exact hslice_dvd k ((2 ^ 0 * 3 ^ u : Nat) : Int) t3u3CorePoly (fun m hm hbk => by
          have hd1 := ((hm_props m hm).2.2.1 (hbk ▸ hk)).1
          exact hterm_23_dvd m.2.2.1 m.2.2.2.1 0 u m.2.2.2.2 (Nat.zero_le _)
            (Nat.le_mul_of_pos_left u hd1))
      have h3_2u_S : ∀ k : Nat, (k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 9) ->
          ((3 ^ (2 * u) : Nat) : Int) ∣ S k := by
        intro k hk
        rw [← show ((2 ^ 0 * 3 ^ (2 * u) : Nat) : Int) = ((3 ^ (2 * u) : Nat) : Int) by simp]
        exact hslice_dvd k ((2 ^ 0 * 3 ^ (2 * u) : Nat) : Int) t3u3CorePoly (fun m hm hbk => by
          have hd2 : m.2.2.2.1 ≥ 2 := by
            rcases hk with rfl | rfl | rfl | rfl
            · exact ((hm_props m hm).2.2.2.1 (Or.inl hbk)).1
            · exact ((hm_props m hm).2.2.2.2.1 hbk).1
            · exact ((hm_props m hm).2.2.2.1 (Or.inr hbk)).1
            · have := ((hm_props m hm).2.2.2.2.2 hbk).1; omega
          exact hterm_23_dvd m.2.2.1 m.2.2.2.1 0 (2 * u) m.2.2.2.2 (Nat.zero_le _)
            (Nat.mul_le_mul_right u hd2))
      -- `S_0` mod 3: unique `d = 0` term in `t3u3CorePoly` is `(9, 0, 6, 0, -4)`!
      have hS0_not3 : ¬ ((3 : Int) ∣ S 0) := by
        -- Split `slicePoly4CoeffInt u 0` into `d = 0` terms + `d ≥ 1` terms:
        let slice0_d0 : List Mono4 -> Int := fun ms =>
          ms.foldr (fun m acc =>
            if m.1 == 9 && m.2.1 == 0 && m.2.2.2.1 == 0 then
              m.2.2.2.2 * (((2 ^ m.2.2.1 * 3 ^ m.2.2.2.1) ^ u : Nat) : Int) + acc
            else acc) 0
        have hsplit0 : ∀ ms : List Mono4,
            (∀ m ∈ ms, m.2.1 = 0 -> m.2.2.2.1 = 0 ∨ m.2.2.2.1 ≥ 1) ->
            (3 : Int) ∣ (slicePoly4CoeffInt u 0 ms - slice0_d0 ms) := by
          intro ms; induction ms with
          | nil => intro _; exact ⟨0, by simp [slicePoly4CoeffInt, slice0_d0]⟩
          | cons m0 tl ih =>
            rcases m0 with ⟨a, b, c, d, cf⟩; intro h01
            rcases ih (fun m hm => h01 m (List.mem_cons_of_mem _ hm)) with ⟨q, hq⟩
            simp only [slicePoly4CoeffInt, slice0_d0, List.foldr_cons, Nat.sub_zero]
            by_cases hab : (a == 9 && b == 0) = true
            · by_cases hd0 : (d == 0) = true
              · simp only [hab, hd0, Bool.and_self, ite_true]
                rw [show (cf * (((2 ^ c * 3 ^ d) ^ u : Nat) : Int) + slicePoly4CoeffInt u 0 tl) -
                      (cf * (((2 ^ c * 3 ^ d) ^ u : Nat) : Int) + slice0_d0 tl) =
                    slicePoly4CoeffInt u 0 tl - slice0_d0 tl by omega]
                exact ⟨q, hq⟩
              · have hd0f : (d == 0) = false := Bool.eq_false_iff.mpr hd0
                simp only [hab, hd0f, Bool.and_false, Bool.false_eq_true, ite_true, ite_false]
                have hd_ge1 : d ≥ 1 := by
                  have hd_ne : d ≠ 0 := beq_eq_false_iff_ne.mp hd0f; omega
                rcases hterm_23_dvd c d 0 1 cf (Nat.zero_le _)
                  (by have := Nat.mul_le_mul hd_ge1 hu10; omega) with ⟨q2, hq2⟩
                simp only [Nat.pow_zero, Nat.pow_one, Nat.one_mul] at hq2
                rw [show ((3 : Nat) : Int) = 3 from rfl] at hq2
                rw [show (cf * (((2 ^ c * 3 ^ d) ^ u : Nat) : Int) + slicePoly4CoeffInt u 0 tl) - slice0_d0 tl =
                    cf * (((2 ^ c * 3 ^ d) ^ u : Nat) : Int) + (slicePoly4CoeffInt u 0 tl - slice0_d0 tl) by omega,
                    hq2, hq]
                exact ⟨q2 + q, by rw [Int.mul_add]⟩
            · simp only [hab, Bool.false_and, Bool.false_eq_true, ite_false, Int.zero_add]
              exact ⟨q, hq⟩
        have hd0_only : t3u3CorePoly.filter (fun m => m.1 == 9 && m.2.1 == 0 && m.2.2.2.1 == 0) =
            [(9, 0, 6, 0, -4)] := by decide
        have hd0_val : slice0_d0 t3u3CorePoly = -4 * (((2 ^ 6) ^ u : Nat) : Int) := by
          have hflt : ∀ ms : List Mono4,
              slice0_d0 ms = slice0_d0 (ms.filter (fun m => m.1 == 9 && m.2.1 == 0 && m.2.2.2.1 == 0)) := by
            intro ms; induction ms with
            | nil => rfl
            | cons m0 tl ih =>
              simp only [slice0_d0, List.foldr_cons, List.filter_cons]
              by_cases hc_m : (m0.1 == 9 && m0.2.1 == 0 && m0.2.2.2.1 == 0) = true
              · simp only [hc_m, ite_true, List.foldr_cons]; congr 1
              · simp only [hc_m, Bool.false_eq_true, ite_false]; exact ih
          rw [hflt t3u3CorePoly, hd0_only]
          simp [slice0_d0]
        rcases hsplit0 t3u3CorePoly (fun _ _ _ => by omega) with ⟨q_diff, hq_diff⟩
        intro ⟨q_s0, hq_s0⟩
        have h3_dvd_4 : (3 : Int) ∣ (-4 : Int) * (((2 ^ 6) ^ u : Nat) : Int) := by
          rw [← hd0_val, show slice0_d0 t3u3CorePoly = S 0 - 3 * q_diff by dsimp only [S]; omega,
              hq_s0]
          exact ⟨q_s0 - q_diff, by rw [Int.mul_sub]⟩
        rcases h3_dvd_4 with ⟨q4, hq4⟩
        have hnat_dvd : 3 ∣ 1 * (4 * (2 ^ 6) ^ u) := by
          rw [Nat.one_mul]
          have habs := congrArg Int.natAbs hq4
          simp only [Int.natAbs_mul, Int.natAbs_natCast] at habs
          exact ⟨q4.natAbs, habs⟩
        have hcop4 : Nat.Coprime 3 4 := by decide
        have hcop64 : Nat.Coprime 3 ((2 ^ 6) ^ u) := ((by decide : Nat.Coprime 3 2).pow_right 6).pow_right u
        have hbad := (hcop4.mul_right hcop64).dvd_of_dvd_mul_right hnat_dvd
        omega
      -- Symbolic 2-adic properties on `S_0..S_7` and `S_9`:
      have h2_6u_S0 : ((2 ^ (6 * u) : Nat) : Int) ∣ S 0 := by
        rw [← show ((2 ^ (6 * u) * 3 ^ 0 : Nat) : Int) = ((2 ^ (6 * u) : Nat) : Int) by simp]
        exact hslice_dvd 0 ((2 ^ (6 * u) * 3 ^ 0 : Nat) : Int) t3u3CorePoly (fun m hm hb0 => by
          have hc6 : m.2.2.1 ≥ 6 := by
            rcases (hm_props m hm).2.1 hb0 with ⟨_, hc_e, _⟩ | ⟨_, hc_ge⟩ <;> omega
          exact hterm_23_dvd m.2.2.1 m.2.2.2.1 (6 * u) 0 m.2.2.2.2
            (Nat.mul_le_mul_right u hc6) (Nat.zero_le _))
      have h2_2u_S234 : ∀ k : Nat, (k = 2 ∨ k = 3 ∨ k = 4) ->
          ((2 ^ (2 * u) : Nat) : Int) ∣ S k := by
        intro k hk
        rw [← show ((2 ^ (2 * u) * 3 ^ 0 : Nat) : Int) = ((2 ^ (2 * u) : Nat) : Int) by simp]
        exact hslice_dvd k ((2 ^ (2 * u) * 3 ^ 0 : Nat) : Int) t3u3CorePoly (fun m hm hbk => by
          have hc2 := ((hm_props m hm).2.2.1 (hbk ▸ hk)).2
          exact hterm_23_dvd m.2.2.1 m.2.2.2.1 (2 * u) 0 m.2.2.2.2
            (Nat.mul_le_mul_right u hc2) (Nat.zero_le _))
      have h2_u1_S57 : ∀ k : Nat, (k = 5 ∨ k = 7) ->
          ((2 ^ (u + 1) : Nat) : Int) ∣ S k := by
        intro k hk
        exact hslice_dvd k ((2 ^ (u + 1) : Nat) : Int) t3u3CorePoly (fun m hm hbk => by
          rcases ((hm_props m hm).2.2.2.1 (hbk ▸ hk)).2 with hc2 | ⟨hc1, hcf2⟩
          · rw [← show ((2 ^ (u + 1) * 3 ^ 0 : Nat) : Int) = ((2 ^ (u + 1) : Nat) : Int) by simp]
            exact hterm_23_dvd m.2.2.1 m.2.2.2.1 (u + 1) 0 m.2.2.2.2
              (by have := Nat.mul_le_mul_right u hc2; omega) (Nat.zero_le _)
          · have hcf_d : (2 : Int) ∣ m.2.2.2.2 := ⟨m.2.2.2.2 / 2, by omega⟩
            rcases hcf_d with ⟨qm, hqm⟩
            rcases hterm_23_dvd m.2.2.1 m.2.2.2.1 u 0 qm
              (by rw [hc1, Nat.one_mul]; exact Nat.le_refl u) (Nat.zero_le _) with ⟨qt, hqt⟩
            simp only [Nat.pow_zero, Nat.mul_one] at hqt
            have hmul2 : m.2.2.2.2 * (((2 ^ m.2.2.1 * 3 ^ m.2.2.2.1) ^ u : Nat) : Int) =
                2 * (qm * (((2 ^ m.2.2.1 * 3 ^ m.2.2.2.1) ^ u : Nat) : Int)) := by rw [hqm]; ac_rfl
            rw [hmul2, hqt]
            exact ⟨qt, by
              rw [Nat.pow_succ 2 u, Int.natCast_mul]
              change (2 : Int) * (((2 ^ u : Nat) : Int) * qt) = (((2 ^ u : Nat) : Int) * 2) * qt
              ac_rfl⟩)
      have h2_u2_S6 : ((2 ^ (u + 2) : Nat) : Int) ∣ S 6 := by
        exact hslice_dvd 6 ((2 ^ (u + 2) : Nat) : Int) t3u3CorePoly (fun m hm hb6 => by
          rcases ((hm_props m hm).2.2.2.2.1 hb6).2 with hc2 | ⟨hc1, hcf4⟩
          · rw [← show ((2 ^ (u + 2) * 3 ^ 0 : Nat) : Int) = ((2 ^ (u + 2) : Nat) : Int) by simp]
            exact hterm_23_dvd m.2.2.1 m.2.2.2.1 (u + 2) 0 m.2.2.2.2
              (by have := Nat.mul_le_mul_right u hc2; omega) (Nat.zero_le _)
          · have hcf_d : (4 : Int) ∣ m.2.2.2.2 := ⟨m.2.2.2.2 / 4, by omega⟩
            rcases hcf_d with ⟨qm, hqm⟩
            rcases hterm_23_dvd m.2.2.1 m.2.2.2.1 u 0 qm
              (by rw [hc1, Nat.one_mul]; exact Nat.le_refl u) (Nat.zero_le _) with ⟨qt, hqt⟩
            simp only [Nat.pow_zero, Nat.mul_one] at hqt
            have hmul4 : m.2.2.2.2 * (((2 ^ m.2.2.1 * 3 ^ m.2.2.2.1) ^ u : Nat) : Int) =
                4 * (qm * (((2 ^ m.2.2.1 * 3 ^ m.2.2.2.1) ^ u : Nat) : Int)) := by rw [hqm]; ac_rfl
            rw [hmul4, hqt]
            exact ⟨qt, by
              rw [Nat.pow_add 2 u 2, show (2 : Nat) ^ 2 = 4 from rfl, Int.natCast_mul]
              change (4 : Int) * (((2 ^ u : Nat) : Int) * qt) = (((2 ^ u : Nat) : Int) * 4) * qt
              ac_rfl⟩)
      have hS9_v2 : ∃ R9 : Int, S 9 = 4 * R9 ∧ ¬ ((2 : Int) ∣ R9) := by
        let slice9_c0 : List Mono4 -> Int := fun ms =>
          ms.foldr (fun m acc =>
            if m.1 == 0 && m.2.1 == 9 && m.2.2.1 == 0 then
              m.2.2.2.2 * (((2 ^ m.2.2.1 * 3 ^ m.2.2.2.1) ^ u : Nat) : Int) + acc
            else acc) 0
        have hsplit9 : ∀ ms : List Mono4,
            (8 : Int) ∣ (slicePoly4CoeffInt u 9 ms - slice9_c0 ms) := by
          intro ms; induction ms with
          | nil => exact ⟨0, by simp [slicePoly4CoeffInt, slice9_c0]⟩
          | cons m0 tl ih =>
            rcases m0 with ⟨a, b, c, d, cf⟩
            rcases ih with ⟨q, hq⟩
            simp only [slicePoly4CoeffInt, slice9_c0, List.foldr_cons, Nat.sub_self]
            by_cases hab : (a == 0 && b == 9) = true
            · by_cases hc0 : (c == 0) = true
              · simp only [hab, hc0, Bool.and_self, ite_true]
                rw [show (cf * (((2 ^ c * 3 ^ d) ^ u : Nat) : Int) + slicePoly4CoeffInt u 9 tl) -
                      (cf * (((2 ^ c * 3 ^ d) ^ u : Nat) : Int) + slice9_c0 tl) =
                    slicePoly4CoeffInt u 9 tl - slice9_c0 tl by omega]
                exact ⟨q, hq⟩
              · have hc0f : (c == 0) = false := Bool.eq_false_iff.mpr hc0
                simp only [hab, hc0f, Bool.and_false, Bool.false_eq_true, ite_true, ite_false]
                have hc_ge1 : c ≥ 1 := by have := beq_eq_false_iff_ne.mp hc0f; omega
                rcases hterm_23_dvd c d 3 0 cf (by have := Nat.mul_le_mul hc_ge1 hu10; omega) (Nat.zero_le _) with ⟨q2, hq2⟩
                simp only [Nat.pow_zero, Nat.mul_one] at hq2
                rw [show ((2 ^ 3 : Nat) : Int) = 8 from rfl] at hq2
                rw [show (cf * (((2 ^ c * 3 ^ d) ^ u : Nat) : Int) + slicePoly4CoeffInt u 9 tl) - slice9_c0 tl =
                    cf * (((2 ^ c * 3 ^ d) ^ u : Nat) : Int) + (slicePoly4CoeffInt u 9 tl - slice9_c0 tl) by omega,
                    hq2, hq]
                exact ⟨q2 + q, by rw [Int.mul_add]⟩
            · simp only [hab, Bool.false_and, Bool.false_eq_true, ite_false, Int.zero_add]
              exact ⟨q, hq⟩
        have hc0_only : t3u3CorePoly.filter (fun m => m.1 == 0 && m.2.1 == 9 && m.2.2.1 == 0) =
            [(0, 9, 0, 6, 4)] := by decide
        have hc0_val : slice9_c0 t3u3CorePoly = 4 * (((3 ^ 6) ^ u : Nat) : Int) := by
          have hflt : ∀ ms : List Mono4,
              slice9_c0 ms = slice9_c0 (ms.filter (fun m => m.1 == 0 && m.2.1 == 9 && m.2.2.1 == 0)) := by
            intro ms; induction ms with
            | nil => rfl
            | cons m0 tl ih =>
              simp only [slice9_c0, List.foldr_cons, List.filter_cons]
              by_cases hc_m : (m0.1 == 0 && m0.2.1 == 9 && m0.2.2.1 == 0) = true
              · simp only [hc_m, ite_true, List.foldr_cons]; congr 1
              · simp only [hc_m, Bool.false_eq_true, ite_false]; exact ih
          rw [hflt t3u3CorePoly, hc0_only]
          simp [slice9_c0]
        rcases hsplit9 t3u3CorePoly with ⟨q8, hq8⟩
        refine ⟨(((3 ^ 6) ^ u : Nat) : Int) + 2 * q8, by dsimp only [S]; omega, ?_⟩
        intro ⟨qr, hqr⟩
        have h2_dvd_3 : (2 : Int) ∣ (((3 ^ 6) ^ u : Nat) : Int) := ⟨qr - q8, by omega⟩
        rcases h2_dvd_3 with ⟨q3, hq3⟩
        have hnat : 2 ∣ 1 * (3 ^ 6) ^ u := by
          rw [Nat.one_mul]
          have habs := congrArg Int.natAbs hq3
          simp only [Int.natAbs_mul, Int.natAbs_natCast] at habs
          exact ⟨q3.natAbs, habs⟩
        have hcop : Nat.Coprime 2 ((3 ^ 6) ^ u) := ((by decide : Nat.Coprime 2 3).pow_right 6).pow_right u
        have hbad := hcop.dvd_of_dvd_mul_right hnat
        omega
      -- Helper: prime `p ∈ {2, 3}` not dividing `X : Int` and not dividing `m : Nat` does not divide `X * (m^9 : Int)`!
      have hnot_dvd_mul_pow9 : ∀ (p : Nat) (X : Int) (m : Nat),
          (p = 2 ∨ p = 3) -> ¬ ((p : Int) ∣ X) -> m % p ≠ 0 ->
          ¬ ((p : Int) ∣ X * ((m ^ 9 : Nat) : Int)) := by
        intro p X m hp hX hm ⟨qz, hqz⟩
        have habs := congrArg Int.natAbs hqz
        rw [Int.natAbs_mul, Int.natAbs_mul] at habs
        simp only [Int.natAbs_natCast] at habs
        have hcop_m : Nat.Coprime p m := by
          rcases hp with rfl | rfl
          · have : m % 2 = 1 := by omega
            rw [Nat.Coprime, Nat.gcd_rec, this]; rfl
          · rcases (by omega : m % 3 = 1 ∨ m % 3 = 2) with h1 | h2
            · rw [Nat.Coprime, Nat.gcd_rec, h1]; rfl
            · rw [Nat.Coprime, Nat.gcd_rec, h2]; rfl
        have hp_dvd_X : p ∣ X.natAbs := (hcop_m.pow_right 9).dvd_of_dvd_mul_right ⟨qz.natAbs, habs⟩
        rcases hp_dvd_X with ⟨qx, hqx⟩
        apply hX
        by_cases hnn : 0 ≤ X
        · have hx_eq : X = (X.natAbs : Int) := by omega
          rw [hx_eq, hqx, Int.natCast_mul]; exact ⟨(qx : Int), rfl⟩
        · have hx_eq : X = -((X.natAbs : Int)) := by omega
          rw [hx_eq, hqx, Int.natCast_mul]; exact ⟨-(qx : Int), by rw [Int.mul_neg]⟩
      change ((w ^ 9 : Nat) : Int) * S 0 +
        ((w ^ (9 - 1) * kn ^ 1 : Nat) : Int) * S 1 +
        ((w ^ 7 * kn ^ 2 : Nat) : Int) * S 2 +
        ((w ^ 6 * kn ^ 3 : Nat) : Int) * S 3 +
        ((w ^ 5 * kn ^ 4 : Nat) : Int) * S 4 +
        ((w ^ 4 * kn ^ 5 : Nat) : Int) * S 5 +
        ((w ^ 3 * kn ^ 6 : Nat) : Int) * S 6 +
        ((w ^ 2 * kn ^ 7 : Nat) : Int) * S 7 +
        ((w ^ (9 - 8) * kn ^ 8 : Nat) : Int) * S 8 +
        ((kn ^ 9 : Nat) : Int) * S 9 = 0 at hprim0
      rw [hS1_0, hS8_0, Int.mul_zero, Int.mul_zero] at hprim0
      have hdvd_pow_ge : ∀ (b a e : Nat), a ≤ e -> ((b ^ a : Nat) : Int) ∣ ((b ^ e : Nat) : Int) := by
        intro b a e hae
        rw [show e = a + (e - a) by omega, Nat.pow_add, Int.natCast_mul]
        exact ⟨((b ^ (e - a) : Nat) : Int), rfl⟩
      have htail0_dvd : ∀ (E : Nat),
          ((3 ^ E : Nat) : Int) ∣ ((w ^ 7 * kn ^ 2 : Nat) : Int) * S 2 ->
          ((3 ^ E : Nat) : Int) ∣ ((w ^ 6 * kn ^ 3 : Nat) : Int) * S 3 ->
          ((3 ^ E : Nat) : Int) ∣ ((w ^ 5 * kn ^ 4 : Nat) : Int) * S 4 ->
          ((3 ^ E : Nat) : Int) ∣ ((w ^ 4 * kn ^ 5 : Nat) : Int) * S 5 ->
          ((3 ^ E : Nat) : Int) ∣ ((w ^ 3 * kn ^ 6 : Nat) : Int) * S 6 ->
          ((3 ^ E : Nat) : Int) ∣ ((w ^ 2 * kn ^ 7 : Nat) : Int) * S 7 ->
          ((3 ^ E : Nat) : Int) ∣ ((kn ^ 9 : Nat) : Int) * S 9 ->
          ((3 ^ E : Nat) : Int) ∣ S 0 * ((w ^ 9 : Nat) : Int) := by
        intro E d2 d3 d4 d5 d6 d7 d9
        rcases d2 with ⟨q2, e2⟩; rcases d3 with ⟨q3, e3⟩; rcases d4 with ⟨q4, e4⟩
        rcases d5 with ⟨q5, e5⟩; rcases d6 with ⟨q6, e6⟩; rcases d7 with ⟨q7, e7⟩; rcases d9 with ⟨q9, e9⟩
        refine ⟨-(q2 + q3 + q4 + q5 + q6 + q7 + q9), ?_⟩
        rw [Int.mul_comm (S 0), Int.mul_neg]
        simp only [Int.mul_add]
        omega
      have htail9_dvd : ∀ (E : Nat),
          ((2 ^ E : Nat) : Int) ∣ ((w ^ 9 : Nat) : Int) * S 0 ->
          ((2 ^ E : Nat) : Int) ∣ ((w ^ 7 * kn ^ 2 : Nat) : Int) * S 2 ->
          ((2 ^ E : Nat) : Int) ∣ ((w ^ 6 * kn ^ 3 : Nat) : Int) * S 3 ->
          ((2 ^ E : Nat) : Int) ∣ ((w ^ 5 * kn ^ 4 : Nat) : Int) * S 4 ->
          ((2 ^ E : Nat) : Int) ∣ ((w ^ 4 * kn ^ 5 : Nat) : Int) * S 5 ->
          ((2 ^ E : Nat) : Int) ∣ ((w ^ 3 * kn ^ 6 : Nat) : Int) * S 6 ->
          ((2 ^ E : Nat) : Int) ∣ ((w ^ 2 * kn ^ 7 : Nat) : Int) * S 7 ->
          ((2 ^ E : Nat) : Int) ∣ S 9 * ((kn ^ 9 : Nat) : Int) := by
        intro E d0 d2 d3 d4 d5 d6 d7
        rcases d0 with ⟨q0, e0⟩; rcases d2 with ⟨q2, e2⟩; rcases d3 with ⟨q3, e3⟩; rcases d4 with ⟨q4, e4⟩
        rcases d5 with ⟨q5, e5⟩; rcases d6 with ⟨q6, e6⟩; rcases d7 with ⟨q7, e7⟩
        refine ⟨-(q0 + q2 + q3 + q4 + q5 + q6 + q7), ?_⟩
        rw [Int.mul_comm (S 9), Int.mul_neg]
        simp only [Int.mul_add]
        omega
      -- Symbolic 3-adic Newton polygon lock: `3 ^ ((2 * u + 8) / 9) ∣ w`
      have hw_dvd3 : 3 ^ ((2 * u + 8) / 9) ∣ w := by
        rcases p_val_decomp_w15 w 3 w (by decide) hw_pos (Nat.le_refl w) with ⟨r, mw, hw_rm, _, hmw_nd3⟩
        have hr_ge : 9 * r ≥ 2 * u := by
          by_cases hge : 9 * r ≥ 2 * u
          · exact hge
          · exfalso
            have hd_234 : ∀ (a b k : Nat), a ≥ 5 -> (k = 2 ∨ k = 3 ∨ k = 4) ->
                ((3 ^ (9 * r + 1) : Nat) : Int) ∣ ((w ^ a * kn ^ b : Nat) : Int) * S k := by
              intro a b k ha5 hk
              have hwa : 3 ^ (r * a) ∣ w ^ a := by
                rw [hw_rm, mul_pow_w15c (3 ^ r) mw a, pow_pow_eq_mul_w5 3 r a]
                exact ⟨mw ^ a, rfl⟩
              rcases hwa with ⟨qw, hqw⟩
              rcases h3_u_S k hk with ⟨qs, hqs⟩
              have hra : r * a + u ≥ 9 * r + 1 := by
                have h5 : 5 * r ≤ r * a := by rw [Nat.mul_comm 5 r]; exact Nat.mul_le_mul_left r ha5
                omega
              rcases hdvd_pow_ge 3 (9 * r + 1) (r * a + u) hra with ⟨qp, hqp⟩
              rw [Nat.pow_add 3 (r * a) u, Int.natCast_mul] at hqp
              have hprod : ((w ^ a * kn ^ b : Nat) : Int) * S k =
                  (((3 ^ (r * a) : Nat) : Int) * ((3 ^ u : Nat) : Int)) *
                    (((qw : Nat) : Int) * ((kn ^ b : Nat) : Int) * qs) := by
                rw [hqw, Int.natCast_mul, Int.natCast_mul, hqs]; ac_rfl
              rw [hprod, hqp]
              exact ⟨qp * (((qw : Nat) : Int) * ((kn ^ b : Nat) : Int) * qs), by ac_rfl⟩
            have hd_5679 : ∀ (A : Int) (k : Nat), (k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 9) ->
                ((3 ^ (9 * r + 1) : Nat) : Int) ∣ A * S k := fun A k hk => by
              rcases Int.dvd_trans (hdvd_pow_ge 3 (9 * r + 1) (2 * u) (by omega)) (h3_2u_S k hk) with ⟨qs, hqs⟩
              exact ⟨A * qs, by rw [hqs]; ac_rfl⟩
            rcases htail0_dvd (9 * r + 1)
              (hd_234 7 2 2 (by decide) (Or.inl rfl))
              (hd_234 6 3 3 (by decide) (Or.inr (Or.inl rfl)))
              (hd_234 5 4 4 (by decide) (Or.inr (Or.inr rfl)))
              (hd_5679 _ 5 (Or.inl rfl))
              (hd_5679 _ 6 (Or.inr (Or.inl rfl)))
              (hd_5679 _ 7 (Or.inr (Or.inr (Or.inl rfl))))
              (hd_5679 _ 9 (Or.inr (Or.inr (Or.inr rfl)))) with ⟨q_tot, hq_tot⟩
            have hw9 : ((w ^ 9 : Nat) : Int) = ((3 ^ (9 * r) : Nat) : Int) * ((mw ^ 9 : Nat) : Int) := by
              rw [hw_rm, mul_pow_w15c (3 ^ r) mw 9, pow_pow_eq_mul_w5 3 r 9, Nat.mul_comm r 9, Int.natCast_mul]
            have hp9_nz : ((3 ^ (9 * r) : Nat) : Int) ≠ 0 := by
              have := pow3_pos_nat (9 * r); omega
            have heq_c : ((3 ^ (9 * r) : Nat) : Int) * (S 0 * ((mw ^ 9 : Nat) : Int)) =
                ((3 ^ (9 * r) : Nat) : Int) * (3 * q_tot) := by
              calc ((3 ^ (9 * r) : Nat) : Int) * (S 0 * ((mw ^ 9 : Nat) : Int))
                  = S 0 * (((3 ^ (9 * r) : Nat) : Int) * ((mw ^ 9 : Nat) : Int)) := by ac_rfl
                _ = S 0 * ((w ^ 9 : Nat) : Int) := by rw [← hw9]
                _ = ((3 ^ (9 * r) : Nat) : Int) * (3 * q_tot) := by
                      rw [hq_tot, Nat.pow_succ 3 (9 * r), Int.natCast_mul]
                      change (((3 ^ (9 * r) : Nat) : Int) * 3) * q_tot = ((3 ^ (9 * r) : Nat) : Int) * (3 * q_tot)
                      ac_rfl
            exact hnot_dvd_mul_pow9 3 (S 0) mw (Or.inr rfl) hS0_not3 hmw_nd3
              ⟨q_tot, Int.eq_of_mul_eq_mul_left hp9_nz heq_c⟩
        have hr_div : (2 * u + 8) / 9 ≤ r := by omega
        rw [hw_rm, show r = (2 * u + 8) / 9 + (r - (2 * u + 8) / 9) by omega, Nat.pow_add]
        exact ⟨3 ^ (r - (2 * u + 8) / 9) * mw, by ac_rfl⟩
      -- Symbolic 2-adic Newton polygon lock: `2 ^ ((u + 2) / 4) ∣ kn`
      rcases hS9_v2 with ⟨R9, hS9_eq, hR9_odd⟩
      have hkn_dvd2 : 2 ^ ((u + 2) / 4) ∣ kn := by
        rcases p_val_decomp_w15 kn 2 kn (by decide) hkn_pos (Nat.le_refl kn) with ⟨s, mk, hkn_sm, _, hmk_nd2⟩
        have hs_ge : 4 * s + 1 ≥ u := by
          by_cases hge : 4 * s + 1 ≥ u
          · exact hge
          · exfalso
            have hd_0 : ((2 ^ (9 * s + 3) : Nat) : Int) ∣ ((w ^ 9 : Nat) : Int) * S 0 := by
              rcases Int.dvd_trans (hdvd_pow_ge 2 (9 * s + 3) (6 * u) (by omega)) h2_6u_S0 with ⟨qs, hqs⟩
              exact ⟨((w ^ 9 : Nat) : Int) * qs, by rw [hqs]; ac_rfl⟩
            have hd_k : ∀ (a b e_s : Nat) (Sk : Int),
                9 * s + 3 ≤ s * b + e_s -> ((2 ^ e_s : Nat) : Int) ∣ Sk ->
                ((2 ^ (9 * s + 3) : Nat) : Int) ∣ ((w ^ a * kn ^ b : Nat) : Int) * Sk := by
              intro a b e_s Sk hle_e ⟨qs, hqs⟩
              have hkb : 2 ^ (s * b) ∣ kn ^ b := by
                rw [hkn_sm, mul_pow_w15c (2 ^ s) mk b, pow_pow_eq_mul_w5 2 s b]
                exact ⟨mk ^ b, rfl⟩
              rcases hkb with ⟨qk, hqk⟩
              rcases hdvd_pow_ge 2 (9 * s + 3) (s * b + e_s) hle_e with ⟨qp, hqp⟩
              rw [Nat.pow_add 2 (s * b) e_s, Int.natCast_mul] at hqp
              have hprod : ((w ^ a * kn ^ b : Nat) : Int) * Sk =
                  (((2 ^ (s * b) : Nat) : Int) * ((2 ^ e_s : Nat) : Int)) *
                    (((w ^ a : Nat) : Int) * ((qk : Nat) : Int) * qs) := by
                rw [hqk, Int.natCast_mul, Int.natCast_mul, hqs]; ac_rfl
              rw [hprod, hqp]
              exact ⟨qp * (((w ^ a : Nat) : Int) * ((qk : Nat) : Int) * qs), by ac_rfl⟩
            rcases htail9_dvd (9 * s + 3) hd_0
              (hd_k 7 2 (2 * u) (S 2) (by omega) (h2_2u_S234 2 (Or.inl rfl)))
              (hd_k 6 3 (2 * u) (S 3) (by omega) (h2_2u_S234 3 (Or.inr (Or.inl rfl))))
              (hd_k 5 4 (2 * u) (S 4) (by omega) (h2_2u_S234 4 (Or.inr (Or.inr rfl))))
              (hd_k 4 5 (u + 1) (S 5) (by omega) (h2_u1_S57 5 (Or.inl rfl)))
              (hd_k 3 6 (u + 2) (S 6) (by omega) h2_u2_S6)
              (hd_k 2 7 (u + 1) (S 7) (by omega) (h2_u1_S57 7 (Or.inr rfl))) with ⟨q_tot, hq_tot⟩
            have hkn9 : ((kn ^ 9 : Nat) : Int) = ((2 ^ (9 * s) : Nat) : Int) * ((mk ^ 9 : Nat) : Int) := by
              rw [hkn_sm, mul_pow_w15c (2 ^ s) mk 9, pow_pow_eq_mul_w5 2 s 9, Nat.mul_comm s 9, Int.natCast_mul]
            have hp2_nz : ((2 ^ (9 * s + 2) : Nat) : Int) ≠ 0 := by
              have := nat_pow_pos_of_pos 2 (by decide) (9 * s + 2); omega
            have heq_c : ((2 ^ (9 * s + 2) : Nat) : Int) * (R9 * ((mk ^ 9 : Nat) : Int)) =
                ((2 ^ (9 * s + 2) : Nat) : Int) * (2 * q_tot) := by
              calc ((2 ^ (9 * s + 2) : Nat) : Int) * (R9 * ((mk ^ 9 : Nat) : Int))
                  = (4 * R9) * (((2 ^ (9 * s) : Nat) : Int) * ((mk ^ 9 : Nat) : Int)) := by
                      rw [Nat.pow_add 2 (9 * s) 2, show (2 : Nat) ^ 2 = 4 from rfl, Int.natCast_mul]
                      change (((2 ^ (9 * s) : Nat) : Int) * 4) * (R9 * ((mk ^ 9 : Nat) : Int)) = _
                      ac_rfl
                _ = S 9 * ((kn ^ 9 : Nat) : Int) := by rw [← hS9_eq, ← hkn9]
                _ = ((2 ^ (9 * s + 2) : Nat) : Int) * (2 * q_tot) := by
                      rw [hq_tot, show 9 * s + 3 = (9 * s + 2) + 1 by omega, Nat.pow_succ 2 (9 * s + 2), Int.natCast_mul]
                      change (((2 ^ (9 * s + 2) : Nat) : Int) * 2) * q_tot = ((2 ^ (9 * s + 2) : Nat) : Int) * (2 * q_tot)
                      ac_rfl
            exact hnot_dvd_mul_pow9 2 R9 mk (Or.inl rfl) hR9_odd hmk_nd2
              ⟨q_tot, Int.eq_of_mul_eq_mul_left hp2_nz heq_c⟩
        have hs_div : (u + 2) / 4 ≤ s := by omega
        rw [hkn_sm, show s = (u + 2) / 4 + (s - (u + 2) / 4) by omega, Nat.pow_add]
        exact ⟨2 ^ (s - (u + 2) / 4) * mk, by ac_rfl⟩
      exact ⟨hw_dvd3, hkn_dvd2⟩)

private theorem t3u3_conefree_all_u_nonzero_w15 :
    ∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 -> u ≥ 1 ->
      ((W / Nat.gcd W K) % 27 ≠ 0 ∨ (K / Nat.gcd W K) % 8 ≠ 0) ->
      intDet 9 (laurentTwoBaseT3U3Mat9 W K u) ≠ 0 := by
  intro W K u hW hK hu1 hcond hz
  by_cases hu9 : u ≤ 9
  · exact t3u3_global_1_to_9_nonzero_w15 W K u hW hK hu1 hu9 hz
  · rcases t3u3_u10_newton_divisibility_w15 W K u hW hK (by omega) hz with ⟨hd3, hd2⟩
    have h27 : 27 ∣ 3 ^ ((2 * u + 8) / 9) := by
      have he : (2 * u + 8) / 9 = 3 + ((2 * u + 8) / 9 - 3) := by omega
      rw [he, Nat.pow_add]; exact ⟨3 ^ ((2 * u + 8) / 9 - 3), rfl⟩
    have h8 : 8 ∣ 2 ^ ((u + 2) / 4) := by
      have he : (u + 2) / 4 = 3 + ((u + 2) / 4 - 3) := by omega
      rw [he, Nat.pow_add]; exact ⟨2 ^ ((u + 2) / 4 - 3), rfl⟩
    have hw27 : (W / Nat.gcd W K) % 27 = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h27 hd3)
    have hk8 : (K / Nat.gcd W K) % 8 = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h8 hd2)
    rcases hcond with hw_ne | hk_ne
    · exact hw_ne hw27
    · exact hk_ne hk8

set_option maxRecDepth 65536 in
private theorem t3u3_27_8_u10_to_13_certs :
    evalSliceSum10Fast 27 8 10 < 0 ∧
    evalSliceSum10Fast 27 8 11 < 0 ∧
    evalSliceSum10Fast 27 8 12 < 0 ∧
    evalSliceSum10Fast 27 8 13 < 0 := by decide

private theorem t3u3_resonant_27_8_ray_all_u_nonzero_w15 :
    ∀ (c u : Nat), c ≥ 1 -> u ≥ 1 ->
      intDet 9 (laurentTwoBaseT3U3Mat9 (27 * c) (8 * c) u) ≠ 0 := by
  have hclosed_u := laurent_9x9_t3u3_all_u_cone_positivity_and_multiu_nonvanishing.1
  rcases t3u3_27_8_u10_to_13_certs with ⟨hs10, hs11, hs12, hs13⟩
  intro c u hc1 hu1
  by_cases hu9 : u ≤ 9
  · exact t3u3_global_1_to_9_nonzero_w15 (27 * c) (8 * c) u (by omega) (by omega) hu1 hu9
  · by_cases hu13 : u ≤ 13
    · intro hz
      have hdet := hclosed_u (27 * c) (8 * c) u (by omega) hu1
      rw [hz, Int.mul_zero, evalPoly4_eq_slice_sum10_w15 (27 * c) (8 * c) u] at hdet
      have hsum_mul10 : ∀ (m : Nat), m ≤ 10 ->
          intSumPrefix 10 (fun k =>
            (((27 * c) ^ (9 - k.val) * (8 * c) ^ k.val : Nat) : Int) *
              slicePoly4CoeffInt u k.val t3u3CorePoly) m =
            ((c ^ 9 : Nat) : Int) * intSumPrefix 10 (fun k =>
              ((27 ^ (9 - k.val) * 8 ^ k.val : Nat) : Int) *
                slicePoly4CoeffInt u k.val t3u3CorePoly) m := by
        intro m hm; induction m with
        | zero => simp [intSumPrefix]
        | succ m' ih =>
          have hlt : m' < 10 := hm
          simp only [intSumPrefix, hlt, dite_true, ih (Nat.le_of_lt hm), Int.mul_add]
          congr 1
          have hhom : (27 * c) ^ (9 - m') * (8 * c) ^ m' = c ^ 9 * (27 ^ (9 - m') * 8 ^ m') := by
            rw [mul_pow_w15c 27 c (9 - m'), mul_pow_w15c 8 c m']
            calc (27 ^ (9 - m') * c ^ (9 - m')) * (8 ^ m' * c ^ m')
                = (c ^ (9 - m') * c ^ m') * (27 ^ (9 - m') * 8 ^ m') := by ac_rfl
              _ = c ^ 9 * (27 ^ (9 - m') * 8 ^ m') := by
                    rw [← Nat.pow_add, show 9 - m' + m' = 9 by omega]
          rw [hhom, Int.natCast_mul, Int.mul_assoc]
      rw [hsum_mul10 10 (Nat.le_refl 10)] at hdet
      change 0 = ((2 ^ (3 * u) * 3 ^ (3 * u) : Nat) : Int) *
        (((c ^ 9 : Nat) : Int) * evalSliceSum10Fast 27 8 u) at hdet
      have h6_pos : ((2 ^ (3 * u) * 3 ^ (3 * u) : Nat) : Int) > 0 := by
        have := Nat.mul_le_mul (nat_pow_pos_of_pos 2 (by decide) (3 * u)) (pow3_pos_nat (3 * u)); omega
      have hc9_pos : ((c ^ 9 : Nat) : Int) > 0 := by
        have := nat_pow_pos_of_pos c hc1 9; omega
      have hs_neg : evalSliceSum10Fast 27 8 u < 0 := by
        rcases (by omega : u = 10 ∨ u = 11 ∨ u = 12 ∨ u = 13) with rfl | rfl | rfl | rfl
        · exact hs10
        · exact hs11
        · exact hs12
        · exact hs13
      have hm_neg := Int.mul_neg_of_pos_of_neg h6_pos (Int.mul_neg_of_pos_of_neg hc9_pos hs_neg)
      omega
    · intro hz
      rcases t3u3_u10_newton_divisibility_w15 (27 * c) (8 * c) u (by omega) (by omega) (by omega) hz with ⟨_, hd2⟩
      have hgcd_c : Nat.gcd (27 * c) (8 * c) = c := by
        apply Nat.dvd_antisymm
        · rcases Nat.gcd_dvd_left (27 * c) (8 * c) with ⟨q1, hq1⟩
          rcases Nat.gcd_dvd_right (27 * c) (8 * c) with ⟨q2, hq2⟩
          let g := Nat.gcd (27 * c) (8 * c)
          change 27 * c = g * q1 at hq1
          change 8 * c = g * q2 at hq2
          have hbez : 3 * (27 * c) = 10 * (8 * c) + c := by omega
          rw [hq1, hq2] at hbez
          have hle_q : 10 * q2 ≤ 3 * q1 := by
            by_cases hle : 10 * q2 ≤ 3 * q1
            · exact hle
            · exfalso
              have hg_pos : g ≥ 1 := Nat.gcd_pos_of_pos_left _ (by omega)
              have hm := Nat.mul_le_mul_left g (by omega : 3 * q1 + 1 ≤ 10 * q2)
              rw [Nat.mul_add, Nat.mul_one] at hm
              have e1 : 3 * (g * q1) = g * (3 * q1) := by ac_rfl
              have e2 : 10 * (g * q2) = g * (10 * q2) := by ac_rfl
              rw [e1, e2] at hbez; omega
          refine ⟨3 * q1 - 10 * q2, ?_⟩
          have hm_sub : g * (3 * q1 - 10 * q2) + g * (10 * q2) = g * (3 * q1) := by
            rw [← Nat.mul_add, Nat.sub_add_cancel hle_q]
          have e1 : 3 * (g * q1) = g * (3 * q1) := by ac_rfl
          have e2 : 10 * (g * q2) = g * (10 * q2) := by ac_rfl
          rw [e1, e2] at hbez
          generalize g * (3 * q1 - 10 * q2) = A, g * (10 * q2) = B, g * (3 * q1) = E at hm_sub hbez
          omega
        · exact Nat.dvd_gcd ⟨27, Nat.mul_comm 27 c⟩ ⟨8, Nat.mul_comm 8 c⟩
      rw [hgcd_c, Nat.mul_div_cancel 8 hc1] at hd2
      have h16 : 16 ∣ 2 ^ ((u + 2) / 4) := by
        have he : (u + 2) / 4 = 4 + ((u + 2) / 4 - 4) := by omega
        rw [he, Nat.pow_add]; exact ⟨2 ^ ((u + 2) / 4 - 4), rfl⟩
      have hle8 : 16 ≤ 8 := Nat.le_of_dvd (by decide) (Nat.dvd_trans h16 hd2)
      omega

private theorem t3u3_signlock_horizon_w15 :
    ∀ W K : Nat, W ≥ 1 -> K ≥ 1 ->
      t3u3SignLockHorizon W K ≥ 1 ∧
      (∀ u : Nat, u ≥ t3u3SignLockHorizon W K ->
        intDet 9 (laurentTwoBaseT3U3Mat9 W K u) ≠ 0) ∧
      (W < K -> ∀ u : Nat, u ≥ t3u3SignLockHorizon W K ->
        intDet 9 (laurentTwoBaseT3U3Mat9 W K u) > 0) ∧
      (K < W -> ∀ u : Nat, u ≥ t3u3SignLockHorizon W K ->
        intDet 9 (laurentTwoBaseT3U3Mat9 W K u) < 0) := by
  have hclosed_u := laurent_9x9_t3u3_all_u_cone_positivity_and_multiu_nonvanishing.1
  intro W K hW hK
  have hhor_ge1 : t3u3SignLockHorizon W K ≥ 1 := by unfold t3u3SignLockHorizon; omega
  have hintPow_ev : ∀ (x d : Nat), intPowNat (x : Int) d = ((x ^ d : Nat) : Int) := by
    intro x d; induction d with
    | zero => rfl
    | succ d' ih => simp [intPowNat, ih, Nat.pow_succ, Int.natCast_mul, Int.mul_comm]
  rcases bool_and_split t3u3_val_and_7_11_certs.1 with ⟨hall_m, hlead_flt⟩
  let leadSum : Nat -> List Mono4 -> Int := fun u ms =>
    ms.foldr (fun m acc =>
      if m.2.2.1 == 10 && m.2.2.2.1 == 10 then
        m.2.2.2.2 * ((W ^ m.1 * K ^ m.2.1 : Nat) : Int) * ((60466176 ^ u : Nat) : Int) + acc
      else acc) 0
  have hrem_bd : ∀ (u : Nat) (ms : List Mono4),
      (∀ m ∈ ms, ¬ (m.2.2.1 == 10 && m.2.2.2.1 == 10) -> 2 ^ m.2.2.1 * 3 ^ m.2.2.2.1 ≤ 45349632) ->
      (evalPoly4 (W : Int) (K : Int) ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int) ms - leadSum u ms).natAbs ≤
        t3u3RemAbsBound.aux W K ms * 45349632 ^ u := by
    intro u ms; induction ms with
    | nil => intro _; simp [evalPoly4, leadSum, t3u3RemAbsBound.aux]
    | cons m0 tl ih =>
      rcases m0 with ⟨a, b, c, d, cf⟩; intro hbd
      have iht := ih (fun m hm => hbd m (List.mem_cons_of_mem _ hm))
      have hpq : intPowNat ((2 ^ u : Nat) : Int) c * intPowNat ((3 ^ u : Nat) : Int) d =
          (((2 ^ c * 3 ^ d) ^ u : Nat) : Int) := by
        rw [hintPow_ev, hintPow_ev, ← Int.natCast_mul]
        apply congrArg Nat.cast
        rw [pow_pow_eq_mul_w5 2 u c, pow_pow_eq_mul_w5 3 u d, Nat.mul_comm u c, Nat.mul_comm u d,
            ← pow_pow_eq_mul_w5 2 c u, ← pow_pow_eq_mul_w5 3 d u, ← mul_pow_w15c]
      have hwk : intPowNat (W : Int) a * intPowNat (K : Int) b = ((W ^ a * K ^ b : Nat) : Int) := by
        rw [hintPow_ev, hintPow_ev, ← Int.natCast_mul]
      have hterm : cf * (intPowNat (W : Int) a * (intPowNat (K : Int) b *
          (intPowNat ((2 ^ u : Nat) : Int) c * intPowNat ((3 ^ u : Nat) : Int) d))) =
          cf * ((W ^ a * K ^ b : Nat) : Int) * (((2 ^ c * 3 ^ d) ^ u : Nat) : Int) := by
        rw [hpq, ← Int.mul_assoc (intPowNat (W : Int) a), hwk]; ac_rfl
      simp only [evalPoly4, evalMono4, hterm, leadSum, List.foldr_cons, t3u3RemAbsBound.aux]
      by_cases h10 : (c == 10 && d == 10) = true
      · rcases bool_and_split h10 with ⟨hc10, hd10⟩
        rw [beq_iff_eq.mp hc10, beq_iff_eq.mp hd10]
        simp only [beq_self_eq_true, Bool.and_self, ite_true, Nat.zero_add,
                   show 2 ^ 10 * 3 ^ 10 = 60466176 from rfl]
        rw [show (cf * ((W ^ a * K ^ b : Nat) : Int) * ((60466176 ^ u : Nat) : Int) +
              evalPoly4 (W : Int) (K : Int) ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int) tl) -
              (cf * ((W ^ a * K ^ b : Nat) : Int) * ((60466176 ^ u : Nat) : Int) + leadSum u tl) =
            evalPoly4 (W : Int) (K : Int) ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int) tl - leadSum u tl by omega]
        exact iht
      · simp only [h10, Bool.false_eq_true, ite_false]
        have hb_le : 2 ^ c * 3 ^ d ≤ 45349632 :=
          hbd (a, b, c, d, cf) List.mem_cons_self (by simp [h10])
        have hp_le := pow_mono_base_w15c (2 ^ c * 3 ^ d) 45349632 hb_le u
        let tA := cf * ((W ^ a * K ^ b : Nat) : Int) * (((2 ^ c * 3 ^ d) ^ u : Nat) : Int)
        let tB := evalPoly4 (W : Int) (K : Int) ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int) tl - leadSum u tl
        have hrew : (tA + evalPoly4 (W : Int) (K : Int) ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int) tl) - leadSum u tl =
            tA + tB := by dsimp [tB]; omega
        rw [hrew, Nat.add_mul]
        have htri_abs : (tA + tB).natAbs ≤ tA.natAbs + tB.natAbs := by omega
        have htA_le : tA.natAbs ≤ cf.natAbs * W ^ a * K ^ b * 45349632 ^ u := by
          dsimp only [tA]
          have hn1 : ((W ^ a * K ^ b : Nat) : Int).natAbs = W ^ a * K ^ b := by omega
          have hn2 : (((2 ^ c * 3 ^ d) ^ u : Nat) : Int).natAbs = (2 ^ c * 3 ^ d) ^ u := by omega
          rw [Int.natAbs_mul, Int.natAbs_mul, hn1, hn2, ← Nat.mul_assoc cf.natAbs (W ^ a) (K ^ b)]
          exact Nat.mul_le_mul_left (cf.natAbs * W ^ a * K ^ b) hp_le
        omega
  have hlead_closed : ∀ u : Nat,
      leadSum u t3u3CorePoly =
        ((W ^ 2 * K ^ 2 : Nat) : Int) * intPowNat ((K : Int) - (W : Int)) 5 *
          ((60466176 ^ u : Nat) : Int) := by
    intro u
    have hflt : ∀ ms : List Mono4,
        leadSum u ms =
          ((ms.filter (fun m => m.2.2.1 == 10 && m.2.2.2.1 == 10)).map
            (fun m => (m.1, m.2.1, m.2.2.2.2))).foldr
            (fun t acc => t.2.2 * ((W ^ t.1 * K ^ t.2.1 : Nat) : Int) * ((60466176 ^ u : Nat) : Int) + acc) 0 := by
      intro ms; induction ms with
      | nil => rfl
      | cons m0 tl ih =>
        simp only [leadSum, List.foldr_cons, List.filter_cons]
        by_cases hc : (m0.2.2.1 == 10 && m0.2.2.2.1 == 10) = true
        · simp only [hc, ite_true, List.map_cons, List.foldr_cons]; congr 1
        · simp only [hc, Bool.false_eq_true, ite_false]; exact ih
    rw [hflt t3u3CorePoly, beq_iff_eq.mp hlead_flt]
    simp only [List.foldr, Int.add_zero]
    let eL : Expr4 :=
      .sub (.add (.sub (.add (.sub (.mul (.const 1) (.mul (expr4Pow .v0 2) (expr4Pow .v1 7)))
                                   (.mul (.const 5) (.mul (expr4Pow .v0 3) (expr4Pow .v1 6))))
                             (.mul (.const 10) (.mul (expr4Pow .v0 4) (expr4Pow .v1 5))))
                       (.mul (.const 10) (.mul (expr4Pow .v0 5) (expr4Pow .v1 4))))
                 (.mul (.const 5) (.mul (expr4Pow .v0 6) (expr4Pow .v1 3))))
           (.mul (.const 1) (.mul (expr4Pow .v0 7) (expr4Pow .v1 2)))
    let eR : Expr4 :=
      .mul (.mul (expr4Pow .v0 2) (expr4Pow .v1 2)) (expr4Pow (.sub .v1 .v0) 5)
    have hid := expr4_eq_of_norm_sub_nil eL eR (by decide) (W : Int) (K : Int) 0 0
    have hexp_ev : ∀ (e : Expr4) (d : Nat),
        evalExpr4 (W : Int) (K : Int) 0 0 (expr4Pow e d) = intPowNat (evalExpr4 (W : Int) (K : Int) 0 0 e) d := by
      intro e d; induction d with
      | zero => rfl
      | succ d' ih => simp [expr4Pow, intPowNat, evalExpr4, ih]
    simp only [eL, eR, evalExpr4, hexp_ev] at hid
    simp only [hintPow_ev, ← Int.natCast_mul] at hid
    rw [← hid]
    let U60 : Int := ((60466176 ^ u : Nat) : Int)
    change 1 * ((W ^ 2 * K ^ 7 : Nat) : Int) * U60 +
        (-5 * ((W ^ 3 * K ^ 6 : Nat) : Int) * U60 +
          (10 * ((W ^ 4 * K ^ 5 : Nat) : Int) * U60 +
            (-10 * ((W ^ 5 * K ^ 4 : Nat) : Int) * U60 +
              (5 * ((W ^ 6 * K ^ 3 : Nat) : Int) * U60 +
                -1 * ((W ^ 7 * K ^ 2 : Nat) : Int) * U60)))) =
      (1 * ((W ^ 2 * K ^ 7 : Nat) : Int) - 5 * ((W ^ 3 * K ^ 6 : Nat) : Int) +
        10 * ((W ^ 4 * K ^ 5 : Nat) : Int) - 10 * ((W ^ 5 * K ^ 4 : Nat) : Int) +
        5 * ((W ^ 6 * K ^ 3 : Nat) : Int) - 1 * ((W ^ 7 * K ^ 2 : Nat) : Int)) * U60
    generalize ((W ^ 2 * K ^ 7 : Nat) : Int) = A2,
      ((W ^ 3 * K ^ 6 : Nat) : Int) = A3,
      ((W ^ 4 * K ^ 5 : Nat) : Int) = A4,
      ((W ^ 5 * K ^ 4 : Nat) : Int) = A5,
      ((W ^ 6 * K ^ 3 : Nat) : Int) = A6,
      ((W ^ 7 * K ^ 2 : Nat) : Int) = A7
    simp only [Int.sub_eq_add_neg, Int.add_mul, Int.neg_mul]
    omega
  have hpow_dom : ∀ B u : Nat, u ≥ 3 * (B + 1) -> B * 45349632 ^ u < 60466176 ^ u := by
    have h3n : ∀ n : Nat, (n + 2) * 45349632 ^ (3 * (n + 1)) < 60466176 ^ (3 * (n + 1)) := by
      intro n; induction n with
      | zero => decide
      | succ n' ih =>
        rw [show 3 * (n' + 1 + 1) = 3 + 3 * (n' + 1) by omega,
            Nat.pow_add 45349632 3, Nat.pow_add 60466176 3]
        have hstep_c : (n' + 3) * 45349632 ^ 3 ≤ 60466176 ^ 3 * (n' + 2) := by
          have h27 : 45349632 ^ 3 = 15116544 ^ 3 * 27 := by decide
          have h64 : 60466176 ^ 3 = 15116544 ^ 3 * 64 := by decide
          calc (n' + 3) * 45349632 ^ 3
              = 15116544 ^ 3 * (27 * (n' + 3)) := by rw [h27]; ac_rfl
            _ ≤ 15116544 ^ 3 * (64 * (n' + 2)) := Nat.mul_le_mul_left (15116544 ^ 3) (by omega)
            _ = 60466176 ^ 3 * (n' + 2) := by rw [h64]; ac_rfl
        calc (n' + 1 + 2) * (45349632 ^ 3 * 45349632 ^ (3 * (n' + 1)))
            = ((n' + 3) * 45349632 ^ 3) * 45349632 ^ (3 * (n' + 1)) := by
                rw [show n' + 1 + 2 = n' + 3 by omega, Nat.mul_assoc]
          _ ≤ (60466176 ^ 3 * (n' + 2)) * 45349632 ^ (3 * (n' + 1)) :=
                Nat.mul_le_mul_right _ hstep_c
          _ = 60466176 ^ 3 * ((n' + 2) * 45349632 ^ (3 * (n' + 1))) := Nat.mul_assoc _ _ _
          _ < 60466176 ^ 3 * 60466176 ^ (3 * (n' + 1)) :=
                Nat.mul_lt_mul_of_pos_left ih (by decide)
    intro B u hu_ge
    have hbase := h3n B
    let r := u - 3 * (B + 1)
    have hu_eq : u = 3 * (B + 1) + r := by omega
    rw [hu_eq, Nat.pow_add 45349632, Nat.pow_add 60466176]
    have hr_le : 45349632 ^ r ≤ 60466176 ^ r := pow_mono_base_w15c _ _ (by decide) r
    have hr_pos : 0 < 45349632 ^ r := nat_pow_pos_of_pos _ (by decide) r
    have hB_le : B ≤ B + 2 := by omega
    calc B * (45349632 ^ (3 * (B + 1)) * 45349632 ^ r)
        ≤ (B + 2) * (45349632 ^ (3 * (B + 1)) * 45349632 ^ r) := Nat.mul_le_mul_right _ hB_le
      _ = ((B + 2) * 45349632 ^ (3 * (B + 1))) * 45349632 ^ r := (Nat.mul_assoc _ _ _).symm
      _ < 60466176 ^ (3 * (B + 1)) * 45349632 ^ r := Nat.mul_lt_mul_of_pos_right hbase hr_pos
      _ ≤ 60466176 ^ (3 * (B + 1)) * 60466176 ^ r := Nat.mul_le_mul_left _ hr_le
  have hall_b45 : ∀ m ∈ t3u3CorePoly, ¬ (m.2.2.1 == 10 && m.2.2.2.1 == 10) ->
      2 ^ m.2.2.1 * 3 ^ m.2.2.2.1 ≤ 45349632 := by
    intro m hm hnot10
    have hb := List.all_eq_true.mp hall_m m hm
    rcases bool_and_split hb with ⟨_, hlast⟩
    have h10f : (m.2.2.1 == 10 && m.2.2.2.1 == 10) = false := by
      cases h : (m.2.2.1 == 10 && m.2.2.2.1 == 10); { rfl }; exact False.elim (hnot10 h)
    rw [h10f] at hlast; exact of_decide_eq_true hlast
  have hsign_w_lt_k : W < K -> ∀ u : Nat, u ≥ t3u3SignLockHorizon W K ->
      intDet 9 (laurentTwoBaseT3U3Mat9 W K u) > 0 := by
    intro hlt u hu_hor
    have hu1 : u ≥ 1 := by omega
    have hdom := hpow_dom (t3u3RemAbsBound W K) u (by unfold t3u3SignLockHorizon at hu_hor; omega)
    have hr_bd := hrem_bd u t3u3CorePoly hall_b45
    change (evalPoly4 (W : Int) (K : Int) ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int) t3u3CorePoly -
      leadSum u t3u3CorePoly).natAbs ≤ t3u3RemAbsBound W K * 45349632 ^ u at hr_bd
    rw [hlead_closed u] at hr_bd
    have hlead_ge1 : ((W ^ 2 * K ^ 2 : Nat) : Int) * intPowNat ((K : Int) - (W : Int)) 5 ≥ 1 := by
      have hkw : (K : Int) - (W : Int) = ((K - W : Nat) : Int) := by omega
      rw [hkw, hintPow_ev, ← Int.natCast_mul]
      have hp1 : W ^ 2 * K ^ 2 * (K - W) ^ 5 ≥ 1 :=
        Nat.mul_le_mul (Nat.mul_le_mul (nat_pow_pos_of_pos W hW 2) (nat_pow_pos_of_pos K hK 2))
          (nat_pow_pos_of_pos (K - W) (by omega) 5)
      omega
    have hlead_ge_60 : ((W ^ 2 * K ^ 2 : Nat) : Int) * intPowNat ((K : Int) - (W : Int)) 5 *
        ((60466176 ^ u : Nat) : Int) ≥ ((60466176 ^ u : Nat) : Int) := by
      have hm := Int.mul_le_mul_of_nonneg_right hlead_ge1 (Int.natCast_nonneg (60466176 ^ u))
      rwa [Int.one_mul] at hm
    have hcore_pos : evalPoly4 (W : Int) (K : Int) ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int) t3u3CorePoly > 0 := by
      omega
    have h4det := hclosed_u W K u hW hu1
    have h6_pos : ((2 ^ (3 * u) * 3 ^ (3 * u) : Nat) : Int) > 0 := by
      have := Nat.mul_le_mul (nat_pow_pos_of_pos 2 (by decide) (3 * u)) (pow3_pos_nat (3 * u)); omega
    have := Int.mul_pos h6_pos hcore_pos
    omega
  have hsign_k_lt_w : K < W -> ∀ u : Nat, u ≥ t3u3SignLockHorizon W K ->
      intDet 9 (laurentTwoBaseT3U3Mat9 W K u) < 0 := by
    intro hlt u hu_hor
    have hu1 : u ≥ 1 := by omega
    have hdom := hpow_dom (t3u3RemAbsBound W K) u (by unfold t3u3SignLockHorizon at hu_hor; omega)
    have hr_bd := hrem_bd u t3u3CorePoly hall_b45
    change (evalPoly4 (W : Int) (K : Int) ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int) t3u3CorePoly -
      leadSum u t3u3CorePoly).natAbs ≤ t3u3RemAbsBound W K * 45349632 ^ u at hr_bd
    rw [hlead_closed u] at hr_bd
    have hlead_le1 : ((W ^ 2 * K ^ 2 : Nat) : Int) * intPowNat ((K : Int) - (W : Int)) 5 ≤ -1 := by
      have hkw : (K : Int) - (W : Int) = -(((W - K : Nat) : Int)) := by omega
      have hneg5 : ∀ x : Int, intPowNat (-x) 5 = -intPowNat x 5 := by
        intro x; simp only [intPowNat, Int.mul_one, Int.neg_mul, Int.mul_neg, Int.neg_neg]
      rw [hkw, hneg5, hintPow_ev, Int.mul_neg, ← Int.natCast_mul]
      have hp1 : W ^ 2 * K ^ 2 * (W - K) ^ 5 ≥ 1 :=
        Nat.mul_le_mul (Nat.mul_le_mul (nat_pow_pos_of_pos W hW 2) (nat_pow_pos_of_pos K hK 2))
          (nat_pow_pos_of_pos (W - K) (by omega) 5)
      omega
    have hlead_le_60 : ((W ^ 2 * K ^ 2 : Nat) : Int) * intPowNat ((K : Int) - (W : Int)) 5 *
        ((60466176 ^ u : Nat) : Int) ≤ -((60466176 ^ u : Nat) : Int) := by
      have hm := Int.mul_le_mul_of_nonneg_right hlead_le1 (Int.natCast_nonneg (60466176 ^ u))
      rwa [Int.neg_one_mul] at hm
    have hcore_neg : evalPoly4 (W : Int) (K : Int) ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int) t3u3CorePoly < 0 := by
      omega
    have h4det := hclosed_u W K u hW hu1
    have h6_pos : ((2 ^ (3 * u) * 3 ^ (3 * u) : Nat) : Int) > 0 := by
      have := Nat.mul_le_mul (nat_pow_pos_of_pos 2 (by decide) (3 * u)) (pow3_pos_nat (3 * u)); omega
    have := Int.mul_neg_of_pos_of_neg h6_pos hcore_neg
    omega
  refine ⟨hhor_ge1, ?_, hsign_w_lt_k, hsign_k_lt_w⟩
  intro u hu_hor
  rcases (by omega : W < K ∨ K < W ∨ W = K) with hlt | hgt | heq
  · have := hsign_w_lt_k hlt u hu_hor; omega
  · have := hsign_k_lt_w hgt u hu_hor; omega
  · subst heq
    apply t3u3_conefree_all_u_nonzero_w15 W W u hW hW (by omega)
    left; rw [Nat.gcd_self, Nat.div_self hW]; decide

private theorem t3u3_7_11_double_flip_w15 :
    3 * 11 ≤ 5 * 7 ∧ 2 ^ 11 < 3 ^ 7 ∧
      intDet 9 (laurentTwoBaseT3U3Mat9 7 11 3) > 0 ∧
      intDet 9 (laurentTwoBaseT3U3Mat9 7 11 4) < 0 ∧
      intDet 9 (laurentTwoBaseT3U3Mat9 7 11 5) > 0 := by
  have hclosed_u := laurent_9x9_t3u3_all_u_cone_positivity_and_multiu_nonvanishing.1
  rcases t3u3_val_and_7_11_certs with ⟨_, hs3, hs4, hs5⟩
  have hc3 := hclosed_u 7 11 3 (by decide) (by decide)
  have hc4 := hclosed_u 7 11 4 (by decide) (by decide)
  have hc5 := hclosed_u 7 11 5 (by decide) (by decide)
  rw [evalPoly4_eq_slice_sum10_w15 7 11 3] at hc3
  rw [evalPoly4_eq_slice_sum10_w15 7 11 4] at hc4
  rw [evalPoly4_eq_slice_sum10_w15 7 11 5] at hc5
  change 4 * intDet 9 (laurentTwoBaseT3U3Mat9 7 11 3) =
      ((2 ^ (3 * 3) * 3 ^ (3 * 3) : Nat) : Int) * evalSliceSum10Fast 7 11 3 at hc3
  change 4 * intDet 9 (laurentTwoBaseT3U3Mat9 7 11 4) =
      ((2 ^ (3 * 4) * 3 ^ (3 * 4) : Nat) : Int) * evalSliceSum10Fast 7 11 4 at hc4
  change 4 * intDet 9 (laurentTwoBaseT3U3Mat9 7 11 5) =
      ((2 ^ (3 * 5) * 3 ^ (3 * 5) : Nat) : Int) * evalSliceSum10Fast 7 11 5 at hc5
  have hp3 : ((2 ^ (3 * 3) * 3 ^ (3 * 3) : Nat) : Int) > 0 := by decide
  have hp4 : ((2 ^ (3 * 4) * 3 ^ (3 * 4) : Nat) : Int) > 0 := by decide
  have hp5 : ((2 ^ (3 * 5) * 3 ^ (3 * 5) : Nat) : Int) > 0 := by decide
  have m3 := Int.mul_pos hp3 hs3
  have m4 := Int.mul_neg_of_pos_of_neg hp4 hs4
  have m5 := Int.mul_pos hp5 hs5
  exact ⟨by decide, by decide, by omega, by omega, by omega⟩

/--
  Theorem W15.2b (`laurent_9x9_t3u3_conefree_nonvanishing_and_multiu_ceiling`,
  `zero custom axioms`):
  Rank-3 `9 × 9` `(T = 3, U = 3)` Global `u ∈ {1..9}` Non-Vanishing, Symbolic `u ≥ 10`
  `(2, 3)`-Adic Newton-Polygon Divisibility Lock (`3 ^ ((2 * u + 8) / 9) ∣ (W / gcd(W, K)) ∧
  2 ^ ((u + 2) / 4) ∣ (K / gcd(W, K))`), Universal Cone-Free `∀ u ≥ 1` Non-Vanishing Outside
  `(27 * w', 8 * k')` AND Along the Minimal Resonant Ray `(27 * c, 8 * c)`, Explicit Finite
  Multi-`u` Zero-Multiplicity Ceiling & Asymptotic Sign Lock Across ALL `W, K ≥ 1`, & `(7, 11)`
  Double Sign-Flip (`u = 3, 4, 5`, `Branch P3.3`, witness `LAURENT_9X9_7_11_U4_DOUBLE_SIGN_FLIP`,
  `W15_H2`).
-/
theorem laurent_9x9_t3u3_conefree_nonvanishing_and_multiu_ceiling :
    (∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 -> 1 ≤ u -> u ≤ 9 ->
      intDet 9 (laurentTwoBaseT3U3Mat9 W K u) ≠ 0) ∧
    (∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 -> u ≥ 10 ->
      intDet 9 (laurentTwoBaseT3U3Mat9 W K u) = 0 ->
      3 ^ ((2 * u + 8) / 9) ∣ (W / Nat.gcd W K) ∧
      2 ^ ((u + 2) / 4) ∣ (K / Nat.gcd W K)) ∧
    (∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 -> u ≥ 1 ->
      ((W / Nat.gcd W K) % 27 ≠ 0 ∨ (K / Nat.gcd W K) % 8 ≠ 0) ->
      intDet 9 (laurentTwoBaseT3U3Mat9 W K u) ≠ 0) ∧
    (∀ (c u : Nat), c ≥ 1 -> u ≥ 1 ->
      intDet 9 (laurentTwoBaseT3U3Mat9 (27 * c) (8 * c) u) ≠ 0) ∧
    (∀ W K : Nat, W ≥ 1 -> K ≥ 1 ->
      t3u3SignLockHorizon W K ≥ 1 ∧
      (∀ u : Nat, u ≥ t3u3SignLockHorizon W K ->
        intDet 9 (laurentTwoBaseT3U3Mat9 W K u) ≠ 0) ∧
      (W < K -> ∀ u : Nat, u ≥ t3u3SignLockHorizon W K ->
        intDet 9 (laurentTwoBaseT3U3Mat9 W K u) > 0) ∧
      (K < W -> ∀ u : Nat, u ≥ t3u3SignLockHorizon W K ->
        intDet 9 (laurentTwoBaseT3U3Mat9 W K u) < 0)) ∧
    (3 * 11 ≤ 5 * 7 ∧ 2 ^ 11 < 3 ^ 7 ∧
      intDet 9 (laurentTwoBaseT3U3Mat9 7 11 3) > 0 ∧
      intDet 9 (laurentTwoBaseT3U3Mat9 7 11 4) < 0 ∧
      intDet 9 (laurentTwoBaseT3U3Mat9 7 11 5) > 0) :=
  ⟨t3u3_global_1_to_9_nonzero_w15,
   t3u3_u10_newton_divisibility_w15,
   t3u3_conefree_all_u_nonzero_w15,
   t3u3_resonant_27_8_ray_all_u_nonzero_w15,
   t3u3_signlock_horizon_w15,
   t3u3_7_11_double_flip_w15⟩

-- ----------------------------------------------------------------------------
-- Section 2C: General `∀ s ≥ 4` Newton–Hensel Mod-`2^s` 2-Adic
--             Inverse-Residue Quotient Boost, `<3> mod 2^s` Subgroup Saturation,
--             & 3-Pivot Cross-Block Brox Elimination (`W15_H2`, Branch P3.4)
-- ----------------------------------------------------------------------------

/-- Constructive 1-bit Hensel odd modular inverse of `d` modulo `2 ^ s` (`1` at `s = 1`,
    lifting `x -> x` or `x + 2 ^ k` from `mod 2 ^ k` to `mod 2 ^ (k + 1)`). -/
def henselOddInvModPow2 : Nat -> Nat -> Nat
  | 0, _ => 0
  | 1, _ => 1
  | k + 2, d =>
    let x := henselOddInvModPow2 (k + 1) d
    if (d * x) % 2 ^ (k + 2) == 1 then x else x + 2 ^ (k + 1)

private theorem henselOddInvModPow2_spec :
    ∀ (s d : Nat), s ≥ 1 -> d % 2 = 1 ->
      1 ≤ henselOddInvModPow2 s d ∧
      henselOddInvModPow2 s d < 2 ^ s ∧
      henselOddInvModPow2 s d % 2 = 1 ∧
      (d * henselOddInvModPow2 s d) % 2 ^ s = 1 := by
  intro s
  induction s with
  | zero => intro _ hs; omega
  | succ s' ih =>
    cases s' with
    | zero =>
      intro d _ hd_odd
      simp only [henselOddInvModPow2]
      exact ⟨by decide, by decide, by decide, by omega⟩
    | succ k =>
      intro d _ hd_odd
      rcases ih d (by omega) hd_odd with ⟨hx1, hx_lt, hx_odd, hx_mod⟩
      simp only [henselOddInvModPow2]
      have hp_pos : 2 ^ (k + 1) ≥ 2 := by simpa using pow2_mono_nat (by omega : 1 ≤ k + 1)
      have hp2_eq : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      by_cases hc : ((d * henselOddInvModPow2 (k + 1) d) % 2 ^ (k + 2) == 1) = true
      · simp only [hc, ite_true]
        exact ⟨hx1, by omega, hx_odd, beq_iff_eq.mp hc⟩
      · simp only [hc, Bool.false_eq_true, ite_false]
        have hne1 : (d * henselOddInvModPow2 (k + 1) d) % 2 ^ (k + 2) ≠ 1 :=
          beq_eq_false_iff_ne.mp (Bool.eq_false_iff.mpr hc)
        let x := henselOddInvModPow2 (k + 1) d
        change 1 ≤ x + 2 ^ (k + 1) ∧ x + 2 ^ (k + 1) < 2 ^ (k + 2) ∧
          (x + 2 ^ (k + 1)) % 2 = 1 ∧ (d * (x + 2 ^ (k + 1))) % 2 ^ (k + 2) = 1
        have hp_ev : 2 ^ (k + 1) % 2 = 0 := by
          rw [Nat.pow_succ]; omega
        let q := (d * x) / 2 ^ (k + 1)
        have hdx : d * x = 2 ^ (k + 1) * q + 1 := by
          have := Nat.div_add_mod (d * x) (2 ^ (k + 1))
          dsimp [x] at *; rw [hx_mod] at this; exact this.symm
        have hq_odd : q % 2 = 1 := by
          by_cases hqe : q % 2 = 0
          · exfalso
            let q_half := q / 2
            have hq2 : q = 2 * q_half := by omega
            have hm_eq : d * x = 2 ^ (k + 2) * q_half + 1 := by
              rw [hdx, hq2, hp2_eq]; ac_rfl
            have hmod1 : (d * x) % 2 ^ (k + 2) = 1 := by
              rw [hm_eq, Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_right]
              exact Nat.mod_eq_of_lt (by omega)
            exact hne1 hmod1
          · omega
        let q' := q / 2
        have hq_sp : q = 2 * q' + 1 := by omega
        let d' := d / 2
        have hd_sp : d = 2 * d' + 1 := by omega
        have hprod_new : d * (x + 2 ^ (k + 1)) = 2 ^ (k + 2) * (q' + d' + 1) + 1 := by
          rw [Nat.mul_add, hdx, hq_sp, hd_sp, hp2_eq]
          simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
          have ec : (2 * d') * 2 ^ (k + 1) = (2 * 2 ^ (k + 1)) * d' := by ac_rfl
          have eq1 : 2 ^ (k + 1) * (2 * q') = (2 * 2 ^ (k + 1)) * q' := by ac_rfl
          rw [ec, eq1]
          generalize (2 * 2 ^ (k + 1)) * q' = A, (2 * 2 ^ (k + 1)) * d' = B, 2 ^ (k + 1) = P
          omega
        refine ⟨by omega, by omega, by omega, ?_⟩
        rw [hprod_new, Nat.mul_comm (2 ^ (k + 2)), Nat.add_comm, Nat.add_mul_mod_self_right]
        exact Nat.mod_eq_of_lt (by omega)

private theorem hensel_quotient_boost_w15
    (s w0 a0 w1 q0 q1 d_mult : Nat)
    (hs4 : s ≥ 4) (ha_ge : a0 ≥ s) (hd_odd : d_mult % 2 = 1) (hdvd : d_mult ∣ q0)
    (hrec : 2 ^ (a0 + w1) * q1 = 3 ^ w0 * q0 + (2 ^ a0 - 1)) :
    (3 ^ w0 * q0) % 2 ^ s = 1 ∧
    q0 ≥ henselOddInvModPow2 s (3 ^ w0 * d_mult) * d_mult := by
  rcases hdvd with ⟨k_q, hkq⟩
  have h2s_pos : 2 ^ s ≥ 16 := by simpa using pow2_mono_nat hs4
  have hlhs_m : (2 ^ (a0 + w1) * q1) % 2 ^ s = 0 := by
    have hp : 2 ^ (a0 + w1) = 2 ^ s * 2 ^ (a0 + w1 - s) := by
      conv => lhs; rw [show a0 + w1 = s + (a0 + w1 - s) by omega, Nat.pow_add]
    rw [hp, Nat.mul_assoc, Nat.mul_mod_right]
  have h2a_div : 2 ^ s ∣ 2 ^ a0 := by
    rw [show a0 = s + (a0 - s) by omega, Nat.pow_add]
    exact ⟨2 ^ (a0 - s), rfl⟩
  have hmod1 : (3 ^ w0 * q0) % 2 ^ s = 1 := by
    rcases h2a_div with ⟨qa, hqa⟩
    have hadd1 : 3 ^ w0 * q0 + 2 ^ a0 = 2 ^ (a0 + w1) * q1 + 1 := by
      have := nat_pow_pos_of_pos 2 (by decide) a0; omega
    have hmod_add := congrArg (· % 2 ^ s) hadd1
    rw [hqa, Nat.add_mul_mod_self_left, Nat.add_mod, hlhs_m, Nat.zero_add, Nat.mod_mod,
        Nat.mod_eq_of_lt (by omega : 1 < 2 ^ s)] at hmod_add
    exact hmod_add
  have h3w_odd : (3 ^ w0 * d_mult) % 2 = 1 := by
    have h3o : ∀ n : Nat, 3 ^ n % 2 = 1 := by
      intro n; induction n with
      | zero => rfl
      | succ n' ihn => rw [Nat.pow_succ, Nat.mul_mod, ihn]
    rw [Nat.mul_mod, h3o w0, hd_odd]
  rcases henselOddInvModPow2_spec s (3 ^ w0 * d_mult) (by omega) h3w_odd with ⟨_, hinv_lt, _, hinv_mod⟩
  let r_inv := henselOddInvModPow2 s (3 ^ w0 * d_mult)
  have hm_mul : ∀ x y : Nat, (x * y) % 2 ^ s = (x * (y % 2 ^ s)) % 2 ^ s := by
    intro x y; rw [Nat.mul_mod x (y % 2 ^ s) (2 ^ s), Nat.mod_mod, ← Nat.mul_mod]
  have hm_mul_l : ∀ x y : Nat, (x * y) % 2 ^ s = ((x % 2 ^ s) * y) % 2 ^ s := by
    intro x y; rw [Nat.mul_mod (x % 2 ^ s) y (2 ^ s), Nat.mod_mod, ← Nat.mul_mod]
  have hkq_mod : k_q % 2 ^ s = r_inv := by
    have hm1 : ((3 ^ w0 * d_mult) * k_q) % 2 ^ s = 1 := by
      rwa [hkq, ← Nat.mul_assoc] at hmod1
    calc k_q % 2 ^ s
        = (1 * k_q) % 2 ^ s := by rw [Nat.one_mul]
      _ = (((r_inv * (3 ^ w0 * d_mult)) % 2 ^ s) * k_q) % 2 ^ s := by
            rw [Nat.mul_comm r_inv, hinv_mod]
      _ = (r_inv * ((3 ^ w0 * d_mult) * k_q)) % 2 ^ s := by
            rw [← hm_mul_l, Nat.mul_assoc]
      _ = (r_inv * (((3 ^ w0 * d_mult) * k_q) % 2 ^ s)) % 2 ^ s := hm_mul _ _
      _ = r_inv % 2 ^ s := by rw [hm1, Nat.mul_one]
      _ = r_inv := Nat.mod_eq_of_lt hinv_lt
  have hkq_ge : k_q ≥ r_inv := by
    have := Nat.mod_le k_q (2 ^ s); omega
  refine ⟨hmod1, ?_⟩
  rw [hkq, Nat.mul_comm d_mult k_q]
  exact Nat.mul_le_mul_right d_mult hkq_ge

private theorem subgroup_sat_mod_pow2_w15 (s : Nat) (hs4 : s ≥ 4) :
    ∃ w0 : Nat, w0 < 2 ^ (s - 2) ∧ (3 ^ w0 * (5 * (2 ^ s - 1))) % 2 ^ s = 1 := by
  have hpow3_lift : ∀ t : Nat, t ≥ 1 ->
      ∃ q : Nat, 3 ^ (2 ^ t) = q * 2 ^ (t + 3) + 2 ^ (t + 2) + 1 := by
    intro t ht; induction t with
    | zero => omega
    | succ t' iht =>
      by_cases ht0 : t' = 0
      · subst ht0; exact ⟨0, by decide⟩
      · rcases iht (by omega) with ⟨q, hq⟩
        have hp_sq : 3 ^ (2 ^ (t' + 1)) = (3 ^ (2 ^ t')) * (3 ^ (2 ^ t')) := by
          rw [Nat.pow_succ 2 t', Nat.mul_two, Nat.pow_add]
        rw [hp_sq, hq]
        let P3 := 2 ^ (t' + 3)
        let P2 := 2 ^ (t' + 2)
        have hP3 : P3 = 2 * P2 := by dsimp [P3, P2]; rw [Nat.pow_succ, Nat.mul_comm]
        have hP4 : 2 ^ (t' + 4) = 2 * P3 := by dsimp [P3]; rw [Nat.pow_succ, Nat.mul_comm]
        have hP2_sq : P2 * P2 = 2 ^ t' * 2 ^ (t' + 4) := by
          dsimp [P2]; rw [← Nat.pow_add, ← Nat.pow_add]
          exact congrArg (2 ^ ·) (by omega)
        refine ⟨q * q * 2 ^ (t' + 2) + q * 2 ^ (t' + 2) + q + 2 ^ t', ?_⟩
        calc (q * P3 + P2 + 1) * (q * P3 + P2 + 1)
            = (q * q) * (P3 * P3) + 2 * (q * (P3 * P2)) + 2 * (q * P3) + P2 * P2 + 2 * P2 + 1 := by
                simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
                have u1 : (q * P3) * (q * P3) = (q * q) * (P3 * P3) := by ac_rfl
                have u2 : (q * P3) * P2 = q * (P3 * P2) := by ac_rfl
                have u3 : P2 * (q * P3) = q * (P3 * P2) := by ac_rfl
                rw [u1, u2, u3]
                generalize (q * q) * (P3 * P3) = A, q * (P3 * P2) = B, q * P3 = C, P2 * P2 = D
                omega
          _ = (q * q * P2 + q * P2 + q + 2 ^ t') * (2 * P3) + P3 + 1 := by
                have e1 : (q * q) * (P3 * P3) = (q * q * P2) * (2 * P3) := by rw [hP3]; ac_rfl
                have e2 : 2 * (q * (P3 * P2)) = (q * P2) * (2 * P3) := by ac_rfl
                have e3 : 2 * (q * P3) = q * (2 * P3) := by ac_rfl
                have e4 : P2 * P2 = 2 ^ t' * (2 * P3) := by rw [hP2_sq, hP4]
                rw [e1, e2, e3, e4, ← hP3]
                simp only [Nat.add_mul]
          _ = (q * q * 2 ^ (t' + 2) + q * 2 ^ (t' + 2) + q + 2 ^ t') * 2 ^ (t' + 4) + 2 ^ (t' + 3) + 1 := by
                rw [← hP4]
  have h5_clean : ∀ t : Nat, t ≥ 1 ->
      ∃ w0 : Nat, w0 < 2 ^ (t + 1) ∧ (5 * 3 ^ w0 + 1) % 2 ^ (t + 3) = 0 := by
    intro t ht; induction t with
    | zero => omega
    | succ t' ih =>
      by_cases ht0 : t' = 0
      · subst ht0; exact ⟨1, by decide, by decide⟩
      · rcases ih (by omega) with ⟨w0, hw_lt, hw_mod⟩
        rcases Nat.dvd_of_mod_eq_zero hw_mod with ⟨m, hm_eq⟩
        by_cases hmev : m % 2 = 0
        · refine ⟨w0, by rw [Nat.pow_succ]; omega, ?_⟩
          let m_half := m / 2
          have hm2 : m = 2 * m_half := by omega
          have heq : 5 * 3 ^ w0 + 1 = 2 ^ (t' + 4) * m_half := by
            rw [hm_eq, hm2, show 2 ^ (t' + 4) = 2 ^ (t' + 3) * 2 by rw [Nat.pow_succ]]; ac_rfl
          rw [heq, Nat.mul_mod_right]
        · refine ⟨w0 + 2 ^ (t' + 1), by rw [Nat.pow_succ 2 (t' + 1)]; omega, ?_⟩
          rcases hpow3_lift (t' + 1) (by omega) with ⟨q, hq⟩
          have h3o : 3 ^ w0 % 2 = 1 := by
            clear hm_eq hw_mod hw_lt
            induction w0 with
            | zero => rfl
            | succ n ihn => rw [Nat.pow_succ, Nat.mul_mod, ihn]
          let a_odd := (5 * 3 ^ w0) / 2
          have ha_sp : 5 * 3 ^ w0 = 2 * a_odd + 1 := by omega
          let m' := m / 2
          have hm_sp : m = 2 * m' + 1 := by omega
          have hp4 : 2 ^ (t' + 4) = 2 * 2 ^ (t' + 3) := by rw [Nat.pow_succ, Nat.mul_comm]
          have hstep_div : 5 * 3 ^ (w0 + 2 ^ (t' + 1)) + 1 =
              2 ^ (t' + 4) * ((5 * 3 ^ w0) * q + a_odd + m' + 1) := by
            calc 5 * 3 ^ (w0 + 2 ^ (t' + 1)) + 1
                = (5 * 3 ^ w0) * 3 ^ (2 ^ (t' + 1)) + 1 := by rw [Nat.pow_add, Nat.mul_assoc]
              _ = (5 * 3 ^ w0) * (q * 2 ^ (t' + 4) + 2 ^ (t' + 3) + 1) + 1 := by rw [hq]
              _ = 2 ^ (t' + 4) * ((5 * 3 ^ w0) * q) + (5 * 3 ^ w0) * 2 ^ (t' + 3) + (5 * 3 ^ w0 + 1) := by
                    simp only [Nat.mul_add, Nat.mul_one]
                    have e0 : (5 * 3 ^ w0) * (q * 2 ^ (t' + 4)) = 2 ^ (t' + 4) * ((5 * 3 ^ w0) * q) := by ac_rfl
                    rw [e0]; omega
              _ = 2 ^ (t' + 4) * ((5 * 3 ^ w0) * q) + (2 * a_odd + 1) * 2 ^ (t' + 3) + 2 ^ (t' + 3) * (2 * m' + 1) := by
                    rw [hm_eq, hm_sp]
                    conv => lhs; lhs; rhs; rw [ha_sp]
              _ = 2 ^ (t' + 4) * ((5 * 3 ^ w0) * q + a_odd + m' + 1) := by
                    rw [hp4]
                    simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one]
                    have ea : (2 * a_odd) * 2 ^ (t' + 3) = (2 * 2 ^ (t' + 3)) * a_odd := by ac_rfl
                    have em : 2 ^ (t' + 3) * (2 * m') = (2 * 2 ^ (t' + 3)) * m' := by ac_rfl
                    rw [ea, em]
                    generalize (2 * 2 ^ (t' + 3)) * ((5 * 3 ^ w0) * q) = A,
                      (2 * 2 ^ (t' + 3)) * a_odd = B,
                      (2 * 2 ^ (t' + 3)) * m' = C,
                      2 ^ (t' + 3) = P
                    omega
          rw [hstep_div, Nat.mul_mod_right]
  rcases h5_clean (s - 3) (by omega) with ⟨w0, hw_lt, hw_mod⟩
  rw [show s - 3 + 1 = s - 2 by omega] at hw_lt
  rw [show s - 3 + 3 = s by omega] at hw_mod
  refine ⟨w0, hw_lt, ?_⟩
  rcases Nat.dvd_of_mod_eq_zero hw_mod with ⟨m, hm_eq⟩
  have h2s_pos : 2 ^ s ≥ 16 := by simpa using pow2_mono_nat hs4
  have hprod : 3 ^ w0 * (5 * (2 ^ s - 1)) = 2 ^ s * (5 * 3 ^ w0 - m) + 1 := by
    have e1 : 3 ^ w0 * (5 * (2 ^ s - 1)) = 2 ^ s * (5 * 3 ^ w0) - 5 * 3 ^ w0 := by
      rw [show 3 ^ w0 * (5 * (2 ^ s - 1)) = (5 * 3 ^ w0) * (2 ^ s - 1) by ac_rfl,
          Nat.mul_sub_left_distrib, Nat.mul_one, Nat.mul_comm (5 * 3 ^ w0) (2 ^ s)]
    have hm_le : m ≤ 5 * 3 ^ w0 := by
      have h1 : 16 * m ≤ 2 ^ s * m := Nat.mul_le_mul_right m h2s_pos
      omega
    rw [e1, Nat.mul_sub_left_distrib]
    have h2 : 2 ^ s * m = 5 * 3 ^ w0 + 1 := hm_eq.symm
    have h3 : 2 ^ s * m ≤ 2 ^ s * (5 * 3 ^ w0) := Nat.mul_le_mul_left (2 ^ s) hm_le
    omega
  rw [hprod, Nat.mul_comm (2 ^ s), Nat.add_comm, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt (by omega)

private theorem three_pivot_brox_squeeze_w15
    (b0 b1 b2 : Nat × Nat) (tail : List (Nat × Nat)) (qs : List Nat) (d_mult : Nat) :
    let blocks := b0 :: b1 :: b2 :: tail
    let W := blockWeightSum blocks
    let K := blockStepSum blocks
    let D := 2 ^ K - 3 ^ W
    let Wt := blockWeightSum tail
    let Et := blockStepSum (b2 :: tail) - blockWeightSum (b2 :: tail)
    (∀ b ∈ blocks, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
    3 ^ W < 2 ^ K ->
    qs.length = blocks.length ->
    (∀ j : Nat, j < blocks.length -> D * natAt qs j = broxSpiralCarry (rotBlocks j blocks)) ->
    d_mult ∣ natListGcd qs ->
    broxSpiralCarry blocks + 3 ^ (b1.1 + b2.1 + Wt) ≤
      3 ^ (b1.1 + b2.1 + Wt) * 2 ^ b0.2 +
      2 ^ (b0.2 + b1.1) * 3 ^ (b2.1 + Wt) * (2 ^ b1.2 - 1) +
      2 ^ (b0.2 + b1.1 + b1.2 + b2.1) * 3 ^ Wt * (2 ^ Et - 1) ∧
    d_mult * D + 3 ^ (b1.1 + b2.1 + Wt) ≤
      3 ^ (b1.1 + b2.1 + Wt) * 2 ^ b0.2 +
      2 ^ (b0.2 + b1.1) * 3 ^ (b2.1 + Wt) * (2 ^ b1.2 - 1) +
      2 ^ (b0.2 + b1.1 + b1.2 + b2.1) * 3 ^ Wt * (2 ^ Et - 1) := by
  dsimp only
  intro hpos _ hlen hqs hdvd_gcd
  let blocks := b0 :: b1 :: b2 :: tail
  let W := blockWeightSum blocks
  let K := blockStepSum blocks
  let D := 2 ^ K - 3 ^ W
  let Wt := blockWeightSum tail
  let Et := blockStepSum (b2 :: tail) - blockWeightSum (b2 :: tail)
  have hpos_b2 : ∀ b ∈ (b2 :: tail), b.1 ≥ 1 ∧ b.2 ≥ 1 :=
    fun b hb => hpos b (List.mem_cons_of_mem b0 (List.mem_cons_of_mem b1 hb))
  have hstep_ge_wt : ∀ xs : List (Nat × Nat), blockStepSum xs ≥ blockWeightSum xs := by
    intro xs; induction xs with
    | nil => exact Nat.le_refl 0
    | cons x xtl ih => simp only [blockStepSum, blockWeightSum]; omega
  have hcarry_ne : ∀ (xtl : List (Nat × Nat)) (x : Nat × Nat),
      (∀ b ∈ x :: xtl, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      broxSpiralCarry (x :: xtl) + 3 ^ blockWeightSum xtl ≤
        3 ^ blockWeightSum xtl * 2 ^ (blockStepSum (x :: xtl) - blockWeightSum (x :: xtl)) := by
    intro xtl; induction xtl with
    | nil =>
      intro x hx
      have hx2 := (hx x List.mem_cons_self).2
      have hp2 := nat_pow_pos_of_pos 2 (by decide) x.2
      simp only [broxSpiralCarry, blockWeightSum, blockStepSum, Nat.add_zero, Nat.pow_zero, Nat.one_mul]
      rw [show x.1 + x.2 - x.1 = x.2 by omega]; omega
    | cons y ytl ih =>
      intro x hx
      have ih_y := ih y (fun b hb => hx b (List.mem_cons_of_mem x hb))
      let W_ytl := blockWeightSum ytl
      let E_y := blockStepSum (y :: ytl) - blockWeightSum (y :: ytl)
      have hge_ytl := hstep_ge_wt ytl
      have hexp_eq : blockStepSum (x :: y :: ytl) - blockWeightSum (x :: y :: ytl) = x.2 + E_y := by
        dsimp [E_y]; simp only [blockStepSum, blockWeightSum]; omega
      rw [hexp_eq]
      simp only [broxSpiralCarry, blockWeightSum]
      change (3 ^ (y.1 + W_ytl) * (2 ^ x.2 - 1) + 2 ^ (x.2 + y.1) * broxSpiralCarry (y :: ytl)) +
        3 ^ (y.1 + W_ytl) ≤ 3 ^ (y.1 + W_ytl) * 2 ^ (x.2 + E_y)
      have hm1 := Nat.mul_le_mul_left (2 ^ (x.2 + y.1)) ih_y
      rw [Nat.mul_add] at hm1
      change 2 ^ (x.2 + y.1) * broxSpiralCarry (y :: ytl) + 2 ^ (x.2 + y.1) * 3 ^ W_ytl ≤
        2 ^ (x.2 + y.1) * (3 ^ W_ytl * 2 ^ E_y) at hm1
      have h2_le_3 : 2 ^ y.1 ≤ 3 ^ y.1 := pow_mono_base_w15c 2 3 (by decide) y.1
      have hp2_x : 2 ^ x.2 ≥ 1 := nat_pow_pos_of_pos 2 (by decide) x.2
      have hsub_x : 3 ^ (y.1 + W_ytl) * (2 ^ x.2 - 1) + 3 ^ (y.1 + W_ytl) =
          3 ^ (y.1 + W_ytl) * 2 ^ x.2 := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
        have := Nat.mul_le_mul_left (3 ^ (y.1 + W_ytl)) hp2_x; omega
      have hcomb_top :
          3 ^ (y.1 + W_ytl) * 2 ^ x.2 + 2 ^ (x.2 + y.1) * (3 ^ W_ytl * 2 ^ E_y) ≤
            2 ^ (x.2 + y.1) * 3 ^ W_ytl + 3 ^ (y.1 + W_ytl) * 2 ^ (x.2 + E_y) := by
        have he_pos : 2 ^ E_y ≥ 1 := nat_pow_pos_of_pos 2 (by decide) E_y
        have hdiff_y : (3 ^ y.1 - 2 ^ y.1) * (3 ^ W_ytl * 2 ^ x.2) ≤
            (3 ^ y.1 - 2 ^ y.1) * (3 ^ W_ytl * (2 ^ x.2 * 2 ^ E_y)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by simpa using Nat.mul_le_mul_left (2 ^ x.2) he_pos))
        rw [Nat.sub_mul, Nat.sub_mul] at hdiff_y
        rw [Nat.pow_add 3 y.1 W_ytl, Nat.pow_add 2 x.2 y.1, Nat.pow_add 2 x.2 E_y]
        have hle_a : 2 ^ y.1 * (3 ^ W_ytl * 2 ^ x.2) ≤ 3 ^ y.1 * (3 ^ W_ytl * 2 ^ x.2) :=
          Nat.mul_le_mul_right _ h2_le_3
        have hle_b : 2 ^ y.1 * (3 ^ W_ytl * (2 ^ x.2 * 2 ^ E_y)) ≤ 3 ^ y.1 * (3 ^ W_ytl * (2 ^ x.2 * 2 ^ E_y)) :=
          Nat.mul_le_mul_right _ h2_le_3
        have eA1 : (3 ^ y.1 * 3 ^ W_ytl) * 2 ^ x.2 = 3 ^ y.1 * (3 ^ W_ytl * 2 ^ x.2) := by ac_rfl
        have eA2 : (2 ^ x.2 * 2 ^ y.1) * (3 ^ W_ytl * 2 ^ E_y) = 2 ^ y.1 * (3 ^ W_ytl * (2 ^ x.2 * 2 ^ E_y)) := by ac_rfl
        have eA3 : (2 ^ x.2 * 2 ^ y.1) * 3 ^ W_ytl = 2 ^ y.1 * (3 ^ W_ytl * 2 ^ x.2) := by ac_rfl
        have eA4 : (3 ^ y.1 * 3 ^ W_ytl) * (2 ^ x.2 * 2 ^ E_y) = 3 ^ y.1 * (3 ^ W_ytl * (2 ^ x.2 * 2 ^ E_y)) := by ac_rfl
        rw [eA1, eA2, eA3, eA4]
        omega
      omega
  have hb2_bd := hcarry_ne tail b2 hpos_b2
  change broxSpiralCarry (b2 :: tail) + 3 ^ Wt ≤ 3 ^ Wt * 2 ^ Et at hb2_bd
  have hexp_3p : broxSpiralCarry blocks =
      3 ^ (b1.1 + b2.1 + Wt) * (2 ^ b0.2 - 1) +
      2 ^ (b0.2 + b1.1) * (3 ^ (b2.1 + Wt) * (2 ^ b1.2 - 1) +
        2 ^ (b1.2 + b2.1) * broxSpiralCarry (b2 :: tail)) := by
    dsimp [blocks, Wt]; simp only [broxSpiralCarry, blockWeightSum]
    rw [show b1.1 + (b2.1 + blockWeightSum tail) = b1.1 + b2.1 + blockWeightSum tail by omega]
  have hcarry_3p : broxSpiralCarry blocks + 3 ^ (b1.1 + b2.1 + Wt) ≤
      3 ^ (b1.1 + b2.1 + Wt) * 2 ^ b0.2 +
      2 ^ (b0.2 + b1.1) * 3 ^ (b2.1 + Wt) * (2 ^ b1.2 - 1) +
      2 ^ (b0.2 + b1.1 + b1.2 + b2.1) * 3 ^ Wt * (2 ^ Et - 1) := by
    have hp_b0 : 2 ^ b0.2 ≥ 1 := nat_pow_pos_of_pos 2 (by decide) b0.2
    have hs0 : 3 ^ (b1.1 + b2.1 + Wt) * (2 ^ b0.2 - 1) + 3 ^ (b1.1 + b2.1 + Wt) =
        3 ^ (b1.1 + b2.1 + Wt) * 2 ^ b0.2 := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      have := Nat.mul_le_mul_left (3 ^ (b1.1 + b2.1 + Wt)) hp_b0; omega
    have hb2_le : broxSpiralCarry (b2 :: tail) ≤ 3 ^ Wt * (2 ^ Et - 1) := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      omega
    have hm_b2 : 2 ^ (b0.2 + b1.1 + b1.2 + b2.1) * broxSpiralCarry (b2 :: tail) ≤
        2 ^ (b0.2 + b1.1 + b1.2 + b2.1) * 3 ^ Wt * (2 ^ Et - 1) := by
      rw [Nat.mul_assoc (2 ^ (b0.2 + b1.1 + b1.2 + b2.1)) (3 ^ Wt)]
      exact Nat.mul_le_mul_left _ hb2_le
    rw [hexp_3p, Nat.mul_add (2 ^ (b0.2 + b1.1)),
        ← Nat.mul_assoc (2 ^ (b0.2 + b1.1)) (3 ^ (b2.1 + Wt)),
        ← Nat.mul_assoc (2 ^ (b0.2 + b1.1)) (2 ^ (b1.2 + b2.1)),
        ← Nat.pow_add 2 (b0.2 + b1.1) (b1.2 + b2.1),
        show b0.2 + b1.1 + (b1.2 + b2.1) = b0.2 + b1.1 + b1.2 + b2.1 by omega]
    omega
  refine ⟨hcarry_3p, ?_⟩
  have hq0_eq := hqs 0 (by dsimp [blocks]; simp)
  simp only [rotBlocks, List.drop, List.take, List.append_nil] at hq0_eq
  change D * natAt qs 0 = broxSpiralCarry blocks at hq0_eq
  have hd_q0 : d_mult ∣ natAt qs 0 := by
    cases qs with
    | nil => dsimp [blocks] at hlen; simp at hlen
    | cons q0 qtl =>
      dsimp [natAt]
      cases qtl with
      | nil => dsimp [blocks] at hlen; simp at hlen
      | cons q1 qt2 =>
        unfold natListGcd at hdvd_gcd
        exact Nat.dvd_trans hdvd_gcd (Nat.gcd_dvd_left q0 _)
  rcases hd_q0 with ⟨k_q, hkq⟩
  have hcarry_pos : broxSpiralCarry blocks ≥ 1 := by
    rw [hexp_3p]
    have hb0_2 := (hpos b0 List.mem_cons_self).2
    have hp2 : 2 ^ b0.2 ≥ 2 := by simpa using pow2_mono_nat hb0_2
    have hp3 := pow3_pos_nat (b1.1 + b2.1 + Wt)
    have hm := Nat.mul_le_mul hp3 (by omega : 2 ^ b0.2 - 1 ≥ 1)
    omega
  have hkq_pos : k_q ≥ 1 := Nat.pos_of_ne_zero (fun hz => by
    have h0 : broxSpiralCarry blocks = 0 := by rw [← hq0_eq, hkq, hz, Nat.mul_zero, Nat.mul_zero]
    omega)
  have hdm_le : d_mult * D ≤ broxSpiralCarry blocks := by
    rw [← hq0_eq, hkq]
    calc d_mult * D = D * (d_mult * 1) := by ac_rfl
      _ ≤ D * (d_mult * k_q) := Nat.mul_le_mul_left D (Nat.mul_le_mul_left d_mult hkq_pos)
  exact Nat.le_trans (Nat.add_le_add_right hdm_le _) hcarry_3p

private theorem elim_of_dvd_and_lt_mul_w15 (D C d q : Nat)
    (hC : C ≥ 1) (hd : d ∣ q) (heq : D * q = C) (hlt : C < d * D) : False := by
  rcases hd with ⟨k, rfl⟩
  have hk : k ≥ 1 := Nat.pos_of_ne_zero (fun hz => by
    rw [hz, Nat.mul_zero] at heq; omega)
  have hle : d * D ≤ C := by
    rw [← heq]
    calc d * D = D * (d * 1) := by ac_rfl
      _ ≤ D * (d * k) := Nat.mul_le_mul_left D (Nat.mul_le_mul_left d hk)
  omega

private theorem elim_of_ge_and_lt_mul_w15 (D C b q : Nat)
    (hge : q ≥ b) (heq : D * q = C) (hlt : C < b * D) : False := by
  have hm := Nat.mul_le_mul_left D hge
  rw [heq, Nat.mul_comm D b] at hm
  omega

private theorem gcd_head_of_len4_w15 (d : Nat) (qs : List Nat)
    (hlen : qs.length = 4) (hd : d ∣ natListGcd qs) : d ∣ natAt qs 0 := by
  cases qs with
  | nil => cases hlen
  | cons q0 qtl =>
    cases qtl with
    | nil => cases hlen
    | cons _ _ => exact Nat.dvd_trans hd (Nat.gcd_dvd_left q0 _)

set_option exponentiation.threshold 2048 in
private theorem bal4_three_pivot_elim_w15 :
    let blocks_bal4 : List (Nat × Nat) := [(17, 2), (17, 2), (17, 2), (17, 34)]
    let D_bal4 := 2 ^ blockStepSum blocks_bal4 - 3 ^ blockWeightSum blocks_bal4
    (∀ j : Nat, j < 4 ->
      let r := rotBlocks j blocks_bal4
      let b0 := blockAt r 0
      let b1 := blockAt r 1
      let b2 := blockAt r 2
      let b3 := blockAt r 3
      3 * D_bal4 <
        3 ^ (b1.1 + b2.1 + b3.1) * (2 ^ b0.2 - 1) +
        2 ^ (b0.2 + b1.1) * 3 ^ (b2.1 + b3.1) * (2 ^ (b1.2 + b2.2 + b3.2) - 1)) ∧
    56063 * broxSpiralCarry blocks_bal4 < 3 * D_bal4 ∧
    ¬ (∃ qs : List Nat,
      qs.length = 4 ∧
      ∀ j : Nat, j < 4 -> D_bal4 * natAt qs j = broxSpiralCarry (rotBlocks j blocks_bal4)) := by
  dsimp only
  refine ⟨?_, by decide, ?_⟩
  · intro j hj4
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> decide
  · rintro ⟨qs, hlen, hqs⟩
    have h3_dvd : 3 ∣ natListGcd qs :=
      (m_block_companion_prime_quotient_cascades.1
        (17, 2) [(17, 2), (17, 2), (17, 34)] qs (by decide) (by decide) hlen hqs).2.1 (by decide)
    exact elim_of_dvd_and_lt_mul_w15
      (2 ^ blockStepSum [(17, 2), (17, 2), (17, 2), (17, 34)] - 3 ^ blockWeightSum [(17, 2), (17, 2), (17, 2), (17, 34)])
      (broxSpiralCarry (rotBlocks 0 [(17, 2), (17, 2), (17, 2), (17, 34)]))
      3 (natAt qs 0) (by decide) (gcd_head_of_len4_w15 3 qs hlen h3_dvd) (hqs 0 (by decide)) (by decide)

set_option exponentiation.threshold 2048 in
private theorem s12_hensel_elim_w15 :
    let blocks_s12 : List (Nat × Nat) := [(10, 12), (11, 8), (10, 2), (10, 2)]
    let D_s12 := 2 ^ blockStepSum blocks_s12 - 3 ^ blockWeightSum blocks_s12
    henselOddInvModPow2 12 (3 ^ 10 * 3) * 3 = 11673 ∧
    9 * D_s12 < broxSpiralCarry blocks_s12 ∧
    11673 * D_s12 > broxSpiralCarry blocks_s12 ∧
    ¬ (∃ qs : List Nat,
      qs.length = 4 ∧
      ∀ j : Nat, j < 4 -> D_s12 * natAt qs j = broxSpiralCarry (rotBlocks j blocks_s12)) := by
  dsimp only
  refine ⟨by decide, by decide, by decide, ?_⟩
  rintro ⟨qs, hlen, hqs⟩
  have h3_dvd : 3 ∣ natListGcd qs :=
    (m_block_companion_prime_quotient_cascades.1
      (10, 12) [(11, 8), (10, 2), (10, 2)] qs (by decide) (by decide) hlen hqs).2.1 (by decide)
  have hrec01 : 2 ^ (12 + 11) * natAt qs 1 = 3 ^ 10 * natAt qs 0 + (2 ^ 12 - 1) :=
    (m_block_two_pivot_telescoping_and_2adic_quotient_boost.1.2
      (10, 12) (11, 8) [(10, 2), (10, 2)] (by decide)).2 (natAt qs 0) (natAt qs 1)
      (hqs 0 (by decide)) (hqs 1 (by decide))
  have hq0_boost := (hensel_quotient_boost_w15 12 10 12 11 (natAt qs 0) (natAt qs 1) 3
    (by decide) (by decide) (by decide) (gcd_head_of_len4_w15 3 qs hlen h3_dvd) hrec01).2
  have hinv_eq : henselOddInvModPow2 12 (3 ^ 10 * 3) * 3 = 11673 := by decide
  rw [hinv_eq] at hq0_boost
  exact elim_of_ge_and_lt_mul_w15
    (2 ^ blockStepSum [(10, 12), (11, 8), (10, 2), (10, 2)] - 3 ^ blockWeightSum [(10, 12), (11, 8), (10, 2), (10, 2)])
    (broxSpiralCarry (rotBlocks 0 [(10, 12), (11, 8), (10, 2), (10, 2)]))
    11673 (natAt qs 0) hq0_boost (hqs 0 (by decide)) (by decide)

set_option exponentiation.threshold 2048 in
/--
  Theorem W15.2c (`m_block_three_pivot_and_mod_pow2_2adic_quotient_boost`,
  `zero custom axioms`):
  Constructive Newton–Hensel Odd Modular Inverse `henselOddInvModPow2`, General `∀ s ≥ 4` Mod-`2^s`
  2-Adic Inverse-Residue Quotient Boost (`q_0 ≥ henselOddInvModPow2 s (3^{w_0} * d_mult) * d_mult`),
  `<3> mod 2^s` Subgroup Saturation at `5 * d_mult` Across ALL `s ≥ 4`, Universal 3-Pivot Cross-Block
  Brox Squeeze, `56,063×` Elimination of Balanced `m = 4` `[(17, 2), (17, 2), (17, 2), (17, 34)]`
  (Escaping ALL 4 Two-Pivot Rotations), & Mod-`2^12` (`q_0 ≥ 11,673`) Elimination of
  `[(10, 12), (11, 8), (10, 2), (10, 2)]` (`Branch P3.4`, witness `M1_BALANCED_4BLOCK_TWO_PIVOT_ESCAPE`,
  `W15_H2`).
-/
theorem m_block_three_pivot_and_mod_pow2_2adic_quotient_boost :
    ((∀ (s d : Nat), s ≥ 1 -> d % 2 = 1 ->
        1 ≤ henselOddInvModPow2 s d ∧
        henselOddInvModPow2 s d < 2 ^ s ∧
        (d * henselOddInvModPow2 s d) % 2 ^ s = 1) ∧
     (∀ (s w0 a0 w1 q0 q1 d_mult : Nat),
        s ≥ 4 -> a0 ≥ s -> d_mult % 2 = 1 -> d_mult ∣ q0 ->
        2 ^ (a0 + w1) * q1 = 3 ^ w0 * q0 + (2 ^ a0 - 1) ->
        (3 ^ w0 * q0) % 2 ^ s = 1 ∧
        q0 ≥ henselOddInvModPow2 s (3 ^ w0 * d_mult) * d_mult) ∧
     (∀ s : Nat, s ≥ 4 ->
        ∃ w0 : Nat, w0 < 2 ^ (s - 2) ∧ (3 ^ w0 * (5 * (2 ^ s - 1))) % 2 ^ s = 1)) ∧
    (∀ (b0 b1 b2 : Nat × Nat) (tail : List (Nat × Nat)) (qs : List Nat) (d_mult : Nat),
      let blocks := b0 :: b1 :: b2 :: tail
      let W := blockWeightSum blocks
      let K := blockStepSum blocks
      let D := 2 ^ K - 3 ^ W
      let Wt := blockWeightSum tail
      let Et := blockStepSum (b2 :: tail) - blockWeightSum (b2 :: tail)
      (∀ b ∈ blocks, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      3 ^ W < 2 ^ K ->
      qs.length = blocks.length ->
      (∀ j : Nat, j < blocks.length -> D * natAt qs j = broxSpiralCarry (rotBlocks j blocks)) ->
      d_mult ∣ natListGcd qs ->
      broxSpiralCarry blocks + 3 ^ (b1.1 + b2.1 + Wt) ≤
        3 ^ (b1.1 + b2.1 + Wt) * 2 ^ b0.2 +
        2 ^ (b0.2 + b1.1) * 3 ^ (b2.1 + Wt) * (2 ^ b1.2 - 1) +
        2 ^ (b0.2 + b1.1 + b1.2 + b2.1) * 3 ^ Wt * (2 ^ Et - 1) ∧
      d_mult * D + 3 ^ (b1.1 + b2.1 + Wt) ≤
        3 ^ (b1.1 + b2.1 + Wt) * 2 ^ b0.2 +
        2 ^ (b0.2 + b1.1) * 3 ^ (b2.1 + Wt) * (2 ^ b1.2 - 1) +
        2 ^ (b0.2 + b1.1 + b1.2 + b2.1) * 3 ^ Wt * (2 ^ Et - 1)) ∧
    (let blocks_bal4 : List (Nat × Nat) := [(17, 2), (17, 2), (17, 2), (17, 34)]
     let D_bal4 := 2 ^ blockStepSum blocks_bal4 - 3 ^ blockWeightSum blocks_bal4
     (∀ j : Nat, j < 4 ->
       let r := rotBlocks j blocks_bal4
       let b0 := blockAt r 0
       let b1 := blockAt r 1
       let b2 := blockAt r 2
       let b3 := blockAt r 3
       3 * D_bal4 <
         3 ^ (b1.1 + b2.1 + b3.1) * (2 ^ b0.2 - 1) +
         2 ^ (b0.2 + b1.1) * 3 ^ (b2.1 + b3.1) * (2 ^ (b1.2 + b2.2 + b3.2) - 1)) ∧
     56063 * broxSpiralCarry blocks_bal4 < 3 * D_bal4 ∧
     ¬ (∃ qs : List Nat,
       qs.length = 4 ∧
       ∀ j : Nat, j < 4 -> D_bal4 * natAt qs j = broxSpiralCarry (rotBlocks j blocks_bal4))) ∧
    (let blocks_s12 : List (Nat × Nat) := [(10, 12), (11, 8), (10, 2), (10, 2)]
     let D_s12 := 2 ^ blockStepSum blocks_s12 - 3 ^ blockWeightSum blocks_s12
     henselOddInvModPow2 12 (3 ^ 10 * 3) * 3 = 11673 ∧
     9 * D_s12 < broxSpiralCarry blocks_s12 ∧
     11673 * D_s12 > broxSpiralCarry blocks_s12 ∧
     ¬ (∃ qs : List Nat,
       qs.length = 4 ∧
       ∀ j : Nat, j < 4 -> D_s12 * natAt qs j = broxSpiralCarry (rotBlocks j blocks_s12))) :=
  ⟨⟨fun s d hs hd =>
      let ⟨h1, h2, _, h4⟩ := henselOddInvModPow2_spec s d hs hd
      ⟨h1, h2, h4⟩,
    hensel_quotient_boost_w15,
    subgroup_sat_mod_pow2_w15⟩,
   three_pivot_brox_squeeze_w15,
   bal4_three_pivot_elim_w15,
   s12_hensel_elim_w15⟩

end CollatzFormal

