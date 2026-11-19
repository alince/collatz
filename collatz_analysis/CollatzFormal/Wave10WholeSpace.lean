/-
  CollatzFormal/Wave10WholeSpace.lean
  Wave 10 Whole-Space Mathematical & CS Proof Loop:
  1. Front A — Swap-Active Higher-Modulus (`M = 3, 4`) & Two-Sided (`semL2 × collatzSemMod M`)
     Zantema Semantic Labelling: Universal Fixed-Point Swap Commutators (`∀ M ≥ 1`),
     Two-Sided Soundness (`-> CollatzConjectureStandard`), 2-Level `M = 3` Termination of `S9`,
     Complete 2-Level Two-Sided `(2 × 6)` Termination of Swap-Active `all11 \ {R8}` (`120 -> 15 -> 0`),
     Garden-of-Eden `R2_1` Removal on Full `all11` (`33 -> 32`), `14/40` Two-Sided `(2 × 2)` Removal on
     `omit R8`, & Universal `∀ k` Positive Parikh-Syzygy Tower Barriers Across 12 Cores (Branch P4.3)
  2. Front B — Universal 1-Block Coprime-Order Prime-Divisor & Subgroup-Product Law,
     Pure-`Nat` Gauss Lemma + Universal Mod-`24` `{11, 13}` 1-Block Exclusion & Shared-Mersenne
     2-Block Mod-`24` `(82, 130)` / `(164, 260)` & `3 ∣ q0, 3 ∣ q1` Obstructions, Exact `6 x 6`
     Single-Base `(T = 2, U = 3)` & `(T = 5, U = 1)` / Two-Base `(T = 2, U = 3)` Factorization,
     Confluent `(2^u - 1)^(2T - 1)` Extrapolation Divisibility, and Convergent-Cone Non-Vanishing (Branches P3.4 & P3.3)
  3. Front C — 2-Regular Stern–Brocot (`sternDiatomic`, `0`-Spine, `1`-Spine, & Alternating `01` Fibonacci)
     & Non-Regular `∀ Q ≥ 1` Zero-Testing `1`-Counter Pushdown Automaton (`OCN`: Bounded, `1`-Incrementing
     Dyck, & `0`-Incrementing `(zeroBitCount - oneBitCount)` `zeroExcessOCN`) Preimage Impossibility,
     plus 7th Solvable Cousin `T_diamond7` (`ω^5` 5-Tier Cascade, `Q_(6)^+` Avoidance, & Separation) (Branches P1.2 & P5.9)
  4. Front D — Complete Mod-`54` (`2 * 3^3`) Markov Bijection & `27 mod 54` Lock, Coupled
     Archimedean–Triadic Dyadic-Window `[2^M, 2^(M+1))` Unique Deterministic Shift-Pinning
     (`∀ L ≤ M + w + 1`), Empty-Cell Annihilation, & Multi-Scale Diagonal `L^2` Energy (Branches P2.2 & P5.3)

  Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

import CollatzFormal.Wave9WholeSpace

namespace CollatzFormal

-- ============================================================================
-- SECTION 1: Front A (Branch P4.3) — Swap-Active `M = 3` & Two-Sided Zantema
--            Semantic Labelling, `all11` GoE Removal, & Positive Parikh Syzygies
-- ============================================================================

/-- `10/11` swap-active rule list omitting only `R8 : [T2, B1] -> [B1, T2]` (`S9 ∪ {R3}`). -/
def all11OmitR8List : List (List MixedSRSSym × List MixedSRSSym) :=
  [ ([.L, .B0], [.L]),
    ([.L, .B1], [.L, .T2]),
    ([.T0, .B0], [.B0, .T0]),
    ([.T0, .B1], [.B1, .T1]),
    ([.T1, .B0], [.B1, .T0]),
    ([.T1, .B1], [.B0, .T2]),
    ([.T2, .B0], [.B0, .T1]),
    ([.T0, .R],  [.B1, .R]),
    ([.T1, .R],  [.B0, .B0, .R]),
    ([.T2, .R],  [.B1, .B0, .R]) ]

/-- `10/11` swap-active rule list omitting only `R3 : [T0, B0] -> [B0, T0]` (`S9 ∪ {R8}`). -/
def all11OmitR3List : List (List MixedSRSSym × List MixedSRSSym) :=
  [ ([.L, .B0], [.L]),
    ([.L, .B1], [.L, .T2]),
    ([.T0, .B1], [.B1, .T1]),
    ([.T1, .B0], [.B1, .T0]),
    ([.T1, .B1], [.B0, .T2]),
    ([.T2, .B0], [.B0, .T1]),
    ([.T2, .B1], [.B1, .T2]),
    ([.T0, .R],  [.B1, .R]),
    ([.T1, .R],  [.B0, .B0, .R]),
    ([.T2, .R],  [.B1, .B0, .R]) ]

theorem omitR8_sub_all11 (r : List MixedSRSSym × List MixedSRSSym)
    (hm : r ∈ all11OmitR8List) : r ∈ all11RuleList := by
  revert r hm; decide

theorem omitR3_sub_all11 (r : List MixedSRSSym × List MixedSRSSym)
    (hm : r ∈ all11OmitR3List) : r ∈ all11RuleList := by
  revert r hm; decide

/--
  Theorem W10.1a (`zantema_fixed_point_swap_commutators`, `zero custom axioms`):
  Universal Fixed-Point Swap Preservation Across ALL Moduli `M ≥ 1`:
  1. At `a = 0` (`2 * 0 ≡ 0` and `3 * 0 ≡ 0 (mod M)`), `R3 : [T0, B0] -> [B0, T0]` labels to the
     pure length-2 commutator `[T0_0, B0_0] -> [B0_0, T0_0]`, which belongs to
     `labelledCollatzRules M hM all11OmitR8List` and `labelledCollatzRules M hM all11RuleList`!
  2. At `a = M - 1 ≡ -1 (mod M)` (the `M2 = Z^-` fixed point `-1`: `2(-1)+1 = -1`, `3(-1)+2 = -1`),
     `R8 : [T2, B1] -> [B1, T2]` labels to the pure length-2 commutator
     `[T2_{M-1}, B1_{M-1}] -> [B1_{M-1}, T2_{M-1}]`, which belongs to
     `labelledCollatzRules M hM all11OmitR3List` and `labelledCollatzRules M hM all11RuleList`!
-/
theorem zantema_fixed_point_swap_commutators (M : Nat) (hM : M ≥ 1) :
    let hm1 : M - 1 < M := by omega
    let b0_0 := labelCollatzSymIdx M hM .B0 0 hM
    let t0_0 := labelCollatzSymIdx M hM .T0 0 hM
    let b1_m := labelCollatzSymIdx M hM .B1 (M - 1) hm1
    let t2_m := labelCollatzSymIdx M hM .T2 (M - 1) hm1
    (labelCollatzWord M hM [.T0, .B0] 0 hM = [t0_0, b0_0] ∧
     labelCollatzWord M hM [.B0, .T0] 0 hM = [b0_0, t0_0] ∧
     ([t0_0, b0_0], [b0_0, t0_0]) ∈ labelledCollatzRules M hM all11OmitR8List ∧
     ([t0_0, b0_0], [b0_0, t0_0]) ∈ labelledCollatzRules M hM all11RuleList) ∧
    (labelCollatzWord M hM [.T2, .B1] (M - 1) hm1 = [t2_m, b1_m] ∧
     labelCollatzWord M hM [.B1, .T2] (M - 1) hm1 = [b1_m, t2_m] ∧
     ([t2_m, b1_m], [b1_m, t2_m]) ∈ labelledCollatzRules M hM all11OmitR3List ∧
     ([t2_m, b1_m], [b1_m, t2_m]) ∈ labelledCollatzRules M hM all11RuleList) := by
  dsimp only
  have hm1 : M - 1 < M := by omega
  have h0_2 : (2 * 0) % M = 0 := by simp
  have h0_3 : (3 * 0) % M = 0 := by simp
  have hm_b1 : (2 * (M - 1) + 1) % M = M - 1 := by
    have heq : 2 * (M - 1) + 1 = (M - 1) + M * 1 := by omega
    rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hm1]
  have hm_t2 : (3 * (M - 1) + 2) % M = M - 1 := by
    have heq : 3 * (M - 1) + 2 = (M - 1) + M * 2 := by omega
    rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hm1]
  have hr3_l : labelCollatzWord M hM [.T0, .B0] 0 hM =
      [labelCollatzSymIdx M hM .T0 0 hM, labelCollatzSymIdx M hM .B0 0 hM] := by
    simp only [labelCollatzWord, evalCollatzSemWord, collatzSemMod, List.cons.injEq, and_true]
    apply Fin.ext; simp [labelCollatzSymIdx, h0_2]
  have hr3_r : labelCollatzWord M hM [.B0, .T0] 0 hM =
      [labelCollatzSymIdx M hM .B0 0 hM, labelCollatzSymIdx M hM .T0 0 hM] := by
    simp only [labelCollatzWord, evalCollatzSemWord, collatzSemMod, List.cons.injEq, and_true]
    apply Fin.ext; simp [labelCollatzSymIdx, h0_3]
  have hr8_l : labelCollatzWord M hM [.T2, .B1] (M - 1) hm1 =
      [labelCollatzSymIdx M hM .T2 (M - 1) hm1, labelCollatzSymIdx M hM .B1 (M - 1) hm1] := by
    simp only [labelCollatzWord, evalCollatzSemWord, collatzSemMod, List.cons.injEq, and_true]
    apply Fin.ext; simp [labelCollatzSymIdx, hm_b1]
  have hr8_r : labelCollatzWord M hM [.B1, .T2] (M - 1) hm1 =
      [labelCollatzSymIdx M hM .B1 (M - 1) hm1, labelCollatzSymIdx M hM .T2 (M - 1) hm1] := by
    simp only [labelCollatzWord, evalCollatzSemWord, collatzSemMod, List.cons.injEq, and_true]
    apply Fin.ext; simp [labelCollatzSymIdx, hm_t2]
  refine ⟨⟨hr3_l, hr3_r, ?_, ?_⟩, ⟨hr8_l, hr8_r, ?_, ?_⟩⟩
  · rw [← hr3_l, ← hr3_r]
    exact mem_labelledCollatzRules M hM all11OmitR8List [.T0, .B0] [.B0, .T0] 0 hM (by decide)
  · rw [← hr3_l, ← hr3_r]
    exact mem_labelledCollatzRules M hM all11RuleList [.T0, .B0] [.B0, .T0] 0 hM (by decide)
  · rw [← hr8_l, ← hr8_r]
    exact mem_labelledCollatzRules M hM all11OmitR3List [.T2, .B1] [.B1, .T2] (M - 1) hm1 (by decide)
  · rw [← hr8_l, ← hr8_r]
    exact mem_labelledCollatzRules M hM all11RuleList [.T2, .B1] [.B1, .T2] (M - 1) hm1 (by decide)

-- Exact 2-State Left-to-Right Semantic Model `collatzSemL2` & General Two-Sided Labelling (`∀ M ≥ 1`):

/-- Exact 2-state left-to-right parity-carry semantic model of `all11RuleList` on `{0, 1}`. -/
def collatzSemL2 (s : MixedSRSSym) (q : Nat) : Nat :=
  match s with
  | .L | .R | .B0 | .T0 => 0
  | .B1 | .T2 => 1
  | .T1 => q % 2

def evalCollatzSemL2 : List MixedSRSSym -> Nat -> Nat
  | [], q => q % 2
  | s :: u, q => evalCollatzSemL2 u (collatzSemL2 s (q % 2))

theorem collatzSemL2_lt (s : MixedSRSSym) (q : Nat) : collatzSemL2 s q < 2 :=
  match s with
  | .L | .R | .B0 | .T0 => Nat.zero_lt_succ 1
  | .B1 | .T2 => Nat.succ_lt_succ (Nat.zero_lt_succ 0)
  | .T1 => Nat.mod_lt q (Nat.zero_lt_succ 1)

theorem evalCollatzSemL2_lt : ∀ (u : List MixedSRSSym) (q : Nat), evalCollatzSemL2 u q < 2
  | [], q => Nat.mod_lt q (by decide)
  | s :: u, q => evalCollatzSemL2_lt u (collatzSemL2 s (q % 2))

theorem collatzSemL2_mod_in (s : MixedSRSSym) (q : Nat) :
    collatzSemL2 s (q % 2) = collatzSemL2 s q := by
  cases s <;> simp [collatzSemL2]

theorem evalCollatzSemL2_mod_in : ∀ (u : List MixedSRSSym) (q : Nat),
    evalCollatzSemL2 u (q % 2) = evalCollatzSemL2 u q
  | [], q => by simp [evalCollatzSemL2]
  | s :: u, q => by simp [evalCollatzSemL2]

theorem evalCollatzSemL2_append : ∀ (u v : List MixedSRSSym) (q : Nat),
    evalCollatzSemL2 (u ++ v) q = evalCollatzSemL2 v (evalCollatzSemL2 u q)
  | [], v, q => by simp [evalCollatzSemL2, evalCollatzSemL2_mod_in]
  | s :: u, v, q => by
    simp only [List.cons_append, evalCollatzSemL2]
    exact evalCollatzSemL2_append u v (collatzSemL2 s (q % 2))

/-- Choice-free `zero custom axioms` proof that `evalCollatzSemL2` preserves ALL 11 rules across `q ∈ {0, 1}`. -/
theorem collatz_l2_is_exact_left_semantic_model
    (r : List MixedSRSSym × List MixedSRSSym) (hr : r ∈ all11RuleList)
    (q : Nat) :
    evalCollatzSemL2 r.1 q = evalCollatzSemL2 r.2 q := by
  have hmod : q % 2 = 0 ∨ q % 2 = 1 := by omega
  rw [← evalCollatzSemL2_mod_in r.1 q, ← evalCollatzSemL2_mod_in r.2 q]
  rcases hmod with h0 | h1
  · rw [h0]; revert r hr; decide
  · rw [h1]; revert r hr; decide

/-- Two-sided symbol index `s * (2 * M) + (q * M + a) < 14 * M` (`q < 2, a < M`). -/
def labelTwoSidedSymIdx (M : Nat) (_hM : M ≥ 1) (s : MixedSRSSym)
    (q : Nat) (hq : q < 2) (a : Nat) (ha : a < M) : Fin (14 * M) :=
  ⟨mixedSymIdx s * (2 * M) + (q * M + a), by
    have hqa : q * M + a < 2 * M := by
      cases q with
      | zero =>
        have h0 : 0 * M + a = a := by rw [Nat.zero_mul, Nat.zero_add]
        rw [h0, Nat.two_mul]
        exact Nat.lt_of_lt_of_le ha (Nat.le_add_left M M)
      | succ q' =>
        cases q' with
        | zero =>
          rw [Nat.one_mul, Nat.two_mul]
          exact Nat.add_lt_add_left ha M
        | succ q'' =>
          exact False.elim (Nat.not_lt_zero q'' (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hq)))
    have hs1 : mixedSymIdx s + 1 ≤ 7 := mixedSymIdx_lt_seven s
    have hm : (mixedSymIdx s + 1) * (2 * M) ≤ 14 * M := by
      have hm0 : (mixedSymIdx s + 1) * (2 * M) ≤ 7 * (2 * M) := Nat.mul_le_mul_right (2 * M) hs1
      rwa [← Nat.mul_assoc 7 2 M] at hm0
    have hlt : mixedSymIdx s * (2 * M) + (q * M + a) < (mixedSymIdx s + 1) * (2 * M) := by
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_lt_add_left hqa _
    exact Nat.lt_of_lt_of_le hlt hm⟩

/-- Label `u` simultaneously left-to-right by `collatzSemL2` (state `q < 2`) and right-to-left by `collatzSemMod M` (state `a < M`). -/
def labelCollatzWordTwoSided (M : Nat) (hM : M ≥ 1) :
    List MixedSRSSym -> (q : Nat) -> q < 2 -> (a : Nat) -> a < M -> List (Fin (14 * M))
  | [], _, _, _, _ => []
  | s :: u, q, hq, a, ha =>
    let a_u := evalCollatzSemWord M u a
    have ha_u : a_u < M := evalCollatzSemWord_lt M hM u a ha
    let q_next := collatzSemL2 s q
    have hq_next : q_next < 2 := collatzSemL2_lt s q
    labelTwoSidedSymIdx M hM s q hq a_u ha_u ::
      labelCollatzWordTwoSided M hM u q_next hq_next a ha

theorem labelCollatzWordTwoSided_congr (M : Nat) (hM : M ≥ 1) (u : List MixedSRSSym)
    (q1 q2 : Nat) (hq1 : q1 < 2) (hq2 : q2 < 2) (hqe : q1 = q2)
    (a1 a2 : Nat) (ha1 : a1 < M) (ha2 : a2 < M) (hae : a1 = a2) :
    labelCollatzWordTwoSided M hM u q1 hq1 a1 ha1 =
      labelCollatzWordTwoSided M hM u q2 hq2 a2 ha2 := by
  subst hqe; subst hae; rfl

theorem labelCollatzWordTwoSided_append (M : Nat) (hM : M ≥ 1) :
    ∀ (u v : List MixedSRSSym) (q : Nat) (hq : q < 2) (a : Nat) (ha : a < M),
      labelCollatzWordTwoSided M hM (u ++ v) q hq a ha =
        labelCollatzWordTwoSided M hM u q hq (evalCollatzSemWord M v a)
          (evalCollatzSemWord_lt M hM v a ha) ++
        labelCollatzWordTwoSided M hM v (evalCollatzSemL2 u q)
          (evalCollatzSemL2_lt u q) a ha
  | [], v, q, hq, a, ha => by
    simp only [List.nil_append, labelCollatzWordTwoSided, evalCollatzSemL2]
    exact labelCollatzWordTwoSided_congr M hM v q (q % 2) hq (Nat.mod_lt q (by decide))
      (Nat.mod_eq_of_lt hq).symm a a ha ha rfl
  | s :: u, v, q, hq, a, ha => by
    simp only [List.cons_append, labelCollatzWordTwoSided, evalCollatzSemL2, List.cons.injEq]
    have hq_mod : q % 2 = q := Nat.mod_eq_of_lt hq
    have heq_r : evalCollatzSemWord M (u ++ v) a =
        evalCollatzSemWord M u (evalCollatzSemWord M v a) :=
      evalCollatzSemWord_append M u v a
    refine ⟨?_, ?_⟩
    · apply Fin.ext; simp [labelTwoSidedSymIdx, heq_r]
    · have ih := labelCollatzWordTwoSided_append M hM u v (collatzSemL2 s q)
        (collatzSemL2_lt s q) a ha
      rw [ih]
      apply congrArg (labelCollatzWordTwoSided M hM u (collatzSemL2 s q) (collatzSemL2_lt s q)
        (evalCollatzSemWord M v a) (evalCollatzSemWord_lt M hM v a ha) ++ ·)
      exact labelCollatzWordTwoSided_congr M hM v
        (evalCollatzSemL2 u (collatzSemL2 s q))
        (evalCollatzSemL2 u (collatzSemL2 s (q % 2)))
        (evalCollatzSemL2_lt u _) (evalCollatzSemL2_lt u _)
        (by rw [hq_mod]) a a ha ha rfl

def expandTwoSidedCarriersAux (M : Nat) (hM : M ≥ 1)
    (l r : List MixedSRSSym) (q : Nat) (hq : q < 2) :
    (k : Nat) -> k ≤ M -> List (List (Fin (14 * M)) × List (Fin (14 * M)))
  | 0, _ => []
  | k + 1, hk =>
    (labelCollatzWordTwoSided M hM l q hq k hk,
     labelCollatzWordTwoSided M hM r q hq k hk) ::
      expandTwoSidedCarriersAux M hM l r q hq k (Nat.le_of_lt hk)

def twoSidedLabelledCollatzRules (M : Nat) (hM : M ≥ 1) :
    List (List MixedSRSSym × List MixedSRSSym) -> List (List (Fin (14 * M)) × List (Fin (14 * M)))
  | [] => []
  | (l, r) :: rs =>
    expandTwoSidedCarriersAux M hM l r 0 (by decide) M (Nat.le_refl M) ++
    expandTwoSidedCarriersAux M hM l r 1 (by decide) M (Nat.le_refl M) ++
    twoSidedLabelledCollatzRules M hM rs

theorem mem_expandTwoSidedCarriersAux (M : Nat) (hM : M ≥ 1)
    (l r : List MixedSRSSym) (q : Nat) (hq : q < 2) :
    ∀ (k : Nat) (hk : k ≤ M) (a : Nat) (ha : a < k),
      (labelCollatzWordTwoSided M hM l q hq a (Nat.lt_of_lt_of_le ha hk),
       labelCollatzWordTwoSided M hM r q hq a (Nat.lt_of_lt_of_le ha hk)) ∈
        expandTwoSidedCarriersAux M hM l r q hq k hk
  | 0, _, _, ha => by omega
  | k + 1, hk, a, ha => by
    simp only [expandTwoSidedCarriersAux, List.mem_cons]
    by_cases hak : a = k
    · subst hak; exact Or.inl rfl
    · exact Or.inr (mem_expandTwoSidedCarriersAux M hM l r q hq k (by omega) a (by omega))

theorem mem_twoSidedLabelledCollatzRules (M : Nat) (hM : M ≥ 1) :
    ∀ (rules : List (List MixedSRSSym × List MixedSRSSym))
      (l r : List MixedSRSSym) (q : Nat) (hq : q < 2) (a : Nat) (ha : a < M),
      (l, r) ∈ rules ->
      (labelCollatzWordTwoSided M hM l q hq a ha,
       labelCollatzWordTwoSided M hM r q hq a ha) ∈
        twoSidedLabelledCollatzRules M hM rules
  | [], _, _, _, _, _, _, hm => by cases hm
  | (l0, r0) :: rs, l, r, q, hq, a, ha, hm => by
    simp only [twoSidedLabelledCollatzRules, List.mem_append]
    cases hm with
    | head =>
      left
      rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl
      · exact Or.inl (mem_expandTwoSidedCarriersAux M hM l0 r0 0 (by decide) M (Nat.le_refl M) a ha)
      · exact Or.inr (mem_expandTwoSidedCarriersAux M hM l0 r0 1 (by decide) M (Nat.le_refl M) a ha)
    | tail _ hrs =>
      exact Or.inr (mem_twoSidedLabelledCollatzRules M hM rs l r q hq a ha hrs)

theorem two_sided_zantema_step_lifts (M : Nat) (hM : M ≥ 1)
    (rules : List (List MixedSRSSym × List MixedSRSSym))
    (hsemL : ∀ r ∈ rules, ∀ q : Nat, evalCollatzSemL2 r.1 q = evalCollatzSemL2 r.2 q)
    (hsemR : ∀ r ∈ rules, ∀ a : Nat, a < M ->
      evalCollatzSemWord M r.1 a = evalCollatzSemWord M r.2 a) :
    ∀ w1 w3 : List MixedSRSSym,
      srsPlusFromList rules w1 w3 ->
      genSRSPlus (twoSidedLabelledCollatzRules M hM rules)
        (labelCollatzWordTwoSided M hM w1 0 (by decide) 0 hM)
        (labelCollatzWordTwoSided M hM w3 0 (by decide) 0 hM) := by
  have hstep : ∀ w1 w2 : List MixedSRSSym,
      srsStepFromList rules w1 w2 ->
      genSRSStep (twoSidedLabelledCollatzRules M hM rules)
        (labelCollatzWordTwoSided M hM w1 0 (by decide) 0 hM)
        (labelCollatzWordTwoSided M hM w2 0 (by decide) 0 hM) := by
    rintro w1 w2 ⟨p, l, r, sfx, hmem, hw1, hw2⟩
    let qp := evalCollatzSemL2 p 0
    have hqp : qp < 2 := evalCollatzSemL2_lt p 0
    let asfx := evalCollatzSemWord M sfx 0
    have hasfx : asfx < M := evalCollatzSemWord_lt M hM sfx 0 hM
    have hls_eq : evalCollatzSemWord M (l ++ sfx) 0 = evalCollatzSemWord M (r ++ sfx) 0 := by
      rw [evalCollatzSemWord_append M l sfx 0, evalCollatzSemWord_append M r sfx 0]
      exact hsemR (l, r) hmem asfx hasfx
    have hpl_eq : evalCollatzSemL2 (p ++ l) 0 = evalCollatzSemL2 (p ++ r) 0 := by
      rw [evalCollatzSemL2_append p l 0, evalCollatzSemL2_append p r 0]
      exact hsemL (l, r) hmem qp
    have hlab1 : labelCollatzWordTwoSided M hM (p ++ l ++ sfx) 0 (by decide) 0 hM =
        labelCollatzWordTwoSided M hM p 0 (by decide)
          (evalCollatzSemWord M (l ++ sfx) 0) (evalCollatzSemWord_lt M hM (l ++ sfx) 0 hM) ++
        labelCollatzWordTwoSided M hM l qp hqp asfx hasfx ++
        labelCollatzWordTwoSided M hM sfx (evalCollatzSemL2 (p ++ l) 0)
          (evalCollatzSemL2_lt (p ++ l) 0) 0 hM := by
      rw [List.append_assoc p l sfx,
          labelCollatzWordTwoSided_append M hM p (l ++ sfx) 0 (by decide) 0 hM,
          labelCollatzWordTwoSided_append M hM l sfx qp hqp 0 hM,
          ← List.append_assoc,
          labelCollatzWordTwoSided_congr M hM sfx
            (evalCollatzSemL2 l qp) (evalCollatzSemL2 (p ++ l) 0)
            (evalCollatzSemL2_lt l qp) (evalCollatzSemL2_lt (p ++ l) 0)
            (evalCollatzSemL2_append p l 0).symm 0 0 hM hM rfl]
    have hlab2 : labelCollatzWordTwoSided M hM (p ++ r ++ sfx) 0 (by decide) 0 hM =
        labelCollatzWordTwoSided M hM p 0 (by decide)
          (evalCollatzSemWord M (l ++ sfx) 0) (evalCollatzSemWord_lt M hM (l ++ sfx) 0 hM) ++
        labelCollatzWordTwoSided M hM r qp hqp asfx hasfx ++
        labelCollatzWordTwoSided M hM sfx (evalCollatzSemL2 (p ++ l) 0)
          (evalCollatzSemL2_lt (p ++ l) 0) 0 hM := by
      rw [List.append_assoc p r sfx,
          labelCollatzWordTwoSided_append M hM p (r ++ sfx) 0 (by decide) 0 hM,
          labelCollatzWordTwoSided_append M hM r sfx qp hqp 0 hM,
          ← List.append_assoc,
          labelCollatzWordTwoSided_congr M hM p 0 0 (by decide) (by decide) rfl
            (evalCollatzSemWord M (r ++ sfx) 0) (evalCollatzSemWord M (l ++ sfx) 0)
            (evalCollatzSemWord_lt M hM (r ++ sfx) 0 hM)
            (evalCollatzSemWord_lt M hM (l ++ sfx) 0 hM) hls_eq.symm,
          labelCollatzWordTwoSided_congr M hM sfx
            (evalCollatzSemL2 r qp) (evalCollatzSemL2 (p ++ l) 0)
            (evalCollatzSemL2_lt r qp) (evalCollatzSemL2_lt (p ++ l) 0)
            (by rw [← evalCollatzSemL2_append p r 0, hpl_eq]) 0 0 hM hM rfl]
    refine ⟨_, labelCollatzWordTwoSided M hM l qp hqp asfx hasfx,
            labelCollatzWordTwoSided M hM r qp hqp asfx hasfx, _,
            mem_twoSidedLabelledCollatzRules M hM rules l r qp hqp asfx hasfx hmem,
            by rw [hw1]; exact hlab1,
            by rw [hw2]; exact hlab2⟩
  have hreach : ∀ w2 w3 : List MixedSRSSym,
      srsReachesFromList rules w2 w3 ->
      genSRSReaches (twoSidedLabelledCollatzRules M hM rules)
        (labelCollatzWordTwoSided M hM w2 0 (by decide) 0 hM)
        (labelCollatzWordTwoSided M hM w3 0 (by decide) 0 hM) := by
    intro w2 w3 hr
    induction hr with
    | refl _ => exact .refl _
    | step hs _ ih => exact .step (hstep _ _ hs) ih
  intro w1 w3 ⟨w2, hs12, hr23⟩
  exact ⟨_, hstep w1 w2 hs12, hreach w2 w3 hr23⟩

/--
  Theorem W10.1b (`two_sided_zantema_semantic_labelling_soundness`, `zero custom axioms`):
  Universal Two-Sided (`collatzSemL2 × collatzSemMod M`) Zantema Semantic Labelling Soundness:
  1. For ANY sub-SRS `rules ⊆ all11RuleList`, any `d`-dimensional `k`-level Hofbauer–Waldmann
     tower orienting `twoSidedLabelledCollatzRules M hM rules` unconditionally rules out infinite
     `srsPlusFromList rules` and `srsStepFromList rules` rewrite chains!
  2. Any two-sided Zantema Hofbauer–Waldmann tower for `all11RuleList` unconditionally implies
     `CollatzConjectureStandard`!
-/
theorem two_sided_zantema_semantic_labelling_soundness
    (M : Nat) (hM : M ≥ 1) (d : Nat) (hd : 0 < d) (k : Nat) :
    (∀ (rules : List (List MixedSRSSym × List MixedSRSSym)),
      (∀ r ∈ rules, r ∈ all11RuleList) ->
      GenOmegaHWTower d hd k (twoSidedLabelledCollatzRules M hM rules) ->
      (∀ seq : Nat -> List MixedSRSSym,
        ¬ (∀ t : Nat, srsPlusFromList rules (seq t) (seq (t + 1)))) ∧
      (∀ seq : Nat -> List MixedSRSSym,
        ¬ (∀ t : Nat, srsStepFromList rules (seq t) (seq (t + 1))))) ∧
    (GenOmegaHWTower d hd k (twoSidedLabelledCollatzRules M hM all11RuleList) ->
      CollatzConjectureStandard) := by
  refine ⟨?_, ?_⟩
  · intro rules hsub htower
    have hlift := two_sided_zantema_step_lifts M hM rules
      (fun r hr q => collatz_l2_is_exact_left_semantic_model r (hsub r hr) q)
      (fun r hr a ha => collatz_mod_m_is_exact_semantic_model M hM r (hsub r hr) a ha)
    have hno_plus : ∀ seq : Nat -> List MixedSRSSym,
        ¬ (∀ t : Nat, srsPlusFromList rules (seq t) (seq (t + 1))) := by
      intro seq hchain
      let lseq : Nat -> List (Fin (14 * M)) :=
        fun t => labelCollatzWordTwoSided M hM (seq t) 0 (by decide) 0 hM
      exact acc_no_infinite_chain (lseq 0)
        (gen_hw_tower_acc_srsPlus d hd k _ htower (lseq 0))
        lseq rfl (fun t => hlift (seq t) (seq (t + 1)) (hchain t))
    exact ⟨hno_plus, fun seq hstep => hno_plus seq (fun t => ⟨seq (t + 1), hstep t, .refl _⟩)⟩
  · intro htower_all
    rw [collatz_standard_iff_compressed]
    intro n hn
    have hlift := two_sided_zantema_step_lifts M hM all11RuleList
      (fun r hr q => collatz_l2_is_exact_left_semantic_model r hr q)
      (fun r hr a ha => collatz_mod_m_is_exact_semantic_model M hM r hr a ha)
    have hstep_pos : ∀ m : Nat, m ≥ 1 -> collatzStep m ≥ 1 := by
      intro m hm
      by_cases he : (m % 2 == 0) = true
      · have hm2 : m % 2 = 0 := of_decide_eq_true he
        simp only [collatzStep, he, ite_true]; omega
      · have hm2 : ¬ (m % 2 = 0) := fun h => he (decide_eq_true h)
        have hef : (m % 2 == 0) = false := decide_eq_false hm2
        simp only [collatzStep, hef, Bool.false_eq_true, ite_false]; omega
    let enc2S : Nat -> List (Fin (14 * M)) :=
      fun m => labelCollatzWordTwoSided M hM ([.L] ++ encodePosBin m ++ [.R]) 0 (by decide) 0 hM
    have hacc_enc : ∀ lw : List (Fin (14 * M)),
        Acc (fun w2 w1 => genSRSPlus (twoSidedLabelledCollatzRules M hM all11RuleList) w1 w2) lw ->
        ∀ m : Nat, m ≥ 1 -> enc2S m = lw -> ∃ t : Nat, collatzIter t m = 1 := by
      intro lw hacc
      induction hacc with
      | intro lw _ ih =>
        intro m hm1 hmlw
        by_cases hm_eq1 : m = 1
        · subst hm_eq1; exact ⟨0, rfl⟩
        · have hplus_unlab := encodePosBin_simulates_srsPlus_all11 m (by omega)
          have hplus_lab : genSRSPlus (twoSidedLabelledCollatzRules M hM all11RuleList)
              lw (enc2S (collatzStep m)) := by
            rw [← hmlw]
            exact hlift _ _ hplus_unlab
          rcases ih (enc2S (collatzStep m)) hplus_lab (collatzStep m) (hstep_pos m hm1) rfl with
            ⟨t, ht⟩
          exact ⟨t + 1, ht⟩
    exact hacc_enc (enc2S n)
      (gen_hw_tower_acc_srsPlus d hd k _ htower_all (enc2S n)) n hn rfl

-- Executable Fin-Alphabet Parikh Infrastructure, Certificates, & Positive Syzygy Barriers:

def evalFinParikh (N : Nat) (wt : Fin N -> Nat) : List (Fin N) -> Nat
  | [] => 0
  | s :: rest => wt s + evalFinParikh N wt rest

def checkFinParikhWeakBool (N : Nat) (wt : Fin N -> Nat) :
    List (List (Fin N) × List (Fin N)) -> Bool
  | [] => true
  | r :: rs =>
    decide (evalFinParikh N wt r.1 ≥ evalFinParikh N wt r.2) &&
    checkFinParikhWeakBool N wt rs

def filterFinParikhUnoriented (N : Nat) (wt : Fin N -> Nat) :
    List (List (Fin N) × List (Fin N)) -> List (List (Fin N) × List (Fin N))
  | [] => []
  | r :: rs =>
    if evalFinParikh N wt r.1 > evalFinParikh N wt r.2 then
      filterFinParikhUnoriented N wt rs
    else
      r :: filterFinParikhUnoriented N wt rs

/-- `k`-level `ω^k` Parikh / linear symbol-weight rule-removal tower over `Fin N`. -/
def GenOmegaParikhTower (N : Nat) : Nat -> List (List (Fin N) × List (Fin N)) -> Prop
  | 0, rules => rules = []
  | k + 1, rules =>
    rules = [] ∨
    ∃ (rem : List (List (Fin N) × List (Fin N)))
      (wt : Fin N -> Nat),
      (∀ r ∈ rules, evalFinParikh N wt r.1 ≥ evalFinParikh N wt r.2) ∧
      (∀ r ∈ rules, ¬ (evalFinParikh N wt r.1 > evalFinParikh N wt r.2) -> r ∈ rem) ∧
      GenOmegaParikhTower N k rem

-- Explicit `M = 3` (`Fin 21`) 2-Level Termination of `S9`, `all11` GoE Removal, & `TwoSided` Removals:

def certS9Mod3_L1 (s : Fin 21) : NatAffineDim 2 :=
  let w :=
    match s.val with
    | 0  => 10 | 1  => 1  | 6  => 12 | 7  => 2
    | 11 => 6  | 12 => 4  | 13 => 9  | 14 => 2
    | 15 => 9  | 16 => 3  | 17 => 7  | 19 => 9
    | 20 => 5  | _  => 0
  mk2DAffineW9 1 0 0 0 w 0

def certS9Mod3_L2 (s : Fin 21) : NatAffineDim 2 :=
  if s.val / 3 ≤ 1 then mk2DAffineW9 1 0 0 0 0 0
  else if s.val / 3 ≤ 3 then mk2DAffineW9 1 0 0 0 1 0
  else mk2DAffineW9 2 0 0 0 0 0

def towerS9Mod3_2Level : List (Fin 21 -> NatAffineDim 2) :=
  [certS9Mod3_L1, certS9Mod3_L2]

def wtM3GoE (s : Fin 21) : Nat :=
  if s.val = 0 then 1 else 0

def wtM3OmitR3 (s : Fin 21) : Nat :=
  match s.val with
  | 0 => 3 | 6 => 3 | 12 => 2 | _ => 0

def wtTwoSidedOmitR8 (s : Fin 28) : Nat :=
  match s.val with
  | 0  => 0   | 1  => 89  | 2  => 0   | 3  => 89
  | 4  => 1   | 5  => 1   | 6  => 98  | 7  => 98
  | 8  => 135 | 9  => 89  | 10 => 148 | 11 => 102
  | 12 => 168 | 13 => 173 | 14 => 130 | 15 => 66
  | 16 => 270 | 17 => 270 | 18 => 283 | 19 => 232
  | 20 => 316 | 21 => 224 | 22 => 265 | 23 => 275
  | 24 => 257 | 25 => 173 | 26 => 333 | _  => 202

def wtTwoSidedOmitR3 (s : Fin 28) : Nat :=
  match s.val with
  | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 17 => 4 | _ => 0

/--
  Theorem W10.1c (`s9_mod3_2level_termination_and_all11_goe_removal_cert`, choice-free `zero custom axioms`):
  Triadic `M = 3` & Two-Sided `(2 × 2)` Zantema Semantic-Labelling Certificates:
  1. **2-Level `M = 3` Termination of `S9 = all11 \ {R3, R8}` (`27 -> 4 -> 0`)**:
     Under `collatzSemMod 3`, `s9RuleList` collapses from Wave 9's 7-level `2D` tower (`M = 2`)
     down to a **2-level diagonal `1D`-affine tower** (`23/27` boundary & mixed rules eliminated
     by Parikh in Level 1, followed by `B(x) = x + 1, T(x) = 2x` terminating all `4` remaining
     interior swaps in Level 2)!
  2. **Garden-of-Eden Rule Removal on FULL `all11RuleList` (`33 -> 32`) & `omit R3` (`30 -> 25`)**:
     On **full `all11RuleList`** (`33` mod-3 labelled rules), `wtM3GoE` (`wt(L_0) = 1`) weakly
     orients all `33` rules and strictly removes `R2_1 : [L_0, B1_1] -> [L_2, T2_1]` (`33 -> 32`),
     while `wtM3OmitR3` strictly removes `5/30` rules from `all11OmitR3List` (`30 -> 25`)!
  3. **Two-Sided `(semL2 × collatzSemMod 2)` Breakthrough on `omit R8` (`40 -> 26`) & `omit R3` (`40 -> 36`)**:
     Whereas right-to-left `M = 2` Parikh removes `0/20` rules on both `omit R8` and `omit R3`,
     Two-Sided `(2 × 2)` strictly removes **`14/40` rules** from `all11OmitR8List` (`40 -> 26`,
     including all `q = 1` right-boundary rules `R9, R10, R11`) and **`4/40` rules** from
     `all11OmitR3List` (`40 -> 36`)!
-/
theorem s9_mod3_2level_termination_and_all11_goe_removal_cert :
    (checkFin2DHWTowerBool 21 towerS9Mod3_2Level (labelledCollatzRules 3 (by decide) s9RuleList) = true ∧
     (filterUnorientedGen2D certS9Mod3_L1 (labelledCollatzRules 3 (by decide) s9RuleList)).length = 4 ∧
     GenOmegaHWTower 2 (by decide) 2 (labelledCollatzRules 3 (by decide) s9RuleList)) ∧
    (checkFinParikhWeakBool 21 wtM3GoE (labelledCollatzRules 3 (by decide) all11RuleList) = true ∧
     (labelledCollatzRules 3 (by decide) all11RuleList).length = 33 ∧
     (filterFinParikhUnoriented 21 wtM3GoE (labelledCollatzRules 3 (by decide) all11RuleList)).length = 32 ∧
     checkFinParikhWeakBool 21 wtM3OmitR3 (labelledCollatzRules 3 (by decide) all11OmitR3List) = true ∧
     (filterFinParikhUnoriented 21 wtM3OmitR3 (labelledCollatzRules 3 (by decide) all11OmitR3List)).length = 25) ∧
    (checkFinParikhWeakBool 28 wtTwoSidedOmitR8
       (twoSidedLabelledCollatzRules 2 (by decide) all11OmitR8List) = true ∧
     (twoSidedLabelledCollatzRules 2 (by decide) all11OmitR8List).length = 40 ∧
     (filterFinParikhUnoriented 28 wtTwoSidedOmitR8
       (twoSidedLabelledCollatzRules 2 (by decide) all11OmitR8List)).length = 26 ∧
     checkFinParikhWeakBool 28 wtTwoSidedOmitR3
       (twoSidedLabelledCollatzRules 2 (by decide) all11OmitR3List) = true ∧
     (filterFinParikhUnoriented 28 wtTwoSidedOmitR3
       (twoSidedLabelledCollatzRules 2 (by decide) all11OmitR3List)).length = 36) := by
  have hb_s9 : checkFin2DHWTowerBool 21 towerS9Mod3_2Level
      (labelledCollatzRules 3 (by decide) s9RuleList) = true := by decide
  refine ⟨⟨hb_s9, by decide,
    checkFin2DHWTowerBool_sound 21 towerS9Mod3_2Level
      (labelledCollatzRules 3 (by decide) s9RuleList) hb_s9⟩,
    ⟨by decide, rfl, by decide, by decide, by decide⟩,
    ⟨by decide, rfl, by decide, by decide, by decide⟩⟩

-- Universal Positive Parikh-Syzygy Collapse Engine (`∀ N, ∀ k : Nat`):

def countFinOcc (N : Nat) (target : Fin N) : List (Fin N) -> Nat
  | [] => 0
  | s :: rest => (if s.val = target.val then 1 else 0) + countFinOcc N target rest

theorem evalFinParikh_eq_sum_count (N : Nat) (wt : Fin N -> Nat) :
    ∀ u : List (Fin N),
      evalFinParikh N wt u = natSumPrefix N (fun s => wt s * countFinOcc N s u) N
  | [] => by
    simp only [evalFinParikh, countFinOcc, Nat.mul_zero]
    exact (natSumPrefix_zero_w6 N N).symm
  | x :: xs => by
    simp only [evalFinParikh, evalFinParikh_eq_sum_count N wt xs]
    have hadd : ∀ k : Nat, k ≤ N ->
        natSumPrefix N (fun s => wt s * countFinOcc N s (x :: xs)) k =
          natSumPrefix N (fun s => if s.val = x.val then wt x else 0) k +
          natSumPrefix N (fun s => wt s * countFinOcc N s xs) k := by
      intro k hk
      induction k with
      | zero => simp [natSumPrefix]
      | succ k' ih =>
        have hk' : k' < N := hk
        simp only [natSumPrefix, hk', dite_true]
        rw [ih (Nat.le_of_lt hk')]
        simp only [countFinOcc]
        by_cases hkx : k' = x.val
        · have hfeq : (⟨k', hk'⟩ : Fin N) = x := Fin.ext hkx
          have h1 : (if k' = x.val then wt x else 0) = wt x :=
            ite_eq_left_iff.mpr (fun hn => False.elim (hn hkx))
          have h2 : (if x.val = k' then 1 else 0) = 1 :=
            ite_eq_left_iff.mpr (fun hn => False.elim (hn hkx.symm))
          rw [h1, h2, hfeq, Nat.mul_add, Nat.mul_one]
          omega
        · have h1 : (if k' = x.val then wt x else 0) = 0 :=
            ite_eq_right_iff.mpr (fun hp => False.elim (hkx hp))
          have h2 : (if x.val = k' then 1 else 0) = 0 :=
            ite_eq_right_iff.mpr (fun hp => False.elim (hkx hp.symm))
          rw [h1, h2, Nat.mul_add, Nat.mul_zero]
          omega
    rw [hadd N (Nat.le_refl N), natSumPrefix_single N x (wt x) N]
    simp [x.isLt]

def weightedSymLhsSum (N : Nat) (s : Fin N) :
    List (List (Fin N) × List (Fin N)) -> List Nat -> Nat
  | [], _ => 0
  | _, [] => 0
  | r :: rs, m :: ms => m * countFinOcc N s r.1 + weightedSymLhsSum N s rs ms

def weightedSymRhsSum (N : Nat) (s : Fin N) :
    List (List (Fin N) × List (Fin N)) -> List Nat -> Nat
  | [], _ => 0
  | _, [] => 0
  | r :: rs, m :: ms => m * countFinOcc N s r.2 + weightedSymRhsSum N s rs ms

def weightedParikhLhs (N : Nat) (wt : Fin N -> Nat) :
    List (List (Fin N) × List (Fin N)) -> List Nat -> Nat
  | [], _ => 0
  | _, [] => 0
  | r :: rs, m :: ms => m * evalFinParikh N wt r.1 + weightedParikhLhs N wt rs ms

def weightedParikhRhs (N : Nat) (wt : Fin N -> Nat) :
    List (List (Fin N) × List (Fin N)) -> List Nat -> Nat
  | [], _ => 0
  | _, [] => 0
  | r :: rs, m :: ms => m * evalFinParikh N wt r.2 + weightedParikhRhs N wt rs ms

theorem weightedParikh_eq_sum_sym (N : Nat) (wt : Fin N -> Nat) :
    ∀ (rules : List (List (Fin N) × List (Fin N))) (mults : List Nat),
      weightedParikhLhs N wt rules mults =
        natSumPrefix N (fun s => wt s * weightedSymLhsSum N s rules mults) N ∧
      weightedParikhRhs N wt rules mults =
        natSumPrefix N (fun s => wt s * weightedSymRhsSum N s rules mults) N
  | [], mults => by
    simp only [weightedParikhLhs, weightedParikhRhs, weightedSymLhsSum, weightedSymRhsSum,
      Nat.mul_zero]
    exact ⟨(natSumPrefix_zero_w6 N N).symm, (natSumPrefix_zero_w6 N N).symm⟩
  | _ :: _, [] => by
    simp only [weightedParikhLhs, weightedParikhRhs, weightedSymLhsSum, weightedSymRhsSum,
      Nat.mul_zero]
    exact ⟨(natSumPrefix_zero_w6 N N).symm, (natSumPrefix_zero_w6 N N).symm⟩
  | r :: rs, m :: ms => by
    rcases weightedParikh_eq_sum_sym N wt rs ms with ⟨ihl, ihr⟩
    have hlin : ∀ (f1 f2 : Fin N -> Nat) (k : Nat),
        natSumPrefix N (fun s => wt s * (m * f1 s + f2 s)) k =
          m * natSumPrefix N (fun s => wt s * f1 s) k +
          natSumPrefix N (fun s => wt s * f2 s) k := by
      intro f1 f2 k
      induction k with
      | zero => simp [natSumPrefix]
      | succ k' ihk =>
        by_cases hk' : k' < N
        · simp only [natSumPrefix, hk', dite_true]
          rw [ihk, Nat.mul_add (wt ⟨k', hk'⟩), Nat.mul_add m]
          have hm_c : wt ⟨k', hk'⟩ * (m * f1 ⟨k', hk'⟩) = m * (wt ⟨k', hk'⟩ * f1 ⟨k', hk'⟩) := by
            rw [← Nat.mul_assoc, Nat.mul_comm (wt ⟨k', hk'⟩) m, Nat.mul_assoc]
          rw [hm_c]; omega
        · simp [natSumPrefix, hk', ihk]
    refine ⟨?_, ?_⟩
    · simp only [weightedParikhLhs, evalFinParikh_eq_sum_count N wt r.1, ihl, weightedSymLhsSum]
      exact (hlin _ _ N).symm
    · simp only [weightedParikhRhs, evalFinParikh_eq_sum_count N wt r.2, ihr, weightedSymRhsSum]
      exact (hlin _ _ N).symm

def checkAllPosNatList : List Nat -> Bool
  | [] => true
  | m :: ms => decide (m ≥ 1) && checkAllPosNatList ms

def checkSymSyzygyUpTo (N : Nat)
    (rules : List (List (Fin N) × List (Fin N))) (mults : List Nat) :
    (k : Nat) -> k ≤ N -> Bool
  | 0, _ => true
  | k + 1, hk =>
    decide (weightedSymLhsSum N ⟨k, hk⟩ rules mults ≤ weightedSymRhsSum N ⟨k, hk⟩ rules mults) &&
    checkSymSyzygyUpTo N rules mults k (Nat.le_of_lt hk)

def checkPositiveParikhSyzygyBool (N : Nat)
    (rules : List (List (Fin N) × List (Fin N))) (mults : List Nat) : Bool :=
  decide (rules.length ≥ 1) &&
  decide (rules.length = mults.length) &&
  checkAllPosNatList mults &&
  checkSymSyzygyUpTo N rules mults N (Nat.le_refl N)

theorem checkSymSyzygyUpTo_sound (N : Nat)
    (rules : List (List (Fin N) × List (Fin N))) (mults : List Nat) :
    ∀ (k : Nat) (hk : k ≤ N),
      checkSymSyzygyUpTo N rules mults k hk = true ->
      ∀ s : Fin N, s.val < k ->
        weightedSymLhsSum N s rules mults ≤ weightedSymRhsSum N s rules mults
  | 0, _, _, _, hs => by omega
  | k + 1, hk, hb, s, hs => by
    unfold checkSymSyzygyUpTo at hb
    rcases bool_and_split hb with ⟨hcur, hrest⟩
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hs) with hsk | hslt
    · have hsf : s = ⟨k, hk⟩ := Fin.ext hsk
      exact hsf.symm ▸ of_decide_eq_true hcur
    · exact checkSymSyzygyUpTo_sound N rules mults k (Nat.le_of_lt hk) hrest s hslt

theorem weightedParikh_ge_of_weak (N : Nat) (wt : Fin N -> Nat) :
    ∀ (rules : List (List (Fin N) × List (Fin N))) (mults : List Nat),
      (∀ r ∈ rules, evalFinParikh N wt r.1 ≥ evalFinParikh N wt r.2) ->
      weightedParikhLhs N wt rules mults ≥ weightedParikhRhs N wt rules mults
  | [], _ => fun _ => by simp [weightedParikhLhs, weightedParikhRhs]
  | _ :: _, [] => fun _ => by simp [weightedParikhLhs, weightedParikhRhs]
  | r0 :: rs, m0 :: ms => fun hweak => by
    simp only [weightedParikhLhs, weightedParikhRhs]
    have hm0 := Nat.mul_le_mul_left m0 (hweak r0 List.mem_cons_self)
    have hrest := weightedParikh_ge_of_weak N wt rs ms
      (fun rx hrx => hweak rx (List.mem_cons_of_mem r0 hrx))
    omega

theorem weightedParikh_strict_of_mem (N : Nat) (wt : Fin N -> Nat) :
    ∀ (rules : List (List (Fin N) × List (Fin N))) (mults : List Nat),
      rules.length = mults.length ->
      checkAllPosNatList mults = true ->
      (∀ r ∈ rules, evalFinParikh N wt r.1 ≥ evalFinParikh N wt r.2) ->
      weightedParikhLhs N wt rules mults ≤ weightedParikhRhs N wt rules mults ->
      ∀ r ∈ rules, evalFinParikh N wt r.1 = evalFinParikh N wt r.2
  | [], [], _, _, _, _, _, hm => by cases hm
  | [], _ :: _, hlen, _, _, _, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _, _, _, _ => by simp at hlen
  | r0 :: rs, m0 :: ms, hlen, hpos, hweak, htot_le, r, hm => by
    unfold checkAllPosNatList at hpos
    rcases bool_and_split hpos with ⟨hm0_b, hpos_ms⟩
    have hm0_pos : m0 ≥ 1 := of_decide_eq_true hm0_b
    have hlen' : rs.length = ms.length := by simp at hlen; exact hlen
    have hge_rs := weightedParikh_ge_of_weak N wt rs ms
      (fun rx hrx => hweak rx (List.mem_cons_of_mem r0 hrx))
    simp only [weightedParikhLhs, weightedParikhRhs] at htot_le
    have hw0 := hweak r0 List.mem_cons_self
    have hm0_ge : m0 * evalFinParikh N wt r0.1 ≥ m0 * evalFinParikh N wt r0.2 :=
      Nat.mul_le_mul_left m0 hw0
    have hm0_eq : m0 * evalFinParikh N wt r0.1 = m0 * evalFinParikh N wt r0.2 := by omega
    have hr0_eq : evalFinParikh N wt r0.1 = evalFinParikh N wt r0.2 :=
      Nat.le_antisymm
        (nat_mul_le_cancel_left_w5 m0 _ _ hm0_pos (by omega))
        hw0
    cases hm with
    | head => exact hr0_eq
    | tail _ hrs =>
      exact weightedParikh_strict_of_mem N wt rs ms hlen' hpos_ms
        (fun rx hrx => hweak rx (List.mem_cons_of_mem r0 hrx))
        (by omega) r hrs

/--
  Theorem W10.1d (`positive_parikh_syzygy_blocks_all_omega_towers`, `zero custom axioms`):
  Universal Positive Parikh-Syzygy Impossibility Principle (`∀ N, ∀ k : Nat`):
  Whenever `checkPositiveParikhSyzygyBool N rules mults = true`:
  1. Every nonnegative symbol weight `wt : Fin N -> Nat` weakly orienting `rules` satisfies
     `evalFinParikh N wt r.1 = evalFinParikh N wt r.2` identically across ALL `r ∈ rules`!
  2. For EVERY finite tower height `k : Nat`, NO `ω^k` Parikh rule-removal tower can terminate `rules`
     (`¬ GenOmegaParikhTower N k rules`)!
-/
theorem positive_parikh_syzygy_blocks_all_omega_towers
    (N : Nat) (rules : List (List (Fin N) × List (Fin N))) (mults : List Nat)
    (hsyz : checkPositiveParikhSyzygyBool N rules mults = true) :
    (∀ wt : Fin N -> Nat,
      (∀ r ∈ rules, evalFinParikh N wt r.1 ≥ evalFinParikh N wt r.2) ->
      ∀ r ∈ rules, evalFinParikh N wt r.1 = evalFinParikh N wt r.2) ∧
    (∀ k : Nat, ¬ GenOmegaParikhTower N k rules) := by
  unfold checkPositiveParikhSyzygyBool at hsyz
  rcases bool_and_split hsyz with ⟨hb1, hsym⟩
  rcases bool_and_split hb1 with ⟨hb2, hpos⟩
  rcases bool_and_split hb2 with ⟨hlen_ge1, hlen_eq⟩
  have hne : rules.length ≥ 1 := of_decide_eq_true hlen_ge1
  have hlen : rules.length = mults.length := of_decide_eq_true hlen_eq
  have hsym_le := checkSymSyzygyUpTo_sound N rules mults N (Nat.le_refl N) hsym
  have heq_all : ∀ wt : Fin N -> Nat,
      (∀ r ∈ rules, evalFinParikh N wt r.1 ≥ evalFinParikh N wt r.2) ->
      ∀ r ∈ rules, evalFinParikh N wt r.1 = evalFinParikh N wt r.2 := by
    intro wt hweak
    rcases weightedParikh_eq_sum_sym N wt rules mults with ⟨hl_sum, hr_sum⟩
    have htot_le : weightedParikhLhs N wt rules mults ≤ weightedParikhRhs N wt rules mults := by
      rw [hl_sum, hr_sum]
      exact natSumPrefix_mono_w5 N _ _
        (fun s => Nat.mul_le_mul_left (wt s) (hsym_le s s.isLt)) N
    exact weightedParikh_strict_of_mem N wt rules mults hlen hpos hweak htot_le
  refine ⟨heq_all, ?_⟩
  cases rules with
  | nil => simp at hne
  | cons r0 rs =>
    have h_imp : ∀ (k : Nat) (cur : List (List (Fin N) × List (Fin N))),
        (∀ r ∈ r0 :: rs, r ∈ cur) -> ¬ GenOmegaParikhTower N k cur := by
      intro k
      induction k with
      | zero =>
        intro cur hsub h0
        rw [GenOmegaParikhTower] at h0; subst h0
        exact List.not_mem_nil (hsub r0 List.mem_cons_self)
      | succ k' ih =>
        intro cur hsub hsucc
        rcases hsucc with rfl | ⟨rem, wt, hweak, hkeep, hrem⟩
        · exact List.not_mem_nil (hsub r0 List.mem_cons_self)
        · have heq := heq_all wt (fun r hr => hweak r (hsub r hr))
          exact ih rem
            (fun r hr => hkeep r (hsub r hr) (by rw [heq r hr]; exact Nat.lt_irrefl _)) hrem
    intro k
    exact h_imp k (r0 :: rs) (fun _ hr => hr)

def syzM2OmitR8 : List Nat := [7, 1, 7, 7, 2, 1, 1, 3, 4, 3, 1, 2, 4, 4, 1, 1, 1, 1, 4, 4]
def syzM2OmitR3 : List Nat := [5, 2, 18, 5, 2, 6, 13, 2, 2, 3, 7, 10, 2, 10, 2, 2, 2, 2, 5, 5]
def syzM2All11  : List Nat := [18, 6, 35, 18, 10, 6, 6, 12, 23, 12, 6, 7, 21, 24, 6, 21, 6, 6, 7, 7, 10, 10]
def syzM3Core32 : List Nat :=
  [2, 12, 2, 20, 10, 2, 7, 2, 7, 4, 5, 12, 7, 4, 2, 4,
   4, 2, 22, 3, 2, 14, 4, 2, 2, 2, 3, 3, 3, 4, 4, 4]
def syzM3OmitR8Core29 : List Nat :=
  [6, 72, 6, 72, 66, 19, 104, 6, 7, 44, 72, 94, 7, 46, 7,
   95, 7, 8, 78, 69, 6, 6, 6, 7, 7, 7, 29, 29, 29]
def syzTwoSidedOmitR8Core26 : List Nat :=
  [45, 45, 23, 45, 23, 45, 71, 20, 25, 71, 25, 25, 23,
   23, 71, 25, 27, 48, 71, 94, 23, 23, 22, 22, 23, 23]
def syzTwoSidedAll11 : List Nat :=
  [377, 120, 377, 120, 978, 377, 978, 377, 605, 120, 227, 672, 128, 295, 442,
   326, 1010, 626, 293, 298, 120, 566, 122, 194, 397, 1051, 881, 598, 995, 838,
   120, 672, 194, 194, 257, 257, 293, 293, 126, 126, 178, 178, 147, 147]

/--
  Theorem W10.1e (`labelled_swap_parikh_syzygy_barriers`, `zero custom axioms`):
  Universal `∀ k : Nat` Labelled Parikh-Syzygy Impossibility Barriers When `{R3, R8}` Re-Enter:
  1. At `M = 2` (`Fin 14`), re-introducing EITHER `R3` (`omit R8`, `20/20`) OR `R8` (`omit R3`, `20/20`)
     OR both (`all11`, `22/22`) locks 100% of rules into a strictly positive Parikh syzygy,
     refuting `GenOmegaParikhTower 14 k` for ALL `k : Nat`!
  2. At `M = 3` (`Fin 21`), after removing `R2_1`, both the `32`-rule core of `all11` and the
     `29`-rule core of `omit R8` satisfy strictly positive Parikh syzygies (`¬ GenOmegaParikhTower 21 k`)!
  3. Under Two-Sided `(semL2 × collatzSemMod 2)` (`Fin 28`), full `all11` (`44/44`) and the `26`-rule
     post-Level-1 core of `omit R8` satisfy strictly positive Parikh syzygies (`¬ GenOmegaParikhTower 28 k`)!
-/
theorem labelled_swap_parikh_syzygy_barriers :
    let m2_or8 := labelledCollatzRules 2 (by decide) all11OmitR8List
    let m2_or3 := labelledCollatzRules 2 (by decide) all11OmitR3List
    let m2_all := labelledCollatzRules 2 (by decide) all11RuleList
    let m3_c32 := filterFinParikhUnoriented 21 wtM3GoE (labelledCollatzRules 3 (by decide) all11RuleList)
    let m3_c29 := filterFinParikhUnoriented 21 wtM3GoE (labelledCollatzRules 3 (by decide) all11OmitR8List)
    let ts_c26 := filterFinParikhUnoriented 28 wtTwoSidedOmitR8
                    (twoSidedLabelledCollatzRules 2 (by decide) all11OmitR8List)
    let ts_all := twoSidedLabelledCollatzRules 2 (by decide) all11RuleList
    ∀ k : Nat,
      ¬ GenOmegaParikhTower 14 k m2_or8 ∧
      ¬ GenOmegaParikhTower 14 k m2_or3 ∧
      ¬ GenOmegaParikhTower 14 k m2_all ∧
      ¬ GenOmegaParikhTower 21 k m3_c32 ∧
      ¬ GenOmegaParikhTower 21 k m3_c29 ∧
      ¬ GenOmegaParikhTower 28 k ts_c26 ∧
      ¬ GenOmegaParikhTower 28 k ts_all := by
  dsimp only
  have h1 := (positive_parikh_syzygy_blocks_all_omega_towers 14
    (labelledCollatzRules 2 (by decide) all11OmitR8List) syzM2OmitR8 (by decide)).2
  have h2 := (positive_parikh_syzygy_blocks_all_omega_towers 14
    (labelledCollatzRules 2 (by decide) all11OmitR3List) syzM2OmitR3 (by decide)).2
  have h3 := (positive_parikh_syzygy_blocks_all_omega_towers 14
    (labelledCollatzRules 2 (by decide) all11RuleList) syzM2All11 (by decide)).2
  have h4 := (positive_parikh_syzygy_blocks_all_omega_towers 21
    (filterFinParikhUnoriented 21 wtM3GoE (labelledCollatzRules 3 (by decide) all11RuleList))
    syzM3Core32 (by decide)).2
  have h5 := (positive_parikh_syzygy_blocks_all_omega_towers 21
    (filterFinParikhUnoriented 21 wtM3GoE (labelledCollatzRules 3 (by decide) all11OmitR8List))
    syzM3OmitR8Core29 (by decide)).2
  have h6 := (positive_parikh_syzygy_blocks_all_omega_towers 28
    (filterFinParikhUnoriented 28 wtTwoSidedOmitR8
      (twoSidedLabelledCollatzRules 2 (by decide) all11OmitR8List))
    syzTwoSidedOmitR8Core26 (by decide)).2
  have h7 := (positive_parikh_syzygy_blocks_all_omega_towers 28
    (twoSidedLabelledCollatzRules 2 (by decide) all11RuleList)
    syzTwoSidedAll11 (by decide)).2
  intro k
  exact ⟨h1 k, h2 k, h3 k, h4 k, h5 k, h6 k, h7 k⟩

-- ============================================================================
-- SECTION 2: Front B (Branches P3.4 & P3.3) — Universal 1-Block Coprime-Order
--            Prime-Divisor Law, Gauss Lemma + Mod-24 `{11, 13}` Exclusion, &
--            Exact `6 x 6` Single-Base / Two-Base Schneider–Laurent Zero Locus
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Section 2A: Constructive Fermat's Little Theorem, Minimal Multiplicative Order,
--             Universal 1-Block Coprime-Order Prime Law, & Mod-24 Exclusion
-- ----------------------------------------------------------------------------

theorem ite_true_of_w10 {α : Type} {c : Prop} [Decidable c] (hc : c) (a b : α) :
    (if c then a else b) = a :=
  ite_eq_left_iff.mpr (fun hn => False.elim (hn hc))

theorem ite_false_of_w10 {α : Type} {c : Prop} [Decidable c] (hnc : ¬ c) (a b : α) :
    (if c then a else b) = b :=
  ite_eq_right_iff.mpr (fun hp => False.elim (hnc hp))

theorem cancel_mul_mod_prime (q b x y : Nat)
    (hq : IsPrimeNat q) (hnd : ¬ (q ∣ b)) (heq : (b * x) % q = (b * y) % q) :
    x % q = y % q := by
  have hq_pos : 0 < q := by have := hq.1; omega
  let rx := x % q
  let ry := y % q
  have hrx_lt : rx < q := Nat.mod_lt x hq_pos
  have hry_lt : ry < q := Nat.mod_lt y hq_pos
  have hbx : (b * rx) % q = (b * x) % q := by
    rw [Nat.mul_mod b rx q, Nat.mod_mod, ← Nat.mul_mod]
  have hby : (b * ry) % q = (b * y) % q := by
    rw [Nat.mul_mod b ry q, Nat.mod_mod, ← Nat.mul_mod]
  have hbr_eq : (b * rx) % q = (b * ry) % q := hbx.trans (heq.trans hby.symm)
  have hsub_zero : ∀ u v : Nat, v ≤ u -> u - v < q -> (b * u) % q = (b * v) % q -> u = v := by
    intro u v hle hlt hm_eq
    have hsp : b * u = b * (u - v) + b * v := by
      rw [← Nat.mul_add, show u - v + v = u by omega]
    have hmod0 : (b * (u - v)) % q = 0 := by
      have hadd_mod : (b * u) % q = ((b * (u - v)) % q + (b * v) % q) % q := by
        rw [hsp, Nat.add_mod]
      rw [hm_eq] at hadd_mod
      have hr1 : (b * (u - v)) % q < q := Nat.mod_lt _ hq_pos
      have hr2 : (b * v) % q < q := Nat.mod_lt _ hq_pos
      by_cases hz : (b * (u - v)) % q = 0
      · exact hz
      · by_cases hlt_q : (b * (u - v)) % q + (b * v) % q < q
        · rw [Nat.mod_eq_of_lt hlt_q] at hadd_mod; omega
        · have hsub_q : ((b * (u - v)) % q + (b * v) % q) % q =
              (b * (u - v)) % q + (b * v) % q - q := by
            have heq_q : (b * (u - v)) % q + (b * v) % q =
                ((b * (u - v)) % q + (b * v) % q - q) + q * 1 := by omega
            conv => lhs; arg 1; rw [heq_q]
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
          rw [hsub_q] at hadd_mod; omega
    have hdvd : q ∣ (b * (u - v)) := Nat.dvd_of_mod_eq_zero hmod0
    rcases gauss_euclid_lemma q b (u - v) hq hdvd with hqb | hquv
    · exact False.elim (hnd hqb)
    · rcases hquv with ⟨c, hc⟩
      cases c with
      | zero => simp at hc; omega
      | succ c' =>
        have hge : q ≤ q * (c' + 1) := by simpa using Nat.mul_le_mul_left q (by omega : 1 ≤ c' + 1)
        omega
  by_cases hle : ry ≤ rx
  · exact hsub_zero rx ry hle (by omega) hbr_eq
  · exact (hsub_zero ry rx (by omega) (by omega) hbr_eq.symm).symm

def natProdRange : Nat -> (Nat -> Nat) -> Nat
  | 0, _ => 1
  | k + 1, f => f k * natProdRange k f

theorem natProdRange_congr (f g : Nat -> Nat) :
    ∀ (k : Nat), (∀ i : Nat, i < k -> f i = g i) -> natProdRange k f = natProdRange k g
  | 0, _ => rfl
  | k + 1, heq => by
    simp only [natProdRange]
    rw [heq k (by omega), natProdRange_congr f g k (fun i hi => heq i (by omega))]

theorem natProdRange_replace_one (v : Nat) (f : Nat -> Nat) :
    ∀ (k i0 : Nat), i0 < k ->
      f i0 * natProdRange k (fun t => if t = i0 then v else f t) = v * natProdRange k f
  | 0, _, hi0 => by omega
  | k + 1, i0, hi0 => by
    simp only [natProdRange]
    by_cases hik : i0 = k
    · subst hik
      simp only [ite_true]
      have hcong : natProdRange i0 (fun t => if t = i0 then v else f t) = natProdRange i0 f :=
        natProdRange_congr _ _ i0 (fun t ht => by simp [show t ≠ i0 by omega])
      rw [hcong, ← Nat.mul_assoc (f i0) v, Nat.mul_comm (f i0) v, Nat.mul_assoc]
    · have hi0_lt : i0 < k := by omega
      simp only [show k ≠ i0 by omega, ite_false]
      rw [← Nat.mul_assoc (f i0) (f k), Nat.mul_comm (f i0) (f k), Nat.mul_assoc (f k),
          natProdRange_replace_one v f k i0 hi0_lt,
          ← Nat.mul_assoc (f k) v, Nat.mul_comm (f k) v, Nat.mul_assoc]

/-- Any bijection on `{0, ..., n - 1}` into `{1, ..., n}` has product `natFact n` (choice-free). -/
theorem natProdRange_inj_eq_fact :
    ∀ (n : Nat) (f : Nat -> Nat),
      (∀ i : Nat, i < n -> 1 ≤ f i ∧ f i ≤ n) ->
      (∀ i j : Nat, i < n -> j < n -> f i = f j -> i = j) ->
      natProdRange n f = natFact n
  | 0, _, _, _ => rfl
  | m + 1, f, hbounds, hinj => by
    let g0 : Nat -> Nat := fun i => f i - 1
    have hg0_lt : ∀ i : Nat, i < m + 1 -> g0 i < m + 1 := by
      intro i hi; have hb := hbounds i hi; dsimp [g0]; omega
    have hg0_inj : ∀ i j : Nat, i < m + 1 -> j < m + 1 -> g0 i = g0 j -> i = j := by
      intro i j hi hj hge
      have hb1 := hbounds i hi
      have hb2 := hbounds j hj
      exact hinj i j hi hj (by dsimp [g0] at hge; omega)
    rcases nat_fin_inj_implies_surj (m + 1) g0 hg0_lt hg0_inj m (by omega) with ⟨i0, hi0_lt, hgi0⟩
    have hfi0 : f i0 = m + 1 := by
      have hb := hbounds i0 hi0_lt; dsimp [g0] at hgi0; omega
    by_cases hi0_m : i0 = m
    · subst hi0_m
      simp only [natProdRange, natFact, hfi0]
      have hf_sub : ∀ i : Nat, i < i0 -> 1 ≤ f i ∧ f i ≤ i0 := by
        intro i hi
        rcases hbounds i (by omega) with ⟨hlo, hhi⟩
        have hne : f i ≠ i0 + 1 := fun he => by
          have hij := hinj i i0 (by omega) (by omega) (he.trans hfi0.symm)
          omega
        exact ⟨hlo, by omega⟩
      rw [natProdRange_inj_eq_fact i0 f hf_sub (fun i j hi hj => hinj i j (by omega) (by omega))]
    · have hi0_lt_m : i0 < m := by omega
      let f_swap : Nat -> Nat := fun t => if t = i0 then f m else f t
      have hswap_bounds : ∀ t : Nat, t < m -> 1 ≤ f_swap t ∧ f_swap t ≤ m := by
        intro t ht
        dsimp [f_swap]
        by_cases hti : t = i0
        · simp only [hti, ite_true]
          rcases hbounds m (by omega) with ⟨hlo, hhi⟩
          have hne : f m ≠ m + 1 := fun he => hi0_m (hinj i0 m hi0_lt (by omega) (hfi0.trans he.symm))
          exact ⟨hlo, by omega⟩
        · simp only [hti, ite_false]
          rcases hbounds t (by omega) with ⟨hlo, hhi⟩
          have hne : f t ≠ m + 1 := fun he => hti (hinj t i0 (by omega) hi0_lt (he.trans hfi0.symm))
          exact ⟨hlo, by omega⟩
      have hswap_inj : ∀ t1 t2 : Nat, t1 < m -> t2 < m -> f_swap t1 = f_swap t2 -> t1 = t2 := by
        intro t1 t2 ht1 ht2 heq
        dsimp [f_swap] at heq
        by_cases h1 : t1 = i0 <;> by_cases h2 : t2 = i0
        · omega
        · simp only [h1, h2, ite_true, ite_false] at heq
          exact False.elim (by have := hinj m t2 (by omega) (by omega) heq; omega)
        · simp only [h1, h2, ite_true, ite_false] at heq
          exact False.elim (by have := hinj t1 m (by omega) (by omega) heq; omega)
        · simp only [h1, h2, ite_false] at heq
          exact hinj t1 t2 (by omega) (by omega) heq
      have hrep := natProdRange_replace_one (f m) f m i0 hi0_lt_m
      change f i0 * natProdRange m f_swap = natProdRange (m + 1) f at hrep
      rw [← hrep, hfi0, natProdRange_inj_eq_fact m f_swap hswap_bounds hswap_inj]
      rfl

theorem prime_not_dvd_natFact (q : Nat) (hq : IsPrimeNat q) :
    ∀ k : Nat, k < q -> ¬ (q ∣ natFact k)
  | 0, _, hdvd => by
    have h1 := Nat.eq_one_of_dvd_one hdvd; have := hq.1; omega
  | k + 1, hlt, hdvd => by
    simp only [natFact] at hdvd
    rcases gauss_euclid_lemma q (k + 1) (natFact k) hq hdvd with hqk | hqf
    · rcases hqk with ⟨c, hc⟩
      cases c with
      | zero => simp at hc
      | succ c' =>
        have hge : q ≤ q * (c' + 1) := by simpa using Nat.mul_le_mul_left q (by omega : 1 ≤ c' + 1)
        omega
    · exact prime_not_dvd_natFact q hq k (by omega) hqf

theorem natProdRange_mul_mod_eq_pow_fact (q b : Nat) :
    ∀ k : Nat, natProdRange k (fun i => (b * (i + 1)) % q) % q = (b ^ k * natFact k) % q
  | 0 => by simp [natProdRange, natFact]
  | k + 1 => by
    simp only [natProdRange, natFact]
    calc
      (((b * (k + 1)) % q) * natProdRange k (fun i => (b * (i + 1)) % q)) % q
          = ((((b * (k + 1)) % q) % q) * (natProdRange k (fun i => (b * (i + 1)) % q) % q)) % q :=
            Nat.mul_mod _ _ q
      _ = (((b * (k + 1)) % q) * ((b ^ k * natFact k) % q)) % q := by
            rw [Nat.mod_mod, natProdRange_mul_mod_eq_pow_fact q b k]
      _ = ((b * (k + 1)) * (b ^ k * natFact k)) % q := (Nat.mul_mod _ _ q).symm
      _ = (b ^ (k + 1) * ((k + 1) * natFact k)) % q := by
            apply congrArg (· % q)
            rw [Nat.pow_succ b k, Nat.mul_comm (b ^ k) b,
                Nat.mul_assoc b (k + 1), ← Nat.mul_assoc (k + 1) (b ^ k),
                Nat.mul_comm (k + 1) (b ^ k), Nat.mul_assoc (b ^ k) (k + 1),
                ← Nat.mul_assoc b (b ^ k)]

/-- Fermat's Little Theorem in pure `Nat` (`choice-free, zero custom axioms`). -/
theorem fermat_little_mod_prime (q b : Nat) (hq : IsPrimeNat q) (hnd : ¬ (q ∣ b)) :
    b ^ (q - 1) % q = 1 := by
  have hq2 := hq.1
  let f : Nat -> Nat := fun i => (b * (i + 1)) % q
  have hf_bounds : ∀ i : Nat, i < q - 1 -> 1 ≤ f i ∧ f i ≤ q - 1 := by
    intro i hi
    dsimp [f]
    have hlt : (b * (i + 1)) % q < q := Nat.mod_lt _ (by omega)
    have hnz : (b * (i + 1)) % q ≠ 0 := by
      intro hz
      rcases gauss_euclid_lemma q b (i + 1) hq (Nat.dvd_of_mod_eq_zero hz) with hqb | hqi
      · exact hnd hqb
      · rcases hqi with ⟨c, hc⟩
        cases c with
        | zero => simp at hc
        | succ c' =>
          have hge : q ≤ q * (c' + 1) := by simpa using Nat.mul_le_mul_left q (by omega : 1 ≤ c' + 1)
          omega
    exact ⟨by omega, by omega⟩
  have hf_inj : ∀ i j : Nat, i < q - 1 -> j < q - 1 -> f i = f j -> i = j := by
    intro i j hi hj heq
    have hc := cancel_mul_mod_prime q b (i + 1) (j + 1) hq hnd heq
    rw [Nat.mod_eq_of_lt (by omega : i + 1 < q), Nat.mod_eq_of_lt (by omega : j + 1 < q)] at hc
    omega
  have hprod_eq := natProdRange_inj_eq_fact (q - 1) f hf_bounds hf_inj
  have hmod_eq := natProdRange_mul_mod_eq_pow_fact q b (q - 1)
  rw [hprod_eq] at hmod_eq
  have hcomm : (b ^ (q - 1) * natFact (q - 1)) % q = (natFact (q - 1) * b ^ (q - 1)) % q := by
    rw [Nat.mul_comm]
  have hrhs : natFact (q - 1) % q = (natFact (q - 1) * 1) % q := by rw [Nat.mul_one]
  have hcanc := cancel_mul_mod_prime q (natFact (q - 1)) (b ^ (q - 1)) 1 hq
    (prime_not_dvd_natFact q hq (q - 1) (by omega))
    (hcomm.symm.trans (hmod_eq.symm.trans hrhs))
  rwa [Nat.mod_eq_of_lt (by omega : 1 < q)] at hcanc

def findMinOrderAux (q b : Nat) : Nat -> Nat -> Nat
  | 0, _ => q - 1
  | fuel + 1, d =>
    if d ≥ q - 1 then q - 1
    else if b ^ d % q = 1 then d
    else findMinOrderAux q b fuel (d + 1)

theorem findMinOrderAux_spec (q b : Nat) (hq : IsPrimeNat q) (hnd : ¬ (q ∣ b)) :
    ∀ (fuel d : Nat),
      1 ≤ d -> d ≤ q - 1 -> q - 1 ≤ d + fuel ->
      (∀ r : Nat, 1 ≤ r -> r < d -> b ^ r % q ≠ 1) ->
      let ord := findMinOrderAux q b fuel d
      IsExactMultOrderMod q b ord ∧ ord ∣ (q - 1)
  | 0, d, hd1, hd_le, hfuel, hno => by
    have hd_eq : d = q - 1 := by omega
    subst hd_eq
    have hflt := fermat_little_mod_prime q b hq hnd
    have hord : IsExactMultOrderMod q b (q - 1) :=
      ⟨hq.1, hd1, hflt, fun r hr1 => hno r.val hr1 r.isLt⟩
    exact ⟨hord, Nat.dvd_refl (q - 1)⟩
  | fuel + 1, d, hd1, hd_le, hfuel, hno => by
    dsimp only
    unfold findMinOrderAux
    by_cases hge : d ≥ q - 1
    · have hd_eq : d = q - 1 := by omega
      simp only [hge, ite_true]
      subst hd_eq
      have hflt := fermat_little_mod_prime q b hq hnd
      exact ⟨⟨hq.1, hd1, hflt, fun r hr1 => hno r.val hr1 r.isLt⟩, Nat.dvd_refl (q - 1)⟩
    · simp only [hge, ite_false]
      by_cases hp1 : b ^ d % q = 1
      · simp only [hp1, ite_true]
        have hord : IsExactMultOrderMod q b d :=
          ⟨hq.1, hd1, hp1, fun r hr1 => hno r.val hr1 r.isLt⟩
        exact ⟨hord, exactMultOrderMod_dvd_of_pow_eq_one q b d (q - 1) hord
          (fermat_little_mod_prime q b hq hnd)⟩
      · simp only [hp1, ite_false]
        apply findMinOrderAux_spec q b hq hnd fuel (d + 1) (by omega) (by omega) (by omega)
        intro r hr1 hr_lt
        by_cases hrd : r = d
        · subst hrd; exact hp1
        · exact hno r hr1 (by omega)

/-- Constructive existence of exact multiplicative order `ord_q(b) ∣ (q - 1)` (`choice-free`). -/
theorem exists_exact_mult_order_mod_prime (q b : Nat) (hq : IsPrimeNat q) (hnd : ¬ (q ∣ b)) :
    ∃ d : Nat, IsExactMultOrderMod q b d ∧ d ∣ (q - 1) := by
  have hq2 := hq.1
  exact ⟨findMinOrderAux q b (q - 1) 1,
    findMinOrderAux_spec q b hq hnd (q - 1) 1 (Nat.le_refl 1) (by omega) (by omega)
      (fun _ hr1 hlt => by omega)⟩

/-- Bezout-free subtraction proof of Euclid's coprime divisibility (`gcd a b = 1 -> a ∣ b*c -> a ∣ c`). -/
theorem coprime_dvd_of_dvd_mul_aux :
    ∀ (fuel a b c : Nat),
      a + b ≤ fuel -> Nat.gcd a b = 1 -> a ∣ (b * c) -> a ∣ c
  | 0, a, b, c, hfuel, hgcd, _ => by
    have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    subst ha0; subst hb0; simp at hgcd
  | fuel + 1, a, b, c, hfuel, hgcd, hdvd => by
    by_cases ha0 : a = 0
    · subst ha0; rw [Nat.gcd_zero_left] at hgcd; subst hgcd; rw [Nat.one_mul] at hdvd; exact hdvd
    · by_cases ha1 : a = 1
      · subst ha1; exact Nat.one_dvd c
      · by_cases hb0 : b = 0
        · subst hb0; rw [Nat.gcd_zero_right] at hgcd; omega
        · by_cases hab : a ≤ b
          · have hb_sp : b = (b - a) + a := by omega
            have hgcd' : Nat.gcd a (b - a) = 1 := by
              have hg : Nat.gcd a b = Nat.gcd a (b - a) := by
                conv => lhs; rw [hb_sp]
                exact Nat.gcd_add_self_right a (b - a)
              rwa [hg] at hgcd
            rcases hdvd with ⟨k, hk⟩
            rw [hb_sp, Nat.add_mul] at hk
            have hk_ge : c ≤ k := by
              by_cases hck : c ≤ k
              · exact hck
              · have hm := Nat.mul_lt_mul_of_pos_left (by omega : k < c) (by omega : 0 < a)
                generalize (b - a) * c = BAC at hk
                omega
            have hdvd' : a ∣ ((b - a) * c) := ⟨k - c, by rw [Nat.mul_sub_left_distrib]; omega⟩
            exact coprime_dvd_of_dvd_mul_aux fuel a (b - a) c (by omega) hgcd' hdvd'
          · -- `1 ≤ b < a`:
            have ha_sp : a = (a - b) + b := by omega
            have hgcd' : Nat.gcd (a - b) b = 1 := by
              have hg : Nat.gcd a b = Nat.gcd (a - b) b := by
                conv => lhs; rw [ha_sp]
                rw [Nat.gcd_comm, Nat.gcd_add_self_right, Nat.gcd_comm]
              rwa [hg] at hgcd
            rcases hdvd with ⟨k, hk⟩
            have hk_le_c : k ≤ c := by
              by_cases hkc : k ≤ c
              · exact hkc
              · have hc_pos : 0 < c := by
                  cases c with
                  | zero =>
                    rw [Nat.mul_zero] at hk
                    rcases Nat.mul_eq_zero.mp hk.symm with rfl | rfl <;> omega
                  | succ _ => omega
                have hm1 : b * c < a * c := Nat.mul_lt_mul_of_pos_right (by omega) hc_pos
                have hm2 : a * c < a * k := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
                exact False.elim (Nat.ne_of_lt (Nat.lt_trans hm1 hm2) hk)
            have hsub_eq : b * (c - k) = (a - b) * k := by
              rw [Nat.mul_sub_left_distrib]
              rw [ha_sp, Nat.add_mul] at hk
              omega
            have hdvd' : (a - b) ∣ (b * (c - k)) := ⟨k, hsub_eq⟩
            rcases coprime_dvd_of_dvd_mul_aux fuel (a - b) b (c - k) (by omega) hgcd' hdvd' with
              ⟨m, hm⟩
            have hk_eq : k = b * m := by
              rw [hm, ← Nat.mul_assoc b (a - b) m, Nat.mul_comm b (a - b), Nat.mul_assoc] at hsub_eq
              exact Nat.le_antisymm
                (nat_mul_le_cancel_left_w5 (a - b) k (b * m) (by omega) (by omega))
                (nat_mul_le_cancel_left_w5 (a - b) (b * m) k (by omega) (by omega))
            refine ⟨m, ?_⟩
            have hc_sp : c = (c - k) + k := by omega
            rw [hc_sp, hm, hk_eq, ← Nat.add_mul, ← ha_sp]

theorem coprime_mul_dvd_of_dvd (a b n : Nat) (hgcd : Nat.gcd a b = 1)
    (ha : a ∣ n) (hb : b ∣ n) : (a * b) ∣ n := by
  rcases ha with ⟨k, rfl⟩
  have hbk : b ∣ (a * k) := hb
  rw [Nat.gcd_comm] at hgcd
  rcases coprime_dvd_of_dvd_mul_aux (b + a) b a k (Nat.le_refl _) hgcd hbk with ⟨m, rfl⟩
  exact ⟨m, (Nat.mul_assoc a b m).symm⟩

/--
  Theorem W10.2a (`one_block_all_prime_divisors_coprime_order_and_totient`, `choice-free, zero custom axioms`):
  Universal 1-Block Coprime-Order Prime-Divisor & Subgroup-Product Law:
  1. For EVERY odd prime `q ≥ 5` (`IsPrimeNat q`), BOTH `2` and `3 / 2 (mod q)` (`ratio32Mod q`)
     possess unique constructive minimal multiplicative orders `d2, d32 ≥ 1` dividing `q - 1`,
     and whenever `Nat.gcd d2 d32 = 1`, their product divides `q - 1` (`(d2 * d32) ∣ (q - 1)`).
  2. On ANY nontrivial 1-block `Z^+` cycle `(2^(w1 + a1) - 3^w1) * q0 = 2^a1 - 1`
     (`w1 ≥ 2, a1 ≥ 1, q0 ≥ 1, 3^w1 < 2^(w1 + a1)`):
     - `D := 2^(w1 + a1) - 3^w1 ≥ 5` has at least one prime divisor `q ∣ D`;
     - **EVERY prime divisor `q ∣ D` (`IsPrimeNat q`) satisfies `q ≥ 5` AND is a coprime-order prime**:
       `∃ d2 d32, IsExactMultOrderMod q 2 d2 ∧ IsExactMultOrderMod q (ratio32Mod q) d32 ∧
        Nat.gcd d2 d32 = 1 ∧ (d2 * d32) ∣ (q - 1)`!
-/
theorem one_block_all_prime_divisors_coprime_order_and_totient :
    (∀ q : Nat, IsPrimeNat q -> q ≥ 5 ->
      ∃ d2 d32 : Nat,
        IsExactMultOrderMod q 2 d2 ∧
        IsExactMultOrderMod q (ratio32Mod q) d32 ∧
        d2 ∣ (q - 1) ∧
        d32 ∣ (q - 1) ∧
        (Nat.gcd d2 d32 = 1 -> (d2 * d32) ∣ (q - 1))) ∧
    (∀ w1 a1 q0 : Nat,
      w1 ≥ 2 -> a1 ≥ 1 -> q0 ≥ 1 -> 3 ^ w1 < 2 ^ (w1 + a1) ->
      (2 ^ (w1 + a1) - 3 ^ w1) * q0 = 2 ^ a1 - 1 ->
      let D := 2 ^ (w1 + a1) - 3 ^ w1
      D ≥ 5 ∧
      (∃ q : Nat, IsPrimeNat q ∧ q ∣ D) ∧
      (∀ q : Nat, IsPrimeNat q -> q ∣ D ->
        q ≥ 5 ∧
        ∃ d2 d32 : Nat,
          IsExactMultOrderMod q 2 d2 ∧
          IsExactMultOrderMod q (ratio32Mod q) d32 ∧
          Nat.gcd d2 d32 = 1 ∧
          (d2 * d32) ∣ (q - 1))) := by
  have hpart1 : ∀ q : Nat, IsPrimeNat q -> q ≥ 5 ->
      ∃ d2 d32 : Nat,
        IsExactMultOrderMod q 2 d2 ∧
        IsExactMultOrderMod q (ratio32Mod q) d32 ∧
        d2 ∣ (q - 1) ∧
        d32 ∣ (q - 1) ∧
        (Nat.gcd d2 d32 = 1 -> (d2 * d32) ∣ (q - 1)) := by
    intro q hq hq5
    have hnd2 : ¬ (q ∣ 2) := by
      rintro ⟨c, hc⟩; cases c with
      | zero => simp at hc
      | succ c' => have := Nat.mul_le_mul_left q (by omega : 1 ≤ c' + 1); omega
    have hq_odd : q % 2 = 1 := by
      by_cases hev : q % 2 = 0
      · exact False.elim (hq.2 2 (Nat.le_refl 2) (by omega) (Nat.dvd_of_mod_eq_zero hev))
      · omega
    have hnd32 : ¬ (q ∣ ratio32Mod q) := by
      intro hdvd
      have hm0 : ratio32Mod q % q = 0 := Nat.mod_eq_zero_of_dvd hdvd
      have h2r : (2 * ratio32Mod q) % q = 3 % q := by
        unfold ratio32Mod
        have h2inv : 2 * ((q + 1) / 2) = 1 + q := by omega
        calc
          (2 * ((3 * ((q + 1) / 2)) % q)) % q
              = (2 * (3 * ((q + 1) / 2))) % q := by
                rw [Nat.mul_mod 2 ((3 * ((q + 1) / 2)) % q) q, Nat.mod_mod, ← Nat.mul_mod]
          _ = (3 * (2 * ((q + 1) / 2))) % q := by
                rw [← Nat.mul_assoc 2 3, Nat.mul_comm 2 3, Nat.mul_assoc]
          _ = (3 + q * 3) % q := by rw [h2inv, Nat.mul_add, Nat.mul_one, Nat.mul_comm 3 q]
          _ = 3 % q := Nat.add_mul_mod_self_left 3 q 3
      rw [Nat.mul_mod 2 (ratio32Mod q) q, hm0, Nat.mul_zero, Nat.zero_mod,
          Nat.mod_eq_of_lt (by omega : 3 < q)] at h2r
      omega
    rcases exists_exact_mult_order_mod_prime q 2 hq hnd2 with ⟨d2, hd2, hdvd2⟩
    rcases exists_exact_mult_order_mod_prime q (ratio32Mod q) hq hnd32 with ⟨d32, hd32, hdvd32⟩
    exact ⟨d2, d32, hd2, hd32, hdvd2, hdvd32,
      fun hcop => coprime_mul_dvd_of_dvd d2 d32 (q - 1) hcop hdvd2 hdvd32⟩
  refine ⟨hpart1, ?_⟩
  intro w1 a1 q0 hw1 ha1 hq0 hgt hbrox
  dsimp only
  let D := 2 ^ (w1 + a1) - 3 ^ w1
  have hD_pos : D ≥ 1 := by dsimp [D]; omega
  -- `D` is odd (`2^(w1 + a1)` even, `3^w1` odd) and neither `1` nor `3`:
  have h2_ev : 2 ^ (w1 + a1) % 2 = 0 := by
    rw [show w1 + a1 = (w1 + a1 - 1) + 1 by omega, Nat.pow_succ]; omega
  have h3_odd : 3 ^ w1 % 2 = 1 := pow3_odd_nat_sec8 w1
  have hD_odd : D % 2 = 1 := by dsimp [D]; omega
  have h3_div3 : 3 ^ w1 % 3 = 0 := by
    rw [show w1 = (w1 - 1) + 1 by omega, Nat.pow_succ]; omega
  have h2_ndiv3 : 2 ^ (w1 + a1) % 3 ≠ 0 := pow2_mod3_nonzero_w5 (w1 + a1)
  have hD_ndiv3 : D % 3 ≠ 0 := by dsimp [D]; omega
  have hD_ne1 : D ≠ 1 := by
    intro hd1
    have h2_eq : 2 ^ (w1 + a1) = 3 ^ w1 + 1 := by dsimp [D] at hd1; omega
    have h2_8 : 2 ^ (w1 + a1) % 8 = 0 := by
      rw [show w1 + a1 = (w1 + a1 - 3) + 3 by omega, Nat.pow_add]
      change (2 ^ (w1 + a1 - 3) * 8) % 8 = 0
      exact Nat.mul_mod_left _ 8
    have h3_8 : ∀ k : Nat, 3 ^ k % 8 = 1 ∨ 3 ^ k % 8 = 3 := by
      intro k
      induction k with
      | zero => exact Or.inl rfl
      | succ k' ih =>
        rw [Nat.pow_succ, Nat.mul_mod]
        rcases ih with h1 | h3
        · rw [h1]; decide
        · rw [h3]; decide
    rcases h3_8 w1 with hm1 | hm3 <;> omega
  have hD_ge5 : D ≥ 5 := by omega
  refine ⟨hD_ge5, exists_prime_divisor_of_ge_two D (by omega), ?_⟩
  intro q hq hqD
  have hq_ge5 : q ≥ 5 := by
    have hq2 := hq.1
    by_cases hqe2 : q = 2
    · subst hqe2; have := Nat.mod_eq_zero_of_dvd hqD; omega
    · by_cases hqe3 : q = 3
      · subst hqe3; have := Nat.mod_eq_zero_of_dvd hqD; omega
      · by_cases hqe4 : q = 4
        · subst hqe4; exact False.elim (hq.2 2 (by decide) (by decide) (by decide))
        · omega
  rcases hpart1 q hq hq_ge5 with ⟨d2, d32, hd2, hd32, _, _, hprod_dvd⟩
  have hq_odd : q % 2 = 1 := by
    by_cases hev : q % 2 = 0
    · exact False.elim (hq.2 2 (Nat.le_refl 2) (by omega) (Nat.dvd_of_mod_eq_zero hev))
    · omega
  have hgcd_pos : Nat.gcd d2 d32 ≥ 1 := by
    have hd2_pos := hd2.2.1
    by_cases hg0 : Nat.gcd d2 d32 = 0
    · rw [Nat.gcd_eq_zero_iff] at hg0; omega
    · omega
  have hgcd_lt2 : ¬ (Nat.gcd d2 d32 ≥ 2) := fun hge2 =>
    one_block_common_order_prime_exclusion w1 a1 q0 q d2 d32
      hw1 ha1 hgt hbrox (by omega) hq_odd hd2 hd32 hge2 hqD
  have hgcd1 : Nat.gcd d2 d32 = 1 := by omega
  exact ⟨hq_ge5, d2, d32, hd2, hd32, hgcd1, hprod_dvd hgcd1⟩

-- Pure-`Nat` Gauss's Lemma & Universal Mod-24 `{11, 13}` Exclusion (`zero custom axioms`):

def gaussFoldMod (q x : Nat) : Nat :=
  if x % q ≤ (q - 1) / 2 then x % q else q - (x % q)

def gaussUpperCount (q b : Nat) : Nat -> Nat
  | 0 => 0
  | k + 1 => (if (b * (k + 1)) % q > (q - 1) / 2 then 1 else 0) + gaussUpperCount q b k

theorem gauss_prod_parity_relation (q b : Nat) (hq : q ≥ 3) :
    ∀ k : Nat,
      (gaussUpperCount q b k % 2 = 0 ->
        (b ^ k * natFact k) % q = natProdRange k (fun i => gaussFoldMod q (b * (i + 1))) % q) ∧
      (gaussUpperCount q b k % 2 = 1 ->
        (b ^ k * natFact k + natProdRange k (fun i => gaussFoldMod q (b * (i + 1)))) % q = 0)
  | 0 => by
    simp [gaussUpperCount, natFact, natProdRange, Nat.mod_eq_of_lt (by omega : 1 < q)]
  | k + 1 => by
    rcases gauss_prod_parity_relation q b hq k with ⟨ihe, iho⟩
    let r := (b * (k + 1)) % q
    let f := gaussFoldMod q (b * (k + 1))
    let P := natProdRange k (fun i => gaussFoldMod q (b * (i + 1)))
    let A := b ^ k * natFact k
    have hpow_step : b ^ (k + 1) * natFact (k + 1) = (b * (k + 1)) * A := by
      simp only [natFact, A]
      rw [Nat.pow_succ b k, Nat.mul_comm (b ^ k) b,
          Nat.mul_assoc b (k + 1), ← Nat.mul_assoc (k + 1) (b ^ k),
          Nat.mul_comm (k + 1) (b ^ k), Nat.mul_assoc (b ^ k) (k + 1),
          ← Nat.mul_assoc b (b ^ k)]
    have hmul_rA : ((b * (k + 1)) * A) % q = (r * (A % q)) % q := by
      dsimp [r]; rw [Nat.mul_mod (b * (k + 1)) A q]
    simp only [gaussUpperCount, natProdRange]
    -- Split on `(b * (k + 1)) % q > (q - 1) / 2`:
    by_cases hup : (b * (k + 1)) % q > (q - 1) / 2
    · have hf_eq : f = q - r := by
        dsimp [f, gaussFoldMod, r]; exact ite_false_of_w10 (by omega) _ _
      have hr_lt : r < q := Nat.mod_lt _ (by omega)
      have hrf : r + f = q := by rw [hf_eq]; omega
      simp only [hup, ite_true]
      refine ⟨?_, ?_⟩
      · intro hpar
        have hprev_odd : gaussUpperCount q b k % 2 = 1 := by omega
        have h0 := iho hprev_odd
        -- `r * A - f * P`: since `(A + P) % q = 0` and `r + f = q`,
        -- `r * A + f * A = q * A` and `f * A + f * P = f * (A + P)`:
        have hsum1 : (r * A + f * A) % q = 0 := by
          rw [← Nat.add_mul r f A, hrf, Nat.mul_comm q A, Nat.mul_mod_left]
        have hsum2 : (f * A + f * P) % q = 0 := by
          rw [← Nat.mul_add f A P, Nat.mul_mod, h0, Nat.mul_zero, Nat.zero_mod]
        rw [hpow_step]
        change ((b * (k + 1)) * A) % q = (f * P) % q
        have hrA_mod : ((b * (k + 1)) * A) % q = (r * A) % q := by
          rw [hmul_rA, Nat.mul_mod r A q, Nat.mod_eq_of_lt hr_lt]
        rw [hrA_mod]
        -- Both `(r * A + f * A) % q = 0` and `(f * P + f * A) % q = 0`!
        have h_add_cancel : ∀ x y z : Nat, (x + z) % q = 0 -> (y + z) % q = 0 -> x % q = y % q := by
          intro x y z hxz hyz
          have h1 : (x % q + z % q) % q = 0 := by rwa [← Nat.add_mod]
          have h2 : (y % q + z % q) % q = 0 := by rwa [← Nat.add_mod]
          have hxl : x % q < q := Nat.mod_lt x (by omega)
          have hyl : y % q < q := Nat.mod_lt y (by omega)
          have hzl : z % q < q := Nat.mod_lt z (by omega)
          by_cases hz0 : z % q = 0
          · rw [hz0, Nat.add_zero, Nat.mod_mod] at h1 h2; omega
          · have hx_sum : x % q + z % q = q := by
              by_cases hlt : x % q + z % q < q
              · rw [Nat.mod_eq_of_lt hlt] at h1; omega
              · have hsp : x % q + z % q = (x % q + z % q - q) + q * 1 := by omega
                rw [hsp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)] at h1; omega
            have hy_sum : y % q + z % q = q := by
              by_cases hlt : y % q + z % q < q
              · rw [Nat.mod_eq_of_lt hlt] at h2; omega
              · have hsp : y % q + z % q = (y % q + z % q - q) + q * 1 := by omega
                rw [hsp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)] at h2; omega
            omega
        exact h_add_cancel (r * A) (f * P) (f * A) hsum1 (by rwa [Nat.add_comm])
      · intro hpar
        have hprev_ev : gaussUpperCount q b k % 2 = 0 := by omega
        have heq := ihe hprev_ev
        rw [hpow_step]
        change ((b * (k + 1)) * A + f * P) % q = 0
        calc
          ((b * (k + 1)) * A + f * P) % q
              = (((b * (k + 1)) * A) % q + (f * P) % q) % q := Nat.add_mod _ _ q
          _ = ((r * (A % q)) % q + ((f % q) * (P % q)) % q) % q := by
                rw [hmul_rA, Nat.mul_mod f P q]
          _ = ((r * (P % q)) % q + ((f % q) * (P % q)) % q) % q := by rw [heq]
          _ = (((r % q) * ((P % q) % q)) % q + ((f % q) * ((P % q) % q)) % q) % q := by
                rw [Nat.mod_eq_of_lt hr_lt, Nat.mod_mod P q]
          _ = ((r * (P % q)) % q + (f * (P % q)) % q) % q := by
                rw [← Nat.mul_mod r (P % q) q, ← Nat.mul_mod f (P % q) q]
          _ = ((r + f) * (P % q)) % q := by rw [← Nat.add_mod, ← Nat.add_mul]
          _ = 0 := by rw [hrf, Nat.mul_comm q, Nat.mul_mod_left]
    · have hf_eq : f = r := by
        dsimp [f, gaussFoldMod, r]; exact ite_true_of_w10 (by omega) _ _
      simp only [hup, ite_false, Nat.zero_add]
      refine ⟨?_, ?_⟩
      · intro hpar
        have heq := ihe hpar
        rw [hpow_step]
        change ((b * (k + 1)) * A) % q = (f * P) % q
        rw [hmul_rA, heq, hf_eq, Nat.mul_mod r P q, Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))]
      · intro hpar
        have h0 := iho hpar
        rw [hpow_step]
        change ((b * (k + 1)) * A + f * P) % q = 0
        have hr_lt : r < q := Nat.mod_lt _ (by omega)
        have hmul_r : ∀ X : Nat, (r * (X % q)) % q = (r * X) % q := fun X => by
          rw [Nat.mul_mod r X q, Nat.mod_eq_of_lt hr_lt]
        calc
          ((b * (k + 1)) * A + f * P) % q
              = (((b * (k + 1)) * A) % q + (f * P) % q) % q := Nat.add_mod _ _ q
          _ = ((r * (A % q)) % q + (r * (P % q)) % q) % q := by
                rw [hmul_rA, hf_eq, Nat.mul_mod r P q, Nat.mod_eq_of_lt hr_lt]
          _ = ((r * A) % q + (r * P) % q) % q := by
                rw [hmul_r A, hmul_r P]
          _ = (r * (A + P)) % q := by rw [← Nat.add_mod, ← Nat.mul_add]
          _ = 0 := by rw [Nat.mul_mod, h0, Nat.mul_zero, Nat.zero_mod]

/-- Gauss's Lemma in pure `Nat` (`zero custom axioms`). -/
theorem gauss_lemma_mod_prime (q b : Nat) (hq : IsPrimeNat q) (hq_odd : q % 2 = 1)
    (hq5 : q ≥ 5) (hnd : ¬ (q ∣ b)) :
    let h := (q - 1) / 2
    (gaussUpperCount q b h % 2 = 0 -> b ^ h % q = 1) ∧
    (gaussUpperCount q b h % 2 = 1 -> b ^ h % q = q - 1) := by
  dsimp only
  let h := (q - 1) / 2
  have hh_lt : h < q := by dsimp [h]; omega
  let f : Nat -> Nat := fun i => gaussFoldMod q (b * (i + 1))
  have hf_bounds : ∀ i : Nat, i < h -> 1 ≤ f i ∧ f i ≤ h := by
    intro i hi
    dsimp [f, gaussFoldMod]
    have hr_lt : (b * (i + 1)) % q < q := Nat.mod_lt _ (by omega)
    have hnz : (b * (i + 1)) % q ≠ 0 := by
      intro hz
      rcases gauss_euclid_lemma q b (i + 1) hq (Nat.dvd_of_mod_eq_zero hz) with hqb | hqi
      · exact hnd hqb
      · rcases hqi with ⟨c, hc⟩
        cases c with
        | zero => simp at hc
        | succ c' =>
          have hge : q ≤ q * (c' + 1) := by simpa using Nat.mul_le_mul_left q (by omega : 1 ≤ c' + 1)
          omega
    by_cases hle : (b * (i + 1)) % q ≤ h
    · rw [ite_true_of_w10 hle]; exact ⟨by omega, hle⟩
    · rw [ite_false_of_w10 hle]; exact ⟨by omega, by dsimp [h] at hle ⊢; omega⟩
  have hf_inj : ∀ i j : Nat, i < h -> j < h -> f i = f j -> i = j := by
    intro i j hi hj heq
    dsimp [f, gaussFoldMod] at heq
    let ri := (b * (i + 1)) % q
    let rj := (b * (j + 1)) % q
    have hri_lt : ri < q := Nat.mod_lt _ (by omega)
    have hrj_lt : rj < q := Nat.mod_lt _ (by omega)
    change (if ri ≤ h then ri else q - ri) = (if rj ≤ h then rj else q - rj) at heq
    by_cases h1 : ri ≤ h <;> by_cases h2 : rj ≤ h
    · rw [ite_true_of_w10 h1, ite_true_of_w10 h2] at heq
      have hc := cancel_mul_mod_prime q b (i + 1) (j + 1) hq hnd heq
      rw [Nat.mod_eq_of_lt (by dsimp [h] at hi; omega),
          Nat.mod_eq_of_lt (by dsimp [h] at hj; omega)] at hc
      omega
    · rw [ite_true_of_w10 h1, ite_false_of_w10 h2] at heq
      have hsum_q : ri + rj = q := by omega
      have hmul_sum : (b * ((i + 1) + (j + 1))) % q = 0 := by
        rw [Nat.mul_add, Nat.add_mod, show (b * (i + 1)) % q = ri from rfl,
            show (b * (j + 1)) % q = rj from rfl, hsum_q, Nat.mod_self]
      rcases gauss_euclid_lemma q b ((i + 1) + (j + 1)) hq (Nat.dvd_of_mod_eq_zero hmul_sum) with
        hqb | hqs
      · exact False.elim (hnd hqb)
      · rcases hqs with ⟨c, hc⟩
        cases c with
        | zero => simp at hc
        | succ c' =>
          have hge : q ≤ q * (c' + 1) := by simpa using Nat.mul_le_mul_left q (by omega : 1 ≤ c' + 1)
          dsimp [h] at hi hj; omega
    · rw [ite_false_of_w10 h1, ite_true_of_w10 h2] at heq
      have hsum_q : ri + rj = q := by omega
      have hmul_sum : (b * ((i + 1) + (j + 1))) % q = 0 := by
        rw [Nat.mul_add, Nat.add_mod, show (b * (i + 1)) % q = ri from rfl,
            show (b * (j + 1)) % q = rj from rfl, hsum_q, Nat.mod_self]
      rcases gauss_euclid_lemma q b ((i + 1) + (j + 1)) hq (Nat.dvd_of_mod_eq_zero hmul_sum) with
        hqb | hqs
      · exact False.elim (hnd hqb)
      · rcases hqs with ⟨c, hc⟩
        cases c with
        | zero => simp at hc
        | succ c' =>
          have hge : q ≤ q * (c' + 1) := by simpa using Nat.mul_le_mul_left q (by omega : 1 ≤ c' + 1)
          dsimp [h] at hi hj; omega
    · rw [ite_false_of_w10 h1, ite_false_of_w10 h2] at heq
      have hre : ri = rj := by omega
      have hc := cancel_mul_mod_prime q b (i + 1) (j + 1) hq hnd hre
      rw [Nat.mod_eq_of_lt (by dsimp [h] at hi; omega),
          Nat.mod_eq_of_lt (by dsimp [h] at hj; omega)] at hc
      omega
  have hprod_fact : natProdRange h f = natFact h := natProdRange_inj_eq_fact h f hf_bounds hf_inj
  rcases gauss_prod_parity_relation q b (by omega) h with ⟨hrel_ev, hrel_odd⟩
  rw [hprod_fact] at hrel_ev hrel_odd
  have hnd_fh := prime_not_dvd_natFact q hq h hh_lt
  refine ⟨?_, ?_⟩
  · intro hev
    have hm := hrel_ev hev
    have hc := cancel_mul_mod_prime q (natFact h) (b ^ h) 1 hq hnd_fh
      (by rw [Nat.mul_comm (natFact h), hm, Nat.mul_one])
    rwa [Nat.mod_eq_of_lt (by omega : 1 < q)] at hc
  · intro hodd
    have hm := hrel_odd hodd
    -- `(natFact h * b ^ h + natFact h) % q = 0` AND `(natFact h * (q - 1) + natFact h) % q = 0`:
    have hqm1 : (natFact h * (q - 1) + natFact h) % q = 0 := by
      have hsp : natFact h * (q - 1) + natFact h = q * natFact h := by
        have hp : q - 1 + 1 = q := by omega
        calc
          natFact h * (q - 1) + natFact h = natFact h * ((q - 1) + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
          _ = q * natFact h := by rw [hp, Nat.mul_comm]
      rw [hsp, Nat.mul_mod_right]
    have hmul_eq : (natFact h * b ^ h) % q = (natFact h * (q - 1)) % q := by
      rw [Nat.mul_comm (natFact h) (b ^ h)]
      have h1 : ((b ^ h * natFact h) % q + natFact h % q) % q = 0 := by rwa [← Nat.add_mod]
      have h2 : ((natFact h * (q - 1)) % q + natFact h % q) % q = 0 := by rwa [← Nat.add_mod]
      have hnz_f : natFact h % q ≠ 0 := fun hz => hnd_fh (Nat.dvd_of_mod_eq_zero hz)
      have hlt_a : (b ^ h * natFact h) % q < q := Nat.mod_lt _ (by omega)
      have hlt_b : (natFact h * (q - 1)) % q < q := Nat.mod_lt _ (by omega)
      have hlt_f : natFact h % q < q := Nat.mod_lt _ (by omega)
      have ha_q : (b ^ h * natFact h) % q + natFact h % q = q := by
        by_cases hlt : (b ^ h * natFact h) % q + natFact h % q < q
        · rw [Nat.mod_eq_of_lt hlt] at h1; omega
        · have hsp : (b ^ h * natFact h) % q + natFact h % q =
              ((b ^ h * natFact h) % q + natFact h % q - q) + q * 1 := by omega
          conv at h1 => lhs; arg 1; rw [hsp]
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)] at h1; omega
      have hb_q : (natFact h * (q - 1)) % q + natFact h % q = q := by
        by_cases hlt : (natFact h * (q - 1)) % q + natFact h % q < q
        · rw [Nat.mod_eq_of_lt hlt] at h2; omega
        · have hsp : (natFact h * (q - 1)) % q + natFact h % q =
              ((natFact h * (q - 1)) % q + natFact h % q - q) + q * 1 := by omega
          conv at h2 => lhs; arg 1; rw [hsp]
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)] at h2; omega
      omega
    have hc := cancel_mul_mod_prime q (natFact h) (b ^ h) (q - 1) hq hnd_fh hmul_eq
    rwa [Nat.mod_eq_of_lt (by omega : q - 1 < q)] at hc

theorem gaussUpperCount_two_eq (q : Nat) (hq_odd : q % 2 = 1) (hq5 : q ≥ 5) :
    ∀ k : Nat, k ≤ (q - 1) / 2 ->
      gaussUpperCount q 2 k = k - (min k ((q - 1) / 4))
  | 0, _ => rfl
  | k + 1, hk => by
    have ih := gaussUpperCount_two_eq q hq_odd hq5 k (by omega)
    simp only [gaussUpperCount, ih]
    have h2k_lt : 2 * (k + 1) < q := by omega
    rw [Nat.mod_eq_of_lt h2k_lt]
    by_cases hgt : 2 * (k + 1) > (q - 1) / 2
    · rw [ite_true_of_w10 hgt]
      have hmin1 : min (k + 1) ((q - 1) / 4) = (q - 1) / 4 := Nat.min_eq_right (by omega)
      have hmin0 : min k ((q - 1) / 4) = (q - 1) / 4 := Nat.min_eq_right (by omega)
      rw [hmin1, hmin0]; omega
    · rw [ite_false_of_w10 hgt]
      have hmin1 : min (k + 1) ((q - 1) / 4) = k + 1 := Nat.min_eq_left (by omega)
      have hmin0 : min k ((q - 1) / 4) = k := Nat.min_eq_left (by omega)
      rw [hmin1, hmin0]; omega

theorem gaussUpperCount_three_eq (q : Nat) (hq_odd : q % 2 = 1) (hq5 : q ≥ 5)
    (hq_nd3 : q % 3 ≠ 0) :
    ∀ k : Nat, k ≤ (q - 1) / 2 ->
      gaussUpperCount q 3 k = min k (q / 3) - min k ((q - 1) / 6)
  | 0, _ => rfl
  | k + 1, hk => by
    have ih := gaussUpperCount_three_eq q hq_odd hq5 hq_nd3 k (by omega)
    simp only [gaussUpperCount, ih]
    by_cases hlt_q : 3 * (k + 1) < q
    · rw [Nat.mod_eq_of_lt hlt_q]
      have hmin_q1 : min (k + 1) (q / 3) = k + 1 := Nat.min_eq_left (by omega)
      have hmin_q0 : min k (q / 3) = k := Nat.min_eq_left (by omega)
      rw [hmin_q1, hmin_q0]
      by_cases hgt : 3 * (k + 1) > (q - 1) / 2
      · rw [ite_true_of_w10 hgt]
        have hm1 : min (k + 1) ((q - 1) / 6) = (q - 1) / 6 := Nat.min_eq_right (by omega)
        have hm0 : min k ((q - 1) / 6) = (q - 1) / 6 := Nat.min_eq_right (by omega)
        rw [hm1, hm0]; omega
      · rw [ite_false_of_w10 hgt]
        have hm1 : min (k + 1) ((q - 1) / 6) = k + 1 := Nat.min_eq_left (by omega)
        have hm0 : min k ((q - 1) / 6) = k := Nat.min_eq_left (by omega)
        rw [hm1, hm0]; omega
    · have hne_q : 3 * (k + 1) ≠ q := fun he => hq_nd3 (by rw [← he, Nat.mul_mod_right])
      have hgt_q : 3 * (k + 1) > q := by omega
      have hlt_2q : 3 * (k + 1) < 2 * q := by omega
      have hmod_sub : (3 * (k + 1)) % q = 3 * (k + 1) - q := by
        have hsp : 3 * (k + 1) = (3 * (k + 1) - q) + q * 1 := by omega
        conv => lhs; arg 1; rw [hsp]
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      rw [hmod_sub]
      have hnot_up : ¬ (3 * (k + 1) - q > (q - 1) / 2) := by omega
      rw [ite_false_of_w10 hnot_up]
      have hmin_q1 : min (k + 1) (q / 3) = q / 3 := Nat.min_eq_right (by omega)
      have hmin_q0 : min k (q / 3) = q / 3 := Nat.min_eq_right (by omega)
      have hm1 : min (k + 1) ((q - 1) / 6) = (q - 1) / 6 := Nat.min_eq_right (by omega)
      have hm0 : min k ((q - 1) / 6) = (q - 1) / 6 := Nat.min_eq_right (by omega)
      rw [hmin_q1, hmin_q0, hm1, hm0]; omega

/--
  Theorem W10.2b (`mod24_11_13_quadratic_reciprocity_and_one_block_exclusion`, `zero custom axioms`):
  Universal Mod-`24` `{11, 13}` Quadratic-Reciprocity Exclusion Law:
  1. For EVERY prime `q` (`IsPrimeNat q`) with `q % 24 = 11 ∨ q % 24 = 13`:
     - `2 ^ ((q - 1) / 2) % q = q - 1` (`(2 / q) = -1`) AND `3 ^ ((q - 1) / 2) % q = 1` (`(3 / q) = +1`);
     - `(ratio32Mod q) ^ ((q - 1) / 2) % q = q - 1`;
     - For ANY exact multiplicative orders `d2 = ord_q(2)` and `d32 = ord_q(3/2)`, BOTH `d2` and `d32`
       are EVEN (`2 ∣ d2 ∧ 2 ∣ d32`), hence `2 ∣ Nat.gcd d2 d32` (`Nat.gcd d2 d32 ≥ 2`)!
  2. Consequently, **NO prime `q` with `q % 24 ∈ {11, 13}` can EVER divide `D = 2^(w1 + a1) - 3^w1`
     on ANY nontrivial 1-block `Z^+` cycle**!
-/
theorem mod24_11_13_quadratic_reciprocity_and_one_block_exclusion :
    (∀ q : Nat, IsPrimeNat q -> (q % 24 = 11 ∨ q % 24 = 13) ->
      let h := (q - 1) / 2
      2 ^ h % q = q - 1 ∧
      3 ^ h % q = 1 ∧
      (ratio32Mod q) ^ h % q = q - 1 ∧
      ∀ d2 d32 : Nat,
        IsExactMultOrderMod q 2 d2 ->
        IsExactMultOrderMod q (ratio32Mod q) d32 ->
        2 ∣ d2 ∧ 2 ∣ d32 ∧ 2 ∣ Nat.gcd d2 d32 ∧ Nat.gcd d2 d32 ≥ 2) ∧
    (∀ w1 a1 q0 q : Nat,
      w1 ≥ 2 -> a1 ≥ 1 -> q0 ≥ 1 -> 3 ^ w1 < 2 ^ (w1 + a1) ->
      (2 ^ (w1 + a1) - 3 ^ w1) * q0 = 2 ^ a1 - 1 ->
      IsPrimeNat q -> (q % 24 = 11 ∨ q % 24 = 13) ->
      ¬ (q ∣ (2 ^ (w1 + a1) - 3 ^ w1))) := by
  have hrec : ∀ q : Nat, IsPrimeNat q -> (q % 24 = 11 ∨ q % 24 = 13) ->
      let h := (q - 1) / 2
      2 ^ h % q = q - 1 ∧
      3 ^ h % q = 1 ∧
      (ratio32Mod q) ^ h % q = q - 1 ∧
      ∀ d2 d32 : Nat,
        IsExactMultOrderMod q 2 d2 ->
        IsExactMultOrderMod q (ratio32Mod q) d32 ->
        2 ∣ d2 ∧ 2 ∣ d32 ∧ 2 ∣ Nat.gcd d2 d32 ∧ Nat.gcd d2 d32 ≥ 2 := by
    intro q hq hmod24
    dsimp only
    let h := (q - 1) / 2
    have hq11 : q ≥ 11 := by omega
    have hq_odd : q % 2 = 1 := by omega
    have hq_nd3 : q % 3 ≠ 0 := by omega
    have hnd2 : ¬ (q ∣ 2) := by
      rintro ⟨c, hc⟩; cases c with
      | zero => simp at hc
      | succ c' => have := Nat.mul_le_mul_left q (by omega : 1 ≤ c' + 1); omega
    have hnd3 : ¬ (q ∣ 3) := by
      rintro ⟨c, hc⟩; cases c with
      | zero => simp at hc
      | succ c' => have := Nat.mul_le_mul_left q (by omega : 1 ≤ c' + 1); omega
    have hc2 := gaussUpperCount_two_eq q hq_odd (by omega) h (Nat.le_refl h)
    have hc3 := gaussUpperCount_three_eq q hq_odd (by omega) hq_nd3 h (Nat.le_refl h)
    have hmin2 : min h ((q - 1) / 4) = (q - 1) / 4 := Nat.min_eq_right (by dsimp [h]; omega)
    have hmin3a : min h (q / 3) = q / 3 := Nat.min_eq_right (by dsimp [h]; omega)
    have hmin3b : min h ((q - 1) / 6) = (q - 1) / 6 := Nat.min_eq_right (by dsimp [h]; omega)
    rw [hmin2] at hc2
    rw [hmin3a, hmin3b] at hc3
    have hc2_odd : gaussUpperCount q 2 h % 2 = 1 := by rw [hc2]; dsimp [h]; omega
    have hc3_ev  : gaussUpperCount q 3 h % 2 = 0 := by rw [hc3]; omega
    have hpow2 : 2 ^ h % q = q - 1 := (gauss_lemma_mod_prime q 2 hq hq_odd (by omega) hnd2).2 hc2_odd
    have hpow3 : 3 ^ h % q = 1     := (gauss_lemma_mod_prime q 3 hq hq_odd (by omega) hnd3).1 hc3_ev
    -- `(2 * ratio32Mod q) ^ h % q = 3 ^ h % q = 1`, and `2 ^ h % q = q - 1 => ratio32Mod q ^ h % q = q - 1`:
    have h2r_mod : (2 * ratio32Mod q) % q = 3 % q := by
      unfold ratio32Mod
      have h2inv : 2 * ((q + 1) / 2) = 1 + q := by omega
      calc
        (2 * ((3 * ((q + 1) / 2)) % q)) % q
            = (2 * (3 * ((q + 1) / 2))) % q := by
              rw [Nat.mul_mod 2 _ q, Nat.mod_mod, ← Nat.mul_mod]
        _ = (3 * (2 * ((q + 1) / 2))) % q := by
              rw [← Nat.mul_assoc 2 3, Nat.mul_comm 2 3, Nat.mul_assoc]
        _ = (3 + q * 3) % q := by rw [h2inv, Nat.mul_add, Nat.mul_one, Nat.mul_comm 3 q]
        _ = 3 % q := Nat.add_mul_mod_self_left 3 q 3
    have hpow_mul : ∀ k : Nat, (2 * ratio32Mod q) ^ k = 2 ^ k * (ratio32Mod q) ^ k := by
      intro k
      induction k with
      | zero => rfl
      | succ k' ih =>
        rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, ih]
        rw [Nat.mul_assoc (2 ^ k') ((ratio32Mod q) ^ k') (2 * ratio32Mod q),
            ← Nat.mul_assoc ((ratio32Mod q) ^ k') 2 (ratio32Mod q),
            Nat.mul_comm ((ratio32Mod q) ^ k') 2,
            Nat.mul_assoc 2 ((ratio32Mod q) ^ k') (ratio32Mod q),
            ← Nat.mul_assoc (2 ^ k') 2]
    have hprod_h : ((q - 1) * (ratio32Mod q) ^ h) % q = ((q - 1) * (q - 1)) % q := by
      have h1 : (2 ^ h * (ratio32Mod q) ^ h) % q = 1 := by
        rw [← hpow_mul h,
            pow_mod_eq_of_mod_eq_w5 q (2 * ratio32Mod q) 3 h2r_mod h,
            hpow3]
      have h2 : ((q - 1) * (ratio32Mod q) ^ h) % q = 1 := by
        rw [Nat.mul_mod (2 ^ h) _ q, hpow2, ← Nat.mod_eq_of_lt (by omega : q - 1 < q), ← Nat.mul_mod] at h1
        exact h1
      have hqm1_sq : ((q - 1) * (q - 1)) % q = 1 := by
        have hsp : (q - 1) * (q - 1) = 1 + q * (q - 2) := by
          let m := q - 2
          have hq2 : q - 2 = m := rfl
          have hq1 : q - 1 = m + 1 := by dsimp [m]; omega
          have hq0 : q = m + 2 := by dsimp [m]; omega
          rw [hq1, hq2, hq0, Nat.add_mul m 1 (m + 1), Nat.mul_add m m 1, Nat.one_mul, Nat.mul_one,
              Nat.add_mul m 2 m]
          omega
        rw [hsp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : 1 < q)]
      rw [h2, hqm1_sq]
    have hnd_qm1 : ¬ (q ∣ (q - 1)) := by
      rintro ⟨c, hc⟩; cases c with
      | zero => simp at hc; omega
      | succ c' => have := Nat.mul_le_mul_left q (by omega : 1 ≤ c' + 1); omega
    have hpow32 : (ratio32Mod q) ^ h % q = q - 1 := by
      have hc := cancel_mul_mod_prime q (q - 1) ((ratio32Mod q) ^ h) (q - 1) hq hnd_qm1 hprod_h
      rwa [Nat.mod_eq_of_lt (by omega : q - 1 < q)] at hc
    refine ⟨hpow2, hpow3, hpow32, ?_⟩
    intro d2 d32 hd2 hd32
    have heven_of_ord : ∀ (b d : Nat),
        ¬ (q ∣ b) -> IsExactMultOrderMod q b d -> b ^ h % q = q - 1 -> 2 ∣ d := by
      intro b d hnd_b hord hbh
      have hdvd_qm1 : d ∣ (q - 1) :=
        exactMultOrderMod_dvd_of_pow_eq_one q b d (q - 1) hord (fermat_little_mod_prime q b hq hnd_b)
      have h2h : q - 1 = 2 * h := by dsimp [h]; omega
      rw [h2h] at hdvd_qm1
      have hnot_dvd_h : ¬ (d ∣ h) := by
        rintro ⟨k, hk_eq⟩
        rw [hk_eq, ← pow_pow_eq_mul_w5 b d k,
            pow_mod_eq_of_mod_eq_w5 q (b ^ d) 1
              (by rw [hord.2.2.1, Nat.mod_eq_of_lt (by omega : 1 < q)]) k,
            Nat.one_pow, Nat.mod_eq_of_lt (by omega : 1 < q)] at hbh
        omega
      by_cases hev : d % 2 = 0
      · exact Nat.dvd_of_mod_eq_zero hev
      · have hd_odd : d % 2 = 1 := by omega
        have hgcd_d2 : Nat.gcd d 2 = 1 := by
          rw [Nat.gcd_comm, Nat.gcd_rec 2 d, hd_odd]; decide
        exact False.elim (hnot_dvd_h
          (coprime_dvd_of_dvd_mul_aux (d + 2) d 2 h (Nat.le_refl _) hgcd_d2 hdvd_qm1))
    have h2_d2 := heven_of_ord 2 d2 hnd2 hd2 hpow2
    have hnd32 : ¬ (q ∣ ratio32Mod q) := by
      intro hd
      rw [Nat.mul_mod, Nat.mod_eq_zero_of_dvd hd, Nat.mul_zero, Nat.zero_mod,
          Nat.mod_eq_of_lt (by omega : 3 < q)] at h2r_mod
      omega
    have h2_d32 := heven_of_ord (ratio32Mod q) d32 hnd32 hd32 hpow32
    have h2_gcd : 2 ∣ Nat.gcd d2 d32 := Nat.dvd_gcd h2_d2 h2_d32
    have hgcd_ge2 : Nat.gcd d2 d32 ≥ 2 := by
      rcases h2_gcd with ⟨c, hc⟩
      cases c with
      | zero =>
        simp only [Nat.mul_zero] at hc
        rw [Nat.gcd_eq_zero_iff] at hc
        have := hd2.2.1; omega
      | succ c' => omega
    exact ⟨h2_d2, h2_d32, h2_gcd, hgcd_ge2⟩
  refine ⟨hrec, ?_⟩
  intro w1 a1 q0 q hw1 ha1 hq0 hgt hbrox hq hmod24 hqD
  rcases (one_block_all_prime_divisors_coprime_order_and_totient.2
    w1 a1 q0 hw1 ha1 hq0 hgt hbrox).2.2 q hq hqD with ⟨_, d2, d32, hd2, hd32, hgcd1, _⟩
  rcases (hrec q hq hmod24).2.2.2 d2 d32 hd2 hd32 with ⟨_, _, _, hge2⟩
  omega

-- ----------------------------------------------------------------------------
-- Section 2B: Certified 4-Variable `Int` Polynomial Ring Reflector & Exact `6 x 6`
--             Single-Base / Two-Base Schneider–Laurent Factorization + Zero Locus
-- ----------------------------------------------------------------------------

def intPowNat : Int -> Nat -> Int
  | _, 0 => 1
  | x, n + 1 => x * intPowNat x n

theorem intPowNat_add (x : Int) : ∀ a b : Nat, intPowNat x (a + b) = intPowNat x a * intPowNat x b
  | 0, b => by simp [intPowNat]
  | a + 1, b => by
    rw [Nat.succ_add, intPowNat, intPowNat, intPowNat_add x a b, Int.mul_assoc]

abbrev Mono4 := Nat × Nat × Nat × Nat × Int

def evalMono4 (x0 x1 x2 x3 : Int) (m : Mono4) : Int :=
  m.2.2.2.2 * (intPowNat x0 m.1 * (intPowNat x1 m.2.1 * (intPowNat x2 m.2.2.1 * intPowNat x3 m.2.2.2.1)))

def evalPoly4 (x0 x1 x2 x3 : Int) : List Mono4 -> Int
  | [] => 0
  | m :: ms => evalMono4 x0 x1 x2 x3 m + evalPoly4 x0 x1 x2 x3 ms

def isZeroInt : Int -> Bool
  | .ofNat 0 => true
  | _ => false

theorem isZeroInt_iff (c : Int) : isZeroInt c = true ↔ c = 0 := by
  cases c with
  | ofNat n =>
    cases n with
    | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | succ m => exact ⟨fun h => (by cases h), fun h => by cases h⟩
  | negSucc n => exact ⟨fun h => (by cases h), fun h => by cases h⟩

def eqExp4Bool (a b : Mono4) : Bool :=
  Nat.beq a.1 b.1 && (Nat.beq a.2.1 b.2.1 && (Nat.beq a.2.2.1 b.2.2.1 && Nat.beq a.2.2.2.1 b.2.2.2.1))

theorem eqExp4Bool_eq_true (a b : Mono4) (h : eqExp4Bool a b = true) :
    a.1 = b.1 ∧ a.2.1 = b.2.1 ∧ a.2.2.1 = b.2.2.1 ∧ a.2.2.2.1 = b.2.2.2.1 := by
  unfold eqExp4Bool at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

def ltExp4Bool (a b : Mono4) : Bool :=
  if Nat.blt a.1 b.1 then true
  else if Nat.beq a.1 b.1 then
    if Nat.blt a.2.1 b.2.1 then true
    else if Nat.beq a.2.1 b.2.1 then
      if Nat.blt a.2.2.1 b.2.2.1 then true
      else if Nat.beq a.2.2.1 b.2.2.1 then Nat.blt a.2.2.2.1 b.2.2.2.1
      else false
    else false
  else false

def mergePoly4Aux (a : Mono4) (as : List Mono4) (mergeAs : List Mono4 -> List Mono4) :
    List Mono4 -> List Mono4
  | [] => a :: as
  | b :: bs =>
    if eqExp4Bool a b then
      let c := a.2.2.2.2 + b.2.2.2.2
      if isZeroInt c then mergeAs bs
      else (b.1, b.2.1, b.2.2.1, b.2.2.2.1, c) :: mergeAs bs
    else if ltExp4Bool a b then
      a :: mergeAs (b :: bs)
    else
      b :: mergePoly4Aux a as mergeAs bs

def addPoly4 : List Mono4 -> List Mono4 -> List Mono4
  | [], q => q
  | a :: as, q => mergePoly4Aux a as (addPoly4 as) q

theorem evalPoly4_mergePoly4Aux (x0 x1 x2 x3 : Int) (a : Mono4) (as : List Mono4)
    (mergeAs : List Mono4 -> List Mono4)
    (hmerge : ∀ r : List Mono4, evalPoly4 x0 x1 x2 x3 (mergeAs r) =
      evalPoly4 x0 x1 x2 x3 as + evalPoly4 x0 x1 x2 x3 r) :
    ∀ q : List Mono4,
      evalPoly4 x0 x1 x2 x3 (mergePoly4Aux a as mergeAs q) =
        evalMono4 x0 x1 x2 x3 a + evalPoly4 x0 x1 x2 x3 as + evalPoly4 x0 x1 x2 x3 q
  | [] => by simp [mergePoly4Aux, evalPoly4]
  | b :: bs => by
    unfold mergePoly4Aux
    cases heq : eqExp4Bool a b with
    | true =>
      simp only [ite_true]
      rcases eqExp4Bool_eq_true a b heq with ⟨he0, he1, he2, he3⟩
      let X := intPowNat x0 b.1 * (intPowNat x1 b.2.1 * (intPowNat x2 b.2.2.1 * intPowNat x3 b.2.2.2.1))
      have ha_ev : evalMono4 x0 x1 x2 x3 a = a.2.2.2.2 * X := by
        unfold evalMono4; rw [he0, he1, he2, he3]
      have hb_ev : evalMono4 x0 x1 x2 x3 b = b.2.2.2.2 * X := rfl
      cases hz : isZeroInt (a.2.2.2.2 + b.2.2.2.2) with
      | true =>
        have hc0 : a.2.2.2.2 + b.2.2.2.2 = 0 := (isZeroInt_iff _).mp hz
        simp only [ite_true, hmerge bs, evalPoly4, ha_ev, hb_ev]
        have hsum : a.2.2.2.2 * X + b.2.2.2.2 * X = 0 := by
          rw [← Int.add_mul, hc0, Int.zero_mul]
        omega
      | false =>
        simp only [Bool.false_eq_true, ite_false, evalPoly4, hmerge bs, ha_ev, hb_ev]
        change (a.2.2.2.2 + b.2.2.2.2) * X + (evalPoly4 x0 x1 x2 x3 as + evalPoly4 x0 x1 x2 x3 bs) = _
        rw [Int.add_mul]
        omega
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      cases hlt : ltExp4Bool a b with
      | true =>
        simp only [ite_true, evalPoly4, hmerge (b :: bs)]
        omega
      | false =>
        simp only [Bool.false_eq_true, ite_false, evalPoly4,
          evalPoly4_mergePoly4Aux x0 x1 x2 x3 a as mergeAs hmerge bs]
        omega

theorem evalPoly4_addPoly4 (x0 x1 x2 x3 : Int) :
    ∀ p q : List Mono4,
      evalPoly4 x0 x1 x2 x3 (addPoly4 p q) = evalPoly4 x0 x1 x2 x3 p + evalPoly4 x0 x1 x2 x3 q
  | [], q => by simp [addPoly4, evalPoly4]
  | a :: as, q => by
    simp only [addPoly4, evalPoly4,
      evalPoly4_mergePoly4Aux x0 x1 x2 x3 a as (addPoly4 as) (evalPoly4_addPoly4 x0 x1 x2 x3 as) q,
      Int.add_assoc]

def negPoly4 : List Mono4 -> List Mono4
  | [] => []
  | m :: ms => (m.1, m.2.1, m.2.2.1, m.2.2.2.1, -m.2.2.2.2) :: negPoly4 ms

theorem evalPoly4_negPoly4 (x0 x1 x2 x3 : Int) :
    ∀ p : List Mono4, evalPoly4 x0 x1 x2 x3 (negPoly4 p) = -evalPoly4 x0 x1 x2 x3 p
  | [] => by simp [negPoly4, evalPoly4]
  | m :: ms => by
    simp only [negPoly4, evalPoly4, evalPoly4_negPoly4 x0 x1 x2 x3 ms, evalMono4]
    rw [Int.neg_mul]; omega

def mulMonoMono4 (a b : Mono4) : Mono4 :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1, a.2.2.2.1 + b.2.2.2.1, a.2.2.2.2 * b.2.2.2.2)

theorem evalMono4_mulMonoMono4 (x0 x1 x2 x3 : Int) (a b : Mono4) :
    evalMono4 x0 x1 x2 x3 (mulMonoMono4 a b) =
      evalMono4 x0 x1 x2 x3 a * evalMono4 x0 x1 x2 x3 b := by
  unfold evalMono4 mulMonoMono4
  simp only [intPowNat_add]
  generalize a.2.2.2.2 = ca, b.2.2.2.2 = cb,
    intPowNat x0 a.1 = A0, intPowNat x0 b.1 = B0,
    intPowNat x1 a.2.1 = A1, intPowNat x1 b.2.1 = B1,
    intPowNat x2 a.2.2.1 = A2, intPowNat x2 b.2.2.1 = B2,
    intPowNat x3 a.2.2.2.1 = A3, intPowNat x3 b.2.2.2.1 = B3
  have h3 : (A2 * B2) * (A3 * B3) = (A2 * A3) * (B2 * B3) := by
    rw [Int.mul_assoc A2 B2 (A3 * B3), ← Int.mul_assoc B2 A3 B3,
        Int.mul_comm B2 A3, Int.mul_assoc A3 B2 B3, ← Int.mul_assoc A2 A3]
  have h2 : (A1 * B1) * ((A2 * A3) * (B2 * B3)) = (A1 * (A2 * A3)) * (B1 * (B2 * B3)) := by
    rw [Int.mul_assoc A1 B1, ← Int.mul_assoc B1 (A2 * A3),
        Int.mul_comm B1 (A2 * A3), Int.mul_assoc (A2 * A3) B1, ← Int.mul_assoc A1 (A2 * A3)]
  have h1 : (A0 * B0) * ((A1 * (A2 * A3)) * (B1 * (B2 * B3))) =
      (A0 * (A1 * (A2 * A3))) * (B0 * (B1 * (B2 * B3))) := by
    rw [Int.mul_assoc A0 B0, ← Int.mul_assoc B0 (A1 * (A2 * A3)),
        Int.mul_comm B0 (A1 * (A2 * A3)), Int.mul_assoc (A1 * (A2 * A3)) B0,
        ← Int.mul_assoc A0 (A1 * (A2 * A3))]
  rw [h3, h2, h1]
  rw [Int.mul_assoc ca cb, ← Int.mul_assoc cb (A0 * (A1 * (A2 * A3))),
      Int.mul_comm cb (A0 * (A1 * (A2 * A3))),
      Int.mul_assoc (A0 * (A1 * (A2 * A3))) cb, ← Int.mul_assoc ca]

def mulMonoPoly4 (m : Mono4) : List Mono4 -> List Mono4
  | [] => []
  | h :: rest =>
    let prod := mulMonoMono4 m h
    if isZeroInt prod.2.2.2.2 then mulMonoPoly4 m rest
    else prod :: mulMonoPoly4 m rest

theorem evalPoly4_mulMonoPoly4 (x0 x1 x2 x3 : Int) (m : Mono4) :
    ∀ p : List Mono4,
      evalPoly4 x0 x1 x2 x3 (mulMonoPoly4 m p) =
        evalMono4 x0 x1 x2 x3 m * evalPoly4 x0 x1 x2 x3 p
  | [] => by simp [mulMonoPoly4, evalPoly4]
  | h :: rest => by
    unfold mulMonoPoly4
    dsimp only
    cases hz : isZeroInt (mulMonoMono4 m h).2.2.2.2 with
    | true =>
      have hc0 : (mulMonoMono4 m h).2.2.2.2 = 0 := (isZeroInt_iff _).mp hz
      have hp0 : evalMono4 x0 x1 x2 x3 (mulMonoMono4 m h) = 0 := by
        unfold evalMono4; rw [hc0, Int.zero_mul]
      simp only [ite_true, evalPoly4, evalPoly4_mulMonoPoly4 x0 x1 x2 x3 m rest,
        Int.mul_add, ← evalMono4_mulMonoMono4, hp0, Int.zero_add]
    | false =>
      simp only [Bool.false_eq_true, ite_false, evalPoly4, evalMono4_mulMonoMono4,
        evalPoly4_mulMonoPoly4 x0 x1 x2 x3 m rest, Int.mul_add]

def mulPoly4 : List Mono4 -> List Mono4 -> List Mono4
  | [], _ => []
  | m :: ms, q => addPoly4 (mulMonoPoly4 m q) (mulPoly4 ms q)

theorem evalPoly4_mulPoly4 (x0 x1 x2 x3 : Int) :
    ∀ p q : List Mono4,
      evalPoly4 x0 x1 x2 x3 (mulPoly4 p q) =
        evalPoly4 x0 x1 x2 x3 p * evalPoly4 x0 x1 x2 x3 q
  | [], _ => by simp [mulPoly4, evalPoly4]
  | m :: ms, q => by
    simp only [mulPoly4, evalPoly4, evalPoly4_addPoly4, evalPoly4_mulMonoPoly4,
      evalPoly4_mulPoly4 x0 x1 x2 x3 ms q, Int.add_mul]

inductive Expr4 where
  | const (c : Int)
  | v0 | v1 | v2 | v3
  | add (a b : Expr4)
  | sub (a b : Expr4)
  | mul (a b : Expr4)
  deriving DecidableEq

def evalExpr4 (x0 x1 x2 x3 : Int) : Expr4 -> Int
  | .const c => c
  | .v0 => x0 | .v1 => x1 | .v2 => x2 | .v3 => x3
  | .add a b => evalExpr4 x0 x1 x2 x3 a + evalExpr4 x0 x1 x2 x3 b
  | .sub a b => evalExpr4 x0 x1 x2 x3 a - evalExpr4 x0 x1 x2 x3 b
  | .mul a b => evalExpr4 x0 x1 x2 x3 a * evalExpr4 x0 x1 x2 x3 b

def normExpr4 : Expr4 -> List Mono4
  | .const c => if isZeroInt c then [] else [(0, 0, 0, 0, c)]
  | .v0 => [(1, 0, 0, 0, 1)]
  | .v1 => [(0, 1, 0, 0, 1)]
  | .v2 => [(0, 0, 1, 0, 1)]
  | .v3 => [(0, 0, 0, 1, 1)]
  | .add a b => addPoly4 (normExpr4 a) (normExpr4 b)
  | .sub a b => addPoly4 (normExpr4 a) (negPoly4 (normExpr4 b))
  | .mul a b => mulPoly4 (normExpr4 a) (normExpr4 b)

theorem evalPoly4_normExpr4 (x0 x1 x2 x3 : Int) :
    ∀ e : Expr4, evalPoly4 x0 x1 x2 x3 (normExpr4 e) = evalExpr4 x0 x1 x2 x3 e
  | .const c => by
    unfold normExpr4 evalExpr4
    cases hz : isZeroInt c with
    | true => rw [(isZeroInt_iff c).mp hz]; simp [evalPoly4]
    | false => simp [evalPoly4, evalMono4, intPowNat]
  | .v0 => by simp [normExpr4, evalPoly4, evalMono4, intPowNat, evalExpr4]
  | .v1 => by simp [normExpr4, evalPoly4, evalMono4, intPowNat, evalExpr4]
  | .v2 => by simp [normExpr4, evalPoly4, evalMono4, intPowNat, evalExpr4]
  | .v3 => by simp [normExpr4, evalPoly4, evalMono4, intPowNat, evalExpr4]
  | .add a b => by
    simp [normExpr4, evalExpr4, evalPoly4_addPoly4,
      evalPoly4_normExpr4 x0 x1 x2 x3 a, evalPoly4_normExpr4 x0 x1 x2 x3 b]
  | .sub a b => by
    simp only [normExpr4, evalExpr4, evalPoly4_addPoly4, evalPoly4_negPoly4,
      evalPoly4_normExpr4 x0 x1 x2 x3 a, evalPoly4_normExpr4 x0 x1 x2 x3 b]
    omega
  | .mul a b => by
    simp [normExpr4, evalExpr4, evalPoly4_mulPoly4,
      evalPoly4_normExpr4 x0 x1 x2 x3 a, evalPoly4_normExpr4 x0 x1 x2 x3 b]

theorem expr4_eq_of_norm_sub_nil (a b : Expr4) (h : normExpr4 (.sub a b) = [])
    (x0 x1 x2 x3 : Int) :
    evalExpr4 x0 x1 x2 x3 a = evalExpr4 x0 x1 x2 x3 b := by
  have hev := evalPoly4_normExpr4 x0 x1 x2 x3 (.sub a b)
  rw [h] at hev
  simp only [evalPoly4, evalExpr4] at hev
  omega

-- Normalized `List Mono4` Laplace Determinant Mirroring `intDet` (O(N^2) compressed minors!):

def poly4SubMat {L : Nat} (P : Fin (L + 1) -> Fin (L + 1) -> List Mono4) (col : Fin (L + 1)) :
    Fin L -> Fin L -> List Mono4 :=
  fun i j => P ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ (skipFinIdx col j)

def poly4SumPrefix (L : Nat) (f : Fin L -> List Mono4) : Nat -> List Mono4
  | 0 => []
  | k + 1 =>
    addPoly4 (poly4SumPrefix L f k) (if h : k < L then f ⟨k, h⟩ else [])

def poly4Det : (L : Nat) -> (Fin L -> Fin L -> List Mono4) -> List Mono4
  | 0, _ => [(0, 0, 0, 0, 1)]
  | L + 1, P =>
    poly4SumPrefix (L + 1) (fun j =>
      match P ⟨0, Nat.zero_lt_succ L⟩ j with
      | [] => []
      | p0j =>
        let signed := if j.val % 2 = 0 then p0j else negPoly4 p0j
        mulPoly4 signed (poly4Det L (poly4SubMat P j))) (L + 1)

theorem evalPoly4_sumPrefix (x0 x1 x2 x3 : Int) (L : Nat) (f : Fin L -> List Mono4) :
    ∀ k : Nat,
      evalPoly4 x0 x1 x2 x3 (poly4SumPrefix L f k) =
        intSumPrefix L (fun j => evalPoly4 x0 x1 x2 x3 (f j)) k
  | 0 => rfl
  | k + 1 => by
    simp only [poly4SumPrefix, evalPoly4_addPoly4,
      evalPoly4_sumPrefix x0 x1 x2 x3 L f k, intSumPrefix]
    by_cases hk : k < L <;> simp [hk, evalPoly4]

theorem evalPoly4_det (x0 x1 x2 x3 : Int) :
    ∀ (L : Nat) (P : Fin L -> Fin L -> List Mono4),
      evalPoly4 x0 x1 x2 x3 (poly4Det L P) =
        intDet L (fun i j => evalPoly4 x0 x1 x2 x3 (P i j))
  | 0, _ => by simp [poly4Det, intDet, evalPoly4, evalMono4, intPowNat]
  | L + 1, P => by
    simp only [poly4Det, intDet, intSumFin]
    rw [evalPoly4_sumPrefix x0 x1 x2 x3 (L + 1)]
    have hcong : ∀ k : Nat,
        intSumPrefix (L + 1) (fun j =>
          evalPoly4 x0 x1 x2 x3
            (match P ⟨0, Nat.zero_lt_succ L⟩ j with
             | [] => []
             | p0j =>
               mulPoly4 (if j.val % 2 = 0 then p0j else negPoly4 p0j)
                 (poly4Det L (poly4SubMat P j)))) k =
        intSumPrefix (L + 1) (fun j =>
          (if j.val % 2 = 0 then (1 : Int) else -1) *
            evalPoly4 x0 x1 x2 x3 (P ⟨0, Nat.zero_lt_succ L⟩ j) *
            intDet L (intSubMat (fun i c => evalPoly4 x0 x1 x2 x3 (P i c)) j)) k := by
      intro k
      induction k with
      | zero => rfl
      | succ k' ih =>
        simp only [intSumPrefix, ih]
        by_cases hk : k' < L + 1
        · simp only [hk, dite_true]
          apply congrArg (intSumPrefix (L + 1) _ k' + ·)
          cases hp : P ⟨0, Nat.zero_lt_succ L⟩ ⟨k', hk⟩ with
          | nil => simp [evalPoly4]
          | cons m0 ms0 =>
            rw [evalPoly4_mulPoly4, evalPoly4_det x0 x1 x2 x3 L (poly4SubMat P ⟨k', hk⟩)]
            have hsub_eq : (fun i c => evalPoly4 x0 x1 x2 x3 (poly4SubMat P ⟨k', hk⟩ i c)) =
                intSubMat (fun i c => evalPoly4 x0 x1 x2 x3 (P i c)) ⟨k', hk⟩ := rfl
            rw [hsub_eq]
            by_cases hev : k' % 2 = 0
            · simp [hev]
            · simp only [hev, ite_false, evalPoly4_negPoly4]
              generalize evalPoly4 x0 x1 x2 x3 (m0 :: ms0) = A,
                intDet L (intSubMat (fun i c => evalPoly4 x0 x1 x2 x3 (P i c)) ⟨k', hk⟩) = B
              have hneg : (-1 : Int) * A * B = -(A * B) := by
                rw [Int.mul_assoc (-1 : Int)]; omega
              have hneg2 : (-A) * B = -(A * B) := Int.neg_mul A B
              rw [hneg, hneg2]
        · simp [hk]
    exact hcong (L + 1)

theorem poly4Det_eq_of_sub_nil {L : Nat} (E : Fin L -> Fin L -> Expr4) (closed : Expr4)
    (h : addPoly4 (poly4Det L (fun i j => normExpr4 (E i j))) (negPoly4 (normExpr4 closed)) = [])
    (x0 x1 x2 x3 : Int) :
    intDet L (fun i j => evalExpr4 x0 x1 x2 x3 (E i j)) = evalExpr4 x0 x1 x2 x3 closed := by
  have hev := congrArg (evalPoly4 x0 x1 x2 x3) h
  rw [evalPoly4_addPoly4, evalPoly4_negPoly4, evalPoly4_det, evalPoly4_normExpr4] at hev
  have hmat : (fun i j => evalPoly4 x0 x1 x2 x3 (normExpr4 (E i j))) =
      (fun i j => evalExpr4 x0 x1 x2 x3 (E i j)) := by
    funext i j; exact evalPoly4_normExpr4 x0 x1 x2 x3 (E i j)
  rw [hmat] at hev
  simp only [evalPoly4] at hev
  omega

-- `6 x 6` Single-Base `(T = 2, U = 3)` and Two-Base `(T = 2, U = 3)` Schneider–Laurent Matrices:

def laurentRowsSingle6 (i : Fin 6) : Nat × Nat := (i.val, 0)

def laurentRowsTwoBase6 (i : Fin 6) : Nat × Nat :=
  match i.val with
  | 0 => (0, 0) | 1 => (1, 0)
  | 2 => (0, 1) | 3 => (1, 1)
  | 4 => (0, 2) | _ => (1, 2)

def laurentColsC23_6 (u : Nat) (j : Fin 6) : Nat × Nat :=
  match j.val with
  | 0 => (0, 0)     | 1 => (1, 0)
  | 2 => (0, u)     | 3 => (1, u)
  | 4 => (0, 2 * u) | _ => (1, 2 * u)

def laurentSingleC23Mat6 (W u : Nat) : Fin 6 -> Fin 6 -> Int :=
  laurentInterpMat W 1 6 laurentRowsSingle6 (laurentColsC23_6 u)

def laurentTwoBaseMat6 (W K u : Nat) : Fin 6 -> Fin 6 -> Int :=
  laurentInterpMat W K 6 laurentRowsTwoBase6 (laurentColsC23_6 u)

def expr4Pow : Expr4 -> Nat -> Expr4
  | _, 0 => .const 1
  | e, n + 1 => .mul e (expr4Pow e n)

def singleC23ExprMat6 (i j : Fin 6) : Expr4 :=
  -- Variables: `v0 = W`, `v2 = P = 2^u`:
  let r := i.val
  let t := j.val % 2
  let kb := j.val / 2
  if t = 0 then
    expr4Pow .v2 (r * kb)
  else if r = 0 then
    .const 0
  else
    .mul (.mul (.const (r : Int)) .v0) (expr4Pow .v2 (r * kb))

def singleC23ClosedExpr : Expr4 :=
  .mul (expr4Pow .v0 3)
    (.mul (expr4Pow .v2 7)
      (.mul (expr4Pow (.sub .v2 (.const 1)) 12) (expr4Pow (.add .v2 (.const 1)) 4)))

def twoBaseExprMat6 (i j : Fin 6) : Expr4 :=
  -- Variables: `v0 = W`, `v1 = K`, `v2 = P = 2^u`, `v3 = Q = 3^u`:
  let rs := laurentRowsTwoBase6 i
  let r := rs.1
  let s := rs.2
  let t := j.val % 2
  let kb := j.val / 2
  let powPQ := .mul (expr4Pow .v2 (r * kb)) (expr4Pow .v3 (s * kb))
  if t = 0 then
    powPQ
  else if r = 0 ∧ s = 0 then
    .const 0
  else
    let linWK := .add (.mul (.const (r : Int)) .v0) (.mul (.const (s : Int)) .v1)
    .mul linWK powPQ

def twoBaseClosedExpr : Expr4 :=
  let W := Expr4.v0
  let K := Expr4.v1
  let P := Expr4.v2
  let Q := Expr4.v3
  let p := Expr4.sub P (.const 1)
  let q := Expr4.sub Q (.const 1)
  let pref := Expr4.mul P (.mul (expr4Pow Q 2) (expr4Pow q 3))
  let lin := Expr4.sub
    (.mul (.mul P (.sub (expr4Pow Q 2) (.const 1))) W)
    (.mul (.mul Q (.sub (expr4Pow P 2) (.const 1))) K)
  let quad := Expr4.sub
    (.add
      (.mul (.mul (.mul P (expr4Pow q 2)) (.add Q (.const 1))) (expr4Pow W 2))
      (.mul (.mul (.mul Q (.sub (expr4Pow P 2) (.const 1))) q) (.mul W K)))
    (.mul (.mul (.mul (.const 2) Q) (.mul (expr4Pow p 2) (.add Q (.const 1)))) (expr4Pow K 2))
  .mul pref (.mul lin quad)

theorem singleC23_poly_identity :
    addPoly4 (poly4Det 6 (fun i j => normExpr4 (singleC23ExprMat6 i j)))
      (negPoly4 (normExpr4 singleC23ClosedExpr)) = [] := by decide

set_option maxRecDepth 16384 in
theorem twoBase6_poly_identity :
    addPoly4 (poly4Det 6 (fun i j => normExpr4 (twoBaseExprMat6 i j)))
      (negPoly4 (normExpr4 twoBaseClosedExpr)) = [] := by decide

-- 3-Adic Infinite Descent for Quadratic Factor Non-Vanishing (`three_mul_sq_ne_sq_mul_nondiv3`):

theorem sq_mod3_ne_two (x : Nat) : (x * x) % 3 ≠ 2 := by
  have hr : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
  rw [Nat.mul_mod]
  rcases hr with h0 | h1 | h2
  · rw [h0]; decide
  · rw [h1]; decide
  · rw [h2]; decide

theorem non_sq_of_eq_sq_mul_mod3_two :
    ∀ (bound X Y D : Nat),
      Y ≤ bound -> Y ≥ 1 -> D % 3 = 2 ->
      X * X ≠ (Y * Y) * D
  | 0, _, Y, _, hY0, hY1, _ => by omega
  | bound + 1, X, Y, D, hYb, hY1, hD2 => by
    intro heq
    by_cases hY3 : Y % 3 = 0
    · have hX3 : X % 3 = 0 := by
        have hrhs0 : ((Y * Y) * D) % 3 = 0 := by
          rw [Nat.mul_mod, Nat.mul_mod Y Y 3, hY3]; simp
        rw [← heq] at hrhs0
        have hx_cases : X % 3 = 0 ∨ X % 3 = 1 ∨ X % 3 = 2 := by omega
        rw [Nat.mul_mod] at hrhs0
        rcases hx_cases with h0 | h1 | h2
        · exact h0
        · rw [h1] at hrhs0; simp at hrhs0
        · rw [h2] at hrhs0; simp at hrhs0
      let X' := X / 3
      let Y' := Y / 3
      have hX_eq : X = 3 * X' := by dsimp [X']; omega
      have hY_eq : Y = 3 * Y' := by dsimp [Y']; omega
      have heq9 : 9 * (X' * X') = 9 * ((Y' * Y') * D) := by
        have hl : (3 * X') * (3 * X') = 9 * (X' * X') := by
          calc
            (3 * X') * (3 * X') = 3 * (X' * (3 * X')) := Nat.mul_assoc 3 X' (3 * X')
            _ = 9 * (X' * X') := by rw [← Nat.mul_assoc X' 3 X', Nat.mul_comm X' 3, Nat.mul_assoc, ← Nat.mul_assoc 3 3]
        have hr : ((3 * Y') * (3 * Y')) * D = 9 * ((Y' * Y') * D) := by
          calc
            ((3 * Y') * (3 * Y')) * D = (3 * (Y' * (3 * Y'))) * D := by rw [Nat.mul_assoc 3 Y' (3 * Y')]
            _ = 9 * ((Y' * Y') * D) := by
                  rw [← Nat.mul_assoc Y' 3 Y', Nat.mul_comm Y' 3, Nat.mul_assoc 3 Y' Y',
                      ← Nat.mul_assoc 3 3, Nat.mul_assoc 9]
        rw [hX_eq, hY_eq, hl, hr] at heq
        exact heq
      exact non_sq_of_eq_sq_mul_mod3_two bound X' Y' D (by dsimp [Y']; omega) (by dsimp [Y']; omega)
        hD2 (by omega)
    · have hYY_1 : (Y * Y) % 3 = 1 := by
        have hy_c : Y % 3 = 1 ∨ Y % 3 = 2 := by omega
        rw [Nat.mul_mod]
        rcases hy_c with h1 | h2
        · rw [h1]
        · rw [h2]
      have hrhs2 : ((Y * Y) * D) % 3 = 2 := by rw [Nat.mul_mod, hYY_1, hD2]
      rw [← heq] at hrhs2
      exact sq_mod3_ne_two X hrhs2

theorem three_mul_sq_ne_sq_mul_nondiv3 :
    ∀ (bound X Y D : Nat),
      X ≤ bound -> X ≥ 1 -> Y ≥ 1 -> D % 3 ≠ 0 ->
      X * X ≠ 3 * (Y * Y) * D
  | 0, X, _, _, hX0, hX1, _, _ => by omega
  | bound + 1, X, Y, D, hXb, hX1, hY1, hD_nd3 => by
    intro heq
    have hX3 : X % 3 = 0 := by
      have hrhs0 : (3 * (Y * Y) * D) % 3 = 0 := by
        rw [Nat.mul_assoc 3, Nat.mul_mod_right]
      rw [← heq] at hrhs0
      have hx_c : X % 3 = 0 ∨ X % 3 = 1 ∨ X % 3 = 2 := by omega
      rw [Nat.mul_mod] at hrhs0
      rcases hx_c with h0 | h1 | h2
      · exact h0
      · rw [h1] at hrhs0; simp at hrhs0
      · rw [h2] at hrhs0; simp at hrhs0
    let X' := X / 3
    have hX_eq : X = 3 * X' := by dsimp [X']; omega
    have hXX : 3 * (X' * X') = (Y * Y) * D := by
      have hl : (3 * X') * (3 * X') = 3 * (3 * (X' * X')) := by
        calc
          (3 * X') * (3 * X') = 3 * (X' * (3 * X')) := Nat.mul_assoc 3 X' (3 * X')
          _ = 3 * (3 * (X' * X')) := by rw [← Nat.mul_assoc X' 3 X', Nat.mul_comm X' 3, Nat.mul_assoc]
      rw [hX_eq, hl, Nat.mul_assoc 3 (Y * Y) D] at heq
      omega
    have hY3 : Y % 3 = 0 := by
      have hlhs0 : (3 * (X' * X')) % 3 = 0 := Nat.mul_mod_right 3 _
      rw [hXX] at hlhs0
      by_cases hy0 : Y % 3 = 0
      · exact hy0
      · have hYY1 : (Y * Y) % 3 = 1 := by
          have hy_c : Y % 3 = 1 ∨ Y % 3 = 2 := by omega
          rw [Nat.mul_mod]
          rcases hy_c with h1 | h2
          · rw [h1]
          · rw [h2]
        rw [Nat.mul_mod, hYY1, Nat.one_mul, Nat.mod_mod] at hlhs0
        exact False.elim (hD_nd3 hlhs0)
    let Y' := Y / 3
    have hY_eq : Y = 3 * Y' := by dsimp [Y']; omega
    have heq' : X' * X' = 3 * (Y' * Y') * D := by
      have hr : ((3 * Y') * (3 * Y')) * D = 3 * (3 * (Y' * Y') * D) := by
        calc
          ((3 * Y') * (3 * Y')) * D = (3 * (Y' * (3 * Y'))) * D := by rw [Nat.mul_assoc 3 Y' (3 * Y')]
          _ = (3 * (3 * (Y' * Y'))) * D := by rw [← Nat.mul_assoc Y' 3 Y', Nat.mul_comm Y' 3, Nat.mul_assoc 3 Y' Y']
          _ = 3 * (3 * (Y' * Y') * D) := Nat.mul_assoc 3 _ D
      rw [hY_eq, hr] at hXX
      omega
    exact three_mul_sq_ne_sq_mul_nondiv3 bound X' Y' D
      (by dsimp [X']; omega) (by dsimp [X']; omega) (by dsimp [Y']; omega) hD_nd3 heq'

theorem pow3_gt_3_mul_pow2_ge3 : ∀ u : Nat, u ≥ 3 -> 3 ^ u > 3 * 2 ^ u
  | 0, hu => by omega
  | 1, hu => by omega
  | 2, hu => by omega
  | 3, _ => by decide
  | u + 4, _ => by
    have ih := pow3_gt_3_mul_pow2_ge3 (u + 3) (by omega)
    rw [Nat.pow_succ 3 (u + 3), Nat.pow_succ 2 (u + 3)]
    omega

set_option maxRecDepth 16384 in
/--
  Theorem W10.2c (`laurent_6x6_exact_factorization_and_zero_locus`, `zero custom axioms`):
  Pure-Integer `6 x 6` Single-Base & Two-Base Confluent Schneider–Laurent Exact Factorization,
  Bijective Zero Locus, Sign-Flip Dichotomy, & Collatz Convergent-Cone Non-Vanishing:
  1. **Single-Base `6 x 6` `(T = 2, U = 3)` Strict Positivity**:
       `intDet 6 (laurentSingleC23Mat6 W u) =
          ((W ^ 3 * (2 ^ u) ^ 7 * (2 ^ u - 1) ^ 12 * (2 ^ u + 1) ^ 4 : Nat) : Int) > 0`;
  2. **Two-Base `6 x 6` `(T = 2, U = 3)` Exact Factored Closed Form**:
     For ALL `W, K, u ≥ 1` (`P := 2 ^ u, Q := 3 ^ u, p := P - 1, q := Q - 1`),
       `intDet 6 (laurentTwoBaseMat6 W K u) =
          ((P * Q ^ 2 * q ^ 3 : Nat) : Int) *
          (((P * (Q ^ 2 - 1) * W : Nat) : Int) - ((Q * (P ^ 2 - 1) * K : Nat) : Int)) *
          (((P * q ^ 2 * (Q + 1) * W ^ 2 + Q * (P ^ 2 - 1) * q * W * K : Nat) : Int) -
           ((2 * Q * p ^ 2 * (Q + 1) * K ^ 2 : Nat) : Int))`;
  3. **Exact Bijective Zero Locus Across ALL `(W, K, u) ∈ (Z^+)^3`**:
       `intDet 6 (laurentTwoBaseMat6 W K u) = 0 ↔
          2 ^ u * (3 ^ (2 * u) - 1) * W = 3 ^ u * (2 ^ (2 * u) - 1) * K`!
     In particular, at **odd `u = 1`** and coprime `(W, K) = (9, 16)` (`3 ^ 9 < 2 ^ 16`),
     `intDet 6 (laurentTwoBaseMat6 9 16 1) = 0` (refuting odd-`u` non-vanishing on `6 x 6`!);
  4. **Sign Flip Inside `3 * K ≤ 5 * W` at `u = 1` & `u = 2`**:
     `intDet 6 (laurentTwoBaseMat6 2 3 1) > 0 ∧ intDet 6 (laurentTwoBaseMat6 5 8 1) < 0` AND
     `intDet 6 (laurentTwoBaseMat6 3 5 2) < 0 ∧ intDet 6 (laurentTwoBaseMat6 5 8 2) > 0`;
  5. **Unconditional Collatz Convergent-Cone Non-Vanishing (`∀ u ≥ 1`) & `u ≥ 3` Positivity**:
     For ALL `W, K, u ≥ 1` with `3 * K ≤ 5 * W`:
       `intDet 6 (laurentTwoBaseMat6 W K u) ≠ 0` AND (`u ≥ 3 -> intDet 6 ... > 0`)!
-/
theorem laurent_6x6_exact_factorization_and_zero_locus :
    (∀ W u : Nat, W ≥ 1 -> u ≥ 1 ->
      intDet 6 (laurentSingleC23Mat6 W u) =
        ((W ^ 3 * (2 ^ u) ^ 7 * (2 ^ u - 1) ^ 12 * (2 ^ u + 1) ^ 4 : Nat) : Int) ∧
      intDet 6 (laurentSingleC23Mat6 W u) > 0) ∧
    (∀ W K u : Nat, W ≥ 1 -> K ≥ 1 -> u ≥ 1 ->
      let P := 2 ^ u
      let Q := 3 ^ u
      let p := P - 1
      let q := Q - 1
      intDet 6 (laurentTwoBaseMat6 W K u) =
        ((P * Q ^ 2 * q ^ 3 : Nat) : Int) *
        (((P * (Q ^ 2 - 1) * W : Nat) : Int) - ((Q * (P ^ 2 - 1) * K : Nat) : Int)) *
        (((P * q ^ 2 * (Q + 1) * W ^ 2 + Q * (P ^ 2 - 1) * q * W * K : Nat) : Int) -
         ((2 * Q * p ^ 2 * (Q + 1) * K ^ 2 : Nat) : Int))) ∧
    (∀ W K u : Nat, W ≥ 1 -> K ≥ 1 -> u ≥ 1 ->
      (intDet 6 (laurentTwoBaseMat6 W K u) = 0 ↔
        2 ^ u * (3 ^ (2 * u) - 1) * W = 3 ^ u * (2 ^ (2 * u) - 1) * K)) ∧
    (Nat.gcd 9 16 = 1 ∧ 3 ^ 9 < 2 ^ 16 ∧ intDet 6 (laurentTwoBaseMat6 9 16 1) = 0 ∧
     intDet 6 (laurentTwoBaseMat6 2 3 1) > 0 ∧ intDet 6 (laurentTwoBaseMat6 5 8 1) < 0 ∧
     intDet 6 (laurentTwoBaseMat6 3 5 2) < 0 ∧ intDet 6 (laurentTwoBaseMat6 5 8 2) > 0) ∧
    (∀ W K u : Nat, W ≥ 1 -> K ≥ 1 -> 3 * K ≤ 5 * W -> u ≥ 1 ->
      intDet 6 (laurentTwoBaseMat6 W K u) ≠ 0 ∧
      (u ≥ 3 -> intDet 6 (laurentTwoBaseMat6 W K u) > 0)) := by
  have hintPow_cast : ∀ (n k : Nat), intPowNat (n : Int) k = ((n ^ k : Nat) : Int) := by
    intro n k
    induction k with
    | zero => rfl
    | succ k' ih =>
      simp only [intPowNat, ih, Nat.pow_succ, Nat.mul_comm (n ^ k') n, natCast_mul]
  have hexprPow_eval : ∀ (x0 x1 x2 x3 : Int) (e : Expr4) (k : Nat),
      evalExpr4 x0 x1 x2 x3 (expr4Pow e k) = intPowNat (evalExpr4 x0 x1 x2 x3 e) k := by
    intro x0 x1 x2 x3 e k
    induction k with
    | zero => rfl
    | succ k' ih => simp [expr4Pow, evalExpr4, intPowNat, ih]
  have hval6 : ∀ x : Fin 6,
      x.val = 0 ∨ x.val = 1 ∨ x.val = 2 ∨
      x.val = 3 ∨ x.val = 4 ∨ x.val = 5 := by decide
  -- Helper closed form for two-base `6 x 6`:
  have hdet_tb6 : ∀ W K u : Nat, W ≥ 1 -> K ≥ 1 -> u ≥ 1 ->
      let P := 2 ^ u
      let Q := 3 ^ u
      let p := P - 1
      let q := Q - 1
      intDet 6 (laurentTwoBaseMat6 W K u) =
        ((P * Q ^ 2 * q ^ 3 : Nat) : Int) *
        (((P * (Q ^ 2 - 1) * W : Nat) : Int) - ((Q * (P ^ 2 - 1) * K : Nat) : Int)) *
        (((P * q ^ 2 * (Q + 1) * W ^ 2 + Q * (P ^ 2 - 1) * q * W * K : Nat) : Int) -
         ((2 * Q * p ^ 2 * (Q + 1) * K ^ 2 : Nat) : Int)) := by
    intro W K u _ _ hu
    dsimp only
    let P := 2 ^ u
    let Q := 3 ^ u
    have hP_ge2 : P ≥ 2 := by dsimp [P]; simpa using pow2_mono_nat hu
    have hQ_ge3 : Q ≥ 3 := by
      dsimp [Q]; rw [show u = 1 + (u - 1) by omega, Nat.pow_add, Nat.pow_one]
      have hp := pow3_pos_nat (u - 1); omega
    have hmat_eq : laurentTwoBaseMat6 W K u =
        (fun i j => evalExpr4 (W : Int) (K : Int) (P : Int) (Q : Int) (twoBaseExprMat6 i j)) := by
      funext i j
      unfold laurentTwoBaseMat6 laurentInterpMat laurentInterpEntry twoBaseExprMat6
        laurentRowsTwoBase6 laurentColsC23_6
      have hp_int_mu : ∀ (b : Int) (m : Nat), b ^ (m * u) = intPowNat (b ^ u) m := by
        intro b m; induction m with
        | zero => simp [intPowNat]
        | succ m' ih => rw [Nat.succ_mul, Nat.add_comm _ u, Int.pow_add, ih]; rfl
      have hp_int_m2u : ∀ (b : Int) (m : Nat), b ^ (m * (2 * u)) = intPowNat (b ^ u) (m * 2) :=
        fun b m => by rw [← Nat.mul_assoc m 2 u, hp_int_mu]
      rcases hval6 i with hi | hi | hi | hi | hi | hi <;>
        rcases hval6 j with hj | hj | hj | hj | hj | hj <;>
        (rw [hi, hj]; dsimp [P, Q] at *;
         simp [laurentInterpBinom_zero_right, laurentInterpBinom_one_right,
           hexprPow_eval, evalExpr4, hp_int_mu, hp_int_m2u, intPowNat, Int.mul_assoc])
    have poly_eq := poly4Det_eq_of_sub_nil twoBaseExprMat6 twoBaseClosedExpr
      twoBase6_poly_identity (W : Int) (K : Int) (P : Int) (Q : Int)
    rw [← hmat_eq] at poly_eq
    rw [poly_eq]
    unfold twoBaseClosedExpr
    simp only [evalExpr4, hexprPow_eval, hintPow_cast]
    have hp_sub : (P : Int) - 1 = ((P - 1 : Nat) : Int) := by omega
    have hq_sub : (Q : Int) - 1 = ((Q - 1 : Nat) : Int) := by omega
    have hp2_ge1 : P ^ 2 ≥ 1 := nat_pow_pos_of_pos P (by omega) 2
    have hq2_ge1 : Q ^ 2 ≥ 1 := nat_pow_pos_of_pos Q (by omega) 2
    have hp2_sub : ((P ^ 2 : Nat) : Int) - 1 = ((P ^ 2 - 1 : Nat) : Int) := by omega
    have hq2_sub : ((Q ^ 2 : Nat) : Int) - 1 = ((Q ^ 2 - 1 : Nat) : Int) := by omega
    have hq1_add : (Q : Int) + 1 = ((Q + 1 : Nat) : Int) := rfl
    rw [hp_sub, hq_sub, hp2_sub, hq2_sub, hq1_add, hintPow_cast, hintPow_cast, hintPow_cast]
    dsimp [P, Q]
    simp only [Int.mul_assoc]
  -- Helper universal non-vanishing of the quadratic factor `Q_2(W, K, u) ≠ 0`:
  have hquad_nz : ∀ W K u : Nat, W ≥ 1 -> K ≥ 1 -> u ≥ 1 ->
      let P := 2 ^ u
      let Q := 3 ^ u
      let p := P - 1
      let q := Q - 1
      P * q ^ 2 * (Q + 1) * W ^ 2 + Q * (P ^ 2 - 1) * q * W * K ≠
        2 * Q * p ^ 2 * (Q + 1) * K ^ 2 := by
    intro W K u hW hK hu
    dsimp only
    intro heq_q
    let P := 2 ^ u
    let Q := 3 ^ u
    let p := P - 1
    let q := Q - 1
    have hP_ge2 : P ≥ 2 := by dsimp [P]; simpa using pow2_mono_nat hu
    have hQ_ge3 : Q ≥ 3 := by
      dsimp [Q]; rw [show u = 1 + (u - 1) by omega, Nat.pow_add, Nat.pow_one]
      have hp := pow3_pos_nat (u - 1); omega
    let al := P * q ^ 2 * (Q + 1)
    let be := Q * (P ^ 2 - 1) * q
    let ga := 2 * Q * p ^ 2 * (Q + 1)
    change al * W ^ 2 + be * W * K = ga * K ^ 2 at heq_q
    -- Complete the square in `Nat`: `(2 * al * W + be * K)^2 = (be^2 + 4 * al * ga) * K^2`!
    let X := 2 * al * W + be * K
    have hX_pos : X ≥ 1 := by
      have hq_pos : q ≥ 2 := by dsimp [q]; omega
      have hal_pos : al ≥ 1 := by
        dsimp [al]
        simpa using
          Nat.mul_le_mul
            (Nat.mul_le_mul (by omega : 1 ≤ P) (nat_pow_pos_of_pos q (by omega) 2))
            (by omega : 1 ≤ Q + 1)
      have hm : 2 ≤ 2 * al * W := by
        simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 (Nat.mul_le_mul hal_pos hW)
      dsimp [X]
      omega
    have hsq_id : X * X = (be * be + 4 * al * ga) * (K * K) := by
      -- Verify via `Expr4` on `(W, K, al, be)`? Even simpler: 4-line `Nat` expansion!
      dsimp [X]
      have hK2 : K ^ 2 = K * K := by rw [Nat.pow_succ, Nat.pow_one]
      have hW2 : W ^ 2 = W * W := by rw [Nat.pow_succ, Nat.pow_one]
      rw [hW2, hK2] at heq_q
      -- Multiply `heq_q` by `4 * al`:
      have hm4 := congrArg (4 * al * ·) heq_q
      -- `(2*al*W + be*K)^2 = 4*al*(al*(W*W) + be*W*K) + (be*be)*(K*K)`:
      have hlhs : (2 * al * W + be * K) * (2 * al * W + be * K) =
          4 * al * (al * (W * W) + be * W * K) + (be * be) * (K * K) := by
        have h_id := expr4_eq_of_norm_sub_nil
          (.mul (.add (.mul (.mul (.const 2) .v0) .v2) (.mul .v1 .v3))
                (.add (.mul (.mul (.const 2) .v0) .v2) (.mul .v1 .v3)))
          (.add (.mul (.mul (.const 4) .v0)
                      (.add (.mul .v0 (.mul .v2 .v2)) (.mul (.mul .v1 .v2) .v3)))
                (.mul (.mul .v1 .v1) (.mul .v3 .v3)))
          (by decide) (al : Int) (be : Int) (W : Int) (K : Int)
        simp only [evalExpr4, ← natCast_mul, ← Int.natCast_add] at h_id
        exact Int.ofNat.inj h_id
      have hrhs : 4 * al * (ga * (K * K)) + (be * be) * (K * K) =
          (be * be + 4 * al * ga) * (K * K) := by
        rw [← Nat.mul_assoc (4 * al) ga (K * K), Nat.add_comm, Nat.add_mul]
      rw [hlhs, hm4, hrhs]
    -- Factor `be * be + 4 * al * ga = Q * (p * q)^2 * D_rem` where `D_rem = Q * (P + 1)^2 + 8 * P * (Q + 1)^2`:
    let D_rem := Q * (P + 1) ^ 2 + 8 * P * (Q + 1) ^ 2
    have hdisc_fac : be * be + 4 * al * ga = Q * ((p * q) * (p * q)) * D_rem := by
      have hp2_fac : P ^ 2 - 1 = (P + 1) * p := by
        dsimp [p]
        let p0 := P - 1
        have hsp : P = p0 + 1 := by dsimp [p0]; omega
        rw [Nat.pow_succ P 1, Nat.pow_one, hsp,
            show p0 + 1 - 1 = p0 by omega,
            Nat.add_mul p0 1 (p0 + 1), Nat.one_mul, Nat.mul_add p0 p0 1, Nat.mul_one,
            Nat.add_mul (p0 + 1) 1 p0, Nat.one_mul, Nat.add_mul p0 1 p0, Nat.one_mul]
        generalize p0 * p0 = pp
        omega
      dsimp [be, al, ga, D_rem]
      rw [hp2_fac,
          Nat.pow_succ q 1, Nat.pow_one,
          Nat.pow_succ p 1, Nat.pow_one,
          Nat.pow_succ (P + 1) 1, Nat.pow_one,
          Nat.pow_succ (Q + 1) 1, Nat.pow_one]
      have h_id := expr4_eq_of_norm_sub_nil
        (.add (.mul (.mul (.mul .v3 (.mul (.add .v2 (.const 1)) .v0)) .v1)
                    (.mul (.mul .v3 (.mul (.add .v2 (.const 1)) .v0)) .v1))
              (.mul (.mul (.const 4) (.mul (.mul .v2 (.mul .v1 .v1)) (.add .v3 (.const 1))))
                    (.mul (.mul (.const 2) .v3) (.mul (.mul .v0 .v0) (.add .v3 (.const 1))))))
        (.mul (.mul .v3 (.mul (.mul .v0 .v1) (.mul .v0 .v1)))
              (.add (.mul .v3 (.mul (.add .v2 (.const 1)) (.add .v2 (.const 1))))
                    (.mul (.mul (.const 8) .v2) (.mul (.add .v3 (.const 1)) (.add .v3 (.const 1))))))
        (by decide) (p : Int) (q : Int) (P : Int) (Q : Int)
      have hc1 : (1 : Int) = ((1 : Nat) : Int) := rfl
      have hc2 : (2 : Int) = ((2 : Nat) : Int) := rfl
      have hc4 : (4 : Int) = ((4 : Nat) : Int) := rfl
      have hc8 : (8 : Int) = ((8 : Nat) : Int) := rfl
      simp only [evalExpr4] at h_id
      rw [hc1, hc2, hc4, hc8] at h_id
      simp only [← Int.natCast_add, ← natCast_mul] at h_id
      have hinj := Int.ofNat.inj h_id
      rwa [← Nat.mul_assoc (2 * Q) (p * p) (Q + 1)] at hinj
    rw [hdisc_fac] at hsq_id
    have hpqK_pos : p * q * K ≥ 1 := by
      simpa using
        Nat.mul_le_mul
          (Nat.mul_le_mul (by dsimp [p]; omega : 1 ≤ p) (by dsimp [q]; omega : 1 ≤ q))
          hK
    -- Parity dichotomy on `u`:
    by_cases hu_odd : u % 2 = 1
    · let m := u / 2
      have hu_eq : u = 2 * m + 1 := by dsimp [m]; omega
      have hQ_fac : Q = 3 * (3 ^ m * 3 ^ m) := by
        dsimp [Q]
        rw [hu_eq, Nat.pow_succ 3 (2 * m), Nat.mul_comm (3 ^ (2 * m)) 3,
            Nat.two_mul m, Nat.pow_add]
      have hP_m3 : P % 3 = 2 := by
        dsimp [P]
        rw [hu_eq, Nat.pow_succ, Nat.mul_comm _ 2, ← pow_pow_eq_mul_w5 2 2 m]
        have h4m : ∀ k : Nat, 4 ^ k % 3 = 1 := by
          intro k; induction k with
          | zero => rfl
          | succ k' ih => rw [Nat.pow_succ, Nat.mul_mod, ih]
        rw [Nat.mul_mod, h4m m]
      have hQ_m3 : Q % 3 = 0 := by rw [hQ_fac, Nat.mul_mod_right]
      have hD_m3 : D_rem % 3 = 1 := by
        dsimp [D_rem]
        rw [Nat.pow_succ (Q + 1) 1, Nat.pow_one, Nat.add_mod,
            Nat.mul_mod Q _, hQ_m3, Nat.zero_mul, Nat.zero_mod, Nat.zero_add, Nat.mod_mod,
            Nat.mul_mod (8 * P), Nat.mul_mod 8 P, hP_m3,
            Nat.mul_mod (Q + 1) (Q + 1) 3, Nat.add_mod Q 1 3, hQ_m3]
      let Y := 3 ^ m * (p * q * K)
      have hY_pos : Y ≥ 1 := Nat.mul_le_mul (pow3_pos_nat m) hpqK_pos
      have hrhs_rew : Q * ((p * q) * (p * q)) * D_rem * (K * K) = 3 * (Y * Y) * D_rem := by
        rw [hQ_fac]
        dsimp [Y]
        have h_id := expr4_eq_of_norm_sub_nil
          (.mul (.mul (.mul (.const 3) (.mul .v0 .v0)) (.mul .v1 .v1))
                (.mul .v3 (.mul .v2 .v2)))
          (.mul (.mul (.const 3) (.mul (.mul .v0 (.mul .v1 .v2)) (.mul .v0 (.mul .v1 .v2)))) .v3)
          (by decide) (3 ^ m : Int) ((p * q : Nat) : Int) (K : Int) (D_rem : Int)
        simp only [evalExpr4, ← natCast_mul] at h_id
        have hinj := Int.ofNat.inj h_id
        rwa [← Nat.mul_assoc _ D_rem (K * K)] at hinj
      rw [hrhs_rew] at hsq_id
      exact three_mul_sq_ne_sq_mul_nondiv3 X X Y D_rem (Nat.le_refl X) hX_pos hY_pos
        (by omega) hsq_id
    · -- Even `u = 2 * m` (`m ≥ 1`):
      let m := u / 2
      have hm1 : m ≥ 1 := by dsimp [m]; omega
      have hu_eq : u = 2 * m := by dsimp [m]; omega
      have hQ_fac : Q = 3 ^ m * 3 ^ m := by
        dsimp [Q]; rw [hu_eq, Nat.two_mul m, Nat.pow_add]
      have hP_m3 : P % 3 = 1 := by
        dsimp [P]; rw [hu_eq, ← pow_pow_eq_mul_w5 2 2 m]
        have h4m : ∀ k : Nat, 4 ^ k % 3 = 1 := by
          intro k; induction k with
          | zero => rfl
          | succ k' ih => rw [Nat.pow_succ, Nat.mul_mod, ih]
        exact h4m m
      have hQ_m3 : Q % 3 = 0 := by
        dsimp [Q]; rw [show u = (u - 1) + 1 by omega, Nat.pow_succ]; omega
      have hD_m3 : D_rem % 3 = 2 := by
        dsimp [D_rem]
        rw [Nat.pow_succ (Q + 1) 1, Nat.pow_one, Nat.add_mod,
            Nat.mul_mod Q _, hQ_m3, Nat.zero_mul, Nat.zero_mod, Nat.zero_add, Nat.mod_mod,
            Nat.mul_mod (8 * P), Nat.mul_mod 8 P, hP_m3,
            Nat.mul_mod (Q + 1) (Q + 1) 3, Nat.add_mod Q 1 3, hQ_m3]
      let Y := 3 ^ m * (p * q * K)
      have hY_pos : Y ≥ 1 := Nat.mul_le_mul (pow3_pos_nat m) hpqK_pos
      have hrhs_rew : Q * ((p * q) * (p * q)) * D_rem * (K * K) = (Y * Y) * D_rem := by
        rw [hQ_fac]
        dsimp [Y]
        have h_id := expr4_eq_of_norm_sub_nil
          (.mul (.mul (.mul .v0 .v0) (.mul .v1 .v1)) (.mul .v3 (.mul .v2 .v2)))
          (.mul (.mul (.mul .v0 (.mul .v1 .v2)) (.mul .v0 (.mul .v1 .v2))) .v3)
          (by decide) (3 ^ m : Int) ((p * q : Nat) : Int) (K : Int) (D_rem : Int)
        simp only [evalExpr4, ← natCast_mul] at h_id
        have hinj := Int.ofNat.inj h_id
        rwa [← Nat.mul_assoc _ D_rem (K * K)] at hinj
      rw [hrhs_rew] at hsq_id
      exact non_sq_of_eq_sq_mul_mod3_two Y X Y D_rem (Nat.le_refl Y) hY_pos hD_m3 hsq_id
  refine ⟨?_, hdet_tb6, ?_, ?_, ?_⟩
  · -- Part 1: Single-base `6 x 6` `(T = 2, U = 3)` closed form & strict positivity:
    intro W u hW hu
    let P := 2 ^ u
    have hP_ge2 : P ≥ 2 := by dsimp [P]; simpa using pow2_mono_nat hu
    have hmat_eq : laurentSingleC23Mat6 W u =
        (fun i j => evalExpr4 (W : Int) 1 (P : Int) 1 (singleC23ExprMat6 i j)) := by
      funext i j
      unfold laurentSingleC23Mat6 laurentInterpMat laurentInterpEntry singleC23ExprMat6
        laurentRowsSingle6 laurentColsC23_6
      have hp_int_mu : ∀ (b : Int) (m : Nat), b ^ (m * u) = intPowNat (b ^ u) m := by
        intro b m; induction m with
        | zero => simp [intPowNat]
        | succ m' ih => rw [Nat.succ_mul, Nat.add_comm _ u, Int.pow_add, ih]; rfl
      have hp_int_m2u : ∀ (b : Int) (m : Nat), b ^ (m * (2 * u)) = intPowNat (b ^ u) (m * 2) :=
        fun b m => by rw [← Nat.mul_assoc m 2 u, hp_int_mu]
      rcases hval6 i with hi | hi | hi | hi | hi | hi <;>
        rcases hval6 j with hj | hj | hj | hj | hj | hj <;>
        (rw [hi, hj]; dsimp [P] at *;
         simp [laurentInterpBinom_zero_right, laurentInterpBinom_one_right,
           hexprPow_eval, evalExpr4, hp_int_mu, hp_int_m2u, intPowNat, Int.mul_assoc])
    have poly_eq := poly4Det_eq_of_sub_nil singleC23ExprMat6 singleC23ClosedExpr
      singleC23_poly_identity (W : Int) 1 (P : Int) 1
    rw [← hmat_eq] at poly_eq
    have hval : intDet 6 (laurentSingleC23Mat6 W u) =
        ((W ^ 3 * P ^ 7 * (P - 1) ^ 12 * (P + 1) ^ 4 : Nat) : Int) := by
      rw [poly_eq]
      unfold singleC23ClosedExpr
      simp only [evalExpr4, hexprPow_eval, hintPow_cast]
      have hp_sub : (P : Int) - 1 = ((P - 1 : Nat) : Int) := by omega
      have hp_add : (P : Int) + 1 = ((P + 1 : Nat) : Int) := rfl
      rw [hp_sub, hp_add, hintPow_cast, hintPow_cast]
      simp only [Int.natCast_mul, Int.mul_assoc]
    have hpos_nat : W ^ 3 * P ^ 7 * (P - 1) ^ 12 * (P + 1) ^ 4 ≥ 1 := by
      simpa using
        Nat.mul_le_mul
          (Nat.mul_le_mul
            (Nat.mul_le_mul (nat_pow_pos_of_pos W hW 3) (nat_pow_pos_of_pos P (by omega) 7))
            (nat_pow_pos_of_pos (P - 1) (by omega) 12))
          (nat_pow_pos_of_pos (P + 1) (by omega) 4)
    exact ⟨hval, by rw [hval]; omega⟩
  · -- Part 3: Exact bijective zero locus `intDet 6 ... = 0 ↔ 2^u * (3^(2u) - 1) * W = 3^u * (2^(2u) - 1) * K`:
    intro W K u hW hK hu
    rw [hdet_tb6 W K u hW hK hu]
    let P := 2 ^ u
    let Q := 3 ^ u
    let p := P - 1
    let q := Q - 1
    have hP_ge2 : P ≥ 2 := by dsimp [P]; simpa using pow2_mono_nat hu
    have hQ_ge3 : Q ≥ 3 := by
      dsimp [Q]; rw [show u = 1 + (u - 1) by omega, Nat.pow_add, Nat.pow_one]
      have hp := pow3_pos_nat (u - 1); omega
    have hpref_pos : P * Q ^ 2 * q ^ 3 ≥ 1 := by
      simpa using
        Nat.mul_le_mul
          (Nat.mul_le_mul (by omega : 1 ≤ P) (nat_pow_pos_of_pos Q (by omega) 2))
          (nat_pow_pos_of_pos q (by dsimp [q]; omega) 3)
    have hq_nz := hquad_nz W K u hW hK hu
    change P * q ^ 2 * (Q + 1) * W ^ 2 + Q * (P ^ 2 - 1) * q * W * K ≠
      2 * Q * p ^ 2 * (Q + 1) * K ^ 2 at hq_nz
    have h3_2u : 3 ^ (2 * u) = Q ^ 2 := by
      dsimp [Q]; rw [Nat.two_mul, Nat.pow_add, Nat.pow_succ, Nat.pow_one]
    have h2_2u : 2 ^ (2 * u) = P ^ 2 := by
      dsimp [P]; rw [Nat.two_mul, Nat.pow_add, Nat.pow_succ, Nat.pow_one]
    rw [h3_2u, h2_2u]
    let n1 := P * Q ^ 2 * q ^ 3
    let n2L := P * (Q ^ 2 - 1) * W
    let n2R := Q * (P ^ 2 - 1) * K
    let n3L := P * q ^ 2 * (Q + 1) * W ^ 2 + Q * (P ^ 2 - 1) * q * W * K
    let n3R := 2 * Q * p ^ 2 * (Q + 1) * K ^ 2
    change (n1 : Int) * ((n2L : Int) - (n2R : Int)) * ((n3L : Int) - (n3R : Int)) = 0 ↔
      n2L = n2R
    change n1 ≥ 1 at hpref_pos
    change n3L ≠ n3R at hq_nz
    constructor
    · intro hz
      rcases Int.mul_eq_zero.mp hz with h12 | h3
      · rcases Int.mul_eq_zero.mp h12 with h1 | h2 <;> omega
      · omega
    · intro heq
      rw [heq, Int.sub_self, Int.mul_zero, Int.zero_mul]
  · -- Part 4: Odd-`u = 1` `(9, 16)` zero & `u = 1, 2` sign flips inside `3 * K ≤ 5 * W`:
    refine ⟨by decide, by decide, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hdet_tb6 9 16 1 (by decide) (by decide) (by decide)]; decide
    · rw [hdet_tb6 2 3 1 (by decide) (by decide) (by decide)]; decide
    · rw [hdet_tb6 5 8 1 (by decide) (by decide) (by decide)]; decide
    · rw [hdet_tb6 3 5 2 (by decide) (by decide) (by decide)]; decide
    · rw [hdet_tb6 5 8 2 (by decide) (by decide) (by decide)]; decide
  · -- Part 5: Unconditional Collatz convergent-cone (`3 * K ≤ 5 * W`) non-vanishing & `u ≥ 3` positivity:
    intro W K u hW hK hcone hu
    let P := 2 ^ u
    let Q := 3 ^ u
    let p := P - 1
    let q := Q - 1
    have hP_ge2 : P ≥ 2 := by dsimp [P]; simpa using pow2_mono_nat hu
    have hQ_ge3 : Q ≥ 3 := by
      dsimp [Q]; rw [show u = 1 + (u - 1) by omega, Nat.pow_add, Nat.pow_one]
      have hp := pow3_pos_nat (u - 1); omega
    -- First show `P * (Q^2 - 1) * W > Q * (P^2 - 1) * K` for ALL `u ≥ 1` on `3 * K ≤ 5 * W`:
    have hlin_coef_gt : 3 * P * (Q ^ 2 - 1) > 5 * Q * (P ^ 2 - 1) := by
      by_cases hu1 : u = 1
      · subst hu1; dsimp [P, Q]; decide
      · by_cases hu2 : u = 2
        · subst hu2; dsimp [P, Q]; decide
        · have hu3 : u ≥ 3 := by omega
          have hQ_gt : Q > 3 * P := pow3_gt_3_mul_pow2_ge3 u hu3
          -- For `Q > 3 * P` and `Q ≥ 27`: `3 * P * (Q^2 - 1) ≥ 3 * P * (9 * P * Q / ...)`
          -- Direct: `Q^2 - 1 ≥ 3 * P * Q` (since `Q ≥ 3*P + 1 => Q^2 ≥ 3*P*Q + Q > 3*P*Q + 1`!):
          have hQ2_ge : Q ^ 2 - 1 ≥ 3 * P * Q := by
            rw [Nat.pow_succ Q 1, Nat.pow_one]
            have hm : (3 * P + 1) * Q ≤ Q * Q := Nat.mul_le_mul_right Q (by omega)
            rw [Nat.add_mul, Nat.one_mul] at hm
            omega
          have h9 : 3 * P * (Q ^ 2 - 1) ≥ 9 * P ^ 2 * Q := by
            have hm := Nat.mul_le_mul_left (3 * P) hQ2_ge
            rw [Nat.pow_succ P 1, Nat.pow_one]
            calc
              3 * P * (Q ^ 2 - 1) ≥ 3 * P * (3 * P * Q) := hm
              _ = 9 * (P * P) * Q := by
                    rw [← Nat.mul_assoc (3 * P) (3 * P) Q, Nat.mul_assoc 3 P (3 * P),
                        ← Nat.mul_assoc P 3 P, Nat.mul_comm P 3, Nat.mul_assoc 3 P P,
                        ← Nat.mul_assoc 3 3]
          have h5 : 5 * Q * (P ^ 2 - 1) < 9 * P ^ 2 * Q := by
            have hp2_pos : P ^ 2 ≥ 4 := by rw [Nat.pow_succ, Nat.pow_one]; exact Nat.mul_le_mul hP_ge2 hP_ge2
            have hlt1 : P ^ 2 - 1 < P ^ 2 := by omega
            have hm1 : (5 * Q) * (P ^ 2 - 1) < (5 * Q) * P ^ 2 :=
              Nat.mul_lt_mul_of_pos_left hlt1 (by omega)
            have hm2 : 5 * (Q * P ^ 2) < 9 * (Q * P ^ 2) :=
              Nat.mul_lt_mul_of_pos_right (by decide : 5 < 9) (Nat.mul_pos (by omega) (by omega))
            rw [Nat.mul_assoc 5 Q (P ^ 2), Nat.mul_comm Q (P ^ 2), ← Nat.mul_assoc 5 (P ^ 2) Q] at hm1
            rw [Nat.mul_comm Q (P ^ 2), ← Nat.mul_assoc 5 (P ^ 2) Q, ← Nat.mul_assoc 9 (P ^ 2) Q] at hm2
            exact Nat.lt_trans hm1 hm2
          omega
    have hlin_gt : P * (Q ^ 2 - 1) * W > Q * (P ^ 2 - 1) * K := by
      have h1 : 3 * (Q * (P ^ 2 - 1) * K) ≤ 5 * Q * (P ^ 2 - 1) * W := by
        have hm := Nat.mul_le_mul_left (Q * (P ^ 2 - 1)) hcone
        calc
          3 * (Q * (P ^ 2 - 1) * K)
              = (Q * (P ^ 2 - 1)) * (3 * K) := by
                rw [← Nat.mul_assoc 3, Nat.mul_comm 3 (Q * (P ^ 2 - 1)), Nat.mul_assoc]
          _ ≤ (Q * (P ^ 2 - 1)) * (5 * W) := hm
          _ = 5 * Q * (P ^ 2 - 1) * W := by
                rw [← Nat.mul_assoc (Q * (P ^ 2 - 1)) 5 W,
                    Nat.mul_comm (Q * (P ^ 2 - 1)) 5, Nat.mul_assoc 5 Q]
      have h2 : 5 * Q * (P ^ 2 - 1) * W < 3 * (P * (Q ^ 2 - 1) * W) := by
        have hm := Nat.mul_lt_mul_of_pos_right hlin_coef_gt hW
        rwa [Nat.mul_assoc 3 P, Nat.mul_assoc 3 (P * (Q ^ 2 - 1)) W] at hm
      omega
    have hnz : intDet 6 (laurentTwoBaseMat6 W K u) ≠ 0 := by
      rw [hdet_tb6 W K u hW hK hu]
      have hpref_pos : P * Q ^ 2 * q ^ 3 ≥ 1 := by
        simpa using
          Nat.mul_le_mul
            (Nat.mul_le_mul (by omega : 1 ≤ P) (nat_pow_pos_of_pos Q (by omega) 2))
            (nat_pow_pos_of_pos q (by dsimp [q]; omega) 3)
      have hq_nz := hquad_nz W K u hW hK hu
      let n1 := P * Q ^ 2 * q ^ 3
      let n2L := P * (Q ^ 2 - 1) * W
      let n2R := Q * (P ^ 2 - 1) * K
      let n3L := P * q ^ 2 * (Q + 1) * W ^ 2 + Q * (P ^ 2 - 1) * q * W * K
      let n3R := 2 * Q * p ^ 2 * (Q + 1) * K ^ 2
      change (n1 : Int) * ((n2L : Int) - (n2R : Int)) * ((n3L : Int) - (n3R : Int)) ≠ 0
      change n1 ≥ 1 at hpref_pos
      change n2L > n2R at hlin_gt
      change n3L ≠ n3R at hq_nz
      intro hz
      rcases Int.mul_eq_zero.mp hz with h12 | h3
      · rcases Int.mul_eq_zero.mp h12 with h1 | h2 <;> omega
      · omega
    refine ⟨hnz, ?_⟩
    intro hu3
    rw [hdet_tb6 W K u hW hK hu]
    -- Show `P * q^2 * (Q + 1) * W^2 + Q * (P^2 - 1) * q * W * K > 2 * Q * p^2 * (Q + 1) * K^2` for `u ≥ 3`:
    have hquad_pos :
        P * q ^ 2 * (Q + 1) * W ^ 2 + Q * (P ^ 2 - 1) * q * W * K >
          2 * Q * p ^ 2 * (Q + 1) * K ^ 2 := by
      by_cases hu3_eq : u = 3
      · subst hu3_eq
        dsimp [P, Q, p, q]
        rw [Nat.pow_succ W 1, Nat.pow_one, Nat.pow_succ K 1, Nat.pow_one]
        have hc1 : 74088 * (3 * K) * K ≤ 74088 * (5 * W) * K :=
          Nat.mul_le_mul_right K (Nat.mul_le_mul_left 74088 hcone)
        have hc2 : 237762 * W * (3 * K) ≤ 237762 * W * (5 * W) :=
          Nat.mul_le_mul_left (237762 * W) hcone
        have hpos_ww : W * W ≥ 1 := by simpa using Nat.mul_le_mul hW hW
        have hr1 : 74088 * (3 * K) * K = 3 * (74088 * (K * K)) := by
          rw [← Nat.mul_assoc 74088 3 K, Nat.mul_comm 74088 3, Nat.mul_assoc 3 74088 K,
              Nat.mul_assoc 3 (74088 * K) K, Nat.mul_assoc 74088 K K]
        have hr2 : 74088 * (5 * W) * K = 370440 * (W * K) := by
          rw [← Nat.mul_assoc 74088 5 W, show 74088 * 5 = 370440 from rfl, Nat.mul_assoc]
        rw [hr1, hr2] at hc1
        have hr3 : 237762 * W * (3 * K) = 3 * (237762 * (W * K)) := by
          rw [← Nat.mul_assoc (237762 * W) 3 K, Nat.mul_comm (237762 * W) 3,
              Nat.mul_assoc 3 (237762 * W) K, Nat.mul_assoc 237762 W K]
        have hr4 : 237762 * W * (5 * W) = 1188810 * (W * W) := by
          rw [← Nat.mul_assoc (237762 * W) 5 W, Nat.mul_assoc 237762 W 5, Nat.mul_comm W 5,
              ← Nat.mul_assoc 237762 5 W, show 237762 * 5 = 1188810 from rfl, Nat.mul_assoc]
        rw [hr3, hr4] at hc2
        have hw_assoc : 44226 * W * K = 44226 * (W * K) := Nat.mul_assoc _ _ _
        rw [hw_assoc]
        generalize W * W = WW, W * K = WK, K * K = KK at hc1 hc2 hpos_ww ⊢
        omega
      · -- For `u ≥ 4` (`u = d + 4`): `9 * 2^u * (3^u - 1)^2 > 50 * 3^u * (2^u - 1)^2`:
        have hu4 : u ≥ 4 := by omega
        have hineq_d : ∀ d : Nat,
            9 * 2 ^ (d + 4) * (3 ^ (d + 4) - 1) ^ 2 >
              50 * 3 ^ (d + 4) * (2 ^ (d + 4) - 1) ^ 2 := by
          intro d
          induction d with
          | zero => decide
          | succ d' ih =>
            let m := d' + 4
            have hm4 : m ≥ 4 := by dsimp [m]; omega
            change 9 * 2 ^ m * (3 ^ m - 1) ^ 2 > 50 * 3 ^ m * (2 ^ m - 1) ^ 2 at ih
            change 9 * 2 ^ (m + 1) * (3 ^ (m + 1) - 1) ^ 2 >
              50 * 3 ^ (m + 1) * (2 ^ (m + 1) - 1) ^ 2
            have hp2_16 : 2 ^ m ≥ 16 := by
              simpa using nat_pow_mono_exp_pos 2 4 m (by decide) hm4
            have hp3_81 : 3 ^ m ≥ 81 := by
              simpa using nat_pow_mono_exp_pos 3 4 m (by decide) hm4
            let A := 3 ^ m - 1
            let B := 2 ^ m - 1
            have hB15 : B ≥ 15 := by dsimp [B]; omega
            have h3m1 : 3 ^ (m + 1) - 1 = 3 * A + 2 := by
              dsimp [A]; rw [Nat.pow_succ 3 m]; omega
            have h2m1 : 2 ^ (m + 1) - 1 = 2 * B + 1 := by
              dsimp [B]; rw [Nat.pow_succ 2 m]; omega
            have hA_sq : (3 ^ (m + 1) - 1) ^ 2 ≥ 9 * A ^ 2 := by
              rw [h3m1, Nat.pow_succ _ 1, Nat.pow_one, Nat.pow_succ A 1, Nat.pow_one]
              have hm_le : (3 * A) * (3 * A) ≤ (3 * A + 2) * (3 * A + 2) :=
                Nat.mul_le_mul (by omega) (by omega)
              have h9a : (3 * A) * (3 * A) = 9 * (A * A) := by
                rw [Nat.mul_assoc 3 A (3 * A), ← Nat.mul_assoc A 3 A, Nat.mul_comm A 3,
                    Nat.mul_assoc 3 A A, ← Nat.mul_assoc 3 3]
              omega
            have hB_lin : 5 * (2 ^ (m + 1) - 1) ≤ 11 * B := by rw [h2m1]; omega
            have hB_sq : 25 * (2 ^ (m + 1) - 1) ^ 2 ≤ 121 * B ^ 2 := by
              have hm_b := Nat.mul_le_mul hB_lin hB_lin
              have hl : (5 * (2 ^ (m + 1) - 1)) * (5 * (2 ^ (m + 1) - 1)) =
                  25 * (2 ^ (m + 1) - 1) ^ 2 := by
                rw [Nat.pow_succ _ 1, Nat.pow_one, Nat.mul_assoc 5, ← Nat.mul_assoc _ 5,
                    Nat.mul_comm _ 5, Nat.mul_assoc 5, ← Nat.mul_assoc 5 5]
              have hr : (11 * B) * (11 * B) = 121 * B ^ 2 := by
                rw [Nat.pow_succ B 1, Nat.pow_one, Nat.mul_assoc 11, ← Nat.mul_assoc B 11,
                    Nat.mul_comm B 11, Nat.mul_assoc 11 B B, ← Nat.mul_assoc 11 11]
              rwa [hl, hr] at hm_b
            have hlhs_ge : 25 * (9 * 2 ^ (m + 1) * (3 ^ (m + 1) - 1) ^ 2) ≥
                450 * (9 * 2 ^ m * A ^ 2) := by
              rw [Nat.pow_succ 2 m]
              have hm_l := Nat.mul_le_mul_left (25 * (9 * (2 ^ m * 2))) hA_sq
              have hrew : 25 * (9 * (2 ^ m * 2)) * (9 * A ^ 2) = 450 * (9 * 2 ^ m * A ^ 2) := by
                rw [Nat.mul_comm (2 ^ m) 2, ← Nat.mul_assoc 9 2 (2 ^ m),
                    ← Nat.mul_assoc 25 (9 * 2) (2 ^ m), show 25 * (9 * 2) = 450 from rfl,
                    Nat.mul_assoc 450 (2 ^ m) (9 * A ^ 2), ← Nat.mul_assoc (2 ^ m) 9 (A ^ 2),
                    Nat.mul_comm (2 ^ m) 9, Nat.mul_assoc 9 (2 ^ m) (A ^ 2)]
              rwa [hrew, Nat.mul_assoc 25 (9 * (2 ^ m * 2))] at hm_l
            have hrhs_le : 25 * (50 * 3 ^ (m + 1) * (2 ^ (m + 1) - 1) ^ 2) ≤
                363 * (50 * 3 ^ m * B ^ 2) := by
              rw [Nat.pow_succ 3 m]
              have hm_r := Nat.mul_le_mul_left (3 * (50 * 3 ^ m)) hB_sq
              have hl : 3 * (50 * 3 ^ m) * (25 * (2 ^ (m + 1) - 1) ^ 2) =
                  25 * (50 * (3 ^ m * 3) * (2 ^ (m + 1) - 1) ^ 2) := by
                generalize (2 ^ (m + 1) - 1) ^ 2 = Z
                rw [Nat.mul_comm 3 (50 * 3 ^ m), Nat.mul_assoc 50 (3 ^ m) 3,
                    ← Nat.mul_assoc (50 * (3 ^ m * 3)) 25 Z, Nat.mul_comm (50 * (3 ^ m * 3)) 25,
                    Nat.mul_assoc 25 (50 * (3 ^ m * 3)) Z]
              have hr : 3 * (50 * 3 ^ m) * (121 * B ^ 2) = 363 * (50 * 3 ^ m * B ^ 2) := by
                rw [Nat.mul_comm 3 (50 * 3 ^ m), Nat.mul_assoc (50 * 3 ^ m) 3 (121 * B ^ 2),
                    ← Nat.mul_assoc 3 121 (B ^ 2), show 3 * 121 = 363 from rfl,
                    ← Nat.mul_assoc (50 * 3 ^ m) 363 (B ^ 2), Nat.mul_comm (50 * 3 ^ m) 363,
                    Nat.mul_assoc 363 (50 * 3 ^ m) (B ^ 2)]
              rwa [hl, hr] at hm_r
            change 9 * 2 ^ m * A ^ 2 > 50 * 3 ^ m * B ^ 2 at ih
            generalize 9 * 2 ^ m * A ^ 2 = XL, 50 * 3 ^ m * B ^ 2 = XR,
              9 * 2 ^ (m + 1) * (3 ^ (m + 1) - 1) ^ 2 = YL,
              50 * 3 ^ (m + 1) * (2 ^ (m + 1) - 1) ^ 2 = YR at ih hlhs_ge hrhs_le ⊢
            omega
        have hi4 : 9 * P * q ^ 2 > 50 * Q * p ^ 2 := by
          have h0 := hineq_d (u - 4)
          rwa [show u - 4 + 4 = u by omega] at h0
        have h9K_le : 9 * K ^ 2 ≤ 25 * W ^ 2 := by
          have hm := Nat.mul_le_mul hcone hcone
          have hl : (3 * K) * (3 * K) = 9 * K ^ 2 := by
            rw [Nat.pow_succ K 1, Nat.pow_one, Nat.mul_assoc 3 K (3 * K),
                ← Nat.mul_assoc K 3 K, Nat.mul_comm K 3, Nat.mul_assoc 3 K K, ← Nat.mul_assoc 3 3]
          have hr : (5 * W) * (5 * W) = 25 * W ^ 2 := by
            rw [Nat.pow_succ W 1, Nat.pow_one, Nat.mul_assoc 5 W (5 * W),
                ← Nat.mul_assoc W 5 W, Nat.mul_comm W 5, Nat.mul_assoc 5 W W, ← Nat.mul_assoc 5 5]
          rwa [hl, hr] at hm
        have hW2_pos : W ^ 2 ≥ 1 := nat_pow_pos_of_pos W hW 2
        have h1 : 9 * (2 * Q * p ^ 2 * (Q + 1) * K ^ 2) ≤
            (50 * Q * p ^ 2) * ((Q + 1) * W ^ 2) := by
          have hm := Nat.mul_le_mul_left (2 * Q * p ^ 2 * (Q + 1)) h9K_le
          have hl : (2 * Q * p ^ 2 * (Q + 1)) * (9 * K ^ 2) =
              9 * (2 * Q * p ^ 2 * (Q + 1) * K ^ 2) := by
            rw [← Nat.mul_assoc _ 9 (K ^ 2), Nat.mul_comm _ 9, Nat.mul_assoc]
          have hr : (2 * Q * p ^ 2 * (Q + 1)) * (25 * W ^ 2) =
              (50 * Q * p ^ 2) * ((Q + 1) * W ^ 2) := by
            rw [← Nat.mul_assoc (2 * Q * p ^ 2 * (Q + 1)) 25 (W ^ 2),
                Nat.mul_assoc (2 * Q * p ^ 2) (Q + 1) 25, Nat.mul_comm (Q + 1) 25,
                ← Nat.mul_assoc (2 * Q * p ^ 2) 25 (Q + 1), Nat.mul_comm (2 * Q * p ^ 2) 25,
                ← Nat.mul_assoc 25 (2 * Q) (p ^ 2), ← Nat.mul_assoc 25 2 Q,
                show 25 * 2 = 50 from rfl, Nat.mul_assoc (50 * Q * p ^ 2) (Q + 1) (W ^ 2)]
          rwa [hl, hr] at hm
        have h2 : (50 * Q * p ^ 2) * ((Q + 1) * W ^ 2) <
            9 * (P * q ^ 2 * (Q + 1) * W ^ 2) := by
          have hm := Nat.mul_lt_mul_of_pos_right hi4
            (Nat.mul_pos (by omega : 0 < Q + 1) hW2_pos)
          have hr : (9 * P * q ^ 2) * ((Q + 1) * W ^ 2) = 9 * (P * q ^ 2 * (Q + 1) * W ^ 2) := by
            rw [Nat.mul_assoc 9 P, Nat.mul_assoc 9 (P * q ^ 2),
                Nat.mul_assoc (P * q ^ 2) (Q + 1) (W ^ 2)]
          rwa [hr] at hm
        have hlt9 : 9 * (2 * Q * p ^ 2 * (Q + 1) * K ^ 2) < 9 * (P * q ^ 2 * (Q + 1) * W ^ 2) :=
          Nat.lt_of_le_of_lt h1 h2
        omega
    -- Product of three strictly positive `Int`s is strictly positive:
    have hpref_pos : P * Q ^ 2 * q ^ 3 ≥ 1 := by
      simpa using
        Nat.mul_le_mul
          (Nat.mul_le_mul (by omega : 1 ≤ P) (nat_pow_pos_of_pos Q (by omega) 2))
          (nat_pow_pos_of_pos q (by dsimp [q]; omega) 3)
    let n1 := P * Q ^ 2 * q ^ 3
    let n2L := P * (Q ^ 2 - 1) * W
    let n2R := Q * (P ^ 2 - 1) * K
    let n3L := P * q ^ 2 * (Q + 1) * W ^ 2 + Q * (P ^ 2 - 1) * q * W * K
    let n3R := 2 * Q * p ^ 2 * (Q + 1) * K ^ 2
    change (n1 : Int) * ((n2L : Int) - (n2R : Int)) * ((n3L : Int) - (n3R : Int)) > 0
    change n1 ≥ 1 at hpref_pos
    change n2L > n2R at hlin_gt
    change n3L > n3R at hquad_pos
    have hf1_pos : (n1 : Int) > 0 := by omega
    have hf2_pos : ((n2L : Int) - (n2R : Int)) > 0 := by omega
    have hf3_pos : ((n3L : Int) - (n3R : Int)) > 0 := by omega
    exact Int.mul_pos (Int.mul_pos hf1_pos hf2_pos) hf3_pos

-- ============================================================================
-- SECTION 3: Front C (Branches P1.2 & P5.9) — Beyond-Regular 2-Regular
--            Stern–Brocot & Non-Regular `∀ Q ≥ 1` 1-Counter Pushdown (`OCN`)
--            Preimage Impossibilities + 7th Solvable Cousin `T_diamond7` (`ω^5`)
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Section 3A.1: 2-Regular Stern–Brocot (`sternDiatomic`) Preimage Impossibility (`P1.2`)
-- ----------------------------------------------------------------------------

/-- Fuel-stabilized Stern–Brocot `2`-regular diatomic sequence (`s(0)=0, s(1)=1, s(2n)=s(n), s(2n+1)=s(n)+s(n+1)`). -/
def sternDiatomicAux : Nat -> Nat -> Nat
  | 0, _ => 0
  | _ + 1, 0 => 0
  | _ + 1, 1 => 1
  | fuel + 1, n =>
    if n % 2 = 0 then sternDiatomicAux fuel (n / 2)
    else sternDiatomicAux fuel (n / 2) + sternDiatomicAux fuel (n / 2 + 1)

def sternDiatomic (n : Nat) : Nat :=
  sternDiatomicAux (n + 1) n

theorem sternDiatomicAux_eq_of_gt :
    ∀ (f1 f2 n : Nat),
      n < f1 -> n < f2 ->
      sternDiatomicAux f1 n = sternDiatomicAux f2 n
  | 0, _, _, h1, _ => by omega
  | _, 0, _, _, h2 => by omega
  | f1 + 1, f2 + 1, n, h1, h2 => by
    cases n with
    | zero => rfl
    | succ m =>
      cases m with
      | zero => rfl
      | succ k =>
        change (if (k + 2) % 2 = 0 then sternDiatomicAux f1 ((k + 2) / 2)
                else sternDiatomicAux f1 ((k + 2) / 2) + sternDiatomicAux f1 ((k + 2) / 2 + 1)) =
               (if (k + 2) % 2 = 0 then sternDiatomicAux f2 ((k + 2) / 2)
                else sternDiatomicAux f2 ((k + 2) / 2) + sternDiatomicAux f2 ((k + 2) / 2 + 1))
        by_cases hev : (k + 2) % 2 = 0
        · rw [ite_true_of_w10 hev, ite_true_of_w10 hev]
          exact sternDiatomicAux_eq_of_gt f1 f2 ((k + 2) / 2) (by omega) (by omega)
        · rw [ite_false_of_w10 hev, ite_false_of_w10 hev,
              sternDiatomicAux_eq_of_gt f1 f2 ((k + 2) / 2) (by omega) (by omega),
              sternDiatomicAux_eq_of_gt f1 f2 ((k + 2) / 2 + 1) (by omega) (by omega)]

theorem sternDiatomic_even (k : Nat) :
    sternDiatomic (2 * k) = sternDiatomic k := by
  cases k with
  | zero => rfl
  | succ m =>
    unfold sternDiatomic
    have h2 : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
    conv => lhs; arg 2; rw [h2]
    change (if (2 * m + 2) % 2 = 0 then sternDiatomicAux (2 * (m + 1)) ((2 * m + 2) / 2)
            else sternDiatomicAux (2 * (m + 1)) ((2 * m + 2) / 2) +
                 sternDiatomicAux (2 * (m + 1)) ((2 * m + 2) / 2 + 1)) =
           sternDiatomicAux (m + 2) (m + 1)
    have hev : (2 * m + 2) % 2 = 0 := by omega
    have hdiv : (2 * m + 2) / 2 = m + 1 := by omega
    rw [ite_true_of_w10 hev, hdiv]
    exact sternDiatomicAux_eq_of_gt (2 * (m + 1)) (m + 2) (m + 1) (by omega) (by omega)

theorem sternDiatomic_odd (k : Nat) :
    sternDiatomic (2 * k + 1) = sternDiatomic k + sternDiatomic (k + 1) := by
  cases k with
  | zero => rfl
  | succ m =>
    unfold sternDiatomic
    have h2 : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by omega
    conv => lhs; arg 2; rw [h2]
    change (if (2 * m + 3) % 2 = 0 then sternDiatomicAux (2 * (m + 1) + 1) ((2 * m + 3) / 2)
            else sternDiatomicAux (2 * (m + 1) + 1) ((2 * m + 3) / 2) +
                 sternDiatomicAux (2 * (m + 1) + 1) ((2 * m + 3) / 2 + 1)) =
           sternDiatomicAux (m + 2) (m + 1) + sternDiatomicAux (m + 3) (m + 2)
    have hodd : ¬ ((2 * m + 3) % 2 = 0) := by omega
    have hdiv : (2 * m + 3) / 2 = m + 1 := by omega
    rw [ite_false_of_w10 hodd, hdiv,
        sternDiatomicAux_eq_of_gt (2 * (m + 1) + 1) (m + 2) (m + 1) (by omega) (by omega),
        sternDiatomicAux_eq_of_gt (2 * (m + 1) + 1) (m + 3) (m + 2) (by omega) (by omega)]

theorem sternDiatomic_pow2 : ∀ r : Nat, sternDiatomic (2 ^ r) = 1
  | 0 => rfl
  | r + 1 => by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ r) 2, sternDiatomic_even, sternDiatomic_pow2 r]

theorem sternDiatomic_three_mul_pow2 : ∀ r : Nat, sternDiatomic (3 * 2 ^ r) = 2
  | 0 => by decide
  | r + 1 => by
    rw [Nat.pow_succ, ← Nat.mul_assoc 3 (2 ^ r) 2, Nat.mul_comm (3 * 2 ^ r) 2,
        sternDiatomic_even, sternDiatomic_three_mul_pow2 r]

theorem sternDiatomic_mersenne : ∀ r : Nat, sternDiatomic (2 ^ r - 1) = r
  | 0 => rfl
  | r + 1 => by
    have hp := pow2_pos_nat r
    have hsplit : 2 ^ (r + 1) - 1 = 2 * (2 ^ r - 1) + 1 := by rw [Nat.pow_succ]; omega
    have hsucc : (2 ^ r - 1) + 1 = 2 ^ r := by omega
    rw [hsplit, sternDiatomic_odd, hsucc, sternDiatomic_mersenne r, sternDiatomic_pow2 r]

theorem sternDiatomic_three_mul_pow2_sub1 :
    ∀ r : Nat, sternDiatomic (3 * 2 ^ r - 1) = 2 * r + 1
  | 0 => by decide
  | r + 1 => by
    have hp := pow2_pos_nat r
    have hsplit : 3 * 2 ^ (r + 1) - 1 = 2 * (3 * 2 ^ r - 1) + 1 := by rw [Nat.pow_succ]; omega
    have hsucc : (3 * 2 ^ r - 1) + 1 = 3 * 2 ^ r := by omega
    rw [hsplit, sternDiatomic_odd, hsucc,
        sternDiatomic_three_mul_pow2_sub1 r, sternDiatomic_three_mul_pow2 r]
    omega

/--
  Theorem W10.3a (`stern_brocot_2regular_preimage_impossibility`, choice-free `zero custom axioms`):
  Universal `2`-Regular Stern–Brocot (`sternDiatomic`) Preimage Weight Impossibility (`Branch P1.2`):
  1. **Exact Mersenne `1`-Spine Affine Laws (`∀ r : Nat`)**:
     `sternDiatomic (2 ^ r - 1) = r`, `sternDiatomic (3 * 2 ^ r - 1) = 2 * r + 1`, and
     `sternDiatomic (2 * (3 * 2 ^ r - 1)) = 2 * r + 1` (proving `sternDiatomic` is unbounded
     and strictly non-finite-state!).
  2. **Concrete Even-Spine Invariance Collapse (`ZPOS_STERN_AND_OCN_PREIMAGE_COLLAPSE_56_VS_224`)**:
     At `m = 56` (`56 % 3 = 2`, `(2 * 56 - 1) / 3 = 37`),
     `sternDiatomic 56 = 3 ∧ sternDiatomic 112 = 3 ∧ sternDiatomic 224 = 3 ∧ sternDiatomic 37 = 11`,
     killing EVERY pure `1`-variable rational weight `fNum (sternDiatomic n) / fDen (sternDiatomic n)`
     in 1 step (`w(112) + w(37) = w(56) + w(37) ≤ θ * w(56)` contradicts `θ ≤ 1` and `w(37) > 0`)!
  3. **Universal Bivariate Polynomial-Quotient Impossibility (`∀ pTerms qTerms pTheta qTheta`)**:
     NO positive rational preimage weight of the form
       `w(n) = evalNatPoly2 pTerms (sternDiatomic n) (binBitLength n) /
               evalNatPoly2 qTerms (sternDiatomic n) (binBitLength n)`
     can satisfy `IsPositiveRationalPreimageWeight`!
-/
theorem stern_brocot_2regular_preimage_impossibility :
    (∀ r : Nat,
      sternDiatomic (2 ^ r - 1) = r ∧
      sternDiatomic (3 * 2 ^ r - 1) = 2 * r + 1 ∧
      sternDiatomic (2 * (3 * 2 ^ r - 1)) = 2 * r + 1) ∧
    (56 % 3 = 2 ∧ (2 * 56 - 1) / 3 = 37 ∧
     sternDiatomic 56 = 3 ∧ sternDiatomic 112 = 3 ∧
     sternDiatomic 224 = 3 ∧ sternDiatomic 37 = 11 ∧
     ∀ (fNum fDen : Nat -> Nat) (pTheta qTheta : Nat),
       ¬ IsPositiveRationalPreimageWeight
         (fun n => fNum (sternDiatomic n))
         (fun n => fDen (sternDiatomic n))
         pTheta qTheta) ∧
    (∀ (pTerms qTerms : NatPoly2) (pTheta qTheta : Nat),
      ¬ IsPositiveRationalPreimageWeight
        (fun n => evalNatPoly2 pTerms (sternDiatomic n) (binBitLength n))
        (fun n => evalNatPoly2 qTerms (sternDiatomic n) (binBitLength n))
        pTheta qTheta) := by
  refine ⟨fun r => ⟨sternDiatomic_mersenne r,
                    sternDiatomic_three_mul_pow2_sub1 r,
                    (sternDiatomic_even (3 * 2 ^ r - 1)).trans (sternDiatomic_three_mul_pow2_sub1 r)⟩,
          ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩, ?_⟩
  · -- Pure `f(sternDiatomic n)` collapse at `m = 56`:
    intro fNum fDen pTheta qTheta hw
    have hs56 : sternDiatomic 56 = 3 := by decide
    have hs112 : sternDiatomic 112 = 3 := by decide
    have hs37 : sternDiatomic 37 = 11 := by decide
    rcases hw.2.2.1 56 (by decide) with ⟨_, hden56⟩
    rcases hw.2.2.1 37 (by decide) with ⟨hnum37, _⟩
    dsimp only at hden56 hnum37
    rw [hs56] at hden56
    rw [hs37] at hnum37
    have hpre := hw.2.2.2.2 56 (by decide) (by decide)
    dsimp only at hpre
    change qTheta * ((fNum (sternDiatomic 112) * fDen (sternDiatomic 37) +
                      fNum (sternDiatomic 37) * fDen (sternDiatomic 112)) * fDen (sternDiatomic 56)) ≤
      pTheta * (fNum (sternDiatomic 56) * (fDen (sternDiatomic 112) * fDen (sternDiatomic 37))) at hpre
    rw [hs56, hs112, hs37] at hpre
    have hcanc := nat_mul_le_cancel_left_w5 qTheta _ _
      (Nat.lt_of_lt_of_le hw.1 hw.2.1)
      (Nat.le_trans hpre (Nat.mul_le_mul_right _ hw.2.1))
    have hpos : fNum 11 * (fDen 3 * fDen 3) ≥ 1 := by
      simpa using Nat.mul_le_mul hnum37 (Nat.mul_le_mul hden56 hden56)
    have hl : (fNum 3 * fDen 11 + fNum 11 * fDen 3) * fDen 3 =
        fNum 3 * (fDen 3 * fDen 11) + fNum 11 * (fDen 3 * fDen 3) := by
      rw [Nat.add_mul, Nat.mul_assoc (fNum 11) (fDen 3) (fDen 3),
          Nat.mul_assoc (fNum 3) (fDen 11) (fDen 3), Nat.mul_comm (fDen 11) (fDen 3)]
    rw [hl] at hcanc
    omega
  · -- Universal `NatPoly2(sternDiatomic n, binBitLength n)` collapse along Mersenne `1`-spines:
    intro pTerms qTerms pTheta qTheta hw
    let dP := maxDegNatPoly2 pTerms
    let dQ := maxDegNatPoly2 qTerms
    let D := dP + dQ
    let C : Nat := 5
    have hC_pos : C ≥ 1 := by decide
    let M_hi : Nat := 8
    have hMhi_ge1 : M_hi ≥ 1 := by decide
    let B_eff := M_hi ^ D
    have hBeff_pos : B_eff ≥ 1 := nat_pow_pos_of_pos M_hi hMhi_ge1 D
    let s := (B_eff + 1 + 1) * (D * C + 1) + 2
    have hs_ge2 : s ≥ 2 := by dsimp [s]; omega
    have hs_ge : s ≥ (B_eff + 1 + 1) * (D * C + 1) := by dsimp [s]; omega
    let ms1 := 3 * 2 ^ s - 1
    let evs1 := 2 * ms1
    let ns1 := 2 ^ (s + 1) - 1
    have hp2_ge4 : 2 ^ s ≥ 4 := by simpa using pow2_mono_nat hs_ge2
    have hms1_ge3 : ms1 ≥ 3 := by dsimp [ms1]; omega
    have hevs1_ge3 : evs1 ≥ 3 := by dsimp [evs1]; omega
    have hns1_ge3 : ns1 ≥ 3 := by dsimp [ns1]; rw [Nat.pow_succ]; omega
    rcases ripple_carry_alternating_cascade_and_mersenne_triples.2.2 (s + 1) (by omega) with
      ⟨hms1_m3_raw, hns1_div_raw, _, _, _, hbl_n_raw, hbl_m_raw, hbl_ev_raw⟩
    have hm_simp : 3 * 2 ^ (s + 1 - 1) - 1 = ms1 := by rw [Nat.add_sub_cancel]
    rw [hm_simp] at hms1_m3_raw hns1_div_raw hbl_m_raw hbl_ev_raw
    have hst_ms1 : sternDiatomic ms1 = s * 2 + 1 := by
      dsimp [ms1]; rw [sternDiatomic_three_mul_pow2_sub1 s, Nat.mul_comm 2 s]
    have hst_evs1 : sternDiatomic evs1 = s * 2 + 1 := by
      dsimp [evs1, ms1]
      rw [sternDiatomic_even, sternDiatomic_three_mul_pow2_sub1 s, Nat.mul_comm 2 s]
    have hst_ns1 : sternDiatomic ns1 = s * 1 + 1 := by
      dsimp [ns1]; rw [sternDiatomic_mersenne (s + 1), Nat.mul_one]
    have hbl_ms1 : binBitLength ms1 = s * 1 + 2 := by rw [hbl_m_raw, Nat.mul_one]
    have hbl_evs1 : binBitLength evs1 = s * 1 + 3 := by
      dsimp [evs1]; rw [hbl_ev_raw, Nat.mul_one]
    have hbl_ns1 : binBitLength ns1 = s * 1 + 1 := by
      dsimp [ns1] at hbl_n_raw ⊢; rw [hbl_n_raw, Nat.mul_one]
    have hpre := hw.2.2.2.2 ms1 hms1_ge3 hms1_m3_raw
    dsimp only at hpre
    rw [hns1_div_raw] at hpre
    have hcanc := nat_mul_le_cancel_left_w5 qTheta _ _
      (Nat.lt_of_lt_of_le hw.1 hw.2.1)
      (Nat.le_trans hpre (Nat.mul_le_mul_right _ hw.2.1))
    let P_m := evalNatPoly2 pTerms (sternDiatomic ms1) (binBitLength ms1)
    let Q_m := evalNatPoly2 qTerms (sternDiatomic ms1) (binBitLength ms1)
    let P_ev := evalNatPoly2 pTerms (sternDiatomic evs1) (binBitLength evs1)
    let Q_ev := evalNatPoly2 qTerms (sternDiatomic evs1) (binBitLength evs1)
    let P_n := evalNatPoly2 pTerms (sternDiatomic ns1) (binBitLength ns1)
    let Q_n := evalNatPoly2 qTerms (sternDiatomic ns1) (binBitLength ns1)
    change (P_ev * Q_n + P_n * Q_ev) * Q_m ≤ P_m * (Q_ev * Q_n) at hcanc
    have hPm_pos : P_m ≥ 1 := (hw.2.2.1 ms1 hms1_ge3).1
    have hQev_pos : Q_ev ≥ 1 := (hw.2.2.1 evs1 hevs1_ge3).2
    have hQn_pos : Q_n ≥ 1 := (hw.2.2.1 ns1 hns1_ge3).2
    have hsame1 : ∀ (k c1 c2 : Nat), k ≥ 1 -> c1 ≤ C ->
        s * (s * k + c1) ≤ (s + C) * (s * k + c2) := by
      intro k c1 c2 hk hc1
      have hkc : c1 ≤ k * C := Nat.le_trans hc1 (by simpa using Nat.mul_le_mul_right C hk)
      calc
        s * (s * k + c1)
            = s * (s * k) + s * c1 := Nat.mul_add _ _ _
        _ ≤ s * (s * k) + C * (s * k) := by
              apply Nat.add_le_add_left
              have hm := Nat.mul_le_mul_left s hkc
              have hr : s * (k * C) = C * (s * k) := by
                rw [← Nat.mul_assoc s k C, Nat.mul_comm (s * k) C]
              rwa [hr] at hm
        _ = (s + C) * (s * k) := (Nat.add_mul s C (s * k)).symm
        _ ≤ (s + C) * (s * k + c2) := Nat.mul_le_mul_left (s + C) (by omega)
    have hdiff1 : ∀ (k1 c1 k2 c2 : Nat),
        k2 ≥ 1 -> k1 + C ≤ M_hi -> c1 ≤ C ->
        1 * (s * k1 + c1) ≤ M_hi * (s * k2 + c2) := by
      intro k1 c1 k2 c2 hk2 hk_hi hc1
      rw [Nat.one_mul]
      have hlo : s ≤ s * k2 + c2 := by
        have hm : s * 1 ≤ s * k2 := Nat.mul_le_mul_left s hk2; omega
      have hhi : s * k1 + c1 ≤ M_hi * s := by
        have hc_s : c1 ≤ C * s :=
          Nat.le_trans hc1 (by simpa using Nat.mul_le_mul_left C (by omega : 1 ≤ s))
        calc
          s * k1 + c1 ≤ k1 * s + C * s := by rw [Nat.mul_comm s k1]; exact Nat.add_le_add_left hc_s _
          _ = (k1 + C) * s := (Nat.add_mul k1 C s).symm
          _ ≤ M_hi * s := Nat.mul_le_mul_right s hk_hi
      exact Nat.le_trans hhi (Nat.mul_le_mul_left M_hi hlo)
    have hpoly2_cr : ∀ (F : NatPoly2) (a b x1 y1 x2 y2 : Nat),
        a ≤ b -> a * x1 ≤ b * x2 -> a * y1 ≤ b * y2 ->
        a ^ (maxDegNatPoly2 F) * evalNatPoly2 F x1 y1 ≤
          b ^ (maxDegNatPoly2 F) * evalNatPoly2 F x2 y2 := by
      intro F a b x1 y1 x2 y2 hab hx hy
      rcases evalNatPoly2_to_3_eq F x1 y1 with ⟨he1, hd1⟩
      rcases evalNatPoly2_to_3_eq F x2 y2 with ⟨he2, _⟩
      rw [he1, he2, hd1]
      exact evalNatPoly3_cross_ratio_bound _ a b x1 y1 1 x2 y2 1 hab hx hy (by omega)
    have hPm_Pev : s ^ dP * P_m ≤ (s + C) ^ dP * P_ev :=
      hpoly2_cr pTerms s (s + C) _ _ _ _ (by omega)
        (by rw [hst_ms1, hst_evs1]; exact hsame1 2 1 1 (by decide) (by decide))
        (by rw [hbl_ms1, hbl_evs1]; exact hsame1 1 2 3 (by decide) (by decide))
    have hQev_Qm : s ^ dQ * Q_ev ≤ (s + C) ^ dQ * Q_m :=
      hpoly2_cr qTerms s (s + C) _ _ _ _ (by omega)
        (by rw [hst_evs1, hst_ms1]; exact hsame1 2 1 1 (by decide) (by decide))
        (by rw [hbl_evs1, hbl_ms1]; exact hsame1 1 3 2 (by decide) (by decide))
    have hPm_Pn : P_m ≤ M_hi ^ dP * P_n := by
      simpa using hpoly2_cr pTerms 1 M_hi
        (sternDiatomic ms1) (binBitLength ms1) (sternDiatomic ns1) (binBitLength ns1) hMhi_ge1
        (by rw [hst_ms1, hst_ns1]; exact hdiff1 2 1 1 1 (by decide) (by decide) (by decide))
        (by rw [hbl_ms1, hbl_ns1]; exact hdiff1 1 2 1 1 (by decide) (by decide) (by decide))
    have hQn_Qm : Q_n ≤ M_hi ^ dQ * Q_m := by
      simpa using hpoly2_cr qTerms 1 M_hi
        (sternDiatomic ns1) (binBitLength ns1) (sternDiatomic ms1) (binBitLength ms1) hMhi_ge1
        (by rw [hst_ns1, hst_ms1]; exact hdiff1 1 1 2 1 (by decide) (by decide) (by decide))
        (by rw [hbl_ns1, hbl_ms1]; exact hdiff1 1 1 1 2 (by decide) (by decide) (by decide))
    let K_den := P_m * (Q_ev * Q_n)
    have hK_pos : K_den ≥ 1 := Nat.mul_le_mul hPm_pos (Nat.mul_le_mul hQev_pos hQn_pos)
    have hbr1 : B_eff * s ^ D * K_den ≤ (B_eff * (s + C) ^ D) * ((P_ev * Q_n) * Q_m) := by
      have hm := Nat.mul_le_mul_left B_eff
        (Nat.mul_le_mul_right Q_n (Nat.mul_le_mul hPm_Pev hQev_Qm))
      have hl : B_eff * ((s ^ dP * P_m * (s ^ dQ * Q_ev)) * Q_n) = B_eff * s ^ D * K_den := by
        dsimp [D, K_den]
        rw [Nat.pow_add s dP dQ, Nat.mul_assoc B_eff]
        apply congrArg (B_eff * ·)
        rw [← Nat.mul_assoc (s ^ dP * P_m), Nat.mul_assoc (s ^ dP) P_m (s ^ dQ),
            Nat.mul_comm P_m (s ^ dQ), ← Nat.mul_assoc (s ^ dP) (s ^ dQ) P_m,
            Nat.mul_assoc (s ^ dP * s ^ dQ) P_m Q_ev, Nat.mul_assoc (s ^ dP * s ^ dQ),
            Nat.mul_assoc P_m Q_ev Q_n]
      have hr : B_eff * (((s + C) ^ dP * P_ev * ((s + C) ^ dQ * Q_m)) * Q_n) =
          (B_eff * (s + C) ^ D) * ((P_ev * Q_n) * Q_m) := by
        dsimp [D]
        rw [Nat.pow_add (s + C) dP dQ, Nat.mul_assoc B_eff]
        apply congrArg (B_eff * ·)
        rw [← Nat.mul_assoc ((s + C) ^ dP * P_ev),
            Nat.mul_assoc ((s + C) ^ dP) P_ev ((s + C) ^ dQ),
            Nat.mul_comm P_ev ((s + C) ^ dQ),
            ← Nat.mul_assoc ((s + C) ^ dP) ((s + C) ^ dQ) P_ev,
            Nat.mul_assoc ((s + C) ^ dP * (s + C) ^ dQ) P_ev Q_m,
            Nat.mul_assoc ((s + C) ^ dP * (s + C) ^ dQ),
            Nat.mul_assoc P_ev Q_m Q_n, Nat.mul_comm Q_m Q_n, ← Nat.mul_assoc P_ev Q_n Q_m]
      rwa [hl, hr] at hm
    have hsD_le : s ^ D ≤ (s + C) ^ D := by
      have hm : ∀ k : Nat, s ^ k ≤ (s + C) ^ k := by
        intro k; induction k with
        | zero => exact Nat.le_refl 1
        | succ k' ih => rw [Nat.pow_succ, Nat.pow_succ]; exact Nat.mul_le_mul ih (by omega)
      exact hm D
    have hbr2 : s ^ D * K_den ≤ (B_eff * (s + C) ^ D) * ((P_n * Q_ev) * Q_m) := by
      have hm_base := Nat.mul_le_mul_right Q_ev (Nat.mul_le_mul hPm_Pn hQn_Qm)
      have hl : (P_m * Q_n) * Q_ev = K_den := by
        dsimp [K_den]; rw [Nat.mul_assoc P_m Q_n Q_ev, Nat.mul_comm Q_n Q_ev]
      have hr : ((M_hi ^ dP * P_n) * (M_hi ^ dQ * Q_m)) * Q_ev = B_eff * ((P_n * Q_ev) * Q_m) := by
        dsimp [B_eff, D]
        rw [Nat.pow_add M_hi dP dQ,
            ← Nat.mul_assoc (M_hi ^ dP * P_n),
            Nat.mul_assoc (M_hi ^ dP) P_n (M_hi ^ dQ),
            Nat.mul_comm P_n (M_hi ^ dQ),
            ← Nat.mul_assoc (M_hi ^ dP) (M_hi ^ dQ) P_n,
            Nat.mul_assoc (M_hi ^ dP * M_hi ^ dQ) P_n Q_m,
            Nat.mul_assoc (M_hi ^ dP * M_hi ^ dQ),
            Nat.mul_assoc P_n Q_m Q_ev, Nat.mul_comm Q_m Q_ev, ← Nat.mul_assoc P_n Q_ev Q_m]
      rw [hl, hr] at hm_base
      calc
        s ^ D * K_den ≤ (s + C) ^ D * K_den := Nat.mul_le_mul_right K_den hsD_le
        _ ≤ (s + C) ^ D * (B_eff * ((P_n * Q_ev) * Q_m)) := Nat.mul_le_mul_left ((s + C) ^ D) hm_base
        _ = (B_eff * (s + C) ^ D) * ((P_n * Q_ev) * Q_m) := by
              rw [← Nat.mul_assoc ((s + C) ^ D) B_eff, Nat.mul_comm ((s + C) ^ D) B_eff]
    have hsum := Nat.add_le_add hbr1 hbr2
    rw [← Nat.one_mul (s ^ D * K_den), ← Nat.mul_assoc 1 (s ^ D) K_den,
        ← Nat.add_mul (B_eff * s ^ D) (1 * s ^ D) K_den,
        ← Nat.add_mul B_eff 1 (s ^ D),
        ← Nat.mul_add (B_eff * (s + C) ^ D),
        ← Nat.add_mul (P_ev * Q_n) (P_n * Q_ev) Q_m] at hsum
    have htot : ((B_eff + 1) * s ^ D) * K_den ≤ (B_eff * (s + C) ^ D) * K_den :=
      Nat.le_trans hsum (Nat.mul_le_mul_left (B_eff * (s + C) ^ D) hcanc)
    have hle_b := nat_mul_le_cancel_right_w5 K_den _ _ hK_pos htot
    have hlt_b := bernoulli_nat_ratio_lt 1 B_eff D C s (by decide) hBeff_pos hC_pos hs_ge
    omega

-- ----------------------------------------------------------------------------
-- Section 3A.2: Non-Regular `∀ Q ≥ 1` Zero-Testing 1-Counter Pushdown Automata (`OCN`)
-- ----------------------------------------------------------------------------

/-- Elementary counter step operation `{-1, 0, +1}` of a `1`-counter pushdown automaton (`OCN`). -/
inductive CounterOp where
  | dec : CounterOp
  | stay : CounterOp
  | inc : CounterOp
  deriving DecidableEq, Repr

def applyCounterOp (c : Nat) : CounterOp -> Nat
  | .dec => c - 1
  | .stay => c
  | .inc => c + 1

/-- Single zero-testing transition step of a `Q`-state `1`-counter pushdown automaton (`OCN`). -/
def stepOCN {Q : Nat}
    (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp)
    (cfg : Fin Q × Nat) (b : Bool) : Fin Q × Nat :=
  if cfg.2 = 0 then
    ((deltaZero cfg.1 b).1, applyCounterOp 0 (deltaZero cfg.1 b).2)
  else
    ((deltaPos cfg.1 b).1, applyCounterOp cfg.2 (deltaPos cfg.1 b).2)

/-- Fuel-stabilized MSB-to-LSB `Q`-state zero-testing `1`-counter pushdown automaton runner. -/
def runMSBOneCounterOCNAux {Q : Nat}
    (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp)
    (q0 : Fin Q) : Nat -> Nat -> Fin Q × Nat
  | 0, _ => (q0, 0)
  | fuel + 1, n =>
    if n = 0 then (q0, 0)
    else stepOCN deltaZero deltaPos
           (runMSBOneCounterOCNAux deltaZero deltaPos q0 fuel (n / 2))
           (n % 2 == 1)

def runMSBOneCounterOCN (Q : Nat)
    (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp)
    (q0 : Fin Q) (n : Nat) : Fin Q × Nat :=
  runMSBOneCounterOCNAux deltaZero deltaPos q0 n n

/-- Iterate unary `0`-bit `OCN` steps `k` times from `cfg`. -/
def iterOCN0 {Q : Nat}
    (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp) :
    Nat -> (Fin Q × Nat) -> (Fin Q × Nat)
  | 0, cfg => cfg
  | k + 1, cfg => stepOCN deltaZero deltaPos (iterOCN0 deltaZero deltaPos k cfg) false

/-- Iterate unary `1`-bit `OCN` steps `k` times from `cfg`. -/
def iterOCN1 {Q : Nat}
    (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp) :
    Nat -> (Fin Q × Nat) -> (Fin Q × Nat)
  | 0, cfg => cfg
  | k + 1, cfg => stepOCN deltaZero deltaPos (iterOCN1 deltaZero deltaPos k cfg) true

theorem iterOCN0_add {Q : Nat}
    (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp) :
    ∀ (a b : Nat) (cfg : Fin Q × Nat),
      iterOCN0 deltaZero deltaPos (a + b) cfg =
        iterOCN0 deltaZero deltaPos a (iterOCN0 deltaZero deltaPos b cfg)
  | 0, _, _ => by simp [iterOCN0]
  | a + 1, b, cfg => by
    rw [Nat.succ_add]
    simp only [iterOCN0, iterOCN0_add deltaZero deltaPos a b cfg]

theorem runMSBOneCounterOCNAux_eq_of_ge {Q : Nat}
    (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp) (q0 : Fin Q) :
    ∀ (f1 f2 n : Nat),
      n ≤ f1 -> n ≤ f2 ->
      runMSBOneCounterOCNAux deltaZero deltaPos q0 f1 n =
        runMSBOneCounterOCNAux deltaZero deltaPos q0 f2 n
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, n, h1, _ => by rw [show n = 0 by omega]; simp [runMSBOneCounterOCNAux]
  | _ + 1, 0, n, _, h2 => by rw [show n = 0 by omega]; simp [runMSBOneCounterOCNAux]
  | f1 + 1, f2 + 1, n, h1, h2 => by
    simp only [runMSBOneCounterOCNAux]
    by_cases hn0 : n = 0
    · simp [hn0]
    · simp only [hn0, ite_false]
      rw [runMSBOneCounterOCNAux_eq_of_ge deltaZero deltaPos q0 f1 f2 (n / 2) (by omega) (by omega)]

theorem runMSBOneCounterOCN_step_pos {Q : Nat}
    (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp)
    (q0 : Fin Q) (n : Nat) (hn : n ≥ 1) :
    runMSBOneCounterOCN Q deltaZero deltaPos q0 n =
      stepOCN deltaZero deltaPos
        (runMSBOneCounterOCN Q deltaZero deltaPos q0 (n / 2))
        (n % 2 == 1) := by
  unfold runMSBOneCounterOCN
  cases n with
  | zero => omega
  | succ m =>
    simp only [runMSBOneCounterOCNAux, Nat.succ_ne_zero, ite_false]
    rw [runMSBOneCounterOCNAux_eq_of_ge deltaZero deltaPos q0 m ((m + 1) / 2) ((m + 1) / 2)
      (by omega) (Nat.le_refl _)]

theorem runMSBOneCounterOCN_mul_pow2 {Q : Nat}
    (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp)
    (q0 : Fin Q) (H : Nat) (hH : H ≥ 1) :
    ∀ d : Nat,
      runMSBOneCounterOCN Q deltaZero deltaPos q0 (2 ^ d * H) =
        iterOCN0 deltaZero deltaPos d (runMSBOneCounterOCN Q deltaZero deltaPos q0 H)
  | 0 => by simp [iterOCN0]
  | d + 1 => by
    have hmul : 2 ^ (d + 1) * H = 2 * (2 ^ d * H) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ d) 2, Nat.mul_assoc]
    have hpos : 2 ^ d * H ≥ 1 := Nat.mul_le_mul (pow2_pos_nat d) hH
    have hm2 : ((2 * (2 ^ d * H)) % 2 == 1) = false := by rw [Nat.mul_mod_right]; rfl
    rw [hmul, runMSBOneCounterOCN_step_pos deltaZero deltaPos q0 _ (by omega), hm2,
        show (2 * (2 ^ d * H)) / 2 = 2 ^ d * H by omega,
        runMSBOneCounterOCN_mul_pow2 deltaZero deltaPos q0 H hH d]
    rfl

theorem runMSBOneCounterOCN_mersenne_tail {Q : Nat}
    (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp)
    (q0 : Fin Q) (H : Nat) (hH : H ≥ 1) :
    ∀ d : Nat,
      runMSBOneCounterOCN Q deltaZero deltaPos q0 (2 ^ d * H + (2 ^ d - 1)) =
        iterOCN1 deltaZero deltaPos d (runMSBOneCounterOCN Q deltaZero deltaPos q0 H)
  | 0 => by simp [iterOCN1]
  | d + 1 => by
    have hp := pow2_pos_nat d
    have hval : 2 ^ (d + 1) * H + (2 ^ (d + 1) - 1) = 2 * (2 ^ d * H + (2 ^ d - 1)) + 1 := by
      rw [Nat.pow_succ 2 d]
      generalize 2 ^ d = p2 at hp ⊢
      rw [Nat.mul_comm p2 2, Nat.mul_assoc 2 p2 H, Nat.mul_add 2 (p2 * H)]
      omega
    have hpos : 2 * (2 ^ d * H + (2 ^ d - 1)) + 1 ≥ 1 := by omega
    have hbit : ((2 * (2 ^ d * H + (2 ^ d - 1)) + 1) % 2 == 1) = true := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left]; rfl
    have hdiv : (2 * (2 ^ d * H + (2 ^ d - 1)) + 1) / 2 = 2 ^ d * H + (2 ^ d - 1) := by omega
    rw [hval, runMSBOneCounterOCN_step_pos deltaZero deltaPos q0 _ hpos, hbit, hdiv,
        runMSBOneCounterOCN_mersenne_tail deltaZero deltaPos q0 H hH d]
    rfl

theorem stepOCN_counter_le_succ {Q : Nat}
    (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp)
    (cfg : Fin Q × Nat) (b : Bool) :
    (stepOCN deltaZero deltaPos cfg b).2 ≤ cfg.2 + 1 := by
  unfold stepOCN
  by_cases hc0 : cfg.2 = 0
  · simp only [hc0, ite_true]
    cases (deltaZero cfg.1 b).2 <;> simp only [applyCounterOp] <;> omega
  · simp only [hc0, ite_false]
    cases (deltaPos cfg.1 b).2 <;> simp only [applyCounterOp] <;> omega

theorem iterOCN0_counter_le_add {Q : Nat}
    (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp) :
    ∀ (k : Nat) (cfg : Fin Q × Nat),
      (iterOCN0 deltaZero deltaPos k cfg).2 ≤ cfg.2 + k
  | 0, _ => Nat.le_refl _
  | k + 1, cfg => by
    simp only [iterOCN0]
    have h1 := stepOCN_counter_le_succ deltaZero deltaPos (iterOCN0 deltaZero deltaPos k cfg) false
    have h2 := iterOCN0_counter_le_add deltaZero deltaPos k cfg
    omega

theorem iterOCN0_pos_state_and_cross_sum {Q : Nat}
    (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp) :
    ∀ (s : Nat) (q : Fin Q) (cA cB : Nat),
      (∀ r : Nat, r < s ->
        (iterOCN0 deltaZero deltaPos r (q, cA)).2 ≥ 1 ∧
        (iterOCN0 deltaZero deltaPos r (q, cB)).2 ≥ 1) ->
      (iterOCN0 deltaZero deltaPos s (q, cA)).1 =
        iterFin (fun st => (deltaPos st false).1) s q ∧
      (iterOCN0 deltaZero deltaPos s (q, cB)).1 =
        iterFin (fun st => (deltaPos st false).1) s q ∧
      (iterOCN0 deltaZero deltaPos s (q, cA)).2 + cB =
        (iterOCN0 deltaZero deltaPos s (q, cB)).2 + cA
  | 0, _, _, _, _ => ⟨rfl, rfl, by simp [iterOCN0]; omega⟩
  | s + 1, q, cA, cB, hpos => by
    rcases iterOCN0_pos_state_and_cross_sum deltaZero deltaPos s q cA cB
      (fun r hr => hpos r (by omega)) with ⟨hqA, hqB, hsum⟩
    rcases hpos s (by omega) with ⟨hcA_pos, hcB_pos⟩
    let cfgA := iterOCN0 deltaZero deltaPos s (q, cA)
    let cfgB := iterOCN0 deltaZero deltaPos s (q, cB)
    change cfgA.2 ≥ 1 at hcA_pos
    change cfgB.2 ≥ 1 at hcB_pos
    change cfgA.1 = iterFin (fun st => (deltaPos st false).1) s q at hqA
    change cfgB.1 = iterFin (fun st => (deltaPos st false).1) s q at hqB
    change cfgA.2 + cB = cfgB.2 + cA at hsum
    have hnzA : ¬ (cfgA.2 = 0) := by omega
    have hnzB : ¬ (cfgB.2 = 0) := by omega
    simp only [iterOCN0, iterFin]
    change (stepOCN deltaZero deltaPos cfgA false).1 = _ ∧
           (stepOCN deltaZero deltaPos cfgB false).1 = _ ∧
           (stepOCN deltaZero deltaPos cfgA false).2 + cB =
             (stepOCN deltaZero deltaPos cfgB false).2 + cA
    unfold stepOCN
    rw [ite_false_of_w10 hnzA, ite_false_of_w10 hnzB, hqA, hqB]
    refine ⟨rfl, rfl, ?_⟩
    dsimp only
    cases (deltaPos (iterFin (fun st => (deltaPos st false).1) s q) false).2 <;>
      simp only [applyCounterOp] <;> omega

theorem iterOCN0_pos_shift {Q : Nat}
    (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp) :
    ∀ (s d : Nat) (cfg : Fin Q × Nat),
      (∀ r : Nat, r < s -> (iterOCN0 deltaZero deltaPos r cfg).2 ≥ 1) ->
      iterOCN0 deltaZero deltaPos s (cfg.1, cfg.2 + d) =
        ((iterOCN0 deltaZero deltaPos s cfg).1, (iterOCN0 deltaZero deltaPos s cfg).2 + d)
  | 0, _, _, _ => rfl
  | s + 1, d, cfg, hpos => by
    have ih := iterOCN0_pos_shift deltaZero deltaPos s d cfg (fun r hr => hpos r (by omega))
    have hc_pos := hpos s (by omega)
    let cur := iterOCN0 deltaZero deltaPos s cfg
    change cur.2 ≥ 1 at hc_pos
    change iterOCN0 deltaZero deltaPos s (cfg.1, cfg.2 + d) = (cur.1, cur.2 + d) at ih
    simp only [iterOCN0]
    rw [ih]
    change stepOCN deltaZero deltaPos (cur.1, cur.2 + d) false =
      ((stepOCN deltaZero deltaPos cur false).1, (stepOCN deltaZero deltaPos cur false).2 + d)
    unfold stepOCN
    have hnz1 : ¬ (cur.2 + d = 0) := by omega
    have hnz2 : ¬ (cur.2 = 0) := by omega
    rw [ite_false_of_w10 hnz1, ite_false_of_w10 hnz2]
    dsimp only
    cases (deltaPos cur.1 false).2 <;> simp only [applyCounterOp] <;> exact Prod.ext rfl (by omega)

/-- Choice-free first-index search on `[0, N]` for a `Bool` predicate. -/
def findFirstTrueLeAux (p : Nat -> Bool) : Nat -> Option Nat
  | 0 => if p 0 then some 0 else none
  | n + 1 =>
    match findFirstTrueLeAux p n with
    | some idx => some idx
    | none => if p (n + 1) then some (n + 1) else none

theorem findFirstTrueLeAux_spec (p : Nat -> Bool) :
    ∀ N : Nat,
      (∀ idx : Nat, findFirstTrueLeAux p N = some idx ->
        idx ≤ N ∧ p idx = true ∧ (∀ t : Nat, t < idx -> p t = false)) ∧
      (findFirstTrueLeAux p N = none -> ∀ t : Nat, t ≤ N -> p t = false)
  | 0 => by
    simp only [findFirstTrueLeAux]
    cases hp0 : p 0 with
    | true =>
      simp only [ite_true]
      exact ⟨fun idx h => by injection h with hi; subst hi; exact ⟨Nat.le_refl 0, hp0, fun _ ht => by omega⟩,
             fun h => by cases h⟩
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      exact ⟨fun _ h => (by cases h),
             fun _ t ht => by rw [show t = 0 by omega]; exact hp0⟩
  | n + 1 => by
    rcases findFirstTrueLeAux_spec p n with ⟨hsome, hnone⟩
    refine ⟨?_, ?_⟩
    · intro idx h
      simp only [findFirstTrueLeAux] at h
      cases hf : findFirstTrueLeAux p n with
      | some j =>
        rw [hf] at h; injection h with hj; subst hj
        rcases hsome j hf with ⟨hle, hpj, hprev⟩
        exact ⟨by omega, hpj, hprev⟩
      | none =>
        rw [hf] at h
        cases hpn : p (n + 1) with
        | true =>
          rw [hpn] at h; simp only [ite_true] at h; injection h with hi; subst hi
          exact ⟨Nat.le_refl _, hpn, fun t ht => hnone hf t (by omega)⟩
        | false => rw [hpn] at h; cases h
    · intro h t ht
      simp only [findFirstTrueLeAux] at h
      cases hf : findFirstTrueLeAux p n with
      | some j => rw [hf] at h; cases h
      | none =>
        rw [hf] at h
        cases hpn : p (n + 1) with
        | true => rw [hpn] at h; cases h
        | false =>
          by_cases hteq : t = n + 1
          · subst hteq; exact hpn
          · exact hnone hf t (by omega)

/-- Choice-free last-index search on `[0, N]` for a `Bool` predicate. -/
def findLastTrueLeAux (p : Nat -> Bool) : Nat -> Option Nat
  | 0 => if p 0 then some 0 else none
  | n + 1 => if p (n + 1) then some (n + 1) else findLastTrueLeAux p n

theorem findLastTrueLeAux_spec (p : Nat -> Bool) :
    ∀ N : Nat,
      (∀ idx : Nat, findLastTrueLeAux p N = some idx ->
        idx ≤ N ∧ p idx = true ∧ (∀ t : Nat, idx < t -> t ≤ N -> p t = false)) ∧
      (findLastTrueLeAux p N = none -> ∀ t : Nat, t ≤ N -> p t = false)
  | 0 => by
    simp only [findLastTrueLeAux]
    cases hp0 : p 0 with
    | true =>
      simp only [ite_true]
      exact ⟨fun idx h => by injection h with hi; subst hi; exact ⟨Nat.le_refl 0, hp0, fun _ h1 h2 => by omega⟩,
             fun h => by cases h⟩
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      exact ⟨fun _ h => (by cases h),
             fun _ t ht => by rw [show t = 0 by omega]; exact hp0⟩
  | n + 1 => by
    rcases findLastTrueLeAux_spec p n with ⟨hsome, hnone⟩
    refine ⟨?_, ?_⟩
    · intro idx h
      simp only [findLastTrueLeAux] at h
      cases hpn : p (n + 1) with
      | true =>
        rw [hpn] at h; simp only [ite_true] at h; injection h with hi; subst hi
        exact ⟨Nat.le_refl _, hpn, fun _ h1 h2 => by omega⟩
      | false =>
        rw [hpn] at h; simp only [Bool.false_eq_true, ite_false] at h
        rcases hsome idx h with ⟨hle, hpi, hafter⟩
        refine ⟨by omega, hpi, ?_⟩
        intro t h1 h2
        by_cases hteq : t = n + 1
        · subst hteq; exact hpn
        · exact hafter t h1 (by omega)
    · intro h t ht
      simp only [findLastTrueLeAux] at h
      cases hpn : p (n + 1) with
      | true => rw [hpn] at h; cases h
      | false =>
        rw [hpn] at h; simp only [Bool.false_eq_true, ite_false] at h
        by_cases hteq : t = n + 1
        · subst hteq; exact hpn
        · exact hnone h t (by omega)

/--
  Universal Unary `0`-Run `OCN` Semilinear Dichotomy Lemma (`choice-free, zero custom axioms`):
  For ANY `Q ≥ 1`, ANY zero-testing `1`-counter pushdown automaton `(deltaZero, deltaPos)`,
  ANY bound `B : Nat`, and ANY starting configuration `cfg0 : Fin Q × Nat` with `cfg0.2 ≤ B`,
  setting `M_box := Q * (B + Q + 1)` and `P_ocn := natFact M_box`, there exists `slope : Nat`
  (`slope = 0` iff the trajectory stays strictly inside `Fin Q × [0, B + Q + 1)` on `[0, M_box]`)
  such that for ALL `k ≥ M_box` and ALL `m : Nat`:
    1. `(iterOCN0 deltaZero deltaPos (k + P_ocn * m) cfg0).1 = (iterOCN0 deltaZero deltaPos k cfg0).1`,
    2. `(iterOCN0 deltaZero deltaPos (k + P_ocn * m) cfg0).2 = m * slope + (iterOCN0 deltaZero deltaPos k cfg0).2`!
-/
theorem ocn_unary_zero_run_semilinear_dichotomy {Q : Nat} (hQ : Q ≥ 1)
    (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp)
    (B : Nat) (cfg0 : Fin Q × Nat) (hB : cfg0.2 ≤ B) :
    let M_box := Q * (B + Q + 1)
    let P_ocn := natFact M_box
    ∃ slope : Nat,
      ((∀ t : Nat, t ≤ M_box -> (iterOCN0 deltaZero deltaPos t cfg0).2 < B + Q + 1) -> slope = 0) ∧
      ∀ (m k : Nat), k ≥ M_box ->
        (iterOCN0 deltaZero deltaPos (k + P_ocn * m) cfg0).1 =
          (iterOCN0 deltaZero deltaPos k cfg0).1 ∧
        (iterOCN0 deltaZero deltaPos (k + P_ocn * m) cfg0).2 =
          m * slope + (iterOCN0 deltaZero deltaPos k cfg0).2 := by
  dsimp only
  let H_box := B + Q + 1
  let M_box := Q * H_box
  let P_ocn := natFact M_box
  have hH_pos : H_box ≥ 2 := by dsimp [H_box]; omega
  have hM_pos : M_box ≥ 2 := by
    dsimp [M_box]; simpa using Nat.mul_le_mul hQ hH_pos
  let predEsc : Nat -> Bool := fun t => decide ((iterOCN0 deltaZero deltaPos t cfg0).2 ≥ H_box)
  cases hfindT : findFirstTrueLeAux predEsc M_box with
  | none =>
    -- Bounded regime (`∀ t ≤ M_box, c(t) < H_box`): exact `(q, c)` periodicity (`slope = 0`)!
    have hnone := (findFirstTrueLeAux_spec predEsc M_box).2 hfindT
    have hlt_all : ∀ t : Nat, t ≤ M_box -> (iterOCN0 deltaZero deltaPos t cfg0).2 < H_box := by
      intro t ht
      have hf := hnone t ht
      dsimp [predEsc] at hf
      by_cases hge : (iterOCN0 deltaZero deltaPos t cfg0).2 ≥ H_box
      · rw [decide_eq_true hge] at hf; cases hf
      · omega
    let enc : Nat -> Nat := fun t =>
      (iterOCN0 deltaZero deltaPos t cfg0).1.val * H_box +
        (iterOCN0 deltaZero deltaPos t cfg0).2
    have henc_lt : ∀ t : Nat, t < M_box + 1 -> enc t < M_box := by
      intro t ht
      have hq_lt := (iterOCN0 deltaZero deltaPos t cfg0).1.isLt
      have hc_lt := hlt_all t (by omega)
      dsimp [enc, M_box]
      have hm : ((iterOCN0 deltaZero deltaPos t cfg0).1.val + 1) * H_box ≤ Q * H_box :=
        Nat.mul_le_mul_right H_box (by omega)
      rw [Nat.add_mul, Nat.one_mul] at hm
      omega
    rcases nat_func_pigeonhole M_box (M_box + 1) enc henc_lt (by omega) with
      ⟨i, j, hij, hj_lt, henc_eq⟩
    have hc_i := hlt_all i (by omega)
    have hc_j := hlt_all j (by omega)
    have hij_cfg : iterOCN0 deltaZero deltaPos i cfg0 = iterOCN0 deltaZero deltaPos j cfg0 := by
      dsimp [enc] at henc_eq
      have hdiv_i : ((iterOCN0 deltaZero deltaPos i cfg0).1.val * H_box +
          (iterOCN0 deltaZero deltaPos i cfg0).2) / H_box =
          (iterOCN0 deltaZero deltaPos i cfg0).1.val := by
        rw [Nat.add_comm, Nat.mul_comm _ H_box,
            Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hc_i, Nat.zero_add]
      have hdiv_j : ((iterOCN0 deltaZero deltaPos j cfg0).1.val * H_box +
          (iterOCN0 deltaZero deltaPos j cfg0).2) / H_box =
          (iterOCN0 deltaZero deltaPos j cfg0).1.val := by
        rw [Nat.add_comm, Nat.mul_comm _ H_box,
            Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hc_j, Nat.zero_add]
      have hq_eq : (iterOCN0 deltaZero deltaPos i cfg0).1.val =
          (iterOCN0 deltaZero deltaPos j cfg0).1.val := by
        have hd := congrArg (· / H_box) henc_eq
        rwa [hdiv_i, hdiv_j] at hd
      have hc_eq : (iterOCN0 deltaZero deltaPos i cfg0).2 =
          (iterOCN0 deltaZero deltaPos j cfg0).2 := by
        rw [hq_eq] at henc_eq; omega
      exact Prod.ext (Fin.ext hq_eq) hc_eq
    let p := j - i
    have hp1 : 1 ≤ p := by dsimp [p]; omega
    have hpM : p ≤ M_box := by dsimp [p]; omega
    have hp_step : ∀ k : Nat, k ≥ i ->
        iterOCN0 deltaZero deltaPos (k + p) cfg0 = iterOCN0 deltaZero deltaPos k cfg0 := by
      intro k hki
      have hk_sp : k + p = (k - i) + j := by dsimp [p]; omega
      have hk0_sp : k = (k - i) + i := by omega
      rw [hk_sp, iterOCN0_add deltaZero deltaPos (k - i) j cfg0, ← hij_cfg,
          ← iterOCN0_add deltaZero deltaPos (k - i) i cfg0, ← hk0_sp]
    have hp_mul : ∀ (c k : Nat), k ≥ i ->
        iterOCN0 deltaZero deltaPos (k + p * c) cfg0 = iterOCN0 deltaZero deltaPos k cfg0 := by
      intro c; induction c with
      | zero => intro k _; simp
      | succ c' ih =>
        intro k hki
        rw [Nat.mul_succ p c', ← Nat.add_assoc k (p * c') p,
            hp_step (k + p * c') (by omega), ih k hki]
    rcases dvd_natFact p M_box hp1 hpM with ⟨u, hu⟩
    refine ⟨0, ⟨fun _ => rfl, ?_⟩⟩
    intro m k hkM
    have heq_cfg : iterOCN0 deltaZero deltaPos (k + P_ocn * m) cfg0 =
        iterOCN0 deltaZero deltaPos k cfg0 := by
      have hi_le_M : i ≤ M_box := by omega
      have hk_ge_M : k ≥ M_box := hkM
      dsimp [P_ocn]
      rw [hu, Nat.mul_assoc p u m]
      exact hp_mul (u * m) k (Nat.le_trans hi_le_M hk_ge_M)
    rw [heq_cfg, Nat.mul_zero, Nat.zero_add]
    exact ⟨rfl, rfl⟩
  | some T =>
    -- Unbounded positive-gain regime (`c(T) ≥ B + Q + 1` at minimal `T ≤ M_box`):
    rcases (findFirstTrueLeAux_spec predEsc M_box).1 T hfindT with ⟨hT_le, hT_esc, _⟩
    have hcT_ge : (iterOCN0 deltaZero deltaPos T cfg0).2 ≥ H_box := of_decide_eq_true hT_esc
    have hnot_all : ¬ (∀ t : Nat, t ≤ M_box -> (iterOCN0 deltaZero deltaPos t cfg0).2 < H_box) :=
      fun hall => by have h := hall T hT_le; omega
    -- Find last index `t_base ≤ T` with `c(t_base) ≤ B`:
    let predBase : Nat -> Bool := fun t => decide ((iterOCN0 deltaZero deltaPos t cfg0).2 ≤ B)
    cases hfindB : findLastTrueLeAux predBase T with
    | none =>
      exfalso
      have hn0 := (findLastTrueLeAux_spec predBase T).2 hfindB 0 (by omega)
      have h0_ok : predBase 0 = true := decide_eq_true hB
      rw [h0_ok] at hn0; cases hn0
    | some t_base =>
      rcases (findLastTrueLeAux_spec predBase T).1 t_base hfindB with ⟨htb_le, htb_ok, htb_after⟩
      have hctb_le : (iterOCN0 deltaZero deltaPos t_base cfg0).2 ≤ B := of_decide_eq_true htb_ok
      have htb_lt_T : t_base < T := by
        by_cases heq : t_base = T
        · subst heq; dsimp [H_box] at hcT_ge; omega
        · omega
      let t_start := t_base + 1
      have hgt_B : ∀ t : Nat, t_start ≤ t -> t ≤ T ->
          (iterOCN0 deltaZero deltaPos t cfg0).2 ≥ B + 1 := by
        intro t h1 h2
        have hf := htb_after t (by dsimp [t_start] at h1; omega) h2
        dsimp [predBase] at hf
        by_cases hle : (iterOCN0 deltaZero deltaPos t cfg0).2 ≤ B
        · rw [decide_eq_true hle] at hf; cases hf
        · omega
      have hcts_eq : (iterOCN0 deltaZero deltaPos t_start cfg0).2 = B + 1 := by
        have hlo := hgt_B t_start (Nat.le_refl _) (by dsimp [t_start]; omega)
        have hhi := stepOCN_counter_le_succ deltaZero deltaPos
          (iterOCN0 deltaZero deltaPos t_base cfg0) false
        dsimp [t_start] at hlo ⊢
        simp only [iterOCN0] at hlo ⊢
        omega
      let cfg_s := iterOCN0 deltaZero deltaPos t_start cfg0
      have hshift_s : ∀ u : Nat,
          iterOCN0 deltaZero deltaPos (t_start + u) cfg0 =
            iterOCN0 deltaZero deltaPos u cfg_s := fun u => by
        rw [Nat.add_comm t_start u, iterOCN0_add]
      have hTs_ge_Q : T - t_start ≥ Q := by
        have hle := iterOCN0_counter_le_add deltaZero deltaPos (T - t_start) cfg_s
        rw [← hshift_s (T - t_start), show t_start + (T - t_start) = T by omega] at hle
        change (iterOCN0 deltaZero deltaPos T cfg0).2 ≤ cfg_s.2 + (T - t_start) at hle
        change cfg_s.2 = B + 1 at hcts_eq
        dsimp [H_box] at hcT_ge
        omega
      have hpos_on_T : ∀ u : Nat, u ≤ T - t_start ->
          (iterOCN0 deltaZero deltaPos u cfg_s).2 ≥ 1 := by
        intro u hu
        have h := hgt_B (t_start + u) (by omega) (by omega)
        rw [hshift_s u] at h; omega
      let gPos : Fin Q -> Fin Q := fun st => (deltaPos st false).1
      have hstate_on_T : ∀ u : Nat, u ≤ T - t_start ->
          (iterOCN0 deltaZero deltaPos u cfg_s).1 = iterFin gPos u cfg_s.1 := by
        intro u hu
        exact (iterOCN0_pos_state_and_cross_sum deltaZero deltaPos u cfg_s.1 cfg_s.2 cfg_s.2
          (fun r hr => ⟨hpos_on_T r (by omega), hpos_on_T r (by omega)⟩)).1
      rcases nat_func_pigeonhole Q (Q + 1) (fun u => (iterFin gPos u cfg_s.1).val)
        (fun u _ => (iterFin gPos u cfg_s.1).isLt) (by omega) with ⟨i, j, hij, hj_lt, hval_ij⟩
      have hqi_eq_qj : iterFin gPos i cfg_s.1 = iterFin gPos j cfg_s.1 := Fin.ext hval_ij
      let L := j - i
      have hL1 : 1 ≤ L := by dsimp [L]; omega
      have hLQ : L ≤ Q := by dsimp [L]; omega
      let cfg_cyc := iterOCN0 deltaZero deltaPos i cfg_s
      have hcyc_shift : ∀ v : Nat,
          iterOCN0 deltaZero deltaPos (i + v) cfg_s =
            iterOCN0 deltaZero deltaPos v cfg_cyc := fun v => by
        rw [Nat.add_comm i v, iterOCN0_add]
      have hqi_cyc : cfg_cyc.1 = iterFin gPos i cfg_s.1 := hstate_on_T i (by omega)
      have hqj_cyc : (iterOCN0 deltaZero deltaPos L cfg_cyc).1 = cfg_cyc.1 := by
        have hs := hstate_on_T j (by omega)
        rw [← hqi_eq_qj, ← hqi_cyc] at hs
        rwa [show j = i + L by dsimp [L]; omega, hcyc_shift L] at hs
      -- Prove strict positive cycle gain `c_j > c_i` by bounding `[t_start + i, T]` if `c_j ≤ c_i`:
      let c_i := cfg_cyc.2
      let c_j := (iterOCN0 deltaZero deltaPos L cfg_cyc).2
      have hci_le : c_i ≤ B + 1 + i := by
        have h := iterOCN0_counter_le_add deltaZero deltaPos i cfg_s
        change c_i ≤ cfg_s.2 + i at h
        change cfg_s.2 = B + 1 at hcts_eq
        omega
      have hcj_gt_ci : c_j > c_i := by
        by_cases hgt : c_j > c_i
        · exact hgt
        · exfalso
          let U := T - t_start - i
          have hpos_v : ∀ v : Nat, v ≤ U -> (iterOCN0 deltaZero deltaPos v cfg_cyc).2 ≥ 1 := by
            intro v hv
            rw [← hcyc_shift v]
            exact hpos_on_T (i + v) (by dsimp [U] at hv; omega)
          let q_div := U / L
          let r_mod := U % L
          have hU_dm : U = L * q_div + r_mod := (Nat.div_add_mod U L).symm
          have hr_lt : r_mod < L := Nat.mod_lt U hL1
          have hperiod_noninc : ∀ m : Nat, L * m ≤ U ->
              (iterOCN0 deltaZero deltaPos (L * m) cfg_cyc).1 = cfg_cyc.1 ∧
              (iterOCN0 deltaZero deltaPos (L * m) cfg_cyc).2 ≤ c_i := by
            intro m; induction m with
            | zero => intro _; exact ⟨rfl, Nat.le_refl c_i⟩
            | succ m' ih =>
              intro hm_le
              rcases ih (by rw [Nat.mul_succ] at hm_le; omega) with ⟨hq_m, hc_m⟩
              let cur_m := iterOCN0 deltaZero deltaPos (L * m') cfg_cyc
              change cur_m.1 = cfg_cyc.1 at hq_m
              change cur_m.2 ≤ c_i at hc_m
              have hstep_L : iterOCN0 deltaZero deltaPos (L * (m' + 1)) cfg_cyc =
                  iterOCN0 deltaZero deltaPos L cur_m := by
                rw [Nat.mul_succ, Nat.add_comm (L * m') L, iterOCN0_add]
              have hboth_pos : ∀ r : Nat, r < L ->
                  (iterOCN0 deltaZero deltaPos r (cfg_cyc.1, cur_m.2)).2 ≥ 1 ∧
                  (iterOCN0 deltaZero deltaPos r (cfg_cyc.1, c_i)).2 ≥ 1 := by
                intro r hr
                have hp1 : cur_m = (cfg_cyc.1, cur_m.2) := Prod.ext hq_m rfl
                have hp2 : cfg_cyc = (cfg_cyc.1, c_i) := rfl
                rw [← hp1, ← hp2]
                have hr_eq : iterOCN0 deltaZero deltaPos r cur_m =
                    iterOCN0 deltaZero deltaPos (L * m' + r) cfg_cyc := by
                  rw [Nat.add_comm (L * m') r, iterOCN0_add]
                rw [hr_eq]
                exact ⟨hpos_v (L * m' + r) (by rw [Nat.mul_succ] at hm_le; omega),
                       hpos_v r (by rw [Nat.mul_succ] at hm_le; omega)⟩
              rcases iterOCN0_pos_state_and_cross_sum deltaZero deltaPos L
                cfg_cyc.1 cur_m.2 c_i hboth_pos with ⟨hq1, hq2, hcsum⟩
              have hp1 : cur_m = (cfg_cyc.1, cur_m.2) := Prod.ext hq_m rfl
              rw [← hp1] at hq1 hcsum
              change (iterOCN0 deltaZero deltaPos L cur_m).2 + c_i = c_j + cur_m.2 at hcsum
              rw [hstep_L]
              refine ⟨hq1.trans (hq2.symm.trans hqj_cyc), by omega⟩
          rcases hperiod_noninc q_div (by omega) with ⟨_, hc_qdiv⟩
          have hc_U : (iterOCN0 deltaZero deltaPos U cfg_cyc).2 ≤ c_i + r_mod := by
            conv => lhs; rw [hU_dm, Nat.add_comm (L * q_div) r_mod]
            rw [iterOCN0_add]
            have h1 := iterOCN0_counter_le_add deltaZero deltaPos r_mod
              (iterOCN0 deltaZero deltaPos (L * q_div) cfg_cyc)
            omega
          have hc_U_eq_T : (iterOCN0 deltaZero deltaPos U cfg_cyc).2 =
              (iterOCN0 deltaZero deltaPos T cfg0).2 := by
            rw [← hcyc_shift U, ← hshift_s (i + U),
                show t_start + (i + U) = T by dsimp [U]; omega]
          rw [hc_U_eq_T] at hc_U
          dsimp [H_box, L] at hcT_ge hr_lt
          omega
      -- Positive cycle gain `Δ := c_j - c_i ≥ 1` locks `(q, c)` into exact affine growth forever!
      let delta := c_j - c_i
      have hdelta_pos : delta ≥ 1 := by dsimp [delta]; omega
      have hfirst_pos : ∀ r : Nat, r < L -> (iterOCN0 deltaZero deltaPos r cfg_cyc).2 ≥ 1 := by
        intro r hr
        rw [← hcyc_shift r]
        exact hpos_on_T (i + r) (by dsimp [L] at hr; omega)
      have hL_exact : iterOCN0 deltaZero deltaPos L cfg_cyc = (cfg_cyc.1, c_i + delta) :=
        Prod.ext hqj_cyc (by dsimp [delta, c_i, c_j]; omega)
      have hcyc_all : ∀ m : Nat,
          (∀ r : Nat, r < L ->
            iterOCN0 deltaZero deltaPos (L * m + r) cfg_cyc =
              ((iterOCN0 deltaZero deltaPos r cfg_cyc).1,
               m * delta + (iterOCN0 deltaZero deltaPos r cfg_cyc).2)) ∧
          (∀ s : Nat, s < L * (m + 1) -> (iterOCN0 deltaZero deltaPos s cfg_cyc).2 ≥ 1) := by
        intro m; induction m with
        | zero =>
          refine ⟨fun r _ => by simp, fun s hs => hfirst_pos s (by simpa using hs)⟩
        | succ m' ih =>
          rcases ih with ⟨ih_eq, ih_pos⟩
          have hnext_eq : ∀ r : Nat, r < L ->
              iterOCN0 deltaZero deltaPos (L * (m' + 1) + r) cfg_cyc =
                ((iterOCN0 deltaZero deltaPos r cfg_cyc).1,
                 (m' + 1) * delta + (iterOCN0 deltaZero deltaPos r cfg_cyc).2) := by
            intro r hr
            have hsp : L * (m' + 1) + r = (L * m' + r) + L := by rw [Nat.mul_succ]; omega
            have hlt_prev : L * m' + r ≤ L * (m' + 1) := by rw [Nat.mul_succ]; omega
            rw [hsp, iterOCN0_add deltaZero deltaPos (L * m' + r) L cfg_cyc, hL_exact]
            have hsh := iterOCN0_pos_shift deltaZero deltaPos (L * m' + r) delta cfg_cyc
              (fun s hs => ih_pos s (by omega))
            change iterOCN0 deltaZero deltaPos (L * m' + r) (cfg_cyc.1, c_i + delta) = _ at hsh
            rw [hsh, ih_eq r hr, Nat.succ_mul]
            exact Prod.ext rfl (by omega)
          refine ⟨hnext_eq, ?_⟩
          intro s hs
          by_cases hlt_prev : s < L * (m' + 1)
          · exact ih_pos s hlt_prev
          · let r := s - L * (m' + 1)
            have hr_lt : r < L := by dsimp [r]; rw [Nat.mul_succ L (m' + 1)] at hs; omega
            have hs_eq : s = L * (m' + 1) + r := by dsimp [r]; omega
            rw [hs_eq, hnext_eq r hr_lt]
            have hp0 := hfirst_pos r hr_lt
            omega
      rcases dvd_natFact L M_box hL1 (Nat.le_trans hLQ (by dsimp [M_box]; exact Nat.le_mul_of_pos_right Q (by omega))) with
        ⟨u_fac, hu_fac⟩
      have hu_pos : u_fac ≥ 1 := by
        cases u_fac with
        | zero =>
          rw [Nat.mul_zero] at hu_fac
          have hp := natFact_pos M_box; omega
        | succ _ => omega
      let slope := u_fac * delta
      refine ⟨slope, ⟨fun hall => False.elim (hnot_all hall), ?_⟩⟩
      intro m k hkM
      let t_cyc := t_start + i
      have hk_ge_M : k ≥ M_box := hkM
      have ht_cyc_le : t_cyc ≤ M_box :=
        Nat.le_trans (by dsimp [t_cyc]; omega : t_cyc ≤ T) hT_le
      have ht_cyc_le_k : t_cyc ≤ k := Nat.le_trans ht_cyc_le hk_ge_M
      have hfrom_cyc : ∀ d : Nat, d ≥ t_cyc ->
          iterOCN0 deltaZero deltaPos d cfg0 =
            iterOCN0 deltaZero deltaPos (d - t_cyc) cfg_cyc := by
        intro d hd
        have hd_sp : d = t_start + (i + (d - t_cyc)) := by dsimp [t_cyc]; omega
        conv => lhs; rw [hd_sp]
        rw [hshift_s (i + (d - t_cyc)), hcyc_shift (d - t_cyc)]
      let d0 := k - t_cyc
      let q0_div := d0 / L
      let r0_mod := d0 % L
      have hr0_lt : r0_mod < L := Nat.mod_lt d0 hL1
      have hd0_dm : d0 = L * q0_div + r0_mod := (Nat.div_add_mod d0 L).symm
      have hdm_m : k + P_ocn * m - t_cyc = L * (q0_div + u_fac * m) + r0_mod := by
        have h1 : k + P_ocn * m - t_cyc = d0 + P_ocn * m := by dsimp [d0]; omega
        rw [h1, hd0_dm]
        dsimp [P_ocn]
        rw [hu_fac, Nat.mul_assoc L u_fac m, Nat.mul_add L q0_div (u_fac * m)]
        omega
      rw [hfrom_cyc (k + P_ocn * m) (by omega), hfrom_cyc k ht_cyc_le_k, hdm_m]
      change (iterOCN0 deltaZero deltaPos (L * (q0_div + u_fac * m) + r0_mod) cfg_cyc).1 =
               (iterOCN0 deltaZero deltaPos d0 cfg_cyc).1 ∧
             (iterOCN0 deltaZero deltaPos (L * (q0_div + u_fac * m) + r0_mod) cfg_cyc).2 =
               m * slope + (iterOCN0 deltaZero deltaPos d0 cfg_cyc).2
      rw [hd0_dm,
          (hcyc_all (q0_div + u_fac * m)).1 r0_mod hr0_lt,
          (hcyc_all q0_div).1 r0_mod hr0_lt]
      refine ⟨rfl, ?_⟩
      dsimp [slope]
      rw [Nat.add_mul q0_div (u_fac * m) delta,
          Nat.mul_comm u_fac m, Nat.mul_assoc m u_fac delta]
      omega

theorem ocn_low_pad_peel_eq {Q : Nat}
    (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp) (q0 : Fin Q)
    (N1 N2 : Nat) (hN1 : N1 ≥ 1) (hN2 : N2 ≥ 1)
    (hcfg : runMSBOneCounterOCN Q deltaZero deltaPos q0 N1 =
              runMSBOneCounterOCN Q deltaZero deltaPos q0 N2) :
    ∀ (r R : Nat), R < 2 ^ r ->
      runMSBOneCounterOCN Q deltaZero deltaPos q0 (2 ^ r * N1 + R) =
        runMSBOneCounterOCN Q deltaZero deltaPos q0 (2 ^ r * N2 + R)
  | 0, R, hR => by
    have hR0 : R = 0 := by simp at hR; exact hR
    subst hR0
    simpa using hcfg
  | r + 1, R, hR => by
    have hrN1_pos : 2 ^ r * N1 ≥ 1 := Nat.mul_le_mul (pow2_pos_nat r) hN1
    have hrN2_pos : 2 ^ r * N2 ≥ 1 := Nat.mul_le_mul (pow2_pos_nat r) hN2
    have hR2 : R / 2 < 2 ^ r := by rw [Nat.pow_succ] at hR; omega
    have hsp1 : 2 ^ (r + 1) * N1 + R = 2 * (2 ^ r * N1) + R := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ r) 2, Nat.mul_assoc]
    have hsp2 : 2 ^ (r + 1) * N2 + R = 2 * (2 ^ r * N2) + R := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ r) 2, Nat.mul_assoc]
    have hbit1 : ((2 * (2 ^ r * N1) + R) % 2 == 1) = (R % 2 == 1) := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left]
    have hbit2 : ((2 * (2 ^ r * N2) + R) % 2 == 1) = (R % 2 == 1) := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left]
    have hdiv1 : (2 * (2 ^ r * N1) + R) / 2 = 2 ^ r * N1 + R / 2 := by omega
    have hdiv2 : (2 * (2 ^ r * N2) + R) / 2 = 2 ^ r * N2 + R / 2 := by omega
    rw [hsp1, hsp2,
        runMSBOneCounterOCN_step_pos deltaZero deltaPos q0 (2 * (2 ^ r * N1) + R) (by omega),
        runMSBOneCounterOCN_step_pos deltaZero deltaPos q0 (2 * (2 ^ r * N2) + R) (by omega),
        hbit1, hbit2, hdiv1, hdiv2,
        ocn_low_pad_peel_eq deltaZero deltaPos q0 N1 N2 hN1 hN2 hcfg r (R / 2) hR2]

/-- Canonical `Q = 1` non-regular Dyck `1^k 0^k` zero-testing `OCN` (`c` increments on `1`, decrements on `0` above `0`). -/
def dyckOCNZero : Fin 1 -> Bool -> Fin 1 × CounterOp :=
  fun q b => (q, if b then .inc else .stay)

def dyckOCNPos : Fin 1 -> Bool -> Fin 1 × CounterOp :=
  fun q b => (q, if b then .inc else .dec)

theorem dyckOCN_exact_1k_0j_formula :
    ∀ (k j : Nat), k ≥ 1 ->
      (runMSBOneCounterOCN 1 dyckOCNZero dyckOCNPos ⟨0, by decide⟩ (2 ^ j * (2 ^ k - 1))).2 = k - j := by
  have hones : ∀ k : Nat, k ≥ 1 ->
      (runMSBOneCounterOCN 1 dyckOCNZero dyckOCNPos ⟨0, by decide⟩ (2 ^ k - 1)).2 = k := by
    intro k; induction k with
    | zero => intro hk; omega
    | succ k' ih =>
      intro _
      cases k' with
      | zero => decide
      | succ m =>
        have ih_m := ih (by omega)
        have hp := pow2_pos_nat (m + 1)
        have hval : 2 ^ (m + 2) - 1 = 2 * (2 ^ (m + 1) - 1) + 1 := by
          rw [Nat.pow_succ 2 (m + 1)]; omega
        have hpos : 2 * (2 ^ (m + 1) - 1) + 1 ≥ 1 := by omega
        have hbit : ((2 * (2 ^ (m + 1) - 1) + 1) % 2 == 1) = true := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_left]; rfl
        have hdiv : (2 * (2 ^ (m + 1) - 1) + 1) / 2 = 2 ^ (m + 1) - 1 := by omega
        rw [hval, runMSBOneCounterOCN_step_pos dyckOCNZero dyckOCNPos _ _ hpos, hbit, hdiv]
        let prev := runMSBOneCounterOCN 1 dyckOCNZero dyckOCNPos ⟨0, by decide⟩ (2 ^ (m + 1) - 1)
        change prev.2 = m + 1 at ih_m
        change (stepOCN dyckOCNZero dyckOCNPos prev true).2 = m + 2
        unfold stepOCN dyckOCNPos applyCounterOp
        have hnz : ¬ (prev.2 = 0) := by omega
        rw [ite_false_of_w10 hnz, ih_m]
        rfl
  intro k j hk
  have hp_gt1 : 2 ^ k - 1 ≥ 1 := by
    have h2 : 2 ^ k ≥ 2 := by simpa using pow2_mono_nat hk
    omega
  rw [runMSBOneCounterOCN_mul_pow2 dyckOCNZero dyckOCNPos ⟨0, by decide⟩ (2 ^ k - 1) hp_gt1 j]
  let base := runMSBOneCounterOCN 1 dyckOCNZero dyckOCNPos ⟨0, by decide⟩ (2 ^ k - 1)
  have hbase : base.2 = k := hones k hk
  induction j with
  | zero => dsimp [iterOCN0]; exact hbase
  | succ j' ih =>
    simp only [iterOCN0]
    let cur := iterOCN0 dyckOCNZero dyckOCNPos j' base
    change cur.2 = k - j' at ih
    change (stepOCN dyckOCNZero dyckOCNPos cur false).2 = k - (j' + 1)
    unfold stepOCN dyckOCNZero dyckOCNPos applyCounterOp
    by_cases hc0 : cur.2 = 0
    · rw [ite_true_of_w10 hc0]; simp only [Bool.false_eq_true, ite_false]; omega
    · rw [ite_false_of_w10 hc0]; simp only [Bool.false_eq_true, ite_false]; omega

/--
  Theorem W10.3b (`one_counter_ocn_preimage_impossibility`, `zero custom axioms`):
  Beyond-Regular `∀ Q ≥ 1` Zero-Testing `1`-Counter Pushdown Automaton (`OCN`) Semilinear
  Dichotomy & Preimage Weight Impossibility (`Branch P1.2`):
  1. **Strict Non-Regularity of `1`-Counter Automata & `56 / 112 / 224` Floor Collapse**:
     - Across ALL `k ≥ 1`, the `1`-state Dyck `OCN` `(dyckOCNZero, dyckOCNPos)` satisfies
       `c(2 ^ (k - 1) * (2 ^ k - 1)) = 1 ≠ 0 = c(2 ^ k * (2 ^ k - 1))` (separating `1^k 0^(k-1)`
       from `1^k 0^k` for unbounded `k`, which NO finite-state automaton can achieve!),
       YET hits the zero-test floor and collides identically on `56, 112, 224`
       (`c(56) = c(112) = c(224) = 0`, `ZPOS_STERN_AND_OCN_PREIMAGE_COLLAPSE_56_VS_224`)!
  2. **Universal Unrestricted `OCN` Unary `0`-Run Semilinear Dichotomy (`∀ Q ≥ 1`)**:
     For EVERY `Q ≥ 1`, EVERY zero-testing `OCN` `(deltaZero, deltaPos)`, EVERY `B : Nat`, and
     EVERY `cfg0 : Fin Q × Nat` with `cfg0.2 ≤ B`, setting `M_box := Q * (B + Q + 1)` and
     `P_ocn := natFact M_box`, there exists `slope : Nat` (`slope = 0` on bounded runs) such that
     `iterOCN0 deltaZero deltaPos (k + P_ocn * m) cfg0` is exact-periodic in `.1` and exact-affine
     (`m * slope + ...`) in `.2` for ALL `k ≥ M_box, m : Nat`!
  3. **Universal Counter-Bounded `OCN` State+Counter Impossibility (`∀ Q ≥ 1, ∀ B ≥ 1`)**:
     Whenever an `OCN` has counter bounded by `B` (`∀ n, (runMSBOneCounterOCN Q deltaZero deltaPos q0 n).2 < B`),
     NO rational weight `fNum(OCN(n)) * P(zeroBitCount n, binBitLength n) / (fDen(OCN(n)) * Q(zeroBitCount n, binBitLength n))`
     can satisfy `IsPositiveRationalPreimageWeight`!
  4. **Universal Unbounded `1`-Incrementing / Dyck `OCN` Preimage Impossibility (`∀ Q ≥ 1`)**:
     In the complementary unbounded-counter regime where `1`-transitions increment the counter
     (`∀ q, (deltaZero q true).2 = .inc ∧ (deltaPos q true).2 = .inc`, including the non-regular
     Dyck `1^k 0^k` `OCN` itself!), NO polynomial quotient
       `evalNatPoly2 pTerms (runMSBOneCounterOCN Q deltaZero deltaPos q0 n).2 (binBitLength n) /
        evalNatPoly2 qTerms (runMSBOneCounterOCN Q deltaZero deltaPos q0 n).2 (binBitLength n)`
     can satisfy `IsPositiveRationalPreimageWeight`!
-/
theorem one_counter_ocn_preimage_impossibility :
    ((∀ k : Nat, k ≥ 1 ->
        (runMSBOneCounterOCN 1 dyckOCNZero dyckOCNPos ⟨0, by decide⟩ (2 ^ (k - 1) * (2 ^ k - 1))).2 = 1 ∧
        (runMSBOneCounterOCN 1 dyckOCNZero dyckOCNPos ⟨0, by decide⟩ (2 ^ k * (2 ^ k - 1))).2 = 0) ∧
     (runMSBOneCounterOCN 1 dyckOCNZero dyckOCNPos ⟨0, by decide⟩ 56).2 = 0 ∧
     (runMSBOneCounterOCN 1 dyckOCNZero dyckOCNPos ⟨0, by decide⟩ 112).2 = 0 ∧
     (runMSBOneCounterOCN 1 dyckOCNZero dyckOCNPos ⟨0, by decide⟩ 224).2 = 0) ∧
    (∀ (Q : Nat) (_hQ : Q ≥ 1)
       (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp)
       (B : Nat) (cfg0 : Fin Q × Nat),
      cfg0.2 ≤ B ->
      let M_box := Q * (B + Q + 1)
      let P_ocn := natFact M_box
      ∃ slope : Nat,
        ∀ (m k : Nat), k ≥ M_box ->
          (iterOCN0 deltaZero deltaPos (k + P_ocn * m) cfg0).1 =
            (iterOCN0 deltaZero deltaPos k cfg0).1 ∧
          (iterOCN0 deltaZero deltaPos (k + P_ocn * m) cfg0).2 =
            m * slope + (iterOCN0 deltaZero deltaPos k cfg0).2) ∧
    (∀ (Q B : Nat) (_hQ : Q ≥ 1) (_hB : B ≥ 1)
       (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp)
       (q0 : Fin Q)
       (_hbdd : ∀ n : Nat, (runMSBOneCounterOCN Q deltaZero deltaPos q0 n).2 < B)
       (fNum fDen : Fin Q × Nat -> Nat)
       (pTerms qTerms : NatPoly2)
       (pTheta qTheta : Nat),
      ¬ IsPositiveRationalPreimageWeight
        (fun n =>
          fNum (runMSBOneCounterOCN Q deltaZero deltaPos q0 n) *
            evalNatPoly2 pTerms (zeroBitCount n) (binBitLength n))
        (fun n =>
          fDen (runMSBOneCounterOCN Q deltaZero deltaPos q0 n) *
            evalNatPoly2 qTerms (zeroBitCount n) (binBitLength n))
        pTheta qTheta) ∧
    (∀ (Q : Nat) (_hQ : Q ≥ 1)
       (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp)
       (q0 : Fin Q)
       (_hinc1 : ∀ q : Fin Q, (deltaZero q true).2 = .inc ∧ (deltaPos q true).2 = .inc)
       (pTerms qTerms : NatPoly2)
       (pTheta qTheta : Nat),
      ¬ IsPositiveRationalPreimageWeight
        (fun n =>
          evalNatPoly2 pTerms (runMSBOneCounterOCN Q deltaZero deltaPos q0 n).2 (binBitLength n))
        (fun n =>
          evalNatPoly2 qTerms (runMSBOneCounterOCN Q deltaZero deltaPos q0 n).2 (binBitLength n))
        pTheta qTheta) := by
  refine ⟨⟨?_, by decide, by decide, by decide⟩,
          fun Q hQ dz dp B cfg0 hB => by
            rcases ocn_unary_zero_run_semilinear_dichotomy hQ dz dp B cfg0 hB with ⟨sl, _, hper⟩
            exact ⟨sl, hper⟩,
          ?_, ?_⟩
  · -- Part 1: Non-regular Dyck `1^k 0^(k-1)` vs `1^k 0^k`:
    intro k hk
    have h1 := dyckOCN_exact_1k_0j_formula k (k - 1) hk
    have h2 := dyckOCN_exact_1k_0j_formula k k hk
    exact ⟨by rw [h1]; omega, by rw [h2]; omega⟩
  · -- Part 3: Counter-bounded `OCN` (`< B`) reduces to a `(Q * B)`-state MSB finite automaton!
    intro Q B hQ hB deltaZero deltaPos q0 hbdd fNum fDen pTerms qTerms pTheta qTheta hw
    let QB := Q * B
    have hQB_pos : QB ≥ 1 := Nat.mul_le_mul hQ hB
    let encCfg : Fin Q × Nat -> Fin QB := fun cfg =>
      if h : cfg.2 < B then
        ⟨cfg.1.val * B + cfg.2, by
          have hm : (cfg.1.val + 1) * B ≤ Q * B := Nat.mul_le_mul_right B (by have := cfg.1.isLt; omega)
          rw [Nat.add_mul, Nat.one_mul] at hm; dsimp [QB]; omega⟩
      else ⟨0, hQB_pos⟩
    let decCfg : Fin QB -> Fin Q × Nat := fun st =>
      (⟨st.val / B, by
          have hlt := st.isLt
          dsimp [QB] at hlt
          by_cases hq_lt : st.val / B < Q
          · exact hq_lt
          · have hm : B * Q ≤ B * (st.val / B) := Nat.mul_le_mul_left B (by omega)
            have hdm := Nat.div_add_mod st.val B
            rw [Nat.mul_comm B Q] at hm
            omega⟩,
       st.val % B)
    have hdec_enc : ∀ cfg : Fin Q × Nat, cfg.2 < B -> decCfg (encCfg cfg) = cfg := by
      intro cfg hlt
      dsimp [encCfg, decCfg]
      split
      · dsimp only
        have hdiv : (cfg.1.val * B + cfg.2) / B = cfg.1.val := by
          rw [Nat.add_comm, Nat.mul_comm _ B,
              Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hlt, Nat.zero_add]
        have hmod : (cfg.1.val * B + cfg.2) % B = cfg.2 := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
        exact Prod.ext (Fin.ext hdiv) hmod
      · contradiction
    let deltaDFA : Fin QB -> Bool -> Fin QB := fun st b =>
      encCfg (stepOCN deltaZero deltaPos (decCfg st) b)
    let q0DFA : Fin QB := encCfg (q0, 0)
    have hsim : ∀ n : Nat,
        decCfg (runMSBAutomaton QB deltaDFA q0DFA n) =
          runMSBOneCounterOCN Q deltaZero deltaPos q0 n := by
      intro n
      -- Strong induction on `n` via `bound`:
      have hsim_bd : ∀ (bd m : Nat), m ≤ bd ->
          decCfg (runMSBAutomaton QB deltaDFA q0DFA m) =
            runMSBOneCounterOCN Q deltaZero deltaPos q0 m := by
        intro bd; induction bd with
        | zero =>
          intro m hm0
          have hm : m = 0 := by omega
          subst hm
          exact hdec_enc (q0, 0) hB
        | succ bd' ih =>
          intro m hmb
          by_cases hm0 : m = 0
          · subst hm0; exact hdec_enc (q0, 0) hB
          · rw [runMSBAutomaton_step_pos deltaDFA q0DFA m (by omega),
                runMSBOneCounterOCN_step_pos deltaZero deltaPos q0 m (by omega)]
            dsimp [deltaDFA]
            rw [ih (m / 2) (by omega)]
            have hlt_step :
                (stepOCN deltaZero deltaPos
                  (runMSBOneCounterOCN Q deltaZero deltaPos q0 (m / 2)) (m % 2 == 1)).2 < B := by
              rw [← runMSBOneCounterOCN_step_pos deltaZero deltaPos q0 m (by omega)]
              exact hbdd m
            exact hdec_enc _ hlt_step
      exact hsim_bd n n (Nat.le_refl n)
    have hw_dfa : IsPositiveRationalPreimageWeight
        (fun n =>
          (fun _ sM => fNum (decCfg sM)) (runLSBAutomaton QB deltaDFA q0DFA n)
            (runMSBAutomaton QB deltaDFA q0DFA n) *
            evalNatPoly2 pTerms (zeroBitCount n) (binBitLength n))
        (fun n =>
          (fun _ sM => fDen (decCfg sM)) (runLSBAutomaton QB deltaDFA q0DFA n)
            (runMSBAutomaton QB deltaDFA q0DFA n) *
            evalNatPoly2 qTerms (zeroBitCount n) (binBitLength n))
        pTheta qTheta := by
      have hfn1 : (fun n =>
          fNum (decCfg (runMSBAutomaton QB deltaDFA q0DFA n)) *
            evalNatPoly2 pTerms (zeroBitCount n) (binBitLength n)) =
          (fun n =>
          fNum (runMSBOneCounterOCN Q deltaZero deltaPos q0 n) *
            evalNatPoly2 pTerms (zeroBitCount n) (binBitLength n)) :=
        funext (fun n => by rw [hsim n])
      have hfn2 : (fun n =>
          fDen (decCfg (runMSBAutomaton QB deltaDFA q0DFA n)) *
            evalNatPoly2 qTerms (zeroBitCount n) (binBitLength n)) =
          (fun n =>
          fDen (runMSBOneCounterOCN Q deltaZero deltaPos q0 n) *
            evalNatPoly2 qTerms (zeroBitCount n) (binBitLength n)) :=
        funext (fun n => by rw [hsim n])
      dsimp only
      rwa [hfn1, hfn2]
    exact berg_meinardus_stateful_automaton_preimage_impossibility.2.2 QB hQB_pos
      deltaDFA deltaDFA q0DFA q0DFA (fun _ sM => fNum (decCfg sM)) (fun _ sM => fDen (decCfg sM))
      pTerms qTerms pTheta qTheta hw_dfa
  · -- Part 4: Unbounded `1`-incrementing / Dyck `OCN` along Mersenne `1`-spines:
    intro Q hQ deltaZero deltaPos q0 hinc1 pTerms qTerms pTheta qTheta hw
    have hiter1_inc : ∀ (d : Nat) (cfg : Fin Q × Nat),
        (iterOCN1 deltaZero deltaPos d cfg).2 = cfg.2 + d := by
      intro d; induction d with
      | zero => intro _; simp [iterOCN1]
      | succ d' ih =>
        intro cfg
        simp only [iterOCN1]
        let cur := iterOCN1 deltaZero deltaPos d' cfg
        have ih_c : cur.2 = cfg.2 + d' := ih cfg
        change (stepOCN deltaZero deltaPos cur true).2 = cfg.2 + (d' + 1)
        unfold stepOCN applyCounterOp
        by_cases hc0 : cur.2 = 0
        · rw [ite_true_of_w10 hc0, (hinc1 cur.1).1]; dsimp only; omega
        · rw [ite_false_of_w10 hc0, (hinc1 cur.1).2]; dsimp only; omega
    let c2 := (runMSBOneCounterOCN Q deltaZero deltaPos q0 2).2
    let c1 := (runMSBOneCounterOCN Q deltaZero deltaPos q0 1).2
    let dP := maxDegNatPoly2 pTerms
    let dQ := maxDegNatPoly2 qTerms
    let D := dP + dQ
    let C := c2 + c1 + 6
    have hC_pos : C ≥ 1 := by dsimp [C]; omega
    let X := 3 * (D * C + 1) + 2
    have hX_ge : X ≥ (1 + 1 + 1) * (D * C + 1) := by dsimp [X]; omega
    let s := X + 1
    have hs_ge2 : s ≥ 2 := by dsimp [s, X]; omega
    let ms1 := 3 * 2 ^ s - 1
    let evs1 := 2 * ms1
    let ns1 := 2 ^ (s + 1) - 1
    have hp2_ge4 : 2 ^ s ≥ 4 := by simpa using pow2_mono_nat hs_ge2
    have hms1_ge3 : ms1 ≥ 3 := by dsimp [ms1]; omega
    have hevs1_ge3 : evs1 ≥ 3 := by dsimp [evs1]; omega
    have hns1_ge3 : ns1 ≥ 3 := by dsimp [ns1]; rw [Nat.pow_succ 2 s]; omega
    rcases ripple_carry_alternating_cascade_and_mersenne_triples.2.2 (s + 1) (by omega) with
      ⟨hms1_m3_raw, hns1_div_raw, _, _, _, hbl_n_raw, hbl_m_raw, hbl_ev_raw⟩
    have hm_simp : 3 * 2 ^ (s + 1 - 1) - 1 = ms1 := by rw [Nat.add_sub_cancel]
    rw [hm_simp] at hms1_m3_raw hns1_div_raw hbl_m_raw hbl_ev_raw
    have hm1_val : 2 ^ s * 2 + (2 ^ s - 1) = ms1 := by
      dsimp [ms1]; have hp := pow2_pos_nat s; generalize 2 ^ s = p2 at hp ⊢; omega
    have hn1_val : 2 ^ s * 1 + (2 ^ s - 1) = ns1 := by
      dsimp [ns1]; rw [Nat.pow_succ 2 s]; have hp := pow2_pos_nat s; generalize 2 ^ s = p2 at hp ⊢; omega
    have hc_ms1 : (runMSBOneCounterOCN Q deltaZero deltaPos q0 ms1).2 = s + c2 := by
      rw [← hm1_val, runMSBOneCounterOCN_mersenne_tail deltaZero deltaPos q0 2 (by decide) s,
          hiter1_inc s]
      dsimp [c2]; omega
    have hc_ns1 : (runMSBOneCounterOCN Q deltaZero deltaPos q0 ns1).2 = s + c1 := by
      rw [← hn1_val, runMSBOneCounterOCN_mersenne_tail deltaZero deltaPos q0 1 (by decide) s,
          hiter1_inc s]
      dsimp [c1]; omega
    have hc_evs1_bounds :
        X ≤ (runMSBOneCounterOCN Q deltaZero deltaPos q0 evs1).2 ∧
        (runMSBOneCounterOCN Q deltaZero deltaPos q0 evs1).2 ≤ X + C := by
      dsimp [evs1]
      rw [runMSBOneCounterOCN_step_pos deltaZero deltaPos q0 (2 * ms1) (by omega),
          show ((2 * ms1) % 2 == 1) = false by rw [Nat.mul_mod_right]; rfl,
          show (2 * ms1) / 2 = ms1 by omega]
      let cfg_m := runMSBOneCounterOCN Q deltaZero deltaPos q0 ms1
      change cfg_m.2 = s + c2 at hc_ms1
      change X ≤ (stepOCN deltaZero deltaPos cfg_m false).2 ∧
             (stepOCN deltaZero deltaPos cfg_m false).2 ≤ X + C
      unfold stepOCN
      have hnz : ¬ (cfg_m.2 = 0) := by omega
      rw [ite_false_of_w10 hnz]
      dsimp only [s, C] at hc_ms1 ⊢
      cases (deltaPos cfg_m.1 false).2 <;> simp only [applyCounterOp] <;> omega
    have hbl_ms1 : binBitLength ms1 = s + 2 := by rw [hbl_m_raw]
    have hbl_evs1 : binBitLength evs1 = s + 3 := by dsimp [evs1]; rw [hbl_ev_raw]
    have hbl_ns1 : binBitLength ns1 = s + 1 := by dsimp [ns1] at hbl_n_raw ⊢; rw [hbl_n_raw]
    have hpre := hw.2.2.2.2 ms1 hms1_ge3 hms1_m3_raw
    dsimp only at hpre
    rw [hns1_div_raw] at hpre
    have hcanc := nat_mul_le_cancel_left_w5 qTheta _ _
      (Nat.lt_of_lt_of_le hw.1 hw.2.1)
      (Nat.le_trans hpre (Nat.mul_le_mul_right _ hw.2.1))
    let P_m := evalNatPoly2 pTerms (runMSBOneCounterOCN Q deltaZero deltaPos q0 ms1).2 (binBitLength ms1)
    let Q_m := evalNatPoly2 qTerms (runMSBOneCounterOCN Q deltaZero deltaPos q0 ms1).2 (binBitLength ms1)
    let P_ev := evalNatPoly2 pTerms (runMSBOneCounterOCN Q deltaZero deltaPos q0 evs1).2 (binBitLength evs1)
    let Q_ev := evalNatPoly2 qTerms (runMSBOneCounterOCN Q deltaZero deltaPos q0 evs1).2 (binBitLength evs1)
    let P_n := evalNatPoly2 pTerms (runMSBOneCounterOCN Q deltaZero deltaPos q0 ns1).2 (binBitLength ns1)
    let Q_n := evalNatPoly2 qTerms (runMSBOneCounterOCN Q deltaZero deltaPos q0 ns1).2 (binBitLength ns1)
    change (P_ev * Q_n + P_n * Q_ev) * Q_m ≤ P_m * (Q_ev * Q_n) at hcanc
    have hPm_pos : P_m ≥ 1 := (hw.2.2.1 ms1 hms1_ge3).1
    have hQev_pos : Q_ev ≥ 1 := (hw.2.2.1 evs1 hevs1_ge3).2
    have hQn_pos : Q_n ≥ 1 := (hw.2.2.1 ns1 hns1_ge3).2
    have hpoly2_sand : ∀ (F : NatPoly2) (z1 L1 z2 L2 : Nat),
        X ≤ z1 -> z1 ≤ X + C -> X ≤ L1 -> L1 ≤ X + C ->
        X ≤ z2 -> z2 ≤ X + C -> X ≤ L2 -> L2 ≤ X + C ->
        X ^ (maxDegNatPoly2 F) * evalNatPoly2 F z1 L1 ≤
          (X + C) ^ (maxDegNatPoly2 F) * evalNatPoly2 F z2 L2 := by
      intro F z1 L1 z2 L2 _ hz1_hi _ hL1_hi hz2_lo _ hL2_lo _
      rcases evalNatPoly2_to_3_eq F z1 L1 with ⟨he1, hd1⟩
      rcases evalNatPoly2_to_3_eq F z2 L2 with ⟨he2, _⟩
      rw [he1, he2, hd1]
      apply evalNatPoly3_cross_ratio_bound _ X (X + C) z1 L1 1 z2 L2 1 (by omega)
      · exact Nat.le_trans (Nat.mul_le_mul_left X hz1_hi)
          (by rw [Nat.mul_comm X (X + C)]; exact Nat.mul_le_mul_left (X + C) hz2_lo)
      · exact Nat.le_trans (Nat.mul_le_mul_left X hL1_hi)
          (by rw [Nat.mul_comm X (X + C)]; exact Nat.mul_le_mul_left (X + C) hL2_lo)
      · omega
    have hb_m : X ≤ (runMSBOneCounterOCN Q deltaZero deltaPos q0 ms1).2 ∧
                (runMSBOneCounterOCN Q deltaZero deltaPos q0 ms1).2 ≤ X + C ∧
                X ≤ binBitLength ms1 ∧ binBitLength ms1 ≤ X + C := by
      rw [hc_ms1, hbl_ms1]; dsimp [s, C]; exact ⟨by omega, by omega, by omega, by omega⟩
    have hb_ev : X ≤ (runMSBOneCounterOCN Q deltaZero deltaPos q0 evs1).2 ∧
                 (runMSBOneCounterOCN Q deltaZero deltaPos q0 evs1).2 ≤ X + C ∧
                 X ≤ binBitLength evs1 ∧ binBitLength evs1 ≤ X + C := by
      rw [hbl_evs1]; dsimp [s, C]
      exact ⟨hc_evs1_bounds.1, hc_evs1_bounds.2, by omega, by omega⟩
    have hb_n : X ≤ (runMSBOneCounterOCN Q deltaZero deltaPos q0 ns1).2 ∧
                (runMSBOneCounterOCN Q deltaZero deltaPos q0 ns1).2 ≤ X + C ∧
                X ≤ binBitLength ns1 ∧ binBitLength ns1 ≤ X + C := by
      rw [hc_ns1, hbl_ns1]; dsimp [s, C]; exact ⟨by omega, by omega, by omega, by omega⟩
    have hPm_Pev : X ^ dP * P_m ≤ (X + C) ^ dP * P_ev :=
      hpoly2_sand pTerms _ _ _ _ hb_m.1 hb_m.2.1 hb_m.2.2.1 hb_m.2.2.2
        hb_ev.1 hb_ev.2.1 hb_ev.2.2.1 hb_ev.2.2.2
    have hQev_Qm : X ^ dQ * Q_ev ≤ (X + C) ^ dQ * Q_m :=
      hpoly2_sand qTerms _ _ _ _ hb_ev.1 hb_ev.2.1 hb_ev.2.2.1 hb_ev.2.2.2
        hb_m.1 hb_m.2.1 hb_m.2.2.1 hb_m.2.2.2
    have hPm_Pn : X ^ dP * P_m ≤ (X + C) ^ dP * P_n :=
      hpoly2_sand pTerms _ _ _ _ hb_m.1 hb_m.2.1 hb_m.2.2.1 hb_m.2.2.2
        hb_n.1 hb_n.2.1 hb_n.2.2.1 hb_n.2.2.2
    have hQn_Qm : X ^ dQ * Q_n ≤ (X + C) ^ dQ * Q_m :=
      hpoly2_sand qTerms _ _ _ _ hb_n.1 hb_n.2.1 hb_n.2.2.1 hb_n.2.2.2
        hb_m.1 hb_m.2.1 hb_m.2.2.1 hb_m.2.2.2
    let K_den := P_m * (Q_ev * Q_n)
    have hK_pos : K_den ≥ 1 := Nat.mul_le_mul hPm_pos (Nat.mul_le_mul hQev_pos hQn_pos)
    have hbr1 : X ^ D * K_den ≤ (X + C) ^ D * ((P_ev * Q_n) * Q_m) := by
      have hm := Nat.mul_le_mul_right Q_n (Nat.mul_le_mul hPm_Pev hQev_Qm)
      have hl : (X ^ dP * P_m * (X ^ dQ * Q_ev)) * Q_n = X ^ D * K_den := by
        dsimp [D, K_den]
        rw [Nat.pow_add X dP dQ, ← Nat.mul_assoc (X ^ dP * P_m),
            Nat.mul_assoc (X ^ dP) P_m (X ^ dQ), Nat.mul_comm P_m (X ^ dQ),
            ← Nat.mul_assoc (X ^ dP) (X ^ dQ) P_m,
            Nat.mul_assoc (X ^ dP * X ^ dQ) P_m Q_ev,
            Nat.mul_assoc (X ^ dP * X ^ dQ), Nat.mul_assoc P_m Q_ev Q_n]
      have hr : ((X + C) ^ dP * P_ev * ((X + C) ^ dQ * Q_m)) * Q_n =
          (X + C) ^ D * ((P_ev * Q_n) * Q_m) := by
        dsimp [D]
        rw [Nat.pow_add (X + C) dP dQ, ← Nat.mul_assoc ((X + C) ^ dP * P_ev),
            Nat.mul_assoc ((X + C) ^ dP) P_ev ((X + C) ^ dQ),
            Nat.mul_comm P_ev ((X + C) ^ dQ),
            ← Nat.mul_assoc ((X + C) ^ dP) ((X + C) ^ dQ) P_ev,
            Nat.mul_assoc ((X + C) ^ dP * (X + C) ^ dQ) P_ev Q_m,
            Nat.mul_assoc ((X + C) ^ dP * (X + C) ^ dQ),
            Nat.mul_assoc P_ev Q_m Q_n, Nat.mul_comm Q_m Q_n, ← Nat.mul_assoc P_ev Q_n Q_m]
      rwa [hl, hr] at hm
    have hbr2 : X ^ D * K_den ≤ (X + C) ^ D * ((P_n * Q_ev) * Q_m) := by
      have hm := Nat.mul_le_mul_right Q_ev (Nat.mul_le_mul hPm_Pn hQn_Qm)
      have hl : (X ^ dP * P_m * (X ^ dQ * Q_n)) * Q_ev = X ^ D * K_den := by
        dsimp [D, K_den]
        rw [Nat.pow_add X dP dQ, ← Nat.mul_assoc (X ^ dP * P_m),
            Nat.mul_assoc (X ^ dP) P_m (X ^ dQ), Nat.mul_comm P_m (X ^ dQ),
            ← Nat.mul_assoc (X ^ dP) (X ^ dQ) P_m,
            Nat.mul_assoc (X ^ dP * X ^ dQ) P_m Q_n,
            Nat.mul_assoc (X ^ dP * X ^ dQ), Nat.mul_assoc P_m Q_n Q_ev, Nat.mul_comm Q_n Q_ev]
      have hr : ((X + C) ^ dP * P_n * ((X + C) ^ dQ * Q_m)) * Q_ev =
          (X + C) ^ D * ((P_n * Q_ev) * Q_m) := by
        dsimp [D]
        rw [Nat.pow_add (X + C) dP dQ, ← Nat.mul_assoc ((X + C) ^ dP * P_n),
            Nat.mul_assoc ((X + C) ^ dP) P_n ((X + C) ^ dQ),
            Nat.mul_comm P_n ((X + C) ^ dQ),
            ← Nat.mul_assoc ((X + C) ^ dP) ((X + C) ^ dQ) P_n,
            Nat.mul_assoc ((X + C) ^ dP * (X + C) ^ dQ) P_n Q_m,
            Nat.mul_assoc ((X + C) ^ dP * (X + C) ^ dQ),
            Nat.mul_assoc P_n Q_m Q_ev, Nat.mul_comm Q_m Q_ev, ← Nat.mul_assoc P_n Q_ev Q_m]
      rwa [hl, hr] at hm
    have hsum := Nat.add_le_add hbr1 hbr2
    rw [← Nat.two_mul (X ^ D * K_den), ← Nat.mul_assoc 2 (X ^ D) K_den,
        ← Nat.mul_add ((X + C) ^ D),
        ← Nat.add_mul (P_ev * Q_n) (P_n * Q_ev) Q_m] at hsum
    have htot : ((1 + 1) * X ^ D) * K_den ≤ (1 * (X + C) ^ D) * K_den := by
      rw [Nat.one_mul]
      exact Nat.le_trans hsum (Nat.mul_le_mul_left ((X + C) ^ D) hcanc)
    have hle_b := nat_mul_le_cancel_right_w5 K_den _ _ hK_pos htot
    have hlt_b := bernoulli_nat_ratio_lt 1 1 D C X (by decide) (by decide) hC_pos hX_ge
    omega

-- ----------------------------------------------------------------------------
-- Section 3B: 7th Solvable Mixed-(2, 3) Cousin `T_diamond7` (`ω^5` Cascade, `Branch P5.9`)
-- ----------------------------------------------------------------------------

/-- Cone 8 of `T_diamond7`: `34603 + x = 2 ^ u * 3 ^ v` with `u ≥ 22, v ≥ 1` (starting at `x = 12548309`). -/
def isDiamond7Cone8 (x : Nat) : Prop :=
  x ≥ 12548309 ∧ x % 4194304 = 4159701 ∧ x % 3 = 2 ∧ coprime23Core (34603 + x) = 1

instance (x : Nat) : Decidable (isDiamond7Cone8 x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/--
  7th solvable mixed-(2, 3) Collatz cousin `T_diamond7` on `Nat`:
  Extends `T_diamond6` by adding Cone 8 (`isDiamond7Cone8 x -> (3 * x + 1) / 128`, a genuine
  `v_2(3x + 1) = 7` Syracuse jump that steps `2 ^ u * 3 ^ v - 34603 -> 2 ^ (u - 7) * 3 ^ (v + 1) - 811`
  directly into Cone 7 -> Cone 6 -> Cone 5's `r`-block spiral climb, e.g. `12548309 -> 294101 -> 6893 -> 2585`,
  while converging globally to `1` under a 5-tier `ω^5` ranking)!
-/
def cousinDiamond7Step (x : Nat) : Nat :=
  if isDiamond7Cone8 x then (3 * x + 1) / 128 else cousinDiamond6Step x

def cousinDiamond7Iter : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamond7Iter k (cousinDiamond7Step x)

theorem cousinDiamond7Iter_add : ∀ (a b x : Nat),
    cousinDiamond7Iter (a + b) x = cousinDiamond7Iter b (cousinDiamond7Iter a x)
  | 0, _, _ => by simp [cousinDiamond7Iter]
  | a + 1, b, x => by
    rw [Nat.succ_add]
    exact cousinDiamond7Iter_add a b (cousinDiamond7Step x)

/-- Signed extension of `T_diamond7` (`q = 3`) to `Int` for `M2 = Z^-` separation. -/
def cousinDiamond7StepInt (x : Int) : Int :=
  if x ≥ 12548309 ∧ x % 4194304 = 4159701 ∧ x % 3 = 2 ∧ coprime23Core (34603 + x.toNat) = 1
  then (3 * x + 1) / 128
  else cousinDiamond6StepInt x

def cousinDiamond7IterInt : Nat -> Int -> Int
  | 0, x => x
  | k + 1, x => cousinDiamond7IterInt k (cousinDiamond7StepInt x)

/-- Hensel lift of `invMod32768Odd` (`2^15`) to `mod 4194304` (`2^22`, since `15 * 2 = 30 ≥ 22`). -/
def invMod4194304Odd (d : Nat) : Nat :=
  let i32k := invMod32768Odd d
  (i32k * (8388610 - ((d % 4194304) * i32k) % 4194304)) % 4194304

/-- Canonical reduced-pair extension of `T_diamond7` (`q = 3`) to positive `Q_(6)^+`. -/
def cousinDiamond7StepQ6 (p : Nat × Nat) : Nat × Nat :=
  let num := p.1
  let den := p.2
  let r4m := (num * invMod4194304Odd den) % 4194304
  let r3 := (num * (den % 3)) % 3
  if num ≥ 12548309 * den ∧ r4m = 4159701 ∧ r3 = 2 ∧ core3 (core2 (34603 * den + num)) = den
  then reduceRatPair (3 * num + den) (128 * den)
  else cousinDiamond6StepQ6 p

def cousinDiamond7IterQ6 : Nat -> (Nat × Nat) -> (Nat × Nat)
  | 0, p => p
  | k + 1, p => cousinDiamond7IterQ6 k (cousinDiamond7StepQ6 p)

/-- Generalized odd-multiplier `q` step of `T_diamond7` on `Nat` for `M3` (`q = 7`) separation. -/
def cousinDiamond7StepParam (q x : Nat) : Nat :=
  if isDiamond7Cone8 x then (q * x + 1) / 128 else cousinDiamond6StepParam q x

def cousinDiamond7IterParam (q : Nat) : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamond7IterParam q k (cousinDiamond7StepParam q x)

/-- Exact `Nat`/`Int` step agreement for `T_diamond7` (`zero custom axioms`). -/
theorem cousinDiamond7StepInt_ofNat_eq (x : Nat) :
    cousinDiamond7StepInt (x : Int) = (cousinDiamond7Step x : Int) := by
  have h1 : ((x : Int) ≥ 12548309) ↔ (x ≥ 12548309) := by omega
  have h2 : ((x : Int) % 4194304 = 4159701) ↔ (x % 4194304 = 4159701) :=
    ⟨Int.ofNat.inj, congrArg Int.ofNat⟩
  have h3 : ((x : Int) % 3 = 2) ↔ (x % 3 = 2) :=
    ⟨Int.ofNat.inj, congrArg Int.ofNat⟩
  have hdiv : ((3 * (x : Int) + 1) / 128) = (((3 * x + 1) / 128 : Nat) : Int) := by omega
  have htoNat : (x : Int).toNat = x := rfl
  unfold cousinDiamond7StepInt cousinDiamond7Step isDiamond7Cone8
  rw [htoNat]
  simp only [h1, h2, h3]
  by_cases hc8 : x ≥ 12548309 ∧ x % 4194304 = 4159701 ∧ x % 3 = 2 ∧ coprime23Core (34603 + x) = 1
  · simp only [hc8, and_self, ite_true, hdiv]
  · simp only [hc8, ite_false]
    exact cousinDiamond6StepInt_ofNat_eq x

theorem cousinDiamond7Step_pos (x : Nat) (hx : x > 0) : cousinDiamond7Step x > 0 := by
  unfold cousinDiamond7Step
  by_cases hc8 : isDiamond7Cone8 x
  · simp only [hc8, ite_true]
    have hge : x ≥ 12548309 := hc8.1
    clear hc8
    have hle : (3 * 12548309 + 1) / 128 ≤ (3 * x + 1) / 128 :=
      Nat.div_le_div_right (by omega)
    exact Nat.lt_of_lt_of_le (by decide : 0 < (3 * 12548309 + 1) / 128) hle
  · simp only [hc8, ite_false]; exact cousinDiamond6Step_pos x hx

theorem cousinDiamond7Step_eq_d6_of_not_cone8 (x : Nat) (hnc8 : ¬ isDiamond7Cone8 x) :
    cousinDiamond7Step x = cousinDiamond6Step x := by
  unfold cousinDiamond7Step; simp [hnc8]

/--
  Theorem W10.3c (`cousin_diamond7_outside_cones45678_strict_descent`, `zero custom axioms`):
  Outside Cones 4, 5, 6, 7, and 8, EVERY `x > 2` strictly decreases `cousinDiamond2Phi` in 1 step!
-/
theorem cousin_diamond7_outside_cones45678_strict_descent
    (x : Nat) (hx : x > 2)
    (hnc4 : ¬ isDiamond3Cone4 x) (hnc5 : ¬ isDiamond4Cone5 x)
    (hnc6 : ¬ isDiamond5Cone6 x) (hnc7 : ¬ isDiamond6Cone7 x)
    (hnc8 : ¬ isDiamond7Cone8 x) :
    cousinDiamond2Phi (cousinDiamond7Step x) < cousinDiamond2Phi x := by
  rw [cousinDiamond7Step_eq_d6_of_not_cone8 x hnc8]
  exact cousin_diamond6_outside_cones4567_strict_descent x hx hnc4 hnc5 hnc6 hnc7

-- Modular & Diophantine Cone-8 avoidance helpers (`4159701 % 32768 = 30933, % 256 = 213, % 32 = 21, % 16 = 5, % 8 = 5, % 4 = 1`):

theorem mod32768_of_cone8 (z : Nat) (hc8 : isDiamond7Cone8 z) : z % 32768 = 30933 := by
  have h := congrArg (· % 32768) hc8.2.1
  rwa [Nat.mod_mod_of_dvd z (by decide : 32768 ∣ 4194304)] at h

theorem mod32_of_cone8 (z : Nat) (hc8 : isDiamond7Cone8 z) : z % 32 = 21 := by
  have h := congrArg (· % 32) (mod32768_of_cone8 z hc8)
  rwa [Nat.mod_mod_of_dvd z (by decide : 32 ∣ 32768)] at h

theorem not_cone8_of_even (z : Nat) (hev : z % 2 = 0) : ¬ isDiamond7Cone8 z := by
  intro hc8
  have h := congrArg (· % 2) (mod32_of_cone8 z hc8)
  rw [Nat.mod_mod_of_dvd z (by decide : 2 ∣ 32), hev] at h
  cases h

theorem not_cone8_of_mod4_eq_3 (z : Nat) (hm4 : z % 4 = 3) : ¬ isDiamond7Cone8 z := by
  intro hc8
  have h := congrArg (· % 4) (mod32_of_cone8 z hc8)
  rw [Nat.mod_mod_of_dvd z (by decide : 4 ∣ 32), hm4] at h
  cases h

theorem not_cone8_of_mod8_ne_5 (z : Nat) (hm8 : z % 8 ≠ 5) : ¬ isDiamond7Cone8 z := by
  intro hc8
  have h := congrArg (· % 8) (mod32_of_cone8 z hc8)
  rw [Nat.mod_mod_of_dvd z (by decide : 8 ∣ 32)] at h
  exact hm8 h

theorem not_cone8_of_mod16_ne_5 (z : Nat) (hm16 : z % 16 ≠ 5) : ¬ isDiamond7Cone8 z := by
  intro hc8
  have h := congrArg (· % 16) (mod32_of_cone8 z hc8)
  rw [Nat.mod_mod_of_dvd z (by decide : 16 ∣ 32)] at h
  exact hm16 h

theorem not_cone8_of_mod32_ne_21 (z : Nat) (hm32 : z % 32 ≠ 21) : ¬ isDiamond7Cone8 z :=
  fun hc8 => hm32 (mod32_of_cone8 z hc8)

theorem not_cone8_of_mod256_ne_213 (z : Nat) (hm256 : z % 256 ≠ 213) : ¬ isDiamond7Cone8 z := by
  intro hc8
  have h := congrArg (· % 256) (mod32768_of_cone8 z hc8)
  rw [Nat.mod_mod_of_dvd z (by decide : 256 ∣ 32768)] at h
  exact hm256 h

theorem not_cone8_of_mod32768_ne_30933 (z : Nat) (hm32k : z % 32768 ≠ 30933) : ¬ isDiamond7Cone8 z :=
  fun hc8 => hm32k (mod32768_of_cone8 z hc8)

theorem not_cone8_of_mod3_ne_2 (z : Nat) (hm3 : z % 3 ≠ 2) : ¬ isDiamond7Cone8 z := by
  rintro ⟨_, _, h3, _⟩; exact hm3 h3

/--
  Crucial Diophantine Cone-8 Exclusion (`not_cone8_six_mul_pow9_sub1`, `zero custom axioms`):
  Even though `ur = 6 * 9 ^ m - 1` (`m ≥ 1`) shares `ur % 16 = 5 = 4159701 % 16` AND `ur % 3 = 2`,
  `ur` NEVER enters `isDiamond7Cone8` for ANY `m : Nat`!
  Proof: For `m = 0`, `ur = 5 < 12548309`; for `m ≥ 1`, `ur + 34603 = 6 * (9 ^ m + 5767)` having
  `coprime23Core = 1` forces `9 ^ m + 5767 = 2 ^ k` (since `(9 ^ m + 5767) % 3 = 1`), hence
  `2 ^ k % 9 = 7 = 2 ^ 4 % 9` (`k % 6 = 4 => k % 3 = 1 => 2 ^ k % 7 = 2`), whereas
  `(9 ^ m + 5767) % 7 ∈ {0, 1, 3}` (`9 ^ 3 % 7 = 1`) — disjoint from `{2}`!
-/
theorem not_cone8_six_mul_pow9_sub1 (m : Nat) :
    ¬ isDiamond7Cone8 (6 * 9 ^ m - 1) := by
  have hm_mod3 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rintro ⟨hge, h4m, h3, hcop⟩
  clear h4m h3
  by_cases hm0 : m = 0
  · subst hm0; simp at hge
  · have hm1 : m ≥ 1 := by clear hcop hm_mod3; omega
    clear hge hm0
    rcases (⟨5767 + 9 ^ m, rfl⟩ : ∃ M : Nat, M = 5767 + 9 ^ m) with ⟨M, hM_def⟩
    have hp9 := nat_pow_pos_of_pos 9 (by decide) m
    have hM_pos : M > 0 := by clear hcop hm_mod3; generalize 9 ^ m = p9 at hp9 hM_def; omega
    have h3M_pos : 3 * M > 0 := Nat.mul_pos (by decide) hM_pos
    have hur_eq : 34603 + (6 * 9 ^ m - 1) = 2 * (3 * M) := by
      clear hcop hm_mod3 hM_pos h3M_pos
      generalize 9 ^ m = p9 at hp9 hM_def ⊢
      omega
    rw [hur_eq, coprime23Core_mul2 (3 * M) h3M_pos, coprime23Core_mul3 M hM_pos] at hcop
    rcases decomp_2_3_exact M hM_pos with ⟨_, _, _, _, _, hM_mul⟩
    have h9_m9 : 9 ^ m % 9 = 0 := by
      have hm_sp : m = (m - 1) + 1 := by clear hcop hm_mod3 hM_def hp9 hM_pos h3M_pos hur_eq hM_mul; omega
      rw [hm_sp, Nat.pow_succ]; exact Nat.mul_mod_left _ 9
    have hM_m9 : M % 9 = 7 := by rw [hM_def, Nat.add_mod, h9_m9]
    have hM_nd3 : M % 3 ≠ 0 := by
      have h3 := congrArg (· % 3) hM_m9
      rw [Nat.mod_mod_of_dvd M (by decide : 3 ∣ 9)] at h3
      rw [h3]; decide
    have hv3_1 : v3Pow M = 1 := v3Pow_of_not_div3 M hM_nd3
    rw [hv3_1, hcop, Nat.mul_one, Nat.mul_one] at hM_mul
    rcases eq_pow2_of_v2Pow_aux M M hM_pos (Nat.le_refl M) with ⟨k, hk_pow⟩
    rw [hk_pow] at hM_mul
    -- Modulo `9`: `2 ^ k % 9 = 7`, forcing `k % 6 = 4` (`k % 3 = 1`):
    have h2k_9 : 2 ^ k % 9 = 7 := by rw [hM_mul, hM_m9]
    clear hm1 hp9 hM_pos h3M_pos hur_eq hcop h9_m9 hM_m9 hM_nd3 hv3_1 hk_pow
    have h2_rk6 : 2 ^ (k % 6) % 9 = 7 := by
      have hk_dm : k = 6 * (k / 6) + k % 6 := (Nat.div_add_mod k 6).symm
      conv at h2k_9 => lhs; rw [hk_dm, Nat.pow_add 2 (6 * (k / 6)) (k % 6),
        Nat.mul_mod, pow2_six_mul_mod9_w8 (k / 6), Nat.one_mul, Nat.mod_mod]
      exact h2k_9
    have hk_m6 : k % 6 = 4 := by
      have hk6_cases : k % 6 = 0 ∨ k % 6 = 1 ∨ k % 6 = 2 ∨ k % 6 = 3 ∨ k % 6 = 4 ∨ k % 6 = 5 := by
        clear hM_def hM_mul h2k_9 h2_rk6 hm_mod3; omega
      rcases hk6_cases with h | h | h | h | h | h
      · rw [h] at h2_rk6; cases h2_rk6
      · rw [h] at h2_rk6; cases h2_rk6
      · rw [h] at h2_rk6; cases h2_rk6
      · rw [h] at h2_rk6; cases h2_rk6
      · exact h
      · rw [h] at h2_rk6; cases h2_rk6
    have hk_m3 : k % 3 = 1 := by
      have h := congrArg (· % 3) hk_m6
      rwa [Nat.mod_mod_of_dvd k (by decide : 3 ∣ 6)] at h
    clear h2k_9 h2_rk6 hk_m6
    -- Modulo `7`: `2 ^ 3 % 7 = 1 => 2 ^ k % 7 = 2`, while `9 ^ 3 % 7 = 1 => M % 7 ∈ {0, 1, 3}`!
    have h2_3mul_7 : ∀ q : Nat, 2 ^ (3 * q) % 7 = 1 := by
      intro q; induction q with
      | zero => rfl
      | succ q' ih => rw [Nat.mul_succ, Nat.pow_add, Nat.mul_mod, ih]
    have h2k_7 : 2 ^ k % 7 = 2 := by
      have hk_dm : k = 3 * (k / 3) + 1 := by
        conv => lhs; rw [← Nat.div_add_mod k 3, hk_m3]
      rw [hk_dm, Nat.pow_add 2 (3 * (k / 3)) 1, Nat.mul_mod, h2_3mul_7 (k / 3)]
    have h9_3mul_7 : ∀ q : Nat, 9 ^ (3 * q) % 7 = 1 := by
      intro q; induction q with
      | zero => rfl
      | succ q' ih => rw [Nat.mul_succ, Nat.pow_add, Nat.mul_mod, ih]
    have h9e_7 : 9 ^ m % 7 = 9 ^ (m % 3) % 7 := by
      have hm_dm : m = 3 * (m / 3) + m % 3 := (Nat.div_add_mod m 3).symm
      conv => lhs; rw [hm_dm]
      rw [Nat.pow_add 9 (3 * (m / 3)) (m % 3), Nat.mul_mod, h9_3mul_7 (m / 3), Nat.one_mul, Nat.mod_mod]
    have hM_7_ne2 : M % 7 ≠ 2 := by
      rw [hM_def, Nat.add_mod, h9e_7]
      rcases hm_mod3 with h0 | h1 | h2
      · rw [h0]; decide
      · rw [h1]; decide
      · rw [h2]; decide
    exact hM_7_ne2 (by rw [← hM_mul, h2k_7])

theorem cousin_diamond7_mersenne_scaled :
    ∀ (k a q : Nat), k + 1 ≤ a -> q ≥ 1 ->
      cousinDiamond7Iter k (2 ^ a * q - 1) = 3 ^ k * 2 ^ (a - k) * q - 1
  | 0, _, _, _, _ => by simp [cousinDiamond7Iter]
  | k + 1, a, q, hka, hq => by
    have hp4 : 2 ^ a * q = 4 * (2 ^ (a - 2) * q) := by
      conv => lhs; rw [show a = (a - 2) + 2 by omega]
      rw [Nat.pow_add 2 (a - 2) 2, show (2 : Nat) ^ 2 = 4 from rfl,
          Nat.mul_comm (2 ^ (a - 2)) 4, Nat.mul_assoc]
    have hm_pos : 2 ^ (a - 2) * q ≥ 1 := Nat.mul_le_mul (pow2_pos_nat (a - 2)) hq
    have hz4 : (2 ^ a * q - 1) % 4 = 3 := by omega
    simp only [cousinDiamond7Iter]
    rw [cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_mod4_eq_3 _ hz4)]
    have hd6 := cousin_diamond6_mersenne_scaled 1 a q (by omega) hq
    simp only [cousinDiamond6Iter, Nat.pow_one] at hd6
    have hstep_eq : cousinDiamond6Step (2 ^ a * q - 1) = 2 ^ (a - 1) * (3 * q) - 1 := by
      rw [hd6]
      apply congrArg (· - 1)
      rw [Nat.mul_comm 3 (2 ^ (a - 1)), Nat.mul_assoc]
    rw [hstep_eq, cousin_diamond7_mersenne_scaled k (a - 1) (3 * q) (by omega) (by omega),
        show a - 1 - k = a - (k + 1) by omega, Nat.pow_succ 3 k]
    apply congrArg (· - 1)
    calc
      3 ^ k * 2 ^ (a - (k + 1)) * (3 * q)
          = 3 ^ k * (2 ^ (a - (k + 1)) * 3) * q := by rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
      _ = 3 ^ k * (3 * 2 ^ (a - (k + 1))) * q := by rw [Nat.mul_comm (2 ^ (a - (k + 1))) 3]
      _ = 3 ^ k * 3 * 2 ^ (a - (k + 1)) * q := by rw [← Nat.mul_assoc (3 ^ k) 3]

theorem cousin_diamond7_even9_spine_drain :
    ∀ k : Nat, cousinDiamond7Iter k ((9 ^ (k + 1) - 1) / 4) = 2
  | 0 => rfl
  | k + 1 => by
    let j := k + 1
    have hp9j_ge9 : 9 ^ j ≥ 9 := by
      dsimp [j]; rw [Nat.pow_succ]; have hp := nat_pow_pos_of_pos 9 (by decide) k; omega
    have hp9j_m8 : 9 ^ j % 8 = 1 := pow9_mod8_eq_one_w5 j
    let q := (9 ^ j - 1) / 8
    have hp9j_eq : 9 ^ j = 8 * q + 1 := by dsimp [q]; omega
    have he_j1 : (9 ^ (j + 1) - 1) / 4 = 18 * q + 2 := by rw [Nat.pow_succ 9 j, hp9j_eq]; omega
    simp only [cousinDiamond7Iter]
    change cousinDiamond7Iter k (cousinDiamond7Step ((9 ^ (j + 1) - 1) / 4)) = 2
    have hnc8 : ¬ isDiamond7Cone8 ((9 ^ (j + 1) - 1) / 4) := by
      rw [he_j1]; exact not_cone8_of_even _ (by omega)
    rw [cousinDiamond7Step_eq_d6_of_not_cone8 _ hnc8]
    have hd6 : cousinDiamond6Step ((9 ^ (j + 1) - 1) / 4) = (9 ^ j - 1) / 4 := by
      have he_j : (9 ^ j - 1) / 4 = 2 * q := by rw [hp9j_eq]; omega
      rw [he_j1, he_j,
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (18 * q + 2) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]; unfold cousinDiamond3Step
      have hq_pos : q ≥ 1 := by dsimp [q]; omega
      have hodd_f : ¬ ((18 * q + 2) % 2 = 1) := by omega
      have h18_t : 18 * q + 2 ≥ 20 ∧ (18 * q + 2) % 18 = 2 := ⟨by omega, by omega⟩
      simp only [hodd_f, h18_t, and_self, ite_true, ite_false]; omega
    rw [hd6]
    exact cousin_diamond7_even9_spine_drain k

theorem cousin_diamond7_pow3_sub1_drain :
    ∀ k : Nat, cousinDiamond7Iter k (3 ^ (k + 1) - 1) = 2
  | 0 => rfl
  | k + 1 => by
    let j := k + 1
    have hp3_ge3 : 3 ^ j ≥ 3 := by dsimp [j]; rw [Nat.pow_succ]; have hp := pow3_pos_nat k; omega
    have ho_j1 := pow3_odd_nat_sec8 (j + 1)
    have hp_j1 := pow3_pos_nat (j + 1)
    simp only [cousinDiamond7Iter]
    change cousinDiamond7Iter k (cousinDiamond7Step (3 ^ (j + 1) - 1)) = 2
    rw [cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
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
    exact cousin_diamond7_pow3_sub1_drain k

theorem cousin_diamond7_cone5_two_step_climb :
    ∀ (q_c a b : Nat), 3 * q_c + 2 ≤ a -> b ≥ 1 ->
      cousinDiamond7Iter (2 * q_c) (2 ^ a * 3 ^ b - 7) =
        2 ^ (a - 3 * q_c) * 3 ^ (b + 2 * q_c) - 7
  | 0, _, _, _, _ => by simp [cousinDiamond7Iter]
  | q_c + 1, a, b, ha, hb => by
    have ha5 : a ≥ 5 := by omega
    have hc5 := isDiamond4Cone5_of_pow2_pow3 a b ha5 hb
    have hnc8_0 : ¬ isDiamond7Cone8 (2 ^ a * 3 ^ b - 7) :=
      not_cone8_of_mod32_ne_21 _ (by have h := hc5.2.1; omega)
    let mid := 2 ^ (a - 2) * 3 ^ (b + 1) - 5
    have hmid_4 : mid % 4 = 3 := by
      dsimp [mid]
      have hp8 : 2 ^ (a - 2) = 8 * 2 ^ (a - 5) := by
        conv => lhs; rw [show a - 2 = 3 + (a - 5) by omega]; rw [Nat.pow_add]
      rw [hp8, Nat.mul_assoc 8]
      have hp_pos : 2 ^ (a - 5) * 3 ^ (b + 1) ≥ 1 :=
        Nat.mul_le_mul (pow2_pos_nat _) (pow3_pos_nat _)
      omega
    have hnc8_1 : ¬ isDiamond7Cone8 mid := not_cone8_of_mod4_eq_3 mid hmid_4
    have hd6_2 := cousin_diamond6_cone5_two_step_climb 1 a b (by omega) hb
    simp only [Nat.mul_one, cousinDiamond6Iter] at hd6_2
    have hd6_s1 : cousinDiamond6Step (2 ^ a * 3 ^ b - 7) = mid := by
      rw [cousinDiamond6Step_eq_d5_of_not_cone7 _
            (not_cone7_of_mod32_ne_21 _ (by have h := hc5.2.1; omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _
            (not_cone6_of_mod32_ne_13 _ (by have h := hc5.2.1; omega))]
      unfold cousinDiamond4Step; simp only [hc5, ite_true]
      dsimp [mid]
      have hp4 : 2 ^ a = 4 * 2 ^ (a - 2) := by
        conv => lhs; rw [show a = 2 + (a - 2) by omega]; rw [Nat.pow_add]
      have hprod_ge : 2 ^ (a - 2) * 3 ^ b ≥ 24 := by
        have h1 : 8 ≤ 2 ^ (a - 2) := by simpa using pow2_mono_nat (by omega : 3 ≤ a - 2)
        have h2 : 3 ≤ 3 ^ b := by
          rw [show b = 1 + (b - 1) by omega, Nat.pow_add, Nat.pow_one]
          have hp := pow3_pos_nat (b - 1); omega
        simpa using Nat.mul_le_mul h1 h2
      rw [hp4, Nat.mul_assoc 4 (2 ^ (a - 2)) (3 ^ b),
          Nat.pow_succ 3 b, ← Nat.mul_assoc (2 ^ (a - 2)) (3 ^ b) 3]; omega
    rw [hd6_s1] at hd6_2
    conv => lhs; rw [show 2 * (q_c + 1) = 2 + 2 * q_c by omega]
    rw [cousinDiamond7Iter_add 2 (2 * q_c)]
    have hi2 : cousinDiamond7Iter 2 (2 ^ a * 3 ^ b - 7) = 2 ^ (a - 3) * 3 ^ (b + 2) - 7 := by
      simp only [cousinDiamond7Iter,
        cousinDiamond7Step_eq_d6_of_not_cone8 _ hnc8_0, hd6_s1,
        cousinDiamond7Step_eq_d6_of_not_cone8 _ hnc8_1, hd6_2]
    rw [hi2, cousin_diamond7_cone5_two_step_climb q_c (a - 3) (b + 2) (by omega) (by omega),
        show a - 3 - 3 * q_c = a - 3 * (q_c + 1) by omega,
        show b + 2 + 2 * q_c = b + 2 * (q_c + 1) by omega]

theorem cousin_diamond7_a0_3_drain (b0 : Nat) (hb0 : b0 ≥ 3) :
    cousinDiamond7Step (8 * 3 ^ b0 - 7) = 12 * 3 ^ b0 - 10 ∧
    cousinDiamond7Step (12 * 3 ^ b0 - 10) = 4 * 3 ^ b0 - 4 ∧
    cousinDiamond7Step (4 * 3 ^ b0 - 4) = 4 * 3 ^ (b0 - 1) - 2 ∧
    cousinDiamond7Iter ((b0 - 1) / 2 + 7) (8 * 3 ^ b0 - 7) = 1 := by
  rcases cousin_diamond6_a0_3_drain b0 hb0 with ⟨hd6_s1, hd6_s2, hd6_s3, _⟩
  have hp3_ge27 : 3 ^ b0 ≥ 27 := by
    simpa using nat_pow_mono_exp_pos 3 3 b0 (by decide) hb0
  have hp3_b1_ge9 : 3 ^ (b0 - 1) ≥ 9 := by
    simpa using nat_pow_mono_exp_pos 3 2 (b0 - 1) (by decide) (by omega)
  have hnc8_8 : ¬ isDiamond7Cone8 (8 * 3 ^ b0 - 7) := by
    apply not_cone8_of_mod16_ne_5
    have ho := pow3_odd_nat_sec8 b0
    omega
  have hs1 : cousinDiamond7Step (8 * 3 ^ b0 - 7) = 12 * 3 ^ b0 - 10 := by
    rw [cousinDiamond7Step_eq_d6_of_not_cone8 _ hnc8_8]; exact hd6_s1
  have hs2 : cousinDiamond7Step (12 * 3 ^ b0 - 10) = 4 * 3 ^ b0 - 4 := by
    rw [cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega))]; exact hd6_s2
  have hs3 : cousinDiamond7Step (4 * 3 ^ b0 - 4) = 4 * 3 ^ (b0 - 1) - 2 := by
    rw [cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega))]; exact hd6_s3
  have hs4 : cousinDiamond7Step (4 * 3 ^ (b0 - 1) - 2) = 2 * 3 ^ (b0 - 1) - 1 := by
    rw [cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
        cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
        cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
    have hnc5 : ¬ isDiamond4Cone5 (4 * 3 ^ (b0 - 1) - 2) := by rintro ⟨_, h32, _, _⟩; omega
    rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
    have hp3_o := pow3_odd_nat_sec8 (b0 - 1)
    have h18 : 4 * 3 ^ (b0 - 1) = 36 * 3 ^ (b0 - 3) := by
      conv => lhs; rhs; rw [show b0 - 1 = 2 + (b0 - 3) by omega]
      rw [Nat.pow_add]; omega
    have hp := pow3_pos_nat (b0 - 3)
    rw [cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) (by omega)]
    omega
  refine ⟨hs1, hs2, hs3, ?_⟩
  let m := (b0 - 1) / 2
  have hm_pos : m ≥ 1 := by dsimp [m]; omega
  have hp9m_ge9 : 9 ^ m ≥ 9 := by
    rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]
    have hp := nat_pow_pos_of_pos 9 (by decide) (m - 1); omega
  have hp9m_m8 : 9 ^ m % 8 = 1 := pow9_mod8_eq_one_w5 m
  by_cases hpar : (b0 - 1) % 2 = 0
  · have hb1_2m : b0 - 1 = 2 * m := by dsimp [m]; omega
    have hu_eq : 2 * 3 ^ (b0 - 1) - 1 = 2 * 9 ^ m - 1 := by
      rw [hb1_2m, ← pow9_eq_pow3_double m]
    let zr := 2 * 9 ^ m - 1
    let yr := (3 * 9 ^ m - 1) / 2
    have hsz : cousinDiamond7Step zr = yr := by
      rw [cousinDiamond7Step_eq_d6_of_not_cone8 zr (not_cone8_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 zr (not_cone7_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 zr (not_cone6_of_mod16_ne_13 zr (by dsimp [zr]; omega))]
      have hnc5 : ¬ isDiamond4Cone5 zr := by rintro ⟨_, h32, _, _⟩; dsimp [zr] at h32; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 zr hnc5]
      have hc3 : core3 (zr + 1) = 2 := by
        rw [show zr + 1 = 2 * 9 ^ m by dsimp [zr]; omega,
            core3_mul2 (9 ^ m) (by omega), (pow9_eq_v3Pow_w5 m).2]
      rw [cousinDiamond3Step_of_core3_succ_two_w8 zr (by dsimp [zr]; omega) (by dsimp [zr]; omega) hc3]
      dsimp [zr, yr]; omega
    have hsy : cousinDiamond7Step yr = (9 ^ (m + 1) - 1) / 4 := by
      have hyr_m3 : yr % 3 = 1 := by
        have hm3 : 9 ^ m % 3 = 0 := by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
        dsimp [yr]; omega
      rw [cousinDiamond7Step_eq_d6_of_not_cone8 yr (not_cone8_of_mod3_ne_2 yr (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 yr (not_cone7_of_mod9_ne_8 yr (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 yr (not_cone6_of_mod9_ne_8 yr (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 yr := by rintro ⟨_, _, hm3, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 yr hnc5]
      by_cases hm1 : m = 1
      · have hyr13 : yr = 13 := by dsimp [yr]; rw [hm1]
        rw [hyr13, hm1]; decide
      · have hm_ge2 : m ≥ 2 := by omega
        have hc3_2 : core3 (2 * yr + 1) = 1 := by
          rw [show 2 * yr + 1 = 3 * 9 ^ m by dsimp [yr]; omega,
              core3_mul3 (9 ^ m) (by omega), (pow9_eq_v3Pow_w5 m).2]
        have hc3_1 : core3 (yr + 1) ≠ 2 := by
          rw [core3_not_div3 (yr + 1) (by omega)]; dsimp [yr]; omega
        have hnc4 : ¬ isDiamond3Cone4 yr := by
          rintro ⟨_, _, hc2⟩
          rcases eq_pow2_of_core2_eq_one (3 * yr + 5) (by dsimp [yr]; omega) hc2 with ⟨M0, hM0⟩
          have h9_eq : 9 ^ (m + 1) + 7 = 2 ^ (M0 + 1) := by
            have h2mul : 2 * (3 * yr + 5) = 9 ^ (m + 1) + 7 := by
              rw [Nat.pow_succ 9 m, Nat.mul_comm (9 ^ m) 9]; dsimp [yr]; omega
            rw [← h2mul, hM0, Nat.pow_succ 2 M0, Nat.mul_comm]
          exact pow9_succ_add_seven_ne_pow2 m (M0 + 1) hm_ge2 h9_eq
        rw [cousinDiamond3Step_odd_half_w8 yr (by dsimp [yr]; omega) hnc4 hc3_2 hc3_1]
        dsimp [yr]; rw [Nat.pow_succ 9 m]; omega
    change cousinDiamond7Iter (m + 7) (8 * 3 ^ b0 - 7) = 1
    rw [show m + 7 = 4 + 1 + 1 + m + 1 by omega,
        cousinDiamond7Iter_add (4 + 1 + 1 + m) 1,
        cousinDiamond7Iter_add (4 + 1 + 1) m,
        cousinDiamond7Iter_add (4 + 1) 1,
        cousinDiamond7Iter_add 4 1]
    have hi4 : cousinDiamond7Iter 4 (8 * 3 ^ b0 - 7) = zr := by
      simp only [cousinDiamond7Iter, hs1, hs2, hs3, hs4, hu_eq]; rfl
    rw [hi4]
    have hiz : cousinDiamond7Iter 1 zr = yr := hsz
    rw [hiz]
    have hiy : cousinDiamond7Iter 1 yr = (9 ^ (m + 1) - 1) / 4 := hsy
    rw [hiy, cousin_diamond7_even9_spine_drain m]
    decide
  · have hb1_2m1 : b0 - 1 = 2 * m + 1 := by dsimp [m]; omega
    have hu_eq : 2 * 3 ^ (b0 - 1) - 1 = 6 * 9 ^ m - 1 := by
      rw [hb1_2m1, Nat.pow_succ, ← pow9_eq_pow3_double m]; omega
    let ur := 6 * 9 ^ m - 1
    let wr := (9 ^ (m + 1) - 1) / 2
    have hsu : cousinDiamond7Step ur = wr := by
      have hur_m16 : ur % 16 = 5 := by
        let q := (9 ^ m - 1) / 8
        have hp9_eq : 9 ^ m = 8 * q + 1 := by dsimp [q]; omega
        dsimp [ur]; rw [hp9_eq]; omega
      rw [cousinDiamond7Step_eq_d6_of_not_cone8 ur (not_cone8_six_mul_pow9_sub1 m),
          cousinDiamond6Step_eq_d5_of_not_cone7 ur (not_cone7_six_mul_pow9_sub1 m),
          cousinDiamond5Step_eq_d4_of_not_cone6 ur (not_cone6_of_mod16_ne_13 ur (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 ur := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 ur hnc5]
      have hc3 : core3 (ur + 1) = 2 := by
        rw [show ur + 1 = 2 * (3 * 9 ^ m) by dsimp [ur]; omega,
            core3_mul2 (3 * 9 ^ m) (by omega),
            core3_mul3 (9 ^ m) (by omega), (pow9_eq_v3Pow_w5 m).2]
      rw [cousinDiamond3Step_of_core3_succ_two_w8 ur (by omega) (by dsimp [ur]; omega) hc3]
      dsimp [ur, wr]; rw [Nat.pow_succ 9 m]; omega
    have hsw : cousinDiamond7Step wr = (9 ^ (m + 1) - 1) / 4 := by
      let q := (9 ^ m - 1) / 8
      have hq_pos : q ≥ 1 := by dsimp [q]; omega
      have hp9_eq : 9 ^ m = 8 * q + 1 := by dsimp [q]; omega
      have hwr_eq : wr = 36 * q + 4 := by dsimp [wr]; rw [Nat.pow_succ 9 m, hp9_eq]; omega
      have hnext_eq : (9 ^ (m + 1) - 1) / 4 = 18 * q + 2 := by rw [Nat.pow_succ 9 m, hp9_eq]; omega
      rw [hwr_eq, hnext_eq,
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (36 * q + 4) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5,
          cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) (by omega)]
      omega
    change cousinDiamond7Iter (m + 7) (8 * 3 ^ b0 - 7) = 1
    rw [show m + 7 = 4 + 1 + 1 + m + 1 by omega,
        cousinDiamond7Iter_add (4 + 1 + 1 + m) 1,
        cousinDiamond7Iter_add (4 + 1 + 1) m,
        cousinDiamond7Iter_add (4 + 1) 1,
        cousinDiamond7Iter_add 4 1]
    have hi4 : cousinDiamond7Iter 4 (8 * 3 ^ b0 - 7) = ur := by
      simp only [cousinDiamond7Iter, hs1, hs2, hs3, hs4, hu_eq]; rfl
    rw [hi4]
    have hiu : cousinDiamond7Iter 1 ur = wr := hsu
    rw [hiu]
    have hiw : cousinDiamond7Iter 1 wr = (9 ^ (m + 1) - 1) / 4 := hsw
    rw [hiw, cousin_diamond7_even9_spine_drain m]
    decide

theorem cousin_diamond7_a0_2_and_4_drain (b0 : Nat) (hb0 : b0 ≥ 3) :
    cousinDiamond7Iter (b0 + 3) (4 * 3 ^ b0 - 7) = 1 ∧
    cousinDiamond7Iter ((b0 - 1) / 2 + 8) (16 * 3 ^ b0 - 7) = 1 := by
  have hp3_ge27 : 3 ^ b0 ≥ 27 := by
    simpa using nat_pow_mono_exp_pos 3 3 b0 (by decide) hb0
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
  have hnc8_4 : ¬ isDiamond7Cone8 (4 * 3 ^ b0 - 7) := by
    apply not_cone8_of_mod32_ne_21
    have hdm := (Nat.div_add_mod (3 ^ b0) 8).symm
    rcases h3b0_m8 with h1 | h3 <;> omega
  have hnc8_16 : ¬ isDiamond7Cone8 (16 * 3 ^ b0 - 7) := by
    apply not_cone8_of_mod32_ne_21
    have ho := pow3_odd_nat_sec8 b0
    omega
  have hnc7_c : ∀ c : Nat, c ≥ 1 -> ¬ isDiamond6Cone7 (c * 3 ^ b0 - 7) := by
    intro c hc1
    apply not_cone7_of_mod9_ne_8
    have hm : c * 3 ^ b0 ≥ 27 := by simpa using Nat.mul_le_mul hc1 hp3_ge27
    have hm9 : (c * 3 ^ b0) % 9 = 0 := by rw [Nat.mul_mod, h3b0_m9, Nat.mul_zero, Nat.zero_mod]
    omega
  have hnc6_c : ∀ c : Nat, c ≥ 1 -> ¬ isDiamond5Cone6 (c * 3 ^ b0 - 7) := by
    intro c hc1
    apply not_cone6_of_mod9_ne_8
    have hm : c * 3 ^ b0 ≥ 27 := by simpa using Nat.mul_le_mul hc1 hp3_ge27
    have hm9 : (c * 3 ^ b0) % 9 = 0 := by rw [Nat.mul_mod, h3b0_m9, Nat.mul_zero, Nat.zero_mod]
    omega
  refine ⟨?_, ?_⟩
  · have hs1 : cousinDiamond7Step (4 * 3 ^ b0 - 7) = 6 * 3 ^ b0 - 10 := by
      rw [cousinDiamond7Step_eq_d6_of_not_cone8 _ hnc8_4,
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (hnc7_c 4 (by decide)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (hnc6_c 4 (by decide))]
      exact cousin_diamond4_exit_step_general_odd 4 b0 (Or.inl rfl) hb0
    have hs2 : cousinDiamond7Step (6 * 3 ^ b0 - 10) = 2 * 3 ^ b0 - 4 := by
      rw [cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (6 * 3 ^ b0 - 10) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 6 * 3 ^ b0 = 18 * 3 ^ (b0 - 1) := by rw [h3b0_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    have hs3 : cousinDiamond7Step (2 * 3 ^ b0 - 4) = 2 * 3 ^ (b0 - 1) - 2 := by
      rw [cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (2 * 3 ^ b0 - 4) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 2 * 3 ^ b0 = 18 * 3 ^ (b0 - 2) := by rw [h3b0_sp, h3b1_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    have hs4 : cousinDiamond7Step (2 * 3 ^ (b0 - 1) - 2) = 3 ^ (b0 - 1) - 1 := by
      rw [cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
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
        cousinDiamond7Iter_add (4 + (b0 - 2)) 1,
        cousinDiamond7Iter_add 4 (b0 - 2)]
    have hi4 : cousinDiamond7Iter 4 (4 * 3 ^ b0 - 7) = 3 ^ ((b0 - 2) + 1) - 1 := by
      simp only [cousinDiamond7Iter, hs1, hs2, hs3, hs4]
      rw [show b0 - 1 = (b0 - 2) + 1 by omega]
    rw [hi4, cousin_diamond7_pow3_sub1_drain (b0 - 2)]
    decide
  · rcases cousin_diamond7_a0_3_drain b0 hb0 with ⟨ha3_s1, ha3_s2, ha3_s3, ha3⟩
    have hs1 : cousinDiamond7Step (16 * 3 ^ b0 - 7) = 24 * 3 ^ b0 - 10 := by
      rw [cousinDiamond7Step_eq_d6_of_not_cone8 _ hnc8_16,
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (hnc7_c 16 (by decide)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (hnc6_c 16 (by decide))]
      exact cousin_diamond4_exit_step_general_odd 16 b0 (Or.inr (Or.inr rfl)) hb0
    have hs2 : cousinDiamond7Step (24 * 3 ^ b0 - 10) = 8 * 3 ^ b0 - 4 := by
      rw [cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (24 * 3 ^ b0 - 10) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 24 * 3 ^ b0 = 18 * (4 * 3 ^ (b0 - 1)) := by rw [h3b0_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    have hs3 : cousinDiamond7Step (8 * 3 ^ b0 - 4) = 8 * 3 ^ (b0 - 1) - 2 := by
      rw [cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (8 * 3 ^ b0 - 4) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 8 * 3 ^ b0 = 18 * (4 * 3 ^ (b0 - 2)) := by rw [h3b0_sp, h3b1_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    have hs4 : cousinDiamond7Step (8 * 3 ^ (b0 - 1) - 2) = 4 * 3 ^ (b0 - 1) - 2 := by
      rw [cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
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
        cousinDiamond7Iter_add 3 ((b0 - 1) / 2 + 4)] at ha3
    have hi3 : cousinDiamond7Iter 3 (8 * 3 ^ b0 - 7) = 4 * 3 ^ (b0 - 1) - 2 := by
      simp only [cousinDiamond7Iter, ha3_s1, ha3_s2, ha3_s3]
    rw [hi3] at ha3
    rw [show (b0 - 1) / 2 + 8 = 4 + ((b0 - 1) / 2 + 4) by omega,
        cousinDiamond7Iter_add 4 ((b0 - 1) / 2 + 4)]
    have hi4 : cousinDiamond7Iter 4 (16 * 3 ^ b0 - 7) = 4 * 3 ^ (b0 - 1) - 2 := by
      simp only [cousinDiamond7Iter, hs1, hs2, hs3, hs4]
    rw [hi4]
    exact ha3

theorem cousin_diamond7_cone4_return_aux (x : Nat) (hc4 : isDiamond3Cone4 x) :
    ∃ k : Nat, k ≤ cousinDiamond2Phi x ∧ cousinDiamond7Iter k x = 1 := by
  rcases cousin_diamond3_cone4_reaches_one_exact x hc4 with ⟨r, hr_ge3, hE, _, hphi_ge⟩
  refine ⟨3 * r + 4, hphi_ge, ?_⟩
  have hnc8_x : ¬ isDiamond7Cone8 x := not_cone8_of_mod8_ne_5 x (by have h8 := hc4.2.1; omega)
  have hnc7_x : ¬ isDiamond6Cone7 x := not_cone7_of_mod8_ne_5 x (by have h8 := hc4.2.1; omega)
  have hnc6_x : ¬ isDiamond5Cone6 x := by rintro ⟨_, h256, _, _⟩; have h8 := hc4.2.1; omega
  have hx_odd : x % 2 = 1 := by have h8 := hc4.2.1; omega
  have hs1 : cousinDiamond7Step x = 2 ^ (2 * r + 1) - 1 := by
    rw [cousinDiamond7Step_eq_d6_of_not_cone8 x hnc8_x,
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
  have hglide : cousinDiamond7Iter (2 * r) (2 ^ (2 * r + 1) - 1) = zr := by
    have hf := cousin_diamond7_mersenne_scaled (2 * r) (2 * r + 1) 1 (by omega) (by decide)
    simp only [Nat.mul_one, show 2 * r + 1 - 2 * r = 1 by omega, Nat.pow_one] at hf
    rw [hf, ← pow9_eq_pow3_double r, Nat.mul_comm]
  have hp9_ge729 : 9 ^ r ≥ 729 := by
    simpa using nat_pow_mono_exp_pos 9 3 r (by decide) hr_ge3
  have hp9_m8 : 9 ^ r % 8 = 1 := pow9_mod8_eq_one_w5 r
  have hsz : cousinDiamond7Step zr = yr := by
    rw [cousinDiamond7Step_eq_d6_of_not_cone8 zr (not_cone8_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
        cousinDiamond6Step_eq_d5_of_not_cone7 zr (not_cone7_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
        cousinDiamond5Step_eq_d4_of_not_cone6 zr (not_cone6_of_mod16_ne_13 zr (by dsimp [zr]; omega))]
    have hnc5 : ¬ isDiamond4Cone5 zr := by rintro ⟨_, h32, _, _⟩; dsimp [zr] at h32; omega
    rw [cousinDiamond4Step_eq_d3_of_not_cone5 zr hnc5]
    have hc3 : core3 (zr + 1) = 2 := by
      rw [show zr + 1 = 2 * 9 ^ r by dsimp [zr]; omega,
          core3_mul2 (9 ^ r) (by omega), (pow9_eq_v3Pow_w5 r).2]
    rw [cousinDiamond3Step_of_core3_succ_two_w8 zr (by dsimp [zr]; omega) (by dsimp [zr]; omega) hc3]
    dsimp [zr, yr]; omega
  have hsy : cousinDiamond7Step yr = (9 ^ (r + 1) - 1) / 4 := by
    have hyr_m3 : yr % 3 = 1 := by
      have hm3 : 9 ^ r % 3 = 0 := by rw [show r = (r - 1) + 1 by omega, Nat.pow_succ]; omega
      dsimp [yr]; omega
    rw [cousinDiamond7Step_eq_d6_of_not_cone8 yr (not_cone8_of_mod3_ne_2 yr (by omega)),
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
      cousinDiamond7Iter_add (1 + 2 * r + 1 + 1 + r) 1,
      cousinDiamond7Iter_add (1 + 2 * r + 1 + 1) r,
      cousinDiamond7Iter_add (1 + 2 * r + 1) 1,
      cousinDiamond7Iter_add (1 + 2 * r) 1,
      cousinDiamond7Iter_add 1 (2 * r)]
  have hi1 : cousinDiamond7Iter 1 x = 2 ^ (2 * r + 1) - 1 := hs1
  rw [hi1, hglide]
  have hiz : cousinDiamond7Iter 1 zr = yr := hsz
  rw [hiz]
  have hiy : cousinDiamond7Iter 1 yr = (9 ^ (r + 1) - 1) / 4 := hsy
  rw [hiy, cousin_diamond7_even9_spine_drain r]
  decide

theorem cousin_diamond7_cone5_return_aux (x : Nat) (hc5 : isDiamond4Cone5 x) :
    ∃ (a b k : Nat),
      a ≥ 5 ∧ b ≥ 1 ∧ x + 7 = 2 ^ a * 3 ^ b ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond7Iter k x = 1 := by
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
  have hclimb := cousin_diamond7_cone5_two_step_climb q_c a b (by dsimp [q_c]; omega) hb1
  rw [← hx_eq] at hclimb
  change cousinDiamond7Iter (2 * q_c) x = 2 ^ a0 * 3 ^ b0 - 7 at hclimb
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
  have hd_3 := (cousin_diamond7_a0_3_drain b0 hb0_ge3).2.2.2
  rcases cousin_diamond7_a0_2_and_4_drain b0 hb0_ge3 with ⟨hd_2, hd_4⟩
  rcases ha0_234 with ha2 | ha3 | ha4
  · have hkx := hbound_x (b0 + 3) (by omega)
    refine ⟨a, b, 2 * q_c + (b0 + 3), ha5, hb1, hmul.symm, hkx,
      Nat.le_trans (by omega : 2 * q_c + (b0 + 3) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond7Iter_add (2 * q_c) (b0 + 3) x, hclimb, ha2]; exact hd_2
  · have hkx := hbound_x ((b0 - 1) / 2 + 7) (by omega)
    refine ⟨a, b, 2 * q_c + ((b0 - 1) / 2 + 7), ha5, hb1, hmul.symm, hkx,
      Nat.le_trans (by omega : 2 * q_c + ((b0 - 1) / 2 + 7) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond7Iter_add (2 * q_c) ((b0 - 1) / 2 + 7) x, hclimb, ha3]; exact hd_3
  · have hkx := hbound_x ((b0 - 1) / 2 + 8) (by omega)
    refine ⟨a, b, 2 * q_c + ((b0 - 1) / 2 + 8), ha5, hb1, hmul.symm, hkx,
      Nat.le_trans (by omega : 2 * q_c + ((b0 - 1) / 2 + 8) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond7Iter_add (2 * q_c) ((b0 - 1) / 2 + 8) x, hclimb, ha4]; exact hd_4

theorem cousin_diamond7_cone6_return_aux (x : Nat) (hc6 : isDiamond5Cone6 x) :
    ∃ (e f k : Nat),
      e ≥ 8 ∧ f ≥ 2 ∧ x + 19 = 2 ^ e * 3 ^ f ∧
      cousinDiamond7Step x = 2 ^ (e - 3) * 3 ^ (f + 1) - 7 ∧
      isDiamond4Cone5 (cousinDiamond7Step x) ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond7Iter k x = 1 := by
  have hnc8_x : ¬ isDiamond7Cone8 x :=
    not_cone8_of_mod256_ne_213 x (by rw [hc6.2.1]; decide)
  have hnc7_x : ¬ isDiamond6Cone7 x :=
    not_cone7_of_mod256_ne_213 x (by rw [hc6.2.1]; decide)
  have hx_ge : x ≥ 2285 := hc6.1
  rcases (cousin_diamond6_cones4567_exact_return.2.2.1 x hc6) with
    ⟨e, f, _, he8, hf2, hmul, hd6_x, _, _, _, _⟩
  let y := 2 ^ (e - 3) * 3 ^ (f + 1) - 7
  have hstep_x : cousinDiamond7Step x = y := by
    rw [cousinDiamond7Step_eq_d6_of_not_cone8 x hnc8_x]; exact hd6_x
  have hy_step : y = (3 * x + 1) / 8 :=
    hd6_x.symm.trans (by rw [cousinDiamond6Step_eq_d5_of_not_cone7 x hnc7_x]; unfold cousinDiamond5Step; simp [hc6])
  clear hc6 hnc8_x hnc7_x hd6_x
  have hc5_y : isDiamond4Cone5 y :=
    isDiamond4Cone5_of_pow2_pow3 (e - 3) (f + 1) (by omega) (by omega)
  rcases cousin_diamond7_cone5_return_aux y hc5_y with ⟨_, _, ky, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hdiv : y * 8 ≤ 3 * x + 1 := by rw [hy_step]; exact Nat.div_mul_le_self (3 * x + 1) 8
    clear hy_step hmul hstep_x hc5_y hky_1
    omega
  have h1ky_x : 1 + ky ≤ x := by clear hy_step hmul hstep_x hc5_y hky_1; omega
  have h1ky_phi : 1 + ky ≤ cousinDiamond2Phi x :=
    Nat.le_trans (by clear hy_step hmul hstep_x hc5_y hky_1; omega : 1 + ky ≤ x + 1) (cousinDiamond2Phi_ge_succ x)
  refine ⟨e, f, 1 + ky, he8, hf2, hmul, hstep_x, ?_, h1ky_x, h1ky_phi, ?_⟩
  · rw [hstep_x]; exact hc5_y
  · rw [cousinDiamond7Iter_add 1 ky x]
    have hi1 : cousinDiamond7Iter 1 x = y := hstep_x
    rw [hi1]; exact hky_1

theorem cousin_diamond7_cone7_return_aux (x : Nat) (hc7 : isDiamond6Cone7 x) :
    ∃ (g h k : Nat),
      g ≥ 15 ∧ h ≥ 2 ∧ x + 811 = 2 ^ g * 3 ^ h ∧
      cousinDiamond7Step x = 2 ^ (g - 7) * 3 ^ (h + 1) - 19 ∧
      isDiamond5Cone6 (cousinDiamond7Step x) ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond7Iter k x = 1 := by
  have hnc8_x : ¬ isDiamond7Cone8 x :=
    not_cone8_of_mod32768_ne_30933 x (by rw [hc7.2.1]; decide)
  have hx_ge : x ≥ 294101 := hc7.1
  rcases (cousin_diamond6_cones4567_exact_return.2.2.2 x hc7) with
    ⟨g, h, _, hg15, hh2, hmul, hd6_x, _, _, _, _⟩
  let y := 2 ^ (g - 7) * 3 ^ (h + 1) - 19
  have hstep_x : cousinDiamond7Step x = y := by
    rw [cousinDiamond7Step_eq_d6_of_not_cone8 x hnc8_x]; exact hd6_x
  have hy_step : y = (3 * x + 1) / 128 :=
    hd6_x.symm.trans (by unfold cousinDiamond6Step; simp [hc7])
  clear hc7 hnc8_x hd6_x
  have hc6_y : isDiamond5Cone6 y :=
    isDiamond5Cone6_of_pow2_pow3 (g - 7) (h + 1) (by omega) (by omega)
  rcases cousin_diamond7_cone6_return_aux y hc6_y with ⟨_, _, ky, _, _, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hdiv : y * 128 ≤ 3 * x + 1 := by rw [hy_step]; exact Nat.div_mul_le_self (3 * x + 1) 128
    clear hy_step hmul hstep_x hc6_y hky_1
    omega
  have h1ky_x : 1 + ky ≤ x := by clear hy_step hmul hstep_x hc6_y hky_1; omega
  have h1ky_phi : 1 + ky ≤ cousinDiamond2Phi x :=
    Nat.le_trans (by clear hy_step hmul hstep_x hc6_y hky_1; omega : 1 + ky ≤ x + 1) (cousinDiamond2Phi_ge_succ x)
  refine ⟨g, h, 1 + ky, hg15, hh2, hmul, hstep_x, ?_, h1ky_x, h1ky_phi, ?_⟩
  · rw [hstep_x]; exact hc6_y
  · rw [cousinDiamond7Iter_add 1 ky x]
    have hi1 : cousinDiamond7Iter 1 x = y := hstep_x
    rw [hi1]; exact hky_1

/--
  Theorem W10.3d (`cousin_diamond7_cones45678_exact_return`, `zero custom axioms`):
  Exact 5-Tier `ω^5` Multi-Block Return Across Cones 4, 5, 6, 7, AND 8 of `T_diamond7`:
  1–4. Every `x` in Cone 4, 5, 6, or 7 reaches `1` in `k ≤ cousinDiamond2Phi x` steps!
  5. Every `x` in Cone 8 (`isDiamond7Cone8 x`) has `x + 34603 = 2 ^ u * 3 ^ v` (`u ≥ 22, v ≥ 1`),
     steps in 1 genuine `v_2(3x + 1) = 7` jump `(3 * x + 1) / 128` directly into the Cone-7 state
     `y = 2 ^ (u - 7) * 3 ^ (v + 1) - 811`, and reaches `1` in `1 + k_y ≤ x` (`≤ cousinDiamond2Phi x`) steps!
-/
theorem cousin_diamond7_cones45678_exact_return :
    (∀ x : Nat, isDiamond3Cone4 x ->
      ∃ k : Nat, k ≤ cousinDiamond2Phi x ∧ cousinDiamond7Iter k x = 1) ∧
    (∀ x : Nat, isDiamond4Cone5 x ->
      ∃ (a b k : Nat),
        a ≥ 5 ∧ b ≥ 1 ∧ x + 7 = 2 ^ a * 3 ^ b ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond7Iter k x = 1) ∧
    (∀ x : Nat, isDiamond5Cone6 x ->
      ∃ (e f k : Nat),
        e ≥ 8 ∧ f ≥ 2 ∧ x + 19 = 2 ^ e * 3 ^ f ∧
        cousinDiamond7Step x = 2 ^ (e - 3) * 3 ^ (f + 1) - 7 ∧
        isDiamond4Cone5 (cousinDiamond7Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond7Iter k x = 1) ∧
    (∀ x : Nat, isDiamond6Cone7 x ->
      ∃ (g h k : Nat),
        g ≥ 15 ∧ h ≥ 2 ∧ x + 811 = 2 ^ g * 3 ^ h ∧
        cousinDiamond7Step x = 2 ^ (g - 7) * 3 ^ (h + 1) - 19 ∧
        isDiamond5Cone6 (cousinDiamond7Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond7Iter k x = 1) ∧
    (∀ x : Nat, isDiamond7Cone8 x ->
      ∃ (u v k : Nat),
        u ≥ 22 ∧ v ≥ 1 ∧ x + 34603 = 2 ^ u * 3 ^ v ∧
        cousinDiamond7Step x = 2 ^ (u - 7) * 3 ^ (v + 1) - 811 ∧
        isDiamond6Cone7 (cousinDiamond7Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond7Iter k x = 1) := by
  refine ⟨cousin_diamond7_cone4_return_aux,
          cousin_diamond7_cone5_return_aux,
          cousin_diamond7_cone6_return_aux,
          cousin_diamond7_cone7_return_aux, ?_⟩
  intro x hc8
  have hraw_step : cousinDiamond7Step x = (3 * x + 1) / 128 := by
    unfold cousinDiamond7Step; simp only [hc8, ite_true]
  rcases hc8 with ⟨hx_ge, hx4m, hx3, hg1⟩
  have hdvd4m : 4194304 ∣ (x + 34603) :=
    Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, hx4m])
  clear hx4m
  rcases (⟨34603 + x, rfl⟩ : ∃ N : Nat, N = 34603 + x) with ⟨N, hN_def⟩
  rw [← hN_def] at hg1
  have hN_pos : N > 0 := by clear hraw_step hdvd4m hx3 hg1; omega
  rcases decomp_2_3_exact N hN_pos with ⟨_, _, _, _, _, hmul⟩
  rw [hg1, Nat.mul_one] at hmul
  rcases eq_pow2_of_v2Pow_aux N N hN_pos (Nat.le_refl _) with ⟨u, hu⟩
  rcases eq_pow3_of_v3Pow_aux N N hN_pos (Nat.le_refl _) with ⟨v, hv⟩
  rw [hu, hv] at hmul
  have hmul_comm : x + 34603 = 2 ^ u * 3 ^ v := by
    rw [Nat.add_comm x 34603, ← hN_def, ← hmul]
  clear hg1 hu hv hN_def hmul hN_pos
  have hu22 : u ≥ 22 := by
    by_cases hlt : u < 22
    · exfalso
      have h4m_sp : 4194304 = 2 ^ (u + 1) * 2 ^ (21 - u) := by
        have hsum22 : u + 1 + (21 - u) = 22 := by clear hraw_step hx_ge hx3 hdvd4m hmul_comm; omega
        rw [← Nat.pow_add 2 (u + 1) (21 - u), hsum22]
      rcases hdvd4m with ⟨q, hq⟩
      rw [hmul_comm, h4m_sp, Nat.mul_assoc (2 ^ (u + 1)),
          Nat.pow_succ 2 u, Nat.mul_assoc (2 ^ u) 2] at hq
      have h3v_ev : 3 ^ v = 2 * (2 ^ (21 - u) * q) :=
        nat_mul_left_cancel_pos (2 ^ u) _ _ (pow2_pos_nat u) hq
      have ho := pow3_odd_nat_sec8 v
      rw [h3v_ev, Nat.mul_mod_right] at ho
      cases ho
    · clear hraw_step hx_ge hx3 hdvd4m hmul_comm; omega
  clear hdvd4m
  have hv1 : v ≥ 1 := by
    cases v with
    | zero =>
      rw [Nat.pow_zero, Nat.mul_one] at hmul_comm
      exact False.elim (pow2_mod3_nonzero_w5 u (by rw [← hmul_comm, Nat.add_mod, hx3]))
    | succ _ => clear hraw_step hx_ge hx3 hmul_comm hu22; omega
  clear hx3
  let y := 2 ^ (u - 7) * 3 ^ (v + 1) - 811
  have hstep_x : cousinDiamond7Step x = y := by
    rw [hraw_step]
    dsimp [y]
    have hp128 : 2 ^ u = 128 * 2 ^ (u - 7) := by
      have hu_sp : u = 7 + (u - 7) := by clear hraw_step hx_ge hmul_comm hv1; omega
      conv => lhs; rw [hu_sp]; rw [Nat.pow_add]
    have hprod_pos : 2 ^ (u - 7) * 3 ^ v ≥ 32768 * 3 := by
      have h1 : 32768 ≤ 2 ^ (u - 7) := by
        have hc : (2 : Nat) ^ 15 = 32768 := by decide
        have h15 : 15 ≤ u - 7 := by clear hraw_step hx_ge hmul_comm hv1 hp128; omega
        rw [← hc]; exact pow2_mono_nat h15
      have h2 : 3 ≤ 3 ^ v := by simpa using nat_pow_mono_exp_pos 3 1 v (by decide) hv1
      simpa using Nat.mul_le_mul h1 h2
    have h3_eq : 2 ^ (u - 7) * 3 ^ (v + 1) = 3 * (2 ^ (u - 7) * 3 ^ v) := by
      rw [Nat.pow_succ 3 v, ← Nat.mul_assoc, Nat.mul_comm _ 3]
    rw [h3_eq]
    have hx128 : x + 34603 = 128 * (2 ^ (u - 7) * 3 ^ v) := by
      rw [hmul_comm, hp128, Nat.mul_assoc]
    have h3x1 : 3 * x + 1 = (3 * (2 ^ (u - 7) * 3 ^ v) - 811) * 128 := by
      clear hraw_step hu22 hv1 hp128 h3_eq hmul_comm
      generalize 2 ^ (u - 7) * 3 ^ v = A at hprod_pos hx128 ⊢
      omega
    rw [h3x1]
    exact Nat.mul_div_left _ (by decide : 0 < 128)
  have hc7_y : isDiamond6Cone7 y :=
    isDiamond6Cone7_of_pow2_pow3 (u - 7) (v + 1)
      (by clear hraw_step hx_ge hmul_comm hstep_x; omega)
      (by clear hraw_step hx_ge hmul_comm hstep_x; omega)
  rcases cousin_diamond7_cone7_return_aux y hc7_y with ⟨_, _, ky, _, _, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hstep_eq : y = (3 * x + 1) / 128 := hstep_x.symm.trans hraw_step
    have hdiv : y * 128 ≤ 3 * x + 1 := by rw [hstep_eq]; exact Nat.div_mul_le_self (3 * x + 1) 128
    clear hraw_step hmul_comm hstep_x hc7_y hky_1 hstep_eq
    omega
  have h1ky_x : 1 + ky ≤ x := by clear hraw_step hmul_comm hstep_x hc7_y hky_1; omega
  have h1ky_phi : 1 + ky ≤ cousinDiamond2Phi x :=
    Nat.le_trans (by clear hraw_step hmul_comm hstep_x hc7_y hky_1; omega : 1 + ky ≤ x + 1)
      (cousinDiamond2Phi_ge_succ x)
  refine ⟨u, v, 1 + ky, hu22, hv1, hmul_comm, hstep_x, ?_, h1ky_x, h1ky_phi, ?_⟩
  · rw [hstep_x]; exact hc7_y
  · rw [cousinDiamond7Iter_add 1 ky x]
    have hi1 : cousinDiamond7Iter 1 x = y := hstep_x
    rw [hi1]; exact hky_1

theorem cousin_diamond7_reaches_one_within_phi :
    ∀ (B x : Nat), x > 0 -> cousinDiamond2Phi x ≤ B ->
      ∃ k : Nat, k ≤ B ∧ cousinDiamond7Iter k x = 1
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
        · rcases cousin_diamond7_cones45678_exact_return.1 x hc4 with ⟨k, hle_phi, hk1⟩
          exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
        · by_cases hc5 : isDiamond4Cone5 x
          · rcases cousin_diamond7_cones45678_exact_return.2.1 x hc5 with
              ⟨_, _, k, _, _, _, _, hle_phi, hk1⟩
            exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
          · by_cases hc6 : isDiamond5Cone6 x
            · rcases cousin_diamond7_cones45678_exact_return.2.2.1 x hc6 with
                ⟨_, _, k, _, _, _, _, _, _, hle_phi, hk1⟩
              exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
            · by_cases hc7 : isDiamond6Cone7 x
              · rcases cousin_diamond7_cones45678_exact_return.2.2.2.1 x hc7 with
                  ⟨_, _, k, _, _, _, _, _, _, hle_phi, hk1⟩
                exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
              · by_cases hc8 : isDiamond7Cone8 x
                · rcases cousin_diamond7_cones45678_exact_return.2.2.2.2 x hc8 with
                    ⟨_, _, k, _, _, _, _, _, _, hle_phi, hk1⟩
                  exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
                · have hdesc := cousin_diamond7_outside_cones45678_strict_descent x
                    (by omega) hc4 hc5 hc6 hc7 hc8
                  have hpos := cousinDiamond7Step_pos x hx
                  rcases cousin_diamond7_reaches_one_within_phi B (cousinDiamond7Step x) hpos (by omega) with
                    ⟨k, hk_le, hk_eq⟩
                  exact ⟨k + 1, by omega, hk_eq⟩

/--
  Theorem W10.3e (`cousin_diamond7_global_convergence`, `zero custom axioms`):
  Unconditional Global Convergence & Degree-5 Polynomial Stopping Bound for `T_diamond7`:
  For EVERY `x > 0`, `cousinDiamond7Iter` reaches `1` within `k ≤ (x + 1) ^ 3 + (x + 1) ^ 5` steps!
-/
theorem cousin_diamond7_global_convergence (x : Nat) (hx : x > 0) :
    ∃ k : Nat, k ≤ (x + 1) ^ 3 + (x + 1) ^ 5 ∧ cousinDiamond7Iter k x = 1 := by
  rcases cousin_diamond7_reaches_one_within_phi (cousinDiamond2Phi x) x hx (Nat.le_refl _) with
    ⟨k, hk_phi, hk1⟩
  exact ⟨k, Nat.le_trans hk_phi (cousinDiamond2Phi_upper_poly_bound x), hk1⟩

theorem exists_non_desc_along_diamond7_iter :
    ∀ (terms : List LaurentTerm) (A0 B0 C0 N z : Nat),
      N ≥ 1 ->
      (∀ i : Nat, i < N ->
        cousinDiamond7Iter i z ≥ 3 ∧
        (cousinDiamond7Iter i z) % 2 = 1 ∧
        cousinDiamond7Step (cousinDiamond7Iter i z) ≥ 3) ->
      ¬ laurentDescProp terms A0 B0 C0 z (cousinDiamond7Iter N z) ->
      ∃ x : Nat,
        x ≥ 3 ∧ x % 2 = 1 ∧ cousinDiamond7Step x ≥ 3 ∧
        ¬ laurentDescProp terms A0 B0 C0 x (cousinDiamond7Step x)
  | _, _, _, _, 0, _, hN, _, _ => by omega
  | terms, A0, B0, C0, 1, z, _, hall, hnd => by
    rcases hall 0 (by decide) with ⟨hz3, hzo, hsz3⟩
    exact ⟨z, hz3, hzo, hsz3, hnd⟩
  | terms, A0, B0, C0, m + 2, z, _, hall, hnd => by
    if h0 : laurentDescProp terms A0 B0 C0 z (cousinDiamond7Step z) then
      have hnd_next : ¬ laurentDescProp terms A0 B0 C0 (cousinDiamond7Step z)
          (cousinDiamond7Iter (m + 1) (cousinDiamond7Step z)) :=
        fun hrest => hnd (laurentDescProp_trans terms A0 B0 C0 z (cousinDiamond7Step z) _ h0 hrest)
      exact exists_non_desc_along_diamond7_iter terms A0 B0 C0 (m + 1) (cousinDiamond7Step z)
        (by omega) (fun i hi => hall (i + 1) (by omega)) hnd_next
    else
      rcases hall 0 (by omega) with ⟨hz3, hzo, hsz3⟩
      exact ⟨z, hz3, hzo, hsz3, h0⟩

/--
  Theorem W10.3f (`cousin_diamond7_r_block_spiral_climb_and_laurent_impossibility`, `zero custom axioms`):
  1. Cone-8 -> Cone-7 -> Cone-6 -> Cone-5 5-Tier Cascade & Unbounded `r`-Block Spiral Climb (`∀ r ≥ 1`):
     `12548309 -> 294101 -> 6893 -> 2585` AND
     `cousinDiamond7Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5` for ALL `j ≤ r`!
  2. Universal `∀ L ≥ 1` Multi-Term Laurent Valuation Impossibility on `cousinDiamond7Step`!
-/
theorem cousin_diamond7_r_block_spiral_climb_and_laurent_impossibility :
    cousinDiamond7Step 12548309 = 294101 ∧
    cousinDiamond7Step 294101 = 6893 ∧
    cousinDiamond7Step 6893 = 2585 ∧
    (∀ (r j : Nat), r ≥ 1 -> j ≤ r ->
      cousinDiamond7Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5) ∧
    (∀ (terms : List LaurentTerm) (A0 B0 C0 : Nat),
      (∃ t ∈ terms, t.coeff > 0) ->
      ∃ x : Nat,
        x ≥ 3 ∧ x % 2 = 1 ∧ cousinDiamond7Step x ≥ 3 ∧
        ¬ (evalLaurentSumNum terms (cousinDiamond7Step x) * laurentValDen A0 B0 C0 x <
            evalLaurentSumNum terms x * laurentValDen A0 B0 C0 (cousinDiamond7Step x))) := by
  have hspiral : ∀ (r j : Nat), r ≥ 1 -> j ≤ r ->
      cousinDiamond7Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5 := by
    intro r j hr hj
    cases j with
    | zero => simp [cousinDiamond7Iter]
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
      have hs_first : cousinDiamond7Step x0 = 2 ^ (4 * r + 1) * 3 ^ 1 - 7 := by
        rw [cousinDiamond7Step_eq_d6_of_not_cone8 x0 (not_cone8_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond6Step_eq_d5_of_not_cone7 x0 (not_cone7_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond5Step_eq_d4_of_not_cone6 x0 (not_cone6_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond4Step_mod4_eq_3 x0 hx0_m4]
        dsimp [x0]
        rw [hx0_pow, show 4 * r + 2 = (4 * r + 1) + 1 by omega, Nat.pow_succ 2 (4 * r + 1)]
        have hp := pow2_pos_nat (4 * r + 1); omega
      have hclimb := cousin_diamond7_cone5_two_step_climb j' (4 * r + 1) 1 (by omega) (by decide)
      let y_end := 2 ^ (4 * r + 1 - 3 * j') * 3 ^ (1 + 2 * j') - 7
      have hy_c5 : isDiamond4Cone5 y_end :=
        isDiamond4Cone5_of_pow2_pow3 (4 * r + 1 - 3 * j') (1 + 2 * j') (by omega) (by omega)
      have hy_nc8 : ¬ isDiamond7Cone8 y_end :=
        not_cone8_of_mod32_ne_21 y_end (by have h := hy_c5.2.1; omega)
      have hy_nc7 : ¬ isDiamond6Cone7 y_end :=
        not_cone7_of_mod32_ne_21 y_end (by have h := hy_c5.2.1; omega)
      have hy_nc6 : ¬ isDiamond5Cone6 y_end :=
        not_cone6_of_mod32_ne_13 y_end (by have h := hy_c5.2.1; omega)
      have hs_last : cousinDiamond7Step y_end = 4 * 16 ^ (r - (j' + 1)) * 18 ^ (j' + 1) - 5 := by
        rw [cousinDiamond7Step_eq_d6_of_not_cone8 y_end hy_nc8,
            cousinDiamond6Step_eq_d5_of_not_cone7 y_end hy_nc7,
            cousinDiamond5Step_eq_d4_of_not_cone6 y_end hy_nc6]
        unfold cousinDiamond4Step; simp only [hy_c5, ite_true]
        dsimp [y_end]
        have ha_sp : 4 * r + 1 - 3 * j' = 2 + (4 * (r - (j' + 1)) + (j' + 1) + 2) := by omega
        have hp2_sp : 2 ^ (4 * r + 1 - 3 * j') = 4 * (4 * 2 ^ (4 * (r - (j' + 1))) * 2 ^ (j' + 1)) := by
          rw [ha_sp, Nat.pow_add 2 2, Nat.pow_add 2 (4 * (r - (j' + 1)) + (j' + 1)) 2,
              Nat.pow_add 2 (4 * (r - (j' + 1))) (j' + 1)]
          change 4 * (2 ^ (4 * (r - (j' + 1))) * 2 ^ (j' + 1) * 4) = _
          rw [Nat.mul_comm (2 ^ (4 * (r - (j' + 1))) * 2 ^ (j' + 1)) 4,
              ← Nat.mul_assoc 4 (2 ^ (4 * (r - (j' + 1)))) (2 ^ (j' + 1))]
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
                = 2 ^ (4 * r + 1 - 3 * j') * (3 * 3 ^ (1 + 2 * j')) := by
                  rw [← Nat.mul_assoc 3, Nat.mul_comm 3 (2 ^ (4 * r + 1 - 3 * j')), Nat.mul_assoc]
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
          cousinDiamond7Iter_add (1 + 2 * j') 1,
          cousinDiamond7Iter_add 1 (2 * j')]
      have hi1 : cousinDiamond7Iter 1 x0 = 2 ^ (4 * r + 1) * 3 ^ 1 - 7 := hs_first
      rw [hi1, hclimb]
      exact hs_last
  refine ⟨by decide, by decide, by decide, hspiral, ?_⟩
  intro terms A0 B0 C0 hnonempty
  rcases three_family_multiterm_laurent_obstruction terms A0 B0 C0 hnonempty with
    h97 | ⟨j2, hj2⟩ | ⟨r, hr_pos, hr3⟩
  · have hs97 : cousinDiamond7Step 97 = 73 := by decide
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
      refine ⟨by dsimp [xj2]; omega, ?_, ?_⟩
      · have hzj_m4 : zj % 4 = 1 := by omega
        dsimp [xj2]; omega
      · have hpow2 : 3 * xj2 + 5 = 2 ^ (6 * j2 + 9) * 1 := by
          rw [Nat.mul_one, show 6 * j2 + 9 = 2 * (3 * j2 + 4) + 1 by omega,
              Nat.pow_succ, ← pow4_eq_pow2_even (3 * j2 + 4), Nat.mul_comm]
          dsimp [xj2]; omega
        rw [hpow2]
        exact core2_pow2_mul (6 * j2 + 9) 1 (by decide) (by decide)
    have hnc8_xj2 : ¬ isDiamond7Cone8 xj2 :=
      not_cone8_of_mod8_ne_5 xj2 (by have h := hc4_xj2.2.1; omega)
    have hnc7_xj2 : ¬ isDiamond6Cone7 xj2 :=
      not_cone7_of_mod8_ne_5 xj2 (by have h := hc4_xj2.2.1; omega)
    have hnc6_xj2 : ¬ isDiamond5Cone6 xj2 := by
      rintro ⟨_, h256, _, _⟩; have h := hc4_xj2.2.1; omega
    have hstep_xj2 : cousinDiamond7Step xj2 = yj2 := by
      rw [cousinDiamond7Step_eq_d6_of_not_cone8 xj2 hnc8_xj2,
          cousinDiamond6Step_eq_d5_of_not_cone7 xj2 hnc7_xj2,
          cousinDiamond5Step_eq_d4_of_not_cone6 xj2 hnc6_xj2]
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
        cousinDiamond7Iter i xr3 = 3 ^ i * 2 ^ (2 * r + 1 - i) - 1 ∧
        cousinDiamond7Iter i xr3 ≥ 7 ∧
        (cousinDiamond7Iter i xr3) % 2 = 1 := by
      intro i hi
      have hf := cousin_diamond7_mersenne_scaled i (2 * r + 1) 1 (by omega) (by decide)
      rw [← hxr3_pow, Nat.mul_one] at hf
      have hprod_ge8 : 3 ^ i * 2 ^ (2 * r + 1 - i) ≥ 8 := by
        have h1 : 2 ^ i * 2 ^ (2 * r + 1 - i) ≤ 3 ^ i * 2 ^ (2 * r + 1 - i) :=
          Nat.mul_le_mul_right _ (pow2_le_pow3 i)
        rw [← Nat.pow_add, show i + (2 * r + 1 - i) = 2 * r + 1 by omega] at h1
        exact Nat.le_trans (pow2_mono_nat (by omega : 3 ≤ 2 * r + 1)) h1
      have hprod_ev : (3 ^ i * 2 ^ (2 * r + 1 - i)) % 2 = 0 := by
        rw [show 2 * r + 1 - i = (2 * r - i) + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc]; omega
      exact ⟨hf, by rw [hf]; omega, by rw [hf]; omega⟩
    have hiter_2r : cousinDiamond7Iter (2 * r) xr3 = zr := by
      have hf := (hglide_i (2 * r) (Nat.le_refl _)).1
      rw [hf, show 2 * r + 1 - 2 * r = 1 by omega, Nat.pow_one,
          ← pow9_eq_pow3_double r, Nat.mul_comm]
    have hstep_zr : cousinDiamond7Step zr = yr3 := by
      rw [cousinDiamond7Step_eq_d6_of_not_cone8 zr (not_cone8_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 zr (not_cone7_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 zr (not_cone6_of_mod16_ne_13 zr (by dsimp [zr]; omega))]
      have hnc5 : ¬ isDiamond4Cone5 zr := by rintro ⟨_, h32, _, _⟩; dsimp [zr] at h32; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 zr hnc5]
      have hc3 : core3 (zr + 1) = 2 := by
        rw [show zr + 1 = 2 * 9 ^ r by dsimp [zr]; omega,
            core3_mul2 (9 ^ r) (by omega), (pow9_eq_v3Pow_w5 r).2]
      rw [cousinDiamond3Step_of_core3_succ_two_w8 zr (by dsimp [zr]; omega) (by dsimp [zr]; omega) hc3]
      dsimp [zr, yr3]; omega
    have hiter_2r1 : cousinDiamond7Iter (2 * r + 1) xr3 = yr3 := by
      rw [cousinDiamond7Iter_add (2 * r) 1 xr3, hiter_2r]; exact hstep_zr
    have hall : ∀ i : Nat, i < 2 * r + 1 ->
        cousinDiamond7Iter i xr3 ≥ 3 ∧
        (cousinDiamond7Iter i xr3) % 2 = 1 ∧
        cousinDiamond7Step (cousinDiamond7Iter i xr3) ≥ 3 := by
      intro i hi
      by_cases hlt : i < 2 * r
      · rcases hglide_i i (by omega) with ⟨_, hge7, hodd_i⟩
        have hnext : cousinDiamond7Step (cousinDiamond7Iter i xr3) =
            cousinDiamond7Iter (i + 1) xr3 :=
          (cousinDiamond7Iter_add i 1 xr3).symm
        rcases hglide_i (i + 1) (by omega) with ⟨_, hge7_n, _⟩
        exact ⟨by omega, hodd_i, by rw [hnext]; omega⟩
      · have hi_eq : i = 2 * r := by omega
        rw [hi_eq, hiter_2r, hstep_zr]
        exact ⟨by dsimp [zr]; omega, by dsimp [zr]; omega, by dsimp [yr3]; omega⟩
    change ¬ laurentDescProp terms A0 B0 C0 xr3 yr3 at hr3
    rw [← hiter_2r1] at hr3
    exact exists_non_desc_along_diamond7_iter terms A0 B0 C0 (2 * r + 1) xr3 (by omega) hall hr3

/--
  Theorem W10.3g (`cousin_diamond7_q6_noninteger_avoids_cone8`, choice-free `zero custom axioms`):
  Universal Non-Integer Rational Exclusion from Cone 8 on `M1 = Q_(6)^+`:
  For EVERY reduced non-integer rational `(num, den)` (`Nat.gcd num den = 1` and `den > 1`),
  `core3 (core2 (34603 * den + num)) ≠ den`, so `cousinDiamond7StepQ6 (num, den)` NEVER enters
  Cone 8 and agrees identically with `cousinDiamond6StepQ6 (num, den)`!
-/
theorem cousin_diamond7_q6_noninteger_avoids_cone8 (num den : Nat)
    (hgcd : Nat.gcd num den = 1) (hden : den > 1) :
    core3 (core2 (34603 * den + num)) ≠ den ∧
    cousinDiamond7StepQ6 (num, den) = cousinDiamond6StepQ6 (num, den) := by
  have hne : core3 (core2 (34603 * den + num)) ≠ den := by
    intro heq
    have hdvd_sum : den ∣ (34603 * den + num) := by
      have hc_dvd : core3 (core2 (34603 * den + num)) ∣ (34603 * den + num) :=
        Nat.dvd_trans (core3Aux_dvd_w8 _ _) (core2Aux_dvd_w8 _ _)
      rwa [heq] at hc_dvd
    rcases hdvd_sum with ⟨k, hk⟩
    have hdvd_num : den ∣ num := ⟨k - 34603, by
      have hge : k ≥ 34603 := by
        by_cases hlt : k < 34603
        · have hm := Nat.mul_le_mul_left den (show k ≤ 34602 by omega); omega
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
  unfold cousinDiamond7StepQ6
  have hcond : ¬ (num ≥ 12548309 * den ∧ (num * invMod4194304Odd den) % 4194304 = 4159701 ∧
      (num * (den % 3)) % 3 = 2 ∧ core3 (core2 (34603 * den + num)) = den) :=
    fun ⟨_, _, _, hc⟩ => hne hc
  simp only [hcond, ite_false]

set_option maxRecDepth 16384 in
/--
  Theorem W10.3h (`cousin_diamond7_counter_model_separation`, choice-free `[]` axioms):
  `T_diamond7` rejects ALL three Counter-Models (`M1 = Q_(6)^+` 5-cycle `(1, 7) -> ... -> (1, 7)`
  plus non-integer `(12548309, 7)` bypassing Cone 8 by `W10.3g`, `M2 = Z^-` cycles `-1` and
  `-5 -> -7 -> -10 -> -5`, and `M3` supercritical `q = 7` 5-cycle at `5`), AND at the genuine
  `v_2(3x + 1) = 7` Cone-8 jumps `12548309 -> 294101 -> 6893 -> 2585` (`14` steps to `1`) and
  `3 * 2 ^ 113 - 34603` (`ZPOS_COUSIN_DIAMOND7_CONE8_JUMP`) strictly increases `cousinDiamond2Phi`
  (`cousinDiamond2Phi x < cousinDiamond2Phi (cousinDiamond7Step x)`) directly into
  `Cone 7 -> Cone 6 -> Cone 5` while converging to `1` in `104` steps!
-/
theorem cousin_diamond7_counter_model_separation :
    cousinDiamond7StepInt (-1) = -1 ∧
    cousinDiamond7IterInt 3 (-5) = -5 ∧
    cousinDiamond7IterParam 7 5 5 = 5 ∧
    cousinDiamond7StepQ6 (1, 7) = (5, 7) ∧
    cousinDiamond7IterQ6 5 (1, 7) = (1, 7) ∧
    cousinDiamond7StepQ6 (12548309, 7) = cousinDiamond6StepQ6 (12548309, 7) ∧
    cousinDiamond7Step 12548309 = 294101 ∧
    cousinDiamond7StepInt 12548309 = 294101 ∧
    cousinDiamond7StepQ6 (12548309, 1) = (294101, 1) ∧
    cousinDiamond7Iter 14 12548309 = 1 ∧
    isDiamond7Cone8 (3 * 2 ^ 113 - 34603) ∧
    isDiamond6Cone7 (cousinDiamond7Step (3 * 2 ^ 113 - 34603)) ∧
    cousinDiamond2Phi (3 * 2 ^ 113 - 34603) <
      cousinDiamond2Phi (cousinDiamond7Step (3 * 2 ^ 113 - 34603)) ∧
    cousinDiamond7Iter 104 (3 * 2 ^ 113 - 34603) = 1 := by
  decide

-- ============================================================================
-- SECTION 4: Front D (Branches P2.2 & P5.3) — Complete Mod-`54` (`2 * 3^3`)
--            Markov Image Law & Coupled Archimedean–Triadic Dyadic Window
--            `[2^M, 2^(M+1))` Unique Shift-Pinning & `L^2` Collision Bounds
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Section 4A: Complete Mod-`54` Markov Bijection & `1111 ↦ 27 mod 54` Lock (`P5.3`)
-- ----------------------------------------------------------------------------

/--
  Theorem W10.4a (`markovShift_mod54_bijection_and_four_ones_27_lock`, `zero custom axioms`):
  Complete Mod-`54` (`2 * 3^3`) Markov Image Bijection, `36 / 54 = 2 / 3` Forbidden-Residue
  Confinement on `w(u) ≥ 4`, & Universal `4`-Ones `27 mod 54` Suffix Lock:
  1. **Exact Mod-`54` Contraction & Bijection onto `18` Odd Non-`5 mod 6` Classes (`∀ w ≥ 3`)**:
     For EVERY weight `w ≥ 3` and `a < 2 * 3 ^ (w - 1)`,
       `markovShiftTrue w a % 54 = markovShiftTrue 3 (a % 18) % 54`,
     and `r ↦ markovShiftTrue 3 r.val % 54` is strictly injective on `Fin 18`, mapping `[0, 18)`
     bijectively onto `[1, 3, 7, 9, 13, 15, 19, 21, 25, 27, 31, 33, 37, 39, 43, 45, 49, 51]`!
  2. **Universal `36 / 54` Core-Word Confinement (`∀ u`, `IsCoreParityWord u`, `parityWeight u ≥ 4`)**:
       `canonicalSuffixShift u 1 % 54 ∈
         ([1, 3, 7, 9, 13, 15, 19, 21, 25, 27, 31, 33, 37, 39, 43, 45, 49, 51] : List Nat)`!
  3. **Exact Mod-`54` Suffix Locks Across Unrestricted Prefixes**:
     - For EVERY `pref : List Bool` with `parityWeight pref ≥ 1`:
       `canonicalSuffixShift (pref ++ [true, true, true]) 1 % 54 = 9 ∨
        canonicalSuffixShift (pref ++ [true, true, true]) 1 % 54 = 27`;
     - For EVERY `pref : List Bool` (completely unrestricted, including `pref = []`):
       `canonicalSuffixShift (pref ++ [true, true, true, true]) 1 % 54 = 27` AND
       `canonicalSuffixShift (pref ++ [true, false, true, true, true]) 1 % 54 = 9`!
-/
theorem markovShift_mod54_bijection_and_four_ones_27_lock :
    ((∀ (w a : Nat), w ≥ 3 -> a < 2 * 3 ^ (w - 1) ->
        markovShiftTrue w a % 54 = markovShiftTrue 3 (a % 18) % 54) ∧
     (∀ x1 x2 : Fin 18,
        markovShiftTrue 3 x1.val % 54 = markovShiftTrue 3 x2.val % 54 -> x1 = x2) ∧
     (∀ x : Fin 18,
        markovShiftTrue 3 x.val % 54 ∈
          ([1, 3, 7, 9, 13, 15, 19, 21, 25, 27, 31, 33, 37, 39, 43, 45, 49, 51] : List Nat))) ∧
    (∀ u : List Bool, IsCoreParityWord u -> parityWeight u ≥ 4 ->
      canonicalSuffixShift u 1 % 54 ∈
        ([1, 3, 7, 9, 13, 15, 19, 21, 25, 27, 31, 33, 37, 39, 43, 45, 49, 51] : List Nat)) ∧
    ((∀ pref : List Bool, parityWeight pref ≥ 1 ->
        canonicalSuffixShift (pref ++ [true, true, true]) 1 % 54 = 9 ∨
        canonicalSuffixShift (pref ++ [true, true, true]) 1 % 54 = 27) ∧
     (∀ pref : List Bool,
        canonicalSuffixShift (pref ++ [true, true, true, true]) 1 % 54 = 27 ∧
        canonicalSuffixShift (pref ++ [true, false, true, true, true]) 1 % 54 = 9)) := by
  have hcongr54 : ∀ (w a : Nat), w ≥ 3 -> a < 2 * 3 ^ (w - 1) ->
      markovShiftTrue w a % 54 = markovShiftTrue 3 (a % 18) % 54 := by
    intro w a hw3 ha_lt
    have hr_lt : a % 18 < 2 * 3 ^ (3 - 1) := Nat.mod_lt a (by decide)
    exact markovShiftTrue_contraction_mod_pow3 2 w 3 a (a % 18)
      (by omega) (by decide) ha_lt hr_lt (by simp)
  have hinj18 : ∀ x1 x2 : Fin 18,
      markovShiftTrue 3 x1.val % 54 = markovShiftTrue 3 x2.val % 54 -> x1 = x2 := by
    decide
  have hmem18 : ∀ x : Fin 18,
      markovShiftTrue 3 x.val % 54 ∈
        ([1, 3, 7, 9, 13, 15, 19, 21, 25, 27, 31, 33, 37, 39, 43, 45, 49, 51] : List Nat) := by
    decide
  refine ⟨⟨hcongr54, hinj18, hmem18⟩, ?_, ⟨?_, ?_⟩⟩
  · -- Core-word mod-`54` confinement on `w(u) ≥ 4`:
    intro u hu hw4
    rcases list_eq_append_true_of_reverse_head u hu.2 with ⟨v, rfl⟩
    have hw_v : parityWeight v ≥ 3 := by
      rw [parityWeight_append] at hw4
      have h1 : parityWeight [true] = 1 := rfl
      rw [h1] at hw4; omega
    have hrec : canonicalSuffixShift (v ++ [true]) 1 =
        markovShiftTrue (parityWeight v) (canonicalSuffixShift v 1) :=
      (canonicalSuffixShift_append_markov_recurrence.2.2 v (by omega)).2.2.1
    have ha_lt := (canonicalSuffixShift_spec_unique v 1 (by omega) (by decide)).1
    rw [hrec, hcongr54 (parityWeight v) (canonicalSuffixShift v 1) hw_v ha_lt]
    exact hmem18 ⟨canonicalSuffixShift v 1 % 18, Nat.mod_lt _ (by decide)⟩
  · -- `pref ++ [true, true, true]` (`parityWeight pref ≥ 1`) mod `54 ∈ {9, 27}`:
    intro pref hwp
    have hap1 := iterMarkovShift_append_canonical [true, true, true] pref hwp
    have ha_lt := (canonicalSuffixShift_spec_unique pref 1 hwp (by decide)).1
    by_cases hpar : canonicalSuffixShift pref 1 % 2 = 0
    · left
      have hbase0 : canonicalSuffixShift [true, false] 1 % 2 = 0 := by decide
      have hap0 := iterMarkovShift_append_canonical [true, true, true] [true, false] (by decide)
      change canonicalSuffixShift ([true, false] ++ [true, true, true]) 1 =
        iterMarkovShift [true, true, true] 1 (canonicalSuffixShift [true, false] 1) at hap0
      have hc := iterMarkovShift_congr_mod_pow3 [true, true, true] 0 (parityWeight pref) 1
        (canonicalSuffixShift pref 1) (canonicalSuffixShift [true, false] 1)
        hwp (by decide) ha_lt (by decide)
        (by simp only [Nat.pow_zero, Nat.mul_one]; exact hpar.trans hbase0.symm)
      rw [← hap1, ← hap0] at hc
      have hv : canonicalSuffixShift ([true, false] ++ [true, true, true]) 1 % 54 = 9 := by decide
      exact hc.trans hv
    · right
      have hodd : canonicalSuffixShift pref 1 % 2 = 1 := by omega
      have hbase1 : canonicalSuffixShift [true] 1 % 2 = 1 := by decide
      have hap1' := iterMarkovShift_append_canonical [true, true, true] [true] (by decide)
      change canonicalSuffixShift ([true] ++ [true, true, true]) 1 =
        iterMarkovShift [true, true, true] 1 (canonicalSuffixShift [true] 1) at hap1'
      have hc := iterMarkovShift_congr_mod_pow3 [true, true, true] 0 (parityWeight pref) 1
        (canonicalSuffixShift pref 1) (canonicalSuffixShift [true] 1)
        hwp (by decide) ha_lt (by decide)
        (by simp only [Nat.pow_zero, Nat.mul_one]; exact hodd.trans hbase1.symm)
      rw [← hap1, ← hap1'] at hc
      have hv : canonicalSuffixShift ([true] ++ [true, true, true]) 1 % 54 = 27 := by decide
      exact hc.trans hv
  · -- Unrestricted `pref ++ [true, true, true, true]` and `pref ++ [true, false, true, true, true]`:
    intro pref
    have ha1 := canonicalSuffixShift_mod18_and_pow3_memory_annihilation.2.1 3 pref
      [true, true, true, true] (by decide)
    have hv1 : canonicalSuffixShift [true, true, true, true] 1 % 54 = 27 := by decide
    have ha2 := canonicalSuffixShift_mod18_and_pow3_memory_annihilation.2.1 3 pref
      [true, false, true, true, true] (by decide)
    have hv2 : canonicalSuffixShift [true, false, true, true, true] 1 % 54 = 9 := by decide
    exact ⟨by simpa using ha1.trans hv1, by simpa using ha2.trans hv2⟩

-- ----------------------------------------------------------------------------
-- Section 4B: Coupled Archimedean–Triadic Dyadic Window `[2^M, 2^(M+1))`
--             Unique Shift-Pinning & Multi-Scale `L^2` Collision Energy (`P2.2`)
-- ----------------------------------------------------------------------------

/--
  Sharp Extremal Carry Identity (`affineCarry_add_pow2_le_pow3_mul_pow2`, `zero custom axioms`):
  For EVERY `u : List Bool`,
    `affineCarry u + 2 ^ u.length ≤ 3 ^ parityWeight u * 2 ^ (u.length - parityWeight u)`
  (equivalently `affineCarry u ≤ (3 ^ w - 2 ^ w) * 2 ^ (L - w) < 3 ^ w * 2 ^ (L - w)`),
  improving `affineCarry < 3 ^ w * 2 ^ L` by the exact factor `2 ^ w`!
-/
theorem affineCarry_add_pow2_le_pow3_mul_pow2 :
    ∀ u : List Bool,
      affineCarry u + 2 ^ u.length ≤ 3 ^ parityWeight u * 2 ^ (u.length - parityWeight u)
  | [] => by decide
  | false :: rest => by
    have ih := affineCarry_add_pow2_le_pow3_mul_pow2 rest
    have hw_le := parityWeight_le_length rest
    have hcar : affineCarry (false :: rest) = 2 * affineCarry rest := by
      change affineCarry ([false] ++ rest) = 2 * affineCarry rest
      rw [affineCarry_append]
      have hc0 : affineCarry [false] = 0 := rfl
      have hl1 : [false].length = 1 := rfl
      rw [hc0, hl1, Nat.mul_zero, Nat.zero_add]
    have hwt : parityWeight (false :: rest) = parityWeight rest := rfl
    rw [hcar, hwt, List.length_cons,
        show rest.length + 1 - parityWeight rest = (rest.length - parityWeight rest) + 1 by omega,
        Nat.pow_succ 2 rest.length, Nat.pow_succ 2 (rest.length - parityWeight rest),
        Nat.mul_comm (2 ^ rest.length) 2, ← Nat.mul_add 2 (affineCarry rest) (2 ^ rest.length)]
    have hm := Nat.mul_le_mul_left 2 ih
    have hr : 2 * (3 ^ parityWeight rest * 2 ^ (rest.length - parityWeight rest)) =
        3 ^ parityWeight rest * (2 ^ (rest.length - parityWeight rest) * 2) := by
      rw [← Nat.mul_assoc 2, Nat.mul_comm 2 (3 ^ parityWeight rest), Nat.mul_assoc,
          Nat.mul_comm 2 (2 ^ (rest.length - parityWeight rest))]
    rwa [hr] at hm
  | true :: rest => by
    have ih := affineCarry_add_pow2_le_pow3_mul_pow2 rest
    have hcar : affineCarry (true :: rest) = 3 ^ parityWeight rest + 2 * affineCarry rest := by
      change affineCarry ([true] ++ rest) = 3 ^ parityWeight rest + 2 * affineCarry rest
      rw [affineCarry_append]
      have hc1 : affineCarry [true] = 1 := rfl
      have hl1 : [true].length = 1 := rfl
      rw [hc1, hl1, Nat.mul_one]
    have hwt : parityWeight (true :: rest) = parityWeight rest + 1 := by
      simp [parityWeight]; omega
    rw [hcar, hwt, List.length_cons,
        show (rest.length + 1) - (parityWeight rest + 1) = rest.length - parityWeight rest by omega,
        Nat.pow_succ 2 rest.length, Nat.pow_succ 3 (parityWeight rest)]
    have hp2_pos := pow2_pos_nat (rest.length - parityWeight rest)
    have h1 : 3 ^ parityWeight rest ≤ 3 ^ parityWeight rest * 2 ^ (rest.length - parityWeight rest) := by
      simpa using Nat.mul_le_mul_left (3 ^ parityWeight rest) hp2_pos
    have h2 : 2 * (affineCarry rest + 2 ^ rest.length) ≤
        2 * (3 ^ parityWeight rest * 2 ^ (rest.length - parityWeight rest)) :=
      Nat.mul_le_mul_left 2 ih
    rw [Nat.mul_add 2 (affineCarry rest) (2 ^ rest.length), Nat.mul_comm 2 (2 ^ rest.length)] at h2
    have hr : 3 ^ parityWeight rest * 3 * 2 ^ (rest.length - parityWeight rest) =
        3 ^ parityWeight rest * 2 ^ (rest.length - parityWeight rest) +
          2 * (3 ^ parityWeight rest * 2 ^ (rest.length - parityWeight rest)) := by
      generalize 3 ^ parityWeight rest = P3, 2 ^ (rest.length - parityWeight rest) = P2
      rw [Nat.mul_assoc P3 3 P2, Nat.mul_comm 3 P2, ← Nat.mul_assoc P3 P2 3]
      omega
    rw [hr]
    omega

theorem core_word_canonicalSuffixShift_mod6_1_or_3 (u : List Bool) (hu : IsCoreParityWord u) :
    canonicalSuffixShift u 1 % 6 = 1 ∨ canonicalSuffixShift u 1 % 6 = 3 := by
  by_cases hw2 : parityWeight u ≥ 2
  · exact canonicalSuffixShift_markov_bijection_and_mod6_lock.2.2.2.2 u hu hw2
  · -- `parityWeight u ≤ 1` with `IsCoreParityWord u` forces `u = [true]`:
    have hw1 : parityWeight u ≥ 1 := reverse_head_true_imp_weight_pos u hu.2
    have hweq : parityWeight u = 1 := by omega
    cases u with
    | nil => simp [IsCoreParityWord] at hu
    | cons b rest =>
      have hb : b = true := by simpa [IsCoreParityWord] using hu.1
      subst hb
      cases rest with
      | nil => left; decide
      | cons b2 rest2 =>
        exfalso
        simp only [parityWeight] at hweq
        have hr0 : parityWeight (b2 :: rest2) = 0 := by omega
        -- `reverse.head? = some true` implies `parityWeight ≥ 1` on `b2 :: rest2`:
        have hrev_tail : (b2 :: rest2).reverse.head? = some true := by
          have hr_app : (true :: b2 :: rest2).reverse = (b2 :: rest2).reverse ++ [true] := by simp
          have hlen_pos : (b2 :: rest2).reverse ≠ [] := by
            intro he; have hl := congrArg List.length he; simp at hl
          rcases List.exists_cons_of_ne_nil hlen_pos with ⟨hd, tl, hcons⟩
          have hhu := hu.2
          rw [hr_app, hcons, List.cons_append] at hhu
          simpa [hcons] using hhu
        have hpos_tail := reverse_head_true_imp_weight_pos (b2 :: rest2) hrev_tail
        omega

/-- Multiplicity of `x : Nat` in `ys : List Nat`. -/
def countEqInList (x : Nat) : List Nat -> Nat
  | [] => 0
  | y :: ys => (if x = y then 1 else 0) + countEqInList x ys

/-- Exact second-moment `L^2` ordered-pair collision energy `∑_{n} count(n, ys)^2 = #{(i, j) | ys[i] = ys[j]}`. -/
def l2CollisionEnergy : List Nat -> Nat
  | [] => 0
  | x :: xs => 1 + 2 * countEqInList x xs + l2CollisionEnergy xs

/-- Surviving multi-scale `q = 0` first-hit leaves up to core length `L_max` falling in `[2 ^ M, 2 ^ (M + 1))`. -/
def dyadicWindowSurvivingQ0Leaves (L_max M : Nat) : List Nat :=
  (firstHitSurvivingQ0LeavesUpToLen L_max).filter (fun y => decide (2 ^ M ≤ y ∧ y < 2 ^ (M + 1)))

theorem countEqInList_eq_zero_of_not_mem (x : Nat) :
    ∀ (ys : List Nat), x ∉ ys -> countEqInList x ys = 0
  | [], _ => rfl
  | y :: ys, hnm => by
    have hxy : ¬ (x = y) := fun h => hnm (h ▸ List.Mem.head _)
    have hnm_ys : x ∉ ys := fun hm => hnm (List.mem_cons_of_mem _ hm)
    simp only [countEqInList, hxy, ite_false, Nat.zero_add,
               countEqInList_eq_zero_of_not_mem x ys hnm_ys]

theorem noDupNat_count_le_one_and_l2_eq_len :
    ∀ ys : List Nat,
      NoDupNat ys ->
      (∀ n : Nat, countEqInList n ys ≤ 1) ∧
      l2CollisionEnergy ys = ys.length
  | [], _ => ⟨fun _ => Nat.zero_le 1, rfl⟩
  | x :: xs, NoDupNat.cons _ _ hnx hnd_xs => by
    rcases noDupNat_count_le_one_and_l2_eq_len xs hnd_xs with ⟨hc_le, hl2⟩
    refine ⟨?_, ?_⟩
    · intro n
      simp only [countEqInList]
      by_cases hnx_eq : n = x
      · subst hnx_eq
        rw [ite_true_of_w10 rfl, countEqInList_eq_zero_of_not_mem n xs hnx]
        omega
      · rw [ite_false_of_w10 hnx_eq, Nat.zero_add]
        exact hc_le n
    · simp only [l2CollisionEnergy, List.length_cons,
                 countEqInList_eq_zero_of_not_mem x xs hnx, Nat.mul_zero, Nat.add_zero, hl2]
      omega

theorem mem_filter_w10 (p : Nat -> Bool) :
    ∀ (xs : List Nat) (y : Nat), y ∈ xs.filter p -> y ∈ xs ∧ p y = true
  | [], _, hm => by cases hm
  | x :: xs, y, hm => by
    cases hpx : p x with
    | false =>
      simp only [List.filter, hpx] at hm
      rcases mem_filter_w10 p xs y hm with ⟨h1, h2⟩
      exact ⟨List.mem_cons_of_mem x h1, h2⟩
    | true =>
      simp only [List.filter, hpx] at hm
      cases hm with
      | head => exact ⟨List.Mem.head _, hpx⟩
      | tail _ htail =>
        rcases mem_filter_w10 p xs y htail with ⟨h1, h2⟩
        exact ⟨List.mem_cons_of_mem x h1, h2⟩

theorem noDupNat_filter (p : Nat -> Bool) :
    ∀ xs : List Nat, NoDupNat xs -> NoDupNat (xs.filter p)
  | [], _ => NoDupNat.nil
  | x :: xs, NoDupNat.cons _ _ hnx hnd_xs => by
    have ih := noDupNat_filter p xs hnd_xs
    cases hpx : p x with
    | false => simpa [List.filter, hpx] using ih
    | true =>
      simp only [List.filter, hpx]
      refine NoDupNat.cons x (xs.filter p) ?_ ih
      intro hm
      exact hnx (mem_filter_w10 p xs x hm).1

theorem noDupNat_map_inj (f : Nat -> Nat) :
    ∀ xs : List Nat,
      NoDupNat xs ->
      (∀ a b : Nat, a ∈ xs -> b ∈ xs -> f a = f b -> a = b) ->
      NoDupNat (xs.map f)
  | [], _, _ => NoDupNat.nil
  | x :: xs, NoDupNat.cons _ _ hnx hnd_xs, hinj => by
    simp only [List.map]
    refine NoDupNat.cons (f x) (xs.map f) ?_
      (noDupNat_map_inj f xs hnd_xs (fun a b ha hb =>
        hinj a b (List.mem_cons_of_mem x ha) (List.mem_cons_of_mem x hb)))
    intro hm
    rcases List.mem_map.mp hm with ⟨z, hz_mem, hfz⟩
    have hzx := hinj z x (List.mem_cons_of_mem x hz_mem) (List.Mem.head _) hfz
    subst hzx
    exact hnx hz_mem

theorem noDupNat_length_le_of_lt :
    ∀ (N : Nat) (xs : List Nat),
      NoDupNat xs -> (∀ y ∈ xs, y < N) -> xs.length ≤ N
  | 0, xs, _, hall => by
    cases xs with
    | nil => exact Nat.le_refl 0
    | cons x _ => exact False.elim (Nat.not_lt_zero x (hall x (List.Mem.head _)))
  | n + 1, xs, hnd, hall => by
    rcases nodup_eraseAllNat_and_len n xs hnd with ⟨hnd', hlen'⟩
    have hall' : ∀ y ∈ eraseAllNat n xs, y < n := by
      intro y hy
      rcases (mem_eraseAllNat_iff n xs y).mp hy with ⟨hy_xs, hy_ne⟩
      have hlt := hall y hy_xs
      omega
    have ih := noDupNat_length_le_of_lt n (eraseAllNat n xs) hnd' hall'
    omega

/--
  Theorem W10.4b (`dyadic_window_unique_shift_pinning_and_l2_energy`, `zero custom axioms`):
  Coupled Archimedean–Triadic Dyadic Window `[2^M, 2^(M+1))` Envelope, Unique Deterministic
  Suffix-Shift Pinning (`∀ L ≤ M + w + 1`), Weight-Split Sharpness, & Multi-Scale `L^2` Energy:
  1. **Two-Sided Dyadic Window Envelope & Forbidden `5 mod 6` Annihilation**:
     For EVERY core parity word `u` (`IsCoreParityWord u`) and `M : Nat` with
     `2 ^ M ≤ exactBackwardQuotient 1 u 0 < 2 ^ (M + 1)`:
     - `3 ^ parityWeight u * 2 ^ M < 2 ^ (u.length + canonicalSuffixShift u 1)`,
     - `2 ^ (u.length + canonicalSuffixShift u 1) <
          3 ^ parityWeight u * (2 ^ (M + 1) + 2 ^ (u.length - parityWeight u))`,
     - `u.length + canonicalSuffixShift u 1 ≥ M + parityWeight u + 1`, AND
     - `canonicalSuffixShift u 1 % 6 = 1 ∨ canonicalSuffixShift u 1 % 6 = 3` (`% 6 ≠ 5` and `% 2 = 1`)!
  2. **Unique Deterministic Suffix-Shift Pinning Across `[2^M, 2^(M+1))` (`∀ L ≤ M + w + 1`)**:
     For ANY two core words `u1, u2` with `u1.length = u2.length`, `parityWeight u1 = parityWeight u2`,
     `u1.length ≤ M + parityWeight u1 + 1`, and BOTH `exactBackwardQuotient 1 u1 0` and
     `exactBackwardQuotient 1 u2 0` in `[2 ^ M, 2 ^ (M + 1))`:
       `canonicalSuffixShift u1 1 = canonicalSuffixShift u2 1`!
  3. **Sharp Weight-Conditioning Necessity Witness (`ZPOS_DYADIC_WINDOW_M8_L6_WEIGHT_SPLIT_301_VS_403`)**:
     Inside `[256, 512)` (`M = 8`) at `L = 6`, `u1 = [true, false, false, true, false, true]`
     (`y = 301, w = 3, a = 7`) and `u2 = [true, true, false, false, true, true]`
     (`y = 403, w = 4, a = 9`) both satisfy `L = 6 ≤ M + w` yet `7 ≠ 9`!
  4. **Multi-Scale Dyadic Window `NoDupNat`, `≤ 2^(M - 1)` Occupancy (`∀ M ≥ 1, ∀ L_max`), & Diagonal `L^2` Energy**:
     For EVERY `L_max M : Nat` with `M ≥ 1`:
     - `NoDupNat (dyadicWindowSurvivingQ0Leaves L_max M)`,
     - `∀ n : Nat, countEqInList n (dyadicWindowSurvivingQ0Leaves L_max M) ≤ 1`,
     - `l2CollisionEnergy (dyadicWindowSurvivingQ0Leaves L_max M) =
          (dyadicWindowSurvivingQ0Leaves L_max M).length` (zero off-diagonal `L^2` collisions!), AND
     - `(dyadicWindowSurvivingQ0Leaves L_max M).length ≤ 2 ^ (M - 1)`!
-/
theorem dyadic_window_unique_shift_pinning_and_l2_energy :
    (∀ (u : List Bool) (M : Nat),
      IsCoreParityWord u ->
      2 ^ M ≤ exactBackwardQuotient 1 u 0 ->
      exactBackwardQuotient 1 u 0 < 2 ^ (M + 1) ->
      3 ^ parityWeight u * 2 ^ M < 2 ^ (u.length + canonicalSuffixShift u 1) ∧
      2 ^ (u.length + canonicalSuffixShift u 1) <
        3 ^ parityWeight u * (2 ^ (M + 1) + 2 ^ (u.length - parityWeight u)) ∧
      u.length + canonicalSuffixShift u 1 ≥ M + parityWeight u + 1 ∧
      (canonicalSuffixShift u 1 % 6 = 1 ∨ canonicalSuffixShift u 1 % 6 = 3)) ∧
    (∀ (u1 u2 : List Bool) (M : Nat),
      IsCoreParityWord u1 -> IsCoreParityWord u2 ->
      u1.length = u2.length ->
      parityWeight u1 = parityWeight u2 ->
      u1.length ≤ M + parityWeight u1 + 1 ->
      2 ^ M ≤ exactBackwardQuotient 1 u1 0 -> exactBackwardQuotient 1 u1 0 < 2 ^ (M + 1) ->
      2 ^ M ≤ exactBackwardQuotient 1 u2 0 -> exactBackwardQuotient 1 u2 0 < 2 ^ (M + 1) ->
      canonicalSuffixShift u1 1 = canonicalSuffixShift u2 1) ∧
    (let u301 : List Bool := [true, false, false, true, false, true]
     let u403 : List Bool := [true, true, false, false, true, true]
     IsCoreParityWord u301 ∧ IsCoreParityWord u403 ∧
     u301.length = 6 ∧ u403.length = 6 ∧
     parityWeight u301 = 3 ∧ parityWeight u403 = 4 ∧
     exactBackwardQuotient 1 u301 0 = 301 ∧
     exactBackwardQuotient 1 u403 0 = 403 ∧
     2 ^ 8 ≤ 301 ∧ 301 < 2 ^ 9 ∧ 2 ^ 8 ≤ 403 ∧ 403 < 2 ^ 9 ∧
     canonicalSuffixShift u301 1 = 7 ∧
     canonicalSuffixShift u403 1 = 9) ∧
    (∀ (L_max M : Nat), M ≥ 1 ->
      let win := dyadicWindowSurvivingQ0Leaves L_max M
      NoDupNat win ∧
      (∀ n : Nat, countEqInList n win ≤ 1) ∧
      l2CollisionEnergy win = win.length ∧
      win.length ≤ 2 ^ (M - 1)) := by
  have henv : ∀ (u : List Bool) (M : Nat),
      IsCoreParityWord u ->
      2 ^ M ≤ exactBackwardQuotient 1 u 0 ->
      exactBackwardQuotient 1 u 0 < 2 ^ (M + 1) ->
      3 ^ parityWeight u * 2 ^ M < 2 ^ (u.length + canonicalSuffixShift u 1) ∧
      2 ^ (u.length + canonicalSuffixShift u 1) <
        3 ^ parityWeight u * (2 ^ (M + 1) + 2 ^ (u.length - parityWeight u)) ∧
      u.length + canonicalSuffixShift u 1 ≥ M + parityWeight u + 1 ∧
      (canonicalSuffixShift u 1 % 6 = 1 ∨ canonicalSuffixShift u 1 % 6 = 3) := by
    intro u M hu hlo hhi
    rcases one_generator_pos_odd_and_reaches_one u 0 hu with ⟨_, _, heq, _⟩
    have hsteps0 : backwardOneTotalSteps u 0 = u.length + canonicalSuffixShift u 1 := by
      unfold backwardOneTotalSteps; simp
    rw [hsteps0] at heq
    -- `affineCarry u ≥ 1` on any core parity word (`u = true :: rest`):
    have hcar_pos : affineCarry u ≥ 1 := by
      cases u with
      | nil => simp [IsCoreParityWord] at hu
      | cons b rest =>
        have hb : b = true := by simpa [IsCoreParityWord] using hu.1
        subst hb
        have hc : affineCarry (true :: rest) = 3 ^ parityWeight rest + 2 * affineCarry rest := by
          change affineCarry ([true] ++ rest) = _
          rw [affineCarry_append]
          have hc1 : affineCarry [true] = 1 := rfl
          have hl1 : [true].length = 1 := rfl
          rw [hc1, hl1, Nat.mul_one]
        have hp3 := pow3_pos_nat (parityWeight rest)
        omega
    have hcar_lt : affineCarry u < 3 ^ parityWeight u * 2 ^ (u.length - parityWeight u) := by
      have hle := affineCarry_add_pow2_le_pow3_mul_pow2 u
      have hp2 := pow2_pos_nat u.length
      omega
    have hm_lo : 3 ^ parityWeight u * 2 ^ M ≤ 3 ^ parityWeight u * exactBackwardQuotient 1 u 0 :=
      Nat.mul_le_mul_left _ hlo
    have hm_hi : 3 ^ parityWeight u * exactBackwardQuotient 1 u 0 ≤
        3 ^ parityWeight u * (2 ^ (M + 1) - 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hgt_left : 3 ^ parityWeight u * 2 ^ M < 2 ^ (u.length + canonicalSuffixShift u 1) := by
      omega
    have hlt_right : 2 ^ (u.length + canonicalSuffixShift u 1) <
        3 ^ parityWeight u * (2 ^ (M + 1) + 2 ^ (u.length - parityWeight u)) := by
      rw [Nat.mul_add]
      have hm_strict : 3 ^ parityWeight u * exactBackwardQuotient 1 u 0 ≤
          3 ^ parityWeight u * 2 ^ (M + 1) :=
        Nat.mul_le_mul_left _ (Nat.le_of_lt hhi)
      omega
    have hexp_ge : u.length + canonicalSuffixShift u 1 ≥ M + parityWeight u + 1 := by
      have hp23 : 2 ^ (M + parityWeight u) ≤ 3 ^ parityWeight u * 2 ^ M := by
        rw [Nat.pow_add 2 M (parityWeight u), Nat.mul_comm (2 ^ M)]
        exact Nat.mul_le_mul_right (2 ^ M) (pow2_le_pow3 (parityWeight u))
      have h2_lt : 2 ^ (M + parityWeight u) < 2 ^ (u.length + canonicalSuffixShift u 1) :=
        Nat.lt_of_le_of_lt hp23 hgt_left
      by_cases hge : u.length + canonicalSuffixShift u 1 ≥ M + parityWeight u + 1
      · exact hge
      · have hle_p2 := pow2_mono_nat
          (by omega : u.length + canonicalSuffixShift u 1 ≤ M + parityWeight u)
        omega
    exact ⟨hgt_left, hlt_right, hexp_ge, core_word_canonicalSuffixShift_mod6_1_or_3 u hu⟩
  refine ⟨henv, ?_, ?_, ?_⟩
  · -- Part 2: Unique Deterministic Suffix-Shift Pinning (`∀ L ≤ M + w + 1`):
    intro u1 u2 M hu1 hu2 hL hw hL_le hlo1 hhi1 hlo2 hhi2
    rcases henv u1 M hu1 hlo1 hhi1 with ⟨hgt1, hlt1, _, hm6_1⟩
    rcases henv u2 M hu2 hlo2 hhi2 with ⟨hgt2, hlt2, _, hm6_2⟩
    rw [hL, hw] at hgt1 hlt1 hL_le
    let L := u2.length
    let w := parityWeight u2
    let a1 := canonicalSuffixShift u1 1
    let a2 := canonicalSuffixShift u2 1
    change 3 ^ w * 2 ^ M < 2 ^ (L + a1) at hgt1
    change 2 ^ (L + a1) < 3 ^ w * (2 ^ (M + 1) + 2 ^ (L - w)) at hlt1
    change 3 ^ w * 2 ^ M < 2 ^ (L + a2) at hgt2
    change 2 ^ (L + a2) < 3 ^ w * (2 ^ (M + 1) + 2 ^ (L - w)) at hlt2
    change L ≤ M + w + 1 at hL_le
    have hp_sub : 2 ^ (L - w) ≤ 2 ^ (M + 1) := pow2_mono_nat (by omega)
    have hrhs_4 : 3 ^ w * (2 ^ (M + 1) + 2 ^ (L - w)) ≤ 4 * (3 ^ w * 2 ^ M) := by
      have hm := Nat.mul_le_mul_left (3 ^ w) (Nat.add_le_add_left hp_sub (2 ^ (M + 1)))
      have h4 : 3 ^ w * (2 ^ (M + 1) + 2 ^ (M + 1)) = 4 * (3 ^ w * 2 ^ M) := by
        rw [Nat.pow_succ 2 M]
        generalize 3 ^ w = P3, 2 ^ M = P2
        rw [← Nat.two_mul (P2 * 2), ← Nat.mul_assoc 2 P2 2, Nat.mul_comm (2 * P2) 2,
            ← Nat.mul_assoc 2 2 P2, show 2 * 2 = 4 from rfl,
            ← Nat.mul_assoc P3 4 P2, Nat.mul_comm P3 4, Nat.mul_assoc]
      rwa [h4] at hm
    have hub1 : 2 ^ (L + a1) < 4 * (3 ^ w * 2 ^ M) := Nat.lt_of_lt_of_le hlt1 hrhs_4
    have hub2 : 2 ^ (L + a2) < 4 * (3 ^ w * 2 ^ M) := Nat.lt_of_lt_of_le hlt2 hrhs_4
    have ha1_odd : a1 % 2 = 1 := by dsimp [a1]; rcases hm6_1 with h | h <;> omega
    have ha2_odd : a2 % 2 = 1 := by dsimp [a2]; rcases hm6_2 with h | h <;> omega
    change a1 = a2
    by_cases h12 : a1 < a2
    · exfalso
      have ha2_ge : L + a2 ≥ (L + a1) + 2 := by omega
      have hp4 : 4 * 2 ^ (L + a1) ≤ 2 ^ (L + a2) := by
        have hm := pow2_mono_nat ha2_ge
        rwa [Nat.pow_add 2 (L + a1) 2, show (2 : Nat) ^ 2 = 4 from rfl, Nat.mul_comm _ 4] at hm
      omega
    · by_cases h21 : a2 < a1
      · exfalso
        have ha1_ge : L + a1 ≥ (L + a2) + 2 := by omega
        have hp4 : 4 * 2 ^ (L + a2) ≤ 2 ^ (L + a1) := by
          have hm := pow2_mono_nat ha1_ge
          rwa [Nat.pow_add 2 (L + a2) 2, show (2 : Nat) ^ 2 = 4 from rfl, Nat.mul_comm _ 4] at hm
        omega
      · omega
  · -- Part 3: Concrete weight-split witness `301` vs `403` in `[256, 512)`:
    dsimp only
    exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, by decide, by decide,
           by decide, by decide, by decide, by decide, by decide, by decide,
           by decide, by decide⟩
  · -- Part 4: Multi-scale dyadic window `NoDupNat`, `≤ 2^(M - 1)` occupancy, & diagonal `L^2` energy:
    intro L_max M hM
    dsimp only
    let win := dyadicWindowSurvivingQ0Leaves L_max M
    rcases multiscale_first_hit_surviving_q0_leaves_nodup L_max with ⟨_, hnd_surv, hmem_surv⟩
    have hnd_win : NoDupNat win :=
      noDupNat_filter _ (firstHitSurvivingQ0LeavesUpToLen L_max) hnd_surv
    rcases noDupNat_count_le_one_and_l2_eq_len win hnd_win with ⟨hcnt_le, hl2_eq⟩
    -- Every `y ∈ win` is odd and lies in `[2^M, 2^(M+1))`:
    have hy_props : ∀ y ∈ win, 2 ^ M ≤ y ∧ y < 2 ^ (M + 1) ∧ y % 2 = 1 := by
      intro y hy
      unfold win dyadicWindowSurvivingQ0Leaves at hy
      rcases mem_filter_w10 _ (firstHitSurvivingQ0LeavesUpToLen L_max) y hy with ⟨hy_surv, hy_dec⟩
      rcases of_decide_eq_true hy_dec with ⟨hlo, hhi⟩
      rcases (hmem_surv y).mp hy_surv with ⟨u, hfh, _, _, rfl⟩
      have hodd := (one_generator_pos_odd_and_reaches_one u 0 hfh.1).2.1
      exact ⟨hlo, hhi, hodd⟩
    have hp2M_ev : 2 ^ M % 2 = 0 := by
      rw [show M = (M - 1) + 1 by omega, Nat.pow_succ]; omega
    let halfIdx : Nat -> Nat := fun y => (y - 2 ^ M) / 2
    have hnd_idx : NoDupNat (win.map halfIdx) := by
      apply noDupNat_map_inj halfIdx win hnd_win
      intro a b ha hb hfeq
      rcases hy_props a ha with ⟨ha_lo, _, ha_odd⟩
      rcases hy_props b hb with ⟨hb_lo, _, hb_odd⟩
      dsimp [halfIdx] at hfeq
      omega
    have hidx_lt : ∀ z ∈ win.map halfIdx, z < 2 ^ (M - 1) := by
      intro z hz
      rcases List.mem_map.mp hz with ⟨y, hy_mem, rfl⟩
      rcases hy_props y hy_mem with ⟨hy_lo, hy_hi, _⟩
      dsimp [halfIdx]
      have hp_sp : 2 ^ (M + 1) = 2 ^ M + 2 ^ M := by rw [Nat.pow_succ 2 M]; omega
      have hp_sp2 : 2 ^ M = 2 * 2 ^ (M - 1) := by
        conv => lhs; rw [show M = (M - 1) + 1 by omega]
        rw [Nat.pow_succ 2 (M - 1), Nat.mul_comm]
      omega
    have hlen_le : win.length ≤ 2 ^ (M - 1) := by
      rw [← List.length_map halfIdx]
      exact noDupNat_length_le_of_lt (2 ^ (M - 1)) (win.map halfIdx) hnd_idx hidx_lt
    exact ⟨hnd_win, hcnt_le, hl2_eq, hlen_le⟩

-- ============================================================================
-- SECTION 5: WAVE 10 COMPLETION — TWO-SIDED MOD-6 TERMINATION OF `all11 \ {R8}`,
-- SHARED-MERSENNE 2-BLOCK MOD-24 OBSTRUCTIONS, `6 x 6` `(T = 5, U = 1)` + CONFLUENT
-- COLUMN EXTRAPOLATION, ALTERNATING `01` STERN FIBONACCI, & ZERO-EXCESS `OCN` BARRIER
-- ============================================================================

-- 5A (`Branch P4.3`): Complete 2-Level `2D` Termination of `all11 \ {R8}` (`120 -> 15 -> 0`)
-- via Two-Sided `(collatzSemL2 × collatzSemMod 6)` & Complete `M ∈ {3, 4}` / `TwoSided` Syzygies:

def wtTwoSidedMod6OmitR8 (s : Fin 84) : Nat :=
  match s.val with
  | 3  => 9   | 9  => 9
  | 24 => 47  | 25 => 1   | 26 => 53  | 27 => 45  | 28 => 43  | 29 => 1
  | 32 => 49  | 34 => 34  | 35 => 22
  | 36 => 81  | 37 => 93  | 38 => 100 | 39 => 122 | 40 => 91  | 41 => 156 | 42 => 39
  | 48 => 89  | 49 => 94  | 50 => 138 | 51 => 88  | 52 => 133 | 53 => 85
  | 54 => 43  | 55 => 2   | 56 => 94  | 58 => 85
  | 60 => 78  | 61 => 55  | 62 => 123 | 63 => 37  | 64 => 123 | 65 => 53
  | 66 => 82  | 67 => 90  | 68 => 91  | 69 => 124 | 70 => 85  | 71 => 149
  | 72 => 80  | 73 => 101 | 74 => 99  | 76 => 75  | 78 => 79  | 79 => 1
  | 80 => 90  | 82 => 75  | _  => 0

def certOmitR8TwoSidedMod6_L1 (s : Fin 84) : NatAffineDim 2 :=
  mk2DAffineW9 1 0 0 0 (wtTwoSidedMod6OmitR8 s) 0

def certOmitR8TwoSidedMod6_L2 (s : Fin 84) : NatAffineDim 2 :=
  match s.val / 12 with
  | 0 => mk2DAffineW9 1 0 0 0 0 0
  | 1 => mk2DAffineW9 1 0 0 0 0 0
  | 2 => mk2DAffineW9 1 0 0 0 1 0
  | 3 => mk2DAffineW9 1 0 0 0 1 0
  | _ => mk2DAffineW9 2 0 0 0 0 0

def towerOmitR8TwoSidedMod6 : List (Fin 84 -> NatAffineDim 2) :=
  [certOmitR8TwoSidedMod6_L1, certOmitR8TwoSidedMod6_L2]

/--
  Theorem W10.1f (`omit_r8_twosided_mod6_admits_2d_hw_tower`, `zero custom axioms`):
  Two-Sided `(collatzSemL2 × collatzSemMod 6)` Terminates Swap-Active `all11 \ {R8}` (`10/11` Rules):
  On `all11OmitR8List = S9 ∪ {R3}` (where swap rule `R3 : T0 B0 -> B0 T0` AND all four infinitely
  recurrent rules `{R2, R5, R7, R9}` are simultaneously active, defeating `M = 2`, `M = 3`, `M = 4`,
  `M = 6`, `M = 8` right-to-left Parikh and `TwoSided(2 × 2)` Parikh!), two-sided labelling over
  `Fin 84` (`14 * 6`) yields an explicit **2-level diagonal `2D` Hofbauer–Waldmann tower (`120 -> 15 -> 0`)**:
  - Level 1 (`certOmitR8TwoSidedMod6_L1`) eliminates `105/120` rules including ALL boundary rules
    (`R1, R2, R9, R10, R11`), leaving `15` pure interior `[T_*, B_*] -> [B_*, T_*]` rules;
  - Level 2 (`certOmitR8TwoSidedMod6_L2`: `B(x) = x + 1, T(x) = 2x`) terminates all `15` remaining rules!
-/
theorem omit_r8_twosided_mod6_admits_2d_hw_tower :
    all11OmitR8List.length = 10 ∧
    (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR8List).length = 120 ∧
    (filterUnorientedGen2D certOmitR8TwoSidedMod6_L1
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR8List)).length = 15 ∧
    checkFin2DHWTowerBool 84 towerOmitR8TwoSidedMod6
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR8List) = true ∧
    GenOmegaHWTower 2 (by decide) 2
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR8List) := by
  have hb : checkFin2DHWTowerBool 84 towerOmitR8TwoSidedMod6
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR8List) = true := by decide
  exact ⟨rfl, rfl, by decide, hb,
    checkFin2DHWTowerBool_sound 84 towerOmitR8TwoSidedMod6
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR8List) hb⟩

theorem all11OmitR8_sub_all11_w10 (r : List MixedSRSSym × List MixedSRSSym)
    (hm : r ∈ all11OmitR8List) : r ∈ all11RuleList := by
  revert r hm; decide

/--
  Theorem W10.1g (`omit_r8_10_of_11_unlabelled_terminates`, `zero custom axioms`):
  Unconditional Unlabelled Termination of Swap-Active `all11 \ {R8}` (`10/11` Collatz Rules):
  Combining `omit_r8_twosided_mod6_admits_2d_hw_tower` with two-sided semantic-labelling lifting
  rules out all infinite `srsPlusFromList` and `srsStepFromList` rewrite chains on `all11OmitR8List`
  (leaving `all11 \ {R3}` as the single remaining open swap-active `10/11` subset of `all11RuleList`)!
-/
theorem omit_r8_10_of_11_unlabelled_terminates :
    (∀ seq : Nat -> List MixedSRSSym,
      ¬ (∀ t : Nat, srsPlusFromList all11OmitR8List (seq t) (seq (t + 1)))) ∧
    (∀ seq : Nat -> List MixedSRSSym,
      ¬ (∀ t : Nat, srsStepFromList all11OmitR8List (seq t) (seq (t + 1)))) := by
  have hM : (6 : Nat) ≥ 1 := by decide
  have hlift := two_sided_zantema_step_lifts 6 hM all11OmitR8List
    (fun r hr q => collatz_l2_is_exact_left_semantic_model r (all11OmitR8_sub_all11_w10 r hr) q)
    (fun r hr a ha => collatz_mod_m_is_exact_semantic_model 6 hM r (all11OmitR8_sub_all11_w10 r hr) a ha)
  have htower := omit_r8_twosided_mod6_admits_2d_hw_tower.2.2.2.2
  have hno_plus : ∀ seq : Nat -> List MixedSRSSym,
      ¬ (∀ t : Nat, srsPlusFromList all11OmitR8List (seq t) (seq (t + 1))) := by
    intro seq hchain
    let lseq : Nat -> List (Fin (14 * 6)) :=
      fun t => labelCollatzWordTwoSided 6 hM (seq t) 0 (by decide) 0 hM
    exact acc_no_infinite_chain (lseq 0)
      (gen_hw_tower_acc_srsPlus 2 (by decide) 2 _ htower (lseq 0))
      lseq rfl (fun t => hlift (seq t) (seq (t + 1)) (hchain t))
  exact ⟨hno_plus, fun seq hstep => hno_plus seq (fun t => ⟨seq (t + 1), hstep t, .refl _⟩)⟩

def syzM3OmitR3Core25 : List Nat :=
  [2, 4, 16, 2, 7, 2, 7, 8, 2, 2, 5, 3, 18, 2, 13, 6, 2, 2, 2, 2, 2, 2, 2, 2, 2]

def syzTwoSidedOmitR3Core36 : List Nat :=
  [1, 1, 1, 1, 1, 1, 17, 1, 4, 7, 12, 1, 6, 1, 9, 1, 1, 1,
   1, 1, 11, 12, 19, 6, 1, 17, 3, 4, 1, 1, 1, 1, 1, 2, 1, 1]

def syzM4OmitR8 : List Nat :=
  [9, 1, 1, 1, 1, 1, 9, 9, 1, 11, 11, 1, 1, 2, 5, 6, 5, 1, 1, 11,
   1, 9, 1, 1, 1, 4, 9, 6, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7]

def syzM4OmitR3 : List Nat :=
  [1, 1, 1, 1, 11, 1, 1, 1, 1, 4, 2, 1, 3, 1, 9, 1, 1, 1, 5, 1,
   5, 8, 4, 1, 1, 7, 12, 7, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

def syzM4All11 : List Nat :=
  [2, 2, 2, 2, 18, 2, 2, 2, 2, 2, 2, 2, 2, 7, 4, 2, 4, 2, 15, 2, 2, 2,
   7, 2, 7, 12, 8, 2, 2, 11, 20, 10, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]

/--
  Theorem W10.1h (`labelled_swap_parikh_syzygy_barriers_complete`, `zero custom axioms`):
  Complete Positive Parikh-Syzygy Barriers on `M = 3 omit R3` (`25/25`), `TwoSided(2 × 2) omit R3`
  (`36/36`), & Higher Dyadic Modulus `M = 4` (`40/40`, `40/40`, `44/44`) Across ALL `k : Nat`.
-/
theorem labelled_swap_parikh_syzygy_barriers_complete :
    let m3_c25 := filterFinParikhUnoriented 21 wtM3OmitR3
                    (labelledCollatzRules 3 (by decide) all11OmitR3List)
    let ts_c36 := filterFinParikhUnoriented 28 wtTwoSidedOmitR3
                    (twoSidedLabelledCollatzRules 2 (by decide) all11OmitR3List)
    let m4_or8 := labelledCollatzRules 4 (by decide) all11OmitR8List
    let m4_or3 := labelledCollatzRules 4 (by decide) all11OmitR3List
    let m4_all := labelledCollatzRules 4 (by decide) all11RuleList
    ∀ k : Nat,
      ¬ GenOmegaParikhTower 21 k m3_c25 ∧
      ¬ GenOmegaParikhTower 28 k ts_c36 ∧
      ¬ GenOmegaParikhTower 28 k m4_or8 ∧
      ¬ GenOmegaParikhTower 28 k m4_or3 ∧
      ¬ GenOmegaParikhTower 28 k m4_all := by
  dsimp only
  have h1 := (positive_parikh_syzygy_blocks_all_omega_towers 21
    (filterFinParikhUnoriented 21 wtM3OmitR3 (labelledCollatzRules 3 (by decide) all11OmitR3List))
    syzM3OmitR3Core25 (by decide)).2
  have h2 := (positive_parikh_syzygy_blocks_all_omega_towers 28
    (filterFinParikhUnoriented 28 wtTwoSidedOmitR3
      (twoSidedLabelledCollatzRules 2 (by decide) all11OmitR3List))
    syzTwoSidedOmitR3Core36 (by decide)).2
  have h3 := (positive_parikh_syzygy_blocks_all_omega_towers 28
    (labelledCollatzRules 4 (by decide) all11OmitR8List) syzM4OmitR8 (by decide)).2
  have h4 := (positive_parikh_syzygy_blocks_all_omega_towers 28
    (labelledCollatzRules 4 (by decide) all11OmitR3List) syzM4OmitR3 (by decide)).2
  have h5 := (positive_parikh_syzygy_blocks_all_omega_towers 28
    (labelledCollatzRules 4 (by decide) all11RuleList) syzM4All11 (by decide)).2
  intro k
  exact ⟨h1 k, h2 k, h3 k, h4 k, h5 k⟩

-- 5B (`Branch P3.4` & `P3.2`): Shared-Mersenne 2-Block `r ≥ 2` `(41 * r, 65 * r)` Squeeze &
-- Universal Mod-24 `{11, 13}` Parity / Companion-Quotient / `(82, 130)` & `(164, 260)` Floors:

def checkSqueeze46At (v : Nat) : Bool :=
  let k0 := minExp2CandW7 v
  decide (k0 ≥ 1) &&
  decide (2 ^ (k0 - 1) ≤ 3 ^ v) &&
  decide (3 ^ v < 2 ^ k0) &&
  decide (46 * (2 ^ k0 - 3 ^ v) ≥ 3 ^ v)

def checkAllSqueeze46UpTo : Nat -> Bool
  | 0 => true
  | v + 1 => checkSqueeze46At (v + 1) && checkAllSqueeze46UpTo v

/-- Pure-kernel certificate verifying `46 * (2 ^ k - 3 ^ v) ≥ 3 ^ v` across all `1 ≤ v ≤ 40`. -/
theorem squeeze46_up_to_40_cert : checkAllSqueeze46UpTo 40 = true := by
  decide

theorem checkSqueeze46At_sound (v k : Nat)
    (hc : checkSqueeze46At v = true) (hgt : 3 ^ v < 2 ^ k) :
    46 * (2 ^ k - 3 ^ v) ≥ 3 ^ v := by
  unfold checkSqueeze46At at hc
  rcases bool_and_split hc with ⟨hc123, hsq_b⟩
  rcases bool_and_split hc123 with ⟨hc12, _⟩
  rcases bool_and_split hc12 with ⟨hk0_pos_b, hle_prev_b⟩
  let k0 := minExp2CandW7 v
  have hk0_pos : k0 ≥ 1 := of_decide_eq_true hk0_pos_b
  have hle_prev : 2 ^ (k0 - 1) ≤ 3 ^ v := of_decide_eq_true hle_prev_b
  have hsq0 : 46 * (2 ^ k0 - 3 ^ v) ≥ 3 ^ v := of_decide_eq_true hsq_b
  have hk_ge_k0 : k ≥ k0 := by
    by_cases hlt : k < k0
    · have hp2_le : 2 ^ k ≤ 2 ^ (k0 - 1) := pow2_mono_nat (by omega)
      omega
    · omega
  have hp2_ge : 2 ^ k0 ≤ 2 ^ k := pow2_mono_nat hk_ge_k0
  exact Nat.le_trans hsq0 (Nat.mul_le_mul_left 46 (by omega : 2 ^ k0 - 3 ^ v ≤ 2 ^ k - 3 ^ v))

theorem checkAllSqueeze46UpTo_sound :
    ∀ (N v k : Nat), checkAllSqueeze46UpTo N = true ->
      1 ≤ v -> v ≤ N -> 3 ^ v < 2 ^ k -> 46 * (2 ^ k - 3 ^ v) ≥ 3 ^ v
  | 0, _, _, _, hv1, hv0, _ => by omega
  | n + 1, v, k, hall, hv1, hv_le, hgt => by
    rcases bool_and_split hall with ⟨hat, hrest⟩
    by_cases heq : v = n + 1
    · rw [heq] at hgt ⊢
      exact checkSqueeze46At_sound (n + 1) k hat hgt
    · exact checkAllSqueeze46UpTo_sound n v k hrest hv1 (by omega) hgt

/--
  Theorem W10.2d (`two_block_shared_mersenne_mod24_and_even_order_obstructions`, `zero custom axioms`):
  Universal `r ≥ 2` Shared-Mersenne 2-Block `(41 * r, 65 * r)` Squeeze & Mod-24 `{11, 13}`
  Quadratic-Reciprocity Parity / Companion-Quotient / `(82, 130)` & `(164, 260)` Obstructions:
  1. **Universal `r ≥ 2` Boost (`46 = 23 * 2`)**: Extending Wave 7's `r ≥ 3` bound to ALL `r ≥ 2`,
     whenever `Nat.gcd d1 d2 ≥ 2` divides `gcd(D, 2 ^ a1 - 1)` on a primitive 2-block cycle,
     `w1 + w2 ≥ 41 * Nat.gcd d1 d2` and `w1 + a1 + w2 + a2 ≥ 65 * Nat.gcd d1 d2`!
  2. **2-Adic Valuation Boost at `q ≡ 13 (mod 24)` (`4 ∣ gcd`)**: For EVERY prime `q % 24 = 13`,
     `4 ∣ ord_q(2) ∧ 4 ∣ ord_q(3/2) ∧ 4 ∣ Nat.gcd (ord_q(2)) (ord_q(3/2))`!
  3. **Shared-Mersenne 2-Block Mod-24 `{11, 13}` Parity, `3 ∣ q0 ∧ 3 ∣ q1`, & `(82, 130)` / `(164, 260)` Floors**:
     For ANY prime `q ∣ gcd(D, 2 ^ a1 - 1)` on `IsPrimitiveTwoBlockBroxWitness w1 a1 w2 a2 q0 q1`:
     - If `q % 24 = 11 ∨ q % 24 = 13`: `2 ∣ a1 ∧ 2 ∣ a2 ∧ 2 ∣ (w1 + w2) ∧ 3 ∣ q0 ∧ 3 ∣ q1 ∧
       w1 + w2 ≥ 82 ∧ w1 + a1 + w2 + a2 ≥ 130`!
     - If `q % 24 = 13`: `4 ∣ a1 ∧ 4 ∣ a2 ∧ 4 ∣ (w1 + w2) ∧ w1 + w2 ≥ 164 ∧ w1 + a1 + w2 + a2 ≥ 260`!
-/
theorem two_block_shared_mersenne_mod24_and_even_order_obstructions :
    (∀ (w1 a1 w2 a2 q0 q1 p d1 d2 : Nat),
      IsPrimitiveTwoBlockBroxWitness w1 a1 w2 a2 q0 q1 ->
      p ≥ 3 -> p % 2 = 1 ->
      IsExactMultOrderMod p 2 d1 ->
      IsExactMultOrderMod p (ratio32Mod p) d2 ->
      Nat.gcd d1 d2 ≥ 2 ->
      p ∣ (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)) ->
      p ∣ (2 ^ a1 - 1) ->
      w1 + w2 ≥ 41 * Nat.gcd d1 d2 ∧
      w1 + a1 + w2 + a2 ≥ 65 * Nat.gcd d1 d2) ∧
    (∀ q d2 d32 : Nat,
      IsPrimeNat q -> q % 24 = 13 ->
      IsExactMultOrderMod q 2 d2 ->
      IsExactMultOrderMod q (ratio32Mod q) d32 ->
      4 ∣ d2 ∧ 4 ∣ d32 ∧ 4 ∣ Nat.gcd d2 d32 ∧ Nat.gcd d2 d32 ≥ 4) ∧
    (∀ (w1 a1 w2 a2 q0 q1 q : Nat),
      IsPrimitiveTwoBlockBroxWitness w1 a1 w2 a2 q0 q1 ->
      IsPrimeNat q ->
      q ∣ (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)) ->
      q ∣ (2 ^ a1 - 1) ->
      ((q % 24 = 11 ∨ q % 24 = 13) ->
        2 ∣ a1 ∧ 2 ∣ a2 ∧ 2 ∣ (w1 + w2) ∧ 3 ∣ q0 ∧ 3 ∣ q1 ∧
        w1 + w2 ≥ 82 ∧ w1 + a1 + w2 + a2 ≥ 130) ∧
      (q % 24 = 13 ->
        4 ∣ a1 ∧ 4 ∣ a2 ∧ 4 ∣ (w1 + w2) ∧
        w1 + w2 ≥ 164 ∧ w1 + a1 + w2 + a2 ≥ 260)) := by
  have huniv2 : ∀ (w1 a1 w2 a2 q0 q1 p d1 d2 : Nat),
      IsPrimitiveTwoBlockBroxWitness w1 a1 w2 a2 q0 q1 ->
      p ≥ 3 -> p % 2 = 1 ->
      IsExactMultOrderMod p 2 d1 ->
      IsExactMultOrderMod p (ratio32Mod p) d2 ->
      Nat.gcd d1 d2 ≥ 2 ->
      p ∣ (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)) ->
      p ∣ (2 ^ a1 - 1) ->
      w1 + w2 ≥ 41 * Nat.gcd d1 d2 ∧
      w1 + a1 + w2 + a2 ≥ 65 * Nat.gcd d1 d2 := by
    intro w1 a1 w2 a2 q0 q1 p d1 d2 hprim hp3 hp_odd hd1 hd2 hr_ge2 hp_D hp_a1
    rcases two_block_shared_mersenne_common_order_scaling_and_squeeze
      w1 a1 w2 a2 q0 q1 p d1 d2 hprim hp3 hp_odd hd1 hd2 hp_D hp_a1 with
      ⟨_, _, _, hr_W, hr_K, hW_5r, _, _, _, h3v_lt_2k, hsqueeze⟩
    let r := Nat.gcd d1 d2
    let W := w1 + w2
    let K := w1 + a1 + w2 + a2
    let v := W / r
    let k := K / r
    change 3 ^ v < 2 ^ k at h3v_lt_2k
    change 23 * r * (2 ^ k - 3 ^ v) < 3 ^ v at hsqueeze
    have hv_ge5 : v ≥ 5 := by
      rcases hr_W with ⟨vw, hvw⟩
      have hv_eq : v = vw := by
        dsimp [v, W, r]; rw [hvw, Nat.mul_comm (Nat.gcd d1 d2) vw, Nat.mul_div_cancel vw (by omega)]
      have h5 : 5 * Nat.gcd d1 d2 ≤ Nat.gcd d1 d2 * vw := by rw [← hvw]; exact hW_5r
      rw [Nat.mul_comm 5 (Nat.gcd d1 d2)] at h5
      have := Nat.le_of_mul_le_mul_left h5 (by omega : 0 < Nat.gcd d1 d2)
      omega
    have h46_lt : 46 * (2 ^ k - 3 ^ v) < 3 ^ v := by
      have hm : 46 ≤ 23 * r := by change 23 * 2 ≤ 23 * r; exact Nat.mul_le_mul_left 23 hr_ge2
      exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right (2 ^ k - 3 ^ v) hm) hsqueeze
    have hv_ge41 : v ≥ 41 := by
      by_cases hle40 : v ≤ 40
      · have hge := checkAllSqueeze46UpTo_sound 40 v k squeeze46_up_to_40_cert
          (by omega) hle40 h3v_lt_2k
        omega
      · omega
    have hk_ge65 : k ≥ 65 := by
      by_cases hlt65 : k ≤ 64
      · have hp2 : 2 ^ k ≤ 2 ^ 64 := pow2_mono_nat hlt65
        have hp3 : 3 ^ 41 ≤ 3 ^ v := pow3_mono_w7 41 v hv_ge41
        have h41_64 : 2 ^ 64 ≤ 3 ^ 41 := by decide
        omega
      · omega
    rcases hr_W with ⟨vw, hvw⟩
    rcases hr_K with ⟨kw, hkw⟩
    have hv_eq : v = vw := by
      dsimp [v, W, r]; rw [hvw, Nat.mul_comm (Nat.gcd d1 d2) vw, Nat.mul_div_cancel vw (by omega)]
    have hk_eq : k = kw := by
      dsimp [k, K, r]; rw [hkw, Nat.mul_comm (Nat.gcd d1 d2) kw, Nat.mul_div_cancel kw (by omega)]
    refine ⟨?_, ?_⟩
    · rw [hvw, Nat.mul_comm 41 (Nat.gcd d1 d2)]
      exact Nat.mul_le_mul_left (Nat.gcd d1 d2) (by omega)
    · rw [hkw, Nat.mul_comm 65 (Nat.gcd d1 d2)]
      exact Nat.mul_le_mul_left (Nat.gcd d1 d2) (by omega)
  have hmod13_4 : ∀ q d2 d32 : Nat,
      IsPrimeNat q -> q % 24 = 13 ->
      IsExactMultOrderMod q 2 d2 ->
      IsExactMultOrderMod q (ratio32Mod q) d32 ->
      4 ∣ d2 ∧ 4 ∣ d32 ∧ 4 ∣ Nat.gcd d2 d32 ∧ Nat.gcd d2 d32 ≥ 4 := by
    intro q d2 d32 hq hq13 hd2 hd32
    rcases mod24_11_13_quadratic_reciprocity_and_one_block_exclusion.1 q hq (Or.inr hq13) with
      ⟨hpow2, _, hpow32, hall_ev⟩
    rcases hall_ev d2 d32 hd2 hd32 with ⟨h2_d2, h2_d32, _, _⟩
    let h := (q - 1) / 2
    let h4 := (q - 1) / 4
    have hq_ge13 : q ≥ 13 := by omega
    have hh_eq : h = 2 * h4 := by dsimp [h, h4]; omega
    have hqm1_eq : q - 1 = 4 * h4 := by dsimp [h4]; omega
    have hdiv4_of : ∀ (b d : Nat),
        ¬ (q ∣ b) -> IsExactMultOrderMod q b d -> 2 ∣ d -> b ^ h % q = q - 1 -> 4 ∣ d := by
      intro b d hnd_b hord h2d hbh
      rcases h2d with ⟨e, he⟩
      have hdvd_qm1 : d ∣ (q - 1) :=
        exactMultOrderMod_dvd_of_pow_eq_one q b d (q - 1) hord (fermat_little_mod_prime q b hq hnd_b)
      rcases hdvd_qm1 with ⟨m, hm⟩
      have he_2h4 : e ∣ (2 * h4) := by
        rw [hqm1_eq, he, Nat.mul_assoc 2 e m] at hm
        exact ⟨m, by omega⟩
      have hnot_e_h4 : ¬ (e ∣ h4) := by
        rintro ⟨c, hc⟩
        have hd_h : d ∣ h := ⟨c, by rw [hh_eq, hc, he, Nat.mul_assoc 2 e c]⟩
        rcases hd_h with ⟨c', hc'⟩
        rw [hc', ← pow_pow_eq_mul_w5 b d c',
            pow_mod_eq_of_mod_eq_w5 q (b ^ d) 1
              (by rw [hord.2.2.1, Nat.mod_eq_of_lt (by omega : 1 < q)]) c',
            Nat.one_pow, Nat.mod_eq_of_lt (by omega : 1 < q)] at hbh
        omega
      by_cases he_ev : e % 2 = 0
      · rcases Nat.dvd_of_mod_eq_zero he_ev with ⟨f, hf⟩
        exact ⟨f, by omega⟩
      · have he_odd : e % 2 = 1 := by omega
        have hgcd_e2 : Nat.gcd e 2 = 1 := by
          rw [Nat.gcd_comm, Nat.gcd_rec 2 e, he_odd]; decide
        exact False.elim (hnot_e_h4
          (coprime_dvd_of_dvd_mul_aux (e + 2) e 2 h4 (Nat.le_refl _) hgcd_e2 he_2h4))
    have hnd2 : ¬ (q ∣ 2) := by
      rintro ⟨c, hc⟩; cases c with
      | zero => simp at hc
      | succ c' => have := Nat.mul_le_mul_left q (by omega : 1 ≤ c' + 1); omega
    have hnd32 : ¬ (q ∣ ratio32Mod q) := by
      rintro ⟨c, hc⟩
      have h2r_mod : (2 * ratio32Mod q) % q = 3 := by
        unfold ratio32Mod
        have h2inv : 2 * ((q + 1) / 2) = 1 + q := by omega
        calc
          (2 * ((3 * ((q + 1) / 2)) % q)) % q
              = (2 * (3 * ((q + 1) / 2))) % q := by rw [Nat.mul_mod 2 _ q, Nat.mod_mod, ← Nat.mul_mod]
          _ = (3 * (2 * ((q + 1) / 2))) % q := by rw [← Nat.mul_assoc 2 3, Nat.mul_comm 2 3, Nat.mul_assoc]
          _ = (3 + q * 3) % q := by rw [h2inv, Nat.mul_add, Nat.mul_one, Nat.mul_comm 3 q]
          _ = 3 := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      rw [hc, ← Nat.mul_assoc 2 q c, Nat.mul_comm 2 q, Nat.mul_assoc q 2 c, Nat.mul_mod_right] at h2r_mod
      omega
    have h4_d2 := hdiv4_of 2 d2 hnd2 hd2 h2_d2 hpow2
    have h4_d32 := hdiv4_of (ratio32Mod q) d32 hnd32 hd32 h2_d32 hpow32
    have h4_g : 4 ∣ Nat.gcd d2 d32 := Nat.dvd_gcd h4_d2 h4_d32
    have hg_ge4 : Nat.gcd d2 d32 ≥ 4 := by
      rcases h4_g with ⟨k, hk⟩
      cases k with
      | zero =>
        rw [Nat.mul_zero] at hk
        have hp := Nat.gcd_pos_of_pos_left d32 hd2.2.1; omega
      | succ k' => omega
    exact ⟨h4_d2, h4_d32, h4_g, hg_ge4⟩
  refine ⟨huniv2, hmod13_4, ?_⟩
  intro w1 a1 w2 a2 q0 q1 q hprim hq hq_D hq_a1
  have h3_q_of_ev : 2 ∣ a1 -> 2 ∣ a2 -> 3 ∣ q0 ∧ 3 ∣ q1 := by
    intro h2a1 h2a2
    rcases hprim with
      ⟨hw1, _, hw2, _, _, _, _, _, _, _, _, _, _, _, hD_mod24,
       _, _, _, _, _, hbrox0, hbrox1, _⟩
    let D := 2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)
    have hgcd_3D : Nat.gcd 3 D = 1 := by
      rw [Nat.gcd_rec 3 D]
      have hD3 : D % 3 = 1 ∨ D % 3 = 2 := by
        rcases hD_mod24 with h | h | h | h <;> omega
      rcases hD3 with h1 | h2
      · rw [h1]; decide
      · rw [h2]; decide
    have h3_2a1 : 3 ∣ (2 ^ a1 - 1) := by
      rcases h2a1 with ⟨k1, hk1⟩
      have hm := pow_sub_pow_mul_dvd_w8 2 1 2 (by decide) k1
      simp only [Nat.one_pow, ← hk1] at hm; exact hm
    have h3_2a2 : 3 ∣ (2 ^ a2 - 1) := by
      rcases h2a2 with ⟨k2, hk2⟩
      have hm := pow_sub_pow_mul_dvd_w8 2 1 2 (by decide) k2
      simp only [Nat.one_pow, ← hk2] at hm; exact hm
    have h3_w2 : 3 ∣ 3 ^ w2 := ⟨3 ^ (w2 - 1), by
      conv => lhs; rw [show w2 = (w2 - 1) + 1 by omega]
      rw [Nat.pow_succ, Nat.mul_comm]⟩
    have h3_w1 : 3 ∣ 3 ^ w1 := ⟨3 ^ (w1 - 1), by
      conv => lhs; rw [show w1 = (w1 - 1) + 1 by omega]
      rw [Nat.pow_succ, Nat.mul_comm]⟩
    have h3_Dq0 : 3 ∣ (D * q0) := by
      change D * q0 = twoBlockBroxCarry w1 a1 w2 a2 at hbrox0
      rw [hbrox0]; unfold twoBlockBroxCarry
      rcases h3_w2 with ⟨c1, hc1⟩
      rcases h3_2a2 with ⟨c2, hc2⟩
      exact ⟨c1 * (2 ^ a1 - 1) + 2 ^ (a1 + w2) * c2, by
        rw [hc1, hc2, Nat.mul_add, Nat.mul_assoc 3 c1,
            ← Nat.mul_assoc (2 ^ (a1 + w2)) 3 c2, Nat.mul_comm (2 ^ (a1 + w2)) 3, Nat.mul_assoc 3]⟩
    have h3_Dq1 : 3 ∣ (D * q1) := by
      change D * q1 = twoBlockBroxCarry w2 a2 w1 a1 at hbrox1
      rw [hbrox1]; unfold twoBlockBroxCarry
      rcases h3_w1 with ⟨c1, hc1⟩
      rcases h3_2a1 with ⟨c2, hc2⟩
      exact ⟨c1 * (2 ^ a2 - 1) + 2 ^ (a2 + w1) * c2, by
        rw [hc1, hc2, Nat.mul_add, Nat.mul_assoc 3 c1,
            ← Nat.mul_assoc (2 ^ (a2 + w1)) 3 c2, Nat.mul_comm (2 ^ (a2 + w1)) 3, Nat.mul_assoc 3]⟩
    exact ⟨coprime_dvd_of_dvd_mul_aux (3 + D) 3 D q0 (Nat.le_refl _) hgcd_3D h3_Dq0,
           coprime_dvd_of_dvd_mul_aux (3 + D) 3 D q1 (Nat.le_refl _) hgcd_3D h3_Dq1⟩
  refine ⟨?_, ?_⟩
  · intro hq_mod24
    have hq11 : q ≥ 11 := by omega
    have hq_odd : q % 2 = 1 := by omega
    have hnd2 : ¬ (q ∣ 2) := by
      rintro ⟨c, hc⟩; cases c with
      | zero => simp at hc
      | succ c' => have := Nat.mul_le_mul_left q (by omega : 1 ≤ c' + 1); omega
    have hnd32 : ¬ (q ∣ ratio32Mod q) := by
      rintro ⟨c, hc⟩
      have h2inv : 2 * ((q + 1) / 2) = 1 + q := by omega
      have h2r : (2 * ratio32Mod q) % q = 3 := by
        unfold ratio32Mod
        calc
          (2 * ((3 * ((q + 1) / 2)) % q)) % q
              = (2 * (3 * ((q + 1) / 2))) % q := by rw [Nat.mul_mod 2 _ q, Nat.mod_mod, ← Nat.mul_mod]
          _ = (3 * (2 * ((q + 1) / 2))) % q := by rw [← Nat.mul_assoc 2 3, Nat.mul_comm 2 3, Nat.mul_assoc]
          _ = (3 + q * 3) % q := by rw [h2inv, Nat.mul_add, Nat.mul_one, Nat.mul_comm 3 q]
          _ = 3 := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      rw [hc, ← Nat.mul_assoc 2 q c, Nat.mul_comm 2 q, Nat.mul_assoc q 2 c, Nat.mul_mod_right] at h2r
      omega
    rcases exists_exact_mult_order_mod_prime q 2 hq hnd2 with ⟨d1, hd1, _⟩
    rcases exists_exact_mult_order_mod_prime q (ratio32Mod q) hq hnd32 with ⟨d2, hd2, _⟩
    rcases (mod24_11_13_quadratic_reciprocity_and_one_block_exclusion.1 q hq hq_mod24).2.2.2
      d1 d2 hd1 hd2 with ⟨_, _, h2_r, hr_ge2⟩
    rcases two_block_shared_mersenne_common_order_scaling_and_squeeze
      w1 a1 w2 a2 q0 q1 q d1 d2 hprim (by omega) hq_odd hd1 hd2 hq_D hq_a1 with
      ⟨_, hr_a1, hr_a2, hr_W, _, _, _, _, _, _, _⟩
    rcases huniv2 w1 a1 w2 a2 q0 q1 q d1 d2 hprim (by omega) hq_odd hd1 hd2 hr_ge2 hq_D hq_a1 with
      ⟨hW_41r, hK_65r⟩
    have h2_a1 : 2 ∣ a1 := Nat.dvd_trans h2_r hr_a1
    have h2_a2 : 2 ∣ a2 := Nat.dvd_trans h2_r hr_a2
    have h2_W  : 2 ∣ (w1 + w2) := Nat.dvd_trans h2_r hr_W
    rcases h3_q_of_ev h2_a1 h2_a2 with ⟨h3_q0, h3_q1⟩
    exact ⟨h2_a1, h2_a2, h2_W, h3_q0, h3_q1,
      Nat.le_trans (Nat.mul_le_mul_left 41 hr_ge2) hW_41r,
      Nat.le_trans (Nat.mul_le_mul_left 65 hr_ge2) hK_65r⟩
  · intro hq13
    have hq13_ge : q ≥ 13 := by omega
    have hq_odd : q % 2 = 1 := by omega
    have hnd2 : ¬ (q ∣ 2) := by
      rintro ⟨c, hc⟩; cases c with
      | zero => simp at hc
      | succ c' => have := Nat.mul_le_mul_left q (by omega : 1 ≤ c' + 1); omega
    have hnd32 : ¬ (q ∣ ratio32Mod q) := by
      rintro ⟨c, hc⟩
      have h2inv : 2 * ((q + 1) / 2) = 1 + q := by omega
      have h2r : (2 * ratio32Mod q) % q = 3 := by
        unfold ratio32Mod
        calc
          (2 * ((3 * ((q + 1) / 2)) % q)) % q
              = (2 * (3 * ((q + 1) / 2))) % q := by rw [Nat.mul_mod 2 _ q, Nat.mod_mod, ← Nat.mul_mod]
          _ = (3 * (2 * ((q + 1) / 2))) % q := by rw [← Nat.mul_assoc 2 3, Nat.mul_comm 2 3, Nat.mul_assoc]
          _ = (3 + q * 3) % q := by rw [h2inv, Nat.mul_add, Nat.mul_one, Nat.mul_comm 3 q]
          _ = 3 := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      rw [hc, ← Nat.mul_assoc 2 q c, Nat.mul_comm 2 q, Nat.mul_assoc q 2 c, Nat.mul_mod_right] at h2r
      omega
    rcases exists_exact_mult_order_mod_prime q 2 hq hnd2 with ⟨d1, hd1, _⟩
    rcases exists_exact_mult_order_mod_prime q (ratio32Mod q) hq hnd32 with ⟨d2, hd2, _⟩
    rcases hmod13_4 q d1 d2 hq hq13 hd1 hd2 with ⟨_, _, h4_r, hr_ge4⟩
    rcases two_block_shared_mersenne_common_order_scaling_and_squeeze
      w1 a1 w2 a2 q0 q1 q d1 d2 hprim (by omega) hq_odd hd1 hd2 hq_D hq_a1 with
      ⟨_, hr_a1, hr_a2, hr_W, _, _, _, _, _, _, _⟩
    rcases huniv2 w1 a1 w2 a2 q0 q1 q d1 d2 hprim (by omega) hq_odd hd1 hd2 (by omega) hq_D hq_a1 with
      ⟨hW_41r, hK_65r⟩
    exact ⟨Nat.dvd_trans h4_r hr_a1, Nat.dvd_trans h4_r hr_a2, Nat.dvd_trans h4_r hr_W,
      Nat.le_trans (Nat.mul_le_mul_left 41 hr_ge4) hW_41r,
      Nat.le_trans (Nat.mul_le_mul_left 65 hr_ge4) hK_65r⟩

-- 5C (`Branch P3.3`): Exact `(T = 5, U = 1)` Single-Base `6 x 6` Closed Form, Confluent
-- Derivative Column-Extrapolated Zero-Gap Divisibility (`(2^u - 1)^(2T - 1)`), & `6 x 6` Bridge:

theorem intDet_col_scale (coef : Int) (L : Nat) (c0 : Fin L) (B : Fin L -> Fin L -> Int) :
    intDet L (fun i j => if j = c0 then coef * B i c0 else B i j) = coef * intDet L B := by
  let Z : Fin L -> Fin L -> Int := fun i j => if j = c0 then 0 else B i j
  have hlin := intDet_col_linear coef L c0
    (fun i j => if j = c0 then coef * B i c0 else B i j) Z B
    (fun i j hj => by dsimp [Z]; simp [hj])
    (fun i => by dsimp [Z]; simp)
  have hz_dvd : (0 : Int) ∣ intDet L Z :=
    intDet_col_dvd 0 L c0 Z (fun i => ⟨0, by dsimp [Z]; simp⟩)
  rcases hz_dvd with ⟨q, hq⟩
  rw [Int.zero_mul] at hq
  rw [hlin, hq, Int.zero_add]

theorem laurentInterpBinom_succ_mul :
    ∀ (y t : Nat),
      (t + 1) * laurentInterpBinom (y + 1) (t + 1) = (y + 1) * laurentInterpBinom y t
  | 0, 0 => rfl
  | 0, _ + 1 => by simp [laurentInterpBinom]
  | y + 1, 0 => by
    rw [Nat.one_mul, laurentInterpBinom_one_right (y + 2),
        laurentInterpBinom_zero_right (y + 1), Nat.mul_one]
  | y + 1, t + 1 => by
    have ih0 := laurentInterpBinom_succ_mul y t
    have ih1 := laurentInterpBinom_succ_mul y (t + 1)
    have hrec1 : laurentInterpBinom (y + 2) (t + 2) =
        laurentInterpBinom (y + 1) (t + 1) + laurentInterpBinom (y + 1) (t + 2) := rfl
    have hrec0 : laurentInterpBinom (y + 1) (t + 1) =
        laurentInterpBinom y t + laurentInterpBinom y (t + 1) := rfl
    rw [hrec1, Nat.mul_add (t + 2),
        show (t + 2) * laurentInterpBinom (y + 1) (t + 1) =
          (t + 1) * laurentInterpBinom (y + 1) (t + 1) + laurentInterpBinom (y + 1) (t + 1) from
          Nat.succ_mul (t + 1) _,
        ih0, ih1]
    conv => rhs; rw [Nat.succ_mul (y + 1) _, hrec0, Nat.mul_add (y + 1)]
    omega

def laurentColsC51_6 (u : Nat) (j : Fin 6) : Nat × Nat :=
  match j.val with
  | 0 => (0, 0) | 1 => (1, 0) | 2 => (2, 0)
  | 3 => (3, 0) | 4 => (4, 0) | _ => (0, u)

def laurentSingleC51Mat6 (W u : Nat) : Fin 6 -> Fin 6 -> Int :=
  laurentInterpMat W 1 6 laurentRowsSingle6 (laurentColsC51_6 u)

def singleC51ScaledExprMat6 (i j : Fin 6) : Expr4 :=
  let n : Expr4 := .mul (.const (i.val : Int)) .v0
  match j.val with
  | 0 => .const 1
  | 1 => n
  | 2 => .mul n (.sub n (.const 1))
  | 3 => .mul (.mul n (.sub n (.const 1))) (.sub n (.const 2))
  | 4 => .mul (.mul (.mul n (.sub n (.const 1))) (.sub n (.const 2))) (.sub n (.const 3))
  | _ => expr4Pow .v2 i.val

def singleC51ScaledClosedExpr : Expr4 :=
  .mul (.const 288) (.mul (expr4Pow .v0 10) (expr4Pow (.sub .v2 (.const 1)) 5))

theorem singleC51_poly_identity :
    addPoly4 (poly4Det 6 (fun i j => normExpr4 (singleC51ScaledExprMat6 i j)))
      (negPoly4 (normExpr4 singleC51ScaledClosedExpr)) = [] := by decide

/--
  Theorem W10.2e (`laurent_6x6_single_base_t5u1_and_confluent_extrapolation`, `zero custom axioms`):
  1. **Exact Single-Base `6 x 6` `(T = 5, U = 1)` Closed Form**:
     For ALL `W ≥ 1, u ≥ 1`, `intDet 6 (laurentSingleC51Mat6 W u) = W ^ 10 * (2 ^ u - 1) ^ 5 > 0`!
  2. **Universal `L x L` Confluent Derivative-Block Binomial-Taylor Extrapolation Divisibility**:
     For ALL `W K L T u : Nat` (`T ≥ 1, u ≥ 1`), `rows cols : Fin L -> Nat × Nat`, polynomial columns
     `idx : Nat -> Fin L` (`∀ t < T, cols (idx t) = (t, 0)`), and distinct confluent columns
     `c0 ≠ c1` with `cols c0 = (0, u)` and `cols c1 = (1, u)`:
       - First-derivative column `c1` alone yields `((2 ^ u * (2 ^ u - 1) ^ (T - 1) : Nat) : Int) ∣ intDet L M0`;
       - Joint confluent block `(c0, c1)` yields **`((2 ^ u * (2 ^ u - 1) ^ (2 * T - 1) : Nat) : Int) ∣ intDet L M0`**!
  3. **`6 x 6` Two-Base $W$-Dilated Zero-Gap Congruence & Convergent-Cone Non-Vanishing Bridge**:
     For ALL `W, K, u ≥ 1` with `3 ^ W < 2 ^ K` and `3 * K ≤ 5 * W`, setting `M0_tb6` on
     `laurentRowsTwoBase6 × laurentColsC23_6 u`:
       `((2 ^ K - 3 ^ W : Nat) : Int) ∣ (intDet 6 M0_tb6 - intDet 6 (laurentTwoBaseMat6 W K (W * u)))` ∧
       `((2 ^ u * (2 ^ u - 1) ^ 3 : Nat) : Int) ∣ intDet 6 M0_tb6` ∧
       `intDet 6 (laurentTwoBaseMat6 W K (W * u)) ≠ 0` ∧
       `(W * u ≥ 3 -> intDet 6 (laurentTwoBaseMat6 W K (W * u)) > 0)`!
-/
theorem laurent_6x6_single_base_t5u1_and_confluent_extrapolation :
    (∀ W u : Nat, W ≥ 1 -> u ≥ 1 ->
      intDet 6 (laurentSingleC51Mat6 W u) =
        ((W ^ 10 * (2 ^ u - 1) ^ 5 : Nat) : Int) ∧
      intDet 6 (laurentSingleC51Mat6 W u) > 0) ∧
    (∀ (W K L T u : Nat) (rows cols : Fin L -> Nat × Nat)
       (idx : Nat -> Fin L) (c1 : Fin L),
      T ≥ 1 -> u ≥ 1 ->
      (∀ t : Nat, 1 ≤ t -> t < T -> cols (idx t) = (t, 0)) ->
      cols c1 = (1, u) ->
      let M0 : Fin L -> Fin L -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2 (cols j).1 (cols j).2 : Int)
      ((2 ^ u * (2 ^ u - 1) ^ (T - 1) : Nat) : Int) ∣ intDet L M0) ∧
    (∀ (W K L T u : Nat) (rows cols : Fin L -> Nat × Nat)
       (idx : Nat -> Fin L) (c0 c1 : Fin L),
      T ≥ 1 -> u ≥ 1 -> c0 ≠ c1 ->
      (∀ t : Nat, t < T -> cols (idx t) = (t, 0)) ->
      cols c0 = (0, u) -> cols c1 = (1, u) ->
      let M0 : Fin L -> Fin L -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2 (cols j).1 (cols j).2 : Int)
      ((2 ^ u * (2 ^ u - 1) ^ (2 * T - 1) : Nat) : Int) ∣ intDet L M0) ∧
    (∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 -> u ≥ 1 -> 3 ^ W < 2 ^ K -> 3 * K ≤ 5 * W ->
      let M0_tb6 : Fin 6 -> Fin 6 -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (laurentRowsTwoBase6 i).1 (laurentRowsTwoBase6 i).2
          (laurentColsC23_6 u j).1 (laurentColsC23_6 u j).2 : Int)
      (((2 ^ K - 3 ^ W : Nat) : Int) ∣
        (intDet 6 M0_tb6 - intDet 6 (laurentTwoBaseMat6 W K (W * u)))) ∧
      (((2 ^ u * (2 ^ u - 1) ^ 3 : Nat) : Int) ∣ intDet 6 M0_tb6) ∧
      intDet 6 (laurentTwoBaseMat6 W K (W * u)) ≠ 0 ∧
      (W * u ≥ 3 -> intDet 6 (laurentTwoBaseMat6 W K (W * u)) > 0)) := by
  have hintPow_cast : ∀ (n k : Nat), intPowNat (n : Int) k = ((n ^ k : Nat) : Int) := by
    intro n k; induction k with
    | zero => rfl
    | succ k' ih => simp only [intPowNat, ih, Nat.pow_succ, Nat.mul_comm (n ^ k') n, natCast_mul]
  have hexprPow_eval : ∀ (x0 x1 x2 x3 : Int) (e : Expr4) (k : Nat),
      evalExpr4 x0 x1 x2 x3 (expr4Pow e k) = intPowNat (evalExpr4 x0 x1 x2 x3 e) k := by
    intro x0 x1 x2 x3 e k; induction k with
    | zero => rfl
    | succ k' ih => simp [expr4Pow, evalExpr4, intPowNat, ih]
  -- Helper falling-factorial identities for `laurentInterpBinom n 2..4`:
  have hb2 : ∀ n : Nat, 2 * laurentInterpBinom n 2 = n * (n - 1) := by
    intro n; induction n with
    | zero => rfl
    | succ m ih =>
      change 2 * (laurentInterpBinom m 1 + laurentInterpBinom m 2) = (m + 1) * m
      rw [Nat.mul_add 2, laurentInterpBinom_one_right m, ih]
      cases m with
      | zero => rfl
      | succ m' =>
        change 2 * (m' + 1) + (m' + 1) * m' = (m' + 2) * (m' + 1)
        rw [Nat.mul_comm (m' + 1) m', ← Nat.add_mul 2 m' (m' + 1), Nat.add_comm 2 m']
  have hb3 : ∀ n : Nat, 6 * laurentInterpBinom n 3 = n * (n - 1) * (n - 2) := by
    intro n; induction n with
    | zero => rfl
    | succ m ih =>
      change 6 * (laurentInterpBinom m 2 + laurentInterpBinom m 3) = (m + 1) * m * (m - 1)
      rw [Nat.mul_add 6, show 6 * laurentInterpBinom m 2 = 3 * (2 * laurentInterpBinom m 2) by omega,
          hb2 m, ih]
      cases m with
      | zero => rfl
      | succ m1 =>
        cases m1 with
        | zero => rfl
        | succ m2 =>
          change 3 * ((m2 + 2) * (m2 + 1)) + (m2 + 2) * (m2 + 1) * m2 =
            (m2 + 3) * (m2 + 2) * (m2 + 1)
          rw [Nat.mul_assoc (m2 + 3) (m2 + 2) (m2 + 1)]
          generalize (m2 + 2) * (m2 + 1) = P
          rw [Nat.add_mul m2 3 P, Nat.mul_comm m2 P]
          omega
  have hb4 : ∀ n : Nat, 24 * laurentInterpBinom n 4 = n * (n - 1) * (n - 2) * (n - 3) := by
    intro n; induction n with
    | zero => rfl
    | succ m ih =>
      change 24 * (laurentInterpBinom m 3 + laurentInterpBinom m 4) =
        (m + 1) * m * (m - 1) * (m - 2)
      rw [Nat.mul_add 24,
          show 24 * laurentInterpBinom m 3 = 4 * (6 * laurentInterpBinom m 3) by omega,
          hb3 m, ih]
      cases m with
      | zero => rfl
      | succ m1 =>
        cases m1 with
        | zero => rfl
        | succ m2 =>
          cases m2 with
          | zero => rfl
          | succ m3 =>
            change 4 * ((m3 + 3) * (m3 + 2) * (m3 + 1)) +
              (m3 + 3) * (m3 + 2) * (m3 + 1) * m3 =
              (m3 + 4) * (m3 + 3) * (m3 + 2) * (m3 + 1)
            have hassoc : (m3 + 4) * (m3 + 3) * (m3 + 2) * (m3 + 1) =
                (m3 + 4) * ((m3 + 3) * (m3 + 2) * (m3 + 1)) := by
              rw [Nat.mul_assoc (m3 + 4) (m3 + 3) (m3 + 2),
                  Nat.mul_assoc (m3 + 4) ((m3 + 3) * (m3 + 2)) (m3 + 1)]
            rw [hassoc]
            generalize (m3 + 3) * (m3 + 2) * (m3 + 1) = Q
            rw [Nat.add_mul m3 4 Q, Nat.mul_comm m3 Q]
            omega
  have hpos_nz : ∀ n : Nat, n ≥ 1 -> Int.ofNat n ≠ 0 := by
    intro n hn; change (n : Int) ≠ 0; omega
  -- Reusable column `(1, u)` remainder lemma on ANY matrix agreeing with `M0` on `idx 1..T-1` and `c1`:
  have hcol1_rem : ∀ (W K L T u : Nat) (rows cols : Fin L -> Nat × Nat)
      (idx : Nat -> Fin L) (c1 : Fin L) (A : Fin L -> Fin L -> Int),
      T ≥ 1 -> u ≥ 1 ->
      (∀ t : Nat, 1 ≤ t -> t < T -> cols (idx t) = (t, 0)) ->
      cols c1 = (1, u) ->
      (∀ i : Fin L, A i c1 =
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2 1 u : Int)) ->
      (∀ (i : Fin L) (t : Nat), 1 ≤ t -> t < T -> A i (idx t) =
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2 t 0 : Int)) ->
      ((2 ^ u * (2 ^ u - 1) ^ (T - 1) : Nat) : Int) ∣ intDet L A := by
    intro W K L T u rows cols idx c1 A _ hu hpoly1 hexp1 hA_c1 hA_idx
    let B : Nat := 2 ^ u - 1
    have h2u_ge2 : 2 ^ u ≥ 2 := by simpa using pow2_mono_nat hu
    have h1B : 1 + B = 2 ^ u := by dsimp [B]; omega
    let idx' : Nat -> Fin L := fun t => idx (t + 1)
    let coef' : Nat -> Int := fun t => Int.ofNat (2 ^ u * (t + 1) * B ^ t)
    have hne_all : ∀ t : Nat, t < T - 1 -> idx' t ≠ c1 := by
      intro t ht heq
      have hc := hpoly1 (t + 1) (by omega) (by omega)
      dsimp [idx'] at heq
      rw [heq, hexp1] at hc
      injection hc with _ hu0; omega
    rw [intDet_sub_col_prefix_invariant L c1 A (T - 1) idx' coef' hne_all]
    have hcast_dvd : ((2 ^ u * B ^ (T - 1) : Nat) : Int) = Int.ofNat (2 ^ u * B ^ (T - 1)) := by
      simp only [Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_pow]
    apply intDet_col_dvd (((2 ^ u * B ^ (T - 1) : Nat) : Int)) L c1
    intro i
    simp only [ite_true]
    let x := (rows i).1 * W + (rows i).2 * K
    cases hx : x with
    | zero =>
      have hAc1_0 : A i c1 = 0 := by
        rw [hA_c1 i]; unfold laurentZeroGapIntEntry
        change ((laurentInterpBinom x 1 * 2 ^ (x * u) : Nat) : Int) = 0
        rw [hx]; simp [laurentInterpBinom]
      have hcomb_0 : ∀ m : Nat, m ≤ T - 1 -> colPrefixComb A idx' coef' i m = 0 := by
        intro m hm; induction m with
        | zero => rfl
        | succ m' ihm =>
          unfold colPrefixComb; rw [ihm (by omega)]
          have hAi : A i (idx' m') = 0 := by
            dsimp [idx']; rw [hA_idx i (m' + 1) (by omega) (by omega)]
            unfold laurentZeroGapIntEntry
            change ((laurentInterpBinom x (m' + 1) * 2 ^ (x * 0) : Nat) : Int) = 0
            rw [hx]; simp [laurentInterpBinom]
          rw [hAi, Int.mul_zero, Int.add_zero]
      rw [hAc1_0, hcomb_0 (T - 1) (Nat.le_refl _)]; exact ⟨0, by simp⟩
    | succ y =>
      have hAc1_y : A i c1 = Int.ofNat (2 ^ u * (y + 1) * (1 + B) ^ y) := by
        rw [hA_c1 i]; unfold laurentZeroGapIntEntry
        apply congrArg Int.ofNat
        change laurentInterpBinom x 1 * 2 ^ (x * u) = 2 ^ u * (y + 1) * (1 + B) ^ y
        rw [hx, laurentInterpBinom_one_right (y + 1), Nat.succ_mul y u, Nat.pow_add 2 (y * u) u,
            Nat.mul_comm y u, ← pow_pow_eq_mul_w5 2 u y, h1B]
        rw [← Nat.mul_assoc (y + 1) ((2 ^ u) ^ y) (2 ^ u),
            Nat.mul_comm ((y + 1) * (2 ^ u) ^ y) (2 ^ u), Nat.mul_assoc]
      have hcomb_y : ∀ m : Nat, m ≤ T - 1 ->
          colPrefixComb A idx' coef' i m =
            Int.ofNat (2 ^ u * (y + 1) * binomTaylorSum y B m) := by
        intro m hm; induction m with
        | zero => simp [colPrefixComb, binomTaylorSum]
        | succ m' ihm =>
          unfold colPrefixComb binomTaylorSum
          rw [ihm (by omega)]
          have hAi : A i (idx' m') = Int.ofNat (laurentInterpBinom (y + 1) (m' + 1)) := by
            dsimp [idx']; rw [hA_idx i (m' + 1) (by omega) (by omega)]
            unfold laurentZeroGapIntEntry
            apply congrArg Int.ofNat
            change laurentInterpBinom x (m' + 1) * 2 ^ (x * 0) = _
            rw [hx, Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
          rw [hAi]; dsimp only [coef']
          have hstep_nat : 2 ^ u * (y + 1) * binomTaylorSum y B m' +
              (2 ^ u * (m' + 1) * B ^ m') * laurentInterpBinom (y + 1) (m' + 1) =
              2 ^ u * (y + 1) * (binomTaylorSum y B m' + laurentInterpBinom y m' * B ^ m') := by
            rw [Nat.mul_add (2 ^ u * (y + 1))]
            apply congrArg (2 ^ u * (y + 1) * binomTaylorSum y B m' + ·)
            have habs := laurentInterpBinom_succ_mul y m'
            calc
              2 ^ u * (m' + 1) * B ^ m' * laurentInterpBinom (y + 1) (m' + 1)
                  = 2 ^ u * ((m' + 1) * laurentInterpBinom (y + 1) (m' + 1)) * B ^ m' := by
                    rw [Nat.mul_assoc (2 ^ u * (m' + 1)), Nat.mul_comm (B ^ m'),
                        ← Nat.mul_assoc (2 ^ u * (m' + 1)), Nat.mul_assoc (2 ^ u) (m' + 1)]
              _ = 2 ^ u * (y + 1) * (laurentInterpBinom y m' * B ^ m') := by
                    rw [habs, ← Nat.mul_assoc (2 ^ u) (y + 1), Nat.mul_assoc (2 ^ u * (y + 1))]
          simp only [Int.ofNat_eq_natCast, ← Int.natCast_mul, ← Int.natCast_add, hstep_nat]
      rw [hAc1_y, hcomb_y (T - 1) (Nat.le_refl _)]
      rcases binomTaylorSum_remainder_dvd y B (T - 1) with ⟨hle_r, qr, hqr⟩
      have hle_m : 2 ^ u * (y + 1) * binomTaylorSum y B (T - 1) ≤ 2 ^ u * (y + 1) * (1 + B) ^ y :=
        Nat.mul_le_mul_left _ hle_r
      have hrem_nat : 2 ^ u * (y + 1) * (1 + B) ^ y - 2 ^ u * (y + 1) * binomTaylorSum y B (T - 1) =
          (2 ^ u * B ^ (T - 1)) * ((y + 1) * qr) := by
        rw [← Nat.mul_sub_left_distrib, hqr, ← Nat.mul_assoc (2 ^ u * (y + 1)),
            Nat.mul_assoc (2 ^ u) (y + 1) (B ^ (T - 1)),
            Nat.mul_comm (y + 1) (B ^ (T - 1)), ← Nat.mul_assoc (2 ^ u) (B ^ (T - 1)),
            Nat.mul_assoc (2 ^ u * B ^ (T - 1))]
      refine ⟨Int.ofNat ((y + 1) * qr), ?_⟩
      rw [hcast_dvd]
      simp only [Int.ofNat_eq_natCast, ← Int.natCast_sub hle_m, ← Int.natCast_mul, hrem_nat]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Part 1: Exact `(T = 5, U = 1)` `6 x 6` Single-Base Closed Form:
    intro W u hW hu
    let P := 2 ^ u
    have hP_ge2 : P ≥ 2 := by dsimp [P]; simpa using pow2_mono_nat hu
    let A0 := laurentSingleC51Mat6 W u
    let c2 : Fin 6 := ⟨2, by decide⟩
    let c3 : Fin 6 := ⟨3, by decide⟩
    let c4 : Fin 6 := ⟨4, by decide⟩
    let A1 : Fin 6 -> Fin 6 -> Int := fun i j => if j = c2 then 2 * A0 i c2 else A0 i j
    let A2 : Fin 6 -> Fin 6 -> Int := fun i j => if j = c3 then 6 * A1 i c3 else A1 i j
    let A3 : Fin 6 -> Fin 6 -> Int := fun i j => if j = c4 then 24 * A2 i c4 else A2 i j
    have hs1 : intDet 6 A1 = 2 * intDet 6 A0 := intDet_col_scale 2 6 c2 A0
    have hs2 : intDet 6 A2 = 6 * intDet 6 A1 := intDet_col_scale 6 6 c3 A1
    have hs3 : intDet 6 A3 = 24 * intDet 6 A2 := intDet_col_scale 24 6 c4 A2
    have h288 : intDet 6 A3 = 288 * intDet 6 A0 := by rw [hs3, hs2, hs1]; omega
    have hpoly := poly4Det_eq_of_sub_nil singleC51ScaledExprMat6 singleC51ScaledClosedExpr
      singleC51_poly_identity (W : Int) 0 (P : Int) 0
    have hmat_eq : A3 = (fun i j => evalExpr4 (W : Int) 0 (P : Int) 0 (singleC51ScaledExprMat6 i j)) := by
      funext i j
      let n := i.val * W
      have hn_cast : ((i.val : Int) * (W : Int)) = (n : Int) := (Int.natCast_mul i.val W).symm
      have hj_cases : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5 := by
        have := j.isLt; omega
      rcases hj_cases with hj0 | hj1 | hj2 | hj3 | hj4 | hj5
      · have hjf : j = ⟨0, by decide⟩ := Fin.ext hj0
        subst hjf
        change laurentSingleC51Mat6 W u i ⟨0, by decide⟩ = 1
        unfold laurentSingleC51Mat6 laurentInterpMat laurentRowsSingle6
        rw [show laurentColsC51_6 u ⟨0, by decide⟩ = (0, 0) from rfl]
        unfold laurentInterpEntry
        simp [laurentInterpBinom_zero_right]
      · have hjf : j = ⟨1, by decide⟩ := Fin.ext hj1
        subst hjf
        change laurentSingleC51Mat6 W u i ⟨1, by decide⟩ = (i.val : Int) * (W : Int)
        unfold laurentSingleC51Mat6 laurentInterpMat laurentRowsSingle6
        rw [show laurentColsC51_6 u ⟨1, by decide⟩ = (1, 0) from rfl]
        unfold laurentInterpEntry
        simp [laurentInterpBinom_one_right]
      · have hjf : j = ⟨2, by decide⟩ := Fin.ext hj2
        subst hjf
        change 2 * laurentSingleC51Mat6 W u i ⟨2, by decide⟩ =
          ((i.val : Int) * (W : Int)) * (((i.val : Int) * (W : Int)) - 1)
        unfold laurentSingleC51Mat6 laurentInterpMat laurentRowsSingle6
        rw [show laurentColsC51_6 u ⟨2, by decide⟩ = (2, 0) from rfl]
        unfold laurentInterpEntry; dsimp only
        rw [Nat.add_zero, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.mul_one, hn_cast,
            show i.val * W = n from rfl, show (2 : Int) = ((2 : Nat) : Int) from rfl,
            ← Int.natCast_mul, hb2 n]
        cases n with
        | zero => rfl
        | succ m => rw [Int.natCast_mul]; congr 1; omega
      · have hjf : j = ⟨3, by decide⟩ := Fin.ext hj3
        subst hjf
        change 6 * laurentSingleC51Mat6 W u i ⟨3, by decide⟩ =
          (((i.val : Int) * (W : Int)) * (((i.val : Int) * (W : Int)) - 1)) *
            (((i.val : Int) * (W : Int)) - 2)
        unfold laurentSingleC51Mat6 laurentInterpMat laurentRowsSingle6
        rw [show laurentColsC51_6 u ⟨3, by decide⟩ = (3, 0) from rfl]
        unfold laurentInterpEntry; dsimp only
        rw [Nat.add_zero, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.mul_one, hn_cast,
            show i.val * W = n from rfl, show (6 : Int) = ((6 : Nat) : Int) from rfl,
            ← Int.natCast_mul, hb3 n]
        cases n with
        | zero => rfl
        | succ m1 =>
          cases m1 with
          | zero => rfl
          | succ m2 =>
            rw [Int.natCast_mul, Int.natCast_mul]
            congr 1
            · congr 1; omega
            · omega
      · have hjf : j = ⟨4, by decide⟩ := Fin.ext hj4
        subst hjf
        change 24 * laurentSingleC51Mat6 W u i ⟨4, by decide⟩ =
          ((((i.val : Int) * (W : Int)) * (((i.val : Int) * (W : Int)) - 1)) *
            (((i.val : Int) * (W : Int)) - 2)) * (((i.val : Int) * (W : Int)) - 3)
        unfold laurentSingleC51Mat6 laurentInterpMat laurentRowsSingle6
        rw [show laurentColsC51_6 u ⟨4, by decide⟩ = (4, 0) from rfl]
        unfold laurentInterpEntry; dsimp only
        rw [Nat.add_zero, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.mul_one, hn_cast,
            show i.val * W = n from rfl, show (24 : Int) = ((24 : Nat) : Int) from rfl,
            ← Int.natCast_mul, hb4 n]
        cases n with
        | zero => rfl
        | succ m1 =>
          cases m1 with
          | zero => rfl
          | succ m2 =>
            cases m2 with
            | zero => rfl
            | succ m3 =>
              rw [Int.natCast_mul, Int.natCast_mul, Int.natCast_mul]
              congr 1
              · congr 1
                · congr 1; omega
                · omega
              · omega
      · have hjf : j = ⟨5, by decide⟩ := Fin.ext hj5
        subst hjf
        change laurentSingleC51Mat6 W u i ⟨5, by decide⟩ =
          evalExpr4 (W : Int) 0 (P : Int) 0 (expr4Pow .v2 i.val)
        rw [hexprPow_eval, show evalExpr4 (W : Int) 0 (P : Int) 0 .v2 = (P : Int) from rfl, hintPow_cast]
        unfold laurentSingleC51Mat6 laurentInterpMat laurentRowsSingle6
        rw [show laurentColsC51_6 u ⟨5, by decide⟩ = (0, u) from rfl]
        unfold laurentInterpEntry; dsimp only
        rw [Nat.add_zero, laurentInterpBinom_zero_right, Nat.one_mul, Nat.zero_mul, Nat.pow_zero,
            Nat.mul_one, Nat.mul_comm i.val u, ← pow_pow_eq_mul_w5 2 u i.val]
    rw [← hmat_eq, h288] at hpoly
    unfold singleC51ScaledClosedExpr at hpoly
    simp only [evalExpr4, hexprPow_eval, hintPow_cast] at hpoly
    have hp_sub : ((P : Int) - 1) = ((P - 1 : Nat) : Int) := by omega
    rw [hp_sub, hintPow_cast] at hpoly
    let targetNat := W ^ 10 * (P - 1) ^ 5
    have hrhs_eq : (288 : Int) * (((W ^ 10 : Nat) : Int) * (((P - 1) ^ 5 : Nat) : Int)) =
        288 * Int.ofNat targetNat := by
      dsimp only [targetNat]
      simp only [Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_pow]
    rw [hrhs_eq] at hpoly
    have hdet_ofNat : intDet 6 A0 = Int.ofNat targetNat := by
      generalize Int.ofNat targetNat = T_int at hpoly ⊢
      omega
    have hpos_nat : targetNat ≥ 1 :=
      Nat.mul_le_mul (nat_pow_pos_of_pos W hW 10) (nat_pow_pos_of_pos (P - 1) (by omega) 5)
    have hdet_pos : intDet 6 A0 > 0 := by
      rw [hdet_ofNat]
      change (targetNat : Int) > 0
      omega
    have hdet_eq : intDet 6 A0 = ((W ^ 10 * (2 ^ u - 1) ^ 5 : Nat) : Int) := by
      rw [hdet_ofNat]
      dsimp only [targetNat, P]
      simp only [Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_pow]
    exact ⟨hdet_eq, hdet_pos⟩
  · -- Part 2: First-derivative column `c1 = (1, u)` divisibility:
    intro W K L T u rows cols idx c1 hT1 hu hpoly1 hexp1
    dsimp only
    let M0 : Fin L -> Fin L -> Int := fun i j =>
      (laurentZeroGapIntEntry W K (rows i).1 (rows i).2 (cols j).1 (cols j).2 : Int)
    exact hcol1_rem W K L T u rows cols idx c1 M0 hT1 hu hpoly1 hexp1
      (fun i => by dsimp [M0]; rw [hexp1])
      (fun i t ht1 htT => by dsimp [M0]; rw [hpoly1 t ht1 htT])
  · -- Part 3: Joint confluent block `c0 = (0, u), c1 = (1, u)` (`(2^u - 1)^(2T - 1)`):
    intro W K L T u rows cols idx c0 c1 hT1 hu hne_c hpoly hexp0 hexp1
    dsimp only
    let M0 : Fin L -> Fin L -> Int := fun i j =>
      (laurentZeroGapIntEntry W K (rows i).1 (rows i).2 (cols j).1 (cols j).2 : Int)
    let B : Nat := 2 ^ u - 1
    have h2u_ge2 : 2 ^ u ≥ 2 := by simpa using pow2_mono_nat hu
    have h1B : 1 + B = 2 ^ u := by dsimp [B]; omega
    have hne_c0 : ∀ t : Nat, t < T -> idx t ≠ c0 := by
      intro t ht heq
      have hc := hpoly t ht
      rw [heq, hexp0] at hc
      injection hc with _ hu0; omega
    let coef0 : Nat -> Int := fun t => Int.ofNat (B ^ t)
    rw [intDet_sub_col_prefix_invariant L c0 M0 T idx coef0 hne_c0]
    let M0_sub : Fin L -> Fin L -> Int := fun i j =>
      if j = c0 then M0 i c0 - colPrefixComb M0 idx coef0 i T else M0 i j
    let D0 : Int := Int.ofNat (B ^ T)
    have hdiv_c0 : ∀ i : Fin L, D0 ∣ M0_sub i c0 := by
      intro i
      dsimp only [M0_sub]; simp only [ite_true]
      let x := (rows i).1 * W + (rows i).2 * K
      have hM0_i : M0 i c0 = Int.ofNat ((1 + B) ^ x) := by
        dsimp only [M0]; rw [hexp0]; unfold laurentZeroGapIntEntry
        apply congrArg Int.ofNat
        change laurentInterpBinom x 0 * 2 ^ (x * u) = (1 + B) ^ x
        rw [laurentInterpBinom_zero_right, Nat.one_mul, Nat.mul_comm x u,
            ← pow_pow_eq_mul_w5 2 u x, h1B]
      have hcomb_i : ∀ m : Nat, m ≤ T ->
          colPrefixComb M0 idx coef0 i m = Int.ofNat (binomTaylorSum x B m) := by
        intro m hm; induction m with
        | zero => rfl
        | succ m' ihm =>
          unfold colPrefixComb binomTaylorSum; rw [ihm (by omega)]
          have hm0_t : M0 i (idx m') = Int.ofNat (laurentInterpBinom x m') := by
            dsimp only [M0]; rw [hpoly m' (by omega)]; unfold laurentZeroGapIntEntry
            apply congrArg Int.ofNat
            change laurentInterpBinom x m' * 2 ^ (x * 0) = _
            rw [Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
          rw [hm0_t]; dsimp only [coef0]
          simp only [Int.ofNat_eq_natCast, ← Int.natCast_mul, ← Int.natCast_add, Nat.mul_comm (B ^ m')]
      rw [hM0_i, hcomb_i T (Nat.le_refl T)]
      rcases binomTaylorSum_remainder_dvd x B T with ⟨hle_r, qr, hqr⟩
      refine ⟨Int.ofNat qr, ?_⟩
      dsimp only [D0]
      simp only [Int.ofNat_eq_natCast, ← Int.natCast_sub hle_r, ← Int.natCast_mul, hqr]
    have hBT_pos : B ^ T ≥ 1 := nat_pow_pos_of_pos B (by dsimp [B]; omega) T
    have hD0_nz : D0 ≠ 0 := hpos_nz (B ^ T) hBT_pos
    let Q_mat : Fin L -> Fin L -> Int := fun i j =>
      if j = c0 then M0_sub i c0 / D0 else M0_sub i j
    have hscale_eq : M0_sub = (fun i j => if j = c0 then D0 * Q_mat i c0 else Q_mat i j) := by
      funext i j
      by_cases hj : j = c0
      · subst hj; dsimp only [Q_mat]; simp only [ite_true]
        rcases hdiv_c0 i with ⟨qi, hqi⟩
        rw [hqi, Int.mul_comm D0 qi, Int.mul_ediv_cancel qi hD0_nz, Int.mul_comm]
      · dsimp only [Q_mat]; simp only [hj, ite_false]
    change ((2 ^ u * (2 ^ u - 1) ^ (2 * T - 1) : Nat) : Int) ∣ intDet L M0_sub
    rw [hscale_eq, intDet_col_scale D0 L c0 Q_mat]
    have hQ_c1 : ∀ i : Fin L, Q_mat i c1 =
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2 1 u : Int) := by
      intro i
      have hc1_ne : c1 ≠ c0 := Ne.symm hne_c
      dsimp only [Q_mat, M0_sub]; simp only [hc1_ne, ite_false]; dsimp only [M0]; rw [hexp1]
    have hQ_idx : ∀ (i : Fin L) (t : Nat), 1 ≤ t -> t < T -> Q_mat i (idx t) =
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2 t 0 : Int) := by
      intro i t _ htT
      have hne_t : idx t ≠ c0 := hne_c0 t htT
      dsimp only [Q_mat, M0_sub]; simp only [hne_t, ite_false]; dsimp only [M0]; rw [hpoly t htT]
    rcases hcol1_rem W K L T u rows cols idx c1 Q_mat hT1 hu
      (fun t _ htT => hpoly t htT) hexp1 hQ_c1 hQ_idx with ⟨q2, hq2⟩
    rw [hq2]
    refine ⟨q2, ?_⟩
    have hpow_comb : B ^ T * (2 ^ u * B ^ (T - 1)) = 2 ^ u * B ^ (2 * T - 1) := by
      rw [← Nat.mul_assoc (B ^ T) (2 ^ u), Nat.mul_comm (B ^ T) (2 ^ u), Nat.mul_assoc,
          ← Nat.pow_add B T (T - 1), show T + (T - 1) = 2 * T - 1 by omega]
    have hp_int := congrArg (fun n : Nat => (n : Int)) hpow_comb
    simp only [D0, B, Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_pow] at hp_int ⊢
    rw [← Int.mul_assoc, hp_int]
  · -- Part 4: `6 x 6` Two-Base $W$-Dilated Congruence + `(2^u * (2^u - 1)^3)` Divisibility + Cone Non-Vanishing:
    intro W K u hW hK hu hgt hcone
    dsimp only
    have hdvd_diff := (laurent_wdilated_zero_gap_entry_and_det_congruence.2
      W K 6 laurentRowsTwoBase6 (laurentColsC23_6 u) hgt).1
    have hMW_eq : (fun i j : Fin 6 =>
        (laurentInterpEntry W K (laurentRowsTwoBase6 i).1 (laurentRowsTwoBase6 i).2
          (laurentColsC23_6 u j).1 (W * (laurentColsC23_6 u j).2) : Int)) =
        laurentTwoBaseMat6 W K (W * u) := by
      funext i j
      unfold laurentTwoBaseMat6 laurentInterpMat laurentColsC23_6
      have hj_c : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5 := by
        have := j.isLt; omega
      rcases hj_c with h0 | h1 | h2 | h3 | h4 | h5
      · simp [h0]
      · simp [h1]
      · simp [h2]
      · simp [h3]
      · simp only [h4]
        have hm2 : W * (2 * u) = 2 * (W * u) := by
          rw [← Nat.mul_assoc W 2 u, Nat.mul_comm W 2, Nat.mul_assoc]
        rw [hm2]
      · simp only [h5]
        have hm2 : W * (2 * u) = 2 * (W * u) := by
          rw [← Nat.mul_assoc W 2 u, Nat.mul_comm W 2, Nat.mul_assoc]
        rw [hm2]
    rw [hMW_eq] at hdvd_diff
    let idx6 : Nat -> Fin 6 := fun t => if h : t < 6 then ⟨t, h⟩ else ⟨0, by decide⟩
    have hpoly6 : ∀ t : Nat, t < 2 -> laurentColsC23_6 u (idx6 t) = (t, 0) := by
      intro t ht
      have ht_c : t = 0 ∨ t = 1 := by omega
      rcases ht_c with rfl | rfl <;> rfl
    let M0_tb6 : Fin 6 -> Fin 6 -> Int := fun i j =>
      (laurentZeroGapIntEntry W K (laurentRowsTwoBase6 i).1 (laurentRowsTwoBase6 i).2
        (laurentColsC23_6 u j).1 (laurentColsC23_6 u j).2 : Int)
    let c0_6 : Fin 6 := ⟨2, by decide⟩
    let c1_6 : Fin 6 := ⟨3, by decide⟩
    let h_part3 : ((2 ^ u * (2 ^ u - 1) ^ (2 * 2 - 1) : Nat) : Int) ∣ intDet 6 M0_tb6 := by
      let B : Nat := 2 ^ u - 1
      have h2u_ge2 : 2 ^ u ≥ 2 := by simpa using pow2_mono_nat hu
      have h1B : 1 + B = 2 ^ u := by dsimp [B]; omega
      have hne_c0_6 : ∀ t : Nat, t < 2 -> idx6 t ≠ c0_6 := by
        intro t ht; have : t = 0 ∨ t = 1 := by omega
        rcases this with rfl | rfl <;> decide
      let coef0 : Nat -> Int := fun t => Int.ofNat (B ^ t)
      rw [intDet_sub_col_prefix_invariant 6 c0_6 M0_tb6 2 idx6 coef0 hne_c0_6]
      let M0_sub6 : Fin 6 -> Fin 6 -> Int := fun i j =>
        if j = c0_6 then M0_tb6 i c0_6 - colPrefixComb M0_tb6 idx6 coef0 i 2 else M0_tb6 i j
      let D2 : Int := Int.ofNat (B ^ 2)
      have hdiv_c0_6 : ∀ i : Fin 6, D2 ∣ M0_sub6 i c0_6 := by
        intro i
        change D2 ∣ M0_tb6 i c0_6 - colPrefixComb M0_tb6 idx6 coef0 i 2
        let x := (laurentRowsTwoBase6 i).1 * W + (laurentRowsTwoBase6 i).2 * K
        have hM0_i : M0_tb6 i c0_6 = Int.ofNat ((1 + B) ^ x) := by
          dsimp only [M0_tb6, c0_6]
          rw [show laurentColsC23_6 u ⟨2, by decide⟩ = (0, u) from rfl]
          unfold laurentZeroGapIntEntry
          apply congrArg Int.ofNat
          change laurentInterpBinom x 0 * 2 ^ (x * u) = (1 + B) ^ x
          rw [laurentInterpBinom_zero_right, Nat.one_mul, Nat.mul_comm x u,
              ← pow_pow_eq_mul_w5 2 u x, h1B]
        have hcomb_i : colPrefixComb M0_tb6 idx6 coef0 i 2 = Int.ofNat (binomTaylorSum x B 2) := by
          change (0 + coef0 0 * M0_tb6 i (idx6 0)) + coef0 1 * M0_tb6 i (idx6 1) =
            Int.ofNat ((0 + laurentInterpBinom x 0 * B ^ 0) + laurentInterpBinom x 1 * B ^ 1)
          have hm0 : M0_tb6 i (idx6 0) = Int.ofNat (laurentInterpBinom x 0) := by
            change (laurentZeroGapIntEntry W K (laurentRowsTwoBase6 i).1 (laurentRowsTwoBase6 i).2 0 0 : Int) = _
            unfold laurentZeroGapIntEntry
            apply congrArg Int.ofNat
            change laurentInterpBinom x 0 * 2 ^ (x * 0) = _
            rw [Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
          have hm1 : M0_tb6 i (idx6 1) = Int.ofNat (laurentInterpBinom x 1) := by
            change (laurentZeroGapIntEntry W K (laurentRowsTwoBase6 i).1 (laurentRowsTwoBase6 i).2 1 0 : Int) = _
            unfold laurentZeroGapIntEntry
            apply congrArg Int.ofNat
            change laurentInterpBinom x 1 * 2 ^ (x * 0) = _
            rw [Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
          rw [hm0, hm1]; dsimp only [coef0]
          simp only [Int.zero_add, Nat.zero_add, Int.ofNat_eq_natCast,
                     ← Int.natCast_mul, ← Int.natCast_add,
                     Nat.mul_comm (B ^ 0), Nat.mul_comm (B ^ 1)]
        rw [hM0_i, hcomb_i]
        rcases binomTaylorSum_remainder_dvd x B 2 with ⟨hle_r, qr, hqr⟩
        refine ⟨Int.ofNat qr, ?_⟩
        dsimp only [D2]
        simp only [Int.ofNat_eq_natCast, ← Int.natCast_sub hle_r, ← Int.natCast_mul, hqr]
      have hD2_nz : D2 ≠ 0 := hpos_nz (B ^ 2) (nat_pow_pos_of_pos B (by dsimp [B]; omega) 2)
      let Q6 : Fin 6 -> Fin 6 -> Int := fun i j =>
        if j = c0_6 then M0_sub6 i c0_6 / D2 else M0_sub6 i j
      have hscale6 : M0_sub6 = (fun i j => if j = c0_6 then D2 * Q6 i c0_6 else Q6 i j) := by
        funext i j
        by_cases hj : j = c0_6
        · subst hj
          change M0_sub6 i c0_6 = D2 * (M0_sub6 i c0_6 / D2)
          rcases hdiv_c0_6 i with ⟨qi, hqi⟩
          rw [hqi, Int.mul_comm D2 qi, Int.mul_ediv_cancel qi hD2_nz, Int.mul_comm]
        · dsimp only [Q6]; simp only [hj, ite_false]
      change ((2 ^ u * (2 ^ u - 1) ^ (2 * 2 - 1) : Nat) : Int) ∣ intDet 6 M0_sub6
      rw [hscale6, intDet_col_scale D2 6 c0_6 Q6]
      rcases hcol1_rem W K 6 2 u laurentRowsTwoBase6 (laurentColsC23_6 u) idx6 c1_6 Q6
        (by decide) hu (fun t _ ht => hpoly6 t ht) rfl
        (fun _ => rfl)
        (fun _ t ht1 ht2 => by
          have ht_eq : t = 1 := by omega
          subst ht_eq
          rfl) with ⟨q2, hq2⟩
      rw [hq2]
      refine ⟨q2, ?_⟩
      have hpow3 : B ^ 2 * (2 ^ u * B ^ 1) = 2 ^ u * B ^ 3 := by
        rw [← Nat.mul_assoc (B ^ 2) (2 ^ u), Nat.mul_comm (B ^ 2) (2 ^ u), Nat.mul_assoc,
            ← Nat.pow_add B 2 1]
      have hp_int := congrArg (fun n : Nat => (n : Int)) hpow3
      simp only [D2, B, Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_pow] at hp_int ⊢
      rw [← Int.mul_assoc, hp_int]
    rcases laurent_6x6_exact_factorization_and_zero_locus.2.2.2.2 W K (W * u)
      hW hK hcone (Nat.mul_le_mul hW hu) with ⟨hnz_Wu, hpos_Wu⟩
    exact ⟨hdvd_diff, h_part3, hnz_Wu, hpos_Wu⟩

-- 5D (`Branch P1.2`): Alternating `01`-Cascade Fibonacci Law on `sternDiatomic` &
-- Non-Regular `(zeroBitCount - oneBitCount)` `zeroExcessOCN` / `0`-Incrementing `OCN` Impossibility:

def natFib : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => natFib n + natFib (n + 1)

/--
  Theorem W10.3d (`stern_alternating_01_cascade_fib`, choice-free `zero custom axioms`):
  Exact Exponential Fibonacci Law for `sternDiatomic` Along Alternating `01`-Cascades:
  For ALL `e ≥ 1`, `a_e := (4 ^ e - 1) / 3` (`1, 5, 21, 85, 341, ...`, binary `1010...1_2`) satisfies
  `sternDiatomic ((4 ^ e - 1) / 3) = natFib (2 * e)` and
  `sternDiatomic ((4 ^ e - 1) / 3 + 1) = natFib (2 * e - 1)`!
-/
theorem stern_alternating_01_cascade_fib :
    sternDiatomic 0 = natFib 0 ∧
    ∀ e : Nat, e ≥ 1 ->
      sternDiatomic ((4 ^ e - 1) / 3) = natFib (2 * e) ∧
      sternDiatomic ((4 ^ e - 1) / 3 + 1) = natFib (2 * e - 1) := by
  have hdiv3 : ∀ e : Nat, 3 * ((4 ^ e - 1) / 3) = 4 ^ e - 1 := by
    intro e; induction e with
    | zero => rfl
    | succ e' ih =>
      have hp := nat_pow_pos_of_pos 4 (by decide) e'
      have hsp : 4 ^ (e' + 1) - 1 = 3 * 4 ^ e' + (4 ^ e' - 1) := by
        rw [Nat.pow_succ 4 e']; omega
      rw [hsp]
      omega
  refine ⟨rfl, ?_⟩
  intro e
  induction e with
  | zero => intro he; omega
  | succ e' ih =>
    intro _
    cases e' with
    | zero => exact ⟨by decide, by decide⟩
    | succ m =>
      rcases ih (by omega) with ⟨ih_a, ih_a1⟩
      let a := (4 ^ (m + 1) - 1) / 3
      change sternDiatomic a = natFib (2 * (m + 1)) at ih_a
      change sternDiatomic (a + 1) = natFib (2 * (m + 1) - 1) at ih_a1
      rw [show 2 * (m + 1) = 2 * m + 2 by omega] at ih_a ih_a1
      rw [show 2 * m + 2 - 1 = 2 * m + 1 by omega] at ih_a1
      have ha_step : (4 ^ (m + 2) - 1) / 3 = 4 * a + 1 := by
        have h3a := hdiv3 (m + 1)
        have h3b := hdiv3 (m + 2)
        have hp : 4 ^ (m + 2) = 4 ^ (m + 1) * 4 := Nat.pow_succ 4 (m + 1)
        have h3eq : 3 * ((4 ^ (m + 2) - 1) / 3) = 3 * (4 * a + 1) := by
          rw [h3b, hp, Nat.mul_add 3 (4 * a) 1, ← Nat.mul_assoc 3 4 a,
              Nat.mul_comm 3 4, Nat.mul_assoc 4 3 a]
          dsimp [a]
          rw [h3a]
          have hp4 := nat_pow_pos_of_pos 4 (by decide) (m + 1)
          omega
        omega
      rw [ha_step]
      have hf3 : natFib (2 * m + 2) + natFib (2 * m + 1) = natFib (2 * m + 3) := by
        have hdef : natFib ((2 * m + 1) + 2) = natFib (2 * m + 1) + natFib (2 * m + 2) := rfl
        rw [show 2 * m + 3 = (2 * m + 1) + 2 by omega, hdef, Nat.add_comm]
      have hs_succ : sternDiatomic (4 * a + 1 + 1) = natFib (2 * m + 3) := by
        rw [show 4 * a + 1 + 1 = 2 * (2 * a + 1) by omega,
            sternDiatomic_even (2 * a + 1),
            sternDiatomic_odd a, ih_a, ih_a1]
        exact hf3
      have hs_cur : sternDiatomic (4 * a + 1) = natFib (2 * m + 4) := by
        rw [show 4 * a + 1 = 2 * (2 * a) + 1 by omega,
            sternDiatomic_odd (2 * a),
            sternDiatomic_even a,
            sternDiatomic_odd a, ih_a, ih_a1, hf3]
        have hdef : natFib ((2 * m + 2) + 2) = natFib (2 * m + 2) + natFib (2 * m + 3) := rfl
        rw [show 2 * m + 4 = (2 * m + 2) + 2 by omega, hdef]
      have hg1 : 2 * (m + 2) = 2 * m + 4 := by omega
      have hg2 : 2 * (m + 2) - 1 = 2 * m + 3 := by omega
      rw [hg2, hg1]
      exact ⟨hs_cur, hs_succ⟩

/-- Canonical `Q = 1` non-regular zero-excess `OCN` (`c` increments on `0`, decrements on `1` above `0`, tracking floor-clamped `(zeroBitCount - oneBitCount)`). -/
def zeroExcessOCNZero : Fin 1 -> Bool -> Fin 1 × CounterOp :=
  fun q b => (q, if b then .stay else .inc)

def zeroExcessOCNPos : Fin 1 -> Bool -> Fin 1 × CounterOp :=
  fun q b => (q, if b then .dec else .inc)

theorem zeroExcessOCN_exact_1_0j_1m_formula (j m : Nat) :
    (runMSBOneCounterOCN 1 zeroExcessOCNZero zeroExcessOCNPos ⟨0, by decide⟩
      (2 ^ (j + m) + (2 ^ m - 1))).2 = j - m := by
  have hsp : 2 ^ (j + m) + (2 ^ m - 1) = 2 ^ m * (2 ^ j * 1) + (2 ^ m - 1) := by
    rw [Nat.mul_one, Nat.pow_add 2 j m, Nat.mul_comm (2 ^ j) (2 ^ m)]
  rw [hsp,
      runMSBOneCounterOCN_mersenne_tail zeroExcessOCNZero zeroExcessOCNPos ⟨0, by decide⟩
        (2 ^ j * 1) (by rw [Nat.mul_one]; exact pow2_pos_nat j) m,
      runMSBOneCounterOCN_mul_pow2 zeroExcessOCNZero zeroExcessOCNPos ⟨0, by decide⟩ 1 (by decide) j]
  have hbase : runMSBOneCounterOCN 1 zeroExcessOCNZero zeroExcessOCNPos ⟨0, by decide⟩ 1 =
      (⟨0, by decide⟩, 0) := by decide
  rw [hbase]
  have hz_run : ∀ d : Nat,
      (iterOCN0 zeroExcessOCNZero zeroExcessOCNPos d (⟨0, by decide⟩, 0)).2 = d := by
    intro d; induction d with
    | zero => rfl
    | succ d' ih =>
      simp only [iterOCN0]
      let cur := iterOCN0 zeroExcessOCNZero zeroExcessOCNPos d' (⟨0, by decide⟩, 0)
      change cur.2 = d' at ih
      change (stepOCN zeroExcessOCNZero zeroExcessOCNPos cur false).2 = d' + 1
      unfold stepOCN zeroExcessOCNZero zeroExcessOCNPos applyCounterOp
      by_cases hc0 : cur.2 = 0
      · rw [ite_true_of_w10 hc0]; simp only [Bool.false_eq_true, ite_false]; omega
      · rw [ite_false_of_w10 hc0]; simp only [Bool.false_eq_true, ite_false]; omega
  let after0 := iterOCN0 zeroExcessOCNZero zeroExcessOCNPos j (⟨0, by decide⟩, 0)
  have ha0 : after0.2 = j := hz_run j
  suffices hiter1 : ∀ r : Nat,
      (iterOCN1 zeroExcessOCNZero zeroExcessOCNPos r after0).2 = j - r from hiter1 m
  intro r
  induction r with
  | zero => dsimp [iterOCN1]; rw [ha0]
  | succ m' ih =>
    simp only [iterOCN1]
    let cur1 := iterOCN1 zeroExcessOCNZero zeroExcessOCNPos m' after0
    change cur1.2 = j - m' at ih
    change (stepOCN zeroExcessOCNZero zeroExcessOCNPos cur1 true).2 = j - (m' + 1)
    unfold stepOCN zeroExcessOCNZero zeroExcessOCNPos applyCounterOp
    by_cases hc0 : cur1.2 = 0
    · rw [ite_true_of_w10 hc0]; simp only [ite_true]; omega
    · rw [ite_false_of_w10 hc0]; simp only [ite_true]; omega

/--
  Theorem W10.3e (`zero_excess_ocn_and_zero_inc_preimage_impossibility`, `zero custom axioms`):
  Strict Non-Regularity of `(zeroBitCount - oneBitCount)` `zeroExcessOCN` & Universal `∀ Q ≥ 1`
  Unbounded `0`-Incrementing `OCN` Preimage Weight Impossibility (`Branch P1.2`):
  1. **Strict Non-Regularity of `zeroExcessOCN`**: Across ALL `k ≥ 1`, `zeroExcessOCN` separates
     `1 0^k 1^(k-1)_2` (`c = 1`) from `1 0^(k-1) 1^(k-1)_2` (`c = 0`), while `c(13) = 0`,
     `c(56) = 3`, and `c(224) = 5`.
  2. **Universal Unbounded `0`-Incrementing `OCN` Impossibility (`∀ Q ≥ 1`)**: For EVERY `Q ≥ 1`
     and EVERY zero-testing `OCN` `(deltaZero, deltaPos)` whose `0`-transitions increment the counter
     (`∀ q, (deltaZero q false).2 = .inc ∧ (deltaPos q false).2 = .inc`, directly covering `zeroExcessOCN`!),
     along the interior-zero-block Collatz family `ms = 3 * 2 ^ s + 2` (`ms % 3 = 2`), `2 * ms`, and
     `ns = (2 * ms - 1) / 3 = 2 ^ (s + 1) + 1`, all three preimage/target coordinates `(c(n), binBitLength(n))`
     cluster inside `[X, X + C]`, refuting ALL `NatPoly2` preimage weights!
-/
theorem zero_excess_ocn_and_zero_inc_preimage_impossibility :
    ((∀ k : Nat, k ≥ 1 ->
        (runMSBOneCounterOCN 1 zeroExcessOCNZero zeroExcessOCNPos ⟨0, by decide⟩
          (2 ^ (2 * k - 1) + (2 ^ (k - 1) - 1))).2 = 1 ∧
        (runMSBOneCounterOCN 1 zeroExcessOCNZero zeroExcessOCNPos ⟨0, by decide⟩
          (2 ^ (2 * k - 2) + (2 ^ (k - 1) - 1))).2 = 0) ∧
     (runMSBOneCounterOCN 1 zeroExcessOCNZero zeroExcessOCNPos ⟨0, by decide⟩ 13).2 = 0 ∧
     (runMSBOneCounterOCN 1 zeroExcessOCNZero zeroExcessOCNPos ⟨0, by decide⟩ 56).2 = 3 ∧
     (runMSBOneCounterOCN 1 zeroExcessOCNZero zeroExcessOCNPos ⟨0, by decide⟩ 224).2 = 5) ∧
    (∀ (Q : Nat) (_hQ : Q ≥ 1)
       (deltaZero deltaPos : Fin Q -> Bool -> Fin Q × CounterOp)
       (q0 : Fin Q)
       (_hinc0 : ∀ q : Fin Q, (deltaZero q false).2 = .inc ∧ (deltaPos q false).2 = .inc)
       (pTerms qTerms : NatPoly2)
       (pTheta qTheta : Nat),
      ¬ IsPositiveRationalPreimageWeight
        (fun n =>
          evalNatPoly2 pTerms (runMSBOneCounterOCN Q deltaZero deltaPos q0 n).2 (binBitLength n))
        (fun n =>
          evalNatPoly2 qTerms (runMSBOneCounterOCN Q deltaZero deltaPos q0 n).2 (binBitLength n))
        pTheta qTheta) := by
  refine ⟨⟨?_, by decide, by decide, by decide⟩, ?_⟩
  · intro k hk
    have h1 := zeroExcessOCN_exact_1_0j_1m_formula k (k - 1)
    have h2 := zeroExcessOCN_exact_1_0j_1m_formula (k - 1) (k - 1)
    rw [show k + (k - 1) = 2 * k - 1 by omega] at h1
    rw [show (k - 1) + (k - 1) = 2 * k - 2 by omega] at h2
    exact ⟨by rw [h1]; omega, by rw [h2]; omega⟩
  · intro Q _ deltaZero deltaPos q0 hinc0 pTerms qTerms pTheta qTheta hw
    have hiter0_inc : ∀ (d : Nat) (cfg : Fin Q × Nat),
        (iterOCN0 deltaZero deltaPos d cfg).2 = cfg.2 + d := by
      intro d; induction d with
      | zero => intro _; simp [iterOCN0]
      | succ d' ih =>
        intro cfg
        simp only [iterOCN0]
        let cur := iterOCN0 deltaZero deltaPos d' cfg
        have ih_c : cur.2 = cfg.2 + d' := ih cfg
        change (stepOCN deltaZero deltaPos cur false).2 = cfg.2 + (d' + 1)
        unfold stepOCN applyCounterOp
        by_cases hc0 : cur.2 = 0
        · rw [ite_true_of_w10 hc0, (hinc0 cur.1).1]; dsimp only; omega
        · rw [ite_false_of_w10 hc0, (hinc0 cur.1).2]; dsimp only; omega
    have hstep_true_bounds : ∀ cfg : Fin Q × Nat,
        cfg.2 - 1 ≤ (stepOCN deltaZero deltaPos cfg true).2 ∧
        (stepOCN deltaZero deltaPos cfg true).2 ≤ cfg.2 + 1 := by
      intro cfg
      unfold stepOCN
      by_cases hc0 : cfg.2 = 0
      · rw [ite_true_of_w10 hc0]
        cases (deltaZero cfg.1 true).2 <;> simp only [applyCounterOp] <;> omega
      · rw [ite_false_of_w10 hc0]
        cases (deltaPos cfg.1 true).2 <;> simp only [applyCounterOp] <;> omega
    have hstep_false_inc : ∀ cfg : Fin Q × Nat,
        (stepOCN deltaZero deltaPos cfg false).2 = cfg.2 + 1 := by
      intro cfg
      unfold stepOCN applyCounterOp
      by_cases hc0 : cfg.2 = 0
      · rw [ite_true_of_w10 hc0, (hinc0 cfg.1).1]; dsimp only; omega
      · rw [ite_false_of_w10 hc0, (hinc0 cfg.1).2]
    let c1 := (runMSBOneCounterOCN Q deltaZero deltaPos q0 1).2
    let c3 := (runMSBOneCounterOCN Q deltaZero deltaPos q0 3).2
    let dP := maxDegNatPoly2 pTerms
    let dQ := maxDegNatPoly2 qTerms
    let D := dP + dQ
    let C := c1 + c3 + 6
    have hC_pos : C ≥ 1 := by dsimp [C]; omega
    let X := 3 * (D * C + 1) + 2
    have hX_ge : X ≥ (1 + 1 + 1) * (D * C + 1) := by dsimp [X]; omega
    have hX_pos : X ≥ 5 := by dsimp [X]; omega
    let s := X + 2
    have hs_ge2 : s ≥ 2 := by dsimp [s, X]; omega
    let ms0 := 3 * 2 ^ s + 2
    let evs0 := 2 * ms0
    let ns0 := 2 ^ (s + 1) + 1
    have hp2s_ge4 : 2 ^ s ≥ 4 := by simpa using pow2_mono_nat hs_ge2
    have hms0_ge3 : ms0 ≥ 3 := by dsimp [ms0]; omega
    have hevs0_ge3 : evs0 ≥ 3 := by dsimp [evs0]; omega
    have hns0_ge3 : ns0 ≥ 3 := by dsimp [ns0]; rw [Nat.pow_succ 2 s]; omega
    have hms0_mod3 : ms0 % 3 = 2 := by
      dsimp [ms0]; rw [Nat.add_comm, Nat.mul_comm 3 (2 ^ s), Nat.add_mul_mod_self_right]
    have hns0_div : (2 * ms0 - 1) / 3 = ns0 := by
      dsimp [ms0, ns0]
      rw [Nat.pow_succ 2 s]
      generalize 2 ^ s = p2 at hp2s_ge4 ⊢
      omega
    have hc_ns0 : X ≤ (runMSBOneCounterOCN Q deltaZero deltaPos q0 ns0).2 ∧
        (runMSBOneCounterOCN Q deltaZero deltaPos q0 ns0).2 ≤ X + C := by
      have hns_rw : ns0 = 2 * (2 ^ s * 1) + 1 := by
        dsimp [ns0]; rw [Nat.mul_one, Nat.pow_succ 2 s, Nat.mul_comm (2 ^ s) 2]
      rw [hns_rw,
          runMSBOneCounterOCN_step_pos deltaZero deltaPos q0 (2 * (2 ^ s * 1) + 1)
            (by rw [Nat.mul_one]; have := pow2_pos_nat s; omega),
          show ((2 * (2 ^ s * 1) + 1) % 2 == 1) = true by
            rw [Nat.add_comm, Nat.add_mul_mod_self_left]; rfl,
          show (2 * (2 ^ s * 1) + 1) / 2 = 2 ^ s * 1 by omega,
          runMSBOneCounterOCN_mul_pow2 deltaZero deltaPos q0 1 (by decide) s]
      let cfg_z := iterOCN0 deltaZero deltaPos s (runMSBOneCounterOCN Q deltaZero deltaPos q0 1)
      change X ≤ (stepOCN deltaZero deltaPos cfg_z true).2 ∧
             (stepOCN deltaZero deltaPos cfg_z true).2 ≤ X + C
      have hcz : cfg_z.2 = c1 + s := hiter0_inc s _
      rcases hstep_true_bounds cfg_z with ⟨hlo, hhi⟩
      dsimp [s, C] at hcz ⊢
      omega
    let half_m := 2 * (2 ^ X * 3) + 1
    have hhm_pos : half_m ≥ 1 := by dsimp [half_m]; omega
    have hms0_rw : ms0 = 2 * half_m := by
      dsimp [ms0, half_m, s]
      rw [Nat.pow_succ 2 (X + 1), Nat.pow_succ 2 X]
      generalize 2 ^ X = p2
      omega
    have hc_hm : c3 + X - 1 ≤ (runMSBOneCounterOCN Q deltaZero deltaPos q0 half_m).2 ∧
        (runMSBOneCounterOCN Q deltaZero deltaPos q0 half_m).2 ≤ c3 + X + 1 := by
      dsimp [half_m]
      rw [runMSBOneCounterOCN_step_pos deltaZero deltaPos q0 (2 * (2 ^ X * 3) + 1)
            (by have := pow2_pos_nat X; omega),
          show ((2 * (2 ^ X * 3) + 1) % 2 == 1) = true by
            rw [Nat.add_comm, Nat.add_mul_mod_self_left]; rfl,
          show (2 * (2 ^ X * 3) + 1) / 2 = 2 ^ X * 3 by omega,
          runMSBOneCounterOCN_mul_pow2 deltaZero deltaPos q0 3 (by decide) X]
      let cfg_z3 := iterOCN0 deltaZero deltaPos X
        (runMSBOneCounterOCN Q deltaZero deltaPos q0 3)
      change c3 + X - 1 ≤ (stepOCN deltaZero deltaPos cfg_z3 true).2 ∧
             (stepOCN deltaZero deltaPos cfg_z3 true).2 ≤ c3 + X + 1
      have hcz3 : cfg_z3.2 = c3 + X := hiter0_inc X _
      rcases hstep_true_bounds cfg_z3 with ⟨hlo, hhi⟩
      omega
    have hc_ms0_step : (runMSBOneCounterOCN Q deltaZero deltaPos q0 ms0).2 =
        (runMSBOneCounterOCN Q deltaZero deltaPos q0 half_m).2 + 1 := by
      conv => lhs; rw [hms0_rw]
      rw [runMSBOneCounterOCN_step_pos deltaZero deltaPos q0 (2 * half_m) (by omega),
          show ((2 * half_m) % 2 == 1) = false by rw [Nat.mul_mod_right]; rfl,
          show (2 * half_m) / 2 = half_m by omega,
          hstep_false_inc]
    have hc_evs0_step : (runMSBOneCounterOCN Q deltaZero deltaPos q0 evs0).2 =
        (runMSBOneCounterOCN Q deltaZero deltaPos q0 ms0).2 + 1 := by
      dsimp [evs0]
      rw [runMSBOneCounterOCN_step_pos deltaZero deltaPos q0 (2 * ms0) (by omega),
          show ((2 * ms0) % 2 == 1) = false by rw [Nat.mul_mod_right]; rfl,
          show (2 * ms0) / 2 = ms0 by omega,
          hstep_false_inc]
    -- Exact `binBitLength` on `ns0`, `ms0`, `evs0`:
    have hbl_ns0 : binBitLength ns0 = s + 2 := by
      apply binBitLength_of_pow2_sandwich (s + 1) ns0
      · dsimp [ns0]; omega
      · dsimp [ns0]; rw [Nat.pow_succ 2 (s + 1), Nat.pow_succ 2 s]
        generalize 2 ^ s = p2 at hp2s_ge4 ⊢; omega
    have hbl_ms0 : binBitLength ms0 = s + 2 := by
      apply binBitLength_of_pow2_sandwich (s + 1) ms0
      · dsimp [ms0]; rw [Nat.pow_succ 2 s]
        generalize 2 ^ s = p2 at hp2s_ge4 ⊢; omega
      · dsimp [ms0]; rw [Nat.pow_succ 2 (s + 1), Nat.pow_succ 2 s]
        generalize 2 ^ s = p2 at hp2s_ge4 ⊢; omega
    have hbl_evs0 : binBitLength evs0 = s + 3 := by
      apply binBitLength_of_pow2_sandwich (s + 2) evs0
      · dsimp [evs0, ms0]; rw [Nat.pow_succ 2 (s + 1), Nat.pow_succ 2 s]
        generalize 2 ^ s = p2 at hp2s_ge4 ⊢; omega
      · dsimp [evs0, ms0]; rw [Nat.pow_succ 2 (s + 2), Nat.pow_succ 2 (s + 1), Nat.pow_succ 2 s]
        generalize 2 ^ s = p2 at hp2s_ge4 ⊢; omega
    rcases hc_hm with ⟨hhm_lo, hhm_hi⟩
    have hb_m : X ≤ (runMSBOneCounterOCN Q deltaZero deltaPos q0 ms0).2 ∧
                (runMSBOneCounterOCN Q deltaZero deltaPos q0 ms0).2 ≤ X + C ∧
                X ≤ binBitLength ms0 ∧ binBitLength ms0 ≤ X + C := by
      rw [hc_ms0_step, hbl_ms0]; dsimp [s, C] at hhm_lo hhm_hi ⊢
      exact ⟨by omega, by omega, by omega, by omega⟩
    have hb_ev : X ≤ (runMSBOneCounterOCN Q deltaZero deltaPos q0 evs0).2 ∧
                 (runMSBOneCounterOCN Q deltaZero deltaPos q0 evs0).2 ≤ X + C ∧
                 X ≤ binBitLength evs0 ∧ binBitLength evs0 ≤ X + C := by
      rw [hc_evs0_step, hc_ms0_step, hbl_evs0]; dsimp [s, C] at hhm_lo hhm_hi ⊢
      exact ⟨by omega, by omega, by omega, by omega⟩
    have hb_n : X ≤ (runMSBOneCounterOCN Q deltaZero deltaPos q0 ns0).2 ∧
                (runMSBOneCounterOCN Q deltaZero deltaPos q0 ns0).2 ≤ X + C ∧
                X ≤ binBitLength ns0 ∧ binBitLength ns0 ≤ X + C := by
      rw [hbl_ns0]; dsimp [s, C]
      exact ⟨hc_ns0.1, hc_ns0.2, by omega, by omega⟩
    have hpre := hw.2.2.2.2 ms0 hms0_ge3 hms0_mod3
    dsimp only at hpre
    rw [hns0_div] at hpre
    have hcanc := nat_mul_le_cancel_left_w5 qTheta _ _
      (Nat.lt_of_lt_of_le hw.1 hw.2.1)
      (Nat.le_trans hpre (Nat.mul_le_mul_right _ hw.2.1))
    let P_m := evalNatPoly2 pTerms (runMSBOneCounterOCN Q deltaZero deltaPos q0 ms0).2 (binBitLength ms0)
    let Q_m := evalNatPoly2 qTerms (runMSBOneCounterOCN Q deltaZero deltaPos q0 ms0).2 (binBitLength ms0)
    let P_ev := evalNatPoly2 pTerms (runMSBOneCounterOCN Q deltaZero deltaPos q0 evs0).2 (binBitLength evs0)
    let Q_ev := evalNatPoly2 qTerms (runMSBOneCounterOCN Q deltaZero deltaPos q0 evs0).2 (binBitLength evs0)
    let P_n := evalNatPoly2 pTerms (runMSBOneCounterOCN Q deltaZero deltaPos q0 ns0).2 (binBitLength ns0)
    let Q_n := evalNatPoly2 qTerms (runMSBOneCounterOCN Q deltaZero deltaPos q0 ns0).2 (binBitLength ns0)
    change (P_ev * Q_n + P_n * Q_ev) * Q_m ≤ P_m * (Q_ev * Q_n) at hcanc
    have hPm_pos : P_m ≥ 1 := (hw.2.2.1 ms0 hms0_ge3).1
    have hQev_pos : Q_ev ≥ 1 := (hw.2.2.1 evs0 hevs0_ge3).2
    have hQn_pos : Q_n ≥ 1 := (hw.2.2.1 ns0 hns0_ge3).2
    have hpoly2_sand : ∀ (F : NatPoly2) (z1 L1 z2 L2 : Nat),
        X ≤ z1 -> z1 ≤ X + C -> X ≤ L1 -> L1 ≤ X + C ->
        X ≤ z2 -> z2 ≤ X + C -> X ≤ L2 -> L2 ≤ X + C ->
        X ^ (maxDegNatPoly2 F) * evalNatPoly2 F z1 L1 ≤
          (X + C) ^ (maxDegNatPoly2 F) * evalNatPoly2 F z2 L2 := by
      intro F z1 L1 z2 L2 _ hz1_hi _ hL1_hi hz2_lo _ hL2_lo _
      rcases evalNatPoly2_to_3_eq F z1 L1 with ⟨he1, hd1⟩
      rcases evalNatPoly2_to_3_eq F z2 L2 with ⟨he2, _⟩
      rw [he1, he2, hd1]
      apply evalNatPoly3_cross_ratio_bound _ X (X + C) z1 L1 1 z2 L2 1 (by omega)
      · exact Nat.le_trans (Nat.mul_le_mul_left X hz1_hi)
          (by rw [Nat.mul_comm X (X + C)]; exact Nat.mul_le_mul_left (X + C) hz2_lo)
      · exact Nat.le_trans (Nat.mul_le_mul_left X hL1_hi)
          (by rw [Nat.mul_comm X (X + C)]; exact Nat.mul_le_mul_left (X + C) hL2_lo)
      · omega
    have hPm_Pev := hpoly2_sand pTerms _ _ _ _ hb_m.1 hb_m.2.1 hb_m.2.2.1 hb_m.2.2.2
      hb_ev.1 hb_ev.2.1 hb_ev.2.2.1 hb_ev.2.2.2
    have hQev_Qm := hpoly2_sand qTerms _ _ _ _ hb_ev.1 hb_ev.2.1 hb_ev.2.2.1 hb_ev.2.2.2
      hb_m.1 hb_m.2.1 hb_m.2.2.1 hb_m.2.2.2
    have hPm_Pn := hpoly2_sand pTerms _ _ _ _ hb_m.1 hb_m.2.1 hb_m.2.2.1 hb_m.2.2.2
      hb_n.1 hb_n.2.1 hb_n.2.2.1 hb_n.2.2.2
    have hQn_Qm := hpoly2_sand qTerms _ _ _ _ hb_n.1 hb_n.2.1 hb_n.2.2.1 hb_n.2.2.2
      hb_m.1 hb_m.2.1 hb_m.2.2.1 hb_m.2.2.2
    let K_den := P_m * (Q_ev * Q_n)
    have hK_pos : K_den ≥ 1 := Nat.mul_le_mul hPm_pos (Nat.mul_le_mul hQev_pos hQn_pos)
    have hbr1 : X ^ D * K_den ≤ (X + C) ^ D * ((P_ev * Q_n) * Q_m) := by
      have hm := Nat.mul_le_mul_right Q_n (Nat.mul_le_mul hPm_Pev hQev_Qm)
      have hl : (X ^ dP * P_m * (X ^ dQ * Q_ev)) * Q_n = X ^ D * K_den := by
        dsimp [D, K_den]
        rw [Nat.pow_add X dP dQ, ← Nat.mul_assoc (X ^ dP * P_m),
            Nat.mul_assoc (X ^ dP) P_m (X ^ dQ), Nat.mul_comm P_m (X ^ dQ),
            ← Nat.mul_assoc (X ^ dP) (X ^ dQ) P_m,
            Nat.mul_assoc (X ^ dP * X ^ dQ) P_m Q_ev,
            Nat.mul_assoc (X ^ dP * X ^ dQ), Nat.mul_assoc P_m Q_ev Q_n]
      have hr : ((X + C) ^ dP * P_ev * ((X + C) ^ dQ * Q_m)) * Q_n =
          (X + C) ^ D * ((P_ev * Q_n) * Q_m) := by
        dsimp [D]
        rw [Nat.pow_add (X + C) dP dQ, ← Nat.mul_assoc ((X + C) ^ dP * P_ev),
            Nat.mul_assoc ((X + C) ^ dP) P_ev ((X + C) ^ dQ),
            Nat.mul_comm P_ev ((X + C) ^ dQ),
            ← Nat.mul_assoc ((X + C) ^ dP) ((X + C) ^ dQ) P_ev,
            Nat.mul_assoc ((X + C) ^ dP * (X + C) ^ dQ) P_ev Q_m,
            Nat.mul_assoc ((X + C) ^ dP * (X + C) ^ dQ),
            Nat.mul_assoc P_ev Q_m Q_n, Nat.mul_comm Q_m Q_n, ← Nat.mul_assoc P_ev Q_n Q_m]
      rwa [hl, hr] at hm
    have hbr2 : X ^ D * K_den ≤ (X + C) ^ D * ((P_n * Q_ev) * Q_m) := by
      have hm := Nat.mul_le_mul_right Q_ev (Nat.mul_le_mul hPm_Pn hQn_Qm)
      have hl : (X ^ dP * P_m * (X ^ dQ * Q_n)) * Q_ev = X ^ D * K_den := by
        dsimp [D, K_den]
        rw [Nat.pow_add X dP dQ, ← Nat.mul_assoc (X ^ dP * P_m),
            Nat.mul_assoc (X ^ dP) P_m (X ^ dQ), Nat.mul_comm P_m (X ^ dQ),
            ← Nat.mul_assoc (X ^ dP) (X ^ dQ) P_m,
            Nat.mul_assoc (X ^ dP * X ^ dQ) P_m Q_n,
            Nat.mul_assoc (X ^ dP * X ^ dQ), Nat.mul_assoc P_m Q_n Q_ev, Nat.mul_comm Q_n Q_ev]
      have hr : ((X + C) ^ dP * P_n * ((X + C) ^ dQ * Q_m)) * Q_ev =
          (X + C) ^ D * ((P_n * Q_ev) * Q_m) := by
        dsimp [D]
        rw [Nat.pow_add (X + C) dP dQ, ← Nat.mul_assoc ((X + C) ^ dP * P_n),
            Nat.mul_assoc ((X + C) ^ dP) P_n ((X + C) ^ dQ),
            Nat.mul_comm P_n ((X + C) ^ dQ),
            ← Nat.mul_assoc ((X + C) ^ dP) ((X + C) ^ dQ) P_n,
            Nat.mul_assoc ((X + C) ^ dP * (X + C) ^ dQ) P_n Q_m,
            Nat.mul_assoc ((X + C) ^ dP * (X + C) ^ dQ),
            Nat.mul_assoc P_n Q_m Q_ev, Nat.mul_comm Q_m Q_ev, ← Nat.mul_assoc P_n Q_ev Q_m]
      rwa [hl, hr] at hm
    have hsum := Nat.add_le_add hbr1 hbr2
    rw [← Nat.two_mul (X ^ D * K_den), ← Nat.mul_assoc 2 (X ^ D) K_den,
        ← Nat.mul_add ((X + C) ^ D),
        ← Nat.add_mul (P_ev * Q_n) (P_n * Q_ev) Q_m] at hsum
    have htot : ((1 + 1) * X ^ D) * K_den ≤ (1 * (X + C) ^ D) * K_den := by
      rw [Nat.one_mul]
      exact Nat.le_trans hsum (Nat.mul_le_mul_left ((X + C) ^ D) hcanc)
    have hle_b := nat_mul_le_cancel_right_w5 K_den _ _ hK_pos htot
    have hlt_b := bernoulli_nat_ratio_lt 1 1 D C X (by decide) (by decide) hC_pos hX_ge
    omega

end CollatzFormal
