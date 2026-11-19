/-
  CollatzFormal/Wave11WholeSpaceCore.lean
  Wave 11 Whole-Space Mathematical & CS Proof Loop (Core — Fronts A & B):
  1. Front A — Left-Anchored / Reachable Arts–Giesl Dependency Pair (`DP2`) Chain Reduction
     (`WellFounded leftAnchoredDP2Step -> CollatzConjectureStandard` + Infinite `L`-Anchored
     `DP2` Recurrence Modulo `all11OmitR2List`, Separating `Z^+` Reachable Words from Unanchored
     `M2 = -1` `R8` Loops), `TwoSided(2 × 3)` / `TwoSided(2 × 6)` Rule-Removal & Positive-Syzygy
     Certificates (`60 -> 39`, `66 -> 64`, `120 -> 78`, `132 -> 126`), Exact Higher `K ∈ {4, 8}`,
     `M ∈ {6, 12, 18}` Left/Right Semantic Carriers, Fixed-Point-Free Period-`2` `deltaL_flip2`
     Certificate (`[]` axioms), & Universal `∀ K, M ≥ 1` Finite-Carrier Mersenne `B1/T2` Spine Lock (Branch P4.3)
  2. Front B — Complete Mod-`24` `2`-Adic Reciprocity Classification (`{7, 19, 23}` Universal Odd-`gcd`,
     Quartic `q ≡ 5` `6^((q-1)/4)` Biconditional, Octic `q ≡ 17` `8 ∣ ord_q(3/2)` Lock), Universal
     `ℓ`-Sylow (`ℓ = 2, 3, 5`; `mod 72, 96, 240`) Order-Lock + All-`m` (`∀ m ≥ 1`) Shared-Mersenne
     `m`-Block Obstructions + 1-Block Companion-Prime Quotient Cascades (`15 ∣ q0`, `255 ∣ q0`, `31 ∣ q0`,
     `511 ∣ q0`) + `(123, 195)` / `(205, 325)` / `(328, 520)` 2-Block Floors, Universal `∀ T ≥ 1`
     `(T + 1) × (T + 1)` Single-Base Closed Form (`W^(T*(T-1)/2) * (2^u - 1)^T`, Including `8 × 8`
     `W^21 * (2^u - 1)^7`) + Upgraded `2^u (2^u - 1)^(2T)` & `2^(3u) (2^u - 1)^9` Extrapolation +
     Column-Majorant Laplace Bound, & Rank-2 Vandermonde `6 × 6` `(T = 3, U = 2)` Closed Form / Cone
     Positivity + `8 × 8` Two-Base `(T = 4, U = 2)` Congruence / Divisibility / Cone Sign-Flip (Branches P3.4 & P3.3)

  Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

import CollatzFormal.Wave10WholeSpace

namespace CollatzFormal

-- ============================================================================
-- SECTION 1: Front A (Branch P4.3) — Left-Anchored Arts–Giesl Dependency Pair
--            (`DP2`) Reduction, `TwoSided(2 × 3)` / `TwoSided(2 × 6)` Cascades,
--            & Universal Finite-Carrier Mersenne `B1/T2` Spine Lock
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Section 1A: Left-Anchored `L`-Confinement & Reachable `DP2` Chain Reduction
-- ----------------------------------------------------------------------------

theorem not_mem_L_of_binSym :
    ∀ u : List MixedSRSSym, (∀ s, s ∈ u -> isBinaryInteriorSym s = true) -> .L ∉ u
  | [], _, hm => by cases hm
  | s :: rest, hbin, hm => by
    cases hm with
    | head =>
      have hs := hbin .L List.mem_cons_self
      cases hs
    | tail _ htail =>
      exact not_mem_L_of_binSym rest (fun x hx => hbin x (List.mem_cons_of_mem s hx)) htail

theorem not_mem_L_encodePosBin_and_R (n : Nat) (hn : n ≥ 1) :
    .L ∉ encodePosBin n ∧ .L ∉ (encodePosBin n ++ [.R]) := by
  rcases encodePosBin_spec n hn with ⟨_, hbin⟩
  have hno := not_mem_L_of_binSym (encodePosBin n) hbin
  refine ⟨hno, ?_⟩
  intro hm
  rcases List.mem_append.mp hm with h1 | h2
  · exact hno h1
  · simp at h2

theorem interior9_sub_omitR2 (r : List MixedSRSSym × List MixedSRSSym)
    (hm : r ∈ interiorAndRight9RuleList) : r ∈ all11OmitR2List := by
  revert r hm; decide

theorem interior9_no_L_rhs (r : List MixedSRSSym × List MixedSRSSym)
    (hm : r ∈ interiorAndRight9RuleList) : .L ∉ r.2 := by
  revert r hm; decide

theorem interior9_head_ne_L_and_nonempty (r : List MixedSRSSym × List MixedSRSSym)
    (hm : r ∈ interiorAndRight9RuleList) :
    r.1 ≠ [] ∧ r.1.head? ≠ some .L := by
  revert r hm; decide

theorem all11_rule_split_L_or_interior9 (r : List MixedSRSSym × List MixedSRSSym)
    (hm : r ∈ all11RuleList) :
    r = ([.L, .B0], [.L]) ∨
    r = ([.L, .B1], [.L, .T2]) ∨
    r ∈ interiorAndRight9RuleList := by
  revert r hm; decide

theorem srsStep_all11_left_anchored_split (w w' : List MixedSRSSym) (hnoL : .L ∉ w)
    (hstep : srsStepFromList all11RuleList ([.L] ++ w) w') :
    ∃ u : List MixedSRSSym,
      w' = [.L] ++ u ∧
      .L ∉ u ∧
      (srsStepFromList all11OmitR2List ([.L] ++ w) ([.L] ++ u) ∨
       ∃ v : List MixedSRSSym, w = .B1 :: v ∧ u = .T2 :: v) := by
  rcases hstep with ⟨p, l, r, sfx, hmem, hw1, hw2⟩
  cases p with
  | nil =>
    simp only [List.nil_append] at hw1 hw2
    rcases all11_rule_split_L_or_interior9 (l, r) hmem with hr1 | hr2 | hint
    · injection hr1 with hl hr; subst hl; subst hr
      have hw_eq : w = .B0 :: sfx := by simpa using hw1
      subst hw_eq
      have hno_sfx : .L ∉ sfx := fun hm => hnoL (List.mem_cons_of_mem .B0 hm)
      refine ⟨sfx, hw2, hno_sfx, Or.inl ?_⟩
      exact ⟨[], [.L, .B0], [.L], sfx, by decide, rfl, rfl⟩
    · injection hr2 with hl hr; subst hl; subst hr
      have hw_eq : w = .B1 :: sfx := by simpa using hw1
      subst hw_eq
      have hno_sfx : .L ∉ sfx := fun hm => hnoL (List.mem_cons_of_mem .B1 hm)
      refine ⟨.T2 :: sfx, ?_, ?_, Or.inr ⟨sfx, rfl, rfl⟩⟩
      · simpa using hw2
      · intro hm
        simp only [List.mem_cons] at hm
        rcases hm with h1 | ht
        · cases h1
        · exact hno_sfx ht
    · exfalso
      rcases interior9_head_ne_L_and_nonempty (l, r) hint with ⟨hl_ne, hl_head⟩
      cases l with
      | nil => exact hl_ne rfl
      | cons l0 ls =>
        simp only [List.cons_append, List.cons.injEq] at hw1
        exact hl_head (by simp [← hw1.1])
  | cons p0 ps =>
    simp only [List.cons_append, List.cons.injEq] at hw1
    rcases hw1 with ⟨hp0, hw_tail⟩
    subst hp0
    simp only [List.nil_append] at hw_tail
    have hl_noL : .L ∉ l := fun hm =>
      hnoL (hw_tail ▸ List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hm))))
    have hint : (l, r) ∈ interiorAndRight9RuleList := by
      rcases all11_rule_split_L_or_interior9 (l, r) hmem with hr1 | hr2 | hi
      · injection hr1 with hl _; subst hl; exact False.elim (hl_noL (List.Mem.head _))
      · injection hr2 with hl _; subst hl; exact False.elim (hl_noL (List.Mem.head _))
      · exact hi
    let u := ps ++ r ++ sfx
    have hw2_eq : w' = [.L] ++ u := by
      rw [hw2]; simp [u, List.cons_append, List.append_assoc]
    have hno_u : .L ∉ u := by
      intro hm
      have hps_no : .L ∉ ps := fun hp =>
        hnoL (hw_tail ▸ List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hp))))
      have hsfx_no : .L ∉ sfx := fun hs =>
        hnoL (hw_tail ▸ List.mem_append.mpr (Or.inr hs))
      have hr_no : .L ∉ r := interior9_no_L_rhs (l, r) hint
      rcases List.mem_append.mp hm with h1 | h2
      · rcases List.mem_append.mp h1 with h1a | h1b
        · exact hps_no h1a
        · exact hr_no h1b
      · exact hsfx_no h2
    refine ⟨u, hw2_eq, hno_u, Or.inl ?_⟩
    exact ⟨.L :: ps, l, r, sfx, interior9_sub_omitR2 (l, r) hint,
      by simp [hw_tail, List.cons_append, List.append_assoc],
      by simp [u, List.cons_append, List.append_assoc]⟩

theorem srsReaches_omitR2_trans {a b c : List MixedSRSSym}
    (h1 : srsReachesFromList all11OmitR2List a b)
    (h2 : srsReachesFromList all11OmitR2List b c) :
    srsReachesFromList all11OmitR2List a c := by
  induction h1 with
  | refl _ => exact h2
  | step hs _ ih => exact .step hs (ih h2)

theorem mixedSRSReaches_noL_to_omitR2 {w1 w2 : List MixedSRSSym}
    (hreach : MixedSRSReaches w1 w2) :
    .L ∉ w1 -> srsReachesFromList all11OmitR2List ([.L] ++ w1) ([.L] ++ w2) := by
  induction hreach with
  | refl w =>
    intro _
    exact .refl ([.L] ++ w)
  | @step a b _ hs _ ih =>
    intro hnoL1
    rcases hs with ⟨p, l, r, q, hrule, hw1, hw2⟩
    have hl_noL : .L ∉ l := fun hm =>
      hnoL1 (hw1 ▸ List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hm))))
    have hint : (l, r) ∈ interiorAndRight9RuleList := by
      rcases all11_rule_split_L_or_interior9 (l, r) (mixedSRSBaseRule_mem_all11 hrule) with
        hr1 | hr2 | hi
      · injection hr1 with hl _; subst hl; exact False.elim (hl_noL (List.Mem.head _))
      · injection hr2 with hl _; subst hl; exact False.elim (hl_noL (List.Mem.head _))
      · exact hi
    have hnoL2 : .L ∉ (p ++ r ++ q) := by
      intro hm
      have hp_no : .L ∉ p := fun hp =>
        hnoL1 (hw1 ▸ List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hp))))
      have hq_no : .L ∉ q := fun hq =>
        hnoL1 (hw1 ▸ List.mem_append.mpr (Or.inr hq))
      have hr_no : .L ∉ r := interior9_no_L_rhs (l, r) hint
      rcases List.mem_append.mp hm with h1 | h2
      · rcases List.mem_append.mp h1 with h1a | h1b
        · exact hp_no h1a
        · exact hr_no h1b
      · exact hq_no h2
    have hstep_L : srsStepFromList all11OmitR2List ([.L] ++ a) ([.L] ++ b) :=
      ⟨.L :: p, l, r, q, interior9_sub_omitR2 (l, r) hint,
       by rw [hw1]; simp [List.cons_append, List.append_assoc],
       by rw [hw2]; simp [List.cons_append, List.append_assoc]⟩
    exact .step hstep_L (ih (hw2 ▸ hnoL2))

/-- Root-anchored Dependency Pair `DP2` transition modulo `all11OmitR2List` (`{R1, R3..R11}`). -/
def leftAnchoredDP2Step (u1 u2 : List MixedSRSSym) : Prop :=
  .L ∉ u1 ∧ .L ∉ u2 ∧
  srsReachesFromList all11OmitR2List ([.L, .T2] ++ u1) ([.L, .B1] ++ u2)

theorem even_drain_reaches_odd_or_one :
    ∀ (fuel m : Nat),
      m ≥ 1 -> m ≤ fuel ->
      (∃ k : Nat, collatzIter k m = 1) ∨
      (∃ (m_odd : Nat) (u : List MixedSRSSym),
        m_odd ≥ 3 ∧ m_odd % 2 = 1 ∧ .L ∉ u ∧
        encodePosBin m_odd ++ [.R] = .B1 :: u ∧
        srsReachesFromList all11OmitR2List
          ([.L] ++ encodePosBin m ++ [.R])
          ([.L, .B1] ++ u) ∧
        (∀ k : Nat, collatzIter k m_odd = 1 -> ∃ k' : Nat, collatzIter k' m = 1))
  | 0, m, hm1, hm0 => by omega
  | fuel + 1, m, hm1, hmf => by
    by_cases hm_eq1 : m = 1
    · subst hm_eq1; exact Or.inl ⟨0, rfl⟩
    · rcases encodePosBin_spec m hm1 with ⟨heval_m, hbin_m⟩
      cases hu : encodePosBin m with
      | nil => rw [hu] at heval_m; simp [srsEvalInterior] at heval_m; omega
      | cons b rest =>
        rw [hu] at heval_m hbin_m
        have hb := hbin_m b List.mem_cons_self
        have hrest_bin : ∀ s, s ∈ rest -> isBinaryInteriorSym s = true :=
          fun s hs => hbin_m s (List.mem_cons_of_mem b hs)
        cases b <;> simp [isBinaryInteriorSym] at hb
        · -- `b = .B0` (`m` even, `m / 2 = srsEvalInterior rest ≥ 1`):
          simp only [srsEvalInterior] at heval_m
          have hm_ev : m % 2 = 0 := by omega
          have hhalf_eq : m / 2 = srsEvalInterior rest := by omega
          have hhalf_pos : m / 2 ≥ 1 := by rw [hhalf_eq]; exact srsEvalInterior_pos rest
          have hrest_eq : rest = encodePosBin (m / 2) := by
            rcases encodePosBin_spec (m / 2) hhalf_pos with ⟨heval_h, hbin_h⟩
            exact binary_interior_unique rest (encodePosBin (m / 2)) hrest_bin hbin_h (by omega)
          have hstep_r1 : srsStepFromList all11OmitR2List
              ([.L] ++ (.B0 :: rest) ++ [.R])
              ([.L] ++ encodePosBin (m / 2) ++ [.R]) := by
            rw [hrest_eq]
            exact ⟨[], [.L, .B0], [.L], encodePosBin (m / 2) ++ [.R], by decide, rfl, rfl⟩
          have hcol_ev : collatzStep m = m / 2 := by
            have hd : (m % 2 == 0) = true := decide_eq_true hm_ev
            simp [collatzStep, hd]
          rcases even_drain_reaches_odd_or_one fuel (m / 2) hhalf_pos (by omega) with
            ⟨k, hk1⟩ | ⟨m_odd, u, hm3, hmodd, hnoL, henc_o, hreach, hback⟩
          · exact Or.inl ⟨k + 1, by simp [collatzIter, hcol_ev, hk1]⟩
          · refine Or.inr ⟨m_odd, u, hm3, hmodd, hnoL, henc_o, .step hstep_r1 hreach, ?_⟩
            intro k hk1
            rcases hback k hk1 with ⟨k', hk'⟩
            exact ⟨k' + 1, by simp [collatzIter, hcol_ev, hk']⟩
        · -- `b = .B1` (`m ≥ 3` odd):
          simp only [srsEvalInterior] at heval_m
          have hm_odd : m % 2 = 1 := by omega
          have hrest_pos := srsEvalInterior_pos rest
          let u := rest ++ [.R]
          have hnoL_u : .L ∉ u := by
            intro hm_in
            rcases List.mem_append.mp hm_in with h1 | h2
            · exact not_mem_L_of_binSym rest hrest_bin h1
            · simp at h2
          have henc_u : encodePosBin m ++ [.R] = .B1 :: u := by
            rw [hu]; rfl
          exact Or.inr ⟨m, u, by omega, hm_odd, hnoL_u, henc_u, .refl _, fun k hk => ⟨k, hk⟩⟩

/--
  Theorem W11.1a (`artsGieslSemanticDP1D_interior_invariant_and_dp1_strict`, `[]` axioms):
  Exact 1D Semantic DP Invariance on ALL 9 Interior/Right Rules `{R3..R11}` & Strict `DP1` Drop:
  `artsGieslSemanticDP1D` evaluates identically on LHS and RHS across all `9` rules in
  `interiorAndRight9RuleList` (with BOTH swap rules `R3` and `R8` active!) while strictly
  orienting `DP1 : [.L, .B0] -> [.L]`.
-/
theorem artsGieslSemanticDP1D_interior_invariant_and_dp1_strict :
    interiorAndRight9RuleList.length = 9 ∧
    (∀ r ∈ interiorAndRight9RuleList,
      evalWordAffine1D artsGieslSemanticDP1D r.1 =
        evalWordAffine1D artsGieslSemanticDP1D r.2) ∧
    (evalWordAffine1D artsGieslSemanticDP1D [.L, .B0]).m ≥
      (evalWordAffine1D artsGieslSemanticDP1D [.L]).m ∧
    (evalWordAffine1D artsGieslSemanticDP1D [.L, .B0]).c >
      (evalWordAffine1D artsGieslSemanticDP1D [.L]).c := by
  refine ⟨rfl, ?_, by decide, by decide⟩
  intro r hr
  have hmc :
      (evalWordAffine1D artsGieslSemanticDP1D r.1).m =
        (evalWordAffine1D artsGieslSemanticDP1D r.2).m ∧
      (evalWordAffine1D artsGieslSemanticDP1D r.1).c =
        (evalWordAffine1D artsGieslSemanticDP1D r.2).c := by
    revert r hr; decide
  cases h1 : evalWordAffine1D artsGieslSemanticDP1D r.1 with
  | mk m1 c1 =>
    cases h2 : evalWordAffine1D artsGieslSemanticDP1D r.2 with
    | mk m2 c2 =>
      rw [h1, h2] at hmc
      rcases hmc with ⟨rfl, rfl⟩
      rfl

/--
  Theorem W11.1b (`left_anchored_dp2_chain_reduction`, `zero custom axioms`):
  Left-Anchored / Reachable Arts–Giesl Dependency Pair (`DP2`) Reduction (`Branch P4.3`):
  1. **`L`-Confinement on Reachable `Z^+` Encodings (`∀ n ≥ 1`)**:
     `.L ∉ (encodePosBin n ++ [.R])`, separating positive integer configurations `[.L] ++ w`
     (`.L ∉ w`) from unanchored interior `M2 = -1` `[.T2, .B1] -> [.B1, .T2]` (`R8`) commutators!
  2. **Infinite `L`-Anchored `DP2` Recurrence Theorem**:
     Because `all11OmitR2List` (`{R1, R3..R11}`, containing BOTH `R3` and `R8`!) is well-founded
     in 1 step under `omitR2Single2DCert`, EVERY infinite `all11RuleList` rewrite sequence starting
     from `[.L] ++ w0` (`.L ∉ w0`) preserves `.L`-confinement at index `0` AND fires root-anchored
     `DP2 : [.L, .B1] ++ v -> [.L, .T2] ++ v` infinitely often (`∀ N, ∃ t ≥ N, ...`)!
  3. **Constructive Forward Bridge (`WellFounded leftAnchoredDP2Step -> CollatzConjectureStandard`)**:
     Well-foundedness of the single root-anchored `DP2` relation `leftAnchoredDP2Step` modulo
     `all11OmitR2List` unconditionally implies `CollatzConjectureStandard`!
-/
theorem left_anchored_dp2_chain_reduction :
    (∀ n : Nat, n ≥ 1 -> .L ∉ (encodePosBin n ++ [.R])) ∧
    (∀ (seq : Nat -> List MixedSRSSym) (w0 : List MixedSRSSym),
      .L ∉ w0 ->
      seq 0 = [.L] ++ w0 ->
      (∀ t : Nat, srsStepFromList all11RuleList (seq t) (seq (t + 1))) ->
      ∀ N : Nat,
        ∃ (t : Nat) (v : List MixedSRSSym),
          t ≥ N ∧ .L ∉ v ∧
          seq t = [.L, .B1] ++ v ∧
          seq (t + 1) = [.L, .T2] ++ v) ∧
    (WellFounded (fun u2 u1 => leftAnchoredDP2Step u1 u2) ->
      CollatzConjectureStandard) := by
  refine ⟨fun n hn => (not_mem_L_encodePosBin_and_R n hn).2, ?_, ?_⟩
  · -- Part 2: Every infinite `L`-anchored `all11RuleList` chain fires root-anchored `DP2` infinitely often:
    intro seq w0 hno0 hseq0 hinf N
    -- First prove by induction on `t` that `∃ wt, .L ∉ wt ∧ seq t = [.L] ++ wt`:
    have hinv : ∀ t : Nat, ∃ wt : List MixedSRSSym, .L ∉ wt ∧ seq t = [.L] ++ wt := by
      intro t; induction t with
      | zero => exact ⟨w0, hno0, hseq0⟩
      | succ t' ih =>
        rcases ih with ⟨wt', hno', heq'⟩
        have hs := hinf t'
        rw [heq'] at hs
        rcases srsStep_all11_left_anchored_split wt' (seq (t' + 1)) hno' hs with
          ⟨ut, hut_eq, hno_ut, _⟩
        exact ⟨ut, hno_ut, hut_eq⟩
    -- Use `Acc` of `all11OmitR2List` (`omit_r2_10_of_11_admits_single_2d_hw_cert`) at `seq N`:
    have htower_r2 := omit_r2_10_of_11_admits_single_2d_hw_cert.2.2.2
    have hacc_N := hofbauer_waldmann_tower_acc_srsPlus 2 (by decide) 1 all11OmitR2List htower_r2 (seq N)
    have hfind : ∀ w : List MixedSRSSym,
        Acc (fun w2 w1 => srsPlusFromList all11OmitR2List w1 w2) w ->
        ∀ k : Nat, seq k = w ->
        ∃ (t : Nat) (v : List MixedSRSSym),
          t ≥ k ∧ .L ∉ v ∧ seq t = [.L, .B1] ++ v ∧ seq (t + 1) = [.L, .T2] ++ v := by
      intro w hacc
      induction hacc with
      | intro w _ ih =>
        intro k hkw
        rcases hinv k with ⟨wk, hnok, hseqk⟩
        have hs := hinf k
        rw [hseqk] at hs
        rcases srsStep_all11_left_anchored_split wk (seq (k + 1)) hnok hs with
          ⟨uk, huk_eq, _, hor⟩
        rcases hor with hs_omit | ⟨v, hwk_v, huk_v⟩
        · have hplus : srsPlusFromList all11OmitR2List w (seq (k + 1)) := by
            rw [← hkw, hseqk, huk_eq]
            exact ⟨[.L] ++ uk, hs_omit, .refl _⟩
          rcases ih (seq (k + 1)) hplus (k + 1) rfl with ⟨t, v, htk, hnov, hst, hst1⟩
          exact ⟨t, v, by omega, hnov, hst, hst1⟩
        · have hnov : .L ∉ v := fun hm => hnok (hwk_v ▸ List.mem_cons_of_mem .B1 hm)
          refine ⟨k, v, Nat.le_refl k, hnov, ?_, ?_⟩
          · rw [hseqk, hwk_v]; rfl
          · rw [huk_eq, huk_v]; rfl
    exact hfind (seq N) hacc_N N rfl
  · -- Part 3: Constructive `WellFounded leftAnchoredDP2Step -> CollatzConjectureStandard`:
    intro hwf
    rw [collatz_standard_iff_compressed]
    intro n hn
    have hacc_odd : ∀ u : List MixedSRSSym,
        Acc (fun u2 u1 => leftAnchoredDP2Step u1 u2) u ->
        ∀ m : Nat, m ≥ 3 -> m % 2 = 1 -> .L ∉ u ->
        encodePosBin m ++ [.R] = .B1 :: u ->
        ∃ t : Nat, collatzIter t m = 1 := by
      intro u hacc
      induction hacc with
      | intro u _ ih =>
        intro m hm3 hmodd hnoL_u henc_m
        -- Odd step `m -> collatzStep m`:
        rcases encodePosBin_spec m (by omega) with ⟨heval_m, hbin_m⟩
        cases hbm : encodePosBin m with
        | nil => rw [hbm] at heval_m; simp [srsEvalInterior] at heval_m; omega
        | cons b rest =>
          rw [hbm] at heval_m hbin_m henc_m
          simp only [List.cons_append, List.cons.injEq] at henc_m
          rcases henc_m with ⟨hb_eq, hrest_R⟩
          subst hb_eq
          have hrest_bin : ∀ s, s ∈ rest -> isBinaryInteriorSym s = true :=
            fun s hs => hbin_m s (List.mem_cons_of_mem .B1 hs)
          simp only [srsEvalInterior] at heval_m
          have hodd_b : (m % 2 == 0) = false := decide_eq_false (by omega)
          have hcstep : collatzStep m = 3 * srsEvalInterior rest + 2 := by
            simp only [collatzStep, hodd_b, Bool.false_eq_true, ite_false]; omega
          have hcstep_pos : collatzStep m ≥ 1 := by omega
          rcases carry_propagate_reaches_binary rest .T2 hrest_bin (Or.inr (Or.inr rfl)) with
            ⟨v, hv_bin, hv_eval, hv_reach⟩
          simp only [srsEvalInterior] at hv_eval
          have hv_eq : v = encodePosBin (collatzStep m) := by
            rcases encodePosBin_spec (collatzStep m) hcstep_pos with ⟨_, hbin_c⟩
            exact binary_interior_unique v (encodePosBin (collatzStep m)) hv_bin hbin_c (by omega)
          have hnoL_t2 : .L ∉ ([.T2] ++ rest ++ [.R]) := by
            intro hm_in
            simp only [List.cons_append, List.nil_append, List.mem_cons] at hm_in
            rcases hm_in with h1 | h2
            · cases h1
            · exact hnoL_u (hrest_R ▸ h2)
          have hreach_c : srsReachesFromList all11OmitR2List
              ([.L, .T2] ++ u)
              ([.L] ++ encodePosBin (collatzStep m) ++ [.R]) := by
            have hr0 := mixedSRSReaches_noL_to_omitR2 hv_reach hnoL_t2
            rw [hv_eq] at hr0
            have hlhs : [.L] ++ ([.T2] ++ rest ++ [.R]) = [.L, .T2] ++ u := by
              rw [← hrest_R]; simp
            have hrhs : [.L] ++ (encodePosBin (collatzStep m) ++ [.R]) =
                [.L] ++ encodePosBin (collatzStep m) ++ [.R] := by simp
            rwa [hlhs, hrhs] at hr0
          rcases even_drain_reaches_odd_or_one (collatzStep m) (collatzStep m)
            hcstep_pos (Nat.le_refl _) with
            ⟨k, hk1⟩ | ⟨m_next, u_next, hm3_n, hmodd_n, hnoL_n, henc_n, hreach_d, hback_n⟩
          · exact ⟨k + 1, hk1⟩
          · have hdp : leftAnchoredDP2Step u u_next :=
              ⟨hnoL_u, hnoL_n, srsReaches_omitR2_trans hreach_c hreach_d⟩
            rcases ih u_next hdp m_next hm3_n hmodd_n hnoL_n henc_n with ⟨k_n, hk_n⟩
            rcases hback_n k_n hk_n with ⟨k_c, hk_c⟩
            exact ⟨k_c + 1, hk_c⟩
    rcases even_drain_reaches_odd_or_one n n hn (Nat.le_refl n) with
      ⟨k, hk1⟩ | ⟨m_odd, u0, hm3, hmodd, hnoL0, henc0, _, hback0⟩
    · exact ⟨k, hk1⟩
    · rcases hacc_odd u0 (hwf.apply u0) m_odd hm3 hmodd hnoL0 henc0 with ⟨k, hk1⟩
      exact hback0 k hk1

-- ----------------------------------------------------------------------------
-- Section 1B: `TwoSided(2 × 3)` & `TwoSided(2 × 6)` Parikh Cascades & Syzygies
-- ----------------------------------------------------------------------------

def wtTwoSidedMod3OmitR3 (s : Fin 42) : Nat :=
  match s.val with
  | 12 => 1 | 15 => 1 | 19 => 2 | 24 => 2 | 25 => 3 | 26 => 3 | 34 => 1 | _ => 0

def syzTwoSidedMod3OmitR3Core39 : List Nat :=
  [2, 4, 2, 4, 24, 2, 2, 2, 14, 10, 14, 10, 12, 2, 10, 2, 10, 2, 10, 10,
   20, 20, 14, 2, 2, 9, 7, 4, 4, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2]

def wtTwoSidedMod3All11 (s : Fin 42) : Nat :=
  if s.val = 0 ∨ s.val = 3 then 1 else 0

def syzTwoSidedMod3All11Core64 : List Nat :=
  [1, 6, 1, 1, 2, 1, 14, 5, 1, 1, 3, 3, 1, 1, 7, 1, 1, 1, 2, 2, 4, 1,
   8, 4, 3, 1, 2, 2, 1, 4, 6, 1, 1, 1, 1, 11, 4, 4, 6, 3, 6, 9, 1, 1,
   1, 3, 2, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

def wtTwoSidedMod6OmitR3 (s : Fin 84) : Nat :=
  match s.val with
  | 24 => 1 | 30 => 1 | 37 => 1 | 40 => 1 | 57 => 1 | 67 => 1 | 70 => 1
  | 27 => 2 | 33 => 2 | 49 => 2 | 51 => 2 | 53 => 2
  | _ => 0

def syzTwoSidedMod6OmitR3Core78 : List Nat :=
  [1, 2, 1, 2, 1, 2, 1, 2, 63, 1, 2, 1, 1, 1, 2, 1, 7, 10, 32, 1, 39, 1,
   3, 7, 2, 30, 8, 33, 1, 1, 1, 2, 6, 8, 1, 5, 1, 4, 8, 37, 7, 36, 44, 1,
   1, 29, 34, 1, 1, 14, 29, 44, 16, 1, 2, 2, 2, 2, 2, 16, 1, 1, 1, 1, 1,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 15]

def wtTwoSidedMod6All11 (s : Fin 84) : Nat :=
  match s.val with
  | 0 => 2 | 6 => 2 | 3 => 1 | 9 => 1 | _ => 0

def syzTwoSidedMod6All11Core126 : List Nat :=
  [1, 2, 1, 14, 1, 1, 2, 1, 2, 1, 11, 13, 14, 1, 1, 1, 2, 1, 1, 1, 1, 3,
   7, 1, 1, 3, 1, 5, 7, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 1, 5, 3, 7,
   9, 5, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 1, 7, 9, 1, 1, 1, 1, 1, 1, 1, 13,
   5, 1, 5, 7, 1, 1, 3, 7, 13, 1, 3, 5, 1, 11, 11, 1, 1, 3, 3, 3, 1, 3,
   2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

-- Single-pass O(|rules| * N) positive Parikh-syzygy checker that strips dependent `Fin N` proofs
-- once per rule so `M = 6` (`Fin 84`, `126` rules) verifies in < 5 MB of kernel memory:

def countNatOccW11 (target : Nat) : List Nat -> Nat
  | [] => 0
  | x :: xs => (if x = target then 1 else 0) + countNatOccW11 target xs

theorem countNatOccW11_map_val (N : Nat) (s : Fin N) :
    ∀ u : List (Fin N), countNatOccW11 s.val (u.map Fin.val) = countFinOcc N s u
  | [] => rfl
  | x :: xs => by
    simp only [List.map, countNatOccW11, countFinOcc, countNatOccW11_map_val N s xs]

def addRuleToCountsW11 (m : Nat) (l r : List Nat) : Nat -> List (Nat × Nat) -> List (Nat × Nat)
  | _, [] => []
  | idx, p :: rest =>
    (p.1 + m * countNatOccW11 idx l, p.2 + m * countNatOccW11 idx r) ::
      addRuleToCountsW11 m l r (idx + 1) rest

def accumSymCountsW11 (N : Nat) :
    List (List (Fin N) × List (Fin N)) -> List Nat -> List (Nat × Nat)
  | [], _ => List.replicate N (0, 0)
  | _, [] => List.replicate N (0, 0)
  | r :: rs, m :: ms =>
    addRuleToCountsW11 m (r.1.map Fin.val) (r.2.map Fin.val) 0 (accumSymCountsW11 N rs ms)

def checkPairsLeBoolW11 : List (Nat × Nat) -> Bool
  | [] => true
  | p :: rest => decide (p.1 ≤ p.2) && checkPairsLeBoolW11 rest

def getPairAtW11 : List (Nat × Nat) -> Nat -> Nat × Nat
  | [], _ => (0, 0)
  | p :: _, 0 => p
  | _ :: rest, k + 1 => getPairAtW11 rest k

theorem getPairAtW11_replicate :
    ∀ n k : Nat, getPairAtW11 (List.replicate n (0, 0)) k = (0, 0)
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | n + 1, k + 1 => getPairAtW11_replicate n k

theorem addRuleToCountsW11_len_and_get (m : Nat) (l r : List Nat) :
    ∀ (acc : List (Nat × Nat)) (idx : Nat),
      (addRuleToCountsW11 m l r idx acc).length = acc.length ∧
      (∀ k : Nat, k < acc.length ->
        getPairAtW11 (addRuleToCountsW11 m l r idx acc) k =
          ((getPairAtW11 acc k).1 + m * countNatOccW11 (idx + k) l,
           (getPairAtW11 acc k).2 + m * countNatOccW11 (idx + k) r))
  | [], _ => ⟨rfl, fun _ hk => by simp at hk⟩
  | p :: rest, idx => by
    rcases addRuleToCountsW11_len_and_get m l r rest (idx + 1) with ⟨hlen, hget⟩
    refine ⟨by simp [addRuleToCountsW11, hlen], ?_⟩
    intro k hk
    cases k with
    | zero => simp [addRuleToCountsW11, getPairAtW11]
    | succ k' =>
      simp only [addRuleToCountsW11, getPairAtW11]
      rw [hget k' (by simp at hk; omega), show idx + 1 + k' = idx + (k' + 1) by omega]

theorem accumSymCountsW11_spec (N : Nat) :
    ∀ (rules : List (List (Fin N) × List (Fin N))) (mults : List Nat),
      (accumSymCountsW11 N rules mults).length = N ∧
      (∀ s : Fin N,
        getPairAtW11 (accumSymCountsW11 N rules mults) s.val =
          (weightedSymLhsSum N s rules mults, weightedSymRhsSum N s rules mults))
  | [], _ => ⟨List.length_replicate, fun s => by
      simp [accumSymCountsW11, getPairAtW11_replicate, weightedSymLhsSum, weightedSymRhsSum]⟩
  | _ :: _, [] => ⟨List.length_replicate, fun s => by
      simp [accumSymCountsW11, getPairAtW11_replicate, weightedSymLhsSum, weightedSymRhsSum]⟩
  | r0 :: rs, m0 :: ms => by
    rcases accumSymCountsW11_spec N rs ms with ⟨hlen, hget⟩
    rcases addRuleToCountsW11_len_and_get m0 (r0.1.map Fin.val) (r0.2.map Fin.val)
      (accumSymCountsW11 N rs ms) 0 with ⟨hlen_a, hget_a⟩
    refine ⟨by simp [accumSymCountsW11, hlen_a, hlen], ?_⟩
    intro s
    simp only [accumSymCountsW11, weightedSymLhsSum, weightedSymRhsSum]
    rw [hget_a s.val (by rw [hlen]; exact s.isLt), hget s, Nat.zero_add,
        countNatOccW11_map_val N s r0.1, countNatOccW11_map_val N s r0.2]
    exact Prod.ext (Nat.add_comm _ _) (Nat.add_comm _ _)

theorem checkPairsLeBoolW11_sound :
    ∀ (acc : List (Nat × Nat)),
      checkPairsLeBoolW11 acc = true ->
      ∀ k : Nat, k < acc.length -> (getPairAtW11 acc k).1 ≤ (getPairAtW11 acc k).2
  | [], _, _, hk => by simp at hk
  | p :: rest, hb, 0, _ => (bool_and_split hb).1 |> of_decide_eq_true
  | _ :: rest, hb, k + 1, hk =>
    checkPairsLeBoolW11_sound rest (bool_and_split hb).2 k (by simp at hk; omega)

def checkPositiveParikhSyzygyFastBool (N : Nat)
    (rules : List (List (Fin N) × List (Fin N))) (mults : List Nat) : Bool :=
  decide (rules.length ≥ 1) &&
  decide (rules.length = mults.length) &&
  checkAllPosNatList mults &&
  checkPairsLeBoolW11 (accumSymCountsW11 N rules mults)

theorem positive_parikh_syzygy_fast_blocks_all_omega_towers
    (N : Nat) (rules : List (List (Fin N) × List (Fin N))) (mults : List Nat)
    (hsyz : checkPositiveParikhSyzygyFastBool N rules mults = true) :
    ∀ k : Nat, ¬ GenOmegaParikhTower N k rules := by
  unfold checkPositiveParikhSyzygyFastBool at hsyz
  rcases bool_and_split hsyz with ⟨hb1, hpairs⟩
  rcases bool_and_split hb1 with ⟨hb2, hpos⟩
  rcases bool_and_split hb2 with ⟨hlen_ge1, hlen_eq⟩
  have hne : rules.length ≥ 1 := of_decide_eq_true hlen_ge1
  have hlen : rules.length = mults.length := of_decide_eq_true hlen_eq
  rcases accumSymCountsW11_spec N rules mults with ⟨hacc_len, hacc_get⟩
  have hsym_le : ∀ s : Fin N, weightedSymLhsSum N s rules mults ≤ weightedSymRhsSum N s rules mults := by
    intro s
    have hle := checkPairsLeBoolW11_sound _ hpairs s.val (by rw [hacc_len]; exact s.isLt)
    rwa [hacc_get s] at hle
  have heq_all : ∀ wt : Fin N -> Nat,
      (∀ r ∈ rules, evalFinParikh N wt r.1 ≥ evalFinParikh N wt r.2) ->
      ∀ r ∈ rules, evalFinParikh N wt r.1 = evalFinParikh N wt r.2 := by
    intro wt hweak
    rcases weightedParikh_eq_sum_sym N wt rules mults with ⟨hl_sum, hr_sum⟩
    have htot_le : weightedParikhLhs N wt rules mults ≤ weightedParikhRhs N wt rules mults := by
      rw [hl_sum, hr_sum]
      exact natSumPrefix_mono_w5 N _ _
        (fun s => Nat.mul_le_mul_left (wt s) (hsym_le s)) N
    exact weightedParikh_strict_of_mem N wt rules mults hlen hpos hweak htot_le
  cases rules with
  | nil => simp at hne
  | cons r0 rs =>
    have h_imp : ∀ (k : Nat) (cur : List (List (Fin N) × List (Fin N))),
        (∀ r ∈ r0 :: rs, r ∈ cur) -> ¬ GenOmegaParikhTower N k cur := by
      intro k; induction k with
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

private theorem ts3_or3_cascade_ok :
    checkFinParikhWeakBool 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List) = true ∧
    (filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)).length = 39 := by decide

private theorem ts3_all_cascade_ok :
    checkFinParikhWeakBool 42 wtTwoSidedMod3All11
      (twoSidedLabelledCollatzRules 3 (by decide) all11RuleList) = true ∧
    (filterFinParikhUnoriented 42 wtTwoSidedMod3All11
      (twoSidedLabelledCollatzRules 3 (by decide) all11RuleList)).length = 64 := by decide

set_option maxRecDepth 65536 in
private theorem ts6_or3_cascade_ok :
    checkFinParikhWeakBool 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List) = true ∧
    (filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)).length = 78 := by decide

set_option maxRecDepth 65536 in
private theorem ts6_all_cascade_ok :
    checkFinParikhWeakBool 84 wtTwoSidedMod6All11
      (twoSidedLabelledCollatzRules 6 (by decide) all11RuleList) = true ∧
    (filterFinParikhUnoriented 84 wtTwoSidedMod6All11
      (twoSidedLabelledCollatzRules 6 (by decide) all11RuleList)).length = 126 := by decide

set_option maxRecDepth 65536 in
private theorem ts3_or3_syz_ok :
    checkPositiveParikhSyzygyFastBool 42
      (filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
        (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List))
      syzTwoSidedMod3OmitR3Core39 = true := by decide

set_option maxRecDepth 65536 in
private theorem ts3_all_syz_ok :
    checkPositiveParikhSyzygyFastBool 42
      (filterFinParikhUnoriented 42 wtTwoSidedMod3All11
        (twoSidedLabelledCollatzRules 3 (by decide) all11RuleList))
      syzTwoSidedMod3All11Core64 = true := by decide

set_option maxRecDepth 65536 in
private theorem ts6_or3_syz_ok :
    checkPositiveParikhSyzygyFastBool 84
      (filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
        (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List))
      syzTwoSidedMod6OmitR3Core78 = true := by decide

set_option maxRecDepth 65536 in
private theorem ts6_all_syz_ok :
    checkPositiveParikhSyzygyFastBool 84
      (filterFinParikhUnoriented 84 wtTwoSidedMod6All11
        (twoSidedLabelledCollatzRules 6 (by decide) all11RuleList))
      syzTwoSidedMod6All11Core126 = true := by decide

/--
  Theorem W11.1c (`twosided_mod3_and_mod6_omit_r3_and_all11_certs`, `zero custom axioms`):
  Two-Sided `(collatzSemL2 × collatzSemMod M)` (`M = 3, 6`) Rule-Removal Cascades & Positive-Syzygy
  Residual Cores on `all11 \ {R3}` (`S9 ∪ {R8}`) and Full `all11RuleList`:
  1. `TwoSided(2 × 3)` (`Fin 42`): strictly removes **`21 / 60` rules** (`60 -> 39`) on `all11OmitR3List`
     and **`2 / 66` rules** (`66 -> 64`) on `all11RuleList`!
  2. `TwoSided(2 × 6)` (`Fin 84`): strictly removes **`42 / 120` rules** (`120 -> 78`, `35%` of the
     system!) on `all11OmitR3List` and **`6 / 132` rules** (`132 -> 126`) on `all11RuleList`!
  3. **Exact Residual Positive Parikh Syzygies (`∀ k : Nat`)**:
     Every surviving core (`39/39`, `64/64`, `78/78`, `126/126`) satisfies a strictly positive
     rule-multiplicity syzygy, refuting `GenOmegaParikhTower` for ALL `k : Nat`!
-/
theorem twosided_mod3_and_mod6_omit_r3_and_all11_certs :
    let ts3_or3 := twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List
    let ts3_all := twoSidedLabelledCollatzRules 3 (by decide) all11RuleList
    let ts6_or3 := twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List
    let ts6_all := twoSidedLabelledCollatzRules 6 (by decide) all11RuleList
    let c39  := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3 ts3_or3
    let c64  := filterFinParikhUnoriented 42 wtTwoSidedMod3All11 ts3_all
    let c78  := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3 ts6_or3
    let c126 := filterFinParikhUnoriented 84 wtTwoSidedMod6All11 ts6_all
    (ts3_or3.length = 60 ∧
     checkFinParikhWeakBool 42 wtTwoSidedMod3OmitR3 ts3_or3 = true ∧
     c39.length = 39 ∧
     ts3_all.length = 66 ∧
     checkFinParikhWeakBool 42 wtTwoSidedMod3All11 ts3_all = true ∧
     c64.length = 64) ∧
    (ts6_or3.length = 120 ∧
     checkFinParikhWeakBool 84 wtTwoSidedMod6OmitR3 ts6_or3 = true ∧
     c78.length = 78 ∧
     ts6_all.length = 132 ∧
     checkFinParikhWeakBool 84 wtTwoSidedMod6All11 ts6_all = true ∧
     c126.length = 126) ∧
    (∀ k : Nat,
      ¬ GenOmegaParikhTower 42 k c39 ∧
      ¬ GenOmegaParikhTower 42 k c64 ∧
      ¬ GenOmegaParikhTower 84 k c78 ∧
      ¬ GenOmegaParikhTower 84 k c126) := by
  dsimp only
  have h39 := positive_parikh_syzygy_fast_blocks_all_omega_towers 42 _ syzTwoSidedMod3OmitR3Core39 ts3_or3_syz_ok
  have h64 := positive_parikh_syzygy_fast_blocks_all_omega_towers 42 _ syzTwoSidedMod3All11Core64 ts3_all_syz_ok
  have h78 := positive_parikh_syzygy_fast_blocks_all_omega_towers 84 _ syzTwoSidedMod6OmitR3Core78 ts6_or3_syz_ok
  have h126 := positive_parikh_syzygy_fast_blocks_all_omega_towers 84 _ syzTwoSidedMod6All11Core126 ts6_all_syz_ok
  exact ⟨⟨rfl, ts3_or3_cascade_ok.1, ts3_or3_cascade_ok.2,
          rfl, ts3_all_cascade_ok.1, ts3_all_cascade_ok.2⟩,
         ⟨rfl, ts6_or3_cascade_ok.1, ts6_or3_cascade_ok.2,
          rfl, ts6_all_cascade_ok.1, ts6_all_cascade_ok.2⟩,
         fun k => ⟨h39 k, h64 k, h78 k, h126 k⟩⟩

-- ----------------------------------------------------------------------------
-- Section 1C: Universal `∀ K ≥ 1` Finite-Carrier Mersenne `B1/T2` Spine Lock
-- ----------------------------------------------------------------------------

/-- Mersenne `B1`-run state trajectory `p_k = B1^k(L(q0))` on a finite `K`-state left carrier. -/
def mersenneLeftSpine {K : Nat} (deltaL : MixedSRSSym -> Fin K -> Fin K)
    (q0 : Fin K) (k : Nat) : Fin K :=
  iterFin (deltaL .B1) k (deltaL .L q0)

def r8CycleParikhLhs {K M : Nat} (wt : MixedSRSSym -> Fin K -> Fin M -> Nat)
    (deltaL : MixedSRSSym -> Fin K -> Fin K) (q0 : Fin K) (aM : Fin M) (i : Nat) : Nat -> Nat
  | 0 => 0
  | t + 1 =>
    let pt := mersenneLeftSpine deltaL q0 (i + t)
    let pn := mersenneLeftSpine deltaL q0 (i + t + 1)
    (wt .T2 pt aM + wt .B1 pn aM) + r8CycleParikhLhs wt deltaL q0 aM i t

def r8CycleParikhRhs {K M : Nat} (wt : MixedSRSSym -> Fin K -> Fin M -> Nat)
    (deltaL : MixedSRSSym -> Fin K -> Fin K) (q0 : Fin K) (aM : Fin M) (i : Nat) : Nat -> Nat
  | 0 => 0
  | t + 1 =>
    let pt := mersenneLeftSpine deltaL q0 (i + t)
    let pn := mersenneLeftSpine deltaL q0 (i + t + 1)
    (wt .B1 pt aM + wt .T2 pn aM) + r8CycleParikhRhs wt deltaL q0 aM i t

theorem r8CycleParikh_telescopes {K M : Nat}
    (wt : MixedSRSSym -> Fin K -> Fin M -> Nat)
    (deltaL : MixedSRSSym -> Fin K -> Fin K) (q0 : Fin K) (aM : Fin M) (i : Nat) :
    ∀ d : Nat,
      r8CycleParikhLhs wt deltaL q0 aM i d + wt .T2 (mersenneLeftSpine deltaL q0 (i + d)) aM +
          wt .B1 (mersenneLeftSpine deltaL q0 i) aM =
        r8CycleParikhRhs wt deltaL q0 aM i d + wt .T2 (mersenneLeftSpine deltaL q0 i) aM +
          wt .B1 (mersenneLeftSpine deltaL q0 (i + d)) aM
  | 0 => by simp [r8CycleParikhLhs, r8CycleParikhRhs]
  | d + 1 => by
    have ih := r8CycleParikh_telescopes wt deltaL q0 aM i d
    simp only [r8CycleParikhLhs, r8CycleParikhRhs]
    rw [← Nat.add_assoc i d 1]
    omega

/--
  Theorem W11.1d (`universal_left_model_mersenne_b1_t2_lock`, choice-free `zero custom axioms`):
  Universal Finite-Carrier Mersenne `B1 / T2` Spine Lock & Cyclic `R8` Commutator Barrier (`∀ K, M ≥ 1`):
  Why EVERY finite two-sided Zantema carrier `(deltaL : Fin K) × (collatzSemMod M : Fin M)` fails
  to eliminate `R8 : [T2, B1] -> [B1, T2]` via Parikh rule removal even on reachable Mersenne states:
  For EVERY `K ≥ 1`, EVERY left-to-right model `deltaL : MixedSRSSym -> Fin K -> Fin K` preserving
  `R2` (`deltaL .B1 (deltaL .L q) = deltaL .T2 (deltaL .L q)`) and `R8`
  (`deltaL .B1 (deltaL .T2 q) = deltaL .T2 (deltaL .B1 q)`), and EVERY initial state `q0 : Fin K`:
  1. **Universal `T2 = B1` Spine Identity (`∀ k : Nat`)**:
     Along the `Z^+`-reachable Mersenne `1`-run spine `p_k := mersenneLeftSpine deltaL q0 k`
     (realized on `[.L] ++ encodePosBin (2 ^ m - 1) ++ [.R]`),
       `deltaL .T2 p_k = deltaL .B1 p_k = p_{k + 1}` identically for ALL `k : Nat`!
  2. **Closed Zero-Parikh-Change `R8` Cycle (`1 ≤ d ≤ K`, `d ∣ natFact K`)**:
     There exist `i < K` and `1 ≤ d ≤ K` (`d ∣ natFact K`) with `p_{i + d} = p_i`, so the `d`
     two-sided labelled `R8` rules at right state `a = M - 1` (`[(T2, p_{i+t}, M-1), (B1, p_{i+t+1}, M-1)]
     -> [(B1, p_{i+t}, M-1), (T2, p_{i+t+1}, M-1)]`) have IDENTICAL total LHS and RHS Parikh weight
     under EVERY symbol weight `wt : MixedSRSSym -> Fin K -> Fin M -> Nat` and EVERY `M ≥ 1`!
-/
theorem universal_left_model_mersenne_b1_t2_lock :
    ∀ (K M : Nat) (_hK : K ≥ 1) (hM : M ≥ 1)
      (deltaL : MixedSRSSym -> Fin K -> Fin K)
      (q0 : Fin K),
      (∀ q : Fin K, deltaL .B1 (deltaL .L q) = deltaL .T2 (deltaL .L q)) ->
      (∀ q : Fin K, deltaL .B1 (deltaL .T2 q) = deltaL .T2 (deltaL .B1 q)) ->
      (∀ k : Nat,
        deltaL .T2 (mersenneLeftSpine deltaL q0 k) =
          deltaL .B1 (mersenneLeftSpine deltaL q0 k) ∧
        deltaL .T2 (mersenneLeftSpine deltaL q0 k) =
          mersenneLeftSpine deltaL q0 (k + 1)) ∧
      ∃ (i d : Nat),
        i < K ∧ 1 ≤ d ∧ d ≤ K ∧ d ∣ natFact K ∧
        mersenneLeftSpine deltaL q0 (i + d) = mersenneLeftSpine deltaL q0 i ∧
        ∀ wt : MixedSRSSym -> Fin K -> Fin M -> Nat,
          r8CycleParikhLhs wt deltaL q0 ⟨M - 1, by omega⟩ i d =
            r8CycleParikhRhs wt deltaL q0 ⟨M - 1, by omega⟩ i d := by
  intro K M _hK hM deltaL q0 hr2 hr8
  have hlock : ∀ k : Nat,
      deltaL .T2 (mersenneLeftSpine deltaL q0 k) =
        deltaL .B1 (mersenneLeftSpine deltaL q0 k) := by
    intro k; induction k with
    | zero => exact (hr2 q0).symm
    | succ k' ih =>
      unfold mersenneLeftSpine at ih ⊢
      simp only [iterFin]
      rw [← hr8 (iterFin (deltaL .B1) k' (deltaL .L q0)), ih]
  refine ⟨fun k => ⟨hlock k, hlock k⟩, ?_⟩
  rcases nat_func_pigeonhole K (K + 1)
    (fun k => (mersenneLeftSpine deltaL q0 k).val)
    (fun k _ => (mersenneLeftSpine deltaL q0 k).isLt)
    (by omega) with ⟨i, j, hij, hj_lt, hval_eq⟩
  let d := j - i
  have hd1 : 1 ≤ d := by dsimp [d]; omega
  have hdK : d ≤ K := by dsimp [d]; omega
  have hid : i + d = j := by dsimp [d]; omega
  have hp_eq : mersenneLeftSpine deltaL q0 (i + d) = mersenneLeftSpine deltaL q0 i := by
    rw [hid]; exact (Fin.ext hval_eq).symm
  refine ⟨i, d, by omega, hd1, hdK, dvd_natFact d K hd1 hdK, hp_eq, ?_⟩
  intro wt
  have htel := r8CycleParikh_telescopes wt deltaL q0 ⟨M - 1, by omega⟩ i d
  rw [hp_eq] at htel
  omega

theorem nat_zero_ne_one_axfree (h : (0 : Nat) = 1) : False :=
  Eq.rec (motive := fun x _ => match x with | 0 => True | _ + 1 => False) trivial h

theorem nat_one_ne_zero_axfree (h : (1 : Nat) = 0) : False :=
  nat_zero_ne_one_axfree h.symm

/-- Fixed-point-free period-`2` `K = 2` left carrier preserving `R2` and `R8` (`0 <-> 1` on `B1, T2`). -/
def deltaL_flip2 (s : MixedSRSSym) (q : Fin 2) : Fin 2 :=
  match s with
  | .B1 =>
    match q.val with
    | 0 => ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩
    | _ + 1 => ⟨0, Nat.zero_lt_succ 1⟩
  | .T2 =>
    match q.val with
    | 0 => ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩
    | _ + 1 => ⟨0, Nat.zero_lt_succ 1⟩
  | .T1 => q
  | .L => ⟨0, Nat.zero_lt_succ 1⟩
  | .R => ⟨0, Nat.zero_lt_succ 1⟩
  | .B0 => ⟨0, Nat.zero_lt_succ 1⟩
  | .T0 => ⟨0, Nat.zero_lt_succ 1⟩

/--
  Theorem W11.1e (`deltaL_flip2_period2_no_fixed_point_cert`, `[]` axioms):
  Sharpness of `1 ≤ d ≤ K` in `universal_left_model_mersenne_b1_t2_lock`:
  `deltaL_flip2` preserves BOTH `R2` and `R8` on `Fin 2`, yet `deltaL_flip2 .B1` and
  `deltaL_flip2 .T2` have **ZERO fixed points** (`d = 1` fails identically; minimal period `d = 2`)!
-/
theorem deltaL_flip2_period2_no_fixed_point_cert :
    let z0 : Fin 2 := ⟨0, Nat.zero_lt_succ 1⟩
    let z1 : Fin 2 := ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩
    deltaL_flip2 .B1 (deltaL_flip2 .L z0) = deltaL_flip2 .T2 (deltaL_flip2 .L z0) ∧
    deltaL_flip2 .B1 (deltaL_flip2 .L z1) = deltaL_flip2 .T2 (deltaL_flip2 .L z1) ∧
    deltaL_flip2 .B1 (deltaL_flip2 .T2 z0) = deltaL_flip2 .T2 (deltaL_flip2 .B1 z0) ∧
    deltaL_flip2 .B1 (deltaL_flip2 .T2 z1) = deltaL_flip2 .T2 (deltaL_flip2 .B1 z1) ∧
    deltaL_flip2 .B1 z0 ≠ z0 ∧ deltaL_flip2 .B1 z1 ≠ z1 ∧
    deltaL_flip2 .T2 z0 ≠ z0 ∧ deltaL_flip2 .T2 z1 ≠ z1 ∧
    deltaL_flip2 .B1 (deltaL_flip2 .B1 z0) = z0 ∧
    deltaL_flip2 .B1 (deltaL_flip2 .B1 z1) = z1 :=
  ⟨rfl, rfl, rfl, rfl,
   fun h => nat_one_ne_zero_axfree (congrArg Fin.val h),
   fun h => nat_zero_ne_one_axfree (congrArg Fin.val h),
   fun h => nat_one_ne_zero_axfree (congrArg Fin.val h),
   fun h => nat_zero_ne_one_axfree (congrArg Fin.val h),
   rfl, rfl⟩

/-- Exact `K = 4` dyadic-fractional left semantic model `B_b(q) = ⌊(q + 4b)/2⌋`, `T_c(q) = ⌊(q + 4c)/3⌋`. -/
def collatzSemL4 (s : MixedSRSSym) (q : Fin 4) : Fin 4 :=
  match s with
  | .L | .R => ⟨0, by decide⟩
  | .B0 =>
    match q.val with
    | 0 | 1 => ⟨0, by decide⟩
    | _ => ⟨1, by decide⟩
  | .B1 =>
    match q.val with
    | 0 | 1 => ⟨2, by decide⟩
    | _ => ⟨3, by decide⟩
  | .T0 =>
    match q.val with
    | 0 | 1 | 2 => ⟨0, by decide⟩
    | _ => ⟨1, by decide⟩
  | .T1 =>
    match q.val with
    | 0 | 1 => ⟨1, by decide⟩
    | _ => ⟨2, by decide⟩
  | .T2 =>
    match q.val with
    | 0 => ⟨2, by decide⟩
    | _ => ⟨3, by decide⟩

/-- Exact `K = 2` non-zero-seen indicator (`0 -> 1` upon reading `B1, T1, T2`). -/
def collatzSemSeen (s : MixedSRSSym) (q : Fin 2) : Fin 2 :=
  match s with
  | .L | .R => ⟨0, by decide⟩
  | .B0 | .T0 => q
  | .B1 | .T1 | .T2 => ⟨1, by decide⟩

/-- Exact `K = 8` (`collatzSemL4 × collatzSemSeen`) left semantic model separating `(0, 0)` from `(0, 1)`. -/
def collatzSemL8 (s : MixedSRSSym) (q : Fin 8) : Fin 8 :=
  let q4 : Fin 4 :=
    match q.val with
    | 0 | 1 => ⟨0, by decide⟩
    | 2 | 3 => ⟨1, by decide⟩
    | 4 | 5 => ⟨2, by decide⟩
    | _ => ⟨3, by decide⟩
  let q2 : Fin 2 :=
    match q.val with
    | 0 | 2 | 4 | 6 => ⟨0, by decide⟩
    | _ => ⟨1, by decide⟩
  ⟨2 * (collatzSemL4 s q4).val + (collatzSemSeen s q2).val, by
    have h4 := (collatzSemL4 s q4).isLt
    have h2 := (collatzSemSeen s q2).isLt
    omega⟩

/-- Left-to-right word action `evalSemLeft deltaL w q` on `Fin K`. -/
def evalSemLeft {K : Nat} (deltaL : MixedSRSSym -> Fin K -> Fin K) :
    List MixedSRSSym -> Fin K -> Fin K
  | [], q => q
  | s :: rest, q => evalSemLeft deltaL rest (deltaL s q)

/--
  Theorem W11.1f (`higher_left_carriers_k4_k8_and_mersenne_r8_lock`, `choice-free, zero custom axioms`):
  Exact `K ∈ {4, 8}` Left Semantic Models & `M ∈ {6, 12, 18}` Reachable Mersenne `R8` Swap Barrier:
  1. Both `collatzSemL4` (`Fin 4`) and `collatzSemL8` (`Fin 8`) are exact left semantic models
     preserving ALL `11/11` Collatz rules `r ∈ all11RuleList` from every state!
  2. Along the `Z^+`-reachable Mersenne `1`-spine (`2^m - 1`, `m ≥ 2`), `collatzSemL4` reaches
     fixed state `3 : Fin 4` (`mersenneLeftSpine collatzSemL4 0 2 = 3`) and `collatzSemL8` reaches
     fixed state `7 : Fin 8` (`mersenneLeftSpine collatzSemL8 0 2 = 7`), where `B1` and `T2` both
     fix the state while right-to-left `collatzSemMod M` (`M ∈ {6, 12, 18}`) fixes `M - 1`, locking
     `R8` into a pure single-rule commutator swap across all `K ∈ {2, 4, 8}`, `M ∈ {6, 12, 18}`!
-/
theorem higher_left_carriers_k4_k8_and_mersenne_r8_lock :
    (∀ r : List MixedSRSSym × List MixedSRSSym, r ∈ all11RuleList ->
      (∀ q : Fin 4, evalSemLeft collatzSemL4 r.1 q = evalSemLeft collatzSemL4 r.2 q) ∧
      (∀ q : Fin 8, evalSemLeft collatzSemL8 r.1 q = evalSemLeft collatzSemL8 r.2 q)) ∧
    (mersenneLeftSpine collatzSemL4 ⟨0, by decide⟩ 2 = ⟨3, by decide⟩ ∧
     collatzSemL4 .B1 ⟨3, by decide⟩ = ⟨3, by decide⟩ ∧
     collatzSemL4 .T2 ⟨3, by decide⟩ = ⟨3, by decide⟩) ∧
    (mersenneLeftSpine collatzSemL8 ⟨0, by decide⟩ 2 = ⟨7, by decide⟩ ∧
     collatzSemL8 .B1 ⟨7, by decide⟩ = ⟨7, by decide⟩ ∧
     collatzSemL8 .T2 ⟨7, by decide⟩ = ⟨7, by decide⟩) ∧
    (∀ M : Nat, (M = 6 ∨ M = 12 ∨ M = 18) ->
      collatzSemMod M .B1 (M - 1) = M - 1 ∧
      collatzSemMod M .T2 (M - 1) = M - 1) := by
  have hex4 : ∀ r ∈ all11RuleList, ∀ q : Fin 4,
      evalSemLeft collatzSemL4 r.1 q = evalSemLeft collatzSemL4 r.2 q := by decide
  have hex8 : ∀ r ∈ all11RuleList, ∀ q : Fin 8,
      evalSemLeft collatzSemL8 r.1 q = evalSemLeft collatzSemL8 r.2 q := by decide
  refine ⟨fun r hr => ⟨hex4 r hr, hex8 r hr⟩,
          ⟨by decide, by decide, by decide⟩,
          ⟨by decide, by decide, by decide⟩,
          ?_⟩
  intro M hM
  rcases hM with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

-- ============================================================================
-- SECTION 2: Front B (Branches P3.4 & P3.3) — Complete Mod-`24` Classification,
--            Universal `ℓ`-Sylow Obstructions, Universal `(T + 1) × (T + 1)`
--            Single-Base + Upgraded Confluent Extrapolation + Laplace Bound,
--            & Exact Rank-2 `6 × 6` Two-Base `(T = 3, U = 2)` Cone Positivity
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Section 2A: Complete Mod-`24` `2`-Adic Reciprocity & Universal `ℓ`-Sylow Lock
-- ----------------------------------------------------------------------------

theorem pow_mul_mod_distrib_w11 (q a b : Nat) :
    ∀ k : Nat, (a * b) ^ k % q = (a ^ k * b ^ k) % q
  | 0 => rfl
  | k + 1 => by
    rw [Nat.pow_succ (a * b) k, Nat.pow_succ a k, Nat.pow_succ b k,
        Nat.mul_mod ((a * b) ^ k) (a * b) q, pow_mul_mod_distrib_w11 q a b k,
        ← Nat.mul_mod]
    apply congrArg (· % q)
    rw [Nat.mul_assoc (a ^ k) (b ^ k) (a * b),
        ← Nat.mul_assoc (b ^ k) a b, Nat.mul_comm (b ^ k) a,
        Nat.mul_assoc a (b ^ k) b, ← Nat.mul_assoc (a ^ k) a]

theorem two_mul_ratio32Mod_eq_three (q : Nat) (hq_odd : q % 2 = 1) (hq5 : q ≥ 5) :
    (2 * ratio32Mod q) % q = 3 := by
  unfold ratio32Mod
  have h2inv : 2 * ((q + 1) / 2) = 1 + q := by omega
  calc
    (2 * ((3 * ((q + 1) / 2)) % q)) % q
        = (2 * (3 * ((q + 1) / 2))) % q := by rw [Nat.mul_mod 2 _ q, Nat.mod_mod, ← Nat.mul_mod]
    _ = (3 * (2 * ((q + 1) / 2))) % q := by rw [← Nat.mul_assoc 2 3, Nat.mul_comm 2 3, Nat.mul_assoc]
    _ = (3 + q * 3) % q := by rw [h2inv, Nat.mul_add, Nat.mul_one, Nat.mul_comm 3 q]
    _ = 3 := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- Universal `ℓ`-Sylow Order-Lock (`choice-free, zero custom axioms`): if `q - 1 = ℓ ^ e * m` with `ℓ` prime and `b ^ m % q ≠ 1`, then `ℓ ∣ ord_q(b)`. -/
theorem sylow_prime_dvd_order_of_pow_ne_one (q ell e m b d : Nat)
    (hq : IsPrimeNat q) (hell : IsPrimeNat ell) (_he : e ≥ 1)
    (hqm1 : q - 1 = ell ^ e * m)
    (hnd : ¬ (q ∣ b)) (hord : IsExactMultOrderMod q b d)
    (hne1 : b ^ m % q ≠ 1) :
    ell ∣ d := by
  have hq2 := hq.1
  have hell2 := hell.1
  have hdvd_tot : d ∣ (ell ^ e * m) := by
    rw [← hqm1]
    exact exactMultOrderMod_dvd_of_pow_eq_one q b d (q - 1) hord
      (fermat_little_mod_prime q b hq hnd)
  have hnot_dvd_m : ¬ (d ∣ m) := by
    rintro ⟨c, hc⟩
    rw [hc, ← pow_pow_eq_mul_w5 b d c,
        pow_mod_eq_of_mod_eq_w5 q (b ^ d) 1
          (by rw [hord.2.2.1, Nat.mod_eq_of_lt (by omega : 1 < q)]) c,
        Nat.one_pow, Nat.mod_eq_of_lt (by omega : 1 < q)] at hne1
    exact hne1 rfl
  by_cases hdiv : ell ∣ d
  · exact hdiv
  · exfalso
    -- Since `ell` is prime and `¬(ell ∣ d)`, `Nat.gcd d ell = 1`, hence `d ∣ m` by induction on `e`!
    have hgcd1 : Nat.gcd d ell = 1 := by
      let g := Nat.gcd d ell
      have hg_ell : g ∣ ell := Nat.gcd_dvd_right d ell
      have hg_d : g ∣ d := Nat.gcd_dvd_left d ell
      have hg_pos : g ≥ 1 := Nat.gcd_pos_of_pos_right d (by omega)
      by_cases hg1 : g = 1
      · exact hg1
      · by_cases hge : g = ell
        · exact False.elim (hdiv (hge ▸ hg_d))
        · have hg_le : g ≤ ell := Nat.le_of_dvd (by omega) hg_ell
          exact False.elim (hell.2 g (by omega) (by omega) hg_ell)
    have hpeel : ∀ k : Nat, d ∣ (ell ^ k * m) -> d ∣ m := by
      intro k; induction k with
      | zero => simp
      | succ k' ih =>
        intro hk
        rw [Nat.pow_succ ell k', Nat.mul_comm (ell ^ k') ell, Nat.mul_assoc ell] at hk
        exact ih (coprime_dvd_of_dvd_mul_aux (d + ell) d ell (ell ^ k' * m)
          (Nat.le_refl _) hgcd1 hk)
    exact hnot_dvd_m (hpeel e hdvd_tot)

/-- Higher `2`-adic Sylow Lock (`choice-free`): if `(q - 1) = 2 ^ e * r`, `b ^ ((q - 1) / 2) % q = q - 1`, and `d = ord_q(b)`, then `2 ^ e ∣ d` (`v_2(d) = v_2(q - 1)`). -/
theorem full_two_sylow_dvd_order_of_half_minus_one (q e r b d : Nat)
    (hq : IsPrimeNat q) (hq5 : q ≥ 5) (he : e ≥ 1)
    (hqm1 : q - 1 = 2 ^ e * r)
    (hnd : ¬ (q ∣ b)) (hord : IsExactMultOrderMod q b d)
    (hhalf : b ^ ((q - 1) / 2) % q = q - 1) :
    2 ^ e ∣ d := by
  have hdvd_tot : d ∣ (2 ^ e * r) := by
    rw [← hqm1]
    exact exactMultOrderMod_dvd_of_pow_eq_one q b d (q - 1) hord
      (fermat_little_mod_prime q b hq hnd)
  have hh_eq : (q - 1) / 2 = 2 ^ (e - 1) * r := by
    have hp : 2 ^ e * r = 2 * (2 ^ (e - 1) * r) := by
      conv => lhs; rw [show e = (e - 1) + 1 by omega, Nat.pow_succ,
        Nat.mul_comm (2 ^ (e - 1)) 2, Nat.mul_assoc]
    omega
  have hnot_dvd_half : ¬ (d ∣ (2 ^ (e - 1) * r)) := by
    rintro ⟨c, hc⟩
    rw [hh_eq, hc, ← pow_pow_eq_mul_w5 b d c,
        pow_mod_eq_of_mod_eq_w5 q (b ^ d) 1
          (by rw [hord.2.2.1, Nat.mod_eq_of_lt (by omega : 1 < q)]) c,
        Nat.one_pow, Nat.mod_eq_of_lt (by omega : 1 < q)] at hhalf
    omega
  -- Peel `2` from `(d, 2^e)` `e` times:
  have hstep_2 : ∀ (k d_cur : Nat),
      k ≥ 1 ->
      d_cur ∣ (2 ^ k * r) ->
      ¬ (d_cur ∣ (2 ^ (k - 1) * r)) ->
      2 ^ k ∣ d_cur := by
    intro k; induction k with
    | zero => intro _ hk; omega
    | succ k' ih =>
      intro d_cur _ hd_k1 hnd_k
      simp only [Nat.add_sub_cancel] at hnd_k
      have h2_d : 2 ∣ d_cur := by
        by_cases hev : d_cur % 2 = 0
        · exact Nat.dvd_of_mod_eq_zero hev
        · have hgcd : Nat.gcd d_cur 2 = 1 := by
            rw [Nat.gcd_comm, Nat.gcd_rec 2 d_cur, show d_cur % 2 = 1 by omega]; decide
          rw [Nat.pow_succ 2 k', Nat.mul_comm (2 ^ k') 2, Nat.mul_assoc 2] at hd_k1
          exact False.elim (hnd_k
            (coprime_dvd_of_dvd_mul_aux (d_cur + 2) d_cur 2 (2 ^ k' * r) (Nat.le_refl _) hgcd hd_k1))
      rcases h2_d with ⟨d_half, rfl⟩
      cases k' with
      | zero => exact ⟨d_half, by simp⟩
      | succ k'' =>
        have hd_sub : d_half ∣ (2 ^ (k'' + 1) * r) := by
          rcases hd_k1 with ⟨m, hm⟩
          rw [Nat.pow_succ 2 (k'' + 1), Nat.mul_comm (2 ^ (k'' + 1)) 2,
              Nat.mul_assoc 2, Nat.mul_assoc 2 d_half m] at hm
          exact ⟨m, by omega⟩
        have hnd_sub : ¬ (d_half ∣ (2 ^ k'' * r)) := by
          rintro ⟨m, hm⟩
          apply hnd_k
          refine ⟨m, ?_⟩
          rw [Nat.pow_succ 2 k'', Nat.mul_comm (2 ^ k'') 2, Nat.mul_assoc 2,
              hm, Nat.mul_assoc 2 d_half m]
        rcases ih d_half (by omega) hd_sub hnd_sub with ⟨u, hu⟩
        refine ⟨u, ?_⟩
        rw [hu, Nat.pow_succ 2 (k'' + 1), Nat.mul_comm (2 ^ (k'' + 1)) 2, Nat.mul_assoc]
  exact hstep_2 e d he hdvd_tot hnot_dvd_half

/--
  Theorem W11.2a (`complete_mod24_and_sylow_reciprocity_obstructions`, `zero custom axioms`):
  Complete Mod-`24` `2`-Adic Reciprocity Classification & Universal `ℓ`-Sylow (`mod 72, 96, 240`)
  1-Block Exclusions + Shared-Mersenne 2-Block `(123, 195)`, `(205, 325)`, & `(328, 520)` Floors:
  1. **Universal `{7, 19, 23} mod 24` Odd-`gcd` Barrier**:
     For EVERY prime `q` with `q % 24 ∈ {7, 19, 23}`, `Nat.gcd (ord_q(2)) (ord_q(3/2)) % 2 = 1`
     (`v_2(q - 1) = 1`, and either `2^((q-1)/2) ≡ 1` or `(3/2)^((q-1)/2) ≡ 1 (mod q)`)!
  2. **Exact Quartic `q % 24 = 5` `6^((q-1)/4)` Biconditional & Octic `q % 24 = 17` `8 ∣ ord_q(3/2)` Lock**:
     - For EVERY prime `q % 24 = 5`: `2 ∣ Nat.gcd d2 d32 ↔ 6 ^ ((q - 1) / 4) % q = 1`!
       Excludes ALL `q % 24 = 5` with `6 ^ ((q - 1) / 4) % q = 1` from 1-block `Z^+` cycles
       (certified at `q = 5, 149, 173`, vs `q = 29` odd-`gcd` escape `6 ^ 7 % 29 = 28`!).
     - For EVERY prime `q % 24 = 17`: `8 ∣ d32` (`v_2(d32) = v_2(q - 1) ≥ 3`), and at `q = 17`,
       `8 ∣ Nat.gcd d2 d32` (excluding 1-block cycles and forcing `(328, 520)` on 2-block cycles,
       vs `q = 89` odd-`ord_89(2) = 11` escape!).
  3. **Universal `ℓ`-Sylow Order-Lock (`∀ q, ℓ, e, m`) & Cubic / Quintic / Octic 2-Block Floors**:
     Whenever `q - 1 = ℓ ^ e * m` (`IsPrimeNat q`, `IsPrimeNat ℓ`, `e ≥ 1`, `m ≥ 1`) with
     `2 ^ m % q ≠ 1` and `(ratio32Mod q) ^ m % q ≠ 1`:
     - `ℓ ∣ Nat.gcd d2 d32` (`Nat.gcd d2 d32 ≥ ℓ ≥ 2`), unconditionally excluding `q ∣ (2^(w1+a1) - 3^w1)`
       on ALL 1-block `Z^+` cycles!
     - On ANY primitive shared-Mersenne 2-block cycle (`q ∣ gcd(D, 2^a1 - 1)`), `ℓ ∣ a1 ∧ ℓ ∣ a2 ∧
       ℓ ∣ (w1 + w2) ∧ w1 + w2 ≥ 41 * ℓ ∧ w1 + a1 + w2 + a2 ≥ 65 * ℓ` (`ℓ = 3 => (123, 195)`,
       certified at `q = 7, 19, 67, 73, 103, 139`; `ℓ = 5 => (205, 325)`, certified at
       `q = 31, 101, 191, 211`)!
-/
theorem complete_mod24_and_sylow_reciprocity_obstructions :
    -- Part 1: `{7, 19, 23} mod 24` universal odd-`gcd`:
    (∀ q d2 d32 : Nat,
      IsPrimeNat q ->
      (q % 24 = 7 ∨ q % 24 = 19 ∨ q % 24 = 23) ->
      IsExactMultOrderMod q 2 d2 ->
      IsExactMultOrderMod q (ratio32Mod q) d32 ->
      Nat.gcd d2 d32 % 2 = 1) ∧
    -- Part 2a: Quartic `q % 24 = 5` exact `6^((q - 1)/4)` biconditional + 1-block exclusion:
    ((∀ q d2 d32 : Nat,
        IsPrimeNat q -> q % 24 = 5 ->
        IsExactMultOrderMod q 2 d2 ->
        IsExactMultOrderMod q (ratio32Mod q) d32 ->
        2 ∣ d2 ∧ (2 ∣ Nat.gcd d2 d32 ↔ 6 ^ ((q - 1) / 4) % q = 1)) ∧
     (∀ w1 a1 q0 q : Nat,
        w1 ≥ 2 -> a1 ≥ 1 -> q0 ≥ 1 -> 3 ^ w1 < 2 ^ (w1 + a1) ->
        (2 ^ (w1 + a1) - 3 ^ w1) * q0 = 2 ^ a1 - 1 ->
        IsPrimeNat q -> q % 24 = 5 -> 6 ^ ((q - 1) / 4) % q = 1 ->
        ¬ (q ∣ (2 ^ (w1 + a1) - 3 ^ w1))) ∧
     6 ^ ((5 - 1) / 4) % 5 = 1 ∧
     6 ^ ((149 - 1) / 4) % 149 = 1 ∧
     6 ^ ((173 - 1) / 4) % 173 = 1 ∧
     6 ^ ((29 - 1) / 4) % 29 = 28) ∧
    -- Part 2b: Octic `q % 24 = 17` universal `8 ∣ ord_q(3/2)` lock + `q = 17` vs `q = 89` dichotomy:
    ((∀ q d32 : Nat,
        IsPrimeNat q -> q % 24 = 17 ->
        IsExactMultOrderMod q (ratio32Mod q) d32 ->
        8 ∣ d32 ∧ d32 ≥ 8) ∧
     IsExactMultOrderMod 17 2 8 ∧
     IsExactMultOrderMod 17 (ratio32Mod 17) 16 ∧
     IsExactMultOrderMod 89 2 11 ∧
     (2 ^ 11) % 89 = 1) ∧
    -- Part 3: Universal `ℓ`-Sylow 1-block exclusion & 2-block `(41 * ℓ, 65 * ℓ)` (`(123, 195)`, `(205, 325)`) floors:
    ((∀ (q ell e m d2 d32 : Nat),
        IsPrimeNat q -> q ≥ 5 -> IsPrimeNat ell -> e ≥ 1 -> m ≥ 1 ->
        q - 1 = ell ^ e * m ->
        IsExactMultOrderMod q 2 d2 ->
        IsExactMultOrderMod q (ratio32Mod q) d32 ->
        2 ^ m % q ≠ 1 -> (ratio32Mod q) ^ m % q ≠ 1 ->
        ell ∣ Nat.gcd d2 d32 ∧ Nat.gcd d2 d32 ≥ ell) ∧
     (∀ (w1 a1 q0 q ell e m : Nat),
        w1 ≥ 2 -> a1 ≥ 1 -> q0 ≥ 1 -> 3 ^ w1 < 2 ^ (w1 + a1) ->
        (2 ^ (w1 + a1) - 3 ^ w1) * q0 = 2 ^ a1 - 1 ->
        IsPrimeNat q -> q ≥ 5 -> IsPrimeNat ell -> e ≥ 1 -> m ≥ 1 ->
        q - 1 = ell ^ e * m ->
        2 ^ m % q ≠ 1 -> (ratio32Mod q) ^ m % q ≠ 1 ->
        ¬ (q ∣ (2 ^ (w1 + a1) - 3 ^ w1))) ∧
     (∀ (w1 a1 w2 a2 q0 q1 q ell e m : Nat),
        IsPrimitiveTwoBlockBroxWitness w1 a1 w2 a2 q0 q1 ->
        IsPrimeNat q -> q ≥ 5 -> IsPrimeNat ell -> e ≥ 1 -> m ≥ 1 ->
        q - 1 = ell ^ e * m ->
        2 ^ m % q ≠ 1 -> (ratio32Mod q) ^ m % q ≠ 1 ->
        q ∣ (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)) ->
        q ∣ (2 ^ a1 - 1) ->
        ell ∣ a1 ∧ ell ∣ a2 ∧ ell ∣ (w1 + w2) ∧
        w1 + w2 ≥ 41 * ell ∧ w1 + a1 + w2 + a2 ≥ 65 * ell) ∧
     -- Concrete cubic (`q = 73`, `73 ≡ 1 mod 72`, `(123, 195)`) & quintic (`q = 31`, `(205, 325)`) certificates:
     (IsPrimeNat 73 ∧ 73 % 72 = 1 ∧ 73 - 1 = 3 ^ 2 * 8 ∧
      2 ^ 8 % 73 ≠ 1 ∧ (ratio32Mod 73) ^ 8 % 73 ≠ 1 ∧ 41 * 3 = 123 ∧ 65 * 3 = 195) ∧
     (IsPrimeNat 31 ∧ 31 - 1 = 5 ^ 1 * 6 ∧
      2 ^ 6 % 31 ≠ 1 ∧ (ratio32Mod 31) ^ 6 % 31 ≠ 1 ∧ 41 * 5 = 205 ∧ 65 * 5 = 325)) := by
  have hnd2_of : ∀ q : Nat, q ≥ 5 -> ¬ (q ∣ 2) := by
    intro q hq5 ⟨c, hc⟩
    cases c with
    | zero => simp at hc
    | succ c' => have := Nat.mul_le_mul_left q (by omega : 1 ≤ c' + 1); omega
  have hnd3_of : ∀ q : Nat, q ≥ 5 -> ¬ (q ∣ 3) := by
    intro q hq5 ⟨c, hc⟩
    cases c with
    | zero => simp at hc
    | succ c' => have := Nat.mul_le_mul_left q (by omega : 1 ≤ c' + 1); omega
  have hnd32_of : ∀ q : Nat, q % 2 = 1 -> q ≥ 5 -> ¬ (q ∣ ratio32Mod q) := by
    intro q hqo hq5 ⟨c, hc⟩
    have h2r := two_mul_ratio32Mod_eq_three q hqo hq5
    rw [hc, ← Nat.mul_assoc 2 q c, Nat.mul_comm 2 q, Nat.mul_assoc q 2 c, Nat.mul_mod_right] at h2r
    omega
  have hodd_of_dvd_odd : ∀ (a b : Nat), a ∣ b -> b % 2 = 1 -> a % 2 = 1 := by
    intro a b ⟨c, hc⟩ hb
    by_cases ha0 : a % 2 = 0
    · rw [hc, Nat.mul_mod, ha0, Nat.zero_mul, Nat.zero_mod] at hb; cases hb
    · omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Part 1: `{7, 19, 23} mod 24` forces `gcd(d2, d32)` odd:
    intro q d2 d32 hq hmod24 hd2 hd32
    let h := (q - 1) / 2
    have hq7 : q ≥ 7 := by omega
    have hqo : q % 2 = 1 := by omega
    have hq_nd3 : q % 3 ≠ 0 := by omega
    have hh_odd : h % 2 = 1 := by dsimp [h]; omega
    rcases hmod24 with h7 | h19 | h23
    · -- `q % 24 = 7`: `gaussUpperCount q 2 h` is even (`2^h % q = 1`), so `d2 ∣ h`, hence `d2` odd!
      have hc2 := gaussUpperCount_two_eq q hqo (by omega) h (Nat.le_refl h)
      rw [Nat.min_eq_right (by dsimp [h]; omega)] at hc2
      have hev2 : gaussUpperCount q 2 h % 2 = 0 := by rw [hc2]; dsimp [h]; omega
      have hp2 := (gauss_lemma_mod_prime q 2 hq hqo (by omega) (hnd2_of q (by omega))).1 hev2
      have hd2_h := exactMultOrderMod_dvd_of_pow_eq_one q 2 d2 h hd2 hp2
      exact hodd_of_dvd_odd _ d2 (Nat.gcd_dvd_left d2 d32) (hodd_of_dvd_odd d2 h hd2_h hh_odd)
    · -- `q % 24 = 19`: `2^h % q = q - 1` and `3^h % q = q - 1`, so `(3/2)^h % q = 1`, hence `d32 ∣ h` odd!
      have hc2 := gaussUpperCount_two_eq q hqo (by omega) h (Nat.le_refl h)
      have hc3 := gaussUpperCount_three_eq q hqo (by omega) hq_nd3 h (Nat.le_refl h)
      rw [Nat.min_eq_right (by dsimp [h]; omega)] at hc2
      rw [Nat.min_eq_right (by dsimp [h]; omega), Nat.min_eq_right (by dsimp [h]; omega)] at hc3
      have ho2 : gaussUpperCount q 2 h % 2 = 1 := by rw [hc2]; dsimp [h]; omega
      have ho3 : gaussUpperCount q 3 h % 2 = 1 := by rw [hc3]; omega
      have hp2 := (gauss_lemma_mod_prime q 2 hq hqo (by omega) (hnd2_of q (by omega))).2 ho2
      have hp3 := (gauss_lemma_mod_prime q 3 hq hqo (by omega) (hnd3_of q (by omega))).2 ho3
      have h2r := two_mul_ratio32Mod_eq_three q hqo (by omega)
      have hmul_h : ((q - 1) * (ratio32Mod q) ^ h) % q = ((q - 1) * 1) % q := by
        have h1 : (2 ^ h * (ratio32Mod q) ^ h) % q = q - 1 := by
          rw [← pow_mul_mod_distrib_w11 q 2 (ratio32Mod q) h,
              pow_mod_eq_of_mod_eq_w5 q (2 * ratio32Mod q) 3
                (by rw [h2r, Nat.mod_eq_of_lt (by omega)]) h,
              hp3]
        rw [Nat.mul_mod (2 ^ h) _ q, hp2, ← Nat.mod_eq_of_lt (by omega : q - 1 < q), ← Nat.mul_mod] at h1
        rw [h1, Nat.mul_one, Nat.mod_eq_of_lt (by omega)]
      have hnd_qm1 : ¬ (q ∣ (q - 1)) := by
        rintro ⟨c, hc⟩; cases c with
        | zero => simp at hc; omega
        | succ c' => have := Nat.mul_le_mul_left q (by omega : 1 ≤ c' + 1); omega
      have hp32 : (ratio32Mod q) ^ h % q = 1 := by
        have hc := cancel_mul_mod_prime q (q - 1) ((ratio32Mod q) ^ h) 1 hq hnd_qm1 hmul_h
        rwa [Nat.mod_eq_of_lt (by omega : 1 < q)] at hc
      have hd32_h := exactMultOrderMod_dvd_of_pow_eq_one q (ratio32Mod q) d32 h hd32 hp32
      exact hodd_of_dvd_odd _ d32 (Nat.gcd_dvd_right d2 d32) (hodd_of_dvd_odd d32 h hd32_h hh_odd)
    · -- `q % 24 = 23`: `2^h % q = 1`, so `d2 ∣ h`, hence `d2` odd!
      have hc2 := gaussUpperCount_two_eq q hqo (by omega) h (Nat.le_refl h)
      rw [Nat.min_eq_right (by dsimp [h]; omega)] at hc2
      have hev2 : gaussUpperCount q 2 h % 2 = 0 := by rw [hc2]; dsimp [h]; omega
      have hp2 := (gauss_lemma_mod_prime q 2 hq hqo (by omega) (hnd2_of q (by omega))).1 hev2
      have hd2_h := exactMultOrderMod_dvd_of_pow_eq_one q 2 d2 h hd2 hp2
      exact hodd_of_dvd_odd _ d2 (Nat.gcd_dvd_left d2 d32) (hodd_of_dvd_odd d2 h hd2_h hh_odd)
  · -- Part 2a: Quartic `q % 24 = 5` biconditional `2 ∣ gcd(d2, d32) ↔ 6^((q - 1)/4) % q = 1`:
    have hq5_law : ∀ q d2 d32 : Nat,
        IsPrimeNat q -> q % 24 = 5 ->
        IsExactMultOrderMod q 2 d2 ->
        IsExactMultOrderMod q (ratio32Mod q) d32 ->
        2 ∣ d2 ∧ (2 ∣ Nat.gcd d2 d32 ↔ 6 ^ ((q - 1) / 4) % q = 1) := by
      intro q d2 d32 hq h5 hd2 hd32
      let m := (q - 1) / 4
      let h := (q - 1) / 2
      have hq5 : q ≥ 5 := by omega
      have hqo : q % 2 = 1 := by omega
      have hq_nd3 : q % 3 ≠ 0 := by omega
      have hm_odd : m % 2 = 1 := by dsimp [m]; omega
      have hh_2m : h = 2 * m := by dsimp [h, m]; omega
      have hqm1_4m : q - 1 = 2 ^ 2 * m := by dsimp [m]; omega
      have hc2 := gaussUpperCount_two_eq q hqo hq5 h (Nat.le_refl h)
      have hc3 := gaussUpperCount_three_eq q hqo hq5 hq_nd3 h (Nat.le_refl h)
      rw [Nat.min_eq_right (by dsimp [h]; omega)] at hc2
      rw [Nat.min_eq_right (by dsimp [h]; omega), Nat.min_eq_right (by dsimp [h]; omega)] at hc3
      have ho2 : gaussUpperCount q 2 h % 2 = 1 := by rw [hc2]; dsimp [h]; omega
      have ho3 : gaussUpperCount q 3 h % 2 = 1 := by rw [hc3]; omega
      have hp2 := (gauss_lemma_mod_prime q 2 hq hqo hq5 (hnd2_of q hq5)).2 ho2
      have hp3 := (gauss_lemma_mod_prime q 3 hq hqo hq5 (hnd3_of q hq5)).2 ho3
      have h4_d2 := full_two_sylow_dvd_order_of_half_minus_one q 2 m 2 d2
        hq hq5 (by decide) hqm1_4m (hnd2_of q hq5) hd2 hp2
      have h2_d2 : 2 ∣ d2 := Nat.dvd_trans (by decide : 2 ∣ 4) h4_d2
      -- `(ratio32Mod q)^h % q = 1`:
      have h2r := two_mul_ratio32Mod_eq_three q hqo hq5
      have hnd_qm1 : ¬ (q ∣ (q - 1)) := by
        rintro ⟨c, hc⟩; cases c with
        | zero => simp at hc; omega
        | succ c' => have := Nat.mul_le_mul_left q (by omega : 1 ≤ c' + 1); omega
      have hp32_h : (ratio32Mod q) ^ h % q = 1 := by
        have h1 : (2 ^ h * (ratio32Mod q) ^ h) % q = q - 1 := by
          rw [← pow_mul_mod_distrib_w11 q 2 (ratio32Mod q) h,
              pow_mod_eq_of_mod_eq_w5 q (2 * ratio32Mod q) 3
                (by rw [h2r, Nat.mod_eq_of_lt (by omega)]) h,
              hp3]
        rw [Nat.mul_mod (2 ^ h) _ q, hp2, ← Nat.mod_eq_of_lt (by omega : q - 1 < q), ← Nat.mul_mod] at h1
        have hm1 : ((q - 1) * (ratio32Mod q) ^ h) % q = ((q - 1) * 1) % q := by
          rw [h1, Nat.mul_one, Nat.mod_eq_of_lt (by omega)]
        have hc := cancel_mul_mod_prime q (q - 1) ((ratio32Mod q) ^ h) 1 hq hnd_qm1 hm1
        rwa [Nat.mod_eq_of_lt (by omega : 1 < q)] at hc
      have hd32_2m : d32 ∣ (2 * m) := by
        rw [← hh_2m]
        exact exactMultOrderMod_dvd_of_pow_eq_one q (ratio32Mod q) d32 h hd32 hp32_h
      -- Relate `6^m % q` and `(ratio32Mod q)^m % q`: since `(4 * ratio32Mod q) % q = 6 % q`,
      -- `6^m % q = (4^m * (ratio32Mod q)^m) % q = ((q - 1) * (ratio32Mod q)^m) % q`!
      have h4r_6 : (4 * ratio32Mod q) % q = 6 % q := by
        have hcalc : (2 * (2 * ratio32Mod q)) % q = (2 * 3) % q := by
          rw [Nat.mul_mod 2 (2 * ratio32Mod q) q, h2r,
              Nat.mul_mod 2 3 q, Nat.mod_eq_of_lt (by omega : 3 < q)]
        rwa [← Nat.mul_assoc 2 2] at hcalc
      have h4m_qm1 : 4 ^ m % q = q - 1 := by
        have h4eq : 4 ^ m = 2 ^ h := by
          rw [hh_2m, show (4 : Nat) = 2 ^ 2 from rfl, pow_pow_eq_mul_w5 2 2 m]
        rw [h4eq, hp2]
      have h6m_rel : 6 ^ m % q = ((q - 1) * ((ratio32Mod q) ^ m % q)) % q := by
        calc
          6 ^ m % q
              = (4 * ratio32Mod q) ^ m % q :=
                (pow_mod_eq_of_mod_eq_w5 q (4 * ratio32Mod q) 6 h4r_6 m).symm
          _ = (4 ^ m * (ratio32Mod q) ^ m) % q := pow_mul_mod_distrib_w11 q 4 (ratio32Mod q) m
          _ = ((4 ^ m % q) * ((ratio32Mod q) ^ m % q)) % q := Nat.mul_mod _ _ q
          _ = ((q - 1) * ((ratio32Mod q) ^ m % q)) % q := by rw [h4m_qm1]
      -- Also `((ratio32Mod q)^m % q)` is a root of `x^2 ≡ 1 (mod q)`, so it is EITHER `1` OR `q - 1`!
      let rm := (ratio32Mod q) ^ m % q
      have hrm_lt : rm < q := Nat.mod_lt _ (by omega)
      have hrm_sq : (rm * rm) % q = 1 := by
        dsimp [rm]
        rw [← Nat.mul_mod, ← Nat.pow_add, show m + m = h by omega, hp32_h]
      have hrm_dich : rm = 1 ∨ rm = q - 1 := by
        -- `q ∣ ((rm - 1) * (rm + 1))`:
        have hrm_pos : rm ≥ 1 := by
          by_cases hz : rm = 0
          · rw [hz] at hrm_sq; simp at hrm_sq
          · omega
        have hdvd_prod : q ∣ ((rm - 1) * (rm + 1)) := by
          have hexp : (rm - 1) * (rm + 1) + 1 = rm * rm := by
            cases hrm_eq : rm with
            | zero => rw [hrm_eq] at hrm_pos; omega
            | succ r' =>
              simp only [Nat.add_sub_cancel]
              rw [Nat.mul_add r' (r' + 1) 1, Nat.add_mul r' 1 (r' + 1)]
              omega
          have hm0 : ((rm - 1) * (rm + 1)) % q = 0 := by
            have h1 := hrm_sq
            rw [← hexp, Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < q)] at h1
            have hlt_m : ((rm - 1) * (rm + 1)) % q < q := Nat.mod_lt _ (by omega)
            by_cases hz0 : ((rm - 1) * (rm + 1)) % q = 0
            · exact hz0
            · have hsum_q : ((rm - 1) * (rm + 1)) % q + 1 < q ∨
                  ((rm - 1) * (rm + 1)) % q + 1 = q := by omega
              rcases hsum_q with hlt_q | heq_q
              · rw [Nat.mod_eq_of_lt hlt_q] at h1; omega
              · rw [heq_q, Nat.mod_self] at h1; omega
          exact Nat.dvd_of_mod_eq_zero hm0
        rcases gauss_euclid_lemma q (rm - 1) (rm + 1) hq hdvd_prod with hd1 | hd2'
        · left
          rcases hd1 with ⟨c, hc⟩
          cases c with
          | zero => simp at hc; omega
          | succ c' => have := Nat.mul_le_mul_left q (by omega : 1 ≤ c' + 1); omega
        · right
          rcases hd2' with ⟨c, hc⟩
          cases c with
          | zero => simp at hc
          | succ c' =>
            cases c' with
            | zero => simp at hc; omega
            | succ c'' =>
              change rm + 1 = q * (c'' + 2) at hc
              have := Nat.mul_le_mul_left q (by omega : 2 ≤ c'' + 2); omega
      refine ⟨h2_d2, ⟨?_, ?_⟩⟩
      · intro h2g
        have h2_d32 : 2 ∣ d32 := Nat.dvd_trans h2g (Nat.gcd_dvd_right d2 d32)
        have hrm_ne1 : rm ≠ 1 := by
          intro hrm1
          have hd32_m := exactMultOrderMod_dvd_of_pow_eq_one q (ratio32Mod q) d32 m hd32 hrm1
          have hm_ev : 2 ∣ m := Nat.dvd_trans h2_d32 hd32_m
          rcases hm_ev with ⟨c, hc⟩; omega
        have hrm_qm1 : rm = q - 1 := by rcases hrm_dich with h1 | h2 <;> omega
        rw [h6m_rel, show (ratio32Mod q) ^ m % q = rm from rfl, hrm_qm1]
        -- `((q - 1) * (q - 1)) % q = 1`:
        have hsp : (q - 1) * (q - 1) = 1 + q * (q - 2) := by
          let u := q - 2
          have hq1 : q - 1 = u + 1 := by dsimp [u]; omega
          have hq0 : q = u + 2 := by dsimp [u]; omega
          rw [show q - 2 = u from rfl, hq1, hq0,
              Nat.add_mul u 1 (u + 1), Nat.mul_add u u 1, Nat.add_mul u 2 u]
          omega
        rw [hsp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      · intro h6_1
        have hrm_ne1 : rm ≠ 1 := by
          intro hrm1
          rw [h6m_rel, show (ratio32Mod q) ^ m % q = rm from rfl, hrm1,
              Nat.mul_one, Nat.mod_eq_of_lt (by omega : q - 1 < q)] at h6_1
          omega
        have hnot_m : ¬ (d32 ∣ m) := by
          rintro ⟨c, hc⟩
          apply hrm_ne1
          dsimp [rm]
          rw [hc, ← pow_pow_eq_mul_w5 _ d32 c,
              pow_mod_eq_of_mod_eq_w5 q ((ratio32Mod q) ^ d32) 1
                (by rw [hd32.2.2.1, Nat.mod_eq_of_lt (by omega : 1 < q)]) c,
              Nat.one_pow, Nat.mod_eq_of_lt (by omega)]
        have h2_d32 : 2 ∣ d32 := by
          by_cases hev : d32 % 2 = 0
          · exact Nat.dvd_of_mod_eq_zero hev
          · have hgcd : Nat.gcd d32 2 = 1 := by
              rw [Nat.gcd_comm, Nat.gcd_rec 2 d32, show d32 % 2 = 1 by omega]; decide
            exact False.elim (hnot_m
              (coprime_dvd_of_dvd_mul_aux (d32 + 2) d32 2 m (Nat.le_refl _) hgcd hd32_2m))
        exact Nat.dvd_gcd h2_d2 h2_d32
    refine ⟨hq5_law, ?_, by decide, by decide, by decide, by decide⟩
    intro w1 a1 q0 q hw1 ha1 hq0 hgt hbrox hq h5 h6_1 hqD
    rcases (one_block_all_prime_divisors_coprime_order_and_totient.2
      w1 a1 q0 hw1 ha1 hq0 hgt hbrox).2.2 q hq hqD with ⟨_, d2, d32, hd2, hd32, hgcd1, _⟩
    have h2g := (hq5_law q d2 d32 hq h5 hd2 hd32).2.mpr h6_1
    rw [hgcd1] at h2g
    rcases h2g with ⟨c, hc⟩; omega
  · -- Part 2b: Octic `q % 24 = 17` universal `8 ∣ ord_q(3/2)` lock:
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · intro q d32 hq h17 hd32
      let h := (q - 1) / 2
      have hq17 : q ≥ 17 := by omega
      have hqo : q % 2 = 1 := by omega
      have hq_nd3 : q % 3 ≠ 0 := by omega
      have hc2 := gaussUpperCount_two_eq q hqo (by omega) h (Nat.le_refl h)
      have hc3 := gaussUpperCount_three_eq q hqo (by omega) hq_nd3 h (Nat.le_refl h)
      rw [Nat.min_eq_right (by dsimp [h]; omega)] at hc2
      rw [Nat.min_eq_right (by dsimp [h]; omega), Nat.min_eq_right (by dsimp [h]; omega)] at hc3
      have hev2 : gaussUpperCount q 2 h % 2 = 0 := by rw [hc2]; dsimp [h]; omega
      have ho3  : gaussUpperCount q 3 h % 2 = 1 := by rw [hc3]; omega
      have hp2 := (gauss_lemma_mod_prime q 2 hq hqo (by omega) (hnd2_of q (by omega))).1 hev2
      have hp3 := (gauss_lemma_mod_prime q 3 hq hqo (by omega) (hnd3_of q (by omega))).2 ho3
      have h2r := two_mul_ratio32Mod_eq_three q hqo (by omega)
      have hp32 : (ratio32Mod q) ^ h % q = q - 1 := by
        have h1 : (2 ^ h * (ratio32Mod q) ^ h) % q = q - 1 := by
          rw [← pow_mul_mod_distrib_w11 q 2 (ratio32Mod q) h,
              pow_mod_eq_of_mod_eq_w5 q (2 * ratio32Mod q) 3
                (by rw [h2r, Nat.mod_eq_of_lt (by omega)]) h,
              hp3]
        rwa [Nat.mul_mod (2 ^ h) _ q, hp2, Nat.one_mul, Nat.mod_mod] at h1
      let r8 := (q - 1) / 8
      have hqm1_8 : q - 1 = 2 ^ 3 * r8 := by dsimp [r8]; omega
      have h8_d32 := full_two_sylow_dvd_order_of_half_minus_one q 3 r8 (ratio32Mod q) d32
        hq (by omega) (by decide) hqm1_8 (hnd32_of q hqo (by omega)) hd32 hp32
      have hd32_ge8 : d32 ≥ 8 := by
        rcases h8_d32 with ⟨c, hc⟩
        cases c with
        | zero => simp at hc; have := hd32.2.1; omega
        | succ _ => omega
      exact ⟨h8_d32, hd32_ge8⟩
    · exact ⟨by decide, by decide, by decide, fun r hr => by revert r hr; decide⟩
    · exact ⟨by decide, by decide, by decide, fun r hr => by revert r hr; decide⟩
    · exact ⟨by decide, by decide, by decide, fun r hr => by revert r hr; decide⟩
  · -- Part 3: Universal `ℓ`-Sylow order-lock, 1-block exclusion, & 2-block `(41 * ℓ, 65 * ℓ)` floors:
    have hsylow_pair : ∀ (q ell e m d2 d32 : Nat),
        IsPrimeNat q -> q ≥ 5 -> IsPrimeNat ell -> e ≥ 1 -> m ≥ 1 ->
        q - 1 = ell ^ e * m ->
        IsExactMultOrderMod q 2 d2 ->
        IsExactMultOrderMod q (ratio32Mod q) d32 ->
        2 ^ m % q ≠ 1 -> (ratio32Mod q) ^ m % q ≠ 1 ->
        ell ∣ Nat.gcd d2 d32 ∧ Nat.gcd d2 d32 ≥ ell := by
      intro q ell e m d2 d32 hq hq5 hell he _ hqm1 hd2 hd32 h2m h32m
      have hqo : q % 2 = 1 := by
        by_cases hev : q % 2 = 0
        · exact False.elim (hq.2 2 (Nat.le_refl 2) (by omega) (Nat.dvd_of_mod_eq_zero hev))
        · omega
      have hl_2 := sylow_prime_dvd_order_of_pow_ne_one q ell e m 2 d2
        hq hell he hqm1 (hnd2_of q hq5) hd2 h2m
      have hl_32 := sylow_prime_dvd_order_of_pow_ne_one q ell e m (ratio32Mod q) d32
        hq hell he hqm1 (hnd32_of q hqo hq5) hd32 h32m
      have hlg : ell ∣ Nat.gcd d2 d32 := Nat.dvd_gcd hl_2 hl_32
      have hg_ge : Nat.gcd d2 d32 ≥ ell := by
        rcases hlg with ⟨c, hc⟩
        cases c with
        | zero =>
          simp only [Nat.mul_zero] at hc
          have hp := Nat.gcd_pos_of_pos_left d32 hd2.2.1; omega
        | succ c' =>
          rw [hc]
          simpa using Nat.mul_le_mul_left ell (by omega : 1 ≤ c' + 1)
      exact ⟨hlg, hg_ge⟩
    refine ⟨hsylow_pair, ?_, ?_, ?_, ?_⟩
    · intro w1 a1 q0 q ell e m hw1 ha1 hq0 hgt hbrox hq hq5 hell he hm1 hqm1 h2m h32m hqD
      rcases (one_block_all_prime_divisors_coprime_order_and_totient.2
        w1 a1 q0 hw1 ha1 hq0 hgt hbrox).2.2 q hq hqD with ⟨_, d2, d32, hd2, hd32, hgcd1, _⟩
      rcases hsylow_pair q ell e m d2 d32 hq hq5 hell he hm1 hqm1 hd2 hd32 h2m h32m with ⟨_, hg_ge⟩
      have := hell.1; omega
    · intro w1 a1 w2 a2 q0 q1 q ell e m hprim hq hq5 hell he hm1 hqm1 h2m h32m hqD hqa1
      have hqo : q % 2 = 1 := by
        by_cases hev : q % 2 = 0
        · exact False.elim (hq.2 2 (Nat.le_refl 2) (by omega) (Nat.dvd_of_mod_eq_zero hev))
        · omega
      rcases exists_exact_mult_order_mod_prime q 2 hq (hnd2_of q hq5) with ⟨d1, hd1, _⟩
      rcases exists_exact_mult_order_mod_prime q (ratio32Mod q) hq (hnd32_of q hqo hq5) with ⟨d2, hd2, _⟩
      rcases hsylow_pair q ell e m d1 d2 hq hq5 hell he hm1 hqm1 hd1 hd2 h2m h32m with ⟨hlg, hg_ge⟩
      have hell2 := hell.1
      rcases two_block_shared_mersenne_common_order_scaling_and_squeeze
        w1 a1 w2 a2 q0 q1 q d1 d2 hprim (by omega) hqo hd1 hd2 hqD hqa1 with
        ⟨_, hr_a1, hr_a2, hr_W, _, _, _, _, _, _, _⟩
      rcases two_block_shared_mersenne_mod24_and_even_order_obstructions.1
        w1 a1 w2 a2 q0 q1 q d1 d2 hprim (by omega) hqo hd1 hd2 (by omega) hqD hqa1 with
        ⟨hW_41, hK_65⟩
      exact ⟨Nat.dvd_trans hlg hr_a1,
             Nat.dvd_trans hlg hr_a2,
             Nat.dvd_trans hlg hr_W,
             Nat.le_trans (Nat.mul_le_mul_left 41 hg_ge) hW_41,
             Nat.le_trans (Nat.mul_le_mul_left 65 hg_ge) hK_65⟩
    · refine ⟨checkSmallPrimeBool_sound 73 (by decide),
              by decide, by decide, by decide, by decide, by decide, by decide⟩
    · refine ⟨checkSmallPrimeBool_sound 31 (by decide),
              by decide, by decide, by decide, by decide, by decide⟩

theorem blockEvenSum_dvd_of_all_dvd (ell : Nat) :
    ∀ bs : List (Nat × Nat),
      (∀ b ∈ bs, ell ∣ b.2) ->
      ell ∣ blockWeightSum bs ->
      ell ∣ blockStepSum bs
  | [], _, hW => hW
  | b :: rest, hall, hW => by
    have hb2 : ell ∣ b.2 := hall b (List.Mem.head _)
    have hrest : ∀ x ∈ rest, ell ∣ x.2 := fun x hx => hall x (List.mem_cons_of_mem _ hx)
    -- Prove `blockStepSum bs = blockWeightSum bs + sumSecond bs`:
    have hsum2 : ∀ xs : List (Nat × Nat),
        (∀ x ∈ xs, ell ∣ x.2) -> ∃ k : Nat, blockStepSum xs = blockWeightSum xs + ell * k := by
      intro xs; induction xs with
      | nil => intro _; exact ⟨0, by simp [blockStepSum, blockWeightSum]⟩
      | cons x0 xs' ih =>
        intro hx_all
        rcases hx_all x0 (List.Mem.head _) with ⟨c0, hc0⟩
        rcases ih (fun y hy => hx_all y (List.mem_cons_of_mem _ hy)) with ⟨kr, hkr⟩
        refine ⟨c0 + kr, ?_⟩
        simp only [blockStepSum, blockWeightSum]
        rw [hc0, hkr, Nat.mul_add]
        omega
    rcases hsum2 (b :: rest) hall with ⟨k, hk⟩
    rcases hW with ⟨kw, hkw⟩
    exact ⟨kw + k, by rw [hk, hkw, Nat.mul_add]⟩

/--
  Theorem W11.2a' (`m_block_shared_mersenne_sylow_and_one_block_companion_cascades`, `zero custom axioms`):
  All-`m` (`∀ m ≥ 1`) Shared-Mersenne `m`-Block `ℓ`-Sylow / Mod-`3` Obstructions &
  1-Block Companion-Prime Quotient Cascades (`q0` & `x0`) (`Branch P3.4`):
  1. **Universal `∀ m ≥ 1` Shared-Mersenne `m`-Block `ℓ`-Sylow & Mod-`3` Lock**:
     For ANY non-empty block list `blocks = b0 :: rest` (`m = blocks.length ≥ 1`) with
     `∀ b ∈ blocks, b.1 ≥ 1 ∧ b.2 ≥ 1`, `3 ^ W < 2 ^ K`, and `D ∣ broxSpiralCarry blocks`:
     - Whenever prime `q ≥ 5` divides `D` and `∀ b ∈ blocks, q ∣ (2 ^ b.2 - 1)`, with
       `q - 1 = ℓ ^ e * m_part` (`IsPrimeNat ℓ, e ≥ 1, m_part ≥ 1`, `2 ^ m_part % q ≠ 1`,
       `(ratio32Mod q) ^ m_part % q ≠ 1`):
         `(∀ b ∈ blocks, ℓ ∣ b.2) ∧ ℓ ∣ blockWeightSum blocks ∧ ℓ ∣ blockStepSum blocks`!
     - Whenever `ℓ = 2` (including `q % 24 ∈ {11, 13}` and `q % 24 = 5` with `6^((q-1)/4) % q = 1`):
       every block quotient in `qs` is divisible by `3` (`3 ∣ natListGcd qs`)!
  2. **1-Block Companion-Prime Quotient Cascades (`15 ∣ q0`, `255 ∣ q0`, `7 ∣ q0`, `31 ∣ q0`, `511 ∣ q0`,
     `5 ∣ x0`, `19 ∣ x0`, `65 ∣ x0`, `665 ∣ x0`)**:
     On ANY 1-block `Z^+` cycle `(w1, a1, q0)` (`w1 ≥ 2, a1 ≥ 1, q0 ≥ 1, 3^w1 < 2^(w1+a1),
     (2^(w1+a1) - 3^w1) * q0 = 2^a1 - 1`, `D := 2^(w1+a1) - 3^w1`, `x0 := 2^w1 * q0 - 1`):
     Wave 10–11 quadratic/quartic/octic/`ℓ`-Sylow exclusions eliminate `{3, 5, 7, 13, 17, 19, 31, 73}`
     from dividing `D`, forcing companion quotient cascades into `q0` and `x0`!
-/
theorem m_block_shared_mersenne_sylow_and_one_block_companion_cascades :
    -- Part 1: Universal `∀ m ≥ 1` shared-Mersenne `m`-block `ℓ`-Sylow & `ℓ = 2 => 3 ∣ qs` lock:
    (∀ (b0 : Nat × Nat) (rest : List (Nat × Nat)) (q ell e m_part : Nat),
      let blocks := b0 :: rest
      let W := blockWeightSum blocks
      let K := blockStepSum blocks
      let D := 2 ^ K - 3 ^ W
      (∀ b ∈ blocks, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      3 ^ W < 2 ^ K ->
      D ∣ broxSpiralCarry blocks ->
      IsPrimeNat q -> q ≥ 5 -> IsPrimeNat ell -> e ≥ 1 -> m_part ≥ 1 ->
      q - 1 = ell ^ e * m_part ->
      2 ^ m_part % q ≠ 1 -> (ratio32Mod q) ^ m_part % q ≠ 1 ->
      q ∣ D ->
      (∀ b ∈ blocks, q ∣ (2 ^ b.2 - 1)) ->
      (∀ b ∈ blocks, ell ∣ b.2) ∧
      ell ∣ W ∧
      ell ∣ K ∧
      (ell = 2 ->
        ∃ qs : List Nat,
          qs.length = blocks.length ∧
          (∀ j : Nat, j < blocks.length -> D * natAt qs j = broxSpiralCarry (rotBlocks j blocks)) ∧
          3 ∣ natListGcd qs)) ∧
    -- Part 2: 1-Block companion-prime exclusions & quotient cascades into `q0` and `x0`:
    (∀ (w1 a1 q0 : Nat),
      w1 ≥ 2 -> a1 ≥ 1 -> q0 ≥ 1 -> 3 ^ w1 < 2 ^ (w1 + a1) ->
      (2 ^ (w1 + a1) - 3 ^ w1) * q0 = 2 ^ a1 - 1 ->
      let D := 2 ^ (w1 + a1) - 3 ^ w1
      let x0 := 2 ^ w1 * q0 - 1
      (¬ (3 ∣ D) ∧ ¬ (5 ∣ D) ∧ ¬ (7 ∣ D) ∧ ¬ (13 ∣ D) ∧
       ¬ (17 ∣ D) ∧ ¬ (19 ∣ D) ∧ ¬ (31 ∣ D) ∧ ¬ (73 ∣ D)) ∧
      ((2 ∣ a1 -> 3 ∣ q0) ∧ (4 ∣ a1 -> 15 ∣ q0) ∧ (8 ∣ a1 -> 255 ∣ q0) ∧
       (3 ∣ a1 -> 7 ∣ q0) ∧ (5 ∣ a1 -> 31 ∣ q0) ∧ (9 ∣ a1 -> 511 ∣ q0)) ∧
      ((2 ∣ w1 -> 5 ∣ x0) ∧ (3 ∣ w1 -> 19 ∣ x0) ∧ (4 ∣ w1 -> 65 ∣ x0) ∧ (6 ∣ w1 -> 665 ∣ x0))) := by
  have hnd2_of : ∀ q : Nat, q ≥ 5 -> ¬ (q ∣ 2) := by
    intro q hq5 ⟨c, hc⟩; cases c with
    | zero => simp at hc
    | succ c' => have := Nat.mul_le_mul_left q (by omega : 1 ≤ c' + 1); omega
  have hnd32_of : ∀ q : Nat, q % 2 = 1 -> q ≥ 5 -> ¬ (q ∣ ratio32Mod q) := by
    intro q hqo hq5 ⟨c, hc⟩
    have h2r := two_mul_ratio32Mod_eq_three q hqo hq5
    rw [hc, ← Nat.mul_assoc 2 q c, Nat.mul_comm 2 q, Nat.mul_assoc q 2 c, Nat.mul_mod_right] at h2r
    omega
  refine ⟨?_, ?_⟩
  · -- Part 1: `∀ m ≥ 1` shared-Mersenne `m`-block `ℓ`-Sylow divisibility:
    intro b0 rest q ell e m_part
    dsimp only
    intro hpos hgt hdvd_H0 hq hq5 hell he hm_pos hqm1 h2m h32m hqD hq_mers
    let blocks := b0 :: rest
    let W := blockWeightSum blocks
    let K := blockStepSum blocks
    let D := 2 ^ K - 3 ^ W
    have hqo : q % 2 = 1 := by
      by_cases hev : q % 2 = 0
      · exact False.elim (hq.2 2 (Nat.le_refl 2) (by omega) (Nat.dvd_of_mod_eq_zero hev))
      · omega
    rcases exists_exact_mult_order_mod_prime q 2 hq (hnd2_of q hq5) with ⟨d2, hd2, _⟩
    rcases exists_exact_mult_order_mod_prime q (ratio32Mod q) hq (hnd32_of q hqo hq5) with ⟨d32, hd32, _⟩
    rcases complete_mod24_and_sylow_reciprocity_obstructions.2.2.2.1
      q ell e m_part d2 d32 hq hq5 hell he hm_pos hqm1 hd2 hd32 h2m h32m with ⟨hell_gcd, _⟩
    have hell_d2 : ell ∣ d2 := Nat.dvd_trans hell_gcd (Nat.gcd_dvd_left d2 d32)
    have hell_d32 : ell ∣ d32 := Nat.dvd_trans hell_gcd (Nat.gcd_dvd_right d2 d32)
    have h2b_mod1 : ∀ b ∈ blocks, 2 ^ b.2 % q = 1 := by
      intro b hb
      rcases hq_mers b hb with ⟨k, hk⟩
      have hp2 : 2 ^ b.2 ≥ 2 := by simpa using pow2_mono_nat (hpos b hb).2
      rw [show 2 ^ b.2 = 1 + q * k by omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have hb_ell : ∀ b ∈ blocks, ell ∣ b.2 := by
      intro b hb
      exact Nat.dvd_trans hell_d2
        (exactMultOrderMod_dvd_of_pow_eq_one q 2 d2 b.2 hd2 (h2b_mod1 b hb))
    have h2K_2W : 2 ^ K % q = 2 ^ W % q :=
      pow2_stepSum_mod_eq_weightSum_mod_w6 q (by omega) blocks h2b_mod1
    have h2K_3W : 2 ^ K % q = 3 ^ W % q := by
      rcases hqD with ⟨k, hk⟩
      have hrew : 2 ^ K = 3 ^ W + q * k := by
        change 2 ^ K - 3 ^ W = q * k at hk
        generalize 2 ^ K = p2k, 3 ^ W = p3w at hgt hk ⊢; omega
      rw [hrew, Nat.add_mul_mod_self_left]
    have h2r := two_mul_ratio32Mod_eq_three q hqo hq5
    have hmul_W : (2 ^ W * (ratio32Mod q) ^ W) % q = (2 ^ W * 1) % q := by
      rw [← pow_mul_mod_distrib_w11 q 2 (ratio32Mod q) W,
          pow_mod_eq_of_mod_eq_w5 q (2 * ratio32Mod q) 3
            (by rw [h2r, Nat.mod_eq_of_lt (by omega)]) W,
          ← h2K_3W, h2K_2W, Nat.mul_one]
    have hnd_2W : ¬ (q ∣ 2 ^ W) := by
      rintro ⟨c, hc⟩
      have hm0 : 2 ^ W % q = 0 := by rw [hc, Nat.mul_mod_right]
      exact odd_mod_pow2_nonzero_w5 q (by omega) hqo W hm0
    have hr32_W : (ratio32Mod q) ^ W % q = 1 := by
      have hc := cancel_mul_mod_prime q (2 ^ W) ((ratio32Mod q) ^ W) 1 hq hnd_2W hmul_W
      rwa [Nat.mod_eq_of_lt (by omega : 1 < q)] at hc
    have hW_ell : ell ∣ W :=
      Nat.dvd_trans hell_d32 (exactMultOrderMod_dvd_of_pow_eq_one q (ratio32Mod q) d32 W hd32 hr32_W)
    have hK_ell : ell ∣ K := blockEvenSum_dvd_of_all_dvd ell blocks hb_ell hW_ell
    refine ⟨hb_ell, hW_ell, hK_ell, ?_⟩
    intro hell2
    subst hell2
    rcases (m_block_cycle_induces_brox_quotients b0 rest hpos hgt).2 hdvd_H0 with
      ⟨qs, hq_len, hqs_eq, _, hmod3⟩
    have hblockAt_mem : ∀ j : Nat, j < blocks.length -> blockAt blocks j ∈ blocks := by
      have haux : ∀ (bs : List (Nat × Nat)) (i : Nat), i < bs.length -> blockAt bs i ∈ bs := by
        intro bs; induction bs with
        | nil => intro _ hi; simp at hi
        | cons _ tl ih =>
          intro i hi; cases i with
          | zero => exact List.Mem.head _
          | succ i' => exact List.mem_cons_of_mem _ (ih i' (by simp at hi; omega))
      exact fun j hj => haux blocks j hj
    refine ⟨qs, hq_len, hqs_eq, dvd_natListGcd_of_forall 3 qs ?_⟩
    intro x hx
    rcases mem_imp_exists_natAt_w6 qs x hx with ⟨i, hi, hxi⟩
    rw [hq_len] at hi
    let m := blocks.length
    change i < m at hi
    have hm_ge1 : m ≥ 1 := by simp [m, blocks]
    let j := if i = 0 then m - 1 else i - 1
    have hj_lt : j < m := by dsimp [j]; by_cases hi0 : i = 0 <;> simp [hi0] <;> omega
    have hj_next : (j + 1) % m = i := by
      dsimp [j]
      by_cases hi0 : i = 0
      · simp only [hi0, ite_true, show m - 1 + 1 = m by omega, Nat.mod_self]
      · simp only [hi0, ite_false]; rw [show i - 1 + 1 = i by omega]; exact Nat.mod_eq_of_lt hi
    rcases hb_ell _ (hblockAt_mem j hj_lt) with ⟨kb, hkb⟩
    have hq_div3 := (hmod3 j hj_lt).mpr (by omega : (blockAt blocks j).2 % 2 = 0)
    rw [hj_next, hxi] at hq_div3
    exact Nat.dvd_of_mod_eq_zero hq_div3
  · -- Part 2: 1-Block exclusions `{3, 5, 7, 13, 17, 19, 31, 73}` & companion quotient cascades:
    intro w1 a1 q0 hw1 ha1 hq0 hgt hbrox
    dsimp only
    let D := 2 ^ (w1 + a1) - 3 ^ w1
    let x0 := 2 ^ w1 * q0 - 1
    -- `3 ∤ D` since `w1 ≥ 2 => 3 ∣ 3^w1` while `2^(w1+a1) % 3 ∈ {1, 2}`:
    have hnd3 : ¬ (3 ∣ D) := by
      rintro ⟨c, hc⟩
      have hp3_dvd : 3 ∣ 3 ^ w1 := ⟨3 ^ (w1 - 1), by
        conv => lhs; rw [show w1 = (w1 - 1) + 1 by omega]
        rw [Nat.pow_succ, Nat.mul_comm]⟩
      rcases hp3_dvd with ⟨c3, hc3⟩
      have h2_3 : 3 ∣ 2 ^ (w1 + a1) := ⟨c + c3, by
        have hlt : 3 ^ w1 < 2 ^ (w1 + a1) := hgt
        change 2 ^ (w1 + a1) - 3 ^ w1 = 3 * c at hc
        rw [Nat.mul_add]; generalize 2 ^ (w1 + a1) = P2, 3 ^ w1 = P3 at hlt hc hc3 ⊢; omega⟩
      have h2m3 : 2 ^ (w1 + a1) % 3 = 0 := by rcases h2_3 with ⟨u, hu⟩; rw [hu, Nat.mul_mod_right]
      have h2_nz : ∀ n : Nat, 2 ^ n % 3 ≠ 0 := by
        intro n; induction n with
        | zero => decide
        | succ n' ih => rw [Nat.pow_succ, Nat.mul_mod]; omega
      exact h2_nz (w1 + a1) h2m3
    have hnd5 : ¬ (5 ∣ D) :=
      complete_mod24_and_sylow_reciprocity_obstructions.2.1.2.1 w1 a1 q0 5
        hw1 ha1 hq0 hgt hbrox (checkSmallPrimeBool_sound 5 (by decide)) (by decide) (by decide)
    have hnd7 : ¬ (7 ∣ D) :=
      complete_mod24_and_sylow_reciprocity_obstructions.2.2.2.2.1 w1 a1 q0 7 3 1 2
        hw1 ha1 hq0 hgt hbrox (checkSmallPrimeBool_sound 7 (by decide)) (by decide)
        (checkSmallPrimeBool_sound 3 (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hnd13 : ¬ (13 ∣ D) :=
      mod24_11_13_quadratic_reciprocity_and_one_block_exclusion.2 w1 a1 q0 13
        hw1 ha1 hq0 hgt hbrox (checkSmallPrimeBool_sound 13 (by decide)) (Or.inr (by decide))
    have hnd17 : ¬ (17 ∣ D) :=
      complete_mod24_and_sylow_reciprocity_obstructions.2.2.2.2.1 w1 a1 q0 17 2 4 1
        hw1 ha1 hq0 hgt hbrox (checkSmallPrimeBool_sound 17 (by decide)) (by decide)
        (checkSmallPrimeBool_sound 2 (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hnd19 : ¬ (19 ∣ D) :=
      complete_mod24_and_sylow_reciprocity_obstructions.2.2.2.2.1 w1 a1 q0 19 3 2 2
        hw1 ha1 hq0 hgt hbrox (checkSmallPrimeBool_sound 19 (by decide)) (by decide)
        (checkSmallPrimeBool_sound 3 (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hnd31 : ¬ (31 ∣ D) :=
      complete_mod24_and_sylow_reciprocity_obstructions.2.2.2.2.1 w1 a1 q0 31 5 1 6
        hw1 ha1 hq0 hgt hbrox (checkSmallPrimeBool_sound 31 (by decide)) (by decide)
        (checkSmallPrimeBool_sound 5 (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hnd73 : ¬ (73 ∣ D) :=
      complete_mod24_and_sylow_reciprocity_obstructions.2.2.2.2.1 w1 a1 q0 73 3 2 8
        hw1 ha1 hq0 hgt hbrox (checkSmallPrimeBool_sound 73 (by decide)) (by decide)
        (checkSmallPrimeBool_sound 3 (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
    -- Pure algebraic `D * x0 = 3^w1 - 2^w1`:
    have hDx0 : D * x0 = 3 ^ w1 - 2 ^ w1 := by
      have hmul_2w : D * (2 ^ w1 * q0) = 2 ^ (w1 + a1) - 2 ^ w1 := by
        calc
          D * (2 ^ w1 * q0) = (D * q0) * 2 ^ w1 := by
            rw [Nat.mul_comm (2 ^ w1) q0, ← Nat.mul_assoc D q0 (2 ^ w1)]
          _ = (2 ^ a1 - 1) * 2 ^ w1 := by rw [hbrox]
          _ = 2 ^ a1 * 2 ^ w1 - 1 * 2 ^ w1 := Nat.sub_mul (2 ^ a1) 1 (2 ^ w1)
          _ = 2 ^ (w1 + a1) - 2 ^ w1 := by rw [Nat.one_mul, ← Nat.pow_add, Nat.add_comm a1 w1]
      have hsub_D := Nat.mul_sub_left_distrib D (2 ^ w1 * q0) 1
      dsimp [x0]; rw [hsub_D, Nat.mul_one, hmul_2w]
      have h2w_le := pow2_le_pow3 w1
      dsimp [D]; generalize 2 ^ (w1 + a1) = p2k, 3 ^ w1 = p3w, 2 ^ w1 = p2w at hgt h2w_le ⊢; omega
    have hq_cascade : ∀ (d : Nat) (ps : List Nat),
        d ∣ a1 ->
        natProdList ps = 2 ^ d - 1 ->
        (∀ p ∈ ps, p ≤ 160 ∧ checkUnitsGrid16x10 p ∧ ¬ (p ∣ D)) ->
        natProdList ps ∣ q0 := by
      intro d ps ⟨k, hk⟩ hprod hall
      have hdvd_a1 : (2 ^ d - 1) ∣ (D * q0) := by
        rw [hbrox, hk]
        have hm := pow_sub_pow_mul_dvd_w8 2 1 d (by decide) k
        simpa using hm
      rw [← hprod, ← Nat.mul_one (natProdList ps)] at hdvd_a1
      exact prime_list_cancel_dvd_w8 D ps q0 1 hall hdvd_a1
    have hx_cascade : ∀ (d : Nat) (ps : List Nat),
        d ∣ w1 ->
        natProdList ps = 3 ^ d - 2 ^ d ->
        (∀ p ∈ ps, p ≤ 160 ∧ checkUnitsGrid16x10 p ∧ ¬ (p ∣ D)) ->
        natProdList ps ∣ x0 := by
      intro d ps ⟨k, hk⟩ hprod hall
      have hdvd_w1 : (3 ^ d - 2 ^ d) ∣ (D * x0) := by
        rw [hDx0, hk]
        exact pow_sub_pow_mul_dvd_w8 3 2 d (by decide) k
      rw [← hprod, ← Nat.mul_one (natProdList ps)] at hdvd_w1
      exact prime_list_cancel_dvd_w8 D ps x0 1 hall hdvd_w1
    have hp_ok : ∀ p : Nat,
        p ∈ ([3, 5, 7, 13, 17, 19, 31, 73] : List Nat) ->
        p ≤ 160 ∧ checkUnitsGrid16x10 p ∧ ¬ (p ∣ D) := by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨by decide, by decide, hnd3⟩
      · exact ⟨by decide, by decide, hnd5⟩
      · exact ⟨by decide, by decide, hnd7⟩
      · exact ⟨by decide, by decide, hnd13⟩
      · exact ⟨by decide, by decide, hnd17⟩
      · exact ⟨by decide, by decide, hnd19⟩
      · exact ⟨by decide, by decide, hnd31⟩
      · exact ⟨by decide, by decide, hnd73⟩
    refine ⟨⟨hnd3, hnd5, hnd7, hnd13, hnd17, hnd19, hnd31, hnd73⟩,
            ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
            ⟨?_, ?_, ?_, ?_⟩⟩
    · intro h2; simpa [natProdList] using hq_cascade 2 [3] h2 (by decide)
        (fun p hp => hp_ok p (by simp at hp; subst hp; simp))
    · intro h4; simpa [natProdList] using hq_cascade 4 [3, 5] h4 (by decide)
        (fun p hp => hp_ok p (by simp at hp; rcases hp with rfl | rfl <;> simp))
    · intro h8; simpa [natProdList] using hq_cascade 8 [3, 5, 17] h8 (by decide)
        (fun p hp => hp_ok p (by simp at hp; rcases hp with rfl | rfl | rfl <;> simp))
    · intro h3; simpa [natProdList] using hq_cascade 3 [7] h3 (by decide)
        (fun p hp => hp_ok p (by simp at hp; subst hp; simp))
    · intro h5; simpa [natProdList] using hq_cascade 5 [31] h5 (by decide)
        (fun p hp => hp_ok p (by simp at hp; subst hp; simp))
    · intro h9; simpa [natProdList] using hq_cascade 9 [7, 73] h9 (by decide)
        (fun p hp => hp_ok p (by simp at hp; rcases hp with rfl | rfl <;> simp))
    · intro h2; simpa [natProdList] using hx_cascade 2 [5] h2 (by decide)
        (fun p hp => hp_ok p (by simp at hp; subst hp; simp))
    · intro h3; simpa [natProdList] using hx_cascade 3 [19] h3 (by decide)
        (fun p hp => hp_ok p (by simp at hp; subst hp; simp))
    · intro h4; simpa [natProdList] using hx_cascade 4 [5, 13] h4 (by decide)
        (fun p hp => hp_ok p (by simp at hp; rcases hp with rfl | rfl <;> simp))
    · intro h6; simpa [natProdList] using hx_cascade 6 [5, 7, 19] h6 (by decide)
        (fun p hp => hp_ok p (by simp at hp; rcases hp with rfl | rfl | rfl <;> simp))

-- ----------------------------------------------------------------------------
-- Section 2B: Pure-`Int` Column-Majorant Laplace Bound, Universal `∀ T ≥ 1`
--             `(T + 1) × (T + 1)` Single-Base Closed Form (Including `8 × 8`),
--             & Upgraded `2^u (2^u - 1)^(2T)` / `2^(3u) (2^u - 1)^9` Extrapolation
-- ----------------------------------------------------------------------------

def colBoundProd : (L : Nat) -> (Fin L -> Nat) -> Nat
  | 0, _ => 1
  | L + 1, B => B ⟨0, Nat.zero_lt_succ L⟩ * colBoundProd L (fun c => B (skipFinIdx ⟨0, Nat.zero_lt_succ L⟩ c))

def colBoundProdPrefix (L : Nat) (B : Fin L -> Nat) : Nat -> Nat
  | 0 => 1
  | k + 1 => colBoundProdPrefix L B k * (if h : k < L then B ⟨k, h⟩ else 1)

theorem colBoundProdPrefix_skip {L : Nat} (B : Fin (L + 1) -> Nat) (j : Fin (L + 1)) :
    B j * colBoundProdPrefix L (fun c => B (skipFinIdx j c)) L =
      colBoundProdPrefix (L + 1) B (L + 1) := by
  -- Prove for all `k ≤ L + 1`:
  have hstep : ∀ (k : Nat), k ≤ L + 1 ->
      (if j.val < k then
        B j * colBoundProdPrefix L (fun c => B (skipFinIdx j c)) (k - 1)
       else
        colBoundProdPrefix L (fun c => B (skipFinIdx j c)) k) =
      colBoundProdPrefix (L + 1) B k := by
    intro k; induction k with
    | zero => simp [colBoundProdPrefix]
    | succ k' ih =>
      intro hk'
      have ih0 := ih (by omega)
      have hk_lt : k' < L + 1 := hk'
      simp only [colBoundProdPrefix, hk_lt, dite_true]
      by_cases hjk : j.val < k'
      · have hjk1 : j.val < k' + 1 := by omega
        rw [ite_true_of_w10 hjk1]
        rw [ite_true_of_w10 hjk] at ih0
        cases k' with
        | zero => omega
        | succ m =>
          have hm_lt : m < L := by omega
          have hm_lt1 : m < L + 1 := by omega
          simp only [Nat.add_sub_cancel] at ih0
          simp only [Nat.add_sub_cancel, colBoundProdPrefix, hm_lt, dite_true]
          have hskip : skipFinIdx j ⟨m, hm_lt⟩ = ⟨m + 1, hk_lt⟩ := by
            dsimp [skipFinIdx]; rw [ite_false_of_w10 (by omega)]
          rw [hskip, ← Nat.mul_assoc (B j), ih0]
          simp only [colBoundProdPrefix, hm_lt1, dite_true]
      · by_cases hjeq : j.val = k'
        · have hjk1 : j.val < k' + 1 := by omega
          rw [ite_true_of_w10 hjk1, Nat.add_sub_cancel]
          rw [ite_false_of_w10 hjk] at ih0
          have hjf : j = ⟨k', hk_lt⟩ := Fin.ext hjeq
          rw [ih0, hjf, Nat.mul_comm]
        · have hjgt : ¬ (j.val < k' + 1) := by omega
          have hk_ltL : k' < L := by have := j.isLt; omega
          rw [ite_false_of_w10 hjgt]
          simp only [hk_ltL, dite_true]
          rw [ite_false_of_w10 hjk] at ih0
          have hskip : skipFinIdx j ⟨k', hk_ltL⟩ = ⟨k', hk_lt⟩ := by
            dsimp [skipFinIdx]; rw [ite_true_of_w10 (by omega)]
          rw [hskip, ih0]
  have hfin := hstep (L + 1) (Nat.le_refl _)
  rw [ite_true_of_w10 j.isLt, Nat.add_sub_cancel] at hfin
  exact hfin

theorem intSumPrefix_natAbs_le (L : Nat) (f : Fin L -> Int) (M : Nat)
    (hbd : ∀ j : Fin L, (f j).natAbs ≤ M) :
    ∀ k : Nat, k ≤ L -> (intSumPrefix L f k).natAbs ≤ k * M
  | 0, _ => by simp [intSumPrefix]
  | k + 1, hk => by
    have hk_lt : k < L := hk
    simp only [intSumPrefix, hk_lt, dite_true]
    have htri := Int.natAbs_add_le (intSumPrefix L f k) (f ⟨k, hk_lt⟩)
    have ih := intSumPrefix_natAbs_le L f M hbd k (Nat.le_of_lt hk)
    have hcur := hbd ⟨k, hk_lt⟩
    rw [Nat.succ_mul]
    omega

/-- Pure-`Int` Column-Majorant Laplace Upper Bound (`|det A| ≤ L! * ∏_j B_j`, `zero custom axioms`). -/
theorem intDet_natAbs_le_fact_mul_colProd :
    ∀ (L : Nat) (A : Fin L -> Fin L -> Int) (B : Fin L -> Nat),
      (∀ (i j : Fin L), (A i j).natAbs ≤ B j) ->
      (intDet L A).natAbs ≤ natFact L * colBoundProdPrefix L B L
  | 0, _, _, _ => by simp [intDet, natFact, colBoundProdPrefix]
  | L + 1, A, B, hbd => by
    simp only [intDet, intSumFin, natFact]
    let M := natFact L * colBoundProdPrefix (L + 1) B (L + 1)
    have hterm : ∀ j : Fin (L + 1),
        (((if j.val % 2 = 0 then (1 : Int) else -1) *
          A ⟨0, Nat.zero_lt_succ L⟩ j * intDet L (intSubMat A j))).natAbs ≤ M := by
      intro j
      rw [Int.natAbs_mul, Int.natAbs_mul]
      have hsgn : (if j.val % 2 = 0 then (1 : Int) else -1).natAbs = 1 := by
        by_cases hev : j.val % 2 = 0 <;> simp [hev]
      rw [hsgn, Nat.one_mul]
      have ha0 := hbd ⟨0, Nat.zero_lt_succ L⟩ j
      have hsub := intDet_natAbs_le_fact_mul_colProd L (intSubMat A j)
        (fun c => B (skipFinIdx j c))
        (fun r c => hbd ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩ (skipFinIdx j c))
      have hm := Nat.mul_le_mul ha0 hsub
      have hprod_eq : B j * (natFact L * colBoundProdPrefix L (fun c => B (skipFinIdx j c)) L) = M := by
        dsimp [M]
        rw [← Nat.mul_assoc (B j) (natFact L), Nat.mul_comm (B j) (natFact L),
            Nat.mul_assoc (natFact L), colBoundProdPrefix_skip B j]
      rwa [hprod_eq] at hm
    have hsum := intSumPrefix_natAbs_le (L + 1) _ M hterm (L + 1) (Nat.le_refl _)
    rwa [← Nat.mul_assoc (L + 1) (natFact L)] at hsum

-- Universal `∀ T ≥ 1` `(T + 1) × (T + 1)` Single-Base `(T, U = 1)` Exact Determinant Infrastructure:

theorem intDet_lower_triangular :
    ∀ (L : Nat) (A : Fin L -> Fin L -> Int),
      (∀ (i j : Fin L), i.val < j.val -> A i j = 0) ->
      intDet L A =
        (match L with
         | 0 => 1
         | m + 1 =>
           A ⟨0, Nat.zero_lt_succ m⟩ ⟨0, Nat.zero_lt_succ m⟩ *
             intDet m (intSubMat A ⟨0, Nat.zero_lt_succ m⟩))
  | 0, _, _ => rfl
  | L + 1, A, htri => by
    simp only [intDet, intSumFin]
    let f : Fin (L + 1) -> Int := fun j =>
      (if j.val % 2 = 0 then (1 : Int) else -1) *
        A ⟨0, Nat.zero_lt_succ L⟩ j * intDet L (intSubMat A j)
    have hf0 : ∀ k : Nat, 1 ≤ k -> k ≤ L + 1 ->
        intSumPrefix (L + 1) f k = f ⟨0, Nat.zero_lt_succ L⟩ := by
      intro k hk1 hk_le
      induction k with
      | zero => omega
      | succ k' ih =>
        cases k' with
        | zero => simp [intSumPrefix]
        | succ m =>
          have hm_lt : m + 1 < L + 1 := hk_le
          change intSumPrefix (L + 1) f (m + 1) +
            (if h : m + 1 < L + 1 then f ⟨m + 1, h⟩ else 0) = _
          simp only [hm_lt, dite_true]
          have hz : A ⟨0, Nat.zero_lt_succ L⟩ ⟨m + 1, hm_lt⟩ = 0 :=
            htri ⟨0, Nat.zero_lt_succ L⟩ ⟨m + 1, hm_lt⟩ (by simp)
          have hfm : f ⟨m + 1, hm_lt⟩ = 0 := by dsimp only [f]; rw [hz]; simp
          rw [ih (by omega) (by omega), hfm, Int.add_zero]
    rw [hf0 (L + 1) (by omega) (Nat.le_refl _)]
    dsimp [f]; simp

/-- Vandermonde convolution `binom(a + b, t) = ∑_{r=0}^t binom(a, r) * binom(b, t - r)` in pure `Nat`. -/
def vandermondeSum (a b t : Nat) : Nat -> Nat
  | 0 => 0
  | m + 1 => vandermondeSum a b t m + laurentInterpBinom a m * laurentInterpBinom b (t - m)

theorem laurentInterpBinom_gt_zero : ∀ n k : Nat, n < k -> laurentInterpBinom n k = 0
  | 0, 0, h => by omega
  | 0, _ + 1, _ => rfl
  | n + 1, 0, h => by omega
  | n + 1, k + 1, h => by
    change laurentInterpBinom n k + laurentInterpBinom n (k + 1) = 0
    rw [laurentInterpBinom_gt_zero n k (by omega),
        laurentInterpBinom_gt_zero n (k + 1) (by omega)]

theorem laurentInterpBinom_self : ∀ n : Nat, laurentInterpBinom n n = 1
  | 0 => rfl
  | n + 1 => by
    change laurentInterpBinom n n + laurentInterpBinom n (n + 1) = 1
    rw [laurentInterpBinom_self n, laurentInterpBinom_gt_zero n (n + 1) (by omega)]

theorem laurentInterpBinom_add :
    ∀ (a b t : Nat), laurentInterpBinom (a + b) t = vandermondeSum a b t (t + 1)
  | 0, b, t => by
    have hz : ∀ m : Nat, 1 ≤ m -> m ≤ t + 1 ->
        vandermondeSum 0 b t m = laurentInterpBinom b t := by
      intro m hm1 hm_le; induction m with
      | zero => omega
      | succ m' ih =>
        cases m' with
        | zero => simp [vandermondeSum, laurentInterpBinom_zero_right]
        | succ r =>
          unfold vandermondeSum
          rw [ih (by omega) (by omega)]
          simp [laurentInterpBinom]
    rw [Nat.zero_add, hz (t + 1) (by omega) (Nat.le_refl _)]
  | a + 1, b, 0 => by simp [vandermondeSum, laurentInterpBinom_zero_right]
  | a + 1, b, t + 1 => by
    rw [Nat.succ_add a b]
    change laurentInterpBinom (a + b) t + laurentInterpBinom (a + b) (t + 1) =
      vandermondeSum (a + 1) b (t + 1) (t + 2)
    rw [laurentInterpBinom_add a b t, laurentInterpBinom_add a b (t + 1)]
    -- Prove prefix identity for all `m ≤ t + 1`:
    have hpref : ∀ m : Nat, m ≤ t + 1 ->
        vandermondeSum (a + 1) b (t + 1) (m + 1) =
          vandermondeSum a b (t + 1) (m + 1) + vandermondeSum a b t m := by
      intro m hm; induction m with
      | zero => simp [vandermondeSum, laurentInterpBinom_zero_right]
      | succ m' ih =>
        unfold vandermondeSum
        rw [ih (by omega)]
        have hpas : laurentInterpBinom (a + 1) (m' + 1) =
            laurentInterpBinom a m' + laurentInterpBinom a (m' + 1) := rfl
        have hsub : t + 1 - (m' + 1) = t - m' := by omega
        rw [hpas, hsub, Nat.add_mul]
        omega
    rw [Nat.add_comm]
    exact (hpref (t + 1) (Nat.le_refl _)).symm

/-- `blockHitCount W k t` = ways to pick `t` items from `k` blocks of size `W` with `≥ 1` item per block. -/
def blockHitCount (W : Nat) : Nat -> Nat -> Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | k + 1, t =>
    natSumRange t (fun r => laurentInterpBinom W (r + 1) * blockHitCount W k (t - (r + 1)))
where
  natSumRange : Nat -> (Nat -> Nat) -> Nat
    | 0, _ => 0
    | m + 1, f => natSumRange m f + f m

theorem blockHitCount_gt_zero (W : Nat) :
    ∀ k t : Nat, t < k -> blockHitCount W k t = 0
  | 0, _, h => by omega
  | k + 1, t, h => by
    unfold blockHitCount
    have hsum0 : ∀ m : Nat, m ≤ t ->
        blockHitCount.natSumRange m
          (fun r => laurentInterpBinom W (r + 1) * blockHitCount W k (t - (r + 1))) = 0 := by
      intro m hm; induction m with
      | zero => rfl
      | succ m' ih =>
        simp only [blockHitCount.natSumRange, ih (by omega),
          blockHitCount_gt_zero W k (t - (m' + 1)) (by omega), Nat.mul_zero, Nat.add_zero]
    exact hsum0 t (Nat.le_refl t)

theorem blockHitCount_diag (W : Nat) :
    ∀ t : Nat, blockHitCount W t t = W ^ t
  | 0 => rfl
  | t + 1 => by
    unfold blockHitCount
    have hsum_pre : ∀ m : Nat, m ≤ t ->
        blockHitCount.natSumRange m
          (fun r => laurentInterpBinom W (r + 1) * blockHitCount W t (t + 1 - (r + 1))) =
        (if m = 0 then 0 else W * W ^ t) := by
      intro m hm; induction m with
      | zero => rfl
      | succ m' ih =>
        simp only [blockHitCount.natSumRange, ih (by omega)]
        cases m' with
        | zero =>
          simp [laurentInterpBinom_one_right, blockHitCount_diag W t]
        | succ r' =>
          simp only [Nat.succ_ne_zero, ite_false,
            blockHitCount_gt_zero W t (t + 1 - (r' + 2)) (by omega), Nat.mul_zero, Nat.add_zero]
    unfold blockHitCount.natSumRange
    rw [hsum_pre t (Nat.le_refl t)]
    cases t with
    | zero => simp [laurentInterpBinom_one_right, blockHitCount]
    | succ t' =>
      dsimp only
      rw [Nat.sub_self, ite_false_of_w10 (Nat.succ_ne_zero t')]
      have hb0 : blockHitCount W (t' + 1) 0 = 0 := by
        exact blockHitCount_gt_zero W (t' + 1) 0 (by omega)
      rw [hb0, Nat.mul_zero, Nat.add_zero, Nat.pow_succ W (t' + 1), Nat.mul_comm]

def stretchBinomSum (W i t : Nat) : Nat -> Nat
  | 0 => 0
  | m + 1 => stretchBinomSum W i t m + blockHitCount W m t * laurentInterpBinom i m

theorem laurentInterpBinom_mul_stretch (W : Nat) :
    ∀ (i t : Nat), laurentInterpBinom (i * W) t = stretchBinomSum W i t (t + 1)
  | 0, 0 => by simp [stretchBinomSum, blockHitCount, laurentInterpBinom_zero_right]
  | 0, t + 1 => by
    rw [Nat.zero_mul]
    have hz : ∀ m : Nat, m ≤ t + 2 -> stretchBinomSum W 0 (t + 1) m = 0 := by
      intro m _; induction m with
      | zero => rfl
      | succ m' ih =>
        simp only [stretchBinomSum, ih (by omega)]
        cases m' with
        | zero => simp [blockHitCount]
        | succ _ => simp [laurentInterpBinom]
    exact (hz (t + 2) (Nat.le_refl _)).symm
  | i + 1, t => by
    rw [Nat.succ_mul i W, laurentInterpBinom_add (i * W) W t]
    -- Double-sum Fubini identity:
    -- `∑_{m=0}^t laurentInterpBinom (i * W) m * binom(W, t - m) = stretchBinomSum W (i + 1) t (t + 1)`:
    -- Step 1: For any `m ≤ t`, `stretchBinomSum W i m (t + 1) = stretchBinomSum W i m (m + 1)`
    -- because `blockHitCount W k m = 0` for `k > m`!
    have hpad : ∀ (m N : Nat), m + 1 ≤ N ->
        stretchBinomSum W i m N = stretchBinomSum W i m (m + 1) := by
      intro m N hmN; induction N with
      | zero => omega
      | succ N' ihN =>
        by_cases heq : N' = m
        · subst heq; rfl
        · simp only [stretchBinomSum, ihN (by omega),
            blockHitCount_gt_zero W N' m (by omega), Nat.zero_mul, Nat.add_zero]
    -- Step 2: Substitute IH for each `m ≤ t` and swap finite sums over `k ≤ K` (`K ≤ t + 1`):
    let F : Nat -> Nat -> Nat := fun m k =>
      blockHitCount W k m * laurentInterpBinom W (t - m) * laurentInterpBinom i k
    have hvand_F : ∀ M : Nat, M ≤ t + 1 ->
        vandermondeSum (i * W) W t M =
          blockHitCount.natSumRange M (fun m =>
            blockHitCount.natSumRange (t + 1) (fun k => F m k)) := by
      intro M hM; induction M with
      | zero => rfl
      | succ M' ihM =>
        simp only [vandermondeSum, blockHitCount.natSumRange, ihM (by omega)]
        apply congrArg (blockHitCount.natSumRange M' _ + ·)
        rw [laurentInterpBinom_mul_stretch W i M', ← hpad M' (t + 1) hM]
        have hdist : ∀ K : Nat,
            stretchBinomSum W i M' K * laurentInterpBinom W (t - M') =
              blockHitCount.natSumRange K (fun k => F M' k) := by
          intro K; induction K with
          | zero => simp [stretchBinomSum, blockHitCount.natSumRange]
          | succ K' ihK =>
            simp only [stretchBinomSum, blockHitCount.natSumRange, Nat.add_mul, ihK]
            dsimp [F]
            rw [Nat.mul_assoc (blockHitCount W K' M') (laurentInterpBinom i K'),
                Nat.mul_comm (laurentInterpBinom i K'),
                ← Nat.mul_assoc (blockHitCount W K' M')]
        exact hdist (t + 1)
    have hswap : ∀ (M K : Nat),
        blockHitCount.natSumRange M (fun m => blockHitCount.natSumRange K (fun k => F m k)) =
          blockHitCount.natSumRange K (fun k => blockHitCount.natSumRange M (fun m => F m k)) := by
      intro M; induction M with
      | zero =>
        intro K; induction K with
        | zero => rfl
        | succ K' ihK =>
          simp only [blockHitCount.natSumRange] at ihK ⊢
          omega
      | succ M' ihM =>
        intro K
        simp only [blockHitCount.natSumRange, ihM K]
        clear ihM
        induction K with
        | zero => rfl
        | succ K' ihK =>
          simp only [blockHitCount.natSumRange]
          omega
    -- Step 3: For each `k ≤ t`, evaluate `∑_{m=0}^t blockHitCount W k m * binom(W, t - m)`:
    have hcol_k : ∀ k : Nat, k ≤ t ->
        blockHitCount.natSumRange (t + 1) (fun m => F m k) =
          blockHitCount W k t * laurentInterpBinom i k +
          (if k = t then 0 else blockHitCount W (k + 1) t * laurentInterpBinom i k) := by
      intro k hk
      -- Factor out `laurentInterpBinom i k`:
      have hfac : ∀ M : Nat,
          blockHitCount.natSumRange M (fun m => F m k) =
            blockHitCount.natSumRange M
              (fun m => blockHitCount W k m * laurentInterpBinom W (t - m)) *
            laurentInterpBinom i k := by
        intro M; induction M with
        | zero => simp [blockHitCount.natSumRange]
        | succ M' ihM =>
          simp only [blockHitCount.natSumRange, ihM, Nat.add_mul]; rfl
      rw [hfac (t + 1)]
      -- Split `M = t + 1` into `m = t` (`binom(W, 0) = 1`) plus `m = 0 .. t - 1` (`r = t - 1 - m`):
      simp only [blockHitCount.natSumRange, Nat.sub_self, laurentInterpBinom_zero_right, Nat.mul_one]
      by_cases hkt : k = t
      · subst hkt
        have hz_lt : ∀ M : Nat, M ≤ k ->
            blockHitCount.natSumRange M
              (fun m => blockHitCount W k m * laurentInterpBinom W (k - m)) = 0 := by
          intro M hM; induction M with
          | zero => rfl
          | succ M' ihM =>
            simp only [blockHitCount.natSumRange, ihM (by omega),
              blockHitCount_gt_zero W k M' (by omega), Nat.zero_mul, Nat.add_zero]
        rw [hz_lt k (Nat.le_refl k), Nat.zero_add]
        simp
      · rw [ite_false_of_w10 hkt]
        -- Reverse index `r = t - 1 - m` on `0 .. t - 1`:
        have hrev : ∀ (N : Nat), N ≤ t ->
            blockHitCount.natSumRange N
              (fun m => blockHitCount W k m * laurentInterpBinom W (t - m)) +
            blockHitCount.natSumRange (t - N)
              (fun r => laurentInterpBinom W (r + 1) * blockHitCount W k (t - (r + 1))) =
            blockHitCount W (k + 1) t := by
          intro N hN; induction N with
          | zero =>
            simp only [blockHitCount.natSumRange, Nat.zero_add, Nat.sub_zero]
            rfl
          | succ N' ihN =>
            have hsp : t - N' = (t - (N' + 1)) + 1 := by omega
            rw [hsp, blockHitCount.natSumRange] at ihN
            have hidx1 : t - (N' + 1) + 1 = t - N' := by omega
            have hidx2 : t - (t - N') = N' := by omega
            rw [hidx1, hidx2, Nat.mul_comm (laurentInterpBinom W (t - N'))] at ihN
            simp only [blockHitCount.natSumRange]
            omega
        have ht0 := hrev t (Nat.le_refl t)
        simp only [Nat.sub_self, blockHitCount.natSumRange, Nat.add_zero] at ht0
        rw [ht0, Nat.add_comm (blockHitCount W (k + 1) t), Nat.add_mul]
    rw [hvand_F (t + 1) (Nat.le_refl _), hswap (t + 1) (t + 1)]
    -- Telescope over `K ≤ t + 1` using Pascal `binom(i, k) + binom(i, k + 1) = binom(i + 1, k + 1)`:
    have htel : ∀ K : Nat, K ≤ t + 1 ->
        blockHitCount.natSumRange K (fun k => blockHitCount.natSumRange (t + 1) (fun m => F m k)) =
          stretchBinomSum W (i + 1) t K +
          (if K = 0 ∨ K = t + 1 then 0 else blockHitCount W K t * laurentInterpBinom i (K - 1)) := by
      intro K hK; induction K with
      | zero => rfl
      | succ K' ihK =>
        change blockHitCount.natSumRange K' (fun k => blockHitCount.natSumRange (t + 1) (fun m => F m k)) +
            blockHitCount.natSumRange (t + 1) (fun m => F m K') =
          (stretchBinomSum W (i + 1) t K' + blockHitCount W K' t * laurentInterpBinom (i + 1) K') +
          (if K' + 1 = 0 ∨ K' + 1 = t + 1 then 0
           else blockHitCount W (K' + 1) t * laurentInterpBinom i K')
        rw [ihK (by omega), hcol_k K' (by omega)]
        cases K' with
        | zero =>
          have h0_l : (0 = 0 ∨ 0 = t + 1) := Or.inl rfl
          rw [ite_true_of_w10 h0_l, Nat.add_zero]
          simp only [laurentInterpBinom_zero_right, Nat.mul_one]
          by_cases ht0 : 0 = t
          · subst ht0; simp
          · have h0_ne : ¬ (1 = 0 ∨ 1 = t + 1) := by omega
            rw [ite_false_of_w10 ht0, ite_false_of_w10 h0_ne]
            omega
        | succ k0 =>
          have hprev_ne : ¬ (k0 + 1 = 0 ∨ k0 + 1 = t + 1) := by omega
          rw [ite_false_of_w10 hprev_ne]
          simp only [Nat.add_sub_cancel]
          have hpas : blockHitCount W (k0 + 1) t * laurentInterpBinom i k0 +
              blockHitCount W (k0 + 1) t * laurentInterpBinom i (k0 + 1) =
              blockHitCount W (k0 + 1) t * laurentInterpBinom (i + 1) (k0 + 1) := by
            rw [← Nat.mul_add]; rfl
          by_cases hkt : k0 + 1 = t
          · have hcur_t : k0 + 2 = 0 ∨ k0 + 2 = t + 1 := Or.inr (by omega)
            rw [ite_true_of_w10 hkt, ite_true_of_w10 hcur_t]
            omega
          · have hcur_f : ¬ (k0 + 2 = 0 ∨ k0 + 2 = t + 1) := by omega
            rw [ite_false_of_w10 hkt, ite_false_of_w10 hcur_f]
            omega
    rw [htel (t + 1) (Nat.le_refl _)]
    simp

/-- General `(T + 1) × (T + 1)` single-base `(T, U = 1)` confluent Schneider–Laurent matrix (`T = 7` is `8 × 8`). -/
def laurentSingleCT1Mat (T W u : Nat) : Fin (T + 1) -> Fin (T + 1) -> Int :=
  fun i j =>
    if j.val < T then
      (laurentInterpBinom (i.val * W) j.val : Int)
    else
      ((2 ^ (i.val * u) : Nat) : Int)

/-- Explicit `8 × 8` single-base `(T = 7, U = 1)` Schneider–Laurent matrix (`laurentSingleCT1Mat 7 W u`). -/
def laurentSingleC71Mat8 (W u : Nat) : Fin 8 -> Fin 8 -> Int :=
  laurentSingleCT1Mat 7 W u

theorem laurent_unit_binom_exp_det :
    ∀ (T u : Nat), u ≥ 1 ->
      intDet (T + 1) (laurentSingleCT1Mat T 1 u) = (((2 ^ u - 1) ^ T : Nat) : Int) := by
  intro T u hu
  let B : Nat := 2 ^ u - 1
  have h2u_ge2 : 2 ^ u ≥ 2 := by simpa using pow2_mono_nat hu
  have h1B : 1 + B = 2 ^ u := by dsimp [B]; omega
  let cLast : Fin (T + 1) := ⟨T, Nat.lt_succ_self T⟩
  let idx : Nat -> Fin (T + 1) := fun t =>
    if h : t < T + 1 then ⟨t, h⟩ else ⟨0, Nat.zero_lt_succ T⟩
  let coef : Nat -> Int := fun t => Int.ofNat (B ^ t)
  have hne : ∀ t : Nat, t < T -> idx t ≠ cLast := by
    intro t ht heq
    have ht1 : t < T + 1 := by omega
    have hi : idx t = ⟨t, ht1⟩ := by simp [idx, ht1]
    rw [hi] at heq; dsimp [cLast] at heq
    injection heq with htv; omega
  rw [intDet_sub_col_prefix_invariant (T + 1) cLast (laurentSingleCT1Mat T 1 u) T idx coef hne]
  let M_red : Fin (T + 1) -> Fin (T + 1) -> Int := fun i j =>
    if j = cLast then
      laurentSingleCT1Mat T 1 u i cLast - colPrefixComb (laurentSingleCT1Mat T 1 u) idx coef i T
    else
      laurentSingleCT1Mat T 1 u i j
  -- Prove `M_red` is lower triangular with diagonal `(1, 1, ..., 1, B^T)`!
  have hcomb_eq : ∀ i : Fin (T + 1),
      colPrefixComb (laurentSingleCT1Mat T 1 u) idx coef i T =
        Int.ofNat (binomTaylorSum i.val B T) := by
    intro i
    have hstep : ∀ m : Nat, m ≤ T ->
        colPrefixComb (laurentSingleCT1Mat T 1 u) idx coef i m =
          Int.ofNat (binomTaylorSum i.val B m) := by
      intro m hm; induction m with
      | zero => rfl
      | succ m' ihm =>
        unfold colPrefixComb binomTaylorSum; rw [ihm (by omega)]
        have hm1 : m' < T + 1 := by omega
        have hidx_m : idx m' = ⟨m', hm1⟩ := by simp [idx, hm1]
        have hent : laurentSingleCT1Mat T 1 u i (idx m') =
            Int.ofNat (laurentInterpBinom i.val m') := by
          rw [hidx_m]; unfold laurentSingleCT1Mat
          simp [show m' < T by omega]
        rw [hent]; dsimp only [coef]
        simp only [Int.ofNat_eq_natCast, ← Int.natCast_mul, ← Int.natCast_add]
        exact congrArg Nat.cast (by rw [Nat.mul_comm (B ^ m')])
    exact hstep T (Nat.le_refl T)
  have hbin_id : ∀ n : Nat, binomTaylorSum n B (n + 1) = (1 + B) ^ n := by
    intro n; induction n with
    | zero => simp [binomTaylorSum, laurentInterpBinom_zero_right]
    | succ n' ihn =>
      have hstep_b : ∀ k : Nat, k ≤ n' + 1 ->
          binomTaylorSum (n' + 1) B (k + 1) =
            binomTaylorSum n' B (k + 1) + B * binomTaylorSum n' B k := by
        intro k hk; induction k with
        | zero => simp [binomTaylorSum, laurentInterpBinom_zero_right]
        | succ k' ihk =>
          change binomTaylorSum (n' + 1) B (k' + 1) +
              laurentInterpBinom (n' + 1) (k' + 1) * B ^ (k' + 1) =
            (binomTaylorSum n' B (k' + 1) + laurentInterpBinom n' (k' + 1) * B ^ (k' + 1)) +
              B * (binomTaylorSum n' B k' + laurentInterpBinom n' k' * B ^ k')
          rw [ihk (by omega)]
          have hpas : laurentInterpBinom (n' + 1) (k' + 1) =
              laurentInterpBinom n' k' + laurentInterpBinom n' (k' + 1) := rfl
          rw [hpas, Nat.add_mul, Nat.mul_add B, Nat.pow_succ B k',
              ← Nat.mul_assoc (laurentInterpBinom n' k') (B ^ k') B,
              Nat.mul_comm (laurentInterpBinom n' k' * B ^ k') B]
          omega
      rw [hstep_b (n' + 1) (Nat.le_refl _)]
      have hextra : binomTaylorSum n' B (n' + 2) = binomTaylorSum n' B (n' + 1) := by
        change binomTaylorSum n' B (n' + 1) + laurentInterpBinom n' (n' + 1) * B ^ (n' + 1) =
          binomTaylorSum n' B (n' + 1)
        rw [laurentInterpBinom_gt_zero n' (n' + 1) (by omega), Nat.zero_mul, Nat.add_zero]
      rw [hextra, ihn, Nat.pow_succ (1 + B) n', Nat.mul_comm ((1 + B) ^ n') (1 + B),
          Nat.add_mul 1 B, Nat.one_mul]
  have hlast_i : ∀ i : Fin (T + 1),
      M_red i cLast = (if i.val < T then 0 else ((B ^ T : Nat) : Int)) := by
    intro i
    dsimp [M_red]; simp only [ite_true, hcomb_eq i]
    have hexp_i : laurentSingleCT1Mat T 1 u i cLast = Int.ofNat ((1 + B) ^ i.val) := by
      unfold laurentSingleCT1Mat; dsimp [cLast]; simp only [Nat.lt_irrefl, ite_false]
      apply congrArg Int.ofNat
      rw [Nat.mul_comm i.val u, ← pow_pow_eq_mul_w5 2 u i.val, ← h1B]
    rw [hexp_i]
    by_cases hilt : i.val < T
    · rw [ite_true_of_w10 hilt]
      have hpad : ∀ m : Nat, i.val + 1 ≤ m ->
          binomTaylorSum i.val B m = binomTaylorSum i.val B (i.val + 1) := by
        intro m hm; induction m with
        | zero => omega
        | succ m' ihm =>
          by_cases heq : m' = i.val
          · subst heq; rfl
          · change binomTaylorSum i.val B m' + laurentInterpBinom i.val m' * B ^ m' =
              binomTaylorSum i.val B (i.val + 1)
            rw [ihm (by omega), laurentInterpBinom_gt_zero i.val m' (by omega),
                Nat.zero_mul, Nat.add_zero]
      rw [hpad T hilt, hbin_id i.val]; simp
    · have hiT : i.val = T := by have := i.isLt; omega
      rw [ite_false_of_w10 hilt, hiT]
      have hbin_T : binomTaylorSum T B T + B ^ T = (1 + B) ^ T := by
        have huT := hbin_id T
        change binomTaylorSum T B T + laurentInterpBinom T T * B ^ T = (1 + B) ^ T at huT
        rwa [laurentInterpBinom_self T, Nat.one_mul] at huT
      rw [← hbin_T]
      change (((binomTaylorSum T B T + B ^ T : Nat) : Int) -
              ((binomTaylorSum T B T : Nat) : Int)) = ((B ^ T : Nat) : Int)
      rw [Int.natCast_add]; omega
  -- Evaluate lower-triangular determinant of `M_red` by induction on `K`:
  have hlow_eval : ∀ (K : Nat) (A_lt : Fin (K + 1) -> Fin (K + 1) -> Int),
      (∀ i j : Fin (K + 1), i.val < j.val -> A_lt i j = 0) ->
      (∀ i : Fin (K + 1), i.val < K -> A_lt i i = 1) ->
      intDet (K + 1) A_lt = A_lt ⟨K, Nat.lt_succ_self K⟩ ⟨K, Nat.lt_succ_self K⟩ := by
    intro K; induction K with
    | zero =>
      intro A_lt htri _
      rw [intDet_lower_triangular 1 A_lt htri]
      simp [intDet]
    | succ K' ihK =>
      intro A_lt htri hdiag1
      rw [intDet_lower_triangular (K' + 2) A_lt htri]
      dsimp only
      have ha00 : A_lt ⟨0, Nat.zero_lt_succ (K' + 1)⟩ ⟨0, Nat.zero_lt_succ (K' + 1)⟩ = 1 :=
        hdiag1 ⟨0, Nat.zero_lt_succ (K' + 1)⟩ (Nat.zero_lt_succ K')
      rw [ha00, Int.one_mul]
      have hsub_tri : ∀ i j : Fin (K' + 1),
          i.val < j.val -> intSubMat A_lt ⟨0, Nat.zero_lt_succ (K' + 1)⟩ i j = 0 := by
        intro i j hij
        unfold intSubMat skipFinIdx
        simp only [Nat.not_lt_zero, ite_false]
        exact htri ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
          (Nat.succ_lt_succ hij)
      have hsub_d1 : ∀ i : Fin (K' + 1),
          i.val < K' -> intSubMat A_lt ⟨0, Nat.zero_lt_succ (K' + 1)⟩ i i = 1 := by
        intro i hi
        unfold intSubMat skipFinIdx
        simp only [Nat.not_lt_zero, ite_false]
        exact hdiag1 ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ (Nat.succ_lt_succ hi)
      rw [ihK (intSubMat A_lt ⟨0, Nat.zero_lt_succ (K' + 1)⟩) hsub_tri hsub_d1]
      unfold intSubMat skipFinIdx
      simp [Nat.not_lt_zero]
  change intDet (T + 1) M_red = (((2 ^ u - 1) ^ T : Nat) : Int)
  rw [hlow_eval T M_red
    (fun i j hij => by
      by_cases hjc : j = cLast
      · subst hjc
        rw [hlast_i i, ite_true_of_w10 (by dsimp [cLast] at hij; omega)]
      · dsimp [M_red]; rw [ite_false_of_w10 hjc]
        unfold laurentSingleCT1Mat
        have hj_ne_T : j.val ≠ T := fun hv => hjc (Fin.ext hv)
        have hjT : j.val < T := by have := j.isLt; omega
        rw [ite_true_of_w10 hjT, Nat.mul_one, laurentInterpBinom_gt_zero i.val j.val hij]
        rfl)
    (fun i hiT => by
      have hic : i ≠ cLast := fun heq => by rw [heq] at hiT; exact Nat.lt_irrefl T hiT
      dsimp [M_red]; rw [ite_false_of_w10 hic]
      unfold laurentSingleCT1Mat
      rw [ite_true_of_w10 hiT, Nat.mul_one, laurentInterpBinom_self i.val]
      rfl)]
  have hc_eq : (⟨T, Nat.lt_succ_self T⟩ : Fin (T + 1)) = cLast := rfl
  rw [hc_eq, hlast_i cLast]
  simp [cLast, B]

/-- Progressive column-stretch reduction: replacing columns `0 .. m - 1` of `laurentSingleCT1Mat T W u` by `binom(i, j)` factors out `W ^ (0 + 1 + ... + (m - 1))` (`∀ m ≤ T`). -/
def partialStretchMat (T W u m : Nat) : Fin (T + 1) -> Fin (T + 1) -> Int :=
  fun i j =>
    if j.val < m then
      (laurentInterpBinom i.val j.val : Int)
    else
      laurentSingleCT1Mat T W u i j

def triSumNat : Nat -> Nat
  | 0 => 0
  | k + 1 => triSumNat k + k

theorem triSumNat_mul_two : ∀ k : Nat, 2 * triSumNat k = k * (k - 1)
  | 0 => rfl
  | k + 1 => by
    simp only [triSumNat, Nat.mul_add, triSumNat_mul_two k, Nat.add_sub_cancel]
    cases k with
    | zero => rfl
    | succ m =>
      simp only [Nat.add_sub_cancel]
      rw [Nat.mul_comm (m + 1) m, ← Nat.add_mul m 2 (m + 1), Nat.mul_comm (m + 2) (m + 1)]

theorem partialStretchMat_step_det (T W u : Nat) :
    ∀ m : Nat, m ≤ T ->
      intDet (T + 1) (partialStretchMat T W u 0) =
        ((W ^ triSumNat m : Nat) : Int) * intDet (T + 1) (partialStretchMat T W u m) := by
  intro m; induction m with
  | zero =>
    intro _; simp [triSumNat]
  | succ m' ihm =>
    intro hm'
    rw [ihm (by omega)]
    let A := partialStretchMat T W u m'
    let cm : Fin (T + 1) := ⟨m', by omega⟩
    let idx : Nat -> Fin (T + 1) := fun k =>
      if h : k < T + 1 then ⟨k, h⟩ else ⟨0, Nat.zero_lt_succ T⟩
    let coef : Nat -> Int := fun k => Int.ofNat (blockHitCount W k m')
    have hne : ∀ k : Nat, k < m' -> idx k ≠ cm := by
      intro k hk heq
      have hk1 : k < T + 1 := by omega
      have hi : idx k = ⟨k, hk1⟩ := by simp [idx, hk1]
      rw [hi] at heq; dsimp [cm] at heq
      injection heq with hkv; omega
    have hsub := intDet_sub_col_prefix_invariant (T + 1) cm A m' idx coef hne
    let A_sub : Fin (T + 1) -> Fin (T + 1) -> Int := fun i j =>
      if j = cm then A i cm - colPrefixComb A idx coef i m' else A i j
    have hA_sub_eq : A_sub = (fun i j =>
        if j = cm then
          ((W ^ m' : Nat) : Int) * partialStretchMat T W u (m' + 1) i cm
        else partialStretchMat T W u (m' + 1) i j) := by
      funext i j
      by_cases hj : j = cm
      · subst hj; dsimp [A_sub]; simp only [ite_true]
        have hA_cm : A i cm = Int.ofNat (laurentInterpBinom (i.val * W) m') := by
          dsimp [A, partialStretchMat, cm]
          rw [ite_false_of_w10 (Nat.lt_irrefl m')]
          unfold laurentSingleCT1Mat
          dsimp only
          rw [ite_true_of_w10 (by omega : m' < T)]
        have hcomb_m : ∀ k : Nat, k ≤ m' ->
            colPrefixComb A idx coef i k = Int.ofNat (stretchBinomSum W i.val m' k) := by
          intro k hk; induction k with
          | zero => rfl
          | succ k' ihk =>
            unfold colPrefixComb stretchBinomSum; rw [ihk (by omega)]
            have hk1 : k' < T + 1 := by omega
            have hidx_k : idx k' = ⟨k', hk1⟩ := by simp [idx, hk1]
            have hAk : A i (idx k') = Int.ofNat (laurentInterpBinom i.val k') := by
              rw [hidx_k]; dsimp [A, partialStretchMat]
              rw [ite_true_of_w10 (by omega : k' < m')]
            rw [hAk]; dsimp [coef]
        rw [hA_cm, hcomb_m m' (Nat.le_refl m'),
            laurentInterpBinom_mul_stretch W i.val m']
        have hexp_st : stretchBinomSum W i.val m' (m' + 1) =
            stretchBinomSum W i.val m' m' + W ^ m' * laurentInterpBinom i.val m' := by
          change stretchBinomSum W i.val m' m' +
            blockHitCount W m' m' * laurentInterpBinom i.val m' = _
          rw [blockHitCount_diag W m']
        have hnext_cm : partialStretchMat T W u (m' + 1) i cm =
            (laurentInterpBinom i.val m' : Int) := by
          dsimp [partialStretchMat, cm]
          rw [ite_true_of_w10 (Nat.lt_succ_self m')]
        rw [hexp_st, hnext_cm]
        change (((stretchBinomSum W i.val m' m' + W ^ m' * laurentInterpBinom i.val m' : Nat) : Int) -
          ((stretchBinomSum W i.val m' m' : Nat) : Int)) =
          ((W ^ m' : Nat) : Int) * (laurentInterpBinom i.val m' : Int)
        rw [Int.natCast_add, Int.natCast_mul]; omega
      · dsimp [A_sub]; rw [ite_false_of_w10 hj, ite_false_of_w10 hj]
        have hj_ne : j.val ≠ m' := fun hv => hj (Fin.ext hv)
        dsimp [A, partialStretchMat]
        by_cases hlt : j.val < m'
        · rw [ite_true_of_w10 hlt, ite_true_of_w10 (by omega)]
        · rw [ite_false_of_w10 hlt, ite_false_of_w10 (by omega)]
    change _ = ((W ^ triSumNat (m' + 1) : Nat) : Int) * _
    rw [hsub]
    change ((W ^ triSumNat m' : Nat) : Int) * intDet (T + 1) A_sub = _
    rw [hA_sub_eq, intDet_col_scale ((W ^ m' : Nat) : Int) (T + 1) cm,
        ← Int.mul_assoc, ← Int.natCast_mul, ← Nat.pow_add W (triSumNat m') m']
    rfl

theorem laurent_single_base_all_T_exact_det (T W u : Nat) (hW : W ≥ 1) (hu : u ≥ 1) :
    intDet (T + 1) (laurentSingleCT1Mat T W u) =
      ((W ^ (T * (T - 1) / 2) * (2 ^ u - 1) ^ T : Nat) : Int) ∧
    intDet (T + 1) (laurentSingleCT1Mat T W u) > 0 := by
  have hp0 : partialStretchMat T W u 0 = laurentSingleCT1Mat T W u := by
    funext i j; simp [partialStretchMat]
  have hpT : partialStretchMat T W u T = laurentSingleCT1Mat T 1 u := by
    funext i j; dsimp [partialStretchMat]
    by_cases hj : j.val < T
    · simp [hj, laurentSingleCT1Mat]
    · simp [hj, laurentSingleCT1Mat]
  have htot := partialStretchMat_step_det T W u T (Nat.le_refl T)
  rw [hp0, hpT, laurent_unit_binom_exp_det T u hu] at htot
  have htri_eq : triSumNat T = T * (T - 1) / 2 := by
    have h2 := triSumNat_mul_two T
    omega
  rw [htri_eq, ← Int.natCast_mul] at htot
  have hpos_nat : W ^ (T * (T - 1) / 2) * (2 ^ u - 1) ^ T ≥ 1 := by
    have h2u : 2 ^ u ≥ 2 := by simpa using pow2_mono_nat hu
    exact Nat.mul_le_mul (nat_pow_pos_of_pos W hW _) (nat_pow_pos_of_pos (2 ^ u - 1) (by omega) T)
  refine ⟨htot, ?_⟩
  rw [htot]
  omega

-- Two-Base `6 × 6` Rank-2 Vandermonde `(T = 3, U = 2)` Matrices & Upgraded Confluent Extrapolation:

def laurentColsC32_6 (u : Nat) (j : Fin 6) : Nat × Nat :=
  match j.val with
  | 0 => (0, 0) | 1 => (1, 0) | 2 => (2, 0)
  | 3 => (0, u) | 4 => (1, u) | _ => (2, u)

def laurentTwoBaseT3U2Mat6 (W K u : Nat) : Fin 6 -> Fin 6 -> Int :=
  laurentInterpMat W K 6 laurentRowsTwoBase6 (laurentColsC32_6 u)

/--
  Theorem W11.2b (`laurent_universal_single_base_upgraded_confluent_and_laplace_bound`, `zero custom axioms`):
  1. **Pure-`Int` Column-Majorant Laplace Upper Bound (`∀ L : Nat`)**:
     `∀ i j, (A i j).natAbs ≤ B j -> (intDet L A).natAbs ≤ natFact L * colBoundProdPrefix L B L`.
  2. **Universal `∀ T, W, u ≥ 1` `(T + 1) × (T + 1)` Single-Base Closed Form & `8 × 8` Corollary**:
     `intDet (T + 1) (laurentSingleCT1Mat T W u) = W^(T*(T - 1)/2) * (2^u - 1)^T > 0`, giving at
     `T = 7` (`8 × 8`) `intDet 8 (laurentSingleC71Mat8 W u) = W ^ 21 * (2 ^ u - 1) ^ 7 > 0`!
  3. **Upgraded `2^u * (2^u - 1)^(2 * T)` Confluent Derivative-Block Extrapolation (`∀ L, ∀ T ≥ 1`)**:
     Strictly strengthens Wave 10's `(2^u - 1)^(2T - 1)` divisibility by an extra factor `(2^u - 1)`
     via cross-column `T * binom(x, T)` cancellation between `c0 = (0, u)` and `c1 = (1, u)`!
  4. **Exact `2^(3 * u) * (2^u - 1)^9` Order-3 Confluent Block Divisibility (`∀ L`, `(0, u), (1, u), (2, u)`)**
     & `6 × 6` Two-Base `(T = 3, U = 2)` `(2^K - 3^W)` Zero-Gap Congruence!
-/
theorem laurent_universal_single_base_upgraded_confluent_and_laplace_bound :
    (∀ (L : Nat) (A : Fin L -> Fin L -> Int) (B : Fin L -> Nat),
      (∀ (i j : Fin L), (A i j).natAbs ≤ B j) ->
      (intDet L A).natAbs ≤ natFact L * colBoundProdPrefix L B L) ∧
    ((∀ (T W u : Nat), W ≥ 1 -> u ≥ 1 ->
        intDet (T + 1) (laurentSingleCT1Mat T W u) =
          ((W ^ (T * (T - 1) / 2) * (2 ^ u - 1) ^ T : Nat) : Int) ∧
        intDet (T + 1) (laurentSingleCT1Mat T W u) > 0) ∧
     (∀ (W u : Nat), W ≥ 1 -> u ≥ 1 ->
        intDet 8 (laurentSingleC71Mat8 W u) =
          ((W ^ 21 * (2 ^ u - 1) ^ 7 : Nat) : Int) ∧
        intDet 8 (laurentSingleC71Mat8 W u) > 0)) ∧
    (∀ (W K L T u : Nat) (rows cols : Fin L -> Nat × Nat)
       (idx : Nat -> Fin L) (c0 c1 : Fin L),
      T ≥ 1 -> u ≥ 1 -> c0 ≠ c1 ->
      (∀ t : Nat, t < T -> cols (idx t) = (t, 0)) ->
      cols c0 = (0, u) -> cols c1 = (1, u) ->
      let M0 : Fin L -> Fin L -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2 (cols j).1 (cols j).2 : Int)
      ((2 ^ u * (2 ^ u - 1) ^ (2 * T) : Nat) : Int) ∣ intDet L M0) ∧
    (∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 -> u ≥ 1 -> 3 ^ W < 2 ^ K ->
      let M0_t3u2 : Fin 6 -> Fin 6 -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (laurentRowsTwoBase6 i).1 (laurentRowsTwoBase6 i).2
          (laurentColsC32_6 u j).1 (laurentColsC32_6 u j).2 : Int)
      (((2 ^ K - 3 ^ W : Nat) : Int) ∣
        (intDet 6 M0_t3u2 - intDet 6 (laurentTwoBaseT3U2Mat6 W K (W * u)))) ∧
      (((2 ^ (3 * u) * (2 ^ u - 1) ^ 9 : Nat) : Int) ∣ intDet 6 M0_t3u2)) := by
  have hpos_nz : ∀ n : Nat, n ≥ 1 -> Int.ofNat n ≠ 0 := by
    intro n hn; change (n : Int) ≠ 0; omega
  refine ⟨intDet_natAbs_le_fact_mul_colProd,
          ⟨fun T W u hW hu => laurent_single_base_all_T_exact_det T W u hW hu,
           fun W u hW hu => laurent_single_base_all_T_exact_det 7 W u hW hu⟩,
          ?_, ?_⟩
  · -- Part 3: Upgraded `2^u * (2^u - 1)^(2 * T)` joint confluent divisibility:
    intro W K L T u rows cols idx c0 c1 hT1 hu hne_c hpoly hexp0 hexp1
    dsimp only
    let M0 : Fin L -> Fin L -> Int := fun i j =>
      (laurentZeroGapIntEntry W K (rows i).1 (rows i).2 (cols j).1 (cols j).2 : Int)
    let B : Nat := 2 ^ u - 1
    have h2u_ge2 : 2 ^ u ≥ 2 := by simpa using pow2_mono_nat hu
    have h1B : 1 + B = 2 ^ u := by dsimp [B]; omega
    have hne_c0 : ∀ t : Nat, t < T -> idx t ≠ c0 := by
      intro t ht heq
      have hc := hpoly t ht; rw [heq, hexp0] at hc
      injection hc with _ hu0; omega
    have hne_c1 : ∀ t : Nat, t < T -> idx t ≠ c1 := by
      intro t ht heq
      have hc := hpoly t ht; rw [heq, hexp1] at hc
      injection hc with _ hu0; omega
    -- Step 3.1: Reduce `c0` modulo `B^T` and factor `B^T` out of column `c0`:
    let coef0 : Nat -> Int := fun t => Int.ofNat (B ^ t)
    rw [intDet_sub_col_prefix_invariant L c0 M0 T idx coef0 hne_c0]
    let M0_sub : Fin L -> Fin L -> Int := fun i j =>
      if j = c0 then M0 i c0 - colPrefixComb M0 idx coef0 i T else M0 i j
    let D0 : Int := Int.ofNat (B ^ T)
    -- Exact formula for `q0(x) := ((1 + B)^x - binomTaylorSum x B T) / B^T = binom(x, T) + B * u0(x)`:
    have hq0_spec : ∀ i : Fin L,
        let x := (rows i).1 * W + (rows i).2 * K
        ∃ (q0i u0i : Nat),
          M0_sub i c0 = D0 * Int.ofNat q0i ∧
          q0i = laurentInterpBinom x T + B * u0i := by
      intro i; dsimp only
      let x := (rows i).1 * W + (rows i).2 * K
      have hM0_i : M0 i c0 = Int.ofNat ((1 + B) ^ x) := by
        dsimp [M0]; rw [hexp0]; unfold laurentZeroGapIntEntry
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
            dsimp [M0]; rw [hpoly m' (by omega)]; unfold laurentZeroGapIntEntry
            apply congrArg Int.ofNat
            change laurentInterpBinom x m' * 2 ^ (x * 0) = _
            rw [Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
          rw [hm0_t]; dsimp only [coef0]
          simp only [Int.ofNat_eq_natCast, ← Int.natCast_mul, ← Int.natCast_add]
          exact congrArg Nat.cast (by rw [Nat.mul_comm (B ^ m')])
      rcases binomTaylorSum_remainder_dvd x B (T + 1) with ⟨hle_T1, u0i, hu0i⟩
      have hbt_step : binomTaylorSum x B (T + 1) =
          binomTaylorSum x B T + laurentInterpBinom x T * B ^ T := rfl
      have hle_T : binomTaylorSum x B T ≤ (1 + B) ^ x := by omega
      let q0i := laurentInterpBinom x T + B * u0i
      have hsub_nat : (1 + B) ^ x - binomTaylorSum x B T = B ^ T * q0i := by
        dsimp [q0i]
        rw [Nat.pow_succ B T, Nat.mul_assoc (B ^ T) B u0i] at hu0i
        rw [Nat.mul_add (B ^ T), Nat.mul_comm (B ^ T) (laurentInterpBinom x T)]
        omega
      refine ⟨q0i, u0i, ?_, rfl⟩
      dsimp [M0_sub, D0]; simp only [ite_true, hM0_i, hcomb_i T (Nat.le_refl T)]
      change (((1 + B) ^ x : Nat) : Int) - ((binomTaylorSum x B T : Nat) : Int) =
        ((B ^ T : Nat) : Int) * ((q0i : Nat) : Int)
      rw [← Int.natCast_sub hle_T, hsub_nat, Int.natCast_mul]
    have hD0_nz : D0 ≠ 0 := hpos_nz (B ^ T) (nat_pow_pos_of_pos B (by dsimp [B]; omega) T)
    let Q_mat : Fin L -> Fin L -> Int := fun i j =>
      if j = c0 then M0_sub i c0 / D0 else M0_sub i j
    have hscale0 : M0_sub = (fun i j => if j = c0 then D0 * Q_mat i c0 else Q_mat i j) := by
      funext i j
      by_cases hj : j = c0
      · subst hj; dsimp [Q_mat]; simp only [ite_true]
        rcases hq0_spec i with ⟨q0i, _, hq0, _⟩
        rw [hq0, Int.mul_comm D0, Int.mul_ediv_cancel _ hD0_nz, Int.mul_comm]
      · dsimp [Q_mat]; simp [hj]
    change ((2 ^ u * (2 ^ u - 1) ^ (2 * T) : Nat) : Int) ∣ intDet L M0_sub
    rw [hscale0, intDet_col_scale D0 L c0 Q_mat]
    -- Step 3.2: Subtract `∑_{t=0}^{T-2} 2^u * (t + 1) * B^t * idx(t + 1)` PLUS `2^u * T * B^(T - 1) * c0` from `c1`!
    let idx1 : Nat -> Fin L := fun s => if s < T - 1 then idx (s + 1) else c0
    let coef1 : Nat -> Int := fun s =>
      if s < T - 1 then Int.ofNat (2 ^ u * (s + 1) * B ^ s)
      else Int.ofNat (2 ^ u * T * B ^ (T - 1))
    have hne1 : ∀ s : Nat, s < T -> idx1 s ≠ c1 := by
      intro s hs
      dsimp [idx1]
      by_cases hslt : s < T - 1
      · rw [ite_true_of_w10 hslt]; exact hne_c1 (s + 1) (by omega)
      · rw [ite_false_of_w10 hslt]; exact hne_c
    rw [intDet_sub_col_prefix_invariant L c1 Q_mat T idx1 coef1 hne1]
    -- Every entry in column `c1` is now divisible by `2^u * B^T`:
    have hdvd_c1 : ((2 ^ u * B ^ T : Nat) : Int) ∣
        intDet L (fun i j =>
          if j = c1 then Q_mat i c1 - colPrefixComb Q_mat idx1 coef1 i T else Q_mat i j) := by
      apply intDet_col_dvd ((2 ^ u * B ^ T : Nat) : Int) L c1
      intro i
      simp only [ite_true]
      let x := (rows i).1 * W + (rows i).2 * K
      have hc1_ne0 : c1 ≠ c0 := Ne.symm hne_c
      have hQc1 : Q_mat i c1 = (laurentZeroGapIntEntry W K (rows i).1 (rows i).2 1 u : Int) := by
        dsimp [Q_mat, M0_sub]; simp only [hc1_ne0, ite_false]; dsimp [M0]; rw [hexp1]
      rcases hq0_spec i with ⟨q0i, u0i, hM0_q0, hq0_val⟩
      have hQc0 : Q_mat i c0 = (q0i : Int) := by
        dsimp [Q_mat]; simp only [ite_true, hM0_q0, Int.ofNat_eq_natCast]
        rw [Int.mul_comm D0, Int.mul_ediv_cancel _ hD0_nz]
      -- Unroll last step `T = (T - 1) + 1` of `colPrefixComb`:
      have hT_sp : T = (T - 1) + 1 := by omega
      have hcomb_last : colPrefixComb Q_mat idx1 coef1 i T =
          colPrefixComb Q_mat idx1 coef1 i (T - 1) +
            Int.ofNat (2 ^ u * T * B ^ (T - 1)) * (q0i : Int) := by
        have hidx_last : idx1 (T - 1) = c0 := by dsimp [idx1]; simp
        have hcoef_last : coef1 (T - 1) = Int.ofNat (2 ^ u * T * B ^ (T - 1)) := by
          dsimp [coef1]; simp
        calc
          colPrefixComb Q_mat idx1 coef1 i T
              = colPrefixComb Q_mat idx1 coef1 i ((T - 1) + 1) := congrArg (colPrefixComb Q_mat idx1 coef1 i) hT_sp
          _ = colPrefixComb Q_mat idx1 coef1 i (T - 1) + coef1 (T - 1) * Q_mat i (idx1 (T - 1)) := rfl
          _ = colPrefixComb Q_mat idx1 coef1 i (T - 1) +
                Int.ofNat (2 ^ u * T * B ^ (T - 1)) * (q0i : Int) := by
                rw [hidx_last, hcoef_last, hQc0]
      rw [hcomb_last]
      cases hx : x with
      | zero =>
        have hQc1_0 : Q_mat i c1 = 0 := by
          rw [hQc1]; unfold laurentZeroGapIntEntry
          change ((laurentInterpBinom x 1 * 2 ^ (x * u) : Nat) : Int) = 0
          rw [hx]; simp [laurentInterpBinom]
        have hpre_0 : ∀ m : Nat, m ≤ T - 1 -> colPrefixComb Q_mat idx1 coef1 i m = 0 := by
          intro m hm; induction m with
          | zero => rfl
          | succ m' ihm =>
            unfold colPrefixComb; rw [ihm (by omega)]
            have hm_lt : m' < T - 1 := by omega
            have hi_m : idx1 m' = idx (m' + 1) := by dsimp [idx1]; rw [ite_true_of_w10 hm_lt]
            have hQm : Q_mat i (idx (m' + 1)) = 0 := by
              have hne_m := hne_c0 (m' + 1) (by omega)
              dsimp [Q_mat, M0_sub]; simp only [hne_m, ite_false]; dsimp [M0]
              rw [hpoly (m' + 1) (by omega)]; unfold laurentZeroGapIntEntry
              change ((laurentInterpBinom x (m' + 1) * 2 ^ (x * 0) : Nat) : Int) = 0
              rw [hx]; simp [laurentInterpBinom]
            rw [hi_m, hQm, Int.mul_zero, Int.add_zero]
        -- Also at `x = 0`, `q0i = 0`:
        have hq0_0 : q0i = 0 := by
          have hb_0 : (1 + B) ^ x - binomTaylorSum x B T = 0 := by
            rw [hx]
            have hb_z : ∀ m : Nat, m ≥ 1 -> binomTaylorSum 0 B m = 1 := by
              intro m hm1; induction m with
              | zero => omega
              | succ m' ihm =>
                cases m' with
                | zero => simp [binomTaylorSum, laurentInterpBinom_zero_right]
                | succ r =>
                  unfold binomTaylorSum
                  rw [ihm (by omega)]
                  simp [laurentInterpBinom]
            rw [hb_z T hT1]; simp
          have h1 := hM0_q0
          dsimp [M0_sub] at h1; simp only [ite_true] at h1
          have hM0_z : M0 i c0 = 1 := by
            dsimp [M0]; rw [hexp0]; unfold laurentZeroGapIntEntry
            change ((laurentInterpBinom x 0 * 2 ^ (x * u) : Nat) : Int) = 1
            rw [hx]; simp [laurentInterpBinom_zero_right]
          have hcz : colPrefixComb M0 idx coef0 i T = 1 := by
            have hstep_z : ∀ m : Nat, 1 ≤ m -> m ≤ T -> colPrefixComb M0 idx coef0 i m = 1 := by
              intro m hm1 hmT; induction m with
              | zero => omega
              | succ m' ihm =>
                cases m' with
                | zero =>
                  unfold colPrefixComb; dsimp [coef0, M0]
                  rw [hpoly 0 hT1]; unfold laurentZeroGapIntEntry
                  change 0 + 1 * ((laurentInterpBinom x 0 * 2 ^ (x * 0) : Nat) : Int) = 1
                  rw [hx]; simp [laurentInterpBinom_zero_right]
                | succ r =>
                  unfold colPrefixComb; rw [ihm (by omega) (by omega)]
                  dsimp [M0]; rw [hpoly (r + 1) (by omega)]; unfold laurentZeroGapIntEntry
                  change 1 + coef0 (r + 1) * ((laurentInterpBinom x (r + 1) * 2 ^ (x * 0) : Nat) : Int) = 1
                  rw [hx]; simp [laurentInterpBinom]
            exact hstep_z T hT1 (Nat.le_refl T)
          rw [hM0_z, hcz] at h1
          have hBT_pos := nat_pow_pos_of_pos B (by dsimp [B]; omega) T
          dsimp [D0] at h1
          change (0 : Int) = Int.ofNat (B ^ T * q0i) at h1
          have hz_nat : B ^ T * q0i = 0 := Int.ofNat.inj h1.symm
          rcases Nat.mul_eq_zero.mp hz_nat with h0 | h0 <;> omega
        rw [hQc1_0, hpre_0 (T - 1) (Nat.le_refl _), hq0_0]
        exact ⟨0, by simp⟩
      | succ y =>
        have hQc1_y : Q_mat i c1 = Int.ofNat (2 ^ u * (y + 1) * (1 + B) ^ y) := by
          rw [hQc1]; unfold laurentZeroGapIntEntry
          apply congrArg Int.ofNat
          change laurentInterpBinom x 1 * 2 ^ (x * u) = 2 ^ u * (y + 1) * (1 + B) ^ y
          rw [hx, laurentInterpBinom_one_right (y + 1), Nat.succ_mul y u, Nat.pow_add 2 (y * u) u,
              Nat.mul_comm y u, ← pow_pow_eq_mul_w5 2 u y, h1B]
          rw [← Nat.mul_assoc (y + 1) ((2 ^ u) ^ y) (2 ^ u),
              Nat.mul_comm ((y + 1) * (2 ^ u) ^ y) (2 ^ u), Nat.mul_assoc]
        have hpre_y : ∀ m : Nat, m ≤ T - 1 ->
            colPrefixComb Q_mat idx1 coef1 i m =
              Int.ofNat (2 ^ u * (y + 1) * binomTaylorSum y B m) := by
          intro m hm; induction m with
          | zero => simp [colPrefixComb, binomTaylorSum]
          | succ m' ihm =>
            unfold colPrefixComb binomTaylorSum; rw [ihm (by omega)]
            have hm_lt : m' < T - 1 := by omega
            have hi_m : idx1 m' = idx (m' + 1) := by dsimp [idx1]; rw [ite_true_of_w10 hm_lt]
            have hc_m : coef1 m' = Int.ofNat (2 ^ u * (m' + 1) * B ^ m') := by
              dsimp [coef1]; rw [ite_true_of_w10 hm_lt]
            have hQm : Q_mat i (idx (m' + 1)) = Int.ofNat (laurentInterpBinom (y + 1) (m' + 1)) := by
              have hne_m := hne_c0 (m' + 1) (by omega)
              dsimp [Q_mat, M0_sub]; simp only [hne_m, ite_false]; dsimp [M0]
              rw [hpoly (m' + 1) (by omega)]; unfold laurentZeroGapIntEntry
              apply congrArg Int.ofNat
              change laurentInterpBinom x (m' + 1) * 2 ^ (x * 0) = _
              rw [hx, Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
            rw [hi_m, hc_m, hQm]
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
        rw [hQc1_y, hpre_y (T - 1) (Nat.le_refl _)]
        -- Expand `(1 + B)^y - binomTaylorSum y B (T - 1) = laurentInterpBinom y (T - 1) * B^(T - 1) + B^T * u1i`:
        rcases binomTaylorSum_remainder_dvd y B T with ⟨hle_yT, u1i, hu1i⟩
        have hbt_y : binomTaylorSum y B T =
            binomTaylorSum y B (T - 1) + laurentInterpBinom y (T - 1) * B ^ (T - 1) :=
          (congrArg (binomTaylorSum y B) hT_sp).trans rfl
        have habs_T : (y + 1) * laurentInterpBinom y (T - 1) = T * laurentInterpBinom (y + 1) T := by
          have h := (laurentInterpBinom_succ_mul y (T - 1)).symm
          rwa [← hT_sp] at h
        have hq0_y : q0i = laurentInterpBinom (y + 1) T + B * u0i := by
          change q0i = laurentInterpBinom x T + B * u0i at hq0_val
          rwa [hx] at hq0_val
        -- Now compute the exact `Int` difference!
        have h1_nat : 2 ^ u * (y + 1) * (1 + B) ^ y =
            2 ^ u * (y + 1) * binomTaylorSum y B (T - 1) +
            2 ^ u * T * B ^ (T - 1) * laurentInterpBinom (y + 1) T +
            (2 ^ u * B ^ T) * ((y + 1) * u1i) := by
          have hy_exp : (1 + B) ^ y =
              binomTaylorSum y B (T - 1) + laurentInterpBinom y (T - 1) * B ^ (T - 1) + B ^ T * u1i := by
            omega
          rw [hy_exp, Nat.mul_add (2 ^ u * (y + 1)), Nat.mul_add (2 ^ u * (y + 1))]
          have hmid : 2 ^ u * (y + 1) * (laurentInterpBinom y (T - 1) * B ^ (T - 1)) =
              2 ^ u * T * B ^ (T - 1) * laurentInterpBinom (y + 1) T := by
            calc
              2 ^ u * (y + 1) * (laurentInterpBinom y (T - 1) * B ^ (T - 1))
                  = 2 ^ u * ((y + 1) * laurentInterpBinom y (T - 1)) * B ^ (T - 1) := by
                    rw [Nat.mul_assoc (2 ^ u) (y + 1), ← Nat.mul_assoc (y + 1),
                        ← Nat.mul_assoc (2 ^ u)]
              _ = 2 ^ u * T * B ^ (T - 1) * laurentInterpBinom (y + 1) T := by
                    rw [habs_T, ← Nat.mul_assoc (2 ^ u) T,
                        Nat.mul_assoc (2 ^ u * T) (laurentInterpBinom (y + 1) T) (B ^ (T - 1)),
                        Nat.mul_comm (laurentInterpBinom (y + 1) T) (B ^ (T - 1)),
                        ← Nat.mul_assoc (2 ^ u * T)]
          have htail : 2 ^ u * (y + 1) * (B ^ T * u1i) = (2 ^ u * B ^ T) * ((y + 1) * u1i) := by
            rw [Nat.mul_assoc (2 ^ u) (y + 1), ← Nat.mul_assoc (y + 1) (B ^ T) u1i,
                Nat.mul_comm (y + 1) (B ^ T), Nat.mul_assoc (B ^ T), ← Nat.mul_assoc (2 ^ u)]
          rw [hmid, htail]
        have h2_nat : 2 ^ u * T * B ^ (T - 1) * q0i =
            2 ^ u * T * B ^ (T - 1) * laurentInterpBinom (y + 1) T +
            (2 ^ u * B ^ T) * (T * u0i) := by
          rw [hq0_y, Nat.mul_add]
          apply congrArg (2 ^ u * T * B ^ (T - 1) * laurentInterpBinom (y + 1) T + ·)
          have hB_pow : B ^ (T - 1) * B = B ^ T :=
            (Nat.pow_succ B (T - 1)).symm.trans (congrArg (B ^ ·) hT_sp.symm)
          calc
            2 ^ u * T * B ^ (T - 1) * (B * u0i)
                = 2 ^ u * T * (B ^ (T - 1) * B) * u0i := by
                  rw [← Nat.mul_assoc (2 ^ u * T * B ^ (T - 1)) B u0i,
                      Nat.mul_assoc (2 ^ u * T) (B ^ (T - 1)) B]
            _ = (2 ^ u * B ^ T) * (T * u0i) := by
                  rw [hB_pow, Nat.mul_assoc (2 ^ u) T (B ^ T), Nat.mul_comm T (B ^ T),
                      ← Nat.mul_assoc (2 ^ u) (B ^ T) T, Nat.mul_assoc (2 ^ u * B ^ T)]
        refine ⟨((y + 1) * u1i : Int) - (T * u0i : Int), ?_⟩
        simp only [Int.ofNat_eq_natCast]
        have h1_int := congrArg (fun n : Nat => (n : Int)) h1_nat
        have h2_int := congrArg (fun n : Nat => (n : Int)) h2_nat
        simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_one] at h1_int h2_int ⊢
        rw [Int.mul_sub]
        generalize ((2 ^ u : Nat) : Int) * ((B ^ T : Nat) : Int) = UBT at h1_int h2_int ⊢
        generalize ((y : Int) + 1) * (u1i : Int) = YU1 at h1_int ⊢
        generalize (T : Int) * (u0i : Int) = TU0 at h2_int ⊢
        omega
    rcases hdvd_c1 with ⟨q_rem, hq_rem⟩
    rw [hq_rem]
    refine ⟨q_rem, ?_⟩
    have hpow_2T : B ^ T * (2 ^ u * B ^ T) = 2 ^ u * B ^ (2 * T) := by
      rw [← Nat.mul_assoc (B ^ T) (2 ^ u), Nat.mul_comm (B ^ T) (2 ^ u), Nat.mul_assoc,
          ← Nat.pow_add B T T, ← Nat.two_mul T]
    have hp_int := congrArg (fun n : Nat => (n : Int)) hpow_2T
    simp only [D0, B, Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_pow] at hp_int ⊢
    rw [← Int.mul_assoc, hp_int]
  · -- Part 4: `6 × 6` Two-Base `(T = 3, U = 2)` `(2^K - 3^W)` congruence + `2^(3u) * (2^u - 1)^9` divisibility:
    intro W K u _ _ hu hgt
    dsimp only
    have hdvd_diff := (laurent_wdilated_zero_gap_entry_and_det_congruence.2
      W K 6 laurentRowsTwoBase6 (laurentColsC32_6 u) hgt).1
    have hMW_eq : (fun i j : Fin 6 =>
        (laurentInterpEntry W K (laurentRowsTwoBase6 i).1 (laurentRowsTwoBase6 i).2
          (laurentColsC32_6 u j).1 (W * (laurentColsC32_6 u j).2) : Int)) =
        laurentTwoBaseT3U2Mat6 W K (W * u) := by
      funext i j
      unfold laurentTwoBaseT3U2Mat6 laurentInterpMat laurentColsC32_6
      have hj_c : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5 := by
        have := j.isLt; omega
      rcases hj_c with h0 | h1 | h2 | h3 | h4 | h5
      · simp [h0]
      · simp [h1]
      · simp [h2]
      · simp [h3]
      · simp [h4]
      · simp [h5]
    rw [hMW_eq] at hdvd_diff
    refine ⟨hdvd_diff, ?_⟩
    -- Order-3 confluent elimination on `M0_t3u2` (`c0 = 3, c1 = 4, c2 = 5`, `T = 3`):
    let M0 : Fin 6 -> Fin 6 -> Int := fun i j =>
      (laurentZeroGapIntEntry W K (laurentRowsTwoBase6 i).1 (laurentRowsTwoBase6 i).2
        (laurentColsC32_6 u j).1 (laurentColsC32_6 u j).2 : Int)
    let P : Nat := 2 ^ u
    let B : Nat := P - 1
    have hP_ge2 : P ≥ 2 := by dsimp [P]; simpa using pow2_mono_nat hu
    have h1B : 1 + B = P := by dsimp [B]; omega
    let idx0 : Nat -> Fin 6 := fun t => if h : t < 6 then ⟨t, h⟩ else ⟨0, by decide⟩
    let c0 : Fin 6 := ⟨3, by decide⟩
    let c1 : Fin 6 := ⟨4, by decide⟩
    let c2 : Fin 6 := ⟨5, by decide⟩
    -- Column `c0` reduction by `B^3`:
    let coef0 : Nat -> Int := fun t => Int.ofNat (B ^ t)
    have hne0 : ∀ t : Nat, t < 3 -> idx0 t ≠ c0 := by
      intro t ht; rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl <;> decide
    change (∃ q : Int, intDet 6 M0 = Int.ofNat (2 ^ (3 * u) * (2 ^ u - 1) ^ 9) * q)
    rw [intDet_sub_col_prefix_invariant 6 c0 M0 3 idx0 coef0 hne0]
    let M1 : Fin 6 -> Fin 6 -> Int := fun i j =>
      if j = c0 then M0 i c0 - colPrefixComb M0 idx0 coef0 i 3 else M0 i j
    -- Taylor remainder for `x = (rows i).1 * W + (rows i).2 * K` up to order 5:
    have hq0_t3 : ∀ i : Fin 6,
        ∃ (q0i u0i : Nat),
          M1 i c0 = Int.ofNat (B ^ 3) * Int.ofNat q0i ∧
          q0i = laurentInterpBinom ((laurentRowsTwoBase6 i).1 * W + (laurentRowsTwoBase6 i).2 * K) 3 +
                laurentInterpBinom ((laurentRowsTwoBase6 i).1 * W + (laurentRowsTwoBase6 i).2 * K) 4 * B +
                B ^ 2 * u0i := by
      intro i
      let x := (laurentRowsTwoBase6 i).1 * W + (laurentRowsTwoBase6 i).2 * K
      have hM0_c0 : M0 i c0 = Int.ofNat ((1 + B) ^ x) := by
        dsimp only [M0, c0]; rw [show laurentColsC32_6 u ⟨3, by decide⟩ = (0, u) from rfl]
        unfold laurentZeroGapIntEntry; apply congrArg Int.ofNat
        change laurentInterpBinom x 0 * 2 ^ (x * u) = (1 + B) ^ x
        rw [laurentInterpBinom_zero_right, Nat.one_mul, Nat.mul_comm x u,
            ← pow_pow_eq_mul_w5 2 u x, h1B]
      have hcomb0 : colPrefixComb M0 idx0 coef0 i 3 = Int.ofNat (binomTaylorSum x B 3) := by
        change ((0 + coef0 0 * M0 i (idx0 0)) + coef0 1 * M0 i (idx0 1)) + coef0 2 * M0 i (idx0 2) =
          Int.ofNat (((0 + laurentInterpBinom x 0 * B ^ 0) + laurentInterpBinom x 1 * B ^ 1) +
            laurentInterpBinom x 2 * B ^ 2)
        have hm0 : M0 i (idx0 0) = Int.ofNat (laurentInterpBinom x 0) := by
          change (laurentZeroGapIntEntry W K _ _ 0 0 : Int) = _
          unfold laurentZeroGapIntEntry; dsimp [x]; simp
        have hm1 : M0 i (idx0 1) = Int.ofNat (laurentInterpBinom x 1) := by
          change (laurentZeroGapIntEntry W K _ _ 1 0 : Int) = _
          unfold laurentZeroGapIntEntry; dsimp [x]; simp
        have hm2 : M0 i (idx0 2) = Int.ofNat (laurentInterpBinom x 2) := by
          change (laurentZeroGapIntEntry W K _ _ 2 0 : Int) = _
          unfold laurentZeroGapIntEntry; dsimp [x]; simp
        rw [hm0, hm1, hm2]; dsimp only [coef0]
        have hn : (0 + B ^ 0 * laurentInterpBinom x 0 + B ^ 1 * laurentInterpBinom x 1 +
            B ^ 2 * laurentInterpBinom x 2) =
            (((0 + laurentInterpBinom x 0 * B ^ 0) + laurentInterpBinom x 1 * B ^ 1) +
              laurentInterpBinom x 2 * B ^ 2) := by
          rw [Nat.mul_comm (B ^ 0), Nat.mul_comm (B ^ 1), Nat.mul_comm (B ^ 2)]
        exact congrArg Int.ofNat hn
      rcases binomTaylorSum_remainder_dvd x B 5 with ⟨hle5, u0i, hu0i⟩
      have hb5 : binomTaylorSum x B 5 =
          binomTaylorSum x B 3 + laurentInterpBinom x 3 * B ^ 3 + laurentInterpBinom x 4 * B ^ 4 := rfl
      have hle3 : binomTaylorSum x B 3 ≤ (1 + B) ^ x := by omega
      let q0i := laurentInterpBinom x 3 + laurentInterpBinom x 4 * B + B ^ 2 * u0i
      have hsub3 : (1 + B) ^ x - binomTaylorSum x B 3 = B ^ 3 * q0i := by
        have hp4 : B ^ 4 = B ^ 3 * B := rfl
        have hp5 : B ^ 5 = B ^ 3 * B ^ 2 := by
          rw [show (5 : Nat) = 3 + 2 from rfl, Nat.pow_add]
        rw [hp4] at hb5
        rw [hp5] at hu0i
        have hrhs_eq : laurentInterpBinom x 3 * B ^ 3 +
            laurentInterpBinom x 4 * (B ^ 3 * B) + B ^ 3 * B ^ 2 * u0i = B ^ 3 * q0i := by
          dsimp only [q0i]
          rw [Nat.mul_add (B ^ 3), Nat.mul_add (B ^ 3)]
          congr 1
          · congr 1 <;> ac_rfl
          · ac_rfl
        omega
      refine ⟨q0i, u0i, ?_, rfl⟩
      dsimp only [M1]; rw [ite_true_of_w10 rfl, hM0_c0, hcomb0]
      change (((1 + B) ^ x : Nat) : Int) - ((binomTaylorSum x B 3 : Nat) : Int) =
        ((B ^ 3 : Nat) : Int) * (q0i : Int)
      rw [← Int.natCast_sub hle3, hsub3, Int.natCast_mul]
    have hB3_nz : Int.ofNat (B ^ 3) ≠ 0 := hpos_nz (B ^ 3) (nat_pow_pos_of_pos B (by dsimp [B]; omega) 3)
    let A1 : Fin 6 -> Fin 6 -> Int := fun i j =>
      if j = c0 then M1 i c0 / Int.ofNat (B ^ 3) else M1 i j
    have hsc1 : M1 = (fun i j => if j = c0 then Int.ofNat (B ^ 3) * A1 i c0 else A1 i j) := by
      funext i j
      by_cases hj : j = c0
      · subst hj; rw [ite_true_of_w10 rfl]; dsimp only [A1]; rw [ite_true_of_w10 rfl]
        rcases hq0_t3 i with ⟨q0i, _, hq, _⟩
        rw [hq, Int.mul_comm (Int.ofNat (B ^ 3)), Int.mul_ediv_cancel _ hB3_nz, Int.mul_comm]
      · rw [ite_false_of_w10 hj]; dsimp only [A1]; rw [ite_false_of_w10 hj]
    -- Column `c1` reduction on `A1` by `P * idx0(1) + 2*P*B * idx0(2) + 3*P*B^2 * c0` (`div by P * B^3`!):
    let idx1_6 : Nat -> Fin 6 := fun s =>
      match s with | 0 => idx0 1 | 1 => idx0 2 | _ => c0
    let coef1_6 : Nat -> Int := fun s =>
      match s with
      | 0 => Int.ofNat P
      | 1 => Int.ofNat (2 * P * B)
      | _ => Int.ofNat (3 * P * B ^ 2)
    have hne1_6 : ∀ s : Nat, s < 3 -> idx1_6 s ≠ c1 := by
      intro s hs; rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2) with rfl | rfl | rfl <;> decide
    let M2 : Fin 6 -> Fin 6 -> Int := fun i j =>
      if j = c1 then A1 i c1 - colPrefixComb A1 idx1_6 coef1_6 i 3 else A1 i j
    have hr1_t3 : ∀ i : Fin 6,
        ∃ (r1i : Int) (v1i : Int),
          M2 i c1 = Int.ofNat (P * B ^ 3) * r1i ∧
          r1i = (laurentInterpBinom ((laurentRowsTwoBase6 i).1 * W + (laurentRowsTwoBase6 i).2 * K) 4 : Int) +
                (B : Int) * v1i := by
      intro i
      let x := (laurentRowsTwoBase6 i).1 * W + (laurentRowsTwoBase6 i).2 * K
      rcases hq0_t3 i with ⟨q0i, u0i, hM1_c0, hq0_val⟩
      change q0i = laurentInterpBinom x 3 + laurentInterpBinom x 4 * B + B ^ 2 * u0i at hq0_val
      have hA1_c0 : A1 i c0 = Int.ofNat q0i := by
        dsimp only [A1]; rw [ite_true_of_w10 rfl, hM1_c0, Int.mul_comm (Int.ofNat (B ^ 3)),
                             Int.mul_ediv_cancel _ hB3_nz]
      have hA1_1 : A1 i (idx0 1) = Int.ofNat (laurentInterpBinom x 1) := by
        change (laurentZeroGapIntEntry W K _ _ 1 0 : Int) = _
        unfold laurentZeroGapIntEntry; dsimp [x]; simp
      have hA1_2 : A1 i (idx0 2) = Int.ofNat (laurentInterpBinom x 2) := by
        change (laurentZeroGapIntEntry W K _ _ 2 0 : Int) = _
        unfold laurentZeroGapIntEntry; dsimp [x]; simp
      have hA1_c1 : A1 i c1 = Int.ofNat (laurentInterpBinom x 1 * P ^ x) := by
        change (laurentZeroGapIntEntry W K _ _ 1 u : Int) = _
        unfold laurentZeroGapIntEntry; apply congrArg Int.ofNat
        change laurentInterpBinom x 1 * 2 ^ (x * u) = _
        rw [Nat.mul_comm x u, ← pow_pow_eq_mul_w5 2 u x]
      have hcomb1 : colPrefixComb A1 idx1_6 coef1_6 i 3 =
          Int.ofNat (P * laurentInterpBinom x 1 + 2 * P * B * laurentInterpBinom x 2 +
            3 * P * B ^ 2 * q0i) := by
        change ((0 + coef1_6 0 * A1 i (idx0 1)) + coef1_6 1 * A1 i (idx0 2)) + coef1_6 2 * A1 i c0 = _
        rw [hA1_1, hA1_2, hA1_c0]
        change ((0 + Int.ofNat P * Int.ofNat (laurentInterpBinom x 1)) +
          Int.ofNat (2 * P * B) * Int.ofNat (laurentInterpBinom x 2)) +
          Int.ofNat (3 * P * B ^ 2) * Int.ofNat q0i = _
        simp only [Int.zero_add, Int.ofNat_eq_natCast, ← Int.natCast_mul, ← Int.natCast_add]
      cases hx : x with
      | zero =>
        have hq0_z : q0i = 0 := by
          have := hM1_c0; dsimp only [M1] at this; rw [ite_true_of_w10 rfl] at this
          have h0a : M0 i c0 = 1 := by
            dsimp only [M0, c0]; rw [show laurentColsC32_6 u ⟨3, by decide⟩ = (0, u) from rfl]
            unfold laurentZeroGapIntEntry
            change ((laurentInterpBinom x 0 * 2 ^ (x * u) : Nat) : Int) = 1
            rw [hx]; simp [laurentInterpBinom_zero_right]
          have h0b : colPrefixComb M0 idx0 coef0 i 3 = 1 := by
            change ((0 + coef0 0 * M0 i (idx0 0)) + coef0 1 * M0 i (idx0 1)) + coef0 2 * M0 i (idx0 2) = 1
            have z0 : M0 i (idx0 0) = 1 := by
              change (laurentZeroGapIntEntry W K _ _ 0 0 : Int) = 1
              unfold laurentZeroGapIntEntry
              change ((laurentInterpBinom x 0 * 2 ^ (x * 0) : Nat) : Int) = 1
              rw [hx]; simp [laurentInterpBinom_zero_right]
            have z1 : M0 i (idx0 1) = 0 := by
              change (laurentZeroGapIntEntry W K _ _ 1 0 : Int) = 0
              unfold laurentZeroGapIntEntry
              change ((laurentInterpBinom x 1 * 2 ^ (x * 0) : Nat) : Int) = 0
              rw [hx]; simp [laurentInterpBinom]
            have z2 : M0 i (idx0 2) = 0 := by
              change (laurentZeroGapIntEntry W K _ _ 2 0 : Int) = 0
              unfold laurentZeroGapIntEntry
              change ((laurentInterpBinom x 2 * 2 ^ (x * 0) : Nat) : Int) = 0
              rw [hx]; simp [laurentInterpBinom]
            rw [z0, z1, z2]; dsimp only [coef0]; simp
          rw [h0a, h0b] at this
          have hB3_p := nat_pow_pos_of_pos B (by dsimp [B]; omega) 3
          change (0 : Int) = Int.ofNat (B ^ 3 * q0i) at this
          have hz_n : B ^ 3 * q0i = 0 := Int.ofNat.inj this.symm
          rcases Nat.mul_eq_zero.mp hz_n with h0 | h0 <;> omega
        refine ⟨0, 0, ?_, ?_⟩
        · dsimp only [M2]; rw [ite_true_of_w10 rfl, hA1_c1, hcomb1, hx, hq0_z]; simp [laurentInterpBinom]
        · change (0 : Int) = (laurentInterpBinom x 4 : Int) + (B : Int) * 0
          rw [hx]; simp [laurentInterpBinom]
      | succ y =>
        rcases binomTaylorSum_remainder_dvd y B 4 with ⟨_, u1i, hu1i⟩
        have hb4_y : binomTaylorSum y B 4 =
            1 + y * B + laurentInterpBinom y 2 * B ^ 2 + laurentInterpBinom y 3 * B ^ 3 := by
          change (((0 + laurentInterpBinom y 0 * B ^ 0) + laurentInterpBinom y 1 * B ^ 1) +
            laurentInterpBinom y 2 * B ^ 2) + laurentInterpBinom y 3 * B ^ 3 = _
          rw [laurentInterpBinom_zero_right, laurentInterpBinom_one_right]
          simp only [Nat.zero_add, Nat.pow_zero, Nat.pow_one, Nat.mul_one]
        have hab1 : (y + 1) * y = 2 * laurentInterpBinom (y + 1) 2 := by
          have h := (laurentInterpBinom_succ_mul y 1).symm
          rwa [laurentInterpBinom_one_right y] at h
        have hab2 : (y + 1) * laurentInterpBinom y 2 = 3 * laurentInterpBinom (y + 1) 3 :=
          (laurentInterpBinom_succ_mul y 2).symm
        have hab3 : (y + 1) * laurentInterpBinom y 3 = 4 * laurentInterpBinom (y + 1) 4 :=
          (laurentInterpBinom_succ_mul y 3).symm
        have hc1_exp : laurentInterpBinom (y + 1) 1 * P ^ (y + 1) =
            P * (y + 1) + 2 * P * B * laurentInterpBinom (y + 1) 2 +
            3 * P * B ^ 2 * laurentInterpBinom (y + 1) 3 +
            4 * P * B ^ 3 * laurentInterpBinom (y + 1) 4 +
            P * B ^ 4 * ((y + 1) * u1i) := by
          have hp_sp : laurentInterpBinom (y + 1) 1 * P ^ (y + 1) =
              P * ((y + 1) * (1 + B) ^ y) := by
            rw [laurentInterpBinom_one_right (y + 1), Nat.pow_succ P y, h1B]
            ac_rfl
          have hy_p : (1 + B) ^ y =
              1 + y * B + laurentInterpBinom y 2 * B ^ 2 + laurentInterpBinom y 3 * B ^ 3 + B ^ 4 * u1i := by
            omega
          rw [hp_sp, hy_p,
              Nat.mul_add (y + 1), Nat.mul_add (y + 1), Nat.mul_add (y + 1), Nat.mul_add (y + 1),
              Nat.mul_one,
              ← Nat.mul_assoc (y + 1) y B, hab1,
              ← Nat.mul_assoc (y + 1) (laurentInterpBinom y 2) (B ^ 2), hab2,
              ← Nat.mul_assoc (y + 1) (laurentInterpBinom y 3) (B ^ 3), hab3,
              Nat.mul_add P, Nat.mul_add P, Nat.mul_add P, Nat.mul_add P]
          have ht2 : P * (2 * laurentInterpBinom (y + 1) 2 * B) =
              2 * P * B * laurentInterpBinom (y + 1) 2 := by
            generalize laurentInterpBinom (y + 1) 2 = C2
            rw [← Nat.mul_assoc P, ← Nat.mul_assoc P 2 C2, Nat.mul_comm P 2,
                Nat.mul_assoc (2 * P) C2 B, Nat.mul_comm C2 B, ← Nat.mul_assoc (2 * P) B C2]
          have ht3 : P * (3 * laurentInterpBinom (y + 1) 3 * B ^ 2) =
              3 * P * B ^ 2 * laurentInterpBinom (y + 1) 3 := by
            generalize laurentInterpBinom (y + 1) 3 = C3
            rw [← Nat.mul_assoc P, ← Nat.mul_assoc P 3 C3, Nat.mul_comm P 3,
                Nat.mul_assoc (3 * P) C3 (B ^ 2), Nat.mul_comm C3 (B ^ 2), ← Nat.mul_assoc (3 * P)]
          have ht4 : P * (4 * laurentInterpBinom (y + 1) 4 * B ^ 3) =
              4 * P * B ^ 3 * laurentInterpBinom (y + 1) 4 := by
            generalize laurentInterpBinom (y + 1) 4 = C4
            rw [← Nat.mul_assoc P, ← Nat.mul_assoc P 4 C4, Nat.mul_comm P 4,
                Nat.mul_assoc (4 * P) C4 (B ^ 3), Nat.mul_comm C4 (B ^ 3), ← Nat.mul_assoc (4 * P)]
          have ht5 : P * ((y + 1) * (B ^ 4 * u1i)) = P * B ^ 4 * ((y + 1) * u1i) := by
            rw [← Nat.mul_assoc (y + 1) (B ^ 4) u1i, Nat.mul_comm (y + 1) (B ^ 4),
                Nat.mul_assoc (B ^ 4), ← Nat.mul_assoc P]
          rw [ht2, ht3, ht4, ht5]
        have hq0_y : q0i = laurentInterpBinom (y + 1) 3 + laurentInterpBinom (y + 1) 4 * B + B ^ 2 * u0i := by
          rwa [hx] at hq0_val
        have hsub1_exp : 3 * P * B ^ 2 * q0i =
            3 * P * B ^ 2 * laurentInterpBinom (y + 1) 3 +
            3 * P * B ^ 3 * laurentInterpBinom (y + 1) 4 +
            P * B ^ 4 * (3 * u0i) := by
          rw [hq0_y, Nat.mul_add, Nat.mul_add]
          have hm1 : 3 * P * B ^ 2 * (laurentInterpBinom (y + 1) 4 * B) =
              3 * P * B ^ 3 * laurentInterpBinom (y + 1) 4 := by
            generalize laurentInterpBinom (y + 1) 4 = C4
            have hb23 : B ^ 2 * B = B ^ 3 := rfl
            rw [← Nat.mul_assoc (3 * P * B ^ 2) C4 B, Nat.mul_assoc (3 * P) (B ^ 2) C4,
                Nat.mul_comm (B ^ 2) C4, ← Nat.mul_assoc (3 * P) C4 (B ^ 2),
                Nat.mul_assoc (3 * P * C4) (B ^ 2) B, hb23,
                Nat.mul_assoc (3 * P) C4 (B ^ 3), Nat.mul_comm C4 (B ^ 3), ← Nat.mul_assoc (3 * P)]
          have hm2 : 3 * P * B ^ 2 * (B ^ 2 * u0i) = P * B ^ 4 * (3 * u0i) := by
            have hb24 : B ^ 2 * B ^ 2 = B ^ 4 := by
              rw [← Nat.pow_add B 2 2]
            rw [← Nat.mul_assoc (3 * P * B ^ 2) (B ^ 2) u0i,
                Nat.mul_assoc (3 * P) (B ^ 2) (B ^ 2), hb24,
                Nat.mul_assoc 3 P (B ^ 4), Nat.mul_comm 3 (P * B ^ 4), Nat.mul_assoc (P * B ^ 4)]
          rw [hm1, hm2]
        let v1i : Int := ((y + 1) * u1i : Int) - (3 * u0i : Int)
        let r1i : Int := (laurentInterpBinom (y + 1) 4 : Int) + (B : Int) * v1i
        refine ⟨r1i, v1i, ?_, ?_⟩
        · dsimp only [M2]; rw [ite_true_of_w10 rfl, hA1_c1, hcomb1, hx, hc1_exp, hsub1_exp,
                               laurentInterpBinom_one_right (y + 1)]
          have hpB4 : ((P * B ^ 4 : Nat) : Int) = ((P * B ^ 3 : Nat) : Int) * (B : Int) := by
            have hp4 : P * B ^ 4 = (P * B ^ 3) * B := by
              rw [show (4 : Nat) = 3 + 1 from rfl, Nat.pow_add, Nat.pow_one, Nat.mul_assoc]
            rw [← Int.natCast_mul, hp4]
          have h43 : ((4 * P * B ^ 3 * laurentInterpBinom (y + 1) 4 : Nat) : Int) =
              ((3 * P * B ^ 3 * laurentInterpBinom (y + 1) 4 : Nat) : Int) +
              ((P * B ^ 3 : Nat) : Int) * (laurentInterpBinom (y + 1) 4 : Int) := by
            have hn : 4 * P * B ^ 3 * laurentInterpBinom (y + 1) 4 =
                3 * P * B ^ 3 * laurentInterpBinom (y + 1) 4 +
                (P * B ^ 3) * laurentInterpBinom (y + 1) 4 := by
              rw [Nat.mul_assoc 4 P (B ^ 3), Nat.mul_assoc 3 P (B ^ 3)]
              generalize P * B ^ 3 = U, laurentInterpBinom (y + 1) 4 = C4
              rw [Nat.mul_assoc 4 U C4, Nat.mul_assoc 3 U C4]
              generalize U * C4 = UC
              omega
            rw [← Int.natCast_mul, ← Int.natCast_add, hn]
          have hm_yu1 : ((P * B ^ 4 * ((y + 1) * u1i) : Nat) : Int) =
              ((P * B ^ 4 : Nat) : Int) * (((y + 1) * u1i : Nat) : Int) :=
            Int.natCast_mul _ _
          have hm_tu0 : ((P * B ^ 4 * (3 * u0i) : Nat) : Int) =
              ((P * B ^ 4 : Nat) : Int) * ((3 * u0i : Nat) : Int) :=
            Int.natCast_mul _ _
          dsimp only [r1i, v1i]
          simp only [Int.ofNat_eq_natCast, Int.natCast_add]
          rw [h43, hm_yu1, hm_tu0,
              show ((y : Int) + 1) * (u1i : Int) = (((y + 1) * u1i : Nat) : Int) by
                simp [Int.natCast_mul, Int.natCast_add],
              show (3 : Int) * (u0i : Int) = ((3 * u0i : Nat) : Int) by
                simp [Int.natCast_mul],
              Int.mul_add ((P * B ^ 3 : Nat) : Int),
              ← Int.mul_assoc ((P * B ^ 3 : Nat) : Int) (B : Int),
              ← hpB4, Int.mul_sub ((P * B ^ 4 : Nat) : Int)]
          generalize ((P * B ^ 3 : Nat) : Int) * (laurentInterpBinom (y + 1) 4 : Int) = A_t,
            ((P * B ^ 4 : Nat) : Int) * (((y + 1) * u1i : Nat) : Int) = B_t,
            ((P * B ^ 4 : Nat) : Int) * ((3 * u0i : Nat) : Int) = C_t
          omega
        · change r1i = (laurentInterpBinom x 4 : Int) + (B : Int) * v1i
          rw [hx]
    have hPB3_nz : Int.ofNat (P * B ^ 3) ≠ 0 :=
      hpos_nz (P * B ^ 3) (by
        have hb3 := nat_pow_pos_of_pos B (by dsimp [B]; omega) 3
        have hm := Nat.mul_le_mul hP_ge2 hb3
        omega)
    let A2 : Fin 6 -> Fin 6 -> Int := fun i j =>
      if j = c1 then M2 i c1 / Int.ofNat (P * B ^ 3) else M2 i j
    have hsc2 : M2 = (fun i j => if j = c1 then Int.ofNat (P * B ^ 3) * A2 i c1 else A2 i j) := by
      funext i j
      by_cases hj : j = c1
      · subst hj; rw [ite_true_of_w10 rfl]; dsimp only [A2]; rw [ite_true_of_w10 rfl]
        rcases hr1_t3 i with ⟨r1i, _, hr1, _⟩
        rw [hr1, Int.mul_comm (Int.ofNat (P * B ^ 3)), Int.mul_ediv_cancel _ hPB3_nz, Int.mul_comm]
      · rw [ite_false_of_w10 hj]; dsimp only [A2]; rw [ite_false_of_w10 hj]
    -- Column `c2` reduction on `A2` by `P^2 * idx0(2) + 3*P^2*B * c0 + 3*P^2*B^2 * c1` (`div by P^2 * B^3`!):
    let idx2_6 : Nat -> Fin 6 := fun s =>
      match s with | 0 => idx0 2 | 1 => c0 | _ => c1
    let coef2_6 : Nat -> Int := fun s =>
      match s with
      | 0 => Int.ofNat (P ^ 2)
      | 1 => Int.ofNat (3 * P ^ 2 * B)
      | _ => Int.ofNat (3 * P ^ 2 * B ^ 2)
    have hne2_6 : ∀ s : Nat, s < 3 -> idx2_6 s ≠ c2 := by
      intro s hs; rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2) with rfl | rfl | rfl <;> decide
    let M3 : Fin 6 -> Fin 6 -> Int := fun i j =>
      if j = c2 then A2 i c2 - colPrefixComb A2 idx2_6 coef2_6 i 3 else A2 i j
    have hdvd_c2 : ∀ i : Fin 6, Int.ofNat (P ^ 2 * B ^ 3) ∣ M3 i c2 := by
      intro i
      dsimp only [M3]; rw [ite_true_of_w10 rfl]
      let x := (laurentRowsTwoBase6 i).1 * W + (laurentRowsTwoBase6 i).2 * K
      rcases hq0_t3 i with ⟨q0i, u0i, hM1_c0, hq0_val⟩
      rcases hr1_t3 i with ⟨r1i, v1i, hM2_c1, hr1_val⟩
      change q0i = laurentInterpBinom x 3 + laurentInterpBinom x 4 * B + B ^ 2 * u0i at hq0_val
      change r1i = (laurentInterpBinom x 4 : Int) + (B : Int) * v1i at hr1_val
      have hA2_2 : A2 i (idx0 2) = Int.ofNat (laurentInterpBinom x 2) := by
        change (laurentZeroGapIntEntry W K _ _ 2 0 : Int) = _
        unfold laurentZeroGapIntEntry; dsimp [x]; simp
      have hA2_c0 : A2 i c0 = Int.ofNat q0i := by
        have hc0_ne1 : c0 ≠ c1 := by decide
        dsimp only [A2, M2]; rw [ite_false_of_w10 hc0_ne1, ite_false_of_w10 hc0_ne1]
        dsimp only [A1]; rw [ite_true_of_w10 rfl, hM1_c0, Int.mul_comm (Int.ofNat (B ^ 3)),
                             Int.mul_ediv_cancel _ hB3_nz]
      have hA2_c1 : A2 i c1 = r1i := by
        dsimp only [A2]; rw [ite_true_of_w10 rfl, hM2_c1, Int.mul_comm (Int.ofNat (P * B ^ 3)),
                             Int.mul_ediv_cancel _ hPB3_nz]
      have hA2_c2 : A2 i c2 = Int.ofNat (laurentInterpBinom x 2 * P ^ x) := by
        change (laurentZeroGapIntEntry W K _ _ 2 u : Int) = _
        unfold laurentZeroGapIntEntry; apply congrArg Int.ofNat
        change laurentInterpBinom x 2 * 2 ^ (x * u) = _
        rw [Nat.mul_comm x u, ← pow_pow_eq_mul_w5 2 u x]
      have hcomb2 : colPrefixComb A2 idx2_6 coef2_6 i 3 =
          Int.ofNat (P ^ 2 * laurentInterpBinom x 2 + 3 * P ^ 2 * B * q0i) +
            Int.ofNat (3 * P ^ 2 * B ^ 2) * r1i := by
        change ((0 + coef2_6 0 * A2 i (idx0 2)) + coef2_6 1 * A2 i c0) + coef2_6 2 * A2 i c1 = _
        rw [hA2_2, hA2_c0, hA2_c1]
        change ((0 + Int.ofNat (P ^ 2) * Int.ofNat (laurentInterpBinom x 2)) +
          Int.ofNat (3 * P ^ 2 * B) * Int.ofNat q0i) +
          Int.ofNat (3 * P ^ 2 * B ^ 2) * r1i = _
        simp only [Int.zero_add, Int.ofNat_eq_natCast, ← Int.natCast_mul, ← Int.natCast_add]
      rw [hA2_c2, hcomb2]
      -- Handle `x = 0`, `x = 1`, and `x = z + 2`:
      cases hx : x with
      | zero =>
        -- At `x = 0`, `C(0, 2) = C(0, 3) = C(0, 4) = 0`, `q0i = B^2 * u0i`, `r1i = B * v1i`:
        have hq0_0 : q0i = B ^ 2 * u0i := by rw [hx] at hq0_val; simpa [laurentInterpBinom] using hq0_val
        have hr1_0 : r1i = (B : Int) * v1i := by rw [hx] at hr1_val; simpa [laurentInterpBinom] using hr1_val
        rw [laurentInterpBinom, Nat.zero_mul, Nat.mul_zero, Nat.zero_add, hq0_0, hr1_0]
        refine ⟨-(3 * (u0i : Int) + 3 * v1i), ?_⟩
        have hm1 : 3 * P ^ 2 * B * (B ^ 2 * u0i) = (P ^ 2 * B ^ 3) * (3 * u0i) := by
          have hb13 : B * B ^ 2 = B ^ 3 := Nat.mul_comm B (B ^ 2)
          rw [← Nat.mul_assoc (3 * P ^ 2 * B) (B ^ 2) u0i,
              Nat.mul_assoc (3 * P ^ 2) B (B ^ 2), hb13,
              Nat.mul_assoc 3 (P ^ 2) (B ^ 3), Nat.mul_comm 3 (P ^ 2 * B ^ 3),
              Nat.mul_assoc (P ^ 2 * B ^ 3)]
        have hm2 : 3 * P ^ 2 * B ^ 2 * B = (P ^ 2 * B ^ 3) * 3 := by
          have hb23 : B ^ 2 * B = B ^ 3 := rfl
          rw [Nat.mul_assoc (3 * P ^ 2) (B ^ 2) B, hb23, Nat.mul_assoc 3 (P ^ 2) (B ^ 3),
              Nat.mul_comm 3 (P ^ 2 * B ^ 3)]
        simp only [Int.ofNat_eq_natCast]
        rw [hm1, ← Int.mul_assoc ((3 * P ^ 2 * B ^ 2 : Nat) : Int) (B : Int) v1i,
            ← Int.natCast_mul (3 * P ^ 2 * B ^ 2) B, hm2,
            Int.natCast_mul (P ^ 2 * B ^ 3) (3 * u0i),
            Int.natCast_mul (P ^ 2 * B ^ 3) 3,
            Int.mul_assoc ((P ^ 2 * B ^ 3 : Nat) : Int) ((3 : Nat) : Int) v1i,
            show ((3 * u0i : Nat) : Int) = 3 * (u0i : Int) by simp [Int.natCast_mul],
            show ((3 : Nat) : Int) = 3 from rfl,
            Int.mul_neg, Int.mul_add]
        generalize ((P ^ 2 * B ^ 3 : Nat) : Int) * (3 * (u0i : Int)) = A_t,
          ((P ^ 2 * B ^ 3 : Nat) : Int) * (3 * v1i) = B_t
        omega
      | succ x1 =>
        cases hx1 : x1 with
        | zero =>
          -- At `x = 1`, `C(1, 2) = C(1, 3) = C(1, 4) = 0`, `q0i = B^2 * u0i`, `r1i = B * v1i`:
          have hq0_1 : q0i = B ^ 2 * u0i := by rw [hx, hx1] at hq0_val; simpa [laurentInterpBinom] using hq0_val
          have hr1_1 : r1i = (B : Int) * v1i := by rw [hx, hx1] at hr1_val; simpa [laurentInterpBinom] using hr1_val
          have hc12 : laurentInterpBinom 1 2 = 0 := rfl
          change Int.ofNat (P ^ 2 * B ^ 3) ∣
            Int.ofNat (laurentInterpBinom 1 2 * P ^ 1) -
              (Int.ofNat (P ^ 2 * laurentInterpBinom 1 2 + 3 * P ^ 2 * B * q0i) +
                Int.ofNat (3 * P ^ 2 * B ^ 2) * r1i)
          rw [hc12, Nat.zero_mul, Nat.mul_zero, Nat.zero_add, hq0_1, hr1_1]
          refine ⟨-(3 * (u0i : Int) + 3 * v1i), ?_⟩
          have hm1 : 3 * P ^ 2 * B * (B ^ 2 * u0i) = (P ^ 2 * B ^ 3) * (3 * u0i) := by
            have hb13 : B * B ^ 2 = B ^ 3 := Nat.mul_comm B (B ^ 2)
            rw [← Nat.mul_assoc (3 * P ^ 2 * B) (B ^ 2) u0i,
                Nat.mul_assoc (3 * P ^ 2) B (B ^ 2), hb13,
                Nat.mul_assoc 3 (P ^ 2) (B ^ 3), Nat.mul_comm 3 (P ^ 2 * B ^ 3),
                Nat.mul_assoc (P ^ 2 * B ^ 3)]
          have hm2 : 3 * P ^ 2 * B ^ 2 * B = (P ^ 2 * B ^ 3) * 3 := by
            have hb23 : B ^ 2 * B = B ^ 3 := rfl
            rw [Nat.mul_assoc (3 * P ^ 2) (B ^ 2) B, hb23, Nat.mul_assoc 3 (P ^ 2) (B ^ 3),
                Nat.mul_comm 3 (P ^ 2 * B ^ 3)]
          simp only [Int.ofNat_eq_natCast]
          rw [hm1, ← Int.mul_assoc ((3 * P ^ 2 * B ^ 2 : Nat) : Int) (B : Int) v1i,
              ← Int.natCast_mul (3 * P ^ 2 * B ^ 2) B, hm2,
              Int.natCast_mul (P ^ 2 * B ^ 3) (3 * u0i),
              Int.natCast_mul (P ^ 2 * B ^ 3) 3,
              Int.mul_assoc ((P ^ 2 * B ^ 3 : Nat) : Int) ((3 : Nat) : Int) v1i,
              show ((3 * u0i : Nat) : Int) = 3 * (u0i : Int) by simp [Int.natCast_mul],
              show ((3 : Nat) : Int) = 3 from rfl,
              Int.mul_neg, Int.mul_add]
          generalize ((P ^ 2 * B ^ 3 : Nat) : Int) * (3 * (u0i : Int)) = A_t,
            ((P ^ 2 * B ^ 3 : Nat) : Int) * (3 * v1i) = B_t
          omega
        | succ z =>
          -- General `x = z + 2`: expand `(1 + B)^z = 1 + z*B + C(z, 2)*B^2 + B^3 * u2i`!
          rcases binomTaylorSum_remainder_dvd z B 3 with ⟨_, u2i, hu2i⟩
          have hb3_z : binomTaylorSum z B 3 = 1 + z * B + laurentInterpBinom z 2 * B ^ 2 := by
            change ((0 + laurentInterpBinom z 0 * B ^ 0) + laurentInterpBinom z 1 * B ^ 1) +
              laurentInterpBinom z 2 * B ^ 2 = _
            rw [laurentInterpBinom_zero_right, laurentInterpBinom_one_right]
            simp only [Nat.zero_add, Nat.pow_zero, Nat.pow_one, Nat.mul_one]
          -- Binomial product identities:
          -- `C(z + 2, 2) * z = 3 * C(z + 2, 3)` and `C(z + 2, 2) * C(z, 2) = 6 * C(z + 2, 4)`:
          have hcz1 : laurentInterpBinom (z + 2) 2 * z = 3 * laurentInterpBinom (z + 2) 3 := by
            have h0 := laurentInterpBinom_succ_mul (z + 1) 1
            rw [laurentInterpBinom_one_right (z + 1)] at h0
            change 2 * laurentInterpBinom (z + 2) 2 = (z + 2) * (z + 1) at h0
            have h1 := laurentInterpBinom_succ_mul (z + 1) 2
            change 3 * laurentInterpBinom (z + 2) 3 = (z + 2) * laurentInterpBinom (z + 1) 2 at h1
            have h2 := laurentInterpBinom_succ_mul z 1
            rw [laurentInterpBinom_one_right z] at h2
            change 2 * laurentInterpBinom (z + 1) 2 = (z + 1) * z at h2
            have hmul2 : 2 * (laurentInterpBinom (z + 2) 2 * z) = 2 * (3 * laurentInterpBinom (z + 2) 3) := by
              calc
                2 * (laurentInterpBinom (z + 2) 2 * z)
                    = (2 * laurentInterpBinom (z + 2) 2) * z := (Nat.mul_assoc 2 _ z).symm
                _ = (z + 2) * ((z + 1) * z) := by rw [h0, Nat.mul_assoc (z + 2)]
                _ = (z + 2) * (2 * laurentInterpBinom (z + 1) 2) := by rw [← h2]
                _ = 2 * ((z + 2) * laurentInterpBinom (z + 1) 2) := by
                      rw [← Nat.mul_assoc (z + 2) 2, Nat.mul_comm (z + 2) 2, Nat.mul_assoc]
                _ = 2 * (3 * laurentInterpBinom (z + 2) 3) := by rw [← h1]
            omega
          have hcz2 : laurentInterpBinom (z + 2) 2 * laurentInterpBinom z 2 =
              6 * laurentInterpBinom (z + 2) 4 := by
            have h0 := laurentInterpBinom_succ_mul (z + 1) 1
            rw [laurentInterpBinom_one_right (z + 1)] at h0
            change 2 * laurentInterpBinom (z + 2) 2 = (z + 2) * (z + 1) at h0
            have h1 := laurentInterpBinom_succ_mul (z + 1) 3
            change 4 * laurentInterpBinom (z + 2) 4 = (z + 2) * laurentInterpBinom (z + 1) 3 at h1
            have h2 := laurentInterpBinom_succ_mul z 2
            change 3 * laurentInterpBinom (z + 1) 3 = (z + 1) * laurentInterpBinom z 2 at h2
            have hmul2 : 2 * (laurentInterpBinom (z + 2) 2 * laurentInterpBinom z 2) =
                2 * (6 * laurentInterpBinom (z + 2) 4) := by
              calc
                2 * (laurentInterpBinom (z + 2) 2 * laurentInterpBinom z 2)
                    = (2 * laurentInterpBinom (z + 2) 2) * laurentInterpBinom z 2 :=
                      (Nat.mul_assoc 2 _ _).symm
                _ = (z + 2) * ((z + 1) * laurentInterpBinom z 2) := by rw [h0, Nat.mul_assoc]
                _ = (z + 2) * (3 * laurentInterpBinom (z + 1) 3) := by rw [← h2]
                _ = 3 * ((z + 2) * laurentInterpBinom (z + 1) 3) := by
                      rw [← Nat.mul_assoc (z + 2) 3, Nat.mul_comm (z + 2) 3, Nat.mul_assoc]
                _ = 3 * (4 * laurentInterpBinom (z + 2) 4) := by rw [← h1]
                _ = 2 * (6 * laurentInterpBinom (z + 2) 4) := by omega
            omega
          have hc2_exp : laurentInterpBinom (z + 2) 2 * P ^ (z + 2) =
              P ^ 2 * laurentInterpBinom (z + 2) 2 +
              3 * P ^ 2 * B * laurentInterpBinom (z + 2) 3 +
              6 * P ^ 2 * B ^ 2 * laurentInterpBinom (z + 2) 4 +
              (P ^ 2 * B ^ 3) * (laurentInterpBinom (z + 2) 2 * u2i) := by
            have hp_sp : laurentInterpBinom (z + 2) 2 * P ^ (z + 2) =
                P ^ 2 * (laurentInterpBinom (z + 2) 2 * (1 + B) ^ z) := by
              rw [Nat.pow_add P z 2, h1B]
              ac_rfl
            have hz_p : (1 + B) ^ z = 1 + z * B + laurentInterpBinom z 2 * B ^ 2 + B ^ 3 * u2i := by omega
            rw [hp_sp, hz_p,
                Nat.mul_add (laurentInterpBinom (z + 2) 2),
                Nat.mul_add (laurentInterpBinom (z + 2) 2),
                Nat.mul_add (laurentInterpBinom (z + 2) 2),
                Nat.mul_one,
                ← Nat.mul_assoc (laurentInterpBinom (z + 2) 2) z B, hcz1,
                ← Nat.mul_assoc (laurentInterpBinom (z + 2) 2) (laurentInterpBinom z 2) (B ^ 2), hcz2,
                Nat.mul_add (P ^ 2), Nat.mul_add (P ^ 2), Nat.mul_add (P ^ 2)]
            have ht2 : P ^ 2 * (3 * laurentInterpBinom (z + 2) 3 * B) =
                3 * P ^ 2 * B * laurentInterpBinom (z + 2) 3 := by
              generalize laurentInterpBinom (z + 2) 3 = C3
              rw [← Nat.mul_assoc (P ^ 2), ← Nat.mul_assoc (P ^ 2) 3 C3, Nat.mul_comm (P ^ 2) 3,
                  Nat.mul_assoc (3 * P ^ 2) C3 B, Nat.mul_comm C3 B, ← Nat.mul_assoc (3 * P ^ 2)]
            have ht3 : P ^ 2 * (6 * laurentInterpBinom (z + 2) 4 * B ^ 2) =
                6 * P ^ 2 * B ^ 2 * laurentInterpBinom (z + 2) 4 := by
              generalize laurentInterpBinom (z + 2) 4 = C4
              rw [← Nat.mul_assoc (P ^ 2), ← Nat.mul_assoc (P ^ 2) 6 C4, Nat.mul_comm (P ^ 2) 6,
                  Nat.mul_assoc (6 * P ^ 2) C4 (B ^ 2), Nat.mul_comm C4 (B ^ 2), ← Nat.mul_assoc (6 * P ^ 2)]
            have ht4 : P ^ 2 * (laurentInterpBinom (z + 2) 2 * (B ^ 3 * u2i)) =
                (P ^ 2 * B ^ 3) * (laurentInterpBinom (z + 2) 2 * u2i) := by
              generalize laurentInterpBinom (z + 2) 2 = C2
              rw [← Nat.mul_assoc C2 (B ^ 3) u2i, Nat.mul_comm C2 (B ^ 3),
                  Nat.mul_assoc (B ^ 3), ← Nat.mul_assoc (P ^ 2)]
            rw [ht2, ht3, ht4]
          have hxz : x = z + 2 := by rw [hx, hx1]
          change q0i = laurentInterpBinom x 3 + laurentInterpBinom x 4 * B + B ^ 2 * u0i at hq0_val
          change r1i = (laurentInterpBinom x 4 : Int) + (B : Int) * v1i at hr1_val
          rw [hxz] at hq0_val hr1_val
          change Int.ofNat (P ^ 2 * B ^ 3) ∣
            Int.ofNat (laurentInterpBinom (z + 2) 2 * P ^ (z + 2)) -
              (Int.ofNat (P ^ 2 * laurentInterpBinom (z + 2) 2 + 3 * P ^ 2 * B * q0i) +
                Int.ofNat (3 * P ^ 2 * B ^ 2) * r1i)
          have hsub_q0 : 3 * P ^ 2 * B * q0i =
              3 * P ^ 2 * B * laurentInterpBinom (z + 2) 3 +
              3 * P ^ 2 * B ^ 2 * laurentInterpBinom (z + 2) 4 +
              (P ^ 2 * B ^ 3) * (3 * u0i) := by
            rw [hq0_val, Nat.mul_add, Nat.mul_add]
            have hm1 : 3 * P ^ 2 * B * (laurentInterpBinom (z + 2) 4 * B) =
                3 * P ^ 2 * B ^ 2 * laurentInterpBinom (z + 2) 4 := by
              generalize laurentInterpBinom (z + 2) 4 = C4
              have hb12 : B * B = B ^ 2 := (Nat.pow_two B).symm
              rw [← Nat.mul_assoc (3 * P ^ 2 * B) C4 B, Nat.mul_assoc (3 * P ^ 2) B C4,
                  Nat.mul_comm B C4, ← Nat.mul_assoc (3 * P ^ 2) C4 B,
                  Nat.mul_assoc (3 * P ^ 2 * C4) B B, hb12,
                  Nat.mul_assoc (3 * P ^ 2) C4 (B ^ 2), Nat.mul_comm C4 (B ^ 2), ← Nat.mul_assoc (3 * P ^ 2)]
            have hm2 : 3 * P ^ 2 * B * (B ^ 2 * u0i) = (P ^ 2 * B ^ 3) * (3 * u0i) := by
              have hb13 : B * B ^ 2 = B ^ 3 := Nat.mul_comm B (B ^ 2)
              rw [← Nat.mul_assoc (3 * P ^ 2 * B) (B ^ 2) u0i,
                  Nat.mul_assoc (3 * P ^ 2) B (B ^ 2), hb13,
                  Nat.mul_assoc 3 (P ^ 2) (B ^ 3), Nat.mul_comm 3 (P ^ 2 * B ^ 3),
                  Nat.mul_assoc (P ^ 2 * B ^ 3)]
            rw [hm1, hm2]
          refine ⟨(laurentInterpBinom (z + 2) 2 * u2i : Int) - 3 * (u0i : Int) - 3 * v1i, ?_⟩
          rw [hc2_exp, hsub_q0, hr1_val]
          have hm3 : ((3 * P ^ 2 * B ^ 2 : Nat) : Int) * (B : Int) =
              ((P ^ 2 * B ^ 3 : Nat) : Int) * 3 := by
            have hp : 3 * P ^ 2 * B ^ 2 * B = (P ^ 2 * B ^ 3) * 3 := by
              have hb23 : B ^ 2 * B = B ^ 3 := rfl
              rw [Nat.mul_assoc (3 * P ^ 2) (B ^ 2) B, hb23, Nat.mul_assoc 3 (P ^ 2) (B ^ 3),
                  Nat.mul_comm 3 (P ^ 2 * B ^ 3)]
            rw [← Int.natCast_mul, hp, Int.natCast_mul]; rfl
          have hm6_c4 : ((6 * P ^ 2 * B ^ 2 * laurentInterpBinom (z + 2) 4 : Nat) : Int) =
              ((3 * P ^ 2 * B ^ 2 * laurentInterpBinom (z + 2) 4 : Nat) : Int) +
              ((3 * P ^ 2 * B ^ 2 : Nat) : Int) * (laurentInterpBinom (z + 2) 4 : Int) := by
            have hp : 6 * P ^ 2 * B ^ 2 * laurentInterpBinom (z + 2) 4 =
                3 * P ^ 2 * B ^ 2 * laurentInterpBinom (z + 2) 4 +
                (3 * P ^ 2 * B ^ 2) * laurentInterpBinom (z + 2) 4 := by
              rw [Nat.mul_assoc 6 (P ^ 2) (B ^ 2), Nat.mul_assoc 3 (P ^ 2) (B ^ 2)]
              generalize P ^ 2 * B ^ 2 = W2, laurentInterpBinom (z + 2) 4 = C4
              rw [Nat.mul_assoc 6 W2 C4, Nat.mul_assoc 3 W2 C4]
              generalize W2 * C4 = WC
              omega
            rw [← Int.natCast_mul, ← Int.natCast_add, hp]
          have hm_u2 : ((P ^ 2 * B ^ 3 * (laurentInterpBinom (z + 2) 2 * u2i) : Nat) : Int) =
              ((P ^ 2 * B ^ 3 : Nat) : Int) * ((laurentInterpBinom (z + 2) 2 : Int) * (u2i : Int)) := by
            rw [Int.natCast_mul (P ^ 2 * B ^ 3) (laurentInterpBinom (z + 2) 2 * u2i),
                Int.natCast_mul (laurentInterpBinom (z + 2) 2) u2i]
          have hm_u0 : ((P ^ 2 * B ^ 3 * (3 * u0i) : Nat) : Int) =
              ((P ^ 2 * B ^ 3 : Nat) : Int) * (3 * (u0i : Int)) := by
            rw [Int.natCast_mul (P ^ 2 * B ^ 3) (3 * u0i),
                Int.natCast_mul 3 u0i]; rfl
          simp only [Int.ofNat_eq_natCast]
          rw [Int.mul_add ((3 * P ^ 2 * B ^ 2 : Nat) : Int),
              ← Int.mul_assoc ((3 * P ^ 2 * B ^ 2 : Nat) : Int) (B : Int) v1i, hm3,
              Int.mul_assoc ((P ^ 2 * B ^ 3 : Nat) : Int) 3 v1i]
          simp only [Int.natCast_add]
          rw [hm6_c4, hm_u2, hm_u0,
              Int.mul_sub ((P ^ 2 * B ^ 3 : Nat) : Int),
              Int.mul_sub ((P ^ 2 * B ^ 3 : Nat) : Int)]
          generalize ((P ^ 2 * B ^ 3 : Nat) : Int) * ((laurentInterpBinom (z + 2) 2 : Int) * (u2i : Int)) = A_t,
            ((P ^ 2 * B ^ 3 : Nat) : Int) * (3 * (u0i : Int)) = B_t,
            ((P ^ 2 * B ^ 3 : Nat) : Int) * (3 * v1i) = C_t,
            ((3 * P ^ 2 * B ^ 2 : Nat) : Int) * (laurentInterpBinom (z + 2) 4 : Int) = D_t
          omega
    -- Combine `B^3 * (P * B^3) * (P^2 * B^3) = 2^(3u) * (2^u - 1)^9`:
    have hd_m3 := intDet_col_dvd (Int.ofNat (P ^ 2 * B ^ 3)) 6 c2 M3 hdvd_c2
    rcases hd_m3 with ⟨q_end, hq_end⟩
    have hdet_chain : intDet 6 M1 =
        Int.ofNat (B ^ 3) * (Int.ofNat (P * B ^ 3) * (Int.ofNat (P ^ 2 * B ^ 3) * q_end)) := by
      rw [hsc1, intDet_col_scale (Int.ofNat (B ^ 3)) 6 c0 A1,
          intDet_sub_col_prefix_invariant 6 c1 A1 3 idx1_6 coef1_6 hne1_6]
      change Int.ofNat (B ^ 3) * intDet 6 M2 = _
      rw [hsc2, intDet_col_scale (Int.ofNat (P * B ^ 3)) 6 c1 A2,
          intDet_sub_col_prefix_invariant 6 c2 A2 3 idx2_6 coef2_6 hne2_6]
      change Int.ofNat (B ^ 3) * (Int.ofNat (P * B ^ 3) * intDet 6 M3) = _
      rw [hq_end]
    refine ⟨q_end, ?_⟩
    rw [hdet_chain]
    have hprod_nat : B ^ 3 * (P * B ^ 3 * (P ^ 2 * B ^ 3)) = 2 ^ (3 * u) * B ^ 9 := by
      have hp3 : P * P ^ 2 = 2 ^ (3 * u) := by
        dsimp [P]
        rw [Nat.mul_comm 3 u, ← pow_pow_eq_mul_w5 2 u 3,
            Nat.pow_succ (2 ^ u) 2, Nat.mul_comm ((2 ^ u) ^ 2) (2 ^ u)]
      calc
        B ^ 3 * (P * B ^ 3 * (P ^ 2 * B ^ 3))
            = (P * P ^ 2) * (B ^ 3 * B ^ 3 * B ^ 3) := by ac_rfl
        _ = 2 ^ (3 * u) * B ^ 9 := by
              rw [hp3, ← Nat.pow_add B 3 3, ← Nat.pow_add B 6 3]
    simp only [Int.ofNat_eq_natCast]
    rw [← Int.mul_assoc ((P * B ^ 3 : Nat) : Int) ((P ^ 2 * B ^ 3 : Nat) : Int) q_end,
        ← Int.mul_assoc ((B ^ 3 : Nat) : Int) _ q_end,
        ← Int.natCast_mul (P * B ^ 3) (P ^ 2 * B ^ 3),
        ← Int.natCast_mul (B ^ 3),
        hprod_nat, Int.natCast_mul]

-- ----------------------------------------------------------------------------
-- Section 2C: Exact Rank-2 Vandermonde `6 × 6` Two-Base `(T = 3, U = 2)` Closed
--             Form, Universal Odd-`u` Non-Vanishing, & All-`u ≥ 1` Cone Positivity
-- ----------------------------------------------------------------------------

def twoBaseT3U2ScaledExprMat6 (i j : Fin 6) : Expr4 :=
  -- Variables: `v0 = W`, `v1 = K`, `v2 = P = 2^u`, `v3 = Q = 3^u`
  -- Columns `2` and `5` (`t = 2`) scaled by `2` so `2 * binom(n, 2) = n * (n - 1)`:
  let rs := laurentRowsTwoBase6 i
  let r := rs.1
  let s := rs.2
  let n : Expr4 := .add (.mul (.const (r : Int)) .v0) (.mul (.const (s : Int)) .v1)
  let powPQ : Expr4 := .mul (expr4Pow .v2 r) (expr4Pow .v3 s)
  match j.val with
  | 0 => .const 1
  | 1 => n
  | 2 => .mul n (.sub n (.const 1))
  | 3 => powPQ
  | 4 => .mul n powPQ
  | _ => .mul (.mul n (.sub n (.const 1))) powPQ

def t3u2BracketExpr (W K P Q : Expr4) : Expr4 :=
  let p := Expr4.sub P (.const 1)
  let q := Expr4.sub Q (.const 1)
  let t1 := Expr4.mul (.mul P (.mul p (expr4Pow q 4))) (expr4Pow W 4)
  let t2 := Expr4.mul
    (.mul (.const 2) (.mul P (.mul (.add P (.const 1)) (.mul (.add Q (.const 1)) (expr4Pow q 3)))))
    (.mul (expr4Pow W 3) K)
  let midQ := Expr4.add (.add (expr4Pow Q 2) (.mul (.const 10) Q)) (.const 1)
  let t3 := Expr4.mul (.mul P (.mul p (.mul (expr4Pow q 2) midQ)))
    (.mul (expr4Pow W 2) (expr4Pow K 2))
  let t4 := Expr4.mul (.mul (.const 4) (.mul (expr4Pow p 3) (expr4Pow Q 2))) (expr4Pow K 4)
  .sub (.add (.sub t1 t2) t3) t4

def twoBaseT3U2ScaledClosedExpr : Expr4 :=
  .mul (expr4Pow .v1 2) (.mul .v3 (t3u2BracketExpr .v0 .v1 .v2 .v3))

set_option maxRecDepth 32768 in
theorem twoBaseT3U2_poly_identity :
    addPoly4 (poly4Det 6 (fun i j => normExpr4 (twoBaseT3U2ScaledExprMat6 i j)))
      (negPoly4 (normExpr4 twoBaseT3U2ScaledClosedExpr)) = [] := by decide

-- Cone parameterization `13 * W = 3 * A + 53 * B`, `13 * K = 5 * A + 84 * B` (`A = 53*K - 84*W ≥ 1`, `B = 5*W - 3*K ≥ 0`):

def checkAllNonnegMono4 : List Mono4 -> Bool
  | [] => true
  | m :: ms => decide (m.2.2.2.2 ≥ 0) && checkAllNonnegMono4 ms

theorem intPowNat_nonneg_mono (a b : Int) (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ k : Nat, 0 ≤ intPowNat a k ∧ intPowNat a k ≤ intPowNat b k := by
  intro k; induction k with
  | zero => simp [intPowNat]
  | succ k ih =>
    rcases ih with ⟨hpk_nn, hpk_le⟩
    simp only [intPowNat]
    exact ⟨Int.mul_nonneg ha hpk_nn,
      Int.le_trans (Int.mul_le_mul_of_nonneg_right hab hpk_nn)
        (Int.mul_le_mul_of_nonneg_left hpk_le (Int.le_trans ha hab))⟩

theorem evalPoly4_mono_of_nonneg (a0 a1 a2 a3 b0 b1 b2 b3 : Int)
    (ha0 : 0 ≤ a0) (hab0 : a0 ≤ b0)
    (ha1 : 0 ≤ a1) (hab1 : a1 ≤ b1)
    (ha2 : 0 ≤ a2) (hab2 : a2 ≤ b2)
    (ha3 : 0 ≤ a3) (hab3 : a3 ≤ b3) :
    ∀ p : List Mono4,
      checkAllNonnegMono4 p = true ->
      evalPoly4 a0 a1 a2 a3 p ≤ evalPoly4 b0 b1 b2 b3 p
  | [], _ => Int.le_refl 0
  | m :: ms, hb => by
    unfold checkAllNonnegMono4 at hb
    rcases bool_and_split hb with ⟨hm_b, hms_b⟩
    have hmc : 0 ≤ m.2.2.2.2 := of_decide_eq_true hm_b
    have ih := evalPoly4_mono_of_nonneg a0 a1 a2 a3 b0 b1 b2 b3
      ha0 hab0 ha1 hab1 ha2 hab2 ha3 hab3 ms hms_b
    simp only [evalPoly4, evalMono4]
    rcases intPowNat_nonneg_mono a0 b0 ha0 hab0 m.1 with ⟨hp0_nn, hp0_le⟩
    rcases intPowNat_nonneg_mono a1 b1 ha1 hab1 m.2.1 with ⟨hp1_nn, hp1_le⟩
    rcases intPowNat_nonneg_mono a2 b2 ha2 hab2 m.2.2.1 with ⟨hp2_nn, hp2_le⟩
    rcases intPowNat_nonneg_mono a3 b3 ha3 hab3 m.2.2.2.1 with ⟨hp3_nn, hp3_le⟩
    have hm23_nn := Int.mul_nonneg hp2_nn hp3_nn
    have hm23_le : intPowNat a2 m.2.2.1 * intPowNat a3 m.2.2.2.1 ≤
        intPowNat b2 m.2.2.1 * intPowNat b3 m.2.2.2.1 :=
      Int.le_trans (Int.mul_le_mul_of_nonneg_right hp2_le hp3_nn)
        (Int.mul_le_mul_of_nonneg_left hp3_le (Int.le_trans hp2_nn hp2_le))
    have hm123_nn := Int.mul_nonneg hp1_nn hm23_nn
    have hm123_le : intPowNat a1 m.2.1 * (intPowNat a2 m.2.2.1 * intPowNat a3 m.2.2.2.1) ≤
        intPowNat b1 m.2.1 * (intPowNat b2 m.2.2.1 * intPowNat b3 m.2.2.2.1) :=
      Int.le_trans (Int.mul_le_mul_of_nonneg_right hp1_le hm23_nn)
        (Int.mul_le_mul_of_nonneg_left hm23_le (Int.le_trans hp1_nn hp1_le))
    have hm0123_le :
        intPowNat a0 m.1 * (intPowNat a1 m.2.1 * (intPowNat a2 m.2.2.1 * intPowNat a3 m.2.2.2.1)) ≤
        intPowNat b0 m.1 * (intPowNat b1 m.2.1 * (intPowNat b2 m.2.2.1 * intPowNat b3 m.2.2.2.1)) :=
      Int.le_trans (Int.mul_le_mul_of_nonneg_right hp0_le hm123_nn)
        (Int.mul_le_mul_of_nonneg_left hm123_le (Int.le_trans hp0_nn hp0_le))
    exact Int.add_le_add (Int.mul_le_mul_of_nonneg_left hm0123_le hmc) ih

def t3u2ConeExprW : Expr4 := .add (.mul (.const 3) .v0) (.mul (.const 53) .v1)
def t3u2ConeExprK : Expr4 := .add (.mul (.const 5) .v0) (.mul (.const 84) .v1)

def t3u2ConeFixedUExpr (P Q : Int) : Expr4 :=
  t3u2BracketExpr t3u2ConeExprW t3u2ConeExprK (.const P) (.const Q)

def t3u2ConeGe5Expr : Expr4 :=
  let P := Expr4.add (.const 32) .v2
  let Q := Expr4.add (.add (.mul (.const 7) P) (.const 19)) .v3
  t3u2BracketExpr t3u2ConeExprW t3u2ConeExprK P Q

theorem t3u2_homog4_identity :
    normExpr4 (.sub
      (.mul (.const 28561) (t3u2BracketExpr .v0 .v1 .v2 .v3))
      (t3u2BracketExpr (.mul (.const 13) .v0) (.mul (.const 13) .v1) .v2 .v3)) = [] := by decide

theorem t3u2_homog3_identity :
    normExpr4 (.sub
      (.mul (.const 81) (t3u2BracketExpr .v0 .v1 .v2 .v3))
      (t3u2BracketExpr (.mul (.const 3) .v0) (.mul (.const 3) .v1) .v2 .v3)) = [] := by decide

set_option maxRecDepth 32768 in
theorem t3u2_cone_pos_certs :
    checkAllNonnegMono4 (normExpr4 (t3u2ConeFixedUExpr 2 3)) = true ∧
    evalExpr4 1 0 0 0 (t3u2ConeFixedUExpr 2 3) > 0 ∧
    checkAllNonnegMono4 (normExpr4 (t3u2ConeFixedUExpr 4 9)) = true ∧
    evalExpr4 1 0 0 0 (t3u2ConeFixedUExpr 4 9) > 0 ∧
    checkAllNonnegMono4 (normExpr4 (t3u2ConeFixedUExpr 8 27)) = true ∧
    evalExpr4 1 0 0 0 (t3u2ConeFixedUExpr 8 27) > 0 ∧
    checkAllNonnegMono4 (normExpr4 (t3u2ConeFixedUExpr 16 81)) = true ∧
    evalExpr4 1 0 0 0 (t3u2ConeFixedUExpr 16 81) > 0 ∧
    checkAllNonnegMono4 (normExpr4 t3u2ConeGe5Expr) = true ∧
    evalExpr4 1 0 0 0 t3u2ConeGe5Expr > 0 := by
  exact ⟨by decide, by decide, by decide, by decide, by decide,
         by decide, by decide, by decide, by decide, by decide⟩

theorem pow3_ge_7_mul_pow2_add19 : ∀ u : Nat, u ≥ 5 -> 3 ^ u ≥ 7 * 2 ^ u + 19
  | 0, hu => by omega
  | 1, hu => by omega
  | 2, hu => by omega
  | 3, hu => by omega
  | 4, hu => by omega
  | 5, _ => by decide
  | u + 6, _ => by
    have ih := pow3_ge_7_mul_pow2_add19 (u + 5) (by omega)
    rw [Nat.pow_succ 3 (u + 5), Nat.pow_succ 2 (u + 5)]
    omega

private theorem pull_front_S3_sq (C1 S U2 s1 : Nat) :
    C1 * (S * U2 * (3 * s1 * U2)) = S * (3 * (C1 * (U2 * (s1 * U2)))) := by
  calc
    C1 * (S * U2 * (3 * s1 * U2))
        = C1 * (S * (U2 * (3 * (s1 * U2)))) := by
          rw [Nat.mul_assoc S U2, Nat.mul_assoc 3 s1 U2]
    _ = C1 * (S * (3 * (U2 * (s1 * U2)))) := by
          rw [← Nat.mul_assoc U2 3 (s1 * U2), Nat.mul_comm U2 3, Nat.mul_assoc 3 U2]
    _ = (C1 * S) * (3 * (U2 * (s1 * U2))) := (Nat.mul_assoc C1 S _).symm
    _ = S * (C1 * (3 * (U2 * (s1 * U2)))) := by rw [Nat.mul_comm C1 S, Nat.mul_assoc S C1]
    _ = S * (3 * (C1 * (U2 * (s1 * U2)))) := by
          rw [← Nat.mul_assoc C1 3, Nat.mul_comm C1 3, Nat.mul_assoc 3 C1]

private theorem pull_front_S3_prod (C S Z K : Nat) :
    C * (S * (3 * Z)) * K = S * (3 * (C * Z * K)) := by
  calc
    C * (S * (3 * Z)) * K
        = ((C * S) * (3 * Z)) * K := by rw [Nat.mul_assoc C S (3 * Z)]
    _ = (S * (C * (3 * Z))) * K := by rw [Nat.mul_comm C S, Nat.mul_assoc S C]
    _ = (S * (3 * (C * Z))) * K := by
          rw [← Nat.mul_assoc C 3 Z, Nat.mul_comm C 3, Nat.mul_assoc 3 C Z]
    _ = S * (3 * (C * Z * K)) := by
          rw [Nat.mul_assoc S (3 * (C * Z)) K, Nat.mul_assoc 3 (C * Z) K]

private theorem pull_front_S_prod (C S U K : Nat) :
    C * (S * U) * K = S * (C * U * K) := by
  calc
    C * (S * U) * K
        = ((C * S) * U) * K := by rw [Nat.mul_assoc C S U]
    _ = (S * (C * U)) * K := by rw [Nat.mul_comm C S, Nat.mul_assoc S C U]
    _ = S * (C * U * K) := Nat.mul_assoc S (C * U) K

/-- 3-Adic Infinite Descent for Odd-`u` Non-Vanishing of `t3u2BracketExpr` across ALL `W, K ≥ 1` (`zero custom axioms`). -/
theorem t3u2_odd_u_bracket_nonzero :
    ∀ (bound W K u : Nat),
      W + K ≤ bound -> W ≥ 1 -> K ≥ 1 -> u % 2 = 1 ->
      evalExpr4 (W : Int) (K : Int) ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int)
        (t3u2BracketExpr .v0 .v1 .v2 .v3) ≠ 0
  | 0, W, _, _, h0, hW1, _, _ => by omega
  | bound + 1, W, K, u, hbd, hW1, hK1, hu_odd => by
    intro hzero
    have hu1 : u ≥ 1 := by omega
    let P := 2 ^ u
    let Q := 3 ^ u
    have hP_m3 : P % 3 = 2 := by
      dsimp [P]
      have hu_eq : u = 2 * (u / 2) + 1 := by omega
      rw [hu_eq, Nat.pow_succ, ← pow4_eq_pow2_even (u / 2)]
      have h4_1 : ∀ k : Nat, 4 ^ k % 3 = 1 := by
        intro k; induction k with
        | zero => rfl
        | succ k' ih => rw [Nat.pow_succ, Nat.mul_mod, ih]
      rw [Nat.mul_mod, h4_1 (u / 2)]
    have hQ_m3 : Q % 3 = 0 := by
      dsimp [Q]; rw [show u = (u - 1) + 1 by omega, Nat.pow_succ]; omega
    have hQ2_0 : (Q ^ 2) % 3 = 0 := by rw [Nat.pow_two, Nat.mul_mod, hQ_m3]
    have hmid_1 : (Q ^ 2 + 10 * Q + 1) % 3 = 1 := by
      rw [Nat.add_mod (Q ^ 2 + 10 * Q) 1 3, Nat.add_mod (Q ^ 2) (10 * Q) 3,
          hQ2_0, Nat.mul_mod 10 Q 3, hQ_m3]
    by_cases hW3 : W % 3 = 0
    · by_cases hK3 : K % 3 = 0
      · -- Both `W, K` divisible by `3`: descend to `(W / 3, K / 3)` via degree-4 homogeneity (`81 * ...`)!
        let W' := W / 3
        let K' := K / 3
        have hW_eq : (W : Int) = 3 * (W' : Int) := by dsimp [W']; omega
        have hK_eq : (K : Int) = 3 * (K' : Int) := by dsimp [K']; omega
        have hhom := expr4_eq_of_norm_sub_nil
          (.mul (.const 81) (t3u2BracketExpr .v0 .v1 .v2 .v3))
          (t3u2BracketExpr (.mul (.const 3) .v0) (.mul (.const 3) .v1) .v2 .v3)
          t3u2_homog3_identity (W' : Int) (K' : Int) (P : Int) (Q : Int)
        change 81 * evalExpr4 (W' : Int) (K' : Int) (P : Int) (Q : Int)
            (t3u2BracketExpr .v0 .v1 .v2 .v3) =
          evalExpr4 (W' : Int) (K' : Int) (P : Int) (Q : Int)
            (t3u2BracketExpr (.mul (.const 3) .v0) (.mul (.const 3) .v1) .v2 .v3) at hhom
        change evalExpr4 (W : Int) (K : Int) (P : Int) (Q : Int)
          (t3u2BracketExpr .v0 .v1 .v2 .v3) = 0 at hzero
        have heq_sub : evalExpr4 (3 * (W' : Int)) (3 * (K' : Int)) (P : Int) (Q : Int)
            (t3u2BracketExpr .v0 .v1 .v2 .v3) = 0 := by
          rwa [← hW_eq, ← hK_eq]
        have hsubst :
            evalExpr4 (W' : Int) (K' : Int) (P : Int) (Q : Int)
              (t3u2BracketExpr (.mul (.const 3) .v0) (.mul (.const 3) .v1) .v2 .v3) =
            evalExpr4 (3 * (W' : Int)) (3 * (K' : Int)) (P : Int) (Q : Int)
              (t3u2BracketExpr .v0 .v1 .v2 .v3) := rfl
        rw [hsubst, heq_sub] at hhom
        have hbr_w' : evalExpr4 (W' : Int) (K' : Int) (P : Int) (Q : Int)
            (t3u2BracketExpr .v0 .v1 .v2 .v3) = 0 := by
          generalize evalExpr4 (W' : Int) (K' : Int) (P : Int) (Q : Int)
            (t3u2BracketExpr .v0 .v1 .v2 .v3) = BV at hhom ⊢
          omega
        exact t3u2_odd_u_bracket_nonzero bound W' K' u
          (by dsimp [W', K']; omega) (by dsimp [W']; omega) (by dsimp [K']; omega) hu_odd
          hbr_w'
      · -- `3 ∣ W` and `3 ∤ K`: decompose `W = 3 ^ a * w0` (`a ≥ 1`, `w0 % 3 ≠ 0`):
        rcases eq_pow3_of_v3Pow_aux W W hW1 (Nat.le_refl W) with ⟨a, ha_v3⟩
        let w0 := core3 W
        have hW_fac : W = 3 ^ a * w0 := by
          have hd := (core3_decomp W hW1).2.2.2.2.symm
          rwa [ha_v3] at hd
        have hw0_nd3 : w0 % 3 ≠ 0 := (core3_decomp W hW1).2.2.1
        have ha_pos : a ≥ 1 := by
          cases a with
          | zero => rw [Nat.pow_zero, Nat.one_mul] at hW_fac; exact False.elim (hw0_nd3 (hW_fac ▸ hW3))
          | succ _ => omega
        -- Unpack the 4 integer terms of `t3u2BracketExpr`:
        let p := P - 1
        let q := Q - 1
        have hp_pos : P ≥ 2 := by dsimp [P]; simpa using pow2_mono_nat hu1
        have hq_pos : Q ≥ 3 := by dsimp [Q]; simpa using nat_pow_mono_exp_pos 3 1 u (by decide) hu1
        have hp_m3 : p % 3 = 1 := by dsimp [p]; omega
        have hpp_m3 : (P + 1) % 3 = 0 := by omega
        have hq_m3 : q % 3 = 2 := by dsimp [q]; omega
        let T1 : Nat := P * p * q ^ 4 * W ^ 4
        let T2 : Nat := 2 * P * (P + 1) * (Q + 1) * q ^ 3 * W ^ 3 * K
        let T3 : Nat := P * p * q ^ 2 * (Q ^ 2 + 10 * Q + 1) * W ^ 2 * K ^ 2
        let T4 : Nat := 4 * p ^ 3 * Q ^ 2 * K ^ 4
        have hbr_nat_eq : T1 + T3 = T2 + T4 := by
          have hintPow_n : ∀ (n k : Nat), intPowNat (n : Int) k = ((n ^ k : Nat) : Int) := by
            intro n k; induction k with
            | zero => rfl
            | succ k' ih => simp [intPowNat, ih, Nat.pow_succ, Nat.mul_comm (n ^ k') n, Int.natCast_mul]
          have hexprPow_n : ∀ (x0 x1 x2 x3 : Int) (e : Expr4) (k : Nat),
              evalExpr4 x0 x1 x2 x3 (expr4Pow e k) = intPowNat (evalExpr4 x0 x1 x2 x3 e) k := by
            intro x0 x1 x2 x3 e k; induction k with
            | zero => rfl
            | succ k' ih => simp [expr4Pow, evalExpr4, intPowNat, ih]
          change evalExpr4 (W : Int) (K : Int) (P : Int) (Q : Int)
            (t3u2BracketExpr .v0 .v1 .v2 .v3) = 0 at hzero
          unfold t3u2BracketExpr at hzero
          simp only [evalExpr4, hexprPow_n] at hzero
          have hp_sub : ((P : Int) - 1) = (p : Int) := by dsimp [p]; omega
          have hq_sub : ((Q : Int) - 1) = (q : Int) := by dsimp [q]; omega
          have hp_add : ((P : Int) + 1) = ((P + 1 : Nat) : Int) := by omega
          have hq_add : ((Q : Int) + 1) = ((Q + 1 : Nat) : Int) := by omega
          rw [hp_sub, hq_sub, hp_add, hq_add] at hzero
          simp only [hintPow_n] at hzero
          have hmid_c : (((Q ^ 2 : Nat) : Int) + 10 * (Q : Int) + 1) =
              ((Q ^ 2 + 10 * Q + 1 : Nat) : Int) := by omega
          rw [hmid_c] at hzero
          have hc1 : (P : Int) * ((p : Int) * ((q ^ 4 : Nat) : Int)) * ((W ^ 4 : Nat) : Int) = (T1 : Int) := by
            simp only [← Int.natCast_mul]; apply congrArg Nat.cast; dsimp only [T1]; ac_rfl
          have hc2 : (2 : Int) * ((P : Int) * (((P + 1 : Nat) : Int) *
              (((Q + 1 : Nat) : Int) * ((q ^ 3 : Nat) : Int)))) * (((W ^ 3 : Nat) : Int) * (K : Int)) =
              (T2 : Int) := by
            rw [show (2 : Int) = ((2 : Nat) : Int) from rfl]
            simp only [← Int.natCast_mul]; apply congrArg Nat.cast; dsimp only [T2]; ac_rfl
          have hc3 : (P : Int) * ((p : Int) * (((q ^ 2 : Nat) : Int) *
              ((Q ^ 2 + 10 * Q + 1 : Nat) : Int))) * (((W ^ 2 : Nat) : Int) * ((K ^ 2 : Nat) : Int)) =
              (T3 : Int) := by
            simp only [← Int.natCast_mul]; apply congrArg Nat.cast; dsimp only [T3]; ac_rfl
          have hc4 : (4 : Int) * (((p ^ 3 : Nat) : Int) * ((Q ^ 2 : Nat) : Int)) *
              ((K ^ 4 : Nat) : Int) = (T4 : Int) := by
            rw [show (4 : Int) = ((4 : Nat) : Int) from rfl]
            simp only [← Int.natCast_mul]; apply congrArg Nat.cast; dsimp only [T4]; ac_rfl
          rw [hc1, hc2, hc3, hc4] at hzero
          omega
        by_cases hau : a < u
        · -- `1 ≤ a < u`: divide `T1 + T3 = T2 + T4` by `3 ^ (2 * a)` and reduce `mod 3`!
          let S := 3 ^ (2 * a)
          have hS_pos : S ≥ 1 := pow3_pos_nat (2 * a)
          have hW2_S : W ^ 2 = S * w0 ^ 2 := by
            dsimp [S]
            rw [hW_fac, Nat.pow_two (3 ^ a * w0), Nat.pow_two w0,
                show 2 * a = a + a by omega, Nat.pow_add 3 a a]
            generalize 3 ^ a = PA
            rw [Nat.mul_assoc PA w0 (PA * w0), ← Nat.mul_assoc w0 PA w0,
                Nat.mul_comm w0 PA, Nat.mul_assoc PA w0 w0, ← Nat.mul_assoc PA PA]
          have hW4_S3 : ∃ m1, T1 = S * (3 * m1) := by
            have h3_2a : 3 ∣ S := ⟨3 ^ (2 * a - 1), by
              dsimp [S]; conv => lhs; rw [show 2 * a = (2 * a - 1) + 1 by omega]
              rw [Nat.pow_succ, Nat.mul_comm]⟩
            rcases h3_2a with ⟨s1, hs1⟩
            have hw4 : W ^ 4 = W ^ 2 * W ^ 2 := by
              rw [show (4 : Nat) = 2 + 2 from rfl, Nat.pow_add]
            refine ⟨P * p * q ^ 4 * (w0 ^ 2 * (s1 * w0 ^ 2)), ?_⟩
            dsimp [T1]
            rw [hw4, hW2_S]
            conv => lhs; rhs; rhs; rw [hs1]
            exact pull_front_S3_sq (P * p * q ^ 4) S (w0 ^ 2) s1
          have hT2_S3 : ∃ m2, T2 = S * (3 * m2) := by
            have ha_sp : 3 ^ a = 3 * 3 ^ (a - 1) := by
              conv => lhs; rw [show a = (a - 1) + 1 by omega]; rw [Nat.pow_succ, Nat.mul_comm]
            have hw3 : W ^ 3 = S * (3 * (3 ^ (a - 1) * w0 ^ 2 * w0)) := by
              rw [show (3 : Nat) = 2 + 1 from rfl, Nat.pow_add W 2 1, Nat.pow_one,
                  hW2_S, hW_fac, ha_sp]
              generalize w0 ^ 2 = U2, 3 ^ (a - 1) = PA1
              rw [Nat.mul_assoc S U2 (3 * PA1 * w0),
                  ← Nat.mul_assoc U2 (3 * PA1) w0,
                  ← Nat.mul_assoc U2 3 PA1, Nat.mul_comm U2 3,
                  Nat.mul_assoc 3 U2 PA1, Nat.mul_comm U2 PA1,
                  Nat.mul_assoc 3 (PA1 * U2) w0]
            refine ⟨2 * P * (P + 1) * (Q + 1) * q ^ 3 * (3 ^ (a - 1) * w0 ^ 2 * w0) * K, ?_⟩
            dsimp [T2]; rw [hw3]
            exact pull_front_S3_prod (2 * P * (P + 1) * (Q + 1) * q ^ 3) S (3 ^ (a - 1) * w0 ^ 2 * w0) K
          have hT4_S3 : ∃ m4, T4 = S * (3 * m4) := by
            have hQ2_sp : Q ^ 2 = S * (3 * 3 ^ (2 * u - 2 * a - 1)) := by
              dsimp [Q, S]
              rw [Nat.pow_two (3 ^ u), ← Nat.pow_add 3 u u,
                  show u + u = 2 * a + (1 + (2 * u - 2 * a - 1)) by omega,
                  Nat.pow_add 3 (2 * a), Nat.pow_add 3 1, Nat.pow_one]
            refine ⟨4 * p ^ 3 * 3 ^ (2 * u - 2 * a - 1) * K ^ 4, ?_⟩
            dsimp [T4]; rw [hQ2_sp]
            exact pull_front_S3_prod (4 * p ^ 3) S (3 ^ (2 * u - 2 * a - 1)) (K ^ 4)
          let q3 := P * p * q ^ 2 * (Q ^ 2 + 10 * Q + 1) * w0 ^ 2 * K ^ 2
          have hT3_S : T3 = S * q3 := by
            dsimp [T3, q3]; rw [hW2_S]
            exact pull_front_S_prod (P * p * q ^ 2 * (Q ^ 2 + 10 * Q + 1)) S (w0 ^ 2) (K ^ 2)
          rcases hW4_S3 with ⟨m1, hm1⟩
          rcases hT2_S3 with ⟨m2, hm2⟩
          rcases hT4_S3 with ⟨m4, hm4⟩
          rw [hm1, hT3_S, hm2, hm4, ← Nat.mul_add S, ← Nat.mul_add S] at hbr_nat_eq
          have hq_eq := nat_mul_left_cancel_pos S _ _ hS_pos hbr_nat_eq
          have hq3_m3_0 : q3 % 3 = 0 := by omega
          have hq2_1 : (q ^ 2) % 3 = 1 := by rw [Nat.pow_two, Nat.mul_mod, hq_m3]
          have hw02_1 : (w0 ^ 2) % 3 = 1 := by
            rw [Nat.pow_two, Nat.mul_mod]
            rcases (by omega : w0 % 3 = 1 ∨ w0 % 3 = 2) with h | h <;> rw [h]
          have hK2_1 : (K ^ 2) % 3 = 1 := by
            rw [Nat.pow_two, Nat.mul_mod]
            rcases (by omega : K % 3 = 1 ∨ K % 3 = 2) with h | h <;> rw [h]
          have hq3_2 : q3 % 3 = 2 := by
            dsimp [q3]
            rw [Nat.mul_mod, hK2_1, Nat.mul_one, Nat.mod_mod,
                Nat.mul_mod _ (w0 ^ 2), hw02_1, Nat.mul_one, Nat.mod_mod,
                Nat.mul_mod _ (Q ^ 2 + 10 * Q + 1), hmid_1, Nat.mul_one, Nat.mod_mod,
                Nat.mul_mod _ (q ^ 2), hq2_1, Nat.mul_one, Nat.mod_mod,
                Nat.mul_mod P p, hP_m3, hp_m3]
          omega
        · -- `a ≥ u`: write `W = Q * w` (`w := 3 ^ (a - u) * w0`), divide by `Q ^ 2`, and reduce `mod 3`!
          let w := 3 ^ (a - u) * w0
          have hW_Qw : W = Q * w := by
            dsimp [Q, w]
            rw [hW_fac, ← Nat.mul_assoc (3 ^ u) (3 ^ (a - u)) w0,
                ← Nat.pow_add 3 u (a - u), show u + (a - u) = a by omega]
          let S := Q ^ 2
          have hS_pos : S ≥ 1 := nat_pow_pos_of_pos Q (by omega) 2
          have hW2_S : W ^ 2 = S * w ^ 2 := by
            dsimp [S]; rw [hW_Qw, Nat.pow_two (Q * w), Nat.pow_two Q, Nat.pow_two w]
            rw [Nat.mul_assoc Q w (Q * w), ← Nat.mul_assoc w Q w,
                Nat.mul_comm w Q, Nat.mul_assoc Q w w, ← Nat.mul_assoc Q Q]
          have hT1_S3 : ∃ m1, T1 = S * (3 * m1) := by
            have h3_S : 3 ∣ S := ⟨3 * 3 ^ (2 * u - 2), by
              dsimp [S, Q]; rw [Nat.pow_two (3 ^ u), ← Nat.pow_add 3 u u]
              conv => lhs; rw [show u + u = (2 * u - 2) + 2 by omega]
              rw [Nat.pow_add 3 (2 * u - 2) 2]
              omega⟩
            rcases h3_S with ⟨s1, hs1⟩
            have hw4 : W ^ 4 = W ^ 2 * W ^ 2 := by rw [show (4 : Nat) = 2 + 2 from rfl, Nat.pow_add]
            refine ⟨P * p * q ^ 4 * (w ^ 2 * (s1 * w ^ 2)), ?_⟩
            dsimp [T1]; rw [hw4, hW2_S]
            conv => lhs; rhs; rhs; rw [hs1]
            exact pull_front_S3_sq (P * p * q ^ 4) S (w ^ 2) s1
          have hT2_S3 : ∃ m2, T2 = S * (3 * m2) := by
            have hQ_3 : Q = 3 * 3 ^ (u - 1) := by
              dsimp [Q]; conv => lhs; rw [show u = (u - 1) + 1 by omega]
              rw [Nat.pow_succ, Nat.mul_comm]
            have hw3 : W ^ 3 = S * (3 * (3 ^ (u - 1) * w ^ 2 * w)) := by
              rw [show (3 : Nat) = 2 + 1 from rfl, Nat.pow_add W 2 1, Nat.pow_one,
                  hW2_S, hW_Qw, hQ_3]
              generalize w ^ 2 = U2, 3 ^ (u - 1) = QU1
              rw [Nat.mul_assoc S U2 (3 * QU1 * w),
                  ← Nat.mul_assoc U2 (3 * QU1) w,
                  ← Nat.mul_assoc U2 3 QU1, Nat.mul_comm U2 3,
                  Nat.mul_assoc 3 U2 QU1, Nat.mul_comm U2 QU1,
                  Nat.mul_assoc 3 (QU1 * U2) w]
            refine ⟨2 * P * (P + 1) * (Q + 1) * q ^ 3 * (3 ^ (u - 1) * w ^ 2 * w) * K, ?_⟩
            dsimp [T2]; rw [hw3]
            exact pull_front_S3_prod (2 * P * (P + 1) * (Q + 1) * q ^ 3) S (3 ^ (u - 1) * w ^ 2 * w) K
          let q3 := P * p * q ^ 2 * (Q ^ 2 + 10 * Q + 1) * w ^ 2 * K ^ 2
          have hT3_S : T3 = S * q3 := by
            dsimp [T3, q3]; rw [hW2_S]
            exact pull_front_S_prod (P * p * q ^ 2 * (Q ^ 2 + 10 * Q + 1)) S (w ^ 2) (K ^ 2)
          let q4 := 4 * p ^ 3 * K ^ 4
          have hT4_S : T4 = S * q4 := by
            dsimp [T4, q4, S]
            rw [Nat.mul_assoc (4 * p ^ 3) (Q ^ 2) (K ^ 4),
                ← Nat.mul_assoc (4 * p ^ 3) (Q ^ 2),
                Nat.mul_comm (4 * p ^ 3) (Q ^ 2),
                Nat.mul_assoc (Q ^ 2)]
          rcases hT1_S3 with ⟨m1, hm1⟩
          rcases hT2_S3 with ⟨m2, hm2⟩
          rw [hm1, hT3_S, hm2, hT4_S, ← Nat.mul_add S, ← Nat.mul_add S] at hbr_nat_eq
          have hq_eq := nat_mul_left_cancel_pos S _ _ hS_pos hbr_nat_eq
          have hK2_1 : (K ^ 2) % 3 = 1 := by
            rw [Nat.pow_two, Nat.mul_mod]
            rcases (by omega : K % 3 = 1 ∨ K % 3 = 2) with h | h <;> rw [h]
          have hK4_1 : (K ^ 4) % 3 = 1 := by
            rw [show (4 : Nat) = 2 + 2 from rfl, Nat.pow_add, Nat.mul_mod, hK2_1]
          have hp3_1 : (p ^ 3) % 3 = 1 := by
            rw [show (3 : Nat) = 2 + 1 from rfl, Nat.pow_add, Nat.pow_one, Nat.pow_two,
                Nat.mul_mod (p * p) p 3, Nat.mul_mod p p 3, hp_m3]
          have hq4_1 : q4 % 3 = 1 := by
            dsimp [q4]
            rw [Nat.mul_mod, hK4_1, Nat.mul_one, Nat.mod_mod, Nat.mul_mod 4, hp3_1]
          have hq2_1 : (q ^ 2) % 3 = 1 := by rw [Nat.pow_two, Nat.mul_mod, hq_m3]
          have hw2_01 : (w ^ 2) % 3 = 0 ∨ (w ^ 2) % 3 = 1 := by
            rw [Nat.pow_two, Nat.mul_mod]
            rcases (by omega : w % 3 = 0 ∨ w % 3 = 1 ∨ w % 3 = 2) with h0 | h1 | h2
            · left; rw [h0]
            · right; rw [h1]
            · right; rw [h2]
          have hq3_m3 : q3 % 3 = (2 * (w ^ 2 % 3)) % 3 := by
            dsimp [q3]
            rw [Nat.mul_mod, hK2_1, Nat.mul_one, Nat.mod_mod,
                Nat.mul_mod _ (w ^ 2),
                Nat.mul_mod (P * p * q ^ 2) (Q ^ 2 + 10 * Q + 1), hmid_1, Nat.mul_one, Nat.mod_mod,
                Nat.mul_mod (P * p) (q ^ 2), hq2_1, Nat.mul_one, Nat.mod_mod,
                Nat.mul_mod P p, hP_m3, hp_m3]
          have heq_m3 : q3 % 3 = q4 % 3 := by omega
          rw [hq4_1, hq3_m3] at heq_m3
          rcases hw2_01 with hw | hw <;> rw [hw] at heq_m3 <;> omega
    · -- `3 ∤ W`: reduce `evalExpr4` directly modulo `3`:
      let p := P - 1
      let q := Q - 1
      have hp_pos : P ≥ 2 := by dsimp [P]; simpa using pow2_mono_nat hu1
      have hq_pos : Q ≥ 3 := by dsimp [Q]; simpa using nat_pow_mono_exp_pos 3 1 u (by decide) hu1
      have hp_m3 : p % 3 = 1 := by dsimp [p]; omega
      have hpp_m3 : (P + 1) % 3 = 0 := by omega
      have hq_m3 : q % 3 = 2 := by dsimp [q]; omega
      let T1 : Nat := P * p * q ^ 4 * W ^ 4
      let T2 : Nat := 2 * P * (P + 1) * (Q + 1) * q ^ 3 * W ^ 3 * K
      let T3 : Nat := P * p * q ^ 2 * (Q ^ 2 + 10 * Q + 1) * W ^ 2 * K ^ 2
      let T4 : Nat := 4 * p ^ 3 * Q ^ 2 * K ^ 4
      have hbr_nat_eq : T1 + T3 = T2 + T4 := by
        have hintPow_n : ∀ (n k : Nat), intPowNat (n : Int) k = ((n ^ k : Nat) : Int) := by
          intro n k; induction k with
          | zero => rfl
          | succ k' ih => simp [intPowNat, ih, Nat.pow_succ, Nat.mul_comm (n ^ k') n, Int.natCast_mul]
        have hexprPow_n : ∀ (x0 x1 x2 x3 : Int) (e : Expr4) (k : Nat),
            evalExpr4 x0 x1 x2 x3 (expr4Pow e k) = intPowNat (evalExpr4 x0 x1 x2 x3 e) k := by
          intro x0 x1 x2 x3 e k; induction k with
          | zero => rfl
          | succ k' ih => simp [expr4Pow, evalExpr4, intPowNat, ih]
        change evalExpr4 (W : Int) (K : Int) (P : Int) (Q : Int)
          (t3u2BracketExpr .v0 .v1 .v2 .v3) = 0 at hzero
        unfold t3u2BracketExpr at hzero
        simp only [evalExpr4, hexprPow_n] at hzero
        have hp_sub : ((P : Int) - 1) = (p : Int) := by dsimp [p]; omega
        have hq_sub : ((Q : Int) - 1) = (q : Int) := by dsimp [q]; omega
        have hp_add : ((P : Int) + 1) = ((P + 1 : Nat) : Int) := by omega
        have hq_add : ((Q : Int) + 1) = ((Q + 1 : Nat) : Int) := by omega
        rw [hp_sub, hq_sub, hp_add, hq_add] at hzero
        simp only [hintPow_n] at hzero
        have hmid_c : (((Q ^ 2 : Nat) : Int) + 10 * (Q : Int) + 1) =
            ((Q ^ 2 + 10 * Q + 1 : Nat) : Int) := by omega
        rw [hmid_c] at hzero
        have hc1 : (P : Int) * ((p : Int) * ((q ^ 4 : Nat) : Int)) * ((W ^ 4 : Nat) : Int) = (T1 : Int) := by
          simp only [← Int.natCast_mul]; apply congrArg Nat.cast; dsimp only [T1]; ac_rfl
        have hc2 : (2 : Int) * ((P : Int) * (((P + 1 : Nat) : Int) *
            (((Q + 1 : Nat) : Int) * ((q ^ 3 : Nat) : Int)))) * (((W ^ 3 : Nat) : Int) * (K : Int)) =
            (T2 : Int) := by
          rw [show (2 : Int) = ((2 : Nat) : Int) from rfl]
          simp only [← Int.natCast_mul]; apply congrArg Nat.cast; dsimp only [T2]; ac_rfl
        have hc3 : (P : Int) * ((p : Int) * (((q ^ 2 : Nat) : Int) *
            ((Q ^ 2 + 10 * Q + 1 : Nat) : Int))) * (((W ^ 2 : Nat) : Int) * ((K ^ 2 : Nat) : Int)) =
            (T3 : Int) := by
          simp only [← Int.natCast_mul]; apply congrArg Nat.cast; dsimp only [T3]; ac_rfl
        have hc4 : (4 : Int) * (((p ^ 3 : Nat) : Int) * ((Q ^ 2 : Nat) : Int)) *
            ((K ^ 4 : Nat) : Int) = (T4 : Int) := by
          rw [show (4 : Int) = ((4 : Nat) : Int) from rfl]
          simp only [← Int.natCast_mul]; apply congrArg Nat.cast; dsimp only [T4]; ac_rfl
        rw [hc1, hc2, hc3, hc4] at hzero
        omega
      have hW2_1 : (W ^ 2) % 3 = 1 := by
        rw [Nat.pow_two, Nat.mul_mod]
        rcases (by omega : W % 3 = 1 ∨ W % 3 = 2) with h | h <;> rw [h]
      have hW4_1 : (W ^ 4) % 3 = 1 := by
        rw [show (4 : Nat) = 2 + 2 from rfl, Nat.pow_add, Nat.mul_mod, hW2_1]
      have hq2_1 : (q ^ 2) % 3 = 1 := by rw [Nat.pow_two, Nat.mul_mod, hq_m3]
      have hq4_1 : (q ^ 4) % 3 = 1 := by
        rw [show (4 : Nat) = 2 + 2 from rfl, Nat.pow_add, Nat.mul_mod, hq2_1]
      have hT1_2 : T1 % 3 = 2 := by
        dsimp [T1]
        rw [Nat.mul_mod, hW4_1, Nat.mul_one, Nat.mod_mod,
            Nat.mul_mod (P * p), hq4_1, Nat.mul_one, Nat.mod_mod,
            Nat.mul_mod P p, hP_m3, hp_m3]
      have hT2_0 : T2 % 3 = 0 := by
        dsimp [T2]
        have hp1_0 : (2 * P * (P + 1)) % 3 = 0 := by rw [Nat.mul_mod, hpp_m3, Nat.mul_zero]
        rw [Nat.mul_mod _ K 3, Nat.mul_mod _ (W ^ 3) 3, Nat.mul_mod _ (q ^ 3) 3,
            Nat.mul_mod _ (Q + 1) 3, hp1_0]
        simp
      have hT4_0 : T4 % 3 = 0 := by
        dsimp [T4]
        rw [Nat.mul_mod _ (K ^ 4) 3, Nat.mul_mod _ (Q ^ 2) 3, hQ2_0]
        simp
      have hK2_01 : (K ^ 2) % 3 = 0 ∨ (K ^ 2) % 3 = 1 := by
        rw [Nat.pow_two, Nat.mul_mod]
        rcases (by omega : K % 3 = 0 ∨ K % 3 = 1 ∨ K % 3 = 2) with h0 | h1 | h2
        · left; rw [h0]
        · right; rw [h1]
        · right; rw [h2]
      have hT3_02 : T3 % 3 = 0 ∨ T3 % 3 = 2 := by
        dsimp [T3]
        rw [Nat.mul_mod,
            Nat.mul_mod _ (W ^ 2), hW2_1, Nat.mul_one, Nat.mod_mod,
            Nat.mul_mod _ (Q ^ 2 + 10 * Q + 1), hmid_1, Nat.mul_one, Nat.mod_mod,
            Nat.mul_mod _ (q ^ 2), hq2_1, Nat.mul_one, Nat.mod_mod,
            Nat.mul_mod P p, hP_m3, hp_m3]
        rcases hK2_01 with hk0 | hk1
        · left; rw [hk0]
        · right; rw [hk1]
      have hrhs0 : (T2 + T4) % 3 = 0 := by rw [Nat.add_mod, hT2_0, hT4_0]
      rw [← hbr_nat_eq, Nat.add_mod, hT1_2] at hrhs0
      rcases hT3_02 with ht | ht <;> rw [ht] at hrhs0 <;> omega

set_option maxRecDepth 32768 in
/--
  Theorem W11.2c (`laurent_6x6_t3u2_factorization_and_cone_positivity`, `zero custom axioms`):
  Exact Rank-2 Vandermonde `6 × 6` Two-Base `(T = 3, U = 2)` Schneider–Laurent Closed Form,
  Universal Odd-`u` Non-Vanishing (`∀ W, K ≥ 1`), All-`u ≥ 1` Collatz Cone Strict Positivity,
  & Even-`u = 2` Resonant Zero `(3, 8, 2)`:
  1. **Exact Homogeneous Degree-6 Closed Form (`∀ W, K, u ≥ 1`)**:
     `4 * intDet 6 (laurentTwoBaseT3U2Mat6 W K u) =
        K^2 * Q * (P*p*q^4*W^4 - 2*P*(P+1)*(Q+1)*q^3*W^3*K
                   + P*p*q^2*(Q^2 + 10*Q + 1)*W^2*K^2 - 4*p^3*Q^2*K^4)`.
  2. **Universal Odd-`u` Non-Vanishing Across ALL `(W, K) ∈ (Z^+)^2`**:
     Whenever `u % 2 = 1`, `intDet 6 (laurentTwoBaseT3U2Mat6 W K u) ≠ 0` for ALL `W, K ≥ 1`
     (completely eliminating Wave 10's `(T = 2, U = 3)` odd-`u = 1` zero at `(9, 16)`!).
  3. **Unconditional Strict Positivity Inside the Collatz Cone (`∀ u ≥ 1`)**:
     Whenever `3 ^ W < 2 ^ K` and `3 * K ≤ 5 * W` (`W, K, u ≥ 1`),
       `intDet 6 (laurentTwoBaseT3U2Mat6 W K u) > 0` (with ZERO sign flips even at `u = 1, 2`!).
  4. **Even-`u = 2` Resonant Zero & Outer Sign-Flip Witnesses (`W11_H3`)**:
     At coprime `(W, K) = (3, 8)` (`3 ^ 3 < 2 ^ 8`) and even `u = 2`,
     `intDet 6 (laurentTwoBaseT3U2Mat6 3 8 2) = 0`, and at `(W, K, u) = (1, 2, 1)`,
     `intDet 6 (laurentTwoBaseT3U2Mat6 1 2 1) = -96 < 0`, while `(9, 16, 1)` is non-zero!
-/
theorem laurent_6x6_t3u2_factorization_and_cone_positivity :
    (∀ W K u : Nat, W ≥ 1 -> K ≥ 1 -> u ≥ 1 ->
      4 * intDet 6 (laurentTwoBaseT3U2Mat6 W K u) =
        evalExpr4 (W : Int) (K : Int) ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int)
          twoBaseT3U2ScaledClosedExpr) ∧
    (∀ W K u : Nat, W ≥ 1 -> K ≥ 1 -> u % 2 = 1 ->
      intDet 6 (laurentTwoBaseT3U2Mat6 W K u) ≠ 0) ∧
    (∀ W K u : Nat, W ≥ 1 -> K ≥ 1 -> u ≥ 1 ->
      3 ^ W < 2 ^ K -> 3 * K ≤ 5 * W ->
      intDet 6 (laurentTwoBaseT3U2Mat6 W K u) > 0) ∧
    (intDet 6 (laurentTwoBaseT3U2Mat6 3 8 2) = 0 ∧
     intDet 6 (laurentTwoBaseT3U2Mat6 1 2 1) = -96 ∧
     intDet 6 (laurentTwoBaseT3U2Mat6 9 16 1) ≠ 0) := by
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
  have hintPow_c : ∀ (n k : Nat), intPowNat (n : Int) k = ((n ^ k : Nat) : Int) := by
    intro n k; induction k with
    | zero => rfl
    | succ k' ih => simp [intPowNat, ih, Nat.pow_succ, Nat.mul_comm (n ^ k') n, Int.natCast_mul]
  have hexprPow_c : ∀ (x0 x1 x2 x3 : Int) (e : Expr4) (k : Nat),
      evalExpr4 x0 x1 x2 x3 (expr4Pow e k) = intPowNat (evalExpr4 x0 x1 x2 x3 e) k := by
    intro x0 x1 x2 x3 e k; induction k with
    | zero => rfl
    | succ k' ih => simp [expr4Pow, evalExpr4, intPowNat, ih]
  have hclosed : ∀ W K u : Nat, W ≥ 1 -> K ≥ 1 -> u ≥ 1 ->
      4 * intDet 6 (laurentTwoBaseT3U2Mat6 W K u) =
        evalExpr4 (W : Int) (K : Int) ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int)
          twoBaseT3U2ScaledClosedExpr := by
    intro W K u _ _ _
    let P := 2 ^ u
    let Q := 3 ^ u
    let A0 := laurentTwoBaseT3U2Mat6 W K u
    let c2 : Fin 6 := ⟨2, by decide⟩
    let c5 : Fin 6 := ⟨5, by decide⟩
    let A1 : Fin 6 -> Fin 6 -> Int := fun i j => if j = c2 then 2 * A0 i c2 else A0 i j
    let A2 : Fin 6 -> Fin 6 -> Int := fun i j => if j = c5 then 2 * A1 i c5 else A1 i j
    have hs1 : intDet 6 A1 = 2 * intDet 6 A0 := intDet_col_scale 2 6 c2 A0
    have hs2 : intDet 6 A2 = 2 * intDet 6 A1 := intDet_col_scale 2 6 c5 A1
    have h4 : intDet 6 A2 = 4 * intDet 6 A0 := by rw [hs2, hs1]; omega
    have hpoly := poly4Det_eq_of_sub_nil twoBaseT3U2ScaledExprMat6 twoBaseT3U2ScaledClosedExpr
      twoBaseT3U2_poly_identity (W : Int) (K : Int) (P : Int) (Q : Int)
    have hmat_eq : A2 = (fun i j =>
        evalExpr4 (W : Int) (K : Int) (P : Int) (Q : Int) (twoBaseT3U2ScaledExprMat6 i j)) := by
      funext i j
      let rs := laurentRowsTwoBase6 i
      let r := rs.1
      let s := rs.2
      let n := r * W + s * K
      have hn_i : ((r : Int) * (W : Int) + (s : Int) * (K : Int)) = (n : Int) := by
        dsimp only [n]; simp only [Int.natCast_add, Int.natCast_mul]
      have hpow_i : evalExpr4 (W : Int) (K : Int) (P : Int) (Q : Int)
          (.mul (expr4Pow .v2 r) (expr4Pow .v3 s)) =
          ((2 ^ (r * u) * 3 ^ (s * u) : Nat) : Int) := by
        simp only [evalExpr4, hexprPow_c, hintPow_c, ← Int.natCast_mul]
        apply congrArg Nat.cast
        dsimp only [P, Q]
        rw [pow_pow_eq_mul_w5 2 u r, pow_pow_eq_mul_w5 3 u s,
            Nat.mul_comm u r, Nat.mul_comm u s]
      have hj_c : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5 := by
        have := j.isLt; omega
      rcases hj_c with h0 | h1 | h2 | h3 | h4_c | h5
      · have hjf : j = ⟨0, by decide⟩ := Fin.ext h0; subst hjf
        change A0 i ⟨0, by decide⟩ = 1
        unfold A0 laurentTwoBaseT3U2Mat6 laurentInterpMat
        rw [show laurentColsC32_6 u ⟨0, by decide⟩ = (0, 0) from rfl]
        unfold laurentInterpEntry; simp [laurentInterpBinom_zero_right]
      · have hjf : j = ⟨1, by decide⟩ := Fin.ext h1; subst hjf
        change A0 i ⟨1, by decide⟩ = (r : Int) * (W : Int) + (s : Int) * (K : Int)
        rw [hn_i]
        unfold A0 laurentTwoBaseT3U2Mat6 laurentInterpMat
        rw [show laurentColsC32_6 u ⟨1, by decide⟩ = (1, 0) from rfl]
        unfold laurentInterpEntry; dsimp only
        rw [laurentInterpBinom_one_right, Nat.mul_zero, Nat.mul_zero, Nat.pow_zero,
            Nat.mul_one, Nat.mul_one]
      · have hjf : j = ⟨2, by decide⟩ := Fin.ext h2; subst hjf
        change 2 * A0 i ⟨2, by decide⟩ =
          ((r : Int) * (W : Int) + (s : Int) * (K : Int)) *
            (((r : Int) * (W : Int) + (s : Int) * (K : Int)) - 1)
        rw [hn_i]
        unfold A0 laurentTwoBaseT3U2Mat6 laurentInterpMat
        rw [show laurentColsC32_6 u ⟨2, by decide⟩ = (2, 0) from rfl]
        unfold laurentInterpEntry; dsimp only
        rw [Nat.mul_zero, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.mul_one,
            show (r * W + s * K) = n from rfl,
            show (2 : Int) = ((2 : Nat) : Int) from rfl, ← Int.natCast_mul, hb2 n]
        cases n with
        | zero => rfl
        | succ m => rw [Int.natCast_mul]; congr 1; omega
      · have hjf : j = ⟨3, by decide⟩ := Fin.ext h3; subst hjf
        change A0 i ⟨3, by decide⟩ =
          evalExpr4 (W : Int) (K : Int) (P : Int) (Q : Int) (.mul (expr4Pow .v2 r) (expr4Pow .v3 s))
        rw [hpow_i]
        unfold A0 laurentTwoBaseT3U2Mat6 laurentInterpMat
        rw [show laurentColsC32_6 u ⟨3, by decide⟩ = (0, u) from rfl]
        unfold laurentInterpEntry; dsimp only
        rw [laurentInterpBinom_zero_right, Nat.one_mul]
      · have hjf : j = ⟨4, by decide⟩ := Fin.ext h4_c; subst hjf
        change A0 i ⟨4, by decide⟩ =
          ((r : Int) * (W : Int) + (s : Int) * (K : Int)) *
            evalExpr4 (W : Int) (K : Int) (P : Int) (Q : Int) (.mul (expr4Pow .v2 r) (expr4Pow .v3 s))
        rw [hn_i, hpow_i, ← Int.natCast_mul]
        unfold A0 laurentTwoBaseT3U2Mat6 laurentInterpMat
        rw [show laurentColsC32_6 u ⟨4, by decide⟩ = (1, u) from rfl]
        unfold laurentInterpEntry; dsimp only
        rw [laurentInterpBinom_one_right, ← Nat.mul_assoc]
      · have hjf : j = ⟨5, by decide⟩ := Fin.ext h5; subst hjf
        change 2 * A0 i ⟨5, by decide⟩ =
          (((r : Int) * (W : Int) + (s : Int) * (K : Int)) *
            (((r : Int) * (W : Int) + (s : Int) * (K : Int)) - 1)) *
            evalExpr4 (W : Int) (K : Int) (P : Int) (Q : Int) (.mul (expr4Pow .v2 r) (expr4Pow .v3 s))
        rw [hn_i, hpow_i]
        unfold A0 laurentTwoBaseT3U2Mat6 laurentInterpMat
        rw [show laurentColsC32_6 u ⟨5, by decide⟩ = (2, u) from rfl]
        unfold laurentInterpEntry
        change (2 : Int) * (((laurentInterpBinom n 2 * 2 ^ (r * u)) * 3 ^ (s * u) : Nat) : Int) = _
        rw [show (2 : Int) = ((2 : Nat) : Int) from rfl,
            ← Int.natCast_mul,
            Nat.mul_assoc (laurentInterpBinom n 2) (2 ^ (r * u)) (3 ^ (s * u)),
            ← Nat.mul_assoc 2 (laurentInterpBinom n 2),
            hb2 n]
        cases n with
        | zero => simp
        | succ m =>
          rw [Int.natCast_mul, Int.natCast_mul]
          congr 1; congr 1; omega
    rw [← h4, hmat_eq]
    exact hpoly
  refine ⟨hclosed, ?_, ?_, ?_⟩
  · -- Part 2: Universal odd-`u` non-vanishing across ALL `W, K ≥ 1`:
    intro W K u hW hK hu_odd hdet0
    have hu1 : u ≥ 1 := by omega
    have hc := hclosed W K u hW hK hu1
    rw [hdet0, Int.mul_zero] at hc
    unfold twoBaseT3U2ScaledClosedExpr at hc
    simp only [evalExpr4, hexprPow_c, hintPow_c] at hc
    have hK2Q_pos : ((K ^ 2 : Nat) : Int) * ((3 ^ u : Nat) : Int) > 0 := by
      rw [← Int.natCast_mul]
      have hp : K ^ 2 * 3 ^ u ≥ 1 := Nat.mul_le_mul (nat_pow_pos_of_pos K hK 2) (pow3_pos_nat u)
      omega
    rw [← Int.mul_assoc] at hc
    have hbr0 : evalExpr4 (W : Int) (K : Int) ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int)
        (t3u2BracketExpr .v0 .v1 .v2 .v3) = 0 := by
      rcases Int.mul_eq_zero.mp hc.symm with hk0 | hb0
      · omega
      · exact hb0
    exact t3u2_odd_u_bracket_nonzero (W + K) W K u (Nat.le_refl _) hW hK hu_odd hbr0
  · -- Part 3: Unconditional strict positivity `> 0` inside `3^W < 2^K ∧ 3 * K ≤ 5 * W` for ALL `u ≥ 1`:
    intro W K u hW hK hu hgt hcone
    -- Step 3.1: `2 ^ 84 < 3 ^ 53` implies `84 * W < 53 * K` (`A := 53 * K - 84 * W ≥ 1`)!
    have h84_53 : 84 * W < 53 * K := by
      have hpow_lt : ∀ (a b m : Nat), a < b -> m ≥ 1 -> a ^ m < b ^ m := by
        intro a b m hab; induction m with
        | zero => intro hm; omega
        | succ m' ihm =>
          intro _
          cases m' with
          | zero => simpa using hab
          | succ r =>
            have ih0 := ihm (by omega)
            by_cases ha0 : a = 0
            · subst ha0; rw [Nat.zero_pow (by omega)]
              exact nat_pow_pos_of_pos b (by omega) (r + 2)
            · rw [Nat.pow_succ a (r + 1), Nat.pow_succ b (r + 1)]
              exact Nat.lt_of_lt_of_le
                (Nat.mul_lt_mul_of_pos_right ih0 (by omega))
                (Nat.mul_le_mul_left (b ^ (r + 1)) (Nat.le_of_lt hab))
      have hbase : 2 ^ 84 < 3 ^ 53 := by decide
      have hpW : (2 ^ 84) ^ W < (3 ^ 53) ^ W := hpow_lt (2 ^ 84) (3 ^ 53) W hbase hW
      have hpK : (3 ^ W) ^ 53 < (2 ^ K) ^ 53 := hpow_lt (3 ^ W) (2 ^ K) 53 hgt (by decide)
      rw [pow_pow_eq_mul_w5 2 84 W, pow_pow_eq_mul_w5 3 53 W] at hpW
      rw [pow_pow_eq_mul_w5 3 W 53, pow_pow_eq_mul_w5 2 K 53, Nat.mul_comm W 53,
          Nat.mul_comm K 53] at hpK
      have h2_lt : 2 ^ (84 * W) < 2 ^ (53 * K) := Nat.lt_trans hpW hpK
      by_cases hlt : 84 * W < 53 * K
      · exact hlt
      · have hle := pow2_mono_nat (by omega : 53 * K ≤ 84 * W)
        omega
    let A : Int := (53 * K - 84 * W : Nat)
    let B_c : Int := (5 * W - 3 * K : Nat)
    have hA_ge1 : 1 ≤ A := by dsimp [A]; omega
    have hB_ge0 : 0 ≤ B_c := by dsimp [B_c]; omega
    have h13W : (13 : Int) * (W : Int) = 3 * A + 53 * B_c := by dsimp [A, B_c]; omega
    have h13K : (13 : Int) * (K : Int) = 5 * A + 84 * B_c := by dsimp [A, B_c]; omega
    let P_i : Int := ((2 ^ u : Nat) : Int)
    let Q_i : Int := ((3 ^ u : Nat) : Int)
    have hhom13 := expr4_eq_of_norm_sub_nil
      (.mul (.const 28561) (t3u2BracketExpr .v0 .v1 .v2 .v3))
      (t3u2BracketExpr (.mul (.const 13) .v0) (.mul (.const 13) .v1) .v2 .v3)
      t3u2_homog4_identity (W : Int) (K : Int) P_i Q_i
    have hsubst13 : evalExpr4 (W : Int) (K : Int) P_i Q_i
        (t3u2BracketExpr (.mul (.const 13) .v0) (.mul (.const 13) .v1) .v2 .v3) =
      evalExpr4 ((13 : Int) * (W : Int)) ((13 : Int) * (K : Int)) P_i Q_i
        (t3u2BracketExpr .v0 .v1 .v2 .v3) := rfl
    rw [hsubst13, h13W, h13K] at hhom13
    simp only [evalExpr4] at hhom13
    rcases t3u2_cone_pos_certs with
      ⟨hc1, hp1, hc2, hp2, hc3, hp3, hc4, hp4, hc5, hp5⟩
    have hbr13_pos : evalExpr4 (3 * A + 53 * B_c) (5 * A + 84 * B_c) P_i Q_i
        (t3u2BracketExpr .v0 .v1 .v2 .v3) > 0 := by
      by_cases hu_le4 : u ≤ 4
      · have hu_c : u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 4 := by omega
        rcases hu_c with rfl | rfl | rfl | rfl
        · have hev : evalExpr4 A B_c 0 0 (t3u2ConeFixedUExpr 2 3) =
              evalExpr4 (3 * A + 53 * B_c) (5 * A + 84 * B_c) P_i Q_i
                (t3u2BracketExpr .v0 .v1 .v2 .v3) := rfl
          rw [← hev, ← evalPoly4_normExpr4 A B_c 0 0]
          have hm := evalPoly4_mono_of_nonneg 1 0 0 0 A B_c 0 0
            (by decide) hA_ge1 (by decide) hB_ge0 (by decide) (Int.le_refl 0) (by decide) (Int.le_refl 0)
            _ hc1
          rw [evalPoly4_normExpr4 1 0 0 0] at hm
          omega
        · have hev : evalExpr4 A B_c 0 0 (t3u2ConeFixedUExpr 4 9) =
              evalExpr4 (3 * A + 53 * B_c) (5 * A + 84 * B_c) P_i Q_i
                (t3u2BracketExpr .v0 .v1 .v2 .v3) := rfl
          rw [← hev, ← evalPoly4_normExpr4 A B_c 0 0]
          have hm := evalPoly4_mono_of_nonneg 1 0 0 0 A B_c 0 0
            (by decide) hA_ge1 (by decide) hB_ge0 (by decide) (Int.le_refl 0) (by decide) (Int.le_refl 0)
            _ hc2
          rw [evalPoly4_normExpr4 1 0 0 0] at hm
          omega
        · have hev : evalExpr4 A B_c 0 0 (t3u2ConeFixedUExpr 8 27) =
              evalExpr4 (3 * A + 53 * B_c) (5 * A + 84 * B_c) P_i Q_i
                (t3u2BracketExpr .v0 .v1 .v2 .v3) := rfl
          rw [← hev, ← evalPoly4_normExpr4 A B_c 0 0]
          have hm := evalPoly4_mono_of_nonneg 1 0 0 0 A B_c 0 0
            (by decide) hA_ge1 (by decide) hB_ge0 (by decide) (Int.le_refl 0) (by decide) (Int.le_refl 0)
            _ hc3
          rw [evalPoly4_normExpr4 1 0 0 0] at hm
          omega
        · have hev : evalExpr4 A B_c 0 0 (t3u2ConeFixedUExpr 16 81) =
              evalExpr4 (3 * A + 53 * B_c) (5 * A + 84 * B_c) P_i Q_i
                (t3u2BracketExpr .v0 .v1 .v2 .v3) := rfl
          rw [← hev, ← evalPoly4_normExpr4 A B_c 0 0]
          have hm := evalPoly4_mono_of_nonneg 1 0 0 0 A B_c 0 0
            (by decide) hA_ge1 (by decide) hB_ge0 (by decide) (Int.le_refl 0) (by decide) (Int.le_refl 0)
            _ hc4
          rw [evalPoly4_normExpr4 1 0 0 0] at hm
          omega
      · -- `u ≥ 5`: `P = 32 + dP`, `Q = 7 * P + 19 + dQ` with `dP ≥ 0, dQ ≥ 0`:
        have hu5 : u ≥ 5 := by omega
        have hp_ge32 : 2 ^ u ≥ 32 := by
          have hc32 : (2 : Nat) ^ 5 = 32 := by decide
          rw [← hc32]; exact pow2_mono_nat hu5
        have hq_ge7 : 3 ^ u ≥ 7 * 2 ^ u + 19 := pow3_ge_7_mul_pow2_add19 u hu5
        let dP : Int := (2 ^ u - 32 : Nat)
        let dQ : Int := (3 ^ u - (7 * 2 ^ u + 19) : Nat)
        have hdP_ge0 : 0 ≤ dP := by dsimp [dP]; omega
        have hdQ_ge0 : 0 ≤ dQ := by dsimp [dQ]; omega
        have hP_eq : 32 + dP = P_i := by
          dsimp only [dP, P_i]
          have hn : 32 + (2 ^ u - 32) = 2 ^ u := by omega
          exact (Int.natCast_add 32 (2 ^ u - 32)).symm.trans (congrArg Nat.cast hn)
        have hQ_eq : 7 * (32 + dP) + 19 + dQ = Q_i := by
          rw [hP_eq]; dsimp only [P_i, dQ, Q_i]
          have hn : 7 * 2 ^ u + 19 + (3 ^ u - (7 * 2 ^ u + 19)) = 3 ^ u := by omega
          have hc := congrArg (fun x : Nat => (x : Int)) hn
          simpa [Int.natCast_add, Int.natCast_mul] using hc
        have hev5 : evalExpr4 A B_c dP dQ t3u2ConeGe5Expr =
            evalExpr4 (3 * A + 53 * B_c) (5 * A + 84 * B_c) P_i Q_i
              (t3u2BracketExpr .v0 .v1 .v2 .v3) := by
          unfold t3u2ConeGe5Expr
          have hsub_eval : ∀ (eW eK eP eQ : Expr4),
              evalExpr4 A B_c dP dQ (t3u2BracketExpr eW eK eP eQ) =
              evalExpr4 (evalExpr4 A B_c dP dQ eW)
                        (evalExpr4 A B_c dP dQ eK)
                        (evalExpr4 A B_c dP dQ eP)
                        (evalExpr4 A B_c dP dQ eQ)
                        (t3u2BracketExpr .v0 .v1 .v2 .v3) := by
            intro eW eK eP eQ
            unfold t3u2BracketExpr
            have hpow4 : ∀ (ex : Expr4) (k : Nat),
                evalExpr4 A B_c dP dQ (expr4Pow ex k) =
                  intPowNat (evalExpr4 A B_c dP dQ ex) k := fun ex k => hexprPow_c A B_c dP dQ ex k
            have hpow0 : ∀ (v0 v1 v2 v3 : Int) (ex : Expr4) (k : Nat),
                evalExpr4 v0 v1 v2 v3 (expr4Pow ex k) =
                  intPowNat (evalExpr4 v0 v1 v2 v3 ex) k := fun v0 v1 v2 v3 ex k => hexprPow_c v0 v1 v2 v3 ex k
            simp only [evalExpr4, hpow4, hpow0]
          rw [hsub_eval]
          have hw_ev : evalExpr4 A B_c dP dQ t3u2ConeExprW = 3 * A + 53 * B_c := rfl
          have hk_ev : evalExpr4 A B_c dP dQ t3u2ConeExprK = 5 * A + 84 * B_c := rfl
          have hp_ev : evalExpr4 A B_c dP dQ (.add (.const 32) .v2) = P_i := hP_eq
          have hq_ev : evalExpr4 A B_c dP dQ
              (.add (.add (.mul (.const 7) (.add (.const 32) .v2)) (.const 19)) .v3) = Q_i := hQ_eq
          rw [hw_ev, hk_ev, hp_ev, hq_ev]
        rw [← hev5, ← evalPoly4_normExpr4 A B_c dP dQ]
        have hm := evalPoly4_mono_of_nonneg 1 0 0 0 A B_c dP dQ
          (by decide) hA_ge1 (by decide) hB_ge0 (by decide) hdP_ge0 (by decide) hdQ_ge0
          _ hc5
        rw [evalPoly4_normExpr4 1 0 0 0] at hm
        omega
    have hbr_pos : evalExpr4 (W : Int) (K : Int) P_i Q_i (t3u2BracketExpr .v0 .v1 .v2 .v3) > 0 := by
      generalize evalExpr4 (W : Int) (K : Int) P_i Q_i (t3u2BracketExpr .v0 .v1 .v2 .v3) = BV at hhom13 ⊢
      omega
    have hc_det := hclosed W K u hW hK hu
    unfold twoBaseT3U2ScaledClosedExpr at hc_det
    simp only [evalExpr4, hexprPow_c, hintPow_c] at hc_det
    have hK2Q_pos : ((K ^ 2 : Nat) : Int) * (((3 ^ u : Nat) : Int)) > 0 := by
      rw [← Int.natCast_mul]
      have hp : K ^ 2 * 3 ^ u ≥ 1 := Nat.mul_le_mul (nat_pow_pos_of_pos K hK 2) (pow3_pos_nat u)
      omega
    have hprod_pos : ((K ^ 2 : Nat) : Int) *
        (((3 ^ u : Nat) : Int) *
          evalExpr4 (W : Int) (K : Int) ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int)
            (t3u2BracketExpr .v0 .v1 .v2 .v3)) > 0 := by
      rw [← Int.mul_assoc]
      exact Int.mul_pos hK2Q_pos hbr_pos
    generalize intDet 6 (laurentTwoBaseT3U2Mat6 W K u) = D6 at hc_det ⊢
    generalize ((K ^ 2 : Nat) : Int) * (((3 ^ u : Nat) : Int) *
      evalExpr4 (W : Int) (K : Int) ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int)
        (t3u2BracketExpr .v0 .v1 .v2 .v3)) = PR at hc_det hprod_pos
    omega
  · -- Part 4: Concrete `(3, 8, 2) = 0`, `(1, 2, 1) = -96`, and `(9, 16, 1) ≠ 0`:
    have hc38 := hclosed 3 8 2 (by decide) (by decide) (by decide)
    have hr38 : evalExpr4 ((3 : Nat) : Int) ((8 : Nat) : Int) ((2 ^ 2 : Nat) : Int) ((3 ^ 2 : Nat) : Int)
        twoBaseT3U2ScaledClosedExpr = 0 := by decide
    rw [hr38] at hc38
    have hc12 := hclosed 1 2 1 (by decide) (by decide) (by decide)
    have hr12 : evalExpr4 ((1 : Nat) : Int) ((2 : Nat) : Int) ((2 ^ 1 : Nat) : Int) ((3 ^ 1 : Nat) : Int)
        twoBaseT3U2ScaledClosedExpr = -384 := by decide
    rw [hr12] at hc12
    have hnz916 := t3u2_odd_u_bracket_nonzero 25 9 16 1 (by decide) (by decide) (by decide) (by decide)
    have hc916 := hclosed 9 16 1 (by decide) (by decide) (by decide)
    refine ⟨by omega, by omega, ?_⟩
    intro hz
    rw [hz, Int.mul_zero] at hc916
    unfold twoBaseT3U2ScaledClosedExpr at hc916
    simp only [evalExpr4, hexprPow_c, hintPow_c] at hc916
    apply hnz916
    generalize evalExpr4 ((9 : Nat) : Int) ((16 : Nat) : Int) ((2 ^ 1 : Nat) : Int) ((3 ^ 1 : Nat) : Int)
      (t3u2BracketExpr .v0 .v1 .v2 .v3) = BV at hc916 ⊢
    omega

-- Two-Base `8 × 8` Rank-2 Vandermonde `(T = 4, U = 2)` Grid (`laurentRowsTwoBase8 × laurentColsC42_8`):

def laurentRowsTwoBase8 (i : Fin 8) : Nat × Nat :=
  match i.val with
  | 0 => (0, 0) | 1 => (1, 0) | 2 => (0, 1) | 3 => (1, 1)
  | 4 => (0, 2) | 5 => (1, 2) | 6 => (0, 3) | _ => (1, 3)

def laurentColsC42_8 (u : Nat) (j : Fin 8) : Nat × Nat :=
  match j.val with
  | 0 => (0, 0) | 1 => (1, 0) | 2 => (2, 0) | 3 => (3, 0)
  | 4 => (0, u) | 5 => (1, u) | 6 => (2, u) | _ => (3, u)

def laurentTwoBaseT4U2Mat8 (W K u : Nat) : Fin 8 -> Fin 8 -> Int :=
  laurentInterpMat W K 8 laurentRowsTwoBase8 (laurentColsC42_8 u)

theorem intSumFin_single_nonzero (L : Nat) (f : Fin L -> Int) (j0 : Fin L)
    (hz : ∀ j : Fin L, j ≠ j0 -> f j = 0) :
    intSumFin L f = f j0 := by
  unfold intSumFin
  have hpref : ∀ k : Nat, k ≤ L ->
      intSumPrefix L f k = if j0.val < k then f j0 else 0 := by
    intro k hk; induction k with
    | zero => simp [intSumPrefix]
    | succ k' ih =>
      have hk_lt : k' < L := hk
      simp only [intSumPrefix, hk_lt, dite_true, ih (Nat.le_of_lt hk)]
      by_cases hjk : j0.val < k'
      · have hjk1 : j0.val < k' + 1 := by omega
        have hne : (⟨k', hk_lt⟩ : Fin L) ≠ j0 := fun heq => by rw [← heq] at hjk; exact Nat.lt_irrefl k' hjk
        rw [ite_true_of_w10 hjk, ite_true_of_w10 hjk1, hz ⟨k', hk_lt⟩ hne, Int.add_zero]
      · by_cases hjeq : j0.val = k'
        · have hjk1 : j0.val < k' + 1 := by omega
          have hjf : (⟨k', hk_lt⟩ : Fin L) = j0 := Fin.ext hjeq.symm
          rw [ite_false_of_w10 hjk, ite_true_of_w10 hjk1, hjf, Int.zero_add]
        · have hjgt : ¬ (j0.val < k' + 1) := by omega
          have hne : (⟨k', hk_lt⟩ : Fin L) ≠ j0 := fun heq => hjeq (congrArg Fin.val heq).symm
          rw [ite_false_of_w10 hjk, ite_false_of_w10 hjgt, hz ⟨k', hk_lt⟩ hne, Int.add_zero]
  rw [hpref L (Nat.le_refl L), ite_true_of_w10 j0.isLt]

theorem intDet_succ_single_row0 (L : Nat) (A : Fin (L + 1) -> Fin (L + 1) -> Int)
    (j0 : Fin (L + 1)) (hz : ∀ j : Fin (L + 1), j ≠ j0 -> A ⟨0, Nat.zero_lt_succ L⟩ j = 0) :
    intDet (L + 1) A =
      (if j0.val % 2 = 0 then (1 : Int) else -1) *
        A ⟨0, Nat.zero_lt_succ L⟩ j0 * intDet L (intSubMat A j0) := by
  conv => lhs; unfold intDet
  apply intSumFin_single_nonzero (L + 1) _ j0
  intro j hj
  rw [hz j hj, Int.mul_zero, Int.zero_mul]

theorem intDet8_two_ones_row0 (A : Fin 8 -> Fin 8 -> Int)
    (h0 : A 0 0 = 1) (h4 : A 0 4 = 1)
    (hz : ∀ j : Fin 8, j ≠ 0 -> j ≠ 4 -> A 0 j = 0) :
    intDet 8 A = intDet 7 (intSubMat (fun i j =>
      if j = 4 then A i 4 - A i 0 else A i j) 0) := by
  let idx0 : Nat -> Fin 8 := fun _ => 0
  let coef0 : Nat -> Int := fun _ => 1
  have hsub := intDet_sub_col_prefix_invariant 8 4 A 1 idx0 coef0
    (fun s hs => by rw [show s = 0 by omega]; decide)
  have hcomb : ∀ i : Fin 8, colPrefixComb A idx0 coef0 i 1 = A i 0 := by
    intro i; simp [colPrefixComb, idx0, coef0]
  let A1 : Fin 8 -> Fin 8 -> Int := fun i j =>
    if j = 4 then A i 4 - A i 0 else A i j
  have hA1_eq : (fun i j : Fin 8 =>
      if j = 4 then A i 4 - colPrefixComb A idx0 coef0 i 1 else A i j) = A1 := by
    funext i j; rw [hcomb i]
  have hz0 : (⟨0, Nat.zero_lt_succ 7⟩ : Fin 8) = 0 := rfl
  rw [hsub, hA1_eq, intDet_succ_single_row0 7 A1 0, hz0]
  · have h00 : A1 0 0 = 1 := by
      change (if (0 : Fin 8) = 4 then _ else A 0 0) = 1
      rw [ite_false_of_w10 (by decide), h0]
    rw [h00]
    change (if (0 : Nat) % 2 = 0 then (1 : Int) else -1) * 1 * intDet 7 (intSubMat A1 0) =
      intDet 7 (intSubMat A1 0)
    simp
  · intro j hj0
    rw [hz0]
    change (if j = 4 then A 0 4 - A 0 0 else A 0 j) = 0
    by_cases hj4 : j = 4
    · rw [ite_true_of_w10 hj4, h4, h0, Int.sub_self]
    · rw [ite_false_of_w10 hj4, hz j hj0 hj4]

theorem intDet7_pivot_col2 (B : Fin 7 -> Fin 7 -> Int) (h02 : B 0 2 = 1) :
    intDet 7 B = intDet 6 (intSubMat (fun i j =>
      if j = 2 then B i j else B i j - B 0 j * B i 2) 2) := by
  have hcol : ∀ (M_cur : Fin 7 -> Fin 7 -> Int) (c : Fin 7),
      c ≠ 2 ->
      (∀ i : Fin 7, M_cur i 2 = B i 2) ->
      intDet 7 M_cur = intDet 7 (fun i j =>
        if j = c then M_cur i c - B 0 c * B i 2 else M_cur i j) := by
    intro M_cur c hc h2eq
    let idx_p : Nat -> Fin 7 := fun _ => 2
    let coef_p : Nat -> Int := fun _ => B 0 c
    have hs := intDet_sub_col_prefix_invariant 7 c M_cur 1 idx_p coef_p
      (fun s hs => by rw [show s = 0 by omega]; exact hc.symm)
    rw [hs]; congr 1; funext i j
    simp [colPrefixComb, idx_p, coef_p, h2eq i]
  have hstep_lt : ∀ k : Nat, k ≤ 7 ->
      intDet 7 B = intDet 7 (fun i j =>
        if j.val < k ∧ j ≠ 2 then B i j - B 0 j * B i 2 else B i j) := by
    intro k hk
    induction k with
    | zero =>
      congr 1
    | succ k' ih =>
      rw [ih (Nat.le_of_lt hk)]
      let M_k : Fin 7 -> Fin 7 -> Int := fun i j =>
        if j.val < k' ∧ j ≠ 2 then B i j - B 0 j * B i 2 else B i j
      change intDet 7 M_k = _
      by_cases hk2 : k' = 2
      · congr 1; funext i j
        dsimp [M_k]
        by_cases hj2 : j = 2
        · have hf1 : ¬ (j.val < k' ∧ j ≠ 2) := fun h => h.2 hj2
          have hf2 : ¬ (j.val < k' + 1 ∧ j ≠ 2) := fun h => h.2 hj2
          rw [ite_false_of_w10 hf1, ite_false_of_w10 hf2]
        · have hjv2 : j.val ≠ 2 := fun hv => hj2 (Fin.ext hv)
          by_cases hlt : j.val < k'
          · have h1 : j.val < k' ∧ j ≠ 2 := ⟨hlt, hj2⟩
            have h2 : j.val < k' + 1 ∧ j ≠ 2 := ⟨by omega, hj2⟩
            rw [ite_true_of_w10 h1, ite_true_of_w10 h2]
          · have hf1 : ¬ (j.val < k' ∧ j ≠ 2) := fun h => hlt h.1
            have hf2 : ¬ (j.val < k' + 1 ∧ j ≠ 2) := fun h => by have := h.1; omega
            rw [ite_false_of_w10 hf1, ite_false_of_w10 hf2]
      · let c : Fin 7 := ⟨k', hk⟩
        have hc2 : c ≠ 2 := fun h => hk2 (congrArg Fin.val h)
        have hM2 : ∀ i : Fin 7, M_k i 2 = B i 2 := by
          intro i; dsimp [M_k]; rw [ite_false_of_w10 (fun h => h.2 rfl)]
        rw [hcol M_k c hc2 hM2]
        congr 1; funext i j
        by_cases hjc : j = c
        · rw [ite_true_of_w10 hjc, hjc]
          have h1 : ¬ (c.val < k' ∧ c ≠ 2) := by dsimp [c]; omega
          have h2 : c.val < k' + 1 ∧ c ≠ 2 := ⟨by dsimp [c]; omega, hc2⟩
          dsimp [M_k]
          rw [ite_false_of_w10 h1, ite_true_of_w10 h2]
        · rw [ite_false_of_w10 hjc]
          have hjv_ne : j.val ≠ k' := fun hv => hjc (Fin.ext hv)
          dsimp [M_k]
          by_cases hlt : j.val < k' ∧ j ≠ 2
          · have h2 : j.val < k' + 1 ∧ j ≠ 2 := ⟨by omega, hlt.2⟩
            rw [ite_true_of_w10 hlt, ite_true_of_w10 h2]
          · have hf2 : ¬ (j.val < k' + 1 ∧ j ≠ 2) := fun h => hlt ⟨by omega, h.2⟩
            rw [ite_false_of_w10 hlt, ite_false_of_w10 hf2]
  let B_flat : Fin 7 -> Fin 7 -> Int := fun i j =>
    if j = 2 then B i j else B i j - B 0 j * B i 2
  have h7 : intDet 7 B = intDet 7 B_flat := by
    rw [hstep_lt 7 (Nat.le_refl 7)]; congr 1; funext i j
    dsimp [B_flat]
    by_cases hj2 : j = 2
    · rw [ite_false_of_w10 (fun h => h.2 hj2), ite_true_of_w10 hj2]
    · rw [ite_true_of_w10 ⟨j.isLt, hj2⟩, ite_false_of_w10 hj2]
  have hz0 : (⟨0, Nat.zero_lt_succ 6⟩ : Fin 7) = 0 := rfl
  rw [h7, intDet_succ_single_row0 6 B_flat 2, hz0]
  · have hb02 : B_flat 0 2 = 1 := by
      change (if (2 : Fin 7) = 2 then B 0 2 else _) = 1
      rw [ite_true_of_w10 rfl, h02]
    rw [hb02]
    change (if (2 : Nat) % 2 = 0 then (1 : Int) else -1) * 1 * intDet 6 (intSubMat B_flat 2) =
      intDet 6 (intSubMat B_flat 2)
    simp
  · intro j hj2
    rw [hz0]
    change (if j = 2 then B 0 j else B 0 j - B 0 j * B 0 2) = 0
    rw [ite_false_of_w10 hj2, h02, Int.mul_one, Int.sub_self]

def t4u2Mat8_3_5_1 (i j : Fin 8) : Int :=
  match i.val, j.val with
  | 0, 0 => 1 | 0, 1 => 0  | 0, 2 => 0   | 0, 3 => 0   | 0, 4 => 1  | 0, 5 => 0   | 0, 6 => 0    | 0, _ => 0
  | 1, 0 => 1 | 1, 1 => 3  | 1, 2 => 3   | 1, 3 => 1   | 1, 4 => 2  | 1, 5 => 6   | 1, 6 => 6    | 1, _ => 2
  | 2, 0 => 1 | 2, 1 => 5  | 2, 2 => 10  | 2, 3 => 10  | 2, 4 => 3  | 2, 5 => 15  | 2, 6 => 30   | 2, _ => 30
  | 3, 0 => 1 | 3, 1 => 8  | 3, 2 => 28  | 3, 3 => 56  | 3, 4 => 6  | 3, 5 => 48  | 3, 6 => 168  | 3, _ => 336
  | 4, 0 => 1 | 4, 1 => 10 | 4, 2 => 45  | 4, 3 => 120 | 4, 4 => 9  | 4, 5 => 90  | 4, 6 => 405  | 4, _ => 1080
  | 5, 0 => 1 | 5, 1 => 13 | 5, 2 => 78  | 5, 3 => 286 | 5, 4 => 18 | 5, 5 => 234 | 5, 6 => 1404 | 5, _ => 5148
  | 6, 0 => 1 | 6, 1 => 15 | 6, 2 => 105 | 6, 3 => 455 | 6, 4 => 27 | 6, 5 => 405 | 6, 6 => 2835 | 6, _ => 12285
  | _, 0 => 1 | _, 1 => 18 | _, 2 => 153 | _, 3 => 816 | _, 4 => 54 | _, 5 => 972 | _, 6 => 8262 | _, _ => 44064

private theorem t4u2_mat8_3_5_1_eq : laurentTwoBaseT4U2Mat8 3 5 1 = t4u2Mat8_3_5_1 := by
  funext i j; revert i j; decide

def t4u2RedMat6 (i j : Fin 6) : Int :=
  match i.val, j.val with
  | 0, 0 => -25   | 0, 1 => -20   | 0, 2 => -8    | 0, 3 => -45    | 0, 4 => -30   | 0, _ => 10
  | 1, 0 => -160  | 1, 1 => -140  | 1, 2 => -51   | 1, 3 => -288   | 1, 4 => -168  | 1, _ => 224
  | 2, 0 => -350  | 2, 1 => -315  | 2, 2 => -112  | 2, 3 => -630   | 2, 4 => -315  | 2, _ => 840
  | 3, 0 => -845  | 3, 1 => -780  | 3, 2 => -269  | 3, 3 => -1482  | 3, 4 => -312  | 3, _ => 4576
  | 4, 0 => -1350 | 4, 1 => -1260 | 4, 2 => -429  | 4, 3 => -2325  | 4, 4 => 105   | 4, _ => 11375
  | _, 0 => -2430 | _, 1 => -2295 | _, 2 => -763  | _, 3 => -3924  | _, 4 => 3366  | _, _ => 42432

/--
  Theorem W11.2d (`laurent_8x8_twobase_t4u2_congruence_divisibility_and_cone_flip`, `zero custom axioms`):
  `8 × 8` Two-Base Rank-2 Vandermonde `(T = 4, U = 2)` Zero-Gap `(2^K - 3^W)` Congruence,
  Upgraded `(2^u - 1)^8` Confluent Divisibility, Laplace Upper Bound, & Convergent-Cone Sign-Flip (`Branch P3.3`):
  1. **Universal `8 × 8` Two-Base `(2^K - 3^W)` Congruence, `2^u * (2^u - 1)^8` Zero-Gap Divisibility, & Laplace Bound**:
     For ALL `W, K, u ≥ 1` with `3 ^ W < 2 ^ K`:
     - `((2 ^ K - 3 ^ W : Nat) : Int) ∣ (intDet 8 M0_t4u2 - intDet 8 (laurentTwoBaseT4U2Mat8 W K (W * u)))`,
     - `((2 ^ u * (2 ^ u - 1) ^ 8 : Nat) : Int) ∣ intDet 8 M0_t4u2`, AND
     - `∀ B, (∀ i j, (M0_t4u2 i j).natAbs ≤ B j) -> (intDet 8 M0_t4u2).natAbs ≤ 40320 * colBoundProdPrefix 8 B 8`!
  2. **Convergent-Cone Sign-Flip Witness (`LAURENT_TWOBASE_8X8_T4U2_CONE_FLIP_3_5_VS_5_8`)**:
     Unlike `6 × 6` `(T = 3, U = 2)` where `det_6 > 0` holds for ALL `u ≥ 1` across `3^W < 2^K, 3*K ≤ 5*W`,
     on `8 × 8` `(T = 4, U = 2)` at convergent `(W, K) = (3, 5)` (`3^3 < 2^5`, `3 * 5 ≤ 5 * 3`),
     `intDet 8 (laurentTwoBaseT4U2Mat8 3 5 1) = -559794375 < 0`!
-/
theorem laurent_8x8_twobase_t4u2_congruence_divisibility_and_cone_flip :
    (∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 -> u ≥ 1 -> 3 ^ W < 2 ^ K ->
      let M0_t4u2 : Fin 8 -> Fin 8 -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (laurentRowsTwoBase8 i).1 (laurentRowsTwoBase8 i).2
          (laurentColsC42_8 u j).1 (laurentColsC42_8 u j).2 : Int)
      (((2 ^ K - 3 ^ W : Nat) : Int) ∣
        (intDet 8 M0_t4u2 - intDet 8 (laurentTwoBaseT4U2Mat8 W K (W * u)))) ∧
      (((2 ^ u * (2 ^ u - 1) ^ 8 : Nat) : Int) ∣ intDet 8 M0_t4u2) ∧
      (∀ B : Fin 8 -> Nat,
        (∀ (i j : Fin 8), (M0_t4u2 i j).natAbs ≤ B j) ->
        (intDet 8 M0_t4u2).natAbs ≤ 40320 * colBoundProdPrefix 8 B 8)) ∧
    (3 ^ 3 < 2 ^ 5 ∧ 3 * 5 ≤ 5 * 3 ∧
     intDet 8 (laurentTwoBaseT4U2Mat8 3 5 1) = -559794375 ∧
     intDet 8 (laurentTwoBaseT4U2Mat8 3 5 1) < 0) := by
  refine ⟨?_, ?_⟩
  · intro W K u _ _ hu hgt
    dsimp only
    have hdvd_diff := (laurent_wdilated_zero_gap_entry_and_det_congruence.2
      W K 8 laurentRowsTwoBase8 (laurentColsC42_8 u) hgt).1
    have hMW_eq : (fun i j : Fin 8 =>
        (laurentInterpEntry W K (laurentRowsTwoBase8 i).1 (laurentRowsTwoBase8 i).2
          (laurentColsC42_8 u j).1 (W * (laurentColsC42_8 u j).2) : Int)) =
        laurentTwoBaseT4U2Mat8 W K (W * u) := by
      funext i j
      unfold laurentTwoBaseT4U2Mat8 laurentInterpMat laurentColsC42_8
      have hj_c : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨
                  j.val = 4 ∨ j.val = 5 ∨ j.val = 6 ∨ j.val = 7 := by
        have := j.isLt; omega
      rcases hj_c with h | h | h | h | h | h | h | h <;> simp [h]
    rw [hMW_eq] at hdvd_diff
    let idx4 : Nat -> Fin 8 := fun t => if h : t < 8 then ⟨t, h⟩ else ⟨0, by decide⟩
    have hconfl := laurent_universal_single_base_upgraded_confluent_and_laplace_bound.2.2.1
      W K 8 4 u laurentRowsTwoBase8 (laurentColsC42_8 u) idx4 ⟨4, by decide⟩ ⟨5, by decide⟩
      (by decide) hu (by decide)
      (fun t ht => by
        rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl <;> rfl)
      rfl rfl
    refine ⟨hdvd_diff, by simpa using hconfl, ?_⟩
    intro B hB
    have hlap := intDet_natAbs_le_fact_mul_colProd 8 _ B hB
    have hf8 : natFact 8 = 40320 := by decide
    rwa [hf8] at hlap
  · -- Fast 2-step flat pivot reduction `8 × 8 -> 7 × 7 -> 6 × 6` at `(W, K, u) = (3, 5, 1)`:
    let A := t4u2Mat8_3_5_1
    let B7 := intSubMat (fun i j : Fin 8 => if j = 4 then A i 4 - A i 0 else A i j) 0
    have hmat6_eq : intSubMat (fun i j : Fin 7 =>
        if j = 2 then B7 i j else B7 i j - B7 0 j * B7 i 2) 2 = t4u2RedMat6 := by
      funext i j; revert i j; decide
    have hdet6 : intDet 6 t4u2RedMat6 = -559794375 := by decide
    have hdet8_val : intDet 8 (laurentTwoBaseT4U2Mat8 3 5 1) = -559794375 := by
      rw [t4u2_mat8_3_5_1_eq,
          intDet8_two_ones_row0 A (by decide) (by decide) (by decide),
          intDet7_pivot_col2 B7 (by decide), hmat6_eq, hdet6]
    exact ⟨by decide, by decide, hdet8_val, by rw [hdet8_val]; decide⟩


end CollatzFormal
