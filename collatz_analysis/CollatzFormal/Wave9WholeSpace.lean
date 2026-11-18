/-
  CollatzFormal/Wave9WholeSpace.lean
  Wave 9 Whole-Space Mathematical & CS Proof Loop:
  1. Front A — `10/11 -> 11/11` Mixed `(2, 3)` Positive Collatz SRS Dichotomy:
     `3D` Non-Triangular Hofbauer–Waldmann Certificate Tower for `omit R9` (`10/11` rules),
     4-Rule Recurrence (`R2, R5, R7, R9`), Universal Zantema Modular Semantic Labelling
     (`∀ M ≥ 1`) + `M = 2, 2D` Tower Terminating `S9 = all11 \ {R3, R8}`, & Unlabelled `2D`
     Subsequence-Pumping `(M_B0)_{1,1} = 0` + Boundary-Coupled Interior-Lower-Triangular /
     Parikh-Syzygy `∀ k` Tower Obstructions (Branch P4.3)
  2. Front B — Pure-Integer `4 x 4` Single-Base & Two-Base Confluent Schneider–Laurent
     Determinant Closed Forms, `(9, 16, 2)` Resonant Zero vs Odd-`u` & Convergent-Cone
     Non-Vanishing, & Pratt–Lucas Certificates for Coprime-Order Primes `p_3 = 45,661,129`
     (`% 8 = 1`) and `p_4 = 107,889,071` (`% 8 = 7`) + `{1, 3} mod 8` Escape & Joint Floors
     (Branches P3.3 & P3.4)
  3. Front C — Universal `∀ Q ≥ 1` Stateful LSB/MSB Finite-State Automaton & Mealy Transducer
     (Transition-Count) Preimage Impossibility Theorems (Closing All Regular/Automaton
     Berg–Meinardus Weights) & 6th Solvable Cousin `T_diamond6` (`ω^4` 4-Tier Convergence with
     `v_2(3x + 1) = 7` Cone-7 -> Cone-6 -> Cone-5 Cascade) (Branches P1.2 & P5)
  4. Front D — Complete Global `(u_1, q_1)` vs `(u_2, q_2)` Collision Classification Across
     All `CoreWords × Nat`, Universal `∀ k` `mod (2 * 3^k)` Markov Prefix-Memory Annihilation,
     Complete Mod-`18` Markov Bijection Table, & Multi-Step `3^(w - 1 - j)` Fiber
     Equidistribution (Branches P5.3 & P2.2)

  Zero external dependencies (pure Lean 4.35.0 Core), zero `sorry`,
  zero `native_decide`, zero custom `axiom`.
-/

import CollatzFormal.Wave8WholeSpace

namespace CollatzFormal

-- ============================================================================
-- SECTION 1: Front A (Branch P4.3) — `3D` Hofbauer–Waldmann Tower for `omit R9`,
--            4-Rule Recurrence (`R2, R5, R7, R9`), Zantema Modular Semantic
--            Labelling (`∀ M ≥ 1`) Terminating `S9`, & `2D` Pumping Obstruction
-- ============================================================================

/-- `10/11` rule subset omitting only `R9 : [T0, R] -> [B1, R]`. -/
def all11OmitR9List : List (List MixedSRSSym × List MixedSRSSym) :=
  [([.L, .B0], [.L]),
   ([.L, .B1], [.L, .T2]),
   ([.T0, .B0], [.B0, .T0]),
   ([.T0, .B1], [.B1, .T1]),
   ([.T1, .B0], [.B1, .T0]),
   ([.T1, .B1], [.B0, .T2]),
   ([.T2, .B0], [.B0, .T1]),
   ([.T2, .B1], [.B1, .T2]),
   ([.T1, .R], [.B0, .B0, .R]),
   ([.T2, .R], [.B1, .B0, .R])]

/-- Critical 9-rule sub-instance `S9 = all11 \ {R3, R8}` (`{R1, R2, R4, R5, R6, R7, R9, R10, R11}`). -/
def s9RuleList : List (List MixedSRSSym × List MixedSRSSym) :=
  [([.L, .B0], [.L]),
   ([.L, .B1], [.L, .T2]),
   ([.T0, .B1], [.B1, .T1]),
   ([.T1, .B0], [.B1, .T0]),
   ([.T1, .B1], [.B0, .T2]),
   ([.T2, .B0], [.B0, .T1]),
   ([.T0, .R], [.B1, .R]),
   ([.T1, .R], [.B0, .B0, .R]),
   ([.T2, .R], [.B1, .B0, .R])]

-- ----------------------------------------------------------------------------
-- `3D` (`3 x 3`) Executable Hofbauer–Waldmann Certificate & Tower Checker
-- ----------------------------------------------------------------------------

def mk3DAffine (m00 m01 m02 m10 m11 m12 m20 m21 m22 v0 v1 v2 : Nat) : NatAffineDim 3 where
  M i j :=
    match i.val, j.val with
    | 0, 0 => m00 | 0, 1 => m01 | 0, 2 => m02
    | 1, 0 => m10 | 1, 1 => m11 | 1, 2 => m12
    | _, 0 => m20 | _, 1 => m21 | _, _ => m22
  v i :=
    match i.val with
    | 0 => v0 | 1 => v1 | _ => v2

def weakOrients3DBool (A B : NatAffineDim 3) : Bool :=
  let i0 : Fin 3 := ⟨0, by decide⟩
  let i1 : Fin 3 := ⟨1, by decide⟩
  let i2 : Fin 3 := ⟨2, by decide⟩
  decide (A.M i0 i0 ≥ B.M i0 i0) &&
  decide (A.M i0 i1 ≥ B.M i0 i1) &&
  decide (A.M i0 i2 ≥ B.M i0 i2) &&
  decide (A.M i1 i0 ≥ B.M i1 i0) &&
  decide (A.M i1 i1 ≥ B.M i1 i1) &&
  decide (A.M i1 i2 ≥ B.M i1 i2) &&
  decide (A.M i2 i0 ≥ B.M i2 i0) &&
  decide (A.M i2 i1 ≥ B.M i2 i1) &&
  decide (A.M i2 i2 ≥ B.M i2 i2) &&
  decide (A.v i0 ≥ B.v i0) &&
  decide (A.v i1 ≥ B.v i1) &&
  decide (A.v i2 ≥ B.v i2)

theorem weakOrients3DBool_sound (A B : NatAffineDim 3)
    (hb : weakOrients3DBool A B = true) :
    weakOrientsNatAffineDim 3 A B := by
  unfold weakOrients3DBool at hb
  rcases bool_and_split hb with ⟨hb11, hv2⟩
  rcases bool_and_split hb11 with ⟨hb10, hv1⟩
  rcases bool_and_split hb10 with ⟨hb9, hv0⟩
  rcases bool_and_split hb9 with ⟨hb8, hm22⟩
  rcases bool_and_split hb8 with ⟨hb7, hm21⟩
  rcases bool_and_split hb7 with ⟨hb6, hm20⟩
  rcases bool_and_split hb6 with ⟨hb5, hm12⟩
  rcases bool_and_split hb5 with ⟨hb4, hm11⟩
  rcases bool_and_split hb4 with ⟨hb3, hm10⟩
  rcases bool_and_split hb3 with ⟨hb2, hm02⟩
  rcases bool_and_split hb2 with ⟨hm00, hm01⟩
  refine ⟨?_, ?_⟩
  · intro ⟨i, hi⟩ ⟨j, hj⟩
    match i, j with
    | 0, 0 => exact of_decide_eq_true hm00
    | 0, 1 => exact of_decide_eq_true hm01
    | 0, 2 => exact of_decide_eq_true hm02
    | 1, 0 => exact of_decide_eq_true hm10
    | 1, 1 => exact of_decide_eq_true hm11
    | 1, 2 => exact of_decide_eq_true hm12
    | 2, 0 => exact of_decide_eq_true hm20
    | 2, 1 => exact of_decide_eq_true hm21
    | 2, 2 => exact of_decide_eq_true hm22
    | k + 3, _ => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 3 k) hi)
    | _, k + 3 => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 3 k) hj)
  · intro ⟨i, hi⟩
    match i with
    | 0 => exact of_decide_eq_true hv0
    | 1 => exact of_decide_eq_true hv1
    | 2 => exact of_decide_eq_true hv2
    | k + 3 => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 3 k) hi)

def checkTopLeft3DBool (interp : MixedSRSSym -> NatAffineDim 3) : Bool :=
  let z : Fin 3 := ⟨0, by decide⟩
  decide ((interp .L).M z z ≥ 1) &&
  decide ((interp .R).M z z ≥ 1) &&
  decide ((interp .B0).M z z ≥ 1) &&
  decide ((interp .B1).M z z ≥ 1) &&
  decide ((interp .T0).M z z ≥ 1) &&
  decide ((interp .T1).M z z ≥ 1) &&
  decide ((interp .T2).M z z ≥ 1)

theorem checkTopLeft3DBool_sound (interp : MixedSRSSym -> NatAffineDim 3)
    (hb : checkTopLeft3DBool interp = true) :
    ∀ s : MixedSRSSym, (interp s).M ⟨0, by decide⟩ ⟨0, by decide⟩ ≥ 1 := by
  unfold checkTopLeft3DBool at hb
  rcases bool_and_split hb with ⟨hb6, ht2⟩
  rcases bool_and_split hb6 with ⟨hb5, ht1⟩
  rcases bool_and_split hb5 with ⟨hb4, ht0⟩
  rcases bool_and_split hb4 with ⟨hb3, hb1⟩
  rcases bool_and_split hb3 with ⟨hb2, hb0⟩
  rcases bool_and_split hb2 with ⟨hl, hr⟩
  intro s
  cases s with
  | L  => exact of_decide_eq_true hl
  | R  => exact of_decide_eq_true hr
  | B0 => exact of_decide_eq_true hb0
  | B1 => exact of_decide_eq_true hb1
  | T0 => exact of_decide_eq_true ht0
  | T1 => exact of_decide_eq_true ht1
  | T2 => exact of_decide_eq_true ht2

def checkAllWeak3DBool (interp : MixedSRSSym -> NatAffineDim 3) :
    List (List MixedSRSSym × List MixedSRSSym) -> Bool
  | [] => true
  | r :: rs =>
    weakOrients3DBool (evalWordNatAffineDim 3 interp r.1) (evalWordNatAffineDim 3 interp r.2) &&
    checkAllWeak3DBool interp rs

theorem checkAllWeak3DBool_sound (interp : MixedSRSSym -> NatAffineDim 3) :
    ∀ (rules : List (List MixedSRSSym × List MixedSRSSym)),
      checkAllWeak3DBool interp rules = true ->
      ∀ r ∈ rules, weakOrientsNatAffineDim 3
        (evalWordNatAffineDim 3 interp r.1) (evalWordNatAffineDim 3 interp r.2)
  | [], _, _, hm => by cases hm
  | _ :: rs, hb, r, hm => by
    rcases bool_and_split hb with ⟨hw0, hrest⟩
    cases hm with
    | head => exact weakOrients3DBool_sound _ _ hw0
    | tail _ hrs => exact checkAllWeak3DBool_sound interp rs hrest r hrs

def filterUnoriented3D (interp : MixedSRSSym -> NatAffineDim 3) :
    List (List MixedSRSSym × List MixedSRSSym) -> List (List MixedSRSSym × List MixedSRSSym)
  | [] => []
  | r :: rs =>
    match orients3DBool (evalWordNatAffineDim 3 interp r.1) (evalWordNatAffineDim 3 interp r.2) with
    | true => filterUnoriented3D interp rs
    | false => r :: filterUnoriented3D interp rs

theorem mem_filterUnoriented3D_of_not_strict (interp : MixedSRSSym -> NatAffineDim 3) :
    ∀ (rules : List (List MixedSRSSym × List MixedSRSSym))
      (r : List MixedSRSSym × List MixedSRSSym),
      r ∈ rules ->
      ¬ orientsNatAffineDim 3 (by decide)
        (evalWordNatAffineDim 3 interp r.1) (evalWordNatAffineDim 3 interp r.2) ->
      r ∈ filterUnoriented3D interp rules
  | [], _, hm, _ => by cases hm
  | r0 :: rs, r, hm, hns => by
    unfold filterUnoriented3D
    cases hm with
    | head =>
      cases ho : orients3DBool (evalWordNatAffineDim 3 interp r0.1)
          (evalWordNatAffineDim 3 interp r0.2) with
      | true => exact False.elim (hns (orients3DBool_sound _ _ ho))
      | false => exact List.Mem.head _
    | tail _ hrs =>
      cases ho : orients3DBool (evalWordNatAffineDim 3 interp r0.1)
          (evalWordNatAffineDim 3 interp r0.2) with
      | true => exact mem_filterUnoriented3D_of_not_strict interp rs r hrs hns
      | false => exact List.Mem.tail _ (mem_filterUnoriented3D_of_not_strict interp rs r hrs hns)

def check3DHWTowerBool :
    List (MixedSRSSym -> NatAffineDim 3) ->
    List (List MixedSRSSym × List MixedSRSSym) -> Bool
  | [], rules => rules.isEmpty
  | interp :: rest, rules =>
    checkTopLeft3DBool interp &&
    checkAllWeak3DBool interp rules &&
    check3DHWTowerBool rest (filterUnoriented3D interp rules)

theorem check3DHWTowerBool_sound :
    ∀ (levels : List (MixedSRSSym -> NatAffineDim 3))
      (rules : List (List MixedSRSSym × List MixedSRSSym)),
      check3DHWTowerBool levels rules = true ->
      OmegaHofbauerWaldmannTower 3 (by decide) levels.length rules
  | [], [], _ => rfl
  | [], _ :: _, hb => by cases hb
  | interp :: rest, rules, hb => by
    unfold check3DHWTowerBool at hb
    rcases bool_and_split hb with ⟨hb1, hrest⟩
    rcases bool_and_split hb1 with ⟨htop, hweak⟩
    exact Or.inr ⟨filterUnoriented3D interp rules, interp,
      checkTopLeft3DBool_sound interp htop,
      checkAllWeak3DBool_sound interp rules hweak,
      mem_filterUnoriented3D_of_not_strict interp rules,
      check3DHWTowerBool_sound rest _ hrest⟩

-- Explicit 5-level `3 x 3` (`d = 3`) Hofbauer–Waldmann certificate tower for `all11OmitR9List`:

def cert3DOmitR9_L1 : MixedSRSSym -> NatAffineDim 3
  | .L  => mk3DAffine 1 0 0  0 0 0  0 0 0  0 0 0
  | .R  => mk3DAffine 1 0 0  0 0 0  0 0 0  0 0 1
  | .B0 => mk3DAffine 1 0 1  0 0 0  0 0 0  0 0 0
  | .B1 => mk3DAffine 1 0 2  0 0 0  0 0 0  0 0 0
  | .T0 => mk3DAffine 1 0 0  0 0 0  0 0 0  0 0 0
  | .T1 => mk3DAffine 1 0 1  0 0 0  0 0 0  0 0 0
  | .T2 => mk3DAffine 1 0 2  0 0 0  0 0 0  0 0 0

def cert3DOmitR9_L2 : MixedSRSSym -> NatAffineDim 3
  | .L  => mk3DAffine 1 0 0  0 0 0  0 0 0  0 0 0
  | .R  => mk3DAffine 1 0 0  0 0 0  0 0 0  0 1 1
  | .B0 => mk3DAffine 1 0 0  0 0 2  0 0 0  2 1 0
  | .B1 => mk3DAffine 1 1 2  0 0 0  0 0 0  1 1 0
  | .T0 => mk3DAffine 1 0 0  0 0 0  0 0 0  2 1 0
  | .T1 => mk3DAffine 1 0 2  0 1 0  0 0 0  2 0 0
  | .T2 => mk3DAffine 1 1 0  0 0 0  0 0 0  1 1 0

def cert3DOmitR9_L3 : MixedSRSSym -> NatAffineDim 3
  | .L  => mk3DAffine 1 0 0  0 0 0  0 0 0  0 0 0
  | .R  => mk3DAffine 1 0 0  0 0 0  0 0 0  0 0 3
  | .B0 => mk3DAffine 1 0 4  0 0 2  0 0 0  3 0 0
  | .B1 => mk3DAffine 1 1 0  0 0 0  0 0 3  3 0 0
  | .T0 => mk3DAffine 1 0 2  0 0 0  0 0 0  0 0 0
  | .T1 => mk3DAffine 1 0 6  0 0 0  0 0 0  0 0 0
  | .T2 => mk3DAffine 1 1 0  0 0 0  0 0 0  0 0 0

def cert3DOmitR9_L4 : MixedSRSSym -> NatAffineDim 3
  | .L  => mk3DAffine 1 0 0  0 0 0  0 0 0  0 0 0
  | .R  => mk3DAffine 1 0 0  0 0 0  0 0 0  0 0 0
  | .B0 => mk3DAffine 1 0 0  0 0 0  0 0 0  0 0 0
  | .B1 => mk3DAffine 1 0 0  0 0 0  0 0 0  0 0 0
  | .T0 => mk3DAffine 1 0 0  0 0 0  0 0 0  1 0 0
  | .T1 => mk3DAffine 1 0 0  0 0 0  0 0 0  1 0 0
  | .T2 => mk3DAffine 1 0 0  0 0 0  0 0 0  1 0 0

def cert3DOmitR9_L5 : MixedSRSSym -> NatAffineDim 3
  | .L  => mk3DAffine 1 0 0  0 0 0  0 0 0  0 0 0
  | .R  => mk3DAffine 1 0 0  0 0 0  0 0 0  0 0 0
  | .B0 => mk3DAffine 1 0 0  0 0 0  1 0 0  1 0 1
  | .B1 => mk3DAffine 1 0 0  1 0 0  0 0 0  1 1 0
  | .T0 => mk3DAffine 2 0 0  0 5 0  2 0 0  4 0 3
  | .T1 => mk3DAffine 2 0 0  0 0 5  0 4 0  4 0 1
  | .T2 => mk3DAffine 2 0 0  0 2 0  0 0 2  4 3 3

def towerOmitR9_3D : List (MixedSRSSym -> NatAffineDim 3) :=
  [cert3DOmitR9_L1, cert3DOmitR9_L2, cert3DOmitR9_L3, cert3DOmitR9_L4, cert3DOmitR9_L5]

/--
  Theorem W9.1a (`omit_r9_10_of_11_admits_3d_hw_tower`, `[]` axioms):
  Dimension `d = 3` Breaks the `omit R9` `2D` Barrier (`10/11` Rules Terminated):
  `all11OmitR9List` (`10` of the `11` positive Collatz SRS rules, omitting only
  `R9 : [T0, R] -> [B1, R]`) is completely terminated by the explicit 5-level `3 x 3`
  non-triangular Hofbauer–Waldmann tower `towerOmitR9_3D` (entries in `{0..6}`)!
-/
theorem omit_r9_10_of_11_admits_3d_hw_tower :
    all11OmitR9List.length = 10 ∧
    check3DHWTowerBool towerOmitR9_3D all11OmitR9List = true ∧
    OmegaHofbauerWaldmannTower 3 (by decide) 5 all11OmitR9List := by
  have hb : check3DHWTowerBool towerOmitR9_3D all11OmitR9List = true := by decide
  exact ⟨rfl, hb, check3DHWTowerBool_sound towerOmitR9_3D all11OmitR9List hb⟩

theorem all11_mem_or_r9 (r : List MixedSRSSym × List MixedSRSSym)
    (hm : r ∈ all11RuleList) :
    r = ([.T0, .R], [.B1, .R]) ∨ r ∈ all11OmitR9List := by
  revert r hm
  decide

/--
  Theorem W9.1b (`infinite_all11_srs_chain_requires_infinitely_many_r2_r5_r7_r9`, zero custom axioms):
  4-Rule Infinite-Recurrence Theorem Across `all11RuleList`:
  Combining Wave 8's `2D` termination of `omit R2`, `omit R5`, `omit R7` with `W9.1a`'s `3D`
  termination of `omit R9`, EVERY infinite `all11RuleList` rewrite sequence MUST apply ALL FOUR
  rules `R2` (`[L, B1] -> [L, T2]`), `R5` (`[T1, B0] -> [B1, T0]`), `R7` (`[T2, B0] -> [B0, T1]`),
  AND `R9` (`[T0, R] -> [B1, R]`) infinitely many times!
-/
theorem infinite_all11_srs_chain_requires_infinitely_many_r2_r5_r7_r9
    (seq : Nat -> List MixedSRSSym)
    (hinf : ∀ t : Nat, srsStepFromList all11RuleList (seq t) (seq (t + 1)))
    (N : Nat) :
    (∃ t : Nat, t ≥ N ∧ ∃ p q : List MixedSRSSym,
      seq t = p ++ [.L, .B1] ++ q ∧ seq (t + 1) = p ++ [.L, .T2] ++ q) ∧
    (∃ t : Nat, t ≥ N ∧ ∃ p q : List MixedSRSSym,
      seq t = p ++ [.T1, .B0] ++ q ∧ seq (t + 1) = p ++ [.B1, .T0] ++ q) ∧
    (∃ t : Nat, t ≥ N ∧ ∃ p q : List MixedSRSSym,
      seq t = p ++ [.T2, .B0] ++ q ∧ seq (t + 1) = p ++ [.B0, .T1] ++ q) ∧
    (∃ t : Nat, t ≥ N ∧ ∃ p q : List MixedSRSSym,
      seq t = p ++ [.T0, .R] ++ q ∧ seq (t + 1) = p ++ [.B1, .R] ++ q) := by
  rcases infinite_all11_srs_chain_requires_infinitely_many_r2_r5_r7 seq hinf N with
    ⟨hr2, hr5, hr7⟩
  refine ⟨hr2, hr5, hr7, ?_⟩
  apply Classical.byContradiction
  intro hnone
  have htail : ∀ k : Nat, srsStepFromList all11OmitR9List (seq (N + k)) (seq (N + (k + 1))) := by
    intro k
    have hnk : seq (N + (k + 1)) = seq ((N + k) + 1) := by rw [Nat.add_assoc N k 1]
    rw [hnk]
    rcases hinf (N + k) with ⟨p, l, r, q, hmem, hw1, hw2⟩
    cases all11_mem_or_r9 (l, r) hmem with
    | inl heq =>
      have hl : l = [.T0, .R] := congrArg Prod.fst heq
      have hr : r = [.B1, .R] := congrArg Prod.snd heq
      rw [hl] at hw1; rw [hr] at hw2
      exact False.elim (hnone ⟨N + k, Nat.le_add_right N k, p, q, hw1, hw2⟩)
    | inr hsub =>
      exact ⟨p, l, r, q, hsub, hw1, hw2⟩
  exact (hofbauer_waldmann_tower_implies_no_infinite_srs_chain 3 (by decide) 5 all11OmitR9List
    omit_r9_10_of_11_admits_3d_hw_tower.2.2).2 (fun k => seq (N + k)) htail

-- ----------------------------------------------------------------------------
-- Parametric-Alphabet Hofbauer–Waldmann Towers & Zantema Modular Semantic Labelling
-- ----------------------------------------------------------------------------

/-- Single SRS step over a parametric symbol alphabet `α`. -/
def genSRSStep {α : Type} (rules : List (List α × List α)) (w1 w2 : List α) : Prop :=
  ∃ p l r q : List α, (l, r) ∈ rules ∧ w1 = p ++ l ++ q ∧ w2 = p ++ r ++ q

inductive genSRSReaches {α : Type} (rules : List (List α × List α)) :
    List α -> List α -> Prop where
  | refl (w : List α) : genSRSReaches rules w w
  | step {w1 w2 w3 : List α} :
      genSRSStep rules w1 w2 -> genSRSReaches rules w2 w3 -> genSRSReaches rules w1 w3

def genSRSPlus {α : Type} (rules : List (List α × List α)) (w1 w3 : List α) : Prop :=
  ∃ w2 : List α, genSRSStep rules w1 w2 ∧ genSRSReaches rules w2 w3

def evalWordGenAffineDim {α : Type} (d : Nat) (interp : α -> NatAffineDim d) :
    List α -> NatAffineDim d
  | [] => { M := natMatId d, v := fun _ => 0 }
  | s :: rest => compNatAffineDim d (interp s) (evalWordGenAffineDim d interp rest)

def GenOmegaHWTower {α : Type} (d : Nat) (hd : 0 < d) :
    Nat -> List (List α × List α) -> Prop
  | 0, rules => rules = []
  | k + 1, rules =>
    rules = [] ∨
    ∃ (rem : List (List α × List α)) (interp : α -> NatAffineDim d),
      (∀ s : α, (interp s).M ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1) ∧
      (∀ r ∈ rules, weakOrientsNatAffineDim d
        (evalWordGenAffineDim d interp r.1) (evalWordGenAffineDim d interp r.2)) ∧
      (∀ r ∈ rules, ¬ orientsNatAffineDim d hd
        (evalWordGenAffineDim d interp r.1) (evalWordGenAffineDim d interp r.2) -> r ∈ rem) ∧
      GenOmegaHWTower d hd k rem

theorem evalWordGenAffineDim_append {α : Type} (d : Nat) (interp : α -> NatAffineDim d) :
    ∀ (u v : List α),
      (∀ i j : Fin d, (evalWordGenAffineDim d interp (u ++ v)).M i j =
        (compNatAffineDim d (evalWordGenAffineDim d interp u) (evalWordGenAffineDim d interp v)).M i j) ∧
      (∀ i : Fin d, (evalWordGenAffineDim d interp (u ++ v)).v i =
        (compNatAffineDim d (evalWordGenAffineDim d interp u) (evalWordGenAffineDim d interp v)).v i)
  | [], v => by
    refine ⟨?_, ?_⟩
    · intro i j
      simp only [List.nil_append, evalWordGenAffineDim, compNatAffineDim]
      exact (natMatMul_left_id_w5 d _ i j).symm
    · intro i
      simp only [List.nil_append, evalWordGenAffineDim, compNatAffineDim, Nat.add_zero]
      exact (natMatVec_id d _ i).symm
  | s :: u, v => by
    rcases evalWordGenAffineDim_append d interp u v with ⟨hm_uv, hv_uv⟩
    rcases compNatAffineDim_assoc_w8 d (interp s)
      (evalWordGenAffineDim d interp u) (evalWordGenAffineDim d interp v) with ⟨hm_a, hv_a⟩
    refine ⟨?_, ?_⟩
    · intro i j
      simp only [List.cons_append, evalWordGenAffineDim]
      have hc : (compNatAffineDim d (interp s) (evalWordGenAffineDim d interp (u ++ v))).M i j =
          (compNatAffineDim d (interp s)
            (compNatAffineDim d (evalWordGenAffineDim d interp u)
              (evalWordGenAffineDim d interp v))).M i j :=
        natSumPrefix_congr d _ _ (fun k => by rw [hm_uv k j]) d
      exact hc.trans (hm_a i j).symm
    · intro i
      simp only [List.cons_append, evalWordGenAffineDim]
      have hc : (compNatAffineDim d (interp s) (evalWordGenAffineDim d interp (u ++ v))).v i =
          (compNatAffineDim d (interp s)
            (compNatAffineDim d (evalWordGenAffineDim d interp u)
              (evalWordGenAffineDim d interp v))).v i := by
        have hmv : natMatVec d (interp s).M (evalWordGenAffineDim d interp (u ++ v)).v i =
            natMatVec d (interp s).M
              (compNatAffineDim d (evalWordGenAffineDim d interp u)
                (evalWordGenAffineDim d interp v)).v i :=
          natSumPrefix_congr d _ _ (fun k => by rw [hv_uv k]) d
        exact congrArg (· + (interp s).v i) hmv
      exact hc.trans (hv_a i).symm

theorem evalWordGen_topLeft_ge_one {α : Type} (d : Nat) (hd : 0 < d)
    (interp : α -> NatAffineDim d)
    (htop : ∀ s : α, (interp s).M ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1) :
    ∀ u : List α, (evalWordGenAffineDim d interp u).M ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1
  | [] => by simp [evalWordGenAffineDim, natMatId]
  | s :: u => by
    have ih := evalWordGen_topLeft_ge_one d hd interp htop u
    simp only [evalWordGenAffineDim, compNatAffineDim]
    have hge : (interp s).M ⟨0, hd⟩ ⟨0, hd⟩ * (evalWordGenAffineDim d interp u).M ⟨0, hd⟩ ⟨0, hd⟩ ≤
        natMatMul d (interp s).M (evalWordGenAffineDim d interp u).M ⟨0, hd⟩ ⟨0, hd⟩ := by
      have hk : ∀ k : Fin d,
          (if k.val = 0 then (interp s).M ⟨0, hd⟩ ⟨0, hd⟩ * (evalWordGenAffineDim d interp u).M ⟨0, hd⟩ ⟨0, hd⟩ else 0) ≤
            (interp s).M ⟨0, hd⟩ k * (evalWordGenAffineDim d interp u).M k ⟨0, hd⟩ := by
        intro k
        by_cases hk0 : k.val = 0
        · have hkz : k = ⟨0, hd⟩ := Fin.ext hk0
          subst hkz; simp
        · simp [hk0]
      have hsum := natSumPrefix_mono_w5 d _ _ hk d
      rw [natSumPrefix_single d ⟨0, hd⟩ _ d] at hsum
      simp [hd] at hsum
      exact hsum
    exact Nat.le_trans (Nat.mul_le_mul (htop s) ih) hge

theorem gen_hw_context_monotonicity {α : Type}
    (d : Nat) (hd : 0 < d) (interp : α -> NatAffineDim d)
    (htop : ∀ s : α, (interp s).M ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1)
    (p l r q : List α) :
    (weakOrientsNatAffineDim d
      (evalWordGenAffineDim d interp l) (evalWordGenAffineDim d interp r) ->
      weakOrientsNatAffineDim d
        (evalWordGenAffineDim d interp (p ++ l ++ q))
        (evalWordGenAffineDim d interp (p ++ r ++ q))) ∧
    (orientsNatAffineDim d hd
      (evalWordGenAffineDim d interp l) (evalWordGenAffineDim d interp r) ->
      orientsNatAffineDim d hd
        (evalWordGenAffineDim d interp (p ++ l ++ q))
        (evalWordGenAffineDim d interp (p ++ r ++ q))) := by
  let EP := evalWordGenAffineDim d interp p
  let EL := evalWordGenAffineDim d interp l
  let ER := evalWordGenAffineDim d interp r
  let EQ := evalWordGenAffineDim d interp q
  have hrefl_P : weakOrientsNatAffineDim d EP EP := ⟨fun _ _ => Nat.le_refl _, fun _ => Nat.le_refl _⟩
  have hrefl_Q : weakOrientsNatAffineDim d EQ EQ := ⟨fun _ _ => Nat.le_refl _, fun _ => Nat.le_refl _⟩
  rcases evalWordGenAffineDim_append d interp (p ++ l) q with ⟨hm_plq1, hv_plq1⟩
  rcases evalWordGenAffineDim_append d interp p l with ⟨hm_pl, hv_pl⟩
  rcases evalWordGenAffineDim_append d interp (p ++ r) q with ⟨hm_prq1, hv_prq1⟩
  rcases evalWordGenAffineDim_append d interp p r with ⟨hm_pr, hv_pr⟩
  have hweak_ctx : weakOrientsNatAffineDim d EL ER ->
      weakOrientsNatAffineDim d
        (evalWordGenAffineDim d interp (p ++ l ++ q))
        (evalWordGenAffineDim d interp (p ++ r ++ q)) := by
    intro hlr
    have hpl : weakOrientsNatAffineDim d (evalWordGenAffineDim d interp (p ++ l))
        (evalWordGenAffineDim d interp (p ++ r)) := by
      have hc := compNatAffineDim_weak_mono_w8 d EP EP EL ER hrefl_P hlr
      exact ⟨fun i j => by rw [hm_pl i j, hm_pr i j]; exact hc.1 i j,
             fun i => by rw [hv_pl i, hv_pr i]; exact hc.2 i⟩
    have hplq := compNatAffineDim_weak_mono_w8 d _ _ EQ EQ hpl hrefl_Q
    exact ⟨fun i j => by rw [hm_plq1 i j, hm_prq1 i j]; exact hplq.1 i j,
           fun i => by rw [hv_plq1 i, hv_prq1 i]; exact hplq.2 i⟩
  refine ⟨hweak_ctx, ?_⟩
  intro hstrict
  have hw_lr : weakOrientsNatAffineDim d EL ER := ⟨hstrict.1, hstrict.2.1⟩
  rcases hweak_ctx hw_lr with ⟨hm_tot, hv_tot⟩
  refine ⟨hm_tot, hv_tot, ?_⟩
  have hassoc_l : p ++ l ++ q = p ++ (l ++ q) := List.append_assoc p l q
  have hassoc_r : p ++ r ++ q = p ++ (r ++ q) := List.append_assoc p r q
  rcases evalWordGenAffineDim_append d interp p (l ++ q) with ⟨_, hv_p_lq⟩
  rcases evalWordGenAffineDim_append d interp p (r ++ q) with ⟨_, hv_p_rq⟩
  rcases evalWordGenAffineDim_append d interp l q with ⟨_, hv_lq⟩
  rcases evalWordGenAffineDim_append d interp r q with ⟨_, hv_rq⟩
  have hw_lq_rq : ∀ k : Fin d,
      (evalWordGenAffineDim d interp (l ++ q)).v k ≥
        (evalWordGenAffineDim d interp (r ++ q)).v k := by
    intro k
    have hc := (compNatAffineDim_weak_mono_w8 d EL ER EQ EQ hw_lr hrefl_Q).2 k
    rw [hv_lq k, hv_rq k]; exact hc
  have hgt_lq_rq : (evalWordGenAffineDim d interp (l ++ q)).v ⟨0, hd⟩ >
      (evalWordGenAffineDim d interp (r ++ q)).v ⟨0, hd⟩ := by
    rw [hv_lq ⟨0, hd⟩, hv_rq ⟨0, hd⟩]
    simp only [compNatAffineDim]
    have hm_q := natMatVec_mono_mat_w8 d
      (evalWordGenAffineDim d interp l).M
      (evalWordGenAffineDim d interp r).M
      (evalWordGenAffineDim d interp q).v hstrict.1 ⟨0, hd⟩
    have hv0_gt : (evalWordGenAffineDim d interp l).v ⟨0, hd⟩ >
        (evalWordGenAffineDim d interp r).v ⟨0, hd⟩ := hstrict.2.2
    omega
  have hp_top := evalWordGen_topLeft_ge_one d hd interp htop p
  have hmv_gt := natMatVec_strict_top_w8 d hd (evalWordGenAffineDim d interp p).M
    (evalWordGenAffineDim d interp (l ++ q)).v
    (evalWordGenAffineDim d interp (r ++ q)).v
    hp_top hw_lq_rq hgt_lq_rq
  rw [hassoc_l, hassoc_r, hv_p_lq ⟨0, hd⟩, hv_p_rq ⟨0, hd⟩]
  simp only [compNatAffineDim]
  omega

theorem genSRSPlus_preserves_weak_and_rem {α : Type}
    (d : Nat) (hd : 0 < d)
    (rules rem : List (List α × List α))
    (interp : α -> NatAffineDim d)
    (htop : ∀ s : α, (interp s).M ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1)
    (hweak : ∀ r ∈ rules, weakOrientsNatAffineDim d
      (evalWordGenAffineDim d interp r.1) (evalWordGenAffineDim d interp r.2))
    (hkeep : ∀ r ∈ rules, ¬ orientsNatAffineDim d hd
      (evalWordGenAffineDim d interp r.1) (evalWordGenAffineDim d interp r.2) -> r ∈ rem) :
    ∀ w1 w3 : List α,
      genSRSPlus rules w1 w3 ->
      (evalWordGenAffineDim d interp w1).v ⟨0, hd⟩ ≥
        (evalWordGenAffineDim d interp w3).v ⟨0, hd⟩ ∧
      ((evalWordGenAffineDim d interp w1).v ⟨0, hd⟩ =
        (evalWordGenAffineDim d interp w3).v ⟨0, hd⟩ ->
        genSRSPlus rem w1 w3) := by
  have hstep_prop : ∀ w1 w2 : List α,
      genSRSStep rules w1 w2 ->
      (evalWordGenAffineDim d interp w1).v ⟨0, hd⟩ ≥ (evalWordGenAffineDim d interp w2).v ⟨0, hd⟩ ∧
      ((evalWordGenAffineDim d interp w1).v ⟨0, hd⟩ = (evalWordGenAffineDim d interp w2).v ⟨0, hd⟩ ->
        genSRSStep rem w1 w2) := by
    intro w1 w2 ⟨p, l, r, q, hmem, hw1, hw2⟩
    rcases gen_hw_context_monotonicity d hd interp htop p l r q with ⟨hw_c, hs_c⟩
    have hw_step := hw_c (hweak (l, r) hmem)
    rw [← hw1, ← hw2] at hw_step
    refine ⟨hw_step.2 ⟨0, hd⟩, ?_⟩
    intro heq_z
    have hnot_strict : ¬ orientsNatAffineDim d hd
        (evalWordGenAffineDim d interp l) (evalWordGenAffineDim d interp r) := by
      intro hstr
      have hsc := hs_c hstr
      rw [← hw1, ← hw2] at hsc
      have hgt := hsc.2.2
      omega
    exact ⟨p, l, r, q, hkeep (l, r) hmem hnot_strict, hw1, hw2⟩
  have hreach_prop : ∀ w1 w3 : List α,
      genSRSReaches rules w1 w3 ->
      (evalWordGenAffineDim d interp w1).v ⟨0, hd⟩ ≥ (evalWordGenAffineDim d interp w3).v ⟨0, hd⟩ ∧
      ((evalWordGenAffineDim d interp w1).v ⟨0, hd⟩ = (evalWordGenAffineDim d interp w3).v ⟨0, hd⟩ ->
        genSRSReaches rem w1 w3) := by
    intro w1 w3 hr
    induction hr with
    | refl w => exact ⟨Nat.le_refl _, fun _ => .refl w⟩
    | @step a b c hs _ ih =>
      rcases hstep_prop a b hs with ⟨hge1, hrem1⟩
      rcases ih with ⟨hge2, hrem2⟩
      exact ⟨Nat.le_trans hge2 hge1, fun heq => .step (hrem1 (by omega)) (hrem2 (by omega))⟩
  intro w1 w3 ⟨w2, hs12, hr23⟩
  rcases hstep_prop w1 w2 hs12 with ⟨hge1, hrem1⟩
  rcases hreach_prop w2 w3 hr23 with ⟨hge2, hrem2⟩
  exact ⟨Nat.le_trans hge2 hge1, fun heq => ⟨w2, hrem1 (by omega), hrem2 (by omega)⟩⟩

theorem gen_hw_tower_acc_srsPlus {α : Type} (d : Nat) (hd : 0 < d) :
    ∀ (k : Nat) (rules : List (List α × List α)),
      GenOmegaHWTower d hd k rules ->
      ∀ w : List α, Acc (fun w2 w1 => genSRSPlus rules w1 w2) w
  | 0, rules, h0, w => by
    rw [GenOmegaHWTower] at h0; subst h0
    refine Acc.intro w ?_
    intro _ ⟨_, ⟨_, _, _, _, hm, _, _⟩, _⟩; cases hm
  | k + 1, rules, hsucc, w0 => by
    rcases hsucc with rfl | ⟨rem, interp, htop, hweak, hkeep, hrem_tower⟩
    · refine Acc.intro w0 ?_
      intro _ ⟨_, ⟨_, _, _, _, hm, _, _⟩, _⟩; cases hm
    · have hpres := genSRSPlus_preserves_weak_and_rem d hd rules rem interp htop hweak hkeep
      have ih_rem := gen_hw_tower_acc_srsPlus d hd k rem hrem_tower
      have hacc_bound : ∀ (B : Nat) (u : List α),
          (evalWordGenAffineDim d interp u).v ⟨0, hd⟩ ≤ B ->
          Acc (fun w2 w1 => genSRSPlus rules w1 w2) u := by
        intro B
        induction B with
        | zero =>
          intro u hu0
          have hrem_zero : ∀ x : List α,
              Acc (fun w2 w1 => genSRSPlus rem w1 w2) x ->
              (evalWordGenAffineDim d interp x).v ⟨0, hd⟩ = 0 ->
              Acc (fun w2 w1 => genSRSPlus rules w1 w2) x := by
            intro x hacc_x
            induction hacc_x with
            | intro x _ ih_x =>
              intro hx0
              refine Acc.intro x ?_
              intro y hxy
              rcases hpres x y hxy with ⟨hge, hto_rem⟩
              exact ih_x y (hto_rem (by omega)) (by omega)
          exact hrem_zero u (ih_rem u) (by omega)
        | succ B' ihB =>
          intro u huB
          have hrem_B : ∀ x : List α,
              Acc (fun w2 w1 => genSRSPlus rem w1 w2) x ->
              (evalWordGenAffineDim d interp x).v ⟨0, hd⟩ ≤ B' + 1 ->
              Acc (fun w2 w1 => genSRSPlus rules w1 w2) x := by
            intro x hacc_x
            induction hacc_x with
            | intro x _ ih_x =>
              intro hxB
              refine Acc.intro x ?_
              intro y hxy
              rcases hpres x y hxy with ⟨hge, hto_rem⟩
              by_cases hlt : (evalWordGenAffineDim d interp y).v ⟨0, hd⟩ <
                  (evalWordGenAffineDim d interp x).v ⟨0, hd⟩
              · exact ihB y (by omega)
              · exact ih_x y (hto_rem (by omega)) (by omega)
          exact hrem_B u (ih_rem u) huB
      exact hacc_bound ((evalWordGenAffineDim d interp w0).v ⟨0, hd⟩) w0 (Nat.le_refl _)

theorem acc_no_infinite_chain {β : Type} {R : β -> β -> Prop} :
    ∀ x : β, Acc (fun y z => R z y) x -> ∀ f : Nat -> β, f 0 = x -> ¬ (∀ t : Nat, R (f t) (f (t + 1))) := by
  intro x hacc
  induction hacc with
  | intro x _ ih =>
    intro f hf0 hchain
    have h01 : R x (f 1) := by rw [← hf0]; exact hchain 0
    exact ih (f 1) h01 (fun t => f (t + 1)) rfl (fun t => hchain (t + 1))

-- Right-to-left modular Collatz semantic model `collatzSemMod M` (`∀ M ≥ 1`):

def mixedSymIdx : MixedSRSSym -> Nat
  | .L  => 0
  | .R  => 1
  | .B0 => 2
  | .B1 => 3
  | .T0 => 4
  | .T1 => 5
  | .T2 => 6

theorem mixedSymIdx_lt_seven (s : MixedSRSSym) : mixedSymIdx s < 7 := by
  cases s <;> decide

/-- Right-to-left modular semantics of each positive Collatz SRS symbol on `Z / M Z`. -/
def collatzSemMod (M : Nat) (s : MixedSRSSym) (a : Nat) : Nat :=
  match s with
  | .L  => 0
  | .R  => 1 % M
  | .B0 => (2 * a) % M
  | .B1 => (2 * a + 1) % M
  | .T0 => (3 * a) % M
  | .T1 => (3 * a + 1) % M
  | .T2 => (3 * a + 2) % M

def evalCollatzSemWord (M : Nat) : List MixedSRSSym -> Nat -> Nat
  | [], a => a
  | s :: u, a => collatzSemMod M s (evalCollatzSemWord M u a)

theorem collatzSemMod_lt (M : Nat) (hM : M ≥ 1) (s : MixedSRSSym) (a : Nat) (_ha : a < M) :
    collatzSemMod M s a < M := by
  have hpos : 0 < M := hM
  cases s with
  | L  => exact hpos
  | R  => exact Nat.mod_lt _ hpos
  | B0 => exact Nat.mod_lt _ hpos
  | B1 => exact Nat.mod_lt _ hpos
  | T0 => exact Nat.mod_lt _ hpos
  | T1 => exact Nat.mod_lt _ hpos
  | T2 => exact Nat.mod_lt _ hpos

theorem evalCollatzSemWord_lt (M : Nat) (hM : M ≥ 1) :
    ∀ (u : List MixedSRSSym) (a : Nat), a < M -> evalCollatzSemWord M u a < M
  | [], _, ha => ha
  | s :: u, a, ha =>
    collatzSemMod_lt M hM s (evalCollatzSemWord M u a) (evalCollatzSemWord_lt M hM u a ha)

theorem evalCollatzSemWord_append (M : Nat) :
    ∀ (u v : List MixedSRSSym) (a : Nat),
      evalCollatzSemWord M (u ++ v) a = evalCollatzSemWord M u (evalCollatzSemWord M v a)
  | [], _, _ => rfl
  | s :: u, v, a => by
    simp only [List.cons_append, evalCollatzSemWord, evalCollatzSemWord_append M u v a]

/--
  Theorem W9.1c (`collatz_mod_m_is_exact_semantic_model`, choice-free `zero custom axioms`):
  Universal Right-to-Left Modular Semantic Model Across ALL Moduli `M ≥ 1`:
  For EVERY modulus `M ≥ 1`, EVERY rule `r ∈ all11RuleList` (`R1`–`R11`), and EVERY carrier
  state `a < M`, `evalCollatzSemWord M r.1 a = evalCollatzSemWord M r.2 a`!
-/
theorem collatz_mod_m_is_exact_semantic_model (M : Nat) (_hM : M ≥ 1)
    (r : List MixedSRSSym × List MixedSRSSym) (hr : r ∈ all11RuleList)
    (a : Nat) (_ha : a < M) :
    evalCollatzSemWord M r.1 a = evalCollatzSemWord M r.2 a := by
  have hmul_mod_l : ∀ c x y : Nat, (c * (x % M) + y) % M = (c * x + y) % M := by
    intro c x y
    calc
      (c * (x % M) + y) % M
          = ((c * (x % M)) % M + y % M) % M := Nat.add_mod _ _ M
      _ = (((c % M) * ((x % M) % M)) % M + y % M) % M := by rw [Nat.mul_mod c (x % M) M]
      _ = (((c % M) * (x % M)) % M + y % M) % M := by rw [Nat.mod_mod]
      _ = ((c * x) % M + y % M) % M := by rw [← Nat.mul_mod c x M]
      _ = (c * x + y) % M := (Nat.add_mod _ _ M).symm
  have hmul_mod_0 : ∀ c x : Nat, (c * (x % M)) % M = (c * x) % M := by
    intro c x
    have h := hmul_mod_l c x 0
    rw [Nat.add_zero, Nat.add_zero] at h
    exact h
  simp only [all11RuleList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · simp only [evalCollatzSemWord, collatzSemMod]
    rw [hmul_mod_0 3 (2 * a), hmul_mod_0 2 (3 * a),
        show 3 * (2 * a) = 2 * (3 * a) by omega]
  · simp only [evalCollatzSemWord, collatzSemMod]
    rw [hmul_mod_0 3 (2 * a + 1), hmul_mod_l 2 (3 * a + 1) 1,
        show 3 * (2 * a + 1) = 2 * (3 * a + 1) + 1 by omega]
  · simp only [evalCollatzSemWord, collatzSemMod]
    rw [hmul_mod_l 3 (2 * a) 1, hmul_mod_l 2 (3 * a) 1,
        show 3 * (2 * a) + 1 = 2 * (3 * a) + 1 by omega]
  · simp only [evalCollatzSemWord, collatzSemMod]
    rw [hmul_mod_l 3 (2 * a + 1) 1, hmul_mod_0 2 (3 * a + 2),
        show 3 * (2 * a + 1) + 1 = 2 * (3 * a + 2) by omega]
  · simp only [evalCollatzSemWord, collatzSemMod]
    rw [hmul_mod_l 3 (2 * a) 2, hmul_mod_0 2 (3 * a + 1),
        show 3 * (2 * a) + 2 = 2 * (3 * a + 1) by omega]
  · simp only [evalCollatzSemWord, collatzSemMod]
    rw [hmul_mod_l 3 (2 * a + 1) 2, hmul_mod_l 2 (3 * a + 2) 1,
        show 3 * (2 * a + 1) + 2 = 2 * (3 * a + 2) + 1 by omega]
  · simp only [evalCollatzSemWord, collatzSemMod]
    rw [hmul_mod_0 3 1, hmul_mod_l 2 1 1]
  · simp only [evalCollatzSemWord, collatzSemMod]
    calc
      (3 * (1 % M) + 1) % M = (3 * 1 + 1) % M := hmul_mod_l 3 1 1
      _ = (4 * 1) % M := rfl
      _ = (4 * (1 % M)) % M := (hmul_mod_0 4 1).symm
      _ = (2 * (2 * (1 % M))) % M := by rw [show 4 * (1 % M) = 2 * (2 * (1 % M)) by omega]
      _ = (2 * ((2 * (1 % M)) % M)) % M := (hmul_mod_0 2 (2 * (1 % M))).symm
  · simp only [evalCollatzSemWord, collatzSemMod]
    calc
      (3 * (1 % M) + 2) % M = (3 * 1 + 2) % M := hmul_mod_l 3 1 2
      _ = (4 * 1 + 1) % M := rfl
      _ = (4 * (1 % M) + 1) % M := (hmul_mod_l 4 1 1).symm
      _ = (2 * (2 * (1 % M)) + 1) % M := by rw [show 4 * (1 % M) = 2 * (2 * (1 % M)) by omega]
      _ = (2 * ((2 * (1 % M)) % M) + 1) % M := (hmul_mod_l 2 (2 * (1 % M)) 1).symm

-- Right-to-left Zantema word labelling into `Fin (7 * M)`:

def labelCollatzSymIdx (M : Nat) (_hM : M ≥ 1) (s : MixedSRSSym) (a : Nat) (ha : a < M) :
    Fin (7 * M) :=
  ⟨mixedSymIdx s * M + a,
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left ha (mixedSymIdx s * M))
      (Nat.succ_mul (mixedSymIdx s) M ▸ Nat.mul_le_mul_right M (mixedSymIdx_lt_seven s))⟩

def labelCollatzWord (M : Nat) (hM : M ≥ 1) :
    List MixedSRSSym -> (a : Nat) -> a < M -> List (Fin (7 * M))
  | [], _, _ => []
  | s :: u, a, ha =>
    let a_u := evalCollatzSemWord M u a
    have ha_u : a_u < M := evalCollatzSemWord_lt M hM u a ha
    labelCollatzSymIdx M hM s a_u ha_u :: labelCollatzWord M hM u a ha

theorem labelCollatzWord_congr_carrier (M : Nat) (hM : M ≥ 1) (u : List MixedSRSSym)
    (a1 a2 : Nat) (h1 : a1 < M) (h2 : a2 < M) (heq : a1 = a2) :
    labelCollatzWord M hM u a1 h1 = labelCollatzWord M hM u a2 h2 := by
  subst heq
  rfl

theorem labelCollatzWord_append (M : Nat) (hM : M ≥ 1) :
    ∀ (u v : List MixedSRSSym) (a : Nat) (ha : a < M),
      labelCollatzWord M hM (u ++ v) a ha =
        labelCollatzWord M hM u (evalCollatzSemWord M v a)
          (evalCollatzSemWord_lt M hM v a ha) ++
        labelCollatzWord M hM v a ha
  | [], _, _, _ => by simp [labelCollatzWord]
  | s :: u, v, a, ha => by
    simp only [List.cons_append, labelCollatzWord, List.cons.injEq]
    have heq_sem : evalCollatzSemWord M (u ++ v) a =
        evalCollatzSemWord M u (evalCollatzSemWord M v a) :=
      evalCollatzSemWord_append M u v a
    refine ⟨?_, labelCollatzWord_append M hM u v a ha⟩
    apply Fin.ext
    simp only [labelCollatzSymIdx, heq_sem]

def expandRuleAllCarriersAux (M : Nat) (hM : M ≥ 1)
    (l r : List MixedSRSSym) : (k : Nat) -> k ≤ M -> List (List (Fin (7 * M)) × List (Fin (7 * M)))
  | 0, _ => []
  | k + 1, hk =>
    (labelCollatzWord M hM l k hk, labelCollatzWord M hM r k hk) ::
      expandRuleAllCarriersAux M hM l r k (Nat.le_of_lt hk)

def labelledCollatzRules (M : Nat) (hM : M ≥ 1) :
    List (List MixedSRSSym × List MixedSRSSym) -> List (List (Fin (7 * M)) × List (Fin (7 * M)))
  | [] => []
  | (l, r) :: rs =>
    expandRuleAllCarriersAux M hM l r M (Nat.le_refl M) ++ labelledCollatzRules M hM rs

theorem mem_expandRuleAllCarriersAux (M : Nat) (hM : M ≥ 1) (l r : List MixedSRSSym) :
    ∀ (k : Nat) (hk : k ≤ M) (a : Nat) (ha : a < k),
      (labelCollatzWord M hM l a (Nat.lt_of_lt_of_le ha hk),
       labelCollatzWord M hM r a (Nat.lt_of_lt_of_le ha hk)) ∈
        expandRuleAllCarriersAux M hM l r k hk
  | 0, _, _, ha => by omega
  | k + 1, hk, a, ha => by
    simp only [expandRuleAllCarriersAux, List.mem_cons]
    by_cases hak : a = k
    · subst hak; exact Or.inl rfl
    · exact Or.inr (mem_expandRuleAllCarriersAux M hM l r k (by omega) a (by omega))

theorem mem_labelledCollatzRules (M : Nat) (hM : M ≥ 1) :
    ∀ (rules : List (List MixedSRSSym × List MixedSRSSym))
      (l r : List MixedSRSSym) (a : Nat) (ha : a < M),
      (l, r) ∈ rules ->
      (labelCollatzWord M hM l a ha, labelCollatzWord M hM r a ha) ∈
        labelledCollatzRules M hM rules
  | [], _, _, _, _, hm => by cases hm
  | (l0, r0) :: rs, l, r, a, ha, hm => by
    simp only [labelledCollatzRules, List.mem_append]
    cases hm with
    | head =>
      exact Or.inl (mem_expandRuleAllCarriersAux M hM l0 r0 M (Nat.le_refl M) a ha)
    | tail _ hrs =>
      exact Or.inr (mem_labelledCollatzRules M hM rs l r a ha hrs)

theorem zantema_step_lifts_to_labelled (M : Nat) (hM : M ≥ 1)
    (rules : List (List MixedSRSSym × List MixedSRSSym))
    (hsem : ∀ r ∈ rules, ∀ a : Nat, a < M ->
      evalCollatzSemWord M r.1 a = evalCollatzSemWord M r.2 a) :
    (∀ w1 w2 : List MixedSRSSym,
      srsStepFromList rules w1 w2 ->
      evalCollatzSemWord M w1 0 = evalCollatzSemWord M w2 0 ∧
      genSRSStep (labelledCollatzRules M hM rules)
        (labelCollatzWord M hM w1 0 hM) (labelCollatzWord M hM w2 0 hM)) ∧
    (∀ w1 w3 : List MixedSRSSym,
      srsPlusFromList rules w1 w3 ->
      genSRSPlus (labelledCollatzRules M hM rules)
        (labelCollatzWord M hM w1 0 hM) (labelCollatzWord M hM w3 0 hM)) := by
  have hstep : ∀ w1 w2 : List MixedSRSSym,
      srsStepFromList rules w1 w2 ->
      (∀ a : Nat, a < M -> evalCollatzSemWord M w1 a = evalCollatzSemWord M w2 a) ∧
      genSRSStep (labelledCollatzRules M hM rules)
        (labelCollatzWord M hM w1 0 hM) (labelCollatzWord M hM w2 0 hM) := by
    intro w1 w2 ⟨p, l, r, q, hmem, hw1, hw2⟩
    have ha_q : evalCollatzSemWord M q 0 < M := evalCollatzSemWord_lt M hM q 0 hM
    have hlr_eq : ∀ a : Nat, a < M ->
        evalCollatzSemWord M (p ++ l ++ q) a = evalCollatzSemWord M (p ++ r ++ q) a := by
      intro a ha
      rw [List.append_assoc p l q, List.append_assoc p r q,
          evalCollatzSemWord_append M p (l ++ q) a,
          evalCollatzSemWord_append M p (r ++ q) a,
          evalCollatzSemWord_append M l q a,
          evalCollatzSemWord_append M r q a,
          hsem (l, r) hmem (evalCollatzSemWord M q a) (evalCollatzSemWord_lt M hM q a ha)]
    refine ⟨fun a ha => by rw [hw1, hw2]; exact hlr_eq a ha, ?_⟩
    let aq := evalCollatzSemWord M q 0
    have hlq_eq : evalCollatzSemWord M (l ++ q) 0 = evalCollatzSemWord M (r ++ q) 0 := by
      rw [evalCollatzSemWord_append M l q 0, evalCollatzSemWord_append M r q 0]
      exact hsem (l, r) hmem aq ha_q
    have hlab1 : labelCollatzWord M hM (p ++ l ++ q) 0 hM =
        labelCollatzWord M hM p (evalCollatzSemWord M (l ++ q) 0)
          (evalCollatzSemWord_lt M hM (l ++ q) 0 hM) ++
        labelCollatzWord M hM l aq ha_q ++
        labelCollatzWord M hM q 0 hM := by
      rw [List.append_assoc p l q,
          labelCollatzWord_append M hM p (l ++ q) 0 hM,
          labelCollatzWord_append M hM l q 0 hM,
          ← List.append_assoc]
    have hlab2 : labelCollatzWord M hM (p ++ r ++ q) 0 hM =
        labelCollatzWord M hM p (evalCollatzSemWord M (l ++ q) 0)
          (evalCollatzSemWord_lt M hM (l ++ q) 0 hM) ++
        labelCollatzWord M hM r aq ha_q ++
        labelCollatzWord M hM q 0 hM := by
      rw [List.append_assoc p r q,
          labelCollatzWord_append M hM p (r ++ q) 0 hM,
          labelCollatzWord_append M hM r q 0 hM,
          ← List.append_assoc,
          labelCollatzWord_congr_carrier M hM p
            (evalCollatzSemWord M (r ++ q) 0)
            (evalCollatzSemWord M (l ++ q) 0)
            (evalCollatzSemWord_lt M hM (r ++ q) 0 hM)
            (evalCollatzSemWord_lt M hM (l ++ q) 0 hM)
            hlq_eq.symm]
    refine ⟨labelCollatzWord M hM p (evalCollatzSemWord M (l ++ q) 0)
              (evalCollatzSemWord_lt M hM (l ++ q) 0 hM),
            labelCollatzWord M hM l aq ha_q,
            labelCollatzWord M hM r aq ha_q,
            labelCollatzWord M hM q 0 hM,
            mem_labelledCollatzRules M hM rules l r aq ha_q hmem,
            by rw [hw1]; exact hlab1,
            by rw [hw2]; exact hlab2⟩
  have hreach : ∀ w1 w3 : List MixedSRSSym,
      srsReachesFromList rules w1 w3 ->
      genSRSReaches (labelledCollatzRules M hM rules)
        (labelCollatzWord M hM w1 0 hM) (labelCollatzWord M hM w3 0 hM) := by
    intro w1 w3 hr
    induction hr with
    | refl _ => exact .refl _
    | step hs _ ih => exact .step (hstep _ _ hs).2 ih
  refine ⟨fun w1 w2 hs => ⟨(hstep w1 w2 hs).1 0 hM, (hstep w1 w2 hs).2⟩, ?_⟩
  intro w1 w3 ⟨w2, hs12, hr23⟩
  exact ⟨labelCollatzWord M hM w2 0 hM, (hstep w1 w2 hs12).2, hreach w2 w3 hr23⟩

/--
  Theorem W9.1d (`zantema_semantic_labelling_soundness`, `zero custom axioms`):
  Universal Zantema Modular Semantic Labelling Soundness (`∀ M ≥ 1, ∀ d ≥ 1, ∀ k : Nat`):
  1. For ANY sub-SRS `rules` preserved by `evalCollatzSemWord M` (including EVERY subset of
     `all11RuleList` by `W9.1c`), any `d`-dimensional `k`-level Hofbauer–Waldmann tower
     orienting `labelledCollatzRules M hM rules` unconditionally rules out infinite
     `srsPlusFromList rules` and `srsStepFromList rules` rewrite chains!
  2. In particular, any Zantema mod-`M` Hofbauer–Waldmann tower for `all11RuleList`
     unconditionally implies `CollatzConjectureStandard`!
-/
theorem zantema_semantic_labelling_soundness
    (M : Nat) (hM : M ≥ 1) (d : Nat) (hd : 0 < d) (k : Nat) :
    (∀ (rules : List (List MixedSRSSym × List MixedSRSSym)),
      (∀ r ∈ rules, ∀ a : Nat, a < M ->
        evalCollatzSemWord M r.1 a = evalCollatzSemWord M r.2 a) ->
      GenOmegaHWTower d hd k (labelledCollatzRules M hM rules) ->
      (∀ seq : Nat -> List MixedSRSSym,
        ¬ (∀ t : Nat, srsPlusFromList rules (seq t) (seq (t + 1)))) ∧
      (∀ seq : Nat -> List MixedSRSSym,
        ¬ (∀ t : Nat, srsStepFromList rules (seq t) (seq (t + 1))))) ∧
    (GenOmegaHWTower d hd k (labelledCollatzRules M hM all11RuleList) ->
      CollatzConjectureStandard) := by
  refine ⟨?_, ?_⟩
  · intro rules hsem htower
    have hlift := (zantema_step_lifts_to_labelled M hM rules hsem).2
    have hno_plus : ∀ seq : Nat -> List MixedSRSSym,
        ¬ (∀ t : Nat, srsPlusFromList rules (seq t) (seq (t + 1))) := by
      intro seq hchain
      let lseq : Nat -> List (Fin (7 * M)) := fun t => labelCollatzWord M hM (seq t) 0 hM
      exact acc_no_infinite_chain (lseq 0)
        (gen_hw_tower_acc_srsPlus d hd k _ htower (lseq 0))
        lseq rfl (fun t => hlift (seq t) (seq (t + 1)) (hchain t))
    exact ⟨hno_plus, fun seq hstep => hno_plus seq (fun t => ⟨seq (t + 1), hstep t, .refl _⟩)⟩
  · intro htower_all
    rw [collatz_standard_iff_compressed]
    intro n hn
    have hsem_all := fun r hr a ha => collatz_mod_m_is_exact_semantic_model M hM r hr a ha
    have hlift := (zantema_step_lifts_to_labelled M hM all11RuleList hsem_all).2
    have hstep_pos : ∀ m : Nat, m ≥ 1 -> collatzStep m ≥ 1 := by
      intro m hm
      by_cases he : (m % 2 == 0) = true
      · have hm2 : m % 2 = 0 := of_decide_eq_true he
        simp only [collatzStep, he, ite_true]; omega
      · have hne : ¬ (m % 2 = 0) := fun h => he (decide_eq_true h)
        have hef : (m % 2 == 0) = false := decide_eq_false (by omega)
        simp only [collatzStep, hef, Bool.false_eq_true, ite_false]; omega
    let encL : Nat -> List (Fin (7 * M)) :=
      fun m => labelCollatzWord M hM ([.L] ++ encodePosBin m ++ [.R]) 0 hM
    have hacc_enc : ∀ lw : List (Fin (7 * M)),
        Acc (fun w2 w1 => genSRSPlus (labelledCollatzRules M hM all11RuleList) w1 w2) lw ->
        ∀ m : Nat, m ≥ 1 -> encL m = lw -> ∃ t : Nat, collatzIter t m = 1 := by
      intro lw hacc
      induction hacc with
      | intro lw _ ih =>
        intro m hm1 hmlw
        by_cases hm_eq1 : m = 1
        · subst hm_eq1; exact ⟨0, rfl⟩
        · have hplus_unlab := encodePosBin_simulates_srsPlus_all11 m (by omega)
          have hplus_lab : genSRSPlus (labelledCollatzRules M hM all11RuleList)
              lw (encL (collatzStep m)) := by
            rw [← hmlw]
            exact hlift _ _ hplus_unlab
          rcases ih (encL (collatzStep m)) hplus_lab (collatzStep m) (hstep_pos m hm1) rfl with ⟨t, ht⟩
          exact ⟨t + 1, ht⟩
    exact hacc_enc (encL n)
      (gen_hw_tower_acc_srsPlus d hd k _ htower_all (encL n)) n hn rfl

-- Executable `2D` checker over `Fin N` for `M = 2` (`N = 14`) semantic-labelling tower on `S9`:

def checkTopLeftFin2DBool (N : Nat) (interp : Fin N -> NatAffineDim 2) :
    (k : Nat) -> k ≤ N -> Bool
  | 0, _ => true
  | k + 1, hk =>
    decide ((interp ⟨k, hk⟩).M ⟨0, by decide⟩ ⟨0, by decide⟩ ≥ 1) &&
    checkTopLeftFin2DBool N interp k (Nat.le_of_lt hk)

theorem checkTopLeftFin2DBool_sound (N : Nat) (interp : Fin N -> NatAffineDim 2) :
    ∀ (m : Nat) (hm : m ≤ N),
      checkTopLeftFin2DBool N interp m hm = true ->
      ∀ (s : Fin N), s.val < m -> (interp s).M ⟨0, by decide⟩ ⟨0, by decide⟩ ≥ 1
  | 0, _, _, _, hs => False.elim (Nat.not_lt_zero _ hs)
  | m + 1, hm, hb, s, hs => by
    unfold checkTopLeftFin2DBool at hb
    rcases bool_and_split hb with ⟨hm_cur, hrest⟩
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hs) with hsm | hslt
    · have hsf : s = ⟨m, hm⟩ := Fin.ext hsm
      exact hsf.symm ▸ of_decide_eq_true hm_cur
    · exact checkTopLeftFin2DBool_sound N interp m (Nat.le_of_lt hm) hrest s hslt

def checkAllWeakGen2DBool {α : Type} (interp : α -> NatAffineDim 2) :
    List (List α × List α) -> Bool
  | [] => true
  | r :: rs =>
    weakOrients2DBool (evalWordGenAffineDim 2 interp r.1) (evalWordGenAffineDim 2 interp r.2) &&
    checkAllWeakGen2DBool interp rs

theorem checkAllWeakGen2DBool_sound {α : Type} (interp : α -> NatAffineDim 2) :
    ∀ (rules : List (List α × List α)),
      checkAllWeakGen2DBool interp rules = true ->
      ∀ r ∈ rules, weakOrientsNatAffineDim 2
        (evalWordGenAffineDim 2 interp r.1) (evalWordGenAffineDim 2 interp r.2)
  | [], _, _, hm => by cases hm
  | _ :: rs, hb, r, hm => by
    rcases bool_and_split hb with ⟨hw0, hrest⟩
    cases hm with
    | head => exact weakOrients2DBool_sound _ _ hw0
    | tail _ hrs => exact checkAllWeakGen2DBool_sound interp rs hrest r hrs

def filterUnorientedGen2D {α : Type} (interp : α -> NatAffineDim 2) :
    List (List α × List α) -> List (List α × List α)
  | [] => []
  | r :: rs =>
    match orients2DBool (evalWordGenAffineDim 2 interp r.1) (evalWordGenAffineDim 2 interp r.2) with
    | true => filterUnorientedGen2D interp rs
    | false => r :: filterUnorientedGen2D interp rs

theorem mem_filterUnorientedGen2D_of_not_strict {α : Type} (interp : α -> NatAffineDim 2) :
    ∀ (rules : List (List α × List α)) (r : List α × List α),
      r ∈ rules ->
      ¬ orientsNatAffineDim 2 (by decide)
        (evalWordGenAffineDim 2 interp r.1) (evalWordGenAffineDim 2 interp r.2) ->
      r ∈ filterUnorientedGen2D interp rules
  | [], _, hm, _ => by cases hm
  | r0 :: rs, r, hm, hns => by
    unfold filterUnorientedGen2D
    cases hm with
    | head =>
      cases ho : orients2DBool (evalWordGenAffineDim 2 interp r0.1)
          (evalWordGenAffineDim 2 interp r0.2) with
      | true => exact False.elim (hns (orients2DBool_sound _ _ ho))
      | false => exact List.Mem.head _
    | tail _ hrs =>
      cases ho : orients2DBool (evalWordGenAffineDim 2 interp r0.1)
          (evalWordGenAffineDim 2 interp r0.2) with
      | true => exact mem_filterUnorientedGen2D_of_not_strict interp rs r hrs hns
      | false => exact List.Mem.tail _ (mem_filterUnorientedGen2D_of_not_strict interp rs r hrs hns)

def checkFin2DHWTowerBool (N : Nat) :
    List (Fin N -> NatAffineDim 2) -> List (List (Fin N) × List (Fin N)) -> Bool
  | [], rules => rules.isEmpty
  | interp :: rest, rules =>
    checkTopLeftFin2DBool N interp N (Nat.le_refl N) &&
    checkAllWeakGen2DBool interp rules &&
    checkFin2DHWTowerBool N rest (filterUnorientedGen2D interp rules)

theorem checkFin2DHWTowerBool_sound (N : Nat) :
    ∀ (levels : List (Fin N -> NatAffineDim 2))
      (rules : List (List (Fin N) × List (Fin N))),
      checkFin2DHWTowerBool N levels rules = true ->
      GenOmegaHWTower 2 (by decide) levels.length rules
  | [], [], _ => rfl
  | [], _ :: _, hb => by cases hb
  | interp :: rest, rules, hb => by
    unfold checkFin2DHWTowerBool at hb
    rcases bool_and_split hb with ⟨hb1, hrest⟩
    rcases bool_and_split hb1 with ⟨htop, hweak⟩
    exact Or.inr ⟨filterUnorientedGen2D interp rules, interp,
      fun s => checkTopLeftFin2DBool_sound N interp N (Nat.le_refl N) htop s s.isLt,
      checkAllWeakGen2DBool_sound interp rules hweak,
      mem_filterUnorientedGen2D_of_not_strict interp rules,
      checkFin2DHWTowerBool_sound N rest _ hrest⟩

-- Explicit 7-level `2 x 2` (`d = 2`) Zantema `M = 2` certificate tower terminating `s9RuleList`:

def mk2DAffineW9 (a b c d x y : Nat) : NatAffineDim 2 where
  M i j :=
    match i.val, j.val with
    | 0, 0 => a | 0, _ => b | _, 0 => c | _, _ => d
  v i :=
    match i.val with
    | 0 => x | _ => y

def certS9Mod2_L1 (s : Fin 14) : NatAffineDim 2 :=
  match s.val with
  | 0  => mk2DAffineW9 1 0 0 0 2 0 | 1  => mk2DAffineW9 1 0 0 0 2 0
  | 2  => mk2DAffineW9 1 0 0 0 1 0 | 3  => mk2DAffineW9 1 0 0 0 1 0
  | 4  => mk2DAffineW9 1 0 1 0 0 1 | 5  => mk2DAffineW9 1 0 0 0 0 0
  | 6  => mk2DAffineW9 1 1 0 0 1 0 | 7  => mk2DAffineW9 1 0 0 0 1 0
  | 8  => mk2DAffineW9 1 0 0 0 0 0 | 9  => mk2DAffineW9 2 0 0 0 1 0
  | 10 => mk2DAffineW9 2 0 0 0 2 0 | 11 => mk2DAffineW9 1 0 1 0 0 1
  | 12 => mk2DAffineW9 1 1 1 0 1 1 | _  => mk2DAffineW9 1 0 0 0 1 0

def certS9Mod2_L2 (s : Fin 14) : NatAffineDim 2 :=
  match s.val with
  | 0  => mk2DAffineW9 1 0 0 0 1 0 | 1  => mk2DAffineW9 1 0 0 0 1 0
  | 2  => mk2DAffineW9 1 0 0 0 0 0 | 3  => mk2DAffineW9 1 0 0 0 0 0
  | 4  => mk2DAffineW9 2 0 0 0 0 0 | 5  => mk2DAffineW9 1 0 0 0 0 0
  | 6  => mk2DAffineW9 1 0 0 0 1 0 | 7  => mk2DAffineW9 1 0 0 0 1 0
  | 8  => mk2DAffineW9 1 0 0 0 0 0 | 9  => mk2DAffineW9 2 0 0 0 0 0
  | 10 => mk2DAffineW9 2 0 0 0 1 0 | 11 => mk2DAffineW9 2 0 0 0 0 0
  | 12 => mk2DAffineW9 1 0 0 0 1 0 | _  => mk2DAffineW9 1 0 0 0 1 0

def certS9Mod2_L3 (s : Fin 14) : NatAffineDim 2 :=
  match s.val with
  | 0  => mk2DAffineW9 1 0 0 0 0 1 | 1  => mk2DAffineW9 1 0 0 0 0 1
  | 2  => mk2DAffineW9 1 0 0 0 0 0 | 3  => mk2DAffineW9 1 0 0 0 0 0
  | 4  => mk2DAffineW9 2 0 0 0 1 0 | 5  => mk2DAffineW9 1 0 0 0 0 0
  | 6  => mk2DAffineW9 1 0 0 0 0 0 | 7  => mk2DAffineW9 1 0 0 0 0 0
  | 8  => mk2DAffineW9 1 0 0 0 0 0 | 9  => mk2DAffineW9 2 0 0 0 0 0
  | 10 => mk2DAffineW9 2 0 0 0 0 0 | 11 => mk2DAffineW9 2 0 0 0 2 0
  | 12 => mk2DAffineW9 1 0 0 0 0 0 | _  => mk2DAffineW9 1 0 0 0 0 0

def certS9Mod2_L4 (s : Fin 14) : NatAffineDim 2 :=
  match s.val with
  | 0  => mk2DAffineW9 1 0 2 0 0 0 | 1  => mk2DAffineW9 1 0 2 0 0 0
  | 2  => mk2DAffineW9 1 0 0 0 0 0 | 3  => mk2DAffineW9 1 0 0 0 0 0
  | 4  => mk2DAffineW9 1 0 0 0 0 0 | 5  => mk2DAffineW9 1 0 0 0 1 0
  | 6  => mk2DAffineW9 1 0 0 0 1 0 | 7  => mk2DAffineW9 1 0 0 0 2 0
  | 8  => mk2DAffineW9 1 0 0 0 0 0 | 9  => mk2DAffineW9 2 0 0 0 1 0
  | 10 => mk2DAffineW9 2 0 0 0 1 0 | 11 => mk2DAffineW9 1 0 0 0 0 0
  | 12 => mk2DAffineW9 1 0 0 0 0 0 | _  => mk2DAffineW9 1 0 0 0 2 0

def certS9Mod2_L5 (s : Fin 14) : NatAffineDim 2 :=
  match s.val with
  | 0  => mk2DAffineW9 1 0 0 0 0 0 | 1  => mk2DAffineW9 1 2 0 0 0 0
  | 2  => mk2DAffineW9 1 0 0 0 0 0 | 3  => mk2DAffineW9 1 0 0 0 0 0
  | 4  => mk2DAffineW9 1 0 0 0 0 0 | 5  => mk2DAffineW9 1 0 0 0 1 1
  | 6  => mk2DAffineW9 1 2 0 0 0 0 | 7  => mk2DAffineW9 1 0 0 0 1 1
  | 8  => mk2DAffineW9 1 0 0 0 0 0 | 9  => mk2DAffineW9 1 0 0 0 2 1
  | 10 => mk2DAffineW9 1 2 0 1 1 0 | 11 => mk2DAffineW9 1 0 0 0 0 0
  | 12 => mk2DAffineW9 1 0 0 0 0 0 | _  => mk2DAffineW9 1 0 0 0 3 0

def certS9Mod2_L6 (s : Fin 14) : NatAffineDim 2 :=
  match s.val with
  | 6  => mk2DAffineW9 1 0 0 0 1 0 | 7  => mk2DAffineW9 1 0 0 0 2 0
  | 9  => mk2DAffineW9 3 0 0 0 0 0 | 13 => mk2DAffineW9 1 0 0 0 2 0
  | _  => mk2DAffineW9 1 0 0 0 0 0

def certS9Mod2_L7 (s : Fin 14) : NatAffineDim 2 :=
  match s.val with
  | 7 => mk2DAffineW9 1 0 0 0 1 0
  | _ => mk2DAffineW9 1 0 0 0 0 0

def towerS9Mod2_2D : List (Fin 14 -> NatAffineDim 2) :=
  [certS9Mod2_L1, certS9Mod2_L2, certS9Mod2_L3, certS9Mod2_L4,
   certS9Mod2_L5, certS9Mod2_L6, certS9Mod2_L7]

/--
  Theorem W9.1e (`s9_mod2_labelled_admits_2d_hw_tower`, `[]` axioms):
  `M = 2` Parity Semantic Labelling Breaks the `S9 = all11 \ {R3, R8}` `2D` Stall:
  Labelling `s9RuleList` (`9` rules, `18` parity-labelled rules over `14` symbols) by
  `collatzSemMod 2` yields an explicit 7-level `2 x 2` (`d = 2`) Hofbauer–Waldmann tower
  `towerS9Mod2_2D` (entries in `{0..3}`) terminating ALL 18 rules!
-/
theorem s9_mod2_labelled_admits_2d_hw_tower :
    s9RuleList.length = 9 ∧
    (labelledCollatzRules 2 (by decide) s9RuleList).length = 18 ∧
    checkFin2DHWTowerBool 14 towerS9Mod2_2D (labelledCollatzRules 2 (by decide) s9RuleList) = true ∧
    GenOmegaHWTower 2 (by decide) 7 (labelledCollatzRules 2 (by decide) s9RuleList) := by
  have hb : checkFin2DHWTowerBool 14 towerS9Mod2_2D
      (labelledCollatzRules 2 (by decide) s9RuleList) = true := by decide
  exact ⟨rfl, rfl, hb,
    checkFin2DHWTowerBool_sound 14 towerS9Mod2_2D
      (labelledCollatzRules 2 (by decide) s9RuleList) hb⟩

theorem s9_sub_all11 (r : List MixedSRSSym × List MixedSRSSym)
    (hm : r ∈ s9RuleList) : r ∈ all11RuleList := by
  revert r hm; decide

/--
  Theorem W9.1e' (`no_infinite_s9_srs_chain`, `zero custom axioms`):
  Unconditional Termination of `S9 = all11 \ {R3, R8}`:
  `s9RuleList` admits NO infinite `srsPlusFromList` or `srsStepFromList` rewrite sequence!
-/
theorem no_infinite_s9_srs_chain :
    (∀ seq : Nat -> List MixedSRSSym,
      ¬ (∀ t : Nat, srsPlusFromList s9RuleList (seq t) (seq (t + 1)))) ∧
    (∀ seq : Nat -> List MixedSRSSym,
      ¬ (∀ t : Nat, srsStepFromList s9RuleList (seq t) (seq (t + 1)))) :=
  (zantema_semantic_labelling_soundness 2 (by decide) 2 (by decide) 7).1
    s9RuleList
    (fun r hr a ha => collatz_mod_m_is_exact_semantic_model 2 (by decide) r (s9_sub_all11 r hr) a ha)
    s9_mod2_labelled_admits_2d_hw_tower.2.2.2

-- Unlabelled `d = 2` Subsequence-Pumping & Zero-Diagonal / Lower-Triangular Obstruction on `S9`:

theorem evalWordNatAffineDim_singleton_eq (d : Nat) (interp : MixedSRSSym -> NatAffineDim d)
    (s : MixedSRSSym) :
    (∀ i j : Fin d, (evalWordNatAffineDim d interp [s]).M i j = (interp s).M i j) ∧
    (∀ i : Fin d, (evalWordNatAffineDim d interp [s]).v i = (interp s).v i) := by
  refine ⟨?_, ?_⟩
  · intro i j
    simp only [evalWordNatAffineDim, compNatAffineDim, natMatMul, natSumFin, natMatId]
    have hcong : natSumPrefix d (fun p => (interp s).M i p * (if p.val = j.val then 1 else 0)) d =
        natSumPrefix d (fun p => if p.val = j.val then (interp s).M i j else 0) d := by
      apply natSumPrefix_congr d; intro p
      by_cases hpj : p.val = j.val
      · have hpe : p = j := Fin.ext hpj; subst hpe; simp
      · simp [hpj]
    rw [hcong, natSumPrefix_single d j ((interp s).M i j) d]
    simp [j.isLt]
  · intro i
    simp only [evalWordNatAffineDim, compNatAffineDim]
    have hz : natMatVec d (interp s).M (fun _ => 0) i = 0 := by
      unfold natMatVec natSumFin
      have hc := natSumPrefix_congr d (fun k => (interp s).M i k * 0) (fun _ => 0)
        (fun k => Nat.mul_zero _) d
      exact hc.trans (natSumPrefix_zero_w6 d d)
    rw [hz, Nat.zero_add]

/--
  Theorem W9.1f (`s9_subseq_pumping_and_d2_zero_diag_obstruction`, `zero custom axioms`):
  Algebraic Subsequence-Pumping & Unlabelled `2D` Zero-Diagonal / Triangular Obstruction on `S9`:
  1. `s9RuleList` generates the 2-step right-expansion loops
     `[L, B1, R] ->+ [L, B1, B0, R]` (`R2 ; R11`) and
     `[L, T2, R] ->+ [L, T2, B0, R]` (`R11 ; R2`), plus
     `[L, B1, B0, B0, R] ->+ [L, B1, B1, R]` and `[L, B1, B0, R] ->+ [L, R]`!
  2. Under ANY unlabelled `2D` (`d = 2`) Hofbauer–Waldmann interpretation weakly orienting `s9RuleList`,
     strict orientation of EITHER `R2` OR `R11` forces
     `v_0([L, B1, R]) > v_0([L, B1, B0, R])`, which algebraically forces
     `(M_{L · B1})_{0, 1} ≥ 1`, `(M_{B0})_{1, 1} = 0` (singular zero lower-right diagonal on `B0`!),
     AND `(v_R)_1 ≥ 1`!
  3. Across ALL dimensions `d ≥ 1` and ALL finite tower heights `k : Nat`, NO coordinatewise-monotone
     or lower-triangular `ω^k` matrix tower can terminate `s9RuleList`!
-/
theorem s9_subseq_pumping_and_d2_zero_diag_obstruction :
    (srsPlusFromList s9RuleList [.L, .B1, .R] [.L, .B1, .B0, .R] ∧
     srsPlusFromList s9RuleList [.L, .T2, .R] [.L, .T2, .B0, .R] ∧
     srsPlusFromList s9RuleList [.L, .B1, .B0, .B0, .R] [.L, .B1, .B1, .R] ∧
     srsPlusFromList s9RuleList [.L, .B1, .B0, .R] [.L, .R]) ∧
    (∀ interp : MixedSRSSym -> NatAffineDim 2,
      (∀ s : MixedSRSSym, (interp s).M ⟨0, by decide⟩ ⟨0, by decide⟩ ≥ 1) ->
      (∀ r ∈ s9RuleList, weakOrientsNatAffineDim 2
        (evalWordNatAffineDim 2 interp r.1) (evalWordNatAffineDim 2 interp r.2)) ->
      (orientsNatAffineDim 2 (by decide)
         (evalWordNatAffineDim 2 interp [.L, .B1]) (evalWordNatAffineDim 2 interp [.L, .T2]) ∨
       orientsNatAffineDim 2 (by decide)
         (evalWordNatAffineDim 2 interp [.T2, .R]) (evalWordNatAffineDim 2 interp [.B1, .B0, .R])) ->
      let idx0 : Fin 2 := ⟨0, by decide⟩
      let idx1 : Fin 2 := ⟨1, by decide⟩
      (evalWordNatAffineDim 2 interp [.L, .B1, .R]).v idx0 >
        (evalWordNatAffineDim 2 interp [.L, .B1, .B0, .R]).v idx0 ∧
      (evalWordNatAffineDim 2 interp [.L, .B1]).M idx0 idx1 ≥ 1 ∧
      (interp .B0).M idx1 idx1 = 0 ∧
      (interp .R).v idx1 ≥ 1) ∧
    (∀ (d : Nat) (hd : 0 < d) (k : Nat),
      ¬ OmegaCoordMonotoneMatrixTower d hd k s9RuleList ∧
      ¬ OmegaLowerTriMatrixTower d hd k s9RuleList) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact ⟨[.L, .T2, .R],
      ⟨[], [.L, .B1], [.L, .T2], [.R], by decide, rfl, rfl⟩,
      .step ⟨[.L], [.T2, .R], [.B1, .B0, .R], [], by decide, rfl, rfl⟩ (.refl _)⟩
  · exact ⟨[.L, .B1, .B0, .R],
      ⟨[.L], [.T2, .R], [.B1, .B0, .R], [], by decide, rfl, rfl⟩,
      .step ⟨[], [.L, .B1], [.L, .T2], [.B0, .R], by decide, rfl, rfl⟩ (.refl _)⟩
  · exact ⟨[.L, .T2, .B0, .B0, .R],
      ⟨[], [.L, .B1], [.L, .T2], [.B0, .B0, .R], by decide, rfl, rfl⟩,
      .step ⟨[.L], [.T2, .B0], [.B0, .T1], [.B0, .R], by decide, rfl, rfl⟩
        (.step ⟨[.L, .B0], [.T1, .B0], [.B1, .T0], [.R], by decide, rfl, rfl⟩
          (.step ⟨[], [.L, .B0], [.L], [.B1, .T0, .R], by decide, rfl, rfl⟩
            (.step ⟨[.L, .B1], [.T0, .R], [.B1, .R], [], by decide, rfl, rfl⟩ (.refl _))))⟩
  · exact ⟨[.L, .T2, .B0, .R],
      ⟨[], [.L, .B1], [.L, .T2], [.B0, .R], by decide, rfl, rfl⟩,
      .step ⟨[.L], [.T2, .B0], [.B0, .T1], [.R], by decide, rfl, rfl⟩
        (.step ⟨[.L, .B0], [.T1, .R], [.B0, .B0, .R], [], by decide, rfl, rfl⟩
          (.step ⟨[], [.L, .B0], [.L], [.B0, .B0, .R], by decide, rfl, rfl⟩
            (.step ⟨[], [.L, .B0], [.L], [.B0, .R], by decide, rfl, rfl⟩
              (.step ⟨[], [.L, .B0], [.L], [.R], by decide, rfl, rfl⟩ (.refl _)))))⟩
  · intro interp htop hweak hstr_or
    dsimp only
    let idx0 : Fin 2 := ⟨0, by decide⟩
    let idx1 : Fin 2 := ⟨1, by decide⟩
    have hw_r2 : weakOrientsNatAffineDim 2
        (evalWordNatAffineDim 2 interp [.L, .B1, .R])
        (evalWordNatAffineDim 2 interp [.L, .T2, .R]) := by
      simpa using (hofbauer_waldmann_context_monotonicity 2 (by decide) interp htop
        [] [.L, .B1] [.L, .T2] [.R]).1 (hweak ([.L, .B1], [.L, .T2]) (by decide))
    have hw_r11 : weakOrientsNatAffineDim 2
        (evalWordNatAffineDim 2 interp [.L, .T2, .R])
        (evalWordNatAffineDim 2 interp [.L, .B1, .B0, .R]) := by
      simpa using (hofbauer_waldmann_context_monotonicity 2 (by decide) interp htop
        [.L] [.T2, .R] [.B1, .B0, .R] []).1 (hweak ([.T2, .R], [.B1, .B0, .R]) (by decide))
    have hgt_loop : (evalWordNatAffineDim 2 interp [.L, .B1, .R]).v idx0 >
        (evalWordNatAffineDim 2 interp [.L, .B1, .B0, .R]).v idx0 := by
      rcases hstr_or with hs2 | hs11
      · have hs2_ctx := (hofbauer_waldmann_context_monotonicity 2 (by decide) interp htop
          [] [.L, .B1] [.L, .T2] [.R]).2 hs2
        have h1 : (evalWordNatAffineDim 2 interp [.L, .B1, .R]).v idx0 >
            (evalWordNatAffineDim 2 interp [.L, .T2, .R]).v idx0 := by
          simpa [idx0] using hs2_ctx.2.2
        have h2 := hw_r11.2 idx0
        omega
      · have hs11_ctx := (hofbauer_waldmann_context_monotonicity 2 (by decide) interp htop
          [.L] [.T2, .R] [.B1, .B0, .R] []).2 hs11
        have h1 := hw_r2.2 idx0
        have h2 : (evalWordNatAffineDim 2 interp [.L, .T2, .R]).v idx0 >
            (evalWordNatAffineDim 2 interp [.L, .B1, .B0, .R]).v idx0 := by
          simpa [idx0] using hs11_ctx.2.2
        omega
    have hv2_expand : ∀ (M2 : Fin 2 -> Fin 2 -> Nat) (w : Fin 2 -> Nat) (i : Fin 2),
        natMatVec 2 M2 w i = M2 i idx0 * w idx0 + M2 i idx1 * w idx1 := by
      intro M2 w i
      unfold natMatVec natSumFin
      simp [natSumPrefix, idx0, idx1]
    rcases evalWordNatAffineDim_append_w8 2 interp [.L, .B1] [.R] with ⟨_, hv_lbr⟩
    rcases evalWordNatAffineDim_append_w8 2 interp [.L, .B1] [.B0, .R] with ⟨_, hv_lb1_b0r⟩
    let LB1 := evalWordNatAffineDim 2 interp [.L, .B1]
    have hb0_00_pos : (interp .B0).M idx0 idx0 ≥ 1 := htop .B0
    have hR_v : ∀ i : Fin 2, (evalWordNatAffineDim 2 interp [.R]).v i = (interp .R).v i :=
      (evalWordNatAffineDim_singleton_eq 2 interp .R).2
    have hB0R_v : ∀ i : Fin 2,
        (evalWordNatAffineDim 2 interp [.B0, .R]).v i =
          natMatVec 2 (interp .B0).M (interp .R).v i + (interp .B0).v i := by
      intro i
      change (compNatAffineDim 2 (interp .B0) (evalWordNatAffineDim 2 interp [.R])).v i = _
      simp only [compNatAffineDim]
      have hmv : natMatVec 2 (interp .B0).M (evalWordNatAffineDim 2 interp [.R]).v i =
          natMatVec 2 (interp .B0).M (interp .R).v i :=
        natSumPrefix_congr 2 _ _ (fun k => by rw [hR_v k]) 2
      rw [hmv]
    have hlhs : (evalWordNatAffineDim 2 interp [.L, .B1, .R]).v idx0 =
        LB1.M idx0 idx0 * (interp .R).v idx0 + LB1.M idx0 idx1 * (interp .R).v idx1 + LB1.v idx0 := by
      change (evalWordNatAffineDim 2 interp ([.L, .B1] ++ [.R])).v idx0 = _
      rw [hv_lbr idx0]
      simp only [compNatAffineDim]
      have hmv : natMatVec 2 LB1.M (evalWordNatAffineDim 2 interp [.R]).v idx0 =
          natMatVec 2 LB1.M (interp .R).v idx0 :=
        natSumPrefix_congr 2 _ _ (fun k => by rw [hR_v k]) 2
      rw [hmv, hv2_expand LB1.M (interp .R).v idx0]
    have hrhs : (evalWordNatAffineDim 2 interp [.L, .B1, .B0, .R]).v idx0 =
        LB1.M idx0 idx0 *
          ((interp .B0).M idx0 idx0 * (interp .R).v idx0 +
           (interp .B0).M idx0 idx1 * (interp .R).v idx1 + (interp .B0).v idx0) +
        LB1.M idx0 idx1 *
          ((interp .B0).M idx1 idx0 * (interp .R).v idx0 +
           (interp .B0).M idx1 idx1 * (interp .R).v idx1 + (interp .B0).v idx1) +
        LB1.v idx0 := by
      change (evalWordNatAffineDim 2 interp ([.L, .B1] ++ [.B0, .R])).v idx0 = _
      rw [hv_lb1_b0r idx0]
      simp only [compNatAffineDim]
      rw [hv2_expand LB1.M (evalWordNatAffineDim 2 interp [.B0, .R]).v idx0,
          hB0R_v idx0, hB0R_v idx1,
          hv2_expand (interp .B0).M (interp .R).v idx0,
          hv2_expand (interp .B0).M (interp .R).v idx1]
    have hge_term0 : LB1.M idx0 idx0 * (interp .R).v idx0 ≤
        LB1.M idx0 idx0 *
          ((interp .B0).M idx0 idx0 * (interp .R).v idx0 +
           (interp .B0).M idx0 idx1 * (interp .R).v idx1 + (interp .B0).v idx0) := by
      apply Nat.mul_le_mul_left
      have hm := Nat.mul_le_mul_right ((interp .R).v idx0) hb0_00_pos
      omega
    have hlt_term1 : LB1.M idx0 idx1 *
          ((interp .B0).M idx1 idx0 * (interp .R).v idx0 +
           (interp .B0).M idx1 idx1 * (interp .R).v idx1 + (interp .B0).v idx1) <
        LB1.M idx0 idx1 * (interp .R).v idx1 := by
      have hg := hgt_loop
      rw [hlhs, hrhs] at hg
      omega
    have hq1_pos : LB1.M idx0 idx1 ≥ 1 := by
      cases hq : LB1.M idx0 idx1 with
      | zero => rw [hq] at hlt_term1; simp at hlt_term1
      | succ _ => omega
    let inner := (interp .B0).M idx1 idx0 * (interp .R).v idx0 +
        (interp .B0).M idx1 idx1 * (interp .R).v idx1 + (interp .B0).v idx1
    have hlt_inner : inner < (interp .R).v idx1 := by
      change LB1.M idx0 idx1 * inner < LB1.M idx0 idx1 * (interp .R).v idx1 at hlt_term1
      by_cases h : inner < (interp .R).v idx1
      · exact h
      · have hm := Nat.mul_le_mul_left (LB1.M idx0 idx1) (by omega : (interp .R).v idx1 ≤ inner)
        omega
    have hyR_pos : (interp .R).v idx1 ≥ 1 := by dsimp [inner] at hlt_inner; omega
    have hdB0_zero : (interp .B0).M idx1 idx1 = 0 := by
      dsimp [inner] at hlt_inner
      cases hd : (interp .B0).M idx1 idx1 with
      | zero => rfl
      | succ d' =>
        rw [hd] at hlt_inner
        have hm := Nat.mul_le_mul_right ((interp .R).v idx1) (by omega : 1 ≤ d' + 1)
        omega
    exact ⟨hgt_loop, hq1_pos, hdB0_zero, hyR_pos⟩
  · intro d hd k
    have hlow_imp : ∀ (lvl : Nat) (rules : List (List MixedSRSSym × List MixedSRSSym)),
        (∀ r ∈ s9RuleList, r ∈ rules) ->
        ¬ OmegaLowerTriMatrixTower d hd lvl rules := by
      intro lvl
      induction lvl with
      | zero =>
        intro rules hsub h0
        rw [OmegaLowerTriMatrixTower] at h0; subst h0
        exact List.not_mem_nil (hsub ([.L, .B1], [.L, .T2]) (by decide))
      | succ lvl' ih =>
        intro rules hsub hsucc
        rcases hsucc with rfl | ⟨rem, interp, htri, hweak, hkeep, hrem_t⟩
        · exact List.not_mem_nil (hsub ([.L, .B1], [.L, .T2]) (by decide))
        · let z : Fin d := ⟨0, hd⟩
          have hz_val : z.val = 0 := rfl
          have htri_z : ∀ (s : MixedSRSSym) (p : Fin d), p.val ≠ 0 -> (interp s).M z p = 0 := by
            intro s p hp0
            exact (htri s).1 z p (by rw [hz_val]; omega)
          have h2_step : ∀ s1 s2 : MixedSRSSym,
              (evalWordNatAffineDim d interp [s1, s2]).M z z =
                (interp s1).M z z * (interp s2).M z z ∧
              (evalWordNatAffineDim d interp [s1, s2]).v z =
                (interp s1).M z z * (interp s2).v z + (interp s1).v z := by
            intro s1 s2
            rcases evalWordNatAffineDim_singleton_eq d interp s2 with ⟨hm2, hv2⟩
            change (compNatAffineDim d (interp s1) (evalWordNatAffineDim d interp [s2])).M z z = _ ∧
              (compNatAffineDim d (interp s1) (evalWordNatAffineDim d interp [s2])).v z = _
            refine ⟨?_, ?_⟩
            · simp only [compNatAffineDim, natMatMul, natSumFin]
              have hcong : natSumPrefix d
                  (fun p => (interp s1).M z p * (evalWordNatAffineDim d interp [s2]).M p z) d =
                  natSumPrefix d
                    (fun p => if p.val = z.val then (interp s1).M z z * (interp s2).M z z else 0) d := by
                apply natSumPrefix_congr d; intro p
                by_cases hpz : p.val = z.val
                · have hp_eq : p = z := Fin.ext hpz
                  subst hp_eq; simp [hm2 z z]
                · simp only [hpz, ite_false]
                  rw [htri_z s1 p (by rw [hz_val] at hpz; exact hpz), Nat.zero_mul]
              rw [hcong, natSumPrefix_single d z _ d]; simp [z, hd]
            · simp only [compNatAffineDim]
              apply congrArg (· + (interp s1).v z)
              unfold natMatVec natSumFin
              have hcong : natSumPrefix d
                  (fun p => (interp s1).M z p * (evalWordNatAffineDim d interp [s2]).v p) d =
                  natSumPrefix d
                    (fun p => if p.val = z.val then (interp s1).M z z * (interp s2).v z else 0) d := by
                apply natSumPrefix_congr d; intro p
                by_cases hpz : p.val = z.val
                · have hp_eq : p = z := Fin.ext hpz
                  subst hp_eq; simp [hv2 z]
                · simp only [hpz, ite_false]
                  rw [htri_z s1 p (by rw [hz_val] at hpz; exact hpz), Nat.zero_mul]
              rw [hcong, natSumPrefix_single d z _ d]; simp [z, hd]
          have h3_step : ∀ s1 s2 s3 : MixedSRSSym,
              (evalWordNatAffineDim d interp [s1, s2, s3]).M z z =
                (interp s1).M z z * ((interp s2).M z z * (interp s3).M z z) ∧
              (evalWordNatAffineDim d interp [s1, s2, s3]).v z =
                (interp s1).M z z * ((interp s2).M z z * (interp s3).v z + (interp s2).v z) +
                  (interp s1).v z := by
            intro s1 s2 s3
            rcases h2_step s2 s3 with ⟨hm23, hv23⟩
            change (compNatAffineDim d (interp s1) (evalWordNatAffineDim d interp [s2, s3])).M z z = _ ∧
              (compNatAffineDim d (interp s1) (evalWordNatAffineDim d interp [s2, s3])).v z = _
            refine ⟨?_, ?_⟩
            · simp only [compNatAffineDim, natMatMul, natSumFin]
              have hcong : natSumPrefix d
                  (fun p => (interp s1).M z p * (evalWordNatAffineDim d interp [s2, s3]).M p z) d =
                  natSumPrefix d
                    (fun p => if p.val = z.val then (interp s1).M z z * (evalWordNatAffineDim d interp [s2, s3]).M z z else 0) d := by
                apply natSumPrefix_congr d; intro p
                by_cases hpz : p.val = z.val
                · have hp_eq : p = z := Fin.ext hpz; subst hp_eq; simp
                · simp [hpz, htri_z s1 p (by rw [hz_val] at hpz; exact hpz)]
              rw [hcong, natSumPrefix_single d z _ d, hm23]; simp [z, hd]
            · simp only [compNatAffineDim]
              apply congrArg (· + (interp s1).v z)
              unfold natMatVec natSumFin
              have hcong : natSumPrefix d
                  (fun p => (interp s1).M z p * (evalWordNatAffineDim d interp [s2, s3]).v p) d =
                  natSumPrefix d
                    (fun p => if p.val = z.val then (interp s1).M z z * (evalWordNatAffineDim d interp [s2, s3]).v z else 0) d := by
                apply natSumPrefix_congr d; intro p
                by_cases hpz : p.val = z.val
                · have hp_eq : p = z := Fin.ext hpz; subst hp_eq; simp
                · simp [hpz, htri_z s1 p (by rw [hz_val] at hpz; exact hpz)]
              rw [hcong, natSumPrefix_single d z _ d, hv23]; simp [z, hd]
          let aL := (interp .L).M z z
          let aR := (interp .R).M z z
          let aB0 := (interp .B0).M z z
          let aB1 := (interp .B1).M z z
          let aT0 := (interp .T0).M z z
          let aT1 := (interp .T1).M z z
          let aT2 := (interp .T2).M z z
          have haL : aL ≥ 1 := (htri .L).2
          have haR : aR ≥ 1 := (htri .R).2
          have haB0 : aB0 ≥ 1 := (htri .B0).2
          have haB1 : aB1 ≥ 1 := (htri .B1).2
          have haT0 : aT0 ≥ 1 := (htri .T0).2
          have haT1 : aT1 ≥ 1 := (htri .T1).2
          have haT2 : aT2 ≥ 1 := (htri .T2).2
          have hw2 := hweak ([.L, .B1], [.L, .T2]) (hsub _ (by decide))
          have hw5 := hweak ([.T1, .B0], [.B1, .T0]) (hsub _ (by decide))
          have hw7 := hweak ([.T2, .B0], [.B0, .T1]) (hsub _ (by decide))
          have hw9 := hweak ([.T0, .R], [.B1, .R]) (hsub _ (by decide))
          have hw11 := hweak ([.T2, .R], [.B1, .B0, .R]) (hsub _ (by decide))
          have hm2 : aL * aB1 ≥ aL * aT2 := by
            have h := hw2.1 z z; rwa [(h2_step .L .B1).1, (h2_step .L .T2).1] at h
          have hm11 : aT2 * aR ≥ aB1 * (aB0 * aR) := by
            have h := hw11.1 z z; rwa [(h2_step .T2 .R).1, (h3_step .B1 .B0 .R).1] at h
          have haB1_ge_T2 : aB1 ≥ aT2 := nat_mul_le_cancel_left_w5 aL aT2 aB1 haL hm2
          have haT2_ge_B1B0 : aT2 ≥ aB1 * aB0 := by
            rw [← Nat.mul_assoc aB1 aB0 aR] at hm11
            exact nat_mul_le_cancel_right_w5 aR (aB1 * aB0) aT2 haR hm11
          have haB0_1 : aB0 = 1 := by
            by_cases hgt : aB0 ≥ 2
            · have hm := Nat.mul_le_mul_left aB1 hgt; omega
            · omega
          have haT2_eq_B1 : aT2 = aB1 := by rw [haB0_1, Nat.mul_one] at haT2_ge_B1B0; omega
          have hm7 : aT2 * aB0 ≥ aB0 * aT1 := by
            have h := hw7.1 z z; rwa [(h2_step .T2 .B0).1, (h2_step .B0 .T1).1] at h
          have haB1_ge_T1 : aB1 ≥ aT1 := by rw [haB0_1, haT2_eq_B1] at hm7; omega
          have hm9 : aT0 * aR ≥ aB1 * aR := by
            have h := hw9.1 z z; rwa [(h2_step .T0 .R).1, (h2_step .B1 .R).1] at h
          have haT0_ge_B1 : aT0 ≥ aB1 := nat_mul_le_cancel_right_w5 aR aB1 aT0 haR hm9
          have hm5 : aT1 * aB0 ≥ aB1 * aT0 := by
            have h := hw5.1 z z; rwa [(h2_step .T1 .B0).1, (h2_step .B1 .T0).1] at h
          rw [haB0_1, Nat.mul_one] at hm5
          have haB1_1 : aB1 = 1 := by
            by_cases hgt : aB1 ≥ 2
            · have hsq : aB1 * aT0 ≥ 2 * aT0 := Nat.mul_le_mul_right aT0 hgt
              omega
            · omega
          have haT2_1 : aT2 = 1 := by omega
          have haT1_1 : aT1 = 1 := by omega
          have haT0_1 : aT0 = 1 := by rw [haB1_1, haT1_1, Nat.one_mul] at hm5; omega
          let xB0 := (interp .B0).v z
          let xB1 := (interp .B1).v z
          let xT0 := (interp .T0).v z
          let xT1 := (interp .T1).v z
          let xT2 := (interp .T2).v z
          have hv2_ineq : aL * xB1 + (interp .L).v z ≥ aL * xT2 + (interp .L).v z := by
            have h := hw2.2 z; rwa [(h2_step .L .B1).2, (h2_step .L .T2).2] at h
          have hxB1_ge_T2 : xB1 ≥ xT2 := nat_mul_le_cancel_left_w5 aL xT2 xB1 haL (by omega)
          have hv11_ineq : aT2 * (interp .R).v z + xT2 ≥ aB1 * (aB0 * (interp .R).v z + xB0) + xB1 := by
            have h := hw11.2 z; rwa [(h2_step .T2 .R).2, (h3_step .B1 .B0 .R).2] at h
          simp only [haT2_1, haB1_1, haB0_1, Nat.one_mul] at hv11_ineq
          have hxB0_0 : xB0 = 0 := by omega
          have hxT2_eq_B1 : xT2 = xB1 := by omega
          have hv7_ineq : aT2 * xB0 + xT2 ≥ aB0 * xT1 + xB0 := by
            have h := hw7.2 z; rwa [(h2_step .T2 .B0).2, (h2_step .B0 .T1).2] at h
          rw [haT2_1, haB0_1, hxB0_0] at hv7_ineq
          have hv5_ineq : aT1 * xB0 + xT1 ≥ aB1 * xT0 + xB1 := by
            have h := hw5.2 z; rwa [(h2_step .T1 .B0).2, (h2_step .B1 .T0).2] at h
          rw [haT1_1, haB1_1, hxB0_0] at hv5_ineq
          have hxT0_0 : xT0 = 0 := by omega
          have hxT1_eq_B1 : xT1 = xB1 := by omega
          have hv9_ineq : aT0 * (interp .R).v z + xT0 ≥ aB1 * (interp .R).v z + xB1 := by
            have h := hw9.2 z; rwa [(h2_step .T0 .R).2, (h2_step .B1 .R).2] at h
          simp only [haT0_1, haB1_1, hxT0_0, Nat.one_mul] at hv9_ineq
          have hxB1_0 : xB1 = 0 := by omega
          have hxT1_0 : xT1 = 0 := by omega
          have hxT2_0 : xT2 = 0 := by omega
          have hall_rem : ∀ r ∈ s9RuleList, r ∈ rem := by
            intro r hr
            apply hkeep r (hsub r hr)
            simp only [s9RuleList, List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · intro hstr; have hgt := hstr.2.2
              have hl := (evalWordNatAffineDim_singleton_eq d interp .L).2 z
              change (evalWordNatAffineDim d interp [.L, .B0]).v z > (evalWordNatAffineDim d interp [.L]).v z at hgt
              rw [(h2_step .L .B0).2, hl] at hgt
              change aL * xB0 + (interp .L).v z > (interp .L).v z at hgt
              rw [hxB0_0, Nat.mul_zero] at hgt; omega
            · intro hstr; have hgt := hstr.2.2
              change (evalWordNatAffineDim d interp [.L, .B1]).v z > (evalWordNatAffineDim d interp [.L, .T2]).v z at hgt
              rw [(h2_step .L .B1).2, (h2_step .L .T2).2] at hgt
              change aL * xB1 + (interp .L).v z > aL * xT2 + (interp .L).v z at hgt
              rw [hxB1_0, hxT2_0] at hgt; omega
            · intro hstr; have hgt := hstr.2.2
              change (evalWordNatAffineDim d interp [.T0, .B1]).v z > (evalWordNatAffineDim d interp [.B1, .T1]).v z at hgt
              rw [(h2_step .T0 .B1).2, (h2_step .B1 .T1).2] at hgt
              change aT0 * xB1 + xT0 > aB1 * xT1 + xB1 at hgt
              rw [hxB1_0, hxT0_0, hxT1_0] at hgt; omega
            · intro hstr; have hgt := hstr.2.2
              change (evalWordNatAffineDim d interp [.T1, .B0]).v z > (evalWordNatAffineDim d interp [.B1, .T0]).v z at hgt
              rw [(h2_step .T1 .B0).2, (h2_step .B1 .T0).2] at hgt
              change aT1 * xB0 + xT1 > aB1 * xT0 + xB1 at hgt
              rw [hxB0_0, hxT1_0, hxT0_0, hxB1_0] at hgt; omega
            · intro hstr; have hgt := hstr.2.2
              change (evalWordNatAffineDim d interp [.T1, .B1]).v z > (evalWordNatAffineDim d interp [.B0, .T2]).v z at hgt
              rw [(h2_step .T1 .B1).2, (h2_step .B0 .T2).2] at hgt
              change aT1 * xB1 + xT1 > aB0 * xT2 + xB0 at hgt
              rw [hxB1_0, hxT1_0, hxT2_0, hxB0_0] at hgt; omega
            · intro hstr; have hgt := hstr.2.2
              change (evalWordNatAffineDim d interp [.T2, .B0]).v z > (evalWordNatAffineDim d interp [.B0, .T1]).v z at hgt
              rw [(h2_step .T2 .B0).2, (h2_step .B0 .T1).2] at hgt
              change aT2 * xB0 + xT2 > aB0 * xT1 + xB0 at hgt
              rw [hxB0_0, hxT2_0, hxT1_0] at hgt; omega
            · intro hstr; have hgt := hstr.2.2
              change (evalWordNatAffineDim d interp [.T0, .R]).v z > (evalWordNatAffineDim d interp [.B1, .R]).v z at hgt
              rw [(h2_step .T0 .R).2, (h2_step .B1 .R).2] at hgt
              change aT0 * (interp .R).v z + xT0 > aB1 * (interp .R).v z + xB1 at hgt
              rw [haT0_1, haB1_1, hxT0_0, hxB1_0] at hgt; omega
            · intro hstr; have hgt := hstr.2.2
              change (evalWordNatAffineDim d interp [.T1, .R]).v z > (evalWordNatAffineDim d interp [.B0, .B0, .R]).v z at hgt
              rw [(h2_step .T1 .R).2, (h3_step .B0 .B0 .R).2] at hgt
              change aT1 * (interp .R).v z + xT1 > aB0 * (aB0 * (interp .R).v z + xB0) + xB0 at hgt
              rw [haT1_1, haB0_1, hxT1_0, hxB0_0] at hgt; omega
            · intro hstr; have hgt := hstr.2.2
              change (evalWordNatAffineDim d interp [.T2, .R]).v z > (evalWordNatAffineDim d interp [.B1, .B0, .R]).v z at hgt
              rw [(h2_step .T2 .R).2, (h3_step .B1 .B0 .R).2] at hgt
              change aT2 * (interp .R).v z + xT2 > aB1 * (aB0 * (interp .R).v z + xB0) + xB1 at hgt
              rw [haT2_1, haB1_1, haB0_1, hxT2_0, hxB0_0, hxB1_0] at hgt; omega
          exact ih rem hall_rem hrem_t
    have hcoord_imp : ∀ (lvl : Nat) (rules : List (List MixedSRSSym × List MixedSRSSym)),
        ([.L, .B1], [.L, .T2]) ∈ rules ->
        ([.T2, .R], [.B1, .B0, .R]) ∈ rules ->
        ¬ OmegaCoordMonotoneMatrixTower d hd lvl rules := by
      intro lvl
      induction lvl with
      | zero =>
        intro rules hr2 _ h0
        rw [OmegaCoordMonotoneMatrixTower] at h0; subst h0
        exact List.not_mem_nil hr2
      | succ lvl' ih =>
        intro rules hr2 hr11 hsucc
        rcases hsucc with rfl | ⟨rem, interp, hdiag, hweak, hkeep, hrem_t⟩
        · exact List.not_mem_nil hr2
        · let z : Fin d := ⟨0, hd⟩
          have htop : ∀ s : MixedSRSSym, (interp s).M z z ≥ 1 := fun s => hdiag s z
          have hw_r2 : weakOrientsNatAffineDim d
              (evalWordNatAffineDim d interp [.L, .B1, .R])
              (evalWordNatAffineDim d interp [.L, .T2, .R]) := by
            simpa using (hofbauer_waldmann_context_monotonicity d hd interp htop
              [] [.L, .B1] [.L, .T2] [.R]).1 (hweak _ hr2)
          have hw_r11 : weakOrientsNatAffineDim d
              (evalWordNatAffineDim d interp [.L, .T2, .R])
              (evalWordNatAffineDim d interp [.L, .B1, .B0, .R]) := by
            simpa using (hofbauer_waldmann_context_monotonicity d hd interp htop
              [.L] [.T2, .R] [.B1, .B0, .R] []).1 (hweak _ hr11)
          have hR_v := (evalWordNatAffineDim_singleton_eq d interp .R).2
          have hb0r_ge : ∀ k : Fin d,
              (evalWordNatAffineDim d interp [.B0, .R]).v k ≥ (interp .R).v k := by
            intro k
            change (compNatAffineDim d (interp .B0) (evalWordNatAffineDim d interp [.R])).v k ≥ _
            simp only [compNatAffineDim]
            have hmv : natMatVec d (interp .B0).M (evalWordNatAffineDim d interp [.R]).v k =
                natMatVec d (interp .B0).M (interp .R).v k :=
              natSumPrefix_congr d _ _ (fun j => by rw [hR_v j]) d
            rw [hmv]
            have hterm : ∀ j : Fin d,
                (if j.val = k.val then (interp .B0).M k k * (interp .R).v k else 0) ≤
                  (interp .B0).M k j * (interp .R).v j := by
              intro j
              by_cases hjk : j.val = k.val
              · have hje : j = k := Fin.ext hjk
                subst hje; simp
              · simp [hjk]
            have hsum := natSumPrefix_mono_w5 d _ _ hterm d
            rw [natSumPrefix_single d k _ d] at hsum
            simp [k.isLt] at hsum
            have hm := Nat.mul_le_mul_right ((interp .R).v k) (hdiag .B0 k)
            unfold natMatVec natSumFin
            omega
          rcases evalWordNatAffineDim_append_w8 d interp [.L, .B1] [.R] with ⟨_, hv_lbr⟩
          rcases evalWordNatAffineDim_append_w8 d interp [.L, .B1] [.B0, .R] with ⟨_, hv_lb1b0r⟩
          have hv_mono : (evalWordNatAffineDim d interp [.L, .B1, .B0, .R]).v z ≥
              (evalWordNatAffineDim d interp [.L, .B1, .R]).v z := by
            change (evalWordNatAffineDim d interp ([.L, .B1] ++ [.B0, .R])).v z ≥
              (evalWordNatAffineDim d interp ([.L, .B1] ++ [.R])).v z
            rw [hv_lb1b0r z, hv_lbr z]
            simp only [compNatAffineDim]
            have hmv : natMatVec d (evalWordNatAffineDim d interp [.L, .B1]).M
                (evalWordNatAffineDim d interp [.R]).v z =
                natMatVec d (evalWordNatAffineDim d interp [.L, .B1]).M (interp .R).v z :=
              natSumPrefix_congr d _ _ (fun j => by rw [hR_v j]) d
            rw [hmv]
            have hm := natMatVec_mono_vec_w8 d (evalWordNatAffineDim d interp [.L, .B1]).M
              (evalWordNatAffineDim d interp [.B0, .R]).v (interp .R).v hb0r_ge z
            omega
          have hnr2 : ¬ orientsNatAffineDim d hd
              (evalWordNatAffineDim d interp [.L, .B1])
              (evalWordNatAffineDim d interp [.L, .T2]) := by
            intro hs2
            have hs2_c := (hofbauer_waldmann_context_monotonicity d hd interp htop
              [] [.L, .B1] [.L, .T2] [.R]).2 hs2
            have h1 : (evalWordNatAffineDim d interp [.L, .B1, .R]).v z >
                (evalWordNatAffineDim d interp [.L, .T2, .R]).v z := by
              simpa [z] using hs2_c.2.2
            have h2 := hw_r11.2 z
            omega
          have hnr11 : ¬ orientsNatAffineDim d hd
              (evalWordNatAffineDim d interp [.T2, .R])
              (evalWordNatAffineDim d interp [.B1, .B0, .R]) := by
            intro hs11
            have hs11_c := (hofbauer_waldmann_context_monotonicity d hd interp htop
              [.L] [.T2, .R] [.B1, .B0, .R] []).2 hs11
            have h1 := hw_r2.2 z
            have h2 : (evalWordNatAffineDim d interp [.L, .T2, .R]).v z >
                (evalWordNatAffineDim d interp [.L, .B1, .B0, .R]).v z := by
              simpa [z] using hs11_c.2.2
            omega
          exact ih rem (hkeep _ hr2 hnr2) (hkeep _ hr11 hnr11) hrem_t
    exact ⟨hcoord_imp k s9RuleList (by decide) (by decide),
           hlow_imp k s9RuleList (fun r hr => hr)⟩

/-- True strictly on the 5 interior symbols `{B0, B1, T0, T1, T2}` (excluding boundary `L, R`). -/
def isInteriorMixedSym : MixedSRSSym -> Bool
  | .L | .R => false
  | _ => true

/-- 1D additive Parikh symbol-weight evaluation of a word over `MixedSRSSym`. -/
def evalParikh1D (wt : MixedSRSSym -> Nat) : List MixedSRSSym -> Nat
  | [] => 0
  | s :: rest => wt s + evalParikh1D wt rest

/-- `k`-level `ω^k` Parikh / linear symbol-weight rule-removal tower. -/
def OmegaParikhRuleRemovalTower : Nat -> List (List MixedSRSSym × List MixedSRSSym) -> Prop
  | 0, rules => rules = []
  | k + 1, rules =>
    rules = [] ∨
    ∃ (rem : List (List MixedSRSSym × List MixedSRSSym))
      (wt : MixedSRSSym -> Nat),
      (∀ r ∈ rules, evalParikh1D wt r.1 ≥ evalParikh1D wt r.2) ∧
      (∀ r ∈ rules, ¬ (evalParikh1D wt r.1 > evalParikh1D wt r.2) -> r ∈ rem) ∧
      OmegaParikhRuleRemovalTower k rem

/--
  `k`-level `2D` (`2 x 2`) boundary-coupled Hofbauer–Waldmann rule-removal tower in which
  the 5 interior symbols `{B0, B1, T0, T1, T2}` are lower-triangular (`(M_s)_{0,1} = 0`,
  arbitrary zero lower diagonals `(M_s)_{1,1} = 0` allowed) while boundary symbols `L` and `R`
  carry **completely unrestricted full `2 x 2` non-triangular `Nat` matrices**!
-/
def OmegaInteriorLowerTri2DTower : Nat -> List (List MixedSRSSym × List MixedSRSSym) -> Prop
  | 0, rules => rules = []
  | k + 1, rules =>
    rules = [] ∨
    ∃ (rem : List (List MixedSRSSym × List MixedSRSSym))
      (interp : MixedSRSSym -> NatAffineDim 2),
      (∀ s : MixedSRSSym, (interp s).M ⟨0, by decide⟩ ⟨0, by decide⟩ ≥ 1) ∧
      (∀ s : MixedSRSSym, isInteriorMixedSym s = true ->
        (interp s).M ⟨0, by decide⟩ ⟨1, by decide⟩ = 0) ∧
      (∀ r ∈ rules, weakOrientsNatAffineDim 2
        (evalWordNatAffineDim 2 interp r.1) (evalWordNatAffineDim 2 interp r.2)) ∧
      (∀ r ∈ rules, ¬ orientsNatAffineDim 2 (by decide)
        (evalWordNatAffineDim 2 interp r.1) (evalWordNatAffineDim 2 interp r.2) -> r ∈ rem) ∧
      OmegaInteriorLowerTri2DTower k rem

theorem evalWord2D_two_eq (interp : MixedSRSSym -> NatAffineDim 2) (s1 s2 : MixedSRSSym) :
    let idx0 : Fin 2 := ⟨0, by decide⟩
    let idx1 : Fin 2 := ⟨1, by decide⟩
    (∀ i j : Fin 2,
      (evalWordNatAffineDim 2 interp [s1, s2]).M i j =
        (interp s1).M i idx0 * (interp s2).M idx0 j +
        (interp s1).M i idx1 * (interp s2).M idx1 j) ∧
    (∀ i : Fin 2,
      (evalWordNatAffineDim 2 interp [s1, s2]).v i =
        (interp s1).M i idx0 * (interp s2).v idx0 +
        (interp s1).M i idx1 * (interp s2).v idx1 + (interp s1).v i) := by
  dsimp only
  rcases evalWordNatAffineDim_singleton_eq 2 interp s2 with ⟨hm2, hv2⟩
  refine ⟨?_, ?_⟩
  · intro i j
    change (compNatAffineDim 2 (interp s1) (evalWordNatAffineDim 2 interp [s2])).M i j = _
    simp only [compNatAffineDim, natMatMul, natSumFin, natSumPrefix]
    simp [hm2]
  · intro i
    change (compNatAffineDim 2 (interp s1) (evalWordNatAffineDim 2 interp [s2])).v i = _
    simp only [compNatAffineDim, natMatVec, natSumFin, natSumPrefix]
    simp [hv2]

theorem evalWord2D_three_eq (interp : MixedSRSSym -> NatAffineDim 2) (s1 s2 s3 : MixedSRSSym) :
    let idx0 : Fin 2 := ⟨0, by decide⟩
    let idx1 : Fin 2 := ⟨1, by decide⟩
    (∀ i j : Fin 2,
      (evalWordNatAffineDim 2 interp [s1, s2, s3]).M i j =
        (interp s1).M i idx0 * (evalWordNatAffineDim 2 interp [s2, s3]).M idx0 j +
        (interp s1).M i idx1 * (evalWordNatAffineDim 2 interp [s2, s3]).M idx1 j) ∧
    (∀ i : Fin 2,
      (evalWordNatAffineDim 2 interp [s1, s2, s3]).v i =
        (interp s1).M i idx0 * (evalWordNatAffineDim 2 interp [s2, s3]).v idx0 +
        (interp s1).M i idx1 * (evalWordNatAffineDim 2 interp [s2, s3]).v idx1 + (interp s1).v i) := by
  dsimp only
  refine ⟨?_, ?_⟩
  · intro i j
    change (compNatAffineDim 2 (interp s1) (evalWordNatAffineDim 2 interp [s2, s3])).M i j = _
    simp [compNatAffineDim, natMatMul, natSumFin, natSumPrefix]
  · intro i
    change (compNatAffineDim 2 (interp s1) (evalWordNatAffineDim 2 interp [s2, s3])).v i = _
    simp [compNatAffineDim, natMatVec, natSumFin, natSumPrefix]

theorem s9_d2_interior_lower_tri_level_collapse (interp : MixedSRSSym -> NatAffineDim 2)
    (htop : ∀ s : MixedSRSSym, (interp s).M ⟨0, by decide⟩ ⟨0, by decide⟩ ≥ 1)
    (hint : ∀ s : MixedSRSSym, isInteriorMixedSym s = true ->
      (interp s).M ⟨0, by decide⟩ ⟨1, by decide⟩ = 0)
    (hweak : ∀ r ∈ s9RuleList, weakOrientsNatAffineDim 2
      (evalWordNatAffineDim 2 interp r.1) (evalWordNatAffineDim 2 interp r.2)) :
    ∀ r ∈ s9RuleList,
      (evalWordNatAffineDim 2 interp r.1).v ⟨0, by decide⟩ =
      (evalWordNatAffineDim 2 interp r.2).v ⟨0, by decide⟩ := by
  let idx0 : Fin 2 := ⟨0, by decide⟩
  let idx1 : Fin 2 := ⟨1, by decide⟩
  have hbB0 : (interp .B0).M idx0 idx1 = 0 := hint .B0 rfl
  have hbB1 : (interp .B1).M idx0 idx1 = 0 := hint .B1 rfl
  have hbT0 : (interp .T0).M idx0 idx1 = 0 := hint .T0 rfl
  have hbT1 : (interp .T1).M idx0 idx1 = 0 := hint .T1 rfl
  have hbT2 : (interp .T2).M idx0 idx1 = 0 := hint .T2 rfl
  let aL := (interp .L).M idx0 idx0
  let bL := (interp .L).M idx0 idx1
  let xL := (interp .L).v idx0
  let aR := (interp .R).M idx0 idx0
  let cR := (interp .R).M idx1 idx0
  let xR := (interp .R).v idx0
  let yR := (interp .R).v idx1
  let aB0 := (interp .B0).M idx0 idx0
  let cB0 := (interp .B0).M idx1 idx0
  let dB0 := (interp .B0).M idx1 idx1
  let xB0 := (interp .B0).v idx0
  let yB0 := (interp .B0).v idx1
  let aB1 := (interp .B1).M idx0 idx0
  let cB1 := (interp .B1).M idx1 idx0
  let dB1 := (interp .B1).M idx1 idx1
  let xB1 := (interp .B1).v idx0
  let yB1 := (interp .B1).v idx1
  let aT0 := (interp .T0).M idx0 idx0
  let xT0 := (interp .T0).v idx0
  let aT1 := (interp .T1).M idx0 idx0
  let dT1 := (interp .T1).M idx1 idx1
  let xT1 := (interp .T1).v idx0
  let yT1 := (interp .T1).v idx1
  let aT2 := (interp .T2).M idx0 idx0
  let cT2 := (interp .T2).M idx1 idx0
  let dT2 := (interp .T2).M idx1 idx1
  let xT2 := (interp .T2).v idx0
  let yT2 := (interp .T2).v idx1
  have haL : aL ≥ 1 := htop .L
  have haR : aR ≥ 1 := htop .R
  have haB0 : aB0 ≥ 1 := htop .B0
  have haB1 : aB1 ≥ 1 := htop .B1
  have haT0 : aT0 ≥ 1 := htop .T0
  have haT1 : aT1 ≥ 1 := htop .T1
  have haT2 : aT2 ≥ 1 := htop .T2
  have hw1 := hweak ([.L, .B0], [.L]) (by decide)
  have hw2 := hweak ([.L, .B1], [.L, .T2]) (by decide)
  have hw5 := hweak ([.T1, .B0], [.B1, .T0]) (by decide)
  have hw6 := hweak ([.T1, .B1], [.B0, .T2]) (by decide)
  have hw7 := hweak ([.T2, .B0], [.B0, .T1]) (by decide)
  have hw9 := hweak ([.T0, .R], [.B1, .R]) (by decide)
  have hw11 := hweak ([.T2, .R], [.B1, .B0, .R]) (by decide)
  have hr1_01 : bL * dB0 ≥ bL := by
    have h := hw1.1 idx0 idx1
    rw [(evalWord2D_two_eq interp .L .B0).1 idx0 idx1,
        (evalWordNatAffineDim_singleton_eq 2 interp .L).1 idx0 idx1] at h
    change aL * (interp .B0).M idx0 idx1 + bL * dB0 ≥ bL at h
    rw [hbB0] at h; omega
  have hr2_00 : aL * aB1 + bL * cB1 ≥ aL * aT2 + bL * cT2 := by
    have h := hw2.1 idx0 idx0
    rw [(evalWord2D_two_eq interp .L .B1).1 idx0 idx0,
        (evalWord2D_two_eq interp .L .T2).1 idx0 idx0] at h
    exact h
  have hr2_01 : bL * dB1 ≥ bL * dT2 := by
    have h := hw2.1 idx0 idx1
    rw [(evalWord2D_two_eq interp .L .B1).1 idx0 idx1,
        (evalWord2D_two_eq interp .L .T2).1 idx0 idx1] at h
    change aL * (interp .B1).M idx0 idx1 + bL * dB1 ≥
      aL * (interp .T2).M idx0 idx1 + bL * dT2 at h
    rw [hbB1, hbT2] at h; omega
  have hr11_00 : aT2 * aR ≥ aB1 * (aB0 * aR) := by
    have h := hw11.1 idx0 idx0
    rw [(evalWord2D_two_eq interp .T2 .R).1 idx0 idx0,
        (evalWord2D_three_eq interp .B1 .B0 .R).1 idx0 idx0,
        (evalWord2D_two_eq interp .B0 .R).1 idx0 idx0] at h
    change aT2 * aR + (interp .T2).M idx0 idx1 * cR ≥
      aB1 * (aB0 * aR + (interp .B0).M idx0 idx1 * cR) +
      (interp .B1).M idx0 idx1 * (evalWordNatAffineDim 2 interp [.B0, .R]).M idx1 idx0 at h
    simp only [hbT2, hbB0, hbB1, Nat.zero_mul, Nat.add_zero] at h
    exact h
  have haT2_ge_B1B0 : aT2 ≥ aB1 * aB0 := by
    rw [← Nat.mul_assoc] at hr11_00
    exact nat_mul_le_cancel_right_w5 aR (aB1 * aB0) aT2 haR hr11_00
  have hr11_10 : cT2 * aR + dT2 * cR ≥
      cB1 * (aB0 * aR) + dB1 * (cB0 * aR + dB0 * cR) := by
    have h := hw11.1 idx1 idx0
    rw [(evalWord2D_two_eq interp .T2 .R).1 idx1 idx0,
        (evalWord2D_three_eq interp .B1 .B0 .R).1 idx1 idx0,
        (evalWord2D_two_eq interp .B0 .R).1 idx0 idx0,
        (evalWord2D_two_eq interp .B0 .R).1 idx1 idx0] at h
    change cT2 * aR + dT2 * cR ≥
      cB1 * (aB0 * aR + (interp .B0).M idx0 idx1 * cR) + dB1 * (cB0 * aR + dB0 * cR) at h
    simp only [hbB0, Nat.zero_mul, Nat.add_zero] at h
    exact h
  have hbL_d10 : bL * (dB1 * (dB0 * cR)) ≥ bL * (dT2 * cR) := by
    have h1 : bL * (dB1 * (dB0 * cR)) = dB1 * ((bL * dB0) * cR) := by
      simp only [← Nat.mul_assoc]; rw [Nat.mul_comm bL dB1]
    have h2 : dB1 * ((bL * dB0) * cR) ≥ dB1 * (bL * cR) :=
      Nat.mul_le_mul_left dB1 (Nat.mul_le_mul_right cR hr1_01)
    have h3 : dB1 * (bL * cR) = (bL * dB1) * cR := by
      rw [← Nat.mul_assoc, Nat.mul_comm dB1 bL]
    have h4 : (bL * dB1) * cR ≥ (bL * dT2) * cR := Nat.mul_le_mul_right cR hr2_01
    have h5 : (bL * dT2) * cR = bL * (dT2 * cR) := Nat.mul_assoc bL dT2 cR
    omega
  have hbL_cB1_aB0 : bL * (cB1 * (aB0 * aR)) ≥ (bL * cB1) * aR := by
    have h1 : aB0 * aR ≥ 1 * aR := Nat.mul_le_mul_right aR haB0
    rw [Nat.one_mul] at h1
    have h2 := Nat.mul_le_mul_left bL (Nat.mul_le_mul_left cB1 h1)
    rwa [Nat.mul_assoc bL cB1 aR]
  have hbL_r11_10 := Nat.mul_le_mul_left bL hr11_10
  simp only [Nat.mul_add] at hbL_r11_10
  have hbL_cT2_ge : (bL * cT2) * aR ≥ (bL * cB1) * aR := by
    have hc_as : bL * (cT2 * aR) = (bL * cT2) * aR := (Nat.mul_assoc bL cT2 aR).symm
    omega
  have hbL_cT2_ge_cB1 : bL * cT2 ≥ bL * cB1 :=
    nat_mul_le_cancel_right_w5 aR (bL * cB1) (bL * cT2) haR hbL_cT2_ge
  have haB1_ge_T2 : aB1 ≥ aT2 := by
    have hsum : aL * aB1 ≥ aL * aT2 := by
      dsimp [aL, bL, aB1, cB1, aT2, cT2] at hr2_00 hbL_cT2_ge_cB1 ⊢
      omega
    exact nat_mul_le_cancel_left_w5 aL aT2 aB1 haL hsum
  have haB0_1 : aB0 = 1 := by
    by_cases hgt : aB0 ≥ 2
    · have hm := Nat.mul_le_mul_left aB1 hgt; omega
    · omega
  have haT2_eq_B1 : aT2 = aB1 := by rw [haB0_1, Nat.mul_one] at haT2_ge_B1B0; omega
  have hbL_c_eq : bL * cB1 = bL * cT2 := by
    rw [haT2_eq_B1] at hr2_00
    dsimp [aL, bL, aB1, cB1, cT2] at hr2_00 hbL_cT2_ge_cB1 ⊢
    omega
  have hr7_00 : aT2 * aB0 ≥ aB0 * aT1 := by
    have h := hw7.1 idx0 idx0
    rw [(evalWord2D_two_eq interp .T2 .B0).1 idx0 idx0,
        (evalWord2D_two_eq interp .B0 .T1).1 idx0 idx0] at h
    change aT2 * aB0 + (interp .T2).M idx0 idx1 * cB0 ≥
      aB0 * aT1 + (interp .B0).M idx0 idx1 * (interp .T1).M idx1 idx0 at h
    rw [hbT2, hbB0] at h; omega
  have haB1_ge_T1 : aB1 ≥ aT1 := by rw [haB0_1, haT2_eq_B1] at hr7_00; omega
  have hr9_00 : aT0 * aR ≥ aB1 * aR := by
    have h := hw9.1 idx0 idx0
    rw [(evalWord2D_two_eq interp .T0 .R).1 idx0 idx0,
        (evalWord2D_two_eq interp .B1 .R).1 idx0 idx0] at h
    change aT0 * aR + (interp .T0).M idx0 idx1 * cR ≥
      aB1 * aR + (interp .B1).M idx0 idx1 * cR at h
    rw [hbT0, hbB1] at h; omega
  have haT0_ge_B1 : aT0 ≥ aB1 := nat_mul_le_cancel_right_w5 aR aB1 aT0 haR hr9_00
  have hr5_00 : aT1 * aB0 ≥ aB1 * aT0 := by
    have h := hw5.1 idx0 idx0
    rw [(evalWord2D_two_eq interp .T1 .B0).1 idx0 idx0,
        (evalWord2D_two_eq interp .B1 .T0).1 idx0 idx0] at h
    change aT1 * aB0 + (interp .T1).M idx0 idx1 * cB0 ≥
      aB1 * aT0 + (interp .B1).M idx0 idx1 * (interp .T0).M idx1 idx0 at h
    rw [hbT1, hbB1] at h; omega
  rw [haB0_1, Nat.mul_one] at hr5_00
  have haB1_1 : aB1 = 1 := by
    by_cases hgt : aB1 ≥ 2
    · have hm := Nat.mul_le_mul_right aT0 hgt; omega
    · omega
  have haT2_1 : aT2 = 1 := by omega
  have haT1_1 : aT1 = 1 := by omega
  have haT0_1 : aT0 = 1 := by rw [haB1_1, haT1_1, Nat.one_mul] at hr5_00; omega
  have hr11_v0 : xR + xT2 ≥ (xR + xB0) + xB1 := by
    have h := hw11.2 idx0
    rw [(evalWord2D_two_eq interp .T2 .R).2 idx0,
        (evalWord2D_three_eq interp .B1 .B0 .R).2 idx0,
        (evalWord2D_two_eq interp .B0 .R).2 idx0] at h
    change aT2 * xR + (interp .T2).M idx0 idx1 * yR + xT2 ≥
      aB1 * (aB0 * xR + (interp .B0).M idx0 idx1 * yR + xB0) +
      (interp .B1).M idx0 idx1 * (evalWordNatAffineDim 2 interp [.B0, .R]).v idx1 + xB1 at h
    simp only [hbT2, hbB0, hbB1, haT2_1, haB1_1, haB0_1, Nat.zero_mul, Nat.one_mul, Nat.add_zero] at h
    exact h
  have hr11_v1 : cT2 * xR + dT2 * yR + yT2 ≥
      cB1 * (xR + xB0) + dB1 * (cB0 * xR + dB0 * yR + yB0) + yB1 := by
    have h := hw11.2 idx1
    rw [(evalWord2D_two_eq interp .T2 .R).2 idx1,
        (evalWord2D_three_eq interp .B1 .B0 .R).2 idx1,
        (evalWord2D_two_eq interp .B0 .R).2 idx0,
        (evalWord2D_two_eq interp .B0 .R).2 idx1] at h
    change cT2 * xR + dT2 * yR + yT2 ≥
      cB1 * (aB0 * xR + (interp .B0).M idx0 idx1 * yR + xB0) +
      dB1 * (cB0 * xR + dB0 * yR + yB0) + yB1 at h
    simp only [hbB0, haB0_1, Nat.zero_mul, Nat.one_mul, Nat.add_zero] at h
    exact h
  have hbL_dyR : bL * (dB1 * (dB0 * yR)) ≥ bL * (dT2 * yR) := by
    have h1 : bL * (dB1 * (dB0 * yR)) = dB1 * ((bL * dB0) * yR) := by
      simp only [← Nat.mul_assoc]; rw [Nat.mul_comm bL dB1]
    have h2 : dB1 * ((bL * dB0) * yR) ≥ dB1 * (bL * yR) :=
      Nat.mul_le_mul_left dB1 (Nat.mul_le_mul_right yR hr1_01)
    have h3 : dB1 * (bL * yR) = (bL * dB1) * yR := by
      rw [← Nat.mul_assoc, Nat.mul_comm dB1 bL]
    have h4 : (bL * dB1) * yR ≥ (bL * dT2) * yR := Nat.mul_le_mul_right yR hr2_01
    have h5 : (bL * dT2) * yR = bL * (dT2 * yR) := Nat.mul_assoc bL dT2 yR
    omega
  have hbL_cxR : bL * (cT2 * xR) = bL * (cB1 * xR) := by
    rw [← Nat.mul_assoc, ← hbL_c_eq, Nat.mul_assoc]
  have hbL_r11_v1 := Nat.mul_le_mul_left bL hr11_v1
  simp only [Nat.mul_add] at hbL_r11_v1
  have hbL_yT2_ge : bL * yT2 ≥ bL * yB1 + bL * (dB1 * yB0) := by omega
  have hr2_v0 : aL * xB1 + bL * yB1 + xL ≥ aL * xT2 + bL * yT2 + xL := by
    have h := hw2.2 idx0
    rw [(evalWord2D_two_eq interp .L .B1).2 idx0,
        (evalWord2D_two_eq interp .L .T2).2 idx0] at h
    exact h
  have hxT2_ge : aL * xT2 ≥ aL * (xB0 + xB1) :=
    Nat.mul_le_mul_left aL (by omega : xT2 ≥ xB0 + xB1)
  rw [Nat.mul_add] at hxT2_ge
  have hxB0_0 : xB0 = 0 := by
    by_cases hpos : xB0 ≥ 1
    · have hm := Nat.mul_le_mul_left aL hpos
      dsimp [aL, bL, xL, xB1, yB1, xT2, yT2] at hr2_v0 hbL_yT2_ge hxT2_ge hm ⊢
      omega
    · omega
  have hxT2_le_B1 : xT2 ≤ xB1 := by
    have hsum : aL * xB1 ≥ aL * xT2 := by
      dsimp [aL, bL, xL, xB1, yB1, xT2, yT2] at hr2_v0 hbL_yT2_ge ⊢
      omega
    exact nat_mul_le_cancel_left_w5 aL xT2 xB1 haL hsum
  have hxT2_eq_B1 : xT2 = xB1 := by omega
  have hbL_y_eq : bL * yB1 = bL * yT2 := by
    rw [hxT2_eq_B1] at hr2_v0
    dsimp [aL, bL, xL, xB1, yB1, yT2] at hr2_v0 hbL_yT2_ge ⊢
    omega
  have hbL_dB1_yB0_0 : bL * (dB1 * yB0) = 0 := by omega
  have hr7_v0 : xB0 + xT2 ≥ xT1 + xB0 := by
    have h := hw7.2 idx0
    rw [(evalWord2D_two_eq interp .T2 .B0).2 idx0,
        (evalWord2D_two_eq interp .B0 .T1).2 idx0] at h
    change aT2 * xB0 + (interp .T2).M idx0 idx1 * yB0 + xT2 ≥
      aB0 * xT1 + (interp .B0).M idx0 idx1 * yT1 + xB0 at h
    rw [hbT2, hbB0, haT2_1, haB0_1] at h; omega
  have hr5_v0 : xB0 + xT1 ≥ xT0 + xB1 := by
    have h := hw5.2 idx0
    rw [(evalWord2D_two_eq interp .T1 .B0).2 idx0,
        (evalWord2D_two_eq interp .B1 .T0).2 idx0] at h
    change aT1 * xB0 + (interp .T1).M idx0 idx1 * yB0 + xT1 ≥
      aB1 * xT0 + (interp .B1).M idx0 idx1 * (interp .T0).v idx1 + xB1 at h
    rw [hbT1, hbB1, haT1_1, haB1_1] at h; omega
  have hr9_v0 : xR + xT0 ≥ xR + xB1 := by
    have h := hw9.2 idx0
    rw [(evalWord2D_two_eq interp .T0 .R).2 idx0,
        (evalWord2D_two_eq interp .B1 .R).2 idx0] at h
    change aT0 * xR + (interp .T0).M idx0 idx1 * yR + xT0 ≥
      aB1 * xR + (interp .B1).M idx0 idx1 * yR + xB1 at h
    rw [hbT0, hbB1, haT0_1, haB1_1] at h; omega
  have hxB1_0 : xB1 = 0 := by omega
  have hxT0_0 : xT0 = 0 := by omega
  have hxT1_0 : xT1 = 0 := by omega
  have hxT2_0 : xT2 = 0 := by omega
  have hbL_yB0_0 : bL * yB0 = 0 := by
    by_cases hb0 : bL = 0
    · simp [hb0]
    · have hbL_pos : bL ≥ 1 := by omega
      have hdB0_pos : dB0 ≥ 1 := by
        by_cases hd0 : dB0 = 0
        · rw [hd0, Nat.mul_zero] at hr1_01; omega
        · omega
      by_cases hdB1_0 : dB1 = 0
      · have hdT2_0 : dT2 = 0 := by
          rw [hdB1_0, Nat.mul_zero] at hr2_01
          by_cases hdt : dT2 = 0
          · exact hdt
          · have hm := Nat.mul_le_mul_left bL (by omega : dT2 ≥ 1); omega
        have hr7_11 : dT2 * dB0 ≥ dB0 * dT1 := by
          have h := hw7.1 idx1 idx1
          rw [(evalWord2D_two_eq interp .T2 .B0).1 idx1 idx1,
              (evalWord2D_two_eq interp .B0 .T1).1 idx1 idx1] at h
          change cT2 * (interp .B0).M idx0 idx1 + dT2 * dB0 ≥
            cB0 * (interp .T1).M idx0 idx1 + dB0 * dT1 at h
          rw [hbB0, hbT1] at h; omega
        have hdT1_0 : dT1 = 0 := by
          rw [hdT2_0, Nat.zero_mul] at hr7_11
          by_cases hdt1 : dT1 = 0
          · exact hdt1
          · have hm := Nat.mul_le_mul_left dB0 (by omega : dT1 ≥ 1); omega
        have hr7_v1 : yT2 ≥ dB0 * yT1 + yB0 := by
          have h := hw7.2 idx1
          rw [(evalWord2D_two_eq interp .T2 .B0).2 idx1,
              (evalWord2D_two_eq interp .B0 .T1).2 idx1] at h
          change cT2 * xB0 + dT2 * yB0 + yT2 ≥ cB0 * xT1 + dB0 * yT1 + yB0 at h
          rw [hxB0_0, hxT1_0, hdT2_0] at h; omega
        have hr6_v1 : yT1 ≥ dB0 * yT2 + yB0 := by
          have h := hw6.2 idx1
          rw [(evalWord2D_two_eq interp .T1 .B1).2 idx1,
              (evalWord2D_two_eq interp .B0 .T2).2 idx1] at h
          change (interp .T1).M idx1 idx0 * xB1 + dT1 * yB1 + yT1 ≥
            cB0 * xT2 + dB0 * yT2 + yB0 at h
          rw [hxB1_0, hxT2_0, hdT1_0] at h; omega
        have hge1 : dB0 * yT1 ≥ yT1 := by
          have hm := Nat.mul_le_mul_right yT1 hdB0_pos; omega
        have hge2 : dB0 * yT2 ≥ yT2 := by
          have hm := Nat.mul_le_mul_right yT2 hdB0_pos; omega
        have hyB0_0 : yB0 = 0 := by omega
        simp [hyB0_0]
      · have hdB1_pos : dB1 ≥ 1 := by omega
        by_cases hy0 : yB0 = 0
        · simp [hy0]
        · have hm1 : dB1 * yB0 ≥ 1 := Nat.mul_le_mul hdB1_pos (by omega : yB0 ≥ 1)
          have hm2 : bL * (dB1 * yB0) ≥ 1 := Nat.mul_le_mul hbL_pos hm1
          omega
  intro r hr
  simp only [s9RuleList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [(evalWord2D_two_eq interp .L .B0).2 idx0,
        (evalWordNatAffineDim_singleton_eq 2 interp .L).2 idx0]
    change aL * xB0 + bL * yB0 + xL = xL
    rw [hxB0_0, hbL_yB0_0]; omega
  · rw [(evalWord2D_two_eq interp .L .B1).2 idx0, (evalWord2D_two_eq interp .L .T2).2 idx0]
    change aL * xB1 + bL * yB1 + xL = aL * xT2 + bL * yT2 + xL
    rw [hxB1_0, hxT2_0, hbL_y_eq]
  · rw [(evalWord2D_two_eq interp .T0 .B1).2 idx0, (evalWord2D_two_eq interp .B1 .T1).2 idx0]
    change aT0 * xB1 + (interp .T0).M idx0 idx1 * yB1 + xT0 =
      aB1 * xT1 + (interp .B1).M idx0 idx1 * yT1 + xB1
    rw [hbT0, hbB1, hxB1_0, hxT0_0, hxT1_0]; omega
  · rw [(evalWord2D_two_eq interp .T1 .B0).2 idx0, (evalWord2D_two_eq interp .B1 .T0).2 idx0]
    change aT1 * xB0 + (interp .T1).M idx0 idx1 * yB0 + xT1 =
      aB1 * xT0 + (interp .B1).M idx0 idx1 * (interp .T0).v idx1 + xB1
    rw [hbT1, hbB1, hxB0_0, hxT1_0, hxT0_0, hxB1_0]; omega
  · rw [(evalWord2D_two_eq interp .T1 .B1).2 idx0, (evalWord2D_two_eq interp .B0 .T2).2 idx0]
    change aT1 * xB1 + (interp .T1).M idx0 idx1 * yB1 + xT1 =
      aB0 * xT2 + (interp .B0).M idx0 idx1 * yT2 + xB0
    rw [hbT1, hbB0, hxB1_0, hxT1_0, hxT2_0, hxB0_0]; omega
  · rw [(evalWord2D_two_eq interp .T2 .B0).2 idx0, (evalWord2D_two_eq interp .B0 .T1).2 idx0]
    change aT2 * xB0 + (interp .T2).M idx0 idx1 * yB0 + xT2 =
      aB0 * xT1 + (interp .B0).M idx0 idx1 * yT1 + xB0
    rw [hbT2, hbB0, hxB0_0, hxT2_0, hxT1_0]; omega
  · rw [(evalWord2D_two_eq interp .T0 .R).2 idx0, (evalWord2D_two_eq interp .B1 .R).2 idx0]
    change aT0 * xR + (interp .T0).M idx0 idx1 * yR + xT0 =
      aB1 * xR + (interp .B1).M idx0 idx1 * yR + xB1
    rw [hbT0, hbB1, haT0_1, haB1_1, hxT0_0, hxB1_0]
  · rw [(evalWord2D_two_eq interp .T1 .R).2 idx0,
        (evalWord2D_three_eq interp .B0 .B0 .R).2 idx0,
        (evalWord2D_two_eq interp .B0 .R).2 idx0]
    change aT1 * xR + (interp .T1).M idx0 idx1 * yR + xT1 =
      aB0 * (aB0 * xR + (interp .B0).M idx0 idx1 * yR + xB0) +
      (interp .B0).M idx0 idx1 * (evalWordNatAffineDim 2 interp [.B0, .R]).v idx1 + xB0
    simp only [hbT1, hbB0, haT1_1, haB0_1, hxT1_0, hxB0_0, Nat.zero_mul, Nat.one_mul, Nat.add_zero]
  · rw [(evalWord2D_two_eq interp .T2 .R).2 idx0,
        (evalWord2D_three_eq interp .B1 .B0 .R).2 idx0,
        (evalWord2D_two_eq interp .B0 .R).2 idx0]
    change aT2 * xR + (interp .T2).M idx0 idx1 * yR + xT2 =
      aB1 * (aB0 * xR + (interp .B0).M idx0 idx1 * yR + xB0) +
      (interp .B1).M idx0 idx1 * (evalWordNatAffineDim 2 interp [.B0, .R]).v idx1 + xB1
    simp only [hbT2, hbB1, hbB0, haT2_1, haB1_1, haB0_1, hxT2_0, hxB0_0, hxB1_0,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero]

/--
  Theorem W9.1g (`s9_d2_boundary_nontri_and_parikh_syzygy_obstruction`, `zero custom axioms`):
  Universal `∀ k : Nat` Parikh / `1D`-Affine Syzygy & `2D` Boundary-Coupled Interior-Lower-Triangular
  `ω^k` Tower Impossibility on Swap-Free `S9 = all11 \ {R3, R8}`:
  1. **Exact Parikh Syzygy Collapse (`Z_int = R4+R5+R6+R7`, `Z_9 = R2+R5+R6+2·R7+R9`,
     `Z_11 = R1+R2+R11`, `Z_10 = R1+R2+R4+R5+R7+R10`)**:
     Every nonnegative symbol weight `wt : MixedSRSSym -> Nat` weakly orienting `s9RuleList`
     satisfies `evalParikh1D wt r.1 = evalParikh1D wt r.2` identically across ALL `9/9` rules of `S9`,
     refuting EVERY `k`-level Parikh rule-removal tower (`¬ OmegaParikhRuleRemovalTower k s9RuleList`)
     and EVERY `k`-level `1D` natural-affine tower (`¬ OmegaAffineRuleRemovalTower k s9RuleList`)!
  2. **Universal `2D` Boundary-Coupled (`L, R` Unrestricted Full `2 x 2` Non-Triangular)
     Interior-Lower-Triangular `ω^k` Tower Impossibility (`∀ k : Nat`)**:
     Even when boundary markers `L` and `R` carry **completely arbitrary full `2 x 2` non-triangular
     `Nat` matrices** (`(interp .L).M 0 1 ≥ 0` coupling `v_1` into `v_0` and `(interp .R).M ≥ 0`
     unrestricted!), ANY `2D` Hofbauer–Waldmann interpretation whose 5 interior symbols
     `{B0, B1, T0, T1, T2}` are lower-triangular (`(interp s).M 0 1 = 0`) and weakly orient `s9RuleList`
     satisfies `(evalWordNatAffineDim 2 interp r.1).v 0 = (evalWordNatAffineDim 2 interp r.2).v 0`
     across ALL `9/9` rules of `S9`, refuting `OmegaInteriorLowerTri2DTower k s9RuleList` and
     `OmegaInteriorLowerTri2DTower k all11RuleList` for EVERY finite tower height `k : Nat`!
-/
theorem s9_d2_boundary_nontri_and_parikh_syzygy_obstruction :
    (∀ wt : MixedSRSSym -> Nat,
      (∀ r ∈ s9RuleList, evalParikh1D wt r.1 ≥ evalParikh1D wt r.2) ->
      ∀ r ∈ s9RuleList, evalParikh1D wt r.1 = evalParikh1D wt r.2) ∧
    (∀ k : Nat,
      ¬ OmegaParikhRuleRemovalTower k s9RuleList ∧
      ¬ OmegaAffineRuleRemovalTower k s9RuleList) ∧
    (∀ interp : MixedSRSSym -> NatAffineDim 2,
      (∀ s : MixedSRSSym, (interp s).M ⟨0, by decide⟩ ⟨0, by decide⟩ ≥ 1) ->
      (∀ s : MixedSRSSym, isInteriorMixedSym s = true ->
        (interp s).M ⟨0, by decide⟩ ⟨1, by decide⟩ = 0) ->
      (∀ r ∈ s9RuleList, weakOrientsNatAffineDim 2
        (evalWordNatAffineDim 2 interp r.1) (evalWordNatAffineDim 2 interp r.2)) ->
      ∀ r ∈ s9RuleList,
        (evalWordNatAffineDim 2 interp r.1).v ⟨0, by decide⟩ =
        (evalWordNatAffineDim 2 interp r.2).v ⟨0, by decide⟩) ∧
    (∀ k : Nat,
      ¬ OmegaInteriorLowerTri2DTower k s9RuleList ∧
      ¬ OmegaInteriorLowerTri2DTower k all11RuleList) := by
  have hpar_eq : ∀ wt : MixedSRSSym -> Nat,
      (∀ r ∈ s9RuleList, evalParikh1D wt r.1 ≥ evalParikh1D wt r.2) ->
      ∀ r ∈ s9RuleList, evalParikh1D wt r.1 = evalParikh1D wt r.2 := by
    intro wt hweak
    have hw1 := hweak ([.L, .B0], [.L]) (by decide)
    have hw2 := hweak ([.L, .B1], [.L, .T2]) (by decide)
    have hw4 := hweak ([.T0, .B1], [.B1, .T1]) (by decide)
    have hw5 := hweak ([.T1, .B0], [.B1, .T0]) (by decide)
    have hw6 := hweak ([.T1, .B1], [.B0, .T2]) (by decide)
    have hw7 := hweak ([.T2, .B0], [.B0, .T1]) (by decide)
    have hw9 := hweak ([.T0, .R], [.B1, .R]) (by decide)
    have hw10 := hweak ([.T1, .R], [.B0, .B0, .R]) (by decide)
    have hw11 := hweak ([.T2, .R], [.B1, .B0, .R]) (by decide)
    simp only [evalParikh1D, Nat.add_zero] at hw1 hw2 hw4 hw5 hw6 hw7 hw9 hw10 hw11
    intro r hr
    simp only [s9RuleList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [evalParikh1D, Nat.add_zero] <;> omega
  refine ⟨hpar_eq, ?_, s9_d2_interior_lower_tri_level_collapse, ?_⟩
  · have hpar_imp : ∀ (k : Nat) (rules : List (List MixedSRSSym × List MixedSRSSym)),
        (∀ r ∈ s9RuleList, r ∈ rules) -> ¬ OmegaParikhRuleRemovalTower k rules := by
      intro k
      induction k with
      | zero =>
        intro rules hsub h0
        rw [OmegaParikhRuleRemovalTower] at h0; subst h0
        exact List.not_mem_nil (hsub ([.L, .B0], [.L]) (by decide))
      | succ k' ih =>
        intro rules hsub hsucc
        rcases hsucc with rfl | ⟨rem, wt, hweak, hkeep, hrem⟩
        · exact List.not_mem_nil (hsub ([.L, .B0], [.L]) (by decide))
        · have heq := hpar_eq wt (fun r hr => hweak r (hsub r hr))
          exact ih rem (fun r hr => hkeep r (hsub r hr) (by rw [heq r hr]; exact Nat.lt_irrefl _)) hrem
    have haff_imp : ∀ (k : Nat) (rules : List (List MixedSRSSym × List MixedSRSSym)),
        (∀ r ∈ s9RuleList, r ∈ rules) -> ¬ OmegaAffineRuleRemovalTower k rules := by
      intro k
      induction k with
      | zero =>
        intro rules hsub h0
        rw [OmegaAffineRuleRemovalTower] at h0; subst h0
        exact List.not_mem_nil (hsub ([.L, .B0], [.L]) (by decide))
      | succ k' ih =>
        intro rules hsub hsucc
        rcases hsucc with rfl | ⟨rem, interp, hpos, hweak, hkeep, hrem⟩
        · exact List.not_mem_nil (hsub ([.L, .B0], [.L]) (by decide))
        · have hw1 := hweak ([.L, .B0], [.L]) (hsub _ (by decide))
          have hw2 := hweak ([.L, .B1], [.L, .T2]) (hsub _ (by decide))
          have hw4 := hweak ([.T0, .B1], [.B1, .T1]) (hsub _ (by decide))
          have hw5 := hweak ([.T1, .B0], [.B1, .T0]) (hsub _ (by decide))
          have hw6 := hweak ([.T1, .B1], [.B0, .T2]) (hsub _ (by decide))
          have hw7 := hweak ([.T2, .B0], [.B0, .T1]) (hsub _ (by decide))
          have hw9 := hweak ([.T0, .R], [.B1, .R]) (hsub _ (by decide))
          have hw10 := hweak ([.T1, .R], [.B0, .B0, .R]) (hsub _ (by decide))
          have hw11 := hweak ([.T2, .R], [.B1, .B0, .R]) (hsub _ (by decide))
          simp only [evalWordAffine1D, weakOrients1D, Nat.mul_one, Nat.mul_zero, Nat.add_zero]
            at hw1 hw2 hw4 hw5 hw6 hw7 hw9 hw10 hw11
          have hmL := hpos .L
          have hmR := hpos .R
          have hmB0 := hpos .B0
          have hmB1 := hpos .B1
          have hmT0 := hpos .T0
          have hmT1 := hpos .T1
          have hmT2 := hpos .T2
          have hB1_ge_T2 : (interp .B1).m ≥ (interp .T2).m :=
            nat_mul_le_cancel_left_w5 (interp .L).m (interp .T2).m (interp .B1).m hmL hw2.1
          have hT2_ge_B1B0 : (interp .T2).m ≥ (interp .B1).m * (interp .B0).m := by
            have h11 : (interp .T2).m * (interp .R).m ≥ ((interp .B1).m * (interp .B0).m) * (interp .R).m := by
              rw [Nat.mul_assoc]; exact hw11.1
            exact nat_mul_le_cancel_right_w5 (interp .R).m ((interp .B1).m * (interp .B0).m) (interp .T2).m hmR h11
          have hmB0_1 : (interp .B0).m = 1 := by
            by_cases hgt : (interp .B0).m ≥ 2
            · have hm := Nat.mul_le_mul_left (interp .B1).m hgt; omega
            · omega
          have hmT2_eq_B1 : (interp .T2).m = (interp .B1).m := by
            rw [hmB0_1, Nat.mul_one] at hT2_ge_B1B0; omega
          have hmT1_le_B1 : (interp .T1).m ≤ (interp .B1).m := by
            have h7 := hw7.1; rw [hmB0_1, hmT2_eq_B1] at h7; omega
          have hmT0_ge_B1 : (interp .T0).m ≥ (interp .B1).m :=
            nat_mul_le_cancel_right_w5 (interp .R).m (interp .B1).m (interp .T0).m hmR hw9.1
          have hm5 := hw5.1; rw [hmB0_1, Nat.mul_one] at hm5
          have hmB1_1 : (interp .B1).m = 1 := by
            by_cases hgt : (interp .B1).m ≥ 2
            · have hm := Nat.mul_le_mul_right (interp .T0).m hgt; omega
            · omega
          have hmT2_1 : (interp .T2).m = 1 := by omega
          have hmT1_1 : (interp .T1).m = 1 := by omega
          have hmT0_1 : (interp .T0).m = 1 := by rw [hmB1_1, hmT1_1, Nat.one_mul] at hm5; omega
          simp only [hmB0_1, hmB1_1, hmT0_1, hmT1_1, hmT2_1, Nat.one_mul, Nat.mul_one]
            at hw1 hw2 hw4 hw5 hw6 hw7 hw9 hw10 hw11
          have hcB1_ge_T2 : (interp .B1).c ≥ (interp .T2).c :=
            nat_mul_le_cancel_left_w5 (interp .L).m (interp .T2).c (interp .B1).c hmL (by omega)
          have hall : ∀ r ∈ s9RuleList, r ∈ rem := by
            intro r hr
            apply hkeep r (hsub r hr)
            simp only [s9RuleList, List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
              simp only [evalWordAffine1D, strictOrients1D, hmB0_1, hmB1_1, hmT0_1, hmT1_1, hmT2_1,
                Nat.one_mul, Nat.mul_one, Nat.mul_zero, Nat.add_zero] <;>
              rintro ⟨_, hstr2⟩
            · have hc0 : (interp .B0).c = 0 := by omega
              rw [hc0, Nat.mul_zero] at hstr2; omega
            · have hceq : (interp .B1).c = (interp .T2).c := by omega
              rw [hceq] at hstr2; omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
            · omega
          exact ih rem hall hrem
    intro k
    exact ⟨hpar_imp k s9RuleList (fun r hr => hr),
           haff_imp k s9RuleList (fun r hr => hr)⟩
  · have h_imp : ∀ (k : Nat) (rules : List (List MixedSRSSym × List MixedSRSSym)),
        (∀ r ∈ s9RuleList, r ∈ rules) -> ¬ OmegaInteriorLowerTri2DTower k rules := by
      intro k
      induction k with
      | zero =>
        intro rules hsub h0
        rw [OmegaInteriorLowerTri2DTower] at h0; subst h0
        exact List.not_mem_nil (hsub ([.L, .B0], [.L]) (by decide))
      | succ k' ih =>
        intro rules hsub hsucc
        rcases hsucc with rfl | ⟨rem, interp, htop, hint, hweak, hkeep, hrem⟩
        · exact List.not_mem_nil (hsub ([.L, .B0], [.L]) (by decide))
        · have heq := s9_d2_interior_lower_tri_level_collapse interp htop hint
            (fun r hr => hweak r (hsub r hr))
          have hall : ∀ r ∈ s9RuleList, r ∈ rem := by
            intro r hr
            apply hkeep r (hsub r hr)
            intro hstr
            have hgt : (evalWordNatAffineDim 2 interp r.1).v ⟨0, by decide⟩ >
                (evalWordNatAffineDim 2 interp r.2).v ⟨0, by decide⟩ := hstr.2.2
            rw [heq r hr] at hgt
            exact Nat.lt_irrefl _ hgt
          exact ih rem hall hrem
    intro k
    exact ⟨h_imp k s9RuleList (fun r hr => hr),
           h_imp k all11RuleList s9_sub_all11⟩

-- ============================================================================
-- SECTION 2: Front B (Branches P3.3 & P3.4) — Pure-Integer `4 x 4` Single-Base
--            & Two-Base Confluent Schneider–Laurent Closed Forms, Convergent-Cone
--            Non-Vanishing, & Pratt–Lucas Certificates for `p_3` and `p_4`
-- ============================================================================

theorem intDet_four (A : Fin 4 -> Fin 4 -> Int) :
    intDet 4 A =
      A ⟨0, by decide⟩ ⟨0, by decide⟩ * intDet 3 (intSubMat A ⟨0, by decide⟩) -
      A ⟨0, by decide⟩ ⟨1, by decide⟩ * intDet 3 (intSubMat A ⟨1, by decide⟩) +
      A ⟨0, by decide⟩ ⟨2, by decide⟩ * intDet 3 (intSubMat A ⟨2, by decide⟩) -
      A ⟨0, by decide⟩ ⟨3, by decide⟩ * intDet 3 (intSubMat A ⟨3, by decide⟩) := by
  conv => lhs; unfold intDet
  simp only [intSumFin, intSumPrefix,
    show (0 : Nat) < 4 by decide, show (1 : Nat) < 4 by decide,
    show (2 : Nat) < 4 by decide, show (3 : Nat) < 4 by decide, dite_true,
    show ¬ ((1 : Nat) % 2 = 0) by decide, show ((2 : Nat) % 2 = 0) by decide,
    ite_true, ite_false, Int.zero_add, Int.one_mul]
  have hneg : ∀ x y : Int, (-1 : Int) * x * y = -(x * y) := by
    intro x y; rw [Int.mul_assoc (-1 : Int)]; omega
  rw [hneg, hneg]
  omega

/-- Row grids for single-base `[(0,0),(1,0),(2,0),(3,0)]` and two-base `[(0,0),(1,0),(0,1),(1,1)]`. -/
def laurentRowsSingle4 (i : Fin 4) : Nat × Nat :=
  match i.val with
  | 0 => (0, 0)
  | 1 => (1, 0)
  | 2 => (2, 0)
  | _ => (3, 0)

def laurentRowsTwoBase4 (i : Fin 4) : Nat × Nat :=
  match i.val with
  | 0 => (0, 0)
  | 1 => (1, 0)
  | 2 => (0, 1)
  | _ => (1, 1)

def laurentColsT3U1_4 (u : Nat) (j : Fin 4) : Nat × Nat :=
  match j.val with
  | 0 => (0, 0)
  | 1 => (1, 0)
  | 2 => (2, 0)
  | _ => (0, u)

def laurentColsC22_4 (u : Nat) (j : Fin 4) : Nat × Nat :=
  match j.val with
  | 0 => (0, 0)
  | 1 => (1, 0)
  | 2 => (0, u)
  | _ => (1, u)

def laurentSingleT3U1Mat4 (W u : Nat) : Fin 4 -> Fin 4 -> Int :=
  laurentInterpMat W 1 4 laurentRowsSingle4 (laurentColsT3U1_4 u)

def laurentSingleC22Mat4 (W u : Nat) : Fin 4 -> Fin 4 -> Int :=
  laurentInterpMat W 1 4 laurentRowsSingle4 (laurentColsC22_4 u)

def laurentTwoBaseMat4 (W K u : Nat) : Fin 4 -> Fin 4 -> Int :=
  laurentInterpMat W K 4 laurentRowsTwoBase4 (laurentColsC22_4 u)

theorem laurentInterpBinom_zero_right : ∀ n : Nat, laurentInterpBinom n 0 = 1
  | 0 => rfl
  | _ + 1 => rfl

theorem laurentInterpBinom_one_right : ∀ n : Nat, laurentInterpBinom n 1 = n
  | 0 => rfl
  | n + 1 => by
    simp only [laurentInterpBinom, laurentInterpBinom_zero_right n, laurentInterpBinom_one_right n]
    omega

theorem laurentInterpBinom_add_two :
    ∀ x y : Nat,
      laurentInterpBinom (x + y) 2 = laurentInterpBinom x 2 + laurentInterpBinom y 2 + x * y
  | 0, y => by simp [laurentInterpBinom]
  | x + 1, y => by
    rw [Nat.succ_add x y]
    change laurentInterpBinom (x + y) 1 + laurentInterpBinom (x + y) 2 =
      (laurentInterpBinom x 1 + laurentInterpBinom x 2) + laurentInterpBinom y 2 + (x + 1) * y
    rw [laurentInterpBinom_one_right (x + y), laurentInterpBinom_one_right x,
        laurentInterpBinom_add_two x y, Nat.add_mul, Nat.one_mul]
    omega

theorem two_mul_sq_ne_sq_mul_odd :
    ∀ (bound X Y C : Nat),
      X ≤ bound -> X ≥ 1 -> Y ≥ 1 -> C % 2 = 1 ->
      2 * (X * X) ≠ (Y * Y) * C
  | 0, X, _, _, hX, hX1, _, _ => by omega
  | bound + 1, X, Y, C, hX, hX1, hY1, hC_odd => by
    intro heq
    have hY_ev : Y % 2 = 0 := by
      by_cases hYo : Y % 2 = 1
      · have hYY_o : (Y * Y) % 2 = 1 := by rw [Nat.mul_mod, hYo]
        have hr_o : ((Y * Y) * C) % 2 = 1 := by rw [Nat.mul_mod, hYY_o, hC_odd]
        have hl_e : (2 * (X * X)) % 2 = 0 := Nat.mul_mod_right 2 (X * X)
        rw [heq] at hl_e; omega
      · omega
    let Y' := Y / 2
    have hY_eq : Y = 2 * Y' := by dsimp [Y']; omega
    have hY'1 : Y' ≥ 1 := by dsimp [Y']; omega
    have hXX : X * X = 2 * ((Y' * Y') * C) := by
      rw [hY_eq] at heq
      have h4 : (2 * Y') * (2 * Y') * C = 2 * (2 * ((Y' * Y') * C)) := by
        calc
          (2 * Y') * (2 * Y') * C = (2 * (Y' * 2 * Y')) * C := by
            rw [Nat.mul_assoc 2 Y' (2 * Y'), Nat.mul_assoc Y' 2 Y']
          _ = (2 * (2 * (Y' * Y'))) * C := by
            rw [Nat.mul_comm Y' 2, Nat.mul_assoc 2 Y' Y']
          _ = 2 * (2 * ((Y' * Y') * C)) := by rw [Nat.mul_assoc, Nat.mul_assoc]
      rw [h4] at heq
      omega
    have hX_ev : X % 2 = 0 := by
      by_cases hXo : X % 2 = 1
      · have hXX_o : (X * X) % 2 = 1 := by rw [Nat.mul_mod, hXo]
        rw [hXX, Nat.mul_mod_right] at hXX_o; omega
      · omega
    let X' := X / 2
    have hX_eq : X = 2 * X' := by dsimp [X']; omega
    have hX'1 : X' ≥ 1 := by dsimp [X']; omega
    have hX'_le : X' ≤ bound := by dsimp [X']; omega
    have heq' : 2 * (X' * X') = (Y' * Y') * C := by
      rw [hX_eq] at hXX
      have h4 : (2 * X') * (2 * X') = 2 * (2 * (X' * X')) := by
        calc
          (2 * X') * (2 * X') = 2 * (X' * (2 * X')) := Nat.mul_assoc 2 X' (2 * X')
          _ = 2 * (2 * (X' * X')) := by rw [← Nat.mul_assoc X' 2 X', Nat.mul_comm X' 2, Nat.mul_assoc]
      rw [h4] at hXX
      omega
    exact two_mul_sq_ne_sq_mul_odd bound X' Y' C hX'_le hX'1 hY'1 hC_odd heq'

theorem cone_twobase_4x4_strict_ineq :
    ∀ u : Nat, u ≥ 2 ->
      9 * 2 ^ u * (3 ^ u - 1) ^ 2 > 25 * 3 ^ u * (2 ^ u - 1) ^ 2
  | 0, hu => by omega
  | 1, hu => by omega
  | 2, _ => by decide
  | u + 3, _ => by
    let v := u + 2
    have hv : v ≥ 2 := by dsimp [v]; omega
    have ih := cone_twobase_4x4_strict_ineq v hv
    change 9 * 2 ^ (v + 1) * (3 ^ (v + 1) - 1) ^ 2 > 25 * 3 ^ (v + 1) * (2 ^ (v + 1) - 1) ^ 2
    have hp2_ge4 : 2 ^ v ≥ 4 := by simpa using pow2_mono_nat hv
    have hp3_ge9 : 3 ^ v ≥ 9 := by simpa using nat_pow_mono_exp_pos 3 2 v (by decide) hv
    let A := 3 ^ v - 1
    let B := 2 ^ v - 1
    have hB_ge3 : B ≥ 3 := by dsimp [B]; omega
    have h3v1 : 3 ^ (v + 1) - 1 = 3 * A + 2 := by
      dsimp [A]; rw [Nat.pow_succ 3 v]; omega
    have h2v1 : 2 ^ (v + 1) - 1 = 2 * B + 1 := by
      dsimp [B]; rw [Nat.pow_succ 2 v]; omega
    -- `(3 * A + 2)^2 ≥ 9 * A^2`:
    have hA_sq : (3 ^ (v + 1) - 1) ^ 2 ≥ 9 * A ^ 2 := by
      rw [h3v1, Nat.pow_succ _ 1, Nat.pow_one, Nat.pow_succ A 1, Nat.pow_one]
      have hm : (3 * A + 2) * (3 * A + 2) ≥ (3 * A) * (3 * A) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h9 : (3 * A) * (3 * A) = 9 * (A * A) := by
        calc
          (3 * A) * (3 * A) = 3 * (A * 3 * A) := by rw [Nat.mul_assoc 3 A (3 * A), Nat.mul_assoc A 3 A]
          _ = 3 * (3 * (A * A)) := by rw [Nat.mul_comm A 3, Nat.mul_assoc 3 A A]
          _ = 9 * (A * A) := by rw [← Nat.mul_assoc 3 3]
      omega
    -- `3 * (2 * B + 1) ≤ 7 * B` for `B ≥ 3`, so `9 * (2^(v+1) - 1)^2 ≤ 49 * B^2`:
    have hB_lin : 3 * (2 ^ (v + 1) - 1) ≤ 7 * B := by rw [h2v1]; omega
    have hB_sq : 9 * (2 ^ (v + 1) - 1) ^ 2 ≤ 49 * B ^ 2 := by
      have hm := Nat.mul_le_mul hB_lin hB_lin
      have hl : (3 * (2 ^ (v + 1) - 1)) * (3 * (2 ^ (v + 1) - 1)) = 9 * (2 ^ (v + 1) - 1) ^ 2 := by
        rw [Nat.pow_succ _ 1, Nat.pow_one]
        calc
          (3 * (2 ^ (v + 1) - 1)) * (3 * (2 ^ (v + 1) - 1))
              = 3 * ((2 ^ (v + 1) - 1) * 3 * (2 ^ (v + 1) - 1)) := by
                rw [Nat.mul_assoc 3, Nat.mul_assoc _ 3]
          _ = 9 * ((2 ^ (v + 1) - 1) * (2 ^ (v + 1) - 1)) := by
                rw [Nat.mul_comm _ 3, Nat.mul_assoc 3, ← Nat.mul_assoc 3 3]
      have hr : (7 * B) * (7 * B) = 49 * B ^ 2 := by
        rw [Nat.pow_succ B 1, Nat.pow_one]
        calc
          (7 * B) * (7 * B) = 7 * (B * 7 * B) := by rw [Nat.mul_assoc 7, Nat.mul_assoc B 7]
          _ = 49 * (B * B) := by rw [Nat.mul_comm B 7, Nat.mul_assoc 7 B B, ← Nat.mul_assoc 7 7]
      rwa [hl, hr] at hm
    -- Multiply `ih : 9 * 2^v * A^2 > 25 * 3^v * B^2`:
    -- `3 * (9 * 2^(v+1) * (3^(v+1) - 1)^2) ≥ 54 * (9 * 2^v * A^2) > 54 * (25 * 3^v * B^2) ≥ 49 * (25 * 3^v * B^2) ≥ 3 * (25 * 3^(v+1) * (2^(v+1) - 1)^2)`!
    have hlhs_ge : 3 * (9 * 2 ^ (v + 1) * (3 ^ (v + 1) - 1) ^ 2) ≥
        54 * (9 * 2 ^ v * A ^ 2) := by
      rw [Nat.pow_succ 2 v]
      have hm := Nat.mul_le_mul_left (3 * (9 * (2 ^ v * 2))) hA_sq
      have hrew : 3 * (9 * (2 ^ v * 2)) * (9 * A ^ 2) = 54 * (9 * 2 ^ v * A ^ 2) := by
        calc
          3 * (9 * (2 ^ v * 2)) * (9 * A ^ 2)
              = (3 * 2 * 9) * (9 * 2 ^ v) * A ^ 2 := by
                rw [← Nat.mul_assoc (9 : Nat) (2 ^ v) 2, Nat.mul_comm (9 * 2 ^ v) 2,
                    ← Nat.mul_assoc 3 2 (9 * 2 ^ v), ← Nat.mul_assoc (3 * 2 * (9 * 2 ^ v)) 9 (A ^ 2),
                    Nat.mul_assoc (3 * 2) (9 * 2 ^ v) 9, Nat.mul_comm (9 * 2 ^ v) 9,
                    ← Nat.mul_assoc (3 * 2) 9 (9 * 2 ^ v)]
          _ = 54 * (9 * 2 ^ v * A ^ 2) := by rw [Nat.mul_assoc 54]
      rw [hrew, Nat.mul_assoc 3 (9 * (2 ^ v * 2))] at hm
      exact hm
    have hrhs_le : 3 * (25 * 3 ^ (v + 1) * (2 ^ (v + 1) - 1) ^ 2) ≤
        49 * (25 * 3 ^ v * B ^ 2) := by
      rw [Nat.pow_succ 3 v]
      have hm := Nat.mul_le_mul_left (25 * 3 ^ v) hB_sq
      have hl : (25 * 3 ^ v) * (9 * (2 ^ (v + 1) - 1) ^ 2) =
          3 * (25 * (3 ^ v * 3) * (2 ^ (v + 1) - 1) ^ 2) := by
        calc
          (25 * 3 ^ v) * (9 * (2 ^ (v + 1) - 1) ^ 2)
              = ((25 * 3 ^ v) * 9) * (2 ^ (v + 1) - 1) ^ 2 := (Nat.mul_assoc _ _ _).symm
          _ = (3 * (25 * (3 ^ v * 3))) * (2 ^ (v + 1) - 1) ^ 2 := by
                apply congrArg (· * (2 ^ (v + 1) - 1) ^ 2); omega
          _ = 3 * (25 * (3 ^ v * 3) * (2 ^ (v + 1) - 1) ^ 2) := Nat.mul_assoc 3 _ _
      have hr : (25 * 3 ^ v) * (49 * B ^ 2) = 49 * (25 * 3 ^ v * B ^ 2) := by
        rw [← Nat.mul_assoc (25 * 3 ^ v) 49, Nat.mul_comm (25 * 3 ^ v) 49, Nat.mul_assoc]
      rwa [hl, hr] at hm
    change 9 * 2 ^ v * A ^ 2 > 25 * 3 ^ v * B ^ 2 at ih
    generalize 9 * 2 ^ v * A ^ 2 = XL, 25 * 3 ^ v * B ^ 2 = XR,
      9 * 2 ^ (v + 1) * (3 ^ (v + 1) - 1) ^ 2 = YL,
      25 * 3 ^ (v + 1) * (2 ^ (v + 1) - 1) ^ 2 = YR at ih hlhs_ge hrhs_le ⊢
    omega

/--
  Theorem W9.2a (`laurent_4x4_confluent_and_twobase_nonvanishing`, `zero custom axioms`):
  Pure-Integer `4 x 4` Single-Base & Two-Base Confluent Schneider–Laurent Determinant Closed Forms
  and Non-Vanishing Dichotomy:
  1. Single-base Taylor-extrapolated `(T = 3, U = 1)`:
       `intDet 4 (laurentSingleT3U1Mat4 W u) = ((W ^ 3 * (2 ^ u - 1) ^ 3 : Nat) : Int) > 0`;
  2. Single-base confluent `(T = 2, U = 2)`:
       `intDet 4 (laurentSingleC22Mat4 W u) = ((W ^ 2 * 2 ^ u * (2 ^ u - 1) ^ 4 : Nat) : Int) > 0`;
  3. Genuine two-base `(2^r 3^s)^u` `4 x 4`:
       `intDet 4 (laurentTwoBaseMat4 W K u) = ((W ^ 2 * 2 ^ u * (3 ^ u - 1) ^ 2 : Nat) : Int) -
         ((K ^ 2 * 3 ^ u * (2 ^ u - 1) ^ 2 : Nat) : Int)`;
  4. Resonant Zero Counterexample (`LAURENT_TWOBASE_4X4_RESONANT_ZERO_W9_K16_U2`):
       At `(W, K, u) = (9, 16, 2)`, `Nat.gcd 9 16 = 1`, `3 ^ 9 < 2 ^ 16`, AND
       `intDet 4 (laurentTwoBaseMat4 9 16 2) = 0`;
  5. Universal Odd-`u` Non-Vanishing (`∀ W, K ≥ 1, ∀ m : Nat`):
       `intDet 4 (laurentTwoBaseMat4 W K (2 * m + 1)) ≠ 0`;
  6. Universal Collatz Convergent-Cone Non-Vanishing (`∀ W, K, u ≥ 1` with `3 * K ≤ 5 * W`):
       `intDet 4 (laurentTwoBaseMat4 W K u) ≠ 0` AND (`u ≥ 2 -> intDet 4 ... > 0`)!
-/
theorem laurent_4x4_confluent_and_twobase_nonvanishing :
    (∀ W u : Nat, W ≥ 1 -> u ≥ 1 ->
      intDet 4 (laurentSingleT3U1Mat4 W u) = ((W ^ 3 * (2 ^ u - 1) ^ 3 : Nat) : Int) ∧
      intDet 4 (laurentSingleT3U1Mat4 W u) > 0) ∧
    (∀ W u : Nat, W ≥ 1 -> u ≥ 1 ->
      intDet 4 (laurentSingleC22Mat4 W u) = ((W ^ 2 * 2 ^ u * (2 ^ u - 1) ^ 4 : Nat) : Int) ∧
      intDet 4 (laurentSingleC22Mat4 W u) > 0) ∧
    (∀ W K u : Nat, W ≥ 1 -> K ≥ 1 -> u ≥ 1 ->
      intDet 4 (laurentTwoBaseMat4 W K u) =
        ((W ^ 2 * 2 ^ u * (3 ^ u - 1) ^ 2 : Nat) : Int) -
        ((K ^ 2 * 3 ^ u * (2 ^ u - 1) ^ 2 : Nat) : Int)) ∧
    (Nat.gcd 9 16 = 1 ∧ 3 ^ 9 < 2 ^ 16 ∧ intDet 4 (laurentTwoBaseMat4 9 16 2) = 0) ∧
    (∀ W K m : Nat, W ≥ 1 -> K ≥ 1 ->
      intDet 4 (laurentTwoBaseMat4 W K (2 * m + 1)) ≠ 0) ∧
    (∀ W K u : Nat, W ≥ 1 -> K ≥ 1 -> 3 * K ≤ 5 * W -> u ≥ 1 ->
      intDet 4 (laurentTwoBaseMat4 W K u) ≠ 0 ∧
      (u ≥ 2 -> intDet 4 (laurentTwoBaseMat4 W K u) > 0)) := by
  have hpow2_2u : ∀ u : Nat, 2 ^ (2 * u) = 2 ^ u * 2 ^ u := fun u => by
    rw [Nat.two_mul, Nat.pow_add]
  have hpow2_3u : ∀ u : Nat, 2 ^ (3 * u) = 2 ^ u * 2 ^ u * 2 ^ u := fun u => by
    rw [show 3 * u = u + u + u by omega, Nat.pow_add, Nat.pow_add]
  -- Helper closed form for `laurentTwoBaseMat4 W K u`:
  have hdet_tb : ∀ W K u : Nat, W ≥ 1 -> K ≥ 1 -> u ≥ 1 ->
      intDet 4 (laurentTwoBaseMat4 W K u) =
        ((W ^ 2 * 2 ^ u * (3 ^ u - 1) ^ 2 : Nat) : Int) -
        ((K ^ 2 * 3 ^ u * (2 ^ u - 1) ^ 2 : Nat) : Int) := by
    intro W K u _ _ hu
    let M0 := laurentTwoBaseMat4 W K u
    let c0 : Fin 4 := ⟨0, by decide⟩
    let c1 : Fin 4 := ⟨1, by decide⟩
    let c2 : Fin 4 := ⟨2, by decide⟩
    let c3 : Fin 4 := ⟨3, by decide⟩
    let M1 : Fin 4 -> Fin 4 -> Int := fun i j => if j = c2 then M0 i c2 - 1 * M0 i c0 else M0 i j
    let M2 : Fin 4 -> Fin 4 -> Int := fun i j => if j = c3 then M1 i c3 - 1 * M1 i c1 else M1 i j
    have hd1 : intDet 4 M0 = intDet 4 M1 := (intDet_sub_col_mul_other 4 c2 c0 (by decide) 1 M0).symm
    have hd2 : intDet 4 M1 = intDet 4 M2 := (intDet_sub_col_mul_other 4 c3 c1 (by decide) 1 M1).symm
    change intDet 4 M0 = _
    rw [hd1, hd2, intDet_four M2]
    have hr00 : M2 ⟨0, by decide⟩ ⟨0, by decide⟩ = 1 := by
      simp [M2, M1, M0, c0, c1, c2, c3, laurentTwoBaseMat4, laurentInterpMat,
            laurentRowsTwoBase4, laurentColsC22_4, laurentInterpEntry, laurentInterpBinom]
    have hr01 : M2 ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 := by
      simp [M2, M1, M0, c0, c1, c2, c3, laurentTwoBaseMat4, laurentInterpMat,
            laurentRowsTwoBase4, laurentColsC22_4, laurentInterpEntry, laurentInterpBinom]
    have hr02 : M2 ⟨0, by decide⟩ ⟨2, by decide⟩ = 0 := by
      simp [M2, M1, M0, c0, c1, c2, c3, laurentTwoBaseMat4, laurentInterpMat,
            laurentRowsTwoBase4, laurentColsC22_4, laurentInterpEntry, laurentInterpBinom]
    have hr03 : M2 ⟨0, by decide⟩ ⟨3, by decide⟩ = 0 := by
      simp [M2, M1, M0, c0, c1, c2, c3, laurentTwoBaseMat4, laurentInterpMat,
            laurentRowsTwoBase4, laurentColsC22_4, laurentInterpEntry, laurentInterpBinom]
    rw [hr00, hr01, hr02, hr03]
    simp only [Int.one_mul, Int.zero_mul, Int.sub_zero, Int.add_zero]
    let S3 := intSubMat M2 ⟨0, by decide⟩
    change intDet 3 S3 = _
    rw [intDet_three S3]
    let P : Nat := 2 ^ u
    let Q : Nat := 3 ^ u
    have hP_ge2 : P ≥ 2 := by dsimp [P]; simpa using pow2_mono_nat hu
    have hQ_ge3 : Q ≥ 3 := by
      dsimp [Q]; rw [show u = 1 + (u - 1) by omega, Nat.pow_add, Nat.pow_one]
      have hp := pow3_pos_nat (u - 1); omega
    let p : Int := (P : Int) - 1
    let q : Int := (Q : Int) - 1
    let w : Int := (W : Int)
    let k : Int := (K : Int)
    let S : Int := p * q + p + q
    have hP_p1 : (P : Int) = p + 1 := by dsimp [p]; omega
    have hQ_q1 : (Q : Int) = q + 1 := by dsimp [q]; omega
    have hPQ_sub : (P : Int) * (Q : Int) - 1 = S := by
      dsimp [S]
      rw [hP_p1, hQ_q1, Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one]
      omega
    have hs00 : S3 ⟨0, by decide⟩ ⟨0, by decide⟩ = w := by
      simp [S3, intSubMat, skipFinIdx, M2, M1, M0, c0, c1, c2, c3, w, laurentTwoBaseMat4,
            laurentInterpMat, laurentRowsTwoBase4, laurentColsC22_4, laurentInterpEntry,
            laurentInterpBinom_one_right]
    have hs01 : S3 ⟨0, by decide⟩ ⟨1, by decide⟩ = p := by
      simp [S3, intSubMat, skipFinIdx, M2, M1, M0, c0, c1, c2, c3, p, P, laurentTwoBaseMat4,
            laurentInterpMat, laurentRowsTwoBase4, laurentColsC22_4, laurentInterpEntry,
            laurentInterpBinom_zero_right]
    have hs02 : S3 ⟨0, by decide⟩ ⟨2, by decide⟩ = w * p := by
      simp [S3, intSubMat, skipFinIdx, M2, M1, M0, c0, c1, c2, c3, w, p, P, laurentTwoBaseMat4,
            laurentInterpMat, laurentRowsTwoBase4, laurentColsC22_4, laurentInterpEntry,
            laurentInterpBinom_one_right, Int.mul_sub]
    have hs10 : S3 ⟨1, by decide⟩ ⟨0, by decide⟩ = k := by
      simp [S3, intSubMat, skipFinIdx, M2, M1, M0, c0, c1, c2, c3, k, laurentTwoBaseMat4,
            laurentInterpMat, laurentRowsTwoBase4, laurentColsC22_4, laurentInterpEntry,
            laurentInterpBinom_one_right]
    have hs11 : S3 ⟨1, by decide⟩ ⟨1, by decide⟩ = q := by
      simp [S3, intSubMat, skipFinIdx, M2, M1, M0, c0, c1, c2, c3, q, Q, laurentTwoBaseMat4,
            laurentInterpMat, laurentRowsTwoBase4, laurentColsC22_4, laurentInterpEntry,
            laurentInterpBinom_zero_right]
    have hs12 : S3 ⟨1, by decide⟩ ⟨2, by decide⟩ = k * q := by
      simp [S3, intSubMat, skipFinIdx, M2, M1, M0, c0, c1, c2, c3, k, q, Q, laurentTwoBaseMat4,
            laurentInterpMat, laurentRowsTwoBase4, laurentColsC22_4, laurentInterpEntry,
            laurentInterpBinom_one_right, Int.mul_sub]
    have hs20 : S3 ⟨2, by decide⟩ ⟨0, by decide⟩ = w + k := by
      simp [S3, intSubMat, skipFinIdx, M2, M1, M0, c0, c1, c2, c3, w, k, laurentTwoBaseMat4,
            laurentInterpMat, laurentRowsTwoBase4, laurentColsC22_4, laurentInterpEntry,
            laurentInterpBinom_one_right]
    have hs21 : S3 ⟨2, by decide⟩ ⟨1, by decide⟩ = S := by
      have hm : S3 ⟨2, by decide⟩ ⟨1, by decide⟩ = (P : Int) * (Q : Int) - 1 := by
        simp [S3, intSubMat, skipFinIdx, M2, M1, M0, c0, c1, c2, c3, P, Q, laurentTwoBaseMat4,
              laurentInterpMat, laurentRowsTwoBase4, laurentColsC22_4, laurentInterpEntry,
              laurentInterpBinom_zero_right]
      exact hm.trans hPQ_sub
    have hs22 : S3 ⟨2, by decide⟩ ⟨2, by decide⟩ = (w + k) * S := by
      have hm : S3 ⟨2, by decide⟩ ⟨2, by decide⟩ =
          (((W + K) * P * Q : Nat) : Int) - ((W + K : Nat) : Int) := by
        simp [S3, intSubMat, skipFinIdx, M2, M1, M0, c0, c1, c2, c3, P, Q, laurentTwoBaseMat4,
              laurentInterpMat, laurentRowsTwoBase4, laurentColsC22_4, laurentInterpEntry,
              laurentInterpBinom_one_right]
      have hcast : (((W + K) * P * Q : Nat) : Int) = (w + k) * ((P : Int) * (Q : Int)) := by
        rw [natCast_mul ((W + K) * P) Q, natCast_mul (W + K) P, Int.mul_assoc]
        rfl
      have hcast1 : ((W + K : Nat) : Int) = w + k := rfl
      rw [hm, hcast, hcast1, ← hPQ_sub, Int.mul_sub, Int.mul_one]
    rw [hs00, hs01, hs02, hs10, hs11, hs12, hs20, hs21, hs22]
    have hrhs_cast :
        ((W ^ 2 * 2 ^ u * (3 ^ u - 1) ^ 2 : Nat) : Int) -
        ((K ^ 2 * 3 ^ u * (2 ^ u - 1) ^ 2 : Nat) : Int) =
        w * w * (p + 1) * (q * q) - k * k * (q + 1) * (p * p) := by
      have hw2 : ((W ^ 2 : Nat) : Int) = w * w := by
        rw [Nat.pow_succ W 1, Nat.pow_one, natCast_mul]
      have hk2 : ((K ^ 2 : Nat) : Int) = k * k := by
        rw [Nat.pow_succ K 1, Nat.pow_one, natCast_mul]
      have hq2 : (((3 ^ u - 1) ^ 2 : Nat) : Int) = q * q := by
        change (((Q - 1) ^ 2 : Nat) : Int) = q * q
        rw [Nat.pow_succ _ 1, Nat.pow_one, natCast_mul]
        have hqm : ((Q - 1 : Nat) : Int) = q := by dsimp [q]; omega
        rw [hqm]
      have hp2 : (((2 ^ u - 1) ^ 2 : Nat) : Int) = p * p := by
        change (((P - 1) ^ 2 : Nat) : Int) = p * p
        rw [Nat.pow_succ _ 1, Nat.pow_one, natCast_mul]
        have hpm : ((P - 1 : Nat) : Int) = p := by dsimp [p]; omega
        rw [hpm]
      rw [natCast_mul (W ^ 2 * 2 ^ u), natCast_mul (W ^ 2) (2 ^ u),
          natCast_mul (K ^ 2 * 3 ^ u), natCast_mul (K ^ 2) (3 ^ u),
          hw2, hk2, hq2, hp2]
      change w * w * (P : Int) * (q * q) - k * k * (Q : Int) * (p * p) = _
      rw [hP_p1, hQ_q1]
    rw [hrhs_cast]
    -- Pure 4-line polynomial identity on `(w, k, p, q)`:
    let T := p * q + p
    have hS_T : S = T + q := rfl
    have hc1 : q * ((w + k) * S) - (k * q) * S = w * (q * S) := by
      rw [Int.add_mul w k S, Int.mul_add q (w * S) (k * S),
          ← Int.mul_assoc q w S, Int.mul_comm q w, Int.mul_assoc w q S,
          ← Int.mul_assoc q k S, Int.mul_comm q k]
      omega
    have hc2 : k * ((w + k) * S) - (k * q) * (w + k) = (w + k) * (k * T) := by
      rw [hS_T, Int.mul_add (w + k) T q, Int.mul_add k ((w + k) * T) ((w + k) * q),
          ← Int.mul_assoc k (w + k) T, Int.mul_comm k (w + k), Int.mul_assoc (w + k) k T,
          ← Int.mul_assoc k (w + k) q, Int.mul_comm k (w + k), Int.mul_assoc (w + k) k q,
          Int.mul_comm (k * q) (w + k)]
      omega
    have hc3 : k * S - q * (w + k) = k * T - w * q := by
      rw [hS_T, Int.mul_add k T q, Int.mul_add q w k, Int.mul_comm q k, Int.mul_comm q w]
      omega
    rw [hc1, hc2, hc3]
    have hmid : p * ((w + k) * (k * T)) = (w * p) * (k * T) + (k * k) * (p * T) := by
      rw [Int.add_mul w k (k * T), Int.mul_add p (w * (k * T)) (k * (k * T)),
          ← Int.mul_assoc p w (k * T), Int.mul_comm p w,
          ← Int.mul_assoc p k (k * T), Int.mul_comm p k,
          Int.mul_assoc k p (k * T), ← Int.mul_assoc p k T, Int.mul_comm p k,
          Int.mul_assoc k p T, ← Int.mul_assoc k k (p * T)]
    have hlast : (w * p) * (k * T - w * q) = (w * p) * (k * T) - (w * w) * (p * q) := by
      rw [Int.mul_sub (w * p) (k * T) (w * q),
          Int.mul_assoc w p (w * q), ← Int.mul_assoc p w q, Int.mul_comm p w,
          Int.mul_assoc w p q, ← Int.mul_assoc w w (p * q)]
    have hfirst : w * (w * (q * S)) - (w * w) * (p * q) = w * w * (p + 1) * (q * q) := by
      have hqS : q * S - p * q = (p + 1) * (q * q) := by
        dsimp [S]
        rw [Int.mul_add q (p * q + p) q, Int.mul_add q (p * q) p,
            ← Int.mul_assoc q p q, Int.mul_comm q p, Int.mul_assoc p q q,
            Int.add_mul p 1 (q * q), Int.one_mul]
        omega
      rw [← Int.mul_assoc w w (q * S), ← Int.mul_sub (w * w) (q * S) (p * q),
          hqS, ← Int.mul_assoc (w * w) (p + 1) (q * q)]
    have hpT : (k * k) * (p * T) = k * k * (q + 1) * (p * p) := by
      have hpT_eq : p * T = (q + 1) * (p * p) := by
        dsimp [T]
        rw [Int.mul_add p (p * q) p, ← Int.mul_assoc p p q, Int.mul_comm (p * p) q,
            Int.add_mul q 1 (p * p), Int.one_mul]
      rw [hpT_eq, ← Int.mul_assoc (k * k) (q + 1) (p * p)]
    rw [hmid, hlast, ← hfirst, ← hpT]
    omega
  refine ⟨?_, ?_, hdet_tb, ?_, ?_, ?_⟩
  · -- Part 1: Single-base `(T = 3, U = 1)` closed form `W^3 * (2^u - 1)^3 > 0`:
    intro W u hW hu
    let M0 := laurentSingleT3U1Mat4 W u
    let c0 : Fin 4 := ⟨0, by decide⟩
    let c3 : Fin 4 := ⟨3, by decide⟩
    let M1 : Fin 4 -> Fin 4 -> Int := fun i j => if j = c3 then M0 i c3 - 1 * M0 i c0 else M0 i j
    have hd1 : intDet 4 M0 = intDet 4 M1 := (intDet_sub_col_mul_other 4 c3 c0 (by decide) 1 M0).symm
    have hdet_val : intDet 4 M0 = ((W ^ 3 * (2 ^ u - 1) ^ 3 : Nat) : Int) := by
      rw [hd1, intDet_four M1]
      have hr00 : M1 ⟨0, by decide⟩ ⟨0, by decide⟩ = 1 := by
        simp [M1, M0, c0, c3, laurentSingleT3U1Mat4, laurentInterpMat,
              laurentRowsSingle4, laurentColsT3U1_4, laurentInterpEntry, laurentInterpBinom]
      have hr01 : M1 ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 := by
        simp [M1, M0, c0, c3, laurentSingleT3U1Mat4, laurentInterpMat,
              laurentRowsSingle4, laurentColsT3U1_4, laurentInterpEntry, laurentInterpBinom]
      have hr02 : M1 ⟨0, by decide⟩ ⟨2, by decide⟩ = 0 := by
        simp [M1, M0, c0, c3, laurentSingleT3U1Mat4, laurentInterpMat,
              laurentRowsSingle4, laurentColsT3U1_4, laurentInterpEntry, laurentInterpBinom]
      have hr03 : M1 ⟨0, by decide⟩ ⟨3, by decide⟩ = 0 := by
        simp [M1, M0, c0, c3, laurentSingleT3U1Mat4, laurentInterpMat,
              laurentRowsSingle4, laurentColsT3U1_4, laurentInterpEntry, laurentInterpBinom]
      rw [hr00, hr01, hr02, hr03]
      simp only [Int.one_mul, Int.zero_mul, Int.sub_zero, Int.add_zero]
      let S3 := intSubMat M1 ⟨0, by decide⟩
      change intDet 3 S3 = _
      rw [intDet_three S3]
      let Z : Nat := 2 ^ u
      have hZ_ge2 : Z ≥ 2 := by dsimp [Z]; simpa using pow2_mono_nat hu
      let p : Int := (Z : Int) - 1
      let w : Int := (W : Int)
      let B : Int := (laurentInterpBinom W 2 : Int)
      have hZ_p1 : (Z : Int) = p + 1 := by dsimp [p]; omega
      have hb_2W : laurentInterpBinom (2 * W) 2 = 2 * laurentInterpBinom W 2 + W * W := by
        rw [Nat.two_mul, laurentInterpBinom_add_two W W]; omega
      have hb_3W : laurentInterpBinom (3 * W) 2 = 3 * laurentInterpBinom W 2 + 3 * (W * W) := by
        rw [show 3 * W = 2 * W + W by omega, laurentInterpBinom_add_two (2 * W) W, hb_2W]
        rw [Nat.two_mul W, Nat.add_mul W W W]; omega
      have hs00 : S3 ⟨0, by decide⟩ ⟨0, by decide⟩ = w := by
        simp [S3, intSubMat, skipFinIdx, M1, M0, c0, c3, w, laurentSingleT3U1Mat4,
              laurentInterpMat, laurentRowsSingle4, laurentColsT3U1_4, laurentInterpEntry,
              laurentInterpBinom_one_right]
      have hs01 : S3 ⟨0, by decide⟩ ⟨1, by decide⟩ = B := by
        simp [S3, intSubMat, skipFinIdx, M1, M0, c0, c3, B, laurentSingleT3U1Mat4,
              laurentInterpMat, laurentRowsSingle4, laurentColsT3U1_4, laurentInterpEntry]
      have hs02 : S3 ⟨0, by decide⟩ ⟨2, by decide⟩ = p := by
        simp [S3, intSubMat, skipFinIdx, M1, M0, c0, c3, p, Z, laurentSingleT3U1Mat4,
              laurentInterpMat, laurentRowsSingle4, laurentColsT3U1_4, laurentInterpEntry,
              laurentInterpBinom_zero_right]
      have hs10 : S3 ⟨1, by decide⟩ ⟨0, by decide⟩ = 2 * w := by
        simp [S3, intSubMat, skipFinIdx, M1, M0, c0, c3, w, laurentSingleT3U1Mat4,
              laurentInterpMat, laurentRowsSingle4, laurentColsT3U1_4, laurentInterpEntry,
              laurentInterpBinom_one_right]
      have hs11 : S3 ⟨1, by decide⟩ ⟨1, by decide⟩ = 2 * B + w * w := by
        have hm : S3 ⟨1, by decide⟩ ⟨1, by decide⟩ = (laurentInterpBinom (2 * W) 2 : Int) := by
          simp [S3, intSubMat, skipFinIdx, M1, M0, c0, c3, laurentSingleT3U1Mat4,
                laurentInterpMat, laurentRowsSingle4, laurentColsT3U1_4, laurentInterpEntry]
        rw [hm, hb_2W, Int.natCast_add, natCast_mul 2, natCast_mul W W]; rfl
      have hs12 : S3 ⟨1, by decide⟩ ⟨2, by decide⟩ = p * p + 2 * p := by
        have hm : S3 ⟨1, by decide⟩ ⟨2, by decide⟩ = ((2 ^ (2 * u) : Nat) : Int) - 1 := by
          simp [S3, intSubMat, skipFinIdx, M1, M0, c0, c3, laurentSingleT3U1Mat4,
                laurentInterpMat, laurentRowsSingle4, laurentColsT3U1_4, laurentInterpEntry,
                laurentInterpBinom_zero_right]
        rw [hm, hpow2_2u u]
        change ((Z * Z : Nat) : Int) - 1 = p * p + 2 * p
        rw [natCast_mul Z Z, hZ_p1, Int.add_mul p 1 (p + 1), Int.mul_add p p 1,
            Int.one_mul, Int.mul_one]
        omega
      have hs20 : S3 ⟨2, by decide⟩ ⟨0, by decide⟩ = 3 * w := by
        simp [S3, intSubMat, skipFinIdx, M1, M0, c0, c3, w, laurentSingleT3U1Mat4,
              laurentInterpMat, laurentRowsSingle4, laurentColsT3U1_4, laurentInterpEntry,
              laurentInterpBinom_one_right]
      have hs21 : S3 ⟨2, by decide⟩ ⟨1, by decide⟩ = 3 * B + 3 * (w * w) := by
        have hm : S3 ⟨2, by decide⟩ ⟨1, by decide⟩ = (laurentInterpBinom (3 * W) 2 : Int) := by
          simp [S3, intSubMat, skipFinIdx, M1, M0, c0, c3, laurentSingleT3U1Mat4,
                laurentInterpMat, laurentRowsSingle4, laurentColsT3U1_4, laurentInterpEntry]
        rw [hm, hb_3W, Int.natCast_add, natCast_mul 3, natCast_mul 3, natCast_mul W W]; rfl
      have hs22 : S3 ⟨2, by decide⟩ ⟨2, by decide⟩ = p * p * p + 3 * (p * p) + 3 * p := by
        have hm : S3 ⟨2, by decide⟩ ⟨2, by decide⟩ = ((2 ^ (3 * u) : Nat) : Int) - 1 := by
          simp [S3, intSubMat, skipFinIdx, M1, M0, c0, c3, laurentSingleT3U1Mat4,
                laurentInterpMat, laurentRowsSingle4, laurentColsT3U1_4, laurentInterpEntry,
                laurentInterpBinom_zero_right]
        rw [hm, hpow2_3u u]
        change ((Z * Z * Z : Nat) : Int) - 1 = p * p * p + 3 * (p * p) + 3 * p
        rw [natCast_mul (Z * Z) Z, natCast_mul Z Z, hZ_p1]
        have hexp : (p + 1) * (p + 1) * (p + 1) - 1 = p * p * p + 3 * (p * p) + 3 * p := by
          rw [Int.add_mul p 1 (p + 1), Int.mul_add p p 1, Int.one_mul, Int.mul_one]
          have h1 : (p * p + p + (p + 1)) * (p + 1) =
              (p * p + 2 * p + 1) * p + (p * p + 2 * p + 1) := by
            have h2p : p * p + p + (p + 1) = p * p + 2 * p + 1 := by omega
            rw [h2p, Int.mul_add _ p 1, Int.mul_one]
          rw [h1, Int.add_mul (p * p + 2 * p) 1 p, Int.add_mul (p * p) (2 * p) p,
              Int.one_mul, Int.mul_assoc 2 p p]
          omega
        exact hexp
      rw [hs00, hs01, hs02, hs10, hs11, hs12, hs20, hs21, hs22]
      have hrhs_cast : ((W ^ 3 * (2 ^ u - 1) ^ 3 : Nat) : Int) = (w * w * w) * (p * p * p) := by
        have hw3 : ((W ^ 3 : Nat) : Int) = w * w * w := by
          rw [show (3 : Nat) = 1 + 1 + 1 from rfl, Nat.pow_add, Nat.pow_add, Nat.pow_one,
              natCast_mul, natCast_mul]
        have hp3 : (((2 ^ u - 1) ^ 3 : Nat) : Int) = p * p * p := by
          change (((Z - 1) ^ 3 : Nat) : Int) = p * p * p
          rw [show (3 : Nat) = 1 + 1 + 1 from rfl, Nat.pow_add, Nat.pow_add, Nat.pow_one,
              natCast_mul, natCast_mul]
          have hpm : ((Z - 1 : Nat) : Int) = p := by dsimp [p]; omega
          rw [hpm]
        rw [natCast_mul (W ^ 3), hw3, hp3]
      rw [hrhs_cast]
      let P2 := p * p + 2 * p
      let P3 := p * p * p + 3 * (p * p) + 3 * p
      change w * ((2 * B + w * w) * P3 - P2 * (3 * B + 3 * (w * w))) -
        B * ((2 * w) * P3 - P2 * (3 * w)) +
        p * ((2 * w) * (3 * B + 3 * (w * w)) - (2 * B + w * w) * (3 * w)) =
        (w * w * w) * (p * p * p)
      have hc01 : w * ((2 * B + w * w) * P3 - P2 * (3 * B + 3 * (w * w))) -
          B * ((2 * w) * P3 - P2 * (3 * w)) = (w * w * w) * (P3 - 3 * P2) := by
        have ht1 : w * ((2 * B + w * w) * P3 - P2 * (3 * B + 3 * (w * w))) =
            (w * B) * (2 * P3 - 3 * P2) + (w * w * w) * (P3 - 3 * P2) := by
          rw [Int.add_mul (2 * B) (w * w) P3, Int.mul_add P2 (3 * B) (3 * (w * w)),
              Int.mul_sub w, Int.mul_add w, Int.mul_add w]
          have ha : w * (2 * B * P3) = (w * B) * (2 * P3) := by
            rw [Int.mul_assoc 2 B P3, Int.mul_comm 2 (B * P3), Int.mul_assoc B P3 2,
                Int.mul_comm P3 2, ← Int.mul_assoc w B (2 * P3)]
          have hb : w * (w * w * P3) = (w * w * w) * P3 := by
            rw [← Int.mul_assoc w (w * w) P3, Int.mul_assoc w w w]
          have hc : w * (P2 * (3 * B)) = (w * B) * (3 * P2) := by
            rw [← Int.mul_assoc P2 3 B, Int.mul_comm P2 3, Int.mul_comm (3 * P2) B,
                ← Int.mul_assoc w B (3 * P2)]
          have hd : w * (P2 * (3 * (w * w))) = (w * w * w) * (3 * P2) := by
            rw [← Int.mul_assoc P2 3 (w * w), Int.mul_comm P2 3,
                Int.mul_comm (3 * P2) (w * w), ← Int.mul_assoc w (w * w) (3 * P2),
                Int.mul_assoc w w w]
          rw [ha, hb, hc, hd, Int.mul_sub (w * B), Int.mul_sub (w * w * w)]
          omega
        have ht2 : B * ((2 * w) * P3 - P2 * (3 * w)) = (w * B) * (2 * P3 - 3 * P2) := by
          have ha : (2 * w) * P3 = w * (2 * P3) := by
            rw [Int.mul_comm 2 w, Int.mul_assoc w 2 P3]
          have hb : P2 * (3 * w) = w * (3 * P2) := by
            rw [← Int.mul_assoc P2 3 w, Int.mul_comm P2 3, Int.mul_comm (3 * P2) w]
          rw [ha, hb, ← Int.mul_sub w (2 * P3) (3 * P2), ← Int.mul_assoc B w, Int.mul_comm B w]
        rw [ht1, ht2]
        omega
      have hc2 : p * ((2 * w) * (3 * B + 3 * (w * w)) - (2 * B + w * w) * (3 * w)) =
          (w * w * w) * (3 * p) := by
        have hin : (2 * w) * (3 * B + 3 * (w * w)) - (2 * B + w * w) * (3 * w) = 3 * (w * w * w) := by
          rw [Int.mul_add (2 * w), Int.add_mul (2 * B) (w * w) (3 * w)]
          have h6B1 : (2 * w) * (3 * B) = 6 * (w * B) := by
            rw [← Int.mul_assoc (2 * w) 3 B, Int.mul_assoc 2 w 3, Int.mul_comm w 3,
                ← Int.mul_assoc 2 3 w, show (2 : Int) * 3 = 6 from rfl, Int.mul_assoc 6 w B]
          have h6B2 : (2 * B) * (3 * w) = 6 * (w * B) := by
            rw [← Int.mul_assoc (2 * B) 3 w, Int.mul_assoc 2 B 3, Int.mul_comm B 3,
                ← Int.mul_assoc 2 3 B, show (2 : Int) * 3 = 6 from rfl, Int.mul_assoc 6 B w,
                Int.mul_comm B w]
          have h6w : (2 * w) * (3 * (w * w)) = 6 * (w * w * w) := by
            rw [← Int.mul_assoc (2 * w) 3 (w * w), Int.mul_assoc 2 w 3, Int.mul_comm w 3,
                ← Int.mul_assoc 2 3 w, show (2 : Int) * 3 = 6 from rfl,
                Int.mul_assoc 6 w (w * w), ← Int.mul_assoc w w w]
          have h3w : (w * w) * (3 * w) = 3 * (w * w * w) := by
            rw [← Int.mul_assoc (w * w) 3 w, Int.mul_comm (w * w) 3, Int.mul_assoc 3 (w * w) w]
          rw [h6B1, h6B2, h6w, h3w]
          omega
        rw [hin, ← Int.mul_assoc p 3 (w * w * w), Int.mul_comm p 3,
            Int.mul_comm (3 * p) (w * w * w)]
      rw [hc01, hc2, ← Int.mul_add (w * w * w) (P3 - 3 * P2) (3 * p)]
      have hp_id : (P3 - 3 * P2) + 3 * p = p * p * p := by
        dsimp [P3, P2]
        rw [Int.mul_add 3 (p * p) (2 * p), ← Int.mul_assoc 3 2 p]
        omega
      rw [hp_id]
    have hpos_nat : W ^ 3 * (2 ^ u - 1) ^ 3 ≥ 1 := by
      have h2u_ge2 : 2 ^ u ≥ 2 := by simpa using pow2_mono_nat hu
      exact Nat.mul_le_mul (nat_pow_pos_of_pos W hW 3)
        (nat_pow_pos_of_pos (2 ^ u - 1) (by omega) 3)
    exact ⟨hdet_val, by rw [hdet_val]; omega⟩
  · -- Part 2: Single-base confluent `(T = 2, U = 2)` closed form `W^2 * 2^u * (2^u - 1)^4 > 0`:
    intro W u hW hu
    let M0 := laurentSingleC22Mat4 W u
    let c0 : Fin 4 := ⟨0, by decide⟩
    let c1 : Fin 4 := ⟨1, by decide⟩
    let c2 : Fin 4 := ⟨2, by decide⟩
    let c3 : Fin 4 := ⟨3, by decide⟩
    let M1 : Fin 4 -> Fin 4 -> Int := fun i j => if j = c2 then M0 i c2 - 1 * M0 i c0 else M0 i j
    let M2 : Fin 4 -> Fin 4 -> Int := fun i j => if j = c3 then M1 i c3 - 1 * M1 i c1 else M1 i j
    have hd1 : intDet 4 M0 = intDet 4 M1 := (intDet_sub_col_mul_other 4 c2 c0 (by decide) 1 M0).symm
    have hd2 : intDet 4 M1 = intDet 4 M2 := (intDet_sub_col_mul_other 4 c3 c1 (by decide) 1 M1).symm
    have hdet_val : intDet 4 M0 = ((W ^ 2 * 2 ^ u * (2 ^ u - 1) ^ 4 : Nat) : Int) := by
      rw [hd1, hd2, intDet_four M2]
      have hr00 : M2 ⟨0, by decide⟩ ⟨0, by decide⟩ = 1 := by
        simp [M2, M1, M0, c0, c1, c2, c3, laurentSingleC22Mat4, laurentInterpMat,
              laurentRowsSingle4, laurentColsC22_4, laurentInterpEntry, laurentInterpBinom]
      have hr01 : M2 ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 := by
        simp [M2, M1, M0, c0, c1, c2, c3, laurentSingleC22Mat4, laurentInterpMat,
              laurentRowsSingle4, laurentColsC22_4, laurentInterpEntry, laurentInterpBinom]
      have hr02 : M2 ⟨0, by decide⟩ ⟨2, by decide⟩ = 0 := by
        simp [M2, M1, M0, c0, c1, c2, c3, laurentSingleC22Mat4, laurentInterpMat,
              laurentRowsSingle4, laurentColsC22_4, laurentInterpEntry, laurentInterpBinom]
      have hr03 : M2 ⟨0, by decide⟩ ⟨3, by decide⟩ = 0 := by
        simp [M2, M1, M0, c0, c1, c2, c3, laurentSingleC22Mat4, laurentInterpMat,
              laurentRowsSingle4, laurentColsC22_4, laurentInterpEntry, laurentInterpBinom]
      rw [hr00, hr01, hr02, hr03]
      simp only [Int.one_mul, Int.zero_mul, Int.sub_zero, Int.add_zero]
      -- In `S3 := intSubMat M2 0`, subtract `w * col 1` from `col 2` so `(0, 2)` becomes `0`:
      let S3 := intSubMat M2 ⟨0, by decide⟩
      let Z : Nat := 2 ^ u
      have hZ_ge2 : Z ≥ 2 := by dsimp [Z]; simpa using pow2_mono_nat hu
      let p : Int := (Z : Int) - 1
      let w : Int := (W : Int)
      have hZ_p1 : (Z : Int) = p + 1 := by dsimp [p]; omega
      let S3' : Fin 3 -> Fin 3 -> Int := fun i j =>
        if j = ⟨2, by decide⟩ then S3 i ⟨2, by decide⟩ - w * S3 i ⟨1, by decide⟩ else S3 i j
      have hd3 : intDet 3 S3 = intDet 3 S3' :=
        (intDet_sub_col_mul_other 3 ⟨2, by decide⟩ ⟨1, by decide⟩ (by decide) w S3).symm
      change intDet 3 S3 = _
      rw [hd3, intDet_three S3']
      let P2 := p * p + 2 * p
      let P3 := p * p * p + 3 * (p * p) + 3 * p
      have hP2_eq : (Z : Int) * (Z : Int) - 1 = P2 := by
        dsimp [P2]; rw [hZ_p1, Int.add_mul p 1 (p + 1), Int.mul_add p p 1, Int.one_mul, Int.mul_one]; omega
      have hP3_eq : (Z : Int) * (Z : Int) * (Z : Int) - 1 = P3 := by
        dsimp [P3]
        rw [hZ_p1, Int.add_mul p 1 (p + 1), Int.mul_add p p 1, Int.one_mul, Int.mul_one]
        have h1 : (p * p + p + (p + 1)) * (p + 1) = (p * p + 2 * p + 1) * p + (p * p + 2 * p + 1) := by
          have h2p : p * p + p + (p + 1) = p * p + 2 * p + 1 := by omega
          rw [h2p, Int.mul_add _ p 1, Int.mul_one]
        rw [h1, Int.add_mul (p * p + 2 * p) 1 p, Int.add_mul (p * p) (2 * p) p,
            Int.one_mul, Int.mul_assoc 2 p p]
        omega
      have hs00 : S3 ⟨0, by decide⟩ ⟨0, by decide⟩ = w := by
        simp [S3, intSubMat, skipFinIdx, M2, M1, M0, c0, c1, c2, c3, w, laurentSingleC22Mat4,
              laurentInterpMat, laurentRowsSingle4, laurentColsC22_4, laurentInterpEntry,
              laurentInterpBinom_one_right]
      have hs01 : S3 ⟨0, by decide⟩ ⟨1, by decide⟩ = p := by
        simp [S3, intSubMat, skipFinIdx, M2, M1, M0, c0, c1, c2, c3, p, Z, laurentSingleC22Mat4,
              laurentInterpMat, laurentRowsSingle4, laurentColsC22_4, laurentInterpEntry,
              laurentInterpBinom_zero_right]
      have hs02 : S3 ⟨0, by decide⟩ ⟨2, by decide⟩ = w * p := by
        simp [S3, intSubMat, skipFinIdx, M2, M1, M0, c0, c1, c2, c3, w, p, Z, laurentSingleC22Mat4,
              laurentInterpMat, laurentRowsSingle4, laurentColsC22_4, laurentInterpEntry,
              laurentInterpBinom_one_right, Int.mul_sub]
      have hs10 : S3 ⟨1, by decide⟩ ⟨0, by decide⟩ = 2 * w := by
        simp [S3, intSubMat, skipFinIdx, M2, M1, M0, c0, c1, c2, c3, w, laurentSingleC22Mat4,
              laurentInterpMat, laurentRowsSingle4, laurentColsC22_4, laurentInterpEntry,
              laurentInterpBinom_one_right]
      have hs11 : S3 ⟨1, by decide⟩ ⟨1, by decide⟩ = P2 := by
        have hm : S3 ⟨1, by decide⟩ ⟨1, by decide⟩ = ((2 ^ (2 * u) : Nat) : Int) - 1 := by
          simp [S3, intSubMat, skipFinIdx, M2, M1, M0, c0, c1, c2, c3, laurentSingleC22Mat4,
                laurentInterpMat, laurentRowsSingle4, laurentColsC22_4, laurentInterpEntry,
                laurentInterpBinom_zero_right]
        rw [hm, hpow2_2u u]
        change ((Z * Z : Nat) : Int) - 1 = P2
        rw [natCast_mul Z Z, hP2_eq]
      have hs12 : S3 ⟨1, by decide⟩ ⟨2, by decide⟩ = (2 * w) * P2 := by
        have hm : S3 ⟨1, by decide⟩ ⟨2, by decide⟩ =
            ((2 * W * 2 ^ (2 * u) : Nat) : Int) - ((2 * W : Nat) : Int) := by
          simp [S3, intSubMat, skipFinIdx, M2, M1, M0, c0, c1, c2, c3, laurentSingleC22Mat4,
                laurentInterpMat, laurentRowsSingle4, laurentColsC22_4, laurentInterpEntry,
                laurentInterpBinom_one_right]
        rw [hm, hpow2_2u u]
        change ((2 * W * (Z * Z) : Nat) : Int) - ((2 * W : Nat) : Int) = (2 * w) * P2
        rw [natCast_mul (2 * W) (Z * Z), natCast_mul 2 W, natCast_mul Z Z]
        change (2 * w) * ((Z : Int) * (Z : Int)) - (2 * w) = (2 * w) * P2
        rw [← hP2_eq, Int.mul_sub, Int.mul_one]
      have hs20 : S3 ⟨2, by decide⟩ ⟨0, by decide⟩ = 3 * w := by
        simp [S3, intSubMat, skipFinIdx, M2, M1, M0, c0, c1, c2, c3, w, laurentSingleC22Mat4,
              laurentInterpMat, laurentRowsSingle4, laurentColsC22_4, laurentInterpEntry,
              laurentInterpBinom_one_right]
      have hs21 : S3 ⟨2, by decide⟩ ⟨1, by decide⟩ = P3 := by
        have hm : S3 ⟨2, by decide⟩ ⟨1, by decide⟩ = ((2 ^ (3 * u) : Nat) : Int) - 1 := by
          simp [S3, intSubMat, skipFinIdx, M2, M1, M0, c0, c1, c2, c3, laurentSingleC22Mat4,
                laurentInterpMat, laurentRowsSingle4, laurentColsC22_4, laurentInterpEntry,
                laurentInterpBinom_zero_right]
        rw [hm, hpow2_3u u]
        change ((Z * Z * Z : Nat) : Int) - 1 = P3
        rw [natCast_mul (Z * Z) Z, natCast_mul Z Z, hP3_eq]
      have hs22 : S3 ⟨2, by decide⟩ ⟨2, by decide⟩ = (3 * w) * P3 := by
        have hm : S3 ⟨2, by decide⟩ ⟨2, by decide⟩ =
            ((3 * W * 2 ^ (3 * u) : Nat) : Int) - ((3 * W : Nat) : Int) := by
          simp [S3, intSubMat, skipFinIdx, M2, M1, M0, c0, c1, c2, c3, laurentSingleC22Mat4,
                laurentInterpMat, laurentRowsSingle4, laurentColsC22_4, laurentInterpEntry,
                laurentInterpBinom_one_right]
        rw [hm, hpow2_3u u]
        change ((3 * W * (Z * Z * Z) : Nat) : Int) - ((3 * W : Nat) : Int) = (3 * w) * P3
        rw [natCast_mul (3 * W) (Z * Z * Z), natCast_mul 3 W,
            natCast_mul (Z * Z) Z, natCast_mul Z Z]
        change (3 * w) * ((Z : Int) * (Z : Int) * (Z : Int)) - (3 * w) = (3 * w) * P3
        rw [← hP3_eq, Int.mul_sub, Int.mul_one]
      have h00' : S3' ⟨0, by decide⟩ ⟨0, by decide⟩ = w := hs00
      have h01' : S3' ⟨0, by decide⟩ ⟨1, by decide⟩ = p := hs01
      have h02' : S3' ⟨0, by decide⟩ ⟨2, by decide⟩ = 0 := by
        change S3 ⟨0, by decide⟩ ⟨2, by decide⟩ - w * S3 ⟨0, by decide⟩ ⟨1, by decide⟩ = 0
        rw [hs02, hs01]; omega
      have h10' : S3' ⟨1, by decide⟩ ⟨0, by decide⟩ = 2 * w := hs10
      have h11' : S3' ⟨1, by decide⟩ ⟨1, by decide⟩ = P2 := hs11
      have h12' : S3' ⟨1, by decide⟩ ⟨2, by decide⟩ = w * P2 := by
        change S3 ⟨1, by decide⟩ ⟨2, by decide⟩ - w * S3 ⟨1, by decide⟩ ⟨1, by decide⟩ = w * P2
        rw [hs12, hs11]
        have h2w : (2 : Int) * w = w + w := by omega
        rw [h2w, Int.add_mul w w P2]; omega
      have h20' : S3' ⟨2, by decide⟩ ⟨0, by decide⟩ = 3 * w := hs20
      have h21' : S3' ⟨2, by decide⟩ ⟨1, by decide⟩ = P3 := hs21
      have h22' : S3' ⟨2, by decide⟩ ⟨2, by decide⟩ = (2 * w) * P3 := by
        change S3 ⟨2, by decide⟩ ⟨2, by decide⟩ - w * S3 ⟨2, by decide⟩ ⟨1, by decide⟩ = (2 * w) * P3
        rw [hs22, hs21]
        have h3 : (3 : Int) * w = 2 * w + w := by omega
        rw [h3, Int.add_mul (2 * w) w P3]; omega
      rw [h00', h01', h02', h10', h11', h12', h20', h21', h22']
      simp only [Int.zero_mul, Int.add_zero]
      have hrhs_cast : ((W ^ 2 * 2 ^ u * (2 ^ u - 1) ^ 4 : Nat) : Int) =
          (w * w) * ((p + 1) * (p * p * p * p)) := by
        have hw2 : ((W ^ 2 : Nat) : Int) = w * w := by
          rw [Nat.pow_succ W 1, Nat.pow_one, natCast_mul]
        have hp4 : (((2 ^ u - 1) ^ 4 : Nat) : Int) = p * p * p * p := by
          change (((Z - 1) ^ 4 : Nat) : Int) = p * p * p * p
          rw [show (4 : Nat) = 1 + 1 + 1 + 1 from rfl,
              Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_one,
              natCast_mul, natCast_mul, natCast_mul]
          have hpm : ((Z - 1 : Nat) : Int) = p := by dsimp [p]; omega
          rw [hpm]
        rw [natCast_mul (W ^ 2 * 2 ^ u), natCast_mul (W ^ 2) (2 ^ u), hw2, hp4]
        change w * w * (Z : Int) * (p * p * p * p) = _
        rw [hZ_p1, Int.mul_assoc (w * w)]
      rw [hrhs_cast]
      have hc0 : w * (P2 * ((2 * w) * P3) - (w * P2) * P3) = (w * w) * (P2 * P3) := by
        have ha : P2 * ((2 * w) * P3) = (2 * w) * (P2 * P3) := by
          rw [← Int.mul_assoc P2 (2 * w) P3, Int.mul_comm P2 (2 * w), Int.mul_assoc (2 * w) P2 P3]
        have hb : (w * P2) * P3 = w * (P2 * P3) := Int.mul_assoc w P2 P3
        have hc : (2 * w) * (P2 * P3) - w * (P2 * P3) = w * (P2 * P3) := by
          rw [← Int.sub_mul (2 * w) w (P2 * P3), show (2 : Int) * w - w = w by omega]
        rw [ha, hb, hc, ← Int.mul_assoc w w (P2 * P3)]
      have hc1 : p * ((2 * w) * ((2 * w) * P3) - (w * P2) * (3 * w)) =
          (w * w) * (p * (4 * P3 - 3 * P2)) := by
        have ha : (2 * w) * ((2 * w) * P3) = (w * w) * (4 * P3) := by
          rw [← Int.mul_assoc (2 * w) (2 * w) P3]
          have h22 : (2 * w) * (2 * w) = (w * w) * 4 := by
            rw [Int.mul_comm 2 w, Int.mul_assoc w 2 (w * 2), Int.mul_comm 2 (w * 2),
                Int.mul_assoc w 2 2, show (2 : Int) * 2 = 4 from rfl, ← Int.mul_assoc w w 4]
          rw [h22, Int.mul_assoc (w * w) 4 P3]
        have hb : (w * P2) * (3 * w) = (w * w) * (3 * P2) := by
          rw [Int.mul_comm 3 w, ← Int.mul_assoc (w * P2) w 3, Int.mul_assoc w P2 w,
              Int.mul_comm P2 w, ← Int.mul_assoc w w P2, Int.mul_assoc (w * w) P2 3,
              Int.mul_comm P2 3]
        rw [ha, hb, ← Int.mul_sub (w * w), ← Int.mul_assoc p (w * w), Int.mul_comm p (w * w),
            Int.mul_assoc (w * w) p]
      rw [hc0, hc1, ← Int.mul_sub (w * w)]
      apply congrArg ((w * w) * ·)
      have hsplit : P2 * P3 - p * (4 * P3 - 3 * P2) = (p * p - 2 * p) * P3 + 3 * p * P2 := by
        change (p * p + 2 * p) * P3 - p * (4 * P3 - 3 * P2) = (p * p - 2 * p) * P3 + 3 * p * P2
        rw [Int.mul_sub p (4 * P3) (3 * P2),
            ← Int.mul_assoc p 4 P3, Int.mul_comm p 4,
            ← Int.mul_assoc p 3 P2, Int.mul_comm p 3,
            Int.sub_mul (p * p) (2 * p) P3, Int.add_mul (p * p) (2 * p) P3,
            show (4 : Int) * p * P3 = 2 * p * P3 + 2 * p * P3 by
              rw [show (4 : Int) = 2 + 2 from rfl, Int.add_mul 2 2 p, Int.add_mul]]
        omega
      rw [hsplit]
      dsimp [P3, P2]
      have hexp1 : (p * p - 2 * p) * (p * p * p + 3 * (p * p) + 3 * p) =
          p * p * p * p * p + p * p * p * p - 3 * (p * p * p) - 6 * (p * p) := by
        rw [Int.sub_mul (p * p) (2 * p),
            Int.mul_add (p * p) (p * p * p + 3 * (p * p)) (3 * p),
            Int.mul_add (p * p) (p * p * p) (3 * (p * p)),
            Int.mul_add (2 * p) (p * p * p + 3 * (p * p)) (3 * p),
            Int.mul_add (2 * p) (p * p * p) (3 * (p * p))]
        have m1 : (p * p) * (p * p * p) = p * p * p * p * p := by
          rw [← Int.mul_assoc (p * p) (p * p) p, ← Int.mul_assoc (p * p) p p]
        have m2 : (p * p) * (3 * (p * p)) = 3 * (p * p * p * p) := by
          rw [← Int.mul_assoc (p * p) 3 (p * p), Int.mul_comm (p * p) 3,
              Int.mul_assoc 3 (p * p) (p * p), ← Int.mul_assoc (p * p) p p]
        have m3 : (p * p) * (3 * p) = 3 * (p * p * p) := by
          rw [← Int.mul_assoc (p * p) 3 p, Int.mul_comm (p * p) 3, Int.mul_assoc 3 (p * p) p]
        have m4 : (2 * p) * (p * p * p) = 2 * (p * p * p * p) := by
          rw [Int.mul_assoc 2 p (p * p * p), ← Int.mul_assoc p (p * p) p, ← Int.mul_assoc p p p]
        have m5 : (2 * p) * (3 * (p * p)) = 6 * (p * p * p) := by
          rw [← Int.mul_assoc (2 * p) 3 (p * p), Int.mul_assoc 2 p 3, Int.mul_comm p 3,
              ← Int.mul_assoc 2 3 p, show (2 : Int) * 3 = 6 from rfl,
              Int.mul_assoc 6 p (p * p), ← Int.mul_assoc p p p]
        have m6 : (2 * p) * (3 * p) = 6 * (p * p) := by
          rw [← Int.mul_assoc (2 * p) 3 p, Int.mul_assoc 2 p 3, Int.mul_comm p 3,
              ← Int.mul_assoc 2 3 p, show (2 : Int) * 3 = 6 from rfl, Int.mul_assoc 6 p p]
        rw [m1, m2, m3, m4, m5, m6]
        omega
      have hexp2 : 3 * p * (p * p + 2 * p) = 3 * (p * p * p) + 6 * (p * p) := by
        rw [Int.mul_add (3 * p) (p * p) (2 * p),
            Int.mul_assoc 3 p (p * p), ← Int.mul_assoc p p p,
            ← Int.mul_assoc (3 * p) 2 p, Int.mul_assoc 3 p 2, Int.mul_comm p 2,
            ← Int.mul_assoc 3 2 p, show (3 : Int) * 2 = 6 from rfl, Int.mul_assoc 6 p p]
      have hexp3 : (p + 1) * (p * p * p * p) = p * p * p * p * p + p * p * p * p := by
        rw [Int.add_mul p 1 (p * p * p * p), Int.one_mul,
            ← Int.mul_assoc p (p * p * p) p, ← Int.mul_assoc p (p * p) p, ← Int.mul_assoc p p p]
      rw [hexp1, hexp2, hexp3]
      omega
    have hpos_nat : W ^ 2 * 2 ^ u * (2 ^ u - 1) ^ 4 ≥ 1 := by
      have h2u_ge2 : 2 ^ u ≥ 2 := by simpa using pow2_mono_nat hu
      exact Nat.mul_le_mul (Nat.mul_le_mul (nat_pow_pos_of_pos W hW 2) (pow2_pos_nat u))
        (nat_pow_pos_of_pos (2 ^ u - 1) (by omega) 4)
    exact ⟨hdet_val, by rw [hdet_val]; omega⟩
  · -- Part 4: Resonant zero at `(W, K, u) = (9, 16, 2)`:
    refine ⟨by decide, by decide, ?_⟩
    rw [hdet_tb 9 16 2 (by decide) (by decide) (by decide)]
    decide
  · -- Part 5: Universal odd-`u` non-vanishing (`u = 2 * m + 1`):
    intro W K m hW hK hzero
    let u := 2 * m + 1
    change intDet 4 (laurentTwoBaseMat4 W K u) = 0 at hzero
    rw [hdet_tb W K u hW hK (by dsimp [u]; omega)] at hzero
    have hnat_eq : W ^ 2 * 2 ^ u * (3 ^ u - 1) ^ 2 = K ^ 2 * 3 ^ u * (2 ^ u - 1) ^ 2 := by
      generalize W ^ 2 * 2 ^ u * (3 ^ u - 1) ^ 2 = nL, K ^ 2 * 3 ^ u * (2 ^ u - 1) ^ 2 = nR at hzero ⊢
      omega
    let X := W * 2 ^ m * (3 ^ u - 1)
    let Y := K * (2 ^ u - 1)
    have h3u_ge3 : 3 ^ u ≥ 3 := by
      dsimp [u]; rw [Nat.pow_succ]; have hp := pow3_pos_nat (2 * m); omega
    have h2u_ge2 : 2 ^ u ≥ 2 := by dsimp [u]; simpa using pow2_mono_nat (by omega : 1 ≤ 2 * m + 1)
    have hX_pos : X ≥ 1 :=
      Nat.mul_le_mul (Nat.mul_le_mul hW (pow2_pos_nat m)) (by omega : 1 ≤ 3 ^ u - 1)
    have hY_pos : Y ≥ 1 := Nat.mul_le_mul hK (by omega : 1 ≤ 2 ^ u - 1)
    have h3u_odd : 3 ^ u % 2 = 1 := pow3_odd_nat_sec8 u
    have h2XX : 2 * (X * X) = W ^ 2 * 2 ^ u * (3 ^ u - 1) ^ 2 := by
      dsimp [X, u]
      rw [Nat.pow_succ W 1, Nat.pow_one, Nat.pow_succ (3 ^ (2 * m + 1) - 1) 1, Nat.pow_one,
          Nat.pow_succ 2 (2 * m), Nat.two_mul m, Nat.pow_add 2 m m]
      let a := W; let b := 2 ^ m; let c := 3 ^ (m + m + 1) - 1
      change 2 * (a * b * c * (a * b * c)) = a * a * (b * b * 2) * (c * c)
      calc
        2 * (a * b * c * (a * b * c))
            = (a * b * c * (a * b * c)) * 2 := Nat.mul_comm 2 _
        _ = (a * a * (b * b) * (c * c)) * 2 := by
              apply congrArg (· * 2)
              calc
                (a * b * c) * (a * b * c)
                    = ((a * b) * (a * b)) * (c * c) := by
                      rw [Nat.mul_assoc (a * b) c (a * b * c),
                          ← Nat.mul_assoc c (a * b) c, Nat.mul_comm c (a * b),
                          Nat.mul_assoc (a * b) c c, ← Nat.mul_assoc (a * b) (a * b) (c * c)]
                _ = (a * a * (b * b)) * (c * c) := by
                      apply congrArg (· * (c * c))
                      rw [Nat.mul_assoc a b (a * b), ← Nat.mul_assoc b a b,
                          Nat.mul_comm b a, Nat.mul_assoc a b b, ← Nat.mul_assoc a a (b * b)]
        _ = a * a * (b * b * 2) * (c * c) := by
              rw [Nat.mul_assoc (a * a * (b * b)) (c * c) 2, Nat.mul_comm (c * c) 2,
                  ← Nat.mul_assoc (a * a * (b * b)) 2 (c * c),
                  Nat.mul_assoc (a * a) (b * b) 2]
    have hYY3 : (Y * Y) * 3 ^ u = K ^ 2 * 3 ^ u * (2 ^ u - 1) ^ 2 := by
      dsimp [Y]
      rw [Nat.pow_succ K 1, Nat.pow_one, Nat.pow_succ (2 ^ u - 1) 1, Nat.pow_one]
      let a := K; let c := 2 ^ u - 1; let d := 3 ^ u
      change (a * c * (a * c)) * d = a * a * d * (c * c)
      have hac : (a * c) * (a * c) = (a * a) * (c * c) := by
        rw [Nat.mul_assoc a c (a * c), ← Nat.mul_assoc c a c, Nat.mul_comm c a,
            Nat.mul_assoc a c c, ← Nat.mul_assoc a a (c * c)]
      rw [hac, Nat.mul_assoc (a * a) (c * c) d, Nat.mul_comm (c * c) d, ← Nat.mul_assoc (a * a) d (c * c)]
    exact two_mul_sq_ne_sq_mul_odd X X Y (3 ^ u) (Nat.le_refl X) hX_pos hY_pos h3u_odd
      (h2XX.trans (hnat_eq.trans hYY3.symm))
  · -- Part 6: Universal Collatz convergent-cone (`3 * K ≤ 5 * W`) non-vanishing & `u ≥ 2` positivity:
    intro W K u hW hK hcone hu1
    by_cases hu_eq1 : u = 1
    · subst hu_eq1
      refine ⟨?_, fun hge2 => by omega⟩
      -- `u = 1 = 2 * 0 + 1` is odd!
      rw [hdet_tb W K 1 hW hK (by decide)]
      intro hzero
      have hnat_eq : W ^ 2 * 2 * 4 = K ^ 2 * 3 * 1 := by
        change ((W ^ 2 * 2 * 4 : Nat) : Int) - ((K ^ 2 * 3 * 1 : Nat) : Int) = 0 at hzero
        omega
      rw [Nat.pow_succ W 1, Nat.pow_one, Nat.pow_succ K 1, Nat.pow_one] at hnat_eq
      have h2XX : 2 * ((2 * W) * (2 * W)) = W * W * 2 * 4 := by
        calc
          2 * ((2 * W) * (2 * W))
              = 2 * (4 * (W * W)) := by
                rw [Nat.mul_assoc 2 W (2 * W), ← Nat.mul_assoc W 2 W,
                    Nat.mul_comm W 2, Nat.mul_assoc 2 W W, ← Nat.mul_assoc 2 2 (W * W)]
          _ = 8 * (W * W) := by rw [← Nat.mul_assoc 2 4]
          _ = W * W * 2 * 4 := by rw [Nat.mul_comm 8 (W * W), ← Nat.mul_assoc (W * W) 2 4]
      exact two_mul_sq_ne_sq_mul_odd (2 * W) (2 * W) K 3 (Nat.le_refl _) (by omega) hK rfl
        (h2XX.trans (by omega))
    · have hu2 : u ≥ 2 := by omega
      have hpos : intDet 4 (laurentTwoBaseMat4 W K u) > 0 := by
        rw [hdet_tb W K u hW hK hu1]
        have hineq := cone_twobase_4x4_strict_ineq u hu2
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
        let L_term := 2 ^ u * (3 ^ u - 1) ^ 2
        let R_term := 3 ^ u * (2 ^ u - 1) ^ 2
        have hstep1 : 9 * K ^ 2 * R_term ≤ 25 * W ^ 2 * R_term :=
          Nat.mul_le_mul_right R_term h9K_le
        have hstep2 : 25 * W ^ 2 * R_term < 9 * W ^ 2 * L_term := by
          have hm := Nat.mul_lt_mul_of_pos_left hineq hW2_pos
          have hl : W ^ 2 * (25 * 3 ^ u * (2 ^ u - 1) ^ 2) = 25 * W ^ 2 * R_term := by
            dsimp [R_term]
            rw [Nat.mul_assoc 25 (3 ^ u), ← Nat.mul_assoc (W ^ 2) 25 R_term, Nat.mul_comm (W ^ 2) 25]
          have hr : W ^ 2 * (9 * 2 ^ u * (3 ^ u - 1) ^ 2) = 9 * W ^ 2 * L_term := by
            dsimp [L_term]
            rw [Nat.mul_assoc 9 (2 ^ u), ← Nat.mul_assoc (W ^ 2) 9 L_term, Nat.mul_comm (W ^ 2) 9]
          rwa [hl, hr] at hm
        have hlt_9 : 9 * (K ^ 2 * R_term) < 9 * (W ^ 2 * L_term) := by
          rw [← Nat.mul_assoc 9, ← Nat.mul_assoc 9]
          exact Nat.lt_of_le_of_lt hstep1 hstep2
        have hlt_nat : K ^ 2 * R_term < W ^ 2 * L_term := by omega
        have heq_l : W ^ 2 * 2 ^ u * (3 ^ u - 1) ^ 2 = W ^ 2 * L_term :=
          Nat.mul_assoc (W ^ 2) (2 ^ u) _
        have heq_r : K ^ 2 * 3 ^ u * (2 ^ u - 1) ^ 2 = K ^ 2 * R_term :=
          Nat.mul_assoc (K ^ 2) (3 ^ u) _
        rw [heq_l, heq_r]
        omega
      exact ⟨by omega, fun _ => hpos⟩

-- ----------------------------------------------------------------------------
-- Choice-Free Pigeonhole, Gauss's Euclid Lemma, Pratt–Lucas Certificates,
-- Coprime-Order Primes `p_3 = 45,661,129` & `p_4 = 107,889,071`, and Joint Floors
-- ----------------------------------------------------------------------------

/-- Pure-`Nat` primality predicate (`p ≥ 2` and no divisor `2 ≤ k < p`). -/
def IsPrimeNat (p : Nat) : Prop :=
  p ≥ 2 ∧ ∀ k : Nat, 2 ≤ k -> k < p -> ¬ (k ∣ p)

def findIndexEqAux (f : Nat -> Nat) (target : Nat) : Nat -> Option Nat
  | 0 => none
  | n + 1 =>
    match findIndexEqAux f target n with
    | some idx => some idx
    | none => if f n = target then some n else none

theorem findIndexEqAux_spec (f : Nat -> Nat) (target : Nat) (N : Nat) :
    (∀ idx : Nat, findIndexEqAux f target N = some idx -> idx < N ∧ f idx = target) ∧
    (findIndexEqAux f target N = none -> ∀ i : Nat, i < N -> f i ≠ target) := by
  induction N with
  | zero => exact ⟨fun _ h => by simp [findIndexEqAux] at h, fun _ _ hi => by omega⟩
  | succ n ih =>
    rcases ih with ⟨hsome, hnone⟩
    refine ⟨?_, ?_⟩
    · intro idx h
      simp only [findIndexEqAux] at h
      cases hf : findIndexEqAux f target n with
      | some j =>
        rw [hf] at h
        injection h with hj
        subst hj
        rcases hsome j hf with ⟨hlt, heq⟩
        exact ⟨by omega, heq⟩
      | none =>
        rw [hf] at h
        by_cases hfn : f n = target
        · simp only [hfn, ite_true] at h
          injection h with hn
          subst hn
          exact ⟨by omega, hfn⟩
        · simp [hfn] at h
    · intro h i hi
      simp only [findIndexEqAux] at h
      cases hf : findIndexEqAux f target n with
      | some j => rw [hf] at h; cases h
      | none =>
        rw [hf] at h
        by_cases hfn : f n = target
        · simp [hfn] at h
        · by_cases hin : i = n
          · subst hin; exact hfn
          · exact hnone hf i (by omega)

/-- Choice-free finite pigeonhole principle on `Nat -> Nat`. -/
theorem nat_func_pigeonhole :
    ∀ (M N : Nat) (f : Nat -> Nat),
      (∀ i : Nat, i < N -> f i < M) ->
      M < N ->
      ∃ i j : Nat, i < j ∧ j < N ∧ f i = f j
  | 0, N, f, hlt, hMN => False.elim (Nat.not_lt_zero _ (hlt 0 hMN))
  | M + 1, N, f, hlt, hMN => by
    cases hfind : findIndexEqAux f M N with
    | none =>
      have hnone := (findIndexEqAux_spec f M N).2 hfind
      exact nat_func_pigeonhole M N f
        (fun i hi => by have h1 := hlt i hi; have h2 := hnone i hi; omega)
        (by omega)
    | some i0 =>
      rcases (findIndexEqAux_spec f M N).1 i0 hfind with ⟨hi0_lt, hfi0⟩
      -- Search for a second index `j ≠ i0` with `f j = M`:
      let f_other : Nat -> Nat := fun j => if j = i0 then 0 else f j + 1
      cases hfind2 : findIndexEqAux f_other (M + 1) N with
      | some j0 =>
        rcases (findIndexEqAux_spec f_other (M + 1) N).1 j0 hfind2 with ⟨hj0_lt, hfj0⟩
        dsimp [f_other] at hfj0
        have hj_ne : j0 ≠ i0 := by
          intro heq; subst heq; simp only [ite_true] at hfj0; omega
        have hfj_M : f j0 = M := by
          simp only [hj_ne, ite_false] at hfj0; omega
        by_cases hij : i0 < j0
        · exact ⟨i0, j0, hij, hj0_lt, hfi0.trans hfj_M.symm⟩
        · exact ⟨j0, i0, by omega, hi0_lt, hfj_M.trans hfi0.symm⟩
      | none =>
        have hno_other := (findIndexEqAux_spec f_other (M + 1) N).2 hfind2
        let g : Nat -> Nat := fun t => f (if t < i0 then t else t + 1)
        have hg_lt : ∀ t : Nat, t < N - 1 -> g t < M := by
          intro t ht
          let idx := if t < i0 then t else t + 1
          have hidx_lt : idx < N := by
            dsimp [idx]; by_cases ht_i0 : t < i0 <;> simp [ht_i0] <;> omega
          have hidx_ne : idx ≠ i0 := by
            dsimp [idx]; by_cases ht_i0 : t < i0 <;> simp [ht_i0] <;> omega
          have h1 := hlt idx hidx_lt
          have h2 := hno_other idx hidx_lt
          dsimp [f_other] at h2
          simp only [hidx_ne, ite_false] at h2
          change f idx < M
          omega
        rcases nat_func_pigeonhole M (N - 1) g hg_lt (by omega) with ⟨t1, t2, ht12, ht2_lt, hgeq⟩
        let idx1 := if t1 < i0 then t1 else t1 + 1
        let idx2 := if t2 < i0 then t2 else t2 + 1
        refine ⟨idx1, idx2, ?_, ?_, hgeq⟩
        · dsimp [idx1, idx2]
          by_cases h1_i0 : t1 < i0 <;> by_cases h2_i0 : t2 < i0 <;>
            simp [h1_i0, h2_i0] <;> omega
        · dsimp [idx2]
          by_cases h2_i0 : t2 < i0 <;> simp [h2_i0] <;> omega

/-- Gauss's Bezout-free proof of Euclid's lemma for `IsPrimeNat q` (`zero custom axioms`). -/
theorem gauss_euclid_lemma_aux (q B : Nat) (hq : IsPrimeNat q) (hndB : ¬ (q ∣ B)) :
    ∀ (bound A : Nat), A ≤ bound -> q ∣ (A * B) -> q ∣ A
  | 0, A, hA0, _ => by rw [show A = 0 by omega]; exact ⟨0, by simp⟩
  | bound + 1, A, hAb, hdvd => by
    by_cases hA0 : A = 0
    · subst hA0; exact ⟨0, by simp⟩
    · by_cases hA1 : A = 1
      · subst hA1; rw [Nat.one_mul] at hdvd; exact False.elim (hndB hdvd)
      · by_cases hlt_q : A < q
        · -- Gauss reduction: `1 ≤ q % A < A` and `(q % A) * B = q * B - (q / A) * (A * B)`:
          have hnd_Aq : ¬ (A ∣ q) := hq.2 A (by omega) hlt_q
          let r := q % A
          have hr_lt : r < A := Nat.mod_lt q (by omega)
          have hr_pos : r ≥ 1 := by
            by_cases hr0 : r = 0
            · exact False.elim (hnd_Aq (Nat.dvd_of_mod_eq_zero hr0))
            · omega
          have hdm : (q / A) * A + r = q := by
            rw [Nat.mul_comm (q / A) A]
            exact Nat.div_add_mod q A
          rcases hdvd with ⟨k, hk⟩
          have hrB : q ∣ (r * B) := by
            have hsum : (q / A) * (A * B) + r * B = q * B := by
              rw [← Nat.mul_assoc (q / A) A B, ← Nat.add_mul, hdm]
            rw [hk] at hsum
            -- `(q / A) * (q * k) + r * B = q * B`, so `r * B = q * (B - (q / A) * k)`:
            have hqk : (q / A) * (q * k) = q * ((q / A) * k) := by
              rw [← Nat.mul_assoc (q / A) q k, Nat.mul_comm (q / A) q, Nat.mul_assoc]
            rw [hqk] at hsum
            have hle_B : (q / A) * k ≤ B := by
              by_cases h : (q / A) * k ≤ B
              · exact h
              · have hq_pos : 0 < q := by have := hq.1; omega
                have hm := Nat.mul_lt_mul_of_pos_left (by omega : B < (q / A) * k) hq_pos
                generalize (q / A) * k = QK at hm hsum
                omega
            exact ⟨B - (q / A) * k, by rw [Nat.mul_sub_left_distrib]; omega⟩
          rcases gauss_euclid_lemma_aux q B hq hndB bound r (by omega) hrB with ⟨m, hm⟩
          cases m with
          | zero => simp at hm; omega
          | succ m' =>
            have hge : q ≤ q * (m' + 1) := by
              simpa using Nat.mul_le_mul_left q (by omega : 1 ≤ m' + 1)
            omega
        · -- `A ≥ q`: reduce to `A - q < A`:
          have hq_ge2 : q ≥ 2 := hq.1
          let A' := A - q
          have hA_eq : A = A' + q := by dsimp [A']; omega
          rcases hdvd with ⟨k, hk⟩
          rw [hA_eq, Nat.add_mul] at hk
          have hle_k : B ≤ k := by
            by_cases h : B ≤ k
            · exact h
            · have hm := Nat.mul_lt_mul_of_pos_left (by omega : k < B) (by omega : 0 < q)
              generalize A' * B = AB at hk
              omega
          have hdvd' : q ∣ (A' * B) := ⟨k - B, by rw [Nat.mul_sub_left_distrib]; omega⟩
          rcases gauss_euclid_lemma_aux q B hq hndB bound A' (by dsimp [A']; omega) hdvd' with
            ⟨m, hm⟩
          exact ⟨m + 1, by rw [hA_eq, hm, Nat.mul_add, Nat.mul_one]⟩

theorem gauss_euclid_lemma (q A B : Nat) (hq : IsPrimeNat q) (hdvd : q ∣ (A * B)) :
    q ∣ A ∨ q ∣ B := by
  by_cases hB : q ∣ B
  · exact Or.inr hB
  · exact Or.inl (gauss_euclid_lemma_aux q B hq hB A A (Nat.le_refl A) hdvd)

theorem prime_dvd_natProdList_mem (q : Nat) (hq : IsPrimeNat q) :
    ∀ qs : List Nat,
      (∀ r ∈ qs, IsPrimeNat r) ->
      q ∣ natProdList qs ->
      q ∈ qs
  | [], _, hdvd => by
    simp only [natProdList] at hdvd
    have h1 := Nat.eq_one_of_dvd_one hdvd
    have hp2 := hq.1
    omega
  | r :: rs, hall, hdvd => by
    simp only [natProdList, List.mem_cons] at hdvd ⊢
    rcases gauss_euclid_lemma q r (natProdList rs) hq hdvd with hqr | hqrs
    · left
      have hr := hall r List.mem_cons_self
      by_cases hlt : q < r
      · exact False.elim (hr.2 q hq.1 hlt hqr)
      · by_cases hgt : r < q
        · rcases hqr with ⟨c, hc⟩
          cases c with
          | zero => simp at hc; have := hr.1; omega
          | succ c' =>
            cases c' with
            | zero => simp at hc; omega
            | succ c'' =>
              have h2 : c'' + 1 + 1 = c'' + 2 := by omega
              rw [h2] at hc
              have hle : q * 2 ≤ q * (c'' + 2) := Nat.mul_le_mul_left q (by omega)
              omega
        · omega
    · exact Or.inr (prime_dvd_natProdList_mem q hq rs (fun x hx => hall x (List.mem_cons_of_mem r hx)) hqrs)

-- Minimal divisor ≥ 2 of `m ≥ 2` is prime (`minDivisor_spec`):

def findMinDivAux (m : Nat) : Nat -> Nat -> Nat
  | 0, _ => m
  | fuel + 1, d =>
    if d ≥ m then m
    else if m % d = 0 then d
    else findMinDivAux m fuel (d + 1)

theorem findMinDivAux_spec (m : Nat) (hm : m ≥ 2) :
    ∀ (fuel d : Nat),
      2 ≤ d -> d ≤ m -> m ≤ d + fuel ->
      (∀ k : Nat, 2 ≤ k -> k < d -> ¬ (k ∣ m)) ->
      let q := findMinDivAux m fuel d
      IsPrimeNat q ∧ q ∣ m
  | 0, d, hd2, hdm, hfuel, hno => by
    have hd_eq : d = m := by omega
    subst hd_eq
    exact ⟨⟨hm, hno⟩, Nat.dvd_refl d⟩
  | fuel + 1, d, hd2, hdm, hfuel, hno => by
    dsimp only
    unfold findMinDivAux
    by_cases hge : d ≥ m
    · have hd_eq : d = m := by omega
      simp only [hge, ite_true]
      subst hd_eq
      exact ⟨⟨hm, hno⟩, Nat.dvd_refl d⟩
    · simp only [hge, ite_false]
      by_cases hmod : m % d = 0
      · simp only [hmod, ite_true]
        have hdvd_dm : d ∣ m := Nat.dvd_of_mod_eq_zero hmod
        refine ⟨⟨hd2, ?_⟩, hdvd_dm⟩
        intro k hk2 hkd hkdvd
        exact hno k hk2 hkd (Nat.dvd_trans hkdvd hdvd_dm)
      · simp only [hmod, ite_false]
        apply findMinDivAux_spec m hm fuel (d + 1) (by omega) (by omega) (by omega)
        intro k hk2 hk_lt
        by_cases hkd : k = d
        · subst hkd
          intro hdvd
          exact hmod (Nat.mod_eq_zero_of_dvd hdvd)
        · exact hno k hk2 (by omega)

theorem exists_prime_divisor_of_ge_two (m : Nat) (hm : m ≥ 2) :
    ∃ q : Nat, IsPrimeNat q ∧ q ∣ m :=
  ⟨findMinDivAux m m 2,
   findMinDivAux_spec m hm m 2 (Nat.le_refl 2) hm (by omega) (fun _ hk2 hlt => by omega)⟩

-- Fast `powModBinAux` correctness & Euclidean `gcd` power lemma:

theorem powModBinAux_spec (p : Nat) (hp : p ≥ 2) :
    ∀ (fuel base exp acc : Nat),
      acc < p -> exp < 2 ^ fuel ->
      powModBinAux p fuel base exp acc = (acc * base ^ exp) % p
  | 0, _, exp, acc, hacc, hexp => by
    have he0 : exp = 0 := by simp at hexp; exact hexp
    subst he0
    simp [powModBinAux, Nat.mod_eq_of_lt hacc]
  | fuel + 1, base, exp, acc, hacc, hexp => by
    simp only [powModBinAux]
    by_cases he0 : exp = 0
    · simp [he0, Nat.mod_eq_of_lt hacc]
    · simp only [he0, ite_false]
      let acc' := if exp % 2 = 1 then (acc * base) % p else acc
      have hacc'_lt : acc' < p := by
        dsimp [acc']
        by_cases heo : exp % 2 = 1
        · simp only [heo, ite_true]; exact Nat.mod_lt _ (by omega)
        · simp only [heo, ite_false]; exact hacc
      have hdiv_lt : exp / 2 < 2 ^ fuel := by
        rw [Nat.pow_succ] at hexp; omega
      rw [powModBinAux_spec p hp fuel ((base * base) % p) (exp / 2) acc' hacc'_lt hdiv_lt]
      have hsq_pow : ((base * base) % p) ^ (exp / 2) % p = base ^ (2 * (exp / 2)) % p := by
        rw [pow_mod_eq_of_mod_eq_w5 p ((base * base) % p) (base * base) (Nat.mod_mod _ p) (exp / 2),
            show base * base = base ^ 2 by rw [Nat.pow_succ, Nat.pow_one],
            pow_pow_eq_mul_w5 base 2 (exp / 2)]
      dsimp [acc']
      by_cases hodd : exp % 2 = 1
      · simp only [hodd, ite_true]
        have hexp_eq : exp = 2 * (exp / 2) + 1 := by omega
        calc
          (((acc * base) % p) * (((base * base) % p) ^ (exp / 2))) % p
              = ((((acc * base) % p) % p) * ((((base * base) % p) ^ (exp / 2)) % p)) % p :=
                Nat.mul_mod _ _ p
          _ = (((acc * base) % p) * ((base ^ (2 * (exp / 2))) % p)) % p := by
                rw [Nat.mod_mod, hsq_pow]
          _ = ((acc * base) * base ^ (2 * (exp / 2))) % p := (Nat.mul_mod _ _ p).symm
          _ = (acc * (base ^ (2 * (exp / 2)) * base)) % p := by
                rw [Nat.mul_assoc acc base, Nat.mul_comm base (base ^ (2 * (exp / 2)))]
          _ = (acc * base ^ exp) % p := by
                rw [← Nat.pow_succ, Nat.succ_eq_add_one, ← hexp_eq]
      · simp only [hodd, ite_false]
        have hexp_eq : exp = 2 * (exp / 2) := by omega
        calc
          (acc * (((base * base) % p) ^ (exp / 2))) % p
              = ((acc % p) * ((((base * base) % p) ^ (exp / 2)) % p)) % p := Nat.mul_mod _ _ p
          _ = ((acc % p) * ((base ^ (2 * (exp / 2))) % p)) % p := by rw [hsq_pow]
          _ = (acc * base ^ exp) % p := by rw [← Nat.mul_mod, ← hexp_eq]

def fastPowMod28 (p b e : Nat) : Nat :=
  powModBinAux p 28 (b % p) e 1

theorem fastPowMod28_eq (p b e : Nat) (hp : p ≥ 2) (he : e < 2 ^ 28) :
    fastPowMod28 p b e = b ^ e % p := by
  unfold fastPowMod28
  rw [powModBinAux_spec p hp 28 (b % p) e 1 (by omega) he, Nat.one_mul]
  exact pow_mod_eq_of_mod_eq_w5 p (b % p) b (Nat.mod_mod b p) e

theorem pow_gcd_mod_eq_one_aux (p b : Nat) (hp : p ≥ 2) :
    ∀ (bound x y : Nat),
      x ≤ bound -> b ^ x % p = 1 -> b ^ y % p = 1 ->
      b ^ (Nat.gcd x y) % p = 1
  | 0, x, y, hx0, _, hy => by
    have h0 : x = 0 := by omega
    subst h0; rw [Nat.gcd_zero_left]; exact hy
  | bound + 1, x, y, hxb, hx, hy => by
    by_cases hx0 : x = 0
    · subst hx0; rw [Nat.gcd_zero_left]; exact hy
    · rw [Nat.gcd_rec x y]
      have hrem_lt : y % x < x := Nat.mod_lt y (by omega)
      have hrem_one : b ^ (y % x) % p = 1 := by
        have hdm : y = x * (y / x) + y % x := (Nat.div_add_mod y x).symm
        have hp_qx : b ^ (x * (y / x)) % p = 1 := by
          rw [← pow_pow_eq_mul_w5 b x (y / x),
              pow_mod_eq_of_mod_eq_w5 p (b ^ x) 1 (by rw [hx, Nat.mod_eq_of_lt hp]) (y / x),
              Nat.one_pow, Nat.mod_eq_of_lt hp]
        have hy_split : b ^ y % p = b ^ (y % x) % p := by
          conv => lhs; rw [hdm]
          rw [Nat.pow_add, Nat.mul_mod, hp_qx, Nat.one_mul, Nat.mod_mod]
        exact hy_split.symm.trans hy
      exact pow_gcd_mod_eq_one_aux p b hp bound (y % x) x (by omega) hrem_one hx

-- Small-prime odd trial division up to `103` (`q ≤ 10609`) & Prime-Factor Order Checker:

def checkOddNoDivAux (q : Nat) : Nat -> Nat -> Bool
  | 0, _ => true
  | fuel + 1, d =>
    if d * d > q then true
    else (q % d != 0) && checkOddNoDivAux q fuel (d + 2)

def checkSmallPrimeBool (q : Nat) : Bool :=
  if q == 2 then true
  else (q ≥ 3) && (q % 2 == 1) && (q ≤ 10608) && checkOddNoDivAux q 52 3

theorem checkOddNoDivAux_sound (q : Nat) :
    ∀ (fuel d : Nat),
      d ≥ 3 -> d % 2 = 1 ->
      (2 * fuel + d) * (2 * fuel + d) > q ->
      checkOddNoDivAux q fuel d = true ->
      ∀ m : Nat, m ≥ d -> m % 2 = 1 -> m * m ≤ q -> ¬ (m ∣ q)
  | 0, d, _, _, hbound, _, m, hmd, _, hmsq => by
    simp only [Nat.mul_zero, Nat.zero_add] at hbound
    have hm := Nat.mul_le_mul hmd hmd
    omega
  | fuel + 1, d, hd3, hd_odd, hbound, hb, m, hmd, hm_odd, hmsq => by
    unfold checkOddNoDivAux at hb
    by_cases hgt : d * d > q
    · have hm := Nat.mul_le_mul hmd hmd; omega
    · simp only [hgt, ite_false] at hb
      rcases bool_and_split hb with ⟨hnd_b, hrest⟩
      by_cases hmeq : m = d
      · subst hmeq
        intro hdvd
        have hm0 := Nat.mod_eq_zero_of_dvd hdvd
        rw [hm0] at hnd_b; cases hnd_b
      · have hm_ge2 : m ≥ d + 2 := by omega
        have hb' : (2 * fuel + (d + 2)) * (2 * fuel + (d + 2)) > q := by
          have heq : 2 * fuel + (d + 2) = 2 * (fuel + 1) + d := by omega
          rw [heq]; exact hbound
        exact checkOddNoDivAux_sound q fuel (d + 2) (by omega) (by omega) hb' hrest
          m hm_ge2 hm_odd hmsq

theorem checkSmallPrimeBool_sound (q : Nat) (hb : checkSmallPrimeBool q = true) :
    IsPrimeNat q := by
  unfold checkSmallPrimeBool at hb
  cases hq2 : q == 2 with
  | true =>
    have heq : q = 2 := of_decide_eq_true hq2
    subst heq
    exact ⟨by decide, fun k hk2 hlt => by omega⟩
  | false =>
    rw [hq2] at hb
    simp only [Bool.false_eq_true, ite_false] at hb
    rcases bool_and_split hb with ⟨hb2, hodd_chk⟩
    rcases bool_and_split hb2 with ⟨hb1, hle_b⟩
    rcases bool_and_split hb1 with ⟨hge3_b, hq_odd_b⟩
    have hge3 : q ≥ 3 := of_decide_eq_true hge3_b
    have hq_odd : q % 2 = 1 := of_decide_eq_true hq_odd_b
    have hle : q ≤ 10608 := of_decide_eq_true hle_b
    have hno_odd := checkOddNoDivAux_sound q 52 3 (by decide) (by decide) (by omega) hodd_chk
    refine ⟨by omega, ?_⟩
    intro k hk2 hlt hkdvd
    rcases hkdvd with ⟨c, hc⟩
    have hc_ge2 : c ≥ 2 := by
      cases c with
      | zero => simp at hc; omega
      | succ c' =>
        cases c' with
        | zero => simp at hc; omega
        | succ _ => omega
    have h_either_sq : k * k ≤ q ∨ c * c ≤ q := by
      by_cases hkc : k ≤ c
      · left
        have hm := Nat.mul_le_mul_left k hkc
        rwa [← hc] at hm
      · right
        have hm := Nat.mul_le_mul_right c (by omega : c ≤ k)
        rwa [← hc] at hm
    have h_odd_div : ∀ x : Nat, 2 ≤ x -> x * x ≤ q -> x ∣ q -> False := by
      intro x hx2 hxsq hxdvd
      by_cases hxe : x % 2 = 0
      · have h2x : 2 ∣ x := Nat.dvd_of_mod_eq_zero hxe
        have h2q : 2 ∣ q := Nat.dvd_trans h2x hxdvd
        have hqm0 := Nat.mod_eq_zero_of_dvd h2q
        omega
      · exact hno_odd x (by omega) (by omega) hxsq hxdvd
    rcases h_either_sq with hksq | hcsq
    · exact h_odd_div k hk2 hksq ⟨c, hc⟩
    · exact h_odd_div c hc_ge2 hcsq ⟨k, by rw [hc, Nat.mul_comm]⟩

def checkAllSmallPrimesBool : List Nat -> Bool
  | [] => true
  | q :: qs => checkSmallPrimeBool q && checkAllSmallPrimesBool qs

theorem checkAllSmallPrimesBool_sound :
    ∀ qs : List Nat, checkAllSmallPrimesBool qs = true -> ∀ q ∈ qs, IsPrimeNat q
  | [], _, _, hm => by cases hm
  | q0 :: qs, hb, q, hm => by
    rcases bool_and_split hb with ⟨hq0, hrest⟩
    cases hm with
    | head => exact checkSmallPrimeBool_sound q0 hq0
    | tail _ hqs => exact checkAllSmallPrimesBool_sound qs hrest q hqs

def checkNoDivQuotPowOneBool (p b d : Nat) : List Nat -> Bool
  | [] => true
  | q :: qs => (fastPowMod28 p b (d / q) != 1) && checkNoDivQuotPowOneBool p b d qs

theorem checkNoDivQuotPowOneBool_sound (p b d : Nat) (hp : p ≥ 2) (hd_lt : d < 2 ^ 28) :
    ∀ qs : List Nat,
      checkNoDivQuotPowOneBool p b d qs = true ->
      ∀ q ∈ qs, b ^ (d / q) % p ≠ 1
  | [], _, _, hm => by cases hm
  | q0 :: qs, hb, q, hm => by
    rcases bool_and_split hb with ⟨hq0, hrest⟩
    cases hm with
    | head =>
      have hdiv_lt : d / q0 < 2 ^ 28 := Nat.lt_of_le_of_lt (Nat.div_le_self d q0) hd_lt
      rw [← fastPowMod28_eq p b (d / q0) hp hdiv_lt]
      intro heq
      rw [heq] at hq0; cases hq0
    | tail _ hqs =>
      exact checkNoDivQuotPowOneBool_sound p b d hp hd_lt qs hrest q hqs

def checkPrimeFactorsOrderBool (p b d : Nat) (qs : List Nat) : Bool :=
  decide (p ≥ 2) &&
  decide (d ≥ 1) &&
  decide (d < 2 ^ 28) &&
  decide (natProdList qs = d) &&
  checkAllSmallPrimesBool qs &&
  (fastPowMod28 p b d == 1) &&
  checkNoDivQuotPowOneBool p b d qs

theorem checkPrimeFactorsOrderBool_sound (p b d : Nat) (qs : List Nat)
    (hb : checkPrimeFactorsOrderBool p b d qs = true) :
    IsExactMultOrderMod p b d := by
  unfold checkPrimeFactorsOrderBool at hb
  rcases bool_and_split hb with ⟨hb6, hnodiv_b⟩
  rcases bool_and_split hb6 with ⟨hb5, hpow1_b⟩
  rcases bool_and_split hb5 with ⟨hb4, hprimes_b⟩
  rcases bool_and_split hb4 with ⟨hb3, hprod_b⟩
  rcases bool_and_split hb3 with ⟨hb2, hdlt_b⟩
  rcases bool_and_split hb2 with ⟨hp2_b, hd1_b⟩
  have hp2 : p ≥ 2 := of_decide_eq_true hp2_b
  have hd1 : d ≥ 1 := of_decide_eq_true hd1_b
  have hdlt : d < 2 ^ 28 := of_decide_eq_true hdlt_b
  have hprod : natProdList qs = d := of_decide_eq_true hprod_b
  have hall_p := checkAllSmallPrimesBool_sound qs hprimes_b
  have hpow_d : b ^ d % p = 1 := by
    rw [← fastPowMod28_eq p b d hp2 hdlt]
    exact of_decide_eq_true hpow1_b
  have hno_quot := checkNoDivQuotPowOneBool_sound p b d hp2 hdlt qs hnodiv_b
  refine ⟨hp2, hd1, hpow_d, ?_⟩
  intro r hr1 hpow_r
  let g := Nat.gcd d r.val
  have hg_pos : g ≥ 1 := Nat.gcd_pos_of_pos_right d hr1
  have hg_le_r : g ≤ r.val := Nat.le_of_dvd hr1 (Nat.gcd_dvd_right d r.val)
  have hg_lt_d : g < d := Nat.lt_of_le_of_lt hg_le_r r.isLt
  have hg_dvd_d : g ∣ d := Nat.gcd_dvd_left d r.val
  have hpow_g : b ^ g % p = 1 :=
    pow_gcd_mod_eq_one_aux p b hp2 d d r.val (Nat.le_refl d) hpow_d hpow_r
  rcases hg_dvd_d with ⟨m, hm⟩
  have hm_ge2 : m ≥ 2 := by
    cases m with
    | zero => simp at hm; omega
    | succ m' =>
      cases m' with
      | zero => simp at hm; omega
      | succ _ => omega
  rcases exists_prime_divisor_of_ge_two m hm_ge2 with ⟨q0, hq0_p, c, hc⟩
  have hq0_dvd_prod : q0 ∣ natProdList qs := ⟨g * c, by
    rw [hprod, hm, hc]
    calc
      g * (q0 * c) = (g * q0) * c := (Nat.mul_assoc g q0 c).symm
      _ = (q0 * g) * c := by rw [Nat.mul_comm g q0]
      _ = q0 * (g * c) := Nat.mul_assoc q0 g c⟩
  have hq0_mem : q0 ∈ qs := prime_dvd_natProdList_mem q0 hq0_p qs hall_p hq0_dvd_prod
  have hd_div_q0 : d / q0 = g * c := by
    have hd_eq : d = q0 * (g * c) := by
      rw [hm, hc, ← Nat.mul_assoc g q0 c, Nat.mul_comm g q0, Nat.mul_assoc]
    rw [hd_eq, Nat.mul_comm q0 (g * c), Nat.mul_div_cancel _ (by have := hq0_p.1; omega)]
  have hpow_dq0 : b ^ (d / q0) % p = 1 := by
    rw [hd_div_q0, ← pow_pow_eq_mul_w5 b g c,
        pow_mod_eq_of_mod_eq_w5 p (b ^ g) 1 (by rw [hpow_g, Nat.mod_eq_of_lt hp2]) c,
        Nat.one_pow, Nat.mod_eq_of_lt hp2]
  exact hno_quot q0 hq0_mem hpow_dq0

/--
  Lucas's Converse of Fermat's Little Theorem (`lucas_order_implies_isPrimeNat`, choice-free `zero custom axioms`):
  If `p ≥ 3` admits ANY base `g` of exact multiplicative order `p - 1` modulo `p`
  (`IsExactMultOrderMod p g (p - 1)`), then `p` is unconditionally prime (`IsPrimeNat p`)!
-/
theorem lucas_order_implies_isPrimeNat (p g : Nat)
    (hp3 : p ≥ 3) (hord : IsExactMultOrderMod p g (p - 1)) :
    IsPrimeNat p := by
  rcases hord with ⟨hp2, _, hpow_pm1, hmin⟩
  refine ⟨hp2, ?_⟩
  intro k hk2 hkp hkdvd
  -- Every `g ^ i % p` (`i < p - 1`) lies in `{1, ..., p - 1} \ {k}` (`p - 2` values):
  have hgi_unit : ∀ i : Nat, i < p - 1 -> 1 ≤ g ^ i % p ∧ g ^ i % p < p ∧ g ^ i % p ≠ k := by
    intro i hi
    have hlt_p : g ^ i % p < p := Nat.mod_lt _ (by omega)
    have hunit : (g ^ i * g ^ (p - 1 - i)) % p = 1 := by
      rw [← Nat.pow_add, show i + (p - 1 - i) = p - 1 by omega, hpow_pm1]
    have hne0 : g ^ i % p ≠ 0 := by
      intro h0
      rw [Nat.mul_mod, h0, Nat.zero_mul, Nat.zero_mod] at hunit
      omega
    have hnek : g ^ i % p ≠ k := by
      intro hgk
      rcases hkdvd with ⟨m, hm⟩
      let qp1 := g ^ i / p
      have hdm : g ^ i = p * qp1 + g ^ i % p := (Nat.div_add_mod (g ^ i) p).symm
      rw [hgk, hm, Nat.mul_assoc k m qp1] at hdm
      have hk_gi : k ∣ g ^ i := ⟨m * qp1 + 1, by rw [Nat.mul_add, Nat.mul_one]; omega⟩
      rcases hk_gi with ⟨c, hc⟩
      have hk_pm1 : k ∣ g ^ (p - 1) := by
        rw [show p - 1 = i + (p - 1 - i) by omega, Nat.pow_add, hc]
        exact ⟨c * g ^ (p - 1 - i), Nat.mul_assoc k c _⟩
      rcases hk_pm1 with ⟨u, hu⟩
      let qp2 := g ^ (p - 1) / p
      have hdm2 : g ^ (p - 1) = p * qp2 + g ^ (p - 1) % p := (Nat.div_add_mod (g ^ (p - 1)) p).symm
      rw [hpow_pm1, hu, hm, Nat.mul_assoc k m qp2] at hdm2
      have hle_u : m * qp2 < u := by
        by_cases h : m * qp2 < u
        · exact h
        · have hmul := Nat.mul_le_mul_left k (by omega : u ≤ m * qp2)
          generalize m * qp2 = MQ at hmul hdm2
          omega
      have h1_eq : k * (u - m * qp2) = 1 := by
        rw [Nat.mul_sub_left_distrib]; omega
      have hge : k * 1 ≤ k * (u - m * qp2) := Nat.mul_le_mul_left k (by omega)
      omega
    exact ⟨by omega, hlt_p, hnek⟩
  let compress : Nat -> Nat := fun y => if y < k then y - 1 else y - 2
  let f : Nat -> Nat := fun i => compress (g ^ i % p)
  have hf_lt : ∀ i : Nat, i < p - 1 -> f i < p - 2 := by
    intro i hi
    rcases hgi_unit i hi with ⟨hge1, hlt_p, hnek⟩
    dsimp [f, compress]
    by_cases hlt_k : g ^ i % p < k <;> simp [hlt_k] <;> omega
  rcases nat_func_pigeonhole (p - 2) (p - 1) f hf_lt (by omega) with ⟨i, j, hij, hj_lt, hfeq⟩
  rcases hgi_unit i (by omega) with ⟨hi1, _, hik⟩
  rcases hgi_unit j hj_lt with ⟨hj1, _, hjk⟩
  have hmod_eq : g ^ i % p = g ^ j % p := by
    dsimp [f, compress] at hfeq
    by_cases h1 : g ^ i % p < k <;> by_cases h2 : g ^ j % p < k <;>
      simp [h1, h2] at hfeq <;> omega
  let d := j - i
  have hd_pos : d ≥ 1 := by dsimp [d]; omega
  have hd_lt : d < p - 1 := by dsimp [d]; omega
  have hinv_i : (g ^ (p - 1 - i) * g ^ i) % p = 1 := by
    rw [← Nat.pow_add, show p - 1 - i + i = p - 1 by omega, hpow_pm1]
  have hd_one : g ^ d % p = 1 := by
    have hmul_eq : (g ^ (p - 1 - i) * g ^ i) % p = (g ^ (p - 1 - i) * g ^ j) % p := by
      rw [Nat.mul_mod (g ^ (p - 1 - i)) (g ^ i), hmod_eq, ← Nat.mul_mod]
    rw [show j = i + d by dsimp [d]; omega, Nat.pow_add g i d,
        ← Nat.mul_assoc (g ^ (p - 1 - i)) (g ^ i) (g ^ d),
        Nat.mul_mod (g ^ (p - 1 - i) * g ^ i) (g ^ d) p,
        hinv_i, Nat.one_mul, Nat.mod_mod] at hmul_eq
    exact hmul_eq.symm
  exact hmin ⟨d, hd_lt⟩ hd_pos hd_one

/--
  Theorem W9.2b (`coprime_primes_45661129_and_107889071_cert`, choice-free `zero custom axioms`):
  Pure-Kernel Pratt–Lucas Primality & Coprime Multiplicative-Order Certificates for
  `331`, `1210483`, `p_3 = 45,661,129` (`% 8 = 1`), and `p_4 = 107,889,071` (`% 8 = 7`):
  1. `IsPrimeNat 331`, `IsPrimeNat 1210483`, `IsPrimeNat 45661129`, `IsPrimeNat 107889071`;
  2. At `p_3 = 45,661,129`: `ord(2) = 12,381`, `ord(3/2) = 1,844`, `gcd = 1`, `45661129 % 8 = 1`;
  3. At `p_4 = 107,889,071`: `ord(2) = 52,835`, `ord(3/2) = 1,021`, `gcd = 1`, `107889071 % 8 = 7`!
-/
theorem coprime_primes_45661129_and_107889071_cert :
    IsPrimeNat 331 ∧
    IsPrimeNat 1210483 ∧
    IsPrimeNat 45661129 ∧
    IsPrimeNat 107889071 ∧
    IsExactMultOrderMod 45661129 2 12381 ∧
    IsExactMultOrderMod 45661129 (ratio32Mod 45661129) 1844 ∧
    Nat.gcd 12381 1844 = 1 ∧
    45661129 % 8 = 1 ∧
    IsExactMultOrderMod 107889071 2 52835 ∧
    IsExactMultOrderMod 107889071 (ratio32Mod 107889071) 1021 ∧
    Nat.gcd 52835 1021 = 1 ∧
    107889071 % 8 = 7 := by
  have hc_p1 : checkPrimeFactorsOrderBool 331 3 330 [2, 3, 5, 11] = true := by decide
  have hc_p2 : checkPrimeFactorsOrderBool 1210483 5 1210482 [2, 3, 3, 7, 13, 739] = true := by decide
  have hc_p3 : checkPrimeFactorsOrderBool 45661129 7 45661128 [2, 2, 2, 3, 461, 4127] = true := by decide
  have hc_p4 : checkPrimeFactorsOrderBool 107889071 11 107889070 [2, 5, 1021, 10567] = true := by decide
  have hc_o3_2 : checkPrimeFactorsOrderBool 45661129 2 12381 [3, 4127] = true := by decide
  have hc_o3_32 : checkPrimeFactorsOrderBool 45661129 (ratio32Mod 45661129) 1844 [2, 2, 461] = true := by decide
  have hc_o4_2 : checkPrimeFactorsOrderBool 107889071 2 52835 [5, 10567] = true := by decide
  have hc_o4_32 : checkPrimeFactorsOrderBool 107889071 (ratio32Mod 107889071) 1021 [1021] = true := by decide
  exact ⟨lucas_order_implies_isPrimeNat 331 3 (by decide) (checkPrimeFactorsOrderBool_sound _ _ _ _ hc_p1),
         lucas_order_implies_isPrimeNat 1210483 5 (by decide) (checkPrimeFactorsOrderBool_sound _ _ _ _ hc_p2),
         lucas_order_implies_isPrimeNat 45661129 7 (by decide) (checkPrimeFactorsOrderBool_sound _ _ _ _ hc_p3),
         lucas_order_implies_isPrimeNat 107889071 11 (by decide) (checkPrimeFactorsOrderBool_sound _ _ _ _ hc_p4),
         checkPrimeFactorsOrderBool_sound _ _ _ _ hc_o3_2,
         checkPrimeFactorsOrderBool_sound _ _ _ _ hc_o3_32,
         by decide,
         by decide,
         checkPrimeFactorsOrderBool_sound _ _ _ _ hc_o4_2,
         checkPrimeFactorsOrderBool_sound _ _ _ _ hc_o4_32,
         by decide,
         by decide⟩

-- Choice-free `{5, 7} mod 8` prime divisor extraction & Joint `(331, 107889071)` Floors:

theorem mod8_5_or_7_has_prime_div_5_or_7 :
    ∀ (bound m : Nat),
      m ≤ bound -> (m % 8 = 5 ∨ m % 8 = 7) ->
      ∃ q : Nat, IsPrimeNat q ∧ q ∣ m ∧ (q % 8 = 5 ∨ q % 8 = 7)
  | 0, m, hm0, hm8 => by rw [show m = 0 by omega] at hm8; rcases hm8 with h | h <;> cases h
  | bound + 1, m, hmb, hm8 => by
    have hm_ge5 : m ≥ 5 := by rcases hm8 with h | h <;> omega
    let q0 := findMinDivAux m m 2
    rcases findMinDivAux_spec m (by omega) m 2 (Nat.le_refl 2) (by omega) (by omega)
      (fun _ hk2 hlt => by omega) with ⟨hq0_p, c, hc⟩
    change IsPrimeNat q0 at hq0_p
    change m = q0 * c at hc
    by_cases hq0_eq_m : q0 = m
    · rw [hq0_eq_m] at hq0_p
      exact ⟨m, hq0_p, Nat.dvd_refl m, hm8⟩
    · have hq0_ge2 := hq0_p.1
      have hq0_lt : q0 < m := by
        cases c with
        | zero => simp at hc; omega
        | succ c' =>
          cases c' with
          | zero => rw [Nat.mul_one] at hc; exact False.elim (hq0_eq_m hc.symm)
          | succ c'' =>
            have h2 : c'' + 1 + 1 = c'' + 2 := by omega
            rw [h2] at hc
            have hge := Nat.mul_le_mul_left q0 (by omega : 2 ≤ c'' + 2)
            omega
      have hc_lt : c < m := by
        have hge := Nat.mul_le_mul_right c hq0_ge2
        omega
      have hm_odd : m % 2 = 1 := by rcases hm8 with h | h <;> omega
      have hq0_odd : q0 % 2 = 1 := by
        by_cases he : q0 % 2 = 0
        · have hq2 : q0 = 2 * (q0 / 2) := by omega
          have h2m : 2 ∣ m := ⟨(q0 / 2) * c, by conv => lhs; rw [hc, hq2]; rw [Nat.mul_assoc]⟩
          have hm0 := Nat.mod_eq_zero_of_dvd h2m; omega
        · omega
      have hc_odd : c % 2 = 1 := by
        by_cases he : c % 2 = 0
        · have hc2 : c = 2 * (c / 2) := by omega
          have h2m : 2 ∣ m := ⟨q0 * (c / 2), by
            conv => lhs; rw [hc, hc2]
            rw [← Nat.mul_assoc q0 2, Nat.mul_comm q0 2, Nat.mul_assoc]⟩
          have hm0 := Nat.mod_eq_zero_of_dvd h2m; omega
        · omega
      by_cases hq0_57 : q0 % 8 = 5 ∨ q0 % 8 = 7
      · exact ⟨q0, hq0_p, ⟨c, hc⟩, hq0_57⟩
      · have hq0_13 : q0 % 8 = 1 ∨ q0 % 8 = 3 := by omega
        have hc_57 : c % 8 = 5 ∨ c % 8 = 7 := by
          by_cases hc_13 : c % 8 = 1 ∨ c % 8 = 3
          · have hprod13 := prod_mod8_in_1_or_3 [q0, c] (by
              intro x hx
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
              rcases hx with rfl | rfl
              · exact hq0_13
              · exact hc_13)
            simp only [natProdList, Nat.mul_one, ← hc] at hprod13
            rcases hm8 with h5 | h7 <;> rcases hprod13 with h1 | h3 <;> omega
          · omega
        rcases mod8_5_or_7_has_prime_div_5_or_7 bound c (by omega) hc_57 with ⟨q, hqp, hqc, hq57⟩
        exact ⟨q, hqp, Nat.dvd_trans hqc ⟨q0, by rw [hc, Nat.mul_comm]⟩, hq57⟩

theorem lcm_coprime_dvd (a b m : Nat) (hcop : Nat.gcd a b = 1)
    (ha : a ∣ m) (hb : b ∣ m) : (a * b) ∣ m := by
  rcases ha with ⟨k, hk⟩
  have hcop_dvd : ∀ (bound B A K : Nat),
      B ≤ bound -> B ≥ 1 -> Nat.gcd A B = 1 -> B ∣ (A * K) -> B ∣ K := by
    intro bound
    induction bound with
    | zero => intro B _ _ _ hB0 hB1; omega
    | succ bd ih =>
      intro B A K hBb hB1 hg hdvd
      by_cases hB_eq1 : B = 1
      · subst hB_eq1; exact ⟨K, (Nat.one_mul K).symm⟩
      · rcases exists_prime_divisor_of_ge_two B (by omega) with ⟨q, hqp, B', hB'⟩
        have hq_nd_A : ¬ (q ∣ A) := by
          intro hqA
          have hqB : q ∣ B := ⟨B', hB'⟩
          have hqg : q ∣ Nat.gcd A B := Nat.dvd_gcd hqA hqB
          rw [hg] at hqg
          have h1 := Nat.eq_one_of_dvd_one hqg
          have hp2 := hqp.1; omega
        have hq_AK : q ∣ (A * K) := Nat.dvd_trans ⟨B', hB'⟩ hdvd
        have hq_K : q ∣ K := by
          rcases gauss_euclid_lemma q A K hqp hq_AK with hqA | hqK
          · exact False.elim (hq_nd_A hqA)
          · exact hqK
        rcases hq_K with ⟨K', hK'⟩
        rcases hdvd with ⟨u, hu⟩
        rw [hB', hK'] at hu
        have hAK_eq : q * (B' * u) = q * (A * K') := by
          calc
            q * (B' * u) = (q * B') * u := (Nat.mul_assoc q B' u).symm
            _ = A * (q * K') := hu.symm
            _ = (A * q) * K' := (Nat.mul_assoc A q K').symm
            _ = (q * A) * K' := by rw [Nat.mul_comm A q]
            _ = q * (A * K') := Nat.mul_assoc q A K'
        have hB'_AK' : B' ∣ (A * K') := ⟨u, (Nat.eq_of_mul_eq_mul_left (by have := hqp.1; omega) hAK_eq).symm⟩
        have hB'_pos : B' ≥ 1 := by
          cases B' with
          | zero => simp at hB'; omega
          | succ _ => omega
        have hB'_lt : B' < B := by
          have h2 := Nat.mul_le_mul_right B' hqp.1; omega
        have hcop' : Nat.gcd A B' = 1 := by
          let g' := Nat.gcd A B'
          have hg'_A : g' ∣ A := Nat.gcd_dvd_left A B'
          have hg'_B : g' ∣ B := Nat.dvd_trans (Nat.gcd_dvd_right A B') ⟨q, by rw [hB', Nat.mul_comm]⟩
          have hg'_g : g' ∣ Nat.gcd A B := Nat.dvd_gcd hg'_A hg'_B
          rw [hg] at hg'_g
          exact Nat.eq_one_of_dvd_one hg'_g
        rcases ih B' A K' (by omega) hB'_pos hcop' hB'_AK' with ⟨v, hv⟩
        exact ⟨v, by rw [hB', hK', hv, Nat.mul_assoc]⟩
  by_cases hb0 : b = 0
  · subst hb0; rcases hb with ⟨u, hu⟩; simp at hu; subst hu; exact ⟨0, by simp⟩
  · rcases hcop_dvd b b a k (Nat.le_refl b) (by omega) hcop (by rw [← hk]; exact hb) with ⟨v, hv⟩
    exact ⟨v, by rw [hk, hv, Nat.mul_assoc]⟩

-- Standalone order-divisibility & binary-arithmetic wrappers (avoiding `whnf` on `2 ^ 52835` inside `omega`):

theorem p4_107889071_order_dvd_one_block (w1 a1 q0 : Nat)
    (hw1 : w1 ≥ 2) (ha1 : a1 ≥ 1) (hgt : 3 ^ w1 < 2 ^ (w1 + a1))
    (hbrox : (2 ^ (w1 + a1) - 3 ^ w1) * q0 = 2 ^ a1 - 1)
    (hp4_D : 107889071 ∣ (2 ^ (w1 + a1) - 3 ^ w1)) :
    52835 ∣ a1 ∧ 1021 ∣ w1 := by
  have hp3 : 107889071 ≥ 3 := by decide
  have hpo : 107889071 % 2 = 1 := by decide
  rcases one_block_cyclotomic_companion_quotient_forcing
    w1 a1 q0 107889071 52835 1021 hw1 ha1 hgt hbrox hp3 hpo
    coprime_primes_45661129_and_107889071_cert.2.2.2.2.2.2.2.2.1
    coprime_primes_45661129_and_107889071_cert.2.2.2.2.2.2.2.2.2.1 hp4_D with
    ⟨_, ha, hw, _, _, _, _⟩
  exact ⟨ha, hw⟩

theorem p4_107889071_pow_dvd_helper (a1 a2 W : Nat)
    (h2a1 : 2 ^ a1 % 107889071 = 1)
    (h2a2 : 2 ^ a2 % 107889071 = 1)
    (h32W : 3 ^ W % 107889071 = 2 ^ W % 107889071) :
    52835 ∣ a1 ∧ 52835 ∣ a2 ∧ 1021 ∣ W := by
  have hp3 : 107889071 ≥ 3 := by decide
  have hpo : 107889071 % 2 = 1 := by decide
  exact ⟨exactMultOrderMod_dvd_of_pow_eq_one 107889071 2 52835 a1
           coprime_primes_45661129_and_107889071_cert.2.2.2.2.2.2.2.2.1 h2a1,
         exactMultOrderMod_dvd_of_pow_eq_one 107889071 2 52835 a2
           coprime_primes_45661129_and_107889071_cert.2.2.2.2.2.2.2.2.1 h2a2,
         exactMultOrderMod_dvd_of_pow_eq_one 107889071 (ratio32Mod 107889071) 1021 W
           coprime_primes_45661129_and_107889071_cert.2.2.2.2.2.2.2.2.2.1
           (ratio32Mod_pow_eq_one_of_pow3_eq_pow2 107889071 W hp3 hpo h32W)⟩

theorem w9_joint_lcm_arith_cert :
    Nat.gcd 331 107889071 = 1 ∧
    331 * 107889071 = 35711282501 ∧
    Nat.gcd 11 1021 = 1 ∧
    11 * 1021 = 11231 ∧
    Nat.gcd 6 52835 = 1 ∧
    6 * 52835 = 317010 ∧
    11231 * 48 = 2 * (11231 * 24) ∧
    331 % 8 = 3 ∧
    1210483 % 8 = 3 ∧
    45661129 % 8 = 1 := by
  decide

private theorem one_block_five_a_lt_three_w (w1 a1 q0 : Nat)
    (hw1 : w1 ≥ 2) (ha1 : a1 ≥ 1) (hgt : 3 ^ w1 < 2 ^ (w1 + a1))
    (hbrox : (2 ^ (w1 + a1) - 3 ^ w1) * q0 = 2 ^ a1 - 1) :
    5 * a1 < 3 * w1 + 5 := by
  have h2_lt_3w : 2 ^ (w1 + a1 - 1) < 3 ^ w1 := by
    have hq0_pos : q0 ≥ 1 := by
      cases q0 with
      | zero => rw [Nat.mul_zero] at hbrox; have hp2 := pow2_mono_nat ha1; omega
      | succ _ => omega
    have hD_le : 2 ^ (w1 + a1) - 3 ^ w1 ≤ 2 ^ a1 - 1 := by
      have hm := Nat.mul_le_mul_left (2 ^ (w1 + a1) - 3 ^ w1) hq0_pos
      rw [Nat.mul_one, hbrox] at hm; exact hm
    have hsplit : 2 ^ (w1 + a1) = 2 * 2 ^ (w1 + a1 - 1) :=
      pow2_split_pred (w1 + a1) (by omega)
    have ha1_le : 2 ^ a1 ≤ 2 ^ (w1 + a1 - 1) := pow2_mono_nat (by omega)
    clear hbrox
    generalize 2 ^ (w1 + a1 - 1) = P_half, 2 ^ (w1 + a1) = P_full,
      3 ^ w1 = Q_full, 2 ^ a1 = P_a1 at hgt hD_le hsplit ha1_le ⊢
    omega
  clear hgt hbrox
  let E := w1 + a1 - 1
  have hp5 : (2 ^ E) ^ 5 < (3 ^ w1) ^ 5 := by
    have hle4 := nat_pow_mono_base (2 ^ E) (3 ^ w1) (Nat.le_of_lt h2_lt_3w) 4
    have hpos4 := nat_pow_pos_of_pos (2 ^ E) (pow2_pos_nat E) 4
    have hm1 : (2 ^ E) ^ 4 * 2 ^ E < (2 ^ E) ^ 4 * 3 ^ w1 :=
      Nat.mul_lt_mul_of_pos_left h2_lt_3w hpos4
    have hm2 : (2 ^ E) ^ 4 * 3 ^ w1 ≤ (3 ^ w1) ^ 4 * 3 ^ w1 :=
      Nat.mul_le_mul_right (3 ^ w1) hle4
    exact Nat.lt_of_lt_of_le hm1 hm2
  rw [pow_pow_eq_mul_w5 2 E 5, pow_pow_eq_mul_w5 3 w1 5,
      Nat.mul_comm w1 5, ← pow_pow_eq_mul_w5 3 5 w1] at hp5
  have h243_le_256 : (3 ^ 5) ^ w1 ≤ (2 ^ 8) ^ w1 :=
    nat_pow_mono_base (3 ^ 5) (2 ^ 8) (by decide) w1
  rw [pow_pow_eq_mul_w5 2 8 w1] at h243_le_256
  have h2_lt_2 : 2 ^ (E * 5) < 2 ^ (8 * w1) := Nat.lt_of_lt_of_le hp5 h243_le_256
  clear hp5 h243_le_256 h2_lt_3w
  by_cases h : 5 * a1 < 3 * w1 + 5
  · exact h
  · have hm := pow2_mono_nat (by dsimp [E]; omega : 8 * w1 ≤ E * 5)
    generalize 2 ^ (E * 5) = PE, 2 ^ (8 * w1) = PW at h2_lt_2 hm
    omega

private theorem joint_331_p4_arith_floor (w1 a1 q0 : Nat)
    (hw1 : w1 ≥ 2) (ha1 : a1 ≥ 1) (hgt : 3 ^ w1 < 2 ^ (w1 + a1))
    (hbrox : (2 ^ (w1 + a1) - 3 ^ w1) * q0 = 2 ^ a1 - 1)
    (h317010_a1 : 317010 ∣ a1) (h11231_w1 : 11231 ∣ w1) (hodd_w1 : ¬ (2 ∣ w1))
    (hkw48_ev : 11231 * 48 = 2 * (11231 * 24)) :
    w1 ≥ 550319 ∧ a1 ≥ 317010 ∧ w1 + a1 ≥ 867329 := by
  have h5a1_lt := one_block_five_a_lt_three_w w1 a1 q0 hw1 ha1 hgt hbrox
  clear hgt hbrox
  rcases h317010_a1 with ⟨ka, rfl⟩
  rcases h11231_w1 with ⟨kw, rfl⟩
  have ha_ge : 317010 ≤ 317010 * ka := by
    cases ka with
    | zero => rw [Nat.mul_zero] at ha1; omega
    | succ ka' =>
      have hm := Nat.mul_le_mul_left 317010 (by omega : 1 ≤ ka' + 1)
      rwa [Nat.mul_one] at hm
  have hkw_gt47 : ¬ (kw ≤ 47) := by
    intro hle47
    have hm1 : 3 * (11231 * kw) + 5 ≤ 3 * (11231 * 47) + 5 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left 11231 hle47)) 5
    have hm2 : 3 * (11231 * 47) + 5 ≤ 5 * 317010 := by decide
    have hm3 : 5 * 317010 ≤ 5 * (317010 * ka) := Nat.mul_le_mul_left 5 ha_ge
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h5a1_lt (Nat.le_trans hm1 (Nat.le_trans hm2 hm3)))
  have hkw_ne48 : kw ≠ 48 := by
    intro hkw48
    exact hodd_w1 ⟨11231 * 24, by rw [hkw48, hkw48_ev]⟩
  have hkw_ge49 : 49 ≤ kw := by
    clear h5a1_lt ha_ge ha1 hw1 hodd_w1 hkw48_ev
    omega
  have hw_ge : 550319 ≤ 11231 * kw := by
    have hc : 550319 = 11231 * 49 := by decide
    rw [hc]
    exact Nat.mul_le_mul_left 11231 hkw_ge49
  have hsum_ge : 867329 ≤ 11231 * kw + 317010 * ka := by
    have hc : 867329 = 550319 + 317010 := by decide
    rw [hc]
    exact Nat.add_le_add hw_ge ha_ge
  exact ⟨hw_ge, ha_ge, hsum_ge⟩

/--
  Theorem W9.2c (`one_block_331_forces_mod8_escape_and_joint_p4_floors`, `zero custom axioms`):
  Third Coprime Prime `p_3 = 45,661,129` (`≡ 1 mod 8`) Obstruction, Mandatory `{5, 7} mod 8`
  Prime Escape, & Joint `(331, 107889071)` 1-Block / 2-Block Weight Floors:
  1. On ANY 1-block positive cycle (`w1 ≥ 2, a1 ≥ 1, 3 ^ w1 < 2 ^ (w1 + a1), D * q0 = 2 ^ a1 - 1`)
     with `331 ∣ D`:
     - `D ≠ 331 ^ e1 * 1210483 ^ e2 * 45661129 ^ e3` for ALL `e1, e2, e3 : Nat` (`45661129 % 8 = 1`
       remains trapped inside the closed `{1, 3} mod 8` multiplicative subgroup!);
     - `D` MUST have an odd prime divisor `q` (`IsPrimeNat q`, `q ∣ D`) with `q % 8 = 5 ∨ q % 8 = 7`
       (in particular `q ∉ {331, 1210483, 45661129}`)!
  2. If `D` is jointly divisible by `331` and the minimal `{5, 7} mod 8` coprime-order prime
     `p_4 = 107,889,071` (`331 ∣ D ∧ 107889071 ∣ D`), then:
     - `35711282501 ∣ D` (`331 * 107889071 = 35,711,282,501`);
     - `11231 ∣ w1` (`lcm(11, 1021) = 11,231`), `317010 ∣ a1` (`lcm(30, 52835) = 317,010`),
       and `Nat.gcd w1 317010 = 1`;
     - **`w1 ≥ 550319`** (`49 * 11231`), **`a1 ≥ 317010`**, and **`w1 + a1 ≥ 867329`**!
  3. On ANY 2-block primitive Brox witness (`IsPrimitiveTwoBlockBroxWitness`) with
     `107889071 ∣ D` and `107889071 ∣ (2 ^ a1 - 1)`:
     - `52835 ∣ a1`, `52835 ∣ a2`, `1021 ∣ (w1 + w2)`;
     - **`w1 + w2 ≥ 159276`** (`156 * 1021`), **`a1 + a2 ≥ 105670`**, and **`w1 + a1 + w2 + a2 ≥ 264946`**!
-/
theorem one_block_331_forces_mod8_escape_and_joint_p4_floors :
    (∀ (w1 a1 q0 : Nat),
      w1 ≥ 2 -> a1 ≥ 1 -> 3 ^ w1 < 2 ^ (w1 + a1) ->
      (2 ^ (w1 + a1) - 3 ^ w1) * q0 = 2 ^ a1 - 1 ->
      let D := 2 ^ (w1 + a1) - 3 ^ w1
      331 ∣ D ->
      (∀ e1 e2 e3 : Nat, D ≠ 331 ^ e1 * 1210483 ^ e2 * 45661129 ^ e3) ∧
      (∃ q : Nat, IsPrimeNat q ∧ q ∣ D ∧ (q % 8 = 5 ∨ q % 8 = 7) ∧
        q ≠ 331 ∧ q ≠ 1210483 ∧ q ≠ 45661129) ∧
      (107889071 ∣ D ->
        35711282501 ∣ D ∧
        11231 ∣ w1 ∧
        317010 ∣ a1 ∧
        Nat.gcd w1 317010 = 1 ∧
        w1 ≥ 550319 ∧
        a1 ≥ 317010 ∧
        w1 + a1 ≥ 867329)) ∧
    (∀ (w1 a1 w2 a2 q0 q1 : Nat),
      IsPrimitiveTwoBlockBroxWitness w1 a1 w2 a2 q0 q1 ->
      107889071 ∣ (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)) ->
      107889071 ∣ (2 ^ a1 - 1) ->
      52835 ∣ a1 ∧
      52835 ∣ a2 ∧
      1021 ∣ (w1 + w2) ∧
      w1 + w2 ≥ 159276 ∧
      a1 + a2 ≥ 105670 ∧
      w1 + a1 + w2 + a2 ≥ 264946) := by
  rcases w9_joint_lcm_arith_cert with
    ⟨hg_331_p4, hmul_331_p4, hg_11_1021, hmul_11_1021, hg_6_52835, hmul_6_52835,
     hkw48_ev, h331_m8, h1210_m8, hp3_m8⟩
  refine ⟨?_, ?_⟩
  · intro w1 a1 q0 hw1 ha1 hgt hbrox
    dsimp only
    let D := 2 ^ (w1 + a1) - 3 ^ w1
    intro h331_D
    rcases (one_block_331_companion_forcing_and_mod8_obstruction w1 a1 q0 hw1 ha1 hgt hbrox).2 h331_D with
      ⟨h30_a1, h11_w1, hcop_w30, _, _, _, _, hD_m8, _, hnot_prod13⟩
    have hnot_triple : ∀ e1 e2 e3 : Nat, D ≠ 331 ^ e1 * 1210483 ^ e2 * 45661129 ^ e3 := by
      intro e1 e2 e3 heq
      have hm1 := pow_mod8_in_1_or_3 331 (Or.inr h331_m8) e1
      have hm2 := pow_mod8_in_1_or_3 1210483 (Or.inr h1210_m8) e2
      have hm3 := pow_mod8_in_1_or_3 45661129 (Or.inl hp3_m8) e3
      have hlist : 331 ^ e1 * 1210483 ^ e2 * 45661129 ^ e3 =
          natProdList [331 ^ e1, 1210483 ^ e2, 45661129 ^ e3] := by
        simp [natProdList, Nat.mul_assoc]
      rw [hlist] at heq
      apply hnot_prod13 [331 ^ e1, 1210483 ^ e2, 45661129 ^ e3] _ heq
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl
      · exact hm1
      · exact hm2
      · exact hm3
    rcases mod8_5_or_7_has_prime_div_5_or_7 D D (Nat.le_refl D) (Or.inl hD_m8) with
      ⟨q, hqp, hqD, hq57⟩
    have hq_ne : q ≠ 331 ∧ q ≠ 1210483 ∧ q ≠ 45661129 := by
      refine ⟨?_, ?_, ?_⟩
      · intro heq; rw [heq, h331_m8] at hq57; rcases hq57 with h | h <;> cases h
      · intro heq; rw [heq, h1210_m8] at hq57; rcases hq57 with h | h <;> cases h
      · intro heq; rw [heq, hp3_m8] at hq57; rcases hq57 with h | h <;> cases h
    refine ⟨hnot_triple, ⟨q, hqp, hqD, hq57, hq_ne⟩, ?_⟩
    intro hp4_D
    have hprod_D : 35711282501 ∣ D := by
      have hm := lcm_coprime_dvd 331 107889071 D hg_331_p4 h331_D hp4_D
      rwa [hmul_331_p4] at hm
    rcases p4_107889071_order_dvd_one_block w1 a1 q0 hw1 ha1 hgt hbrox hp4_D with
      ⟨h52835_a1, h1021_w1⟩
    have h11231_w1 : 11231 ∣ w1 := by
      have hm := lcm_coprime_dvd 11 1021 w1 hg_11_1021 h11_w1 h1021_w1
      rwa [hmul_11_1021] at hm
    have h6_a1 : 6 ∣ a1 := Nat.dvd_trans ⟨5, rfl⟩ h30_a1
    have h317010_a1 : 317010 ∣ a1 := by
      have hm := lcm_coprime_dvd 6 52835 a1 hg_6_52835 h6_a1 h52835_a1
      rwa [hmul_6_52835] at hm
    have hcop_wa : Nat.gcd w1 a1 = 1 := one_block_exponents_coprime w1 a1 q0 hw1 ha1 hgt hbrox
    have hcop_w317 : Nat.gcd w1 317010 = 1 := by
      let g := Nat.gcd w1 317010
      have hg_w1 : g ∣ w1 := Nat.gcd_dvd_left w1 317010
      have hg_a1 : g ∣ a1 := Nat.dvd_trans (Nat.gcd_dvd_right w1 317010) h317010_a1
      have hg_wa : g ∣ Nat.gcd w1 a1 := Nat.dvd_gcd hg_w1 hg_a1
      rw [hcop_wa] at hg_wa
      exact Nat.eq_one_of_dvd_one hg_wa
    have hodd_w1 : ¬ (2 ∣ w1) := by
      intro h2_w1
      have h2_g : 2 ∣ Nat.gcd w1 30 := Nat.dvd_gcd h2_w1 ⟨15, rfl⟩
      rw [hcop_w30] at h2_g
      cases Nat.eq_one_of_dvd_one h2_g
    rcases joint_331_p4_arith_floor w1 a1 q0 hw1 ha1 hgt hbrox h317010_a1 h11231_w1 hodd_w1 hkw48_ev with
      ⟨hw1_ge550319, ha1_ge, hK_ge⟩
    exact ⟨hprod_D, h11231_w1, h317010_a1, hcop_w317, hw1_ge550319, ha1_ge, hK_ge⟩
  · -- 2-block shared-Mersenne `107889071 ∣ D` floor (`W ≥ 159276`, `K ≥ 264946`):
    intro w1 a1 w2 a2 q0 q1 hprim hp4_D hp4_a1
    rcases hprim with
      ⟨hw1, ha1, hw2, ha2, _, _, _, _, _, _, hband_lo, hband_hi, _, _, _, _, _, _, _, _, hbrox0, _, _⟩
    let W := w1 + w2
    let K := w1 + a1 + w2 + a2
    let D := 2 ^ K - 3 ^ W
    have hgt : 3 ^ W < 2 ^ K := by
      change 21 ^ W < 7 ^ W * 2 ^ K at hband_lo
      rw [show (21 : Nat) ^ W = 7 ^ W * 3 ^ W from mul_pow_nat 7 3 W] at hband_lo
      by_cases hlt : 3 ^ W < 2 ^ K
      · exact hlt
      · have hm := Nat.mul_le_mul_left (7 ^ W) (by omega : 2 ^ K ≤ 3 ^ W)
        generalize 7 ^ W = p7, 3 ^ W = p3, 2 ^ K = p2 at hband_lo hm
        omega
    have hdvd_H0 : D ∣ broxSpiralCarry [(w1, a1), (w2, a2)] := by
      have hcar_eq : broxSpiralCarry [(w1, a1), (w2, a2)] = twoBlockBroxCarry w1 a1 w2 a2 := by
        simp [broxSpiralCarry, twoBlockBroxCarry, blockWeightSum]
      rw [hcar_eq]; exact ⟨q0, hbrox0.symm⟩
    rcases (two_block_shared_mersenne_propagation_and_equal_even_exclusion
      w1 a1 w2 a2 (by omega) ha1 hw2 ha2 hgt).1 hdvd_H0 107889071 (by decide) hp4_D with ⟨hiff_a2, h3W2W⟩
    have hp4_a2 : 107889071 ∣ (2 ^ a2 - 1) := hiff_a2.mp hp4_a1
    have hp4_diffW : 107889071 ∣ (3 ^ W - 2 ^ W) := h3W2W hp4_a1
    have h1_lt_p4 : 1 < 107889071 := by decide
    have h2a1 : 2 ^ a1 % 107889071 = 1 := by
      rcases hp4_a1 with ⟨m, hm⟩
      have hp2 : 2 ^ a1 ≥ 2 := by simpa using pow2_mono_nat ha1
      have hrew : 2 ^ a1 = 1 + 107889071 * m := by
        generalize 2 ^ a1 = pa1, 107889071 * m = pm at hm hp2 ⊢; omega
      rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1_lt_p4]
    have h2a2 : 2 ^ a2 % 107889071 = 1 := by
      rcases hp4_a2 with ⟨m, hm⟩
      have hp2 : 2 ^ a2 ≥ 2 := by simpa using pow2_mono_nat ha2
      have hrew : 2 ^ a2 = 1 + 107889071 * m := by
        generalize 2 ^ a2 = pa2, 107889071 * m = pm at hm hp2 ⊢; omega
      rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1_lt_p4]
    have h32W : 3 ^ W % 107889071 = 2 ^ W % 107889071 := by
      rcases hp4_diffW with ⟨m, hm⟩
      have h2le3 : 2 ^ W ≤ 3 ^ W := pow2_le_pow3 W
      have hrew : 3 ^ W = 2 ^ W + 107889071 * m := by
        generalize 3 ^ W = p3, 2 ^ W = p2, 107889071 * m = pm at hm h2le3 ⊢; omega
      rw [hrew, Nat.add_mul_mod_self_left]
    rcases p4_107889071_pow_dvd_helper a1 a2 W h2a1 h2a2 h32W with ⟨h52835_a1, h52835_a2, h1021_W⟩
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
      · have hm := pow2_mono_nat (by omega : 5 * W ≤ K * 3)
        generalize 2 ^ (K * 3) = pk, 2 ^ (5 * W) = pw at h2_lt hm
        omega
    clear hband_lo hband_hi hbrox0 hgt hdvd_H0 hp4_D hp4_a1 hp4_a2 hp4_diffW hiff_a2 h3W2W h2a1 h2a2 h32W D
    have ha1_ge : 52835 ≤ a1 := by
      rcases h52835_a1 with ⟨k1, hk1⟩
      cases k1 with
      | zero => rw [Nat.mul_zero] at hk1; omega
      | succ k1' =>
        have hm := Nat.mul_le_mul_left 52835 (by omega : 1 ≤ k1' + 1)
        rwa [Nat.mul_one, ← hk1] at hm
    have ha2_ge : 52835 ≤ a2 := by
      rcases h52835_a2 with ⟨k2, hk2⟩
      cases k2 with
      | zero => rw [Nat.mul_zero] at hk2; omega
      | succ k2' =>
        have hm := Nat.mul_le_mul_left 52835 (by omega : 1 ≤ k2' + 1)
        rwa [Nat.mul_one, ← hk2] at hm
    have ha_sum_ge : 105670 ≤ a1 + a2 := by
      have hc : 105670 = 52835 + 52835 := by decide
      rw [hc]
      exact Nat.add_le_add ha1_ge ha2_ge
    have h2W_gt : 3 * 105670 < 2 * W := by
      have hK_eq : K = W + (a1 + a2) := by dsimp [K, W]; omega
      rw [hK_eq, Nat.mul_add 3 W (a1 + a2)] at h3K_lt_5W
      have hm3 : 3 * 105670 ≤ 3 * (a1 + a2) := Nat.mul_le_mul_left 3 ha_sum_ge
      have h5W : 5 * W = 3 * W + 2 * W := by rw [show (5 : Nat) = 3 + 2 from rfl, Nat.add_mul]
      rw [h5W] at h3K_lt_5W
      exact Nat.lt_of_le_of_lt hm3 (Nat.lt_of_add_lt_add_left h3K_lt_5W)
    have hW_ge : 159276 ≤ w1 + w2 := by
      change 159276 ≤ W
      rcases h1021_W with ⟨kw, hkw⟩
      have hkw_gt155 : ¬ (kw ≤ 155) := by
        intro hle155
        have hm1 : 2 * W ≤ 2 * (1021 * 155) := by
          rw [hkw]
          exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 1021 hle155)
        have hm2 : 2 * (1021 * 155) ≤ 3 * 105670 := by decide
        exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h2W_gt (Nat.le_trans hm1 hm2))
      have hkw_ge156 : 156 ≤ kw := by
        clear h2W_gt hkw h3K_lt_5W ha_sum_ge ha1_ge ha2_ge h52835_a1 h52835_a2 hw1 ha1 hw2 ha2 K W
        omega
      rw [hkw, show (159276 : Nat) = 1021 * 156 by decide]
      exact Nat.mul_le_mul_left 1021 hkw_ge156
    have hK_ge : 264946 ≤ w1 + a1 + w2 + a2 := by
      have hrew : w1 + a1 + w2 + a2 = (w1 + w2) + (a1 + a2) := by
        clear hW_ge ha_sum_ge h2W_gt h3K_lt_5W ha1_ge ha2_ge h52835_a1 h52835_a2 h1021_W K W
        omega
      rw [hrew, show (264946 : Nat) = 159276 + 105670 by decide]
      exact Nat.add_le_add hW_ge ha_sum_ge
    exact ⟨h52835_a1, h52835_a2, h1021_W, hW_ge, ha_sum_ge, hK_ge⟩

theorem p3_45661129_order_dvd_one_block (w1 a1 q0 : Nat)
    (hw1 : w1 ≥ 2) (ha1 : a1 ≥ 1) (hgt : 3 ^ w1 < 2 ^ (w1 + a1))
    (hbrox : (2 ^ (w1 + a1) - 3 ^ w1) * q0 = 2 ^ a1 - 1)
    (hp3_D : 45661129 ∣ (2 ^ (w1 + a1) - 3 ^ w1)) :
    (2 ^ (w1 + a1) - 3 ^ w1) * (2 ^ w1 * q0 - 1) = 3 ^ w1 - 2 ^ w1 ∧
    12381 ∣ a1 ∧ 1844 ∣ w1 := by
  rcases one_block_cyclotomic_companion_quotient_forcing
    w1 a1 q0 45661129 12381 1844 hw1 ha1 hgt hbrox (by decide) (by decide)
    coprime_primes_45661129_and_107889071_cert.2.2.2.2.1
    coprime_primes_45661129_and_107889071_cert.2.2.2.2.2.1 hp3_D with
    ⟨hDx0, ha, hw, _, _, _, _⟩
  exact ⟨hDx0, ha, hw⟩

/-- Pure-kernel (`[]` axioms) cyclotomic companion-factor certificate for `p_3` and `p_4`. -/
theorem p3_p4_companion_arith_cert :
    checkExactMultOrderBool 5 2 4 = true ∧
    checkExactMultOrderBool 5 (ratio32Mod 5) 2 = true ∧
    checkExactMultOrderBool 13 2 12 = true ∧
    checkExactMultOrderBool 13 (ratio32Mod 13) 4 = true ∧
    checkSmallPrimeBool 5 = true ∧
    checkSmallPrimeBool 7 = true ∧
    checkSmallPrimeBool 13 = true ∧
    checkSmallPrimeBool 31 = true ∧
    Nat.gcd 5 13 = 1 ∧
    5 * 13 = 65 ∧
    2 ^ 5 - 1 = 31 ∧
    52835 = 5 * 10567 ∧
    2 ^ 3 - 1 = 7 ∧
    12381 = 3 * 4127 ∧
    3 ^ 4 - 2 ^ 4 = 65 ∧
    1844 = 4 * 461 := by
  decide

private theorem solo_p4_arith_floor (w1 a1 q0 : Nat)
    (hw1 : w1 ≥ 2) (ha1 : a1 ≥ 1) (hgt : 3 ^ w1 < 2 ^ (w1 + a1))
    (hbrox : (2 ^ (w1 + a1) - 3 ^ w1) * q0 = 2 ^ a1 - 1)
    (h52835_a1 : 52835 ∣ a1) (h1021_w1 : 1021 ∣ w1) :
    w1 ≥ 88827 ∧ a1 ≥ 52835 ∧ w1 + a1 ≥ 141662 := by
  have h5a1_lt := one_block_five_a_lt_three_w w1 a1 q0 hw1 ha1 hgt hbrox
  clear hgt hbrox
  rcases h52835_a1 with ⟨ka, rfl⟩
  rcases h1021_w1 with ⟨kw, rfl⟩
  have ha_ge : 52835 ≤ 52835 * ka := by
    cases ka with
    | zero => rw [Nat.mul_zero] at ha1; omega
    | succ ka' =>
      have hm := Nat.mul_le_mul_left 52835 (by omega : 1 ≤ ka' + 1)
      rwa [Nat.mul_one] at hm
  have hkw_gt86 : ¬ (kw ≤ 86) := by
    intro hle86
    have hm1 : 3 * (1021 * kw) + 5 ≤ 3 * (1021 * 86) + 5 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left 1021 hle86)) 5
    have hm2 : 3 * (1021 * 86) + 5 ≤ 5 * 52835 := by decide
    have hm3 : 5 * 52835 ≤ 5 * (52835 * ka) := Nat.mul_le_mul_left 5 ha_ge
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h5a1_lt (Nat.le_trans hm1 (Nat.le_trans hm2 hm3)))
  have hkw_ge87 : 87 ≤ kw := by clear h5a1_lt ha_ge ha1 hw1; omega
  have hw_ge : 88827 ≤ 1021 * kw := by
    rw [show (88827 : Nat) = 1021 * 87 by decide]
    exact Nat.mul_le_mul_left 1021 hkw_ge87
  have hsum_ge : 141662 ≤ 1021 * kw + 52835 * ka := by
    rw [show (141662 : Nat) = 88827 + 52835 by decide]
    exact Nat.add_le_add hw_ge ha_ge
  exact ⟨hw_ge, ha_ge, hsum_ge⟩

private theorem solo_p3_arith_floor (w1 a1 q0 : Nat)
    (hw1 : w1 ≥ 2) (ha1 : a1 ≥ 1) (hgt : 3 ^ w1 < 2 ^ (w1 + a1))
    (hbrox : (2 ^ (w1 + a1) - 3 ^ w1) * q0 = 2 ^ a1 - 1)
    (h12381_a1 : 12381 ∣ a1) (h1844_w1 : 1844 ∣ w1) :
    w1 ≥ 22128 ∧ a1 ≥ 12381 ∧ w1 + a1 ≥ 34509 := by
  have h5a1_lt := one_block_five_a_lt_three_w w1 a1 q0 hw1 ha1 hgt hbrox
  clear hgt hbrox
  rcases h12381_a1 with ⟨ka, rfl⟩
  rcases h1844_w1 with ⟨kw, rfl⟩
  have ha_ge : 12381 ≤ 12381 * ka := by
    cases ka with
    | zero => rw [Nat.mul_zero] at ha1; omega
    | succ ka' =>
      have hm := Nat.mul_le_mul_left 12381 (by omega : 1 ≤ ka' + 1)
      rwa [Nat.mul_one] at hm
  have hkw_gt11 : ¬ (kw ≤ 11) := by
    intro hle11
    have hm1 : 3 * (1844 * kw) + 5 ≤ 3 * (1844 * 11) + 5 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left 1844 hle11)) 5
    have hm2 : 3 * (1844 * 11) + 5 ≤ 5 * 12381 := by decide
    have hm3 : 5 * 12381 ≤ 5 * (12381 * ka) := Nat.mul_le_mul_left 5 ha_ge
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h5a1_lt (Nat.le_trans hm1 (Nat.le_trans hm2 hm3)))
  have hkw_ge12 : 12 ≤ kw := by clear h5a1_lt ha_ge ha1 hw1; omega
  have hw_ge : 22128 ≤ 1844 * kw := by
    rw [show (22128 : Nat) = 1844 * 12 by decide]
    exact Nat.mul_le_mul_left 1844 hkw_ge12
  have hsum_ge : 34509 ≤ 1844 * kw + 12381 * ka := by
    rw [show (34509 : Nat) = 22128 + 12381 by decide]
    exact Nat.add_le_add hw_ge ha_ge
  exact ⟨hw_ge, ha_ge, hsum_ge⟩

/--
  Theorem W9.2d (`p3_and_p4_cyclotomic_companion_quotient_forcing`, choice-free `zero custom axioms`):
  Standalone Cyclotomic Companion-Prime Quotient Forcing & Solo Weight Floors for
  `p_4 = 107,889,071` (`% 8 = 7`) and `p_3 = 45,661,129` (`% 8 = 1`):
  On ANY 1-block positive cycle (`w1 ≥ 2, a1 ≥ 1, 3 ^ w1 < 2 ^ (w1 + a1), D * q0 = 2 ^ a1 - 1`):
  1. Companion primes `{5, 7, 13, 31}` are ALL unconditionally excluded from dividing `D`;
  2. If `107889071 ∣ D` (even WITHOUT `331 ∣ D`!):
     `52835 ∣ a1`, `1021 ∣ w1`, **`31 ∣ q0`** (since `5 ∣ 52835 => 31 = 2^5 - 1 ∣ D * q0` and `¬ (31 ∣ D)`),
     **`w1 ≥ 88827`** (`87 * 1021`), **`a1 ≥ 52835`**, and **`w1 + a1 ≥ 141662`**!
  3. If `45661129 ∣ D`:
     `12381 ∣ a1`, `1844 ∣ w1`, **`7 ∣ q0`** (`3 ∣ 12381 => 7 = 2^3 - 1 ∣ D * q0`),
     **`65 ∣ (2 ^ w1 * q0 - 1)`** (`4 ∣ 1844 => 65 = 5 * 13 = 3^4 - 2^4 ∣ D * x0`),
     **`w1 ≥ 22128`** (`12 * 1844`), **`a1 ≥ 12381`**, and **`w1 + a1 ≥ 34509`**!
-/
theorem p3_and_p4_cyclotomic_companion_quotient_forcing
    (w1 a1 q0 : Nat)
    (hw1 : w1 ≥ 2) (ha1 : a1 ≥ 1) (hgt : 3 ^ w1 < 2 ^ (w1 + a1))
    (hbrox : (2 ^ (w1 + a1) - 3 ^ w1) * q0 = 2 ^ a1 - 1) :
    let D := 2 ^ (w1 + a1) - 3 ^ w1
    (¬ (5 ∣ D) ∧ ¬ (7 ∣ D) ∧ ¬ (13 ∣ D) ∧ ¬ (31 ∣ D)) ∧
    (107889071 ∣ D ->
      52835 ∣ a1 ∧
      1021 ∣ w1 ∧
      31 ∣ q0 ∧
      w1 ≥ 88827 ∧
      a1 ≥ 52835 ∧
      w1 + a1 ≥ 141662) ∧
    (45661129 ∣ D ->
      12381 ∣ a1 ∧
      1844 ∣ w1 ∧
      7 ∣ q0 ∧
      65 ∣ (2 ^ w1 * q0 - 1) ∧
      w1 ≥ 22128 ∧
      a1 ≥ 12381 ∧
      w1 + a1 ≥ 34509) := by
  dsimp only
  let D := 2 ^ (w1 + a1) - 3 ^ w1
  rcases p3_p4_companion_arith_cert with
    ⟨hc5_2, hc5_32, hc13_2, hc13_32, hp5, hp7, hp13, hp31,
     hg5_13, hmul5_13, hm2_5, hf52835, hm2_3, hf12381, hd32_4, hf1844⟩
  rcases (one_block_331_companion_forcing_and_mod8_obstruction w1 a1 q0 hw1 ha1 hgt hbrox).1 with
    ⟨_, hnd7, _, _, hnd31, _⟩
  have hnd5 : ¬ (5 ∣ D) :=
    one_block_common_order_prime_exclusion w1 a1 q0 5 4 2 hw1 ha1 hgt hbrox
      (by decide) (by decide) (checkExactMultOrderBool_sound _ _ _ hc5_2)
      (checkExactMultOrderBool_sound _ _ _ hc5_32) (by decide)
  have hnd13 : ¬ (13 ∣ D) :=
    one_block_common_order_prime_exclusion w1 a1 q0 13 12 4 hw1 ha1 hgt hbrox
      (by decide) (by decide) (checkExactMultOrderBool_sound _ _ _ hc13_2)
      (checkExactMultOrderBool_sound _ _ _ hc13_32) (by decide)
  refine ⟨⟨hnd5, hnd7, hnd13, hnd31⟩, ?_, ?_⟩
  · intro hp4_D
    rcases p4_107889071_order_dvd_one_block w1 a1 q0 hw1 ha1 hgt hbrox hp4_D with
      ⟨h52835_a1, h1021_w1⟩
    have h5_a1 : 5 ∣ a1 := Nat.dvd_trans ⟨10567, hf52835⟩ h52835_a1
    rcases h5_a1 with ⟨m5, hm5⟩
    have h31_Dq0 : 31 ∣ (D * q0) := by
      change 31 ∣ (2 ^ (w1 + a1) - 3 ^ w1) * q0
      rw [hbrox, hm5]
      have hm := pow_sub_pow_mul_dvd_w8 2 1 5 (by decide) m5
      simp only [Nat.one_pow, hm2_5] at hm
      exact hm
    have h31_q0 : 31 ∣ q0 := by
      rcases gauss_euclid_lemma 31 D q0 (checkSmallPrimeBool_sound 31 hp31) h31_Dq0 with hD | hq
      · exact False.elim (hnd31 hD)
      · exact hq
    rcases solo_p4_arith_floor w1 a1 q0 hw1 ha1 hgt hbrox h52835_a1 h1021_w1 with
      ⟨hw_ge, ha_ge, hsum_ge⟩
    exact ⟨h52835_a1, h1021_w1, h31_q0, hw_ge, ha_ge, hsum_ge⟩
  · intro hp3_D
    rcases p3_45661129_order_dvd_one_block w1 a1 q0 hw1 ha1 hgt hbrox hp3_D with
      ⟨hDx0, h12381_a1, h1844_w1⟩
    have h3_a1 : 3 ∣ a1 := Nat.dvd_trans ⟨4127, hf12381⟩ h12381_a1
    rcases h3_a1 with ⟨m3, hm3⟩
    have h7_Dq0 : 7 ∣ (D * q0) := by
      change 7 ∣ (2 ^ (w1 + a1) - 3 ^ w1) * q0
      rw [hbrox, hm3]
      have hm := pow_sub_pow_mul_dvd_w8 2 1 3 (by decide) m3
      simp only [Nat.one_pow, hm2_3] at hm
      exact hm
    have h7_q0 : 7 ∣ q0 := by
      rcases gauss_euclid_lemma 7 D q0 (checkSmallPrimeBool_sound 7 hp7) h7_Dq0 with hD | hq
      · exact False.elim (hnd7 hD)
      · exact hq
    have h4_w1 : 4 ∣ w1 := Nat.dvd_trans ⟨461, hf1844⟩ h1844_w1
    rcases h4_w1 with ⟨m4, hm4⟩
    let x0 := 2 ^ w1 * q0 - 1
    have h65_Dx0 : 65 ∣ (D * x0) := by
      change 65 ∣ (2 ^ (w1 + a1) - 3 ^ w1) * x0
      rw [hDx0, hm4]
      have hm := pow_sub_pow_mul_dvd_w8 3 2 4 (by decide) m4
      rwa [hd32_4] at hm
    have h5_Dx0 : 5 ∣ (D * x0) := Nat.dvd_trans ⟨13, hmul5_13.symm⟩ h65_Dx0
    have h13_Dx0 : 13 ∣ (D * x0) :=
      Nat.dvd_trans ⟨5, by rw [Nat.mul_comm, hmul5_13]⟩ h65_Dx0
    have h5_x0 : 5 ∣ x0 := by
      rcases gauss_euclid_lemma 5 D x0 (checkSmallPrimeBool_sound 5 hp5) h5_Dx0 with hD | hx
      · exact False.elim (hnd5 hD)
      · exact hx
    have h13_x0 : 13 ∣ x0 := by
      rcases gauss_euclid_lemma 13 D x0 (checkSmallPrimeBool_sound 13 hp13) h13_Dx0 with hD | hx
      · exact False.elim (hnd13 hD)
      · exact hx
    have h65_x0 : 65 ∣ x0 := by
      have hm := lcm_coprime_dvd 5 13 x0 hg5_13 h5_x0 h13_x0
      rwa [hmul5_13] at hm
    rcases solo_p3_arith_floor w1 a1 q0 hw1 ha1 hgt hbrox h12381_a1 h1844_w1 with
      ⟨hw_ge, ha_ge, hsum_ge⟩
    exact ⟨h12381_a1, h1844_w1, h7_q0, h65_x0, hw_ge, ha_ge, hsum_ge⟩

-- ============================================================================
-- SECTION 3: Front C (Branches P1.2 & P5) — Universal `∀ Q ≥ 1` Stateful
--            LSB/MSB Finite-State Automaton Preimage Impossibility Theorem &
--            6th Solvable Mixed-(2, 3) Cousin `T_diamond6` (`ω^4` Convergence)
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Section 3A: Finite Unary Periodicity (`Q!`) & LSB/MSB `Q`-State Automata (`P1.2`)
-- ----------------------------------------------------------------------------

/-- Pure-`Nat` factorial `Q!`. -/
def natFact : Nat -> Nat
  | 0 => 1
  | n + 1 => (n + 1) * natFact n

theorem natFact_pos : ∀ n : Nat, natFact n ≥ 1
  | 0 => Nat.le_refl 1
  | n + 1 => by
    simp only [natFact]
    simpa using Nat.mul_le_mul (by omega : 1 ≤ n + 1) (natFact_pos n)

theorem dvd_natFact :
    ∀ (k n : Nat), 1 ≤ k -> k ≤ n -> k ∣ natFact n
  | _, 0, hk1, hk0 => by omega
  | k, n + 1, hk1, hkn => by
    simp only [natFact]
    by_cases heq : k = n + 1
    · subst heq
      exact ⟨natFact n, rfl⟩
    · exact Nat.dvd_trans (dvd_natFact k n hk1 (by omega))
        ⟨n + 1, Nat.mul_comm (n + 1) (natFact n)⟩

/-- Iterate a unary transition map `g : Fin Q -> Fin Q` `k` times. -/
def iterFin {Q : Nat} (g : Fin Q -> Fin Q) : Nat -> Fin Q -> Fin Q
  | 0, q => q
  | k + 1, q => g (iterFin g k q)

theorem iterFin_add {Q : Nat} (g : Fin Q -> Fin Q) :
    ∀ (a b : Nat) (q : Fin Q),
      iterFin g (a + b) q = iterFin g a (iterFin g b q)
  | 0, _, _ => by simp [iterFin]
  | a + 1, b, q => by
    rw [Nat.succ_add]
    simp only [iterFin, iterFin_add g a b q]

/--
  Choice-free finite unary periodicity lemma (`zero custom axioms`):
  For ANY `Q ≥ 1`, ANY `g : Fin Q -> Fin Q`, and ANY `q : Fin Q`, the tail above `Q`
  is periodic with universal period `natFact Q` (`∀ k ≥ Q, ∀ m : Nat`,
  `iterFin g (k + natFact Q * m) q = iterFin g k q`).
-/
theorem fin_unary_iter_factorial_period {Q : Nat} (_hQ : Q ≥ 1)
    (g : Fin Q -> Fin Q) (q : Fin Q) :
    ∀ (m k : Nat), k ≥ Q ->
      iterFin g (k + natFact Q * m) q = iterFin g k q := by
  rcases nat_func_pigeonhole Q (Q + 1) (fun t => (iterFin g t q).val)
    (fun t _ => (iterFin g t q).isLt) (by omega) with ⟨i, j, hij, hj_lt, hv_eq⟩
  have hij_eq : iterFin g i q = iterFin g j q := Fin.ext hv_eq
  let p := j - i
  have hp1 : 1 ≤ p := by dsimp [p]; omega
  have hpQ : p ≤ Q := by dsimp [p]; omega
  have hp_step : ∀ k : Nat, k ≥ i -> iterFin g (k + p) q = iterFin g k q := by
    intro k hki
    have hk_sp : k + p = (k - i) + j := by dsimp [p]; omega
    have hk0_sp : k = (k - i) + i := by omega
    rw [hk_sp, iterFin_add g (k - i) j q, ← hij_eq, ← iterFin_add g (k - i) i q, ← hk0_sp]
  have hp_mul : ∀ (c k : Nat), k ≥ i -> iterFin g (k + p * c) q = iterFin g k q := by
    intro c
    induction c with
    | zero => intro k _; simp
    | succ c' ih =>
      intro k hki
      rw [Nat.mul_succ p c', ← Nat.add_assoc k (p * c') p,
          hp_step (k + p * c') (by omega), ih k hki]
  rcases dvd_natFact p Q hp1 hpQ with ⟨u, hu⟩
  intro m k hkQ
  rw [hu, Nat.mul_assoc p u m]
  exact hp_mul (u * m) k (by omega)

/-- Fuel-bounded LSB-to-MSB binary finite-state automaton runner. -/
def runLSBAutomatonAux {Q : Nat} (delta : Fin Q -> Bool -> Fin Q) :
    Nat -> Fin Q -> Nat -> Fin Q
  | 0, q, _ => q
  | fuel + 1, q, n =>
    if n = 0 then q
    else runLSBAutomatonAux delta fuel (delta q (n % 2 == 1)) (n / 2)

def runLSBFrom {Q : Nat} (delta : Fin Q -> Bool -> Fin Q) (q : Fin Q) (n : Nat) : Fin Q :=
  runLSBAutomatonAux delta n q n

/--
  Run a deterministic `Q`-state finite automaton LSB-to-MSB across the unpadded binary
  expansion of `n` (`n = 0` reads empty word `[]`, returning `q0`).
-/
def runLSBAutomaton (Q : Nat) (delta : Fin Q -> Bool -> Fin Q) (q0 : Fin Q) (n : Nat) : Fin Q :=
  runLSBFrom delta q0 n

/-- Fuel-bounded MSB-to-LSB binary finite-state automaton runner (zero list allocation). -/
def runMSBAutomatonAux {Q : Nat} (delta : Fin Q -> Bool -> Fin Q) (q0 : Fin Q) :
    Nat -> Nat -> Fin Q
  | 0, _ => q0
  | fuel + 1, n =>
    if n = 0 then q0
    else delta (runMSBAutomatonAux delta q0 fuel (n / 2)) (n % 2 == 1)

/--
  Run a deterministic `Q`-state finite automaton MSB-to-LSB across the unpadded binary
  expansion of `n` (`n = 0` reads empty word `[]`, returning `q0`).
-/
def runMSBAutomaton (Q : Nat) (delta : Fin Q -> Bool -> Fin Q) (q0 : Fin Q) (n : Nat) : Fin Q :=
  runMSBAutomatonAux delta q0 n n

theorem runLSBAutomatonAux_eq_of_ge {Q : Nat} (delta : Fin Q -> Bool -> Fin Q) :
    ∀ (f1 f2 : Nat) (q : Fin Q) (n : Nat),
      n ≤ f1 -> n ≤ f2 ->
      runLSBAutomatonAux delta f1 q n = runLSBAutomatonAux delta f2 q n
  | 0, 0, _, _, _, _ => rfl
  | 0, _ + 1, q, n, h1, _ => by rw [show n = 0 by omega]; simp [runLSBAutomatonAux]
  | _ + 1, 0, q, n, _, h2 => by rw [show n = 0 by omega]; simp [runLSBAutomatonAux]
  | f1 + 1, f2 + 1, q, n, h1, h2 => by
    simp only [runLSBAutomatonAux]
    by_cases hn0 : n = 0
    · simp [hn0]
    · simp only [hn0, ite_false]
      exact runLSBAutomatonAux_eq_of_ge delta f1 f2
        (delta q (n % 2 == 1)) (n / 2) (by omega) (by omega)

theorem runMSBAutomatonAux_eq_of_ge {Q : Nat} (delta : Fin Q -> Bool -> Fin Q) (q0 : Fin Q) :
    ∀ (f1 f2 n : Nat),
      n ≤ f1 -> n ≤ f2 ->
      runMSBAutomatonAux delta q0 f1 n = runMSBAutomatonAux delta q0 f2 n
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, n, h1, _ => by rw [show n = 0 by omega]; simp [runMSBAutomatonAux]
  | _ + 1, 0, n, _, h2 => by rw [show n = 0 by omega]; simp [runMSBAutomatonAux]
  | f1 + 1, f2 + 1, n, h1, h2 => by
    simp only [runMSBAutomatonAux]
    by_cases hn0 : n = 0
    · simp [hn0]
    · simp only [hn0, ite_false]
      rw [runMSBAutomatonAux_eq_of_ge delta q0 f1 f2 (n / 2) (by omega) (by omega)]

theorem runLSBFrom_step_pos {Q : Nat} (delta : Fin Q -> Bool -> Fin Q)
    (q : Fin Q) (n : Nat) (hn : n ≥ 1) :
    runLSBFrom delta q n = runLSBFrom delta (delta q (n % 2 == 1)) (n / 2) := by
  unfold runLSBFrom
  cases n with
  | zero => omega
  | succ m =>
    simp only [runLSBAutomatonAux, Nat.succ_ne_zero, ite_false]
    exact runLSBAutomatonAux_eq_of_ge delta m ((m + 1) / 2) _ ((m + 1) / 2)
      (by omega) (Nat.le_refl _)

theorem runMSBAutomaton_step_pos {Q : Nat} (delta : Fin Q -> Bool -> Fin Q)
    (q0 : Fin Q) (n : Nat) (hn : n ≥ 1) :
    runMSBAutomaton Q delta q0 n =
      delta (runMSBAutomaton Q delta q0 (n / 2)) (n % 2 == 1) := by
  unfold runMSBAutomaton
  cases n with
  | zero => omega
  | succ m =>
    simp only [runMSBAutomatonAux, Nat.succ_ne_zero, ite_false]
    rw [runMSBAutomatonAux_eq_of_ge delta q0 m ((m + 1) / 2) ((m + 1) / 2)
      (by omega) (Nat.le_refl _)]

theorem runLSBFrom_mul_pow2 {Q : Nat} (delta : Fin Q -> Bool -> Fin Q)
    (H : Nat) (hH : H ≥ 1) :
    ∀ (d : Nat) (q : Fin Q),
      runLSBFrom delta q (2 ^ d * H) =
        runLSBFrom delta (iterFin (fun s => delta s false) d q) H
  | 0, q => by simp [iterFin]
  | d + 1, q => by
    have hmul : 2 ^ (d + 1) * H = 2 * (2 ^ d * H) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ d) 2, Nat.mul_assoc]
    have hpos : 2 ^ d * H ≥ 1 := Nat.mul_le_mul (pow2_pos_nat d) hH
    have hm2 : ((2 * (2 ^ d * H)) % 2 == 1) = false := by
      rw [Nat.mul_mod_right]; rfl
    rw [hmul, runLSBFrom_step_pos delta q _ (by omega), hm2,
        show (2 * (2 ^ d * H)) / 2 = 2 ^ d * H by omega,
        runLSBFrom_mul_pow2 delta H hH d (delta q false)]
    have hit : iterFin (fun s => delta s false) d (delta q false) =
        iterFin (fun s => delta s false) (d + 1) q :=
      (iterFin_add (fun s => delta s false) d 1 q).symm
    rw [hit]

theorem runMSBAutomaton_mul_pow2 {Q : Nat} (delta : Fin Q -> Bool -> Fin Q)
    (q0 : Fin Q) (H : Nat) (hH : H ≥ 1) :
    ∀ d : Nat,
      runMSBAutomaton Q delta q0 (2 ^ d * H) =
        iterFin (fun s => delta s false) d (runMSBAutomaton Q delta q0 H)
  | 0 => by simp [iterFin]
  | d + 1 => by
    have hmul : 2 ^ (d + 1) * H = 2 * (2 ^ d * H) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ d) 2, Nat.mul_assoc]
    have hpos : 2 ^ d * H ≥ 1 := Nat.mul_le_mul (pow2_pos_nat d) hH
    have hm2 : ((2 * (2 ^ d * H)) % 2 == 1) = false := by
      rw [Nat.mul_mod_right]; rfl
    rw [hmul, runMSBAutomaton_step_pos delta q0 _ (by omega), hm2,
        show (2 * (2 ^ d * H)) / 2 = 2 ^ d * H by omega,
        runMSBAutomaton_mul_pow2 delta q0 H hH d]
    rfl

theorem both_automata_low_pad_peel {Q : Nat} (hQ : Q ≥ 1)
    (delta : Fin Q -> Bool -> Fin Q) (q0 : Fin Q)
    (H k m : Nat) (hH : H ≥ 1) (hk : k ≥ Q) :
    ∀ (r R : Nat) (q : Fin Q),
      R < 2 ^ r ->
      let Nm := 2 ^ (k + natFact Q * m) * H
      let N0 := 2 ^ k * H
      runLSBFrom delta q (2 ^ r * Nm + R) = runLSBFrom delta q (2 ^ r * N0 + R) ∧
      runMSBAutomaton Q delta q0 (2 ^ r * Nm + R) =
        runMSBAutomaton Q delta q0 (2 ^ r * N0 + R)
  | 0, R, q, hR => by
    have hR0 : R = 0 := by simp at hR; exact hR
    subst hR0
    dsimp only
    simp only [Nat.pow_zero, Nat.one_mul, Nat.add_zero]
    rw [runLSBFrom_mul_pow2 delta H hH (k + natFact Q * m) q,
        runLSBFrom_mul_pow2 delta H hH k q,
        runMSBAutomaton_mul_pow2 delta q0 H hH (k + natFact Q * m),
        runMSBAutomaton_mul_pow2 delta q0 H hH k,
        fin_unary_iter_factorial_period hQ (fun s => delta s false) q m k hk,
        fin_unary_iter_factorial_period hQ (fun s => delta s false)
          (runMSBAutomaton Q delta q0 H) m k hk]
    exact ⟨rfl, rfl⟩
  | r + 1, R, q, hR => by
    dsimp only
    let Nm := 2 ^ (k + natFact Q * m) * H
    let N0 := 2 ^ k * H
    have hNm_pos : Nm ≥ 1 := Nat.mul_le_mul (pow2_pos_nat _) hH
    have hN0_pos : N0 ≥ 1 := Nat.mul_le_mul (pow2_pos_nat _) hH
    have hrNm_pos : 2 ^ r * Nm ≥ 1 := Nat.mul_le_mul (pow2_pos_nat r) hNm_pos
    have hrN0_pos : 2 ^ r * N0 ≥ 1 := Nat.mul_le_mul (pow2_pos_nat r) hN0_pos
    have hR2 : R / 2 < 2 ^ r := by rw [Nat.pow_succ] at hR; omega
    have hsp_m : 2 ^ (r + 1) * Nm + R = 2 * (2 ^ r * Nm) + R := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ r) 2, Nat.mul_assoc]
    have hsp_0 : 2 ^ (r + 1) * N0 + R = 2 * (2 ^ r * N0) + R := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ r) 2, Nat.mul_assoc]
    have hbit_m : ((2 * (2 ^ r * Nm) + R) % 2 == 1) = (R % 2 == 1) := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left]
    have hbit_0 : ((2 * (2 ^ r * N0) + R) % 2 == 1) = (R % 2 == 1) := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left]
    have hdiv_m : (2 * (2 ^ r * Nm) + R) / 2 = 2 ^ r * Nm + R / 2 := by omega
    have hdiv_0 : (2 * (2 ^ r * N0) + R) / 2 = 2 ^ r * N0 + R / 2 := by omega
    rcases both_automata_low_pad_peel hQ delta q0 H k m hH hk r (R / 2)
      (delta q (R % 2 == 1)) hR2 with ⟨ih_lsb, ih_msb⟩
    change runLSBFrom delta _ (2 ^ r * Nm + R / 2) = runLSBFrom delta _ (2 ^ r * N0 + R / 2) at ih_lsb
    change runMSBAutomaton Q delta q0 (2 ^ r * Nm + R / 2) =
      runMSBAutomaton Q delta q0 (2 ^ r * N0 + R / 2) at ih_msb
    refine ⟨?_, ?_⟩
    · rw [hsp_m, hsp_0,
          runLSBFrom_step_pos delta q (2 * (2 ^ r * Nm) + R) (by omega),
          runLSBFrom_step_pos delta q (2 * (2 ^ r * N0) + R) (by omega),
          hbit_m, hbit_0, hdiv_m, hdiv_0]
      exact ih_lsb
    · rw [hsp_m, hsp_0,
          runMSBAutomaton_step_pos delta q0 (2 * (2 ^ r * Nm) + R) (by omega),
          runMSBAutomaton_step_pos delta q0 (2 * (2 ^ r * N0) + R) (by omega),
          hbit_m, hbit_0, hdiv_m, hdiv_0, ih_msb]

/-- Exact count of `0`-bits in the unpadded binary expansion of `n` (`0` at `n = 0`). -/
def zeroBitCount (n : Nat) : Nat :=
  zeroWindowCount 1 n

theorem zeroBitCount_and_len_mul_pow2 (m : Nat) (hm : m ≥ 1) :
    ∀ d : Nat,
      zeroBitCount (2 ^ d * m) = d + zeroBitCount m ∧
      binBitLength (2 ^ d * m) = d + binBitLength m
  | 0 => by simp [zeroBitCount]
  | d + 1 => by
    rcases zeroBitCount_and_len_mul_pow2 m hm d with ⟨ih_z, ih_l⟩
    have hmul : 2 ^ (d + 1) * m = 2 * (2 ^ d * m) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ d) 2, Nat.mul_assoc]
    have hpos : 2 ^ d * m ≥ 1 := Nat.mul_le_mul (pow2_pos_nat d) hm
    have hs_z := (window_step_pos 1 (2 * (2 ^ d * m)) (by omega)).2
    have hm0 : (2 * (2 ^ d * m)) % (2 ^ 1) = 0 := by
      rw [Nat.pow_one, Nat.mul_mod_right]
    rw [hm0, show (2 * (2 ^ d * m)) / 2 = 2 ^ d * m by omega] at hs_z
    simp only [ite_true] at hs_z
    have hs_l : binBitLength (2 * (2 ^ d * m)) = 1 + binBitLength (2 ^ d * m) := by
      rw [binBitLength_step_pos (2 * (2 ^ d * m)) (by omega),
          show (2 * (2 ^ d * m)) / 2 = 2 ^ d * m by omega]
    unfold zeroBitCount at ih_z ⊢
    rw [hmul, hs_z, hs_l, ih_z, ih_l]
    exact ⟨by omega, by omega⟩

theorem preimage_multistep_even_branch_ineq
    (wNum wDen : Nat -> Nat) (pTheta qTheta m d : Nat)
    (hw : IsPositiveRationalPreimageWeight wNum wDen pTheta qTheta)
    (hm : m ≥ 3) (hm3 : m % 3 = 2) (hd : d ≥ 1) :
    let ev := 2 ^ d * m
    let nOdd := (2 * m - 1) / 3
    (wNum ev * wDen nOdd + wNum nOdd * wDen ev) * wDen m ≤
      wNum m * (wDen ev * wDen nOdd) := by
  dsimp only
  have hdouble_le : ∀ x : Nat, x ≥ 3 -> wNum (2 * x) * wDen x ≤ wNum x * wDen (2 * x) := by
    intro x hx
    have hs := preimage_rational_forward_step_laws wNum wDen pTheta qTheta (2 * x) hw
      (by omega) (by rw [collatzStep_double_pos x]; omega)
    simpa [collatzStep_double_pos x] using hs.2.1
  have hpow2_le : ∀ k : Nat,
      wNum (2 ^ (k + 1) * m) * wDen (2 * m) ≤ wNum (2 * m) * wDen (2 ^ (k + 1) * m) := by
    intro k
    induction k with
    | zero => rw [Nat.pow_one]; exact Nat.le_refl _
    | succ k' ih =>
      have hpos_k : 2 ^ (k' + 1) * m ≥ 3 := by
        have hm1 := Nat.mul_le_mul (pow2_pos_nat (k' + 1)) hm; omega
      have hmul : 2 ^ (k' + 2) * m = 2 * (2 ^ (k' + 1) * m) := by
        rw [Nat.pow_succ 2 (k' + 1), Nat.mul_comm (2 ^ (k' + 1)) 2, Nat.mul_assoc]
      rw [hmul]
      exact rat_le_trans_pos_w5 _ _ (wNum (2 ^ (k' + 1) * m)) (wDen (2 ^ (k' + 1) * m)) _ _
        (hw.2.2.1 (2 ^ (k' + 1) * m) hpos_k).2
        (hdouble_le (2 ^ (k' + 1) * m) hpos_k) ih
  have hev_le_2m : wNum (2 ^ d * m) * wDen (2 * m) ≤ wNum (2 * m) * wDen (2 ^ d * m) := by
    have hd_sp : d = (d - 1) + 1 := by omega
    rw [hd_sp]; exact hpow2_le (d - 1)
  have hpre := hw.2.2.2.2 m hm hm3
  dsimp only at hpre
  have hcanc := nat_mul_le_cancel_left_w5 qTheta _ _
    (Nat.lt_of_lt_of_le hw.1 hw.2.1)
    (Nat.le_trans hpre (Nat.mul_le_mul_right _ hw.2.1))
  let ae := wNum (2 ^ d * m)
  let be := wDen (2 ^ d * m)
  let a2 := wNum (2 * m)
  let b2 := wDen (2 * m)
  let an := wNum ((2 * m - 1) / 3)
  let bn := wDen ((2 * m - 1) / 3)
  let am := wNum m
  let bm := wDen m
  have hb2_pos : b2 > 0 := (hw.2.2.1 (2 * m) (by omega)).2
  apply nat_mul_le_cancel_right_w5 b2 _ _ hb2_pos
  change ((ae * bn + an * be) * bm) * b2 ≤ (am * (be * bn)) * b2
  have hlhs_le : ((ae * bn + an * be) * bm) * b2 ≤ ((a2 * bn + an * b2) * bm) * be := by
    have hinner : (ae * bn + an * be) * b2 ≤ (a2 * bn + an * b2) * be := by
      rw [Nat.add_mul, Nat.add_mul]
      have ht1 : (ae * bn) * b2 ≤ (a2 * bn) * be := by
        have h1 : (ae * bn) * b2 = (ae * b2) * bn := by
          rw [Nat.mul_assoc, Nat.mul_comm bn b2, ← Nat.mul_assoc]
        have h2 : (a2 * bn) * be = (a2 * be) * bn := by
          rw [Nat.mul_assoc, Nat.mul_comm bn be, ← Nat.mul_assoc]
        rw [h1, h2]
        exact Nat.mul_le_mul_right bn hev_le_2m
      have ht2 : (an * be) * b2 = (an * b2) * be := by
        rw [Nat.mul_assoc, Nat.mul_comm be b2, ← Nat.mul_assoc]
      rw [ht2]
      exact Nat.add_le_add_right ht1 ((an * b2) * be)
    have hr1 : ((ae * bn + an * be) * bm) * b2 = ((ae * bn + an * be) * b2) * bm := by
      rw [Nat.mul_assoc, Nat.mul_comm bm b2, ← Nat.mul_assoc]
    have hr2 : ((a2 * bn + an * b2) * bm) * be = ((a2 * bn + an * b2) * be) * bm := by
      rw [Nat.mul_assoc, Nat.mul_comm bm be, ← Nat.mul_assoc]
    rw [hr1, hr2]
    exact Nat.mul_le_mul_right bm hinner
  have hrhs_eq : (am * (b2 * bn)) * be = (am * (be * bn)) * b2 := by
    calc
      (am * (b2 * bn)) * be
          = am * ((b2 * bn) * be) := Nat.mul_assoc _ _ _
      _ = am * (b2 * (bn * be)) := by rw [Nat.mul_assoc b2 bn be]
      _ = am * (b2 * (be * bn)) := by rw [Nat.mul_comm bn be]
      _ = am * ((be * bn) * b2) := by rw [Nat.mul_comm b2 (be * bn)]
      _ = (am * (be * bn)) * b2 := (Nat.mul_assoc _ _ _).symm
  rw [← hrhs_eq]
  exact Nat.le_trans hlhs_le (Nat.mul_le_mul_right be hcanc)

/--
  Theorem W9.3a (`berg_meinardus_stateful_automaton_preimage_impossibility`, choice-free `zero custom axioms`):
  Universal `∀ Q ≥ 1` Stateful LSB-First & MSB-First Finite-State Automaton Preimage Impossibility
  (Permanently Closing All Regular / Finite-Automaton Berg–Meinardus Preimage Weights in `Branch P1.2`):
  1. **Universal `Q!`-Padded Automaton Collision & Affine Growth Family (`∀ Q ≥ 1, ∀ s : Nat`)**:
     Along `ms = 3 * 4 ^ (2 * Q + natFact Q * s) + 2 ^ (2 * Q + 1)`, `evs = 2 ^ (natFact Q) * ms`,
     and `ns = (2 * ms - 1) / 3`:
     - `ms % 3 = 2`, BOTH `runLSBAutomaton Q delta q0` AND `runMSBAutomaton Q delta q0` map
       `ms` and `evs` to the **IDENTICAL** state as `m0`, and map `ns` to the **IDENTICAL** state
       as `n0` across ALL transition tables `delta` and initial states `q0`!
     - `zeroBitCount` and `binBitLength` grow with exact affine slope `2 * natFact Q * s`!
  2. **Concrete `Q = 2` Witness (`ZPOS_STATEFUL_Q2_COLLISION_800_VS_3200`)**:
     `m0 = 800`, `evs = 3200`, `n0 = 533`, and `runLSBAutomaton 2 delta q0 800 = runLSBAutomaton 2 delta q0 3200`
     AND `runMSBAutomaton 2 delta q0 800 = runMSBAutomaton 2 delta q0 3200` across ALL `2`-state automata!
  3. **Universal Stateful Barrier (`∀ Q ≥ 1`)**:
     For EVERY state count `Q ≥ 1`, ANY LSB automaton `(deltaL, q0L)`, ANY MSB automaton `(deltaM, q0M)`,
     ANY joint state-pair weights `fNum, fDen : Fin Q -> Fin Q -> Nat`, and ANY non-separable
     bivariate polynomials `pTerms, qTerms : NatPoly2` in `(zeroBitCount n, binBitLength n)`,
     NO positive rational preimage weight of the form
       `w(n) = (fNum (runLSBAutomaton Q deltaL q0L n) (runMSBAutomaton Q deltaM q0M n) *
                  evalNatPoly2 pTerms (zeroBitCount n) (binBitLength n)) /
               (fDen (runLSBAutomaton Q deltaL q0L n) (runMSBAutomaton Q deltaM q0M n) *
                  evalNatPoly2 qTerms (zeroBitCount n) (binBitLength n))`
     can satisfy `IsPositiveRationalPreimageWeight`!
-/
theorem berg_meinardus_stateful_automaton_preimage_impossibility :
    (∀ (Q s : Nat), Q ≥ 1 ->
      let P := natFact Q
      let m0 := 3 * 4 ^ (2 * Q) + 2 ^ (2 * Q + 1)
      let n0 := (2 * m0 - 1) / 3
      let ms := 3 * 4 ^ (2 * Q + P * s) + 2 ^ (2 * Q + 1)
      let evs := 2 ^ P * ms
      let ns := (2 * ms - 1) / 3
      ms % 3 = 2 ∧
      (∀ (delta : Fin Q -> Bool -> Fin Q) (q0 : Fin Q),
        runLSBAutomaton Q delta q0 ms = runLSBAutomaton Q delta q0 m0 ∧
        runLSBAutomaton Q delta q0 evs = runLSBAutomaton Q delta q0 m0 ∧
        runLSBAutomaton Q delta q0 ns = runLSBAutomaton Q delta q0 n0 ∧
        runMSBAutomaton Q delta q0 ms = runMSBAutomaton Q delta q0 m0 ∧
        runMSBAutomaton Q delta q0 evs = runMSBAutomaton Q delta q0 m0 ∧
        runMSBAutomaton Q delta q0 ns = runMSBAutomaton Q delta q0 n0) ∧
      zeroBitCount ms = 2 * P * s + zeroBitCount m0 ∧
      zeroBitCount evs = 2 * P * s + P + zeroBitCount m0 ∧
      zeroBitCount ns = 2 * P * s + zeroBitCount n0 ∧
      binBitLength ms = 2 * P * s + binBitLength m0 ∧
      binBitLength evs = 2 * P * s + P + binBitLength m0 ∧
      binBitLength ns = 2 * P * s + binBitLength n0) ∧
    (3 * 4 ^ (2 * 2) + 2 ^ (2 * 2 + 1) = 800 ∧
     2 ^ (natFact 2) * 800 = 3200 ∧
     (2 * 800 - 1) / 3 = 533 ∧
     ∀ (delta : Fin 2 -> Bool -> Fin 2) (q0 : Fin 2),
       runLSBAutomaton 2 delta q0 800 = runLSBAutomaton 2 delta q0 3200 ∧
       runMSBAutomaton 2 delta q0 800 = runMSBAutomaton 2 delta q0 3200) ∧
    (∀ (Q : Nat) (_hQ : Q ≥ 1)
       (deltaL deltaM : Fin Q -> Bool -> Fin Q)
       (q0L q0M : Fin Q)
       (fNum fDen : Fin Q -> Fin Q -> Nat)
       (pTerms qTerms : NatPoly2)
       (pTheta qTheta : Nat),
      ¬ IsPositiveRationalPreimageWeight
        (fun n =>
          fNum (runLSBAutomaton Q deltaL q0L n) (runMSBAutomaton Q deltaM q0M n) *
            evalNatPoly2 pTerms (zeroBitCount n) (binBitLength n))
        (fun n =>
          fDen (runLSBAutomaton Q deltaL q0L n) (runMSBAutomaton Q deltaM q0M n) *
            evalNatPoly2 qTerms (zeroBitCount n) (binBitLength n))
        pTheta qTheta) := by
  have hfamily : ∀ (Q s : Nat), Q ≥ 1 ->
      let P := natFact Q
      let m0 := 3 * 4 ^ (2 * Q) + 2 ^ (2 * Q + 1)
      let n0 := (2 * m0 - 1) / 3
      let ms := 3 * 4 ^ (2 * Q + P * s) + 2 ^ (2 * Q + 1)
      let evs := 2 ^ P * ms
      let ns := (2 * ms - 1) / 3
      ms % 3 = 2 ∧
      (∀ (delta : Fin Q -> Bool -> Fin Q) (q0 : Fin Q),
        runLSBAutomaton Q delta q0 ms = runLSBAutomaton Q delta q0 m0 ∧
        runLSBAutomaton Q delta q0 evs = runLSBAutomaton Q delta q0 m0 ∧
        runLSBAutomaton Q delta q0 ns = runLSBAutomaton Q delta q0 n0 ∧
        runMSBAutomaton Q delta q0 ms = runMSBAutomaton Q delta q0 m0 ∧
        runMSBAutomaton Q delta q0 evs = runMSBAutomaton Q delta q0 m0 ∧
        runMSBAutomaton Q delta q0 ns = runMSBAutomaton Q delta q0 n0) ∧
      zeroBitCount ms = 2 * P * s + zeroBitCount m0 ∧
      zeroBitCount evs = 2 * P * s + P + zeroBitCount m0 ∧
      zeroBitCount ns = 2 * P * s + zeroBitCount n0 ∧
      binBitLength ms = 2 * P * s + binBitLength m0 ∧
      binBitLength evs = 2 * P * s + P + binBitLength m0 ∧
      binBitLength ns = 2 * P * s + binBitLength n0 := by
    intro Q s hQ
    dsimp only
    let P := natFact Q
    have hfam_w := berg_meinardus_sliding_window_kgram_impossibility.1 1
      (2 * Q - 2 + P * s) (by decide)
    -- Reuse Wave 8's `W = Q` family directly for `ms % 3 = 2` and `binBitLength`:
    rcases berg_meinardus_sliding_window_kgram_impossibility.1 Q (P * s) hQ with
      ⟨hms_m3, _, _, _, _, _, _, hbl_ms_raw, _, hbl_ns_raw⟩
    let m0 := 3 * 4 ^ (2 * Q) + 2 ^ (2 * Q + 1)
    let n0 := (2 * m0 - 1) / 3
    let ms := 3 * 4 ^ (2 * Q + P * s) + 2 ^ (2 * Q + 1)
    let evs := 2 ^ P * ms
    let ns := (2 * ms - 1) / 3
    clear hfam_w
    have hms_pos : ms ≥ 1 := by
      dsimp [ms]; have hp := pow2_pos_nat (2 * Q + 1); omega
    rcases zeroBitCount_and_len_mul_pow2 ms hms_pos P with ⟨hz_evs_step, hbl_evs_step⟩
    have h2Ps : 2 * (P * s) = 2 * P * s := (Nat.mul_assoc 2 P s).symm
    -- Zero-bit counts of `ms` and `ns` via `W = 1` (`Q = 1`) or `window_low_pad_peel 1` (`Q ≥ 2`):
    have hz_ms_ns :
        zeroBitCount ms = 2 * P * s + zeroBitCount m0 ∧
        zeroBitCount ns = 2 * P * s + zeroBitCount n0 := by
      by_cases hQ1 : Q = 1
      · subst hQ1
        rcases berg_meinardus_sliding_window_kgram_impossibility.1 1 s (by decide) with
          ⟨_, _, _, _, hzm1, _, hzn1, _, _, _⟩
        have hP1 : P = 1 := rfl
        have hms1 : ms = 3 * 4 ^ (2 * 1 + s) + 2 ^ (2 * 1 + 1) := by
          dsimp [ms]; rw [hP1, Nat.one_mul]
        have hns1 : ns = (2 * (3 * 4 ^ (2 * 1 + s) + 2 ^ (2 * 1 + 1)) - 1) / 3 := by
          dsimp [ns]; rw [hms1]
        unfold zeroBitCount
        rw [hms1, hns1, hP1, Nat.mul_one]
        exact ⟨hzm1, hzn1⟩
      · have hQ2 : Q ≥ 2 := by omega
        let R_m := 2 ^ (2 * Q + 1)
        let R_n := (4 ^ (Q + 1) - 1) / 3
        have h4_m3 : 4 ^ Q % 3 = 1 := by
          have hm := (pow4_ge_four_and_mod3_w5 (Q - 1)).2
          rwa [show Q - 1 + 1 = Q by omega] at hm
        have h3Rn : 3 * R_n = 2 * R_m - 1 := by
          dsimp [R_n, R_m]
          have h4_1 : 4 ^ (Q + 1) % 3 = 1 := by rw [Nat.pow_succ, Nat.mul_mod, h4_m3]
          have h4_eq : 4 ^ (Q + 1) = 2 * 2 ^ (2 * Q + 1) := by
            rw [Nat.pow_succ 4 Q, pow4_eq_pow2_even Q, Nat.pow_succ 2 (2 * Q)]; omega
          omega
        have hns_eq : ∀ u : Nat, (2 * (3 * 4 ^ u + R_m) - 1) / 3 = 2 * 4 ^ u + R_n := by
          intro u
          have hRm_pos : R_m ≥ 1 := pow2_pos_nat (2 * Q + 1)
          generalize 4 ^ u = p4u, R_m = rm, R_n = rn at hRm_pos h3Rn ⊢
          omega
        have hRm_lt : R_m < 2 ^ (4 * Q - 1) := by
          dsimp [R_m]
          have hm := pow2_mono_nat (by omega : 2 * Q + 2 ≤ 4 * Q - 1)
          rw [show 2 * Q + 2 = (2 * Q + 1) + 1 by omega, Nat.pow_succ] at hm
          have hp := pow2_pos_nat (2 * Q + 1); omega
        have hRn_lt : R_n < 2 ^ (4 * Q - 1) := by
          have hp := pow2_pos_nat (2 * Q + 1)
          have hlt_m : R_n < R_m := by dsimp [R_m] at h3Rn ⊢; omega
          exact Nat.lt_trans hlt_m hRm_lt
        have hm_pad : ms = 2 ^ (1 + 2 * P * s + (4 * Q - 1)) * 3 + R_m := by
          dsimp [ms]
          rw [pow4_eq_pow2_even (2 * Q + P * s),
              show 2 * (2 * Q + P * s) = 1 + 2 * P * s + (4 * Q - 1) by rw [← h2Ps]; omega,
              Nat.mul_comm 3]
        have hm0_pad : m0 = 2 ^ (1 + (4 * Q - 1)) * 3 + R_m := by
          dsimp [m0]
          rw [pow4_eq_pow2_even (2 * Q), show 2 * (2 * Q) = 1 + (4 * Q - 1) by omega, Nat.mul_comm 3]
        have hn_pad : ns = 2 ^ (1 + 2 * P * s + (4 * Q - 1)) * 2 + R_n := by
          dsimp [ns, ms]
          rw [hns_eq (2 * Q + P * s), pow4_eq_pow2_even (2 * Q + P * s),
              show 2 * (2 * Q + P * s) = 1 + 2 * P * s + (4 * Q - 1) by rw [← h2Ps]; omega,
              Nat.mul_comm 2]
        have hn0_pad : n0 = 2 ^ (1 + (4 * Q - 1)) * 2 + R_n := by
          dsimp [n0, m0]
          rw [hns_eq (2 * Q), pow4_eq_pow2_even (2 * Q),
              show 2 * (2 * Q) = 1 + (4 * Q - 1) by omega, Nat.mul_comm 2]
        have hzm := (window_low_pad_peel 1 3 (2 * P * s) (by decide) (4 * Q - 1) R_m hRm_lt).2
        have hzn := (window_low_pad_peel 1 2 (2 * P * s) (by decide) (4 * Q - 1) R_n hRn_lt).2
        rw [← hm_pad, ← hm0_pad] at hzm
        rw [← hn_pad, ← hn0_pad] at hzn
        exact ⟨hzm, hzn⟩
    -- Automaton state invariance across ALL `delta` and `q0`:
    have haut : ∀ (delta : Fin Q -> Bool -> Fin Q) (q0 : Fin Q),
        runLSBAutomaton Q delta q0 ms = runLSBAutomaton Q delta q0 m0 ∧
        runLSBAutomaton Q delta q0 evs = runLSBAutomaton Q delta q0 m0 ∧
        runLSBAutomaton Q delta q0 ns = runLSBAutomaton Q delta q0 n0 ∧
        runMSBAutomaton Q delta q0 ms = runMSBAutomaton Q delta q0 m0 ∧
        runMSBAutomaton Q delta q0 evs = runMSBAutomaton Q delta q0 m0 ∧
        runMSBAutomaton Q delta q0 ns = runMSBAutomaton Q delta q0 n0 := by
      intro delta q0
      by_cases hQ1 : Q = 1
      · subst hQ1
        have hsub : ∀ a b : Fin 1, a = b := fun a b => Fin.ext (by omega)
        exact ⟨hsub _ _, hsub _ _, hsub _ _, hsub _ _, hsub _ _, hsub _ _⟩
      · have hQ2 : Q ≥ 2 := by omega
        have hP_2s : natFact Q * (2 * s) = 2 * (natFact Q * s) := by
          rw [← Nat.mul_assoc (natFact Q) 2 s, Nat.mul_comm (natFact Q) 2, Nat.mul_assoc]
        unfold runLSBAutomaton
        -- 1. `ms` vs `m0`: `r = 2 * Q + 2`, `R = 2 ^ (2 * Q + 1) < 2 ^ r`, `k = 2 * Q - 2 ≥ Q`, `m = 2 * s`, `H = 3`:
        have hR_m_lt : 2 ^ (2 * Q + 1) < 2 ^ (2 * Q + 2) := by
          rw [Nat.pow_succ 2 (2 * Q + 1)]; have hp := pow2_pos_nat (2 * Q + 1); omega
        rcases both_automata_low_pad_peel hQ delta q0 3 (2 * Q - 2) (2 * s)
          (by decide) (by omega) (2 * Q + 2) (2 ^ (2 * Q + 1)) q0 hR_m_lt with ⟨hms_l, hms_m⟩
        have hms_rew : 2 ^ (2 * Q + 2) * (2 ^ (2 * Q - 2 + natFact Q * (2 * s)) * 3) + 2 ^ (2 * Q + 1) = ms := by
          dsimp [ms, P]
          rw [← Nat.mul_assoc (2 ^ (2 * Q + 2)), ← Nat.pow_add 2 (2 * Q + 2),
              show 2 * Q + 2 + (2 * Q - 2 + natFact Q * (2 * s)) = 2 * (2 * Q + natFact Q * s) by rw [hP_2s]; omega,
              ← pow4_eq_pow2_even, Nat.mul_comm _ 3]
        have hm0_rew : 2 ^ (2 * Q + 2) * (2 ^ (2 * Q - 2) * 3) + 2 ^ (2 * Q + 1) = m0 := by
          dsimp [m0]
          rw [← Nat.mul_assoc (2 ^ (2 * Q + 2)), ← Nat.pow_add 2 (2 * Q + 2) (2 * Q - 2),
              show 2 * Q + 2 + (2 * Q - 2) = 2 * (2 * Q) by omega,
              ← pow4_eq_pow2_even, Nat.mul_comm _ 3]
        rw [hms_rew, hm0_rew] at hms_l hms_m
        -- 2. `evs` vs `ms`: `ms = 2 ^ (2 * Q + 1) * H_ms` with `k = 2 * Q + 1 ≥ Q`, `m = 1`, `r = 0, R = 0`:
        let H_ms := 3 * 2 ^ (2 * Q - 1 + 2 * P * s) + 1
        have hHms_pos : H_ms ≥ 1 := by dsimp [H_ms]; omega
        rcases both_automata_low_pad_peel hQ delta q0 H_ms (2 * Q + 1) 1
          hHms_pos (by omega) 0 0 q0 (by decide) with ⟨hevs_l, hevs_m⟩
        simp only [Nat.pow_zero, Nat.one_mul, Nat.add_zero, Nat.mul_one] at hevs_l hevs_m
        have hms_fac : 2 ^ (2 * Q + 1) * H_ms = ms := by
          dsimp [H_ms, ms]
          rw [Nat.mul_add (2 ^ (2 * Q + 1)), Nat.mul_one,
              ← Nat.mul_assoc (2 ^ (2 * Q + 1)) 3, Nat.mul_comm (2 ^ (2 * Q + 1)) 3,
              Nat.mul_assoc 3, ← Nat.pow_add 2 (2 * Q + 1),
              show 2 * Q + 1 + (2 * Q - 1 + 2 * P * s) = 2 * (2 * Q + P * s) by rw [← h2Ps]; omega,
              ← pow4_eq_pow2_even]
        have hevs_fac : 2 ^ (2 * Q + 1 + natFact Q) * H_ms = evs := by
          dsimp [evs, P]
          rw [Nat.add_comm (2 * Q + 1) (natFact Q), Nat.pow_add 2 (natFact Q) (2 * Q + 1),
              Nat.mul_assoc, hms_fac]
        rw [hevs_fac, hms_fac] at hevs_l hevs_m
        -- 3. `ns` vs `n0`: `r = 2 * Q + 1`, `R = (4 ^ (Q + 1) - 1) / 3 < 2 ^ r`, `k = 2 * Q ≥ Q`, `m = 2 * s`, `H = 1`:
        let R_n := (4 ^ (Q + 1) - 1) / 3
        have h4_m3 : 4 ^ Q % 3 = 1 := by
          have hm := (pow4_ge_four_and_mod3_w5 (Q - 1)).2
          rwa [show Q - 1 + 1 = Q by omega] at hm
        have h3Rn : 3 * R_n = 2 * 2 ^ (2 * Q + 1) - 1 := by
          dsimp [R_n]
          have h4_1 : 4 ^ (Q + 1) % 3 = 1 := by rw [Nat.pow_succ, Nat.mul_mod, h4_m3]
          have h4_eq : 4 ^ (Q + 1) = 2 * 2 ^ (2 * Q + 1) := by
            rw [Nat.pow_succ 4 Q, pow4_eq_pow2_even Q, Nat.pow_succ 2 (2 * Q)]; omega
          omega
        have hRn_lt : R_n < 2 ^ (2 * Q + 1) := by
          have hp := pow2_pos_nat (2 * Q + 1); omega
        rcases both_automata_low_pad_peel hQ delta q0 1 (2 * Q) (2 * s)
          (by decide) (by omega) (2 * Q + 1) R_n q0 hRn_lt with ⟨hns_l, hns_m⟩
        simp only [Nat.mul_one] at hns_l hns_m
        have hns_rew : 2 ^ (2 * Q + 1) * 2 ^ (2 * Q + natFact Q * (2 * s)) + R_n = ns := by
          dsimp [ns, ms, P]
          have hdiv : (2 * (3 * 4 ^ (2 * Q + natFact Q * s) + 2 ^ (2 * Q + 1)) - 1) / 3 =
              2 * 4 ^ (2 * Q + natFact Q * s) + R_n := by
            have hp2 := pow2_pos_nat (2 * Q + 1)
            generalize 4 ^ (2 * Q + natFact Q * s) = p4u, 2 ^ (2 * Q + 1) = rm, R_n = rn at hp2 h3Rn ⊢
            omega
          rw [hdiv, ← Nat.pow_add 2 (2 * Q + 1),
              show 2 * Q + 1 + (2 * Q + natFact Q * (2 * s)) = 2 * (2 * Q + natFact Q * s) + 1 by rw [hP_2s]; omega,
              Nat.pow_succ, ← pow4_eq_pow2_even, Nat.mul_comm _ 2]
        have hn0_rew : 2 ^ (2 * Q + 1) * 2 ^ (2 * Q) + R_n = n0 := by
          dsimp [n0, m0]
          have hdiv : (2 * (3 * 4 ^ (2 * Q) + 2 ^ (2 * Q + 1)) - 1) / 3 =
              2 * 4 ^ (2 * Q) + R_n := by
            have hp2 := pow2_pos_nat (2 * Q + 1)
            generalize 4 ^ (2 * Q) = p4u, 2 ^ (2 * Q + 1) = rm, R_n = rn at hp2 h3Rn ⊢
            omega
          rw [hdiv, ← Nat.pow_add 2 (2 * Q + 1) (2 * Q),
              show 2 * Q + 1 + 2 * Q = 2 * (2 * Q) + 1 by omega,
              Nat.pow_succ, ← pow4_eq_pow2_even, Nat.mul_comm _ 2]
        rw [hns_rew, hn0_rew] at hns_l hns_m
        exact ⟨hms_l, hevs_l.trans hms_l, hns_l, hms_m, hevs_m.trans hms_m, hns_m⟩
    exact ⟨hms_m3, haut, hz_ms_ns.1,
           by rw [hz_evs_step, hz_ms_ns.1]; dsimp [P, m0]; omega,
           hz_ms_ns.2,
           by rw [hbl_ms_raw, h2Ps],
           by rw [hbl_evs_step, hbl_ms_raw, h2Ps]; dsimp [P, m0]; omega,
           by rw [hbl_ns_raw, h2Ps]⟩
  refine ⟨hfamily, ?_, ?_⟩
  · -- Part 2: Concrete `Q = 2` witness (`800` vs `3200`, `533`):
    refine ⟨by decide, by decide, by decide, ?_⟩
    intro delta q0
    rcases (hfamily 2 0 (by decide)).2.1 delta q0 with ⟨_, hevs_l, _, _, hevs_m, _⟩
    exact ⟨hevs_l.symm, hevs_m.symm⟩
  · -- Part 3: Universal `∀ Q ≥ 1` stateful automaton + bivariate polynomial impossibility:
    intro Q hQ deltaL deltaM q0L q0M fNum fDen pTerms qTerms pTheta qTheta hw
    let P := natFact Q
    have hP_pos : P ≥ 1 := natFact_pos Q
    let m0 := 3 * 4 ^ (2 * Q) + 2 ^ (2 * Q + 1)
    let n0 := (2 * m0 - 1) / 3
    let aE := fNum (runLSBAutomaton Q deltaL q0L m0) (runMSBAutomaton Q deltaM q0M m0)
    let bE := fDen (runLSBAutomaton Q deltaL q0L m0) (runMSBAutomaton Q deltaM q0M m0)
    let aO := fNum (runLSBAutomaton Q deltaL q0L n0) (runMSBAutomaton Q deltaM q0M n0)
    let bO := fDen (runLSBAutomaton Q deltaL q0L n0) (runMSBAutomaton Q deltaM q0M n0)
    have hpos_fac : ∀ x y : Nat, x * y > 0 -> x ≥ 1 ∧ y ≥ 1 := by
      intro x y h
      cases x with
      | zero => simp at h
      | succ _ =>
        cases y with
        | zero => simp at h
        | succ _ => exact ⟨by omega, by omega⟩
    have hm0_ge3 : m0 ≥ 3 := by
      have h4 := nat_pow_pos_of_pos 4 (by decide) (2 * Q)
      dsimp [m0]; generalize 4 ^ (2 * Q) = p4, 2 ^ (2 * Q + 1) = p2 at h4 ⊢; omega
    have hn0_ge3 : n0 ≥ 3 := by
      have h4 : 4 ^ (2 * Q) ≥ 16 := by
        simpa using nat_pow_mono_exp_pos 4 2 (2 * Q) (by decide) (by omega)
      dsimp [n0, m0]; generalize 4 ^ (2 * Q) = p4, 2 ^ (2 * Q + 1) = p2 at h4 ⊢; omega
    rcases hw.2.2.1 m0 hm0_ge3 with ⟨hnum_m0, hden_m0⟩
    rcases hw.2.2.1 n0 hn0_ge3 with ⟨hnum_n0, hden_n0⟩
    dsimp only at hnum_m0 hden_m0 hnum_n0 hden_n0
    have haE_pos : aE ≥ 1 := (hpos_fac _ _ hnum_m0).1
    have hbE_pos : bE ≥ 1 := (hpos_fac _ _ hden_m0).1
    have haO_pos : aO ≥ 1 := (hpos_fac _ _ hnum_n0).1
    have hbO_pos : bO ≥ 1 := (hpos_fac _ _ hden_n0).1
    let dP := maxDegNatPoly2 pTerms
    let dQ := maxDegNatPoly2 qTerms
    let D := dP + dQ
    let Zm0 := zeroBitCount m0
    let Zn0 := zeroBitCount n0
    let Lm0 := binBitLength m0
    let Ln0 := binBitLength n0
    let C := Zm0 + Zn0 + Lm0 + Ln0 + P + 2
    have hC_pos : C ≥ 1 := by dsimp [C]; omega
    let A_b := aO * bE
    let B_b := aE * bO
    have hAb_pos : A_b ≥ 1 := Nat.mul_le_mul haO_pos hbE_pos
    have hBb_pos : B_b ≥ 1 := Nat.mul_le_mul haE_pos hbO_pos
    let s := (B_b + A_b + 1) * (D * C + 1) + 1
    let X := 2 * P * s
    have hX_ge : X ≥ (B_b + A_b + 1) * (D * C + 1) := by
      have hm : 2 * 1 * s ≤ 2 * P * s :=
        Nat.mul_le_mul_right s (Nat.mul_le_mul_left 2 hP_pos)
      dsimp [X, s] at hm ⊢
      omega
    rcases hfamily Q s hQ with
      ⟨hms_m3, haut, hz_ms, hz_evs, hz_ns, hbl_ms, hbl_evs, hbl_ns⟩
    rcases haut deltaL q0L with ⟨hl_ms, hl_evs, hl_ns, _, _, _⟩
    rcases haut deltaM q0M with ⟨_, _, _, hm_ms, hm_evs, hm_ns⟩
    let ms := 3 * 4 ^ (2 * Q + P * s) + 2 ^ (2 * Q + 1)
    let evs := 2 ^ P * ms
    let ns := (2 * ms - 1) / 3
    have hms_ge3 : ms ≥ 3 := by
      have h4 := nat_pow_pos_of_pos 4 (by decide) (2 * Q + P * s)
      dsimp [ms]; generalize 4 ^ (2 * Q + P * s) = p4, 2 ^ (2 * Q + 1) = p2 at h4 ⊢; omega
    have hns_ge3 : ns ≥ 3 := by
      have h4 : 4 ^ (2 * Q + P * s) ≥ 16 := by
        simpa using nat_pow_mono_exp_pos 4 2 (2 * Q + P * s) (by decide) (by omega)
      dsimp [ns, ms]; generalize 4 ^ (2 * Q + P * s) = p4, 2 ^ (2 * Q + 1) = p2 at h4 ⊢; omega
    have hevs_ge3 : evs ≥ 3 := by
      dsimp [evs]; simpa using Nat.mul_le_mul (pow2_pos_nat P) hms_ge3
    have hcanc := preimage_multistep_even_branch_ineq
      (fun n =>
        fNum (runLSBAutomaton Q deltaL q0L n) (runMSBAutomaton Q deltaM q0M n) *
          evalNatPoly2 pTerms (zeroBitCount n) (binBitLength n))
      (fun n =>
        fDen (runLSBAutomaton Q deltaL q0L n) (runMSBAutomaton Q deltaM q0M n) *
          evalNatPoly2 qTerms (zeroBitCount n) (binBitLength n))
      pTheta qTheta ms P hw hms_ge3 hms_m3 hP_pos
    dsimp only at hcanc
    change ((fNum (runLSBAutomaton Q deltaL q0L evs) (runMSBAutomaton Q deltaM q0M evs) *
              evalNatPoly2 pTerms (zeroBitCount evs) (binBitLength evs)) *
            (fDen (runLSBAutomaton Q deltaL q0L ns) (runMSBAutomaton Q deltaM q0M ns) *
              evalNatPoly2 qTerms (zeroBitCount ns) (binBitLength ns)) +
            (fNum (runLSBAutomaton Q deltaL q0L ns) (runMSBAutomaton Q deltaM q0M ns) *
              evalNatPoly2 pTerms (zeroBitCount ns) (binBitLength ns)) *
            (fDen (runLSBAutomaton Q deltaL q0L evs) (runMSBAutomaton Q deltaM q0M evs) *
              evalNatPoly2 qTerms (zeroBitCount evs) (binBitLength evs))) *
          (fDen (runLSBAutomaton Q deltaL q0L ms) (runMSBAutomaton Q deltaM q0M ms) *
            evalNatPoly2 qTerms (zeroBitCount ms) (binBitLength ms)) ≤
      (fNum (runLSBAutomaton Q deltaL q0L ms) (runMSBAutomaton Q deltaM q0M ms) *
        evalNatPoly2 pTerms (zeroBitCount ms) (binBitLength ms)) *
      ((fDen (runLSBAutomaton Q deltaL q0L evs) (runMSBAutomaton Q deltaM q0M evs) *
          evalNatPoly2 qTerms (zeroBitCount evs) (binBitLength evs)) *
        (fDen (runLSBAutomaton Q deltaL q0L ns) (runMSBAutomaton Q deltaM q0M ns) *
          evalNatPoly2 qTerms (zeroBitCount ns) (binBitLength ns))) at hcanc
    rw [hl_ms, hl_evs, hl_ns, hm_ms, hm_evs, hm_ns] at hcanc
    let P_m := evalNatPoly2 pTerms (zeroBitCount ms) (binBitLength ms)
    let Q_m := evalNatPoly2 qTerms (zeroBitCount ms) (binBitLength ms)
    let P_ev := evalNatPoly2 pTerms (zeroBitCount evs) (binBitLength evs)
    let Q_ev := evalNatPoly2 qTerms (zeroBitCount evs) (binBitLength evs)
    let P_n := evalNatPoly2 pTerms (zeroBitCount ns) (binBitLength ns)
    let Q_n := evalNatPoly2 qTerms (zeroBitCount ns) (binBitLength ns)
    change ((aE * P_ev) * (bO * Q_n) + (aO * P_n) * (bE * Q_ev)) * (bE * Q_m) ≤
      (aE * P_m) * ((bE * Q_ev) * (bO * Q_n)) at hcanc
    rcases hw.2.2.1 ms hms_ge3 with ⟨hnum_ms, _⟩
    rcases hw.2.2.1 evs hevs_ge3 with ⟨_, hden_evs⟩
    rcases hw.2.2.1 ns hns_ge3 with ⟨_, hden_ns⟩
    dsimp only at hnum_ms hden_evs hden_ns
    have hPm_pos : P_m ≥ 1 := (hpos_fac _ _ hnum_ms).2
    have hQev_pos : Q_ev ≥ 1 := (hpos_fac _ _ hden_evs).2
    have hQn_pos : Q_n ≥ 1 := (hpos_fac _ _ hden_ns).2
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
    have hb_ms : X ≤ zeroBitCount ms ∧ zeroBitCount ms ≤ X + C ∧
        X ≤ binBitLength ms ∧ binBitLength ms ≤ X + C := by
      change X ≤ zeroBitCount ms ∧ zeroBitCount ms ≤ X + C ∧
        X ≤ binBitLength ms ∧ binBitLength ms ≤ X + C
      rw [hz_ms, hbl_ms]; dsimp [X, C, Zm0, Zn0, Lm0, Ln0, m0, n0, P]
      exact ⟨by omega, by omega, by omega, by omega⟩
    have hb_evs : X ≤ zeroBitCount evs ∧ zeroBitCount evs ≤ X + C ∧
        X ≤ binBitLength evs ∧ binBitLength evs ≤ X + C := by
      rw [hz_evs, hbl_evs]; dsimp [X, C, Zm0, Zn0, Lm0, Ln0, m0, n0, P]
      exact ⟨by omega, by omega, by omega, by omega⟩
    have hb_ns : X ≤ zeroBitCount ns ∧ zeroBitCount ns ≤ X + C ∧
        X ≤ binBitLength ns ∧ binBitLength ns ≤ X + C := by
      rw [hz_ns, hbl_ns]; dsimp [X, C, Zm0, Zn0, Lm0, Ln0, m0, n0, P]
      exact ⟨by omega, by omega, by omega, by omega⟩
    have hPm_Pev : X ^ dP * P_m ≤ (X + C) ^ dP * P_ev :=
      hpoly2_sand pTerms _ _ _ _ hb_ms.1 hb_ms.2.1 hb_ms.2.2.1 hb_ms.2.2.2
        hb_evs.1 hb_evs.2.1 hb_evs.2.2.1 hb_evs.2.2.2
    have hQev_Qm : X ^ dQ * Q_ev ≤ (X + C) ^ dQ * Q_m :=
      hpoly2_sand qTerms _ _ _ _ hb_evs.1 hb_evs.2.1 hb_evs.2.2.1 hb_evs.2.2.2
        hb_ms.1 hb_ms.2.1 hb_ms.2.2.1 hb_ms.2.2.2
    have hPm_Pn : X ^ dP * P_m ≤ (X + C) ^ dP * P_n :=
      hpoly2_sand pTerms _ _ _ _ hb_ms.1 hb_ms.2.1 hb_ms.2.2.1 hb_ms.2.2.2
        hb_ns.1 hb_ns.2.1 hb_ns.2.2.1 hb_ns.2.2.2
    have hQn_Qm : X ^ dQ * Q_n ≤ (X + C) ^ dQ * Q_m :=
      hpoly2_sand qTerms _ _ _ _ hb_ns.1 hb_ns.2.1 hb_ns.2.2.1 hb_ns.2.2.2
        hb_ms.1 hb_ms.2.1 hb_ms.2.2.1 hb_ms.2.2.2
    let K_den := bE * (P_m * (Q_ev * Q_n))
    have hK_pos : K_den ≥ 1 :=
      Nat.mul_le_mul hbE_pos (Nat.mul_le_mul hPm_pos (Nat.mul_le_mul hQev_pos hQn_pos))
    have hrhs_f : (aE * P_m) * ((bE * Q_ev) * (bO * Q_n)) = B_b * K_den := by
      dsimp [B_b, K_den]
      calc
        (aE * P_m) * ((bE * Q_ev) * (bO * Q_n))
            = aE * (P_m * ((bE * bO) * (Q_ev * Q_n))) := by
              have hmid : (bE * Q_ev) * (bO * Q_n) = (bE * bO) * (Q_ev * Q_n) := by
                rw [Nat.mul_assoc bE Q_ev, ← Nat.mul_assoc Q_ev bO Q_n,
                    Nat.mul_comm Q_ev bO, Nat.mul_assoc bO Q_ev Q_n, ← Nat.mul_assoc bE bO]
              rw [hmid, Nat.mul_assoc aE P_m]
        _ = (aE * bO) * (bE * (P_m * (Q_ev * Q_n))) := by
              have hinner : P_m * ((bE * bO) * (Q_ev * Q_n)) = bO * (bE * (P_m * (Q_ev * Q_n))) := by
                rw [Nat.mul_comm bE bO, Nat.mul_assoc bO bE (Q_ev * Q_n),
                    ← Nat.mul_assoc P_m bO (bE * (Q_ev * Q_n)),
                    Nat.mul_comm P_m bO, Nat.mul_assoc bO P_m (bE * (Q_ev * Q_n)),
                    ← Nat.mul_assoc P_m bE (Q_ev * Q_n), Nat.mul_comm P_m bE,
                    Nat.mul_assoc bE P_m (Q_ev * Q_n)]
              rw [hinner, ← Nat.mul_assoc aE bO]
    have hbr1 : B_b * X ^ D * K_den ≤ (X + C) ^ D * (((aE * P_ev) * (bO * Q_n)) * (bE * Q_m)) := by
      have hm := Nat.mul_le_mul_left B_b
        (Nat.mul_le_mul_right (bE * Q_n) (Nat.mul_le_mul hPm_Pev hQev_Qm))
      have hl : B_b * ((X ^ dP * P_m * (X ^ dQ * Q_ev)) * (bE * Q_n)) = B_b * X ^ D * K_den := by
        dsimp [D, K_den]
        rw [Nat.pow_add X dP dQ, Nat.mul_assoc B_b]
        apply congrArg (B_b * ·)
        calc
          (X ^ dP * P_m * (X ^ dQ * Q_ev)) * (bE * Q_n)
              = (X ^ dP * X ^ dQ) * (P_m * Q_ev) * (bE * Q_n) := by
                rw [← Nat.mul_assoc (X ^ dP * P_m), Nat.mul_assoc (X ^ dP) P_m (X ^ dQ),
                    Nat.mul_comm P_m (X ^ dQ), ← Nat.mul_assoc (X ^ dP) (X ^ dQ) P_m,
                    Nat.mul_assoc (X ^ dP * X ^ dQ) P_m Q_ev]
          _ = (X ^ dP * X ^ dQ) * (bE * (P_m * (Q_ev * Q_n))) := by
                rw [Nat.mul_assoc (X ^ dP * X ^ dQ)]
                apply congrArg ((X ^ dP * X ^ dQ) * ·)
                rw [← Nat.mul_assoc (P_m * Q_ev) bE Q_n, Nat.mul_comm (P_m * Q_ev) bE,
                    Nat.mul_assoc bE (P_m * Q_ev) Q_n, Nat.mul_assoc P_m Q_ev Q_n]
      have hr : B_b * (((X + C) ^ dP * P_ev * ((X + C) ^ dQ * Q_m)) * (bE * Q_n)) =
          (X + C) ^ D * (((aE * P_ev) * (bO * Q_n)) * (bE * Q_m)) := by
        dsimp [D, B_b]
        rw [Nat.pow_add (X + C) dP dQ]
        calc
          (aE * bO) * (((X + C) ^ dP * P_ev * ((X + C) ^ dQ * Q_m)) * (bE * Q_n))
              = (aE * bO) * (((X + C) ^ dP * (X + C) ^ dQ) * (P_ev * Q_m * (bE * Q_n))) := by
                apply congrArg ((aE * bO) * ·)
                rw [← Nat.mul_assoc ((X + C) ^ dP * P_ev),
                    Nat.mul_assoc ((X + C) ^ dP) P_ev ((X + C) ^ dQ),
                    Nat.mul_comm P_ev ((X + C) ^ dQ),
                    ← Nat.mul_assoc ((X + C) ^ dP) ((X + C) ^ dQ) P_ev,
                    Nat.mul_assoc ((X + C) ^ dP * (X + C) ^ dQ) P_ev Q_m,
                    Nat.mul_assoc ((X + C) ^ dP * (X + C) ^ dQ)]
          _ = ((X + C) ^ dP * (X + C) ^ dQ) * ((aE * bO) * (P_ev * Q_m * (bE * Q_n))) := by
                rw [← Nat.mul_assoc (aE * bO), Nat.mul_comm (aE * bO) ((X + C) ^ dP * (X + C) ^ dQ),
                    Nat.mul_assoc]
          _ = ((X + C) ^ dP * (X + C) ^ dQ) * (((aE * P_ev) * (bO * Q_n)) * (bE * Q_m)) := by
                apply congrArg (((X + C) ^ dP * (X + C) ^ dQ) * ·)
                have h1 : P_ev * Q_m * (bE * Q_n) = P_ev * Q_n * (bE * Q_m) := by
                  rw [Nat.mul_assoc P_ev Q_m, ← Nat.mul_assoc Q_m bE Q_n,
                      Nat.mul_comm (Q_m * bE) Q_n, Nat.mul_comm Q_m bE,
                      ← Nat.mul_assoc P_ev Q_n]
                have h2 : (aE * bO) * (P_ev * Q_n) = (aE * P_ev) * (bO * Q_n) := by
                  rw [Nat.mul_assoc aE bO, ← Nat.mul_assoc bO P_ev Q_n,
                      Nat.mul_comm bO P_ev, Nat.mul_assoc P_ev bO Q_n, ← Nat.mul_assoc aE P_ev]
                rw [h1, ← Nat.mul_assoc (aE * bO) (P_ev * Q_n), h2]
      rwa [hl, hr] at hm
    have hbr2 : A_b * X ^ D * K_den ≤ (X + C) ^ D * (((aO * P_n) * (bE * Q_ev)) * (bE * Q_m)) := by
      have hm := Nat.mul_le_mul_left A_b
        (Nat.mul_le_mul_right (bE * Q_ev) (Nat.mul_le_mul hPm_Pn hQn_Qm))
      have hl : A_b * ((X ^ dP * P_m * (X ^ dQ * Q_n)) * (bE * Q_ev)) = A_b * X ^ D * K_den := by
        dsimp [D, K_den]
        rw [Nat.pow_add X dP dQ, Nat.mul_assoc A_b]
        apply congrArg (A_b * ·)
        calc
          (X ^ dP * P_m * (X ^ dQ * Q_n)) * (bE * Q_ev)
              = (X ^ dP * X ^ dQ) * (P_m * Q_n) * (bE * Q_ev) := by
                rw [← Nat.mul_assoc (X ^ dP * P_m), Nat.mul_assoc (X ^ dP) P_m (X ^ dQ),
                    Nat.mul_comm P_m (X ^ dQ), ← Nat.mul_assoc (X ^ dP) (X ^ dQ) P_m,
                    Nat.mul_assoc (X ^ dP * X ^ dQ) P_m Q_n]
          _ = (X ^ dP * X ^ dQ) * (bE * (P_m * (Q_ev * Q_n))) := by
                rw [Nat.mul_assoc (X ^ dP * X ^ dQ)]
                apply congrArg ((X ^ dP * X ^ dQ) * ·)
                rw [← Nat.mul_assoc (P_m * Q_n) bE Q_ev, Nat.mul_comm (P_m * Q_n) bE,
                    Nat.mul_assoc bE (P_m * Q_n) Q_ev, Nat.mul_assoc P_m Q_n Q_ev,
                    Nat.mul_comm Q_n Q_ev]
      have hr : A_b * (((X + C) ^ dP * P_n * ((X + C) ^ dQ * Q_m)) * (bE * Q_ev)) =
          (X + C) ^ D * (((aO * P_n) * (bE * Q_ev)) * (bE * Q_m)) := by
        dsimp [D, A_b]
        rw [Nat.pow_add (X + C) dP dQ]
        calc
          (aO * bE) * (((X + C) ^ dP * P_n * ((X + C) ^ dQ * Q_m)) * (bE * Q_ev))
              = (aO * bE) * (((X + C) ^ dP * (X + C) ^ dQ) * (P_n * Q_m * (bE * Q_ev))) := by
                apply congrArg ((aO * bE) * ·)
                rw [← Nat.mul_assoc ((X + C) ^ dP * P_n),
                    Nat.mul_assoc ((X + C) ^ dP) P_n ((X + C) ^ dQ),
                    Nat.mul_comm P_n ((X + C) ^ dQ),
                    ← Nat.mul_assoc ((X + C) ^ dP) ((X + C) ^ dQ) P_n,
                    Nat.mul_assoc ((X + C) ^ dP * (X + C) ^ dQ) P_n Q_m,
                    Nat.mul_assoc ((X + C) ^ dP * (X + C) ^ dQ)]
          _ = ((X + C) ^ dP * (X + C) ^ dQ) * ((aO * bE) * (P_n * Q_m * (bE * Q_ev))) := by
                rw [← Nat.mul_assoc (aO * bE), Nat.mul_comm (aO * bE) ((X + C) ^ dP * (X + C) ^ dQ),
                    Nat.mul_assoc]
          _ = ((X + C) ^ dP * (X + C) ^ dQ) * (((aO * P_n) * (bE * Q_ev)) * (bE * Q_m)) := by
                apply congrArg (((X + C) ^ dP * (X + C) ^ dQ) * ·)
                have h1 : P_n * Q_m * (bE * Q_ev) = P_n * (bE * Q_ev) * Q_m := by
                  rw [Nat.mul_assoc P_n Q_m, Nat.mul_comm Q_m (bE * Q_ev), ← Nat.mul_assoc P_n]
                have ha : aO * bE * P_n = aO * P_n * bE := by
                  rw [Nat.mul_assoc aO bE P_n, Nat.mul_comm bE P_n, ← Nat.mul_assoc aO P_n bE]
                have hb : bE * (bE * Q_ev) * Q_m = (bE * Q_ev) * (bE * Q_m) := by
                  rw [Nat.mul_comm bE (bE * Q_ev), Nat.mul_assoc (bE * Q_ev) bE Q_m]
                rw [h1, ← Nat.mul_assoc (aO * bE) (P_n * (bE * Q_ev)) Q_m,
                    ← Nat.mul_assoc (aO * bE) P_n (bE * Q_ev), ha,
                    Nat.mul_assoc (aO * P_n) bE (bE * Q_ev),
                    Nat.mul_assoc (aO * P_n) (bE * (bE * Q_ev)) Q_m,
                    hb, ← Nat.mul_assoc (aO * P_n) (bE * Q_ev) (bE * Q_m)]
      rwa [hl, hr] at hm
    have hsum := Nat.add_le_add hbr1 hbr2
    rw [← Nat.add_mul (B_b * X ^ D) (A_b * X ^ D) K_den,
        ← Nat.add_mul B_b A_b (X ^ D),
        ← Nat.mul_add ((X + C) ^ D),
        ← Nat.add_mul ((aE * P_ev) * (bO * Q_n)) ((aO * P_n) * (bE * Q_ev)) (bE * Q_m)] at hsum
    have htot : ((B_b + A_b) * X ^ D) * K_den ≤ (B_b * (X + C) ^ D) * K_den := by
      have hm := Nat.mul_le_mul_left ((X + C) ^ D) hcanc
      rw [hrhs_f, ← Nat.mul_assoc ((X + C) ^ D) B_b K_den,
          Nat.mul_comm ((X + C) ^ D) B_b] at hm
      exact Nat.le_trans hsum hm
    have hle_b := nat_mul_le_cancel_right_w5 K_den _ _ hK_pos htot
    have hlt_b := bernoulli_nat_ratio_lt A_b B_b D C X hAb_pos hBb_pos hC_pos hX_ge
    omega

-- ----------------------------------------------------------------------------
-- Section 3A.2: Stateful `Q`-State LSB & MSB Mealy Transducer Preimage Impossibility (`P1.2`)
-- ----------------------------------------------------------------------------

/-- Accumulate unary state-emission weights `e (iterFin g t q)` across `k` steps from `q`. -/
def sumIterFin {Q : Nat} (g : Fin Q -> Fin Q) (e : Fin Q -> Nat) : Nat -> Fin Q -> Nat
  | 0, _ => 0
  | k + 1, q => sumIterFin g e k q + e (iterFin g k q)

theorem sumIterFin_add {Q : Nat} (g : Fin Q -> Fin Q) (e : Fin Q -> Nat) :
    ∀ (a b : Nat) (q : Fin Q),
      sumIterFin g e (a + b) q = sumIterFin g e a q + sumIterFin g e b (iterFin g a q)
  | a, 0, q => by simp [sumIterFin]
  | a, b + 1, q => by
    rw [← Nat.add_assoc a b 1]
    simp only [sumIterFin]
    rw [sumIterFin_add g e a b q, Nat.add_comm a b, iterFin_add g b a q, Nat.add_assoc]

theorem sumIterFin_succ_head {Q : Nat} (g : Fin Q -> Fin Q) (e : Fin Q -> Nat) :
    ∀ (k : Nat) (q : Fin Q),
      sumIterFin g e (k + 1) q = e q + sumIterFin g e k (g q)
  | 0, q => by simp [sumIterFin, iterFin]
  | k + 1, q => by
    have hl : sumIterFin g e (k + 1 + 1) q = sumIterFin g e (k + 1) q + e (iterFin g (k + 1) q) := rfl
    have hr : sumIterFin g e (k + 1) (g q) = sumIterFin g e k (g q) + e (iterFin g k (g q)) := rfl
    rw [hl, hr, sumIterFin_succ_head g e k q]
    have hit : iterFin g (k + 1) q = iterFin g k (g q) := by
      simpa [iterFin] using iterFin_add g k 1 q
    rw [hit, Nat.add_assoc]

/--
  Choice-free unary periodicity starting at `Q - 1` (`i < j < Q + 1 => i ≤ Q - 1`) and
  exact `natFact Q`-periodic affine growth of `sumIterFin` (`choice-free, zero custom axioms`).
-/
theorem fin_unary_iter_and_sum_period_sub1 {Q : Nat} (_hQ : Q ≥ 1)
    (g : Fin Q -> Fin Q) (e : Fin Q -> Nat) (q : Fin Q) :
    ∀ (m k : Nat), k + 1 ≥ Q ->
      iterFin g (k + natFact Q * m) q = iterFin g k q ∧
      sumIterFin g e (k + natFact Q * m) q =
        m * sumIterFin g e (natFact Q) (iterFin g k q) + sumIterFin g e k q := by
  rcases nat_func_pigeonhole Q (Q + 1) (fun t => (iterFin g t q).val)
    (fun t _ => (iterFin g t q).isLt) (by omega) with ⟨i, j, hij, hj_lt, hv_eq⟩
  have hij_eq : iterFin g i q = iterFin g j q := Fin.ext hv_eq
  let p := j - i
  have hp1 : 1 ≤ p := by dsimp [p]; omega
  have hpQ : p ≤ Q := by dsimp [p]; omega
  have hp_step : ∀ k : Nat, k ≥ i -> iterFin g (k + p) q = iterFin g k q := by
    intro k hki
    have hk_sp : k + p = (k - i) + j := by dsimp [p]; omega
    have hk0_sp : k = (k - i) + i := by omega
    rw [hk_sp, iterFin_add g (k - i) j q, ← hij_eq, ← iterFin_add g (k - i) i q, ← hk0_sp]
  have hp_mul : ∀ (c k : Nat), k ≥ i -> iterFin g (k + p * c) q = iterFin g k q := by
    intro c
    induction c with
    | zero => intro k _; simp
    | succ c' ih =>
      intro k hki
      rw [Nat.mul_succ p c', ← Nat.add_assoc k (p * c') p,
          hp_step (k + p * c') (by omega), ih k hki]
  rcases dvd_natFact p Q hp1 hpQ with ⟨u, hu⟩
  have hit_per : ∀ (m k : Nat), k + 1 ≥ Q ->
      iterFin g (k + natFact Q * m) q = iterFin g k q := by
    intro m k hk
    rw [hu, Nat.mul_assoc p u m]
    exact hp_mul (u * m) k (by omega)
  intro m k hk
  refine ⟨hit_per m k hk, ?_⟩
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.mul_succ (natFact Q) m', ← Nat.add_assoc k (natFact Q * m') (natFact Q),
        sumIterFin_add g e (k + natFact Q * m') (natFact Q) q,
        hit_per m' k hk, ih, Nat.succ_mul]
    omega

/-- Fuel-bounded LSB-to-MSB binary Mealy transducer output accumulator. -/
def runLSBTransducerAux {Q : Nat} (delta : Fin Q -> Bool -> Fin Q)
    (emit : Fin Q -> Bool -> Nat) : Nat -> Fin Q -> Nat -> Nat
  | 0, _, _ => 0
  | fuel + 1, q, n =>
    if n = 0 then 0
    else emit q (n % 2 == 1) + runLSBTransducerAux delta emit fuel (delta q (n % 2 == 1)) (n / 2)

def runLSBTransducerFrom {Q : Nat} (delta : Fin Q -> Bool -> Fin Q)
    (emit : Fin Q -> Bool -> Nat) (q : Fin Q) (n : Nat) : Nat :=
  runLSBTransducerAux delta emit n q n

/--
  Run a deterministic `Q`-state binary Mealy transducer LSB-to-MSB across the unpadded binary
  expansion of `n`, summing per-transition weights `emit q b` (`0` at `n = 0`).
  Every nonnegative linear combination of state-transition counts `∑_{q, b} c_{q, b} · #trans_{q, b}(n)`
  is an instance with `emit q b := c_{q, b}`.
-/
def runLSBTransducerOut (Q : Nat) (delta : Fin Q -> Bool -> Fin Q)
    (emit : Fin Q -> Bool -> Nat) (q0 : Fin Q) (n : Nat) : Nat :=
  runLSBTransducerFrom delta emit q0 n

/-- Fuel-bounded MSB-to-LSB binary Mealy transducer output accumulator. -/
def runMSBTransducerAux {Q : Nat} (delta : Fin Q -> Bool -> Fin Q)
    (emit : Fin Q -> Bool -> Nat) (q0 : Fin Q) : Nat -> Nat -> Nat
  | 0, _ => 0
  | fuel + 1, n =>
    if n = 0 then 0
    else runMSBTransducerAux delta emit q0 fuel (n / 2) +
         emit (runMSBAutomaton Q delta q0 (n / 2)) (n % 2 == 1)

/--
  Run a deterministic `Q`-state binary Mealy transducer MSB-to-LSB across the unpadded binary
  expansion of `n`, summing per-transition weights `emit q b` (`0` at `n = 0`).
-/
def runMSBTransducerOut (Q : Nat) (delta : Fin Q -> Bool -> Fin Q)
    (emit : Fin Q -> Bool -> Nat) (q0 : Fin Q) (n : Nat) : Nat :=
  runMSBTransducerAux delta emit q0 n n

theorem runLSBTransducerAux_eq_of_ge {Q : Nat} (delta : Fin Q -> Bool -> Fin Q)
    (emit : Fin Q -> Bool -> Nat) :
    ∀ (f1 f2 : Nat) (q : Fin Q) (n : Nat),
      n ≤ f1 -> n ≤ f2 ->
      runLSBTransducerAux delta emit f1 q n = runLSBTransducerAux delta emit f2 q n
  | 0, 0, _, _, _, _ => rfl
  | 0, _ + 1, _, n, h1, _ => by rw [show n = 0 by omega]; simp [runLSBTransducerAux]
  | _ + 1, 0, _, n, _, h2 => by rw [show n = 0 by omega]; simp [runLSBTransducerAux]
  | f1 + 1, f2 + 1, q, n, h1, h2 => by
    simp only [runLSBTransducerAux]
    by_cases hn0 : n = 0
    · simp [hn0]
    · simp only [hn0, ite_false]
      rw [runLSBTransducerAux_eq_of_ge delta emit f1 f2
        (delta q (n % 2 == 1)) (n / 2) (by omega) (by omega)]

theorem runMSBTransducerAux_eq_of_ge {Q : Nat} (delta : Fin Q -> Bool -> Fin Q)
    (emit : Fin Q -> Bool -> Nat) (q0 : Fin Q) :
    ∀ (f1 f2 n : Nat),
      n ≤ f1 -> n ≤ f2 ->
      runMSBTransducerAux delta emit q0 f1 n = runMSBTransducerAux delta emit q0 f2 n
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, n, h1, _ => by rw [show n = 0 by omega]; simp [runMSBTransducerAux]
  | _ + 1, 0, n, _, h2 => by rw [show n = 0 by omega]; simp [runMSBTransducerAux]
  | f1 + 1, f2 + 1, n, h1, h2 => by
    simp only [runMSBTransducerAux]
    by_cases hn0 : n = 0
    · simp [hn0]
    · simp only [hn0, ite_false]
      rw [runMSBTransducerAux_eq_of_ge delta emit q0 f1 f2 (n / 2) (by omega) (by omega)]

theorem runLSBTransducerFrom_step_pos {Q : Nat} (delta : Fin Q -> Bool -> Fin Q)
    (emit : Fin Q -> Bool -> Nat) (q : Fin Q) (n : Nat) (hn : n ≥ 1) :
    runLSBTransducerFrom delta emit q n =
      emit q (n % 2 == 1) + runLSBTransducerFrom delta emit (delta q (n % 2 == 1)) (n / 2) := by
  unfold runLSBTransducerFrom
  cases n with
  | zero => omega
  | succ m =>
    simp only [runLSBTransducerAux, Nat.succ_ne_zero, ite_false]
    rw [runLSBTransducerAux_eq_of_ge delta emit m ((m + 1) / 2) _ ((m + 1) / 2)
      (by omega) (Nat.le_refl _)]

theorem runMSBTransducerOut_step_pos {Q : Nat} (delta : Fin Q -> Bool -> Fin Q)
    (emit : Fin Q -> Bool -> Nat) (q0 : Fin Q) (n : Nat) (hn : n ≥ 1) :
    runMSBTransducerOut Q delta emit q0 n =
      runMSBTransducerOut Q delta emit q0 (n / 2) +
        emit (runMSBAutomaton Q delta q0 (n / 2)) (n % 2 == 1) := by
  unfold runMSBTransducerOut
  cases n with
  | zero => omega
  | succ m =>
    simp only [runMSBTransducerAux, Nat.succ_ne_zero, ite_false]
    rw [runMSBTransducerAux_eq_of_ge delta emit q0 m ((m + 1) / 2) ((m + 1) / 2)
      (by omega) (Nat.le_refl _)]

theorem runLSBTransducerFrom_mul_pow2 {Q : Nat} (delta : Fin Q -> Bool -> Fin Q)
    (emit : Fin Q -> Bool -> Nat) (H : Nat) (hH : H ≥ 1) :
    ∀ (d : Nat) (q : Fin Q),
      runLSBTransducerFrom delta emit q (2 ^ d * H) =
        sumIterFin (fun s => delta s false) (fun s => emit s false) d q +
          runLSBTransducerFrom delta emit (iterFin (fun s => delta s false) d q) H
  | 0, q => by simp [sumIterFin, iterFin]
  | d + 1, q => by
    have hmul : 2 ^ (d + 1) * H = 2 * (2 ^ d * H) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ d) 2, Nat.mul_assoc]
    have hpos : 2 ^ d * H ≥ 1 := Nat.mul_le_mul (pow2_pos_nat d) hH
    have hm2 : ((2 * (2 ^ d * H)) % 2 == 1) = false := by
      rw [Nat.mul_mod_right]; rfl
    rw [hmul, runLSBTransducerFrom_step_pos delta emit q _ (by omega), hm2,
        show (2 * (2 ^ d * H)) / 2 = 2 ^ d * H by omega,
        runLSBTransducerFrom_mul_pow2 delta emit H hH d (delta q false),
        ← Nat.add_assoc, ← sumIterFin_succ_head (fun s => delta s false) (fun s => emit s false) d q]
    have hit : iterFin (fun s => delta s false) d (delta q false) =
        iterFin (fun s => delta s false) (d + 1) q :=
      (iterFin_add (fun s => delta s false) d 1 q).symm
    rw [hit]

theorem runMSBTransducerOut_mul_pow2 {Q : Nat} (delta : Fin Q -> Bool -> Fin Q)
    (emit : Fin Q -> Bool -> Nat) (q0 : Fin Q) (H : Nat) (hH : H ≥ 1) :
    ∀ d : Nat,
      runMSBTransducerOut Q delta emit q0 (2 ^ d * H) =
        runMSBTransducerOut Q delta emit q0 H +
          sumIterFin (fun s => delta s false) (fun s => emit s false) d
            (runMSBAutomaton Q delta q0 H)
  | 0 => by simp [sumIterFin]
  | d + 1 => by
    have hmul : 2 ^ (d + 1) * H = 2 * (2 ^ d * H) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ d) 2, Nat.mul_assoc]
    have hpos : 2 ^ d * H ≥ 1 := Nat.mul_le_mul (pow2_pos_nat d) hH
    have hm2 : ((2 * (2 ^ d * H)) % 2 == 1) = false := by
      rw [Nat.mul_mod_right]; rfl
    rw [hmul, runMSBTransducerOut_step_pos delta emit q0 _ (by omega), hm2,
        show (2 * (2 ^ d * H)) / 2 = 2 ^ d * H by omega,
        runMSBTransducerOut_mul_pow2 delta emit q0 H hH d,
        runMSBAutomaton_mul_pow2 delta q0 H hH d, Nat.add_assoc]
    rfl

/-- Fixed-width `r`-bit LSB state transition across the low `r` bits of `R`. -/
def runLSBFixedWidth {Q : Nat} (delta : Fin Q -> Bool -> Fin Q) :
    Nat -> Fin Q -> Nat -> Fin Q
  | 0, q, _ => q
  | r + 1, q, R => runLSBFixedWidth delta r (delta q (R % 2 == 1)) (R / 2)

theorem runLSBFixedWidth_zero_val {Q : Nat} (delta : Fin Q -> Bool -> Fin Q) :
    ∀ (b : Nat) (q : Fin Q),
      runLSBFixedWidth delta b q 0 = iterFin (fun s => delta s false) b q
  | 0, q => rfl
  | b + 1, q => by
    simp only [runLSBFixedWidth]
    have hb0 : (0 % 2 == 1) = false := rfl
    have hd0 : 0 / 2 = 0 := rfl
    rw [hb0, hd0, runLSBFixedWidth_zero_val delta b (delta q false)]
    exact (iterFin_add (fun s => delta s false) b 1 q).symm

theorem runLSBFixedWidth_pow2 {Q : Nat} (delta : Fin Q -> Bool -> Fin Q) :
    ∀ (a b : Nat) (q : Fin Q),
      runLSBFixedWidth delta (a + 1 + b) q (2 ^ a) =
        iterFin (fun s => delta s false) b
          (delta (iterFin (fun s => delta s false) a q) true)
  | 0, b, q => by
    simp only [Nat.zero_add, Nat.pow_zero, iterFin]
    have h1b : 1 + b = b + 1 := Nat.add_comm 1 b
    rw [h1b]
    simp only [runLSBFixedWidth]
    have hb1 : (1 % 2 == 1) = true := rfl
    have hd1 : 1 / 2 = 0 := rfl
    rw [hb1, hd1]
    exact runLSBFixedWidth_zero_val delta b (delta q true)
  | a + 1, b, q => by
    have hsp : (a + 1) + 1 + b = (a + 1 + b) + 1 := by omega
    rw [hsp]
    simp only [runLSBFixedWidth]
    have hmul : 2 ^ (a + 1) = 2 * 2 ^ a := by rw [Nat.pow_succ, Nat.mul_comm]
    have hb0 : ((2 * 2 ^ a) % 2 == 1) = false := by rw [Nat.mul_mod_right]; rfl
    have hd0 : (2 * 2 ^ a) / 2 = 2 ^ a := by omega
    rw [hmul, hb0, hd0, runLSBFixedWidth_pow2 delta a b (delta q false)]
    have hit : iterFin (fun s => delta s false) a (delta q false) =
        iterFin (fun s => delta s false) (a + 1) q :=
      (iterFin_add (fun s => delta s false) a 1 q).symm
    rw [hit]

theorem both_transducers_low_pad_peel {Q : Nat} (hQ : Q ≥ 1)
    (delta : Fin Q -> Bool -> Fin Q) (emit : Fin Q -> Bool -> Nat) (q0 : Fin Q)
    (H k m : Nat) (hH : H ≥ 1) (hk : k + 1 ≥ Q) :
    ∀ (r R : Nat) (q : Fin Q),
      R < 2 ^ r ->
      let Nm := 2 ^ (k + natFact Q * m) * H
      let N0 := 2 ^ k * H
      let g0 := fun s => delta s false
      let e0 := fun s => emit s false
      (runLSBFrom delta q (2 ^ r * Nm + R) = runLSBFrom delta q (2 ^ r * N0 + R) ∧
       runMSBAutomaton Q delta q0 (2 ^ r * Nm + R) =
         runMSBAutomaton Q delta q0 (2 ^ r * N0 + R)) ∧
      runLSBTransducerFrom delta emit q (2 ^ r * Nm + R) =
        m * sumIterFin g0 e0 (natFact Q) (iterFin g0 k (runLSBFixedWidth delta r q R)) +
          runLSBTransducerFrom delta emit q (2 ^ r * N0 + R) ∧
      runMSBTransducerOut Q delta emit q0 (2 ^ r * Nm + R) =
        m * sumIterFin g0 e0 (natFact Q) (iterFin g0 k (runMSBAutomaton Q delta q0 H)) +
          runMSBTransducerOut Q delta emit q0 (2 ^ r * N0 + R)
  | 0, R, q, hR => by
    have hR0 : R = 0 := by simp at hR; exact hR
    subst hR0
    dsimp only
    simp only [Nat.pow_zero, Nat.one_mul, Nat.add_zero, runLSBFixedWidth]
    rcases fin_unary_iter_and_sum_period_sub1 hQ (fun s => delta s false) (fun s => emit s false)
      q m k hk with ⟨hitL, hsumL⟩
    rcases fin_unary_iter_and_sum_period_sub1 hQ (fun s => delta s false) (fun s => emit s false)
      (runMSBAutomaton Q delta q0 H) m k hk with ⟨hitM, hsumM⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [runLSBFrom_mul_pow2 delta H hH (k + natFact Q * m) q,
          runLSBFrom_mul_pow2 delta H hH k q, hitL]
    · rw [runMSBAutomaton_mul_pow2 delta q0 H hH (k + natFact Q * m),
          runMSBAutomaton_mul_pow2 delta q0 H hH k, hitM]
    · rw [runLSBTransducerFrom_mul_pow2 delta emit H hH (k + natFact Q * m) q,
          runLSBTransducerFrom_mul_pow2 delta emit H hH k q, hitL, hsumL, Nat.add_assoc]
    · rw [runMSBTransducerOut_mul_pow2 delta emit q0 H hH (k + natFact Q * m),
          runMSBTransducerOut_mul_pow2 delta emit q0 H hH k, hsumM]
      omega
  | r + 1, R, q, hR => by
    dsimp only
    let Nm := 2 ^ (k + natFact Q * m) * H
    let N0 := 2 ^ k * H
    have hNm_pos : Nm ≥ 1 := Nat.mul_le_mul (pow2_pos_nat _) hH
    have hN0_pos : N0 ≥ 1 := Nat.mul_le_mul (pow2_pos_nat _) hH
    have hrNm_pos : 2 ^ r * Nm ≥ 1 := Nat.mul_le_mul (pow2_pos_nat r) hNm_pos
    have hrN0_pos : 2 ^ r * N0 ≥ 1 := Nat.mul_le_mul (pow2_pos_nat r) hN0_pos
    have hR2 : R / 2 < 2 ^ r := by rw [Nat.pow_succ] at hR; omega
    have hsp_m : 2 ^ (r + 1) * Nm + R = 2 * (2 ^ r * Nm) + R := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ r) 2, Nat.mul_assoc]
    have hsp_0 : 2 ^ (r + 1) * N0 + R = 2 * (2 ^ r * N0) + R := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ r) 2, Nat.mul_assoc]
    have hbit_m : ((2 * (2 ^ r * Nm) + R) % 2 == 1) = (R % 2 == 1) := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left]
    have hbit_0 : ((2 * (2 ^ r * N0) + R) % 2 == 1) = (R % 2 == 1) := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left]
    have hdiv_m : (2 * (2 ^ r * Nm) + R) / 2 = 2 ^ r * Nm + R / 2 := by omega
    have hdiv_0 : (2 * (2 ^ r * N0) + R) / 2 = 2 ^ r * N0 + R / 2 := by omega
    rcases both_transducers_low_pad_peel hQ delta emit q0 H k m hH hk r (R / 2)
      (delta q (R % 2 == 1)) hR2 with ⟨⟨ih_autL, ih_autM⟩, ih_trL, ih_trM⟩
    change runLSBFrom delta _ (2 ^ r * Nm + R / 2) = runLSBFrom delta _ (2 ^ r * N0 + R / 2) at ih_autL
    change runMSBAutomaton Q delta q0 (2 ^ r * Nm + R / 2) =
      runMSBAutomaton Q delta q0 (2 ^ r * N0 + R / 2) at ih_autM
    change runLSBTransducerFrom delta emit _ (2 ^ r * Nm + R / 2) = _ at ih_trL
    change runMSBTransducerOut Q delta emit q0 (2 ^ r * Nm + R / 2) = _ at ih_trM
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hsp_m, hsp_0,
          runLSBFrom_step_pos delta q (2 * (2 ^ r * Nm) + R) (by omega),
          runLSBFrom_step_pos delta q (2 * (2 ^ r * N0) + R) (by omega),
          hbit_m, hbit_0, hdiv_m, hdiv_0]
      exact ih_autL
    · rw [hsp_m, hsp_0,
          runMSBAutomaton_step_pos delta q0 (2 * (2 ^ r * Nm) + R) (by omega),
          runMSBAutomaton_step_pos delta q0 (2 * (2 ^ r * N0) + R) (by omega),
          hbit_m, hbit_0, hdiv_m, hdiv_0, ih_autM]
    · simp only [runLSBFixedWidth]
      rw [hsp_m, hsp_0,
          runLSBTransducerFrom_step_pos delta emit q (2 * (2 ^ r * Nm) + R) (by omega),
          runLSBTransducerFrom_step_pos delta emit q (2 * (2 ^ r * N0) + R) (by omega),
          hbit_m, hbit_0, hdiv_m, hdiv_0, ih_trL]
      dsimp [N0]; omega
    · rw [hsp_m, hsp_0,
          runMSBTransducerOut_step_pos delta emit q0 (2 * (2 ^ r * Nm) + R) (by omega),
          runMSBTransducerOut_step_pos delta emit q0 (2 * (2 ^ r * N0) + R) (by omega),
          hbit_m, hbit_0, hdiv_m, hdiv_0, ih_autM, ih_trM]
      dsimp [N0]; omega

theorem runMSBAutomaton_and_transducer_mersenne_tail {Q : Nat}
    (delta : Fin Q -> Bool -> Fin Q) (emit : Fin Q -> Bool -> Nat) (q0 : Fin Q)
    (H : Nat) (hH : H ≥ 1) :
    ∀ d : Nat,
      runMSBAutomaton Q delta q0 (2 ^ d * H + (2 ^ d - 1)) =
        iterFin (fun s => delta s true) d (runMSBAutomaton Q delta q0 H) ∧
      runMSBTransducerOut Q delta emit q0 (2 ^ d * H + (2 ^ d - 1)) =
        runMSBTransducerOut Q delta emit q0 H +
          sumIterFin (fun s => delta s true) (fun s => emit s true) d
            (runMSBAutomaton Q delta q0 H)
  | 0 => by simp [iterFin, sumIterFin]
  | d + 1 => by
    rcases runMSBAutomaton_and_transducer_mersenne_tail delta emit q0 H hH d with ⟨ih_a, ih_t⟩
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
    refine ⟨?_, ?_⟩
    · rw [hval, runMSBAutomaton_step_pos delta q0 _ hpos, hbit, hdiv, ih_a]; rfl
    · rw [hval, runMSBTransducerOut_step_pos delta emit q0 _ hpos, hbit, hdiv, ih_a, ih_t,
          Nat.add_assoc]
      rfl

/--
  Theorem W9.3a' (`berg_meinardus_stateful_transducer_preimage_impossibility`, choice-free `zero custom axioms`):
  Universal `∀ Q ≥ 1` Stateful LSB & MSB Finite-State Mealy Transducer Preimage Impossibility
  (Closing Transition-Count / Per-Transition Weighted Automata Quotients in `Branch P1.2`):
  1. **Universal `Q!`-Periodic Affine Transition-Weight Growth (`∀ Q ≥ 1`, Unrestricted `emit`)**:
     For EVERY state count `Q ≥ 1`, EVERY transition table `delta : Fin Q -> Bool -> Fin Q`,
     EVERY per-transition weight `emit : Fin Q -> Bool -> Nat` (representing arbitrary nonnegative
     linear combinations of state-transition counts `∑_{q, b} c_{q, b} · #trans_{q, b}(n)`), and
     EVERY `q0 : Fin Q`, along `ms = 3 * 4 ^ (2 * Q + natFact Q * s) + 2 ^ (2 * Q + 1)`,
     `evs = 2 ^ (natFact Q) * ms`, and `ns = (2 * ms - 1) / 3`:
     - BOTH `runLSBTransducerOut` AND `runMSBTransducerOut` grow **EXACTLY AFFINELY** in `s`, with
       **100% IDENTICAL** linear slope `2 * cycSum_m` on `ms` and `evs`!
  2. **Universal Joint LSB + MSB Positive-`0`-Cycle Mealy Transducer Impossibility (`∀ Q ≥ 1`)**:
     Even when disconnected `0`-cycles have **distinct** positive slopes (`cycSum_m ≠ cycSum_n`),
     whenever every `0`-cycle has positive weight (`∀ q, sumIterFin (delta · false) (emit · false) (natFact Q) q ≥ 1`,
     including EVERY positive transition weight `∀ q, emit q false ≥ 1` and `zeroBitCount`),
     NO rational quotient built from joint `(runLSBAutomaton, runMSBAutomaton)` states and
     trivariate `NatPoly3` polynomials in `(runLSBTransducerOut, runMSBTransducerOut, binBitLength)`
     can satisfy `IsPositiveRationalPreimageWeight`!
  3. **Universal Positive-`1`-Cycle MSB Mealy Transducer Impossibility via Mersenne `1`-Spines (`∀ Q ≥ 1`)**:
     Dually, whenever every `1`-cycle has positive weight (`∀ q, sumIterFin (delta · true) (emit · true) (natFact Q) q ≥ 1`,
     covering `oneBitCount` and parity-gated `1`-transition counters whose `0`-cycles emit `0`!),
     NO polynomial quotient `evalNatPoly2 pTerms (runMSBTransducerOut Q deltaM emitM q0M n) (binBitLength n) / evalNatPoly2 qTerms ...`
     can satisfy `IsPositiveRationalPreimageWeight` (killed along `ms_1 = 3 * 2 ^ (2 * Q + natFact Q * s) - 1`,
     `2 * ms_1`, `ns_1 = 2 ^ (2 * Q + natFact Q * s + 1) - 1`)!
-/
theorem berg_meinardus_stateful_transducer_preimage_impossibility :
    (∀ (Q s : Nat) (_hQ : Q ≥ 1)
       (delta : Fin Q -> Bool -> Fin Q) (emit : Fin Q -> Bool -> Nat) (q0 : Fin Q),
      let P := natFact Q
      let m0 := 3 * 4 ^ (2 * Q) + 2 ^ (2 * Q + 1)
      let ev0 := 2 ^ P * m0
      let n0 := (2 * m0 - 1) / 3
      let ms := 3 * 4 ^ (2 * Q + P * s) + 2 ^ (2 * Q + 1)
      let evs := 2 ^ P * ms
      let ns := (2 * ms - 1) / 3
      let g0 := fun st => delta st false
      let e0 := fun st => emit st false
      let kL_m := sumIterFin g0 e0 P
        (iterFin g0 (2 * Q - 2) (runLSBFixedWidth delta (2 * Q + 2) q0 (2 ^ (2 * Q + 1))))
      let kL_n := sumIterFin g0 e0 P
        (iterFin g0 (2 * Q) (runLSBFixedWidth delta (2 * Q + 1) q0 ((4 ^ (Q + 1) - 1) / 3)))
      let kM_m := sumIterFin g0 e0 P
        (iterFin g0 (2 * Q - 2) (runMSBAutomaton Q delta q0 3))
      let kM_n := sumIterFin g0 e0 P
        (iterFin g0 (2 * Q) (runMSBAutomaton Q delta q0 1))
      runLSBTransducerOut Q delta emit q0 ms = 2 * s * kL_m + runLSBTransducerOut Q delta emit q0 m0 ∧
      runLSBTransducerOut Q delta emit q0 evs = 2 * s * kL_m + runLSBTransducerOut Q delta emit q0 ev0 ∧
      runLSBTransducerOut Q delta emit q0 ns = 2 * s * kL_n + runLSBTransducerOut Q delta emit q0 n0 ∧
      runMSBTransducerOut Q delta emit q0 ms = 2 * s * kM_m + runMSBTransducerOut Q delta emit q0 m0 ∧
      runMSBTransducerOut Q delta emit q0 evs = 2 * s * kM_m + runMSBTransducerOut Q delta emit q0 ev0 ∧
      runMSBTransducerOut Q delta emit q0 ns = 2 * s * kM_n + runMSBTransducerOut Q delta emit q0 n0) ∧
    (∀ (Q : Nat) (_hQ : Q ≥ 1)
       (deltaL deltaM : Fin Q -> Bool -> Fin Q)
       (emitL emitM : Fin Q -> Bool -> Nat)
       (q0L q0M : Fin Q)
       (_hposL : ∀ q : Fin Q,
         sumIterFin (fun s => deltaL s false) (fun s => emitL s false) (natFact Q) q ≥ 1)
       (_hposM : ∀ q : Fin Q,
         sumIterFin (fun s => deltaM s false) (fun s => emitM s false) (natFact Q) q ≥ 1)
       (fNum fDen : Fin Q -> Fin Q -> Nat)
       (pTerms qTerms : NatPoly3)
       (pTheta qTheta : Nat),
      ¬ IsPositiveRationalPreimageWeight
        (fun n =>
          fNum (runLSBAutomaton Q deltaL q0L n) (runMSBAutomaton Q deltaM q0M n) *
            evalNatPoly3 pTerms
              (runLSBTransducerOut Q deltaL emitL q0L n)
              (runMSBTransducerOut Q deltaM emitM q0M n)
              (binBitLength n))
        (fun n =>
          fDen (runLSBAutomaton Q deltaL q0L n) (runMSBAutomaton Q deltaM q0M n) *
            evalNatPoly3 qTerms
              (runLSBTransducerOut Q deltaL emitL q0L n)
              (runMSBTransducerOut Q deltaM emitM q0M n)
              (binBitLength n))
        pTheta qTheta) ∧
    (∀ (Q : Nat) (_hQ : Q ≥ 1)
       (deltaM : Fin Q -> Bool -> Fin Q)
       (emitM : Fin Q -> Bool -> Nat)
       (q0M : Fin Q)
       (_hpos1 : ∀ q : Fin Q,
         sumIterFin (fun s => deltaM s true) (fun s => emitM s true) (natFact Q) q ≥ 1)
       (pTerms qTerms : NatPoly2)
       (pTheta qTheta : Nat),
      ¬ IsPositiveRationalPreimageWeight
        (fun n => evalNatPoly2 pTerms (runMSBTransducerOut Q deltaM emitM q0M n) (binBitLength n))
        (fun n => evalNatPoly2 qTerms (runMSBTransducerOut Q deltaM emitM q0M n) (binBitLength n))
        pTheta qTheta) := by
  have htr_fam : ∀ (Q s : Nat) (hQ : Q ≥ 1)
      (delta : Fin Q -> Bool -> Fin Q) (emit : Fin Q -> Bool -> Nat) (q0 : Fin Q),
      let P := natFact Q
      let m0 := 3 * 4 ^ (2 * Q) + 2 ^ (2 * Q + 1)
      let ev0 := 2 ^ P * m0
      let n0 := (2 * m0 - 1) / 3
      let ms := 3 * 4 ^ (2 * Q + P * s) + 2 ^ (2 * Q + 1)
      let evs := 2 ^ P * ms
      let ns := (2 * ms - 1) / 3
      let g0 := fun st => delta st false
      let e0 := fun st => emit st false
      let kL_m := sumIterFin g0 e0 P
        (iterFin g0 (2 * Q - 2) (runLSBFixedWidth delta (2 * Q + 2) q0 (2 ^ (2 * Q + 1))))
      let kL_n := sumIterFin g0 e0 P
        (iterFin g0 (2 * Q) (runLSBFixedWidth delta (2 * Q + 1) q0 ((4 ^ (Q + 1) - 1) / 3)))
      let kM_m := sumIterFin g0 e0 P
        (iterFin g0 (2 * Q - 2) (runMSBAutomaton Q delta q0 3))
      let kM_n := sumIterFin g0 e0 P
        (iterFin g0 (2 * Q) (runMSBAutomaton Q delta q0 1))
      runLSBTransducerOut Q delta emit q0 ms = 2 * s * kL_m + runLSBTransducerOut Q delta emit q0 m0 ∧
      runLSBTransducerOut Q delta emit q0 evs = 2 * s * kL_m + runLSBTransducerOut Q delta emit q0 ev0 ∧
      runLSBTransducerOut Q delta emit q0 ns = 2 * s * kL_n + runLSBTransducerOut Q delta emit q0 n0 ∧
      runMSBTransducerOut Q delta emit q0 ms = 2 * s * kM_m + runMSBTransducerOut Q delta emit q0 m0 ∧
      runMSBTransducerOut Q delta emit q0 evs = 2 * s * kM_m + runMSBTransducerOut Q delta emit q0 ev0 ∧
      runMSBTransducerOut Q delta emit q0 ns = 2 * s * kM_n + runMSBTransducerOut Q delta emit q0 n0 := by
    intro Q s hQ delta emit q0
    dsimp only
    let P := natFact Q
    have hP_2s : P * (2 * s) = 2 * (P * s) := by
      rw [← Nat.mul_assoc P 2 s, Nat.mul_comm P 2, Nat.mul_assoc]
    unfold runLSBTransducerOut
    -- 1. `ms` vs `m0`:
    have hR_m_lt : 2 ^ (2 * Q + 1) < 2 ^ (2 * Q + 2) := by
      rw [Nat.pow_succ 2 (2 * Q + 1)]; have hp := pow2_pos_nat (2 * Q + 1); omega
    rcases both_transducers_low_pad_peel hQ delta emit q0 3 (2 * Q - 2) (2 * s)
      (by decide) (by omega) (2 * Q + 2) (2 ^ (2 * Q + 1)) q0 hR_m_lt with ⟨_, hms_l, hms_m⟩
    have hms_rew : 2 ^ (2 * Q + 2) * (2 ^ (2 * Q - 2 + P * (2 * s)) * 3) + 2 ^ (2 * Q + 1) =
        3 * 4 ^ (2 * Q + P * s) + 2 ^ (2 * Q + 1) := by
      rw [← Nat.mul_assoc (2 ^ (2 * Q + 2)), ← Nat.pow_add 2 (2 * Q + 2),
          show 2 * Q + 2 + (2 * Q - 2 + P * (2 * s)) = 2 * (2 * Q + P * s) by rw [hP_2s]; omega,
          ← pow4_eq_pow2_even, Nat.mul_comm _ 3]
    have hm0_rew : 2 ^ (2 * Q + 2) * (2 ^ (2 * Q - 2) * 3) + 2 ^ (2 * Q + 1) =
        3 * 4 ^ (2 * Q) + 2 ^ (2 * Q + 1) := by
      rw [← Nat.mul_assoc (2 ^ (2 * Q + 2)), ← Nat.pow_add 2 (2 * Q + 2) (2 * Q - 2),
          show 2 * Q + 2 + (2 * Q - 2) = 2 * (2 * Q) by omega,
          ← pow4_eq_pow2_even, Nat.mul_comm _ 3]
    rw [hms_rew, hm0_rew] at hms_l hms_m
    -- 2. `evs` vs `ev0`:
    have hR_ev_lt : 2 ^ (2 * Q + 1 + P) < 2 ^ (2 * Q + 2 + P) := by
      rw [show 2 * Q + 2 + P = (2 * Q + 1 + P) + 1 by omega, Nat.pow_succ]
      have hp := pow2_pos_nat (2 * Q + 1 + P); omega
    rcases both_transducers_low_pad_peel hQ delta emit q0 3 (2 * Q - 2) (2 * s)
      (by decide) (by omega) (2 * Q + 2 + P) (2 ^ (2 * Q + 1 + P)) q0 hR_ev_lt with
      ⟨_, hevs_l, hevs_m⟩
    have hevs_rew :
        2 ^ (2 * Q + 2 + P) * (2 ^ (2 * Q - 2 + P * (2 * s)) * 3) + 2 ^ (2 * Q + 1 + P) =
          2 ^ P * (3 * 4 ^ (2 * Q + P * s) + 2 ^ (2 * Q + 1)) := by
      rw [Nat.mul_add (2 ^ P),
          show 2 ^ P * 2 ^ (2 * Q + 1) = 2 ^ (2 * Q + 1 + P) by
            rw [Nat.add_comm (2 * Q + 1) P, ← Nat.pow_add],
          ← Nat.mul_assoc (2 ^ (2 * Q + 2 + P)), ← Nat.pow_add 2 (2 * Q + 2 + P),
          show 2 * Q + 2 + P + (2 * Q - 2 + P * (2 * s)) = P + 2 * (2 * Q + P * s) by
            rw [hP_2s]; omega,
          Nat.pow_add 2 P, ← pow4_eq_pow2_even,
          Nat.mul_comm (2 ^ P * 4 ^ (2 * Q + P * s)) 3,
          ← Nat.mul_assoc 3 (2 ^ P), Nat.mul_comm 3 (2 ^ P), Nat.mul_assoc]
    have hev0_rew :
        2 ^ (2 * Q + 2 + P) * (2 ^ (2 * Q - 2) * 3) + 2 ^ (2 * Q + 1 + P) =
          2 ^ P * (3 * 4 ^ (2 * Q) + 2 ^ (2 * Q + 1)) := by
      rw [Nat.mul_add (2 ^ P),
          show 2 ^ P * 2 ^ (2 * Q + 1) = 2 ^ (2 * Q + 1 + P) by
            rw [Nat.add_comm (2 * Q + 1) P, ← Nat.pow_add],
          ← Nat.mul_assoc (2 ^ (2 * Q + 2 + P)), ← Nat.pow_add 2 (2 * Q + 2 + P),
          show 2 * Q + 2 + P + (2 * Q - 2) = P + 2 * (2 * Q) by omega,
          Nat.pow_add 2 P, ← pow4_eq_pow2_even,
          Nat.mul_comm (2 ^ P * 4 ^ (2 * Q)) 3,
          ← Nat.mul_assoc 3 (2 ^ P), Nat.mul_comm 3 (2 ^ P), Nat.mul_assoc]
    have hfw_eq : runLSBFixedWidth delta (2 * Q + 2 + P) q0 (2 ^ (2 * Q + 1 + P)) =
        runLSBFixedWidth delta (2 * Q + 2) q0 (2 ^ (2 * Q + 1)) := by
      have h1 := runLSBFixedWidth_pow2 delta (2 * Q + 1 + P) 0 q0
      have h2 := runLSBFixedWidth_pow2 delta (2 * Q + 1) 0 q0
      have hsp1 : 2 * Q + 1 + P + 1 + 0 = 2 * Q + 2 + P := by omega
      have hsp2 : 2 * Q + 1 + 1 + 0 = 2 * Q + 2 := by omega
      rw [hsp1] at h1
      rw [hsp2] at h2
      rw [h1, h2]
      dsimp only [iterFin]
      have hper := (fin_unary_iter_and_sum_period_sub1 hQ (fun st => delta st false)
        (fun st => emit st false) q0 1 (2 * Q + 1) (by omega)).1
      dsimp [P]
      rw [Nat.mul_one] at hper
      rw [hper]
      rfl
    rw [hevs_rew, hev0_rew, hfw_eq] at hevs_l
    rw [hevs_rew, hev0_rew] at hevs_m
    -- 3. `ns` vs `n0`:
    let R_n := (4 ^ (Q + 1) - 1) / 3
    have h4_m3 : 4 ^ Q % 3 = 1 := by
      have hm := (pow4_ge_four_and_mod3_w5 (Q - 1)).2
      rwa [show Q - 1 + 1 = Q by omega] at hm
    have h3Rn : 3 * R_n = 2 * 2 ^ (2 * Q + 1) - 1 := by
      dsimp [R_n]
      have h4_1 : 4 ^ (Q + 1) % 3 = 1 := by rw [Nat.pow_succ, Nat.mul_mod, h4_m3]
      have h4_eq : 4 ^ (Q + 1) = 2 * 2 ^ (2 * Q + 1) := by
        rw [Nat.pow_succ 4 Q, pow4_eq_pow2_even Q, Nat.pow_succ 2 (2 * Q)]; omega
      omega
    have hRn_lt : R_n < 2 ^ (2 * Q + 1) := by
      have hp := pow2_pos_nat (2 * Q + 1); omega
    rcases both_transducers_low_pad_peel hQ delta emit q0 1 (2 * Q) (2 * s)
      (by decide) (by omega) (2 * Q + 1) R_n q0 hRn_lt with ⟨_, hns_l, hns_m⟩
    simp only [Nat.mul_one] at hns_l hns_m
    have hns_rew : 2 ^ (2 * Q + 1) * 2 ^ (2 * Q + P * (2 * s)) + R_n =
        (2 * (3 * 4 ^ (2 * Q + P * s) + 2 ^ (2 * Q + 1)) - 1) / 3 := by
      have hdiv : (2 * (3 * 4 ^ (2 * Q + P * s) + 2 ^ (2 * Q + 1)) - 1) / 3 =
          2 * 4 ^ (2 * Q + P * s) + R_n := by
        have hp2 := pow2_pos_nat (2 * Q + 1)
        generalize 4 ^ (2 * Q + P * s) = p4u, 2 ^ (2 * Q + 1) = rm, R_n = rn at hp2 h3Rn ⊢
        omega
      rw [hdiv, ← Nat.pow_add 2 (2 * Q + 1),
          show 2 * Q + 1 + (2 * Q + P * (2 * s)) = 2 * (2 * Q + P * s) + 1 by rw [hP_2s]; omega,
          Nat.pow_succ, ← pow4_eq_pow2_even, Nat.mul_comm _ 2]
    have hn0_rew : 2 ^ (2 * Q + 1) * 2 ^ (2 * Q) + R_n =
        (2 * (3 * 4 ^ (2 * Q) + 2 ^ (2 * Q + 1)) - 1) / 3 := by
      have hdiv : (2 * (3 * 4 ^ (2 * Q) + 2 ^ (2 * Q + 1)) - 1) / 3 =
          2 * 4 ^ (2 * Q) + R_n := by
        have hp2 := pow2_pos_nat (2 * Q + 1)
        generalize 4 ^ (2 * Q) = p4u, 2 ^ (2 * Q + 1) = rm, R_n = rn at hp2 h3Rn ⊢
        omega
      rw [hdiv, ← Nat.pow_add 2 (2 * Q + 1) (2 * Q),
          show 2 * Q + 1 + 2 * Q = 2 * (2 * Q) + 1 by omega,
          Nat.pow_succ, ← pow4_eq_pow2_even, Nat.mul_comm _ 2]
    rw [hns_rew, hn0_rew] at hns_l hns_m
    exact ⟨hms_l, hevs_l, hns_l, hms_m, hevs_m, hns_m⟩
  have hpos_fac : ∀ x y : Nat, x * y > 0 -> x ≥ 1 ∧ y ≥ 1 := by
    intro x y h
    cases x with
    | zero => simp at h
    | succ _ =>
      cases y with
      | zero => simp at h
      | succ _ => exact ⟨by omega, by omega⟩
  refine ⟨htr_fam, ?_, ?_⟩
  · -- Part 2: Universal Joint LSB + MSB Positive-`0`-Cycle Mealy Transducer Impossibility:
    intro Q hQ deltaL deltaM emitL emitM q0L q0M hposL hposM fNum fDen pTerms qTerms pTheta qTheta hw
    let P := natFact Q
    have hP_pos : P ≥ 1 := natFact_pos Q
    let m0 := 3 * 4 ^ (2 * Q) + 2 ^ (2 * Q + 1)
    let ev0 := 2 ^ P * m0
    let n0 := (2 * m0 - 1) / 3
    let aE := fNum (runLSBAutomaton Q deltaL q0L m0) (runMSBAutomaton Q deltaM q0M m0)
    let bE := fDen (runLSBAutomaton Q deltaL q0L m0) (runMSBAutomaton Q deltaM q0M m0)
    let aO := fNum (runLSBAutomaton Q deltaL q0L n0) (runMSBAutomaton Q deltaM q0M n0)
    let bO := fDen (runLSBAutomaton Q deltaL q0L n0) (runMSBAutomaton Q deltaM q0M n0)
    have hm0_ge3 : m0 ≥ 3 := by
      have h4 := nat_pow_pos_of_pos 4 (by decide) (2 * Q)
      dsimp [m0]; generalize 4 ^ (2 * Q) = p4, 2 ^ (2 * Q + 1) = p2 at h4 ⊢; omega
    have hn0_ge3 : n0 ≥ 3 := by
      have h4 : 4 ^ (2 * Q) ≥ 16 := by
        simpa using nat_pow_mono_exp_pos 4 2 (2 * Q) (by decide) (by omega)
      dsimp [n0, m0]; generalize 4 ^ (2 * Q) = p4, 2 ^ (2 * Q + 1) = p2 at h4 ⊢; omega
    rcases hw.2.2.1 m0 hm0_ge3 with ⟨hnum_m0, hden_m0⟩
    rcases hw.2.2.1 n0 hn0_ge3 with ⟨hnum_n0, hden_n0⟩
    dsimp only at hnum_m0 hden_m0 hnum_n0 hden_n0
    have haE_pos : aE ≥ 1 := (hpos_fac _ _ hnum_m0).1
    have hbE_pos : bE ≥ 1 := (hpos_fac _ _ hden_m0).1
    have haO_pos : aO ≥ 1 := (hpos_fac _ _ hnum_n0).1
    have hbO_pos : bO ≥ 1 := (hpos_fac _ _ hden_n0).1
    let g0L := fun st => deltaL st false
    let e0L := fun st => emitL st false
    let g0M := fun st => deltaM st false
    let e0M := fun st => emitM st false
    let kL_m := sumIterFin g0L e0L P
      (iterFin g0L (2 * Q - 2) (runLSBFixedWidth deltaL (2 * Q + 2) q0L (2 ^ (2 * Q + 1))))
    let kL_n := sumIterFin g0L e0L P
      (iterFin g0L (2 * Q) (runLSBFixedWidth deltaL (2 * Q + 1) q0L ((4 ^ (Q + 1) - 1) / 3)))
    let kM_m := sumIterFin g0M e0M P
      (iterFin g0M (2 * Q - 2) (runMSBAutomaton Q deltaM q0M 3))
    let kM_n := sumIterFin g0M e0M P
      (iterFin g0M (2 * Q) (runMSBAutomaton Q deltaM q0M 1))
    have hkLm_pos : kL_m ≥ 1 := hposL _
    have hkLn_pos : kL_n ≥ 1 := hposL _
    have hkMm_pos : kM_m ≥ 1 := hposM _
    have hkMn_pos : kM_n ≥ 1 := hposM _
    let dP := maxDegNatPoly3 pTerms
    let dQ := maxDegNatPoly3 qTerms
    let D := dP + dQ
    let C := runLSBTransducerOut Q deltaL emitL q0L m0 +
             runLSBTransducerOut Q deltaL emitL q0L ev0 +
             runLSBTransducerOut Q deltaL emitL q0L n0 +
             runMSBTransducerOut Q deltaM emitM q0M m0 +
             runMSBTransducerOut Q deltaM emitM q0M ev0 +
             runMSBTransducerOut Q deltaM emitM q0M n0 +
             binBitLength m0 + binBitLength n0 + P + 2
    have hC_pos : C ≥ 1 := by dsimp [C]; omega
    let M_hi := 2 * (kL_m + kL_n + kM_m + kM_n + P) + C
    have hMhi_ge2 : M_hi ≥ 2 := by dsimp [M_hi]; omega
    let B_eff := (aE * bO) * M_hi ^ D
    let A_eff := (aO * bE) * 2 ^ D
    have hBeff_pos : B_eff ≥ 1 :=
      Nat.mul_le_mul (Nat.mul_le_mul haE_pos hbO_pos) (nat_pow_pos_of_pos M_hi (by omega) D)
    have hAeff_pos : A_eff ≥ 1 :=
      Nat.mul_le_mul (Nat.mul_le_mul haO_pos hbE_pos) (pow2_pos_nat D)
    let s := (B_eff + A_eff + 1) * (D * C + 1) + 1
    have hs_pos : s ≥ 1 := by dsimp [s]; omega
    let X := 2 * s
    have hX_ge : X ≥ (B_eff + A_eff + 1) * (D * C + 1) := by dsimp [X, s]; omega
    rcases berg_meinardus_stateful_automaton_preimage_impossibility.1 Q s hQ with
      ⟨hms_m3, haut, _, _, _, hbl_ms, hbl_evs, hbl_ns⟩
    rcases haut deltaL q0L with ⟨hl_ms, hl_evs, hl_ns, _, _, _⟩
    rcases haut deltaM q0M with ⟨_, _, _, hm_ms, hm_evs, hm_ns⟩
    rcases htr_fam Q s hQ deltaL emitL q0L with ⟨htL_ms, htL_evs, htL_ns, _, _, _⟩
    rcases htr_fam Q s hQ deltaM emitM q0M with ⟨_, _, _, htM_ms, htM_evs, htM_ns⟩
    let ms := 3 * 4 ^ (2 * Q + P * s) + 2 ^ (2 * Q + 1)
    let evs := 2 ^ P * ms
    let ns := (2 * ms - 1) / 3
    have hms_ge3 : ms ≥ 3 := by
      have h4 := nat_pow_pos_of_pos 4 (by decide) (2 * Q + P * s)
      dsimp [ms]; generalize 4 ^ (2 * Q + P * s) = p4, 2 ^ (2 * Q + 1) = p2 at h4 ⊢; omega
    have hns_ge3 : ns ≥ 3 := by
      have h4 : 4 ^ (2 * Q + P * s) ≥ 16 := by
        simpa using nat_pow_mono_exp_pos 4 2 (2 * Q + P * s) (by decide) (by omega)
      dsimp [ns, ms]; generalize 4 ^ (2 * Q + P * s) = p4, 2 ^ (2 * Q + 1) = p2 at h4 ⊢; omega
    have hevs_ge3 : evs ≥ 3 := by
      dsimp [evs]; simpa using Nat.mul_le_mul (pow2_pos_nat P) hms_ge3
    have hcanc := preimage_multistep_even_branch_ineq
      (fun n =>
        fNum (runLSBAutomaton Q deltaL q0L n) (runMSBAutomaton Q deltaM q0M n) *
          evalNatPoly3 pTerms
            (runLSBTransducerOut Q deltaL emitL q0L n)
            (runMSBTransducerOut Q deltaM emitM q0M n)
            (binBitLength n))
      (fun n =>
        fDen (runLSBAutomaton Q deltaL q0L n) (runMSBAutomaton Q deltaM q0M n) *
          evalNatPoly3 qTerms
            (runLSBTransducerOut Q deltaL emitL q0L n)
            (runMSBTransducerOut Q deltaM emitM q0M n)
            (binBitLength n))
      pTheta qTheta ms P hw hms_ge3 hms_m3 hP_pos
    dsimp only at hcanc
    change ((fNum (runLSBAutomaton Q deltaL q0L evs) (runMSBAutomaton Q deltaM q0M evs) *
              evalNatPoly3 pTerms (runLSBTransducerOut Q deltaL emitL q0L evs)
                (runMSBTransducerOut Q deltaM emitM q0M evs) (binBitLength evs)) *
            (fDen (runLSBAutomaton Q deltaL q0L ns) (runMSBAutomaton Q deltaM q0M ns) *
              evalNatPoly3 qTerms (runLSBTransducerOut Q deltaL emitL q0L ns)
                (runMSBTransducerOut Q deltaM emitM q0M ns) (binBitLength ns)) +
            (fNum (runLSBAutomaton Q deltaL q0L ns) (runMSBAutomaton Q deltaM q0M ns) *
              evalNatPoly3 pTerms (runLSBTransducerOut Q deltaL emitL q0L ns)
                (runMSBTransducerOut Q deltaM emitM q0M ns) (binBitLength ns)) *
            (fDen (runLSBAutomaton Q deltaL q0L evs) (runMSBAutomaton Q deltaM q0M evs) *
              evalNatPoly3 qTerms (runLSBTransducerOut Q deltaL emitL q0L evs)
                (runMSBTransducerOut Q deltaM emitM q0M evs) (binBitLength evs))) *
          (fDen (runLSBAutomaton Q deltaL q0L ms) (runMSBAutomaton Q deltaM q0M ms) *
            evalNatPoly3 qTerms (runLSBTransducerOut Q deltaL emitL q0L ms)
              (runMSBTransducerOut Q deltaM emitM q0M ms) (binBitLength ms)) ≤
      (fNum (runLSBAutomaton Q deltaL q0L ms) (runMSBAutomaton Q deltaM q0M ms) *
        evalNatPoly3 pTerms (runLSBTransducerOut Q deltaL emitL q0L ms)
          (runMSBTransducerOut Q deltaM emitM q0M ms) (binBitLength ms)) *
      ((fDen (runLSBAutomaton Q deltaL q0L evs) (runMSBAutomaton Q deltaM q0M evs) *
          evalNatPoly3 qTerms (runLSBTransducerOut Q deltaL emitL q0L evs)
            (runMSBTransducerOut Q deltaM emitM q0M evs) (binBitLength evs)) *
        (fDen (runLSBAutomaton Q deltaL q0L ns) (runMSBAutomaton Q deltaM q0M ns) *
          evalNatPoly3 qTerms (runLSBTransducerOut Q deltaL emitL q0L ns)
            (runMSBTransducerOut Q deltaM emitM q0M ns) (binBitLength ns))) at hcanc
    rw [hl_ms, hl_evs, hl_ns, hm_ms, hm_evs, hm_ns] at hcanc
    let P_m := evalNatPoly3 pTerms (runLSBTransducerOut Q deltaL emitL q0L ms)
      (runMSBTransducerOut Q deltaM emitM q0M ms) (binBitLength ms)
    let Q_m := evalNatPoly3 qTerms (runLSBTransducerOut Q deltaL emitL q0L ms)
      (runMSBTransducerOut Q deltaM emitM q0M ms) (binBitLength ms)
    let P_ev := evalNatPoly3 pTerms (runLSBTransducerOut Q deltaL emitL q0L evs)
      (runMSBTransducerOut Q deltaM emitM q0M evs) (binBitLength evs)
    let Q_ev := evalNatPoly3 qTerms (runLSBTransducerOut Q deltaL emitL q0L evs)
      (runMSBTransducerOut Q deltaM emitM q0M evs) (binBitLength evs)
    let P_n := evalNatPoly3 pTerms (runLSBTransducerOut Q deltaL emitL q0L ns)
      (runMSBTransducerOut Q deltaM emitM q0M ns) (binBitLength ns)
    let Q_n := evalNatPoly3 qTerms (runLSBTransducerOut Q deltaL emitL q0L ns)
      (runMSBTransducerOut Q deltaM emitM q0M ns) (binBitLength ns)
    change ((aE * P_ev) * (bO * Q_n) + (aO * P_n) * (bE * Q_ev)) * (bE * Q_m) ≤
      (aE * P_m) * ((bE * Q_ev) * (bO * Q_n)) at hcanc
    rcases hw.2.2.1 ms hms_ge3 with ⟨hnum_ms, _⟩
    rcases hw.2.2.1 evs hevs_ge3 with ⟨_, hden_evs⟩
    rcases hw.2.2.1 ns hns_ge3 with ⟨_, hden_ns⟩
    dsimp only at hnum_ms hden_evs hden_ns
    have hPm_pos : P_m ≥ 1 := (hpos_fac _ _ hnum_ms).2
    have hQev_pos : Q_ev ≥ 1 := (hpos_fac _ _ hden_evs).2
    have hQn_pos : Q_n ≥ 1 := (hpos_fac _ _ hden_ns).2
    -- Cross-ratio helper for same-slope affine coordinates `2 * s * k + c`:
    have hsame_slope : ∀ (k c1 c2 : Nat), k ≥ 1 -> c1 ≤ C ->
        X * (2 * s * k + c1) ≤ (X + C) * (2 * s * k + c2) := by
      intro k c1 c2 hk hc1
      dsimp [X]
      have hkc : c1 ≤ k * C := Nat.le_trans hc1 (by simpa using Nat.mul_le_mul_right C hk)
      calc
        (2 * s) * (2 * s * k + c1)
            = (2 * s) * (2 * s * k) + (2 * s) * c1 := Nat.mul_add _ _ _
        _ ≤ (2 * s) * (2 * s * k) + C * (2 * s * k) := by
              apply Nat.add_le_add_left
              have hm := Nat.mul_le_mul_left (2 * s) hkc
              have hr : (2 * s) * (k * C) = C * (2 * s * k) := by
                rw [← Nat.mul_assoc (2 * s) k C, Nat.mul_comm (2 * s * k) C]
              rwa [hr] at hm
        _ = (2 * s + C) * (2 * s * k) := (Nat.add_mul (2 * s) C (2 * s * k)).symm
        _ ≤ (2 * s + C) * (2 * s * k + c2) := Nat.mul_le_mul_left (2 * s + C) (by omega)
    -- Cross-ratio helper for distinct positive slopes `2 * s ≤ 2 * s * k + c ≤ M_hi * s`:
    have hdiff_slope : ∀ (k1 c1 k2 c2 : Nat),
        k2 ≥ 1 -> 2 * k1 + C ≤ M_hi -> c1 ≤ C ->
        2 * (2 * s * k1 + c1) ≤ M_hi * (2 * s * k2 + c2) := by
      intro k1 c1 k2 c2 hk2 hk_hi hc1
      have hlo : 2 * s ≤ 2 * s * k2 + c2 := by
        have hm : 2 * s * 1 ≤ 2 * s * k2 := Nat.mul_le_mul_left (2 * s) hk2
        omega
      have hhi : 2 * s * k1 + c1 ≤ M_hi * s := by
        have hc_s : c1 ≤ C * s :=
          Nat.le_trans hc1 (by simpa using Nat.mul_le_mul_left C hs_pos)
        calc
          2 * s * k1 + c1
              ≤ (2 * k1) * s + C * s := by
                rw [Nat.mul_assoc 2 s k1, Nat.mul_comm s k1, ← Nat.mul_assoc 2 k1 s]
                exact Nat.add_le_add_left hc_s _
          _ = (2 * k1 + C) * s := (Nat.add_mul (2 * k1) C s).symm
          _ ≤ M_hi * s := Nat.mul_le_mul_right s hk_hi
      calc
        2 * (2 * s * k1 + c1)
            ≤ 2 * (M_hi * s) := Nat.mul_le_mul_left 2 hhi
        _ = M_hi * (2 * s) := by rw [← Nat.mul_assoc 2 M_hi s, Nat.mul_comm 2 M_hi, Nat.mul_assoc]
        _ ≤ M_hi * (2 * s * k2 + c2) := Nat.mul_le_mul_left M_hi hlo
    have hbl_ms_f : binBitLength ms = 2 * s * P + binBitLength m0 := by
      rw [hbl_ms]; rw [Nat.mul_assoc 2 P s, Nat.mul_comm P s, ← Nat.mul_assoc 2 s P]
    have hbl_evs_f : binBitLength evs = 2 * s * P + (P + binBitLength m0) := by
      rw [hbl_evs]; rw [Nat.mul_assoc 2 P s, Nat.mul_comm P s, ← Nat.mul_assoc 2 s P, Nat.add_assoc]
    have hbl_ns_f : binBitLength ns = 2 * s * P + binBitLength n0 := by
      rw [hbl_ns]; rw [Nat.mul_assoc 2 P s, Nat.mul_comm P s, ← Nat.mul_assoc 2 s P]
    have hPm_Pev : X ^ dP * P_m ≤ (X + C) ^ dP * P_ev := by
      dsimp [P_m, P_ev]
      apply evalNatPoly3_cross_ratio_bound pTerms X (X + C) _ _ _ _ _ _ (by omega)
      · change X * runLSBTransducerOut Q deltaL emitL q0L ms ≤
          (X + C) * runLSBTransducerOut Q deltaL emitL q0L evs
        rw [htL_ms, htL_evs]
        exact hsame_slope kL_m _ _ hkLm_pos (by dsimp [C, ev0, m0, n0, P]; omega)
      · change X * runMSBTransducerOut Q deltaM emitM q0M ms ≤
          (X + C) * runMSBTransducerOut Q deltaM emitM q0M evs
        rw [htM_ms, htM_evs]
        exact hsame_slope kM_m _ _ hkMm_pos (by dsimp [C, ev0, m0, n0, P]; omega)
      · rw [hbl_ms_f, hbl_evs_f]
        exact hsame_slope P _ _ hP_pos (by dsimp [C, ev0, m0, n0, P]; omega)
    have hQev_Qm : X ^ dQ * Q_ev ≤ (X + C) ^ dQ * Q_m := by
      dsimp [Q_ev, Q_m]
      apply evalNatPoly3_cross_ratio_bound qTerms X (X + C) _ _ _ _ _ _ (by omega)
      · change X * runLSBTransducerOut Q deltaL emitL q0L evs ≤
          (X + C) * runLSBTransducerOut Q deltaL emitL q0L ms
        rw [htL_evs, htL_ms]
        exact hsame_slope kL_m _ _ hkLm_pos (by dsimp [C, ev0, m0, n0, P]; omega)
      · change X * runMSBTransducerOut Q deltaM emitM q0M evs ≤
          (X + C) * runMSBTransducerOut Q deltaM emitM q0M ms
        rw [htM_evs, htM_ms]
        exact hsame_slope kM_m _ _ hkMm_pos (by dsimp [C, ev0, m0, n0, P]; omega)
      · rw [hbl_evs_f, hbl_ms_f]
        exact hsame_slope P _ _ hP_pos (by dsimp [C, ev0, m0, n0, P]; omega)
    have hPm_Pn : 2 ^ dP * P_m ≤ M_hi ^ dP * P_n := by
      dsimp [P_m, P_n]
      apply evalNatPoly3_cross_ratio_bound pTerms 2 M_hi _ _ _ _ _ _ hMhi_ge2
      · change 2 * runLSBTransducerOut Q deltaL emitL q0L ms ≤
          M_hi * runLSBTransducerOut Q deltaL emitL q0L ns
        rw [htL_ms, htL_ns]
        exact hdiff_slope kL_m _ kL_n _ hkLn_pos (by dsimp [M_hi]; omega) (by dsimp [C, ev0, m0, n0, P]; omega)
      · change 2 * runMSBTransducerOut Q deltaM emitM q0M ms ≤
          M_hi * runMSBTransducerOut Q deltaM emitM q0M ns
        rw [htM_ms, htM_ns]
        exact hdiff_slope kM_m _ kM_n _ hkMn_pos (by dsimp [M_hi]; omega) (by dsimp [C, ev0, m0, n0, P]; omega)
      · rw [hbl_ms_f, hbl_ns_f]
        exact hdiff_slope P _ P _ hP_pos (by dsimp [M_hi]; omega) (by dsimp [C, ev0, m0, n0, P]; omega)
    have hQn_Qm : 2 ^ dQ * Q_n ≤ M_hi ^ dQ * Q_m := by
      dsimp [Q_n, Q_m]
      apply evalNatPoly3_cross_ratio_bound qTerms 2 M_hi _ _ _ _ _ _ hMhi_ge2
      · change 2 * runLSBTransducerOut Q deltaL emitL q0L ns ≤
          M_hi * runLSBTransducerOut Q deltaL emitL q0L ms
        rw [htL_ns, htL_ms]
        exact hdiff_slope kL_n _ kL_m _ hkLm_pos (by dsimp [M_hi]; omega) (by dsimp [C, ev0, m0, n0, P]; omega)
      · change 2 * runMSBTransducerOut Q deltaM emitM q0M ns ≤
          M_hi * runMSBTransducerOut Q deltaM emitM q0M ms
        rw [htM_ns, htM_ms]
        exact hdiff_slope kM_n _ kM_m _ hkMm_pos (by dsimp [M_hi]; omega) (by dsimp [C, ev0, m0, n0, P]; omega)
      · rw [hbl_ns_f, hbl_ms_f]
        exact hdiff_slope P _ P _ hP_pos (by dsimp [M_hi]; omega) (by dsimp [C, ev0, m0, n0, P]; omega)
    let K_den := bE * (P_m * (Q_ev * Q_n))
    have hK_pos : K_den ≥ 1 :=
      Nat.mul_le_mul hbE_pos (Nat.mul_le_mul hPm_pos (Nat.mul_le_mul hQev_pos hQn_pos))
    have hrhs_f : (aE * P_m) * ((bE * Q_ev) * (bO * Q_n)) = (aE * bO) * K_den := by
      dsimp [K_den]
      calc
        (aE * P_m) * ((bE * Q_ev) * (bO * Q_n))
            = aE * (P_m * ((bE * bO) * (Q_ev * Q_n))) := by
              have hmid : (bE * Q_ev) * (bO * Q_n) = (bE * bO) * (Q_ev * Q_n) := by
                rw [Nat.mul_assoc bE Q_ev, ← Nat.mul_assoc Q_ev bO Q_n,
                    Nat.mul_comm Q_ev bO, Nat.mul_assoc bO Q_ev Q_n, ← Nat.mul_assoc bE bO]
              rw [hmid, Nat.mul_assoc aE P_m]
        _ = (aE * bO) * (bE * (P_m * (Q_ev * Q_n))) := by
              have hinner : P_m * ((bE * bO) * (Q_ev * Q_n)) = bO * (bE * (P_m * (Q_ev * Q_n))) := by
                rw [Nat.mul_comm bE bO, Nat.mul_assoc bO bE (Q_ev * Q_n),
                    ← Nat.mul_assoc P_m bO (bE * (Q_ev * Q_n)),
                    Nat.mul_comm P_m bO, Nat.mul_assoc bO P_m (bE * (Q_ev * Q_n)),
                    ← Nat.mul_assoc P_m bE (Q_ev * Q_n), Nat.mul_comm P_m bE,
                    Nat.mul_assoc bE P_m (Q_ev * Q_n)]
              rw [hinner, ← Nat.mul_assoc aE bO]
    have hbr1 : B_eff * X ^ D * K_den ≤
        (M_hi ^ D * (X + C) ^ D) * (((aE * P_ev) * (bO * Q_n)) * (bE * Q_m)) := by
      have hm := Nat.mul_le_mul_left B_eff
        (Nat.mul_le_mul_right (bE * Q_n) (Nat.mul_le_mul hPm_Pev hQev_Qm))
      have hl : B_eff * ((X ^ dP * P_m * (X ^ dQ * Q_ev)) * (bE * Q_n)) = B_eff * X ^ D * K_den := by
        dsimp [D, K_den]
        rw [Nat.pow_add X dP dQ, Nat.mul_assoc B_eff]
        apply congrArg (B_eff * ·)
        calc
          (X ^ dP * P_m * (X ^ dQ * Q_ev)) * (bE * Q_n)
              = (X ^ dP * X ^ dQ) * (P_m * Q_ev) * (bE * Q_n) := by
                rw [← Nat.mul_assoc (X ^ dP * P_m), Nat.mul_assoc (X ^ dP) P_m (X ^ dQ),
                    Nat.mul_comm P_m (X ^ dQ), ← Nat.mul_assoc (X ^ dP) (X ^ dQ) P_m,
                    Nat.mul_assoc (X ^ dP * X ^ dQ) P_m Q_ev]
          _ = (X ^ dP * X ^ dQ) * (bE * (P_m * (Q_ev * Q_n))) := by
                rw [Nat.mul_assoc (X ^ dP * X ^ dQ)]
                apply congrArg ((X ^ dP * X ^ dQ) * ·)
                rw [← Nat.mul_assoc (P_m * Q_ev) bE Q_n, Nat.mul_comm (P_m * Q_ev) bE,
                    Nat.mul_assoc bE (P_m * Q_ev) Q_n, Nat.mul_assoc P_m Q_ev Q_n]
      have hr : B_eff * (((X + C) ^ dP * P_ev * ((X + C) ^ dQ * Q_m)) * (bE * Q_n)) =
          (M_hi ^ D * (X + C) ^ D) * (((aE * P_ev) * (bO * Q_n)) * (bE * Q_m)) := by
        dsimp [D, B_eff]
        rw [Nat.pow_add (X + C) dP dQ]
        calc
          ((aE * bO) * M_hi ^ (dP + dQ)) * (((X + C) ^ dP * P_ev * ((X + C) ^ dQ * Q_m)) * (bE * Q_n))
              = (aE * bO) * (M_hi ^ (dP + dQ) * (((X + C) ^ dP * (X + C) ^ dQ) * (P_ev * Q_m * (bE * Q_n)))) := by
                rw [Nat.mul_assoc (aE * bO)]
                apply congrArg ((aE * bO) * ·)
                apply congrArg (M_hi ^ (dP + dQ) * ·)
                rw [← Nat.mul_assoc ((X + C) ^ dP * P_ev),
                    Nat.mul_assoc ((X + C) ^ dP) P_ev ((X + C) ^ dQ),
                    Nat.mul_comm P_ev ((X + C) ^ dQ),
                    ← Nat.mul_assoc ((X + C) ^ dP) ((X + C) ^ dQ) P_ev,
                    Nat.mul_assoc ((X + C) ^ dP * (X + C) ^ dQ) P_ev Q_m,
                    Nat.mul_assoc ((X + C) ^ dP * (X + C) ^ dQ)]
          _ = (M_hi ^ (dP + dQ) * ((X + C) ^ dP * (X + C) ^ dQ)) * ((aE * bO) * (P_ev * Q_m * (bE * Q_n))) := by
                rw [← Nat.mul_assoc (M_hi ^ (dP + dQ)),
                    ← Nat.mul_assoc (aE * bO),
                    Nat.mul_comm (aE * bO) (M_hi ^ (dP + dQ) * ((X + C) ^ dP * (X + C) ^ dQ)),
                    Nat.mul_assoc]
          _ = (M_hi ^ (dP + dQ) * ((X + C) ^ dP * (X + C) ^ dQ)) * (((aE * P_ev) * (bO * Q_n)) * (bE * Q_m)) := by
                apply congrArg ((M_hi ^ (dP + dQ) * ((X + C) ^ dP * (X + C) ^ dQ)) * ·)
                have h1 : P_ev * Q_m * (bE * Q_n) = P_ev * Q_n * (bE * Q_m) := by
                  rw [Nat.mul_assoc P_ev Q_m, ← Nat.mul_assoc Q_m bE Q_n,
                      Nat.mul_comm (Q_m * bE) Q_n, Nat.mul_comm Q_m bE,
                      ← Nat.mul_assoc P_ev Q_n]
                have h2 : (aE * bO) * (P_ev * Q_n) = (aE * P_ev) * (bO * Q_n) := by
                  rw [Nat.mul_assoc aE bO, ← Nat.mul_assoc bO P_ev Q_n,
                      Nat.mul_comm bO P_ev, Nat.mul_assoc P_ev bO Q_n, ← Nat.mul_assoc aE P_ev]
                rw [h1, ← Nat.mul_assoc (aE * bO) (P_ev * Q_n), h2]
      rwa [hl, hr] at hm
    have hXD_le : X ^ D ≤ (X + C) ^ D := by
      have hm : ∀ k : Nat, X ^ k ≤ (X + C) ^ k := by
        intro k; induction k with
        | zero => exact Nat.le_refl 1
        | succ k' ih => rw [Nat.pow_succ, Nat.pow_succ]; exact Nat.mul_le_mul ih (by omega)
      exact hm D
    have hbr2 : A_eff * X ^ D * K_den ≤
        (M_hi ^ D * (X + C) ^ D) * (((aO * P_n) * (bE * Q_ev)) * (bE * Q_m)) := by
      have hm_base := Nat.mul_le_mul_left (aO * bE)
        (Nat.mul_le_mul_right (bE * Q_ev) (Nat.mul_le_mul hPm_Pn hQn_Qm))
      have hl : (aO * bE) * ((2 ^ dP * P_m * (2 ^ dQ * Q_n)) * (bE * Q_ev)) = A_eff * K_den := by
        dsimp [D, A_eff, K_den]
        rw [Nat.pow_add 2 dP dQ, Nat.mul_assoc (aO * bE)]
        apply congrArg ((aO * bE) * ·)
        calc
          (2 ^ dP * P_m * (2 ^ dQ * Q_n)) * (bE * Q_ev)
              = (2 ^ dP * 2 ^ dQ) * (P_m * Q_n) * (bE * Q_ev) := by
                rw [← Nat.mul_assoc (2 ^ dP * P_m), Nat.mul_assoc (2 ^ dP) P_m (2 ^ dQ),
                    Nat.mul_comm P_m (2 ^ dQ), ← Nat.mul_assoc (2 ^ dP) (2 ^ dQ) P_m,
                    Nat.mul_assoc (2 ^ dP * 2 ^ dQ) P_m Q_n]
          _ = (2 ^ dP * 2 ^ dQ) * (bE * (P_m * (Q_ev * Q_n))) := by
                rw [Nat.mul_assoc (2 ^ dP * 2 ^ dQ)]
                apply congrArg ((2 ^ dP * 2 ^ dQ) * ·)
                rw [← Nat.mul_assoc (P_m * Q_n) bE Q_ev, Nat.mul_comm (P_m * Q_n) bE,
                    Nat.mul_assoc bE (P_m * Q_n) Q_ev, Nat.mul_assoc P_m Q_n Q_ev,
                    Nat.mul_comm Q_n Q_ev]
      have hr : (aO * bE) * (((M_hi ^ dP * P_n) * (M_hi ^ dQ * Q_m)) * (bE * Q_ev)) =
          M_hi ^ D * (((aO * P_n) * (bE * Q_ev)) * (bE * Q_m)) := by
        dsimp [D]
        rw [Nat.pow_add M_hi dP dQ]
        calc
          (aO * bE) * (((M_hi ^ dP * P_n) * (M_hi ^ dQ * Q_m)) * (bE * Q_ev))
              = (aO * bE) * ((M_hi ^ dP * M_hi ^ dQ) * (P_n * Q_m * (bE * Q_ev))) := by
                apply congrArg ((aO * bE) * ·)
                rw [← Nat.mul_assoc (M_hi ^ dP * P_n),
                    Nat.mul_assoc (M_hi ^ dP) P_n (M_hi ^ dQ),
                    Nat.mul_comm P_n (M_hi ^ dQ),
                    ← Nat.mul_assoc (M_hi ^ dP) (M_hi ^ dQ) P_n,
                    Nat.mul_assoc (M_hi ^ dP * M_hi ^ dQ) P_n Q_m,
                    Nat.mul_assoc (M_hi ^ dP * M_hi ^ dQ)]
          _ = (M_hi ^ dP * M_hi ^ dQ) * ((aO * bE) * (P_n * Q_m * (bE * Q_ev))) := by
                rw [← Nat.mul_assoc (aO * bE), Nat.mul_comm (aO * bE) (M_hi ^ dP * M_hi ^ dQ),
                    Nat.mul_assoc]
          _ = (M_hi ^ dP * M_hi ^ dQ) * (((aO * P_n) * (bE * Q_ev)) * (bE * Q_m)) := by
                apply congrArg ((M_hi ^ dP * M_hi ^ dQ) * ·)
                have h1 : P_n * Q_m * (bE * Q_ev) = P_n * (bE * Q_ev) * Q_m := by
                  rw [Nat.mul_assoc P_n Q_m, Nat.mul_comm Q_m (bE * Q_ev), ← Nat.mul_assoc P_n]
                have ha : aO * bE * P_n = aO * P_n * bE := by
                  rw [Nat.mul_assoc aO bE P_n, Nat.mul_comm bE P_n, ← Nat.mul_assoc aO P_n bE]
                have hb : bE * (bE * Q_ev) * Q_m = (bE * Q_ev) * (bE * Q_m) := by
                  rw [Nat.mul_comm bE (bE * Q_ev), Nat.mul_assoc (bE * Q_ev) bE Q_m]
                rw [h1, ← Nat.mul_assoc (aO * bE) (P_n * (bE * Q_ev)) Q_m,
                    ← Nat.mul_assoc (aO * bE) P_n (bE * Q_ev), ha,
                    Nat.mul_assoc (aO * P_n) bE (bE * Q_ev),
                    Nat.mul_assoc (aO * P_n) (bE * (bE * Q_ev)) Q_m,
                    hb, ← Nat.mul_assoc (aO * P_n) (bE * Q_ev) (bE * Q_m)]
      rw [hl, hr] at hm_base
      calc
        A_eff * X ^ D * K_den
            ≤ A_eff * (X + C) ^ D * K_den :=
              Nat.mul_le_mul_right K_den (Nat.mul_le_mul_left A_eff hXD_le)
        _ = (X + C) ^ D * (A_eff * K_den) := by
              rw [Nat.mul_comm A_eff ((X + C) ^ D), Nat.mul_assoc]
        _ ≤ (X + C) ^ D * (M_hi ^ D * (((aO * P_n) * (bE * Q_ev)) * (bE * Q_m))) :=
              Nat.mul_le_mul_left ((X + C) ^ D) hm_base
        _ = (M_hi ^ D * (X + C) ^ D) * (((aO * P_n) * (bE * Q_ev)) * (bE * Q_m)) := by
              rw [← Nat.mul_assoc ((X + C) ^ D) (M_hi ^ D), Nat.mul_comm ((X + C) ^ D) (M_hi ^ D)]
    have hsum := Nat.add_le_add hbr1 hbr2
    rw [← Nat.add_mul (B_eff * X ^ D) (A_eff * X ^ D) K_den,
        ← Nat.add_mul B_eff A_eff (X ^ D),
        ← Nat.mul_add (M_hi ^ D * (X + C) ^ D),
        ← Nat.add_mul ((aE * P_ev) * (bO * Q_n)) ((aO * P_n) * (bE * Q_ev)) (bE * Q_m)] at hsum
    have htot : ((B_eff + A_eff) * X ^ D) * K_den ≤ (B_eff * (X + C) ^ D) * K_den := by
      have hm := Nat.mul_le_mul_left (M_hi ^ D * (X + C) ^ D) hcanc
      have hr : (M_hi ^ D * (X + C) ^ D) * ((aE * bO) * K_den) = (B_eff * (X + C) ^ D) * K_den := by
        dsimp [B_eff]
        rw [← Nat.mul_assoc (M_hi ^ D * (X + C) ^ D) (aE * bO) K_den]
        apply congrArg (· * K_den)
        rw [Nat.mul_comm (M_hi ^ D) ((X + C) ^ D), Nat.mul_assoc ((X + C) ^ D) (M_hi ^ D) (aE * bO),
            Nat.mul_comm (M_hi ^ D) (aE * bO), Nat.mul_comm ((X + C) ^ D) ((aE * bO) * M_hi ^ D)]
      rw [hrhs_f, hr] at hm
      exact Nat.le_trans hsum hm
    have hle_b := nat_mul_le_cancel_right_w5 K_den _ _ hK_pos htot
    have hlt_b := bernoulli_nat_ratio_lt A_eff B_eff D C X hAeff_pos hBeff_pos hC_pos hX_ge
    omega
  · -- Part 3: Universal Positive-`1`-Cycle MSB Mealy Transducer Impossibility via Mersenne `1`-Spines:
    intro Q hQ deltaM emitM q0M hpos1 pTerms qTerms pTheta qTheta hw
    let P := natFact Q
    have hP_pos : P ≥ 1 := natFact_pos Q
    let g1 := fun st => deltaM st true
    let e1 := fun st => emitM st true
    let q_m0 := iterFin g1 (2 * Q) (runMSBAutomaton Q deltaM q0M 2)
    let q_n0 := iterFin g1 (2 * Q) (runMSBAutomaton Q deltaM q0M 1)
    let k1_m := sumIterFin g1 e1 P q_m0
    let k1_n := sumIterFin g1 e1 P q_n0
    have hk1m_pos : k1_m ≥ 1 := hpos1 _
    have hk1n_pos : k1_n ≥ 1 := hpos1 _
    let c1_m := runMSBTransducerOut Q deltaM emitM q0M 2 +
      sumIterFin g1 e1 (2 * Q) (runMSBAutomaton Q deltaM q0M 2)
    let c1_ev := c1_m + emitM q_m0 false
    let c1_n := runMSBTransducerOut Q deltaM emitM q0M 1 +
      sumIterFin g1 e1 (2 * Q) (runMSBAutomaton Q deltaM q0M 1)
    let dP := maxDegNatPoly2 pTerms
    let dQ := maxDegNatPoly2 qTerms
    let D := dP + dQ
    let C := c1_m + c1_ev + c1_n + 2 * Q + 5
    have hC_pos : C ≥ 1 := by dsimp [C]; omega
    let M_hi := k1_m + k1_n + P + C
    have hMhi_ge1 : M_hi ≥ 1 := by dsimp [M_hi]; omega
    let B_eff := M_hi ^ D
    have hBeff_pos : B_eff ≥ 1 := nat_pow_pos_of_pos M_hi hMhi_ge1 D
    let s := (B_eff + 1 + 1) * (D * C + 1) + 1
    have hs_pos : s ≥ 1 := by dsimp [s]; omega
    have hs_ge : s ≥ (B_eff + 1 + 1) * (D * C + 1) := by dsimp [s]; omega
    let d_s := 2 * Q + P * s
    let ms1 := 3 * 2 ^ d_s - 1
    let evs1 := 2 * ms1
    let ns1 := 2 ^ (d_s + 1) - 1
    have hds_ge2 : d_s ≥ 2 := by dsimp [d_s]; omega
    have hp2_ge4 : 2 ^ d_s ≥ 4 := by simpa using pow2_mono_nat hds_ge2
    have hms1_ge3 : ms1 ≥ 3 := by dsimp [ms1]; omega
    have hevs1_ge3 : evs1 ≥ 3 := by dsimp [evs1]; omega
    have hns1_ge3 : ns1 ≥ 3 := by dsimp [ns1]; rw [Nat.pow_succ]; omega
    rcases ripple_carry_alternating_cascade_and_mersenne_triples.2.2 (d_s + 1) (by omega) with
      ⟨hms1_m3_raw, hns1_div_raw, _, _, _, hbl_n_raw, hbl_m_raw, hbl_ev_raw⟩
    have hm_simp : 3 * 2 ^ (d_s + 1 - 1) - 1 = ms1 := by
      rw [show d_s + 1 - 1 = d_s by omega]
    rw [hm_simp] at hms1_m3_raw hns1_div_raw hbl_m_raw hbl_ev_raw
    -- Exact MSB transducer affine formulas along `ms1`, `evs1`, `ns1`:
    have hm1_val : 2 ^ d_s * 2 + (2 ^ d_s - 1) = ms1 := by
      dsimp [ms1]; have hp := pow2_pos_nat d_s; generalize 2 ^ d_s = p2 at hp ⊢; omega
    have hn1_val : 2 ^ d_s * 1 + (2 ^ d_s - 1) = ns1 := by
      dsimp [ns1]; rw [Nat.pow_succ]; have hp := pow2_pos_nat d_s; generalize 2 ^ d_s = p2 at hp ⊢; omega
    rcases runMSBAutomaton_and_transducer_mersenne_tail deltaM emitM q0M 2 (by decide) d_s with
      ⟨hst_ms1, hout_ms1⟩
    rcases runMSBAutomaton_and_transducer_mersenne_tail deltaM emitM q0M 1 (by decide) d_s with
      ⟨_, hout_ns1⟩
    rw [hm1_val] at hst_ms1 hout_ms1
    rw [hn1_val] at hout_ns1
    rcases fin_unary_iter_and_sum_period_sub1 hQ g1 e1 (runMSBAutomaton Q deltaM q0M 2)
      s (2 * Q) (by omega) with ⟨hit1_m, hsum1_m⟩
    rcases fin_unary_iter_and_sum_period_sub1 hQ g1 e1 (runMSBAutomaton Q deltaM q0M 1)
      s (2 * Q) (by omega) with ⟨_, hsum1_n⟩
    have hout_ms1_eq : runMSBTransducerOut Q deltaM emitM q0M ms1 = s * k1_m + c1_m := by
      change runMSBTransducerOut Q deltaM emitM q0M ms1 = s * k1_m + c1_m
      rw [hout_ms1]
      change runMSBTransducerOut Q deltaM emitM q0M 2 +
          sumIterFin g1 e1 (2 * Q + natFact Q * s) (runMSBAutomaton Q deltaM q0M 2) = _
      rw [hsum1_m]; dsimp [k1_m, c1_m, q_m0, P]; omega
    have hout_evs1_eq : runMSBTransducerOut Q deltaM emitM q0M evs1 = s * k1_m + c1_ev := by
      dsimp [evs1]
      rw [runMSBTransducerOut_step_pos deltaM emitM q0M (2 * ms1) (by omega),
          show ((2 * ms1) % 2 == 1) = false by rw [Nat.mul_mod_right]; rfl,
          show (2 * ms1) / 2 = ms1 by omega,
          hout_ms1_eq, hst_ms1]
      change (s * k1_m + c1_m) +
          emitM (iterFin g1 (2 * Q + natFact Q * s) (runMSBAutomaton Q deltaM q0M 2)) false = _
      rw [hit1_m]; dsimp [c1_ev, q_m0]; omega
    have hout_ns1_eq : runMSBTransducerOut Q deltaM emitM q0M ns1 = s * k1_n + c1_n := by
      rw [hout_ns1]
      change runMSBTransducerOut Q deltaM emitM q0M 1 +
          sumIterFin g1 e1 (2 * Q + natFact Q * s) (runMSBAutomaton Q deltaM q0M 1) = _
      rw [hsum1_n]; dsimp [k1_n, c1_n, q_n0, P]; omega
    have hbl_ms1_eq : binBitLength ms1 = s * P + (2 * Q + 2) := by
      rw [hbl_m_raw]; dsimp [d_s]; rw [Nat.mul_comm P s]; omega
    have hbl_evs1_eq : binBitLength evs1 = s * P + (2 * Q + 3) := by
      dsimp [evs1]; rw [hbl_ev_raw]; dsimp [d_s]; rw [Nat.mul_comm P s]; omega
    have hbl_ns1_eq : binBitLength ns1 = s * P + (2 * Q + 1) := by
      dsimp [ns1] at hbl_n_raw ⊢; rw [hbl_n_raw]; dsimp [d_s]; rw [Nat.mul_comm P s]; omega
    -- Preimage inequality at `ms1`:
    have hpre := hw.2.2.2.2 ms1 hms1_ge3 hms1_m3_raw
    dsimp only at hpre
    rw [hns1_div_raw] at hpre
    have hcanc := nat_mul_le_cancel_left_w5 qTheta _ _
      (Nat.lt_of_lt_of_le hw.1 hw.2.1)
      (Nat.le_trans hpre (Nat.mul_le_mul_right _ hw.2.1))
    let P_m := evalNatPoly2 pTerms (runMSBTransducerOut Q deltaM emitM q0M ms1) (binBitLength ms1)
    let Q_m := evalNatPoly2 qTerms (runMSBTransducerOut Q deltaM emitM q0M ms1) (binBitLength ms1)
    let P_ev := evalNatPoly2 pTerms (runMSBTransducerOut Q deltaM emitM q0M evs1) (binBitLength evs1)
    let Q_ev := evalNatPoly2 qTerms (runMSBTransducerOut Q deltaM emitM q0M evs1) (binBitLength evs1)
    let P_n := evalNatPoly2 pTerms (runMSBTransducerOut Q deltaM emitM q0M ns1) (binBitLength ns1)
    let Q_n := evalNatPoly2 qTerms (runMSBTransducerOut Q deltaM emitM q0M ns1) (binBitLength ns1)
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
        have hm : s * 1 ≤ s * k2 := Nat.mul_le_mul_left s hk2
        omega
      have hhi : s * k1 + c1 ≤ M_hi * s := by
        have hc_s : c1 ≤ C * s :=
          Nat.le_trans hc1 (by simpa using Nat.mul_le_mul_left C hs_pos)
        calc
          s * k1 + c1
              ≤ k1 * s + C * s := by rw [Nat.mul_comm s k1]; exact Nat.add_le_add_left hc_s _
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
    have hPm_Pev : s ^ dP * P_m ≤ (s + C) ^ dP * P_ev := by
      apply hpoly2_cr pTerms s (s + C) _ _ _ _ (by omega)
      · rw [hout_ms1_eq, hout_evs1_eq]; exact hsame1 k1_m _ _ hk1m_pos (by dsimp [C]; omega)
      · rw [hbl_ms1_eq, hbl_evs1_eq]; exact hsame1 P _ _ hP_pos (by dsimp [C]; omega)
    have hQev_Qm : s ^ dQ * Q_ev ≤ (s + C) ^ dQ * Q_m := by
      apply hpoly2_cr qTerms s (s + C) _ _ _ _ (by omega)
      · rw [hout_evs1_eq, hout_ms1_eq]; exact hsame1 k1_m _ _ hk1m_pos (by dsimp [C]; omega)
      · rw [hbl_evs1_eq, hbl_ms1_eq]; exact hsame1 P _ _ hP_pos (by dsimp [C]; omega)
    have hPm_Pn : P_m ≤ M_hi ^ dP * P_n := by
      have h := hpoly2_cr pTerms 1 M_hi
        (runMSBTransducerOut Q deltaM emitM q0M ms1) (binBitLength ms1)
        (runMSBTransducerOut Q deltaM emitM q0M ns1) (binBitLength ns1) hMhi_ge1
        (by rw [hout_ms1_eq, hout_ns1_eq]; exact hdiff1 k1_m _ k1_n _ hk1n_pos (by dsimp [M_hi]; omega) (by dsimp [C]; omega))
        (by rw [hbl_ms1_eq, hbl_ns1_eq]; exact hdiff1 P _ P _ hP_pos (by dsimp [M_hi]; omega) (by dsimp [C]; omega))
      simpa using h
    have hQn_Qm : Q_n ≤ M_hi ^ dQ * Q_m := by
      have h := hpoly2_cr qTerms 1 M_hi
        (runMSBTransducerOut Q deltaM emitM q0M ns1) (binBitLength ns1)
        (runMSBTransducerOut Q deltaM emitM q0M ms1) (binBitLength ms1) hMhi_ge1
        (by rw [hout_ns1_eq, hout_ms1_eq]; exact hdiff1 k1_n _ k1_m _ hk1m_pos (by dsimp [M_hi]; omega) (by dsimp [C]; omega))
        (by rw [hbl_ns1_eq, hbl_ms1_eq]; exact hdiff1 P _ P _ hP_pos (by dsimp [M_hi]; omega) (by dsimp [C]; omega))
      simpa using h
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
        s ^ D * K_den
            ≤ (s + C) ^ D * K_den := Nat.mul_le_mul_right K_den hsD_le
        _ ≤ (s + C) ^ D * (B_eff * ((P_n * Q_ev) * Q_m)) := Nat.mul_le_mul_left ((s + C) ^ D) hm_base
        _ = (B_eff * (s + C) ^ D) * ((P_n * Q_ev) * Q_m) := by
              rw [← Nat.mul_assoc ((s + C) ^ D) B_eff, Nat.mul_comm ((s + C) ^ D) B_eff]
    have hsum := Nat.add_le_add hbr1 hbr2
    rw [← Nat.one_mul (s ^ D * K_den), ← Nat.mul_assoc 1 (s ^ D) K_den,
        ← Nat.add_mul (B_eff * s ^ D) (1 * s ^ D) K_den,
        ← Nat.add_mul B_eff 1 (s ^ D),
        ← Nat.mul_add (B_eff * (s + C) ^ D),
        ← Nat.add_mul (P_ev * Q_n) (P_n * Q_ev) Q_m] at hsum
    have htot : ((B_eff + 1) * s ^ D) * K_den ≤ (B_eff * (s + C) ^ D) * K_den := by
      have hm := Nat.mul_le_mul_left (B_eff * (s + C) ^ D) hcanc
      exact Nat.le_trans hsum hm
    have hle_b := nat_mul_le_cancel_right_w5 K_den _ _ hK_pos htot
    have hlt_b := bernoulli_nat_ratio_lt 1 B_eff D C s (by decide) hBeff_pos hC_pos hs_ge
    omega

-- ----------------------------------------------------------------------------
-- Section 3B: 6th Solvable Mixed-(2, 3) Cousin `T_diamond6` (`Branch P5`)
-- ----------------------------------------------------------------------------

/-- Cone 7 of `T_diamond6`: `x + 811 = 2 ^ g * 3 ^ h` with `g ≥ 15, h ≥ 2` (starting at `x = 294101`). -/
def isDiamond6Cone7 (x : Nat) : Prop :=
  x ≥ 294101 ∧ x % 32768 = 31957 ∧ x % 9 = 8 ∧ coprime23Core (x + 811) = 1

instance (x : Nat) : Decidable (isDiamond6Cone7 x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/--
  6th solvable mixed-(2, 3) Collatz cousin `T_diamond6` on `Nat`:
  Extends `T_diamond5` by adding Cone 7 (`isDiamond6Cone7 x -> (3 * x + 1) / 128`, a genuine
  `v_2(3x + 1) = 7` Syracuse jump that steps `2 ^ g * 3 ^ h - 811 -> 2 ^ (g - 7) * 3 ^ (h + 1) - 19`
  directly into Cone 6 -> Cone 5's `r`-block spiral climb, e.g. `294101 -> 6893 -> 2585` and
  `21232853 -> 497645 -> 186617`, while converging globally to `1` under a 4-tier `ω^4` ranking)!
-/
def cousinDiamond6Step (x : Nat) : Nat :=
  if isDiamond6Cone7 x then (3 * x + 1) / 128 else cousinDiamond5Step x

def cousinDiamond6Iter : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamond6Iter k (cousinDiamond6Step x)

theorem cousinDiamond6Iter_add : ∀ (a b x : Nat),
    cousinDiamond6Iter (a + b) x = cousinDiamond6Iter b (cousinDiamond6Iter a x)
  | 0, _, _ => by simp [cousinDiamond6Iter]
  | a + 1, b, x => by
    rw [Nat.succ_add]
    exact cousinDiamond6Iter_add a b (cousinDiamond6Step x)

/-- Signed extension of `T_diamond6` (`q = 3`) to `Int` for `M2 = Z^-` separation. -/
def cousinDiamond6StepInt (x : Int) : Int :=
  if x ≥ 294101 ∧ x % 32768 = 31957 ∧ x % 9 = 8 ∧ coprime23Core (x.toNat + 811) = 1
  then (3 * x + 1) / 128
  else cousinDiamond5StepInt x

def cousinDiamond6IterInt : Nat -> Int -> Int
  | 0, x => x
  | k + 1, x => cousinDiamond6IterInt k (cousinDiamond6StepInt x)

/-- Hensel lift of `invMod256Odd` to `mod 32768` (`256^2 = 65536 = 2 * 32768`). -/
def invMod32768Odd (d : Nat) : Nat :=
  let i256 := invMod256Odd d
  (i256 * (65538 - ((d % 32768) * i256) % 32768)) % 32768

/-- Canonical reduced-pair extension of `T_diamond6` (`q = 3`) to positive `Q_(6)^+`. -/
def cousinDiamond6StepQ6 (p : Nat × Nat) : Nat × Nat :=
  let num := p.1
  let den := p.2
  let r32768 := (num * invMod32768Odd den) % 32768
  let r9 := (num * ((den % 9) ^ 5 % 9)) % 9
  if num ≥ 294101 * den ∧ r32768 = 31957 ∧ r9 = 8 ∧ core3 (core2 (num + 811 * den)) = den
  then reduceRatPair (3 * num + den) (128 * den)
  else cousinDiamond5StepQ6 p

def cousinDiamond6IterQ6 : Nat -> (Nat × Nat) -> (Nat × Nat)
  | 0, p => p
  | k + 1, p => cousinDiamond6IterQ6 k (cousinDiamond6StepQ6 p)

/-- Generalized odd-multiplier `q` step of `T_diamond6` on `Nat` for `M3` (`q = 7`) separation. -/
def cousinDiamond6StepParam (q x : Nat) : Nat :=
  if isDiamond6Cone7 x then (q * x + 1) / 128 else cousinDiamond5StepParam q x

def cousinDiamond6IterParam (q : Nat) : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamond6IterParam q k (cousinDiamond6StepParam q x)

/-- Exact `Nat`/`Int` step agreement for `T_diamond6` (`zero custom axioms`). -/
theorem cousinDiamond6StepInt_ofNat_eq (x : Nat) :
    cousinDiamond6StepInt (x : Int) = (cousinDiamond6Step x : Int) := by
  unfold cousinDiamond6StepInt cousinDiamond6Step isDiamond6Cone7
  have htoNat : (x : Int).toNat = x := rfl
  rw [htoNat]
  by_cases hc7 : x ≥ 294101 ∧ x % 32768 = 31957 ∧ x % 9 = 8 ∧ coprime23Core (x + 811) = 1
  · have hc7_i : (x : Int) ≥ 294101 ∧ (x : Int) % 32768 = 31957 ∧ (x : Int) % 9 = 8 ∧
        coprime23Core (x + 811) = 1 :=
      ⟨by omega, by omega, by omega, hc7.2.2.2⟩
    simp only [hc7_i, hc7, and_self, ite_true]
    omega
  · have hnc7_i : ¬ ((x : Int) ≥ 294101 ∧ (x : Int) % 32768 = 31957 ∧ (x : Int) % 9 = 8 ∧
        coprime23Core (x + 811) = 1) :=
      fun ⟨h1, h2, h3, h4⟩ => hc7 ⟨by omega, by omega, by omega, h4⟩
    simp only [hnc7_i, hc7, ite_false]
    exact cousinDiamond5StepInt_ofNat_eq x

theorem cousinDiamond6Step_pos (x : Nat) (hx : x > 0) : cousinDiamond6Step x > 0 := by
  unfold cousinDiamond6Step
  by_cases hc7 : isDiamond6Cone7 x
  · simp only [hc7, ite_true]; rcases hc7 with ⟨hge, _, _, _⟩; omega
  · simp only [hc7, ite_false]; exact cousinDiamond5Step_pos x hx

theorem cousinDiamond6Step_eq_d5_of_not_cone7 (x : Nat) (hnc7 : ¬ isDiamond6Cone7 x) :
    cousinDiamond6Step x = cousinDiamond5Step x := by
  unfold cousinDiamond6Step; simp [hnc7]

/--
  Theorem W9.3b (`cousin_diamond6_outside_cones4567_strict_descent`, `zero custom axioms`):
  Outside Cones 4, 5, 6, and 7, EVERY `x > 2` strictly decreases `cousinDiamond2Phi` in 1 step!
-/
theorem cousin_diamond6_outside_cones4567_strict_descent
    (x : Nat) (hx : x > 2)
    (hnc4 : ¬ isDiamond3Cone4 x) (hnc5 : ¬ isDiamond4Cone5 x)
    (hnc6 : ¬ isDiamond5Cone6 x) (hnc7 : ¬ isDiamond6Cone7 x) :
    cousinDiamond2Phi (cousinDiamond6Step x) < cousinDiamond2Phi x := by
  rw [cousinDiamond6Step_eq_d5_of_not_cone7 x hnc7]
  exact cousin_diamond5_outside_cones456_strict_descent x hx hnc4 hnc5 hnc6

-- Modular & Diophantine Cone-7 avoidance helpers:

theorem not_cone7_of_even (z : Nat) (hev : z % 2 = 0) : ¬ isDiamond6Cone7 z := by
  rintro ⟨_, h32k, _, _⟩; omega

theorem not_cone7_of_mod4_eq_3 (z : Nat) (hm4 : z % 4 = 3) : ¬ isDiamond6Cone7 z := by
  rintro ⟨_, h32k, _, _⟩; omega

theorem not_cone7_of_mod8_ne_5 (z : Nat) (hm8 : z % 8 ≠ 5) : ¬ isDiamond6Cone7 z := by
  rintro ⟨_, h32k, _, _⟩; omega

theorem not_cone7_of_mod32_ne_21 (z : Nat) (hm32 : z % 32 ≠ 21) : ¬ isDiamond6Cone7 z := by
  rintro ⟨_, h32k, _, _⟩; omega

theorem not_cone7_of_mod256_ne_213 (z : Nat) (hm256 : z % 256 ≠ 213) : ¬ isDiamond6Cone7 z := by
  rintro ⟨_, h32k, _, _⟩; omega

theorem not_cone7_of_mod9_ne_8 (z : Nat) (hm9 : z % 9 ≠ 8) : ¬ isDiamond6Cone7 z := by
  rintro ⟨_, _, h9, _⟩; exact hm9 h9

/--
  Crucial Diophantine Cone-7 Exclusion (`not_cone7_six_mul_pow9_sub1`, `zero custom axioms`):
  Even though `ur = 6 * 9 ^ m - 1` (`m ≥ 1`) shares `ur % 16 = 5 = 31957 % 16` AND
  `ur % 9 = 8 = 31957 % 9` with Cone 7, `ur` NEVER enters `isDiamond6Cone7` for ANY `m : Nat`!
  Proof: For `m ≤ 4`, `ur ≤ 39365 < 294101`; for `m = 5`, `ur % 32768 = 26613 ≠ 31957`; and for
  `m ≥ 6` (`e := m - 3 ≥ 3`), `ur + 811 = 162 * (27 * 9 ^ e + 5)` having `coprime23Core = 1`
  forces `27 * 9 ^ e + 5 = 2 ^ k`, hence `2 ^ k % 243 = 5 = 2 ^ 23 % 243` (`k % 162 = 23`),
  so `2 ^ k % 163 = 139`, whereas `(27 * 9 ^ e + 5) % 163` (`9 ^ 81 % 163 = 1`) avoids `139`!
-/
theorem not_cone7_six_mul_pow9_sub1 (m : Nat) :
    ¬ isDiamond6Cone7 (6 * 9 ^ m - 1) := by
  rintro ⟨hge, h32k, _, hcop⟩
  by_cases hm4 : m ≤ 4
  · have hp9 : 9 ^ m ≤ 9 ^ 4 := by
      have hsp : 4 = m + (4 - m) := by omega
      rw [hsp, Nat.pow_add 9 m (4 - m)]
      simpa using Nat.mul_le_mul_left (9 ^ m) (nat_pow_pos_of_pos 9 (by decide) (4 - m))
    have hle : 6 * 9 ^ m - 1 ≤ 39365 := by
      have h94 : (9 : Nat) ^ 4 = 6561 := by decide
      rw [h94] at hp9; omega
    have hlt : ¬ (294101 ≤ 39365) := by decide
    exact hlt (Nat.le_trans hge hle)
  · by_cases hm5 : m = 5
    · subst hm5
      have hbad : (6 * 9 ^ 5 - 1) % 32768 ≠ 31957 := by decide
      exact hbad h32k
    · have hm6 : m ≥ 6 := by omega
      clear hge h32k hm4 hm5
      let e := m - 3
      have he1 : e ≥ 1 := by dsimp [e]; omega
      let M := 27 * 9 ^ e + 5
      have hM_pos : M > 0 := by dsimp [M]; omega
      have hur_eq : 6 * 9 ^ m - 1 + 811 = 2 * (3 * (3 * (3 * (3 * M)))) := by
        dsimp [M, e]
        have hm_sp : m = 3 + (m - 3) := by omega
        conv => lhs; rw [hm_sp]
        rw [Nat.pow_add 9 3 (m - 3), show (9 : Nat) ^ 3 = 729 by decide]
        have hp9_pos := nat_pow_pos_of_pos 9 (by decide) (m - 3)
        generalize 9 ^ (m - 3) = p9 at hp9_pos ⊢
        omega
      rw [hur_eq,
          coprime23Core_mul2 _ (by omega),
          coprime23Core_mul3 _ (by omega),
          coprime23Core_mul3 _ (by omega),
          coprime23Core_mul3 _ (by omega),
          coprime23Core_mul3 M hM_pos] at hcop
      rcases decomp_2_3_exact M hM_pos with ⟨_, _, _, _, _, hM_mul⟩
      have hv3_1 : v3Pow M = 1 := v3Pow_of_not_div3 M (by dsimp [M]; omega)
      rw [hv3_1, hcop, Nat.mul_one, Nat.mul_one] at hM_mul
      rcases eq_pow2_of_v2Pow_aux M M hM_pos (Nat.le_refl M) with ⟨k, hk_pow⟩
      rw [hk_pow] at hM_mul
      -- Modulo `243 = 3 ^ 5`: `2 ^ k % 243 = 5`, forcing `k % 162 = 23`:
      have hM_243 : M % 243 = 5 := by
        dsimp [M]
        have he_sp : e = 1 + (e - 1) := by omega
        rw [he_sp, Nat.pow_add 9 1 (e - 1), Nat.pow_one,
            ← Nat.mul_assoc 27 9, show 27 * 9 = 243 from rfl,
            Nat.add_comm _ 5, Nat.add_mul_mod_self_left]
      have h2k_243 : 2 ^ k % 243 = 5 := by rw [hM_mul, hM_243]
      have h2_162_243 : 2 ^ 162 % 243 = 1 :=
        (pow2_totient_exact_valuation_all_weights 5 (by decide)).2.2.1
      have h2_rk_243 : 2 ^ (k % 162) % 243 = 2 ^ 23 % 243 := by
        have hk_dm : k = 162 * (k / 162) + k % 162 := (Nat.div_add_mod k 162).symm
        have hp_mul : (2 ^ 162) ^ (k / 162) % 243 = 1 := by
          rw [pow_mod_eq_of_mod_eq_w5 243 (2 ^ 162) 1 h2_162_243 (k / 162), Nat.one_pow]
        have h1 : 2 ^ k % 243 = 2 ^ (k % 162) % 243 := by
          conv => lhs; rw [hk_dm]
          rw [Nat.pow_add 2 (162 * (k / 162)) (k % 162),
              ← pow_pow_eq_mul_w5 2 162 (k / 162),
              Nat.mul_mod, hp_mul, Nat.one_mul, Nat.mod_mod]
        have h23_243 : 2 ^ 23 % 243 = 5 := by
          rw [← fastPowMod28_eq 243 2 23 (by decide) (by decide)]
          decide
        rw [← h1, h2k_243, h23_243]
      have hrk_eq : k % 162 = 23 :=
        pow2_inj_mod_pow3_w8 5 (k % 162) 23 (by decide)
          (Nat.mod_lt k (by decide)) (by decide) h2_rk_243
      -- Modulo `163`: `2 ^ 162 % 163 = 1 => 2 ^ k % 163 = 139`, whereas `(27 * 9 ^ e + 5) % 163 ≠ 139`:
      have h2_162_163 : 2 ^ 162 % 163 = 1 := by
        rw [← fastPowMod28_eq 163 2 162 (by decide) (by decide)]
        decide
      have h2k_163 : 2 ^ k % 163 = 139 := by
        have hk_dm : k = 162 * (k / 162) + 23 := by
          have h := (Nat.div_add_mod k 162).symm; omega
        have hp_mul : (2 ^ 162) ^ (k / 162) % 163 = 1 := by
          rw [pow_mod_eq_of_mod_eq_w5 163 (2 ^ 162) 1 h2_162_163 (k / 162), Nat.one_pow]
        rw [hk_dm, Nat.pow_add 2 (162 * (k / 162)) 23,
            ← pow_pow_eq_mul_w5 2 162 (k / 162),
            Nat.mul_mod, hp_mul, Nat.one_mul, Nat.mod_mod,
            ← fastPowMod28_eq 163 2 23 (by decide) (by decide)]
        decide
      have h9_81_163 : 9 ^ 81 % 163 = 1 := by
        rw [← fastPowMod28_eq 163 9 81 (by decide) (by decide)]
        decide
      let re : Fin 81 := ⟨e % 81, Nat.mod_lt e (by decide)⟩
      have h9e_163 : 9 ^ e % 163 = fastPowMod28 163 9 re.val := by
        have he_dm : e = 81 * (e / 81) + re.val := (Nat.div_add_mod e 81).symm
        have hp_mul : (9 ^ 81) ^ (e / 81) % 163 = 1 := by
          rw [pow_mod_eq_of_mod_eq_w5 163 (9 ^ 81) 1 h9_81_163 (e / 81), Nat.one_pow]
        conv => lhs; rw [he_dm]
        rw [Nat.pow_add 9 (81 * (e / 81)) re.val,
            ← pow_pow_eq_mul_w5 9 81 (e / 81),
            Nat.mul_mod, hp_mul, Nat.one_mul, Nat.mod_mod,
            ← fastPowMod28_eq 163 9 re.val (by decide) (by have := re.isLt; omega)]
      have hfp_mod : fastPowMod28 163 9 re.val % 163 = fastPowMod28 163 9 re.val := by
        rw [← h9e_163, Nat.mod_mod]
      have hM_163 : M % 163 = (27 * fastPowMod28 163 9 re.val + 5) % 163 := by
        dsimp [M]
        calc
          (27 * 9 ^ e + 5) % 163
              = ((27 * 9 ^ e) % 163 + 5 % 163) % 163 := Nat.add_mod _ _ 163
          _ = (((27 % 163) * (9 ^ e % 163)) % 163 + 5 % 163) % 163 := by rw [Nat.mul_mod 27 (9 ^ e) 163]
          _ = (((27 % 163) * (fastPowMod28 163 9 re.val % 163)) % 163 + 5 % 163) % 163 := by
                rw [h9e_163, hfp_mod]
          _ = ((27 * fastPowMod28 163 9 re.val) % 163 + 5 % 163) % 163 := by
                rw [← Nat.mul_mod 27 (fastPowMod28 163 9 re.val) 163]
          _ = (27 * fastPowMod28 163 9 re.val + 5) % 163 := (Nat.add_mod _ _ 163).symm
      have hno_163 : ∀ r : Fin 81, (27 * fastPowMod28 163 9 r.val + 5) % 163 ≠ 139 := by
        decide
      exact hno_163 re (hM_163.symm.trans (by rw [← hM_mul, h2k_163]))

theorem isDiamond5Cone6_of_pow2_pow3 (e f : Nat) (he : e ≥ 8) (hf : f ≥ 2) :
    isDiamond5Cone6 (2 ^ e * 3 ^ f - 19) := by
  have hp2_256 : 2 ^ e = 256 * 2 ^ (e - 8) := by
    conv => lhs; rw [show e = 8 + (e - 8) by omega]; rw [Nat.pow_add]
  have hp3_9 : 3 ^ f = 9 * 3 ^ (f - 2) := by
    conv => lhs; rw [show f = 2 + (f - 2) by omega]; rw [Nat.pow_add]
  have hge2304 : 2 ^ e * 3 ^ f ≥ 2304 := by
    have h1 : 256 ≤ 2 ^ e := by rw [hp2_256]; have hp := pow2_pos_nat (e - 8); omega
    have h2 : 9 ≤ 3 ^ f := by rw [hp3_9]; have hp := pow3_pos_nat (f - 2); omega
    simpa using Nat.mul_le_mul h1 h2
  refine ⟨by omega, ?_, ?_, ?_⟩
  · have hp_pos : 2 ^ (e - 8) * 3 ^ f ≥ 9 := by
      rw [hp3_9]
      simpa using Nat.mul_le_mul (pow2_pos_nat (e - 8)) (by have := pow3_pos_nat (f - 2); omega)
    rw [hp2_256, Nat.mul_assoc 256]; omega
  · have hp_ge : 2 ^ e * 3 ^ (f - 2) ≥ 256 := by
      rw [hp2_256]
      simpa using Nat.mul_le_mul (by have := pow2_pos_nat (e - 8); omega) (pow3_pos_nat (f - 2))
    rw [hp3_9, ← Nat.mul_assoc (2 ^ e) 9, Nat.mul_comm (2 ^ e) 9, Nat.mul_assoc 9]; omega
  · rw [show 2 ^ e * 3 ^ f - 19 + 19 = 2 ^ e * 3 ^ f by omega]
    exact coprime23Core_pow2_pow3 e f

theorem isDiamond6Cone7_of_pow2_pow3 (g h : Nat) (hg : g ≥ 15) (hh : h ≥ 2) :
    isDiamond6Cone7 (2 ^ g * 3 ^ h - 811) := by
  have hp2_32k : 2 ^ g = 32768 * 2 ^ (g - 15) := by
    conv => lhs; rw [show g = 15 + (g - 15) by omega]
    rw [Nat.pow_add, show (2 : Nat) ^ 15 = 32768 by decide]
  have hp3_9 : 3 ^ h = 9 * 3 ^ (h - 2) := by
    conv => lhs; rw [show h = 2 + (h - 2) by omega]; rw [Nat.pow_add]
  have hge : 2 ^ g * 3 ^ h ≥ 294912 := by
    have h1 : 32768 ≤ 2 ^ g := by rw [hp2_32k]; have hp := pow2_pos_nat (g - 15); omega
    have h2 : 9 ≤ 3 ^ h := by rw [hp3_9]; have hp := pow3_pos_nat (h - 2); omega
    have hc : 32768 * 9 = 294912 := by decide
    have hm := Nat.mul_le_mul h1 h2
    rwa [hc] at hm
  refine ⟨by omega, ?_, ?_, ?_⟩
  · have hp_pos : 2 ^ (g - 15) * 3 ^ h ≥ 9 := by
      rw [hp3_9]
      simpa using Nat.mul_le_mul (pow2_pos_nat (g - 15)) (by have := pow3_pos_nat (h - 2); omega)
    rw [hp2_32k, Nat.mul_assoc 32768]; omega
  · have hp_ge : 2 ^ g * 3 ^ (h - 2) ≥ 32768 := by
      rw [hp2_32k]
      simpa using Nat.mul_le_mul (by have := pow2_pos_nat (g - 15); omega) (pow3_pos_nat (h - 2))
    rw [hp3_9, ← Nat.mul_assoc (2 ^ g) 9, Nat.mul_comm (2 ^ g) 9, Nat.mul_assoc 9]; omega
  · rw [show 2 ^ g * 3 ^ h - 811 + 811 = 2 ^ g * 3 ^ h by omega]
    exact coprime23Core_pow2_pow3 g h

theorem cousin_diamond6_mersenne_scaled :
    ∀ (k a q : Nat), k + 1 ≤ a -> q ≥ 1 ->
      cousinDiamond6Iter k (2 ^ a * q - 1) = 3 ^ k * 2 ^ (a - k) * q - 1
  | 0, _, _, _, _ => by simp [cousinDiamond6Iter]
  | k + 1, a, q, hka, hq => by
    have hp4 : 2 ^ a * q = 4 * (2 ^ (a - 2) * q) := by
      conv => lhs; rw [show a = (a - 2) + 2 by omega]
      rw [Nat.pow_add 2 (a - 2) 2, show (2 : Nat) ^ 2 = 4 from rfl,
          Nat.mul_comm (2 ^ (a - 2)) 4, Nat.mul_assoc]
    have hm_pos : 2 ^ (a - 2) * q ≥ 1 := Nat.mul_le_mul (pow2_pos_nat (a - 2)) hq
    have hz4 : (2 ^ a * q - 1) % 4 = 3 := by omega
    simp only [cousinDiamond6Iter]
    rw [cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_mod4_eq_3 _ hz4)]
    have hd5 := cousin_diamond5_mersenne_scaled 1 a q (by omega) hq
    simp only [cousinDiamond5Iter, Nat.pow_one] at hd5
    have hstep_eq : cousinDiamond5Step (2 ^ a * q - 1) = 2 ^ (a - 1) * (3 * q) - 1 := by
      rw [hd5]
      apply congrArg (· - 1)
      rw [Nat.mul_comm 3 (2 ^ (a - 1)), Nat.mul_assoc]
    rw [hstep_eq, cousin_diamond6_mersenne_scaled k (a - 1) (3 * q) (by omega) (by omega),
        show a - 1 - k = a - (k + 1) by omega, Nat.pow_succ 3 k]
    apply congrArg (· - 1)
    calc
      3 ^ k * 2 ^ (a - (k + 1)) * (3 * q)
          = 3 ^ k * (2 ^ (a - (k + 1)) * 3) * q := by rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
      _ = 3 ^ k * (3 * 2 ^ (a - (k + 1))) * q := by rw [Nat.mul_comm (2 ^ (a - (k + 1))) 3]
      _ = 3 ^ k * 3 * 2 ^ (a - (k + 1)) * q := by rw [← Nat.mul_assoc (3 ^ k) 3]

theorem cousin_diamond6_even9_spine_drain :
    ∀ k : Nat, cousinDiamond6Iter k ((9 ^ (k + 1) - 1) / 4) = 2
  | 0 => rfl
  | k + 1 => by
    let j := k + 1
    have hp9j_ge9 : 9 ^ j ≥ 9 := by
      dsimp [j]; rw [Nat.pow_succ]; have hp := nat_pow_pos_of_pos 9 (by decide) k; omega
    have hp9j_m8 : 9 ^ j % 8 = 1 := pow9_mod8_eq_one_w5 j
    let q := (9 ^ j - 1) / 8
    have hp9j_eq : 9 ^ j = 8 * q + 1 := by dsimp [q]; omega
    have he_j1 : (9 ^ (j + 1) - 1) / 4 = 18 * q + 2 := by rw [Nat.pow_succ 9 j, hp9j_eq]; omega
    simp only [cousinDiamond6Iter]
    change cousinDiamond6Iter k (cousinDiamond6Step ((9 ^ (j + 1) - 1) / 4)) = 2
    have hnc7 : ¬ isDiamond6Cone7 ((9 ^ (j + 1) - 1) / 4) := by
      rw [he_j1]; exact not_cone7_of_even _ (by omega)
    rw [cousinDiamond6Step_eq_d5_of_not_cone7 _ hnc7]
    have hd5 : cousinDiamond5Step ((9 ^ (j + 1) - 1) / 4) = (9 ^ j - 1) / 4 := by
      have he_j : (9 ^ j - 1) / 4 = 2 * q := by rw [hp9j_eq]; omega
      rw [he_j1, he_j, cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (18 * q + 2) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]; unfold cousinDiamond3Step
      have hq_pos : q ≥ 1 := by dsimp [q]; omega
      have hodd_f : ¬ ((18 * q + 2) % 2 = 1) := by omega
      have h18_t : 18 * q + 2 ≥ 20 ∧ (18 * q + 2) % 18 = 2 := ⟨by omega, by omega⟩
      simp only [hodd_f, h18_t, and_self, ite_true, ite_false]; omega
    rw [hd5]
    exact cousin_diamond6_even9_spine_drain k

theorem cousin_diamond6_pow3_sub1_drain :
    ∀ k : Nat, cousinDiamond6Iter k (3 ^ (k + 1) - 1) = 2
  | 0 => rfl
  | k + 1 => by
    let j := k + 1
    have hp3_ge3 : 3 ^ j ≥ 3 := by dsimp [j]; rw [Nat.pow_succ]; have hp := pow3_pos_nat k; omega
    have ho_j1 := pow3_odd_nat_sec8 (j + 1)
    have hp_j1 := pow3_pos_nat (j + 1)
    simp only [cousinDiamond6Iter]
    change cousinDiamond6Iter k (cousinDiamond6Step (3 ^ (j + 1) - 1)) = 2
    rw [cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
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
    exact cousin_diamond6_pow3_sub1_drain k

theorem cousin_diamond6_cone5_two_step_climb :
    ∀ (q_c a b : Nat), 3 * q_c + 2 ≤ a -> b ≥ 1 ->
      cousinDiamond6Iter (2 * q_c) (2 ^ a * 3 ^ b - 7) =
        2 ^ (a - 3 * q_c) * 3 ^ (b + 2 * q_c) - 7
  | 0, _, _, _, _ => by simp [cousinDiamond6Iter]
  | q_c + 1, a, b, ha, hb => by
    have ha5 : a ≥ 5 := by omega
    have hc5 := isDiamond4Cone5_of_pow2_pow3 a b ha5 hb
    have hnc7_0 : ¬ isDiamond6Cone7 (2 ^ a * 3 ^ b - 7) :=
      not_cone7_of_mod32_ne_21 _ (by have h := hc5.2.1; omega)
    let mid := 2 ^ (a - 2) * 3 ^ (b + 1) - 5
    have hmid_4 : mid % 4 = 3 := by
      dsimp [mid]
      have hp8 : 2 ^ (a - 2) = 8 * 2 ^ (a - 5) := by
        conv => lhs; rw [show a - 2 = 3 + (a - 5) by omega]; rw [Nat.pow_add]
      rw [hp8, Nat.mul_assoc 8]
      have hp_pos : 2 ^ (a - 5) * 3 ^ (b + 1) ≥ 1 :=
        Nat.mul_le_mul (pow2_pos_nat _) (pow3_pos_nat _)
      omega
    have hnc7_1 : ¬ isDiamond6Cone7 mid := not_cone7_of_mod4_eq_3 mid hmid_4
    have hd5_2 := cousin_diamond5_cone5_two_step_climb 1 a b (by omega) hb
    simp only [Nat.mul_one, cousinDiamond5Iter] at hd5_2
    have hd5_s1 : cousinDiamond5Step (2 ^ a * 3 ^ b - 7) = mid := by
      rw [cousinDiamond5Step_eq_d4_of_not_cone6 _
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
    rw [hd5_s1] at hd5_2
    conv => lhs; rw [show 2 * (q_c + 1) = 2 + 2 * q_c by omega]
    rw [cousinDiamond6Iter_add 2 (2 * q_c)]
    have hi2 : cousinDiamond6Iter 2 (2 ^ a * 3 ^ b - 7) = 2 ^ (a - 3) * 3 ^ (b + 2) - 7 := by
      simp only [cousinDiamond6Iter,
        cousinDiamond6Step_eq_d5_of_not_cone7 _ hnc7_0, hd5_s1,
        cousinDiamond6Step_eq_d5_of_not_cone7 _ hnc7_1, hd5_2]
    rw [hi2, cousin_diamond6_cone5_two_step_climb q_c (a - 3) (b + 2) (by omega) (by omega),
        show a - 3 - 3 * q_c = a - 3 * (q_c + 1) by omega,
        show b + 2 + 2 * q_c = b + 2 * (q_c + 1) by omega]

theorem cousin_diamond6_a0_3_drain (b0 : Nat) (hb0 : b0 ≥ 3) :
    cousinDiamond6Step (8 * 3 ^ b0 - 7) = 12 * 3 ^ b0 - 10 ∧
    cousinDiamond6Step (12 * 3 ^ b0 - 10) = 4 * 3 ^ b0 - 4 ∧
    cousinDiamond6Step (4 * 3 ^ b0 - 4) = 4 * 3 ^ (b0 - 1) - 2 ∧
    cousinDiamond6Iter ((b0 - 1) / 2 + 7) (8 * 3 ^ b0 - 7) = 1 := by
  rcases cousin_diamond5_a0_3_drain b0 hb0 with ⟨hd5_s1, hd5_s2, hd5_s3, _⟩
  have hp3_ge27 : 3 ^ b0 ≥ 27 := by
    simpa using nat_pow_mono_exp_pos 3 3 b0 (by decide) hb0
  have hp3_b1_ge9 : 3 ^ (b0 - 1) ≥ 9 := by
    simpa using nat_pow_mono_exp_pos 3 2 (b0 - 1) (by decide) (by omega)
  have h3b0_m9 : 3 ^ b0 % 9 = 0 := by
    have hsp : b0 = 2 + (b0 - 2) := by omega
    rw [hsp, Nat.pow_add 3 2]; omega
  have hnc7_8 : ¬ isDiamond6Cone7 (8 * 3 ^ b0 - 7) := by
    apply not_cone7_of_mod9_ne_8
    have hm9 : (8 * 3 ^ b0) % 9 = 0 := by rw [Nat.mul_mod, h3b0_m9, Nat.mul_zero, Nat.zero_mod]
    omega
  have hs1 : cousinDiamond6Step (8 * 3 ^ b0 - 7) = 12 * 3 ^ b0 - 10 := by
    rw [cousinDiamond6Step_eq_d5_of_not_cone7 _ hnc7_8]; exact hd5_s1
  have hs2 : cousinDiamond6Step (12 * 3 ^ b0 - 10) = 4 * 3 ^ b0 - 4 := by
    rw [cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega))]; exact hd5_s2
  have hs3 : cousinDiamond6Step (4 * 3 ^ b0 - 4) = 4 * 3 ^ (b0 - 1) - 2 := by
    rw [cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega))]; exact hd5_s3
  have hs4 : cousinDiamond6Step (4 * 3 ^ (b0 - 1) - 2) = 2 * 3 ^ (b0 - 1) - 1 := by
    rw [cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
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
    have hsz : cousinDiamond6Step zr = yr := by
      rw [cousinDiamond6Step_eq_d5_of_not_cone7 zr (not_cone7_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 zr (not_cone6_of_mod16_ne_13 zr (by dsimp [zr]; omega))]
      have hnc5 : ¬ isDiamond4Cone5 zr := by rintro ⟨_, h32, _, _⟩; dsimp [zr] at h32; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 zr hnc5]
      have hc3 : core3 (zr + 1) = 2 := by
        rw [show zr + 1 = 2 * 9 ^ m by dsimp [zr]; omega,
            core3_mul2 (9 ^ m) (by omega), (pow9_eq_v3Pow_w5 m).2]
      rw [cousinDiamond3Step_of_core3_succ_two_w8 zr (by dsimp [zr]; omega) (by dsimp [zr]; omega) hc3]
      dsimp [zr, yr]; omega
    have hsy : cousinDiamond6Step yr = (9 ^ (m + 1) - 1) / 4 := by
      have hyr_m3 : yr % 3 = 1 := by
        have hm3 : 9 ^ m % 3 = 0 := by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
        dsimp [yr]; omega
      rw [cousinDiamond6Step_eq_d5_of_not_cone7 yr (not_cone7_of_mod9_ne_8 yr (by omega)),
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
    change cousinDiamond6Iter (m + 7) (8 * 3 ^ b0 - 7) = 1
    rw [show m + 7 = 4 + 1 + 1 + m + 1 by omega,
        cousinDiamond6Iter_add (4 + 1 + 1 + m) 1,
        cousinDiamond6Iter_add (4 + 1 + 1) m,
        cousinDiamond6Iter_add (4 + 1) 1,
        cousinDiamond6Iter_add 4 1]
    have hi4 : cousinDiamond6Iter 4 (8 * 3 ^ b0 - 7) = zr := by
      simp only [cousinDiamond6Iter, hs1, hs2, hs3, hs4, hu_eq]; rfl
    rw [hi4]
    have hiz : cousinDiamond6Iter 1 zr = yr := hsz
    rw [hiz]
    have hiy : cousinDiamond6Iter 1 yr = (9 ^ (m + 1) - 1) / 4 := hsy
    rw [hiy, cousin_diamond6_even9_spine_drain m]
    decide
  · have hb1_2m1 : b0 - 1 = 2 * m + 1 := by dsimp [m]; omega
    have hu_eq : 2 * 3 ^ (b0 - 1) - 1 = 6 * 9 ^ m - 1 := by
      rw [hb1_2m1, Nat.pow_succ, ← pow9_eq_pow3_double m]; omega
    let ur := 6 * 9 ^ m - 1
    let wr := (9 ^ (m + 1) - 1) / 2
    have hsu : cousinDiamond6Step ur = wr := by
      have hur_m16 : ur % 16 = 5 := by
        let q := (9 ^ m - 1) / 8
        have hp9_eq : 9 ^ m = 8 * q + 1 := by dsimp [q]; omega
        dsimp [ur]; rw [hp9_eq]; omega
      rw [cousinDiamond6Step_eq_d5_of_not_cone7 ur (not_cone7_six_mul_pow9_sub1 m),
          cousinDiamond5Step_eq_d4_of_not_cone6 ur (not_cone6_of_mod16_ne_13 ur (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 ur := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 ur hnc5]
      have hc3 : core3 (ur + 1) = 2 := by
        rw [show ur + 1 = 2 * (3 * 9 ^ m) by dsimp [ur]; omega,
            core3_mul2 (3 * 9 ^ m) (by omega),
            core3_mul3 (9 ^ m) (by omega), (pow9_eq_v3Pow_w5 m).2]
      rw [cousinDiamond3Step_of_core3_succ_two_w8 ur (by omega) (by dsimp [ur]; omega) hc3]
      dsimp [ur, wr]; rw [Nat.pow_succ 9 m]; omega
    have hsw : cousinDiamond6Step wr = (9 ^ (m + 1) - 1) / 4 := by
      let q := (9 ^ m - 1) / 8
      have hq_pos : q ≥ 1 := by dsimp [q]; omega
      have hp9_eq : 9 ^ m = 8 * q + 1 := by dsimp [q]; omega
      have hwr_eq : wr = 36 * q + 4 := by dsimp [wr]; rw [Nat.pow_succ 9 m, hp9_eq]; omega
      have hnext_eq : (9 ^ (m + 1) - 1) / 4 = 18 * q + 2 := by rw [Nat.pow_succ 9 m, hp9_eq]; omega
      rw [hwr_eq, hnext_eq,
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (36 * q + 4) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      rw [cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) (by omega)]
      omega
    change cousinDiamond6Iter (m + 7) (8 * 3 ^ b0 - 7) = 1
    rw [show m + 7 = 4 + 1 + 1 + m + 1 by omega,
        cousinDiamond6Iter_add (4 + 1 + 1 + m) 1,
        cousinDiamond6Iter_add (4 + 1 + 1) m,
        cousinDiamond6Iter_add (4 + 1) 1,
        cousinDiamond6Iter_add 4 1]
    have hi4 : cousinDiamond6Iter 4 (8 * 3 ^ b0 - 7) = ur := by
      simp only [cousinDiamond6Iter, hs1, hs2, hs3, hs4, hu_eq]; rfl
    rw [hi4]
    have hiu : cousinDiamond6Iter 1 ur = wr := hsu
    rw [hiu]
    have hiw : cousinDiamond6Iter 1 wr = (9 ^ (m + 1) - 1) / 4 := hsw
    rw [hiw, cousin_diamond6_even9_spine_drain m]
    decide

theorem cousin_diamond6_a0_2_and_4_drain (b0 : Nat) (hb0 : b0 ≥ 3) :
    cousinDiamond6Iter (b0 + 3) (4 * 3 ^ b0 - 7) = 1 ∧
    cousinDiamond6Iter ((b0 - 1) / 2 + 8) (16 * 3 ^ b0 - 7) = 1 := by
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
  · have hs1 : cousinDiamond6Step (4 * 3 ^ b0 - 7) = 6 * 3 ^ b0 - 10 := by
      rw [cousinDiamond6Step_eq_d5_of_not_cone7 _ (hnc7_c 4 (by decide)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (hnc6_c 4 (by decide))]
      exact cousin_diamond4_exit_step_general_odd 4 b0 (Or.inl rfl) hb0
    have hs2 : cousinDiamond6Step (6 * 3 ^ b0 - 10) = 2 * 3 ^ b0 - 4 := by
      rw [cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (6 * 3 ^ b0 - 10) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 6 * 3 ^ b0 = 18 * 3 ^ (b0 - 1) := by rw [h3b0_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    have hs3 : cousinDiamond6Step (2 * 3 ^ b0 - 4) = 2 * 3 ^ (b0 - 1) - 2 := by
      rw [cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (2 * 3 ^ b0 - 4) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 2 * 3 ^ b0 = 18 * 3 ^ (b0 - 2) := by rw [h3b0_sp, h3b1_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    have hs4 : cousinDiamond6Step (2 * 3 ^ (b0 - 1) - 2) = 3 ^ (b0 - 1) - 1 := by
      rw [cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
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
        cousinDiamond6Iter_add (4 + (b0 - 2)) 1,
        cousinDiamond6Iter_add 4 (b0 - 2)]
    have hi4 : cousinDiamond6Iter 4 (4 * 3 ^ b0 - 7) = 3 ^ ((b0 - 2) + 1) - 1 := by
      simp only [cousinDiamond6Iter, hs1, hs2, hs3, hs4]
      rw [show b0 - 1 = (b0 - 2) + 1 by omega]
    rw [hi4, cousin_diamond6_pow3_sub1_drain (b0 - 2)]
    decide
  · rcases cousin_diamond6_a0_3_drain b0 hb0 with ⟨ha3_s1, ha3_s2, ha3_s3, ha3⟩
    have hs1 : cousinDiamond6Step (16 * 3 ^ b0 - 7) = 24 * 3 ^ b0 - 10 := by
      rw [cousinDiamond6Step_eq_d5_of_not_cone7 _ (hnc7_c 16 (by decide)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (hnc6_c 16 (by decide))]
      exact cousin_diamond4_exit_step_general_odd 16 b0 (Or.inr (Or.inr rfl)) hb0
    have hs2 : cousinDiamond6Step (24 * 3 ^ b0 - 10) = 8 * 3 ^ b0 - 4 := by
      rw [cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (24 * 3 ^ b0 - 10) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 24 * 3 ^ b0 = 18 * (4 * 3 ^ (b0 - 1)) := by rw [h3b0_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    have hs3 : cousinDiamond6Step (8 * 3 ^ b0 - 4) = 8 * 3 ^ (b0 - 1) - 2 := by
      rw [cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (8 * 3 ^ b0 - 4) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 8 * 3 ^ b0 = 18 * (4 * 3 ^ (b0 - 2)) := by rw [h3b0_sp, h3b1_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    have hs4 : cousinDiamond6Step (8 * 3 ^ (b0 - 1) - 2) = 4 * 3 ^ (b0 - 1) - 2 := by
      rw [cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
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
        cousinDiamond6Iter_add 3 ((b0 - 1) / 2 + 4)] at ha3
    have hi3 : cousinDiamond6Iter 3 (8 * 3 ^ b0 - 7) = 4 * 3 ^ (b0 - 1) - 2 := by
      simp only [cousinDiamond6Iter, ha3_s1, ha3_s2, ha3_s3]
    rw [hi3] at ha3
    rw [show (b0 - 1) / 2 + 8 = 4 + ((b0 - 1) / 2 + 4) by omega,
        cousinDiamond6Iter_add 4 ((b0 - 1) / 2 + 4)]
    have hi4 : cousinDiamond6Iter 4 (16 * 3 ^ b0 - 7) = 4 * 3 ^ (b0 - 1) - 2 := by
      simp only [cousinDiamond6Iter, hs1, hs2, hs3, hs4]
    rw [hi4]
    exact ha3

theorem cousin_diamond6_cone4_return_aux (x : Nat) (hc4 : isDiamond3Cone4 x) :
    ∃ k : Nat, k ≤ cousinDiamond2Phi x ∧ cousinDiamond6Iter k x = 1 := by
  rcases cousin_diamond3_cone4_reaches_one_exact x hc4 with ⟨r, hr_ge3, hE, _, hphi_ge⟩
  refine ⟨3 * r + 4, hphi_ge, ?_⟩
  have hnc7_x : ¬ isDiamond6Cone7 x := not_cone7_of_mod8_ne_5 x (by have h8 := hc4.2.1; omega)
  have hnc6_x : ¬ isDiamond5Cone6 x := by rintro ⟨_, h256, _, _⟩; have h8 := hc4.2.1; omega
  have hx_odd : x % 2 = 1 := by have h8 := hc4.2.1; omega
  have hs1 : cousinDiamond6Step x = 2 ^ (2 * r + 1) - 1 := by
    rw [cousinDiamond6Step_eq_d5_of_not_cone7 x hnc7_x,
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
  have hglide : cousinDiamond6Iter (2 * r) (2 ^ (2 * r + 1) - 1) = zr := by
    have hf := cousin_diamond6_mersenne_scaled (2 * r) (2 * r + 1) 1 (by omega) (by decide)
    simp only [Nat.mul_one, show 2 * r + 1 - 2 * r = 1 by omega, Nat.pow_one] at hf
    rw [hf, ← pow9_eq_pow3_double r, Nat.mul_comm]
  have hp9_ge729 : 9 ^ r ≥ 729 := by
    simpa using nat_pow_mono_exp_pos 9 3 r (by decide) hr_ge3
  have hp9_m8 : 9 ^ r % 8 = 1 := pow9_mod8_eq_one_w5 r
  have hsz : cousinDiamond6Step zr = yr := by
    rw [cousinDiamond6Step_eq_d5_of_not_cone7 zr (not_cone7_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
        cousinDiamond5Step_eq_d4_of_not_cone6 zr (not_cone6_of_mod16_ne_13 zr (by dsimp [zr]; omega))]
    have hnc5 : ¬ isDiamond4Cone5 zr := by rintro ⟨_, h32, _, _⟩; dsimp [zr] at h32; omega
    rw [cousinDiamond4Step_eq_d3_of_not_cone5 zr hnc5]
    have hc3 : core3 (zr + 1) = 2 := by
      rw [show zr + 1 = 2 * 9 ^ r by dsimp [zr]; omega,
          core3_mul2 (9 ^ r) (by omega), (pow9_eq_v3Pow_w5 r).2]
    rw [cousinDiamond3Step_of_core3_succ_two_w8 zr (by dsimp [zr]; omega) (by dsimp [zr]; omega) hc3]
    dsimp [zr, yr]; omega
  have hsy : cousinDiamond6Step yr = (9 ^ (r + 1) - 1) / 4 := by
    have hyr_m3 : yr % 3 = 1 := by
      have hm3 : 9 ^ r % 3 = 0 := by rw [show r = (r - 1) + 1 by omega, Nat.pow_succ]; omega
      dsimp [yr]; omega
    rw [cousinDiamond6Step_eq_d5_of_not_cone7 yr (not_cone7_of_mod9_ne_8 yr (by omega)),
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
      cousinDiamond6Iter_add (1 + 2 * r + 1 + 1 + r) 1,
      cousinDiamond6Iter_add (1 + 2 * r + 1 + 1) r,
      cousinDiamond6Iter_add (1 + 2 * r + 1) 1,
      cousinDiamond6Iter_add (1 + 2 * r) 1,
      cousinDiamond6Iter_add 1 (2 * r)]
  have hi1 : cousinDiamond6Iter 1 x = 2 ^ (2 * r + 1) - 1 := hs1
  rw [hi1, hglide]
  have hiz : cousinDiamond6Iter 1 zr = yr := hsz
  rw [hiz]
  have hiy : cousinDiamond6Iter 1 yr = (9 ^ (r + 1) - 1) / 4 := hsy
  rw [hiy, cousin_diamond6_even9_spine_drain r]
  decide

theorem cousin_diamond6_cone5_return_aux (x : Nat) (hc5 : isDiamond4Cone5 x) :
    ∃ (a b k : Nat),
      a ≥ 5 ∧ b ≥ 1 ∧ x + 7 = 2 ^ a * 3 ^ b ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond6Iter k x = 1 := by
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
  have hqc_pos : q_c ≥ 1 := by dsimp [q_c]; omega
  have hb0_ge3 : b0 ≥ 3 := by dsimp [b0]; omega
  have ha0_234 : a0 = 2 ∨ a0 = 3 ∨ a0 = 4 := by dsimp [a0, q_c]; omega
  have hclimb := cousin_diamond6_cone5_two_step_climb q_c a b (by dsimp [q_c]; omega) hb1
  rw [← hx_eq] at hclimb
  change cousinDiamond6Iter (2 * q_c) x = 2 ^ a0 * 3 ^ b0 - 7 at hclimb
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
  have hd_3 := (cousin_diamond6_a0_3_drain b0 hb0_ge3).2.2.2
  rcases cousin_diamond6_a0_2_and_4_drain b0 hb0_ge3 with ⟨hd_2, hd_4⟩
  rcases ha0_234 with ha2 | ha3 | ha4
  · have hkx := hbound_x (b0 + 3) (by omega)
    refine ⟨a, b, 2 * q_c + (b0 + 3), ha5, hb1, hmul.symm, hkx,
      Nat.le_trans (by omega : 2 * q_c + (b0 + 3) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond6Iter_add (2 * q_c) (b0 + 3) x, hclimb, ha2]; exact hd_2
  · have hkx := hbound_x ((b0 - 1) / 2 + 7) (by omega)
    refine ⟨a, b, 2 * q_c + ((b0 - 1) / 2 + 7), ha5, hb1, hmul.symm, hkx,
      Nat.le_trans (by omega : 2 * q_c + ((b0 - 1) / 2 + 7) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond6Iter_add (2 * q_c) ((b0 - 1) / 2 + 7) x, hclimb, ha3]; exact hd_3
  · have hkx := hbound_x ((b0 - 1) / 2 + 8) (by omega)
    refine ⟨a, b, 2 * q_c + ((b0 - 1) / 2 + 8), ha5, hb1, hmul.symm, hkx,
      Nat.le_trans (by omega : 2 * q_c + ((b0 - 1) / 2 + 8) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond6Iter_add (2 * q_c) ((b0 - 1) / 2 + 8) x, hclimb, ha4]; exact hd_4

theorem cousin_diamond6_cone6_return_aux (x : Nat) (hc6 : isDiamond5Cone6 x) :
    ∃ (e f k : Nat),
      e ≥ 8 ∧ f ≥ 2 ∧ x + 19 = 2 ^ e * 3 ^ f ∧
      cousinDiamond6Step x = 2 ^ (e - 3) * 3 ^ (f + 1) - 7 ∧
      isDiamond4Cone5 (cousinDiamond6Step x) ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond6Iter k x = 1 := by
  have hnc7_x : ¬ isDiamond6Cone7 x :=
    not_cone7_of_mod256_ne_213 x (by have h := hc6.2.1; omega)
  rcases (cousin_diamond5_cones456_exact_return.2.2 x hc6) with
    ⟨e, f, _, he8, hf2, hmul, hd5_x, _, _, _⟩
  let y := 2 ^ (e - 3) * 3 ^ (f + 1) - 7
  have hstep_x : cousinDiamond6Step x = y := by
    rw [cousinDiamond6Step_eq_d5_of_not_cone7 x hnc7_x]; exact hd5_x
  have hc5_y : isDiamond4Cone5 y :=
    isDiamond4Cone5_of_pow2_pow3 (e - 3) (f + 1) (by omega) (by omega)
  rcases cousin_diamond6_cone5_return_aux y hc5_y with ⟨_, _, ky, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hy_step : y = (3 * x + 1) / 8 :=
      hd5_x.symm.trans (by unfold cousinDiamond5Step; simp [hc6])
    have hx_ge := hc6.1
    omega
  have h1ky_x : 1 + ky ≤ x := by omega
  have h1ky_phi : 1 + ky ≤ cousinDiamond2Phi x :=
    Nat.le_trans (by omega : 1 + ky ≤ x + 1) (cousinDiamond2Phi_ge_succ x)
  refine ⟨e, f, 1 + ky, he8, hf2, hmul, hstep_x, ?_, h1ky_x, h1ky_phi, ?_⟩
  · rw [hstep_x]; exact hc5_y
  · rw [cousinDiamond6Iter_add 1 ky x]
    have hi1 : cousinDiamond6Iter 1 x = y := hstep_x
    rw [hi1]; exact hky_1

/--
  Theorem W9.3c (`cousin_diamond6_cones4567_exact_return`, `zero custom axioms`):
  Exact 4-Tier `ω^4` Multi-Block Return Across Cones 4, 5, 6, AND 7 of `T_diamond6`:
  1. Every `x` in Cone 4 (`isDiamond3Cone4 x`) reaches `1` in `k ≤ cousinDiamond2Phi x` steps!
  2. Every `x` in Cone 5 (`isDiamond4Cone5 x`) has `x + 7 = 2 ^ a * 3 ^ b` (`a ≥ 5, b ≥ 1`) and
     reaches `1` in `k ≤ x` (`≤ cousinDiamond2Phi x`) steps!
  3. Every `x` in Cone 6 (`isDiamond5Cone6 x`) has `x + 19 = 2 ^ e * 3 ^ f` (`e ≥ 8, f ≥ 2`),
     steps into Cone 5, and reaches `1` in `k ≤ x` (`≤ cousinDiamond2Phi x`) steps!
  4. Every `x` in Cone 7 (`isDiamond6Cone7 x`) has `x + 811 = 2 ^ g * 3 ^ h` (`g ≥ 15, h ≥ 2`),
     steps in 1 genuine `v_2(3x + 1) = 7` jump `(3 * x + 1) / 128` directly into the Cone-6 state
     `y = 2 ^ (g - 7) * 3 ^ (h + 1) - 19`, and reaches `1` in `1 + k_y ≤ x` (`≤ cousinDiamond2Phi x`) steps!
-/
theorem cousin_diamond6_cones4567_exact_return :
    (∀ x : Nat, isDiamond3Cone4 x ->
      ∃ k : Nat, k ≤ cousinDiamond2Phi x ∧ cousinDiamond6Iter k x = 1) ∧
    (∀ x : Nat, isDiamond4Cone5 x ->
      ∃ (a b k : Nat),
        a ≥ 5 ∧ b ≥ 1 ∧ x + 7 = 2 ^ a * 3 ^ b ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond6Iter k x = 1) ∧
    (∀ x : Nat, isDiamond5Cone6 x ->
      ∃ (e f k : Nat),
        e ≥ 8 ∧ f ≥ 2 ∧ x + 19 = 2 ^ e * 3 ^ f ∧
        cousinDiamond6Step x = 2 ^ (e - 3) * 3 ^ (f + 1) - 7 ∧
        isDiamond4Cone5 (cousinDiamond6Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond6Iter k x = 1) ∧
    (∀ x : Nat, isDiamond6Cone7 x ->
      ∃ (g h k : Nat),
        g ≥ 15 ∧ h ≥ 2 ∧ x + 811 = 2 ^ g * 3 ^ h ∧
        cousinDiamond6Step x = 2 ^ (g - 7) * 3 ^ (h + 1) - 19 ∧
        isDiamond5Cone6 (cousinDiamond6Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond6Iter k x = 1) := by
  refine ⟨cousin_diamond6_cone4_return_aux,
          cousin_diamond6_cone5_return_aux,
          cousin_diamond6_cone6_return_aux, ?_⟩
  intro x hc7
  rcases hc7 with ⟨hx_ge, hx32k, hx9, hg1⟩
  have hc7_hold : isDiamond6Cone7 x := ⟨hx_ge, hx32k, hx9, hg1⟩
  rcases decomp_2_3_exact (x + 811) (by omega) with ⟨_, _, _, _, _, hmul⟩
  rw [hg1, Nat.mul_one] at hmul
  rcases eq_pow2_of_v2Pow_aux (x + 811) (x + 811) (by omega) (Nat.le_refl _) with ⟨g, hg⟩
  rcases eq_pow3_of_v3Pow_aux (x + 811) (x + 811) (by omega) (Nat.le_refl _) with ⟨h, hh⟩
  rw [hg, hh] at hmul
  -- `g ≥ 15` since `32768 = 2 ^ 15 ∣ (x + 811)` (`31957 + 811 = 32768`):
  have hg15 : g ≥ 15 := by
    by_cases hlt : g < 15
    · exfalso
      have hdiv32k : (x + 811) % 32768 = 0 := by omega
      have h32k_sp : 32768 = 2 ^ (g + 1) * 2 ^ (14 - g) := by
        rw [← Nat.pow_add 2 (g + 1) (14 - g), show g + 1 + (14 - g) = 15 by omega]
      rcases Nat.dvd_of_mod_eq_zero hdiv32k with ⟨q, hq⟩
      rw [← hmul, h32k_sp, Nat.mul_assoc (2 ^ (g + 1)),
          Nat.pow_succ 2 g, Nat.mul_assoc (2 ^ g) 2] at hq
      have h3h_ev : 3 ^ h = 2 * (2 ^ (14 - g) * q) :=
        nat_mul_left_cancel_pos (2 ^ g) _ _ (pow2_pos_nat g) hq
      have ho := pow3_odd_nat_sec8 h
      rw [h3h_ev, Nat.mul_mod_right] at ho
      cases ho
    · omega
  have hh2 : h ≥ 2 := by
    by_cases hh0 : h = 0
    · rw [hh0, Nat.pow_zero, Nat.mul_one] at hmul
      exact False.elim (pow2_mod3_nonzero_w5 g (by rw [hmul]; omega))
    · by_cases hh1 : h = 1
      · rw [hh1, Nat.pow_one] at hmul
        have hm3 := pow2_mod3_nonzero_w5 g
        have hdiv := (Nat.div_add_mod (2 ^ g) 3).symm
        have hx9_eq : (x + 811) % 9 = 0 := by omega
        rw [← hmul, hdiv, Nat.add_mul,
            show 3 * (2 ^ g / 3) * 3 = 9 * (2 ^ g / 3) by omega] at hx9_eq
        omega
      · omega
  let y := 2 ^ (g - 7) * 3 ^ (h + 1) - 19
  have hstep_x : cousinDiamond6Step x = y := by
    unfold cousinDiamond6Step
    simp only [hc7_hold, ite_true]
    dsimp [y]
    have hp128 : 2 ^ g = 128 * 2 ^ (g - 7) := by
      conv => lhs; rw [show g = 7 + (g - 7) by omega]; rw [Nat.pow_add]
    have hprod_pos : 2 ^ (g - 7) * 3 ^ h ≥ 256 * 9 := by
      have h1 : 256 ≤ 2 ^ (g - 7) := by simpa using pow2_mono_nat (by omega : 8 ≤ g - 7)
      have h2 : 9 ≤ 3 ^ h := by simpa using nat_pow_mono_exp_pos 3 2 h (by decide) hh2
      simpa using Nat.mul_le_mul h1 h2
    have hx_val : x = 128 * 2 ^ (g - 7) * 3 ^ h - 811 := by rw [← hp128]; omega
    rw [hx_val, Nat.mul_assoc 128 (2 ^ (g - 7)) (3 ^ h),
        Nat.pow_succ 3 h, ← Nat.mul_assoc (2 ^ (g - 7)) (3 ^ h) 3]
    omega
  have hc6_y : isDiamond5Cone6 y :=
    isDiamond5Cone6_of_pow2_pow3 (g - 7) (h + 1) (by omega) (by omega)
  rcases cousin_diamond6_cone6_return_aux y hc6_y with ⟨_, _, ky, _, _, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hstep_eq : y = (3 * x + 1) / 128 :=
      hstep_x.symm.trans (by unfold cousinDiamond6Step; simp [hc7_hold])
    omega
  have h1ky_x : 1 + ky ≤ x := by omega
  have h1ky_phi : 1 + ky ≤ cousinDiamond2Phi x :=
    Nat.le_trans (by omega : 1 + ky ≤ x + 1) (cousinDiamond2Phi_ge_succ x)
  refine ⟨g, h, 1 + ky, hg15, hh2, hmul.symm, hstep_x, ?_, h1ky_x, h1ky_phi, ?_⟩
  · rw [hstep_x]; exact hc6_y
  · rw [cousinDiamond6Iter_add 1 ky x]
    have hi1 : cousinDiamond6Iter 1 x = y := hstep_x
    rw [hi1]; exact hky_1

theorem cousin_diamond6_reaches_one_within_phi :
    ∀ (B x : Nat), x > 0 -> cousinDiamond2Phi x ≤ B ->
      ∃ k : Nat, k ≤ B ∧ cousinDiamond6Iter k x = 1
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
        · rcases cousin_diamond6_cones4567_exact_return.1 x hc4 with ⟨k, hle_phi, hk1⟩
          exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
        · by_cases hc5 : isDiamond4Cone5 x
          · rcases cousin_diamond6_cones4567_exact_return.2.1 x hc5 with
              ⟨_, _, k, _, _, _, _, hle_phi, hk1⟩
            exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
          · by_cases hc6 : isDiamond5Cone6 x
            · rcases cousin_diamond6_cones4567_exact_return.2.2.1 x hc6 with
                ⟨_, _, k, _, _, _, _, _, _, hle_phi, hk1⟩
              exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
            · by_cases hc7 : isDiamond6Cone7 x
              · rcases cousin_diamond6_cones4567_exact_return.2.2.2 x hc7 with
                  ⟨_, _, k, _, _, _, _, _, _, hle_phi, hk1⟩
                exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
              · have hdesc := cousin_diamond6_outside_cones4567_strict_descent x
                  (by omega) hc4 hc5 hc6 hc7
                have hpos := cousinDiamond6Step_pos x hx
                rcases cousin_diamond6_reaches_one_within_phi B (cousinDiamond6Step x) hpos (by omega) with
                  ⟨k, hk_le, hk_eq⟩
                exact ⟨k + 1, by omega, hk_eq⟩

/--
  Theorem W9.3d (`cousin_diamond6_global_convergence`, `zero custom axioms`):
  Unconditional Global Convergence & Degree-5 Polynomial Stopping Bound for `T_diamond6`:
  For EVERY `x > 0`, `cousinDiamond6Iter` reaches `1` within `k ≤ (x + 1) ^ 3 + (x + 1) ^ 5` steps!
-/
theorem cousin_diamond6_global_convergence (x : Nat) (hx : x > 0) :
    ∃ k : Nat, k ≤ (x + 1) ^ 3 + (x + 1) ^ 5 ∧ cousinDiamond6Iter k x = 1 := by
  rcases cousin_diamond6_reaches_one_within_phi (cousinDiamond2Phi x) x hx (Nat.le_refl _) with
    ⟨k, hk_phi, hk1⟩
  exact ⟨k, Nat.le_trans hk_phi (cousinDiamond2Phi_upper_poly_bound x), hk1⟩

theorem exists_non_desc_along_diamond6_iter :
    ∀ (terms : List LaurentTerm) (A0 B0 C0 N z : Nat),
      N ≥ 1 ->
      (∀ i : Nat, i < N ->
        cousinDiamond6Iter i z ≥ 3 ∧
        (cousinDiamond6Iter i z) % 2 = 1 ∧
        cousinDiamond6Step (cousinDiamond6Iter i z) ≥ 3) ->
      ¬ laurentDescProp terms A0 B0 C0 z (cousinDiamond6Iter N z) ->
      ∃ x : Nat,
        x ≥ 3 ∧ x % 2 = 1 ∧ cousinDiamond6Step x ≥ 3 ∧
        ¬ laurentDescProp terms A0 B0 C0 x (cousinDiamond6Step x)
  | _, _, _, _, 0, _, hN, _, _ => by omega
  | terms, A0, B0, C0, 1, z, _, hall, hnd => by
    rcases hall 0 (by decide) with ⟨hz3, hzo, hsz3⟩
    exact ⟨z, hz3, hzo, hsz3, hnd⟩
  | terms, A0, B0, C0, m + 2, z, _, hall, hnd => by
    if h0 : laurentDescProp terms A0 B0 C0 z (cousinDiamond6Step z) then
      have hnd_next : ¬ laurentDescProp terms A0 B0 C0 (cousinDiamond6Step z)
          (cousinDiamond6Iter (m + 1) (cousinDiamond6Step z)) :=
        fun hrest => hnd (laurentDescProp_trans terms A0 B0 C0 z (cousinDiamond6Step z) _ h0 hrest)
      exact exists_non_desc_along_diamond6_iter terms A0 B0 C0 (m + 1) (cousinDiamond6Step z)
        (by omega) (fun i hi => hall (i + 1) (by omega)) hnd_next
    else
      rcases hall 0 (by omega) with ⟨hz3, hzo, hsz3⟩
      exact ⟨z, hz3, hzo, hsz3, h0⟩

/--
  Theorem W9.3e (`cousin_diamond6_r_block_spiral_climb_and_laurent_impossibility`, zero custom axioms):
  1. Cone-7 -> Cone-6 -> Cone-5 4-Tier Cascade & Unbounded `r`-Block Spiral Climb (`∀ r ≥ 1`):
     `294101 -> 6893 -> 2585`, `21232853 -> 497645 -> 186617`, AND
     `cousinDiamond6Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5` for ALL `j ≤ r`!
  2. Universal `∀ L ≥ 1` Multi-Term Laurent Valuation Impossibility on `cousinDiamond6Step`!
-/
theorem cousin_diamond6_r_block_spiral_climb_and_laurent_impossibility :
    cousinDiamond6Step 294101 = 6893 ∧
    cousinDiamond6Step 6893 = 2585 ∧
    cousinDiamond6Step 21232853 = 497645 ∧
    cousinDiamond6Step 497645 = 186617 ∧
    (∀ (r j : Nat), r ≥ 1 -> j ≤ r ->
      cousinDiamond6Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5) ∧
    (∀ (terms : List LaurentTerm) (A0 B0 C0 : Nat),
      (∃ t ∈ terms, t.coeff > 0) ->
      ∃ x : Nat,
        x ≥ 3 ∧ x % 2 = 1 ∧ cousinDiamond6Step x ≥ 3 ∧
        ¬ (evalLaurentSumNum terms (cousinDiamond6Step x) * laurentValDen A0 B0 C0 x <
            evalLaurentSumNum terms x * laurentValDen A0 B0 C0 (cousinDiamond6Step x))) := by
  have hspiral : ∀ (r j : Nat), r ≥ 1 -> j ≤ r ->
      cousinDiamond6Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5 := by
    intro r j hr hj
    cases j with
    | zero => simp [cousinDiamond6Iter]
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
      have hs_first : cousinDiamond6Step x0 = 2 ^ (4 * r + 1) * 3 ^ 1 - 7 := by
        rw [cousinDiamond6Step_eq_d5_of_not_cone7 x0 (not_cone7_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond5Step_eq_d4_of_not_cone6 x0 (not_cone6_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond4Step_mod4_eq_3 x0 hx0_m4]
        dsimp [x0]
        rw [hx0_pow, show 4 * r + 2 = (4 * r + 1) + 1 by omega, Nat.pow_succ 2 (4 * r + 1)]
        have hp := pow2_pos_nat (4 * r + 1); omega
      have hclimb := cousin_diamond6_cone5_two_step_climb j' (4 * r + 1) 1 (by omega) (by decide)
      let y_end := 2 ^ (4 * r + 1 - 3 * j') * 3 ^ (1 + 2 * j') - 7
      have hy_c5 : isDiamond4Cone5 y_end :=
        isDiamond4Cone5_of_pow2_pow3 (4 * r + 1 - 3 * j') (1 + 2 * j') (by omega) (by omega)
      have hy_nc7 : ¬ isDiamond6Cone7 y_end :=
        not_cone7_of_mod32_ne_21 y_end (by have h := hy_c5.2.1; omega)
      have hy_nc6 : ¬ isDiamond5Cone6 y_end :=
        not_cone6_of_mod32_ne_13 y_end (by have h := hy_c5.2.1; omega)
      have hs_last : cousinDiamond6Step y_end = 4 * 16 ^ (r - (j' + 1)) * 18 ^ (j' + 1) - 5 := by
        rw [cousinDiamond6Step_eq_d5_of_not_cone7 y_end hy_nc7,
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
          have hm := Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl 4) h1) h2
          simpa using hm
        have hy_gt7 : 2 ^ (4 * r + 1 - 3 * j') * 3 ^ (1 + 2 * j') ≥ 7 := by omega
        omega
      rw [show 2 * (j' + 1) = 1 + 2 * j' + 1 by omega,
          cousinDiamond6Iter_add (1 + 2 * j') 1,
          cousinDiamond6Iter_add 1 (2 * j')]
      have hi1 : cousinDiamond6Iter 1 x0 = 2 ^ (4 * r + 1) * 3 ^ 1 - 7 := hs_first
      rw [hi1, hclimb]
      exact hs_last
  refine ⟨by decide, by decide, by decide, by decide, hspiral, ?_⟩
  intro terms A0 B0 C0 hnonempty
  rcases three_family_multiterm_laurent_obstruction terms A0 B0 C0 hnonempty with
    h97 | ⟨j2, hj2⟩ | ⟨r, hr_pos, hr3⟩
  · have hs97 : cousinDiamond6Step 97 = 73 := by decide
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
    have hnc7_xj2 : ¬ isDiamond6Cone7 xj2 :=
      not_cone7_of_mod8_ne_5 xj2 (by have h := hc4_xj2.2.1; omega)
    have hnc6_xj2 : ¬ isDiamond5Cone6 xj2 := by
      rintro ⟨_, h256, _, _⟩; have h := hc4_xj2.2.1; omega
    have hstep_xj2 : cousinDiamond6Step xj2 = yj2 := by
      rw [cousinDiamond6Step_eq_d5_of_not_cone7 xj2 hnc7_xj2,
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
        cousinDiamond6Iter i xr3 = 3 ^ i * 2 ^ (2 * r + 1 - i) - 1 ∧
        cousinDiamond6Iter i xr3 ≥ 7 ∧
        (cousinDiamond6Iter i xr3) % 2 = 1 := by
      intro i hi
      have hf := cousin_diamond6_mersenne_scaled i (2 * r + 1) 1 (by omega) (by decide)
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
    have hiter_2r : cousinDiamond6Iter (2 * r) xr3 = zr := by
      have hf := (hglide_i (2 * r) (Nat.le_refl _)).1
      rw [hf, show 2 * r + 1 - 2 * r = 1 by omega, Nat.pow_one,
          ← pow9_eq_pow3_double r, Nat.mul_comm]
    have hstep_zr : cousinDiamond6Step zr = yr3 := by
      rw [cousinDiamond6Step_eq_d5_of_not_cone7 zr (not_cone7_of_mod8_ne_5 zr (by dsimp [zr]; omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 zr (not_cone6_of_mod16_ne_13 zr (by dsimp [zr]; omega))]
      have hnc5 : ¬ isDiamond4Cone5 zr := by rintro ⟨_, h32, _, _⟩; dsimp [zr] at h32; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 zr hnc5]
      have hc3 : core3 (zr + 1) = 2 := by
        rw [show zr + 1 = 2 * 9 ^ r by dsimp [zr]; omega,
            core3_mul2 (9 ^ r) (by omega), (pow9_eq_v3Pow_w5 r).2]
      rw [cousinDiamond3Step_of_core3_succ_two_w8 zr (by dsimp [zr]; omega) (by dsimp [zr]; omega) hc3]
      dsimp [zr, yr3]; omega
    have hiter_2r1 : cousinDiamond6Iter (2 * r + 1) xr3 = yr3 := by
      rw [cousinDiamond6Iter_add (2 * r) 1 xr3, hiter_2r]; exact hstep_zr
    have hall : ∀ i : Nat, i < 2 * r + 1 ->
        cousinDiamond6Iter i xr3 ≥ 3 ∧
        (cousinDiamond6Iter i xr3) % 2 = 1 ∧
        cousinDiamond6Step (cousinDiamond6Iter i xr3) ≥ 3 := by
      intro i hi
      by_cases hlt : i < 2 * r
      · rcases hglide_i i (by omega) with ⟨_, hge7, hodd_i⟩
        have hnext : cousinDiamond6Step (cousinDiamond6Iter i xr3) =
            cousinDiamond6Iter (i + 1) xr3 :=
          (cousinDiamond6Iter_add i 1 xr3).symm
        rcases hglide_i (i + 1) (by omega) with ⟨_, hge7_n, _⟩
        exact ⟨by omega, hodd_i, by rw [hnext]; omega⟩
      · have hi_eq : i = 2 * r := by omega
        rw [hi_eq, hiter_2r, hstep_zr]
        exact ⟨by dsimp [zr]; omega, by dsimp [zr]; omega, by dsimp [yr3]; omega⟩
    change ¬ laurentDescProp terms A0 B0 C0 xr3 yr3 at hr3
    rw [← hiter_2r1] at hr3
    exact exists_non_desc_along_diamond6_iter terms A0 B0 C0 (2 * r + 1) xr3 (by omega) hall hr3

/--
  Theorem W9.3f (`cousin_diamond6_q6_noninteger_avoids_cone7`, choice-free `zero custom axioms`):
  Universal Non-Integer Rational Exclusion from Cone 7 on `M1 = Q_(6)^+`:
  For EVERY reduced non-integer rational `(num, den)` (`Nat.gcd num den = 1` and `den > 1`),
  `core3 (core2 (num + 811 * den)) ≠ den`, so `cousinDiamond6StepQ6 (num, den)` NEVER enters
  Cone 7 and agrees identically with `cousinDiamond5StepQ6 (num, den)`!
-/
theorem cousin_diamond6_q6_noninteger_avoids_cone7 (num den : Nat)
    (hgcd : Nat.gcd num den = 1) (hden : den > 1) :
    core3 (core2 (num + 811 * den)) ≠ den ∧
    cousinDiamond6StepQ6 (num, den) = cousinDiamond5StepQ6 (num, den) := by
  have hne : core3 (core2 (num + 811 * den)) ≠ den := by
    intro heq
    have hdvd_sum : den ∣ (num + 811 * den) := by
      have hc_dvd : core3 (core2 (num + 811 * den)) ∣ (num + 811 * den) :=
        Nat.dvd_trans (core3Aux_dvd_w8 _ _) (core2Aux_dvd_w8 _ _)
      rwa [heq] at hc_dvd
    rcases hdvd_sum with ⟨k, hk⟩
    have hdvd_num : den ∣ num := ⟨k - 811, by
      have hge : k ≥ 811 := by
        by_cases hlt : k < 811
        · have hm := Nat.mul_le_mul_left den (show k ≤ 810 by omega)
          omega
        · omega
      rw [Nat.mul_sub_left_distrib]
      omega⟩
    have hdvd_gcd : den ∣ Nat.gcd num den := Nat.dvd_gcd hdvd_num (Nat.dvd_refl den)
    rw [hgcd] at hdvd_gcd
    rcases hdvd_gcd with ⟨c, hc⟩
    cases c with
    | zero => omega
    | succ c' =>
      have hle : den * 1 ≤ den * (c' + 1) := Nat.mul_le_mul_left den (by omega)
      omega
  refine ⟨hne, ?_⟩
  unfold cousinDiamond6StepQ6
  have hcond : ¬ (num ≥ 294101 * den ∧ (num * invMod32768Odd den) % 32768 = 31957 ∧
      (num * ((den % 9) ^ 5 % 9)) % 9 = 8 ∧ core3 (core2 (num + 811 * den)) = den) :=
    fun ⟨_, _, _, hc⟩ => hne hc
  simp only [hcond, ite_false]

/--
  Theorem W9.3g (`cousin_diamond6_counter_model_separation`, choice-free `[]` axioms):
  `T_diamond6` rejects ALL three Counter-Models (`M1 = Q_(6)^+` 5-cycle `(1, 7) -> ... -> (1, 7)`
  plus non-integer `(294101, 7)` bypassing Cone 7 by `W9.3f`, `M2 = Z^-` cycles `-1` and
  `-5 -> -7 -> -10 -> -5`, and `M3` supercritical `q = 7` 5-cycle at `5`), AND at the genuine
  `v_2(3x + 1) = 7` Cone-7 jumps `294101 -> 6893 -> 2585` and `21232853 -> 497645 -> 186617`
  (`ZPOS_COUSIN_DIAMOND6_CONE7_21232853_JUMP`) strictly increases `cousinDiamond2Phi`
  (`cousinDiamond2Phi 21232853 < cousinDiamond2Phi 497645`) directly into Cone 6 -> Cone 5
  while converging to `1` in `13` and `19` steps respectively!
-/
theorem cousin_diamond6_counter_model_separation :
    cousinDiamond6StepInt (-1) = -1 ∧
    cousinDiamond6IterInt 3 (-5) = -5 ∧
    cousinDiamond6IterParam 7 5 5 = 5 ∧
    cousinDiamond6StepQ6 (1, 7) = (5, 7) ∧
    cousinDiamond6IterQ6 5 (1, 7) = (1, 7) ∧
    cousinDiamond6StepQ6 (294101, 7) = cousinDiamond5StepQ6 (294101, 7) ∧
    cousinDiamond6Step 294101 = 6893 ∧
    cousinDiamond6StepInt 294101 = 6893 ∧
    cousinDiamond6StepQ6 (294101, 1) = (6893, 1) ∧
    cousinDiamond6Iter 13 294101 = 1 ∧
    cousinDiamond6Step 21232853 = 497645 ∧
    cousinDiamond6Step 497645 = 186617 ∧
    cousinDiamond2Phi 21232853 < cousinDiamond2Phi 497645 ∧
    cousinDiamond6Iter 19 21232853 = 1 := by
  decide

-- ============================================================================
-- SECTION 4: Front D (Branches P5.3 & P2.2) — Complete Global `(u_1, q_1)` vs
--            `(u_2, q_2)` Collision Classification Across All `CoreWords × Nat`
--            & Universal `∀ k` `mod (2 * 3^k)` Markov Prefix-Memory Annihilation
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Section 4A: Universal `q ≥ 1` First-Hit (`∀ w ≥ 1`) & Global Collision Theorem (`P5.3`)
-- ----------------------------------------------------------------------------

/--
  Universal `q ≥ 1` First-Hit Theorem Across ALL Core Parity Words (`w ≥ 1`, zero custom axioms):
  Drops Wave 5's `parityWeight u ≥ 2` side condition (`one_generator_q_pos_always_first_hit`),
  proving EVERY `(u, q)` with `IsCoreParityWord u` and `q ≥ 1` (including `u = [true]`)
  satisfies `IsFirstHitOnePair u q`!
-/
theorem one_generator_q_pos_all_weights_first_hit
    (u : List Bool) (q : Nat)
    (hu : IsCoreParityWord u) (hq : q ≥ 1) :
    IsFirstHitOnePair u q := by
  refine ⟨hu, ?_⟩
  let y := exactBackwardQuotient 1 u q
  let L := backwardOneTotalSteps u q
  let shift := canonicalSuffixShift u 1 + q * (2 * 3 ^ (parityWeight u - 1))
  have hcs_odd : canonicalSuffixShift u 1 % 2 = 1 :=
    canonicalSuffixShift_append_markov_recurrence.1 u hu.2
  have hshift_ge3 : shift ≥ 3 := by
    dsimp [shift]
    have hp3 := pow3_pos_nat (parityWeight u - 1)
    have hm := Nat.mul_le_mul hq (by omega : 2 ≤ 2 * 3 ^ (parityWeight u - 1))
    omega
  have hu_len : u.length ≥ 1 := by
    cases u with
    | nil => have hh := hu.1; simp at hh
    | cons _ _ => simp
  have hL_eq : L = u.length + shift := rfl
  have hL_ge4 : L ≥ 4 := by omega
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
  · have hsplit_j : L - 2 = j + (L - 2 - j) := by omega
    have htriv : collatzIter (L - 2) y = 1 ∨ collatzIter (L - 2) y = 2 := by
      rw [hsplit_j, collatzIter_add]
      exact collatzIter_triv_one_two_w5 (L - 2 - j) (collatzIter j y) (Or.inl hj1)
    rcases htriv with h_eq1 | h_eq2
    · have hpar_split : parityOfIter L y = parityOfIter (L - 2) y ++ [true, false] := by
        have hLs : L = (L - 2) + 2 := by omega
        conv => lhs; rw [hLs]
        rw [parityOfIter_append_split (L - 2) 2 y, h_eq1]
        rfl
      have hv_split : v = (u ++ List.replicate (shift - 2) false) ++ [false, false] := by
        dsimp [v]
        have hs2 : shift = (shift - 2) + 2 := by omega
        conv => lhs; rhs; rw [hs2]
        rw [replicate_false_split_w5 (shift - 2) 2, ← List.append_assoc]
        rfl
      rw [hv_split, hpar_split] at hv_par
      have hlen_pre : (u ++ List.replicate (shift - 2) false).length =
          (parityOfIter (L - 2) y).length := by
        rw [List.length_append, List.length_replicate, parityOfIter_length]; omega
      have hsuf := list_append_right_eq_of_eq_len_w5 _ _ [false, false] [true, false]
        hlen_pre hv_par
      simp at hsuf
    · have hLs : L = (L - 2) + 2 := by omega
      rw [hLs, collatzIter_add (L - 2) 2 y, h_eq2] at hiterL
      have hs2 : collatzIter 2 2 = 2 := by decide
      rw [hs2] at hiterL
      omega

/--
  Canonical `(q, m)` loop-unrolled `q = 0` core parity word colliding with `(u, q)`:
    `((u ++ replicate (canonicalSuffixShift u 1 + q * (2 * 3 ^ (w - 1))) false) ++ [true]) ++ loopPairRepeat m`.
  At `q = 0`, `loopUnroll u 0 m = trivialLoopExt u m`.
-/
def loopUnroll (u : List Bool) (q m : Nat) : List Bool :=
  ((u ++ List.replicate (canonicalSuffixShift u 1 + q * (2 * 3 ^ (parityWeight u - 1))) false) ++ [true]) ++
    loopPairRepeat m

theorem loopUnroll_zero_eq_trivialLoopExt (u : List Bool) (m : Nat) :
    loopUnroll u 0 m = trivialLoopExt u m := by
  simp [loopUnroll, trivialLoopExt]

theorem loopUnroll_spec (u : List Bool) (q : Nat) (hu : IsCoreParityWord u) :
    ∀ m : Nat,
      IsCoreParityWord (loopUnroll u q m) ∧
      canonicalSuffixShift (loopUnroll u q m) 1 = 1 ∧
      (loopUnroll u q m).length = backwardOneTotalSteps u q + 2 * m + 1 ∧
      exactBackwardQuotient 1 (loopUnroll u q m) 0 = exactBackwardQuotient 1 u q ∧
      ¬ IsFirstHitOnePair (loopUnroll u q m) 0
  | 0 => by
    let shift := canonicalSuffixShift u 1 + q * (2 * 3 ^ (parityWeight u - 1))
    have hex0 : loopUnroll u q 0 = (u ++ List.replicate shift false) ++ [true] := by
      simp [loopUnroll, loopPairRepeat, shift]
    rcases one_generator_trivial_loop_extension u q hu with ⟨hcore, hcs, hy, hnfh⟩
    rw [← hex0] at hcore hcs hy hnfh
    have hlen : (loopUnroll u q 0).length = backwardOneTotalSteps u q + 2 * 0 + 1 := by
      rw [hex0, List.length_append, List.length_append, List.length_replicate, List.length_singleton]
      rfl
    exact ⟨hcore, hcs, hlen, hy, hnfh⟩
  | m + 1 => by
    rcases loopUnroll_spec u q hu m with ⟨hcore_m, hcs_m, hlen_m, hy_m, _⟩
    rcases one_generator_trivial_loop_extension (loopUnroll u q m) 0 hcore_m with
      ⟨hcore_next, hcs_next, hy_next, hnfh_next⟩
    simp only [Nat.zero_mul, Nat.add_zero, hcs_m] at hcore_next hcs_next hy_next hnfh_next
    have hex_succ : ((loopUnroll u q m ++ List.replicate 1 false) ++ [true]) =
        loopUnroll u q (m + 1) := by
      have hlr : loopPairRepeat (m + 1) = loopPairRepeat m ++ [false, true] := rfl
      have hr1 : List.replicate 1 false = [false] := rfl
      unfold loopUnroll
      rw [hlr, hr1]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [hex_succ] at hcore_next hcs_next hy_next hnfh_next
    have hlen_next : (loopUnroll u q (m + 1)).length =
        backwardOneTotalSteps u q + 2 * (m + 1) + 1 := by
      rw [← hex_succ, List.length_append, List.length_append, List.length_replicate,
          List.length_singleton, hlen_m]
      omega
    exact ⟨hcore_next, hcs_next, hlen_next, hy_next.trans hy_m, hnfh_next⟩

theorem trivialLoopExt_singleton_true :
    ∀ m : Nat, trivialLoopExt [true] m = [true] ++ loopPairRepeat (m + 1)
  | 0 => by decide
  | m + 1 => by
    have hcs1 : canonicalSuffixShift [true] 1 = 1 := by decide
    have hex : trivialLoopExt [true] (m + 1) = trivialLoopExt [true] m ++ [false, true] := by
      unfold trivialLoopExt
      have hlr : loopPairRepeat (m + 1) = loopPairRepeat m ++ [false, true] := rfl
      rw [hlr, ← List.append_assoc]
    rw [hex, trivialLoopExt_singleton_true m]
    have hlr2 : loopPairRepeat (m + 2) = loopPairRepeat (m + 1) ++ [false, true] := rfl
    rw [hlr2, ← List.append_assoc]

/--
  Theorem W9.4a (`global_one_generator_collision_classification`, `zero custom axioms`):
  Complete Global `(u_1, q_1)` vs `(u_2, q_2)` Collision Classification Across ALL `CoreWords × Nat`:
  1. **Universal `q ≥ 1` First-Hit & Global `IsFirstHitOnePair` Injectivity (`∀ w ≥ 1`)**:
     Every `(u, q)` with `IsCoreParityWord u` and `q ≥ 1` satisfies `IsFirstHitOnePair u q`,
     and `(u, q) ↦ exactBackwardQuotient 1 u q` is globally injective across ALL `IsFirstHitOnePair`!
  2. **Unrestricted `q_1 ≥ 1, q_2 ≥ 1` Global Injectivity**:
     For ALL core words `u_1, u_2` (including `w = 1`) and ALL `q_1 ≥ 1, q_2 ≥ 1`,
       `exactBackwardQuotient 1 u1 q1 = exactBackwardQuotient 1 u2 q2 -> u1 = u2 ∧ q1 = q2`!
  3. **Exact Mixed `q_1 = 0, q_2 ≥ 1` Collision Biconditional (`loopUnroll`)**:
     For ALL core words `u_1, u_2` and `q_2 ≥ 1`:
       `exactBackwardQuotient 1 u1 0 = exactBackwardQuotient 1 u2 q2 ↔
        ∃ m : Nat, u1 = loopUnroll u2 q2 m`,
     and EVERY such colliding `u_1` fails `IsFirstHitOnePair u1 0`!
  4. **Complete `q_1 = 0, q_2 = 0` Trichotomy**:
     For ALL core words `u_1, u_2`:
       `exactBackwardQuotient 1 u1 0 = exactBackwardQuotient 1 u2 0 ↔
        u1 = u2 ∨ (∃ m, u2 = trivialLoopExt u1 m) ∨ (∃ m, u1 = trivialLoopExt u2 m)`!
  5. **Exact `y = 1` Fiber & Mixed Collision Witness (`ZPOS_RAY_MIXED_Q0_Q1_COLLISION_5`)**:
     `exactBackwardQuotient 1 u q = 1 ↔ (q = 0 ∧ ∃ m : Nat, u = [true] ++ loopPairRepeat m)`,
     and `(u_2 = [true], q_2 = 1)` collides with `(u_1 = [true, false, false, false, true], q_1 = 0)`
     at `y = 5` (`W9_H4_RAW_MIXED_Q0_QPOS_DISJOINTNESS_WITHOUT_FIRST_HIT`)!
-/
theorem global_one_generator_collision_classification :
    ((∀ (u : List Bool) (q : Nat),
        IsCoreParityWord u -> q ≥ 1 -> IsFirstHitOnePair u q) ∧
     (∀ (u1 u2 : List Bool) (q1 q2 : Nat),
        IsFirstHitOnePair u1 q1 -> IsFirstHitOnePair u2 q2 ->
        exactBackwardQuotient 1 u1 q1 = exactBackwardQuotient 1 u2 q2 ->
        u1 = u2 ∧ q1 = q2)) ∧
    (∀ (u1 u2 : List Bool) (q1 q2 : Nat),
      IsCoreParityWord u1 -> IsCoreParityWord u2 ->
      q1 ≥ 1 -> q2 ≥ 1 ->
      exactBackwardQuotient 1 u1 q1 = exactBackwardQuotient 1 u2 q2 ->
      u1 = u2 ∧ q1 = q2) ∧
    (∀ (u1 u2 : List Bool) (q2 : Nat),
      IsCoreParityWord u1 -> IsCoreParityWord u2 -> q2 ≥ 1 ->
      (exactBackwardQuotient 1 u1 0 = exactBackwardQuotient 1 u2 q2 ↔
       ∃ m : Nat, u1 = loopUnroll u2 q2 m) ∧
      (exactBackwardQuotient 1 u1 0 = exactBackwardQuotient 1 u2 q2 ->
       ¬ IsFirstHitOnePair u1 0)) ∧
    (∀ (u1 u2 : List Bool),
      IsCoreParityWord u1 -> IsCoreParityWord u2 ->
      (exactBackwardQuotient 1 u1 0 = exactBackwardQuotient 1 u2 0 ↔
       u1 = u2 ∨ (∃ m : Nat, u2 = trivialLoopExt u1 m) ∨ (∃ m : Nat, u1 = trivialLoopExt u2 m))) ∧
    ((∀ (u : List Bool) (q : Nat),
        IsCoreParityWord u ->
        (exactBackwardQuotient 1 u q = 1 ↔
         q = 0 ∧ ∃ m : Nat, u = [true] ++ loopPairRepeat m)) ∧
     exactBackwardQuotient 1 [true] 1 = 5 ∧
     loopUnroll [true] 1 0 = [true, false, false, false, true] ∧
     exactBackwardQuotient 1 [true, false, false, false, true] 0 = 5 ∧
     ¬ IsFirstHitOnePair [true, false, false, false, true] 0) := by
  have hinj_fh := first_hit_ray_global_disjointness_and_q0_necessity.1
  have hinj_qpos : ∀ (u1 u2 : List Bool) (q1 q2 : Nat),
      IsCoreParityWord u1 -> IsCoreParityWord u2 ->
      q1 ≥ 1 -> q2 ≥ 1 ->
      exactBackwardQuotient 1 u1 q1 = exactBackwardQuotient 1 u2 q2 ->
      u1 = u2 ∧ q1 = q2 := by
    intro u1 u2 q1 q2 hu1 hu2 hq1 hq2 heq
    exact hinj_fh u1 u2 q1 q2
      (one_generator_q_pos_all_weights_first_hit u1 q1 hu1 hq1)
      (one_generator_q_pos_all_weights_first_hit u2 q2 hu2 hq2)
      heq
  -- Mixed `q1 = 0, q2 ≥ 1` biconditional:
  have hmixed : ∀ (u1 u2 : List Bool) (q2 : Nat),
      IsCoreParityWord u1 -> IsCoreParityWord u2 -> q2 ≥ 1 ->
      (exactBackwardQuotient 1 u1 0 = exactBackwardQuotient 1 u2 q2 ↔
       ∃ m : Nat, u1 = loopUnroll u2 q2 m) ∧
      (exactBackwardQuotient 1 u1 0 = exactBackwardQuotient 1 u2 q2 ->
       ¬ IsFirstHitOnePair u1 0) := by
    intro u1 u2 q2 hu1 hu2 hq2
    have hfh2 : IsFirstHitOnePair u2 q2 :=
      one_generator_q_pos_all_weights_first_hit u2 q2 hu2 hq2
    have hiff : exactBackwardQuotient 1 u1 0 = exactBackwardQuotient 1 u2 q2 ↔
        ∃ m : Nat, u1 = loopUnroll u2 q2 m := by
      constructor
      · intro hy_eq
        let y := exactBackwardQuotient 1 u2 q2
        let sh2 := canonicalSuffixShift u2 1 + q2 * (2 * 3 ^ (parityWeight u2 - 1))
        let K2 := backwardOneTotalSteps u2 q2
        have hK2_eq : K2 = u2.length + sh2 := rfl
        rcases one_generator_pos_odd_and_reaches_one u2 q2 hu2 with ⟨_, _, heq2, hiter2⟩
        change 2 ^ K2 = 3 ^ parityWeight u2 * y + affineCarry u2 at heq2
        change collatzIter K2 y = 1 at hiter2
        rcases affineCarry_append_replicate_false u2 sh2 with ⟨hwt_v2, hcar_v2⟩
        have hv2_len : (u2 ++ List.replicate sh2 false).length = K2 := by
          rw [List.length_append, List.length_replicate]; rfl
        have hv2_aff : 2 ^ (u2 ++ List.replicate sh2 false).length * 1 =
            3 ^ parityWeight (u2 ++ List.replicate sh2 false) * y +
              affineCarry (u2 ++ List.replicate sh2 false) := by
          rw [Nat.mul_one, hv2_len, hwt_v2, hcar_v2]; exact heq2
        have hpar_K2 : u2 ++ List.replicate sh2 false = parityOfIter K2 y := by
          have hp := eq_parityOfIter_of_nat_affine (u2 ++ List.replicate sh2 false) y 1 hv2_aff
          rwa [hv2_len] at hp
        have hpar_u2 : parityOfIter u2.length y = u2 := by
          have hsp := parityOfIter_append_split u2.length sh2 y
          rw [← hK2_eq, ← hpar_K2] at hsp
          have hlen_u2 : u2.length = (parityOfIter u2.length y).length := (parityOfIter_length _ y).symm
          exact (list_append_inj_left_eq_len _ _ _ _ hlen_u2 hsp).1.symm
        -- Recover `u1 = parityOfIter u1.length y` and `collatzIter K1 y = 1`:
        rcases one_generator_pos_odd_and_reaches_one u1 0 hu1 with ⟨_, _, heq1, hiter1⟩
        rw [hy_eq] at heq1 hiter1
        let a1 := canonicalSuffixShift u1 1
        let K1 := u1.length + a1
        have hsteps1 : backwardOneTotalSteps u1 0 = K1 := by
          unfold backwardOneTotalSteps; dsimp [K1, a1]; omega
        rw [hsteps1] at heq1 hiter1
        change collatzIter K1 y = 1 at hiter1
        rcases affineCarry_append_replicate_false u1 a1 with ⟨hwt_v1, hcar_v1⟩
        have hv1_len : (u1 ++ List.replicate a1 false).length = K1 := by
          rw [List.length_append, List.length_replicate]
        have hv1_aff : 2 ^ (u1 ++ List.replicate a1 false).length * 1 =
            3 ^ parityWeight (u1 ++ List.replicate a1 false) * y +
              affineCarry (u1 ++ List.replicate a1 false) := by
          rw [Nat.mul_one, hv1_len, hwt_v1, hcar_v1]; exact heq1
        have hpar_u1 : parityOfIter u1.length y = u1 := by
          have hp := eq_parityOfIter_of_nat_affine (u1 ++ List.replicate a1 false) y 1 hv1_aff
          rw [hv1_len] at hp
          have hsp := parityOfIter_append_split u1.length a1 y
          rw [← hp] at hsp
          have hlen_u1 : u1.length = (parityOfIter u1.length y).length := (parityOfIter_length _ y).symm
          exact (list_append_inj_left_eq_len _ _ _ _ hlen_u1 hsp).1.symm
        -- By `IsFirstHitOnePair u2 q2`, `K1 < K2` is impossible, so `K2 ≤ K1`:
        have hK2_le_K1 : K2 ≤ K1 := by
          by_cases hlt : K1 < K2
          · exact False.elim (hfh2.2 K1 hlt hiter1)
          · omega
        -- Prove `K2 < u1.length`:
        have hK2_lt : K2 < u1.length := by
          by_cases hle : u1.length ≤ K2
          · by_cases hu_cmp : u1.length ≤ u2.length
            · -- Then `u2 = u1 ++ _`, so `parityWeight u1 ≤ parityWeight u2`, forcing `a1 < sh2` & `K1 < K2`!
              have hu2_sp : parityOfIter u2.length y =
                  parityOfIter u1.length y ++
                    parityOfIter (u2.length - u1.length) (collatzIter u1.length y) := by
                conv => lhs; rw [show u2.length = u1.length + (u2.length - u1.length) by omega]
                exact parityOfIter_append_split u1.length (u2.length - u1.length) y
              rw [hpar_u2, hpar_u1] at hu2_sp
              have hw_le : parityWeight u1 ≤ parityWeight u2 := by
                rw [hu2_sp, parityWeight_append]; omega
              have hw1_pos : parityWeight u1 ≥ 1 := reverse_head_true_imp_weight_pos u1 hu1.2
              have ha1_lt : a1 < 2 * 3 ^ (parityWeight u1 - 1) :=
                (canonicalSuffixShift_spec_unique u1 1 hw1_pos (by decide)).1
              have hp3_le : 3 ^ (parityWeight u1 - 1) ≤ 3 ^ (parityWeight u2 - 1) := by
                have hd : parityWeight u2 - 1 =
                    (parityWeight u1 - 1) + ((parityWeight u2 - 1) - (parityWeight u1 - 1)) := by omega
                rw [hd, Nat.pow_add]
                simpa using Nat.mul_le_mul_left (3 ^ (parityWeight u1 - 1))
                  (pow3_pos_nat ((parityWeight u2 - 1) - (parityWeight u1 - 1)))
              have hq2_mul : 2 * 3 ^ (parityWeight u2 - 1) ≤
                  q2 * (2 * 3 ^ (parityWeight u2 - 1)) := by
                simpa using Nat.mul_le_mul_right (2 * 3 ^ (parityWeight u2 - 1)) hq2
              have ha1_lt_sh2 : a1 < sh2 := by dsimp [sh2]; omega
              have hK1_lt_K2 : K1 < K2 := by dsimp [K1]; rw [hK2_eq]; omega
              omega
            · -- `u2.length < u1.length ≤ K2`: last bit `true` of `u1` lands inside `replicate sh2 false`!
              have hsp : parityOfIter K2 y =
                  parityOfIter u1.length y ++
                    parityOfIter (K2 - u1.length) (collatzIter u1.length y) := by
                conv => lhs; rw [show K2 = u1.length + (K2 - u1.length) by omega]
                exact parityOfIter_append_split u1.length (K2 - u1.length) y
              rw [← hpar_K2, hpar_u1] at hsp
              rcases list_eq_append_true_of_reverse_head u1 hu1.2 with ⟨v1, hv1_eq⟩
              have hv1_ge : u2.length ≤ v1.length := by
                have hl : u1.length = v1.length + 1 := by
                  rw [hv1_eq, List.length_append, List.length_singleton]
                omega
              rw [hv1_eq] at hsp
              exact False.elim (prefix_append_true_of_append_replicate_false_w8 u2 v1 _ sh2 hv1_ge hsp)
          · omega
        let d := u1.length - K2
        have hd_pos : d ≥ 1 := by dsimp [d]; omega
        have hu1_split : u1 = (u2 ++ List.replicate sh2 false) ++ parityOfIter d 1 := by
          rw [← hpar_u1, show u1.length = K2 + d by dsimp [d]; omega,
              parityOfIter_append_split K2 d y, ← hpar_K2, hiter2]
        by_cases hd_ev : d % 2 = 0
        · let m := (d - 2) / 2
          have hd_eq : d = 2 * m + 2 := by dsimp [m]; omega
          rw [hd_eq, (parityOfIter_one_odd_even_w8 m).2] at hu1_split
          have hlast_false : u1.reverse.head? = some false := by
            rw [hu1_split, ← List.append_assoc, List.reverse_append]; rfl
          have htr := hu1.2
          rw [hlast_false] at htr
          cases htr
        · let m := (d - 1) / 2
          have hd_eq : d = 2 * m + 1 := by dsimp [m]; omega
          refine ⟨m, ?_⟩
          rw [hd_eq, (parityOfIter_one_odd_even_w8 m).1] at hu1_split
          unfold loopUnroll
          change u1 = ((u2 ++ List.replicate sh2 false) ++ [true]) ++ loopPairRepeat m
          simp only [hu1_split, List.append_assoc]
      · rintro ⟨m, rfl⟩
        exact (loopUnroll_spec u2 q2 hu2 m).2.2.2.1
    refine ⟨hiff, fun hy_eq => ?_⟩
    rcases hiff.mp hy_eq with ⟨m, rfl⟩
    exact (loopUnroll_spec u2 q2 hu2 m).2.2.2.2
  -- Complete `q1 = 0, q2 = 0` trichotomy:
  have hq0_tri : ∀ (u1 u2 : List Bool),
      IsCoreParityWord u1 -> IsCoreParityWord u2 ->
      (exactBackwardQuotient 1 u1 0 = exactBackwardQuotient 1 u2 0 ↔
       u1 = u2 ∨ (∃ m : Nat, u2 = trivialLoopExt u1 m) ∨ (∃ m : Nat, u1 = trivialLoopExt u2 m)) := by
    intro u1 u2 hu1 hu2
    constructor
    · intro hy_eq
      by_cases hlt : u1.length < u2.length
      · exact Or.inr (Or.inl ((q0_cross_scale_leaf_collision_iff_trivial_loop.1 u1 u2 hu1 hu2 hlt).mp hy_eq))
      · by_cases hgt : u2.length < u1.length
        · exact Or.inr (Or.inr ((q0_cross_scale_leaf_collision_iff_trivial_loop.1 u2 u1 hu2 hu1 hgt).mp hy_eq.symm))
        · left
          have hlen_eq : u1.length = u2.length := by omega
          let y := exactBackwardQuotient 1 u1 0
          have hpar_word : ∀ u : List Bool, IsCoreParityWord u ->
              exactBackwardQuotient 1 u 0 = y -> parityOfIter u.length y = u := by
            intro u hu hy_u
            rcases one_generator_pos_odd_and_reaches_one u 0 hu with ⟨_, _, heq, _⟩
            rw [hy_u] at heq
            let a := canonicalSuffixShift u 1
            have hst : backwardOneTotalSteps u 0 = u.length + a := by
              unfold backwardOneTotalSteps; dsimp [a]; omega
            rw [hst] at heq
            rcases affineCarry_append_replicate_false u a with ⟨hwt_v, hcar_v⟩
            have hv_len : (u ++ List.replicate a false).length = u.length + a := by
              rw [List.length_append, List.length_replicate]
            have hv_aff : 2 ^ (u ++ List.replicate a false).length * 1 =
                3 ^ parityWeight (u ++ List.replicate a false) * y +
                  affineCarry (u ++ List.replicate a false) := by
              rw [Nat.mul_one, hv_len, hwt_v, hcar_v]; exact heq
            have hp := eq_parityOfIter_of_nat_affine (u ++ List.replicate a false) y 1 hv_aff
            rw [hv_len] at hp
            have hsp := parityOfIter_append_split u.length a y
            rw [← hp] at hsp
            have hlu : u.length = (parityOfIter u.length y).length := (parityOfIter_length _ y).symm
            exact (list_append_inj_left_eq_len _ _ _ _ hlu hsp).1.symm
          have hp1 := hpar_word u1 hu1 rfl
          have hp2 := hpar_word u2 hu2 hy_eq.symm
          rw [← hlen_eq] at hp2
          exact hp1.symm.trans hp2
    · rintro (rfl | ⟨m, rfl⟩ | ⟨m, rfl⟩)
      · rfl
      · exact (trivialLoopExt_spec u1 hu1 m).2.2.2.1.symm
      · exact (trivialLoopExt_spec u2 hu2 m).2.2.2.1
  -- Exact `y = 1` fiber characterization:
  have hy1_fiber : ∀ (u : List Bool) (q : Nat),
      IsCoreParityWord u ->
      (exactBackwardQuotient 1 u q = 1 ↔
       q = 0 ∧ ∃ m : Nat, u = [true] ++ loopPairRepeat m) := by
    intro u q hu
    constructor
    · intro hy1
      cases q with
      | succ q' =>
        have hfh := one_generator_q_pos_all_weights_first_hit u (q' + 1) hu (by omega)
        have hgt1 := (first_hit_one_pair_sound_and_injective u u (q' + 1) (q' + 1) hfh hfh).1
        rw [hy1] at hgt1
        omega
      | zero =>
        refine ⟨rfl, ?_⟩
        have h1_tr : exactBackwardQuotient 1 [true] 0 = 1 := by decide
        have htri := (hq0_tri [true] u ⟨rfl, rfl⟩ hu).mp (h1_tr.trans hy1.symm)
        rcases htri with rfl | ⟨m, rfl⟩ | ⟨m, heq_rev⟩
        · exact ⟨0, rfl⟩
        · exact ⟨m + 1, trivialLoopExt_singleton_true m⟩
        · exfalso
          have hlen := (trivialLoopExt_spec u hu m).2.2.1
          rw [← heq_rev] at hlen
          have hl1 : [true].length = 1 := rfl
          have hu_len : u.length ≥ 1 := by
            cases u with | nil => have hh := hu.1; simp at hh | cons _ _ => simp
          have hcs_pos : canonicalSuffixShift u 1 ≥ 1 := by
            have ho := canonicalSuffixShift_append_markov_recurrence.1 u hu.2; omega
          rw [hl1] at hlen
          omega
    · rintro ⟨rfl, m, rfl⟩
      cases m with
      | zero => decide
      | succ m' =>
        rw [← trivialLoopExt_singleton_true m',
            (trivialLoopExt_spec [true] ⟨rfl, rfl⟩ m').2.2.2.1]
        decide
  refine ⟨⟨one_generator_q_pos_all_weights_first_hit, hinj_fh⟩,
          hinj_qpos, hmixed, hq0_tri,
          ⟨hy1_fiber, by decide, by decide, by decide, ?_⟩⟩
  have hnfh := (loopUnroll_spec [true] 1 ⟨rfl, rfl⟩ 0).2.2.2.2
  have hunr : loopUnroll [true] 1 0 = [true, false, false, false, true] := by decide
  rwa [hunr] at hnfh

-- ----------------------------------------------------------------------------
-- Section 4B: 3-Adic Markov Contraction (`∀ k`) & Mod-18 Suffix Locks (`P2.2`)
-- ----------------------------------------------------------------------------

theorem markovShiftFalse_mod_pow3_formula (j w a : Nat)
    (hw : w ≥ j + 1) (ha : a < 2 * 3 ^ (w - 1)) :
    let M0 := 2 * 3 ^ j
    markovShiftFalse w a % M0 = if a % M0 = 0 then M0 - 1 else a % M0 - 1 := by
  dsimp only
  let M0 := 2 * 3 ^ j
  have hM0_ge2 : M0 ≥ 2 := by dsimp [M0]; have hp := pow3_pos_nat j; omega
  have hP_fac : 2 * 3 ^ (w - 1) = M0 * 3 ^ (w - 1 - j) := by
    dsimp [M0]
    rw [Nat.mul_assoc 2 (3 ^ j), ← Nat.pow_add 3 j (w - 1 - j),
        show j + (w - 1 - j) = w - 1 by omega]
  unfold markovShiftFalse
  by_cases ha1 : a ≥ 1
  · simp only [ha1, ite_true]
    have hdm : a = M0 * (a / M0) + a % M0 := (Nat.div_add_mod a M0).symm
    have hlt_m : a % M0 < M0 := Nat.mod_lt a (by omega)
    by_cases hr0 : a % M0 = 0
    · rw [ite_eq_left_iff.mpr (fun h => False.elim (h hr0))]
      have hq_pos : a / M0 ≥ 1 := by
        cases hq : a / M0 with
        | zero => rw [hq, hr0] at hdm; omega
        | succ _ => omega
      have hrew : a - 1 = (M0 - 1) + M0 * (a / M0 - 1) := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
        have hm := Nat.mul_le_mul_left M0 hq_pos
        omega
      rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    · rw [ite_eq_right_iff.mpr (fun h => False.elim (hr0 h))]
      have hrew : a - 1 = (a % M0 - 1) + M0 * (a / M0) := by omega
      rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · simp only [ha1, ite_false]
    have ha0 : a = 0 := by omega
    subst ha0
    simp only [Nat.zero_mod, ite_true]
    have hp_pos := pow3_pos_nat (w - 1 - j)
    have hrew : 2 * 3 ^ (w - 1) - 1 = (M0 - 1) + M0 * (3 ^ (w - 1 - j) - 1) := by
      rw [hP_fac, Nat.mul_sub_left_distrib, Nat.mul_one]
      have hm := Nat.mul_le_mul_left M0 hp_pos
      omega
    rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem markovShiftFalse_congr_mod_pow3 (j w1 w2 a1 a2 : Nat)
    (hw1 : w1 ≥ j + 1) (hw2 : w2 ≥ j + 1)
    (ha1 : a1 < 2 * 3 ^ (w1 - 1)) (ha2 : a2 < 2 * 3 ^ (w2 - 1))
    (hcongr : a1 % (2 * 3 ^ j) = a2 % (2 * 3 ^ j)) :
    markovShiftFalse w1 a1 % (2 * 3 ^ j) = markovShiftFalse w2 a2 % (2 * 3 ^ j) := by
  have f1 := markovShiftFalse_mod_pow3_formula j w1 a1 hw1 ha1
  have f2 := markovShiftFalse_mod_pow3_formula j w2 a2 hw2 ha2
  dsimp only at f1 f2
  rw [f1, f2, hcongr]

theorem markovShiftTrue_contraction_mod_pow3 (j w1 w2 a1 a2 : Nat)
    (hw1 : w1 ≥ j + 1) (hw2 : w2 ≥ j + 1)
    (ha1 : a1 < 2 * 3 ^ (w1 - 1)) (ha2 : a2 < 2 * 3 ^ (w2 - 1))
    (hcongr : a1 % (2 * 3 ^ j) = a2 % (2 * 3 ^ j)) :
    markovShiftTrue w1 a1 % (2 * 3 ^ (j + 1)) =
      markovShiftTrue w2 a2 % (2 * 3 ^ (j + 1)) := by
  let P0 := 2 * 3 ^ j
  let M1 := 3 ^ (j + 1)
  let M2 := 3 ^ (j + 2)
  let P1 := 2 * 3 ^ (j + 1)
  have h2P0_M1 : 2 ^ P0 % M1 = 1 :=
    (pow2_totient_exact_valuation_all_weights (j + 1) (by omega)).2.2.1
  have hpow_mod_eq : ∀ a : Nat, 2 ^ a % M1 = 2 ^ (a % P0) % M1 := by
    intro a
    have hdm : a = P0 * (a / P0) + a % P0 := (Nat.div_add_mod a P0).symm
    have hp_mul : (2 ^ P0) ^ (a / P0) % M1 = 1 := by
      have hM1_gt1 : 1 < M1 := by dsimp [M1]; rw [Nat.pow_succ]; have := pow3_pos_nat j; omega
      rw [pow_mod_eq_of_mod_eq_w5 M1 (2 ^ P0) 1 (by rw [h2P0_M1, Nat.mod_eq_of_lt hM1_gt1]) (a / P0),
          Nat.one_pow]
      exact Nat.mod_eq_of_lt hM1_gt1
    conv => lhs; rw [hdm]
    rw [Nat.pow_add 2 (P0 * (a / P0)) (a % P0), ← pow_pow_eq_mul_w5 2 P0 (a / P0),
        Nat.mul_mod, hp_mul, Nat.one_mul, Nat.mod_mod]
  have h2a_eq : 2 ^ a1 % M1 = 2 ^ a2 % M1 := by
    rw [hpow_mod_eq a1, hpow_mod_eq a2, hcongr]
  have hM2_eq : M2 = 3 * M1 := by dsimp [M2, M1]; rw [Nat.pow_succ, Nat.mul_comm]
  have ht_eq : (3 * 2 ^ a1 + 1) % M2 = (3 * 2 ^ a2 + 1) % M2 := by
    rw [hM2_eq,
        mul3_add1_mod_mul3_w8 (2 ^ a1) M1 (pow3_pos_nat (j + 1)),
        mul3_add1_mod_mul3_w8 (2 ^ a2) M1 (pow3_pos_nat (j + 1)),
        h2a_eq]
  let e1 := dlog2ModPow3 (w1 + 1) (3 * 2 ^ a1 + 1)
  let e2 := dlog2ModPow3 (w2 + 1) (3 * 2 ^ a2 + 1)
  have hdlog_m2 : ∀ (w a : Nat), w ≥ j + 1 ->
      2 ^ (dlog2ModPow3 (w + 1) (3 * 2 ^ a + 1)) % M2 = (3 * 2 ^ a + 1) % M2 := by
    intro w a hw
    rcases dlog2ModPow3_spec (w + 1) (3 * 2 ^ a + 1) (by omega) (by omega) with ⟨_, hmod⟩
    have hsp : 3 ^ (w + 1) = M2 * 3 ^ (w - 1 - j) := by
      dsimp [M2]
      rw [← Nat.pow_add 3 (j + 2) (w - 1 - j), show j + 2 + (w - 1 - j) = w + 1 by omega]
    have hm_l := mod_mul_mod_eq (2 ^ dlog2ModPow3 (w + 1) (3 * 2 ^ a + 1)) M2 (3 ^ (w - 1 - j))
    have hm_r := mod_mul_mod_eq (3 * 2 ^ a + 1) M2 (3 ^ (w - 1 - j))
    rw [← hsp] at hm_l hm_r
    rw [← hm_l, hmod, hm_r]
  have he12_m2 : 2 ^ e1 % M2 = 2 ^ e2 % M2 :=
    (hdlog_m2 w1 a1 hw1).trans (ht_eq.trans (hdlog_m2 w2 a2 hw2).symm)
  have h2P1_M2 : 2 ^ P1 % M2 = 1 :=
    (pow2_totient_exact_valuation_all_weights (j + 2) (by omega)).2.2.1
  have hpow_P1 : ∀ e : Nat, 2 ^ e % M2 = 2 ^ (e % P1) % M2 := by
    intro e
    have hdm : e = P1 * (e / P1) + e % P1 := (Nat.div_add_mod e P1).symm
    have hp_mul : (2 ^ P1) ^ (e / P1) % M2 = 1 := by
      have hM2_gt1 : 1 < M2 := by dsimp [M2]; rw [Nat.pow_succ]; have := pow3_pos_nat (j + 1); omega
      rw [pow_mod_eq_of_mod_eq_w5 M2 (2 ^ P1) 1 (by rw [h2P1_M2, Nat.mod_eq_of_lt hM2_gt1]) (e / P1),
          Nat.one_pow]
      exact Nat.mod_eq_of_lt hM2_gt1
    conv => lhs; rw [hdm]
    rw [Nat.pow_add 2 (P1 * (e / P1)) (e % P1), ← pow_pow_eq_mul_w5 2 P1 (e / P1),
        Nat.mul_mod, hp_mul, Nat.one_mul, Nat.mod_mod]
  have hP1_pos : P1 ≥ 6 := by
    dsimp [P1]; rw [Nat.pow_succ 3 j]; have := pow3_pos_nat j; omega
  have he_mod_eq : e1 % P1 = e2 % P1 :=
    pow2_inj_mod_pow3_w8 (j + 2) (e1 % P1) (e2 % P1) (by omega)
      (by show e1 % P1 < P1; exact Nat.mod_lt e1 (by omega))
      (by show e2 % P1 < P1; exact Nat.mod_lt e2 (by omega))
      ((hpow_P1 e1).symm.trans (he12_m2.trans (hpow_P1 e2)))
  -- Neither `e1 % P1` nor `e2 % P1` can be `0`, because `(e - 1) % 6 ∈ {1, 3}` and `6 ∣ P1`:
  have hsub1_mod : ∀ (w a : Nat), w ≥ j + 1 -> a < 2 * 3 ^ (w - 1) ->
      let e := dlog2ModPow3 (w + 1) (3 * 2 ^ a + 1)
      (e - 1) % P1 = e % P1 - 1 := by
    intro w a hw ha_lt
    dsimp only
    let e := dlog2ModPow3 (w + 1) (3 * 2 ^ a + 1)
    have hm6 := (canonicalSuffixShift_markov_bijection_and_mod6_lock.2.1 w a (by omega) ha_lt).2
    unfold markovShiftTrue at hm6
    change (e - 1) % 6 = 1 ∨ (e - 1) % 6 = 3 at hm6
    have he_ge2 : e ≥ 2 := by
      rcases hm6 with h1 | h3 <;> omega
    have hP1_6 : P1 = 6 * 3 ^ j := by dsimp [P1]; rw [Nat.pow_succ 3 j]; omega
    have hnz : e % P1 ≠ 0 := by
      intro hz
      have hm6_e : e % 6 = 0 := by
        have hm := mod_mul_mod_eq e 6 (3 ^ j)
        rw [← hP1_6, hz] at hm
        exact hm.symm
      rcases hm6 with h1 | h3 <;> omega
    have hdm : e = P1 * (e / P1) + e % P1 := (Nat.div_add_mod e P1).symm
    have hlt_p1 : e % P1 < P1 := Nat.mod_lt e (by omega)
    have hrew : e - 1 = (e % P1 - 1) + P1 * (e / P1) := by omega
    rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  unfold markovShiftTrue
  rw [hsub1_mod w1 a1 hw1 ha1, hsub1_mod w2 a2 hw2 ha2, he_mod_eq]

theorem markov_tail_contraction :
    ∀ (tail v1 v2 : List Bool) (j : Nat),
      parityWeight v1 ≥ j + 1 ->
      parityWeight v2 ≥ j + 1 ->
      canonicalSuffixShift v1 1 % (2 * 3 ^ j) = canonicalSuffixShift v2 1 % (2 * 3 ^ j) ->
      canonicalSuffixShift (v1 ++ tail) 1 % (2 * 3 ^ (j + parityWeight tail)) =
        canonicalSuffixShift (v2 ++ tail) 1 % (2 * 3 ^ (j + parityWeight tail))
  | [], v1, v2, j, _, _, hcongr => by
    simp [parityWeight, hcongr]
  | false :: rest, v1, v2, j, hw1, hw2, hcongr => by
    have hv1_sp : v1 ++ (false :: rest) = (v1 ++ [false]) ++ rest := by simp
    have hv2_sp : v2 ++ (false :: rest) = (v2 ++ [false]) ++ rest := by simp
    have hwt_f : parityWeight (false :: rest) = parityWeight rest := rfl
    have hwt_v1f : parityWeight (v1 ++ [false]) = parityWeight v1 := by
      rw [parityWeight_append]; rfl
    have hwt_v2f : parityWeight (v2 ++ [false]) = parityWeight v2 := by
      rw [parityWeight_append]; rfl
    have hrec1 : canonicalSuffixShift (v1 ++ [false]) 1 =
        markovShiftFalse (parityWeight v1) (canonicalSuffixShift v1 1) :=
      canonicalSuffixShift_append_markov_recurrence.2.1 v1 (by omega)
    have hrec2 : canonicalSuffixShift (v2 ++ [false]) 1 =
        markovShiftFalse (parityWeight v2) (canonicalSuffixShift v2 1) :=
      canonicalSuffixShift_append_markov_recurrence.2.1 v2 (by omega)
    have ha1_lt := (canonicalSuffixShift_spec_unique v1 1 (by omega) (by decide)).1
    have ha2_lt := (canonicalSuffixShift_spec_unique v2 1 (by omega) (by decide)).1
    have hstep := markovShiftFalse_congr_mod_pow3 j (parityWeight v1) (parityWeight v2)
      (canonicalSuffixShift v1 1) (canonicalSuffixShift v2 1) hw1 hw2 ha1_lt ha2_lt hcongr
    rw [← hrec1, ← hrec2] at hstep
    rw [hv1_sp, hv2_sp, hwt_f]
    exact markov_tail_contraction rest (v1 ++ [false]) (v2 ++ [false]) j
      (by rw [hwt_v1f]; exact hw1) (by rw [hwt_v2f]; exact hw2) hstep
  | true :: rest, v1, v2, j, hw1, hw2, hcongr => by
    have hv1_sp : v1 ++ (true :: rest) = (v1 ++ [true]) ++ rest := by simp
    have hv2_sp : v2 ++ (true :: rest) = (v2 ++ [true]) ++ rest := by simp
    have hwt_t : j + parityWeight (true :: rest) = (j + 1) + parityWeight rest := by
      simp only [parityWeight]; omega
    have hwt_v1t : parityWeight (v1 ++ [true]) = parityWeight v1 + 1 := by
      rw [parityWeight_append]; rfl
    have hwt_v2t : parityWeight (v2 ++ [true]) = parityWeight v2 + 1 := by
      rw [parityWeight_append]; rfl
    have hrec1 : canonicalSuffixShift (v1 ++ [true]) 1 =
        markovShiftTrue (parityWeight v1) (canonicalSuffixShift v1 1) :=
      (canonicalSuffixShift_append_markov_recurrence.2.2 v1 (by omega)).2.2.1
    have hrec2 : canonicalSuffixShift (v2 ++ [true]) 1 =
        markovShiftTrue (parityWeight v2) (canonicalSuffixShift v2 1) :=
      (canonicalSuffixShift_append_markov_recurrence.2.2 v2 (by omega)).2.2.1
    have ha1_lt := (canonicalSuffixShift_spec_unique v1 1 (by omega) (by decide)).1
    have ha2_lt := (canonicalSuffixShift_spec_unique v2 1 (by omega) (by decide)).1
    have hstep := markovShiftTrue_contraction_mod_pow3 j (parityWeight v1) (parityWeight v2)
      (canonicalSuffixShift v1 1) (canonicalSuffixShift v2 1) hw1 hw2 ha1_lt ha2_lt hcongr
    rw [← hrec1, ← hrec2] at hstep
    rw [hv1_sp, hv2_sp, hwt_t]
    exact markov_tail_contraction rest (v1 ++ [true]) (v2 ++ [true]) (j + 1)
      (by rw [hwt_v1t]; omega) (by rw [hwt_v2t]; omega) hstep

theorem canonicalSuffixShift_zero_weight_prefix_invariant :
    ∀ (z suf : List Bool),
      parityWeight z = 0 -> parityWeight suf ≥ 1 ->
      canonicalSuffixShift (z ++ suf) 1 = canonicalSuffixShift suf 1
  | [], suf, _, _ => rfl
  | false :: zr, suf, hz0, hsuf => by
    simp only [parityWeight] at hz0
    have ih := canonicalSuffixShift_zero_weight_prefix_invariant zr suf hz0 hsuf
    rw [List.cons_append]
    -- Show `canonicalSuffixShift (false :: v) 1 = canonicalSuffixShift v 1` for `v := zr ++ suf`:
    let v := zr ++ suf
    have hw_v : parityWeight v ≥ 1 := by
      dsimp [v]; rw [parityWeight_append, hz0, Nat.zero_add]; exact hsuf
    have hwt_fv : parityWeight (false :: v) = parityWeight v := rfl
    have hcar_fv : affineCarry (false :: v) = 2 * affineCarry v := by
      change affineCarry ([false] ++ v) = 2 * affineCarry v
      rw [affineCarry_append]
      have hc0 : affineCarry [false] = 0 := rfl
      have hl1 : [false].length = 1 := rfl
      rw [hc0, hl1, Nat.mul_zero, Nat.zero_add]
    rcases canonicalSuffixShift_spec_unique v 1 hw_v (by decide) with ⟨ha_lt, ha_congr, _⟩
    rcases canonicalSuffixShift_spec_unique (false :: v) 1 (by rw [hwt_fv]; exact hw_v) (by decide) with
      ⟨_, _, huniq_fv⟩
    rw [Nat.mul_one] at ha_congr
    have hfv_eq : canonicalSuffixShift (false :: v) 1 = canonicalSuffixShift v 1 := by
      symm
      apply huniq_fv (canonicalSuffixShift v 1) (by rw [hwt_fv]; exact ha_lt)
      rw [Nat.mul_one, hwt_fv, hcar_fv, List.length_cons,
          show v.length + 1 + canonicalSuffixShift v 1 = 1 + (v.length + canonicalSuffixShift v 1) by omega,
          Nat.pow_add 2 1, Nat.pow_one,
          Nat.mul_mod 2 (2 ^ _) (3 ^ parityWeight v),
          ha_congr, ← Nat.mul_mod]
    exact hfv_eq.trans ih
  | true :: _, _, hz0, _ => by simp [parityWeight] at hz0

theorem split_first_true_of_weight_pos :
    ∀ u : List Bool, parityWeight u ≥ 1 ->
      ∃ (z tail : List Bool),
        parityWeight z = 0 ∧ u = z ++ (true :: tail)
  | [], hw => by simp [parityWeight] at hw
  | true :: tail, _ => ⟨[], tail, rfl, rfl⟩
  | false :: rest, hw => by
    simp only [parityWeight] at hw
    rcases split_first_true_of_weight_pos rest hw with ⟨z, tail, hz0, rfl⟩
    exact ⟨false :: z, tail, hz0, rfl⟩

/--
  Theorem W9.4b (`canonicalSuffixShift_mod18_and_pow3_memory_annihilation`, `zero custom axioms`):
  Universal 3-Adic Markov Prefix-Memory Annihilation (`∀ k`) & Exact Mod-`18` Suffix Locks:
  1. **Sharp Weight-Exact Memory Annihilation (`∀ pref suf`, `parityWeight suf ≥ 1`)**:
       `canonicalSuffixShift (pref ++ suf) 1 % (2 * 3 ^ (parityWeight suf - 1)) =
        canonicalSuffixShift suf 1 % (2 * 3 ^ (parityWeight suf - 1))`!
  2. **Universal `∀ k : Nat` `mod (2 * 3^k)` Prefix-Memory Annihilation**:
     Whenever `parityWeight suf ≥ k + 1`, EVERY prefix `pref : List Bool` is completely
     annihilated modulo `2 * 3 ^ k`:
       `canonicalSuffixShift (pref ++ suf) 1 % (2 * 3 ^ k) =
        canonicalSuffixShift suf 1 % (2 * 3 ^ k)`!
  3. **Exact Mod-`18` Suffix Locks**:
     - For EVERY `pref : List Bool` with `parityWeight pref ≥ 1`:
       * `canonicalSuffixShift (pref ++ [true, true]) 1 % 18 = 9 ∨
          canonicalSuffixShift (pref ++ [true, true]) 1 % 18 = 15` (hence `% 6 = 3`);
       * `canonicalSuffixShift (pref ++ [true, false, true]) 1 % 18 = 1 ∨
          canonicalSuffixShift (pref ++ [true, false, true]) 1 % 18 = 7` (hence `% 6 = 1`);
     - For EVERY `pref : List Bool` (unrestricted, including `pref = []`):
       * `canonicalSuffixShift (pref ++ [true, true, true]) 1 % 18 = 9`!
-/
theorem canonicalSuffixShift_mod18_and_pow3_memory_annihilation :
    (∀ (pref suf : List Bool), parityWeight suf ≥ 1 ->
      canonicalSuffixShift (pref ++ suf) 1 % (2 * 3 ^ (parityWeight suf - 1)) =
        canonicalSuffixShift suf 1 % (2 * 3 ^ (parityWeight suf - 1))) ∧
    (∀ (k : Nat) (pref suf : List Bool), parityWeight suf ≥ k + 1 ->
      canonicalSuffixShift (pref ++ suf) 1 % (2 * 3 ^ k) =
        canonicalSuffixShift suf 1 % (2 * 3 ^ k)) ∧
    (∀ pref : List Bool, parityWeight pref ≥ 1 ->
      (canonicalSuffixShift (pref ++ [true, true]) 1 % 18 = 9 ∨
       canonicalSuffixShift (pref ++ [true, true]) 1 % 18 = 15) ∧
      (canonicalSuffixShift (pref ++ [true, false, true]) 1 % 18 = 1 ∨
       canonicalSuffixShift (pref ++ [true, false, true]) 1 % 18 = 7)) ∧
    (∀ pref : List Bool,
      canonicalSuffixShift (pref ++ [true, true, true]) 1 % 18 = 9) := by
  have hsharp : ∀ (pref suf : List Bool), parityWeight suf ≥ 1 ->
      canonicalSuffixShift (pref ++ suf) 1 % (2 * 3 ^ (parityWeight suf - 1)) =
        canonicalSuffixShift suf 1 % (2 * 3 ^ (parityWeight suf - 1)) := by
    intro pref suf hsuf
    by_cases hwp0 : parityWeight pref = 0
    · rw [canonicalSuffixShift_zero_weight_prefix_invariant pref suf hwp0 hsuf]
    · rcases split_first_true_of_weight_pos suf hsuf with ⟨z, tail, hz0, rfl⟩
      have hsuf_wt : parityWeight (z ++ (true :: tail)) - 1 = parityWeight tail := by
        rw [parityWeight_append, hz0, Nat.zero_add]; simp [parityWeight]
      have hrhs_z : canonicalSuffixShift (z ++ (true :: tail)) 1 =
          canonicalSuffixShift ([true] ++ tail) 1 :=
        canonicalSuffixShift_zero_weight_prefix_invariant z (true :: tail) hz0 (by simp [parityWeight])
      let v1 := (pref ++ z) ++ [true]
      have hlhs_assoc : pref ++ (z ++ (true :: tail)) = v1 ++ tail := by
        dsimp [v1]; simp [List.append_assoc]
      have hv1_wt : parityWeight v1 ≥ 1 := by
        dsimp [v1]; rw [parityWeight_append]; simp [parityWeight]
      have hv1_odd : canonicalSuffixShift v1 1 % 2 = 1 :=
        canonicalSuffixShift_append_markov_recurrence.1 v1
          (by dsimp [v1]; rw [List.reverse_append]; rfl)
      have hv2_odd : canonicalSuffixShift [true] 1 % 2 = 1 := by decide
      have htail := markov_tail_contraction tail v1 [true] 0
        hv1_wt (by decide)
        (by simp only [Nat.pow_zero, Nat.mul_one]; exact hv1_odd.trans hv2_odd.symm)
      simp only [Nat.zero_add] at htail
      rw [hsuf_wt, hlhs_assoc, hrhs_z]
      exact htail
  have hann_k : ∀ (k : Nat) (pref suf : List Bool), parityWeight suf ≥ k + 1 ->
      canonicalSuffixShift (pref ++ suf) 1 % (2 * 3 ^ k) =
        canonicalSuffixShift suf 1 % (2 * 3 ^ k) := by
    intro k pref suf hsuf_k
    have hs := hsharp pref suf (by omega)
    have hfac : 2 * 3 ^ (parityWeight suf - 1) = (2 * 3 ^ k) * 3 ^ (parityWeight suf - 1 - k) := by
      rw [Nat.mul_assoc 2 (3 ^ k), ← Nat.pow_add 3 k (parityWeight suf - 1 - k),
          show k + (parityWeight suf - 1 - k) = parityWeight suf - 1 by omega]
    have hm1 := mod_mul_mod_eq (canonicalSuffixShift (pref ++ suf) 1) (2 * 3 ^ k)
      (3 ^ (parityWeight suf - 1 - k))
    have hm2 := mod_mul_mod_eq (canonicalSuffixShift suf 1) (2 * 3 ^ k)
      (3 ^ (parityWeight suf - 1 - k))
    rw [← hfac] at hm1 hm2
    rw [← hm1, hs, hm2]
  refine ⟨hsharp, hann_k, ?_, ?_⟩
  · intro pref hwp
    by_cases hpar : canonicalSuffixShift pref 1 % 2 = 0
    · have hbase0 : canonicalSuffixShift [true, false] 1 % 2 = 0 := by decide
      have ht_11 := markov_tail_contraction [true, true] pref [true, false] 0
        hwp (by decide) (by simp only [Nat.pow_zero, Nat.mul_one]; exact hpar.trans hbase0.symm)
      have ht_101 := markov_tail_contraction [true, false, true] pref [true, false] 0
        hwp (by decide) (by simp only [Nat.pow_zero, Nat.mul_one]; exact hpar.trans hbase0.symm)
      have hv_11 : canonicalSuffixShift ([true, false] ++ [true, true]) 1 % 18 = 15 := by decide
      have hv_101 : canonicalSuffixShift ([true, false] ++ [true, false, true]) 1 % 18 = 1 := by decide
      refine ⟨Or.inr (ht_11.trans hv_11), Or.inl (ht_101.trans hv_101)⟩
    · have hodd : canonicalSuffixShift pref 1 % 2 = 1 := by omega
      have hbase1 : canonicalSuffixShift [true] 1 % 2 = 1 := by decide
      have ht_11 := markov_tail_contraction [true, true] pref [true] 0
        hwp (by decide) (by simp only [Nat.pow_zero, Nat.mul_one]; exact hodd.trans hbase1.symm)
      have ht_101 := markov_tail_contraction [true, false, true] pref [true] 0
        hwp (by decide) (by simp only [Nat.pow_zero, Nat.mul_one]; exact hodd.trans hbase1.symm)
      have hv_11 : canonicalSuffixShift ([true] ++ [true, true]) 1 % 18 = 9 := by decide
      have hv_101 : canonicalSuffixShift ([true] ++ [true, false, true]) 1 % 18 = 7 := by decide
      refine ⟨Or.inl (ht_11.trans hv_11), Or.inr (ht_101.trans hv_101)⟩
  · intro pref
    have ha := hann_k 2 pref [true, true, true] (by decide)
    have hv : canonicalSuffixShift [true, true, true] 1 % 18 = 9 := by decide
    simpa using ha.trans hv

/--
  Constructive finite bijection lemma on `[0, N)` (`choice-free, zero custom axioms`):
  Every injective function `f : Nat -> Nat` mapping `[0, N)` into `[0, N)` is surjective onto `[0, N)`.
-/
theorem nat_fin_inj_implies_surj :
    ∀ (N : Nat) (f : Nat -> Nat),
      (∀ x : Nat, x < N -> f x < N) ->
      (∀ x1 x2 : Nat, x1 < N -> x2 < N -> f x1 = f x2 -> x1 = x2) ->
      ∀ y : Nat, y < N -> ∃ x : Nat, x < N ∧ f x = y
  | 0, _, _, _, _, hy => by omega
  | n + 1, f, hf_lt, hf_inj, y, hy => by
    cases hfind : findIndexEqAux f n (n + 1) with
    | none =>
      have hnone := (findIndexEqAux_spec f n (n + 1)).2 hfind
      have hlt_n : ∀ x : Nat, x < n + 1 -> f x < n := by
        intro x hx
        have h1 := hf_lt x hx
        have h2 := hnone x hx
        omega
      rcases nat_func_pigeonhole n (n + 1) f hlt_n (by omega) with ⟨i, j, hij, hj_lt, heq⟩
      have hij_eq := hf_inj i j (by omega) hj_lt heq
      omega
    | some x_top =>
      rcases (findIndexEqAux_spec f n (n + 1)).1 x_top hfind with ⟨hx_lt, hx_eq⟩
      by_cases hy_top : y = n
      · subst hy_top
        exact ⟨x_top, hx_lt, hx_eq⟩
      · have hy_lt_n : y < n := by omega
        let g : Nat -> Nat := fun x => if x = x_top then f n else f x
        have hg_lt : ∀ x : Nat, x < n -> g x < n := by
          intro x hx
          dsimp [g]
          by_cases hxx : x = x_top
          · simp only [hxx, ite_true]
            have hfn_lt := hf_lt n (by omega)
            have hfn_ne : f n ≠ n := by
              intro heq_n
              have h_eq := hf_inj n x_top (by omega) hx_lt (heq_n.trans hx_eq.symm)
              omega
            omega
          · simp only [hxx, ite_false]
            have hfx_lt := hf_lt x (by omega)
            have hfx_ne : f x ≠ n := by
              intro heq_x
              exact hxx (hf_inj x x_top (by omega) hx_lt (heq_x.trans hx_eq.symm))
            omega
        have hg_inj : ∀ x1 x2 : Nat, x1 < n -> x2 < n -> g x1 = g x2 -> x1 = x2 := by
          intro x1 x2 hx1 hx2 hgeq
          dsimp [g] at hgeq
          by_cases h1 : x1 = x_top
          · simp only [h1, ite_true] at hgeq
            by_cases h2 : x2 = x_top
            · omega
            · simp only [h2, ite_false] at hgeq
              have hn_eq := hf_inj n x2 (by omega) (by omega) hgeq
              omega
          · simp only [h1, ite_false] at hgeq
            by_cases h2 : x2 = x_top
            · simp only [h2, ite_true] at hgeq
              have hn_eq := hf_inj x1 n (by omega) (by omega) hgeq
              omega
            · simp only [h2, ite_false] at hgeq
              exact hf_inj x1 x2 (by omega) (by omega) hgeq
        rcases nat_fin_inj_implies_surj n g hg_lt hg_inj y hy_lt_n with ⟨z, hz_lt, hgz⟩
        dsimp [g] at hgz
        by_cases hzx : z = x_top
        · simp only [hzx, ite_true] at hgz
          exact ⟨n, by omega, hgz⟩
        · simp only [hzx, ite_false] at hgz
          exact ⟨z, by omega, hgz⟩

/-- Multi-step canonical suffix Markov operator along `tail : List Bool` starting at weight `w`. -/
def iterMarkovShift : List Bool -> Nat -> Nat -> Nat
  | [], _, a => a
  | false :: rest, w, a => iterMarkovShift rest w (markovShiftFalse w a)
  | true :: rest, w, a => iterMarkovShift rest (w + 1) (markovShiftTrue w a)

theorem iterMarkovShift_append_canonical :
    ∀ (tail u : List Bool), parityWeight u ≥ 1 ->
      canonicalSuffixShift (u ++ tail) 1 =
        iterMarkovShift tail (parityWeight u) (canonicalSuffixShift u 1)
  | [], u, _ => by simp [iterMarkovShift]
  | false :: rest, u, hwu => by
    have hsp : u ++ (false :: rest) = (u ++ [false]) ++ rest := by simp
    have hwt : parityWeight (u ++ [false]) = parityWeight u := by rw [parityWeight_append]; rfl
    have hrec : canonicalSuffixShift (u ++ [false]) 1 =
        markovShiftFalse (parityWeight u) (canonicalSuffixShift u 1) :=
      canonicalSuffixShift_append_markov_recurrence.2.1 u hwu
    rw [hsp, iterMarkovShift_append_canonical rest (u ++ [false]) (by rw [hwt]; exact hwu),
        hwt, hrec]
    rfl
  | true :: rest, u, hwu => by
    have hsp : u ++ (true :: rest) = (u ++ [true]) ++ rest := by simp
    have hwt : parityWeight (u ++ [true]) = parityWeight u + 1 := by rw [parityWeight_append]; rfl
    have hrec : canonicalSuffixShift (u ++ [true]) 1 =
        markovShiftTrue (parityWeight u) (canonicalSuffixShift u 1) :=
      (canonicalSuffixShift_append_markov_recurrence.2.2 u hwu).2.2.1
    rw [hsp, iterMarkovShift_append_canonical rest (u ++ [true]) (by rw [hwt]; omega),
        hwt, hrec]
    rfl

theorem iterMarkovShift_range_and_inj :
    ∀ (tail : List Bool) (w : Nat), w ≥ 1 ->
      (∀ a : Nat, a < 2 * 3 ^ (w - 1) ->
        iterMarkovShift tail w a < 2 * 3 ^ (w + parityWeight tail - 1)) ∧
      (∀ a1 a2 : Nat, a1 < 2 * 3 ^ (w - 1) -> a2 < 2 * 3 ^ (w - 1) ->
        iterMarkovShift tail w a1 = iterMarkovShift tail w a2 -> a1 = a2)
  | [], w, _ => ⟨fun _ ha => by simpa [iterMarkovShift, parityWeight] using ha,
                  fun _ _ _ _ heq => by simpa [iterMarkovShift] using heq⟩
  | false :: rest, w, hw => by
    rcases iterMarkovShift_range_and_inj rest w hw with ⟨hr_rest, hinj_rest⟩
    refine ⟨?_, ?_⟩
    · intro a ha
      have hf := (canonicalSuffixShift_markov_bijection_and_mod6_lock.1 w a hw ha).1
      simpa [iterMarkovShift, parityWeight] using hr_rest (markovShiftFalse w a) hf
    · intro a1 a2 ha1 ha2 heq
      rcases canonicalSuffixShift_markov_bijection_and_mod6_lock.1 w a1 hw ha1 with ⟨hf1_lt, _, hinv1, _⟩
      rcases canonicalSuffixShift_markov_bijection_and_mod6_lock.1 w a2 hw ha2 with ⟨hf2_lt, _, hinv2, _⟩
      have hmid := hinj_rest _ _ hf1_lt hf2_lt heq
      rw [← hinv1, ← hinv2, hmid]
  | true :: rest, w, hw => by
    rcases iterMarkovShift_range_and_inj rest (w + 1) (by omega) with ⟨hr_rest, hinj_rest⟩
    have hwt_eq : w + parityWeight (true :: rest) - 1 = (w + 1) + parityWeight rest - 1 := by
      simp only [parityWeight]; omega
    refine ⟨?_, ?_⟩
    · intro a ha
      have ht : markovShiftTrue w a < 2 * 3 ^ ((w + 1) - 1) := by
        simpa using (canonicalSuffixShift_markov_bijection_and_mod6_lock.2.1 w a hw ha).1
      rw [hwt_eq]
      exact hr_rest (markovShiftTrue w a) ht
    · intro a1 a2 ha1 ha2 heq
      have ht1 : markovShiftTrue w a1 < 2 * 3 ^ ((w + 1) - 1) := by
        simpa using (canonicalSuffixShift_markov_bijection_and_mod6_lock.2.1 w a1 hw ha1).1
      have ht2 : markovShiftTrue w a2 < 2 * 3 ^ ((w + 1) - 1) := by
        simpa using (canonicalSuffixShift_markov_bijection_and_mod6_lock.2.1 w a2 hw ha2).1
      have hmid := hinj_rest _ _ ht1 ht2 heq
      exact canonicalSuffixShift_markov_bijection_and_mod6_lock.2.2.1 w a1 a2 hw ha1 ha2 hmid

theorem iterMarkovShift_congr_mod_pow3 :
    ∀ (tail : List Bool) (j w1 w2 a1 a2 : Nat),
      w1 ≥ j + 1 -> w2 ≥ j + 1 ->
      a1 < 2 * 3 ^ (w1 - 1) -> a2 < 2 * 3 ^ (w2 - 1) ->
      a1 % (2 * 3 ^ j) = a2 % (2 * 3 ^ j) ->
      iterMarkovShift tail w1 a1 % (2 * 3 ^ (j + parityWeight tail)) =
        iterMarkovShift tail w2 a2 % (2 * 3 ^ (j + parityWeight tail))
  | [], _, _, _, _, _, _, _, _, _, hcongr => by
    simpa [iterMarkovShift, parityWeight] using hcongr
  | false :: rest, j, w1, w2, a1, a2, hw1, hw2, ha1, ha2, hcongr => by
    have hf1 := (canonicalSuffixShift_markov_bijection_and_mod6_lock.1 w1 a1 (by omega) ha1).1
    have hf2 := (canonicalSuffixShift_markov_bijection_and_mod6_lock.1 w2 a2 (by omega) ha2).1
    have hstep := markovShiftFalse_congr_mod_pow3 j w1 w2 a1 a2 hw1 hw2 ha1 ha2 hcongr
    exact iterMarkovShift_congr_mod_pow3 rest j w1 w2
      (markovShiftFalse w1 a1) (markovShiftFalse w2 a2) hw1 hw2 hf1 hf2 hstep
  | true :: rest, j, w1, w2, a1, a2, hw1, hw2, ha1, ha2, hcongr => by
    have ht1 : markovShiftTrue w1 a1 < 2 * 3 ^ ((w1 + 1) - 1) := by
      simpa using (canonicalSuffixShift_markov_bijection_and_mod6_lock.2.1 w1 a1 (by omega) ha1).1
    have ht2 : markovShiftTrue w2 a2 < 2 * 3 ^ ((w2 + 1) - 1) := by
      simpa using (canonicalSuffixShift_markov_bijection_and_mod6_lock.2.1 w2 a2 (by omega) ha2).1
    have hstep := markovShiftTrue_contraction_mod_pow3 j w1 w2 a1 a2 hw1 hw2 ha1 ha2 hcongr
    have hwt : j + parityWeight (true :: rest) = (j + 1) + parityWeight rest := by
      simp only [parityWeight]; omega
    rw [hwt]
    exact iterMarkovShift_congr_mod_pow3 rest (j + 1) (w1 + 1) (w2 + 1)
      (markovShiftTrue w1 a1) (markovShiftTrue w2 a2) (by omega) (by omega) ht1 ht2 hstep

/--
  Theorem W9.4c (`markovShift_mod18_bijection_and_multistep_fiber_equidistribution`, `zero custom axioms`):
  Complete Mod-`18` Markov Image Law & Universal Multi-Step `3^(w - 1 - j)` Fiber Equidistribution:
  1. **Multi-Step Markov Operator & Global Injectivity**:
     For ALL `u tail : List Bool` with `parityWeight u ≥ 1`,
     `canonicalSuffixShift (u ++ tail) 1 = iterMarkovShift tail (parityWeight u) (canonicalSuffixShift u 1)`,
     and for every `w ≥ 1`, `iterMarkovShift tail w` maps `[0, 2 * 3 ^ (w - 1))` injectively into
     `[0, 2 * 3 ^ (w + parityWeight tail - 1))`.
  2. **Complete Mod-`18` Markov Bijection & `12 / 18` Forbidden-Residue Law**:
     For EVERY weight `w ≥ 2` and `a < 2 * 3 ^ (w - 1)`, `markovShiftTrue w a % 18` is uniquely
     determined by `a % 6` via `(0, 1, 2, 3, 4, 5) ↦ (1, 15, 7, 9, 13, 3)`, confining EVERY core
     parity word `u` with `parityWeight u ≥ 3` strictly to `{1, 3, 7, 9, 13, 15} mod 18`
     (eliminating `12 / 18 = 2 / 3` of all mod-`18` residue classes!).
  3. **Universal Multi-Step Fiber Equidistribution (`∀ tail, ∀ w ≥ j + 1, ∀ r0 < 2 * 3 ^ j`)**:
     Along the `3 ^ (w - 1 - j)`-element residue fiber `a_t := r0 + 2 * 3 ^ j * t`
     (`t < 3 ^ (w - 1 - j)`), `iterMarkovShift tail w` maps `{0, ..., 3 ^ (w - 1 - j) - 1}`
     **bijectively and uniformly** onto the arithmetic progression
       `{(iterMarkovShift tail w r0 % (2 * 3 ^ (j + parityWeight tail))) +
         2 * 3 ^ (j + parityWeight tail) * q | q < 3 ^ (w - 1 - j)}`!
-/
theorem markovShift_mod18_bijection_and_multistep_fiber_equidistribution :
    ((∀ (u tail : List Bool), parityWeight u ≥ 1 ->
        canonicalSuffixShift (u ++ tail) 1 =
          iterMarkovShift tail (parityWeight u) (canonicalSuffixShift u 1)) ∧
     (∀ (tail : List Bool) (w : Nat), w ≥ 1 ->
        (∀ a : Nat, a < 2 * 3 ^ (w - 1) ->
          iterMarkovShift tail w a < 2 * 3 ^ (w + parityWeight tail - 1)) ∧
        (∀ a1 a2 : Nat, a1 < 2 * 3 ^ (w - 1) -> a2 < 2 * 3 ^ (w - 1) ->
          iterMarkovShift tail w a1 = iterMarkovShift tail w a2 -> a1 = a2))) ∧
    ((∀ (w a : Nat), w ≥ 2 -> a < 2 * 3 ^ (w - 1) ->
        (a % 6 = 0 -> markovShiftTrue w a % 18 = 1) ∧
        (a % 6 = 1 -> markovShiftTrue w a % 18 = 15) ∧
        (a % 6 = 2 -> markovShiftTrue w a % 18 = 7) ∧
        (a % 6 = 3 -> markovShiftTrue w a % 18 = 9) ∧
        (a % 6 = 4 -> markovShiftTrue w a % 18 = 13) ∧
        (a % 6 = 5 -> markovShiftTrue w a % 18 = 3)) ∧
     (∀ u : List Bool, IsCoreParityWord u -> parityWeight u ≥ 3 ->
        canonicalSuffixShift u 1 % 18 ∈ ([1, 3, 7, 9, 13, 15] : List Nat))) ∧
    (∀ (tail : List Bool) (j w r0 : Nat),
      w ≥ j + 1 -> r0 < 2 * 3 ^ j ->
      let M0 := 2 * 3 ^ j
      let Mk := 2 * 3 ^ (j + parityWeight tail)
      let N := 3 ^ (w - 1 - j)
      let base := iterMarkovShift tail w r0 % Mk
      (∀ t : Nat, t < N ->
        ∃ q : Nat, q < N ∧ iterMarkovShift tail w (r0 + M0 * t) = base + Mk * q) ∧
      (∀ q : Nat, q < N ->
        ∃ t : Nat, t < N ∧
          iterMarkovShift tail w (r0 + M0 * t) = base + Mk * q ∧
          ∀ t' : Nat, t' < N ->
            iterMarkovShift tail w (r0 + M0 * t') = base + Mk * q -> t' = t)) := by
  have hmod18_table : ∀ (w a : Nat), w ≥ 2 -> a < 2 * 3 ^ (w - 1) ->
      (a % 6 = 0 -> markovShiftTrue w a % 18 = 1) ∧
      (a % 6 = 1 -> markovShiftTrue w a % 18 = 15) ∧
      (a % 6 = 2 -> markovShiftTrue w a % 18 = 7) ∧
      (a % 6 = 3 -> markovShiftTrue w a % 18 = 9) ∧
      (a % 6 = 4 -> markovShiftTrue w a % 18 = 13) ∧
      (a % 6 = 5 -> markovShiftTrue w a % 18 = 3) := by
    intro w a hw2 ha_lt
    have hr_lt : a % 6 < 2 * 3 ^ (2 - 1) := Nat.mod_lt a (by decide)
    have hcongr := markovShiftTrue_contraction_mod_pow3 1 w 2 a (a % 6)
      (by omega) (by decide) ha_lt hr_lt (by simp)
    change markovShiftTrue w a % 18 = markovShiftTrue 2 (a % 6) % 18 at hcongr
    have hb0 : markovShiftTrue 2 0 % 18 = 1 := by decide
    have hb1 : markovShiftTrue 2 1 % 18 = 15 := by decide
    have hb2 : markovShiftTrue 2 2 % 18 = 7 := by decide
    have hb3 : markovShiftTrue 2 3 % 18 = 9 := by decide
    have hb4 : markovShiftTrue 2 4 % 18 = 13 := by decide
    have hb5 : markovShiftTrue 2 5 % 18 = 3 := by decide
    refine ⟨fun h => by rw [hcongr, h, hb0],
            fun h => by rw [hcongr, h, hb1],
            fun h => by rw [hcongr, h, hb2],
            fun h => by rw [hcongr, h, hb3],
            fun h => by rw [hcongr, h, hb4],
            fun h => by rw [hcongr, h, hb5]⟩
  refine ⟨⟨fun u tail hwu => iterMarkovShift_append_canonical tail u hwu,
           iterMarkovShift_range_and_inj⟩,
          ⟨hmod18_table, ?_⟩, ?_⟩
  · -- Core parity word mod-`18` confinement (`w(u) ≥ 3`):
    intro u hu hw3
    rcases list_eq_append_true_of_reverse_head u hu.2 with ⟨v, rfl⟩
    have hw_v : parityWeight v ≥ 2 := by
      rw [parityWeight_append] at hw3
      have h1 : parityWeight [true] = 1 := rfl
      rw [h1] at hw3; omega
    have hrec : canonicalSuffixShift (v ++ [true]) 1 =
        markovShiftTrue (parityWeight v) (canonicalSuffixShift v 1) :=
      (canonicalSuffixShift_append_markov_recurrence.2.2 v (by omega)).2.2.1
    have ha_lt := (canonicalSuffixShift_spec_unique v 1 (by omega) (by decide)).1
    rcases hmod18_table (parityWeight v) (canonicalSuffixShift v 1) hw_v ha_lt with
      ⟨h0, h1, h2, h3, h4, h5⟩
    rw [hrec]
    have hm6_lt : canonicalSuffixShift v 1 % 6 < 6 := Nat.mod_lt _ (by decide)
    rcases (by omega : canonicalSuffixShift v 1 % 6 = 0 ∨
                       canonicalSuffixShift v 1 % 6 = 1 ∨
                       canonicalSuffixShift v 1 % 6 = 2 ∨
                       canonicalSuffixShift v 1 % 6 = 3 ∨
                       canonicalSuffixShift v 1 % 6 = 4 ∨
                       canonicalSuffixShift v 1 % 6 = 5) with hr | hr | hr | hr | hr | hr
    · rw [h0 hr]; decide
    · rw [h1 hr]; decide
    · rw [h2 hr]; decide
    · rw [h3 hr]; decide
    · rw [h4 hr]; decide
    · rw [h5 hr]; decide
  · -- Universal multi-step `3 ^ (w - 1 - j)` fiber equidistribution:
    intro tail j w r0 hw hr0
    dsimp only
    let M0 := 2 * 3 ^ j
    let Mk := 2 * 3 ^ (j + parityWeight tail)
    let N := 3 ^ (w - 1 - j)
    let base := iterMarkovShift tail w r0 % Mk
    have hM0_pos : M0 ≥ 2 := by dsimp [M0]; have := pow3_pos_nat j; omega
    have hMk_pos : Mk ≥ 2 := by dsimp [Mk]; have := pow3_pos_nat (j + parityWeight tail); omega
    have hdom_fac : 2 * 3 ^ (w - 1) = M0 * N := by
      dsimp [M0, N]
      rw [Nat.mul_assoc 2 (3 ^ j), ← Nat.pow_add 3 j (w - 1 - j),
          show j + (w - 1 - j) = w - 1 by omega]
    have hcod_fac : 2 * 3 ^ (w + parityWeight tail - 1) = Mk * N := by
      dsimp [Mk, N]
      rw [Nat.mul_assoc 2, ← Nat.pow_add 3 (j + parityWeight tail) (w - 1 - j),
          show j + parityWeight tail + (w - 1 - j) = w + parityWeight tail - 1 by omega]
    have hat_lt : ∀ t : Nat, t < N -> r0 + M0 * t < 2 * 3 ^ (w - 1) := by
      intro t ht
      rw [hdom_fac]
      have hm : M0 * (t + 1) ≤ M0 * N := Nat.mul_le_mul_left M0 (by omega)
      rw [Nat.mul_add, Nat.mul_one] at hm
      omega
    have hr0_dom : r0 < 2 * 3 ^ (w - 1) := by
      simpa using hat_lt 0 (pow3_pos_nat (w - 1 - j))
    rcases iterMarkovShift_range_and_inj tail w (by omega) with ⟨hrange, hinj⟩
    let qMap : Nat -> Nat := fun t => iterMarkovShift tail w (r0 + M0 * t) / Mk
    have hdecomp : ∀ t : Nat, t < N ->
        qMap t < N ∧ iterMarkovShift tail w (r0 + M0 * t) = base + Mk * qMap t := by
      intro t ht
      have hy_lt : iterMarkovShift tail w (r0 + M0 * t) < Mk * N := by
        rw [← hcod_fac]; exact hrange (r0 + M0 * t) (hat_lt t ht)
      have hmod_in : (r0 + M0 * t) % M0 = r0 % M0 := Nat.add_mul_mod_self_left r0 M0 t
      have hmod_out : iterMarkovShift tail w (r0 + M0 * t) % Mk = base :=
        iterMarkovShift_congr_mod_pow3 tail j w w (r0 + M0 * t) r0
          hw hw (hat_lt t ht) hr0_dom hmod_in
      have hdm : iterMarkovShift tail w (r0 + M0 * t) =
          Mk * qMap t + iterMarkovShift tail w (r0 + M0 * t) % Mk :=
        (Nat.div_add_mod _ Mk).symm
      rw [hmod_out, Nat.add_comm (Mk * qMap t) base] at hdm
      have hq_lt : qMap t < N := by
        by_cases hlt : qMap t < N
        · exact hlt
        · have hm : Mk * N ≤ Mk * qMap t := Nat.mul_le_mul_left Mk (by omega)
          omega
      exact ⟨hq_lt, hdm⟩
    have hq_inj : ∀ t1 t2 : Nat, t1 < N -> t2 < N -> qMap t1 = qMap t2 -> t1 = t2 := by
      intro t1 t2 ht1 ht2 hqe
      have hy1 := (hdecomp t1 ht1).2
      have hy2 := (hdecomp t2 ht2).2
      rw [hqe, ← hy2] at hy1
      have ha_eq := hinj _ _ (hat_lt t1 ht1) (hat_lt t2 ht2) hy1
      exact nat_mul_le_cancel_left_w5 M0 t1 t2 (by omega) (by omega) |> fun h12 =>
        Nat.le_antisymm h12 (nat_mul_le_cancel_left_w5 M0 t2 t1 (by omega) (by omega))
    refine ⟨fun t ht => ⟨qMap t, (hdecomp t ht).1, (hdecomp t ht).2⟩, ?_⟩
    intro q hq
    rcases nat_fin_inj_implies_surj N qMap (fun t ht => (hdecomp t ht).1) hq_inj q hq with
      ⟨t, ht_lt, hqt_eq⟩
    have hyt_eq : iterMarkovShift tail w (r0 + M0 * t) = base + Mk * q := by
      rw [(hdecomp t ht_lt).2, hqt_eq]
    refine ⟨t, ht_lt, hyt_eq, ?_⟩
    intro t' ht'_lt hyt'_eq
    have ha_eq := hinj _ _ (hat_lt t' ht'_lt) (hat_lt t ht_lt) (hyt'_eq.trans hyt_eq.symm)
    exact Nat.le_antisymm
      (nat_mul_le_cancel_left_w5 M0 t' t (by omega) (by omega))
      (nat_mul_le_cancel_left_w5 M0 t t' (by omega) (by omega))

end CollatzFormal
