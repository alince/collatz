/-
  CollatzFormal/Wave17WholeSpaceCore.lean
  Wave 17 Whole-Space Mathematical & CS Proof Loop (Core — Fronts A & B):
  1. Front A — All-Dimension (`∀ d ≥ 1`) Active-`.B` Subdiagonal Cascade Collapse (`9` `.B` symbols
     on `c39`, `18` `.B` symbols on `c78`) & Universal `GenOmegaBidirectionalBAndTTopRowMatTower`
     Impossibility on `c39` & `c78`,
     Infinite 4-Parameter Simultaneous Bidirectional `.B` + `.T` + `.R`-Boundary-Growth Mixed
     Zero-Diagonal `d = 2` Cones (`biBTRMat2DC39` & `biBTRMat2DC78`, strictly orienting `18/39`
     and `36/78` rules while escaping Wave 16's 2-Rule & 7-Rule Farkas Syzygies by `+13` and `+10`)
     Locked by Parameterized 4-Rule & 11-Rule Farkas Syzygies,
     & Unconditional `1..20`-Cycle Freedom Across ALL `DP2` Words + Universal Arbitrary-`m`
     (`∀ m ≥ 1`) `.R`-Carrying `leftAnchoredDP2Step` Cycle-to-Brox Spiral Locks (`W17_H1`, Branch P4.3)
  2. Front B — Universal Rectangular `u = 1` Coprime-`W` Exact `Nat.lcm = Product` & Pure-`2^E_2(U, T)`
     Super-Exponential `(U * T)!` Dominance Across `(U * T) × (U * T)` Grids (`∀ U ≥ 4, 1 ≤ T < U`)
     + `12 × 12` `(U = 4, T = 3, u = 2)` Overlap & `(U = 4, T = 1, u = 1)` Sharpness Certificates,
     Rank-3 Order-4 `12 × 12` `(T = 4, U = 3)` Two-Base Schneider–Laurent Collatz-Cone Sign-Flip
     (`(3, 5, 1) < 0` vs `(5, 8, 1) > 0` & `(3, 5, 2) > 0`), Exact Degree-18 Closed Form
     `det_12(W, K, 1) = 3888 * K^3 * (4 * W - K) * Q_14(W, K)`, & Complete `u = 1` Zero Locus `K = 4 * W`
     via Projective `P^1(F_47)` Root-Freeness,
     & Choice-Free General Mersenne Companion-Divisor Cascades (`{3, 7, 15, 31, 51, 73, 255, 511}`)
     Coupled With All-Rotation Cyclic `p`-Pivot Brox Minimization & `henselOddInvModPow2` Boosts
     Eliminating Balanced & Convergent Semi-Balanced `m = 6` Families (`W17_H2`, Branches P3.2–P3.4)

  Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

import CollatzFormal.Wave16WholeSpace

namespace CollatzFormal

-- ============================================================================
-- SECTION 1: Front A (Branch P4.3) — All-Dimension Bidirectional `.B` + `.T`
--            Cascade Collapse, 4-Parameter Simultaneous Bidirectional `.B`+`.T`+`.R`
--            `d = 2` Farkas Locks, & Unconditional `1..20`-Cycle Freedom +
--            Universal Arbitrary-`m` `.R`-Carrying `leftAnchoredDP2Step` Locks (`W17_H1`)
-- ============================================================================

private theorem mul_pow_w17c (a b : Nat) : ∀ n : Nat, (a * b) ^ n = a ^ n * b ^ n
  | 0 => rfl
  | n + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, mul_pow_w17c a b n]
    ac_rfl

private theorem pow_mono_base_w17c (a b : Nat) (hle : a ≤ b) : ∀ n : Nat, a ^ n ≤ b ^ n
  | 0 => Nat.le_refl 1
  | n + 1 => Nat.mul_le_mul (pow_mono_base_w17c a b hle n) hle

private def toFinWordW17 (N : Nat) (hN : N ≥ 1) : List Nat -> List (Fin N)
  | [] => []
  | x :: xs => (if h : x < N then ⟨x, h⟩ else ⟨0, hN⟩) :: toFinWordW17 N hN xs

private def toFinRulesW17 (N : Nat) (hN : N ≥ 1) :
    List (List Nat × List Nat) -> List (List (Fin N) × List (Fin N))
  | [] => []
  | (l, r) :: rs => (toFinWordW17 N hN l, toFinWordW17 N hN r) :: toFinRulesW17 N hN rs

private def c39FastRulesW17 : List (List (Fin 42) × List (Fin 42)) :=
  toFinRulesW17 42 (by decide)
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

private def c78FastRulesW17 : List (List (Fin 84) × List (Fin 84)) :=
  toFinRulesW17 84 (by decide)
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
private theorem c39_eq_fastRules_w17 :
    filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List) = c39FastRulesW17 := by decide

set_option maxRecDepth 65536 in
private theorem c78_eq_fastRules_w17 :
    filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List) = c78FastRulesW17 := by decide

-- ----------------------------------------------------------------------------
-- Section 1A: All-Dimension (`∀ d ≥ 1`) Active-`.B` Subdiagonal Cascade Collapse
--             & Universal `GenOmegaBidirectionalBAndTTopRowMatTower` Impossibility
-- ----------------------------------------------------------------------------

/-- Count active `.B` symbols (`4 * M ≤ s < 8 * M` appearing in `rules`). -/
def countActiveBSymsBool (M : Nat)
    (rules : List (List (Fin (14 * M)) × List (Fin (14 * M)))) : Nat :=
  let rec loop : Nat -> Nat
    | 0 => 0
    | k + 1 =>
      (if decide (4 * M ≤ k ∧ k < 8 * M) && symAppearsInRulesBool (14 * M) k rules then 1 else 0) +
        loop k
  loop (14 * M)

/-- Dual `k`-level `ω^k` Hofbauer–Waldmann natural matrix tower over `Fin (14 * M)` of dimension
    `d ≥ 1` in the bidirectional `.B` + `.T`-top-row + arbitrary-`.R` stratum:
    - Every symbol satisfies `(M_s)_{0,0} ≥ 1`,
    - `.L` (`s < 2 * M`) has `(M_s)_{0,0} = 1` and zero bottom `d - 1` rows (`i ≥ 1 -> (M_s)_{i,j} = 0`),
    - `.B` (`4 * M ≤ s < 8 * M`) has **simultaneous bidirectional zero-diagonal**
      `[[1, b_b^T], [c_b, 0]]`: `(M_b)_{0,0} = 1`, arbitrary top-row off-diagonals `(M_b)_{0,j}`,
      arbitrary subdiagonals `(M_b)_{i,0}`, and zero lower-right block `(M_b)_{i,j} = 0` (`i, j ≥ 1`),
    - `.T` (`s ≥ 8 * M`) has arbitrary top row `[(M_t)_{0,0}, b_t^T]` and zero bottom `d - 1` rows
      (`i ≥ 1 -> (M_t)_{i,j} = 0`),
    - `.R` (`2 * M ≤ s < 4 * M`) has **completely arbitrary** `d × d` entries (`(M_r)_{0,0} ≥ 1`). -/
def GenOmegaBidirectionalBAndTTopRowMatTower (M d : Nat) (hd : d ≥ 1) :
    Nat -> List (List (Fin (14 * M)) × List (Fin (14 * M))) -> Prop
  | 0, rules => rules = []
  | k + 1, rules =>
    rules = [] ∨
    ∃ (rem : List (List (Fin (14 * M)) × List (Fin (14 * M))))
      (mat : Fin (14 * M) -> Fin d -> Fin d -> Nat)
      (v : Fin (14 * M) -> Fin d -> Nat),
      (∀ s : Fin (14 * M), mat s ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1) ∧
      (∀ s : Fin (14 * M), s.val < 2 * M ->
        mat s ⟨0, hd⟩ ⟨0, hd⟩ = 1 ∧ ∀ (i j : Fin d), i.val ≥ 1 -> mat s i j = 0) ∧
      (∀ s : Fin (14 * M), 4 * M ≤ s.val ∧ s.val < 8 * M ->
        mat s ⟨0, hd⟩ ⟨0, hd⟩ = 1 ∧
        ∀ (i j : Fin d), i.val ≥ 1 -> j.val ≥ 1 -> mat s i j = 0) ∧
      (∀ s : Fin (14 * M), s.val ≥ 8 * M ->
        ∀ (i j : Fin d), i.val ≥ 1 -> mat s i j = 0) ∧
      (∀ r ∈ rules,
        (∀ i j : Fin d, evalFinWordMat (14 * M) d mat r.1 i j ≥ evalFinWordMat (14 * M) d mat r.2 i j) ∧
        (∀ i : Fin d, evalFinWordVec (14 * M) d mat v r.1 i ≥ evalFinWordVec (14 * M) d mat v r.2 i)) ∧
      (∀ r ∈ rules,
        ¬ (evalFinWordVec (14 * M) d mat v r.1 ⟨0, hd⟩ >
           evalFinWordVec (14 * M) d mat v r.2 ⟨0, hd⟩) ->
        r ∈ rem) ∧
      GenOmegaBidirectionalBAndTTopRowMatTower M d hd k rem

private def noRWordBoolW17 (M : Nat) : List (Fin (14 * M)) -> Bool
  | [] => true
  | s :: tl => decide (s.val < 2 * M ∨ s.val ≥ 4 * M) && noRWordBoolW17 M tl

private def noRRuleBoolW17 (M : Nat) (r : List (Fin (14 * M)) × List (Fin (14 * M))) : Bool :=
  noRWordBoolW17 M r.1 && noRWordBoolW17 M r.2

private def activeBForcedByTRuleBool (M : Nat)
    (rules : List (List (Fin (14 * M)) × List (Fin (14 * M)))) : Bool :=
  let rec loop : Nat -> Bool
    | 0 => true
    | k + 1 =>
      let ok_k :=
        if decide (4 * M ≤ k ∧ k < 8 * M) && symAppearsInRulesBool (14 * M) k rules then
          rules.any (fun r =>
            match r.1, r.2 with
            | l0 :: _, r0 :: _ => decide (l0.val ≥ 8 * M ∧ r0.val = k)
            | _, _ => false)
        else true
      ok_k && loop k
  loop (14 * M)

private def cascadeOneTopLeftC39 : List (Nat × Nat × Nat × Nat) :=
  [(1, 18, 2, 36), (2, 20, 2, 38), (36, 22, 20, 40), (38, 16, 13, 31),
   (38, 23, 20, 41), (40, 17, 16, 32), (40, 21, 23, 39), (31, 14, 18, 29),
   (32, 13, 18, 28), (28, 18, 22, 33), (29, 20, 22, 35), (33, 22, 17, 37)]

private def cascadeOneTopLeftC78 : List (Nat × Nat × Nat × Nat) :=
  [(1, 36, 2, 72), (1, 39, 5, 75), (5, 38, 2, 74), (5, 41, 5, 77),
   (74, 31, 28, 61), (74, 34, 25, 64), (75, 43, 41, 79), (75, 46, 38, 82),
   (77, 44, 38, 80), (77, 47, 41, 83), (79, 42, 44, 78), (79, 45, 47, 81),
   (82, 32, 31, 62), (82, 35, 34, 65), (62, 25, 39, 55), (62, 28, 36, 58),
   (64, 26, 36, 56), (64, 29, 39, 59), (55, 36, 43, 66), (55, 39, 46, 69),
   (59, 38, 43, 68), (59, 41, 46, 71), (69, 43, 35, 73), (69, 46, 32, 76)]

private def inUnitTopLeftSetBoolW17 (M : Nat) (acc : List Nat) (x : Nat) : Bool :=
  decide (x < 2 * M ∨ (4 * M ≤ x ∧ x < 8 * M)) || acc.any (· == x)

private def checkUnitTopLeftCascadeBoolW17 (M : Nat)
    (noR_rules : List (List (Fin (14 * M)) × List (Fin (14 * M))))
    (acc : List Nat) : List (Nat × Nat × Nat × Nat) -> Option (List Nat)
  | [] => some acc
  | (s1, s2, u1, u2) :: rest =>
    if h : s1 < 14 * M ∧ s2 < 14 * M ∧ u1 < 14 * M ∧ u2 < 14 * M then
      let r_cand : List (Fin (14 * M)) × List (Fin (14 * M)) :=
        ([⟨s1, h.1⟩, ⟨s2, h.2.1⟩], [⟨u1, h.2.2.1⟩, ⟨u2, h.2.2.2⟩])
      if inUnitTopLeftSetBoolW17 M acc s1 && inUnitTopLeftSetBoolW17 M acc s2 &&
         noR_rules.any (· == r_cand) then
        checkUnitTopLeftCascadeBoolW17 M noR_rules (u2 :: acc) rest
      else none
    else none

private def checkBidirectionalCollapseCertBoolW17 (M : Nat)
    (rules : List (List (Fin (14 * M)) × List (Fin (14 * M))))
    (casc : List (Nat × Nat × Nat × Nat))
    (syz : List Nat)
    (flow : List (Nat × Nat × Nat × Nat × Nat)) : Bool :=
  let noR_rules := rules.filter (noRRuleBoolW17 M)
  activeBForcedByTRuleBool M rules &&
  match checkUnitTopLeftCascadeBoolW17 M noR_rules [] casc with
  | none => false
  | some finalAcc =>
    rules.all (fun r =>
      nonLastOutsideRBool M r.1 && nonLastOutsideRBool M r.2 &&
      (r.1 ++ r.2).all (fun s =>
        decide (s.val < 8 * M) || inUnitTopLeftSetBoolW17 M finalAcc s.val)) &&
    checkPositiveParikhSyzygyFastBool (14 * M) rules syz &&
    flow.all (fun e =>
      let x1 := e.1; let y1 := e.2.1; let x2 := e.2.2.1; let y2 := e.2.2.2.1
      decide (x1 < 14 * M ∧ y1 < 14 * M ∧ x2 < 14 * M ∧ y2 < 14 * M) &&
      (decide (x1 = x2) || hasLastRulePairBool x2 x1 noR_rules) &&
      (decide (y1 = y2) || hasFirstRulePairBool y2 y1 rules)) &&
    cancelAllWeightedPairs
      (rulesLhs2GramItems rules syz ++ flowDstItems flow)
      (rulesRhs2GramItems rules syz ++ flowSrcItems flow)

set_option maxRecDepth 65536 in
private theorem bi_collapse_c39_c78_certs :
    countActiveBSymsBool 3 c39FastRulesW17 = 9 ∧
    countActiveBSymsBool 6 c78FastRulesW17 = 18 ∧
    checkBidirectionalCollapseCertBoolW17 3 c39FastRulesW17
      cascadeOneTopLeftC39 syzC39ZeroDiag2Gram flowC39ZeroDiag2Gram = true ∧
    checkBidirectionalCollapseCertBoolW17 6 c78FastRulesW17
      cascadeOneTopLeftC78 syzC78ZeroDiag2Gram flowC78ZeroDiag2Gram = true ∧
    c39FastRulesW17 ≠ [] ∧
    c78FastRulesW17 ≠ [] := by decide

private theorem natSumFin_zero_w17 (d : Nat) (f : Fin d -> Nat)
    (hz : ∀ k : Fin d, f k = 0) : natSumFin d f = 0 := by
  unfold natSumFin
  have hst : ∀ m : Nat, m ≤ d -> natSumPrefix d f m = 0 := by
    intro m hm; induction m with
    | zero => rfl
    | succ m' ih =>
      have hm_lt : m' < d := hm
      simp only [natSumPrefix, hm_lt, dite_true, ih (Nat.le_of_lt hm), hz ⟨m', hm_lt⟩, Nat.add_zero]
  exact hst d (Nat.le_refl d)

private theorem natSumFin_ge_at_w17 (d : Nat) (f : Fin d -> Nat) (k0 : Fin d) :
    natSumFin d f ≥ f k0 := by
  unfold natSumFin
  have hst : ∀ m : Nat, m ≤ d -> (k0.val < m -> natSumPrefix d f m ≥ f k0) := by
    intro m hm; induction m with
    | zero => intro hlt; omega
    | succ m' ih =>
      have hm_lt : m' < d := hm
      intro hlt
      simp only [natSumPrefix, hm_lt, dite_true]
      by_cases heq : k0.val = m'
      · have hkf : (⟨m', hm_lt⟩ : Fin d) = k0 := Fin.ext heq.symm
        rw [hkf]; omega
      · have hp := ih (Nat.le_of_lt hm) (by omega); omega
  exact hst d (Nat.le_refl d) k0.isLt

private theorem natSumFin_single_w17 (d : Nat) (f : Fin d -> Nat) (k0 : Fin d)
    (hz : ∀ k : Fin d, k ≠ k0 -> f k = 0) :
    natSumFin d f = f k0 := by
  unfold natSumFin
  have hst : ∀ m : Nat, m ≤ d -> natSumPrefix d f m = if k0.val < m then f k0 else 0 := by
    intro m hm; induction m with
    | zero => simp [natSumPrefix]
    | succ m' ih =>
      have hm_lt : m' < d := hm
      simp only [natSumPrefix, hm_lt, dite_true, ih (Nat.le_of_lt hm)]
      by_cases heq : m' = k0.val
      · have hkf : (⟨m', hm_lt⟩ : Fin d) = k0 := Fin.ext heq
        rw [hkf, ite_false_of_w10 (by omega : ¬ (k0.val < m')),
            ite_true_of_w10 (by omega : k0.val < m' + 1), Nat.zero_add]
      · have hne : (⟨m', hm_lt⟩ : Fin d) ≠ k0 := fun h => heq (congrArg Fin.val h)
        rw [hz ⟨m', hm_lt⟩ hne, Nat.add_zero]
        by_cases hlt : k0.val < m'
        · rw [ite_true_of_w10 hlt, ite_true_of_w10 (by omega)]
        · rw [ite_false_of_w10 hlt, ite_false_of_w10 (by omega)]
  rw [hst d (Nat.le_refl d), ite_true_of_w10 k0.isLt]

private theorem natSumFin_split_zero_w17 (d : Nat) (hd : d ≥ 1) (f : Fin d -> Nat) :
    natSumFin d f = f ⟨0, hd⟩ + natSumFin d (fun j => if j.val = 0 then 0 else f j) := by
  unfold natSumFin
  have hst : ∀ m : Nat, 1 ≤ m -> m ≤ d ->
      natSumPrefix d f m = f ⟨0, hd⟩ + natSumPrefix d (fun j => if j.val = 0 then 0 else f j) m := by
    intro m hm1 hmd; induction m with
    | zero => omega
    | succ m' ih =>
      have hm_lt : m' < d := hmd
      by_cases hm0 : m' = 0
      · subst hm0; simp [natSumPrefix, hm_lt]
      · simp only [natSumPrefix, hm_lt, dite_true, hm0, ite_false,
                   ih (by omega) (Nat.le_of_lt hmd), Nat.add_assoc]
  exact hst d hd (Nat.le_refl d)

private theorem evalFinWordMat_00_ge_one_w17 (N d : Nat) (hd : d ≥ 1)
    (mat : Fin N -> Fin d -> Fin d -> Nat)
    (hm_pos : ∀ s : Fin N, mat s ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1) :
    ∀ w : List (Fin N), evalFinWordMat N d mat w ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1
  | [] => by simp [evalFinWordMat, natMatId]
  | s :: rest => by
    let z0 : Fin d := ⟨0, hd⟩
    change natSumFin d (fun k => mat s z0 k * evalFinWordMat N d mat rest k z0) ≥ 1
    have hg := natSumFin_ge_at_w17 d (fun k => mat s z0 k * evalFinWordMat N d mat rest k z0) z0
    have hp := Nat.mul_le_mul (hm_pos s) (evalFinWordMat_00_ge_one_w17 N d hd mat hm_pos rest)
    dsimp only [z0] at hg
    exact Nat.le_trans hp hg

private theorem mem_of_countFinOcc_pos_w17 (N : Nat) (s : Fin N) :
    ∀ w : List (Fin N), countFinOcc N s w ≥ 1 -> s ∈ w
  | [], h => by simp [countFinOcc] at h
  | x :: xs, h => by
    by_cases hx : x = s
    · subst hx; exact List.Mem.head _
    · have hne_v : x.val ≠ s.val := fun hv => hx (Fin.ext hv)
      simp [countFinOcc, hne_v] at h
      exact List.Mem.tail x (mem_of_countFinOcc_pos_w17 N s xs h)

private theorem exists_rule_of_symAppearsInRulesBool_w17 (N : Nat) (s : Fin N) :
    ∀ rs : List (List (Fin N) × List (Fin N)),
      symAppearsInRulesBool N s.val rs = true -> ∃ r ∈ rs, s ∈ r.1 ++ r.2
  | [], h => by simp [symAppearsInRulesBool] at h
  | (l0, r0) :: rtl, h => by
    unfold symAppearsInRulesBool at h
    rcases Bool.or_eq_true_iff.mp h with hhere | hthere
    · have hc := of_decide_eq_true hhere
      rw [countNatOccW11_map_val N s l0, countNatOccW11_map_val N s r0] at hc
      refine ⟨(l0, r0), List.Mem.head _, ?_⟩
      by_cases h1 : countFinOcc N s l0 ≥ 1
      · exact List.mem_append_left _ (mem_of_countFinOcc_pos_w17 N s l0 h1)
      · exact List.mem_append_right _ (mem_of_countFinOcc_pos_w17 N s r0 (by omega))
    · rcases exists_rule_of_symAppearsInRulesBool_w17 N s rtl hthere with ⟨r', hr', hs_m⟩
      exact ⟨r', List.Mem.tail (l0, r0) hr', hs_m⟩

private theorem upperZeroDiag_helpers_w17 (N d : Nat) (hd : d ≥ 1)
    (M : Fin N -> Fin d -> Fin d -> Nat) (v : Fin N -> Fin d -> Nat)
    (h00 : ∀ s : Fin N, M s ⟨0, hd⟩ ⟨0, hd⟩ = 1)
    (hlow : ∀ (s : Fin N) (i j : Fin d), i.val > 0 -> M s i j = 0) :
    (∀ (s0 : Fin N) (rest : List (Fin N)) (j : Fin d),
      evalFinWordMat N d M (s0 :: rest) ⟨0, hd⟩ j = M (lastFinSym s0 (s0 :: rest)) ⟨0, hd⟩ j) ∧
    (∀ (s0 : Fin N) (rest : List (Fin N)) (i : Fin d),
      i.val > 0 -> evalFinWordVec N d M v (s0 :: rest) i = v s0 i) ∧
    (∀ w : List (Fin N),
      evalFinWordVec N d M v w ⟨0, hd⟩ =
        evalFinParikh N (fun s => v s ⟨0, hd⟩) w + eval2GramFin N (pairWeightFin N d hd M v) w) := by
  have hlow_mat : ∀ (s0 : Fin N) (rest : List (Fin N)) (i j : Fin d),
      i.val > 0 -> evalFinWordMat N d M (s0 :: rest) i j = 0 := by
    intro s0 rest i j hi
    simp only [evalFinWordMat, natMatMul]
    exact natSumFin_zero_w17 d _ (fun k => by rw [hlow s0 i k hi, Nat.zero_mul])
  have hlast_irr : ∀ (d1 d2 a : Fin N) (tl : List (Fin N)),
      lastFinSym d1 (a :: tl) = lastFinSym d2 (a :: tl) := by
    intro d1 d2 a tl; induction tl generalizing a with
    | nil => rfl
    | cons b tl' ih => exact ih b
  have htop_mat : ∀ (s0 : Fin N) (rest : List (Fin N)) (j : Fin d),
      evalFinWordMat N d M (s0 :: rest) ⟨0, hd⟩ j = M (lastFinSym s0 (s0 :: rest)) ⟨0, hd⟩ j := by
    intro s0 rest; induction rest generalizing s0 with
    | nil =>
      intro j; simp only [evalFinWordMat, natMatMul, lastFinSym]
      rw [natSumFin_single_w17 d (fun k => M s0 ⟨0, hd⟩ k * natMatId d k j) j]
      · simp [natMatId]
      · intro k hkj; have hkv : k.val ≠ j.val := fun hv => hkj (Fin.ext hv); simp [natMatId, hkv]
    | cons s1 tl ih =>
      intro j
      change natSumFin d (fun k => M s0 ⟨0, hd⟩ k * evalFinWordMat N d M (s1 :: tl) k j) =
        M (lastFinSym s0 (s1 :: tl)) ⟨0, hd⟩ j
      rw [natSumFin_single_w17 d (fun k => M s0 ⟨0, hd⟩ k * evalFinWordMat N d M (s1 :: tl) k j) ⟨0, hd⟩]
      · rw [h00 s0, Nat.one_mul, hlast_irr s0 s1 s1 tl]; exact ih s1 j
      · intro k hk0
        have hk_pos : k.val > 0 := by have : k.val ≠ 0 := fun hv => hk0 (Fin.ext hv); omega
        rw [hlow_mat s1 tl k j hk_pos, Nat.mul_zero]
  have hlow_vec : ∀ (s0 : Fin N) (rest : List (Fin N)) (i : Fin d),
      i.val > 0 -> evalFinWordVec N d M v (s0 :: rest) i = v s0 i := by
    intro s0 rest i hi; simp only [evalFinWordVec, natMatVec]
    rw [natSumFin_zero_w17 d _ (fun k => by rw [hlow s0 i k hi, Nat.zero_mul]), Nat.add_zero]
  have htop_vec : ∀ w : List (Fin N),
      evalFinWordVec N d M v w ⟨0, hd⟩ =
        evalFinParikh N (fun s => v s ⟨0, hd⟩) w + eval2GramFin N (pairWeightFin N d hd M v) w := by
    intro w; induction w with
    | nil => rfl
    | cons a xs ih =>
      cases xs with
      | nil =>
        simp only [evalFinWordVec, evalFinParikh, eval2GramFin, natMatVec, Nat.add_zero]
        rw [natSumFin_zero_w17 d _ (fun _ => Nat.mul_zero _), Nat.add_zero]
      | cons b tl =>
        change v a ⟨0, hd⟩ + natSumFin d (fun j => M a ⟨0, hd⟩ j * evalFinWordVec N d M v (b :: tl) j) =
          (v a ⟨0, hd⟩ + evalFinParikh N (fun s => v s ⟨0, hd⟩) (b :: tl)) +
            (pairWeightFin N d hd M v a b + eval2GramFin N (pairWeightFin N d hd M v) (b :: tl))
        rw [natSumFin_split_zero_w17 d hd, h00 a, Nat.one_mul, ih]
        have hpw : natSumFin d (fun j =>
              if j.val = 0 then 0 else M a ⟨0, hd⟩ j * evalFinWordVec N d M v (b :: tl) j) =
            pairWeightFin N d hd M v a b := by
          unfold pairWeightFin natSumFin
          have hcon : ∀ m : Nat, m ≤ d ->
              natSumPrefix d (fun j =>
                if j.val = 0 then 0 else M a ⟨0, hd⟩ j * evalFinWordVec N d M v (b :: tl) j) m =
              natSumPrefix d (fun j => if j.val = 0 then 0 else M a ⟨0, hd⟩ j * v b j) m := by
            intro m hm; induction m with
            | zero => rfl
            | succ m' ihm =>
              have hm'_lt : m' < d := hm
              simp only [natSumPrefix, hm'_lt, dite_true, ihm (Nat.le_of_lt hm)]
              by_cases hm0 : m' = 0
              · simp [hm0]
              · simp only [hm0, ite_false]
                rw [hlow_vec b tl ⟨m', hm'_lt⟩ (Nat.pos_of_ne_zero hm0)]
          exact hcon d (Nat.le_refl d)
        rw [hpw]; omega
  exact ⟨htop_mat, hlow_vec, htop_vec⟩

private theorem cancelAllWeightedPairs_sound_w17 (N : Nat) (pw : Fin N -> Fin N -> Nat) :
    (∀ xs ys : List (Nat × Nat × Nat),
      evalWeightedPairs N pw (xs ++ ys) = evalWeightedPairs N pw xs + evalWeightedPairs N pw ys) ∧
    (∀ (rules : List (List (Fin N) × List (Fin N))) (syz : List Nat),
      evalWeightedPairs N pw (rulesLhs2GramItems rules syz) = weighted2GramLhs N pw rules syz ∧
      evalWeightedPairs N pw (rulesRhs2GramItems rules syz) = weighted2GramRhs N pw rules syz) ∧
    (∀ (xs ys : List (Nat × Nat × Nat)),
      cancelAllWeightedPairs xs ys = true ->
      evalWeightedPairs N pw xs ≤ evalWeightedPairs N pw ys) := by
  have happ : ∀ xs ys : List (Nat × Nat × Nat),
      evalWeightedPairs N pw (xs ++ ys) = evalWeightedPairs N pw xs + evalWeightedPairs N pw ys := by
    intro xs ys; induction xs with
    | nil => simp [evalWeightedPairs]
    | cons _ tl ih => simp only [List.cons_append, evalWeightedPairs, ih, Nat.add_assoc]
  have hw2g : ∀ (m : Nat) (u : List (Fin N)),
      evalWeightedPairs N pw (word2GramItems m (u.map Fin.val)) = m * eval2GramFin N pw u := by
    intro m u; induction u with
    | nil => simp [word2GramItems, evalWeightedPairs, eval2GramFin]
    | cons a xs ih =>
      cases xs with
      | nil => simp [word2GramItems, evalWeightedPairs, eval2GramFin]
      | cons b tl =>
        simp only [List.map_cons] at ih ⊢
        simp only [word2GramItems, evalWeightedPairs, eval2GramFin, a.isLt, b.isLt, dite_true, ih, Nat.mul_add]
  have hr2g : ∀ (rules : List (List (Fin N) × List (Fin N))) (syz : List Nat),
      evalWeightedPairs N pw (rulesLhs2GramItems rules syz) = weighted2GramLhs N pw rules syz ∧
      evalWeightedPairs N pw (rulesRhs2GramItems rules syz) = weighted2GramRhs N pw rules syz := by
    intro rules; induction rules with
    | nil => intro _; exact ⟨rfl, rfl⟩
    | cons r rs ih =>
      intro syz; cases syz with
      | nil => exact ⟨rfl, rfl⟩
      | cons m ms =>
        rcases ih ms with ⟨hl, hr⟩
        exact ⟨by simp only [rulesLhs2GramItems, weighted2GramLhs, happ, hw2g, hl],
               by simp only [rulesRhs2GramItems, weighted2GramRhs, happ, hw2g, hr]⟩
  have hsub : ∀ (x y rem : Nat) (ys ys' : List (Nat × Nat × Nat)),
      subFromWeightedPairs x y rem ys = some ys' ->
      (if hx : x < N then if hy : y < N then rem * pw ⟨x, hx⟩ ⟨y, hy⟩ else 0 else 0) +
        evalWeightedPairs N pw ys' = evalWeightedPairs N pw ys := by
    intro x y rem ys; induction ys generalizing rem with
    | nil =>
      intro ys' h; cases rem with
      | zero => simp [subFromWeightedPairs] at h; subst h; simp
      | succ _ => simp [subFromWeightedPairs] at h
    | cons hd_p rest ih =>
      rcases hd_p with ⟨rx, ry, rw⟩
      intro ys' h; cases rem with
      | zero => simp [subFromWeightedPairs] at h; subst h; simp
      | succ r' =>
        unfold subFromWeightedPairs at h
        by_cases heq : x = rx ∧ y = ry
        · rcases heq with ⟨rfl, rfl⟩
          simp only [and_self, ite_true] at h
          by_cases hle : r' + 1 ≤ rw
          · simp only [hle, ite_true, Option.some.injEq] at h; subst h
            simp only [evalWeightedPairs]
            by_cases hx : x < N
            · by_cases hy : y < N
              · simp only [hx, hy, dite_true]
                generalize pw ⟨x, hx⟩ ⟨y, hy⟩ = P, evalWeightedPairs N pw rest = E
                have hm := Nat.add_mul (r' + 1) (rw - (r' + 1)) P
                rw [show r' + 1 + (rw - (r' + 1)) = rw by omega] at hm
                omega
              · simp [hx, hy]
            · simp [hx]
          · simp only [hle, ite_false] at h
            have ih_s := ih (r' + 1 - rw) ys' h
            simp only [evalWeightedPairs]; rw [← ih_s]
            by_cases hx : x < N
            · by_cases hy : y < N
              · simp only [hx, hy, dite_true]
                generalize pw ⟨x, hx⟩ ⟨y, hy⟩ = P, evalWeightedPairs N pw ys' = E
                have hm := Nat.add_mul rw (r' + 1 - rw) P
                rw [show rw + (r' + 1 - rw) = r' + 1 by omega] at hm
                omega
              · simp [hx, hy]
            · simp [hx]
        · simp only [heq, ite_false] at h
          cases hs : subFromWeightedPairs x y (r' + 1) rest with
          | none => rw [hs] at h; cases h
          | some rest' =>
            rw [hs] at h; simp only [Option.some.injEq] at h; subst h
            have ih_s := ih (r' + 1) rest' hs
            simp only [evalWeightedPairs]; rw [← ih_s]
            generalize (if hx : x < N then if hy : y < N then (r' + 1) * pw ⟨x, hx⟩ ⟨y, hy⟩ else 0 else 0) = A,
              (if hx : rx < N then if hy : ry < N then rw * pw ⟨rx, hx⟩ ⟨ry, hy⟩ else 0 else 0) = B
            omega
  refine ⟨happ, hr2g, ?_⟩
  intro xs; induction xs with
  | nil => intros; exact Nat.zero_le _
  | cons p xs' ih =>
    rcases p with ⟨x, y, w⟩
    intro ys hb; unfold cancelAllWeightedPairs at hb
    cases hs : subFromWeightedPairs x y w ys with
    | none => rw [hs] at hb; cases hb
    | some ys' =>
      rw [hs] at hb
      have heq := hsub x y w ys ys' hs
      have hle := ih ys' hb
      simp only [evalWeightedPairs]; rw [← heq]; exact Nat.add_le_add_left hle _

private theorem activeBForcedByTRuleBool_sound_w17
    (M : Nat)
    (rules : List (List (Fin (14 * M)) × List (Fin (14 * M))))
    (hb_force : activeBForcedByTRuleBool M rules = true)
    (d : Nat) (hd : d ≥ 1)
    (mat : Fin (14 * M) -> Fin d -> Fin d -> Nat)
    (hm_pos : ∀ s : Fin (14 * M), mat s ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1)
    (hB : ∀ s : Fin (14 * M), 4 * M ≤ s.val ∧ s.val < 8 * M ->
      mat s ⟨0, hd⟩ ⟨0, hd⟩ = 1 ∧ ∀ (i j : Fin d), i.val ≥ 1 -> j.val ≥ 1 -> mat s i j = 0)
    (hT : ∀ s : Fin (14 * M), s.val ≥ 8 * M -> ∀ (i j : Fin d), i.val ≥ 1 -> mat s i j = 0)
    (hweak_mat : ∀ r ∈ rules,
      ∀ i j : Fin d, evalFinWordMat (14 * M) d mat r.1 i j ≥ evalFinWordMat (14 * M) d mat r.2 i j) :
    ∀ s : Fin (14 * M), 4 * M ≤ s.val ∧ s.val < 8 * M ->
      symAppearsInRulesBool (14 * M) s.val rules = true ->
      ∀ (i j : Fin d), i.val ≥ 1 -> mat s i j = 0 := by
  have hlp : ∀ n : Nat, n ≤ 14 * M ->
      activeBForcedByTRuleBool.loop M rules n = true ->
      ∀ m : Nat, m < n -> (hm : m < 14 * M) -> 4 * M ≤ m ∧ m < 8 * M ->
        symAppearsInRulesBool (14 * M) m rules = true ->
        ∀ (i j : Fin d), i.val ≥ 1 -> mat ⟨m, hm⟩ i j = 0 := by
    intro n; induction n with
    | zero => intros _ _ _ hlt; omega
    | succ n' ih =>
      intro hn_le hn m hmn hmN hmb hact i j hi1
      rcases bool_and_split hn with ⟨hok, hprev⟩
      by_cases hmeq : m = n'
      · subst hmeq
        have hcond : (decide (4 * M ≤ m ∧ m < 8 * M) && symAppearsInRulesBool (14 * M) m rules) = true := by
          simp [hmb, hact]
        rw [ite_true_of_w10 hcond] at hok
        rcases List.any_eq_true.mp hok with ⟨r_t, hr_mem, hr_match⟩
        cases hl : r_t.1 with
        | nil => rw [hl] at hr_match; cases hr_match
        | cons l0 ltl =>
          cases hr : r_t.2 with
          | nil => rw [hl, hr] at hr_match; cases hr_match
          | cons r0 rtl =>
            rw [hl, hr] at hr_match
            rcases of_decide_eq_true hr_match with ⟨hl0_T, hr0_m⟩
            have hr0_eq : r0 = ⟨m, hmN⟩ := Fin.ext hr0_m
            by_cases hj1 : j.val ≥ 1
            · exact (hB ⟨m, hmN⟩ hmb).2 i j hi1 hj1
            · have hj0 : j = ⟨0, hd⟩ := Fin.ext (by dsimp; omega)
              rw [hj0]
              have hlhs0 : evalFinWordMat (14 * M) d mat (l0 :: ltl) i ⟨0, hd⟩ = 0 := by
                simp only [evalFinWordMat, natMatMul]
                exact natSumFin_zero_w17 d _ (fun k => by rw [hT l0 hl0_T i k hi1, Nat.zero_mul])
              have hrhs_ge : evalFinWordMat (14 * M) d mat (r0 :: rtl) i ⟨0, hd⟩ ≥ mat r0 i ⟨0, hd⟩ := by
                change natSumFin d (fun k => mat r0 i k * evalFinWordMat (14 * M) d mat rtl k ⟨0, hd⟩) ≥
                  mat r0 i ⟨0, hd⟩
                have hg := natSumFin_ge_at_w17 d
                  (fun k => mat r0 i k * evalFinWordMat (14 * M) d mat rtl k ⟨0, hd⟩) ⟨0, hd⟩
                have hm_rtl := evalFinWordMat_00_ge_one_w17 (14 * M) d hd mat hm_pos rtl
                have hmul := Nat.mul_le_mul_left (mat r0 i ⟨0, hd⟩) hm_rtl
                rw [Nat.mul_one] at hmul; omega
              have hwk := hweak_mat r_t hr_mem i ⟨0, hd⟩
              rw [hl, hr, hlhs0] at hwk
              rw [hr0_eq] at hrhs_ge hwk
              omega
      · exact ih (Nat.le_of_lt hn_le) hprev m (by omega) hmN hmb hact i j hi1
  intro s hs_b hact
  exact hlp (14 * M) (Nat.le_refl _) hb_force s.val s.isLt s.isLt hs_b hact

private theorem bidirectional_collapse_sound_w17
    (M : Nat)
    (rules : List (List (Fin (14 * M)) × List (Fin (14 * M))))
    (casc : List (Nat × Nat × Nat × Nat))
    (syz : List Nat)
    (flow : List (Nat × Nat × Nat × Nat × Nat))
    (hcert : checkBidirectionalCollapseCertBoolW17 M rules casc syz flow = true)
    (d : Nat) (hd : d ≥ 1)
    (mat : Fin (14 * M) -> Fin d -> Fin d -> Nat)
    (v : Fin (14 * M) -> Fin d -> Nat)
    (hm_pos : ∀ s : Fin (14 * M), mat s ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1)
    (hL : ∀ s : Fin (14 * M), s.val < 2 * M ->
      mat s ⟨0, hd⟩ ⟨0, hd⟩ = 1 ∧ ∀ (i j : Fin d), i.val ≥ 1 -> mat s i j = 0)
    (hB : ∀ s : Fin (14 * M), 4 * M ≤ s.val ∧ s.val < 8 * M ->
      mat s ⟨0, hd⟩ ⟨0, hd⟩ = 1 ∧ ∀ (i j : Fin d), i.val ≥ 1 -> j.val ≥ 1 -> mat s i j = 0)
    (hT : ∀ s : Fin (14 * M), s.val ≥ 8 * M ->
      ∀ (i j : Fin d), i.val ≥ 1 -> mat s i j = 0)
    (hweak : ∀ r ∈ rules,
      (∀ i j : Fin d, evalFinWordMat (14 * M) d mat r.1 i j ≥ evalFinWordMat (14 * M) d mat r.2 i j) ∧
      (∀ i : Fin d, evalFinWordVec (14 * M) d mat v r.1 i ≥ evalFinWordVec (14 * M) d mat v r.2 i)) :
    (∀ s : Fin (14 * M), 4 * M ≤ s.val ∧ s.val < 8 * M ->
      symAppearsInRulesBool (14 * M) s.val rules = true ->
      ∀ (i j : Fin d), i.val ≥ 1 -> mat s i j = 0) ∧
    (∀ s : Fin (14 * M), s.val ≥ 8 * M ->
      symAppearsInRulesBool (14 * M) s.val rules = true ->
      mat s ⟨0, hd⟩ ⟨0, hd⟩ = 1) ∧
    (∀ r ∈ rules, evalFinWordVec (14 * M) d mat v r.1 ⟨0, hd⟩ = evalFinWordVec (14 * M) d mat v r.2 ⟨0, hd⟩) := by
  let N := 14 * M
  let z0 : Fin d := ⟨0, hd⟩
  let noR_rules := rules.filter (noRRuleBoolW17 M)
  unfold checkBidirectionalCollapseCertBoolW17 at hcert
  rcases bool_and_split hcert with ⟨hb_force, hrest_cert⟩
  -- Step 1: Every active `.B` symbol has `(mat b)_{i, 0} = 0` (`i ≥ 1`), hence full row `i ≥ 1` zero!
  have hB_sub0 : ∀ s : Fin N, 4 * M ≤ s.val ∧ s.val < 8 * M ->
      symAppearsInRulesBool N s.val rules = true ->
      ∀ (i j : Fin d), i.val ≥ 1 -> mat s i j = 0 :=
    activeBForcedByTRuleBool_sound_w17 M rules hb_force d hd mat hm_pos hB hT
      (fun r hr => (hweak r hr).1)
  -- Unpack `checkUnitTopLeftCascadeBoolW17`:
  cases hc_opt : checkUnitTopLeftCascadeBoolW17 M noR_rules [] casc with
  | none => dsimp only [noR_rules] at hc_opt; rw [hc_opt] at hrest_cert; cases hrest_cert
  | some finalAcc =>
    dsimp only [noR_rules] at hc_opt
    rw [hc_opt] at hrest_cert
    rcases bool_and_split hrest_cert with ⟨hc1, hcan⟩
    rcases bool_and_split hc1 with ⟨hc2, hflow_all⟩
    rcases bool_and_split hc2 with ⟨hrules_cov, hsyz⟩
    have hsym_in_rules : ∀ (r : List (Fin N) × List (Fin N)) (s : Fin N),
        r ∈ rules -> (s ∈ r.1 ∨ s ∈ r.2) -> symAppearsInRulesBool N s.val rules = true := by
      intro r s hr hs
      rcases hs with h1 | h2
      · exact symAppearsInRulesBool_of_mem_lhs N s rules r hr h1
      · exact symAppearsInRulesBool_of_mem_rhs N s rules r hr h2
    -- Step 2: Every active non-`.R` symbol `s` has row `i ≥ 1` identically zero (`mat s i j = 0`):
    have hout_row_zero : ∀ s : Fin N, (s.val < 2 * M ∨ s.val ≥ 4 * M) ->
        symAppearsInRulesBool N s.val rules = true ->
        ∀ (i j : Fin d), i.val ≥ 1 -> mat s i j = 0 := by
      intro s hout hact i j hi1
      rcases hout with hlt2 | hge4
      · exact (hL s hlt2).2 i j hi1
      · by_cases hlt8 : s.val < 8 * M
        · exact hB_sub0 s ⟨hge4, hlt8⟩ hact i j hi1
        · exact hT s (by omega) i j hi1
    have hmat1_eq : ∀ (m_fn : Fin N -> Fin d -> Fin d -> Nat) (x : Fin N) (i j : Fin d),
        evalFinWordMat N d m_fn [x] i j = m_fn x i j := by
      intro m_fn x i j
      change natSumFin d (fun k => m_fn x i k * natMatId d k j) = m_fn x i j
      rw [natSumFin_single_w17 d (fun k => m_fn x i k * natMatId d k j) j]
      · simp [natMatId]
      · intro k hkj; have hkv : k.val ≠ j.val := fun hv => hkj (Fin.ext hv); simp [natMatId, hkv]
    have hpair_00 : ∀ (a b : Fin N),
        (∀ i : Fin d, i.val ≥ 1 -> mat b i z0 = 0) ->
        evalFinWordMat N d mat [a, b] z0 z0 = mat a z0 z0 * mat b z0 z0 := by
      intro a b hb0
      change natSumFin d (fun k => mat a z0 k * evalFinWordMat N d mat [b] k z0) = mat a z0 z0 * mat b z0 z0
      rw [natSumFin_single_w17 d (fun k => mat a z0 k * evalFinWordMat N d mat [b] k z0) z0]
      · rw [hmat1_eq mat b z0 z0]
      · intro k hk0
        have hk1 : k.val ≥ 1 := by have : k.val ≠ 0 := fun hv => hk0 (Fin.ext hv); omega
        rw [hmat1_eq mat b k z0, hb0 k hk1, Nat.mul_zero]
    -- Step 3: Cascade along `noR_rules` forces `(mat t)_{0,0} = 1` across all active `.T` symbols:
    have hin_unit : ∀ (acc : List Nat),
        (∀ x ∈ acc, ∀ hx : x < N, mat ⟨x, hx⟩ z0 z0 = 1) ->
        ∀ (y : Nat) (hy : y < N), inUnitTopLeftSetBoolW17 M acc y = true -> mat ⟨y, hy⟩ z0 z0 = 1 := by
      intro acc hacc y hy hin
      unfold inUnitTopLeftSetBoolW17 at hin
      rcases Bool.or_eq_true_iff.mp hin with hlb_b | hany_b
      · rcases of_decide_eq_true hlb_b with hlt2 | h48
        · exact (hL ⟨y, hy⟩ hlt2).1
        · exact (hB ⟨y, hy⟩ h48).1
      · rcases List.any_eq_true.mp hany_b with ⟨x, hx_m, hxy_b⟩
        have hxy : x = y := Nat.eq_of_beq_eq_true hxy_b
        subst hxy; exact hacc x hx_m hy
    have hwalk_unit : ∀ (steps : List (Nat × Nat × Nat × Nat)) (acc : List Nat),
        (∀ x ∈ acc, ∀ hx : x < N, mat ⟨x, hx⟩ z0 z0 = 1) ->
        checkUnitTopLeftCascadeBoolW17 M noR_rules acc steps = some finalAcc ->
        ∀ x ∈ finalAcc, ∀ hx : x < N, mat ⟨x, hx⟩ z0 z0 = 1 := by
      intro steps; induction steps with
      | nil =>
        intro acc hacc hs; simp only [checkUnitTopLeftCascadeBoolW17, Option.some.injEq] at hs
        subst hs; exact hacc
      | cons st tl ih =>
        rcases st with ⟨s1, s2, u1, u2⟩
        intro acc hacc hs
        unfold checkUnitTopLeftCascadeBoolW17 at hs
        by_cases hlt : s1 < 14 * M ∧ s2 < 14 * M ∧ u1 < 14 * M ∧ u2 < 14 * M
        · simp only [hlt] at hs
          let r_c : List (Fin (14 * M)) × List (Fin (14 * M)) :=
            ([⟨s1, hlt.1⟩, ⟨s2, hlt.2.1⟩], [⟨u1, hlt.2.2.1⟩, ⟨u2, hlt.2.2.2⟩])
          change (if (inUnitTopLeftSetBoolW17 M acc s1 && inUnitTopLeftSetBoolW17 M acc s2 &&
              noR_rules.any (· == r_c)) = true then
              checkUnitTopLeftCascadeBoolW17 M noR_rules (u2 :: acc) tl else none) = some finalAcc at hs
          by_cases hcond : (inUnitTopLeftSetBoolW17 M acc s1 && inUnitTopLeftSetBoolW17 M acc s2 &&
              noR_rules.any (· == r_c)) = true
          · rw [ite_true_of_w10 hcond] at hs
            rcases bool_and_split hcond with ⟨hs12, hmem_b⟩
            rcases bool_and_split hs12 with ⟨hs1_b, hs2_b⟩
            rcases List.any_eq_true.mp hmem_b with ⟨r_m, hr_flt, hr_eq_b⟩
            have hr_eq : r_m = r_c := beq_iff_eq.mp hr_eq_b
            subst hr_eq
            rcases List.mem_filter.mp hr_flt with ⟨hr_rules, hnoR_b⟩
            unfold noRRuleBoolW17 noRWordBoolW17 at hnoR_b
            rcases bool_and_split hnoR_b with ⟨hnl_r, hnr_r⟩
            rcases bool_and_split hnl_r with ⟨_, hs2_r⟩
            rcases bool_and_split hs2_r with ⟨hs2_out_b, _⟩
            rcases bool_and_split hnr_r with ⟨_, hu2_r⟩
            rcases bool_and_split hu2_r with ⟨hu2_out_b, _⟩
            have hs2_z0 : ∀ i : Fin d, i.val ≥ 1 -> mat ⟨s2, hlt.2.1⟩ i z0 = 0 := fun i hi =>
              hout_row_zero ⟨s2, hlt.2.1⟩ (of_decide_eq_true hs2_out_b)
                (hsym_in_rules r_c ⟨s2, hlt.2.1⟩ hr_rules (Or.inl (List.Mem.tail _ (List.Mem.head _)))) i z0 hi
            have hu2_z0 : ∀ i : Fin d, i.val ≥ 1 -> mat ⟨u2, hlt.2.2.2⟩ i z0 = 0 := fun i hi =>
              hout_row_zero ⟨u2, hlt.2.2.2⟩ (of_decide_eq_true hu2_out_b)
                (hsym_in_rules r_c ⟨u2, hlt.2.2.2⟩ hr_rules (Or.inr (List.Mem.tail _ (List.Mem.head _)))) i z0 hi
            have hl00 := hpair_00 ⟨s1, hlt.1⟩ ⟨s2, hlt.2.1⟩ hs2_z0
            have hr00 := hpair_00 ⟨u1, hlt.2.2.1⟩ ⟨u2, hlt.2.2.2⟩ hu2_z0
            rw [hin_unit acc hacc s1 hlt.1 hs1_b, hin_unit acc hacc s2 hlt.2.1 hs2_b, Nat.mul_one] at hl00
            have hwk00 := (hweak r_c hr_rules).1 z0 z0
            dsimp only [r_c, N] at hwk00 hl00 hr00
            rw [hl00, hr00] at hwk00
            have hu1_pos := hm_pos ⟨u1, hlt.2.2.1⟩
            have hu2_pos := hm_pos ⟨u2, hlt.2.2.2⟩
            dsimp only [z0] at hwk00
            have hu2_ge : mat ⟨u1, hlt.2.2.1⟩ ⟨0, hd⟩ ⟨0, hd⟩ * mat ⟨u2, hlt.2.2.2⟩ ⟨0, hd⟩ ⟨0, hd⟩ ≥
                1 * mat ⟨u2, hlt.2.2.2⟩ ⟨0, hd⟩ ⟨0, hd⟩ :=
              Nat.mul_le_mul_right _ hu1_pos
            rw [Nat.one_mul] at hu2_ge
            have hu2_one : mat ⟨u2, hlt.2.2.2⟩ z0 z0 = 1 := by dsimp only [z0]; omega
            apply ih (u2 :: acc) _ hs
            intro x hx_c hx_lt
            cases hx_c with
            | head => exact hu2_one
            | tail _ htl_m => exact hacc x htl_m hx_lt
          · rw [ite_false_of_w10 hcond] at hs; cases hs
        · simp only [hlt, dite_false] at hs; cases hs
    have hfinal_unit := hwalk_unit casc [] (fun _ h => by cases h) hc_opt
    have hall_cov := List.all_eq_true.mp hrules_cov
    have hT_unit : ∀ s : Fin N, s.val ≥ 8 * M ->
        symAppearsInRulesBool N s.val rules = true -> mat s z0 z0 = 1 := by
      intro s hs8 hact
      rcases exists_rule_of_symAppearsInRulesBool_w17 N s rules hact with ⟨r, hr_m, hs_m⟩
      rcases bool_and_split (hall_cov r hr_m) with ⟨_, hcov_s⟩
      rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp hcov_s s hs_m) with hlt8 | hin_b
      · have := of_decide_eq_true hlt8; omega
      · exact hin_unit finalAcc hfinal_unit s.val s.isLt hin_b
    -- Step 4: Sanitized upper zero-diagonal matrix `matSan` agrees with `mat` on all active non-`.R` symbols!
    let matSan (s : Fin N) (i j : Fin d) : Nat :=
      if i.val = 0 then
        if j.val = 0 then 1
        else if decide (s.val < 2 * M ∨ s.val ≥ 4 * M) && symAppearsInRulesBool N s.val rules then
          mat s z0 j
        else 0
      else 0
    have hsan_00 : ∀ s : Fin N, matSan s z0 z0 = 1 := fun _ => rfl
    have hsan_low : ∀ (s : Fin N) (i j : Fin d), i.val > 0 -> matSan s i j = 0 := by
      intro s i j hi
      have hne : i.val ≠ 0 := by omega
      dsimp [matSan]; rw [ite_false_of_w10 hne]
    have hsan_eq_act : ∀ s : Fin N, (s.val < 2 * M ∨ s.val ≥ 4 * M) ->
        symAppearsInRulesBool N s.val rules = true ->
        ∀ i j : Fin d, matSan s i j = mat s i j := by
      intro s hout hact i j
      by_cases hi0 : i.val = 0
      · have hie : i = z0 := Fin.ext hi0
        subst hie
        by_cases hj0 : j.val = 0
        · have hje : j = z0 := Fin.ext hj0
          subst hje
          have hm1_eq : mat s z0 z0 = 1 := by
            rcases hout with hlt2 | hge4
            · exact (hL s hlt2).1
            · by_cases hlt8 : s.val < 8 * M
              · exact (hB s ⟨hge4, hlt8⟩).1
              · exact hT_unit s (by omega) hact
          rw [hm1_eq]; rfl
        · have hc_t : (decide (s.val < 2 * M ∨ s.val ≥ 4 * M) && symAppearsInRulesBool N s.val rules) = true := by
            simp [hout, hact]
          dsimp only [matSan, z0]
          rw [ite_true_of_w10 rfl, ite_false_of_w10 hj0, ite_true_of_w10 hc_t]
      · rw [hsan_low s i j (by omega), hout_row_zero s hout hact i j (by omega)]
    have hmat_congr_noR : ∀ w : List (Fin N),
        noRWordBoolW17 M w = true ->
        (∀ s ∈ w, symAppearsInRulesBool N s.val rules = true) ->
        ∀ i j : Fin d, evalFinWordMat N d matSan w i j = evalFinWordMat N d mat w i j := by
      intro w; induction w with
      | nil => intros; rfl
      | cons s tl ih =>
        intro hnr hall i j
        unfold noRWordBoolW17 at hnr
        rcases bool_and_split hnr with ⟨hs_b, htl_nr⟩
        have hs_eq := hsan_eq_act s (of_decide_eq_true hs_b) (hall s (List.Mem.head _))
        have ih_tl := ih htl_nr (fun x hx => hall x (List.Mem.tail s hx))
        simp only [evalFinWordMat, natMatMul]
        unfold natSumFin
        have hsum : ∀ m : Nat, m ≤ d ->
            natSumPrefix d (fun k => matSan s i k * evalFinWordMat N d matSan tl k j) m =
            natSumPrefix d (fun k => mat s i k * evalFinWordMat N d mat tl k j) m := by
          intro m hm; induction m with
          | zero => rfl
          | succ m' ihm =>
            have hm_lt : m' < d := hm
            simp only [natSumPrefix, hm_lt, dite_true, ihm (Nat.le_of_lt hm),
                       hs_eq i ⟨m', hm_lt⟩, ih_tl ⟨m', hm_lt⟩ j]
        exact hsum d (Nat.le_refl d)
    have hvec_congr_nl : ∀ w : List (Fin N),
        nonLastOutsideRBool M w = true ->
        (∀ s ∈ w, symAppearsInRulesBool N s.val rules = true) ->
        ∀ i : Fin d, evalFinWordVec N d matSan v w i = evalFinWordVec N d mat v w i := by
      intro w; induction w with
      | nil => intros; rfl
      | cons s xs ih =>
        cases xs with
        | nil =>
          intros _ _ i
          simp only [evalFinWordVec, natMatVec]
          rw [natSumFin_zero_w17 d _ (fun _ => Nat.mul_zero _),
              natSumFin_zero_w17 d _ (fun _ => Nat.mul_zero _)]
        | cons s2 tl =>
          intro hnl hall i
          unfold nonLastOutsideRBool at hnl
          rcases bool_and_split hnl with ⟨hs_b, htl_nl⟩
          have hs_eq := hsan_eq_act s (of_decide_eq_true hs_b) (hall s (List.Mem.head _))
          have ih_tl := ih htl_nl (fun x hx => hall x (List.Mem.tail s hx))
          simp only [evalFinWordVec, natMatVec]
          apply congrArg (v s i + ·)
          unfold natSumFin
          have hsum : ∀ m : Nat, m ≤ d ->
              natSumPrefix d (fun k => matSan s i k * evalFinWordVec N d matSan v (s2 :: tl) k) m =
              natSumPrefix d (fun k => mat s i k * evalFinWordVec N d mat v (s2 :: tl) k) m := by
            intro m hm; induction m with
            | zero => rfl
            | succ m' ihm =>
              have hm_lt : m' < d := hm
              simp only [natSumPrefix, hm_lt, dite_true, ihm (Nat.le_of_lt hm),
                         hs_eq i ⟨m', hm_lt⟩, ih_tl ⟨m', hm_lt⟩]
          exact hsum d (Nat.le_refl d)
    have hsan_noR_weak : ∀ r ∈ noR_rules, ∀ i j : Fin d,
        evalFinWordMat N d matSan r.1 i j ≥ evalFinWordMat N d matSan r.2 i j := by
      intro r hr_f i j
      rcases List.mem_filter.mp hr_f with ⟨hr_m, hnr_b⟩
      rcases bool_and_split hnr_b with ⟨hnr1, hnr2⟩
      rw [hmat_congr_noR r.1 hnr1 (fun s hs => hsym_in_rules r s hr_m (Or.inl hs)) i j,
          hmat_congr_noR r.2 hnr2 (fun s hs => hsym_in_rules r s hr_m (Or.inr hs)) i j]
      exact (hweak r hr_m).1 i j
    have hsan_vec_eq : ∀ r ∈ rules, ∀ i : Fin d,
        evalFinWordVec N d matSan v r.1 i = evalFinWordVec N d mat v r.1 i ∧
        evalFinWordVec N d matSan v r.2 i = evalFinWordVec N d mat v r.2 i := by
      intro r hr_m i
      rcases bool_and_split (hall_cov r hr_m) with ⟨hnl12, _⟩
      rcases bool_and_split hnl12 with ⟨hnl1, hnl2⟩
      exact ⟨hvec_congr_nl r.1 hnl1 (fun s hs => hsym_in_rules r s hr_m (Or.inl hs)) i,
             hvec_congr_nl r.2 hnl2 (fun s hs => hsym_in_rules r s hr_m (Or.inr hs)) i⟩
    have hsan_vec_weak : ∀ r ∈ rules, ∀ i : Fin d,
        evalFinWordVec N d matSan v r.1 i ≥ evalFinWordVec N d matSan v r.2 i := by
      intro r hr_m i
      rcases hsan_vec_eq r hr_m i with ⟨e1, e2⟩
      rw [e1, e2]; exact (hweak r hr_m).2 i
    -- Step 5: 2-gram flow + Parikh syzygy on `matSan` forces `evalFinWordVec =` on all `r ∈ rules`:
    rcases upperZeroDiag_helpers_w17 N d hd matSan v hsan_00 hsan_low with
      ⟨htop_mat, hlow_vec, htop_vec⟩
    have hlast_dom : ∀ (x2 x1 : Fin N) (rs : List (List (Fin N) × List (Fin N))),
        (∀ r ∈ rs, ∀ i j : Fin d, evalFinWordMat N d matSan r.1 i j ≥ evalFinWordMat N d matSan r.2 i j) ->
        hasLastRulePairBool x2.val x1.val rs = true ->
        ∀ j : Fin d, matSan x2 z0 j ≥ matSan x1 z0 j := by
      intro x2 x1 rs; induction rs with
      | nil => intros _ hb; cases hb
      | cons r rtl ih =>
        intro hw_rs hb
        unfold hasLastRulePairBool at hb
        rcases Bool.or_eq_true_iff.mp hb with h0 | htl
        · cases hl : r.1 with
          | nil => rw [hl] at h0; cases h0
          | cons l0 ltl =>
            cases hr : r.2 with
            | nil => rw [hl, hr] at h0; cases h0
            | cons r0 r_tl =>
              rw [hl, hr] at h0
              rcases of_decide_eq_true h0 with ⟨ha, hb_e⟩
              have hlv : ∀ (d0 : Fin N) (w : List (Fin N)),
                  (lastFinSym d0 w).val = lastNatVal d0.val (w.map Fin.val) := by
                intro d0 w; induction w with
                | nil => rfl
                | cons a0 xs ihw => cases xs with | nil => rfl | cons b0 ys => exact ihw
              have hx2 : lastFinSym l0 (l0 :: ltl) = x2 := Fin.ext ((hlv l0 (l0 :: ltl)).trans ha)
              have hx1 : lastFinSym r0 (r0 :: r_tl) = x1 := Fin.ext ((hlv r0 (r0 :: r_tl)).trans hb_e)
              intro j
              have hm := hw_rs r (List.Mem.head _) z0 j
              rw [hl, hr, htop_mat l0 ltl j, htop_mat r0 r_tl j, hx2, hx1] at hm
              exact hm
        · exact ih (fun q hq => hw_rs q (List.Mem.tail r hq)) htl
    have hfirst_dom : ∀ (y2 y1 : Fin N) (rs : List (List (Fin N) × List (Fin N))),
        (∀ r ∈ rs, ∀ i : Fin d, evalFinWordVec N d matSan v r.1 i ≥ evalFinWordVec N d matSan v r.2 i) ->
        hasFirstRulePairBool y2.val y1.val rs = true ->
        ∀ j : Fin d, j.val > 0 -> v y2 j ≥ v y1 j := by
      intro y2 y1 rs; induction rs with
      | nil => intros _ hb; cases hb
      | cons r rtl ih =>
        intro hw_rs hb
        unfold hasFirstRulePairBool at hb
        rcases Bool.or_eq_true_iff.mp hb with h0 | htl
        · cases hl : r.1 with
          | nil => rw [hl] at h0; cases h0
          | cons l0 ltl =>
            cases hr : r.2 with
            | nil => rw [hl, hr] at h0; cases h0
            | cons r0 r_tl =>
              rw [hl, hr] at h0
              rcases of_decide_eq_true h0 with ⟨ha, hb_e⟩
              have hy2 : l0 = y2 := Fin.ext ha
              have hy1 : r0 = y1 := Fin.ext hb_e
              intro j hj
              have hv := hw_rs r (List.Mem.head _) j
              rw [hl, hr, hlow_vec l0 ltl j hj, hlow_vec r0 r_tl j hj, hy2, hy1] at hv
              exact hv
        · exact ih (fun q hq => hw_rs q (List.Mem.tail r hq)) htl
    let pw := pairWeightFin N d hd matSan v
    have hflow_le : evalWeightedPairs N pw (flowSrcItems flow) ≤
        evalWeightedPairs N pw (flowDstItems flow) := by
      have hfl : ∀ fl : List (Nat × Nat × Nat × Nat × Nat),
          (∀ e ∈ fl,
            (decide (e.1 < 14 * M ∧ e.2.1 < 14 * M ∧ e.2.2.1 < 14 * M ∧ e.2.2.2.1 < 14 * M) &&
             (decide (e.1 = e.2.2.1) || hasLastRulePairBool e.2.2.1 e.1 noR_rules) &&
             (decide (e.2.1 = e.2.2.2.1) || hasFirstRulePairBool e.2.2.2.1 e.2.1 rules)) = true) ->
          evalWeightedPairs N pw (flowSrcItems fl) ≤ evalWeightedPairs N pw (flowDstItems fl) := by
        intro fl; induction fl with
        | nil => intros; exact Nat.le_refl 0
        | cons e rest ih =>
          rcases e with ⟨x1, y1, x2, y2, fw⟩
          intro hall_f
          have he := hall_f (x1, y1, x2, y2, fw) (List.Mem.head _)
          rcases bool_and_split he with ⟨he1, hy_d⟩
          rcases bool_and_split he1 with ⟨hbnd, hx_d⟩
          rcases of_decide_eq_true hbnd with ⟨hx1, hy1, hx2, hy2⟩
          have hx_le : ∀ j : Fin d, matSan ⟨x1, hx1⟩ z0 j ≤ matSan ⟨x2, hx2⟩ z0 j := by
            rcases Bool.or_eq_true_iff.mp hx_d with heq | hrl
            · have hf : (⟨x1, hx1⟩ : Fin N) = ⟨x2, hx2⟩ := Fin.ext (of_decide_eq_true heq)
              intro j; rw [hf]; exact Nat.le_refl _
            · exact hlast_dom ⟨x2, hx2⟩ ⟨x1, hx1⟩ noR_rules hsan_noR_weak hrl
          have hy_le : ∀ j : Fin d, j.val > 0 -> v ⟨y1, hy1⟩ j ≤ v ⟨y2, hy2⟩ j := by
            rcases Bool.or_eq_true_iff.mp hy_d with heq | hrf
            · have hf : (⟨y1, hy1⟩ : Fin N) = ⟨y2, hy2⟩ := Fin.ext (of_decide_eq_true heq)
              intro j _; rw [hf]; exact Nat.le_refl _
            · exact hfirst_dom ⟨y2, hy2⟩ ⟨y1, hy1⟩ rules hsan_vec_weak hrf
          have hpw_le : pw ⟨x1, hx1⟩ ⟨y1, hy1⟩ ≤ pw ⟨x2, hx2⟩ ⟨y2, hy2⟩ := by
            dsimp [pw]; unfold pairWeightFin natSumFin
            exact natSumPrefix_mono_w5 d _ _ (fun j => by
              by_cases hj0 : j.val = 0
              · simp [hj0]
              · simp only [hj0, ite_false]; exact Nat.mul_le_mul (hx_le j) (hy_le j (by omega))) d
          have ih_r := ih (fun q hq => hall_f q (List.Mem.tail _ hq))
          simp only [flowSrcItems, flowDstItems, evalWeightedPairs,
                     show x1 < N from hx1, show y1 < N from hy1,
                     show x2 < N from hx2, show y2 < N from hy2, dite_true]
          exact Nat.add_le_add (Nat.mul_le_mul_left fw hpw_le) ih_r
      exact hfl flow (List.all_eq_true.mp hflow_all)
    rcases cancelAllWeightedPairs_sound_w17 N pw with ⟨happ_wp, hr2g_wp, hcan_wp⟩
    have hcan_le := hcan_wp _ _ hcan
    rw [happ_wp, happ_wp, (hr2g_wp rules syz).1, (hr2g_wp rules syz).2] at hcan_le
    have h2g_le : weighted2GramLhs N pw rules syz ≤ weighted2GramRhs N pw rules syz := by omega
    unfold checkPositiveParikhSyzygyFastBool at hsyz
    rcases bool_and_split hsyz with ⟨hs1, hpairs⟩
    rcases bool_and_split hs1 with ⟨hs2, hpos_m⟩
    rcases bool_and_split hs2 with ⟨_, hlen_eq⟩
    have hlen : rules.length = syz.length := of_decide_eq_true hlen_eq
    rcases accumSymCountsW11_spec N rules syz with ⟨hacc_len, hacc_get⟩
    let wt : Fin N -> Nat := fun s => v s z0
    rcases weightedParikh_eq_sum_sym N wt rules syz with ⟨hl_sum, hr_sum⟩
    have hpar_le : weightedParikhLhs N wt rules syz ≤ weightedParikhRhs N wt rules syz := by
      rw [hl_sum, hr_sum]
      exact natSumPrefix_mono_w5 N _ _ (fun s => Nat.mul_le_mul_left (wt s) (by
        have hle := checkPairsLeBoolW11_sound _ hpairs s.val (by rw [hacc_len]; exact s.isLt)
        rwa [hacc_get s] at hle)) N
    -- Combine `weightedParikh + weighted2Gram` rule-by-rule:
    have hcomb_eq : ∀ (rs : List (List (Fin N) × List (Fin N))) (ms : List Nat),
        rs.length = ms.length ->
        checkAllPosNatList ms = true ->
        (∀ r ∈ rs, evalFinWordVec N d matSan v r.1 z0 ≥ evalFinWordVec N d matSan v r.2 z0) ->
        weightedParikhLhs N wt rs ms + weighted2GramLhs N pw rs ms ≥
          weightedParikhRhs N wt rs ms + weighted2GramRhs N pw rs ms ∧
        (weightedParikhLhs N wt rs ms + weighted2GramLhs N pw rs ms ≤
          weightedParikhRhs N wt rs ms + weighted2GramRhs N pw rs ms ->
          ∀ r ∈ rs, evalFinWordVec N d matSan v r.1 z0 = evalFinWordVec N d matSan v r.2 z0) := by
      intro rs; induction rs with
      | nil => intros; exact ⟨Nat.le_refl 0, fun _ _ hr => by cases hr⟩
      | cons r0 rtl ih =>
        intro ms hl hp hw_r
        cases ms with
        | nil => simp at hl
        | cons m0 mtl =>
          rcases bool_and_split hp with ⟨hm0_b, hmtl_p⟩
          have hm0_pos : m0 ≥ 1 := of_decide_eq_true hm0_b
          rcases ih mtl (by simp at hl; omega) hmtl_p
            (fun q hq => hw_r q (List.Mem.tail r0 hq)) with ⟨hge_tl, himp_tl⟩
          have hw0 := hw_r r0 (List.Mem.head _)
          have hl0_eq := htop_vec r0.1
          have hr0_eq := htop_vec r0.2
          simp only [weightedParikhLhs, weightedParikhRhs, weighted2GramLhs, weighted2GramRhs]
          have hwt_eq : wt = (fun s => v s ⟨0, hd⟩) := rfl
          have hpw_eq : pw = pairWeightFin N d hd matSan v := rfl
          rw [← hwt_eq, ← hpw_eq] at hl0_eq hr0_eq
          have hm_l0 : m0 * evalFinParikh N wt r0.1 + m0 * eval2GramFin N pw r0.1 =
              m0 * evalFinWordVec N d matSan v r0.1 z0 := by
            dsimp only [z0]; rw [← Nat.mul_add, ← hl0_eq]
          have hm_r0 : m0 * evalFinParikh N wt r0.2 + m0 * eval2GramFin N pw r0.2 =
              m0 * evalFinWordVec N d matSan v r0.2 z0 := by
            dsimp only [z0]; rw [← Nat.mul_add, ← hr0_eq]
          have hm0_ge : m0 * evalFinWordVec N d matSan v r0.1 z0 ≥
              m0 * evalFinWordVec N d matSan v r0.2 z0 := Nat.mul_le_mul_left m0 hw0
          generalize m0 * evalFinParikh N wt r0.1 = PL,
            m0 * eval2GramFin N pw r0.1 = GL,
            m0 * evalFinParikh N wt r0.2 = PR,
            m0 * eval2GramFin N pw r0.2 = GR,
            weightedParikhLhs N wt rtl mtl = TL_P,
            weighted2GramLhs N pw rtl mtl = TL_G,
            weightedParikhRhs N wt rtl mtl = TR_P,
            weighted2GramRhs N pw rtl mtl = TR_G at hm_l0 hm_r0 hge_tl himp_tl ⊢
          refine ⟨by omega, fun htot_le r hr_m => ?_⟩
          cases hr_m with
          | head =>
            have heq_m : m0 * evalFinWordVec N d matSan v r0.1 z0 =
                m0 * evalFinWordVec N d matSan v r0.2 z0 := by omega
            exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < m0) heq_m
          | tail _ htl_m =>
            exact himp_tl (by omega) r htl_m
    have hsan_all_eq := (hcomb_eq rules syz hlen hpos_m
      (fun r hr => hsan_vec_weak r hr z0)).2 (Nat.add_le_add hpar_le h2g_le)
    refine ⟨hB_sub0, hT_unit, fun r hr => ?_⟩
    rcases hsan_vec_eq r hr z0 with ⟨e1, e2⟩
    rw [← e1, ← e2]; exact hsan_all_eq r hr

/--
  Theorem W17.1a (`twosided_c39_c78_bidirectional_b_and_t_toprow_impossibility`,
  `zero custom axioms`):
  Universal All-Dimension (`∀ d ≥ 1`) Active-`.B` Subdiagonal Cascade Collapse (`9` Active `.B`
  Symbols of `c39` & `18` Active `.B` Symbols of `c78`), Active-`.T` Top-Left Unit Lock Under
  Arbitrary `d × d` `.R` Boundary Matrices, & Universal Impossibility of
  `GenOmegaBidirectionalBAndTTopRowMatTower` Across `TwoSided(2 × 3)` `c39` & `TwoSided(2 × 6)` `c78`
  (`Branch P4.3`, witness `ZPOS_C39_BIDIRECTIONAL_B_AND_T_D2_FARKAS_ESCAPE`, `W17_H1`).
-/
theorem twosided_c39_c78_bidirectional_b_and_t_toprow_impossibility :
    let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
    let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
    (countActiveBSymsBool 3 c39 = 9 ∧ countActiveBSymsBool 6 c78 = 18) ∧
    (∀ (d : Nat) (hd : d ≥ 1) (mat : Fin 42 -> Fin d -> Fin d -> Nat),
      (∀ s : Fin 42, mat s ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1) ->
      (∀ s : Fin 42, 12 ≤ s.val ∧ s.val < 24 ->
        mat s ⟨0, hd⟩ ⟨0, hd⟩ = 1 ∧ ∀ (i j : Fin d), i.val ≥ 1 -> j.val ≥ 1 -> mat s i j = 0) ->
      (∀ s : Fin 42, s.val ≥ 24 -> ∀ (i j : Fin d), i.val ≥ 1 -> mat s i j = 0) ->
      (∀ r ∈ c39, ∀ i j : Fin d,
        evalFinWordMat 42 d mat r.1 i j ≥ evalFinWordMat 42 d mat r.2 i j) ->
      ∀ s : Fin 42, 12 ≤ s.val ∧ s.val < 24 -> symAppearsInRulesBool 42 s.val c39 = true ->
        ∀ (i j : Fin d), i.val ≥ 1 -> mat s i j = 0) ∧
    (∀ (d : Nat) (hd : d ≥ 1) (mat : Fin 84 -> Fin d -> Fin d -> Nat),
      (∀ s : Fin 84, mat s ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1) ->
      (∀ s : Fin 84, 24 ≤ s.val ∧ s.val < 48 ->
        mat s ⟨0, hd⟩ ⟨0, hd⟩ = 1 ∧ ∀ (i j : Fin d), i.val ≥ 1 -> j.val ≥ 1 -> mat s i j = 0) ->
      (∀ s : Fin 84, s.val ≥ 48 -> ∀ (i j : Fin d), i.val ≥ 1 -> mat s i j = 0) ->
      (∀ r ∈ c78, ∀ i j : Fin d,
        evalFinWordMat 84 d mat r.1 i j ≥ evalFinWordMat 84 d mat r.2 i j) ->
      ∀ s : Fin 84, 24 ≤ s.val ∧ s.val < 48 -> symAppearsInRulesBool 84 s.val c78 = true ->
        ∀ (i j : Fin d), i.val ≥ 1 -> mat s i j = 0) ∧
    (∀ (d : Nat) (hd : d ≥ 1) (k : Nat),
      ¬ GenOmegaBidirectionalBAndTTopRowMatTower 3 d hd k c39 ∧
      ¬ GenOmegaBidirectionalBAndTTopRowMatTower 6 d hd k c78) := by
  dsimp only
  rw [c39_eq_fastRules_w17, c78_eq_fastRules_w17]
  rcases bi_collapse_c39_c78_certs with ⟨hcnt39, hcnt78, hcert39, hcert78, hne39, hne78⟩
  have hb39 : activeBForcedByTRuleBool 3 c39FastRulesW17 = true := by
    have hc := hcert39; unfold checkBidirectionalCollapseCertBoolW17 at hc; exact (bool_and_split hc).1
  have hb78 : activeBForcedByTRuleBool 6 c78FastRulesW17 = true := by
    have hc := hcert78; unfold checkBidirectionalCollapseCertBoolW17 at hc; exact (bool_and_split hc).1
  have hno_tower : ∀ (M : Nat) (core : List (List (Fin (14 * M)) × List (Fin (14 * M))))
      (casc : List (Nat × Nat × Nat × Nat)) (syz : List Nat)
      (flow : List (Nat × Nat × Nat × Nat × Nat)),
      core ≠ [] ->
      checkBidirectionalCollapseCertBoolW17 M core casc syz flow = true ->
      ∀ (d : Nat) (hd : d ≥ 1) (k : Nat),
        ¬ GenOmegaBidirectionalBAndTTopRowMatTower M d hd k core := by
    intro M core casc syz flow hne hcert d hd
    cases hcore : core with
    | nil => exact False.elim (hne hcore)
    | cons r0 rs =>
      rw [← hcore]
      have hmem0 : r0 ∈ core := hcore ▸ List.Mem.head _
      have himp : ∀ (k : Nat) (cur : List (List (Fin (14 * M)) × List (Fin (14 * M)))),
          (∀ r ∈ core, r ∈ cur) -> ¬ GenOmegaBidirectionalBAndTTopRowMatTower M d hd k cur := by
        intro k; induction k with
        | zero =>
          intro cur hsub h0; rw [GenOmegaBidirectionalBAndTTopRowMatTower] at h0; subst h0
          exact List.not_mem_nil (hsub r0 hmem0)
        | succ k' ih =>
          intro cur hsub hsucc
          rcases hsucc with rfl | ⟨rem, mat, v, hm1, hL, hB, hT, hweak, hkeep, hrem⟩
          · exact List.not_mem_nil (hsub r0 hmem0)
          · have heq := (bidirectional_collapse_sound_w17 M core casc syz flow hcert d hd mat v
              hm1 hL hB hT (fun r hr => hweak r (hsub r hr))).2.2
            exact ih rem (fun r hr => hkeep r (hsub r hr)
              (by rw [heq r hr]; exact Nat.lt_irrefl _)) hrem
      exact fun k => himp k core (fun _ hr => hr)
  exact ⟨⟨hcnt39, hcnt78⟩,
         activeBForcedByTRuleBool_sound_w17 3 c39FastRulesW17 hb39,
         activeBForcedByTRuleBool_sound_w17 6 c78FastRulesW17 hb78,
         fun d hd k =>
           ⟨hno_tower 3 c39FastRulesW17 _ _ _ hne39 hcert39 d hd k,
            hno_tower 6 c78FastRulesW17 _ _ _ hne78 hcert78 d hd k⟩⟩

-- ----------------------------------------------------------------------------
-- Section 1B: Infinite 4-Parameter Simultaneous Bidirectional `.B` + `.T` + `.R`
--             Mixed Zero-Diagonal `d = 2` Cones & Parameterized Farkas Syzygies
-- ----------------------------------------------------------------------------

/-- Infinite 4-parameter simultaneous bidirectional `.B` + `.T` + `.R`-boundary-growth `d = 2`
    matrix cone on `Fin 42` (`c39`):
    - `.R` boundary growth: `(M_6)_{0,0} = (M_9)_{0,0} = k` (`k ≥ 2`), `(M_6)_{1,1} = 1`,
    - `.B` top-row off-diagonals: `(M_{22})_{0,1} = (M_{23})_{0,1} = α`,
    - `.B` subdiagonals: `(M_{14})_{1,0} = (M_{18})_{1,0} = β`, `(M_{20})_{1,0} = γ`,
    - `.T` top-row off-diagonals: `(M_{37})_{0,1} = (M_{40})_{0,1} = (M_{41})_{0,1} = α`,
    - `.T` subdiagonals: `(M_{28})_{1,0} = β`, `(M_{31})_{1,0} = 2β`, `(M_{32})_{1,0} = β + γ`,
      `(M_{36})_{1,0} = (M_{38})_{1,0} = γ`, `(M_{37})_{1,0} = 2γ` (`37` is bidirectional on a single symbol!). -/
def biBTRMat2DC39 (k alpha beta gamma : Nat) (s : Fin 42) (i j : Fin 2) : Nat :=
  match i.val, j.val with
  | 0, 0 => if s.val == 6 || s.val == 9 then k else 1
  | 0, 1 =>
    match s.val with
    | 22 => alpha | 23 => alpha | 37 => alpha | 40 => alpha | 41 => alpha | _ => 0
  | 1, 0 =>
    match s.val with
    | 14 => beta | 18 => beta | 20 => gamma
    | 28 => beta | 31 => 2 * beta | 32 => beta + gamma
    | 36 => gamma | 37 => 2 * gamma | 38 => gamma | _ => 0
  | _, _ => if s.val == 6 then 1 else 0

/-- Lifted 4-parameter simultaneous bidirectional `.B` + `.T` + `.R` `d = 2` cone on `Fin 84` (`c78`). -/
def biBTRMat2DC78 (k alpha beta gamma : Nat) (s : Fin 84) (i j : Fin 2) : Nat :=
  biBTRMat2DC39 k alpha beta gamma (projSym84To42 s) i j

/-- Non-negative 4-rule integral Farkas row-1 base multipliers `μ_1(r)` for `biBTRMat2DC39`
    (supported on `([33,22],[17,37]): 6`, `([35,16],[21,28]): 3`, `([35,23],[17,38]): 4`, `([39,22],[23,40]): 1`). -/
def farkasMu1BiBTRC39 : List (Fin 42) -> Nat
  | a :: b :: _ =>
    match a.val, b.val with
    | 33, 22 => 6 | 35, 16 => 3 | 35, 23 => 4 | 39, 22 => 1 | _, _ => 0
  | _ => 0

/-- Non-negative 11-rule integral Farkas row-1 base multipliers `μ_1(r)` for `biBTRMat2DC78`. -/
def farkasMu1BiBTRC78 : List (Fin 84) -> Nat
  | a :: b :: _ =>
    match a.val, b.val with
    | 68, 31 => 30 | 68, 34 => 2  | 69, 43 => 9  | 69, 46 => 1
    | 71, 44 => 7  | 79, 18 => 15 | 80, 31 => 37 | 80, 34 => 7
    | 81, 46 => 29 | 82, 32 => 9  | 83, 47 => 1  | _, _ => 0
  | _ => 0

private abbrev fin2Z0W17 : Fin 2 := ⟨0, by decide⟩
private abbrev fin2Z1W17 : Fin 2 := ⟨1, by decide⟩

private theorem mat2_step_expandN_w17 (N : Nat) (M : Fin N -> Fin 2 -> Fin 2 -> Nat)
    (v : Fin N -> Fin 2 -> Nat) (s : Fin N) (rest : List (Fin N)) (i : Fin 2) :
    evalFinWordVec N 2 M v (s :: rest) i =
      v s i + M s i fin2Z0W17 * evalFinWordVec N 2 M v rest fin2Z0W17 +
        M s i fin2Z1W17 * evalFinWordVec N 2 M v rest fin2Z1W17 := by
  change v s i + ((0 + M s i fin2Z0W17 * evalFinWordVec N 2 M v rest fin2Z0W17) +
    M s i fin2Z1W17 * evalFinWordVec N 2 M v rest fin2Z1W17) = _
  omega

private def biWordRow0LinearBoolW17 (N : Nat) (proj : Fin N -> Fin 42) : List (Fin N) -> Bool
  | [] => true
  | [_] => true
  | [s1, _] => decide ((proj s1).val ≠ 6 ∧ (proj s1).val ≠ 9)
  | [s1, s2, _] =>
    decide ((proj s1).val ≠ 6 ∧ (proj s1).val ≠ 9 ∧ ((proj s2).val = 13 ∨ (proj s2).val = 16))
  | _ => false

private def biWordRow1HeadConstBoolW17 (N : Nat) (proj : Fin N -> Fin 42) : List (Fin N) -> Bool
  | [] => true
  | [_] => true
  | s1 :: _ :: _ =>
    let p := (proj s1).val
    decide (p ≠ 6 ∧ p ≠ 14 ∧ p ≠ 18 ∧ p ≠ 20 ∧ p ≠ 28 ∧ p ≠ 31 ∧ p ≠ 32 ∧ p ≠ 36 ∧ p ≠ 37 ∧ p ≠ 38)

private theorem biBTRMatProj_vec_linearity_w17 (N : Nat) (proj : Fin N -> Fin 42)
    (k alpha beta gamma : Nat) (v : Fin N -> Fin 2 -> Nat) :
    let matFn := fun k' a' b' g' (s : Fin N) => biBTRMat2DC39 k' a' b' g' (proj s)
    (∀ w : List (Fin N), biWordRow1HeadConstBoolW17 N proj w = true ->
      evalFinWordVec N 2 (matFn k alpha beta gamma) v w fin2Z1W17 =
        evalFinWordVec N 2 (matFn 1 0 0 0) v w fin2Z1W17) ∧
    (∀ w : List (Fin N), biWordRow0LinearBoolW17 N proj w = true ->
      evalFinWordVec N 2 (matFn 1 0 0 0) v w fin2Z0W17 ≤
        evalFinWordVec N 2 (matFn 1 1 0 0) v w fin2Z0W17 ∧
      evalFinWordVec N 2 (matFn k alpha beta gamma) v w fin2Z0W17 =
        evalFinWordVec N 2 (matFn 1 0 0 0) v w fin2Z0W17 +
          alpha * (evalFinWordVec N 2 (matFn 1 1 0 0) v w fin2Z0W17 -
            evalFinWordVec N 2 (matFn 1 0 0 0) v w fin2Z0W17)) := by
  dsimp only
  let matFn := fun k' a' b' g' (s : Fin N) => biBTRMat2DC39 k' a' b' g' (proj s)
  have hv_single : ∀ (M : Fin N -> Fin 2 -> Fin 2 -> Nat) (s : Fin N) (i : Fin 2),
      evalFinWordVec N 2 M v [s] i = v s i := by
    intro M s i
    rw [mat2_step_expandN_w17 N M v s [] i]
    change v s i + M s i fin2Z0W17 * 0 + M s i fin2Z1W17 * 0 = v s i; omega
  have hs00_unit : ∀ (s : Fin N), (proj s).val ≠ 6 -> (proj s).val ≠ 9 ->
      ∀ k' a' b' g' : Nat, matFn k' a' b' g' s fin2Z0W17 fin2Z0W17 = 1 := by
    intro s hn6 hn9 k' a' b' g'
    dsimp [matFn]; unfold biBTRMat2DC39
    rw [beq_false_of_ne hn6, beq_false_of_ne hn9]; rfl
  have hs01_lin : ∀ (s : Fin N) (k' a' b' g' : Nat),
      matFn k' a' b' g' s fin2Z0W17 fin2Z1W17 =
        a' * matFn 1 1 0 0 s fin2Z0W17 fin2Z1W17 ∧
      matFn 1 0 0 0 s fin2Z0W17 fin2Z1W17 = 0 := by
    intro s k' a' b' g'
    refine ⟨?_, ?_⟩
    · change (match (proj s).val with
        | 22 => a' | 23 => a' | 37 => a' | 40 => a' | 41 => a' | _ => 0) =
        a' * (match (proj s).val with
        | 22 => 1 | 23 => 1 | 37 => 1 | 40 => 1 | 41 => 1 | _ => 0)
      split <;> omega
    · change (match (proj s).val with
        | 22 => 0 | 23 => 0 | 37 => 0 | 40 => 0 | 41 => 0 | _ => 0) = 0
      split <;> rfl
  have hs13_16 : ∀ (s : Fin N), ((proj s).val = 13 ∨ (proj s).val = 16) ->
      ∀ k' a' b' g' : Nat,
        matFn k' a' b' g' s fin2Z0W17 fin2Z0W17 = 1 ∧
        matFn k' a' b' g' s fin2Z0W17 fin2Z1W17 = 0 ∧
        matFn k' a' b' g' s fin2Z1W17 fin2Z0W17 = 0 ∧
        matFn k' a' b' g' s fin2Z1W17 fin2Z1W17 = 0 := by
    intro s h1316 k' a' b' g'
    rcases h1316 with h | h <;> simp [matFn, biBTRMat2DC39, h]
  refine ⟨?_, ?_⟩
  · intro w hbw
    cases w with
    | nil => rfl
    | cons s1 xs =>
      cases xs with
      | nil => rw [hv_single, hv_single]
      | cons s2 tl =>
        unfold biWordRow1HeadConstBoolW17 at hbw
        rcases of_decide_eq_true hbw with ⟨hn6, hn14, hn18, hn20, hn28, hn31, hn32, hn36, hn37, hn38⟩
        have hr10_a : ∀ k' a' b' g' : Nat, matFn k' a' b' g' s1 fin2Z1W17 fin2Z0W17 = 0 := by
          intro k' a' b' g'
          change (match (proj s1).val with
            | 14 => b' | 18 => b' | 20 => g' | 28 => b' | 31 => 2 * b'
            | 32 => b' + g' | 36 => g' | 37 => 2 * g' | 38 => g' | _ => 0) = 0
          split <;> omega
        have hr11_a : ∀ k' a' b' g' : Nat, matFn k' a' b' g' s1 fin2Z1W17 fin2Z1W17 = 0 := by
          intro k' a' b' g'
          dsimp [matFn]; unfold biBTRMat2DC39
          simp [beq_false_of_ne hn6]
        rw [mat2_step_expandN_w17 N (matFn k alpha beta gamma) v s1 (s2 :: tl) fin2Z1W17,
            mat2_step_expandN_w17 N (matFn 1 0 0 0) v s1 (s2 :: tl) fin2Z1W17,
            hr10_a k alpha beta gamma, hr10_a 1 0 0 0,
            hr11_a k alpha beta gamma, hr11_a 1 0 0 0]
        omega
  · intro w hbw
    cases w with
    | nil => exact ⟨Nat.le_refl 0, by simp [evalFinWordVec]⟩
    | cons s1 xs =>
      cases xs with
      | nil => simp [hv_single]
      | cons s2 xs2 =>
        cases xs2 with
        | nil =>
          unfold biWordRow0LinearBoolW17 at hbw
          rcases of_decide_eq_true hbw with ⟨hn6, hn9⟩
          rw [mat2_step_expandN_w17 N (matFn 1 0 0 0) v s1 [s2] fin2Z0W17,
              mat2_step_expandN_w17 N (matFn 1 1 0 0) v s1 [s2] fin2Z0W17,
              mat2_step_expandN_w17 N (matFn k alpha beta gamma) v s1 [s2] fin2Z0W17,
              hs00_unit s1 hn6 hn9 1 0 0 0, hs00_unit s1 hn6 hn9 1 1 0 0,
              hs00_unit s1 hn6 hn9 k alpha beta gamma,
              (hs01_lin s1 1 0 0 0).2, (hs01_lin s1 k alpha beta gamma).1,
              hv_single (matFn 1 0 0 0), hv_single (matFn 1 0 0 0),
              hv_single (matFn 1 1 0 0), hv_single (matFn 1 1 0 0),
              hv_single (matFn k alpha beta gamma), hv_single (matFn k alpha beta gamma)]
          rw [Nat.zero_mul, Nat.add_zero, Nat.one_mul, Nat.mul_assoc]
          refine ⟨by omega, ?_⟩
          have hsub : (v s1 fin2Z0W17 + v s2 fin2Z0W17 + matFn 1 1 0 0 s1 fin2Z0W17 fin2Z1W17 * v s2 fin2Z1W17) -
              (v s1 fin2Z0W17 + v s2 fin2Z0W17) =
              matFn 1 1 0 0 s1 fin2Z0W17 fin2Z1W17 * v s2 fin2Z1W17 := by omega
          rw [hsub]
        | cons s3 xs3 =>
          cases xs3 with
          | nil =>
            unfold biWordRow0LinearBoolW17 at hbw
            rcases of_decide_eq_true hbw with ⟨hn6, hn9, h1316⟩
            have hv_tail : ∀ k' a' b' g' : Nat,
                evalFinWordVec N 2 (matFn k' a' b' g') v [s2, s3] fin2Z0W17 =
                  v s2 fin2Z0W17 + v s3 fin2Z0W17 ∧
                evalFinWordVec N 2 (matFn k' a' b' g') v [s2, s3] fin2Z1W17 =
                  v s2 fin2Z1W17 := by
              intro k' a' b' g'
              rcases hs13_16 s2 h1316 k' a' b' g' with ⟨m00, m01, m10, m11⟩
              refine ⟨?_, ?_⟩
              · rw [mat2_step_expandN_w17 N (matFn k' a' b' g') v s2 [s3] fin2Z0W17, m00, m01,
                    hv_single (matFn k' a' b' g'), hv_single (matFn k' a' b' g')]; omega
              · rw [mat2_step_expandN_w17 N (matFn k' a' b' g') v s2 [s3] fin2Z1W17, m10, m11,
                    hv_single (matFn k' a' b' g'), hv_single (matFn k' a' b' g')]; omega
            rw [mat2_step_expandN_w17 N (matFn 1 0 0 0) v s1 [s2, s3] fin2Z0W17,
                mat2_step_expandN_w17 N (matFn 1 1 0 0) v s1 [s2, s3] fin2Z0W17,
                mat2_step_expandN_w17 N (matFn k alpha beta gamma) v s1 [s2, s3] fin2Z0W17,
                hs00_unit s1 hn6 hn9 1 0 0 0, hs00_unit s1 hn6 hn9 1 1 0 0,
                hs00_unit s1 hn6 hn9 k alpha beta gamma,
                (hs01_lin s1 1 0 0 0).2, (hs01_lin s1 k alpha beta gamma).1,
                (hv_tail 1 0 0 0).1, (hv_tail 1 1 0 0).1, (hv_tail k alpha beta gamma).1,
                (hv_tail 1 1 0 0).2, (hv_tail k alpha beta gamma).2]
            rw [Nat.zero_mul, Nat.add_zero, Nat.one_mul, Nat.mul_assoc]
            refine ⟨by omega, ?_⟩
            have hsub3 : (v s1 fin2Z0W17 + (v s2 fin2Z0W17 + v s3 fin2Z0W17) +
                matFn 1 1 0 0 s1 fin2Z0W17 fin2Z1W17 * v s2 fin2Z1W17) -
                (v s1 fin2Z0W17 + (v s2 fin2Z0W17 + v s3 fin2Z0W17)) =
                matFn 1 1 0 0 s1 fin2Z0W17 fin2Z1W17 * v s2 fin2Z1W17 := by omega
            rw [hsub3]
          | cons _ _ => cases hbw

private def farkasBiVecLhsN (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 : List (Fin N) -> Nat) (k alpha beta gamma : Nat) (v : Fin N -> Fin 2 -> Nat) :
    List (List (Fin N) × List (Fin N)) -> Nat
  | [] => 0
  | (l, _) :: rs =>
    let M := fun s => biBTRMat2DC39 k alpha beta gamma (proj s)
    mu0 l * evalFinWordVec N 2 M v l fin2Z0W17 +
      (alpha * mu1 l) * evalFinWordVec N 2 M v l fin2Z1W17 +
      farkasBiVecLhsN N proj mu0 mu1 k alpha beta gamma v rs

private def farkasBiVecRhsN (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 : List (Fin N) -> Nat) (k alpha beta gamma : Nat) (v : Fin N -> Fin 2 -> Nat) :
    List (List (Fin N) × List (Fin N)) -> Nat
  | [] => 0
  | (l, r) :: rs =>
    let M := fun s => biBTRMat2DC39 k alpha beta gamma (proj s)
    mu0 l * evalFinWordVec N 2 M v r fin2Z0W17 +
      (alpha * mu1 l) * evalFinWordVec N 2 M v r fin2Z1W17 +
      farkasBiVecRhsN N proj mu0 mu1 k alpha beta gamma v rs

private def evalWordVec2DFastW17 (N : Nat) (M : Fin N -> Fin 2 -> Fin 2 -> Nat)
    (v : Fin N -> Fin 2 -> Nat) : List (Fin N) -> Nat × Nat
  | [] => (0, 0)
  | s :: u =>
    let p := evalWordVec2DFastW17 N M v u
    (v s fin2Z0W17 + M s fin2Z0W17 fin2Z0W17 * p.1 + M s fin2Z0W17 fin2Z1W17 * p.2,
     v s fin2Z1W17 + M s fin2Z1W17 fin2Z0W17 * p.1 + M s fin2Z1W17 fin2Z1W17 * p.2)

private def farkasBiFastPairN (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 : List (Fin N) -> Nat) (k alpha beta gamma : Nat) (v : Fin N -> Fin 2 -> Nat) :
    List (List (Fin N) × List (Fin N)) -> Nat × Nat
  | [] => (0, 0)
  | (l, r) :: rs =>
    let M := fun s => biBTRMat2DC39 k alpha beta gamma (proj s)
    let pl := evalWordVec2DFastW17 N M v l
    let pr := evalWordVec2DFastW17 N M v r
    let ptl := farkasBiFastPairN N proj mu0 mu1 k alpha beta gamma v rs
    (mu0 l * pl.1 + (alpha * mu1 l) * pl.2 + ptl.1,
     mu0 l * pr.1 + (alpha * mu1 l) * pr.2 + ptl.2)

private theorem farkasBiFastPairN_eq (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 : List (Fin N) -> Nat) (k alpha beta gamma : Nat) (v : Fin N -> Fin 2 -> Nat) :
    ∀ rs : List (List (Fin N) × List (Fin N)),
      farkasBiFastPairN N proj mu0 mu1 k alpha beta gamma v rs =
        (farkasBiVecLhsN N proj mu0 mu1 k alpha beta gamma v rs,
         farkasBiVecRhsN N proj mu0 mu1 k alpha beta gamma v rs) := by
  let M := fun s => biBTRMat2DC39 k alpha beta gamma (proj s)
  have hv_eq : ∀ w : List (Fin N),
      evalWordVec2DFastW17 N M v w =
        (evalFinWordVec N 2 M v w fin2Z0W17, evalFinWordVec N 2 M v w fin2Z1W17) := by
    intro w; induction w with
    | nil => rfl
    | cons s u ih => simp only [evalWordVec2DFastW17, ih, mat2_step_expandN_w17 N M v s u]
  dsimp only [M] at hv_eq
  intro rs; induction rs with
  | nil => rfl
  | cons r0 rtl ih =>
    rcases r0 with ⟨l, r⟩
    simp only [farkasBiFastPairN, farkasBiVecLhsN, farkasBiVecRhsN, hv_eq, ih]

private def checkBiFarkasRangeNBool (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 : List (Fin N) -> Nat) (j0 : Fin 2)
    (rules : List (List (Fin N) × List (Fin N))) (lo : Nat) : Nat -> Bool
  | 0 => true
  | c + 1 =>
    if h : lo + c < N then
      let p0 := farkasBiFastPairN N proj mu0 mu1 1 0 0 0 (basisVec2D N ⟨lo + c, h⟩ j0) rules
      let p1 := farkasBiFastPairN N proj mu0 mu1 1 1 0 0 (basisVec2D N ⟨lo + c, h⟩ j0) rules
      decide (p0.1 ≤ p0.2 ∧ p1.1 - p0.1 ≤ p1.2 - p0.2) &&
        checkBiFarkasRangeNBool N proj mu0 mu1 j0 rules lo c
    else false

private def checkBiFarkasCoordNBool (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 : List (Fin N) -> Nat) (j0 : Fin 2)
    (rules : List (List (Fin N) × List (Fin N))) : Bool :=
  checkBiFarkasRangeNBool N proj mu0 mu1 j0 rules 0 N

private theorem checkBiFarkasRangeNBool_append (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 : List (Fin N) -> Nat) (j0 : Fin 2)
    (rules : List (List (Fin N) × List (Fin N))) (a b : Nat)
    (ha : checkBiFarkasRangeNBool N proj mu0 mu1 j0 rules 0 a = true)
    (hb : checkBiFarkasRangeNBool N proj mu0 mu1 j0 rules a b = true) :
    checkBiFarkasRangeNBool N proj mu0 mu1 j0 rules 0 (a + b) = true := by
  induction b with
  | zero => simpa using ha
  | succ b' ih =>
    rw [show a + (b' + 1) = (a + b') + 1 by omega]
    unfold checkBiFarkasRangeNBool at hb ⊢
    by_cases hlt : a + b' < N
    · have hlt0 : 0 + (a + b') < N := by omega
      simp only [hlt, hlt0, dite_true] at hb ⊢
      rcases bool_and_split hb with ⟨hc, hprev⟩
      have hc0 : decide (
          (farkasBiFastPairN N proj mu0 mu1 1 0 0 0 (basisVec2D N ⟨0 + (a + b'), hlt0⟩ j0) rules).1 ≤
          (farkasBiFastPairN N proj mu0 mu1 1 0 0 0 (basisVec2D N ⟨0 + (a + b'), hlt0⟩ j0) rules).2 ∧
          (farkasBiFastPairN N proj mu0 mu1 1 1 0 0 (basisVec2D N ⟨0 + (a + b'), hlt0⟩ j0) rules).1 -
          (farkasBiFastPairN N proj mu0 mu1 1 0 0 0 (basisVec2D N ⟨0 + (a + b'), hlt0⟩ j0) rules).1 ≤
          (farkasBiFastPairN N proj mu0 mu1 1 1 0 0 (basisVec2D N ⟨0 + (a + b'), hlt0⟩ j0) rules).2 -
          (farkasBiFastPairN N proj mu0 mu1 1 0 0 0 (basisVec2D N ⟨0 + (a + b'), hlt0⟩ j0) rules).2) = true := by
        have hfin : (⟨0 + (a + b'), hlt0⟩ : Fin N) = ⟨a + b', hlt⟩ := Fin.ext (Nat.zero_add _)
        simpa only [hfin] using hc
      rw [hc0, ih hprev]; rfl
    · simp only [hlt, dite_false] at hb; cases hb

private def checkWordShapeBiNBool (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 : List (Fin N) -> Nat) (rs : List (List (Fin N) × List (Fin N))) : Bool :=
  rs.all (fun r =>
    biWordRow0LinearBoolW17 N proj r.1 && biWordRow0LinearBoolW17 N proj r.2 &&
    (decide (mu1 r.1 = 0) ||
      (biWordRow1HeadConstBoolW17 N proj r.1 && biWordRow1HeadConstBoolW17 N proj r.2)) &&
    decide (mu0 r.1 ≥ 1))

private def w16FarkasFastPairOnBi (mu0 mu1 : List (Fin 42) -> Nat) (v : Fin 42 -> Fin 2 -> Nat) :
    List (List (Fin 42) × List (Fin 42)) -> Nat × Nat
  | [] => (0, 0)
  | (l, r) :: rs =>
    let pl := evalWordVec2DFastW17 42 (biBTRMat2DC39 2 1 1 1) v l
    let pr := evalWordVec2DFastW17 42 (biBTRMat2DC39 2 1 1 1) v r
    let ptl := w16FarkasFastPairOnBi mu0 mu1 v rs
    (mu0 l * pl.1 + mu1 l * pl.2 + ptl.1,
     mu0 l * pr.1 + mu1 l * pr.2 + ptl.2)

private def w16FarkasLhsOnBi (mu0 mu1 : List (Fin 42) -> Nat) (v : Fin 42 -> Fin 2 -> Nat) :
    List (List (Fin 42) × List (Fin 42)) -> Nat
  | [] => 0
  | (l, _) :: rs =>
    mu0 l * evalFinWordVec 42 2 (biBTRMat2DC39 2 1 1 1) v l fin2Z0W17 +
      mu1 l * evalFinWordVec 42 2 (biBTRMat2DC39 2 1 1 1) v l fin2Z1W17 +
      w16FarkasLhsOnBi mu0 mu1 v rs

private def w16FarkasRhsOnBi (mu0 mu1 : List (Fin 42) -> Nat) (v : Fin 42 -> Fin 2 -> Nat) :
    List (List (Fin 42) × List (Fin 42)) -> Nat
  | [] => 0
  | (l, r) :: rs =>
    mu0 l * evalFinWordVec 42 2 (biBTRMat2DC39 2 1 1 1) v r fin2Z0W17 +
      mu1 l * evalFinWordVec 42 2 (biBTRMat2DC39 2 1 1 1) v r fin2Z1W17 +
      w16FarkasRhsOnBi mu0 mu1 v rs

private theorem w16FarkasFastPairOnBi_eq (mu0 mu1 : List (Fin 42) -> Nat) (v : Fin 42 -> Fin 2 -> Nat) :
    ∀ rs : List (List (Fin 42) × List (Fin 42)),
      w16FarkasFastPairOnBi mu0 mu1 v rs =
        (w16FarkasLhsOnBi mu0 mu1 v rs, w16FarkasRhsOnBi mu0 mu1 v rs) := by
  have hv_eq : ∀ w : List (Fin 42),
      evalWordVec2DFastW17 42 (biBTRMat2DC39 2 1 1 1) v w =
        (evalFinWordVec 42 2 (biBTRMat2DC39 2 1 1 1) v w fin2Z0W17,
         evalFinWordVec 42 2 (biBTRMat2DC39 2 1 1 1) v w fin2Z1W17) := by
    intro w; induction w with
    | nil => rfl
    | cons s u ih =>
      simp only [evalWordVec2DFastW17, ih, mat2_step_expandN_w17 42 (biBTRMat2DC39 2 1 1 1) v s u]
  intro rs; induction rs with
  | nil => rfl
  | cons r0 rtl ih =>
    rcases r0 with ⟨l, r⟩
    simp only [w16FarkasFastPairOnBi, w16FarkasLhsOnBi, w16FarkasRhsOnBi, hv_eq, ih]

private theorem bi_c39_c78_shape_and_witness_certs :
    checkWordShapeBiNBool 42 id farkasMu0CoupledC39 farkasMu1BiBTRC39 c39FastRulesW17 = true ∧
    checkWordShapeBiNBool 84 projSym84To42 farkasMu0CoupledC78 farkasMu1BiBTRC78 c78FastRulesW17 = true ∧
    c78FastRulesW17.all (fun r =>
      c39FastRulesW17.any (· == (r.1.map projSym84To42, r.2.map projSym84To42))) = true ∧
    countStrictMat2DRules 42 (biBTRMat2DC39 2 1 1 1) c39FastRulesW17 = 18 ∧
    countStrictMat2DRules 84 (biBTRMat2DC78 2 1 1 1) c78FastRulesW17 = 36 ∧
    (let p1 := w16FarkasFastPairOnBi farkasMu0C39 farkasMu1C39
       (basisVec2D 42 ⟨17, by decide⟩ fin2Z1W17) c39FastRulesW17
     let p2 := w16FarkasFastPairOnBi farkasMu0CoupledC39 farkasMu1CoupledC39
       (basisVec2D 42 ⟨17, by decide⟩ fin2Z0W17) c39FastRulesW17
     p1.1 - p1.2 = 13 ∧ p2.1 - p2.2 = 10) := by decide

private theorem bi_c39_farkas_b0_cert :
    checkBiFarkasCoordNBool 42 id farkasMu0CoupledC39 farkasMu1BiBTRC39 fin2Z0W17 c39FastRulesW17 = true := by
  decide

private theorem bi_c39_farkas_b1_cert :
    checkBiFarkasCoordNBool 42 id farkasMu0CoupledC39 farkasMu1BiBTRC39 fin2Z1W17 c39FastRulesW17 = true := by
  decide

private theorem bi_c78_b0_c0 : checkBiFarkasRangeNBool 84 projSym84To42 farkasMu0CoupledC78 farkasMu1BiBTRC78 fin2Z0W17 c78FastRulesW17 0 12 = true := by decide
private theorem bi_c78_b0_c1 : checkBiFarkasRangeNBool 84 projSym84To42 farkasMu0CoupledC78 farkasMu1BiBTRC78 fin2Z0W17 c78FastRulesW17 12 12 = true := by decide
private theorem bi_c78_b0_c2 : checkBiFarkasRangeNBool 84 projSym84To42 farkasMu0CoupledC78 farkasMu1BiBTRC78 fin2Z0W17 c78FastRulesW17 24 12 = true := by decide
private theorem bi_c78_b0_c3 : checkBiFarkasRangeNBool 84 projSym84To42 farkasMu0CoupledC78 farkasMu1BiBTRC78 fin2Z0W17 c78FastRulesW17 36 12 = true := by decide
private theorem bi_c78_b0_c4 : checkBiFarkasRangeNBool 84 projSym84To42 farkasMu0CoupledC78 farkasMu1BiBTRC78 fin2Z0W17 c78FastRulesW17 48 12 = true := by decide
private theorem bi_c78_b0_c5 : checkBiFarkasRangeNBool 84 projSym84To42 farkasMu0CoupledC78 farkasMu1BiBTRC78 fin2Z0W17 c78FastRulesW17 60 12 = true := by decide
private theorem bi_c78_b0_c6 : checkBiFarkasRangeNBool 84 projSym84To42 farkasMu0CoupledC78 farkasMu1BiBTRC78 fin2Z0W17 c78FastRulesW17 72 12 = true := by decide

private theorem bi_c78_farkas_b0_cert :
    checkBiFarkasCoordNBool 84 projSym84To42 farkasMu0CoupledC78 farkasMu1BiBTRC78 fin2Z0W17 c78FastRulesW17 = true := by
  unfold checkBiFarkasCoordNBool
  have h24 := checkBiFarkasRangeNBool_append 84 _ _ _ _ _ 12 12 bi_c78_b0_c0 bi_c78_b0_c1
  have h36 := checkBiFarkasRangeNBool_append 84 _ _ _ _ _ 24 12 h24 bi_c78_b0_c2
  have h48 := checkBiFarkasRangeNBool_append 84 _ _ _ _ _ 36 12 h36 bi_c78_b0_c3
  have h60 := checkBiFarkasRangeNBool_append 84 _ _ _ _ _ 48 12 h48 bi_c78_b0_c4
  have h72 := checkBiFarkasRangeNBool_append 84 _ _ _ _ _ 60 12 h60 bi_c78_b0_c5
  exact checkBiFarkasRangeNBool_append 84 _ _ _ _ _ 72 12 h72 bi_c78_b0_c6

private theorem bi_c78_b1_c0 : checkBiFarkasRangeNBool 84 projSym84To42 farkasMu0CoupledC78 farkasMu1BiBTRC78 fin2Z1W17 c78FastRulesW17 0 12 = true := by decide
private theorem bi_c78_b1_c1 : checkBiFarkasRangeNBool 84 projSym84To42 farkasMu0CoupledC78 farkasMu1BiBTRC78 fin2Z1W17 c78FastRulesW17 12 12 = true := by decide
private theorem bi_c78_b1_c2 : checkBiFarkasRangeNBool 84 projSym84To42 farkasMu0CoupledC78 farkasMu1BiBTRC78 fin2Z1W17 c78FastRulesW17 24 12 = true := by decide
private theorem bi_c78_b1_c3 : checkBiFarkasRangeNBool 84 projSym84To42 farkasMu0CoupledC78 farkasMu1BiBTRC78 fin2Z1W17 c78FastRulesW17 36 12 = true := by decide
private theorem bi_c78_b1_c4 : checkBiFarkasRangeNBool 84 projSym84To42 farkasMu0CoupledC78 farkasMu1BiBTRC78 fin2Z1W17 c78FastRulesW17 48 12 = true := by decide
private theorem bi_c78_b1_c5 : checkBiFarkasRangeNBool 84 projSym84To42 farkasMu0CoupledC78 farkasMu1BiBTRC78 fin2Z1W17 c78FastRulesW17 60 12 = true := by decide
private theorem bi_c78_b1_c6 : checkBiFarkasRangeNBool 84 projSym84To42 farkasMu0CoupledC78 farkasMu1BiBTRC78 fin2Z1W17 c78FastRulesW17 72 12 = true := by decide

private theorem bi_c78_farkas_b1_cert :
    checkBiFarkasCoordNBool 84 projSym84To42 farkasMu0CoupledC78 farkasMu1BiBTRC78 fin2Z1W17 c78FastRulesW17 = true := by
  unfold checkBiFarkasCoordNBool
  have h24 := checkBiFarkasRangeNBool_append 84 _ _ _ _ _ 12 12 bi_c78_b1_c0 bi_c78_b1_c1
  have h36 := checkBiFarkasRangeNBool_append 84 _ _ _ _ _ 24 12 h24 bi_c78_b1_c2
  have h48 := checkBiFarkasRangeNBool_append 84 _ _ _ _ _ 36 12 h36 bi_c78_b1_c3
  have h60 := checkBiFarkasRangeNBool_append 84 _ _ _ _ _ 48 12 h48 bi_c78_b1_c4
  have h72 := checkBiFarkasRangeNBool_append 84 _ _ _ _ _ 60 12 h60 bi_c78_b1_c5
  exact checkBiFarkasRangeNBool_append 84 _ _ _ _ _ 72 12 h72 bi_c78_b1_c6

private def no69NonLastBoolW17 : List (Fin 42) -> Bool
  | [] => true
  | [_] => true
  | s :: s2 :: tl => decide (s.val ≠ 6 ∧ s.val ≠ 9) && no69NonLastBoolW17 (s2 :: tl)

private def endIs69BoolW17 : List (Fin 42) -> Bool
  | [] => false
  | [s] => s.val == 6 || s.val == 9
  | _ :: s2 :: tl => endIs69BoolW17 (s2 :: tl)

private def biWord6MonoShapeBoolW17 : List (Fin 42) -> Bool
  | [s1] => decide (s1.val ≠ 6 ∧ s1.val ≠ 9)
  | [s1, _] => decide (s1.val ≠ 6 ∧ s1.val ≠ 9)
  | [s1, s2, _] => decide (s1.val ≠ 6 ∧ s1.val ≠ 9 ∧ (s2.val = 13 ∨ s2.val = 16))
  | _ => false

private def biDecomp6CoeffsW17 (w : List (Fin 42)) (i j : Fin 2) :
    Nat × Nat × Nat × Nat × Nat × Nat :=
  let c0 := evalFinWordMat 42 2 (biBTRMat2DC39 1 0 0 0) w i j
  let ca := evalFinWordMat 42 2 (biBTRMat2DC39 1 1 0 0) w i j - c0
  let cb := evalFinWordMat 42 2 (biBTRMat2DC39 1 0 1 0) w i j - c0
  let cg := evalFinWordMat 42 2 (biBTRMat2DC39 1 0 0 1) w i j - c0
  let cab := evalFinWordMat 42 2 (biBTRMat2DC39 1 1 1 0) w i j - c0 - ca - cb
  let cag := evalFinWordMat 42 2 (biBTRMat2DC39 1 1 0 1) w i j - c0 - ca - cg
  (c0, ca, cb, cg, cab, cag)

private theorem weak_mat_orientation_4param_bi_cones_w17 (k alpha beta gamma : Nat) :
    (∀ r ∈ c39FastRulesW17, ∀ i j : Fin 2,
      evalFinWordMat 42 2 (biBTRMat2DC39 k alpha beta gamma) r.1 i j ≥
        evalFinWordMat 42 2 (biBTRMat2DC39 k alpha beta gamma) r.2 i j) ∧
    (∀ r ∈ c78FastRulesW17, ∀ i j : Fin 2,
      evalFinWordMat 84 2 (biBTRMat2DC78 k alpha beta gamma) r.1 i j ≥
        evalFinWordMat 84 2 (biBTRMat2DC78 k alpha beta gamma) r.2 i j) := by
  have hm_step : ∀ (fn : Fin 42 -> Fin 2 -> Fin 2 -> Nat) (s : Fin 42) (tl : List (Fin 42)) (i j : Fin 2),
      evalFinWordMat 42 2 fn (s :: tl) i j =
        fn s i fin2Z0W17 * evalFinWordMat 42 2 fn tl fin2Z0W17 j +
        fn s i fin2Z1W17 * evalFinWordMat 42 2 fn tl fin2Z1W17 j := by
    intro fn s tl i j
    change (0 + fn s i fin2Z0W17 * evalFinWordMat 42 2 fn tl fin2Z0W17 j) +
      fn s i fin2Z1W17 * evalFinWordMat 42 2 fn tl fin2Z1W17 j = _; omega
  have hm_single : ∀ (fn : Fin 42 -> Fin 2 -> Fin 2 -> Nat) (s : Fin 42) (i j : Fin 2),
      evalFinWordMat 42 2 fn [s] i j = fn s i j := by
    intro fn s i j
    rw [hm_step fn s [] i j]
    rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1) with hj0 | hj1
    · rw [show j = fin2Z0W17 from Fin.ext hj0]
      change fn s i fin2Z0W17 * 1 + fn s i fin2Z1W17 * 0 = fn s i fin2Z0W17; omega
    · rw [show j = fin2Z1W17 from Fin.ext hj1]
      change fn s i fin2Z0W17 * 0 + fn s i fin2Z1W17 * 1 = fn s i fin2Z1W17; omega
  -- Notice `(M_s)_{0,0} = 1` everywhere at `k = 1`, `(M_s)_{0,1}` depends ONLY on `a'`,
  -- `(M_s)_{1,0}` depends ONLY on `(b', g')`, and `(M_s)_{1,1}` is constant!
  -- Wrap the 4 base matrix entries in an auxiliary function `baseBiEntry` so `simp only` never loops!
  let baseBiEntry (mode : Nat) (s : Fin 42) : Nat :=
    match mode with
    | 0 => biBTRMat2DC39 1 1 0 0 s fin2Z0W17 fin2Z1W17
    | 1 => biBTRMat2DC39 1 0 1 0 s fin2Z1W17 fin2Z0W17
    | 2 => biBTRMat2DC39 1 0 0 1 s fin2Z1W17 fin2Z0W17
    | _ => biBTRMat2DC39 1 0 0 0 s fin2Z1W17 fin2Z1W17
  have hsym_sep : ∀ (s : Fin 42) (a' b' g' : Nat),
      biBTRMat2DC39 1 a' b' g' s fin2Z0W17 fin2Z0W17 = 1 ∧
      biBTRMat2DC39 1 a' b' g' s fin2Z0W17 fin2Z1W17 = a' * baseBiEntry 0 s ∧
      biBTRMat2DC39 1 a' b' g' s fin2Z1W17 fin2Z0W17 =
        b' * baseBiEntry 1 s + g' * baseBiEntry 2 s ∧
      biBTRMat2DC39 1 a' b' g' s fin2Z1W17 fin2Z1W17 = baseBiEntry 3 s := by
    intro s a' b' g'
    refine ⟨?_, ?_, ?_, rfl⟩
    · unfold biBTRMat2DC39; dsimp [fin2Z0W17]
      by_cases h : (s.val == 6 || s.val == 9) = true <;> simp [h]
    · change (match s.val with | 22 => a' | 23 => a' | 37 => a' | 40 => a' | 41 => a' | _ => 0) =
        a' * (match s.val with | 22 => 1 | 23 => 1 | 37 => 1 | 40 => 1 | 41 => 1 | _ => 0)
      split <;> omega
    · change (match s.val with
        | 14 => b' | 18 => b' | 20 => g' | 28 => b' | 31 => 2 * b'
        | 32 => b' + g' | 36 => g' | 37 => 2 * g' | 38 => g' | _ => 0) =
        b' * (match s.val with
          | 14 => 1 | 18 => 1 | 20 => 0 | 28 => 1 | 31 => 2 * 1
          | 32 => 1 + 0 | 36 => 0 | 37 => 2 * 0 | 38 => 0 | _ => 0) +
        g' * (match s.val with
          | 14 => 0 | 18 => 0 | 20 => 1 | 28 => 0 | 31 => 2 * 0
          | 32 => 0 + 1 | 36 => 1 | 37 => 2 * 1 | 38 => 1 | _ => 0)
      split <;> omega
  have hsym_lin : ∀ (s : Fin 42) (a' b' g' : Nat) (i j : Fin 2),
      biBTRMat2DC39 1 a' b' g' s i j =
        biBTRMat2DC39 1 0 0 0 s i j +
        a' * (biBTRMat2DC39 1 1 0 0 s i j - biBTRMat2DC39 1 0 0 0 s i j) +
        b' * (biBTRMat2DC39 1 0 1 0 s i j - biBTRMat2DC39 1 0 0 0 s i j) +
        g' * (biBTRMat2DC39 1 0 0 1 s i j - biBTRMat2DC39 1 0 0 0 s i j) := by
    intro s a' b' g' i j
    rcases (by have := i.isLt; omega : i.val = 0 ∨ i.val = 1) with hi | hi <;>
    rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1) with hj | hj
    · rw [show i = fin2Z0W17 from Fin.ext hi, show j = fin2Z0W17 from Fin.ext hj]
      simp only [(hsym_sep s _ _ _).1]; omega
    · rw [show i = fin2Z0W17 from Fin.ext hi, show j = fin2Z1W17 from Fin.ext hj]
      simp only [(hsym_sep s _ _ _).2.1, Nat.zero_mul, Nat.one_mul, Nat.sub_zero]; omega
    · rw [show i = fin2Z1W17 from Fin.ext hi, show j = fin2Z0W17 from Fin.ext hj]
      simp only [(hsym_sep s _ _ _).2.2.1, Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add, Nat.sub_zero]; omega
    · rw [show i = fin2Z1W17 from Fin.ext hi, show j = fin2Z1W17 from Fin.ext hj]
      simp only [(hsym_sep s _ _ _).2.2.2, Nat.sub_self, Nat.mul_zero]; omega
  have hword_6mono : ∀ (w : List (Fin 42)), biWord6MonoShapeBoolW17 w = true ->
      ∀ i j : Fin 2,
        let c := biDecomp6CoeffsW17 w i j
        evalFinWordMat 42 2 (biBTRMat2DC39 1 alpha beta gamma) w i j =
          c.1 + alpha * c.2.1 + beta * c.2.2.1 + gamma * c.2.2.2.1 +
          (alpha * beta) * c.2.2.2.2.1 + (alpha * gamma) * c.2.2.2.2.2 := by
    intro w hsh i j; dsimp only
    cases w with
    | nil => cases hsh
    | cons s1 xs =>
      cases xs with
      | nil =>
        unfold biDecomp6CoeffsW17
        simp only [hm_single]
        rw [hsym_lin s1 alpha beta gamma i j,
            hsym_lin s1 1 1 0 i j, hsym_lin s1 1 0 1 i j]
        generalize biBTRMat2DC39 1 0 0 0 s1 i j = c0,
          biBTRMat2DC39 1 1 0 0 s1 i j = e100,
          biBTRMat2DC39 1 0 1 0 s1 i j = e010,
          biBTRMat2DC39 1 0 0 1 s1 i j = e001
        have h1 : (c0 + 1 * (e100 - c0) + 1 * (e010 - c0) + 0 * (e001 - c0)) - c0 - (e100 - c0) - (e010 - c0) = 0 := by omega
        have h2 : (c0 + 1 * (e100 - c0) + 0 * (e010 - c0) + 1 * (e001 - c0)) - c0 - (e100 - c0) - (e001 - c0) = 0 := by omega
        rw [h1, h2, Nat.mul_zero, Nat.mul_zero]; omega
      | cons s2 xs2 =>
        cases xs2 with
        | nil =>
          -- `[s1, s2]` with `s1 ∉ {6, 9}` (so `(M_{s1})_{1,1} = 0`!):
          unfold biWord6MonoShapeBoolW17 at hsh
          rcases of_decide_eq_true hsh with ⟨hn6, _⟩
          have hs1_11 : ∀ a' b' g' : Nat, biBTRMat2DC39 1 a' b' g' s1 fin2Z1W17 fin2Z1W17 = 0 := by
            intro a' b' g'; unfold biBTRMat2DC39; dsimp [fin2Z1W17]; simp [beq_false_of_ne hn6]
          have hexp2 : ∀ a' b' g' : Nat,
              evalFinWordMat 42 2 (biBTRMat2DC39 1 a' b' g') [s1, s2] i j =
                biBTRMat2DC39 1 a' b' g' s1 i fin2Z0W17 * biBTRMat2DC39 1 a' b' g' s2 fin2Z0W17 j +
                biBTRMat2DC39 1 a' b' g' s1 i fin2Z1W17 * biBTRMat2DC39 1 a' b' g' s2 fin2Z1W17 j := by
            intro a' b' g'; rw [hm_step, hm_single, hm_single]
          unfold biDecomp6CoeffsW17; dsimp only
          simp only [hexp2]
          rcases (by have := i.isLt; omega : i.val = 0 ∨ i.val = 1) with hi | hi <;>
          rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1) with hj | hj
          · have ei : i = fin2Z0W17 := Fin.ext hi; have ej : j = fin2Z0W17 := Fin.ext hj
            rw [ei, ej]
            simp only [(hsym_sep s1 _ _ _).1, (hsym_sep s2 _ _ _).1,
                       (hsym_sep s1 _ _ _).2.1, (hsym_sep s2 _ _ _).2.2.1,
                       Nat.one_mul, Nat.mul_one, Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
            generalize baseBiEntry 0 s1 = A1, baseBiEntry 1 s2 = B2, baseBiEntry 2 s2 = G2
            rw [Nat.mul_add (alpha * A1),
                show (alpha * A1) * (beta * B2) = (alpha * beta) * (A1 * B2) by ac_rfl,
                show (alpha * A1) * (gamma * G2) = (alpha * gamma) * (A1 * G2) by ac_rfl]
            generalize alpha * beta = AB, alpha * gamma = AG
            simp [Nat.add_sub_cancel_left]
            omega
          · have ei : i = fin2Z0W17 := Fin.ext hi; have ej : j = fin2Z1W17 := Fin.ext hj
            rw [ei, ej]
            simp only [(hsym_sep s1 _ _ _).1, (hsym_sep s1 _ _ _).2.1,
                       (hsym_sep s2 _ _ _).2.1, (hsym_sep s2 _ _ _).2.2.2,
                       Nat.one_mul, Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
            generalize baseBiEntry 0 s2 = A2, baseBiEntry 0 s1 = A1, baseBiEntry 3 s2 = D2
            rw [Nat.mul_assoc alpha A1 D2, ← Nat.mul_add alpha A2 (A1 * D2)]
            generalize A2 + A1 * D2 = AT, alpha * beta = AB, alpha * gamma = AG
            simp
          · have ei : i = fin2Z1W17 := Fin.ext hi; have ej : j = fin2Z0W17 := Fin.ext hj
            rw [ei, ej]
            simp only [hs1_11, (hsym_sep s2 _ _ _).1, (hsym_sep s1 _ _ _).2.2.1,
                       Nat.zero_mul, Nat.mul_one, Nat.one_mul, Nat.add_zero, Nat.zero_add]
            generalize baseBiEntry 1 s1 = B1, baseBiEntry 2 s1 = G1,
              alpha * beta = AB, alpha * gamma = AG
            simp only [Nat.sub_zero, Nat.sub_self, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
          · have ei : i = fin2Z1W17 := Fin.ext hi; have ej : j = fin2Z1W17 := Fin.ext hj
            rw [ei, ej]
            simp only [hs1_11, (hsym_sep s1 _ _ _).2.2.1, (hsym_sep s2 _ _ _).2.1,
                       Nat.zero_mul, Nat.mul_zero, Nat.one_mul, Nat.add_zero, Nat.zero_add]
            generalize baseBiEntry 1 s1 = B1, baseBiEntry 2 s1 = G1, baseBiEntry 0 s2 = A2
            rw [Nat.add_mul (beta * B1) (gamma * G1) (alpha * A2),
                show (beta * B1) * (alpha * A2) = (alpha * beta) * (B1 * A2) by ac_rfl,
                show (gamma * G1) * (alpha * A2) = (alpha * gamma) * (G1 * A2) by ac_rfl]
            generalize alpha * beta = AB, alpha * gamma = AG
            simp only [Nat.sub_zero, Nat.sub_self, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
        | cons s3 xs3 =>
          cases xs3 with
          | nil =>
            -- `[s1, s2, s3]` with `s1 ∉ {6, 9}` and `s2 ∈ {13, 16}` (`M_{s2} = [[1, 0], [0, 0]]`!):
            unfold biWord6MonoShapeBoolW17 at hsh
            rcases of_decide_eq_true hsh with ⟨hn6, _, h1316⟩
            have hs1_11 : ∀ a' b' g' : Nat, biBTRMat2DC39 1 a' b' g' s1 fin2Z1W17 fin2Z1W17 = 0 := by
              intro a' b' g'; unfold biBTRMat2DC39; dsimp [fin2Z1W17]; simp [beq_false_of_ne hn6]
            have hs23 : ∀ a' b' g' : Nat,
                evalFinWordMat 42 2 (biBTRMat2DC39 1 a' b' g') [s2, s3] fin2Z0W17 j =
                  biBTRMat2DC39 1 a' b' g' s3 fin2Z0W17 j ∧
                evalFinWordMat 42 2 (biBTRMat2DC39 1 a' b' g') [s2, s3] fin2Z1W17 j = 0 := by
              intro a' b' g'
              have hm00 : biBTRMat2DC39 1 a' b' g' s2 fin2Z0W17 fin2Z0W17 = 1 := by
                rcases h1316 with h | h <;> simp [biBTRMat2DC39, h]
              have hm01 : biBTRMat2DC39 1 a' b' g' s2 fin2Z0W17 fin2Z1W17 = 0 := by
                rcases h1316 with h | h <;> simp [biBTRMat2DC39, h]
              have hm10 : biBTRMat2DC39 1 a' b' g' s2 fin2Z1W17 fin2Z0W17 = 0 := by
                rcases h1316 with h | h <;> simp [biBTRMat2DC39, h]
              have hm11 : biBTRMat2DC39 1 a' b' g' s2 fin2Z1W17 fin2Z1W17 = 0 := by
                rcases h1316 with h | h <;> simp [biBTRMat2DC39, h]
              refine ⟨?_, ?_⟩
              · rw [hm_step, hm00, hm01, hm_single, Nat.one_mul, Nat.zero_mul, Nat.add_zero]
              · rw [hm_step, hm10, hm11, Nat.zero_mul, Nat.zero_mul]
            have hexp3 : ∀ a' b' g' : Nat,
                evalFinWordMat 42 2 (biBTRMat2DC39 1 a' b' g') [s1, s2, s3] i j =
                  biBTRMat2DC39 1 a' b' g' s1 i fin2Z0W17 * biBTRMat2DC39 1 a' b' g' s3 fin2Z0W17 j := by
              intro a' b' g'
              rw [hm_step _ s1 [s2, s3] i j, (hs23 a' b' g').1, (hs23 a' b' g').2,
                  Nat.mul_zero, Nat.add_zero]
            unfold biDecomp6CoeffsW17; dsimp only
            simp only [hexp3]
            rcases (by have := i.isLt; omega : i.val = 0 ∨ i.val = 1) with hi | hi <;>
            rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1) with hj | hj
            · have ei : i = fin2Z0W17 := Fin.ext hi; have ej : j = fin2Z0W17 := Fin.ext hj
              rw [ei, ej]
              simp only [(hsym_sep s1 _ _ _).1, (hsym_sep s3 _ _ _).1]
              omega
            · have ei : i = fin2Z0W17 := Fin.ext hi; have ej : j = fin2Z1W17 := Fin.ext hj
              rw [ei, ej]
              simp only [(hsym_sep s1 _ _ _).1, (hsym_sep s3 _ _ _).2.1,
                         Nat.one_mul, Nat.zero_mul, Nat.mul_zero]
              generalize baseBiEntry 0 s3 = A3, alpha * beta = AB, alpha * gamma = AG
              simp only [Nat.sub_zero, Nat.sub_self, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
            · have ei : i = fin2Z1W17 := Fin.ext hi; have ej : j = fin2Z0W17 := Fin.ext hj
              rw [ei, ej]
              simp only [(hsym_sep s1 _ _ _).2.2.1, (hsym_sep s3 _ _ _).1,
                         Nat.mul_one, Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add]
              generalize baseBiEntry 1 s1 = B1, baseBiEntry 2 s1 = G1,
                alpha * beta = AB, alpha * gamma = AG
              simp only [Nat.sub_zero, Nat.sub_self, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
            · have ei : i = fin2Z1W17 := Fin.ext hi; have ej : j = fin2Z1W17 := Fin.ext hj
              rw [ei, ej]
              simp only [(hsym_sep s1 _ _ _).2.2.1, (hsym_sep s3 _ _ _).2.1,
                         Nat.zero_mul, Nat.mul_zero, Nat.one_mul, Nat.add_zero, Nat.zero_add]
              generalize baseBiEntry 1 s1 = B1, baseBiEntry 2 s1 = G1, baseBiEntry 0 s3 = A3
              rw [Nat.add_mul (beta * B1) (gamma * G1) (alpha * A3),
                  show (beta * B1) * (alpha * A3) = (alpha * beta) * (B1 * A3) by ac_rfl,
                  show (gamma * G1) * (alpha * A3) = (alpha * gamma) * (G1 * A3) by ac_rfl]
              generalize alpha * beta = AB, alpha * gamma = AG
              simp only [Nat.sub_zero, Nat.sub_self, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
          | cons _ _ => cases hsh
  have hbi_corners :
      c39FastRulesW17.all (fun r =>
        biWord6MonoShapeBoolW17 r.1 && biWord6MonoShapeBoolW17 r.2 &&
        decide (r.1 ≠ [] ∧ r.2 ≠ []) &&
        no69NonLastBoolW17 r.1 && no69NonLastBoolW17 r.2 &&
        decide (endIs69BoolW17 r.1 = endIs69BoolW17 r.2) &&
        [fin2Z0W17, fin2Z1W17].all (fun i =>
          [fin2Z0W17, fin2Z1W17].all (fun j =>
            let cl := biDecomp6CoeffsW17 r.1 i j
            let cr := biDecomp6CoeffsW17 r.2 i j
            decide (cr.1 ≤ cl.1 ∧ cr.2.1 ≤ cl.2.1 ∧ cr.2.2.1 ≤ cl.2.2.1 ∧
                    cr.2.2.2.1 ≤ cl.2.2.2.1 ∧ cr.2.2.2.2.1 ≤ cl.2.2.2.2.1 ∧
                    cr.2.2.2.2.2 ≤ cl.2.2.2.2.2)))) = true := by decide
  have hk_scale : ∀ (w : List (Fin 42)), w ≠ [] -> no69NonLastBoolW17 w = true ->
      ∀ i j : Fin 2,
        evalFinWordMat 42 2 (biBTRMat2DC39 k alpha beta gamma) w i j =
          evalFinWordMat 42 2 (biBTRMat2DC39 1 alpha beta gamma) w i j *
            (if endIs69BoolW17 w && (j.val == 0) then k else 1) := by
    intro w; induction w with
    | nil => intro hne; exact False.elim (hne rfl)
    | cons s xs ih =>
      cases xs with
      | nil =>
        intros _ _ i j
        rw [hm_single, hm_single]
        unfold endIs69BoolW17
        by_cases hs69 : (s.val == 6 || s.val == 9) = true
        · have hs_v : s.val = 6 ∨ s.val = 9 := by
            rcases Bool.or_eq_true_iff.mp hs69 with h6 | h9
            · exact Or.inl (Nat.eq_of_beq_eq_true h6)
            · exact Or.inr (Nat.eq_of_beq_eq_true h9)
          rcases (by have := i.isLt; omega : i.val = 0 ∨ i.val = 1) with hi | hi <;>
          rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1) with hj | hj <;>
          (rcases hs_v with hs | hs <;> simp [biBTRMat2DC39, hi, hj, hs])
        · have hn6 : s.val ≠ 6 := fun h => hs69 (by simp [h])
          have hn9 : s.val ≠ 9 := fun h => hs69 (by simp [h])
          have hout : biBTRMat2DC39 k alpha beta gamma s i j = biBTRMat2DC39 1 alpha beta gamma s i j := by
            unfold biBTRMat2DC39
            rcases (by have := i.isLt; omega : i.val = 0 ∨ i.val = 1) with hi | hi <;>
            rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1) with hj | hj <;>
            simp only [hi, hj, beq_false_of_ne hn6, beq_false_of_ne hn9]; all_goals rfl
          simp [hs69, hout]
      | cons s2 tl =>
        intro _ hnl i j
        unfold no69NonLastBoolW17 at hnl
        rcases bool_and_split hnl with ⟨hs_b, htl_nl⟩
        rcases of_decide_eq_true hs_b with ⟨hn6, hn9⟩
        have hout : ∀ p q : Fin 2,
            biBTRMat2DC39 k alpha beta gamma s p q = biBTRMat2DC39 1 alpha beta gamma s p q := by
          intro p q; unfold biBTRMat2DC39
          rcases (by have := p.isLt; omega : p.val = 0 ∨ p.val = 1) with hp | hp <;>
          rcases (by have := q.isLt; omega : q.val = 0 ∨ q.val = 1) with hq | hq <;>
          simp only [hp, hq, beq_false_of_ne hn6, beq_false_of_ne hn9]; all_goals rfl
        have he_end : endIs69BoolW17 (s :: s2 :: tl) = endIs69BoolW17 (s2 :: tl) := rfl
        rw [he_end, hm_step (biBTRMat2DC39 k alpha beta gamma) s (s2 :: tl) i j,
            hm_step (biBTRMat2DC39 1 alpha beta gamma) s (s2 :: tl) i j,
            hout i fin2Z0W17, hout i fin2Z1W17,
            ih (by simp) htl_nl fin2Z0W17 j, ih (by simp) htl_nl fin2Z1W17 j,
            Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc]
  have hw39 : ∀ r ∈ c39FastRulesW17, ∀ i j : Fin 2,
      evalFinWordMat 42 2 (biBTRMat2DC39 k alpha beta gamma) r.1 i j ≥
        evalFinWordMat 42 2 (biBTRMat2DC39 k alpha beta gamma) r.2 i j := by
    intro r hr i j
    rcases bool_and_split (List.all_eq_true.mp hbi_corners r hr) with ⟨hb1, hall_ij⟩
    rcases bool_and_split hb1 with ⟨hb2, hend_b⟩
    rcases bool_and_split hb2 with ⟨hb3, hnl2⟩
    rcases bool_and_split hb3 with ⟨hb4, hnl1⟩
    rcases bool_and_split hb4 with ⟨hsh12, hne_b⟩
    rcases bool_and_split hsh12 with ⟨hsh1, hsh2⟩
    rcases of_decide_eq_true hne_b with ⟨hne1, hne2⟩
    have hend := of_decide_eq_true hend_b
    rw [hk_scale r.1 hne1 hnl1 i j, hk_scale r.2 hne2 hnl2 i j, hend]
    apply Nat.mul_le_mul_right
    have hi_m : i ∈ [fin2Z0W17, fin2Z1W17] := by
      rcases (by have := i.isLt; omega : i.val = 0 ∨ i.val = 1) with h | h
      · rw [show i = fin2Z0W17 from Fin.ext h]; exact List.Mem.head _
      · rw [show i = fin2Z1W17 from Fin.ext h]; exact List.Mem.tail _ (List.Mem.head _)
    have hj_m : j ∈ [fin2Z0W17, fin2Z1W17] := by
      rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1) with h | h
      · rw [show j = fin2Z0W17 from Fin.ext h]; exact List.Mem.head _
      · rw [show j = fin2Z1W17 from Fin.ext h]; exact List.Mem.tail _ (List.Mem.head _)
    rcases of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hall_ij i hi_m) j hj_m) with
      ⟨hc0, hca, hcb, hcg, hcab, hcag⟩
    have hl := hword_6mono r.1 hsh1 i j
    have hr_e := hword_6mono r.2 hsh2 i j
    dsimp only at hl hr_e
    rw [hl, hr_e]
    exact Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add (Nat.add_le_add hc0 (Nat.mul_le_mul_left _ hca)) (Nat.mul_le_mul_left _ hcb))
          (Nat.mul_le_mul_left _ hcg))
        (Nat.mul_le_mul_left _ hcab))
      (Nat.mul_le_mul_left _ hcag)
  have hproj84 : ∀ (w : List (Fin 84)) (i j : Fin 2),
      evalFinWordMat 84 2 (biBTRMat2DC78 k alpha beta gamma) w i j =
        evalFinWordMat 42 2 (biBTRMat2DC39 k alpha beta gamma) (w.map projSym84To42) i j := by
    intro w; induction w with
    | nil => intros; rfl
    | cons s tl ih =>
      intro i j
      have hm84 : evalFinWordMat 84 2 (biBTRMat2DC78 k alpha beta gamma) (s :: tl) i j =
          biBTRMat2DC78 k alpha beta gamma s i fin2Z0W17 *
            evalFinWordMat 84 2 (biBTRMat2DC78 k alpha beta gamma) tl fin2Z0W17 j +
          biBTRMat2DC78 k alpha beta gamma s i fin2Z1W17 *
            evalFinWordMat 84 2 (biBTRMat2DC78 k alpha beta gamma) tl fin2Z1W17 j := by
        change (0 + biBTRMat2DC78 k alpha beta gamma s i fin2Z0W17 *
          evalFinWordMat 84 2 (biBTRMat2DC78 k alpha beta gamma) tl fin2Z0W17 j) +
          biBTRMat2DC78 k alpha beta gamma s i fin2Z1W17 *
            evalFinWordMat 84 2 (biBTRMat2DC78 k alpha beta gamma) tl fin2Z1W17 j = _; omega
      simp only [List.map_cons]
      rw [hm84, hm_step _ (projSym84To42 s) (tl.map projSym84To42) i j,
          ih fin2Z0W17 j, ih fin2Z1W17 j]
      rfl
  refine ⟨hw39, ?_⟩
  have hc78_proj := bi_c39_c78_shape_and_witness_certs.2.2.1
  intro r hr i j
  rw [hproj84 r.1 i j, hproj84 r.2 i j]
  rcases List.any_eq_true.mp (List.all_eq_true.mp hc78_proj r hr) with ⟨r39, hr39, hbeq⟩
  have heq_p := beq_iff_eq.mp hbeq
  rcases r39 with ⟨l39, r39_r⟩
  rcases Prod.mk.injEq _ _ _ _ ▸ heq_p with ⟨hl_eq, hr_eq⟩
  rw [← hl_eq, ← hr_eq]
  exact hw39 (l39, r39_r) hr39 i j

private theorem bi_farkas_zero_strict_proj_w17
    (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 : List (Fin N) -> Nat)
    (rs : List (List (Fin N) × List (Fin N)))
    (hshape_b : checkWordShapeBiNBool N proj mu0 mu1 rs = true)
    (hfark_b0 : checkBiFarkasCoordNBool N proj mu0 mu1 fin2Z0W17 rs = true)
    (hfark_b1 : checkBiFarkasCoordNBool N proj mu0 mu1 fin2Z1W17 rs = true)
    (k alpha beta gamma : Nat) (v : Fin N -> Fin 2 -> Nat)
    (hv_weak : ∀ r ∈ rs, ∀ i : Fin 2,
      evalFinWordVec N 2 (fun s => biBTRMat2DC39 k alpha beta gamma (proj s)) v r.1 i ≥
        evalFinWordVec N 2 (fun s => biBTRMat2DC39 k alpha beta gamma (proj s)) v r.2 i) :
    ∀ r ∈ rs,
      evalFinWordVec N 2 (fun s => biBTRMat2DC39 k alpha beta gamma (proj s)) v r.1 fin2Z0W17 =
        evalFinWordVec N 2 (fun s => biBTRMat2DC39 k alpha beta gamma (proj s)) v r.2 fin2Z0W17 := by
  let matFn := fun k' a' b' g' (s : Fin N) => biBTRMat2DC39 k' a' b' g' (proj s)
  have hfark_aff : ∀ (v0 : Fin N -> Fin 2 -> Nat)
      (xs : List (List (Fin N) × List (Fin N))),
      checkWordShapeBiNBool N proj mu0 mu1 xs = true ->
      farkasBiVecLhsN N proj mu0 mu1 1 0 0 0 v0 xs ≤
        farkasBiVecLhsN N proj mu0 mu1 1 1 0 0 v0 xs ∧
      farkasBiVecRhsN N proj mu0 mu1 1 0 0 0 v0 xs ≤
        farkasBiVecRhsN N proj mu0 mu1 1 1 0 0 v0 xs ∧
      farkasBiVecLhsN N proj mu0 mu1 k alpha beta gamma v0 xs =
        farkasBiVecLhsN N proj mu0 mu1 1 0 0 0 v0 xs +
          alpha * (farkasBiVecLhsN N proj mu0 mu1 1 1 0 0 v0 xs -
            farkasBiVecLhsN N proj mu0 mu1 1 0 0 0 v0 xs) ∧
      farkasBiVecRhsN N proj mu0 mu1 k alpha beta gamma v0 xs =
        farkasBiVecRhsN N proj mu0 mu1 1 0 0 0 v0 xs +
          alpha * (farkasBiVecRhsN N proj mu0 mu1 1 1 0 0 v0 xs -
            farkasBiVecRhsN N proj mu0 mu1 1 0 0 0 v0 xs) := by
    intro v0 xs; induction xs with
    | nil => intros; simp [farkasBiVecLhsN, farkasBiVecRhsN]
    | cons r0 rtl ih =>
      rcases r0 with ⟨l0, r0_w⟩
      intro hbw
      unfold checkWordShapeBiNBool at hbw
      simp only [List.all_cons] at hbw
      rcases bool_and_split hbw with ⟨h0_b, htl_b⟩
      rcases ih htl_b with ⟨hle_tl1, hle_tl2, htl1, htl2⟩
      rcases bool_and_split h0_b with ⟨hb_a, _⟩
      rcases bool_and_split hb_a with ⟨hb_b, hmu1_disj⟩
      rcases bool_and_split hb_b with ⟨hl_nb, hr_nb⟩
      rcases (biBTRMatProj_vec_linearity_w17 N proj k alpha beta gamma v0).2 l0 hl_nb with ⟨hle_l0, hl0_ab⟩
      rcases (biBTRMatProj_vec_linearity_w17 N proj k alpha beta gamma v0).2 r0_w hr_nb with ⟨hle_r0, hr0_ab⟩
      have hm1_term :
          (alpha * mu1 l0) * evalFinWordVec N 2 (matFn k alpha beta gamma) v0 l0 fin2Z1W17 =
            alpha * (mu1 l0 * evalFinWordVec N 2 (matFn 1 1 0 0) v0 l0 fin2Z1W17) ∧
          (alpha * mu1 l0) * evalFinWordVec N 2 (matFn k alpha beta gamma) v0 r0_w fin2Z1W17 =
            alpha * (mu1 l0 * evalFinWordVec N 2 (matFn 1 1 0 0) v0 r0_w fin2Z1W17) := by
        rcases Bool.or_eq_true_iff.mp hmu1_disj with hm0_b | hnb_12
        · rw [of_decide_eq_true hm0_b]; simp
        · rcases bool_and_split hnb_12 with ⟨hnl1, hnl2⟩
          have e1 := (biBTRMatProj_vec_linearity_w17 N proj k alpha beta gamma v0).1 l0 hnl1
          have e1' := (biBTRMatProj_vec_linearity_w17 N proj 1 1 0 0 v0).1 l0 hnl1
          have e2 := (biBTRMatProj_vec_linearity_w17 N proj k alpha beta gamma v0).1 r0_w hnl2
          have e2' := (biBTRMatProj_vec_linearity_w17 N proj 1 1 0 0 v0).1 r0_w hnl2
          dsimp only [matFn] at e1 e1' e2 e2' ⊢
          rw [e1, ← e1', e2, ← e2', Nat.mul_assoc, Nat.mul_assoc]
          exact ⟨rfl, rfl⟩
      simp only [farkasBiVecLhsN, farkasBiVecRhsN, Nat.zero_mul, Nat.one_mul, Nat.add_zero]
      dsimp only [matFn] at hl0_ab hr0_ab hm1_term hle_l0 hle_r0
      rw [hl0_ab, hr0_ab, hm1_term.1, hm1_term.2, htl1, htl2]
      have hm_l0 := Nat.mul_le_mul_left (mu0 l0) hle_l0
      have hm_r0 := Nat.mul_le_mul_left (mu0 l0) hle_r0
      refine ⟨by omega, by omega, ?_, ?_⟩
      · have hs1 :
            (mu0 l0 * evalFinWordVec N 2 (matFn 1 1 0 0) v0 l0 fin2Z0W17 +
             mu1 l0 * evalFinWordVec N 2 (matFn 1 1 0 0) v0 l0 fin2Z1W17 +
             farkasBiVecLhsN N proj mu0 mu1 1 1 0 0 v0 rtl) -
            (mu0 l0 * evalFinWordVec N 2 (matFn 1 0 0 0) v0 l0 fin2Z0W17 +
             farkasBiVecLhsN N proj mu0 mu1 1 0 0 0 v0 rtl) =
            mu0 l0 *
              (evalFinWordVec N 2 (matFn 1 1 0 0) v0 l0 fin2Z0W17 -
               evalFinWordVec N 2 (matFn 1 0 0 0) v0 l0 fin2Z0W17) +
            mu1 l0 * evalFinWordVec N 2 (matFn 1 1 0 0) v0 l0 fin2Z1W17 +
            (farkasBiVecLhsN N proj mu0 mu1 1 1 0 0 v0 rtl -
             farkasBiVecLhsN N proj mu0 mu1 1 0 0 0 v0 rtl) := by
          dsimp only [matFn] at hm_l0 ⊢
          rw [Nat.mul_sub_left_distrib]; omega
        dsimp only [matFn] at hs1 ⊢
        rw [hs1, Nat.mul_add (mu0 l0), Nat.mul_add alpha, Nat.mul_add alpha,
            ← Nat.mul_assoc alpha (mu0 l0), Nat.mul_comm alpha (mu0 l0),
            Nat.mul_assoc (mu0 l0) alpha]
        omega
      · have hs2 :
            (mu0 l0 * evalFinWordVec N 2 (matFn 1 1 0 0) v0 r0_w fin2Z0W17 +
             mu1 l0 * evalFinWordVec N 2 (matFn 1 1 0 0) v0 r0_w fin2Z1W17 +
             farkasBiVecRhsN N proj mu0 mu1 1 1 0 0 v0 rtl) -
            (mu0 l0 * evalFinWordVec N 2 (matFn 1 0 0 0) v0 r0_w fin2Z0W17 +
             farkasBiVecRhsN N proj mu0 mu1 1 0 0 0 v0 rtl) =
            mu0 l0 *
              (evalFinWordVec N 2 (matFn 1 1 0 0) v0 r0_w fin2Z0W17 -
               evalFinWordVec N 2 (matFn 1 0 0 0) v0 r0_w fin2Z0W17) +
            mu1 l0 * evalFinWordVec N 2 (matFn 1 1 0 0) v0 r0_w fin2Z1W17 +
            (farkasBiVecRhsN N proj mu0 mu1 1 1 0 0 v0 rtl -
             farkasBiVecRhsN N proj mu0 mu1 1 0 0 0 v0 rtl) := by
          dsimp only [matFn] at hm_r0 ⊢
          rw [Nat.mul_sub_left_distrib]; omega
        dsimp only [matFn] at hs2 ⊢
        rw [hs2, Nat.mul_add (mu0 l0), Nat.mul_add alpha, Nat.mul_add alpha,
            ← Nat.mul_assoc alpha (mu0 l0), Nat.mul_comm alpha (mu0 l0),
            Nat.mul_assoc (mu0 l0) alpha]
        omega
  have hcoord_kabg : ∀ (j0 : Fin 2),
      checkBiFarkasCoordNBool N proj mu0 mu1 j0 rs = true ->
      ∀ s0 : Fin N,
        farkasBiVecLhsN N proj mu0 mu1 k alpha beta gamma (basisVec2D N s0 j0) rs ≤
          farkasBiVecRhsN N proj mu0 mu1 k alpha beta gamma (basisVec2D N s0 j0) rs := by
    intro j0 hchk
    unfold checkBiFarkasCoordNBool at hchk
    have hlp : ∀ n : Nat, n ≤ N ->
        checkBiFarkasRangeNBool N proj mu0 mu1 j0 rs 0 n = true ->
        ∀ m : Nat, m < n -> (hm : m < N) ->
          farkasBiVecLhsN N proj mu0 mu1 k alpha beta gamma (basisVec2D N ⟨m, hm⟩ j0) rs ≤
            farkasBiVecRhsN N proj mu0 mu1 k alpha beta gamma (basisVec2D N ⟨m, hm⟩ j0) rs := by
      intro n; induction n with
      | zero => intros _ _ _ hlt; omega
      | succ n' ih =>
        intro hn_le hn m hmn hmN
        have hnN : 0 + n' < N := by omega
        unfold checkBiFarkasRangeNBool at hn
        simp only [hnN, dite_true] at hn
        rcases bool_and_split hn with ⟨hc, hprev⟩
        by_cases hmeq : m = n'
        · subst hmeq
          have hfin : (⟨0 + m, hnN⟩ : Fin N) = ⟨m, hmN⟩ := Fin.ext (Nat.zero_add m)
          rw [hfin] at hc
          rcases hfark_aff (basisVec2D N ⟨m, hmN⟩ j0) rs hshape_b with ⟨_, _, ha1, ha2⟩
          rw [farkasBiFastPairN_eq N proj mu0 mu1 1 0 0 0,
              farkasBiFastPairN_eq N proj mu0 mu1 1 1 0 0] at hc
          dsimp only at hc
          rw [ha1, ha2]
          rcases of_decide_eq_true hc with ⟨hb0_le, hsl⟩
          have hm_sl := Nat.mul_le_mul_left alpha hsl
          omega
        · exact ih (Nat.le_of_lt hn_le) hprev m (by omega) hmN
    intro s0; exact hlp N (Nat.le_refl N) hchk s0.val s0.isLt s0.isLt
  have hbasis_kabg : ∀ s0 : Fin N,
      farkasBiVecLhsN N proj mu0 mu1 k alpha beta gamma (basisVec2D N s0 fin2Z0W17) rs ≤
        farkasBiVecRhsN N proj mu0 mu1 k alpha beta gamma (basisVec2D N s0 fin2Z0W17) rs ∧
      farkasBiVecLhsN N proj mu0 mu1 k alpha beta gamma (basisVec2D N s0 fin2Z1W17) rs ≤
        farkasBiVecRhsN N proj mu0 mu1 k alpha beta gamma (basisVec2D N s0 fin2Z1W17) rs :=
    fun s0 => ⟨hcoord_kabg fin2Z0W17 hfark_b0 s0, hcoord_kabg fin2Z1W17 hfark_b1 s0⟩
  let M := matFn k alpha beta gamma
  have hsum_add : ∀ (f g : Fin N -> Nat) (m : Nat),
      natSumPrefix N (fun s => f s + g s) m = natSumPrefix N f m + natSumPrefix N g m := by
    intro f g m; induction m with
    | zero => rfl
    | succ m' ih => simp only [natSumPrefix]; by_cases hm : m' < N <;> simp [hm, ih]; omega
  have hsum_mul : ∀ (c : Nat) (f : Fin N -> Nat) (m : Nat),
      c * natSumPrefix N f m = natSumPrefix N (fun s => c * f s) m := by
    intro c f m; induction m with
    | zero => simp [natSumPrefix]
    | succ m' ih => simp only [natSumPrefix]; by_cases hm : m' < N <;> simp [hm, Nat.mul_add, ih]
  have hcongr : ∀ (f g : Fin N -> Nat), (∀ s0 : Fin N, f s0 = g s0) ->
      ∀ m : Nat, natSumPrefix N f m = natSumPrefix N g m := by
    intro f g hfg m; induction m with
    | zero => rfl
    | succ m' ihm => simp only [natSumPrefix]; by_cases hm : m' < N <;> simp [hm, ihm, hfg]
  have hv_lin : ∀ (w : List (Fin N)) (i : Fin 2),
      evalFinWordVec N 2 M v w i =
        natSumPrefix N (fun s0 =>
          v s0 fin2Z0W17 * evalFinWordVec N 2 M (basisVec2D N s0 fin2Z0W17) w i +
          v s0 fin2Z1W17 * evalFinWordVec N 2 M (basisVec2D N s0 fin2Z1W17) w i) N := by
    have hdelta : ∀ (s : Fin N) (j : Fin 2),
        v s j = natSumPrefix N (fun s0 =>
          v s0 fin2Z0W17 * basisVec2D N s0 fin2Z0W17 s j +
          v s0 fin2Z1W17 * basisVec2D N s0 fin2Z1W17 s j) N := by
      intro s j
      have hst : ∀ m : Nat, m ≤ N ->
          natSumPrefix N (fun s0 =>
            v s0 fin2Z0W17 * basisVec2D N s0 fin2Z0W17 s j +
            v s0 fin2Z1W17 * basisVec2D N s0 fin2Z1W17 s j) m =
            if s.val < m then v s j else 0 := by
        intro m hm; induction m with
        | zero => simp [natSumPrefix]
        | succ m' ih =>
          have hm_lt : m' < N := hm
          simp only [natSumPrefix, hm_lt, dite_true, ih (Nat.le_of_lt hm)]
          by_cases heq : s.val = m'
          · have hsf : (⟨m', hm_lt⟩ : Fin N) = s := Fin.ext heq.symm
            rw [hsf, ite_false_of_w10 (by omega : ¬ (s.val < m')),
                ite_true_of_w10 (by omega : s.val < m' + 1)]
            rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1) with hj | hj
            · rw [show j = fin2Z0W17 from Fin.ext hj]; simp [basisVec2D, fin2Z0W17, fin2Z1W17]
            · rw [show j = fin2Z1W17 from Fin.ext hj]; simp [basisVec2D, fin2Z0W17, fin2Z1W17]
          · have hne_b : (s.val == m') = false := beq_false_of_ne heq
            have hb0 : basisVec2D N ⟨m', hm_lt⟩ fin2Z0W17 s j = 0 := by simp [basisVec2D, hne_b]
            have hb1 : basisVec2D N ⟨m', hm_lt⟩ fin2Z1W17 s j = 0 := by simp [basisVec2D, hne_b]
            rw [hb0, hb1, Nat.mul_zero, Nat.mul_zero, Nat.add_zero, Nat.add_zero]
            by_cases hlt : s.val < m'
            · rw [ite_true_of_w10 hlt, ite_true_of_w10 (by omega)]
            · rw [ite_false_of_w10 hlt, ite_false_of_w10 (by omega)]
      rw [hst N (Nat.le_refl N), ite_true_of_w10 s.isLt]
    intro w; induction w with
    | nil =>
      intro i
      have hz : ∀ m : Nat, natSumPrefix N (fun _ => 0) m = 0 := by
        intro m; induction m with
        | zero => rfl
        | succ m' ih => simp only [natSumPrefix]; by_cases hm : m' < N <;> simp [hm, ih]
      simpa [evalFinWordVec] using (hz N).symm
    | cons s rest ih =>
      intro i
      rw [mat2_step_expandN_w17 N M v s rest i, hdelta s i, ih fin2Z0W17, ih fin2Z1W17,
          hsum_mul (M s i fin2Z0W17), hsum_mul (M s i fin2Z1W17), ← hsum_add, ← hsum_add]
      apply hcongr _ _ (fun s0 => ?_) N
      rw [mat2_step_expandN_w17 N M (basisVec2D N s0 fin2Z0W17) s rest i,
          mat2_step_expandN_w17 N M (basisVec2D N s0 fin2Z1W17) s rest i,
          Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add]
      ac_rfl
  have hfark_lin : ∀ xs : List (List (Fin N) × List (Fin N)),
      farkasBiVecLhsN N proj mu0 mu1 k alpha beta gamma v xs =
        natSumPrefix N (fun s0 =>
          v s0 fin2Z0W17 * farkasBiVecLhsN N proj mu0 mu1 k alpha beta gamma (basisVec2D N s0 fin2Z0W17) xs +
          v s0 fin2Z1W17 * farkasBiVecLhsN N proj mu0 mu1 k alpha beta gamma (basisVec2D N s0 fin2Z1W17) xs) N ∧
      farkasBiVecRhsN N proj mu0 mu1 k alpha beta gamma v xs =
        natSumPrefix N (fun s0 =>
          v s0 fin2Z0W17 * farkasBiVecRhsN N proj mu0 mu1 k alpha beta gamma (basisVec2D N s0 fin2Z0W17) xs +
          v s0 fin2Z1W17 * farkasBiVecRhsN N proj mu0 mu1 k alpha beta gamma (basisVec2D N s0 fin2Z1W17) xs) N := by
    intro xs; induction xs with
    | nil =>
      have hz : ∀ m : Nat, natSumPrefix N (fun _ => 0) m = 0 := by
        intro m; induction m with
        | zero => rfl
        | succ m' ih => simp only [natSumPrefix]; by_cases hm : m' < N <;> simp [hm, ih]
      refine ⟨?_, ?_⟩ <;> simpa [farkasBiVecLhsN, farkasBiVecRhsN] using (hz N).symm
    | cons r0 rtl ih =>
      rcases r0 with ⟨l0, r0_w⟩
      rcases ih with ⟨ihl, ihr⟩
      refine ⟨?_, ?_⟩
      · simp only [farkasBiVecLhsN]
        change mu0 l0 * evalFinWordVec N 2 M v l0 fin2Z0W17 +
          (alpha * mu1 l0) * evalFinWordVec N 2 M v l0 fin2Z1W17 +
          farkasBiVecLhsN N proj mu0 mu1 k alpha beta gamma v rtl = _
        rw [hv_lin l0 fin2Z0W17, hv_lin l0 fin2Z1W17, ihl,
            hsum_mul (mu0 l0), hsum_mul (alpha * mu1 l0), ← hsum_add, ← hsum_add]
        apply hcongr _ _ (fun s0 => ?_) N; simp only [Nat.mul_add]; ac_rfl
      · simp only [farkasBiVecRhsN]
        change mu0 l0 * evalFinWordVec N 2 M v r0_w fin2Z0W17 +
          (alpha * mu1 l0) * evalFinWordVec N 2 M v r0_w fin2Z1W17 +
          farkasBiVecRhsN N proj mu0 mu1 k alpha beta gamma v rtl = _
        rw [hv_lin r0_w fin2Z0W17, hv_lin r0_w fin2Z1W17, ihr,
            hsum_mul (mu0 l0), hsum_mul (alpha * mu1 l0), ← hsum_add, ← hsum_add]
        apply hcongr _ _ (fun s0 => ?_) N; simp only [Nat.mul_add]; ac_rfl
  have htot_le : farkasBiVecLhsN N proj mu0 mu1 k alpha beta gamma v rs ≤
      farkasBiVecRhsN N proj mu0 mu1 k alpha beta gamma v rs := by
    rcases hfark_lin rs with ⟨hl, hr⟩
    rw [hl, hr]
    exact natSumPrefix_mono_w5 N _ _ (fun s0 =>
      Nat.add_le_add (Nat.mul_le_mul_left _ (hbasis_kabg s0).1)
                     (Nat.mul_le_mul_left _ (hbasis_kabg s0).2)) N
  have hmu0_pos : ∀ r ∈ rs, mu0 r.1 ≥ 1 := by
    intro r hr
    unfold checkWordShapeBiNBool at hshape_b
    rcases bool_and_split (List.all_eq_true.mp hshape_b r hr) with ⟨_, hm0_b⟩
    exact of_decide_eq_true hm0_b
  have hge_imp : ∀ xs : List (List (Fin N) × List (Fin N)),
      (∀ r ∈ xs, mu0 r.1 ≥ 1) ->
      (∀ r ∈ xs, ∀ i : Fin 2, evalFinWordVec N 2 M v r.1 i ≥ evalFinWordVec N 2 M v r.2 i) ->
      farkasBiVecLhsN N proj mu0 mu1 k alpha beta gamma v xs ≥
        farkasBiVecRhsN N proj mu0 mu1 k alpha beta gamma v xs ∧
      (farkasBiVecLhsN N proj mu0 mu1 k alpha beta gamma v xs =
        farkasBiVecRhsN N proj mu0 mu1 k alpha beta gamma v xs ->
        ∀ r ∈ xs, evalFinWordVec N 2 M v r.1 fin2Z0W17 = evalFinWordVec N 2 M v r.2 fin2Z0W17) := by
    intro xs; induction xs with
    | nil => intros; exact ⟨Nat.le_refl 0, fun _ _ hr => by cases hr⟩
    | cons r0 rtl ih =>
      rcases r0 with ⟨l0, r0_w⟩
      intro hmp hw
      rcases ih (fun r hr => hmp r (List.Mem.tail _ hr))
        (fun r hr => hw r (List.Mem.tail _ hr)) with ⟨hge_tl, heq_tl⟩
      simp only [farkasBiVecLhsN, farkasBiVecRhsN]
      have hm0_1 : mu0 l0 ≥ 1 := hmp (l0, r0_w) (List.Mem.head _)
      have hw0 := hw (l0, r0_w) (List.Mem.head _) fin2Z0W17
      have hw1 := hw (l0, r0_w) (List.Mem.head _) fin2Z1W17
      have hg0 := Nat.mul_le_mul_left (mu0 l0) hw0
      have hg1 := Nat.mul_le_mul_left (alpha * mu1 l0) hw1
      dsimp only [M, matFn] at hw0 hw1 hg0 hg1 ⊢
      refine ⟨by omega, fun heq_tot r hr => ?_⟩
      cases hr with
      | head =>
        dsimp only [M, matFn]
        have heq_m0 : mu0 l0 * evalFinWordVec N 2 (fun s => biBTRMat2DC39 k alpha beta gamma (proj s)) v l0 fin2Z0W17 =
            mu0 l0 * evalFinWordVec N 2 (fun s => biBTRMat2DC39 k alpha beta gamma (proj s)) v r0_w fin2Z0W17 := by omega
        exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < mu0 l0) heq_m0
      | tail _ htl_m => exact heq_tl (by omega) r htl_m
  rcases hge_imp rs hmu0_pos hv_weak with ⟨hge_tot, heq_imp⟩
  exact heq_imp (by omega)

/--
  Theorem W17.1b (`simultaneous_bidirectional_b_and_t_d2_farkas_locks`,
  `zero custom axioms`):
  Infinite 4-Parameter Simultaneous Bidirectional `.B` + `.T` + `.R`-Boundary-Growth Mixed
  Zero-Diagonal `d = 2` Cones on BOTH `c39` (`biBTRMat2DC39 k α β γ`, `18/39` strict matrix rules)
  AND `c78` (`biBTRMat2DC78 k α β γ`, `36/78` strict matrix rules), `+13` & `+10` Escapes From
  Wave 16's 2-Rule & 7-Rule Farkas Syzygies, & Universal Parameterized 4-Rule & 11-Rule Bilinear
  Farkas Zero-Strict-Drop Locks (`Branch P4.3`, witness
  `ZPOS_C39_BIDIRECTIONAL_B_AND_T_D2_FARKAS_ESCAPE`, `W17_H1`).
-/
theorem simultaneous_bidirectional_b_and_t_d2_farkas_locks :
    let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
    let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
    (countStrictMat2DRules 42 (biBTRMat2DC39 2 1 1 1) c39 = 18 ∧
     countStrictMat2DRules 84 (biBTRMat2DC78 2 1 1 1) c78 = 36 ∧
     biBTRMat2DC39 2 1 1 1 ⟨6, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩ = 2 ∧
     biBTRMat2DC39 2 1 1 1 ⟨14, by decide⟩ ⟨1, by decide⟩ ⟨0, by decide⟩ = 1 ∧
     biBTRMat2DC39 2 1 1 1 ⟨22, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩ = 1 ∧
     biBTRMat2DC39 2 1 1 1 ⟨37, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩ = 1 ∧
     biBTRMat2DC39 2 1 1 1 ⟨37, by decide⟩ ⟨1, by decide⟩ ⟨0, by decide⟩ = 2 ∧
     w16FarkasLhsOnBi farkasMu0C39 farkasMu1C39
       (basisVec2D 42 ⟨17, by decide⟩ ⟨1, by decide⟩) c39 -
       w16FarkasRhsOnBi farkasMu0C39 farkasMu1C39
         (basisVec2D 42 ⟨17, by decide⟩ ⟨1, by decide⟩) c39 = 13 ∧
     w16FarkasLhsOnBi farkasMu0CoupledC39 farkasMu1CoupledC39
       (basisVec2D 42 ⟨17, by decide⟩ ⟨0, by decide⟩) c39 -
       w16FarkasRhsOnBi farkasMu0CoupledC39 farkasMu1CoupledC39
         (basisVec2D 42 ⟨17, by decide⟩ ⟨0, by decide⟩) c39 = 10) ∧
    (∀ (k alpha beta gamma : Nat), k ≥ 2 -> alpha ≥ 1 -> beta ≥ 1 -> gamma ≥ 1 ->
      (∀ r ∈ c39, ∀ i j : Fin 2,
        evalFinWordMat 42 2 (biBTRMat2DC39 k alpha beta gamma) r.1 i j ≥
          evalFinWordMat 42 2 (biBTRMat2DC39 k alpha beta gamma) r.2 i j) ∧
      (∀ v : Fin 42 -> Fin 2 -> Nat,
        (∀ r ∈ c39, ∀ i : Fin 2,
          evalFinWordVec 42 2 (biBTRMat2DC39 k alpha beta gamma) v r.1 i ≥
            evalFinWordVec 42 2 (biBTRMat2DC39 k alpha beta gamma) v r.2 i) ->
        ∀ r ∈ c39,
          evalFinWordVec 42 2 (biBTRMat2DC39 k alpha beta gamma) v r.1 ⟨0, by decide⟩ =
            evalFinWordVec 42 2 (biBTRMat2DC39 k alpha beta gamma) v r.2 ⟨0, by decide⟩)) ∧
    (∀ (k alpha beta gamma : Nat), k ≥ 2 -> alpha ≥ 1 -> beta ≥ 1 -> gamma ≥ 1 ->
      (∀ r ∈ c78, ∀ i j : Fin 2,
        evalFinWordMat 84 2 (biBTRMat2DC78 k alpha beta gamma) r.1 i j ≥
          evalFinWordMat 84 2 (biBTRMat2DC78 k alpha beta gamma) r.2 i j) ∧
      (∀ v : Fin 84 -> Fin 2 -> Nat,
        (∀ r ∈ c78, ∀ i : Fin 2,
          evalFinWordVec 84 2 (biBTRMat2DC78 k alpha beta gamma) v r.1 i ≥
            evalFinWordVec 84 2 (biBTRMat2DC78 k alpha beta gamma) v r.2 i) ->
        ∀ r ∈ c78,
          evalFinWordVec 84 2 (biBTRMat2DC78 k alpha beta gamma) v r.1 ⟨0, by decide⟩ =
            evalFinWordVec 84 2 (biBTRMat2DC78 k alpha beta gamma) v r.2 ⟨0, by decide⟩)) := by
  dsimp only
  rw [c39_eq_fastRules_w17, c78_eq_fastRules_w17]
  rcases bi_c39_c78_shape_and_witness_certs with
    ⟨hshape39, hshape78, _, hst18, hst36, hexc13, hexc10⟩
  rw [w16FarkasFastPairOnBi_eq] at hexc13 hexc10
  refine ⟨⟨hst18, hst36, rfl, rfl, rfl, rfl, rfl, hexc13, hexc10⟩, ?_, ?_⟩
  · intro k alpha beta gamma _ _ _ _
    refine ⟨(weak_mat_orientation_4param_bi_cones_w17 k alpha beta gamma).1, ?_⟩
    intro v hv_weak
    exact bi_farkas_zero_strict_proj_w17 42 id farkasMu0CoupledC39 farkasMu1BiBTRC39
      c39FastRulesW17 hshape39 bi_c39_farkas_b0_cert bi_c39_farkas_b1_cert
      k alpha beta gamma v hv_weak
  · intro k alpha beta gamma _ _ _ _
    refine ⟨(weak_mat_orientation_4param_bi_cones_w17 k alpha beta gamma).2, ?_⟩
    intro v hv_weak
    exact bi_farkas_zero_strict_proj_w17 84 projSym84To42 farkasMu0CoupledC78 farkasMu1BiBTRC78
      c78FastRulesW17 hshape78 bi_c78_farkas_b0_cert bi_c78_farkas_b1_cert
      k alpha beta gamma v hv_weak

-- ----------------------------------------------------------------------------
-- Section 1C: Unconditional `1..20`-Cycle Freedom Across ALL `DP2` Words &
--             Universal Arbitrary-`m` (`∀ m ≥ 1`) `.R`-Carrying `leftAnchoredDP2Step`
--             Cycle-to-Brox Spiral Locks (`W17_H1`)
-- ----------------------------------------------------------------------------

/-- Canonical shift-word expansion of an `m`-block Syracuse tuple `[(w_0, a_0), ..., (w_{m-1}, a_{m-1})]`:
    maps each `(w, a)` to `List.replicate (w - 1) 1 ++ [1 + a]`. -/
def dp2BlocksToShifts : List (Nat × Nat) -> List Nat
  | [] => []
  | (w, a) :: rest => (List.replicate (w - 1) 1 ++ [1 + a]) ++ dp2BlocksToShifts rest

private def syrStepW17 (n : Nat) : Nat := core2 (3 * n + 1)

private def syrIterW17 : Nat -> Nat -> Nat
  | 0, n => n
  | k + 1, n => syrIterW17 k (syrStepW17 n)

private theorem syrIterW17_add :
    ∀ (a b n : Nat), syrIterW17 (a + b) n = syrIterW17 b (syrIterW17 a n)
  | 0, _, _ => by rw [Nat.zero_add]; rfl
  | a + 1, b, n => by rw [Nat.succ_add]; exact syrIterW17_add a b (syrStepW17 n)

set_option maxRecDepth 65536 in
private theorem no_small_odd_syr_cycles_16_to_20 :
    ∀ (r : Fin 21) (k : Fin 72),
      16 ≤ r.val -> syrIterW17 r.val (2 * k.val + 3) ≠ 2 * k.val + 3 := by decide

private theorem dp2AnnotatedChain_syr_and_ge147_bound_w17 :
    ∀ (shifts : List Nat) (u0 ur : List MixedSRSSym),
      dp2AnnotatedChain u0 shifts ur ->
      dp2GlobalOddVal ur = syrIterW17 shifts.length (dp2GlobalOddVal u0) ∧
      ((∃ n : Nat, 3 ≤ n ∧ n ≤ 145 ∧ n % 2 = 1 ∧
          ∃ i : Nat, i ≤ shifts.length ∧
            syrIterW17 i (dp2GlobalOddVal u0) = n ∧
            dp2GlobalOddVal ur = syrIterW17 (shifts.length - i) n) ∨
       147 ^ shifts.length * 2 ^ dp2ShiftSum shifts * dp2GlobalOddVal ur ≤
         442 ^ shifts.length * dp2GlobalOddVal u0)
  | [], u0, ur, heq => by
    subst heq; exact ⟨rfl, Or.inr (by simp [dp2ShiftSum])⟩
  | a :: rest, u0, ur, ⟨_, w, _, hsyr_step, htl⟩ => by
    have hNw_pos : dp2GlobalOddVal w > 0 := by unfold dp2GlobalOddVal; omega
    have hNw_odd : dp2GlobalOddVal w % 2 = 1 := by unfold dp2GlobalOddVal; omega
    have hNu_ge3 : dp2GlobalOddVal u0 ≥ 3 := by unfold dp2GlobalOddVal; omega
    have hNu_odd : dp2GlobalOddVal u0 % 2 = 1 := by unfold dp2GlobalOddVal; omega
    have hsyr_eq : syrStepW17 (dp2GlobalOddVal u0) = dp2GlobalOddVal w := by
      unfold syrStepW17
      rw [← hsyr_step, core2_pow2_mul a (dp2GlobalOddVal w) hNw_pos hNw_odd]
    rcases dp2AnnotatedChain_syr_and_ge147_bound_w17 rest w ur htl with ⟨ih_syr, ih_disj⟩
    have hiter_tot : dp2GlobalOddVal ur = syrIterW17 (rest.length + 1) (dp2GlobalOddVal u0) := by
      simp only [syrIterW17, hsyr_eq]; exact ih_syr
    simp only [List.length_cons, dp2ShiftSum]
    refine ⟨hiter_tot, ?_⟩
    by_cases hle145 : dp2GlobalOddVal u0 ≤ 145
    · left
      exact ⟨dp2GlobalOddVal u0, hNu_ge3, hle145, hNu_odd, 0, Nat.zero_le _, rfl, hiter_tot⟩
    · rcases ih_disj with ⟨n, hn3, hn145, hno, i, hi_le, hi_eq, hur_eq⟩ | ih_ge147
      · left
        refine ⟨n, hn3, hn145, hno, i + 1, Nat.succ_le_succ hi_le, ?_, ?_⟩
        · simp only [syrIterW17, hsyr_eq]; exact hi_eq
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

private theorem dp2AnnotatedChain_split_w17 :
    ∀ (xs ys : List Nat) (u0 uz : List MixedSRSSym),
      dp2AnnotatedChain u0 (xs ++ ys) uz ->
      ∃ um : List MixedSRSSym, dp2AnnotatedChain u0 xs um ∧ dp2AnnotatedChain um ys uz
  | [], ys, u0, uz, h => ⟨u0, rfl, h⟩
  | x :: xtl, ys, u0, uz, ⟨hx, w, hst, hsyr, htl⟩ => by
    rcases dp2AnnotatedChain_split_w17 xtl ys w uz htl with ⟨um, h1, h2⟩
    exact ⟨um, ⟨hx, w, hst, hsyr, h1⟩, h2⟩

private theorem dp2AnnotatedChain_concat_w17 :
    ∀ (xs ys : List Nat) (u0 um uz : List MixedSRSSym),
      dp2AnnotatedChain u0 xs um ->
      dp2AnnotatedChain um ys uz ->
      dp2AnnotatedChain u0 (xs ++ ys) uz
  | [], _, u0, um, _, h1, h2 => by subst h1; exact h2
  | x :: xtl, ys, u0, um, uz, ⟨hx, w, hst, hsyr, htl⟩, h2 =>
    ⟨hx, w, hst, hsyr, dp2AnnotatedChain_concat_w17 xtl ys w um uz htl h2⟩

private theorem hensel_quotient_boost_cf_w17
    (s w0 a0 w1 q0 q1 d_mult : Nat)
    (hs4 : s ≥ 4) (ha_ge : a0 ≥ s) (hd_odd : d_mult % 2 = 1) (hdvd : d_mult ∣ q0)
    (hrec : 2 ^ (a0 + w1) * q1 = 3 ^ w0 * q0 + (2 ^ a0 - 1)) :
    q0 ≥ henselOddInvModPow2 s (3 ^ w0 * d_mult) * d_mult := by
  have henson_spec : ∀ (k d : Nat), k ≥ 1 -> d % 2 = 1 ->
      1 ≤ henselOddInvModPow2 k d ∧
      henselOddInvModPow2 k d < 2 ^ k ∧
      henselOddInvModPow2 k d % 2 = 1 ∧
      (d * henselOddInvModPow2 k d) % 2 ^ k = 1 := by
    intro k; induction k with
    | zero => intro _ hk; omega
    | succ k' ih =>
      cases k' with
      | zero =>
        intro d _ hd_o; simp only [henselOddInvModPow2]
        exact ⟨by decide, by decide, by decide, by omega⟩
      | succ m =>
        intro d _ hd_o
        rcases ih d (by omega) hd_o with ⟨hx1, hx_lt, hx_odd, hx_mod⟩
        simp only [henselOddInvModPow2]
        have hp_pos : 2 ^ (m + 1) ≥ 2 := by simpa using pow2_mono_nat (by omega : 1 ≤ m + 1)
        have hp2_eq : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
        cases hc : ((d * henselOddInvModPow2 (m + 1) d) % 2 ^ (m + 2) == 1)
        · simp only [Bool.false_eq_true, ite_false]
          have hne1 := beq_eq_false_iff_ne.mp hc
          let x := henselOddInvModPow2 (m + 1) d
          change 1 ≤ x + 2 ^ (m + 1) ∧ x + 2 ^ (m + 1) < 2 ^ (m + 2) ∧
            (x + 2 ^ (m + 1)) % 2 = 1 ∧ (d * (x + 2 ^ (m + 1))) % 2 ^ (m + 2) = 1
          have hp_ev : 2 ^ (m + 1) % 2 = 0 := by rw [Nat.pow_succ]; omega
          let q := (d * x) / 2 ^ (m + 1)
          have hdx : d * x = 2 ^ (m + 1) * q + 1 := by
            have := Nat.div_add_mod (d * x) (2 ^ (m + 1))
            dsimp [x] at *; rw [hx_mod] at this; exact this.symm
          have hq_odd : q % 2 = 1 := by
            rcases (by omega : q % 2 = 0 ∨ q % 2 = 1) with hqe | hqo
            · exfalso
              let qh := q / 2
              have hm_eq : d * x = 2 ^ (m + 2) * qh + 1 := by
                rw [hdx, show q = 2 * qh by omega, hp2_eq]; ac_rfl
              have hmod1 : (d * x) % 2 ^ (m + 2) = 1 := by
                rw [hm_eq, Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_right]
                exact Nat.mod_eq_of_lt (by omega)
              exact hne1 hmod1
            · exact hqo
          let q' := q / 2
          let d' := d / 2
          have hprod_new : d * (x + 2 ^ (m + 1)) = 2 ^ (m + 2) * (q' + d' + 1) + 1 := by
            rw [Nat.mul_add, hdx, show q = 2 * q' + 1 by omega, show d = 2 * d' + 1 by omega, hp2_eq]
            simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
            rw [show (2 * d') * 2 ^ (m + 1) = (2 * 2 ^ (m + 1)) * d' by ac_rfl,
                show 2 ^ (m + 1) * (2 * q') = (2 * 2 ^ (m + 1)) * q' by ac_rfl]
            generalize (2 * 2 ^ (m + 1)) * q' = A, (2 * 2 ^ (m + 1)) * d' = B, 2 ^ (m + 1) = P
            omega
          refine ⟨by omega, by omega, by omega, ?_⟩
          rw [hprod_new, Nat.mul_comm (2 ^ (m + 2)), Nat.add_comm, Nat.add_mul_mod_self_right]
          exact Nat.mod_eq_of_lt (by omega)
        · simp only [ite_true]
          exact ⟨hx1, by omega, hx_odd, beq_iff_eq.mp hc⟩
  rcases hdvd with ⟨k_q, hkq⟩
  have h2s_pos : 2 ^ s ≥ 16 := by simpa using pow2_mono_nat hs4
  have hlhs_m : (2 ^ (a0 + w1) * q1) % 2 ^ s = 0 := by
    rw [show a0 + w1 = s + (a0 + w1 - s) by omega, Nat.pow_add, Nat.mul_assoc, Nat.mul_mod_right]
  have hmod1 : (3 ^ w0 * q0) % 2 ^ s = 1 := by
    have hqa : 2 ^ a0 = 2 ^ s * 2 ^ (a0 - s) := by
      conv => lhs; rw [show a0 = s + (a0 - s) by omega, Nat.pow_add]
    have hadd1 : 3 ^ w0 * q0 + 2 ^ a0 = 2 ^ (a0 + w1) * q1 + 1 := by
      have := nat_pow_pos_of_pos 2 (by decide) a0; omega
    have hmod_add := congrArg (· % 2 ^ s) hadd1
    rwa [hqa, Nat.add_mul_mod_self_left, Nat.add_mod, hlhs_m, Nat.zero_add, Nat.mod_mod,
         Nat.mod_eq_of_lt (by omega : 1 < 2 ^ s)] at hmod_add
  have h3w_odd : (3 ^ w0 * d_mult) % 2 = 1 := by
    have h3o : ∀ n : Nat, 3 ^ n % 2 = 1 := by
      intro n; induction n with | zero => rfl | succ n' ihn => rw [Nat.pow_succ, Nat.mul_mod, ihn]
    rw [Nat.mul_mod, h3o w0, hd_odd]
  rcases henson_spec s (3 ^ w0 * d_mult) (by omega) h3w_odd with ⟨_, hinv_lt, _, hinv_mod⟩
  let r_inv := henselOddInvModPow2 s (3 ^ w0 * d_mult)
  have hm_mul : ∀ x y : Nat, (x * y) % 2 ^ s = (x * (y % 2 ^ s)) % 2 ^ s := by
    intro x y; rw [Nat.mul_mod x (y % 2 ^ s) (2 ^ s), Nat.mod_mod, ← Nat.mul_mod]
  have hm_mul_l : ∀ x y : Nat, (x * y) % 2 ^ s = ((x % 2 ^ s) * y) % 2 ^ s := by
    intro x y; rw [Nat.mul_mod (x % 2 ^ s) y (2 ^ s), Nat.mod_mod, ← Nat.mul_mod]
  have hkq_mod : k_q % 2 ^ s = r_inv := by
    have hm1 : ((3 ^ w0 * d_mult) * k_q) % 2 ^ s = 1 := by rwa [hkq, ← Nat.mul_assoc] at hmod1
    calc k_q % 2 ^ s
        = (1 * k_q) % 2 ^ s := by rw [Nat.one_mul]
      _ = (((r_inv * (3 ^ w0 * d_mult)) % 2 ^ s) * k_q) % 2 ^ s := by rw [Nat.mul_comm r_inv, hinv_mod]
      _ = (r_inv * ((3 ^ w0 * d_mult) * k_q)) % 2 ^ s := by rw [← hm_mul_l, Nat.mul_assoc]
      _ = (r_inv * (((3 ^ w0 * d_mult) * k_q) % 2 ^ s)) % 2 ^ s := hm_mul _ _
      _ = r_inv % 2 ^ s := by rw [hm1, Nat.mul_one]
      _ = r_inv := Nat.mod_eq_of_lt hinv_lt
  have hkq_ge : k_q ≥ r_inv := by have := Nat.mod_le k_q (2 ^ s); omega
  rw [hkq, Nat.mul_comm d_mult k_q]
  exact Nat.mul_le_mul_right d_mult hkq_ge

private theorem rotBlocks_one_rotBlocks_cf_w17 (bs : List (Nat × Nat))
    (_hge2 : bs.length ≥ 2) (j : Nat) (hj : j < bs.length) :
    rotBlocks 1 (rotBlocks j bs) = rotBlocks ((j + 1) % bs.length) bs := by
  have hdrop_cons : ∀ (xs : List (Nat × Nat)) (idx : Nat), idx < xs.length ->
      ∃ x : Nat × Nat, xs.drop idx = x :: xs.drop (idx + 1) ∧ xs.take (idx + 1) = xs.take idx ++ [x] := by
    intro xs; induction xs with
    | nil => intro _ h; simp at h
    | cons a xtl ih =>
      intro idx h; cases idx with
      | zero => exact ⟨a, rfl, rfl⟩
      | succ idx' =>
        rcases ih idx' (by simp at h; omega) with ⟨x, hdx, htx⟩
        exact ⟨x, hdx, by simp [htx]⟩
  rcases hdrop_cons bs j hj with ⟨bj, hdj, htj1⟩
  rcases Nat.lt_or_ge (j + 1) bs.length with hj1_lt | hj1_ge
  · have hmod_eq : (j + 1) % bs.length = j + 1 := Nat.mod_eq_of_lt hj1_lt
    rw [hmod_eq]
    unfold rotBlocks
    rw [hdj, List.cons_append]
    simp only [List.drop, List.take, List.append_assoc, ← htj1]
  · have hj1_eq : j + 1 = bs.length := by omega
    have hmod0 : (j + 1) % bs.length = 0 := by rw [hj1_eq, Nat.mod_self]
    rw [hmod0]
    have hdrop_end : bs.drop (j + 1) = [] := by simp [hj1_eq]
    have htake_end : bs.take (j + 1) = bs := by simp [hj1_eq]
    rw [hdrop_end] at hdj
    rw [htake_end] at htj1
    unfold rotBlocks
    rw [hdj, List.singleton_append]
    simp only [List.drop, List.take, List.append_nil, ← htj1]

/--
  Theorem W17.1c (`leftAnchoredDP2_no_1_to_20_cycles_and_all_m_block_locks`,
  `zero custom axioms`):
  Unconditional `1..20`-Cycle Freedom Across ALL `DP2` Words, `M1` `(r = 17, A = 27)`
  `129009091 / 5077565` Carry Separation, Exact Universal Arbitrary-`m` (`∀ m ≥ 1`)
  `dp2IterCarry (dp2BlocksToShifts blocks) <-> broxSpiralCarry blocks` Identity, &
  Universal Arbitrary-`m` (`∀ blocks = b0 :: rest`) `.R`-Carrying `leftAnchoredDP2Step`
  Cycle-to-Brox Spiral Lock Across All `m` Cyclic Rotations (`Branch P4.3`, witness
  `M1_DP2_17CYCLE_129009091_OVER_5077565`, `W17_H1`).
-/
theorem leftAnchoredDP2_no_1_to_20_cycles_and_all_m_block_locks :
    ((∀ (r : Nat) (u : List MixedSRSSym),
        1 ≤ r -> r ≤ 20 -> ¬ dp2StepIter r u u) ∧
     (dp2IterCarry (List.replicate 16 1 ++ [11]) = 129009091 ∧
      2 ^ 27 - 3 ^ 17 = 5077565 ∧
      129009091 % 5077565 = 2069966)) ∧
    (∀ (b0 : Nat × Nat) (rest : List (Nat × Nat)),
      (∀ b ∈ b0 :: rest, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      let blocks := b0 :: rest
      (dp2BlocksToShifts blocks).length = blockWeightSum blocks ∧
      dp2ShiftSum (dp2BlocksToShifts blocks) = blockStepSum blocks ∧
      2 ^ b0.1 * broxSpiralCarry blocks + 3 ^ blockWeightSum blocks =
        dp2IterCarry (dp2BlocksToShifts blocks) + 2 ^ blockStepSum blocks) ∧
    (∀ (b0 : Nat × Nat) (rest : List (Nat × Nat)) (u0 : List MixedSRSSym),
      let blocks := b0 :: rest
      let W := blockWeightSum blocks
      let K := blockStepSum blocks
      let D := 2 ^ K - 3 ^ W
      (∀ b ∈ blocks, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      dp2AnnotatedChain u0 (dp2BlocksToShifts blocks) u0 ->
      W ≥ 21 ∧
      3 ^ W < 2 ^ K ∧
      (∃ (us : List (List MixedSRSSym)) (qs : List Nat),
        us.length = blocks.length ∧
        qs.length = blocks.length ∧
        us.head? = some u0 ∧
        (∀ j : Nat, j < blocks.length ->
          match us.drop j with
          | uj :: _ =>
            let bj := blockAt blocks j
            2 ^ bj.1 ∣ (dp2GlobalOddVal uj + 1) ∧
            natAt qs j = (dp2GlobalOddVal uj + 1) / 2 ^ bj.1 ∧
            natAt qs j ≥ 1 ∧
            natAt qs j % 2 = 1 ∧
            D * natAt qs j = broxSpiralCarry (rotBlocks j blocks)
          | [] => False) ∧
        (∀ (pivots : List (Nat × Nat)) (b_last : Nat × Nat) (tail : List (Nat × Nat)),
          pivots ++ (b_last :: tail) = blocks ->
          D ≤ multiPivotCarryUB pivots b_last tail) ∧
        (¬ (3 ∣ D) ∧
         ((∀ b ∈ blocks, 2 ∣ b.2) -> 3 ∣ natListGcd qs) ∧
         ((∀ b ∈ blocks, 4 ∣ b.2) -> (2 ∣ W ∨ (¬ (5 ∣ D) ∧ 15 ∣ natListGcd qs))) ∧
         ((∀ b ∈ blocks, 8 ∣ b.2) ->
           (2 ∣ W ∨ (¬ (5 ∣ D) ∧ ¬ (17 ∣ D) ∧ 255 ∣ natListGcd qs)) ∧
           (16 ∣ W ∨ (¬ (17 ∣ D) ∧ 51 ∣ natListGcd qs))) ∧
         ((∀ b ∈ blocks, 3 ∣ b.2) -> (6 ∣ W ∨ (¬ (7 ∣ D) ∧ 7 ∣ natListGcd qs))) ∧
         ((∀ b ∈ blocks, 5 ∣ b.2) -> (30 ∣ W ∨ (¬ (31 ∣ D) ∧ 31 ∣ natListGcd qs))) ∧
         ((∀ b ∈ blocks, 9 ∣ b.2) ->
           (6 ∣ W ∨ (¬ (7 ∣ D) ∧ ¬ (73 ∣ D) ∧ 511 ∣ natListGcd qs)) ∧
           (36 ∣ W ∨ (¬ (73 ∣ D) ∧ 73 ∣ natListGcd qs)))) ∧
        (∀ (j : Nat) (pivots : List (Nat × Nat)) (b_last : Nat × Nat)
           (tail : List (Nat × Nat)) (d_mult : Nat),
          j < blocks.length ->
          rotBlocks j blocks = pivots ++ (b_last :: tail) ->
          d_mult ∣ natAt qs j ->
          d_mult * D ≤ multiPivotCarryUB pivots b_last tail) ∧
        (blocks.length ≥ 2 ->
          ∀ (j : Nat) (bj : Nat × Nat) (ps : List (Nat × Nat)) (b_last : Nat × Nat)
            (tail : List (Nat × Nat)) (s d_mult : Nat),
            j < blocks.length ->
            rotBlocks j blocks = (bj :: ps) ++ (b_last :: tail) ->
            s ≥ 4 ->
            bj.2 ≥ s ->
            d_mult % 2 = 1 ->
            d_mult ∣ natAt qs j ->
            (henselOddInvModPow2 s (3 ^ bj.1 * d_mult) * d_mult) * D ≤
              multiPivotCarryUB (bj :: ps) b_last tail))) := by
  have hno_1_15 := leftAnchoredDP2_no_1_to_15_cycles_and_three_block_locks.2.1.1
  have happ := leftAnchoredDP2_no_1_to_10_cycles_and_two_block_locks.1.1
  -- Part 1: Unconditional `1..20`-cycle freedom across ALL `DP2` words (`N_cut = 147`):
  have hno_1_20 : ∀ (r : Nat) (u : List MixedSRSSym),
      1 ≤ r -> r ≤ 20 -> ¬ dp2StepIter r u u := by
    intro r u hr1 hr20 hiter
    by_cases hr15 : r ≤ 15
    · exact hno_1_15 r u hr1 hr15 hiter
    · rcases (leftAnchoredDP2_iterated_affine_carry_and_cycle_laws.1 r u u hiter).2 with
        ⟨shifts, hlen, _, hann, _, _⟩
      rcases leftAnchoredDP2_iterated_affine_carry_and_cycle_laws.2.1.1 shifts u (by omega) hann with
        ⟨hlt, _, _, _⟩
      rw [hlen] at hlt
      rcases dp2AnnotatedChain_syr_and_ge147_bound_w17 shifts u u hann with ⟨_, hsmall | hge147⟩
      · rcases hsmall with ⟨n, hn3, hn145, hno, i, hi_le, hi_eq, hur_eq⟩
        rw [hlen] at hi_le hur_eq
        have hcyc_n : syrIterW17 r n = n := by
          rw [show r = (r - i) + i by omega, syrIterW17_add (r - i) i n, ← hur_eq, hi_eq]
        let k := (n - 3) / 2
        have hk_lt : k < 72 := by dsimp [k]; omega
        have hn_eq : n = 2 * k + 3 := by dsimp [k]; omega
        rw [hn_eq] at hcyc_n
        exact no_small_odd_syr_cycles_16_to_20 ⟨r, by omega⟩ ⟨k, hk_lt⟩ (by dsimp; omega) hcyc_n
      · rw [hlen] at hge147
        have hNu_pos : dp2GlobalOddVal u > 0 := by unfold dp2GlobalOddVal; omega
        have h147_le : 147 ^ r * 2 ^ dp2ShiftSum shifts ≤ 442 ^ r :=
          nat_mul_le_cancel_right_w5 (dp2GlobalOddVal u) _ _ hNu_pos hge147
        let A := dp2ShiftSum shifts
        change 3 ^ r < 2 ^ A at hlt
        change 147 ^ r * 2 ^ A ≤ 442 ^ r at h147_le
        rcases (by omega : r = 16 ∨ r = 17 ∨ r = 18 ∨ r = 19 ∨ r = 20) with
          rfl | rfl | rfl | rfl | rfl
        · by_cases hA : A ≤ 25
          · exact absurd (Nat.lt_of_lt_of_le hlt (nat_pow_mono_exp_pos 2 A 25 (by decide) hA)) (by decide)
          · have hp := Nat.mul_le_mul_left (147 ^ 16) (nat_pow_mono_exp_pos 2 26 A (by decide) (by omega))
            exact absurd (Nat.le_trans hp h147_le) (by decide)
        · by_cases hA : A ≤ 26
          · exact absurd (Nat.lt_of_lt_of_le hlt (nat_pow_mono_exp_pos 2 A 26 (by decide) hA)) (by decide)
          · have hp := Nat.mul_le_mul_left (147 ^ 17) (nat_pow_mono_exp_pos 2 27 A (by decide) (by omega))
            exact absurd (Nat.le_trans hp h147_le) (by decide)
        · by_cases hA : A ≤ 28
          · exact absurd (Nat.lt_of_lt_of_le hlt (nat_pow_mono_exp_pos 2 A 28 (by decide) hA)) (by decide)
          · have hp := Nat.mul_le_mul_left (147 ^ 18) (nat_pow_mono_exp_pos 2 29 A (by decide) (by omega))
            exact absurd (Nat.le_trans hp h147_le) (by decide)
        · by_cases hA : A ≤ 30
          · exact absurd (Nat.lt_of_lt_of_le hlt (nat_pow_mono_exp_pos 2 A 30 (by decide) hA)) (by decide)
          · have hp := Nat.mul_le_mul_left (147 ^ 19) (nat_pow_mono_exp_pos 2 31 A (by decide) (by omega))
            exact absurd (Nat.le_trans hp h147_le) (by decide)
        · by_cases hA : A ≤ 31
          · exact absurd (Nat.lt_of_lt_of_le hlt (nat_pow_mono_exp_pos 2 A 31 (by decide) hA)) (by decide)
          · have hp := Nat.mul_le_mul_left (147 ^ 20) (nat_pow_mono_exp_pos 2 32 A (by decide) (by omega))
            exact absurd (Nat.le_trans hp h147_le) (by decide)
  -- Part 2: Universal `∀ m ≥ 1` `dp2IterCarry (dp2BlocksToShifts blocks) <-> broxSpiralCarry blocks` identity:
  have hsum_blk : ∀ w a : Nat, w ≥ 1 ->
      (List.replicate (w - 1) 1 ++ [1 + a]).length = w ∧
      dp2ShiftSum (List.replicate (w - 1) 1 ++ [1 + a]) = w + a := by
    intro w a hw
    have hrep : ∀ k : Nat, dp2ShiftSum (List.replicate k 1) = k := by
      intro k; induction k with
      | zero => rfl
      | succ k' ih => simp [List.replicate, dp2ShiftSum, ih]; omega
    rw [List.length_append, List.length_replicate, List.length_singleton,
        (happ _ _).1, hrep (w - 1)]
    simp [dp2ShiftSum]; omega
  have hall_m_id : ∀ (rest : List (Nat × Nat)) (b0 : Nat × Nat),
      (∀ b ∈ b0 :: rest, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      (dp2BlocksToShifts (b0 :: rest)).length = blockWeightSum (b0 :: rest) ∧
      dp2ShiftSum (dp2BlocksToShifts (b0 :: rest)) = blockStepSum (b0 :: rest) ∧
      2 ^ b0.1 * broxSpiralCarry (b0 :: rest) + 3 ^ blockWeightSum (b0 :: rest) =
        dp2IterCarry (dp2BlocksToShifts (b0 :: rest)) + 2 ^ blockStepSum (b0 :: rest) := by
    intro rest; induction rest with
    | nil =>
      intro b0 hpos
      rcases hpos b0 (List.Mem.head _) with ⟨hw0, ha0⟩
      simp only [dp2BlocksToShifts, List.append_nil, blockWeightSum, blockStepSum,
                 Nat.add_zero, broxSpiralCarry]
      refine ⟨(hsum_blk b0.1 b0.2 hw0).1, (hsum_blk b0.1 b0.2 hw0).2, ?_⟩
      rw [(leftAnchoredDP2_iterated_affine_carry_and_cycle_laws.2.2.2 b0.1 (1 + b0.2) hw0).1]
      have hle_23 : 2 ^ b0.1 ≤ 3 ^ b0.1 := pow_mono_base_w17c 2 3 (by decide) b0.1
      have hp_a0 : 2 ^ b0.2 ≥ 1 := nat_pow_pos_of_pos 2 (by decide) b0.2
      rw [Nat.pow_add 2 b0.1 b0.2, Nat.mul_sub_left_distrib, Nat.mul_one]
      generalize 2 ^ b0.1 = P2, 3 ^ b0.1 = P3, 2 ^ b0.2 = PA at hle_23 hp_a0 ⊢
      have hle_pa : P2 ≤ P2 * PA := Nat.le_mul_of_pos_right P2 hp_a0
      omega
    | cons b1 tl ih =>
      intro b0 hpos
      rcases hpos b0 (List.Mem.head _) with ⟨hw0, ha0⟩
      rcases ih b1 (fun b hb => hpos b (List.Mem.tail b0 hb)) with ⟨ih_len, ih_sum, ih_car⟩
      let blk0 := List.replicate (b0.1 - 1) 1 ++ [1 + b0.2]
      let tail_sh := dp2BlocksToShifts (b1 :: tl)
      have hsh_eq : dp2BlocksToShifts (b0 :: b1 :: tl) = blk0 ++ tail_sh := rfl
      have hlen_tot : (dp2BlocksToShifts (b0 :: b1 :: tl)).length = blockWeightSum (b0 :: b1 :: tl) := by
        rw [hsh_eq, List.length_append, (hsum_blk b0.1 b0.2 hw0).1, ih_len]; rfl
      have hsum_tot : dp2ShiftSum (dp2BlocksToShifts (b0 :: b1 :: tl)) = blockStepSum (b0 :: b1 :: tl) := by
        rw [hsh_eq, (happ blk0 tail_sh).1, (hsum_blk b0.1 b0.2 hw0).2, ih_sum]; rfl
      refine ⟨hlen_tot, hsum_tot, ?_⟩
      rw [hsh_eq, (happ blk0 tail_sh).2, ih_len,
          (hsum_blk b0.1 b0.2 hw0).2,
          (leftAnchoredDP2_iterated_affine_carry_and_cycle_laws.2.2.2 b0.1 (1 + b0.2) hw0).1]
      unfold broxSpiralCarry
      have hle_23 : 2 ^ b0.1 ≤ 3 ^ b0.1 := pow_mono_base_w17c 2 3 (by decide) b0.1
      have hp_a0 : 2 ^ b0.2 ≥ 1 := nat_pow_pos_of_pos 2 (by decide) b0.2
      let W_rem := blockWeightSum (b1 :: tl)
      let K_rem := blockStepSum (b1 :: tl)
      change 2 ^ b0.1 * (3 ^ W_rem * (2 ^ b0.2 - 1) + 2 ^ (b0.2 + b1.1) * broxSpiralCarry (b1 :: tl)) +
          3 ^ (b0.1 + W_rem) =
        3 ^ W_rem * (3 ^ b0.1 - 2 ^ b0.1) + 2 ^ (b0.1 + b0.2) * dp2IterCarry tail_sh +
          2 ^ (b0.1 + b0.2 + K_rem)
      have hmul_ih := congrArg ((2 ^ (b0.1 + b0.2)) * ·) ih_car
      dsimp only [W_rem, K_rem, tail_sh] at hmul_ih ⊢
      rw [Nat.mul_add (2 ^ (b0.1 + b0.2)), Nat.mul_add (2 ^ (b0.1 + b0.2)),
          ← Nat.pow_add 2 (b0.1 + b0.2) (blockStepSum (b1 :: tl))] at hmul_ih
      have hlhs_sp : 2 ^ b0.1 * (2 ^ (b0.2 + b1.1) * broxSpiralCarry (b1 :: tl)) =
          2 ^ (b0.1 + b0.2) * (2 ^ b1.1 * broxSpiralCarry (b1 :: tl)) := by
        rw [Nat.pow_add 2 b0.1 b0.2, Nat.pow_add 2 b0.2 b1.1]; ac_rfl
      rw [Nat.mul_add (2 ^ b0.1), hlhs_sp, Nat.pow_add 3 b0.1 (blockWeightSum (b1 :: tl))]
      have ht1 : 2 ^ b0.1 * (3 ^ blockWeightSum (b1 :: tl) * (2 ^ b0.2 - 1)) =
          3 ^ blockWeightSum (b1 :: tl) * (2 ^ (b0.1 + b0.2) - 2 ^ b0.1) := by
        calc 2 ^ b0.1 * (3 ^ blockWeightSum (b1 :: tl) * (2 ^ b0.2 - 1))
            = 3 ^ blockWeightSum (b1 :: tl) * (2 ^ b0.1 * (2 ^ b0.2 - 1)) := by ac_rfl
          _ = 3 ^ blockWeightSum (b1 :: tl) * (2 ^ b0.1 * 2 ^ b0.2 - 2 ^ b0.1 * 1) := by
              rw [Nat.mul_sub_left_distrib]
          _ = 3 ^ blockWeightSum (b1 :: tl) * (2 ^ (b0.1 + b0.2) - 2 ^ b0.1) := by
              rw [← Nat.pow_add, Nat.mul_one]
      rw [ht1]
      generalize 3 ^ blockWeightSum (b1 :: tl) = P3R,
        2 ^ (b0.1 + b0.2) * (2 ^ b1.1 * broxSpiralCarry (b1 :: tl)) = LHS_B,
        2 ^ (b0.1 + b0.2) * dp2IterCarry (dp2BlocksToShifts (b1 :: tl)) = RHS_C,
        2 ^ (b0.1 + b0.2 + blockStepSum (b1 :: tl)) = PK at hmul_ih ⊢
      have hp_b0_le : 2 ^ b0.1 ≤ 2 ^ (b0.1 + b0.2) :=
        nat_pow_mono_exp_pos 2 b0.1 (b0.1 + b0.2) (by decide) (by omega)
      rw [Nat.mul_sub_left_distrib P3R (2 ^ (b0.1 + b0.2)) (2 ^ b0.1),
          Nat.mul_sub_left_distrib P3R (3 ^ b0.1) (2 ^ b0.1),
          Nat.mul_comm (3 ^ b0.1) P3R]
      have h1 : P3R * 2 ^ b0.1 ≤ P3R * 2 ^ (b0.1 + b0.2) := Nat.mul_le_mul_left P3R hp_b0_le
      have h2 : P3R * 2 ^ b0.1 ≤ P3R * 3 ^ b0.1 := Nat.mul_le_mul_left P3R hle_23
      rw [Nat.mul_comm (2 ^ (b0.1 + b0.2)) P3R] at hmul_ih
      omega
  -- Part 3: Universal `∀ blocks = b0 :: rest` `.R`-carrying `DP2` cycle-to-Brox lock across all rotations:
  have hhom : ∀ (sh : List Nat) (x0 y0 : List MixedSRSSym),
      dp2AnnotatedChain x0 sh y0 ->
      2 ^ dp2ShiftSum sh * dp2GlobalOddVal y0 =
        3 ^ sh.length * dp2GlobalOddVal x0 + dp2IterCarry sh := by
    intro sh; induction sh with
    | nil => intro x0 y0 he; subst he; simp [dp2ShiftSum, dp2IterCarry]
    | cons s stl ih =>
      intro x0 y0 ⟨_, z, _, hsyr, htl⟩
      have ihz := ih z y0 htl
      rw [show s :: stl = [s] ++ stl from rfl, (happ [s] stl).1, (happ [s] stl).2]
      simp only [List.length_append, List.length_singleton, dp2ShiftSum, Nat.add_zero]
      have hc1 : dp2IterCarry [s] = 1 := rfl
      rw [hc1, Nat.pow_add 2 s (dp2ShiftSum stl), Nat.mul_assoc (2 ^ s), ihz,
          Nat.mul_add (2 ^ s), ← Nat.mul_assoc (2 ^ s) (3 ^ stl.length),
          Nat.mul_comm (2 ^ s) (3 ^ stl.length), Nat.mul_assoc (3 ^ stl.length), hsyr,
          Nat.mul_add (3 ^ stl.length), Nat.mul_one,
          ← Nat.mul_assoc (3 ^ stl.length) 3, ← Nat.pow_succ]
      ac_rfl
  have hann_to_iter : ∀ (sh : List Nat) (x y : List MixedSRSSym),
      dp2AnnotatedChain x sh y -> dp2StepIter sh.length x y := by
    intro sh; induction sh with
    | nil => intro x y h0; exact h0
    | cons s stl ih => intro x y ⟨_, z, hst, _, htl⟩; exact ⟨z, hst, ih z y htl⟩
  have hshifts_app : ∀ xs ys : List (Nat × Nat),
      dp2BlocksToShifts (xs ++ ys) = dp2BlocksToShifts xs ++ dp2BlocksToShifts ys := by
    intro xs ys; induction xs with
    | nil => rfl
    | cons x xtl ih => simp only [List.cons_append, dp2BlocksToShifts, ih, List.append_assoc]
  have hwt_app : ∀ xs ys : List (Nat × Nat),
      blockWeightSum (xs ++ ys) = blockWeightSum xs + blockWeightSum ys ∧
      blockStepSum (xs ++ ys) = blockStepSum xs + blockStepSum ys := by
    intro xs ys; induction xs with
    | nil => simp [blockWeightSum, blockStepSum]
    | cons x xtl ih => simp only [List.cons_append, blockWeightSum, blockStepSum, ih.1, ih.2]; omega
  refine ⟨⟨hno_1_20, by decide⟩, fun b0 rest hp => hall_m_id rest b0 hp, ?_⟩
  intro b0 rest u0; dsimp only
  intro hpos hann
  let blocks := b0 :: rest
  rcases hall_m_id rest b0 hpos with ⟨hlen_sh, hsum_sh, _⟩
  have hW_ge21 : blockWeightSum blocks ≥ 21 := by
    by_cases hle20 : blockWeightSum blocks ≤ 20
    · exfalso
      have hit := hann_to_iter (dp2BlocksToShifts blocks) u0 u0 hann
      rw [hlen_sh] at hit
      exact hno_1_20 (blockWeightSum blocks) u0 (by
        have hb0 := (hpos b0 (List.Mem.head _)).1
        dsimp [blocks, blockWeightSum]; omega) hle20 hit
    · omega
  rcases leftAnchoredDP2_iterated_affine_carry_and_cycle_laws.2.1.1
    (dp2BlocksToShifts blocks) u0 (by rw [hlen_sh]; dsimp only [blocks] at hW_ge21 ⊢; omega) hann with ⟨hlt_raw, _, _, _⟩
  rw [hlen_sh, hsum_sh] at hlt_raw
  -- Extract the `m`-element vertex list `us` along `dp2BlocksToShifts blocks`:
  have hextract_us : ∀ (bs : List (Nat × Nat)) (x_start x_end : List MixedSRSSym),
      dp2AnnotatedChain x_start (dp2BlocksToShifts bs) x_end ->
      ∃ us : List (List MixedSRSSym),
        us.length = bs.length ∧
        (bs ≠ [] -> us.head? = some x_start) ∧
        ∀ j : Nat, j < bs.length ->
          ∃ uj : List MixedSRSSym,
            us.drop j = uj :: (us.drop (j + 1)) ∧
            dp2AnnotatedChain x_start (dp2BlocksToShifts (bs.take j)) uj ∧
            dp2AnnotatedChain uj (dp2BlocksToShifts (bs.drop j)) x_end := by
    intro bs; induction bs with
    | nil =>
      intro x_start x_end _
      exact ⟨[], rfl, fun hne => False.elim (hne rfl), fun _ hlt => by simp at hlt⟩
    | cons bh btl ih =>
      intro x_start x_end hch
      unfold dp2BlocksToShifts at hch
      rcases dp2AnnotatedChain_split_w17 (List.replicate (bh.1 - 1) 1 ++ [1 + bh.2])
        (dp2BlocksToShifts btl) x_start x_end hch with ⟨u_mid, h1, h2⟩
      rcases ih u_mid x_end h2 with ⟨us_tl, hlen_tl, _, hspec_tl⟩
      refine ⟨x_start :: us_tl, by simp [hlen_tl], fun _ => rfl, ?_⟩
      intro j hj
      cases j with
      | zero =>
        refine ⟨x_start, rfl, rfl, ?_⟩
        simp only [List.drop]; exact dp2AnnotatedChain_concat_w17 _ _ x_start u_mid x_end h1 h2
      | succ j' =>
        have hj' : j' < btl.length := by simp at hj; omega
        rcases hspec_tl j' hj' with ⟨uj, hdrop_j, htake_j, hrem_j⟩
        refine ⟨uj, hdrop_j, ?_, hrem_j⟩
        simp only [List.take, dp2BlocksToShifts]
        exact dp2AnnotatedChain_concat_w17 _ _ x_start u_mid uj h1 htake_j
  rcases hextract_us blocks u0 u0 hann with ⟨us, hus_len, hus_hd_fn, hus_spec⟩
  let qs : List Nat := List.zipWith (fun u b => (dp2GlobalOddVal u + 1) / 2 ^ b.1) us blocks
  have hqs_len : qs.length = blocks.length := by simp [qs, hus_len]
  have hnatAt_qs : ∀ j : Nat, j < blocks.length ->
      ∀ uj : List MixedSRSSym, us.drop j = uj :: us.drop (j + 1) ->
        natAt qs j = (dp2GlobalOddVal uj + 1) / 2 ^ (blockAt blocks j).1 := by
    have hzw : ∀ (xs : List (List MixedSRSSym)) (ys : List (Nat × Nat)) (j : Nat),
        xs.length = ys.length -> j < ys.length ->
        ∀ xj : List MixedSRSSym, xs.drop j = xj :: xs.drop (j + 1) ->
          natAt (List.zipWith (fun u b => (dp2GlobalOddVal u + 1) / 2 ^ b.1) xs ys) j =
            (dp2GlobalOddVal xj + 1) / 2 ^ (blockAt ys j).1 := by
      intro xs; induction xs with
      | nil => intro ys j hl hj; simp [← hl] at hj
      | cons x xtl ih =>
        intro ys j hl hj xj hdx
        cases ys with
        | nil => simp at hj
        | cons y ytl =>
          cases j with
          | zero =>
            simp only [List.drop, List.cons.injEq] at hdx
            rcases hdx with ⟨rfl, _⟩
            rfl
          | succ j' =>
            simp only [List.zipWith_cons_cons, natAt, List.drop, blockAt]
            exact ih ytl j' (by simp at hl; omega) (by simp at hj; omega) xj hdx
    intro j hj uj hdu; exact hzw us blocks j hus_len hj uj hdu
  have hrot_all : ∀ j : Nat, j < blocks.length ->
      match us.drop j with
      | uj :: _ =>
        let bj := blockAt blocks j
        2 ^ bj.1 ∣ (dp2GlobalOddVal uj + 1) ∧
        natAt qs j = (dp2GlobalOddVal uj + 1) / 2 ^ bj.1 ∧
        natAt qs j ≥ 1 ∧
        natAt qs j % 2 = 1 ∧
        (2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks) * natAt qs j =
          broxSpiralCarry (rotBlocks j blocks)
      | [] => False := by
    intro j hj
    rcases hus_spec j hj with ⟨uj, hdrop_u, htake_u, hrem_u⟩
    rw [hdrop_u]; dsimp only
    have hrot_chain : dp2AnnotatedChain uj (dp2BlocksToShifts (rotBlocks j blocks)) uj := by
      unfold rotBlocks
      rw [hshifts_app]
      exact dp2AnnotatedChain_concat_w17 _ _ uj u0 uj hrem_u htake_u
    have hrot_nonempty : (rotBlocks j blocks).length = blocks.length := by
      unfold rotBlocks; rw [List.length_append, List.length_drop, List.length_take]; omega
    cases hrot_eq : rotBlocks j blocks with
    | nil => rw [hrot_eq] at hrot_nonempty; simp [blocks] at hrot_nonempty
    | cons bj r_tl =>
      have hbj_eq : bj = blockAt blocks j := by
        have hhd : (blocks.drop j).head? = some (blockAt blocks j) := by
          have hst : ∀ (bs : List (Nat × Nat)) (idx : Nat), idx < bs.length ->
              (bs.drop idx).head? = some (blockAt bs idx) := by
            intro bs; induction bs with
            | nil => intro _ h; simp at h
            | cons b btl ihb =>
              intro idx h; cases idx with
              | zero => rfl
              | succ idx' => exact ihb idx' (by simp at h; omega)
          exact hst blocks j hj
        have hrot_hd : (rotBlocks j blocks).head? = (blocks.drop j).head? := by
          unfold rotBlocks
          cases hdj : blocks.drop j with
          | nil => rw [hdj] at hhd; cases hhd
          | cons _ _ => rfl
        rw [hrot_eq] at hrot_hd
        exact Option.some.inj (hrot_hd.trans hhd)
      have hpos_rot : ∀ b ∈ bj :: r_tl, b.1 ≥ 1 ∧ b.2 ≥ 1 := by
        rw [← hrot_eq]; unfold rotBlocks
        intro b hb
        rcases List.mem_append.mp hb with hd | ht
        · exact hpos b (List.mem_of_mem_drop hd)
        · exact hpos b (List.mem_of_mem_take ht)
      have hw_rot : blockWeightSum (bj :: r_tl) = blockWeightSum blocks ∧
          blockStepSum (bj :: r_tl) = blockStepSum blocks := by
        rw [← hrot_eq]; unfold rotBlocks
        rcases hwt_app (blocks.drop j) (blocks.take j) with ⟨hw1, hk1⟩
        have htd : blocks.take j ++ blocks.drop j = blocks := List.take_append_drop j blocks
        rcases hwt_app (blocks.take j) (blocks.drop j) with ⟨hw2, hk2⟩
        rw [htd] at hw2 hk2
        exact ⟨by omega, by omega⟩
      rcases hall_m_id r_tl bj hpos_rot with ⟨hlen_r, hsum_r, hcar_r⟩
      rw [hrot_eq] at hrot_chain
      have hhom_r := hhom (dp2BlocksToShifts (bj :: r_tl)) uj uj hrot_chain
      rw [hlen_r, hsum_r, hw_rot.1, hw_rot.2] at hhom_r
      rw [hw_rot.1, hw_rot.2] at hcar_r
      let W := blockWeightSum blocks
      let K := blockStepSum blocks
      let D := 2 ^ K - 3 ^ W
      have hlt_WK : 3 ^ W < 2 ^ K := hlt_raw
      have hD_Nj : D * dp2GlobalOddVal uj = dp2IterCarry (dp2BlocksToShifts (bj :: r_tl)) := by
        dsimp only [D, W, K]; rw [Nat.sub_mul]
        have hle_m := Nat.mul_le_mul_right (dp2GlobalOddVal uj) (Nat.le_of_lt hlt_WK)
        dsimp only [W, K] at hle_m hhom_r
        omega
      have hD_Nj1 : D * (dp2GlobalOddVal uj + 1) = 2 ^ bj.1 * broxSpiralCarry (bj :: r_tl) := by
        rw [Nat.mul_add, Nat.mul_one, hD_Nj]
        dsimp only [D, W, K] at hlt_WK hcar_r ⊢
        omega
      have hcop_2D : Nat.Coprime (2 ^ bj.1) D := by
        have hD_odd : D % 2 = 1 := by
          have hK1 : K ≥ 1 := by
            have := (hpos b0 (List.Mem.head _)).1; dsimp [K, blocks, blockStepSum]; omega
          have h2K_ev : 2 ^ K % 2 = 0 := by
            rw [show K = (K - 1) + 1 by omega, Nat.pow_succ]; omega
          have h3W_odd : 3 ^ W % 2 = 1 := by
            have h3o : ∀ n : Nat, 3 ^ n % 2 = 1 := by
              intro n; induction n with | zero => rfl | succ n' ihn => rw [Nat.pow_succ, Nat.mul_mod, ihn]
            exact h3o W
          dsimp only [D]; omega
        have hc2 : Nat.Coprime 2 D := by
          rw [Nat.coprime_iff_gcd_eq_one]
          have hg2 : Nat.gcd 2 D ≤ 2 := Nat.le_of_dvd (by decide) (Nat.gcd_dvd_left 2 D)
          have hg_pos : Nat.gcd 2 D ≥ 1 := Nat.gcd_pos_of_pos_left D (by decide)
          have hgD : Nat.gcd 2 D ∣ D := Nat.gcd_dvd_right 2 D
          by_cases h1 : Nat.gcd 2 D = 1
          · exact h1
          · have hg_eq2 : Nat.gcd 2 D = 2 := by omega
            rw [hg_eq2] at hgD
            rcases hgD with ⟨kD, hkD⟩
            omega
        exact hc2.pow_left bj.1
      have hdvd_2bj : 2 ^ bj.1 ∣ (dp2GlobalOddVal uj + 1) :=
        hcop_2D.dvd_of_dvd_mul_left ⟨broxSpiralCarry (bj :: r_tl), hD_Nj1⟩
      have hqs_j := hnatAt_qs j hj uj hdrop_u
      rw [← hbj_eq] at hqs_j ⊢
      rcases hdvd_2bj with ⟨qj, hqj⟩
      have hp2_pos : 0 < 2 ^ bj.1 := nat_pow_pos_of_pos 2 (by decide) bj.1
      have hdiv_qj : (dp2GlobalOddVal uj + 1) / 2 ^ bj.1 = qj := by
        rw [hqj, Nat.mul_comm (2 ^ bj.1) qj, Nat.mul_div_cancel qj hp2_pos]
      have hqs_eq_qj : natAt qs j = qj := hqs_j.trans hdiv_qj
      have hD_qj : D * qj = broxSpiralCarry (bj :: r_tl) := by
        have hm : 2 ^ bj.1 * (D * qj) = 2 ^ bj.1 * broxSpiralCarry (bj :: r_tl) := by
          calc 2 ^ bj.1 * (D * qj) = D * (2 ^ bj.1 * qj) := by ac_rfl
            _ = D * (dp2GlobalOddVal uj + 1) := by rw [← hqj]
            _ = 2 ^ bj.1 * broxSpiralCarry (bj :: r_tl) := hD_Nj1
        exact Nat.eq_of_mul_eq_mul_left hp2_pos hm
      have hqj_pos : qj ≥ 1 := by
        cases qj with
        | zero => rw [Nat.mul_zero] at hqj; unfold dp2GlobalOddVal at hqj; omega
        | succ _ => omega
      have hqj_odd : qj % 2 = 1 := by
        unfold dp2BlocksToShifts at hrot_chain
        rcases dp2AnnotatedChain_split_w17 (List.replicate (bj.1 - 1) 1 ++ [1 + bj.2])
          (dp2BlocksToShifts r_tl) uj uj hrot_chain with ⟨u_nxt, h1_blk, _⟩
        have hh1 := hhom _ uj u_nxt h1_blk
        have hbj_pos := hpos_rot bj (List.Mem.head _)
        rw [(hsum_blk bj.1 bj.2 hbj_pos.1).1, (hsum_blk bj.1 bj.2 hbj_pos.1).2,
            (leftAnchoredDP2_iterated_affine_carry_and_cycle_laws.2.2.2 bj.1 (1 + bj.2) hbj_pos.1).1] at hh1
        have hle_b23 : 2 ^ bj.1 ≤ 3 ^ bj.1 := pow_mono_base_w17c 2 3 (by decide) bj.1
        have hh1' : 2 ^ bj.1 * (2 ^ bj.2 * dp2GlobalOddVal u_nxt + 1) =
            3 ^ bj.1 * (dp2GlobalOddVal uj + 1) := by
          rw [Nat.pow_add 2 bj.1 bj.2, Nat.mul_assoc] at hh1
          generalize 2 ^ bj.1 = B2, 2 ^ bj.2 * dp2GlobalOddVal u_nxt = UN,
            3 ^ bj.1 = B3, dp2GlobalOddVal uj = UJ at hh1 hle_b23 ⊢
          rw [Nat.mul_add B2, Nat.mul_one, Nat.mul_add B3, Nat.mul_one]
          omega
        have hbal1 : 2 ^ bj.1 * (2 ^ bj.2 * dp2GlobalOddVal u_nxt + 1) =
            2 ^ bj.1 * (3 ^ bj.1 * qj) := by
          rw [hh1', hqj]; ac_rfl
        have hstep_qj : 2 ^ bj.2 * dp2GlobalOddVal u_nxt + 1 = 3 ^ bj.1 * qj :=
          Nat.eq_of_mul_eq_mul_left hp2_pos hbal1
        have hlhs_odd : (2 ^ bj.2 * dp2GlobalOddVal u_nxt + 1) % 2 = 1 := by
          rw [show bj.2 = (bj.2 - 1) + 1 by omega, Nat.pow_succ,
              show 2 ^ (bj.2 - 1) * 2 * dp2GlobalOddVal u_nxt =
                2 * (2 ^ (bj.2 - 1) * dp2GlobalOddVal u_nxt) by ac_rfl]
          generalize 2 ^ (bj.2 - 1) * dp2GlobalOddVal u_nxt = M_ev
          omega
        have hrhs_mod := congrArg (· % 2) hstep_qj
        rw [hlhs_odd, Nat.mul_mod] at hrhs_mod
        by_cases hqo : qj % 2 = 1
        · exact hqo
        · have hqe : qj % 2 = 0 := by omega
          rw [hqe, Nat.mul_zero] at hrhs_mod; cases hrhs_mod
      exact ⟨⟨qj, hqj⟩, hqs_j, by rwa [hqs_eq_qj], by rwa [hqs_eq_qj], by rwa [hqs_eq_qj]⟩
  have hsp0 : ∀ j : Nat, j < blocks.length ->
      (2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks) * natAt qs j =
        broxSpiralCarry (rotBlocks j blocks) := by
    intro j hj
    rcases hus_spec j hj with ⟨uj, hdrop_u, _, _⟩
    have hrj := hrot_all j hj
    rw [hdrop_u] at hrj
    exact hrj.2.2.2.2
  have hpos_rot_all : ∀ (j : Nat) (b : Nat × Nat),
      j < blocks.length -> b ∈ rotBlocks j blocks -> b.1 ≥ 1 ∧ b.2 ≥ 1 := by
    intro j b _ hb
    unfold rotBlocks at hb
    rcases List.mem_append.mp hb with hd | ht
    · exact hpos b (List.mem_of_mem_drop hd)
    · exact hpos b (List.mem_of_mem_take ht)
  refine ⟨hW_ge21, hlt_raw,
          ⟨us, qs, hus_len, hqs_len, hus_hd_fn (by simp [blocks]), hrot_all, ?_,
           m_block_companion_prime_quotient_cascades.1 b0 rest qs hpos hlt_raw hqs_len hsp0,
           ?_, ?_⟩⟩
  · intro pivots b_last tail hblk_eq
    have hsq := m_block_recursive_p_pivot_brox_squeeze.2.2.1 pivots b_last tail qs 1
      (by rwa [hblk_eq]) (by rwa [hblk_eq]) (by rwa [hblk_eq])
      (by rwa [hblk_eq]) (Nat.one_dvd _)
    rw [Nat.one_mul, hblk_eq] at hsq
    exact hsq
  · intro j pivots b_last tail d_mult hj hrot_eq hdvd_qj
    rcases hus_spec j hj with ⟨uj, hdrop_u, _, _⟩
    have hrj := hrot_all j hj
    rw [hdrop_u] at hrj
    have hdm_le : d_mult ≤ natAt qs j := Nat.le_of_dvd hrj.2.2.1 hdvd_qj
    have hpos_r : ∀ b ∈ pivots ++ (b_last :: tail), b.1 ≥ 1 ∧ b.2 ≥ 1 := by
      intro b hb; rw [← hrot_eq] at hb; exact hpos_rot_all j b hj hb
    calc d_mult * (2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks)
        ≤ natAt qs j * (2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks) :=
          Nat.mul_le_mul_right _ hdm_le
      _ = (2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks) * natAt qs j := Nat.mul_comm _ _
      _ = broxSpiralCarry (rotBlocks j blocks) := hrj.2.2.2.2
      _ = broxSpiralCarry (pivots ++ (b_last :: tail)) := by rw [hrot_eq]
      _ ≤ multiPivotCarryUB pivots b_last tail :=
          m_block_recursive_p_pivot_brox_squeeze.1 pivots b_last tail hpos_r
  · intro hge2 j bj ps b_last tail s d_mult hj hrot_eq hs4 hbj_s hd_odd hdvd_qj
    have hw_rot : blockWeightSum (rotBlocks j blocks) = blockWeightSum blocks ∧
        blockStepSum (rotBlocks j blocks) = blockStepSum blocks := by
      unfold rotBlocks
      rcases hwt_app (blocks.drop j) (blocks.take j) with ⟨w1, k1⟩
      rcases hwt_app (blocks.take j) (blocks.drop j) with ⟨w2, k2⟩
      rw [List.take_append_drop j blocks] at w2 k2
      exact ⟨by omega, by omega⟩
    let j1 := (j + 1) % blocks.length
    have hj1 : j1 < blocks.length := Nat.mod_lt (j + 1) (by dsimp [blocks]; omega)
    have h0_eq := hsp0 j hj
    have h1_eq := hsp0 j1 hj1
    rw [← rotBlocks_one_rotBlocks_cf_w17 blocks hge2 j hj] at h1_eq
    have hlt_rot : 3 ^ blockWeightSum ((bj :: ps) ++ (b_last :: tail)) <
        2 ^ blockStepSum ((bj :: ps) ++ (b_last :: tail)) := by
      rwa [← hrot_eq, hw_rot.1, hw_rot.2]
    have hD_rot : 2 ^ blockStepSum ((bj :: ps) ++ (b_last :: tail)) -
        3 ^ blockWeightSum ((bj :: ps) ++ (b_last :: tail)) =
        2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks := by
      rw [← hrot_eq, hw_rot.1, hw_rot.2]
    rw [hrot_eq, ← hD_rot] at h0_eq h1_eq
    have hqj_ge : natAt qs j ≥ henselOddInvModPow2 s (3 ^ bj.1 * d_mult) * d_mult := by
      cases hps : ps with
      | nil =>
        simp only [hps, List.cons_append, List.nil_append] at hlt_rot h0_eq h1_eq
        have hrec := (m_block_two_pivot_telescoping_and_2adic_quotient_boost.1.2
          bj b_last tail hlt_rot).2 (natAt qs j) (natAt qs j1) h0_eq h1_eq
        exact hensel_quotient_boost_cf_w17 s bj.1 bj.2 b_last.1 (natAt qs j) (natAt qs j1) d_mult
          hs4 hbj_s hd_odd hdvd_qj hrec
      | cons b_n ptl =>
        simp only [hps, List.cons_append] at hlt_rot h0_eq h1_eq
        have hrec := (m_block_two_pivot_telescoping_and_2adic_quotient_boost.1.2
          bj b_n (ptl ++ (b_last :: tail)) hlt_rot).2 (natAt qs j) (natAt qs j1) h0_eq h1_eq
        exact hensel_quotient_boost_cf_w17 s bj.1 bj.2 b_n.1 (natAt qs j) (natAt qs j1) d_mult
          hs4 hbj_s hd_odd hdvd_qj hrec
    have hpos_r : ∀ b ∈ (bj :: ps) ++ (b_last :: tail), b.1 ≥ 1 ∧ b.2 ≥ 1 := by
      intro b hb; rw [← hrot_eq] at hb; exact hpos_rot_all j b hj hb
    calc (henselOddInvModPow2 s (3 ^ bj.1 * d_mult) * d_mult) *
          (2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks)
        ≤ natAt qs j * (2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks) :=
          Nat.mul_le_mul_right _ hqj_ge
      _ = (2 ^ blockStepSum ((bj :: ps) ++ (b_last :: tail)) -
            3 ^ blockWeightSum ((bj :: ps) ++ (b_last :: tail))) * natAt qs j := by
            rw [hD_rot, Nat.mul_comm]
      _ = broxSpiralCarry ((bj :: ps) ++ (b_last :: tail)) := h0_eq
      _ ≤ multiPivotCarryUB (bj :: ps) b_last tail :=
          m_block_recursive_p_pivot_brox_squeeze.1 (bj :: ps) b_last tail hpos_r

-- ============================================================================
-- SECTION 2: Front B (Branches P3.2–P3.4) — Asymptotic Rectangular Joint-`Nat.lcm`
--            Exact-Product & Pure-`2^E_2` Factorial Dominance, Rank-3 Order-4
--            `12 × 12` `(T = 4, U = 3)` Two-Base Cone Sign-Flip & Exact `u = 1`
--            Zero-Locus `K = 4 * W`, & All-Rotation Cyclic `p`-Pivot + Multi-Prime
--            Brox Elimination (`W17_H2`)
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Section 2A: Asymptotic Rectangular `(U * T) × (U * T)` Coprime-`W` Exact-Product
--             & Universal Pure-`2^E_2` Super-Factorial Joint-`Nat.lcm` Dominance
-- ----------------------------------------------------------------------------

/-- Tetrahedral prefix sum `∑_{m < U} triNumNat m = U * (U - 1) * (U - 2) / 6`. -/
def tetNumNat : Nat -> Nat
  | 0 => 0
  | m + 1 => tetNumNat m + triNumNat m

/-- Exact 2-adic exponent `v_2(confluentFactorAllU U T u)`:
    `u * (triNumNat U * triNumNat T + tetNumNat U * (T * T))`. -/
def rectConfluentTwoExp (U T u : Nat) : Nat :=
  u * (triNumNat U * triNumNat T + tetNumNat U * (T * T))

private theorem coprime_pow2_sub1_of_coprime_w17 :
    ∀ (fuel a b : Nat), a + b ≤ fuel -> Nat.Coprime a b ->
      Nat.Coprime (2 ^ a - 1) (2 ^ b - 1)
  | 0, a, b, hle, hcop => by
    have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    subst ha0; subst hb0; cases hcop
  | fuel + 1, a, b, hle, hcop => by
    by_cases ha0 : a = 0
    · subst ha0
      have hb1 : b = 1 := by simpa [Nat.coprime_iff_gcd_eq_one] using hcop
      subst hb1; decide
    · by_cases hb0 : b = 0
      · subst hb0
        have ha1 : a = 1 := by simpa [Nat.coprime_iff_gcd_eq_one] using hcop
        subst ha1; decide
      · by_cases hab : a = b
        · subst hab
          have ha1 : a = 1 := by simpa [Nat.coprime_iff_gcd_eq_one, Nat.gcd_self] using hcop
          subst ha1; decide
        · by_cases hlt : a < b
          · let c := b - a
            have hb_eq : b = a + c := by omega
            have hc_pos : c ≥ 1 := by omega
            have hcop_ac : Nat.Coprime a c := by
              rw [Nat.coprime_iff_gcd_eq_one] at hcop ⊢
              have hg_a : Nat.gcd a c ∣ a := Nat.gcd_dvd_left a c
              have hg_b : Nat.gcd a c ∣ b := by
                rw [hb_eq]; exact Nat.dvd_add hg_a (Nat.gcd_dvd_right a c)
              have hg_1 : Nat.gcd a c ∣ 1 := by
                rw [← hcop]; exact Nat.dvd_gcd hg_a hg_b
              exact Nat.eq_one_of_dvd_one hg_1
            have ih := coprime_pow2_sub1_of_coprime_w17 fuel a c (by omega) hcop_ac
            rw [Nat.coprime_iff_gcd_eq_one] at ih ⊢
            let g := Nat.gcd (2 ^ a - 1) (2 ^ b - 1)
            have hg_ma : g ∣ (2 ^ a - 1) := Nat.gcd_dvd_left _ _
            have hg_mb : g ∣ (2 ^ b - 1) := Nat.gcd_dvd_right _ _
            have hdecomp : 2 ^ b - 1 = 2 ^ c * (2 ^ a - 1) + (2 ^ c - 1) := by
              rw [hb_eq, Nat.pow_add 2 a c, Nat.mul_comm (2 ^ a) (2 ^ c),
                  Nat.mul_sub_left_distrib, Nat.mul_one]
              have hp_c : 2 ^ c ≥ 1 := nat_pow_pos_of_pos 2 (by decide) c
              have hp_a : 2 ^ a ≥ 1 := nat_pow_pos_of_pos 2 (by decide) a
              have hle_c : 2 ^ c ≤ 2 ^ c * 2 ^ a := Nat.le_mul_of_pos_right _ hp_a
              omega
            have hg_mc : g ∣ (2 ^ c - 1) := by
              rcases hg_ma with ⟨qa, hqa⟩
              rcases hg_mb with ⟨qb, hqb⟩
              refine ⟨qb - 2 ^ c * qa, ?_⟩
              have h1 : g * qb = 2 ^ c * (g * qa) + (2 ^ c - 1) := by
                rw [← hqa, ← hqb]; exact hdecomp
              have h2 : g * (2 ^ c * qa) ≤ g * qb := by
                rw [show g * (2 ^ c * qa) = 2 ^ c * (g * qa) by ac_rfl]; omega
              rw [Nat.mul_sub_left_distrib]
              have h3 : g * (2 ^ c * qa) = 2 ^ c * (g * qa) := by ac_rfl
              omega
            have hg_1 : g ∣ 1 := by rw [← ih]; exact Nat.dvd_gcd hg_ma hg_mc
            exact Nat.eq_one_of_dvd_one hg_1
          · have hgt : b < a := by omega
            exact (coprime_pow2_sub1_of_coprime_w17 (fuel + 1) b a (by omega) hcop.symm).symm

private theorem pow_dvd_of_dvd_w17 (a b k : Nat) (h : a ∣ b) : a ^ k ∣ b ^ k := by
  induction k with
  | zero => exact ⟨1, by simp⟩
  | succ k' ih =>
    rcases ih with ⟨q1, hq1⟩
    rcases h with ⟨q2, hq2⟩
    rw [Nat.pow_succ, Nat.pow_succ, hq1, hq2]
    exact ⟨q1 * q2, by ac_rfl⟩

private theorem blockNodeDiffProd_two_and_coprime_w17 (u m : Nat) (_hu : u ≥ 1) :
    (2 ^ u) ^ triNumNat m ∣ blockNodeDiffProd (2 ^ u) m m ∧
    (∀ W : Nat, W ≥ 1 ->
      (∀ d : Nat, 1 ≤ d -> d ≤ m -> Nat.Coprime W d) ->
      Nat.Coprime (blockNodeDiffProd 2 m m) (2 ^ W - 1)) := by
  have hstep : ∀ k : Nat, k ≤ m ->
      (2 ^ u) ^ triNumNat k ∣ blockNodeDiffProd (2 ^ u) m k ∧
      (∀ W : Nat, W ≥ 1 ->
        (∀ d : Nat, 1 ≤ d -> d ≤ m -> Nat.Coprime W d) ->
        Nat.Coprime (blockNodeDiffProd 2 m k) (2 ^ W - 1)) := by
    intro k hk; induction k with
    | zero =>
      simp only [triNumNat, Nat.pow_zero, blockNodeDiffProd]
      exact ⟨⟨1, rfl⟩, fun _ _ _ => Nat.coprime_one_left _⟩
    | succ k' ih =>
      rcases ih (Nat.le_of_lt hk) with ⟨ih_dvd, ih_cop⟩
      simp only [triNumNat, blockNodeDiffProd]
      have hfac_u : (2 ^ u) ^ m - (2 ^ u) ^ k' =
          (2 ^ u) ^ k' * ((2 ^ u) ^ (m - k') - 1) := by
        conv => lhs; lhs; rw [show m = k' + (m - k') by omega, Nat.pow_add]
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      refine ⟨?_, ?_⟩
      · rcases ih_dvd with ⟨q, hq⟩
        rw [Nat.pow_add, hq, hfac_u]
        exact ⟨q * ((2 ^ u) ^ (m - k') - 1), by ac_rfl⟩
      · intro W hW hcop_all
        have hfac_2 : 2 ^ m - 2 ^ k' = 2 ^ k' * (2 ^ (m - k') - 1) := by
          conv => lhs; lhs; rw [show m = k' + (m - k') by omega, Nat.pow_add]
          rw [Nat.mul_sub_left_distrib, Nat.mul_one]
        rw [hfac_2]
        have hodd_W : (2 ^ W - 1) % 2 = 1 := by
          rw [show W = (W - 1) + 1 by omega, Nat.pow_succ]
          have hp := nat_pow_pos_of_pos 2 (by decide) (W - 1); omega
        have hc2 : Nat.Coprime 2 (2 ^ W - 1) := by
          rw [Nat.coprime_iff_gcd_eq_one]
          have hg2 : Nat.gcd 2 (2 ^ W - 1) ≤ 2 := Nat.le_of_dvd (by decide) (Nat.gcd_dvd_left _ _)
          have hgp : Nat.gcd 2 (2 ^ W - 1) ≥ 1 := Nat.gcd_pos_of_pos_left _ (by decide)
          have hgd := Nat.gcd_dvd_right 2 (2 ^ W - 1)
          by_cases h1 : Nat.gcd 2 (2 ^ W - 1) = 1
          · exact h1
          · have he2 : Nat.gcd 2 (2 ^ W - 1) = 2 := by omega
            rw [he2] at hgd; rcases hgd with ⟨q, hq⟩; omega
        have hc_diff : Nat.Coprime (2 ^ (m - k') - 1) (2 ^ W - 1) :=
          (coprime_pow2_sub1_of_coprime_w17 (W + (m - k')) W (m - k') (by omega)
            (hcop_all (m - k') (by omega) (by omega))).symm
        exact (ih_cop W hW hcop_all).mul_left ((hc2.pow_left k').mul_left hc_diff)
  exact hstep m (Nat.le_refl m)

private theorem confluentFactorAllU_two_dvd_and_coprime_w17 (U T u : Nat) (hu : u ≥ 1) :
    2 ^ rectConfluentTwoExp U T u ∣ confluentFactorAllU U T u ∧
    (∀ W : Nat, W ≥ 1 ->
      (∀ d : Nat, 1 ≤ d -> d < U -> Nat.Coprime W d) ->
      Nat.Coprime (confluentFactorAllU U T 1) (2 ^ W - 1)) := by
  unfold confluentFactorAllU rectConfluentTwoExp
  induction U with
  | zero =>
    simp only [triNumNat, tetNumNat, Nat.zero_mul, Nat.add_zero, Nat.mul_zero,
               Nat.pow_zero, confluentFactorAllUAux]
    exact ⟨⟨1, rfl⟩, fun _ _ _ => Nat.coprime_one_left _⟩
  | succ m ih =>
    rcases ih with ⟨ih_dvd, ih_cop⟩
    rcases blockNodeDiffProd_two_and_coprime_w17 u m hu with ⟨hd_m, _⟩
    rcases blockNodeDiffProd_two_and_coprime_w17 1 m (by decide) with ⟨_, hcop_m⟩
    simp only [triNumNat, tetNumNat, confluentFactorAllUAux, confluentBlockFactor]
    refine ⟨?_, ?_⟩
    · have hexp_split :
          u * ((triNumNat m + m) * triNumNat T + (tetNumNat m + triNumNat m) * (T * T)) =
          u * (triNumNat m * triNumNat T + tetNumNat m * (T * T)) +
            u * (m * triNumNat T) + u * (triNumNat m * (T * T)) := by
        simp only [Nat.add_mul, Nat.mul_add]; omega
      rw [hexp_split, Nat.pow_add, Nat.pow_add]
      rcases ih_dvd with ⟨q1, hq1⟩
      have hd_pow := pow_dvd_of_dvd_w17 _ _ (T * T) hd_m
      rw [pow_pow_eq_mul_w5 (2 ^ u) (triNumNat m) (T * T),
          pow_pow_eq_mul_w5 2 u (triNumNat m * (T * T))] at hd_pow
      rcases hd_pow with ⟨q2, hq2⟩
      have hp_m : (2 ^ u) ^ (m * triNumNat T) = 2 ^ (u * (m * triNumNat T)) :=
        pow_pow_eq_mul_w5 2 u (m * triNumNat T)
      rw [hq1, hp_m, hq2]
      exact ⟨q1 * q2, by ac_rfl⟩
    · intro W hW hcop_all
      have hc_prev := ih_cop W hW (fun d hd1 hdm => hcop_all d hd1 (by omega))
      have hc_cur := hcop_m W hW (fun d hd1 hdm => hcop_all d hd1 (by omega))
      have hodd_W : (2 ^ W - 1) % 2 = 1 := by
        rw [show W = (W - 1) + 1 by omega, Nat.pow_succ]
        have hp := nat_pow_pos_of_pos 2 (by decide) (W - 1); omega
      have hc2 : Nat.Coprime 2 (2 ^ W - 1) := by
        rw [Nat.coprime_iff_gcd_eq_one]
        have hg2 : Nat.gcd 2 (2 ^ W - 1) ≤ 2 := Nat.le_of_dvd (by decide) (Nat.gcd_dvd_left _ _)
        have hgp : Nat.gcd 2 (2 ^ W - 1) ≥ 1 := Nat.gcd_pos_of_pos_left _ (by decide)
        have hgd := Nat.gcd_dvd_right 2 (2 ^ W - 1)
        by_cases h1 : Nat.gcd 2 (2 ^ W - 1) = 1
        · exact h1
        · have he2 : Nat.gcd 2 (2 ^ W - 1) = 2 := by omega
          rw [he2] at hgd; rcases hgd with ⟨q, hq⟩; omega
      have hp1 : (2 ^ 1 : Nat) = 2 := rfl
      rw [hp1]
      exact hc_prev.mul_left ((hc2.pow_left (m * triNumNat T)).mul_left (hc_cur.pow_left (T * T)))

private theorem pure_two_exp_gt_natFact_w17 (U T u : Nat) (hT : T ≥ 1) (hu : u ≥ 1)
    (hdom : (U ≥ 5 ∧ U > T) ∨ (U = 4 ∧ 2 ≤ T ∧ T < 4) ∨ (U = 4 ∧ T = 1 ∧ u ≥ 2)) :
    2 ^ rectConfluentTwoExp U T u > natFact (U * T) := by
  have hpow2_gt_self : ∀ n : Nat, n < 2 ^ n := by
    intro n; induction n with
    | zero => decide
    | succ n' ih => rw [Nat.pow_succ]; omega
  have hfact_step : ∀ a k : Nat, natFact (a + k) ≤ natFact a * (a + k) ^ k := by
    intro a k; induction k with
    | zero => simp
    | succ k' ih =>
      rw [Nat.add_succ, natFact, Nat.pow_succ]
      have h1 : natFact (a + k') ≤ natFact a * (a + k' + 1) ^ k' :=
        Nat.le_trans ih (Nat.mul_le_mul_left _
          (pow_mono_base_w17c (a + k') (a + k' + 1) (Nat.le_succ _) k'))
      calc (a + k' + 1) * natFact (a + k')
          ≤ (a + k' + 1) * (natFact a * (a + k' + 1) ^ k') := Nat.mul_le_mul_left _ h1
        _ = natFact a * ((a + k' + 1) ^ k' * (a + k' + 1)) := by ac_rfl
  rcases hdom with ⟨hU5, _⟩ | ⟨rfl, hT2, hT4⟩ | ⟨rfl, rfl, hu2⟩
  · -- Case 1: `U ≥ 5`, `T ≥ 1`, `u ≥ 1`:
    have hu1_le : rectConfluentTwoExp U T 1 ≤ rectConfluentTwoExp U T u := by
      unfold rectConfluentTwoExp
      simpa [Nat.one_mul] using Nat.mul_le_mul_right
        (triNumNat U * triNumNat T + tetNumNat U * (T * T)) hu
    apply Nat.lt_of_lt_of_le _ (nat_pow_mono_exp_pos 2 _ _ (by decide) hu1_le)
    -- Step 1a: Base `U = 5` for all `T ≥ 1`:
    have hbase5 : ∀ t : Nat, t ≥ 1 -> natFact (5 * t) < 2 ^ (10 * (t * t)) := by
      intro t ht1
      have h5t_le : ∀ q : Nat, q ≥ 1 -> 5 * (q + 1) ≤ 2 ^ (4 * q + 2) := by
        intro q hq1; induction q with
        | zero => omega
        | succ q' ihq =>
          by_cases hq0 : q' = 0
          · subst hq0; decide
          · have ih1 := ihq (by omega)
            rw [show 4 * (q' + 1) + 2 = (4 * q' + 2) + 4 by omega, Nat.pow_add]
            omega
      induction t with
      | zero => omega
      | succ t' iht =>
        by_cases ht0 : t' = 0
        · subst ht0; decide
        · have ih_prev := iht (by omega)
          have hf_st := hfact_step (5 * t') 5
          rw [show 5 * t' + 5 = 5 * (t' + 1) by omega] at hf_st
          have hpow5 : (5 * (t' + 1)) ^ 5 ≤ 2 ^ (20 * t' + 10) := by
            have hb := pow_mono_base_w17c _ _ (h5t_le t' (by omega)) 5
            rwa [pow_pow_eq_mul_w5 2 (4 * t' + 2) 5,
                 show (4 * t' + 2) * 5 = 20 * t' + 10 by omega] at hb
          have hexp_eq : 10 * ((t' + 1) * (t' + 1)) = 10 * (t' * t') + (20 * t' + 10) := by
            simp only [Nat.add_mul, Nat.mul_add]; omega
          rw [hexp_eq, Nat.pow_add]
          have hp_pos : 2 ^ (20 * t' + 10) ≥ 1 := nat_pow_pos_of_pos 2 (by decide) _
          calc natFact (5 * (t' + 1))
              ≤ natFact (5 * t') * (5 * (t' + 1)) ^ 5 := hf_st
            _ ≤ natFact (5 * t') * 2 ^ (20 * t' + 10) := Nat.mul_le_mul_left _ hpow5
            _ < 2 ^ (10 * (t' * t')) * 2 ^ (20 * t' + 10) :=
                  Nat.mul_lt_mul_of_pos_right ih_prev hp_pos
    -- Step 1b: Induction on `U ≥ 5`:
    have htri_ge : ∀ m : Nat, m ≥ 5 -> triNumNat m ≥ m + 2 := by
      intro m hm5; induction m with
      | zero => omega
      | succ m' ih =>
        by_cases hm4 : m' = 4
        · subst hm4; decide
        · have ih1 := ih (by omega); simp only [triNumNat]; omega
    have hall_U : ∀ m : Nat, m ≥ 5 -> natFact (m * T) < 2 ^ rectConfluentTwoExp m T 1 := by
      intro m hm5; induction m with
      | zero => omega
      | succ m' ihm =>
        by_cases hm4 : m' = 4
        · subst hm4
          have htet5 : 10 * (T * T) ≤ rectConfluentTwoExp 5 T 1 := by
            unfold rectConfluentTwoExp
            have ht5 : tetNumNat 5 = 10 := by decide
            rw [Nat.one_mul, ht5]; omega
          exact Nat.lt_of_lt_of_le (hbase5 T hT) (nat_pow_mono_exp_pos 2 _ _ (by decide) htet5)
        · have ih_prev := ihm (by omega)
          have hf_st := hfact_step (m' * T) T
          rw [show m' * T + T = (m' + 1) * T by rw [Nat.add_mul, Nat.one_mul]] at hf_st
          have htm : triNumNat m' ≥ m' + 2 := htri_ge m' (by omega)
          have hexp_ge : (m' + 1) + T ≤ triNumNat m' * T := by
            have h1 : (m' + 2) + (m' + 2) * (T - 1) = (m' + 2) * T := by
              conv => lhs; lhs; rw [← Nat.mul_one (m' + 2)]
              rw [← Nat.mul_add, show 1 + (T - 1) = T by omega]
            have h2 : (m' + 2) * T ≤ triNumNat m' * T := Nat.mul_le_mul_right T htm
            have h3 : T - 1 ≤ (m' + 2) * (T - 1) := by
              simpa using Nat.mul_le_mul_right (T - 1) (by omega : 1 ≤ m' + 2)
            omega
          have hbase_le : (m' + 1) * T ≤ 2 ^ (triNumNat m' * T) := by
            have h1 : (m' + 1) * T ≤ 2 ^ (m' + 1) * 2 ^ T :=
              Nat.mul_le_mul (Nat.le_of_lt (hpow2_gt_self (m' + 1))) (Nat.le_of_lt (hpow2_gt_self T))
            rw [← Nat.pow_add] at h1
            exact Nat.le_trans h1 (nat_pow_mono_exp_pos 2 _ _ (by decide) hexp_ge)
          have hpowT : ((m' + 1) * T) ^ T ≤ 2 ^ (triNumNat m' * (T * T)) := by
            have hb := pow_mono_base_w17c _ _ hbase_le T
            rwa [pow_pow_eq_mul_w5 2 (triNumNat m' * T) T, Nat.mul_assoc] at hb
          have hexp_step : rectConfluentTwoExp m' T 1 + triNumNat m' * (T * T) ≤
              rectConfluentTwoExp (m' + 1) T 1 := by
            unfold rectConfluentTwoExp; simp only [Nat.one_mul, triNumNat, tetNumNat, Nat.add_mul]; omega
          have hp_pos : 2 ^ (triNumNat m' * (T * T)) ≥ 1 := nat_pow_pos_of_pos 2 (by decide) _
          have hlt_mid : natFact ((m' + 1) * T) <
              2 ^ (rectConfluentTwoExp m' T 1 + triNumNat m' * (T * T)) := by
            rw [Nat.pow_add]
            calc natFact ((m' + 1) * T)
                ≤ natFact (m' * T) * ((m' + 1) * T) ^ T := hf_st
              _ ≤ natFact (m' * T) * 2 ^ (triNumNat m' * (T * T)) := Nat.mul_le_mul_left _ hpowT
              _ < 2 ^ rectConfluentTwoExp m' T 1 * 2 ^ (triNumNat m' * (T * T)) :=
                    Nat.mul_lt_mul_of_pos_right ih_prev hp_pos
          exact Nat.lt_of_lt_of_le hlt_mid (nat_pow_mono_exp_pos 2 _ _ (by decide) hexp_step)
    exact hall_U U hU5
  · -- Case 2: `U = 4`, `T ∈ {2, 3}`, `u ≥ 1`:
    rcases (by omega : T = 2 ∨ T = 3) with rfl | rfl
    · have hexp : 22 ≤ rectConfluentTwoExp 4 2 u := by
        have h1 : rectConfluentTwoExp 4 2 1 = 22 := by decide
        unfold rectConfluentTwoExp at h1 ⊢
        rw [Nat.one_mul] at h1; rw [h1]; simpa using Nat.mul_le_mul_right 22 hu
      exact Nat.lt_of_lt_of_le (by decide : natFact 8 < 2 ^ 22)
        (nat_pow_mono_exp_pos 2 22 _ (by decide) hexp)
    · have hexp : 54 ≤ rectConfluentTwoExp 4 3 u := by
        have h1 : rectConfluentTwoExp 4 3 1 = 54 := by decide
        unfold rectConfluentTwoExp at h1 ⊢
        rw [Nat.one_mul] at h1; rw [h1]; simpa using Nat.mul_le_mul_right 54 hu
      exact Nat.lt_of_lt_of_le (by decide : natFact 12 < 2 ^ 54)
        (nat_pow_mono_exp_pos 2 54 _ (by decide) hexp)
  · -- Case 3: `U = 4`, `T = 1`, `u ≥ 2`:
    have hexp : 8 ≤ rectConfluentTwoExp 4 1 u := by
      have h1 : rectConfluentTwoExp 4 1 1 = 4 := by decide
      unfold rectConfluentTwoExp at h1 ⊢
      rw [Nat.one_mul] at h1; rw [h1]; omega
    exact Nat.lt_of_lt_of_le (by decide : natFact 4 < 2 ^ 8)
      (nat_pow_mono_exp_pos 2 8 _ (by decide) hexp)

-- ----------------------------------------------------------------------------
-- O(N^3) Upper-Lower Triangular Multiplier Determinant Engine (`checkULDet12Bool`)
-- ----------------------------------------------------------------------------

private theorem intPowNat_ne_zero_w17 (p : Int) (hp : p ≠ 0) (k : Nat) :
    intPowNat p k ≠ 0 := by
  induction k with
  | zero => simp [intPowNat]
  | succ _ ih => exact Int.mul_ne_zero hp ih

private def intAt2DW17 (tbl : List (List Int)) (i j : Nat) : Int :=
  match tbl.drop i with
  | row :: _ =>
    match row.drop j with
    | x :: _ => x
    | [] => 0
  | [] => 0

private def intDiagProdPrefixW17 (N : Nat) (U : Fin N -> Fin N -> Int) : Nat -> Int
  | 0 => 1
  | k + 1 =>
    if h : k < N then intDiagProdPrefixW17 N U k * U ⟨k, h⟩ ⟨k, h⟩
    else intDiagProdPrefixW17 N U k

private theorem intDet_mul_upper_tri_w17 (N : Nat) (A U : Fin N -> Fin N -> Int)
    (hupper : ∀ r c : Fin N, c.val < r.val -> U r c = 0) :
    intDet N (fun i j => intSumPrefix N (fun r => A i r * U r j) N) =
      intDiagProdPrefixW17 N U N * intDet N A := by
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
      intDet N (M_stage 0) = intDiagProdPrefixW17 N U k * intDet N (M_stage k) := by
    intro k hk; induction k with
    | zero => simp [intDiagProdPrefixW17]
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
      simp only [intDiagProdPrefixW17, hk'_lt, dite_true]
      exact (Int.mul_assoc (intDiagProdPrefixW17 N U k') (U jk jk) _).symm
  rw [h0_eq, hstep N (Nat.le_refl N), hN_eq]

private theorem intDet_lower_tri_w17 :
    ∀ (N : Nat) (L_mat : Fin N -> Fin N -> Int),
      (∀ r c : Fin N, r.val < c.val -> L_mat r c = 0) ->
      intDet N L_mat = intDiagProdPrefixW17 N L_mat N
  | 0, _, _ => rfl
  | N + 1, L_mat, hlow => by
    let z0 : Fin (N + 1) := ⟨0, Nat.zero_lt_succ N⟩
    rw [intDet_succ_single_row0 N L_mat z0
        (fun j hj => hlow z0 j (by
          have hv : j.val ≠ 0 := fun h => hj (Fin.ext h)
          dsimp [z0]; omega))]
    have hev : z0.val % 2 = 0 := rfl
    rw [ite_true_of_w10 hev, Int.one_mul]
    have hsub_low : ∀ r c : Fin N, r.val < c.val -> intSubMat L_mat z0 r c = 0 := by
      intro r c hrc
      simp only [intSubMat, skipFinIdx, z0, Nat.not_lt_zero, ite_false]
      exact hlow ⟨r.val + 1, by omega⟩ ⟨c.val + 1, by omega⟩ (by dsimp; omega)
    rw [intDet_lower_tri_w17 N (intSubMat L_mat z0) hsub_low]
    have hprod_shift : ∀ k : Nat, k ≤ N ->
        L_mat z0 z0 * intDiagProdPrefixW17 N (intSubMat L_mat z0) k =
          intDiagProdPrefixW17 (N + 1) L_mat (k + 1) := by
      intro k hk; induction k with
      | zero =>
        simp only [intDiagProdPrefixW17, Nat.zero_lt_succ, dite_true, Int.one_mul, Int.mul_one]
        rfl
      | succ k' ih =>
        have hk'_N : k' < N := hk
        have hk1_N1 : k' + 1 < N + 1 := Nat.succ_lt_succ hk
        simp only [intDiagProdPrefixW17, hk'_N, hk1_N1, dite_true, ← Int.mul_assoc, ih (Nat.le_of_lt hk)]
        simp only [intSubMat, skipFinIdx, z0, Nat.not_lt_zero, ite_false]
    exact hprod_shift N (Nat.le_refl N)

private def allFin12LoopW17 (p : Fin 12 -> Bool) : Nat -> Bool
  | 0 => true
  | k + 1 => (if h : k < 12 then p ⟨k, h⟩ else true) && allFin12LoopW17 p k

private theorem allFin12LoopW17_spec (p : Fin 12 -> Bool) (h : allFin12LoopW17 p 12 = true) :
    ∀ x : Fin 12, p x = true := by
  have hst : ∀ k : Nat, k ≤ 12 -> allFin12LoopW17 p k = true -> ∀ x : Fin 12, x.val < k -> p x = true := by
    intro k hk; induction k with
    | zero => intros _ _ hlt; omega
    | succ k' ih =>
      intro ha x hx_lt
      unfold allFin12LoopW17 at ha
      rcases bool_and_split ha with ⟨hcur, hprev⟩
      by_cases hxk : x.val = k'
      · have hk_lt : k' < 12 := hk
        simp only [hk_lt, dite_true] at hcur
        rwa [show x = ⟨k', hk_lt⟩ from Fin.ext hxk]
      · exact ih (Nat.le_of_lt hk) hprev x (by omega)
  intro x; exact hst 12 (Nat.le_refl _) h x x.isLt

private def checkULDet12Bool (A : Fin 12 -> Fin 12 -> Int) (uTbl : List (List Int)) (expDet : Int) : Bool :=
  let U (i j : Fin 12) : Int := intAt2DW17 uTbl i.val j.val
  let prodMat (i j : Fin 12) : Int := intSumPrefix 12 (fun r => A i r * U r j) 12
  let upperOk := allFin12LoopW17 (fun r =>
    allFin12LoopW17 (fun c => if c.val < r.val then U r c == 0 else true) 12) 12
  let lowerOk := allFin12LoopW17 (fun r =>
    allFin12LoopW17 (fun c => if r.val < c.val then prodMat r c == 0 else true) 12) 12
  let uDiag := intDiagProdPrefixW17 12 U 12
  let lDiag := intDiagProdPrefixW17 12 prodMat 12
  upperOk && lowerOk && (uDiag != 0) && (lDiag == uDiag * expDet)

private theorem checkULDet12Bool_sound_w17 (A : Fin 12 -> Fin 12 -> Int)
    (uTbl : List (List Int)) (expDet : Int)
    (h : checkULDet12Bool A uTbl expDet = true) :
    intDet 12 A = expDet := by
  let U (i j : Fin 12) : Int := intAt2DW17 uTbl i.val j.val
  let prodMat (i j : Fin 12) : Int := intSumPrefix 12 (fun r => A i r * U r j) 12
  unfold checkULDet12Bool at h
  rcases bool_and_split h with ⟨hb1, hl_eq_b⟩
  rcases bool_and_split hb1 with ⟨hb2, hu_nz_b⟩
  rcases bool_and_split hb2 with ⟨hup_b, hlo_b⟩
  have hupper : ∀ r c : Fin 12, c.val < r.val -> U r c = 0 := by
    intro r c hlt
    have hc := allFin12LoopW17_spec _ (allFin12LoopW17_spec _ hup_b r) c
    dsimp only at hc; rw [ite_true_of_w10 hlt] at hc
    exact beq_iff_eq.mp hc
  have hlower : ∀ r c : Fin 12, r.val < c.val -> prodMat r c = 0 := by
    intro r c hlt
    have hc := allFin12LoopW17_spec _ (allFin12LoopW17_spec _ hlo_b r) c
    dsimp only at hc; rw [ite_true_of_w10 hlt] at hc
    exact beq_iff_eq.mp hc
  have hu_nz : intDiagProdPrefixW17 12 U 12 ≠ 0 := bne_iff_ne.mp hu_nz_b
  have hl_eq : intDiagProdPrefixW17 12 prodMat 12 = intDiagProdPrefixW17 12 U 12 * expDet :=
    beq_iff_eq.mp hl_eq_b
  have hmul_det := intDet_mul_upper_tri_w17 12 A U hupper
  have hlow_det := intDet_lower_tri_w17 12 prodMat hlower
  dsimp only [prodMat] at hlow_det
  rw [hlow_det, hl_eq] at hmul_det
  exact (Int.eq_of_mul_eq_mul_left hu_nz hmul_det).symm

private def fastBinom3W17 (x t : Nat) : Nat :=
  match t with
  | 0 => 1
  | 1 => x
  | 2 => (x * (x - 1)) / 2
  | 3 => (x * (x - 1) * (x - 2)) / 6
  | _ => laurentInterpBinom x t

private theorem fastBinom3W17_eq_laurentInterpBinom (x t : Nat) (ht : t < 4) :
    fastBinom3W17 x t = laurentInterpBinom x t := by
  have hst : ∀ n : Nat,
      laurentInterpBinom n 0 = 1 ∧
      laurentInterpBinom n 1 = n ∧
      2 * laurentInterpBinom n 2 + n = n * n ∧
      6 * laurentInterpBinom n 3 + 3 * (n * n) = n * n * n + 2 * n := by
    intro n; induction n with
    | zero => decide
    | succ n' ih =>
      rcases ih with ⟨h0, h1, h2, h3⟩
      refine ⟨rfl, ?_, ?_, ?_⟩
      · simp [laurentInterpBinom, h0, h1]; omega
      · simp only [laurentInterpBinom, h1]
        change 2 * (n' + laurentInterpBinom n' 2) + (n' + 1) = (n' + 1) * (n' + 1)
        rw [Nat.mul_add 2 n' (laurentInterpBinom n' 2),
            show (n' + 1) * (n' + 1) = n' * n' + 2 * n' + 1 by simp only [Nat.add_mul, Nat.mul_add]; omega]
        omega
      · simp only [laurentInterpBinom]
        change 6 * (laurentInterpBinom n' 2 + laurentInterpBinom n' 3) + 3 * ((n' + 1) * (n' + 1)) =
          (n' + 1) * (n' + 1) * (n' + 1) + 2 * (n' + 1)
        have hsq : (n' + 1) * (n' + 1) = n' * n' + 2 * n' + 1 := by
          simp only [Nat.add_mul, Nat.mul_add]; omega
        have hcub : (n' + 1) * (n' + 1) * (n' + 1) = n' * n' * n' + 3 * (n' * n') + 3 * n' + 1 := by
          rw [hsq]
          simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul, Nat.mul_assoc 2 n' n']
          generalize n' * n' * n' = X3; generalize n' * n' = X2; omega
        rw [Nat.mul_add 6 (laurentInterpBinom n' 2) (laurentInterpBinom n' 3),
            show 6 * laurentInterpBinom n' 2 = 3 * (2 * laurentInterpBinom n' 2) from Nat.mul_assoc 3 2 _,
            hcub, hsq, Nat.mul_add 3 (n' * n' + 2 * n') 1, Nat.mul_add 3 (n' * n') (2 * n')]
        generalize 6 * laurentInterpBinom n' 3 = C3 at h3 ⊢
        generalize 2 * laurentInterpBinom n' 2 = C2 at h2 ⊢
        generalize n' * n' * n' = X3 at h3 ⊢
        generalize n' * n' = X2 at h2 h3 ⊢
        omega
  rcases hst x with ⟨hb0, hb1, hb2, hb3⟩
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl
  · exact hb0.symm
  · exact hb1.symm
  · change (x * (x - 1)) / 2 = laurentInterpBinom x 2
    have hmul : x * (x - 1) = 2 * laurentInterpBinom x 2 := by
      cases x with
      | zero => exact hb2.symm
      | succ m =>
        have h1 : (m + 1) * m = (m + 1) * (m + 1) - (m + 1) := by
          simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
          generalize m * m = M2; omega
        simp only [Nat.add_sub_cancel]
        generalize laurentInterpBinom (m + 1) 2 = C2 at hb2 ⊢
        generalize (m + 1) * (m + 1) = X2 at hb2 h1
        generalize (m + 1) * m = P2 at h1 ⊢
        omega
    generalize laurentInterpBinom x 2 = C2 at hmul ⊢
    generalize x * (x - 1) = P2 at hmul ⊢
    omega
  · change (x * (x - 1) * (x - 2)) / 6 = laurentInterpBinom x 3
    have hmul3 : x * (x - 1) * (x - 2) = 6 * laurentInterpBinom x 3 := by
      cases x with
      | zero => exact hb3.symm
      | succ m =>
        cases m with
        | zero => simp at hb3 ⊢; omega
        | succ q =>
          have h21 : (q + 2) * (q + 1) = q * q + 3 * q + 2 := by
            simp only [Nat.add_mul, Nat.mul_add]; omega
          have h22 : (q + 2) * (q + 2) = q * q + 4 * q + 4 := by
            simp only [Nat.add_mul, Nat.mul_add]; omega
          have hp1 : (q + 2) * (q + 1) * q = q * q * q + 3 * (q * q) + 2 * q := by
            rw [h21]; simp only [Nat.add_mul, Nat.mul_assoc 3 q q]
          have hp2 : (q + 2) * (q + 2) * (q + 2) = q * q * q + 6 * (q * q) + 12 * q + 8 := by
            rw [h22]; simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc 4 q q]
            generalize q * q * q = Q3; generalize q * q = Q2; omega
          have hq3 : (q + 2) * (q + 1) * q + 3 * ((q + 2) * (q + 2)) =
              (q + 2) * (q + 2) * (q + 2) + 2 * (q + 2) := by
            rw [hp1, hp2, h22]
            generalize q * q * q = Q3; generalize q * q = Q2; omega
          simp only [Nat.add_sub_cancel]
          change (q + 2) * (q + 1) * q = 6 * laurentInterpBinom (q + 2) 3
          generalize (q + 2) * (q + 1) * q = P3 at hq3 ⊢
          generalize laurentInterpBinom (q + 2) 3 = C3 at hb3 ⊢
          generalize (q + 2) * (q + 2) * (q + 2) = X3 at hb3 hq3
          generalize (q + 2) * (q + 2) = X2 at hb3 hq3
          omega
    generalize laurentInterpBinom x 3 = C3 at hmul3 ⊢
    generalize x * (x - 1) * (x - 2) = P3 at hmul3 ⊢
    omega

private def fastM0_12_582Fn (i j : Fin 12) : Int :=
  let r := i.val % 4; let s := i.val / 4
  let t := j.val % 3; let kc := (j.val / 3) * 2
  let x := r * 5 + s * 8
  ((fastBinom3W17 x t * 2 ^ (x * kc) : Nat) : Int)

private def uM0_12_582Tbl : List (List Int) :=
  [[1, 0, 0, -25, 25600, -10217062400, 61362281947184758784, -8100091611303186307871670272, 20676727674139987444498432, -921545600120370440253692649370885363954914600943616, 11523526180800243976828481409233145268231622275492202122005446656, -597126162812850162618928105810739284472929586040211583316296977978579414442573824],
   [0, 1, -2, 2087943, -710938624, 10435688398848, -50975813365532055306240, 6595451634473669759085712506880, -16611965177084306099074498560, 706983345233650752871990512452299505822049000971304960, -8818275964598357570686989851674477521980042080006006235131658895360, 456322095801015044153676431109288285204478170812635496345109557141649711158463037440],
   [0, 0, 1, -1046529, 357215232, -5579882102784, 27490084852853794406400, -3559987066267803428556531302400, 8971966823257515045892915200, -382655341416249235762228375648838493983219596551782400, 4773466748058226066476532740430449540889656577223556947234940518400, -247030000935223439075723391570208656034941517558222065700954774169589855607691673600],
   [0, 0, 0, 25, -25600, 10217062400, -61362281951485112500, 8100091614851910195968000000, -20676727700967993344000000, 921545603971049151069134468824279461877206456729600, -11523526231658189604760823960311598477231712650393147174761267200, 597126165529189586444828449750063312876430758583793475588163508791904474752876544],
   [0, 0, 0, 0, 1705, -1595592018, 10176810733254288750, -1350489732070623052937600000, 3459565429791530188800000, -156014725418875116038339285769440562839633657856000, 1952134295777851645570854156756693564940410362778392922685440000, -101190519371922111615247510842383613354941600943958540015403337624758088514928640],
   [0, 0, 0, 0, 0, 130640169, -913422141407593125, 122141493602265604473600000, -314505948162866380800000, 14423144877198986718712790950047519781988597760000, -180632340784433059498056012280880324911327852410703215329280000, 9367809900320100102831155546246292061424661948091653174038322666394397284761600],
   [0, 0, 0, 0, 0, 0, 4300353716, -3548723888096329728, 26828005899501568, -3850678710815446930701822033719200106743884, 50857945627937134213458895882023436399297674532842553344, -2716339423827180538144928738391079788119557738594771658080257532501426176],
   [0, 0, 0, 0, 0, 0, 0, 195147270691204315, -2568914751102810, 423993022499934832728842009967277444540050, -5636797012566926023065871157108462662799314688180812800, 302197670532256275679682922719240671489176230561400571311367196029747200],
   [0, 0, 0, 0, 0, 0, 0, 0, 127499317034925, -24746430428963083921920311575790360826075, 331623634122320936417412988899157596244785429024307200, -17860865669862317558948298795751837721206705779857479897187572993228800],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 5111248427935796908250957900, -4791662380442673023346024396729480086732800, 1280194205604709987578615575975846322905127266932472191123456],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 205174494965252332427939721403864161193875, -101334369363249288830788538105287565259435108605405094688950],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4168144096192723730396294226926795766923174242235318019675]]

private theorem m0_12_582_ul_cert :
    checkULDet12Bool fastM0_12_582Fn uM0_12_582Tbl (46558461071235227007405710911151890386680280679811809367547602757305367832327345725373300455850243437009644501991692800180852521887506232429176648342956794713182761728031058778186934118069468410798496613128453583011840000000000000000000000) = true ∧
    ((46558461071235227007405710911151890386680280679811809367547602757305367832327345725373300455850243437009644501991692800180852521887506232429176648342956794713182761728031058778186934118069468410798496613128453583011840000000000000000000000 : Int) % ((confluentFactorAllU 4 3 2 * (2 ^ (5 * 2) - 1) ^ (3 * (4 - 3)) : Nat) : Int) ≠ 0) := by
  decide

/--
  Theorem W17.2a (`laurent_rect_coprime_exact_product_and_factorial_dominance`,
  `zero custom axioms`):
  Universal Rectangular `(U * T) × (U * T)` Pure-`2^E_2` (`rectConfluentTwoExp U T u`) Divisibility,
  Unconditional Coprimality to `(2^(W * u) - 1)^(T * (U - T))`, Super-Factorial Joint-`Nat.lcm`
  Dominance Across ALL `(U ≥ 5 ∧ U > T) ∨ (U = 4 ∧ T ≥ 2) ∨ (U = 4 ∧ T = 1 ∧ u ≥ 2)` AND Coprime-`W`
  Exact `Nat.lcm = colFac * rowFac > (U * T)! * rowFac` Product Law Across `∀ U ≥ 4, 1 ≤ T < U`,
  `(U = 4, T = 1, u = 1, W = 6)` Sharpness, & `12 × 12` `(U = 4, T = 3, W = 5, K = 8, u = 2)`
  Overlap `gcd = 27` Certificate (`Branches P3.2–P3.3`, witness
  `LAURENT_12X12_T4U3_CONE_FLIP_AND_RECT_U2_OVERLAP`, `W17_H2`).
-/
theorem laurent_rect_coprime_exact_product_and_factorial_dominance :
    (∀ (U T W u : Nat), T ≥ 1 -> U > T -> W ≥ 1 -> u ≥ 1 ->
      let colFac := confluentFactorAllU U T u
      let rowFac := (2 ^ (W * u) - 1) ^ (T * (U - T))
      2 ^ rectConfluentTwoExp U T u ∣ colFac ∧
      Nat.Coprime (2 ^ rectConfluentTwoExp U T u) rowFac ∧
      2 ^ rectConfluentTwoExp U T u * rowFac ∣ Nat.lcm colFac rowFac ∧
      2 ^ (rectConfluentTwoExp U T u + (W * u - 1) * (T * (U - T))) ≤ Nat.lcm colFac rowFac) ∧
    (∀ (U T W u : Nat), T ≥ 1 -> U > T -> W ≥ 1 -> u ≥ 1 ->
      ((U ≥ 5) ∨ (U = 4 ∧ T ≥ 2) ∨ (U = 4 ∧ T = 1 ∧ u ≥ 2)) ->
      let colFac := confluentFactorAllU U T u
      let rowFac := (2 ^ (W * u) - 1) ^ (T * (U - T))
      2 ^ rectConfluentTwoExp U T u > natFact (U * T) ∧
      Nat.lcm colFac rowFac > natFact (U * T) * rowFac ∧
      (∀ (K X_max : Nat), X_max ≥ U * T ->
        (∀ i : Fin (U * T), (laurentRectRows U T i).1 * W + (laurentRectRows U T i).2 * K ≤ X_max) ->
        let M0 : Fin (U * T) -> Fin (U * T) -> Int := fun i j =>
          (laurentZeroGapIntEntry W K (laurentRectRows U T i).1 (laurentRectRows U T i).2
            (laurentColsAllU U T u j).1 (laurentColsAllU U T u j).2 : Int)
        let newtonProd := colBoundProdPrefix (U * T)
          (fun j => mixedNewtonCoeffAllU T (2 ^ u) X_max j.val) (U * T)
        let rawProd := colBoundProdPrefix (U * T)
          (fun j => laurentInterpBinom X_max (laurentColsAllU U T u j).1 *
            2 ^ (X_max * (laurentColsAllU U T u j).2)) (U * T)
        ((intDet (U * T) M0).natAbs / Nat.lcm colFac rowFac) * rowFac ≤ colFac * newtonProd ∧
        ((intDet (U * T) M0).natAbs / Nat.lcm colFac rowFac) * rowFac < rawProd ∧
        (intDet (U * T) M0).natAbs / Nat.lcm colFac rowFac ≤ rawProd / rowFac)) ∧
    (∀ (U T W K X_max : Nat), T ≥ 1 -> U > T -> U ≥ 4 -> W ≥ 1 -> X_max ≥ U * T ->
      (∀ d : Nat, 1 ≤ d -> d < U -> Nat.Coprime W d) ->
      (∀ i : Fin (U * T), (laurentRectRows U T i).1 * W + (laurentRectRows U T i).2 * K ≤ X_max) ->
      let colFac := confluentFactorAllU U T 1
      let rowFac := (2 ^ W - 1) ^ (T * (U - T))
      let M0 : Fin (U * T) -> Fin (U * T) -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (laurentRectRows U T i).1 (laurentRectRows U T i).2
          (laurentColsAllU U T 1 j).1 (laurentColsAllU U T 1 j).2 : Int)
      let newtonProd := colBoundProdPrefix (U * T)
        (fun j => mixedNewtonCoeffAllU T 2 X_max j.val) (U * T)
      let rawProd := colBoundProdPrefix (U * T)
        (fun j => laurentInterpBinom X_max (laurentColsAllU U T 1 j).1 *
          2 ^ (X_max * (laurentColsAllU U T 1 j).2)) (U * T)
      Nat.Coprime colFac rowFac ∧
      Nat.lcm colFac rowFac = colFac * rowFac ∧
      Nat.lcm colFac rowFac > natFact (U * T) * rowFac ∧
      (intDet (U * T) M0).natAbs / (colFac * rowFac) ≤ (natFact (U * T) * newtonProd) / rowFac ∧
      ((intDet (U * T) M0).natAbs / (colFac * rowFac)) * rowFac < rawProd ∧
      (intDet (U * T) M0).natAbs / (colFac * rowFac) ≤ rawProd / rowFac) ∧
    (let M0_12_582 : Fin 12 -> Fin 12 -> Int := fun i j =>
       (laurentZeroGapIntEntry 5 8 (laurentRectRows 4 3 i).1 (laurentRectRows 4 3 i).2
         (laurentColsAllU 4 3 2 j).1 (laurentColsAllU 4 3 2 j).2 : Int)
     confluentFactorAllU 4 1 1 = 1008 ∧
     Nat.lcm (confluentFactorAllU 4 1 1) ((2 ^ 6 - 1) ^ 3) < natFact 4 * (2 ^ 6 - 1) ^ 3 ∧
     Nat.gcd (confluentFactorAllU 4 3 2) ((2 ^ (5 * 2) - 1) ^ (3 * (4 - 3))) = 27 ∧
     ¬ (((confluentFactorAllU 4 3 2 * (2 ^ (5 * 2) - 1) ^ (3 * (4 - 3)) : Nat) : Int) ∣
       intDet 12 M0_12_582)) := by
  have hw15_maj := laurent_all_blocks_arbitrary_U_confluent_divisibility_and_majorant.2.2.1
  have hw15_dom := laurent_all_blocks_arbitrary_U_confluent_divisibility_and_majorant.2.2.2.2.2.2
  have hw16_maj := laurent_rect_all_U_gt_T_joint_row_col_lcm_and_reduced_bound.2.1
  have hnatFact_pos : ∀ n : Nat, natFact n ≥ 1 := by
    intro n; induction n with
    | zero => decide
    | succ n' ih => simp only [natFact]; exact Nat.mul_pos (by omega) ih
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Part 1: Pure-`2^E_2` divisibility, coprimality to `rowFac`, & joint exponential lower bound:
    intro U T W u hT hUT hW hu; dsimp only
    have hdvd_col := (confluentFactorAllU_two_dvd_and_coprime_w17 U T u hu).1
    have hWu_pos : W * u ≥ 1 := Nat.mul_le_mul hW hu
    have hodd_m : (2 ^ (W * u) - 1) % 2 = 1 := by
      rw [show W * u = (W * u - 1) + 1 by omega, Nat.pow_succ]
      have hp := nat_pow_pos_of_pos 2 (by decide) (W * u - 1); omega
    have hc2_base : Nat.Coprime 2 (2 ^ (W * u) - 1) := by
      rw [Nat.coprime_iff_gcd_eq_one]
      have hg2 : Nat.gcd 2 (2 ^ (W * u) - 1) ≤ 2 := Nat.le_of_dvd (by decide) (Nat.gcd_dvd_left _ _)
      have hgp : Nat.gcd 2 (2 ^ (W * u) - 1) ≥ 1 := Nat.gcd_pos_of_pos_left _ (by decide)
      have hgd := Nat.gcd_dvd_right 2 (2 ^ (W * u) - 1)
      by_cases h1 : Nat.gcd 2 (2 ^ (W * u) - 1) = 1
      · exact h1
      · have he2 : Nat.gcd 2 (2 ^ (W * u) - 1) = 2 := by omega
        rw [he2] at hgd; rcases hgd with ⟨q, hq⟩; omega
    have hcop_2r : Nat.Coprime (2 ^ rectConfluentTwoExp U T u) ((2 ^ (W * u) - 1) ^ (T * (U - T))) :=
      (hc2_base.pow_left _).pow_right _
    have hd1 : 2 ^ rectConfluentTwoExp U T u ∣
        Nat.lcm (confluentFactorAllU U T u) ((2 ^ (W * u) - 1) ^ (T * (U - T))) :=
      Nat.dvd_trans hdvd_col (Nat.dvd_lcm_left _ _)
    have hd2 : (2 ^ (W * u) - 1) ^ (T * (U - T)) ∣
        Nat.lcm (confluentFactorAllU U T u) ((2 ^ (W * u) - 1) ^ (T * (U - T))) :=
      Nat.dvd_lcm_right _ _
    have hdvd_prod := hcop_2r.mul_dvd_of_dvd_of_dvd hd1 hd2
    have hcf_pos : confluentFactorAllU U T u ≥ 1 := by
      let P := 2 ^ u
      have hP2 : P ≥ 2 := by simpa [P] using pow2_mono_nat hu
      have hnd : ∀ m b : Nat, b ≤ m -> blockNodeDiffProd P m b ≥ 1 := by
        intro m b hb; induction b with
        | zero => exact Nat.le_refl 1
        | succ b' ih =>
          simp only [blockNodeDiffProd]
          have hgt : P ^ b' < P ^ m := by
            have h1 : P ^ b' < P ^ (b' + 1) := by
              rw [Nat.pow_succ]
              have hp := nat_pow_pos_of_pos P (by omega) b'
              calc P ^ b' = P ^ b' * 1 := (Nat.mul_one _).symm
                _ < P ^ b' * 2 := Nat.mul_lt_mul_of_pos_left (by decide) hp
                _ ≤ P ^ b' * P := Nat.mul_le_mul_left _ hP2
            exact Nat.lt_of_lt_of_le h1 (nat_pow_mono_exp_pos P _ _ (by omega) hb)
          exact Nat.mul_pos (ih (by omega)) (by omega)
      have hpos_aux : ∀ m : Nat, confluentFactorAllUAux T P m ≥ 1 := by
        intro m; induction m with
        | zero => exact Nat.le_refl 1
        | succ m' ihm =>
          simp only [confluentFactorAllUAux, confluentBlockFactor]
          exact Nat.mul_pos ihm
            (Nat.mul_pos (nat_pow_pos_of_pos P (by omega) _)
              (nat_pow_pos_of_pos _ (hnd m' m' (Nat.le_refl m')) _))
      exact hpos_aux U
    have hrf_ge_pow : (2 ^ (W * u) - 1) ^ (T * (U - T)) ≥ 2 ^ ((W * u - 1) * (T * (U - T))) := by
      have hbase_ge : 2 ^ (W * u - 1) ≤ 2 ^ (W * u) - 1 := by
        have heq_wu : 2 ^ (W * u) = 2 ^ (W * u - 1) * 2 := by
          conv => lhs; rw [show W * u = (W * u - 1) + 1 by omega, Nat.pow_succ]
        have hp := nat_pow_pos_of_pos 2 (by decide) (W * u - 1)
        omega
      have hpow_le := pow_mono_base_w17c (2 ^ (W * u - 1)) (2 ^ (W * u) - 1) hbase_ge (T * (U - T))
      rwa [← pow_pow_eq_mul_w5 2 (W * u - 1) (T * (U - T))]
    have hrf_pos : (2 ^ (W * u) - 1) ^ (T * (U - T)) ≥ 1 :=
      Nat.le_trans (nat_pow_pos_of_pos 2 (by decide) _) hrf_ge_pow
    have hlcm_pos : Nat.lcm (confluentFactorAllU U T u) ((2 ^ (W * u) - 1) ^ (T * (U - T))) ≥ 1 := by
      have hgl := Nat.gcd_mul_lcm (confluentFactorAllU U T u) ((2 ^ (W * u) - 1) ^ (T * (U - T)))
      have hp_pos := Nat.mul_pos hcf_pos hrf_pos
      by_cases hl0 : Nat.lcm (confluentFactorAllU U T u) ((2 ^ (W * u) - 1) ^ (T * (U - T))) = 0
      · rw [hl0, Nat.mul_zero] at hgl; omega
      · omega
    have hexp_le : 2 ^ (rectConfluentTwoExp U T u + (W * u - 1) * (T * (U - T))) ≤
        Nat.lcm (confluentFactorAllU U T u) ((2 ^ (W * u) - 1) ^ (T * (U - T))) := by
      rw [Nat.pow_add]
      exact Nat.le_trans (Nat.mul_le_mul_left _ hrf_ge_pow) (Nat.le_of_dvd hlcm_pos hdvd_prod)
    exact ⟨hdvd_col, hcop_2r, hdvd_prod, hexp_le⟩
  · -- Part 2: Universal pure-`2^E_2` super-factorial dominance & `(U * T)!`-cancelled bound:
    intro U T W u hT hUT hW hu hcases; dsimp only
    have hdom_arg : (U ≥ 5 ∧ U > T) ∨ (U = 4 ∧ 2 ≤ T ∧ T < 4) ∨ (U = 4 ∧ T = 1 ∧ u ≥ 2) := by
      rcases hcases with h5 | ⟨rfl, h2⟩ | h412
      · exact Or.inl ⟨h5, hUT⟩
      · exact Or.inr (Or.inl ⟨rfl, h2, hUT⟩)
      · exact Or.inr (Or.inr h412)
    have hgt_fact := pure_two_exp_gt_natFact_w17 U T u hT hu hdom_arg
    have hWu_pos : W * u ≥ 1 := Nat.mul_le_mul hW hu
    have hrf_pos : (2 ^ (W * u) - 1) ^ (T * (U - T)) ≥ 1 := by
      have hp : 2 ^ (W * u) ≥ 2 := by simpa using pow2_mono_nat hWu_pos
      exact nat_pow_pos_of_pos _ (by omega) _
    have hdvd_lcm : 2 ^ rectConfluentTwoExp U T u * (2 ^ (W * u) - 1) ^ (T * (U - T)) ∣
        Nat.lcm (confluentFactorAllU U T u) ((2 ^ (W * u) - 1) ^ (T * (U - T))) := by
      have hodd_m : (2 ^ (W * u) - 1) % 2 = 1 := by
        rw [show W * u = (W * u - 1) + 1 by omega, Nat.pow_succ]
        have hp := nat_pow_pos_of_pos 2 (by decide) (W * u - 1); omega
      have hc2_base : Nat.Coprime 2 (2 ^ (W * u) - 1) := by
        rw [Nat.coprime_iff_gcd_eq_one]
        have hg2 : Nat.gcd 2 (2 ^ (W * u) - 1) ≤ 2 := Nat.le_of_dvd (by decide) (Nat.gcd_dvd_left _ _)
        have hgp : Nat.gcd 2 (2 ^ (W * u) - 1) ≥ 1 := Nat.gcd_pos_of_pos_left _ (by decide)
        have hgd := Nat.gcd_dvd_right 2 (2 ^ (W * u) - 1)
        by_cases h1 : Nat.gcd 2 (2 ^ (W * u) - 1) = 1
        · exact h1
        · have he2 : Nat.gcd 2 (2 ^ (W * u) - 1) = 2 := by omega
          rw [he2] at hgd; rcases hgd with ⟨q, hq⟩; omega
      exact ((hc2_base.pow_left _).pow_right _).mul_dvd_of_dvd_of_dvd
        (Nat.dvd_trans (confluentFactorAllU_two_dvd_and_coprime_w17 U T u hu).1 (Nat.dvd_lcm_left _ _))
        (Nat.dvd_lcm_right _ _)
    have hlcm_pos : Nat.lcm (confluentFactorAllU U T u) ((2 ^ (W * u) - 1) ^ (T * (U - T))) ≥ 1 := by
      have hcf_gt : confluentFactorAllU U T u > natFact (U * T) := hw15_dom U T u (by omega) hT hu
      have hgl := Nat.gcd_mul_lcm (confluentFactorAllU U T u) ((2 ^ (W * u) - 1) ^ (T * (U - T)))
      have hprod_pos : confluentFactorAllU U T u * (2 ^ (W * u) - 1) ^ (T * (U - T)) ≥ 1 :=
        Nat.mul_pos (by omega) hrf_pos
      by_cases hl0 : Nat.lcm (confluentFactorAllU U T u) ((2 ^ (W * u) - 1) ^ (T * (U - T))) = 0
      · rw [hl0, Nat.mul_zero] at hgl; omega
      · omega
    have hle_lcm := Nat.le_of_dvd hlcm_pos hdvd_lcm
    have hlcm_gt : Nat.lcm (confluentFactorAllU U T u) ((2 ^ (W * u) - 1) ^ (T * (U - T))) >
        natFact (U * T) * (2 ^ (W * u) - 1) ^ (T * (U - T)) :=
      Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hgt_fact hrf_pos) hle_lcm
    refine ⟨hgt_fact, hlcm_gt, ?_⟩
    intro K X_max hX hrows
    rcases hw15_maj U W K T u X_max (laurentRectRows U T) (by omega) hT hu hX hrows with
      ⟨hd_le_red, hred_lt_raw⟩
    rcases hw16_maj U T W K u X_max hT hUT hW hu hX hrows with ⟨_, _, hdiv_mul_eq, _⟩
    let colFac := confluentFactorAllU U T u
    let rowFac := (2 ^ (W * u) - 1) ^ (T * (U - T))
    let jointLcm := Nat.lcm colFac rowFac
    let Q := (intDet (U * T) (fun i j =>
      (laurentZeroGapIntEntry W K (laurentRectRows U T i).1 (laurentRectRows U T i).2
        (laurentColsAllU U T u j).1 (laurentColsAllU U T u j).2 : Int))).natAbs / jointLcm
    let redProd := colFac * colBoundProdPrefix (U * T) (fun j => mixedNewtonCoeffAllU T (2 ^ u) X_max j.val) (U * T)
    let rawProd := colBoundProdPrefix (U * T)
      (fun j => laurentInterpBinom X_max (laurentColsAllU U T u j).1 *
        2 ^ (X_max * (laurentColsAllU U T u j).2)) (U * T)
    change Q * jointLcm = _ at hdiv_mul_eq
    change _ ≤ natFact (U * T) * redProd at hd_le_red
    change redProd < rawProd at hred_lt_raw
    have hnf_pos := hnatFact_pos (U * T)
    have hQ_red : natFact (U * T) * (Q * rowFac) ≤ natFact (U * T) * redProd := by
      calc natFact (U * T) * (Q * rowFac)
          = Q * (natFact (U * T) * rowFac) := by ac_rfl
        _ ≤ Q * jointLcm := Nat.mul_le_mul_left Q (Nat.le_of_lt hlcm_gt)
        _ ≤ natFact (U * T) * redProd := by rw [hdiv_mul_eq]; exact hd_le_red
    have hle_red : Q * rowFac ≤ redProd :=
      Nat.le_of_mul_le_mul_left hQ_red hnf_pos
    have hlt_raw : Q * rowFac < rawProd := Nat.lt_of_le_of_lt hle_red hred_lt_raw
    have hdiv_raw : Q ≤ rawProd / rowFac := by
      have hm := Nat.div_le_div_right (Nat.le_of_lt hlt_raw) (c := rowFac)
      rwa [Nat.mul_div_cancel Q hrf_pos] at hm
    exact ⟨hle_red, hlt_raw, hdiv_raw⟩
  · -- Part 3: Coprime-`W` exact `Nat.lcm = colFac * rowFac` & `(U * T)!`-cancelled reduced bound:
    intro U T W K X_max hT hUT hU4 hW hX hcop_d hrows; dsimp only
    have hc_base := (confluentFactorAllU_two_dvd_and_coprime_w17 U T 1 (by decide)).2 W hW hcop_d
    have hcop_cr : Nat.Coprime (confluentFactorAllU U T 1) ((2 ^ W - 1) ^ (T * (U - T))) :=
      hc_base.pow_right (T * (U - T))
    have hlcm_prod : Nat.lcm (confluentFactorAllU U T 1) ((2 ^ W - 1) ^ (T * (U - T))) =
        confluentFactorAllU U T 1 * (2 ^ W - 1) ^ (T * (U - T)) := by
      have hg_lcm := Nat.gcd_mul_lcm (confluentFactorAllU U T 1) ((2 ^ W - 1) ^ (T * (U - T)))
      have hg1 : Nat.gcd (confluentFactorAllU U T 1) ((2 ^ W - 1) ^ (T * (U - T))) = 1 := hcop_cr
      rw [hg1, Nat.one_mul] at hg_lcm
      exact hg_lcm
    have hcf_gt := hw15_dom U T 1 hU4 hT (by decide)
    have hrf_pos : (2 ^ W - 1) ^ (T * (U - T)) ≥ 1 := by
      have hp : 2 ^ W ≥ 2 := by simpa using pow2_mono_nat hW
      exact nat_pow_pos_of_pos _ (by omega) _
    have hgt_prod : Nat.lcm (confluentFactorAllU U T 1) ((2 ^ W - 1) ^ (T * (U - T))) >
        natFact (U * T) * (2 ^ W - 1) ^ (T * (U - T)) := by
      rw [hlcm_prod]; exact Nat.mul_lt_mul_of_pos_right hcf_gt hrf_pos
    rcases hw16_maj U T W K 1 X_max hT hUT hW (by decide) hX hrows with ⟨_, _, hdiv_eq1, hmaj_bd⟩
    rcases hw15_maj U W K T 1 X_max (laurentRectRows U T) (by omega) hT (by decide) hX hrows with
      ⟨hd_le_red1, hred_lt_raw1⟩
    rw [Nat.mul_one] at hmaj_bd hdiv_eq1
    have hg1 : Nat.gcd (confluentFactorAllU U T 1) ((2 ^ W - 1) ^ (T * (U - T))) = 1 := hcop_cr
    rw [hlcm_prod, hg1, Nat.div_one, show (2 ^ 1 : Nat) = 2 from rfl] at hmaj_bd
    rw [hlcm_prod] at hdiv_eq1
    let colFac1 := confluentFactorAllU U T 1
    let rowFac1 := (2 ^ W - 1) ^ (T * (U - T))
    let Q1 := (intDet (U * T) (fun i j =>
      (laurentZeroGapIntEntry W K (laurentRectRows U T i).1 (laurentRectRows U T i).2
        (laurentColsAllU U T 1 j).1 (laurentColsAllU U T 1 j).2 : Int))).natAbs / (colFac1 * rowFac1)
    let redProd1 := colFac1 * colBoundProdPrefix (U * T) (fun j => mixedNewtonCoeffAllU T (2 ^ 1) X_max j.val) (U * T)
    let rawProd1 := colBoundProdPrefix (U * T)
      (fun j => laurentInterpBinom X_max (laurentColsAllU U T 1 j).1 *
        2 ^ (X_max * (laurentColsAllU U T 1 j).2)) (U * T)
    change Q1 * (colFac1 * rowFac1) = _ at hdiv_eq1
    change _ ≤ natFact (U * T) * redProd1 at hd_le_red1
    change redProd1 < rawProd1 at hred_lt_raw1
    have hnf_pos1 := hnatFact_pos (U * T)
    have hQ1_red : natFact (U * T) * (Q1 * rowFac1) ≤ natFact (U * T) * redProd1 := by
      calc natFact (U * T) * (Q1 * rowFac1)
          = Q1 * (natFact (U * T) * rowFac1) := by ac_rfl
        _ ≤ Q1 * (colFac1 * rowFac1) :=
          Nat.mul_le_mul_left Q1 (Nat.mul_le_mul_right rowFac1 (Nat.le_of_lt hcf_gt))
        _ ≤ natFact (U * T) * redProd1 := by rw [hdiv_eq1]; exact hd_le_red1
    have hQ1_lt_raw : Q1 * rowFac1 < rawProd1 :=
      Nat.lt_of_le_of_lt (Nat.le_of_mul_le_mul_left hQ1_red hnf_pos1) hred_lt_raw1
    have hQ1_div_raw : Q1 ≤ rawProd1 / rowFac1 := by
      have hm := Nat.div_le_div_right (Nat.le_of_lt hQ1_lt_raw) (c := rowFac1)
      rwa [Nat.mul_div_cancel Q1 hrf_pos] at hm
    exact ⟨hcop_cr, hlcm_prod, hgt_prod, hmaj_bd, hQ1_lt_raw, hQ1_div_raw⟩
  · dsimp only
    let M0_12_582 : Fin 12 -> Fin 12 -> Int := fun i j =>
      (laurentZeroGapIntEntry 5 8 (laurentRectRows 4 3 i).1 (laurentRectRows 4 3 i).2
        (laurentColsAllU 4 3 2 j).1 (laurentColsAllU 4 3 2 j).2 : Int)
    have hm0_eq : M0_12_582 = fastM0_12_582Fn := by
      funext i j
      dsimp [M0_12_582, fastM0_12_582Fn, laurentZeroGapIntEntry, laurentRectRows, laurentColsAllU]
      rw [fastBinom3W17_eq_laurentInterpBinom _ _ (by have := Nat.mod_lt j.val (by decide : 0 < 3); omega)]
    rcases m0_12_582_ul_cert with ⟨hul, hrem_nz⟩
    have hdet_m0 := checkULDet12Bool_sound_w17 fastM0_12_582Fn uM0_12_582Tbl (46558461071235227007405710911151890386680280679811809367547602757305367832327345725373300455850243437009644501991692800180852521887506232429176648342956794713182761728031058778186934118069468410798496613128453583011840000000000000000000000) hul
    rw [← hm0_eq] at hdet_m0
    have hndvd : ¬ ((((confluentFactorAllU 4 3 2 * (2 ^ (5 * 2) - 1) ^ (3 * (4 - 3)) : Nat) : Int)) ∣ intDet 12 M0_12_582) := by
      rw [hdet_m0]
      rintro ⟨q, hq⟩
      rw [hq, Int.mul_emod_right] at hrem_nz
      exact hrem_nz rfl
    exact ⟨by decide, by decide, by decide, hndvd⟩

-- ----------------------------------------------------------------------------
-- Section 2B: Rank-3 Order-4 `12 × 12` `(T = 4, U = 3)` Two-Base Schneider–Laurent
--             Determinants, Collatz-Cone Sign-Flip, Exact Degree-18 Closed Form,
--             & Projective `P^1(F_47)` Non-Vanishing (`K = 4 * W` Zero Locus)
-- ----------------------------------------------------------------------------

/-- Canonical `12`-row two-base grid `(i % 3, i / 3)` (`r < 3, s < 4`). -/
def laurentRowsTwoBase12 (i : Fin 12) : Nat × Nat :=
  (i.val % 3, i.val / 3)

/-- Canonical `12`-column order-4 rank-3 grid `(j % 4, (j / 4) * u)` (`t < 4, m < 3`). -/
def laurentColsT4U3_12 (u : Nat) (j : Fin 12) : Nat × Nat :=
  (j.val % 4, (j.val / 4) * u)

/-- Rank-3 order-4 `12 × 12` `(T = 4, U = 3)` two-base Schneider–Laurent matrix. -/
def laurentTwoBaseT4U3Mat12 (W K u : Nat) : Fin 12 -> Fin 12 -> Int :=
  laurentInterpMat W K 12 laurentRowsTwoBase12 (laurentColsT4U3_12 u)

/-- Exact 15-coefficient homogeneous degree-14 core polynomial `Q_14(W, K)` of `det_12(W, K, 1)`
    (ascending in `W`-degree `0 .. 14`, multiplying `W^d * K^(14 - d)`). -/
def q14T4U3Coeffs : List Int :=
  [-129140163, -516560652, 11401898256, -56586403008,
   167234674464, -403944741504, 805882269504, -1042083490560,
   491454281984, 602538914816, -1058060256256, 619444207616,
   -152458756096, 17397972992, -805306368]

/-- Homogeneous bivariate polynomial evaluator `∑_d c_d * w^(curW + d) * k^(totalDeg - (curW + d))`. -/
def evalHomogAscAux (totalDeg curW : Nat) (w k : Int) : List Int -> Int
  | [] => 0
  | c :: cs =>
    c * intPowNat w curW * intPowNat k (totalDeg - curW) +
      evalHomogAscAux totalDeg (curW + 1) w k cs

/-- Exact homogeneous degree-14 core polynomial `Q_14(W, K)` over `Int`. -/
def q14T4U3PolyInt (W K : Int) : Int :=
  evalHomogAscAux 14 0 W K q14T4U3Coeffs

private def evalUniInt (x : Int) : List Int -> Int
  | [] => 0
  | c :: cs => c + x * evalUniInt x cs

private def divByLinearInt (r : Int) : List Int -> List Int × Int
  | [] => ([], 0)
  | c :: cs =>
    let qr := divByLinearInt r cs
    (if cs.isEmpty then [] else qr.2 :: qr.1, c + r * qr.2)

private theorem divByLinearInt_spec_w17 (r : Int) :
    ∀ p : List Int,
      (p ≠ [] -> (divByLinearInt r p).1.length + 1 = p.length) ∧
      (∀ x : Int, evalUniInt x p = (x - r) * evalUniInt x (divByLinearInt r p).1 + (divByLinearInt r p).2)
  | [] => ⟨fun h => False.elim (h rfl), fun _ => by simp [divByLinearInt, evalUniInt]⟩
  | [c] =>
    ⟨fun _ => rfl, fun x => by simp [divByLinearInt, evalUniInt]⟩
  | c :: d :: tl => by
    rcases divByLinearInt_spec_w17 r (d :: tl) with ⟨hlen, heval⟩
    have hne : d :: tl ≠ [] := by simp
    have hl := hlen hne
    refine ⟨fun _ => by
              simp only [divByLinearInt, List.isEmpty_cons, Bool.false_eq_true, ite_false, List.length_cons] at hl ⊢
              omega,
            fun x => ?_⟩
    simp only [divByLinearInt, List.isEmpty_cons, Bool.false_eq_true, ite_false]
    change c + x * evalUniInt x (d :: tl) =
      (x - r) * ((divByLinearInt r (d :: tl)).2 + x * evalUniInt x (divByLinearInt r (d :: tl)).1) +
        (c + r * (divByLinearInt r (d :: tl)).2)
    rw [heval x]
    generalize evalUniInt x (divByLinearInt r (d :: tl)).1 = Q,
      (divByLinearInt r (d :: tl)).2 = R
    rw [Int.mul_add x ((x - r) * Q) R, Int.mul_add (x - r) R (x * Q),
        Int.sub_mul x r R,
        show (x - r) * (x * Q) = x * ((x - r) * Q) by ac_rfl]
    omega

private theorem evalUniInt_zero_of_roots_from_w17 :
    ∀ (n s0 : Nat) (p : List Int),
      p.length ≤ n ->
      (∀ idx : Nat, idx < n -> evalUniInt ((s0 + idx : Nat) : Int) p = 0) ->
      ∀ x : Int, evalUniInt x p = 0
  | 0, _, p, hlen, _, x => by
    cases p with
    | nil => rfl
    | cons _ _ => simp at hlen
  | n' + 1, s0, p, hlen, hroots, x => by
    cases p with
    | nil => rfl
    | cons c cs =>
      let r : Int := ((s0 + n' : Nat) : Int)
      rcases divByLinearInt_spec_w17 r (c :: cs) with ⟨hq_len, hq_eval⟩
      have hrem0 : (divByLinearInt r (c :: cs)).2 = 0 := by
        have hr0 := hroots n' (by omega)
        have he := hq_eval r
        rw [Int.sub_self, Int.zero_mul, Int.zero_add] at he
        exact he.symm.trans hr0
      let q := (divByLinearInt r (c :: cs)).1
      have hq_le : q.length ≤ n' := by
        have hl := hq_len (by simp)
        dsimp [q] at *; simp at hlen hl; omega
      have hq_roots : ∀ idx : Nat, idx < n' -> evalUniInt ((s0 + idx : Nat) : Int) q = 0 := by
        intro idx hidx
        have hi_p := hroots idx (by omega)
        have he := hq_eval ((s0 + idx : Nat) : Int)
        rw [hrem0, Int.add_zero, hi_p] at he
        have hdiff_ne : ((s0 + idx : Nat) : Int) - r ≠ 0 := by dsimp [r]; omega
        by_cases hqz : evalUniInt ((s0 + idx : Nat) : Int) q = 0
        · exact hqz
        · exact False.elim (Int.mul_ne_zero hdiff_ne hqz he.symm)
      rw [hq_eval x, hrem0, Int.add_zero, evalUniInt_zero_of_roots_from_w17 n' s0 q hq_le hq_roots x,
          Int.mul_zero]

private theorem allZero_of_evalUniInt_zero_w17 :
    ∀ p : List Int, (∀ x : Int, evalUniInt x p = 0) -> ∀ a ∈ p, a = 0
  | [], _, _, ha => by cases ha
  | c :: cs, hall, a, ha => by
    have hc0 : c = 0 := by simpa [evalUniInt] using hall 0
    have hcs_roots : ∀ idx : Nat, idx < cs.length -> evalUniInt ((1 + idx : Nat) : Int) cs = 0 := by
      intro idx _
      have hi := hall ((1 + idx : Nat) : Int)
      simp only [evalUniInt, hc0, Int.zero_add] at hi
      by_cases hz : evalUniInt ((1 + idx : Nat) : Int) cs = 0
      · exact hz
      · exact False.elim (Int.mul_ne_zero (by omega : ((1 + idx : Nat) : Int) ≠ 0) hz hi)
    have hcs_all := evalUniInt_zero_of_roots_from_w17 cs.length 1 cs (Nat.le_refl _) hcs_roots
    cases ha with
    | head => exact hc0
    | tail _ htl => exact allZero_of_evalUniInt_zero_w17 cs hcs_all a htl

private theorem evalHomogAscAux_at_k1_w17 (D : Nat) (w : Int) :
    ∀ (cs : List Int) (curW : Nat),
      evalHomogAscAux D curW w 1 cs = intPowNat w curW * evalUniInt w cs
  | [], _ => by simp [evalHomogAscAux, evalUniInt]
  | c :: tl, curW => by
    have hp1 : ∀ m : Nat, intPowNat 1 m = 1 := by
      intro m; induction m with | zero => rfl | succ m' ih => simp [intPowNat, ih]
    simp only [evalHomogAscAux, evalUniInt, hp1, Int.mul_one,
               evalHomogAscAux_at_k1_w17 D w tl (curW + 1)]
    have hpw : intPowNat w (curW + 1) = intPowNat w curW * w := by
      rw [intPowNat_add w curW 1]; simp [intPowNat]
    rw [hpw, Int.mul_add]
    ac_rfl

private def addPolySameLen : List Int -> List Int -> List Int := List.zipWith (· + ·)
private def subPolySameLen : List Int -> List Int -> List Int := List.zipWith (· - ·)
private def scalePolyInt (c : Int) (p : List Int) : List Int := p.map (c * ·)

private theorem poly_linear_ops_spec_w17 (D : Nat) (w k : Int) :
    (∀ (c : Int) (p : List Int) (curW : Nat),
      (scalePolyInt c p).length = p.length ∧
      evalHomogAscAux D curW w k (scalePolyInt c p) = c * evalHomogAscAux D curW w k p) ∧
    (∀ (p q : List Int) (curW : Nat), p.length = q.length ->
      (addPolySameLen p q).length = p.length ∧
      evalHomogAscAux D curW w k (addPolySameLen p q) =
        evalHomogAscAux D curW w k p + evalHomogAscAux D curW w k q) ∧
    (∀ (p q : List Int) (curW : Nat), p.length = q.length ->
      (subPolySameLen p q).length = p.length ∧
      evalHomogAscAux D curW w k (subPolySameLen p q) =
        evalHomogAscAux D curW w k p - evalHomogAscAux D curW w k q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c p; induction p with
    | nil => intro _; exact ⟨rfl, by simp [scalePolyInt, evalHomogAscAux]⟩
    | cons a tl ih =>
      intro curW
      refine ⟨by simp [scalePolyInt], ?_⟩
      change (c * a) * intPowNat w curW * intPowNat k (D - curW) +
        evalHomogAscAux D (curW + 1) w k (scalePolyInt c tl) =
        c * (a * intPowNat w curW * intPowNat k (D - curW) + evalHomogAscAux D (curW + 1) w k tl)
      rw [(ih (curW + 1)).2, Int.mul_add]
      ac_rfl
  · intro p; induction p with
    | nil =>
      intro q _ hlen; cases q with
      | nil => exact ⟨rfl, by simp [addPolySameLen, evalHomogAscAux]⟩
      | cons _ _ => simp at hlen
    | cons a ptl ih =>
      intro q curW hlen; cases q with
      | nil => simp at hlen
      | cons b qtl =>
        have hl : ptl.length = qtl.length := by simp at hlen; omega
        rcases ih qtl (curW + 1) hl with ⟨ihl, ihe⟩
        refine ⟨?_, ?_⟩
        · change ((a + b) :: addPolySameLen ptl qtl).length = (a :: ptl).length
          simp only [List.length_cons, ihl]
        · change (a + b) * intPowNat w curW * intPowNat k (D - curW) +
            evalHomogAscAux D (curW + 1) w k (addPolySameLen ptl qtl) =
            (a * intPowNat w curW * intPowNat k (D - curW) + evalHomogAscAux D (curW + 1) w k ptl) +
            (b * intPowNat w curW * intPowNat k (D - curW) + evalHomogAscAux D (curW + 1) w k qtl)
          rw [ihe, Int.add_mul, Int.add_mul]
          omega
  · intro p; induction p with
    | nil =>
      intro q _ hlen; cases q with
      | nil => exact ⟨rfl, by simp [subPolySameLen, evalHomogAscAux]⟩
      | cons _ _ => simp at hlen
    | cons a ptl ih =>
      intro q curW hlen; cases q with
      | nil => simp at hlen
      | cons b qtl =>
        have hl : ptl.length = qtl.length := by simp at hlen; omega
        rcases ih qtl (curW + 1) hl with ⟨ihl, ihe⟩
        refine ⟨?_, ?_⟩
        · change ((a - b) :: subPolySameLen ptl qtl).length = (a :: ptl).length
          simp only [List.length_cons, ihl]
        · change (a - b) * intPowNat w curW * intPowNat k (D - curW) +
            evalHomogAscAux D (curW + 1) w k (subPolySameLen ptl qtl) =
            (a * intPowNat w curW * intPowNat k (D - curW) + evalHomogAscAux D (curW + 1) w k ptl) -
            (b * intPowNat w curW * intPowNat k (D - curW) + evalHomogAscAux D (curW + 1) w k qtl)
          rw [ihe, Int.sub_mul, Int.sub_mul]
          omega

private def mulHomogPoly : List Int -> List Int -> List Int
  | [], _ => []
  | [c], q => scalePolyInt c q
  | c :: p1 :: ptl, q =>
    let tail_prod := mulHomogPoly (p1 :: ptl) q
    addPolySameLen (scalePolyInt c q ++ List.replicate (p1 :: ptl).length 0) (0 :: tail_prod)

private theorem mulHomogPoly_spec_w17 :
    ∀ (d1 : Nat) (p : List Int), p.length = d1 + 1 ->
      ∀ (d2 : Nat) (q : List Int), q.length = d2 + 1 ->
        (mulHomogPoly p q).length = d1 + d2 + 1 ∧
        (∀ w k : Int,
          evalHomogAscAux (d1 + d2) 0 w k (mulHomogPoly p q) =
            evalHomogAscAux d1 0 w k p * evalHomogAscAux d2 0 w k q) := by
  have happ_zeros : ∀ (D n curW : Nat) (w k : Int) (xs : List Int),
      evalHomogAscAux D curW w k (xs ++ List.replicate n 0) = evalHomogAscAux D curW w k xs := by
    intro D n curW w k xs; induction xs generalizing curW with
    | nil =>
      induction n generalizing curW with
      | zero => rfl
      | succ n' ihn =>
        simp only [List.nil_append] at ihn ⊢
        simp only [List.replicate, evalHomogAscAux, Int.zero_mul, Int.zero_add, ihn (curW + 1)]
    | cons x xtl ihx => simp [evalHomogAscAux, ihx (curW + 1)]
  have hshift_k : ∀ (d2 extra curW : Nat) (w k : Int) (xs : List Int),
      curW + xs.length ≤ d2 + 1 ->
      evalHomogAscAux (d2 + extra) curW w k xs =
        intPowNat k extra * evalHomogAscAux d2 curW w k xs := by
    intro d2 extra curW w k xs; induction xs generalizing curW with
    | nil => intros; simp [evalHomogAscAux]
    | cons x xtl ih =>
      intro hle
      have hsub : d2 + extra - curW = extra + (d2 - curW) := by simp at hle; omega
      simp only [evalHomogAscAux, hsub, intPowNat_add k extra (d2 - curW),
                 ih (curW + 1) (by simp at hle ⊢; omega), Int.mul_add]
      ac_rfl
  have hshift_w : ∀ (D curW : Nat) (w k : Int) (xs : List Int),
      evalHomogAscAux (D + 1) (curW + 1) w k xs =
        w * evalHomogAscAux D curW w k xs := by
    intro D curW w k xs; induction xs generalizing curW with
    | nil => simp [evalHomogAscAux]
    | cons x xtl ih =>
      simp only [evalHomogAscAux, Nat.succ_sub_succ, ih (curW + 1), Int.mul_add]
      rw [intPowNat_add w curW 1, show intPowNat w 1 = w by simp [intPowNat]]
      ac_rfl
  intro d1; induction d1 with
  | zero =>
    intro p hp d2 q hq
    cases p with
    | nil => simp at hp
    | cons c ptl =>
      cases ptl with
      | nil =>
        simp only [mulHomogPoly]
        refine ⟨by simp [scalePolyInt, hq], fun w k => ?_⟩
        rw [Nat.zero_add, (poly_linear_ops_spec_w17 d2 w k).1 c q 0 |>.2]
        simp [evalHomogAscAux, intPowNat]
      | cons _ _ => simp at hp
  | succ d1' ih =>
    intro p hp d2 q hq
    cases p with
    | nil => simp at hp
    | cons c ptl =>
      cases ptl with
      | nil => simp at hp
      | cons p1 ptl' =>
        have hptl_len : (p1 :: ptl').length = d1' + 1 := by simp at hp ⊢; omega
        rcases ih (p1 :: ptl') hptl_len d2 q hq with ⟨ihl, ihe⟩
        simp only [mulHomogPoly]
        have hl1 : (scalePolyInt c q ++ List.replicate (p1 :: ptl').length 0).length =
            (d1' + 1) + d2 + 1 := by
          rw [List.length_append, List.length_replicate, scalePolyInt, List.length_map,
              hq, hptl_len]; omega
        have hl2 : (0 :: mulHomogPoly (p1 :: ptl') q).length = (d1' + 1) + d2 + 1 := by
          simp [ihl]; omega
        refine ⟨by rw [(poly_linear_ops_spec_w17 0 0 0).2.1 _ _ 0 (hl1.trans hl2.symm) |>.1, hl1],
                fun w k => ?_⟩
        rw [(poly_linear_ops_spec_w17 ((d1' + 1) + d2) w k).2.1 _ _ 0 (hl1.trans hl2.symm) |>.2,
            happ_zeros]
        have he_sc : evalHomogAscAux ((d1' + 1) + d2) 0 w k (scalePolyInt c q) =
            c * intPowNat k (d1' + 1) * evalHomogAscAux d2 0 w k q := by
          rw [(poly_linear_ops_spec_w17 ((d1' + 1) + d2) w k).1 c q 0 |>.2,
              show (d1' + 1) + d2 = d2 + (d1' + 1) by omega,
              hshift_k d2 (d1' + 1) 0 w k q (by omega), ← Int.mul_assoc]
        have he_cons : evalHomogAscAux ((d1' + 1) + d2) 0 w k (0 :: mulHomogPoly (p1 :: ptl') q) =
            w * (evalHomogAscAux d1' 0 w k (p1 :: ptl') * evalHomogAscAux d2 0 w k q) := by
          conv => lhs; simp only [evalHomogAscAux, Int.zero_mul, Int.zero_add]
          rw [show (d1' + 1) + d2 = (d1' + d2) + 1 by omega,
              hshift_w (d1' + d2) 0 w k (mulHomogPoly (p1 :: ptl') q), ihe w k]
        have hp_head : evalHomogAscAux (d1' + 1) 0 w k (c :: p1 :: ptl') =
            c * intPowNat k (d1' + 1) + w * evalHomogAscAux d1' 0 w k (p1 :: ptl') := by
          change c * intPowNat w 0 * intPowNat k ((d1' + 1) - 0) +
              evalHomogAscAux (d1' + 1) (0 + 1) w k (p1 :: ptl') = _
          rw [Nat.sub_zero, show intPowNat w 0 = 1 from rfl, Int.mul_one,
              hshift_w d1' 0 w k (p1 :: ptl')]
        rw [he_sc, he_cons, hp_head, Int.add_mul, Int.mul_assoc w]

private def colDegSum : (m : Nat) -> (Fin m -> Nat) -> Nat
  | 0, _ => 0
  | L + 1, deg =>
    deg ⟨0, Nat.zero_lt_succ L⟩ + colDegSum L (fun c => deg (skipFinIdx ⟨0, Nat.zero_lt_succ L⟩ c))

private theorem colDegSum_split_at_w17 :
    ∀ (L : Nat) (deg : Fin (L + 1) -> Nat) (j : Fin (L + 1)),
      colDegSum (L + 1) deg = deg j + colDegSum L (fun c => deg (skipFinIdx j c))
  | 0, deg, j => by
    have hj0 : j = ⟨0, Nat.zero_lt_one⟩ := Fin.ext (by omega)
    subst hj0; rfl
  | L' + 1, deg, j => by
    let z0 : Fin (L' + 2) := ⟨0, Nat.zero_lt_succ (L' + 1)⟩
    by_cases hj0 : j = z0
    · subst hj0; rfl
    · have hj_pos : j.val ≥ 1 := by have : j.val ≠ 0 := fun hv => hj0 (Fin.ext hv); omega
      let j_pred : Fin (L' + 1) := ⟨j.val - 1, by omega⟩
      have hsk_z0 : skipFinIdx z0 j_pred = j := by
        apply Fin.ext; unfold skipFinIdx
        split <;> dsimp [z0, j_pred] at * <;> omega
      have hcomm_sk : (fun c : Fin L' => deg (skipFinIdx z0 (skipFinIdx j_pred c))) =
          (fun c : Fin L' => (fun c' : Fin (L' + 1) => deg (skipFinIdx j c'))
            (skipFinIdx ⟨0, Nat.zero_lt_succ L'⟩ c)) := by
        funext c
        apply congrArg deg
        apply Fin.ext
        unfold skipFinIdx
        by_cases hlt : c.val < j.val - 1
        · have hlt2 : c.val + 1 < j.val := by omega
          simp [z0, j_pred, hlt, hlt2]
        · have hnlt2 : ¬ (c.val + 1 < j.val) := by omega
          simp [z0, j_pred, hlt, hnlt2]
      have ih1 := colDegSum_split_at_w17 L' (fun c => deg (skipFinIdx z0 c)) j_pred
      have hexp0 : colDegSum (L' + 2) deg = deg z0 + colDegSum (L' + 1) (fun c => deg (skipFinIdx z0 c)) := rfl
      have hexpj : colDegSum (L' + 1) (fun c => deg (skipFinIdx j c)) =
          deg (skipFinIdx j ⟨0, Nat.zero_lt_succ L'⟩) +
            colDegSum L' (fun c => (fun c' => deg (skipFinIdx j c')) (skipFinIdx ⟨0, Nat.zero_lt_succ L'⟩ c)) := rfl
      have hsk_j0 : skipFinIdx j ⟨0, Nat.zero_lt_succ L'⟩ = z0 := by
        apply Fin.ext
        have h0_lt : 0 < j.val := by omega
        simp [skipFinIdx, z0, h0_lt]
      rw [hexp0, ih1, hsk_z0, hcomm_sk, hexpj, hsk_j0]
      omega

private theorem poly_det_exists_homog_w17 :
    ∀ (m : Nat) (deg : Fin m -> Nat) (M : Int -> Int -> Fin m -> Fin m -> Int),
      (∀ (i j : Fin m), ∃ cij : List Int,
        cij.length = deg j + 1 ∧
        ∀ w k : Int, M w k i j = evalHomogAscAux (deg j) 0 w k cij) ->
      ∃ cs : List Int,
        cs.length = colDegSum m deg + 1 ∧
        ∀ w k : Int, intDet m (M w k) = evalHomogAscAux (colDegSum m deg) 0 w k cs
  | 0, _, _, _ =>
    ⟨[1], rfl, fun _ _ => by simp [intDet, colDegSum, evalHomogAscAux, intPowNat]⟩
  | L + 1, deg, M, hentry => by
    let z0 : Fin (L + 1) := ⟨0, Nat.zero_lt_succ L⟩
    let D := colDegSum (L + 1) deg
    -- Prefix sum over columns `0 .. m_c`:
    have hpref : ∀ m_c : Nat, m_c ≤ L + 1 ->
        ∃ cp : List Int,
          cp.length = D + 1 ∧
          ∀ w k : Int,
            intSumPrefix (L + 1) (fun j =>
              (if j.val % 2 = 0 then (1 : Int) else -1) * M w k z0 j *
                intDet L (intSubMat (M w k) j)) m_c =
            evalHomogAscAux D 0 w k cp := by
      intro m_c hm_c; induction m_c with
      | zero =>
        refine ⟨List.replicate (D + 1) 0, List.length_replicate, fun w k => ?_⟩
        have hz : ∀ n idx : Nat, evalHomogAscAux D idx w k (List.replicate n 0) = 0 := by
          intro n; induction n with
          | zero => intro _; rfl
          | succ n' ihn => intro idx; simp [List.replicate, evalHomogAscAux, ihn (idx + 1)]
        simp [intSumPrefix, hz]
      | succ mc' ihc =>
        have hmc_lt : mc' < L + 1 := hm_c
        let jc : Fin (L + 1) := ⟨mc', hmc_lt⟩
        rcases ihc (Nat.le_of_lt hm_c) with ⟨cp_prev, hlen_prev, hev_prev⟩
        rcases hentry z0 jc with ⟨c0j, hlen_0j, hev_0j⟩
        have ih_sub := poly_det_exists_homog_w17 L (fun c => deg (skipFinIdx jc c))
          (fun w k => intSubMat (M w k) jc)
          (fun r c => hentry ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩ (skipFinIdx jc c))
        rcases ih_sub with ⟨c_sub, hlen_sub, hev_sub⟩
        have hdeg_eq : D = deg jc + colDegSum L (fun c => deg (skipFinIdx jc c)) :=
          colDegSum_split_at_w17 L deg jc
        let sgn : Int := if jc.val % 2 = 0 then 1 else -1
        rcases mulHomogPoly_spec_w17 (deg jc) c0j hlen_0j
          (colDegSum L (fun c => deg (skipFinIdx jc c))) c_sub hlen_sub with ⟨hlen_mul, hev_mul⟩
        rw [← hdeg_eq] at hlen_mul hev_mul
        let term_p := scalePolyInt sgn (mulHomogPoly c0j c_sub)
        have hlen_tp : term_p.length = D + 1 := by simp [term_p, scalePolyInt, hlen_mul]
        refine ⟨addPolySameLen cp_prev term_p,
                by rw [(poly_linear_ops_spec_w17 0 0 0).2.1 _ _ 0 (hlen_prev.trans hlen_tp.symm) |>.1, hlen_prev],
                fun w k => ?_⟩
        simp only [intSumPrefix, hmc_lt, dite_true]
        rw [(poly_linear_ops_spec_w17 D w k).2.1 cp_prev term_p 0 (hlen_prev.trans hlen_tp.symm) |>.2,
            ← hev_prev w k,
            (poly_linear_ops_spec_w17 D w k).1 sgn _ 0 |>.2,
            hev_mul w k, ← hev_0j w k, ← hev_sub w k, ← Int.mul_assoc]
    rcases hpref (L + 1) (Nat.le_refl _) with ⟨cs, hlen_cs, hev_cs⟩
    exact ⟨cs, hlen_cs, fun w k => hev_cs w k⟩

private def powModFuelW17 : Nat -> Nat -> Nat -> Nat -> Nat
  | 0, _, _, _ => 1
  | f' + 1, b, e, m =>
    if e = 0 then 1 % m
    else
      let half := powModFuelW17 f' b (e / 2) m
      let sq := (half * half) % m
      if e % 2 = 1 then (sq * (b % m)) % m else sq

private def q14Mod47AllInv : Nat -> Bool
  | 0 => true
  | x + 1 =>
    (if x == 0 then true else (((x * powModFuelW17 8 x 45 47) % 47) == 1)) && q14Mod47AllInv x

private def q14Mod47AllAff : Nat -> Bool
  | 0 => true
  | t + 1 => ((evalHomogAscAux 14 0 (t : Int) 1 q14T4U3Coeffs % 47) != 0) && q14Mod47AllAff t

private def checkQ14ProjRootFreeMod47Bool : Bool :=
  q14Mod47AllInv 47 && ((evalHomogAscAux 14 0 1 0 q14T4U3Coeffs % 47) != 0) && q14Mod47AllAff 47

private def fastMat12T4U3Fn (W K u : Nat) (i j : Fin 12) : Int :=
  let r := i.val % 3; let s := i.val / 3
  let t := j.val % 4; let kc := (j.val / 4) * u
  ((fastBinom3W17 (r * W + s * K) t * (2 ^ (r * kc) * 3 ^ (s * kc)) : Nat) : Int)

private def apow12FastFn (W : Nat) (i j : Fin 12) : Int :=
  let r := i.val % 3; let s := i.val / 3
  let t := j.val % 4; let m := j.val / 4
  (((r * W + s) ^ t * (2 ^ (r * m) * 3 ^ (s * m)) : Nat) : Int)

private def uT4U3_351Tbl : List (List Int) :=
  [[1, 0, 0, 0, -45, 120, -240, 360, -510, 960, -2160, 38880],
   [0, 1, -1, 5, -20, -5, 5, -45, 60, -150, 4590, -85050],
   [0, 0, 1, -6, 7, -2, 14, -18, 30, -84, 2016, -37044],
   [0, 0, 0, 3, -6, -9, 3, 9, 0, -18, 702, -12798],
   [0, 0, 0, 0, 45, -120, 240, -360, 495, -840, -6300, 118080],
   [0, 0, 0, 0, 0, 25, -55, 115, -160, 345, -5265, 97155],
   [0, 0, 0, 0, 0, 0, 5, -26, 26, -36, 81, -1746],
   [0, 0, 0, 0, 0, 0, 0, 3, -3, 3, 72, -1287],
   [0, 0, 0, 0, 0, 0, 0, 0, 15, -120, 8460, -156960],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 5, -755, 14185],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35, -686],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3]]
private def uT4U3_581Tbl : List (List Int) :=
  [[1, 0, 0, 0, -100, 0, -390, 0, -9240, 27300, 205920, 9126000],
   [0, 1, -2, 6, -18, -8, 10, -12, 660, -2220, 166500, -10718460],
   [0, 0, 1, -4, 0, 0, 6, 0, 168, -588, 37656, -2059128],
   [0, 0, 0, 1, -1, -1, 2, 6, 6, -66, 8712, -264816],
   [0, 0, 0, 0, 100, 0, 390, 0, 8960, -25480, -792480, 24710400],
   [0, 0, 0, 0, 0, 5, -58, 18, -1830, 5710, -160240, 12513600],
   [0, 0, 0, 0, 0, 0, 3, -10, 186, -492, -768, -928224],
   [0, 0, 0, 0, 0, 0, 0, 1, -13, 31, 1384, 15312],
   [0, 0, 0, 0, 0, 0, 0, 0, 280, -1820, 586560, -33836400],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 35, -35885, 2610735],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1110, -140566],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4018]]
private def uT4U3_352Tbl : List (List Int) :=
  [[1, 0, 0, 0, -5, 40, -680, 3240, -470124, 1969344, -15252686208, 9030825266112],
   [0, 1, -1, 5, -10, -85, -35, 1215, -55080, 179100, 3132145260, 31861053540],
   [0, 0, 1, -6, 7, 94, -78, -1818, 44532, -96552, -4748895864, -136348426872],
   [0, 0, 0, 3, -6, -87, 159, 1269, 19224, -176364, 9331595604, -1800208026612],
   [0, 0, 0, 0, 5, -40, 680, -3240, 469755, -1965080, 14338629500, -8710388642800],
   [0, 0, 0, 0, 0, 15, -175, 1235, -146870, 602245, -4437286975, 2993705585075],
   [0, 0, 0, 0, 0, 0, 20, -402, 31344, -117004, -298654725, -431716858410],
   [0, 0, 0, 0, 0, 0, 0, 66, -4017, 13797, 197051700, 24091524705],
   [0, 0, 0, 0, 0, 0, 0, 0, 369, -4264, 914056708, -320436623312],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 205, -115210085, 51890901185],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7606141, -5946419726],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 363718491]]

private def uT4U3_142Tbl : List (List Int) :=
  [[1, 0, 0, 0, -2, 46, -3088, 46368, 30240, -104544, -12751402320, -93625714944],
   [0, 1, 0, 0, -6, 78, -3316, 33948, 12924, -71604, -6579774828, -966102797268],
   [0, 0, 1, 0, -18, 54, 2104, -43992, -61848, 131400, 17477277336, -133991827128],
   [0, 0, 0, 1, 29, -202, 2480, 9144, 76536, -90216, -14679135576, 826531212888],
   [0, 0, 0, 0, 2, -46, 3088, -46368, -30352, 104848, 12707761703, 141119621874],
   [0, 0, 0, 0, 0, 15, -1487, 26289, 19113, -59723, -7977592852, 252625761063],
   [0, 0, 0, 0, 0, 0, 362, -10602, -9306, 25710, 3603590506, -186785300970],
   [0, 0, 0, 0, 0, 0, 0, 2462, 1710, -5674, -778294888, 44009745858],
   [0, 0, 0, 0, 0, 0, 0, 0, 112, -304, 43640617, -47493906930],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 32, -17984258, 15290593209],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3011534, -3374585550],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 389559446]]

private theorem t4u3_351_cert :
    checkULDet12Bool (fastMat12T4U3Fn 3 5 1) uT4U3_351Tbl (-1008815432152374000) = true := by decide
private theorem t4u3_581_cert :
    checkULDet12Bool (fastMat12T4U3Fn 5 8 1) uT4U3_581Tbl 16919290838092087296 = true := by decide
private theorem t4u3_352_cert :
    checkULDet12Bool (fastMat12T4U3Fn 3 5 2) uT4U3_352Tbl 177759891811505204469541718468100000000 = true := by decide
private theorem t4u3_142_cert :
    checkULDet12Bool (fastMat12T4U3Fn 1 4 2) uT4U3_142Tbl (-15742910792136445715997717744844800000000) = true := by decide
private theorem t4u3_mod47_cert : checkQ14ProjRootFreeMod47Bool = true := by decide

private def uApow12_w2Tbl : List (List Int) :=
  [[1, 0, 0, 0, -24, 264, -13080, -7920, -1584, 100080, -21424392, 952294320],
   [0, 1, -2, 8, -110, 602, -15662, -11460, -1868, 68604, -449370, 1211538492],
   [0, 0, 1, -6, 75, -483, 17586, 11898, 2130, -109818, 16338699, -1346835114],
   [0, 0, 0, 1, -13, 67, -3172, -2094, -382, 21846, -3965049, 242069526],
   [0, 0, 0, 0, 24, -264, 13080, 7920, 1576, -96840, 19152888, -957642840],
   [0, 0, 0, 0, 0, 114, -9927, -5402, -1234, 99706, -28565342, 692415306],
   [0, 0, 0, 0, 0, 0, 1623, 627, 203, -23799, 9291132, -82235835],
   [0, 0, 0, 0, 0, 0, 0, 47, -1, 1157, -762397, -6519843],
   [0, 0, 0, 0, 0, 0, 0, 0, 8, -3240, 2271504, 5348520],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 864, -1021176, -4615402],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 99813, -748869],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 336019]]
private theorem apow12_w2_cert :
    checkULDet12Bool (apow12FastFn 2) uApow12_w2Tbl (1498836300870466833408) = true ∧
    (1498836300870466833408 : Int) = 1728 * (3888 * (4 * (2 : Int) - 1) * q14T4U3PolyInt (2 : Int) 1) := by decide

private def uApow12_w3Tbl : List (List Int) :=
  [[1, 0, 0, 0, -90, 456, -7224, 373464, -27762228, 1827264, 26286104016, 274186744416],
   [0, 1, -3, 18, -303, 922, -9478, 369786, -24488754, 1280316, 21018489264, 193852566684],
   [0, 0, 1, -9, 139, -495, 6401, -278631, 19544598, -1175610, -17864368110, -177591944934],
   [0, 0, 0, 1, -16, 47, -769, 34791, -2467308, 156714, 2323911906, 23684954094],
   [0, 0, 0, 0, 90, -456, 7224, -373464, 27656694, -1794792, -26142042348, -267655645728],
   [0, 0, 0, 0, 0, 146, -3998, 245664, -19518264, 1448344, 19437577761, 218110582038],
   [0, 0, 0, 0, 0, 0, 464, -40184, 3423229, -285699, -3515999211, -43515314883],
   [0, 0, 0, 0, 0, 0, 0, 1514, -153697, 14393, 153381192, 2234240943],
   [0, 0, 0, 0, 0, 0, 0, 0, 105534, -32472, -144061668, -6531098688],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 6314, -41571789, 2126902698],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11979095, -238319993],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14304053]]
private theorem apow12_w3_cert :
    checkULDet12Bool (apow12FastFn 3) uApow12_w3Tbl (253140258100885372800000) = true ∧
    (253140258100885372800000 : Int) = 1728 * (3888 * (4 * (3 : Int) - 1) * q14T4U3PolyInt (3 : Int) 1) := by decide

private def uApow12_w4Tbl : List (List Int) :=
  [[1, 0, 0, 0, -672, 2592, -40752, 1562976, -23290272, 1114848, -269778718368, 17652005421984],
   [0, 1, -4, 32, -1972, 5092, -57782, 1411356, -19703148, 839652, -189820959642, 11922270948036],
   [0, 0, 1, -12, 687, -2037, 27402, -781686, 11254626, -511542, 119841353847, -7702790632326],
   [0, 0, 0, 1, -59, 149, -2452, 74346, -1077222, 50466, -11972478141, 775918951218],
   [0, 0, 0, 0, 672, -2592, 40752, -1562976, 23229168, -1102992, 265212242892, -17223135515136],
   [0, 0, 0, 0, 0, 660, -17835, 948590, -14728298, 757918, -190695782878, 12807923374254],
   [0, 0, 0, 0, 0, 0, 1611, -147513, 2359167, -128541, 33549005541, -2314770889653],
   [0, 0, 0, 0, 0, 0, 0, 6235, -104677, 5903, -1604027633, 113963207199],
   [0, 0, 0, 0, 0, 0, 0, 0, 61104, -11856, 4566475476, -428869906848],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 1824, -1014535164, 128697096562],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42113970, -11202688635],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 337141265]]
private theorem apow12_w4_cert :
    checkULDet12Bool (apow12FastFn 4) uApow12_w4Tbl (5869824984959079600000000) = true ∧
    (5869824984959079600000000 : Int) = 1728 * (3888 * (4 * (4 : Int) - 1) * q14T4U3PolyInt (4 : Int) 1) := by decide

private def uApow12_w5Tbl : List (List Int) :=
  [[1, 0, 0, 0, -900, 5250, -44970, 1012200, -567692370, 64461600, -123311107955160, -38325449937006000],
   [0, 1, -5, 50, -2440, 10225, -67427, 891500, -482167491, 51496068, -86047230741648, -29051991959836644],
   [0, 0, 1, -15, 687, -3249, 24498, -380736, 209231784, -23043222, 40990070429262, 13289529229758666],
   [0, 0, 0, 1, -47, 194, -1741, 28996, -15991383, 1790574, -3264200286834, -1041089281304202],
   [0, 0, 0, 0, 900, -5250, 44970, -1012200, 566730780, -64054620, 120947941909890, 38289878007312600],
   [0, 0, 0, 0, 0, 1110, -16296, 573790, -330085847, 39172952, -81775381943941, -23795426282964882],
   [0, 0, 0, 0, 0, 0, 1206, -82191, 47961603, -5863113, 13105223559549, 3583123876071693],
   [0, 0, 0, 0, 0, 0, 0, 3281, -1951486, 241771, -575014208648, -147781806342861],
   [0, 0, 0, 0, 0, 0, 0, 0, 961590, -406980, 2363166045270, 35571929693400],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 51870, -555412530615, 142586120673362],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28264330215, -30771885042393],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1460564248801]]
private theorem apow12_w5_cert :
    checkULDet12Bool (apow12FastFn 5) uApow12_w5Tbl (40042299149080995303263232) = true ∧
    (40042299149080995303263232 : Int) = 1728 * (3888 * (4 * (5 : Int) - 1) * q14T4U3PolyInt (5 : Int) 1) := by decide

private def uApow12_w6Tbl : List (List Int) :=
  [[1, 0, 0, 0, -3960, 36120, -3972696, 249618096, -9363921360, 293807472, -63371774074824, -4741983060962544],
   [0, 1, -6, 72, -10194, 70186, -6205658, 219004716, -8064795852, 245488740, -44857413246690, -5659549258736196],
   [0, 0, 1, -18, 2411, -18469, 1823110, -75209742, 2790494610, -86120502, 16845621972039, 1741696823870838],
   [0, 0, 0, 1, -137, 933, -107276, 4753050, -176670126, 5497482, -1106997714189, -103892790924666],
   [0, 0, 0, 0, 3960, -36120, 3972696, -249618096, 9354873528, -292806696, 62132221854612, 5413641501570120],
   [0, 0, 0, 0, 0, 6530, -1228909, 133875390, -5093859138, 163795526, -39785973166122, -1295189993426070],
   [0, 0, 0, 0, 0, 0, 77053, -17625137, 675067603, -22021881, 5795207756982, -469527766155],
   [0, 0, 0, 0, 0, 0, 0, 645803, -24927913, 817531, -229420897257, 6331240186005],
   [0, 0, 0, 0, 0, 0, 0, 0, 9047832, -1000776, 1239552220212, -671658440607576],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 108928, -280612336236, 306294716247990],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13777495915, -36942135653461],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1282373908699]]
private theorem apow12_w6_cert :
    checkULDet12Bool (apow12FastFn 6) uApow12_w6Tbl (-54207836286886853678822400) = true ∧
    (-54207836286886853678822400 : Int) = 1728 * (3888 * (4 * (6 : Int) - 1) * q14T4U3PolyInt (6 : Int) 1) := by decide

private def uApow12_w7Tbl : List (List Int) :=
  [[1, 0, 0, 0, -3822, 119952, -3773280, 565745040, -297932985756, 7991948160, -5154410651551404768, 73146129966103521600],
   [0, 1, -7, 98, -9485, 233086, -6079954, 498099270, -260527492302, 6912380028, -3715731105025546800, -2206430735078034972],
   [0, 0, 1, -21, 1935, -52299, 1497567, -142123707, 74527808670, -1986402906, 1141745584137940746, -5978905369047860346],
   [0, 0, 0, 1, -94, 2291, -75119, 7652751, -4015629408, 107344122, -63608200371249606, 496142309053004994],
   [0, 0, 0, 0, 3822, -119952, 3773280, -565745040, 297817340814, -7981439760, 5054379033111352392, -52326019998309294720],
   [0, 0, 0, 0, 0, 18942, -1018419, 289987658, -153578387596, 4159964312, -3092675949272184083, 85199933174064138954],
   [0, 0, 0, 0, 0, 0, 55401, -35213493, 18691271997, -508868283, 411603832119070653, -15106262915396293965],
   [0, 0, 0, 0, 0, 0, 0, 1179757, -627727109, 17117569, -14729374467097768, 646810039168591833],
   [0, 0, 0, 0, 0, 0, 0, 0, 115644942, -10508400, 100031618440052376, -20820109967794226880],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 998298, -21427094216475129, 8252144999356457782],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 981225591626847, -869650266831966231],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26468894201728931]]
private theorem apow12_w7_cert :
    checkULDet12Bool (apow12FastFn 7) uApow12_w7Tbl (-3334953981095407615945208832) = true ∧
    (-3334953981095407615945208832 : Int) = 1728 * (3888 * (4 * (7 : Int) - 1) * q14T4U3PolyInt (7 : Int) 1) := by decide

private def uApow12_w8Tbl : List (List Int) :=
  [[1, 0, 0, 0, -13440, 475776, -67422816, 1956764736, 2065610668608, -20750855616, -3252546654429192192, 180585883433444375232],
   [0, 1, -8, 128, -32456, 925352, -111304262, 1733208804, 1832008817004, -18442348404, -2386239401033992890, 70230634707235969692],
   [0, 0, 1, -24, 5823, -180885, 23588154, -421414074, -445233056418, 4478502510, 617574730726584279, -23854967757704352042],
   [0, 0, 0, 1, -247, 6997, -1030516, 19728054, 20840558358, -209516826, -29787508421426205, 1275420334403565486],
   [0, 0, 0, 0, 13440, -475776, 67422816, -1956764736, -2065775303904, 20756292768, 3190495639533912936, -154165498773704675136],
   [0, 0, 0, 0, 0, 66696, -16141827, 966042226, 1018601924954, -10212425926, -1879500568991279002, 152232834804017067234],
   [0, 0, 0, 0, 0, 0, 775491, -108712551, -114580908999, 1147705161, 229998952318200543, -22238641595095497171],
   [0, 0, 0, 0, 0, 0, 0, 3339221, 3518052877, -35229347, -7483713278618729, 811725741263671425],
   [0, 0, 0, 0, 0, 0, 0, 0, 164635296, -5437152, 62051014895279256, -26420384659739700096],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 458304, -12530822347830696, 9760685489002530622],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 531796831593636, -939328263596023005],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25890629130830543]]
private theorem apow12_w8_cert :
    checkULDet12Bool (apow12FastFn 8) uApow12_w8Tbl (-37903994450280915184070784000) = true ∧
    (-37903994450280915184070784000 : Int) = 1728 * (3888 * (4 * (8 : Int) - 1) * q14T4U3PolyInt (8 : Int) 1) := by decide

private def uApow12_w9Tbl : List (List Int) :=
  [[1, 0, 0, 0, -11016, 14472, -228114, 12923496, 27894030, -2032800, -208458974952, 500925328272],
   [0, 1, -9, 162, -26046, 28182, -383959, 11523876, 25052649, -1846572, -155361829680, 242513708724],
   [0, 0, 1, -27, 4171, -4879, 71378, -2435292, -5281854, 387762, 34636287438, -63312044850],
   [0, 0, 0, 1, -157, 169, -2761, 100704, 218271, -15978, -1470567186, 2871771138],
   [0, 0, 0, 0, 11016, -14472, 228114, -12923496, -27907002, 2035836, 204560362782, -441685964664],
   [0, 0, 0, 0, 0, 1824, -49073, 6182022, 13253795, -954760, -116715739205, 382875582330],
   [0, 0, 0, 0, 0, 0, 2111, -647779, -1385868, 99339, 13211415633, -49824424161],
   [0, 0, 0, 0, 0, 0, 0, 18325, 39127, -2801, -393414040, 1623256569],
   [0, 0, 0, 0, 0, 0, 0, 0, 12972, -3036, 3898612170, -59239363608],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 230, -742593511, 20834446086],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29226771, -1860423043],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47105731]]
private theorem apow12_w9_cert :
    checkULDet12Bool (apow12FastFn 9) uApow12_w9Tbl (-295994838786916277106000000000) = true ∧
    (-295994838786916277106000000000 : Int) = 1728 * (3888 * (4 * (9 : Int) - 1) * q14T4U3PolyInt (9 : Int) 1) := by decide

private def uApow12_w10Tbl : List (List Int) :=
  [[1, 0, 0, 0, -34200, 1485000, -257731320, 28661094000, 5421506071920, -101562872400, -113666268240618116760, 87209899311729173562000],
   [0, 1, -10, 200, -79510, 2895650, -440752046, 25726526580, 4923257234188, -93926226468, -85891037068091387214, 46314738776372307703812],
   [0, 0, 1, -30, 11499, -449787, 72959154, -4800254418, -915363328242, 17359697142, 16789269315231740961, -10152103568756457017718],
   [0, 0, 0, 1, -389, 14107, -2531428, 177594198, 33830562494, -638721114, -635916052383823467, 404385936853734534186],
   [0, 0, 0, 0, 34200, -1485000, 257731320, -28661094000, -5425775044680, 101814935640, 111582839453130925440, -77958922126310620540200],
   [0, 0, 0, 0, 0, 170010, -50339943, 13346482130, 2496013939026, -45849942422, -61958009510491167458, 63088426234827222512406],
   [0, 0, 0, 0, 0, 0, 1960503, -1307952183, -243821040459, 4444353153, 6522214770793622112, -7479845710132016800629],
   [0, 0, 0, 0, 0, 0, 0, 34243933, 6365047713, -115805251, -178853634954412519, 221243607818656938723],
   [0, 0, 0, 0, 0, 0, 0, 0, 4268972760, -252063240, 2083428787487191320, -9250977185418553021800],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 17340960, -375003072826255440, 3129829887710870759434],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13727486497362315, -261616821323492597451],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6138955163565402797]]
private theorem apow12_w10_cert :
    checkULDet12Bool (apow12FastFn 10) uApow12_w10Tbl (-1835140059659522710152057811968) = true ∧
    (-1835140059659522710152057811968 : Int) = 1728 * (3888 * (4 * (10 : Int) - 1) * q14T4U3PolyInt (10 : Int) 1) := by decide

private def uApow12_w11Tbl : List (List Int) :=
  [[1, 0, 0, 0, -25410, 1205160, -57095016, 4691512584, 1303337339172, -199740518208, -98999722099392819408, 5863165428690832759200],
   [0, 1, -11, 242, -58267, 2353054, -98938618, 4237474314, 1195032642330, -187501007580, -75714557831118081360, 3288888193661215355916],
   [0, 0, 1, -33, 7683, -331401, 14758515, -707067243, -198544304358, 30929333418, 13161951572829848730, -626067280062012529854],
   [0, 0, 0, 1, -236, 9497, -464171, 23650755, 6632514564, -1027465338, -449635508698701078, 22286145886605667782],
   [0, 0, 0, 0, 25410, -1205160, 57095016, -4691512584, -1304719930470, 200398173624, 97219900549105652076, -5281695696786965412000],
   [0, 0, 0, 0, 0, 126390, -10211904, 2134641980, 583980355600, -87156708184, -52735277049832718651, 4083419023607207942510],
   [0, 0, 0, 0, 0, 0, 363318, -196435158, -53526235725, 7911944859, 5187464611859971521, -446285589972734955375],
   [0, 0, 0, 0, 0, 0, 0, 4782292, 1298639465, -191537729, -131738605803295096, 12108995219055107035],
   [0, 0, 0, 0, 0, 0, 0, 0, 1382591298, -657655416, 1779821550287167332, -581469731903867347200],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 41437638, -303420587601999681, 190477895992217282002],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10367409580490523, -14993281803586112637],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 328152784532922329]]
private theorem apow12_w11_cert :
    checkULDet12Bool (apow12FastFn 11) uApow12_w11Tbl (-9496570519903884880244457600000) = true ∧
    (-9496570519903884880244457600000 : Int) = 1728 * (3888 * (4 * (11 : Int) - 1) * q14T4U3PolyInt (11 : Int) 1) := by decide

private def uApow12_w12Tbl : List (List Int) :=
  [[1, 0, 0, 0, -72864, 1249248, -256666800, 34726255200, 28975206514464, -41115678240, -147983941260530380512, 207375568417423142736480],
   [0, 1, -12, 288, -165180, 2442164, -449768834, 31546514100, 26793179079348, -39086767092, -114374777350557661830, 120783265560566836245972],
   [0, 0, 1, -36, 20015, -314571, 61049662, -4757060466, -4020906980430, 5819683854, 17887585140450172089, -20370189231061195792734],
   [0, 0, 0, 1, -563, 8299, -1755644, 145123278, 122483607882, -176157258, -556191555196817619, 655899069397912664346],
   [0, 0, 0, 0, 72864, -1249248, 256666800, -34726255200, -29012742377136, 41278888560, 145371414533563759788, -187742973343861587712320],
   [0, 0, 0, 0, 0, 120868, -42339409, 15485009274, 12680087831334, -17418550198, -77269491649578367482, 140318415807869354977446],
   [0, 0, 0, 0, 0, 0, 1386481, -1342899059, -1094738952473, 1487422497, 7132790574081632727, -14248018966227018386985],
   [0, 0, 0, 0, 0, 0, 0, 30534281, 24798503171, -33614171, -168605439062721807, 357323719273245250347],
   [0, 0, 0, 0, 0, 0, 0, 0, 37535862672, -163210320, 2612526726966620724, -19632595073561555024160],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 9485728, -422838873164434236, 6255634178851334749818],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13534476066899978, -465794670529757386759],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9557179963457856709]]
private theorem apow12_w12_cert :
    checkULDet12Bool (apow12FastFn 12) uApow12_w12Tbl (-42248222740702331945563713795072) = true ∧
    (-42248222740702331945563713795072 : Int) = 1728 * (3888 * (4 * (12 : Int) - 1) * q14T4U3PolyInt (12 : Int) 1) := by decide

private def uApow12_w13Tbl : List (List Int) :=
  [[1, 0, 0, 0, -50700, 702702, -155591982, 91694827224, 45255480646662, -652090604256, -29078343090399445128, 5156700980756347131408],
   [0, 1, -13, 338, -113828, 1375309, -275271169, 83738564196, 42160523904921, -626652857964, -22682804691274645680, 3088997095713802861788],
   [0, 0, 1, -39, 12759, -163200, 34275198, -11512250136, -5766640045812, 85001594130, 3222260814325344786, -468097814479123368918],
   [0, 0, 0, 1, -331, 3989, -907847, 322686516, 161377196217, -2362487226, -91898189792759790, 13761562032847252854],
   [0, 0, 0, 0, 50700, -702702, 155591982, -91694827224, -45323315755536, 655053288708, 28573592878006841574, -4685015385092829130344],
   [0, 0, 0, 0, 0, 63102, -23815794, 40170387394, 19398906871681, -269189437256, -14920047932078078443, 3409364403212387869326],
   [0, 0, 0, 0, 0, 0, 722412, -3293728449, -1582962032631, 21706127331, 1297340683356395307, -323550044794984851459],
   [0, 0, 0, 0, 0, 0, 0, 70225679, 33618355868, -459858457, -28673611252984856, 7545671622160408275],
   [0, 0, 0, 0, 0, 0, 0, 0, 67835108874, -2962684452, 504750212392603554, -471685595663518001064],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 159794934, -77739450126550329, 146701000612492585138],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2339138072278449, -10370815580173966665],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 200326312968630977]]
private theorem apow12_w13_cert :
    checkULDet12Bool (apow12FastFn 13) uApow12_w13Tbl (-165279638753453769907378536576000) = true ∧
    (-165279638753453769907378536576000 : Int) = 1728 * (3888 * (4 * (13 : Int) - 1) * q14T4U3PolyInt (13 : Int) 1) := by decide

private def uApow12_w14Tbl : List (List Int) :=
  [[1, 0, 0, 0, -137592, 1635816, -77664552, 1375199952, 2853148125744, -8810429040, -3367859833558505880, 4409832154113693900432],
   [0, 1, -14, 392, -306362, 3205006, -138545342, 1261921124, 2675627438820, -8546374164, -2648626476480598902, 2700584135319213898956],
   [0, 0, 1, -42, 31947, -352539, 15932898, -159346746, -336080490102, 1064347902, 344527499471217165, -371695366912308887970],
   [0, 0, 0, 1, -769, 8027, -391108, 4129822, 8695426026, -27340386, -9071869895546511, 10053388890305753166],
   [0, 0, 0, 0, 137592, -1635816, 77664552, -1375199952, -2857932961800, 8854797672, 3310306246456412532, -4017106703773204322904],
   [0, 0, 0, 0, 0, 137046, -11088447, 593086250, 1200821918246, -3554605166, -1701586462866031190, 2860079764703132533314],
   [0, 0, 0, 0, 0, 0, 313263, -46112955, -92896872777, 271561941, 139838903065155726, -254893270729792860927],
   [0, 0, 0, 0, 0, 0, 0, 925273, 1856574667, -5413807, -2901508139924755, 5556077850585358833],
   [0, 0, 0, 0, 0, 0, 0, 0, 4784836056, -44368632, 57553587102093348, -392725450340489577528],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 2232384, -8453570282840844, 119551425709487741150],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 239888171480517, -8048639241980799009],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 146895477086325439]]
private theorem apow12_w14_cert :
    checkULDet12Bool (apow12FastFn 14) uApow12_w14Tbl (-579224379546953651459480400000000) = true ∧
    (-579224379546953651459480400000000 : Int) = 1728 * (3888 * (4 * (14 : Int) - 1) * q14T4U3PolyInt (14 : Int) 1) := by decide

private def uApow12_w15Tbl : List (List Int) :=
  [[1, 0, 0, 0, -91350, 1932000, -122373120, 41946645600, 6568256879220, -11720236800, -20343444129321180480, 1572566370937667856000],
   [0, 1, -15, 450, -201945, 3789050, -219885934, 38660210130, 6195886885962, -11462365596, -16115060107207312848, 980511912630784841796],
   [0, 0, 1, -45, 19687, -388397, 23491541, -4512492909, -719324103378, 1319285514, 1932630706043145342, -123636173230804858794],
   [0, 0, 0, 1, -442, 8277, -537277, 108729249, 17301648456, -31497738, -47250945277947954, 3096238174821483858],
   [0, 0, 0, 0, 91350, -1932000, 122373120, -41946645600, -6580304283330, 11784268320, 20000775053471206320, -1435502497765195929600],
   [0, 0, 0, 0, 0, 151690, -16370987, 17839372170, 2719694426844, -4632961624, -10138382491926165321, 1003404285169078112058],
   [0, 0, 0, 0, 0, 0, 432797, -1318741829, -200013688211, 336333171, 789839527649623119, -84317889713681695077],
   [0, 0, 0, 0, 0, 0, 0, 24984569, 3774228947, -6330857, -15440770946530968, 1725335548715303169],
   [0, 0, 0, 0, 0, 0, 0, 0, 12047404110, -64031520, 342669075849974160, -137063873172471926400],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 3019030, -48098997795334395, 40931118442387404102],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1291090947459845, -2631212206994150303],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45517133832373211]]
private theorem apow12_w15_cert :
    checkULDet12Bool (apow12FastFn 15) uApow12_w15Tbl (-1846461378125805908202802914259968) = true ∧
    (-1846461378125805908202802914259968 : Int) = 1728 * (3888 * (4 * (15 : Int) - 1) * q14T4U3PolyInt (15 : Int) 1) := by decide

private def uApow12_w16Tbl : List (List Int) :=
  [[1, 0, 0, 0, -238080, 16058880, -393204288, 10302574464, 448065910656, -36732749184, -180880717827605760, 8932667777421598080],
   [0, 1, -16, 512, -523024, 31523408, -711048274, 9533366844, 424892737236, -36184474500, -144212167649219598, 5653845248891059548],
   [0, 0, 1, -48, 47871, -3025197, 70926510, -1034265078, -45848150334, 3870856134, 16039497970046997, -657810754924899978],
   [0, 0, 0, 1, -1007, 60589, -1518428, 23279610, 1030105770, -86315394, -365919568719111, 15336224245517166],
   [0, 0, 0, 0, 238080, -16058880, 393204288, -10302574464, -448950325824, 36947184192, 177874256610753072, -8167847430398655360],
   [0, 0, 0, 0, 0, 1186320, -49485417, 4326968350, 182835319334, -14256666142, -89044748655663142, 5619824316096339650],
   [0, 0, 0, 0, 0, 0, 1229289, -304848753, -12814100409, 986056557, 6594023512234857, -446826147378524835],
   [0, 0, 0, 0, 0, 0, 0, 5469587, 228993619, -17578127, -121848975920987, 8615581890599425],
   [0, 0, 0, 0, 0, 0, 0, 0, 884415168, -214435008, 3006461216852688, -764820347022942720],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 9512064, -404053049231664, 224477573430666974],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10287343632984, -13810692345952461],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 227081909055823]]
private theorem apow12_w16_cert :
    checkULDet12Bool (apow12FastFn 16) uApow12_w16Tbl (-5422417212499092574238636191872000) = true ∧
    (-5422417212499092574238636191872000 : Int) = 1728 * (3888 * (4 * (16 : Int) - 1) * q14T4U3PolyInt (16 : Int) 1) := by decide

private def uApow12_w17Tbl : List (List Int) :=
  [[1, 0, 0, 0, -152592, 5451696, -777728070, 202656376440, 524737540401318, -4338585430560, -841277103115325074480728, 1527467988623923508586257520],
   [0, 1, -17, 578, -333370, 10710578, -1414384909, 188210948220, 499958607302421, -4301268119628, -674624342269739540028240, 979222128374701742178608604],
   [0, 0, 1, -51, 28755, -966207, 132305742, -19070032428, -50385291648210, 429767988066, 69943004261574283656666, -105759536832963356987286198],
   [0, 0, 0, 1, -569, 18253, -2662139, 402654744, 1061919571719, -8989086522, -1495394911329586515846, 2306291647101971188135302],
   [0, 0, 0, 0, 152592, -5451696, 777728070, -202656376440, -525838848768222, 4365347306220, 827465174088064874960562, -1398637603125799341047098920],
   [0, 0, 0, 0, 0, 380256, -92403069, 84156426002, 211316174540003, -1656279105352, -409600725325760370387223, 949185639634649801538529422],
   [0, 0, 0, 0, 0, 0, 2164791, -5663184297, -14145562565586, 109398632163, 28902697065236814059763, -71624319228681805371860595],
   [0, 0, 0, 0, 0, 0, 0, 96485743, 240053150677, -1852046009, -506313252792237394088, 1305729684245926944161739],
   [0, 0, 0, 0, 0, 0, 0, 0, 1101308366904, -26761875660, 13811929027260199520166, -128830385498124167539158600],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 1120796502, -1780441069545521744109, 37222774588276246004307826],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 43105187904508185177, -2196267363442738047303993],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34410194845369453609193]]
private theorem apow12_w17_cert :
    checkULDet12Bool (apow12FastFn 17) uApow12_w17Tbl (-14823490740306571048796151142413312) = true ∧
    (-14823490740306571048796151142413312 : Int) = 1728 * (3888 * (4 * (17 : Int) - 1) * q14T4U3PolyInt (17 : Int) 1) := by decide

private def uApow12_w18Tbl : List (List Int) :=
  [[1, 0, 0, 0, -385560, 9697752, -2921909832, 606147150096, 392592268514832, -240477600048, -246706955217002416104, 22963269235309857516528],
   [0, 1, -18, 648, -838206, 19067214, -5340777914, 564824372124, 375656104791396, -239776629612, -198870214855943562930, 14884435242904428394668],
   [0, 0, 1, -54, 68363, -1622705, 470321638, -53675723574, -35508873804342, 22473190050, 19305953390653960383, -1500014322286164737298],
   [0, 0, 0, 1, -1277, 29009, -8926412, 1067120034, 704651538042, -442577838, -388316793728841525, 30722819527349298414],
   [0, 0, 0, 0, 385560, -9697752, 2921909832, -606147150096, -393460359320376, 242031680424, 242702466611969144232, -21051336919493171137464],
   [0, 0, 0, 0, 0, 640662, -328766509, 249145367766, 156221585259766, -90437710818, -118923107175169349974, 14114603996086690247346],
   [0, 0, 0, 0, 0, 0, 7287517, -16046096981, -10008573760161, 5716689363, 8013930552361303476, -1013546094652138509639],
   [0, 0, 0, 0, 0, 0, 0, 260239751, 161691724163, -92136921, -133439326714647593, 17521789243268300625],
   [0, 0, 0, 0, 0, 0, 0, 0, 868090805544, -1554080376, 4004488605033271872, -1911932315816686379064],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 61641632, -495934348335980552, 544547790406114652718],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11443686489543097, -30870869807517023545],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 461918661486841567]]
private theorem apow12_w18_cert :
    checkULDet12Bool (apow12FastFn 18) uApow12_w18Tbl (-38053088332968453959222458888320000) = true ∧
    (-38053088332968453959222458888320000 : Int) = 1728 * (3888 * (4 * (18 : Int) - 1) * q14T4U3PolyInt (18 : Int) 1) := by decide

private def uApow12_w19Tbl : List (List Int) :=
  [[1, 0, 0, 0, -240426, 3820824, -60613800, 26605201896, 7707501001284, -76045620672, -393238235034097169616, 188085921212718317687328],
   [0, 1, -19, 722, -520391, 7517654, -111297490, 24867601662, 7403683324858, -76214788044, -318489802644091986288, 123095126783560064425380],
   [0, 0, 1, -57, 40251, -605505, 9258555, -2224765269, -658881896286, 6726142098, 29065233067360980534, -11627227020837881133882],
   [0, 0, 0, 1, -712, 10273, -166283, 41784549, 12352105196, -125140098, -551869567748019162, 224490335435090901234],
   [0, 0, 0, 0, 240426, -3820824, 60613800, -26605201896, -7725327136254, 76557090792, 386922375396482629548, -172600734750409267761888],
   [0, 0, 0, 0, 0, 239742, -6477030, 10833937352, 3033791538568, -28210934584, -187844726730853260061, 114487477016105962395018],
   [0, 0, 0, 0, 0, 0, 136236, -669028476, -186367045929, 1709882487, 12113271991751811663, -7842373836636843763533],
   [0, 0, 0, 0, 0, 0, 0, 10352074, 2872727021, -26295893, -192176361323100008, 128910133610791144065],
   [0, 0, 0, 0, 0, 0, 0, 0, 17826134970, -511470120, 6315859637614540068, -15485186462309049925440],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 19267710, -752620240616650407, 4352815276525738770614],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16587413046771573, -237490277052274307895],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3400685181416804827]]
private theorem apow12_w19_cert :
    checkULDet12Bool (apow12FastFn 19) uApow12_w19Tbl (-92399209299951972039632754000000000) = true ∧
    (-92399209299951972039632754000000000 : Int) = 1728 * (3888 * (4 * (19 : Int) - 1) * q14T4U3PolyInt (19 : Int) 1) := by decide

private def uApow12_w20Tbl : List (List Int) :=
  [[1, 0, 0, 0, -592800, 49476000, -16488701040, 1272263882400, 3072852351721440, -13644992037600, -519854494724196945216480, 938277512433637788916764000],
   [0, 1, -20, 800, -1278020, 97410500, -30400911686, 1192533664980, 2962185976585428, -13739034013908, -422850945180255255427086, 619313887313480922753774636],
   [0, 0, 1, -60, 93999, -7446777, 2396296314, -100776372066, -249025170001662, 1145559414942, 36403979979052193508549, -55046086056297150724867554],
   [0, 0, 0, 1, -1579, 120217, -40842868, 1793414526, 4423539496314, -20195874714, -654499533905681396823, 1005112627366710376742598],
   [0, 0, 0, 0, 592800, -49476000, 16488701040, -1272263882400, -3080243184340560, 13740002171280, 511586583679758084616020, -861788437838903197284278400],
   [0, 0, 0, 0, 0, 2956020, -1677551283, 513674871050, 1197543003619766, -4999070259622, -246278851921762965379402, 566145350728246365311898138],
   [0, 0, 0, 0, 0, 0, 33570003, -30466543371, -70659244221489, 291041919273, 15225795367652867324103, -37074807652481913105510327],
   [0, 0, 0, 0, 0, 0, 0, 450691441, 1041361151083, -4279651091, -230658706062780002771, 580861462680347339387589],
   [0, 0, 0, 0, 0, 0, 0, 0, 7390832619120, -95010133680, 8267911044438860600460, -76489074594734591632485600],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 3407908320, -949339315392051432420, 21242034790771136541025862],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20023182125420705070, -1117110953316400851186393],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15336710967291708545611]]
private theorem apow12_w20_cert :
    checkULDet12Bool (apow12FastFn 20) uApow12_w20Tbl (-213521891344886683283653873885344768) = true ∧
    (-213521891344886683283653873885344768 : Int) = 1728 * (3888 * (4 * (20 : Int) - 1) * q14T4U3PolyInt (20 : Int) 1) := by decide

private theorem fastMat12T4U3Fn_eq (W K u : Nat) :
    fastMat12T4U3Fn W K u = laurentTwoBaseT4U3Mat12 W K u := by
  funext i j
  unfold fastMat12T4U3Fn laurentTwoBaseT4U3Mat12 laurentInterpMat laurentInterpEntry
    laurentRowsTwoBase12 laurentColsT4U3_12
  dsimp only
  rw [fastBinom3W17_eq_laurentInterpBinom _ _ (Nat.mod_lt j.val (by decide)),
      ← Nat.mul_assoc (laurentInterpBinom _ _)]

private def apow12U_w17 (u : Nat) (w k : Int) (i j : Fin 12) : Int :=
  let r := (laurentRowsTwoBase12 i).1
  let s := (laurentRowsTwoBase12 i).2
  let t := j.val % 4
  let m := (j.val / 4) * u
  intPowNat ((r : Int) * w + (s : Int) * k) t *
    ((2 ^ (r * m) * 3 ^ (s * m) : Nat) : Int)

private theorem stirling_1728_det12_t4u3_u_w17 (u W K : Nat) :
    1728 * intDet 12 (laurentTwoBaseT4U3Mat12 W K u) =
      intDet 12 (apow12U_w17 u (W : Int) (K : Int)) := by
  have hbinom_stirling : ∀ x : Nat,
      laurentInterpBinom x 0 = 1 ∧
      laurentInterpBinom x 1 = x ∧
      2 * laurentInterpBinom x 2 + x = x * x ∧
      6 * laurentInterpBinom x 3 + 3 * (x * x) = x * x * x + 2 * x := by
    intro x; induction x with
    | zero => decide
    | succ x' ih =>
      rcases ih with ⟨h0, h1, h2, h3⟩
      refine ⟨rfl, ?_, ?_, ?_⟩
      · simp [laurentInterpBinom, h0, h1]; omega
      · simp only [laurentInterpBinom, h1]
        change 2 * (x' + laurentInterpBinom x' 2) + (x' + 1) = (x' + 1) * (x' + 1)
        rw [Nat.mul_add 2 x' (laurentInterpBinom x' 2),
            show (x' + 1) * (x' + 1) = x' * x' + 2 * x' + 1 by
              simp only [Nat.add_mul, Nat.mul_add]; omega]
        omega
      · simp only [laurentInterpBinom]
        change 6 * (laurentInterpBinom x' 2 + laurentInterpBinom x' 3) + 3 * ((x' + 1) * (x' + 1)) =
          (x' + 1) * (x' + 1) * (x' + 1) + 2 * (x' + 1)
        rw [Nat.mul_add 6 (laurentInterpBinom x' 2) (laurentInterpBinom x' 3)]
        have h6c2 : 6 * laurentInterpBinom x' 2 = 3 * (2 * laurentInterpBinom x' 2) :=
          Nat.mul_assoc 3 2 _
        have hsq : (x' + 1) * (x' + 1) = x' * x' + 2 * x' + 1 := by
          simp only [Nat.add_mul, Nat.mul_add]; omega
        have hcub : (x' + 1) * (x' + 1) * (x' + 1) = x' * x' * x' + 3 * (x' * x') + 3 * x' + 1 := by
          rw [hsq]
          simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul, Nat.mul_assoc 2 x' x']
          generalize x' * x' * x' = X3; generalize x' * x' = X2; omega
        rw [h6c2, hcub, hsq, Nat.mul_add 3 (x' * x' + 2 * x') 1, Nat.mul_add 3 (x' * x') (2 * x')]
        generalize 6 * laurentInterpBinom x' 3 = C3 at h3 ⊢
        generalize 2 * laurentInterpBinom x' 2 = C2 at h2 ⊢
        generalize x' * x' * x' = X3 at h3 ⊢
        generalize x' * x' = X2 at h2 h3 ⊢
        omega
  let blkDoneU (b_done : Nat) (i j : Fin 12) : Int :=
    if j.val / 4 < b_done then apow12U_w17 u (W : Int) (K : Int) i j
    else laurentTwoBaseT4U3Mat12 W K u i j
  have hblk_stepU : ∀ m : Nat, m < 3 ->
      12 * intDet 12 (blkDoneU m) = intDet 12 (blkDoneU (m + 1)) := by
    intro m hm3
    let c1 : Fin 12 := ⟨4 * m + 1, by omega⟩
    let c2 : Fin 12 := ⟨4 * m + 2, by omega⟩
    let c3 : Fin 12 := ⟨4 * m + 3, by omega⟩
    let B0 := blkDoneU m
    let B1 : Fin 12 -> Fin 12 -> Int := fun i j => if j = c2 then 2 * B0 i c2 else B0 i j
    let B2 : Fin 12 -> Fin 12 -> Int := fun i j => if j = c3 then 6 * B1 i c3 else B1 i j
    have hd1 : intDet 12 B1 = 2 * intDet 12 B0 := intDet_col_scale 2 12 c2 B0
    have hd2 : intDet 12 B2 = 6 * intDet 12 B1 := intDet_col_scale 6 12 c3 B1
    let B3 : Fin 12 -> Fin 12 -> Int := fun i j => if j = c2 then B2 i c2 - (-1) * B2 i c1 else B2 i j
    have hd3 : intDet 12 B3 = intDet 12 B2 :=
      intDet_sub_col_mul_other 12 c2 c1 (by dsimp [c1, c2]; intro h; have := congrArg Fin.val h; dsimp at this; omega) (-1) B2
    let B4 : Fin 12 -> Fin 12 -> Int := fun i j => if j = c3 then B3 i c3 - (-3) * B3 i c2 else B3 i j
    have hd4 : intDet 12 B4 = intDet 12 B3 :=
      intDet_sub_col_mul_other 12 c3 c2 (by dsimp [c2, c3]; intro h; have := congrArg Fin.val h; dsimp at this; omega) (-3) B3
    let B5 : Fin 12 -> Fin 12 -> Int := fun i j => if j = c3 then B4 i c3 - 2 * B4 i c1 else B4 i j
    have hd5 : intDet 12 B5 = intDet 12 B4 :=
      intDet_sub_col_mul_other 12 c3 c1 (by dsimp [c1, c3]; intro h; have := congrArg Fin.val h; dsimp at this; omega) 2 B4
    have hB5_eq : B5 = blkDoneU (m + 1) := by
      funext i j
      by_cases hjm : j.val / 4 = m
      · have hj_rem : j.val = 4 * m + j.val % 4 := by
          have := Nat.div_add_mod j.val 4; rw [hjm] at this; omega
        let r := (laurentRowsTwoBase12 i).1
        let s := (laurentRowsTwoBase12 i).2
        let x := r * W + s * K
        let E : Int := ((2 ^ (r * (m * u)) * 3 ^ (s * (m * u)) : Nat) : Int)
        have hraw_col : ∀ t : Nat, (ht : t < 4) ->
            B0 i ⟨4 * m + t, by omega⟩ = ((laurentInterpBinom x t : Nat) : Int) * E := by
          intro t ht
          have hdiv_m : (4 * m + t) / 4 = m := by omega
          have hmod_t : (4 * m + t) % 4 = t := by omega
          dsimp [B0, blkDoneU]
          rw [ite_false_of_w10 (by omega : ¬ ((4 * m + t) / 4 < m))]
          unfold laurentTwoBaseT4U3Mat12 laurentInterpMat laurentInterpEntry laurentColsT4U3_12
          dsimp only
          rw [hmod_t, hdiv_m, Nat.mul_assoc (laurentInterpBinom _ _), Int.natCast_mul]
        rcases hbinom_stirling x with ⟨hb0, hb1, hb2, hb3⟩
        have hx_int : ((x : Nat) : Int) = (r : Int) * (W : Int) + (s : Int) * (K : Int) := by
          dsimp only [x]; simp only [Int.natCast_add, Int.natCast_mul]
        rcases (by omega : j.val % 4 = 0 ∨ j.val % 4 = 1 ∨ j.val % 4 = 2 ∨ j.val % 4 = 3) with
          hm0 | hm1 | hm2 | hm3_c
        · let c0_m : Fin 12 := ⟨4 * m + 0, by omega⟩
          have hjf : j = c0_m := Fin.ext (by dsimp [c0_m]; omega)
          rw [hjf]
          have hn2 : c0_m ≠ c2 := by intro h; have := congrArg Fin.val h; dsimp [c0_m, c2] at this; omega
          have hn3 : c0_m ≠ c3 := by intro h; have := congrArg Fin.val h; dsimp [c0_m, c3] at this; omega
          change (if c0_m = c3 then _ else B4 i c0_m) = _; rw [ite_false_of_w10 hn3]
          change (if c0_m = c3 then _ else B3 i c0_m) = _; rw [ite_false_of_w10 hn3]
          change (if c0_m = c2 then _ else B2 i c0_m) = _; rw [ite_false_of_w10 hn2]
          change (if c0_m = c3 then _ else B1 i c0_m) = _; rw [ite_false_of_w10 hn3]
          change (if c0_m = c2 then _ else B0 i c0_m) = _; rw [ite_false_of_w10 hn2]
          dsimp only [c0_m]; rw [hraw_col 0 (by decide)]
          dsimp [blkDoneU]; rw [ite_true_of_w10 (by omega : (4 * m) / 4 < m + 1)]
          dsimp [apow12U_w17]; rw [show (4 * m) % 4 = 0 by omega, show (4 * m) / 4 = m by omega, hb0]
          rw [show ((1 : Nat) : Int) = 1 from rfl]; simp only [intPowNat, Int.one_mul]; rfl
        · have hjf : j = c1 := Fin.ext (by dsimp [c1]; rw [hj_rem, hm1])
          rw [hjf]
          have hn12 : c1 ≠ c2 := by intro h; have := congrArg Fin.val h; dsimp [c1, c2] at this; omega
          have hn13 : c1 ≠ c3 := by intro h; have := congrArg Fin.val h; dsimp [c1, c3] at this; omega
          change (if c1 = c3 then _ else B4 i c1) = _; rw [ite_false_of_w10 hn13]
          change (if c1 = c3 then _ else B3 i c1) = _; rw [ite_false_of_w10 hn13]
          change (if c1 = c2 then _ else B2 i c1) = _; rw [ite_false_of_w10 hn12]
          change (if c1 = c3 then _ else B1 i c1) = _; rw [ite_false_of_w10 hn13]
          change (if c1 = c2 then _ else B0 i c1) = _; rw [ite_false_of_w10 hn12]
          dsimp only [c1]; rw [hraw_col 1 (by decide)]
          dsimp [blkDoneU]; rw [ite_true_of_w10 (by omega : (4 * m + 1) / 4 < m + 1)]
          dsimp [apow12U_w17]; rw [show (4 * m + 1) % 4 = 1 by omega, show (4 * m + 1) / 4 = m by omega, hb1, hx_int]
          simp only [intPowNat, Int.mul_one]; rfl
        · have hjf : j = c2 := Fin.ext (by dsimp [c2]; rw [hj_rem, hm2])
          rw [hjf]
          have hn23 : c2 ≠ c3 := by intro h; have := congrArg Fin.val h; dsimp [c2, c3] at this; omega
          have hn12 : c1 ≠ c2 := by intro h; have := congrArg Fin.val h; dsimp [c1, c2] at this; omega
          have hn13 : c1 ≠ c3 := by intro h; have := congrArg Fin.val h; dsimp [c1, c3] at this; omega
          change (if c2 = c3 then _ else B4 i c2) = _; rw [ite_false_of_w10 hn23]
          change (if c2 = c3 then _ else B3 i c2) = _; rw [ite_false_of_w10 hn23]
          change (if c2 = c2 then B2 i c2 - (-1) * B2 i c1 else _) = _; rw [ite_true_of_w10 rfl]
          have hb2_c2 : B2 i c2 = 2 * B0 i c2 := by dsimp [B2, B1]; rw [ite_false_of_w10 hn23, ite_true_of_w10 rfl]
          have hb2_c1 : B2 i c1 = B0 i c1 := by dsimp [B2, B1]; rw [ite_false_of_w10 hn13, ite_false_of_w10 hn12]
          rw [hb2_c2, hb2_c1]; dsimp only [c1, c2]; rw [hraw_col 2 (by decide), hraw_col 1 (by decide)]
          dsimp [blkDoneU]; rw [ite_true_of_w10 (by omega : (4 * m + 2) / 4 < m + 1)]
          dsimp [apow12U_w17]; rw [show (4 * m + 2) % 4 = 2 by omega, show (4 * m + 2) / 4 = m by omega, hb1]
          have hb2_int : (2 : Int) * (laurentInterpBinom x 2 : Int) - (-1) * (x : Int) = (x : Int) * (x : Int) := by
            have hc := congrArg (fun n : Nat => (n : Int)) hb2
            simp only [Int.natCast_add, Int.natCast_mul] at hc; omega
          calc 2 * ((laurentInterpBinom x 2 : Int) * E) - (-1) * ((x : Int) * E)
              = (2 * (laurentInterpBinom x 2 : Int) - (-1) * (x : Int)) * E := by rw [Int.sub_mul]; ac_rfl
            _ = ((x : Int) * (x : Int)) * E := by rw [hb2_int]
            _ = intPowNat ((r : Int) * (W : Int) + (s : Int) * (K : Int)) 2 * E := by rw [← hx_int]; simp [intPowNat]
        · have hjf : j = c3 := Fin.ext (by dsimp [c3]; rw [hj_rem, hm3_c])
          rw [hjf]
          have hn23 : c2 ≠ c3 := by intro h; have := congrArg Fin.val h; dsimp [c2, c3] at this; omega
          have hn32 : c3 ≠ c2 := Ne.symm hn23
          have hn12 : c1 ≠ c2 := by intro h; have := congrArg Fin.val h; dsimp [c1, c2] at this; omega
          have hn13 : c1 ≠ c3 := by intro h; have := congrArg Fin.val h; dsimp [c1, c3] at this; omega
          have hb2_c3 : B2 i c3 = 6 * B0 i c3 := by dsimp [B2, B1]; rw [ite_true_of_w10 rfl, ite_false_of_w10 hn32]
          have hb2_c2 : B2 i c2 = 2 * B0 i c2 := by dsimp [B2, B1]; rw [ite_false_of_w10 hn23, ite_true_of_w10 rfl]
          have hb2_c1 : B2 i c1 = B0 i c1 := by dsimp [B2, B1]; rw [ite_false_of_w10 hn13, ite_false_of_w10 hn12]
          have hb3_c3 : B3 i c3 = 6 * B0 i c3 := by dsimp [B3]; rw [ite_false_of_w10 hn32, hb2_c3]
          have hb3_c2 : B3 i c2 = 2 * B0 i c2 - (-1) * B0 i c1 := by dsimp [B3]; rw [ite_true_of_w10 rfl, hb2_c2, hb2_c1]
          have hb3_c1 : B3 i c1 = B0 i c1 := by dsimp [B3]; rw [ite_false_of_w10 hn12, hb2_c1]
          have hb4_c3 : B4 i c3 = 6 * B0 i c3 - (-3) * (2 * B0 i c2 - (-1) * B0 i c1) := by
            dsimp [B4]; rw [ite_true_of_w10 rfl, hb3_c3, hb3_c2]
          have hb4_c1 : B4 i c1 = B0 i c1 := by dsimp [B4]; rw [ite_false_of_w10 hn13, hb3_c1]
          change (if c3 = c3 then B4 i c3 - 2 * B4 i c1 else _) = _
          rw [ite_true_of_w10 rfl, hb4_c3, hb4_c1]; dsimp only [c1, c2, c3]
          rw [hraw_col 3 (by decide), hraw_col 2 (by decide), hraw_col 1 (by decide)]
          dsimp [blkDoneU]; rw [ite_true_of_w10 (by omega : (4 * m + 3) / 4 < m + 1)]
          dsimp [apow12U_w17]; rw [show (4 * m + 3) % 4 = 3 by omega, show (4 * m + 3) / 4 = m by omega, hb1]
          have hb3_int : (6 : Int) * (laurentInterpBinom x 3 : Int) -
              (-3) * ((2 : Int) * (laurentInterpBinom x 2 : Int) - (-1) * (x : Int)) -
              2 * (x : Int) = (x : Int) * ((x : Int) * (x : Int)) := by
            have hc2 := congrArg (fun n : Nat => (n : Int)) hb2
            have hc3 := congrArg (fun n : Nat => (n : Int)) hb3
            simp only [Int.natCast_add, Int.natCast_mul] at hc2 hc3
            rw [Int.mul_assoc (x : Int) (x : Int) (x : Int)] at hc3
            generalize (laurentInterpBinom x 3 : Int) = C3 at hc3 ⊢
            generalize (laurentInterpBinom x 2 : Int) = C2 at hc2 ⊢
            generalize (x : Int) * ((x : Int) * (x : Int)) = X3 at hc3 ⊢
            generalize (x : Int) * (x : Int) = X2 at hc2 hc3
            generalize (x : Int) = X1 at hc2 hc3 ⊢
            omega
          calc 6 * ((laurentInterpBinom x 3 : Int) * E) -
                (-3) * (2 * ((laurentInterpBinom x 2 : Int) * E) - (-1) * ((x : Int) * E)) -
                2 * ((x : Int) * E)
              = (6 * (laurentInterpBinom x 3 : Int) -
                  (-3) * (2 * (laurentInterpBinom x 2 : Int) - (-1) * (x : Int)) -
                  2 * (x : Int)) * E := by simp only [Int.sub_mul, Int.mul_sub]; ac_rfl
            _ = ((x : Int) * ((x : Int) * (x : Int))) * E := by rw [hb3_int]
            _ = intPowNat ((r : Int) * (W : Int) + (s : Int) * (K : Int)) 3 * E := by rw [← hx_int]; simp [intPowNat]
      · have hn1 : j ≠ c1 := by intro h; apply hjm; rw [h]; dsimp [c1]; omega
        have hn2 : j ≠ c2 := by intro h; apply hjm; rw [h]; dsimp [c2]; omega
        have hn3 : j ≠ c3 := by intro h; apply hjm; rw [h]; dsimp [c3]; omega
        change (if j = c3 then _ else B4 i j) = _; rw [ite_false_of_w10 hn3]
        change (if j = c3 then _ else B3 i j) = _; rw [ite_false_of_w10 hn3]
        change (if j = c2 then _ else B2 i j) = _; rw [ite_false_of_w10 hn2]
        change (if j = c3 then _ else B1 i j) = _; rw [ite_false_of_w10 hn3]
        change (if j = c2 then _ else B0 i j) = _; rw [ite_false_of_w10 hn2]
        dsimp [B0, blkDoneU]
        by_cases hlt_m : j.val / 4 < m
        · rw [ite_true_of_w10 hlt_m, ite_true_of_w10 (by omega)]
        · rw [ite_false_of_w10 hlt_m, ite_false_of_w10 (by omega)]
    rw [← hB5_eq, hd5, hd4, hd3, hd2, hd1, ← Int.mul_assoc]; rfl
  have hb0_eq : blkDoneU 0 = laurentTwoBaseT4U3Mat12 W K u := by funext i j; simp [blkDoneU]
  have hb3_eq : blkDoneU 3 = apow12U_w17 u (W : Int) (K : Int) := by
    funext i j; dsimp [blkDoneU]; rw [ite_true_of_w10 (by have := j.isLt; omega : j.val / 4 < 3)]
  calc 1728 * intDet 12 (laurentTwoBaseT4U3Mat12 W K u)
      = 12 * (12 * (12 * intDet 12 (blkDoneU 0))) := by rw [hb0_eq]; omega
    _ = intDet 12 (blkDoneU 3) := by
          rw [hblk_stepU 0 (by decide), hblk_stepU 1 (by decide), hblk_stepU 2 (by decide)]
    _ = intDet 12 (apow12U_w17 u (W : Int) (K : Int)) := by rw [hb3_eq]

private theorem det12_t4u3_u1_closed_form_w17 (W K : Nat) :
    intDet 12 (laurentTwoBaseT4U3Mat12 W K 1) =
      3888 * intPowNat (K : Int) 3 * (4 * (W : Int) - (K : Int)) *
        q14T4U3PolyInt (W : Int) (K : Int) := by
  let deg12 : Fin 12 -> Nat := fun j => j.val % 4
  have hdeg12_sum : colDegSum 12 deg12 = 18 := by decide
  have hapow_homog : ∃ cs_lhs : List Int,
      cs_lhs.length = 19 ∧
      ∀ w k : Int, intDet 12 (apow12U_w17 1 w k) = evalHomogAscAux 18 0 w k cs_lhs := by
    have hent : ∀ i j : Fin 12, ∃ cij : List Int,
        cij.length = deg12 j + 1 ∧
        ∀ w k : Int, apow12U_w17 1 w k i j = evalHomogAscAux (deg12 j) 0 w k cij := by
      intro i j
      let r : Int := ((laurentRowsTwoBase12 i).1 : Int)
      let s : Int := ((laurentRowsTwoBase12 i).2 : Int)
      let E : Int := ((2 ^ ((laurentRowsTwoBase12 i).1 * ((j.val / 4) * 1)) *
        3 ^ ((laurentRowsTwoBase12 i).2 * ((j.val / 4) * 1)) : Nat) : Int)
      let lin : List Int := [s, r]
      have hlin_ev : ∀ w k : Int, evalHomogAscAux 1 0 w k lin = r * w + s * k := by
        intro w k; simp [lin, evalHomogAscAux, intPowNat]; omega
      have hpow_lin : ∀ t : Nat, ∃ ct : List Int,
          ct.length = t + 1 ∧
          ∀ w k : Int, intPowNat (r * w + s * k) t = evalHomogAscAux t 0 w k ct := by
        intro t; induction t with
        | zero => exact ⟨[1], rfl, fun _ _ => by simp [evalHomogAscAux, intPowNat]⟩
        | succ t' iht =>
          rcases iht with ⟨ct', hl', he'⟩
          rcases mulHomogPoly_spec_w17 1 lin rfl t' ct' hl' with ⟨hlm, hem⟩
          refine ⟨mulHomogPoly lin ct', by rw [hlm]; omega, fun w k => ?_⟩
          rw [show t' + 1 = 1 + t' by omega, hem w k, hlin_ev w k, ← he' w k]
          simp [intPowNat, Nat.add_comm 1 t']
      rcases hpow_lin (deg12 j) with ⟨ct, hlt, het⟩
      refine ⟨scalePolyInt E ct, by simp [scalePolyInt, hlt], fun w k => ?_⟩
      rw [(poly_linear_ops_spec_w17 (deg12 j) w k).1 E ct 0 |>.2, ← het w k, Int.mul_comm]
      rfl
    rcases poly_det_exists_homog_w17 12 deg12 (apow12U_w17 1) hent with ⟨cs_lhs, hl_lhs, he_lhs⟩
    rw [hdeg12_sum] at hl_lhs he_lhs
    exact ⟨cs_lhs, hl_lhs, he_lhs⟩
  have hrhs_homog : ∃ cs_rhs : List Int,
      cs_rhs.length = 19 ∧
      ∀ w k : Int,
        1728 * (3888 * intPowNat k 3 * (4 * w - k) * q14T4U3PolyInt w k) =
          evalHomogAscAux 18 0 w k cs_rhs := by
    let p_k3 : List Int := [1, 0, 0, 0]
    have hk3_ev : ∀ w k : Int, evalHomogAscAux 3 0 w k p_k3 = intPowNat k 3 := by
      intro w k; simp [p_k3, evalHomogAscAux, intPowNat]
    let p_lin : List Int := [-1, 4]
    have hlin_ev : ∀ w k : Int, evalHomogAscAux 1 0 w k p_lin = 4 * w - k := by
      intro w k; simp [p_lin, evalHomogAscAux, intPowNat]; omega
    rcases mulHomogPoly_spec_w17 3 p_k3 rfl 1 p_lin rfl with ⟨hl4, he4⟩
    have hq14_len : q14T4U3Coeffs.length = 15 := rfl
    rcases mulHomogPoly_spec_w17 4 (mulHomogPoly p_k3 p_lin) hl4 14 q14T4U3Coeffs hq14_len with ⟨hl18, he18⟩
    let cs_rhs := scalePolyInt 6718464 (mulHomogPoly (mulHomogPoly p_k3 p_lin) q14T4U3Coeffs)
    refine ⟨cs_rhs, by simp [cs_rhs, scalePolyInt, hl18], fun w k => ?_⟩
    dsimp [cs_rhs]
    rw [(poly_linear_ops_spec_w17 18 w k).1 6718464 _ 0 |>.2, he18 w k, he4 w k,
        hk3_ev w k, hlin_ev w k]
    unfold q14T4U3PolyInt
    have h6718 : (1728 : Int) * 3888 = 6718464 := rfl
    calc (1728 : Int) * (3888 * intPowNat k 3 * (4 * w - k) * evalHomogAscAux 14 0 w k q14T4U3Coeffs)
        = ((1728 : Int) * 3888) * (intPowNat k 3 * (4 * w - k) * evalHomogAscAux 14 0 w k q14T4U3Coeffs) := by ac_rfl
      _ = 6718464 * (intPowNat k 3 * (4 * w - k) * evalHomogAscAux 14 0 w k q14T4U3Coeffs) := by rw [h6718]
  rcases hapow_homog with ⟨cs_lhs, hl_lhs, he_lhs⟩
  rcases hrhs_homog with ⟨cs_rhs, hl_rhs, he_rhs⟩
  let diff := subPolySameLen cs_lhs cs_rhs
  have hdiff_len : diff.length = 19 := by
    rw [(poly_linear_ops_spec_w17 0 0 0).2.2 _ _ 0 (hl_lhs.trans hl_rhs.symm) |>.1, hl_lhs]
  have hapow_fn_eq : ∀ W0 : Nat, apow12FastFn W0 = apow12U_w17 1 (W0 : Int) 1 := by
    have hipow : ∀ (x : Int) (d : Nat), x ^ d = intPowNat x d := by
      intro x d; induction d with
      | zero => simp [Int.pow_zero, intPowNat]
      | succ d' ih => rw [Int.pow_succ, ih]; simp only [intPowNat]; ac_rfl
    intro W0; funext i j
    simp only [apow12FastFn, apow12U_w17, laurentRowsTwoBase12, Nat.mul_one,
               Int.natCast_mul, Int.natCast_add, Int.natCast_pow, Int.mul_one, hipow]
  have hroots19 : ∀ idx : Nat, idx < 19 -> evalUniInt ((2 + idx : Nat) : Int) diff = 0 := by
    intro idx hidx
    have hex_cert : ∃ uTbl d,
        checkULDet12Bool (apow12FastFn (2 + idx)) uTbl d = true ∧
        d = 1728 * (3888 * (4 * ((2 + idx : Nat) : Int) - 1) * q14T4U3PolyInt ((2 + idx : Nat) : Int) 1) := by
      match idx with
      | 0 => exact ⟨uApow12_w2Tbl, _, apow12_w2_cert.1, apow12_w2_cert.2⟩
      | 1 => exact ⟨uApow12_w3Tbl, _, apow12_w3_cert.1, apow12_w3_cert.2⟩
      | 2 => exact ⟨uApow12_w4Tbl, _, apow12_w4_cert.1, apow12_w4_cert.2⟩
      | 3 => exact ⟨uApow12_w5Tbl, _, apow12_w5_cert.1, apow12_w5_cert.2⟩
      | 4 => exact ⟨uApow12_w6Tbl, _, apow12_w6_cert.1, apow12_w6_cert.2⟩
      | 5 => exact ⟨uApow12_w7Tbl, _, apow12_w7_cert.1, apow12_w7_cert.2⟩
      | 6 => exact ⟨uApow12_w8Tbl, _, apow12_w8_cert.1, apow12_w8_cert.2⟩
      | 7 => exact ⟨uApow12_w9Tbl, _, apow12_w9_cert.1, apow12_w9_cert.2⟩
      | 8 => exact ⟨uApow12_w10Tbl, _, apow12_w10_cert.1, apow12_w10_cert.2⟩
      | 9 => exact ⟨uApow12_w11Tbl, _, apow12_w11_cert.1, apow12_w11_cert.2⟩
      | 10 => exact ⟨uApow12_w12Tbl, _, apow12_w12_cert.1, apow12_w12_cert.2⟩
      | 11 => exact ⟨uApow12_w13Tbl, _, apow12_w13_cert.1, apow12_w13_cert.2⟩
      | 12 => exact ⟨uApow12_w14Tbl, _, apow12_w14_cert.1, apow12_w14_cert.2⟩
      | 13 => exact ⟨uApow12_w15Tbl, _, apow12_w15_cert.1, apow12_w15_cert.2⟩
      | 14 => exact ⟨uApow12_w16Tbl, _, apow12_w16_cert.1, apow12_w16_cert.2⟩
      | 15 => exact ⟨uApow12_w17Tbl, _, apow12_w17_cert.1, apow12_w17_cert.2⟩
      | 16 => exact ⟨uApow12_w18Tbl, _, apow12_w18_cert.1, apow12_w18_cert.2⟩
      | 17 => exact ⟨uApow12_w19Tbl, _, apow12_w19_cert.1, apow12_w19_cert.2⟩
      | 18 => exact ⟨uApow12_w20Tbl, _, apow12_w20_cert.1, apow12_w20_cert.2⟩
      | _ + 19 => omega
    rcases hex_cert with ⟨uTbl, di, hchk, hdi_eq⟩
    have hdet_apow := checkULDet12Bool_sound_w17 (apow12FastFn (2 + idx)) uTbl di hchk
    rw [hapow_fn_eq (2 + idx), hdi_eq] at hdet_apow
    have hl_ev := he_lhs ((2 + idx : Nat) : Int) 1
    have hr_ev := he_rhs ((2 + idx : Nat) : Int) 1
    simp only [intPowNat, Int.mul_one] at hr_ev
    have heq_ev : evalHomogAscAux 18 0 ((2 + idx : Nat) : Int) 1 diff = 0 := by
      rw [(poly_linear_ops_spec_w17 18 ((2 + idx : Nat) : Int) 1).2.2 cs_lhs cs_rhs 0 (hl_lhs.trans hl_rhs.symm) |>.2,
          ← hl_ev, ← hr_ev, hdet_apow]
      omega
    rwa [evalHomogAscAux_at_k1_w17 18 ((2 + idx : Nat) : Int) diff 0,
         show intPowNat ((2 + idx : Nat) : Int) 0 = 1 from rfl, Int.one_mul] at heq_ev
  have hall_zero := allZero_of_evalUniInt_zero_w17 diff
    (evalUniInt_zero_of_roots_from_w17 19 2 diff (by omega) hroots19)
  have hdiff_zero_ev : ∀ w k : Int, evalHomogAscAux 18 0 w k diff = 0 := by
    have hz : ∀ (xs : List Int) (curW : Nat) (w k : Int),
        (∀ a ∈ xs, a = 0) -> evalHomogAscAux 18 curW w k xs = 0 := by
      intro xs; induction xs with
      | nil => intros; rfl
      | cons a tl ih =>
        intro curW w k hall
        rw [evalHomogAscAux, hall a (List.Mem.head _), Int.zero_mul, Int.zero_mul, Int.zero_add]
        exact ih (curW + 1) w k (fun x hx => hall x (List.Mem.tail a hx))
    intro w k; exact hz diff 0 w k hall_zero
  have heq_wk : 1728 * intDet 12 (laurentTwoBaseT4U3Mat12 W K 1) =
      1728 * (3888 * intPowNat (K : Int) 3 * (4 * (W : Int) - (K : Int)) *
        q14T4U3PolyInt (W : Int) (K : Int)) := by
    have hz := hdiff_zero_ev (W : Int) (K : Int)
    rw [(poly_linear_ops_spec_w17 18 (W : Int) (K : Int)).2.2 cs_lhs cs_rhs 0
          (hl_lhs.trans hl_rhs.symm) |>.2,
        ← he_lhs (W : Int) (K : Int), ← he_rhs (W : Int) (K : Int),
        ← stirling_1728_det12_t4u3_u_w17 1 W K] at hz
    omega
  exact Int.eq_of_mul_eq_mul_left (by decide : (1728 : Int) ≠ 0) heq_wk

private theorem q14T4U3PolyInt_ne_zero_w17 (W K : Nat) (hW : W ≥ 1) (_hK : K ≥ 1) :
    q14T4U3PolyInt (W : Int) (K : Int) ≠ 0 := by
  have hmod47 := t4u3_mod47_cert
  have hhomog14 : ∀ (cs : List Int) (curW : Nat), curW + cs.length ≤ 15 ->
      ∀ (w k g : Int),
        evalHomogAscAux 14 curW (w * g) (k * g) cs =
          intPowNat g 14 * evalHomogAscAux 14 curW w k cs := by
    have hmul_pow : ∀ (a b : Int) (n : Nat), intPowNat (a * b) n = intPowNat a n * intPowNat b n := by
      intro a b n; induction n with
      | zero => simp [intPowNat]
      | succ n' ih => simp only [intPowNat, ih]; ac_rfl
    intro cs; induction cs with
    | nil => intros; simp [evalHomogAscAux]
    | cons c tl ih =>
      intro curW hle w k g
      have hexp14 : curW + (14 - curW) = 14 := by simp at hle; omega
      simp only [evalHomogAscAux, hmul_pow w g curW, hmul_pow k g (14 - curW),
                 ih (curW + 1) (by simp at hle ⊢; omega) w k g, Int.mul_add]
      have hterm : c * (intPowNat w curW * intPowNat g curW) *
          (intPowNat k (14 - curW) * intPowNat g (14 - curW)) =
          intPowNat g 14 * (c * intPowNat w curW * intPowNat k (14 - curW)) := by
        calc c * (intPowNat w curW * intPowNat g curW) *
              (intPowNat k (14 - curW) * intPowNat g (14 - curW))
            = (intPowNat g curW * intPowNat g (14 - curW)) *
              (c * intPowNat w curW * intPowNat k (14 - curW)) := by ac_rfl
          _ = intPowNat g 14 * (c * intPowNat w curW * intPowNat k (14 - curW)) := by
              rw [← intPowNat_add g curW (14 - curW), hexp14]
      rw [hterm]
  have hmod_congr : ∀ (cs : List Int) (curW : Nat) (w1 w2 k1 k2 : Int),
      w1 % 47 = w2 % 47 -> k1 % 47 = k2 % 47 ->
      evalHomogAscAux 14 curW w1 k1 cs % 47 = evalHomogAscAux 14 curW w2 k2 cs % 47 := by
    have hpow_m : ∀ (a b : Int) (n : Nat), a % 47 = b % 47 -> intPowNat a n % 47 = intPowNat b n % 47 := by
      intro a b n hab; induction n with
      | zero => rfl
      | succ n' ih => simp only [intPowNat]; rw [Int.mul_emod, hab, ih, ← Int.mul_emod]
    intro cs; induction cs with
    | nil => intros; rfl
    | cons c tl ih =>
      intro curW w1 w2 k1 k2 hw hk
      simp only [evalHomogAscAux]
      rw [Int.add_emod, Int.add_emod (c * _ * _), ih (curW + 1) w1 w2 k1 k2 hw hk,
          Int.mul_emod (c * intPowNat w1 curW), Int.mul_emod c (intPowNat w1 curW),
          hpow_m w1 w2 curW hw, hpow_m k1 k2 (14 - curW) hk,
          ← Int.mul_emod c (intPowNat w2 curW), ← Int.mul_emod (c * intPowNat w2 curW)]
  unfold checkQ14ProjRootFreeMod47Bool at hmod47
  rcases bool_and_split hmod47 with ⟨hb1, hall_aff⟩
  rcases bool_and_split hb1 with ⟨hall_inv, hinf_b⟩
  have hinf_nz := bne_iff_ne.mp hinf_b
  have hinv_spec : ∀ x : Nat, x < 47 -> x ≠ 0 ->
      (x * powModFuelW17 8 x 45 47) % 47 = 1 := by
    have hlp : ∀ n : Nat, n ≤ 47 ->
        q14Mod47AllInv n = true ->
        ∀ x : Nat, x < n -> x ≠ 0 ->
          (x * powModFuelW17 8 x 45 47) % 47 = 1 := by
      intro n hn; induction n with
      | zero => intros _ _ hlt; omega
      | succ n' ihn =>
        intro ha x hx hne
        unfold q14Mod47AllInv at ha
        rcases bool_and_split ha with ⟨hcur, hprev⟩
        by_cases hxeq : x = n'
        · subst hxeq; rw [beq_false_of_ne hne] at hcur; exact beq_iff_eq.mp hcur
        · exact ihn (Nat.le_of_lt hn) hprev x (by omega) hne
    exact hlp 47 (Nat.le_refl _) hall_inv
  have haff_spec : ∀ t : Nat, t < 47 ->
      evalHomogAscAux 14 0 (t : Int) 1 q14T4U3Coeffs % 47 ≠ 0 := by
    have hlp : ∀ n : Nat, n ≤ 47 ->
        q14Mod47AllAff n = true ->
        ∀ t : Nat, t < n -> evalHomogAscAux 14 0 (t : Int) 1 q14T4U3Coeffs % 47 ≠ 0 := by
      intro n hn; induction n with
      | zero => intros _ _ hlt; omega
      | succ n' ihn =>
        intro ha t ht
        unfold q14Mod47AllAff at ha
        rcases bool_and_split ha with ⟨hcur, hprev⟩
        by_cases hteq : t = n'
        · subst hteq; exact bne_iff_ne.mp hcur
        · exact ihn (Nat.le_of_lt hn) hprev t (by omega)
    exact hlp 47 (Nat.le_refl _) hall_aff
  have hcancel14 : ∀ (x inv : Nat) (V : Int),
      (x * inv) % 47 = 1 ->
      (intPowNat (x : Int) 14 * V) % 47 = 0 ->
      V % 47 = 0 := by
    intro x inv V hxinv hxv0
    have hp_d : ∀ d : Nat, ((x * inv) ^ d) % 47 = 1 := by
      intro d; induction d with
      | zero => rfl
      | succ d' ih => rw [Nat.pow_succ, Nat.mul_mod, ih, Nat.one_mul, Nat.mod_mod, hxinv]
    have hpow_nat : ∀ (n d : Nat), intPowNat (n : Int) d = ((n ^ d : Nat) : Int) := by
      intro n d; induction d with
      | zero => rfl
      | succ d' ih => simp only [intPowNat, ih, Nat.pow_succ, Int.natCast_mul]; ac_rfl
    have hp14_1 : (x ^ 14 * inv ^ 14) % 47 = 1 := by
      have hm_pow : ∀ a b d : Nat, a ^ d * b ^ d = (a * b) ^ d := by
        intro a b d; induction d with
        | zero => rfl
        | succ d' ih => simp only [Nat.pow_succ, ← ih]; ac_rfl
      rw [hm_pow]; exact hp_d 14
    have hm1 : (((x ^ 14 * inv ^ 14 : Nat) : Int) % 47) = 1 := by
      have hc : (((x ^ 14 * inv ^ 14 : Nat) : Int) % 47) = (((x ^ 14 * inv ^ 14) % 47 : Nat) : Int) :=
        (Int.natCast_emod (x ^ 14 * inv ^ 14) 47).symm
      rw [hc, hp14_1]; rfl
    rw [hpow_nat x 14] at hxv0
    calc V % 47
        = ((1 % 47) * (V % 47)) % 47 := by simp
      _ = ((((x ^ 14 * inv ^ 14 : Nat) : Int) % 47) * (V % 47)) % 47 := by rw [hm1]; rfl
      _ = (((x ^ 14 * inv ^ 14 : Nat) : Int) * V) % 47 := (Int.mul_emod _ _ _).symm
      _ = (((inv ^ 14 : Nat) : Int) * (((x ^ 14 : Nat) : Int) * V)) % 47 := by
            rw [Int.natCast_mul]; ac_rfl
      _ = ((((inv ^ 14 : Nat) : Int) % 47) * ((((x ^ 14 : Nat) : Int) * V) % 47)) % 47 :=
            Int.mul_emod _ _ _
      _ = 0 := by rw [hxv0, Int.mul_zero, Int.zero_emod]
  intro hz
  let g := Nat.gcd W K
  have hg_pos : g ≥ 1 := Nat.gcd_pos_of_pos_left K hW
  let w' := W / g
  let k' := K / g
  have hW_eq : W = w' * g := (Nat.div_mul_cancel (Nat.gcd_dvd_left W K)).symm
  have hK_eq : K = k' * g := (Nat.div_mul_cancel (Nat.gcd_dvd_right W K)).symm
  unfold q14T4U3PolyInt at hz
  rw [hW_eq, hK_eq, Int.natCast_mul, Int.natCast_mul,
      hhomog14 q14T4U3Coeffs 0 (by decide) (w' : Int) (k' : Int) (g : Int)] at hz
  have hg14_nz : intPowNat (g : Int) 14 ≠ 0 := intPowNat_ne_zero_w17 (g : Int) (by omega) 14
  have hcore0 : evalHomogAscAux 14 0 (w' : Int) (k' : Int) q14T4U3Coeffs = 0 := by
    by_cases hc : evalHomogAscAux 14 0 (w' : Int) (k' : Int) q14T4U3Coeffs = 0
    · exact hc
    · exact False.elim (Int.mul_ne_zero hg14_nz hc hz)
  let wm := w' % 47
  let km := k' % 47
  have hwm_lt : wm < 47 := Nat.mod_lt w' (by decide)
  have hkm_lt : km < 47 := Nat.mod_lt k' (by decide)
  have hnot_both0 : ¬ (wm = 0 ∧ km = 0) := by
    rintro ⟨hw0, hk0⟩
    rcases Nat.dvd_of_mod_eq_zero hw0 with ⟨qw, hqw⟩
    rcases Nat.dvd_of_mod_eq_zero hk0 with ⟨qk, hqk⟩
    have hdW : 47 * g ∣ W := ⟨qw, by rw [hW_eq, hqw]; ac_rfl⟩
    have hdK : 47 * g ∣ K := ⟨qk, by rw [hK_eq, hqk]; ac_rfl⟩
    have hle := Nat.le_of_dvd hg_pos (Nat.dvd_gcd hdW hdK)
    omega
  have hm_wk : evalHomogAscAux 14 0 (wm : Int) (km : Int) q14T4U3Coeffs % 47 = 0 := by
    rw [hmod_congr q14T4U3Coeffs 0 (wm : Int) (w' : Int) (km : Int) (k' : Int)
          (by dsimp [wm]; omega)
          (by dsimp [km]; omega),
        hcore0, Int.zero_emod]
  by_cases hkm0 : km = 0
  · have hwm_ne : wm ≠ 0 := fun hw0 => hnot_both0 ⟨hw0, hkm0⟩
    let inv := powModFuelW17 8 wm 45 47
    have hinv := hinv_spec wm hwm_lt hwm_ne
    rw [hkm0, show (wm : Int) = 1 * (wm : Int) by omega,
        show ((0 : Nat) : Int) = 0 * (wm : Int) by omega,
        hhomog14 q14T4U3Coeffs 0 (by decide) 1 0 (wm : Int)] at hm_wk
    exact hinf_nz (hcancel14 wm inv _ hinv hm_wk)
  · let inv := powModFuelW17 8 km 45 47
    have hinv := hinv_spec km hkm_lt hkm0
    let t := (wm * inv) % 47
    have ht_lt : t < 47 := Nat.mod_lt _ (by decide)
    have htkm : ((t : Int) * (km : Int)) % 47 = (wm : Int) % 47 := by
      have hnat : (t * km) % 47 = wm := by
        dsimp [t]
        rw [Nat.mod_mul_mod, Nat.mul_assoc wm inv km, Nat.mul_comm inv km,
            Nat.mul_mod wm (km * inv) 47, hinv, Nat.mul_one, Nat.mod_mod,
            Nat.mod_eq_of_lt hwm_lt]
      rw [← Int.natCast_mul]; omega
    have htk0 : evalHomogAscAux 14 0 ((t : Int) * (km : Int)) (1 * (km : Int)) q14T4U3Coeffs % 47 = 0 := by
      rw [hmod_congr q14T4U3Coeffs 0 _ (wm : Int) _ (km : Int) htkm (by rw [Int.one_mul]), hm_wk]
    rw [hhomog14 q14T4U3Coeffs 0 (by decide) (t : Int) 1 (km : Int)] at htk0
    exact haff_spec t ht_lt (hcancel14 km inv _ hinv htk0)

private def degPref12_w17 : Nat -> Nat
  | 0 => 0
  | k + 1 => k % 4 + degPref12_w17 k

private theorem det12_t4u3_ray_4w_u2_scale_w17 (W : Nat) :
    intDet 12 (laurentTwoBaseT4U3Mat12 W (4 * W) 2) =
      intPowNat (W : Int) 18 * intDet 12 (laurentTwoBaseT4U3Mat12 1 4 2) := by
  let colSc (c_done : Nat) (i j : Fin 12) : Int :=
    if j.val < c_done then intPowNat (W : Int) (j.val % 4) * apow12U_w17 2 1 4 i j
    else apow12U_w17 2 1 4 i j
  have hmul_pow_int : ∀ (a b : Int) (d : Nat), intPowNat (a * b) d = intPowNat a d * intPowNat b d := by
    intro a b d; induction d with
    | zero => simp [intPowNat]
    | succ d' ih => simp only [intPowNat, ih]; ac_rfl
  have hadd_pow_int : ∀ (a : Int) (d1 d2 : Nat), intPowNat a (d1 + d2) = intPowNat a d1 * intPowNat a d2 := by
    intro a d1; induction d1 with
    | zero => intro d2; simp [intPowNat]
    | succ d1' ih => intro d2; rw [Nat.succ_add, intPowNat, intPowNat, ih d2, Int.mul_assoc]
  have hsc_step : ∀ (c : Nat) (hc : c < 12),
      intDet 12 (colSc (c + 1)) = intPowNat (W : Int) (c % 4) * intDet 12 (colSc c) := by
    intro c hc
    let jc : Fin 12 := ⟨c, hc⟩
    have heq_mat : colSc (c + 1) = (fun i j : Fin 12 =>
        if j = jc then intPowNat (W : Int) (c % 4) * colSc c i jc else colSc c i j) := by
      funext i j
      by_cases hjc : j = jc
      · subst hjc
        have hc1 : c < c + 1 := Nat.lt_succ_self c
        have hcc : ¬ (c < c) := Nat.lt_irrefl c
        change (if c < c + 1 then intPowNat (W : Int) (c % 4) * apow12U_w17 2 1 4 i jc
                else apow12U_w17 2 1 4 i jc) =
               (if jc = jc then intPowNat (W : Int) (c % 4) *
                  (if c < c then intPowNat (W : Int) (c % 4) * apow12U_w17 2 1 4 i jc
                   else apow12U_w17 2 1 4 i jc)
                else colSc c i jc)
        rw [ite_true_of_w10 hc1, ite_true_of_w10 rfl, ite_false_of_w10 hcc]
      · dsimp [colSc]
        rw [ite_false_of_w10 hjc]
        have hj_ne : j.val ≠ c := fun hv => hjc (Fin.ext hv)
        by_cases hlt : j.val < c
        · rw [ite_true_of_w10 (by omega : j.val < c + 1), ite_true_of_w10 hlt]
        · rw [ite_false_of_w10 (by omega : ¬ (j.val < c + 1)), ite_false_of_w10 hlt]
    rw [heq_mat]; exact intDet_col_scale (intPowNat (W : Int) (c % 4)) 12 jc (colSc c)
  have hsc_0 : colSc 0 = apow12U_w17 2 1 4 := by funext i j; simp [colSc]
  have hsc_12 : colSc 12 = apow12U_w17 2 (W : Int) (((4 * W : Nat) : Int)) := by
    funext i j
    dsimp [colSc]
    rw [ite_true_of_w10 j.isLt]
    dsimp [apow12U_w17]
    have hlin_w : ((laurentRowsTwoBase12 i).1 : Int) * (W : Int) +
        ((laurentRowsTwoBase12 i).2 : Int) * (4 * (W : Int)) =
        (W : Int) * (((laurentRowsTwoBase12 i).1 : Int) * 1 + ((laurentRowsTwoBase12 i).2 : Int) * 4) := by
      generalize ((laurentRowsTwoBase12 i).1 : Int) = R,
                 ((laurentRowsTwoBase12 i).2 : Int) = S,
                 (W : Int) = wi
      calc R * wi + S * (4 * wi)
          = wi * R + wi * (S * 4) := by ac_rfl
        _ = wi * (R * 1) + wi * (S * 4) := by rw [Int.mul_one]
        _ = wi * (R * 1 + S * 4) := (Int.mul_add wi (R * 1) (S * 4)).symm
    rw [hlin_w, hmul_pow_int (W : Int) _ (j.val % 4), Int.mul_assoc]
  have hind_sc : ∀ n : Nat, n ≤ 12 ->
      intDet 12 (colSc n) = intPowNat (W : Int) (degPref12_w17 n) * intDet 12 (colSc 0) := by
    intro n; induction n with
    | zero => intro _; simp [degPref12_w17, intPowNat]
    | succ n' ihn =>
      intro hn
      rw [hsc_step n' hn, ihn (Nat.le_of_lt hn), ← Int.mul_assoc,
          ← hadd_pow_int (W : Int) (n' % 4) (degPref12_w17 n')]
      rfl
  have hdet_sc12 : intDet 12 (colSc 12) = intPowNat (W : Int) 18 * intDet 12 (colSc 0) := by
    have h12 := hind_sc 12 (Nat.le_refl 12)
    have hd12 : degPref12_w17 12 = 18 := by decide
    rwa [hd12] at h12
  rw [hsc_12, hsc_0] at hdet_sc12
  have h14 : 1728 * intDet 12 (laurentTwoBaseT4U3Mat12 1 4 2) = intDet 12 (apow12U_w17 2 1 4) :=
    stirling_1728_det12_t4u3_u_w17 2 1 4
  have hmul_1728 : 1728 * intDet 12 (laurentTwoBaseT4U3Mat12 W (4 * W) 2) =
      1728 * (intPowNat (W : Int) 18 * intDet 12 (laurentTwoBaseT4U3Mat12 1 4 2)) := by
    rw [stirling_1728_det12_t4u3_u_w17 2 W (4 * W), hdet_sc12, ← h14]
    generalize intDet 12 (laurentTwoBaseT4U3Mat12 1 4 2) = D14, intPowNat (W : Int) 18 = W18
    calc W18 * (1728 * D14)
        = (W18 * 1728) * D14 := (Int.mul_assoc _ _ _).symm
      _ = (1728 * W18) * D14 := by rw [Int.mul_comm W18 1728]
      _ = 1728 * (W18 * D14) := Int.mul_assoc _ _ _
  exact Int.eq_of_mul_eq_mul_left (by decide : (1728 : Int) ≠ 0) hmul_1728

private theorem intPowNat_pos_of_pos_w17 (n d : Nat) (hn : n ≥ 1) :
    intPowNat (n : Int) d ≥ 1 := by
  have hp_nat : ∀ k : Nat, intPowNat (n : Int) k = ((n ^ k : Nat) : Int) := by
    intro k; induction k with
    | zero => rfl
    | succ k' ih => simp only [intPowNat, ih, Nat.pow_succ, Int.natCast_mul]; ac_rfl
  have hp_pos := nat_pow_pos_of_pos n hn d
  rw [hp_nat d]; omega

/--
  Theorem W17.2b (`laurent_12x12_t4u3_cone_flip_and_exact_u1_zero_locus`,
  `zero custom axioms`):
  Rank-3 Order-4 `12 × 12` `(T = 4, U = 3)` Two-Base Schneider–Laurent Determinant Theorem:
  Collatz-Cone Sign-Flip at `u = 1` (`det_12(3, 5, 1) < 0` vs `det_12(5, 8, 1) > 0`, Contrasting
  `9 × 9` `(T = 3, U = 3)` All-`u` Positivity) & Shift-`u = 2` Recovery (`det_12(3, 5, 2) > 0`),
  `(2^K - 3^W)` Congruence & `confluentFactorAllU 3 4 u` Divisibility, Exact Homogeneous Degree-18
  Closed Form `det_12(W, K, 1) = 3888 * K^3 * (4 * W - K) * Q_14(W, K)` Across ALL `W, K : Nat`,
  Projective `P^1(F_47)` Non-Vanishing of `Q_14`, & Exact Positive-Quadrant Zero Locus
  `∀ W, K ≥ 1, det_12(W, K, 1) = 0 ↔ K = 4 * W` Plus Ray-`K = 4 * W` `u = 2` Non-Vanishing
  (`det_12(W, 4 * W, 2) = W^18 * det_12(1, 4, 2) < 0`, `Branch P3.3`, witness
  `LAURENT_12X12_T4U3_CONE_FLIP_AND_RECT_U2_OVERLAP`, `W17_H2`).
-/
theorem laurent_12x12_t4u3_cone_flip_and_exact_u1_zero_locus :
    (intDet 12 (laurentTwoBaseT4U3Mat12 3 5 1) = -1008815432152374000 ∧
     intDet 12 (laurentTwoBaseT4U3Mat12 3 5 1) < 0 ∧
     intDet 12 (laurentTwoBaseT4U3Mat12 5 8 1) = 16919290838092087296 ∧
     intDet 12 (laurentTwoBaseT4U3Mat12 5 8 1) > 0 ∧
     intDet 12 (laurentTwoBaseT4U3Mat12 3 5 2) = 177759891811505204469541718468100000000 ∧
     intDet 12 (laurentTwoBaseT4U3Mat12 3 5 2) > 0 ∧
     intDet 12 (laurentTwoBaseT4U3Mat12 1 4 1) = 0 ∧
     intDet 12 (laurentTwoBaseT4U3Mat12 1 4 2) = -15742910792136445715997717744844800000000 ∧
     intDet 12 (laurentTwoBaseT4U3Mat12 1 4 2) < 0) ∧
    (∀ (W K u : Nat), W ≥ 1 -> u ≥ 1 ->
      let M0 : Fin 12 -> Fin 12 -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (laurentRowsTwoBase12 i).1 (laurentRowsTwoBase12 i).2
          (laurentColsT4U3_12 u j).1 (laurentColsT4U3_12 u j).2 : Int)
      ((confluentFactorAllU 3 4 u : Nat) : Int) ∣ intDet 12 M0 ∧
      (3 ^ W < 2 ^ K ->
        ((2 ^ K - 3 ^ W : Nat) : Int) ∣
          (intDet 12 (laurentTwoBaseT4U3Mat12 W K (W * u)) - intDet 12 M0))) ∧
    (∀ W K : Nat,
      intDet 12 (laurentTwoBaseT4U3Mat12 W K 1) =
        3888 * intPowNat (K : Int) 3 * (4 * (W : Int) - (K : Int)) *
          q14T4U3PolyInt (W : Int) (K : Int)) ∧
    (∀ W K : Nat, W ≥ 1 -> K ≥ 1 -> q14T4U3PolyInt (W : Int) (K : Int) ≠ 0) ∧
    (∀ W K : Nat, W ≥ 1 -> K ≥ 1 ->
      (intDet 12 (laurentTwoBaseT4U3Mat12 W K 1) = 0 ↔ K = 4 * W) ∧
      (K = 4 * W ->
        intDet 12 (laurentTwoBaseT4U3Mat12 W K 2) =
          intPowNat (W : Int) 18 * intDet 12 (laurentTwoBaseT4U3Mat12 1 4 2) ∧
        intDet 12 (laurentTwoBaseT4U3Mat12 W K 2) < 0) ∧
      ¬ (intDet 12 (laurentTwoBaseT4U3Mat12 W K 1) = 0 ∧
         intDet 12 (laurentTwoBaseT4U3Mat12 W K 2) = 0)) := by
  have hd351 : intDet 12 (laurentTwoBaseT4U3Mat12 3 5 1) = -1008815432152374000 := by
    rw [← fastMat12T4U3Fn_eq]; exact checkULDet12Bool_sound_w17 _ _ _ t4u3_351_cert
  have hd581 : intDet 12 (laurentTwoBaseT4U3Mat12 5 8 1) = 16919290838092087296 := by
    rw [← fastMat12T4U3Fn_eq]; exact checkULDet12Bool_sound_w17 _ _ _ t4u3_581_cert
  have hd352 : intDet 12 (laurentTwoBaseT4U3Mat12 3 5 2) = 177759891811505204469541718468100000000 := by
    rw [← fastMat12T4U3Fn_eq]; exact checkULDet12Bool_sound_w17 _ _ _ t4u3_352_cert
  have hd142 : intDet 12 (laurentTwoBaseT4U3Mat12 1 4 2) = -15742910792136445715997717744844800000000 := by
    rw [← fastMat12T4U3Fn_eq]; exact checkULDet12Bool_sound_w17 _ _ _ t4u3_142_cert
  have hpart2 : ∀ (W K u : Nat), W ≥ 1 -> u ≥ 1 ->
      let M0 : Fin 12 -> Fin 12 -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (laurentRowsTwoBase12 i).1 (laurentRowsTwoBase12 i).2
          (laurentColsT4U3_12 u j).1 (laurentColsT4U3_12 u j).2 : Int)
      ((confluentFactorAllU 3 4 u : Nat) : Int) ∣ intDet 12 M0 ∧
      (3 ^ W < 2 ^ K ->
        ((2 ^ K - 3 ^ W : Nat) : Int) ∣
          (intDet 12 (laurentTwoBaseT4U3Mat12 W K (W * u)) - intDet 12 M0)) := by
    intro W K u _ hu; dsimp only
    have hc_dvd := (laurent_all_blocks_arbitrary_U_confluent_divisibility_and_majorant.1
      3 W K 4 u laurentRowsTwoBase12 (by decide) (by decide) hu).2
    refine ⟨hc_dvd, fun hlt => ?_⟩
    have hcong := (laurent_wdilated_zero_gap_entry_and_det_congruence.2
      W K 12 laurentRowsTwoBase12 (laurentColsT4U3_12 u) hlt).1
    have hMW_eq : (fun i j : Fin 12 =>
        (laurentInterpEntry W K (laurentRowsTwoBase12 i).1 (laurentRowsTwoBase12 i).2
          (laurentColsT4U3_12 u j).1 (W * (laurentColsT4U3_12 u j).2) : Int)) =
        laurentTwoBaseT4U3Mat12 W K (W * u) := by
      funext i j; unfold laurentTwoBaseT4U3Mat12 laurentInterpMat laurentColsT4U3_12
      dsimp; rw [show W * (j.val / 4 * u) = j.val / 4 * (W * u) by ac_rfl]
    rw [hMW_eq] at hcong
    rcases hcong with ⟨c_q, hc_q⟩
    exact ⟨-c_q, by rw [Int.mul_neg]; omega⟩
  refine ⟨⟨hd351, by rw [hd351]; decide,
           hd581, by rw [hd581]; decide,
           hd352, by rw [hd352]; decide,
           by rw [det12_t4u3_u1_closed_form_w17 1 4]; simp [Int.sub_self, Int.mul_zero, Int.zero_mul],
           hd142, by rw [hd142]; decide⟩,
          hpart2, det12_t4u3_u1_closed_form_w17, q14T4U3PolyInt_ne_zero_w17, ?_⟩
  intro W K hW hK
  have hiff_4w : intDet 12 (laurentTwoBaseT4U3Mat12 W K 1) = 0 ↔ K = 4 * W := by
    rw [det12_t4u3_u1_closed_form_w17 W K]
    constructor
    · intro hz
      have hq_nz := q14T4U3PolyInt_ne_zero_w17 W K hW hK
      have hk3_nz : (3888 : Int) * intPowNat (K : Int) 3 ≠ 0 :=
        Int.mul_ne_zero (by decide) (intPowNat_ne_zero_w17 (K : Int) (by omega) 3)
      by_cases h4 : 4 * (W : Int) - (K : Int) = 0
      · omega
      · exact False.elim (Int.mul_ne_zero (Int.mul_ne_zero hk3_nz h4) hq_nz hz)
    · intro hK4
      rw [hK4]; simp [Int.natCast_mul, Int.sub_self, Int.mul_zero, Int.zero_mul]
  have hu2_neg_on_ray : K = 4 * W ->
      intDet 12 (laurentTwoBaseT4U3Mat12 W K 2) =
        intPowNat (W : Int) 18 * intDet 12 (laurentTwoBaseT4U3Mat12 1 4 2) ∧
      intDet 12 (laurentTwoBaseT4U3Mat12 W K 2) < 0 := by
    intro hK4; subst hK4
    have hsc := det12_t4u3_ray_4w_u2_scale_w17 W
    refine ⟨hsc, ?_⟩
    rw [hsc, hd142]
    have hw_pos : intPowNat (W : Int) 18 > 0 := by
      have := intPowNat_pos_of_pos_w17 W 18 hW; omega
    exact Int.mul_neg_of_pos_of_neg hw_pos (by decide)
  refine ⟨hiff_4w, hu2_neg_on_ray, ?_⟩
  rintro ⟨hz1, hz2⟩
  have hlt0 := (hu2_neg_on_ray (hiff_4w.mp hz1)).2
  omega

-- ----------------------------------------------------------------------------
-- Section 2C: All-Rotation Cyclic `p`-Pivot Brox Minimization, Constructive
--             Multi-Prime Companion Cascades `{3, 7, 15, 31, 51, 73, 255, 511}`,
--             & `m = 6` Balanced + Convergent Semi-Balanced Eliminations
--             (`W17_H2`, Branch P3.4, `zero custom axioms`)
-- ----------------------------------------------------------------------------

/--
  Theorem W17.2c (`m_block_all_rotation_cyclic_brox_and_multiprime_elimination`,
  `zero custom axioms`):
  Constructive Multi-Prime Mersenne Companion-Divisor Cascade (`{3, 7, 15, 31, 51, 73, 255, 511}`),
  All-Rotation (`∀ j < blocks.length`) Cyclic `p`-Pivot & Coupled `henselOddInvModPow2` Brox
  Squeezes, `82×` 5-Pivot Elimination of Balanced `m = 6` `[(17, 2)^5, (17, 50)]` (Escaping All 6
  Four-Pivot Rotations), & `36×` Rotation-`2` `s = 9` Hensel (`1827 * D`) Elimination of Convergent
  `(W = 41, K = 65)` Semi-Balanced `m = 6` `[(7, 3), (7, 3), (7, 9), (7, 3), (7, 3), (6, 3)]`
  (Escaping All 6 Non-Hensel 5-Pivot Rotations, `Branch P3.4`, witness
  `M1_BALANCED_6BLOCK_FOUR_PIVOT_ESCAPE`, `W17_H2`).
-/
theorem m_block_all_rotation_cyclic_brox_and_multiprime_elimination :
    ((2 ^ 2 - 1 = 3 ∧ 2 ^ 3 - 1 = 7 ∧ 2 ^ 4 - 1 = 15 ∧ 2 ^ 5 - 1 = 31 ∧
      51 ∣ (2 ^ 8 - 1) ∧ 2 ^ 8 - 1 = 255 ∧ 73 ∣ (2 ^ 9 - 1) ∧ 2 ^ 9 - 1 = 511) ∧
     (∀ (b0 : Nat × Nat) (rest : List (Nat × Nat)) (qs : List Nat) (d_a d_mult : Nat),
      let blocks := b0 :: rest
      let W := blockWeightSum blocks
      let K := blockStepSum blocks
      let D := 2 ^ K - 3 ^ W
      (∀ b ∈ blocks, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      3 ^ W < 2 ^ K ->
      qs.length = blocks.length ->
      (∀ j : Nat, j < blocks.length -> D * natAt qs j = broxSpiralCarry (rotBlocks j blocks)) ->
      Nat.Coprime 3 D ∧
      (d_a ≥ 1 -> (∀ b ∈ blocks, d_a ∣ b.2) -> d_mult ∣ (2 ^ d_a - 1) ->
        Nat.Coprime d_mult D -> d_mult ∣ natListGcd qs))) ∧
    (∀ (blocks : List (Nat × Nat)) (qs : List Nat) (j : Nat)
       (pivots : List (Nat × Nat)) (b_last : Nat × Nat) (tail : List (Nat × Nat)) (d_mult : Nat),
      let W := blockWeightSum blocks
      let K := blockStepSum blocks
      let D := 2 ^ K - 3 ^ W
      (∀ b ∈ blocks, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      3 ^ W < 2 ^ K ->
      qs.length = blocks.length ->
      (∀ i : Nat, i < blocks.length -> D * natAt qs i = broxSpiralCarry (rotBlocks i blocks)) ->
      j < blocks.length ->
      rotBlocks j blocks = pivots ++ (b_last :: tail) ->
      d_mult ∣ natListGcd qs ->
      d_mult * D ≤ multiPivotCarryUB pivots b_last tail) ∧
    (∀ (blocks : List (Nat × Nat)) (qs : List Nat) (j : Nat)
       (bj : Nat × Nat) (ps : List (Nat × Nat)) (b_last : Nat × Nat) (tail : List (Nat × Nat))
       (s d_mult : Nat),
      let W := blockWeightSum blocks
      let K := blockStepSum blocks
      let D := 2 ^ K - 3 ^ W
      blocks.length ≥ 2 ->
      (∀ b ∈ blocks, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      3 ^ W < 2 ^ K ->
      qs.length = blocks.length ->
      (∀ i : Nat, i < blocks.length -> D * natAt qs i = broxSpiralCarry (rotBlocks i blocks)) ->
      j < blocks.length ->
      rotBlocks j blocks = (bj :: ps) ++ (b_last :: tail) ->
      s ≥ 4 ->
      bj.2 ≥ s ->
      d_mult % 2 = 1 ->
      d_mult ∣ natListGcd qs ->
      (henselOddInvModPow2 s (3 ^ bj.1 * d_mult) * d_mult) * D ≤
        multiPivotCarryUB (bj :: ps) b_last tail) ∧
    (let blocks_bal6 : List (Nat × Nat) := [(17, 2), (17, 2), (17, 2), (17, 2), (17, 2), (17, 50)]
     let D_bal6 := 2 ^ blockStepSum blocks_bal6 - 3 ^ blockWeightSum blocks_bal6
     let blocks_mp6 : List (Nat × Nat) := [(7, 3), (7, 3), (7, 9), (7, 3), (7, 3), (6, 3)]
     let D_mp6 := 2 ^ blockStepSum blocks_mp6 - 3 ^ blockWeightSum blocks_mp6
     (∀ j : Nat, j < 6 ->
       match rotBlocks j blocks_bal6 with
       | b0 :: b1 :: b2 :: b3 :: rest => multiPivotCarryUB [b0, b1, b2] b3 rest > 3 * D_bal6
       | _ => False) ∧
     82 * multiPivotCarryUB [(17, 2), (17, 2), (17, 2), (17, 2)] (17, 2) [(17, 50)] < 3 * D_bal6 ∧
     ¬ (∃ qs : List Nat,
       qs.length = 6 ∧
       ∀ j : Nat, j < 6 -> D_bal6 * natAt qs j = broxSpiralCarry (rotBlocks j blocks_bal6)) ∧
     ¬ (∃ u0 : List MixedSRSSym, dp2AnnotatedChain u0 (dp2BlocksToShifts blocks_bal6) u0) ∧
     Nat.Coprime 7 D_mp6 ∧
     (∀ j : Nat, j < 6 ->
       match rotBlocks j blocks_mp6 with
       | b0 :: b1 :: b2 :: b3 :: b4 :: rest => multiPivotCarryUB [b0, b1, b2, b3] b4 rest > 7 * D_mp6
       | _ => False) ∧
     henselOddInvModPow2 9 (3 ^ 7 * 7) * 7 = 1827 ∧
     36 * multiPivotCarryUB [(7, 9), (7, 3), (7, 3), (6, 3)] (7, 3) [(7, 3)] < 1827 * D_mp6 ∧
     ¬ (∃ qs : List Nat,
       qs.length = 6 ∧
       ∀ j : Nat, j < 6 -> D_mp6 * natAt qs j = broxSpiralCarry (rotBlocks j blocks_mp6)) ∧
     ¬ (∃ u0 : List MixedSRSSym, dp2AnnotatedChain u0 (dp2BlocksToShifts blocks_mp6) u0)) := by
  have hcarry_ub := m_block_recursive_p_pivot_brox_squeeze.1
  have hgcd_natAt : ∀ (xs : List Nat) (idx : Nat), idx < xs.length -> natListGcd xs ∣ natAt xs idx := by
    intro xs; induction xs with
    | nil => intro _ h; simp at h
    | cons x xtl ih =>
      intro idx h; cases idx with
      | zero => exact Nat.gcd_dvd_left x (natListGcd xtl)
      | succ idx' =>
        exact Nat.dvd_trans (Nat.gcd_dvd_right x (natListGcd xtl)) (ih idx' (by simp at h; omega))
  have hdvd_gcd_all : ∀ (d : Nat) (xs : List Nat),
      (∀ idx : Nat, idx < xs.length -> d ∣ natAt xs idx) -> d ∣ natListGcd xs := by
    intro d xs; induction xs with
    | nil => intros; exact Nat.dvd_zero d
    | cons x xtl ih =>
      intro hall
      exact Nat.dvd_gcd (hall 0 (by simp))
        (ih (fun idx h => hall (idx + 1) (by simp; omega)))
  have hpos_rot_mem : ∀ (bs : List (Nat × Nat)) (j : Nat) (b : Nat × Nat),
      (∀ x ∈ bs, x.1 ≥ 1 ∧ x.2 ≥ 1) -> b ∈ rotBlocks j bs -> b.1 ≥ 1 ∧ b.2 ≥ 1 := by
    intro bs j b hpos hb
    unfold rotBlocks at hb
    rcases List.mem_append.mp hb with hd | ht
    · exact hpos b (List.mem_of_mem_drop hd)
    · exact hpos b (List.mem_of_mem_take ht)
  have hcar_pos : ∀ bs : List (Nat × Nat), bs ≠ [] ->
      (∀ b ∈ bs, b.1 ≥ 1 ∧ b.2 ≥ 1) -> broxSpiralCarry bs ≥ 1 := by
    intro bs; induction bs with
    | nil => intro hne; exact False.elim (hne rfl)
    | cons b0 btl ih =>
      intro _ hpos
      have hb0_2 : 2 ^ b0.2 - 1 ≥ 1 := by
        have hp : 2 ^ b0.2 ≥ 2 := by simpa using pow2_mono_nat (hpos b0 (List.Mem.head _)).2
        omega
      cases btl with
      | nil => simpa [broxSpiralCarry] using hb0_2
      | cons b1 tl' =>
        unfold broxSpiralCarry
        have hp3 : 3 ^ blockWeightSum (b1 :: tl') ≥ 1 := pow3_pos_nat _
        have hm := Nat.mul_le_mul hp3 hb0_2
        omega
  -- Part 1: Constructive Mersenne companion-divisor cascade:
  have hm_cascade : ∀ (b0 : Nat × Nat) (rest : List (Nat × Nat)) (qs : List Nat) (d_a d_mult : Nat),
      let blocks := b0 :: rest
      let W := blockWeightSum blocks
      let K := blockStepSum blocks
      let D := 2 ^ K - 3 ^ W
      (∀ b ∈ blocks, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      3 ^ W < 2 ^ K ->
      qs.length = blocks.length ->
      (∀ j : Nat, j < blocks.length -> D * natAt qs j = broxSpiralCarry (rotBlocks j blocks)) ->
      Nat.Coprime 3 D ∧
      (d_a ≥ 1 -> (∀ b ∈ blocks, d_a ∣ b.2) -> d_mult ∣ (2 ^ d_a - 1) ->
        Nat.Coprime d_mult D -> d_mult ∣ natListGcd qs) := by
    intro b0 rest qs d_a d_mult; dsimp only
    intro hpos hlt hlen hspec
    let blocks := b0 :: rest
    let W := blockWeightSum blocks
    let K := blockStepSum blocks
    let D := 2 ^ K - 3 ^ W
    have hW1 : W ≥ 1 := by have := (hpos b0 (List.Mem.head _)).1; dsimp [W, blocks, blockWeightSum]; omega
    have hcop3 : Nat.Coprime 3 D := by
      rw [Nat.coprime_iff_gcd_eq_one]
      have hg3 : Nat.gcd 3 D ≤ 3 := Nat.le_of_dvd (by decide) (Nat.gcd_dvd_left 3 D)
      have hg_pos : Nat.gcd 3 D ≥ 1 := Nat.gcd_pos_of_pos_left D (by decide)
      have hg_l := Nat.gcd_dvd_left 3 D
      have hg_r := Nat.gcd_dvd_right 3 D
      rcases (by omega : Nat.gcd 3 D = 1 ∨ Nat.gcd 3 D = 2 ∨ Nat.gcd 3 D = 3) with h1 | h2 | h3
      · exact h1
      · exfalso; rw [h2] at hg_l; rcases hg_l with ⟨k, hk⟩; omega
      · exfalso
        rw [h3] at hg_r
        rcases hg_r with ⟨c, hc⟩
        have hp3_d : 3 ∣ 3 ^ W := ⟨3 ^ (W - 1), by
          conv => lhs; rw [show W = (W - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]⟩
        rcases hp3_d with ⟨c3, hc3⟩
        have h2_m3 : 2 ^ K % 3 = 0 := by
          have heq2 : 2 ^ K = 3 * (c + c3) := by
            have hlt_wk : 3 ^ W < 2 ^ K := hlt
            dsimp [D] at hc; rw [Nat.mul_add]
            generalize 2 ^ K = P2, 3 ^ W = P3 at hlt_wk hc hc3 ⊢; omega
          rw [heq2, Nat.mul_mod_right]
        have h2_nz : ∀ n : Nat, 2 ^ n % 3 ≠ 0 := by
          intro n; induction n with | zero => decide | succ n' ihn => rw [Nat.pow_succ, Nat.mul_mod]; omega
        exact h2_nz K h2_m3
    refine ⟨hcop3, ?_⟩
    intro hda hall_da hdm_mers hcop_dD
    have hmers_mul : ∀ k : Nat, (2 ^ d_a - 1) ∣ (2 ^ (d_a * k) - 1) := by
      intro k; induction k with
      | zero => exact ⟨0, by simp⟩
      | succ k' ih =>
        rcases ih with ⟨q, hq⟩
        refine ⟨2 ^ (d_a * k') + q, ?_⟩
        rw [Nat.mul_succ, Nat.pow_add, Nat.mul_add]
        have hp_k : 2 ^ (d_a * k') ≥ 1 := nat_pow_pos_of_pos 2 (by decide) _
        have hp_d : 2 ^ d_a ≥ 2 := by simpa using pow2_mono_nat hda
        have hsub : (2 ^ d_a - 1) * 2 ^ (d_a * k') = 2 ^ (d_a * k') * 2 ^ d_a - 2 ^ (d_a * k') := by
          rw [Nat.sub_mul, Nat.one_mul, Nat.mul_comm]
        have hle_p : 2 ^ (d_a * k') ≤ 2 ^ (d_a * k') * 2 ^ d_a := Nat.le_mul_of_pos_right _ (by omega)
        omega
    have hcar_dvd : ∀ bs : List (Nat × Nat),
        (∀ b ∈ bs, d_a ∣ b.2) -> (2 ^ d_a - 1) ∣ broxSpiralCarry bs := by
      intro bs; induction bs with
      | nil => intros; exact ⟨0, by simp [broxSpiralCarry]⟩
      | cons x xtl ih =>
        intro hall_b
        rcases hall_b x (List.Mem.head _) with ⟨kx, hkx⟩
        have hx_d : (2 ^ d_a - 1) ∣ (2 ^ x.2 - 1) := hkx ▸ hmers_mul kx
        cases xtl with
        | nil => simpa [broxSpiralCarry] using hx_d
        | cons y ytl =>
          unfold broxSpiralCarry
          rcases hx_d with ⟨qx, hqx⟩
          rcases ih (fun b hb => hall_b b (List.Mem.tail x hb)) with ⟨qr, hqr⟩
          rw [hqx, hqr]
          exact ⟨3 ^ blockWeightSum (y :: ytl) * qx + 2 ^ (x.2 + y.1) * qr, by rw [Nat.mul_add]; ac_rfl⟩
    apply hdvd_gcd_all d_mult qs
    intro j hj
    rw [hlen] at hj
    have hd_rot : d_mult ∣ broxSpiralCarry (rotBlocks j blocks) :=
      Nat.dvd_trans hdm_mers (hcar_dvd (rotBlocks j blocks) (fun b hb => by
        unfold rotBlocks at hb
        rcases List.mem_append.mp hb with hd | ht
        · exact hall_da b (List.mem_of_mem_drop hd)
        · exact hall_da b (List.mem_of_mem_take ht)))
    rw [← hspec j hj] at hd_rot
    exact hcop_dD.dvd_of_dvd_mul_left hd_rot
  -- Part 2: All-rotation cyclic `p`-pivot squeeze:
  have hcyc_piv : ∀ (blocks : List (Nat × Nat)) (qs : List Nat) (j : Nat)
       (pivots : List (Nat × Nat)) (b_last : Nat × Nat) (tail : List (Nat × Nat)) (d_mult : Nat),
      let W := blockWeightSum blocks
      let K := blockStepSum blocks
      let D := 2 ^ K - 3 ^ W
      (∀ b ∈ blocks, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      3 ^ W < 2 ^ K ->
      qs.length = blocks.length ->
      (∀ i : Nat, i < blocks.length -> D * natAt qs i = broxSpiralCarry (rotBlocks i blocks)) ->
      j < blocks.length ->
      rotBlocks j blocks = pivots ++ (b_last :: tail) ->
      d_mult ∣ natListGcd qs ->
      d_mult * D ≤ multiPivotCarryUB pivots b_last tail := by
    intro blocks qs j pivots b_last tail d_mult; dsimp only
    intro hpos _ hlen hspec hj hrot_eq hdvd_g
    have hdvd_qj : d_mult ∣ natAt qs j :=
      Nat.dvd_trans hdvd_g (hgcd_natAt qs j (by omega))
    have hpos_r : ∀ b ∈ pivots ++ (b_last :: tail), b.1 ≥ 1 ∧ b.2 ≥ 1 := by
      intro b hb; rw [← hrot_eq] at hb; exact hpos_rot_mem blocks j b hpos hb
    have hc_pos : broxSpiralCarry (rotBlocks j blocks) ≥ 1 := by
      rw [hrot_eq]; exact hcar_pos _ (by simp) hpos_r
    have hsp_j := hspec j hj
    have hqj_pos : natAt qs j ≥ 1 := by
      cases hq : natAt qs j with
      | zero => rw [hq, Nat.mul_zero] at hsp_j; omega
      | succ _ => omega
    have hdm_le : d_mult ≤ natAt qs j := Nat.le_of_dvd hqj_pos hdvd_qj
    calc d_mult * (2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks)
        ≤ natAt qs j * (2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks) := Nat.mul_le_mul_right _ hdm_le
      _ = (2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks) * natAt qs j := Nat.mul_comm _ _
      _ = broxSpiralCarry (rotBlocks j blocks) := hsp_j
      _ = broxSpiralCarry (pivots ++ (b_last :: tail)) := by rw [hrot_eq]
      _ ≤ multiPivotCarryUB pivots b_last tail := hcarry_ub pivots b_last tail hpos_r
  -- Part 3: All-rotation cyclic `p`-pivot + `henselOddInvModPow2` squeeze:
  have hcyc_hensel : ∀ (blocks : List (Nat × Nat)) (qs : List Nat) (j : Nat)
       (bj : Nat × Nat) (ps : List (Nat × Nat)) (b_last : Nat × Nat) (tail : List (Nat × Nat))
       (s d_mult : Nat),
      let W := blockWeightSum blocks
      let K := blockStepSum blocks
      let D := 2 ^ K - 3 ^ W
      blocks.length ≥ 2 ->
      (∀ b ∈ blocks, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      3 ^ W < 2 ^ K ->
      qs.length = blocks.length ->
      (∀ i : Nat, i < blocks.length -> D * natAt qs i = broxSpiralCarry (rotBlocks i blocks)) ->
      j < blocks.length ->
      rotBlocks j blocks = (bj :: ps) ++ (b_last :: tail) ->
      s ≥ 4 ->
      bj.2 ≥ s ->
      d_mult % 2 = 1 ->
      d_mult ∣ natListGcd qs ->
      (henselOddInvModPow2 s (3 ^ bj.1 * d_mult) * d_mult) * D ≤
        multiPivotCarryUB (bj :: ps) b_last tail := by
    intro blocks qs j bj ps b_last tail s d_mult; dsimp only
    intro hge2 hpos hlt hlen hspec hj hrot_eq hs4 hbj_s hd_odd hdvd_g
    have hwt_app : ∀ xs ys : List (Nat × Nat),
        blockWeightSum (xs ++ ys) = blockWeightSum xs + blockWeightSum ys ∧
        blockStepSum (xs ++ ys) = blockStepSum xs + blockStepSum ys := by
      intro xs ys; induction xs with
      | nil => simp [blockWeightSum, blockStepSum]
      | cons x xtl ih => simp only [List.cons_append, blockWeightSum, blockStepSum, ih.1, ih.2]; omega
    have hw_rot : blockWeightSum (rotBlocks j blocks) = blockWeightSum blocks ∧
        blockStepSum (rotBlocks j blocks) = blockStepSum blocks := by
      unfold rotBlocks
      rcases hwt_app (blocks.drop j) (blocks.take j) with ⟨w1, k1⟩
      rcases hwt_app (blocks.take j) (blocks.drop j) with ⟨w2, k2⟩
      rw [List.take_append_drop j blocks] at w2 k2
      exact ⟨by omega, by omega⟩
    let j1 := (j + 1) % blocks.length
    have hj1 : j1 < blocks.length := Nat.mod_lt (j + 1) (by omega)
    let qj := natAt qs j
    let qj1 := natAt qs j1
    have hdvd_qj : d_mult ∣ qj := Nat.dvd_trans hdvd_g (hgcd_natAt qs j (by omega))
    have hsp0 := hspec j hj
    have hsp1 := hspec j1 hj1
    rw [← rotBlocks_one_rotBlocks_cf_w17 blocks hge2 j hj] at hsp1
    have hlt_rot : 3 ^ blockWeightSum ((bj :: ps) ++ (b_last :: tail)) <
        2 ^ blockStepSum ((bj :: ps) ++ (b_last :: tail)) := by
      rwa [← hrot_eq, hw_rot.1, hw_rot.2]
    have hD_rot : 2 ^ blockStepSum ((bj :: ps) ++ (b_last :: tail)) -
        3 ^ blockWeightSum ((bj :: ps) ++ (b_last :: tail)) =
        2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks := by
      rw [← hrot_eq, hw_rot.1, hw_rot.2]
    rw [hrot_eq, ← hD_rot] at hsp0 hsp1
    have hqj_ge : qj ≥ henselOddInvModPow2 s (3 ^ bj.1 * d_mult) * d_mult := by
      cases hps : ps with
      | nil =>
        simp only [hps, List.cons_append, List.nil_append] at hlt_rot hsp0 hsp1
        have hrec := (m_block_two_pivot_telescoping_and_2adic_quotient_boost.1.2
          bj b_last tail hlt_rot).2 qj qj1 hsp0 hsp1
        exact hensel_quotient_boost_cf_w17 s bj.1 bj.2 b_last.1 qj qj1 d_mult
          hs4 hbj_s hd_odd hdvd_qj hrec
      | cons b_n ptl =>
        simp only [hps, List.cons_append] at hlt_rot hsp0 hsp1
        have hrec := (m_block_two_pivot_telescoping_and_2adic_quotient_boost.1.2
          bj b_n (ptl ++ (b_last :: tail)) hlt_rot).2 qj qj1 hsp0 hsp1
        exact hensel_quotient_boost_cf_w17 s bj.1 bj.2 b_n.1 qj qj1 d_mult
          hs4 hbj_s hd_odd hdvd_qj hrec
    have hpos_r : ∀ b ∈ (bj :: ps) ++ (b_last :: tail), b.1 ≥ 1 ∧ b.2 ≥ 1 := by
      intro b hb; rw [← hrot_eq] at hb; exact hpos_rot_mem blocks j b hpos hb
    calc (henselOddInvModPow2 s (3 ^ bj.1 * d_mult) * d_mult) *
          (2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks)
        ≤ qj * (2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks) := Nat.mul_le_mul_right _ hqj_ge
      _ = (2 ^ blockStepSum ((bj :: ps) ++ (b_last :: tail)) -
            3 ^ blockWeightSum ((bj :: ps) ++ (b_last :: tail))) * qj := by
            rw [hD_rot, Nat.mul_comm]
      _ = broxSpiralCarry ((bj :: ps) ++ (b_last :: tail)) := hsp0
      _ ≤ multiPivotCarryUB (bj :: ps) b_last tail := hcarry_ub (bj :: ps) b_last tail hpos_r
  refine ⟨⟨⟨rfl, rfl, rfl, rfl, by decide, rfl, by decide, rfl⟩, hm_cascade⟩,
          hcyc_piv, hcyc_hensel, ?_⟩
  -- Part 4: `blocks_bal6` (`82×` 5-pivot) & `blocks_mp6` (`36×` rotation-2 `s = 9` Hensel `1827`):
  dsimp only
  let blocks_bal6 : List (Nat × Nat) := [(17, 2), (17, 2), (17, 2), (17, 2), (17, 2), (17, 50)]
  let D_bal6 := 2 ^ blockStepSum blocks_bal6 - 3 ^ blockWeightSum blocks_bal6
  let blocks_mp6 : List (Nat × Nat) := [(7, 3), (7, 3), (7, 9), (7, 3), (7, 3), (6, 3)]
  let D_mp6 := 2 ^ blockStepSum blocks_mp6 - 3 ^ blockWeightSum blocks_mp6
  have hbal6_rot4 : ∀ j : Nat, j < 6 ->
      match rotBlocks j blocks_bal6 with
      | b0 :: b1 :: b2 :: b3 :: rest => multiPivotCarryUB [b0, b1, b2] b3 rest > 3 * D_bal6
      | _ => False := by
    intro j hj6
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp only [blocks_bal6, D_bal6, rotBlocks, List.drop, List.take,
                  List.cons_append, List.nil_append]; decide)
  have hbal6_82 :
      82 * multiPivotCarryUB [(17, 2), (17, 2), (17, 2), (17, 2)] (17, 2) [(17, 50)] <
        3 * D_bal6 := by decide
  have hno_bal6 : ¬ (∃ qs : List Nat,
      qs.length = 6 ∧
      ∀ j : Nat, j < 6 -> D_bal6 * natAt qs j = broxSpiralCarry (rotBlocks j blocks_bal6)) := by
    rintro ⟨qs, hlen6, hqs_spec⟩
    rcases hm_cascade (17, 2) [(17, 2), (17, 2), (17, 2), (17, 2), (17, 50)] qs 2 3
      (by decide) (by decide) hlen6 hqs_spec with ⟨hcop3, hcasc3⟩
    have h3_dvd : 3 ∣ natListGcd qs := hcasc3 (by decide) (by decide) (by decide) hcop3
    have hle := hcyc_piv blocks_bal6 qs 0 [(17, 2), (17, 2), (17, 2), (17, 2)] (17, 2) [(17, 50)] 3
      (by decide) (by decide) hlen6 hqs_spec (by decide) rfl h3_dvd
    change 3 * D_bal6 ≤ multiPivotCarryUB [(17, 2), (17, 2), (17, 2), (17, 2)] (17, 2) [(17, 50)] at hle
    have hpos_ub : multiPivotCarryUB [(17, 2), (17, 2), (17, 2), (17, 2)] (17, 2) [(17, 50)] ≥ 1 := by decide
    omega
  have hcop7_mp6 : Nat.Coprime 7 D_mp6 := by decide
  have hmp6_rot5 : ∀ j : Nat, j < 6 ->
      match rotBlocks j blocks_mp6 with
      | b0 :: b1 :: b2 :: b3 :: b4 :: rest => multiPivotCarryUB [b0, b1, b2, b3] b4 rest > 7 * D_mp6
      | _ => False := by
    intro j hj6
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp only [blocks_mp6, D_mp6, rotBlocks, List.drop, List.take,
                  List.cons_append, List.nil_append]; decide)
  have hmp6_inv : henselOddInvModPow2 9 (3 ^ 7 * 7) * 7 = 1827 := by decide
  have hmp6_36 :
      36 * multiPivotCarryUB [(7, 9), (7, 3), (7, 3), (6, 3)] (7, 3) [(7, 3)] <
        1827 * D_mp6 := by decide
  have hno_mp6 : ¬ (∃ qs : List Nat,
      qs.length = 6 ∧
      ∀ j : Nat, j < 6 -> D_mp6 * natAt qs j = broxSpiralCarry (rotBlocks j blocks_mp6)) := by
    rintro ⟨qs, hlen6, hqs_spec⟩
    have h7_dvd : 7 ∣ natListGcd qs :=
      (hm_cascade (7, 3) [(7, 3), (7, 9), (7, 3), (7, 3), (6, 3)] qs 3 7
        (by decide) (by decide) hlen6 hqs_spec).2 (by decide) (by decide) (by decide) hcop7_mp6
    have hle := hcyc_hensel blocks_mp6 qs 2 (7, 9) [(7, 3), (7, 3), (6, 3)] (7, 3) [(7, 3)] 9 7
      (by decide) (by decide) (by decide) hlen6 hqs_spec (by decide) rfl
      (by decide) (by decide) (by decide) h7_dvd
    rw [hmp6_inv] at hle
    change 1827 * D_mp6 ≤ multiPivotCarryUB [(7, 9), (7, 3), (7, 3), (6, 3)] (7, 3) [(7, 3)] at hle
    have hpos_ub : multiPivotCarryUB [(7, 9), (7, 3), (7, 3), (6, 3)] (7, 3) [(7, 3)] ≥ 1 := by decide
    omega
  have hno_dp2_bal6 : ¬ (∃ u0 : List MixedSRSSym,
      dp2AnnotatedChain u0 (dp2BlocksToShifts blocks_bal6) u0) := by
    rintro ⟨u0, hann⟩
    rcases (leftAnchoredDP2_no_1_to_20_cycles_and_all_m_block_locks.2.2
      (17, 2) [(17, 2), (17, 2), (17, 2), (17, 2), (17, 50)] u0 (by decide) hann).2.2 with
      ⟨us, qs, hus_len, hqs_len, _, hrot_all, _⟩
    exact hno_bal6 ⟨qs, hqs_len, fun j hj => by
      have hdrop_ne : us.drop j ≠ [] := by
        intro he; have := congrArg List.length he; rw [List.length_drop, hus_len] at this
        change 6 - j = 0 at this; omega
      have hrj := hrot_all j hj
      cases hd : us.drop j with
      | nil => exact False.elim (hdrop_ne hd)
      | cons _ _ => rw [hd] at hrj; exact hrj.2.2.2.2⟩
  have hno_dp2_mp6 : ¬ (∃ u0 : List MixedSRSSym,
      dp2AnnotatedChain u0 (dp2BlocksToShifts blocks_mp6) u0) := by
    rintro ⟨u0, hann⟩
    rcases (leftAnchoredDP2_no_1_to_20_cycles_and_all_m_block_locks.2.2
      (7, 3) [(7, 3), (7, 9), (7, 3), (7, 3), (6, 3)] u0 (by decide) hann).2.2 with
      ⟨us, qs, hus_len, hqs_len, _, hrot_all, _⟩
    exact hno_mp6 ⟨qs, hqs_len, fun j hj => by
      have hdrop_ne : us.drop j ≠ [] := by
        intro he; have := congrArg List.length he; rw [List.length_drop, hus_len] at this
        change 6 - j = 0 at this; omega
      have hrj := hrot_all j hj
      cases hd : us.drop j with
      | nil => exact False.elim (hdrop_ne hd)
      | cons _ _ => rw [hd] at hrj; exact hrj.2.2.2.2⟩
  exact ⟨hbal6_rot4, hbal6_82, hno_bal6, hno_dp2_bal6,
         hcop7_mp6, hmp6_rot5, hmp6_inv, hmp6_36, hno_mp6, hno_dp2_mp6⟩

end CollatzFormal
