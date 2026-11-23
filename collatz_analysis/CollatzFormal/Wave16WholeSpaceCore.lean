/-
  CollatzFormal/Wave16WholeSpaceCore.lean
  Wave 16 Whole-Space Mathematical & CS Proof Loop (Core — Fronts A & B):
  1. Front A — All-Dimension (`∀ d ≥ 1`) `.R`-Boundary Vector-Independence Law,
     100% Active-`.T` Top-Row Off-Diagonal Cascade Collapse (`12` `.T` symbols on `c39`,
     `24` `.T` symbols on `c78`), & Universal `GenOmegaNonUniformMixedZeroDiagTRMatTower`
     Impossibility on `c39` & `c78`,
     Three Infinite 3-Parameter Coupled `.R`-Boundary-Growth (`k ≥ 2`) + `.B`/`.T`-Top-Row
     Mixed Zero-Diagonal `d = 2` Cones (`bndParamMat2DC39`, `coupledBTRTopRowMat2DC39`, &
     `coupledBTRTopRowMat2DC78`) Locked by Parameterized 2-Rule, 7-Rule, & 14-Rule Farkas Syzygies,
     & Unconditional `1..15`-Cycle Freedom Across ALL `DP2` Words + 3-Block `.R`-Carrying
     `leftAnchoredDP2Step` Cycle, Equal-Shift, & Balanced-Tuple Locks (`W16_H1`, Branch P4.3)
  2. Front B — General Rectangular `∀ U > T ≥ 1` Row-Side `(2^(W * u) - 1)^(T * (U - T))`
     Vandermonde Divisibility, Universal `(U * T) × (U * T)` Joint `Nat.lcm` Row+Column
     Confluent Divisibility & Joint-LCM Reduced Majorant Bound, + `8 × 8` `(T = 2, U = 4)`
     Row-Column Overlap Certificate,
     Rank-3 Two-Base `9 × 9` `(T = 3, U = 3)` Global `u ∈ {1..17}` Non-Vanishing (`P^1(F_p)` Sieves),
     Cone-Free `∀ u ≥ 1` Non-Vanishing Outside `(81 * w', 32 * k')` & Along `(81 * c, 16 * c)`,
     `(81 * c, 8 * c)`, `(27 * c, 16 * c)` + Uniform Logarithmic Multi-`u` Zero-Horizon Bound,
     & Choice-Free Universal Recursive Arbitrary-`p` (`∀ pivots : List (Nat × Nat)`) Cross-Block
     Brox Carry Squeeze Coupled With `henselOddInvModPow2` Boosts Eliminating Balanced `m = 5`
     Families (`W16_H2`, Branches P3.2–P3.4)

  Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

import CollatzFormal.Wave15WholeSpace

namespace CollatzFormal

-- ============================================================================
-- SECTION 1: Front A (Branch P4.3) — `.R`-Boundary Vector Independence,
--            All-Dimension `.T`-Top-Row Cascade Collapse, 3-Parameter Coupled
--            `.R`-Boundary + `.T`-Top-Row Farkas Locks, & `1..15`-Cycle /
--            3-Block `leftAnchoredDP2Step` Laws (`W16_H1`)
-- ============================================================================

private theorem mul_pow_w16c (a b : Nat) : ∀ n : Nat, (a * b) ^ n = a ^ n * b ^ n
  | 0 => rfl
  | n + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, mul_pow_w16c a b n]
    ac_rfl

private theorem pow_mono_base_w16c (a b : Nat) (hle : a ≤ b) : ∀ n : Nat, a ^ n ≤ b ^ n
  | 0 => Nat.le_refl 1
  | n + 1 => Nat.mul_le_mul (pow_mono_base_w16c a b hle n) hle

private def toFinWordW16 (N : Nat) (hN : N ≥ 1) : List Nat -> List (Fin N)
  | [] => []
  | x :: xs => (if h : x < N then ⟨x, h⟩ else ⟨0, hN⟩) :: toFinWordW16 N hN xs

private def toFinRulesW16 (N : Nat) (hN : N ≥ 1) :
    List (List Nat × List Nat) -> List (List (Fin N) × List (Fin N))
  | [] => []
  | (l, r) :: rs => (toFinWordW16 N hN l, toFinWordW16 N hN r) :: toFinRulesW16 N hN rs

private def c39FastRulesW16 : List (List (Fin 42) × List (Fin 42)) :=
  toFinRulesW16 42 (by decide)
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

private def c78FastRulesW16 : List (List (Fin 84) × List (Fin 84)) :=
  toFinRulesW16 84 (by decide)
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
private theorem c39_eq_fastRules_w16 :
    filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List) = c39FastRulesW16 := by decide

set_option maxRecDepth 65536 in
private theorem c78_eq_fastRules_w16 :
    filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List) = c78FastRulesW16 := by decide

-- ----------------------------------------------------------------------------
-- Section 1A: `.R`-Boundary Vector Independence, Active-`.T` Top-Row Cascade,
--             & All-Dimension `GenOmegaNonUniformMixedZeroDiagTRMatTower` Collapse
-- ----------------------------------------------------------------------------

/-- Non-final symbols of `w` lie outside `.R` (`2 * M ≤ s.val < 4 * M`). -/
def nonLastOutsideRBool (M : Nat) : List (Fin (14 * M)) -> Bool
  | [] => true
  | [_] => true
  | s :: s2 :: tl => decide (s.val < 2 * M ∨ s.val ≥ 4 * M) && nonLastOutsideRBool M (s2 :: tl)

/-- Dual `k`-level `ω^k` Hofbauer–Waldmann natural matrix tower over `Fin (14 * M)` of dimension
    `d ≥ 1` in the non-uniform mixed zero-diagonal TR stratum:
    - Every symbol satisfies `(M_s)_{0,0} ≥ 1` (including arbitrary `.R`-boundary growth
      `(M_6)_{0,0}, (M_9)_{0,0} ≥ 2`),
    - `.L` (`s < 2 * M`) and `.B` (`4 * M ≤ s < 8 * M`) have top row `[1, 0, ..., 0]` and
      arbitrary bottom `d - 1` rows,
    - `.T` (`s ≥ 8 * M`) has **completely arbitrary** `.T`-top-row entries and bottom rows,
    - `.R` (`2 * M ≤ s < 4 * M`) has **completely arbitrary** `d × d` entries. -/
def GenOmegaNonUniformMixedZeroDiagTRMatTower (M d : Nat) (hd : d ≥ 1) :
    Nat -> List (List (Fin (14 * M)) × List (Fin (14 * M))) -> Prop
  | 0, rules => rules = []
  | k + 1, rules =>
    rules = [] ∨
    ∃ (rem : List (List (Fin (14 * M)) × List (Fin (14 * M))))
      (mat : Fin (14 * M) -> Fin d -> Fin d -> Nat)
      (v : Fin (14 * M) -> Fin d -> Nat),
      (∀ s : Fin (14 * M), mat s ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1) ∧
      (∀ s : Fin (14 * M), (s.val < 2 * M ∨ (4 * M ≤ s.val ∧ s.val < 8 * M)) ->
        mat s ⟨0, hd⟩ ⟨0, hd⟩ = 1 ∧ ∀ j : Fin d, j.val ≥ 1 -> mat s ⟨0, hd⟩ j = 0) ∧
      (∀ r ∈ rules,
        (∀ i j : Fin d, evalFinWordMat (14 * M) d mat r.1 i j ≥ evalFinWordMat (14 * M) d mat r.2 i j) ∧
        (∀ i : Fin d, evalFinWordVec (14 * M) d mat v r.1 i ≥ evalFinWordVec (14 * M) d mat v r.2 i)) ∧
      (∀ r ∈ rules,
        ¬ (evalFinWordVec (14 * M) d mat v r.1 ⟨0, hd⟩ >
           evalFinWordVec (14 * M) d mat v r.2 ⟨0, hd⟩) ->
        r ∈ rem) ∧
      GenOmegaNonUniformMixedZeroDiagTRMatTower M d hd k rem

private theorem evalFinWordVec_congr_outside_R_w16 (M d : Nat)
    (mat1 mat2 : Fin (14 * M) -> Fin d -> Fin d -> Nat)
    (v : Fin (14 * M) -> Fin d -> Nat)
    (heq_out : ∀ s : Fin (14 * M), (s.val < 2 * M ∨ s.val ≥ 4 * M) ->
      ∀ i j : Fin d, mat1 s i j = mat2 s i j) :
    ∀ (w : List (Fin (14 * M))),
      nonLastOutsideRBool M w = true ->
      ∀ i : Fin d, evalFinWordVec (14 * M) d mat1 v w i = evalFinWordVec (14 * M) d mat2 v w i
  | [], _, _ => rfl
  | [s], _, i => by
    have hz : ∀ m : Nat, natSumPrefix d (fun _ => (0 : Nat)) m = 0 := by
      intro m; induction m with
      | zero => rfl
      | succ m' ih =>
        simp only [natSumPrefix]
        by_cases hm : m' < d <;> simp only [hm, dite_true, dite_false, ih, Nat.add_zero]
    change v s i + natSumPrefix d (fun k => mat1 s i k * (0 : Nat)) d =
      v s i + natSumPrefix d (fun k => mat2 s i k * (0 : Nat)) d
    simp only [Nat.mul_zero, hz d]
  | s :: s2 :: tl, hb, i => by
    unfold nonLastOutsideRBool at hb
    rcases bool_and_split hb with ⟨hs_b, htl_b⟩
    have hs_out := of_decide_eq_true hs_b
    have ih := evalFinWordVec_congr_outside_R_w16 M d mat1 mat2 v heq_out (s2 :: tl) htl_b
    change v s i + natSumPrefix d (fun k => mat1 s i k * evalFinWordVec (14 * M) d mat1 v (s2 :: tl) k) d =
      v s i + natSumPrefix d (fun k => mat2 s i k * evalFinWordVec (14 * M) d mat2 v (s2 :: tl) k) d
    have hsum_eq : ∀ m : Nat,
        natSumPrefix d (fun k => mat1 s i k * evalFinWordVec (14 * M) d mat1 v (s2 :: tl) k) m =
        natSumPrefix d (fun k => mat2 s i k * evalFinWordVec (14 * M) d mat2 v (s2 :: tl) k) m := by
      intro m; induction m with
      | zero => rfl
      | succ m' ihm =>
        simp only [natSumPrefix]
        by_cases hm : m' < d
        · simp only [hm, dite_true, ihm, heq_out s hs_out i ⟨m', hm⟩, ih ⟨m', hm⟩]
        · simp only [hm, dite_false, ihm]
    rw [hsum_eq d]

private def cascadeRulesC39 : List (Nat × Nat × Nat × Nat) :=
  [(1, 18, 2, 36), (2, 20, 2, 38), (36, 22, 20, 40), (38, 16, 13, 31),
   (38, 23, 20, 41), (40, 17, 16, 32), (40, 21, 23, 39), (31, 14, 18, 29),
   (32, 13, 18, 28), (28, 18, 22, 33), (29, 20, 22, 35), (33, 22, 17, 37)]

private def cascadeRulesC78 : List (Nat × Nat × Nat × Nat) :=
  [(1, 36, 2, 72), (1, 39, 5, 75), (5, 38, 2, 74), (5, 41, 5, 77),
   (74, 31, 28, 61), (74, 34, 25, 64), (75, 43, 41, 79), (75, 46, 38, 82),
   (77, 44, 38, 80), (77, 47, 41, 83), (79, 42, 44, 78), (79, 45, 47, 81),
   (82, 32, 31, 62), (82, 35, 34, 65), (62, 25, 39, 55), (62, 28, 36, 58),
   (64, 26, 36, 56), (64, 29, 39, 59), (55, 36, 43, 66), (55, 39, 46, 69),
   (59, 38, 43, 68), (59, 41, 46, 71), (69, 43, 35, 73), (69, 46, 32, 76)]

private def inZeroTopSetBool (M : Nat) (acc : List Nat) (x : Nat) : Bool :=
  decide (x < 2 * M ∨ (4 * M ≤ x ∧ x < 8 * M)) || acc.any (· == x)

private def checkCascadeValidBool (M : Nat) (hM : M ≥ 1)
    (rules : List (List (Fin (14 * M)) × List (Fin (14 * M))))
    (acc : List Nat) : List (Nat × Nat × Nat × Nat) -> Option (List Nat)
  | [] => some acc
  | (s1, s2, u1, u2) :: rest =>
    if h : s1 < 14 * M ∧ s2 < 14 * M ∧ u1 < 14 * M ∧ u2 < 14 * M then
      let r_cand : List (Fin (14 * M)) × List (Fin (14 * M)) :=
        ([⟨s1, h.1⟩, ⟨s2, h.2.1⟩], [⟨u1, h.2.2.1⟩, ⟨u2, h.2.2.2⟩])
      if inZeroTopSetBool M acc s1 && inZeroTopSetBool M acc s2 &&
         rules.any (· == r_cand) then
        checkCascadeValidBool M hM rules (u2 :: acc) rest
      else none
    else none

private def checkFullTRCollapseCertBool (M : Nat) (hM : M ≥ 1)
    (rules : List (List (Fin (14 * M)) × List (Fin (14 * M))))
    (casc : List (Nat × Nat × Nat × Nat)) : Bool :=
  match checkCascadeValidBool M hM rules [] casc with
  | none => false
  | some finalAcc =>
    rules.all (fun r =>
      nonLastOutsideRBool M r.1 && nonLastOutsideRBool M r.2 &&
      decide (r.1 ≠ [] ∧ r.2 ≠ []) &&
      (r.1 ++ r.2).all (fun s =>
        decide (s.val < 8 * M) || inZeroTopSetBool M finalAcc s.val))

private theorem cascade_step_forces_zero_toprow_w16 (N d : Nat) (hd : d ≥ 1)
    (mat : Fin N -> Fin d -> Fin d -> Nat)
    (s1 s2 u1 u2 : Fin N)
    (hu1_pos : mat u1 ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1)
    (hs1_z : ∀ j : Fin d, j.val ≥ 1 -> mat s1 ⟨0, hd⟩ j = 0)
    (hs2_z : ∀ j : Fin d, j.val ≥ 1 -> mat s2 ⟨0, hd⟩ j = 0)
    (hweak : ∀ i j : Fin d,
      evalFinWordMat N d mat [s1, s2] i j ≥ evalFinWordMat N d mat [u1, u2] i j) :
    ∀ j : Fin d, j.val ≥ 1 -> mat u2 ⟨0, hd⟩ j = 0 := by
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
  have hmat1_eq : ∀ (x : Fin N) (k j : Fin d), evalFinWordMat N d mat [x] k j = mat x k j := by
    intro x k j
    change natSumPrefix d (fun m => mat x k m * natMatId d m j) d = mat x k j
    have hst : ∀ m : Nat, m ≤ d ->
        natSumPrefix d (fun c => mat x k c * natMatId d c j) m =
          (if j.val < m then mat x k j else 0) := by
      intro m hm; induction m with
      | zero => simp [natSumPrefix]
      | succ m' ih =>
        have hm_lt : m' < d := hm
        simp only [natSumPrefix, hm_lt, dite_true, ih (Nat.le_of_lt hm)]
        by_cases heq : m' = j.val
        · have hcf : (⟨m', hm_lt⟩ : Fin d) = j := Fin.ext heq
          rw [hcf, ite_false_of_w10 (by omega : ¬ (j.val < m')),
              ite_true_of_w10 (by omega : j.val < m' + 1)]
          simp [natMatId]
        · have hne : ¬ (m' = j.val) := heq
          have hid0 : natMatId d ⟨m', hm_lt⟩ j = 0 := by simp [natMatId, hne]
          rw [hid0, Nat.mul_zero, Nat.add_zero]
          by_cases hlt : j.val < m'
          · rw [ite_true_of_w10 hlt, ite_true_of_w10 (by omega)]
          · rw [ite_false_of_w10 hlt, ite_false_of_w10 (by omega)]
    rw [hst d (Nat.le_refl d), ite_true_of_w10 j.isLt]
  intro j hj1
  have hlhs0 : evalFinWordMat N d mat [s1, s2] z0 j = 0 := by
    change natSumPrefix d (fun k => mat s1 z0 k * evalFinWordMat N d mat [s2] k j) d = 0
    rw [hsum_single0 _ (fun k hk => by rw [hs1_z k hk, Nat.zero_mul]),
        hmat1_eq s2 z0 j, hs2_z j hj1, Nat.mul_zero]
  have hrhs_ge : evalFinWordMat N d mat [u1, u2] z0 j ≥ mat u2 z0 j := by
    change natSumPrefix d (fun k => mat u1 z0 k * evalFinWordMat N d mat [u2] k j) d ≥ mat u2 z0 j
    have hg := hsum_ge0 (fun k => mat u1 z0 k * evalFinWordMat N d mat [u2] k j)
    rw [hmat1_eq u2 z0 j] at hg
    have hm := Nat.mul_le_mul (show mat u1 z0 z0 ≥ 1 from hu1_pos) (Nat.le_refl (mat u2 z0 j))
    rw [Nat.one_mul] at hm
    omega
  have hw := hweak z0 j
  change mat u2 z0 j = 0
  omega

/-- Count active `.T` symbols (`s ≥ 8 * M` appearing in `rules`). -/
def countActiveTSymsBool (M : Nat)
    (rules : List (List (Fin (14 * M)) × List (Fin (14 * M)))) : Nat :=
  let rec loop : Nat -> Nat
    | 0 => 0
    | k + 1 =>
      (if k ≥ 8 * M && symAppearsInRulesBool (14 * M) k rules then 1 else 0) + loop k
  loop (14 * M)

set_option maxRecDepth 65536 in
private theorem tr_cascade_c39_c78_certs :
    countActiveTSymsBool 3 c39FastRulesW16 = 12 ∧
    countActiveTSymsBool 6 c78FastRulesW16 = 24 ∧
    checkFullTRCollapseCertBool 3 (by decide) c39FastRulesW16 cascadeRulesC39 = true ∧
    checkFullTRCollapseCertBool 6 (by decide) c78FastRulesW16 cascadeRulesC78 = true ∧
    checkPositiveParikhSyzygyFastBool 42 c39FastRulesW16 syzTwoSidedMod3OmitR3Core39 = true ∧
    checkPositiveParikhSyzygyFastBool 84 c78FastRulesW16 syzTwoSidedMod6OmitR3Core78 = true ∧
    c39FastRulesW16 ≠ [] ∧
    c78FastRulesW16 ≠ [] := by decide

private theorem mem_of_countFinOcc_pos_w16 (N : Nat) (s : Fin N) :
    ∀ w : List (Fin N), countFinOcc N s w ≥ 1 -> s ∈ w
  | [], h => by simp [countFinOcc] at h
  | x :: xs, h => by
    by_cases hx : x = s
    · subst hx; exact List.Mem.head _
    · have hne_v : x.val ≠ s.val := fun hv => hx (Fin.ext hv)
      simp [countFinOcc, hne_v] at h
      exact List.Mem.tail x (mem_of_countFinOcc_pos_w16 N s xs h)

private theorem exists_rule_of_symAppearsInRulesBool_w16 (N : Nat) (s : Fin N) :
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
      · exact List.mem_append_left _ (mem_of_countFinOcc_pos_w16 N s l0 h1)
      · exact List.mem_append_right _ (mem_of_countFinOcc_pos_w16 N s r0 (by omega))
    · rcases exists_rule_of_symAppearsInRulesBool_w16 N s rtl hthere with ⟨r', hr', hs_m⟩
      exact ⟨r', List.Mem.tail (l0, r0) hr', hs_m⟩

private theorem cascade_sound_all_active_T_zero_toprow_w16
    (M : Nat) (hM : M ≥ 1)
    (rules : List (List (Fin (14 * M)) × List (Fin (14 * M))))
    (casc : List (Nat × Nat × Nat × Nat))
    (hcert : checkFullTRCollapseCertBool M hM rules casc = true)
    (d : Nat) (hd : d ≥ 1) (mat : Fin (14 * M) -> Fin d -> Fin d -> Nat)
    (hm_pos : ∀ s : Fin (14 * M), mat s ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1)
    (hLB_z : ∀ s : Fin (14 * M), (s.val < 2 * M ∨ (4 * M ≤ s.val ∧ s.val < 8 * M)) ->
      ∀ j : Fin d, j.val ≥ 1 -> mat s ⟨0, hd⟩ j = 0)
    (hweak : ∀ r ∈ rules, ∀ i j : Fin d,
      evalFinWordMat (14 * M) d mat r.1 i j ≥ evalFinWordMat (14 * M) d mat r.2 i j) :
    (∀ r ∈ rules,
      nonLastOutsideRBool M r.1 = true ∧ nonLastOutsideRBool M r.2 = true ∧
      r.1 ≠ [] ∧ r.2 ≠ []) ∧
    (∀ s : Fin (14 * M), s.val ≥ 8 * M ->
      symAppearsInRulesBool (14 * M) s.val rules = true ->
      ∀ j : Fin d, j.val ≥ 1 -> mat s ⟨0, hd⟩ j = 0) := by
  unfold checkFullTRCollapseCertBool at hcert
  cases hc_opt : checkCascadeValidBool M hM rules [] casc with
  | none => rw [hc_opt] at hcert; cases hcert
  | some finalAcc =>
    rw [hc_opt] at hcert
    have hin_sound : ∀ (acc : List Nat),
        (∀ x ∈ acc, ∀ (hx : x < 14 * M) (j : Fin d), j.val ≥ 1 -> mat ⟨x, hx⟩ ⟨0, hd⟩ j = 0) ->
        ∀ (y : Nat) (hy : y < 14 * M), inZeroTopSetBool M acc y = true ->
          ∀ j : Fin d, j.val ≥ 1 -> mat ⟨y, hy⟩ ⟨0, hd⟩ j = 0 := by
      intro acc hacc y hy hin j hj1
      unfold inZeroTopSetBool at hin
      rcases Bool.or_eq_true_iff.mp hin with hlb_b | hany_b
      · exact hLB_z ⟨y, hy⟩ (of_decide_eq_true hlb_b) j hj1
      · rcases List.any_eq_true.mp hany_b with ⟨x, hx_mem, hxy_b⟩
        have hxy : x = y := Nat.eq_of_beq_eq_true hxy_b
        subst hxy
        exact hacc x hx_mem hy j hj1
    have hwalk : ∀ (steps : List (Nat × Nat × Nat × Nat)) (acc : List Nat),
        (∀ x ∈ acc, ∀ (hx : x < 14 * M) (j : Fin d), j.val ≥ 1 -> mat ⟨x, hx⟩ ⟨0, hd⟩ j = 0) ->
        checkCascadeValidBool M hM rules acc steps = some finalAcc ->
        ∀ x ∈ finalAcc, ∀ (hx : x < 14 * M) (j : Fin d), j.val ≥ 1 -> mat ⟨x, hx⟩ ⟨0, hd⟩ j = 0 := by
      intro steps; induction steps with
      | nil =>
        intro acc hacc hs; simp only [checkCascadeValidBool, Option.some.injEq] at hs
        subst hs; exact hacc
      | cons st tl ih =>
        rcases st with ⟨s1, s2, u1, u2⟩
        intro acc hacc hs
        unfold checkCascadeValidBool at hs
        by_cases hlt : s1 < 14 * M ∧ s2 < 14 * M ∧ u1 < 14 * M ∧ u2 < 14 * M
        · simp only [hlt] at hs
          by_cases hcond : (inZeroTopSetBool M acc s1 && inZeroTopSetBool M acc s2 &&
              rules.any (· == ([⟨s1, hlt.1⟩, ⟨s2, hlt.2.1⟩], [⟨u1, hlt.2.2.1⟩, ⟨u2, hlt.2.2.2⟩]))) = true
          · simp only [hcond, ite_true] at hs
            rcases bool_and_split hcond with ⟨hs12, hmem_b⟩
            rcases bool_and_split hs12 with ⟨hs1_b, hs2_b⟩
            rcases List.any_eq_true.mp hmem_b with ⟨r_m, hr_mem, hr_eq_b⟩
            have hr_eq : r_m = ([⟨s1, hlt.1⟩, ⟨s2, hlt.2.1⟩], [⟨u1, hlt.2.2.1⟩, ⟨u2, hlt.2.2.2⟩]) :=
              beq_iff_eq.mp hr_eq_b
            subst hr_eq
            have hu2_z := cascade_step_forces_zero_toprow_w16 (14 * M) d hd mat
              ⟨s1, hlt.1⟩ ⟨s2, hlt.2.1⟩ ⟨u1, hlt.2.2.1⟩ ⟨u2, hlt.2.2.2⟩
              (hm_pos _)
              (hin_sound acc hacc s1 hlt.1 hs1_b)
              (hin_sound acc hacc s2 hlt.2.1 hs2_b)
              (hweak _ hr_mem)
            apply ih (u2 :: acc) _ hs
            intro x hx_c hx_lt j hj1
            cases hx_c with
            | head => exact hu2_z j hj1
            | tail _ htl_m => exact hacc x htl_m hx_lt j hj1
          · simp [hcond] at hs
        · simp [hlt] at hs
    have hfinal_z := hwalk casc [] (fun _ h => by cases h) hc_opt
    have hall_r := List.all_eq_true.mp hcert
    refine ⟨?_, ?_⟩
    · intro r hr
      rcases bool_and_split (hall_r r hr) with ⟨hb1, _⟩
      rcases bool_and_split hb1 with ⟨hb2, hne_b⟩
      rcases bool_and_split hb2 with ⟨hn1, hn2⟩
      rcases of_decide_eq_true hne_b with ⟨hne1, hne2⟩
      exact ⟨hn1, hn2, hne1, hne2⟩
    · intro s hs8 hsym_app
      rcases exists_rule_of_symAppearsInRulesBool_w16 (14 * M) s rules hsym_app with ⟨r, hr_mem, hs_mem⟩
      rcases bool_and_split (hall_r r hr_mem) with ⟨_, hcov⟩
      have hsc := List.all_eq_true.mp hcov s hs_mem
      rcases Bool.or_eq_true_iff.mp hsc with hlt8_b | hin_b
      · have hlt8 := of_decide_eq_true hlt8_b; omega
      · exact hin_sound finalAcc hfinal_z s.val s.isLt hin_b

private def topLeftOnlyMatW16 (N d : Nat) (hd : d ≥ 1)
    (mat : Fin N -> Fin d -> Fin d -> Nat) (s : Fin N) (i j : Fin d) : Nat :=
  if i.val == 0 && j.val == 0 then mat s ⟨0, hd⟩ ⟨0, hd⟩ else 0

private def prodDiagW16 (N : Nat) (f : Fin N -> Nat) : List (Fin N) -> Nat
  | [] => 1
  | s :: rest => f s * prodDiagW16 N f rest

private theorem eval_topLeftOnlyMat_and_outsideR_zero_toprow_w16
    (M d : Nat) (hd : d ≥ 1) (mat : Fin (14 * M) -> Fin d -> Fin d -> Nat)
    (w : List (Fin (14 * M))) (hne : w ≠ [])
    (hnlast : nonLastOutsideRBool M w = true)
    (hw_z : ∀ s ∈ w, (s.val < 2 * M ∨ s.val ≥ 4 * M) ->
      ∀ j : Fin d, j.val ≥ 1 -> mat s ⟨0, hd⟩ j = 0) :
    let z0 : Fin d := ⟨0, hd⟩
    evalFinWordMat (14 * M) d mat w z0 z0 =
      prodDiagW16 (14 * M) (fun s => mat s z0 z0) w ∧
    (∀ i j : Fin d,
      evalFinWordMat (14 * M) d (topLeftOnlyMatW16 (14 * M) d hd mat) w i j =
        if i.val = 0 ∧ j.val = 0 then prodDiagW16 (14 * M) (fun s => mat s z0 z0) w else 0) := by
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
        | zero => have h0f : (⟨0, hm_lt⟩ : Fin d) = z0 := rfl; rw [h0f]; simp
        | succ m'' => rw [hz ⟨m'' + 1, hm_lt⟩ (by dsimp; omega), Nat.add_zero]; simp
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
  have hmat1_eq : ∀ (m_fn : Fin (14 * M) -> Fin d -> Fin d -> Nat) (x : Fin (14 * M)) (i j : Fin d),
      evalFinWordMat (14 * M) d m_fn [x] i j = m_fn x i j := by
    intro m_fn x i j
    change natSumPrefix d (fun c => m_fn x i c * natMatId d c j) d = m_fn x i j
    have hst : ∀ m : Nat, m ≤ d ->
        natSumPrefix d (fun c => m_fn x i c * natMatId d c j) m =
          (if j.val < m then m_fn x i j else 0) := by
      intro m hm; induction m with
      | zero => simp [natSumPrefix]
      | succ m' ih =>
        have hm_lt : m' < d := hm
        simp only [natSumPrefix, hm_lt, dite_true, ih (Nat.le_of_lt hm)]
        by_cases heq : m' = j.val
        · have hcf : (⟨m', hm_lt⟩ : Fin d) = j := Fin.ext heq
          rw [hcf, ite_false_of_w10 (by omega : ¬ (j.val < m')),
              ite_true_of_w10 (by omega : j.val < m' + 1)]
          simp [natMatId]
        · have hne_c : ¬ (m' = j.val) := heq
          have hid0 : natMatId d ⟨m', hm_lt⟩ j = 0 := by simp [natMatId, hne_c]
          rw [hid0, Nat.mul_zero, Nat.add_zero]
          by_cases hlt : j.val < m'
          · rw [ite_true_of_w10 hlt, ite_true_of_w10 (by omega)]
          · rw [ite_false_of_w10 hlt, ite_false_of_w10 (by omega)]
    rw [hst d (Nat.le_refl d), ite_true_of_w10 j.isLt]
  induction w with
  | nil => exact False.elim (hne rfl)
  | cons s rest ih =>
    cases rest with
    | nil =>
      refine ⟨by rw [hmat1_eq mat s z0 z0]; simp only [prodDiagW16, Nat.mul_one]; rfl, ?_⟩
      intro i j
      rw [hmat1_eq _ s i j]
      unfold topLeftOnlyMatW16
      by_cases hij : i.val = 0 ∧ j.val = 0
      · rw [ite_true_of_w10 hij]; simp [hij.1, hij.2, prodDiagW16]
      · rw [ite_false_of_w10 hij]
        have hbf : (i.val == 0 && j.val == 0) = false := by
          by_cases hi0 : i.val = 0
          · have hj_ne : j.val ≠ 0 := fun hj0 => hij ⟨hi0, hj0⟩
            simp [hi0, beq_false_of_ne hj_ne]
          · simp [beq_false_of_ne hi0]
        simp [hbf]
    | cons s2 tl =>
      unfold nonLastOutsideRBool at hnlast
      rcases bool_and_split hnlast with ⟨hs_b, htl_nl⟩
      have hs_out := of_decide_eq_true hs_b
      have hs_z := hw_z s (List.Mem.head _) hs_out
      rcases ih (by simp) htl_nl (fun x hx => hw_z x (List.Mem.tail s hx)) with ⟨ih_mat, ih_tl⟩
      refine ⟨?_, ?_⟩
      · change natSumPrefix d (fun k => mat s z0 k * evalFinWordMat (14 * M) d mat (s2 :: tl) k z0) d =
          mat s z0 z0 * prodDiagW16 (14 * M) (fun x => mat x z0 z0) (s2 :: tl)
        rw [hsum_single0 _ (fun k hk => by rw [hs_z k hk, Nat.zero_mul]), ih_mat]
      · intro i j
        change natSumPrefix d (fun k =>
          topLeftOnlyMatW16 (14 * M) d hd mat s i k *
            evalFinWordMat (14 * M) d (topLeftOnlyMatW16 (14 * M) d hd mat) (s2 :: tl) k j) d = _
        by_cases hij : i.val = 0 ∧ j.val = 0
        · rw [ite_true_of_w10 hij]
          have hie : i = z0 := Fin.ext hij.1
          subst hie
          rw [hsum_single0 _ (fun k hk => by
                have hk_ne : (k.val == 0) = false := beq_false_of_ne (by omega)
                simp [topLeftOnlyMatW16, hk_ne]),
              ih_tl z0 j, ite_true_of_w10 ⟨rfl, hij.2⟩]
          simp [topLeftOnlyMatW16, z0, prodDiagW16]
        · rw [ite_false_of_w10 hij]
          apply hsum_zero; intro k
          by_cases hi0 : i.val = 0
          · have hj_ne : j.val ≠ 0 := fun hj0 => hij ⟨hi0, hj0⟩
            rw [ih_tl k j, ite_false_of_w10 (fun h => hj_ne h.2), Nat.mul_zero]
          · have hi_ne : (i.val == 0) = false := beq_false_of_ne hi0
            simp [topLeftOnlyMatW16, hi_ne]

/--
  Theorem W16.1a (`twosided_c39_c78_nonuniform_mixed_zerodiag_tr_impossibility`,
  `zero custom axioms`):
  Universal All-Dimension (`∀ d ≥ 1`) `.R`-Boundary Vector-Independence Law, 100% Active-`.T`
  Top-Row Off-Diagonal Cascade Collapse (`12` `.T` Symbols of `c39` & `24` `.T` Symbols of `c78`),
  & Universal Impossibility of `GenOmegaNonUniformMixedZeroDiagTRMatTower` Across `TwoSided(2 × 3)`
  `c39` & `TwoSided(2 × 6)` `c78` (`Branch P4.3`, witness
  `ZPOS_C39_COUPLED_R_BND_AND_T_TOPROW_FARKAS_ESCAPE`, `W16_H1`).
-/
theorem twosided_c39_c78_nonuniform_mixed_zerodiag_tr_impossibility :
    let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
    let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
    (countActiveTSymsBool 3 c39 = 12 ∧ countActiveTSymsBool 6 c78 = 24) ∧
    ((∀ (d : Nat) (mat1 mat2 : Fin 42 -> Fin d -> Fin d -> Nat) (v : Fin 42 -> Fin d -> Nat),
        (∀ s : Fin 42, (s.val < 6 ∨ s.val ≥ 12) -> ∀ i j : Fin d, mat1 s i j = mat2 s i j) ->
        ∀ r ∈ c39, ∀ i : Fin d,
          evalFinWordVec 42 d mat1 v r.1 i = evalFinWordVec 42 d mat2 v r.1 i ∧
          evalFinWordVec 42 d mat1 v r.2 i = evalFinWordVec 42 d mat2 v r.2 i) ∧
     (∀ (d : Nat) (mat1 mat2 : Fin 84 -> Fin d -> Fin d -> Nat) (v : Fin 84 -> Fin d -> Nat),
        (∀ s : Fin 84, (s.val < 12 ∨ s.val ≥ 24) -> ∀ i j : Fin d, mat1 s i j = mat2 s i j) ->
        ∀ r ∈ c78, ∀ i : Fin d,
          evalFinWordVec 84 d mat1 v r.1 i = evalFinWordVec 84 d mat2 v r.1 i ∧
          evalFinWordVec 84 d mat1 v r.2 i = evalFinWordVec 84 d mat2 v r.2 i)) ∧
    (∀ (d : Nat) (hd : d ≥ 1) (mat : Fin 42 -> Fin d -> Fin d -> Nat),
      let z0 : Fin d := ⟨0, hd⟩
      (∀ s : Fin 42, mat s z0 z0 ≥ 1) ->
      (∀ s : Fin 42, (s.val < 6 ∨ (12 ≤ s.val ∧ s.val < 24)) ->
        ∀ j : Fin d, j.val ≥ 1 -> mat s z0 j = 0) ->
      (∀ r ∈ c39, ∀ i j : Fin d,
        evalFinWordMat 42 d mat r.1 i j ≥ evalFinWordMat 42 d mat r.2 i j) ->
      ∀ s : Fin 42, s.val ≥ 24 -> symAppearsInRulesBool 42 s.val c39 = true ->
        mat s z0 z0 = 1 ∧ ∀ j : Fin d, j.val ≥ 1 -> mat s z0 j = 0) ∧
    (∀ (d : Nat) (hd : d ≥ 1) (mat : Fin 84 -> Fin d -> Fin d -> Nat),
      let z0 : Fin d := ⟨0, hd⟩
      (∀ s : Fin 84, mat s z0 z0 ≥ 1) ->
      (∀ s : Fin 84, (s.val < 12 ∨ (24 ≤ s.val ∧ s.val < 48)) ->
        ∀ j : Fin d, j.val ≥ 1 -> mat s z0 j = 0) ->
      (∀ r ∈ c78, ∀ i j : Fin d,
        evalFinWordMat 84 d mat r.1 i j ≥ evalFinWordMat 84 d mat r.2 i j) ->
      ∀ s : Fin 84, s.val ≥ 48 -> symAppearsInRulesBool 84 s.val c78 = true ->
        mat s z0 z0 = 1 ∧ ∀ j : Fin d, j.val ≥ 1 -> mat s z0 j = 0) ∧
    (∀ (d : Nat) (hd : d ≥ 1) (k : Nat),
      ¬ GenOmegaNonUniformMixedZeroDiagTRMatTower 3 d hd k c39 ∧
      ¬ GenOmegaNonUniformMixedZeroDiagTRMatTower 6 d hd k c78) := by
  dsimp only
  rw [c39_eq_fastRules_w16, c78_eq_fastRules_w16]
  rcases tr_cascade_c39_c78_certs with
    ⟨hcnt39, hcnt78, hcert39, hcert78, hsyz39, hsyz78, hne39, hne78⟩
  have hlock39_w15 := c39_c78_interior_topleft_unit_lock_and_boundary_growth.2.1
  have hlock78_w15 := c39_c78_interior_topleft_unit_lock_and_boundary_growth.2.2.1
  rw [c39_eq_fastRules_w16] at hlock39_w15
  rw [c78_eq_fastRules_w16] at hlock78_w15
  have hsym_in_rules : ∀ (N : Nat) (rs : List (List (Fin N) × List (Fin N)))
      (r : List (Fin N) × List (Fin N)) (s : Fin N),
      r ∈ rs -> (s ∈ r.1 ∨ s ∈ r.2) -> symAppearsInRulesBool N s.val rs = true := by
    intro N rs r s hr hs
    rcases hs with h1 | h2
    · exact symAppearsInRulesBool_of_mem_lhs N s rs r hr h1
    · exact symAppearsInRulesBool_of_mem_rhs N s rs r hr h2
  have hmaster_lock : ∀ (M : Nat) (hM : M ≥ 1)
      (rules : List (List (Fin (14 * M)) × List (Fin (14 * M))))
      (casc : List (Nat × Nat × Nat × Nat)),
      checkFullTRCollapseCertBool M hM rules casc = true ->
      (∀ (d : Nat) (hd : d ≥ 1) (mat : Fin (14 * M) -> Fin d -> Fin d -> Nat),
        let z0 : Fin d := ⟨0, hd⟩
        (∀ s : Fin (14 * M), mat s z0 z0 ≥ 1) ->
        ((∀ (s : Fin (14 * M)) (i : Fin d), i.val ≥ 1 -> mat s i z0 = 0) ∨
         (∀ (s : Fin (14 * M)) (j : Fin d), j.val ≥ 1 -> mat s z0 j = 0)) ->
        (∀ r ∈ rules, ∀ i j : Fin d,
          evalFinWordMat (14 * M) d mat r.1 i j ≥ evalFinWordMat (14 * M) d mat r.2 i j) ->
        ∀ s : Fin (14 * M), s.val ≥ 4 * M ->
          symAppearsInRulesBool (14 * M) s.val rules = true -> mat s z0 z0 = 1) ->
      ∀ (d : Nat) (hd : d ≥ 1) (mat : Fin (14 * M) -> Fin d -> Fin d -> Nat),
        let z0 : Fin d := ⟨0, hd⟩
        (∀ s : Fin (14 * M), mat s z0 z0 ≥ 1) ->
        (∀ s : Fin (14 * M), (s.val < 2 * M ∨ (4 * M ≤ s.val ∧ s.val < 8 * M)) ->
          ∀ j : Fin d, j.val ≥ 1 -> mat s z0 j = 0) ->
        (∀ r ∈ rules, ∀ i j : Fin d,
          evalFinWordMat (14 * M) d mat r.1 i j ≥ evalFinWordMat (14 * M) d mat r.2 i j) ->
        ∀ s : Fin (14 * M), s.val ≥ 8 * M ->
          symAppearsInRulesBool (14 * M) s.val rules = true ->
          mat s z0 z0 = 1 ∧ ∀ j : Fin d, j.val ≥ 1 -> mat s z0 j = 0 := by
    intro M hM rules casc hcert hlock_int d hd mat; dsimp only
    intro hm1 hLB_z hweak
    let z0 : Fin d := ⟨0, hd⟩
    rcases cascade_sound_all_active_T_zero_toprow_w16 M hM rules casc hcert d hd mat hm1 hLB_z hweak with
      ⟨hr_shape, hT_z⟩
    let dMat := topLeftOnlyMatW16 (14 * M) d hd mat
    have hdMat_m1 : ∀ s : Fin (14 * M), dMat s z0 z0 ≥ 1 := by
      intro s; dsimp [dMat, topLeftOnlyMatW16, z0]; exact hm1 s
    have hdMat_r0 : ∀ (s : Fin (14 * M)) (j : Fin d), j.val ≥ 1 -> dMat s z0 j = 0 := by
      intro s j hj1
      have hj_ne : (j.val == 0) = false := beq_false_of_ne (by omega)
      simp [dMat, topLeftOnlyMatW16, hj_ne]
    have hdMat_weak : ∀ r ∈ rules, ∀ i j : Fin d,
        evalFinWordMat (14 * M) d dMat r.1 i j ≥ evalFinWordMat (14 * M) d dMat r.2 i j := by
      intro r hr i j
      rcases hr_shape r hr with ⟨hnl1, hnl2, hne1, hne2⟩
      have hw1_z : ∀ x ∈ r.1, (x.val < 2 * M ∨ x.val ≥ 4 * M) ->
          ∀ k : Fin d, k.val ≥ 1 -> mat x z0 k = 0 := by
        intro x hx hout
        by_cases hlt8 : x.val < 8 * M
        · exact hLB_z x (by rcases hout with h1 | h2; exact Or.inl h1; exact Or.inr ⟨h2, hlt8⟩)
        · exact hT_z x (by omega) (hsym_in_rules (14 * M) rules r x hr (Or.inl hx))
      have hw2_z : ∀ x ∈ r.2, (x.val < 2 * M ∨ x.val ≥ 4 * M) ->
          ∀ k : Fin d, k.val ≥ 1 -> mat x z0 k = 0 := by
        intro x hx hout
        by_cases hlt8 : x.val < 8 * M
        · exact hLB_z x (by rcases hout with h1 | h2; exact Or.inl h1; exact Or.inr ⟨h2, hlt8⟩)
        · exact hT_z x (by omega) (hsym_in_rules (14 * M) rules r x hr (Or.inr hx))
      rcases eval_topLeftOnlyMat_and_outsideR_zero_toprow_w16 M d hd mat r.1 hne1 hnl1 hw1_z with
        ⟨hev1, htl1⟩
      rcases eval_topLeftOnlyMat_and_outsideR_zero_toprow_w16 M d hd mat r.2 hne2 hnl2 hw2_z with
        ⟨hev2, htl2⟩
      dsimp only [dMat]
      rw [htl1 i j, htl2 i j]
      by_cases hij : i.val = 0 ∧ j.val = 0
      · rw [ite_true_of_w10 hij, ite_true_of_w10 hij, ← hev1, ← hev2]
        exact hweak r hr z0 z0
      · rw [ite_false_of_w10 hij, ite_false_of_w10 hij]; exact Nat.le_refl 0
    intro s hs8 hact
    have hunit : dMat s z0 z0 = 1 :=
      hlock_int d hd dMat hdMat_m1 (Or.inr hdMat_r0) hdMat_weak s (by omega) hact
    dsimp [dMat, topLeftOnlyMatW16, z0] at hunit
    exact ⟨hunit, hT_z s hs8 hact⟩
  have htr_imposs : ∀ (M : Nat) (hM : M ≥ 1)
      (core : List (List (Fin (14 * M)) × List (Fin (14 * M))))
      (casc : List (Nat × Nat × Nat × Nat)) (syz : List Nat),
      core ≠ [] ->
      checkFullTRCollapseCertBool M hM core casc = true ->
      checkPositiveParikhSyzygyFastBool (14 * M) core syz = true ->
      (∀ (d : Nat) (hd : d ≥ 1) (mat : Fin (14 * M) -> Fin d -> Fin d -> Nat),
        let z0 : Fin d := ⟨0, hd⟩
        (∀ s : Fin (14 * M), mat s z0 z0 ≥ 1) ->
        ((∀ (s : Fin (14 * M)) (i : Fin d), i.val ≥ 1 -> mat s i z0 = 0) ∨
         (∀ (s : Fin (14 * M)) (j : Fin d), j.val ≥ 1 -> mat s z0 j = 0)) ->
        (∀ r ∈ core, ∀ i j : Fin d,
          evalFinWordMat (14 * M) d mat r.1 i j ≥ evalFinWordMat (14 * M) d mat r.2 i j) ->
        ∀ s : Fin (14 * M), s.val ≥ 4 * M ->
          symAppearsInRulesBool (14 * M) s.val core = true -> mat s z0 z0 = 1) ->
      ∀ (d : Nat) (hd : d ≥ 1) (k : Nat),
        ¬ GenOmegaNonUniformMixedZeroDiagTRMatTower M d hd k core := by
    intro M hM core casc syz hne hcert hsyz hlock_int d hd
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
    have hno_strict : ∀ (mat : Fin N -> Fin d -> Fin d -> Nat) (v : Fin N -> Fin d -> Nat),
        (∀ s : Fin N, mat s z0 z0 ≥ 1) ->
        (∀ s : Fin N, (s.val < 2 * M ∨ (4 * M ≤ s.val ∧ s.val < 8 * M)) ->
          mat s z0 z0 = 1 ∧ ∀ j : Fin d, j.val ≥ 1 -> mat s z0 j = 0) ->
        (∀ r ∈ core,
          (∀ i j : Fin d, evalFinWordMat N d mat r.1 i j ≥ evalFinWordMat N d mat r.2 i j) ∧
          evalFinWordVec N d mat v r.1 z0 ≥ evalFinWordVec N d mat v r.2 z0) ->
        ∀ r ∈ core, evalFinWordVec N d mat v r.1 z0 = evalFinWordVec N d mat v r.2 z0 := by
      intro mat v hm1 hLB hweak_c
      have hT_lock := hmaster_lock M hM core casc hcert hlock_int d hd mat hm1
        (fun s hs => (hLB s hs).2) (fun r hr => (hweak_c r hr).1)
      rcases cascade_sound_all_active_T_zero_toprow_w16 M hM core casc hcert d hd mat hm1
        (fun s hs => (hLB s hs).2) (fun r hr => (hweak_c r hr).1) with ⟨hr_sh, _⟩
      have hv_par : ∀ (w : List (Fin N)),
          nonLastOutsideRBool M w = true ->
          (∀ s ∈ w, symAppearsInRulesBool N s.val core = true) ->
          evalFinWordVec N d mat v w z0 = evalFinParikh N (fun s => v s z0) w := by
        intro w; induction w with
        | nil => intros; rfl
        | cons s xs ihw =>
          cases xs with
          | nil =>
            intros
            have hz : ∀ m : Nat, natSumPrefix d (fun _ => (0 : Nat)) m = 0 := by
              intro m; induction m with
              | zero => rfl
              | succ m' ihm =>
                simp only [natSumPrefix]
                by_cases hm : m' < d <;> simp only [hm, dite_true, dite_false, ihm, Nat.add_zero]
            change v s z0 + natSumPrefix d (fun k => mat s z0 k * (0 : Nat)) d = v s z0 + 0
            simp only [Nat.mul_zero, hz d]
          | cons s2 tl =>
            intro hnl hall_in
            unfold nonLastOutsideRBool at hnl
            rcases bool_and_split hnl with ⟨hs_b, htl_nl⟩
            have hs_out := of_decide_eq_true hs_b
            have ih_xs := ihw htl_nl (fun x hx => hall_in x (List.Mem.tail s hx))
            have hs_row0 : mat s z0 z0 = 1 ∧ ∀ j : Fin d, j.val ≥ 1 -> mat s z0 j = 0 := by
              by_cases hlt8 : s.val < 8 * M
              · exact hLB s (by rcases hs_out with h1 | h2; exact Or.inl h1; exact Or.inr ⟨h2, hlt8⟩)
              · exact hT_lock s (by omega) (hall_in s (List.Mem.head _))
            have hsum0 : ∀ (f : Fin d -> Nat), (∀ k : Fin d, k.val ≥ 1 -> f k = 0) ->
                natSumPrefix d f d = f z0 := by
              intro f hz
              have hst : ∀ m : Nat, m ≤ d -> natSumPrefix d f m = (if 0 < m then f z0 else 0) := by
                intro m hm; induction m with
                | zero => rfl
                | succ m' ihm =>
                  have hm_lt : m' < d := hm
                  simp only [natSumPrefix, hm_lt, dite_true, ihm (Nat.le_of_lt hm)]
                  cases m' with
                  | zero => have h0f : (⟨0, hm_lt⟩ : Fin d) = z0 := rfl; rw [h0f]; simp
                  | succ m'' => rw [hz ⟨m'' + 1, hm_lt⟩ (by dsimp; omega), Nat.add_zero]; simp
              rw [hst d (Nat.le_refl d), ite_true_of_w10 (by omega : 0 < d)]
            change v s z0 + natSumPrefix d (fun j => mat s z0 j * evalFinWordVec N d mat v (s2 :: tl) j) d =
              v s z0 + evalFinParikh N (fun x => v x z0) (s2 :: tl)
            rw [hsum0 _ (fun j hj => by rw [hs_row0.2 j hj, Nat.zero_mul]), hs_row0.1, Nat.one_mul, ih_xs]
      have hboth : ∀ r ∈ core,
          evalFinWordVec N d mat v r.1 z0 = evalFinParikh N (fun s => v s z0) r.1 ∧
          evalFinWordVec N d mat v r.2 z0 = evalFinParikh N (fun s => v s z0) r.2 := by
        intro r hr
        rcases hr_sh r hr with ⟨hnl1, hnl2, _, _⟩
        exact ⟨hv_par r.1 hnl1 (fun s hs => hsym_in_rules N core r s hr (Or.inl hs)),
               hv_par r.2 hnl2 (fun s hs => hsym_in_rules N core r s hr (Or.inr hs))⟩
      have hpar_eq := hsyz_par (fun s => v s z0) (fun r hr => by
        rcases hboth r hr with ⟨e1, e2⟩
        have hv0 := (hweak_c r hr).2; omega)
      intro r hr
      rcases hboth r hr with ⟨e1, e2⟩
      rw [e1, e2, hpar_eq r hr]
    cases hc_eq : core with
    | nil => exact False.elim (hne hc_eq)
    | cons r0 rs =>
      rw [← hc_eq]
      have hm0 : r0 ∈ core := hc_eq ▸ List.Mem.head _
      have himp : ∀ (k : Nat) (cur : List (List (Fin N) × List (Fin N))),
          (∀ r ∈ core, r ∈ cur) -> ¬ GenOmegaNonUniformMixedZeroDiagTRMatTower M d hd k cur := by
        intro k; induction k with
        | zero =>
          intro cur hsub h0; rw [GenOmegaNonUniformMixedZeroDiagTRMatTower] at h0; subst h0
          exact List.not_mem_nil (hsub r0 hm0)
        | succ k' ih =>
          intro cur hsub hsucc
          rcases hsucc with rfl | ⟨rem, mat, v, hm1, hLB, hweak, hkeep, hrem⟩
          · exact List.not_mem_nil (hsub r0 hm0)
          · have heq := hno_strict mat v hm1 hLB
              (fun r hr => ⟨(hweak r (hsub r hr)).1, (hweak r (hsub r hr)).2 z0⟩)
            exact ih rem (fun r hr => hkeep r (hsub r hr)
              (by rw [heq r hr]; exact Nat.lt_irrefl _)) hrem
      exact fun k => himp k core (fun _ hr => hr)
  have hnl_c39 : ∀ r ∈ c39FastRulesW16,
      nonLastOutsideRBool 3 r.1 = true ∧ nonLastOutsideRBool 3 r.2 = true := by
    have hb : c39FastRulesW16.all (fun r => nonLastOutsideRBool 3 r.1 && nonLastOutsideRBool 3 r.2) = true :=
      by decide
    exact fun r hr => bool_and_split (List.all_eq_true.mp hb r hr)
  have hnl_c78 : ∀ r ∈ c78FastRulesW16,
      nonLastOutsideRBool 6 r.1 = true ∧ nonLastOutsideRBool 6 r.2 = true := by
    have hb : c78FastRulesW16.all (fun r => nonLastOutsideRBool 6 r.1 && nonLastOutsideRBool 6 r.2) = true :=
      by decide
    exact fun r hr => bool_and_split (List.all_eq_true.mp hb r hr)
  refine ⟨⟨hcnt39, hcnt78⟩, ⟨?_, ?_⟩,
          hmaster_lock 3 (by decide) c39FastRulesW16 cascadeRulesC39 hcert39 hlock39_w15,
          hmaster_lock 6 (by decide) c78FastRulesW16 cascadeRulesC78 hcert78 hlock78_w15,
          fun d hd k =>
            ⟨htr_imposs 3 (by decide) c39FastRulesW16 cascadeRulesC39 _ hne39 hcert39 hsyz39 hlock39_w15 d hd k,
             htr_imposs 6 (by decide) c78FastRulesW16 cascadeRulesC78 _ hne78 hcert78 hsyz78 hlock78_w15 d hd k⟩⟩
  · intro d mat1 mat2 v heq_out r hr i
    rcases hnl_c39 r hr with ⟨hn1, hn2⟩
    exact ⟨evalFinWordVec_congr_outside_R_w16 3 d mat1 mat2 v heq_out r.1 hn1 i,
           evalFinWordVec_congr_outside_R_w16 3 d mat1 mat2 v heq_out r.2 hn2 i⟩
  · intro d mat1 mat2 v heq_out r hr i
    rcases hnl_c78 r hr with ⟨hn1, hn2⟩
    exact ⟨evalFinWordVec_congr_outside_R_w16 6 d mat1 mat2 v heq_out r.1 hn1 i,
           evalFinWordVec_congr_outside_R_w16 6 d mat1 mat2 v heq_out r.2 hn2 i⟩

-- ----------------------------------------------------------------------------
-- Section 1B: Two Infinite 3-Parameter Coupled `.R`-Boundary + `.B`/`.T`-Top-Row
--             Mixed Zero-Diagonal `d = 2` Cones & Parameterized Farkas Syzygies
-- ----------------------------------------------------------------------------

/-- First 3-parameter coupled `.R`-boundary-growth + `.B`/`.T`-top-row `d = 2` cone on `c39`:
    `(M_6)_{0,0} = (M_9)_{0,0} = k` (`k ≥ 2`), `(M_20)_{0,1} = 6α`, `(M_22)_{0,1} = (M_23)_{0,1} = 5α`,
    `(M_37)_{0,1} = α`, `(M_28)_{1,0} = β`, `(M_31)_{1,0} = 7β`. -/
def bndParamMat2DC39 (k alpha beta : Nat) (s : Fin 42) (i j : Fin 2) : Nat :=
  match i.val, j.val with
  | 0, 0 => if s.val == 6 || s.val == 9 then k else 1
  | 0, 1 =>
    match s.val with
    | 20 => 6 * alpha | 22 => 5 * alpha | 23 => 5 * alpha | 37 => alpha | _ => 0
  | 1, 0 =>
    match s.val with
    | 28 => beta | 31 => 7 * beta | _ => 0
  | _, _ =>
    match s.val with
    | 6 => 5 | 7 => 3 | 14 => 3 | 17 => 1 | 23 => 1 | 28 => 5 | 31 => 1 | 32 => 1 | _ => 0

/-- Second 3-parameter coupled `.R`-boundary-growth + 6-symbol `.B_1`/`.T`-top-row `d = 2` cone on `c39`:
    `(M_20)_{0,1} = 0`, `(M_s)_{0,1} = α` across `{22, 23, 32, 37, 40, 41}`, `(M_6)_{0,0} = (M_9)_{0,0} = k`,
    `(M_28)_{1,0} = β`, `(M_31)_{1,0} = 7β` (escaping Wave 15's 2-rule `farkasMu1C39` by `+13`). -/
def coupledBTRTopRowMat2DC39 (k alpha beta : Nat) (s : Fin 42) (i j : Fin 2) : Nat :=
  match i.val, j.val with
  | 0, 0 => if s.val == 6 || s.val == 9 then k else 1
  | 0, 1 =>
    match s.val with
    | 22 => alpha | 23 => alpha | 32 => alpha | 37 => alpha | 40 => alpha | 41 => alpha | _ => 0
  | 1, 0 =>
    match s.val with
    | 28 => beta | 31 => 7 * beta | _ => 0
  | _, _ =>
    match s.val with
    | 6 => 5 | 7 => 3 | 14 => 3 | 17 => 1 | 23 => 1 | 28 => 5 | 31 => 1 | 32 => 1 | _ => 0

/-- Positive integral Farkas row-0 multipliers `μ_0(r) ≥ 1` for `coupledBTRTopRowMat2DC39`. -/
def farkasMu0CoupledC39 : List (Fin 42) -> Nat
  | a :: b :: _ =>
    match a.val, b.val with
    | 1, 14 => 1  | 1, 18 => 8  | 2, 13 => 9  | 2, 20 => 9
    | 4, 14 => 1  | 4, 18 => 1  | 5, 13 => 2  | 5, 20 => 1
    | 28, 6 => 2  | 28, 7 => 2  | 28, 8 => 2  | 28, 18 => 6
    | 29, 20 => 7 | 31, 6 => 5  | 31, 7 => 1  | 31, 8 => 1
    | 31, 14 => 7 | 31, 18 => 1 | 32, 13 => 9 | 32, 20 => 1
    | 33, 22 => 6 | 35, 16 => 3 | 35, 23 => 4 | 36, 22 => 10
    | 37, 9 => 1  | 37, 10 => 1 | 37, 11 => 1 | 37, 17 => 1
    | 37, 21 => 2 | 38, 16 => 12 | 38, 23 => 3 | 39, 22 => 3
    | 40, 9 => 1  | 40, 10 => 1 | 40, 11 => 1 | 40, 17 => 9
    | 40, 21 => 1 | 41, 16 => 3 | 41, 23 => 1 | _, _ => 1
  | _ => 1

/-- Non-negative 7-rule integral Farkas row-1 base multipliers `μ_1(r)` for `coupledBTRTopRowMat2DC39`. -/
def farkasMu1CoupledC39 : List (Fin 42) -> Nat
  | a :: b :: _ =>
    match a.val, b.val with
    | 33, 22 => 6 | 35, 16 => 3 | 35, 23 => 4 | 37, 9 => 1
    | 37, 17 => 5 | 38, 16 => 4 | 39, 22 => 1 | _, _ => 0
  | _ => 0

/-- Canonical mod-3 right-state projection `Fin 84 -> Fin 42` (`TwoSided(2 × 6) -> TwoSided(2 × 3)`). -/
def projSym84To42 (s : Fin 84) : Fin 42 :=
  ⟨(s.val / 12) * 6 + ((s.val % 12) / 6) * 3 + (s.val % 3), by have := s.isLt; omega⟩

/-- Lifted 3-parameter coupled `.R`-boundary-growth + 12-symbol `.B_1`/`.T`-top-row `d = 2` cone on `c78`
    (`22/78` strict matrix rules; direct mod-3 Farkas pullback fails by `+12`, locked by 14-rule asymmetric syzygy). -/
def coupledBTRTopRowMat2DC78 (k alpha beta : Nat) (s : Fin 84) (i j : Fin 2) : Nat :=
  coupledBTRTopRowMat2DC39 k alpha beta (projSym84To42 s) i j

/-- Positive integral Farkas row-0 multipliers `μ_0(r) ≥ 1` (`max = 63`) for `coupledBTRTopRowMat2DC78`. -/
def farkasMu0CoupledC78 : List (Fin 84) -> Nat
  | a :: b :: _ =>
    match a.val, b.val with
    | 2, 25 => 2   | 2, 28 => 2   | 5, 38 => 2   | 5, 41 => 63
    | 8, 25 => 2   | 8, 28 => 2   | 11, 38 => 2  | 55, 12 => 16
    | 55, 13 => 2  | 55, 14 => 2  | 55, 15 => 2  | 55, 16 => 2
    | 55, 17 => 2  | 55, 39 => 10 | 59, 38 => 32 | 59, 41 => 7
    | 61, 39 => 33 | 62, 25 => 7  | 64, 26 => 3  | 64, 29 => 39
    | 65, 41 => 8  | 68, 31 => 30 | 68, 34 => 2  | 69, 43 => 8
    | 69, 46 => 2  | 71, 44 => 6  | 74, 31 => 4  | 74, 34 => 5
    | 75, 43 => 34 | 77, 44 => 29 | 77, 47 => 44 | 79, 18 => 15
    | 79, 45 => 29 | 80, 31 => 36 | 80, 34 => 37 | 81, 43 => 16
    | 81, 46 => 14 | 82, 32 => 7  | 82, 35 => 8  | 83, 44 => 44
    | _, _ => 1
  | _ => 1

/-- Non-negative 14-rule asymmetric integral Farkas row-1 base multipliers `μ_1(r)` for `coupledBTRTopRowMat2DC78`. -/
def farkasMu1CoupledC78 : List (Fin 84) -> Nat
  | a :: b :: _ =>
    match a.val, b.val with
    | 68, 31 => 30 | 68, 34 => 2 | 69, 43 => 9  | 69, 46 => 1
    | 71, 44 => 7  | 73, 18 => 1 | 73, 45 => 8  | 74, 31 => 1
    | 74, 34 => 6  | 76, 32 => 1 | 79, 18 => 17 | 80, 31 => 37
    | 81, 43 => 1  | 81, 46 => 27 | _, _ => 0
  | _ => 0

private abbrev fin2Z0W16 : Fin 2 := ⟨0, by decide⟩
private abbrev fin2Z1W16 : Fin 2 := ⟨1, by decide⟩

private def nonLastNoBetaRProjBool (N : Nat) (proj : Fin N -> Fin 42) : List (Fin N) -> Bool
  | [] => true
  | [_] => true
  | s :: s2 :: tl =>
    let pv := (proj s).val
    decide (pv ≠ 6 ∧ pv ≠ 9 ∧ pv ≠ 28 ∧ pv ≠ 31) && nonLastNoBetaRProjBool N proj (s2 :: tl)

private def wordRow0NoBetaRProjBool (N : Nat) (proj : Fin N -> Fin 42) : List (Fin N) -> Bool
  | [] => true
  | [_] => true
  | s :: s2 :: tl =>
    let pv := (proj s).val
    decide (pv ≠ 6 ∧ pv ≠ 9) && nonLastNoBetaRProjBool N proj (s2 :: tl)

private theorem mat2_step_expandN_w16 (N : Nat) (M : Fin N -> Fin 2 -> Fin 2 -> Nat)
    (v : Fin N -> Fin 2 -> Nat) (s : Fin N) (rest : List (Fin N)) (i : Fin 2) :
    evalFinWordVec N 2 M v (s :: rest) i =
      v s i + M s i fin2Z0W16 * evalFinWordVec N 2 M v rest fin2Z0W16 +
        M s i fin2Z1W16 * evalFinWordVec N 2 M v rest fin2Z1W16 := by
  change v s i + ((0 + M s i fin2Z0W16 * evalFinWordVec N 2 M v rest fin2Z0W16) +
    M s i fin2Z1W16 * evalFinWordVec N 2 M v rest fin2Z1W16) = _
  omega

private theorem coupledMatProj_affine_in_alpha_w16 (N : Nat) (proj : Fin N -> Fin 42)
    (k alpha beta : Nat) (v : Fin N -> Fin 2 -> Nat) :
    let matFn := fun k' a' b' (s : Fin N) => coupledBTRTopRowMat2DC39 k' a' b' (proj s)
    (∀ w : List (Fin N), nonLastNoBetaRProjBool N proj w = true ->
      evalFinWordVec N 2 (matFn k alpha beta) v w fin2Z1W16 =
        evalFinWordVec N 2 (matFn 1 0 0) v w fin2Z1W16) ∧
    (∀ w : List (Fin N), wordRow0NoBetaRProjBool N proj w = true ->
      evalFinWordVec N 2 (matFn 1 0 0) v w fin2Z0W16 ≤
        evalFinWordVec N 2 (matFn 1 1 0) v w fin2Z0W16 ∧
      evalFinWordVec N 2 (matFn k alpha beta) v w fin2Z0W16 =
        evalFinWordVec N 2 (matFn 1 0 0) v w fin2Z0W16 +
          alpha * (evalFinWordVec N 2 (matFn 1 1 0) v w fin2Z0W16 -
            evalFinWordVec N 2 (matFn 1 0 0) v w fin2Z0W16)) := by
  dsimp only
  let matFn := fun k' a' b' (s : Fin N) => coupledBTRTopRowMat2DC39 k' a' b' (proj s)
  have hv_single : ∀ (M : Fin N -> Fin 2 -> Fin 2 -> Nat) (s : Fin N) (i : Fin 2),
      evalFinWordVec N 2 M v [s] i = v s i := by
    intro M s i
    rw [mat2_step_expandN_w16 N M v s [] i]
    change v s i + M s i fin2Z0W16 * 0 + M s i fin2Z1W16 * 0 = v s i
    omega
  have hz1_ind : ∀ w : List (Fin N), nonLastNoBetaRProjBool N proj w = true ->
      ∀ (k' a' b' : Nat),
        evalFinWordVec N 2 (matFn k' a' b') v w fin2Z1W16 =
          evalFinWordVec N 2 (matFn 1 0 0) v w fin2Z1W16 := by
    intro w; induction w with
    | nil => intros; rfl
    | cons s xs ih =>
      cases xs with
      | nil => intros _ k' a' b'; rw [hv_single, hv_single]
      | cons s2 tl =>
        intro hb k' a' b'
        unfold nonLastNoBetaRProjBool at hb
        rcases bool_and_split hb with ⟨hs_b, htl_b⟩
        rcases of_decide_eq_true hs_b with ⟨_, _, hn28, hn31⟩
        have hc0 : matFn k' a' b' s fin2Z1W16 fin2Z0W16 = 0 := by
          change (match (proj s).val with | 28 => b' | 31 => 7 * b' | _ => 0) = 0
          split <;> omega
        have hc0_base : matFn 1 0 0 s fin2Z1W16 fin2Z0W16 = 0 := by
          change (match (proj s).val with | 28 => 0 | 31 => 7 * 0 | _ => 0) = 0
          split <;> omega
        have hd_eq : matFn k' a' b' s fin2Z1W16 fin2Z1W16 =
            matFn 1 0 0 s fin2Z1W16 fin2Z1W16 := rfl
        rw [mat2_step_expandN_w16 N _ v s (s2 :: tl) fin2Z1W16,
            mat2_step_expandN_w16 N _ v s (s2 :: tl) fin2Z1W16,
            hc0, hc0_base, Nat.zero_mul, Nat.zero_mul, hd_eq,
            ih htl_b k' a' b']
  refine ⟨fun w hb => hz1_ind w hb k alpha beta, ?_⟩
  have hz0_tail : ∀ w : List (Fin N), nonLastNoBetaRProjBool N proj w = true ->
      evalFinWordVec N 2 (matFn 1 0 0) v w fin2Z0W16 ≤
        evalFinWordVec N 2 (matFn 1 1 0) v w fin2Z0W16 ∧
      evalFinWordVec N 2 (matFn k alpha beta) v w fin2Z0W16 =
        evalFinWordVec N 2 (matFn 1 0 0) v w fin2Z0W16 +
          alpha * (evalFinWordVec N 2 (matFn 1 1 0) v w fin2Z0W16 -
            evalFinWordVec N 2 (matFn 1 0 0) v w fin2Z0W16) := by
    intro w; induction w with
    | nil => intros; exact ⟨Nat.le_refl 0, by simp [evalFinWordVec]⟩
    | cons s xs ih =>
      cases xs with
      | nil => intros; simp [hv_single]
      | cons s2 tl =>
        intro hb
        unfold nonLastNoBetaRProjBool at hb
        rcases bool_and_split hb with ⟨hs_b, htl_b⟩
        rcases of_decide_eq_true hs_b with ⟨hn6, hn9, _, _⟩
        rcases ih htl_b with ⟨hle_tl, heq_tl⟩
        have ha00 : ∀ k' a' b' : Nat, matFn k' a' b' s fin2Z0W16 fin2Z0W16 = 1 := by
          intro k' a' b'
          dsimp [matFn]; unfold coupledBTRTopRowMat2DC39
          rw [beq_false_of_ne hn6, beq_false_of_ne hn9]; rfl
        have hb01 : matFn k alpha beta s fin2Z0W16 fin2Z1W16 =
            alpha * matFn 1 1 0 s fin2Z0W16 fin2Z1W16 ∧
            matFn 1 0 0 s fin2Z0W16 fin2Z1W16 = 0 := by
          refine ⟨?_, ?_⟩
          · change (match (proj s).val with
              | 22 => alpha | 23 => alpha | 32 => alpha | 37 => alpha | 40 => alpha | 41 => alpha | _ => 0) =
              alpha * (match (proj s).val with
              | 22 => 1 | 23 => 1 | 32 => 1 | 37 => 1 | 40 => 1 | 41 => 1 | _ => 0)
            split <;> omega
          · change (match (proj s).val with
              | 22 => 0 | 23 => 0 | 32 => 0 | 37 => 0 | 40 => 0 | 41 => 0 | _ => 0) = 0
            split <;> rfl
        rw [mat2_step_expandN_w16 N (matFn 1 0 0) v s (s2 :: tl) fin2Z0W16,
            mat2_step_expandN_w16 N (matFn 1 1 0) v s (s2 :: tl) fin2Z0W16,
            mat2_step_expandN_w16 N (matFn k alpha beta) v s (s2 :: tl) fin2Z0W16,
            ha00 1 0 0, ha00 1 1 0, ha00 k alpha beta,
            Nat.one_mul, Nat.one_mul, Nat.one_mul,
            hb01.2, Nat.zero_mul, Nat.add_zero,
            hb01.1, hz1_ind (s2 :: tl) htl_b k alpha beta,
            hz1_ind (s2 :: tl) htl_b 1 1 0, heq_tl]
        refine ⟨by omega, ?_⟩
        have hsub : (v s fin2Z0W16 + evalFinWordVec N 2 (matFn 1 1 0) v (s2 :: tl) fin2Z0W16 +
            matFn 1 1 0 s fin2Z0W16 fin2Z1W16 *
              evalFinWordVec N 2 (matFn 1 0 0) v (s2 :: tl) fin2Z1W16) -
          (v s fin2Z0W16 + evalFinWordVec N 2 (matFn 1 0 0) v (s2 :: tl) fin2Z0W16) =
          (evalFinWordVec N 2 (matFn 1 1 0) v (s2 :: tl) fin2Z0W16 -
            evalFinWordVec N 2 (matFn 1 0 0) v (s2 :: tl) fin2Z0W16) +
          matFn 1 1 0 s fin2Z0W16 fin2Z1W16 *
            evalFinWordVec N 2 (matFn 1 0 0) v (s2 :: tl) fin2Z1W16 := by omega
        rw [hsub, Nat.mul_add alpha, Nat.mul_assoc]
        omega
  intro w hbw
  cases w with
  | nil => exact ⟨Nat.le_refl 0, by simp [evalFinWordVec]⟩
  | cons s xs =>
    cases xs with
    | nil => simp [hv_single]
    | cons s2 tl =>
      unfold wordRow0NoBetaRProjBool at hbw
      rcases bool_and_split hbw with ⟨hs_b, htl_b⟩
      rcases of_decide_eq_true hs_b with ⟨hn6, hn9⟩
      rcases hz0_tail (s2 :: tl) htl_b with ⟨hle_tl, heq_tl⟩
      have ha00 : ∀ k' a' b' : Nat, matFn k' a' b' s fin2Z0W16 fin2Z0W16 = 1 := by
        intro k' a' b'
        dsimp [matFn]; unfold coupledBTRTopRowMat2DC39
        rw [beq_false_of_ne hn6, beq_false_of_ne hn9]; rfl
      have hb01 : matFn k alpha beta s fin2Z0W16 fin2Z1W16 =
          alpha * matFn 1 1 0 s fin2Z0W16 fin2Z1W16 ∧
          matFn 1 0 0 s fin2Z0W16 fin2Z1W16 = 0 := by
        refine ⟨?_, ?_⟩
        · change (match (proj s).val with
            | 22 => alpha | 23 => alpha | 32 => alpha | 37 => alpha | 40 => alpha | 41 => alpha | _ => 0) =
            alpha * (match (proj s).val with
            | 22 => 1 | 23 => 1 | 32 => 1 | 37 => 1 | 40 => 1 | 41 => 1 | _ => 0)
          split <;> omega
        · change (match (proj s).val with
            | 22 => 0 | 23 => 0 | 32 => 0 | 37 => 0 | 40 => 0 | 41 => 0 | _ => 0) = 0
          split <;> rfl
      rw [mat2_step_expandN_w16 N (matFn 1 0 0) v s (s2 :: tl) fin2Z0W16,
          mat2_step_expandN_w16 N (matFn 1 1 0) v s (s2 :: tl) fin2Z0W16,
          mat2_step_expandN_w16 N (matFn k alpha beta) v s (s2 :: tl) fin2Z0W16,
          ha00 1 0 0, ha00 1 1 0, ha00 k alpha beta,
          Nat.one_mul, Nat.one_mul, Nat.one_mul,
          hb01.2, Nat.zero_mul, Nat.add_zero,
          hb01.1, hz1_ind (s2 :: tl) htl_b k alpha beta,
          hz1_ind (s2 :: tl) htl_b 1 1 0, heq_tl]
      refine ⟨by omega, ?_⟩
      have hsub : (v s fin2Z0W16 + evalFinWordVec N 2 (matFn 1 1 0) v (s2 :: tl) fin2Z0W16 +
          matFn 1 1 0 s fin2Z0W16 fin2Z1W16 *
            evalFinWordVec N 2 (matFn 1 0 0) v (s2 :: tl) fin2Z1W16) -
        (v s fin2Z0W16 + evalFinWordVec N 2 (matFn 1 0 0) v (s2 :: tl) fin2Z0W16) =
        (evalFinWordVec N 2 (matFn 1 1 0) v (s2 :: tl) fin2Z0W16 -
          evalFinWordVec N 2 (matFn 1 0 0) v (s2 :: tl) fin2Z0W16) +
        matFn 1 1 0 s fin2Z0W16 fin2Z1W16 *
          evalFinWordVec N 2 (matFn 1 0 0) v (s2 :: tl) fin2Z1W16 := by omega
      rw [hsub, Nat.mul_add alpha, Nat.mul_assoc]
      omega

private def farkasCoupledVecLhsN (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 : List (Fin N) -> Nat) (k alpha beta : Nat) (v : Fin N -> Fin 2 -> Nat) :
    List (List (Fin N) × List (Fin N)) -> Nat
  | [] => 0
  | (l, _) :: rs =>
    let M := fun s => coupledBTRTopRowMat2DC39 k alpha beta (proj s)
    mu0 l * evalFinWordVec N 2 M v l fin2Z0W16 +
      (alpha * mu1 l) * evalFinWordVec N 2 M v l fin2Z1W16 +
      farkasCoupledVecLhsN N proj mu0 mu1 k alpha beta v rs

private def farkasCoupledVecRhsN (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 : List (Fin N) -> Nat) (k alpha beta : Nat) (v : Fin N -> Fin 2 -> Nat) :
    List (List (Fin N) × List (Fin N)) -> Nat
  | [] => 0
  | (l, r) :: rs =>
    let M := fun s => coupledBTRTopRowMat2DC39 k alpha beta (proj s)
    mu0 l * evalFinWordVec N 2 M v r fin2Z0W16 +
      (alpha * mu1 l) * evalFinWordVec N 2 M v r fin2Z1W16 +
      farkasCoupledVecRhsN N proj mu0 mu1 k alpha beta v rs

private def evalWordVec2DFastN (N : Nat) (M : Fin N -> Fin 2 -> Fin 2 -> Nat)
    (v : Fin N -> Fin 2 -> Nat) : List (Fin N) -> Nat × Nat
  | [] => (0, 0)
  | s :: u =>
    let p := evalWordVec2DFastN N M v u
    (v s fin2Z0W16 + M s fin2Z0W16 fin2Z0W16 * p.1 + M s fin2Z0W16 fin2Z1W16 * p.2,
     v s fin2Z1W16 + M s fin2Z1W16 fin2Z0W16 * p.1 + M s fin2Z1W16 fin2Z1W16 * p.2)

private def farkasCoupledFastPairN (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 : List (Fin N) -> Nat) (k alpha beta : Nat) (v : Fin N -> Fin 2 -> Nat) :
    List (List (Fin N) × List (Fin N)) -> Nat × Nat
  | [] => (0, 0)
  | (l, r) :: rs =>
    let M := fun s => coupledBTRTopRowMat2DC39 k alpha beta (proj s)
    let pl := evalWordVec2DFastN N M v l
    let pr := evalWordVec2DFastN N M v r
    let ptl := farkasCoupledFastPairN N proj mu0 mu1 k alpha beta v rs
    (mu0 l * pl.1 + (alpha * mu1 l) * pl.2 + ptl.1,
     mu0 l * pr.1 + (alpha * mu1 l) * pr.2 + ptl.2)

private theorem farkasCoupledFastPairN_eq (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 : List (Fin N) -> Nat) (k alpha beta : Nat) (v : Fin N -> Fin 2 -> Nat) :
    ∀ rs : List (List (Fin N) × List (Fin N)),
      farkasCoupledFastPairN N proj mu0 mu1 k alpha beta v rs =
        (farkasCoupledVecLhsN N proj mu0 mu1 k alpha beta v rs,
         farkasCoupledVecRhsN N proj mu0 mu1 k alpha beta v rs) := by
  let M := fun s => coupledBTRTopRowMat2DC39 k alpha beta (proj s)
  have hv_eq : ∀ w : List (Fin N),
      evalWordVec2DFastN N M v w =
        (evalFinWordVec N 2 M v w fin2Z0W16, evalFinWordVec N 2 M v w fin2Z1W16) := by
    intro w; induction w with
    | nil => rfl
    | cons s u ih =>
      simp only [evalWordVec2DFastN, ih, mat2_step_expandN_w16 N M v s u]
  dsimp only [M] at hv_eq
  intro rs; induction rs with
  | nil => rfl
  | cons r0 rtl ih =>
    rcases r0 with ⟨l, r⟩
    simp only [farkasCoupledFastPairN, farkasCoupledVecLhsN, farkasCoupledVecRhsN, hv_eq, ih]

private def checkCoupledFarkasCoordNBool (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 : List (Fin N) -> Nat) (j0 : Fin 2)
    (rules : List (List (Fin N) × List (Fin N))) : Bool :=
  let rec loop : Nat -> Bool
    | 0 => true
    | m + 1 =>
      if h : m < N then
        let p0 := farkasCoupledFastPairN N proj mu0 mu1 1 0 0 (basisVec2D N ⟨m, h⟩ j0) rules
        let p1 := farkasCoupledFastPairN N proj mu0 mu1 1 1 0 (basisVec2D N ⟨m, h⟩ j0) rules
        decide (p0.1 ≤ p0.2 ∧ p1.1 - p0.1 ≤ p1.2 - p0.2) && loop m
      else false
  loop N

private def checkWordShapeCoupledNBool (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 : List (Fin N) -> Nat) (rs : List (List (Fin N) × List (Fin N))) : Bool :=
  rs.all (fun r =>
    wordRow0NoBetaRProjBool N proj r.1 && wordRow0NoBetaRProjBool N proj r.2 &&
    (decide (mu1 r.1 = 0) ||
      (nonLastNoBetaRProjBool N proj r.1 && nonLastNoBetaRProjBool N proj r.2)) &&
    decide (mu0 r.1 ≥ 1))

private def w15FarkasFastDiffOnCoupled (v : Fin 42 -> Fin 2 -> Nat) :
    List (List (Fin 42) × List (Fin 42)) -> Nat × Nat
  | [] => (0, 0)
  | (l, r) :: rs =>
    let pl := evalWordVec2DFastN 42 (coupledBTRTopRowMat2DC39 2 1 1) v l
    let pr := evalWordVec2DFastN 42 (coupledBTRTopRowMat2DC39 2 1 1) v r
    let ptl := w15FarkasFastDiffOnCoupled v rs
    (farkasMu0C39 l * pl.1 + farkasMu1C39 l * pl.2 + ptl.1,
     farkasMu0C39 l * pr.1 + farkasMu1C39 l * pr.2 + ptl.2)

private def w15FarkasLhsOnCoupled (v : Fin 42 -> Fin 2 -> Nat) :
    List (List (Fin 42) × List (Fin 42)) -> Nat
  | [] => 0
  | (l, _) :: rs =>
    farkasMu0C39 l * evalFinWordVec 42 2 (coupledBTRTopRowMat2DC39 2 1 1) v l fin2Z0W16 +
      farkasMu1C39 l * evalFinWordVec 42 2 (coupledBTRTopRowMat2DC39 2 1 1) v l fin2Z1W16 +
      w15FarkasLhsOnCoupled v rs

private def w15FarkasRhsOnCoupled (v : Fin 42 -> Fin 2 -> Nat) :
    List (List (Fin 42) × List (Fin 42)) -> Nat
  | [] => 0
  | (l, r) :: rs =>
    farkasMu0C39 l * evalFinWordVec 42 2 (coupledBTRTopRowMat2DC39 2 1 1) v r fin2Z0W16 +
      farkasMu1C39 l * evalFinWordVec 42 2 (coupledBTRTopRowMat2DC39 2 1 1) v r fin2Z1W16 +
      w15FarkasRhsOnCoupled v rs

private theorem w15FarkasFastDiff_eq (v : Fin 42 -> Fin 2 -> Nat) :
    ∀ rs : List (List (Fin 42) × List (Fin 42)),
      w15FarkasFastDiffOnCoupled v rs = (w15FarkasLhsOnCoupled v rs, w15FarkasRhsOnCoupled v rs) := by
  have hv_eq : ∀ w : List (Fin 42),
      evalWordVec2DFastN 42 (coupledBTRTopRowMat2DC39 2 1 1) v w =
        (evalFinWordVec 42 2 (coupledBTRTopRowMat2DC39 2 1 1) v w fin2Z0W16,
         evalFinWordVec 42 2 (coupledBTRTopRowMat2DC39 2 1 1) v w fin2Z1W16) := by
    intro w; induction w with
    | nil => rfl
    | cons s u ih =>
      simp only [evalWordVec2DFastN, ih,
                 mat2_step_expandN_w16 42 (coupledBTRTopRowMat2DC39 2 1 1) v s u]
  intro rs; induction rs with
  | nil => rfl
  | cons r0 rtl ih =>
    rcases r0 with ⟨l, r⟩
    simp only [w15FarkasFastDiffOnCoupled, w15FarkasLhsOnCoupled, w15FarkasRhsOnCoupled, hv_eq, ih]

private theorem coupled_c39_c78_shape_and_witness_certs :
    checkWordShapeCoupledNBool 42 id farkasMu0CoupledC39 farkasMu1CoupledC39 c39FastRulesW16 = true ∧
    checkWordShapeCoupledNBool 84 projSym84To42 farkasMu0CoupledC78 farkasMu1CoupledC78 c78FastRulesW16 = true ∧
    c78FastRulesW16.all (fun r =>
      c39FastRulesW16.any (· == (r.1.map projSym84To42, r.2.map projSym84To42))) = true ∧
    countStrictMat2DRules 42 (bndParamMat2DC39 2 1 1) c39FastRulesW16 = 20 ∧
    countStrictMat2DRules 42 (coupledBTRTopRowMat2DC39 2 1 1) c39FastRulesW16 = 11 ∧
    countStrictMat2DRules 84 (coupledBTRTopRowMat2DC78 2 1 1) c78FastRulesW16 = 22 ∧
    (let p := w15FarkasFastDiffOnCoupled (basisVec2D 42 ⟨17, by decide⟩ fin2Z1W16) c39FastRulesW16
     p.1 - p.2 = 13) := by decide

private theorem coupled_c39_farkas_b0_cert :
    checkCoupledFarkasCoordNBool 42 id farkasMu0CoupledC39 farkasMu1CoupledC39 fin2Z0W16 c39FastRulesW16 = true := by
  decide

private theorem coupled_c39_farkas_b1_cert :
    checkCoupledFarkasCoordNBool 42 id farkasMu0CoupledC39 farkasMu1CoupledC39 fin2Z1W16 c39FastRulesW16 = true := by
  decide

set_option maxRecDepth 65536 in
private theorem coupled_c78_farkas_b0_cert :
    checkCoupledFarkasCoordNBool 84 projSym84To42 farkasMu0CoupledC78 farkasMu1CoupledC78 fin2Z0W16 c78FastRulesW16 = true := by
  decide

set_option maxRecDepth 65536 in
private theorem coupled_c78_farkas_b1_cert :
    checkCoupledFarkasCoordNBool 84 projSym84To42 farkasMu0CoupledC78 farkasMu1CoupledC78 fin2Z1W16 c78FastRulesW16 = true := by
  decide

private def no69NonLastBoolW16 : List (Fin 42) -> Bool
  | [] => true
  | [_] => true
  | s :: s2 :: tl => decide (s.val ≠ 6 ∧ s.val ≠ 9) && no69NonLastBoolW16 (s2 :: tl)

private def endIs69BoolW16 : List (Fin 42) -> Bool
  | [] => false
  | [s] => s.val == 6 || s.val == 9
  | _ :: s2 :: tl => endIs69BoolW16 (s2 :: tl)

private def noAlphaSymBoolW16 : List (Fin 42) -> Bool
  | [] => true
  | s :: tl =>
    decide (s.val ≠ 22 ∧ s.val ≠ 23 ∧ s.val ≠ 32 ∧ s.val ≠ 37 ∧ s.val ≠ 40 ∧ s.val ≠ 41) &&
      noAlphaSymBoolW16 tl

private def noBetaSymBoolW16 : List (Fin 42) -> Bool
  | [] => true
  | s :: tl => decide (s.val ≠ 28 ∧ s.val ≠ 31) && noBetaSymBoolW16 tl

private theorem weak_mat_orientation_3param_cones_w16 (k alpha beta : Nat)
    (_hk : k ≥ 1) (ha1 : alpha ≥ 1) (hb1 : beta ≥ 1) :
    (∀ r ∈ c39FastRulesW16, ∀ i j : Fin 2,
      evalFinWordMat 42 2 (bndParamMat2DC39 k alpha beta) r.1 i j ≥
        evalFinWordMat 42 2 (bndParamMat2DC39 k alpha beta) r.2 i j) ∧
    (∀ r ∈ c39FastRulesW16, ∀ i j : Fin 2,
      evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 k alpha beta) r.1 i j ≥
        evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 k alpha beta) r.2 i j) := by
  have hm_step : ∀ (fn : Fin 42 -> Fin 2 -> Fin 2 -> Nat) (s : Fin 42) (tl : List (Fin 42)) (i j : Fin 2),
      evalFinWordMat 42 2 fn (s :: tl) i j =
        fn s i fin2Z0W16 * evalFinWordMat 42 2 fn tl fin2Z0W16 j +
        fn s i fin2Z1W16 * evalFinWordMat 42 2 fn tl fin2Z1W16 j := by
    intro fn s tl i j
    change (0 + fn s i fin2Z0W16 * evalFinWordMat 42 2 fn tl fin2Z0W16 j) +
      fn s i fin2Z1W16 * evalFinWordMat 42 2 fn tl fin2Z1W16 j = _; omega
  have hm_single : ∀ (fn : Fin 42 -> Fin 2 -> Fin 2 -> Nat) (s : Fin 42) (i j : Fin 2),
      evalFinWordMat 42 2 fn [s] i j = fn s i j := by
    intro fn s i j
    rw [hm_step fn s [] i j]
    rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1) with hj0 | hj1
    · rw [show j = fin2Z0W16 from Fin.ext hj0]
      change fn s i fin2Z0W16 * 1 + fn s i fin2Z1W16 * 0 = fn s i fin2Z0W16; omega
    · rw [show j = fin2Z1W16 from Fin.ext hj1]
      change fn s i fin2Z0W16 * 0 + fn s i fin2Z1W16 * 1 = fn s i fin2Z1W16; omega
  -- Right-end `{6, 9}` scaling law: for ANY `fn : Nat -> Fin 42 -> Fin 2 -> Fin 2 -> Nat` with
  -- `fn kv s = fn 1 s` outside `{6, 9}` and `fn kv s = [[kv, 0], [0, d_s]]` on `{6, 9}`,
  -- on any non-empty `w` with `no69NonLastBoolW16 w = true`:
  --   `evalFinWordMat (fn k) w i j = evalFinWordMat (fn 1) w i j * (if endIs69BoolW16 w && j == 0 then k else 1)`.
  have hk_scale : ∀ (fn : Nat -> Fin 42 -> Fin 2 -> Fin 2 -> Nat),
      (∀ s : Fin 42, s.val ≠ 6 -> s.val ≠ 9 -> ∀ p q : Fin 2, fn k s p q = fn 1 s p q) ->
      (∀ s : Fin 42, (s.val == 6 || s.val == 9) = true ->
        fn k s fin2Z0W16 fin2Z0W16 = k ∧ fn 1 s fin2Z0W16 fin2Z0W16 = 1 ∧
        fn k s fin2Z0W16 fin2Z1W16 = 0 ∧ fn 1 s fin2Z0W16 fin2Z1W16 = 0 ∧
        fn k s fin2Z1W16 fin2Z0W16 = 0 ∧ fn 1 s fin2Z1W16 fin2Z0W16 = 0 ∧
        fn k s fin2Z1W16 fin2Z1W16 = fn 1 s fin2Z1W16 fin2Z1W16) ->
      ∀ (w : List (Fin 42)), w ≠ [] -> no69NonLastBoolW16 w = true ->
        ∀ i j : Fin 2,
          evalFinWordMat 42 2 (fn k) w i j =
            evalFinWordMat 42 2 (fn 1) w i j *
              (if endIs69BoolW16 w && (j.val == 0) then k else 1) := by
    intro fn hout h69 w; induction w with
    | nil => intro hne; exact False.elim (hne rfl)
    | cons s xs ih =>
      cases xs with
      | nil =>
        intros _ _ i j
        rw [hm_single, hm_single]
        unfold endIs69BoolW16
        by_cases hs69 : (s.val == 6 || s.val == 9) = true
        · rcases h69 s hs69 with ⟨hk00, h100, hk01, h101, hk10, h110, hd11⟩
          rcases (by have := i.isLt; omega : i.val = 0 ∨ i.val = 1) with hi | hi <;>
          rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1) with hj | hj
          · have e1 : i = fin2Z0W16 := Fin.ext hi
            have e2 : j = fin2Z0W16 := Fin.ext hj
            rw [e1, e2, hk00, h100]
            simp [hs69]
          · have e1 : i = fin2Z0W16 := Fin.ext hi
            have e2 : j = fin2Z1W16 := Fin.ext hj
            rw [e1, e2, hk01, h101]
            simp [hs69]
          · have e1 : i = fin2Z1W16 := Fin.ext hi
            have e2 : j = fin2Z0W16 := Fin.ext hj
            rw [e1, e2, hk10, h110]
            simp [hs69]
          · have e1 : i = fin2Z1W16 := Fin.ext hi
            have e2 : j = fin2Z1W16 := Fin.ext hj
            rw [e1, e2, hd11]
            simp [hs69]
        · have hn6 : s.val ≠ 6 := fun h => hs69 (by simp [h])
          have hn9 : s.val ≠ 9 := fun h => hs69 (by simp [h])
          simp [hs69, hout s hn6 hn9 i j]
      | cons s2 tl =>
        intro _ hnl i j
        unfold no69NonLastBoolW16 at hnl
        rcases bool_and_split hnl with ⟨hs_b, htl_nl⟩
        rcases of_decide_eq_true hs_b with ⟨hn6, hn9⟩
        have he_end : endIs69BoolW16 (s :: s2 :: tl) = endIs69BoolW16 (s2 :: tl) := rfl
        rw [he_end, hm_step (fn k) s (s2 :: tl) i j, hm_step (fn 1) s (s2 :: tl) i j,
            hout s hn6 hn9 i fin2Z0W16, hout s hn6 hn9 i fin2Z1W16,
            ih (by simp) htl_nl fin2Z0W16 j, ih (by simp) htl_nl fin2Z1W16 j,
            Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc]
  have hr_end69 : c39FastRulesW16.all (fun r =>
      decide (r.1 ≠ [] ∧ r.2 ≠ []) &&
      no69NonLastBoolW16 r.1 && no69NonLastBoolW16 r.2 &&
      decide (endIs69BoolW16 r.1 = endIs69BoolW16 r.2)) = true := by decide
  have hlift_from_k1 : ∀ (fn : Nat -> Fin 42 -> Fin 2 -> Fin 2 -> Nat),
      (∀ s : Fin 42, s.val ≠ 6 -> s.val ≠ 9 -> ∀ p q : Fin 2, fn k s p q = fn 1 s p q) ->
      (∀ s : Fin 42, (s.val == 6 || s.val == 9) = true ->
        fn k s fin2Z0W16 fin2Z0W16 = k ∧ fn 1 s fin2Z0W16 fin2Z0W16 = 1 ∧
        fn k s fin2Z0W16 fin2Z1W16 = 0 ∧ fn 1 s fin2Z0W16 fin2Z1W16 = 0 ∧
        fn k s fin2Z1W16 fin2Z0W16 = 0 ∧ fn 1 s fin2Z1W16 fin2Z0W16 = 0 ∧
        fn k s fin2Z1W16 fin2Z1W16 = fn 1 s fin2Z1W16 fin2Z1W16) ->
      (∀ r ∈ c39FastRulesW16, ∀ i j : Fin 2,
        evalFinWordMat 42 2 (fn 1) r.1 i j ≥ evalFinWordMat 42 2 (fn 1) r.2 i j) ->
      ∀ r ∈ c39FastRulesW16, ∀ i j : Fin 2,
        evalFinWordMat 42 2 (fn k) r.1 i j ≥ evalFinWordMat 42 2 (fn k) r.2 i j := by
    intro fn hout h69 hw1 r hr i j
    rcases bool_and_split (List.all_eq_true.mp hr_end69 r hr) with ⟨hb1, hend_b⟩
    rcases bool_and_split hb1 with ⟨hb2, hnl2⟩
    rcases bool_and_split hb2 with ⟨hne_b, hnl1⟩
    rcases of_decide_eq_true hne_b with ⟨hne1, hne2⟩
    have hend := of_decide_eq_true hend_b
    rw [hk_scale fn hout h69 r.1 hne1 hnl1 i j,
        hk_scale fn hout h69 r.2 hne2 hnl2 i j, hend]
    exact Nat.mul_le_mul_right _ (hw1 r hr i j)
  -- 1. `bndParamMat2DC39 1 alpha beta = paramMat2DC39 alpha beta`, proved in Wave 15:
  have hbnd_k1_eq : bndParamMat2DC39 1 alpha beta = paramMat2DC39 alpha beta := by
    funext s p q
    unfold bndParamMat2DC39 paramMat2DC39
    rcases (by have := p.isLt; omega : p.val = 0 ∨ p.val = 1) with hp | hp <;>
    rcases (by have := q.isLt; omega : q.val = 0 ∨ q.val = 1) with hq | hq <;>
    simp only [hp, hq]
    · by_cases h : (s.val == 6 || s.val == 9) = true <;> simp [h]
    · rfl
    · rfl
    · rfl
  have hbnd_w1 : ∀ r ∈ c39FastRulesW16, ∀ i j : Fin 2,
      evalFinWordMat 42 2 (bndParamMat2DC39 1 alpha beta) r.1 i j ≥
        evalFinWordMat 42 2 (bndParamMat2DC39 1 alpha beta) r.2 i j := by
    rw [hbnd_k1_eq]
    have hw15 := (param_mixed_zerodiag_t_coupled_d2_farkas_lock.2 alpha beta ha1 hb1).1
    rwa [c39_eq_fastRules_w16] at hw15
  have hbnd_wk : ∀ r ∈ c39FastRulesW16, ∀ i j : Fin 2,
      evalFinWordMat 42 2 (bndParamMat2DC39 k alpha beta) r.1 i j ≥
        evalFinWordMat 42 2 (bndParamMat2DC39 k alpha beta) r.2 i j := by
    apply hlift_from_k1 (fun kv => bndParamMat2DC39 kv alpha beta)
    · intro s hn6 hn9 p q
      unfold bndParamMat2DC39
      rcases (by have := p.isLt; omega : p.val = 0 ∨ p.val = 1) with hp | hp <;>
      rcases (by have := q.isLt; omega : q.val = 0 ∨ q.val = 1) with hq | hq <;>
      simp only [hp, hq, beq_false_of_ne hn6, beq_false_of_ne hn9]; all_goals rfl
    · intro s hs69
      have hs_v : s.val = 6 ∨ s.val = 9 := by
        rcases Bool.or_eq_true_iff.mp hs69 with h6 | h9
        · exact Or.inl (Nat.eq_of_beq_eq_true h6)
        · exact Or.inr (Nat.eq_of_beq_eq_true h9)
      rcases hs_v with hs | hs <;> simp [bndParamMat2DC39, hs]
    · exact hbnd_w1
  -- 2. `coupledBTRTopRowMat2DC39 1 alpha beta`: every word in `c39FastRulesW16` avoids `{28, 31}`
  --    OR avoids `{22, 23, 32, 37, 40, 41}`, so `M(1, alpha, beta)(w)` is purely affine in `(alpha, beta)`!
  have hcongr_noB : ∀ (a' b' : Nat) (u : List (Fin 42)), noBetaSymBoolW16 u = true ->
      ∀ p q : Fin 2,
        evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 1 a' b') u p q =
          evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 1 a' 0) u p q := by
    intro a' b' u; induction u with
    | nil => intros; rfl
    | cons x xs ihu =>
      intro hbu p q; unfold noBetaSymBoolW16 at hbu
      rcases bool_and_split hbu with ⟨hx_b, hxs_b⟩
      rcases of_decide_eq_true hx_b with ⟨hx28, hx31⟩
      have hmat_eq : ∀ c : Fin 2,
          coupledBTRTopRowMat2DC39 1 a' b' x p c = coupledBTRTopRowMat2DC39 1 a' 0 x p c := by
        intro c
        rcases (by have := p.isLt; omega : p.val = 0 ∨ p.val = 1) with hp | hp <;>
        rcases (by have := c.isLt; omega : c.val = 0 ∨ c.val = 1) with hc0 | hc0
        · unfold coupledBTRTopRowMat2DC39; simp [hp, hc0]
        · unfold coupledBTRTopRowMat2DC39; simp [hp, hc0]
        · have ep : p = fin2Z1W16 := Fin.ext hp
          have ec : c = fin2Z0W16 := Fin.ext hc0
          rw [ep, ec]
          change (match x.val with | 28 => b' | 31 => 7 * b' | _ => 0) =
            (match x.val with | 28 => 0 | 31 => 7 * 0 | _ => 0)
          split <;> omega
        · unfold coupledBTRTopRowMat2DC39; simp [hp, hc0]
      rw [hm_step _ x xs p q, hm_step _ x xs p q, hmat_eq, hmat_eq,
          ihu hxs_b fin2Z0W16 q, ihu hxs_b fin2Z1W16 q]
  have hcongr_noA : ∀ (a' b' : Nat) (u : List (Fin 42)), noAlphaSymBoolW16 u = true ->
      ∀ p q : Fin 2,
        evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 1 a' b') u p q =
          evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 1 0 b') u p q := by
    intro a' b' u; induction u with
    | nil => intros; rfl
    | cons x xs ihu =>
      intro hau p q; unfold noAlphaSymBoolW16 at hau
      rcases bool_and_split hau with ⟨hx_b, hxs_b⟩
      rcases of_decide_eq_true hx_b with ⟨hx22, hx23, hx32, hx37, hx40, hx41⟩
      have hmat_eq : ∀ c : Fin 2,
          coupledBTRTopRowMat2DC39 1 a' b' x p c = coupledBTRTopRowMat2DC39 1 0 b' x p c := by
        intro c
        rcases (by have := p.isLt; omega : p.val = 0 ∨ p.val = 1) with hp | hp <;>
        rcases (by have := c.isLt; omega : c.val = 0 ∨ c.val = 1) with hc0 | hc0
        · unfold coupledBTRTopRowMat2DC39; simp [hp, hc0]
        · have ep : p = fin2Z0W16 := Fin.ext hp
          have ec : c = fin2Z1W16 := Fin.ext hc0
          rw [ep, ec]
          change (match x.val with
            | 22 => a' | 23 => a' | 32 => a' | 37 => a' | 40 => a' | 41 => a' | _ => 0) =
            (match x.val with
            | 22 => 0 | 23 => 0 | 32 => 0 | 37 => 0 | 40 => 0 | 41 => 0 | _ => 0)
          split <;> omega
        · unfold coupledBTRTopRowMat2DC39; simp [hp, hc0]
        · unfold coupledBTRTopRowMat2DC39; simp [hp, hc0]
      rw [hm_step _ x xs p q, hm_step _ x xs p q, hmat_eq, hmat_eq,
          ihu hxs_b fin2Z0W16 q, ihu hxs_b fin2Z1W16 q]
  have hno_beta_aff : ∀ (w : List (Fin 42)), noBetaSymBoolW16 w = true ->
      (∀ a' : Nat,
        evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 1 a' 0) w fin2Z1W16 fin2Z0W16 = 0 ∧
        evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 1 a' 0) w fin2Z1W16 fin2Z1W16 =
          evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 1 0 0) w fin2Z1W16 fin2Z1W16 ∧
        evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 1 a' 0) w fin2Z0W16 fin2Z0W16 = 1 ∧
        evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 1 a' 0) w fin2Z0W16 fin2Z1W16 =
          a' * evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 1 1 0) w fin2Z0W16 fin2Z1W16) := by
    intro w; induction w with
    | nil =>
      intros _ a'; simp [evalFinWordMat, natMatId]
    | cons s tl ih =>
      intro hnb a'
      unfold noBetaSymBoolW16 at hnb
      rcases bool_and_split hnb with ⟨hs_b, htl_nb⟩
      rcases of_decide_eq_true hs_b with ⟨hn28, hn31⟩
      rcases ih htl_nb a' with ⟨ih10, ih11, ih00, ih01⟩
      rcases ih htl_nb 1 with ⟨ih10_1, ih11_1, ih00_1, _⟩
      have hs00 : ∀ x : Nat, coupledBTRTopRowMat2DC39 1 x 0 s fin2Z0W16 fin2Z0W16 = 1 := by
        intro x; unfold coupledBTRTopRowMat2DC39; dsimp only [fin2Z0W16]
        by_cases h : (s.val == 6 || s.val == 9) = true <;> simp [h]
      have hs10 : ∀ x : Nat, coupledBTRTopRowMat2DC39 1 x 0 s fin2Z1W16 fin2Z0W16 = 0 := by
        intro x; change (match s.val with | 28 => 0 | 31 => 7 * 0 | _ => 0) = 0; split <;> omega
      have hs11 : ∀ x : Nat, coupledBTRTopRowMat2DC39 1 x 0 s fin2Z1W16 fin2Z1W16 =
          coupledBTRTopRowMat2DC39 1 0 0 s fin2Z1W16 fin2Z1W16 := fun _ => rfl
      have hs01 : coupledBTRTopRowMat2DC39 1 a' 0 s fin2Z0W16 fin2Z1W16 =
          a' * coupledBTRTopRowMat2DC39 1 1 0 s fin2Z0W16 fin2Z1W16 := by
        change (match s.val with
          | 22 => a' | 23 => a' | 32 => a' | 37 => a' | 40 => a' | 41 => a' | _ => 0) =
          a' * (match s.val with
          | 22 => 1 | 23 => 1 | 32 => 1 | 37 => 1 | 40 => 1 | 41 => 1 | _ => 0)
        split <;> omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hm_step _ s tl fin2Z1W16 fin2Z0W16, hs10, ih10, Nat.zero_mul, Nat.mul_zero]
      · rw [hm_step _ s tl fin2Z1W16 fin2Z1W16, hm_step _ s tl fin2Z1W16 fin2Z1W16,
            hs10, hs10, Nat.zero_mul, Nat.zero_mul, hs11, ih11]
      · rw [hm_step _ s tl fin2Z0W16 fin2Z0W16, hs00, ih00, ih10, Nat.mul_zero, Nat.mul_one]
      · rw [hm_step _ s tl fin2Z0W16 fin2Z1W16, hm_step _ s tl fin2Z0W16 fin2Z1W16,
            hs00, hs00, Nat.one_mul, Nat.one_mul, ih01, hs01, ih11, ih11_1,
            Nat.mul_add a', Nat.mul_assoc]
  have hno_alpha_aff : ∀ (w : List (Fin 42)), noAlphaSymBoolW16 w = true ->
      (∀ b' : Nat,
        evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 1 0 b') w fin2Z0W16 fin2Z1W16 = 0 ∧
        evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 1 0 b') w fin2Z0W16 fin2Z0W16 = 1 ∧
        evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 1 0 b') w fin2Z1W16 fin2Z1W16 =
          evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 1 0 0) w fin2Z1W16 fin2Z1W16 ∧
        evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 1 0 b') w fin2Z1W16 fin2Z0W16 =
          b' * evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 1 0 1) w fin2Z1W16 fin2Z0W16) := by
    intro w; induction w with
    | nil =>
      intros _ b'; simp [evalFinWordMat, natMatId]
    | cons s tl ih =>
      intro hna b'
      unfold noAlphaSymBoolW16 at hna
      rcases bool_and_split hna with ⟨hs_b, htl_na⟩
      rcases of_decide_eq_true hs_b with ⟨hn22, hn23, hn32, hn37, hn40, hn41⟩
      rcases ih htl_na b' with ⟨ih01, ih00, ih11, ih10⟩
      rcases ih htl_na 1 with ⟨ih01_1, ih00_1, _, ih10_1⟩
      rcases ih htl_na 0 with ⟨ih01_0, _, _, _⟩
      have hs00 : ∀ y : Nat, coupledBTRTopRowMat2DC39 1 0 y s fin2Z0W16 fin2Z0W16 = 1 := by
        intro y; unfold coupledBTRTopRowMat2DC39; dsimp only [fin2Z0W16]
        by_cases h : (s.val == 6 || s.val == 9) = true <;> simp [h]
      have hs01 : ∀ y : Nat, coupledBTRTopRowMat2DC39 1 0 y s fin2Z0W16 fin2Z1W16 = 0 := by
        intro y
        change (match s.val with
          | 22 => 0 | 23 => 0 | 32 => 0 | 37 => 0 | 40 => 0 | 41 => 0 | _ => 0) = 0
        split <;> omega
      have hs11 : ∀ y : Nat, coupledBTRTopRowMat2DC39 1 0 y s fin2Z1W16 fin2Z1W16 =
          coupledBTRTopRowMat2DC39 1 0 0 s fin2Z1W16 fin2Z1W16 := fun _ => rfl
      have hs10 : coupledBTRTopRowMat2DC39 1 0 b' s fin2Z1W16 fin2Z0W16 =
          b' * coupledBTRTopRowMat2DC39 1 0 1 s fin2Z1W16 fin2Z0W16 := by
        change (match s.val with | 28 => b' | 31 => 7 * b' | _ => 0) =
          b' * (match s.val with | 28 => 1 | 31 => 7 * 1 | _ => 0)
        split <;> omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hm_step _ s tl fin2Z0W16 fin2Z1W16, hs01, ih01, Nat.zero_mul, Nat.mul_zero]
      · rw [hm_step _ s tl fin2Z0W16 fin2Z0W16, hs00, hs01, ih00, Nat.zero_mul, Nat.mul_one]
      · rw [hm_step _ s tl fin2Z1W16 fin2Z1W16, hm_step _ s tl fin2Z1W16 fin2Z1W16,
            ih01, ih01_0, Nat.mul_zero, Nat.mul_zero, hs11, ih11]
      · rw [hm_step _ s tl fin2Z1W16 fin2Z0W16, hm_step _ s tl fin2Z1W16 fin2Z0W16,
            ih00, ih00_1, Nat.mul_one, Nat.mul_one, hs10, ih10, hs11 b', hs11 1,
            Nat.mul_add b', ← Nat.mul_assoc _ b', Nat.mul_comm _ b', Nat.mul_assoc b']
  have hword_ab_lin : ∀ (w : List (Fin 42)),
      (noBetaSymBoolW16 w || noAlphaSymBoolW16 w) = true ->
      ∀ i j : Fin 2,
        let e00 := evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 1 0 0) w i j
        let e10 := evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 1 1 0) w i j
        let e01 := evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 1 0 1) w i j
        evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 1 alpha beta) w i j =
          e00 + alpha * (e10 - e00) + beta * (e01 - e00) := by
    intro w hor i j; dsimp only
    rcases Bool.or_eq_true_iff.mp hor with hnb | hna
    · rw [hcongr_noB alpha beta w hnb i j, hcongr_noB 0 1 w hnb i j,
          Nat.sub_self, Nat.mul_zero, Nat.add_zero]
      rcases hno_beta_aff w hnb alpha with ⟨h10_a, h11_a, h00_a, h01_a⟩
      rcases hno_beta_aff w hnb 1 with ⟨h10_1, h11_1, h00_1, _⟩
      rcases hno_beta_aff w hnb 0 with ⟨h10_0, _, h00_0, h01_0⟩
      rcases (by have := i.isLt; omega : i.val = 0 ∨ i.val = 1) with hi | hi <;>
      rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1) with hj | hj
      · have e1 : i = fin2Z0W16 := Fin.ext hi
        have e2 : j = fin2Z0W16 := Fin.ext hj
        rw [e1, e2, h00_a, h00_0, h00_1]; omega
      · have e1 : i = fin2Z0W16 := Fin.ext hi
        have e2 : j = fin2Z1W16 := Fin.ext hj
        rw [e1, e2, h01_a, h01_0, Nat.zero_mul, Nat.sub_zero]; omega
      · have e1 : i = fin2Z1W16 := Fin.ext hi
        have e2 : j = fin2Z0W16 := Fin.ext hj
        rw [e1, e2, h10_a, h10_0, h10_1]; omega
      · have e1 : i = fin2Z1W16 := Fin.ext hi
        have e2 : j = fin2Z1W16 := Fin.ext hj
        rw [e1, e2, h11_a, h11_1, Nat.sub_self, Nat.mul_zero]; omega
    · rw [hcongr_noA alpha beta w hna i j, hcongr_noA 1 0 w hna i j,
          Nat.sub_self, Nat.mul_zero, Nat.add_zero]
      rcases hno_alpha_aff w hna beta with ⟨h01_b, h00_b, h11_b, h10_b⟩
      rcases hno_alpha_aff w hna 1 with ⟨h01_1, h00_1, h11_1, _⟩
      rcases hno_alpha_aff w hna 0 with ⟨h01_0, h00_0, _, h10_0⟩
      rcases (by have := i.isLt; omega : i.val = 0 ∨ i.val = 1) with hi | hi <;>
      rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1) with hj | hj
      · have e1 : i = fin2Z0W16 := Fin.ext hi
        have e2 : j = fin2Z0W16 := Fin.ext hj
        rw [e1, e2, h00_b, h00_0, h00_1]; omega
      · have e1 : i = fin2Z0W16 := Fin.ext hi
        have e2 : j = fin2Z1W16 := Fin.ext hj
        rw [e1, e2, h01_b, h01_0, h01_1]; omega
      · have e1 : i = fin2Z1W16 := Fin.ext hi
        have e2 : j = fin2Z0W16 := Fin.ext hj
        rw [e1, e2, h10_b, h10_0, Nat.zero_mul, Nat.sub_zero]; omega
      · have e1 : i = fin2Z1W16 := Fin.ext hi
        have e2 : j = fin2Z1W16 := Fin.ext hj
        rw [e1, e2, h11_b, h11_1, Nat.sub_self, Nat.mul_zero]; omega
  have hcpl_corners :
      c39FastRulesW16.all (fun r =>
        (noBetaSymBoolW16 r.1 || noAlphaSymBoolW16 r.1) &&
        (noBetaSymBoolW16 r.2 || noAlphaSymBoolW16 r.2) &&
        [fin2Z0W16, fin2Z1W16].all (fun i =>
          [fin2Z0W16, fin2Z1W16].all (fun j =>
            let l00 := evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 1 0 0) r.1 i j
            let r00 := evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 1 0 0) r.2 i j
            let l10 := evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 1 1 0) r.1 i j
            let r10 := evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 1 1 0) r.2 i j
            let l01 := evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 1 0 1) r.1 i j
            let r01 := evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 1 0 1) r.2 i j
            decide (r00 ≤ l00 ∧ r10 - r00 ≤ l10 - l00 ∧ r01 - r00 ≤ l01 - l00)))) = true := by decide
  have hcpl_w1 : ∀ r ∈ c39FastRulesW16, ∀ i j : Fin 2,
      evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 1 alpha beta) r.1 i j ≥
        evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 1 alpha beta) r.2 i j := by
    intro r hr i j
    rcases bool_and_split (List.all_eq_true.mp hcpl_corners r hr) with ⟨hb1, hall_ij⟩
    rcases bool_and_split hb1 with ⟨hor1, hor2⟩
    have hi_m : i ∈ [fin2Z0W16, fin2Z1W16] := by
      rcases (by have := i.isLt; omega : i.val = 0 ∨ i.val = 1) with h | h
      · rw [show i = fin2Z0W16 from Fin.ext h]; exact List.Mem.head _
      · rw [show i = fin2Z1W16 from Fin.ext h]; exact List.Mem.tail _ (List.Mem.head _)
    have hj_m : j ∈ [fin2Z0W16, fin2Z1W16] := by
      rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1) with h | h
      · rw [show j = fin2Z0W16 from Fin.ext h]; exact List.Mem.head _
      · rw [show j = fin2Z1W16 from Fin.ext h]; exact List.Mem.tail _ (List.Mem.head _)
    rcases of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hall_ij i hi_m) j hj_m) with
      ⟨hc00, hca, hcb⟩
    have hl := hword_ab_lin r.1 hor1 i j
    have hr_e := hword_ab_lin r.2 hor2 i j
    dsimp only at hl hr_e
    rw [hl, hr_e]
    have hma := Nat.mul_le_mul_left alpha hca
    have hmb := Nat.mul_le_mul_left beta hcb
    omega
  have hcpl_wk : ∀ r ∈ c39FastRulesW16, ∀ i j : Fin 2,
      evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 k alpha beta) r.1 i j ≥
        evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 k alpha beta) r.2 i j := by
    apply hlift_from_k1 (fun kv => coupledBTRTopRowMat2DC39 kv alpha beta)
    · intro s hn6 hn9 p q
      unfold coupledBTRTopRowMat2DC39
      rcases (by have := p.isLt; omega : p.val = 0 ∨ p.val = 1) with hp | hp <;>
      rcases (by have := q.isLt; omega : q.val = 0 ∨ q.val = 1) with hq | hq <;>
      simp only [hp, hq, beq_false_of_ne hn6, beq_false_of_ne hn9]; all_goals rfl
    · intro s hs69
      have hs_v : s.val = 6 ∨ s.val = 9 := by
        rcases Bool.or_eq_true_iff.mp hs69 with h6 | h9
        · exact Or.inl (Nat.eq_of_beq_eq_true h6)
        · exact Or.inr (Nat.eq_of_beq_eq_true h9)
      rcases hs_v with hs | hs <;> simp [coupledBTRTopRowMat2DC39, hs]
    · exact hcpl_w1
  exact ⟨hbnd_wk, hcpl_wk⟩

private theorem evalFinWordMat_proj84To42_w16 (k alpha beta : Nat) :
    ∀ (w : List (Fin 84)) (i j : Fin 2),
      evalFinWordMat 84 2 (coupledBTRTopRowMat2DC78 k alpha beta) w i j =
        evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 k alpha beta) (w.map projSym84To42) i j
  | [], _, _ => rfl
  | s :: tl, i, j => by
    have hm84 : evalFinWordMat 84 2 (coupledBTRTopRowMat2DC78 k alpha beta) (s :: tl) i j =
        coupledBTRTopRowMat2DC78 k alpha beta s i fin2Z0W16 *
          evalFinWordMat 84 2 (coupledBTRTopRowMat2DC78 k alpha beta) tl fin2Z0W16 j +
        coupledBTRTopRowMat2DC78 k alpha beta s i fin2Z1W16 *
          evalFinWordMat 84 2 (coupledBTRTopRowMat2DC78 k alpha beta) tl fin2Z1W16 j := by
      change (0 + coupledBTRTopRowMat2DC78 k alpha beta s i fin2Z0W16 *
        evalFinWordMat 84 2 (coupledBTRTopRowMat2DC78 k alpha beta) tl fin2Z0W16 j) +
        coupledBTRTopRowMat2DC78 k alpha beta s i fin2Z1W16 *
          evalFinWordMat 84 2 (coupledBTRTopRowMat2DC78 k alpha beta) tl fin2Z1W16 j = _; omega
    have hm42 : evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 k alpha beta)
          (projSym84To42 s :: tl.map projSym84To42) i j =
        coupledBTRTopRowMat2DC39 k alpha beta (projSym84To42 s) i fin2Z0W16 *
          evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 k alpha beta) (tl.map projSym84To42) fin2Z0W16 j +
        coupledBTRTopRowMat2DC39 k alpha beta (projSym84To42 s) i fin2Z1W16 *
          evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 k alpha beta) (tl.map projSym84To42) fin2Z1W16 j := by
      change (0 + coupledBTRTopRowMat2DC39 k alpha beta (projSym84To42 s) i fin2Z0W16 *
        evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 k alpha beta) (tl.map projSym84To42) fin2Z0W16 j) +
        coupledBTRTopRowMat2DC39 k alpha beta (projSym84To42 s) i fin2Z1W16 *
          evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 k alpha beta) (tl.map projSym84To42) fin2Z1W16 j = _; omega
    simp only [List.map_cons]
    rw [hm84, hm42,
        evalFinWordMat_proj84To42_w16 k alpha beta tl fin2Z0W16 j,
        evalFinWordMat_proj84To42_w16 k alpha beta tl fin2Z1W16 j]
    rfl

private theorem coupled_farkas_zero_strict_proj_w16
    (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 : List (Fin N) -> Nat)
    (rs : List (List (Fin N) × List (Fin N)))
    (hshape_b : checkWordShapeCoupledNBool N proj mu0 mu1 rs = true)
    (hfark_b0 : checkCoupledFarkasCoordNBool N proj mu0 mu1 fin2Z0W16 rs = true)
    (hfark_b1 : checkCoupledFarkasCoordNBool N proj mu0 mu1 fin2Z1W16 rs = true)
    (k alpha beta : Nat) (v : Fin N -> Fin 2 -> Nat)
    (hv_weak : ∀ r ∈ rs, ∀ i : Fin 2,
      evalFinWordVec N 2 (fun s => coupledBTRTopRowMat2DC39 k alpha beta (proj s)) v r.1 i ≥
        evalFinWordVec N 2 (fun s => coupledBTRTopRowMat2DC39 k alpha beta (proj s)) v r.2 i) :
    ∀ r ∈ rs,
      evalFinWordVec N 2 (fun s => coupledBTRTopRowMat2DC39 k alpha beta (proj s)) v r.1 fin2Z0W16 =
        evalFinWordVec N 2 (fun s => coupledBTRTopRowMat2DC39 k alpha beta (proj s)) v r.2 fin2Z0W16 := by
  let matFn := fun k' a' b' (s : Fin N) => coupledBTRTopRowMat2DC39 k' a' b' (proj s)
  have hfark_aff : ∀ (v0 : Fin N -> Fin 2 -> Nat)
      (xs : List (List (Fin N) × List (Fin N))),
      checkWordShapeCoupledNBool N proj mu0 mu1 xs = true ->
      farkasCoupledVecLhsN N proj mu0 mu1 1 0 0 v0 xs ≤
        farkasCoupledVecLhsN N proj mu0 mu1 1 1 0 v0 xs ∧
      farkasCoupledVecRhsN N proj mu0 mu1 1 0 0 v0 xs ≤
        farkasCoupledVecRhsN N proj mu0 mu1 1 1 0 v0 xs ∧
      farkasCoupledVecLhsN N proj mu0 mu1 k alpha beta v0 xs =
        farkasCoupledVecLhsN N proj mu0 mu1 1 0 0 v0 xs +
          alpha * (farkasCoupledVecLhsN N proj mu0 mu1 1 1 0 v0 xs -
            farkasCoupledVecLhsN N proj mu0 mu1 1 0 0 v0 xs) ∧
      farkasCoupledVecRhsN N proj mu0 mu1 k alpha beta v0 xs =
        farkasCoupledVecRhsN N proj mu0 mu1 1 0 0 v0 xs +
          alpha * (farkasCoupledVecRhsN N proj mu0 mu1 1 1 0 v0 xs -
            farkasCoupledVecRhsN N proj mu0 mu1 1 0 0 v0 xs) := by
    intro v0 xs; induction xs with
    | nil => intros; simp [farkasCoupledVecLhsN, farkasCoupledVecRhsN]
    | cons r0 rtl ih =>
      rcases r0 with ⟨l0, r0_w⟩
      intro hbw
      unfold checkWordShapeCoupledNBool at hbw
      simp only [List.all_cons] at hbw
      rcases bool_and_split hbw with ⟨h0_b, htl_b⟩
      rcases ih htl_b with ⟨hle_tl1, hle_tl2, htl1, htl2⟩
      rcases bool_and_split h0_b with ⟨hb_a, _⟩
      rcases bool_and_split hb_a with ⟨hb_b, hmu1_disj⟩
      rcases bool_and_split hb_b with ⟨hl_nb, hr_nb⟩
      rcases (coupledMatProj_affine_in_alpha_w16 N proj k alpha beta v0).2 l0 hl_nb with ⟨hle_l0, hl0_ab⟩
      rcases (coupledMatProj_affine_in_alpha_w16 N proj k alpha beta v0).2 r0_w hr_nb with ⟨hle_r0, hr0_ab⟩
      have hm1_term :
          (alpha * mu1 l0) * evalFinWordVec N 2 (matFn k alpha beta) v0 l0 fin2Z1W16 =
            alpha * (mu1 l0 * evalFinWordVec N 2 (matFn 1 1 0) v0 l0 fin2Z1W16) ∧
          (alpha * mu1 l0) * evalFinWordVec N 2 (matFn k alpha beta) v0 r0_w fin2Z1W16 =
            alpha * (mu1 l0 * evalFinWordVec N 2 (matFn 1 1 0) v0 r0_w fin2Z1W16) := by
        rcases Bool.or_eq_true_iff.mp hmu1_disj with hm0_b | hnb_12
        · rw [of_decide_eq_true hm0_b]; simp
        · rcases bool_and_split hnb_12 with ⟨hnl1, hnl2⟩
          have e1 := (coupledMatProj_affine_in_alpha_w16 N proj k alpha beta v0).1 l0 hnl1
          have e1' := (coupledMatProj_affine_in_alpha_w16 N proj 1 1 0 v0).1 l0 hnl1
          have e2 := (coupledMatProj_affine_in_alpha_w16 N proj k alpha beta v0).1 r0_w hnl2
          have e2' := (coupledMatProj_affine_in_alpha_w16 N proj 1 1 0 v0).1 r0_w hnl2
          dsimp only [matFn] at e1 e1' e2 e2' ⊢
          rw [e1, ← e1', e2, ← e2', Nat.mul_assoc, Nat.mul_assoc]
          exact ⟨rfl, rfl⟩
      simp only [farkasCoupledVecLhsN, farkasCoupledVecRhsN, Nat.zero_mul, Nat.one_mul, Nat.add_zero]
      dsimp only [matFn] at hl0_ab hr0_ab hm1_term hle_l0 hle_r0
      rw [hl0_ab, hr0_ab, hm1_term.1, hm1_term.2, htl1, htl2]
      have hm_l0 := Nat.mul_le_mul_left (mu0 l0) hle_l0
      have hm_r0 := Nat.mul_le_mul_left (mu0 l0) hle_r0
      refine ⟨by omega, by omega, ?_, ?_⟩
      · have hs1 :
            (mu0 l0 * evalFinWordVec N 2 (matFn 1 1 0) v0 l0 fin2Z0W16 +
             mu1 l0 * evalFinWordVec N 2 (matFn 1 1 0) v0 l0 fin2Z1W16 +
             farkasCoupledVecLhsN N proj mu0 mu1 1 1 0 v0 rtl) -
            (mu0 l0 * evalFinWordVec N 2 (matFn 1 0 0) v0 l0 fin2Z0W16 +
             farkasCoupledVecLhsN N proj mu0 mu1 1 0 0 v0 rtl) =
            mu0 l0 *
              (evalFinWordVec N 2 (matFn 1 1 0) v0 l0 fin2Z0W16 -
               evalFinWordVec N 2 (matFn 1 0 0) v0 l0 fin2Z0W16) +
            mu1 l0 * evalFinWordVec N 2 (matFn 1 1 0) v0 l0 fin2Z1W16 +
            (farkasCoupledVecLhsN N proj mu0 mu1 1 1 0 v0 rtl -
             farkasCoupledVecLhsN N proj mu0 mu1 1 0 0 v0 rtl) := by
          dsimp only [matFn] at hm_l0 ⊢
          rw [Nat.mul_sub_left_distrib]; omega
        dsimp only [matFn] at hs1 ⊢
        rw [hs1, Nat.mul_add (mu0 l0), Nat.mul_add alpha, Nat.mul_add alpha,
            ← Nat.mul_assoc alpha (mu0 l0), Nat.mul_comm alpha (mu0 l0),
            Nat.mul_assoc (mu0 l0) alpha]
        omega
      · have hs2 :
            (mu0 l0 * evalFinWordVec N 2 (matFn 1 1 0) v0 r0_w fin2Z0W16 +
             mu1 l0 * evalFinWordVec N 2 (matFn 1 1 0) v0 r0_w fin2Z1W16 +
             farkasCoupledVecRhsN N proj mu0 mu1 1 1 0 v0 rtl) -
            (mu0 l0 * evalFinWordVec N 2 (matFn 1 0 0) v0 r0_w fin2Z0W16 +
             farkasCoupledVecRhsN N proj mu0 mu1 1 0 0 v0 rtl) =
            mu0 l0 *
              (evalFinWordVec N 2 (matFn 1 1 0) v0 r0_w fin2Z0W16 -
               evalFinWordVec N 2 (matFn 1 0 0) v0 r0_w fin2Z0W16) +
            mu1 l0 * evalFinWordVec N 2 (matFn 1 1 0) v0 r0_w fin2Z1W16 +
            (farkasCoupledVecRhsN N proj mu0 mu1 1 1 0 v0 rtl -
             farkasCoupledVecRhsN N proj mu0 mu1 1 0 0 v0 rtl) := by
          dsimp only [matFn] at hm_r0 ⊢
          rw [Nat.mul_sub_left_distrib]; omega
        dsimp only [matFn] at hs2 ⊢
        rw [hs2, Nat.mul_add (mu0 l0), Nat.mul_add alpha, Nat.mul_add alpha,
            ← Nat.mul_assoc alpha (mu0 l0), Nat.mul_comm alpha (mu0 l0),
            Nat.mul_assoc (mu0 l0) alpha]
        omega
  have hcoord_kab : ∀ (j0 : Fin 2),
      checkCoupledFarkasCoordNBool N proj mu0 mu1 j0 rs = true ->
      ∀ s0 : Fin N,
        farkasCoupledVecLhsN N proj mu0 mu1 k alpha beta (basisVec2D N s0 j0) rs ≤
          farkasCoupledVecRhsN N proj mu0 mu1 k alpha beta (basisVec2D N s0 j0) rs := by
    intro j0 hchk
    unfold checkCoupledFarkasCoordNBool at hchk
    have hlp : ∀ n : Nat, n ≤ N ->
        checkCoupledFarkasCoordNBool.loop N proj mu0 mu1 j0 rs n = true ->
        ∀ m : Nat, m < n -> (hm : m < N) ->
          farkasCoupledVecLhsN N proj mu0 mu1 k alpha beta (basisVec2D N ⟨m, hm⟩ j0) rs ≤
            farkasCoupledVecRhsN N proj mu0 mu1 k alpha beta (basisVec2D N ⟨m, hm⟩ j0) rs := by
      intro n; induction n with
      | zero => intros _ _ _ hlt; omega
      | succ n' ih =>
        intro hn_le hn m hmn hmN
        have hnN : n' < N := hn_le
        unfold checkCoupledFarkasCoordNBool.loop at hn
        simp only [hnN, dite_true] at hn
        rcases bool_and_split hn with ⟨hc, hprev⟩
        by_cases hmeq : m = n'
        · subst hmeq
          rcases hfark_aff (basisVec2D N ⟨m, hmN⟩ j0) rs hshape_b with ⟨_, _, ha1, ha2⟩
          rw [farkasCoupledFastPairN_eq N proj mu0 mu1 1 0 0,
              farkasCoupledFastPairN_eq N proj mu0 mu1 1 1 0] at hc
          dsimp only at hc
          rw [ha1, ha2]
          rcases of_decide_eq_true hc with ⟨hb0_le, hsl⟩
          have hm_sl := Nat.mul_le_mul_left alpha hsl
          omega
        · exact ih (Nat.le_of_lt hn_le) hprev m (by omega) hmN
    intro s0; exact hlp N (Nat.le_refl N) hchk s0.val s0.isLt s0.isLt
  have hbasis_kab : ∀ s0 : Fin N,
      farkasCoupledVecLhsN N proj mu0 mu1 k alpha beta (basisVec2D N s0 fin2Z0W16) rs ≤
        farkasCoupledVecRhsN N proj mu0 mu1 k alpha beta (basisVec2D N s0 fin2Z0W16) rs ∧
      farkasCoupledVecLhsN N proj mu0 mu1 k alpha beta (basisVec2D N s0 fin2Z1W16) rs ≤
        farkasCoupledVecRhsN N proj mu0 mu1 k alpha beta (basisVec2D N s0 fin2Z1W16) rs :=
    fun s0 => ⟨hcoord_kab fin2Z0W16 hfark_b0 s0, hcoord_kab fin2Z1W16 hfark_b1 s0⟩
  let M := matFn k alpha beta
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
          v s0 fin2Z0W16 * evalFinWordVec N 2 M (basisVec2D N s0 fin2Z0W16) w i +
          v s0 fin2Z1W16 * evalFinWordVec N 2 M (basisVec2D N s0 fin2Z1W16) w i) N := by
    have hdelta : ∀ (s : Fin N) (j : Fin 2),
        v s j = natSumPrefix N (fun s0 =>
          v s0 fin2Z0W16 * basisVec2D N s0 fin2Z0W16 s j +
          v s0 fin2Z1W16 * basisVec2D N s0 fin2Z1W16 s j) N := by
      intro s j
      have hst : ∀ m : Nat, m ≤ N ->
          natSumPrefix N (fun s0 =>
            v s0 fin2Z0W16 * basisVec2D N s0 fin2Z0W16 s j +
            v s0 fin2Z1W16 * basisVec2D N s0 fin2Z1W16 s j) m =
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
            · rw [show j = fin2Z0W16 from Fin.ext hj]; simp [basisVec2D, fin2Z0W16, fin2Z1W16]
            · rw [show j = fin2Z1W16 from Fin.ext hj]; simp [basisVec2D, fin2Z0W16, fin2Z1W16]
          · have hne_b : (s.val == m') = false := beq_false_of_ne heq
            have hb0 : basisVec2D N ⟨m', hm_lt⟩ fin2Z0W16 s j = 0 := by simp [basisVec2D, hne_b]
            have hb1 : basisVec2D N ⟨m', hm_lt⟩ fin2Z1W16 s j = 0 := by simp [basisVec2D, hne_b]
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
      rw [mat2_step_expandN_w16 N M v s rest i, hdelta s i, ih fin2Z0W16, ih fin2Z1W16,
          hsum_mul (M s i fin2Z0W16), hsum_mul (M s i fin2Z1W16), ← hsum_add, ← hsum_add]
      have hpt : ∀ s0 : Fin N,
          (v s0 fin2Z0W16 * basisVec2D N s0 fin2Z0W16 s i +
           v s0 fin2Z1W16 * basisVec2D N s0 fin2Z1W16 s i) +
          M s i fin2Z0W16 *
            (v s0 fin2Z0W16 * evalFinWordVec N 2 M (basisVec2D N s0 fin2Z0W16) rest fin2Z0W16 +
             v s0 fin2Z1W16 * evalFinWordVec N 2 M (basisVec2D N s0 fin2Z1W16) rest fin2Z0W16) +
          M s i fin2Z1W16 *
            (v s0 fin2Z0W16 * evalFinWordVec N 2 M (basisVec2D N s0 fin2Z0W16) rest fin2Z1W16 +
             v s0 fin2Z1W16 * evalFinWordVec N 2 M (basisVec2D N s0 fin2Z1W16) rest fin2Z1W16) =
          v s0 fin2Z0W16 * evalFinWordVec N 2 M (basisVec2D N s0 fin2Z0W16) (s :: rest) i +
          v s0 fin2Z1W16 * evalFinWordVec N 2 M (basisVec2D N s0 fin2Z1W16) (s :: rest) i := by
        intro s0
        rw [mat2_step_expandN_w16 N M (basisVec2D N s0 fin2Z0W16) s rest i,
            mat2_step_expandN_w16 N M (basisVec2D N s0 fin2Z1W16) s rest i,
            Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add]
        ac_rfl
      exact hcongr _ _ hpt N
  have hfark_lin : ∀ xs : List (List (Fin N) × List (Fin N)),
      farkasCoupledVecLhsN N proj mu0 mu1 k alpha beta v xs =
        natSumPrefix N (fun s0 =>
          v s0 fin2Z0W16 * farkasCoupledVecLhsN N proj mu0 mu1 k alpha beta (basisVec2D N s0 fin2Z0W16) xs +
          v s0 fin2Z1W16 * farkasCoupledVecLhsN N proj mu0 mu1 k alpha beta (basisVec2D N s0 fin2Z1W16) xs) N ∧
      farkasCoupledVecRhsN N proj mu0 mu1 k alpha beta v xs =
        natSumPrefix N (fun s0 =>
          v s0 fin2Z0W16 * farkasCoupledVecRhsN N proj mu0 mu1 k alpha beta (basisVec2D N s0 fin2Z0W16) xs +
          v s0 fin2Z1W16 * farkasCoupledVecRhsN N proj mu0 mu1 k alpha beta (basisVec2D N s0 fin2Z1W16) xs) N := by
    intro xs; induction xs with
    | nil =>
      have hz : ∀ m : Nat, natSumPrefix N (fun _ => 0) m = 0 := by
        intro m; induction m with
        | zero => rfl
        | succ m' ih => simp only [natSumPrefix]; by_cases hm : m' < N <;> simp [hm, ih]
      refine ⟨?_, ?_⟩ <;> simpa [farkasCoupledVecLhsN, farkasCoupledVecRhsN] using (hz N).symm
    | cons r0 rtl ih =>
      rcases r0 with ⟨l0, r0_w⟩
      rcases ih with ⟨ihl, ihr⟩
      refine ⟨?_, ?_⟩
      · simp only [farkasCoupledVecLhsN]
        change mu0 l0 * evalFinWordVec N 2 M v l0 fin2Z0W16 +
          (alpha * mu1 l0) * evalFinWordVec N 2 M v l0 fin2Z1W16 +
          farkasCoupledVecLhsN N proj mu0 mu1 k alpha beta v rtl = _
        rw [hv_lin l0 fin2Z0W16, hv_lin l0 fin2Z1W16, ihl,
            hsum_mul (mu0 l0), hsum_mul (alpha * mu1 l0),
            ← hsum_add, ← hsum_add]
        apply hcongr _ _ (fun s0 => ?_) N
        simp only [Nat.mul_add]; ac_rfl
      · simp only [farkasCoupledVecRhsN]
        change mu0 l0 * evalFinWordVec N 2 M v r0_w fin2Z0W16 +
          (alpha * mu1 l0) * evalFinWordVec N 2 M v r0_w fin2Z1W16 +
          farkasCoupledVecRhsN N proj mu0 mu1 k alpha beta v rtl = _
        rw [hv_lin r0_w fin2Z0W16, hv_lin r0_w fin2Z1W16, ihr,
            hsum_mul (mu0 l0), hsum_mul (alpha * mu1 l0),
            ← hsum_add, ← hsum_add]
        apply hcongr _ _ (fun s0 => ?_) N
        simp only [Nat.mul_add]; ac_rfl
  have htot_le : farkasCoupledVecLhsN N proj mu0 mu1 k alpha beta v rs ≤
      farkasCoupledVecRhsN N proj mu0 mu1 k alpha beta v rs := by
    rcases hfark_lin rs with ⟨hl, hr⟩
    rw [hl, hr]
    exact natSumPrefix_mono_w5 N _ _ (fun s0 =>
      Nat.add_le_add (Nat.mul_le_mul_left _ (hbasis_kab s0).1)
                     (Nat.mul_le_mul_left _ (hbasis_kab s0).2)) N
  have hmu0_pos : ∀ r ∈ rs, mu0 r.1 ≥ 1 := by
    intro r hr
    unfold checkWordShapeCoupledNBool at hshape_b
    rcases bool_and_split (List.all_eq_true.mp hshape_b r hr) with ⟨_, hm0_b⟩
    exact of_decide_eq_true hm0_b
  have hge_imp : ∀ xs : List (List (Fin N) × List (Fin N)),
      (∀ r ∈ xs, mu0 r.1 ≥ 1) ->
      (∀ r ∈ xs, ∀ i : Fin 2, evalFinWordVec N 2 M v r.1 i ≥ evalFinWordVec N 2 M v r.2 i) ->
      farkasCoupledVecLhsN N proj mu0 mu1 k alpha beta v xs ≥
        farkasCoupledVecRhsN N proj mu0 mu1 k alpha beta v xs ∧
      (farkasCoupledVecLhsN N proj mu0 mu1 k alpha beta v xs =
        farkasCoupledVecRhsN N proj mu0 mu1 k alpha beta v xs ->
        ∀ r ∈ xs, evalFinWordVec N 2 M v r.1 fin2Z0W16 = evalFinWordVec N 2 M v r.2 fin2Z0W16) := by
    intro xs; induction xs with
    | nil =>
      intros; exact ⟨Nat.le_refl 0, fun _ _ hr => by cases hr⟩
    | cons r0 rtl ih =>
      rcases r0 with ⟨l0, r0_w⟩
      intro hmp hw
      rcases ih (fun r hr => hmp r (List.Mem.tail _ hr))
        (fun r hr => hw r (List.Mem.tail _ hr)) with ⟨hge_tl, heq_tl⟩
      simp only [farkasCoupledVecLhsN, farkasCoupledVecRhsN]
      have hm0_1 : mu0 l0 ≥ 1 := hmp (l0, r0_w) (List.Mem.head _)
      have hw0 := hw (l0, r0_w) (List.Mem.head _) fin2Z0W16
      have hw1 := hw (l0, r0_w) (List.Mem.head _) fin2Z1W16
      have hg0 := Nat.mul_le_mul_left (mu0 l0) hw0
      have hg1 := Nat.mul_le_mul_left (alpha * mu1 l0) hw1
      dsimp only [M, matFn] at hw0 hw1 hg0 hg1 ⊢
      refine ⟨by omega, fun heq_tot r hr => ?_⟩
      cases hr with
      | head =>
        dsimp only [M, matFn]
        have heq_m0 : mu0 l0 * evalFinWordVec N 2 (fun s => coupledBTRTopRowMat2DC39 k alpha beta (proj s)) v l0 fin2Z0W16 =
            mu0 l0 * evalFinWordVec N 2 (fun s => coupledBTRTopRowMat2DC39 k alpha beta (proj s)) v r0_w fin2Z0W16 := by omega
        exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < mu0 l0) heq_m0
      | tail _ htl_m => exact heq_tl (by omega) r htl_m
  rcases hge_imp rs hmu0_pos hv_weak with ⟨hge_tot, heq_imp⟩
  exact heq_imp (by omega)

/--
  Theorem W16.1b (`coupled_r_boundary_and_t_toprow_d2_farkas_locks`,
  `zero custom axioms`):
  Infinite 3-Parameter Coupled `.R`-Boundary-Growth (`(M_6)_{0,0} = (M_9)_{0,0} = k ≥ 2`) +
  `.B`/`.T`-Top-Row Mixed Zero-Diagonal `d = 2` Cones on BOTH `c39` (`bndParamMat2DC39 k α β`,
  `20/39` strict matrix rules; `coupledBTRTopRowMat2DC39 k α β`, `11/39` strict matrix rules) AND
  `c78` (`coupledBTRTopRowMat2DC78 k α β`, `22/78` strict matrix rules), `+13` Escape From Wave 15's
  2-Rule Farkas Syzygy, & Universal Parameterized 2-Rule / 7-Rule / 14-Rule Bilinear Farkas
  Zero-Strict-Drop Locks (`Branch P4.3`, witness `ZPOS_C39_COUPLED_R_BND_AND_T_TOPROW_FARKAS_ESCAPE`,
  `W16_H1`).
-/
theorem coupled_r_boundary_and_t_toprow_d2_farkas_locks :
    let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
    let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
    (countStrictMat2DRules 42 (bndParamMat2DC39 2 1 1) c39 = 20 ∧
     countStrictMat2DRules 42 (coupledBTRTopRowMat2DC39 2 1 1) c39 = 11 ∧
     countStrictMat2DRules 84 (coupledBTRTopRowMat2DC78 2 1 1) c78 = 22 ∧
     coupledBTRTopRowMat2DC39 2 1 1 ⟨6, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩ = 2 ∧
     coupledBTRTopRowMat2DC39 2 1 1 ⟨9, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩ = 2 ∧
     coupledBTRTopRowMat2DC39 2 1 1 ⟨20, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 ∧
     coupledBTRTopRowMat2DC39 2 1 1 ⟨37, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩ = 1 ∧
     w15FarkasLhsOnCoupled (basisVec2D 42 ⟨17, by decide⟩ ⟨1, by decide⟩) c39 -
       w15FarkasRhsOnCoupled (basisVec2D 42 ⟨17, by decide⟩ ⟨1, by decide⟩) c39 = 13) ∧
    (∀ (k alpha beta : Nat), k ≥ 2 -> alpha ≥ 1 -> beta ≥ 1 ->
      (∀ r ∈ c39, ∀ i j : Fin 2,
        evalFinWordMat 42 2 (bndParamMat2DC39 k alpha beta) r.1 i j ≥
          evalFinWordMat 42 2 (bndParamMat2DC39 k alpha beta) r.2 i j) ∧
      (∀ v : Fin 42 -> Fin 2 -> Nat,
        (∀ r ∈ c39, ∀ i : Fin 2,
          evalFinWordVec 42 2 (bndParamMat2DC39 k alpha beta) v r.1 i ≥
            evalFinWordVec 42 2 (bndParamMat2DC39 k alpha beta) v r.2 i) ->
        ∀ r ∈ c39,
          evalFinWordVec 42 2 (bndParamMat2DC39 k alpha beta) v r.1 ⟨0, by decide⟩ =
            evalFinWordVec 42 2 (bndParamMat2DC39 k alpha beta) v r.2 ⟨0, by decide⟩)) ∧
    (∀ (k alpha beta : Nat), k ≥ 2 -> alpha ≥ 1 -> beta ≥ 1 ->
      (∀ r ∈ c39, ∀ i j : Fin 2,
        evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 k alpha beta) r.1 i j ≥
          evalFinWordMat 42 2 (coupledBTRTopRowMat2DC39 k alpha beta) r.2 i j) ∧
      (∀ v : Fin 42 -> Fin 2 -> Nat,
        (∀ r ∈ c39, ∀ i : Fin 2,
          evalFinWordVec 42 2 (coupledBTRTopRowMat2DC39 k alpha beta) v r.1 i ≥
            evalFinWordVec 42 2 (coupledBTRTopRowMat2DC39 k alpha beta) v r.2 i) ->
        ∀ r ∈ c39,
          evalFinWordVec 42 2 (coupledBTRTopRowMat2DC39 k alpha beta) v r.1 ⟨0, by decide⟩ =
            evalFinWordVec 42 2 (coupledBTRTopRowMat2DC39 k alpha beta) v r.2 ⟨0, by decide⟩)) ∧
    (∀ (k alpha beta : Nat), k ≥ 2 -> alpha ≥ 1 -> beta ≥ 1 ->
      (∀ r ∈ c78, ∀ i j : Fin 2,
        evalFinWordMat 84 2 (coupledBTRTopRowMat2DC78 k alpha beta) r.1 i j ≥
          evalFinWordMat 84 2 (coupledBTRTopRowMat2DC78 k alpha beta) r.2 i j) ∧
      (∀ v : Fin 84 -> Fin 2 -> Nat,
        (∀ r ∈ c78, ∀ i : Fin 2,
          evalFinWordVec 84 2 (coupledBTRTopRowMat2DC78 k alpha beta) v r.1 i ≥
            evalFinWordVec 84 2 (coupledBTRTopRowMat2DC78 k alpha beta) v r.2 i) ->
        ∀ r ∈ c78,
          evalFinWordVec 84 2 (coupledBTRTopRowMat2DC78 k alpha beta) v r.1 ⟨0, by decide⟩ =
            evalFinWordVec 84 2 (coupledBTRTopRowMat2DC78 k alpha beta) v r.2 ⟨0, by decide⟩)) := by
  dsimp only
  have hr_indep := twosided_c39_c78_nonuniform_mixed_zerodiag_tr_impossibility.2.1.1 2
  have hw15_param := param_mixed_zerodiag_t_coupled_d2_farkas_lock.2
  rw [c39_eq_fastRules_w16] at hr_indep hw15_param ⊢
  rw [c78_eq_fastRules_w16]
  rcases coupled_c39_c78_shape_and_witness_certs with
    ⟨hshape39, hshape78, hc78_proj, hst20, hst11, hst22, hw15_exc_fast⟩
  have hw15_exc :
      w15FarkasLhsOnCoupled (basisVec2D 42 ⟨17, by decide⟩ ⟨1, by decide⟩) c39FastRulesW16 -
        w15FarkasRhsOnCoupled (basisVec2D 42 ⟨17, by decide⟩ ⟨1, by decide⟩) c39FastRulesW16 = 13 := by
    dsimp only at hw15_exc_fast
    rw [w15FarkasFastDiff_eq] at hw15_exc_fast
    exact hw15_exc_fast
  refine ⟨⟨hst20, hst11, hst22, rfl, rfl, rfl, rfl, hw15_exc⟩, ?_, ?_, ?_⟩
  · -- Part 2: `bndParamMat2DC39 k alpha beta` on `c39`:
    intro k alpha beta hk2 ha1 hb1
    refine ⟨(weak_mat_orientation_3param_cones_w16 k alpha beta (by omega) ha1 hb1).1, ?_⟩
    intro v hv_weak
    have hout_eq : ∀ s : Fin 42, (s.val < 6 ∨ s.val ≥ 12) ->
        ∀ i j : Fin 2, bndParamMat2DC39 k alpha beta s i j = paramMat2DC39 alpha beta s i j := by
      intro s hs i j
      have hn6 : (s.val == 6) = false := beq_false_of_ne (by omega)
      have hn9 : (s.val == 9) = false := beq_false_of_ne (by omega)
      unfold bndParamMat2DC39 paramMat2DC39
      rcases (by have := i.isLt; omega : i.val = 0 ∨ i.val = 1) with hi | hi <;>
      rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1) with hj | hj <;>
      simp only [hi, hj, hn6, hn9]; all_goals rfl
    have hv_p := hr_indep (bndParamMat2DC39 k alpha beta) (paramMat2DC39 alpha beta) v hout_eq
    have hweak_p : ∀ r ∈ c39FastRulesW16, ∀ i : Fin 2,
        evalFinWordVec 42 2 (paramMat2DC39 alpha beta) v r.1 i ≥
          evalFinWordVec 42 2 (paramMat2DC39 alpha beta) v r.2 i := by
      intro r hr i
      rcases hv_p r hr i with ⟨e1, e2⟩
      rw [← e1, ← e2]; exact hv_weak r hr i
    have heq_p := (hw15_param alpha beta ha1 hb1).2 v hweak_p
    intro r hr
    rcases hv_p r hr ⟨0, by decide⟩ with ⟨e1, e2⟩
    rw [e1, e2, heq_p r hr]
  · -- Part 3: `coupledBTRTopRowMat2DC39 k alpha beta` on `c39` (7-rule parameterized Farkas syzygy):
    intro k alpha beta hk2 ha1 hb1
    refine ⟨(weak_mat_orientation_3param_cones_w16 k alpha beta (by omega) ha1 hb1).2, ?_⟩
    intro v hv_weak
    exact coupled_farkas_zero_strict_proj_w16 42 id farkasMu0CoupledC39 farkasMu1CoupledC39
      c39FastRulesW16 hshape39 coupled_c39_farkas_b0_cert coupled_c39_farkas_b1_cert
      k alpha beta v hv_weak
  · -- Part 4: `coupledBTRTopRowMat2DC78 k alpha beta` on `c78` (14-rule asymmetric Farkas syzygy):
    intro k alpha beta hk2 ha1 hb1
    have hw39 := (weak_mat_orientation_3param_cones_w16 k alpha beta (by omega) ha1 hb1).2
    have hw78 : ∀ r ∈ c78FastRulesW16, ∀ i j : Fin 2,
        evalFinWordMat 84 2 (coupledBTRTopRowMat2DC78 k alpha beta) r.1 i j ≥
          evalFinWordMat 84 2 (coupledBTRTopRowMat2DC78 k alpha beta) r.2 i j := by
      intro r hr i j
      rw [evalFinWordMat_proj84To42_w16 k alpha beta r.1 i j,
          evalFinWordMat_proj84To42_w16 k alpha beta r.2 i j]
      rcases List.any_eq_true.mp (List.all_eq_true.mp hc78_proj r hr) with ⟨r39, hr39, hbeq⟩
      have heq_pair := beq_iff_eq.mp hbeq
      have heq1 : r39.1 = r.1.map projSym84To42 := congrArg Prod.fst heq_pair
      have heq2 : r39.2 = r.2.map projSym84To42 := congrArg Prod.snd heq_pair
      rw [← heq1, ← heq2]
      exact hw39 r39 hr39 i j
    refine ⟨hw78, ?_⟩
    intro v hv_weak
    exact coupled_farkas_zero_strict_proj_w16 84 projSym84To42 farkasMu0CoupledC78 farkasMu1CoupledC78
      c78FastRulesW16 hshape78 coupled_c78_farkas_b0_cert coupled_c78_farkas_b1_cert
      k alpha beta v hv_weak

-- ----------------------------------------------------------------------------
-- Section 1C: Unconditional `1..15`-Cycle Freedom Across ALL `DP2` Words &
--             3-Block `.R`-Carrying `leftAnchoredDP2Step` Cycle Locks (`W16_H1`)
-- ----------------------------------------------------------------------------

private def syrStepW16 (n : Nat) : Nat := core2 (3 * n + 1)

private def syrIterW16 : Nat -> Nat -> Nat
  | 0, n => n
  | k + 1, n => syrIterW16 k (syrStepW16 n)

private theorem syrIterW16_add :
    ∀ (a b n : Nat), syrIterW16 (a + b) n = syrIterW16 b (syrIterW16 a n)
  | 0, _, _ => by rw [Nat.zero_add]; rfl
  | a + 1, b, n => by rw [Nat.succ_add]; exact syrIterW16_add a b (syrStepW16 n)

set_option maxRecDepth 65536 in
private theorem no_small_odd_syr_cycles_11_to_15 :
    ∀ (r : Fin 16) (k : Fin 15),
      11 ≤ r.val -> syrIterW16 r.val (2 * k.val + 3) ≠ 2 * k.val + 3 := by decide

private theorem dp2AnnotatedChain_syr_and_ge33_bound_w16 :
    ∀ (shifts : List Nat) (u0 ur : List MixedSRSSym),
      dp2AnnotatedChain u0 shifts ur ->
      dp2GlobalOddVal ur = syrIterW16 shifts.length (dp2GlobalOddVal u0) ∧
      ((∃ n : Nat, 3 ≤ n ∧ n ≤ 31 ∧ n % 2 = 1 ∧
          ∃ i : Nat, i ≤ shifts.length ∧
            syrIterW16 i (dp2GlobalOddVal u0) = n ∧
            dp2GlobalOddVal ur = syrIterW16 (shifts.length - i) n) ∨
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
    have hsyr_eq : syrStepW16 (dp2GlobalOddVal u0) = dp2GlobalOddVal w := by
      unfold syrStepW16
      rw [← hsyr_step, core2_pow2_mul a (dp2GlobalOddVal w) hNw_pos hNw_odd]
    rcases dp2AnnotatedChain_syr_and_ge33_bound_w16 rest w ur htl with ⟨ih_syr, ih_disj⟩
    have hiter_tot : dp2GlobalOddVal ur = syrIterW16 (rest.length + 1) (dp2GlobalOddVal u0) := by
      simp only [syrIterW16, hsyr_eq]; exact ih_syr
    simp only [List.length_cons, dp2ShiftSum]
    refine ⟨hiter_tot, ?_⟩
    by_cases hle31 : dp2GlobalOddVal u0 ≤ 31
    · left
      exact ⟨dp2GlobalOddVal u0, hNu_ge3, hle31, hNu_odd, 0, Nat.zero_le _, rfl, hiter_tot⟩
    · rcases ih_disj with ⟨n, hn3, hn31, hno, i, hi_le, hi_eq, hur_eq⟩ | ih_ge33
      · left
        refine ⟨n, hn3, hn31, hno, i + 1, Nat.succ_le_succ hi_le, ?_, ?_⟩
        · simp only [syrIterW16, hsyr_eq]; exact hi_eq
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

private theorem dp2AnnotatedChain_split_w16 :
    ∀ (xs ys : List Nat) (u0 uz : List MixedSRSSym),
      dp2AnnotatedChain u0 (xs ++ ys) uz ->
      ∃ um : List MixedSRSSym, dp2AnnotatedChain u0 xs um ∧ dp2AnnotatedChain um ys uz
  | [], ys, u0, uz, h => ⟨u0, rfl, h⟩
  | x :: xtl, ys, u0, uz, ⟨hx, w, hst, hsyr, htl⟩ => by
    rcases dp2AnnotatedChain_split_w16 xtl ys w uz htl with ⟨um, h1, h2⟩
    exact ⟨um, ⟨hx, w, hst, hsyr, h1⟩, h2⟩

/--
  Theorem W16.1c (`leftAnchoredDP2_no_1_to_15_cycles_and_three_block_locks`,
  `zero custom axioms`):
  Unconditional `1..15`-Cycle Freedom Across ALL `DP2` Words, `M1` `(r = 11, A = 18)`
  `175099 / 84997` Carry Separation, & 3-Block `.R`-Carrying `leftAnchoredDP2Step` Cycle Locks
  (`w_1 + w_2 + w_3 ≥ 16`, Exact 3-Block `dp2IterCarry` & `broxSpiralCarry` Resultant, Coupled
  `D * q_0` & `D` 2-Pivot Archimedean Squeezes, Equal-Shift `a_1 = a_2 = a_3 -> a_1 ≥ 4` Lock,
  Symmetric `17 * 2^{w_1} - 1` Collapse, Even-Shift `3 * 2^{w_j} - 1` & Odd-Weight Mod-4
  `75 * 2^{w_j} - 1` All-Vertex Floors, & Balanced `(17, 2, 17, 2, 17, 26)` `DP2` Exclusion,
  `Branch P4.3`, witness `M1_DP2_11CYCLE_175099_OVER_84997`, `W16_H1`).
-/
theorem leftAnchoredDP2_no_1_to_15_cycles_and_three_block_locks :
    (∀ w1 a1 w2 a2 w3 a3 : Nat, w1 ≥ 1 -> w2 ≥ 1 -> w3 ≥ 1 ->
      dp2IterCarry ((List.replicate (w1 - 1) 1 ++ [1 + a1]) ++
                    (List.replicate (w2 - 1) 1 ++ [1 + a2]) ++
                    (List.replicate (w3 - 1) 1 ++ [1 + a3])) =
        3 ^ (w2 + w3) * (3 ^ w1 - 2 ^ w1) +
        3 ^ w3 * 2 ^ (w1 + a1) * (3 ^ w2 - 2 ^ w2) +
        2 ^ (w1 + a1 + w2 + a2) * (3 ^ w3 - 2 ^ w3)) ∧
    ((∀ (r : Nat) (u : List MixedSRSSym),
        1 ≤ r -> r ≤ 15 -> ¬ dp2StepIter r u u) ∧
     (dp2IterCarry (List.replicate 10 1 ++ [8]) = 175099 ∧
      2 ^ 18 - 3 ^ 11 = 84997 ∧
      175099 % 84997 = 5105)) ∧
    (∀ (w1 a1 w2 a2 w3 a3 : Nat) (u0 : List MixedSRSSym),
      w1 ≥ 1 -> a1 ≥ 1 -> w2 ≥ 1 -> a2 ≥ 1 -> w3 ≥ 1 -> a3 ≥ 1 ->
      let blk1 := List.replicate (w1 - 1) 1 ++ [1 + a1]
      let blk2 := List.replicate (w2 - 1) 1 ++ [1 + a2]
      let blk3 := List.replicate (w3 - 1) 1 ++ [1 + a3]
      let W := w1 + w2 + w3
      let K := w1 + a1 + w2 + a2 + w3 + a3
      let D := 2 ^ K - 3 ^ W
      dp2AnnotatedChain u0 (blk1 ++ blk2 ++ blk3) u0 ->
      w1 + w2 + w3 ≥ 16 ∧
      3 ^ W < 2 ^ K ∧
      (∃ u1 u2 : List MixedSRSSym,
        dp2AnnotatedChain u0 blk1 u1 ∧
        dp2AnnotatedChain u1 blk2 u2 ∧
        dp2AnnotatedChain u2 blk3 u0 ∧
        let q0 := (dp2GlobalOddVal u0 + 1) / 2 ^ w1
        let q1 := (dp2GlobalOddVal u1 + 1) / 2 ^ w2
        let q2 := (dp2GlobalOddVal u2 + 1) / 2 ^ w3
        2 ^ w1 ∣ (dp2GlobalOddVal u0 + 1) ∧
        2 ^ w2 ∣ (dp2GlobalOddVal u1 + 1) ∧
        2 ^ w3 ∣ (dp2GlobalOddVal u2 + 1) ∧
        q0 ≥ 1 ∧ q1 ≥ 1 ∧ q2 ≥ 1 ∧
        q0 % 2 = 1 ∧ q1 % 2 = 1 ∧ q2 % 2 = 1 ∧
        2 ^ (a1 + w2) * q1 = 3 ^ w1 * q0 + (2 ^ a1 - 1) ∧
        2 ^ (a2 + w3) * q2 = 3 ^ w2 * q1 + (2 ^ a2 - 1) ∧
        2 ^ (a3 + w1) * q0 = 3 ^ w3 * q2 + (2 ^ a3 - 1) ∧
        D * q0 = broxSpiralCarry [(w1, a1), (w2, a2), (w3, a3)] ∧
        D * q0 + 3 ^ (w2 + w3) ≤
          3 ^ (w2 + w3) * 2 ^ a1 + 2 ^ (a1 + w2) * 3 ^ w3 * (2 ^ (a2 + a3) - 1) ∧
        D + 3 ^ (w2 + w3) ≤
          3 ^ (w2 + w3) * 2 ^ a1 + 2 ^ (a1 + w2) * 3 ^ w3 * (2 ^ (a2 + a3) - 1) ∧
        (a1 = a2 ∧ a2 = a3 ->
          a1 ≥ 4 ∧
          D * q0 = (2 ^ a1 - 1) * (3 ^ (w2 + w3) + 2 ^ (a1 + w2) * 3 ^ w3 + 2 ^ (2 * a1 + w2 + w3))) ∧
        (w1 = w2 ∧ w2 = w3 ∧ a1 = a2 ∧ a2 = a3 ->
          w1 ≥ 13 ∧ a1 ≥ 8 ∧ q0 = q1 ∧ q1 = q2 ∧ dp2GlobalOddVal u0 ≥ 17 * 2 ^ w1 - 1) ∧
        (2 ∣ a1 ∧ 2 ∣ a2 ∧ 2 ∣ a3 ->
          3 ∣ q0 ∧ 3 ∣ q1 ∧ 3 ∣ q2 ∧
          dp2GlobalOddVal u0 ≥ 3 * 2 ^ w1 - 1 ∧
          dp2GlobalOddVal u1 ≥ 3 * 2 ^ w2 - 1 ∧
          dp2GlobalOddVal u2 ≥ 3 * 2 ^ w3 - 1) ∧
        (W % 2 = 1 ∧ 4 ∣ a1 ∧ 4 ∣ a2 ∧ 4 ∣ a3 ->
          15 ∣ q0 ∧ 15 ∣ q1 ∧ 15 ∣ q2 ∧
          q0 ≥ 75 ∧ q1 ≥ 75 ∧ q2 ≥ 75 ∧
          dp2GlobalOddVal u0 ≥ 75 * 2 ^ w1 - 1 ∧
          dp2GlobalOddVal u1 ≥ 75 * 2 ^ w2 - 1 ∧
          dp2GlobalOddVal u2 ≥ 75 * 2 ^ w3 - 1))) ∧
    (∀ u0 : List MixedSRSSym,
      ¬ dp2AnnotatedChain u0
        ((List.replicate 16 1 ++ [3]) ++ (List.replicate 16 1 ++ [3]) ++ (List.replicate 16 1 ++ [27])) u0) := by
  have happ := leftAnchoredDP2_no_1_to_10_cycles_and_two_block_locks.1.1
  have h2blk_car := leftAnchoredDP2_no_1_to_10_cycles_and_two_block_locks.1.2
  have hno_1_10 := leftAnchoredDP2_no_1_to_10_cycles_and_two_block_locks.2.1.1
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
  have hcar_3blk : ∀ w1 a1 w2 a2 w3 a3 : Nat, w1 ≥ 1 -> w2 ≥ 1 -> w3 ≥ 1 ->
      dp2IterCarry ((List.replicate (w1 - 1) 1 ++ [1 + a1]) ++
                    (List.replicate (w2 - 1) 1 ++ [1 + a2]) ++
                    (List.replicate (w3 - 1) 1 ++ [1 + a3])) =
        3 ^ (w2 + w3) * (3 ^ w1 - 2 ^ w1) +
        3 ^ w3 * 2 ^ (w1 + a1) * (3 ^ w2 - 2 ^ w2) +
        2 ^ (w1 + a1 + w2 + a2) * (3 ^ w3 - 2 ^ w3) := by
    intro w1 a1 w2 a2 w3 a3 hw1 hw2 hw3
    rw [(happ (_ ++ _) _).2,
        h2blk_car w1 a1 w2 a2 hw1 hw2,
        (hsum_blk w3 a3 hw3).1,
        (happ _ _).1, (hsum_blk w1 a1 hw1).2, (hsum_blk w2 a2 hw2).2,
        (leftAnchoredDP2_iterated_affine_carry_and_cycle_laws.2.2.2 w3 (1 + a3) hw3).1,
        Nat.mul_add (3 ^ w3), ← Nat.mul_assoc (3 ^ w3) (3 ^ w2),
        ← Nat.pow_add 3 w3 w2, Nat.add_comm w3 w2,
        ← Nat.mul_assoc (3 ^ w3), ← Nat.add_assoc (w1 + a1) w2 a2]
  have hno_1_15 : ∀ (r : Nat) (u : List MixedSRSSym),
      1 ≤ r -> r ≤ 15 -> ¬ dp2StepIter r u u := by
    intro r u hr1 hr15 hiter
    by_cases hr10 : r ≤ 10
    · exact hno_1_10 r u hr1 hr10 hiter
    · rcases (leftAnchoredDP2_iterated_affine_carry_and_cycle_laws.1 r u u hiter).2 with
        ⟨shifts, hlen, _, hann, _, _⟩
      rcases leftAnchoredDP2_iterated_affine_carry_and_cycle_laws.2.1.1 shifts u (by omega) hann with
        ⟨hlt, _, _, _⟩
      rw [hlen] at hlt
      rcases dp2AnnotatedChain_syr_and_ge33_bound_w16 shifts u u hann with ⟨_, hsmall | hge33⟩
      · rcases hsmall with ⟨n, hn3, hn31, hno, i, hi_le, hi_eq, hur_eq⟩
        rw [hlen] at hi_le hur_eq
        have hcyc_n : syrIterW16 r n = n := by
          rw [show r = (r - i) + i by omega, syrIterW16_add (r - i) i n, ← hur_eq, hi_eq]
        let k := (n - 3) / 2
        have hk_lt : k < 15 := by dsimp [k]; omega
        have hn_eq : n = 2 * k + 3 := by dsimp [k]; omega
        rw [hn_eq] at hcyc_n
        exact no_small_odd_syr_cycles_11_to_15 ⟨r, by omega⟩ ⟨k, hk_lt⟩ (by dsimp; omega) hcyc_n
      · rw [hlen] at hge33
        have hNu_pos : dp2GlobalOddVal u > 0 := by unfold dp2GlobalOddVal; omega
        have h33_le : 33 ^ r * 2 ^ dp2ShiftSum shifts ≤ 100 ^ r :=
          nat_mul_le_cancel_right_w5 (dp2GlobalOddVal u) _ _ hNu_pos hge33
        let A := dp2ShiftSum shifts
        change 3 ^ r < 2 ^ A at hlt
        change 33 ^ r * 2 ^ A ≤ 100 ^ r at h33_le
        rcases (by omega : r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15) with
          rfl | rfl | rfl | rfl | rfl
        · by_cases hA : A ≤ 17
          · exact absurd (Nat.lt_of_lt_of_le hlt (nat_pow_mono_exp_pos 2 A 17 (by decide) hA)) (by decide)
          · have hp := Nat.mul_le_mul_left (33 ^ 11) (nat_pow_mono_exp_pos 2 18 A (by decide) (by omega))
            exact absurd (Nat.le_trans hp h33_le) (by decide)
        · by_cases hA : A ≤ 19
          · exact absurd (Nat.lt_of_lt_of_le hlt (nat_pow_mono_exp_pos 2 A 19 (by decide) hA)) (by decide)
          · have hp := Nat.mul_le_mul_left (33 ^ 12) (nat_pow_mono_exp_pos 2 20 A (by decide) (by omega))
            exact absurd (Nat.le_trans hp h33_le) (by decide)
        · by_cases hA : A ≤ 20
          · exact absurd (Nat.lt_of_lt_of_le hlt (nat_pow_mono_exp_pos 2 A 20 (by decide) hA)) (by decide)
          · have hp := Nat.mul_le_mul_left (33 ^ 13) (nat_pow_mono_exp_pos 2 21 A (by decide) (by omega))
            exact absurd (Nat.le_trans hp h33_le) (by decide)
        · by_cases hA : A ≤ 22
          · exact absurd (Nat.lt_of_lt_of_le hlt (nat_pow_mono_exp_pos 2 A 22 (by decide) hA)) (by decide)
          · have hp := Nat.mul_le_mul_left (33 ^ 14) (nat_pow_mono_exp_pos 2 23 A (by decide) (by omega))
            exact absurd (Nat.le_trans hp h33_le) (by decide)
        · by_cases hA : A ≤ 23
          · exact absurd (Nat.lt_of_lt_of_le hlt (nat_pow_mono_exp_pos 2 A 23 (by decide) hA)) (by decide)
          · have hp := Nat.mul_le_mul_left (33 ^ 15) (nat_pow_mono_exp_pos 2 24 A (by decide) (by omega))
            exact absurd (Nat.le_trans hp h33_le) (by decide)
  -- 3-Block `.R`-carrying `leftAnchoredDP2Step` laws:
  have h3blk_main : ∀ (w1 a1 w2 a2 w3 a3 : Nat) (u0 : List MixedSRSSym),
      w1 ≥ 1 -> a1 ≥ 1 -> w2 ≥ 1 -> a2 ≥ 1 -> w3 ≥ 1 -> a3 ≥ 1 ->
      let blk1 := List.replicate (w1 - 1) 1 ++ [1 + a1]
      let blk2 := List.replicate (w2 - 1) 1 ++ [1 + a2]
      let blk3 := List.replicate (w3 - 1) 1 ++ [1 + a3]
      let W := w1 + w2 + w3
      let K := w1 + a1 + w2 + a2 + w3 + a3
      let D := 2 ^ K - 3 ^ W
      dp2AnnotatedChain u0 (blk1 ++ blk2 ++ blk3) u0 ->
      w1 + w2 + w3 ≥ 16 ∧
      3 ^ W < 2 ^ K ∧
      (∃ u1 u2 : List MixedSRSSym,
        dp2AnnotatedChain u0 blk1 u1 ∧
        dp2AnnotatedChain u1 blk2 u2 ∧
        dp2AnnotatedChain u2 blk3 u0 ∧
        let q0 := (dp2GlobalOddVal u0 + 1) / 2 ^ w1
        let q1 := (dp2GlobalOddVal u1 + 1) / 2 ^ w2
        let q2 := (dp2GlobalOddVal u2 + 1) / 2 ^ w3
        2 ^ w1 ∣ (dp2GlobalOddVal u0 + 1) ∧
        2 ^ w2 ∣ (dp2GlobalOddVal u1 + 1) ∧
        2 ^ w3 ∣ (dp2GlobalOddVal u2 + 1) ∧
        q0 ≥ 1 ∧ q1 ≥ 1 ∧ q2 ≥ 1 ∧
        q0 % 2 = 1 ∧ q1 % 2 = 1 ∧ q2 % 2 = 1 ∧
        2 ^ (a1 + w2) * q1 = 3 ^ w1 * q0 + (2 ^ a1 - 1) ∧
        2 ^ (a2 + w3) * q2 = 3 ^ w2 * q1 + (2 ^ a2 - 1) ∧
        2 ^ (a3 + w1) * q0 = 3 ^ w3 * q2 + (2 ^ a3 - 1) ∧
        D * q0 = broxSpiralCarry [(w1, a1), (w2, a2), (w3, a3)] ∧
        D * q0 + 3 ^ (w2 + w3) ≤
          3 ^ (w2 + w3) * 2 ^ a1 + 2 ^ (a1 + w2) * 3 ^ w3 * (2 ^ (a2 + a3) - 1) ∧
        D + 3 ^ (w2 + w3) ≤
          3 ^ (w2 + w3) * 2 ^ a1 + 2 ^ (a1 + w2) * 3 ^ w3 * (2 ^ (a2 + a3) - 1) ∧
        (a1 = a2 ∧ a2 = a3 ->
          a1 ≥ 4 ∧
          D * q0 = (2 ^ a1 - 1) * (3 ^ (w2 + w3) + 2 ^ (a1 + w2) * 3 ^ w3 + 2 ^ (2 * a1 + w2 + w3))) ∧
        (w1 = w2 ∧ w2 = w3 ∧ a1 = a2 ∧ a2 = a3 ->
          w1 ≥ 13 ∧ a1 ≥ 8 ∧ q0 = q1 ∧ q1 = q2 ∧ dp2GlobalOddVal u0 ≥ 17 * 2 ^ w1 - 1) ∧
        (2 ∣ a1 ∧ 2 ∣ a2 ∧ 2 ∣ a3 ->
          3 ∣ q0 ∧ 3 ∣ q1 ∧ 3 ∣ q2 ∧
          dp2GlobalOddVal u0 ≥ 3 * 2 ^ w1 - 1 ∧
          dp2GlobalOddVal u1 ≥ 3 * 2 ^ w2 - 1 ∧
          dp2GlobalOddVal u2 ≥ 3 * 2 ^ w3 - 1) ∧
        (W % 2 = 1 ∧ 4 ∣ a1 ∧ 4 ∣ a2 ∧ 4 ∣ a3 ->
          15 ∣ q0 ∧ 15 ∣ q1 ∧ 15 ∣ q2 ∧
          q0 ≥ 75 ∧ q1 ≥ 75 ∧ q2 ≥ 75 ∧
          dp2GlobalOddVal u0 ≥ 75 * 2 ^ w1 - 1 ∧
          dp2GlobalOddVal u1 ≥ 75 * 2 ^ w2 - 1 ∧
          dp2GlobalOddVal u2 ≥ 75 * 2 ^ w3 - 1)) := by
    intro w1 a1 w2 a2 w3 a3 u0 hw1 ha1 hw2 ha2 hw3 ha3
    dsimp only
    intro hann
    have hann_to_iter : ∀ (sh : List Nat) (x y : List MixedSRSSym),
        dp2AnnotatedChain x sh y -> dp2StepIter sh.length x y := by
      intro sh; induction sh with
      | nil => intro x y h0; exact h0
      | cons s stl ih =>
        intro x y ⟨_, z, hst, _, htl⟩
        exact ⟨z, hst, ih z y htl⟩
    let blk1 := List.replicate (w1 - 1) 1 ++ [1 + a1]
    let blk2 := List.replicate (w2 - 1) 1 ++ [1 + a2]
    let blk3 := List.replicate (w3 - 1) 1 ++ [1 + a3]
    have hlen123 : (blk1 ++ blk2 ++ blk3).length = w1 + w2 + w3 := by
      rw [List.length_append, List.length_append,
          (hsum_blk w1 a1 hw1).1, (hsum_blk w2 a2 hw2).1, (hsum_blk w3 a3 hw3).1]
    have hsum123 : dp2ShiftSum (blk1 ++ blk2 ++ blk3) = w1 + a1 + w2 + a2 + w3 + a3 := by
      rw [(happ (blk1 ++ blk2) blk3).1, (happ blk1 blk2).1,
          (hsum_blk w1 a1 hw1).2, (hsum_blk w2 a2 hw2).2, (hsum_blk w3 a3 hw3).2]; omega
    have hw123_ge16 : w1 + w2 + w3 ≥ 16 := by
      by_cases hle15 : w1 + w2 + w3 ≤ 15
      · exfalso
        have hit := hann_to_iter (blk1 ++ blk2 ++ blk3) u0 u0 hann
        rw [hlen123] at hit
        exact hno_1_15 (w1 + w2 + w3) u0 (by omega) hle15 hit
      · omega
    rcases leftAnchoredDP2_iterated_affine_carry_and_cycle_laws.2.1.1 (blk1 ++ blk2 ++ blk3) u0
      (by rw [hlen123]; omega) hann with ⟨hlt, _, _, _⟩
    rw [hlen123, hsum123] at hlt
    rcases dp2AnnotatedChain_split_w16 (blk1 ++ blk2) blk3 u0 u0 hann with ⟨u2, hann12, hann3⟩
    rcases dp2AnnotatedChain_split_w16 blk1 blk2 u0 u2 hann12 with ⟨u1, hann1, hann2⟩
    have hblock_step : ∀ (w a : Nat) (x y : List MixedSRSSym), w ≥ 1 ->
        dp2AnnotatedChain x (List.replicate (w - 1) 1 ++ [1 + a]) y ->
        2 ^ w ∣ (dp2GlobalOddVal x + 1) ∧
        2 ^ a * dp2GlobalOddVal y + 1 = 3 ^ w * ((dp2GlobalOddVal x + 1) / 2 ^ w) := by
      intro w a x y hw hch
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
      have heq_hom := hhom _ x y hch
      rw [(hsum_blk w a hw).1, (hsum_blk w a hw).2,
          (leftAnchoredDP2_iterated_affine_carry_and_cycle_laws.2.2.2 w (1 + a) hw).1] at heq_hom
      have hle_23 : 2 ^ w ≤ 3 ^ w := pow_mono_base_w16c 2 3 (by decide) w
      have hbal : 2 ^ w * (2 ^ a * dp2GlobalOddVal y + 1) = 3 ^ w * (dp2GlobalOddVal x + 1) := by
        rw [Nat.pow_add 2 w a, Nat.mul_assoc] at heq_hom
        rw [Nat.mul_add (2 ^ w), Nat.mul_one, Nat.mul_add (3 ^ w), Nat.mul_one]
        omega
      have hcop : Nat.Coprime (2 ^ w) (3 ^ w) := ((by decide : Nat.Coprime 2 3).pow_left w).pow_right w
      rcases hcop.dvd_of_dvd_mul_left ⟨2 ^ a * dp2GlobalOddVal y + 1, hbal.symm⟩ with ⟨q, hq⟩
      have hp2_pos : 0 < 2 ^ w := nat_pow_pos_of_pos 2 (by decide) w
      have hdiv : (dp2GlobalOddVal x + 1) / 2 ^ w = q := by
        rw [hq, Nat.mul_comm (2 ^ w) q, Nat.mul_div_cancel q hp2_pos]
      have hmul_q : 2 ^ w * (2 ^ a * dp2GlobalOddVal y + 1) = 2 ^ w * (3 ^ w * q) := by
        rw [hbal, hq]; ac_rfl
      exact ⟨⟨q, hq⟩, by rw [hdiv]; exact Nat.eq_of_mul_eq_mul_left hp2_pos hmul_q⟩
    rcases hblock_step w1 a1 u0 u1 hw1 hann1 with ⟨hdvd0, hsyr0⟩
    rcases hblock_step w2 a2 u1 u2 hw2 hann2 with ⟨hdvd1, hsyr1⟩
    rcases hblock_step w3 a3 u2 u0 hw3 hann3 with ⟨hdvd2, hsyr2⟩
    let q0 := (dp2GlobalOddVal u0 + 1) / 2 ^ w1
    let q1 := (dp2GlobalOddVal u1 + 1) / 2 ^ w2
    let q2 := (dp2GlobalOddVal u2 + 1) / 2 ^ w3
    have hN0_eq : dp2GlobalOddVal u0 + 1 = 2 ^ w1 * q0 := (Nat.mul_div_cancel' hdvd0).symm
    have hN1_eq : dp2GlobalOddVal u1 + 1 = 2 ^ w2 * q1 := (Nat.mul_div_cancel' hdvd1).symm
    have hN2_eq : dp2GlobalOddVal u2 + 1 = 2 ^ w3 * q2 := (Nat.mul_div_cancel' hdvd2).symm
    have hq0_pos : q0 ≥ 1 := by cases hq : q0 with | zero => rw [hq, Nat.mul_zero] at hN0_eq; omega | succ _ => omega
    have hq1_pos : q1 ≥ 1 := by cases hq : q1 with | zero => rw [hq, Nat.mul_zero] at hN1_eq; omega | succ _ => omega
    have hq2_pos : q2 ≥ 1 := by cases hq : q2 with | zero => rw [hq, Nat.mul_zero] at hN2_eq; omega | succ _ => omega
    have h2a1_pos : 2 ^ a1 ≥ 1 := nat_pow_pos_of_pos 2 (by decide) a1
    have h2a2_pos : 2 ^ a2 ≥ 1 := nat_pow_pos_of_pos 2 (by decide) a2
    have h2a3_pos : 2 ^ a3 ≥ 1 := nat_pow_pos_of_pos 2 (by decide) a3
    have hbrox1 : 2 ^ (a1 + w2) * q1 = 3 ^ w1 * q0 + (2 ^ a1 - 1) := by
      have hm : 2 ^ a1 * (dp2GlobalOddVal u1 + 1) = 2 ^ (a1 + w2) * q1 := by rw [hN1_eq, Nat.pow_add]; ac_rfl
      rw [Nat.mul_add, Nat.mul_one] at hm; change 2 ^ a1 * dp2GlobalOddVal u1 + 1 = 3 ^ w1 * q0 at hsyr0; omega
    have hbrox2 : 2 ^ (a2 + w3) * q2 = 3 ^ w2 * q1 + (2 ^ a2 - 1) := by
      have hm : 2 ^ a2 * (dp2GlobalOddVal u2 + 1) = 2 ^ (a2 + w3) * q2 := by rw [hN2_eq, Nat.pow_add]; ac_rfl
      rw [Nat.mul_add, Nat.mul_one] at hm; change 2 ^ a2 * dp2GlobalOddVal u2 + 1 = 3 ^ w2 * q1 at hsyr1; omega
    have hbrox3 : 2 ^ (a3 + w1) * q0 = 3 ^ w3 * q2 + (2 ^ a3 - 1) := by
      have hm : 2 ^ a3 * (dp2GlobalOddVal u0 + 1) = 2 ^ (a3 + w1) * q0 := by rw [hN0_eq, Nat.pow_add]; ac_rfl
      rw [Nat.mul_add, Nat.mul_one] at hm; change 2 ^ a3 * dp2GlobalOddVal u0 + 1 = 3 ^ w3 * q2 at hsyr2; omega
    have hodd_of_brox : ∀ (a wn w q_cur q_nxt : Nat),
        a ≥ 1 -> wn ≥ 1 -> 2 ^ (a + wn) * q_nxt = 3 ^ w * q_cur + (2 ^ a - 1) -> q_cur % 2 = 1 := by
      intro a wn w q_cur q_nxt ha hwn hb
      by_cases ho : q_cur % 2 = 1
      · exact ho
      · exfalso
        have he : q_cur % 2 = 0 := by omega
        have hlhs : (2 ^ (a + wn) * q_nxt) % 2 = 0 := by
          rw [show a + wn = (a + wn - 1) + 1 by omega, Nat.pow_succ,
              Nat.mul_comm (2 ^ (a + wn - 1)) 2, Nat.mul_assoc]; omega
        have hp2a : (2 ^ a - 1) % 2 = 1 := by
          cases a with
          | zero => omega
          | succ a' =>
            have hp : 2 ^ a' ≥ 1 := pow2_pos_nat a'
            rw [Nat.pow_succ]; omega
        have hrhs : (3 ^ w * q_cur + (2 ^ a - 1)) % 2 = 1 := by
          rw [Nat.add_mod, Nat.mul_mod, he, Nat.mul_zero, hp2a]
        rw [← hb] at hrhs; omega
    have hq0_odd := hodd_of_brox a1 w2 w1 q0 q1 ha1 hw2 hbrox1
    have hq1_odd := hodd_of_brox a2 w3 w2 q1 q2 ha2 hw3 hbrox2
    have hq2_odd := hodd_of_brox a3 w1 w3 q2 q0 ha3 hw1 hbrox3
    let D := 2 ^ (w1 + a1 + w2 + a2 + w3 + a3) - 3 ^ (w1 + w2 + w3)
    have h3rot_eq : ∀ (x1 b1 x2 b2 x3 b3 r0 r1 r2 : Nat),
        3 ^ (x1 + x2 + x3) < 2 ^ (x1 + b1 + x2 + b2 + x3 + b3) ->
        2 ^ (b1 + x2) * r1 = 3 ^ x1 * r0 + (2 ^ b1 - 1) ->
        2 ^ (b2 + x3) * r2 = 3 ^ x2 * r1 + (2 ^ b2 - 1) ->
        2 ^ (b3 + x1) * r0 = 3 ^ x3 * r2 + (2 ^ b3 - 1) ->
        (2 ^ (x1 + b1 + x2 + b2 + x3 + b3) - 3 ^ (x1 + x2 + x3)) * r0 =
          broxSpiralCarry [(x1, b1), (x2, b2), (x3, b3)] := by
      intro x1 b1 x2 b2 x3 b3 r0 r1 r2 hlt_x hb1 hb2 hb3
      have hcar_def : broxSpiralCarry [(x1, b1), (x2, b2), (x3, b3)] =
          3 ^ (x2 + x3) * (2 ^ b1 - 1) +
          2 ^ (b1 + x2) * (3 ^ x3 * (2 ^ b2 - 1) + 2 ^ (b2 + x3) * (2 ^ b3 - 1)) := by
        simp [broxSpiralCarry, blockWeightSum]
      rw [hcar_def, Nat.sub_mul]
      have e1 : 2 ^ (x1 + b1 + x2 + b2 + x3 + b3) * r0 =
          2 ^ (b1 + x2) * (2 ^ (b2 + x3) * (2 ^ (b3 + x1) * r0)) := by
        rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add,
            show b1 + x2 + (b2 + x3) + (b3 + x1) = x1 + b1 + x2 + b2 + x3 + b3 by omega]
      have e2 : 2 ^ (b2 + x3) * (3 ^ x3 * r2) = 3 ^ x3 * (2 ^ (b2 + x3) * r2) := by ac_rfl
      have e3 : 2 ^ (b1 + x2) * (3 ^ x3 * (3 ^ x2 * r1)) = 3 ^ (x2 + x3) * (2 ^ (b1 + x2) * r1) := by
        rw [Nat.pow_add 3 x2 x3]; ac_rfl
      have e4 : 3 ^ (x2 + x3) * (3 ^ x1 * r0) = 3 ^ (x1 + x2 + x3) * r0 := by
        calc 3 ^ (x2 + x3) * (3 ^ x1 * r0)
            = (3 ^ x1 * 3 ^ (x2 + x3)) * r0 := by ac_rfl
          _ = 3 ^ (x1 + x2 + x3) * r0 := by rw [← Nat.pow_add, ← Nat.add_assoc]
      have hrearr :
          3 ^ (x1 + x2 + x3) * r0 + 3 ^ (x2 + x3) * (2 ^ b1 - 1) +
            2 ^ (b1 + x2) * (3 ^ x3 * (2 ^ b2 - 1)) +
            2 ^ (b1 + x2) * (2 ^ (b2 + x3) * (2 ^ b3 - 1)) =
          3 ^ (x1 + x2 + x3) * r0 +
            (3 ^ (x2 + x3) * (2 ^ b1 - 1) +
             2 ^ (b1 + x2) * (3 ^ x3 * (2 ^ b2 - 1) + 2 ^ (b2 + x3) * (2 ^ b3 - 1))) := by
        rw [Nat.mul_add (2 ^ (b1 + x2))]; omega
      rw [e1, hb3, Nat.mul_add (2 ^ (b2 + x3)), e2, hb2, Nat.mul_add (3 ^ x3),
          Nat.mul_add (2 ^ (b1 + x2)), Nat.mul_add (2 ^ (b1 + x2)), e3, hb1,
          Nat.mul_add (3 ^ (x2 + x3)), e4, hrearr, Nat.add_sub_cancel_left]
    have hq0_brox := h3rot_eq w1 a1 w2 a2 w3 a3 q0 q1 q2 hlt hbrox1 hbrox2 hbrox3
    have hq1_brox := h3rot_eq w2 a2 w3 a3 w1 a1 q1 q2 q0
      (by rw [show w2 + w3 + w1 = w1 + w2 + w3 by omega,
              show w2 + a2 + w3 + a3 + w1 + a1 = w1 + a1 + w2 + a2 + w3 + a3 by omega]; exact hlt)
      hbrox2 hbrox3 hbrox1
    have hq2_brox := h3rot_eq w3 a3 w1 a1 w2 a2 q2 q0 q1
      (by rw [show w3 + w1 + w2 = w1 + w2 + w3 by omega,
              show w3 + a3 + w1 + a1 + w2 + a2 = w1 + a1 + w2 + a2 + w3 + a3 by omega]; exact hlt)
      hbrox3 hbrox1 hbrox2
    let qs3 : List Nat := [q0, q1, q2]
    have hqs3_spec : ∀ j : Nat, j < [(w1, a1), (w2, a2), (w3, a3)].length ->
        (2 ^ blockStepSum [(w1, a1), (w2, a2), (w3, a3)] -
         3 ^ blockWeightSum [(w1, a1), (w2, a2), (w3, a3)]) * natAt qs3 j =
          broxSpiralCarry (rotBlocks j [(w1, a1), (w2, a2), (w3, a3)]) := by
      intro j hj3
      simp only [List.length_cons, List.length_nil] at hj3
      have hD_eq : 2 ^ blockStepSum [(w1, a1), (w2, a2), (w3, a3)] -
          3 ^ blockWeightSum [(w1, a1), (w2, a2), (w3, a3)] = D := by
        simp [D, blockStepSum, blockWeightSum, Nat.add_assoc]
      rw [hD_eq]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
      · exact hq0_brox
      · simpa [qs3, natAt, rotBlocks, show w2 + w3 + w1 = w1 + w2 + w3 by omega,
               show w2 + a2 + w3 + a3 + w1 + a1 = w1 + a1 + w2 + a2 + w3 + a3 by omega] using hq1_brox
      · simpa [qs3, natAt, rotBlocks, show w3 + w1 + w2 = w1 + w2 + w3 by omega,
               show w3 + a3 + w1 + a1 + w2 + a2 = w1 + a1 + w2 + a2 + w3 + a3 by omega] using hq2_brox
    rcases m_block_two_pivot_telescoping_and_2adic_quotient_boost.2.2.1
      (w1, a1) (w2, a2) [(w3, a3)] qs3 1
      (by intro b hb; simp at hb; rcases hb with rfl | rfl | rfl <;> omega)
      (by simpa [blockWeightSum, blockStepSum, Nat.add_assoc] using hlt)
      rfl hqs3_spec (Nat.one_dvd _) with ⟨h2piv_car, h2piv_raw⟩
    have h2piv_dq0 : D * q0 + 3 ^ (w2 + w3) ≤
        3 ^ (w2 + w3) * 2 ^ a1 + 2 ^ (a1 + w2) * 3 ^ w3 * (2 ^ (a2 + a3) - 1) := by
      rw [hq0_brox]
      simp only [blockWeightSum, blockStepSum, Nat.add_zero] at h2piv_car
      rw [show w2 + a2 + (w3 + a3) - (w2 + w3) = a2 + a3 by omega] at h2piv_car
      exact h2piv_car
    have h2piv_dp2 : D + 3 ^ (w2 + w3) ≤
        3 ^ (w2 + w3) * 2 ^ a1 + 2 ^ (a1 + w2) * 3 ^ w3 * (2 ^ (a2 + a3) - 1) := by
      simp only [blockWeightSum, blockStepSum, Nat.add_zero, Nat.one_mul] at h2piv_raw
      rw [show w2 + a2 + (w3 + a3) - (w2 + w3) = a2 + a3 by omega] at h2piv_raw
      simpa [D, Nat.add_assoc] using h2piv_raw
    refine ⟨hw123_ge16, hlt, u1, u2, hann1, hann2, hann3,
            hdvd0, hdvd1, hdvd2, hq0_pos, hq1_pos, hq2_pos,
            hq0_odd, hq1_odd, hq2_odd, hbrox1, hbrox2, hbrox3, hq0_brox,
            h2piv_dq0, h2piv_dp2, ?_, ?_, ?_, ?_⟩
    · -- Equal-shift `a1 = a2 = a3`:
      rintro ⟨ha12, ha23⟩
      subst ha12; subst ha23
      have ha1_ge4 : a1 ≥ 4 := by
        by_cases ha4 : a1 ≥ 4
        · exact ha4
        · exfalso
          have h512_lt : ∀ n : Nat, n ≥ 16 -> 512 * 2 ^ n < 3 ^ n := by
            intro n hn; induction n with
            | zero => omega
            | succ n' ihn =>
              by_cases hn16 : n' = 15
              · subst hn16; decide
              · have ih1 := ihn (by omega)
                rw [Nat.pow_succ 2 n', Nat.pow_succ 3 n']
                omega
          have h512 := h512_lt (w1 + w2 + w3) hw123_ge16
          have hexp_le : w1 + a1 + w2 + a1 + w3 + a1 ≤ 9 + (w1 + w2 + w3) := by omega
          have hp_le := nat_pow_mono_exp_pos 2 _ _ (by decide) hexp_le
          rw [Nat.pow_add 2 9 (w1 + w2 + w3), show (2 : Nat) ^ 9 = 512 from rfl] at hp_le
          omega
      refine ⟨ha1_ge4, ?_⟩
      rw [hq0_brox]
      simp only [broxSpiralCarry, blockWeightSum, Nat.add_zero]
      rw [Nat.mul_add (2 ^ a1 - 1), Nat.mul_add (2 ^ a1 - 1),
          Nat.mul_comm (2 ^ a1 - 1) (3 ^ (w2 + w3)),
          Nat.mul_add (2 ^ (a1 + w2)),
          ← Nat.mul_assoc (2 ^ (a1 + w2)) (2 ^ (a1 + w3)),
          ← Nat.pow_add 2 (a1 + w2) (a1 + w3),
          show a1 + w2 + (a1 + w3) = 2 * a1 + w2 + w3 by omega]
      ac_rfl
    · -- Symmetric `w1 = w2 = w3 ∧ a1 = a2 = a3`:
      rintro ⟨hw12, hw23, ha12, ha23⟩
      subst hw12; subst hw23; subst ha12; subst ha23
      have hsand : ∀ (x y z : Nat),
          2 ^ (a1 + w1) * y = 3 ^ w1 * x + (2 ^ a1 - 1) ->
          2 ^ (a1 + w1) * z = 3 ^ w1 * y + (2 ^ a1 - 1) ->
          2 ^ (a1 + w1) * x = 3 ^ w1 * z + (2 ^ a1 - 1) ->
          x ≤ y -> x ≤ z -> x = y ∧ y = z := by
        intro x y z e1 _ e3 hxy hxz
        have hm1 : 2 ^ (a1 + w1) * x ≤ 2 ^ (a1 + w1) * y := Nat.mul_le_mul_left _ hxy
        have hm2 : 3 ^ w1 * x + (2 ^ a1 - 1) ≤ 3 ^ w1 * z + (2 ^ a1 - 1) :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ hxz) _
        rw [e1] at hm1
        rw [← e3] at hm2
        have hp2_pos : 0 < 2 ^ (a1 + w1) := nat_pow_pos_of_pos 2 (by decide) (a1 + w1)
        have hp3_pos : 0 < 3 ^ w1 := pow3_pos_nat w1
        have heq_p2 : 2 ^ (a1 + w1) * x = 2 ^ (a1 + w1) * y := by rw [e1]; omega
        have heq_p3 : 3 ^ w1 * x = 3 ^ w1 * z := by omega
        have hxy_eq := Nat.eq_of_mul_eq_mul_left hp2_pos heq_p2
        have hxz_eq := Nat.eq_of_mul_eq_mul_left hp3_pos heq_p3
        exact ⟨hxy_eq, hxy_eq.symm.trans hxz_eq⟩
      have hq_all_eq : q0 = q1 ∧ q1 = q2 := by
        by_cases h01 : q0 ≤ q1
        · by_cases h02 : q0 ≤ q2
          · exact hsand q0 q1 q2 hbrox1 hbrox2 hbrox3 h01 h02
          · rcases hsand q2 q0 q1 hbrox3 hbrox1 hbrox2 (by omega) (by omega) with ⟨e20, e01⟩
            exact ⟨e01, e01.symm.trans e20.symm⟩
        · by_cases h12 : q1 ≤ q2
          · rcases hsand q1 q2 q0 hbrox2 hbrox3 hbrox1 h12 (by omega) with ⟨e12, e20⟩
            exact ⟨e20.symm.trans e12.symm, e12⟩
          · rcases hsand q2 q0 q1 hbrox3 hbrox1 hbrox2 (by omega) (by omega) with ⟨e20, e01⟩
            exact ⟨e01, e01.symm.trans e20.symm⟩
      rcases hq_all_eq with ⟨hq01, hq12⟩
      have hbrox_1b : 2 ^ (w1 + a1) * q0 = 3 ^ w1 * q0 + (2 ^ a1 - 1) := by
        rw [Nat.add_comm a1 w1, ← hq01] at hbrox1; exact hbrox1
      have hgt1 : 3 ^ w1 < 2 ^ (w1 + a1) := by
        by_cases hg : 3 ^ w1 < 2 ^ (w1 + a1)
        · exact hg
        · have hm := Nat.mul_le_mul_right q0 (by omega : 2 ^ (w1 + a1) ≤ 3 ^ w1)
          have ha2_ge : 2 ^ a1 - 1 ≥ 1 := by
            have hp : 2 ≤ 2 ^ a1 := by simpa using pow2_mono_nat ha1
            omega
          omega
      have hw1_ge2 : w1 ≥ 2 := by omega
      have h1b : (2 ^ (w1 + a1) - 3 ^ w1) * q0 = 2 ^ a1 - 1 := by
        rw [Nat.sub_mul, hbrox_1b]
        have hm_le := Nat.mul_le_mul_right q0 (Nat.le_of_lt hgt1); omega
      have hD_le : 2 ^ (w1 + a1) - 3 ^ w1 ≤ 2 ^ a1 - 1 := by
        have hm := Nat.mul_le_mul_left (2 ^ (w1 + a1) - 3 ^ w1) hq0_pos
        rwa [Nat.mul_one, h1b] at hm
      rcases one_block_w1_ge_13_and_a1_ge_8 w1 a1 hw1_ge2 ha1 hgt1 hD_le with ⟨hw13, ha8⟩
      have hq0_ge17 : q0 ≥ 17 :=
        (one_block_no_pow3_quotient_and_q0_ge_17 w1 a1 q0 hw1_ge2 ha1 hgt1 h1b).2.2.2.2.1
      have hN0_17 : dp2GlobalOddVal u0 ≥ 17 * 2 ^ w1 - 1 := by
        have hm := Nat.mul_le_mul_left (2 ^ w1) hq0_ge17
        rw [← hN0_eq, Nat.mul_comm (2 ^ w1) 17] at hm; omega
      exact ⟨hw13, ha8, hq01, hq12, hN0_17⟩
    · -- `2 ∣ a1 ∧ 2 ∣ a2 ∧ 2 ∣ a3`:
      rintro ⟨ha1_2, ha2_2, ha3_2⟩
      have h3_gcd : 3 ∣ natListGcd qs3 :=
        (m_block_companion_prime_quotient_cascades.1 (w1, a1) [(w2, a2), (w3, a3)] qs3
          (by intro b hb; simp at hb; rcases hb with rfl | rfl | rfl <;> omega)
          (by simpa [blockWeightSum, blockStepSum, Nat.add_assoc] using hlt)
          rfl hqs3_spec).2.1
          (by intro b hb; simp at hb; rcases hb with rfl | rfl | rfl
              · exact ha1_2
              · exact ha2_2
              · exact ha3_2)
      have hg0 : 3 ∣ q0 := Nat.dvd_trans h3_gcd (Nat.gcd_dvd_left q0 _)
      have hg12 : 3 ∣ Nat.gcd q1 (Nat.gcd q2 0) := Nat.dvd_trans h3_gcd (Nat.gcd_dvd_right q0 _)
      have hg1 : 3 ∣ q1 := Nat.dvd_trans hg12 (Nat.gcd_dvd_left q1 _)
      have hg2 : 3 ∣ q2 := by
        have h := Nat.dvd_trans hg12 (Nat.gcd_dvd_right q1 _)
        rwa [Nat.gcd_zero_right] at h
      have hge3 : ∀ q : Nat, q ≥ 1 -> 3 ∣ q -> q ≥ 3 := by
        intro q hq ⟨c, hc⟩; cases c with | zero => rw [Nat.mul_zero] at hc; omega | succ _ => omega
      have hfl0 : dp2GlobalOddVal u0 ≥ 3 * 2 ^ w1 - 1 := by
        have hm := Nat.mul_le_mul_left (2 ^ w1) (hge3 q0 hq0_pos hg0)
        rw [← hN0_eq, Nat.mul_comm (2 ^ w1) 3] at hm; omega
      have hfl1 : dp2GlobalOddVal u1 ≥ 3 * 2 ^ w2 - 1 := by
        have hm := Nat.mul_le_mul_left (2 ^ w2) (hge3 q1 hq1_pos hg1)
        rw [← hN1_eq, Nat.mul_comm (2 ^ w2) 3] at hm; omega
      have hfl2 : dp2GlobalOddVal u2 ≥ 3 * 2 ^ w3 - 1 := by
        have hm := Nat.mul_le_mul_left (2 ^ w3) (hge3 q2 hq2_pos hg2)
        rw [← hN2_eq, Nat.mul_comm (2 ^ w3) 3] at hm; omega
      exact ⟨hg0, hg1, hg2, hfl0, hfl1, hfl2⟩
    · -- `(w1 + w2 + w3) % 2 = 1 ∧ 4 ∣ a1 ∧ 4 ∣ a2 ∧ 4 ∣ a3`:
      rintro ⟨hw_odd, ha1_4, ha2_4, ha3_4⟩
      have hall4 : ∀ b ∈ [(w1, a1), (w2, a2), (w3, a3)], 4 ∣ b.2 := by
        intro b hb; simp at hb; rcases hb with rfl | rfl | rfl
        · exact ha1_4
        · exact ha2_4
        · exact ha3_4
      have hcasc := m_block_companion_prime_quotient_cascades.1 (w1, a1) [(w2, a2), (w3, a3)] qs3
        (by intro b hb; simp at hb; rcases hb with rfl | rfl | rfl <;> omega)
        (by simpa [blockWeightSum, blockStepSum, Nat.add_assoc] using hlt)
        rfl hqs3_spec
      have h15_g : 15 ∣ natListGcd qs3 := by
        rcases hcasc.2.2.1 hall4 with ⟨c, hc⟩ | ⟨_, h15⟩
        · exfalso; simp only [blockWeightSum, Nat.add_zero] at hc; omega
        · exact h15
      have h15_q0 : 15 ∣ q0 := Nat.dvd_trans h15_g (Nat.gcd_dvd_left q0 _)
      have h15_12 : 15 ∣ Nat.gcd q1 (Nat.gcd q2 0) := Nat.dvd_trans h15_g (Nat.gcd_dvd_right q0 _)
      have h15_q1 : 15 ∣ q1 := Nat.dvd_trans h15_12 (Nat.gcd_dvd_left q1 _)
      have h15_q2 : 15 ∣ q2 := by
        have h := Nat.dvd_trans h15_12 (Nat.gcd_dvd_right q1 _)
        rwa [Nat.gcd_zero_right] at h
      have ha1_ge4 : a1 ≥ 4 := by rcases ha1_4 with ⟨c, hc⟩; omega
      have ha2_ge4 : a2 ≥ 4 := by rcases ha2_4 with ⟨c, hc⟩; omega
      have ha3_ge4 : a3 ≥ 4 := by rcases ha3_4 with ⟨c, hc⟩; omega
      have hq0_75 : q0 ≥ 75 :=
        (m_block_two_pivot_telescoping_and_2adic_quotient_boost.2.1.1 w1 a1 w2 q0 q1 15
          ha1_ge4 (by decide) h15_q0 hbrox1).2
      have hq1_75 : q1 ≥ 75 :=
        (m_block_two_pivot_telescoping_and_2adic_quotient_boost.2.1.1 w2 a2 w3 q1 q2 15
          ha2_ge4 (by decide) h15_q1 hbrox2).2
      have hq2_75 : q2 ≥ 75 :=
        (m_block_two_pivot_telescoping_and_2adic_quotient_boost.2.1.1 w3 a3 w1 q2 q0 15
          ha3_ge4 (by decide) h15_q2 hbrox3).2
      have hN0_75 : dp2GlobalOddVal u0 ≥ 75 * 2 ^ w1 - 1 := by
        have hm := Nat.mul_le_mul_left (2 ^ w1) hq0_75
        rw [← hN0_eq, Nat.mul_comm (2 ^ w1) 75] at hm; omega
      have hN1_75 : dp2GlobalOddVal u1 ≥ 75 * 2 ^ w2 - 1 := by
        have hm := Nat.mul_le_mul_left (2 ^ w2) hq1_75
        rw [← hN1_eq, Nat.mul_comm (2 ^ w2) 75] at hm; omega
      have hN2_75 : dp2GlobalOddVal u2 ≥ 75 * 2 ^ w3 - 1 := by
        have hm := Nat.mul_le_mul_left (2 ^ w3) hq2_75
        rw [← hN2_eq, Nat.mul_comm (2 ^ w3) 75] at hm; omega
      exact ⟨h15_q0, h15_q1, h15_q2, hq0_75, hq1_75, hq2_75, hN0_75, hN1_75, hN2_75⟩
  have h3blk_even_elim : ∀ (w1 a1 w2 a2 w3 a3 : Nat) (u0 : List MixedSRSSym),
      w1 ≥ 1 -> a1 ≥ 1 -> w2 ≥ 1 -> a2 ≥ 1 -> w3 ≥ 1 -> a3 ≥ 1 ->
      2 ∣ a1 -> 2 ∣ a2 -> 2 ∣ a3 ->
      (2 ^ (w1 + a1 + w2 + a2 + w3 + a3) - 3 ^ (w1 + w2 + w3)) * 3 + 3 ^ (w2 + w3) >
        3 ^ (w2 + w3) * 2 ^ a1 + 2 ^ (a1 + w2) * 3 ^ w3 * (2 ^ (a2 + a3) - 1) ->
      ¬ dp2AnnotatedChain u0
        ((List.replicate (w1 - 1) 1 ++ [1 + a1]) ++
         (List.replicate (w2 - 1) 1 ++ [1 + a2]) ++
         (List.replicate (w3 - 1) 1 ++ [1 + a3])) u0 := by
    intro w1 a1 w2 a2 w3 a3 u0 hw1 ha1 hw2 ha2 hw3 ha3 he1 he2 he3 hgt_3d hann
    rcases (h3blk_main w1 a1 w2 a2 w3 a3 u0 hw1 ha1 hw2 ha2 hw3 ha3 hann).2.2 with
      ⟨_, _, _, _, _, _, _, _, hq0_pos, _, _, _, _, _, _, _, _, _, h2piv_dq0, _, _, _, hev, _⟩
    rcases hev ⟨he1, he2, he3⟩ with ⟨hq0_3, _, _, _, _, _⟩
    rcases hq0_3 with ⟨k0, hk0⟩
    have hk0_pos : k0 ≥ 1 := by
      cases k0 with
      | zero => rw [Nat.mul_zero] at hk0; omega
      | succ _ => omega
    have hq0_ge3 : 3 ≤ (dp2GlobalOddVal u0 + 1) / 2 ^ w1 := by omega
    have h3D_le := Nat.mul_le_mul_left
      (2 ^ (w1 + a1 + w2 + a2 + w3 + a3) - 3 ^ (w1 + w2 + w3)) hq0_ge3
    have hle := Nat.le_trans (Nat.add_le_add_right h3D_le (3 ^ (w2 + w3))) h2piv_dq0
    omega
  refine ⟨hcar_3blk, ⟨hno_1_15, by decide⟩, h3blk_main, ?_⟩
  intro u0
  exact h3blk_even_elim 17 2 17 2 17 26 u0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

-- ============================================================================
-- SECTION 2: Front B (Branches P3.2–P3.4) — General Rectangular `∀ U > T ≥ 1`
--            Row+Column `Nat.lcm` Confluence & Joint-LCM Reduced Majorant,
--            `9 × 9` `(T = 3, U = 3)` Higher Resonant Rays & Log Zero-Horizon,
--            & Universal Recursive `p`-Pivot Brox Carry Squeeze (`W16_H2`)
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Section 2A: General Rectangular `∀ U > T ≥ 1` Row-Side `(2^(W*u) - 1)^(T*(U-T))`
--             Vandermonde Divisibility, Joint `Nat.lcm` Confluence, & `8 × 8`
--             Row-Column Overlap Certificate (`W16_H2`)
-- ----------------------------------------------------------------------------

/-- Canonical `U × T` rectangular row grid `(i % U, i / U)` (`r < U`, `s < T`, grouped by `s`-block). -/
def laurentRectRows (U _T : Nat) (i : Fin (U * _T)) : Nat × Nat :=
  (i.val % U, i.val / U)

private theorem intSumPrefix_add_w16 (L : Nat) (f g : Fin L -> Int) :
    ∀ k : Nat, intSumPrefix L (fun j => f j + g j) k = intSumPrefix L f k + intSumPrefix L g k
  | 0 => rfl
  | k + 1 => by
    simp only [intSumPrefix, intSumPrefix_add_w16 L f g k]
    by_cases hk : k < L
    · simp only [hk, dite_true]; omega
    · simp only [hk, dite_false, Int.add_zero]

private theorem intSumPrefix_sub_eq_w16 (L : Nat) (f g : Fin L -> Int) :
    ∀ k : Nat, intSumPrefix L (fun j => f j - g j) k = intSumPrefix L f k - intSumPrefix L g k
  | 0 => rfl
  | k + 1 => by
    simp only [intSumPrefix, intSumPrefix_sub_eq_w16 L f g k]
    by_cases hk : k < L
    · simp only [hk, dite_true]; omega
    · simp only [hk, dite_false, Int.add_zero]

private theorem intSumPrefix_mul_w16 (c : Int) (L : Nat) (f : Fin L -> Int) :
    ∀ k : Nat, intSumPrefix L (fun j => c * f j) k = c * intSumPrefix L f k
  | 0 => by simp [intSumPrefix]
  | k + 1 => by
    simp only [intSumPrefix, intSumPrefix_mul_w16 c L f k]
    by_cases hk : k < L
    · simp only [hk, dite_true, Int.mul_add]
    · simp only [hk, dite_false, Int.add_zero]

private theorem intSumPrefix_zero_w16 (L : Nat) (f : Fin L -> Int) (hz : ∀ j : Fin L, f j = 0) :
    ∀ k : Nat, intSumPrefix L f k = 0
  | 0 => rfl
  | k + 1 => by
    simp only [intSumPrefix, intSumPrefix_zero_w16 L f hz k]
    by_cases hk : k < L
    · simp only [hk, dite_true, hz ⟨k, hk⟩, Int.add_zero]
    · simp only [hk, dite_false, Int.add_zero]

private theorem intSumPrefix_congr_w16 (L : Nat) (f g : Fin L -> Int)
    (hfg : ∀ j : Fin L, f j = g j) :
    ∀ k : Nat, intSumPrefix L f k = intSumPrefix L g k
  | 0 => rfl
  | k + 1 => by
    simp only [intSumPrefix, intSumPrefix_congr_w16 L f g hfg k]
    by_cases hk : k < L
    · simp only [hk, dite_true, hfg ⟨k, hk⟩]
    · simp only [hk, dite_false]

private theorem dite_pos_w16 {α : Sort _} {P : Prop} [Decidable P] (h : P)
    (t : P -> α) (e : ¬ P -> α) : dite P t e = t h := by
  split
  · rfl
  · next hn => exact False.elim (hn h)

private theorem dite_neg_w16 {α : Sort _} {P : Prop} [Decidable P] (h : ¬ P)
    (t : P -> α) (e : ¬ P -> α) : dite P t e = e h := by
  split
  · next hp => exact False.elim (h hp)
  · rfl

private theorem antisym_double_sum_zero_w16 (N : Nat) (G : Fin N -> Fin N -> Int)
    (hanti : ∀ a b : Fin N, G a b + G b a = 0) :
    ∀ m : Nat, m ≤ N -> intSumPrefix N (fun a => intSumPrefix N (fun b => G a b) m) m = 0
  | 0, _ => rfl
  | m + 1, hm => by
    have hm_lt : m < N := hm
    have hdiag : G ⟨m, hm_lt⟩ ⟨m, hm_lt⟩ = 0 := by have h := hanti ⟨m, hm_lt⟩ ⟨m, hm_lt⟩; omega
    have hstep_in : ∀ a : Fin N,
        intSumPrefix N (fun b => G a b) (m + 1) = intSumPrefix N (fun b => G a b) m + G a ⟨m, hm_lt⟩ := by
      intro a; simp only [intSumPrefix, hm_lt, dite_true]
    have hcongr := intSumPrefix_congr_w16 N
      (fun a => intSumPrefix N (fun b => G a b) (m + 1))
      (fun a => intSumPrefix N (fun b => G a b) m + G a ⟨m, hm_lt⟩) hstep_in m
    conv => lhs; unfold intSumPrefix
    simp only [hm_lt, dite_true]
    rw [hcongr]
    conv => lhs; rhs; unfold intSumPrefix
    simp only [hm_lt, dite_true]
    rw [intSumPrefix_add_w16 N _ _ m,
        antisym_double_sum_zero_w16 N G hanti m (Nat.le_of_lt hm), Int.zero_add,
        hdiag, Int.add_zero,
        ← intSumPrefix_add_w16 N (fun a => G a ⟨m, hm_lt⟩) (fun b => G ⟨m, hm_lt⟩ b) m]
    exact intSumPrefix_zero_w16 N _ (fun a => hanti a ⟨m, hm_lt⟩) m

private theorem intDet_row0_eq_row1_zero_w16 (L : Nat) (A : Fin (L + 2) -> Fin (L + 2) -> Int)
    (heq01 : ∀ j : Fin (L + 2),
      A ⟨0, Nat.zero_lt_succ (L + 1)⟩ j = A ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ L)⟩ j) :
    intDet (L + 2) A = 0 := by
  let z0 : Fin (L + 2) := ⟨0, Nat.zero_lt_succ (L + 1)⟩
  let z1 : Fin (L + 2) := ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ L)⟩
  let sgn2 (k : Nat) : Int := if k % 2 = 0 then 1 else -1
  let f (j : Fin (L + 2)) (c : Fin (L + 1)) : Int :=
    sgn2 j.val * A z0 j *
      (sgn2 c.val * A z1 (skipFinIdx j c) * intDet L (intSubMat (intSubMat A j) c))
  let G (a b : Fin (L + 2)) : Int :=
    if hlt : a.val < b.val then f a ⟨b.val - 1, by omega⟩
    else if hgt : b.val < a.val then f a ⟨b.val, by omega⟩
    else 0
  have hsub2_sym : ∀ (a b : Fin (L + 2)) (hlt : a.val < b.val),
      intSubMat (intSubMat A a) ⟨b.val - 1, by omega⟩ =
        intSubMat (intSubMat A b) ⟨a.val, by omega⟩ := by
    intro a b hlt; funext r k
    unfold intSubMat skipFinIdx
    dsimp only
    by_cases hka : k.val < a.val
    · have hkb : k.val < b.val - 1 := by omega
      have hkb2 : k.val < b.val := by omega
      simp only [hkb, hka, hkb2, ite_true]
    · by_cases hkb : k.val < b.val - 1
      · have hk1_b : k.val + 1 < b.val := by omega
        simp only [hkb, ite_true, hka, ite_false, hk1_b]
      · have hk1_nb : ¬ (k.val + 1 < b.val) := by omega
        have hk1_na : ¬ (k.val + 1 < a.val) := by omega
        simp only [hkb, hka, hk1_nb, hk1_na, ite_false]
  have hsgn_flip : ∀ n : Nat, sgn2 (n + 1) = - sgn2 n := by
    intro n; dsimp only [sgn2]
    by_cases hn : n % 2 = 0
    · have hn1 : ¬ ((n + 1) % 2 = 0) := by omega
      simp [hn, hn1]
    · have hn1 : (n + 1) % 2 = 0 := by omega
      simp [hn, hn1]
  have hpair : ∀ (a b : Fin (L + 2)) (hlt : a.val < b.val),
      f a ⟨b.val - 1, by omega⟩ + f b ⟨a.val, by omega⟩ = 0 := by
    intro a b hlt
    have hsk1 : skipFinIdx a ⟨b.val - 1, by omega⟩ = b := by
      unfold skipFinIdx; dsimp only
      rw [ite_false_of_w10 (by omega : ¬ (b.val - 1 < a.val))]
      exact Fin.ext (by dsimp; omega)
    have hsk2 : skipFinIdx b ⟨a.val, by omega⟩ = a := by
      unfold skipFinIdx; dsimp only
      rw [ite_true_of_w10 hlt]
    have hb_succ : sgn2 b.val = - sgn2 (b.val - 1) := by
      conv => lhs; rw [show b.val = (b.val - 1) + 1 by omega]
      exact hsgn_flip (b.val - 1)
    dsimp only [f]
    rw [hsk1, hsk2, hsub2_sym a b hlt, ← heq01 a, ← heq01 b, hb_succ]
    generalize sgn2 a.val = sa, sgn2 (b.val - 1) = sb,
      A z0 a = xa, A z0 b = xb,
      intDet L (intSubMat (intSubMat A b) ⟨a.val, by omega⟩) = dm
    rw [Int.neg_mul, Int.neg_mul,
        show sb * xb * (sa * xa * dm) = sa * xa * (sb * xb * dm) by ac_rfl]
    omega
  have hanti : ∀ a b : Fin (L + 2), G a b + G b a = 0 := by
    intro a b; dsimp only [G]
    by_cases hab : a.val < b.val
    · have hba : ¬ (b.val < a.val) := by omega
      simp only [hab, hba, dite_true, dite_false]
      exact hpair a b hab
    · by_cases hba : b.val < a.val
      · simp only [hab, hba, dite_false, dite_true]
        rw [Int.add_comm]; exact hpair b a hba
      · simp only [hab, hba, dite_false]; rfl
  have hrow_sum : ∀ a : Fin (L + 2),
      intSumPrefix (L + 1) (fun c => f a c) (L + 1) =
        intSumPrefix (L + 2) (fun b => G a b) (L + 2) := by
    intro a
    have hpre : ∀ m : Nat, m ≤ L + 1 ->
        intSumPrefix (L + 1) (fun c => f a c) m =
          intSumPrefix (L + 2) (fun b => G a b) (if a.val < m then m + 1 else m) := by
      intro m hm; induction m with
      | zero => simp [intSumPrefix]
      | succ m' ih =>
        have hm'_lt1 : m' < L + 1 := hm
        have hm'_lt2 : m' < L + 2 := by omega
        have hm1_lt2 : m' + 1 < L + 2 := by omega
        simp only [intSumPrefix, hm'_lt1, dite_true, ih (Nat.le_of_lt hm)]
        by_cases ham : a.val < m'
        · have ham1 : a.val < m' + 1 := by omega
          rw [ite_true_of_w10 ham, ite_true_of_w10 ham1]
          simp only [intSumPrefix, hm1_lt2, dite_true]
          have hG : G a ⟨m' + 1, hm1_lt2⟩ = f a ⟨m', hm'_lt1⟩ := by
            dsimp only [G]; simp only [ham1, dite_true]; rfl
          rw [hG]
        · by_cases heq : a.val = m'
          · have ham1 : a.val < m' + 1 := by omega
            rw [ite_false_of_w10 ham, ite_true_of_w10 ham1]
            conv => rhs; unfold intSumPrefix
            simp only [hm1_lt2, dite_true]
            conv => rhs; lhs; unfold intSumPrefix
            simp only [hm'_lt2, dite_true]
            have hGa : G a ⟨m', hm'_lt2⟩ = 0 := by
              dsimp only [G]
              have h1 : ¬ (a.val < m') := by omega
              have h2 : ¬ (m' < a.val) := by omega
              simp [h1, h2]
            have hGm1 : G a ⟨m' + 1, hm1_lt2⟩ = f a ⟨m', hm'_lt1⟩ := by
              dsimp only [G]; simp only [ham1, dite_true]; rfl
            rw [hGa, Int.add_zero, hGm1]
          · have hgt : m' < a.val := by omega
            have hnam1 : ¬ (a.val < m' + 1) := by omega
            rw [ite_false_of_w10 ham, ite_false_of_w10 hnam1]
            simp only [intSumPrefix, hm'_lt2, dite_true]
            have hGm : G a ⟨m', hm'_lt2⟩ = f a ⟨m', hm'_lt1⟩ := by
              dsimp only [G]; simp only [ham, hgt, dite_false, dite_true]
            rw [hGm]
    have ha_lt : a.val < L + 1 ∨ a.val = L + 1 := by have := a.isLt; omega
    rcases ha_lt with hlt | heq
    · have hp := hpre (L + 1) (Nat.le_refl _)
      rwa [ite_true_of_w10 hlt] at hp
    · have hp := hpre (L + 1) (Nat.le_refl _)
      rw [ite_false_of_w10 (by omega : ¬ (a.val < L + 1))] at hp
      rw [hp]
      conv => rhs; unfold intSumPrefix
      have hlt2 : L + 1 < L + 2 := Nat.lt_succ_self (L + 1)
      simp only [hlt2, dite_true]
      have hGz : G a ⟨L + 1, hlt2⟩ = 0 := by
        dsimp only [G]
        have h1 : ¬ (a.val < L + 1) := by omega
        have h2 : ¬ (L + 1 < a.val) := by omega
        simp [h1, h2]
      rw [hGz, Int.add_zero]
  have hexpand : intDet (L + 2) A =
      intSumPrefix (L + 2) (fun j => intSumPrefix (L + 1) (fun c => f j c) (L + 1)) (L + 2) := by
    conv => lhs; unfold intDet intSumFin
    apply intSumPrefix_congr_w16 (L + 2)
    intro j
    conv => lhs; rhs; unfold intDet intSumFin
    rw [← intSumPrefix_mul_w16 _ (L + 1)]
    apply intSumPrefix_congr_w16 (L + 1)
    intro c; rfl
  rw [hexpand,
      intSumPrefix_congr_w16 (L + 2) _ (fun j => intSumPrefix (L + 2) (fun b => G j b) (L + 2)) hrow_sum (L + 2)]
  exact antisym_double_sum_zero_w16 (L + 2) G hanti (L + 2) (Nat.le_refl _)

private theorem intDet_row0_sub_w16 (L : Nat) (A B : Fin (L + 1) -> Fin (L + 1) -> Int)
    (heq_rest : ∀ (i : Fin (L + 1)) (j : Fin (L + 1)), i.val ≥ 1 -> A i j = B i j) :
    intDet (L + 1) (fun i j => if i.val = 0 then A i j - B i j else A i j) =
      intDet (L + 1) A - intDet (L + 1) B := by
  let C : Fin (L + 1) -> Fin (L + 1) -> Int := fun i j => if i.val = 0 then A i j - B i j else A i j
  have hsubC : ∀ j : Fin (L + 1), intSubMat C j = intSubMat A j := by
    intro j; funext r c; unfold intSubMat
    dsimp only [C]; simp
  have hsubB : ∀ j : Fin (L + 1), intSubMat B j = intSubMat A j := by
    intro j; funext r c; unfold intSubMat
    exact (heq_rest ⟨r.val + 1, by omega⟩ (skipFinIdx j c) (by dsimp; omega)).symm
  change intDet (L + 1) C = intDet (L + 1) A - intDet (L + 1) B
  simp only [intDet, intSumFin]
  rw [← intSumPrefix_sub_eq_w16 (L + 1)]
  apply intSumPrefix_congr_w16 (L + 1)
  intro j
  rw [hsubC j, hsubB j]
  have hC0 : C ⟨0, Nat.zero_lt_succ L⟩ j = A ⟨0, Nat.zero_lt_succ L⟩ j - B ⟨0, Nat.zero_lt_succ L⟩ j := rfl
  rw [hC0]
  generalize (if j.val % 2 = 0 then (1 : Int) else -1) = sgn,
    A ⟨0, Nat.zero_lt_succ L⟩ j = a0,
    B ⟨0, Nat.zero_lt_succ L⟩ j = b0,
    intDet L (intSubMat A j) = dA
  rw [Int.mul_sub sgn a0 b0, Int.sub_mul (sgn * a0) (sgn * b0) dA]

private theorem intDet_sub_prev_row_eq_w16 :
    ∀ (k L : Nat) (hk : k + 1 < L) (A : Fin L -> Fin L -> Int),
      intDet L (fun i j => if i.val = k + 1 then A i j - A ⟨k, by omega⟩ j else A i j) =
        intDet L A
  | 0, 0, hk, _ => by omega
  | 0, 1, hk, _ => by omega
  | 0, m + 2, _, A => by
    let z0 : Fin (m + 2) := ⟨0, Nat.zero_lt_succ (m + 1)⟩
    let z1 : Fin (m + 2) := ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ m)⟩
    let A' : Fin (m + 2) -> Fin (m + 2) -> Int := fun i j =>
      if i.val = 1 then A i j - A z0 j else A i j
    let A_dup : Fin (m + 2) -> Fin (m + 2) -> Int := fun i j =>
      if i.val = 1 then A z0 j else A i j
    have hdup0 : intDet (m + 2) A_dup = 0 :=
      intDet_row0_eq_row1_zero_w16 m A_dup (fun j => rfl)
    change intDet (m + 2) A' = intDet (m + 2) A
    rw [show intDet (m + 2) A = intDet (m + 2) A - intDet (m + 2) A_dup by rw [hdup0, Int.sub_zero]]
    conv => lhs; unfold intDet intSumFin
    conv => rhs; lhs; unfold intDet intSumFin
    conv => rhs; rhs; unfold intDet intSumFin
    rw [← intSumPrefix_sub_eq_w16 (m + 2)]
    apply intSumPrefix_congr_w16 (m + 2)
    intro j
    have hA'0 : A' ⟨0, Nat.zero_lt_succ (m + 1)⟩ j = A ⟨0, Nat.zero_lt_succ (m + 1)⟩ j := rfl
    have hAd0 : A_dup ⟨0, Nat.zero_lt_succ (m + 1)⟩ j = A ⟨0, Nat.zero_lt_succ (m + 1)⟩ j := rfl
    have hsub_eq : intSubMat A' j = (fun r c =>
        if r.val = 0 then intSubMat A j r c - intSubMat A_dup j r c else intSubMat A j r c) := by
      funext r c; unfold intSubMat
      by_cases hr0 : r.val = 0
      · have hr0_s : r.val + 1 = 1 := by omega
        dsimp only [A', A_dup]
        rw [ite_true_of_w10 hr0_s, ite_true_of_w10 hr0, ite_true_of_w10 hr0_s]
      · have hr1 : (⟨r.val + 1, by omega⟩ : Fin (m + 2)).val ≠ 1 := by dsimp; omega
        dsimp only [A']
        rw [ite_false_of_w10 hr1, ite_false_of_w10 hr0]
    have hrest_eq : ∀ (r c : Fin (m + 1)), r.val ≥ 1 -> intSubMat A j r c = intSubMat A_dup j r c := by
      intro r c hr1; unfold intSubMat
      have hne1 : (⟨r.val + 1, by omega⟩ : Fin (m + 2)).val ≠ 1 := by dsimp; omega
      dsimp only [A_dup]; rw [ite_false_of_w10 hne1]
    rw [hA'0, hAd0, hsub_eq, intDet_row0_sub_w16 m (intSubMat A j) (intSubMat A_dup j) hrest_eq,
        Int.mul_sub]
  | k' + 1, 0, hk, _ => by omega
  | k' + 1, 1, hk, _ => by omega
  | k' + 1, m + 2, hk, A => by
    let A' : Fin (m + 2) -> Fin (m + 2) -> Int := fun i j =>
      if i.val = k' + 2 then A i j - A ⟨k' + 1, by omega⟩ j else A i j
    change intDet (m + 2) A' = intDet (m + 2) A
    conv => lhs; unfold intDet intSumFin
    conv => rhs; unfold intDet intSumFin
    apply intSumPrefix_congr_w16 (m + 2)
    intro j
    have hA'0 : A' ⟨0, Nat.zero_lt_succ (m + 1)⟩ j = A ⟨0, Nat.zero_lt_succ (m + 1)⟩ j := rfl
    have hsub : intSubMat A' j = (fun r c =>
        if r.val = k' + 1 then intSubMat A j r c - intSubMat A j ⟨k', by omega⟩ c
        else intSubMat A j r c) := by
      funext r c; unfold intSubMat
      by_cases hr : r.val = k' + 1
      · have hr2 : (⟨r.val + 1, by omega⟩ : Fin (m + 2)).val = k' + 2 := by dsimp; omega
        dsimp only [A']
        rw [ite_true_of_w10 hr2, ite_true_of_w10 hr]
      · have hr2 : (⟨r.val + 1, by omega⟩ : Fin (m + 2)).val ≠ k' + 2 := by dsimp; omega
        dsimp only [A']
        rw [ite_false_of_w10 hr2, ite_false_of_w10 hr]
    rw [hA'0, hsub, intDet_sub_prev_row_eq_w16 k' (m + 1) (by omega) (intSubMat A j)]

private theorem intDet_scale_row_w16 (c : Int) :
    ∀ (L : Nat) (r0 : Fin L) (A : Fin L -> Fin L -> Int),
      intDet L (fun i j => if i = r0 then c * A i j else A i j) = c * intDet L A
  | 0, r0, _ => Fin.elim0 r0
  | L + 1, r0, A => by
    let A' : Fin (L + 1) -> Fin (L + 1) -> Int := fun i j => if i = r0 then c * A i j else A i j
    change intDet (L + 1) A' = c * intDet (L + 1) A
    conv => lhs; unfold intDet intSumFin
    conv => rhs; rhs; unfold intDet intSumFin
    rw [← intSumPrefix_mul_w16 c (L + 1)]
    apply intSumPrefix_congr_w16 (L + 1)
    intro j
    by_cases hr0 : r0.val = 0
    · have h0eq : (⟨0, Nat.zero_lt_succ L⟩ : Fin (L + 1)) = r0 := Fin.ext hr0.symm
      have hA'0 : A' ⟨0, Nat.zero_lt_succ L⟩ j = c * A ⟨0, Nat.zero_lt_succ L⟩ j := by
        dsimp only [A']; rw [ite_true_of_w10 h0eq]
      have hsub : intSubMat A' j = intSubMat A j := by
        funext r col; unfold intSubMat
        have hne : (⟨r.val + 1, by omega⟩ : Fin (L + 1)) ≠ r0 := fun he => by
          have hv := congrArg Fin.val he; dsimp at hv; omega
        dsimp only [A']; rw [ite_false_of_w10 hne]
      rw [hA'0, hsub]; ac_rfl
    · have h0ne : (⟨0, Nat.zero_lt_succ L⟩ : Fin (L + 1)) ≠ r0 := fun he => hr0 (congrArg Fin.val he).symm
      have hA'0 : A' ⟨0, Nat.zero_lt_succ L⟩ j = A ⟨0, Nat.zero_lt_succ L⟩ j := by
        dsimp only [A']; rw [ite_false_of_w10 h0ne]
      let r' : Fin L := ⟨r0.val - 1, by have := r0.isLt; omega⟩
      have hsub : intSubMat A' j = (fun r col => if r = r' then c * intSubMat A j r col else intSubMat A j r col) := by
        funext r col; unfold intSubMat
        by_cases hrr : r = r'
        · have heq_f : (⟨r.val + 1, by omega⟩ : Fin (L + 1)) = r0 := by
            apply Fin.ext; have hv := congrArg Fin.val hrr; dsimp [r'] at hv ⊢; omega
          dsimp only [A']; rw [ite_true_of_w10 heq_f, ite_true_of_w10 hrr]
        · have hne_f : (⟨r.val + 1, by omega⟩ : Fin (L + 1)) ≠ r0 := fun he => hrr (by
            apply Fin.ext; have hv := congrArg Fin.val he; dsimp [r'] at hv ⊢; omega)
          dsimp only [A']; rw [ite_false_of_w10 hne_f, ite_false_of_w10 hrr]
      rw [hA'0, hsub, intDet_scale_row_w16 c L r' (intSubMat A j)]; ac_rfl

private def intRowFactorProdPrefixW16 (L : Nat) (m : Fin L -> Int) : Nat -> Int
  | 0 => 1
  | k + 1 =>
    if h : k < L then intRowFactorProdPrefixW16 L m k * m ⟨k, h⟩
    else intRowFactorProdPrefixW16 L m k

private theorem intDet_row_factors_dvd_w16 (L : Nat) (m : Fin L -> Int) (B : Fin L -> Fin L -> Int)
    (hdvd : ∀ i j : Fin L, m i ∣ B i j) :
    intRowFactorProdPrefixW16 L m L ∣ intDet L B := by
  let Q : Fin L -> Fin L -> Int := fun i j =>
    if m i = 0 then 0 else B i j / m i
  have hBQ : ∀ i j : Fin L, B i j = m i * Q i j := by
    intro i j; dsimp only [Q]
    rcases hdvd i j with ⟨q, hq⟩
    by_cases hm0 : m i = 0
    · rw [hm0] at hq ⊢; simp [hq]
    · simp only [hm0, ite_false]
      rw [hq, Int.mul_comm (m i) q, Int.mul_ediv_cancel _ hm0, Int.mul_comm]
  let B_st : Nat -> Fin L -> Fin L -> Int := fun k i j =>
    if i.val < k then Q i j else B i j
  have h0 : B_st 0 = B := by funext i j; simp [B_st]
  have hL : B_st L = Q := by funext i j; dsimp [B_st]; rw [ite_true_of_w10 i.isLt]
  have hstep : ∀ k : Nat, k ≤ L ->
      intDet L B = intRowFactorProdPrefixW16 L m k * intDet L (B_st k) := by
    intro k hk; induction k with
    | zero => simp [intRowFactorProdPrefixW16, h0]
    | succ k' ih =>
      have hk_lt : k' < L := hk
      let rk : Fin L := ⟨k', hk_lt⟩
      have hrew : B_st k' = (fun i j => if i = rk then m rk * B_st (k' + 1) i j else B_st (k' + 1) i j) := by
        funext i j
        by_cases hi : i = rk
        · subst hi
          rw [ite_true_of_w10 rfl]
          dsimp [B_st, rk]
          rw [ite_false_of_w10 (Nat.lt_irrefl k'), ite_true_of_w10 (Nat.lt_succ_self k')]
          exact hBQ ⟨k', hk_lt⟩ j
        · rw [ite_false_of_w10 hi]
          have hiv : i.val ≠ k' := fun hv => hi (Fin.ext hv)
          dsimp [B_st]
          by_cases hlt : i.val < k'
          · rw [ite_true_of_w10 hlt, ite_true_of_w10 (by omega)]
          · rw [ite_false_of_w10 hlt, ite_false_of_w10 (by omega)]
      rw [ih (Nat.le_of_lt hk), hrew, intDet_scale_row_w16 (m rk) L rk (B_st (k' + 1))]
      simp only [intRowFactorProdPrefixW16, hk_lt, dite_true, Int.mul_assoc]
      dsimp only [rk]
  exact ⟨intDet L Q, by rw [hstep L (Nat.le_refl L), hL]⟩

private def bwdDiffAtW16 : Nat -> (Nat -> Int) -> Nat -> Int
  | 0, f, r => f r
  | p + 1, f, r => bwdDiffAtW16 p f r - bwdDiffAtW16 p f (r - 1)

private theorem bwdDiffAt_shift_w16 :
    ∀ (p : Nat) (f : Nat -> Int) (r : Nat), p + 1 ≤ r ->
      bwdDiffAtW16 (p + 1) f r = bwdDiffAtW16 p (fun q => f (q + 1) - f q) (r - 1)
  | 0, f, r, hr => by
    simp only [bwdDiffAtW16]
    rw [show r - 1 + 1 = r by omega]
  | p + 1, f, r, hr => by
    have e1 := bwdDiffAt_shift_w16 p f r (by omega)
    have e2 := bwdDiffAt_shift_w16 p f (r - 1) (by omega)
    conv => lhs; unfold bwdDiffAtW16
    rw [e1, e2]
    rfl

private theorem bwdDiffAt_zero_fn_w16 :
    ∀ (p r : Nat), bwdDiffAtW16 p (fun _ => (0 : Int)) r = 0
  | 0, _ => rfl
  | p + 1, r => by simp [bwdDiffAtW16, bwdDiffAt_zero_fn_w16 p]

private theorem bwdDiffAt_add_w16 :
    ∀ (p : Nat) (f g : Nat -> Int) (r : Nat),
      bwdDiffAtW16 p (fun q => f q + g q) r = bwdDiffAtW16 p f r + bwdDiffAtW16 p g r
  | 0, _, _, _ => rfl
  | p + 1, f, g, r => by
    simp only [bwdDiffAtW16, bwdDiffAt_add_w16 p f g]
    omega

private theorem bwdDiffAt_mul_const_w16 (c : Int) :
    ∀ (p : Nat) (f : Nat -> Int) (r : Nat),
      bwdDiffAtW16 p (fun q => f q * c) r = bwdDiffAtW16 p f r * c
  | 0, _, _ => rfl
  | p + 1, f, r => by
    simp only [bwdDiffAtW16, bwdDiffAt_mul_const_w16 c p f, Int.sub_mul]

private def intNatSumUpToW16 : Nat -> (Nat -> Int) -> Int
  | 0, _ => 0
  | n + 1, f => intNatSumUpToW16 n f + f n

private theorem bwdDiffAt_natSumUpTo_w16 (p : Nat) :
    ∀ (n : Nat) (F : Nat -> Nat -> Int) (r : Nat),
      bwdDiffAtW16 p (fun q => intNatSumUpToW16 n (fun m => F m q)) r =
        intNatSumUpToW16 n (fun m => bwdDiffAtW16 p (F m) r)
  | 0, _, _ => bwdDiffAt_zero_fn_w16 p _
  | n + 1, F, r => by
    simp only [intNatSumUpToW16]
    rw [bwdDiffAt_add_w16 p (fun q => intNatSumUpToW16 n (fun m => F m q)) (F n) r,
        bwdDiffAt_natSumUpTo_w16 p n F r]

private theorem binom_pascal_telescope_w16 (A t : Nat) :
    ∀ W : Nat,
      (laurentInterpBinom (A + W) (t + 1) : Int) - (laurentInterpBinom A (t + 1) : Int) =
        intNatSumUpToW16 W (fun m => (laurentInterpBinom (A + m) t : Int))
  | 0 => by simp [intNatSumUpToW16]
  | W + 1 => by
    have hpas : laurentInterpBinom (A + W + 1) (t + 1) =
        laurentInterpBinom (A + W) t + laurentInterpBinom (A + W) (t + 1) := by
      simp [laurentInterpBinom]
    simp only [intNatSumUpToW16, ← binom_pascal_telescope_w16 A t W]
    rw [← Nat.add_assoc A W 1, hpas, Int.natCast_add]
    omega

private theorem bwdDiffAt_binom_vanish_w16 (W : Nat) :
    ∀ (p x0 t r : Nat), t < p -> p ≤ r ->
      bwdDiffAtW16 p (fun q => (laurentInterpBinom (q * W + x0) t : Int)) r = 0
  | 0, _, _, _, ht, _ => by omega
  | p + 1, x0, 0, r, _, hr => by
    rw [bwdDiffAt_shift_w16 p _ r hr]
    have hz : (fun q => (laurentInterpBinom ((q + 1) * W + x0) 0 : Int) -
        (laurentInterpBinom (q * W + x0) 0 : Int)) = (fun _ => 0) := by
      funext q; simp [laurentInterpBinom_zero_right]
    rw [hz, bwdDiffAt_zero_fn_w16]
  | p + 1, x0, t' + 1, r, ht, hr => by
    rw [bwdDiffAt_shift_w16 p _ r hr]
    have hfn : (fun q => (laurentInterpBinom ((q + 1) * W + x0) (t' + 1) : Int) -
        (laurentInterpBinom (q * W + x0) (t' + 1) : Int)) =
        (fun q => intNatSumUpToW16 W (fun m => (laurentInterpBinom (q * W + (x0 + m)) t' : Int))) := by
      funext q
      have hadd : (q + 1) * W + x0 = (q * W + x0) + W := by rw [Nat.add_mul, Nat.one_mul]; omega
      rw [hadd, binom_pascal_telescope_w16 (q * W + x0) t' W]
      have hsum_eq : ∀ n : Nat,
          intNatSumUpToW16 n (fun m => (laurentInterpBinom (q * W + x0 + m) t' : Int)) =
          intNatSumUpToW16 n (fun m => (laurentInterpBinom (q * W + (x0 + m)) t' : Int)) := by
        intro n; induction n with
        | zero => rfl
        | succ n' ih => rw [intNatSumUpToW16, intNatSumUpToW16, ih, Nat.add_assoc]
      exact hsum_eq W
    rw [hfn, bwdDiffAt_natSumUpTo_w16 p W]
    have hz_sum : ∀ n : Nat,
        intNatSumUpToW16 n (fun m =>
          bwdDiffAtW16 p (fun q => (laurentInterpBinom (q * W + (x0 + m)) t' : Int)) (r - 1)) = 0 := by
      intro n; induction n with
      | zero => rfl
      | succ n' ih =>
        simp only [intNatSumUpToW16, ih, Int.zero_add]
        exact bwdDiffAt_binom_vanish_w16 W p (x0 + n') t' (r - 1) (by omega) (by omega)
    exact hz_sum W

-- Downward sweep of adjacent-row differences within block `s` from `r = U - 1` down to `p + 1`:
private def sweepSingleBlockW16 (N U s p : Nat) : Nat -> (Fin N -> Fin N -> Int) -> (Fin N -> Fin N -> Int)
  | 0, A => A
  | cnt + 1, A =>
    let r := p + 1 + cnt
    let A1 := if h : s * U + r < N then
      (fun i j => if i.val = s * U + r then A i j - A ⟨s * U + r - 1, by omega⟩ j else A i j)
    else A
    sweepSingleBlockW16 N U s p cnt A1

private def sweepAllBlocksPassW16 (N U p : Nat) : Nat -> (Fin N -> Fin N -> Int) -> (Fin N -> Fin N -> Int)
  | 0, A => A
  | s + 1, A =>
    sweepSingleBlockW16 N U s p (U - (p + 1)) (sweepAllBlocksPassW16 N U p s A)

private def sweepMultiPassW16 (N U T : Nat) : Nat -> (Fin N -> Fin N -> Int) -> (Fin N -> Fin N -> Int)
  | 0, A => A
  | p + 1, A => sweepAllBlocksPassW16 N U p T (sweepMultiPassW16 N U T p A)

private def v8OverlapDataW16 : List (List Int) :=
  [[1, 0, 0, 0, 0, 0, 0, 0],
   [0, 1, -1, 1, -17, 53, -501, 4205],
   [0, 0, 2, -2, 34, -106, 1002, -8410],
   [0, 0, 0, 3, -57, 209, -2041, 17457],
   [0, 0, 0, 0, 36, -300, 3228, -29052],
   [0, 0, 0, 0, 0, 684, -8884, 86644],
   [0, 0, 0, 0, 0, 0, 13856, -185504],
   [0, 0, 0, 0, 0, 0, 0, 654208]]

private def m8OverlapDataW16 : List (List Int) :=
  [[1, 0, 0, 0, 0, 0, 0, 0],
   [1, 2, 0, 0, 0, 0, 0, 0],
   [1, 4, 18, 0, 0, 0, 0, 0],
   [1, 6, 108, 108, 0, 0, 0, 0],
   [1, 5, 47, 22, -152, 0, 0, 0],
   [1, 7, 233, 370, 4168, 13856, 0, 0],
   [1, 9, 995, 2878, 177688, 1476832, 20934656, 0],
   [1, 11, 4061, 17482, 3706408, 55472928, 2881852416, 17348297728]]

private def intAt2DW16 (tbl : List (List Int)) (i j : Nat) : Int :=
  match tbl.drop i with
  | row :: _ =>
    match row.drop j with
    | x :: _ => x
    | [] => 0
  | [] => 0

private def v8OverlapMatW16 (i j : Fin 8) : Int := intAt2DW16 v8OverlapDataW16 i.val j.val
private def m8OverlapMatW16 (i j : Fin 8) : Int := intAt2DW16 m8OverlapDataW16 i.val j.val
private def a8Newton251W16 (i j : Fin 8) : Int :=
  Int.ofNat (mixedNewtonCoeffAllU 2 2
    ((laurentRectRows 4 2 i).1 * 2 + (laurentRectRows 4 2 i).2 * 5) j.val)

private def intDiagProdPrefixW16 (N : Nat) (U : Fin N -> Fin N -> Int) : Nat -> Int
  | 0 => 1
  | k + 1 =>
    if h : k < N then intDiagProdPrefixW16 N U k * U ⟨k, h⟩ ⟨k, h⟩
    else intDiagProdPrefixW16 N U k

private theorem intDet_mul_upper_tri_w16 (N : Nat) (A U : Fin N -> Fin N -> Int)
    (hupper : ∀ r c : Fin N, c.val < r.val -> U r c = 0) :
    intDet N (fun i j => intSumPrefix N (fun r => A i r * U r j) N) =
      intDiagProdPrefixW16 N U N * intDet N A := by
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
      intDet N (M_stage 0) = intDiagProdPrefixW16 N U k * intDet N (M_stage k) := by
    intro k hk; induction k with
    | zero => simp [intDiagProdPrefixW16]
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
      simp only [intDiagProdPrefixW16, hk'_lt, dite_true]
      exact (Int.mul_assoc (intDiagProdPrefixW16 N U k') (U jk jk) _).symm
  rw [h0_eq, hstep N (Nat.le_refl N), hN_eq]

private theorem intDet_lower_tri_w16 :
    ∀ (N : Nat) (L_mat : Fin N -> Fin N -> Int),
      (∀ r c : Fin N, r.val < c.val -> L_mat r c = 0) ->
      intDet N L_mat = intDiagProdPrefixW16 N L_mat N
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
    rw [intDet_lower_tri_w16 N (intSubMat L_mat z0) hsub_low]
    have hprod_shift : ∀ k : Nat, k ≤ N ->
        L_mat z0 z0 * intDiagProdPrefixW16 N (intSubMat L_mat z0) k =
          intDiagProdPrefixW16 (N + 1) L_mat (k + 1) := by
      intro k hk; induction k with
      | zero =>
        simp only [intDiagProdPrefixW16, Nat.zero_lt_succ, dite_true, Int.one_mul, Int.mul_one]
        rfl
      | succ k' ih =>
        have hk'_N : k' < N := hk
        have hk1_N1 : k' + 1 < N + 1 := Nat.succ_lt_succ hk
        simp only [intDiagProdPrefixW16, hk'_N, hk1_N1, dite_true, ← Int.mul_assoc, ih (Nat.le_of_lt hk)]
        simp only [intSubMat, skipFinIdx, z0, Nat.not_lt_zero, ite_false]
    exact hprod_shift N (Nat.le_refl N)

set_option maxRecDepth 65536 in
private theorem rect_8x8_251_overlap_certs :
    confluentFactorAllU 4 2 1 = 66072707334144 ∧
    (2 ^ (2 * 1) - 1) ^ (2 * (4 - 2)) = 81 ∧
    Nat.gcd 66072707334144 81 = 81 ∧
    Nat.lcm 66072707334144 81 = 66072707334144 ∧
    (∀ r c : Fin 8, c.val < r.val -> v8OverlapMatW16 r c = 0) ∧
    (∀ r c : Fin 8, r.val < c.val -> m8OverlapMatW16 r c = 0) ∧
    (∀ i j : Fin 8, intSumPrefix 8 (fun r => a8Newton251W16 i r * v8OverlapMatW16 r j) 8 = m8OverlapMatW16 i j) ∧
    intDiagProdPrefixW16 8 m8OverlapMatW16 8 =
      intDiagProdPrefixW16 8 v8OverlapMatW16 8 * (-2220582109184) ∧
    intDiagProdPrefixW16 8 v8OverlapMatW16 8 > 0 := by decide

/--
  Theorem W16.2a (`laurent_rect_all_U_gt_T_joint_row_col_lcm_and_reduced_bound`,
  `zero custom axioms`):
  General Rectangular `∀ U > T ≥ 1` Row-Side `(2^(W * u) - 1)^(T * (U - T))` Vandermonde
  Divisibility, Universal `(U * T) × (U * T)` Joint `Nat.lcm` Row+Column Confluent Divisibility,
  Extra Row-Factor Newton-Quotient Divisibility & Joint-LCM Reduced Majorant Bound, + `8 × 8`
  `(T = 2, U = 4)` Row-Column Overlap Certificate (`Branch P3.2`–`P3.3`, witness
  `LAURENT_RECT_8X8_T2U4_OVERLAP_AND_9X9_81_16_RESONANT`, `W16_H2`).
-/
theorem laurent_rect_all_U_gt_T_joint_row_col_lcm_and_reduced_bound :
    (∀ (U T W K u : Nat), T ≥ 1 -> U > T -> W ≥ 1 -> u ≥ 1 ->
      let M0 : Fin (U * T) -> Fin (U * T) -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (laurentRectRows U T i).1 (laurentRectRows U T i).2
          (laurentColsAllU U T u j).1 (laurentColsAllU U T u j).2 : Int)
      let colFac := confluentFactorAllU U T u
      let rowFac := (2 ^ (W * u) - 1) ^ (T * (U - T))
      let jointLcm := Nat.lcm colFac rowFac
      ((rowFac : Nat) : Int) ∣ intDet (U * T) M0 ∧
      ((jointLcm : Nat) : Int) ∣ intDet (U * T) M0 ∧
      (3 ^ W < 2 ^ K ->
        let M_W := laurentInterpMat W K (U * T) (laurentRectRows U T) (laurentColsAllU U T (W * u))
        ((2 ^ K - 3 ^ W : Nat) : Int) ∣ (intDet (U * T) M_W - intDet (U * T) M0))) ∧
    (∀ (U T W K u X_max : Nat), T ≥ 1 -> U > T -> W ≥ 1 -> u ≥ 1 -> X_max ≥ U * T ->
      (∀ i : Fin (U * T), (laurentRectRows U T i).1 * W + (laurentRectRows U T i).2 * K ≤ X_max) ->
      let M0 : Fin (U * T) -> Fin (U * T) -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (laurentRectRows U T i).1 (laurentRectRows U T i).2
          (laurentColsAllU U T u j).1 (laurentColsAllU U T u j).2 : Int)
      let A_newton : Fin (U * T) -> Fin (U * T) -> Int := fun i j =>
        Int.ofNat (mixedNewtonCoeffAllU T (2 ^ u)
          ((laurentRectRows U T i).1 * W + (laurentRectRows U T i).2 * K) j.val)
      let colFac := confluentFactorAllU U T u
      let rowFac := (2 ^ (W * u) - 1) ^ (T * (U - T))
      let jointLcm := Nat.lcm colFac rowFac
      let extraRowFac := rowFac / Nat.gcd colFac rowFac
      let newtonProd := colBoundProdPrefix (U * T)
        (fun j => mixedNewtonCoeffAllU T (2 ^ u) X_max j.val) (U * T)
      jointLcm = colFac * extraRowFac ∧
      extraRowFac ∣ (intDet (U * T) A_newton).natAbs ∧
      ((intDet (U * T) M0).natAbs / jointLcm) * jointLcm = (intDet (U * T) M0).natAbs ∧
      (intDet (U * T) M0).natAbs / jointLcm ≤ (natFact (U * T) * newtonProd) / extraRowFac) ∧
    (let M0_8_251 : Fin 8 -> Fin 8 -> Int := fun i j =>
       (laurentZeroGapIntEntry 2 5 (laurentRectRows 4 2 i).1 (laurentRectRows 4 2 i).2
         (laurentColsAllU 4 2 1 j).1 (laurentColsAllU 4 2 1 j).2 : Int)
     confluentFactorAllU 4 2 1 = 66072707334144 ∧
     Nat.gcd (confluentFactorAllU 4 2 1) ((2 ^ (2 * 1) - 1) ^ (2 * (4 - 2))) = 81 ∧
     Nat.lcm (confluentFactorAllU 4 2 1) ((2 ^ (2 * 1) - 1) ^ (2 * (4 - 2))) = 66072707334144 ∧
     intDet 8 M0_8_251 = (66072707334144 : Int) * (-2220582109184) ∧
     ¬ (((66072707334144 * 81 : Nat) : Int) ∣ intDet 8 M0_8_251)) := by
  have hw15_col := laurent_all_blocks_arbitrary_U_confluent_divisibility_and_majorant
  -- Core row-Vandermonde proof for `∀ U > T ≥ 1`:
  have hrow_vand : ∀ (U T W K u : Nat), T ≥ 1 -> U > T -> W ≥ 1 -> u ≥ 1 ->
      let M0 : Fin (U * T) -> Fin (U * T) -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (laurentRectRows U T i).1 (laurentRectRows U T i).2
          (laurentColsAllU U T u j).1 (laurentColsAllU U T u j).2 : Int)
      (((2 ^ (W * u) - 1) ^ (T * (U - T)) : Nat) : Int) ∣ intDet (U * T) M0 := by
    intro U T W K u hT hUT hW hu; dsimp only
    let N := U * T
    have hU_pos : U ≥ 2 := by omega
    let P_row := 2 ^ (W * u)
    have hWu_pos : W * u ≥ 1 := Nat.mul_le_mul hW hu
    have hP_ge2 : P_row ≥ 2 := by dsimp [P_row]; simpa using pow2_mono_nat hWu_pos
    let d : Int := ((P_row - 1 : Nat) : Int)
    let M0 : Fin N -> Fin N -> Int := fun i j =>
      (laurentZeroGapIntEntry W K (laurentRectRows U T i).1 (laurentRectRows U T i).2
        (laurentColsAllU U T u j).1 (laurentColsAllU U T u j).2 : Int)
    let B0 : Fin N -> Fin N -> Int := fun i j =>
      let r := i.val % U
      let s := i.val / U
      let col := laurentColsAllU U T u j
      ((laurentInterpBinom (r * W + s * K) col.1 * 2 ^ ((s * K) * col.2) : Nat) : Int)
    -- Step 1: `d ∣ (M0 i j - B0 i j)` for all `i, j`:
    have hpow_sub1_dvd : ∀ m : Nat, (P_row - 1) ∣ (P_row ^ m - 1) := by
      intro m; induction m with
      | zero => exact ⟨0, by simp⟩
      | succ m' ih =>
        rcases ih with ⟨q, hq⟩
        refine ⟨P_row ^ m' + q, ?_⟩
        rw [Nat.pow_succ, Nat.mul_add]
        have hp_pos : P_row ^ m' ≥ 1 := nat_pow_pos_of_pos P_row (by omega) m'
        have hle_pm : P_row ^ m' ≤ P_row ^ m' * P_row := Nat.le_mul_of_pos_right _ (by omega)
        have hm1 : (P_row - 1) * P_row ^ m' = P_row ^ m' * P_row - P_row ^ m' := by
          rw [Nat.sub_mul, Nat.one_mul, Nat.mul_comm]
        omega
    have hMB0_congr : ∀ i j : Fin N, d ∣ (M0 i j - B0 i j) := by
      intro i j
      let r := i.val % U
      let s := i.val / U
      let t := (laurentColsAllU U T u j).1
      let uc := (laurentColsAllU U T u j).2
      have huc_u : u ∣ uc := ⟨j.val / T, by dsimp only [uc]; unfold laurentColsAllU; dsimp; rw [Nat.mul_comm]⟩
      rcases huc_u with ⟨m, hm_uc⟩
      have hexp : (r * W + s * K) * uc = (s * K) * uc + (W * u) * (r * m) := by
        rw [hm_uc, Nat.add_mul]
        have e : (r * W) * (u * m) = (W * u) * (r * m) := by ac_rfl
        rw [e, Nat.add_comm]
      have hp_split : 2 ^ ((r * W + s * K) * uc) = 2 ^ ((s * K) * uc) * P_row ^ (r * m) := by
        rw [hexp, Nat.pow_add, pow_pow_eq_mul_w5 2 (W * u) (r * m)]
      rcases hpow_sub1_dvd (r * m) with ⟨q, hq⟩
      have hp_ge1 : P_row ^ (r * m) ≥ 1 := nat_pow_pos_of_pos P_row (by omega) (r * m)
      let c_front := laurentInterpBinom (r * W + s * K) t * 2 ^ ((s * K) * uc)
      have hdiff_nat : laurentInterpBinom (r * W + s * K) t * 2 ^ ((r * W + s * K) * uc) =
          c_front + (P_row - 1) * (c_front * q) := by
        rw [hp_split, ← Nat.mul_assoc, show P_row ^ (r * m) = 1 + (P_row ^ (r * m) - 1) by omega,
            hq, Nat.mul_add c_front 1 ((P_row - 1) * q), Nat.mul_one]
        ac_rfl
      change d ∣ (((laurentInterpBinom (r * W + s * K) t * 2 ^ ((r * W + s * K) * uc) : Nat) : Int) -
        ((c_front : Nat) : Int))
      rw [hdiff_nat, Int.natCast_add, Int.natCast_mul]
      refine ⟨((c_front * q : Nat) : Int), ?_⟩
      dsimp [d]; omega
    -- Step 2: Single-block downward sweep preserves `intDet`, preserves `d`-congruence,
    --         leaves other blocks untouched, and updates block `s` rows `r ≥ p + 1` to `A(r) - A(r - 1)`:
    have hsweep_blk : ∀ (s p cnt : Nat) (A B : Fin N -> Fin N -> Int),
        p + 1 + cnt ≤ U -> s < T ->
        (∀ i j : Fin N, d ∣ (A i j - B i j)) ->
        intDet N (sweepSingleBlockW16 N U s p cnt A) = intDet N A ∧
        (∀ i j : Fin N, d ∣ (sweepSingleBlockW16 N U s p cnt A i j -
                             sweepSingleBlockW16 N U s p cnt B i j)) ∧
        (∀ i j : Fin N,
          sweepSingleBlockW16 N U s p cnt B i j =
            if s * U + (p + 1) ≤ i.val ∧ i.val < s * U + (p + 1 + cnt) then
              B i j - B ⟨i.val - 1, by omega⟩ j
            else B i j) := by
      intro s p cnt; induction cnt with
      | zero =>
        intro A B _ _ hcongr
        refine ⟨rfl, hcongr, fun i j => ?_⟩
        simp only [sweepSingleBlockW16, Nat.add_zero]
        have hfalse : ¬ (s * U + (p + 1) ≤ i.val ∧ i.val < s * U + (p + 1)) := by omega
        rw [ite_false_of_w10 hfalse]
      | succ cnt' ih =>
        intro A B hle_U hsT hcongr
        let r_top := p + 1 + cnt'
        have hlt_N : s * U + r_top < N := by
          have h1 : (s + 1) * U ≤ T * U := Nat.mul_le_mul_right U hsT
          have h2 : T * U = N := Nat.mul_comm T U
          rw [Nat.add_mul, Nat.one_mul] at h1; omega
        have hr_pos : s * U + r_top ≥ 1 := by omega
        let k_prev := s * U + r_top - 1
        have hk_succ : k_prev + 1 = s * U + r_top := by omega
        let A1 : Fin N -> Fin N -> Int := fun i j =>
          if i.val = s * U + r_top then A i j - A ⟨k_prev, by omega⟩ j else A i j
        let B1 : Fin N -> Fin N -> Int := fun i j =>
          if i.val = s * U + r_top then B i j - B ⟨k_prev, by omega⟩ j else B i j
        have hdet1 : intDet N A1 = intDet N A := by
          have heq_fn : A1 = (fun i j => if i.val = k_prev + 1 then A i j - A ⟨k_prev, by omega⟩ j else A i j) := by
            funext i j; dsimp [A1]; rw [hk_succ]
          rw [heq_fn]
          exact intDet_sub_prev_row_eq_w16 k_prev N (by omega) A
        have hcongr1 : ∀ i j : Fin N, d ∣ (A1 i j - B1 i j) := by
          intro i j; dsimp only [A1, B1]
          by_cases hi : i.val = s * U + r_top
          · simp only [hi, ite_true]
            rcases hcongr i j with ⟨q1, hq1⟩
            rcases hcongr ⟨k_prev, by omega⟩ j with ⟨q2, hq2⟩
            exact ⟨q1 - q2, by rw [Int.mul_sub]; omega⟩
          · simp only [hi, ite_false]; exact hcongr i j
        rcases ih A1 B1 (by omega) hsT hcongr1 with ⟨ih_det, ih_congr, ih_B⟩
        have hsw_A : sweepSingleBlockW16 N U s p (cnt' + 1) A = sweepSingleBlockW16 N U s p cnt' A1 := by
          conv => lhs; unfold sweepSingleBlockW16
          dsimp only; rw [dite_pos_w16 hlt_N]
        have hsw_B : sweepSingleBlockW16 N U s p (cnt' + 1) B = sweepSingleBlockW16 N U s p cnt' B1 := by
          conv => lhs; unfold sweepSingleBlockW16
          dsimp only; rw [dite_pos_w16 hlt_N]
        rw [hsw_A, hsw_B]
        refine ⟨ih_det.trans hdet1, ih_congr, fun i j => ?_⟩
        rw [ih_B i j]
        by_cases hlow : s * U + (p + 1) ≤ i.val ∧ i.val < s * U + (p + 1 + cnt')
        · have hlow2 : s * U + (p + 1) ≤ i.val ∧ i.val < s * U + (p + 1 + (cnt' + 1)) := by omega
          rw [ite_true_of_w10 hlow, ite_true_of_w10 hlow2]
          have hne1 : i.val ≠ s * U + r_top := by dsimp [r_top]; omega
          have hne2 : i.val - 1 ≠ s * U + r_top := by dsimp [r_top]; omega
          dsimp [B1]; rw [ite_false_of_w10 hne1, ite_false_of_w10 hne2]
        · rw [ite_false_of_w10 hlow]
          by_cases htop : i.val = s * U + r_top
          · have hlow2 : s * U + (p + 1) ≤ i.val ∧ i.val < s * U + (p + 1 + (cnt' + 1)) := by
              dsimp [r_top] at htop; omega
            rw [ite_true_of_w10 hlow2]
            dsimp [B1]; rw [ite_true_of_w10 htop]
            have hf_eq : (⟨k_prev, by omega⟩ : Fin N) = ⟨i.val - 1, by omega⟩ :=
              Fin.ext (by dsimp [k_prev]; omega)
            rw [hf_eq]
          · have hlow2 : ¬ (s * U + (p + 1) ≤ i.val ∧ i.val < s * U + (p + 1 + (cnt' + 1))) := by
              dsimp [r_top] at htop; omega
            rw [ite_false_of_w10 hlow2]
            dsimp [B1]; rw [ite_false_of_w10 htop]
    -- All-blocks pass `p`:
    have hsweep_pass : ∀ (p s_lim : Nat) (A B : Fin N -> Fin N -> Int),
        p < T -> s_lim ≤ T ->
        (∀ i j : Fin N, d ∣ (A i j - B i j)) ->
        intDet N (sweepAllBlocksPassW16 N U p s_lim A) = intDet N A ∧
        (∀ i j : Fin N, d ∣ (sweepAllBlocksPassW16 N U p s_lim A i j -
                             sweepAllBlocksPassW16 N U p s_lim B i j)) ∧
        (∀ i j : Fin N,
          sweepAllBlocksPassW16 N U p s_lim B i j =
            if hcond : i.val / U < s_lim ∧ p + 1 ≤ i.val % U then
              B i j - B ⟨i.val - 1, by
                have hmod := hcond.2
                have hge : i.val ≥ i.val % U := Nat.mod_le i.val U
                omega⟩ j
            else B i j) := by
      intro p s_lim; induction s_lim with
      | zero =>
        intro A B _ _ hcongr
        refine ⟨rfl, hcongr, fun i j => ?_⟩
        simp only [sweepAllBlocksPassW16, Nat.not_lt_zero, false_and, dite_false]
      | succ s' ih =>
        intro A B hpT hs_le hcongr
        rcases ih A B hpT (Nat.le_of_lt hs_le) hcongr with ⟨ih_det, ih_congr, ih_B⟩
        let A_prev := sweepAllBlocksPassW16 N U p s' A
        let B_prev := sweepAllBlocksPassW16 N U p s' B
        have hcnt_eq : p + 1 + (U - (p + 1)) = U := by omega
        rcases hsweep_blk s' p (U - (p + 1)) A_prev B_prev (by omega) hs_le ih_congr with
          ⟨hdet_s, hcongr_s, hB_s⟩
        simp only [sweepAllBlocksPassW16]
        refine ⟨hdet_s.trans ih_det, hcongr_s, fun i j => ?_⟩
        rw [hB_s i j, hcnt_eq]
        have hdiv_mod : i.val = (i.val / U) * U + i.val % U := by
          have h := (Nat.div_add_mod i.val U).symm
          rwa [Nat.mul_comm U (i.val / U)] at h
        have hmod_lt : i.val % U < U := Nat.mod_lt i.val (by omega)
        by_cases h_in_s : s' * U + (p + 1) ≤ i.val ∧ i.val < s' * U + U
        · rw [ite_true_of_w10 h_in_s]
          have hq_eq : i.val / U = s' := by
            by_cases hlt_q : i.val / U < s'
            · have hm : (i.val / U + 1) * U ≤ s' * U := Nat.mul_le_mul_right U hlt_q
              rw [Nat.add_mul, Nat.one_mul] at hm; omega
            · by_cases hgt_q : s' < i.val / U
              · have hm : (s' + 1) * U ≤ (i.val / U) * U := Nat.mul_le_mul_right U hgt_q
                rw [Nat.add_mul, Nat.one_mul] at hm; omega
              · omega
          have hr_ge : p + 1 ≤ i.val % U := by rw [hq_eq] at hdiv_mod; omega
          have hcond_s1 : i.val / U < s' + 1 ∧ p + 1 ≤ i.val % U := ⟨by omega, hr_ge⟩
          rw [dite_pos_w16 hcond_s1]
          have hc_prev1 : ¬ (i.val / U < s' ∧ p + 1 ≤ i.val % U) := by omega
          have hi1_div : (i.val - 1) / U = s' := by
            have hi1_eq : i.val - 1 = (i.val % U - 1) + U * s' := by
              rw [hq_eq, Nat.mul_comm s' U] at hdiv_mod; omega
            rw [hi1_eq, Nat.add_mul_div_left (i.val % U - 1) s' (by omega : 0 < U),
                Nat.div_eq_of_lt (by omega : i.val % U - 1 < U), Nat.zero_add]
          have hc_prev2 : ¬ ((i.val - 1) / U < s' ∧ p + 1 ≤ (i.val - 1) % U) := by omega
          dsimp only [B_prev]
          rw [ih_B i j, dite_neg_w16 hc_prev1,
              ih_B ⟨i.val - 1, by have := i.isLt; omega⟩ j, dite_neg_w16 hc_prev2]
        · rw [ite_false_of_w10 h_in_s]
          dsimp only [B_prev]
          rw [ih_B i j]
          by_cases hlt_s : i.val / U < s'
          · by_cases hr_ge : p + 1 ≤ i.val % U
            · rw [dite_pos_w16 ⟨hlt_s, hr_ge⟩, dite_pos_w16 ⟨by omega, hr_ge⟩]
            · rw [dite_neg_w16 (by omega), dite_neg_w16 (by omega)]
          · have hnot_s1 : ¬ (i.val / U < s' + 1 ∧ p + 1 ≤ i.val % U) := by
              rintro ⟨hlt1, hr_ge⟩
              have hq_eq : i.val / U = s' := by omega
              exact h_in_s ⟨by rw [hq_eq] at hdiv_mod; omega, by rw [hq_eq] at hdiv_mod; omega⟩
            rw [dite_neg_w16 (by omega), dite_neg_w16 hnot_s1]
    -- Step 3: Multi-pass induction `p = 0 .. T`:
    let F_base (s : Nat) (j : Fin N) (r : Nat) : Int :=
      let col := laurentColsAllU U T u j
      ((laurentInterpBinom (r * W + s * K) col.1 : Nat) : Int) *
        ((2 ^ ((s * K) * col.2) : Nat) : Int)
    have hmulti : ∀ p : Nat, p ≤ T ->
        intDet N (sweepMultiPassW16 N U T p M0) = intDet N M0 ∧
        (∀ i j : Fin N, d ∣ (sweepMultiPassW16 N U T p M0 i j -
                             sweepMultiPassW16 N U T p B0 i j)) ∧
        (∀ i j : Fin N, p ≤ i.val % U ->
          sweepMultiPassW16 N U T p B0 i j = bwdDiffAtW16 p (F_base (i.val / U) j) (i.val % U)) := by
      intro p; induction p with
      | zero =>
        intro _
        refine ⟨rfl, hMB0_congr, fun i j _ => ?_⟩
        simp only [sweepMultiPassW16, bwdDiffAtW16, B0, F_base, Int.natCast_mul]
      | succ p' ih =>
        intro hp_le
        rcases ih (Nat.le_of_lt hp_le) with ⟨ih_det, ih_congr, ih_B⟩
        rcases hsweep_pass p' T (sweepMultiPassW16 N U T p' M0) (sweepMultiPassW16 N U T p' B0)
          hp_le (Nat.le_refl T) ih_congr with ⟨hd_s, hc_s, hB_s⟩
        simp only [sweepMultiPassW16]
        refine ⟨hd_s.trans ih_det, hc_s, fun i j hr_ge => ?_⟩
        have hs_lt : i.val / U < T := by
          by_cases hlt : i.val / U < T
          · exact hlt
          · have hm : T * U ≤ (i.val / U) * U := Nat.mul_le_mul_right U (by omega)
            have hle_i : (i.val / U) * U ≤ i.val := Nat.div_mul_le_self i.val U
            have hiN : i.val < U * T := i.isLt
            rw [Nat.mul_comm T U] at hm; omega
        have hcond_cur : i.val / U < T ∧ p' + 1 ≤ i.val % U := ⟨hs_lt, hr_ge⟩
        rw [hB_s i j, dite_pos_w16 hcond_cur]
        have hi_decomp : i.val = U * (i.val / U) + i.val % U := (Nat.div_add_mod i.val U).symm
        have hmod_lt : i.val % U < U := Nat.mod_lt i.val (by omega)
        have hi1_eq : i.val - 1 = (i.val % U - 1) + U * (i.val / U) := by omega
        have hi1_div : (i.val - 1) / U = i.val / U := by
          rw [hi1_eq, Nat.add_mul_div_left (i.val % U - 1) (i.val / U) (by omega : 0 < U),
              Nat.div_eq_of_lt (by omega : i.val % U - 1 < U), Nat.zero_add]
        have hi1_mod : (i.val - 1) % U = i.val % U - 1 := by
          rw [hi1_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
        rw [ih_B i j (by omega),
            ih_B ⟨i.val - 1, by have := i.isLt; omega⟩ j (by dsimp; rw [hi1_mod]; omega)]
        dsimp only
        rw [hi1_div, hi1_mod]
        rfl
    rcases hmulti T (Nat.le_refl T) with ⟨hdet_T, hcongr_T, hB_T⟩
    let M_T := sweepMultiPassW16 N U T T M0
    let B_T := sweepMultiPassW16 N U T T B0
    have hBT_zero : ∀ i j : Fin N, T ≤ i.val % U -> B_T i j = 0 := by
      intro i j hr_ge
      dsimp only [B_T]
      rw [hB_T i j hr_ge]
      dsimp only [F_base]
      rw [bwdDiffAt_mul_const_w16]
      have ht_lt : (laurentColsAllU U T u j).1 < T := by
        unfold laurentColsAllU; exact Nat.mod_lt j.val (by omega)
      rw [bwdDiffAt_binom_vanish_w16 W T ((i.val / U) * K) (laurentColsAllU U T u j).1 (i.val % U)
            ht_lt hr_ge, Int.zero_mul]
    let m_row : Fin N -> Int := fun i => if T ≤ i.val % U then d else 1
    have hrow_dvd : ∀ i j : Fin N, m_row i ∣ M_T i j := by
      intro i j; dsimp only [m_row]
      by_cases hr : T ≤ i.val % U
      · rw [ite_true_of_w10 hr]
        have hc := hcongr_T i j
        change d ∣ (M_T i j - B_T i j) at hc
        rwa [hBT_zero i j hr, Int.sub_zero] at hc
      · rw [ite_false_of_w10 hr]; exact ⟨M_T i j, (Int.one_mul _).symm⟩
    have hprod_dvd : intRowFactorProdPrefixW16 N m_row N ∣ intDet N M0 := by
      rw [← hdet_T]
      exact intDet_row_factors_dvd_w16 N m_row M_T hrow_dvd
    -- Evaluate `intRowFactorProdPrefixW16 N m_row N = (((P_row - 1) ^ (T * (U - T)) : Nat) : Int)`:
    have hprod_eval : ∀ s : Nat, s ≤ T ->
        intRowFactorProdPrefixW16 N m_row (s * U) =
          (((P_row - 1) ^ (s * (U - T)) : Nat) : Int) := by
      intro s hs; induction s with
      | zero => simp [intRowFactorProdPrefixW16]
      | succ s' ih =>
        have hblk_step : ∀ r : Nat, r ≤ U ->
            intRowFactorProdPrefixW16 N m_row (s' * U + r) =
              intRowFactorProdPrefixW16 N m_row (s' * U) *
                (((P_row - 1) ^ (r - T) : Nat) : Int) := by
          intro r hr; induction r with
          | zero => simp
          | succ r' ihr =>
            have hlt_n : s' * U + r' < N := by
              have h1 : (s' + 1) * U ≤ T * U := Nat.mul_le_mul_right U hs
              rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm T U] at h1; omega
            rw [Nat.add_succ]
            simp only [intRowFactorProdPrefixW16, hlt_n, dite_true, ihr (Nat.le_of_lt hr)]
            have hmod_r : (s' * U + r') % U = r' := by
              rw [Nat.add_comm, Nat.mul_comm s' U, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
            dsimp only [m_row]; rw [hmod_r]
            by_cases hrT : T ≤ r'
            · rw [ite_true_of_w10 hrT, show r' + 1 - T = (r' - T) + 1 by omega,
                  Nat.pow_succ, Int.natCast_mul, Int.mul_assoc]
            · rw [ite_false_of_w10 hrT, show r' + 1 - T = 0 by omega,
                  show r' - T = 0 by omega, Nat.pow_zero, Int.natCast_one, Int.mul_one, Int.mul_one]
        rw [Nat.succ_mul s' U, hblk_step U (Nat.le_refl U), ih (Nat.le_of_lt hs),
            ← Int.natCast_mul, ← Nat.pow_add, Nat.succ_mul s' (U - T)]
    have hN_eq : T * U = N := Nat.mul_comm T U
    have hprod_N := hprod_eval T (Nat.le_refl T)
    rw [hN_eq] at hprod_N
    rw [hprod_N] at hprod_dvd
    exact hprod_dvd
  -- Helper: `(a : Int) ∣ z ↔ a ∣ z.natAbs`:
  have hint_dvd_iff_natAbs : ∀ (a : Nat) (z : Int), ((a : Nat) : Int) ∣ z ↔ a ∣ z.natAbs := by
    intro a z; constructor
    · rintro ⟨q, hq⟩
      refine ⟨q.natAbs, ?_⟩
      rw [hq, Int.natAbs_mul, Int.natAbs_natCast]
    · rintro ⟨q, hq⟩
      by_cases hz : 0 ≤ z
      · refine ⟨(q : Int), ?_⟩
        have hz_eq : ((z.natAbs : Nat) : Int) = z := Int.natAbs_of_nonneg hz
        rw [← hz_eq, hq, Int.natCast_mul]
      · refine ⟨-(q : Int), ?_⟩
        have hz_eq : -((z.natAbs : Nat) : Int) = z := by omega
        rw [← hz_eq, hq, Int.natCast_mul, Int.mul_neg]
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1:
    intro U T W K u hT hUT hW hu; dsimp only
    have hU2 : U ≥ 2 := by omega
    have hcol_dvd := (hw15_col.1 U W K T u (laurentRectRows U T) hU2 hT hu).2
    have hrow_dvd := hrow_vand U T W K u hT hUT hW hu
    have hlcm_nat : Nat.lcm (confluentFactorAllU U T u) ((2 ^ (W * u) - 1) ^ (T * (U - T))) ∣
        (intDet (U * T) (fun i j =>
          (laurentZeroGapIntEntry W K (laurentRectRows U T i).1 (laurentRectRows U T i).2
            (laurentColsAllU U T u j).1 (laurentColsAllU U T u j).2 : Int))).natAbs :=
      Nat.lcm_dvd ((hint_dvd_iff_natAbs _ _).mp hcol_dvd) ((hint_dvd_iff_natAbs _ _).mp hrow_dvd)
    refine ⟨hrow_dvd, (hint_dvd_iff_natAbs _ _).mpr hlcm_nat, fun hlt_wk => ?_⟩
    -- Congruence `intDet (M_W) ≡ intDet (M0) mod (2^K - 3^W)` via Wave 7:
    have hcong := (laurent_wdilated_zero_gap_entry_and_det_congruence.2
      W K (U * T) (laurentRectRows U T) (laurentColsAllU U T u) hlt_wk).1
    have hMW_eq : (fun i j : Fin (U * T) =>
        (laurentInterpEntry W K (laurentRectRows U T i).1 (laurentRectRows U T i).2
          (laurentColsAllU U T u j).1 (W * (laurentColsAllU U T u j).2) : Int)) =
        laurentInterpMat W K (U * T) (laurentRectRows U T) (laurentColsAllU U T (W * u)) := by
      funext i j; unfold laurentInterpMat
      have hcol_Wu : ((laurentColsAllU U T u j).1, W * (laurentColsAllU U T u j).2) =
          laurentColsAllU U T (W * u) j := by
        unfold laurentColsAllU; dsimp; refine Prod.ext rfl ?_; ac_rfl
      rw [← hcol_Wu]
    rw [hMW_eq] at hcong
    rcases hcong with ⟨c_q, hc_q⟩
    exact ⟨-c_q, by rw [Int.mul_neg]; omega⟩
  · -- Part 2: Joint-LCM reduced majorant bound & `extraRowFac` Newton-quotient divisibility:
    intro U T W K u X_max hT hUT hW hu hX_ge hX_rows; dsimp only
    have hU2 : U ≥ 2 := by omega
    let colFac := confluentFactorAllU U T u
    let rowFac := (2 ^ (W * u) - 1) ^ (T * (U - T))
    let jointLcm := Nat.lcm colFac rowFac
    let g := Nat.gcd colFac rowFac
    let extraRowFac := rowFac / g
    let M0 : Fin (U * T) -> Fin (U * T) -> Int := fun i j =>
      (laurentZeroGapIntEntry W K (laurentRectRows U T i).1 (laurentRectRows U T i).2
        (laurentColsAllU U T u j).1 (laurentColsAllU U T u j).2 : Int)
    let A_newton : Fin (U * T) -> Fin (U * T) -> Int := fun i j =>
      Int.ofNat (mixedNewtonCoeffAllU T (2 ^ u)
        ((laurentRectRows U T i).1 * W + (laurentRectRows U T i).2 * K) j.val)
    let newtonProd := colBoundProdPrefix (U * T)
      (fun j => mixedNewtonCoeffAllU T (2 ^ u) X_max j.val) (U * T)
    -- `colFac ≥ 1` and `rowFac ≥ 1`:
    have hcol_pos : colFac ≥ 1 := by
      have h2u_pos : 2 ^ u ≥ 1 := nat_pow_pos_of_pos 2 (by decide) u
      have hblk_pos : ∀ m : Nat, confluentFactorAllUAux T (2 ^ u) m ≥ 1 := by
        intro m; induction m with
        | zero => exact Nat.le_refl 1
        | succ m' ih =>
          have hcf_pos : confluentBlockFactor T (2 ^ u) m' ≥ 1 := by
            unfold confluentBlockFactor
            have hdiff_pos : ∀ k : Nat, k ≤ m' -> blockNodeDiffProd (2 ^ u) m' k ≥ 1 := by
              intro k hk; induction k with
              | zero => exact Nat.le_refl 1
              | succ k' ihk =>
                simp only [blockNodeDiffProd]
                have hp_lt : (2 ^ u) ^ k' < (2 ^ u) ^ m' := by
                  have h2u_gt1 : 2 ^ u ≥ 2 := by simpa using pow2_mono_nat hu
                  have hle1 : (2 ^ u) ^ (k' + 1) ≤ (2 ^ u) ^ m' :=
                    nat_pow_mono_exp_pos (2 ^ u) (k' + 1) m' h2u_pos hk
                  rw [Nat.pow_succ] at hle1
                  have hk_pos : (2 ^ u) ^ k' ≥ 1 := nat_pow_pos_of_pos _ h2u_pos k'
                  have hm2 : (2 ^ u) ^ k' * 2 ≤ (2 ^ u) ^ k' * (2 ^ u) :=
                    Nat.mul_le_mul_left _ h2u_gt1
                  omega
                exact Nat.mul_le_mul (ihk (Nat.le_of_lt hk)) (by omega : 1 ≤ (2 ^ u) ^ m' - (2 ^ u) ^ k')
            exact Nat.mul_le_mul
              (nat_pow_pos_of_pos (2 ^ u) h2u_pos (m' * triNumNat T))
              (nat_pow_pos_of_pos _ (hdiff_pos m' (Nat.le_refl m')) (T * T))
          exact Nat.mul_le_mul ih hcf_pos
      exact hblk_pos U
    have hWu_pos : W * u ≥ 1 := Nat.mul_le_mul hW hu
    have hP_ge2 : 2 ^ (W * u) ≥ 2 := by simpa using pow2_mono_nat hWu_pos
    have hrow_pos : rowFac ≥ 1 := nat_pow_pos_of_pos (2 ^ (W * u) - 1) (by omega) (T * (U - T))
    have hg_pos : g ≥ 1 := Nat.gcd_pos_of_pos_left rowFac hcol_pos
    have hextra_pos : extraRowFac ≥ 1 := by
      rcases Nat.gcd_dvd_right colFac rowFac with ⟨q, hq⟩
      have hdiv : rowFac / g = q := by
        rw [hq, Nat.mul_comm g q, Nat.mul_div_cancel q hg_pos]
      cases q with
      | zero => rw [Nat.mul_zero] at hq; omega
      | succ _ => dsimp [extraRowFac]; omega
    have hlcm_eq : jointLcm = colFac * extraRowFac := by
      have hgl := Nat.gcd_mul_lcm colFac rowFac
      rcases Nat.gcd_dvd_right colFac rowFac with ⟨q, hq⟩
      have hextra_q : extraRowFac = q := by
        dsimp [extraRowFac]; rw [hq, Nat.mul_comm g q, Nat.mul_div_cancel q hg_pos]
      have hmul_g : g * jointLcm = g * (colFac * extraRowFac) := by
        dsimp [g, jointLcm]
        rw [hgl, hextra_q]
        conv => rhs; rw [← Nat.mul_assoc g colFac q, Nat.mul_comm g colFac, Nat.mul_assoc colFac g q, ← hq]
      exact Nat.eq_of_mul_eq_mul_left hg_pos hmul_g
    have hdet_fac := (hw15_col.1 U W K T u (laurentRectRows U T) hU2 hT hu).1
    have hrow_dvd := hrow_vand U T W K u hT hUT hW hu
    have hlcm_nat : jointLcm ∣ (intDet (U * T) M0).natAbs :=
      Nat.lcm_dvd
        ((hint_dvd_iff_natAbs _ _).mp (hw15_col.1 U W K T u (laurentRectRows U T) hU2 hT hu).2)
        ((hint_dvd_iff_natAbs _ _).mp hrow_dvd)
    have hM0_abs : (intDet (U * T) M0).natAbs = colFac * (intDet (U * T) A_newton).natAbs := by
      change intDet (U * T) M0 = Int.ofNat colFac * intDet (U * T) A_newton at hdet_fac
      rw [hdet_fac, Int.natAbs_mul]; rfl
    have hextra_dvd_A : extraRowFac ∣ (intDet (U * T) A_newton).natAbs := by
      rcases hlcm_nat with ⟨q, hq⟩
      rw [hM0_abs, hlcm_eq, Nat.mul_assoc colFac extraRowFac q] at hq
      exact ⟨q, Nat.eq_of_mul_eq_mul_left hcol_pos hq⟩
    have hdiv_exact : ((intDet (U * T) M0).natAbs / jointLcm) * jointLcm = (intDet (U * T) M0).natAbs :=
      Nat.div_mul_cancel hlcm_nat
    -- Majorant bound on `A_newton` from Wave 15 `.2.2.1`? Wait: Wave 15 `.2.1` gives
    -- `(intDet (U * T) M0).natAbs ≤ natFact (U * T) * (colFac * newtonProd)`!
    have hmaj_M0 := (hw15_col.2.2.1 U W K T u X_max (laurentRectRows U T) hU2 hT hu hX_ge hX_rows).1
    change (intDet (U * T) M0).natAbs ≤ natFact (U * T) * (colFac * newtonProd) at hmaj_M0
    have hlcm_pos : jointLcm ≥ 1 := by rw [hlcm_eq]; exact Nat.mul_le_mul hcol_pos hextra_pos
    have hquot_le : (intDet (U * T) M0).natAbs / jointLcm ≤ (natFact (U * T) * newtonProd) / extraRowFac := by
      rcases hlcm_nat with ⟨q, hq⟩
      have hq_div : (intDet (U * T) M0).natAbs / jointLcm = q := by
        rw [hq, Nat.mul_comm jointLcm q, Nat.mul_div_cancel q hlcm_pos]
      rw [hq_div]
      have hcol_q : colFac * (q * extraRowFac) ≤ colFac * (natFact (U * T) * newtonProd) := by
        calc colFac * (q * extraRowFac)
            = (colFac * extraRowFac) * q := by ac_rfl
          _ = (intDet (U * T) M0).natAbs := by rw [← hlcm_eq, ← hq]
          _ ≤ natFact (U * T) * (colFac * newtonProd) := hmaj_M0
          _ = colFac * (natFact (U * T) * newtonProd) := by ac_rfl
      have hqe_le : q * extraRowFac ≤ natFact (U * T) * newtonProd :=
        nat_mul_le_cancel_left_w5 colFac _ _ hcol_pos hcol_q
      exact (Nat.le_div_iff_mul_le hextra_pos).mpr hqe_le
    exact ⟨hlcm_eq, hextra_dvd_A, hdiv_exact, hquot_le⟩
  · -- Part 3: `8 × 8` `(T = 2, U = 4)` `(2, 5, 1)` overlap certificate:
    dsimp only
    rcases rect_8x8_251_overlap_certs with
      ⟨hcf8, hrf8, hgcd8, hlcm8, hv_up, hm_low, hmul_eq, hdiag_rel, hv_pos⟩
    have hdet_fac := (hw15_col.1 4 2 5 2 1 (laurentRectRows 4 2) (by decide) (by decide) (by decide)).1
    have hdetA : intDet 8 a8Newton251W16 = -2220582109184 := by
      have hu_eq := intDet_mul_upper_tri_w16 8 a8Newton251W16 v8OverlapMatW16 hv_up
      have hfn : (fun i j : Fin 8 => intSumPrefix 8 (fun r => a8Newton251W16 i r * v8OverlapMatW16 r j) 8) =
          m8OverlapMatW16 := by funext i j; exact hmul_eq i j
      rw [hfn, intDet_lower_tri_w16 8 m8OverlapMatW16 hm_low, hdiag_rel] at hu_eq
      exact Int.eq_of_mul_eq_mul_left (by omega : intDiagProdPrefixW16 8 v8OverlapMatW16 8 ≠ 0) hu_eq.symm
    change confluentFactorAllU 4 2 1 = 66072707334144 ∧ _
    have hA_same : (fun i j : Fin (4 * 2) =>
        Int.ofNat (mixedNewtonCoeffAllU 2 (2 ^ 1)
          ((laurentRectRows 4 2 i).1 * 2 + (laurentRectRows 4 2 i).2 * 5) j.val)) =
        a8Newton251W16 := rfl
    rw [hA_same, hdetA, hcf8] at hdet_fac
    simp only [Int.ofNat_eq_natCast] at hdet_fac
    refine ⟨hcf8, by rw [hcf8, hrf8]; exact hgcd8, by rw [hcf8, hrf8]; exact hlcm8, hdet_fac, ?_⟩
    rw [hdet_fac]
    rintro ⟨q, hq⟩
    have hmod : (((66072707334144 : Nat) : Int) * (-2220582109184)) % ((66072707334144 * 81 : Nat) : Int) = 0 := by
      rw [hq, Int.mul_emod_right]
    exact absurd hmod (by decide)

-- ----------------------------------------------------------------------------
-- Section 2B: Rank-3 `9 × 9` `(T = 3, U = 3)` Global `u ∈ {1..17}` Projective
--             Non-Vanishing, Cone-Free `(81 * w', 32 * k')` & Higher Resonant
--             Rays, & Uniform Logarithmic Multi-`u` Zero-Horizon (`W16_H2`)
-- ----------------------------------------------------------------------------

private def intPowModW16 (x m : Int) : Nat -> Int
  | 0 => 1 % m
  | d + 1 => (x * intPowModW16 x m d) % m

private theorem intPowNat_emod_w16 (x m : Int) :
    ∀ d : Nat, intPowNat x d % m = intPowModW16 (x % m) m d
  | 0 => by simp [intPowNat, intPowModW16]
  | d + 1 => by
    simp only [intPowNat, intPowModW16]
    rw [Int.mul_emod, intPowNat_emod_w16 x m d]

private def addCoeffAtAW16 (a : Nat) (v m : Int) : List (Nat × Int) -> List (Nat × Int)
  | [] => [(a, v % m)]
  | (a0, c0) :: tl =>
    if a == a0 then (a0, (c0 + v) % m) :: tl
    else (a0, c0) :: addCoeffAtAW16 a v m tl

private def evalDeg9PolyModW16 (x y m : Int) : List (Nat × Int) -> Int
  | [] => 0
  | (a, cf) :: tl =>
    ((cf * ((intPowModW16 x m a * intPowModW16 y m (9 - a)) % m)) % m +
      evalDeg9PolyModW16 x y m tl) % m

private theorem evalDeg9PolyModW16_addCoeff (x y m : Int) (a : Nat) (v : Int) :
    ∀ tbl : List (Nat × Int),
      evalDeg9PolyModW16 x y m (addCoeffAtAW16 a v m tbl) =
        (((v % m) * ((intPowModW16 x m a * intPowModW16 y m (9 - a)) % m)) % m +
          evalDeg9PolyModW16 x y m tbl) % m
  | [] => by
    simp only [addCoeffAtAW16, evalDeg9PolyModW16, Int.add_zero, Int.emod_emod]
  | (a0, c0) :: tl => by
    simp only [addCoeffAtAW16]
    by_cases ha : a == a0
    · simp only [ha, ite_true, evalDeg9PolyModW16]
      have ha_eq : a = a0 := Nat.eq_of_beq_eq_true ha
      subst ha_eq
      generalize (intPowModW16 x m a * intPowModW16 y m (9 - a)) % m = P
      generalize evalDeg9PolyModW16 x y m tl = R
      have e1 : (((c0 + v) % m) * P) % m = ((c0 + v) * P) % m := by
        conv => rhs; rw [Int.mul_emod]
        conv => lhs; rw [Int.mul_emod, Int.emod_emod]
      have e2 : (((v % m) * P) % m + ((c0 * P) % m + R) % m) % m =
          ((c0 + v) * P + R) % m := by
        have ev : ((v % m) * P) % m = (v * P) % m := by
          conv => rhs; rw [Int.mul_emod]
          conv => lhs; rw [Int.mul_emod, Int.emod_emod]
        rw [ev]
        conv => lhs; rw [Int.add_emod, Int.emod_emod, Int.emod_emod, ← Int.add_emod]
        have es : v * P + ((c0 * P) % m + R) = (c0 * P) % m + (v * P + R) := by omega
        rw [es]
        conv => lhs; rw [Int.add_emod, Int.emod_emod, ← Int.add_emod]
        have es2 : c0 * P + (v * P + R) = (c0 + v) * P + R := by
          rw [Int.add_mul]; omega
        rw [es2]
      rw [e1, e2]
      conv => lhs; rw [Int.add_emod, Int.emod_emod, ← Int.add_emod]
    · simp only [ha, Bool.false_eq_true, ite_false, evalDeg9PolyModW16,
        evalDeg9PolyModW16_addCoeff x y m a v tl]
      generalize (c0 * ((intPowModW16 x m a0 * intPowModW16 y m (9 - a0)) % m)) % m = C0
      generalize ((v % m) * ((intPowModW16 x m a * intPowModW16 y m (9 - a)) % m)) % m = V0
      generalize evalDeg9PolyModW16 x y m tl = R
      conv => lhs; rw [Int.add_emod, Int.emod_emod, ← Int.add_emod]
      conv => rhs; rw [Int.add_emod, Int.emod_emod, ← Int.add_emod]
      have es : C0 + (V0 + R) = V0 + (C0 + R) := by omega
      rw [es]

private def compileDeg9ModW16 (z w m : Int) : List Mono4 -> List (Nat × Int)
  | [] => []
  | (a, _, c, d, cf) :: tl =>
    let v := ((cf % m) * ((intPowModW16 z m c * intPowModW16 w m d) % m)) % m
    addCoeffAtAW16 a v m (compileDeg9ModW16 z w m tl)

private theorem compileDeg9ModW16_spec (x y z w m : Int) :
    ∀ ms : List Mono4, ms.all (fun mn => mn.1 + mn.2.1 == 9) = true ->
      evalDeg9PolyModW16 (x % m) (y % m) m (compileDeg9ModW16 (z % m) (w % m) m ms) =
        evalPoly4 x y z w ms % m
  | [], _ => by simp [compileDeg9ModW16, evalDeg9PolyModW16, evalPoly4]
  | (a, b, c, d, cf) :: tl, hall => by
    simp only [List.all_cons] at hall
    rcases bool_and_split hall with ⟨hab_b, htl⟩
    have hb_eq : b = 9 - a := by have := Nat.eq_of_beq_eq_true hab_b; omega
    subst hb_eq
    simp only [compileDeg9ModW16, evalDeg9PolyModW16_addCoeff,
      compileDeg9ModW16_spec x y z w m tl htl, evalPoly4]
    conv => rhs; rw [Int.add_emod]
    congr 1
    congr 1
    rw [Int.emod_emod]
    unfold evalMono4
    have ez : intPowNat z c % m = intPowModW16 (z % m) m c := intPowNat_emod_w16 z m c
    have ew : intPowNat w d % m = intPowModW16 (w % m) m d := intPowNat_emod_w16 w m d
    have ex : intPowNat x a % m = intPowModW16 (x % m) m a := intPowNat_emod_w16 x m a
    have ey : intPowNat y (9 - a) % m = intPowModW16 (y % m) m (9 - a) := intPowNat_emod_w16 y m (9 - a)
    have ezw : (intPowNat z c * intPowNat w d) % m =
        (intPowModW16 (z % m) m c * intPowModW16 (w % m) m d) % m := by
      rw [Int.mul_emod, ez, ew]
    have exy : (intPowNat x a * intPowNat y (9 - a)) % m =
        (intPowModW16 (x % m) m a * intPowModW16 (y % m) m (9 - a)) % m := by
      rw [Int.mul_emod, ex, ey]
    change (((cf % m) * ((intPowModW16 (z % m) m c * intPowModW16 (w % m) m d) % m)) % m *
        ((intPowModW16 (x % m) m a * intPowModW16 (y % m) m (9 - a)) % m)) % m =
      (cf * (intPowNat x a * (intPowNat y (9 - a) * (intPowNat z c * intPowNat w d)))) % m
    have erhs : cf * (intPowNat x a * (intPowNat y (9 - a) * (intPowNat z c * intPowNat w d))) =
        (cf * (intPowNat z c * intPowNat w d)) * (intPowNat x a * intPowNat y (9 - a)) := by ac_rfl
    rw [erhs, Int.mul_emod (cf * _), Int.mul_emod cf, ezw, exy]

private def powModFuelW16 : Nat -> Nat -> Nat -> Nat -> Nat
  | 0, _, _, p => 1 % p
  | fuel + 1, a, e, p =>
    if e == 0 then 1 % p
    else
      let half := powModFuelW16 fuel a (e / 2) p
      let sq := (half * half) % p
      if e % 2 == 1 then (sq * a) % p else sq

private def allBelowBoolW16 : Nat -> (Nat -> Bool) -> Bool
  | 0, _ => true
  | n + 1, f => f n && allBelowBoolW16 n f

private theorem allBelowBoolW16_spec (n : Nat) (f : Nat -> Bool) :
    allBelowBoolW16 n f = true -> ∀ k : Nat, k < n -> f k = true := by
  induction n with
  | zero => intros _ _ hk; omega
  | succ n' ih =>
    intro hall k hk
    unfold allBelowBoolW16 at hall
    rcases bool_and_split hall with ⟨hfn, htl⟩
    by_cases hkeq : k = n'
    · subst hkeq; exact hfn
    · exact ih htl k (by omega)

private def allAffineNonzeroW16 : Nat -> Int -> List (Nat × Int) -> Bool
  | 0, _, _ => true
  | t + 1, pI, tbl =>
    (evalDeg9PolyModW16 (t : Int) 1 pI tbl != 0) && allAffineNonzeroW16 t pI tbl

private theorem allAffineNonzeroW16_spec (n : Nat) (pI : Int) (tbl : List (Nat × Int)) :
    allAffineNonzeroW16 n pI tbl = true ->
    ∀ t : Nat, t < n -> evalDeg9PolyModW16 (t : Int) 1 pI tbl ≠ 0 := by
  induction n with
  | zero => intros _ _ ht; omega
  | succ n' ih =>
    intro hall t ht
    unfold allAffineNonzeroW16 at hall
    rcases bool_and_split hall with ⟨hfn, htl⟩
    by_cases hteq : t = n'
    · subst hteq; exact bne_iff_ne.mp hfn
    · exact ih htl t (by omega)

private def checkProjRootFreeModPBool (u p : Nat) : Bool :=
  let pI : Int := (p : Int)
  let p2m : Int := (((2 ^ u) % p : Nat) : Int)
  let p3m : Int := (((3 ^ u) % p : Nat) : Int)
  let tbl := compileDeg9ModW16 p2m p3m pI t3u3CorePoly
  allBelowBoolW16 p (fun a =>
    (a == 0) || ((a * powModFuelW16 8 a (p - 2) p) % p == 1)) &&
  (evalDeg9PolyModW16 1 0 pI tbl != 0) &&
  allAffineNonzeroW16 p pI tbl

set_option maxRecDepth 65536 in
private theorem t3u3_deg9_cert : t3u3CorePoly.all (fun m => m.1 + m.2.1 == 9) = true := by decide
set_option maxRecDepth 65536 in
private theorem t3u3_proj_u10_cert : checkProjRootFreeModPBool 10 43 = true := by decide
set_option maxRecDepth 65536 in
private theorem t3u3_proj_u11_cert : checkProjRootFreeModPBool 11 29 = true := by decide
set_option maxRecDepth 65536 in
private theorem t3u3_proj_u12_cert : checkProjRootFreeModPBool 12 59 = true := by decide
set_option maxRecDepth 65536 in
private theorem t3u3_proj_u13_cert : checkProjRootFreeModPBool 13 37 = true := by decide
set_option maxRecDepth 65536 in
private theorem t3u3_proj_u14_cert : checkProjRootFreeModPBool 14 83 = true := by decide
set_option maxRecDepth 65536 in
private theorem t3u3_proj_u15_cert : checkProjRootFreeModPBool 15 109 = true := by decide
set_option maxRecDepth 65536 in
private theorem t3u3_proj_u16_cert : checkProjRootFreeModPBool 16 47 = true := by decide
set_option maxRecDepth 65536 in
private theorem t3u3_proj_u17_cert : checkProjRootFreeModPBool 17 13 = true := by decide

private theorem evalPoly4_homog_deg9_w16 (w0 k0 c u : Nat) :
    t3u3CorePoly.all (fun m => m.1 + m.2.1 == 9) = true ->
    evalPoly4 ((w0 * c : Nat) : Int) ((k0 * c : Nat) : Int)
      ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int) t3u3CorePoly =
    ((c ^ 9 : Nat) : Int) *
      evalPoly4 (w0 : Int) (k0 : Int) ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int) t3u3CorePoly := by
  have hintPow_ev : ∀ (x d : Nat), intPowNat (x : Int) d = ((x ^ d : Nat) : Int) := by
    intro x d; induction d with
    | zero => rfl
    | succ d' ih => simp [intPowNat, ih, Nat.pow_succ, Int.natCast_mul, Int.mul_comm]
  have hwalk : ∀ ms : List Mono4, ms.all (fun m => m.1 + m.2.1 == 9) = true ->
      evalPoly4 ((w0 * c : Nat) : Int) ((k0 * c : Nat) : Int)
        ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int) ms =
      ((c ^ 9 : Nat) : Int) *
        evalPoly4 (w0 : Int) (k0 : Int) ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int) ms := by
    intro ms; induction ms with
    | nil => intros; simp [evalPoly4]
    | cons m0 tl ih =>
      rcases m0 with ⟨a, b, p2, p3, cf⟩
      intro hall
      simp only [List.all_cons] at hall
      rcases bool_and_split hall with ⟨hab_b, htl⟩
      have hab9 : a + b = 9 := Nat.eq_of_beq_eq_true hab_b
      simp only [evalPoly4, evalMono4, ih htl, Int.mul_add]
      congr 1
      rw [hintPow_ev (w0 * c) a, hintPow_ev (k0 * c) b, hintPow_ev w0 a, hintPow_ev k0 b]
      have hnat : (w0 * c) ^ a * (k0 * c) ^ b = c ^ 9 * (w0 ^ a * k0 ^ b) := by
        rw [mul_pow_w16c w0 c a, mul_pow_w16c k0 c b]
        calc (w0 ^ a * c ^ a) * (k0 ^ b * c ^ b)
            = (c ^ a * c ^ b) * (w0 ^ a * k0 ^ b) := by ac_rfl
          _ = c ^ 9 * (w0 ^ a * k0 ^ b) := by rw [← Nat.pow_add, hab9]
      generalize intPowNat ((2 ^ u : Nat) : Int) p2 * intPowNat ((3 ^ u : Nat) : Int) p3 = pq
      have hlhs : cf * ((((w0 * c) ^ a : Nat) : Int) * ((((k0 * c) ^ b : Nat) : Int) * pq)) =
          cf * ((((w0 * c) ^ a * (k0 * c) ^ b : Nat) : Int) * pq) := by
        rw [Int.natCast_mul, Int.mul_assoc]
      have hrhs : ((c ^ 9 : Nat) : Int) * (cf * (((w0 ^ a : Nat) : Int) * (((k0 ^ b : Nat) : Int) * pq))) =
          cf * (((c ^ 9 * (w0 ^ a * k0 ^ b) : Nat) : Int) * pq) := by
        rw [Int.natCast_mul, Int.natCast_mul]; ac_rfl
      rw [hlhs, hrhs, hnat]
  exact hwalk t3u3CorePoly

private theorem mod_mul_inv_cancel_w16 (a b inv p : Nat)
    (ha : a < p) (hinv : (b * inv) % p = 1) :
    (((a * inv) % p) * b) % p = a := by
  calc (((a * inv) % p) * b) % p
      = (((a * inv) % p) * (b % p)) % p := by
          conv => lhs; rw [Nat.mul_mod ((a * inv) % p) b p, Nat.mod_mod]
    _ = ((a * inv) * b) % p := (Nat.mul_mod (a * inv) b p).symm
    _ = (a * (b * inv)) % p := by
          have e : (a * inv) * b = a * (b * inv) := by ac_rfl
          rw [e]
    _ = ((a % p) * ((b * inv) % p)) % p := Nat.mul_mod a (b * inv) p
    _ = ((a % p) * 1) % p := by rw [hinv]
    _ = a := by rw [Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt ha]

private theorem projRootFree_imp_nonzero_w16 (u p : Nat)
    (hu1 : u ≥ 1) (hp2 : p ≥ 2)
    (hdeg9 : t3u3CorePoly.all (fun m => m.1 + m.2.1 == 9) = true)
    (hcert : checkProjRootFreeModPBool u p = true) :
    ∀ W K : Nat, W ≥ 1 -> K ≥ 1 -> intDet 9 (laurentTwoBaseT3U3Mat9 W K u) ≠ 0 := by
  have hclosed_u := laurent_9x9_t3u3_all_u_cone_positivity_and_multiu_nonvanishing.1
  unfold checkProjRootFreeModPBool at hcert
  rcases bool_and_split hcert with ⟨hb1, hall_aff⟩
  rcases bool_and_split hb1 with ⟨hall_inv, hinf_b⟩
  have hinf_nz := bne_iff_ne.mp hinf_b
  let pI : Int := (p : Int)
  let p2 : Int := ((2 ^ u : Nat) : Int)
  let p3 : Int := ((3 ^ u : Nat) : Int)
  have hp2m_eq : p2 % pI = (((2 ^ u) % p : Nat) : Int) := (Int.natCast_emod (2 ^ u) p).symm
  have hp3m_eq : p3 % pI = (((3 ^ u) % p : Nat) : Int) := (Int.natCast_emod (3 ^ u) p).symm
  have hcancel9 : ∀ (x inv : Nat) (V : Int),
      (x * inv) % p = 1 ->
      (((x ^ 9 : Nat) : Int) * V) % pI = 0 ->
      V % pI = 0 := by
    intro x inv V hxinv hxv0
    have hp_d : ∀ d : Nat, ((x * inv) ^ d) % p = 1 := by
      intro d; induction d with
      | zero => exact Nat.mod_eq_of_lt hp2
      | succ d' ih => rw [Nat.pow_succ, Nat.mul_mod, ih, Nat.one_mul, Nat.mod_mod, hxinv]
    have hp9_1 : (x ^ 9 * inv ^ 9) % p = 1 := by
      rw [← mul_pow_w16c x inv 9]; exact hp_d 9
    have hm1 : (((x ^ 9 * inv ^ 9 : Nat) : Int) % pI) = 1 := by
      have hc : (((x ^ 9 * inv ^ 9 : Nat) : Int) % pI) = (((x ^ 9 * inv ^ 9) % p : Nat) : Int) :=
        (Int.natCast_emod (x ^ 9 * inv ^ 9) p).symm
      rw [hc, hp9_1]; rfl
    have h1p : (1 : Int) % pI = 1 := Int.emod_eq_of_lt (by decide) (by dsimp [pI]; omega)
    calc V % pI
        = (1 * V) % pI := by rw [Int.one_mul]
      _ = ((1 % pI) * (V % pI)) % pI := Int.mul_emod 1 V pI
      _ = ((((x ^ 9 * inv ^ 9 : Nat) : Int) % pI) * (V % pI)) % pI := by rw [h1p, hm1]
      _ = (((x ^ 9 * inv ^ 9 : Nat) : Int) * V) % pI := (Int.mul_emod _ _ _).symm
      _ = (((inv ^ 9 : Nat) : Int) * (((x ^ 9 : Nat) : Int) * V)) % pI := by
            rw [Int.natCast_mul]; ac_rfl
      _ = ((((inv ^ 9 : Nat) : Int) % pI) * ((((x ^ 9 : Nat) : Int) * V) % pI)) % pI :=
            Int.mul_emod _ _ _
      _ = 0 := by rw [hxv0, Int.mul_zero, Int.zero_emod]
  intro W K hW hK hz
  let g := Nat.gcd W K
  have hg_pos : g ≥ 1 := Nat.gcd_pos_of_pos_left K hW
  let w' := W / g
  let k' := K / g
  have hW_eq : W = w' * g := (Nat.div_mul_cancel (Nat.gcd_dvd_left W K)).symm
  have hK_eq : K = k' * g := (Nat.div_mul_cancel (Nat.gcd_dvd_right W K)).symm
  have hdet := hclosed_u W K u hW hu1
  rw [hz, Int.mul_zero, hW_eq, hK_eq, evalPoly4_homog_deg9_w16 w' k' g u hdeg9] at hdet
  have h6_pos : ((2 ^ (3 * u) * 3 ^ (3 * u) : Nat) : Int) > 0 := by
    have := Nat.mul_le_mul (nat_pow_pos_of_pos 2 (by decide) (3 * u)) (pow3_pos_nat (3 * u)); omega
  have hg9_pos : ((g ^ 9 : Nat) : Int) > 0 := by
    have := nat_pow_pos_of_pos g hg_pos 9; omega
  have hcore0 : evalPoly4 (w' : Int) (k' : Int) p2 p3 t3u3CorePoly = 0 := by
    by_cases hc : evalPoly4 (w' : Int) (k' : Int) p2 p3 t3u3CorePoly = 0
    · exact hc
    · exfalso
      exact absurd hdet.symm (Int.mul_ne_zero (by omega) (Int.mul_ne_zero (by omega) hc))
  let wm := w' % p
  let km := k' % p
  have hwm_lt : wm < p := Nat.mod_lt w' (by omega)
  have hkm_lt : km < p := Nat.mod_lt k' (by omega)
  have hnot_both0 : ¬ (wm = 0 ∧ km = 0) := by
    rintro ⟨hw0, hk0⟩
    rcases Nat.dvd_of_mod_eq_zero hw0 with ⟨qw, hqw⟩
    rcases Nat.dvd_of_mod_eq_zero hk0 with ⟨qk, hqk⟩
    have hdW : p * g ∣ W := ⟨qw, by rw [hW_eq, hqw]; ac_rfl⟩
    have hdK : p * g ∣ K := ⟨qk, by rw [hK_eq, hqk]; ac_rfl⟩
    have hdg : p * g ∣ g := Nat.dvd_gcd hdW hdK
    have hle := Nat.le_of_dvd hg_pos hdg
    have hge := Nat.mul_le_mul_right g hp2
    omega
  have hcw : (w' : Int) % pI = (wm : Int) := (Int.natCast_emod w' p).symm
  have hck : (k' : Int) % pI = (km : Int) := (Int.natCast_emod k' p).symm
  have hwm_mod : (wm : Int) % pI = (wm : Int) :=
    Int.emod_eq_of_lt (Int.natCast_nonneg wm) (by dsimp [pI]; omega)
  have hkm_mod : (km : Int) % pI = (km : Int) :=
    Int.emod_eq_of_lt (Int.natCast_nonneg km) (by dsimp [pI]; omega)
  have hm_wk : evalPoly4 (wm : Int) (km : Int) p2 p3 t3u3CorePoly % pI = 0 := by
    rw [← compileDeg9ModW16_spec (wm : Int) (km : Int) p2 p3 pI t3u3CorePoly hdeg9,
        hwm_mod, hkm_mod, ← hcw, ← hck,
        compileDeg9ModW16_spec (w' : Int) (k' : Int) p2 p3 pI t3u3CorePoly hdeg9,
        hcore0, Int.zero_emod]
  by_cases hkm0 : km = 0
  · have hwm_ne : wm ≠ 0 := fun hw0 => hnot_both0 ⟨hw0, hkm0⟩
    have hinv_or := allBelowBoolW16_spec p _ hall_inv wm hwm_lt
    have hbeq_f : (wm == 0) = false := beq_false_of_ne hwm_ne
    rw [hbeq_f, Bool.false_or] at hinv_or
    let inv := powModFuelW16 8 wm (p - 2) p
    have hinv : (wm * inv) % p = 1 := beq_iff_eq.mp hinv_or
    rw [hkm0, show (wm : Int) = ((1 * wm : Nat) : Int) by simp,
        show ((0 : Nat) : Int) = ((0 * wm : Nat) : Int) by simp,
        evalPoly4_homog_deg9_w16 1 0 wm u hdeg9] at hm_wk
    have hv10_0 := hcancel9 wm inv (evalPoly4 1 0 p2 p3 t3u3CorePoly) hinv hm_wk
    rw [← compileDeg9ModW16_spec 1 0 p2 p3 pI t3u3CorePoly hdeg9,
        show (1 : Int) % pI = 1 from Int.emod_eq_of_lt (by decide) (by dsimp [pI]; omega),
        Int.zero_emod, hp2m_eq, hp3m_eq] at hv10_0
    exact hinf_nz hv10_0
  · have hinv_or := allBelowBoolW16_spec p _ hall_inv km hkm_lt
    have hbeq_f : (km == 0) = false := beq_false_of_ne hkm0
    rw [hbeq_f, Bool.false_or] at hinv_or
    let inv := powModFuelW16 8 km (p - 2) p
    have hinv : (km * inv) % p = 1 := beq_iff_eq.mp hinv_or
    let t := (wm * inv) % p
    have ht_lt : t < p := Nat.mod_lt _ (by omega)
    have htkm : (t * km) % p = wm := mod_mul_inv_cancel_w16 wm km inv p hwm_lt hinv
    have htk_eq : evalPoly4 ((t * km : Nat) : Int) ((1 * km : Nat) : Int) p2 p3 t3u3CorePoly % pI = 0 := by
      rw [← compileDeg9ModW16_spec ((t * km : Nat) : Int) ((1 * km : Nat) : Int) p2 p3 pI t3u3CorePoly hdeg9]
      have ec1 : ((t * km : Nat) : Int) % pI = (wm : Int) % pI := by
        have e : ((t * km : Nat) : Int) % pI = (((t * km) % p : Nat) : Int) :=
          (Int.natCast_emod (t * km) p).symm
        rw [e, htkm, hwm_mod]
      have ec2 : ((1 * km : Nat) : Int) % pI = (km : Int) % pI := by rw [Nat.one_mul]
      rw [ec1, ec2, compileDeg9ModW16_spec (wm : Int) (km : Int) p2 p3 pI t3u3CorePoly hdeg9, hm_wk]
    rw [evalPoly4_homog_deg9_w16 t 1 km u hdeg9] at htk_eq
    have hvt_0 := hcancel9 km inv (evalPoly4 (t : Int) 1 p2 p3 t3u3CorePoly) hinv htk_eq
    rw [← compileDeg9ModW16_spec (t : Int) 1 p2 p3 pI t3u3CorePoly hdeg9,
        show (t : Int) % pI = (t : Int) from Int.emod_eq_of_lt (Int.natCast_nonneg t) (by dsimp [pI]; omega),
        show (1 : Int) % pI = 1 from Int.emod_eq_of_lt (by decide) (by dsimp [pI]; omega),
        hp2m_eq, hp3m_eq] at hvt_0
    have htnz := allAffineNonzeroW16_spec p pI _ hall_aff t ht_lt
    exact htnz hvt_0

private theorem gcd_coprime_scale_w16 (a b c : Nat) (hcop : Nat.Coprime a b) :
    Nat.gcd (a * c) (b * c) = c := by
  have h1 : Nat.gcd (c * a) (c * b) = c * Nat.gcd a b := Nat.gcd_mul_left c a b
  rw [Nat.mul_comm a c, Nat.mul_comm b c, h1, hcop, Nat.mul_one]

private theorem lt_pow2_binBitLength_w16 (n : Nat) :
    n < 2 ^ binBitLength n := by
  have haux : ∀ (fuel x : Nat), x ≤ fuel -> x < 2 ^ binBitLengthAux fuel x := by
    intro fuel; induction fuel with
    | zero =>
      intro x hx
      have hx0 : x = 0 := by omega
      rw [hx0]; decide
    | succ f' ih =>
      intro x hx
      unfold binBitLengthAux
      by_cases hx0 : x = 0
      · rw [hx0]; simp
      · simp only [hx0, ite_false]
        have hx_div : x / 2 ≤ f' := by omega
        have ih_d := ih (x / 2) hx_div
        have hdm := (Nat.div_add_mod x 2).symm
        rw [Nat.add_comm 1, Nat.pow_succ]
        omega
  exact haux n n (Nat.le_refl n)

/--
  Theorem W16.2b (`laurent_9x9_t3u3_higher_resonant_rays_and_log_zero_horizon`,
  `zero custom axioms`):
  Rank-3 Two-Base `9 × 9` `(T = 3, U = 3)` Global `u ∈ {1..17}` Non-Vanishing via Projective
  `P^1(F_p)` Sieves (`p = 43, 29, 59, 37, 83, 109, 47, 13` for `u = 10..17`), Cone-Free `∀ u ≥ 1`
  Non-Vanishing Outside `(81 * w', 32 * k')` & Along Higher Resonant Rays `(81 * c, 16 * c)`,
  `(81 * c, 8 * c)`, & `(27 * c, 16 * c)`, Prime-Power Ray Cap `u ≤ 4 * s + 1`, & Uniform
  Logarithmic Multi-`u` Zero-Horizon `u + 2 < 4 * binBitLength (K / gcd(W, K))` Across ALL
  `W, K ≥ 1` (`Branch P3.3`, witness `LAURENT_RECT_8X8_T2U4_OVERLAP_AND_9X9_81_16_RESONANT`, `W16_H2`).
-/
theorem laurent_9x9_t3u3_higher_resonant_rays_and_log_zero_horizon :
    (∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 -> 1 ≤ u -> u ≤ 17 ->
      intDet 9 (laurentTwoBaseT3U3Mat9 W K u) ≠ 0) ∧
    (∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 -> u ≥ 1 ->
      ((W / Nat.gcd W K) % 81 ≠ 0 ∨ (K / Nat.gcd W K) % 32 ≠ 0) ->
      intDet 9 (laurentTwoBaseT3U3Mat9 W K u) ≠ 0) ∧
    (∀ (c u : Nat), c ≥ 1 -> u ≥ 1 ->
      intDet 9 (laurentTwoBaseT3U3Mat9 (81 * c) (16 * c) u) ≠ 0 ∧
      intDet 9 (laurentTwoBaseT3U3Mat9 (81 * c) (8 * c) u) ≠ 0 ∧
      intDet 9 (laurentTwoBaseT3U3Mat9 (27 * c) (16 * c) u) ≠ 0) ∧
    (∀ (r s c u : Nat), c ≥ 1 -> u ≥ 1 ->
      intDet 9 (laurentTwoBaseT3U3Mat9 (3 ^ r * c) (2 ^ s * c) u) = 0 ->
      u ≥ 18 ∧ (2 * u + 8) / 9 ≤ r ∧ (u + 2) / 4 ≤ s ∧ u ≤ 4 * s + 1) ∧
    (∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 -> u ≥ 1 ->
      intDet 9 (laurentTwoBaseT3U3Mat9 W K u) = 0 ->
      u ≥ 18 ∧
      3 ^ ((2 * u + 8) / 9) ≤ W / Nat.gcd W K ∧
      2 ^ ((u + 2) / 4) ≤ K / Nat.gcd W K ∧
      u + 2 < 4 * binBitLength (K / Nat.gcd W K)) := by
  have hw15 := laurent_9x9_t3u3_conefree_nonvanishing_and_multiu_ceiling
  have hdeg9 := t3u3_deg9_cert
  have hglob_1_17 : ∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 -> 1 ≤ u -> u ≤ 17 ->
      intDet 9 (laurentTwoBaseT3U3Mat9 W K u) ≠ 0 := by
    intro W K u hW hK hu1 hu17
    by_cases hu9 : u ≤ 9
    · exact hw15.1 W K u hW hK hu1 hu9
    · rcases (by omega : u = 10 ∨ u = 11 ∨ u = 12 ∨ u = 13 ∨ u = 14 ∨ u = 15 ∨ u = 16 ∨ u = 17) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact projRootFree_imp_nonzero_w16 10 43 (by decide) (by decide) hdeg9 t3u3_proj_u10_cert W K hW hK
      · exact projRootFree_imp_nonzero_w16 11 29 (by decide) (by decide) hdeg9 t3u3_proj_u11_cert W K hW hK
      · exact projRootFree_imp_nonzero_w16 12 59 (by decide) (by decide) hdeg9 t3u3_proj_u12_cert W K hW hK
      · exact projRootFree_imp_nonzero_w16 13 37 (by decide) (by decide) hdeg9 t3u3_proj_u13_cert W K hW hK
      · exact projRootFree_imp_nonzero_w16 14 83 (by decide) (by decide) hdeg9 t3u3_proj_u14_cert W K hW hK
      · exact projRootFree_imp_nonzero_w16 15 109 (by decide) (by decide) hdeg9 t3u3_proj_u15_cert W K hW hK
      · exact projRootFree_imp_nonzero_w16 16 47 (by decide) (by decide) hdeg9 t3u3_proj_u16_cert W K hW hK
      · exact projRootFree_imp_nonzero_w16 17 13 (by decide) (by decide) hdeg9 t3u3_proj_u17_cert W K hW hK
  have hcone_81_32 : ∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 -> u ≥ 1 ->
      ((W / Nat.gcd W K) % 81 ≠ 0 ∨ (K / Nat.gcd W K) % 32 ≠ 0) ->
      intDet 9 (laurentTwoBaseT3U3Mat9 W K u) ≠ 0 := by
    intro W K u hW hK hu1 hcond hz
    by_cases hu17 : u ≤ 17
    · exact hglob_1_17 W K u hW hK hu1 hu17 hz
    · rcases hw15.2.1 W K u hW hK (by omega) hz with ⟨hd3, hd2⟩
      have h81 : 81 ∣ 3 ^ ((2 * u + 8) / 9) := by
        have he : (2 * u + 8) / 9 = 4 + ((2 * u + 8) / 9 - 4) := by omega
        rw [he, Nat.pow_add]; exact ⟨3 ^ ((2 * u + 8) / 9 - 4), rfl⟩
      have h32 : 32 ∣ 2 ^ ((u + 2) / 4) := by
        have he : (u + 2) / 4 = 5 + ((u + 2) / 4 - 5) := by omega
        rw [he, Nat.pow_add]; exact ⟨2 ^ ((u + 2) / 4 - 5), rfl⟩
      have hw81 : (W / Nat.gcd W K) % 81 = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h81 hd3)
      have hk32 : (K / Nat.gcd W K) % 32 = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h32 hd2)
      rcases hcond with hw_ne | hk_ne
      · exact hw_ne hw81
      · exact hk_ne hk32
  have h3rays : ∀ (c u : Nat), c ≥ 1 -> u ≥ 1 ->
      intDet 9 (laurentTwoBaseT3U3Mat9 (81 * c) (16 * c) u) ≠ 0 ∧
      intDet 9 (laurentTwoBaseT3U3Mat9 (81 * c) (8 * c) u) ≠ 0 ∧
      intDet 9 (laurentTwoBaseT3U3Mat9 (27 * c) (16 * c) u) ≠ 0 := by
    intro c u hc1 hu1
    refine ⟨?_, ?_, ?_⟩
    · apply hcone_81_32 (81 * c) (16 * c) u (by omega) (by omega) hu1
      right; rw [gcd_coprime_scale_w16 81 16 c (by decide), Nat.mul_div_cancel 16 hc1]; decide
    · apply hcone_81_32 (81 * c) (8 * c) u (by omega) (by omega) hu1
      right; rw [gcd_coprime_scale_w16 81 8 c (by decide), Nat.mul_div_cancel 8 hc1]; decide
    · apply hcone_81_32 (27 * c) (16 * c) u (by omega) (by omega) hu1
      left; rw [gcd_coprime_scale_w16 27 16 c (by decide), Nat.mul_div_cancel 27 hc1]; decide
  have hray_hor : ∀ (r s c u : Nat), c ≥ 1 -> u ≥ 1 ->
      intDet 9 (laurentTwoBaseT3U3Mat9 (3 ^ r * c) (2 ^ s * c) u) = 0 ->
      u ≥ 18 ∧ (2 * u + 8) / 9 ≤ r ∧ (u + 2) / 4 ≤ s ∧ u ≤ 4 * s + 1 := by
    intro r s c u hc1 hu1 hz
    have hW_pos : 3 ^ r * c ≥ 1 := Nat.mul_le_mul (pow3_pos_nat r) hc1
    have hK_pos : 2 ^ s * c ≥ 1 := Nat.mul_le_mul (nat_pow_pos_of_pos 2 (by decide) s) hc1
    have hu18 : u ≥ 18 := by
      by_cases hle17 : u ≤ 17
      · exact False.elim (hglob_1_17 (3 ^ r * c) (2 ^ s * c) u hW_pos hK_pos hu1 hle17 hz)
      · omega
    rcases hw15.2.1 (3 ^ r * c) (2 ^ s * c) u hW_pos hK_pos (by omega) hz with ⟨hd3, hd2⟩
    have hcop32 : Nat.Coprime (3 ^ r) (2 ^ s) :=
      ((by decide : Nat.Coprime 3 2).pow_left r).pow_right s
    rw [gcd_coprime_scale_w16 (3 ^ r) (2 ^ s) c hcop32,
        Nat.mul_div_cancel (3 ^ r) hc1] at hd3
    rw [gcd_coprime_scale_w16 (3 ^ r) (2 ^ s) c hcop32,
        Nat.mul_div_cancel (2 ^ s) hc1] at hd2
    have hr_le : (2 * u + 8) / 9 ≤ r := by
      by_cases hle : (2 * u + 8) / 9 ≤ r
      · exact hle
      · exfalso
        have hlt_p : 3 ^ r < 3 ^ ((2 * u + 8) / 9) := by
          have hm := nat_pow_mono_exp_pos 3 (r + 1) ((2 * u + 8) / 9) (by decide) (by omega)
          rw [Nat.pow_succ] at hm
          have hp := pow3_pos_nat r; omega
        have hle_p := Nat.le_of_dvd (pow3_pos_nat r) hd3
        omega
    have hs_le : (u + 2) / 4 ≤ s := by
      by_cases hle : (u + 2) / 4 ≤ s
      · exact hle
      · exfalso
        have hlt_p : 2 ^ s < 2 ^ ((u + 2) / 4) := by
          have hm := nat_pow_mono_exp_pos 2 (s + 1) ((u + 2) / 4) (by decide) (by omega)
          rw [Nat.pow_succ] at hm
          have hp := nat_pow_pos_of_pos 2 (by decide) s; omega
        have hle_p := Nat.le_of_dvd (nat_pow_pos_of_pos 2 (by decide) s) hd2
        omega
    exact ⟨hu18, hr_le, hs_le, by omega⟩
  refine ⟨hglob_1_17, hcone_81_32, h3rays, hray_hor, ?_⟩
  intro W K u hW hK hu1 hz
  have hu18 : u ≥ 18 := by
    by_cases hle17 : u ≤ 17
    · exact False.elim (hglob_1_17 W K u hW hK hu1 hle17 hz)
    · omega
  rcases hw15.2.1 W K u hW hK (by omega) hz with ⟨hd3, hd2⟩
  have hg_pos : 0 < Nat.gcd W K := Nat.gcd_pos_of_pos_left K hW
  have hwn_pos : W / Nat.gcd W K ≥ 1 := Nat.div_pos (Nat.le_of_dvd hW (Nat.gcd_dvd_left W K)) hg_pos
  have hkn_pos : K / Nat.gcd W K ≥ 1 := Nat.div_pos (Nat.le_of_dvd hK (Nat.gcd_dvd_right W K)) hg_pos
  have hle_3 : 3 ^ ((2 * u + 8) / 9) ≤ W / Nat.gcd W K := Nat.le_of_dvd hwn_pos hd3
  have hle_2 : 2 ^ ((u + 2) / 4) ≤ K / Nat.gcd W K := Nat.le_of_dvd hkn_pos hd2
  have hlt_bit : 2 ^ ((u + 2) / 4) < 2 ^ binBitLength (K / Nat.gcd W K) :=
    Nat.lt_of_le_of_lt hle_2 (lt_pow2_binBitLength_w16 (K / Nat.gcd W K))
  have hexp_lt : (u + 2) / 4 < binBitLength (K / Nat.gcd W K) := by
    by_cases hlt_e : (u + 2) / 4 < binBitLength (K / Nat.gcd W K)
    · exact hlt_e
    · exfalso
      have hm := nat_pow_mono_exp_pos 2 (binBitLength (K / Nat.gcd W K)) ((u + 2) / 4) (by decide) (by omega)
      omega
  exact ⟨hu18, hle_3, hle_2, by omega⟩

-- ----------------------------------------------------------------------------
-- Section 2C: Universal Recursive Arbitrary-`p` Cross-Block Brox Carry Squeeze,
--             Coupled `henselOddInvModPow2` Boost, & Balanced `m = 5` Eliminations
--             (`W16_H2`, Branch P3.4, `choice-free`)
-- ----------------------------------------------------------------------------

/-- Universal recursive `p`-pivot upper bound on `broxSpiralCarry (pivots ++ (b_last :: tail))`:
    - `pivots = []`: `3 ^ blockWeightSum tail * (2 ^ (blockStepSum (b_last :: tail) - blockWeightSum (b_last :: tail)) - 1)`
    - `pivots = b0 :: ps`: exact 1-step Brox carry unfolding applied to `multiPivotCarryUB ps b_last tail`. -/
def multiPivotCarryUB : List (Nat × Nat) -> (Nat × Nat) -> List (Nat × Nat) -> Nat
  | [], b_last, tail =>
    let rem := b_last :: tail
    3 ^ blockWeightSum tail * (2 ^ (blockStepSum rem - blockWeightSum rem) - 1)
  | b0 :: ps, b_last, tail =>
    let sub := ps ++ (b_last :: tail)
    let b_next := match ps with | [] => b_last | b1 :: _ => b1
    3 ^ blockWeightSum sub * (2 ^ b0.2 - 1) +
      2 ^ (b0.2 + b_next.1) * multiPivotCarryUB ps b_last tail

private theorem henselOddInvModPow2_spec_cf_w16 :
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
      cases hc : ((d * henselOddInvModPow2 (k + 1) d) % 2 ^ (k + 2) == 1)
      · simp only [Bool.false_eq_true, ite_false]
        have hne1 : (d * henselOddInvModPow2 (k + 1) d) % 2 ^ (k + 2) ≠ 1 :=
          beq_eq_false_iff_ne.mp hc
        let x := henselOddInvModPow2 (k + 1) d
        change 1 ≤ x + 2 ^ (k + 1) ∧ x + 2 ^ (k + 1) < 2 ^ (k + 2) ∧
          (x + 2 ^ (k + 1)) % 2 = 1 ∧ (d * (x + 2 ^ (k + 1))) % 2 ^ (k + 2) = 1
        have hp_ev : 2 ^ (k + 1) % 2 = 0 := by rw [Nat.pow_succ]; omega
        let q := (d * x) / 2 ^ (k + 1)
        have hdx : d * x = 2 ^ (k + 1) * q + 1 := by
          have := Nat.div_add_mod (d * x) (2 ^ (k + 1))
          dsimp [x] at *; rw [hx_mod] at this; exact this.symm
        have hq_odd : q % 2 = 1 := by
          rcases (by omega : q % 2 = 0 ∨ q % 2 = 1) with hqe | hqo
          · exfalso
            let q_half := q / 2
            have hq2 : q = 2 * q_half := by omega
            have hm_eq : d * x = 2 ^ (k + 2) * q_half + 1 := by
              rw [hdx, hq2, hp2_eq]; ac_rfl
            have hmod1 : (d * x) % 2 ^ (k + 2) = 1 := by
              rw [hm_eq, Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_right]
              exact Nat.mod_eq_of_lt (by omega)
            exact hne1 hmod1
          · exact hqo
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
      · simp only [ite_true]
        exact ⟨hx1, by omega, hx_odd, beq_iff_eq.mp hc⟩

private theorem hensel_quotient_boost_cf_w16
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
  have hmod1 : (3 ^ w0 * q0) % 2 ^ s = 1 := by
    have hqa : 2 ^ a0 = 2 ^ s * 2 ^ (a0 - s) := by
      conv => lhs; rw [show a0 = s + (a0 - s) by omega, Nat.pow_add]
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
  rcases henselOddInvModPow2_spec_cf_w16 s (3 ^ w0 * d_mult) (by omega) h3w_odd with
    ⟨_, hinv_lt, _, hinv_mod⟩
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

/--
  Theorem W16.2c (`m_block_recursive_p_pivot_brox_squeeze`,
  choice-free `zero custom axioms`):
  Universal Recursive Arbitrary-`p` (`∀ pivots : List (Nat × Nat)`) Cross-Block Brox Carry Upper
  Bound, Monotone Refinement (`(p + 1)`-Pivot Bound ≤ `p`-Pivot Bound), Companion-Prime `d_mult * D`
  & Coupled `henselOddInvModPow2 s (3 ^ b0.1 * d_mult) * d_mult * D` Archimedean Squeezes Across ALL
  `m`-Block Tuples, `69×` Elimination of Balanced `m = 5` `[(17, 2), (17, 2), (17, 2), (17, 2), (17, 42)]`
  (Escaping All 5 Three-Pivot Rotations), & `7,859×` Mod-`2^16` Hensel + 4-Pivot Elimination of
  Balanced `m = 5` `[(10, 16), (10, 8), (10, 2), (10, 2), (10, 2)]` (`Branch P3.4`, witness
  `M1_BALANCED_5BLOCK_THREE_PIVOT_ESCAPE`, `W16_H2`).
-/
theorem m_block_recursive_p_pivot_brox_squeeze :
    (∀ (pivots : List (Nat × Nat)) (b_last : Nat × Nat) (tail : List (Nat × Nat)),
      let blocks := pivots ++ (b_last :: tail)
      (∀ b ∈ blocks, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      broxSpiralCarry blocks ≤ multiPivotCarryUB pivots b_last tail) ∧
    (∀ (pivots : List (Nat × Nat)) (b_pen b_last : Nat × Nat) (tail : List (Nat × Nat)),
      let blocks := pivots ++ (b_pen :: b_last :: tail)
      (∀ b ∈ blocks, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      multiPivotCarryUB (pivots ++ [b_pen]) b_last tail ≤
        multiPivotCarryUB pivots b_pen (b_last :: tail)) ∧
    (∀ (pivots : List (Nat × Nat)) (b_last : Nat × Nat) (tail : List (Nat × Nat))
       (qs : List Nat) (d_mult : Nat),
      let blocks := pivots ++ (b_last :: tail)
      let W := blockWeightSum blocks
      let K := blockStepSum blocks
      let D := 2 ^ K - 3 ^ W
      (∀ b ∈ blocks, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      3 ^ W < 2 ^ K ->
      qs.length = blocks.length ->
      (∀ j : Nat, j < blocks.length -> D * natAt qs j = broxSpiralCarry (rotBlocks j blocks)) ->
      d_mult ∣ natListGcd qs ->
      d_mult * D ≤ multiPivotCarryUB pivots b_last tail) ∧
    (∀ (b0 : Nat × Nat) (ps : List (Nat × Nat)) (b_last : Nat × Nat) (tail : List (Nat × Nat))
       (qs : List Nat) (s d_mult : Nat),
      let blocks := (b0 :: ps) ++ (b_last :: tail)
      let W := blockWeightSum blocks
      let K := blockStepSum blocks
      let D := 2 ^ K - 3 ^ W
      (∀ b ∈ blocks, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      3 ^ W < 2 ^ K ->
      qs.length = blocks.length ->
      (∀ j : Nat, j < blocks.length -> D * natAt qs j = broxSpiralCarry (rotBlocks j blocks)) ->
      s ≥ 4 ->
      b0.2 ≥ s ->
      d_mult % 2 = 1 ->
      d_mult ∣ natListGcd qs ->
      (henselOddInvModPow2 s (3 ^ b0.1 * d_mult) * d_mult) * D ≤
        multiPivotCarryUB (b0 :: ps) b_last tail) ∧
    (let blocks_bal5 : List (Nat × Nat) := [(17, 2), (17, 2), (17, 2), (17, 2), (17, 42)]
     let D_bal5 := 2 ^ blockStepSum blocks_bal5 - 3 ^ blockWeightSum blocks_bal5
     let blocks_h5 : List (Nat × Nat) := [(10, 16), (10, 8), (10, 2), (10, 2), (10, 2)]
     let D_h5 := 2 ^ blockStepSum blocks_h5 - 3 ^ blockWeightSum blocks_h5
     (∀ j : Nat, j < 5 ->
       match rotBlocks j blocks_bal5 with
       | b0 :: b1 :: b2 :: rest => multiPivotCarryUB [b0, b1] b2 rest > 3 * D_bal5
       | _ => False) ∧
     69 * multiPivotCarryUB [(17, 2), (17, 2), (17, 2)] (17, 2) [(17, 42)] < 3 * D_bal5 ∧
     ¬ (∃ qs : List Nat,
       qs.length = 5 ∧
       ∀ j : Nat, j < 5 -> D_bal5 * natAt qs j = broxSpiralCarry (rotBlocks j blocks_bal5)) ∧
     henselOddInvModPow2 16 (3 ^ 10 * 3) * 3 = 73113 ∧
     9 * D_h5 < broxSpiralCarry blocks_h5 ∧
     7859 * multiPivotCarryUB [(10, 16), (10, 8), (10, 2)] (10, 2) [(10, 2)] < 73113 * D_h5 ∧
     ¬ (∃ qs : List Nat,
       qs.length = 5 ∧
       ∀ j : Nat, j < 5 -> D_h5 * natAt qs j = broxSpiralCarry (rotBlocks j blocks_h5))) := by
  have hw13_brox := m_block_brox_carry_bound_and_cross_block_squeeze
  -- Part 1: Recursive `p`-pivot carry bound by structural induction on `pivots`:
  have hcarry_ub : ∀ (pivots : List (Nat × Nat)) (b_last : Nat × Nat) (tail : List (Nat × Nat)),
      (∀ b ∈ pivots ++ (b_last :: tail), b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      broxSpiralCarry (pivots ++ (b_last :: tail)) ≤ multiPivotCarryUB pivots b_last tail := by
    intro pivots; induction pivots with
    | nil =>
      intro b_last tail hpos
      simp only [List.nil_append, multiPivotCarryUB]
      have hb0 := (hw13_brox.1 b_last tail hpos).1 0 (by simp)
      have hw_sub : blockWeightSum (b_last :: tail) - (blockAt (b_last :: tail) 0).1 = blockWeightSum tail := by
        simp [blockWeightSum, blockAt]
      have hrot0 : rotBlocks 0 (b_last :: tail) = b_last :: tail := by simp [rotBlocks]
      rw [hrot0, hw_sub] at hb0
      have hmul_sub : 3 ^ blockWeightSum tail *
          (2 ^ (blockStepSum (b_last :: tail) - blockWeightSum (b_last :: tail)) - 1) =
          3 ^ blockWeightSum tail * 2 ^ (blockStepSum (b_last :: tail) - blockWeightSum (b_last :: tail)) -
            3 ^ blockWeightSum tail := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      rw [hmul_sub]
      have hle2 := hb0.2
      omega
    | cons b0 ps ih =>
      intro b_last tail hpos
      simp only [List.cons_append, multiPivotCarryUB]
      have ih_ps := ih b_last tail (fun b hb => hpos b (List.Mem.tail b0 hb))
      cases ps with
      | nil =>
        simp only [List.nil_append] at ih_ps ⊢
        unfold broxSpiralCarry
        exact Nat.add_le_add_left (Nat.mul_le_mul_left _ ih_ps) _
      | cons b1 ptl =>
        simp only [List.cons_append] at ih_ps ⊢
        unfold broxSpiralCarry
        exact Nat.add_le_add_left (Nat.mul_le_mul_left _ ih_ps) _
  -- Part 2: Monotone refinement (`(p + 1)`-pivot bound ≤ `p`-pivot bound):
  have hmono_piv : ∀ (pivots : List (Nat × Nat)) (b_pen b_last : Nat × Nat) (tail : List (Nat × Nat)),
      (∀ b ∈ pivots ++ (b_pen :: b_last :: tail), b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      multiPivotCarryUB (pivots ++ [b_pen]) b_last tail ≤
        multiPivotCarryUB pivots b_pen (b_last :: tail) := by
    intro pivots; induction pivots with
    | nil =>
      intro b_pen b_last tail hpos
      simp only [List.nil_append, multiPivotCarryUB]
      let rem := b_last :: tail
      have hb_pen := hpos b_pen (List.Mem.head _)
      have hrem_le : ∀ xs : List (Nat × Nat), (∀ b ∈ xs, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
          blockWeightSum xs ≤ blockStepSum xs := by
        intro xs; induction xs with
        | nil => intros; exact Nat.le_refl 0
        | cons x xtl ihx =>
          intro hp; have hx := hp x (List.Mem.head _)
          have iht := ihx (fun b hb => hp b (List.Mem.tail x hb))
          simp only [blockWeightSum, blockStepSum]; omega
      have hw_le_k : blockWeightSum rem ≤ blockStepSum rem :=
        hrem_le rem (fun b hb => hpos b (List.Mem.tail b_pen hb))
      let E_rem := blockStepSum rem - blockWeightSum rem
      have hE_tot : blockStepSum (b_pen :: rem) - blockWeightSum (b_pen :: rem) = b_pen.2 + E_rem := by
        dsimp [E_rem]; simp only [blockStepSum, blockWeightSum]; omega
      rw [hE_tot]
      have hw_rem : blockWeightSum rem = b_last.1 + blockWeightSum tail := rfl
      have h2_le_3 : 2 ^ b_last.1 ≤ 3 ^ b_last.1 := pow_mono_base_w16c 2 3 (by decide) b_last.1
      have hterm2_le : 2 ^ (b_pen.2 + b_last.1) * (3 ^ blockWeightSum tail * (2 ^ E_rem - 1)) ≤
          3 ^ blockWeightSum rem * (2 ^ b_pen.2 * (2 ^ E_rem - 1)) := by
        rw [Nat.pow_add 2 b_pen.2 b_last.1, hw_rem, Nat.pow_add 3 b_last.1 (blockWeightSum tail)]
        calc (2 ^ b_pen.2 * 2 ^ b_last.1) * (3 ^ blockWeightSum tail * (2 ^ E_rem - 1))
            = 2 ^ b_last.1 * (3 ^ blockWeightSum tail * (2 ^ b_pen.2 * (2 ^ E_rem - 1))) := by ac_rfl
          _ ≤ 3 ^ b_last.1 * (3 ^ blockWeightSum tail * (2 ^ b_pen.2 * (2 ^ E_rem - 1))) :=
                Nat.mul_le_mul_right _ h2_le_3
          _ = (3 ^ b_last.1 * 3 ^ blockWeightSum tail) * (2 ^ b_pen.2 * (2 ^ E_rem - 1)) := by ac_rfl
      have hexp_id : (2 ^ b_pen.2 - 1) + 2 ^ b_pen.2 * (2 ^ E_rem - 1) = 2 ^ (b_pen.2 + E_rem) - 1 := by
        have hp1 : 2 ^ b_pen.2 ≥ 1 := nat_pow_pos_of_pos 2 (by decide) b_pen.2
        have hp2 : 2 ^ E_rem ≥ 1 := nat_pow_pos_of_pos 2 (by decide) E_rem
        have hp_le : 2 ^ b_pen.2 ≤ 2 ^ (b_pen.2 + E_rem) :=
          nat_pow_mono_exp_pos 2 _ _ (by decide) (by omega)
        rw [Nat.mul_sub_left_distrib, Nat.mul_one, ← Nat.pow_add 2 b_pen.2 E_rem]
        omega
      calc 3 ^ blockWeightSum rem * (2 ^ b_pen.2 - 1) +
            2 ^ (b_pen.2 + b_last.1) * (3 ^ blockWeightSum tail * (2 ^ E_rem - 1))
          ≤ 3 ^ blockWeightSum rem * (2 ^ b_pen.2 - 1) +
            3 ^ blockWeightSum rem * (2 ^ b_pen.2 * (2 ^ E_rem - 1)) :=
              Nat.add_le_add_left hterm2_le _
        _ = 3 ^ blockWeightSum rem * ((2 ^ b_pen.2 - 1) + 2 ^ b_pen.2 * (2 ^ E_rem - 1)) :=
              (Nat.mul_add _ _ _).symm
        _ = 3 ^ blockWeightSum rem * (2 ^ (b_pen.2 + E_rem) - 1) := by rw [hexp_id]
    | cons b0 ps ih =>
      intro b_pen b_last tail hpos
      simp only [List.cons_append, multiPivotCarryUB]
      have ih_ps := ih b_pen b_last tail (fun b hb => hpos b (List.Mem.tail b0 hb))
      have hsub_eq : (ps ++ [b_pen]) ++ (b_last :: tail) = ps ++ (b_pen :: b_last :: tail) := by
        simp [List.append_assoc]
      cases ps with
      | nil =>
        simp only [List.nil_append] at hsub_eq ih_ps ⊢
        exact Nat.add_le_add_left (Nat.mul_le_mul_left _ ih_ps) _
      | cons b1 ptl =>
        simp only [List.cons_append] at hsub_eq ih_ps ⊢
        rw [hsub_eq]
        exact Nat.add_le_add_left (Nat.mul_le_mul_left _ ih_ps) _
  -- Part 3: Companion-prime `d_mult * D ≤ multiPivotCarryUB`:
  have hsqueeze : ∀ (pivots : List (Nat × Nat)) (b_last : Nat × Nat) (tail : List (Nat × Nat))
       (qs : List Nat) (d_mult : Nat),
      let blocks := pivots ++ (b_last :: tail)
      let W := blockWeightSum blocks
      let K := blockStepSum blocks
      let D := 2 ^ K - 3 ^ W
      (∀ b ∈ blocks, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      3 ^ W < 2 ^ K ->
      qs.length = blocks.length ->
      (∀ j : Nat, j < blocks.length -> D * natAt qs j = broxSpiralCarry (rotBlocks j blocks)) ->
      d_mult ∣ natListGcd qs ->
      d_mult * D ≤ multiPivotCarryUB pivots b_last tail := by
    intro pivots b_last tail qs d_mult; dsimp only
    intro hpos hlt hlen hspec hdvd_g
    let blocks := pivots ++ (b_last :: tail)
    have hne_blk : blocks.length ≥ 1 := by
      dsimp [blocks]; rw [List.length_append, List.length_cons]; omega
    cases hqs : qs with
    | nil => rw [hqs] at hlen; simp at hlen
    | cons q0 qtl =>
      have hq0_spec := hspec 0 hne_blk
      rw [hqs] at hq0_spec hdvd_g
      simp only [natAt, List.drop] at hq0_spec
      have hrot0 : rotBlocks 0 blocks = blocks := by
        dsimp [blocks]; cases pivots <;> simp [rotBlocks]
      change (2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks) * q0 =
        broxSpiralCarry (rotBlocks 0 blocks) at hq0_spec
      rw [hrot0] at hq0_spec
      have hdvd_q0 : d_mult ∣ q0 :=
        Nat.dvd_trans hdvd_g (Nat.gcd_dvd_left q0 (natListGcd qtl))
      have hcar_pos : broxSpiralCarry blocks ≥ 1 := by
        cases hbl : blocks with
        | nil => rw [hbl] at hne_blk; simp at hne_blk
        | cons bh btl =>
          have hp := (hw13_brox.1 bh btl (by rwa [← hbl])).1 0 (by simp)
          simpa [rotBlocks] using hp.1
      have hq0_pos : q0 ≥ 1 := by
        cases q0 with
        | zero => rw [Nat.mul_zero] at hq0_spec; omega
        | succ _ => omega
      have hdm_le : d_mult ≤ q0 := Nat.le_of_dvd hq0_pos hdvd_q0
      calc d_mult * (2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks)
          ≤ q0 * (2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks) := Nat.mul_le_mul_right _ hdm_le
        _ = (2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks) * q0 := Nat.mul_comm _ _
        _ = broxSpiralCarry blocks := hq0_spec
        _ ≤ multiPivotCarryUB pivots b_last tail := hcarry_ub pivots b_last tail hpos
  -- Part 4: Coupled `henselOddInvModPow2` + `p`-pivot Brox squeeze (`choice-free`):
  have hhensel_sq : ∀ (b0 : Nat × Nat) (ps : List (Nat × Nat)) (b_last : Nat × Nat)
       (tail : List (Nat × Nat)) (qs : List Nat) (s d_mult : Nat),
      let blocks := (b0 :: ps) ++ (b_last :: tail)
      let W := blockWeightSum blocks
      let K := blockStepSum blocks
      let D := 2 ^ K - 3 ^ W
      (∀ b ∈ blocks, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      3 ^ W < 2 ^ K ->
      qs.length = blocks.length ->
      (∀ j : Nat, j < blocks.length -> D * natAt qs j = broxSpiralCarry (rotBlocks j blocks)) ->
      s ≥ 4 ->
      b0.2 ≥ s ->
      d_mult % 2 = 1 ->
      d_mult ∣ natListGcd qs ->
      (henselOddInvModPow2 s (3 ^ b0.1 * d_mult) * d_mult) * D ≤
        multiPivotCarryUB (b0 :: ps) b_last tail := by
    intro b0 ps b_last tail qs s d_mult; dsimp only
    intro hpos hlt hlen hspec hs4 hb0_s hd_odd hdvd_g
    have hge2 : ((b0 :: ps) ++ (b_last :: tail)).length ≥ 2 := by simp; omega
    cases hqs0 : qs with
    | nil =>
      have h0 : qs.length = 0 := by simp [hqs0]
      omega
    | cons q0 qtl1 =>
      cases hqs1 : qtl1 with
      | nil =>
        have h1 : qs.length = 1 := by simp [hqs0, hqs1]
        omega
      | cons q1 qtl2 =>
        have hsp0 := hspec 0 (by omega)
        have hsp1 := hspec 1 (by omega)
        rw [hqs0, hqs1] at hsp0 hsp1 hdvd_g
        simp only [natAt, List.drop] at hsp0 hsp1
        have hdvd_q0 : d_mult ∣ q0 :=
          Nat.dvd_trans hdvd_g (Nat.gcd_dvd_left q0 _)
        have hrot0 : rotBlocks 0 ((b0 :: ps) ++ (b_last :: tail)) = (b0 :: ps) ++ (b_last :: tail) := by
          simp [rotBlocks]
        rw [hrot0] at hsp0
        have hq0_ge : q0 ≥ henselOddInvModPow2 s (3 ^ b0.1 * d_mult) * d_mult := by
          cases hps : ps with
          | nil =>
            simp only [hps, List.cons_append, List.nil_append] at hlt hsp0 hsp1
            have hrec := (m_block_two_pivot_telescoping_and_2adic_quotient_boost.1.2
              b0 b_last tail hlt).2 q0 q1 hsp0 hsp1
            exact (hensel_quotient_boost_cf_w16 s b0.1 b0.2 b_last.1 q0 q1 d_mult
              hs4 hb0_s hd_odd hdvd_q0 hrec).2
          | cons b1 ptl =>
            simp only [hps, List.cons_append] at hlt hsp0 hsp1
            have hrec := (m_block_two_pivot_telescoping_and_2adic_quotient_boost.1.2
              b0 b1 (ptl ++ (b_last :: tail)) hlt).2 q0 q1 hsp0 hsp1
            exact (hensel_quotient_boost_cf_w16 s b0.1 b0.2 b1.1 q0 q1 d_mult
              hs4 hb0_s hd_odd hdvd_q0 hrec).2
        calc (henselOddInvModPow2 s (3 ^ b0.1 * d_mult) * d_mult) *
              (2 ^ blockStepSum ((b0 :: ps) ++ (b_last :: tail)) -
                3 ^ blockWeightSum ((b0 :: ps) ++ (b_last :: tail)))
            ≤ q0 * (2 ^ blockStepSum ((b0 :: ps) ++ (b_last :: tail)) -
                3 ^ blockWeightSum ((b0 :: ps) ++ (b_last :: tail))) := Nat.mul_le_mul_right _ hq0_ge
          _ = (2 ^ blockStepSum ((b0 :: ps) ++ (b_last :: tail)) -
                3 ^ blockWeightSum ((b0 :: ps) ++ (b_last :: tail))) * q0 := Nat.mul_comm _ _
          _ = broxSpiralCarry ((b0 :: ps) ++ (b_last :: tail)) := hsp0
          _ ≤ multiPivotCarryUB (b0 :: ps) b_last tail := hcarry_ub (b0 :: ps) b_last tail hpos
  -- Part 5: Balanced `m = 5` `blocks_bal5` (`69×`) & `blocks_h5` (`7,859×`) certificates & refutations:
  refine ⟨hcarry_ub, hmono_piv, hsqueeze, hhensel_sq, ?_⟩
  dsimp only
  let blocks_bal5 : List (Nat × Nat) := [(17, 2), (17, 2), (17, 2), (17, 2), (17, 42)]
  let D_bal5 := 2 ^ blockStepSum blocks_bal5 - 3 ^ blockWeightSum blocks_bal5
  let blocks_h5 : List (Nat × Nat) := [(10, 16), (10, 8), (10, 2), (10, 2), (10, 2)]
  let D_h5 := 2 ^ blockStepSum blocks_h5 - 3 ^ blockWeightSum blocks_h5
  have hrot3_gt : ∀ j : Nat, j < 5 ->
      match rotBlocks j blocks_bal5 with
      | b0 :: b1 :: b2 :: rest => multiPivotCarryUB [b0, b1] b2 rest > 3 * D_bal5
      | _ => False := by
    intro j hj5
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [blocks_bal5, D_bal5, rotBlocks, List.drop, List.take, List.cons_append, List.nil_append]; decide)
  have h4piv_69 : 69 * multiPivotCarryUB [(17, 2), (17, 2), (17, 2)] (17, 2) [(17, 42)] < 3 * D_bal5 := by
    decide
  have hno_bal5 : ¬ (∃ qs : List Nat,
      qs.length = 5 ∧
      ∀ j : Nat, j < 5 -> D_bal5 * natAt qs j = broxSpiralCarry (rotBlocks j blocks_bal5)) := by
    rintro ⟨qs, hlen5, hqs_spec⟩
    have h3_dvd : 3 ∣ natListGcd qs :=
      (m_block_companion_prime_quotient_cascades.1
        (17, 2) [(17, 2), (17, 2), (17, 2), (17, 42)] qs (by decide) (by decide) hlen5 hqs_spec).2.1 (by decide)
    have h3D_le := hsqueeze [(17, 2), (17, 2), (17, 2)] (17, 2) [(17, 42)] qs 3
      (by decide) (by decide) hlen5 hqs_spec h3_dvd
    have hpos_ub : multiPivotCarryUB [(17, 2), (17, 2), (17, 2)] (17, 2) [(17, 42)] ≥ 1 := by decide
    change 3 * D_bal5 ≤ multiPivotCarryUB [(17, 2), (17, 2), (17, 2)] (17, 2) [(17, 42)] at h3D_le
    omega
  have hh5_inv : henselOddInvModPow2 16 (3 ^ 10 * 3) * 3 = 73113 := by decide
  have hh5_9D : 9 * D_h5 < broxSpiralCarry blocks_h5 := by decide
  have hh5_7859 : 7859 * multiPivotCarryUB [(10, 16), (10, 8), (10, 2)] (10, 2) [(10, 2)] < 73113 * D_h5 := by
    decide
  refine ⟨hrot3_gt, h4piv_69, hno_bal5, hh5_inv, hh5_9D, hh5_7859, ?_⟩
  rintro ⟨qs, hlen5, hqs_spec⟩
  have h3_dvd : 3 ∣ natListGcd qs :=
    (m_block_companion_prime_quotient_cascades.1
      (10, 16) [(10, 8), (10, 2), (10, 2), (10, 2)] qs (by decide) (by decide) hlen5 hqs_spec).2.1 (by decide)
  have h73113_le := hhensel_sq (10, 16) [(10, 8), (10, 2)] (10, 2) [(10, 2)] qs 16 3
    (by decide) (by decide) hlen5 hqs_spec (by decide) (by decide) (by decide) h3_dvd
  rw [hh5_inv] at h73113_le
  change 73113 * D_h5 ≤ multiPivotCarryUB [(10, 16), (10, 8), (10, 2)] (10, 2) [(10, 2)] at h73113_le
  have hpos_ub : multiPivotCarryUB [(10, 16), (10, 8), (10, 2)] (10, 2) [(10, 2)] ≥ 1 := by decide
  omega

end CollatzFormal
