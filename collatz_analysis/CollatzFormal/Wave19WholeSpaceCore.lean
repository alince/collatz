/-
  CollatzFormal/Wave19WholeSpaceCore.lean
  =======================================
  Wave 19 Whole-Space Mathematical & CS Proof Loop (Core — Fronts A & B):
  * Front A (`Branch P4.3`):
    - `twosided_c39_c78_expanding_b_and_t_toprow_impossibility`: all-dimension (`∀ d ≥ 2`)
      expanding-`.B` lower-right (`∑_{i ≥ 1} M_b[i,j] ≥ 2`) + `.T`-top-row + arbitrary `d × d` `.R`
      cascade & tail-row collapse across all `∀ k : Nat` towers on `c39` & `c78`.
    - `simultaneous_d3_invertible_and_d4_multichannel_farkas_locks`: infinite 6-parameter `d = 3`
      (`3 × 3`) invertible positive-trace lower-right (`39/39` & `78/78` = `100%` strict rules),
      7-parameter `d = 4` (`4 × 4`) 4-channel invertible (`100%` strict rules), & all-dimension
      (`∀ d ≥ 4`) multi-channel invertible Farkas locks on `c39` & `c78` (`W19_H1`).
    - `leftAnchoredDP2_no_1_to_30_cycles_and_heterogeneous_m_block_exclusions`: unconditional
      `1..30`-cycle freedom across ALL `DP2` words (`M1` `29`-cycle `68629840493971 /
      1738366812781` separation) and multi-spike / heterogeneous-weight symbolic all-`m` (`∀ m ≥ 3`)
      `.R`-carrying `DP2` cycle exclusions.
  * Front B (`Branches P3.2–P3.4`):
    - `laurent_12x12_t4u3_u6_to_9_nonvanishing_and_resonant_mod243_elimination`: global zero-free
      non-vanishing on `12 × 12` `(T = 4, U = 3)` for `u ∈ {6, 7, 8, 9}` (`p = 197, 13, 103, 67`),
      exact `laurentTrop3Mat12Explicit` factorization, `3^((u+2)/3 + 1) ∣ Q_u` (`243 ∣ Q_u` for
      `u ≥ 10`), `v_2(k') = 1 -> u ≤ 18`, & all-`u` resonant-ray `(5W, 2W)` / `(W, 14W)` / `(W, 22W)`
      elimination (`W19_H2`).
    - `laurent_16x16_t4u4_cone_flip_confluent_and_u1_to_5_nonvanishing`: symmetric rank-4 order-4
      `16 × 16` `(T = 4, U = 4)` interior Collatz-cone sign-flip (`det_16(3, 5, 1) < 0 < det_16(4, 7, 1)`),
      exact confluent divisibility, `(2^K - 3^W)` congruence, degree-24 homogeneity, `det_16(W, 4W, 1) < 0`,
      & global `u = 1..5` zero-free non-vanishing (`p = 31, 59, 41, 67, 37`).
    - `m_block_all_m_multispike_hensel_brox_and_8block_elimination`: symbolic all-`m` (`∀ m ≥ 3`)
      multi-spike & heterogeneous-weight + `henselOddInvModPow2` Brox squeeze, eliminating infinite
      all-`m` families escaping all non-Hensel rotations plus balanced & convergent `(41, 65)` `m = 8`
      benchmarks.

  Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

import CollatzFormal.Wave18WholeSpaceCore
import CollatzFormal.Wave18WholeSpace

namespace CollatzFormal

-- ============================================================================
-- Fast Rule Tables (`c39` & `c78`) and Tail-Row Sum Infrastructure (`∀ d ≥ 2`)
-- ============================================================================

private def toFinWordW19 (N : Nat) (hN : N ≥ 1) : List Nat -> List (Fin N)
  | [] => []
  | x :: xs => (if h : x < N then ⟨x, h⟩ else ⟨0, hN⟩) :: toFinWordW19 N hN xs

private def toFinRulesW19 (N : Nat) (hN : N ≥ 1) :
    List (List Nat × List Nat) -> List (List (Fin N) × List (Fin N))
  | [] => []
  | (l, r) :: rs => (toFinWordW19 N hN l, toFinWordW19 N hN r) :: toFinRulesW19 N hN rs

private def c39RawRulesW19 : List (List Nat × List Nat) :=
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

private def c78RawRulesW19 : List (List Nat × List Nat) :=
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
   ([79, 20], [44, 31, 14]), ([79, 19], [44, 31, 13]), ([79, 20 - 2], [44, 31, 12])]

private def c39FastRulesW19 : List (List (Fin 42) × List (Fin 42)) :=
  toFinRulesW19 42 (by decide) c39RawRulesW19

private def c78FastRulesW19 : List (List (Fin 84) × List (Fin 84)) :=
  toFinRulesW19 84 (by decide) c78RawRulesW19

set_option maxRecDepth 65536 in
private theorem c39_beq_fastRules_w19 :
    (filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List) == c39FastRulesW19) = true := by decide

private theorem c39_eq_fastRules_w19 :
    filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List) = c39FastRulesW19 :=
  beq_iff_eq.mp c39_beq_fastRules_w19

set_option maxRecDepth 65536 in
private theorem c78_beq_fastRules_w19 :
    (filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List) == c78FastRulesW19) = true := by decide

private theorem c78_eq_fastRules_w19 :
    filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List) = c78FastRulesW19 :=
  beq_iff_eq.mp c78_beq_fastRules_w19

private theorem bool_and_split_w19 {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true :=
  Bool.and_eq_true_iff.mp h

/-- Sum of tail coordinates `∑_{i ≥ 1} f(i)` over `Fin d`. -/
def natTailSum1 (d : Nat) (f : Fin d -> Nat) : Nat :=
  natSumFin d (fun i => if i.val = 0 then 0 else f i)

/-- Concrete `d = 2` expanding-`.B` lower-right + `.T`-top-row + `.R`-growth witness on `Fin 42`
    (`c39`, strictly orienting `27/39` matrix rules at `k = 2`):
    - `.L` (`s < 6`): `[[1, 0], [0, 0]]`,
    - `.R` (`6 ≤ s < 12`): `[[k, 0], [0, 0]]`,
    - `.B` (`12 ≤ s < 24`): `[[1, 2], [0, 5]]` (`M_b[1, 1] = 5 ≥ 2`!),
    - `.T` (`s ≥ 24`): `[[1, 1 on {36, 38} else 5], [0, 0]]`. -/
def expandingBWitnessMat2DC39 (k : Nat) (s : Fin 42) (i j : Fin 2) : Nat :=
  let sv := s.val
  if i.val == 0 && j.val == 0 then
    if sv < 6 then 1 else if sv < 12 then k else 1
  else if i.val == 0 && j.val == 1 then
    if sv < 12 then 0
    else if sv < 24 then 2
    else if sv == 36 || sv == 38 then 1 else 5
  else if i.val == 1 && j.val == 1 then
    if 12 ≤ sv && sv < 24 then 5 else 0
  else 0

/-- All-dimension (`d ≥ 2`) `k`-level `ω^k` Hofbauer–Waldmann natural matrix tower over
    `Fin (14 * M)` in the **expanding-`.B` lower-right + `.T`-top-row + arbitrary-`.R` stratum**:
    - Every symbol satisfies `(M_s)_{0,0} ≥ 1`,
    - `.L` (`s < 2 * M`) has `(M_s)_{0,0} = 1` and zero off-topleft entries,
    - `.B` (`4 * M ≤ s < 8 * M`) has `(M_b)_{0,0} = 1`, zero subdiagonal `(M_b)_{i,0} = 0` (`i ≥ 1`),
      and **column-expanding `(d - 1) × (d - 1)` lower-right block**
      `∀ j ≥ 1, ∑_{i ≥ 1} (M_b)_{i,j} ≥ 2` (covering invertible positive-trace blocks such as
      `[[2, 1], [1, 2]]` in `d = 3` and `[[2, 1, 0], [1, 2, 1], [0, 1, 2]]` in `d = 4`!),
    - `.T` (`s ≥ 8 * M`) has zero bottom rows `∀ i ≥ 1, ∀ j, (M_t)_{i,j} = 0` (with arbitrary top row!),
    - `.R` (`2 * M ≤ s < 4 * M`) has **100% arbitrary `d × d` entries** (`(M_r)_{0,0} ≥ 1`),
    - Rules may be eliminated at a level if **any** vector coordinate `∃ i : Fin d` drops strictly! -/
def GenOmegaExpandingBLowerRightAndTTopRowMatTower (M d : Nat) (hd : d ≥ 2) :
    Nat -> List (List (Fin (14 * M)) × List (Fin (14 * M))) -> Prop
  | 0, rules => rules = []
  | k + 1, rules =>
    rules = [] ∨
    ∃ (rem : List (List (Fin (14 * M)) × List (Fin (14 * M))))
      (mat : Fin (14 * M) -> Fin d -> Fin d -> Nat)
      (v : Fin (14 * M) -> Fin d -> Nat),
      (∀ s : Fin (14 * M), mat s ⟨0, by omega⟩ ⟨0, by omega⟩ ≥ 1) ∧
      (∀ s : Fin (14 * M), s.val < 2 * M ->
        mat s ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 ∧
        ∀ (i j : Fin d), (i.val ≥ 1 ∨ j.val ≥ 1) -> mat s i j = 0) ∧
      (∀ s : Fin (14 * M), 4 * M ≤ s.val ∧ s.val < 8 * M ->
        mat s ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 ∧
        (∀ i : Fin d, i.val ≥ 1 -> mat s i ⟨0, by omega⟩ = 0) ∧
        (∀ j : Fin d, j.val ≥ 1 -> natTailSum1 d (fun i => mat s i j) ≥ 2)) ∧
      (∀ s : Fin (14 * M), s.val ≥ 8 * M ->
        ∀ (i j : Fin d), i.val ≥ 1 -> mat s i j = 0) ∧
      (∀ r ∈ rules,
        (∀ i j : Fin d, evalFinWordMat (14 * M) d mat r.1 i j ≥ evalFinWordMat (14 * M) d mat r.2 i j) ∧
        (∀ i : Fin d, evalFinWordVec (14 * M) d mat v r.1 i ≥ evalFinWordVec (14 * M) d mat v r.2 i)) ∧
      (∀ r ∈ rules,
        ¬ (∃ i : Fin d, evalFinWordVec (14 * M) d mat v r.1 i > evalFinWordVec (14 * M) d mat v r.2 i) ->
        r ∈ rem) ∧
      GenOmegaExpandingBLowerRightAndTTopRowMatTower M d hd k rem

-- Basic algebra on `natSumPrefix`, `natSumFin`, and `natTailSum1`:

private theorem natSumPrefix_zero_w19 (d : Nat) (f : Fin d -> Nat) (hf : ∀ i : Fin d, f i = 0) :
    ∀ n : Nat, natSumPrefix d f n = 0
  | 0 => rfl
  | n + 1 => by
    simp only [natSumPrefix, natSumPrefix_zero_w19 d f hf n, Nat.zero_add]
    by_cases hn : n < d
    · simp only [hn, dite_true, hf ⟨n, hn⟩]
    · simp only [hn, dite_false]

private theorem natSumFin_zero_w19 (d : Nat) (f : Fin d -> Nat) (hf : ∀ i : Fin d, f i = 0) :
    natSumFin d f = 0 := natSumPrefix_zero_w19 d f hf d

private theorem natSumPrefix_add_w19 (d : Nat) (f g : Fin d -> Nat) :
    ∀ n : Nat, natSumPrefix d (fun i => f i + g i) n = natSumPrefix d f n + natSumPrefix d g n
  | 0 => rfl
  | n + 1 => by
    simp only [natSumPrefix, natSumPrefix_add_w19 d f g n]
    by_cases hn : n < d
    · simp only [hn, dite_true]; omega
    · simp only [hn, dite_false, Nat.add_zero]

private theorem natSumFin_add_w19 (d : Nat) (f g : Fin d -> Nat) :
    natSumFin d (fun i => f i + g i) = natSumFin d f + natSumFin d g :=
  natSumPrefix_add_w19 d f g d

private theorem natSumPrefix_mul_const_w19 (d c : Nat) (f : Fin d -> Nat) :
    ∀ n : Nat, natSumPrefix d (fun i => f i * c) n = natSumPrefix d f n * c
  | 0 => by simp [natSumPrefix]
  | n + 1 => by
    simp only [natSumPrefix, natSumPrefix_mul_const_w19 d c f n]
    by_cases hn : n < d
    · simp only [hn, dite_true, Nat.add_mul]
    · simp only [hn, dite_false, Nat.add_zero]

private theorem natSumFin_mul_const_w19 (d c : Nat) (f : Fin d -> Nat) :
    natSumFin d (fun i => f i * c) = natSumFin d f * c :=
  natSumPrefix_mul_const_w19 d c f d

private theorem natSumPrefix_le_w19 (d : Nat) (f g : Fin d -> Nat) (hle : ∀ i : Fin d, f i ≤ g i) :
    ∀ n : Nat, natSumPrefix d f n ≤ natSumPrefix d g n
  | 0 => Nat.le_refl 0
  | n + 1 => by
    simp only [natSumPrefix]
    have ih := natSumPrefix_le_w19 d f g hle n
    by_cases hn : n < d
    · simp only [hn, dite_true]; exact Nat.add_le_add ih (hle ⟨n, hn⟩)
    · simp only [hn, dite_false]; exact ih

private theorem natSumFin_le_w19 (d : Nat) (f g : Fin d -> Nat) (hle : ∀ i : Fin d, f i ≤ g i) :
    natSumFin d f ≤ natSumFin d g := natSumPrefix_le_w19 d f g hle d

private theorem natSumPrefix_swap_w19 (d : Nat) (G : Fin d -> Fin d -> Nat) :
    ∀ m n : Nat,
      natSumPrefix d (fun i => natSumPrefix d (fun j => G i j) n) m =
        natSumPrefix d (fun j => natSumPrefix d (fun i => G i j) m) n
  | 0, n => by
    rw [natSumPrefix]
    exact (natSumPrefix_zero_w19 d _ (fun _ => rfl) n).symm
  | m + 1, n => by
    simp only [natSumPrefix, natSumPrefix_swap_w19 d G m n]
    by_cases hm : m < d
    · simp only [hm, dite_true, ← natSumPrefix_add_w19]
    · simp only [hm, dite_false, Nat.add_zero]

private theorem natSumFin_swap_w19 (d : Nat) (G : Fin d -> Fin d -> Nat) :
    natSumFin d (fun i => natSumFin d (fun j => G i j)) =
      natSumFin d (fun j => natSumFin d (fun i => G i j)) :=
  natSumPrefix_swap_w19 d G d d

private theorem natSumPrefix_single_zero_w19 (d : Nat) (hd : d ≥ 1) (f : Fin d -> Nat)
    (hz : ∀ j : Fin d, j.val ≥ 1 -> f j = 0) :
    ∀ n : Nat, n ≥ 1 -> natSumPrefix d f n = f ⟨0, hd⟩
  | 0, h => by omega
  | 1, _ => by
    have h0d : 0 < d := by omega
    simp only [natSumPrefix, h0d, dite_true, Nat.zero_add]
  | n' + 2, _ => by
    rw [natSumPrefix, natSumPrefix_single_zero_w19 d hd f hz (n' + 1) (by omega)]
    by_cases hn : n' + 1 < d
    · simp only [hn, dite_true, hz ⟨n' + 1, hn⟩ (by dsimp; omega), Nat.add_zero]
    · simp only [hn, dite_false, Nat.add_zero]

private theorem natSumFin_single_zero_w19 (d : Nat) (hd : d ≥ 1) (f : Fin d -> Nat)
    (hz : ∀ j : Fin d, j.val ≥ 1 -> f j = 0) :
    natSumFin d f = f ⟨0, hd⟩ :=
  natSumPrefix_single_zero_w19 d hd f hz d hd

private theorem natTailSum1_eq_zero_iff_w19 (d : Nat) (f : Fin d -> Nat) :
    natTailSum1 d f = 0 ↔ ∀ i : Fin d, i.val ≥ 1 -> f i = 0 := by
  constructor
  · intro h0 i hi
    have hle : ∀ n : Nat, i.val < n -> f i ≤ natSumPrefix d (fun k => if k.val = 0 then 0 else f k) n := by
      intro n; induction n with
      | zero => intro hlt; omega
      | succ n' ih =>
        intro hlt
        unfold natSumPrefix
        by_cases heq : i.val = n'
        · have hn_d : n' < d := heq ▸ i.isLt
          have hn_nz : ¬ (n' = 0) := by omega
          have hfin : (⟨n', hn_d⟩ : Fin d) = i := Fin.ext heq.symm
          simp only [hn_d, dite_true, hn_nz, ite_false, hfin]
          omega
        · have hprev := ih (by omega)
          by_cases hn_d : n' < d
          · simp only [hn_d, dite_true]; omega
          · simp only [hn_d, dite_false]; exact hprev
    have hfi := hle d i.isLt
    unfold natTailSum1 natSumFin at h0
    omega
  · intro hz
    apply natSumFin_zero_w19
    intro i
    by_cases hi0 : i.val = 0
    · simp [hi0]
    · rw [ite_false_of_w10 hi0]; exact hz i (by omega)

private theorem natTailSum1_add_w19 (d : Nat) (f g : Fin d -> Nat) :
    natTailSum1 d (fun i => f i + g i) = natTailSum1 d f + natTailSum1 d g := by
  unfold natTailSum1
  rw [← natSumFin_add_w19]
  have hcongr : (fun i : Fin d => if i.val = 0 then 0 else f i + g i) =
      (fun i : Fin d => (if i.val = 0 then 0 else f i) + (if i.val = 0 then 0 else g i)) := by
    funext i; by_cases h : i.val = 0 <;> simp [h]
  rw [hcongr]

private theorem natTailSum1_le_w19 (d : Nat) (f g : Fin d -> Nat)
    (hle : ∀ i : Fin d, i.val ≥ 1 -> f i ≤ g i) :
    natTailSum1 d f ≤ natTailSum1 d g := by
  apply natSumFin_le_w19
  intro i
  by_cases h0 : i.val = 0
  · simp [h0]
  · simp only [h0, ite_false]; exact hle i (by omega)

-- Key inequality: on an expanding-`.B` matrix `B`, `natTailSum1 d (B * u) ≥ 2 * natTailSum1 d u`!
private theorem natTailSum1_expanding_matVec_ge_two_w19 (d : Nat) (hd : d ≥ 2)
    (B : Fin d -> Fin d -> Nat) (u : Fin d -> Nat)
    (_hb_col0 : ∀ i : Fin d, i.val ≥ 1 -> B i ⟨0, by omega⟩ = 0)
    (hb_exp : ∀ j : Fin d, j.val ≥ 1 -> natTailSum1 d (fun i => B i j) ≥ 2) :
    natTailSum1 d (natMatVec d B u) ≥ 2 * natTailSum1 d u := by
  let G (i j : Fin d) : Nat := if i.val = 0 then 0 else B i j * u j
  have hlhs : natTailSum1 d (natMatVec d B u) = natSumFin d (fun i => natSumFin d (fun j => G i j)) := by
    unfold natTailSum1 natMatVec
    have hc : (fun i : Fin d => if i.val = 0 then 0 else natSumFin d (fun j => B i j * u j)) =
        (fun i : Fin d => natSumFin d (fun j => G i j)) := by
      funext i
      by_cases hi : i.val = 0
      · simp only [hi, ite_true, G]
        exact (natSumFin_zero_w19 d _ (fun _ => rfl)).symm
      · simp only [hi, ite_false, G]
    rw [hc]
  rw [hlhs, natSumFin_swap_w19 d G]
  have hcol : ∀ j : Fin d,
      natSumFin d (fun i => G i j) ≥ 2 * (if j.val = 0 then 0 else u j) := by
    intro j
    by_cases hj0 : j.val = 0
    · rw [ite_true_of_w10 hj0, Nat.mul_zero]; exact Nat.zero_le _
    · rw [ite_false_of_w10 hj0]
      have hfactor : natSumFin d (fun i => G i j) = natTailSum1 d (fun i => B i j) * u j := by
        unfold natTailSum1
        have hfg : (fun i : Fin d => G i j) = (fun i : Fin d => (if i.val = 0 then 0 else B i j) * u j) := by
          funext i; dsimp [G]; by_cases hi : i.val = 0 <;> simp [hi]
        rw [hfg, natSumFin_mul_const_w19]
      rw [hfactor]
      exact Nat.mul_le_mul_right (u j) (hb_exp j (by omega))
  have h2sum : 2 * natTailSum1 d u = natSumFin d (fun j => (if j.val = 0 then 0 else u j) * 2) := by
    rw [natSumFin_mul_const_w19, Nat.mul_comm]; rfl
  rw [h2sum]
  exact natSumFin_le_w19 d _ _ (fun j => by rw [Nat.mul_comm _ 2]; exact hcol j)

-- On a `.T` (or `.L`) matrix `T` with `∀ i ≥ 1, T i j = 0`, `natTailSum1 d (T * u) = 0`:
private theorem natTailSum1_toprow_matVec_zero_w19 (d : Nat)
    (T : Fin d -> Fin d -> Nat) (u : Fin d -> Nat)
    (ht : ∀ (i j : Fin d), i.val ≥ 1 -> T i j = 0) :
    natTailSum1 d (natMatVec d T u) = 0 := by
  rw [natTailSum1_eq_zero_iff_w19]
  intro i hi
  unfold natMatVec
  exact natSumFin_zero_w19 d _ (fun j => by rw [ht i j hi, Nat.zero_mul])

-- Evaluation of `natTailSum1` on words in `GenOmegaExpandingBLowerRightAndTTopRowMatTower`:
private theorem word_tailSum_t_head_w19 (M d : Nat) (_hd : d ≥ 2)
    (mat : Fin (14 * M) -> Fin d -> Fin d -> Nat) (v : Fin (14 * M) -> Fin d -> Nat)
    (ht_zero : ∀ s : Fin (14 * M), s.val ≥ 8 * M -> ∀ (i j : Fin d), i.val ≥ 1 -> mat s i j = 0)
    (t : Fin (14 * M)) (ht : t.val ≥ 8 * M) (rest : List (Fin (14 * M))) :
    natTailSum1 d (evalFinWordVec (14 * M) d mat v (t :: rest)) = natTailSum1 d (v t) := by
  simp only [evalFinWordVec]
  rw [natTailSum1_add_w19, natTailSum1_toprow_matVec_zero_w19 d (mat t) _ (ht_zero t ht), Nat.add_zero]

private theorem word_tailSum_b_head_ge_w19 (M d : Nat) (hd : d ≥ 2)
    (mat : Fin (14 * M) -> Fin d -> Fin d -> Nat) (v : Fin (14 * M) -> Fin d -> Nat)
    (hb : ∀ s : Fin (14 * M), 4 * M ≤ s.val ∧ s.val < 8 * M ->
      mat s ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 ∧
      (∀ i : Fin d, i.val ≥ 1 -> mat s i ⟨0, by omega⟩ = 0) ∧
      (∀ j : Fin d, j.val ≥ 1 -> natTailSum1 d (fun i => mat s i j) ≥ 2))
    (b : Fin (14 * M)) (hbm : 4 * M ≤ b.val ∧ b.val < 8 * M) (rest : List (Fin (14 * M))) :
    natTailSum1 d (evalFinWordVec (14 * M) d mat v (b :: rest)) ≥
      natTailSum1 d (v b) + 2 * natTailSum1 d (evalFinWordVec (14 * M) d mat v rest) := by
  simp only [evalFinWordVec]
  rw [natTailSum1_add_w19]
  rcases hb b hbm with ⟨_, hcol0, hexp⟩
  exact Nat.add_le_add_left
    (natTailSum1_expanding_matVec_ge_two_w19 d hd (mat b) _ hcol0 hexp) _

-- Executable certificate checker for the positive rule-weight Farkas sum forcing `vTailSum = 0`
-- across all active `.B/.T/.R` symbols (`s ≥ 2 * M`), plus `.L`-equality cycles & `(0,0)` cascade:

-- Clean index-free weighted tail-sum accumulator over `(weight, lw, rw)` lists:
private def evalTailLinearCombW19 (N : Nat) (f : Fin N -> Nat) : List (Fin N × Nat) -> Nat
  | [] => 0
  | (s, c) :: tl => c * f s + evalTailLinearCombW19 N f tl

private def tailRuleTermsW19 (M : Nat) (r : List (Fin (14 * M)) × List (Fin (14 * M))) :
    Option (Fin (14 * M) × List (Fin (14 * M) × Nat)) :=
  match r.1, r.2 with
  | [t, _], [b1, u] =>
    if t.val ≥ 8 * M && 4 * M ≤ b1.val && b1.val < 8 * M then
      some (t, [(b1, 1), (u, 2)])
    else none
  | [t, _], [b1, b2, u] =>
    if t.val ≥ 8 * M && 4 * M ≤ b1.val && b1.val < 8 * M && 4 * M ≤ b2.val && b2.val < 8 * M then
      some (t, [(b1, 1), (b2, 2), (u, 4)])
    else none
  | _, _ => none

private theorem tailRuleTermsW19_sound (M d : Nat) (hd : d ≥ 2)
    (mat : Fin (14 * M) -> Fin d -> Fin d -> Nat) (v : Fin (14 * M) -> Fin d -> Nat)
    (hb : ∀ s : Fin (14 * M), 4 * M ≤ s.val ∧ s.val < 8 * M ->
      mat s ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 ∧
      (∀ i : Fin d, i.val ≥ 1 -> mat s i ⟨0, by omega⟩ = 0) ∧
      (∀ j : Fin d, j.val ≥ 1 -> natTailSum1 d (fun i => mat s i j) ≥ 2))
    (ht : ∀ s : Fin (14 * M), s.val ≥ 8 * M -> ∀ (i j : Fin d), i.val ≥ 1 -> mat s i j = 0)
    (r : List (Fin (14 * M)) × List (Fin (14 * M)))
    (t0 : Fin (14 * M)) (rhsTerms : List (Fin (14 * M) × Nat))
    (hterm : tailRuleTermsW19 M r = some (t0, rhsTerms))
    (hvec : ∀ i : Fin d, evalFinWordVec (14 * M) d mat v r.1 i ≥ evalFinWordVec (14 * M) d mat v r.2 i) :
    let S := fun s => natTailSum1 d (v s)
    S t0 ≥ evalTailLinearCombW19 (14 * M) S rhsTerms := by
  dsimp only
  have hge_tail : natTailSum1 d (evalFinWordVec (14 * M) d mat v r.1) ≥
      natTailSum1 d (evalFinWordVec (14 * M) d mat v r.2) :=
    natTailSum1_le_w19 d _ _ (fun i _ => hvec i)
  rcases r with ⟨lw, rw⟩
  dsimp only at hge_tail
  unfold tailRuleTermsW19 at hterm
  cases lw with
  | nil => cases hterm
  | cons t tl =>
    cases tl with
    | nil => cases hterm
    | cons x tl2 =>
      cases tl2 with
      | cons _ _ => cases hterm
      | nil =>
        cases rw with
        | nil => cases hterm
        | cons b1 rw1 =>
          cases rw1 with
          | nil => cases hterm
          | cons u rw2 =>
            cases rw2 with
            | nil =>
              dsimp only at hterm
              by_cases hc : (t.val ≥ 8 * M && 4 * M ≤ b1.val && b1.val < 8 * M) = true
              · rw [hc] at hterm; simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hterm
                rcases hterm with ⟨rfl, rfl⟩
                rcases bool_and_split_w19 hc with ⟨hc1, hb_hi⟩
                rcases bool_and_split_w19 hc1 with ⟨ht_lo, hb_lo⟩
                have hlhs := word_tailSum_t_head_w19 M d hd mat v ht t (of_decide_eq_true ht_lo) [x]
                have hrhs1 := word_tailSum_b_head_ge_w19 M d hd mat v hb b1
                  ⟨of_decide_eq_true hb_lo, of_decide_eq_true hb_hi⟩ [u]
                have hu_singleton : natTailSum1 d (evalFinWordVec (14 * M) d mat v [u]) =
                    natTailSum1 d (v u) := by
                  simp only [evalFinWordVec]
                  have hz : natMatVec d (mat u) (fun _ => 0) = fun _ => 0 := by
                    funext i; unfold natMatVec; exact natSumFin_zero_w19 d _ (fun _ => Nat.mul_zero _)
                  rw [hz]; simp [Nat.add_zero]
                rw [hlhs] at hge_tail
                rw [hu_singleton] at hrhs1
                dsimp only [evalTailLinearCombW19]
                omega
              · rw [Bool.eq_false_iff.mpr hc] at hterm; cases hterm
            | cons u2 rw3 =>
              cases rw3 with
              | cons _ _ => cases hterm
              | nil =>
                dsimp only at hterm
                by_cases hc : (t.val ≥ 8 * M && 4 * M ≤ b1.val && b1.val < 8 * M &&
                    4 * M ≤ u.val && u.val < 8 * M) = true
                · rw [hc] at hterm; simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hterm
                  rcases hterm with ⟨rfl, rfl⟩
                  rcases bool_and_split_w19 hc with ⟨hc3, hu_hi⟩
                  rcases bool_and_split_w19 hc3 with ⟨hc2, hu_lo⟩
                  rcases bool_and_split_w19 hc2 with ⟨hc1, hb1_hi⟩
                  rcases bool_and_split_w19 hc1 with ⟨ht_lo, hb1_lo⟩
                  have hlhs := word_tailSum_t_head_w19 M d hd mat v ht t (of_decide_eq_true ht_lo) [x]
                  have hrhs1 := word_tailSum_b_head_ge_w19 M d hd mat v hb b1
                    ⟨of_decide_eq_true hb1_lo, of_decide_eq_true hb1_hi⟩ [u, u2]
                  have hrhs2 := word_tailSum_b_head_ge_w19 M d hd mat v hb u
                    ⟨of_decide_eq_true hu_lo, of_decide_eq_true hu_hi⟩ [u2]
                  have hu2_sing : natTailSum1 d (evalFinWordVec (14 * M) d mat v [u2]) =
                      natTailSum1 d (v u2) := by
                    simp only [evalFinWordVec]
                    have hz : natMatVec d (mat u2) (fun _ => 0) = fun _ => 0 := by
                      funext i; unfold natMatVec; exact natSumFin_zero_w19 d _ (fun _ => Nat.mul_zero _)
                    rw [hz]; simp [Nat.add_zero]
                  rw [hlhs] at hge_tail
                  rw [hu2_sing] at hrhs2
                  dsimp only [evalTailLinearCombW19]
                  omega
                · rw [Bool.eq_false_iff.mpr hc] at hterm; cases hterm

private def sumWeightedTailRulesW19 (M : Nat) (S : Fin (14 * M) -> Nat) :
    List (List (Fin (14 * M)) × List (Fin (14 * M))) -> List Nat -> Nat × Nat
  | [], _ => (0, 0)
  | _, [] => (0, 0)
  | r :: rs, w :: ws =>
    let sub := sumWeightedTailRulesW19 M S rs ws
    if w == 0 then sub
    else
      match tailRuleTermsW19 M r with
      | none => sub
      | some (t0, rhsTerms) =>
        (w * S t0 + sub.1, w * evalTailLinearCombW19 (14 * M) S rhsTerms + sub.2)

private theorem sumWeightedTailRulesW19_ge (M d : Nat) (hd : d ≥ 2)
    (mat : Fin (14 * M) -> Fin d -> Fin d -> Nat) (v : Fin (14 * M) -> Fin d -> Nat)
    (hb : ∀ s : Fin (14 * M), 4 * M ≤ s.val ∧ s.val < 8 * M ->
      mat s ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 ∧
      (∀ i : Fin d, i.val ≥ 1 -> mat s i ⟨0, by omega⟩ = 0) ∧
      (∀ j : Fin d, j.val ≥ 1 -> natTailSum1 d (fun i => mat s i j) ≥ 2))
    (ht : ∀ s : Fin (14 * M), s.val ≥ 8 * M -> ∀ (i j : Fin d), i.val ≥ 1 -> mat s i j = 0) :
    ∀ (rs : List (List (Fin (14 * M)) × List (Fin (14 * M)))) (ws : List Nat),
      (∀ r ∈ rs, ∀ i : Fin d,
        evalFinWordVec (14 * M) d mat v r.1 i ≥ evalFinWordVec (14 * M) d mat v r.2 i) ->
      let p := sumWeightedTailRulesW19 M (fun s => natTailSum1 d (v s)) rs ws
      p.1 ≥ p.2
  | [], _, _ => Nat.le_refl 0
  | _ :: _, [], _ => Nat.le_refl 0
  | r :: rs, w :: ws, hall => by
    dsimp only [sumWeightedTailRulesW19]
    have ih := sumWeightedTailRulesW19_ge M d hd mat v hb ht rs ws
      (fun r' hr' => hall r' (List.Mem.tail r hr'))
    dsimp only at ih
    cases hw0 : (w == 0)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hterm : tailRuleTermsW19 M r with
      | none => exact ih
      | some tr =>
        rcases tr with ⟨t0, rhsTerms⟩
        dsimp only
        have hr_ge := tailRuleTermsW19_sound M d hd mat v hb ht r t0 rhsTerms hterm
          (hall r (List.Mem.head _))
        exact Nat.add_le_add (Nat.mul_le_mul_left w hr_ge) ih
    · simp only [↓reduceIte]; exact ih

private theorem sumWeightedTailRulesW19_basis_decomp (M : Nat) :
    ∀ (rs : List (List (Fin (14 * M)) × List (Fin (14 * M)))) (ws : List Nat) (S : Fin (14 * M) -> Nat),
      sumWeightedTailRulesW19 M S rs ws =
        (natSumFin (14 * M) (fun s0 =>
           (sumWeightedTailRulesW19 M (fun s => if s = s0 then 1 else 0) rs ws).1 * S s0),
         natSumFin (14 * M) (fun s0 =>
           (sumWeightedTailRulesW19 M (fun s => if s = s0 then 1 else 0) rs ws).2 * S s0)) := by
  have hpoint : ∀ (s : Fin (14 * M)) (S : Fin (14 * M) -> Nat),
      14 * M ≥ 1 ->
      S s = natSumFin (14 * M) (fun s0 => (if s = s0 then 1 else 0) * S s0) := by
    intro s S _
    have hpre : ∀ n : Nat, s.val < n -> n ≤ 14 * M ->
        natSumPrefix (14 * M) (fun s0 => (if s = s0 then 1 else 0) * S s0) n = S s := by
      intro n; induction n with
      | zero => intro hlt _; omega
      | succ n' ih =>
        intro hlt hle
        have hn_lt : n' < 14 * M := hle
        unfold natSumPrefix
        simp only [hn_lt, dite_true]
        by_cases heq : s.val = n'
        · have hs_eq : s = ⟨n', hn_lt⟩ := Fin.ext heq
          subst hs_eq
          have hz : natSumPrefix (14 * M) (fun s0 => (if (⟨n', hn_lt⟩ : Fin (14 * M)) = s0 then 1 else 0) * S s0) n' = 0 := by
            have h0 : ∀ k : Nat, k ≤ n' ->
                natSumPrefix (14 * M) (fun s0 => (if (⟨n', hn_lt⟩ : Fin (14 * M)) = s0 then 1 else 0) * S s0) k = 0 := by
              intro k; induction k with
              | zero => intros; rfl
              | succ k' ihk =>
                intro hk
                have hk_lt : k' < 14 * M := by omega
                have hne : (⟨n', hn_lt⟩ : Fin (14 * M)) ≠ ⟨k', hk_lt⟩ := fun h => by
                  have := congrArg Fin.val h; dsimp at this; omega
                unfold natSumPrefix
                simp only [hk_lt, dite_true, ihk (by omega), ite_false_of_w10 hne, Nat.zero_mul, Nat.add_zero]
            exact h0 n' (Nat.le_refl n')
          rw [hz, Nat.zero_add, ite_true_of_w10 rfl, Nat.one_mul]
        · have hne : s ≠ ⟨n', hn_lt⟩ := fun h => heq (congrArg Fin.val h)
          rw [ih (by omega) (by omega), ite_false_of_w10 hne, Nat.zero_mul, Nat.add_zero]
    by_cases hM0 : 14 * M = 0
    · exact Fin.elim0 (hM0 ▸ s)
    · exact (hpre (14 * M) s.isLt (Nat.le_refl _)).symm
  have hlin : ∀ (terms : List (Fin (14 * M) × Nat)) (S : Fin (14 * M) -> Nat),
      14 * M ≥ 1 ->
      evalTailLinearCombW19 (14 * M) S terms =
        natSumFin (14 * M) (fun s0 =>
          evalTailLinearCombW19 (14 * M) (fun s => if s = s0 then 1 else 0) terms * S s0) := by
    intro terms S hpos; induction terms with
    | nil =>
      dsimp [evalTailLinearCombW19]
      exact (natSumFin_zero_w19 _ _ (fun _ => Nat.zero_mul _)).symm
    | cons sc tl ih =>
      rcases sc with ⟨s, c⟩
      dsimp only [evalTailLinearCombW19]
      rw [ih]
      conv => lhs; lhs; rw [hpoint s S hpos, Nat.mul_comm c _, ← natSumFin_mul_const_w19]
      rw [← natSumFin_add_w19]
      apply congrArg (natSumFin (14 * M))
      funext s0; rw [Nat.add_mul]
      congr 1; ac_rfl
  intro rs; induction rs with
  | nil =>
    intro ws S
    dsimp [sumWeightedTailRulesW19]
    exact Prod.ext
      (natSumFin_zero_w19 _ _ (fun _ => Nat.zero_mul _)).symm
      (natSumFin_zero_w19 _ _ (fun _ => Nat.zero_mul _)).symm
  | cons r rs' ih =>
    intro ws S
    cases ws with
    | nil =>
      dsimp [sumWeightedTailRulesW19]
      exact Prod.ext
        (natSumFin_zero_w19 _ _ (fun _ => Nat.zero_mul _)).symm
        (natSumFin_zero_w19 _ _ (fun _ => Nat.zero_mul _)).symm
    | cons w ws' =>
      by_cases hM0 : M = 0
      · subst hM0
        have he0 : ∀ f : Fin 0 -> Nat, natSumFin 0 f = 0 := fun _ => rfl
        simp only [Nat.mul_zero] at *
        have hall0 : ∀ (rs0 : List (List (Fin 0) × List (Fin 0))) (ws0 : List Nat) (f : Fin 0 -> Nat),
            sumWeightedTailRulesW19 0 f rs0 ws0 = (0, 0) := by
          intro rs0; induction rs0 with
          | nil => intros; rfl
          | cons r0 tl0 ih0 =>
            intro ws0 f; cases ws0 with
            | nil => rfl
            | cons w0 wtl0 =>
              dsimp only [sumWeightedTailRulesW19]
              rcases r0 with ⟨l0, rr0⟩
              cases l0 with
              | cons x _ => exact Fin.elim0 x
              | nil =>
                have ht0 : tailRuleTermsW19 0 ([], rr0) = none := rfl
                rw [ht0, ih0]
                cases (w0 == 0) <;> rfl
        rw [hall0, he0, he0]
      · have hpos14 : 14 * M ≥ 1 := by omega
        dsimp only [sumWeightedTailRulesW19]
        cases hw0 : (w == 0)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases hterm : tailRuleTermsW19 M r with
          | none => exact ih ws' S
          | some tr =>
            rcases tr with ⟨t0, rhsTerms⟩
            dsimp only
            rw [ih ws' S]
            apply Prod.ext
            · dsimp only
              conv => lhs; lhs; rw [hpoint t0 S hpos14, Nat.mul_comm w _, ← natSumFin_mul_const_w19]
              rw [← natSumFin_add_w19]
              apply congrArg (natSumFin (14 * M))
              funext s0; rw [Nat.add_mul]; congr 1; ac_rfl
            · dsimp only
              conv => lhs; lhs; rw [hlin rhsTerms S hpos14, Nat.mul_comm w _, ← natSumFin_mul_const_w19]
              rw [← natSumFin_add_w19]
              apply congrArg (natSumFin (14 * M))
              funext s0; rw [Nat.add_mul]; congr 1; ac_rfl
        · simp only [↓reduceIte]; exact ih ws' S

private def tailWeightsC39W19 : List Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0,
   2, 3, 2, 3, 1, 2, 2, 1, 4, 2, 3, 1, 1, 1, 2, 1, 1, 1, 1,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

private def tailWeightsC78W19 : List Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   2, 5, 2, 1, 3, 1, 1, 6, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5, 2, 2, 3, 5, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

private def checkTailCollapseDomBoolW19 (M : Nat)
    (rs : List (List (Fin (14 * M)) × List (Fin (14 * M)))) (ws : List Nat) : Nat -> Bool
  | 0 => true
  | s + 1 =>
    let ok_s :=
      if s < 2 * M || !(symAppearsInRulesBool (14 * M) s rs) then
        if hlt : s < 14 * M then
          let p := sumWeightedTailRulesW19 M (fun x => if x = ⟨s, hlt⟩ then 1 else 0) rs ws
          Nat.ble p.1 p.2
        else true
      else
        if hlt : s < 14 * M then
          let p := sumWeightedTailRulesW19 M (fun x => if x = ⟨s, hlt⟩ then 1 else 0) rs ws
          Nat.ble (p.1 + 1) p.2
        else true
    ok_s && checkTailCollapseDomBoolW19 M rs ws s

set_option maxRecDepth 65536 in
private theorem tail_collapse_dom_c39_w19 :
    checkTailCollapseDomBoolW19 3 c39FastRulesW19 tailWeightsC39W19 42 = true := by decide

set_option maxRecDepth 65536 in
private theorem tail_collapse_dom_c78_w19 :
    checkTailCollapseDomBoolW19 6 c78FastRulesW19 tailWeightsC78W19 84 = true := by decide

private theorem unpack_tailCollapseDom_w19 (M : Nat)
    (rs : List (List (Fin (14 * M)) × List (Fin (14 * M)))) (ws : List Nat) :
    ∀ k : Nat, checkTailCollapseDomBoolW19 M rs ws k = true ->
      ∀ s : Fin (14 * M), s.val < k ->
        let p := sumWeightedTailRulesW19 M (fun x => if x = s then 1 else 0) rs ws
        p.1 ≤ p.2 ∧ (s.val ≥ 2 * M -> symAppearsInRulesBool (14 * M) s.val rs = true -> p.1 + 1 ≤ p.2)
  | 0, _, s, hlt => by omega
  | k' + 1, hchk, s, hlt => by
    unfold checkTailCollapseDomBoolW19 at hchk
    rcases bool_and_split_w19 hchk with ⟨hok, hprev⟩
    by_cases heq : s.val = k'
    · have hk_lt : k' < 14 * M := heq ▸ s.isLt
      have hs_eq : (⟨k', hk_lt⟩ : Fin (14 * M)) = s := Fin.ext heq.symm
      dsimp only at hok ⊢
      by_cases hcond : (k' < 2 * M || !(symAppearsInRulesBool (14 * M) k' rs)) = true
      · simp only [hcond, ↓reduceIte, hk_lt, dite_true, hs_eq] at hok
        refine ⟨Nat.ble_eq.mp hok, fun hge2M happ => ?_⟩
        rw [← heq] at hcond
        have hnlt : ¬ (s.val < 2 * M) := by omega
        simp only [decide_eq_false hnlt, Bool.false_or, happ, Bool.not_true] at hcond
        cases hcond
      · simp only [Bool.eq_false_iff.mpr hcond, Bool.false_eq_true, ↓reduceIte, hk_lt, dite_true, hs_eq] at hok
        have hlt_p := Nat.ble_eq.mp hok
        exact ⟨by omega, fun _ _ => hlt_p⟩
    · exact unpack_tailCollapseDom_w19 M rs ws k' hprev s (by omega)

private theorem active_btr_tail_zero_of_dom_w19 (M d : Nat) (hd : d ≥ 2)
    (rs : List (List (Fin (14 * M)) × List (Fin (14 * M)))) (ws : List Nat)
    (hdom : checkTailCollapseDomBoolW19 M rs ws (14 * M) = true)
    (mat : Fin (14 * M) -> Fin d -> Fin d -> Nat) (v : Fin (14 * M) -> Fin d -> Nat)
    (hb : ∀ s : Fin (14 * M), 4 * M ≤ s.val ∧ s.val < 8 * M ->
      mat s ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 ∧
      (∀ i : Fin d, i.val ≥ 1 -> mat s i ⟨0, by omega⟩ = 0) ∧
      (∀ j : Fin d, j.val ≥ 1 -> natTailSum1 d (fun i => mat s i j) ≥ 2))
    (ht : ∀ s : Fin (14 * M), s.val ≥ 8 * M -> ∀ (i j : Fin d), i.val ≥ 1 -> mat s i j = 0)
    (hvec : ∀ r ∈ rs, ∀ i : Fin d,
      evalFinWordVec (14 * M) d mat v r.1 i ≥ evalFinWordVec (14 * M) d mat v r.2 i) :
    ∀ s : Fin (14 * M), s.val ≥ 2 * M -> symAppearsInRulesBool (14 * M) s.val rs = true ->
      ∀ i : Fin d, i.val ≥ 1 -> v s i = 0 := by
  let S (x : Fin (14 * M)) : Nat := natTailSum1 d (v x)
  have hsum_ge := sumWeightedTailRulesW19_ge M d hd mat v hb ht rs ws hvec
  dsimp only at hsum_ge
  rw [sumWeightedTailRulesW19_basis_decomp M rs ws S] at hsum_ge
  dsimp only at hsum_ge
  have hpt := unpack_tailCollapseDom_w19 M rs ws (14 * M) hdom
  intro s0 hs0_ge happ0
  suffices hS0 : S s0 = 0 by
    exact (natTailSum1_eq_zero_iff_w19 d (v s0)).mp hS0
  by_cases hpos : S s0 = 0
  · exact hpos
  · exfalso
    let fL (x : Fin (14 * M)) : Nat :=
      (sumWeightedTailRulesW19 M (fun y => if y = x then 1 else 0) rs ws).1 * S x
    let fR (x : Fin (14 * M)) : Nat :=
      (sumWeightedTailRulesW19 M (fun y => if y = x then 1 else 0) rs ws).2 * S x
    have hstrict_at : ∀ n : Nat, s0.val < n -> n ≤ 14 * M ->
        natSumPrefix (14 * M) fL n + 1 ≤ natSumPrefix (14 * M) fR n := by
      intro n; induction n with
      | zero => intro hlt _; omega
      | succ n' ih =>
        intro hlt hle
        have hn_lt : n' < 14 * M := hle
        unfold natSumPrefix
        simp only [hn_lt, dite_true]
        by_cases heq : s0.val = n'
        · have hs_eq : (⟨n', hn_lt⟩ : Fin (14 * M)) = s0 := Fin.ext heq.symm
          rw [hs_eq]
          have hpre_le := natSumPrefix_le_w19 (14 * M) fL fR
            (fun x => Nat.mul_le_mul_right (S x) (hpt x x.isLt).1) n'
          have hstrict_c := (hpt s0 s0.isLt).2 hs0_ge happ0
          have hm : ((sumWeightedTailRulesW19 M (fun y => if y = s0 then 1 else 0) rs ws).1 + 1) * S s0 ≤
              (sumWeightedTailRulesW19 M (fun y => if y = s0 then 1 else 0) rs ws).2 * S s0 :=
            Nat.mul_le_mul_right (S s0) hstrict_c
          rw [Nat.add_mul, Nat.one_mul] at hm
          have hfl_s0 : fL s0 + S s0 ≤ fR s0 := hm
          omega
        · have ih_n := ih (by omega) (by omega)
          have hcur : fL ⟨n', hn_lt⟩ ≤ fR ⟨n', hn_lt⟩ :=
            Nat.mul_le_mul_right (S ⟨n', hn_lt⟩) (hpt ⟨n', hn_lt⟩ hn_lt).1
          omega
    have hlt_tot := hstrict_at (14 * M) s0.isLt (Nat.le_refl _)
    change natSumPrefix (14 * M) fL (14 * M) ≥ natSumPrefix (14 * M) fR (14 * M) at hsum_ge
    omega

-- Cascade forcing `(M_t)_{0,0} = 1` across ALL active `.T` symbols of `c39` and `c78`
-- whenever `.L` and `.B` have `(0,0) = 1` and `.L, .B, .T` all have `i ≥ 1 -> M[i, 0] = 0`!

private def expCascadeC39W19 : List (Nat × Nat × Nat × Nat) :=
  [(1, 18, 2, 36), (2, 20, 2, 38), (36, 22, 20, 40), (38, 16, 13, 31),
   (38, 23, 20, 41), (40, 17, 16, 32), (40, 21, 23, 39), (31, 14, 18, 29),
   (32, 13, 18, 28), (28, 18, 22, 33), (29, 20, 22, 35), (33, 22, 17, 37)]

private def expCascadeC78W19 : List (Nat × Nat × Nat × Nat) :=
  [(1, 36, 2, 72), (1, 39, 5, 75), (5, 38, 2, 74), (5, 41, 5, 77),
   (74, 31, 28, 61), (74, 34, 25, 64), (75, 43, 41, 79), (75, 46, 38, 82),
   (77, 44, 38, 80), (77, 47, 41, 83), (79, 42, 44, 78), (79, 45, 47, 81),
   (82, 32, 31, 62), (82, 35, 34, 65), (62, 25, 39, 55), (62, 28, 36, 58),
   (64, 26, 36, 56), (64, 29, 39, 59), (55, 36, 43, 66), (55, 39, 46, 69),
   (59, 38, 43, 68), (59, 41, 46, 71), (69, 43, 35, 73), (69, 46, 32, 76)]

private def inUnit00SetBoolW19 (M : Nat) (acc : List Nat) (x : Nat) : Bool :=
  Nat.ble (x + 1) (2 * M) || (Nat.ble (4 * M) x && Nat.ble (x + 1) (8 * M)) || acc.any (· == x)

private def hasLen2RuleValsW19 (N s1 s2 u1 u2 : Nat) :
    List (List (Fin N) × List (Fin N)) -> Bool
  | [] => false
  | ([a, b], [c, d]) :: rs =>
    (a.val == s1 && b.val == s2 && c.val == u1 && d.val == u2) ||
      hasLen2RuleValsW19 N s1 s2 u1 u2 rs
  | _ :: rs => hasLen2RuleValsW19 N s1 s2 u1 u2 rs

private def runUnit00CascadeW19 (M : Nat)
    (rs : List (List (Fin (14 * M)) × List (Fin (14 * M))))
    (acc : List Nat) : List (Nat × Nat × Nat × Nat) -> Option (List Nat)
  | [] => some acc
  | (s1, s2, u1, u2) :: rest =>
    if inUnit00SetBoolW19 M acc s1 && inUnit00SetBoolW19 M acc s2 &&
       !(Nat.ble (2 * M) s2 && Nat.ble (s2 + 1) (4 * M)) &&
       !(Nat.ble (2 * M) u2 && Nat.ble (u2 + 1) (4 * M)) &&
       hasLen2RuleValsW19 (14 * M) s1 s2 u1 u2 rs then
      runUnit00CascadeW19 M rs (u1 :: u2 :: acc) rest
    else none

private theorem mat2_00_prod_of_col0_zero_w19 (N d : Nat) (hd : d ≥ 1)
    (mat : Fin N -> Fin d -> Fin d -> Nat) (x y : Fin N)
    (hy_col0 : ∀ q : Fin d, q.val ≥ 1 -> mat y q ⟨0, hd⟩ = 0) :
    evalFinWordMat N d mat [x, y] ⟨0, hd⟩ ⟨0, hd⟩ =
      mat x ⟨0, hd⟩ ⟨0, hd⟩ * mat y ⟨0, hd⟩ ⟨0, hd⟩ := by
  have hy_id : evalFinWordMat N d mat [y] ⟨0, hd⟩ ⟨0, hd⟩ = mat y ⟨0, hd⟩ ⟨0, hd⟩ := by
    simp only [evalFinWordMat, natMatMul]
    rw [natSumFin_single_zero_w19 d hd _ (fun q hq => by simp [natMatId, show ¬ (q.val = 0) by omega])]
    simp [natMatId]
  have hy_q : ∀ q : Fin d, q.val ≥ 1 -> evalFinWordMat N d mat [y] q ⟨0, hd⟩ = 0 := by
    intro q hq
    simp only [evalFinWordMat, natMatMul]
    rw [natSumFin_single_zero_w19 d hd _ (fun k hk => by simp [natMatId, show ¬ (k.val = 0) by omega])]
    simp [natMatId, hy_col0 q hq]
  simp only [evalFinWordMat, natMatMul] at hy_id hy_q ⊢
  rw [natSumFin_single_zero_w19 d hd _ (fun q hq => by rw [hy_q q hq, Nat.mul_zero]), hy_id]

private theorem hasLen2RuleValsW19_mem (N s1 s2 u1 u2 : Nat) :
    ∀ rs : List (List (Fin N) × List (Fin N)),
      hasLen2RuleValsW19 N s1 s2 u1 u2 rs = true ->
      ∃ (a b c d : Fin N), a.val = s1 ∧ b.val = s2 ∧ c.val = u1 ∧ d.val = u2 ∧ ([a, b], [c, d]) ∈ rs
  | [], h => by cases h
  | (lw, rw) :: rs, h => by
    cases lw with
    | nil => exact let ⟨a,b,c,d,h1,h2,h3,h4,hm⟩ := hasLen2RuleValsW19_mem N s1 s2 u1 u2 rs h
                   ⟨a,b,c,d,h1,h2,h3,h4,List.mem_cons_of_mem _ hm⟩
    | cons a l1 =>
      cases l1 with
      | nil => exact let ⟨a',b,c,d,h1,h2,h3,h4,hm⟩ := hasLen2RuleValsW19_mem N s1 s2 u1 u2 rs h
                     ⟨a',b,c,d,h1,h2,h3,h4,List.mem_cons_of_mem _ hm⟩
      | cons b l2 =>
        cases l2 with
        | cons _ _ => exact let ⟨a',b',c,d,h1,h2,h3,h4,hm⟩ := hasLen2RuleValsW19_mem N s1 s2 u1 u2 rs h
                            ⟨a',b',c,d,h1,h2,h3,h4,List.mem_cons_of_mem _ hm⟩
        | nil =>
          cases rw with
          | nil => exact let ⟨a',b',c,d,h1,h2,h3,h4,hm⟩ := hasLen2RuleValsW19_mem N s1 s2 u1 u2 rs h
                         ⟨a',b',c,d,h1,h2,h3,h4,List.Mem.tail _ hm⟩
          | cons c r1 =>
            cases r1 with
            | nil => exact let ⟨a',b',c',d,h1,h2,h3,h4,hm⟩ := hasLen2RuleValsW19_mem N s1 s2 u1 u2 rs h
                           ⟨a',b',c',d,h1,h2,h3,h4,List.Mem.tail _ hm⟩
            | cons d r2 =>
              cases r2 with
              | cons _ _ => exact let ⟨a',b',c',d',h1,h2,h3,h4,hm⟩ := hasLen2RuleValsW19_mem N s1 s2 u1 u2 rs h
                                  ⟨a',b',c',d',h1,h2,h3,h4,List.Mem.tail _ hm⟩
              | nil =>
                unfold hasLen2RuleValsW19 at h
                rcases Bool.or_eq_true_iff.mp h with hcur | htl
                · rcases bool_and_split_w19 hcur with ⟨hc3, hd_eq⟩
                  rcases bool_and_split_w19 hc3 with ⟨hc2, hc_eq⟩
                  rcases bool_and_split_w19 hc2 with ⟨ha_eq, hb_eq⟩
                  exact ⟨a, b, c, d, beq_iff_eq.mp ha_eq, beq_iff_eq.mp hb_eq,
                         beq_iff_eq.mp hc_eq, beq_iff_eq.mp hd_eq, List.Mem.head _⟩
                · rcases hasLen2RuleValsW19_mem N s1 s2 u1 u2 rs htl with ⟨a',b',c',d',h1,h2,h3,h4,hm⟩
                  exact ⟨a',b',c',d',h1,h2,h3,h4,List.Mem.tail _ hm⟩

private theorem runUnit00CascadeW19_sound (M d : Nat) (hd : d ≥ 1)
    (rs : List (List (Fin (14 * M)) × List (Fin (14 * M))))
    (mat : Fin (14 * M) -> Fin d -> Fin d -> Nat)
    (hpos : ∀ s : Fin (14 * M), mat s ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1)
    (hl1 : ∀ s : Fin (14 * M), s.val < 2 * M -> mat s ⟨0, hd⟩ ⟨0, hd⟩ = 1)
    (hb1 : ∀ s : Fin (14 * M), 4 * M ≤ s.val ∧ s.val < 8 * M -> mat s ⟨0, hd⟩ ⟨0, hd⟩ = 1)
    (hcol0 : ∀ s : Fin (14 * M), ¬ (2 * M ≤ s.val ∧ s.val < 4 * M) ->
      ∀ q : Fin d, q.val ≥ 1 -> mat s q ⟨0, hd⟩ = 0)
    (hmat : ∀ r ∈ rs, ∀ i j : Fin d, evalFinWordMat (14 * M) d mat r.1 i j ≥ evalFinWordMat (14 * M) d mat r.2 i j) :
    ∀ (steps : List (Nat × Nat × Nat × Nat)) (acc out : List Nat),
      (∀ s : Fin (14 * M), inUnit00SetBoolW19 M acc s.val = true -> mat s ⟨0, hd⟩ ⟨0, hd⟩ = 1) ->
      runUnit00CascadeW19 M rs acc steps = some out ->
      ∀ s : Fin (14 * M), inUnit00SetBoolW19 M out s.val = true -> mat s ⟨0, hd⟩ ⟨0, hd⟩ = 1
  | [], acc, out, hacc, hrun => by
    injection hrun with heq; subst heq; exact hacc
  | (s1, s2, u1, u2) :: rest, acc, out, hacc, hrun => by
    unfold runUnit00CascadeW19 at hrun
    by_cases hc : (inUnit00SetBoolW19 M acc s1 && inUnit00SetBoolW19 M acc s2 &&
        !(Nat.ble (2 * M) s2 && Nat.ble (s2 + 1) (4 * M)) &&
        !(Nat.ble (2 * M) u2 && Nat.ble (u2 + 1) (4 * M)) &&
        hasLen2RuleValsW19 (14 * M) s1 s2 u1 u2 rs) = true
    · rw [hc] at hrun; simp only [↓reduceIte] at hrun
      rcases bool_and_split_w19 hc with ⟨hc4, hmem_b⟩
      rcases bool_and_split_w19 hc4 with ⟨hc3, hnu2⟩
      rcases bool_and_split_w19 hc3 with ⟨hc2, hns2⟩
      rcases bool_and_split_w19 hc2 with ⟨hs1_in, hs2_in⟩
      rcases hasLen2RuleValsW19_mem (14 * M) s1 s2 u1 u2 rs hmem_b with
        ⟨fa, fb, fc, fd, hfa, hfb, hfc, hfd, hrmem⟩
      have ha1 : mat fa ⟨0, hd⟩ ⟨0, hd⟩ = 1 := hacc fa (hfa.symm ▸ hs1_in)
      have hb_eq1 : mat fb ⟨0, hd⟩ ⟨0, hd⟩ = 1 := hacc fb (hfb.symm ▸ hs2_in)
      have hfb_nr : ¬ (2 * M ≤ fb.val ∧ fb.val < 4 * M) := by
        intro ⟨hlo, hhi⟩; rw [← hfb] at hns2
        rw [Nat.ble_eq.mpr hlo, Nat.ble_eq.mpr hhi] at hns2; cases hns2
      have hfd_nr : ¬ (2 * M ≤ fd.val ∧ fd.val < 4 * M) := by
        intro ⟨hlo, hhi⟩; rw [← hfd] at hnu2
        rw [Nat.ble_eq.mpr hlo, Nat.ble_eq.mpr hhi] at hnu2; cases hnu2
      have hineq := hmat ([fa, fb], [fc, fd]) hrmem ⟨0, hd⟩ ⟨0, hd⟩
      rw [mat2_00_prod_of_col0_zero_w19 (14 * M) d hd mat fa fb (hcol0 fb hfb_nr),
          mat2_00_prod_of_col0_zero_w19 (14 * M) d hd mat fc fd (hcol0 fd hfd_nr),
          ha1, hb_eq1, Nat.mul_one] at hineq
      have hfc_pos := hpos fc; have hfd_pos := hpos fd
      have hfc1 : mat fc ⟨0, hd⟩ ⟨0, hd⟩ = 1 := by
        by_cases hgt : mat fc ⟨0, hd⟩ ⟨0, hd⟩ ≥ 2
        · have := Nat.mul_le_mul hgt hfd_pos; omega
        · omega
      have hfd1 : mat fd ⟨0, hd⟩ ⟨0, hd⟩ = 1 := by rw [hfc1, Nat.one_mul] at hineq; omega
      apply runUnit00CascadeW19_sound M d hd rs mat hpos hl1 hb1 hcol0 hmat rest (u1 :: u2 :: acc) out _ hrun
      intro s hs_in
      unfold inUnit00SetBoolW19 at hs_in
      rcases Bool.or_eq_true_iff.mp hs_in with hlb | hlist
      · exact hacc s (by unfold inUnit00SetBoolW19; rw [hlb, Bool.true_or])
      · simp only [List.any_cons] at hlist
        rcases Bool.or_eq_true_iff.mp hlist with heq1 | hlist2
        · have hv : s = fc := Fin.ext ((beq_iff_eq.mp heq1).symm.trans hfc.symm)
          rwa [hv]
        · rcases Bool.or_eq_true_iff.mp hlist2 with heq2 | hlist3
          · have hv : s = fd := Fin.ext ((beq_iff_eq.mp heq2).symm.trans hfd.symm)
            rwa [hv]
          · exact hacc s (by unfold inUnit00SetBoolW19; rw [hlist3, Bool.or_true])
    · rw [Bool.eq_false_iff.mpr hc] at hrun; cases hrun

-- Check that the cascade covers all active `.T` symbols AND verify `.L`-class equality + non-`.R` prefix property:

private def allNatLoopW19 (p : Nat -> Bool) : Nat -> Bool
  | 0 => true
  | k + 1 => p k && allNatLoopW19 p k

private theorem allNatLoopW19_spec (p : Nat -> Bool) :
    ∀ k : Nat, allNatLoopW19 p k = true -> ∀ x : Nat, x < k -> p x = true
  | 0, _, _, hx => by omega
  | k' + 1, ha, x, hx => by
    unfold allNatLoopW19 at ha
    rcases bool_and_split_w19 ha with ⟨hk, hprev⟩
    by_cases heq : x = k'
    · subst heq; exact hk
    · exact allNatLoopW19_spec p k' hprev x (by omega)

private def checkExpandingFullCollapseCertW19 (M : Nat)
    (rs : List (List (Fin (14 * M)) × List (Fin (14 * M))))
    (steps : List (Nat × Nat × Nat × Nat))
    (lPairs : List (Nat × Nat)) : Bool :=
  match runUnit00CascadeW19 M rs [] steps with
  | none => false
  | some out =>
    allNatLoopW19 (fun s =>
      if s ≥ 8 * M && symAppearsInRulesBool (14 * M) s rs then
        inUnit00SetBoolW19 M out s
      else true) (14 * M) &&
    rs.all (fun r =>
      match r.1, r.2 with
      | l0 :: ltl, r0 :: rtl =>
        ltl.all (fun x => x.val ≥ 2 * M) && rtl.all (fun x => x.val ≥ 2 * M) &&
        (r.1.dropLast).all (fun x => !(2 * M ≤ x.val && x.val < 4 * M) && inUnit00SetBoolW19 M out x.val) &&
        (r.2.dropLast).all (fun x => !(2 * M ≤ x.val && x.val < 4 * M) && inUnit00SetBoolW19 M out x.val) &&
        ((l0.val < 2 * M && r0.val < 2 * M && decide ((l0.val, r0.val) ∈ lPairs)) ||
         (l0.val ≥ 2 * M && r0.val ≥ 2 * M))
      | _, _ => false) &&
    rs.all (fun r =>
      r.1.all (fun x => (2 * M ≤ x.val && x.val < 4 * M) || inUnit00SetBoolW19 M out x.val) &&
      r.2.all (fun x => (2 * M ≤ x.val && x.val < 4 * M) || inUnit00SetBoolW19 M out x.val) &&
      r.1.all (fun x => symAppearsInRulesBool (14 * M) x.val rs) &&
      r.2.all (fun x => symAppearsInRulesBool (14 * M) x.val rs))

private def lEqPairsC39W19 : List (Nat × Nat) :=
  [(1, 1), (2, 2), (1, 2), (2, 1), (4, 4), (5, 5), (4, 5), (5, 4)]

private def lEqPairsC78W19 : List (Nat × Nat) :=
  [(1,1),(2,2),(4,4),(5,5),(1,2),(2,1),(1,5),(5,1),(2,4),(4,2),(2,5),(5,2),(4,5),(5,4),
   (7,7),(8,8),(10,10),(11,11),(7,8),(8,7),(7,11),(11,7),(8,10),(10,8),(8,11),(11,8),(10,11),(11,10)]

set_option maxRecDepth 65536 in
private theorem exp_full_cert_c39_w19 :
    checkExpandingFullCollapseCertW19 3 c39FastRulesW19 expCascadeC39W19 lEqPairsC39W19 = true := by decide

-- Let's also check strict matrix count 27/39 and weak 39/39 for `expandingBWitnessMat2DC39`:
private theorem exp2d_witness_c39_certs_w19 :
    countStrictMat2DRules 42 (expandingBWitnessMat2DC39 2) c39FastRulesW19 = 27 ∧
    c39FastRulesW19.all (fun r =>
      decide (∀ i j : Fin 2,
        evalFinWordMat 42 2 (expandingBWitnessMat2DC39 1) r.1 i j ≥
          evalFinWordMat 42 2 (expandingBWitnessMat2DC39 1) r.2 i j) &&
      decide (∀ i j : Fin 2,
        evalFinWordMat 42 2 (expandingBWitnessMat2DC39 2) r.1 i j ≥
          evalFinWordMat 42 2 (expandingBWitnessMat2DC39 2) r.2 i j)) = true := by decide

set_option maxRecDepth 65536 in
private theorem exp_full_cert_c78_only_w19 :
    checkExpandingFullCollapseCertW19 6 c78FastRulesW19 expCascadeC78W19 lEqPairsC78W19 = true := by decide

-- Positive Parikh-syzygy certificates on row 0 using `syzTwoSidedMod3OmitR3Core39` and `syzTwoSidedMod6OmitR3Core78`:
set_option maxRecDepth 65536 in
private theorem parikh_syz_c39_c78_w19 :
    checkPositiveParikhSyzygyFastBool 42 c39FastRulesW19 syzTwoSidedMod3OmitR3Core39 = true ∧
    checkPositiveParikhSyzygyFastBool 84 c78FastRulesW19 syzTwoSidedMod6OmitR3Core78 = true := by decide

private theorem parikh_zero_strict_of_fast_syz_w19 (N : Nat)
    (rs : List (List (Fin N) × List (Fin N))) (syz : List Nat)
    (hsyz : checkPositiveParikhSyzygyFastBool N rs syz = true)
    (wt : Fin N -> Nat)
    (hweak : ∀ r ∈ rs, evalFinParikh N wt r.1 ≥ evalFinParikh N wt r.2) :
    ∀ r ∈ rs, evalFinParikh N wt r.1 = evalFinParikh N wt r.2 := by
  unfold checkPositiveParikhSyzygyFastBool at hsyz
  rcases bool_and_split_w19 hsyz with ⟨hs1, hpairs⟩
  rcases bool_and_split_w19 hs1 with ⟨hs2, hpos_m⟩
  rcases bool_and_split_w19 hs2 with ⟨_, hlen_eq⟩
  have hlen : rs.length = syz.length := of_decide_eq_true hlen_eq
  rcases accumSymCountsW11_spec N rs syz with ⟨hacc_len, hacc_get⟩
  rcases weightedParikh_eq_sum_sym N wt rs syz with ⟨hl_sum, hr_sum⟩
  have hpar_le : weightedParikhLhs N wt rs syz ≤ weightedParikhRhs N wt rs syz := by
    rw [hl_sum, hr_sum]
    exact natSumPrefix_mono_w5 N _ _ (fun s => Nat.mul_le_mul_left (wt s) (by
      have hle := checkPairsLeBoolW11_sound _ hpairs s.val (by rw [hacc_len]; exact s.isLt)
      rwa [hacc_get s] at hle)) N
  have hpar_all_eq : ∀ (rs0 : List (List (Fin N) × List (Fin N))) (ms : List Nat),
      rs0.length = ms.length ->
      checkAllPosNatList ms = true ->
      (∀ r ∈ rs0, evalFinParikh N wt r.1 ≥ evalFinParikh N wt r.2) ->
      weightedParikhLhs N wt rs0 ms ≥ weightedParikhRhs N wt rs0 ms ∧
      (weightedParikhLhs N wt rs0 ms ≤ weightedParikhRhs N wt rs0 ms ->
        ∀ r ∈ rs0, evalFinParikh N wt r.1 = evalFinParikh N wt r.2) := by
    intro rs0; induction rs0 with
    | nil => intros; exact ⟨Nat.le_refl 0, fun _ _ hr => by cases hr⟩
    | cons r0 rtl ih =>
      intro ms hl hp hw_r
      cases ms with
      | nil => simp at hl
      | cons m0 mtl =>
        rcases bool_and_split_w19 hp with ⟨hm0_b, hmtl_p⟩
        have hm0_pos : m0 ≥ 1 := of_decide_eq_true hm0_b
        rcases ih mtl (by simp at hl; omega) hmtl_p
          (fun q hq => hw_r q (List.Mem.tail r0 hq)) with ⟨hge_tl, himp_tl⟩
        have hm0_ge := Nat.mul_le_mul_left m0 (hw_r r0 (List.Mem.head _))
        simp only [weightedParikhLhs, weightedParikhRhs]
        refine ⟨by omega, fun htot_le r hr_m => ?_⟩
        cases hr_m with
        | head =>
          have heq_m : m0 * evalFinParikh N wt r0.1 = m0 * evalFinParikh N wt r0.2 := by omega
          exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < m0) heq_m
        | tail _ htl_m => exact himp_tl (by omega) r htl_m
  exact (hpar_all_eq rs syz hlen hpos_m hweak).2 hpar_le

private theorem evalWordVec_collapse_suffix_w19 (N d : Nat) (hd : d ≥ 1)
    (mat : Fin N -> Fin d -> Fin d -> Nat) (v : Fin N -> Fin d -> Nat) :
    ∀ w : List (Fin N),
      (∀ s ∈ w, ∀ i : Fin d, i.val ≥ 1 -> v s i = 0) ->
      (∀ s ∈ w.dropLast, mat s ⟨0, hd⟩ ⟨0, hd⟩ = 1 ∧ ∀ i : Fin d, i.val ≥ 1 -> mat s i ⟨0, hd⟩ = 0) ->
      evalFinWordVec N d mat v w ⟨0, hd⟩ = evalFinParikh N (fun s => v s ⟨0, hd⟩) w ∧
      (∀ i : Fin d, i.val ≥ 1 -> evalFinWordVec N d mat v w i = 0)
  | [], _, _ => ⟨rfl, fun _ _ => rfl⟩
  | [s], hv, _ => by
    have hz : natMatVec d (mat s) (fun _ => 0) = fun _ => 0 := by
      funext i; unfold natMatVec; exact natSumFin_zero_w19 d _ (fun _ => Nat.mul_zero _)
    have h0 : evalFinWordVec N d mat v [s] ⟨0, hd⟩ = evalFinParikh N (fun x => v x ⟨0, hd⟩) [s] := by
      change v s ⟨0, hd⟩ + natMatVec d (mat s) (fun _ => 0) ⟨0, hd⟩ = v s ⟨0, hd⟩ + 0
      rw [hz]
    refine ⟨h0, fun i hi => ?_⟩
    change v s i + natMatVec d (mat s) (fun _ => 0) i = 0
    rw [hz, Nat.add_zero]
    exact hv s (List.Mem.head _) i hi
  | s :: s2 :: rest, hv, hdl => by
    have hdl_cons : (s :: s2 :: rest).dropLast = s :: (s2 :: rest).dropLast := rfl
    rw [hdl_cons] at hdl
    rcases hdl s (List.Mem.head _) with ⟨hs00, hs_col0⟩
    rcases evalWordVec_collapse_suffix_w19 N d hd mat v (s2 :: rest)
      (fun x hx => hv x (List.Mem.tail _ hx))
      (fun x hx => hdl x (List.Mem.tail _ hx)) with ⟨hsub0, hsub_tail⟩
    refine ⟨?_, ?_⟩
    · change v s ⟨0, hd⟩ + natMatVec d (mat s) (evalFinWordVec N d mat v (s2 :: rest)) ⟨0, hd⟩ =
        v s ⟨0, hd⟩ + evalFinParikh N (fun x => v x ⟨0, hd⟩) (s2 :: rest)
      unfold natMatVec
      rw [natSumFin_single_zero_w19 d hd _ (fun q hq => by rw [hsub_tail q hq, Nat.mul_zero]),
          hs00, Nat.one_mul, hsub0]
    · intro i hi
      change v s i + natMatVec d (mat s) (evalFinWordVec N d mat v (s2 :: rest)) i = 0
      unfold natMatVec
      rw [hv s (List.Mem.head _) i hi, Nat.zero_add,
          natSumFin_single_zero_w19 d hd _ (fun q hq => by rw [hsub_tail q hq, Nat.mul_zero]),
          hs_col0 i hi, Nat.zero_mul]

/--
  Theorem W19.1a (`twosided_c39_c78_expanding_b_and_t_toprow_impossibility`,
  `zero custom axioms`):
  Universal All-Dimension (`∀ d ≥ 2`) Expanding-`.B` Lower-Right + `.T`-Top-Row + Arbitrary-`.R`
  Cascade & Tail-Row Collapse (`12/12` Active `.T` Top-Left Unit Locks on `c39`, `24/24` on `c78`,
  `27/39` Strict Matrix Rules in `d = 2` via `expandingBWitnessMat2DC39 2`, `0` Tail-Row Vector
  Activity Across All `27` Active `.B/.T/.R` Symbols of `c39` and `54` of `c78`, and Universal
  Impossibility of `GenOmegaExpandingBLowerRightAndTTopRowMatTower` Across All `d ≥ 2` and `k ≥ 0`
  on `TwoSided(2 × 3)` `c39` & `TwoSided(2 × 6)` `c78`, `Branch P4.3`, witness
  `ZPOS_C39_4D_MULTICHAN_INV_AND_EXPANDING_B_ESCAPE`, `W19_H1`).
-/
theorem twosided_c39_c78_expanding_b_and_t_toprow_impossibility :
    let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
    let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
    (countActiveTSymsBool 3 c39 = 12 ∧
     countActiveTSymsBool 6 c78 = 24 ∧
     countStrictMat2DRules 42 (expandingBWitnessMat2DC39 2) c39 = 27 ∧
     (∀ r ∈ c39, ∀ i j : Fin 2,
       evalFinWordMat 42 2 (expandingBWitnessMat2DC39 2) r.1 i j ≥
         evalFinWordMat 42 2 (expandingBWitnessMat2DC39 2) r.2 i j)) ∧
    (∀ (d : Nat) (hd : d ≥ 2) (mat : Fin 42 -> Fin d -> Fin d -> Nat) (v : Fin 42 -> Fin d -> Nat),
      (∀ s : Fin 42, 12 ≤ s.val ∧ s.val < 24 ->
        mat s ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 ∧
        (∀ i : Fin d, i.val ≥ 1 -> mat s i ⟨0, by omega⟩ = 0) ∧
        (∀ j : Fin d, j.val ≥ 1 -> natTailSum1 d (fun i => mat s i j) ≥ 2)) ->
      (∀ s : Fin 42, s.val ≥ 24 -> ∀ (i j : Fin d), i.val ≥ 1 -> mat s i j = 0) ->
      (∀ r ∈ c39, ∀ i : Fin d, evalFinWordVec 42 d mat v r.1 i ≥ evalFinWordVec 42 d mat v r.2 i) ->
      ∀ s : Fin 42, s.val ≥ 6 -> symAppearsInRulesBool 42 s.val c39 = true ->
        ∀ i : Fin d, i.val ≥ 1 -> v s i = 0) ∧
    (∀ (d : Nat) (hd : d ≥ 2) (mat : Fin 84 -> Fin d -> Fin d -> Nat) (v : Fin 84 -> Fin d -> Nat),
      (∀ s : Fin 84, 24 ≤ s.val ∧ s.val < 48 ->
        mat s ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 ∧
        (∀ i : Fin d, i.val ≥ 1 -> mat s i ⟨0, by omega⟩ = 0) ∧
        (∀ j : Fin d, j.val ≥ 1 -> natTailSum1 d (fun i => mat s i j) ≥ 2)) ->
      (∀ s : Fin 84, s.val ≥ 48 -> ∀ (i j : Fin d), i.val ≥ 1 -> mat s i j = 0) ->
      (∀ r ∈ c78, ∀ i : Fin d, evalFinWordVec 84 d mat v r.1 i ≥ evalFinWordVec 84 d mat v r.2 i) ->
      ∀ s : Fin 84, s.val ≥ 12 -> symAppearsInRulesBool 84 s.val c78 = true ->
        ∀ i : Fin d, i.val ≥ 1 -> v s i = 0) ∧
    (∀ (d : Nat) (hd : d ≥ 2) (k : Nat),
      ¬ GenOmegaExpandingBLowerRightAndTTopRowMatTower 3 d hd k c39 ∧
      ¬ GenOmegaExpandingBLowerRightAndTTopRowMatTower 6 d hd k c78) := by
  dsimp only
  rcases twosided_c39_c78_dual_b_toprow_and_t_subdiag_impossibility.1 with ⟨hc39_act, hc78_act, _, _⟩
  rw [c39_eq_fastRules_w19] at hc39_act
  rw [c78_eq_fastRules_w19] at hc78_act
  rw [c39_eq_fastRules_w19, c78_eq_fastRules_w19]
  rcases exp2d_witness_c39_certs_w19 with ⟨hst27, hwk2d_b⟩
  have hwk2d : ∀ r ∈ c39FastRulesW19, ∀ i j : Fin 2,
      evalFinWordMat 42 2 (expandingBWitnessMat2DC39 2) r.1 i j ≥
        evalFinWordMat 42 2 (expandingBWitnessMat2DC39 2) r.2 i j := by
    intro r hr
    have hr_b := List.all_eq_true.mp hwk2d_b r hr
    exact of_decide_eq_true (bool_and_split_w19 hr_b).2
  have htail39 : ∀ (d : Nat) (hd : d ≥ 2) (mat : Fin 42 -> Fin d -> Fin d -> Nat) (v : Fin 42 -> Fin d -> Nat),
      (∀ s : Fin 42, 12 ≤ s.val ∧ s.val < 24 ->
        mat s ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 ∧
        (∀ i : Fin d, i.val ≥ 1 -> mat s i ⟨0, by omega⟩ = 0) ∧
        (∀ j : Fin d, j.val ≥ 1 -> natTailSum1 d (fun i => mat s i j) ≥ 2)) ->
      (∀ s : Fin 42, s.val ≥ 24 -> ∀ (i j : Fin d), i.val ≥ 1 -> mat s i j = 0) ->
      (∀ r ∈ c39FastRulesW19, ∀ i : Fin d, evalFinWordVec 42 d mat v r.1 i ≥ evalFinWordVec 42 d mat v r.2 i) ->
      ∀ s : Fin 42, s.val ≥ 6 -> symAppearsInRulesBool 42 s.val c39FastRulesW19 = true ->
        ∀ i : Fin d, i.val ≥ 1 -> v s i = 0 :=
    fun d hd mat v hb ht hv =>
      active_btr_tail_zero_of_dom_w19 3 d hd c39FastRulesW19 tailWeightsC39W19 tail_collapse_dom_c39_w19 mat v hb ht hv
  have htail78 : ∀ (d : Nat) (hd : d ≥ 2) (mat : Fin 84 -> Fin d -> Fin d -> Nat) (v : Fin 84 -> Fin d -> Nat),
      (∀ s : Fin 84, 24 ≤ s.val ∧ s.val < 48 ->
        mat s ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 ∧
        (∀ i : Fin d, i.val ≥ 1 -> mat s i ⟨0, by omega⟩ = 0) ∧
        (∀ j : Fin d, j.val ≥ 1 -> natTailSum1 d (fun i => mat s i j) ≥ 2)) ->
      (∀ s : Fin 84, s.val ≥ 48 -> ∀ (i j : Fin d), i.val ≥ 1 -> mat s i j = 0) ->
      (∀ r ∈ c78FastRulesW19, ∀ i : Fin d, evalFinWordVec 84 d mat v r.1 i ≥ evalFinWordVec 84 d mat v r.2 i) ->
      ∀ s : Fin 84, s.val ≥ 12 -> symAppearsInRulesBool 84 s.val c78FastRulesW19 = true ->
        ∀ i : Fin d, i.val ≥ 1 -> v s i = 0 :=
    fun d hd mat v hb ht hv =>
      active_btr_tail_zero_of_dom_w19 6 d hd c78FastRulesW19 tailWeightsC78W19 tail_collapse_dom_c78_w19 mat v hb ht hv
  -- Helper proving no strict coordinate drop in ANY `i : Fin d` on `M ∈ {3, 6}`:
  have hno_tower : ∀ (M : Nat) (rs : List (List (Fin (14 * M)) × List (Fin (14 * M))))
      (ws : List Nat) (steps : List (Nat × Nat × Nat × Nat)) (lPairs : List (Nat × Nat))
      (syz : List Nat),
      rs ≠ [] ->
      checkTailCollapseDomBoolW19 M rs ws (14 * M) = true ->
      checkExpandingFullCollapseCertW19 M rs steps lPairs = true ->
      checkPositiveParikhSyzygyFastBool (14 * M) rs syz = true ->
      (∀ (d : Nat) (hd : d ≥ 2) (mat : Fin (14 * M) -> Fin d -> Fin d -> Nat) (v : Fin (14 * M) -> Fin d -> Nat),
        (∀ s : Fin (14 * M), s.val < 2 * M -> ∀ (i j : Fin d), i.val ≥ 1 -> mat s i j = 0) ->
        (∀ r ∈ rs, ∀ i : Fin d, evalFinWordVec (14 * M) d mat v r.1 i ≥ evalFinWordVec (14 * M) d mat v r.2 i) ->
        ∀ (a b : Fin (14 * M)), (a.val, b.val) ∈ lPairs -> ∀ i : Fin d, i.val ≥ 1 -> v a i = v b i) ->
      ∀ (d : Nat) (hd : d ≥ 2) (k : Nat),
        ¬ GenOmegaExpandingBLowerRightAndTTopRowMatTower M d hd k rs := by
    intro M rs ws steps lPairs syz hrs_ne hdom hfull hsyz hl_eq d hd k
    induction k with
    | zero => exact hrs_ne
    | succ k' ih =>
      rintro (hempty | ⟨rem, mat, v, hpos, hl, hb, ht, hboth, hkeep, hrem_tow⟩)
      · exact hrs_ne hempty
      · apply ih
        have hmat_wk : ∀ r ∈ rs, ∀ i j : Fin d,
            evalFinWordMat (14 * M) d mat r.1 i j ≥ evalFinWordMat (14 * M) d mat r.2 i j :=
          fun r hr => (hboth r hr).1
        have hvec_wk : ∀ r ∈ rs, ∀ i : Fin d,
            evalFinWordVec (14 * M) d mat v r.1 i ≥ evalFinWordVec (14 * M) d mat v r.2 i :=
          fun r hr => (hboth r hr).2
        have hbtr_zero := active_btr_tail_zero_of_dom_w19 M d hd rs ws hdom mat v hb ht hvec_wk
        have hcol0_nonR : ∀ s : Fin (14 * M), ¬ (2 * M ≤ s.val ∧ s.val < 4 * M) ->
            ∀ q : Fin d, q.val ≥ 1 -> mat s q ⟨0, by omega⟩ = 0 := by
          intro s hnr q hq
          by_cases hlt2 : s.val < 2 * M
          · exact (hl s hlt2).2 q ⟨0, by omega⟩ (Or.inl hq)
          · by_cases hlt8 : s.val < 8 * M
            · exact (hb s ⟨by omega, hlt8⟩).2.1 q hq
            · exact ht s (by omega) q ⟨0, by omega⟩ hq
        unfold checkExpandingFullCollapseCertW19 at hfull
        cases hrun : runUnit00CascadeW19 M rs [] steps with
        | none => rw [hrun] at hfull; cases hfull
        | some out =>
          rw [hrun] at hfull; dsimp only at hfull
          rcases bool_and_split_w19 hfull with ⟨hf1, hr_act⟩
          rcases bool_and_split_w19 hf1 with ⟨_, hr_shape⟩
          have hout_1 : ∀ s : Fin (14 * M), inUnit00SetBoolW19 M out s.val = true ->
              mat s ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 := by
            apply runUnit00CascadeW19_sound M d (by omega) rs mat hpos
              (fun s hs => (hl s hs).1) (fun s hs => (hb s hs).1) hcol0_nonR hmat_wk steps [] out _ hrun
            intro s hs0
            unfold inUnit00SetBoolW19 at hs0
            simp only [List.any_nil, Bool.or_false] at hs0
            rcases Bool.or_eq_true_iff.mp hs0 with h1 | h2
            · exact (hl s (Nat.ble_eq.mp h1)).1
            · rcases bool_and_split_w19 h2 with ⟨hb_lo, hb_hi⟩
              exact (hb s ⟨Nat.ble_eq.mp hb_lo, Nat.ble_eq.mp hb_hi⟩).1
          -- Show `evalFinWordVec ... w 0 = evalFinParikh` on every rule `r ∈ rs`:
          have hrow0_scalar : ∀ r ∈ rs,
              evalFinWordVec (14 * M) d mat v r.1 ⟨0, by omega⟩ =
                evalFinParikh (14 * M) (fun s => v s ⟨0, by omega⟩) r.1 ∧
              evalFinWordVec (14 * M) d mat v r.2 ⟨0, by omega⟩ =
                evalFinParikh (14 * M) (fun s => v s ⟨0, by omega⟩) r.2 ∧
              (∀ i : Fin d, i.val ≥ 1 ->
                evalFinWordVec (14 * M) d mat v r.1 i = evalFinWordVec (14 * M) d mat v r.2 i) := by
            intro r hr
            have hsh := List.all_eq_true.mp hr_shape r hr
            have hact_r := List.all_eq_true.mp hr_act r hr
            rcases bool_and_split_w19 hact_r with ⟨ha12, hr2_app⟩
            rcases bool_and_split_w19 ha12 with ⟨_, hr1_app⟩
            cases hlw : r.1 with
            | nil => try rw [hlw] at hsh; cases hsh
            | cons l0 ltl =>
              cases hrw : r.2 with
              | nil => try rw [hlw] at hsh; try rw [hrw] at hsh; cases hsh
              | cons r0 rtl =>
                try rw [hlw] at hsh
                try rw [hrw] at hsh
                try rw [hlw] at hr1_app
                try rw [hrw] at hr2_app
                dsimp only at hsh
                rcases bool_and_split_w19 hsh with ⟨hs_a, hl_or⟩
                rcases bool_and_split_w19 hs_a with ⟨hs_b, hdl_r⟩
                rcases bool_and_split_w19 hs_b with ⟨hs_c, hdl_l⟩
                rcases bool_and_split_w19 hs_c with ⟨hltl_2m, hrtl_2m⟩
                have hltl_z : ∀ x ∈ ltl, ∀ i : Fin d, i.val ≥ 1 -> v x i = 0 := by
                  intro x hx i hi
                  exact hbtr_zero x (of_decide_eq_true (List.all_eq_true.mp hltl_2m x hx))
                    (List.all_eq_true.mp hr1_app x (List.Mem.tail _ hx)) i hi
                have hrtl_z : ∀ x ∈ rtl, ∀ i : Fin d, i.val ≥ 1 -> v x i = 0 := by
                  intro x hx i hi
                  exact hbtr_zero x (of_decide_eq_true (List.all_eq_true.mp hrtl_2m x hx))
                    (List.all_eq_true.mp hr2_app x (List.Mem.tail _ hx)) i hi
                have hdl_l_prop : ∀ x ∈ (l0 :: ltl).dropLast,
                    mat x ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 ∧ ∀ i : Fin d, i.val ≥ 1 -> mat x i ⟨0, by omega⟩ = 0 := by
                  intro x hx
                  rcases bool_and_split_w19 (List.all_eq_true.mp hdl_l x hx) with ⟨hnr_b, hin_out⟩
                  have hnr : ¬ (2 * M ≤ x.val ∧ x.val < 4 * M) := by
                    intro h24; simp [h24] at hnr_b
                  exact ⟨hout_1 x hin_out, hcol0_nonR x hnr⟩
                have hdl_r_prop : ∀ x ∈ (r0 :: rtl).dropLast,
                    mat x ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 ∧ ∀ i : Fin d, i.val ≥ 1 -> mat x i ⟨0, by omega⟩ = 0 := by
                  intro x hx
                  rcases bool_and_split_w19 (List.all_eq_true.mp hdl_r x hx) with ⟨hnr_b, hin_out⟩
                  have hnr : ¬ (2 * M ≤ x.val ∧ x.val < 4 * M) := by
                    intro h24; simp [h24] at hnr_b
                  exact ⟨hout_1 x hin_out, hcol0_nonR x hnr⟩
                -- Split `l0 :: ltl` and `r0 :: rtl` at the head:
                have hsub_l := evalWordVec_collapse_suffix_w19 (14 * M) d (by omega) mat v ltl hltl_z
                  (fun x hx => hdl_l_prop x (by
                    cases ltl with
                    | nil => cases hx
                    | cons y ytl => exact List.Mem.tail l0 hx))
                have hsub_r := evalWordVec_collapse_suffix_w19 (14 * M) d (by omega) mat v rtl hrtl_z
                  (fun x hx => hdl_r_prop x (by
                    cases rtl with
                    | nil => cases hx
                    | cons y ytl => exact List.Mem.tail r0 hx))
                have hl0_row0 : evalFinWordVec (14 * M) d mat v (l0 :: ltl) ⟨0, by omega⟩ =
                    evalFinParikh (14 * M) (fun s => v s ⟨0, by omega⟩) (l0 :: ltl) := by
                  cases ltl with
                  | nil =>
                    change v l0 ⟨0, by omega⟩ + natMatVec d (mat l0) (fun _ => 0) ⟨0, by omega⟩ =
                      v l0 ⟨0, by omega⟩ + 0
                    have hz : natMatVec d (mat l0) (fun _ => 0) ⟨0, by omega⟩ = 0 :=
                      natSumFin_zero_w19 d _ (fun _ => Nat.mul_zero _)
                    rw [hz]
                  | cons y ytl =>
                    have hl0_1 := (hdl_l_prop l0 (List.Mem.head _)).1
                    change v l0 ⟨0, by omega⟩ + natMatVec d (mat l0) (evalFinWordVec (14 * M) d mat v (y :: ytl)) ⟨0, by omega⟩ =
                      v l0 ⟨0, by omega⟩ + evalFinParikh (14 * M) (fun s => v s ⟨0, by omega⟩) (y :: ytl)
                    unfold natMatVec
                    rw [natSumFin_single_zero_w19 d (by omega) _ (fun q hq => by rw [hsub_l.2 q hq, Nat.mul_zero]),
                        hl0_1, Nat.one_mul, hsub_l.1]
                have hr0_row0 : evalFinWordVec (14 * M) d mat v (r0 :: rtl) ⟨0, by omega⟩ =
                    evalFinParikh (14 * M) (fun s => v s ⟨0, by omega⟩) (r0 :: rtl) := by
                  cases rtl with
                  | nil =>
                    change v r0 ⟨0, by omega⟩ + natMatVec d (mat r0) (fun _ => 0) ⟨0, by omega⟩ =
                      v r0 ⟨0, by omega⟩ + 0
                    have hz : natMatVec d (mat r0) (fun _ => 0) ⟨0, by omega⟩ = 0 :=
                      natSumFin_zero_w19 d _ (fun _ => Nat.mul_zero _)
                    rw [hz]
                  | cons y ytl =>
                    have hr0_1 := (hdl_r_prop r0 (List.Mem.head _)).1
                    change v r0 ⟨0, by omega⟩ + natMatVec d (mat r0) (evalFinWordVec (14 * M) d mat v (y :: ytl)) ⟨0, by omega⟩ =
                      v r0 ⟨0, by omega⟩ + evalFinParikh (14 * M) (fun s => v s ⟨0, by omega⟩) (y :: ytl)
                    unfold natMatVec
                    rw [natSumFin_single_zero_w19 d (by omega) _ (fun q hq => by rw [hsub_r.2 q hq, Nat.mul_zero]),
                        hr0_1, Nat.one_mul, hsub_r.1]
                refine ⟨hl0_row0, hr0_row0, fun i hi => ?_⟩
                -- Tail rows `i ≥ 1`:
                have hl_tail_i : evalFinWordVec (14 * M) d mat v (l0 :: ltl) i = v l0 i := by
                  cases ltl with
                  | nil =>
                    change v l0 i + natMatVec d (mat l0) (fun _ => 0) i = v l0 i
                    have hz : natMatVec d (mat l0) (fun _ => 0) i = 0 :=
                      natSumFin_zero_w19 d _ (fun _ => Nat.mul_zero _)
                    rw [hz, Nat.add_zero]
                  | cons y ytl =>
                    have hc0 := (hdl_l_prop l0 (List.Mem.head _)).2 i hi
                    change v l0 i + natMatVec d (mat l0) (evalFinWordVec (14 * M) d mat v (y :: ytl)) i = v l0 i
                    unfold natMatVec
                    rw [natSumFin_single_zero_w19 d (by omega) _ (fun q hq => by rw [hsub_l.2 q hq, Nat.mul_zero]),
                        hc0, Nat.zero_mul, Nat.add_zero]
                have hr_tail_i : evalFinWordVec (14 * M) d mat v (r0 :: rtl) i = v r0 i := by
                  cases rtl with
                  | nil =>
                    change v r0 i + natMatVec d (mat r0) (fun _ => 0) i = v r0 i
                    have hz : natMatVec d (mat r0) (fun _ => 0) i = 0 :=
                      natSumFin_zero_w19 d _ (fun _ => Nat.mul_zero _)
                    rw [hz, Nat.add_zero]
                  | cons y ytl =>
                    have hc0 := (hdl_r_prop r0 (List.Mem.head _)).2 i hi
                    change v r0 i + natMatVec d (mat r0) (evalFinWordVec (14 * M) d mat v (y :: ytl)) i = v r0 i
                    unfold natMatVec
                    rw [natSumFin_single_zero_w19 d (by omega) _ (fun q hq => by rw [hsub_r.2 q hq, Nat.mul_zero]),
                        hc0, Nat.zero_mul, Nat.add_zero]
                rw [hl_tail_i, hr_tail_i]
                rcases Bool.or_eq_true_iff.mp hl_or with hl_pair | hge_both
                · rcases bool_and_split_w19 hl_pair with ⟨_, hp_in_b⟩
                  exact hl_eq d hd mat v (fun s hs i' j' hi' => (hl s hs).2 i' j' (Or.inl hi'))
                    hvec_wk l0 r0 (of_decide_eq_true hp_in_b) i hi
                · rcases bool_and_split_w19 hge_both with ⟨hl0_ge_b, hr0_ge_b⟩
                  have hl0_z := hbtr_zero l0 (of_decide_eq_true hl0_ge_b)
                    (List.all_eq_true.mp hr1_app l0 (List.Mem.head _)) i hi
                  have hr0_z := hbtr_zero r0 (of_decide_eq_true hr0_ge_b)
                    (List.all_eq_true.mp hr2_app r0 (List.Mem.head _)) i hi
                  rw [hl0_z, hr0_z]
          -- Now Parikh balance on row 0 forces `eval r.1 0 = eval r.2 0` across all `r ∈ rs`:
          have hscalar_wk : ∀ r ∈ rs,
              evalFinParikh (14 * M) (fun s => v s ⟨0, by omega⟩) r.1 ≥
                evalFinParikh (14 * M) (fun s => v s ⟨0, by omega⟩) r.2 := by
            intro r hr
            have h0 := hvec_wk r hr ⟨0, by omega⟩
            rcases hrow0_scalar r hr with ⟨he1, he2, _⟩
            omega
          have hscalar_eq := parikh_zero_strict_of_fast_syz_w19 (14 * M) rs syz hsyz
            (fun s => v s ⟨0, by omega⟩) hscalar_wk
          have hall_in_rem : ∀ r ∈ rs, r ∈ rem := by
            intro r hr
            apply hkeep r hr
            rintro ⟨i, hgt⟩
            rcases hrow0_scalar r hr with ⟨he1, he2, htail_eq⟩
            by_cases hi0 : i.val = 0
            · have hi_eq : i = ⟨0, by omega⟩ := Fin.ext hi0
              rw [hi_eq, he1, he2, hscalar_eq r hr] at hgt
              omega
            · rw [htail_eq i (by omega)] at hgt
              omega
          -- Subset monotonicity of `GenOmegaExpandingBLowerRightAndTTopRowMatTower`:
          have hmono : ∀ (k0 : Nat) (sub sup : List (List (Fin (14 * M)) × List (Fin (14 * M)))),
              (∀ r ∈ sub, r ∈ sup) ->
              GenOmegaExpandingBLowerRightAndTTopRowMatTower M d hd k0 sup ->
              GenOmegaExpandingBLowerRightAndTTopRowMatTower M d hd k0 sub := by
            intro k0; induction k0 with
            | zero =>
              intro sub sup hsub hsup
              rw [GenOmegaExpandingBLowerRightAndTTopRowMatTower] at hsup ⊢
              cases sub with
              | nil => rfl
              | cons r0 _ =>
                have := hsub r0 (List.Mem.head _)
                rw [hsup] at this; cases this
            | succ k1 _ =>
              intro sub sup hsub hsup
              rcases hsup with hempty | ⟨rem1, m1, v1, hp1, hl1, hb1, ht1, hboth1, hkeep1, hrem1⟩
              · left
                cases sub with
                | nil => rfl
                | cons r0 _ =>
                  have := hsub r0 (List.Mem.head _)
                  rw [hempty] at this; cases this
              · right
                exact ⟨rem1, m1, v1, hp1, hl1, hb1, ht1,
                       fun r hr => hboth1 r (hsub r hr),
                       fun r hr hns => hkeep1 r (hsub r hr) hns,
                       hrem1⟩
          exact hmono k' rs rem hall_in_rem hrem_tow
  -- Helper proving `.L` head equality on `lEqPairsC39W19` and `lEqPairsC78W19`:
  have hl_rule_ge : ∀ (N d : Nat) (hd : d ≥ 2) (M0 : Nat)
      (rs : List (List (Fin N) × List (Fin N)))
      (mat : Fin N -> Fin d -> Fin d -> Nat) (v : Fin N -> Fin d -> Nat)
      (hlz : ∀ s : Fin N, s.val < M0 -> ∀ (i j : Fin d), i.val ≥ 1 -> mat s i j = 0)
      (hvec : ∀ r ∈ rs, ∀ i : Fin d, evalFinWordVec N d mat v r.1 i ≥ evalFinWordVec N d mat v r.2 i)
      (s1 s2 u1 : Nat) (rest_r : List (Fin N)) (fa fb fc : Fin N),
      fa.val = s1 -> fb.val = s2 -> fc.val = u1 ->
      s1 < M0 -> u1 < M0 -> ([fa, fb], fc :: rest_r) ∈ rs ->
      ∀ i : Fin d, i.val ≥ 1 -> v fa i ≥ v fc i := by
    intro N d hd M0 rs mat v hlz hvec s1 s2 u1 rest_r fa fb fc hfa hfb hfc hs1 hu1 hmem i hi
    have hv_i := hvec ([fa, fb], fc :: rest_r) hmem i
    have hl_ev : evalFinWordVec N d mat v [fa, fb] i = v fa i := by
      change v fa i + natMatVec d (mat fa) (evalFinWordVec N d mat v [fb]) i = v fa i
      rw [show natMatVec d (mat fa) (evalFinWordVec N d mat v [fb]) i = 0 from
        natSumFin_zero_w19 d _ (fun j => by rw [hlz fa (hfa ▸ hs1) i j hi, Nat.zero_mul]), Nat.add_zero]
    have hr_ev : evalFinWordVec N d mat v (fc :: rest_r) i = v fc i := by
      change v fc i + natMatVec d (mat fc) (evalFinWordVec N d mat v rest_r) i = v fc i
      rw [show natMatVec d (mat fc) (evalFinWordVec N d mat v rest_r) i = 0 from
        natSumFin_zero_w19 d _ (fun j => by rw [hlz fc (hfc ▸ hu1) i j hi, Nat.zero_mul]), Nat.add_zero]
    rw [hl_ev, hr_ev] at hv_i; exact hv_i
  rcases parikh_syz_c39_c78_w19 with ⟨hsyz39, hsyz78⟩
  refine ⟨⟨hc39_act, hc78_act, hst27, hwk2d⟩, htail39, htail78, fun d hd k => ⟨?_, ?_⟩⟩
  · apply hno_tower 3 c39FastRulesW19 tailWeightsC39W19 expCascadeC39W19 lEqPairsC39W19
      syzTwoSidedMod3OmitR3Core39 (by decide) tail_collapse_dom_c39_w19 exp_full_cert_c39_w19
      hsyz39 _ d hd k
    intro d0 hd0 mat v hlz hvec a b hmem_p i hi
    have h12 := hl_rule_ge 42 d0 hd0 6 c39FastRulesW19 mat v hlz hvec 1 14 2 []
      ⟨1, by decide⟩ ⟨14, by decide⟩ ⟨2, by decide⟩ rfl rfl rfl (by decide) (by decide) (by decide) i hi
    have h21 := hl_rule_ge 42 d0 hd0 6 c39FastRulesW19 mat v hlz hvec 2 13 1 []
      ⟨2, by decide⟩ ⟨13, by decide⟩ ⟨1, by decide⟩ rfl rfl rfl (by decide) (by decide) (by decide) i hi
    have h45 := hl_rule_ge 42 d0 hd0 6 c39FastRulesW19 mat v hlz hvec 4 14 5 []
      ⟨4, by decide⟩ ⟨14, by decide⟩ ⟨5, by decide⟩ rfl rfl rfl (by decide) (by decide) (by decide) i hi
    have h54 := hl_rule_ge 42 d0 hd0 6 c39FastRulesW19 mat v hlz hvec 5 13 4 []
      ⟨5, by decide⟩ ⟨13, by decide⟩ ⟨4, by decide⟩ rfl rfl rfl (by decide) (by decide) (by decide) i hi
    have he12 : v ⟨1, by decide⟩ i = v ⟨2, by decide⟩ i := by omega
    have he45 : v ⟨4, by decide⟩ i = v ⟨5, by decide⟩ i := by omega
    have hcls : ((a.val == 1 || a.val == 2) && (b.val == 1 || b.val == 2)) ||
                ((a.val == 4 || a.val == 5) && (b.val == 4 || b.val == 5)) = true := by
      have hall : lEqPairsC39W19.all (fun p =>
          ((p.1 == 1 || p.1 == 2) && (p.2 == 1 || p.2 == 2)) ||
          ((p.1 == 4 || p.1 == 5) && (p.2 == 4 || p.2 == 5))) = true := by decide
      exact List.all_eq_true.mp hall (a.val, b.val) hmem_p
    rcases Bool.or_eq_true_iff.mp hcls with hc12 | hc45
    · rcases bool_and_split_w19 hc12 with ⟨ha12, hb12⟩
      have ha_eq : v a i = v ⟨1, by decide⟩ i := by
        rcases Bool.or_eq_true_iff.mp ha12 with h1 | h2
        · rw [show a = ⟨1, by decide⟩ from Fin.ext (beq_iff_eq.mp h1)]
        · rw [show a = ⟨2, by decide⟩ from Fin.ext (beq_iff_eq.mp h2), he12]
      have hb_eq : v b i = v ⟨1, by decide⟩ i := by
        rcases Bool.or_eq_true_iff.mp hb12 with h1 | h2
        · rw [show b = ⟨1, by decide⟩ from Fin.ext (beq_iff_eq.mp h1)]
        · rw [show b = ⟨2, by decide⟩ from Fin.ext (beq_iff_eq.mp h2), he12]
      exact ha_eq.trans hb_eq.symm
    · rcases bool_and_split_w19 hc45 with ⟨ha45, hb45⟩
      have ha_eq : v a i = v ⟨4, by decide⟩ i := by
        rcases Bool.or_eq_true_iff.mp ha45 with h4 | h5
        · rw [show a = ⟨4, by decide⟩ from Fin.ext (beq_iff_eq.mp h4)]
        · rw [show a = ⟨5, by decide⟩ from Fin.ext (beq_iff_eq.mp h5), he45]
      have hb_eq : v b i = v ⟨4, by decide⟩ i := by
        rcases Bool.or_eq_true_iff.mp hb45 with h4 | h5
        · rw [show b = ⟨4, by decide⟩ from Fin.ext (beq_iff_eq.mp h4)]
        · rw [show b = ⟨5, by decide⟩ from Fin.ext (beq_iff_eq.mp h5), he45]
      exact ha_eq.trans hb_eq.symm
  · apply hno_tower 6 c78FastRulesW19 tailWeightsC78W19 expCascadeC78W19 lEqPairsC78W19
      syzTwoSidedMod6OmitR3Core78 (by decide) tail_collapse_dom_c78_w19 exp_full_cert_c78_only_w19
      hsyz78 _ d hd k
    intro d0 hd0 mat v hlz hvec a b hmem_p i hi
    have h45 := hl_rule_ge 84 d0 hd0 12 c78FastRulesW19 mat v hlz hvec 4 29 5 []
      ⟨4, by decide⟩ ⟨29, by decide⟩ ⟨5, by decide⟩ rfl rfl rfl (by decide) (by decide) (by decide) i hi
    have h24 := hl_rule_ge 84 d0 hd0 12 c78FastRulesW19 mat v hlz hvec 2 28 4 []
      ⟨2, by decide⟩ ⟨28, by decide⟩ ⟨4, by decide⟩ rfl rfl rfl (by decide) (by decide) (by decide) i hi
    have h21 := hl_rule_ge 84 d0 hd0 12 c78FastRulesW19 mat v hlz hvec 2 25 1 []
      ⟨2, by decide⟩ ⟨25, by decide⟩ ⟨1, by decide⟩ rfl rfl rfl (by decide) (by decide) (by decide) i hi
    have h52 := hl_rule_ge 84 d0 hd0 12 c78FastRulesW19 mat v hlz hvec 5 38 2 [⟨74, by decide⟩]
      ⟨5, by decide⟩ ⟨38, by decide⟩ ⟨2, by decide⟩ rfl rfl rfl (by decide) (by decide) (by decide) i hi
    have h12 := hl_rule_ge 84 d0 hd0 12 c78FastRulesW19 mat v hlz hvec 1 36 2 [⟨72, by decide⟩]
      ⟨1, by decide⟩ ⟨36, by decide⟩ ⟨2, by decide⟩ rfl rfl rfl (by decide) (by decide) (by decide) i hi
    have h10_11 := hl_rule_ge 84 d0 hd0 12 c78FastRulesW19 mat v hlz hvec 10 29 11 []
      ⟨10, by decide⟩ ⟨29, by decide⟩ ⟨11, by decide⟩ rfl rfl rfl (by decide) (by decide) (by decide) i hi
    have h8_10 := hl_rule_ge 84 d0 hd0 12 c78FastRulesW19 mat v hlz hvec 8 28 10 []
      ⟨8, by decide⟩ ⟨28, by decide⟩ ⟨10, by decide⟩ rfl rfl rfl (by decide) (by decide) (by decide) i hi
    have h8_7 := hl_rule_ge 84 d0 hd0 12 c78FastRulesW19 mat v hlz hvec 8 25 7 []
      ⟨8, by decide⟩ ⟨25, by decide⟩ ⟨7, by decide⟩ rfl rfl rfl (by decide) (by decide) (by decide) i hi
    have h11_8 := hl_rule_ge 84 d0 hd0 12 c78FastRulesW19 mat v hlz hvec 11 38 8 [⟨74, by decide⟩]
      ⟨11, by decide⟩ ⟨38, by decide⟩ ⟨8, by decide⟩ rfl rfl rfl (by decide) (by decide) (by decide) i hi
    have h7_8 := hl_rule_ge 84 d0 hd0 12 c78FastRulesW19 mat v hlz hvec 7 36 8 [⟨72, by decide⟩]
      ⟨7, by decide⟩ ⟨36, by decide⟩ ⟨8, by decide⟩ rfl rfl rfl (by decide) (by decide) (by decide) i hi
    have he2 : v ⟨2, by decide⟩ i = v ⟨1, by decide⟩ i := by omega
    have he4 : v ⟨4, by decide⟩ i = v ⟨1, by decide⟩ i := by omega
    have he5 : v ⟨5, by decide⟩ i = v ⟨1, by decide⟩ i := by omega
    have he8 : v ⟨8, by decide⟩ i = v ⟨7, by decide⟩ i := by omega
    have he10 : v ⟨10, by decide⟩ i = v ⟨7, by decide⟩ i := by omega
    have he11 : v ⟨11, by decide⟩ i = v ⟨7, by decide⟩ i := by omega
    have hcls :
        ((a.val == 1 || a.val == 2 || a.val == 4 || a.val == 5) &&
         (b.val == 1 || b.val == 2 || b.val == 4 || b.val == 5)) ||
        ((a.val == 7 || a.val == 8 || a.val == 10 || a.val == 11) &&
         (b.val == 7 || b.val == 8 || b.val == 10 || b.val == 11)) = true := by
      have hall : lEqPairsC78W19.all (fun p =>
          ((p.1 == 1 || p.1 == 2 || p.1 == 4 || p.1 == 5) &&
           (p.2 == 1 || p.2 == 2 || p.2 == 4 || p.2 == 5)) ||
          ((p.1 == 7 || p.1 == 8 || p.1 == 10 || p.1 == 11) &&
           (p.2 == 7 || p.2 == 8 || p.2 == 10 || p.2 == 11))) = true := by decide
      exact List.all_eq_true.mp hall (a.val, b.val) hmem_p
    have hgrp1 : ∀ x : Fin 84, (x.val == 1 || x.val == 2 || x.val == 4 || x.val == 5) = true ->
        v x i = v ⟨1, by decide⟩ i := by
      intro x hx
      rcases Bool.or_eq_true_iff.mp hx with h124 | h5
      · rcases Bool.or_eq_true_iff.mp h124 with h12_x | h4
        · rcases Bool.or_eq_true_iff.mp h12_x with h1 | h2
          · rw [show x = ⟨1, by decide⟩ from Fin.ext (beq_iff_eq.mp h1)]
          · rw [show x = ⟨2, by decide⟩ from Fin.ext (beq_iff_eq.mp h2), he2]
        · rw [show x = ⟨4, by decide⟩ from Fin.ext (beq_iff_eq.mp h4), he4]
      · rw [show x = ⟨5, by decide⟩ from Fin.ext (beq_iff_eq.mp h5), he5]
    have hgrp7 : ∀ x : Fin 84, (x.val == 7 || x.val == 8 || x.val == 10 || x.val == 11) = true ->
        v x i = v ⟨7, by decide⟩ i := by
      intro x hx
      rcases Bool.or_eq_true_iff.mp hx with h7810 | h11
      · rcases Bool.or_eq_true_iff.mp h7810 with h78_x | h10
        · rcases Bool.or_eq_true_iff.mp h78_x with h7 | h8
          · rw [show x = ⟨7, by decide⟩ from Fin.ext (beq_iff_eq.mp h7)]
          · rw [show x = ⟨8, by decide⟩ from Fin.ext (beq_iff_eq.mp h8), he8]
        · rw [show x = ⟨10, by decide⟩ from Fin.ext (beq_iff_eq.mp h10), he10]
      · rw [show x = ⟨11, by decide⟩ from Fin.ext (beq_iff_eq.mp h11), he11]
    rcases Bool.or_eq_true_iff.mp hcls with hc1 | hc7
    · rcases bool_and_split_w19 hc1 with ⟨ha1, hb1⟩
      exact (hgrp1 a ha1).trans (hgrp1 b hb1).symm
    · rcases bool_and_split_w19 hc7 with ⟨ha7, hb7⟩
      exact (hgrp7 a ha7).trans (hgrp7 b hb7).symm

-- ============================================================================
-- Section 1B: Infinite 6-Parameter `d = 3` (`3 × 3`) Invertible Positive-Trace
--             Lower-Right Cones, 7-Parameter `d = 4` (`4 × 4`) 4-Channel Cones,
--             & All-Dimension (`∀ d ≥ 4`) Multi-Channel Invertible Cones + Farkas Locks
-- ============================================================================

private def isT1InvSymW19 (v : Nat) : Bool :=
  v == 33 || v == 35 || v == 39 || v == 40 || v == 41

private def isT2InvSymW19 (v : Nat) : Bool :=
  v == 28 || v == 29 || v == 31 || v == 32 || v == 36 || v == 37 || v == 38

/-- Infinite 6-parameter `d = 3` (`3 × 3`) non-nilpotent invertible positive-trace lower-right
    `.B` + `.T` + `.R` mixed zero-diagonal cone on `Fin 42` (`c39`, strictly orienting **`39/39` (`100%`)**
    of `c39` at `(2, 1, 1, 1, 1, 1)`!):
    - On `s ∈ {29, 31}`, lower-right `2 × 2` block is `[[1, 0], [η, η]]` (`det = η ≥ 1`, `tr = η + 1 ≥ 2`),
    - On `s = 35`, lower-right `2 × 2` block is `[[η, η], [0, 1]]` (`det = η ≥ 1`, `tr = η + 1 ≥ 2`),
    - On all `12/12` active `.T` symbols, `D_s^2 ≠ 0` (`tr(D_s) ≥ η ≥ 1`). -/
def invPosTraceMat3DC39 (k alpha beta gamma delta eta : Nat) (s : Fin 42) (i j : Fin 3) : Nat :=
  let sv := s.val
  if i.val == 0 && j.val == 0 then
    if 6 ≤ sv && sv ≤ 11 then k else 1
  else if i.val == 0 && j.val == 1 then
    if sv == 13 || sv == 14 || sv == 16 || sv == 17 || sv == 18 || sv == 21 then 2 * beta
    else if sv == 28 || sv == 32 || sv == 36 then beta
    else 0
  else if i.val == 0 && j.val == 2 then
    if sv == 20 || sv == 22 || sv == 23 then 2 * alpha
    else if sv == 37 || sv == 40 || sv == 41 then alpha
    else 0
  else if i.val == 1 then
    if isT1InvSymW19 sv then (if j.val == 0 then delta else eta)
    else if (sv == 29 || sv == 31) && j.val == 1 then 1
    else 0
  else
    if isT2InvSymW19 sv then (if j.val == 0 then gamma else eta)
    else if (sv == 35 || (6 ≤ sv && sv ≤ 8)) && j.val == 2 then 1
    else 0

/-- Lifted 6-parameter `d = 3` (`3 × 3`) invertible positive-trace cone on `Fin 84` (`c78`,
    strictly orienting **`78/78` (`100%`)** of `c78`!). -/
def invPosTraceMat3DC78 (k alpha beta gamma delta eta : Nat) (s : Fin 84) (i j : Fin 3) : Nat :=
  invPosTraceMat3DC39 k alpha beta gamma delta eta (projSym84To42 s) i j

/-- Infinite 7-parameter `d = 4` (`4 × 4`) 4-channel cross-coupled invertible positive-trace
    `.B` + `.T` + `.R` cone on `Fin 42` (`c39`, strictly orienting **`39/39` (`100%`)** of `c39`,
    with invertible `3 × 3` lower-right subblocks `det(D_s) = η ≥ 1`, `tr(D_s) = η + 2 ≥ 3` on `{29, 31, 35}`!). -/
def multiChanInvMat4DC39 (k alpha beta gamma delta eta zeta : Nat) (s : Fin 42) (i j : Fin 4) : Nat :=
  let sv := s.val
  if i.val == 0 && j.val == 0 then
    if 6 ≤ sv && sv ≤ 11 then k else 1
  else if i.val == 0 && j.val == 1 then
    if sv == 13 || sv == 14 || sv == 16 || sv == 17 || sv == 18 then 2 * beta
    else if sv == 28 || sv == 32 || sv == 36 then beta
    else 0
  else if i.val == 0 && j.val == 2 then
    if sv == 20 || sv == 22 then 2 * alpha
    else if sv == 37 || sv == 40 then alpha
    else 0
  else if i.val == 0 && j.val == 3 then
    if sv == 21 || sv == 23 then 2 * zeta
    else if sv == 41 then zeta
    else 0
  else if i.val == 1 then
    if isT1InvSymW19 sv then (if j.val == 0 then delta else eta)
    else if (sv == 29 || sv == 31) && j.val == 1 then 1
    else 0
  else if i.val == 2 then
    if isT2InvSymW19 sv then (if j.val == 0 then gamma else eta)
    else if (sv == 35 || (6 ≤ sv && sv ≤ 8)) && j.val == 2 then 1
    else 0
  else
    if (sv == 29 || sv == 31 || sv == 35) && j.val == 3 then 1
    else 0

/-- Lifted 7-parameter `d = 4` (`4 × 4`) 4-channel invertible cone on `Fin 84` (`c78`,
    strictly orienting **`78/78` (`100%`)** of `c78`!). -/
def multiChanInvMat4DC78 (k alpha beta gamma delta eta zeta : Nat) (s : Fin 84) (i j : Fin 4) : Nat :=
  multiChanInvMat4DC39 k alpha beta gamma delta eta zeta (projSym84To42 s) i j

/-- All-dimension (`∀ d ≥ 4`) multi-channel cross-coupled invertible cone on `Fin 42` (`c39`),
    distributing arbitrary channel weights `zetaCh j` across all extra dimensions `j ≥ 3` while
    maintaining invertible `(d - 1) × (d - 1)` lower-right blocks (`det(D_s) = η ≥ 1`) on `{29, 31, 35}`. -/
def multiChanInvMatTowerAnyDC39 (d : Nat) (k alpha beta gamma delta eta : Nat)
    (zetaCh : Fin d -> Nat) (s : Fin 42) (i j : Fin d) : Nat :=
  let sv := s.val
  if i.val < 3 && j.val < 3 then
    multiChanInvMat4DC39 k alpha beta gamma delta eta 0 s
      ⟨i.val % 3, Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)⟩
      ⟨j.val % 3, Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)⟩
  else if i.val == 0 && j.val ≥ 3 then
    if sv == 21 || sv == 23 then 2 * zetaCh j
    else if sv == 41 then zetaCh j
    else 0
  else if i.val == 1 && j.val ≥ 3 then
    if isT1InvSymW19 sv then eta else 0
  else if i.val == 2 && j.val ≥ 3 then
    if isT2InvSymW19 sv then eta else 0
  else if i.val ≥ 3 && i.val == j.val then
    if sv == 29 || sv == 31 || sv == 35 then 1 else 0
  else 0

/-- All-dimension (`∀ d ≥ 4`) multi-channel cross-coupled invertible cone on `Fin 84` (`c78`). -/
def multiChanInvMatTowerAnyDC78 (d : Nat) (k alpha beta gamma delta eta : Nat)
    (zetaCh : Fin d -> Nat) (s : Fin 84) (i j : Fin d) : Nat :=
  multiChanInvMatTowerAnyDC39 d k alpha beta gamma delta eta zetaCh (projSym84To42 s) i j

/-- Standard `4D` unit basis vector on `Fin N`. -/
def basisVec4D (N : Nat) (s0 : Fin N) (j0 : Fin 4) (s : Fin N) (j : Fin 4) : Nat :=
  if s.val == s0.val && j.val == j0.val then 1 else 0

/-- Count rules strictly oriented (`∃ i j : Fin 4, LHS > RHS`) by a `4 × 4` matrix interpretation. -/
def countStrictMat4DRules (N : Nat) (M : Fin N -> Fin 4 -> Fin 4 -> Nat) :
    List (List (Fin N) × List (Fin N)) -> Nat
  | [] => 0
  | (l, r) :: rs =>
    let z0 : Fin 4 := ⟨0, by decide⟩
    let z1 : Fin 4 := ⟨1, by decide⟩
    let z2 : Fin 4 := ⟨2, by decide⟩
    let z3 : Fin 4 := ⟨3, by decide⟩
    let is_st := [z0, z1, z2, z3].any (fun i =>
      [z0, z1, z2, z3].any (fun j =>
        decide (evalFinWordMat N 4 M l i j > evalFinWordMat N 4 M r i j)))
    (if is_st then 1 else 0) + countStrictMat4DRules N M rs

/-- Row-1 Farkas multipliers `μ_1` for `invPosTraceMat3DC39` and `multiChanInvMat4DC39`
    (`([28,18],[22,33]): 10`, `([32,13],[18,28]): 6`, `([36,22],[20,40]): 1`). -/
def farkasMu1InvW19C39 : List (Fin 42) -> Nat
  | a :: b :: _ =>
    if a.val == 28 && b.val == 18 then 10
    else if a.val == 32 && b.val == 13 then 6
    else if a.val == 36 && b.val == 22 then 1
    else 0
  | _ => 0

/-- Row-2 Farkas multipliers `μ_2` for `multiChanInvMat4DC39` (`([33,22],[17,37]): 10`, `([35,16],[21,28]): 3`). -/
def farkasMu2InvW19C39 : List (Fin 42) -> Nat
  | a :: b :: _ =>
    if a.val == 33 && b.val == 22 then 10
    else if a.val == 35 && b.val == 16 then 3
    else 0
  | _ => 0

/-- Row-3 Farkas multipliers `μ_3` for `multiChanInvMat4DC39` (`([39,22],[23,40]): 1`). -/
def farkasMu3InvW19C39 : List (Fin 42) -> Nat
  | a :: b :: _ =>
    if a.val == 39 && b.val == 22 then 1 else 0
  | _ => 0

/-- Row-1 Farkas multipliers `μ_1` for `invPosTraceMat3DC78` and `multiChanInvMat4DC78`. -/
def farkasMu1InvW19C78 : List (Fin 84) -> Nat
  | a :: b :: _ =>
    let av := a.val; let bv := b.val
    if av == 74 && bv == 31 then 1
    else if av == 62 && bv == 28 then 1
    else if av == 62 && bv == 25 then 10
    else if av == 55 && bv == 36 then 14
    else if av == 59 && bv == 38 then 20
    else if av == 59 && bv == 41 then 1
    else if av == 75 && bv == 46 then 21
    else if av == 75 && bv == 43 then 9
    else 0
  | _ => 0

/-- Row-2 Farkas multipliers `μ_2` for `multiChanInvMat4DC78`. -/
def farkasMu2InvW19C78 : List (Fin 84) -> Nat
  | a :: b :: _ =>
    let av := a.val; let bv := b.val
    if av == 69 && bv == 46 then 8
    else if av == 69 && bv == 43 then 9
    else if av == 68 && bv == 34 then 2
    else if av == 80 && bv == 31 then 2
    else if av == 68 && bv == 31 then 30
    else if av == 80 && bv == 34 then 18
    else 0
  | _ => 0

/-- Row-3 Farkas multipliers `μ_3` for `multiChanInvMat4DC78`. -/
def farkasMu3InvW19C78 : List (Fin 84) -> Nat
  | a :: b :: _ =>
    let av := a.val; let bv := b.val
    if av == 80 && bv == 31 then 37
    else if av == 81 && bv == 46 then 44
    else if av == 81 && bv == 43 then 1
    else 0
  | _ => 0

/-- 3-channel Farkas LHS functional on `invPosTraceMat3DC39`. -/
def farkasInv3DVecLhsN (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 m1 m2 : List (Fin N) -> Nat) (k alpha beta gamma delta eta : Nat)
    (v : Fin N -> Fin 3 -> Nat) : List (List (Fin N) × List (Fin N)) -> Nat
  | [] => 0
  | (l, _) :: rs =>
    let M := fun s => invPosTraceMat3DC39 k alpha beta gamma delta eta (proj s)
    mu0 l * evalFinWordVec N 3 M v l ⟨0, by decide⟩ +
      m1 l * evalFinWordVec N 3 M v l ⟨1, by decide⟩ +
      m2 l * evalFinWordVec N 3 M v l ⟨2, by decide⟩ +
      farkasInv3DVecLhsN N proj mu0 m1 m2 k alpha beta gamma delta eta v rs

/-- 3-channel Farkas RHS functional on `invPosTraceMat3DC39`. -/
def farkasInv3DVecRhsN (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 m1 m2 : List (Fin N) -> Nat) (k alpha beta gamma delta eta : Nat)
    (v : Fin N -> Fin 3 -> Nat) : List (List (Fin N) × List (Fin N)) -> Nat
  | [] => 0
  | (l, r) :: rs =>
    let M := fun s => invPosTraceMat3DC39 k alpha beta gamma delta eta (proj s)
    mu0 l * evalFinWordVec N 3 M v r ⟨0, by decide⟩ +
      m1 l * evalFinWordVec N 3 M v r ⟨1, by decide⟩ +
      m2 l * evalFinWordVec N 3 M v r ⟨2, by decide⟩ +
      farkasInv3DVecRhsN N proj mu0 m1 m2 k alpha beta gamma delta eta v rs

/-- 4-channel Farkas LHS functional on `multiChanInvMat4DC39`. -/
def farkasInv4DVecLhsN (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 m1 m2 m3 : List (Fin N) -> Nat) (k alpha beta gamma delta eta zeta : Nat)
    (v : Fin N -> Fin 4 -> Nat) : List (List (Fin N) × List (Fin N)) -> Nat
  | [] => 0
  | (l, _) :: rs =>
    let M := fun s => multiChanInvMat4DC39 k alpha beta gamma delta eta zeta (proj s)
    mu0 l * evalFinWordVec N 4 M v l ⟨0, by decide⟩ +
      m1 l * evalFinWordVec N 4 M v l ⟨1, by decide⟩ +
      m2 l * evalFinWordVec N 4 M v l ⟨2, by decide⟩ +
      m3 l * evalFinWordVec N 4 M v l ⟨3, by decide⟩ +
      farkasInv4DVecLhsN N proj mu0 m1 m2 m3 k alpha beta gamma delta eta zeta v rs

/-- 4-channel Farkas RHS functional on `multiChanInvMat4DC39`. -/
def farkasInv4DVecRhsN (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 m1 m2 m3 : List (Fin N) -> Nat) (k alpha beta gamma delta eta zeta : Nat)
    (v : Fin N -> Fin 4 -> Nat) : List (List (Fin N) × List (Fin N)) -> Nat
  | [] => 0
  | (l, r) :: rs =>
    let M := fun s => multiChanInvMat4DC39 k alpha beta gamma delta eta zeta (proj s)
    mu0 l * evalFinWordVec N 4 M v r ⟨0, by decide⟩ +
      m1 l * evalFinWordVec N 4 M v r ⟨1, by decide⟩ +
      m2 l * evalFinWordVec N 4 M v r ⟨2, by decide⟩ +
      m3 l * evalFinWordVec N 4 M v r ⟨3, by decide⟩ +
      farkasInv4DVecRhsN N proj mu0 m1 m2 m3 k alpha beta gamma delta eta zeta v rs

-- General 7-variable sparse polynomial algebra `Poly7W19` for case-free matrix & Farkas dominance:

private abbrev Mono7W19 := Nat × Nat × Nat × Nat × Nat × Nat × Nat
private abbrev Poly7W19 := List (Mono7W19 × Nat)

private def evalMono7W19 (v0 v1 v2 v3 v4 v5 v6 : Nat) (m : Mono7W19) : Nat :=
  v0 ^ m.1 * v1 ^ m.2.1 * v2 ^ m.2.2.1 * v3 ^ m.2.2.2.1 *
    v4 ^ m.2.2.2.2.1 * v5 ^ m.2.2.2.2.2.1 * v6 ^ m.2.2.2.2.2.2

private def mulMono7W19 (a b : Mono7W19) : Mono7W19 :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1, a.2.2.2.1 + b.2.2.2.1,
   a.2.2.2.2.1 + b.2.2.2.2.1, a.2.2.2.2.2.1 + b.2.2.2.2.2.1, a.2.2.2.2.2.2 + b.2.2.2.2.2.2)

private theorem evalMono7W19_mul (v0 v1 v2 v3 v4 v5 v6 : Nat) (a b : Mono7W19) :
    evalMono7W19 v0 v1 v2 v3 v4 v5 v6 (mulMono7W19 a b) =
      evalMono7W19 v0 v1 v2 v3 v4 v5 v6 a * evalMono7W19 v0 v1 v2 v3 v4 v5 v6 b := by
  unfold evalMono7W19 mulMono7W19
  dsimp only
  simp only [Nat.pow_add]
  ac_rfl

private def evalPoly7W19 (v0 v1 v2 v3 v4 v5 v6 : Nat) : Poly7W19 -> Nat
  | [] => 0
  | (m, c) :: tl => c * evalMono7W19 v0 v1 v2 v3 v4 v5 v6 m + evalPoly7W19 v0 v1 v2 v3 v4 v5 v6 tl

private def poly7Insert (m : Mono7W19) (c : Nat) : Poly7W19 -> Poly7W19
  | [] => if c = 0 then [] else [(m, c)]
  | (m2, c2) :: tl =>
    if c = 0 then (m2, c2) :: tl
    else if m2 = m then (m2, c2 + c) :: tl
    else (m2, c2) :: poly7Insert m c tl

private theorem evalPoly7W19_insert (v0 v1 v2 v3 v4 v5 v6 : Nat) (m : Mono7W19) (c : Nat) :
    ∀ p : Poly7W19,
      evalPoly7W19 v0 v1 v2 v3 v4 v5 v6 (poly7Insert m c p) =
        c * evalMono7W19 v0 v1 v2 v3 v4 v5 v6 m + evalPoly7W19 v0 v1 v2 v3 v4 v5 v6 p
  | [] => by
    unfold poly7Insert
    by_cases hc : c = 0
    · subst hc; simp [evalPoly7W19]
    · rw [ite_false_of_w10 hc]; simp [evalPoly7W19]
  | (m2, c2) :: tl => by
    unfold poly7Insert
    by_cases hc : c = 0
    · subst hc; simp [evalPoly7W19]
    · rw [ite_false_of_w10 hc]
      by_cases hm : m2 = m
      · subst hm; rw [ite_true_of_w10 rfl]
        simp only [evalPoly7W19, Nat.add_mul]; omega
      · rw [ite_false_of_w10 hm]
        simp only [evalPoly7W19, evalPoly7W19_insert v0 v1 v2 v3 v4 v5 v6 m c tl]; omega

private def poly7Add : Poly7W19 -> Poly7W19 -> Poly7W19
  | p, [] => p
  | p, (m, c) :: tl => poly7Add (poly7Insert m c p) tl

private theorem evalPoly7W19_add (v0 v1 v2 v3 v4 v5 v6 : Nat) :
    ∀ (p q : Poly7W19),
      evalPoly7W19 v0 v1 v2 v3 v4 v5 v6 (poly7Add p q) =
        evalPoly7W19 v0 v1 v2 v3 v4 v5 v6 p + evalPoly7W19 v0 v1 v2 v3 v4 v5 v6 q
  | p, [] => by simp [poly7Add, evalPoly7W19]
  | p, (m, c) :: tl => by
    simp only [poly7Add, evalPoly7W19_add v0 v1 v2 v3 v4 v5 v6 (poly7Insert m c p) tl,
               evalPoly7W19_insert, evalPoly7W19]
    omega

private def poly7ScaleMono (m1 : Mono7W19) (c1 : Nat) : Poly7W19 -> Poly7W19 -> Poly7W19
  | acc, [] => acc
  | acc, (m2, c2) :: tl => poly7ScaleMono m1 c1 (poly7Insert (mulMono7W19 m1 m2) (c1 * c2) acc) tl

private theorem evalPoly7W19_scaleMono (v0 v1 v2 v3 v4 v5 v6 : Nat) (m1 : Mono7W19) (c1 : Nat) :
    ∀ (acc q : Poly7W19),
      evalPoly7W19 v0 v1 v2 v3 v4 v5 v6 (poly7ScaleMono m1 c1 acc q) =
        evalPoly7W19 v0 v1 v2 v3 v4 v5 v6 acc +
          (c1 * evalMono7W19 v0 v1 v2 v3 v4 v5 v6 m1) * evalPoly7W19 v0 v1 v2 v3 v4 v5 v6 q
  | acc, [] => by simp [poly7ScaleMono, evalPoly7W19]
  | acc, (m2, c2) :: tl => by
    simp only [poly7ScaleMono, evalPoly7W19_scaleMono v0 v1 v2 v3 v4 v5 v6 m1 c1 _ tl,
               evalPoly7W19_insert, evalMono7W19_mul, evalPoly7W19, Nat.mul_add]
    have hm : c1 * c2 * (evalMono7W19 v0 v1 v2 v3 v4 v5 v6 m1 * evalMono7W19 v0 v1 v2 v3 v4 v5 v6 m2) =
        c1 * evalMono7W19 v0 v1 v2 v3 v4 v5 v6 m1 * (c2 * evalMono7W19 v0 v1 v2 v3 v4 v5 v6 m2) := by ac_rfl
    rw [hm]; omega

private def poly7MulAux : Poly7W19 -> Poly7W19 -> Poly7W19 -> Poly7W19
  | acc, [], _ => acc
  | acc, (m1, c1) :: tl, q => poly7MulAux (poly7ScaleMono m1 c1 acc q) tl q

private def poly7Mul (p q : Poly7W19) : Poly7W19 := poly7MulAux [] p q

private theorem evalPoly7W19_mul (v0 v1 v2 v3 v4 v5 v6 : Nat) (p q : Poly7W19) :
    evalPoly7W19 v0 v1 v2 v3 v4 v5 v6 (poly7Mul p q) =
      evalPoly7W19 v0 v1 v2 v3 v4 v5 v6 p * evalPoly7W19 v0 v1 v2 v3 v4 v5 v6 q := by
  have haux : ∀ (acc xs : Poly7W19),
      evalPoly7W19 v0 v1 v2 v3 v4 v5 v6 (poly7MulAux acc xs q) =
        evalPoly7W19 v0 v1 v2 v3 v4 v5 v6 acc +
          evalPoly7W19 v0 v1 v2 v3 v4 v5 v6 xs * evalPoly7W19 v0 v1 v2 v3 v4 v5 v6 q := by
    intro acc xs; induction xs generalizing acc with
    | nil => simp [poly7MulAux, evalPoly7W19]
    | cons mc tl ih =>
      rcases mc with ⟨m1, c1⟩
      simp only [poly7MulAux, ih, evalPoly7W19_scaleMono, evalPoly7W19, Nat.add_mul, Nat.add_assoc]
  simpa [poly7Mul, evalPoly7W19] using haux [] p

private def poly7SubTerm (m : Mono7W19) (cs : Nat) : Poly7W19 -> Option Poly7W19
  | [] => if cs = 0 then some [] else none
  | (m2, cb) :: tl =>
    if cs = 0 then some ((m2, cb) :: tl)
    else if m2 = m then
      if cb ≥ cs then some ((m2, cb - cs) :: tl) else none
    else
      match poly7SubTerm m cs tl with
      | none => none
      | some tl' => some ((m2, cb) :: tl')

private theorem poly7SubTerm_sound (v0 v1 v2 v3 v4 v5 v6 : Nat) (m : Mono7W19) (cs : Nat) :
    ∀ (p rem : Poly7W19),
      poly7SubTerm m cs p = some rem ->
      evalPoly7W19 v0 v1 v2 v3 v4 v5 v6 p =
        cs * evalMono7W19 v0 v1 v2 v3 v4 v5 v6 m + evalPoly7W19 v0 v1 v2 v3 v4 v5 v6 rem
  | [], rem, h => by
    unfold poly7SubTerm at h
    by_cases h0 : cs = 0
    · subst h0; simp only [↓reduceIte, Option.some.injEq] at h; subst h; simp [evalPoly7W19]
    · rw [ite_false_of_w10 h0] at h; cases h
  | (m2, cb) :: tl, rem, h => by
    unfold poly7SubTerm at h
    by_cases h0 : cs = 0
    · subst h0; simp only [↓reduceIte, Option.some.injEq] at h; subst h; simp [evalPoly7W19]
    · rw [ite_false_of_w10 h0] at h
      by_cases hm : m2 = m
      · subst hm; rw [ite_true_of_w10 rfl] at h
        by_cases hge : cb ≥ cs
        · rw [ite_true_of_w10 hge] at h; injection h with hrem; subst hrem
          simp only [evalPoly7W19]
          have hmul : cb * evalMono7W19 v0 v1 v2 v3 v4 v5 v6 m2 =
              cs * evalMono7W19 v0 v1 v2 v3 v4 v5 v6 m2 + (cb - cs) * evalMono7W19 v0 v1 v2 v3 v4 v5 v6 m2 := by
            rw [← Nat.add_mul, Nat.add_sub_of_le hge]
          omega
        · rw [ite_false_of_w10 hge] at h; cases h
      · rw [ite_false_of_w10 hm] at h
        cases hsub : poly7SubTerm m cs tl with
        | none => rw [hsub] at h; cases h
        | some tl' =>
          rw [hsub] at h; injection h with hrem; subst hrem
          simp only [evalPoly7W19, poly7SubTerm_sound v0 v1 v2 v3 v4 v5 v6 m cs tl tl' hsub]
          omega

private def poly7DomBool : Poly7W19 -> Poly7W19 -> Bool
  | _, [] => true
  | pBig, (m, cs) :: tl =>
    match poly7SubTerm m cs pBig with
    | none => false
    | some rem => poly7DomBool rem tl

private theorem poly7DomBool_sound (v0 v1 v2 v3 v4 v5 v6 : Nat) :
    ∀ (pBig pSmall : Poly7W19),
      poly7DomBool pBig pSmall = true ->
      evalPoly7W19 v0 v1 v2 v3 v4 v5 v6 pBig ≥ evalPoly7W19 v0 v1 v2 v3 v4 v5 v6 pSmall
  | _, [], _ => Nat.zero_le _
  | pBig, (m, cs) :: tl, h => by
    unfold poly7DomBool at h
    cases hsub : poly7SubTerm m cs pBig with
    | none => rw [hsub] at h; cases h
    | some rem =>
      rw [hsub] at h
      have heq := poly7SubTerm_sound v0 v1 v2 v3 v4 v5 v6 m cs pBig rem hsub
      have hge := poly7DomBool_sound v0 v1 v2 v3 v4 v5 v6 rem tl h
      simp only [evalPoly7W19]
      omega

-- Symbolic `d × d` (`d ∈ {3, 4}`) matrix & vector evaluation over `Poly7W19`:

private def poly7SumFin (d : Nat) (f : Fin d -> Poly7W19) : Nat -> Poly7W19
  | 0 => []
  | n + 1 =>
    if h : n < d then poly7Add (poly7SumFin d f n) (f ⟨n, h⟩)
    else poly7SumFin d f n

private theorem evalPoly7W19_sumFin (v0 v1 v2 v3 v4 v5 v6 d : Nat) (f : Fin d -> Poly7W19) :
    ∀ n : Nat,
      evalPoly7W19 v0 v1 v2 v3 v4 v5 v6 (poly7SumFin d f n) =
        natSumPrefix d (fun q => evalPoly7W19 v0 v1 v2 v3 v4 v5 v6 (f q)) n
  | 0 => rfl
  | n + 1 => by
    unfold poly7SumFin natSumPrefix
    by_cases hn : n < d
    · simp only [hn, dite_true, evalPoly7W19_add, evalPoly7W19_sumFin v0 v1 v2 v3 v4 v5 v6 d f n]
    · simp only [hn, dite_false, Nat.add_zero, evalPoly7W19_sumFin v0 v1 v2 v3 v4 v5 v6 d f n]

private def poly7WordMat (N d : Nat) (symM : Fin N -> Fin d -> Fin d -> Poly7W19) :
    List (Fin N) -> Fin d -> Fin d -> Poly7W19
  | [], i, j => if i.val = j.val then [((0, 0, 0, 0, 0, 0, 0), 1)] else []
  | s :: rest, i, j =>
    let sub := poly7WordMat N d symM rest
    poly7SumFin d (fun q => poly7Mul (symM s i q) (sub q j)) d

private theorem evalPoly7W19_wordMat (v0 v1 v2 v3 v4 v5 v6 N d : Nat)
    (symM : Fin N -> Fin d -> Fin d -> Poly7W19)
    (mat : Fin N -> Fin d -> Fin d -> Nat)
    (hmat : ∀ (s : Fin N) (i j : Fin d),
      evalPoly7W19 v0 v1 v2 v3 v4 v5 v6 (symM s i j) = mat s i j) :
    ∀ (w : List (Fin N)) (i j : Fin d),
      evalPoly7W19 v0 v1 v2 v3 v4 v5 v6 (poly7WordMat N d symM w i j) =
        evalFinWordMat N d mat w i j
  | [], i, j => by
    unfold poly7WordMat evalFinWordMat natMatId
    by_cases hij : i.val = j.val
    · rw [ite_true_of_w10 hij, ite_true_of_w10 hij]; simp [evalPoly7W19, evalMono7W19]
    · rw [ite_false_of_w10 hij, ite_false_of_w10 hij]; rfl
  | s :: rest, i, j => by
    unfold poly7WordMat
    dsimp only
    rw [evalPoly7W19_sumFin]
    change natSumPrefix d _ d = natSumFin d (fun q => mat s i q * evalFinWordMat N d mat rest q j)
    unfold natSumFin
    have hcongr : (fun q : Fin d =>
        evalPoly7W19 v0 v1 v2 v3 v4 v5 v6
          (poly7Mul (symM s i q) (poly7WordMat N d symM rest q j))) =
        (fun q : Fin d => mat s i q * evalFinWordMat N d mat rest q j) := by
      funext q
      rw [evalPoly7W19_mul, hmat s i q, evalPoly7W19_wordMat v0 v1 v2 v3 v4 v5 v6 N d symM mat hmat rest q j]
    rw [hcongr]

private def poly7WordVecBasis (N d : Nat) (symM : Fin N -> Fin d -> Fin d -> Poly7W19)
    (s0Val j0Val : Nat) : List (Fin N) -> Fin d -> Poly7W19
  | [], _ => []
  | s :: rest, i =>
    let sub := poly7WordVecBasis N d symM s0Val j0Val rest
    let v_here : Poly7W19 := if s.val == s0Val && i.val == j0Val then [((0, 0, 0, 0, 0, 0, 0), 1)] else []
    poly7Add v_here (poly7SumFin d (fun q => poly7Mul (symM s i q) (sub q)) d)

private theorem evalPoly7W19_wordVecBasis (v0 v1 v2 v3 v4 v5 v6 N d : Nat)
    (symM : Fin N -> Fin d -> Fin d -> Poly7W19)
    (mat : Fin N -> Fin d -> Fin d -> Nat)
    (hmat : ∀ (s : Fin N) (i j : Fin d),
      evalPoly7W19 v0 v1 v2 v3 v4 v5 v6 (symM s i j) = mat s i j)
    (s0 : Fin N) (j0 : Fin d) :
    ∀ (w : List (Fin N)) (i : Fin d),
      evalPoly7W19 v0 v1 v2 v3 v4 v5 v6 (poly7WordVecBasis N d symM s0.val j0.val w i) =
        evalFinWordVec N d mat (fun s j => if s.val == s0.val && j.val == j0.val then 1 else 0) w i
  | [], _ => rfl
  | s :: rest, i => by
    unfold poly7WordVecBasis
    dsimp only
    rw [evalPoly7W19_add, evalPoly7W19_sumFin]
    have hv_eq : evalPoly7W19 v0 v1 v2 v3 v4 v5 v6
        (if s.val == s0.val && i.val == j0.val then [((0, 0, 0, 0, 0, 0, 0), 1)] else []) =
        (if s.val == s0.val && i.val == j0.val then 1 else 0) := by
      cases (s.val == s0.val && i.val == j0.val) <;> simp [evalPoly7W19, evalMono7W19]
    rw [hv_eq]
    change _ + natSumPrefix d _ d = _ + natSumFin d (fun q => mat s i q * evalFinWordVec N d mat _ rest q)
    unfold natSumFin
    have hcongr : (fun q : Fin d =>
        evalPoly7W19 v0 v1 v2 v3 v4 v5 v6
          (poly7Mul (symM s i q) (poly7WordVecBasis N d symM s0.val j0.val rest q))) =
        (fun q : Fin d =>
          mat s i q * evalFinWordVec N d mat
            (fun s' j' => if s'.val == s0.val && j'.val == j0.val then 1 else 0) rest q) := by
      funext q
      rw [evalPoly7W19_mul, hmat s i q,
          evalPoly7W19_wordVecBasis v0 v1 v2 v3 v4 v5 v6 N d symM mat hmat s0 j0 rest q]
    rw [hcongr]

-- Symbolic single-symbol matrices for `invPosTraceMat3DC39 (2 + dk) a b g d e` and
-- `multiChanInvMat4DC39 (2 + dk) a b g d e z`:

private def symInvMat3DC39W19 (s : Fin 42) (i j : Fin 3) : Poly7W19 :=
  let sv := s.val
  if i.val == 0 && j.val == 0 then
    if 6 ≤ sv && sv ≤ 11 then [((0,0,0,0,0,0,0), 2), ((1,0,0,0,0,0,0), 1)] else [((0,0,0,0,0,0,0), 1)]
  else if i.val == 0 && j.val == 1 then
    if sv == 13 || sv == 14 || sv == 16 || sv == 17 || sv == 18 || sv == 21 then [((0,0,1,0,0,0,0), 2)]
    else if sv == 28 || sv == 32 || sv == 36 then [((0,0,1,0,0,0,0), 1)]
    else []
  else if i.val == 0 && j.val == 2 then
    if sv == 20 || sv == 22 || sv == 23 then [((0,1,0,0,0,0,0), 2)]
    else if sv == 37 || sv == 40 || sv == 41 then [((0,1,0,0,0,0,0), 1)]
    else []
  else if i.val == 1 then
    if isT1InvSymW19 sv then (if j.val == 0 then [((0,0,0,0,1,0,0), 1)] else [((0,0,0,0,0,1,0), 1)])
    else if (sv == 29 || sv == 31) && j.val == 1 then [((0,0,0,0,0,0,0), 1)]
    else []
  else
    if isT2InvSymW19 sv then (if j.val == 0 then [((0,0,0,1,0,0,0), 1)] else [((0,0,0,0,0,1,0), 1)])
    else if (sv == 35 || (6 ≤ sv && sv ≤ 8)) && j.val == 2 then [((0,0,0,0,0,0,0), 1)]
    else []

private theorem eval_symInvMat3DC39W19 (dk a b g d e z : Nat) (s : Fin 42) (i j : Fin 3) :
    evalPoly7W19 dk a b g d e z (symInvMat3DC39W19 s i j) =
      invPosTraceMat3DC39 (2 + dk) a b g d e s i j := by
  unfold symInvMat3DC39W19 invPosTraceMat3DC39
  dsimp only
  split
  · split <;> simp [evalPoly7W19, evalMono7W19]
  · split
    · split
      · simp [evalPoly7W19, evalMono7W19]
      · split <;> simp [evalPoly7W19, evalMono7W19]
    · split
      · split
        · simp [evalPoly7W19, evalMono7W19]
        · split <;> simp [evalPoly7W19, evalMono7W19]
      · split
        · split
          · split <;> simp [evalPoly7W19, evalMono7W19]
          · split <;> simp [evalPoly7W19, evalMono7W19]
        · split
          · split <;> simp [evalPoly7W19, evalMono7W19]
          · split <;> simp [evalPoly7W19, evalMono7W19]

private def symMultiChanMat4DC39W19 (s : Fin 42) (i j : Fin 4) : Poly7W19 :=
  let sv := s.val
  if i.val == 0 && j.val == 0 then
    if 6 ≤ sv && sv ≤ 11 then [((0,0,0,0,0,0,0), 2), ((1,0,0,0,0,0,0), 1)] else [((0,0,0,0,0,0,0), 1)]
  else if i.val == 0 && j.val == 1 then
    if sv == 13 || sv == 14 || sv == 16 || sv == 17 || sv == 18 then [((0,0,1,0,0,0,0), 2)]
    else if sv == 28 || sv == 32 || sv == 36 then [((0,0,1,0,0,0,0), 1)]
    else []
  else if i.val == 0 && j.val == 2 then
    if sv == 20 || sv == 22 then [((0,1,0,0,0,0,0), 2)]
    else if sv == 37 || sv == 40 then [((0,1,0,0,0,0,0), 1)]
    else []
  else if i.val == 0 && j.val == 3 then
    if sv == 21 || sv == 23 then [((0,0,0,0,0,0,1), 2)]
    else if sv == 41 then [((0,0,0,0,0,0,1), 1)]
    else []
  else if i.val == 1 then
    if isT1InvSymW19 sv then (if j.val == 0 then [((0,0,0,0,1,0,0), 1)] else [((0,0,0,0,0,1,0), 1)])
    else if (sv == 29 || sv == 31) && j.val == 1 then [((0,0,0,0,0,0,0), 1)]
    else []
  else if i.val == 2 then
    if isT2InvSymW19 sv then (if j.val == 0 then [((0,0,0,1,0,0,0), 1)] else [((0,0,0,0,0,1,0), 1)])
    else if (sv == 35 || (6 ≤ sv && sv ≤ 8)) && j.val == 2 then [((0,0,0,0,0,0,0), 1)]
    else []
  else
    if (sv == 29 || sv == 31 || sv == 35) && j.val == 3 then [((0,0,0,0,0,0,0), 1)]
    else []

private theorem eval_symMultiChanMat4DC39W19 (dk a b g d e z : Nat) (s : Fin 42) (i j : Fin 4) :
    evalPoly7W19 dk a b g d e z (symMultiChanMat4DC39W19 s i j) =
      multiChanInvMat4DC39 (2 + dk) a b g d e z s i j := by
  unfold symMultiChanMat4DC39W19 multiChanInvMat4DC39
  dsimp only
  split
  · split <;> simp [evalPoly7W19, evalMono7W19]
  · split
    · split
      · simp [evalPoly7W19, evalMono7W19]
      · split <;> simp [evalPoly7W19, evalMono7W19]
    · split
      · split
        · simp [evalPoly7W19, evalMono7W19]
        · split <;> simp [evalPoly7W19, evalMono7W19]
      · split
        · split
          · simp [evalPoly7W19, evalMono7W19]
          · split <;> simp [evalPoly7W19, evalMono7W19]
        · split
          · split
            · split <;> simp [evalPoly7W19, evalMono7W19]
            · split <;> simp [evalPoly7W19, evalMono7W19]
          · split
            · split
              · split <;> simp [evalPoly7W19, evalMono7W19]
              · split <;> simp [evalPoly7W19, evalMono7W19]
            · split <;> simp [evalPoly7W19, evalMono7W19]

-- Boolean dominance checkers for matrix rules (`3D` & `4D`) and Farkas basis pairs (`3D` & `4D`):

private def checkSymMatDomW19 (N d : Nat) (symM : Fin N -> Fin d -> Fin d -> Poly7W19)
    (rs : List (List (Fin N) × List (Fin N))) : Bool :=
  rs.all (fun r =>
    allNatLoopW19 (fun iv =>
      allNatLoopW19 (fun jv =>
        if h : iv < d ∧ jv < d then
          poly7DomBool (poly7WordMat N d symM r.1 ⟨iv, h.1⟩ ⟨jv, h.2⟩)
                       (poly7WordMat N d symM r.2 ⟨iv, h.1⟩ ⟨jv, h.2⟩)
        else true) d) d)

private theorem checkSymMatDomW19_sound (N d : Nat)
    (symM : Fin N -> Fin d -> Fin d -> Poly7W19)
    (rs : List (List (Fin N) × List (Fin N)))
    (hdom : checkSymMatDomW19 N d symM rs = true)
    (v0 v1 v2 v3 v4 v5 v6 : Nat)
    (mat : Fin N -> Fin d -> Fin d -> Nat)
    (hmat : ∀ (s : Fin N) (i j : Fin d), evalPoly7W19 v0 v1 v2 v3 v4 v5 v6 (symM s i j) = mat s i j) :
    ∀ r ∈ rs, ∀ i j : Fin d,
      evalFinWordMat N d mat r.1 i j ≥ evalFinWordMat N d mat r.2 i j := by
  intro r hr i j
  have hr_b := List.all_eq_true.mp hdom r hr
  have hij_b := allNatLoopW19_spec _ d (allNatLoopW19_spec _ d hr_b i.val i.isLt) j.val j.isLt
  have hij : i.val < d ∧ j.val < d := ⟨i.isLt, j.isLt⟩
  simp only [hij] at hij_b
  rw [← evalPoly7W19_wordMat v0 v1 v2 v3 v4 v5 v6 N d symM mat hmat r.1 i j,
      ← evalPoly7W19_wordMat v0 v1 v2 v3 v4 v5 v6 N d symM mat hmat r.2 i j]
  exact poly7DomBool_sound v0 v1 v2 v3 v4 v5 v6 _ _ hij_b

private def wordHasValW19 (s0Val : Nat) : List (Fin N) -> Bool
  | [] => false
  | x :: xs => (x.val == s0Val) || wordHasValW19 s0Val xs

private theorem evalFinWordVec_zero_of_no_sym_w19 (N d : Nat)
    (mat : Fin N -> Fin d -> Fin d -> Nat) (s0 : Fin N) (j0 : Fin d) :
    ∀ (w : List (Fin N)), wordHasValW19 s0.val w = false ->
      ∀ i : Fin d,
        evalFinWordVec N d mat (fun s j => if s.val == s0.val && j.val == j0.val then 1 else 0) w i = 0
  | [], _, _ => rfl
  | x :: xs, hno, i => by
    unfold wordHasValW19 at hno
    rcases Bool.or_eq_false_iff.mp hno with ⟨hx_ne, hxs_no⟩
    change (if x.val == s0.val && i.val == j0.val then 1 else 0) +
      natSumFin d (fun q => mat x i q * evalFinWordVec N d mat _ xs q) = 0
    rw [hx_ne, Bool.false_and]; simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    exact natSumFin_zero_w19 d _ (fun q => by
      rw [evalFinWordVec_zero_of_no_sym_w19 N d mat s0 j0 xs hxs_no q, Nat.mul_zero])

private def symFarkas3DPairW19 (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 mu23 : List (Fin N) -> Nat) (s0Val j0Val : Nat) :
    List (List (Fin N) × List (Fin N)) -> Poly7W19 × Poly7W19
  | [] => ([], [])
  | (l, r) :: rs =>
    let sub := symFarkas3DPairW19 N proj mu0 mu1 mu23 s0Val j0Val rs
    if !(wordHasValW19 s0Val l || wordHasValW19 s0Val r) then sub
    else
      let symM := fun s => symInvMat3DC39W19 (proj s)
      let vl := poly7WordVecBasis N 3 symM s0Val j0Val l
      let vr := poly7WordVecBasis N 3 symM s0Val j0Val r
      let w0 : Poly7W19 := if mu0 l = 0 then [] else [((0,0,0,0,0,0,0), mu0 l)]
      let w1 : Poly7W19 := if mu1 l = 0 then [] else [((0,0,1,0,0,0,0), mu1 l)]
      let w2 : Poly7W19 := if mu23 l = 0 then [] else [((0,1,0,0,0,0,0), mu23 l)]
      let hl := poly7Add (poly7Add (poly7Mul w0 (vl ⟨0, by decide⟩)) (poly7Mul w1 (vl ⟨1, by decide⟩)))
                         (poly7Mul w2 (vl ⟨2, by decide⟩))
      let hr := poly7Add (poly7Add (poly7Mul w0 (vr ⟨0, by decide⟩)) (poly7Mul w1 (vr ⟨1, by decide⟩)))
                         (poly7Mul w2 (vr ⟨2, by decide⟩))
      (poly7Add hl sub.1, poly7Add hr sub.2)

private theorem eval_symFarkas3DPairW19 (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 mu23 : List (Fin N) -> Nat) (dk a b g d e z : Nat)
    (s0 : Fin N) (j0 : Fin 3) :
    ∀ rs : List (List (Fin N) × List (Fin N)),
      let p := symFarkas3DPairW19 N proj mu0 mu1 mu23 s0.val j0.val rs
      (evalPoly7W19 dk a b g d e z p.1, evalPoly7W19 dk a b g d e z p.2) =
        (farkasInv3DVecLhsN N proj mu0 (fun l => b * mu1 l) (fun l => a * mu23 l)
           (2 + dk) a b g d e (basisVec3D N s0 j0) rs,
         farkasInv3DVecRhsN N proj mu0 (fun l => b * mu1 l) (fun l => a * mu23 l)
           (2 + dk) a b g d e (basisVec3D N s0 j0) rs)
  | [] => rfl
  | (l, r) :: rs => by
    dsimp only [symFarkas3DPairW19]
    have ih := eval_symFarkas3DPairW19 N proj mu0 mu1 mu23 dk a b g d e z s0 j0 rs
    dsimp only at ih
    let M := fun s => invPosTraceMat3DC39 (2 + dk) a b g d e (proj s)
    have hmat : ∀ (s : Fin N) (i j : Fin 3),
        evalPoly7W19 dk a b g d e z (symInvMat3DC39W19 (proj s) i j) = M s i j :=
      fun s i j => eval_symInvMat3DC39W19 dk a b g d e z (proj s) i j
    cases hhas : (wordHasValW19 s0.val l || wordHasValW19 s0.val r)
    · simp only [Bool.not_false, ↓reduceIte, farkasInv3DVecLhsN, farkasInv3DVecRhsN]
      rcases Bool.or_eq_false_iff.mp hhas with ⟨hnl, hnr⟩
      have hzl := evalFinWordVec_zero_of_no_sym_w19 N 3 M s0 j0 l hnl
      have hzr := evalFinWordVec_zero_of_no_sym_w19 N 3 M s0 j0 r hnr
      change (evalPoly7W19 dk a b g d e z (symFarkas3DPairW19 N proj mu0 mu1 mu23 s0.val j0.val rs).1,
              evalPoly7W19 dk a b g d e z (symFarkas3DPairW19 N proj mu0 mu1 mu23 s0.val j0.val rs).2) =
        (mu0 l * evalFinWordVec N 3 M (basisVec3D N s0 j0) l ⟨0, by decide⟩ +
          (b * mu1 l) * evalFinWordVec N 3 M (basisVec3D N s0 j0) l ⟨1, by decide⟩ +
          (a * mu23 l) * evalFinWordVec N 3 M (basisVec3D N s0 j0) l ⟨2, by decide⟩ + _,
         mu0 l * evalFinWordVec N 3 M (basisVec3D N s0 j0) r ⟨0, by decide⟩ +
          (b * mu1 l) * evalFinWordVec N 3 M (basisVec3D N s0 j0) r ⟨1, by decide⟩ +
          (a * mu23 l) * evalFinWordVec N 3 M (basisVec3D N s0 j0) r ⟨2, by decide⟩ + _)
      unfold basisVec3D
      rw [hzl ⟨0, by decide⟩, hzl ⟨1, by decide⟩, hzl ⟨2, by decide⟩,
          hzr ⟨0, by decide⟩, hzr ⟨1, by decide⟩, hzr ⟨2, by decide⟩]
      simp only [Nat.mul_zero, Nat.zero_add]
      exact ih
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, farkasInv3DVecLhsN, farkasInv3DVecRhsN,
                 evalPoly7W19_add, evalPoly7W19_mul,
                 evalPoly7W19_wordVecBasis dk a b g d e z N 3 _ M hmat s0 j0]
      have hw0 : evalPoly7W19 dk a b g d e z (if mu0 l = 0 then [] else [((0,0,0,0,0,0,0), mu0 l)]) = mu0 l := by
        by_cases h0 : mu0 l = 0
        · rw [h0]; simp [evalPoly7W19]
        · rw [ite_false_of_w10 h0]; simp [evalPoly7W19, evalMono7W19]
      have hw1 : evalPoly7W19 dk a b g d e z (if mu1 l = 0 then [] else [((0,0,1,0,0,0,0), mu1 l)]) = b * mu1 l := by
        by_cases h0 : mu1 l = 0
        · rw [h0]; simp [evalPoly7W19]
        · rw [ite_false_of_w10 h0]; simp [evalPoly7W19, evalMono7W19, Nat.mul_comm]
      have hw2 : evalPoly7W19 dk a b g d e z (if mu23 l = 0 then [] else [((0,1,0,0,0,0,0), mu23 l)]) = a * mu23 l := by
        by_cases h0 : mu23 l = 0
        · rw [h0]; simp [evalPoly7W19]
        · rw [ite_false_of_w10 h0]; simp [evalPoly7W19, evalMono7W19, Nat.mul_comm]
      rw [hw0, hw1, hw2]
      injection ih with ihl ihr
      rw [ihl, ihr]; rfl

private def symFarkas4DPairW19 (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 mu2 mu3 : List (Fin N) -> Nat) (s0Val j0Val : Nat) :
    List (List (Fin N) × List (Fin N)) -> Poly7W19 × Poly7W19
  | [] => ([], [])
  | (l, r) :: rs =>
    let sub := symFarkas4DPairW19 N proj mu0 mu1 mu2 mu3 s0Val j0Val rs
    if !(wordHasValW19 s0Val l || wordHasValW19 s0Val r) then sub
    else
      let symM := fun s => symMultiChanMat4DC39W19 (proj s)
      let vl := poly7WordVecBasis N 4 symM s0Val j0Val l
      let vr := poly7WordVecBasis N 4 symM s0Val j0Val r
      let w0 : Poly7W19 := if mu0 l = 0 then [] else [((0,0,0,0,0,0,0), mu0 l)]
      let w1 : Poly7W19 := if mu1 l = 0 then [] else [((0,0,1,0,0,0,0), mu1 l)]
      let w2 : Poly7W19 := if mu2 l = 0 then [] else [((0,1,0,0,0,0,0), mu2 l)]
      let w3 : Poly7W19 := if mu3 l = 0 then [] else [((0,0,0,0,0,0,1), mu3 l)]
      let hl := poly7Add (poly7Add (poly7Add (poly7Mul w0 (vl ⟨0, by decide⟩)) (poly7Mul w1 (vl ⟨1, by decide⟩)))
                                   (poly7Mul w2 (vl ⟨2, by decide⟩)))
                         (poly7Mul w3 (vl ⟨3, by decide⟩))
      let hr := poly7Add (poly7Add (poly7Add (poly7Mul w0 (vr ⟨0, by decide⟩)) (poly7Mul w1 (vr ⟨1, by decide⟩)))
                                   (poly7Mul w2 (vr ⟨2, by decide⟩)))
                         (poly7Mul w3 (vr ⟨3, by decide⟩))
      (poly7Add hl sub.1, poly7Add hr sub.2)

private theorem eval_symFarkas4DPairW19 (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 mu2 mu3 : List (Fin N) -> Nat) (dk a b g d e z : Nat)
    (s0 : Fin N) (j0 : Fin 4) :
    ∀ rs : List (List (Fin N) × List (Fin N)),
      let p := symFarkas4DPairW19 N proj mu0 mu1 mu2 mu3 s0.val j0.val rs
      (evalPoly7W19 dk a b g d e z p.1, evalPoly7W19 dk a b g d e z p.2) =
        (farkasInv4DVecLhsN N proj mu0 (fun l => b * mu1 l) (fun l => a * mu2 l) (fun l => z * mu3 l)
           (2 + dk) a b g d e z (basisVec4D N s0 j0) rs,
         farkasInv4DVecRhsN N proj mu0 (fun l => b * mu1 l) (fun l => a * mu2 l) (fun l => z * mu3 l)
           (2 + dk) a b g d e z (basisVec4D N s0 j0) rs)
  | [] => rfl
  | (l, r) :: rs => by
    dsimp only [symFarkas4DPairW19]
    have ih := eval_symFarkas4DPairW19 N proj mu0 mu1 mu2 mu3 dk a b g d e z s0 j0 rs
    dsimp only at ih
    let M := fun s => multiChanInvMat4DC39 (2 + dk) a b g d e z (proj s)
    have hmat : ∀ (s : Fin N) (i j : Fin 4),
        evalPoly7W19 dk a b g d e z (symMultiChanMat4DC39W19 (proj s) i j) = M s i j :=
      fun s i j => eval_symMultiChanMat4DC39W19 dk a b g d e z (proj s) i j
    cases hhas : (wordHasValW19 s0.val l || wordHasValW19 s0.val r)
    · simp only [Bool.not_false, ↓reduceIte, farkasInv4DVecLhsN, farkasInv4DVecRhsN]
      rcases Bool.or_eq_false_iff.mp hhas with ⟨hnl, hnr⟩
      have hzl := evalFinWordVec_zero_of_no_sym_w19 N 4 M s0 j0 l hnl
      have hzr := evalFinWordVec_zero_of_no_sym_w19 N 4 M s0 j0 r hnr
      change (evalPoly7W19 dk a b g d e z (symFarkas4DPairW19 N proj mu0 mu1 mu2 mu3 s0.val j0.val rs).1,
              evalPoly7W19 dk a b g d e z (symFarkas4DPairW19 N proj mu0 mu1 mu2 mu3 s0.val j0.val rs).2) =
        (mu0 l * evalFinWordVec N 4 M (basisVec4D N s0 j0) l ⟨0, by decide⟩ +
          (b * mu1 l) * evalFinWordVec N 4 M (basisVec4D N s0 j0) l ⟨1, by decide⟩ +
          (a * mu2 l) * evalFinWordVec N 4 M (basisVec4D N s0 j0) l ⟨2, by decide⟩ +
          (z * mu3 l) * evalFinWordVec N 4 M (basisVec4D N s0 j0) l ⟨3, by decide⟩ + _,
         mu0 l * evalFinWordVec N 4 M (basisVec4D N s0 j0) r ⟨0, by decide⟩ +
          (b * mu1 l) * evalFinWordVec N 4 M (basisVec4D N s0 j0) r ⟨1, by decide⟩ +
          (a * mu2 l) * evalFinWordVec N 4 M (basisVec4D N s0 j0) r ⟨2, by decide⟩ +
          (z * mu3 l) * evalFinWordVec N 4 M (basisVec4D N s0 j0) r ⟨3, by decide⟩ + _)
      unfold basisVec4D
      rw [hzl ⟨0, by decide⟩, hzl ⟨1, by decide⟩, hzl ⟨2, by decide⟩, hzl ⟨3, by decide⟩,
          hzr ⟨0, by decide⟩, hzr ⟨1, by decide⟩, hzr ⟨2, by decide⟩, hzr ⟨3, by decide⟩]
      simp only [Nat.mul_zero, Nat.zero_add]
      exact ih
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, farkasInv4DVecLhsN, farkasInv4DVecRhsN,
                 evalPoly7W19_add, evalPoly7W19_mul,
                 evalPoly7W19_wordVecBasis dk a b g d e z N 4 _ M hmat s0 j0]
      have hw0 : evalPoly7W19 dk a b g d e z (if mu0 l = 0 then [] else [((0,0,0,0,0,0,0), mu0 l)]) = mu0 l := by
        by_cases h0 : mu0 l = 0
        · rw [h0]; simp [evalPoly7W19]
        · rw [ite_false_of_w10 h0]; simp [evalPoly7W19, evalMono7W19]
      have hw1 : evalPoly7W19 dk a b g d e z (if mu1 l = 0 then [] else [((0,0,1,0,0,0,0), mu1 l)]) = b * mu1 l := by
        by_cases h0 : mu1 l = 0
        · rw [h0]; simp [evalPoly7W19]
        · rw [ite_false_of_w10 h0]; simp [evalPoly7W19, evalMono7W19, Nat.mul_comm]
      have hw2 : evalPoly7W19 dk a b g d e z (if mu2 l = 0 then [] else [((0,1,0,0,0,0,0), mu2 l)]) = a * mu2 l := by
        by_cases h0 : mu2 l = 0
        · rw [h0]; simp [evalPoly7W19]
        · rw [ite_false_of_w10 h0]; simp [evalPoly7W19, evalMono7W19, Nat.mul_comm]
      have hw3 : evalPoly7W19 dk a b g d e z (if mu3 l = 0 then [] else [((0,0,0,0,0,0,1), mu3 l)]) = z * mu3 l := by
        by_cases h0 : mu3 l = 0
        · rw [h0]; simp [evalPoly7W19]
        · rw [ite_false_of_w10 h0]; simp [evalPoly7W19, evalMono7W19, Nat.mul_comm]
      rw [hw0, hw1, hw2, hw3]
      injection ih with ihl ihr
      rw [ihl, ihr]; rfl

private def checkSymFarkas3DRangeW19 (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 mu23 : List (Fin N) -> Nat)
    (rs : List (List (Fin N) × List (Fin N))) (start : Nat) : Nat -> Bool
  | 0 => true
  | cnt + 1 =>
    let idx := start + cnt
    allNatLoopW19 (fun j0v =>
      let p := symFarkas3DPairW19 N proj mu0 mu1 mu23 idx j0v rs
      poly7DomBool p.2 p.1) 3 &&
    checkSymFarkas3DRangeW19 N proj mu0 mu1 mu23 rs start cnt

private def checkSymFarkas4DRangeW19 (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 mu2 mu3 : List (Fin N) -> Nat)
    (rs : List (List (Fin N) × List (Fin N))) (start : Nat) : Nat -> Bool
  | 0 => true
  | cnt + 1 =>
    let idx := start + cnt
    allNatLoopW19 (fun j0v =>
      let p := symFarkas4DPairW19 N proj mu0 mu1 mu2 mu3 idx j0v rs
      poly7DomBool p.2 p.1) 4 &&
    checkSymFarkas4DRangeW19 N proj mu0 mu1 mu2 mu3 rs start cnt

-- Modular `by decide` certificates for `3D` & `4D` matrix dominance, strict counts, escapes, & Farkas ranges:

set_option maxRecDepth 65536 in
private theorem inv3d_4d_mat_dom_and_strict_c39_w19 :
    checkSymMatDomW19 42 3 symInvMat3DC39W19 c39FastRulesW19 = true ∧
    checkSymMatDomW19 42 4 symMultiChanMat4DC39W19 c39FastRulesW19 = true ∧
    c78FastRulesW19.all (fun r =>
      c39FastRulesW19.any (fun r39 =>
        (r.1.map projSym84To42, r.2.map projSym84To42) == r39)) = true ∧
    c39FastRulesW19.all (fun r => decide (farkasMu0CoupledC39 r.1 ≥ 1)) = true ∧
    c78FastRulesW19.all (fun r => decide (farkasMu0CoupledC78 r.1 ≥ 1)) = true ∧
    countStrictMat3DRules 42 (invPosTraceMat3DC39 2 1 1 1 1 1) c39FastRulesW19 = 39 ∧
    countStrictMat4DRules 42 (multiChanInvMat4DC39 2 1 1 1 1 1 1) c39FastRulesW19 = 39 := by decide

set_option maxRecDepth 65536 in
private theorem inv3d_4d_strict_c78_and_escapes_w19 :
    countStrictMat3DRules 84 (invPosTraceMat3DC78 2 1 1 1 1 1) c78FastRulesW19 = 78 ∧
    countStrictMat4DRules 84 (multiChanInvMat4DC78 2 1 1 1 1 1 1) c78FastRulesW19 = 78 ∧
    farkasInv3DVecLhsN 42 id farkasMu0CoupledC39 farkasMu1BlockNilp3DC39 farkasMu1BiBTRC39
      2 1 1 1 1 1 (basisVec3D 42 ⟨14, by decide⟩ ⟨1, by decide⟩) c39FastRulesW19 -
    farkasInv3DVecRhsN 42 id farkasMu0CoupledC39 farkasMu1BlockNilp3DC39 farkasMu1BiBTRC39
      2 1 1 1 1 1 (basisVec3D 42 ⟨14, by decide⟩ ⟨1, by decide⟩) c39FastRulesW19 = 6 ∧
    farkasInv4DVecLhsN 42 id farkasMu0CoupledC39 farkasMu1InvW19C39 farkasMu2InvW19C39 (fun _ => 0)
      2 1 1 1 1 1 1 (basisVec4D 42 ⟨23, by decide⟩ ⟨3, by decide⟩) c39FastRulesW19 -
    farkasInv4DVecRhsN 42 id farkasMu0CoupledC39 farkasMu1InvW19C39 farkasMu2InvW19C39 (fun _ => 0)
      2 1 1 1 1 1 1 (basisVec4D 42 ⟨23, by decide⟩ ⟨3, by decide⟩) c39FastRulesW19 = 1 := by decide

set_option maxRecDepth 65536 in
private theorem inv3d_farkas_c39_cert_w19 :
    checkSymFarkas3DRangeW19 42 id farkasMu0CoupledC39 farkasMu1InvW19C39
      (fun l => farkasMu2InvW19C39 l + farkasMu3InvW19C39 l) c39FastRulesW19 0 42 = true := by decide

set_option maxRecDepth 65536 in
private theorem inv4d_farkas_c39_cert_w19 :
    checkSymFarkas4DRangeW19 42 id farkasMu0CoupledC39 farkasMu1InvW19C39
      farkasMu2InvW19C39 farkasMu3InvW19C39 c39FastRulesW19 0 42 = true := by decide

set_option maxRecDepth 65536 in
private theorem inv3d_farkas_c78_q0_w19 :
    checkSymFarkas3DRangeW19 84 projSym84To42 farkasMu0CoupledC78 farkasMu1InvW19C78
      (fun l => farkasMu2InvW19C78 l + farkasMu3InvW19C78 l) c78FastRulesW19 0 21 = true := by decide
set_option maxRecDepth 65536 in
private theorem inv3d_farkas_c78_q1_w19 :
    checkSymFarkas3DRangeW19 84 projSym84To42 farkasMu0CoupledC78 farkasMu1InvW19C78
      (fun l => farkasMu2InvW19C78 l + farkasMu3InvW19C78 l) c78FastRulesW19 21 21 = true := by decide
set_option maxRecDepth 65536 in
private theorem inv3d_farkas_c78_q2_w19 :
    checkSymFarkas3DRangeW19 84 projSym84To42 farkasMu0CoupledC78 farkasMu1InvW19C78
      (fun l => farkasMu2InvW19C78 l + farkasMu3InvW19C78 l) c78FastRulesW19 42 21 = true := by decide
set_option maxRecDepth 65536 in
private theorem inv3d_farkas_c78_q3_w19 :
    checkSymFarkas3DRangeW19 84 projSym84To42 farkasMu0CoupledC78 farkasMu1InvW19C78
      (fun l => farkasMu2InvW19C78 l + farkasMu3InvW19C78 l) c78FastRulesW19 63 21 = true := by decide

set_option maxRecDepth 65536 in
private theorem inv4d_farkas_c78_q0_w19 :
    checkSymFarkas4DRangeW19 84 projSym84To42 farkasMu0CoupledC78 farkasMu1InvW19C78
      farkasMu2InvW19C78 farkasMu3InvW19C78 c78FastRulesW19 0 21 = true := by decide
set_option maxRecDepth 65536 in
private theorem inv4d_farkas_c78_q1_w19 :
    checkSymFarkas4DRangeW19 84 projSym84To42 farkasMu0CoupledC78 farkasMu1InvW19C78
      farkasMu2InvW19C78 farkasMu3InvW19C78 c78FastRulesW19 21 21 = true := by decide
set_option maxRecDepth 65536 in
private theorem inv4d_farkas_c78_q2_w19 :
    checkSymFarkas4DRangeW19 84 projSym84To42 farkasMu0CoupledC78 farkasMu1InvW19C78
      farkasMu2InvW19C78 farkasMu3InvW19C78 c78FastRulesW19 42 21 = true := by decide
set_option maxRecDepth 65536 in
private theorem inv4d_farkas_c78_q3_w19 :
    checkSymFarkas4DRangeW19 84 projSym84To42 farkasMu0CoupledC78 farkasMu1InvW19C78
      farkasMu2InvW19C78 farkasMu3InvW19C78 c78FastRulesW19 63 21 = true := by decide

-- General `d`-dimensional (`∀ d ≥ 1`) basis linearity & Farkas zero-strict-drop lemma:

private def genFarkasVecLhsW19 (N d : Nat) (M : Fin N -> Fin d -> Fin d -> Nat)
    (wt : Fin d -> List (Fin N) -> Nat) (v : Fin N -> Fin d -> Nat) :
    List (List (Fin N) × List (Fin N)) -> Nat
  | [] => 0
  | (l, _) :: rs =>
    natSumFin d (fun i => wt i l * evalFinWordVec N d M v l i) +
      genFarkasVecLhsW19 N d M wt v rs

private def genFarkasVecRhsW19 (N d : Nat) (M : Fin N -> Fin d -> Fin d -> Nat)
    (wt : Fin d -> List (Fin N) -> Nat) (v : Fin N -> Fin d -> Nat) :
    List (List (Fin N) × List (Fin N)) -> Nat
  | [] => 0
  | (l, r) :: rs =>
    natSumFin d (fun i => wt i l * evalFinWordVec N d M v r i) +
      genFarkasVecRhsW19 N d M wt v rs

private theorem natSumFin_const_mul_w19 (d c : Nat) (f : Fin d -> Nat) :
    c * natSumFin d f = natSumFin d (fun i => c * f i) := by
  calc c * natSumFin d f = natSumFin d f * c := Nat.mul_comm _ _
    _ = natSumFin d (fun i => f i * c) := (natSumFin_mul_const_w19 d c f).symm
    _ = natSumFin d (fun i => c * f i) := congrArg (natSumFin d) (funext fun i => Nat.mul_comm _ _)

private theorem genFarkas_zero_strict_of_basis_w19 (N d : Nat) (hd : d ≥ 1)
    (M : Fin N -> Fin d -> Fin d -> Nat)
    (wt : Fin d -> List (Fin N) -> Nat)
    (rs : List (List (Fin N) × List (Fin N)))
    (hwt0_pos : ∀ r ∈ rs, wt ⟨0, hd⟩ r.1 ≥ 1)
    (hbasis : ∀ (s0 : Fin N) (j0 : Fin d),
      let bVec := fun (s : Fin N) (j : Fin d) => if s.val == s0.val && j.val == j0.val then 1 else 0
      genFarkasVecLhsW19 N d M wt bVec rs ≤ genFarkasVecRhsW19 N d M wt bVec rs)
    (v : Fin N -> Fin d -> Nat)
    (hv_weak : ∀ r ∈ rs, ∀ i : Fin d, evalFinWordVec N d M v r.1 i ≥ evalFinWordVec N d M v r.2 i) :
    ∀ r ∈ rs, evalFinWordVec N d M v r.1 ⟨0, hd⟩ = evalFinWordVec N d M v r.2 ⟨0, hd⟩ := by
  let bVec (s0 : Fin N) (j0 : Fin d) (s : Fin N) (j : Fin d) : Nat :=
    if s.val == s0.val && j.val == j0.val then 1 else 0
  have hdelta : ∀ (s : Fin N) (j : Fin d),
      v s j = natSumFin N (fun s0 => natSumFin d (fun j0 => v s0 j0 * bVec s0 j0 s j)) := by
    intro s j
    have hinner : ∀ s0 : Fin N,
        natSumFin d (fun j0 => v s0 j0 * bVec s0 j0 s j) = if s.val == s0.val then v s0 j else 0 := by
      intro s0
      cases hs : (s.val == s0.val)
      · exact natSumFin_zero_w19 d _ (fun j0 => by dsimp [bVec]; rw [hs]; simp)
      · have hpre : ∀ n : Nat, j.val < n -> n ≤ d ->
            natSumPrefix d (fun j0 => v s0 j0 * bVec s0 j0 s j) n = v s0 j := by
          intro n; induction n with
          | zero => intro hlt _; omega
          | succ n' ih =>
            intro hlt hle
            have hn_lt : n' < d := hle
            unfold natSumPrefix; simp only [hn_lt, dite_true]
            by_cases heq : j.val = n'
            · have hj_eq : j = ⟨n', hn_lt⟩ := Fin.ext heq
              subst hj_eq
              have hz : natSumPrefix d (fun j0 => v s0 j0 * bVec s0 j0 s ⟨n', hn_lt⟩) n' = 0 := by
                have h0 : ∀ m : Nat, m ≤ n' ->
                    natSumPrefix d (fun j0 => v s0 j0 * bVec s0 j0 s ⟨n', hn_lt⟩) m = 0 := by
                  intro m; induction m with
                  | zero => intros; rfl
                  | succ m' ihm =>
                    intro hm'
                    have hm_lt : m' < d := by omega
                    have hne : (n' == m') = false := beq_false_of_ne (by omega)
                    unfold natSumPrefix; simp only [hm_lt, dite_true]
                    rw [ihm (by omega), Nat.zero_add]; dsimp [bVec]; rw [hs, hne]; simp
                exact h0 n' (Nat.le_refl n')
              rw [hz, Nat.zero_add]; dsimp [bVec]; rw [hs, beq_self_eq_true]; simp
            · have hne : (j.val == n') = false := beq_false_of_ne heq
              rw [ih (by omega) (by omega)]; dsimp [bVec]; rw [hs, hne]; simp
        exact hpre d j.isLt (Nat.le_refl d)
    have houter : ∀ n : Nat, s.val < n -> n ≤ N ->
        natSumPrefix N (fun s0 => if s.val == s0.val then v s0 j else 0) n = v s j := by
      intro n; induction n with
      | zero => intro hlt _; omega
      | succ n' ih =>
        intro hlt hle
        have hn_lt : n' < N := hle
        unfold natSumPrefix; simp only [hn_lt, dite_true]
        by_cases heq : s.val = n'
        · have hs_eq : s = ⟨n', hn_lt⟩ := Fin.ext heq
          subst hs_eq
          have hz : natSumPrefix N (fun s0 => if n' == s0.val then v s0 j else 0) n' = 0 := by
            have h0 : ∀ m : Nat, m ≤ n' ->
                natSumPrefix N (fun s0 => if n' == s0.val then v s0 j else 0) m = 0 := by
              intro m; induction m with
              | zero => intros; rfl
              | succ m' ihm =>
                intro hm'
                have hm_lt : m' < N := by omega
                have hne : (n' == m') = false := beq_false_of_ne (by omega)
                unfold natSumPrefix; simp only [hm_lt, dite_true]
                rw [ihm (by omega), Nat.zero_add, hne]; simp
            exact h0 n' (Nat.le_refl n')
          rw [hz, Nat.zero_add, beq_self_eq_true]; simp
        · have hne : (s.val == n') = false := beq_false_of_ne heq
          rw [ih (by omega) (by omega), hne]; simp
    have hc : (fun s0 : Fin N => natSumFin d (fun j0 => v s0 j0 * bVec s0 j0 s j)) =
        (fun s0 : Fin N => if s.val == s0.val then v s0 j else 0) := funext hinner
    rw [hc]; exact (houter N s.isLt (Nat.le_refl N)).symm
  have hv_lin : ∀ (w : List (Fin N)) (i : Fin d),
      evalFinWordVec N d M v w i =
        natSumFin N (fun s0 => natSumFin d (fun j0 => v s0 j0 * evalFinWordVec N d M (bVec s0 j0) w i)) := by
    intro w; induction w with
    | nil =>
      intro i
      change 0 = _
      exact (natSumFin_zero_w19 N _ (fun _ => natSumFin_zero_w19 d _ (fun _ => Nat.mul_zero _))).symm
    | cons s rest ih =>
      intro i
      change v s i + natSumFin d (fun q => M s i q * evalFinWordVec N d M v rest q) = _
      rw [hdelta s i]
      have hmat_sum : natSumFin d (fun q => M s i q * evalFinWordVec N d M v rest q) =
          natSumFin N (fun s0 => natSumFin d (fun j0 =>
            v s0 j0 * natSumFin d (fun q => M s i q * evalFinWordVec N d M (bVec s0 j0) rest q))) := by
        have hstep1 : (fun q : Fin d => M s i q * evalFinWordVec N d M v rest q) =
            (fun q : Fin d => natSumFin N (fun s0 => natSumFin d (fun j0 =>
              v s0 j0 * (M s i q * evalFinWordVec N d M (bVec s0 j0) rest q)))) := by
          funext q
          rw [ih q, natSumFin_const_mul_w19]
          apply congrArg (natSumFin N); funext s0
          rw [natSumFin_const_mul_w19]
          apply congrArg (natSumFin d); funext j0; ac_rfl
        rw [hstep1]
        -- Swap `q : Fin d` past `s0 : Fin N` and `j0 : Fin d`:
        have hswap_Nd : ∀ (G : Fin d -> Fin N -> Nat),
            natSumFin d (fun q => natSumFin N (fun s0 => G q s0)) =
              natSumFin N (fun s0 => natSumFin d (fun q => G q s0)) := by
          intro G
          have hpre : ∀ m n : Nat,
              natSumPrefix d (fun q => natSumPrefix N (fun s0 => G q s0) n) m =
                natSumPrefix N (fun s0 => natSumPrefix d (fun q => G q s0) m) n := by
            intro m; induction m with
            | zero => intro n; exact (natSumPrefix_zero_w19 N _ (fun _ => rfl) n).symm
            | succ m' ihm =>
              intro n; simp only [natSumPrefix, ihm n]
              by_cases hm : m' < d
              · simp only [hm, dite_true, ← natSumPrefix_add_w19]
              · simp only [hm, dite_false, Nat.add_zero]
          exact hpre d N
        rw [hswap_Nd]
        apply congrArg (natSumFin N); funext s0
        rw [natSumFin_swap_w19 d]
        apply congrArg (natSumFin d); funext j0
        rw [natSumFin_const_mul_w19]
      rw [hmat_sum, ← natSumFin_add_w19]
      apply congrArg (natSumFin N); funext s0
      rw [← natSumFin_add_w19]
      apply congrArg (natSumFin d); funext j0
      rw [← Nat.mul_add]; rfl
  have hfark_lin : ∀ xs : List (List (Fin N) × List (Fin N)),
      genFarkasVecLhsW19 N d M wt v xs =
        natSumFin N (fun s0 => natSumFin d (fun j0 => v s0 j0 * genFarkasVecLhsW19 N d M wt (bVec s0 j0) xs)) ∧
      genFarkasVecRhsW19 N d M wt v xs =
        natSumFin N (fun s0 => natSumFin d (fun j0 => v s0 j0 * genFarkasVecRhsW19 N d M wt (bVec s0 j0) xs)) := by
    intro xs; induction xs with
    | nil =>
      refine ⟨?_, ?_⟩ <;>
      exact (natSumFin_zero_w19 N _ (fun _ => natSumFin_zero_w19 d _ (fun _ => Nat.mul_zero _))).symm
    | cons r0 rtl ih =>
      rcases r0 with ⟨l0, r0_w⟩
      rcases ih with ⟨ihl, ihr⟩
      have hrow_lin : ∀ w : List (Fin N),
          natSumFin d (fun i => wt i l0 * evalFinWordVec N d M v w i) =
            natSumFin N (fun s0 => natSumFin d (fun j0 =>
              v s0 j0 * natSumFin d (fun i => wt i l0 * evalFinWordVec N d M (bVec s0 j0) w i))) := by
        intro w
        have h1 : (fun i : Fin d => wt i l0 * evalFinWordVec N d M v w i) =
            (fun i : Fin d => natSumFin N (fun s0 => natSumFin d (fun j0 =>
              v s0 j0 * (wt i l0 * evalFinWordVec N d M (bVec s0 j0) w i)))) := by
          funext i; rw [hv_lin w i, natSumFin_const_mul_w19]
          apply congrArg (natSumFin N); funext s0
          rw [natSumFin_const_mul_w19]
          apply congrArg (natSumFin d); funext j0; ac_rfl
        rw [h1]
        have hswap_Nd : ∀ (G : Fin d -> Fin N -> Nat),
            natSumFin d (fun i => natSumFin N (fun s0 => G i s0)) =
              natSumFin N (fun s0 => natSumFin d (fun i => G i s0)) := by
          intro G
          have hpre : ∀ m n : Nat,
              natSumPrefix d (fun i => natSumPrefix N (fun s0 => G i s0) n) m =
                natSumPrefix N (fun s0 => natSumPrefix d (fun i => G i s0) m) n := by
            intro m; induction m with
            | zero => intro n; exact (natSumPrefix_zero_w19 N _ (fun _ => rfl) n).symm
            | succ m' ihm =>
              intro n; simp only [natSumPrefix, ihm n]
              by_cases hm : m' < d
              · simp only [hm, dite_true, ← natSumPrefix_add_w19]
              · simp only [hm, dite_false, Nat.add_zero]
          exact hpre d N
        rw [hswap_Nd]
        apply congrArg (natSumFin N); funext s0
        rw [natSumFin_swap_w19 d]
        apply congrArg (natSumFin d); funext j0
        rw [natSumFin_const_mul_w19]
      refine ⟨?_, ?_⟩
      · simp only [genFarkasVecLhsW19, hrow_lin l0, ihl]
        rw [← natSumFin_add_w19]
        apply congrArg (natSumFin N); funext s0
        rw [← natSumFin_add_w19]; apply congrArg (natSumFin d); funext j0; exact (Nat.mul_add _ _ _).symm
      · simp only [genFarkasVecRhsW19, hrow_lin r0_w, ihr]
        rw [← natSumFin_add_w19]
        apply congrArg (natSumFin N); funext s0
        rw [← natSumFin_add_w19]; apply congrArg (natSumFin d); funext j0; exact (Nat.mul_add _ _ _).symm
  have htot_le : genFarkasVecLhsW19 N d M wt v rs ≤ genFarkasVecRhsW19 N d M wt v rs := by
    rcases hfark_lin rs with ⟨hl, hr⟩
    rw [hl, hr]
    exact natSumFin_le_w19 N _ _ (fun s0 =>
      natSumFin_le_w19 d _ _ (fun j0 => Nat.mul_le_mul_left _ (hbasis s0 j0)))
  have hge_imp : ∀ xs : List (List (Fin N) × List (Fin N)),
      (∀ r ∈ xs, wt ⟨0, hd⟩ r.1 ≥ 1) ->
      (∀ r ∈ xs, ∀ i : Fin d, evalFinWordVec N d M v r.1 i ≥ evalFinWordVec N d M v r.2 i) ->
      genFarkasVecLhsW19 N d M wt v xs ≥ genFarkasVecRhsW19 N d M wt v xs ∧
      (genFarkasVecLhsW19 N d M wt v xs ≤ genFarkasVecRhsW19 N d M wt v xs ->
        ∀ r ∈ xs, evalFinWordVec N d M v r.1 ⟨0, hd⟩ = evalFinWordVec N d M v r.2 ⟨0, hd⟩) := by
    intro xs; induction xs with
    | nil => intros; exact ⟨Nat.le_refl 0, fun _ _ hr => by cases hr⟩
    | cons r0 rtl ih =>
      rcases r0 with ⟨l0, r0_w⟩
      intro hpos hw
      rcases ih (fun r hr => hpos r (List.Mem.tail _ hr))
        (fun r hr => hw r (List.Mem.tail _ hr)) with ⟨hge_tl, heq_tl⟩
      have hsum_ge : natSumFin d (fun i => wt i l0 * evalFinWordVec N d M v l0 i) ≥
          natSumFin d (fun i => wt i l0 * evalFinWordVec N d M v r0_w i) :=
        natSumFin_le_w19 d _ _ (fun i => Nat.mul_le_mul_left _ (hw (l0, r0_w) (List.Mem.head _) i))
      simp only [genFarkasVecLhsW19, genFarkasVecRhsW19]
      refine ⟨by omega, fun htot r hr => ?_⟩
      cases hr with
      | head =>
        have hsum_eq : natSumFin d (fun i => wt i l0 * evalFinWordVec N d M v l0 i) =
            natSumFin d (fun i => wt i l0 * evalFinWordVec N d M v r0_w i) := by omega
        -- Split off index `0`:
        have h0_split : ∀ (f : Fin d -> Nat),
            natSumFin d f = f ⟨0, hd⟩ + natTailSum1 d f := by
          intro f; unfold natTailSum1
          have hc : f = (fun i : Fin d => (if i.val = 0 then f i else 0) + (if i.val = 0 then 0 else f i)) := by
            funext i; by_cases hi : i.val = 0 <;> simp [hi]
          conv => lhs; rw [hc]
          rw [natSumFin_add_w19, natSumFin_single_zero_w19 d hd _ (fun j hj => by rw [ite_false_of_w10 (by omega)])]
          simp
        rw [h0_split (fun i => wt i l0 * evalFinWordVec N d M v l0 i),
            h0_split (fun i => wt i l0 * evalFinWordVec N d M v r0_w i)] at hsum_eq
        have htail_ge : natTailSum1 d (fun i => wt i l0 * evalFinWordVec N d M v l0 i) ≥
            natTailSum1 d (fun i => wt i l0 * evalFinWordVec N d M v r0_w i) :=
          natTailSum1_le_w19 d _ _ (fun i _ => Nat.mul_le_mul_left _ (hw (l0, r0_w) (List.Mem.head _) i))
        have h0_ge := Nat.mul_le_mul_left (wt ⟨0, hd⟩ l0) (hw (l0, r0_w) (List.Mem.head _) ⟨0, hd⟩)
        have hw0_pos := hpos (l0, r0_w) (List.Mem.head _)
        dsimp only at h0_ge hw0_pos
        have h0_eq : wt ⟨0, hd⟩ l0 * evalFinWordVec N d M v l0 ⟨0, hd⟩ =
            wt ⟨0, hd⟩ l0 * evalFinWordVec N d M v r0_w ⟨0, hd⟩ := by omega
        exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < wt ⟨0, hd⟩ l0) h0_eq
      | tail _ htl => exact heq_tl (by omega) r htl
  exact (hge_imp rs hwt0_pos hv_weak).2 htot_le

-- Unpack `checkSymFarkas3DRangeW19` and `checkSymFarkas4DRangeW19`:

private theorem unpack_symFarkas3DRange_w19 (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 mu23 : List (Fin N) -> Nat)
    (rs : List (List (Fin N) × List (Fin N))) (start : Nat) :
    ∀ cnt : Nat, checkSymFarkas3DRangeW19 N proj mu0 mu1 mu23 rs start cnt = true ->
      ∀ (dk a b g d e : Nat) (s0 : Fin N) (j0 : Fin 3),
        start ≤ s0.val -> s0.val < start + cnt ->
        farkasInv3DVecLhsN N proj mu0 (fun l => b * mu1 l) (fun l => a * mu23 l)
          (2 + dk) a b g d e (basisVec3D N s0 j0) rs ≤
        farkasInv3DVecRhsN N proj mu0 (fun l => b * mu1 l) (fun l => a * mu23 l)
          (2 + dk) a b g d e (basisVec3D N s0 j0) rs
  | 0, _, _, _, _, _, _, _, _, _, hlo, hhi => by omega
  | cnt' + 1, hchk, dk, a, b, g, d, e, s0, j0, hlo, hhi => by
    unfold checkSymFarkas3DRangeW19 at hchk
    rcases bool_and_split_w19 hchk with ⟨hcur, hprev⟩
    by_cases heq : s0.val = start + cnt'
    · have hj_dom := allNatLoopW19_spec _ 3 hcur j0.val j0.isLt
      dsimp only at hj_dom
      rw [← heq] at hj_dom
      have hge := poly7DomBool_sound dk a b g d e 0 _ _ hj_dom
      have hev := eval_symFarkas3DPairW19 N proj mu0 mu1 mu23 dk a b g d e 0 s0 j0 rs
      dsimp only at hev
      injection hev with hl hr
      omega
    · exact unpack_symFarkas3DRange_w19 N proj mu0 mu1 mu23 rs start cnt' hprev
        dk a b g d e s0 j0 hlo (by omega)

private theorem unpack_symFarkas4DRange_w19 (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 mu2 mu3 : List (Fin N) -> Nat)
    (rs : List (List (Fin N) × List (Fin N))) (start : Nat) :
    ∀ cnt : Nat, checkSymFarkas4DRangeW19 N proj mu0 mu1 mu2 mu3 rs start cnt = true ->
      ∀ (dk a b g d e z : Nat) (s0 : Fin N) (j0 : Fin 4),
        start ≤ s0.val -> s0.val < start + cnt ->
        farkasInv4DVecLhsN N proj mu0 (fun l => b * mu1 l) (fun l => a * mu2 l) (fun l => z * mu3 l)
          (2 + dk) a b g d e z (basisVec4D N s0 j0) rs ≤
        farkasInv4DVecRhsN N proj mu0 (fun l => b * mu1 l) (fun l => a * mu2 l) (fun l => z * mu3 l)
          (2 + dk) a b g d e z (basisVec4D N s0 j0) rs
  | 0, _, _, _, _, _, _, _, _, _, _, hlo, hhi => by omega
  | cnt' + 1, hchk, dk, a, b, g, d, e, z, s0, j0, hlo, hhi => by
    unfold checkSymFarkas4DRangeW19 at hchk
    rcases bool_and_split_w19 hchk with ⟨hcur, hprev⟩
    by_cases heq : s0.val = start + cnt'
    · have hj_dom := allNatLoopW19_spec _ 4 hcur j0.val j0.isLt
      dsimp only at hj_dom
      rw [← heq] at hj_dom
      have hge := poly7DomBool_sound dk a b g d e z _ _ hj_dom
      have hev := eval_symFarkas4DPairW19 N proj mu0 mu1 mu2 mu3 dk a b g d e z s0 j0 rs
      dsimp only at hev
      injection hev with hl hr
      omega
    · exact unpack_symFarkas4DRange_w19 N proj mu0 mu1 mu2 mu3 rs start cnt' hprev
        dk a b g d e z s0 j0 hlo (by omega)

-- Exact reduction of `multiChanInvMatTowerAnyDC39 d` (`∀ d ≥ 4`) to `multiChanInvMat4DC39`:

private theorem natSumFin_split3_w19 (d : Nat) (hd : d ≥ 4) (f : Fin d -> Nat) :
    natSumFin d f =
      f ⟨0, by omega⟩ + f ⟨1, by omega⟩ + f ⟨2, by omega⟩ +
        natSumFin d (fun q => if q.val ≥ 3 then f q else 0) := by
  have hpre : ∀ n : Nat, 3 ≤ n -> n ≤ d ->
      natSumPrefix d f n =
        f ⟨0, by omega⟩ + f ⟨1, by omega⟩ + f ⟨2, by omega⟩ +
          natSumPrefix d (fun q => if q.val ≥ 3 then f q else 0) n := by
    intro n; induction n with
    | zero => intro h3 _; omega
    | succ n' ih =>
      intro h3 hle
      have hn_lt : n' < d := hle
      by_cases h2 : n' = 2
      · subst h2
        have h0 : 0 < d := by omega
        have h1 : 1 < d := by omega
        have h2d : 2 < d := by omega
        simp only [natSumPrefix, h0, h1, h2d, dite_true]
        have hn0 : ¬ (0 ≥ 3) := by decide
        have hn1 : ¬ (1 ≥ 3) := by decide
        have hn2 : ¬ (2 ≥ 3) := by decide
        simp only [hn0, hn1, hn2, ite_false]; omega
      · have hge3 : 3 ≤ n' := by omega
        unfold natSumPrefix
        simp only [hn_lt, dite_true, ih hge3 (by omega), ite_true_of_w10 hge3]
        omega
  exact hpre d (by omega) (Nat.le_refl d)

private theorem anyD_wordMat_eq_4d_w19 (N d : Nat) (hd : d ≥ 4) (proj : Fin N -> Fin 42)
    (k a b g de e : Nat) (zetaCh : Fin d -> Nat) :
    let Many := fun s => multiChanInvMatTowerAnyDC39 d k a b g de e zetaCh (proj s)
    let M4 := fun z s => multiChanInvMat4DC39 k a b g de e z (proj s)
    ∀ w : List (Fin N),
      (∀ (i j : Fin d) (hi : i.val < 3) (hj : j.val < 3),
        evalFinWordMat N d Many w i j =
          evalFinWordMat N 4 (M4 0) w ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) ∧
      (∀ (i j : Fin d) (hi : i.val < 3), j.val ≥ 3 ->
        evalFinWordMat N d Many w i j =
          evalFinWordMat N 4 (M4 (zetaCh j)) w ⟨i.val, by omega⟩ ⟨3, by decide⟩) ∧
      (∀ (i : Fin d), i.val ≥ 3 ->
        evalFinWordMat N d Many w i i =
          evalFinWordMat N 4 (M4 0) w ⟨3, by decide⟩ ⟨3, by decide⟩) ∧
      (∀ (i j : Fin d), i.val ≥ 3 -> i ≠ j ->
        evalFinWordMat N d Many w i j = 0) := by
  intro Many M4 w
  have hentry_lt3 : ∀ (s : Fin N) (i j : Fin d) (hi : i.val < 3) (hj : j.val < 3) (z : Nat),
      Many s i j = M4 z s ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ := by
    intro s i j hi hj z
    dsimp [Many, M4, multiChanInvMatTowerAnyDC39]
    have hb : (decide (i.val < 3) && decide (j.val < 3)) = true := by simp [hi, hj]
    rw [hb]; simp only [↓reduceIte, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
    unfold multiChanInvMat4DC39; dsimp only
    rcases (by omega : j.val = 0 ∨ j.val = 1 ∨ j.val = 2) with hj0 | hj1 | hj2 <;>
    rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2) with hi0 | hi1 | hi2 <;>
    simp_all
  have hentry_ge3_row : ∀ (s : Fin N) (i q : Fin d), i.val ≥ 3 ->
      Many s i q = if q = i then M4 (zetaCh q) s ⟨3, by decide⟩ ⟨3, by decide⟩ else 0 := by
    intro s i q hi
    dsimp only [Many, M4]; unfold multiChanInvMatTowerAnyDC39 multiChanInvMat4DC39; dsimp only
    have hni3 : ¬ (i.val < 3) := by omega
    have hi0 : (i.val == 0) = false := beq_false_of_ne (by omega)
    have hi1 : (i.val == 1) = false := beq_false_of_ne (by omega)
    have hi2 : (i.val == 2) = false := beq_false_of_ne (by omega)
    simp only [hni3, decide_false, Bool.false_and, hi0, hi1, hi2, Bool.false_eq_true, ↓reduceIte]
    by_cases hqi : q = i
    · subst hqi; rw [beq_self_eq_true]; simp [hi]
    · have hne' : (i.val == q.val) = false := beq_false_of_ne (fun h => hqi (Fin.ext h.symm))
      rw [hne']; simp [hqi]
  have hentry_col_ge3 : ∀ (s : Fin N) (i j : Fin d) (hi : i.val < 3), j.val ≥ 3 ->
      Many s i j = M4 (zetaCh j) s ⟨i.val, by omega⟩ ⟨3, by decide⟩ := by
    intro s i j hi hj
    dsimp only [Many, M4]; unfold multiChanInvMatTowerAnyDC39 multiChanInvMat4DC39; dsimp only
    have hnj3 : ¬ (j.val < 3) := by omega
    simp only [hnj3, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2) with h0 | h1 | h2
    · simp [h0, hj]
    · simp [h1, hj]
    · simp [h2, hj]
  have hsum4 : ∀ f : Fin 4 -> Nat,
      natSumFin 4 f = f ⟨0, by decide⟩ + f ⟨1, by decide⟩ + f ⟨2, by decide⟩ + f ⟨3, by decide⟩ := by
    intro f
    change ((((0 + f ⟨0, by decide⟩) + f ⟨1, by decide⟩) + f ⟨2, by decide⟩) + f ⟨3, by decide⟩) = _
    omega
  induction w with
  | nil =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i j hi hj
      change natMatId d i j = natMatId 4 ⟨i.val, _⟩ ⟨j.val, _⟩
      unfold natMatId; dsimp
    · intro i j hi hj
      change natMatId d i j = natMatId 4 ⟨i.val, _⟩ ⟨3, _⟩
      unfold natMatId; dsimp only
      rw [ite_false_of_w10 (by omega) 1 0, ite_false_of_w10 (by omega) 1 0]
    · intro i hi
      change natMatId d i i = natMatId 4 ⟨3, _⟩ ⟨3, _⟩
      unfold natMatId; dsimp only; simp
    · intro i j _ hij
      change natMatId d i j = 0
      unfold natMatId
      exact ite_false_of_w10 (fun h => hij (Fin.ext h)) 1 0
  | cons s rest ih =>
    rcases ih with ⟨ih_lt, ih_col, ih_diag, ih_off⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i j hi hj
      change natSumFin d (fun q => Many s i q * evalFinWordMat N d Many rest q j) =
        natSumFin 4 (fun q => M4 0 s ⟨i.val, _⟩ q * evalFinWordMat N 4 (M4 0) rest q ⟨j.val, _⟩)
      rw [natSumFin_split3_w19 d hd, hsum4]
      have htail0 : natSumFin d (fun q => if q.val ≥ 3 then Many s i q * evalFinWordMat N d Many rest q j else 0) = 0 :=
        natSumFin_zero_w19 d _ (fun q => by
          by_cases hq : q.val ≥ 3
          · rw [ite_true_of_w10 hq, ih_off q j hq (fun heq => by subst heq; omega), Nat.mul_zero]
          · rw [ite_false_of_w10 hq])
      have h4_3 : evalFinWordMat N 4 (M4 0) rest ⟨3, by decide⟩ ⟨j.val, by omega⟩ = 0 := by
        have hm4_30 : ∀ xs : List (Fin N), ∀ c : Fin 4, c.val < 3 ->
            evalFinWordMat N 4 (M4 0) xs ⟨3, by decide⟩ c = 0 := by
          intro xs; induction xs with
          | nil => intro c hc; unfold evalFinWordMat natMatId; dsimp only; exact ite_false_of_w10 (by omega) 1 0
          | cons s' tl' ih4 =>
            intro c hc
            change natSumFin 4 (fun q => M4 0 s' ⟨3, by decide⟩ q * evalFinWordMat N 4 (M4 0) tl' q c) = 0
            rw [hsum4]
            have z0 : M4 0 s' ⟨3, by decide⟩ ⟨0, by decide⟩ = 0 := by dsimp only [M4, multiChanInvMat4DC39]; simp
            have z1 : M4 0 s' ⟨3, by decide⟩ ⟨1, by decide⟩ = 0 := by dsimp only [M4, multiChanInvMat4DC39]; simp
            have z2 : M4 0 s' ⟨3, by decide⟩ ⟨2, by decide⟩ = 0 := by dsimp only [M4, multiChanInvMat4DC39]; simp
            rw [z0, z1, z2, ih4 c hc]; simp
        exact hm4_30 rest ⟨j.val, by omega⟩ hj
      rw [htail0, Nat.add_zero, h4_3, Nat.mul_zero, Nat.add_zero,
          hentry_lt3 s i ⟨0, by omega⟩ hi (by dsimp; omega) 0,
          hentry_lt3 s i ⟨1, by omega⟩ hi (by dsimp; omega) 0,
          hentry_lt3 s i ⟨2, by omega⟩ hi (by dsimp; omega) 0,
          ih_lt ⟨0, by omega⟩ j (by dsimp; omega) hj,
          ih_lt ⟨1, by omega⟩ j (by dsimp; omega) hj,
          ih_lt ⟨2, by omega⟩ j (by dsimp; omega) hj]
    · intro i j hi hj
      change natSumFin d (fun q => Many s i q * evalFinWordMat N d Many rest q j) =
        natSumFin 4 (fun q => M4 (zetaCh j) s ⟨i.val, _⟩ q * evalFinWordMat N 4 (M4 (zetaCh j)) rest q ⟨3, _⟩)
      rw [natSumFin_split3_w19 d hd, hsum4]
      have htail_j : natSumFin d (fun q => if q.val ≥ 3 then Many s i q * evalFinWordMat N d Many rest q j else 0) =
          Many s i j * evalFinWordMat N d Many rest j j := by
        have hsingle : ∀ n : Nat, j.val < n -> n ≤ d ->
            natSumPrefix d (fun q => if q.val ≥ 3 then Many s i q * evalFinWordMat N d Many rest q j else 0) n =
              Many s i j * evalFinWordMat N d Many rest j j := by
          intro n; induction n with
          | zero => intro hlt _; omega
          | succ n' ihn =>
            intro hlt hle
            have hn_lt : n' < d := hle
            unfold natSumPrefix; simp only [hn_lt, dite_true]
            by_cases heq : j.val = n'
            · have hj_eq : j = ⟨n', hn_lt⟩ := Fin.ext heq
              subst hj_eq
              have hz : natSumPrefix d (fun q =>
                  if q.val ≥ 3 then Many s i q * evalFinWordMat N d Many rest q ⟨n', hn_lt⟩ else 0) n' = 0 := by
                have h0 : ∀ m : Nat, m ≤ n' ->
                    natSumPrefix d (fun q =>
                      if q.val ≥ 3 then Many s i q * evalFinWordMat N d Many rest q ⟨n', hn_lt⟩ else 0) m = 0 := by
                  intro m; induction m with
                  | zero => intros; rfl
                  | succ m' ihm =>
                    intro hm'
                    have hm_lt : m' < d := by omega
                    unfold natSumPrefix; simp only [hm_lt, dite_true, ihm (by omega), Nat.zero_add]
                    by_cases hge3 : m' ≥ 3
                    · simp only [hge3, ite_true]
                      rw [ih_off ⟨m', hm_lt⟩ ⟨n', hn_lt⟩ hge3 (fun h => by have := congrArg Fin.val h; dsimp at this; omega),
                          Nat.mul_zero]
                    · simp only [hge3, ite_false]
                exact h0 n' (Nat.le_refl n')
              rw [hz, Nat.zero_add, ite_true_of_w10 hj]
            · rw [ihn (by omega) (by omega)]
              by_cases hge3 : n' ≥ 3
              · simp only [hge3, ite_true]
                rw [ih_off ⟨n', hn_lt⟩ j hge3 (fun h => heq (congrArg Fin.val h.symm)), Nat.mul_zero, Nat.add_zero]
              · simp only [hge3, ite_false, Nat.add_zero]
        exact hsingle d j.isLt (Nat.le_refl d)
      have hm4_diag_indep : ∀ (z : Nat) (xs : List (Fin N)),
          evalFinWordMat N 4 (M4 z) xs ⟨3, by decide⟩ ⟨3, by decide⟩ =
            evalFinWordMat N 4 (M4 0) xs ⟨3, by decide⟩ ⟨3, by decide⟩ := by
        intro z xs; induction xs with
        | nil => rfl
        | cons s' tl' ihz =>
          change natSumFin 4 (fun q => M4 z s' ⟨3, by decide⟩ q * evalFinWordMat N 4 (M4 z) tl' q ⟨3, by decide⟩) =
            natSumFin 4 (fun q => M4 0 s' ⟨3, by decide⟩ q * evalFinWordMat N 4 (M4 0) tl' q ⟨3, by decide⟩)
          rw [hsum4, hsum4]
          have z0 : ∀ z', M4 z' s' ⟨3, by decide⟩ ⟨0, by decide⟩ = 0 := fun _ => by dsimp only [M4, multiChanInvMat4DC39]; simp
          have z1 : ∀ z', M4 z' s' ⟨3, by decide⟩ ⟨1, by decide⟩ = 0 := fun _ => by dsimp only [M4, multiChanInvMat4DC39]; simp
          have z2 : ∀ z', M4 z' s' ⟨3, by decide⟩ ⟨2, by decide⟩ = 0 := fun _ => by dsimp only [M4, multiChanInvMat4DC39]; simp
          have z3 : M4 z s' ⟨3, by decide⟩ ⟨3, by decide⟩ = M4 0 s' ⟨3, by decide⟩ ⟨3, by decide⟩ := rfl
          rw [z0, z0, z1, z1, z2, z2, z3, ihz]; simp
      rw [htail_j, ih_diag j hj, ← hm4_diag_indep (zetaCh j) rest,
          hentry_col_ge3 s i j hi hj,
          hentry_lt3 s i ⟨0, by omega⟩ hi (by dsimp; omega) (zetaCh j),
          hentry_lt3 s i ⟨1, by omega⟩ hi (by dsimp; omega) (zetaCh j),
          hentry_lt3 s i ⟨2, by omega⟩ hi (by dsimp; omega) (zetaCh j),
          ih_col ⟨0, by omega⟩ j (by dsimp; omega) hj,
          ih_col ⟨1, by omega⟩ j (by dsimp; omega) hj,
          ih_col ⟨2, by omega⟩ j (by dsimp; omega) hj]
    · intro i hi
      change natSumFin d (fun q => Many s i q * evalFinWordMat N d Many rest q i) =
        natSumFin 4 (fun q => M4 0 s ⟨3, _⟩ q * evalFinWordMat N 4 (M4 0) rest q ⟨3, _⟩)
      rw [hsum4]
      have z0 : M4 0 s ⟨3, by decide⟩ ⟨0, by decide⟩ = 0 := by dsimp only [M4, multiChanInvMat4DC39]; simp
      have z1 : M4 0 s ⟨3, by decide⟩ ⟨1, by decide⟩ = 0 := by dsimp only [M4, multiChanInvMat4DC39]; simp
      have z2 : M4 0 s ⟨3, by decide⟩ ⟨2, by decide⟩ = 0 := by dsimp only [M4, multiChanInvMat4DC39]; simp
      have z3 : M4 (zetaCh i) s ⟨3, by decide⟩ ⟨3, by decide⟩ = M4 0 s ⟨3, by decide⟩ ⟨3, by decide⟩ := rfl
      rw [z0, z1, z2]; simp only [Nat.zero_mul, Nat.zero_add]
      have hsingle : ∀ n : Nat, i.val < n -> n ≤ d ->
          natSumPrefix d (fun q => Many s i q * evalFinWordMat N d Many rest q i) n =
            M4 0 s ⟨3, by decide⟩ ⟨3, by decide⟩ * evalFinWordMat N 4 (M4 0) rest ⟨3, by decide⟩ ⟨3, by decide⟩ := by
        intro n; induction n with
        | zero => intro hlt _; omega
        | succ n' ihn =>
          intro hlt hle
          have hn_lt : n' < d := hle
          unfold natSumPrefix; simp only [hn_lt, dite_true]
          by_cases heq : i.val = n'
          · have hi_eq : i = ⟨n', hn_lt⟩ := Fin.ext heq
            subst hi_eq
            have hz : natSumPrefix d (fun q => Many s ⟨n', hn_lt⟩ q * evalFinWordMat N d Many rest q ⟨n', hn_lt⟩) n' = 0 := by
              have h0 : ∀ m : Nat, m ≤ n' ->
                  natSumPrefix d (fun q => Many s ⟨n', hn_lt⟩ q * evalFinWordMat N d Many rest q ⟨n', hn_lt⟩) m = 0 := by
                intro m; induction m with
                | zero => intros; rfl
                | succ m' ihm =>
                  intro hm'; have hm_lt : m' < d := by omega
                  unfold natSumPrefix; simp only [hm_lt, dite_true, ihm (by omega), Nat.zero_add]
                  rw [hentry_ge3_row s ⟨n', hn_lt⟩ ⟨m', hm_lt⟩ hi,
                      ite_false_of_w10 (fun h => by have := congrArg Fin.val h; dsimp at this; omega), Nat.zero_mul]
              exact h0 n' (Nat.le_refl n')
            rw [hz, Nat.zero_add, hentry_ge3_row s _ _ hi, ite_true_of_w10 rfl, z3, ih_diag _ hi]
          · rw [ihn (by omega) (by omega), hentry_ge3_row s i ⟨n', hn_lt⟩ hi,
                ite_false_of_w10 (fun h => heq (congrArg Fin.val h.symm)), Nat.zero_mul, Nat.add_zero]
      exact hsingle d i.isLt (Nat.le_refl d)
    · intro i j hi hij
      change natSumFin d (fun q => Many s i q * evalFinWordMat N d Many rest q j) = 0
      exact natSumFin_zero_w19 d _ (fun q => by
        rw [hentry_ge3_row s i q hi]
        by_cases hqi : q = i
        · subst hqi; rw [ite_true_of_w10 rfl, ih_off q j hi hij, Nat.mul_zero]
        · rw [ite_false_of_w10 hqi, Nat.zero_mul])

private theorem anyD_basisVec_eq_4d_w19 (N d : Nat) (hd : d ≥ 4) (proj : Fin N -> Fin 42)
    (k a b g de e : Nat) (zetaCh : Fin d -> Nat) (s0 : Fin N) (j0 : Fin d) :
    let Many := fun s => multiChanInvMatTowerAnyDC39 d k a b g de e zetaCh (proj s)
    let M4 := fun z s => multiChanInvMat4DC39 k a b g de e z (proj s)
    let bAny := fun (s : Fin N) (j : Fin d) => if s.val == s0.val && j.val == j0.val then 1 else 0
    ∀ w : List (Fin N),
      (∀ hj0 : j0.val < 3,
        (∀ (i : Fin d) (hi : i.val < 3),
          evalFinWordVec N d Many bAny w i =
            evalFinWordVec N 4 (M4 0) (basisVec4D N s0 ⟨j0.val, by omega⟩) w ⟨i.val, by omega⟩) ∧
        (∀ (i : Fin d), i.val ≥ 3 -> evalFinWordVec N d Many bAny w i = 0)) ∧
      (j0.val ≥ 3 ->
        (∀ (i : Fin d) (hi : i.val < 3),
          evalFinWordVec N d Many bAny w i =
            evalFinWordVec N 4 (M4 (zetaCh j0)) (basisVec4D N s0 ⟨3, by decide⟩) w ⟨i.val, by omega⟩) ∧
        evalFinWordVec N d Many bAny w j0 =
          evalFinWordVec N 4 (M4 (zetaCh j0)) (basisVec4D N s0 ⟨3, by decide⟩) w ⟨3, by decide⟩ ∧
        (∀ (i : Fin d), i.val ≥ 3 -> i ≠ j0 -> evalFinWordVec N d Many bAny w i = 0)) := by
  intro Many M4 bAny w
  have hentry_lt3 : ∀ (s : Fin N) (i j : Fin d) (hi : i.val < 3) (hj : j.val < 3) (z : Nat),
      Many s i j = M4 z s ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ := by
    intro s i j hi hj z
    dsimp [Many, M4, multiChanInvMatTowerAnyDC39]
    have hb : (decide (i.val < 3) && decide (j.val < 3)) = true := by simp [hi, hj]
    rw [hb]; simp only [↓reduceIte, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
    unfold multiChanInvMat4DC39; dsimp only
    rcases (by omega : j.val = 0 ∨ j.val = 1 ∨ j.val = 2) with hj0 | hj1 | hj2 <;>
    rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2) with hi0 | hi1 | hi2 <;>
    simp_all
  have hentry_ge3_row : ∀ (s : Fin N) (i q : Fin d), i.val ≥ 3 ->
      Many s i q = if q = i then M4 (zetaCh q) s ⟨3, by decide⟩ ⟨3, by decide⟩ else 0 := by
    intro s i q hi
    dsimp only [Many, M4]; unfold multiChanInvMatTowerAnyDC39 multiChanInvMat4DC39; dsimp only
    have hni3 : ¬ (i.val < 3) := by omega
    have hi0 : (i.val == 0) = false := beq_false_of_ne (by omega)
    have hi1 : (i.val == 1) = false := beq_false_of_ne (by omega)
    have hi2 : (i.val == 2) = false := beq_false_of_ne (by omega)
    simp only [hni3, decide_false, Bool.false_and, hi0, hi1, hi2, Bool.false_eq_true, ↓reduceIte]
    by_cases hqi : q = i
    · subst hqi; rw [beq_self_eq_true]; simp [hi]
    · have hne' : (i.val == q.val) = false := beq_false_of_ne (fun h => hqi (Fin.ext h.symm))
      rw [hne']; simp [hqi]
  have hentry_col_ge3 : ∀ (s : Fin N) (i j : Fin d) (hi : i.val < 3), j.val ≥ 3 ->
      Many s i j = M4 (zetaCh j) s ⟨i.val, by omega⟩ ⟨3, by decide⟩ := by
    intro s i j hi hj
    dsimp only [Many, M4]; unfold multiChanInvMatTowerAnyDC39 multiChanInvMat4DC39; dsimp only
    have hnj3 : ¬ (j.val < 3) := by omega
    simp only [hnj3, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2) with h0 | h1 | h2
    · simp [h0, hj]
    · simp [h1, hj]
    · simp [h2, hj]
  have hsum4 : ∀ f : Fin 4 -> Nat,
      natSumFin 4 f = f ⟨0, by decide⟩ + f ⟨1, by decide⟩ + f ⟨2, by decide⟩ + f ⟨3, by decide⟩ := by
    intro f
    change ((((0 + f ⟨0, by decide⟩) + f ⟨1, by decide⟩) + f ⟨2, by decide⟩) + f ⟨3, by decide⟩) = _
    omega
  induction w with
  | nil =>
    exact ⟨fun _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩,
           fun _ => ⟨fun _ _ => rfl, rfl, fun _ _ _ => rfl⟩⟩
  | cons s rest ih =>
    rcases ih with ⟨ih_lt3, ih_ge3⟩
    refine ⟨?_, ?_⟩
    · intro hj0
      rcases ih_lt3 hj0 with ⟨ih_i_lt, ih_i_ge⟩
      have hm4_v3_zero : ∀ xs : List (Fin N),
          evalFinWordVec N 4 (M4 0) (basisVec4D N s0 ⟨j0.val, by omega⟩) xs ⟨3, by decide⟩ = 0 := by
        intro xs; induction xs with
        | nil => rfl
        | cons s' tl' ih4 =>
          change basisVec4D N s0 ⟨j0.val, by omega⟩ s' ⟨3, by decide⟩ +
            natSumFin 4 (fun q => M4 0 s' ⟨3, by decide⟩ q * evalFinWordVec N 4 (M4 0) _ tl' q) = 0
          rw [hsum4]
          have hb0 : basisVec4D N s0 ⟨j0.val, by omega⟩ s' ⟨3, by decide⟩ = 0 := by
            unfold basisVec4D; dsimp only
            have hne : (3 == j0.val) = false := beq_false_of_ne (by omega)
            rw [hne, Bool.and_false]; rfl
          have z0 : M4 0 s' ⟨3, by decide⟩ ⟨0, by decide⟩ = 0 := by dsimp only [M4, multiChanInvMat4DC39]; simp
          have z1 : M4 0 s' ⟨3, by decide⟩ ⟨1, by decide⟩ = 0 := by dsimp only [M4, multiChanInvMat4DC39]; simp
          have z2 : M4 0 s' ⟨3, by decide⟩ ⟨2, by decide⟩ = 0 := by dsimp only [M4, multiChanInvMat4DC39]; simp
          rw [hb0, z0, z1, z2, ih4]; simp
      refine ⟨?_, ?_⟩
      · intro i hi
        change bAny s i + natSumFin d (fun q => Many s i q * evalFinWordVec N d Many bAny rest q) =
          basisVec4D N s0 ⟨j0.val, by omega⟩ s ⟨i.val, by omega⟩ +
            natSumFin 4 (fun q => M4 0 s ⟨i.val, by omega⟩ q * evalFinWordVec N 4 (M4 0) _ rest q)
        rw [natSumFin_split3_w19 d hd, hsum4, hm4_v3_zero rest]
        have htail0 : natSumFin d (fun q => if q.val ≥ 3 then Many s i q * evalFinWordVec N d Many bAny rest q else 0) = 0 :=
          natSumFin_zero_w19 d _ (fun q => by
            by_cases hq : q.val ≥ 3
            · rw [ite_true_of_w10 hq, ih_i_ge q hq, Nat.mul_zero]
            · rw [ite_false_of_w10 hq])
        rw [htail0, Nat.add_zero, Nat.mul_zero, Nat.add_zero,
            hentry_lt3 s i ⟨0, by omega⟩ hi (by dsimp; omega) 0,
            hentry_lt3 s i ⟨1, by omega⟩ hi (by dsimp; omega) 0,
            hentry_lt3 s i ⟨2, by omega⟩ hi (by dsimp; omega) 0,
            ih_i_lt ⟨0, by omega⟩ (by dsimp; omega),
            ih_i_lt ⟨1, by omega⟩ (by dsimp; omega),
            ih_i_lt ⟨2, by omega⟩ (by dsimp; omega)]
        rfl
      · intro i hi
        change bAny s i + natSumFin d (fun q => Many s i q * evalFinWordVec N d Many bAny rest q) = 0
        have hb0 : bAny s i = 0 := by
          dsimp [bAny]; rw [beq_false_of_ne (by omega : i.val ≠ j0.val), Bool.and_false]; rfl
        rw [hb0, Nat.zero_add]
        exact natSumFin_zero_w19 d _ (fun q => by
          rw [hentry_ge3_row s i q hi]
          by_cases hqi : q = i
          · subst hqi; rw [ite_true_of_w10 rfl, ih_i_ge q hi, Nat.mul_zero]
          · rw [ite_false_of_w10 hqi, Nat.zero_mul])
    · intro hj0
      rcases ih_ge3 hj0 with ⟨ih_i_lt, ih_j0, ih_off⟩
      refine ⟨?_, ?_, ?_⟩
      · intro i hi
        change bAny s i + natSumFin d (fun q => Many s i q * evalFinWordVec N d Many bAny rest q) =
          basisVec4D N s0 ⟨3, by decide⟩ s ⟨i.val, by omega⟩ +
            natSumFin 4 (fun q => M4 (zetaCh j0) s ⟨i.val, by omega⟩ q * evalFinWordVec N 4 (M4 (zetaCh j0)) _ rest q)
        have hb_l : bAny s i = 0 := by
          dsimp only [bAny]; rw [beq_false_of_ne (by omega : i.val ≠ j0.val), Bool.and_false]; rfl
        have hb_r : basisVec4D N s0 ⟨3, by decide⟩ s ⟨i.val, by omega⟩ = 0 := by
          unfold basisVec4D; dsimp only; rw [beq_false_of_ne (by omega : i.val ≠ 3), Bool.and_false]; rfl
        rw [hb_l, hb_r, Nat.zero_add, Nat.zero_add, natSumFin_split3_w19 d hd, hsum4]
        have htail_j0 : natSumFin d (fun q => if q.val ≥ 3 then Many s i q * evalFinWordVec N d Many bAny rest q else 0) =
            Many s i j0 * evalFinWordVec N d Many bAny rest j0 := by
          have hsingle : ∀ n : Nat, j0.val < n -> n ≤ d ->
              natSumPrefix d (fun q => if q.val ≥ 3 then Many s i q * evalFinWordVec N d Many bAny rest q else 0) n =
                Many s i j0 * evalFinWordVec N d Many bAny rest j0 := by
            intro n; induction n with
            | zero => intro hlt _; omega
            | succ n' ihn =>
              intro hlt hle; have hn_lt : n' < d := hle
              unfold natSumPrefix; simp only [hn_lt, dite_true]
              by_cases heq : j0.val = n'
              · have hj_eq : j0 = ⟨n', hn_lt⟩ := Fin.ext heq; subst hj_eq
                have hz : natSumPrefix d (fun q => if q.val ≥ 3 then Many s i q * evalFinWordVec N d Many bAny rest q else 0) n' = 0 := by
                  have h0 : ∀ m : Nat, m ≤ n' ->
                      natSumPrefix d (fun q => if q.val ≥ 3 then Many s i q * evalFinWordVec N d Many bAny rest q else 0) m = 0 := by
                    intro m; induction m with
                    | zero => intros; rfl
                    | succ m' ihm =>
                      intro hm'; have hm_lt : m' < d := by omega
                      unfold natSumPrefix; simp only [hm_lt, dite_true, ihm (by omega), Nat.zero_add]
                      by_cases hge3 : m' ≥ 3
                      · simp only [hge3, ite_true]
                        rw [ih_off ⟨m', hm_lt⟩ hge3 (fun h => by have := congrArg Fin.val h; dsimp at this; omega), Nat.mul_zero]
                      · simp only [hge3, ite_false]
                  exact h0 n' (Nat.le_refl n')
                rw [hz, Nat.zero_add, ite_true_of_w10 hj0]
              · rw [ihn (by omega) (by omega)]
                by_cases hge3 : n' ≥ 3
                · simp only [hge3, ite_true]
                  rw [ih_off ⟨n', hn_lt⟩ hge3 (fun h => heq (congrArg Fin.val h.symm)), Nat.mul_zero, Nat.add_zero]
                · simp only [hge3, ite_false, Nat.add_zero]
          exact hsingle d j0.isLt (Nat.le_refl d)
        rw [htail_j0, hentry_col_ge3 s i j0 hi hj0, ih_j0,
            hentry_lt3 s i ⟨0, by omega⟩ hi (by dsimp; omega) (zetaCh j0),
            hentry_lt3 s i ⟨1, by omega⟩ hi (by dsimp; omega) (zetaCh j0),
            hentry_lt3 s i ⟨2, by omega⟩ hi (by dsimp; omega) (zetaCh j0),
            ih_i_lt ⟨0, by omega⟩ (by dsimp; omega),
            ih_i_lt ⟨1, by omega⟩ (by dsimp; omega),
            ih_i_lt ⟨2, by omega⟩ (by dsimp; omega)]
      · change bAny s j0 + natSumFin d (fun q => Many s j0 q * evalFinWordVec N d Many bAny rest q) =
          basisVec4D N s0 ⟨3, by decide⟩ s ⟨3, by decide⟩ +
            natSumFin 4 (fun q => M4 (zetaCh j0) s ⟨3, by decide⟩ q * evalFinWordVec N 4 (M4 (zetaCh j0)) _ rest q)
        have hb_eq : bAny s j0 = basisVec4D N s0 ⟨3, by decide⟩ s ⟨3, by decide⟩ := by
          unfold basisVec4D; dsimp only [bAny]; simp
        rw [hb_eq, hsum4]
        have z0 : M4 (zetaCh j0) s ⟨3, by decide⟩ ⟨0, by decide⟩ = 0 := by dsimp only [M4, multiChanInvMat4DC39]; simp
        have z1 : M4 (zetaCh j0) s ⟨3, by decide⟩ ⟨1, by decide⟩ = 0 := by dsimp only [M4, multiChanInvMat4DC39]; simp
        have z2 : M4 (zetaCh j0) s ⟨3, by decide⟩ ⟨2, by decide⟩ = 0 := by dsimp only [M4, multiChanInvMat4DC39]; simp
        rw [z0, z1, z2]; simp only [Nat.zero_mul, Nat.zero_add]
        have hsingle : ∀ n : Nat, j0.val < n -> n ≤ d ->
            natSumPrefix d (fun q => Many s j0 q * evalFinWordVec N d Many bAny rest q) n =
              M4 (zetaCh j0) s ⟨3, by decide⟩ ⟨3, by decide⟩ *
                evalFinWordVec N 4 (M4 (zetaCh j0)) (basisVec4D N s0 ⟨3, by decide⟩) rest ⟨3, by decide⟩ := by
          intro n; induction n with
          | zero => intro hlt _; omega
          | succ n' ihn =>
            intro hlt hle; have hn_lt : n' < d := hle
            unfold natSumPrefix; simp only [hn_lt, dite_true]
            by_cases heq : j0.val = n'
            · have hj_eq : j0 = ⟨n', hn_lt⟩ := Fin.ext heq; subst hj_eq
              have hz : natSumPrefix d (fun q => Many s ⟨n', hn_lt⟩ q * evalFinWordVec N d Many bAny rest q) n' = 0 := by
                have h0 : ∀ m : Nat, m ≤ n' ->
                    natSumPrefix d (fun q => Many s ⟨n', hn_lt⟩ q * evalFinWordVec N d Many bAny rest q) m = 0 := by
                  intro m; induction m with
                  | zero => intros; rfl
                  | succ m' ihm =>
                    intro hm'; have hm_lt : m' < d := by omega
                    unfold natSumPrefix; simp only [hm_lt, dite_true, ihm (by omega), Nat.zero_add]
                    rw [hentry_ge3_row s ⟨n', hn_lt⟩ ⟨m', hm_lt⟩ hj0,
                        ite_false_of_w10 (fun h => by have := congrArg Fin.val h; dsimp at this; omega), Nat.zero_mul]
                exact h0 n' (Nat.le_refl n')
              rw [hz, Nat.zero_add, hentry_ge3_row s _ _ hj0, ite_true_of_w10 rfl, ih_j0]
            · rw [ihn (by omega) (by omega), hentry_ge3_row s j0 ⟨n', hn_lt⟩ hj0,
                  ite_false_of_w10 (fun h => heq (congrArg Fin.val h.symm)), Nat.zero_mul, Nat.add_zero]
        unfold natSumFin
        rw [hsingle d j0.isLt (Nat.le_refl d)]
      · intro i hi hij0
        change bAny s i + natSumFin d (fun q => Many s i q * evalFinWordVec N d Many bAny rest q) = 0
        have hb0 : bAny s i = 0 := by
          dsimp [bAny]; rw [beq_false_of_ne (fun h => hij0 (Fin.ext h)), Bool.and_false]; rfl
        rw [hb0, Nat.zero_add]
        exact natSumFin_zero_w19 d _ (fun q => by
          rw [hentry_ge3_row s i q hi]
          by_cases hqi : q = i
          · subst hqi; rw [ite_true_of_w10 rfl, ih_off q hi hij0, Nat.mul_zero]
          · rw [ite_false_of_w10 hqi, Nat.zero_mul])

/--
  Theorem W19.1b (`simultaneous_d3_invertible_and_d4_multichannel_farkas_locks`,
  `zero custom axioms`):
  Infinite 6-Parameter `d = 3` (`3 × 3`) Invertible Positive-Trace Lower-Right Cones
  (`invPosTraceMat3DC39` & `invPosTraceMat3DC78`, `det(D_{29,31,35}) = η ≥ 1`, `tr(D_{29,31,35}) = η + 1 ≥ 2`,
  Strictly Orienting **`39/39` (`100%`)** of `c39` and **`78/78` (`100%`)** of `c78`, Escaping Wave 18's
  3-Channel Farkas Syzygy by `+6`), Infinite 7-Parameter `d = 4` (`4 × 4`) 4-Channel Invertible Cones
  (`multiChanInvMat4DC39` & `multiChanInvMat4DC78`, **`39/39` & `78/78` (`100%`)**, Escaping 3-Channel
  Farkas by `+1`), AND All-Dimension (`∀ d ≥ 4`) Multi-Channel Cross-Coupled Invertible Cones
  (`multiChanInvMatTowerAnyDC39` & `multiChanInvMatTowerAnyDC78`), Simultaneously Locked at `0` Strict
  `v_0` Drops Across `c39` & `c78` via Multi-Channel `(μ_0, β * μ_1, α * μ_2, ζ * μ_3)` Farkas Syzygies
  (`Branch P4.3`, witness `ZPOS_C39_4D_MULTICHAN_INV_AND_EXPANDING_B_ESCAPE`, `W19_H1`).
-/
theorem simultaneous_d3_invertible_and_d4_multichannel_farkas_locks :
    let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
    let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
    (countStrictMat3DRules 42 (invPosTraceMat3DC39 2 1 1 1 1 1) c39 = 39 ∧
     countStrictMat3DRules 84 (invPosTraceMat3DC78 2 1 1 1 1 1) c78 = 78 ∧
     countStrictMat4DRules 42 (multiChanInvMat4DC39 2 1 1 1 1 1 1) c39 = 39 ∧
     countStrictMat4DRules 84 (multiChanInvMat4DC78 2 1 1 1 1 1 1) c78 = 78 ∧
     (∀ k a b g d e : Nat,
       let m35 := invPosTraceMat3DC39 k a b g d e ⟨35, by decide⟩
       let m29 := invPosTraceMat3DC39 k a b g d e ⟨29, by decide⟩
       m35 ⟨1, by decide⟩ ⟨1, by decide⟩ * m35 ⟨2, by decide⟩ ⟨2, by decide⟩ -
         m35 ⟨1, by decide⟩ ⟨2, by decide⟩ * m35 ⟨2, by decide⟩ ⟨1, by decide⟩ = e ∧
       m35 ⟨1, by decide⟩ ⟨1, by decide⟩ + m35 ⟨2, by decide⟩ ⟨2, by decide⟩ = e + 1 ∧
       m29 ⟨1, by decide⟩ ⟨1, by decide⟩ * m29 ⟨2, by decide⟩ ⟨2, by decide⟩ -
         m29 ⟨1, by decide⟩ ⟨2, by decide⟩ * m29 ⟨2, by decide⟩ ⟨1, by decide⟩ = e ∧
       m29 ⟨1, by decide⟩ ⟨1, by decide⟩ + m29 ⟨2, by decide⟩ ⟨2, by decide⟩ = 1 + e) ∧
     farkasInv3DVecLhsN 42 id farkasMu0CoupledC39 farkasMu1BlockNilp3DC39 farkasMu1BiBTRC39
       2 1 1 1 1 1 (basisVec3D 42 ⟨14, by decide⟩ ⟨1, by decide⟩) c39 -
     farkasInv3DVecRhsN 42 id farkasMu0CoupledC39 farkasMu1BlockNilp3DC39 farkasMu1BiBTRC39
       2 1 1 1 1 1 (basisVec3D 42 ⟨14, by decide⟩ ⟨1, by decide⟩) c39 = 6 ∧
     farkasInv4DVecLhsN 42 id farkasMu0CoupledC39 farkasMu1InvW19C39 farkasMu2InvW19C39 (fun _ => 0)
       2 1 1 1 1 1 1 (basisVec4D 42 ⟨23, by decide⟩ ⟨3, by decide⟩) c39 -
     farkasInv4DVecRhsN 42 id farkasMu0CoupledC39 farkasMu1InvW19C39 farkasMu2InvW19C39 (fun _ => 0)
       2 1 1 1 1 1 1 (basisVec4D 42 ⟨23, by decide⟩ ⟨3, by decide⟩) c39 = 1) ∧
    (∀ (k alpha beta gamma delta eta : Nat),
      k ≥ 2 -> alpha ≥ 1 -> beta ≥ 1 -> gamma ≥ 1 -> delta ≥ 1 -> eta ≥ 1 ->
      (∀ r ∈ c39, ∀ i j : Fin 3,
        evalFinWordMat 42 3 (invPosTraceMat3DC39 k alpha beta gamma delta eta) r.1 i j ≥
          evalFinWordMat 42 3 (invPosTraceMat3DC39 k alpha beta gamma delta eta) r.2 i j) ∧
      (∀ v : Fin 42 -> Fin 3 -> Nat,
        (∀ r ∈ c39, ∀ i : Fin 3,
          evalFinWordVec 42 3 (invPosTraceMat3DC39 k alpha beta gamma delta eta) v r.1 i ≥
            evalFinWordVec 42 3 (invPosTraceMat3DC39 k alpha beta gamma delta eta) v r.2 i) ->
        ∀ r ∈ c39,
          evalFinWordVec 42 3 (invPosTraceMat3DC39 k alpha beta gamma delta eta) v r.1 ⟨0, by decide⟩ =
            evalFinWordVec 42 3 (invPosTraceMat3DC39 k alpha beta gamma delta eta) v r.2 ⟨0, by decide⟩) ∧
      (∀ r ∈ c78, ∀ i j : Fin 3,
        evalFinWordMat 84 3 (invPosTraceMat3DC78 k alpha beta gamma delta eta) r.1 i j ≥
          evalFinWordMat 84 3 (invPosTraceMat3DC78 k alpha beta gamma delta eta) r.2 i j) ∧
      (∀ v : Fin 84 -> Fin 3 -> Nat,
        (∀ r ∈ c78, ∀ i : Fin 3,
          evalFinWordVec 84 3 (invPosTraceMat3DC78 k alpha beta gamma delta eta) v r.1 i ≥
            evalFinWordVec 84 3 (invPosTraceMat3DC78 k alpha beta gamma delta eta) v r.2 i) ->
        ∀ r ∈ c78,
          evalFinWordVec 84 3 (invPosTraceMat3DC78 k alpha beta gamma delta eta) v r.1 ⟨0, by decide⟩ =
            evalFinWordVec 84 3 (invPosTraceMat3DC78 k alpha beta gamma delta eta) v r.2 ⟨0, by decide⟩)) ∧
    (∀ (k alpha beta gamma delta eta zeta : Nat),
      k ≥ 2 -> alpha ≥ 1 -> beta ≥ 1 -> gamma ≥ 1 -> delta ≥ 1 -> eta ≥ 1 -> zeta ≥ 1 ->
      (∀ r ∈ c39, ∀ i j : Fin 4,
        evalFinWordMat 42 4 (multiChanInvMat4DC39 k alpha beta gamma delta eta zeta) r.1 i j ≥
          evalFinWordMat 42 4 (multiChanInvMat4DC39 k alpha beta gamma delta eta zeta) r.2 i j) ∧
      (∀ v : Fin 42 -> Fin 4 -> Nat,
        (∀ r ∈ c39, ∀ i : Fin 4,
          evalFinWordVec 42 4 (multiChanInvMat4DC39 k alpha beta gamma delta eta zeta) v r.1 i ≥
            evalFinWordVec 42 4 (multiChanInvMat4DC39 k alpha beta gamma delta eta zeta) v r.2 i) ->
        ∀ r ∈ c39,
          evalFinWordVec 42 4 (multiChanInvMat4DC39 k alpha beta gamma delta eta zeta) v r.1 ⟨0, by decide⟩ =
            evalFinWordVec 42 4 (multiChanInvMat4DC39 k alpha beta gamma delta eta zeta) v r.2 ⟨0, by decide⟩) ∧
      (∀ r ∈ c78, ∀ i j : Fin 4,
        evalFinWordMat 84 4 (multiChanInvMat4DC78 k alpha beta gamma delta eta zeta) r.1 i j ≥
          evalFinWordMat 84 4 (multiChanInvMat4DC78 k alpha beta gamma delta eta zeta) r.2 i j) ∧
      (∀ v : Fin 84 -> Fin 4 -> Nat,
        (∀ r ∈ c78, ∀ i : Fin 4,
          evalFinWordVec 84 4 (multiChanInvMat4DC78 k alpha beta gamma delta eta zeta) v r.1 i ≥
            evalFinWordVec 84 4 (multiChanInvMat4DC78 k alpha beta gamma delta eta zeta) v r.2 i) ->
        ∀ r ∈ c78,
          evalFinWordVec 84 4 (multiChanInvMat4DC78 k alpha beta gamma delta eta zeta) v r.1 ⟨0, by decide⟩ =
            evalFinWordVec 84 4 (multiChanInvMat4DC78 k alpha beta gamma delta eta zeta) v r.2 ⟨0, by decide⟩)) ∧
    (∀ (d : Nat) (hd : d ≥ 4) (k alpha beta gamma delta eta : Nat) (zetaCh : Fin d -> Nat),
      k ≥ 2 ->
      (∀ r ∈ c39, ∀ i j : Fin d,
        evalFinWordMat 42 d (multiChanInvMatTowerAnyDC39 d k alpha beta gamma delta eta zetaCh) r.1 i j ≥
          evalFinWordMat 42 d (multiChanInvMatTowerAnyDC39 d k alpha beta gamma delta eta zetaCh) r.2 i j) ∧
      (∀ v : Fin 42 -> Fin d -> Nat,
        (∀ r ∈ c39, ∀ i : Fin d,
          evalFinWordVec 42 d (multiChanInvMatTowerAnyDC39 d k alpha beta gamma delta eta zetaCh) v r.1 i ≥
            evalFinWordVec 42 d (multiChanInvMatTowerAnyDC39 d k alpha beta gamma delta eta zetaCh) v r.2 i) ->
        ∀ r ∈ c39,
          evalFinWordVec 42 d (multiChanInvMatTowerAnyDC39 d k alpha beta gamma delta eta zetaCh) v r.1 ⟨0, by omega⟩ =
            evalFinWordVec 42 d (multiChanInvMatTowerAnyDC39 d k alpha beta gamma delta eta zetaCh) v r.2 ⟨0, by omega⟩) ∧
      (∀ r ∈ c78, ∀ i j : Fin d,
        evalFinWordMat 84 d (multiChanInvMatTowerAnyDC78 d k alpha beta gamma delta eta zetaCh) r.1 i j ≥
          evalFinWordMat 84 d (multiChanInvMatTowerAnyDC78 d k alpha beta gamma delta eta zetaCh) r.2 i j) ∧
      (∀ v : Fin 84 -> Fin d -> Nat,
        (∀ r ∈ c78, ∀ i : Fin d,
          evalFinWordVec 84 d (multiChanInvMatTowerAnyDC78 d k alpha beta gamma delta eta zetaCh) v r.1 i ≥
            evalFinWordVec 84 d (multiChanInvMatTowerAnyDC78 d k alpha beta gamma delta eta zetaCh) v r.2 i) ->
        ∀ r ∈ c78,
          evalFinWordVec 84 d (multiChanInvMatTowerAnyDC78 d k alpha beta gamma delta eta zetaCh) v r.1 ⟨0, by omega⟩ =
            evalFinWordVec 84 d (multiChanInvMatTowerAnyDC78 d k alpha beta gamma delta eta zetaCh) v r.2 ⟨0, by omega⟩)) := by
  dsimp only
  rw [c39_eq_fastRules_w19, c78_eq_fastRules_w19]
  rcases inv3d_4d_mat_dom_and_strict_c39_w19 with
    ⟨hdom3, hdom4, hc78_proj, hmu0_39_b, hmu0_78_b, hst3_39, hst4_39⟩
  rcases inv3d_4d_strict_c78_and_escapes_w19 with ⟨hst3_78, hst4_78, hesc3, hesc4⟩
  have hmu0_39 : ∀ r ∈ c39FastRulesW19, farkasMu0CoupledC39 r.1 ≥ 1 :=
    fun r hr => of_decide_eq_true (List.all_eq_true.mp hmu0_39_b r hr)
  have hmu0_78 : ∀ r ∈ c78FastRulesW19, farkasMu0CoupledC78 r.1 ≥ 1 :=
    fun r hr => of_decide_eq_true (List.all_eq_true.mp hmu0_78_b r hr)
  -- Universal `4D` weak matrix orientation & Farkas lock for ALL `k ≥ 2` and `a..z ≥ 0`:
  have h4d_all : ∀ (k a b g de e z : Nat), k ≥ 2 ->
      (∀ r ∈ c39FastRulesW19, ∀ i j : Fin 4,
        evalFinWordMat 42 4 (multiChanInvMat4DC39 k a b g de e z) r.1 i j ≥
          evalFinWordMat 42 4 (multiChanInvMat4DC39 k a b g de e z) r.2 i j) ∧
      (∀ r ∈ c78FastRulesW19, ∀ i j : Fin 4,
        evalFinWordMat 84 4 (multiChanInvMat4DC78 k a b g de e z) r.1 i j ≥
          evalFinWordMat 84 4 (multiChanInvMat4DC78 k a b g de e z) r.2 i j) ∧
      (∀ (s0 : Fin 42) (j0 : Fin 4),
        farkasInv4DVecLhsN 42 id farkasMu0CoupledC39 (fun l => b * farkasMu1InvW19C39 l)
          (fun l => a * farkasMu2InvW19C39 l) (fun l => z * farkasMu3InvW19C39 l)
          k a b g de e z (basisVec4D 42 s0 j0) c39FastRulesW19 ≤
        farkasInv4DVecRhsN 42 id farkasMu0CoupledC39 (fun l => b * farkasMu1InvW19C39 l)
          (fun l => a * farkasMu2InvW19C39 l) (fun l => z * farkasMu3InvW19C39 l)
          k a b g de e z (basisVec4D 42 s0 j0) c39FastRulesW19) ∧
      (∀ (s0 : Fin 84) (j0 : Fin 4),
        farkasInv4DVecLhsN 84 projSym84To42 farkasMu0CoupledC78 (fun l => b * farkasMu1InvW19C78 l)
          (fun l => a * farkasMu2InvW19C78 l) (fun l => z * farkasMu3InvW19C78 l)
          k a b g de e z (basisVec4D 84 s0 j0) c78FastRulesW19 ≤
        farkasInv4DVecRhsN 84 projSym84To42 farkasMu0CoupledC78 (fun l => b * farkasMu1InvW19C78 l)
          (fun l => a * farkasMu2InvW19C78 l) (fun l => z * farkasMu3InvW19C78 l)
          k a b g de e z (basisVec4D 84 s0 j0) c78FastRulesW19) := by
    intro k a b g de e z hk2
    have hk_eq : k = 2 + (k - 2) := by omega
    rw [hk_eq]
    have hw39 := checkSymMatDomW19_sound 42 4 symMultiChanMat4DC39W19 c39FastRulesW19 hdom4
      (k - 2) a b g de e z _ (eval_symMultiChanMat4DC39W19 (k - 2) a b g de e z)
    have hproj84_4 : ∀ (w : List (Fin 84)) (i j : Fin 4),
        evalFinWordMat 84 4 (multiChanInvMat4DC78 (2 + (k - 2)) a b g de e z) w i j =
          evalFinWordMat 42 4 (multiChanInvMat4DC39 (2 + (k - 2)) a b g de e z) (w.map projSym84To42) i j := by
      intro w; induction w with
      | nil => intros; rfl
      | cons s tl ih =>
        intro i j; simp only [List.map_cons]
        change natSumFin 4 (fun q => _ * evalFinWordMat 84 4 _ tl q j) =
          natSumFin 4 (fun q => _ * evalFinWordMat 42 4 _ (tl.map projSym84To42) q j)
        apply congrArg (natSumFin 4); funext q; rw [ih q j]; rfl
    refine ⟨hw39, ?_, ?_, ?_⟩
    · intro r hr i j
      rw [hproj84_4 r.1 i j, hproj84_4 r.2 i j]
      rcases List.any_eq_true.mp (List.all_eq_true.mp hc78_proj r hr) with ⟨r39, hr39, hbeq⟩
      have heq_p := beq_iff_eq.mp hbeq
      have h1 : r.1.map projSym84To42 = r39.1 := congrArg Prod.fst heq_p
      have h2 : r.2.map projSym84To42 = r39.2 := congrArg Prod.snd heq_p
      rw [h1, h2]
      exact hw39 r39 hr39 i j
    · intro s0 j0
      exact unpack_symFarkas4DRange_w19 42 id farkasMu0CoupledC39 farkasMu1InvW19C39
        farkasMu2InvW19C39 farkasMu3InvW19C39 c39FastRulesW19 0 42 inv4d_farkas_c39_cert_w19
        (k - 2) a b g de e z s0 j0 (Nat.zero_le _) s0.isLt
    · intro s0 j0
      by_cases h21 : s0.val < 21
      · exact unpack_symFarkas4DRange_w19 84 projSym84To42 _ _ _ _ c78FastRulesW19 0 21
          inv4d_farkas_c78_q0_w19 (k - 2) a b g de e z s0 j0 (Nat.zero_le _) h21
      · by_cases h42 : s0.val < 42
        · exact unpack_symFarkas4DRange_w19 84 projSym84To42 _ _ _ _ c78FastRulesW19 21 21
            inv4d_farkas_c78_q1_w19 (k - 2) a b g de e z s0 j0 (by omega) h42
        · by_cases h63 : s0.val < 63
          · exact unpack_symFarkas4DRange_w19 84 projSym84To42 _ _ _ _ c78FastRulesW19 42 21
              inv4d_farkas_c78_q2_w19 (k - 2) a b g de e z s0 j0 (by omega) h63
          · exact unpack_symFarkas4DRange_w19 84 projSym84To42 _ _ _ _ c78FastRulesW19 63 21
              inv4d_farkas_c78_q3_w19 (k - 2) a b g de e z s0 j0 (by omega) s0.isLt
  -- Equivalence between `farkasInv3DVec*` / `farkasInv4DVec*` and `genFarkasVec*`:
  have hgen3_eq : ∀ (N : Nat) (proj : Fin N -> Fin 42) (m0 m1 m2 : List (Fin N) -> Nat)
      (k a b g de e : Nat) (v : Fin N -> Fin 3 -> Nat) (rs : List (List (Fin N) × List (Fin N))),
      let wt : Fin 3 -> List (Fin N) -> Nat := fun i l =>
        if i.val == 0 then m0 l else if i.val == 1 then m1 l else m2 l
      genFarkasVecLhsW19 N 3 (fun s => invPosTraceMat3DC39 k a b g de e (proj s)) wt v rs =
        farkasInv3DVecLhsN N proj m0 m1 m2 k a b g de e v rs ∧
      genFarkasVecRhsW19 N 3 (fun s => invPosTraceMat3DC39 k a b g de e (proj s)) wt v rs =
        farkasInv3DVecRhsN N proj m0 m1 m2 k a b g de e v rs := by
    intro N proj m0 m1 m2 k a b g de e v rs
    have h3 : ∀ f : Fin 3 -> Nat, natSumFin 3 f = f ⟨0, by decide⟩ + f ⟨1, by decide⟩ + f ⟨2, by decide⟩ := by
      intro f; change (((0 + f ⟨0, by decide⟩) + f ⟨1, by decide⟩) + f ⟨2, by decide⟩) = _; omega
    induction rs with
    | nil => exact ⟨rfl, rfl⟩
    | cons r0 rtl ih =>
      rcases r0 with ⟨l0, r0_w⟩
      dsimp only [genFarkasVecLhsW19, genFarkasVecRhsW19, farkasInv3DVecLhsN, farkasInv3DVecRhsN]
      rw [h3, h3, ih.1, ih.2]; exact ⟨rfl, rfl⟩
  have hgen4_eq : ∀ (N : Nat) (proj : Fin N -> Fin 42) (m0 m1 m2 m3 : List (Fin N) -> Nat)
      (k a b g de e z : Nat) (v : Fin N -> Fin 4 -> Nat) (rs : List (List (Fin N) × List (Fin N))),
      let wt : Fin 4 -> List (Fin N) -> Nat := fun i l =>
        if i.val == 0 then m0 l else if i.val == 1 then m1 l else if i.val == 2 then m2 l else m3 l
      genFarkasVecLhsW19 N 4 (fun s => multiChanInvMat4DC39 k a b g de e z (proj s)) wt v rs =
        farkasInv4DVecLhsN N proj m0 m1 m2 m3 k a b g de e z v rs ∧
      genFarkasVecRhsW19 N 4 (fun s => multiChanInvMat4DC39 k a b g de e z (proj s)) wt v rs =
        farkasInv4DVecRhsN N proj m0 m1 m2 m3 k a b g de e z v rs := by
    intro N proj m0 m1 m2 m3 k a b g de e z v rs
    have h4 : ∀ f : Fin 4 -> Nat,
        natSumFin 4 f = f ⟨0, by decide⟩ + f ⟨1, by decide⟩ + f ⟨2, by decide⟩ + f ⟨3, by decide⟩ := by
      intro f; change ((((0 + f ⟨0, by decide⟩) + f ⟨1, by decide⟩) + f ⟨2, by decide⟩) + f ⟨3, by decide⟩) = _; omega
    induction rs with
    | nil => exact ⟨rfl, rfl⟩
    | cons r0 rtl ih =>
      rcases r0 with ⟨l0, r0_w⟩
      dsimp only [genFarkasVecLhsW19, genFarkasVecRhsW19, farkasInv4DVecLhsN, farkasInv4DVecRhsN]
      rw [h4, h4, ih.1, ih.2]; exact ⟨rfl, rfl⟩
  refine ⟨⟨hst3_39, hst3_78, hst4_39, hst4_78, ?_, hesc3, hesc4⟩, ?_, ?_, ?_⟩
  · intro k a b g d e
    simp [invPosTraceMat3DC39, isT1InvSymW19, isT2InvSymW19]
  · intro k a b g de e hk2 _ _ _ _ _
    have hk_eq : k = 2 + (k - 2) := by omega
    rw [hk_eq]
    have hw39 := checkSymMatDomW19_sound 42 3 symInvMat3DC39W19 c39FastRulesW19 hdom3
      (k - 2) a b g de e 0 _ (eval_symInvMat3DC39W19 (k - 2) a b g de e 0)
    have hproj84_3 : ∀ (w : List (Fin 84)) (i j : Fin 3),
        evalFinWordMat 84 3 (invPosTraceMat3DC78 (2 + (k - 2)) a b g de e) w i j =
          evalFinWordMat 42 3 (invPosTraceMat3DC39 (2 + (k - 2)) a b g de e) (w.map projSym84To42) i j := by
      intro w; induction w with
      | nil => intros; rfl
      | cons s tl ih =>
        intro i j; simp only [List.map_cons]
        change natSumFin 3 (fun q => _ * evalFinWordMat 84 3 _ tl q j) =
          natSumFin 3 (fun q => _ * evalFinWordMat 42 3 _ (tl.map projSym84To42) q j)
        apply congrArg (natSumFin 3); funext q; rw [ih q j]; rfl
    refine ⟨hw39, ?_, ?_, ?_⟩
    · intro v hv_wk
      apply genFarkas_zero_strict_of_basis_w19 42 3 (by decide)
        (invPosTraceMat3DC39 (2 + (k - 2)) a b g de e)
        (fun i l => if i.val == 0 then farkasMu0CoupledC39 l
                    else if i.val == 1 then b * farkasMu1InvW19C39 l
                    else a * (farkasMu2InvW19C39 l + farkasMu3InvW19C39 l))
        c39FastRulesW19 hmu0_39 _ v hv_wk
      intro s0 j0; dsimp only
      rcases hgen3_eq 42 id farkasMu0CoupledC39 (fun l => b * farkasMu1InvW19C39 l)
        (fun l => a * (farkasMu2InvW19C39 l + farkasMu3InvW19C39 l)) (2 + (k - 2)) a b g de e
        (basisVec3D 42 s0 j0) c39FastRulesW19 with ⟨hl, hr⟩
      have hub := unpack_symFarkas3DRange_w19 42 id farkasMu0CoupledC39 farkasMu1InvW19C39
        (fun l => farkasMu2InvW19C39 l + farkasMu3InvW19C39 l) c39FastRulesW19 0 42 inv3d_farkas_c39_cert_w19
        (k - 2) a b g de e s0 j0 (Nat.zero_le _) s0.isLt
      rw [← hl, ← hr] at hub
      exact hub
    · intro r hr i j
      rw [hproj84_3 r.1 i j, hproj84_3 r.2 i j]
      rcases List.any_eq_true.mp (List.all_eq_true.mp hc78_proj r hr) with ⟨r39, hr39, hbeq⟩
      have heq_p := beq_iff_eq.mp hbeq
      have h1 : r.1.map projSym84To42 = r39.1 := congrArg Prod.fst heq_p
      have h2 : r.2.map projSym84To42 = r39.2 := congrArg Prod.snd heq_p
      rw [h1, h2]
      exact hw39 r39 hr39 i j
    · intro v hv_wk
      apply genFarkas_zero_strict_of_basis_w19 84 3 (by decide)
        (invPosTraceMat3DC78 (2 + (k - 2)) a b g de e)
        (fun i l => if i.val == 0 then farkasMu0CoupledC78 l
                    else if i.val == 1 then b * farkasMu1InvW19C78 l
                    else a * (farkasMu2InvW19C78 l + farkasMu3InvW19C78 l))
        c78FastRulesW19 hmu0_78 _ v hv_wk
      intro s0 j0; dsimp only
      rcases hgen3_eq 84 projSym84To42 farkasMu0CoupledC78 (fun l => b * farkasMu1InvW19C78 l)
        (fun l => a * (farkasMu2InvW19C78 l + farkasMu3InvW19C78 l)) (2 + (k - 2)) a b g de e
        (basisVec3D 84 s0 j0) c78FastRulesW19 with ⟨hl, hr⟩
      have hub : farkasInv3DVecLhsN 84 projSym84To42 farkasMu0CoupledC78
          (fun l => b * farkasMu1InvW19C78 l) (fun l => a * (farkasMu2InvW19C78 l + farkasMu3InvW19C78 l))
          (2 + (k - 2)) a b g de e (basisVec3D 84 s0 j0) c78FastRulesW19 ≤
        farkasInv3DVecRhsN 84 projSym84To42 farkasMu0CoupledC78
          (fun l => b * farkasMu1InvW19C78 l) (fun l => a * (farkasMu2InvW19C78 l + farkasMu3InvW19C78 l))
          (2 + (k - 2)) a b g de e (basisVec3D 84 s0 j0) c78FastRulesW19 := by
        by_cases h21 : s0.val < 21
        · exact unpack_symFarkas3DRange_w19 84 projSym84To42 _ _ _ c78FastRulesW19 0 21
            inv3d_farkas_c78_q0_w19 (k - 2) a b g de e s0 j0 (Nat.zero_le _) h21
        · by_cases h42 : s0.val < 42
          · exact unpack_symFarkas3DRange_w19 84 projSym84To42 _ _ _ c78FastRulesW19 21 21
              inv3d_farkas_c78_q1_w19 (k - 2) a b g de e s0 j0 (by omega) h42
          · by_cases h63 : s0.val < 63
            · exact unpack_symFarkas3DRange_w19 84 projSym84To42 _ _ _ c78FastRulesW19 42 21
                inv3d_farkas_c78_q2_w19 (k - 2) a b g de e s0 j0 (by omega) h63
            · exact unpack_symFarkas3DRange_w19 84 projSym84To42 _ _ _ c78FastRulesW19 63 21
                inv3d_farkas_c78_q3_w19 (k - 2) a b g de e s0 j0 (by omega) s0.isLt
      rw [← hl, ← hr] at hub
      exact hub
  · intro k a b g de e z hk2 _ _ _ _ _ _
    rcases h4d_all k a b g de e z hk2 with ⟨hw39, hw78, hb39, hb78⟩
    refine ⟨hw39, ?_, hw78, ?_⟩
    · intro v hv_wk
      apply genFarkas_zero_strict_of_basis_w19 42 4 (by decide)
        (multiChanInvMat4DC39 k a b g de e z)
        (fun i l => if i.val == 0 then farkasMu0CoupledC39 l
                    else if i.val == 1 then b * farkasMu1InvW19C39 l
                    else if i.val == 2 then a * farkasMu2InvW19C39 l
                    else z * farkasMu3InvW19C39 l)
        c39FastRulesW19 hmu0_39 _ v hv_wk
      intro s0 j0; dsimp only
      rcases hgen4_eq 42 id farkasMu0CoupledC39 (fun l => b * farkasMu1InvW19C39 l)
        (fun l => a * farkasMu2InvW19C39 l) (fun l => z * farkasMu3InvW19C39 l) k a b g de e z
        (basisVec4D 42 s0 j0) c39FastRulesW19 with ⟨hl, hr⟩
      have hub := hb39 s0 j0
      rw [← hl, ← hr] at hub
      exact hub
    · intro v hv_wk
      apply genFarkas_zero_strict_of_basis_w19 84 4 (by decide)
        (multiChanInvMat4DC78 k a b g de e z)
        (fun i l => if i.val == 0 then farkasMu0CoupledC78 l
                    else if i.val == 1 then b * farkasMu1InvW19C78 l
                    else if i.val == 2 then a * farkasMu2InvW19C78 l
                    else z * farkasMu3InvW19C78 l)
        c78FastRulesW19 hmu0_78 _ v hv_wk
      intro s0 j0; dsimp only
      rcases hgen4_eq 84 projSym84To42 farkasMu0CoupledC78 (fun l => b * farkasMu1InvW19C78 l)
        (fun l => a * farkasMu2InvW19C78 l) (fun l => z * farkasMu3InvW19C78 l) k a b g de e z
        (basisVec4D 84 s0 j0) c78FastRulesW19 with ⟨hl, hr⟩
      have hub := hb78 s0 j0
      rw [← hl, ← hr] at hub
      exact hub
  · -- All-dimension `∀ d ≥ 4` multi-channel invertible cones on `c39` and `c78`:
    intro d hd k a b g de e zetaCh hk2
    have hany_mat : ∀ (N : Nat) (proj : Fin N -> Fin 42)
        (rs : List (List (Fin N) × List (Fin N))),
        (∀ z : Nat, ∀ r ∈ rs, ∀ i j : Fin 4,
          evalFinWordMat N 4 (fun s => multiChanInvMat4DC39 k a b g de e z (proj s)) r.1 i j ≥
            evalFinWordMat N 4 (fun s => multiChanInvMat4DC39 k a b g de e z (proj s)) r.2 i j) ->
        ∀ r ∈ rs, ∀ i j : Fin d,
          evalFinWordMat N d (fun s => multiChanInvMatTowerAnyDC39 d k a b g de e zetaCh (proj s)) r.1 i j ≥
            evalFinWordMat N d (fun s => multiChanInvMatTowerAnyDC39 d k a b g de e zetaCh (proj s)) r.2 i j := by
      intro N proj rs h4_wk r hr i j
      rcases anyD_wordMat_eq_4d_w19 N d hd proj k a b g de e zetaCh r.1 with ⟨hl1, hl2, hl3, hl4⟩
      rcases anyD_wordMat_eq_4d_w19 N d hd proj k a b g de e zetaCh r.2 with ⟨hr1, hr2, hr3, hr4⟩
      by_cases hi : i.val < 3
      · by_cases hj : j.val < 3
        · rw [hl1 i j hi hj, hr1 i j hi hj]
          exact h4_wk 0 r hr ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
        · rw [hl2 i j hi (by omega), hr2 i j hi (by omega)]
          exact h4_wk (zetaCh j) r hr ⟨i.val, by omega⟩ ⟨3, by decide⟩
      · by_cases hij : i = j
        · subst hij; rw [hl3 i (by omega), hr3 i (by omega)]
          exact h4_wk 0 r hr ⟨3, by decide⟩ ⟨3, by decide⟩
        · rw [hl4 i j (by omega) hij, hr4 i j (by omega) hij]; omega
    have hany_farkas : ∀ (N : Nat) (proj : Fin N -> Fin 42)
        (mu0 mu1 mu2 mu3 : List (Fin N) -> Nat)
        (rs : List (List (Fin N) × List (Fin N))),
        (∀ r ∈ rs, mu0 r.1 ≥ 1) ->
        (∀ (z : Nat) (s0 : Fin N) (j0 : Fin 4),
          farkasInv4DVecLhsN N proj mu0 (fun l => b * mu1 l) (fun l => a * mu2 l) (fun l => z * mu3 l)
            k a b g de e z (basisVec4D N s0 j0) rs ≤
          farkasInv4DVecRhsN N proj mu0 (fun l => b * mu1 l) (fun l => a * mu2 l) (fun l => z * mu3 l)
            k a b g de e z (basisVec4D N s0 j0) rs) ->
        ∀ v : Fin N -> Fin d -> Nat,
          (∀ r ∈ rs, ∀ i : Fin d,
            evalFinWordVec N d (fun s => multiChanInvMatTowerAnyDC39 d k a b g de e zetaCh (proj s)) v r.1 i ≥
              evalFinWordVec N d (fun s => multiChanInvMatTowerAnyDC39 d k a b g de e zetaCh (proj s)) v r.2 i) ->
          ∀ r ∈ rs,
            evalFinWordVec N d (fun s => multiChanInvMatTowerAnyDC39 d k a b g de e zetaCh (proj s)) v r.1 ⟨0, by omega⟩ =
              evalFinWordVec N d (fun s => multiChanInvMatTowerAnyDC39 d k a b g de e zetaCh (proj s)) v r.2 ⟨0, by omega⟩ := by
      intro N proj mu0 mu1 mu2 mu3 rs hmu_p h4_bas v hv_wk
      let wtAny : Fin d -> List (Fin N) -> Nat := fun i l =>
        if i.val == 0 then mu0 l
        else if i.val == 1 then b * mu1 l
        else if i.val == 2 then a * mu2 l
        else zetaCh i * mu3 l
      apply genFarkas_zero_strict_of_basis_w19 N d (by omega)
        (fun s => multiChanInvMatTowerAnyDC39 d k a b g de e zetaCh (proj s))
        wtAny rs hmu_p _ v hv_wk
      intro s0 j0; dsimp only
      let bAny := fun (s : Fin N) (j : Fin d) => if s.val == s0.val && j.val == j0.val then 1 else 0
      -- Show `genFarkasVec* N d ... bAny xs = farkasInv4DVec* N proj ...`:
      by_cases hj0 : j0.val < 3
      · have heq0 : ∀ xs : List (List (Fin N) × List (Fin N)),
            genFarkasVecLhsW19 N d (fun s => multiChanInvMatTowerAnyDC39 d k a b g de e zetaCh (proj s)) wtAny bAny xs =
              farkasInv4DVecLhsN N proj mu0 (fun l => b * mu1 l) (fun l => a * mu2 l) (fun l => 0 * mu3 l)
                k a b g de e 0 (basisVec4D N s0 ⟨j0.val, by omega⟩) xs ∧
            genFarkasVecRhsW19 N d (fun s => multiChanInvMatTowerAnyDC39 d k a b g de e zetaCh (proj s)) wtAny bAny xs =
              farkasInv4DVecRhsN N proj mu0 (fun l => b * mu1 l) (fun l => a * mu2 l) (fun l => 0 * mu3 l)
                k a b g de e 0 (basisVec4D N s0 ⟨j0.val, by omega⟩) xs := by
          intro xs; induction xs with
          | nil => exact ⟨rfl, rfl⟩
          | cons r0 rtl ihx =>
            rcases r0 with ⟨l0, r0_w⟩
            have hrow : ∀ w : List (Fin N),
                natSumFin d (fun i => wtAny i l0 *
                  evalFinWordVec N d (fun s => multiChanInvMatTowerAnyDC39 d k a b g de e zetaCh (proj s)) bAny w i) =
                mu0 l0 * evalFinWordVec N 4 (fun s => multiChanInvMat4DC39 k a b g de e 0 (proj s))
                    (basisVec4D N s0 ⟨j0.val, by omega⟩) w ⟨0, by decide⟩ +
                (b * mu1 l0) * evalFinWordVec N 4 (fun s => multiChanInvMat4DC39 k a b g de e 0 (proj s))
                    (basisVec4D N s0 ⟨j0.val, by omega⟩) w ⟨1, by decide⟩ +
                (a * mu2 l0) * evalFinWordVec N 4 (fun s => multiChanInvMat4DC39 k a b g de e 0 (proj s))
                    (basisVec4D N s0 ⟨j0.val, by omega⟩) w ⟨2, by decide⟩ +
                (0 * mu3 l0) * evalFinWordVec N 4 (fun s => multiChanInvMat4DC39 k a b g de e 0 (proj s))
                    (basisVec4D N s0 ⟨j0.val, by omega⟩) w ⟨3, by decide⟩ := by
              intro w
              rcases (anyD_basisVec_eq_4d_w19 N d hd proj k a b g de e zetaCh s0 j0 w).1 hj0 with ⟨hi_lt, hi_ge⟩
              rw [natSumFin_split3_w19 d hd]
              have htail0 : natSumFin d (fun q => if q.val ≥ 3 then wtAny q l0 *
                  evalFinWordVec N d (fun s => multiChanInvMatTowerAnyDC39 d k a b g de e zetaCh (proj s)) bAny w q else 0) = 0 :=
                natSumFin_zero_w19 d _ (fun q => by
                  by_cases hq : q.val ≥ 3
                  · rw [ite_true_of_w10 hq, hi_ge q hq, Nat.mul_zero]
                  · rw [ite_false_of_w10 hq])
              rw [htail0, Nat.add_zero, Nat.zero_mul, Nat.zero_mul, Nat.add_zero,
                  hi_lt ⟨0, by omega⟩ (by dsimp; omega), hi_lt ⟨1, by omega⟩ (by dsimp; omega), hi_lt ⟨2, by omega⟩ (by dsimp; omega)]
              rfl
            simp only [genFarkasVecLhsW19, genFarkasVecRhsW19, farkasInv4DVecLhsN, farkasInv4DVecRhsN,
                       hrow l0, hrow r0_w, ihx.1, ihx.2]
            simp
        rcases heq0 rs with ⟨hl, hr⟩
        rw [hl, hr]; exact h4_bas 0 s0 ⟨j0.val, by omega⟩
      · have hj0_ge : j0.val ≥ 3 := by omega
        have heq3 : ∀ xs : List (List (Fin N) × List (Fin N)),
            genFarkasVecLhsW19 N d (fun s => multiChanInvMatTowerAnyDC39 d k a b g de e zetaCh (proj s)) wtAny bAny xs =
              farkasInv4DVecLhsN N proj mu0 (fun l => b * mu1 l) (fun l => a * mu2 l) (fun l => zetaCh j0 * mu3 l)
                k a b g de e (zetaCh j0) (basisVec4D N s0 ⟨3, by decide⟩) xs ∧
            genFarkasVecRhsW19 N d (fun s => multiChanInvMatTowerAnyDC39 d k a b g de e zetaCh (proj s)) wtAny bAny xs =
              farkasInv4DVecRhsN N proj mu0 (fun l => b * mu1 l) (fun l => a * mu2 l) (fun l => zetaCh j0 * mu3 l)
                k a b g de e (zetaCh j0) (basisVec4D N s0 ⟨3, by decide⟩) xs := by
          intro xs; induction xs with
          | nil => exact ⟨rfl, rfl⟩
          | cons r0 rtl ihx =>
            rcases r0 with ⟨l0, r0_w⟩
            have hrow : ∀ w : List (Fin N),
                natSumFin d (fun i => wtAny i l0 *
                  evalFinWordVec N d (fun s => multiChanInvMatTowerAnyDC39 d k a b g de e zetaCh (proj s)) bAny w i) =
                mu0 l0 * evalFinWordVec N 4 (fun s => multiChanInvMat4DC39 k a b g de e (zetaCh j0) (proj s))
                    (basisVec4D N s0 ⟨3, by decide⟩) w ⟨0, by decide⟩ +
                (b * mu1 l0) * evalFinWordVec N 4 (fun s => multiChanInvMat4DC39 k a b g de e (zetaCh j0) (proj s))
                    (basisVec4D N s0 ⟨3, by decide⟩) w ⟨1, by decide⟩ +
                (a * mu2 l0) * evalFinWordVec N 4 (fun s => multiChanInvMat4DC39 k a b g de e (zetaCh j0) (proj s))
                    (basisVec4D N s0 ⟨3, by decide⟩) w ⟨2, by decide⟩ +
                (zetaCh j0 * mu3 l0) * evalFinWordVec N 4 (fun s => multiChanInvMat4DC39 k a b g de e (zetaCh j0) (proj s))
                    (basisVec4D N s0 ⟨3, by decide⟩) w ⟨3, by decide⟩ := by
              intro w
              rcases (anyD_basisVec_eq_4d_w19 N d hd proj k a b g de e zetaCh s0 j0 w).2 hj0_ge with ⟨hi_lt, hj0_eq, hi_off⟩
              rw [natSumFin_split3_w19 d hd]
              have htail_j0 : natSumFin d (fun q => if q.val ≥ 3 then wtAny q l0 *
                  evalFinWordVec N d (fun s => multiChanInvMatTowerAnyDC39 d k a b g de e zetaCh (proj s)) bAny w q else 0) =
                  (zetaCh j0 * mu3 l0) *
                    evalFinWordVec N 4 (fun s => multiChanInvMat4DC39 k a b g de e (zetaCh j0) (proj s))
                      (basisVec4D N s0 ⟨3, by decide⟩) w ⟨3, by decide⟩ := by
                have hsingle : ∀ n : Nat, j0.val < n -> n ≤ d ->
                    natSumPrefix d (fun q => if q.val ≥ 3 then wtAny q l0 *
                      evalFinWordVec N d (fun s => multiChanInvMatTowerAnyDC39 d k a b g de e zetaCh (proj s)) bAny w q else 0) n =
                    (zetaCh j0 * mu3 l0) *
                      evalFinWordVec N 4 (fun s => multiChanInvMat4DC39 k a b g de e (zetaCh j0) (proj s))
                        (basisVec4D N s0 ⟨3, by decide⟩) w ⟨3, by decide⟩ := by
                  intro n; induction n with
                  | zero => intro hlt _; omega
                  | succ n' ihn =>
                    intro hlt hle; have hn_lt : n' < d := hle
                    unfold natSumPrefix; simp only [hn_lt, dite_true]
                    by_cases heq : j0.val = n'
                    · have hj_eq : j0 = ⟨n', hn_lt⟩ := Fin.ext heq; subst hj_eq
                      have hz : natSumPrefix d (fun q => if q.val ≥ 3 then wtAny q l0 *
                          evalFinWordVec N d (fun s => multiChanInvMatTowerAnyDC39 d k a b g de e zetaCh (proj s)) bAny w q else 0) n' = 0 := by
                        have h0 : ∀ m : Nat, m ≤ n' ->
                            natSumPrefix d (fun q => if q.val ≥ 3 then wtAny q l0 *
                              evalFinWordVec N d (fun s => multiChanInvMatTowerAnyDC39 d k a b g de e zetaCh (proj s)) bAny w q else 0) m = 0 := by
                          intro m; induction m with
                          | zero => intros; rfl
                          | succ m' ihm =>
                            intro hm'; have hm_lt : m' < d := by omega
                            unfold natSumPrefix; simp only [hm_lt, dite_true, ihm (by omega), Nat.zero_add]
                            by_cases hge3 : m' ≥ 3
                            · simp only [hge3, ite_true]
                              rw [hi_off ⟨m', hm_lt⟩ hge3 (fun h => by have := congrArg Fin.val h; dsimp at this; omega), Nat.mul_zero]
                            · simp only [hge3, ite_false]
                        exact h0 n' (Nat.le_refl n')
                      rw [hz, Nat.zero_add, ite_true_of_w10 hj0_ge, hj0_eq]
                      have hwt_j0 : wtAny ⟨n', hn_lt⟩ l0 = zetaCh ⟨n', hn_lt⟩ * mu3 l0 := by
                        dsimp [wtAny]
                        rw [beq_false_of_ne (by omega : n' ≠ 0), beq_false_of_ne (by omega : n' ≠ 1),
                            beq_false_of_ne (by omega : n' ≠ 2)]
                        rfl
                      rw [hwt_j0]
                    · rw [ihn (by omega) (by omega)]
                      by_cases hge3 : n' ≥ 3
                      · simp only [hge3, ite_true]
                        rw [hi_off ⟨n', hn_lt⟩ hge3 (fun h => heq (congrArg Fin.val h.symm)), Nat.mul_zero, Nat.add_zero]
                      · simp only [hge3, ite_false, Nat.add_zero]
                exact hsingle d j0.isLt (Nat.le_refl d)
              rw [htail_j0, hi_lt ⟨0, by omega⟩ (by dsimp; omega), hi_lt ⟨1, by omega⟩ (by dsimp; omega),
                  hi_lt ⟨2, by omega⟩ (by dsimp; omega)]
              rfl
            simp only [genFarkasVecLhsW19, genFarkasVecRhsW19, farkasInv4DVecLhsN, farkasInv4DVecRhsN,
                       hrow l0, hrow r0_w, ihx.1, ihx.2]
            simp
        rcases heq3 rs with ⟨hl, hr⟩
        rw [hl, hr]; exact h4_bas (zetaCh j0) s0 ⟨3, by decide⟩
    exact ⟨hany_mat 42 id c39FastRulesW19 (fun z => (h4d_all k a b g de e z hk2).1),
           hany_farkas 42 id farkasMu0CoupledC39 farkasMu1InvW19C39 farkasMu2InvW19C39 farkasMu3InvW19C39
             c39FastRulesW19 hmu0_39 (fun z => (h4d_all k a b g de e z hk2).2.2.1),
           hany_mat 84 projSym84To42 c78FastRulesW19 (fun z => (h4d_all k a b g de e z hk2).2.1),
           hany_farkas 84 projSym84To42 farkasMu0CoupledC78 farkasMu1InvW19C78 farkasMu2InvW19C78 farkasMu3InvW19C78
             c78FastRulesW19 hmu0_78 (fun z => (h4d_all k a b g de e z hk2).2.2.2)⟩

-- ============================================================================
-- Section 2A: Rank-3 Order-4 `12 × 12` `(T = 4, U = 3)` Global `u ∈ {6, 7, 8, 9}`
--             Non-Vanishing, Exact `laurentTrop3Mat12` Closed-Form Factorization,
--             & Mod-`243` Resonant-Ray Elimination (`W19_H2`, Branch P3.2–P3.3)
-- ============================================================================

private theorem dite_pos_w19 {p : Prop} [inst : Decidable p] {α : Sort _}
    {t : p -> α} {e : ¬ p -> α} (hp : p) : (if h : p then t h else e h) = t hp := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn hp)

private theorem dite_neg_w19 {p : Prop} [inst : Decidable p] {α : Sort _}
    {t : p -> α} {e : ¬ p -> α} (hnp : ¬ p) : (if h : p then t h else e h) = e hnp := by
  cases inst with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

private theorem mul_pow_w19 (a b : Nat) : ∀ n : Nat, (a * b) ^ n = a ^ n * b ^ n
  | 0 => rfl
  | n + 1 => by rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, mul_pow_w19 a b n]; ac_rfl

private theorem intPowNat_natCast_w19 (n d : Nat) :
    intPowNat (n : Int) d = ((n ^ d : Nat) : Int) := by
  induction d with
  | zero => rfl
  | succ d' ih => simp only [intPowNat, ih, Nat.pow_succ, Int.natCast_mul]; ac_rfl

private theorem int_mod_sub_dvd_w19 (a pNat : Nat) :
    (pNat : Int) ∣ (((a % pNat : Nat) : Int) - (a : Int)) := by
  refine ⟨-((a / pNat : Nat) : Int), ?_⟩
  have hc := congrArg (fun n : Nat => (n : Int)) (Nat.div_add_mod a pNat)
  simp only [Int.natCast_add, Int.natCast_mul] at hc
  rw [Int.mul_neg]; omega

private def intAt2DW19 (rows : List (List Int)) (r c : Nat) : Int :=
  match rows.drop r with
  | row :: _ =>
    match row.drop c with
    | x :: _ => x
    | [] => 0
  | [] => 0

private def intDiagProdPrefixW19 (N : Nat) (U : Fin N -> Fin N -> Int) : Nat -> Int
  | 0 => 1
  | k + 1 =>
    if h : k < N then intDiagProdPrefixW19 N U k * U ⟨k, h⟩ ⟨k, h⟩
    else intDiagProdPrefixW19 N U k

private def allFinLoopW19 (N : Nat) (p : Fin N -> Bool) : Nat -> Bool
  | 0 => true
  | k + 1 => (if h : k < N then p ⟨k, h⟩ else true) && allFinLoopW19 N p k

private theorem allFinLoopW19_spec (N : Nat) (p : Fin N -> Bool) (h : allFinLoopW19 N p N = true) :
    ∀ x : Fin N, p x = true := by
  have hst : ∀ k : Nat, k ≤ N -> allFinLoopW19 N p k = true -> ∀ x : Fin N, x.val < k -> p x = true := by
    intro k hk; induction k with
    | zero => intros _ _ hlt; omega
    | succ k' ih =>
      intro ha x hx_lt
      unfold allFinLoopW19 at ha
      rcases bool_and_split ha with ⟨hcur, hprev⟩
      by_cases hxk : x.val = k'
      · have hk_lt : k' < N := hk
        simp only [hk_lt, dite_true] at hcur
        rwa [show x = ⟨k', hk_lt⟩ from Fin.ext hxk]
      · exact ih (Nat.le_of_lt hk) hprev x (by omega)
  intro x; exact hst N (Nat.le_refl _) h x x.isLt

private theorem intDet_mul_upper_tri_w19 (N : Nat) (A U : Fin N -> Fin N -> Int)
    (hupper : ∀ r c : Fin N, c.val < r.val -> U r c = 0) :
    intDet N (fun i j => intSumPrefix N (fun r => A i r * U r j) N) =
      intDiagProdPrefixW19 N U N * intDet N A := by
  have htrunc : ∀ (i j : Fin N) (m : Nat), j.val + 1 ≤ m -> m ≤ N ->
      intSumPrefix N (fun r => A i r * U r j) m =
        intSumPrefix N (fun r => A i r * U r j) (j.val + 1) := by
    intro i j m hlo hhi
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
      intDet N (M_stage 0) = intDiagProdPrefixW19 N U k * intDet N (M_stage k) := by
    intro k hk; induction k with
    | zero => simp [intDiagProdPrefixW19]
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
      simp only [intDiagProdPrefixW19, hk'_lt, dite_true]
      exact (Int.mul_assoc (intDiagProdPrefixW19 N U k') (U jk jk) _).symm
  rw [h0_eq, hstep N (Nat.le_refl N), hN_eq]

private theorem intDet_peel_lower_rows_w19 :
    ∀ (k rem : Nat) (L_mat : Fin (rem + k) -> Fin (rem + k) -> Int),
      (∀ r c : Fin (rem + k), r.val < k -> r.val < c.val -> L_mat r c = 0) ->
      intDet (rem + k) L_mat =
        intDiagProdPrefixW19 (rem + k) L_mat k *
          intDet rem (fun a b => L_mat ⟨k + a.val, by omega⟩ ⟨k + b.val, by omega⟩)
  | 0, rem, L_mat, _ => by
    simp only [intDiagProdPrefixW19, Int.one_mul]
    congr 1; funext a b
    congr 1 <;> (apply Fin.ext; dsimp; omega)
  | k' + 1, rem, L_mat, hlow => by
    let z0 : Fin (rem + k' + 1) := ⟨0, Nat.zero_lt_succ _⟩
    change intDet (rem + k' + 1) L_mat =
      intDiagProdPrefixW19 (rem + k' + 1) L_mat (k' + 1) *
        intDet rem (fun a b => L_mat ⟨(k' + 1) + a.val, by omega⟩ ⟨(k' + 1) + b.val, by omega⟩)
    rw [intDet_succ_single_row0 (rem + k') L_mat z0
        (fun j hj => hlow z0 j (Nat.zero_lt_succ k') (by
          have hv : j.val ≠ 0 := fun h => hj (Fin.ext h)
          dsimp [z0]; omega))]
    have hev : z0.val % 2 = 0 := rfl
    rw [ite_true_of_w10 hev, Int.one_mul]
    have hsub_low : ∀ r c : Fin (rem + k'), r.val < k' -> r.val < c.val ->
        intSubMat L_mat z0 r c = 0 := by
      intro r c hrk hrc
      simp only [intSubMat, skipFinIdx, z0, Nat.not_lt_zero, ite_false]
      exact hlow ⟨r.val + 1, by omega⟩ ⟨c.val + 1, by omega⟩ (by dsimp; omega) (by dsimp; omega)
    rw [intDet_peel_lower_rows_w19 k' rem (intSubMat L_mat z0) hsub_low]
    have hprod_shift : ∀ m : Nat, m ≤ rem + k' ->
        L_mat z0 z0 * intDiagProdPrefixW19 (rem + k') (intSubMat L_mat z0) m =
          intDiagProdPrefixW19 (rem + k' + 1) L_mat (m + 1) := by
      intro m hm; induction m with
      | zero =>
        simp only [intDiagProdPrefixW19, Nat.zero_lt_succ, dite_true, Int.one_mul, Int.mul_one]
        rfl
      | succ m' ih =>
        have hm'_lt : m' < rem + k' := hm
        have hm1_lt : m' + 1 < rem + k' + 1 := Nat.succ_lt_succ hm
        simp only [intDiagProdPrefixW19, hm'_lt, hm1_lt, dite_true, ← Int.mul_assoc, ih (Nat.le_of_lt hm)]
        simp only [intSubMat, skipFinIdx, z0, Nat.not_lt_zero, ite_false]
    have htail_eq : (fun a b : Fin rem =>
          intSubMat L_mat z0
            ⟨k' + a.val, by change k' + a.val < rem + k'; rw [Nat.add_comm rem k']; exact Nat.add_lt_add_left a.isLt k'⟩
            ⟨k' + b.val, by change k' + b.val < rem + k'; rw [Nat.add_comm rem k']; exact Nat.add_lt_add_left b.isLt k'⟩) =
        (fun a b : Fin rem => L_mat ⟨(k' + 1) + a.val, by omega⟩ ⟨(k' + 1) + b.val, by omega⟩) := by
      funext a b
      simp only [intSubMat, skipFinIdx, z0, Nat.not_lt_zero, ite_false]
      congr 1 <;> (apply Fin.ext; dsimp; omega)
    rw [← Int.mul_assoc, hprod_shift k' (by omega), htail_eq]

private theorem intDet_lower_tri_w19 :
    ∀ (N : Nat) (L_mat : Fin N -> Fin N -> Int),
      (∀ r c : Fin N, r.val < c.val -> L_mat r c = 0) ->
      intDet N L_mat = intDiagProdPrefixW19 N L_mat N
  | 0, _, _ => rfl
  | n' + 1, L_mat, hlow => by
    let z0 : Fin (n' + 1) := ⟨0, Nat.zero_lt_succ n'⟩
    rw [intDet_succ_single_row0 n' L_mat z0 (fun j hj => hlow z0 j (by
      have hv : j.val ≠ 0 := fun h => hj (Fin.ext h)
      dsimp [z0]; omega))]
    have hev : z0.val % 2 = 0 := rfl
    rw [ite_true_of_w10 hev, Int.one_mul]
    have hsub : ∀ r c : Fin n', r.val < c.val -> intSubMat L_mat z0 r c = 0 := by
      intro r c hrc
      simp only [intSubMat, skipFinIdx, z0, Nat.not_lt_zero, ite_false]
      exact hlow ⟨r.val + 1, by omega⟩ ⟨c.val + 1, by omega⟩ (by dsimp; omega)
    rw [intDet_lower_tri_w19 n' (intSubMat L_mat z0) hsub]
    have hsh : ∀ m : Nat, m ≤ n' ->
        L_mat z0 z0 * intDiagProdPrefixW19 n' (intSubMat L_mat z0) m =
          intDiagProdPrefixW19 (n' + 1) L_mat (m + 1) := by
      intro m hm; induction m with
      | zero =>
        simp only [intDiagProdPrefixW19, Nat.zero_lt_succ, dite_true, Int.one_mul, Int.mul_one]
        rfl
      | succ m' ih =>
        have hm'_lt : m' < n' := hm
        have hm1_lt : m' + 1 < n' + 1 := Nat.succ_lt_succ hm
        simp only [intDiagProdPrefixW19, hm'_lt, hm1_lt, dite_true, ← Int.mul_assoc, ih (Nat.le_of_lt hm)]
        simp only [intSubMat, skipFinIdx, z0, Nat.not_lt_zero, ite_false]
    exact hsh n' (Nat.le_refl n')

private def checkULDetBoolW19 (N : Nat) (A : Fin N -> Fin N -> Int) (uTbl : List (List Int)) (expDet : Int) : Bool :=
  let U (i j : Fin N) : Int := intAt2DW19 uTbl i.val j.val
  let prodMat (i j : Fin N) : Int := intSumPrefix N (fun r => A i r * U r j) N
  let upperOk := allFinLoopW19 N (fun r =>
    allFinLoopW19 N (fun c => if c.val < r.val then U r c == 0 else true) N) N
  let lowerOk := allFinLoopW19 N (fun r =>
    allFinLoopW19 N (fun c => if r.val < c.val then prodMat r c == 0 else true) N) N
  let uDiag := intDiagProdPrefixW19 N U N
  let lDiag := intDiagProdPrefixW19 N prodMat N
  upperOk && lowerOk && (uDiag != 0) && (lDiag == uDiag * expDet)

private theorem checkULDetBoolW19_sound (N : Nat) (A : Fin N -> Fin N -> Int)
    (uTbl : List (List Int)) (expDet : Int)
    (h : checkULDetBoolW19 N A uTbl expDet = true) :
    intDet N A = expDet := by
  let U (i j : Fin N) : Int := intAt2DW19 uTbl i.val j.val
  let prodMat (i j : Fin N) : Int := intSumPrefix N (fun r => A i r * U r j) N
  unfold checkULDetBoolW19 at h
  rcases bool_and_split h with ⟨hb1, hl_eq_b⟩
  rcases bool_and_split hb1 with ⟨hb2, hu_nz_b⟩
  rcases bool_and_split hb2 with ⟨hup_b, hlo_b⟩
  have hupper : ∀ r c : Fin N, c.val < r.val -> U r c = 0 := by
    intro r c hlt
    have hc := allFinLoopW19_spec N _ (allFinLoopW19_spec N _ hup_b r) c
    dsimp only at hc; rw [ite_true_of_w10 hlt] at hc
    exact beq_iff_eq.mp hc
  have hlower : ∀ r c : Fin N, r.val < c.val -> prodMat r c = 0 := by
    intro r c hlt
    have hc := allFinLoopW19_spec N _ (allFinLoopW19_spec N _ hlo_b r) c
    dsimp only at hc; rw [ite_true_of_w10 hlt] at hc
    exact beq_iff_eq.mp hc
  have hu_nz : intDiagProdPrefixW19 N U N ≠ 0 := bne_iff_ne.mp hu_nz_b
  have hl_eq : intDiagProdPrefixW19 N prodMat N = intDiagProdPrefixW19 N U N * expDet :=
    beq_iff_eq.mp hl_eq_b
  have hmul : intDiagProdPrefixW19 N U N * intDet N A = intDiagProdPrefixW19 N U N * expDet := by
    rw [← intDet_mul_upper_tri_w19 N A U hupper]
    change intDet N prodMat = _
    rw [intDet_lower_tri_w19 N prodMat hlower, hl_eq]
  exact Int.eq_of_mul_eq_mul_left hu_nz hmul

private theorem signedColSwap_det_w19 (N : Nat) (c1 c2 : Fin N) (hne : c1 ≠ c2)
    (M : Fin N -> Fin N -> Int) :
    intDet N (fun i j => if j = c1 then M i c2 else if j = c2 then -(M i c1) else M i j) =
      intDet N M := by
  let M1 : Fin N -> Fin N -> Int := fun i j => if j = c1 then M i c1 - (-1) * M i c2 else M i j
  let M2 : Fin N -> Fin N -> Int := fun i j => if j = c2 then M1 i c2 - 1 * M1 i c1 else M1 i j
  let M3 : Fin N -> Fin N -> Int := fun i j => if j = c1 then M2 i c1 - (-1) * M2 i c2 else M2 i j
  have hd1 : intDet N M1 = intDet N M := intDet_sub_col_mul_other N c1 c2 (Ne.symm hne) (-1) M
  have hd2 : intDet N M2 = intDet N M1 := intDet_sub_col_mul_other N c2 c1 hne 1 M1
  have hd3 : intDet N M3 = intDet N M2 := intDet_sub_col_mul_other N c1 c2 (Ne.symm hne) (-1) M2
  have hM3_eq : M3 = (fun i j => if j = c1 then M i c2 else if j = c2 then -(M i c1) else M i j) := by
    funext i j
    have hm1_c1 : M1 i c1 = M i c1 - (-1) * M i c2 := by dsimp [M1]; rw [ite_true_of_w10 rfl]
    have hm1_c2 : M1 i c2 = M i c2 := by dsimp [M1]; rw [ite_false_of_w10 (Ne.symm hne)]
    have hm2_c1 : M2 i c1 = M1 i c1 := by dsimp [M2]; rw [ite_false_of_w10 hne]
    have hm2_c2 : M2 i c2 = M1 i c2 - 1 * M1 i c1 := by dsimp [M2]; rw [ite_true_of_w10 rfl]
    by_cases hj1 : j = c1
    · subst hj1
      rw [ite_true_of_w10 rfl]
      dsimp [M3]; rw [ite_true_of_w10 rfl, hm2_c1, hm2_c2, hm1_c1, hm1_c2]; omega
    · rw [ite_false_of_w10 hj1]
      by_cases hj2 : j = c2
      · subst hj2
        rw [ite_true_of_w10 rfl]
        dsimp [M3]; rw [ite_false_of_w10 (Ne.symm hne), hm2_c2, hm1_c2, hm1_c1]; omega
      · rw [ite_false_of_w10 hj2]
        dsimp [M3, M2, M1]; rw [ite_false_of_w10 hj1, ite_false_of_w10 hj2, ite_false_of_w10 hj1]
  rw [← hM3_eq, hd3, hd2, hd1]

private def applySignedSwapsIntW19 (N : Nat) :
    List (Nat × Nat) -> (Fin N -> Fin N -> Int) -> (Fin N -> Fin N -> Int)
  | [], M => M
  | (c1, c2) :: rest, M =>
    let M' :=
      if h : c1 < N ∧ c2 < N ∧ c1 ≠ c2 then
        fun i j =>
          if j = ⟨c1, h.1⟩ then M i ⟨c2, h.2.1⟩
          else if j = ⟨c2, h.2.1⟩ then -(M i ⟨c1, h.1⟩)
          else M i j
      else M
    applySignedSwapsIntW19 N rest M'

private theorem applySignedSwapsIntW19_det (N : Nat) :
    ∀ (swaps : List (Nat × Nat)) (M : Fin N -> Fin N -> Int),
      intDet N (applySignedSwapsIntW19 N swaps M) = intDet N M
  | [], _ => rfl
  | (c1, c2) :: rest, M => by
    unfold applySignedSwapsIntW19
    by_cases h : c1 < N ∧ c2 < N ∧ c1 ≠ c2
    · rw [dite_pos_w19 h, applySignedSwapsIntW19_det N rest]
      exact signedColSwap_det_w19 N ⟨c1, h.1⟩ ⟨c2, h.2.1⟩ (fun heq => h.2.2 (congrArg Fin.val heq)) M
    · rw [dite_neg_w19 h, applySignedSwapsIntW19_det N rest]

-- Order-4 Stirling block reduction (`12 * det(blk m) = det(blk (m + 1))`) for ANY `N = 4 * U`:
private theorem stirling_order4_blocks_w19 (U : Nat) (xFn : Fin (4 * U) -> Nat)
    (eFn : Fin (4 * U) -> Nat -> Int) :
    ((12 ^ U : Nat) : Int) *
      intDet (4 * U) (fun i j => ((laurentInterpBinom (xFn i) (j.val % 4) : Nat) : Int) * eFn i (j.val / 4)) =
    intDet (4 * U) (fun i j => intPowNat ((xFn i : Nat) : Int) (j.val % 4) * eFn i (j.val / 4)) := by
  let N := 4 * U
  have hbinom_st : ∀ x : Nat,
      laurentInterpBinom x 0 = 1 ∧ laurentInterpBinom x 1 = x ∧
      2 * laurentInterpBinom x 2 + x = x * x ∧
      6 * laurentInterpBinom x 3 + 3 * (x * x) = x * x * x + 2 * x := by
    intro x; induction x with
    | zero => decide
    | succ x' ih =>
      rcases ih with ⟨h0, h1, h2, h3⟩
      refine ⟨rfl, by simp [laurentInterpBinom, h0, h1]; omega, ?_, ?_⟩
      · simp only [laurentInterpBinom, h1]
        change 2 * (x' + laurentInterpBinom x' 2) + (x' + 1) = (x' + 1) * (x' + 1)
        rw [Nat.mul_add 2, show (x' + 1) * (x' + 1) = x' * x' + 2 * x' + 1 by simp only [Nat.add_mul, Nat.mul_add]; omega]
        omega
      · simp only [laurentInterpBinom]
        change 6 * (laurentInterpBinom x' 2 + laurentInterpBinom x' 3) + 3 * ((x' + 1) * (x' + 1)) =
          (x' + 1) * (x' + 1) * (x' + 1) + 2 * (x' + 1)
        have hsq : (x' + 1) * (x' + 1) = x' * x' + 2 * x' + 1 := by simp only [Nat.add_mul, Nat.mul_add]; omega
        have hcub : (x' + 1) * (x' + 1) * (x' + 1) = x' * x' * x' + 3 * (x' * x') + 3 * x' + 1 := by
          rw [hsq]; simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul, Nat.mul_assoc 2 x' x']
          generalize x' * x' * x' = X3; generalize x' * x' = X2; omega
        rw [Nat.mul_add 6, show 6 * laurentInterpBinom x' 2 = 3 * (2 * laurentInterpBinom x' 2) from Nat.mul_assoc 3 2 _,
            hcub, hsq, Nat.mul_add 3 (x' * x' + 2 * x') 1, Nat.mul_add 3 (x' * x') (2 * x')]
        generalize 6 * laurentInterpBinom x' 3 = C3 at h3 ⊢
        generalize 2 * laurentInterpBinom x' 2 = C2 at h2 ⊢
        generalize x' * x' * x' = X3 at h3 ⊢
        generalize x' * x' = X2 at h2 h3 ⊢
        omega
  let blkSt (b_done : Nat) (i j : Fin N) : Int :=
    if j.val / 4 < b_done then intPowNat ((xFn i : Nat) : Int) (j.val % 4) * eFn i (j.val / 4)
    else ((laurentInterpBinom (xFn i) (j.val % 4) : Nat) : Int) * eFn i (j.val / 4)
  have hstep : ∀ m : Nat, m < U -> 12 * intDet N (blkSt m) = intDet N (blkSt (m + 1)) := by
    intro m hmU
    have hmN : 4 * m + 3 < N := by dsimp [N]; omega
    let c1 : Fin N := ⟨4 * m + 1, by omega⟩
    let c2 : Fin N := ⟨4 * m + 2, by omega⟩
    let c3 : Fin N := ⟨4 * m + 3, hmN⟩
    let B0 := blkSt m
    let B1 : Fin N -> Fin N -> Int := fun i j => if j = c2 then 2 * B0 i c2 else B0 i j
    let B2 : Fin N -> Fin N -> Int := fun i j => if j = c3 then 6 * B1 i c3 else B1 i j
    have hd1 : intDet N B1 = 2 * intDet N B0 := intDet_col_scale 2 N c2 B0
    have hd2 : intDet N B2 = 6 * intDet N B1 := intDet_col_scale 6 N c3 B1
    let B3 : Fin N -> Fin N -> Int := fun i j => if j = c2 then B2 i c2 - (-1) * B2 i c1 else B2 i j
    have hd3 : intDet N B3 = intDet N B2 :=
      intDet_sub_col_mul_other N c2 c1 (by intro h; have := congrArg Fin.val h; dsimp [c1, c2] at this; omega) (-1) B2
    let B4 : Fin N -> Fin N -> Int := fun i j => if j = c3 then B3 i c3 - (-3) * B3 i c2 else B3 i j
    have hd4 : intDet N B4 = intDet N B3 :=
      intDet_sub_col_mul_other N c3 c2 (by intro h; have := congrArg Fin.val h; dsimp [c2, c3] at this; omega) (-3) B3
    let B5 : Fin N -> Fin N -> Int := fun i j => if j = c3 then B4 i c3 - 2 * B4 i c1 else B4 i j
    have hd5 : intDet N B5 = intDet N B4 :=
      intDet_sub_col_mul_other N c3 c1 (by intro h; have := congrArg Fin.val h; dsimp [c1, c3] at this; omega) 2 B4
    have hB5_eq : B5 = blkSt (m + 1) := by
      funext i j
      by_cases hjm : j.val / 4 = m
      · have hj_rem : j.val = 4 * m + j.val % 4 := by
          have := Nat.div_add_mod j.val 4; rw [hjm] at this; omega
        let x := xFn i
        let E := eFn i m
        have hraw : ∀ t : Nat, (ht : t < 4) ->
            B0 i ⟨4 * m + t, by omega⟩ = ((laurentInterpBinom x t : Nat) : Int) * E := by
          intro t ht
          dsimp [B0, blkSt]
          rw [show (4 * m + t) / 4 = m by omega, show (4 * m + t) % 4 = t by omega,
              ite_false_of_w10 (Nat.lt_irrefl m)]
        rcases hbinom_st x with ⟨hb0, hb1, hb2, hb3⟩
        dsimp only [x] at hb0 hb1 hb2 hb3
        have hn23 : c2 ≠ c3 := by intro h; have := congrArg Fin.val h; dsimp [c2, c3] at this; omega
        have hn32 : c3 ≠ c2 := Ne.symm hn23
        have hn12 : c1 ≠ c2 := by intro h; have := congrArg Fin.val h; dsimp [c1, c2] at this; omega
        have hn13 : c1 ≠ c3 := by intro h; have := congrArg Fin.val h; dsimp [c1, c3] at this; omega
        rcases (by omega : j.val % 4 = 0 ∨ j.val % 4 = 1 ∨ j.val % 4 = 2 ∨ j.val % 4 = 3) with hm0 | hm1 | hm2 | hm3_c
        · let c0_m : Fin N := ⟨4 * m, by omega⟩
          have hjf : j = c0_m := Fin.ext (by dsimp [c0_m]; omega)
          rw [hjf]
          have h02 : c0_m ≠ c2 := by intro h; have := congrArg Fin.val h; dsimp [c0_m, c2] at this; omega
          have h03 : c0_m ≠ c3 := by intro h; have := congrArg Fin.val h; dsimp [c0_m, c3] at this; omega
          change (if c0_m = c3 then _ else B4 i c0_m) = _; rw [ite_false_of_w10 h03]
          change (if c0_m = c3 then _ else B3 i c0_m) = _; rw [ite_false_of_w10 h03]
          change (if c0_m = c2 then _ else B2 i c0_m) = _; rw [ite_false_of_w10 h02]
          change (if c0_m = c3 then _ else B1 i c0_m) = _; rw [ite_false_of_w10 h03]
          change (if c0_m = c2 then _ else B0 i c0_m) = _; rw [ite_false_of_w10 h02]
          have hc0_eq : c0_m = ⟨4 * m + 0, by omega⟩ := Fin.ext (by dsimp [c0_m])
          conv => lhs; rw [hc0_eq, hraw 0 (by decide)]
          dsimp [blkSt, c0_m, x, E]
          rw [show (4 * m) / 4 = m by omega, show (4 * m) % 4 = 0 by omega,
              ite_true_of_w10 (Nat.lt_succ_self m), hb0]
          simp [intPowNat]
        · have hjf : j = c1 := Fin.ext (by dsimp [c1]; rw [hj_rem, hm1])
          rw [hjf]
          change (if c1 = c3 then _ else B4 i c1) = _; rw [ite_false_of_w10 hn13]
          change (if c1 = c3 then _ else B3 i c1) = _; rw [ite_false_of_w10 hn13]
          change (if c1 = c2 then _ else B2 i c1) = _; rw [ite_false_of_w10 hn12]
          change (if c1 = c3 then _ else B1 i c1) = _; rw [ite_false_of_w10 hn13]
          change (if c1 = c2 then _ else B0 i c1) = _; rw [ite_false_of_w10 hn12]
          dsimp only [c1]; rw [hraw 1 (by decide)]
          dsimp [blkSt, x, E]
          rw [show (4 * m + 1) / 4 = m by omega, show (4 * m + 1) % 4 = 1 by omega,
              ite_true_of_w10 (Nat.lt_succ_self m), hb1]
          simp [intPowNat]
        · have hjf : j = c2 := Fin.ext (by dsimp [c2]; rw [hj_rem, hm2])
          rw [hjf]
          change (if c2 = c3 then _ else B4 i c2) = _; rw [ite_false_of_w10 hn23]
          change (if c2 = c3 then _ else B3 i c2) = _; rw [ite_false_of_w10 hn23]
          change (if c2 = c2 then B2 i c2 - (-1) * B2 i c1 else _) = _; rw [ite_true_of_w10 rfl]
          have hb2_c2 : B2 i c2 = 2 * B0 i c2 := by dsimp [B2, B1]; rw [ite_false_of_w10 hn23, ite_true_of_w10 rfl]
          have hb2_c1 : B2 i c1 = B0 i c1 := by dsimp [B2, B1]; rw [ite_false_of_w10 hn13, ite_false_of_w10 hn12]
          rw [hb2_c2, hb2_c1]; dsimp only [c1, c2]; rw [hraw 2 (by decide), hraw 1 (by decide)]
          dsimp [blkSt]; rw [show (4 * m + 2) / 4 = m by omega, show (4 * m + 2) % 4 = 2 by omega,
                             ite_true_of_w10 (Nat.lt_succ_self m), hb1]
          have hb2_int : (2 : Int) * (laurentInterpBinom x 2 : Int) - (-1) * (x : Int) = (x : Int) * (x : Int) := by
            have hc := congrArg (fun n : Nat => (n : Int)) hb2
            simp only [Int.natCast_add, Int.natCast_mul] at hc
            generalize (laurentInterpBinom x 2 : Int) = C2 at hc ⊢
            generalize (x : Int) * (x : Int) = X2 at hc ⊢
            generalize (x : Int) = X1 at hc ⊢
            omega
          calc 2 * ((laurentInterpBinom x 2 : Int) * E) - (-1) * ((x : Int) * E)
              = (2 * (laurentInterpBinom x 2 : Int) - (-1) * (x : Int)) * E := by rw [Int.sub_mul]; ac_rfl
            _ = intPowNat (x : Int) 2 * E := by rw [hb2_int]; simp [intPowNat]
        · have hjf : j = c3 := Fin.ext (by dsimp [c3]; rw [hj_rem, hm3_c])
          rw [hjf]
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
          rw [hraw 3 (by decide), hraw 2 (by decide), hraw 1 (by decide)]
          dsimp [blkSt]; rw [show (4 * m + 3) / 4 = m by omega, show (4 * m + 3) % 4 = 3 by omega,
                             ite_true_of_w10 (Nat.lt_succ_self m), hb1]
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
            _ = intPowNat (x : Int) 3 * E := by rw [hb3_int]; simp [intPowNat]
      · have hn1 : j ≠ c1 := by intro h; apply hjm; rw [h]; dsimp [c1]; omega
        have hn2 : j ≠ c2 := by intro h; apply hjm; rw [h]; dsimp [c2]; omega
        have hn3 : j ≠ c3 := by intro h; apply hjm; rw [h]; dsimp [c3]; omega
        change (if j = c3 then _ else B4 i j) = _; rw [ite_false_of_w10 hn3]
        change (if j = c3 then _ else B3 i j) = _; rw [ite_false_of_w10 hn3]
        change (if j = c2 then _ else B2 i j) = _; rw [ite_false_of_w10 hn2]
        change (if j = c3 then _ else B1 i j) = _; rw [ite_false_of_w10 hn3]
        change (if j = c2 then _ else B0 i j) = _; rw [ite_false_of_w10 hn2]
        dsimp [B0, blkSt]
        by_cases hlt_m : j.val / 4 < m
        · rw [ite_true_of_w10 hlt_m, ite_true_of_w10 (by omega)]
        · rw [ite_false_of_w10 hlt_m, ite_false_of_w10 (by omega)]
    rw [← hB5_eq, hd5, hd4, hd3, hd2, hd1, ← Int.mul_assoc]; rfl
  have hind : ∀ b : Nat, b ≤ U -> ((12 ^ b : Nat) : Int) * intDet N (blkSt (U - b)) = intDet N (blkSt U) := by
    intro b hb; induction b with
    | zero => rw [Nat.sub_zero]; simp
    | succ b' ih =>
      have hm_lt : U - (b' + 1) < U := by omega
      have hsucc : U - (b' + 1) + 1 = U - b' := by omega
      rw [Nat.pow_succ, Int.natCast_mul, Int.mul_assoc,
          show ((12 : Nat) : Int) = 12 from rfl, hstep (U - (b' + 1)) hm_lt, hsucc]
      exact ih (Nat.le_of_lt hb)
  have hmain := hind U (Nat.le_refl U)
  rw [Nat.sub_self] at hmain
  have hb0 : blkSt 0 = (fun i j => ((laurentInterpBinom (xFn i) (j.val % 4) : Nat) : Int) * eFn i (j.val / 4)) := by
    funext i j; simp [blkSt]
  have hbU : blkSt U = (fun i j => intPowNat ((xFn i : Nat) : Int) (j.val % 4) * eFn i (j.val / 4)) := by
    funext i j; dsimp [blkSt]; rw [ite_true_of_w10 (by have := j.isLt; dsimp [N] at this; omega : j.val / 4 < U)]
  rwa [hb0, hbU] at hmain

-- ============================================================================
-- Exact 9-Pivot `Poly3` Upper-Triangular Factorization of `laurentTrop3Mat12`
-- ============================================================================

/-- Resonant quadratic factor `Q_u(W, K) := (2^u - 1)*K^2 + 3*(2^u + 1)*W*K + 2*(2^u - 1)*W^2`
    governing the `3`-adic Newton-polygon / tropical determinant `laurentTrop3Mat12 W K u`. -/
def laurentTrop3ResonantQuad (W K u : Nat) : Nat :=
  (2 ^ u - 1) * (K * K) + 3 * (2 ^ u + 1) * (W * K) + 2 * (2 ^ u - 1) * (W * W)

private abbrev Mono3W19 := Nat × Nat × Nat
private abbrev Poly3W19 := List (Mono3W19 × Int)

private def evalMono3W19 (w k x : Int) (m : Mono3W19) : Int :=
  intPowNat w m.1 * intPowNat k m.2.1 * intPowNat x m.2.2

private def evalPoly3W19 (w k x : Int) : Poly3W19 -> Int
  | [] => 0
  | (m, c) :: rest => c * evalMono3W19 w k x m + evalPoly3W19 w k x rest

private def poly3AddW19 (p q : Poly3W19) : Poly3W19 := p ++ q
private def poly3NegW19 (p : Poly3W19) : Poly3W19 := p.map (fun mc => (mc.1, -mc.2))
private def poly3SubW19 (p q : Poly3W19) : Poly3W19 := poly3AddW19 p (poly3NegW19 q)

private def poly3InsTermW19 (m : Mono3W19) (c : Int) : Poly3W19 -> Poly3W19
  | [] => if c == 0 then [] else [(m, c)]
  | (m', c') :: rest =>
    if c == 0 then (m', c') :: rest
    else if m == m' then
      if c + c' == 0 then rest else (m', c + c') :: rest
    else (m', c') :: poly3InsTermW19 m c rest

private def poly3NormW19 : Poly3W19 -> Poly3W19
  | [] => []
  | (m, c) :: rest => poly3InsTermW19 m c (poly3NormW19 rest)

private def poly3MulTermW19 (m1 : Mono3W19) (c1 : Int) : Poly3W19 -> Poly3W19
  | [] => []
  | (m2, c2) :: rest =>
    ((m1.1 + m2.1, m1.2.1 + m2.2.1, m1.2.2 + m2.2.2), c1 * c2) :: poly3MulTermW19 m1 c1 rest

private def poly3MulRawW19 : Poly3W19 -> Poly3W19 -> Poly3W19
  | [], _ => []
  | (m1, c1) :: rest, q => poly3AddW19 (poly3MulTermW19 m1 c1 q) (poly3MulRawW19 rest q)

private def poly3MulW19 (p q : Poly3W19) : Poly3W19 :=
  poly3NormW19 (poly3MulRawW19 p q)

private def poly3PowW19 (p : Poly3W19) : Nat -> Poly3W19
  | 0 => [((0, 0, 0), 1)]
  | e + 1 => poly3MulW19 p (poly3PowW19 p e)

private theorem evalPoly3W19_add (w k x : Int) :
    ∀ p q : Poly3W19, evalPoly3W19 w k x (poly3AddW19 p q) = evalPoly3W19 w k x p + evalPoly3W19 w k x q
  | [], _ => by simp [poly3AddW19, evalPoly3W19]
  | (m, c) :: rest, q => by
    change c * evalMono3W19 w k x m + evalPoly3W19 w k x (poly3AddW19 rest q) =
      (c * evalMono3W19 w k x m + evalPoly3W19 w k x rest) + evalPoly3W19 w k x q
    rw [evalPoly3W19_add w k x rest q, Int.add_assoc]

private theorem evalPoly3W19_neg (w k x : Int) :
    ∀ p : Poly3W19, evalPoly3W19 w k x (poly3NegW19 p) = -evalPoly3W19 w k x p
  | [] => by simp [poly3NegW19, evalPoly3W19]
  | (m, c) :: rest => by
    change (-c) * evalMono3W19 w k x m + evalPoly3W19 w k x (poly3NegW19 rest) =
      -(c * evalMono3W19 w k x m + evalPoly3W19 w k x rest)
    rw [evalPoly3W19_neg w k x rest, Int.neg_mul]
    omega

private theorem evalPoly3W19_sub (w k x : Int) (p q : Poly3W19) :
    evalPoly3W19 w k x (poly3SubW19 p q) = evalPoly3W19 w k x p - evalPoly3W19 w k x q := by
  unfold poly3SubW19; rw [evalPoly3W19_add, evalPoly3W19_neg]; omega

private theorem evalPoly3W19_insTerm (w k x : Int) (m : Mono3W19) (c : Int) :
    ∀ ps : Poly3W19, evalPoly3W19 w k x (poly3InsTermW19 m c ps) = c * evalMono3W19 w k x m + evalPoly3W19 w k x ps
  | [] => by
    unfold poly3InsTermW19
    by_cases hc : c = 0
    · subst hc; simp [evalPoly3W19]
    · rw [beq_false_of_ne hc]; simp [evalPoly3W19]
  | (m', c') :: rest => by
    unfold poly3InsTermW19
    by_cases hc : c = 0
    · subst hc; simp [evalPoly3W19]
    · rw [beq_false_of_ne hc]; simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hm : m = m'
      · subst hm; simp only [beq_self_eq_true, ↓reduceIte]
        by_cases hsum : c + c' = 0
        · rw [beq_iff_eq.mpr hsum]; simp only [↓reduceIte, evalPoly3W19]
          have : c * evalMono3W19 w k x m + c' * evalMono3W19 w k x m = (c + c') * evalMono3W19 w k x m :=
            (Int.add_mul c c' _).symm
          rw [← Int.add_assoc, this, hsum, Int.zero_mul, Int.zero_add]
        · rw [beq_false_of_ne hsum]; simp only [Bool.false_eq_true, ↓reduceIte, evalPoly3W19, Int.add_mul, Int.add_assoc]
      · rw [beq_false_of_ne hm]; simp only [Bool.false_eq_true, ↓reduceIte, evalPoly3W19,
                                             evalPoly3W19_insTerm w k x m c rest]
        ac_rfl

private theorem evalPoly3W19_norm (w k x : Int) :
    ∀ p : Poly3W19, evalPoly3W19 w k x (poly3NormW19 p) = evalPoly3W19 w k x p
  | [] => rfl
  | (m, c) :: rest => by
    unfold poly3NormW19
    rw [evalPoly3W19_insTerm, evalPoly3W19_norm w k x rest]; rfl

private theorem evalMono3W19_add (w k x : Int) (m1 m2 : Mono3W19) :
    evalMono3W19 w k x (m1.1 + m2.1, m1.2.1 + m2.2.1, m1.2.2 + m2.2.2) =
      evalMono3W19 w k x m1 * evalMono3W19 w k x m2 := by
  unfold evalMono3W19
  dsimp only
  rw [intPowNat_add w m1.1 m2.1, intPowNat_add k m1.2.1 m2.2.1, intPowNat_add x m1.2.2 m2.2.2]
  ac_rfl

private theorem evalPoly3W19_mulTerm (w k x : Int) (m1 : Mono3W19) (c1 : Int) :
    ∀ q : Poly3W19,
      evalPoly3W19 w k x (poly3MulTermW19 m1 c1 q) = c1 * evalMono3W19 w k x m1 * evalPoly3W19 w k x q
  | [] => by simp [poly3MulTermW19, evalPoly3W19]
  | (m2, c2) :: rest => by
    simp only [poly3MulTermW19, evalPoly3W19, evalPoly3W19_mulTerm w k x m1 c1 rest,
               evalMono3W19_add, Int.mul_add]
    congr 1; ac_rfl

private theorem evalPoly3W19_mul (w k x : Int) (p q : Poly3W19) :
    evalPoly3W19 w k x (poly3MulW19 p q) = evalPoly3W19 w k x p * evalPoly3W19 w k x q := by
  unfold poly3MulW19
  rw [evalPoly3W19_norm]
  induction p with
  | nil => simp [poly3MulRawW19, evalPoly3W19]
  | cons mc rest ih =>
    rcases mc with ⟨m1, c1⟩
    simp only [poly3MulRawW19, evalPoly3W19_add, evalPoly3W19_mulTerm, evalPoly3W19, ih, Int.add_mul]

private theorem evalPoly3W19_pow (w k x : Int) (p : Poly3W19) :
    ∀ e : Nat, evalPoly3W19 w k x (poly3PowW19 p e) = intPowNat (evalPoly3W19 w k x p) e
  | 0 => by simp [poly3PowW19, evalPoly3W19, evalMono3W19, intPowNat]
  | e + 1 => by
    simp only [poly3PowW19, intPowNat, evalPoly3W19_mul, evalPoly3W19_pow w k x p e]

private def poly3EqBoolW19 (p q : Poly3W19) : Bool :=
  poly3NormW19 (poly3SubW19 p q) == []

private theorem poly3EqBoolW19_sound (w k x : Int) (p q : Poly3W19)
    (h : poly3EqBoolW19 p q = true) :
    evalPoly3W19 w k x p = evalPoly3W19 w k x q := by
  have h0 : poly3NormW19 (poly3SubW19 p q) = [] := beq_iff_eq.mp h
  have he := evalPoly3W19_norm w k x (poly3SubW19 p q)
  rw [h0, evalPoly3W19_sub] at he
  change 0 = evalPoly3W19 w k x p - evalPoly3W19 w k x q at he
  omega

private def poly3At1DW19 : List Poly3W19 -> Nat -> Poly3W19
  | [], _ => []
  | x :: _, 0 => x
  | _ :: xs, k + 1 => poly3At1DW19 xs k

private def poly3At2DW19 : List (List Poly3W19) -> Nat -> Nat -> Poly3W19
  | [], _, _ => []
  | r :: _, 0, c => poly3At1DW19 r c
  | _ :: rs, r + 1, c => poly3At2DW19 rs r c

private def buildRow12Poly3W19 (f : Nat -> Poly3W19) : List Poly3W19 :=
  [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11]

private def buildMat12Poly3W19 (f : Nat -> Nat -> Poly3W19) : List (List Poly3W19) :=
  [buildRow12Poly3W19 (f 0), buildRow12Poly3W19 (f 1), buildRow12Poly3W19 (f 2), buildRow12Poly3W19 (f 3),
   buildRow12Poly3W19 (f 4), buildRow12Poly3W19 (f 5), buildRow12Poly3W19 (f 6), buildRow12Poly3W19 (f 7),
   buildRow12Poly3W19 (f 8), buildRow12Poly3W19 (f 9), buildRow12Poly3W19 (f 10), buildRow12Poly3W19 (f 11)]

private theorem poly3At2DW19_buildMat12 (f : Nat -> Nat -> Poly3W19) (r c : Nat) (hr : r < 12) (hc : c < 12) :
    poly3At2DW19 (buildMat12Poly3W19 f) r c = f r c := by
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨
      r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  (rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨
      c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 ∨ c = 10 ∨ c = 11) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)

/-- Explicit row `3`-adic shift `a_row(s)` (`3, 1, 0, 0` for `s = 0, 1, 2, 3`) for `12 × 12` tropical congruence. -/
def aRow3TropExplicit (s : Nat) : Nat := match s with | 0 => 3 | 1 => 1 | _ => 0

/-- Explicit column `3`-adic shift `b_col(m)` (`0, 2, 3` for `m = 0, 1, 2`) for `12 × 12` tropical congruence. -/
def bCol3TropExplicit (m : Nat) : Nat := match m with | 0 => 0 | 1 => 2 | _ => 3

/-- Explicit `3`-adic active-block predicate `s * m + a_row(s) == b_col(m)` on `(s, m) ∈ Fin 4 × Fin 3`. -/
def trop3ActiveBoolExplicit (s m : Nat) : Bool := (s * m + aRow3TropExplicit s == bCol3TropExplicit m)

/-- Transparent leading `3 ^ (8 * u)` Newton-polygon / tropical integer matrix of `laurentTwoBaseT4U3Mat12 W K u`. -/
def laurentTrop3Mat12Explicit (W K u : Nat) (i j : Fin 12) : Int :=
  let r := i.val % 3; let s := i.val / 3
  let t := j.val % 4; let m := j.val / 4
  if trop3ActiveBoolExplicit s m then
    Int.ofNat (laurentInterpBinom (r * W + s * K) t * 2 ^ (r * (m * u)))
  else 0

private theorem intDet_scale_row0_w19 (L : Nat) (c : Int) (A : Fin (L + 1) -> Fin (L + 1) -> Int) :
    intDet (L + 1) (fun i j => if i.val = 0 then c * A i j else A i j) = c * intDet (L + 1) A := by
  let B : Fin (L + 1) -> Fin (L + 1) -> Int := fun i j => if i.val = 0 then c * A i j else A i j
  have hsub : ∀ j : Fin (L + 1), intSubMat B j = intSubMat A j := by
    intro j; funext r col; unfold intSubMat; simp [B]
  change intDet (L + 1) B = c * intDet (L + 1) A
  simp only [intDet, intSumFin]
  have hst : ∀ m : Nat, m ≤ L + 1 ->
      intSumPrefix (L + 1) (fun j => (if j.val % 2 = 0 then 1 else -1) * B ⟨0, Nat.zero_lt_succ L⟩ j * intDet L (intSubMat B j)) m =
        c * intSumPrefix (L + 1) (fun j => (if j.val % 2 = 0 then 1 else -1) * A ⟨0, Nat.zero_lt_succ L⟩ j * intDet L (intSubMat A j)) m := by
    intro m hm; induction m with
    | zero => simp [intSumPrefix]
    | succ m' ih =>
      have hm_lt : m' < L + 1 := hm
      conv => lhs; unfold intSumPrefix
      simp only [hm_lt, dite_true]
      rw [ih (Nat.le_of_lt hm), hsub ⟨m', hm_lt⟩]
      conv => rhs; rhs; unfold intSumPrefix
      simp only [hm_lt, dite_true, Int.mul_add]
      have hB0 : B ⟨0, Nat.zero_lt_succ L⟩ ⟨m', hm_lt⟩ = c * A ⟨0, Nat.zero_lt_succ L⟩ ⟨m', hm_lt⟩ := rfl
      rw [hB0]; ac_rfl
  exact hst (L + 1) (Nat.le_refl _)

private theorem intDet_scale_row_w19 (c : Int) :
    ∀ (L r0 : Nat) (_hr : r0 < L) (A : Fin L -> Fin L -> Int),
      intDet L (fun i j => if i.val = r0 then c * A i j else A i j) = c * intDet L A
  | 0, _, hr, _ => by omega
  | m + 1, 0, _, A => intDet_scale_row0_w19 m c A
  | m + 1, r' + 1, hr, A => by
    let B : Fin (m + 1) -> Fin (m + 1) -> Int := fun i j => if i.val = r' + 1 then c * A i j else A i j
    change intDet (m + 1) B = c * intDet (m + 1) A
    simp only [intDet, intSumFin]
    have hsub : ∀ j : Fin (m + 1),
        intDet m (intSubMat B j) = c * intDet m (intSubMat A j) := by
      intro j
      have heq_s : intSubMat B j = (fun r col => if r.val = r' then c * intSubMat A j r col else intSubMat A j r col) := by
        funext r col; unfold intSubMat; dsimp [B]
        by_cases hre : r.val = r'
        · rw [ite_true_of_w10 (by omega : r.val + 1 = r' + 1), ite_true_of_w10 hre]
        · rw [ite_false_of_w10 (by omega : r.val + 1 ≠ r' + 1), ite_false_of_w10 hre]
      rw [heq_s]; exact intDet_scale_row_w19 c m r' (by omega) (intSubMat A j)
    have hst : ∀ k : Nat, k ≤ m + 1 ->
        intSumPrefix (m + 1) (fun j => (if j.val % 2 = 0 then 1 else -1) * B ⟨0, Nat.zero_lt_succ m⟩ j * intDet m (intSubMat B j)) k =
          c * intSumPrefix (m + 1) (fun j => (if j.val % 2 = 0 then 1 else -1) * A ⟨0, Nat.zero_lt_succ m⟩ j * intDet m (intSubMat A j)) k := by
      intro k hk; induction k with
      | zero => simp [intSumPrefix]
      | succ k' ih =>
        have hk_lt : k' < m + 1 := hk
        conv => lhs; unfold intSumPrefix
        simp only [hk_lt, dite_true]
        rw [ih (Nat.le_of_lt hk), hsub ⟨k', hk_lt⟩]
        conv => rhs; rhs; unfold intSumPrefix
        simp only [hk_lt, dite_true, Int.mul_add]
        have hB0 : B ⟨0, Nat.zero_lt_succ m⟩ ⟨k', hk_lt⟩ = A ⟨0, Nat.zero_lt_succ m⟩ ⟨k', hk_lt⟩ := rfl
        rw [hB0]; ac_rfl
    exact hst (m + 1) (Nat.le_refl _)

private def rowPrefExp3TropW19 (u : Nat) : Nat -> Nat
  | 0 => 0
  | r + 1 => aRow3TropExplicit (r / 3) * u + rowPrefExp3TropW19 u r

private def colPrefExp3TropW19 (u : Nat) : Nat -> Nat
  | 0 => 0
  | c + 1 => bCol3TropExplicit (c / 4) * u + colPrefExp3TropW19 u c

private theorem det12_t4u3_3adic_congr_w19 (W K u : Nat) :
    Int.ofNat (3 ^ (9 * u)) ∣
      (intDet 12 (laurentTwoBaseT4U3Mat12 W K u) -
        Int.ofNat (3 ^ (8 * u)) * intDet 12 (laurentTrop3Mat12Explicit W K u)) := by
  have hmul_ofNat : ∀ a b : Nat, Int.ofNat (a * b) = Int.ofNat a * Int.ofNat b := Int.natCast_mul
  let aRow := aRow3TropExplicit
  let bCol := bCol3TropExplicit
  let M_trop3 : Fin 12 -> Fin 12 -> Int := fun i j =>
    let r := i.val % 3; let s := i.val / 3
    let t := j.val % 4; let m := j.val / 4
    let e3 := (s * m + aRow s - bCol m) * u
    Int.ofNat (laurentInterpBinom (r * W + s * K) t * (2 ^ (r * (m * u)) * 3 ^ e3))
  let rowPrefExp := rowPrefExp3TropW19 u
  let colPrefExp := colPrefExp3TropW19 u
  let M_row (r_done : Nat) (i j : Fin 12) : Int :=
    if i.val < r_done then Int.ofNat (3 ^ (aRow (i.val / 3) * u)) * laurentTwoBaseT4U3Mat12 W K u i j
    else laurentTwoBaseT4U3Mat12 W K u i j
  have hrow_ind : ∀ n : Nat, n ≤ 12 ->
      intDet 12 (M_row n) = Int.ofNat (3 ^ rowPrefExp n) * intDet 12 (M_row 0) := by
    intro n; induction n with
    | zero => intro _; rw [show Int.ofNat (3 ^ rowPrefExp 0) = 1 from rfl, Int.one_mul]
    | succ n' ih =>
      intro hn
      have heq_r : M_row (n' + 1) = (fun i j =>
          if i.val = n' then Int.ofNat (3 ^ (aRow (n' / 3) * u)) * M_row n' i j else M_row n' i j) := by
        funext i j
        by_cases hi : i.val = n'
        · dsimp [M_row]; rw [ite_true_of_w10 (by omega : i.val < n' + 1), ite_true_of_w10 hi,
                              ite_false_of_w10 (by omega : ¬ (i.val < n')), hi]
        · dsimp [M_row]; rw [ite_false_of_w10 hi]
          by_cases hlt : i.val < n'
          · rw [ite_true_of_w10 (by omega), ite_true_of_w10 hlt]
          · rw [ite_false_of_w10 (by omega), ite_false_of_w10 hlt]
      rw [heq_r, intDet_scale_row_w19 _ 12 n' hn, ih (Nat.le_of_lt hn), ← Int.mul_assoc,
          ← hmul_ofNat, ← Nat.pow_add]; rfl
  let M_col (c_done : Nat) (i j : Fin 12) : Int :=
    if j.val < c_done then Int.ofNat (3 ^ (bCol (j.val / 4) * u)) * M_trop3 i j
    else M_trop3 i j
  have hcol_ind : ∀ n : Nat, n ≤ 12 ->
      intDet 12 (M_col n) = Int.ofNat (3 ^ colPrefExp n) * intDet 12 (M_col 0) := by
    intro n; induction n with
    | zero => intro _; rw [show Int.ofNat (3 ^ colPrefExp 0) = 1 from rfl, Int.one_mul]
    | succ n' ih =>
      intro hn
      let jn : Fin 12 := ⟨n', hn⟩
      have heq_c : M_col (n' + 1) = (fun i j =>
          if j = jn then Int.ofNat (3 ^ (bCol (n' / 4) * u)) * M_col n' i jn else M_col n' i j) := by
        funext i j
        by_cases hj : j = jn
        · subst hj; dsimp [M_col, jn]
          rw [ite_true_of_w10 (Nat.lt_succ_self n'), ite_true_of_w10 rfl, ite_false_of_w10 (Nat.lt_irrefl n')]
        · dsimp [M_col]; rw [ite_false_of_w10 hj]
          have hjv : j.val ≠ n' := fun hv => hj (Fin.ext hv)
          by_cases hlt : j.val < n'
          · rw [ite_true_of_w10 (by omega), ite_true_of_w10 hlt]
          · rw [ite_false_of_w10 (by omega), ite_false_of_w10 hlt]
      rw [heq_c, intDet_col_scale _ 12 jn, ih (Nat.le_of_lt hn), ← Int.mul_assoc,
          ← hmul_ofNat, ← Nat.pow_add]; rfl
  have hMrow_eq_Mcol : M_row 12 = M_col 12 := by
    funext i j
    dsimp only [M_row, M_col]
    rw [ite_true_of_w10 i.isLt, ite_true_of_w10 j.isLt]
    dsimp only [M_trop3]; unfold laurentTwoBaseT4U3Mat12 laurentInterpMat laurentInterpEntry
      laurentRowsTwoBase12 laurentColsT4U3_12
    dsimp only
    have hl_eq : Int.ofNat (laurentInterpBinom (i.val % 3 * W + i.val / 3 * K) (j.val % 4) *
        2 ^ (i.val % 3 * (j.val / 4 * u)) * 3 ^ (i.val / 3 * (j.val / 4 * u))) =
      ((laurentInterpBinom (i.val % 3 * W + i.val / 3 * K) (j.val % 4) *
        2 ^ (i.val % 3 * (j.val / 4 * u)) * 3 ^ (i.val / 3 * (j.val / 4 * u)) : Nat) : Int) := rfl
    rw [← hl_eq, ← hmul_ofNat, ← hmul_ofNat]
    apply congrArg Int.ofNat
    have hexp_eq : bCol (j.val / 4) * u + (i.val / 3 * (j.val / 4) + aRow (i.val / 3) - bCol (j.val / 4)) * u =
        aRow (i.val / 3) * u + i.val / 3 * (j.val / 4 * u) := by
      have hge : bCol (j.val / 4) ≤ i.val / 3 * (j.val / 4) + aRow (i.val / 3) := by
        rcases (by have := i.isLt; omega : i.val / 3 = 0 ∨ i.val / 3 = 1 ∨ i.val / 3 = 2 ∨ i.val / 3 = 3) with
          hs | hs | hs | hs <;>
        rcases (by have := j.isLt; omega : j.val / 4 = 0 ∨ j.val / 4 = 1 ∨ j.val / 4 = 2) with hm | hm | hm <;>
        simp [aRow, bCol, aRow3TropExplicit, bCol3TropExplicit, hs, hm]
      have h1 : bCol (j.val / 4) + (i.val / 3 * (j.val / 4) + aRow (i.val / 3) - bCol (j.val / 4)) =
          aRow (i.val / 3) + i.val / 3 * (j.val / 4) := by omega
      calc bCol (j.val / 4) * u + (i.val / 3 * (j.val / 4) + aRow (i.val / 3) - bCol (j.val / 4)) * u
          = (bCol (j.val / 4) + (i.val / 3 * (j.val / 4) + aRow (i.val / 3) - bCol (j.val / 4))) * u :=
            (Nat.add_mul _ _ _).symm
        _ = (aRow (i.val / 3) + i.val / 3 * (j.val / 4)) * u := by rw [h1]
        _ = aRow (i.val / 3) * u + i.val / 3 * (j.val / 4 * u) := by rw [Nat.add_mul, Nat.mul_assoc]
    calc 3 ^ (aRow (i.val / 3) * u) *
           (laurentInterpBinom (i.val % 3 * W + i.val / 3 * K) (j.val % 4) *
             2 ^ (i.val % 3 * (j.val / 4 * u)) * 3 ^ (i.val / 3 * (j.val / 4 * u)))
        = laurentInterpBinom (i.val % 3 * W + i.val / 3 * K) (j.val % 4) *
            2 ^ (i.val % 3 * (j.val / 4 * u)) *
            (3 ^ (aRow (i.val / 3) * u) * 3 ^ (i.val / 3 * (j.val / 4 * u))) := by ac_rfl
      _ = laurentInterpBinom (i.val % 3 * W + i.val / 3 * K) (j.val % 4) *
            2 ^ (i.val % 3 * (j.val / 4 * u)) *
            3 ^ (aRow (i.val / 3) * u + i.val / 3 * (j.val / 4 * u)) := by rw [← Nat.pow_add]
      _ = laurentInterpBinom (i.val % 3 * W + i.val / 3 * K) (j.val % 4) *
            2 ^ (i.val % 3 * (j.val / 4 * u)) *
            (3 ^ (bCol (j.val / 4) * u) *
             3 ^ ((i.val / 3 * (j.val / 4) + aRow (i.val / 3) - bCol (j.val / 4)) * u)) := by
            rw [← hexp_eq, Nat.pow_add]
      _ = 3 ^ (bCol (j.val / 4) * u) *
            (laurentInterpBinom (i.val % 3 * W + i.val / 3 * K) (j.val % 4) *
              (2 ^ (i.val % 3 * (j.val / 4 * u)) *
               3 ^ ((i.val / 3 * (j.val / 4) + aRow (i.val / 3) - bCol (j.val / 4)) * u))) := by ac_rfl
  have hrow12_exp : rowPrefExp 12 = 12 * u := by
    simp [rowPrefExp, rowPrefExp3TropW19, aRow3TropExplicit]; omega
  have hcol12_exp : colPrefExp 12 = 20 * u := by
    simp [colPrefExp, colPrefExp3TropW19, bCol3TropExplicit]; omega
  have hr0 : M_row 0 = laurentTwoBaseT4U3Mat12 W K u := by funext i j; simp [M_row]
  have hc0 : M_col 0 = M_trop3 := by funext i j; simp [M_col]
  have hscale_rel : intDet 12 (laurentTwoBaseT4U3Mat12 W K u) =
      Int.ofNat (3 ^ (8 * u)) * intDet 12 M_trop3 := by
    have heq12 := hrow_ind 12 (Nat.le_refl 12)
    rw [hMrow_eq_Mcol, hcol_ind 12 (Nat.le_refl 12), hrow12_exp, hcol12_exp, hr0, hc0] at heq12
    have h20 : Int.ofNat (3 ^ (20 * u)) = Int.ofNat (3 ^ (12 * u)) * Int.ofNat (3 ^ (8 * u)) := by
      rw [← hmul_ofNat, ← Nat.pow_add, show 12 * u + 8 * u = 20 * u by omega]
    rw [h20, Int.mul_assoc] at heq12
    have hp12_nz : Int.ofNat (3 ^ (12 * u)) ≠ 0 := by
      intro hz; injection hz with h0
      have hp := nat_pow_pos_of_pos 3 (by decide) (12 * u); omega
    exact Int.eq_of_mul_eq_mul_left hp12_nz heq12.symm
  have hdvd_trop3 : Int.ofNat (3 ^ u) ∣ (intDet 12 M_trop3 - intDet 12 (laurentTrop3Mat12Explicit W K u)) := by
    apply intDet_congr_dvd (Int.ofNat (3 ^ u)) 12
    intro i j
    change Int.ofNat (3 ^ u) ∣
      (Int.ofNat (laurentInterpBinom (i.val % 3 * W + i.val / 3 * K) (j.val % 4) *
        (2 ^ (i.val % 3 * (j.val / 4 * u)) *
         3 ^ ((i.val / 3 * (j.val / 4) + aRow3TropExplicit (i.val / 3) - bCol3TropExplicit (j.val / 4)) * u))) -
       if trop3ActiveBoolExplicit (i.val / 3) (j.val / 4) then
         Int.ofNat (laurentInterpBinom (i.val % 3 * W + i.val / 3 * K) (j.val % 4) *
           2 ^ (i.val % 3 * (j.val / 4 * u)))
       else 0)
    by_cases hact : trop3ActiveBoolExplicit (i.val / 3) (j.val / 4) = true
    · rw [ite_true_of_w10 hact]
      have he0 : (i.val / 3 * (j.val / 4) + aRow3TropExplicit (i.val / 3) - bCol3TropExplicit (j.val / 4)) * u = 0 := by
        unfold trop3ActiveBoolExplicit at hact
        have heq := beq_iff_eq.mp hact
        rw [show i.val / 3 * (j.val / 4) + aRow3TropExplicit (i.val / 3) - bCol3TropExplicit (j.val / 4) = 0 by omega,
            Nat.zero_mul]
      rw [he0, Nat.pow_zero, Nat.mul_one, Int.sub_self]
      exact ⟨0, (Int.mul_zero _).symm⟩
    · rw [ite_false_of_w10 hact, Int.sub_zero]
      have hpos_gap : i.val / 3 * (j.val / 4) + aRow3TropExplicit (i.val / 3) - bCol3TropExplicit (j.val / 4) ≥ 1 := by
        unfold trop3ActiveBoolExplicit at hact
        rcases (by have := i.isLt; omega : i.val / 3 = 0 ∨ i.val / 3 = 1 ∨ i.val / 3 = 2 ∨ i.val / 3 = 3) with
          hs | hs | hs | hs <;>
        rcases (by have := j.isLt; omega : j.val / 4 = 0 ∨ j.val / 4 = 1 ∨ j.val / 4 = 2) with hm | hm | hm <;>
        (rw [hs, hm] at hact ⊢; simp [aRow3TropExplicit, bCol3TropExplicit] at hact ⊢)
      let eg := i.val / 3 * (j.val / 4) + aRow3TropExplicit (i.val / 3) - bCol3TropExplicit (j.val / 4)
      refine ⟨Int.ofNat (laurentInterpBinom (i.val % 3 * W + i.val / 3 * K) (j.val % 4) *
          2 ^ (i.val % 3 * (j.val / 4 * u)) * 3 ^ ((eg - 1) * u)), ?_⟩
      rw [← hmul_ofNat]; apply congrArg Int.ofNat
      have heg : eg * u = u + (eg - 1) * u := by
        conv => lhs; rw [show eg = 1 + (eg - 1) by dsimp [eg]; omega, Nat.add_mul, Nat.one_mul]
      change laurentInterpBinom (i.val % 3 * W + i.val / 3 * K) (j.val % 4) *
          (2 ^ (i.val % 3 * (j.val / 4 * u)) * 3 ^ (eg * u)) =
        3 ^ u * (laurentInterpBinom (i.val % 3 * W + i.val / 3 * K) (j.val % 4) *
          2 ^ (i.val % 3 * (j.val / 4 * u)) * 3 ^ ((eg - 1) * u))
      rw [heg, Nat.pow_add 3 u ((eg - 1) * u)]
      ac_rfl
  rcases hdvd_trop3 with ⟨q3, hq3⟩
  refine ⟨q3, ?_⟩
  have hcast_9u : Int.ofNat (3 ^ (9 * u)) = Int.ofNat (3 ^ (8 * u)) * Int.ofNat (3 ^ u) := by
    rw [← hmul_ofNat, ← Nat.pow_add, show 8 * u + u = 9 * u by omega]
  rw [hscale_rel, hcast_9u, Int.mul_assoc, ← hq3, Int.mul_sub]

private def trop3PowMat12W19 (w k X : Int) (i j : Fin 12) : Int :=
  let r := i.val % 3; let s := i.val / 3
  let t := j.val % 4; let m := j.val / 4
  if trop3ActiveBoolExplicit s m then intPowNat ((r : Int) * w + (s : Int) * k) t * intPowNat X (r * m)
  else 0

private def trop3EntryPoly3W19 (i j : Nat) : Poly3W19 :=
  let r := i % 3; let s := i / 3
  let t := j % 4; let m := j / 4
  if trop3ActiveBoolExplicit s m then
    let lin : Poly3W19 := [((1, 0, 0), (r : Int)), ((0, 1, 0), (s : Int))]
    poly3MulW19 (poly3PowW19 lin t) [((0, 0, r * m), 1)]
  else []

private theorem evalPoly3W19_trop3Entry (w k X : Int) (i j : Fin 12) :
    evalPoly3W19 w k X (trop3EntryPoly3W19 i.val j.val) = trop3PowMat12W19 w k X i j := by
  unfold trop3EntryPoly3W19 trop3PowMat12W19
  dsimp only
  let r : Nat := i.val % 3
  let s : Nat := i.val / 3
  by_cases ha : trop3ActiveBoolExplicit s (j.val / 4) = true
  · rw [ite_true_of_w10 ha, ite_true_of_w10 ha, evalPoly3W19_mul, evalPoly3W19_pow]
    have hlin : evalPoly3W19 w k X [((1, 0, 0), (r : Int)), ((0, 1, 0), (s : Int))] =
        (r : Int) * w + (s : Int) * k := by
      simp [evalPoly3W19, evalMono3W19, intPowNat]
    have hx : evalPoly3W19 w k X [((0, 0, r * (j.val / 4)), 1)] =
        intPowNat X (r * (j.val / 4)) := by
      simp [evalPoly3W19, evalMono3W19, intPowNat]
    rw [hlin, hx]
  · rw [ite_false_of_w10 ha, ite_false_of_w10 ha]; rfl

private def applySignedSwapsPoly3W19 : List (Nat × Nat) -> List (List Poly3W19) -> List (List Poly3W19)
  | [], M => M
  | (c1, c2) :: rest, M =>
    let M' :=
      if Nat.ble (c1 + 1) 12 && Nat.ble (c2 + 1) 12 && (c1 != c2) then
        buildMat12Poly3W19 (fun r j =>
          if j == c1 then poly3At2DW19 M r c2
          else if j == c2 then poly3NegW19 (poly3At2DW19 M r c1)
          else poly3At2DW19 M r j)
      else M
    applySignedSwapsPoly3W19 rest M'

private theorem eval_applySignedSwapsPoly3W19 (w k X : Int) :
    ∀ (swaps : List (Nat × Nat)) (M : List (List Poly3W19)),
      applySignedSwapsIntW19 12 swaps (fun i j => evalPoly3W19 w k X (poly3At2DW19 M i.val j.val)) =
        (fun i j => evalPoly3W19 w k X (poly3At2DW19 (applySignedSwapsPoly3W19 swaps M) i.val j.val))
  | [], _ => rfl
  | (c1, c2) :: rest, M => by
    unfold applySignedSwapsIntW19 applySignedSwapsPoly3W19
    by_cases h : c1 < 12 ∧ c2 < 12 ∧ c1 ≠ c2
    · have hb : (Nat.ble (c1 + 1) 12 && Nat.ble (c2 + 1) 12 && (c1 != c2)) = true := by
        rw [Nat.ble_eq.mpr h.1, Nat.ble_eq.mpr h.2.1, bne_iff_ne.mpr h.2.2]; rfl
      rw [dite_pos_w19 h, hb]; simp only [↓reduceIte]
      have hstep :
          (fun i j : Fin 12 =>
            if j = ⟨c1, h.1⟩ then evalPoly3W19 w k X (poly3At2DW19 M i.val c2)
            else if j = ⟨c2, h.2.1⟩ then -evalPoly3W19 w k X (poly3At2DW19 M i.val c1)
            else evalPoly3W19 w k X (poly3At2DW19 M i.val j.val)) =
          (fun i j : Fin 12 =>
            evalPoly3W19 w k X (poly3At2DW19 (buildMat12Poly3W19 (fun r q =>
              if q == c1 then poly3At2DW19 M r c2
              else if q == c2 then poly3NegW19 (poly3At2DW19 M r c1)
              else poly3At2DW19 M r q)) i.val j.val)) := by
        funext i j
        rw [poly3At2DW19_buildMat12 _ i.val j.val i.isLt j.isLt]
        by_cases hj1 : j = ⟨c1, h.1⟩
        · subst hj1; simp
        · have hb1 : (j.val == c1) = false := beq_false_of_ne (fun hv => hj1 (Fin.ext hv))
          by_cases hj2 : j = ⟨c2, h.2.1⟩
          · subst hj2; simp [hj1, hb1, evalPoly3W19_neg]
          · have hb2 : (j.val == c2) = false := beq_false_of_ne (fun hv => hj2 (Fin.ext hv))
            simp [hj1, hj2, hb1, hb2]
      rw [hstep]
      exact eval_applySignedSwapsPoly3W19 w k X rest _
    · have hb : (Nat.ble (c1 + 1) 12 && Nat.ble (c2 + 1) 12 && (c1 != c2)) = false := by
        cases h0 : (Nat.ble (c1 + 1) 12 && Nat.ble (c2 + 1) 12 && (c1 != c2))
        · rfl
        · rcases bool_and_split h0 with ⟨h12, h3⟩
          rcases bool_and_split h12 with ⟨h1, h2⟩
          exact False.elim (h ⟨Nat.ble_eq.mp h1, Nat.ble_eq.mp h2, bne_iff_ne.mp h3⟩)
      rw [dite_neg_w19 h, hb]; simp only [Bool.false_eq_true, ↓reduceIte]
      exact eval_applySignedSwapsPoly3W19 w k X rest M

private def dotPrefixPoly3W19 (M U : List (List Poly3W19)) (r c : Nat) : Nat -> Poly3W19
  | 0 => []
  | n + 1 =>
    poly3NormW19 (poly3AddW19 (dotPrefixPoly3W19 M U r c n)
      (poly3MulW19 (poly3At2DW19 M r n) (poly3At2DW19 U n c)))

private theorem eval_dotPrefixPoly3W19 (w k X : Int) (M U : List (List Poly3W19)) (r c : Fin 12) :
    ∀ n : Nat, n ≤ 12 ->
      evalPoly3W19 w k X (dotPrefixPoly3W19 M U r.val c.val n) =
        intSumPrefix 12 (fun q => evalPoly3W19 w k X (poly3At2DW19 M r.val q.val) *
          evalPoly3W19 w k X (poly3At2DW19 U q.val c.val)) n
  | 0, _ => rfl
  | n + 1, hn => by
    have hn_lt : n < 12 := hn
    unfold dotPrefixPoly3W19
    rw [evalPoly3W19_norm, evalPoly3W19_add, evalPoly3W19_mul,
        eval_dotPrefixPoly3W19 w k X M U r c n (Nat.le_of_lt hn)]
    simp only [intSumPrefix, hn_lt, dite_true]

private def diagProdPoly3W19 (T : List (List Poly3W19)) : Nat -> Poly3W19
  | 0 => [((0, 0, 0), 1)]
  | m + 1 => poly3MulW19 (diagProdPoly3W19 T m) (poly3At2DW19 T m m)

private theorem eval_diagProdPoly3W19 (w k X : Int) (T : List (List Poly3W19)) :
    ∀ m : Nat, m ≤ 12 ->
      evalPoly3W19 w k X (diagProdPoly3W19 T m) =
        intDiagProdPrefixW19 12 (fun i j => evalPoly3W19 w k X (poly3At2DW19 T i.val j.val)) m
  | 0, _ => by simp [diagProdPoly3W19, intDiagProdPrefixW19, evalPoly3W19, evalMono3W19, intPowNat]
  | m + 1, hm => by
    have hm_lt : m < 12 := hm
    unfold diagProdPoly3W19
    rw [evalPoly3W19_mul, eval_diagProdPoly3W19 w k X T m (Nat.le_of_lt hm)]
    simp only [intDiagProdPrefixW19, hm_lt, dite_true]

private def det3TailPoly3W19 (P : List (List Poly3W19)) : Poly3W19 :=
  let b (i j : Nat) := poly3At2DW19 P (9 + i) (9 + j)
  poly3AddW19
    (poly3SubW19
      (poly3MulW19 (b 0 0) (poly3SubW19 (poly3MulW19 (b 1 1) (b 2 2)) (poly3MulW19 (b 1 2) (b 2 1))))
      (poly3MulW19 (b 0 1) (poly3SubW19 (poly3MulW19 (b 1 0) (b 2 2)) (poly3MulW19 (b 1 2) (b 2 0)))))
    (poly3MulW19 (b 0 2) (poly3SubW19 (poly3MulW19 (b 1 0) (b 2 1)) (poly3MulW19 (b 1 1) (b 2 0))))

private def poly3RowAtW19 : List (List Poly3W19) -> Nat -> List Poly3W19
  | [], _ => []
  | r :: _, 0 => r
  | _ :: rs, r + 1 => poly3RowAtW19 rs r

private theorem poly3At2DW19_eq_rowAt :
    ∀ (M : List (List Poly3W19)) (r c : Nat),
      poly3At2DW19 M r c = poly3At1DW19 (poly3RowAtW19 M r) c
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: rs, r' + 1, c => poly3At2DW19_eq_rowAt rs r' c

private theorem poly3At1DW19_buildRow12 (f : Nat -> Poly3W19) (c : Nat) (hc : c < 12) :
    poly3At1DW19 (buildRow12Poly3W19 f) c = f c := by
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨
      c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 ∨ c = 10 ∨ c = 11) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private def poly3RowEqBoolW19 : List Poly3W19 -> List Poly3W19 -> Bool
  | [], [] => true
  | p :: ps, q :: qs => poly3EqBoolW19 p q && poly3RowEqBoolW19 ps qs
  | _, _ => false

private theorem poly3RowEqBoolW19_sound (w k x : Int) :
    ∀ (r1 r2 : List Poly3W19) (c : Nat),
      poly3RowEqBoolW19 r1 r2 = true ->
      evalPoly3W19 w k x (poly3At1DW19 r1 c) = evalPoly3W19 w k x (poly3At1DW19 r2 c)
  | [], [], _, _ => rfl
  | _ :: _, [], _, h => by cases h
  | [], _ :: _, _, h => by cases h
  | p :: _, q :: _, 0, h => poly3EqBoolW19_sound w k x p q (bool_and_split h).1
  | _ :: ps, _ :: qs, c' + 1, h => poly3RowEqBoolW19_sound w k x ps qs c' (bool_and_split h).2

private def poly3MatEqBoolW19 : List (List Poly3W19) -> List (List Poly3W19) -> Bool
  | [], [] => true
  | r1 :: rs1, r2 :: rs2 => poly3RowEqBoolW19 r1 r2 && poly3MatEqBoolW19 rs1 rs2
  | _, _ => false

private theorem poly3MatEqBoolW19_sound (w k x : Int) :
    ∀ (M1 M2 : List (List Poly3W19)) (r c : Nat),
      poly3MatEqBoolW19 M1 M2 = true ->
      evalPoly3W19 w k x (poly3At2DW19 M1 r c) = evalPoly3W19 w k x (poly3At2DW19 M2 r c)
  | [], [], _, _, _ => rfl
  | _ :: _, [], _, _, h => by cases h
  | [], _ :: _, _, _, h => by cases h
  | r1 :: _, r2 :: _, 0, c, h => poly3RowEqBoolW19_sound w k x r1 r2 c (bool_and_split h).1
  | _ :: rs1, _ :: rs2, r' + 1, c, h => poly3MatEqBoolW19_sound w k x rs1 rs2 r' c (bool_and_split h).2

private def trop3SwapsW19 : List (Nat × Nat) := [(0, 8), (1, 9), (2, 10), (3, 4), (4, 5), (5, 6), (6, 8), (7, 9), (8, 10), (9, 10)]

private def apTrop3PolyTblW19 : List (List Poly3W19) :=
[
  [[((0, 0, 0), 1)], [], [], [], [], [], [], [], [], [], [], []],
  [[((0, 0, 2), 1)], [((1, 0, 2), 1)], [((2, 0, 2), 1)], [], [], [], [], [], [], [], [], [((3, 0, 2), 1)]],
  [[((0, 0, 4), 1)], [((1, 0, 4), 2)], [((2, 0, 4), 4)], [], [], [], [], [], [], [], [], [((3, 0, 4), 8)]],
  [[((0, 0, 0), 1)], [((0, 1, 0), 1)], [((0, 2, 0), 1)], [((0, 0, 0), 1)], [((0, 1, 0), 1)], [((0, 2, 0), 1)], [], [], [], [], [((0, 3, 0), 1)], [((0, 3, 0), 1)]],
  [[((0, 0, 2), 1)], [((0, 1, 2), 1), ((1, 0, 2), 1)], [((0, 2, 2), 1), ((1, 1, 2), 2), ((2, 0, 2), 1)], [((0, 0, 1), 1)], [((0, 1, 1), 1), ((1, 0, 1), 1)], [((0, 2, 1), 1), ((1, 1, 1), 2), ((2, 0, 1), 1)], [], [], [], [], [((0, 3, 1), 1), ((1, 2, 1), 3), ((2, 1, 1), 3), ((3, 0, 1), 1)], [((0, 3, 2), 1), ((1, 2, 2), 3), ((2, 1, 2), 3), ((3, 0, 2), 1)]],
  [[((0, 0, 4), 1)], [((0, 1, 4), 1), ((1, 0, 4), 2)], [((0, 2, 4), 1), ((1, 1, 4), 4), ((2, 0, 4), 4)], [((0, 0, 2), 1)], [((0, 1, 2), 1), ((1, 0, 2), 2)], [((0, 2, 2), 1), ((1, 1, 2), 4), ((2, 0, 2), 4)], [], [], [], [], [((0, 3, 2), 1), ((1, 2, 2), 6), ((2, 1, 2), 12), ((3, 0, 2), 8)], [((0, 3, 4), 1), ((1, 2, 4), 6), ((2, 1, 4), 12), ((3, 0, 4), 8)]],
  [[], [], [], [((0, 0, 0), 1)], [((0, 1, 0), 2)], [((0, 2, 0), 4)], [((0, 0, 0), -1)], [((0, 1, 0), -2)], [((0, 2, 0), -4)], [((0, 3, 0), -8)], [((0, 3, 0), 8)], []],
  [[], [], [], [((0, 0, 1), 1)], [((0, 1, 1), 2), ((1, 0, 1), 1)], [((0, 2, 1), 4), ((1, 1, 1), 4), ((2, 0, 1), 1)], [((0, 0, 0), -1)], [((0, 1, 0), -2), ((1, 0, 0), -1)], [((0, 2, 0), -4), ((1, 1, 0), -4), ((2, 0, 0), -1)], [((0, 3, 0), -8), ((1, 2, 0), -12), ((2, 1, 0), -6), ((3, 0, 0), -1)], [((0, 3, 1), 8), ((1, 2, 1), 12), ((2, 1, 1), 6), ((3, 0, 1), 1)], []],
  [[], [], [], [((0, 0, 2), 1)], [((0, 1, 2), 2), ((1, 0, 2), 2)], [((0, 2, 2), 4), ((1, 1, 2), 8), ((2, 0, 2), 4)], [((0, 0, 0), -1)], [((0, 1, 0), -2), ((1, 0, 0), -2)], [((0, 2, 0), -4), ((1, 1, 0), -8), ((2, 0, 0), -4)], [((0, 3, 0), -8), ((1, 2, 0), -24), ((2, 1, 0), -24), ((3, 0, 0), -8)], [((0, 3, 2), 8), ((1, 2, 2), 24), ((2, 1, 2), 24), ((3, 0, 2), 8)], []],
  [[], [], [], [], [], [], [((0, 0, 0), -1)], [((0, 1, 0), -3)], [((0, 2, 0), -9)], [((0, 3, 0), -27)], [], []],
  [[], [], [], [], [], [], [((0, 0, 0), -1)], [((0, 1, 0), -3), ((1, 0, 0), -1)], [((0, 2, 0), -9), ((1, 1, 0), -6), ((2, 0, 0), -1)], [((0, 3, 0), -27), ((1, 2, 0), -27), ((2, 1, 0), -9), ((3, 0, 0), -1)], [], []],
  [[], [], [], [], [], [], [((0, 0, 0), -1)], [((0, 1, 0), -3), ((1, 0, 0), -2)], [((0, 2, 0), -9), ((1, 1, 0), -12), ((2, 0, 0), -4)], [((0, 3, 0), -27), ((1, 2, 0), -54), ((2, 1, 0), -36), ((3, 0, 0), -8)], [], []]
]

private def u9Trop3PolyTblW19 : List (List Poly3W19) :=
[
  [[((0, 0, 0), 1)], [], [], [], [], [], [], [], [], [], [], []],
  [[], [((0, 0, 0), 1)], [((1, 0, 0), -1)], [], [], [], [], [], [], [], [], [((6, 0, 0), 8)]],
  [[], [], [((0, 0, 0), 1)], [], [], [], [], [], [], [], [], [((5, 0, 0), -12)]],
  [[], [], [], [((0, 0, 0), 1)], [((0, 1, 0), -1)], [((0, 2, 0), 1), ((1, 1, 0), 1)], [], [], [], [], [((2, 3, 0), -2), ((3, 2, 0), -6), ((4, 1, 0), -4)], [((2, 5, 0), -2), ((2, 5, 1), 4), ((2, 5, 2), -2), ((3, 4, 1), 8), ((3, 4, 2), -8), ((4, 3, 0), 10), ((4, 3, 1), -4), ((4, 3, 2), -10), ((5, 2, 1), -8), ((5, 2, 2), -4), ((6, 1, 0), -8)]],
  [[], [], [], [], [((0, 0, 0), 1)], [((0, 1, 0), -2), ((1, 0, 0), -1)], [], [], [], [], [((2, 2, 0), 6), ((3, 1, 0), 12), ((4, 0, 0), 4)], [((2, 4, 0), 4), ((2, 4, 1), -8), ((2, 4, 2), 4), ((3, 3, 0), -6), ((3, 3, 1), -8), ((3, 3, 2), 14), ((4, 2, 0), -10), ((4, 2, 1), 8), ((4, 2, 2), 14), ((5, 1, 0), 12), ((5, 1, 1), 8), ((5, 1, 2), 4)]],
  [[], [], [], [], [], [((0, 0, 0), 1)], [], [], [], [], [((2, 1, 0), -6), ((3, 0, 0), -6)], [((2, 3, 0), -2), ((2, 3, 1), 4), ((2, 3, 2), -2), ((3, 2, 0), 6), ((3, 2, 2), -6), ((4, 1, 0), -4), ((4, 1, 1), -4), ((4, 1, 2), -4)]],
  [[], [], [], [], [], [], [((0, 0, 0), 1)], [((0, 1, 0), -2)], [((0, 2, 0), 4), ((1, 1, 0), 2)], [((0, 3, 0), -8), ((1, 2, 0), -12), ((2, 1, 0), -4)], [((0, 5, 0), 4), ((0, 5, 1), -8), ((0, 5, 2), 4), ((1, 4, 0), -6), ((1, 4, 1), -8), ((1, 4, 2), 14), ((2, 3, 0), -8), ((2, 3, 1), 8), ((2, 3, 2), 14), ((3, 2, 0), 6), ((3, 2, 1), 8), ((3, 2, 2), 4), ((4, 1, 0), 4)], [((0, 7, 0), -4), ((0, 7, 1), 16), ((0, 7, 2), -24), ((0, 7, 3), 16), ((0, 7, 4), -4), ((1, 6, 0), 18), ((1, 6, 1), -28), ((1, 6, 2), -24), ((1, 6, 3), 60), ((1, 6, 4), -26), ((2, 5, 0), -18), ((2, 5, 1), -20), ((2, 5, 2), 30), ((2, 5, 3), 72), ((2, 5, 4), -64), ((3, 4, 0), -18), ((3, 4, 1), 20), ((3, 4, 2), 36), ((3, 4, 3), 36), ((3, 4, 4), -74), ((4, 3, 0), 30), ((4, 3, 1), 4), ((4, 3, 2), -6), ((4, 3, 3), 8), ((4, 3, 4), -40), ((5, 2, 1), 8), ((5, 2, 2), -12), ((5, 2, 4), -8), ((6, 1, 0), -8)]],
  [[], [], [], [], [], [], [], [((0, 0, 0), 1)], [((0, 1, 0), -4), ((1, 0, 0), -1)], [((0, 2, 0), 12), ((1, 1, 0), 12), ((2, 0, 0), 2)], [((0, 4, 0), -4), ((0, 4, 1), 8), ((0, 4, 2), -4), ((1, 3, 0), 9), ((1, 3, 1), 4), ((1, 3, 2), -13), ((2, 2, 0), 1), ((2, 2, 1), -8), ((2, 2, 2), -11), ((3, 1, 0), -6), ((3, 1, 1), -4), ((3, 1, 2), -2)], [((0, 6, 0), 4), ((0, 6, 1), -16), ((0, 6, 2), 24), ((0, 6, 3), -16), ((0, 6, 4), 4), ((1, 5, 0), -21), ((1, 5, 1), 38), ((1, 5, 2), 12), ((1, 5, 3), -54), ((1, 5, 4), 25), ((2, 4, 0), 34), ((2, 4, 1), -4), ((2, 4, 2), -36), ((2, 4, 3), -52), ((2, 4, 4), 58), ((3, 3, 0), -9), ((3, 3, 1), -14), ((3, 3, 2), -20), ((3, 3, 3), -18), ((3, 3, 4), 61), ((4, 2, 0), -20), ((4, 2, 1), -4), ((4, 2, 2), 12), ((4, 2, 3), -4), ((4, 2, 4), 28), ((5, 1, 0), 12), ((5, 1, 2), 8), ((5, 1, 4), 4)]],
  [[], [], [], [], [], [], [], [], [((0, 0, 0), 1)], [((0, 1, 0), -6), ((1, 0, 0), -3)], [((0, 3, 0), 1), ((0, 3, 1), -2), ((0, 3, 2), 1), ((1, 2, 0), -3), ((1, 2, 2), 3), ((2, 1, 0), 2), ((2, 1, 1), 2), ((2, 1, 2), 2)], [((0, 5, 0), -1), ((0, 5, 1), 4), ((0, 5, 2), -6), ((0, 5, 3), 4), ((0, 5, 4), -1), ((1, 4, 0), 6), ((1, 4, 1), -12), ((1, 4, 3), 12), ((1, 4, 4), -6), ((2, 3, 0), -13), ((2, 3, 1), 8), ((2, 3, 2), 10), ((2, 3, 3), 8), ((2, 3, 4), -13), ((3, 2, 0), 12), ((3, 2, 4), -12), ((4, 1, 0), -4), ((4, 1, 2), -4), ((4, 1, 4), -4)]],
  [[], [], [], [], [], [], [], [], [], [((0, 0, 0), 1)], [], []],
  [[], [], [], [], [], [], [], [], [], [], [((2, 0, 0), 2)], []],
  [[], [], [], [], [], [], [], [], [], [], [], [((4, 0, 0), 4)]]
]

private def prodTrop3PolyTblW19 : List (List Poly3W19) :=
[
  [[((0, 0, 0), 1)], [], [], [], [], [], [], [], [], [], [], []],
  [[((0, 0, 2), 1)], [((1, 0, 2), 1)], [], [], [], [], [], [], [], [], [], []],
  [[((0, 0, 4), 1)], [((1, 0, 4), 2)], [((2, 0, 4), 2)], [], [], [], [], [], [], [], [], []],
  [[((0, 0, 0), 1)], [((0, 1, 0), 1)], [((0, 2, 0), 1), ((1, 1, 0), -1)], [((0, 0, 0), 1)], [], [], [], [], [], [], [], []],
  [[((0, 0, 2), 1)], [((0, 1, 2), 1), ((1, 0, 2), 1)], [((0, 2, 2), 1), ((1, 1, 2), 1)], [((0, 0, 1), 1)], [((1, 0, 1), 1)], [], [], [], [], [], [], []],
  [[((0, 0, 4), 1)], [((0, 1, 4), 1), ((1, 0, 4), 2)], [((0, 2, 4), 1), ((1, 1, 4), 3), ((2, 0, 4), 2)], [((0, 0, 2), 1)], [((1, 0, 2), 2)], [((2, 0, 2), 2)], [], [], [], [], [], []],
  [[], [], [], [((0, 0, 0), 1)], [((0, 1, 0), 1)], [((0, 2, 0), 1), ((1, 1, 0), -1)], [((0, 0, 0), -1)], [], [], [], [], []],
  [[], [], [], [((0, 0, 1), 1)], [((0, 1, 1), 1), ((1, 0, 1), 1)], [((0, 2, 1), 1), ((1, 1, 1), 1)], [((0, 0, 0), -1)], [((1, 0, 0), -1)], [], [], [], []],
  [[], [], [], [((0, 0, 2), 1)], [((0, 1, 2), 1), ((1, 0, 2), 2)], [((0, 2, 2), 1), ((1, 1, 2), 3), ((2, 0, 2), 2)], [((0, 0, 0), -1)], [((1, 0, 0), -2)], [((2, 0, 0), -2)], [], [], []],
  [[], [], [], [], [], [], [((0, 0, 0), -1)], [((0, 1, 0), -1)], [((0, 2, 0), -1), ((1, 1, 0), 1)], [((0, 3, 0), -1), ((1, 2, 0), 3), ((2, 1, 0), -2)], [((0, 5, 0), -1), ((0, 5, 1), 2), ((0, 5, 2), -1), ((1, 4, 0), 6), ((1, 4, 1), -4), ((1, 4, 2), -2), ((2, 3, 0), -13), ((2, 3, 1), -2), ((2, 3, 2), 1), ((3, 2, 0), 12), ((3, 2, 1), 4), ((3, 2, 2), 2), ((4, 1, 0), -4)], [((0, 7, 0), 1), ((0, 7, 1), -4), ((0, 7, 2), 6), ((0, 7, 3), -4), ((0, 7, 4), 1), ((1, 6, 0), -9), ((1, 6, 1), 22), ((1, 6, 2), -12), ((1, 6, 3), -6), ((1, 6, 4), 5), ((2, 5, 0), 33), ((2, 5, 1), -40), ((2, 5, 2), -12), ((2, 5, 3), 12), ((2, 5, 4), 7), ((3, 4, 0), -63), ((3, 4, 1), 22), ((3, 4, 2), 24), ((3, 4, 3), 18), ((3, 4, 4), -1), ((4, 3, 0), 66), ((4, 3, 1), 8), ((4, 3, 2), 6), ((4, 3, 3), 4), ((4, 3, 4), -8), ((5, 2, 0), -36), ((5, 2, 1), -8), ((5, 2, 2), -12), ((5, 2, 4), -4), ((6, 1, 0), 8)]],
  [[], [], [], [], [], [], [((0, 0, 0), -1)], [((0, 1, 0), -1), ((1, 0, 0), -1)], [((0, 2, 0), -1), ((1, 1, 0), -1)], [((0, 3, 0), -1), ((2, 1, 0), 1)], [((0, 5, 0), -1), ((0, 5, 1), 2), ((0, 5, 2), -1), ((1, 4, 0), 4), ((1, 4, 2), -4), ((2, 3, 0), -5), ((2, 3, 1), -4), ((2, 3, 2), -5), ((3, 2, 0), 2), ((3, 2, 2), -2), ((4, 1, 1), 2)], [((0, 7, 0), 1), ((0, 7, 1), -4), ((0, 7, 2), 6), ((0, 7, 3), -4), ((0, 7, 4), 1), ((1, 6, 0), -7), ((1, 6, 1), 14), ((1, 6, 3), -14), ((1, 6, 4), 7), ((2, 5, 0), 19), ((2, 5, 1), -10), ((2, 5, 2), -18), ((2, 5, 3), -10), ((2, 5, 4), 19), ((3, 4, 0), -25), ((3, 4, 1), -10), ((3, 4, 3), 10), ((3, 4, 4), 25), ((4, 3, 0), 16), ((4, 3, 1), 14), ((4, 3, 2), 16), ((4, 3, 3), 14), ((4, 3, 4), 16), ((5, 2, 0), -4), ((5, 2, 1), -4), ((5, 2, 3), 4), ((5, 2, 4), 4), ((6, 1, 2), -4)]],
  [[], [], [], [], [], [], [((0, 0, 0), -1)], [((0, 1, 0), -1), ((1, 0, 0), -2)], [((0, 2, 0), -1), ((1, 1, 0), -3), ((2, 0, 0), -2)], [((0, 3, 0), -1), ((1, 2, 0), -3), ((2, 1, 0), -2)], [((0, 5, 0), -1), ((0, 5, 1), 2), ((0, 5, 2), -1), ((1, 4, 0), 2), ((1, 4, 1), 4), ((1, 4, 2), -6), ((2, 3, 0), 1), ((2, 3, 1), -2), ((2, 3, 2), -13), ((3, 2, 0), -2), ((3, 2, 1), -4), ((3, 2, 2), -12), ((4, 1, 2), -4)], [((0, 7, 0), 1), ((0, 7, 1), -4), ((0, 7, 2), 6), ((0, 7, 3), -4), ((0, 7, 4), 1), ((1, 6, 0), -5), ((1, 6, 1), 6), ((1, 6, 2), 12), ((1, 6, 3), -22), ((1, 6, 4), 9), ((2, 5, 0), 7), ((2, 5, 1), 12), ((2, 5, 2), -12), ((2, 5, 3), -40), ((2, 5, 4), 33), ((3, 4, 0), 1), ((3, 4, 1), -18), ((3, 4, 2), -24), ((3, 4, 3), -22), ((3, 4, 4), 63), ((4, 3, 0), -8), ((4, 3, 1), 4), ((4, 3, 2), 6), ((4, 3, 3), 8), ((4, 3, 4), 66), ((5, 2, 0), 4), ((5, 2, 2), 12), ((5, 2, 3), 8), ((5, 2, 4), 36), ((6, 1, 4), 8)]]
]

private def rhsTrop3TargetPolyW19 : Poly3W19 :=
  let wP : Poly3W19 := [((1, 0, 0), 1)]
  let kP : Poly3W19 := [((0, 1, 0), 1)]
  let xm1 : Poly3W19 := [((0, 0, 1), 1), ((0, 0, 0), -1)]
  let xp1 : Poly3W19 := [((0, 0, 1), 1), ((0, 0, 0), 1)]
  let linF := poly3AddW19 (poly3MulW19 xm1 kP) (poly3MulW19 xp1 wP)
  let qP := poly3AddW19
    (poly3AddW19 (poly3MulW19 xm1 (poly3MulW19 kP kP))
                 (poly3MulW19 [((0, 0, 0), 3)] (poly3MulW19 xp1 (poly3MulW19 wP kP))))
    (poly3MulW19 [((0, 0, 0), 2)] (poly3MulW19 xm1 (poly3MulW19 wP wP)))
  poly3MulW19 [((8, 3, 10), 4)] (poly3MulW19 linF (poly3PowW19 qP 3))

set_option maxRecDepth 65536 in
private theorem trop3_ap_ok_w19 :
    poly3MatEqBoolW19
      (applySignedSwapsPoly3W19 trop3SwapsW19 (buildMat12Poly3W19 trop3EntryPoly3W19))
      apTrop3PolyTblW19 = true := by decide

private def checkTrop3ProdRowBoolW19 (r : Nat) : Bool :=
  poly3RowEqBoolW19
    (poly3RowAtW19 prodTrop3PolyTblW19 r)
    (buildRow12Poly3W19 (fun c => dotPrefixPoly3W19 apTrop3PolyTblW19 u9Trop3PolyTblW19 r c 12))

set_option maxRecDepth 65536 in
private theorem trop3_prod_s0_w19 :
    checkTrop3ProdRowBoolW19 0 = true ∧ checkTrop3ProdRowBoolW19 1 = true ∧
    checkTrop3ProdRowBoolW19 2 = true := by decide

set_option maxRecDepth 65536 in
private theorem trop3_prod_s1_w19 :
    checkTrop3ProdRowBoolW19 3 = true ∧ checkTrop3ProdRowBoolW19 4 = true ∧
    checkTrop3ProdRowBoolW19 5 = true := by decide

set_option maxRecDepth 65536 in
private theorem trop3_prod_s2_w19 :
    checkTrop3ProdRowBoolW19 6 = true ∧ checkTrop3ProdRowBoolW19 7 = true ∧
    checkTrop3ProdRowBoolW19 8 = true := by decide

set_option maxRecDepth 65536 in
private theorem trop3_prod_s3_w19 :
    checkTrop3ProdRowBoolW19 9 = true ∧ checkTrop3ProdRowBoolW19 10 = true ∧
    checkTrop3ProdRowBoolW19 11 = true := by decide

private def diag9LitPolyW19 : Poly3W19 := [((9, 0, 9), -8)]
private def det3M0LitPolyW19 : Poly3W19 := [((3, 9, 1), 2), ((3, 9, 2), -8), ((3, 9, 3), 12), ((3, 9, 4), -8), ((3, 9, 5), 2), ((4, 8, 1), -16), ((4, 8, 2), 28), ((4, 8, 3), 12), ((4, 8, 4), -44), ((4, 8, 5), 20), ((5, 7, 1), 52), ((5, 7, 2), -8), ((5, 7, 3), -56), ((5, 7, 4), -72), ((5, 7, 5), 84), ((6, 6, 1), -88), ((6, 6, 2), -56), ((6, 6, 3), -48), ((6, 6, 5), 192), ((7, 5, 1), 82), ((7, 5, 2), 40), ((7, 5, 3), 52), ((7, 5, 4), 96), ((7, 5, 5), 258), ((8, 4, 1), -40), ((8, 4, 2), 28), ((8, 4, 3), 36), ((8, 4, 4), 60), ((8, 4, 5), 204), ((9, 3, 1), 8), ((9, 3, 2), -24), ((9, 3, 3), -8), ((9, 3, 4), -16), ((9, 3, 5), 88), ((10, 2, 4), -16), ((10, 2, 5), 16)]
private def det3M1LitPolyW19 : Poly3W19 := [((1, 9, 0), 1), ((1, 9, 1), -4), ((1, 9, 2), 6), ((1, 9, 3), -4), ((1, 9, 4), 1), ((2, 8, 0), -6), ((2, 8, 1), 8), ((2, 8, 2), 12), ((2, 8, 3), -24), ((2, 8, 4), 10), ((3, 7, 0), 12), ((3, 7, 1), 12), ((3, 7, 2), -18), ((3, 7, 3), -48), ((3, 7, 4), 42), ((4, 6, 0), -6), ((4, 6, 1), -28), ((4, 6, 2), -38), ((4, 6, 3), -24), ((4, 6, 4), 96), ((5, 5, 0), -9), ((5, 5, 2), 12), ((5, 5, 3), 36), ((5, 5, 4), 129), ((6, 4, 0), 12), ((6, 4, 1), 20), ((6, 4, 2), 34), ((6, 4, 3), 48), ((6, 4, 4), 102), ((7, 3, 0), -4), ((7, 3, 1), -8), ((7, 3, 3), 16), ((7, 3, 4), 44), ((8, 2, 2), -8), ((8, 2, 4), 8)]
private def det3M2LitPolyW19 : Poly3W19 := [((1, 7, 0), -1), ((1, 7, 1), 2), ((1, 7, 2), -1), ((2, 6, 0), 3), ((2, 6, 1), 4), ((2, 6, 2), -7), ((3, 5, 0), -1), ((3, 5, 1), -4), ((3, 5, 2), -19), ((4, 4, 0), -3), ((4, 4, 1), -8), ((4, 4, 2), -25), ((5, 3, 0), 2), ((5, 3, 1), 2), ((5, 3, 2), -16), ((6, 2, 1), 4), ((6, 2, 2), -4)]
private def b9_9LitW19 : Poly3W19 := [((0, 3, 0), -1), ((1, 2, 0), 3), ((2, 1, 0), -2)]
private def b9_10aLitW19 : Poly3W19 := [((0, 5, 0), -1), ((0, 5, 1), 2), ((0, 5, 2), -1), ((1, 4, 0), 6), ((1, 4, 1), -4), ((1, 4, 2), -2), ((2, 3, 0), -13)]
private def b9_10bLitW19 : Poly3W19 := [((2, 3, 1), -2), ((2, 3, 2), 1), ((3, 2, 0), 12), ((3, 2, 1), 4), ((3, 2, 2), 2), ((4, 1, 0), -4)]
private def b9_11aLitW19 : Poly3W19 := [((0, 7, 0), 1), ((0, 7, 1), -4), ((0, 7, 2), 6), ((0, 7, 3), -4), ((0, 7, 4), 1), ((1, 6, 0), -9), ((1, 6, 1), 22), ((1, 6, 2), -12), ((1, 6, 3), -6), ((1, 6, 4), 5), ((2, 5, 0), 33), ((2, 5, 1), -40), ((2, 5, 2), -12), ((2, 5, 3), 12), ((2, 5, 4), 7)]
private def b9_11bLitW19 : Poly3W19 := [((3, 4, 0), -63), ((3, 4, 1), 22), ((3, 4, 2), 24), ((3, 4, 3), 18), ((3, 4, 4), -1), ((4, 3, 0), 66), ((4, 3, 1), 8), ((4, 3, 2), 6), ((4, 3, 3), 4), ((4, 3, 4), -8), ((5, 2, 0), -36), ((5, 2, 1), -8), ((5, 2, 2), -12), ((5, 2, 4), -4), ((6, 1, 0), 8)]
private def det3T0LitPolyW19 : Poly3W19 := [((3, 12, 1), -2), ((3, 12, 2), 8), ((3, 12, 3), -12), ((3, 12, 4), 8), ((3, 12, 5), -2), ((4, 11, 1), 22), ((4, 11, 2), -52), ((4, 11, 3), 24), ((4, 11, 4), 20), ((4, 11, 5), -14), ((5, 10, 1), -104), ((5, 10, 2), 108), ((5, 10, 3), 68), ((5, 10, 4), -44), ((5, 10, 5), -28), ((6, 9, 1), 276), ((6, 9, 2), -24), ((6, 9, 3), -144), ((6, 9, 4), -128), ((6, 9, 5), 20), ((7, 8, 1), -450), ((7, 8, 2), -192), ((7, 8, 3), -84), ((7, 8, 4), 48), ((7, 8, 5), 150), ((8, 7, 1), 462), ((8, 7, 2), 204), ((8, 7, 3), 216), ((8, 7, 4), 228), ((8, 7, 5), 186), ((9, 6, 1), -292), ((9, 6, 2), 28), ((9, 6, 3), 12), ((9, 6, 4), 4), ((9, 6, 5), 8), ((10, 5, 1), 104), ((10, 5, 2), -128), ((10, 5, 3), -96), ((10, 5, 4), -152), ((10, 5, 5), -160), ((11, 4, 1), -16), ((11, 4, 2), 48), ((11, 4, 3), 16), ((11, 4, 4), -16), ((11, 4, 5), -128), ((12, 3, 4), 32), ((12, 3, 5), -32)]
private def t1aLitW19 : Poly3W19 := [((1, 14, 0), -1), ((1, 14, 1), 6), ((1, 14, 2), -15), ((1, 14, 3), 20), ((1, 14, 4), -15), ((1, 14, 5), 6), ((1, 14, 6), -1), ((2, 13, 0), 12), ((2, 13, 1), -48), ((2, 13, 2), 60), ((2, 13, 4), -60), ((2, 13, 5), 48), ((2, 13, 6), -12), ((3, 12, 0), -61), ((3, 12, 1), 136), ((3, 12, 2), 4), ((3, 12, 3), -156), ((3, 12, 4), -1), ((3, 12, 5), 140), ((3, 12, 6), -62), ((4, 11, 0), 156), ((4, 11, 1), -64), ((4, 11, 2), -348), ((4, 11, 3), 48), ((4, 11, 4), 244), ((4, 11, 5), 144), ((4, 11, 6), -180), ((5, 10, 0), -183), ((5, 10, 1), -318), ((5, 10, 2), 127), ((5, 10, 3), 676), ((5, 10, 4), 133), ((5, 10, 5), -114), ((5, 10, 6), -321), ((6, 9, 0), 12), ((6, 9, 1), 404), ((6, 9, 2), 578), ((6, 9, 3), 480), ((6, 9, 4), -682), ((6, 9, 5), -432), ((6, 9, 6), -360), ((7, 8, 0), 193), ((7, 8, 1), 72), ((7, 8, 2), -68), ((7, 8, 3), -364), ((7, 8, 4), -1337), ((7, 8, 5), -432), ((7, 8, 6), -248), ((8, 7, 0), -180), ((8, 7, 1), -292), ((8, 7, 2), -394), ((8, 7, 3), -528), ((8, 7, 4), -1126), ((8, 7, 5), -192), ((8, 7, 6), -96), ((9, 6, 0), 52), ((9, 6, 1), 104), ((9, 6, 2), -48), ((9, 6, 3), -176), ((9, 6, 4), -508), ((9, 6, 5), -32), ((9, 6, 6), -16), ((10, 5, 2), 104), ((10, 5, 4), -104)]
private def t1bLitW19 : Poly3W19 := [((3, 12, 1), -2), ((3, 12, 2), 9), ((3, 12, 3), -16), ((3, 12, 4), 14), ((3, 12, 5), -6), ((3, 12, 6), 1), ((4, 11, 0), 12), ((4, 11, 1), -32), ((4, 11, 2), 36), ((4, 11, 3), -48), ((4, 11, 4), 68), ((4, 11, 5), -48), ((4, 11, 6), 12), ((5, 10, 0), -76), ((5, 10, 1), 64), ((5, 10, 2), 128), ((5, 10, 3), -160), ((5, 10, 4), 122), ((5, 10, 5), -140), ((5, 10, 6), 62), ((6, 9, 0), 168), ((6, 9, 1), 172), ((6, 9, 2), -142), ((6, 9, 3), -480), ((6, 9, 4), 246), ((6, 9, 5), -144), ((6, 9, 6), 180), ((7, 8, 0), -120), ((7, 8, 1), -390), ((7, 8, 2), -517), ((7, 8, 3), -328), ((7, 8, 4), 752), ((7, 8, 5), 114), ((7, 8, 6), 321), ((8, 7, 0), -84), ((8, 7, 1), 52), ((8, 7, 2), 250), ((8, 7, 3), 528), ((8, 7, 4), 1270), ((8, 7, 5), 432), ((8, 7, 6), 360), ((9, 6, 0), 180), ((9, 6, 1), 296), ((9, 6, 2), 476), ((9, 6, 3), 600), ((9, 6, 4), 936), ((9, 6, 5), 432), ((9, 6, 6), 248), ((10, 5, 0), -96), ((10, 5, 1), -192), ((10, 5, 2), -176), ((10, 5, 4), 176), ((10, 5, 5), 192), ((10, 5, 6), 96), ((11, 4, 0), 16), ((11, 4, 1), 32), ((11, 4, 2), -96), ((11, 4, 3), -96), ((11, 4, 4), -96), ((11, 4, 5), 32), ((11, 4, 6), 16), ((12, 3, 2), 32), ((12, 3, 4), -32)]
private def det3T1LitPolyW19 : Poly3W19 := [((1, 14, 0), -1), ((1, 14, 1), 6), ((1, 14, 2), -15), ((1, 14, 3), 20), ((1, 14, 4), -15), ((1, 14, 5), 6), ((1, 14, 6), -1), ((2, 13, 0), 12), ((2, 13, 1), -48), ((2, 13, 2), 60), ((2, 13, 4), -60), ((2, 13, 5), 48), ((2, 13, 6), -12), ((3, 12, 0), -61), ((3, 12, 1), 134), ((3, 12, 2), 13), ((3, 12, 3), -172), ((3, 12, 4), 13), ((3, 12, 5), 134), ((3, 12, 6), -61), ((4, 11, 0), 168), ((4, 11, 1), -96), ((4, 11, 2), -312), ((4, 11, 4), 312), ((4, 11, 5), 96), ((4, 11, 6), -168), ((5, 10, 0), -259), ((5, 10, 1), -254), ((5, 10, 2), 255), ((5, 10, 3), 516), ((5, 10, 4), 255), ((5, 10, 5), -254), ((5, 10, 6), -259), ((6, 9, 0), 180), ((6, 9, 1), 576), ((6, 9, 2), 436), ((6, 9, 4), -436), ((6, 9, 5), -576), ((6, 9, 6), -180), ((7, 8, 0), 73), ((7, 8, 1), -318), ((7, 8, 2), -585), ((7, 8, 3), -692), ((7, 8, 4), -585), ((7, 8, 5), -318), ((7, 8, 6), 73), ((8, 7, 0), -264), ((8, 7, 1), -240), ((8, 7, 2), -144), ((8, 7, 4), 144), ((8, 7, 5), 240), ((8, 7, 6), 264), ((9, 6, 0), 232), ((9, 6, 1), 400), ((9, 6, 2), 428), ((9, 6, 3), 424), ((9, 6, 4), 428), ((9, 6, 5), 400), ((9, 6, 6), 232), ((10, 5, 0), -96), ((10, 5, 1), -192), ((10, 5, 2), -72), ((10, 5, 4), 72), ((10, 5, 5), 192), ((10, 5, 6), 96), ((11, 4, 0), 16), ((11, 4, 1), 32), ((11, 4, 2), -96), ((11, 4, 3), -96), ((11, 4, 4), -96), ((11, 4, 5), 32), ((11, 4, 6), 16), ((12, 3, 2), 32), ((12, 3, 4), -32)]
private def t2aLitW19 : Poly3W19 := [((1, 14, 0), -1), ((1, 14, 1), 6), ((1, 14, 2), -15), ((1, 14, 3), 20), ((1, 14, 4), -15), ((1, 14, 5), 6), ((1, 14, 6), -1), ((2, 13, 0), 12), ((2, 13, 1), -48), ((2, 13, 2), 60), ((2, 13, 4), -60), ((2, 13, 5), 48), ((2, 13, 6), -12), ((3, 12, 0), -61), ((3, 12, 1), 136), ((3, 12, 2), 5), ((3, 12, 3), -160), ((3, 12, 4), 5), ((3, 12, 5), 136), ((3, 12, 6), -61), ((4, 11, 0), 105), ((4, 11, 1), 30), ((4, 11, 2), -343), ((4, 11, 3), -32), ((4, 11, 4), 279), ((4, 11, 5), 130), ((4, 11, 6), -169), ((5, 10, 0), -4), ((5, 10, 1), -92), ((5, 10, 2), -382), ((5, 10, 3), 428), ((5, 10, 4), 404), ((5, 10, 5), -80), ((5, 10, 6), -274), ((6, 9, 0), -117), ((6, 9, 1), -114), ((6, 9, 2), -325), ((6, 9, 3), 712), ((6, 9, 4), 333), ((6, 9, 5), -230), ((6, 9, 6), -259), ((7, 8, 0), 66), ((7, 8, 1), -50), ((7, 8, 2), -508), ((7, 8, 3), 504), ((7, 8, 4), 254), ((7, 8, 5), -134), ((7, 8, 6), -132), ((8, 7, 1), 132), ((8, 7, 2), -292), ((8, 7, 3), 112), ((8, 7, 4), 96), ((8, 7, 5), -20), ((8, 7, 6), -28)]
private def t2bLitW19 : Poly3W19 := [((4, 11, 0), 63), ((4, 11, 1), -148), ((4, 11, 2), 83), ((4, 11, 3), 8), ((4, 11, 4), 13), ((4, 11, 5), -20), ((4, 11, 6), 1), ((5, 10, 0), -255), ((5, 10, 1), -62), ((5, 10, 2), 545), ((5, 10, 3), -4), ((5, 10, 4), -89), ((5, 10, 5), -150), ((5, 10, 6), 15), ((6, 9, 0), 297), ((6, 9, 1), 454), ((6, 9, 2), 705), ((6, 9, 3), -568), ((6, 9, 4), -561), ((6, 9, 5), -406), ((6, 9, 6), 79), ((7, 8, 0), 7), ((7, 8, 1), 14), ((7, 8, 2), 211), ((7, 8, 3), -968), ((7, 8, 4), -791), ((7, 8, 5), -502), ((7, 8, 6), 205), ((8, 7, 0), -264), ((8, 7, 1), -450), ((8, 7, 2), 40), ((8, 7, 3), -328), ((8, 7, 4), -276), ((8, 7, 5), -310), ((8, 7, 6), 292), ((9, 6, 0), 232), ((9, 6, 1), 176), ((9, 6, 2), 160), ((9, 6, 3), 196), ((9, 6, 4), 184), ((9, 6, 5), -124), ((9, 6, 6), 232), ((10, 5, 0), -96), ((10, 5, 1), 112), ((10, 5, 2), 104), ((10, 5, 3), 96), ((10, 5, 4), 176), ((10, 5, 5), -56), ((10, 5, 6), 96), ((11, 4, 0), 16), ((11, 4, 1), -128), ((11, 4, 2), -16), ((11, 4, 3), -16), ((11, 4, 4), 48), ((11, 4, 5), -16), ((11, 4, 6), 16), ((12, 3, 1), 32), ((12, 3, 2), -32)]
private def det3T2LitPolyW19 : Poly3W19 := [((1, 14, 0), -1), ((1, 14, 1), 6), ((1, 14, 2), -15), ((1, 14, 3), 20), ((1, 14, 4), -15), ((1, 14, 5), 6), ((1, 14, 6), -1), ((2, 13, 0), 12), ((2, 13, 1), -48), ((2, 13, 2), 60), ((2, 13, 4), -60), ((2, 13, 5), 48), ((2, 13, 6), -12), ((3, 12, 0), -61), ((3, 12, 1), 136), ((3, 12, 2), 5), ((3, 12, 3), -160), ((3, 12, 4), 5), ((3, 12, 5), 136), ((3, 12, 6), -61), ((4, 11, 0), 168), ((4, 11, 1), -118), ((4, 11, 2), -260), ((4, 11, 3), -24), ((4, 11, 4), 292), ((4, 11, 5), 110), ((4, 11, 6), -168), ((5, 10, 0), -259), ((5, 10, 1), -154), ((5, 10, 2), 163), ((5, 10, 3), 424), ((5, 10, 4), 315), ((5, 10, 5), -230), ((5, 10, 6), -259), ((6, 9, 0), 180), ((6, 9, 1), 340), ((6, 9, 2), 380), ((6, 9, 3), 144), ((6, 9, 4), -228), ((6, 9, 5), -636), ((6, 9, 6), -180), ((7, 8, 0), 73), ((7, 8, 1), -36), ((7, 8, 2), -297), ((7, 8, 3), -464), ((7, 8, 4), -537), ((7, 8, 5), -636), ((7, 8, 6), 73), ((8, 7, 0), -264), ((8, 7, 1), -318), ((8, 7, 2), -252), ((8, 7, 3), -216), ((8, 7, 4), -180), ((8, 7, 5), -330), ((8, 7, 6), 264), ((9, 6, 0), 232), ((9, 6, 1), 176), ((9, 6, 2), 160), ((9, 6, 3), 196), ((9, 6, 4), 184), ((9, 6, 5), -124), ((9, 6, 6), 232), ((10, 5, 0), -96), ((10, 5, 1), 112), ((10, 5, 2), 104), ((10, 5, 3), 96), ((10, 5, 4), 176), ((10, 5, 5), -56), ((10, 5, 6), 96), ((11, 4, 0), 16), ((11, 4, 1), -128), ((11, 4, 2), -16), ((11, 4, 3), -16), ((11, 4, 4), 48), ((11, 4, 5), -16), ((11, 4, 6), 16), ((12, 3, 1), 32), ((12, 3, 2), -32)]
private def det3LitPolyW19 : Poly3W19 := [((5, 10, 1), -4), ((5, 10, 2), 16), ((5, 10, 3), -24), ((5, 10, 4), 16), ((5, 10, 5), -4), ((6, 9, 1), 40), ((6, 9, 2), -80), ((6, 9, 4), 80), ((6, 9, 5), -40), ((7, 8, 1), -168), ((7, 8, 2), 96), ((7, 8, 3), 144), ((7, 8, 4), 96), ((7, 8, 5), -168), ((8, 7, 1), 384), ((8, 7, 2), 96), ((8, 7, 4), -96), ((8, 7, 5), -384), ((9, 6, 1), -516), ((9, 6, 2), -240), ((9, 6, 3), -216), ((9, 6, 4), -240), ((9, 6, 5), -516), ((10, 5, 1), 408), ((10, 5, 2), 48), ((10, 5, 4), -48), ((10, 5, 5), -408), ((11, 4, 1), -176), ((11, 4, 2), 128), ((11, 4, 3), 96), ((11, 4, 4), 128), ((11, 4, 5), -176), ((12, 3, 1), 32), ((12, 3, 2), -64), ((12, 3, 4), 64), ((12, 3, 5), -32)]
private def qLitPolyW19 : Poly3W19 := [((0, 2, 0), -1), ((0, 2, 1), 1), ((1, 1, 0), 3), ((1, 1, 1), 3), ((2, 0, 0), -2), ((2, 0, 1), 2)]
private def q2LitPolyW19 : Poly3W19 := [((0, 4, 0), 1), ((0, 4, 1), -2), ((0, 4, 2), 1), ((1, 3, 0), -6), ((1, 3, 2), 6), ((2, 2, 0), 13), ((2, 2, 1), 10), ((2, 2, 2), 13), ((3, 1, 0), -12), ((3, 1, 2), 12), ((4, 0, 0), 4), ((4, 0, 1), -8), ((4, 0, 2), 4)]
private def q3LitPolyW19 : Poly3W19 := [((0, 6, 0), -1), ((0, 6, 1), 3), ((0, 6, 2), -3), ((0, 6, 3), 1), ((1, 5, 0), 9), ((1, 5, 1), -9), ((1, 5, 2), -9), ((1, 5, 3), 9), ((2, 4, 0), -33), ((2, 4, 1), -9), ((2, 4, 2), 9), ((2, 4, 3), 33), ((3, 3, 0), 63), ((3, 3, 1), 45), ((3, 3, 2), 45), ((3, 3, 3), 63), ((4, 2, 0), -66), ((4, 2, 1), -18), ((4, 2, 2), 18), ((4, 2, 3), 66), ((5, 1, 0), 36), ((5, 1, 1), -36), ((5, 1, 2), -36), ((5, 1, 3), 36), ((6, 0, 0), -8), ((6, 0, 1), 24), ((6, 0, 2), -24), ((6, 0, 3), 8)]
private def linFLitPolyW19 : Poly3W19 := [((0, 1, 0), -1), ((0, 1, 1), 1), ((1, 0, 0), 1), ((1, 0, 1), 1)]
private def linQ3LitPolyW19 : Poly3W19 := [((0, 7, 0), 1), ((0, 7, 1), -4), ((0, 7, 2), 6), ((0, 7, 3), -4), ((0, 7, 4), 1), ((1, 6, 0), -10), ((1, 6, 1), 20), ((1, 6, 3), -20), ((1, 6, 4), 10), ((2, 5, 0), 42), ((2, 5, 1), -24), ((2, 5, 2), -36), ((2, 5, 3), -24), ((2, 5, 4), 42), ((3, 4, 0), -96), ((3, 4, 1), -24), ((3, 4, 3), 24), ((3, 4, 4), 96), ((4, 3, 0), 129), ((4, 3, 1), 60), ((4, 3, 2), 54), ((4, 3, 3), 60), ((4, 3, 4), 129), ((5, 2, 0), -102), ((5, 2, 1), -12), ((5, 2, 3), 12), ((5, 2, 4), 102), ((6, 1, 0), 44), ((6, 1, 1), -32), ((6, 1, 2), -24), ((6, 1, 3), -32), ((6, 1, 4), 44), ((7, 0, 0), -8), ((7, 0, 1), 16), ((7, 0, 3), -16), ((7, 0, 4), 8)]
private def rhsLitPolyW19 : Poly3W19 := [((8, 10, 10), 4), ((8, 10, 11), -16), ((8, 10, 12), 24), ((8, 10, 13), -16), ((8, 10, 14), 4), ((9, 9, 10), -40), ((9, 9, 11), 80), ((9, 9, 13), -80), ((9, 9, 14), 40), ((10, 8, 10), 168), ((10, 8, 11), -96), ((10, 8, 12), -144), ((10, 8, 13), -96), ((10, 8, 14), 168), ((11, 7, 10), -384), ((11, 7, 11), -96), ((11, 7, 13), 96), ((11, 7, 14), 384), ((12, 6, 10), 516), ((12, 6, 11), 240), ((12, 6, 12), 216), ((12, 6, 13), 240), ((12, 6, 14), 516), ((13, 5, 10), -408), ((13, 5, 11), -48), ((13, 5, 13), 48), ((13, 5, 14), 408), ((14, 4, 10), 176), ((14, 4, 11), -128), ((14, 4, 12), -96), ((14, 4, 13), -128), ((14, 4, 14), 176), ((15, 3, 10), -32), ((15, 3, 11), 64), ((15, 3, 13), -64), ((15, 3, 14), 32)]

set_option maxRecDepth 65536 in
private theorem trop3_tri_and_diag_cert_w19 :
    allFinLoopW19 12 (fun r =>
      allFinLoopW19 12 (fun c =>
        if c.val < r.val then poly3EqBoolW19 (poly3At2DW19 u9Trop3PolyTblW19 r.val c.val) []
        else true) 12) 12 = true ∧
    allFinLoopW19 12 (fun r =>
      allFinLoopW19 12 (fun c =>
        if r.val < 9 && r.val < c.val then poly3EqBoolW19 (poly3At2DW19 prodTrop3PolyTblW19 r.val c.val) []
        else true) 12) 12 = true ∧
    poly3EqBoolW19 (diagProdPoly3W19 u9Trop3PolyTblW19 12) [((6, 0, 0), 8)] = true ∧
    poly3EqBoolW19 (diagProdPoly3W19 prodTrop3PolyTblW19 9) diag9LitPolyW19 = true := by decide

private def b10_10LitW19 : Poly3W19 := [((0, 5, 0), -1), ((0, 5, 1), 2), ((0, 5, 2), -1), ((1, 4, 0), 4), ((1, 4, 2), -4), ((2, 3, 0), -5), ((2, 3, 1), -4), ((2, 3, 2), -5), ((3, 2, 0), 2), ((3, 2, 2), -2), ((4, 1, 1), 2)]
private def b11_11aLitW19 : Poly3W19 := [((0, 7, 0), 1), ((0, 7, 1), -4), ((0, 7, 2), 6), ((0, 7, 3), -4), ((0, 7, 4), 1), ((1, 6, 0), -5), ((1, 6, 1), 6), ((1, 6, 2), 12), ((1, 6, 3), -22), ((1, 6, 4), 9), ((2, 5, 0), 7), ((2, 5, 1), 12), ((2, 5, 2), -12), ((2, 5, 3), -40), ((2, 5, 4), 33)]
private def b11_11bLitW19 : Poly3W19 := [((3, 4, 0), 1), ((3, 4, 1), -18), ((3, 4, 2), -24), ((3, 4, 3), -22), ((3, 4, 4), 63), ((4, 3, 0), -8), ((4, 3, 1), 4), ((4, 3, 2), 6), ((4, 3, 3), 8), ((4, 3, 4), 66), ((5, 2, 0), 4), ((5, 2, 2), 12), ((5, 2, 3), 8), ((5, 2, 4), 36), ((6, 1, 4), 8)]
private def b10_11aLitW19 : Poly3W19 := [((0, 7, 0), 1), ((0, 7, 1), -4), ((0, 7, 2), 6), ((0, 7, 3), -4), ((0, 7, 4), 1), ((1, 6, 0), -7), ((1, 6, 1), 14), ((1, 6, 3), -14), ((1, 6, 4), 7), ((2, 5, 0), 19), ((2, 5, 1), -10), ((2, 5, 2), -18), ((2, 5, 3), -10), ((2, 5, 4), 19)]
private def b10_11bLitW19 : Poly3W19 := [((3, 4, 0), -25), ((3, 4, 1), -10), ((3, 4, 3), 10), ((3, 4, 4), 25), ((4, 3, 0), 16), ((4, 3, 1), 14), ((4, 3, 2), 16), ((4, 3, 3), 14), ((4, 3, 4), 16), ((5, 2, 0), -4), ((5, 2, 1), -4), ((5, 2, 3), 4), ((5, 2, 4), 4), ((6, 1, 2), -4)]
private def b11_10LitW19 : Poly3W19 := [((0, 5, 0), -1), ((0, 5, 1), 2), ((0, 5, 2), -1), ((1, 4, 0), 2), ((1, 4, 1), 4), ((1, 4, 2), -6), ((2, 3, 0), 1), ((2, 3, 1), -2), ((2, 3, 2), -13), ((3, 2, 0), -2), ((3, 2, 1), -4), ((3, 2, 2), -12), ((4, 1, 2), -4)]
private def dm0PaLitW19 : Poly3W19 := [((0, 12, 0), -1), ((0, 12, 1), 6), ((0, 12, 2), -15), ((0, 12, 3), 20), ((0, 12, 4), -15), ((0, 12, 5), 6), ((0, 12, 6), -1), ((1, 11, 0), 9), ((1, 11, 1), -32), ((1, 11, 2), 25), ((1, 11, 3), 40), ((1, 11, 4), -85), ((1, 11, 5), 56), ((1, 11, 6), -13), ((2, 10, 0), -32), ((2, 10, 1), 42), ((2, 10, 2), 78), ((2, 10, 3), -92), ((2, 10, 4), -132), ((2, 10, 5), 210), ((2, 10, 6), -74), ((3, 9, 0), 55), ((3, 9, 1), 30), ((3, 9, 2), -125), ((3, 9, 3), -176), ((3, 9, 4), 153), ((3, 9, 5), 242), ((3, 9, 6), -179), ((4, 8, 0), -45), ((4, 8, 1), -74), ((4, 8, 2), 3), ((4, 8, 3), 144), ((4, 8, 4), 41), ((4, 8, 5), 114), ((4, 8, 6), -183), ((5, 7, 0), 14), ((5, 7, 1), 14), ((5, 7, 2), -26), ((5, 7, 3), -80), ((5, 7, 4), 46), ((5, 7, 5), 98), ((5, 7, 6), -66), ((6, 6, 1), 14), ((6, 6, 2), 24), ((6, 6, 3), -24), ((6, 6, 4), -80), ((6, 6, 5), 66)]
private def dm0PbLitW19 : Poly3W19 := [((3, 9, 0), -1), ((3, 9, 1), 20), ((3, 9, 2), -13), ((3, 9, 3), -8), ((3, 9, 4), -83), ((3, 9, 5), 148), ((3, 9, 6), -63), ((4, 8, 0), 12), ((4, 8, 1), -92), ((4, 8, 2), -90), ((4, 8, 3), -16), ((4, 8, 4), 292), ((4, 8, 5), 212), ((4, 8, 6), -318), ((5, 7, 0), -41), ((5, 7, 1), 110), ((5, 7, 2), 227), ((5, 7, 3), 328), ((5, 7, 4), 101), ((5, 7, 5), -110), ((5, 7, 6), -615), ((6, 6, 0), 58), ((6, 6, 1), -24), ((6, 6, 2), -24), ((6, 6, 3), -60), ((6, 6, 4), -130), ((6, 6, 5), -276), ((6, 6, 6), -608), ((7, 5, 0), -36), ((7, 5, 1), -6), ((7, 5, 2), -88), ((7, 5, 3), -128), ((7, 5, 4), -164), ((7, 5, 5), -74), ((7, 5, 6), -344), ((8, 4, 0), 8), ((8, 4, 1), -16), ((8, 4, 2), 24), ((8, 4, 3), 28), ((8, 4, 4), 24), ((8, 4, 5), 84), ((8, 4, 6), -112), ((9, 3, 1), 8), ((9, 3, 3), 24), ((9, 3, 4), 32), ((9, 3, 5), 72), ((9, 3, 6), -16), ((10, 2, 5), 16)]
private def dm0QaLitW19 : Poly3W19 := [((0, 12, 0), -1), ((0, 12, 1), 6), ((0, 12, 2), -15), ((0, 12, 3), 20), ((0, 12, 4), -15), ((0, 12, 5), 6), ((0, 12, 6), -1), ((1, 11, 0), 9), ((1, 11, 1), -32), ((1, 11, 2), 25), ((1, 11, 3), 40), ((1, 11, 4), -85), ((1, 11, 5), 56), ((1, 11, 6), -13), ((2, 10, 0), -32), ((2, 10, 1), 42), ((2, 10, 2), 78), ((2, 10, 3), -92), ((2, 10, 4), -132), ((2, 10, 5), 210), ((2, 10, 6), -74), ((3, 9, 0), 29), ((3, 9, 1), 88), ((3, 9, 2), -135), ((3, 9, 3), -196), ((3, 9, 4), 83), ((3, 9, 5), 348), ((3, 9, 6), -217), ((4, 8, 0), 33), ((4, 8, 1), -48), ((4, 8, 2), -221), ((4, 8, 3), 32), ((4, 8, 4), 291), ((4, 8, 5), 248), ((4, 8, 6), -335), ((5, 7, 0), -38), ((5, 7, 1), -56), ((5, 7, 2), -124), ((5, 7, 3), 156), ((5, 7, 4), 218), ((5, 7, 5), 100), ((5, 7, 6), -256), ((6, 6, 2), -76), ((6, 6, 3), 40), ((6, 6, 4), 72), ((6, 6, 5), 40), ((6, 6, 6), -76)]
private def dm0QbLitW19 : Poly3W19 := [((3, 9, 0), 25), ((3, 9, 1), -40), ((3, 9, 2), 5), ((3, 9, 4), -5), ((3, 9, 5), 40), ((3, 9, 6), -25), ((4, 8, 0), -66), ((4, 8, 1), -102), ((4, 8, 2), 106), ((4, 8, 3), 84), ((4, 8, 4), 86), ((4, 8, 5), 58), ((4, 8, 6), -166), ((5, 7, 0), 11), ((5, 7, 1), 128), ((5, 7, 2), 333), ((5, 7, 3), 148), ((5, 7, 4), 1), ((5, 7, 5), -196), ((5, 7, 6), -425), ((6, 6, 0), 58), ((6, 6, 1), 78), ((6, 6, 2), 132), ((6, 6, 3), -76), ((6, 6, 4), -282), ((6, 6, 5), -442), ((6, 6, 6), -532), ((7, 5, 0), -36), ((7, 5, 1), -88), ((7, 5, 2), -128), ((7, 5, 3), -180), ((7, 5, 4), -260), ((7, 5, 5), -332), ((7, 5, 6), -344), ((8, 4, 0), 8), ((8, 4, 1), 24), ((8, 4, 2), -4), ((8, 4, 3), -8), ((8, 4, 4), -36), ((8, 4, 5), -120), ((8, 4, 6), -112), ((9, 3, 2), 24), ((9, 3, 3), 32), ((9, 3, 4), 48), ((9, 3, 5), -16), ((9, 3, 6), -16), ((10, 2, 4), 16)]

set_option maxRecDepth 65536 in
private theorem trop3_b10_11_split_cert_w19 :
    poly3EqBoolW19 (poly3At2DW19 prodTrop3PolyTblW19 10 10) b10_10LitW19 = true ∧
    poly3EqBoolW19 (poly3At2DW19 prodTrop3PolyTblW19 11 11) (poly3AddW19 b11_11aLitW19 b11_11bLitW19) = true ∧
    poly3EqBoolW19 (poly3At2DW19 prodTrop3PolyTblW19 10 11) (poly3AddW19 b10_11aLitW19 b10_11bLitW19) = true ∧
    poly3EqBoolW19 (poly3At2DW19 prodTrop3PolyTblW19 11 10) b11_10LitW19 = true := by decide

set_option maxRecDepth 65536 in
private theorem trop3_dm0_pa_cert_w19 :
    poly3EqBoolW19 (poly3MulW19 b10_10LitW19 b11_11aLitW19) dm0PaLitW19 = true := by decide

set_option maxRecDepth 65536 in
private theorem trop3_dm0_pb_cert_w19 :
    poly3EqBoolW19 (poly3MulW19 b10_10LitW19 b11_11bLitW19) dm0PbLitW19 = true := by decide

set_option maxRecDepth 65536 in
private theorem trop3_dm0_qa_cert_w19 :
    poly3EqBoolW19 (poly3MulW19 b10_11aLitW19 b11_10LitW19) dm0QaLitW19 = true := by decide

set_option maxRecDepth 65536 in
private theorem trop3_dm0_qb_cert_w19 :
    poly3EqBoolW19 (poly3MulW19 b10_11bLitW19 b11_10LitW19) dm0QbLitW19 = true := by decide

set_option maxRecDepth 65536 in
private theorem trop3_dm0_sum_cert_w19 :
    poly3EqBoolW19
      (poly3SubW19 (poly3AddW19 dm0PaLitW19 dm0PbLitW19) (poly3AddW19 dm0QaLitW19 dm0QbLitW19))
      det3M0LitPolyW19 = true := by decide

private theorem trop3_dm0_eval_w19 (w k X : Int) :
    evalPoly3W19 w k X (poly3At2DW19 prodTrop3PolyTblW19 10 10) *
      evalPoly3W19 w k X (poly3At2DW19 prodTrop3PolyTblW19 11 11) -
    evalPoly3W19 w k X (poly3At2DW19 prodTrop3PolyTblW19 10 11) *
      evalPoly3W19 w k X (poly3At2DW19 prodTrop3PolyTblW19 11 10) =
    evalPoly3W19 w k X det3M0LitPolyW19 := by
  rcases trop3_b10_11_split_cert_w19 with ⟨hb10_10, hb11_11, hb10_11, hb11_10⟩
  have e10_10 := poly3EqBoolW19_sound w k X _ _ hb10_10
  have e11_11 := poly3EqBoolW19_sound w k X _ _ hb11_11
  have e10_11 := poly3EqBoolW19_sound w k X _ _ hb10_11
  have e11_10 := poly3EqBoolW19_sound w k X _ _ hb11_10
  have hpa := poly3EqBoolW19_sound w k X _ _ trop3_dm0_pa_cert_w19
  have hpb := poly3EqBoolW19_sound w k X _ _ trop3_dm0_pb_cert_w19
  have hqa := poly3EqBoolW19_sound w k X _ _ trop3_dm0_qa_cert_w19
  have hqb := poly3EqBoolW19_sound w k X _ _ trop3_dm0_qb_cert_w19
  have hsum := poly3EqBoolW19_sound w k X _ _ trop3_dm0_sum_cert_w19
  rw [evalPoly3W19_add] at e11_11 e10_11
  rw [evalPoly3W19_mul] at hpa hpb hqa hqb
  rw [evalPoly3W19_sub, evalPoly3W19_add, evalPoly3W19_add] at hsum
  rw [e10_10, e11_11, e10_11, e11_10, Int.mul_add, Int.add_mul, hpa, hpb, hqa, hqb, hsum]

set_option maxRecDepth 65536 in
private theorem trop3_dm1_cert_w19 :
    poly3EqBoolW19
      (poly3SubW19 (poly3MulW19 (poly3At2DW19 prodTrop3PolyTblW19 10 9) (poly3At2DW19 prodTrop3PolyTblW19 11 11))
                   (poly3MulW19 (poly3At2DW19 prodTrop3PolyTblW19 10 11) (poly3At2DW19 prodTrop3PolyTblW19 11 9)))
      det3M1LitPolyW19 = true := by decide

set_option maxRecDepth 65536 in
private theorem trop3_dm2_cert_w19 :
    poly3EqBoolW19
      (poly3SubW19 (poly3MulW19 (poly3At2DW19 prodTrop3PolyTblW19 10 9) (poly3At2DW19 prodTrop3PolyTblW19 11 10))
                   (poly3MulW19 (poly3At2DW19 prodTrop3PolyTblW19 10 10) (poly3At2DW19 prodTrop3PolyTblW19 11 9)))
      det3M2LitPolyW19 = true := by decide

set_option maxRecDepth 65536 in
private theorem trop3_b9_split_cert_w19 :
    poly3EqBoolW19 (poly3At2DW19 prodTrop3PolyTblW19 9 9) b9_9LitW19 = true ∧
    poly3EqBoolW19 (poly3At2DW19 prodTrop3PolyTblW19 9 10) (poly3AddW19 b9_10aLitW19 b9_10bLitW19) = true ∧
    poly3EqBoolW19 (poly3At2DW19 prodTrop3PolyTblW19 9 11) (poly3AddW19 b9_11aLitW19 b9_11bLitW19) = true := by decide

set_option maxRecDepth 65536 in
private theorem trop3_t0_cert_w19 :
    poly3EqBoolW19 (poly3MulW19 b9_9LitW19 det3M0LitPolyW19) det3T0LitPolyW19 = true := by decide

set_option maxRecDepth 65536 in
private theorem trop3_t1a_cert_w19 :
    poly3EqBoolW19 (poly3MulW19 b9_10aLitW19 det3M1LitPolyW19) t1aLitW19 = true := by decide

set_option maxRecDepth 65536 in
private theorem trop3_t1b_cert_w19 :
    poly3EqBoolW19 (poly3MulW19 b9_10bLitW19 det3M1LitPolyW19) t1bLitW19 = true := by decide

set_option maxRecDepth 65536 in
private theorem trop3_t2a_cert_w19 :
    poly3EqBoolW19 (poly3MulW19 b9_11aLitW19 det3M2LitPolyW19) t2aLitW19 = true := by decide

set_option maxRecDepth 65536 in
private theorem trop3_t2b_cert_w19 :
    poly3EqBoolW19 (poly3MulW19 b9_11bLitW19 det3M2LitPolyW19) t2bLitW19 = true := by decide

set_option maxRecDepth 65536 in
private theorem trop3_det3_cert_w19 :
    poly3EqBoolW19 (poly3AddW19 t1aLitW19 t1bLitW19) det3T1LitPolyW19 = true ∧
    poly3EqBoolW19 (poly3AddW19 t2aLitW19 t2bLitW19) det3T2LitPolyW19 = true ∧
    poly3EqBoolW19 (poly3AddW19 (poly3SubW19 det3T0LitPolyW19 det3T1LitPolyW19) det3T2LitPolyW19)
      det3LitPolyW19 = true := by decide

set_option maxRecDepth 65536 in
private theorem trop3_rhs_step_cert_w19 :
    let wP : Poly3W19 := [((1, 0, 0), 1)]
    let kP : Poly3W19 := [((0, 1, 0), 1)]
    let xm1 : Poly3W19 := [((0, 0, 1), 1), ((0, 0, 0), -1)]
    let xp1 : Poly3W19 := [((0, 0, 1), 1), ((0, 0, 0), 1)]
    let linF := poly3AddW19 (poly3MulW19 xm1 kP) (poly3MulW19 xp1 wP)
    let qP := poly3AddW19
      (poly3AddW19 (poly3MulW19 xm1 (poly3MulW19 kP kP))
                   (poly3MulW19 [((0, 0, 0), 3)] (poly3MulW19 xp1 (poly3MulW19 wP kP))))
      (poly3MulW19 [((0, 0, 0), 2)] (poly3MulW19 xm1 (poly3MulW19 wP wP)))
    poly3EqBoolW19 linF linFLitPolyW19 = true ∧
    poly3EqBoolW19 qP qLitPolyW19 = true ∧
    poly3EqBoolW19 (poly3MulW19 qLitPolyW19 qLitPolyW19) q2LitPolyW19 = true ∧
    poly3EqBoolW19 (poly3MulW19 qLitPolyW19 q2LitPolyW19) q3LitPolyW19 = true := by decide

set_option maxRecDepth 65536 in
private theorem trop3_final_mul_cert_w19 :
    poly3EqBoolW19 (poly3MulW19 linFLitPolyW19 q3LitPolyW19) linQ3LitPolyW19 = true ∧
    poly3EqBoolW19 (poly3MulW19 [((8, 3, 10), 4)] linQ3LitPolyW19) rhsLitPolyW19 = true ∧
    poly3EqBoolW19 (poly3MulW19 diag9LitPolyW19 det3LitPolyW19)
                   (poly3MulW19 [((6, 0, 0), 8)] rhsLitPolyW19) = true := by decide

private theorem intDet_last_two_rows_eq_zero_w19 :
    ∀ (k : Nat) (A : Fin (k + 2) -> Fin (k + 2) -> Int),
      (∀ j : Fin (k + 2), A ⟨k, by omega⟩ j = A ⟨k + 1, by omega⟩ j) ->
      intDet (k + 2) A = 0
  | 0, A, heq => by
    rw [intDet_two A, heq ⟨0, by decide⟩, heq ⟨1, by decide⟩]
    rw [Int.mul_comm (A ⟨1, by decide⟩ ⟨0, by decide⟩) (A ⟨1, by decide⟩ ⟨1, by decide⟩), Int.sub_self]
  | k' + 1, A, heq => by
    have hsub0 : ∀ j : Fin (k' + 3), intDet (k' + 2) (intSubMat A j) = 0 := by
      intro j
      apply intDet_last_two_rows_eq_zero_w19 k' (intSubMat A j)
      intro c
      unfold intSubMat
      exact heq (skipFinIdx j c)
    unfold intDet intSumFin
    have hst : ∀ m : Nat, m ≤ k' + 3 ->
        intSumPrefix (k' + 3) (fun j =>
          (if j.val % 2 = 0 then 1 else -1) * A ⟨0, Nat.zero_lt_succ _⟩ j * intDet (k' + 2) (intSubMat A j)) m = 0 := by
      intro m hm; induction m with
      | zero => rfl
      | succ m' ih =>
        have hm_lt : m' < k' + 3 := hm
        simp only [intSumPrefix, hm_lt, dite_true, ih (Nat.le_of_lt hm), hsub0 ⟨m', hm_lt⟩, Int.mul_zero, Int.add_zero]
    exact hst (k' + 3) (Nat.le_refl _)

private theorem laurentTrop3Mat12Explicit_closed_form_w19 (W K u : Nat) (hu : u ≥ 1) :
    27 * intDet 12 (laurentTrop3Mat12Explicit W K u) =
      Int.ofNat (2 ^ (10 * u - 4) * W ^ 8 * K ^ 3 * ((2 ^ u - 1) * K + (2 ^ u + 1) * W) *
        (laurentTrop3ResonantQuad W K u) ^ 3) := by
  by_cases hW0 : W = 0
  · subst hW0
    have hdet0 : intDet 12 (laurentTrop3Mat12Explicit 0 K u) = 0 := by
      apply intDet_last_two_rows_eq_zero_w19 10 (laurentTrop3Mat12Explicit 0 K u)
      rintro ⟨j, hj⟩
      unfold laurentTrop3Mat12Explicit trop3ActiveBoolExplicit aRow3TropExplicit bCol3TropExplicit
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨
          j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp
    rw [hdet0, Int.mul_zero]
    have hz8 : (0 : Nat) ^ 8 = 0 := by decide
    rw [hz8]; simp
  · have hW1 : W ≥ 1 := by omega
    let w : Int := (W : Int)
    let k : Int := (K : Int)
    let X : Int := ((2 ^ u : Nat) : Int)
    have hstirl : 1728 * intDet 12 (laurentTrop3Mat12Explicit W K u) = intDet 12 (trop3PowMat12W19 w k X) := by
      let xFn (i : Fin 12) : Nat := i.val % 3 * W + i.val / 3 * K
      let eFn (i : Fin 12) (m : Nat) : Int :=
        if trop3ActiveBoolExplicit (i.val / 3) m then ((2 ^ (i.val % 3 * (m * u)) : Nat) : Int) else 0
      have hin : laurentTrop3Mat12Explicit W K u =
          (fun i j => ((laurentInterpBinom (xFn i) (j.val % 4) : Nat) : Int) * eFn i (j.val / 4)) := by
        funext i j
        unfold laurentTrop3Mat12Explicit
        dsimp only [xFn, eFn]
        by_cases ha : trop3ActiveBoolExplicit (i.val / 3) (j.val / 4) = true
        · rw [ite_true_of_w10 ha, ite_true_of_w10 ha]; exact Int.natCast_mul _ _
        · rw [ite_false_of_w10 ha, ite_false_of_w10 ha, Int.mul_zero]
      have hout : (fun i j : Fin 12 => intPowNat ((xFn i : Nat) : Int) (j.val % 4) * eFn i (j.val / 4)) =
          trop3PowMat12W19 w k X := by
        funext i j
        dsimp only [xFn, eFn, trop3PowMat12W19, w, k, X]
        let r : Nat := i.val % 3
        let s : Nat := i.val / 3
        have hlin : ((r * W + s * K : Nat) : Int) = (r : Int) * (W : Int) + (s : Int) * (K : Int) := by
          simp [Int.natCast_add, Int.natCast_mul]
        change intPowNat ((r * W + s * K : Nat) : Int) (j.val % 4) *
            (if trop3ActiveBoolExplicit s (j.val / 4) = true then ((2 ^ (r * (j.val / 4 * u)) : Nat) : Int) else 0) =
          if trop3ActiveBoolExplicit s (j.val / 4) = true then
            intPowNat ((r : Int) * (W : Int) + (s : Int) * (K : Int)) (j.val % 4) *
              intPowNat ((2 ^ u : Nat) : Int) (r * (j.val / 4))
          else 0
        rw [hlin]
        by_cases ha : trop3ActiveBoolExplicit s (j.val / 4) = true
        · rw [ite_true_of_w10 ha, ite_true_of_w10 ha, intPowNat_natCast_w19 (2 ^ u) (r * (j.val / 4))]
          apply congrArg (intPowNat ((r : Int) * (W : Int) + (s : Int) * (K : Int)) (j.val % 4) * ·)
          apply congrArg Int.ofNat
          rw [pow_pow_eq_mul_w5 2 u (r * (j.val / 4))]
          apply congrArg (2 ^ ·); ac_rfl
        · rw [ite_false_of_w10 ha, ite_false_of_w10 ha, Int.mul_zero]
      have hs3 := stirling_order4_blocks_w19 3 xFn eFn
      rw [show ((12 ^ 3 : Nat) : Int) = 1728 by decide] at hs3
      change 1728 * intDet 12 (fun i j => ((laurentInterpBinom (xFn i) (j.val % 4) : Nat) : Int) * eFn i (j.val / 4)) =
        intDet 12 (fun i j => intPowNat ((xFn i : Nat) : Int) (j.val % 4) * eFn i (j.val / 4)) at hs3
      rwa [hin, ← hout]
    rcases trop3_tri_and_diag_cert_w19 with ⟨hup_b, hlow9_b, hudiag_b, hdiag9_b⟩
    have hdm1_b := trop3_dm1_cert_w19
    have hdm2_b := trop3_dm2_cert_w19
    have hdet3_b := trop3_det3_cert_w19
    rcases trop3_rhs_step_cert_w19 with ⟨hlin_b, hq_b, hq2_b, hq3_b⟩
    rcases trop3_final_mul_cert_w19 with ⟨hlinq3_b, hrhs_lit_b, hfinal_b⟩
    let Ap (i j : Fin 12) : Int := evalPoly3W19 w k X (poly3At2DW19 apTrop3PolyTblW19 i.val j.val)
    let U9 (i j : Fin 12) : Int := evalPoly3W19 w k X (poly3At2DW19 u9Trop3PolyTblW19 i.val j.val)
    let Prod (i j : Fin 12) : Int := evalPoly3W19 w k X (poly3At2DW19 prodTrop3PolyTblW19 i.val j.val)
    have hAp_det : intDet 12 Ap = intDet 12 (trop3PowMat12W19 w k X) := by
      let m0P := buildMat12Poly3W19 trop3EntryPoly3W19
      have hap_tbl : Ap = (fun i j : Fin 12 =>
          evalPoly3W19 w k X (poly3At2DW19 (applySignedSwapsPoly3W19 trop3SwapsW19 m0P) i.val j.val)) := by
        funext i j
        exact (poly3MatEqBoolW19_sound w k X _ apTrop3PolyTblW19 i.val j.val trop3_ap_ok_w19).symm
      have hm0_eq : (fun i j : Fin 12 => evalPoly3W19 w k X (poly3At2DW19 m0P i.val j.val)) =
          trop3PowMat12W19 w k X := by
        funext i j
        exact (congrArg (evalPoly3W19 w k X)
          (poly3At2DW19_buildMat12 trop3EntryPoly3W19 i.val j.val i.isLt j.isLt)).trans
          (evalPoly3W19_trop3Entry w k X i j)
      have hap_sw := eval_applySignedSwapsPoly3W19 w k X trop3SwapsW19 m0P
      rw [hap_tbl, ← hap_sw, hm0_eq]
      exact applySignedSwapsIntW19_det 12 trop3SwapsW19 (trop3PowMat12W19 w k X)
    have hProd_eq : Prod = (fun i j : Fin 12 => intSumPrefix 12 (fun q => Ap i q * U9 q j) 12) := by
      have hrow_ok : ∀ r : Nat, r < 12 -> checkTrop3ProdRowBoolW19 r = true := by
        intro r hr
        rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨
            r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact trop3_prod_s0_w19.1
        · exact trop3_prod_s0_w19.2.1
        · exact trop3_prod_s0_w19.2.2
        · exact trop3_prod_s1_w19.1
        · exact trop3_prod_s1_w19.2.1
        · exact trop3_prod_s1_w19.2.2
        · exact trop3_prod_s2_w19.1
        · exact trop3_prod_s2_w19.2.1
        · exact trop3_prod_s2_w19.2.2
        · exact trop3_prod_s3_w19.1
        · exact trop3_prod_s3_w19.2.1
        · exact trop3_prod_s3_w19.2.2
      funext i j
      have hr_eq := poly3RowEqBoolW19_sound w k X _ _ j.val (hrow_ok i.val i.isLt)
      rw [← poly3At2DW19_eq_rowAt prodTrop3PolyTblW19 i.val j.val,
          poly3At1DW19_buildRow12 _ j.val j.isLt] at hr_eq
      exact hr_eq.trans (eval_dotPrefixPoly3W19 w k X apTrop3PolyTblW19 u9Trop3PolyTblW19 i j 12 (Nat.le_refl 12))
    have hU9_up : ∀ r c : Fin 12, c.val < r.val -> U9 r c = 0 := by
      intro r c hlt
      have hb := allFinLoopW19_spec 12 _ (allFinLoopW19_spec 12 _ hup_b r) c
      rw [ite_true_of_w10 hlt] at hb
      exact poly3EqBoolW19_sound w k X _ [] hb
    have hProd_low9 : ∀ r c : Fin 12, r.val < 9 -> r.val < c.val -> Prod r c = 0 := by
      intro r c hr9 hrc
      have hb := allFinLoopW19_spec 12 _ (allFinLoopW19_spec 12 _ hlow9_b r) c
      have hcond : (decide (r.val < 9) && decide (r.val < c.val)) = true := by
        rw [decide_eq_true hr9, decide_eq_true hrc]; rfl
      rw [ite_true_of_w10 hcond] at hb
      exact poly3EqBoolW19_sound w k X _ [] hb
    have hdet_prod1 : intDet 12 Prod = intDiagProdPrefixW19 12 U9 12 * intDet 12 Ap := by
      rw [hProd_eq]; exact intDet_mul_upper_tri_w19 12 Ap U9 hU9_up
    have hdet_prod2 : intDet 12 Prod =
        intDiagProdPrefixW19 12 Prod 9 *
          intDet 3 (fun a b => Prod ⟨9 + a.val, by omega⟩ ⟨9 + b.val, by omega⟩) :=
      intDet_peel_lower_rows_w19 9 3 Prod hProd_low9
    have hdet3_eval : evalPoly3W19 w k X det3LitPolyW19 =
        intDet 3 (fun a b => Prod ⟨9 + a.val, by omega⟩ ⟨9 + b.val, by omega⟩) := by
      rcases trop3_b9_split_cert_w19 with ⟨hb9_9, hb9_10, hb9_11⟩
      rcases hdet3_b with ⟨ht1_s, ht2_s, hd3_s⟩
      have hm0 := trop3_dm0_eval_w19 w k X
      have hm1 := poly3EqBoolW19_sound w k X _ _ hdm1_b
      have hm2 := poly3EqBoolW19_sound w k X _ _ hdm2_b
      have he9_9 := poly3EqBoolW19_sound w k X _ _ hb9_9
      have he9_10 := poly3EqBoolW19_sound w k X _ _ hb9_10
      have he9_11 := poly3EqBoolW19_sound w k X _ _ hb9_11
      have ht0 := poly3EqBoolW19_sound w k X _ _ trop3_t0_cert_w19
      have ht1a := poly3EqBoolW19_sound w k X _ _ trop3_t1a_cert_w19
      have ht1b := poly3EqBoolW19_sound w k X _ _ trop3_t1b_cert_w19
      have ht2a := poly3EqBoolW19_sound w k X _ _ trop3_t2a_cert_w19
      have ht2b := poly3EqBoolW19_sound w k X _ _ trop3_t2b_cert_w19
      have ht1 := poly3EqBoolW19_sound w k X _ _ ht1_s
      have ht2 := poly3EqBoolW19_sound w k X _ _ ht2_s
      have hd3 := (poly3EqBoolW19_sound w k X _ _ hd3_s).symm
      rw [evalPoly3W19_add] at he9_10 he9_11 ht1 ht2
      rw [evalPoly3W19_mul] at ht0 ht1a ht1b ht2a ht2b
      rw [intDet_three, hd3, evalPoly3W19_add, evalPoly3W19_sub, ← ht0, ← ht1, ← ht2,
          ← ht1a, ← ht1b, ← ht2a, ← ht2b, ← Int.add_mul, ← Int.add_mul,
          ← he9_9, ← he9_10, ← he9_11, ← hm0, ← hm1, ← hm2]
      simp only [evalPoly3W19_sub, evalPoly3W19_mul]
      rfl
    have hdiag9_eval : evalPoly3W19 w k X diag9LitPolyW19 = intDiagProdPrefixW19 12 Prod 9 :=
      (poly3EqBoolW19_sound w k X _ _ hdiag9_b).symm.trans
        (eval_diagProdPoly3W19 w k X prodTrop3PolyTblW19 9 (by decide))
    have hudiag_lit : evalPoly3W19 w k X [((6, 0, 0), 8)] = intDiagProdPrefixW19 12 U9 12 :=
      (poly3EqBoolW19_sound w k X _ _ hudiag_b).symm.trans
        (eval_diagProdPoly3W19 w k X u9Trop3PolyTblW19 12 (Nat.le_refl 12))
    have hudiag_eval : intDiagProdPrefixW19 12 U9 12 = 8 * intPowNat w 6 := by
      rw [← hudiag_lit]; simp [evalPoly3W19, evalMono3W19, intPowNat]
    have hlhs_rhs := poly3EqBoolW19_sound w k X _ _ hfinal_b
    rw [evalPoly3W19_mul, evalPoly3W19_mul, hdiag9_eval, hdet3_eval, hudiag_lit] at hlhs_rhs
    have hmul_u : intDiagProdPrefixW19 12 U9 12 * intDet 12 Ap =
        intDiagProdPrefixW19 12 U9 12 * evalPoly3W19 w k X rhsLitPolyW19 := by
      rw [← hdet_prod1, hdet_prod2, hlhs_rhs]
    have hu_nz : intDiagProdPrefixW19 12 U9 12 ≠ 0 := by
      rw [hudiag_eval]; dsimp [w]; rw [intPowNat_natCast_w19 W 6]
      have hp6 := nat_pow_pos_of_pos W hW1 6
      omega
    have hap_val : intDet 12 (trop3PowMat12W19 w k X) = evalPoly3W19 w k X rhsLitPolyW19 := by
      rw [← hAp_det]; exact Int.eq_of_mul_eq_mul_left hu_nz hmul_u
    have hrhs_eq_target : evalPoly3W19 w k X rhsLitPolyW19 = evalPoly3W19 w k X rhsTrop3TargetPolyW19 := by
      have hl1 := poly3EqBoolW19_sound w k X _ _ hlin_b
      have hq1 := poly3EqBoolW19_sound w k X _ _ hq_b
      have hq2 := poly3EqBoolW19_sound w k X _ _ hq2_b
      have hq3 := poly3EqBoolW19_sound w k X _ _ hq3_b
      have hlq3 := poly3EqBoolW19_sound w k X _ _ hlinq3_b
      have hr1 := (poly3EqBoolW19_sound w k X _ _ hrhs_lit_b).symm
      rw [evalPoly3W19_mul] at hq2 hq3 hlq3 hr1
      unfold rhsTrop3TargetPolyW19
      dsimp only
      have hp3_unfold : ∀ P0 : Poly3W19, poly3PowW19 P0 3 = poly3MulW19 P0 (poly3MulW19 P0 (poly3MulW19 P0 [((0, 0, 0), 1)])) :=
        fun _ => rfl
      rw [hp3_unfold, evalPoly3W19_mul, evalPoly3W19_mul, evalPoly3W19_mul, evalPoly3W19_mul, evalPoly3W19_mul]
      have hone : evalPoly3W19 w k X [((0, 0, 0), 1)] = 1 := by simp [evalPoly3W19, evalMono3W19, intPowNat]
      rw [hone, Int.mul_one, hq1, hq2, hq3, hl1, hlq3, ← hr1]
    rw [hrhs_eq_target] at hap_val
    -- Evaluate `rhsTrop3TargetPolyW19` on `w = W, k = K, X = 2^u` (`2^u ≥ 2`):
    have h2u_ge2 : 2 ^ u ≥ 2 := by simpa using pow2_mono_nat hu
    have hxm1 : evalPoly3W19 w k X [((0, 0, 1), 1), ((0, 0, 0), -1)] = ((2 ^ u - 1 : Nat) : Int) := by
      simp only [evalPoly3W19, evalMono3W19, intPowNat, X]
      omega
    have hxp1 : evalPoly3W19 w k X [((0, 0, 1), 1), ((0, 0, 0), 1)] = ((2 ^ u + 1 : Nat) : Int) := by
      simp only [evalPoly3W19, evalMono3W19, intPowNat, X]
      omega
    have hwP : evalPoly3W19 w k X [((1, 0, 0), 1)] = (W : Int) := by
      simp [evalPoly3W19, evalMono3W19, intPowNat, w]
    have hkP : evalPoly3W19 w k X [((0, 1, 0), 1)] = (K : Int) := by
      simp [evalPoly3W19, evalMono3W19, intPowNat, k]
    have hlead : evalPoly3W19 w k X [((8, 3, 10), 4)] =
        64 * ((2 ^ (10 * u - 4) * W ^ 8 * K ^ 3 : Nat) : Int) := by
      simp only [evalPoly3W19, evalMono3W19, Int.add_zero, w, k, X,
                 intPowNat_natCast_w19 W 8, intPowNat_natCast_w19 K 3, intPowNat_natCast_w19 (2 ^ u) 10]
      have hp10 : 4 * ((2 ^ u) ^ 10 * W ^ 8 * K ^ 3) = 64 * (2 ^ (10 * u - 4) * W ^ 8 * K ^ 3) := by
        rw [pow_pow_eq_mul_w5 2 u 10, show u * 10 = 10 * u by omega,
            ← Nat.mul_assoc 4, ← Nat.mul_assoc 4,
            show 4 * 2 ^ (10 * u) = 64 * 2 ^ (10 * u - 4) by
              rw [show (4 : Nat) = 2 ^ 2 by decide, ← Nat.pow_add,
                  show (64 : Nat) = 2 ^ 6 by decide, ← Nat.pow_add,
                  show 2 + 10 * u = 6 + (10 * u - 4) by omega]]
        ac_rfl
      have hc := congrArg (fun n : Nat => (n : Int)) hp10
      simp only [Int.natCast_mul] at hc ⊢
      calc (4 : Int) * (((W ^ 8 : Nat) : Int) * ((K ^ 3 : Nat) : Int) * (((2 ^ u) ^ 10 : Nat) : Int))
          = ((4 : Nat) : Int) * ((((2 ^ u) ^ 10 : Nat) : Int) * ((W ^ 8 : Nat) : Int) * ((K ^ 3 : Nat) : Int)) := by
              rw [show (4 : Int) = ((4 : Nat) : Int) from rfl]; ac_rfl
        _ = ((64 : Nat) : Int) * (((2 ^ (10 * u - 4) : Nat) : Int) * ((W ^ 8 : Nat) : Int) * ((K ^ 3 : Nat) : Int)) := hc
        _ = 64 * (((2 ^ (10 * u - 4) : Nat) : Int) * ((W ^ 8 : Nat) : Int) * ((K ^ 3 : Nat) : Int)) := rfl
    have hrhs_eval : evalPoly3W19 w k X rhsTrop3TargetPolyW19 =
        64 * Int.ofNat (2 ^ (10 * u - 4) * W ^ 8 * K ^ 3 *
          ((2 ^ u - 1) * K + (2 ^ u + 1) * W) * (laurentTrop3ResonantQuad W K u) ^ 3) := by
      unfold rhsTrop3TargetPolyW19
      simp only [evalPoly3W19_mul, evalPoly3W19_add, evalPoly3W19_pow,
                 hxm1, hxp1, hwP, hkP, hlead]
      have hc3 : evalPoly3W19 w k X [((0, 0, 0), 3)] = ((3 : Nat) : Int) := by
        simp [evalPoly3W19, evalMono3W19, intPowNat]
      have hc2 : evalPoly3W19 w k X [((0, 0, 0), 2)] = ((2 : Nat) : Int) := by
        simp [evalPoly3W19, evalMono3W19, intPowNat]
      rw [hc3, hc2]
      have hq_eq : ((2 ^ u - 1 : Nat) : Int) * ((K : Int) * (K : Int)) +
          ((3 : Nat) : Int) * (((2 ^ u + 1 : Nat) : Int) * ((W : Int) * (K : Int))) +
          ((2 : Nat) : Int) * (((2 ^ u - 1 : Nat) : Int) * ((W : Int) * (W : Int))) =
          (laurentTrop3ResonantQuad W K u : Int) := by
        unfold laurentTrop3ResonantQuad
        simp only [Int.natCast_add, Int.natCast_mul]
        ac_rfl
      rw [hq_eq, intPowNat_natCast_w19 (laurentTrop3ResonantQuad W K u) 3]
      change _ = 64 * ((2 ^ (10 * u - 4) * W ^ 8 * K ^ 3 *
        ((2 ^ u - 1) * K + (2 ^ u + 1) * W) * (laurentTrop3ResonantQuad W K u) ^ 3 : Nat) : Int)
      simp only [Int.natCast_mul, Int.natCast_add]
      ac_rfl
    have h64 : 64 * (27 * intDet 12 (laurentTrop3Mat12Explicit W K u)) =
        64 * Int.ofNat (2 ^ (10 * u - 4) * W ^ 8 * K ^ 3 *
          ((2 ^ u - 1) * K + (2 ^ u + 1) * W) * (laurentTrop3ResonantQuad W K u) ^ 3) := by
      rw [← Int.mul_assoc 64 27, show (64 * 27 : Int) = 1728 by decide, hstirl, hap_val, hrhs_eval]
    exact Int.eq_of_mul_eq_mul_left (by decide : (64 : Int) ≠ 0) h64

-- 3-Adic Prime-Power Cancellation & Cube Valuation Squeeze (`3^(3*e + 1) ∣ Q^3 -> 3^(e + 1) ∣ Q`):
private theorem cancel_coprime3_pow_dvd_w19 (F : Nat) (hF : F % 3 ≠ 0) :
    ∀ (m X : Nat), 3 ^ m ∣ F * X -> 3 ^ m ∣ X
  | 0, _ => fun _ => ⟨_, (Nat.one_mul _).symm⟩
  | m' + 1, X => fun hd => by
    have hd3 : 3 ∣ F * X := by
      rcases hd with ⟨q, hq⟩
      rw [Nat.pow_succ] at hq
      exact ⟨3 ^ m' * q, by rw [hq]; ac_rfl⟩
    have hm0 : (F * X) % 3 = 0 := Nat.mod_eq_zero_of_dvd hd3
    have hX3 : X % 3 = 0 := by
      rw [Nat.mul_mod] at hm0
      rcases (by have := Nat.mod_lt F (by decide : 0 < 3); omega : F % 3 = 1 ∨ F % 3 = 2) with hf | hf <;>
      rcases (by have := Nat.mod_lt X (by decide : 0 < 3); omega : X % 3 = 0 ∨ X % 3 = 1 ∨ X % 3 = 2) with hx | hx | hx <;>
      (rw [hf, hx] at hm0; try omega)
    rcases Nat.dvd_of_mod_eq_zero hX3 with ⟨X', hX'⟩
    rcases hd with ⟨q, hq⟩
    have hsub : 3 ^ m' ∣ F * X' := by
      refine ⟨q, ?_⟩
      have h3 : 3 * (F * X') = 3 * (3 ^ m' * q) := by
        calc 3 * (F * X') = F * (3 * X') := by ac_rfl
          _ = F * X := by rw [← hX']
          _ = 3 ^ (m' + 1) * q := hq
          _ = 3 * (3 ^ m' * q) := by rw [Nat.pow_succ]; ac_rfl
      exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3) h3
    rcases cancel_coprime3_pow_dvd_w19 F hF m' X' hsub with ⟨q', hq'⟩
    exact ⟨q', by rw [hX', hq', Nat.pow_succ]; ac_rfl⟩

private theorem pow3_dvd_of_cube_dvd_w19 :
    ∀ (e Q : Nat), 3 ^ (3 * e + 1) ∣ Q ^ 3 -> 3 ^ (e + 1) ∣ Q
  | 0, Q, hd => by
    simp only [Nat.mul_zero, Nat.zero_add, Nat.pow_one] at hd ⊢
    by_cases hm : Q % 3 = 0
    · exact Nat.dvd_of_mod_eq_zero hm
    · exfalso
      have hq3_nz : (Q ^ 3) % 3 ≠ 0 := by
        have hm0 := Nat.mod_eq_zero_of_dvd hd
        have hcub_q : Q ^ 3 = Q * (Q * Q) := by
          simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]; ac_rfl
        rw [hcub_q, Nat.mul_mod, Nat.mul_mod Q Q 3] at hm0
        rcases (by have := Nat.mod_lt Q (by decide : 0 < 3); omega : Q % 3 = 1 ∨ Q % 3 = 2) with h | h <;>
        (rw [h] at hm0; omega)
      exact hq3_nz (Nat.mod_eq_zero_of_dvd hd)
  | e' + 1, Q, hd => by
    have hd1 : 3 ^ (3 * 0 + 1) ∣ Q ^ 3 := by
      rcases hd with ⟨q, hq⟩
      exact ⟨3 ^ (3 * (e' + 1)) * q, by
        rw [hq, show 3 * 0 + 1 = 1 by decide, ← Nat.mul_assoc, ← Nat.pow_add,
            show 1 + 3 * (e' + 1) = 3 * (e' + 1) + 1 by omega]⟩
    rcases pow3_dvd_of_cube_dvd_w19 0 Q hd1 with ⟨Q', hQ'⟩
    rw [show 0 + 1 = 1 from rfl, Nat.pow_one] at hQ'
    have hQ3 : Q ^ 3 = 27 * (Q' ^ 3) := by
      rw [hQ', mul_pow_w19 3 Q' 3]
    rcases hd with ⟨q, hq⟩
    have hsub : 3 ^ (3 * e' + 1) ∣ Q' ^ 3 := by
      refine ⟨q, ?_⟩
      have h27 : 27 * (Q' ^ 3) = 27 * (3 ^ (3 * e' + 1) * q) := by
        rw [← hQ3, hq, show 3 * (e' + 1) + 1 = 3 + (3 * e' + 1) by omega, Nat.pow_add,
            show (3 : Nat) ^ 3 = 27 by decide, Nat.mul_assoc]
      exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 27) h27
    rcases pow3_dvd_of_cube_dvd_w19 e' Q' hsub with ⟨q', hq'⟩
    have hpow_step : 3 * 3 ^ (e' + 1) = 3 ^ (e' + 1 + 1) := by
      conv => rhs; rw [Nat.pow_succ 3 (e' + 1), Nat.mul_comm]
    exact ⟨q', by rw [hQ', hq', ← Nat.mul_assoc 3 (3 ^ (e' + 1)) q', hpow_step]⟩

-- ============================================================================
-- Mod-`p` Signed-Swap + Unit-Upper-Triangular `SL_N(F_p)` Sieves (`N = 12` & `N = 16`)
-- ============================================================================

private def qCubicW19 (r : Nat) (w y : Int) : Int :=
  match r with
  | 0 => (y - w) * (y - 2 * w)
  | 1 => (w + y) * (y - w)
  | _ => (2 * w + y) * (w + y)

private def apow12UW19 (u : Nat) (w k : Int) (i j : Fin 12) : Int :=
  let r := (laurentRowsTwoBase12 i).1
  let s := (laurentRowsTwoBase12 i).2
  let t := j.val % 4
  let m := (j.val / 4) * u
  intPowNat ((r : Int) * w + (s : Int) * k) t *
    ((2 ^ (r * m) * 3 ^ (s * m) : Nat) : Int)

private def apow12KDivW19 (u : Nat) (w k : Int) (i j : Fin 12) : Int :=
  let r := i.val % 3; let s := i.val / 3
  let t := j.val % 4; let m := j.val / 4
  let E : Int := ((2 ^ (r * (m * u)) * 3 ^ (s * (m * u)) : Nat) : Int)
  if t < 3 then intPowNat ((r : Int) * w + (s : Int) * k) t * E
  else (s : Int) * qCubicW19 r w ((s : Int) * k) * E

private theorem stirling_1728_det12_t4u3_u_w19 (u W K : Nat) :
    1728 * intDet 12 (laurentTwoBaseT4U3Mat12 W K u) =
      intDet 12 (apow12UW19 u (W : Int) (K : Int)) := by
  have heq_in : laurentTwoBaseT4U3Mat12 W K u =
      (fun i j => ((laurentInterpBinom ((laurentRowsTwoBase12 i).1 * W + (laurentRowsTwoBase12 i).2 * K) (j.val % 4) : Nat) : Int) *
        ((2 ^ ((laurentRowsTwoBase12 i).1 * ((j.val / 4) * u)) * 3 ^ ((laurentRowsTwoBase12 i).2 * ((j.val / 4) * u)) : Nat) : Int)) := by
    funext i j
    unfold laurentTwoBaseT4U3Mat12 laurentInterpMat laurentInterpEntry laurentColsT4U3_12
    dsimp only; rw [← Int.natCast_mul]; apply congrArg Int.ofNat; ac_rfl
  have hs3 := stirling_order4_blocks_w19 3
    (fun i => (laurentRowsTwoBase12 i).1 * W + (laurentRowsTwoBase12 i).2 * K)
    (fun i m => ((2 ^ ((laurentRowsTwoBase12 i).1 * (m * u)) * 3 ^ ((laurentRowsTwoBase12 i).2 * (m * u)) : Nat) : Int))
  rw [show ((12 ^ 3 : Nat) : Int) = 1728 by decide] at hs3
  change 1728 * intDet 12 (fun i j =>
      ((laurentInterpBinom ((laurentRowsTwoBase12 i).1 * W + (laurentRowsTwoBase12 i).2 * K) (j.val % 4) : Nat) : Int) *
        ((2 ^ ((laurentRowsTwoBase12 i).1 * ((j.val / 4) * u)) * 3 ^ ((laurentRowsTwoBase12 i).2 * ((j.val / 4) * u)) : Nat) : Int)) =
    intDet 12 (fun i j =>
      intPowNat (((laurentRowsTwoBase12 i).1 * W + (laurentRowsTwoBase12 i).2 * K : Nat) : Int) (j.val % 4) *
        ((2 ^ ((laurentRowsTwoBase12 i).1 * ((j.val / 4) * u)) * 3 ^ ((laurentRowsTwoBase12 i).2 * ((j.val / 4) * u)) : Nat) : Int)) at hs3
  rw [heq_in, hs3]
  exact congrArg (intDet 12) (by funext i j; simp [apow12UW19, Int.natCast_add, Int.natCast_mul])

private def degKW19 (j : Nat) : Nat := if j % 4 < 3 then j % 4 else 2

private def degPrefKW19 : Nat -> Nat
  | 0 => 0
  | c + 1 => degKW19 c + degPrefKW19 c

private theorem apow12_extract_k3_and_homog15_w19 (u : Nat) :
    (∀ w k : Int,
      intDet 12 (apow12UW19 u w k) = intPowNat k 3 * intDet 12 (apow12KDivW19 u w k)) ∧
    (∀ w k g : Int,
      intDet 12 (apow12KDivW19 u (g * w) (g * k)) =
        intPowNat g 15 * intDet 12 (apow12KDivW19 u w k)) := by
  have hgen_cub : ∀ (x w : Int),
      intPowNat x 3 - 3 * w * intPowNat x 2 + 2 * (w * w) * intPowNat x 1 =
        x * ((x - w) * (x - 2 * w)) := by
    intro x w
    simp only [intPowNat, Int.mul_one]
    have hrhs : x * ((x - w) * (x - 2 * w)) =
        x * (x * x) - x * (x * (2 * w)) - x * (w * x) + x * (w * (2 * w)) := by
      simp only [Int.mul_sub, Int.sub_mul]; omega
    rw [hrhs,
        show x * (x * (2 * w)) = 2 * (w * (x * x)) by ac_rfl,
        show x * (w * x) = w * (x * x) by ac_rfl,
        show x * (w * (2 * w)) = 2 * ((w * w) * x) by ac_rfl,
        show 3 * w * (x * x) = 3 * (w * (x * x)) by ac_rfl,
        Int.mul_assoc 2 (w * w) x]
    generalize x * (x * x) = C, w * (x * x) = A, (w * w) * x = B
    omega
  have hcubic_id : ∀ (r : Nat), r < 3 -> ∀ (w y : Int),
      intPowNat ((r : Int) * w + y) 3 -
        3 * w * intPowNat ((r : Int) * w + y) 2 +
        2 * (w * w) * intPowNat ((r : Int) * w + y) 1 =
      y * qCubicW19 r w y := by
    intro r hr w y
    rw [hgen_cub ((r : Int) * w + y) w]
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl
    · simp only [qCubicW19, show ((0 : Nat) : Int) = 0 from rfl, Int.zero_mul, Int.zero_add]
    · simp only [qCubicW19, show ((1 : Nat) : Int) = 1 from rfl, Int.one_mul]
      rw [show w + y - w = y by omega, show w + y - 2 * w = y - w by omega]; ac_rfl
    · simp only [qCubicW19, show ((2 : Nat) : Int) = 2 from rfl]
      rw [show 2 * w + y - w = w + y by omega, show 2 * w + y - 2 * w = y by omega]; ac_rfl
  refine ⟨?_, ?_⟩
  · intro w k
    let blkK (b_done : Nat) (i j : Fin 12) : Int :=
      if j.val / 4 < b_done then apow12KDivW19 u w k i j else apow12UW19 u w k i j
    have hstep : ∀ m : Nat, m < 3 ->
        intDet 12 (blkK m) = k * intDet 12 (blkK (m + 1)) := by
      intro m hm3
      let c1 : Fin 12 := ⟨4 * m + 1, by omega⟩
      let c2 : Fin 12 := ⟨4 * m + 2, by omega⟩
      let c3 : Fin 12 := ⟨4 * m + 3, by omega⟩
      let B0 := blkK m
      let B1 : Fin 12 -> Fin 12 -> Int := fun i j => if j = c3 then B0 i c3 - (3 * w) * B0 i c2 else B0 i j
      let B2 : Fin 12 -> Fin 12 -> Int := fun i j => if j = c3 then B1 i c3 - (-(2 * (w * w))) * B1 i c1 else B1 i j
      have hd1 : intDet 12 B1 = intDet 12 B0 :=
        intDet_sub_col_mul_other 12 c3 c2 (by intro h; have := congrArg Fin.val h; dsimp [c2, c3] at this; omega) (3 * w) B0
      have hd2 : intDet 12 B2 = intDet 12 B1 :=
        intDet_sub_col_mul_other 12 c3 c1 (by intro h; have := congrArg Fin.val h; dsimp [c1, c3] at this; omega) (-(2 * (w * w))) B1
      have hB2_eq : B2 = (fun i j => if j = c3 then k * blkK (m + 1) i c3 else blkK (m + 1) i j) := by
        funext i j
        have hn13 : c1 ≠ c3 := by intro h; have := congrArg Fin.val h; dsimp [c1, c3] at this; omega
        by_cases hj3 : j = c3
        · subst hj3
          rw [ite_true_of_w10 rfl]
          dsimp [B2, B1]
          rw [ite_true_of_w10 rfl, ite_true_of_w10 rfl, ite_false_of_w10 hn13]
          dsimp [B0, blkK, c1, c2, c3]
          simp only [show (4 * m + 3) / 4 = m by omega, show (4 * m + 2) / 4 = m by omega,
                     show (4 * m + 1) / 4 = m by omega, Nat.lt_irrefl, Nat.lt_succ_self, reduceIte]
          unfold apow12UW19 apow12KDivW19 laurentRowsTwoBase12
          dsimp only
          simp only [show (4 * m + 3) / 4 = m by omega, show (4 * m + 2) / 4 = m by omega,
                     show (4 * m + 1) / 4 = m by omega,
                     show (4 * m + 3) % 4 = 3 by omega, show (4 * m + 2) % 4 = 2 by omega,
                     show (4 * m + 1) % 4 = 1 by omega, show ¬ (3 < 3) by decide, reduceIte]
          let r := i.val % 3; let s := i.val / 3
          let E : Int := ((2 ^ (r * (m * u)) * 3 ^ (s * (m * u)) : Nat) : Int)
          have hcub := hcubic_id r (Nat.mod_lt i.val (by decide)) w ((s : Int) * k)
          change intPowNat ((r : Int) * w + (s : Int) * k) 3 * E -
              3 * w * (intPowNat ((r : Int) * w + (s : Int) * k) 2 * E) -
              -(2 * (w * w)) * (intPowNat ((r : Int) * w + (s : Int) * k) 1 * E) =
            k * ((s : Int) * qCubicW19 r w ((s : Int) * k) * E)
          calc intPowNat ((r : Int) * w + (s : Int) * k) 3 * E -
                 3 * w * (intPowNat ((r : Int) * w + (s : Int) * k) 2 * E) -
                 -(2 * (w * w)) * (intPowNat ((r : Int) * w + (s : Int) * k) 1 * E)
              = (intPowNat ((r : Int) * w + (s : Int) * k) 3 -
                 3 * w * intPowNat ((r : Int) * w + (s : Int) * k) 2 +
                 2 * (w * w) * intPowNat ((r : Int) * w + (s : Int) * k) 1) * E := by
                simp only [Int.sub_mul, Int.add_mul, Int.neg_mul]
                rw [Int.sub_neg, Int.mul_assoc (3 * w), Int.mul_assoc (2 * (w * w))]
            _ = (((s : Int) * k) * qCubicW19 r w ((s : Int) * k)) * E := by rw [hcub]
            _ = k * ((s : Int) * qCubicW19 r w ((s : Int) * k) * E) := by ac_rfl
        · rw [ite_false_of_w10 hj3]
          dsimp [B2, B1]; rw [ite_false_of_w10 hj3, ite_false_of_w10 hj3]
          dsimp [B0, blkK]
          by_cases hjm : j.val / 4 = m
          · have hj_lt3 : j.val % 4 < 3 := by
              by_cases h3 : j.val % 4 = 3
              · exfalso; apply hj3; apply Fin.ext; dsimp [c3]; have := Nat.div_add_mod j.val 4; omega
              · have := Nat.mod_lt j.val (by decide : 0 < 4); omega
            rw [hjm, ite_false_of_w10 (Nat.lt_irrefl m), ite_true_of_w10 (Nat.lt_succ_self m)]
            unfold apow12KDivW19 apow12UW19 laurentRowsTwoBase12
            dsimp only; rw [ite_true_of_w10 hj_lt3]
          · by_cases hlt_m : j.val / 4 < m
            · rw [ite_true_of_w10 hlt_m, ite_true_of_w10 (by omega)]
            · rw [ite_false_of_w10 hlt_m, ite_false_of_w10 (by omega)]
      rw [← hd1, ← hd2, hB2_eq]
      exact intDet_col_scale k 12 c3 (blkK (m + 1))
    have hb0 : blkK 0 = apow12UW19 u w k := by funext i j; simp [blkK]
    have hb3 : blkK 3 = apow12KDivW19 u w k := by
      funext i j; dsimp [blkK]; rw [ite_true_of_w10 (by have := j.isLt; omega : j.val / 4 < 3)]
    rw [← hb0, hstep 0 (by decide), hstep 1 (by decide), hstep 2 (by decide), hb3]
    simp only [intPowNat, Int.mul_one]; ac_rfl
  · intro w k g
    let colSc (c_done : Nat) (i j : Fin 12) : Int :=
      if j.val < c_done then intPowNat g (degKW19 j.val) * apow12KDivW19 u w k i j
      else apow12KDivW19 u w k i j
    have hmul_pow : ∀ (a b : Int) (d : Nat), intPowNat (a * b) d = intPowNat a d * intPowNat b d := by
      intro a b d; induction d with
      | zero => simp [intPowNat]
      | succ d' ih => simp only [intPowNat, ih]; ac_rfl
    have hsc_step : ∀ (c : Nat) (hc : c < 12),
        intDet 12 (colSc (c + 1)) = intPowNat g (degKW19 c) * intDet 12 (colSc c) := by
      intro c hc
      let jc : Fin 12 := ⟨c, hc⟩
      have heq_m : colSc (c + 1) = (fun i j =>
          if j = jc then intPowNat g (degKW19 c) * colSc c i jc else colSc c i j) := by
        funext i j
        by_cases hj : j = jc
        · subst hj; dsimp [colSc, jc]
          rw [ite_true_of_w10 (Nat.lt_succ_self c), ite_true_of_w10 rfl, ite_false_of_w10 (Nat.lt_irrefl c)]
        · dsimp [colSc]; rw [ite_false_of_w10 hj]
          have hjv : j.val ≠ c := fun hv => hj (Fin.ext hv)
          by_cases hlt : j.val < c
          · rw [ite_true_of_w10 (by omega), ite_true_of_w10 hlt]
          · rw [ite_false_of_w10 (by omega), ite_false_of_w10 hlt]
      rw [heq_m]; exact intDet_col_scale (intPowNat g (degKW19 c)) 12 jc (colSc c)
    have hind : ∀ n : Nat, n ≤ 12 ->
        intDet 12 (colSc n) = intPowNat g (degPrefKW19 n) * intDet 12 (colSc 0) := by
      intro n; induction n with
      | zero => intro _; simp [degPrefKW19, intPowNat]
      | succ n' ihn =>
        intro hn
        rw [hsc_step n' hn, ihn (Nat.le_of_lt hn), ← Int.mul_assoc, ← intPowNat_add]
        rfl
    have h12 := hind 12 (Nat.le_refl 12)
    have hdeg15 : degPrefKW19 12 = 15 := by decide
    have h0 : colSc 0 = apow12KDivW19 u w k := by funext i j; simp [colSc]
    have h12_eq : colSc 12 = apow12KDivW19 u (g * w) (g * k) := by
      funext i j
      dsimp [colSc]; rw [ite_true_of_w10 j.isLt]
      unfold apow12KDivW19 degKW19
      dsimp only
      let E : Int := ((2 ^ (i.val % 3 * (j.val / 4 * u)) * 3 ^ (i.val / 3 * (j.val / 4 * u)) : Nat) : Int)
      by_cases ht3 : j.val % 4 < 3
      · rw [ite_true_of_w10 ht3, ite_true_of_w10 ht3, ite_true_of_w10 ht3]
        have hlin : ((i.val % 3 : Nat) : Int) * (g * w) + ((i.val / 3 : Nat) : Int) * (g * k) =
            g * (((i.val % 3 : Nat) : Int) * w + ((i.val / 3 : Nat) : Int) * k) := by
          rw [Int.mul_add]; congr 1 <;> ac_rfl
        rw [hlin, hmul_pow, Int.mul_assoc]
      · rw [ite_false_of_w10 ht3, ite_false_of_w10 ht3, ite_false_of_w10 ht3]
        have hq : qCubicW19 (i.val % 3) (g * w) ((i.val / 3 : Int) * (g * k)) =
            intPowNat g 2 * qCubicW19 (i.val % 3) w ((i.val / 3 : Int) * k) := by
          let s : Int := (i.val / 3 : Int)
          change qCubicW19 (i.val % 3) (g * w) (s * (g * k)) = intPowNat g 2 * qCubicW19 (i.val % 3) w (s * k)
          rcases (by have := Nat.mod_lt i.val (by decide : 0 < 3); omega : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2) with h | h | h
          · have h1 : s * (g * k) - g * w = g * (s * k - w) := by rw [Int.mul_sub]; congr 1; ac_rfl
            have h2 : s * (g * k) - 2 * (g * w) = g * (s * k - 2 * w) := by rw [Int.mul_sub]; congr 1 <;> ac_rfl
            rw [h]; dsimp only [qCubicW19, intPowNat]; rw [Int.mul_one, h1, h2]; ac_rfl
          · have h1 : g * w + s * (g * k) = g * (w + s * k) := by rw [Int.mul_add]; congr 1; ac_rfl
            have h2 : s * (g * k) - g * w = g * (s * k - w) := by rw [Int.mul_sub]; congr 1; ac_rfl
            rw [h]; dsimp only [qCubicW19, intPowNat]; rw [Int.mul_one, h1, h2]; ac_rfl
          · have h1 : 2 * (g * w) + s * (g * k) = g * (2 * w + s * k) := by rw [Int.mul_add]; congr 1 <;> ac_rfl
            have h2 : g * w + s * (g * k) = g * (w + s * k) := by rw [Int.mul_add]; congr 1; ac_rfl
            rw [h]; dsimp only [qCubicW19, intPowNat]; rw [Int.mul_one, h1, h2]; ac_rfl
        change intPowNat g 2 * ((i.val / 3 : Int) * qCubicW19 (i.val % 3) w ((i.val / 3 : Int) * k) * E) =
          (i.val / 3 : Int) * qCubicW19 (i.val % 3) (g * w) ((i.val / 3 : Int) * (g * k)) * E
        rw [hq]; ac_rfl
    rw [hdeg15, h0, h12_eq] at h12
    exact h12

private theorem det12_t4u3_homog18_w19 (u g W K : Nat) :
    intDet 12 (laurentTwoBaseT4U3Mat12 (g * W) (g * K) u) =
      intPowNat (g : Int) 18 * intDet 12 (laurentTwoBaseT4U3Mat12 W K u) := by
  have h1 := stirling_1728_det12_t4u3_u_w19 u (g * W) (g * K)
  have h2 := stirling_1728_det12_t4u3_u_w19 u W K
  rcases apow12_extract_k3_and_homog15_w19 u with ⟨hk3, hhom15⟩
  have hm : 1728 * intDet 12 (laurentTwoBaseT4U3Mat12 (g * W) (g * K) u) =
      1728 * (intPowNat (g : Int) 18 * intDet 12 (laurentTwoBaseT4U3Mat12 W K u)) := by
    rw [h1]
    simp only [Int.natCast_mul]
    rw [hk3 ((g : Int) * (W : Int)) ((g : Int) * (K : Int)),
        hhom15 (W : Int) (K : Int) (g : Int)]
    have hrhs_apow : intDet 12 (apow12UW19 u (W : Int) (K : Int)) =
        intPowNat (K : Int) 3 * intDet 12 (apow12KDivW19 u (W : Int) (K : Int)) := hk3 _ _
    have hmul_g3 : intPowNat ((g : Int) * (K : Int)) 3 = intPowNat (g : Int) 3 * intPowNat (K : Int) 3 := by
      simp only [intPowNat, Int.mul_one]; ac_rfl
    have hg18 : intPowNat (g : Int) 3 * intPowNat (g : Int) 15 = intPowNat (g : Int) 18 :=
      (intPowNat_add (g : Int) 3 15).symm
    calc intPowNat ((g : Int) * (K : Int)) 3 * (intPowNat (g : Int) 15 * intDet 12 (apow12KDivW19 u (W : Int) (K : Int)))
        = (intPowNat (g : Int) 3 * intPowNat (g : Int) 15) *
            (intPowNat (K : Int) 3 * intDet 12 (apow12KDivW19 u (W : Int) (K : Int))) := by rw [hmul_g3]; ac_rfl
      _ = intPowNat (g : Int) 18 * (intPowNat (K : Int) 3 * intDet 12 (apow12KDivW19 u (W : Int) (K : Int))) := by rw [hg18]
      _ = intPowNat (g : Int) 18 * (1728 * intDet 12 (laurentTwoBaseT4U3Mat12 W K u)) := by rw [← hrhs_apow, ← h2]
      _ = 1728 * (intPowNat (g : Int) 18 * intDet 12 (laurentTwoBaseT4U3Mat12 W K u)) :=
            Int.mul_left_comm (intPowNat (g : Int) 18) 1728 _
  exact Int.eq_of_mul_eq_mul_left (by decide : (1728 : Int) ≠ 0) hm

-- Shared fast modular utilities (`N = 12` and `N = 16`):
private def powModFuelNatW19 : Nat -> Nat -> Nat -> Nat -> Nat
  | 0, _, _, _ => 1
  | f' + 1, b, e, m =>
    if e = 0 then 1 % m
    else
      let half := powModFuelNatW19 f' b (e / 2) m
      let sq := (half * half) % m
      if e % 2 = 1 then (sq * (b % m)) % m else sq

private def natAt1DW19 : List Nat -> Nat -> Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, k + 1 => natAt1DW19 xs k

private def natRowAtW19 : List (List Nat) -> Nat -> List Nat
  | [], _ => []
  | r :: _, 0 => r
  | _ :: rs, k + 1 => natRowAtW19 rs k

private def natAt2DW19 (rows : List (List Nat)) (r c : Nat) : Nat :=
  natAt1DW19 (natRowAtW19 rows r) c

private def natSubModPW19 (pNat posPart negPart : Nat) : Nat :=
  (posPart % pNat + pNat - negPart % pNat) % pNat

private theorem natSubModPW19_dvd_int (pNat posPart negPart : Nat) (hp : pNat ≥ 1) :
    (pNat : Int) ∣ (((natSubModPW19 pNat posPart negPart : Nat) : Int) -
      ((posPart : Int) - (negPart : Int))) := by
  unfold natSubModPW19
  let ra := posPart % pNat
  let rb := negPart % pNat
  have hrb_lt : rb < pNat := Nat.mod_lt negPart hp
  let S := ra + pNat - rb
  have hS_int : (S : Int) = (ra : Int) + (pNat : Int) - (rb : Int) := by dsimp [S]; omega
  have hda := congrArg (fun n : Nat => (n : Int)) (Nat.div_add_mod posPart pNat)
  have hdb := congrArg (fun n : Nat => (n : Int)) (Nat.div_add_mod negPart pNat)
  have hdS := congrArg (fun n : Nat => (n : Int)) (Nat.div_add_mod S pNat)
  simp only [Int.natCast_add, Int.natCast_mul] at hda hdb hdS
  refine ⟨-((S / pNat : Nat) : Int) + 1 - ((posPart / pNat : Nat) : Int) + ((negPart / pNat : Nat) : Int), ?_⟩
  dsimp [ra, rb, S] at hda hdb hdS hS_int ⊢
  rw [Int.mul_add, Int.mul_sub, Int.mul_add, Int.mul_neg, Int.mul_one]
  omega

private def uStrictNatValW19 (uRows : List (List Nat)) (r c : Nat) : Nat :=
  if Nat.ble (c + 1) r then 0
  else if c == r then 1
  else natAt2DW19 uRows r (c - r - 1)

private def dotPrefixNatW19 (row col : List Nat) : Nat -> Nat
  | 0 => 0
  | n + 1 => dotPrefixNatW19 row col n + natAt1DW19 row n * natAt1DW19 col n

private def dotListsPrefixW19 : Nat -> List Nat -> List Nat -> Nat
  | 0, _, _ => 0
  | n + 1, x :: xs, y :: ys =>
    (if x == 0 || y == 0 then 0 else x * y) + dotListsPrefixW19 n xs ys
  | _, _, _ => 0

private theorem dotListsPrefixW19_eq :
    ∀ (n : Nat) (xs ys : List Nat),
      dotListsPrefixW19 n xs ys = dotPrefixNatW19 xs ys n := by
  have hnil_l : ∀ (m : Nat) (ys : List Nat), dotPrefixNatW19 [] ys m = 0 := by
    intro m ys; induction m with
    | zero => rfl
    | succ m' ih => simp [dotPrefixNatW19, natAt1DW19, ih]
  have hnil_r : ∀ (m : Nat) (xs : List Nat), dotPrefixNatW19 xs [] m = 0 := by
    intro m xs; induction m with
    | zero => rfl
    | succ m' ih => simp [dotPrefixNatW19, natAt1DW19, ih]
  have hcons : ∀ (m x y : Nat) (xs ys : List Nat),
      dotPrefixNatW19 (x :: xs) (y :: ys) (m + 1) = x * y + dotPrefixNatW19 xs ys m := by
    intro m x y xs ys; induction m with
    | zero => simp [dotPrefixNatW19, natAt1DW19]
    | succ m' ih =>
      change dotPrefixNatW19 (x :: xs) (y :: ys) (m' + 1) +
          natAt1DW19 xs m' * natAt1DW19 ys m' =
        x * y + (dotPrefixNatW19 xs ys m' + natAt1DW19 xs m' * natAt1DW19 ys m')
      rw [ih, Nat.add_assoc]
  intro n; induction n with
  | zero => intros; rfl
  | succ n' ih =>
    intro xs ys
    cases xs with
    | nil => simp [dotListsPrefixW19, hnil_l]
    | cons x xtl =>
      cases ys with
      | nil => simp [dotListsPrefixW19, hnil_r]
      | cons y ytl =>
        rw [hcons n' x y xtl ytl]
        unfold dotListsPrefixW19
        rw [ih xtl ytl]
        apply congrArg (· + dotPrefixNatW19 xtl ytl n')
        cases x <;> cases y <;> simp

private def allNatLoop2W19 (p : Nat -> Bool) : Nat -> Bool
  | 0 => true
  | k + 1 => p k && allNatLoop2W19 p k

private theorem allNatLoop2W19_spec (p : Nat -> Bool) :
    ∀ k : Nat, allNatLoop2W19 p k = true -> ∀ x : Nat, x < k -> p x = true
  | 0, _, _, hx => by omega
  | k' + 1, ha, x, hx => by
    unfold allNatLoop2W19 at ha
    rcases bool_and_split ha with ⟨hk, hprev⟩
    by_cases heq : x = k'
    · subst heq; exact hk
    · exact allNatLoop2W19_spec p k' hprev x (by omega)

private theorem allNatLoop2W19_congr (p q : Nat -> Bool) :
    ∀ k : Nat, (∀ x : Nat, x < k -> p x = q x) -> allNatLoop2W19 p k = allNatLoop2W19 q k
  | 0, _ => rfl
  | k' + 1, h => by
    unfold allNatLoop2W19
    rw [h k' (Nat.lt_succ_self k'), allNatLoop2W19_congr p q k' (fun x hx => h x (Nat.lt_succ_of_lt hx))]

private def natDiagProdModPW19 (pNat : Nat) (apRows uCols : List (List Nat)) : Nat -> Nat
  | 0 => 1 % pNat
  | k + 1 =>
    let dk := dotListsPrefixW19 (k + 1) (natRowAtW19 apRows k) (natRowAtW19 uCols k) % pNat
    (natDiagProdModPW19 pNat apRows uCols k * dk) % pNat

private def iterNegModPW19 (pNat : Nat) : Nat -> Nat -> Nat
  | 0, v => v
  | k + 1, v => natSubModPW19 pNat 0 (iterNegModPW19 pNat k v)

private theorem iterNegModPW19_neg (pNat : Nat) :
    ∀ (cnt v : Nat),
      iterNegModPW19 pNat cnt (natSubModPW19 pNat 0 v) = iterNegModPW19 pNat (cnt + 1) v
  | 0, _ => rfl
  | cnt' + 1, v => congrArg (natSubModPW19 pNat 0) (iterNegModPW19_neg pNat cnt' v)

private def traceColSwapsNW19 (N : Nat) : List (Nat × Nat) -> Nat -> Nat × Nat
  | [], j => (j, 0)
  | (c1, c2) :: rest, j =>
    match traceColSwapsNW19 N rest j with
    | (j', cnt) =>
      if Nat.ble (c1 + 1) N && Nat.ble (c2 + 1) N && (c1 != c2) then
        if j' == c1 then (c2, cnt)
        else if j' == c2 then (c1, cnt + 1)
        else (j', cnt)
      else (j', cnt)

private def dotDirectW19 (f g : Nat -> Nat) : Nat -> Nat
  | 0 => 0
  | n + 1 =>
    dotDirectW19 f g n +
      (let x := f n
       if x == 0 then 0 else x * g n)

private def natDiagDirectModPW19 (pNat : Nat) (apFn uFn : Nat -> Nat -> Nat) : Nat -> Nat
  | 0 => 1 % pNat
  | k + 1 =>
    let dk := dotDirectW19 (apFn k) (fun n => uFn n k) (k + 1) % pNat
    (natDiagDirectModPW19 pNat apFn uFn k * dk) % pNat

private def checkAllInvModPBoolW19 (pNat : Nat) : Nat -> Bool
  | 0 => true
  | x + 1 =>
    (if x == 0 then true else ((x * powModFuelNatW19 8 x (pNat - 2) pNat) % pNat == 1)) &&
      checkAllInvModPBoolW19 pNat x

private def dropCertsW19 : Nat -> List (List (Nat × Nat) × List (List Nat)) ->
    List (List (Nat × Nat) × List (List Nat))
  | 0, cs => cs
  | _ + 1, [] => []
  | k + 1, _ :: cs => dropCertsW19 k cs

private def decodeSwapsW19 : Nat -> Nat -> List (Nat × Nat)
  | 0, _ => []
  | fuel + 1, pk =>
    let b := pk % 65536
    if b == 0 then []
    else decodeSwapsW19 fuel (pk / 65536) ++ [((b % 32) - 1, (b / 32) - 1)]

private def decodeUSeqRowW19 : Nat -> Nat -> List Nat × Nat
  | 0, cur => ([], cur)
  | k + 1, cur =>
    let (rest, nxt) := decodeUSeqRowW19 k (cur / 256)
    (cur % 256 :: rest, nxt)

private def decodeUSeqRowsW19 : List Nat -> Nat -> List (List Nat)
  | [], _ => []
  | len :: ls, cur =>
    let (row, nxt) := decodeUSeqRowW19 len cur
    row :: decodeUSeqRowsW19 ls nxt

private def decodeUCert12W19 (pk : Nat × Nat) : List (Nat × Nat) × List (List Nat) :=
  (decodeSwapsW19 20 pk.1, decodeUSeqRowsW19 [11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1] pk.2)

private def decodeUCert16W19 (pk : Nat × Nat) : List (Nat × Nat) × List (List Nat) :=
  (decodeSwapsW19 24 pk.1, decodeUSeqRowsW19 [15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1] pk.2)

-- `N = 12` Mod-`p` UL Engine:
private def buildRow12NatW19 (f : Nat -> Nat) : List Nat :=
  [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11]

private def buildMat12NatW19 (f : Nat -> Nat -> Nat) : List (List Nat) :=
  [buildRow12NatW19 (f 0), buildRow12NatW19 (f 1), buildRow12NatW19 (f 2), buildRow12NatW19 (f 3),
   buildRow12NatW19 (f 4), buildRow12NatW19 (f 5), buildRow12NatW19 (f 6), buildRow12NatW19 (f 7),
   buildRow12NatW19 (f 8), buildRow12NatW19 (f 9), buildRow12NatW19 (f 10), buildRow12NatW19 (f 11)]

private theorem natAt1DW19_buildRow12 (f : Nat -> Nat) (k : Nat) (hk : k < 12) :
    natAt1DW19 (buildRow12NatW19 f) k = f k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
      k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem natRowAtW19_buildMat12 (f : Nat -> Nat -> Nat) (r : Nat) (hr : r < 12) :
    natRowAtW19 (buildMat12NatW19 f) r = buildRow12NatW19 (fun c => f r c) := by
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨
      r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem natAt2DW19_buildMat12 (f : Nat -> Nat -> Nat) (r c : Nat) (hr : r < 12) (hc : c < 12) :
    natAt2DW19 (buildMat12NatW19 f) r c = f r c := by
  unfold natAt2DW19; rw [natRowAtW19_buildMat12 f r hr, natAt1DW19_buildRow12 _ c hc]

private def swapOneMat12NatW19 (pNat c1 c2 : Nat) (M : List (List Nat)) : List (List Nat) :=
  if Nat.ble (c1 + 1) 12 && Nat.ble (c2 + 1) 12 && (c1 != c2) then
    buildMat12NatW19 (fun r j =>
      if j == c1 then natAt2DW19 M r c2
      else if j == c2 then natSubModPW19 pNat 0 (natAt2DW19 M r c1)
      else natAt2DW19 M r j)
  else M

private def applySignedSwapsMat12NatW19 (pNat : Nat) :
    List (Nat × Nat) -> List (List Nat) -> List (List Nat)
  | [], M => M
  | (c1, c2) :: rest, M =>
    applySignedSwapsMat12NatW19 pNat rest (swapOneMat12NatW19 pNat c1 c2 M)

private def checkRawMatULModP12BoolW19 (pNat : Nat) (a0 : List (List Nat))
    (cert : List (Nat × Nat) × List (List Nat)) : Bool :=
  let apRows := applySignedSwapsMat12NatW19 pNat cert.1 a0
  let uCols := buildMat12NatW19 (fun c r => uStrictNatValW19 cert.2 r c)
  allNatLoop2W19 (fun r =>
    let row_r := natRowAtW19 apRows r
    allNatLoop2W19 (fun c =>
      if Nat.ble (r + 1) c then
        dotListsPrefixW19 (c + 1) row_r (natRowAtW19 uCols c) % pNat == 0
      else true) 12) 12 &&
  (natDiagProdModPW19 pNat apRows uCols 12 != 0)

private theorem checkRawMatULModP12BoolW19_sound (pNat : Nat) (hp : pNat ≥ 2)
    (a0 : List (List Nat)) (cert : List (Nat × Nat) × List (List Nat))
    (h : checkRawMatULModP12BoolW19 pNat a0 cert = true) :
    intDet 12 (fun i j => (natAt2DW19 a0 i.val j.val : Int)) % (pNat : Int) ≠ 0 := by
  let p : Int := (pNat : Int)
  have hp1 : pNat ≥ 1 := by omega
  let matOf (T : List (List Nat)) (i j : Fin 12) : Int := (natAt2DW19 T i.val j.val : Int)
  have hd_trans : ∀ a b c : Int, p ∣ (a - b) -> p ∣ (b - c) -> p ∣ (a - c) := by
    intro a b c ⟨q1, h1⟩ ⟨q2, h2⟩; exact ⟨q1 + q2, by rw [Int.mul_add]; omega⟩
  have hd_sub_r : ∀ a b : Nat, p ∣ (((a : Int) - (b : Int)) - (natSubModPW19 pNat a b : Int)) := by
    intro a b
    rcases natSubModPW19_dvd_int pNat a b hp1 with ⟨q, hq⟩
    exact ⟨-q, by dsimp [p]; rw [Int.mul_neg]; omega⟩
  let apRows := applySignedSwapsMat12NatW19 pNat cert.1 a0
  let uCols := buildMat12NatW19 (fun c r => uStrictNatValW19 cert.2 r c)
  have hd_swaps : ∀ (swaps : List (Nat × Nat)) (M : List (List Nat)),
      p ∣ (intDet 12 (matOf M) - intDet 12 (matOf (applySignedSwapsMat12NatW19 pNat swaps M))) := by
    intro swaps; induction swaps with
    | nil => intro M; exact ⟨0, by simp [applySignedSwapsMat12NatW19]⟩
    | cons sw rest ih =>
      rcases sw with ⟨c1, c2⟩
      intro M
      unfold applySignedSwapsMat12NatW19
      let M' := swapOneMat12NatW19 pNat c1 c2 M
      have hd_one : p ∣ (intDet 12 (matOf M) - intDet 12 (matOf M')) := by
        dsimp only [M']; unfold swapOneMat12NatW19
        by_cases hc : c1 < 12 ∧ c2 < 12 ∧ c1 ≠ c2
        · have hcond : (Nat.ble (c1 + 1) 12 && Nat.ble (c2 + 1) 12 && (c1 != c2)) = true := by
            rw [Nat.ble_eq.mpr hc.1, Nat.ble_eq.mpr hc.2.1, bne_iff_ne.mpr hc.2.2]; rfl
          change p ∣ (intDet 12 (matOf M) - intDet 12 (matOf
            (if (Nat.ble (c1 + 1) 12 && Nat.ble (c2 + 1) 12 && (c1 != c2)) = true then
              buildMat12NatW19 (fun r j =>
                if j == c1 then natAt2DW19 M r c2
                else if j == c2 then natSubModPW19 pNat 0 (natAt2DW19 M r c1)
                else natAt2DW19 M r j)
            else M)))
          rw [ite_true_of_w10 hcond]
          let fc1 : Fin 12 := ⟨c1, hc.1⟩
          let fc2 : Fin 12 := ⟨c2, hc.2.1⟩
          let S_int (i j : Fin 12) : Int :=
            if j = fc1 then matOf M i fc2 else if j = fc2 then -(matOf M i fc1) else matOf M i j
          rw [← signedColSwap_det_w19 12 fc1 fc2 (fun h => hc.2.2 (congrArg Fin.val h)) (matOf M)]
          apply intDet_congr_dvd p 12 S_int
          intro i j
          dsimp only [S_int, matOf]
          rw [natAt2DW19_buildMat12 _ i.val j.val i.isLt j.isLt]
          by_cases hj1 : j = fc1
          · subst hj1
            dsimp only [fc1, fc2]
            have hb1 : (c1 == c1) = true := beq_iff_eq.mpr rfl
            simp only [hb1, ↓reduceIte, Int.sub_self]
            exact ⟨0, (Int.mul_zero p).symm⟩
          · have hne1 : j.val ≠ c1 := fun hv => hj1 (Fin.ext hv)
            have hb1f : (j.val == c1) = false := beq_false_of_ne hne1
            by_cases hj2 : j = fc2
            · subst hj2
              have hb2 : (fc2.val == c2) = true := beq_iff_eq.mpr rfl
              simp only [hj1, hb1f, hb2, Bool.false_eq_true, ↓reduceIte]
              simpa using hd_sub_r 0 (natAt2DW19 M i.val c1)
            · have hne2 : j.val ≠ c2 := fun hv => hj2 (Fin.ext hv)
              have hb2f : (j.val == c2) = false := beq_false_of_ne hne2
              simp only [hj1, hj2, hb1f, hb2f, Bool.false_eq_true, ↓reduceIte, Int.sub_self]
              exact ⟨0, (Int.mul_zero p).symm⟩
        · have hcond : ¬ ((Nat.ble (c1 + 1) 12 && Nat.ble (c2 + 1) 12 && (c1 != c2)) = true) := by
            intro htrue
            rcases bool_and_split htrue with ⟨h12, h3⟩
            rcases bool_and_split h12 with ⟨h1, h2⟩
            exact hc ⟨Nat.ble_eq.mp h1, Nat.ble_eq.mp h2, bne_iff_ne.mp h3⟩
          change p ∣ (intDet 12 (matOf M) - intDet 12 (matOf
            (if (Nat.ble (c1 + 1) 12 && Nat.ble (c2 + 1) 12 && (c1 != c2)) = true then _ else M)))
          rw [ite_false_of_w10 hcond]; exact ⟨0, by simp⟩
      exact hd_trans _ _ _ hd_one (ih M')
  let Ap := matOf apRows
  let U (r c : Fin 12) : Int := (uStrictNatValW19 cert.2 r.val c.val : Int)
  let prodFull (r c : Fin 12) : Int := intSumPrefix 12 (fun k_f => Ap r k_f * U k_f c) 12
  let prodTrunc (r c : Fin 12) : Int := intSumPrefix 12 (fun k_f => Ap r k_f * U k_f c) (c.val + 1)
  unfold checkRawMatULModP12BoolW19 at h
  rcases bool_and_split h with ⟨hsup_b, hdiag_nz_b⟩
  have hdiag_nz := bne_iff_ne.mp hdiag_nz_b
  have hupper : ∀ r c : Fin 12, c.val < r.val -> U r c = 0 := by
    intro r c hlt; dsimp [U, uStrictNatValW19]; rw [ite_true_of_w10 (Nat.ble_eq.mpr hlt)]; rfl
  have hu_diag1 : intDiagProdPrefixW19 12 U 12 = 1 := by
    have hst : ∀ m : Nat, m ≤ 12 -> intDiagProdPrefixW19 12 U m = 1 := by
      intro m hm; induction m with
      | zero => rfl
      | succ m' ih =>
        have hm_lt : m' < 12 := hm
        simp only [intDiagProdPrefixW19, hm_lt, dite_true, ih (Nat.le_of_lt hm), Int.one_mul]
        dsimp [U, uStrictNatValW19]
        have hnlt : ¬ (Nat.ble (m' + 1) m' = true) := fun hb => Nat.lt_irrefl m' (Nat.ble_eq.mp hb)
        rw [ite_false_of_w10 hnlt, ite_true_of_w10 (beq_iff_eq.mpr rfl)]; rfl
    exact hst 12 (Nat.le_refl 12)
  have htrunc_eq : prodFull = prodTrunc := by
    funext r c; dsimp [prodFull, prodTrunc]
    have hst : ∀ d : Nat, c.val + 1 + d ≤ 12 ->
        intSumPrefix 12 (fun k_f => Ap r k_f * U k_f c) (c.val + 1 + d) =
          intSumPrefix 12 (fun k_f => Ap r k_f * U k_f c) (c.val + 1) := by
      intro d hd; induction d with
      | zero => rfl
      | succ d' ih =>
        rw [Nat.add_succ]
        have hlt : c.val + 1 + d' < 12 := hd
        conv => lhs; unfold intSumPrefix
        simp only [hlt, dite_true]
        rw [ih (by omega), hupper ⟨c.val + 1 + d', hlt⟩ c (by dsimp; omega), Int.mul_zero, Int.add_zero]
    have h12 := hst (12 - (c.val + 1)) (by have := c.isLt; omega)
    rwa [show c.val + 1 + (12 - (c.val + 1)) = 12 by have := c.isLt; omega] at h12
  have hdet_prod : intDet 12 prodTrunc = intDet 12 Ap := by
    rw [← htrunc_eq]
    have hm := intDet_mul_upper_tri_w19 12 Ap U hupper
    dsimp only [prodFull]; rw [hm, hu_diag1, Int.one_mul]
  have hdot_eq : ∀ (r c : Fin 12) (n : Nat), n ≤ 12 ->
      ((dotPrefixNatW19 (natRowAtW19 apRows r.val) (natRowAtW19 uCols c.val) n : Nat) : Int) =
        intSumPrefix 12 (fun k_f => Ap r k_f * U k_f c) n := by
    intro r c n hn; induction n with
    | zero => rfl
    | succ n' ih =>
      have hn_lt : n' < 12 := hn
      simp only [dotPrefixNatW19, intSumPrefix, hn_lt, dite_true,
                 Int.natCast_add, Int.natCast_mul, ih (Nat.le_of_lt hn)]
      have hu_at : natAt1DW19 (natRowAtW19 uCols c.val) n' = uStrictNatValW19 cert.2 n' c.val := by
        dsimp only [uCols]
        rw [natRowAtW19_buildMat12 _ c.val c.isLt, natAt1DW19_buildRow12 _ n' hn_lt]
      rw [hu_at]; rfl
  let prodLow (r c : Fin 12) : Int := if r.val < c.val then 0 else prodTrunc r c
  have hd_low : p ∣ (intDet 12 prodTrunc - intDet 12 prodLow) := by
    apply intDet_congr_dvd p 12 prodTrunc prodLow
    intro r c; dsimp [prodLow]
    by_cases hrc : r.val < c.val
    · rw [ite_true_of_w10 hrc, Int.sub_zero]
      have hr_b := allNatLoop2W19_spec _ 12 hsup_b r.val r.isLt
      have hc_b := allNatLoop2W19_spec _ 12 hr_b c.val c.isLt
      rw [Nat.ble_eq.mpr hrc, dotListsPrefixW19_eq] at hc_b
      have hm_nat := beq_iff_eq.mp hc_b
      have hm_int : prodTrunc r c % p = 0 := by
        dsimp only [prodTrunc, p]
        rw [← hdot_eq r c (c.val + 1) (by have := c.isLt; omega)]
        exact (Int.natCast_emod _ pNat).symm.trans (by rw [hm_nat]; rfl)
      exact Int.dvd_of_emod_eq_zero hm_int
    · rw [ite_false_of_w10 hrc, Int.sub_self]; exact ⟨0, by simp⟩
  have hdet_low : intDet 12 prodLow = intDiagProdPrefixW19 12 prodTrunc 12 := by
    rw [intDet_lower_tri_w19 12 prodLow (fun r c hrc => by dsimp [prodLow]; rw [ite_true_of_w10 hrc])]
    have hst : ∀ m : Nat, m ≤ 12 -> intDiagProdPrefixW19 12 prodLow m = intDiagProdPrefixW19 12 prodTrunc m := by
      intro m hm; induction m with
      | zero => rfl
      | succ m' ih =>
        have hm_lt : m' < 12 := hm
        simp only [intDiagProdPrefixW19, hm_lt, dite_true, ih (Nat.le_of_lt hm)]
        dsimp [prodLow]; rw [ite_false_of_w10 (Nat.lt_irrefl m')]
    exact hst 12 (Nat.le_refl 12)
  have hdiag_eq : ∀ m : Nat, m ≤ 12 ->
      ((natDiagProdModPW19 pNat apRows uCols m : Nat) : Int) =
        intDiagProdPrefixW19 12 prodTrunc m % p := by
    intro m hm; induction m with
    | zero => exact Int.natCast_emod 1 pNat
    | succ m' ih =>
      have hm_lt : m' < 12 := hm
      let fm : Fin 12 := ⟨m', hm_lt⟩
      simp only [natDiagProdModPW19, dotListsPrefixW19_eq]
      rw [Int.natCast_emod, Int.natCast_mul, Int.natCast_emod,
          ih (Nat.le_of_lt hm), hdot_eq fm fm (m' + 1) hm]
      simp only [intDiagProdPrefixW19, hm_lt, dite_true]
      exact (Int.mul_emod _ _ p).symm
  have hd_ap_diag : p ∣ (intDet 12 Ap - intDiagProdPrefixW19 12 prodTrunc 12) := by
    rw [← hdet_prod, ← hdet_low]; exact hd_low
  have hd_tot := hd_trans _ _ _ (hd_swaps cert.1 a0) hd_ap_diag
  rcases hd_tot with ⟨qt, hqt⟩
  intro hz_mod
  have hdiag_mod0 : intDiagProdPrefixW19 12 prodTrunc 12 % p = 0 := by
    have heq : intDiagProdPrefixW19 12 prodTrunc 12 =
        intDet 12 (matOf a0) + p * (-qt) := by
      rw [Int.mul_neg]; omega
    rw [heq, Int.add_emod, hz_mod, Int.zero_add, Int.mul_emod_right, Int.zero_emod]
  have hnat0_int : ((natDiagProdModPW19 pNat apRows uCols 12 : Nat) : Int) = ((0 : Nat) : Int) := by
    rw [hdiag_eq 12 (Nat.le_refl 12), hdiag_mod0]; rfl
  exact hdiag_nz (Int.ofNat.inj hnat0_int)

private def fastApow12KDivNatW19 (u w k : Nat) (i j : Fin 12) : Int :=
  let r := i.val % 3; let s := i.val / 3
  let t := j.val % 4; let m := j.val / 4
  let E : Int := ((2 ^ (r * (m * u)) * 3 ^ (s * (m * u)) : Nat) : Int)
  if t < 3 then (((r * w + s * k) ^ t : Nat) : Int) * E
  else (s : Int) * qCubicW19 r (w : Int) ((s * k : Nat) : Int) * E

private theorem fastApow12KDivNatW19_eq (u w k : Nat) :
    fastApow12KDivNatW19 u w k = apow12KDivW19 u (w : Int) (k : Int) := by
  funext i j
  unfold fastApow12KDivNatW19 apow12KDivW19
  dsimp only
  by_cases ht3 : j.val % 4 < 3
  · rw [ite_true_of_w10 ht3, ite_true_of_w10 ht3, ← intPowNat_natCast_w19]
    simp only [Int.natCast_add, Int.natCast_mul]
  · rw [ite_false_of_w10 ht3, ite_false_of_w10 ht3]
    simp only [Int.natCast_mul]

private def fastApow12DirectModPW19 (pNat u w k rCol cCol : Nat) : Nat :=
  let r := rCol % 3; let s := rCol / 3
  let t := cCol % 4; let m := cCol / 4
  let E := ((2 ^ (r * (m * u))) % pNat * ((3 ^ (s * (m * u))) % pNat)) % pNat
  let sk := s * k
  let poly :=
    if Nat.ble (t + 1) 3 then ((r * w + sk) ^ t) % pNat
    else
      let qc :=
        match r with
        | 0 => (natSubModPW19 pNat sk w * natSubModPW19 pNat sk (2 * w)) % pNat
        | 1 => (((w + sk) % pNat) * natSubModPW19 pNat sk w) % pNat
        | _ => (((2 * w + sk) % pNat) * ((w + sk) % pNat)) % pNat
      (s * qc) % pNat
  (poly * E) % pNat

private def checkULModPNat12BoolW19 (pNat u w k : Nat)
    (cert : List (Nat × Nat) × List (List Nat)) : Bool :=
  checkRawMatULModP12BoolW19 pNat (buildMat12NatW19 (fastApow12DirectModPW19 pNat u w k)) cert

private theorem checkULModPNat12BoolW19_sound (pNat u w k : Nat) (hp : pNat ≥ 2)
    (cert : List (Nat × Nat) × List (List Nat))
    (h : checkULModPNat12BoolW19 pNat u w k cert = true) :
    intDet 12 (apow12KDivW19 u (w : Int) (k : Int)) % (pNat : Int) ≠ 0 := by
  let p : Int := (pNat : Int)
  have hp1 : pNat ≥ 1 := by omega
  let a0 := buildMat12NatW19 (fastApow12DirectModPW19 pNat u w k)
  let matOf (T : List (List Nat)) (i j : Fin 12) : Int := (natAt2DW19 T i.val j.val : Int)
  have hd_trans : ∀ a b c : Int, p ∣ (a - b) -> p ∣ (b - c) -> p ∣ (a - c) := by
    intro a b c ⟨q1, h1⟩ ⟨q2, h2⟩; exact ⟨q1 + q2, by rw [Int.mul_add]; omega⟩
  have hd_mul : ∀ a1 a2 b1 b2 : Int, p ∣ (a1 - a2) -> p ∣ (b1 - b2) -> p ∣ (a1 * b1 - a2 * b2) := by
    intro a1 a2 b1 b2 ⟨q1, h1⟩ ⟨q2, h2⟩
    refine ⟨q1 * b1 + a2 * q2, ?_⟩
    have : a1 * b1 - a2 * b2 = (a1 - a2) * b1 + a2 * (b1 - b2) := by
      simp only [Int.sub_mul, Int.mul_sub]; omega
    rw [this, h1, h2, Int.mul_add, Int.mul_assoc p q1 b1,
        ← Int.mul_assoc a2 p q2, Int.mul_comm a2 p, Int.mul_assoc p a2 q2]
  have hd_mod_r : ∀ n : Nat, p ∣ ((n : Int) - ((n % pNat : Nat) : Int)) := by
    intro n
    rcases int_mod_sub_dvd_w19 n pNat with ⟨q, hq⟩
    exact ⟨-q, by dsimp [p]; rw [Int.mul_neg]; omega⟩
  have hd_sub_r : ∀ a b : Nat, p ∣ (((a : Int) - (b : Int)) - (natSubModPW19 pNat a b : Int)) := by
    intro a b
    rcases natSubModPW19_dvd_int pNat a b hp1 with ⟨q, hq⟩
    exact ⟨-q, by dsimp [p]; rw [Int.mul_neg]; omega⟩
  have hd_A0 : p ∣ (intDet 12 (apow12KDivW19 u (w : Int) (k : Int)) - intDet 12 (matOf a0)) := by
    rw [← fastApow12KDivNatW19_eq u w k]
    apply intDet_congr_dvd p 12
    intro i j
    dsimp only [matOf, a0]
    rw [natAt2DW19_buildMat12 _ i.val j.val i.isLt j.isLt]
    unfold fastApow12KDivNatW19 fastApow12DirectModPW19
    dsimp only
    let r := i.val % 3; let s := i.val / 3
    let t := j.val % 4; let m := j.val / 4
    let E_int : Int := ((2 ^ (r * (m * u)) * 3 ^ (s * (m * u)) : Nat) : Int)
    let E_nat : Nat := ((2 ^ (r * (m * u))) % pNat * ((3 ^ (s * (m * u))) % pNat)) % pNat
    have hd_E : p ∣ (E_int - (E_nat : Int)) := by
      have hm_e : E_int = ((2 ^ (r * (m * u)) : Nat) : Int) * ((3 ^ (s * (m * u)) : Nat) : Int) :=
        Int.natCast_mul _ _
      rw [hm_e]
      exact hd_trans _ (((2 ^ (r * (m * u))) % pNat * ((3 ^ (s * (m * u))) % pNat) : Nat) : Int) _
        (by rw [Int.natCast_mul]; exact hd_mul _ _ _ _ (hd_mod_r _) (hd_mod_r _))
        (hd_mod_r _)
    by_cases ht3 : j.val % 4 < 3
    · have ht_ble : Nat.ble (j.val % 4 + 1) 3 = true := Nat.ble_eq.mpr ht3
      rw [ite_true_of_w10 ht3, ite_true_of_w10 ht_ble]
      exact hd_trans _ (((((r * w + s * k) ^ t) % pNat * E_nat : Nat) : Int)) _
        (by rw [Int.natCast_mul]; exact hd_mul _ _ _ _ (hd_mod_r _) hd_E)
        (hd_mod_r _)
    · have ht_nble : ¬ (Nat.ble (j.val % 4 + 1) 3 = true) := fun hb => ht3 (Nat.ble_eq.mp hb)
      rw [ite_false_of_w10 ht3, ite_false_of_w10 ht_nble]
      let sk := s * k
      let qc_nat : Nat :=
        match r with
        | 0 => (natSubModPW19 pNat sk w * natSubModPW19 pNat sk (2 * w)) % pNat
        | 1 => (((w + sk) % pNat) * natSubModPW19 pNat sk w) % pNat
        | _ => (((2 * w + sk) % pNat) * ((w + sk) % pNat)) % pNat
      have hd_qc : p ∣ (qCubicW19 r (w : Int) (sk : Int) - (qc_nat : Int)) := by
        dsimp only [qc_nat]
        rcases (by have := Nat.mod_lt i.val (by decide : 0 < 3); omega : r = 0 ∨ r = 1 ∨ r = 2) with hr | hr | hr
        · rw [hr]; dsimp only [qCubicW19]
          rw [show (2 : Int) * (w : Int) = ((2 * w : Nat) : Int) by simp [Int.natCast_mul]]
          exact hd_trans _ ((natSubModPW19 pNat sk w * natSubModPW19 pNat sk (2 * w) : Nat) : Int) _
            (by rw [Int.natCast_mul]; exact hd_mul _ _ _ _ (hd_sub_r sk w) (hd_sub_r sk (2 * w)))
            (hd_mod_r _)
        · rw [hr]; dsimp only [qCubicW19]
          rw [show (w : Int) + (sk : Int) = ((w + sk : Nat) : Int) by simp [Int.natCast_add]]
          exact hd_trans _ ((((w + sk) % pNat * natSubModPW19 pNat sk w : Nat) : Int)) _
            (by rw [Int.natCast_mul]; exact hd_mul _ _ _ _ (hd_mod_r (w + sk)) (hd_sub_r sk w))
            (hd_mod_r _)
        · rw [hr]; dsimp only [qCubicW19]
          rw [show (2 : Int) * (w : Int) + (sk : Int) = ((2 * w + sk : Nat) : Int) by simp [Int.natCast_add, Int.natCast_mul],
              show (w : Int) + (sk : Int) = ((w + sk : Nat) : Int) by simp [Int.natCast_add]]
          exact hd_trans _ ((((2 * w + sk) % pNat * ((w + sk) % pNat) : Nat) : Int)) _
            (by rw [Int.natCast_mul]; exact hd_mul _ _ _ _ (hd_mod_r _) (hd_mod_r _))
            (hd_mod_r _)
      let poly_nat : Nat := (s * qc_nat) % pNat
      have hd_sqc : p ∣ ((s : Int) * qCubicW19 r (w : Int) (sk : Int) - (poly_nat : Int)) :=
        hd_trans _ (((s * qc_nat : Nat) : Int)) _
          (by rw [Int.natCast_mul]; exact hd_mul (s : Int) (s : Int) _ _ ⟨0, by simp⟩ hd_qc)
          (hd_mod_r (s * qc_nat))
      change p ∣ ((s : Int) * qCubicW19 r (w : Int) (sk : Int) * E_int - (((poly_nat * E_nat) % pNat : Nat) : Int))
      exact hd_trans _ (((poly_nat * E_nat : Nat) : Int)) _
        (by rw [Int.natCast_mul]; exact hd_mul _ _ _ _ hd_sqc hd_E)
        (hd_mod_r (poly_nat * E_nat))
  have hraw_nz : intDet 12 (matOf a0) % p ≠ 0 :=
    checkRawMatULModP12BoolW19_sound pNat hp a0 cert h
  rcases hd_A0 with ⟨qt, hqt⟩
  intro hz_mod
  have hmat0 : intDet 12 (matOf a0) % p = 0 := by
    have heq : intDet 12 (matOf a0) =
        intDet 12 (apow12KDivW19 u (w : Int) (k : Int)) + p * (-qt) := by
      rw [Int.mul_neg]; omega
    rw [heq, Int.add_emod, hz_mod, Int.zero_add, Int.mul_emod_right, Int.zero_emod]
  exact hraw_nz hmat0

private theorem traceColSwaps12_spec_w19 (pNat : Nat) :
    ∀ (swaps : List (Nat × Nat)) (M : List (List Nat)) (r j : Nat),
      r < 12 -> j < 12 ->
      (traceColSwapsNW19 12 swaps j).1 < 12 ∧
      natAt2DW19 (applySignedSwapsMat12NatW19 pNat swaps M) r j =
        iterNegModPW19 pNat (traceColSwapsNW19 12 swaps j).2
          (natAt2DW19 M r (traceColSwapsNW19 12 swaps j).1)
  | [], _, _, _, _, hj => ⟨hj, rfl⟩
  | (c1, c2) :: rest, M, r, j, hr, hj => by
    unfold applySignedSwapsMat12NatW19 traceColSwapsNW19
    rcases htr : traceColSwapsNW19 12 rest j with ⟨j', cnt⟩
    dsimp only
    cases hcond : (Nat.ble (c1 + 1) 12 && Nat.ble (c2 + 1) 12 && (c1 != c2))
    · have hsw : swapOneMat12NatW19 pNat c1 c2 M = M := by
        unfold swapOneMat12NatW19; rw [hcond]; rfl
      rw [hsw]; simp only [Bool.false_eq_true, ↓reduceIte]
      rcases traceColSwaps12_spec_w19 pNat rest M r j hr hj with ⟨hj', ih_eq⟩
      rw [htr] at hj' ih_eq; exact ⟨hj', ih_eq⟩
    · simp only [↓reduceIte]
      let M' := swapOneMat12NatW19 pNat c1 c2 M
      rcases traceColSwaps12_spec_w19 pNat rest M' r j hr hj with ⟨hj', ih_eq⟩
      rw [htr] at hj' ih_eq; dsimp only at hj' ih_eq
      rcases bool_and_split hcond with ⟨hc12, _⟩
      rcases bool_and_split hc12 with ⟨hc1_b, hc2_b⟩
      have hc1 : c1 < 12 := Nat.ble_eq.mp hc1_b
      have hc2 : c2 < 12 := Nat.ble_eq.mp hc2_b
      have hM'_at : natAt2DW19 M' r j' =
          if j' == c1 then natAt2DW19 M r c2
          else if j' == c2 then natSubModPW19 pNat 0 (natAt2DW19 M r c1)
          else natAt2DW19 M r j' := by
        unfold M' swapOneMat12NatW19; rw [hcond]; simp only [↓reduceIte]
        exact natAt2DW19_buildMat12 _ r j' hr hj'
      rw [hM'_at] at ih_eq
      cases he1 : (j' == c1)
      · cases he2 : (j' == c2)
        · simp only [he1, he2, Bool.false_eq_true, ↓reduceIte] at ih_eq ⊢; exact ⟨hj', ih_eq⟩
        · simp only [he1, he2, Bool.false_eq_true, ↓reduceIte] at ih_eq ⊢
          rw [iterNegModPW19_neg] at ih_eq; exact ⟨hc1, ih_eq⟩
      · simp only [he1, ↓reduceIte] at ih_eq ⊢; exact ⟨hc2, ih_eq⟩

private theorem buildRow12NatW19_congr (f g : Nat -> Nat) (h : ∀ j : Nat, j < 12 -> f j = g j) :
    buildRow12NatW19 f = buildRow12NatW19 g := by
  unfold buildRow12NatW19
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide),
      h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide),
      h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide)]

private theorem buildMat12NatW19_congr (f g : Nat -> Nat -> Nat)
    (h : ∀ r j : Nat, r < 12 -> j < 12 -> f r j = g r j) :
    buildMat12NatW19 f = buildMat12NatW19 g := by
  unfold buildMat12NatW19
  rw [buildRow12NatW19_congr _ _ (fun j hj => h 0 j (by decide) hj),
      buildRow12NatW19_congr _ _ (fun j hj => h 1 j (by decide) hj),
      buildRow12NatW19_congr _ _ (fun j hj => h 2 j (by decide) hj),
      buildRow12NatW19_congr _ _ (fun j hj => h 3 j (by decide) hj),
      buildRow12NatW19_congr _ _ (fun j hj => h 4 j (by decide) hj),
      buildRow12NatW19_congr _ _ (fun j hj => h 5 j (by decide) hj),
      buildRow12NatW19_congr _ _ (fun j hj => h 6 j (by decide) hj),
      buildRow12NatW19_congr _ _ (fun j hj => h 7 j (by decide) hj),
      buildRow12NatW19_congr _ _ (fun j hj => h 8 j (by decide) hj),
      buildRow12NatW19_congr _ _ (fun j hj => h 9 j (by decide) hj),
      buildRow12NatW19_congr _ _ (fun j hj => h 10 j (by decide) hj),
      buildRow12NatW19_congr _ _ (fun j hj => h 11 j (by decide) hj)]

private theorem applySignedSwaps_is_buildMat12W19 (pNat : Nat) :
    ∀ (swaps : List (Nat × Nat)) (f : Nat -> Nat -> Nat),
      ∃ g : Nat -> Nat -> Nat,
        applySignedSwapsMat12NatW19 pNat swaps (buildMat12NatW19 f) = buildMat12NatW19 g
  | [], f => ⟨f, rfl⟩
  | (c1, c2) :: rest, f => by
    unfold applySignedSwapsMat12NatW19 swapOneMat12NatW19
    cases (Nat.ble (c1 + 1) 12 && Nat.ble (c2 + 1) 12 && (c1 != c2)) <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;>
      exact applySignedSwaps_is_buildMat12W19 pNat rest _

private theorem applySignedSwaps_eq_tracedBuildMat12W19 (pNat : Nat)
    (swaps : List (Nat × Nat)) (f : Nat -> Nat -> Nat) :
    applySignedSwapsMat12NatW19 pNat swaps (buildMat12NatW19 f) =
      buildMat12NatW19 (fun r j =>
        match traceColSwapsNW19 12 swaps j with
        | (j0, cnt) => iterNegModPW19 pNat cnt (f r j0)) := by
  rcases applySignedSwaps_is_buildMat12W19 pNat swaps f with ⟨g, hg⟩
  have hspec : ∀ r j : Nat, r < 12 -> j < 12 ->
      g r j = match traceColSwapsNW19 12 swaps j with
              | (j0, cnt) => iterNegModPW19 pNat cnt (f r j0) := by
    intro r j hr hj
    rcases traceColSwaps12_spec_w19 pNat swaps (buildMat12NatW19 f) r j hr hj with ⟨hj0, heq⟩
    rw [hg, natAt2DW19_buildMat12 g r j hr hj] at heq
    rcases htr : traceColSwapsNW19 12 swaps j with ⟨j0, cnt⟩
    rw [htr] at hj0 heq; dsimp only at hj0 heq ⊢
    rw [heq, natAt2DW19_buildMat12 f r j0 hr hj0]
  rw [hg]; exact buildMat12NatW19_congr g _ hspec

private theorem dotDirect12W19_eq (f g : Nat -> Nat) :
    ∀ n : Nat, n ≤ 12 ->
      dotDirectW19 f g n = dotPrefixNatW19 (buildRow12NatW19 f) (buildRow12NatW19 g) n
  | 0, _ => rfl
  | n' + 1, hn => by
    have hn_lt : n' < 12 := hn
    simp only [dotDirectW19, dotPrefixNatW19,
               dotDirect12W19_eq f g n' (Nat.le_of_lt hn),
               natAt1DW19_buildRow12 f n' hn_lt, natAt1DW19_buildRow12 g n' hn_lt]
    apply congrArg (dotPrefixNatW19 (buildRow12NatW19 f) (buildRow12NatW19 g) n' + ·)
    cases f n' <;> simp

private def checkULModPNat12FastBoolW19 (pNat u w k : Nat)
    (cert : List (Nat × Nat) × List (List Nat)) : Bool :=
  let apFn (r j : Nat) : Nat :=
    match traceColSwapsNW19 12 cert.1 j with
    | (j0, cnt) => iterNegModPW19 pNat cnt (fastApow12DirectModPW19 pNat u w k r j0)
  let uFn (n c : Nat) : Nat := uStrictNatValW19 cert.2 n c
  allNatLoop2W19 (fun r =>
    allNatLoop2W19 (fun c =>
      if Nat.ble (r + 1) c then
        dotDirectW19 (apFn r) (fun n => uFn n c) (c + 1) % pNat == 0
      else true) 12) 12 &&
  (natDiagDirectModPW19 pNat apFn uFn 12 != 0)

private theorem checkULModPNat12FastBoolW19_eq (pNat u w k : Nat)
    (cert : List (Nat × Nat) × List (List Nat)) :
    checkULModPNat12FastBoolW19 pNat u w k cert =
      checkULModPNat12BoolW19 pNat u w k cert := by
  unfold checkULModPNat12FastBoolW19 checkULModPNat12BoolW19 checkRawMatULModP12BoolW19
  dsimp only
  let apFn (r j : Nat) : Nat :=
    match traceColSwapsNW19 12 cert.1 j with
    | (j0, cnt) => iterNegModPW19 pNat cnt (fastApow12DirectModPW19 pNat u w k r j0)
  change (allNatLoop2W19 (fun r => allNatLoop2W19 (fun c =>
            if Nat.ble (r + 1) c then dotDirectW19 (apFn r) (fun n => uStrictNatValW19 cert.2 n c) (c + 1) % pNat == 0
            else true) 12) 12 &&
          (natDiagDirectModPW19 pNat apFn (uStrictNatValW19 cert.2) 12 != 0)) = _
  rw [applySignedSwaps_eq_tracedBuildMat12W19 pNat cert.1 (fastApow12DirectModPW19 pNat u w k)]
  let apRows := buildMat12NatW19 apFn
  let uCols := buildMat12NatW19 (fun c r => uStrictNatValW19 cert.2 r c)
  have hdot : ∀ (r c m : Nat), r < 12 -> c < 12 -> m ≤ 12 ->
      dotDirectW19 (apFn r) (fun n => uStrictNatValW19 cert.2 n c) m =
        dotListsPrefixW19 m (natRowAtW19 apRows r) (natRowAtW19 uCols c) := by
    intro r c m hr hc hm
    rw [dotListsPrefixW19_eq, dotDirect12W19_eq _ _ m hm]
    dsimp only [apRows, uCols]
    rw [natRowAtW19_buildMat12 _ r hr, natRowAtW19_buildMat12 _ c hc]
  have hloop :
      allNatLoop2W19 (fun r => allNatLoop2W19 (fun c =>
        if Nat.ble (r + 1) c then dotDirectW19 (apFn r) (fun n => uStrictNatValW19 cert.2 n c) (c + 1) % pNat == 0
        else true) 12) 12 =
      allNatLoop2W19 (fun r =>
        let row_r := natRowAtW19 apRows r
        allNatLoop2W19 (fun c =>
          if Nat.ble (r + 1) c then dotListsPrefixW19 (c + 1) row_r (natRowAtW19 uCols c) % pNat == 0
          else true) 12) 12 := by
    apply allNatLoop2W19_congr _ _ 12; intro r hr
    apply allNatLoop2W19_congr _ _ 12; intro c hc
    rw [hdot r c (c + 1) hr hc (by omega)]
  have hdiag : ∀ m : Nat, m ≤ 12 ->
      natDiagDirectModPW19 pNat apFn (uStrictNatValW19 cert.2) m =
        natDiagProdModPW19 pNat apRows uCols m := by
    intro m hm; induction m with
    | zero => rfl
    | succ m' ih =>
      have hm_lt : m' < 12 := hm
      simp only [natDiagDirectModPW19, natDiagProdModPW19,
                 ih (Nat.le_of_lt hm), hdot m' m' (m' + 1) hm_lt hm_lt hm]
  rw [hloop, hdiag 12 (Nat.le_refl 12)]

private def checkAffRangeULModP12BoolW19 (u pNat start : Nat) :
    Nat -> List (List (Nat × Nat) × List (List Nat)) -> Bool
  | 0, _ => true
  | cnt + 1, c :: cs =>
    checkULModPNat12BoolW19 pNat u start 1 c &&
      checkAffRangeULModP12BoolW19 u pNat (start + 1) cnt cs
  | _, [] => false

private def checkAffRangeULModP12FastBoolW19 (u pNat start : Nat) :
    Nat -> List (List (Nat × Nat) × List (List Nat)) -> Bool
  | 0, _ => true
  | cnt + 1, c :: cs =>
    checkULModPNat12FastBoolW19 pNat u start 1 c &&
      checkAffRangeULModP12FastBoolW19 u pNat (start + 1) cnt cs
  | _, [] => false

private theorem checkAffRangeULModP12FastBoolW19_eq (u pNat : Nat) :
    ∀ (cnt start : Nat) (cs : List (List (Nat × Nat) × List (List Nat))),
      checkAffRangeULModP12FastBoolW19 u pNat start cnt cs =
        checkAffRangeULModP12BoolW19 u pNat start cnt cs
  | 0, _, _ => rfl
  | _ + 1, _, [] => rfl
  | cnt' + 1, start, c :: cs => by
    change (checkULModPNat12FastBoolW19 pNat u start 1 c && checkAffRangeULModP12FastBoolW19 u pNat (start + 1) cnt' cs) =
      (checkULModPNat12BoolW19 pNat u start 1 c && checkAffRangeULModP12BoolW19 u pNat (start + 1) cnt' cs)
    rw [checkULModPNat12FastBoolW19_eq, checkAffRangeULModP12FastBoolW19_eq u pNat cnt' (start + 1) cs]

private theorem checkAffRangeULModP12FastBoolW19_glue (u pNat : Nat) :
    ∀ (a b start : Nat) (cs : List (List (Nat × Nat) × List (List Nat))),
      checkAffRangeULModP12FastBoolW19 u pNat start a cs = true ->
      checkAffRangeULModP12FastBoolW19 u pNat (start + a) b (dropCertsW19 a cs) = true ->
      checkAffRangeULModP12FastBoolW19 u pNat start (a + b) cs = true
  | 0, _, start, _, _, hb => by rw [Nat.zero_add]; rw [Nat.add_zero] at hb; exact hb
  | _ + 1, _, _, [], ha, _ => by cases ha
  | a' + 1, b, start, c :: cs, ha, hb => by
    rw [Nat.succ_add]
    change (checkULModPNat12FastBoolW19 pNat u start 1 c && checkAffRangeULModP12FastBoolW19 u pNat (start + 1) a' cs) = true at ha
    change (checkULModPNat12FastBoolW19 pNat u start 1 c && checkAffRangeULModP12FastBoolW19 u pNat (start + 1) (a' + b) cs) = true
    rcases bool_and_split ha with ⟨hc, hrest⟩
    rw [hc, Bool.true_and]
    apply checkAffRangeULModP12FastBoolW19_glue u pNat a' b (start + 1) cs hrest
    rwa [show (start + 1) + a' = start + (a' + 1) by omega]

private theorem unpack_affRangeULModP12_w19 (u pNat : Nat) (hp : pNat ≥ 2) :
    ∀ (cnt start : Nat) (cs : List (List (Nat × Nat) × List (List Nat))),
      checkAffRangeULModP12BoolW19 u pNat start cnt cs = true ->
      ∀ t : Nat, start ≤ t -> t < start + cnt ->
        intDet 12 (apow12KDivW19 u (t : Int) 1) % (pNat : Int) ≠ 0
  | 0, _, _, _, _, hlo, hhi => by omega
  | _ + 1, _, [], hchk, _, _, _ => by cases hchk
  | cnt' + 1, start, c :: cs, hchk, t, hlo, hhi => by
    change (checkULModPNat12BoolW19 pNat u start 1 c && checkAffRangeULModP12BoolW19 u pNat (start + 1) cnt' cs) = true at hchk
    rcases bool_and_split hchk with ⟨hcur, hrest⟩
    by_cases hteq : t = start
    · subst hteq; exact checkULModPNat12BoolW19_sound pNat u t 1 hp c hcur
    · exact unpack_affRangeULModP12_w19 u pNat hp cnt' (start + 1) cs hrest t (by omega) (by omega)

private theorem det12_t4u3_nonzero_of_proj_sieve_w19 (u pNat : Nat) (hp : pNat ≥ 3)
    (hinv_b : checkAllInvModPBoolW19 pNat pNat = true)
    (hinf_nz : intDet 12 (apow12KDivW19 u 1 0) % (pNat : Int) ≠ 0)
    (haff_spec : ∀ t : Nat, t < pNat -> intDet 12 (apow12KDivW19 u (t : Int) 1) % (pNat : Int) ≠ 0)
    (W K : Nat) (hW : W ≥ 1) (hK : K ≥ 1) :
    intDet 12 (laurentTwoBaseT4U3Mat12 W K u) ≠ 0 := by
  let p : Int := (pNat : Int)
  have hinv_spec : ∀ x : Nat, x < pNat -> x ≠ 0 ->
      (x * powModFuelNatW19 8 x (pNat - 2) pNat) % pNat = 1 := by
    have hlp : ∀ n : Nat, n ≤ pNat -> checkAllInvModPBoolW19 pNat n = true ->
        ∀ x : Nat, x < n -> x ≠ 0 -> (x * powModFuelNatW19 8 x (pNat - 2) pNat) % pNat = 1 := by
      intro n hn; induction n with
      | zero => intros _ _ hlt; omega
      | succ n' ihn =>
        intro ha x hx hne
        unfold checkAllInvModPBoolW19 at ha
        rcases bool_and_split ha with ⟨hcur, hprev⟩
        by_cases hxeq : x = n'
        · subst hxeq; rw [beq_false_of_ne hne] at hcur; exact beq_iff_eq.mp hcur
        · exact ihn (Nat.le_of_lt hn) hprev x (by omega) hne
    exact hlp pNat (Nat.le_refl _) hinv_b
  have hcancel15 : ∀ (x inv : Nat) (V : Int),
      (x * inv) % pNat = 1 ->
      (intPowNat (x : Int) 15 * V) % p = 0 ->
      V % p = 0 := by
    intro x inv V hxinv hxv0
    have hp_d : ∀ d : Nat, ((x * inv) ^ d) % pNat = 1 := by
      intro d; induction d with
      | zero => simp only [Nat.pow_zero]; exact Nat.mod_eq_of_lt (by omega)
      | succ d' ih => rw [Nat.pow_succ, Nat.mul_mod, ih, Nat.one_mul, Nat.mod_mod, hxinv]
    let x15 : Nat := x ^ 15
    let inv15 : Nat := inv ^ 15
    let prod15 : Nat := x15 * inv15
    have hp15_1 : prod15 % pNat = 1 := by
      dsimp [prod15, x15, inv15]; rw [← mul_pow_w19 x inv 15]; exact hp_d 15
    have hm1 : (prod15 : Int) % p = 1 := by
      dsimp [p]
      have hdm := congrArg (fun n : Nat => (n : Int)) (Nat.div_add_mod prod15 pNat)
      rw [hp15_1] at hdm
      rw [← hdm, Int.natCast_add, Int.natCast_mul, Int.add_comm, Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt (by decide) (by omega)
    have h1p : (1 : Int) % p = 1 := Int.emod_eq_of_lt (by decide) (by dsimp [p]; omega)
    rw [intPowNat_natCast_w19 x 15] at hxv0
    change (x15 : Int) * V % p = 0 at hxv0
    calc V % p
        = ((1 % p) * (V % p)) % p := by rw [h1p, Int.one_mul, Int.emod_emod]
      _ = (((prod15 : Int) % p) * (V % p)) % p := by rw [hm1, h1p]
      _ = ((prod15 : Int) * V) % p := (Int.mul_emod _ _ _).symm
      _ = ((inv15 : Int) * ((x15 : Int) * V)) % p := by
          dsimp [prod15]; rw [Int.mul_comm (x15 : Int), Int.mul_assoc]
      _ = (((inv15 : Int) % p) * (((x15 : Int) * V) % p)) % p := Int.mul_emod _ _ _
      _ = 0 := by rw [hxv0, Int.mul_zero, Int.zero_emod]
  have hmat_mod_congr : ∀ (w1 w2 k1 k2 : Int),
      p ∣ (w1 - w2) -> p ∣ (k1 - k2) ->
      p ∣ (intDet 12 (apow12KDivW19 u w1 k1) - intDet 12 (apow12KDivW19 u w2 k2)) := by
    have hd_add : ∀ a1 a2 b1 b2 : Int, p ∣ (a1 - a2) -> p ∣ (b1 - b2) -> p ∣ ((a1 + b1) - (a2 + b2)) := by
      intro a1 a2 b1 b2 ⟨q1, h1⟩ ⟨q2, h2⟩; exact ⟨q1 + q2, by rw [Int.mul_add]; omega⟩
    have hd_sub : ∀ a1 a2 b1 b2 : Int, p ∣ (a1 - a2) -> p ∣ (b1 - b2) -> p ∣ ((a1 - b1) - (a2 - b2)) := by
      intro a1 a2 b1 b2 ⟨q1, h1⟩ ⟨q2, h2⟩; exact ⟨q1 - q2, by rw [Int.mul_sub]; omega⟩
    have hd_mul : ∀ a1 a2 b1 b2 : Int, p ∣ (a1 - a2) -> p ∣ (b1 - b2) -> p ∣ (a1 * b1 - a2 * b2) := by
      intro a1 a2 b1 b2 ⟨q1, h1⟩ ⟨q2, h2⟩
      exact ⟨q1 * b1 + a2 * q2, by
        have : a1 * b1 - a2 * b2 = (a1 - a2) * b1 + a2 * (b1 - b2) := by
          simp only [Int.sub_mul, Int.mul_sub]; omega
        rw [this, h1, h2, Int.mul_add, Int.mul_assoc p q1 b1,
            ← Int.mul_assoc a2 p q2, Int.mul_comm a2 p, Int.mul_assoc p a2 q2]⟩
    have hd_pow : ∀ (a1 a2 : Int) (d : Nat), p ∣ (a1 - a2) -> p ∣ (intPowNat a1 d - intPowNat a2 d) := by
      intro a1 a2 d hd; induction d with
      | zero => exact ⟨0, by simp [intPowNat]⟩
      | succ d' ih => exact hd_mul a1 a2 _ _ hd ih
    intro w1 w2 k1 k2 hw hk
    apply intDet_congr_dvd p 12
    intro i j; unfold apow12KDivW19; dsimp only
    let r : Int := (i.val % 3 : Int)
    let s : Int := (i.val / 3 : Int)
    let E : Int := ((2 ^ (i.val % 3 * (j.val / 4 * u)) * 3 ^ (i.val / 3 * (j.val / 4 * u)) : Nat) : Int)
    have hlin : p ∣ ((r * w1 + s * k1) - (r * w2 + s * k2)) :=
      hd_add _ _ _ _ (hd_mul r r w1 w2 ⟨0, by simp⟩ hw) (hd_mul s s k1 k2 ⟨0, by simp⟩ hk)
    by_cases ht3 : j.val % 4 < 3
    · rw [ite_true_of_w10 ht3, ite_true_of_w10 ht3]
      exact hd_mul _ _ E E (hd_pow _ _ (j.val % 4) hlin) ⟨0, by simp⟩
    · rw [ite_false_of_w10 ht3, ite_false_of_w10 ht3]
      have hsk : p ∣ (s * k1 - s * k2) := hd_mul s s k1 k2 ⟨0, by simp⟩ hk
      have hqc : p ∣ (qCubicW19 (i.val % 3) w1 (s * k1) - qCubicW19 (i.val % 3) w2 (s * k2)) := by
        rcases (by have := Nat.mod_lt i.val (by decide : 0 < 3); omega : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2) with h | h | h
        · simp only [h, qCubicW19]
          exact hd_mul _ _ _ _ (hd_sub _ _ _ _ hsk hw)
            (hd_sub _ _ _ _ hsk (hd_mul 2 2 w1 w2 ⟨0, by simp⟩ hw))
        · simp only [h, qCubicW19]
          exact hd_mul _ _ _ _ (hd_add _ _ _ _ hw hsk) (hd_sub _ _ _ _ hsk hw)
        · simp only [h, qCubicW19]
          exact hd_mul _ _ _ _ (hd_add _ _ _ _ (hd_mul 2 2 w1 w2 ⟨0, by simp⟩ hw) hsk)
            (hd_add _ _ _ _ hw hsk)
      exact hd_mul _ _ E E (hd_mul s s _ _ ⟨0, by simp⟩ hqc) ⟨0, by simp⟩
  intro hz_det
  let g := Nat.gcd W K
  have hg_pos : g ≥ 1 := Nat.gcd_pos_of_pos_left K hW
  let w' := W / g
  let k' := K / g
  have hW_eq : W = g * w' := by rw [Nat.mul_comm]; exact (Nat.div_mul_cancel (Nat.gcd_dvd_left W K)).symm
  have hK_eq : K = g * k' := by rw [Nat.mul_comm]; exact (Nat.div_mul_cancel (Nat.gcd_dvd_right W K)).symm
  have hk'_pos : k' ≥ 1 := Nat.div_pos (Nat.le_of_dvd hK (Nat.gcd_dvd_right W K)) hg_pos
  rw [hW_eq, hK_eq, det12_t4u3_homog18_w19 u g w' k'] at hz_det
  have hg18_pos : intPowNat (g : Int) 18 > 0 := by
    rw [intPowNat_natCast_w19 g 18]; have := nat_pow_pos_of_pos g hg_pos 18; omega
  have hdet_wk0 : intDet 12 (laurentTwoBaseT4U3Mat12 w' k' u) = 0 := by
    by_cases h0 : intDet 12 (laurentTwoBaseT4U3Mat12 w' k' u) = 0
    · exact h0
    · exact False.elim (Int.mul_ne_zero (by omega) h0 hz_det)
  have hapow0 := stirling_1728_det12_t4u3_u_w19 u w' k'
  rw [hdet_wk0, Int.mul_zero, (apow12_extract_k3_and_homog15_w19 u).1 (w' : Int) (k' : Int)] at hapow0
  have hk3_nz : intPowNat (k' : Int) 3 ≠ 0 := by
    rw [intPowNat_natCast_w19 k' 3]; have := nat_pow_pos_of_pos k' hk'_pos 3; omega
  have hkdiv0 : intDet 12 (apow12KDivW19 u (w' : Int) (k' : Int)) = 0 := by
    by_cases h0 : intDet 12 (apow12KDivW19 u (w' : Int) (k' : Int)) = 0
    · exact h0
    · exact False.elim (Int.mul_ne_zero hk3_nz h0 hapow0.symm)
  let wm := w' % pNat
  let km := k' % pNat
  have hwm_lt : wm < pNat := Nat.mod_lt w' (by omega)
  have hkm_lt : km < pNat := Nat.mod_lt k' (by omega)
  have hnot_both0 : ¬ (wm = 0 ∧ km = 0) := by
    rintro ⟨hw0, hk0⟩
    rcases Nat.dvd_of_mod_eq_zero hw0 with ⟨qw, hqw⟩
    rcases Nat.dvd_of_mod_eq_zero hk0 with ⟨qk, hqk⟩
    have hdW : pNat * g ∣ W := ⟨qw, by rw [hW_eq, hqw]; ac_rfl⟩
    have hdK : pNat * g ∣ K := ⟨qk, by rw [hK_eq, hqk]; ac_rfl⟩
    have hle := Nat.le_of_dvd hg_pos (Nat.dvd_gcd hdW hdK)
    have h2g : 2 * g ≤ pNat * g := Nat.mul_le_mul_right g (by omega)
    omega
  have hm_wk : intDet 12 (apow12KDivW19 u (wm : Int) (km : Int)) % p = 0 := by
    rcases hmat_mod_congr (wm : Int) (w' : Int) (km : Int) (k' : Int)
      (int_mod_sub_dvd_w19 w' pNat) (int_mod_sub_dvd_w19 k' pNat) with ⟨q, hq⟩
    rw [hkdiv0, Int.sub_zero] at hq
    rw [hq, Int.mul_emod_right]
  by_cases hkm0 : km = 0
  · have hwm_ne : wm ≠ 0 := fun hw0 => hnot_both0 ⟨hw0, hkm0⟩
    let inv := powModFuelNatW19 8 wm (pNat - 2) pNat
    have hinv := hinv_spec wm hwm_lt hwm_ne
    rw [hkm0, show (wm : Int) = (wm : Int) * 1 by omega,
        show ((0 : Nat) : Int) = (wm : Int) * 0 by omega,
        (apow12_extract_k3_and_homog15_w19 u).2 1 0 (wm : Int)] at hm_wk
    exact hinf_nz (hcancel15 wm inv _ hinv hm_wk)
  · let inv := powModFuelNatW19 8 km (pNat - 2) pNat
    have hinv := hinv_spec km hkm_lt hkm0
    let t := (wm * inv) % pNat
    have ht_lt : t < pNat := Nat.mod_lt _ (by omega)
    have htkm_dvd : p ∣ ((km : Int) * (t : Int) - (wm : Int)) := by
      have hnat : (km * t) % pNat = wm := by
        dsimp [t]
        rw [Nat.mul_comm km, Nat.mod_mul_mod, Nat.mul_assoc wm inv km, Nat.mul_comm inv km,
            Nat.mul_mod wm (km * inv) pNat, hinv, Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hwm_lt]
      have hsub := int_mod_sub_dvd_w19 (km * t) pNat
      rw [hnat] at hsub
      rcases hsub with ⟨q, hq⟩
      simp only [Int.natCast_mul] at hq
      exact ⟨-q, by dsimp [p]; rw [Int.mul_neg]; omega⟩
    rcases hmat_mod_congr ((km : Int) * (t : Int)) (wm : Int) ((km : Int) * 1) (km : Int)
      htkm_dvd ⟨0, by simp⟩ with ⟨qd, hqd⟩
    have htk_mod0 : intDet 12 (apow12KDivW19 u ((km : Int) * (t : Int)) ((km : Int) * 1)) % p = 0 := by
      have heq : intDet 12 (apow12KDivW19 u ((km : Int) * (t : Int)) ((km : Int) * 1)) =
          intDet 12 (apow12KDivW19 u (wm : Int) (km : Int)) + p * qd := by omega
      rw [heq, Int.add_emod, hm_wk, Int.zero_add, Int.mul_emod_right, Int.zero_emod]
    rw [(apow12_extract_k3_and_homog15_w19 u).2 (t : Int) 1 (km : Int)] at htk_mod0
    exact haff_spec t ht_lt (hcancel15 km inv _ hinv htk_mod0)

-- `12 × 12` `P^1(F_p)` Sieve Certificates for `u = 6..9` (`p = 197, 13, 103, 67`):
private def sieve12InfU6W19 : List (Nat × Nat) × List (List Nat) := decodeUCert12W19 (0x0, 0xc24b375bb4c01121839b002b9ca48218406b6531313607b120580d53af14455b8ac17e1e7d08966bc24fb6540087c342448e27293200c4340a19a46db872c4000000)

private def sieve12AffU6C0W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0xa2012300c5014601280169, 0x7f6cb8c200002376613a0dc20058c2020000c400003902006d03c45c8f69623a0100ae3b0000000000000000000000000000000000008400000000000000000040c4),
  (0xa400c50127, 0x8b57c0a87120522427423a06c30000b37c3b838e2e97985b03004f00ad948fc3007100c460bac00100a00015541663b3c2007600af32c4a32b380200530001c40000),
  (0x0, 0xaa356d477a7411b770ab5361366d7575516c430b1d5ebc5016651925b65250528db84388019d18aab37d8c15004b164836b920a51900c3205401ae60aca0c4000000),
  (0x0, 0x6816646f508b988db014b5967c113768246d6169029b6e2164713fc25e511555133393a19e0097505610074b0037640116b752af9400c280071960548603c4000000),
  (0x0, 0x48391e952f88999b88071943bf8a5d841c24137cc02a2518ac9b1daaa529804f444f6083496531c2a3a7b4990069827f475148b76f00c1067125182aa81bc4000000),
  (0x0, 0x9245828e9e02a4bbba6b118f9720b3b466be435a64023b2600ae4b373eb2167f2abe131caa04bab514867f1b00021b1b636f88b80a00c035b19dc4177a8ec4000000),
  (0x0, 0x9e0283197c9511825463a25c45739ea5083688829cacc2536c06442c74425d12757bb414953e13be8d0e9944006696bd1d223f844a00bf004ca258bf8199c4000000),
  (0x0, 0x695e652d525a317c796b436d75485a215d8760863135a7615d2aa86ec2379abc9a5f4477621c0fbd35b85b3a00b4330b1cc47552b000be63910a679b1d57c4000000),
  (0x0, 0x7265751ab130f3d86780a9fbc6439131570336d9f70421a2c058410889c0375afaf4b3f76761b3414746cba0008a573b93d33809a00bd049d9898c041b5c4000000),
  (0x0, 0x5f068e3a991e1e11b457155eaf1a742e701837bf1327045467985d73680000c260058463c06008b98c5cb64a00903a1388c24e367300bc6428535d2d6852c4000000),
  (0x0, 0x1044119a70822e2c89a5651557807ea43a244335491ead6a63c34b1c1e28c03437635f9057772e121b596538006eab3fa5427aa80500bb0d6d9e61027aa9c4000000),
  (0x0, 0x9d2560ae1f449a9cbeb26d836f87a8a0a8480b9d0d420b57437e3008450e3baa6537311803092825b998a01e0036880d110051887000ba9a9b2a814795bdc4000000),
  (0x0, 0x9803621353e7a54afa15f6d17bcbd621a4cab07644d99a4574a44797a2f6d370fc410b09d642199660a9111007fad71202d26ab2500b957bca86d7b814cc4000000),
  (0x0, 0x6c06366dbf9a2386ac36b9108d6ab7a76e2ec434830f722f5aa387ac293ca58cc45119a35e3f10443666aec200aa628a54189a901300b84959c16a223e19c4000000),
  (0x0, 0x39900d9f883040142967be1d2c5f7810b0ab1c12544c775a922e2411c428210f36661e4845bc678901743971005d07af973013915800b79f8b3b3297a1b4c4000000),
  (0x0, 0xac5d2c377c264fa54fc0562d4f39839f84250424304b9eb72b6a90950843ac4c169e32c4123c4d4bc17e3c03004b1a748e7135414500b64370ad995b3530c4000000),
  (0x0, 0xa8890d028a1254bb7faaad3e3a1c4f251d16b02b26603b72057490149c951f1e7542ac8e3e012b0db618579100629022bb087cbd4d00b5630041bf5135b1c4000000),
  (0x149, 0xba02721663004c4c3babac9e757969b7b10a845637c2976b106c05a345b23a1e9d6458891f9a497d1fc0594e00663a3263373b7d8e00b405a05bb559c022c4000000),
  (0x0, 0x84aa062b4244b8b84bad3ec14105406f2c0c2e64a6c02787651d52766b8cc0bb02c323c1094f6380bb88ba7500ab5b91221f43739c00b39f5cbf5fa8734fc4000000),
  (0x0, 0xa8167fbd39309f596f5e896843a2be7d8a6da2bc35a14375bc23900425436f51724596342c4d2f7618c10157004e5469799f9a500d00b22c492008a235c1c4000000)
  ] : List (Nat × Nat)).map decodeUCert12W19

private def sieve12AffU6C1W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x0, 0x189e54159c265a626ec0933130b32d0633281f434923b82357b84d0b2816adb2b6253155259f7d225bb36e0e006f37434f5c699a6500b18d367c6d0d78bac4000000),
  (0x0, 0xc11d3fa01381185ab911965602a12153a791a6b4681c198d6e4c413975c145b8631152be072a8d02394e2c5e0088a6749d1e1117be00b009997c5679848cc4000000),
  (0x0, 0x5a872160a6185098bd7684724a2155be65478328749b5f5ca29c8a6781c2b07e4d4c489b1da8834aa0572b6a00ab24adc07c34533800af8f855122293b5ec4000000),
  (0x0, 0x9a927034b91280a9416d313f347ba2734500a5813d2c34770c95107d20a0872faa443c02a62d3a442cb31e050075529cb7619f892d00ae659d3cb830b548c4000000),
  (0x0, 0xa16c776f4c997ac2981b43a63f8d228b939b63c0a69b9ba55b6211872c6b2374c0ae877bc02384240f3a3d9800965576637f153f7500ad80a34c6963b43ec4000000),
  (0x0, 0xb38103ad4038c2c0550d8b7aa840762c55af40192abcb38d7185ab034fb802ae6c01934446a66ea975b8664800160467212e0b220200ac21970053401ac2c4000000),
  (0x0, 0xc4070928aa431e826e95b80a8481387598a56fa50b84b28304473597b1552c196ebb267d748c497f576d549300a802390a3ab2b66c00ab192ec4c07e902ec4000000),
  (0x0, 0x420ab77ca3c1b84663840f3f447972c4924da95f32820e641b4ec05a5b4a5b9cb39b7860925492744ea88334008820ba106f87816800aa8c1465a977056bc4000000),
  (0x0, 0xb60ca543068648c311288e98ab60498e91b6b3b96981c19fc2847a927d4fa6302837c06e6c66b5309ec28bb00089c4a16eb040942c00a901c36502414b33c4000000),
  (0x0, 0x35ea1558a544a7b4eacb7463e20babdbe9d3ead441b17357a32ad55417f2b090a4b256a50b8521d78139bb400bd5f7ca5167f7f7c00a855243c4a931870c4000000),
  (0x0, 0x79bb445f8f933452c230aab3bc7a660885140c00bc2f0732a04fbb59786127385949a5387d8e69717f6b15320025566cbd50c32d8500a7372f0024760a6cc4000000),
  (0x0, 0xafc35a3580908cb3a4bab06101775d0a0709bab4347f138d21323ca4876d8d356a4253191a487092794a675f009b829eac99858c7400a611326da3938921c4000000),
  (0x0, 0x1ca4bc0935a764aa43624c7e169a568a0474941f93145e47a018a114b0115d904cbf7ca632beb715401308b800918029ad61930a8900a5a8329c24ad24b1c4000000),
  (0x0, 0x7f189b516c587a09b7279f9f0b968a70a302075e656f721774432f20908aaea9137fc199be426701452750450008b5a01bac94ac6700a405ac56508296a5c4000000),
  (0x0, 0x55046e731b7a640a1b129f7ac3ae9736675c72366e08385e0c4c247d8b6158766d373e6d95970cb8146e417600775aab1e3648264700a34a72b2b879a148c4000000),
  (0x0, 0x652034b82c5624a6b4579989bf3a80747e5150bb924662101cbbbd9aa0891883b43d12c25dba517826457459006c69b26c1fa0337200a28c375fa80a082bc4000000),
  (0x0, 0x5e409a12784aba6286798f81b5be3019862f781c11829c4a40505a6a1a1a14b455a8a93917638d1f69b984b1003869b4a27b85164e00a131763184756b5bc4000000),
  (0x169, 0xb23192a500009aa862268157642f579dad56b6bac12b9dbe7d25c133afb9858c94a8673e13526d3d61006d1f004b3673703593310c00a087290748a00492c4000000),
  (0x0, 0x6d9dbf9e813448be2dbcaf6b2c5db832a56eb0b3939129576966bf24be1e7a1934428fa74ba86c5ec1797547008256505350254169009f5b1b3a5b5f06a1c4000000),
  (0x0, 0xa6684e8329064f7773355ca16416520d578daaa7a40813b23e12bc8423a88b6a2d001a8689000b688d2dba83007809415e37584c48009e3a890d86b30941c4000000)
  ] : List (Nat × Nat)).map decodeUCert12W19

private def sieve12AffU6C2W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x0, 0x68023b4bbe98b44c3143b97c366ba733a92d124e815f0d1443a460022b1907a09c1f4a7a2ac4546bbf08b666000c171f793e3c8195009d1bbf19812165c3c4000000),
  (0x0, 0x8319861873482f9bae0d8fbb198aa268892f2489131f7d71465c3a10663e4e4d3834b09aafaa87291d90ac77002a89909a968986b3009c8e9a0c7e698bb5c4000000),
  (0x0, 0xba680b609c3a9836ca96bb72900570f823c744946685c4b6f5920142b869a9a49a4325149a04d8c0458b17a0052509b1921789b5f009b6c607c556ca5b1c4000000),
  (0x0, 0x8c7a861c8160414429823404b5c39e7c20bc98b7473b59be99945649c424bd0d5f9c6c77105817811ec327a70085745507839623bd009a6eb06c2b316f7cc4000000),
  (0x0, 0x1faf0e6a57809d884822670c677d1c7a5a8b592727539b8f5dc2547a6a88206c0f6c21913502a459af103d7d0032967806a1725f1c009908987b6703714bc4000000),
  (0x0, 0x710c72463a571f512d59375b0e3d351d773ead2765a3ab9d0f48a51f16b1b5ae740627be556e3555aaae904200011c4c076f8096170098a1a596b57d20a6c4000000),
  (0x0, 0x9b90439397828303bfbc7cac7d095411a4b51b8333029f2d00303c850405664191201f05295b26bc2d777395008ebb332d170da4790097305416c4958940c4000000),
  (0x0, 0x419082a17f5b82566fa727426a8f566d156a68b8a08a2e884b73c30c3c5838496403802835bf8683801e2b02003368404cb03d188300965f18a7795202b9c4000000),
  (0x0, 0x50a02a6f26c21d8b7907128917737d0c41251d169e1b8aad59545c159b860d3d3233530b6c3bb3015b177b2600bd62877d1a78ad9d00953b151b6b7169b0c4000000),
  (0x0, 0x652bd6ea22c1e764b779c542723131758620b77369e1d479b77294c430b42482697c21a1e8b4f3e2e4148a2003a1b253583a1c2c200947e0652294e9c79c4000000),
  (0x0, 0x60c0977c933a6eb137a058a0988f7b18697cb81eb76440973baa17220b697e52b2aca14250aa352202b0a1120002116aad39a33e010093aab7b9891baea3c4000000),
  (0x0, 0xbb850ba19e98198fc1bd1e543050bf82316b9a33bb747c4f1c84498427bd226f704238ba3d13137cb071168c00acb13f4d1f11a97100927570a3a8417c41c4000000),
  (0x0, 0xc4ae414b175e181e082e138c7ab85b5d1aac83c461ad647ca19d6e7a64395b83876e382b3f0ab63677277d5600598b0e0d7c6473360091924ab02328574bc4000000),
  (0x0, 0x32a5e2b391c4caf8f32ad1e8aab93083813c37d9fac1d21a57ebfa63b9362a38ba0bc3d8f58801251ad743000994481ab21898c4f0090b36f881f47061fc4000000),
  (0x0, 0x7e600e97358daa8b5602207c708e56925a03a37eab32ad2018c392b2bf85775e607e276c9fc49024a76f8a0d000b517c88b6371934008fc1a818ac023313c4000000),
  (0x0, 0x1ab2b3041371878a71544b4159ab469d571a87081a73256a610557a6b03e8f4a5c8b1b4aa65c27b033bd4150005f8db4ab7f6ea1b4008e4e8daf63c06e1fc4000000),
  (0x0, 0x17b3444016a7b20c202f3e1513379e34b1605e1f00837eaec05c576e37be37b10927b40317699fba3e22282c003a043b1b9e045416008d02313504696e57c4000000),
  (0x0, 0x42026e1d015aa8b75b0e811455c1af776c218ab35b8436047abb088a67a01d43b82ec254847e363e1549668d00aec140997e032346008c248e674a0abd3bc4000000),
  (0x0, 0x92c282934e67228b0893592e904ba0b78bb16876003b88c0851b147dad5d268b0eb5019c384f2b4fb83d792d00a637273fae5c5f3e008bbcb4633faab148c4000000),
  (0x0, 0x632e37b712578d687734140b7f2f5d0f8819796c6c4208b82d93c22f897189c01fa0705aaea88ac03d25907e009c755412210ea85b008a91ab7b97320396c4000000)
  ] : List (Nat × Nat)).map decodeUCert12W19

private def sieve12AffU6C3W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x0, 0xa8227d9b4763ad47855c7e2b0f127c0e248f8a848b0d7d6b916276438046b87253246b8b29102245392a026f003b625784ad7c33a500891d01bc33634f82c4000000),
  (0x0, 0xa2ac5f128f9b519650a3b779803ba1600e798c8b43c03240374f5d620724a59a1087be77b4bf58be99893c20003d9a44889eaba0820088b804af8d766863c4000000),
  (0x0, 0xb54419be5293b1b16f556d10b23a03be5514bc97200d99ab3cad3a437a102f106e2cb71371392aaa392b094900004fa49f1869ab3a0087bf9f4c88188b82c4000000),
  (0x0, 0x2369ad34207a36a47d870168a5aabd59635cac179611aab003447ac16fa76d14435d8179644d2d4b548a8762001f438f4f0b0a6781008680c060c1814b04c4000000),
  (0x0, 0x85b0c1ac4c7b7abb4dbc82200448315aa8c20e6dbc94374a48a25f76185f20075e788f48537f3730389e2e2e005192a041ad0622a700854a42007c23664fc4000000),
  (0x0, 0x7998b8c44aad1dc032500275591ebcb249b56e26319d932d8d4a1f192cbc59244cb24603238b9ec3ba9f87bd0007b87f2fa4ac7b7a008429adb0377ba6acc4000000),
  (0x0, 0xa210164abd48ac411fbbb415a17bb36a1743c4851623041e147c294568000030260e138557a91f0324334da50030c42c598dc38696008358045fb0499c80c4000000),
  (0x0, 0x45065085741e41ad5eaa8d0aa74f19582e5eb08e24c38907b061955e037b4817931695b67b69b42c9f7a89c3007f2a3e94796e07880082428da014643067c4000000),
  (0x0, 0x427ea17453ab7b5576968c493a862ab379844ca0aba5b45e4bc0959308bb92c21c67665d4506a772547992800062671868ac211a86008171838179053032c4000000),
  (0x0, 0xa4bb1d6f2daa31af567d0c5938a227beb56911a9683d37b2a93a0c825f1540873c30096aa11f829aa00e316e000c9c805aa91c080f008019612e1b8bb943c4000000),
  (0x0, 0xc3b14b9c3db48b7ea0c44542295b0d3a9a28880cb6030b32bc1b150649c12d7d11c3542c8c2c6c80053187aa00917d98a55c40ad39007f267da408aab0bfc4000000),
  (0x0, 0xadc121118a5092b38d7c719252a8ab953abb2696b5807c5a21b2bb62ac501c8020201b056d46782d2eb1457b0002042c76a93e0b22007e34841ba3130a63c4000000),
  (0x0, 0x469aa45a5491ab1ac4e7d2d1d256f426610938a9a170b28a80f7a3e5c1e5c675d67ae38749e441b81ab1cc0007129ba3226395227007d6915541cb64b87c4000000),
  (0x0, 0x20741aa457345bc38441af0c474a8cab8211325b9b2349835219334329be4fa89094534d0ab76e7d4d3ba7a6007d593e27a58b37a8007cc3250e72ac9282c4000000),
  (0x0, 0xaaba765407c2b4182c79584b66144c3610c367412497887f3e82a616880a20b58f33b16c7363625113367c39006768ac4c0e39a006007b9f364986431fafc4000000),
  (0xc5, 0x7790344c094202b61c1b307fb89c5a7869a229748970159f4b885000c36d74052d7e765729c46a0b9593bd9f0097196478227b411c007a2c60602874890100000000),
  (0x0, 0x3197379db2275e228cc08501b3ab2284875b84774956409606ac989e46316d4f194bbb8e621128716b08094300a4b49e102eab31970079979808be192d27c4000000),
  (0x0, 0x683f463397278f2c81aebb6e15ba888691ad88729ca9373d5b874686af3118a46590ab97b6aa5e299eb3934d002bb52085189905100078aebc61693e7f3fc4000000),
  (0x0, 0x70aa9272c30db45c25127e1d47c2c3c1a47866a28179251d3eaa6c83bd53b4a9a6a60c5cbc454595a7001652009a907d504cb6102400779fa29b861b5942c4000000),
  (0x0, 0x578814098f53400c5b4db54ea51e06954fbb4f357d12b7c34c243f593d9589714f2b12bbb8ad64c358564e8200c2663d90b96311350076aa447478a1866cc4000000)
  ] : List (Nat × Nat)).map decodeUCert12W19

private def sieve12AffU6C4W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x16a, 0x380c00022541a2878e15659fa7a38d4157a0b0a52853beb82d60bfa97a17bc4a12490d1aad3f9a888c903f7c00696243b84d1b6dad007570a7919765061cc4000000),
  (0x0, 0x8ab34b1e4c63254f49bda25ec49584b30878b0823c56502b608422057e65204792a43b316f1518715046019f00354c80781ca446a600745129376441a3c0c4000000),
  (0x0, 0x2b630983ad4352618d8c7c2c43666589b5af9c24a9304e0fb03c6faa9f7fae41318c90605c0982898243994f004cc16bb3a76a4abc0073128f731489561bc4000000),
  (0x0, 0x955d1d7c5c002507bc508e6e7b230b135c4f0a6118309b41b6b670b5000a4bc1574f57a449285f0468a334b700bc44b9632807c2a200721993840e0f5510c4000000),
  (0x0, 0xab37513a0f1a989b63a06ba8a0b687780c860c582ec3bd71ad685cafadc05b1abc997ea9ab646dab8c994581008b9639183323a59200718dbe3a175d6916c4000000),
  (0x0, 0x2769a051538a885a8f449f6b3ba15a9c1863a8519844780b031b22c452a577143f5d0b059a568f140252190b00818525a7241327ba007030bf30c1aaa301c4000000),
  (0x0, 0x43fb72a2065a368968a557806c31205031a802e6d498e566a0944813572ba67c093516a8ca76436913c935b00b02c3d4a285667c1006f52170a5abc8144c4000000),
  (0x0, 0x357fa0245003197e7c357a101632922e7eb04e9a0b945923a81b60534a072d1b3c13110705b1922a27b85c14003ca01c5645be2c6b006e0d1c9f1caa6572c4000000),
  (0x0, 0x89378f49733f3b4312480a921f7c8d6578941651ab8a24b4b7572bab966203bd649742aabab63904561a40b30062737977b06d3a0e006db72e970d6e9a1ac4000000),
  (0x0, 0x824130618b3d2a806e6c89628398a9bb6556001e56313543854a9cb48eb698c0340822c08a9ec30981376197006a04521bba964cab006c3305453f7b2911c4000000),
  (0x0, 0x6a767689e5e3f84459812347f4da91d319d3366ad1739bf2d7d102602771542ae5f437872506664a2b94673006b3b03c27473476e006b46b36d9748b59fc4000000),
  (0x0, 0x3f59062fa06eb67b6764667e1d9aaf374fbe7340046b6b0c79a7846d11bc2c026f6706444fab90883f62700c00371e78992c139b3b006a2b7f4b4b1e4158c4000000),
  (0x0, 0x2b437c307317393f08bc56293d4e9f14bcab0b767a0648586c1039bf9016bc4c6eafa17b47a771a0348047b900baa8176b4c363b9f00698f0a5658b58c06c4000000),
  (0x0, 0xab101057b7bb3d2f93941c14b2a5b51f32b60a4315761947bab67e68b7169e3ab32844bd49a07b3d536c20780045b42b5b9872afaa0068bdba880a0f475dc4000000),
  (0x0, 0x1464a18f7b657a4674953db4b38c5d46220f876532519f79977c59c25c5b4d7a3da31888822aa9ac78ad0863009e7768128ac47fa40067aa70ac2d496c03c4000000),
  (0x0, 0x6d7db32a406c5bb393159a3d90572b138a0c540d1b1a4e456e75887b34b4639912c24005a05523aa859c8a23008c9cb07f2c6f482a006681371456503d4ac4000000),
  (0x0, 0x49451f4395c017305c06a4c1ba32469f6c44299685750d5e382a0aaa6f47395cad364d82951f9633b6abc26c0083931b3e776daeb100650d236c8c9bbb1bc4000000),
  (0x0, 0x21704704093e7a48a3bf1552699b0b7a88586889a8673b93470b91767127a53512908b2d90a9aa0a2ca943670075a378a16978a66200645a81b97dba344fc4000000),
  (0x0, 0x113f86bb20ab321c4a6b615e41bf0a2d09aaae54aca6b24d8d0000c4175282213c1d8b07a8b84d80ab4d2d8b00a63b707235c18061006329b89237000001c4000000),
  (0xa4, 0xbd9d8711273d49a529552db3be571b35a129b67128386e82646d2e7297153b1c399cc40054392f42875947008b98ac861277437d0064621d894da88c290100c40000)
  ] : List (Nat × Nat)).map decodeUCert12W19

private def sieve12AffU6C5W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x107, 0x169047ad6c01801709989b6d4d09002b098f2834913d5fa3758655888e3c318ebd409837afb16c939dbe5b6700c4188b81414060630061a0bf214f3f703dc4000000),
  (0x0, 0x9fb9a2b1ad903f87a6920a7600af52115d6128c067103582b61c47697c6c372ebca317786474b9300b7b996c00839bb1ab77249e14006004a8780ea97e5cc4000000),
  (0x0, 0xbe9e632ac0a3a5beb19bbd0fc043419b340d1954240255c25e2c8f9e53c06eba659f24390057849d9a7c2c23004f9768ad09b15a9b005f99752566993627c4000000),
  (0x0, 0x74aa77811a2c20149f8715358a46995e95490534a1764b1b58686f363e0f3478c13b2a6e9c4108731d33746300bab14e08ad862521005e93607e6c5d568fc4000000),
  (0x0, 0xbbbea66c56910e1493ab792834a8a1001e1786624177407e582fa9331e4358201494485ab20566ae46b0327800a37335c2566a1a1b005da72f7b6c961c92c4000000),
  (0x0, 0x7f8f9e0fbaa38a6627ad6050ac9c7f6463b7ad3d512ebb631600180054b27859a4b05a66416a929c558801b900b245476f892a1c26005c881584ae00ad00c4000000),
  (0x0, 0x22147e58ba867561a965568012ad332584155e39b8457a0764443269001644632c81660c814c2544c3aa5c0c002b3e413ec424898a005b2856386081935cc4000000),
  (0x0, 0xc2766957c35adb17402387bbd4da78d1201584ca54e3cb6070b4d317fa83504a553178ca0a9a0420e2a5573004c0b33c3604e9a57005aa70d9fbdba7894c4000000),
  (0x0, 0xa552ad1c67afab2a3e028b0738738f4286b829be0db1926ec26c06406d99bf22af82c22266b280ba536b699700165342561665741a0059bd916d0259bf85c4000000),
  (0x0, 0x991f9e7770219b1e93ba0c208e8c078c05c1b52670529aa23d7c6881672e987251319f0fb76b0c419bb634b3006c212ba42f42c0b70058c1800287495d44c4000000),
  (0x0, 0xb8a15fa7804a015208507d4567a845b6259766b10e7b50bb4a4d8659ae535b960c9a837eb23c49a09799c41400810569815dbb9e5a005768ba857a783f6cc4000000),
  (0x0, 0x42145695011a8a743e2f52842e4256b85a317e31ab7a809da886099136425bb82164971664b32343b6c3a25b0011876db09320110400567b440e1c3fbc34c4000000),
  (0x0, 0x721ab03695424e791aa5375f67092b81bc8b9ea53878480e20b6b3b3828a409c606b7e1c8a28a162ad63a00b001b8561669f6f1b0b005517ad75a40f1212c4000000),
  (0x0, 0x69b31e096e8e9f0e1342643b5cae5d2b8c529f82b7a9896d891c1a6bc1a05094088f976a2b0f9e06b8463d8100392faa662f38a633005413938f3ba9ab5ac4000000),
  (0x0, 0x112a9c88a98164720c4eb91892afc1aa690827a247172e38496670a4ab28864e3167bf311a896c3c2d982bb70010ac7eb12f5c3723005326b30c7b5f5521c4000000),
  (0x0, 0x384136a05c549d18c03b44070c0d4490c1c301523d50af767d6b184187b8c31db9978ebd48aea45898665b4f00a722ab5f6323160900529a7fc0475aad84c4000000),
  (0x0, 0x3e5faa4143020f2c5055ac236962b1155fc14b2eb90cb48d2d418ab22c5a932b02375146007b31330895899f000d4a6c56aa461e1f005178933697843b13c4000000),
  (0x0, 0x39487a228b9a430636a37d69b942c161189a3230339c8a110091a65f46a04bb7a52fa5174b95ae13c20fa87c001f5c7c7b49948d18005007751ac4341f66c4000000),
  (0x0, 0x55925c83088d7b5a423d3771383269b8238882985261b49a4b5a8a8f6770886e2c90504f575b52221a378a8200c333116499928490004fa60963796b3b36c4000000),
  (0x0, 0x58696f099614335a0c329b46af87326bba611d39b723ab2ea014c1695d1062279850c09294394b4515311852000387457a9fafbca1004e99498324b1045cc4000000)
  ] : List (Nat × Nat)).map decodeUCert12W19

private def sieve12AffU6C6W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x0, 0x681a92674c3c12a5065e073f2bb7757a78a6b2ba724baa93880923a487b11f40790499aac01e092b3c23904d006226570b2957a2b5004d1394bb3cbca221c4000000),
  (0x0, 0x2f3e0781b00cc06e71734c64c3882b8fb252540120534e97120d266b167e60b216828aa384af64a4c19510430035a8b8afa456192e004cb68c22b2b89f5ac4000000),
  (0x0, 0x85adc2b7ae35ac225684b92065a0332a631e55818cc01f62a1a7ba78b17281c0311d0c72083a5a115b3b0d0800b22b9b72a72b9141004b13bd2e231e0b4dc4000000),
  (0x0, 0xb136b48a0a6c5b8ac12e8e01b8426c535a63196c98625c9bc021b7a866c3bea3728ec1a40f1fb141107044390009a2455e91b405bf004a9e5f8304a40e1dc4000000),
  (0x0, 0x16743b41292163086013631391127e903e7ea45092297cbd25332eb975b59b0b2a2f563d86b26470115662a6005f220fa3a8434a1d00495b20ac9f92970cc4000000),
  (0x0, 0x306175563c9503724f7f56b4772eb43d128a7d1961b0aa37c48ab5382989683e303f458f6fac9852018eaac0007f6f287b5b8b0b9e004884a4be003b108dc4000000),
  (0x0, 0xbb7faf8e38784d41166d2e441e7c7f833d127a700fa6218123578d58586963307b9b3e4f9cae52ad31439a7b000a28357fb85fbca30047566c91a16e386dc4000000),
  (0x0, 0x7a25a229178a67516e927a395b9942040bb580a467b65982824b382e5653685a10c3b3c16752836a4c9a25aa00204dbfaa5f0ba48c0046ab557e427a8d97c4000000),
  (0x0, 0x991e6c9c5a2a8c301307ae984e6766943b7e133a7a5506429d0911c3b24eb22d180c036baab91276448f2c6e005c7d12b7c4763ab6004599655927bcb402c4000000),
  (0x0, 0x87bc152e86788f9d113902366d9a09717180871064bcb54ea2bca670143654318a7206af3603399021956b80003008c2069a9bbd3f0044a04fc422091f55c4000000),
  (0x0, 0x740e1818478b1f9256b153b1a4407c9d0c17636b5284345e6e2b9a6b712eb916556131c08b606613b9b134c300141259729796363d0043294aa1569a2b5ac4000000),
  (0x0, 0x7c1c267b2255b44e876595198527b35fa84b84b715b24d26421ca563481c9a2fab3b17a8827584a262473fa5001ebdb03a3a8b962f00425d564a82a92062c4000000),
  (0x0, 0x281a7b92a019933b112042c1377b10644a6a190588b1b3197b98138dad4c7c2b6f7b493f0c1c080f248a71bd009577420129a8a24b0041473793492db238c4000000),
  (0x0, 0x782f4b738570be5a39752f9e1c0959c2ab2d2d4da1c3443b675c0b9d160e1857976b192e33bb85820d9dc12e005bbf4a8ba49a0a1e004054c11a5d69ba28c4000000),
  (0x0, 0x829fa68854180dac3db9664d4c82074f143e038705161a190c7f0e20bf12a4692b74293432a3030d2c4130620066ac6f38198a2544003f275794b846b7a5c4000000),
  (0x0, 0x6dc1062a505b3d1362530b1a98688197a4aa3d11950c7112966f5a2d6180bb7a634f35bc54867bbc05705a4900b76c15396798b08b003e8f04582e566b98c4000000),
  (0x0, 0x78052a82b2afa8a6851cb206524524725964378389434a1fac127c750a834262a0095c5ea575ad1e0d067a2000be40850e8184b843003d008ebc18b34950c4000000),
  (0x0, 0x6d59be61b0b6b34d0ab9819076c4488077750b990d59a711b6485bbf6b0f84435a0a2086541f066b3f80476f00b20b8e3966742120003c0b33c30e7d6a06c4000000),
  (0x0, 0x2eb624a87460c354117e98a0a02e85167935b58917340b280f10995412b56103a58c02b15f56688801250b7e008675889db260436a003bae463db5b52c71c4000000),
  (0x0, 0x8107378e7c3f2594aa203b8091400956b8301a7472256a2cc30493287670c1395f3315b625197361664a0f2d005984686b85976d87003a12a45a01c1329dc4000000)
  ] : List (Nat × Nat)).map decodeUCert12W19

private def sieve12AffU6C7W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x0, 0x4cb82c94bead3ab09a6e3a55591f564d23639029356f1741a26f3abc066070200019a6780005a05a748ba08d00a7211192ab87437f003987b59c22568b09c4000000),
  (0x0, 0x8874938e58bd4837796a35668e2251bf699518af402c0f50099d8d09377a409f9bbca96f8f48907d0b7b4a2c007a44795c84091baf00380b5e7dbb2838bcc4000000),
  (0x0, 0x1306455f4219a363b103bc4022486e020b7b9a9e50393bb90d45409c44a5821a2d0063226f5f73ae4a2d5550002787837f8067771100372d48b8b7808529c4000000),
  (0x0, 0x834819211c17489d4911be2db0453465c2520514544a14a6ada10a449f01157a1159627c881994740f2f690d00499d4f8f7faa269100365a95081724bb81c4000000),
  (0x0, 0x3f4d545e2e532c6f28612cb29b815379873c347647564c425d80053366b4786c036c2a9fb088a03eb7ab3830009214b22b907388760035114b306745c092c4000000),
  (0xc5, 0x9a709780a5b62886964d7c91898eac695b208c3d64c048aa267bc300ba89660c567870ab4966a2347ea56f7b00a7727243526e361c0034ae7b2f8b3d640100000000),
  (0x0, 0x3db76228b991a2a48194b0a35f879fc3a3537841b163789f7ebda03d99c2772bc214ae8636291b73466a098c0068637d57b9931e5400333a595a46082588c4000000),
  (0x0, 0x2f20ae047c3c9f1a150321243ba56d46062a7c0d0036b60711bd29c219521d78030f3153ad937895a060031200843a408a69121fc400328b5882b3089c03c4000000),
  (0x0, 0x6f3d789f60569c5b0e23561412363cc170b870863d655f6ba502184d71a31c6c22aebd72179e10a89d6859a2001e51529e11353e0300318606041fc3ad78c4000000),
  (0x0, 0x422d06a463139f6f2525af9dbd239623aaa774173a9c3e2a966f2f997e36158655c1849599a98b3d4c6ab92600b98597bdb8bc292800304a24882e56962cc4000000),
  (0x0, 0x2858923422b84d6c5248b9401832940b9f5a303e42a8565282062e1d6e460250b66f747a0728157e97a62702007c4aae28a7b0a942002fae4d8042bf97a8c4000000),
  (0x0, 0x983d0a41aa7b315a548f62be4c53552dc1b777a0c09892bc2d2dc020a50abb2722756776b624393e81b32a950059019965184e604c002eb14e53979805a5c4000000),
  (0x0, 0x4b870e3e800389754cbdab8eb4948892100965762288c22b4e85936ab2ab3c3cab6e4f815b0329567a3221420044862ab2147e97ae002dc448977640325bc4000000),
  (0x0, 0x960494abc349b6154067605704a25e070da0715a712b26a46a144a5d41afa32b0d4f179a746b937c6121167d00596a2a34ae58b6a9002cb4a19d5ab17b68c4000000),
  (0x0, 0x6f6636bdc02f962f83869262130c45915da07c996687467d4f3d171e378c3c92539ab72d5a6c7756891b17a700326516b403354708002b4684197588aea7c4000000),
  (0x0, 0x1173032d5d2f66176595be1aa1c2ad47bb00c39130896849692aa4bf650389c3a89e32acb4521740ae89987a0058898e81a5640766002a0f004d5b9b2106c4000000),
  (0x0, 0x666eb0c2a714443d9e7d7a35267537470078213ca87a6669021c2c348532191cab8d0dc34653c029254628770041bc9ac4b077b01200294e7d48c2a99991c4000000),
  (0x0, 0x3d6189a68e598bbd09831a34086d6b1f566cb58e2044ad9462363b6a9f90b4ab25c2429eb143423b17aac4660048439263996fbf300028a04f9d628f8a5bc4000000),
  (0x0, 0x9b9271331b2226214012b09f6b8548744b8e71866b72523b131d988475118700623e7b4a2c1c629c27b078830038bb7b1a932db17d0027205868b1a82d41c4000000),
  (0x0, 0x50471e5b800d4c34b36b0d707fbd663ca43810684d3ca3908971147a37069c6601ae292b012b4f32b4344547005435236b419c175c00262e67283b54b14bc4000000)
  ] : List (Nat × Nat)).map decodeUCert12W19

private def sieve12AffU6C8W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x128, 0x7b1a0c889091bc40060099a816452136081d8276044c53ab00637f04c4b5a6a49c4397189e7aa7647479141f000cb113bb3536b1b90025823214006146c1c4000000),
  (0x0, 0x642e3e05be67718d9545014b223dba012f6c087f82974e5dabc3596e577168488330aa5e4f49065b32794fb1004908206c8c7974770024297e0119026c57c4000000),
  (0x0, 0xb3422d7d6271800e96bb41424c9e3e1c25a9414d545632ba27717b10b4758f2e5056c2b4bd05b15fa3062a5900090d4082940eae530023b7315f9d544ab5c4000000),
  (0x0, 0x9dbf11b0b2703f5ca819947977897e35a6152d47416e30a93c64638f7e909d1880733e785824b47ba64427760066b2931a949e777e00226ca87188616236c4000000),
  (0x0, 0x2872433b5c3818b84b4eae2f9283b52e201508306e7d1d409c50a5b25f5b9d83060b6bad15bebdbe82951d45004a44598b1e6b0f5e00210d4c4d28752013c4000000),
  (0x0, 0x2e1d3265970e2bb5ba914f84bab304af45194e4213b3b983bdb88983826d5da74c0f6a501d1b773507a8c4b800be5249abab6a083c0020723a34070d3c42c4000000),
  (0x0, 0x10c38600806e5a10166b496a4e91066357653b9eb74dbd08745aae8e11aa5f69aa2e4d428cae6d10ac96085f00c17e723491766851001f784d4f506b1737c4000000),
  (0x0, 0x712f7503bca064021f821e07667089553e754509997744ab7a416c7c1e840a4b788171499493167249b8bc32008b20095179a05440001e4b8a3f4a845949c4000000),
  (0x0, 0xa636a42c5aa1a07abf6f816b629f74bdb59f4ba0a3b1b2a18c353a31813785035a2cb382477cba05b2ad80b4004281934449713b49001dad7e4838908b94c4000000),
  (0x0, 0xa42028267b88beb4271f69736c9657400496879e3033afabaf6054314e4a399c0365092890ae61a091ac64b0003da4a71297b32799001c6c605715657194c4000000),
  (0x0, 0xb6437e110680927a5ab6c366ad4a19060553bb7b6c72a725b7af679e1342416d82bd11acbc04b25bbd9d9d3400376198537e95905d001b4218200d165e27c4000000),
  (0x0, 0x8422b59c2eb85b1ba0173246a192112fa1a6a97f5739544005a942b7ab6e561c3aaebf85434c577d3a7c9e9300403a074870b1a159001ab54392bf1c830ec4000000),
  (0x0, 0x498f382e94c486bd4f5ba503226a379b9eb98fc1aba3bc1dacb88bbb847b2d8079c230863a5d00428962b64800b15d6cba3b6b30c30019b93aa9180d3a0ac4000000),
  (0x0, 0x24bb38078b472100ab1483c667a860fa40cad2a773315758f214e2f86a2010619539dc1050357247450179800b294692475222d50001812386135a47796c4000000),
  (0x0, 0x1b8ac1d7dc1957857395d4b4ba4b90882c2632eb8ad3d25897fb82f621ca740b6b4875db202c434341d2a050018af74353e7e50980017c00ba43b460d96c4000000),
  (0x0, 0xb0435e1ca974162aad2e2e059e7691a46130200a6305bd6031737418099e0f65527c6f4f6a009d834933176a0012b31a8d2f6c3f8d0016a424b6935251adc4000000),
  (0x0, 0x364554359aabbb740789d741314a402351dabc2375881a5c2ada98f068f3b2223196dc1524b970821c2295e006e6c3a88c3292c0700152ab03b02181c36c4000000),
  (0x0, 0xa5999101c38e777577a73c263f0d21409652376aae54c16eaf24682996bb34a73d90321d8f5d007888c41b0e00589b327a20901860001470068e15a15d9cc4000000),
  (0x0, 0x1a35bd4c693a2ca30ab973894c8d34366f9b435da85aabc12f9fa3b03d1da16b7c4434338e9e1c1a707f605700310c20b3b64a68b800131f768f95262215c4000000),
  (0x0, 0x4f26bf471cbdae8a24af70772382052d234aa585874398c234923c6f233d3214246a1349a55c43157fad0c75006bbc21132daa302900123b110b90338956c4000000)
  ] : List (Nat × Nat)).map decodeUCert12W19

private def sieve12AffU6C9W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x0, 0x6e17044f4a8335a326c18e19670e913f445046aca03a28035813457785b9c39975b26f548b329d14a3ab284e003a5d4c245219483700113c533f6cb2804ec4000000),
  (0x0, 0x9c0797b08b1c0d97a74425bb232e940008039317bf12a55e693358718d2ab206247f88ab81aac3257fa559910054294bad769fc0780010035a4b5b926d54c4000000),
  (0x0, 0x67ba0e835e2a0372b63f100e492b320640375f1871499d396ca8c2654b7385bfacc281240d935f5e96866303005ca3688f0c149780000fbe8f62581d0360c4000000),
  (0x0, 0x8a1414b5395959c4aaa0683b42a96aa5553f76109494221556b9068354177c67290390912ab21e6f0d6c777100126a861e6f377b6d000e416a576e0cbf42c4000000),
  (0x0, 0x7a8895bd4cc05c84633b88777663bb22542048823385b11592873e570ab2999b2fc3897604be267b282122c200687ba033ad1994b2000d488db5323e876ec4000000),
  (0x0, 0x6853b87734992bafa25d485a165d308cc02041bc76bf5862060f03513d883760bc1613ad945056b1663389110060728c48b400b7a0000c54398fbeb6c274c4000000),
  (0x0, 0xab319d4369c473b783521d5e0681a35c3b8f54b6934286542f9639276237642f08993e776f3331366d17441e005c4d3b55b32abf55000b409b72952f8c9ec4000000),
  (0x0, 0xc2c11942a89bb9b889966b0386c4284195451d9db621695ec33780ba7474c0bd076307405897608251543f3800b62813303e3753c0000a627991018e450bc4000000),
  (0x0, 0x12a53578bbbb7a3a2503450c72bc6ac312a5c2682ba396497447b272586e72bc11872f46a55fae1b914d134a0064bf4940399d755200096f3986507e1353c4000000),
  (0x0, 0x3a77647554582d669f3f22670c68597b0f3e385f61880879afa2a96c69694a2e533e2d4795632682bd5c68ba002c0eb4c0a7288d2b00088d69b915231c59c4000000),
  (0x0, 0x9c07c357400e65149dbcc41e354416109b5c7cabb69ba467814405138c3b81905b38164d8b1370a63c46663a00112a15178daa2115000798a6504381c0b2c4000000),
  (0x0, 0x1e5a3f8054831d501bc16b3181448c091aba8aad628286138448053a778384778b6a3d46a73f3c0f92965544004b01b522c058467b000688b02f407dc08bc4000000),
  (0x0, 0x8ea69e411d5048ba89034954308e9701a75f30732d16642e185300506e3b8949263f23810a35225d05baa91b004043b3b5bc8f10bb00056e4447ac720075c4000000),
  (0x0, 0x120e5cbc8022c1c43e589f7e76692dc38c085ea407553c156585b281439e5b122164089e223717729c9e3c9900b48269c431be5a56000479098e5f401344c4000000),
  (0x0, 0x3c9189704a2b5c871a785c5b2885b0b62e57ab01b7b969bd8e01c40fb658286829079736774283947ea7694b00a371034d2ebdac3100036112a236c401b6c4000000),
  (0x0, 0x223c46105c0c378b88473a5789a12c1933405f79859b3643166f97a6aa9e9c8143885aaf45a46e2d89b0b7150023775f79b5ac0fac00021a3376ae562e1fc4000000),
  (0x107, 0x53274a000000a8a08a474fc3b2ab008f128950c4000000002000000064512509bf3b9a46544e58b39c005c54002e963eac9c001c930001000000a4000000c4000000)
  ] : List (Nat × Nat)).map decodeUCert12W19

private def sieve12InfU7W19 : List (Nat × Nat) × List (List Nat) := decodeUCert12W19 (0x0, 0xa0806030a0901090701030a0c06090b08080c010a040709040707030b040c0203060a0c0a070c08090900020001050b0b06080b01000c0609080806060a0c000000)

private def sieve12AffU7C0W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0xa2012300c5014601280169, 0x104020a0000070a050a0a0a0009070200000c000002020004060c030b0c060a0100080a000000000000000000000000000000000000010000000000000000000b0c),
  (0xa400c50127, 0x90108080b0b030c070901060b000002080b040107090906030003000100060b0009000c000905010002000502010b050a00020007010c0b070902000300010c0000),
  (0x0, 0x20302000a090c0307050c020703090c03030c08020c0306090008000c010c030707060c0a09070403010a07000302050107050807000b01000b030005000c000000),
  (0x0, 0xb020c010904070006060002070605040407040600030b0200060708010106070206050a0c030003000607060003050b0809080209000a0906070c0706050c000000),
  (0xc5, 0x805050a050b0306010005000c0202060b0a0704020405060a0604000b05020c0609070b0b0403000300080500000b080400080308000909060c0604020100000000),
  (0x0, 0x7000303020101070b03080a050402050a080501080105080b0303090c0801050205030709000b0804030c0b0000040603090502080008090604010a0a040c000000),
  (0x149, 0x804090606000606020a0b030a0b000a050a000b0900000000000001010204040809070602090c05020707080004070a070a01060b00070409010000000c0c000000),
  (0xa401280149, 0x9040b070800050c000c070908040901000c060b010b04060606030a010006030c0b0c000107060a0c010600080a0a0005000a060002060701070b000201000c0000),
  (0x0, 0x10a030309070a0908060508040000060c020b0a010004070908080b090c070904070308070207010909000b000a04080403010b0500050a000c030505020c000000),
  (0x128, 0x6070607080809080100090104080a0a080800040b02050a00040a05090a07070c0108070205040b090b07050000060c0604050a030004020002000803080c000000),
  (0x0, 0x7030b08090a040a00090109070c0202030900000b0101020a0c070909050500080a0709060605050a050600010a00030b0c0a0400030404030a0301060c000000),
  (0x16a, 0x30c0009060102000c04070708010b0b060c040c020a0b04040a04030a0802050204030c0209020b090b0b0700070506020903000600020709080803090a0c000000),
  (0x0, 0xc000000050401070404030901040b060b0101000000050000000c010206060908060a0c050109090602000a0807060909080c0001000000070000000c000000)
  ] : List (Nat × Nat)).map decodeUCert12W19

private def sieve12InfU8W19 : List (Nat × Nat) × List (List Nat) := decodeUCert12W19 (0x0, 0xf5d28014661322a0d4d59661c453c0f013a3c3b0c5c023a66092032244c5b2548644f105448425e49372e57002058214619601d4600660a1f33005e473566000000)

private def sieve12AffU8C0W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0xa2012300c5014601280169, 0x5b50376400005648323c24640011060200006600004f0200566166243f18333c0100341f000000000000000000000000000000000000340000000000000000003266),
  (0xa400c50127, 0x839624f21175e273d453c06650000402953222c082522320300630024405f65005800663e4e0001002d0026571b55626400270040466607210a02000e0001660000),
  (0x0, 0x216145624d6010522c0739355e5c62515e43445f5e2c350d1e24555a4201654f46005f451e643b4b04463f63000e64402e0a215b230065404c614843120d66000000),
  (0x0, 0x5422322234601e1059300632504c443b201330233e3d2d295f37053d3a3547655f134f484f1446462555522c001b654c333557515c00640806450730622a66000000),
  (0x0, 0x8295522554c4442492b5728393600171f663b0f0451360621370c4b27653c0066433c0d2e5f05604f0455660044100f512537384500635b431545305b1c66000000),
  (0x0, 0x10531f0a2c161124161d5607562d325e340743300f354f54344f3c474e312516414d31652d5255524f011d5a002650211c2837620e006228536432182b2066000000),
  (0x0, 0x36323354546418316024190c401a1f31092b1c102c3d56581b61600d295b395c32550e25564965312f2c4e0b0027505b4246390b2e00613d24124b06075a66000000),
  (0x0, 0x1327596136615916521f463e62485e3c401829010d274c03573a16440e260c295b61523e293e3c0b22372c1b003f3f3c2057065d0a0060464c030f2d512366000000),
  (0x0, 0x1452d07341e224c0612532d3250381c1b5c161f5e59354006470a2e2d316648253625594d6208245c2c114d005c0e182218174956005f07650960205d3966000000),
  (0x0, 0x71b11505e335c3d2a0f0845562f4d105617282d5d4245602b1152192860115b134911252c3244493f3238550032420023185c0841005e3c2b3b3b56154e66000000),
  (0x0, 0x163737423c115e500123574365654d4030620b2b23211e4b192264310523220e1a37291663605e3d4437554a001830364121064107005d040d0b4d45033666000000),
  (0x16a, 0x5f1e003e354362145c4d240a5017611d355636384b5e1f52085d5e3155612e4a0d0c1e1d2c5b43641f313216001e266314230e5a64005c3213395e0a093666000000),
  (0x0, 0x632d0d27322615180254004d420540480e6444453d4a545c5f65101d190000621a4004493f0f55182e404950001014342e19535017005b5d484c0702574a66000000),
  (0x0, 0x3e320f581b353f494a4f2e412b0e353b3b45143c054a49660c250756133e026358161219542e5c3b3d5c4a06003d1f5f4b5c015a2d005a2c03335a42601166000000),
  (0x0, 0x57405e541e1f033b3a1f3d3157352a170312656337611303185d465307271e2e3a2049061c2c3d09143c6654003d063f340d64220500591936454e0a211466000000),
  (0x0, 0x2654551646614f3f190e413d0856454d1c4e2c1132271631514413131a522f360e1e651404454f1c1e113d0a00220f363a4b56332700582a0b3c1523545466000000),
  (0x0, 0x1e5a100d544e2448062d5a473d4249173e1d544763122102220145021e5b0f59231024645c195c664e371b2d001a14322b564f0e2b00574859174466226566000000),
  (0x0, 0xc4d453a124627125665550a320a5d5f0d650362396410012a3b2c0b0f393119113638573a57181f0556152a000d2a072537312e5f00563045203c2c3b5c66000000),
  (0x0, 0x3e45035a321b1d3a5e642638593d153a02101356042a5335155a5d336259541358321d430639173a09154b2f00374b5f4b53255c5400554a4917510d0a3466000000),
  (0x0, 0x5d532d14531f27301f13114f52600d5221031b65250729404c3d524745403b423d1f5b063e04265906500647001d19131217475c5500544c52081a2a152066000000)
  ] : List (Nat × Nat)).map decodeUCert12W19

private def sieve12AffU8C1W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x0, 0x594b5c58592859425a2221165e234e4864142e053265474d612635635d2b580703311134560f0a5756333d46005b244343285311370053112e590541320466000000),
  (0x0, 0x27093b2a083b115b204721574a605448623f6117641153181663623658404c2e1c3302583b11253e1c140b03001d5936203b41054800522c0c145004053166000000),
  (0x0, 0x3f431b2a05003d532156491b3f4d5402511b0f562d1b1c194045630f6011394b21660410540f13300d112039002e421a0661153c32005122464e2622045866000000),
  (0x18b, 0x53391f5429401d250f21226208041531572a4d19362b0828390f48394f09050d6500653d3f57553c1b652b00094e5e47352e470c0050124f363e2e581f66000000),
  (0x149, 0x5b161712005c3d0a1c6211395b206647365c4e4140063f19501f37382033024f30436612485718592f1c1400065d4808221c613f004f1b10294e17483066000000),
  (0x0, 0x1d4d493c102f58105a34643a023d5c074453284e5a624c053e62662d3d4b0264552f413c551213591a31405600553a32485465362c004e300b332805013a66000000),
  (0x1280149, 0x3d3f203049002a0400190d2915362b50010c394e42150458101d18492b3562291a57125a0259205c2d462b350028583d4055004d4a004d285f0f3e494f1e66000000),
  (0x0, 0x4934475a1d1d3b494e3c53015825291654110b386404595c232645050c5c386122353a0a2b5a462319475a65002e22181540080238004c0958554341226266000000),
  (0x0, 0x2a0d53553330244e0037041b1d580e3600381e562a0b1714193e664e211a533717012d66244e00514f0639150007052d0160101436004b071d234d29011966000000),
  (0x0, 0x3c3d16521c39224e41441f6136342f04440d03113345133f304a0039300a396302454b4c3a13562e2c36636000310d532e13635e4d004a373856361d002e66000000),
  (0x0, 0x19265448193d5d4b41280a653c592b605246645d2a43560a2913282a66354a190530454d654b3a214a3f5c36000845010e02291a470049435f203d543f3d66000000),
  (0x107, 0x622d38134c12052536405a201a14002638612c120b3a3647143904524e352e5b391c232f38380c0f07252430000c66483004333c5200481a4c0e522e631566000000),
  (0x0, 0x51002f16490a643d385a21064a2e405327525450664c5008470a1f3635422a073f3a1c475d440331295b3d2500554109201e003b4900470535551f5d483166000000),
  (0x0, 0x4c24212f285e0615353b5f535c3c013851360627450a05580b3c01063a0861551364102149091a20621f545e000742501e0644196600462e3a185b2b666166000000),
  (0x0, 0xf5a111a61391c383f504a3f1751274d0b1e2d5e505208490e185701363c234b561812510a3b31366105633e00221628155e121b63004562654c584f106666000000),
  (0x0, 0xe403f360c233f4e57624d626339534b384f48360f1c4644444c0e47065e5c10424a2c180a10495c5d583443000d024d5f4e5646020044151500221b592066000000),
  (0x0, 0xc49175a2e3203200f270d4c463114440d5946604a542a04282b302206146640334d4c20650d1d0f5c1f0b59001e4b1d1e5830112a0043200f313e3c374566000000),
  (0x0, 0x2f5401570726333646621b183c38581142192c22342c350c6215111508521a025f16374a191f44392832404b003037265b5f2c5d3400424b2b350452565266000000),
  (0x0, 0x82b042b2647021722154c460e5d2a0836241928213914144e5907224f5463492100650938005c6364212b5f00530744523109225e0041032d0c180e604566000000),
  (0x0, 0x4a0e2e2218251a2f4a5a062b24575724402b1f615223521a094a2b3c4c613d27023c351d015b5b54443d1e230026102261371d040f00402264285d1d3c2b66000000)
  ] : List (Nat × Nat)).map decodeUCert12W19

private def sieve12AffU8C2W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x0, 0x1736033f253a19060b51041b5d4a1b2a414f16255234001352633656283e3221382f175d56265e2f33584f450020202b0749011b4f003f5b421a1404311166000000),
  (0x0, 0x2b1b1551175e595456245c01081a301f5628273612361d2426592032421408083a4f4c4e0f5a2e1e5d2e4e0c005f523f240d11293e003e47334c400e473566000000),
  (0x0, 0xa375e2f575b271c331432373d431e0e0c1a1b421f1a53472e42364e5e4749184f5b371f512e4922583f564e0002173f08461b3a24003d1e242c3825311966000000),
  (0x0, 0x4c5f473165425a56440b0e2f1f425f6517176317620308420333322b1b3a2b0625590316196541153e4648410055186218525c6510003c33614a6334353c66000000),
  (0x0, 0x60130d34320c1b3c3a622c3f49224461452b3d3a4f23570d423d0222425335314d5005665d500538013e4928005e45535a0d303919003b10454e242a654566000000),
  (0x0, 0x2808152f135f5234133a3f322e28294524531e5200280b1f6119034a491208041a4a5e3102625953154255180035620b5e4610420d003a104950054e641d66000000),
  (0x0, 0x2e483f420a5f01541040192d255a0b064f21650f470961202346255d4f15531404440859183711623c522b5800484356282d5a4a0600391c634f4321420a66000000),
  (0x0, 0x383f1957455a024a13022c1306180a3a142961045248632025514f544a180217424c5d083562243533052f1f005666025d145c1d4c00382f26544116181366000000),
  (0x0, 0x3562155a5c2a0e112e4614391b3e485337141b55022218406163024145462c5e60204a5a19563a581d4162050022214923014946530037525a640504652666000000),
  (0x0, 0x56030362358515f075a12163d02295e484c350a244b2e28364d1a07142f1e623f0a194a6048284f5b2365330027245a0a5956294b00364d164e301a4d6066000000),
  (0x0, 0x5a3e4c1f291b5d3d5f13603b615d3d592737334b132c070c365b0b32544f144f325d4704192b0c021b486349002e40251e0a49651600351c3740300c5c3566000000),
  (0x0, 0x1410383f1c36581765550a183f470165250b1339071f47382b00001035084e043027030a072d0d5a3d62412700554b565b2621394200340904603b00005766000000),
  (0xa4, 0x470b5b0c45566431164e6119312502475e614a5e4d265120545417010b370c62071966006201092a471f0500270c2b480d27616100253350520504604e0100660000),
  (0x0, 0x343a1717013761415c355803591b550733012e47091d1318171b634e4f58025c382f0e541f325d0463284e49004a0e25540e5f425100323353184f4c041966000000),
  (0x0, 0x314c0944573c341a1a0d511b0d2e09613d28204425010701221c1e0f2139461b20523f4e22242e3a244e5e3300344f0e063017271c003122092a444b495866000000),
  (0x0, 0x4b1d420021333e1623461f455f04436142131631560056014401324531170f475f35484c525d44540e5d390500164b0c334f0a481400300057332266352266000000),
  (0x0, 0x4b034f0a150a5a421534493662620833401906613e5c073d43445b346214461a5a293050361f5d180533311f0066013149423d601b002f014b2023230c3366000000),
  (0x0, 0x5c4346224d47283604335d5849542b4d1a2b4f0d2a0f35220c5a2f1902200f4a5253524f074844425c4b2958002924251742395761002e364c655a0d384e66000000),
  (0x0, 0x1a25142a0a134334593842030520215a5d051c200726214421652419213a3d0e1d2b33050d18203b641a191800233817561a510f5a002d173c104502434e66000000),
  (0x0, 0x145e251046026341593f57264f031d592e291b4b22134d1328433b17272621042e63065d201f5c5530472c28004e3e3a1929494a4e002c443b523e242c5066000000)
  ] : List (Nat × Nat)).map decodeUCert12W19

private def sieve12AffU8C3W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x0, 0x532b5c36623c4b343c3e133724183d403c2f271f4160463346295233294e35064a430d665523111759094041002e0b242930142757002b38265f203e153466000000),
  (0x0, 0x42661542494630320a0a092d622062462e06302229434014032b5343393f102e4e525529053e1b1d5024644e000a59163a331c5b43002a49450d633c142466000000),
  (0x0, 0x293010325d5a3d202e4a010956455c531106262318582e084b32554d1d09510e2b4e32554b3a1a225731040c00372e5546503b622900294443051b35121a66000000),
  (0x0, 0x419363212282b5d40411107224e132e23322e0a4e564e2d152d4233545d31643860292f414665523204014500252f5237106113180028460712513a253466000000),
  (0x0, 0x3157184b02364905231d352b062b10105756145f4439425f4f3b3b0805173c102c4b0d094556610c233d542300233f18113a370e5800274a2339172c2c5f66000000),
  (0x0, 0x3613744473e3a0f02603134462207022d59604b1b181550440a37611a243b413442422f1a32500d2e0a2a5f004c4215000811500900260b0b40225d300666000000),
  (0x0, 0x4d2b5347142321250a0a5d075b12310e50395e0836502a2f603565032643651b303f501b652a654e0a44584b00521341040e07513300253729150632026466000000),
  (0x0, 0x55430e094f643b631b4951490d32634c103354361b391e0c19275d26384a3c074f5a4d47124c1d663f420b5900055c5739563c533d002425615e4d400a4166000000),
  (0x0, 0x512753181a3c27452d576006372f4466565557142b1e3f23345f2c4c2b2b105e3f3512433b541916221f430016250f075c0d2e65002350310e4333083b66000000),
  (0x1280149, 0x23394a3254002922001e16560f0955160812251c4f442b521b1a5f140006621310572a350f3702601e4d463e006666305a226608040022611a152e4c085366000000),
  (0x0, 0x374d204025420966550c5a273c1a055c27424e3754424d13655f161b63661158490332480d3c645b4a311f5e00093b283a633d3a0100214c5c120108514c66000000),
  (0x0, 0x152018593045473b604230131d6563574a3b46194132251143605e643a612e1e224e382a5a461b6059094b25004a33034a533f2c1e00204312112307090366000000),
  (0x0, 0x50191620202120302d2f5141093d24331c6313014c3a0e4206234449460652143e0e283261300250081f5b30003961146512651315001f0d39046044231e66000000),
  (0x0, 0x610353033b4c2612590b1d0c1e504e59243a2e4a171a121e1b000e00253d1104624c083920450b6052130d3600641c010c5b091f20001e4a1a644b00590066000000),
  (0x0, 0x4e2a441e412f452d336109180f465b174726660a514a554a0611382751573715292f50524a10143c143435600004365838425d0f1a001d66385560562f4066000000),
  (0x0, 0x1d0d4c61501d5f2c4e48523949124a590154304939343f53605f0462510c3e414600480d615f023e3b462215000c474f631e025f31001c393f5e0608630566000000),
  (0x0, 0x4b5c1865303b4613140b572d154f28164a42181a33245b4d272e292b1f340b563f4f1e55370b47563741146500511d403c123d5f2f001b4543463f393e3c66000000),
  (0x0, 0x25602b445e2961460f1e0e140d493955251b0a31471a00022d595e1e27130365445b102a6420094c3f433c35005a324f265c614d1d001a09093c390e094966000000),
  (0x0, 0x38196431170c114841204c023f3f631d615300010c5510345e12594447171f1f42032c505f192d3616454b5600280108035c1c1a3b001948402708550e2366000000),
  (0x0, 0x122a1d490c3703151d58150c0318323e3e2a4d13433459112b07154427232a053e1266282b594b2914233f140028364018063b4928001851021f3b60522366000000)
  ] : List (Nat × Nat)).map decodeUCert12W19

private def sieve12AffU8C4W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x0, 0x3a480b643e13395b630b6260582b2f542a252e0f5453096214582659563f1241383619295e09621c1122182b004d373d010546605b0017172059520f410e66000000),
  (0x0, 0x3f2e043a5516044c24323920183c06362d5b30470529434c344235381e59175b521221053d533a1532176539005d2423634a120c3500160436053225322f66000000),
  (0x0, 0x2b282f0b432e13234a164f5e5d361b0d3b1e631a510604371a4d190c61455800345d2d1b03242434512b5403000905400b165a5e1f00155620024c1a4e5b66000000),
  (0x0, 0x5c110d241e3e32115009462261194765302f3e3c5c2712294e1b0f4f032b3b051f08412d452f5e633b392746005d2e433a19170c3000141c3700184c581866000000),
  (0x0, 0x13265b593a5b153142470e190e4b4b5e1e5f58103e1d1525544f4c11563851074d58630d5e0c3015170b3e47002d04602825061c12001358184e12181b5666000000),
  (0x0, 0x30293e291835320f415c63304059151e1d24032223424e1b0b5b5e3234384a63053006520e4126225159252f0056543e24333a361300126301175b0c093566000000),
  (0x0, 0x560231114d1a3c2516535b281b051c115d15042a4b296303053e64361a0f575353490b32374a123131561f2a005f50593a523e330800112d1e4a6129033166000000),
  (0x0, 0x5d400b1012221e0306174101274806320e1a0e264e145d280c490831112e0f4238106420102e0364510f022d001d170b1c6464573c0010435f1d5a1e5f3666000000),
  (0x0, 0x2c65270360300d265623145831230c37565a130457323c5a2e3c41026523455f35393c335d452f4d0e162e0a0061373b5827653840000f323244382b266566000000),
  (0x0, 0x290f5c1e2865503405581c29314f244727454a624757335636610e0f475d5e5a08180b5c5f5d412635666054000f48371509453b62000e590c133006595866000000),
  (0x0, 0x374a355b56122b12085f5f660f6352470d0523643b3a020a424f495c642008633655270713230f5162274306001c5b441c632b0b3a000d390f4b24181e0b66000000),
  (0x0, 0x3a061128071c1f514820165e420c02325118513f284c101d5d411363351f282e2100015f50541f514d21495000225b004b485f1450000c5a502e0926540466000000),
  (0x0, 0x5a5e082329565a104e2b5b5e2d5130565529190a0f0b2102552910655614300339035e1f4d3809344f07391600396416264e461903000b391d0f113e570266000000),
  (0x0, 0xd210d176445462f0911420360633c5724000631430b3d0543643c2046133959475c45515b182c215d2b264a00325530091b250d60000a452d1d23032b4766000000),
  (0x0, 0x62213d234111451a2903394c2a12561d475140344d1044266345042e3a2d55016125181906243a48316405550025351a0d4d331c2600093449300322633966000000),
  (0x0, 0x59343d5a054e300b0f115a251a1a161d08560719252c625c41445235463d512511512b07313d63080e34574d00311a2b3d6009051100084800242523153266000000),
  (0x0, 0x32566315292501265f2f192428384e43223664632b0320270c39292b032c3d291d44540d4b0c3f345353451b001d5e3f3a34620d5d00074f1e1b5a2e3e3c66000000),
  (0x0, 0x39121719631c074239434722440a3e1a64411c404b2b0a664e292549123615584d041b03071c5f1410172c0b00332e082c593f4839000623614c183e421e66000000),
  (0x0, 0x2b346047262113485a4a3f3446280e08664d04585863051d0c3026501e61642d06262444362f245d4f51445a005d204758592f2c590005243c295a37411766000000),
  (0x0, 0x46550e4e4f02220408283348091138655201574143161321373e34560363481f3a2c34103e04600811253f66000f5a1a144a04472200040305442f29331166000000)
  ] : List (Nat × Nat)).map decodeUCert12W19

private def sieve12AffU8C5W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x0, 0x210422223a224e2c5d0a5f593a4b1247074a2a135e510d1b605a0c232f4448035045582f4841414e2749162c0040312b2b2958040b00035b202a060d5b4466000000),
  (0x0, 0x494741311e3d2e27384b362a63324f5c0f49604755513a3f32121763160c5e492503175e3500075b0c640563005a0a36184d40444400024c0f523455500466000000),
  (0x0, 0x5b0d30000000083838491d1952153d55344c1f3d01000000040000002a5d12241d362636665222332b4b515700015e64532b4b1f2100010000006200000066000000)
  ] : List (Nat × Nat)).map decodeUCert12W19

private def sieve12InfU9W19 : List (Nat × Nat) × List (List Nat) := decodeUCert12W19 (0x0, 0x42708001a3e3d20310f3d2a1d1723021d173e0b2b270a09420d3438403c1b26340e2e08133d221a02383938000b32350714161b2400421c1f3f00360f0b42000000)

private def sieve12AffU9C0W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0xa2012300c5014601280169, 0x1c3311400000180820383240001027020000420000380200331c42390819213801001b0f000000000000000000000000000000000000170000000000000000002b42),
  (0xa400c50127, 0x240f3e2e1b171f16342d1b06410000182b2f1640372c032903001e001d230a4100090042201e15010001000e381f3d1d400022003424420b1a3b0200390001420000),
  (0x0, 0x2840170106050035040e002a12142500101a0e263800010a1a2c242916002f101c023a113c2d3410290f060e001e21413e070316120041423c3428171f1a42000000),
  (0x0, 0x11413c37343c3c1a3a1325221f1c233b21112f3429080e38133b033e27341515081d16252937352e0a2d1624001f12062f1f081c0c00400401122f08400542000000),
  (0x0, 0x73d0d3c1f09243818051a131a2f2b0041011c112e18123c41170a1c161f33291f18353831113e1a3c420f25002f333910011b0509003f321241012c392742000000),
  (0x0, 0x133c1017084031191931361b2f1b10042121270d050c304026110a1416152123320b0f2635363e400e2a201500051f2f2d240d1f22003e200b061c32392f42000000),
  (0x0, 0x1e313c292404211d21060703121c40284119050b19241a1134203b214232410004203e272b411a0824043f09002614250f3e271206003d39052e0e23082242000000),
  (0x0, 0x2c02150b3c34202d1b3e331a1d0d1c19172f00400b0f2c02181b0323112423000b1e422f34052b1138133231002b381a313a0d0035003c291e0d2a28402042000000),
  (0x0, 0x2a3e052402252e1637323d1a2b10233919103433360e1c402e171c2c30030c2508072217240c1f3613321a00021c17353e150d26003b08112502152c2742000000),
  (0x0, 0x1e311f03100b2d0e0b3a324230290e3e133f3b1240160a2d092d12250d2c212309221604310d2b0703223b0400150f330103162304003a2a290b3916311e42000000),
  (0x0, 0x19194209211a270d3e29422c1b1b2d120c3e09022318071c323c0b18192a410d0a021e0315262d0a04304216000f361740253a1b110039221b0d1007382b42000000),
  (0x0, 0x1f231d3d3c3a420b260e3834231827150c1c3237061d2110173f031d3c42372c3c16002811273e32160716060002273d12300f373400382c293c2b04402642000000),
  (0x0, 0x36053d42092226084224102c322a0842421431263f3804172c003d001f302d11190a06360e0d25310f311113001d410130151b150300370c360a1600060042000000),
  (0x128, 0x400f361c34243c200e003d071e1c06162a1839202d1b093500053a363f12281941390633211c3b2c2c3c200f00213b2e122c02342c00362f1a00003d090d42000000),
  (0x0, 0x2e03271731102f2517080b0e2f181a2b1e023601232535163f3a24173313260d00111408211a1d01372b021d001d41112f2c403d3c003507201d03091f2c42000000),
  (0x0, 0x38043d27212b1a3a362b402d0b1a1d083b3941292e08050a04360d091d42091a333c403e27240e311a07302f002e1b070e023f38380034141d0e3e0d363a42000000),
  (0x0, 0x3f062a2b0116394219072d2110270b331d11310521283c17004219263b0713283440073d0e1b4218021b2a28001219310823000613003333061642012a1d42000000),
  (0x0, 0x311608310f352e30270c353a120f04400a2c410139060c352e0f081909080835013d033d1e370a3d262b221900203b3f201f24030a00320c281c14343b2a42000000),
  (0x0, 0x342e27390c31013a000c3f324010303928180b02032c262f0e19270f35181a003c202a390c232d1f24240401003e100c06002133020031211126342a1c3442000000),
  (0x0, 0x1e2908262f3c1d270900191f2f2f1525390e370707402b2d240b2441260201392f38301007241d22302b34400015120142060638100030202c1d1e381f0242000000)
  ] : List (Nat × Nat)).map decodeUCert12W19

private def sieve12AffU9C1W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x0, 0x423522271841290e261c112d0916403d2b113c3f3f041b3c1c2b313c01400505330a24220c05160e20332027001e013b12052d3e2a002f1810092618120742000000),
  (0x0, 0x2a05413542151d2042332b193c013417153421222b262a2d32203c28233b420210121107062e2a362e1f234100233b1329411c0d28002e2b1a011023071b42000000),
  (0x0, 0x1f361f29170c1e2d10121d282728262935353e140c044134210c273d2e37232b333f131e2139200b280e3123000711412a043e421a002d162e0321371c0642000000),
  (0x0, 0x111011161c0c38121e360042181d07240f23211d103e3a110341162e350321153d2f1302362b2d0c373c053b003a22331d042e1a36002c3230263f022d1542000000),
  (0x0, 0x1d3e3009353629072c160b2e023d41392f1d1e33422b022228402a140f121c0d07363d1d161c300e29140337003937174030203323002b0f0c2e1a03192f42000000),
  (0x0, 0x180d160027301d3f3a28232802301f1034283c06310004061802072a053e1a30421316142124141930171621003b0135023b02342f002a00180d2a413c1942000000),
  (0x0, 0x240e1f000e362721023b29010c3c2e2a27032a16010d2d18262b0036121c403f113d0c2524193200232b3036001e001d073d42031600293608381c18000d42000000),
  (0x0, 0x12e3d2806160730172e39100e00271b3b361228323c1921342a10081c021b42273c0e2f0b21271602411a3c001f0f412e0510362e002822240c0e19333b42000000),
  (0x0, 0x2c2c302d1f33353f2b2d081c293e35241232342433362a0a090819361520050a2d0d231b2001231c3f363b18001d011e06412d211e0027233d06393b2a0d42000000),
  (0x0, 0x2c2a36222c373c232507081c35301e150a1e3019220b31380321370a0e14030b39081f2c11211904313d031000001f20414221083b00261629173f220c3942000000),
  (0x0, 0x2b011d3621340c39112e2f352c3e0d04361e1b0f23072e003432042d4034282a0d171b182f320917292f173e00232732382d40081c002506370f0e113f1642000000),
  (0x0, 0x2a23171b370516252d18273c080531030d102622222711260012022342401510361f11000f07412714321f11003a301a23183935420024013e184231412042000000),
  (0x0, 0x1d1e01021f230e2a3f2719053f1837073536371a2a410a1325211a05160d2f1a34201c0322081a273405300a00384200023042232b0023001a0d1d22293e42000000),
  (0x0, 0x3b271c140c31002f3a3b273c16221f411d341736213613053f00001c31000c1b1e3d1a2c252d311a03212317001a391221151a0f3e00223c240d0300002742000000),
  (0xa4, 0xd390a22371f32123a0c061c41240e21310937162a1f1b3715050642290f40121f184200250537373b1e3200170f3e0222273d100005213b402730242b0100420000),
  (0xe6, 0x2c182a103200153d230933340e2c2a27190e013e002e25372e0a2f3c1d374017002135311637244000421b0a0002100831062318180020052f0c1439140742000000),
  (0x0, 0x1900213706330c0f1d233a1734261e2325161311170b37131033003332061e413a1a161628251b102004181100221a070d19420501001f0106403210001042000000),
  (0x149, 0x703273d2f002716122515403a2210390e131d15071e38363c1f233c1f3a333f37311d273628060c083e373e000a161c0329111027001e28320e0724200742000000),
  (0x0, 0x3a12243b2c122b2b3a2e260b06223f051b261d251b0e2903063636052c04351905242b263500393f36292410003837290b2c223d08001d3d312e3c0d0d3e42000000),
  (0x0, 0x272f23363c020b110d2d383826421a33300b0413071e3c0d420b2b0f181c07372426084225120a24190638180036150a410f1e2825001c320e340038183442000000)
  ] : List (Nat × Nat)).map decodeUCert12W19

private def sieve12AffU9C2W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x0, 0x170925261d261a1928170435383a023223371c0e400839171025131e131c053a23204141241e26333c092b3c003408212e371d3015001b153006321e302542000000),
  (0x0, 0x321f152f3914082a020a243819230f19243b030a0e070c401c383f320d213b3c2c08142c14371a013d22073600290306052d023c2d001a0d4132260b041142000000),
  (0x0, 0x131533170122212f20401c1922022c1c3341312b391c3b0b08131c2a2b260c0e31321b11140e1d3f1f2c032100122524192c1f391400191007163a30271942000000),
  (0x0, 0x2f422d18344017143d031624173f0f3a4013370319192033192e0939190c092c1717041c1c401f22280b0b37002e1c30370a132420001812321329153a0a42000000),
  (0x0, 0x420120390d110205141f1203233a033a0214251230240e311e2f3b0f3438230c00412b4228392910230c2b3b00000e2f203f250f0d00172928012414083442000000),
  (0x0, 0x22251f3d140e053126192001043441220a0c04010942112f2d183f11203c0807320c424111003d2d34260123001c1d1903041730290016071e06152b043242000000),
  (0x0, 0x3829293910123528331e12310d2e162a2d05263b251f2e2f251d073c2b1c273f1e1237183524092030312141002c1112022514211b00152e05021d263c0742000000),
  (0x0, 0x11122a27172f2b1001421c06370805130d05271e0a3a1b1b2520002f091308023810372d04101022143e362700030c0703143e3919001425113c1d23001442000000),
  (0x128, 0x3d1614060c3308120f001a2c09180b402626281a413e2c02003e0b0a103d2919130f222e321c261329163a400014052b193f1e3e3300134005320004383942000000),
  (0x0, 0x82829331f1527361336013928372f1d2a1e300933334031282121230e090f24293632211b2d000001152e01000e2935212829124100122027401a22222042000000),
  (0x0, 0x2616411b1d0f04421a0e1518114133261e0906313f1a083c4222103b3904323e1b2d3905210c170332093819002f26153d3e3b223900110e1e3b0021330842000000),
  (0x0, 0x401901040839300d2f3e2b3801223d273b143b012f1600371812121d39402f1f2b08222819400f3c08001928001c0e0e33290406300010293b162a31312642000000),
  (0x0, 0xa150d1e3c392e21370d0c41170f0e1d3d1c0e1d0b35090f422a250142313019161d1d3a220f0d1f0341142f0030110040353a200b000f33413e00191e4242000000),
  (0x0, 0x310033b2330243d25112909383b1219022313302b2e24051b050e154101292738282628032d002c2b14011d0035083c14090d2207000e1d3f0e273e352e42000000),
  (0x0, 0x3526374042042a143c213308050202091842372842070c30002424382b290e2d1c071128413a3c421d3c0a0f003c2d18100f0e2417000d3f380f421f1f0b42000000),
  (0x0, 0x2e3922320f092230142a3316123311213d013a08210a252c1e1d390b15170a2c001a1300063c182b36103a13002b362d08203a3740000c070f0e24260a3842000000),
  (0x0, 0x21d37213a143f3c3d232f05071d3c01422c3e21380e2441150a2d1d3b34133f382d043a0e06243c2a233a0600192e0b152e29360f000b1428312d39162642000000),
  (0x0, 0x3c340a1424104030041c323807190a122a340c2a08423626032f210307021d203c3b13101d35312a231e3b1600241027330d022532000a302c0d3f14224042000000),
  (0x0, 0x333b2f400a2f423113112c13050e3a240c402c2a0f36033106113c3f2e16330d3b0c331d280e352c344006040035331e2e3c3e253f00091036263c32070442000000),
  (0x0, 0x211e410e101a39381101262f160e1d04253e422e190c3706211440240e353d343b3e0a0501183a101012061a00262a073039113c1d0008293f23212f031f42000000)
  ] : List (Nat × Nat)).map decodeUCert12W19

private def sieve12AffU9C3W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x0, 0x1f062434113518403609223d2f0e313b0d2b2b2e3b22412a311c281f02122c060d1520382c322a26253c2331001a1c3f284220350e000730342711271b2442000000),
  (0x0, 0x2f013e131637131737353a1317391542361d102d1f240f1d05212c0a00313b2918100130293a2b09002a3809002341050a1d151c3d00060c1e323d22173942000000),
  (0x0, 0x42122e1211232503212b27282809391513082909322d083c3202302a232c1902263e2f262d0d3d3f120340150038103411163300210005042a271041131942000000),
  (0x128, 0x193710360a393c2f0b000c002b4116140c1107091d03120200272e340b262e190241051f3d0630342d344025000c1b3d203c12163a0004040236001b150f42000000),
  (0x0, 0x2a251c332c2b0d3c27011921260b07413b103e3e0b233a0e3b160f0d3d2d3e10363220262030163f02174124000d25253119024237000330200a072d343642000000),
  (0x0, 0x26212d12213a131f161122051815172f0333272e12200e3327122a3f1c3a382a18160a2e4103263002372b0e00181b20192f241a3100021114191b31190442000000),
  (0x0, 0x2c09020000002613112f000f21391e0224360a1e0100000029000000033735181d3f212c10222b21061b403800391d263f061b151f00010000001900000042000000)
  ] : List (Nat × Nat)).map decodeUCert12W19

set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c0_s0_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 0 4 (dropCertsW19 0 sieve12AffU6C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c0_s1_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 4 4 (dropCertsW19 4 sieve12AffU6C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c0_s2_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 8 4 (dropCertsW19 8 sieve12AffU6C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c0_s3_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 12 4 (dropCertsW19 12 sieve12AffU6C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c0_s4_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 16 4 (dropCertsW19 16 sieve12AffU6C0W19) = true := by decide
private theorem sieve12_aff_u6_c0_fast_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 0 20 sieve12AffU6C0W19 = true := by
  have h0 : checkAffRangeULModP12FastBoolW19 6 197 0 4 sieve12AffU6C0W19 = true := sieve12_aff_u6_c0_s0_w19
  have h1 : checkAffRangeULModP12FastBoolW19 6 197 0 8 sieve12AffU6C0W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 4 4 0 sieve12AffU6C0W19 h0 sieve12_aff_u6_c0_s1_w19
  have h2 : checkAffRangeULModP12FastBoolW19 6 197 0 12 sieve12AffU6C0W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 8 4 0 sieve12AffU6C0W19 h1 sieve12_aff_u6_c0_s2_w19
  have h3 : checkAffRangeULModP12FastBoolW19 6 197 0 16 sieve12AffU6C0W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 12 4 0 sieve12AffU6C0W19 h2 sieve12_aff_u6_c0_s3_w19
  have h4 : checkAffRangeULModP12FastBoolW19 6 197 0 20 sieve12AffU6C0W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 16 4 0 sieve12AffU6C0W19 h3 sieve12_aff_u6_c0_s4_w19
  exact h4
private theorem sieve12_aff_u6_c0_ok_w19 :
    checkAffRangeULModP12BoolW19 6 197 0 20 sieve12AffU6C0W19 = true :=
  (checkAffRangeULModP12FastBoolW19_eq 6 197 20 0 sieve12AffU6C0W19).symm.trans sieve12_aff_u6_c0_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c1_s0_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 20 4 (dropCertsW19 0 sieve12AffU6C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c1_s1_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 24 4 (dropCertsW19 4 sieve12AffU6C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c1_s2_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 28 4 (dropCertsW19 8 sieve12AffU6C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c1_s3_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 32 4 (dropCertsW19 12 sieve12AffU6C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c1_s4_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 36 4 (dropCertsW19 16 sieve12AffU6C1W19) = true := by decide
private theorem sieve12_aff_u6_c1_fast_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 20 20 sieve12AffU6C1W19 = true := by
  have h0 : checkAffRangeULModP12FastBoolW19 6 197 20 4 sieve12AffU6C1W19 = true := sieve12_aff_u6_c1_s0_w19
  have h1 : checkAffRangeULModP12FastBoolW19 6 197 20 8 sieve12AffU6C1W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 4 4 20 sieve12AffU6C1W19 h0 sieve12_aff_u6_c1_s1_w19
  have h2 : checkAffRangeULModP12FastBoolW19 6 197 20 12 sieve12AffU6C1W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 8 4 20 sieve12AffU6C1W19 h1 sieve12_aff_u6_c1_s2_w19
  have h3 : checkAffRangeULModP12FastBoolW19 6 197 20 16 sieve12AffU6C1W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 12 4 20 sieve12AffU6C1W19 h2 sieve12_aff_u6_c1_s3_w19
  have h4 : checkAffRangeULModP12FastBoolW19 6 197 20 20 sieve12AffU6C1W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 16 4 20 sieve12AffU6C1W19 h3 sieve12_aff_u6_c1_s4_w19
  exact h4
private theorem sieve12_aff_u6_c1_ok_w19 :
    checkAffRangeULModP12BoolW19 6 197 20 20 sieve12AffU6C1W19 = true :=
  (checkAffRangeULModP12FastBoolW19_eq 6 197 20 20 sieve12AffU6C1W19).symm.trans sieve12_aff_u6_c1_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c2_s0_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 40 4 (dropCertsW19 0 sieve12AffU6C2W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c2_s1_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 44 4 (dropCertsW19 4 sieve12AffU6C2W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c2_s2_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 48 4 (dropCertsW19 8 sieve12AffU6C2W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c2_s3_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 52 4 (dropCertsW19 12 sieve12AffU6C2W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c2_s4_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 56 4 (dropCertsW19 16 sieve12AffU6C2W19) = true := by decide
private theorem sieve12_aff_u6_c2_fast_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 40 20 sieve12AffU6C2W19 = true := by
  have h0 : checkAffRangeULModP12FastBoolW19 6 197 40 4 sieve12AffU6C2W19 = true := sieve12_aff_u6_c2_s0_w19
  have h1 : checkAffRangeULModP12FastBoolW19 6 197 40 8 sieve12AffU6C2W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 4 4 40 sieve12AffU6C2W19 h0 sieve12_aff_u6_c2_s1_w19
  have h2 : checkAffRangeULModP12FastBoolW19 6 197 40 12 sieve12AffU6C2W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 8 4 40 sieve12AffU6C2W19 h1 sieve12_aff_u6_c2_s2_w19
  have h3 : checkAffRangeULModP12FastBoolW19 6 197 40 16 sieve12AffU6C2W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 12 4 40 sieve12AffU6C2W19 h2 sieve12_aff_u6_c2_s3_w19
  have h4 : checkAffRangeULModP12FastBoolW19 6 197 40 20 sieve12AffU6C2W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 16 4 40 sieve12AffU6C2W19 h3 sieve12_aff_u6_c2_s4_w19
  exact h4
private theorem sieve12_aff_u6_c2_ok_w19 :
    checkAffRangeULModP12BoolW19 6 197 40 20 sieve12AffU6C2W19 = true :=
  (checkAffRangeULModP12FastBoolW19_eq 6 197 20 40 sieve12AffU6C2W19).symm.trans sieve12_aff_u6_c2_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c3_s0_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 60 4 (dropCertsW19 0 sieve12AffU6C3W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c3_s1_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 64 4 (dropCertsW19 4 sieve12AffU6C3W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c3_s2_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 68 4 (dropCertsW19 8 sieve12AffU6C3W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c3_s3_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 72 4 (dropCertsW19 12 sieve12AffU6C3W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c3_s4_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 76 4 (dropCertsW19 16 sieve12AffU6C3W19) = true := by decide
private theorem sieve12_aff_u6_c3_fast_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 60 20 sieve12AffU6C3W19 = true := by
  have h0 : checkAffRangeULModP12FastBoolW19 6 197 60 4 sieve12AffU6C3W19 = true := sieve12_aff_u6_c3_s0_w19
  have h1 : checkAffRangeULModP12FastBoolW19 6 197 60 8 sieve12AffU6C3W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 4 4 60 sieve12AffU6C3W19 h0 sieve12_aff_u6_c3_s1_w19
  have h2 : checkAffRangeULModP12FastBoolW19 6 197 60 12 sieve12AffU6C3W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 8 4 60 sieve12AffU6C3W19 h1 sieve12_aff_u6_c3_s2_w19
  have h3 : checkAffRangeULModP12FastBoolW19 6 197 60 16 sieve12AffU6C3W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 12 4 60 sieve12AffU6C3W19 h2 sieve12_aff_u6_c3_s3_w19
  have h4 : checkAffRangeULModP12FastBoolW19 6 197 60 20 sieve12AffU6C3W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 16 4 60 sieve12AffU6C3W19 h3 sieve12_aff_u6_c3_s4_w19
  exact h4
private theorem sieve12_aff_u6_c3_ok_w19 :
    checkAffRangeULModP12BoolW19 6 197 60 20 sieve12AffU6C3W19 = true :=
  (checkAffRangeULModP12FastBoolW19_eq 6 197 20 60 sieve12AffU6C3W19).symm.trans sieve12_aff_u6_c3_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c4_s0_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 80 4 (dropCertsW19 0 sieve12AffU6C4W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c4_s1_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 84 4 (dropCertsW19 4 sieve12AffU6C4W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c4_s2_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 88 4 (dropCertsW19 8 sieve12AffU6C4W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c4_s3_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 92 4 (dropCertsW19 12 sieve12AffU6C4W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c4_s4_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 96 4 (dropCertsW19 16 sieve12AffU6C4W19) = true := by decide
private theorem sieve12_aff_u6_c4_fast_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 80 20 sieve12AffU6C4W19 = true := by
  have h0 : checkAffRangeULModP12FastBoolW19 6 197 80 4 sieve12AffU6C4W19 = true := sieve12_aff_u6_c4_s0_w19
  have h1 : checkAffRangeULModP12FastBoolW19 6 197 80 8 sieve12AffU6C4W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 4 4 80 sieve12AffU6C4W19 h0 sieve12_aff_u6_c4_s1_w19
  have h2 : checkAffRangeULModP12FastBoolW19 6 197 80 12 sieve12AffU6C4W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 8 4 80 sieve12AffU6C4W19 h1 sieve12_aff_u6_c4_s2_w19
  have h3 : checkAffRangeULModP12FastBoolW19 6 197 80 16 sieve12AffU6C4W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 12 4 80 sieve12AffU6C4W19 h2 sieve12_aff_u6_c4_s3_w19
  have h4 : checkAffRangeULModP12FastBoolW19 6 197 80 20 sieve12AffU6C4W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 16 4 80 sieve12AffU6C4W19 h3 sieve12_aff_u6_c4_s4_w19
  exact h4
private theorem sieve12_aff_u6_c4_ok_w19 :
    checkAffRangeULModP12BoolW19 6 197 80 20 sieve12AffU6C4W19 = true :=
  (checkAffRangeULModP12FastBoolW19_eq 6 197 20 80 sieve12AffU6C4W19).symm.trans sieve12_aff_u6_c4_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c5_s0_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 100 4 (dropCertsW19 0 sieve12AffU6C5W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c5_s1_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 104 4 (dropCertsW19 4 sieve12AffU6C5W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c5_s2_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 108 4 (dropCertsW19 8 sieve12AffU6C5W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c5_s3_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 112 4 (dropCertsW19 12 sieve12AffU6C5W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c5_s4_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 116 4 (dropCertsW19 16 sieve12AffU6C5W19) = true := by decide
private theorem sieve12_aff_u6_c5_fast_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 100 20 sieve12AffU6C5W19 = true := by
  have h0 : checkAffRangeULModP12FastBoolW19 6 197 100 4 sieve12AffU6C5W19 = true := sieve12_aff_u6_c5_s0_w19
  have h1 : checkAffRangeULModP12FastBoolW19 6 197 100 8 sieve12AffU6C5W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 4 4 100 sieve12AffU6C5W19 h0 sieve12_aff_u6_c5_s1_w19
  have h2 : checkAffRangeULModP12FastBoolW19 6 197 100 12 sieve12AffU6C5W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 8 4 100 sieve12AffU6C5W19 h1 sieve12_aff_u6_c5_s2_w19
  have h3 : checkAffRangeULModP12FastBoolW19 6 197 100 16 sieve12AffU6C5W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 12 4 100 sieve12AffU6C5W19 h2 sieve12_aff_u6_c5_s3_w19
  have h4 : checkAffRangeULModP12FastBoolW19 6 197 100 20 sieve12AffU6C5W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 16 4 100 sieve12AffU6C5W19 h3 sieve12_aff_u6_c5_s4_w19
  exact h4
private theorem sieve12_aff_u6_c5_ok_w19 :
    checkAffRangeULModP12BoolW19 6 197 100 20 sieve12AffU6C5W19 = true :=
  (checkAffRangeULModP12FastBoolW19_eq 6 197 20 100 sieve12AffU6C5W19).symm.trans sieve12_aff_u6_c5_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c6_s0_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 120 4 (dropCertsW19 0 sieve12AffU6C6W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c6_s1_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 124 4 (dropCertsW19 4 sieve12AffU6C6W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c6_s2_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 128 4 (dropCertsW19 8 sieve12AffU6C6W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c6_s3_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 132 4 (dropCertsW19 12 sieve12AffU6C6W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c6_s4_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 136 4 (dropCertsW19 16 sieve12AffU6C6W19) = true := by decide
private theorem sieve12_aff_u6_c6_fast_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 120 20 sieve12AffU6C6W19 = true := by
  have h0 : checkAffRangeULModP12FastBoolW19 6 197 120 4 sieve12AffU6C6W19 = true := sieve12_aff_u6_c6_s0_w19
  have h1 : checkAffRangeULModP12FastBoolW19 6 197 120 8 sieve12AffU6C6W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 4 4 120 sieve12AffU6C6W19 h0 sieve12_aff_u6_c6_s1_w19
  have h2 : checkAffRangeULModP12FastBoolW19 6 197 120 12 sieve12AffU6C6W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 8 4 120 sieve12AffU6C6W19 h1 sieve12_aff_u6_c6_s2_w19
  have h3 : checkAffRangeULModP12FastBoolW19 6 197 120 16 sieve12AffU6C6W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 12 4 120 sieve12AffU6C6W19 h2 sieve12_aff_u6_c6_s3_w19
  have h4 : checkAffRangeULModP12FastBoolW19 6 197 120 20 sieve12AffU6C6W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 16 4 120 sieve12AffU6C6W19 h3 sieve12_aff_u6_c6_s4_w19
  exact h4
private theorem sieve12_aff_u6_c6_ok_w19 :
    checkAffRangeULModP12BoolW19 6 197 120 20 sieve12AffU6C6W19 = true :=
  (checkAffRangeULModP12FastBoolW19_eq 6 197 20 120 sieve12AffU6C6W19).symm.trans sieve12_aff_u6_c6_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c7_s0_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 140 4 (dropCertsW19 0 sieve12AffU6C7W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c7_s1_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 144 4 (dropCertsW19 4 sieve12AffU6C7W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c7_s2_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 148 4 (dropCertsW19 8 sieve12AffU6C7W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c7_s3_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 152 4 (dropCertsW19 12 sieve12AffU6C7W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c7_s4_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 156 4 (dropCertsW19 16 sieve12AffU6C7W19) = true := by decide
private theorem sieve12_aff_u6_c7_fast_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 140 20 sieve12AffU6C7W19 = true := by
  have h0 : checkAffRangeULModP12FastBoolW19 6 197 140 4 sieve12AffU6C7W19 = true := sieve12_aff_u6_c7_s0_w19
  have h1 : checkAffRangeULModP12FastBoolW19 6 197 140 8 sieve12AffU6C7W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 4 4 140 sieve12AffU6C7W19 h0 sieve12_aff_u6_c7_s1_w19
  have h2 : checkAffRangeULModP12FastBoolW19 6 197 140 12 sieve12AffU6C7W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 8 4 140 sieve12AffU6C7W19 h1 sieve12_aff_u6_c7_s2_w19
  have h3 : checkAffRangeULModP12FastBoolW19 6 197 140 16 sieve12AffU6C7W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 12 4 140 sieve12AffU6C7W19 h2 sieve12_aff_u6_c7_s3_w19
  have h4 : checkAffRangeULModP12FastBoolW19 6 197 140 20 sieve12AffU6C7W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 16 4 140 sieve12AffU6C7W19 h3 sieve12_aff_u6_c7_s4_w19
  exact h4
private theorem sieve12_aff_u6_c7_ok_w19 :
    checkAffRangeULModP12BoolW19 6 197 140 20 sieve12AffU6C7W19 = true :=
  (checkAffRangeULModP12FastBoolW19_eq 6 197 20 140 sieve12AffU6C7W19).symm.trans sieve12_aff_u6_c7_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c8_s0_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 160 4 (dropCertsW19 0 sieve12AffU6C8W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c8_s1_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 164 4 (dropCertsW19 4 sieve12AffU6C8W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c8_s2_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 168 4 (dropCertsW19 8 sieve12AffU6C8W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c8_s3_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 172 4 (dropCertsW19 12 sieve12AffU6C8W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c8_s4_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 176 4 (dropCertsW19 16 sieve12AffU6C8W19) = true := by decide
private theorem sieve12_aff_u6_c8_fast_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 160 20 sieve12AffU6C8W19 = true := by
  have h0 : checkAffRangeULModP12FastBoolW19 6 197 160 4 sieve12AffU6C8W19 = true := sieve12_aff_u6_c8_s0_w19
  have h1 : checkAffRangeULModP12FastBoolW19 6 197 160 8 sieve12AffU6C8W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 4 4 160 sieve12AffU6C8W19 h0 sieve12_aff_u6_c8_s1_w19
  have h2 : checkAffRangeULModP12FastBoolW19 6 197 160 12 sieve12AffU6C8W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 8 4 160 sieve12AffU6C8W19 h1 sieve12_aff_u6_c8_s2_w19
  have h3 : checkAffRangeULModP12FastBoolW19 6 197 160 16 sieve12AffU6C8W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 12 4 160 sieve12AffU6C8W19 h2 sieve12_aff_u6_c8_s3_w19
  have h4 : checkAffRangeULModP12FastBoolW19 6 197 160 20 sieve12AffU6C8W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 16 4 160 sieve12AffU6C8W19 h3 sieve12_aff_u6_c8_s4_w19
  exact h4
private theorem sieve12_aff_u6_c8_ok_w19 :
    checkAffRangeULModP12BoolW19 6 197 160 20 sieve12AffU6C8W19 = true :=
  (checkAffRangeULModP12FastBoolW19_eq 6 197 20 160 sieve12AffU6C8W19).symm.trans sieve12_aff_u6_c8_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c9_s0_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 180 4 (dropCertsW19 0 sieve12AffU6C9W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c9_s1_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 184 4 (dropCertsW19 4 sieve12AffU6C9W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c9_s2_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 188 4 (dropCertsW19 8 sieve12AffU6C9W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c9_s3_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 192 4 (dropCertsW19 12 sieve12AffU6C9W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u6_c9_s4_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 196 1 (dropCertsW19 16 sieve12AffU6C9W19) = true := by decide
private theorem sieve12_aff_u6_c9_fast_w19 :
    checkAffRangeULModP12FastBoolW19 6 197 180 17 sieve12AffU6C9W19 = true := by
  have h0 : checkAffRangeULModP12FastBoolW19 6 197 180 4 sieve12AffU6C9W19 = true := sieve12_aff_u6_c9_s0_w19
  have h1 : checkAffRangeULModP12FastBoolW19 6 197 180 8 sieve12AffU6C9W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 4 4 180 sieve12AffU6C9W19 h0 sieve12_aff_u6_c9_s1_w19
  have h2 : checkAffRangeULModP12FastBoolW19 6 197 180 12 sieve12AffU6C9W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 8 4 180 sieve12AffU6C9W19 h1 sieve12_aff_u6_c9_s2_w19
  have h3 : checkAffRangeULModP12FastBoolW19 6 197 180 16 sieve12AffU6C9W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 12 4 180 sieve12AffU6C9W19 h2 sieve12_aff_u6_c9_s3_w19
  have h4 : checkAffRangeULModP12FastBoolW19 6 197 180 17 sieve12AffU6C9W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 6 197 16 1 180 sieve12AffU6C9W19 h3 sieve12_aff_u6_c9_s4_w19
  exact h4
private theorem sieve12_aff_u6_c9_ok_w19 :
    checkAffRangeULModP12BoolW19 6 197 180 17 sieve12AffU6C9W19 = true :=
  (checkAffRangeULModP12FastBoolW19_eq 6 197 17 180 sieve12AffU6C9W19).symm.trans sieve12_aff_u6_c9_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve12_inf_and_inv_u6_fast_w19 :
    checkAllInvModPBoolW19 197 197 = true ∧
    checkULModPNat12FastBoolW19 197 6 1 0 sieve12InfU6W19 = true := by decide
private theorem sieve12_inf_and_inv_u6_ok_w19 :
    checkAllInvModPBoolW19 197 197 = true ∧
    checkULModPNat12BoolW19 197 6 1 0 sieve12InfU6W19 = true :=
  ⟨sieve12_inf_and_inv_u6_fast_w19.1,
   (checkULModPNat12FastBoolW19_eq 197 6 1 0 sieve12InfU6W19).symm.trans sieve12_inf_and_inv_u6_fast_w19.2⟩
private theorem sieve12_aff_all_u6_w19 (t : Nat) (ht : t < 197) :
    intDet 12 (apow12KDivW19 6 (t : Int) 1) % (197 : Int) ≠ 0 := by
  if hc0 : t < 20 then
    exact unpack_affRangeULModP12_w19 6 197 (by decide) 20 0 sieve12AffU6C0W19 sieve12_aff_u6_c0_ok_w19 t (by omega) hc0
  else
  if hc1 : t < 40 then
    exact unpack_affRangeULModP12_w19 6 197 (by decide) 20 20 sieve12AffU6C1W19 sieve12_aff_u6_c1_ok_w19 t (by omega) hc1
  else
  if hc2 : t < 60 then
    exact unpack_affRangeULModP12_w19 6 197 (by decide) 20 40 sieve12AffU6C2W19 sieve12_aff_u6_c2_ok_w19 t (by omega) hc2
  else
  if hc3 : t < 80 then
    exact unpack_affRangeULModP12_w19 6 197 (by decide) 20 60 sieve12AffU6C3W19 sieve12_aff_u6_c3_ok_w19 t (by omega) hc3
  else
  if hc4 : t < 100 then
    exact unpack_affRangeULModP12_w19 6 197 (by decide) 20 80 sieve12AffU6C4W19 sieve12_aff_u6_c4_ok_w19 t (by omega) hc4
  else
  if hc5 : t < 120 then
    exact unpack_affRangeULModP12_w19 6 197 (by decide) 20 100 sieve12AffU6C5W19 sieve12_aff_u6_c5_ok_w19 t (by omega) hc5
  else
  if hc6 : t < 140 then
    exact unpack_affRangeULModP12_w19 6 197 (by decide) 20 120 sieve12AffU6C6W19 sieve12_aff_u6_c6_ok_w19 t (by omega) hc6
  else
  if hc7 : t < 160 then
    exact unpack_affRangeULModP12_w19 6 197 (by decide) 20 140 sieve12AffU6C7W19 sieve12_aff_u6_c7_ok_w19 t (by omega) hc7
  else
  if hc8 : t < 180 then
    exact unpack_affRangeULModP12_w19 6 197 (by decide) 20 160 sieve12AffU6C8W19 sieve12_aff_u6_c8_ok_w19 t (by omega) hc8
  else
    exact unpack_affRangeULModP12_w19 6 197 (by decide) 17 180 sieve12AffU6C9W19 sieve12_aff_u6_c9_ok_w19 t (by omega) (by omega)

set_option maxRecDepth 65536 in
private theorem sieve12_aff_u7_c0_s0_w19 :
    checkAffRangeULModP12FastBoolW19 7 13 0 4 (dropCertsW19 0 sieve12AffU7C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u7_c0_s1_w19 :
    checkAffRangeULModP12FastBoolW19 7 13 4 4 (dropCertsW19 4 sieve12AffU7C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u7_c0_s2_w19 :
    checkAffRangeULModP12FastBoolW19 7 13 8 4 (dropCertsW19 8 sieve12AffU7C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u7_c0_s3_w19 :
    checkAffRangeULModP12FastBoolW19 7 13 12 1 (dropCertsW19 12 sieve12AffU7C0W19) = true := by decide
private theorem sieve12_aff_u7_c0_fast_w19 :
    checkAffRangeULModP12FastBoolW19 7 13 0 13 sieve12AffU7C0W19 = true := by
  have h0 : checkAffRangeULModP12FastBoolW19 7 13 0 4 sieve12AffU7C0W19 = true := sieve12_aff_u7_c0_s0_w19
  have h1 : checkAffRangeULModP12FastBoolW19 7 13 0 8 sieve12AffU7C0W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 7 13 4 4 0 sieve12AffU7C0W19 h0 sieve12_aff_u7_c0_s1_w19
  have h2 : checkAffRangeULModP12FastBoolW19 7 13 0 12 sieve12AffU7C0W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 7 13 8 4 0 sieve12AffU7C0W19 h1 sieve12_aff_u7_c0_s2_w19
  have h3 : checkAffRangeULModP12FastBoolW19 7 13 0 13 sieve12AffU7C0W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 7 13 12 1 0 sieve12AffU7C0W19 h2 sieve12_aff_u7_c0_s3_w19
  exact h3
private theorem sieve12_aff_u7_c0_ok_w19 :
    checkAffRangeULModP12BoolW19 7 13 0 13 sieve12AffU7C0W19 = true :=
  (checkAffRangeULModP12FastBoolW19_eq 7 13 13 0 sieve12AffU7C0W19).symm.trans sieve12_aff_u7_c0_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve12_inf_and_inv_u7_fast_w19 :
    checkAllInvModPBoolW19 13 13 = true ∧
    checkULModPNat12FastBoolW19 13 7 1 0 sieve12InfU7W19 = true := by decide
private theorem sieve12_inf_and_inv_u7_ok_w19 :
    checkAllInvModPBoolW19 13 13 = true ∧
    checkULModPNat12BoolW19 13 7 1 0 sieve12InfU7W19 = true :=
  ⟨sieve12_inf_and_inv_u7_fast_w19.1,
   (checkULModPNat12FastBoolW19_eq 13 7 1 0 sieve12InfU7W19).symm.trans sieve12_inf_and_inv_u7_fast_w19.2⟩
private theorem sieve12_aff_all_u7_w19 (t : Nat) (ht : t < 13) :
    intDet 12 (apow12KDivW19 7 (t : Int) 1) % (13 : Int) ≠ 0 := by
    exact unpack_affRangeULModP12_w19 7 13 (by decide) 13 0 sieve12AffU7C0W19 sieve12_aff_u7_c0_ok_w19 t (by omega) (by omega)

set_option maxRecDepth 65536 in
private theorem sieve12_aff_u8_c0_s0_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 0 4 (dropCertsW19 0 sieve12AffU8C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u8_c0_s1_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 4 4 (dropCertsW19 4 sieve12AffU8C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u8_c0_s2_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 8 4 (dropCertsW19 8 sieve12AffU8C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u8_c0_s3_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 12 4 (dropCertsW19 12 sieve12AffU8C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u8_c0_s4_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 16 4 (dropCertsW19 16 sieve12AffU8C0W19) = true := by decide
private theorem sieve12_aff_u8_c0_fast_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 0 20 sieve12AffU8C0W19 = true := by
  have h0 : checkAffRangeULModP12FastBoolW19 8 103 0 4 sieve12AffU8C0W19 = true := sieve12_aff_u8_c0_s0_w19
  have h1 : checkAffRangeULModP12FastBoolW19 8 103 0 8 sieve12AffU8C0W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 8 103 4 4 0 sieve12AffU8C0W19 h0 sieve12_aff_u8_c0_s1_w19
  have h2 : checkAffRangeULModP12FastBoolW19 8 103 0 12 sieve12AffU8C0W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 8 103 8 4 0 sieve12AffU8C0W19 h1 sieve12_aff_u8_c0_s2_w19
  have h3 : checkAffRangeULModP12FastBoolW19 8 103 0 16 sieve12AffU8C0W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 8 103 12 4 0 sieve12AffU8C0W19 h2 sieve12_aff_u8_c0_s3_w19
  have h4 : checkAffRangeULModP12FastBoolW19 8 103 0 20 sieve12AffU8C0W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 8 103 16 4 0 sieve12AffU8C0W19 h3 sieve12_aff_u8_c0_s4_w19
  exact h4
private theorem sieve12_aff_u8_c0_ok_w19 :
    checkAffRangeULModP12BoolW19 8 103 0 20 sieve12AffU8C0W19 = true :=
  (checkAffRangeULModP12FastBoolW19_eq 8 103 20 0 sieve12AffU8C0W19).symm.trans sieve12_aff_u8_c0_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u8_c1_s0_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 20 4 (dropCertsW19 0 sieve12AffU8C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u8_c1_s1_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 24 4 (dropCertsW19 4 sieve12AffU8C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u8_c1_s2_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 28 4 (dropCertsW19 8 sieve12AffU8C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u8_c1_s3_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 32 4 (dropCertsW19 12 sieve12AffU8C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u8_c1_s4_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 36 4 (dropCertsW19 16 sieve12AffU8C1W19) = true := by decide
private theorem sieve12_aff_u8_c1_fast_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 20 20 sieve12AffU8C1W19 = true := by
  have h0 : checkAffRangeULModP12FastBoolW19 8 103 20 4 sieve12AffU8C1W19 = true := sieve12_aff_u8_c1_s0_w19
  have h1 : checkAffRangeULModP12FastBoolW19 8 103 20 8 sieve12AffU8C1W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 8 103 4 4 20 sieve12AffU8C1W19 h0 sieve12_aff_u8_c1_s1_w19
  have h2 : checkAffRangeULModP12FastBoolW19 8 103 20 12 sieve12AffU8C1W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 8 103 8 4 20 sieve12AffU8C1W19 h1 sieve12_aff_u8_c1_s2_w19
  have h3 : checkAffRangeULModP12FastBoolW19 8 103 20 16 sieve12AffU8C1W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 8 103 12 4 20 sieve12AffU8C1W19 h2 sieve12_aff_u8_c1_s3_w19
  have h4 : checkAffRangeULModP12FastBoolW19 8 103 20 20 sieve12AffU8C1W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 8 103 16 4 20 sieve12AffU8C1W19 h3 sieve12_aff_u8_c1_s4_w19
  exact h4
private theorem sieve12_aff_u8_c1_ok_w19 :
    checkAffRangeULModP12BoolW19 8 103 20 20 sieve12AffU8C1W19 = true :=
  (checkAffRangeULModP12FastBoolW19_eq 8 103 20 20 sieve12AffU8C1W19).symm.trans sieve12_aff_u8_c1_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u8_c2_s0_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 40 4 (dropCertsW19 0 sieve12AffU8C2W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u8_c2_s1_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 44 4 (dropCertsW19 4 sieve12AffU8C2W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u8_c2_s2_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 48 4 (dropCertsW19 8 sieve12AffU8C2W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u8_c2_s3_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 52 4 (dropCertsW19 12 sieve12AffU8C2W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u8_c2_s4_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 56 4 (dropCertsW19 16 sieve12AffU8C2W19) = true := by decide
private theorem sieve12_aff_u8_c2_fast_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 40 20 sieve12AffU8C2W19 = true := by
  have h0 : checkAffRangeULModP12FastBoolW19 8 103 40 4 sieve12AffU8C2W19 = true := sieve12_aff_u8_c2_s0_w19
  have h1 : checkAffRangeULModP12FastBoolW19 8 103 40 8 sieve12AffU8C2W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 8 103 4 4 40 sieve12AffU8C2W19 h0 sieve12_aff_u8_c2_s1_w19
  have h2 : checkAffRangeULModP12FastBoolW19 8 103 40 12 sieve12AffU8C2W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 8 103 8 4 40 sieve12AffU8C2W19 h1 sieve12_aff_u8_c2_s2_w19
  have h3 : checkAffRangeULModP12FastBoolW19 8 103 40 16 sieve12AffU8C2W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 8 103 12 4 40 sieve12AffU8C2W19 h2 sieve12_aff_u8_c2_s3_w19
  have h4 : checkAffRangeULModP12FastBoolW19 8 103 40 20 sieve12AffU8C2W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 8 103 16 4 40 sieve12AffU8C2W19 h3 sieve12_aff_u8_c2_s4_w19
  exact h4
private theorem sieve12_aff_u8_c2_ok_w19 :
    checkAffRangeULModP12BoolW19 8 103 40 20 sieve12AffU8C2W19 = true :=
  (checkAffRangeULModP12FastBoolW19_eq 8 103 20 40 sieve12AffU8C2W19).symm.trans sieve12_aff_u8_c2_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u8_c3_s0_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 60 4 (dropCertsW19 0 sieve12AffU8C3W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u8_c3_s1_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 64 4 (dropCertsW19 4 sieve12AffU8C3W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u8_c3_s2_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 68 4 (dropCertsW19 8 sieve12AffU8C3W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u8_c3_s3_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 72 4 (dropCertsW19 12 sieve12AffU8C3W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u8_c3_s4_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 76 4 (dropCertsW19 16 sieve12AffU8C3W19) = true := by decide
private theorem sieve12_aff_u8_c3_fast_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 60 20 sieve12AffU8C3W19 = true := by
  have h0 : checkAffRangeULModP12FastBoolW19 8 103 60 4 sieve12AffU8C3W19 = true := sieve12_aff_u8_c3_s0_w19
  have h1 : checkAffRangeULModP12FastBoolW19 8 103 60 8 sieve12AffU8C3W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 8 103 4 4 60 sieve12AffU8C3W19 h0 sieve12_aff_u8_c3_s1_w19
  have h2 : checkAffRangeULModP12FastBoolW19 8 103 60 12 sieve12AffU8C3W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 8 103 8 4 60 sieve12AffU8C3W19 h1 sieve12_aff_u8_c3_s2_w19
  have h3 : checkAffRangeULModP12FastBoolW19 8 103 60 16 sieve12AffU8C3W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 8 103 12 4 60 sieve12AffU8C3W19 h2 sieve12_aff_u8_c3_s3_w19
  have h4 : checkAffRangeULModP12FastBoolW19 8 103 60 20 sieve12AffU8C3W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 8 103 16 4 60 sieve12AffU8C3W19 h3 sieve12_aff_u8_c3_s4_w19
  exact h4
private theorem sieve12_aff_u8_c3_ok_w19 :
    checkAffRangeULModP12BoolW19 8 103 60 20 sieve12AffU8C3W19 = true :=
  (checkAffRangeULModP12FastBoolW19_eq 8 103 20 60 sieve12AffU8C3W19).symm.trans sieve12_aff_u8_c3_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u8_c4_s0_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 80 4 (dropCertsW19 0 sieve12AffU8C4W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u8_c4_s1_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 84 4 (dropCertsW19 4 sieve12AffU8C4W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u8_c4_s2_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 88 4 (dropCertsW19 8 sieve12AffU8C4W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u8_c4_s3_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 92 4 (dropCertsW19 12 sieve12AffU8C4W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u8_c4_s4_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 96 4 (dropCertsW19 16 sieve12AffU8C4W19) = true := by decide
private theorem sieve12_aff_u8_c4_fast_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 80 20 sieve12AffU8C4W19 = true := by
  have h0 : checkAffRangeULModP12FastBoolW19 8 103 80 4 sieve12AffU8C4W19 = true := sieve12_aff_u8_c4_s0_w19
  have h1 : checkAffRangeULModP12FastBoolW19 8 103 80 8 sieve12AffU8C4W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 8 103 4 4 80 sieve12AffU8C4W19 h0 sieve12_aff_u8_c4_s1_w19
  have h2 : checkAffRangeULModP12FastBoolW19 8 103 80 12 sieve12AffU8C4W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 8 103 8 4 80 sieve12AffU8C4W19 h1 sieve12_aff_u8_c4_s2_w19
  have h3 : checkAffRangeULModP12FastBoolW19 8 103 80 16 sieve12AffU8C4W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 8 103 12 4 80 sieve12AffU8C4W19 h2 sieve12_aff_u8_c4_s3_w19
  have h4 : checkAffRangeULModP12FastBoolW19 8 103 80 20 sieve12AffU8C4W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 8 103 16 4 80 sieve12AffU8C4W19 h3 sieve12_aff_u8_c4_s4_w19
  exact h4
private theorem sieve12_aff_u8_c4_ok_w19 :
    checkAffRangeULModP12BoolW19 8 103 80 20 sieve12AffU8C4W19 = true :=
  (checkAffRangeULModP12FastBoolW19_eq 8 103 20 80 sieve12AffU8C4W19).symm.trans sieve12_aff_u8_c4_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u8_c5_s0_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 100 3 (dropCertsW19 0 sieve12AffU8C5W19) = true := by decide
private theorem sieve12_aff_u8_c5_fast_w19 :
    checkAffRangeULModP12FastBoolW19 8 103 100 3 sieve12AffU8C5W19 = true := by
  have h0 : checkAffRangeULModP12FastBoolW19 8 103 100 3 sieve12AffU8C5W19 = true := sieve12_aff_u8_c5_s0_w19
  exact h0
private theorem sieve12_aff_u8_c5_ok_w19 :
    checkAffRangeULModP12BoolW19 8 103 100 3 sieve12AffU8C5W19 = true :=
  (checkAffRangeULModP12FastBoolW19_eq 8 103 3 100 sieve12AffU8C5W19).symm.trans sieve12_aff_u8_c5_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve12_inf_and_inv_u8_fast_w19 :
    checkAllInvModPBoolW19 103 103 = true ∧
    checkULModPNat12FastBoolW19 103 8 1 0 sieve12InfU8W19 = true := by decide
private theorem sieve12_inf_and_inv_u8_ok_w19 :
    checkAllInvModPBoolW19 103 103 = true ∧
    checkULModPNat12BoolW19 103 8 1 0 sieve12InfU8W19 = true :=
  ⟨sieve12_inf_and_inv_u8_fast_w19.1,
   (checkULModPNat12FastBoolW19_eq 103 8 1 0 sieve12InfU8W19).symm.trans sieve12_inf_and_inv_u8_fast_w19.2⟩
private theorem sieve12_aff_all_u8_w19 (t : Nat) (ht : t < 103) :
    intDet 12 (apow12KDivW19 8 (t : Int) 1) % (103 : Int) ≠ 0 := by
  if hc0 : t < 20 then
    exact unpack_affRangeULModP12_w19 8 103 (by decide) 20 0 sieve12AffU8C0W19 sieve12_aff_u8_c0_ok_w19 t (by omega) hc0
  else
  if hc1 : t < 40 then
    exact unpack_affRangeULModP12_w19 8 103 (by decide) 20 20 sieve12AffU8C1W19 sieve12_aff_u8_c1_ok_w19 t (by omega) hc1
  else
  if hc2 : t < 60 then
    exact unpack_affRangeULModP12_w19 8 103 (by decide) 20 40 sieve12AffU8C2W19 sieve12_aff_u8_c2_ok_w19 t (by omega) hc2
  else
  if hc3 : t < 80 then
    exact unpack_affRangeULModP12_w19 8 103 (by decide) 20 60 sieve12AffU8C3W19 sieve12_aff_u8_c3_ok_w19 t (by omega) hc3
  else
  if hc4 : t < 100 then
    exact unpack_affRangeULModP12_w19 8 103 (by decide) 20 80 sieve12AffU8C4W19 sieve12_aff_u8_c4_ok_w19 t (by omega) hc4
  else
    exact unpack_affRangeULModP12_w19 8 103 (by decide) 3 100 sieve12AffU8C5W19 sieve12_aff_u8_c5_ok_w19 t (by omega) (by omega)

set_option maxRecDepth 65536 in
private theorem sieve12_aff_u9_c0_s0_w19 :
    checkAffRangeULModP12FastBoolW19 9 67 0 4 (dropCertsW19 0 sieve12AffU9C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u9_c0_s1_w19 :
    checkAffRangeULModP12FastBoolW19 9 67 4 4 (dropCertsW19 4 sieve12AffU9C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u9_c0_s2_w19 :
    checkAffRangeULModP12FastBoolW19 9 67 8 4 (dropCertsW19 8 sieve12AffU9C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u9_c0_s3_w19 :
    checkAffRangeULModP12FastBoolW19 9 67 12 4 (dropCertsW19 12 sieve12AffU9C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u9_c0_s4_w19 :
    checkAffRangeULModP12FastBoolW19 9 67 16 4 (dropCertsW19 16 sieve12AffU9C0W19) = true := by decide
private theorem sieve12_aff_u9_c0_fast_w19 :
    checkAffRangeULModP12FastBoolW19 9 67 0 20 sieve12AffU9C0W19 = true := by
  have h0 : checkAffRangeULModP12FastBoolW19 9 67 0 4 sieve12AffU9C0W19 = true := sieve12_aff_u9_c0_s0_w19
  have h1 : checkAffRangeULModP12FastBoolW19 9 67 0 8 sieve12AffU9C0W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 9 67 4 4 0 sieve12AffU9C0W19 h0 sieve12_aff_u9_c0_s1_w19
  have h2 : checkAffRangeULModP12FastBoolW19 9 67 0 12 sieve12AffU9C0W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 9 67 8 4 0 sieve12AffU9C0W19 h1 sieve12_aff_u9_c0_s2_w19
  have h3 : checkAffRangeULModP12FastBoolW19 9 67 0 16 sieve12AffU9C0W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 9 67 12 4 0 sieve12AffU9C0W19 h2 sieve12_aff_u9_c0_s3_w19
  have h4 : checkAffRangeULModP12FastBoolW19 9 67 0 20 sieve12AffU9C0W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 9 67 16 4 0 sieve12AffU9C0W19 h3 sieve12_aff_u9_c0_s4_w19
  exact h4
private theorem sieve12_aff_u9_c0_ok_w19 :
    checkAffRangeULModP12BoolW19 9 67 0 20 sieve12AffU9C0W19 = true :=
  (checkAffRangeULModP12FastBoolW19_eq 9 67 20 0 sieve12AffU9C0W19).symm.trans sieve12_aff_u9_c0_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u9_c1_s0_w19 :
    checkAffRangeULModP12FastBoolW19 9 67 20 4 (dropCertsW19 0 sieve12AffU9C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u9_c1_s1_w19 :
    checkAffRangeULModP12FastBoolW19 9 67 24 4 (dropCertsW19 4 sieve12AffU9C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u9_c1_s2_w19 :
    checkAffRangeULModP12FastBoolW19 9 67 28 4 (dropCertsW19 8 sieve12AffU9C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u9_c1_s3_w19 :
    checkAffRangeULModP12FastBoolW19 9 67 32 4 (dropCertsW19 12 sieve12AffU9C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u9_c1_s4_w19 :
    checkAffRangeULModP12FastBoolW19 9 67 36 4 (dropCertsW19 16 sieve12AffU9C1W19) = true := by decide
private theorem sieve12_aff_u9_c1_fast_w19 :
    checkAffRangeULModP12FastBoolW19 9 67 20 20 sieve12AffU9C1W19 = true := by
  have h0 : checkAffRangeULModP12FastBoolW19 9 67 20 4 sieve12AffU9C1W19 = true := sieve12_aff_u9_c1_s0_w19
  have h1 : checkAffRangeULModP12FastBoolW19 9 67 20 8 sieve12AffU9C1W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 9 67 4 4 20 sieve12AffU9C1W19 h0 sieve12_aff_u9_c1_s1_w19
  have h2 : checkAffRangeULModP12FastBoolW19 9 67 20 12 sieve12AffU9C1W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 9 67 8 4 20 sieve12AffU9C1W19 h1 sieve12_aff_u9_c1_s2_w19
  have h3 : checkAffRangeULModP12FastBoolW19 9 67 20 16 sieve12AffU9C1W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 9 67 12 4 20 sieve12AffU9C1W19 h2 sieve12_aff_u9_c1_s3_w19
  have h4 : checkAffRangeULModP12FastBoolW19 9 67 20 20 sieve12AffU9C1W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 9 67 16 4 20 sieve12AffU9C1W19 h3 sieve12_aff_u9_c1_s4_w19
  exact h4
private theorem sieve12_aff_u9_c1_ok_w19 :
    checkAffRangeULModP12BoolW19 9 67 20 20 sieve12AffU9C1W19 = true :=
  (checkAffRangeULModP12FastBoolW19_eq 9 67 20 20 sieve12AffU9C1W19).symm.trans sieve12_aff_u9_c1_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u9_c2_s0_w19 :
    checkAffRangeULModP12FastBoolW19 9 67 40 4 (dropCertsW19 0 sieve12AffU9C2W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u9_c2_s1_w19 :
    checkAffRangeULModP12FastBoolW19 9 67 44 4 (dropCertsW19 4 sieve12AffU9C2W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u9_c2_s2_w19 :
    checkAffRangeULModP12FastBoolW19 9 67 48 4 (dropCertsW19 8 sieve12AffU9C2W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u9_c2_s3_w19 :
    checkAffRangeULModP12FastBoolW19 9 67 52 4 (dropCertsW19 12 sieve12AffU9C2W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u9_c2_s4_w19 :
    checkAffRangeULModP12FastBoolW19 9 67 56 4 (dropCertsW19 16 sieve12AffU9C2W19) = true := by decide
private theorem sieve12_aff_u9_c2_fast_w19 :
    checkAffRangeULModP12FastBoolW19 9 67 40 20 sieve12AffU9C2W19 = true := by
  have h0 : checkAffRangeULModP12FastBoolW19 9 67 40 4 sieve12AffU9C2W19 = true := sieve12_aff_u9_c2_s0_w19
  have h1 : checkAffRangeULModP12FastBoolW19 9 67 40 8 sieve12AffU9C2W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 9 67 4 4 40 sieve12AffU9C2W19 h0 sieve12_aff_u9_c2_s1_w19
  have h2 : checkAffRangeULModP12FastBoolW19 9 67 40 12 sieve12AffU9C2W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 9 67 8 4 40 sieve12AffU9C2W19 h1 sieve12_aff_u9_c2_s2_w19
  have h3 : checkAffRangeULModP12FastBoolW19 9 67 40 16 sieve12AffU9C2W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 9 67 12 4 40 sieve12AffU9C2W19 h2 sieve12_aff_u9_c2_s3_w19
  have h4 : checkAffRangeULModP12FastBoolW19 9 67 40 20 sieve12AffU9C2W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 9 67 16 4 40 sieve12AffU9C2W19 h3 sieve12_aff_u9_c2_s4_w19
  exact h4
private theorem sieve12_aff_u9_c2_ok_w19 :
    checkAffRangeULModP12BoolW19 9 67 40 20 sieve12AffU9C2W19 = true :=
  (checkAffRangeULModP12FastBoolW19_eq 9 67 20 40 sieve12AffU9C2W19).symm.trans sieve12_aff_u9_c2_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u9_c3_s0_w19 :
    checkAffRangeULModP12FastBoolW19 9 67 60 4 (dropCertsW19 0 sieve12AffU9C3W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve12_aff_u9_c3_s1_w19 :
    checkAffRangeULModP12FastBoolW19 9 67 64 3 (dropCertsW19 4 sieve12AffU9C3W19) = true := by decide
private theorem sieve12_aff_u9_c3_fast_w19 :
    checkAffRangeULModP12FastBoolW19 9 67 60 7 sieve12AffU9C3W19 = true := by
  have h0 : checkAffRangeULModP12FastBoolW19 9 67 60 4 sieve12AffU9C3W19 = true := sieve12_aff_u9_c3_s0_w19
  have h1 : checkAffRangeULModP12FastBoolW19 9 67 60 7 sieve12AffU9C3W19 = true :=
    checkAffRangeULModP12FastBoolW19_glue 9 67 4 3 60 sieve12AffU9C3W19 h0 sieve12_aff_u9_c3_s1_w19
  exact h1
private theorem sieve12_aff_u9_c3_ok_w19 :
    checkAffRangeULModP12BoolW19 9 67 60 7 sieve12AffU9C3W19 = true :=
  (checkAffRangeULModP12FastBoolW19_eq 9 67 7 60 sieve12AffU9C3W19).symm.trans sieve12_aff_u9_c3_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve12_inf_and_inv_u9_fast_w19 :
    checkAllInvModPBoolW19 67 67 = true ∧
    checkULModPNat12FastBoolW19 67 9 1 0 sieve12InfU9W19 = true := by decide
private theorem sieve12_inf_and_inv_u9_ok_w19 :
    checkAllInvModPBoolW19 67 67 = true ∧
    checkULModPNat12BoolW19 67 9 1 0 sieve12InfU9W19 = true :=
  ⟨sieve12_inf_and_inv_u9_fast_w19.1,
   (checkULModPNat12FastBoolW19_eq 67 9 1 0 sieve12InfU9W19).symm.trans sieve12_inf_and_inv_u9_fast_w19.2⟩
private theorem sieve12_aff_all_u9_w19 (t : Nat) (ht : t < 67) :
    intDet 12 (apow12KDivW19 9 (t : Int) 1) % (67 : Int) ≠ 0 := by
  if hc0 : t < 20 then
    exact unpack_affRangeULModP12_w19 9 67 (by decide) 20 0 sieve12AffU9C0W19 sieve12_aff_u9_c0_ok_w19 t (by omega) hc0
  else
  if hc1 : t < 40 then
    exact unpack_affRangeULModP12_w19 9 67 (by decide) 20 20 sieve12AffU9C1W19 sieve12_aff_u9_c1_ok_w19 t (by omega) hc1
  else
  if hc2 : t < 60 then
    exact unpack_affRangeULModP12_w19 9 67 (by decide) 20 40 sieve12AffU9C2W19 sieve12_aff_u9_c2_ok_w19 t (by omega) hc2
  else
    exact unpack_affRangeULModP12_w19 9 67 (by decide) 7 60 sieve12AffU9C3W19 sieve12_aff_u9_c3_ok_w19 t (by omega) (by omega)


-- Mod-`243` Resonant-Ray Non-Vanishing on `u ∈ {11, 13, 15, 17}` (`v_2(k') = 1` caps `u ≤ 18`):
private def checkResonantMod243UpTo18W19 (w0 k0 : Nat) : Bool :=
  (laurentTrop3ResonantQuad w0 k0 11 % 243 != 0) &&
  (laurentTrop3ResonantQuad w0 k0 13 % 243 != 0) &&
  (laurentTrop3ResonantQuad w0 k0 15 % 243 != 0) &&
  (laurentTrop3ResonantQuad w0 k0 17 % 243 != 0)

private theorem odd_resonant_mod243_rays_cert_w19 :
    checkResonantMod243UpTo18W19 5 2 = true ∧
    checkResonantMod243UpTo18W19 1 14 = true ∧
    checkResonantMod243UpTo18W19 1 22 = true := by decide

/--
  Theorem W19.2a (`laurent_12x12_t4u3_u6_to_9_nonvanishing_and_resonant_mod243_elimination`,
  `zero custom axioms`):
  Rank-3 Order-4 `12 × 12` `(T = 4, U = 3)` Global `u ∈ {6, 7, 8, 9}` Zero-Freeness, Exact
  Closed-Form `laurentTrop3Mat12` Factorization, `v_3(Q_u) ≥ (u + 5) / 3` (`243 ∣ Q_u` for `u ≥ 10`)
  & `v_2(k') = 1 -> u ≤ 18` Locks, & Complete `∀ u ≥ 1` Elimination of Mod-`9` Resonant Rays
  `(5 * W, 2 * W)`, `(W, 14 * W)`, `(W, 22 * W)`:
  1. Projective `P^1(F_p)` sieves (`p = 197, 13, 103, 67` for `u = 6, 7, 8, 9`) prove global
     ZERO-FREE non-vanishing across 100% of `W, K ≥ 1` for ALL `u ∈ {2, ..., 9}`, lifting the
     multi-`u` zero-horizon from `u ≥ 6` to `u ≥ 10`, while `(K / gcd(W, K)) % 4 = 2` (`v_2(k') = 1`)
     caps any zero universally to `u ≤ 18` (`u ≥ 19 -> det_12(W, K, u) ≠ 0`);
  2. Exact closed-form factorization across ALL `W, K : Nat` and ALL `u ≥ 1`:
     `27 * det_12(laurentTrop3Mat12Explicit W K u) = 2^(10*u - 4) * W^8 * K^3 * ((2^u - 1)*K + (2^u + 1)*W) * Q_u(W, K)^3`;
  3. Universal `3`-adic valuation squeeze on coprime non-3-divisible rays: any zero at `u ≥ 1` forces
     `3 ^ ((u + 2) / 3 + 1) ∣ Q_u(w', k')` (`27 ∣ Q_u` for `u ≥ 4`, `243 ∣ Q_u` for `u ≥ 10`);
  4. Complete `∀ W ≥ 1, ∀ u ≥ 1` zero-free elimination of resonant rays `(5*W, 2*W)`, `(W, 14*W)`,
     and `(W, 22*W)` (`Branch P3.2`–`P3.3`, witness `LAURENT_16X16_T4U4_U1_CONE_SIGN_FLIP_3_5_VS_4_7`, `W19_H2`).
-/
theorem laurent_12x12_t4u3_u6_to_9_nonvanishing_and_resonant_mod243_elimination :
    (∀ (u W K : Nat), (u = 6 ∨ u = 7 ∨ u = 8 ∨ u = 9) -> W ≥ 1 -> K ≥ 1 ->
      intDet 12 (laurentTwoBaseT4U3Mat12 W K u) ≠ 0) ∧
    (∀ (u W K : Nat), 2 ≤ u -> u ≤ 9 -> W ≥ 1 -> K ≥ 1 ->
      intDet 12 (laurentTwoBaseT4U3Mat12 W K u) ≠ 0) ∧
    (∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 -> (K / Nat.gcd W K) % 4 = 2 -> u ≥ 19 ->
      intDet 12 (laurentTwoBaseT4U3Mat12 W K u) ≠ 0) ∧
    (∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 -> u ≥ 1 ->
      intDet 12 (laurentTwoBaseT4U3Mat12 W K u) = 0 ->
      (u = 1 ∧ K = 4 * W) ∨
      (u ≥ 10 ∧ K ≠ 4 * W ∧ (K / Nat.gcd W K) % 2 = 0 ∧
        2 ^ ((u + 17) / 18) ≤ K / Nat.gcd W K ∧
        u < 18 * binBitLength (K / Nat.gcd W K))) ∧
    ((∀ (W K u : Nat),
        Int.ofNat (3 ^ (9 * u)) ∣
          (intDet 12 (laurentTwoBaseT4U3Mat12 W K u) -
            Int.ofNat (3 ^ (8 * u)) * intDet 12 (laurentTrop3Mat12Explicit W K u))) ∧
     (∀ (W K u : Nat), u ≥ 1 ->
        27 * intDet 12 (laurentTrop3Mat12Explicit W K u) =
          Int.ofNat (2 ^ (10 * u - 4) * W ^ 8 * K ^ 3 *
            ((2 ^ u - 1) * K + (2 ^ u + 1) * W) * (laurentTrop3ResonantQuad W K u) ^ 3))) ∧
    (∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 ->
      (W / Nat.gcd W K) % 3 ≠ 0 -> (K / Nat.gcd W K) % 3 ≠ 0 ->
      intDet 12 (laurentTwoBaseT4U3Mat12 W K u) = 0 ->
      (u ≥ 1 -> 3 ^ ((u + 2) / 3 + 1) ∣ laurentTrop3ResonantQuad (W / Nat.gcd W K) (K / Nat.gcd W K) u) ∧
      (u ≥ 4 -> 27 ∣ laurentTrop3ResonantQuad (W / Nat.gcd W K) (K / Nat.gcd W K) u) ∧
      (u ≥ 10 -> 243 ∣ laurentTrop3ResonantQuad (W / Nat.gcd W K) (K / Nat.gcd W K) u)) ∧
    (∀ (W u : Nat), W ≥ 1 -> u ≥ 1 ->
      intDet 12 (laurentTwoBaseT4U3Mat12 (5 * W) (2 * W) u) ≠ 0 ∧
      intDet 12 (laurentTwoBaseT4U3Mat12 W (14 * W) u) ≠ 0 ∧
      intDet 12 (laurentTwoBaseT4U3Mat12 W (22 * W) u) ≠ 0) := by
  have hu69 : ∀ (u W K : Nat), (u = 6 ∨ u = 7 ∨ u = 8 ∨ u = 9) -> W ≥ 1 -> K ≥ 1 ->
      intDet 12 (laurentTwoBaseT4U3Mat12 W K u) ≠ 0 := by
    intro u W K hu hW hK
    rcases hu with rfl | rfl | rfl | rfl
    · exact det12_t4u3_nonzero_of_proj_sieve_w19 6 197 (by decide)
        sieve12_inf_and_inv_u6_ok_w19.1
        (checkULModPNat12BoolW19_sound 197 6 1 0 (by decide) sieve12InfU6W19 sieve12_inf_and_inv_u6_ok_w19.2)
        sieve12_aff_all_u6_w19 W K hW hK
    · exact det12_t4u3_nonzero_of_proj_sieve_w19 7 13 (by decide)
        sieve12_inf_and_inv_u7_ok_w19.1
        (checkULModPNat12BoolW19_sound 13 7 1 0 (by decide) sieve12InfU7W19 sieve12_inf_and_inv_u7_ok_w19.2)
        sieve12_aff_all_u7_w19 W K hW hK
    · exact det12_t4u3_nonzero_of_proj_sieve_w19 8 103 (by decide)
        sieve12_inf_and_inv_u8_ok_w19.1
        (checkULModPNat12BoolW19_sound 103 8 1 0 (by decide) sieve12InfU8W19 sieve12_inf_and_inv_u8_ok_w19.2)
        sieve12_aff_all_u8_w19 W K hW hK
    · exact det12_t4u3_nonzero_of_proj_sieve_w19 9 67 (by decide)
        sieve12_inf_and_inv_u9_ok_w19.1
        (checkULModPNat12BoolW19_sound 67 9 1 0 (by decide) sieve12InfU9W19 sieve12_inf_and_inv_u9_ok_w19.2)
        sieve12_aff_all_u9_w19 W K hW hK
  have hw18 := laurent_12x12_t4u3_u2_to_5_nonvanishing_and_2adic_zero_horizon
  have hu29 : ∀ (u W K : Nat), 2 ≤ u -> u ≤ 9 -> W ≥ 1 -> K ≥ 1 ->
      intDet 12 (laurentTwoBaseT4U3Mat12 W K u) ≠ 0 := by
    intro u W K hlo hhi hW hK
    rcases (by omega : (u = 2 ∨ u = 3 ∨ u = 4 ∨ u = 5) ∨ (u = 6 ∨ u = 7 ∨ u = 8 ∨ u = 9)) with h25 | h69
    · exact hw18.2.1.1 W K u hW hK (by omega) (by omega)
    · exact hu69 u W K h69 hW hK
  have hv2_cap18 : ∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 -> (K / Nat.gcd W K) % 4 = 2 -> u ≥ 19 ->
      intDet 12 (laurentTwoBaseT4U3Mat12 W K u) ≠ 0 := by
    intro W K u hW _ hk4 hu19 hz
    let g := Nat.gcd W K
    have hg_pos : g ≥ 1 := Nat.gcd_pos_of_pos_left K hW
    let w' := W / g
    let k' := K / g
    have hW_eq : W = g * w' := by rw [Nat.mul_comm]; exact (Nat.div_mul_cancel (Nat.gcd_dvd_left W K)).symm
    have hK_eq : K = g * k' := by rw [Nat.mul_comm]; exact (Nat.div_mul_cancel (Nat.gcd_dvd_right W K)).symm
    have hz_prim : intDet 12 (laurentTwoBaseT4U3Mat12 w' k' u) = 0 := by
      rw [hW_eq, hK_eq, det12_t4u3_homog18_w19 u g w' k'] at hz
      have hg18_pos : intPowNat (g : Int) 18 > 0 := by
        rw [intPowNat_natCast_w19 g 18]; have := nat_pow_pos_of_pos g hg_pos 18; omega
      by_cases h0 : intDet 12 (laurentTwoBaseT4U3Mat12 w' k' u) = 0
      · exact h0
      · exact False.elim (Int.mul_ne_zero (by omega) h0 hz)
    rcases hw18.2.2.1.1 w' k' u with ⟨q2, hq2⟩
    rw [hz_prim, Int.zero_sub] at hq2
    have hq2_nn : -q2 ≥ 0 := by
      by_cases hneg : -q2 < 0
      · exfalso
        have hp_pos : Int.ofNat (2 ^ (5 * u)) > 0 :=
          Int.ofNat_lt.mpr (nat_pow_pos_of_pos 2 (by decide) (5 * u))
        have hlhs_neg : Int.ofNat (2 ^ (5 * u)) * (-q2) < 0 := Int.mul_neg_of_pos_of_neg hp_pos hneg
        have heq_neg : Int.ofNat (2 ^ (4 * u) * 3 ^ (18 * u) * k' ^ 18) = Int.ofNat (2 ^ (5 * u)) * (-q2) := by
          rw [Int.mul_neg]; omega
        rw [← heq_neg] at hlhs_neg
        exact absurd hlhs_neg (Int.not_lt.mpr (Int.natCast_nonneg _))
      · omega
    let qNat := (-q2).toNat
    have hqNat : (-q2) = Int.ofNat qNat := (Int.toNat_of_nonneg hq2_nn).symm
    have hm_ofNat : Int.ofNat (2 ^ (5 * u) * qNat) = Int.ofNat (2 ^ (5 * u)) * Int.ofNat qNat :=
      Int.natCast_mul (2 ^ (5 * u)) qNat
    have heq_int : Int.ofNat (2 ^ (4 * u) * 3 ^ (18 * u) * k' ^ 18) = Int.ofNat (2 ^ (5 * u) * qNat) := by
      rw [hm_ofNat, ← hqNat, Int.mul_neg]; omega
    have hnat_eq := Int.ofNat.inj heq_int
    let m_odd := k' / 2
    have hk'_2m : k' = 2 * m_odd := by dsimp [m_odd, k', g] at hk4 ⊢; omega
    have hm_odd : m_odd % 2 = 1 := by dsimp [m_odd, k', g] at hk4 ⊢; omega
    have hpow_odd : ∀ (a d : Nat), a % 2 = 1 -> (a ^ d) % 2 = 1 := by
      intro a d ha; induction d with
      | zero => rfl
      | succ d' ih => rw [Nat.pow_succ, Nat.mul_mod, ih, ha]
    have hlhs_split : 2 ^ (4 * u) * 3 ^ (18 * u) * k' ^ 18 =
        2 ^ (4 * u + 18) * (3 ^ (18 * u) * m_odd ^ 18) := by
      rw [hk'_2m, mul_pow_w19 2 m_odd 18, Nat.pow_add 2 (4 * u) 18]; ac_rfl
    have hrhs_split : 2 ^ (5 * u) * qNat =
        2 ^ (4 * u + 18) * (2 * (2 ^ (u - 19) * qNat)) := by
      have hexp : 5 * u = (4 * u + 18) + (1 + (u - 19)) := by omega
      rw [hexp, Nat.pow_add 2 (4 * u + 18) (1 + (u - 19)), Nat.pow_add 2 1 (u - 19), Nat.pow_one]
      ac_rfl
    rw [hlhs_split, hrhs_split] at hnat_eq
    have hev_prod := Nat.eq_of_mul_eq_mul_left (nat_pow_pos_of_pos 2 (by decide) (4 * u + 18)) hnat_eq
    have hm2_lhs : (3 ^ (18 * u) * m_odd ^ 18) % 2 = 1 := by
      rw [Nat.mul_mod, hpow_odd 3 (18 * u) rfl, hpow_odd m_odd 18 hm_odd]
    have hm2_rhs : (2 * (2 ^ (u - 19) * qNat)) % 2 = 0 := Nat.mul_mod_right 2 _
    rw [hev_prod, hm2_rhs] at hm2_lhs
    omega
  have hhor10 : ∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 -> u ≥ 1 ->
      intDet 12 (laurentTwoBaseT4U3Mat12 W K u) = 0 ->
      (u = 1 ∧ K = 4 * W) ∨
      (u ≥ 10 ∧ K ≠ 4 * W ∧ (K / Nat.gcd W K) % 2 = 0 ∧
        2 ^ ((u + 17) / 18) ≤ K / Nat.gcd W K ∧
        u < 18 * binBitLength (K / Nat.gcd W K)) := by
    intro W K u hW hK hu hz
    rcases hw18.2.2.2 W K u hW hK hu with ⟨hodd_nz, _, _, hhor6⟩
    rcases hhor6 hz with h1 | ⟨hu6, hne4, hpow, hbl⟩
    · exact Or.inl h1
    · right
      have hu10 : u ≥ 10 := by
        by_cases hle9 : u ≤ 9
        · exact False.elim (hu29 u W K (by omega) hle9 hW hK hz)
        · omega
      have hev_k : (K / Nat.gcd W K) % 2 = 0 := by
        by_cases hod : (K / Nat.gcd W K) % 2 = 1
        · exact False.elim (hodd_nz hod hz)
        · omega
      exact ⟨hu10, hne4, hev_k, hpow, hbl⟩
  have hv3_sq : ∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 ->
      (W / Nat.gcd W K) % 3 ≠ 0 -> (K / Nat.gcd W K) % 3 ≠ 0 ->
      intDet 12 (laurentTwoBaseT4U3Mat12 W K u) = 0 ->
      (u ≥ 1 -> 3 ^ ((u + 2) / 3 + 1) ∣ laurentTrop3ResonantQuad (W / Nat.gcd W K) (K / Nat.gcd W K) u) ∧
      (u ≥ 4 -> 27 ∣ laurentTrop3ResonantQuad (W / Nat.gcd W K) (K / Nat.gcd W K) u) ∧
      (u ≥ 10 -> 243 ∣ laurentTrop3ResonantQuad (W / Nat.gcd W K) (K / Nat.gcd W K) u) := by
    intro W K u hW hK hw3 hk3 hz
    let g := Nat.gcd W K
    have hg_pos : g ≥ 1 := Nat.gcd_pos_of_pos_left K hW
    let w' := W / g
    let k' := K / g
    have hW_eq : W = g * w' := by rw [Nat.mul_comm]; exact (Nat.div_mul_cancel (Nat.gcd_dvd_left W K)).symm
    have hK_eq : K = g * k' := by rw [Nat.mul_comm]; exact (Nat.div_mul_cancel (Nat.gcd_dvd_right W K)).symm
    have hz_prim : intDet 12 (laurentTwoBaseT4U3Mat12 w' k' u) = 0 := by
      rw [hW_eq, hK_eq, det12_t4u3_homog18_w19 u g w' k'] at hz
      have hg18_pos : intPowNat (g : Int) 18 > 0 := by
        rw [intPowNat_natCast_w19 g 18]; have := nat_pow_pos_of_pos g hg_pos 18; omega
      by_cases h0 : intDet 12 (laurentTwoBaseT4U3Mat12 w' k' u) = 0
      · exact h0
      · exact False.elim (Int.mul_ne_zero (by omega) h0 hz)
    have hcore_dvd : u ≥ 1 -> 3 ^ (u + 3) ∣ (laurentTrop3ResonantQuad w' k' u) ^ 3 := by
      intro hu1
      rcases det12_t4u3_3adic_congr_w19 w' k' u with ⟨q3, hq3⟩
      rw [hz_prim, Int.zero_sub] at hq3
      have h8u_nz : Int.ofNat (3 ^ (8 * u)) ≠ 0 := by
        intro h0; injection h0 with hn0
        have := nat_pow_pos_of_pos 3 (by decide) (8 * u); omega
      have h9u_mul : Int.ofNat (3 ^ (8 * u) * 3 ^ u) = Int.ofNat (3 ^ (8 * u)) * Int.ofNat (3 ^ u) :=
        Int.natCast_mul (3 ^ (8 * u)) (3 ^ u)
      have h9u_split : Int.ofNat (3 ^ (9 * u)) = Int.ofNat (3 ^ (8 * u)) * Int.ofNat (3 ^ u) := by
        rw [show 9 * u = 8 * u + u by omega, Nat.pow_add, h9u_mul]
      have htrop_eq : intDet 12 (laurentTrop3Mat12Explicit w' k' u) = Int.ofNat (3 ^ u) * (-q3) := by
        apply Int.eq_of_mul_eq_mul_left h8u_nz
        rw [Int.mul_neg, ← Int.neg_mul_eq_mul_neg]
        have : -(Int.ofNat (3 ^ (8 * u)) * intDet 12 (laurentTrop3Mat12Explicit w' k' u)) =
            Int.ofNat (3 ^ (8 * u)) * (Int.ofNat (3 ^ u) * q3) := by
          rw [hq3, h9u_split, Int.mul_assoc]
        omega
      have hcf := laurentTrop3Mat12Explicit_closed_form_w19 w' k' u hu1
      have h3u_mul : Int.ofNat (3 ^ 3) * Int.ofNat (3 ^ u) = Int.ofNat (3 ^ 3 * 3 ^ u) :=
        (Int.natCast_mul (3 ^ 3) (3 ^ u)).symm
      rw [htrop_eq, ← Int.mul_assoc 27, show (27 : Int) = Int.ofNat (3 ^ 3) by decide,
          h3u_mul, ← Nat.pow_add 3 3 u, show 3 + u = u + 3 by omega] at hcf
      have hq_nonneg : -q3 ≥ 0 := by
        by_cases hneg : -q3 < 0
        · exfalso
          have hp_pos : Int.ofNat (3 ^ (u + 3)) > 0 :=
            Int.ofNat_lt.mpr (nat_pow_pos_of_pos 3 (by decide) (u + 3))
          have hlhs_neg : Int.ofNat (3 ^ (u + 3)) * (-q3) < 0 := Int.mul_neg_of_pos_of_neg hp_pos hneg
          rw [hcf] at hlhs_neg
          exact absurd hlhs_neg (Int.not_lt.mpr (Int.natCast_nonneg _))
        · omega
      let qNat := (-q3).toNat
      have hqNat : (-q3) = Int.ofNat qNat := (Int.toNat_of_nonneg hq_nonneg).symm
      have hq_mul : Int.ofNat (3 ^ (u + 3)) * Int.ofNat qNat = Int.ofNat (3 ^ (u + 3) * qNat) :=
        (Int.natCast_mul (3 ^ (u + 3)) qNat).symm
      rw [hqNat, hq_mul] at hcf
      have hnat_eq := Int.ofNat.inj hcf.symm
      let F := 2 ^ (10 * u - 4) * w' ^ 8 * k' ^ 3 * ((2 ^ u - 1) * k' + (2 ^ u + 1) * w')
      have hd_FX : 3 ^ (u + 3) ∣ F * (laurentTrop3ResonantQuad w' k' u) ^ 3 := ⟨qNat, hnat_eq⟩
      have hmul3_nz : ∀ a b : Nat, a % 3 ≠ 0 -> b % 3 ≠ 0 -> (a * b) % 3 ≠ 0 := by
        intro a b ha hb; rw [Nat.mul_mod]
        rcases (by have := Nat.mod_lt a (by decide : 0 < 3); omega : a % 3 = 1 ∨ a % 3 = 2) with r1 | r1 <;>
        rcases (by have := Nat.mod_lt b (by decide : 0 < 3); omega : b % 3 = 1 ∨ b % 3 = 2) with r2 | r2 <;>
        (rw [r1, r2]; decide)
      have hpow3_nz : ∀ a d : Nat, a % 3 ≠ 0 -> (a ^ d) % 3 ≠ 0 := by
        intro a d ha; induction d with
        | zero => rw [Nat.pow_zero]; decide
        | succ d' ih => rw [Nat.pow_succ]; exact hmul3_nz _ _ ih ha
      have h2u_m3 : 2 ^ u % 3 = 1 ∨ 2 ^ u % 3 = 2 := by
        have := hpow3_nz 2 u (by decide)
        have := Nat.mod_lt (2 ^ u) (by decide : 0 < 3); omega
      have h2u_pos : 2 ^ u ≥ 2 := by simpa using pow2_mono_nat hu1
      have hlin_nz : ((2 ^ u - 1) * k' + (2 ^ u + 1) * w') % 3 ≠ 0 := by
        rcases h2u_m3 with hm1 | hm2
        · have hs1 : (2 ^ u - 1) % 3 = 0 := by omega
          have hs2 : (2 ^ u + 1) % 3 = 2 := by omega
          rw [Nat.add_mod, Nat.mul_mod (2 ^ u - 1), hs1, Nat.zero_mul, Nat.zero_mod, Nat.zero_add,
              Nat.mod_mod, Nat.mul_mod (2 ^ u + 1), hs2]
          change w' % 3 ≠ 0 at hw3
          rcases (by have := Nat.mod_lt w' (by decide : 0 < 3); omega : w' % 3 = 1 ∨ w' % 3 = 2) with hr | hr <;>
            (rw [hr]; decide)
        · have hs1 : (2 ^ u - 1) % 3 = 1 := by omega
          have hs2 : (2 ^ u + 1) % 3 = 0 := by omega
          rw [Nat.add_mod, Nat.mul_mod (2 ^ u + 1), hs2, Nat.zero_mul, Nat.zero_mod, Nat.add_zero,
              Nat.mod_mod, Nat.mul_mod (2 ^ u - 1), hs1, Nat.one_mul, Nat.mod_mod]
          exact hk3
      have hF_nz : F % 3 ≠ 0 :=
        hmul3_nz _ _
          (hmul3_nz _ _ (hmul3_nz _ _ (hpow3_nz 2 _ (by decide)) (hpow3_nz w' 8 hw3)) (hpow3_nz k' 3 hk3))
          hlin_nz
      exact cancel_coprime3_pow_dvd_w19 F hF_nz (u + 3) _ hd_FX
    have hall_u : ∀ hu1 : u ≥ 1, 3 ^ ((u + 2) / 3 + 1) ∣ laurentTrop3ResonantQuad w' k' u := by
      intro hu1
      have hc := hcore_dvd hu1
      let e := (u + 2) / 3
      have he_le : 3 * e + 1 ≤ u + 3 := by dsimp [e]; omega
      have hd_e : 3 ^ (3 * e + 1) ∣ (laurentTrop3ResonantQuad w' k' u) ^ 3 := by
        rcases hc with ⟨q, hq⟩
        exact ⟨3 ^ (u + 3 - (3 * e + 1)) * q, by
          rw [hq, ← Nat.mul_assoc, ← Nat.pow_add, show (3 * e + 1) + (u + 3 - (3 * e + 1)) = u + 3 by omega]⟩
      exact pow3_dvd_of_cube_dvd_w19 e _ hd_e
    refine ⟨hall_u, fun hu4 => ?_, fun hu10 => ?_⟩
    · rcases hall_u (by omega) with ⟨q, hq⟩
      exact ⟨3 ^ (((u + 2) / 3 + 1) - 3) * q, by
        rw [hq, show (27 : Nat) = 3 ^ 3 by decide, ← Nat.mul_assoc, ← Nat.pow_add,
            show 3 + (((u + 2) / 3 + 1) - 3) = (u + 2) / 3 + 1 by omega]⟩
    · rcases hall_u (by omega) with ⟨q, hq⟩
      exact ⟨3 ^ (((u + 2) / 3 + 1) - 5) * q, by
        rw [hq, show (243 : Nat) = 3 ^ 5 by decide, ← Nat.mul_assoc, ← Nat.pow_add,
            show 5 + (((u + 2) / 3 + 1) - 5) = (u + 2) / 3 + 1 by omega]⟩
  have hray_elim : ∀ (w0 k0 : Nat), w0 ≥ 1 -> k0 ≥ 1 ->
      Nat.gcd w0 k0 = 1 -> w0 % 3 ≠ 0 -> k0 % 3 ≠ 0 -> k0 % 4 = 2 -> k0 ≠ 4 * w0 ->
      checkResonantMod243UpTo18W19 w0 k0 = true ->
      ∀ (W u : Nat), W ≥ 1 -> u ≥ 1 ->
        intDet 12 (laurentTwoBaseT4U3Mat12 (w0 * W) (k0 * W) u) ≠ 0 := by
    intro w0 k0 hw0 hk0 hcop hw0_3 hk0_3 hk0_4 hne4 hchk W u hW hu hz
    have hW0_pos : w0 * W ≥ 1 := Nat.mul_le_mul hw0 hW
    have hK0_pos : k0 * W ≥ 1 := Nat.mul_le_mul hk0 hW
    have hgcd_eq : Nat.gcd (w0 * W) (k0 * W) = W := by
      rw [Nat.gcd_mul_right, hcop, Nat.one_mul]
    have hw'_eq : (w0 * W) / Nat.gcd (w0 * W) (k0 * W) = w0 := by
      rw [hgcd_eq]; exact Nat.mul_div_cancel w0 (by omega)
    have hk'_eq : (k0 * W) / Nat.gcd (w0 * W) (k0 * W) = k0 := by
      rw [hgcd_eq]; exact Nat.mul_div_cancel k0 (by omega)
    rcases hhor10 (w0 * W) (k0 * W) u hW0_pos hK0_pos hu hz with ⟨_, hk4w⟩ | ⟨hu10, _⟩
    · have h4 : k0 * W = (4 * w0) * W := by rw [hk4w]; ac_rfl
      exact hne4 (Nat.eq_of_mul_eq_mul_right (by omega : 0 < W) h4)
    · by_cases hu19 : u ≥ 19
      · exact hv2_cap18 (w0 * W) (k0 * W) u hW0_pos hK0_pos (by rw [hk'_eq]; exact hk0_4) hu19 hz
      · by_cases hev : u % 2 = 0
        · exact (hw18.2.2.2 (w0 * W) (k0 * W) u hW0_pos hK0_pos hu).2.1 hev
            (by rw [hw'_eq]; exact hw0_3)
            (by rw [hk'_eq]; exact hk0_3) hz
        · have hd243 := (hv3_sq (w0 * W) (k0 * W) u hW0_pos hK0_pos
              (by rw [hw'_eq]; exact hw0_3) (by rw [hk'_eq]; exact hk0_3) hz).2.2 hu10
          rw [hw'_eq, hk'_eq] at hd243
          have hm0 := Nat.mod_eq_zero_of_dvd hd243
          unfold checkResonantMod243UpTo18W19 at hchk
          rcases bool_and_split hchk with ⟨hc123, h17⟩
          rcases bool_and_split hc123 with ⟨hc12, h15⟩
          rcases bool_and_split hc12 with ⟨h11, h13⟩
          rcases (by omega : u = 11 ∨ u = 13 ∨ u = 15 ∨ u = 17) with rfl | rfl | rfl | rfl
          · exact bne_iff_ne.mp h11 hm0
          · exact bne_iff_ne.mp h13 hm0
          · exact bne_iff_ne.mp h15 hm0
          · exact bne_iff_ne.mp h17 hm0
  refine ⟨hu69, hu29, hv2_cap18, hhor10, ⟨det12_t4u3_3adic_congr_w19, laurentTrop3Mat12Explicit_closed_form_w19⟩, hv3_sq, ?_⟩
  intro W u hW hu
  rcases odd_resonant_mod243_rays_cert_w19 with ⟨hc52, hc114, hc122⟩
  refine ⟨hray_elim 5 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc52 W u hW hu, ?_, ?_⟩
  · simpa [Nat.one_mul] using
      hray_elim 1 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc114 W u hW hu
  · simpa [Nat.one_mul] using
      hray_elim 1 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc122 W u hW hu

-- ============================================================================
-- Section 2B: Symmetric Rank-4 Order-4 `16 × 16` `(T = 4, U = 4)` Two-Base
--             Determinants: Interior Cone Sign-Flip, Confluent & Liouville
--             Congruences, & Global `u = 1..5` Non-Vanishing (`W19_H2`, Branch P3.4)
-- ============================================================================

/-- Symmetric `4 × 4` two-base row grid `(r, s) = (i % 4, i / 4)` (`0 ≤ r, s < 4`). -/
def laurentRowsTwoBase16 (i : Fin 16) : Nat × Nat :=
  (i.val % 4, i.val / 4)

/-- Order-`4`, `4`-block column grid `(t, m * u) = (j % 4, (j / 4) * u)` (`0 ≤ t, m < 4`). -/
def laurentColsT4U4_16 (u : Nat) (j : Fin 16) : Nat × Nat :=
  laurentColsAllU 4 4 u j

/-- Symmetric rank-4 order-4 `16 × 16` `(T = 4, U = 4)` two-base Schneider–Laurent matrix. -/
def laurentTwoBaseT4U4Mat16 (W K u : Nat) : Fin 16 -> Fin 16 -> Int :=
  laurentInterpMat W K 16 laurentRowsTwoBase16 (laurentColsT4U4_16 u)

private def fastMat16T4U4FnW19 (W K u : Nat) (i j : Fin 16) : Int :=
  let r := i.val % 4; let s := i.val / 4
  let t := j.val % 4; let kc := (j.val / 4) * u
  let x := r * W + s * K
  let binv := match t with
    | 0 => 1 | 1 => x | 2 => (x * (x - 1)) / 2 | 3 => (x * (x - 1) * (x - 2)) / 6
    | _ => laurentInterpBinom x t
  ((binv * (2 ^ (r * kc) * 3 ^ (s * kc)) : Nat) : Int)

private theorem fastMat16T4U4FnW19_eq (W K u : Nat) :
    fastMat16T4U4FnW19 W K u = laurentTwoBaseT4U4Mat16 W K u := by
  have hst : ∀ n : Nat,
      laurentInterpBinom n 0 = 1 ∧ laurentInterpBinom n 1 = n ∧
      (n * (n - 1)) / 2 = laurentInterpBinom n 2 ∧
      (n * (n - 1) * (n - 2)) / 6 = laurentInterpBinom n 3 := by
    have hind : ∀ n : Nat,
        laurentInterpBinom n 0 = 1 ∧ laurentInterpBinom n 1 = n ∧
        2 * laurentInterpBinom n 2 + n = n * n ∧
        6 * laurentInterpBinom n 3 + 3 * (n * n) = n * n * n + 2 * n := by
      intro n; induction n with
      | zero => decide
      | succ n' ih =>
        rcases ih with ⟨h0, h1, h2, h3⟩
        refine ⟨rfl, by simp [laurentInterpBinom, h0, h1]; omega, ?_, ?_⟩
        · simp only [laurentInterpBinom, h1]
          change 2 * (n' + laurentInterpBinom n' 2) + (n' + 1) = (n' + 1) * (n' + 1)
          rw [Nat.mul_add 2, show (n' + 1) * (n' + 1) = n' * n' + 2 * n' + 1 by simp only [Nat.add_mul, Nat.mul_add]; omega]
          omega
        · simp only [laurentInterpBinom]
          change 6 * (laurentInterpBinom n' 2 + laurentInterpBinom n' 3) + 3 * ((n' + 1) * (n' + 1)) =
            (n' + 1) * (n' + 1) * (n' + 1) + 2 * (n' + 1)
          have hsq : (n' + 1) * (n' + 1) = n' * n' + 2 * n' + 1 := by simp only [Nat.add_mul, Nat.mul_add]; omega
          have hcub : (n' + 1) * (n' + 1) * (n' + 1) = n' * n' * n' + 3 * (n' * n') + 3 * n' + 1 := by
            rw [hsq]; simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul, Nat.mul_assoc 2 n' n']
            generalize n' * n' * n' = X3; generalize n' * n' = X2; omega
          rw [Nat.mul_add 6, show 6 * laurentInterpBinom n' 2 = 3 * (2 * laurentInterpBinom n' 2) from Nat.mul_assoc 3 2 _,
              hcub, hsq, Nat.mul_add 3 (n' * n' + 2 * n') 1, Nat.mul_add 3 (n' * n') (2 * n')]
          generalize 6 * laurentInterpBinom n' 3 = C3 at h3 ⊢
          generalize 2 * laurentInterpBinom n' 2 = C2 at h2 ⊢
          generalize n' * n' * n' = X3 at h3 ⊢
          generalize n' * n' = X2 at h2 h3 ⊢
          omega
    intro n; rcases hind n with ⟨h0, h1, h2, h3⟩
    refine ⟨h0, h1, ?_, ?_⟩
    · have hm2 : n * (n - 1) = 2 * laurentInterpBinom n 2 := by
        cases n with
        | zero => exact h2.symm
        | succ m =>
          have hs : (m + 1) * m = (m + 1) * (m + 1) - (m + 1) := by
            simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; generalize m * m = M2; omega
          simp only [Nat.add_sub_cancel]
          generalize laurentInterpBinom (m + 1) 2 = C2 at h2 ⊢
          generalize (m + 1) * (m + 1) = X2 at h2 hs
          generalize (m + 1) * m = P2 at hs ⊢
          omega
      generalize laurentInterpBinom n 2 = C2 at hm2 ⊢
      generalize n * (n - 1) = P2 at hm2 ⊢
      omega
    · have hm3 : n * (n - 1) * (n - 2) = 6 * laurentInterpBinom n 3 := by
        cases n with
        | zero => exact h3.symm
        | succ m =>
          cases m with
          | zero => simp at h3 ⊢; omega
          | succ q =>
            have h21 : (q + 2) * (q + 1) = q * q + 3 * q + 2 := by simp only [Nat.add_mul, Nat.mul_add]; omega
            have h22 : (q + 2) * (q + 2) = q * q + 4 * q + 4 := by simp only [Nat.add_mul, Nat.mul_add]; omega
            have hp1 : (q + 2) * (q + 1) * q = q * q * q + 3 * (q * q) + 2 * q := by
              rw [h21]; simp only [Nat.add_mul, Nat.mul_assoc 3 q q]
            have hp2 : (q + 2) * (q + 2) * (q + 2) = q * q * q + 6 * (q * q) + 12 * q + 8 := by
              rw [h22]; simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc 4 q q]
              generalize q * q * q = Q3; generalize q * q = Q2; omega
            have hq3 : (q + 2) * (q + 1) * q + 3 * ((q + 2) * (q + 2)) =
                (q + 2) * (q + 2) * (q + 2) + 2 * (q + 2) := by
              rw [hp1, hp2, h22]; generalize q * q * q = Q3; generalize q * q = Q2; omega
            simp only [Nat.add_sub_cancel]
            change (q + 2) * (q + 1) * q = 6 * laurentInterpBinom (q + 2) 3
            generalize (q + 2) * (q + 1) * q = P3 at hq3 ⊢
            generalize laurentInterpBinom (q + 2) 3 = C3 at h3 ⊢
            generalize (q + 2) * (q + 2) * (q + 2) = X3 at h3 hq3
            generalize (q + 2) * (q + 2) = X2 at h3 hq3
            omega
      generalize laurentInterpBinom n 3 = C3 at hm3 ⊢
      generalize n * (n - 1) * (n - 2) = P3 at hm3 ⊢
      omega
  funext i j
  unfold fastMat16T4U4FnW19 laurentTwoBaseT4U4Mat16 laurentInterpMat laurentInterpEntry
    laurentRowsTwoBase16 laurentColsT4U4_16 laurentColsAllU
  dsimp only
  rcases hst (i.val % 4 * W + i.val / 4 * K) with ⟨hb0, hb1, hb2, hb3⟩
  have ht_lt : j.val % 4 < 4 := Nat.mod_lt j.val (by decide)
  rcases (by omega : j.val % 4 = 0 ∨ j.val % 4 = 1 ∨ j.val % 4 = 2 ∨ j.val % 4 = 3) with h | h | h | h <;>
  (simp only [h, hb0, hb1, hb2, hb3]; apply congrArg Int.ofNat; ac_rfl)

private def uT4U4_351TblW19 : List (List Int) :=
  [[1, 0, 0, 0, -81, 135, -1080, 5400, -806, -220, 270, 0, 36936, -2994840, 22812840, -662661000],
   [0, 1, -1, 5, -23, -31, 16, -600, 110, 4, 162, 0, -12312, 2142072, -21385944, 683422920],
   [0, 0, 1, -6, -3, 5, 76, -276, 46, -4, 90, 288, -7272, 384408, -8779752, 509917032],
   [0, 0, 0, 3, -3, -21, -6, 108, -6, -12, 54, 216, -2376, -119448, -2533032, 214658424],
   [0, 0, 0, 0, 81, -135, 1080, -5400, 783, 270, -675, 0, -23142, -467070, 13308930, -406510650],
   [0, 0, 0, 0, 0, 39, -254, 1660, -266, -43, -129, -180, 21360, -2497206, 27341892, -1121188230],
   [0, 0, 0, 0, 0, 0, 29, -353, 49, 20, -39, -288, -138, 684426, -1340910, -194390478],
   [0, 0, 0, 0, 0, 0, 0, 39, -6, -3, 9, 54, -252, -96462, 32724, 43675254],
   [0, 0, 0, 0, 0, 0, 0, 0, 23, -50, 405, 0, -13851, 3495825, -37620315, 1302494175],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 3, -31, 170, -388, -601127, 2624874, 168698745],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -36, 282, 85710, -213771, -46100403],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, -33, -6222, 18666, 3652479],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57, -33915, 1498545, -233322525],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1521, -130372, 30074045],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5917, -2702343],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 127299]]

private def uT4U4_471TblW19 : List (List Int) :=
  [[1, 0, 0, 0, -128, 112, -8624, 1786400, -64436952, 8586480, -6840565200, 64370607840, 795363120487584, -317393153755547184, 197649693053237727792, -3079494458412249060866592],
   [0, 1, -3, 7, -27, -9, 9, -142086, 5628204, -1094364, 1027600044, -576847662888, 55775052447912, 110267793664529148, 17237869017875391996, -5028847579433072768007096],
   [0, 0, 2, -6, -2, 4, 452, -61760, 2280660, -503736, 225639816, -10862239632, -37428394390128, 22790769269142168, -31874709849253286184, 3584952914606330010457680],
   [0, 0, 0, 2, -2, -5, -71, 17894, -333768, -62484, -152546796, 62998733352, -19084108354920, -943356019103820, -21136680787359126780, 2439677655009509462371224],
   [0, 0, 0, 0, 128, -112, 8624, -1786400, 62967038, -6945260, 6071168740, 1413104206360, -1114061966445912, 82857499278316812, -261635960972893217676, 17535210185877639071333496],
   [0, 0, 0, 0, 0, 18, -1614, 430731, -15976629, 2584593, -2076087653, 496871887876, 105204225908592, -158912693242268367, 53382465753860616336, -2474415694346920559753322],
   [0, 0, 0, 0, 0, 0, 152, -69728, 2258831, -181154, 468996774, -207851814568, 34113575884944, 24628161230447946, 41127218349200699832, -6287488116350651119856964],
   [0, 0, 0, 0, 0, 0, 0, 5577, -191428, 7927, -38664047, 21055906104, -4203515057748, -2407220012554137, -4150109250979935954, 721840620008003075197794],
   [0, 0, 0, 0, 0, 0, 0, 0, 1469914, -1641220, 769396460, -1477474814200, 317453274373576, 237705319153870624, 39702745551321902518, -7924768600965929248030068],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 59526, -135312746, 257969544847, -74054819062629, -26137624030871351, -49063695045104621757, 8658565226735777798469871],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9235260, -27476362930, 8592558568774, 2683423659938346, 5425316081121156162, -1147562440165931003602170],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1413050495, -495197867117, -137962751408393, -226343444856652406, 60462352162318910679101],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1245571584752, -3169664676640252, 24283522368333587366, -6530947126499460762436836],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 100013179723720, -1634412782772077625, 633893848817901871717357],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 56986263370257010, -42089819690976005639886],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1434724628080800005231]]

private def uT4U4_141TblW19 : List (List Int) :=
  [[1, 0, 0, 0, -1, 11, -2, 76, -636, 3528, -6300, 0, -3780, 13149864, 112761612, 76280832],
   [0, 1, 0, 0, -1, 5, 4, -14, 84, -312, 1164, -432, 10044, -1587384, -22290228, 36067680],
   [0, 0, 1, 0, -1, -1, 2, -16, 156, -1104, 1776, 96, -972, -3861864, -32477004, -28885248],
   [0, 0, 0, 1, -1, -7, -8, 22, -132, 432, -1080, 96, -3132, 2568024, 25476228, 1346976],
   [0, 0, 0, 0, 1, -11, 2, -76, 631, -3388, 5642, 476, -6747, -12741210, -105634191, -107069016],
   [0, 0, 0, 0, 0, 3, -3, 45, -365, 2026, -4034, 320, -9285, 7683582, 73229307, 7519740],
   [0, 0, 0, 0, 0, 0, 2, -22, 157, -690, 1659, -308, 7671, -2980230, -29502477, 8715696],
   [0, 0, 0, 0, 0, 0, 0, 6, -41, 128, -337, 90, -2085, 503406, 4604883, -2125764],
   [0, 0, 0, 0, 0, 0, 0, 0, 5, -140, 658, -476, 10522, -390256, -7433488, 33083436],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 17, -178, 186, -4082, 61732, 592748, -8109540],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27, -50, 1075, 32820, 658236, 958116],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, -149, -12574, -192178, -2884],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, -18398, 306067, -2295252],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1757, -93399, 652059],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12671, -125040],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12341]]

set_option exponentiation.threshold 2048 in
private theorem t4u4_351_cert_w19 :
    checkULDetBoolW19 16 (fastMat16T4U4FnW19 3 5 1) uT4U4_351TblW19
      (-346869345187079025627401176785813504) = true := by decide

set_option exponentiation.threshold 2048 in
private theorem t4u4_471_cert_w19 :
    checkULDetBoolW19 16 (fastMat16T4U4FnW19 4 7 1) uT4U4_471TblW19
      223551144063582960394327584357593948160000 = true := by decide

set_option exponentiation.threshold 2048 in
private theorem t4u4_141_cert_w19 :
    checkULDetBoolW19 16 (fastMat16T4U4FnW19 1 4 1) uT4U4_141TblW19
      (-5480111512833949589330460672000000000000000) = true := by decide

-- `N = 16` Pure-Power Stirling & Degree-24 Homogeneity + Mod-`p` UL Engine:
private def apow16UW19 (u : Nat) (w k : Int) (i j : Fin 16) : Int :=
  let r := i.val % 4; let s := i.val / 4
  let t := j.val % 4; let m := j.val / 4
  intPowNat ((r : Int) * w + (s : Int) * k) t *
    ((2 ^ (r * (m * u)) * 3 ^ (s * (m * u)) : Nat) : Int)

private theorem stirling_20736_det16_t4u4_u_w19 (u W K : Nat) :
    20736 * intDet 16 (laurentTwoBaseT4U4Mat16 W K u) =
      intDet 16 (apow16UW19 u (W : Int) (K : Int)) := by
  have heq_in : laurentTwoBaseT4U4Mat16 W K u =
      (fun i j => ((laurentInterpBinom (i.val % 4 * W + i.val / 4 * K) (j.val % 4) : Nat) : Int) *
        ((2 ^ (i.val % 4 * ((j.val / 4) * u)) * 3 ^ (i.val / 4 * ((j.val / 4) * u)) : Nat) : Int)) := by
    funext i j
    unfold laurentTwoBaseT4U4Mat16 laurentInterpMat laurentInterpEntry
      laurentRowsTwoBase16 laurentColsT4U4_16 laurentColsAllU
    dsimp only; rw [← Int.natCast_mul]; apply congrArg Int.ofNat; ac_rfl
  have hs4 := stirling_order4_blocks_w19 4
    (fun i => i.val % 4 * W + i.val / 4 * K)
    (fun i m => ((2 ^ (i.val % 4 * (m * u)) * 3 ^ (i.val / 4 * (m * u)) : Nat) : Int))
  rw [show ((12 ^ 4 : Nat) : Int) = 20736 by decide] at hs4
  change 20736 * intDet 16 (fun i j =>
      ((laurentInterpBinom (i.val % 4 * W + i.val / 4 * K) (j.val % 4) : Nat) : Int) *
        ((2 ^ (i.val % 4 * ((j.val / 4) * u)) * 3 ^ (i.val / 4 * ((j.val / 4) * u)) : Nat) : Int)) =
    intDet 16 (fun i j =>
      intPowNat ((i.val % 4 * W + i.val / 4 * K : Nat) : Int) (j.val % 4) *
        ((2 ^ (i.val % 4 * ((j.val / 4) * u)) * 3 ^ (i.val / 4 * ((j.val / 4) * u)) : Nat) : Int)) at hs4
  rw [heq_in, hs4]
  exact congrArg (intDet 16) (by funext i j; simp [apow16UW19, Int.natCast_add, Int.natCast_mul])

private def degPref16W19 : Nat -> Nat
  | 0 => 0
  | c + 1 => (c % 4) + degPref16W19 c

private theorem apow16_homog24_w19 (u : Nat) (w k g : Int) :
    intDet 16 (apow16UW19 u (g * w) (g * k)) =
      intPowNat g 24 * intDet 16 (apow16UW19 u w k) := by
  let colSc (c_done : Nat) (i j : Fin 16) : Int :=
    if j.val < c_done then intPowNat g (j.val % 4) * apow16UW19 u w k i j
    else apow16UW19 u w k i j
  have hmul_pow : ∀ (a b : Int) (d : Nat), intPowNat (a * b) d = intPowNat a d * intPowNat b d := by
    intro a b d; induction d with
    | zero => simp [intPowNat]
    | succ d' ih => simp only [intPowNat, ih]; ac_rfl
  have hsc_step : ∀ (c : Nat) (hc : c < 16),
      intDet 16 (colSc (c + 1)) = intPowNat g (c % 4) * intDet 16 (colSc c) := by
    intro c hc
    let jc : Fin 16 := ⟨c, hc⟩
    have heq_m : colSc (c + 1) = (fun i j =>
        if j = jc then intPowNat g (c % 4) * colSc c i jc else colSc c i j) := by
      funext i j
      by_cases hj : j = jc
      · subst hj; dsimp [colSc, jc]
        rw [ite_true_of_w10 (Nat.lt_succ_self c), ite_true_of_w10 rfl, ite_false_of_w10 (Nat.lt_irrefl c)]
      · dsimp [colSc]; rw [ite_false_of_w10 hj]
        have hjv : j.val ≠ c := fun hv => hj (Fin.ext hv)
        by_cases hlt : j.val < c
        · rw [ite_true_of_w10 (by omega), ite_true_of_w10 hlt]
        · rw [ite_false_of_w10 (by omega), ite_false_of_w10 hlt]
    rw [heq_m]; exact intDet_col_scale (intPowNat g (c % 4)) 16 jc (colSc c)
  have hind : ∀ n : Nat, n ≤ 16 ->
      intDet 16 (colSc n) = intPowNat g (degPref16W19 n) * intDet 16 (colSc 0) := by
    intro n; induction n with
    | zero => intro _; simp [degPref16W19, intPowNat]
    | succ n' ihn =>
      intro hn; rw [hsc_step n' hn, ihn (Nat.le_of_lt hn), ← Int.mul_assoc, ← intPowNat_add]; rfl
  have h16 := hind 16 (Nat.le_refl 16)
  have hdeg24 : degPref16W19 16 = 24 := by decide
  have h0 : colSc 0 = apow16UW19 u w k := by funext i j; simp [colSc]
  have h16_eq : colSc 16 = apow16UW19 u (g * w) (g * k) := by
    funext i j
    dsimp [colSc]; rw [ite_true_of_w10 j.isLt]
    unfold apow16UW19; dsimp only
    have hlin : ((i.val % 4 : Nat) : Int) * (g * w) + ((i.val / 4 : Nat) : Int) * (g * k) =
        g * (((i.val % 4 : Nat) : Int) * w + ((i.val / 4 : Nat) : Int) * k) := by
      rw [Int.mul_add]; congr 1 <;> ac_rfl
    rw [hlin, hmul_pow, Int.mul_assoc]
  rw [hdeg24, h0, h16_eq] at h16
  exact h16

private theorem det16_t4u4_homog24_w19 (u g W K : Nat) :
    intDet 16 (laurentTwoBaseT4U4Mat16 (g * W) (g * K) u) =
      intPowNat (g : Int) 24 * intDet 16 (laurentTwoBaseT4U4Mat16 W K u) := by
  have h1 := stirling_20736_det16_t4u4_u_w19 u (g * W) (g * K)
  have h2 := stirling_20736_det16_t4u4_u_w19 u W K
  have hm : 20736 * intDet 16 (laurentTwoBaseT4U4Mat16 (g * W) (g * K) u) =
      20736 * (intPowNat (g : Int) 24 * intDet 16 (laurentTwoBaseT4U4Mat16 W K u)) := by
    rw [h1]; simp only [Int.natCast_mul]
    rw [apow16_homog24_w19 u (W : Int) (K : Int) (g : Int), ← h2]
    exact Int.mul_left_comm (intPowNat (g : Int) 24) 20736 _
  exact Int.eq_of_mul_eq_mul_left (by decide : (20736 : Int) ≠ 0) hm

private def buildRow16NatW19 (f : Nat -> Nat) : List Nat :=
  [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15]

private def buildMat16NatW19 (f : Nat -> Nat -> Nat) : List (List Nat) :=
  [buildRow16NatW19 (f 0), buildRow16NatW19 (f 1), buildRow16NatW19 (f 2), buildRow16NatW19 (f 3),
   buildRow16NatW19 (f 4), buildRow16NatW19 (f 5), buildRow16NatW19 (f 6), buildRow16NatW19 (f 7),
   buildRow16NatW19 (f 8), buildRow16NatW19 (f 9), buildRow16NatW19 (f 10), buildRow16NatW19 (f 11),
   buildRow16NatW19 (f 12), buildRow16NatW19 (f 13), buildRow16NatW19 (f 14), buildRow16NatW19 (f 15)]

private theorem natAt1DW19_buildRow16 (f : Nat -> Nat) (k : Nat) (hk : k < 16) :
    natAt1DW19 (buildRow16NatW19 f) k = f k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨
      k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem natRowAtW19_buildMat16 (f : Nat -> Nat -> Nat) (r : Nat) (hr : r < 16) :
    natRowAtW19 (buildMat16NatW19 f) r = buildRow16NatW19 (fun c => f r c) := by
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨
      r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem natAt2DW19_buildMat16 (f : Nat -> Nat -> Nat) (r c : Nat) (hr : r < 16) (hc : c < 16) :
    natAt2DW19 (buildMat16NatW19 f) r c = f r c := by
  unfold natAt2DW19; rw [natRowAtW19_buildMat16 f r hr, natAt1DW19_buildRow16 _ c hc]

private def swapOneMat16NatW19 (pNat c1 c2 : Nat) (M : List (List Nat)) : List (List Nat) :=
  if Nat.ble (c1 + 1) 16 && Nat.ble (c2 + 1) 16 && (c1 != c2) then
    buildMat16NatW19 (fun r j =>
      if j == c1 then natAt2DW19 M r c2
      else if j == c2 then natSubModPW19 pNat 0 (natAt2DW19 M r c1)
      else natAt2DW19 M r j)
  else M

private def applySignedSwapsMat16NatW19 (pNat : Nat) :
    List (Nat × Nat) -> List (List Nat) -> List (List Nat)
  | [], M => M
  | (c1, c2) :: rest, M =>
    applySignedSwapsMat16NatW19 pNat rest (swapOneMat16NatW19 pNat c1 c2 M)

private def checkRawMatULModP16BoolW19 (pNat : Nat) (a0 : List (List Nat))
    (cert : List (Nat × Nat) × List (List Nat)) : Bool :=
  let apRows := applySignedSwapsMat16NatW19 pNat cert.1 a0
  let uCols := buildMat16NatW19 (fun c r => uStrictNatValW19 cert.2 r c)
  allNatLoop2W19 (fun r =>
    let row_r := natRowAtW19 apRows r
    allNatLoop2W19 (fun c =>
      if Nat.ble (r + 1) c then
        dotListsPrefixW19 (c + 1) row_r (natRowAtW19 uCols c) % pNat == 0
      else true) 16) 16 &&
  (natDiagProdModPW19 pNat apRows uCols 16 != 0)

private theorem checkRawMatULModP16BoolW19_sound (pNat : Nat) (hp : pNat ≥ 2)
    (a0 : List (List Nat)) (cert : List (Nat × Nat) × List (List Nat))
    (h : checkRawMatULModP16BoolW19 pNat a0 cert = true) :
    intDet 16 (fun i j => (natAt2DW19 a0 i.val j.val : Int)) % (pNat : Int) ≠ 0 := by
  let p : Int := (pNat : Int)
  have hp1 : pNat ≥ 1 := by omega
  let matOf (T : List (List Nat)) (i j : Fin 16) : Int := (natAt2DW19 T i.val j.val : Int)
  have hd_trans : ∀ a b c : Int, p ∣ (a - b) -> p ∣ (b - c) -> p ∣ (a - c) := by
    intro a b c ⟨q1, h1⟩ ⟨q2, h2⟩; exact ⟨q1 + q2, by rw [Int.mul_add]; omega⟩
  have hd_sub_r : ∀ a b : Nat, p ∣ (((a : Int) - (b : Int)) - (natSubModPW19 pNat a b : Int)) := by
    intro a b
    rcases natSubModPW19_dvd_int pNat a b hp1 with ⟨q, hq⟩
    exact ⟨-q, by dsimp [p]; rw [Int.mul_neg]; omega⟩
  let apRows := applySignedSwapsMat16NatW19 pNat cert.1 a0
  let uCols := buildMat16NatW19 (fun c r => uStrictNatValW19 cert.2 r c)
  have hd_swaps : ∀ (swaps : List (Nat × Nat)) (M : List (List Nat)),
      p ∣ (intDet 16 (matOf M) - intDet 16 (matOf (applySignedSwapsMat16NatW19 pNat swaps M))) := by
    intro swaps; induction swaps with
    | nil => intro M; exact ⟨0, by simp [applySignedSwapsMat16NatW19]⟩
    | cons sw rest ih =>
      rcases sw with ⟨c1, c2⟩
      intro M
      unfold applySignedSwapsMat16NatW19
      let M' := swapOneMat16NatW19 pNat c1 c2 M
      have hd_one : p ∣ (intDet 16 (matOf M) - intDet 16 (matOf M')) := by
        dsimp only [M']; unfold swapOneMat16NatW19
        by_cases hc : c1 < 16 ∧ c2 < 16 ∧ c1 ≠ c2
        · have hcond : (Nat.ble (c1 + 1) 16 && Nat.ble (c2 + 1) 16 && (c1 != c2)) = true := by
            rw [Nat.ble_eq.mpr hc.1, Nat.ble_eq.mpr hc.2.1, bne_iff_ne.mpr hc.2.2]; rfl
          change p ∣ (intDet 16 (matOf M) - intDet 16 (matOf
            (if (Nat.ble (c1 + 1) 16 && Nat.ble (c2 + 1) 16 && (c1 != c2)) = true then
              buildMat16NatW19 (fun r j =>
                if j == c1 then natAt2DW19 M r c2
                else if j == c2 then natSubModPW19 pNat 0 (natAt2DW19 M r c1)
                else natAt2DW19 M r j)
            else M)))
          rw [ite_true_of_w10 hcond]
          let fc1 : Fin 16 := ⟨c1, hc.1⟩
          let fc2 : Fin 16 := ⟨c2, hc.2.1⟩
          let S_int (i j : Fin 16) : Int :=
            if j = fc1 then matOf M i fc2 else if j = fc2 then -(matOf M i fc1) else matOf M i j
          rw [← signedColSwap_det_w19 16 fc1 fc2 (fun h => hc.2.2 (congrArg Fin.val h)) (matOf M)]
          apply intDet_congr_dvd p 16 S_int
          intro i j; dsimp only [S_int, matOf]
          rw [natAt2DW19_buildMat16 _ i.val j.val i.isLt j.isLt]
          by_cases hj1 : j = fc1
          · subst hj1; dsimp only [fc1, fc2]
            have hb1 : (c1 == c1) = true := beq_iff_eq.mpr rfl
            simp only [hb1, ↓reduceIte, Int.sub_self]; exact ⟨0, (Int.mul_zero p).symm⟩
          · have hb1f : (j.val == c1) = false := beq_false_of_ne (fun hv => hj1 (Fin.ext hv))
            by_cases hj2 : j = fc2
            · subst hj2; have hb2 : (fc2.val == c2) = true := beq_iff_eq.mpr rfl
              simp only [hj1, hb1f, hb2, Bool.false_eq_true, ↓reduceIte]
              simpa using hd_sub_r 0 (natAt2DW19 M i.val c1)
            · have hb2f : (j.val == c2) = false := beq_false_of_ne (fun hv => hj2 (Fin.ext hv))
              simp only [hj1, hj2, hb1f, hb2f, Bool.false_eq_true, ↓reduceIte, Int.sub_self]
              exact ⟨0, (Int.mul_zero p).symm⟩
        · have hcond : ¬ ((Nat.ble (c1 + 1) 16 && Nat.ble (c2 + 1) 16 && (c1 != c2)) = true) := by
            intro htrue; rcases bool_and_split htrue with ⟨h12, h3⟩
            rcases bool_and_split h12 with ⟨h1, h2⟩
            exact hc ⟨Nat.ble_eq.mp h1, Nat.ble_eq.mp h2, bne_iff_ne.mp h3⟩
          change p ∣ (intDet 16 (matOf M) - intDet 16 (matOf
            (if (Nat.ble (c1 + 1) 16 && Nat.ble (c2 + 1) 16 && (c1 != c2)) = true then _ else M)))
          rw [ite_false_of_w10 hcond]; exact ⟨0, by simp⟩
      exact hd_trans _ _ _ hd_one (ih M')
  let Ap := matOf apRows
  let U (r c : Fin 16) : Int := (uStrictNatValW19 cert.2 r.val c.val : Int)
  let prodFull (r c : Fin 16) : Int := intSumPrefix 16 (fun k_f => Ap r k_f * U k_f c) 16
  let prodTrunc (r c : Fin 16) : Int := intSumPrefix 16 (fun k_f => Ap r k_f * U k_f c) (c.val + 1)
  unfold checkRawMatULModP16BoolW19 at h
  rcases bool_and_split h with ⟨hsup_b, hdiag_nz_b⟩
  have hdiag_nz := bne_iff_ne.mp hdiag_nz_b
  have hupper : ∀ r c : Fin 16, c.val < r.val -> U r c = 0 := by
    intro r c hlt; dsimp [U, uStrictNatValW19]; rw [ite_true_of_w10 (Nat.ble_eq.mpr hlt)]; rfl
  have hu_diag1 : intDiagProdPrefixW19 16 U 16 = 1 := by
    have hst : ∀ m : Nat, m ≤ 16 -> intDiagProdPrefixW19 16 U m = 1 := by
      intro m hm; induction m with
      | zero => rfl
      | succ m' ih =>
        have hm_lt : m' < 16 := hm
        simp only [intDiagProdPrefixW19, hm_lt, dite_true, ih (Nat.le_of_lt hm), Int.one_mul]
        dsimp [U, uStrictNatValW19]
        have hnlt : ¬ (Nat.ble (m' + 1) m' = true) := fun hb => Nat.lt_irrefl m' (Nat.ble_eq.mp hb)
        rw [ite_false_of_w10 hnlt, ite_true_of_w10 (beq_iff_eq.mpr rfl)]; rfl
    exact hst 16 (Nat.le_refl 16)
  have htrunc_eq : prodFull = prodTrunc := by
    funext r c; dsimp [prodFull, prodTrunc]
    have hst : ∀ d : Nat, c.val + 1 + d ≤ 16 ->
        intSumPrefix 16 (fun k_f => Ap r k_f * U k_f c) (c.val + 1 + d) =
          intSumPrefix 16 (fun k_f => Ap r k_f * U k_f c) (c.val + 1) := by
      intro d hd; induction d with
      | zero => rfl
      | succ d' ih =>
        rw [Nat.add_succ]; have hlt : c.val + 1 + d' < 16 := hd
        conv => lhs; unfold intSumPrefix
        simp only [hlt, dite_true]
        rw [ih (by omega), hupper ⟨c.val + 1 + d', hlt⟩ c (by dsimp; omega), Int.mul_zero, Int.add_zero]
    have h16 := hst (16 - (c.val + 1)) (by have := c.isLt; omega)
    rwa [show c.val + 1 + (16 - (c.val + 1)) = 16 by have := c.isLt; omega] at h16
  have hdet_prod : intDet 16 prodTrunc = intDet 16 Ap := by
    rw [← htrunc_eq]; have hm := intDet_mul_upper_tri_w19 16 Ap U hupper
    dsimp only [prodFull]; rw [hm, hu_diag1, Int.one_mul]
  have hdot_eq : ∀ (r c : Fin 16) (n : Nat), n ≤ 16 ->
      ((dotPrefixNatW19 (natRowAtW19 apRows r.val) (natRowAtW19 uCols c.val) n : Nat) : Int) =
        intSumPrefix 16 (fun k_f => Ap r k_f * U k_f c) n := by
    intro r c n hn; induction n with
    | zero => rfl
    | succ n' ih =>
      have hn_lt : n' < 16 := hn
      simp only [dotPrefixNatW19, intSumPrefix, hn_lt, dite_true,
                 Int.natCast_add, Int.natCast_mul, ih (Nat.le_of_lt hn)]
      have hu_at : natAt1DW19 (natRowAtW19 uCols c.val) n' = uStrictNatValW19 cert.2 n' c.val := by
        dsimp only [uCols]; rw [natRowAtW19_buildMat16 _ c.val c.isLt, natAt1DW19_buildRow16 _ n' hn_lt]
      rw [hu_at]; rfl
  let prodLow (r c : Fin 16) : Int := if r.val < c.val then 0 else prodTrunc r c
  have hd_low : p ∣ (intDet 16 prodTrunc - intDet 16 prodLow) := by
    apply intDet_congr_dvd p 16 prodTrunc prodLow
    intro r c; dsimp [prodLow]
    by_cases hrc : r.val < c.val
    · rw [ite_true_of_w10 hrc, Int.sub_zero]
      have hr_b := allNatLoop2W19_spec _ 16 hsup_b r.val r.isLt
      have hc_b := allNatLoop2W19_spec _ 16 hr_b c.val c.isLt
      rw [Nat.ble_eq.mpr hrc, dotListsPrefixW19_eq] at hc_b
      have hm_nat := beq_iff_eq.mp hc_b
      have hm_int : prodTrunc r c % p = 0 := by
        dsimp only [prodTrunc, p]
        rw [← hdot_eq r c (c.val + 1) (by have := c.isLt; omega)]
        exact (Int.natCast_emod _ pNat).symm.trans (by rw [hm_nat]; rfl)
      exact Int.dvd_of_emod_eq_zero hm_int
    · rw [ite_false_of_w10 hrc, Int.sub_self]; exact ⟨0, by simp⟩
  have hdet_low : intDet 16 prodLow = intDiagProdPrefixW19 16 prodTrunc 16 := by
    rw [intDet_lower_tri_w19 16 prodLow (fun r c hrc => by dsimp [prodLow]; rw [ite_true_of_w10 hrc])]
    have hst : ∀ m : Nat, m ≤ 16 -> intDiagProdPrefixW19 16 prodLow m = intDiagProdPrefixW19 16 prodTrunc m := by
      intro m hm; induction m with
      | zero => rfl
      | succ m' ih =>
        have hm_lt : m' < 16 := hm
        simp only [intDiagProdPrefixW19, hm_lt, dite_true, ih (Nat.le_of_lt hm)]
        dsimp [prodLow]; rw [ite_false_of_w10 (Nat.lt_irrefl m')]
    exact hst 16 (Nat.le_refl 16)
  have hdiag_eq : ∀ m : Nat, m ≤ 16 ->
      ((natDiagProdModPW19 pNat apRows uCols m : Nat) : Int) =
        intDiagProdPrefixW19 16 prodTrunc m % p := by
    intro m hm; induction m with
    | zero => exact Int.natCast_emod 1 pNat
    | succ m' ih =>
      have hm_lt : m' < 16 := hm
      let fm : Fin 16 := ⟨m', hm_lt⟩
      simp only [natDiagProdModPW19, dotListsPrefixW19_eq]
      rw [Int.natCast_emod, Int.natCast_mul, Int.natCast_emod,
          ih (Nat.le_of_lt hm), hdot_eq fm fm (m' + 1) hm]
      simp only [intDiagProdPrefixW19, hm_lt, dite_true]
      exact (Int.mul_emod _ _ p).symm
  have hd_ap_diag : p ∣ (intDet 16 Ap - intDiagProdPrefixW19 16 prodTrunc 16) := by
    rw [← hdet_prod, ← hdet_low]; exact hd_low
  have hd_tot := hd_trans _ _ _ (hd_swaps cert.1 a0) hd_ap_diag
  rcases hd_tot with ⟨qt, hqt⟩
  intro hz_mod
  have hdiag_mod0 : intDiagProdPrefixW19 16 prodTrunc 16 % p = 0 := by
    have heq : intDiagProdPrefixW19 16 prodTrunc 16 =
        intDet 16 (matOf a0) + p * (-qt) := by
      rw [Int.mul_neg]; omega
    rw [heq, Int.add_emod, hz_mod, Int.zero_add, Int.mul_emod_right, Int.zero_emod]
  have hnat0_int : ((natDiagProdModPW19 pNat apRows uCols 16 : Nat) : Int) = ((0 : Nat) : Int) := by
    rw [hdiag_eq 16 (Nat.le_refl 16), hdiag_mod0]; rfl
  exact hdiag_nz (Int.ofNat.inj hnat0_int)

private def fastApow16DirectModPW19 (pNat u w k rCol cCol : Nat) : Nat :=
  let r := rCol % 4; let s := rCol / 4
  let t := cCol % 4; let m := cCol / 4
  let E := ((2 ^ (r * (m * u))) % pNat * ((3 ^ (s * (m * u))) % pNat)) % pNat
  (((r * w + s * k) ^ t) % pNat * E) % pNat

private def checkULModPNat16BoolW19 (pNat u w k : Nat)
    (cert : List (Nat × Nat) × List (List Nat)) : Bool :=
  checkRawMatULModP16BoolW19 pNat (buildMat16NatW19 (fastApow16DirectModPW19 pNat u w k)) cert

private theorem checkULModPNat16BoolW19_sound (pNat u w k : Nat) (hp : pNat ≥ 2)
    (cert : List (Nat × Nat) × List (List Nat))
    (h : checkULModPNat16BoolW19 pNat u w k cert = true) :
    intDet 16 (apow16UW19 u (w : Int) (k : Int)) % (pNat : Int) ≠ 0 := by
  let p : Int := (pNat : Int)
  let a0 := buildMat16NatW19 (fastApow16DirectModPW19 pNat u w k)
  let matOf (T : List (List Nat)) (i j : Fin 16) : Int := (natAt2DW19 T i.val j.val : Int)
  have hd_trans : ∀ a b c : Int, p ∣ (a - b) -> p ∣ (b - c) -> p ∣ (a - c) := by
    intro a b c ⟨q1, h1⟩ ⟨q2, h2⟩; exact ⟨q1 + q2, by rw [Int.mul_add]; omega⟩
  have hd_mul : ∀ a1 a2 b1 b2 : Int, p ∣ (a1 - a2) -> p ∣ (b1 - b2) -> p ∣ (a1 * b1 - a2 * b2) := by
    intro a1 a2 b1 b2 ⟨q1, h1⟩ ⟨q2, h2⟩
    exact ⟨q1 * b1 + a2 * q2, by
      have : a1 * b1 - a2 * b2 = (a1 - a2) * b1 + a2 * (b1 - b2) := by
        simp only [Int.sub_mul, Int.mul_sub]; omega
      rw [this, h1, h2, Int.mul_add, Int.mul_assoc p q1 b1,
          ← Int.mul_assoc a2 p q2, Int.mul_comm a2 p, Int.mul_assoc p a2 q2]⟩
  have hd_mod_r : ∀ n : Nat, p ∣ ((n : Int) - ((n % pNat : Nat) : Int)) := by
    intro n; rcases int_mod_sub_dvd_w19 n pNat with ⟨q, hq⟩
    exact ⟨-q, by dsimp [p]; rw [Int.mul_neg]; omega⟩
  have hd_A0 : p ∣ (intDet 16 (apow16UW19 u (w : Int) (k : Int)) - intDet 16 (matOf a0)) := by
    apply intDet_congr_dvd p 16
    intro i j
    dsimp only [matOf, a0]
    rw [natAt2DW19_buildMat16 _ i.val j.val i.isLt j.isLt]
    unfold apow16UW19 fastApow16DirectModPW19
    dsimp only
    let r := i.val % 4; let s := i.val / 4
    let t := j.val % 4; let m := j.val / 4
    have hpow_eq : intPowNat ((r : Int) * (w : Int) + (s : Int) * (k : Int)) t = (((r * w + s * k) ^ t : Nat) : Int) := by
      rw [← intPowNat_natCast_w19]; simp [Int.natCast_add, Int.natCast_mul]
    rw [hpow_eq]
    let E_int : Int := ((2 ^ (r * (m * u)) * 3 ^ (s * (m * u)) : Nat) : Int)
    let E_nat : Nat := ((2 ^ (r * (m * u))) % pNat * ((3 ^ (s * (m * u))) % pNat)) % pNat
    have hd_E : p ∣ (E_int - (E_nat : Int)) := by
      have hm_e : E_int = ((2 ^ (r * (m * u)) : Nat) : Int) * ((3 ^ (s * (m * u)) : Nat) : Int) := Int.natCast_mul _ _
      rw [hm_e]
      exact hd_trans _ (((2 ^ (r * (m * u))) % pNat * ((3 ^ (s * (m * u))) % pNat) : Nat) : Int) _
        (by rw [Int.natCast_mul]; exact hd_mul _ _ _ _ (hd_mod_r _) (hd_mod_r _))
        (hd_mod_r _)
    exact hd_trans _ (((((r * w + s * k) ^ t) % pNat * E_nat : Nat) : Int)) _
      (by rw [Int.natCast_mul]; exact hd_mul _ _ _ _ (hd_mod_r _) hd_E)
      (hd_mod_r _)
  have hraw_nz : intDet 16 (matOf a0) % p ≠ 0 :=
    checkRawMatULModP16BoolW19_sound pNat hp a0 cert h
  rcases hd_A0 with ⟨qt, hqt⟩
  intro hz_mod
  have hmat0 : intDet 16 (matOf a0) % p = 0 := by
    have heq : intDet 16 (matOf a0) =
        intDet 16 (apow16UW19 u (w : Int) (k : Int)) + p * (-qt) := by
      rw [Int.mul_neg]; omega
    rw [heq, Int.add_emod, hz_mod, Int.zero_add, Int.mul_emod_right, Int.zero_emod]
  exact hraw_nz hmat0

private theorem traceColSwaps16_spec_w19 (pNat : Nat) :
    ∀ (swaps : List (Nat × Nat)) (M : List (List Nat)) (r j : Nat),
      r < 16 -> j < 16 ->
      (traceColSwapsNW19 16 swaps j).1 < 16 ∧
      natAt2DW19 (applySignedSwapsMat16NatW19 pNat swaps M) r j =
        iterNegModPW19 pNat (traceColSwapsNW19 16 swaps j).2
          (natAt2DW19 M r (traceColSwapsNW19 16 swaps j).1)
  | [], _, _, _, _, hj => ⟨hj, rfl⟩
  | (c1, c2) :: rest, M, r, j, hr, hj => by
    unfold applySignedSwapsMat16NatW19 traceColSwapsNW19
    rcases htr : traceColSwapsNW19 16 rest j with ⟨j', cnt⟩
    dsimp only
    cases hcond : (Nat.ble (c1 + 1) 16 && Nat.ble (c2 + 1) 16 && (c1 != c2))
    · have hsw : swapOneMat16NatW19 pNat c1 c2 M = M := by
        unfold swapOneMat16NatW19; rw [hcond]; rfl
      rw [hsw]; simp only [Bool.false_eq_true, ↓reduceIte]
      rcases traceColSwaps16_spec_w19 pNat rest M r j hr hj with ⟨hj', ih_eq⟩
      rw [htr] at hj' ih_eq; exact ⟨hj', ih_eq⟩
    · simp only [↓reduceIte]
      let M' := swapOneMat16NatW19 pNat c1 c2 M
      rcases traceColSwaps16_spec_w19 pNat rest M' r j hr hj with ⟨hj', ih_eq⟩
      rw [htr] at hj' ih_eq; dsimp only at hj' ih_eq
      rcases bool_and_split hcond with ⟨hc12, _⟩
      rcases bool_and_split hc12 with ⟨hc1_b, hc2_b⟩
      have hc1 : c1 < 16 := Nat.ble_eq.mp hc1_b
      have hc2 : c2 < 16 := Nat.ble_eq.mp hc2_b
      have hM'_at : natAt2DW19 M' r j' =
          if j' == c1 then natAt2DW19 M r c2
          else if j' == c2 then natSubModPW19 pNat 0 (natAt2DW19 M r c1)
          else natAt2DW19 M r j' := by
        unfold M' swapOneMat16NatW19; rw [hcond]; simp only [↓reduceIte]
        exact natAt2DW19_buildMat16 _ r j' hr hj'
      rw [hM'_at] at ih_eq
      cases he1 : (j' == c1)
      · cases he2 : (j' == c2)
        · simp only [he1, he2, Bool.false_eq_true, ↓reduceIte] at ih_eq ⊢; exact ⟨hj', ih_eq⟩
        · simp only [he1, he2, Bool.false_eq_true, ↓reduceIte] at ih_eq ⊢
          rw [iterNegModPW19_neg] at ih_eq; exact ⟨hc1, ih_eq⟩
      · simp only [he1, ↓reduceIte] at ih_eq ⊢; exact ⟨hc2, ih_eq⟩

private theorem buildRow16NatW19_congr (f g : Nat -> Nat) (h : ∀ j : Nat, j < 16 -> f j = g j) :
    buildRow16NatW19 f = buildRow16NatW19 g := by
  unfold buildRow16NatW19
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide),
      h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide),
      h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide),
      h 12 (by decide), h 13 (by decide), h 14 (by decide), h 15 (by decide)]

private theorem buildMat16NatW19_congr (f g : Nat -> Nat -> Nat)
    (h : ∀ r j : Nat, r < 16 -> j < 16 -> f r j = g r j) :
    buildMat16NatW19 f = buildMat16NatW19 g := by
  unfold buildMat16NatW19
  rw [buildRow16NatW19_congr _ _ (fun j hj => h 0 j (by decide) hj),
      buildRow16NatW19_congr _ _ (fun j hj => h 1 j (by decide) hj),
      buildRow16NatW19_congr _ _ (fun j hj => h 2 j (by decide) hj),
      buildRow16NatW19_congr _ _ (fun j hj => h 3 j (by decide) hj),
      buildRow16NatW19_congr _ _ (fun j hj => h 4 j (by decide) hj),
      buildRow16NatW19_congr _ _ (fun j hj => h 5 j (by decide) hj),
      buildRow16NatW19_congr _ _ (fun j hj => h 6 j (by decide) hj),
      buildRow16NatW19_congr _ _ (fun j hj => h 7 j (by decide) hj),
      buildRow16NatW19_congr _ _ (fun j hj => h 8 j (by decide) hj),
      buildRow16NatW19_congr _ _ (fun j hj => h 9 j (by decide) hj),
      buildRow16NatW19_congr _ _ (fun j hj => h 10 j (by decide) hj),
      buildRow16NatW19_congr _ _ (fun j hj => h 11 j (by decide) hj),
      buildRow16NatW19_congr _ _ (fun j hj => h 12 j (by decide) hj),
      buildRow16NatW19_congr _ _ (fun j hj => h 13 j (by decide) hj),
      buildRow16NatW19_congr _ _ (fun j hj => h 14 j (by decide) hj),
      buildRow16NatW19_congr _ _ (fun j hj => h 15 j (by decide) hj)]

private theorem applySignedSwaps_is_buildMat16W19 (pNat : Nat) :
    ∀ (swaps : List (Nat × Nat)) (f : Nat -> Nat -> Nat),
      ∃ g : Nat -> Nat -> Nat,
        applySignedSwapsMat16NatW19 pNat swaps (buildMat16NatW19 f) = buildMat16NatW19 g
  | [], f => ⟨f, rfl⟩
  | (c1, c2) :: rest, f => by
    unfold applySignedSwapsMat16NatW19 swapOneMat16NatW19
    cases (Nat.ble (c1 + 1) 16 && Nat.ble (c2 + 1) 16 && (c1 != c2)) <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;>
      exact applySignedSwaps_is_buildMat16W19 pNat rest _

private theorem applySignedSwaps_eq_tracedBuildMat16W19 (pNat : Nat)
    (swaps : List (Nat × Nat)) (f : Nat -> Nat -> Nat) :
    applySignedSwapsMat16NatW19 pNat swaps (buildMat16NatW19 f) =
      buildMat16NatW19 (fun r j =>
        match traceColSwapsNW19 16 swaps j with
        | (j0, cnt) => iterNegModPW19 pNat cnt (f r j0)) := by
  rcases applySignedSwaps_is_buildMat16W19 pNat swaps f with ⟨g, hg⟩
  have hspec : ∀ r j : Nat, r < 16 -> j < 16 ->
      g r j = match traceColSwapsNW19 16 swaps j with
              | (j0, cnt) => iterNegModPW19 pNat cnt (f r j0) := by
    intro r j hr hj
    rcases traceColSwaps16_spec_w19 pNat swaps (buildMat16NatW19 f) r j hr hj with ⟨hj0, heq⟩
    rw [hg, natAt2DW19_buildMat16 g r j hr hj] at heq
    rcases htr : traceColSwapsNW19 16 swaps j with ⟨j0, cnt⟩
    rw [htr] at hj0 heq; dsimp only at hj0 heq ⊢
    rw [heq, natAt2DW19_buildMat16 f r j0 hr hj0]
  rw [hg]; exact buildMat16NatW19_congr g _ hspec

private theorem dotDirect16W19_eq (f g : Nat -> Nat) :
    ∀ n : Nat, n ≤ 16 ->
      dotDirectW19 f g n = dotPrefixNatW19 (buildRow16NatW19 f) (buildRow16NatW19 g) n
  | 0, _ => rfl
  | n' + 1, hn => by
    have hn_lt : n' < 16 := hn
    simp only [dotDirectW19, dotPrefixNatW19,
               dotDirect16W19_eq f g n' (Nat.le_of_lt hn),
               natAt1DW19_buildRow16 f n' hn_lt, natAt1DW19_buildRow16 g n' hn_lt]
    apply congrArg (dotPrefixNatW19 (buildRow16NatW19 f) (buildRow16NatW19 g) n' + ·)
    cases f n' <;> simp

private def checkULModPNat16FastBoolW19 (pNat u w k : Nat)
    (cert : List (Nat × Nat) × List (List Nat)) : Bool :=
  let apFn (r j : Nat) : Nat :=
    match traceColSwapsNW19 16 cert.1 j with
    | (j0, cnt) => iterNegModPW19 pNat cnt (fastApow16DirectModPW19 pNat u w k r j0)
  let uFn (n c : Nat) : Nat := uStrictNatValW19 cert.2 n c
  allNatLoop2W19 (fun r =>
    allNatLoop2W19 (fun c =>
      if Nat.ble (r + 1) c then
        dotDirectW19 (apFn r) (fun n => uFn n c) (c + 1) % pNat == 0
      else true) 16) 16 &&
  (natDiagDirectModPW19 pNat apFn uFn 16 != 0)

private theorem checkULModPNat16FastBoolW19_eq (pNat u w k : Nat)
    (cert : List (Nat × Nat) × List (List Nat)) :
    checkULModPNat16FastBoolW19 pNat u w k cert =
      checkULModPNat16BoolW19 pNat u w k cert := by
  unfold checkULModPNat16FastBoolW19 checkULModPNat16BoolW19 checkRawMatULModP16BoolW19
  dsimp only
  let apFn (r j : Nat) : Nat :=
    match traceColSwapsNW19 16 cert.1 j with
    | (j0, cnt) => iterNegModPW19 pNat cnt (fastApow16DirectModPW19 pNat u w k r j0)
  change (allNatLoop2W19 (fun r => allNatLoop2W19 (fun c =>
            if Nat.ble (r + 1) c then dotDirectW19 (apFn r) (fun n => uStrictNatValW19 cert.2 n c) (c + 1) % pNat == 0
            else true) 16) 16 &&
          (natDiagDirectModPW19 pNat apFn (uStrictNatValW19 cert.2) 16 != 0)) = _
  rw [applySignedSwaps_eq_tracedBuildMat16W19 pNat cert.1 (fastApow16DirectModPW19 pNat u w k)]
  let apRows := buildMat16NatW19 apFn
  let uCols := buildMat16NatW19 (fun c r => uStrictNatValW19 cert.2 r c)
  have hdot : ∀ (r c m : Nat), r < 16 -> c < 16 -> m ≤ 16 ->
      dotDirectW19 (apFn r) (fun n => uStrictNatValW19 cert.2 n c) m =
        dotListsPrefixW19 m (natRowAtW19 apRows r) (natRowAtW19 uCols c) := by
    intro r c m hr hc hm
    rw [dotListsPrefixW19_eq, dotDirect16W19_eq _ _ m hm]
    dsimp only [apRows, uCols]
    rw [natRowAtW19_buildMat16 _ r hr, natRowAtW19_buildMat16 _ c hc]
  have hloop :
      allNatLoop2W19 (fun r => allNatLoop2W19 (fun c =>
        if Nat.ble (r + 1) c then dotDirectW19 (apFn r) (fun n => uStrictNatValW19 cert.2 n c) (c + 1) % pNat == 0
        else true) 16) 16 =
      allNatLoop2W19 (fun r =>
        let row_r := natRowAtW19 apRows r
        allNatLoop2W19 (fun c =>
          if Nat.ble (r + 1) c then dotListsPrefixW19 (c + 1) row_r (natRowAtW19 uCols c) % pNat == 0
          else true) 16) 16 := by
    apply allNatLoop2W19_congr _ _ 16; intro r hr
    apply allNatLoop2W19_congr _ _ 16; intro c hc
    rw [hdot r c (c + 1) hr hc (by omega)]
  have hdiag : ∀ m : Nat, m ≤ 16 ->
      natDiagDirectModPW19 pNat apFn (uStrictNatValW19 cert.2) m =
        natDiagProdModPW19 pNat apRows uCols m := by
    intro m hm; induction m with
    | zero => rfl
    | succ m' ih =>
      have hm_lt : m' < 16 := hm
      simp only [natDiagDirectModPW19, natDiagProdModPW19,
                 ih (Nat.le_of_lt hm), hdot m' m' (m' + 1) hm_lt hm_lt hm]
  rw [hloop, hdiag 16 (Nat.le_refl 16)]

private def checkAffRangeULModP16BoolW19 (u pNat start : Nat) :
    Nat -> List (List (Nat × Nat) × List (List Nat)) -> Bool
  | 0, _ => true
  | cnt + 1, c :: cs =>
    checkULModPNat16BoolW19 pNat u start 1 c &&
      checkAffRangeULModP16BoolW19 u pNat (start + 1) cnt cs
  | _, [] => false

private def checkAffRangeULModP16FastBoolW19 (u pNat start : Nat) :
    Nat -> List (List (Nat × Nat) × List (List Nat)) -> Bool
  | 0, _ => true
  | cnt + 1, c :: cs =>
    checkULModPNat16FastBoolW19 pNat u start 1 c &&
      checkAffRangeULModP16FastBoolW19 u pNat (start + 1) cnt cs
  | _, [] => false

private theorem checkAffRangeULModP16FastBoolW19_eq (u pNat : Nat) :
    ∀ (cnt start : Nat) (cs : List (List (Nat × Nat) × List (List Nat))),
      checkAffRangeULModP16FastBoolW19 u pNat start cnt cs =
        checkAffRangeULModP16BoolW19 u pNat start cnt cs
  | 0, _, _ => rfl
  | _ + 1, _, [] => rfl
  | cnt' + 1, start, c :: cs => by
    change (checkULModPNat16FastBoolW19 pNat u start 1 c && checkAffRangeULModP16FastBoolW19 u pNat (start + 1) cnt' cs) =
      (checkULModPNat16BoolW19 pNat u start 1 c && checkAffRangeULModP16BoolW19 u pNat (start + 1) cnt' cs)
    rw [checkULModPNat16FastBoolW19_eq, checkAffRangeULModP16FastBoolW19_eq u pNat cnt' (start + 1) cs]

private theorem checkAffRangeULModP16FastBoolW19_glue (u pNat : Nat) :
    ∀ (a b start : Nat) (cs : List (List (Nat × Nat) × List (List Nat))),
      checkAffRangeULModP16FastBoolW19 u pNat start a cs = true ->
      checkAffRangeULModP16FastBoolW19 u pNat (start + a) b (dropCertsW19 a cs) = true ->
      checkAffRangeULModP16FastBoolW19 u pNat start (a + b) cs = true
  | 0, _, start, _, _, hb => by rw [Nat.zero_add]; rw [Nat.add_zero] at hb; exact hb
  | _ + 1, _, _, [], ha, _ => by cases ha
  | a' + 1, b, start, c :: cs, ha, hb => by
    rw [Nat.succ_add]
    change (checkULModPNat16FastBoolW19 pNat u start 1 c && checkAffRangeULModP16FastBoolW19 u pNat (start + 1) a' cs) = true at ha
    change (checkULModPNat16FastBoolW19 pNat u start 1 c && checkAffRangeULModP16FastBoolW19 u pNat (start + 1) (a' + b) cs) = true
    rcases bool_and_split ha with ⟨hc, hrest⟩
    rw [hc, Bool.true_and]
    apply checkAffRangeULModP16FastBoolW19_glue u pNat a' b (start + 1) cs hrest
    rwa [show (start + 1) + a' = start + (a' + 1) by omega]

private theorem unpack_affRangeULModP16_w19 (u pNat : Nat) (hp : pNat ≥ 2) :
    ∀ (cnt start : Nat) (cs : List (List (Nat × Nat) × List (List Nat))),
      checkAffRangeULModP16BoolW19 u pNat start cnt cs = true ->
      ∀ t : Nat, start ≤ t -> t < start + cnt ->
        intDet 16 (apow16UW19 u (t : Int) 1) % (pNat : Int) ≠ 0
  | 0, _, _, _, _, hlo, hhi => by omega
  | _ + 1, _, [], hchk, _, _, _ => by cases hchk
  | cnt' + 1, start, c :: cs, hchk, t, hlo, hhi => by
    change (checkULModPNat16BoolW19 pNat u start 1 c && checkAffRangeULModP16BoolW19 u pNat (start + 1) cnt' cs) = true at hchk
    rcases bool_and_split hchk with ⟨hcur, hrest⟩
    by_cases hteq : t = start
    · subst hteq; exact checkULModPNat16BoolW19_sound pNat u t 1 hp c hcur
    · exact unpack_affRangeULModP16_w19 u pNat hp cnt' (start + 1) cs hrest t (by omega) (by omega)

private theorem det16_t4u4_nonzero_of_proj_sieve_w19 (u pNat : Nat) (hp : pNat ≥ 3)
    (hinv_b : checkAllInvModPBoolW19 pNat pNat = true)
    (hinf_nz : intDet 16 (apow16UW19 u 1 0) % (pNat : Int) ≠ 0)
    (haff_spec : ∀ t : Nat, t < pNat -> intDet 16 (apow16UW19 u (t : Int) 1) % (pNat : Int) ≠ 0)
    (W K : Nat) (hW : W ≥ 1) (_hK : K ≥ 1) :
    intDet 16 (laurentTwoBaseT4U4Mat16 W K u) ≠ 0 := by
  let p : Int := (pNat : Int)
  have hinv_spec : ∀ x : Nat, x < pNat -> x ≠ 0 ->
      (x * powModFuelNatW19 8 x (pNat - 2) pNat) % pNat = 1 := by
    have hlp : ∀ n : Nat, n ≤ pNat -> checkAllInvModPBoolW19 pNat n = true ->
        ∀ x : Nat, x < n -> x ≠ 0 -> (x * powModFuelNatW19 8 x (pNat - 2) pNat) % pNat = 1 := by
      intro n hn; induction n with
      | zero => intros _ _ hlt; omega
      | succ n' ihn =>
        intro ha x hx hne
        unfold checkAllInvModPBoolW19 at ha
        rcases bool_and_split ha with ⟨hcur, hprev⟩
        by_cases hxeq : x = n'
        · subst hxeq; rw [beq_false_of_ne hne] at hcur; exact beq_iff_eq.mp hcur
        · exact ihn (Nat.le_of_lt hn) hprev x (by omega) hne
    exact hlp pNat (Nat.le_refl _) hinv_b
  have hcancel24 : ∀ (x inv : Nat) (V : Int),
      (x * inv) % pNat = 1 ->
      (intPowNat (x : Int) 24 * V) % p = 0 ->
      V % p = 0 := by
    intro x inv V hxinv hxv0
    have hp_d : ∀ d : Nat, ((x * inv) ^ d) % pNat = 1 := by
      intro d; induction d with
      | zero => simp only [Nat.pow_zero]; exact Nat.mod_eq_of_lt (by omega)
      | succ d' ih => rw [Nat.pow_succ, Nat.mul_mod, ih, Nat.one_mul, Nat.mod_mod, hxinv]
    let x24 : Nat := x ^ 24
    let inv24 : Nat := inv ^ 24
    let prod24 : Nat := x24 * inv24
    have hp24_1 : prod24 % pNat = 1 := by
      dsimp [prod24, x24, inv24]; rw [← mul_pow_w19 x inv 24]; exact hp_d 24
    have hm1 : (prod24 : Int) % p = 1 := by
      dsimp [p]
      have hdm := congrArg (fun n : Nat => (n : Int)) (Nat.div_add_mod prod24 pNat)
      rw [hp24_1] at hdm
      rw [← hdm, Int.natCast_add, Int.natCast_mul, Int.add_comm, Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt (by decide) (by omega)
    have h1p : (1 : Int) % p = 1 := Int.emod_eq_of_lt (by decide) (by dsimp [p]; omega)
    rw [intPowNat_natCast_w19 x 24] at hxv0
    change (x24 : Int) * V % p = 0 at hxv0
    calc V % p
        = ((1 % p) * (V % p)) % p := by rw [h1p, Int.one_mul, Int.emod_emod]
      _ = (((prod24 : Int) % p) * (V % p)) % p := by rw [hm1, h1p]
      _ = ((prod24 : Int) * V) % p := (Int.mul_emod _ _ _).symm
      _ = ((inv24 : Int) * ((x24 : Int) * V)) % p := by
          dsimp [prod24]; rw [Int.mul_comm (x24 : Int), Int.mul_assoc]
      _ = (((inv24 : Int) % p) * (((x24 : Int) * V) % p)) % p := Int.mul_emod _ _ _
      _ = 0 := by rw [hxv0, Int.mul_zero, Int.zero_emod]
  have hmat_mod_congr : ∀ (w1 w2 k1 k2 : Int),
      p ∣ (w1 - w2) -> p ∣ (k1 - k2) ->
      p ∣ (intDet 16 (apow16UW19 u w1 k1) - intDet 16 (apow16UW19 u w2 k2)) := by
    have hd_add : ∀ a1 a2 b1 b2 : Int, p ∣ (a1 - a2) -> p ∣ (b1 - b2) -> p ∣ ((a1 + b1) - (a2 + b2)) := by
      intro a1 a2 b1 b2 ⟨q1, h1⟩ ⟨q2, h2⟩; exact ⟨q1 + q2, by rw [Int.mul_add]; omega⟩
    have hd_mul : ∀ a1 a2 b1 b2 : Int, p ∣ (a1 - a2) -> p ∣ (b1 - b2) -> p ∣ (a1 * b1 - a2 * b2) := by
      intro a1 a2 b1 b2 ⟨q1, h1⟩ ⟨q2, h2⟩
      exact ⟨q1 * b1 + a2 * q2, by
        have : a1 * b1 - a2 * b2 = (a1 - a2) * b1 + a2 * (b1 - b2) := by
          simp only [Int.sub_mul, Int.mul_sub]; omega
        rw [this, h1, h2, Int.mul_add, Int.mul_assoc p q1 b1,
            ← Int.mul_assoc a2 p q2, Int.mul_comm a2 p, Int.mul_assoc p a2 q2]⟩
    have hd_pow : ∀ (a1 a2 : Int) (d : Nat), p ∣ (a1 - a2) -> p ∣ (intPowNat a1 d - intPowNat a2 d) := by
      intro a1 a2 d hd; induction d with
      | zero => exact ⟨0, by simp [intPowNat]⟩
      | succ d' ih => exact hd_mul a1 a2 _ _ hd ih
    intro w1 w2 k1 k2 hw hk
    apply intDet_congr_dvd p 16
    intro i j; unfold apow16UW19; dsimp only
    let r : Int := (i.val % 4 : Int)
    let s : Int := (i.val / 4 : Int)
    let E : Int := ((2 ^ (i.val % 4 * (j.val / 4 * u)) * 3 ^ (i.val / 4 * (j.val / 4 * u)) : Nat) : Int)
    have hlin : p ∣ ((r * w1 + s * k1) - (r * w2 + s * k2)) :=
      hd_add _ _ _ _ (hd_mul r r w1 w2 ⟨0, by simp⟩ hw) (hd_mul s s k1 k2 ⟨0, by simp⟩ hk)
    exact hd_mul _ _ E E (hd_pow _ _ (j.val % 4) hlin) ⟨0, by simp⟩
  intro hz_det
  let g := Nat.gcd W K
  have hg_pos : g ≥ 1 := Nat.gcd_pos_of_pos_left K hW
  let w' := W / g
  let k' := K / g
  have hW_eq : W = g * w' := by rw [Nat.mul_comm]; exact (Nat.div_mul_cancel (Nat.gcd_dvd_left W K)).symm
  have hK_eq : K = g * k' := by rw [Nat.mul_comm]; exact (Nat.div_mul_cancel (Nat.gcd_dvd_right W K)).symm
  rw [hW_eq, hK_eq, det16_t4u4_homog24_w19 u g w' k'] at hz_det
  have hg24_pos : intPowNat (g : Int) 24 > 0 := by
    rw [intPowNat_natCast_w19 g 24]; have := nat_pow_pos_of_pos g hg_pos 24; omega
  have hdet_wk0 : intDet 16 (laurentTwoBaseT4U4Mat16 w' k' u) = 0 := by
    by_cases h0 : intDet 16 (laurentTwoBaseT4U4Mat16 w' k' u) = 0
    · exact h0
    · exact False.elim (Int.mul_ne_zero (by omega) h0 hz_det)
  have hapow0 := stirling_20736_det16_t4u4_u_w19 u w' k'
  rw [hdet_wk0, Int.mul_zero] at hapow0
  let wm := w' % pNat
  let km := k' % pNat
  have hwm_lt : wm < pNat := Nat.mod_lt w' (by omega)
  have hkm_lt : km < pNat := Nat.mod_lt k' (by omega)
  have hnot_both0 : ¬ (wm = 0 ∧ km = 0) := by
    rintro ⟨hw0, hk0⟩
    rcases Nat.dvd_of_mod_eq_zero hw0 with ⟨qw, hqw⟩
    rcases Nat.dvd_of_mod_eq_zero hk0 with ⟨qk, hqk⟩
    have hdW : pNat * g ∣ W := ⟨qw, by rw [hW_eq, hqw]; ac_rfl⟩
    have hdK : pNat * g ∣ K := ⟨qk, by rw [hK_eq, hqk]; ac_rfl⟩
    have hle := Nat.le_of_dvd hg_pos (Nat.dvd_gcd hdW hdK)
    have h2g : 2 * g ≤ pNat * g := Nat.mul_le_mul_right g (by omega)
    omega
  have hm_wk : intDet 16 (apow16UW19 u (wm : Int) (km : Int)) % p = 0 := by
    rcases hmat_mod_congr (wm : Int) (w' : Int) (km : Int) (k' : Int)
      (int_mod_sub_dvd_w19 w' pNat) (int_mod_sub_dvd_w19 k' pNat) with ⟨q, hq⟩
    rw [hapow0.symm, Int.sub_zero] at hq
    rw [hq, Int.mul_emod_right]
  by_cases hkm0 : km = 0
  · have hwm_ne : wm ≠ 0 := fun hw0 => hnot_both0 ⟨hw0, hkm0⟩
    let inv := powModFuelNatW19 8 wm (pNat - 2) pNat
    have hinv := hinv_spec wm hwm_lt hwm_ne
    rw [hkm0, show (wm : Int) = (wm : Int) * 1 by omega,
        show ((0 : Nat) : Int) = (wm : Int) * 0 by omega,
        apow16_homog24_w19 u 1 0 (wm : Int)] at hm_wk
    exact hinf_nz (hcancel24 wm inv _ hinv hm_wk)
  · let inv := powModFuelNatW19 8 km (pNat - 2) pNat
    have hinv := hinv_spec km hkm_lt hkm0
    let t := (wm * inv) % pNat
    have ht_lt : t < pNat := Nat.mod_lt _ (by omega)
    have htkm_dvd : p ∣ ((km : Int) * (t : Int) - (wm : Int)) := by
      have hnat : (km * t) % pNat = wm := by
        dsimp [t]
        rw [Nat.mul_comm km, Nat.mod_mul_mod, Nat.mul_assoc wm inv km, Nat.mul_comm inv km,
            Nat.mul_mod wm (km * inv) pNat, hinv, Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hwm_lt]
      have hsub := int_mod_sub_dvd_w19 (km * t) pNat
      rw [hnat] at hsub
      rcases hsub with ⟨q, hq⟩
      simp only [Int.natCast_mul] at hq
      exact ⟨-q, by dsimp [p]; rw [Int.mul_neg]; omega⟩
    rcases hmat_mod_congr ((km : Int) * (t : Int)) (wm : Int) ((km : Int) * 1) (km : Int)
      htkm_dvd ⟨0, by simp⟩ with ⟨qd, hqd⟩
    have htk_mod0 : intDet 16 (apow16UW19 u ((km : Int) * (t : Int)) ((km : Int) * 1)) % p = 0 := by
      have heq : intDet 16 (apow16UW19 u ((km : Int) * (t : Int)) ((km : Int) * 1)) =
          intDet 16 (apow16UW19 u (wm : Int) (km : Int)) + p * qd := by omega
      rw [heq, Int.add_emod, hm_wk, Int.zero_add, Int.mul_emod_right, Int.zero_emod]
    rw [apow16_homog24_w19 u (t : Int) 1 (km : Int)] at htk_mod0
    exact haff_spec t ht_lt (hcancel24 km inv _ hinv htk_mod0)

-- `16 × 16` `P^1(F_p)` Sieve Certificates for `u = 1..5` (`p = 31, 59, 41, 67, 37`):
private def sieve16InfU1W19 : List (Nat × Nat) × List (List Nat) := decodeUCert16W19 (0x0, 0x1c021e000000140a1203020b0d001c090a050f021e00000012000000100c14051e0f1b140e1e0515030104001c0114071d1d0f1707021e000000080000001b000000021909160614171d171b1e05191a0b010d131d04180801001c040b0c050c1716070f1b1d19021e00000004000000030000001e000000)

private def sieve16AffU1C0W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0xa2012301a4014701c801ec, 0x3180c0f01041c000000090300001e151a1c000d1b111c131c041816020000001e000000191d0000011e00000a0e071d000d1b010002161e0208021b07091e1e0d03000000000000000000000000000000000000000000000000180000000000000000000000000e1c00000000000000000000000017021e),
  (0x20f, 0x1b0515141c071e11131d0d080e041119150f171a1a151a1617061d030418090f041412111a1a0f0f020c1d190a1318030c07051e0b1c0f0407070d081e0b19021e170a1513041d1c091e08190514011e1505120104060601001c0c0f0a06170a180514130419021e001101011a110313061d011e000000),
  (0x0, 0x1107170b1707071803011a0b0d091915190a120716141b1e1c0f1616110f161d15030b0103181312080f180a040a110c160c0307111b0d070a0f04050803121d1018050d100b04130a05170c07140a0b17140e1b040508001000190a12131b15130a110107131c081d18020a1d0b01060c020f071e000000),
  (0x149, 0x1c021d08051910131816030e0e190a1b040d11120401070a0406150014180f1e061519130f13120e100405160718050b0e021d1c170300110a1a0908020e1e1b1d0c10050d18090c121403060916030f080307071d10190915001601051e150b15070d0911051d121c021418070a0212010402131e000000),
  (0x0, 0x20a13171705091703090f17080a0b1d060b0b11161a190d10011a09061716150018191b110e040d0109080e1a0f0c121d150c121c10020a0c0a1915091b1b1217080b0b141d1a130606061d12120b0d0f11130f03120019080013080e05040c120d110f0f110e011b03020314091b1a030d08171e000000),
  (0x0, 0x11e02191e1407081a080a040e040c1d00130106140911011d1709040c1a1b04110e0b0c0c191a19160918191715151e17140f0e071b031d0f1d100a1901161911061310011a1c17061a080719050710170e1e0a1b060b161900100d0c09110a0719011a121c05131a1e000c101d1c1a08060e191e000000),
  (0x0, 0x40b1218010417170b120f19090a04051a181d0002181e14020a0d130806050712001e001206170c080210171c0d0a090b161b1d071d0f151109011a1617101600101e1707040209071e1e16131a080a1612131013191d1b1a000d1c03170d1e170701021b0d1e0a19180e1d1b1a1b140e09000f1e000000),
  (0x0, 0x15001a0718100217111416060513160210010a140606131a051e0d0c100f1613041a0c1b1718160a080400181008100a030f16031005000f160e101802121d1e061c02070e0d081612120e0114120f1002180f12011b050909000a191c150a1b050c1d0a0605080518031c0609081001010119031e000000),
  (0x0, 0x1a1b0f131d0c0a11031300051d181a03190c1a0716131e0a0f0d18120a02071004090e1404151b1d1a1c0f0d0c0b01011b1b16041d171e18180d1b12000e1b18040c13011b021b1318100e050b0a170c110f001e1d02030504000701020200071a080d0d0d14070417000a1b1300071e03071b131e000000),
  (0x0, 0x51401180c09191110011d1a131607020c0b000e0c0c170d0d04040c011703000019170912180e0d1a010d04181d1612131015011010011c0015111108081810190a0d111d0f171a1911030b140a1815090d141b0c011910070004070c1c01010d0a19030a0c1407161d1b13000a130b060f06151e000000),
  (0x0, 0x71b181e070f03071011160b130a06170010110b011d19020106001b18041c0a061a131b090b11110007111207061b001e09020a1d0c0d000412190500070619170f0b170815130b02090b110c14131008050607181915011c000106030605140e00030d1214120e15031a1b0414001c180608101e000000),
  (0xe6020f, 0x7070b1a100c1a15080600190c0404080106140217161c04101e050a0c10051b000905060d0a181b0111060f0f150608191a0a1b0f0002040a01151b14011c16120709130f140705081811190d12180d0e0714130c100e09001d0e0d00141e0b05101915141619141a0a08191905061d03090d1e000000),
  (0x0, 0x8140a150c191b1c00060b0a00000012150e1a091d111b020208191b15081713050b0319121e1915180f1901131805140302090f0c1c020912151c15091615190a001005000e010a04121611110b190c0c111c14191207040d001a0f0c080c171c0711190c1d0f09130f050e00021c0d090615001e000000),
  (0x0, 0x70c110b03031a130b1d0a171d0311170e170d1e06091b0b050014071d051a1b120f010408060d19060e0e090e1e1c190e06070d160b0108060a1c0008121e0b19100f04120b0a1c04041d0516160718181a020511041b150c00170610090d18170b051e0b18151c12031a071c0003060014060f1e000000),
  (0xe6, 0x1907010d0c13090a091a190114101a01111a18121b181b0308061a1614020f0811141b041d1a13160110041b14081c0119190e040d050011151a19131a17121611031a031205030106080b0c170a0d050b0f00180000150b09001417030413031d17091c081504141108020e1c060a110c090e1c1e000000),
  (0x0, 0x1a180118071e07140c1813051a0e14051c130a1a0f1600101e00000f081c051e1c1611151912191911171c000c0f021a050d01190d130a07110b0b00001612000501140903120a190001171212160a021c0f070209071e141d0011161c051c06010b01060c0a0c1010090705140000190c001a1e1e000000),
  (0x0, 0x180e1915170b1616051b03001704020910160104011402101e0d0e110108040e16100b12030e1709060d0e1613151e0c121c060b10020d0c19100f1508181e09111e130400060e151006111d12091a02170d19080d191d0402000e17151612121e0b0c190f0a13100f090c13101c091500160e011e000000)
  ] : List (Nat × Nat)).map decodeUCert16W19

private def sieve16AffU1C1W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x0, 0xa0c16010c060f080a0911000a11111e170515121a060b1d151c12041e19140f04141e1b0a001e1600020507101b02041701061e0101141b041a13061a1e0f0b00091e1d0b0610061d1a0f0506151615030d1a0d14011b0c0b000b1512000e03101b10060d181b140e1c0401151c121c0f1400161e000000),
  (0x0, 0x21a0f0c170f120a160d0a07181b17061d1a0712191a0b171a041512130a0b110a1c190c070f0813131d141e1c150915151c030c050d071208140415120c0f120f000b0115001509001c0b180b091d081601171b16001112130008030f05000f1c020a1b1c1d0a1c0d061404000617010f0d10001e000000),
  (0x149020f, 0x81719120b1910080317181e14071409111006130e16061e1d1b0004070d151904071302040d0c081a001c1613131e1901171a130b0014150c1e0b10141a0f171100180d0c151e001c051d1014190416141617080519091200051205060a0d1c101218061610090c060119101a030c0510080e1e000000),
  (0x149, 0xb131d130011011c0813140e160e1617021c081e06020c061b1b1b000115160c0d0d1b120b1e1d16110007081a07140c151e0802031c0704160208010d1e1e120612091011071210000c011e04121e0011191a181215190e0e00021e1c0a1d1d08081c150d0509190b000b091e1d1802010d190d1e000000),
  (0x0, 0x1e010b18010d100e1b03101413081c110a0d0a0d1b140c0c1711120a04171014091d0b0e19191e1d17071009141504181b0506031b0f0f151817191b0a04011a0f1e1701000916171d08100f0b0b1e0807040b0f08110e1703001e161e1017010918011b08100d0e0a1c190e0d1203111d0510011e000000),
  (0x0, 0xb0007111a0715051b07181e02061e150a171902050f0c04141807140e120f1202061318150a150e13040d101b01010c09010d1409021e0c0115180316001a080a081519071c0d0f110f020f1a15101518160c10000d051018001b1916041a03191e0d0b0b180b070912171e1104020b041715171e000000),
  (0x0, 0x60e1d16151b1217130c17050806111919001003160e0d0c09140a020a1e101114100616030a0e080816010c18170b1c0503160d0d0f161d1d1b041c0716181a19070a0c11160e18021515070715130b0d180d1d13080c0e1b0018061e070a021805160c0f0b1804081c1e1b110e0e07060506181e000000),
  (0x0, 0xa030a16160c0e02081212000a0910160f041c090a150305080b1d08191303180e010e0612010f1a1d140a19121016100915111816020e150514120d10140d1c001a14070108171a08101e1b090d19090f15110a1e001207160015170b090a090e0f08130e071705071d011904071103110300051e000000),
  (0x1ee, 0x191b000c0e0e100f150113110d1b071d040708021c0a0b03181501010015170117051a161c131b07131e0b1a19171506181611031a0e1e1c001d1e1e150d0d17120e1a130305190b0113121c0e050c120d19150e040b010405001206171c100204121801190c010a060c0610070b091111080d111e000000),
  (0x0, 0x16170e130210140d100e120c021115140a06031e081a16150c081310011e010b12121d141e1d0d11041b08090508071a1415050e1507001a0c0f010c0815181a110805180906041a0c040509111a130a13041d1406021c0906000f070512051a1416050007141a1305161a0a110b041906050e171e000000),
  (0x0, 0x14190d190203011a0a0300180402030a13090114141c0116170e1b0d1e0d0e1909020d13021c1a080b1a0c1e020d18060a1c13091d040b180a1a180e0e1204141709041d0a03080b151e0107160d070b0c0d040c1515070e17000c09130d080f17110918151b11010410120b0e0315001a0b08161e000000),
  (0x0, 0x50d0119040f04090b131b0913131e17010d020d060b1d02100509050e190a1c040503100403061918131c07011617131b16120d021100100613040b12181819170e17040b1305001e0704021a0900050f1b0315191a01090a00090a09031d04171a160c021a0212030a171a0a0f0402060608111e000000),
  (0x0, 0x1a0f1312191b1e1b140a0307050e0816071d170b0805121e1e0d0b101b1e11170b06121401020119150e0b160405000201141300091c0c180b1b11010803061d030f140c1d0013091c131611020b030f0704171c181a11030f0006120c07190c021c1e151c0c0308020f08090e110c0c18021c101e000000),
  (0x1ee, 0x80400150916161b1411091619120907030e0d040d1b100f13000d071e1d0310061a0a0e0012130c0b0204170a10141d1c1e171d100917181c030a00020d180000150403080b0913180f140d121a09110c17170c030a01111e000312051c050b1001080c16000602011509160100100b0600000a1e000000)
  ] : List (Nat × Nat)).map decodeUCert16W19

private def sieve16InfU2W19 : List (Nat × Nat) × List (List Nat) := decodeUCert16W19 (0x0, 0x38023a00000011390e2108192e343822243037023a0000001b00000002181a2d0933380e35180c332029071f38040b1b23121a0f2b023a00000034000000310000001e182d0c302d2212360b29191c342320212d342c0f0a2a0938012a3331251c3a0e31261f16023a00000026000000090000003a000000)

private def sieve16AffU2C0W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0xa2012301a4014701c801ec, 0x1c080d31352638000000190300000a2314380036331e120438160b25020000003a00000003390000313a00002f2b21390036330100130e272f11022530163a2e1e0900000000000000000000000000000000000000000000000026000000000000000000000000193600000000000000000000000036043a),
  (0x0, 0x321024060138110f352e352608290e221f00381d36182d1f3137063935020e15343a04180c1e320912341a04351704182d2b363a110b382c122c0a102e2b0135023a013738070e19282f3a261019101e27272e042b330603210938072e34132324283a30140916023a2c362e3a2f0712390639013a000000),
  (0x0, 0xb10392509192f05280e0f1d0d0b0a3228250535371220160d1b1a2d19082c261a0937020d2d06282f2d2938191f372429290507351126260c0535083330350c222f1813040c270931091f2311282c082f312c091b301d0c3511351d2d071c262606212f26110b083919060733182919052f190c3a000000),
  (0x0, 0x151238042f0e0e2e2c1b29100e3915051b02211e1c1034271a0d1232051a0134110b292627182e03053223362331081a1a1d283a140a2e0a191c0516370f2a340c391c15231132182813390212311319131d0f0b29071f000c013200042f3907133a191a0a241b12381d35251b182d3510072f023a000000),
  (0x0, 0x1e101d281237131a2c0312022727170c211827061d131c1a1b24001419261d301d0c2d250434100a1c29061b2433280825372c360d2b212b122211112637020013271b312b140a0f11241822270537223622391901322e160e132f0f311e081c0b2b0a2411272320371036030e06152b380028143a000000),
  (0x1ac020f, 0x209392d0830280f00322c361d2824141820021d3a210e35330610370b2500222e033535112d2430152f1e2f321312252d20273511172b3810110f002c2b0f0e180211283320062c021b3a380c341b213a30032e211e342b392c0420301c0519331c0522361c32361c300e3033353a0f2c2d233a000000),
  (0x0, 0x3512102e3305352d1f08051a0b073632160a1b0c270c1f2f3a2c3a081024192f290e0c2228242f1b332a1c1f22330d3a2f38371f0219230d13102a100c13040e270f0c29310b180e333a131a192b001c0801373033341438370f29380e33001031260111311b2b0d352f1132113a3020362d142c3a000000),
  (0x0, 0x2d0b0c2c1c0c3827251e08323a32061133121436082e1a04320b0b3205251e20001f1b1c261b102f1b302012132812141c1d3122240927192a290c232e2f2f26000a2a12282c0015321a3816252e221a29221e3626150c32380526341c011220292e39102836142734031602370d02150b1500313a000000),
  (0x0, 0x2d04150d3a2e3918343418361d11043721391919162c0313281c001c382c28040d0a3536263320090822151125100a0c100a10190d1d071119102531032106303621162c38370a050d29051230082e241d2e222b022b06062c31230b11180d2b0331230503302f0a332c202528293839340b051a3a000000),
  (0x0, 0x82f1b37191410241e000301321c201415120a1b2a1c1a33071235341d293514071e0a2c13121a240311012830333a092e332b3808240e3620191d290d082b1e1c011e06343802320c0406241e0408372032030b210730091f2e20321b372a10220323030928092c322823161600343a0f1d1f3a3a000000),
  (0x0, 0x123131132e31030017031e221b30062b11331d1b00000034212038002c140932050a1f260b261f2b0c283813011024151424120c39363422010b0911082d042e19240f2d00002d0837272012371f141200000532231f3410391d1d3a030425290f351f2f38040e1731060c06100a360e360d22173a000000),
  (0x0, 0x3162e0d0f011f250904140c162208330921002a38121f0b2e022e1737223832352734250f32340819280710151812382d1c181e38091b0a232c1b0b1636081d151e0d33350c1702140336290618073102363110012b291908031a331f242517160b092b2d200206301225032c2e3229321e261d3a000000),
  (0x0, 0xe3705290b0e2a39260a3518170909122522041b0c0d1c0a183906342b0f052d39191d02383714372a0333302b27390b011a0f310118271e21141f222c1c0639211e0f171f112725372f28311539343434063610391e17203930170a03122027232c2c31031b33342f222e0f031b092634021a1d3a000000),
  (0x149, 0x6060d332b021c0b3110330726380c321833251e08262d090e0332001c3009060b021a21182536052e1c1f121c252e24191b061e070f15141b00032f2d13201d042c320c002a1e331635141f2d06102b31202f2b0034042d0f1514323617240d260827383033262b2e260d31212a16291b1e370f3a000000),
  (0x0, 0x10352a2f20352a210106322215163114370d350803013311132b1737280c103031200b2f1a151924041d24162733382536272f2c0e1836150f2b250335182813340922352c110511040119100532392e100e23000728172b1d10112f36310638162b333221030a262d311405020d2a27122807323a000000),
  (0x0, 0x25062d1401160120182132221429021d070f32070e3605181f091b1d201a022923112b1c2f3614170d2c13291a02060b20150f2f10303719120302372d0e171118121e13181516101b2c20350f072a1f0503172007100c042e1a0e20342a0413110c201e0e161d252c13230a19362e10232a23293a000000),
  (0x0, 0x232c292e1e180832381e32302f202f2f2d3a2e06092c33052a2d11122902181a152a27070a2e06200d2a1d280d132f16223828112329181e0e2f0702112a373409080323050a00190d181d1d0d0118012420030011232f04311b0b3618292c2f22032810182a35282b39172a090c193a030732333a000000)
  ] : List (Nat × Nat)).map decodeUCert16W19

private def sieve16AffU2C1W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x18b, 0x29030e0021123512003a041232090030240f1936010d0e16321a140d230e210b2408111b05300c1f2928133a0d362024142a2e333509291b0c1c1e121201240e2e2f162f28212a37392822323a14160a291e1432160b0101111c083a08380d14220f32001d0c242f2a130032250f152d162d0d0c3a000000),
  (0x0, 0xa1417170d050b0b0038071208222e1e34352e0106220a2f272824000426231415172813381c1c2f250a011f1c291327041c122028363623280d3130230c252224372b0b0e2b273a2918001f221e14272701193016333a0223290538030f32090f2f252c0a0d223a291a37351d1e2f2f151917043a000000),
  (0x0, 0x112e372e0901162b1b1b0739040e2b09182d030e351a0818052313022623130004192317011d040f042c2632112f270f3a251528011a38260f342526322c0c091b282321261d2a223530060024290b0b0814201736132206272302091a2f1d262535231720091a0e28081b29102d310d2e3220133a000000),
  (0x0, 0x25123501351c123427192e340f20131d33083117370f26281b2806271f180c04012830122c071136372c0407281407380a2b1b02010902342a082b2518231309383a380e2e1e392316100b31301a2e053939361b2b1d13022d163a1a2800322b2c2714260518072127322c2a2f291d2c273203013a000000),
  (0x1ac, 0x1c3928231301141f380028161507051715262b100e1f0016090c0c1e10012b00290d0f25102e33090b090b07341e390f05151b1c33383607140c37290f2231290d323a180c33340d09182c172411251e2c1d160016331f17383537071b00222418220e20041e2e382601081c3605203609122e093a000000),
  (0x0, 0x1270c0d3113212920192e202f121514001e13302f2f072d04353803070c0d331c2c1c1907392d2a0009310324171839230424192d321e0f06390325013a16330d2b0733160331132336273227030d031d211c3809261338062d3414081822310b1739312a0f0118252b3838331c023924082e103a000000),
  (0x0, 0x2c1d3234153719010106151e33061f1c1a1733201f2f030539162c1b2e0a39321c26141639051202140a292e29200e033232010e3834110c3028342a0c280e1f351b3a1e22130806363813140b0b231f3521093708131d0a0f1931361a1b171610062126212c2a3724072e12083603332c1c06203a000000),
  (0x0, 0x27230f3707261f193a321d03122205101d1f160c2f2a290004361c27030f08371f0306292c28350a2d2016060e18060110262901131203352b31240b13281f0820382d0831193031312e2732152c17062a12251b193a172b0a0c2e0c2a0d2c2c282624311c2b371f231b1b1f12350c271b331b033a000000),
  (0x0, 0xd330e1f15241932280f1d19100b330d03240f28361f242e00192c1c0e2c0e082e0f2f2c31243708042a270b16012f37393104270c290c2a1910043933310f2e21250e2b242803202f2c250a291b37103338321e3516213535072b2a340c0404210f10301c0e290b220e2414362417292b0d1a163a000000),
  (0x0, 0xd190123332c1b1c22202726180c1d33063919011a05171718050f262036151623060c0039363a0d27031611023931220200160607393110251c3832121a1d362a3634160611011c25112e321e2d3101252f17392b2a3009061428292435040b3a070337283613362103071725041a361d0511053a000000),
  (0x0, 0x153a2d00270a03270638133139292d032519260428171f210c3013022700120400220a140404352d321f3210270515032e32100c09281815301a37032c3207082a1f0525010a121512240301311633011b24063339372a092a3325352f18130c183411381306032a200f0031320837073333111c3a000000),
  (0x0, 0x2a070710342c2001110b041f1d181f332b2e0a1437281b050036132d04071305223a200c1928142d24070a1c261c1c23011e2c0727061210190d18382505052721030f1926380e211035220337152323330a1e1f263122222b04221706052b2f25200b29002e05221f2e0e382208030935141a383a000000),
  (0x0, 0x342a3821360406052e09010a2b12131a3323242a213112380521041a090520390d2e122638111a0f0a161703341a10102e1a3a2824380216142a2f350a06200022242a252015041d16010a202c242f1e02020b110428332e20241f342c21250d202d331424280f1e1e0e1a1006202d1b1a0019173a000000),
  (0x0, 0x33331a38122c22292d20191a0a16182f370f03241906341e3a202d2a2b06051c17301612090d2d301f270c040a1b252c3134330c142c1b381b0a002f220033041f3a37211b34322730122735171700070606221b200a080e30241c0718292a351e123210172e2c1e1d0015220027271107371c013a000000),
  (0x0, 0x6270e2e330e20300907152912031a08020b1e20303124181811083a1f2e1318090025283615132908252b042220291f3025113234110f2c121b0d2a322c170710261a1c2a000c2f2904011f14261c32292b2b0017060d050304190717231c0504062a342e1236221c260d351500011023342b153a000000),
  (0x0, 0x92b170b2634152b380605141a27132405040d2f1838212b2d0c223a373a2b0a2216342b2919393803080e13261b240f0c2813062219161f25120a1f063402190f340f000e0d042b3603191f3425252d153135080c26182a0233161e20042a31193102010d34382a1b140a050310130838222c073a000000),
  (0x0, 0x23041e1b2b042739252607392a2626361a2816281217202a200b331808130e2f113538013a07082309101f0c072a1f3007280a243500101828181b23372a081f2c1400271e04203604171121040e222c2f2536280b0314033a141331102b2f1527160338310528361a2c03303a0d0c34321c0f273a000000)
  ] : List (Nat × Nat)).map decodeUCert16W19

private def sieve16AffU2C2W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x0, 0xd010a21140e0504010f1f2d0321342c093614070d320d2818101d000b0932100e340919080121043115311e03180211221d14293027293208231622113319223a283a2013212207342c24301b20101f1328300d2a093a360e07100f041712352501260e002b120b192c121d0c090d08211901133a000000),
  (0x0, 0x83633382a202c2f21042a1d2239161a25170e220010370820210f34180e34130c211a052025120d08061f01220506183a362b1d0b012e023239080b28350239071c0f08110f152b261b14332a0f0c39142700122115171a360c0d0639292233132439032219041f182c1e15120f040d3802341f3a000000),
  (0x16a, 0x2d1e2a1f26271b2f240403083902130c1a1c020500190102182325303a011f251d13360139062135150038292a14161b363024223038080508371c16360e131e0d03101d26252806150c303723303933372f020535160f341b190a24150b1a2c12192d2d0317113717390c1606021b38271d2e383a000000),
  (0x0, 0x2c392c2523062218123a2f2f192f1409223507322224301723031c350436091c2b090b1b253802332726282819351821332c1c1e190e2a22140824011d1c16242905122c0a29300712000f350d380e32372c0f0e193a2e141e2d0711082b11020f34263a261a3a18160b0f162e370225241712363a000000),
  (0x0, 0x1927172e21242b031b2609201a02260e0a252907152622211727262418021e062829122a051f382814382104130b1a0906201c10192b2d232f33383933053a271c190024050322062e310719002a27360d28050f1618151e193504251d190120372d2a250f020d38153a043926161d1200141f223a000000),
  (0x0, 0x2190d001b3a15312207311832030e1b120d072e3526261418023a36001834080a081b380e161f2b0a1e2939311b28060136380c2e343216251e0b1a2e350d0a24371c14253622132a27190c01211434212d15191522161f161601110333282f3538171124003421143a100a171f0e0b2d3117043a000000),
  (0xe6, 0xf1308272a1f0f16321b0e1b281e193305371203391409102d370d3833072a1a1e0a2f35180003331e183625391a20371d081c322c2b001d2c1f3604241f2828061435350e35043120173201191204100c121d302c362c1d2c2339170817201105262d393139210e131e172812000a1f121335273a000000),
  (0x16a, 0x2e300c362434162e0f312c050822101a032a153a00350029070d3a07320208092705300c25021b021f1b32000f223619150e032e0f163a0c1c130d2b0a320f2f0b27390e03061e303800251f2e1d01042f270f31103708352b29361b30221437170a21040503193a123a3606260332022b0c30143a000000),
  (0x0, 0x1342e34331530331130301009281f0c13112b1436060e0018142803361615242615093303230521191325031e132a1a3128240f3a141d1e0c1828381437132f310e070e2139020c14100a291227150f101f0932120e0125271c33242a1c150035091c271b3a172f111e290e352a3a01270c0a2d3a000000),
  (0x0, 0xb21041a0512151317000c18100e041d081c07192a16051d0e070e020e3415202d03080907082536240a343a1e3a27263031201e322b040b270211021f31010e362427000b041e171a3719071c3a113239073a2e25323936121b302b1d0a362b2c1c3419340b062810000a0a1b320e08392d05173a000000),
  (0x0, 0x2f2c012119141d1d280633222b2b313117071116262f2510343317201900280b250d1903102f1b22172a121a29060a1e2433373220292b1b0f09071c0613382e171c022a130627042c0a02322f34061615073703330e20221d1a2d102d3601282133141f2c2d1e250f0b290e3a271e08020d241f3a000000),
  (0xe601cd, 0x405330c1100072131291335312908102d242f0713161d292f2a2833332f0522020e302531101032372d1d2424162e0b312623240b27002a260828042f14330b1f38022b13201a1d1a0e0c100309380b1e143608273a201b04102a3035331c1c291028090d0831260e002b0b1f0d1f2f07301c033a000000),
  (0x0, 0x307321517372d1620252f2c1232003a0e2c12040b36231e182b191e01080007030e0a012631382d31120b391d1e2f0b121e0a22262b34191d0a160f2e352c00241d022600002d0a3004230f14350623000036301b1c34322b15272d2b29122400061d173732152b0d121f170c012f230e00171e3a000000),
  (0x0, 0x2a0e00241b300900000f0e202006350e2a22143823331a27260006021e2b3529302435063921233536061511151429153918341c031f2e0b3615242130130a0a2026180c03221709112f1f31270206272901232d3726240b1530240e24271412282134191c2808340c140b0a2b1a052630311b153a000000),
  (0x1ac, 0x2f1c0b2c372b2d1505002f160c020c361801162e282d052a0e21070b2e070e0615171d27312b082b2d3a070d1a24371c21341e2d08312912060a102f09142e191f3310250808343419212713092330090b342d2c200d041a3a03213622342c101a281c11252f39060b0a1b021d252b1c0c221c083a000000),
  (0x0, 0x33162701171a293a3912200a0615370b170d212e1502341d1d11053129180a0f3123142124252f1132252c1734313a24091e091b242231343a1a3637091421120628383907081f1b08211217001c140f05310a111b082a20171d1e2b110f380529001a1025022d170a042c25222e2d31192935133a000000),
  (0x0, 0x9312236191004132d2b0c32161d3a0510170f2e1f2b221c161828071a0e352613361e2013293818152915223208122226231e2903213730080e26061c153400362223111b260626051223020837043928391f160c020b392d2e1b122f32161938392b180814322c09203301391d321f060005193a000000)
  ] : List (Nat × Nat)).map decodeUCert16W19

private def sieve16AffU2C3W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x0, 0x37333a160c17091c1f110016070f300f090d2112012516381100291b1233102625251e300830133a2f0f231f00371336230b031d11303107080d01003a29292c15271f2d0925330c101c1c090333271d312c200e172a1c2a033118322d223407391b0f24271b0c0a0834111a28001332110f26143a000000),
  (0x149, 0x829130911380f000e2d0d1322062d222a32292f2e042c2222020b00013129372f0a201a1c0e2c2518350639192e0f080d101c0f1712271e381d2f0a0a02261d2a370a200010062c34353727380d0a05331206052f39141c2105151c1b35230031131a050434272707361c183425243a151e11043a000000),
  (0x0, 0x10a25053a2200220c361303351e232c202d2c2724231522112a160c0b023a1c11231301391b1e2e1e34190b1a35332f1636030300121a2f0b321a0f232a2c2d342d1319191f0c2e280304042910212335363009221f1601130f121635121025390e10232c2b100d061f1c000f0202050e0e070e3a000000),
  (0x0, 0x121c342b3709073503182d182822370d153833340a1a390a1a252f2515360411120c163211020f1911172a0b111816310a031b171a0308312a3303122f27081c312a0a16250f00030f3234001f2f20190d0a070c022c023402390f17103a000c0524290506231f32050017301d04182a321f0a113a000000),
  (0x20f, 0x140724252d25370a3a2914202c1f141f182b0f1131372d1a28083315301c33303417312e26142d1b06332923203638352a0a2f342b0b1f1d1932121110300e202f222327131a321607223a16360f100037372f3328122b1b130c36153222220724280a0726182004023803290122330a2d1b0c3a000000),
  (0x0, 0x2a371f382d071a05012f130a010f2213172b071f142b1e320e1a37360722250b0d0d341c2b0d1e2718260c1f1f2927300a162020191f23090f25170c180e3807010326232e2a18280f0833151c0a16282e22100f0c1a272330010932052217312c18273619092012030a1c181515273202343a383a000000),
  (0x0, 0x1b38093221022f0519281a132a38350d320025290f1a220007211d2004052a302d2f2a35130506132010341418381f030410000427062d26201c280d0f362a201426083a06190c1e2f1c1a0427132d0e2a121b20373911252311062b2c23230d010e190c221a30080204131d0b0d0f20101b27153a000000),
  (0x1cd, 0xc392b172d00132d1f262425273729163715362c0e301e2300001c33310e241d0a162825230d1b11133508211519080b1d0723353014382a292600001a01160000133a08331d222c150f2102262239053026292c1c182f010b09031a13310f0a2606000e0f1a2502011a1f2e00000507240000283a000000)
  ] : List (Nat × Nat)).map decodeUCert16W19

private def sieve16InfU3W19 : List (Nat × Nat) × List (List Nat) := decodeUCert16W19 (0x0, 0x2602280000001e10070e21071605261312180c022800000016000000242624280e02060c0f07160128060d10261f250f0b1c2103160228000000150000000d0000001a2523231102111c1503091204011a1e1f09280d13092818260b030201221e1f14011d19210228000000260000001b00000028000000)

private def sieve16AffU3C0W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0xa2012301a4014701c801ec, 0xe210e071f26260000000103000001182826000a01141e092610080902000000280000000d2700002828000026100d27000a01010021030e15230219212028131f1b000000000000000000000000000000000000000000000000090000000000000000000000000a20000000000000000000000000150828),
  (0x0, 0xf091f10152604191a0b05022300121e09031a0e24031228280f0627202414021e0515240a1400130511160d23210e120d141927260b260d2415221c0623012302281e021e1c200d14242815201215191d1f1f0f251b0612101826210e0412100606201e042121022809071807271d082706270128000000),
  (0x0, 0xa151e24041e1a0e0c11180f090e07180f2623160b0712112110191e1526271d1820092715221d0521191b260105201b1b261b011a242501001f27180a0e150d2005041d241f0c06220a161c222110181510191a1b0b232609062320212712210c21180e030525082726130409010626131c092428000000),
  (0x0, 0x3201a1220161713212211230e0d000e26170b2405061108101f1222150f1002071d150f13091e1d111c170227071c16051f260d121924140b19270e2603190109260a17221c000211220205281c12280f1b0b060c0f0414131e2014020e210d230f06110d210b122626161b1a251a040f28200328000000),
  (0x0, 0x423111e271222241b151726260d230b07130f12230f092023192628101f0107010804091512250a0c271a1d1b141a051f1e180c241a182114250e15060d2206071a0d1423181d0a280d151e0d282225110e1d1a060d092108161d180c0a22251e270d25170e272025040e242024261d0623220f28000000),
  (0xe6, 0x62315110c152219230a231c1613230c0b0d000d061024070812062020122508200603280410260503040f1c000b0507060d26041702002622031a272424071204091e2522061205021009221a090e081c1210191c1b091b0f131a260f190b26041e1d071a1a1709240b000a0619280e2117252028000000),
  (0x0, 0x2823231f1c231a211b0e16251a1616161c20000609011c0c0e261c21061727190e18201f020c26122711011323061b1d0528281b0a2408132214231926110d050a04191523151a26270d212704181d1808250216161a1c1b171c1727230b02230514162605061a1f231f210f201310201b241f2528000000),
  (0x0, 0xc10050a1e13170621050a1611161a18020725172607101718062000261b272620091020051f121e0b22270a0c22062619051a091e040223001316122412021d0e1e0b100000071f160b1c0720221a1b00000f0d042117260203142110151b240101140702142210221e241523110e17260c1b0b28000000),
  (0x0, 0x151e270d0b13000616121104280a00180502201d11252423000c062117050a270505020914250e27200d211500021a0b05200024151310271f0a06030f2013250b0e23100f18141c270c1e1c08051f14081d0c1221151705001a11190c1a0f1026132103010b280521220412221a141115041e1b28000000),
  (0x0, 0x200c100f0d04160f0106242209081215260b04160710000d1e25091014071c001906010822162117201f251516142220280d0b1d062314230603161623181d030a260f280720061b1e00071426271628040616242315041e28110e102804230c19080c1a190e1f27201016151d1726010b261f0328000000),
  (0x0, 0x25080b22080e08210a25122007220a2407240b13251118091b1515151a260c040309200d05260e1e1810081d0522241015242003021404251e0a060416032613271c110a25221d0e1b1914032025020713050d04031b23230e0f0b00081d171b16102514021320241f231408071027110216020d28000000),
  (0x0, 0x190c18201123260b0b280e152207190c1112102114121b271b1123051a12070d1314140404070b1a27202213150e2825022707190926232517151b241c061c0b210e0c142228001b0e071f100c1d06151a1825120916021e161d08090c171c1412021d1d0a1a03251e240f1c1b1d131e0c1e081b28000000),
  (0x20f, 0xd281200060e220414211400181e0323172523230817021c2318081c192100112505131b12260b01280f04150a1107100a2026181a112022171627191a13232019211f16140f1c261212220b030512140e1a121205011d1c0705062403002300051c1e0d160d011d18190a1f0821071506091028000000),
  (0xe6, 0x1e020c111917040b13230714101714121f09281a01250d162303190f06070411251e1719212120261a1b24180a081d02190520211b05001921232628260c0f0c0426091500271a081b1c16221f0b0201210e1821170a1c1e0a0d02160727282610240f21170a0c0a1c030b020827130e191d250328000000),
  (0x0, 0x110b28120607230a2525072125010f0d1d15192419041816061320190f0018220721271a1f0d1d0423181c082228191a12100c1114231701200c22082206160c11282318260f0f10150f08220523000f18050c0225031b031b0b2826041b0d0503200c12150811171b121400000e100a121d180128000000),
  (0x0, 0x80c1f180e041b00240f24011d1a111b132120101021080e1b0c1e220e0619121f2415112721120e001d240a1a2721120403220920261c1e080a261418220d09191c06050f110907171c0213050e08240a16271f0205211127222506221621061d240e1a071523281a240b0d10091c0e1b20100d28000000),
  (0x0, 0x121c1d171d2128200a1a0a27001e252116110f23021d040f181c001b12010a0a1c06071b040b1609280f0a1515111a001f221d080f070d13210e1f141c2618031a0c180428091b0b0e0019002110180e181d15270e1b1719131b2222101024221f1724221c131414190b10141a220d1110260f1d28000000)
  ] : List (Nat × Nat)).map decodeUCert16W19

private def sieve16AffU3C1W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x0, 0x1c230c26141701150a0524111125110926201e12000c1d0b001606261e1612210f231e28120a26231509261216062400101b2823280d180c12191920071d030305241924231c1f0801011d27200f1c011b080f0023111a1c220c1f011e081d0f1e100f021e250e0418140f170f1c1c0f2526240528000000),
  (0x1ac, 0x91d011601231e1e1f000f270a1d1c012502250b0b0603270a172513041b0e1a06221c1d0e1d161e01040c21051213250e280503262524032318001e250b2722210d241d0a1024262223241f0f0a1f27151f13200c0e0d0d1d231c180e221321071213261a01242117020e1d1f1c080b0107081c28000000),
  (0x0, 0x30a0e0f082226270a210a1b0f1c1f0a030b26230e05192218112018261e1f1d0a19082606170a0c0b182205092820232810180e12150901170924132508040f272028100d0f2525270a0c190b161211001207071a0723140e2619221010170f141605261812131916141a0515050d09241a020928000000),
  (0x0, 0xe09041e05060d08091c0f1f1b0f2821250a1d140e18270a080c2003171f2704180f210816271e12071d0d001c0e130a162017150e0f0c1204001827161422001b0f16101804101920041e050814091e181a14270e1d0600070e16000d2820091301100608131015150a2219081f1c1206000e1a28000000),
  (0x0, 0x7101b1d021c0703020e052228150504140013180d0021240b000615191d07020e0d06241f240e260114041f0001250f0f1c0e080f1a12062427170f131e200e16281b1100251125190e271b0f150b210c071a231c211722190e13030822191d200721220200191514060b14061a101f081b130128000000),
  (0x0, 0x230904210424030426010017272024191f142519220c1a1609161810071302000015100f081a10090211091418180a2711031e01220d22201d1d0e1b0308061e25261202070a09250b04211b1d1303280f22191f24081f0b1626101c240f121e08201d10170016191305172411210e11220b040328000000),
  (0x0, 0x201023180d001a22051816260e22081c060f1d260919002006200d0d0a000d2020071d0908211e1e240405081c0f0a1a14021b1a171428231806091e1319190e0c192413020d2221051c0d08041f0a22011f1d010f1813021e230d2801241e1313162003061b052112270403191409030f1b1d1028000000),
  (0x0, 0x1917261e0217060f0101260b0e091025241d1f211a2215082115181c151d0b152115120c121a070b0b0b2124211e241a12160306021422090305151b1218270c250b07091c05181e09041b1d181a2827271b23240c261203260c0a1e201a28031d20171e1d231b0411090f051b22281e011d041e28000000),
  (0x1cd, 0x13210e1902002108070f222708181d1d040115181a190e0c171a1004100206171d0200091e11041e251f202107141a130e1d031722030828111826230d0414081f27181a17151b1c1e170d19251920021f161b1f031c1005051b070c28231205121a0b281c1815141009180615150c2114210a0228000000),
  (0x1ac, 0x11061c22112603231f001e25240b120813021c241a031d011f280d281323140b220c2300150c0521180b0b11071b0a110a250d28191a132321121d25181c031e01160d0014100903080e1f04021b0908151a131f18191f0515220423061826230e211e03282206280f001a201604040e250b281328000000),
  (0x0, 0x12020b0026200000061b231b160c0121131a1a280e0a1c130524221818191016081f0b270f0b120d0c0501131622071c0a1a0417201720021d211a280f0d212515141b2405231228150614112506121a0310091c01081607120b01102825031c030a1d090f0d18170e1d1c27090621040704141528000000),
  (0x0, 0x26110a180c08030c090e2821002709241e090b1d1c182208211718210028271500130f1a1c0a1e12022201171524272822161001141903271a2114081b16110a0a120c200e110a1720171814111e04071f2713102417181f070d271b0d1a26181d132516200e1d0a0d240a211c0a1f1b171f1f1728000000),
  (0x0, 0x20232325030c261d1e1c20231c1c0c251e28271427000c0822151d25120a0a09001b040e050d1923090425110a1318000118201810132124040026151214201308151b190a222503220a1b2425260d0b0e021209061b06240707240a110714281b20041020271c010c091615092823190816211428000000),
  (0x0, 0x12081f151e0c150528121f0c0d02070b000314230c1824260e0d0b261a21201612201501030925282014192209031d0a28130e0d1b07161f0b1d16282116201908101228161b081315271416030c0615052605021c0426251c1d210f142212141a1403160e1226250b060503041d26160810211928000000),
  (0x0, 0x91d0d190b010e2602170d1e15250f271f0618020025262401000027242420030a1c111c160606281d23180c221e02151c16171e2805280c22240919170d15011f011a050b1a0d08170e111c19041f021526100b0801161a0b0f1e141e17190916282403012209240a0828091e10121e13280a2828000000),
  (0x107, 0x6260314240810260f0d2623250a0f0c10221d1a0e1c0120050e0f181d0b23192215281e260f27170f061a28000f0f1c0b1810170205040203201821071d1113051519071005071e2728080d21022710200a1105231c180d14111b111f1c032200272516251e0a270920010a0b23131d1716241428000000),
  (0x0, 0x1f071a210102112125181a0c1f1a012214012516011f230a2007082127122806260b10091409170c2106191405211603161e1f19041e231a00031613131d1705060822150a26132420030c2115240c121225210d051f1d1e271a1821170f1e0616150405272101050821051a1b0f0e141124232128000000)
  ] : List (Nat × Nat)).map decodeUCert16W19

private def sieve16AffU3C2W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x149018b, 0x19120410022307012625260a22060023162600280c141b0d121f27001a1a241127182201261910051f0f061a1109170405232302231e0e031720231d2521110c0e0e16160b1b08082017090b0c0708220315260f1108250b07031527101127070428231b1d0007100710260c050b1009181d1b1b28000000),
  (0x0, 0x1b091c0d071517271425041a1e25231b1416210a140805180b23160f2017272512172127100c1c06201c0e120328170e0a240717102403231618040b0b0f1c1f24271e10081117170c08240626112807090b0c270a060d0c211c12191d1800070c1e032104240f1f061a070d1924080b0c0a050228000000),
  (0x0, 0x12162202280c140a1f1723210d0c1b150c25191b060b1c1f0d1f0d0d1e06161c0b1b0908101f090311251407241b250117181e08080911192527170211241a19011c171120132615071b0827252027222724171713220f0e20130f222706211a2717050c092512090503120004080b210e10280d28000000),
  (0x0, 0x25011c032306220808002126230e080f061106231919080b0f0a180a08111227231015101d0f221b1d272017082206110b2801272513230727231f23182628211a251f280d0a1c0c23140a23230107230c011a0911210a1919160c28270a0f04271d16060e1102200406001e2325222200080f0428000000),
  (0x0, 0x1404191b0014231310191e1f21022117001800261d220d23101509240f0c1814020211132222141703261916101115150d10282809262014030506090a02010707190f141312061611191625270d2715181b00022328260a1a1e09000914000a071304241c251e1203011916120b16032722221028000000),
  (0x0, 0x12517101a0016170c1a0a250e1022002506200625110b151a091417171b1d1b250320141e192023121f0417161f0124021d200f202526051b0f0d181a201c0417211809071e12180e050c260a0801210e1022231b171a010e060612250701102227110120220408020312050108241b0c25120828000000),
  (0x1ac, 0x50f07211c15270006001a001b0600172813071f28140016001f211f11230b1027062520240a06181a0c2107280c1a12082812031227151a0004001c0e261d0000151e271d10031f0a17210d0017192707151a0c1d191b1d0d18030d1001051d111b0623141d0802012600090016230d0b00001428000000)
  ] : List (Nat × Nat)).map decodeUCert16W19

private def sieve16InfU4W19 : List (Nat × Nat) × List (List Nat) := decodeUCert16W19 (0x0, 0x4002420000002c3a1703020d0a0540153f082b02420000003900000011180d0e4214012610371a3f03350f29402237172e413d0c1f024200000006000000340000002b013c373e3808373a2e0907052724410f27100d1b08012240131b412639270912310d290b0242000000030000000e00000042000000)

private def sieve16AffU4C0W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0xa2012301a4014701c801ec, 0x341133190a03400000001603000019103040000a313b253a400e020502000000420000001e4100002a42000040212041000a310100021e3214060235413e42280d0e0000000000000000000000000000000000000000000000003e0000000000000000000000000d320000000000000000000000003a1042),
  (0x0, 0x2314180035402f403036113408112a10192f05273e040720140e06410139193d4104030019002e272e0d2b2a3d2a262401093c151b0b401816091c0f401e233d0242143e384230394104422a02070f0c332a0c100f0a06072222401e0e3019212b3b2d38141e0b024227341d122640271f06410142000000),
  (0x0, 0x1033190e293537083513040a051f01292d2c410e3a2a2c3c2d201f1713361c340a0402330e0a17252e141c232822102a1340422241370d2c1b38411626412a172f2e160302182925080c0038091a141d0a3f3a0e0f01110d172a3d3f37300d1010360d0f3e1a270841221620170d412e182c141542000000),
  (0x0, 0x2a12372f191c023033363d2b223c0c3d41290a06362a0a2a42340c08210b0b080d0a23263537092c2f301d1020411f00341e270f1a110c0c3f1a1b14201a07001f1e2b1b0820290708391b152e23301e2c19361d2c23030b02293a150d3b1b410b1f2b0735111a1240212426283e17213b00242542000000),
  (0x0, 0x322c3f170e09161e242f3c04230c3f39161c0f00253a280006033b3425101f11262b17162709401a1f2504101d2003033a0804332d2d1e0519071105331f1c2c280f012c173a15232a1f3823141411020e3c37272d1f1501072c371a0527403926081a2b0f2035203f3037332b3b183326171b3442000000),
  (0xc5, 0x1536190f10190740363a12372026371d4114353a272c0a2d391c1229110d191e17071218243b3c0e24283c230e0237082e32030c1b260322081c142030020c083200060d271f08293e081509263e1017181309370624111f041b340a0b20061e3c173800162629323e0a1d05371634261a26030100000000),
  (0x0, 0x3c2c160a3c2d152d1b0f26292501330130223a322001022a1324180c253307191435280442293c263c1e2f0530092c0a3c29221c103f222110093f2d0e371f0e13160d353e211b381442341f3f3f423a221815232b2f1b0e2f1b313b2924220706220b2f163b0d053d17382633351d002335302d42000000),
  (0x128, 0x41c3219382014343f30301106272e08193436130319022426063f1a3b0f41052a4238000d41380e2142131d17280b1928261c33120d20110c3a3e0d0d2f083501031f01331e0a0d032834252c1a4127032c06102d3d2911140d2e17281725173404163c07113b1f3c21332e420c371f3b0d424042000000),
  (0x0, 0x23053732360f063a2a41183721081f24391d421c011d0c211516272237022120200717201f0f21200b211d0f2a1c3c09240721342324171535001506321d1d373c2d0541353c352d173d042e092415320121333d08401e1b010b2b041b0c401307141f15113d3c3d3b220f1318272d04250c071642000000),
  (0x0, 0x3f291624311d1709130f2d1a362c2c3d1c230b3c3a280b3f351c3a33003401091e2c0c360b410b00243d40282e230422393902011e021b1b04421a360420030c33352341100912271b3412262c293136352a142727043315300c284036021d281418331b19091f1c3a1f032b363405333f37100e42000000),
  (0x0, 0x34250d302c3b2f0b22290d3a0a300713071c12152523312a0219203c1f41293c223b283b343539392a01312b243306251b403439392b02040a3f2d36222d08292f0a06423b40083b3629361f230c020427022524343a0a38254225021c361c00132a381940343042392f1f251337011d3a1a143942000000),
  (0x0, 0x25373814282a39200e140f2730110322162c1e071417222c1238090621253c0d0f15040532033e131d120a3a032c051d062f290313142e0e302c1b04391028163c33010b393527221a1723213d1d41413421162a043b040929122206052e0e091f2241093d190129380a0c041507012d1a2d071042000000),
  (0x0, 0x4013d222f2d2a0735030c3e1a17120806291d252c201c242b200a09243d2201003c42190f0d0710152e41100839292c3f413f2f391b0600220730040036113614303a342007313b091600304021130721010e3f311b292c11391f050c373a180817271a131228143701192e2a1f3904310d2f1342000000),
  (0x0, 0x3a0e08212c19053e16332a0432190a1f29384127383b1b163942401a13190f12383d19162b291828173603283a110c12243f422e0a0e402b37382f200b27030116370a312b132741421d34010c211d2c06041e2b313b02231b2d1c3d052527311c2c0a32292406033642081f1d243b023f422d0c42000000),
  (0x0, 0x40042d410c15213c2a09092312000e0a3b3e1b1a0b180e081d332e01151a2d183e0b41131d1816050032250a01090b0f3f021c413e313e09062420081d292f30112b003a18251337123b193d0e14280014302e353f333b1c0d14191632172b310c0715340e033f393524230205083b191313321842000000),
  (0x0, 0x2c3c2f091c1d01240d3a2033133b142c3c312c201e2d3f1c132011183830420b280e0418313407252e292438320b0331161535320c3f0e071c132d092d3235403b0e14122b270a1401031e1b0c0b03261d372339073b220c280716052b0501031a282c363814203034060f3a021a053c0d03083542000000),
  (0xc5, 0x310f0628122d340e402c1227251f0a08050933102b0e1f0e10230b0a04391a221a1e250d383537120e253e24151b1804220b392235003606280f2d402b2f053c3700041f103e3c2c41421b321d100a051f3d2f040a14032c0e151329120e1a402a3f361c1925292b33282a0c112b2e183400360100000000)
  ] : List (Nat × Nat)).map decodeUCert16W19

private def sieve16AffU4C1W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x0, 0x13310c2e2d2c1f04011f293d313202173c071127212e1f3f0d261c2a131d06411d113a151c392e081e1f32160c373332201c180d272d2d2935071f183d2b3a12220339020142021c2b1024170e2e363503230b312b342b3b1c0810082b380522013e2e0e26272c2a3201051416052d310831214042000000),
  (0x0, 0x2d2b282a13131926402f1714073b2c2c280007020e341c042e3527143d414104250310283815311c243f3c421b290f080b38161108010a2726191f1710182100151323400e0503311833281e092f1137272c061a12070e0d1f030d2c242f3b2f000a00094222312d31013113383a0c1721002e3042000000),
  (0x0, 0xf0b34242b04103e4036303c223240093c2d2408241637170a171d31313f24082810170b0c341d2d3d06410a1a3c351a123e2b0e423f2b410e423c402a0f0c06393f30120e002227030d152b3e0b271741012a01333a39421d3a0a2701013d3c021d233a080e3934300b16293f2f3f03363d0a0442000000),
  (0x0, 0x1e401639191f132e083c16170d402c0e31313211071307173b1f2a350a13303417213b1822192a0a343405190b04100a3d21412b41353828193d013e2a1521233e3e300b2140300a2805421c3723162708302e0a1f0a0e030832072a3738331b26162b1d2837183f2f120a130629323c2120050542000000),
  (0x0, 0x210c06371b2b1e290a17130d2426150020120a3f192132242c251a20381c22280e2817420929140a331c3a0439061b150412041b323b2f2d33053f181a03023a2c2c02401b2e3d3c371e0a32333f3b2606172342153b391c143d04201720330f142c1414120d2a0b2e0106321a060f204009171742000000),
  (0x128, 0x321a2e3d3e32130b112829072a28020538331f400120242d3b070a030f371f070d04340021211b1620170a2c36171a32232c17132f04162d002f3b181c1d00350f26421f21230b161f1b1337010c00321642120326310f2c22260125101a1d2c0c2b040c363c221e2d0d1106001e2335000d341d42000000),
  (0x0, 0x29392c10360c38210e3e13021e1e0f092208160c342e0f0f02052540200303370f3f2842171e21410c040f1202230b0e340803133e203f2f1b36261f21370e082134372f1c0c420e0a2401131a203a200b0c021f071f410f3c2b410b0820050d261c3a0a301c32352c1926351a1f400f343b220f42000000),
  (0x1ee, 0x32a0030020a240e002738121b2f00314110183d2901331a381c401b06110e0d38160b3d331f2f35072e093b1d12363632342230102a0b1f42052d222b3908062d01231b40403d3909251100012e300133022c2a3e2105112d1f3e17171f163f310b051f223d140d2b360f1a20051b323a3d164242000000),
  (0x0, 0x2e3a260b31152d340e01131f1435012905200e313d34130a16144225203938351b1c2541340d333c011a2c3e053005162814050b171f0a1a1414410b2a30062c2c2003263f22113b392c043138221b3737183c1f0c291a400b203b3400232c133037151320272e2c2a2d2e102e241a313c17172342000000),
  (0x0, 0x2a1e0839370c0d1940152d41133f160223363c013539132c2422302f193316050304013022280b230d2612423b25202e340e2527043732041c1e271b421b1a29081a411d27030e321d2e0a38192e40030430330e06201f03281c382107402018041b0f1b3d34030c291020303a06143c281a3b2942000000),
  (0x0, 0x1b1216140840123e002f051e3a322a3b031d1d0a271006300340031d1717181f390b2b2c031821202509270c2534272539323f361405132b4217132b07002b102a16063b3112363a1d3e2d1c2d0436212020212c2610131a0c2e351242170f4002112f403a2d3733283736422c1b39261733192d42000000),
  (0x0, 0x372c2417342015233003270337130f02331b3b30251210132a05190b422332032613270c2d2137230516042821140312181c14122523203216113410182a2c2b3006403c14132131393d112a2624112734152b2a1b212b1e2a05323611130f0a153d2517301d411b272b2c42272e120e1618133d42000000),
  (0x128, 0x27253d352b393d103a1c2623010f2f3426173b2a0d343b2d1c061621272e410d27383a000f321011200b0b263d1002332e33332d0b152b1a2c111c2d200e343004403f20233b313e071b3b14270728041a32001c403e09321b302f0c21271f2c0a2e252a421a05072610013e19322e3e0f123f0342000000),
  (0x0, 0x2e14263f411a343023082c361e143817061c00363e192a293039102d0d1d3726173333352e391a4231022512363f11163d191a062314320635031925381f2d243d3640243b3f0d0117290c16163c34280f1b241c2d3e373820342c212200340e161d2d171722103a252829403c283e3a151f060d42000000),
  (0x128, 0x21362f3334403506103d2e1e172530053a3832293c42091d25332e1603202e040c110a00070338243b3f093424412e001f32020929320b0c0402182f283e3d024012331515253820121b0a34192420022d1d282c201505423c33290d2c0425080e020f221502092e24012e1626080a3e0640033142000000),
  (0x0, 0x2d3c3a312d21152c1311393f2b282e1c0c4035210f2c251632370c192e26002201251623380e17392e3e181a1715243f04123035123615370d0d3d2421162a282828101d413f0f1f40363a0e3c371d112435091601411438261e26203e1a1641181a2c3428260f2623352742162b1614181b1b1b42000000),
  (0x0, 0x32170e052d40161908242333332f0e0708070212161c2e31273224013e3a0c0635211131413d27122d3122040b0c280d03104203372e20421b1c1e2a31212100141c161f292c2f31193f3038090b062205033e0c2f1030343602232a152e3117281b3f1e291c2d222223103c402a312121002f2742000000)
  ] : List (Nat × Nat)).map decodeUCert16W19

private def sieve16AffU4C2W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x0, 0x2a0a0e2b192d3822031d2e130b2002021f3a24274014201f05120f0f2e1337043f410015040621401239183b25343719242829140b141f162c0a381b0c3a29092342033b2a2b183b422e05252f380c0632152a322e000f070002202e05400d100c141d383a131622213121300516283d193a200142000000),
  (0x0, 0x3114202a3d1e083d1f032a0a053c231439141035232c00202b29113d1f403b11162f370e23170a0a1c19071121370d0f2c071e3c1e06142f1d0c2c110c2b0b0e25082418071641250a22422f210c0a28161c131f1c1b3e263e1e1d300d262e39250914010b37342620012c3c2e09261e37351e3b42000000),
  (0x18b, 0x2833131a352941360f2b072d3c3900282521353417033f280436342a072c40071c3318112b0127290b061b3327182135201b2d0d35261238380f16342537010f0c14172a0e211b3c06271f22401f1c36080903072d160f3402331a220d04361540022f071c3e3a2e1f311d26281c2d254134372f42000000),
  (0x0, 0x2825223f3a1c1f16162c0a26063c402a0b18010326060407141d181102171a253f1835150916041205131a083329143c210110003f3c1d280c0830032f1e37290f2c0c060f1d3c19143a2c2226071b37162838171f341816273417343a15403f3c22252a4207333a1e193c1841233f140b1a341742000000),
  (0x1ac, 0x83b33062d2b160b01001008390035233b29292f40043e091a2f13402714371d2d390817102f342e00082517011d3a0b0e050a3621343e30041536162d262a2237313027192d2325392c2f1b343c143305122b09221012142530140d3f3814391f1a240a1f403e071d3c39243640032018210c1242000000),
  (0x0, 0x1e340d0b1a0131160d0b1419001d310d31350336391118120d120c330c31013902281a142f312c3b31283e0833381614170c2e3b3523402d2e423b0d10420d31192e413500380d190534182e2a1f1d091f0b2e36231822241105113926353f363523221e1742021b1c3d26313d24271135122a1542000000),
  (0xc5, 0x213c0e0821253c0c40323026141b0d12281b14300d2f06060103130f27371c131e32413a1d113d21280604151b2905022b1626393b321e201e063e293c1c371505000e3b0506331e250c32200418061a032b0719291a340b153e0e0413210c070403413f3e3729331b35211a2913132a3a321e0100000000),
  (0x0, 0x1b2521223d111730022317103a3a020a1a1c390333132a07191e37270211242119323d270413211734273234231910163000270a04271e34052826072d2d192c3f2f34011c0c3d410f221a0d11151a1611152b3639321a233d1c0b061f363c09252009012722400c1a1d1a03031e22322917041442000000),
  (0x0, 0x334238323b1b2a1901283311390712220b113e2c403b3a22250b0a2e0e311e0641082f27250438190a1501170d0a2202283004321d12222c333129323139410d2e1815151d0a3505172427231c212b0a321d32020b392f0b272008352e0f0932100a05220509152c193021183706081f0136152b42000000),
  (0x16a, 0x835120c2a36221b3426093f38022f111e413d21003a1625361b0e253a2a3a3f36053022082d03072e14340b1b1b103c3e4027282c210126232c29171e0b05382c0c29181302363a3e230a2a06151a04381b10011c260113171f05010a0d0b2d072c1d0f09022f0d181a2342261117133d0b173742000000),
  (0x0, 0x1c3034363319330a4034003a321702072a3d13093631261b32001a4236032d22232b0d3b153c0d0d1906353d130f3a0725152c1818414025022512062e2e0d0c282e412215220223181e16222723201b1432343b08161e19002b02401e2b11002d342f0934131135173d2b2d413d3e1635371b1542000000),
  (0x0, 0x1e0b3a164017222c230140012735260541372901031c2a19201a214022251b3a2907023d31063318334110080f38043418261b0d043d16001338361b370f26392c420f0012290b07271d240c1a3739060a3229132a1700052026421238380209220e2e151b08211e1611091e2f0e2e371c0a170142000000),
  (0x0, 0x313a3621421b143e0d06003312101e1d252401172e351f2b3c2b030110343f2a190936012a3f123f3238351b400d412b3a2007290714112a0b030c27280b06400629061f3f143930193703373804343813051a3536003524063d3f1816351a301f3e3542303d190b15061a3d3d3418373c033d1a42000000),
  (0x0, 0x1e33323d29353a053a1c1322224106172825000e131c332239103510180d0a19012a0b363d0c15360d321010282917183f3a3f0a333a2b0e311639131c120f07040a1b1f0914181f20153a310e20050e103f01371205312429323c334232093c0924221833022b3f141f3c1913203521333c3f3942000000),
  (0x0, 0x93042300805040537111f2f1c3512212f37072934323d39343c1a082003262e3f333a3e31372e1f0a2d2b142e2e183524283919270a3e0a313f13012a03243b110b3e082d372b35143623033438351d3e181a310a2025162a3a3937091442012b1d24260b110a34131a10093e0642381e08323842000000),
  (0x0, 0x8033503332f04311d3d053631023b3f081c111b293335221b321d150d3f1d1e03262b170b20060e2b262b1d0210223d00182c1a22281a162b0d223a1e0d2b15271f422d17203f0b3b09113f04140721072f1005413333413403363f0234203d280c3b3e3b3f122d123a3628051a0821172e1c2442000000),
  (0x0, 0x2d380e2d081f18080a383d191b231c06262f141f13350217393108013e35371f2437081a1836020d1b23270f403c142720352513092a4003072124083d283e3815403b1e2d34362f384131390e151e3929393a3e32162737270833191d20401b0e02151f2d27172a1121322f280a411a040b2e0342000000)
  ] : List (Nat × Nat)).map decodeUCert16W19

private def sieve16AffU4C3W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x0, 0x11131913042c34102126001f0e12371d27162e1402203f421e3d361c23263e243b162f273507312337350736253b2f04381332010c371811112e413a2a3e133304191222100e0f3c05031d0f041d05200d200a1e11292c341f353017401723301e313627001c252b1042322d260f262c2f103f2a42000000),
  (0x0, 0x322a0a072c1022280b39160b102215240e3a1c420a0425093711080028191b22421320391035423f25193a04320422022d37360d082b3e001e39251421100b33033932033c15063607200a302338340442363e3e33382a0837072d3240183c0c3e270f2e1c1a23300f381734291e1a333710400a42000000),
  (0x0, 0x1b0216132417332626383d321a1b381a39402f0b01240f1912410709023321211f261e3137070c0e2c232e0d23061b254210062e081a410b13001c0e31070f37112c0e1c2f3a1f3f3a323520102f1d2a102b0411402d3f3e34142a043909372b260e092b221004390e01401314370b33330c321742000000),
  (0x0, 0x2c0d371434271d2d3722400819270435310c1b2c3b243f3c3b00341c20133c1f3a321941270d1e22022306290307101a051a1e3635002c0e101f14003003053238093d2b183d163a3941063d2c22161b39014205171c3c1a272d272c2e0a1919390322201d363d030d400304360022243d110b3a42000000),
  (0x20f, 0x3401222c0e3519292a082f24282a2c2b2d231e253e1908073120353f151e2b1e0b2a0427410428181211010b400819100e2c222e233141101e122a2713052928100d2f312a13120519002d1d22420c333416022d031c2e0d39240f3d04383a274003361d041b140c28310f292b3f3e3d1a1b3342000000),
  (0x0, 0x251b39012008412c3c42270c3a4021061e141b3c210f0d233c0c25063f18323921203f38032402413d39152040121e2d07211e33032f160a063a18181134231d0c1127013f030105013501082026043c32213c1f121004162c12211a0e3200420a02113c1c1842290b291021311f0d091f26373242000000),
  (0x0, 0x1b020b40072a022e19351722062f26042b381d302c0d2e100a261c09163f072910163e242d2624290935321f34261e2611033715321d0814070721063b17261825400903370f2d1f073e2f2b1237063c33060a1b2b1d234117421e1e27290c041a3b3d42163313420a25070217172f231c2b1e0342000000),
  (0x0, 0x2d3a2e1b06172e0e1a1a39073c220a2c2317210a1c1329142a05102e2742093619330f1d20280a4127031706151f35381626111a240f3a2813272e39180619223b0e0c0b301d1941340a02262c1a05112834163f233c2630130c1b2942350b3f0d1818053f09241c093001342d051b0f2921083542000000),
  (0x149, 0x423833251f093f35241d090f17141c141f1a3d201218400d0b0e3f003a190c12042541181b231201003c340f00023e3d37042e152b3f2c243918230e074119242802220f422f0b25003a3c043b1f243c0f373509183a0e082f0b183b27321400100718242c37073d080e0a3c19120b032a1f1b4142000000),
  (0xe6, 0x3231183e050f062e1639033725381837093f2f2b191a350e2f0f192e08180b3f2e1441163004402904322436050a203a080c0b26400700072927351217203e06051f172e2b0739220d161e2626293323361f2f0a2b30112e0a0d150617100606020a16224204081f0727234221221338043d3e2442000000),
  (0x0, 0x3d192e0538133b0a2a3839293b0203010e3040382c08050d2e2b261611303d2210321e0a372a06351a32082225153013303e36091c373134250d1c360f1b1c343c3c382108012741052f0f033804260d25402224221c1418171b123003142d020b1b214022413605060224163b250e12260f070742000000),
  (0x0, 0x23340d03153e34232628303a303c2e130c150b01060b3b230c071810043b320e0d180623072201011c41111e1b0129331c11010415083b1936160d1c18071033203e27060d300814360a402706261f24230a082a3403201e3c3f0f273c26031c133e370a0f342632051c000f2920132c3210230542000000),
  (0x128, 0x2a3634033a06092c3b0d2e312f06010b05243c05341d40390d1728233203150a0026030021133e042f1f3433061a2a2a09283a0628321e0d2c24013c06231d283e0a13350039102e381b360b382f3128060721150b392810152c0c0808422f344032150f062f0e2004011d043707171d261a053942000000),
  (0x0, 0x3f420411102726291d0f320c3a180c32253f3010023632042e302522110f0c2517223b3d3a391e2c3a41111942402e32342b3f42272d3e0e063e012f1a041e103b3b1403271e41302f25150b0d2016163c002036012b07281d2909270c0d1042084040052a30291203313e1d1327041d2433080842000000),
  (0x0, 0x1225021722083d220f4114263c3b2c082b0f000c271322100230241609182c161e04350b22303f3b2519352606112a0540223327310f02221c0801281e311e022f040a1004273f201c34051c31293f2c09423c0f02363c27002a06002b231d3941350e0311131c08023a26233f2e013f2441143f42000000),
  (0x0, 0x35282b073e283f102338373124412c10400d3f280a0f1239320041200a4115111524151137233f241210181f3006410f0a0a1911272f0c39371d380030242b00000e320500192c0f2c0141352d3c272c3d3119082c25414006220332022709053c2e000024153802013742081b0015421700003542000000)
  ] : List (Nat × Nat)).map decodeUCert16W19

private def sieve16InfU5W19 : List (Nat × Nat) × List (List Nat) := decodeUCert16W19 (0x0, 0x220224000000070108121003230b220e210f0b022400000012000000171c091f0c07130f05161408011517032209181e1c18091f0302240000001d0000000f0000001d02091b091312190e02102418151f200a0703102006211622150e0320120b17131c1d1e1602240000001a0000001500000024000000)

private def sieve16AffU5C0W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0xa2012301a4014701c801ec, 0x90e070e181a220000001b0300001a20102200140c200221220808030200000024000000132300000b2400000309172300140c0100130a1c0b0f021d1d22241f16150000000000000000000000000000000000000000000000001000000000000000000000000006040000000000000000000000000e2024),
  (0x0, 0xc161d150f221a1e0e04091f05221d00190e2115201f141022130623240804191a04100f0b0502031822081d1f1716081b0f0d210f0b220706230d241c21241f0224170319151c181d232405112418001204050a210106150b16220c242109230c00071a0d081602240f211a1a1303060006230124000000),
  (0x0, 0x714001d1e1719190d1b22081a0424120f1208221800182009061c0c101720211a010f1f101f1b181424160a2120080d182303061d1c2411020108070103090d162123101b0710060f14041e17170d121e03141e2418070e0d181f0a21170b191f240c1222170b08231c1212131808161b180f0424000000),
  (0x20f, 0x10e1d0f0702200521001c0722151017150b150e1f0e201318080a0e1901220122010224051a15191e150f15011018181b24140b090f1e082115230a0b150b19161a2424150f080605141d1b1a080e1b210a011c120e0224171c212311110f19110914151f201222150002210f13100f1a0c0f24000000),
  (0x0, 0xb1d190c040723021812091b000c1c1f242206081715231c1910160c1d0803020e130b1302221b08080e171e200421190f13081708100c0701000913120a1b22221e180f040512221e0d071f041a1803111e121304111d091f061924181c0d08211a0d1f060a1820212222020202220f0903030724000000),
  (0x0, 0x1907242323231a0c01160f08001e1b18120721061c03221f1f0819071e150c180112240514081804111b09200c0a11150521020623160a1617010809110a070e1523061019181d110f04021b1b1d0401040f181b1117060b1e1d16040b15200e00171b0d0e24220d200e1307221420141d17100224000000),
  (0x0, 0x230804170502081d16241e0905240b091d102024190d1b091d101d13060403062221101118220a0720011f16221b011124061214110b210307141f0d042112181319210214050c162010031b131f050810112112110b06061d0f13220c1e051312232019141710231f2323060d080416120d120c24000000),
  (0x0, 0xc071d181c181d240a1c0522190019061e21050d0012001f0d2013010a0c2120020b181c16130b121d021f0711120508051a0b0e02060e230c03040c08011d070f112421241c1b20141b16031c0b0d00241b0e21141d1c03230810051e002319100f2209081413181e222210131e0a23071e161424000000),
  (0x0, 0xc0f1e23160514101a07051000132121041807240c0b1c1b1d011f0308200307021f0f0b0f2203001723020e1d1e122102091311071a071e240c201d1a01181d06121e17051d1323131f11051f1f0d0409061024231f1f1a08140d18220c072007040b090e180c111d23191e0c0711210c081f1324000000),
  (0x0, 0x2101c071408000d20151104120c15071119211f0f0e0d1008171c1408010d0e1407161613171f1f0720130b1f0020042100031f0313230b1e1d1406001b1319060d1d23220f012202220d160f1b23170011100b1f09220a04130a221513001c0a21090a1121170e1c050b150808091b110c1f1824000000),
  (0x0, 0x15230116020f18201d001402030005201902221317191e1518201f150d1a1d1823020a16170510030d140b10222002031a0817091c08110a0109050a121f0a1d110b011b1f18031c0c0c1f1a01242106172217000e0f080d162307021b041b160a2013201420110f1b11041d072019161a08141a24000000),
  (0x1cd, 0x220f04171c0003170714070c021a221f001e1e240c23131f14091211172006171a0c041f0d24230b170c1c1724241924011d0d140311171600050e031503071813100911001a0c0e1c11170919011d0f17141721120d0118101104051a1c0d210e14061b081902141a201602031923111d0d121524000000),
  (0x0, 0x81c051622061119120e1122081d1e1f171f1012061e062008130723040a1c000d050919150a0d1f1201161e0218090212000b1a0918230f030a0611100622040d10201b0b1100200a190e09151b240709001e081e1a0824230d011e0c1e2010230701220c0a081d19071f1a16010e210221181524000000),
  (0x0, 0xf110f1b1b041e16181f1c1b02201c0b0d0f06171a24230b1c1d00230122000a030b0b18230f0a211e0f06221e180c121d0d1f08081a0a22191706000214180c130f19030f100e160116150d1b1d20020e21070a0b0d170d0f1f230f1201221921141b241d072105180e1824020823130c19121624000000),
  (0x0, 0x2100316041e0d0023220b11180508141b090605091b19220723031c1f0c14020f00160c241008090f020924050504061a1f1f13121e00060c1f170e151f15060c1721000e0f15131824191f0f06081b15070a0e1704021a0e022019171d0421061a08160f081c161713211006190d0f0f1f190e24000000),
  (0xc5020f, 0x101b16001f120111240c04132220221a1e09231f090e1b1e090c060c150200222220190d1615060b0f100b071e230710212102071e070101241d001310060511000e18031e2109081e0f200e1e021f2209140105070e1e05111d1d0621040d2005020221011e061624151716181521061e070100000000),
  (0x0, 0x81a13090d12171a09050820161813091e100f1b0e0223040b1e1615080d0b200d07140b0d0c170801090c130718051d0e0906202313210801060f1f241a0b0203190a19091a1413110d201f101b1e00221d211a1506061217051a190822091e10231c151c20061f151219090a0d101b1923220c24000000)
  ] : List (Nat × Nat)).map decodeUCert16W19

private def sieve16AffU5C1W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x0, 0x24220b071c120b0d0d0022151a12090b2008091b2404230d070319141e1820071f051e001c061c1c241b0019010a1c052412040c11121b13191d08150d23230d1b0f142106230010160b01031c0e231d1e231314221f1e051a121717211306080a24081d0b200a171407170e150d241301180a1624000000),
  (0x0, 0x181e0f111a2022211824191801081516070720242116131a22240c160411180d231d231e0f0b07140208220f0e131809062406240f1a1d021f0304080f091d000e06131c040c08130e240c0801081d061f221a0413121c17120e14020a0701222204221815191e131321230d231e0a060700171f24000000),
  (0x0, 0x2017000e1002081d0c181006041920031e0c150b18090d210c000b081b0319092307071117150c0e082221021e0c05201a0d20040d161015090b1b1d0a172115142406110b181d080719190c231d0d1f1f24160e241110060f0e1119101c191b1d0e241102170713121e241c220810060310110124000000),
  (0x0, 0x2321191e08010208010918231f1322061111160216161206152223231b20190007131c2408241a121315101c0a0c01080022120b0e15011a0c080d231f091e042015120502171c2100040f0b05170c040a1a0d1009051f081e120e1e0122121618140e1002051b17112124160205081e0621051024000000),
  (0x0, 0x110609200b012100101c1f2321001b0b0a00070d18081b0b060006211707201f1214010b211e0e14220f1c040424090200160b231105060d0c00220a1d1c121403141d0117111b0a20201a14160a180821180b1a17011e0011050b121d1f1d21221a0c0020151f1f10151819211b020d1211221124000000),
  (0x0, 0x120e0e09151c0d13152400190d1223070316130b1c151d02170b17211b1d0d1218230c171b080706182304230714100307181d0f1108210211111f0e211f160217190d0612071b1b1f0507010a0e10000f071c0e1e201d1d0620081d0e1c0f031a181820111201060f05071b130c120a0e230e0c24000000),
  (0x0, 0x1100f09080818081018111b2219121f071b180d001c03221a0d0f1d1c1b1213030c21131a030c1817170d1f17100009051b1018070b1e1e06001e10231c0f2403090d21171c062404130221081f0b1f1b011a2308150b060d0205121e24080f2201150c1b0009160e071420110818111501221c24000000),
  (0x0, 0x23230b0f0e2009040a1605040f1b181c1900120209021900180822040624081100121f21191f170f08220f0a001e05211706090f220c130408070a11011112171e200d1b192307180b23170921082219070908130d16020a241f020f1004231306020513220a04050d101b23020c0210120e070524000000),
  (0x0, 0x1f181f010214240d1d220f080f1204000406070300120a071b0c0b1f141b230c060b13150708120e031623001e1c0d170d141e131704080221120f10012417021c2405022315181519202006170a13001602070a0615040b0c0d2408221a1500051a0a030b011d1d0c101d1d1f0919070d23090124000000),
  (0x0, 0x1c07121f03191c22150c130411071d12240716120a1a07190423050d0b1c0b0e22131b1e0f0b0b131718090e1300051f0508120b061e22181c0c17220924110304131104132006101d0117011b2416110c1a040b1a130b051811210817212205082000031e1d23140b1e240c090517191322211224000000),
  (0x0, 0x1410140813201b0a0601121a20191f08081d1202220f2316182302040e0a23070d1e141c0d1323191315140e12200216061b1b170111091923151410221615211909020a041b2417190c1a23150121090c111a22081614000c231e1e23200c1b202410122019140f0a1a16241d17010b0f040c1c24000000),
  (0x20f, 0x61e0210051f161907010c1e08221e0f08111a0e1b0801011a1d0a020b091323210c240d170d231e1007052206111f092411200c15160324150e0f07090701150d0411021f0e23180e1a1f100a131101051f03120b030c09131b1c2402050403081521101b0e0e09050e0a152101121d24101824000000),
  (0x0, 0x1401041e22170f2123210d1d0520241f1a231b042306100b0e030301161c051506211703001b13120309180414060d212402051e03171c03240408061d1d17050f080316121a12090f0b241e02060d13051d1307241818141f14181f01170c061110021a03081911082319240e1c05070d20161d24000000),
  (0x0, 0x4240a0200101e132010060321011c1c1b111c131b090a0821151f15230606030e1f1b231f0216150c060f19150420021a220d24081907150b211b0f1c1b1206190f1e0f0914000a051c0b1a091a230a0b0b150a060f241524081516111205101507171e19041218070510110d010f1a121f0c1624000000),
  (0x1cd, 0x1424010609000d061e2001091f1d0c1b18230b0b020907201b000f09070c0d150316201215012218161f0a011e1420021810100e1d23221c0e23131a1f120b1b1c04240a0e1220130e0b1d1c0806110c09031402080f0f0d240f1207130611080e23081c21031523062411081c0b1c0a190a092124000000),
  (0x0, 0x824241d1b061f1814041b0b07131b0306051a22032400140c1f04130a1f1a1808071101220c0120110b1e02081405211c0b080e1b15010618101514021a231e070e05030f0816181a050c130c080610140e190b02071d06161d0f1c0b070e20241a1f180f23030d0503172003171f1d01071e1724000000),
  (0x0, 0x1a1a080a05240606112316190324170511040c1e0f2311030d141e040e1c18111e011b140502200913021f0b13102419070114092107050d180c00060102171f0c0d1f171f0c190c150c1503210b1e1a0f2218011f230a0505060c112314211616000303210e0d2004101c17170b061f0d06191824000000)
  ] : List (Nat × Nat)).map decodeUCert16W19

private def sieve16AffU5C2W19 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x0, 0x90d17180a160f0d081c191924170b09031115231500041213190f1d1a1a1513091400040002030e15040514050f242320000c13170f19202011210b0f2102180b1c1818080d03021b100d20160b0108041816191e1100110417090f101821200508111c2416051203121c111501070c220d1a0924000000),
  (0x0, 0x1a101c0c1a0620211020081700031a051007041e151d231d160218220d0d00131c241c091119061f0407010e1117130d19190a1b1c210b0b130e240517050d17122306241517200b1e03041c0d0e220c231213220303050c1c1806180208050f180e240e0e0f1a0802161f190f1e1b23170e130224000000),
  (0x149, 0x1211c0f150b10200b1700081c0e09100f1d06000a1b1e151d1312000c1001150e080f1b13001c0907111720201723070c08190d031f1316101a240021070000001005210f060a1e230f1e1b20011607090d181a05221f0417160301030c17241b0315011e0b0f0201100f1d06000e1f0000001524000000)
  ] : List (Nat × Nat)).map decodeUCert16W19

set_option maxRecDepth 65536 in
private theorem sieve16_aff_u1_c0_s0_w19 :
    checkAffRangeULModP16FastBoolW19 1 31 0 3 (dropCertsW19 0 sieve16AffU1C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u1_c0_s1_w19 :
    checkAffRangeULModP16FastBoolW19 1 31 3 3 (dropCertsW19 3 sieve16AffU1C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u1_c0_s2_w19 :
    checkAffRangeULModP16FastBoolW19 1 31 6 3 (dropCertsW19 6 sieve16AffU1C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u1_c0_s3_w19 :
    checkAffRangeULModP16FastBoolW19 1 31 9 3 (dropCertsW19 9 sieve16AffU1C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u1_c0_s4_w19 :
    checkAffRangeULModP16FastBoolW19 1 31 12 3 (dropCertsW19 12 sieve16AffU1C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u1_c0_s5_w19 :
    checkAffRangeULModP16FastBoolW19 1 31 15 2 (dropCertsW19 15 sieve16AffU1C0W19) = true := by decide
private theorem sieve16_aff_u1_c0_fast_w19 :
    checkAffRangeULModP16FastBoolW19 1 31 0 17 sieve16AffU1C0W19 = true := by
  have h0 : checkAffRangeULModP16FastBoolW19 1 31 0 3 sieve16AffU1C0W19 = true := sieve16_aff_u1_c0_s0_w19
  have h1 : checkAffRangeULModP16FastBoolW19 1 31 0 6 sieve16AffU1C0W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 1 31 3 3 0 sieve16AffU1C0W19 h0 sieve16_aff_u1_c0_s1_w19
  have h2 : checkAffRangeULModP16FastBoolW19 1 31 0 9 sieve16AffU1C0W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 1 31 6 3 0 sieve16AffU1C0W19 h1 sieve16_aff_u1_c0_s2_w19
  have h3 : checkAffRangeULModP16FastBoolW19 1 31 0 12 sieve16AffU1C0W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 1 31 9 3 0 sieve16AffU1C0W19 h2 sieve16_aff_u1_c0_s3_w19
  have h4 : checkAffRangeULModP16FastBoolW19 1 31 0 15 sieve16AffU1C0W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 1 31 12 3 0 sieve16AffU1C0W19 h3 sieve16_aff_u1_c0_s4_w19
  have h5 : checkAffRangeULModP16FastBoolW19 1 31 0 17 sieve16AffU1C0W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 1 31 15 2 0 sieve16AffU1C0W19 h4 sieve16_aff_u1_c0_s5_w19
  exact h5
private theorem sieve16_aff_u1_c0_ok_w19 :
    checkAffRangeULModP16BoolW19 1 31 0 17 sieve16AffU1C0W19 = true :=
  (checkAffRangeULModP16FastBoolW19_eq 1 31 17 0 sieve16AffU1C0W19).symm.trans sieve16_aff_u1_c0_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u1_c1_s0_w19 :
    checkAffRangeULModP16FastBoolW19 1 31 17 3 (dropCertsW19 0 sieve16AffU1C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u1_c1_s1_w19 :
    checkAffRangeULModP16FastBoolW19 1 31 20 3 (dropCertsW19 3 sieve16AffU1C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u1_c1_s2_w19 :
    checkAffRangeULModP16FastBoolW19 1 31 23 3 (dropCertsW19 6 sieve16AffU1C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u1_c1_s3_w19 :
    checkAffRangeULModP16FastBoolW19 1 31 26 3 (dropCertsW19 9 sieve16AffU1C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u1_c1_s4_w19 :
    checkAffRangeULModP16FastBoolW19 1 31 29 2 (dropCertsW19 12 sieve16AffU1C1W19) = true := by decide
private theorem sieve16_aff_u1_c1_fast_w19 :
    checkAffRangeULModP16FastBoolW19 1 31 17 14 sieve16AffU1C1W19 = true := by
  have h0 : checkAffRangeULModP16FastBoolW19 1 31 17 3 sieve16AffU1C1W19 = true := sieve16_aff_u1_c1_s0_w19
  have h1 : checkAffRangeULModP16FastBoolW19 1 31 17 6 sieve16AffU1C1W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 1 31 3 3 17 sieve16AffU1C1W19 h0 sieve16_aff_u1_c1_s1_w19
  have h2 : checkAffRangeULModP16FastBoolW19 1 31 17 9 sieve16AffU1C1W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 1 31 6 3 17 sieve16AffU1C1W19 h1 sieve16_aff_u1_c1_s2_w19
  have h3 : checkAffRangeULModP16FastBoolW19 1 31 17 12 sieve16AffU1C1W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 1 31 9 3 17 sieve16AffU1C1W19 h2 sieve16_aff_u1_c1_s3_w19
  have h4 : checkAffRangeULModP16FastBoolW19 1 31 17 14 sieve16AffU1C1W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 1 31 12 2 17 sieve16AffU1C1W19 h3 sieve16_aff_u1_c1_s4_w19
  exact h4
private theorem sieve16_aff_u1_c1_ok_w19 :
    checkAffRangeULModP16BoolW19 1 31 17 14 sieve16AffU1C1W19 = true :=
  (checkAffRangeULModP16FastBoolW19_eq 1 31 14 17 sieve16AffU1C1W19).symm.trans sieve16_aff_u1_c1_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve16_inf_and_inv_u1_fast_w19 :
    checkAllInvModPBoolW19 31 31 = true ∧
    checkULModPNat16FastBoolW19 31 1 1 0 sieve16InfU1W19 = true := by decide
private theorem sieve16_inf_and_inv_u1_ok_w19 :
    checkAllInvModPBoolW19 31 31 = true ∧
    checkULModPNat16BoolW19 31 1 1 0 sieve16InfU1W19 = true :=
  ⟨sieve16_inf_and_inv_u1_fast_w19.1,
   (checkULModPNat16FastBoolW19_eq 31 1 1 0 sieve16InfU1W19).symm.trans sieve16_inf_and_inv_u1_fast_w19.2⟩
private theorem sieve16_aff_all_u1_w19 (t : Nat) (ht : t < 31) :
    intDet 16 (apow16UW19 1 (t : Int) 1) % (31 : Int) ≠ 0 := by
  if hc0 : t < 17 then
    exact unpack_affRangeULModP16_w19 1 31 (by decide) 17 0 sieve16AffU1C0W19 sieve16_aff_u1_c0_ok_w19 t (by omega) hc0
  else
    exact unpack_affRangeULModP16_w19 1 31 (by decide) 14 17 sieve16AffU1C1W19 sieve16_aff_u1_c1_ok_w19 t (by omega) (by omega)

set_option maxRecDepth 65536 in
private theorem sieve16_aff_u2_c0_s0_w19 :
    checkAffRangeULModP16FastBoolW19 2 59 0 3 (dropCertsW19 0 sieve16AffU2C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u2_c0_s1_w19 :
    checkAffRangeULModP16FastBoolW19 2 59 3 3 (dropCertsW19 3 sieve16AffU2C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u2_c0_s2_w19 :
    checkAffRangeULModP16FastBoolW19 2 59 6 3 (dropCertsW19 6 sieve16AffU2C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u2_c0_s3_w19 :
    checkAffRangeULModP16FastBoolW19 2 59 9 3 (dropCertsW19 9 sieve16AffU2C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u2_c0_s4_w19 :
    checkAffRangeULModP16FastBoolW19 2 59 12 3 (dropCertsW19 12 sieve16AffU2C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u2_c0_s5_w19 :
    checkAffRangeULModP16FastBoolW19 2 59 15 2 (dropCertsW19 15 sieve16AffU2C0W19) = true := by decide
private theorem sieve16_aff_u2_c0_fast_w19 :
    checkAffRangeULModP16FastBoolW19 2 59 0 17 sieve16AffU2C0W19 = true := by
  have h0 : checkAffRangeULModP16FastBoolW19 2 59 0 3 sieve16AffU2C0W19 = true := sieve16_aff_u2_c0_s0_w19
  have h1 : checkAffRangeULModP16FastBoolW19 2 59 0 6 sieve16AffU2C0W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 2 59 3 3 0 sieve16AffU2C0W19 h0 sieve16_aff_u2_c0_s1_w19
  have h2 : checkAffRangeULModP16FastBoolW19 2 59 0 9 sieve16AffU2C0W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 2 59 6 3 0 sieve16AffU2C0W19 h1 sieve16_aff_u2_c0_s2_w19
  have h3 : checkAffRangeULModP16FastBoolW19 2 59 0 12 sieve16AffU2C0W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 2 59 9 3 0 sieve16AffU2C0W19 h2 sieve16_aff_u2_c0_s3_w19
  have h4 : checkAffRangeULModP16FastBoolW19 2 59 0 15 sieve16AffU2C0W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 2 59 12 3 0 sieve16AffU2C0W19 h3 sieve16_aff_u2_c0_s4_w19
  have h5 : checkAffRangeULModP16FastBoolW19 2 59 0 17 sieve16AffU2C0W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 2 59 15 2 0 sieve16AffU2C0W19 h4 sieve16_aff_u2_c0_s5_w19
  exact h5
private theorem sieve16_aff_u2_c0_ok_w19 :
    checkAffRangeULModP16BoolW19 2 59 0 17 sieve16AffU2C0W19 = true :=
  (checkAffRangeULModP16FastBoolW19_eq 2 59 17 0 sieve16AffU2C0W19).symm.trans sieve16_aff_u2_c0_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u2_c1_s0_w19 :
    checkAffRangeULModP16FastBoolW19 2 59 17 3 (dropCertsW19 0 sieve16AffU2C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u2_c1_s1_w19 :
    checkAffRangeULModP16FastBoolW19 2 59 20 3 (dropCertsW19 3 sieve16AffU2C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u2_c1_s2_w19 :
    checkAffRangeULModP16FastBoolW19 2 59 23 3 (dropCertsW19 6 sieve16AffU2C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u2_c1_s3_w19 :
    checkAffRangeULModP16FastBoolW19 2 59 26 3 (dropCertsW19 9 sieve16AffU2C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u2_c1_s4_w19 :
    checkAffRangeULModP16FastBoolW19 2 59 29 3 (dropCertsW19 12 sieve16AffU2C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u2_c1_s5_w19 :
    checkAffRangeULModP16FastBoolW19 2 59 32 2 (dropCertsW19 15 sieve16AffU2C1W19) = true := by decide
private theorem sieve16_aff_u2_c1_fast_w19 :
    checkAffRangeULModP16FastBoolW19 2 59 17 17 sieve16AffU2C1W19 = true := by
  have h0 : checkAffRangeULModP16FastBoolW19 2 59 17 3 sieve16AffU2C1W19 = true := sieve16_aff_u2_c1_s0_w19
  have h1 : checkAffRangeULModP16FastBoolW19 2 59 17 6 sieve16AffU2C1W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 2 59 3 3 17 sieve16AffU2C1W19 h0 sieve16_aff_u2_c1_s1_w19
  have h2 : checkAffRangeULModP16FastBoolW19 2 59 17 9 sieve16AffU2C1W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 2 59 6 3 17 sieve16AffU2C1W19 h1 sieve16_aff_u2_c1_s2_w19
  have h3 : checkAffRangeULModP16FastBoolW19 2 59 17 12 sieve16AffU2C1W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 2 59 9 3 17 sieve16AffU2C1W19 h2 sieve16_aff_u2_c1_s3_w19
  have h4 : checkAffRangeULModP16FastBoolW19 2 59 17 15 sieve16AffU2C1W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 2 59 12 3 17 sieve16AffU2C1W19 h3 sieve16_aff_u2_c1_s4_w19
  have h5 : checkAffRangeULModP16FastBoolW19 2 59 17 17 sieve16AffU2C1W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 2 59 15 2 17 sieve16AffU2C1W19 h4 sieve16_aff_u2_c1_s5_w19
  exact h5
private theorem sieve16_aff_u2_c1_ok_w19 :
    checkAffRangeULModP16BoolW19 2 59 17 17 sieve16AffU2C1W19 = true :=
  (checkAffRangeULModP16FastBoolW19_eq 2 59 17 17 sieve16AffU2C1W19).symm.trans sieve16_aff_u2_c1_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u2_c2_s0_w19 :
    checkAffRangeULModP16FastBoolW19 2 59 34 3 (dropCertsW19 0 sieve16AffU2C2W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u2_c2_s1_w19 :
    checkAffRangeULModP16FastBoolW19 2 59 37 3 (dropCertsW19 3 sieve16AffU2C2W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u2_c2_s2_w19 :
    checkAffRangeULModP16FastBoolW19 2 59 40 3 (dropCertsW19 6 sieve16AffU2C2W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u2_c2_s3_w19 :
    checkAffRangeULModP16FastBoolW19 2 59 43 3 (dropCertsW19 9 sieve16AffU2C2W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u2_c2_s4_w19 :
    checkAffRangeULModP16FastBoolW19 2 59 46 3 (dropCertsW19 12 sieve16AffU2C2W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u2_c2_s5_w19 :
    checkAffRangeULModP16FastBoolW19 2 59 49 2 (dropCertsW19 15 sieve16AffU2C2W19) = true := by decide
private theorem sieve16_aff_u2_c2_fast_w19 :
    checkAffRangeULModP16FastBoolW19 2 59 34 17 sieve16AffU2C2W19 = true := by
  have h0 : checkAffRangeULModP16FastBoolW19 2 59 34 3 sieve16AffU2C2W19 = true := sieve16_aff_u2_c2_s0_w19
  have h1 : checkAffRangeULModP16FastBoolW19 2 59 34 6 sieve16AffU2C2W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 2 59 3 3 34 sieve16AffU2C2W19 h0 sieve16_aff_u2_c2_s1_w19
  have h2 : checkAffRangeULModP16FastBoolW19 2 59 34 9 sieve16AffU2C2W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 2 59 6 3 34 sieve16AffU2C2W19 h1 sieve16_aff_u2_c2_s2_w19
  have h3 : checkAffRangeULModP16FastBoolW19 2 59 34 12 sieve16AffU2C2W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 2 59 9 3 34 sieve16AffU2C2W19 h2 sieve16_aff_u2_c2_s3_w19
  have h4 : checkAffRangeULModP16FastBoolW19 2 59 34 15 sieve16AffU2C2W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 2 59 12 3 34 sieve16AffU2C2W19 h3 sieve16_aff_u2_c2_s4_w19
  have h5 : checkAffRangeULModP16FastBoolW19 2 59 34 17 sieve16AffU2C2W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 2 59 15 2 34 sieve16AffU2C2W19 h4 sieve16_aff_u2_c2_s5_w19
  exact h5
private theorem sieve16_aff_u2_c2_ok_w19 :
    checkAffRangeULModP16BoolW19 2 59 34 17 sieve16AffU2C2W19 = true :=
  (checkAffRangeULModP16FastBoolW19_eq 2 59 17 34 sieve16AffU2C2W19).symm.trans sieve16_aff_u2_c2_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u2_c3_s0_w19 :
    checkAffRangeULModP16FastBoolW19 2 59 51 3 (dropCertsW19 0 sieve16AffU2C3W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u2_c3_s1_w19 :
    checkAffRangeULModP16FastBoolW19 2 59 54 3 (dropCertsW19 3 sieve16AffU2C3W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u2_c3_s2_w19 :
    checkAffRangeULModP16FastBoolW19 2 59 57 2 (dropCertsW19 6 sieve16AffU2C3W19) = true := by decide
private theorem sieve16_aff_u2_c3_fast_w19 :
    checkAffRangeULModP16FastBoolW19 2 59 51 8 sieve16AffU2C3W19 = true := by
  have h0 : checkAffRangeULModP16FastBoolW19 2 59 51 3 sieve16AffU2C3W19 = true := sieve16_aff_u2_c3_s0_w19
  have h1 : checkAffRangeULModP16FastBoolW19 2 59 51 6 sieve16AffU2C3W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 2 59 3 3 51 sieve16AffU2C3W19 h0 sieve16_aff_u2_c3_s1_w19
  have h2 : checkAffRangeULModP16FastBoolW19 2 59 51 8 sieve16AffU2C3W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 2 59 6 2 51 sieve16AffU2C3W19 h1 sieve16_aff_u2_c3_s2_w19
  exact h2
private theorem sieve16_aff_u2_c3_ok_w19 :
    checkAffRangeULModP16BoolW19 2 59 51 8 sieve16AffU2C3W19 = true :=
  (checkAffRangeULModP16FastBoolW19_eq 2 59 8 51 sieve16AffU2C3W19).symm.trans sieve16_aff_u2_c3_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve16_inf_and_inv_u2_fast_w19 :
    checkAllInvModPBoolW19 59 59 = true ∧
    checkULModPNat16FastBoolW19 59 2 1 0 sieve16InfU2W19 = true := by decide
private theorem sieve16_inf_and_inv_u2_ok_w19 :
    checkAllInvModPBoolW19 59 59 = true ∧
    checkULModPNat16BoolW19 59 2 1 0 sieve16InfU2W19 = true :=
  ⟨sieve16_inf_and_inv_u2_fast_w19.1,
   (checkULModPNat16FastBoolW19_eq 59 2 1 0 sieve16InfU2W19).symm.trans sieve16_inf_and_inv_u2_fast_w19.2⟩
private theorem sieve16_aff_all_u2_w19 (t : Nat) (ht : t < 59) :
    intDet 16 (apow16UW19 2 (t : Int) 1) % (59 : Int) ≠ 0 := by
  if hc0 : t < 17 then
    exact unpack_affRangeULModP16_w19 2 59 (by decide) 17 0 sieve16AffU2C0W19 sieve16_aff_u2_c0_ok_w19 t (by omega) hc0
  else
  if hc1 : t < 34 then
    exact unpack_affRangeULModP16_w19 2 59 (by decide) 17 17 sieve16AffU2C1W19 sieve16_aff_u2_c1_ok_w19 t (by omega) hc1
  else
  if hc2 : t < 51 then
    exact unpack_affRangeULModP16_w19 2 59 (by decide) 17 34 sieve16AffU2C2W19 sieve16_aff_u2_c2_ok_w19 t (by omega) hc2
  else
    exact unpack_affRangeULModP16_w19 2 59 (by decide) 8 51 sieve16AffU2C3W19 sieve16_aff_u2_c3_ok_w19 t (by omega) (by omega)

set_option maxRecDepth 65536 in
private theorem sieve16_aff_u3_c0_s0_w19 :
    checkAffRangeULModP16FastBoolW19 3 41 0 3 (dropCertsW19 0 sieve16AffU3C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u3_c0_s1_w19 :
    checkAffRangeULModP16FastBoolW19 3 41 3 3 (dropCertsW19 3 sieve16AffU3C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u3_c0_s2_w19 :
    checkAffRangeULModP16FastBoolW19 3 41 6 3 (dropCertsW19 6 sieve16AffU3C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u3_c0_s3_w19 :
    checkAffRangeULModP16FastBoolW19 3 41 9 3 (dropCertsW19 9 sieve16AffU3C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u3_c0_s4_w19 :
    checkAffRangeULModP16FastBoolW19 3 41 12 3 (dropCertsW19 12 sieve16AffU3C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u3_c0_s5_w19 :
    checkAffRangeULModP16FastBoolW19 3 41 15 2 (dropCertsW19 15 sieve16AffU3C0W19) = true := by decide
private theorem sieve16_aff_u3_c0_fast_w19 :
    checkAffRangeULModP16FastBoolW19 3 41 0 17 sieve16AffU3C0W19 = true := by
  have h0 : checkAffRangeULModP16FastBoolW19 3 41 0 3 sieve16AffU3C0W19 = true := sieve16_aff_u3_c0_s0_w19
  have h1 : checkAffRangeULModP16FastBoolW19 3 41 0 6 sieve16AffU3C0W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 3 41 3 3 0 sieve16AffU3C0W19 h0 sieve16_aff_u3_c0_s1_w19
  have h2 : checkAffRangeULModP16FastBoolW19 3 41 0 9 sieve16AffU3C0W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 3 41 6 3 0 sieve16AffU3C0W19 h1 sieve16_aff_u3_c0_s2_w19
  have h3 : checkAffRangeULModP16FastBoolW19 3 41 0 12 sieve16AffU3C0W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 3 41 9 3 0 sieve16AffU3C0W19 h2 sieve16_aff_u3_c0_s3_w19
  have h4 : checkAffRangeULModP16FastBoolW19 3 41 0 15 sieve16AffU3C0W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 3 41 12 3 0 sieve16AffU3C0W19 h3 sieve16_aff_u3_c0_s4_w19
  have h5 : checkAffRangeULModP16FastBoolW19 3 41 0 17 sieve16AffU3C0W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 3 41 15 2 0 sieve16AffU3C0W19 h4 sieve16_aff_u3_c0_s5_w19
  exact h5
private theorem sieve16_aff_u3_c0_ok_w19 :
    checkAffRangeULModP16BoolW19 3 41 0 17 sieve16AffU3C0W19 = true :=
  (checkAffRangeULModP16FastBoolW19_eq 3 41 17 0 sieve16AffU3C0W19).symm.trans sieve16_aff_u3_c0_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u3_c1_s0_w19 :
    checkAffRangeULModP16FastBoolW19 3 41 17 3 (dropCertsW19 0 sieve16AffU3C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u3_c1_s1_w19 :
    checkAffRangeULModP16FastBoolW19 3 41 20 3 (dropCertsW19 3 sieve16AffU3C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u3_c1_s2_w19 :
    checkAffRangeULModP16FastBoolW19 3 41 23 3 (dropCertsW19 6 sieve16AffU3C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u3_c1_s3_w19 :
    checkAffRangeULModP16FastBoolW19 3 41 26 3 (dropCertsW19 9 sieve16AffU3C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u3_c1_s4_w19 :
    checkAffRangeULModP16FastBoolW19 3 41 29 3 (dropCertsW19 12 sieve16AffU3C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u3_c1_s5_w19 :
    checkAffRangeULModP16FastBoolW19 3 41 32 2 (dropCertsW19 15 sieve16AffU3C1W19) = true := by decide
private theorem sieve16_aff_u3_c1_fast_w19 :
    checkAffRangeULModP16FastBoolW19 3 41 17 17 sieve16AffU3C1W19 = true := by
  have h0 : checkAffRangeULModP16FastBoolW19 3 41 17 3 sieve16AffU3C1W19 = true := sieve16_aff_u3_c1_s0_w19
  have h1 : checkAffRangeULModP16FastBoolW19 3 41 17 6 sieve16AffU3C1W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 3 41 3 3 17 sieve16AffU3C1W19 h0 sieve16_aff_u3_c1_s1_w19
  have h2 : checkAffRangeULModP16FastBoolW19 3 41 17 9 sieve16AffU3C1W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 3 41 6 3 17 sieve16AffU3C1W19 h1 sieve16_aff_u3_c1_s2_w19
  have h3 : checkAffRangeULModP16FastBoolW19 3 41 17 12 sieve16AffU3C1W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 3 41 9 3 17 sieve16AffU3C1W19 h2 sieve16_aff_u3_c1_s3_w19
  have h4 : checkAffRangeULModP16FastBoolW19 3 41 17 15 sieve16AffU3C1W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 3 41 12 3 17 sieve16AffU3C1W19 h3 sieve16_aff_u3_c1_s4_w19
  have h5 : checkAffRangeULModP16FastBoolW19 3 41 17 17 sieve16AffU3C1W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 3 41 15 2 17 sieve16AffU3C1W19 h4 sieve16_aff_u3_c1_s5_w19
  exact h5
private theorem sieve16_aff_u3_c1_ok_w19 :
    checkAffRangeULModP16BoolW19 3 41 17 17 sieve16AffU3C1W19 = true :=
  (checkAffRangeULModP16FastBoolW19_eq 3 41 17 17 sieve16AffU3C1W19).symm.trans sieve16_aff_u3_c1_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u3_c2_s0_w19 :
    checkAffRangeULModP16FastBoolW19 3 41 34 3 (dropCertsW19 0 sieve16AffU3C2W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u3_c2_s1_w19 :
    checkAffRangeULModP16FastBoolW19 3 41 37 3 (dropCertsW19 3 sieve16AffU3C2W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u3_c2_s2_w19 :
    checkAffRangeULModP16FastBoolW19 3 41 40 1 (dropCertsW19 6 sieve16AffU3C2W19) = true := by decide
private theorem sieve16_aff_u3_c2_fast_w19 :
    checkAffRangeULModP16FastBoolW19 3 41 34 7 sieve16AffU3C2W19 = true := by
  have h0 : checkAffRangeULModP16FastBoolW19 3 41 34 3 sieve16AffU3C2W19 = true := sieve16_aff_u3_c2_s0_w19
  have h1 : checkAffRangeULModP16FastBoolW19 3 41 34 6 sieve16AffU3C2W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 3 41 3 3 34 sieve16AffU3C2W19 h0 sieve16_aff_u3_c2_s1_w19
  have h2 : checkAffRangeULModP16FastBoolW19 3 41 34 7 sieve16AffU3C2W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 3 41 6 1 34 sieve16AffU3C2W19 h1 sieve16_aff_u3_c2_s2_w19
  exact h2
private theorem sieve16_aff_u3_c2_ok_w19 :
    checkAffRangeULModP16BoolW19 3 41 34 7 sieve16AffU3C2W19 = true :=
  (checkAffRangeULModP16FastBoolW19_eq 3 41 7 34 sieve16AffU3C2W19).symm.trans sieve16_aff_u3_c2_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve16_inf_and_inv_u3_fast_w19 :
    checkAllInvModPBoolW19 41 41 = true ∧
    checkULModPNat16FastBoolW19 41 3 1 0 sieve16InfU3W19 = true := by decide
private theorem sieve16_inf_and_inv_u3_ok_w19 :
    checkAllInvModPBoolW19 41 41 = true ∧
    checkULModPNat16BoolW19 41 3 1 0 sieve16InfU3W19 = true :=
  ⟨sieve16_inf_and_inv_u3_fast_w19.1,
   (checkULModPNat16FastBoolW19_eq 41 3 1 0 sieve16InfU3W19).symm.trans sieve16_inf_and_inv_u3_fast_w19.2⟩
private theorem sieve16_aff_all_u3_w19 (t : Nat) (ht : t < 41) :
    intDet 16 (apow16UW19 3 (t : Int) 1) % (41 : Int) ≠ 0 := by
  if hc0 : t < 17 then
    exact unpack_affRangeULModP16_w19 3 41 (by decide) 17 0 sieve16AffU3C0W19 sieve16_aff_u3_c0_ok_w19 t (by omega) hc0
  else
  if hc1 : t < 34 then
    exact unpack_affRangeULModP16_w19 3 41 (by decide) 17 17 sieve16AffU3C1W19 sieve16_aff_u3_c1_ok_w19 t (by omega) hc1
  else
    exact unpack_affRangeULModP16_w19 3 41 (by decide) 7 34 sieve16AffU3C2W19 sieve16_aff_u3_c2_ok_w19 t (by omega) (by omega)

set_option maxRecDepth 65536 in
private theorem sieve16_aff_u4_c0_s0_w19 :
    checkAffRangeULModP16FastBoolW19 4 67 0 3 (dropCertsW19 0 sieve16AffU4C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u4_c0_s1_w19 :
    checkAffRangeULModP16FastBoolW19 4 67 3 3 (dropCertsW19 3 sieve16AffU4C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u4_c0_s2_w19 :
    checkAffRangeULModP16FastBoolW19 4 67 6 3 (dropCertsW19 6 sieve16AffU4C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u4_c0_s3_w19 :
    checkAffRangeULModP16FastBoolW19 4 67 9 3 (dropCertsW19 9 sieve16AffU4C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u4_c0_s4_w19 :
    checkAffRangeULModP16FastBoolW19 4 67 12 3 (dropCertsW19 12 sieve16AffU4C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u4_c0_s5_w19 :
    checkAffRangeULModP16FastBoolW19 4 67 15 2 (dropCertsW19 15 sieve16AffU4C0W19) = true := by decide
private theorem sieve16_aff_u4_c0_fast_w19 :
    checkAffRangeULModP16FastBoolW19 4 67 0 17 sieve16AffU4C0W19 = true := by
  have h0 : checkAffRangeULModP16FastBoolW19 4 67 0 3 sieve16AffU4C0W19 = true := sieve16_aff_u4_c0_s0_w19
  have h1 : checkAffRangeULModP16FastBoolW19 4 67 0 6 sieve16AffU4C0W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 4 67 3 3 0 sieve16AffU4C0W19 h0 sieve16_aff_u4_c0_s1_w19
  have h2 : checkAffRangeULModP16FastBoolW19 4 67 0 9 sieve16AffU4C0W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 4 67 6 3 0 sieve16AffU4C0W19 h1 sieve16_aff_u4_c0_s2_w19
  have h3 : checkAffRangeULModP16FastBoolW19 4 67 0 12 sieve16AffU4C0W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 4 67 9 3 0 sieve16AffU4C0W19 h2 sieve16_aff_u4_c0_s3_w19
  have h4 : checkAffRangeULModP16FastBoolW19 4 67 0 15 sieve16AffU4C0W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 4 67 12 3 0 sieve16AffU4C0W19 h3 sieve16_aff_u4_c0_s4_w19
  have h5 : checkAffRangeULModP16FastBoolW19 4 67 0 17 sieve16AffU4C0W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 4 67 15 2 0 sieve16AffU4C0W19 h4 sieve16_aff_u4_c0_s5_w19
  exact h5
private theorem sieve16_aff_u4_c0_ok_w19 :
    checkAffRangeULModP16BoolW19 4 67 0 17 sieve16AffU4C0W19 = true :=
  (checkAffRangeULModP16FastBoolW19_eq 4 67 17 0 sieve16AffU4C0W19).symm.trans sieve16_aff_u4_c0_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u4_c1_s0_w19 :
    checkAffRangeULModP16FastBoolW19 4 67 17 3 (dropCertsW19 0 sieve16AffU4C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u4_c1_s1_w19 :
    checkAffRangeULModP16FastBoolW19 4 67 20 3 (dropCertsW19 3 sieve16AffU4C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u4_c1_s2_w19 :
    checkAffRangeULModP16FastBoolW19 4 67 23 3 (dropCertsW19 6 sieve16AffU4C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u4_c1_s3_w19 :
    checkAffRangeULModP16FastBoolW19 4 67 26 3 (dropCertsW19 9 sieve16AffU4C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u4_c1_s4_w19 :
    checkAffRangeULModP16FastBoolW19 4 67 29 3 (dropCertsW19 12 sieve16AffU4C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u4_c1_s5_w19 :
    checkAffRangeULModP16FastBoolW19 4 67 32 2 (dropCertsW19 15 sieve16AffU4C1W19) = true := by decide
private theorem sieve16_aff_u4_c1_fast_w19 :
    checkAffRangeULModP16FastBoolW19 4 67 17 17 sieve16AffU4C1W19 = true := by
  have h0 : checkAffRangeULModP16FastBoolW19 4 67 17 3 sieve16AffU4C1W19 = true := sieve16_aff_u4_c1_s0_w19
  have h1 : checkAffRangeULModP16FastBoolW19 4 67 17 6 sieve16AffU4C1W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 4 67 3 3 17 sieve16AffU4C1W19 h0 sieve16_aff_u4_c1_s1_w19
  have h2 : checkAffRangeULModP16FastBoolW19 4 67 17 9 sieve16AffU4C1W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 4 67 6 3 17 sieve16AffU4C1W19 h1 sieve16_aff_u4_c1_s2_w19
  have h3 : checkAffRangeULModP16FastBoolW19 4 67 17 12 sieve16AffU4C1W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 4 67 9 3 17 sieve16AffU4C1W19 h2 sieve16_aff_u4_c1_s3_w19
  have h4 : checkAffRangeULModP16FastBoolW19 4 67 17 15 sieve16AffU4C1W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 4 67 12 3 17 sieve16AffU4C1W19 h3 sieve16_aff_u4_c1_s4_w19
  have h5 : checkAffRangeULModP16FastBoolW19 4 67 17 17 sieve16AffU4C1W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 4 67 15 2 17 sieve16AffU4C1W19 h4 sieve16_aff_u4_c1_s5_w19
  exact h5
private theorem sieve16_aff_u4_c1_ok_w19 :
    checkAffRangeULModP16BoolW19 4 67 17 17 sieve16AffU4C1W19 = true :=
  (checkAffRangeULModP16FastBoolW19_eq 4 67 17 17 sieve16AffU4C1W19).symm.trans sieve16_aff_u4_c1_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u4_c2_s0_w19 :
    checkAffRangeULModP16FastBoolW19 4 67 34 3 (dropCertsW19 0 sieve16AffU4C2W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u4_c2_s1_w19 :
    checkAffRangeULModP16FastBoolW19 4 67 37 3 (dropCertsW19 3 sieve16AffU4C2W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u4_c2_s2_w19 :
    checkAffRangeULModP16FastBoolW19 4 67 40 3 (dropCertsW19 6 sieve16AffU4C2W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u4_c2_s3_w19 :
    checkAffRangeULModP16FastBoolW19 4 67 43 3 (dropCertsW19 9 sieve16AffU4C2W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u4_c2_s4_w19 :
    checkAffRangeULModP16FastBoolW19 4 67 46 3 (dropCertsW19 12 sieve16AffU4C2W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u4_c2_s5_w19 :
    checkAffRangeULModP16FastBoolW19 4 67 49 2 (dropCertsW19 15 sieve16AffU4C2W19) = true := by decide
private theorem sieve16_aff_u4_c2_fast_w19 :
    checkAffRangeULModP16FastBoolW19 4 67 34 17 sieve16AffU4C2W19 = true := by
  have h0 : checkAffRangeULModP16FastBoolW19 4 67 34 3 sieve16AffU4C2W19 = true := sieve16_aff_u4_c2_s0_w19
  have h1 : checkAffRangeULModP16FastBoolW19 4 67 34 6 sieve16AffU4C2W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 4 67 3 3 34 sieve16AffU4C2W19 h0 sieve16_aff_u4_c2_s1_w19
  have h2 : checkAffRangeULModP16FastBoolW19 4 67 34 9 sieve16AffU4C2W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 4 67 6 3 34 sieve16AffU4C2W19 h1 sieve16_aff_u4_c2_s2_w19
  have h3 : checkAffRangeULModP16FastBoolW19 4 67 34 12 sieve16AffU4C2W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 4 67 9 3 34 sieve16AffU4C2W19 h2 sieve16_aff_u4_c2_s3_w19
  have h4 : checkAffRangeULModP16FastBoolW19 4 67 34 15 sieve16AffU4C2W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 4 67 12 3 34 sieve16AffU4C2W19 h3 sieve16_aff_u4_c2_s4_w19
  have h5 : checkAffRangeULModP16FastBoolW19 4 67 34 17 sieve16AffU4C2W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 4 67 15 2 34 sieve16AffU4C2W19 h4 sieve16_aff_u4_c2_s5_w19
  exact h5
private theorem sieve16_aff_u4_c2_ok_w19 :
    checkAffRangeULModP16BoolW19 4 67 34 17 sieve16AffU4C2W19 = true :=
  (checkAffRangeULModP16FastBoolW19_eq 4 67 17 34 sieve16AffU4C2W19).symm.trans sieve16_aff_u4_c2_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u4_c3_s0_w19 :
    checkAffRangeULModP16FastBoolW19 4 67 51 3 (dropCertsW19 0 sieve16AffU4C3W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u4_c3_s1_w19 :
    checkAffRangeULModP16FastBoolW19 4 67 54 3 (dropCertsW19 3 sieve16AffU4C3W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u4_c3_s2_w19 :
    checkAffRangeULModP16FastBoolW19 4 67 57 3 (dropCertsW19 6 sieve16AffU4C3W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u4_c3_s3_w19 :
    checkAffRangeULModP16FastBoolW19 4 67 60 3 (dropCertsW19 9 sieve16AffU4C3W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u4_c3_s4_w19 :
    checkAffRangeULModP16FastBoolW19 4 67 63 3 (dropCertsW19 12 sieve16AffU4C3W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u4_c3_s5_w19 :
    checkAffRangeULModP16FastBoolW19 4 67 66 1 (dropCertsW19 15 sieve16AffU4C3W19) = true := by decide
private theorem sieve16_aff_u4_c3_fast_w19 :
    checkAffRangeULModP16FastBoolW19 4 67 51 16 sieve16AffU4C3W19 = true := by
  have h0 : checkAffRangeULModP16FastBoolW19 4 67 51 3 sieve16AffU4C3W19 = true := sieve16_aff_u4_c3_s0_w19
  have h1 : checkAffRangeULModP16FastBoolW19 4 67 51 6 sieve16AffU4C3W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 4 67 3 3 51 sieve16AffU4C3W19 h0 sieve16_aff_u4_c3_s1_w19
  have h2 : checkAffRangeULModP16FastBoolW19 4 67 51 9 sieve16AffU4C3W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 4 67 6 3 51 sieve16AffU4C3W19 h1 sieve16_aff_u4_c3_s2_w19
  have h3 : checkAffRangeULModP16FastBoolW19 4 67 51 12 sieve16AffU4C3W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 4 67 9 3 51 sieve16AffU4C3W19 h2 sieve16_aff_u4_c3_s3_w19
  have h4 : checkAffRangeULModP16FastBoolW19 4 67 51 15 sieve16AffU4C3W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 4 67 12 3 51 sieve16AffU4C3W19 h3 sieve16_aff_u4_c3_s4_w19
  have h5 : checkAffRangeULModP16FastBoolW19 4 67 51 16 sieve16AffU4C3W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 4 67 15 1 51 sieve16AffU4C3W19 h4 sieve16_aff_u4_c3_s5_w19
  exact h5
private theorem sieve16_aff_u4_c3_ok_w19 :
    checkAffRangeULModP16BoolW19 4 67 51 16 sieve16AffU4C3W19 = true :=
  (checkAffRangeULModP16FastBoolW19_eq 4 67 16 51 sieve16AffU4C3W19).symm.trans sieve16_aff_u4_c3_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve16_inf_and_inv_u4_fast_w19 :
    checkAllInvModPBoolW19 67 67 = true ∧
    checkULModPNat16FastBoolW19 67 4 1 0 sieve16InfU4W19 = true := by decide
private theorem sieve16_inf_and_inv_u4_ok_w19 :
    checkAllInvModPBoolW19 67 67 = true ∧
    checkULModPNat16BoolW19 67 4 1 0 sieve16InfU4W19 = true :=
  ⟨sieve16_inf_and_inv_u4_fast_w19.1,
   (checkULModPNat16FastBoolW19_eq 67 4 1 0 sieve16InfU4W19).symm.trans sieve16_inf_and_inv_u4_fast_w19.2⟩
private theorem sieve16_aff_all_u4_w19 (t : Nat) (ht : t < 67) :
    intDet 16 (apow16UW19 4 (t : Int) 1) % (67 : Int) ≠ 0 := by
  if hc0 : t < 17 then
    exact unpack_affRangeULModP16_w19 4 67 (by decide) 17 0 sieve16AffU4C0W19 sieve16_aff_u4_c0_ok_w19 t (by omega) hc0
  else
  if hc1 : t < 34 then
    exact unpack_affRangeULModP16_w19 4 67 (by decide) 17 17 sieve16AffU4C1W19 sieve16_aff_u4_c1_ok_w19 t (by omega) hc1
  else
  if hc2 : t < 51 then
    exact unpack_affRangeULModP16_w19 4 67 (by decide) 17 34 sieve16AffU4C2W19 sieve16_aff_u4_c2_ok_w19 t (by omega) hc2
  else
    exact unpack_affRangeULModP16_w19 4 67 (by decide) 16 51 sieve16AffU4C3W19 sieve16_aff_u4_c3_ok_w19 t (by omega) (by omega)

set_option maxRecDepth 65536 in
private theorem sieve16_aff_u5_c0_s0_w19 :
    checkAffRangeULModP16FastBoolW19 5 37 0 3 (dropCertsW19 0 sieve16AffU5C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u5_c0_s1_w19 :
    checkAffRangeULModP16FastBoolW19 5 37 3 3 (dropCertsW19 3 sieve16AffU5C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u5_c0_s2_w19 :
    checkAffRangeULModP16FastBoolW19 5 37 6 3 (dropCertsW19 6 sieve16AffU5C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u5_c0_s3_w19 :
    checkAffRangeULModP16FastBoolW19 5 37 9 3 (dropCertsW19 9 sieve16AffU5C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u5_c0_s4_w19 :
    checkAffRangeULModP16FastBoolW19 5 37 12 3 (dropCertsW19 12 sieve16AffU5C0W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u5_c0_s5_w19 :
    checkAffRangeULModP16FastBoolW19 5 37 15 2 (dropCertsW19 15 sieve16AffU5C0W19) = true := by decide
private theorem sieve16_aff_u5_c0_fast_w19 :
    checkAffRangeULModP16FastBoolW19 5 37 0 17 sieve16AffU5C0W19 = true := by
  have h0 : checkAffRangeULModP16FastBoolW19 5 37 0 3 sieve16AffU5C0W19 = true := sieve16_aff_u5_c0_s0_w19
  have h1 : checkAffRangeULModP16FastBoolW19 5 37 0 6 sieve16AffU5C0W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 5 37 3 3 0 sieve16AffU5C0W19 h0 sieve16_aff_u5_c0_s1_w19
  have h2 : checkAffRangeULModP16FastBoolW19 5 37 0 9 sieve16AffU5C0W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 5 37 6 3 0 sieve16AffU5C0W19 h1 sieve16_aff_u5_c0_s2_w19
  have h3 : checkAffRangeULModP16FastBoolW19 5 37 0 12 sieve16AffU5C0W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 5 37 9 3 0 sieve16AffU5C0W19 h2 sieve16_aff_u5_c0_s3_w19
  have h4 : checkAffRangeULModP16FastBoolW19 5 37 0 15 sieve16AffU5C0W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 5 37 12 3 0 sieve16AffU5C0W19 h3 sieve16_aff_u5_c0_s4_w19
  have h5 : checkAffRangeULModP16FastBoolW19 5 37 0 17 sieve16AffU5C0W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 5 37 15 2 0 sieve16AffU5C0W19 h4 sieve16_aff_u5_c0_s5_w19
  exact h5
private theorem sieve16_aff_u5_c0_ok_w19 :
    checkAffRangeULModP16BoolW19 5 37 0 17 sieve16AffU5C0W19 = true :=
  (checkAffRangeULModP16FastBoolW19_eq 5 37 17 0 sieve16AffU5C0W19).symm.trans sieve16_aff_u5_c0_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u5_c1_s0_w19 :
    checkAffRangeULModP16FastBoolW19 5 37 17 3 (dropCertsW19 0 sieve16AffU5C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u5_c1_s1_w19 :
    checkAffRangeULModP16FastBoolW19 5 37 20 3 (dropCertsW19 3 sieve16AffU5C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u5_c1_s2_w19 :
    checkAffRangeULModP16FastBoolW19 5 37 23 3 (dropCertsW19 6 sieve16AffU5C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u5_c1_s3_w19 :
    checkAffRangeULModP16FastBoolW19 5 37 26 3 (dropCertsW19 9 sieve16AffU5C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u5_c1_s4_w19 :
    checkAffRangeULModP16FastBoolW19 5 37 29 3 (dropCertsW19 12 sieve16AffU5C1W19) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u5_c1_s5_w19 :
    checkAffRangeULModP16FastBoolW19 5 37 32 2 (dropCertsW19 15 sieve16AffU5C1W19) = true := by decide
private theorem sieve16_aff_u5_c1_fast_w19 :
    checkAffRangeULModP16FastBoolW19 5 37 17 17 sieve16AffU5C1W19 = true := by
  have h0 : checkAffRangeULModP16FastBoolW19 5 37 17 3 sieve16AffU5C1W19 = true := sieve16_aff_u5_c1_s0_w19
  have h1 : checkAffRangeULModP16FastBoolW19 5 37 17 6 sieve16AffU5C1W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 5 37 3 3 17 sieve16AffU5C1W19 h0 sieve16_aff_u5_c1_s1_w19
  have h2 : checkAffRangeULModP16FastBoolW19 5 37 17 9 sieve16AffU5C1W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 5 37 6 3 17 sieve16AffU5C1W19 h1 sieve16_aff_u5_c1_s2_w19
  have h3 : checkAffRangeULModP16FastBoolW19 5 37 17 12 sieve16AffU5C1W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 5 37 9 3 17 sieve16AffU5C1W19 h2 sieve16_aff_u5_c1_s3_w19
  have h4 : checkAffRangeULModP16FastBoolW19 5 37 17 15 sieve16AffU5C1W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 5 37 12 3 17 sieve16AffU5C1W19 h3 sieve16_aff_u5_c1_s4_w19
  have h5 : checkAffRangeULModP16FastBoolW19 5 37 17 17 sieve16AffU5C1W19 = true :=
    checkAffRangeULModP16FastBoolW19_glue 5 37 15 2 17 sieve16AffU5C1W19 h4 sieve16_aff_u5_c1_s5_w19
  exact h5
private theorem sieve16_aff_u5_c1_ok_w19 :
    checkAffRangeULModP16BoolW19 5 37 17 17 sieve16AffU5C1W19 = true :=
  (checkAffRangeULModP16FastBoolW19_eq 5 37 17 17 sieve16AffU5C1W19).symm.trans sieve16_aff_u5_c1_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve16_aff_u5_c2_s0_w19 :
    checkAffRangeULModP16FastBoolW19 5 37 34 3 (dropCertsW19 0 sieve16AffU5C2W19) = true := by decide
private theorem sieve16_aff_u5_c2_fast_w19 :
    checkAffRangeULModP16FastBoolW19 5 37 34 3 sieve16AffU5C2W19 = true := by
  have h0 : checkAffRangeULModP16FastBoolW19 5 37 34 3 sieve16AffU5C2W19 = true := sieve16_aff_u5_c2_s0_w19
  exact h0
private theorem sieve16_aff_u5_c2_ok_w19 :
    checkAffRangeULModP16BoolW19 5 37 34 3 sieve16AffU5C2W19 = true :=
  (checkAffRangeULModP16FastBoolW19_eq 5 37 3 34 sieve16AffU5C2W19).symm.trans sieve16_aff_u5_c2_fast_w19
set_option maxRecDepth 65536 in
private theorem sieve16_inf_and_inv_u5_fast_w19 :
    checkAllInvModPBoolW19 37 37 = true ∧
    checkULModPNat16FastBoolW19 37 5 1 0 sieve16InfU5W19 = true := by decide
private theorem sieve16_inf_and_inv_u5_ok_w19 :
    checkAllInvModPBoolW19 37 37 = true ∧
    checkULModPNat16BoolW19 37 5 1 0 sieve16InfU5W19 = true :=
  ⟨sieve16_inf_and_inv_u5_fast_w19.1,
   (checkULModPNat16FastBoolW19_eq 37 5 1 0 sieve16InfU5W19).symm.trans sieve16_inf_and_inv_u5_fast_w19.2⟩
private theorem sieve16_aff_all_u5_w19 (t : Nat) (ht : t < 37) :
    intDet 16 (apow16UW19 5 (t : Int) 1) % (37 : Int) ≠ 0 := by
  if hc0 : t < 17 then
    exact unpack_affRangeULModP16_w19 5 37 (by decide) 17 0 sieve16AffU5C0W19 sieve16_aff_u5_c0_ok_w19 t (by omega) hc0
  else
  if hc1 : t < 34 then
    exact unpack_affRangeULModP16_w19 5 37 (by decide) 17 17 sieve16AffU5C1W19 sieve16_aff_u5_c1_ok_w19 t (by omega) hc1
  else
    exact unpack_affRangeULModP16_w19 5 37 (by decide) 3 34 sieve16AffU5C2W19 sieve16_aff_u5_c2_ok_w19 t (by omega) (by omega)


/--
  Theorem W19.2b (`laurent_16x16_t4u4_cone_flip_confluent_and_u1_to_5_nonvanishing`,
  `zero custom axioms`):
  Symmetric Rank-4 Order-4 `16 × 16` `(T = 4, U = 4)` Two-Base Schneider–Laurent Determinants:
  1. Restoring square symmetry `T = U = 4` does NOT recover Wave 14's `9 × 9` `(T = U = 3)`
     Collatz-cone strict positivity: inside `3^W < 2^K ∧ 3 * K ≤ 5 * W`, `det_16(3, 5, 1) < 0`
     flips sign against `det_16(4, 7, 1) > 0`;
  2. Universal `∀ W, K, u` (`u ≥ 1`) rank-4 `16 × 16` zero-gap confluent divisibility
     `confluentFactorAllU 4 4 u ∣ det_16(M_0)` AND `(2^K - 3^W)` Liouville congruence & lower bound;
  3. Global ZERO-FREE non-vanishing across 100% of `W, K ≥ 1` for ALL `u ∈ {1, 2, 3, 4, 5}`
     via projective `P^1(F_p)` sieves (`p = 31, 59, 41, 67, 37`), including complete elimination
     of `12 × 12`'s `u = 1, K = 4 * W` resonant zero ray (`det_16(W, 4 * W, 1) = W^24 * det_16(1, 4, 1) < 0`)
     (`Branch P3.4`, witness `LAURENT_16X16_T4U4_U1_CONE_SIGN_FLIP_3_5_VS_4_7`, `W19_H2`).
-/
theorem laurent_16x16_t4u4_cone_flip_confluent_and_u1_to_5_nonvanishing :
    (3 ^ 3 < 2 ^ 5 ∧ 3 * 5 ≤ 5 * 3 ∧
     intDet 16 (laurentTwoBaseT4U4Mat16 3 5 1) = -346869345187079025627401176785813504 ∧
     intDet 16 (laurentTwoBaseT4U4Mat16 3 5 1) < 0 ∧
     3 ^ 4 < 2 ^ 7 ∧ 2 ^ 7 < 2 * 3 ^ 4 ∧
     intDet 16 (laurentTwoBaseT4U4Mat16 4 7 1) = 223551144063582960394327584357593948160000 ∧
     intDet 16 (laurentTwoBaseT4U4Mat16 4 7 1) > 0 ∧
     intDet 16 (laurentTwoBaseT4U4Mat16 1 4 1) = -5480111512833949589330460672000000000000000 ∧
     intDet 16 (laurentTwoBaseT4U4Mat16 1 4 1) < 0) ∧
    (∀ (W K u : Nat), u ≥ 1 ->
      let M0 : Fin 16 -> Fin 16 -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (laurentRowsTwoBase16 i).1 (laurentRowsTwoBase16 i).2
          (laurentColsT4U4_16 u j).1 (laurentColsT4U4_16 u j).2 : Int)
      Int.ofNat (confluentFactorAllU 4 4 u) ∣ intDet 16 M0 ∧
      (3 ^ W < 2 ^ K ->
        (((2 ^ K - 3 ^ W : Nat) : Int) ∣
          (intDet 16 M0 - intDet 16 (laurentTwoBaseT4U4Mat16 W K (W * u)))) ∧
        (intDet 16 M0 ≠ intDet 16 (laurentTwoBaseT4U4Mat16 W K (W * u)) ->
          2 ^ K - 3 ^ W ≤ (intDet 16 M0).natAbs + (intDet 16 (laurentTwoBaseT4U4Mat16 W K (W * u))).natAbs))) ∧
    (∀ (u W K : Nat), 1 ≤ u -> u ≤ 5 -> W ≥ 1 -> K ≥ 1 ->
      intDet 16 (laurentTwoBaseT4U4Mat16 W K u) ≠ 0) ∧
    (∀ W : Nat, W ≥ 1 -> intDet 16 (laurentTwoBaseT4U4Mat16 W (4 * W) 1) < 0) := by
  have hd351 : intDet 16 (laurentTwoBaseT4U4Mat16 3 5 1) = -346869345187079025627401176785813504 := by
    rw [← fastMat16T4U4FnW19_eq 3 5 1]
    exact checkULDetBoolW19_sound 16 _ _ _ t4u4_351_cert_w19
  have hd471 : intDet 16 (laurentTwoBaseT4U4Mat16 4 7 1) = 223551144063582960394327584357593948160000 := by
    rw [← fastMat16T4U4FnW19_eq 4 7 1]
    exact checkULDetBoolW19_sound 16 _ _ _ t4u4_471_cert_w19
  have hd141 : intDet 16 (laurentTwoBaseT4U4Mat16 1 4 1) = -5480111512833949589330460672000000000000000 := by
    rw [← fastMat16T4U4FnW19_eq 1 4 1]
    exact checkULDetBoolW19_sound 16 _ _ _ t4u4_141_cert_w19
  have hu15 : ∀ (u W K : Nat), 1 ≤ u -> u ≤ 5 -> W ≥ 1 -> K ≥ 1 ->
      intDet 16 (laurentTwoBaseT4U4Mat16 W K u) ≠ 0 := by
    intro u W K hlo hhi hW hK
    rcases (by omega : u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 4 ∨ u = 5) with rfl | rfl | rfl | rfl | rfl
    · exact det16_t4u4_nonzero_of_proj_sieve_w19 1 31 (by decide)
        sieve16_inf_and_inv_u1_ok_w19.1
        (checkULModPNat16BoolW19_sound 31 1 1 0 (by decide) sieve16InfU1W19 sieve16_inf_and_inv_u1_ok_w19.2)
        sieve16_aff_all_u1_w19 W K hW hK
    · exact det16_t4u4_nonzero_of_proj_sieve_w19 2 59 (by decide)
        sieve16_inf_and_inv_u2_ok_w19.1
        (checkULModPNat16BoolW19_sound 59 2 1 0 (by decide) sieve16InfU2W19 sieve16_inf_and_inv_u2_ok_w19.2)
        sieve16_aff_all_u2_w19 W K hW hK
    · exact det16_t4u4_nonzero_of_proj_sieve_w19 3 41 (by decide)
        sieve16_inf_and_inv_u3_ok_w19.1
        (checkULModPNat16BoolW19_sound 41 3 1 0 (by decide) sieve16InfU3W19 sieve16_inf_and_inv_u3_ok_w19.2)
        sieve16_aff_all_u3_w19 W K hW hK
    · exact det16_t4u4_nonzero_of_proj_sieve_w19 4 67 (by decide)
        sieve16_inf_and_inv_u4_ok_w19.1
        (checkULModPNat16BoolW19_sound 67 4 1 0 (by decide) sieve16InfU4W19 sieve16_inf_and_inv_u4_ok_w19.2)
        sieve16_aff_all_u4_w19 W K hW hK
    · exact det16_t4u4_nonzero_of_proj_sieve_w19 5 37 (by decide)
        sieve16_inf_and_inv_u5_ok_w19.1
        (checkULModPNat16BoolW19_sound 37 5 1 0 (by decide) sieve16InfU5W19 sieve16_inf_and_inv_u5_ok_w19.2)
        sieve16_aff_all_u5_w19 W K hW hK
  refine ⟨⟨by decide, by decide, hd351, by rw [hd351]; decide,
           by decide, by decide, hd471, by rw [hd471]; decide,
           hd141, by rw [hd141]; decide⟩, ?_, hu15, ?_⟩
  · intro W K u hu
    dsimp only
    have hconf := (laurent_all_blocks_arbitrary_U_confluent_divisibility_and_majorant.1
      4 W K 4 u laurentRowsTwoBase16 (by decide) (by decide) hu).2
    refine ⟨hconf, fun hgt => ?_⟩
    have hliouv := laurent_wdilated_zero_gap_entry_and_det_congruence.2
      W K 16 laurentRowsTwoBase16 (laurentColsT4U4_16 u) hgt
    dsimp only at hliouv
    have hmw_eq : (fun i j : Fin 16 =>
        (laurentInterpEntry W K (laurentRowsTwoBase16 i).1 (laurentRowsTwoBase16 i).2
          (laurentColsT4U4_16 u j).1 (W * (laurentColsT4U4_16 u j).2) : Int)) =
        laurentTwoBaseT4U4Mat16 W K (W * u) := by
      funext i j
      unfold laurentTwoBaseT4U4Mat16 laurentInterpMat laurentColsT4U4_16 laurentColsAllU
      dsimp only
      rw [Nat.mul_left_comm W (j.val / 4) u]
    rwa [hmw_eq] at hliouv
  · intro W hW
    have hrew : laurentTwoBaseT4U4Mat16 W (4 * W) 1 =
        laurentTwoBaseT4U4Mat16 (W * 1) (W * 4) 1 := by
      rw [Nat.mul_one, Nat.mul_comm 4 W]
    rw [hrew, det16_t4u4_homog24_w19 1 W 1 4, hd141, intPowNat_natCast_w19 W 24]
    have hp24 : ((W ^ 24 : Nat) : Int) > 0 := by
      have := nat_pow_pos_of_pos W hW 24; omega
    exact Int.mul_neg_of_pos_of_neg hp24 (by decide)

private theorem sub_mod_of_le_s4_w19 (M R U : Nat) (hM : M ≥ 1) (hUR : U ≤ R) :
    (R - U) % M = (R % M + M - U % M) % M := by
  have hR := (Nat.div_add_mod R M).symm
  have hU := (Nat.div_add_mod U M).symm
  have hrm : R % M < M := Nat.mod_lt R hM
  have hum : U % M < M := Nat.mod_lt U hM
  if hcmp : U % M ≤ R % M then
    have hsub : R - U = M * (R / M - U / M) + (R % M - U % M) := by
      have hq : U / M ≤ R / M := by
        if hq : U / M ≤ R / M then exact hq
        else exfalso; have hm := Nat.mul_le_mul_left M (by omega : R / M + 1 ≤ U / M); rw [Nat.mul_add, Nat.mul_one] at hm; omega
      have hq_mul : M * (U / M) ≤ M * (R / M) := Nat.mul_le_mul_left M hq
      rw [Nat.mul_sub_left_distrib]
      generalize M * (R / M) = QR, M * (U / M) = QU at hR hU hq_mul ⊢; omega
    have hadd : R % M + M - U % M = M * 1 + (R % M - U % M) := by omega
    rw [hsub, hadd, Nat.add_comm (M * _), Nat.add_mul_mod_self_left, Nat.add_comm (M * 1), Nat.add_mul_mod_self_left]
  else
    have hq : U / M + 1 ≤ R / M := by
      if hq : U / M + 1 ≤ R / M then exact hq
      else exfalso; have hm := Nat.mul_le_mul_left M (by omega : R / M ≤ U / M); omega
    have hsub : R - U = M * (R / M - (U / M + 1)) + (R % M + M - U % M) := by
      have hq_mul : M * (U / M) + M ≤ M * (R / M) := by simpa [Nat.mul_add, Nat.mul_one] using Nat.mul_le_mul_left M hq
      rw [Nat.mul_sub_left_distrib, Nat.mul_add, Nat.mul_one]
      generalize M * (R / M) = QR, M * (U / M) = QU at hR hU hq_mul ⊢; omega
    rw [hsub, Nat.add_comm (M * _), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : R % M + M - U % M < M)]

-- ============================================================================
-- SECTION 4: Front A Part 2 & Front B Part 3 (`Branches P4.3 & P3.4`) —
--            Unconditional `1..30`-Cycle Freedom Across ALL `DP2` Words,
--            Symbolic All-`m ≥ 3` Multi-Spike Heterogeneous `(m - 1)`-Pivot
--            Closed-Form Identity + `henselOddInvModPow2` Brox & `DP2`
--            Eliminations, & `m = 8` Balanced / Convergent `(41, 65)` Squeezes
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Section 4A: Unconditional `1..30`-Cycle Freedom Across ALL `DP2` Words
--             (`N_cut = 389`, `blockWeightSum ≥ 31`, & `M1` `29`-Cycle
--             Separation `M1_DP2_29CYCLE_68629840493971_OVER_1738366812781`)
-- ----------------------------------------------------------------------------

private def syrStepW19 (n : Nat) : Nat := core2 (3 * n + 1)

private def syrIterW19 : Nat -> Nat -> Nat
  | 0, n => n
  | k + 1, n => syrIterW19 k (syrStepW19 n)

private theorem syrIterW19_add :
    ∀ (a b n : Nat), syrIterW19 (a + b) n = syrIterW19 b (syrIterW19 a n)
  | 0, _, _ => by rw [Nat.zero_add]; rfl
  | a + 1, b, n => by rw [Nat.succ_add]; exact syrIterW19_add a b (syrStepW19 n)

set_option maxRecDepth 65536 in
private theorem no_small_odd_syr_cycles_26_to_30_w19 :
    ∀ (r : Fin 31) (k : Fin 193),
      26 ≤ r.val -> syrIterW19 r.val (2 * k.val + 3) ≠ 2 * k.val + 3 := by decide

private theorem dp2AnnotatedChain_syr_and_ge389_bound_w19 :
    ∀ (shifts : List Nat) (u0 ur : List MixedSRSSym),
      dp2AnnotatedChain u0 shifts ur ->
      dp2GlobalOddVal ur = syrIterW19 shifts.length (dp2GlobalOddVal u0) ∧
      ((∃ n : Nat, 3 ≤ n ∧ n ≤ 387 ∧ n % 2 = 1 ∧
          ∃ i : Nat, i ≤ shifts.length ∧
            syrIterW19 i (dp2GlobalOddVal u0) = n ∧
            dp2GlobalOddVal ur = syrIterW19 (shifts.length - i) n) ∨
       389 ^ shifts.length * 2 ^ dp2ShiftSum shifts * dp2GlobalOddVal ur ≤
         1168 ^ shifts.length * dp2GlobalOddVal u0)
  | [], u0, ur, heq => by
    subst heq; exact ⟨rfl, Or.inr (by simp [dp2ShiftSum])⟩
  | a :: rest, u0, ur, ⟨_, w, _, hsyr_step, htl⟩ => by
    have hNw_pos : dp2GlobalOddVal w > 0 := by unfold dp2GlobalOddVal; omega
    have hNw_odd : dp2GlobalOddVal w % 2 = 1 := by unfold dp2GlobalOddVal; omega
    have hNu_ge3 : dp2GlobalOddVal u0 ≥ 3 := by unfold dp2GlobalOddVal; omega
    have hNu_odd : dp2GlobalOddVal u0 % 2 = 1 := by unfold dp2GlobalOddVal; omega
    have hsyr_eq : syrStepW19 (dp2GlobalOddVal u0) = dp2GlobalOddVal w := by
      unfold syrStepW19
      rw [← hsyr_step, core2_pow2_mul a (dp2GlobalOddVal w) hNw_pos hNw_odd]
    rcases dp2AnnotatedChain_syr_and_ge389_bound_w19 rest w ur htl with ⟨ih_syr, ih_disj⟩
    have hiter_tot : dp2GlobalOddVal ur = syrIterW19 (rest.length + 1) (dp2GlobalOddVal u0) := by
      simp only [syrIterW19, hsyr_eq]; exact ih_syr
    simp only [List.length_cons, dp2ShiftSum]
    refine ⟨hiter_tot, ?_⟩
    by_cases hle387 : dp2GlobalOddVal u0 ≤ 387
    · left
      exact ⟨dp2GlobalOddVal u0, hNu_ge3, hle387, hNu_odd, 0, Nat.zero_le _, rfl, hiter_tot⟩
    · rcases ih_disj with ⟨n, hn3, hn387, hno, i, hi_le, hi_eq, hur_eq⟩ | ih_ge389
      · left
        refine ⟨n, hn3, hn387, hno, i + 1, Nat.succ_le_succ hi_le, ?_, ?_⟩
        · simp only [syrIterW19, hsyr_eq]; exact hi_eq
        · rw [Nat.succ_sub_succ]; exact hur_eq
      · right
        have hstep389 : 389 * (2 ^ a * dp2GlobalOddVal w) ≤ 1168 * dp2GlobalOddVal u0 := by
          rw [hsyr_step]; omega
        rw [Nat.pow_succ 389 rest.length, Nat.pow_add 2 a (dp2ShiftSum rest),
            Nat.pow_succ 1168 rest.length]
        calc
          ((389 ^ rest.length * 389) * (2 ^ a * 2 ^ dp2ShiftSum rest)) * dp2GlobalOddVal ur
              = 2 ^ a * (389 * (389 ^ rest.length * 2 ^ dp2ShiftSum rest * dp2GlobalOddVal ur)) := by ac_rfl
          _ ≤ 2 ^ a * (389 * (1168 ^ rest.length * dp2GlobalOddVal w)) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 389 ih_ge389)
          _ = 1168 ^ rest.length * (389 * (2 ^ a * dp2GlobalOddVal w)) := by ac_rfl
          _ ≤ 1168 ^ rest.length * (1168 * dp2GlobalOddVal u0) :=
                Nat.mul_le_mul_left _ hstep389
          _ = (1168 ^ rest.length * 1168) * dp2GlobalOddVal u0 := by ac_rfl

-- Multi-spike heterogeneous `(m - 1)`-pivot closed-form identity & Hensel squeeze helpers:
private theorem all_m_tail_pivot_exact_geom_w19
    (k w a w_tl a_tl : Nat) (hle : 2 ^ (w + a) ≤ 3 ^ w) :
    (3 ^ w - 2 ^ (w + a)) * multiPivotCarryUB (List.replicate k (w, a)) (w, a) [(w_tl, a_tl)] =
      (3 ^ (k * w) - 2 ^ (k * (w + a))) * 3 ^ (w + w_tl) * (2 ^ a - 1) +
        (3 ^ w - 2 ^ (w + a)) * 2 ^ (k * (w + a)) * 3 ^ w_tl * (2 ^ (a + a_tl) - 1) := by
  have hrep_wt : ∀ n : Nat, blockWeightSum (List.replicate n (w, a)) = n * w := by
    intro n; induction n with
    | zero => simp [blockWeightSum]
    | succ n' ih => simp only [List.replicate_succ, blockWeightSum, ih, Nat.succ_mul]; omega
  have hwt_app : ∀ xs ys : List (Nat × Nat), blockWeightSum (xs ++ ys) = blockWeightSum xs + blockWeightSum ys := by
    intro xs ys; induction xs with
    | nil => simp [blockWeightSum]
    | cons x xtl ih => simp only [List.cons_append, blockWeightSum, ih]; omega
  have hpow_le : ∀ n : Nat, 2 ^ (n * (w + a)) ≤ 3 ^ (n * w) := by
    intro n; induction n with
    | zero => simp
    | succ n' ih =>
      rw [Nat.succ_mul n' (w + a), Nat.succ_mul n' w, Nat.pow_add 2 (n' * (w + a)) (w + a), Nat.pow_add 3 (n' * w) w]
      exact Nat.mul_le_mul ih hle
  induction k with
  | zero =>
    simp only [List.replicate, multiPivotCarryUB, blockWeightSum, blockStepSum,
               Nat.zero_mul, Nat.pow_zero, Nat.sub_self, Nat.zero_add, Nat.add_zero]
    rw [show (w + a + (w_tl + a_tl)) - (w + w_tl) = a + a_tl by omega]
    ac_rfl
  | succ k' ih =>
    have hsub_wt : blockWeightSum (List.replicate k' (w, a) ++ [(w, a), (w_tl, a_tl)]) = (k' + 1) * w + w_tl := by
      rw [hwt_app, hrep_wt k']; simp only [blockWeightSum, Nat.add_zero, Nat.add_mul]; omega
    have hstep_ub : multiPivotCarryUB (List.replicate (k' + 1) (w, a)) (w, a) [(w_tl, a_tl)] =
        3 ^ ((k' + 1) * w + w_tl) * (2 ^ a - 1) +
          2 ^ (w + a) * multiPivotCarryUB (List.replicate k' (w, a)) (w, a) [(w_tl, a_tl)] := by
      conv => lhs; rw [List.replicate_succ]; unfold multiPivotCarryUB
      dsimp only; rw [hsub_wt]; cases k' <;> simp only [List.replicate, Nat.add_comm a w]
    rw [hstep_ub, Nat.mul_add (3 ^ w - 2 ^ (w + a)), Nat.mul_left_comm (3 ^ w - 2 ^ (w + a)) (2 ^ (w + a)), ih, Nat.mul_add (2 ^ (w + a))]
    have h3_split : 3 ^ ((k' + 1) * w + w_tl) = 3 ^ (k' * w) * 3 ^ (w + w_tl) := by
      rw [← Nat.pow_add, show k' * w + (w + w_tl) = (k' + 1) * w + w_tl by simp [Nat.add_mul]; omega]
    have ht1_id : (3 ^ w - 2 ^ (w + a)) * 3 ^ (k' * w) + 2 ^ (w + a) * (3 ^ (k' * w) - 2 ^ (k' * (w + a))) =
        3 ^ ((k' + 1) * w) - 2 ^ ((k' + 1) * (w + a)) := by
      have hk_le := hpow_le k'
      have hm1 : 2 ^ (w + a) * 2 ^ (k' * (w + a)) ≤ 2 ^ (w + a) * 3 ^ (k' * w) := Nat.mul_le_mul_left _ hk_le
      have hm2 : 2 ^ (w + a) * 3 ^ (k' * w) ≤ 3 ^ w * 3 ^ (k' * w) := Nat.mul_le_mul_right _ hle
      have hp3_s : 3 ^ ((k' + 1) * w) = 3 ^ w * 3 ^ (k' * w) := by rw [← Nat.pow_add, show w + k' * w = (k' + 1) * w by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]]
      have hp2_s : 2 ^ ((k' + 1) * (w + a)) = 2 ^ (w + a) * 2 ^ (k' * (w + a)) := by rw [← Nat.pow_add, show (w + a) + k' * (w + a) = (k' + 1) * (w + a) by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]]
      rw [Nat.sub_mul, Nat.mul_sub, hp3_s, hp2_s]
      generalize 3 ^ w * 3 ^ (k' * w) = A1, 2 ^ (w + a) * 3 ^ (k' * w) = A2, 2 ^ (w + a) * 2 ^ (k' * (w + a)) = A3 at hm1 hm2 ⊢; omega
    have ht2_id : 2 ^ (w + a) * ((3 ^ w - 2 ^ (w + a)) * 2 ^ (k' * (w + a)) * 3 ^ w_tl * (2 ^ (a + a_tl) - 1)) =
        (3 ^ w - 2 ^ (w + a)) * 2 ^ ((k' + 1) * (w + a)) * 3 ^ w_tl * (2 ^ (a + a_tl) - 1) := by
      have hp2_s : 2 ^ (w + a) * 2 ^ (k' * (w + a)) = 2 ^ ((k' + 1) * (w + a)) := by
        rw [← Nat.pow_add, show (w + a) + k' * (w + a) = (k' + 1) * (w + a) by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]]
      calc 2 ^ (w + a) * ((3 ^ w - 2 ^ (w + a)) * 2 ^ (k' * (w + a)) * 3 ^ w_tl * (2 ^ (a + a_tl) - 1))
          = (3 ^ w - 2 ^ (w + a)) * (2 ^ (w + a) * 2 ^ (k' * (w + a))) * 3 ^ w_tl * (2 ^ (a + a_tl) - 1) := by ac_rfl
        _ = (3 ^ w - 2 ^ (w + a)) * 2 ^ ((k' + 1) * (w + a)) * 3 ^ w_tl * (2 ^ (a + a_tl) - 1) := by rw [hp2_s]
    rw [h3_split, ht2_id]
    have hcomb1 : (3 ^ w - 2 ^ (w + a)) * (3 ^ (k' * w) * 3 ^ (w + w_tl) * (2 ^ a - 1)) +
        2 ^ (w + a) * ((3 ^ (k' * w) - 2 ^ (k' * (w + a))) * 3 ^ (w + w_tl) * (2 ^ a - 1)) =
        ((3 ^ w - 2 ^ (w + a)) * 3 ^ (k' * w) + 2 ^ (w + a) * (3 ^ (k' * w) - 2 ^ (k' * (w + a)))) * 3 ^ (w + w_tl) * (2 ^ a - 1) := by
      simp only [Nat.add_mul]; ac_rfl
    rw [← Nat.add_assoc, hcomb1, ht1_id]

private theorem all_m_multispike_pivot_exact_geom_w19
    (m w_sp a_sp w a w_tl a_tl : Nat) (hm : m ≥ 3) (hle : 2 ^ (w + a) ≤ 3 ^ w) :
    (3 ^ w - 2 ^ (w + a)) *
        multiPivotCarryUB ((w_sp, a_sp) :: List.replicate (m - 3) (w, a)) (w, a) [(w_tl, a_tl)] =
      (3 ^ w - 2 ^ (w + a)) * 3 ^ ((m - 2) * w + w_tl) * (2 ^ a_sp - 1) +
        2 ^ (a_sp + w) * (3 ^ ((m - 3) * w) - 2 ^ ((m - 3) * (w + a))) * 3 ^ (w + w_tl) * (2 ^ a - 1) +
        (3 ^ w - 2 ^ (w + a)) * 2 ^ (a_sp + w + (m - 3) * (w + a)) * 3 ^ w_tl * (2 ^ (a + a_tl) - 1) := by
  have hrep_wt : ∀ n : Nat, blockWeightSum (List.replicate n (w, a)) = n * w := by
    intro n; induction n with
    | zero => simp [blockWeightSum]
    | succ n' ih => simp only [List.replicate_succ, blockWeightSum, ih, Nat.succ_mul]; omega
  have hwt_app : ∀ xs ys : List (Nat × Nat), blockWeightSum (xs ++ ys) = blockWeightSum xs + blockWeightSum ys := by
    intro xs ys; induction xs with
    | nil => simp [blockWeightSum]
    | cons x xtl ih => simp only [List.cons_append, blockWeightSum, ih]; omega
  have hsub_wt : blockWeightSum (List.replicate (m - 3) (w, a) ++ [(w, a), (w_tl, a_tl)]) = (m - 2) * w + w_tl := by
    rw [hwt_app, hrep_wt (m - 3)]; simp only [blockWeightSum, Nat.add_zero]
    have hm2 : (m - 2) * w = (m - 3) * w + w := by
      conv => lhs; rw [show m - 2 = (m - 3) + 1 by omega, Nat.add_mul, Nat.one_mul]
    omega
  have hhead : multiPivotCarryUB ((w_sp, a_sp) :: List.replicate (m - 3) (w, a)) (w, a) [(w_tl, a_tl)] =
      3 ^ ((m - 2) * w + w_tl) * (2 ^ a_sp - 1) +
        2 ^ (a_sp + w) * multiPivotCarryUB (List.replicate (m - 3) (w, a)) (w, a) [(w_tl, a_tl)] := by
    conv => lhs; unfold multiPivotCarryUB
    dsimp only; rw [hsub_wt]; cases (m - 3) <;> simp only [List.replicate]
  rw [hhead, Nat.mul_add (3 ^ w - 2 ^ (w + a)), Nat.mul_left_comm (3 ^ w - 2 ^ (w + a)) (2 ^ (a_sp + w)),
      all_m_tail_pivot_exact_geom_w19 (m - 3) w a w_tl a_tl hle, Nat.mul_add (2 ^ (a_sp + w))]
  have ht1 : (3 ^ w - 2 ^ (w + a)) * (3 ^ ((m - 2) * w + w_tl) * (2 ^ a_sp - 1)) =
      (3 ^ w - 2 ^ (w + a)) * 3 ^ ((m - 2) * w + w_tl) * (2 ^ a_sp - 1) := by ac_rfl
  have ht2 : 2 ^ (a_sp + w) * ((3 ^ ((m - 3) * w) - 2 ^ ((m - 3) * (w + a))) * 3 ^ (w + w_tl) * (2 ^ a - 1)) =
      2 ^ (a_sp + w) * (3 ^ ((m - 3) * w) - 2 ^ ((m - 3) * (w + a))) * 3 ^ (w + w_tl) * (2 ^ a - 1) := by ac_rfl
  have ht3 : 2 ^ (a_sp + w) * ((3 ^ w - 2 ^ (w + a)) * 2 ^ ((m - 3) * (w + a)) * 3 ^ w_tl * (2 ^ (a + a_tl) - 1)) =
      (3 ^ w - 2 ^ (w + a)) * 2 ^ (a_sp + w + (m - 3) * (w + a)) * 3 ^ w_tl * (2 ^ (a + a_tl) - 1) := by
    calc 2 ^ (a_sp + w) * ((3 ^ w - 2 ^ (w + a)) * 2 ^ ((m - 3) * (w + a)) * 3 ^ w_tl * (2 ^ (a + a_tl) - 1))
        = (3 ^ w - 2 ^ (w + a)) * (2 ^ (a_sp + w) * 2 ^ ((m - 3) * (w + a))) * 3 ^ w_tl * (2 ^ (a + a_tl) - 1) := by ac_rfl
      _ = (3 ^ w - 2 ^ (w + a)) * 2 ^ (a_sp + w + (m - 3) * (w + a)) * 3 ^ w_tl * (2 ^ (a + a_tl) - 1) := by rw [← Nat.pow_add]
  rw [ht1, ht2, ht3, ← Nat.add_assoc]

-- General symbolic all-`m ≥ 3` multi-spike + `henselOddInvModPow2` Brox & `DP2` elimination:
private theorem rotBlocks_last_to_front_w19
    (xs : List (Nat × Nat)) (last : Nat × Nat) :
    rotBlocks xs.length (xs ++ [last]) = last :: xs := by
  unfold rotBlocks
  have hd : ∀ (ys : List (Nat × Nat)), (ys ++ [last]).drop ys.length = [last] := by
    intro ys; induction ys with
    | nil => rfl
    | cons _ tl ih => simp only [List.cons_append, List.length_cons, List.drop_succ_cons, ih]
  have ht : ∀ (ys : List (Nat × Nat)), (ys ++ [last]).take ys.length = ys := by
    intro ys; induction ys with
    | nil => rfl
    | cons _ tl ih => simp only [List.cons_append, List.length_cons, List.take_succ_cons, ih]
  rw [hd xs, ht xs]; rfl

private theorem all_m_multispike_hensel_elim_w19
    (m w_sp a_sp w a w_tl a_tl d_a d_mult : Nat)
    (hm : m ≥ 3) (hw_sp : w_sp ≥ 1) (ha_sp : a_sp ≥ 4)
    (hw : w ≥ 1) (ha : a ≥ 1) (hw_tl : w_tl ≥ 1) (ha_tl : a_tl ≥ 1)
    (hda : d_a ≥ 1) (hd_sp : d_a ∣ a_sp) (hd_a : d_a ∣ a) (hd_tl : d_a ∣ a_tl)
    (hd_m : d_mult ∣ (2 ^ d_a - 1)) (hd_odd : d_mult % 2 = 1)
    (hlt : 3 ^ blockWeightSum (List.replicate (m - 2) (w, a) ++ [(w_tl, a_tl), (w_sp, a_sp)]) <
           2 ^ blockStepSum (List.replicate (m - 2) (w, a) ++ [(w_tl, a_tl), (w_sp, a_sp)]))
    (hcop : Nat.Coprime d_mult
      (2 ^ blockStepSum (List.replicate (m - 2) (w, a) ++ [(w_tl, a_tl), (w_sp, a_sp)]) -
       3 ^ blockWeightSum (List.replicate (m - 2) (w, a) ++ [(w_tl, a_tl), (w_sp, a_sp)])))
    (hub : multiPivotCarryUB ((w_sp, a_sp) :: List.replicate (m - 3) (w, a)) (w, a) [(w_tl, a_tl)] <
      (henselOddInvModPow2 a_sp (3 ^ w_sp * d_mult) * d_mult) *
        (2 ^ blockStepSum (List.replicate (m - 2) (w, a) ++ [(w_tl, a_tl), (w_sp, a_sp)]) -
         3 ^ blockWeightSum (List.replicate (m - 2) (w, a) ++ [(w_tl, a_tl), (w_sp, a_sp)]))) :
    let blocks := List.replicate (m - 2) (w, a) ++ [(w_tl, a_tl), (w_sp, a_sp)]
    let D := 2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks
    (¬ ∃ qs : List Nat,
        qs.length = blocks.length ∧
        ∀ j : Nat, j < blocks.length -> D * natAt qs j = broxSpiralCarry (rotBlocks j blocks)) ∧
    (∀ u0 : List MixedSRSSym, ¬ dp2AnnotatedChain u0 (dp2BlocksToShifts blocks) u0) := by
  dsimp only
  have hw17 := m_block_all_rotation_cyclic_brox_and_multiprime_elimination
  let blocks := List.replicate (m - 2) (w, a) ++ [(w_tl, a_tl), (w_sp, a_sp)]
  let D := 2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks
  have hm2_succ : m - 2 = 1 + (m - 3) := by omega
  have hblk_cons : List.replicate (m - 2) (w, a) ++ [(w_tl, a_tl), (w_sp, a_sp)] =
      (w, a) :: (List.replicate (m - 3) (w, a) ++ [(w_tl, a_tl), (w_sp, a_sp)]) := by
    rw [hm2_succ, Nat.add_comm 1, List.replicate_succ, List.cons_append]
  have hblk_len : blocks.length = m := by
    dsimp [blocks]; rw [List.length_append, List.length_replicate]; simp; omega
  have ha_sp1 : a_sp ≥ 1 := by omega
  have hpos_all : ∀ b ∈ (w, a) :: (List.replicate (m - 3) (w, a) ++ [(w_tl, a_tl), (w_sp, a_sp)]), b.1 ≥ 1 ∧ b.2 ≥ 1 := by
    intro b hb; cases hb with
    | head => exact ⟨hw, ha⟩
    | tail _ htl =>
      rcases List.mem_append.mp htl with hrep | htwo
      · rw [List.eq_of_mem_replicate hrep]; exact ⟨hw, ha⟩
      · rcases List.mem_cons.mp htwo with rfl | h2
        · exact ⟨hw_tl, ha_tl⟩
        · rw [List.mem_singleton.mp h2]; exact ⟨hw_sp, ha_sp1⟩
  have hpos_blk : ∀ b ∈ blocks, b.1 ≥ 1 ∧ b.2 ≥ 1 := by dsimp [blocks]; rw [hblk_cons]; exact hpos_all
  have hdvd_all : ∀ b ∈ (w, a) :: (List.replicate (m - 3) (w, a) ++ [(w_tl, a_tl), (w_sp, a_sp)]), d_a ∣ b.2 := by
    intro b hb; cases hb with
    | head => exact hd_a
    | tail _ htl =>
      rcases List.mem_append.mp htl with hrep | htwo
      · rw [List.eq_of_mem_replicate hrep]; exact hd_a
      · rcases List.mem_cons.mp htwo with rfl | h2
        · exact hd_tl
        · rw [List.mem_singleton.mp h2]; exact hd_sp
  have hrot_m1 : rotBlocks (m - 1) blocks =
      (w_sp, a_sp) :: (List.replicate (m - 3) (w, a) ++ [(w, a), (w_tl, a_tl)]) := by
    have hsp : blocks = (List.replicate (m - 2) (w, a) ++ [(w_tl, a_tl)]) ++ [(w_sp, a_sp)] := by
      dsimp [blocks]; simp [List.append_assoc]
    have hlen_pre : (List.replicate (m - 2) (w, a) ++ [(w_tl, a_tl)]).length = m - 1 := by
      rw [List.length_append, List.length_replicate]; simp; omega
    have hr := rotBlocks_last_to_front_w19 (List.replicate (m - 2) (w, a) ++ [(w_tl, a_tl)]) (w_sp, a_sp)
    rw [hlen_pre, ← hsp] at hr
    have hm2_r : List.replicate (m - 2) (w, a) = List.replicate (m - 3) (w, a) ++ [(w, a)] := by
      conv => lhs; rw [show m - 2 = (m - 3) + 1 by omega, List.replicate_succ']
    rw [hr, hm2_r, List.append_assoc]; rfl
  have hno_qs : ¬ ∃ qs : List Nat, qs.length = blocks.length ∧
      ∀ j : Nat, j < blocks.length -> D * natAt qs j = broxSpiralCarry (rotBlocks j blocks) := by
    rintro ⟨qs, hqs_len, hqs_spec⟩
    have hqs_c := hqs_len; have hsp_c := hqs_spec; have hwk_c := hlt; have hcop_c := hcop
    dsimp only [blocks, D] at hqs_c hsp_c
    rw [hblk_cons] at hqs_c hsp_c hwk_c hcop_c
    have hd_dvd : d_mult ∣ natListGcd qs :=
      (hw17.1.2 (w, a) (List.replicate (m - 3) (w, a) ++ [(w_tl, a_tl), (w_sp, a_sp)]) qs d_a d_mult
        hpos_all hwk_c hqs_c hsp_c).2 hda hdvd_all hd_m hcop_c
    have hlen_ge2 : blocks.length ≥ 2 := by rw [hblk_len]; omega
    have hhen_le := hw17.2.2.1 blocks qs (m - 1)
      (w_sp, a_sp) (List.replicate (m - 3) (w, a)) (w, a) [(w_tl, a_tl)] a_sp d_mult
      hlen_ge2 hpos_blk hlt hqs_len hqs_spec (by rw [hblk_len]; omega) hrot_m1
      ha_sp (Nat.le_refl a_sp) hd_odd hd_dvd
    dsimp only [blocks] at hhen_le
    omega
  refine ⟨hno_qs, ?_⟩
  intro u0 hann
  rw [hblk_cons] at hann
  rcases (leftAnchoredDP2_no_1_to_20_cycles_and_all_m_block_locks.2.2
    (w, a) (List.replicate (m - 3) (w, a) ++ [(w_tl, a_tl), (w_sp, a_sp)]) u0 hpos_all hann).2.2 with
    ⟨ws, qs, _, hqs_len, _, hrot_q, _, _, _, _⟩
  rw [← hblk_cons] at hqs_len hrot_q
  exact hno_qs ⟨qs, hqs_len, fun j hj => by
    have hrj := hrot_q j hj
    cases hd_u : ws.drop j with
    | nil => rw [hd_u] at hrj; exact False.elim hrj
    | cons _ _ => rw [hd_u] at hrj; exact hrj.2.2.2.2⟩

-- Unconditional all-`m ≥ 3` heterogeneous multi-spike instantiation:
-- `[(4, 2)^(m - 2), (9, 2 * m + 10), (31, 8)]` (`s = 8`, `henselOddInvModPow2 8 (3^31 * 3) * 3 = 387`, `22 * UB < 387 * D`)!
private theorem all_m_het_4_9_31_hensel387_elim_w19 (m : Nat) (hm : m ≥ 3) :
    let blocks := List.replicate (m - 2) (4, 2) ++ [(9, 2 * m + 10), (31, 8)]
    let D := 2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks
    blockWeightSum blocks = 4 * m + 32 ∧
    blockStepSum blocks = 8 * m + 46 ∧
    3 ^ blockWeightSum blocks < 2 ^ blockStepSum blocks ∧
    Nat.Coprime 3 D ∧
    henselOddInvModPow2 8 (3 ^ 31 * 3) * 3 = 387 ∧
    22 * multiPivotCarryUB ((31, 8) :: List.replicate (m - 3) (4, 2)) (4, 2) [(9, 2 * m + 10)] < 387 * D ∧
    (¬ ∃ qs : List Nat,
        qs.length = blocks.length ∧
        ∀ j : Nat, j < blocks.length -> D * natAt qs j = broxSpiralCarry (rotBlocks j blocks)) ∧
    (∀ u0 : List MixedSRSSym, ¬ dp2AnnotatedChain u0 (dp2BlocksToShifts blocks) u0) := by
  dsimp only
  let blocks := List.replicate (m - 2) (4, 2) ++ [(9, 2 * m + 10), (31, 8)]
  have hrep_w : ∀ n : Nat, blockWeightSum (List.replicate n (4, 2)) = 4 * n := by
    intro n; induction n with
    | zero => simp [blockWeightSum]
    | succ n' ih => simp only [List.replicate_succ, blockWeightSum, ih]; omega
  have hrep_k : ∀ n : Nat, blockStepSum (List.replicate n (4, 2)) = 6 * n := by
    intro n; induction n with
    | zero => simp [blockStepSum]
    | succ n' ih => simp only [List.replicate_succ, blockStepSum, ih]; omega
  have hw_app : ∀ xs ys : List (Nat × Nat), blockWeightSum (xs ++ ys) = blockWeightSum xs + blockWeightSum ys := by
    intro xs ys; induction xs with | nil => simp [blockWeightSum] | cons _ _ ih => simp only [List.cons_append, blockWeightSum, ih]; omega
  have hk_app : ∀ xs ys : List (Nat × Nat), blockStepSum (xs ++ ys) = blockStepSum xs + blockStepSum ys := by
    intro xs ys; induction xs with | nil => simp [blockStepSum] | cons _ _ ih => simp only [List.cons_append, blockStepSum, ih]; omega
  have hW : blockWeightSum blocks = 4 * m + 32 := by
    dsimp [blocks]; rw [hw_app, hrep_w (m - 2)]; simp [blockWeightSum]; omega
  have hK : blockStepSum blocks = 8 * m + 46 := by
    dsimp [blocks]; rw [hk_app, hrep_k (m - 2)]; simp [blockStepSum]; omega
  let k := m - 3
  have hm_eq : m = k + 3 := by dsimp [k]; omega
  have h7_3W_lt_6_2K : 7 * 3 ^ (4 * m + 32) < 6 * 2 ^ (8 * m + 46) := by
    rw [hm_eq, show 4 * (k + 3) + 32 = 44 + 4 * k by omega, show 8 * (k + 3) + 46 = 70 + 8 * k by omega,
        Nat.pow_add 3 44 (4 * k), Nat.pow_add 2 70 (8 * k),
        ← pow_pow_eq_mul_w5 3 4 k, ← pow_pow_eq_mul_w5 2 8 k]
    have hbase : 7 * 3 ^ 44 < 6 * 2 ^ 70 := by decide
    have hk_le : (3 ^ 4) ^ k ≤ (2 ^ 8) ^ k := by
      induction k with
      | zero => simp
      | succ k' ih => rw [Nat.pow_succ (3 ^ 4), Nat.pow_succ (2 ^ 8)]; exact Nat.mul_le_mul ih (by decide)
    have hp256_pos : (2 ^ 8) ^ k > 0 := nat_pow_pos_of_pos _ (by decide) k
    calc 7 * (3 ^ 44 * (3 ^ 4) ^ k) = (7 * 3 ^ 44) * (3 ^ 4) ^ k := by ac_rfl
      _ ≤ (7 * 3 ^ 44) * (2 ^ 8) ^ k := Nat.mul_le_mul_left _ hk_le
      _ < (6 * 2 ^ 70) * (2 ^ 8) ^ k := Nat.mul_lt_mul_of_pos_right hbase hp256_pos
      _ = 6 * (2 ^ 70 * (2 ^ 8) ^ k) := by ac_rfl
  have hlt_WK : 3 ^ blockWeightSum blocks < 2 ^ blockStepSum blocks := by
    rw [hW, hK]; generalize 3 ^ (4 * m + 32) = P3, 2 ^ (8 * m + 46) = P2 at h7_3W_lt_6_2K ⊢; omega
  let D := 2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks
  have h2K_lt_7D : 2 ^ (8 * m + 46) < 7 * D := by
    dsimp [D]; rw [hW, hK]; generalize 3 ^ (4 * m + 32) = P3, 2 ^ (8 * m + 46) = P2 at h7_3W_lt_6_2K ⊢; omega
  have hcop3_D : Nat.Coprime 3 D := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hg1 := Nat.gcd_dvd_left 3 D; have hg2 := Nat.gcd_dvd_right 3 D
    have hg_le : Nat.gcd 3 D ≤ 3 := Nat.le_of_dvd (by decide) hg1
    have hg_pos : Nat.gcd 3 D ≥ 1 := Nat.gcd_pos_of_pos_left D (by decide)
    have hD_n3 : D % 3 ≠ 0 := by
      dsimp [D]; rw [hW, hK]
      have hp3_m3 : 3 ^ (4 * m + 32) % 3 = 0 := by rw [show 4 * m + 32 = (4 * m + 31) + 1 by omega, Nat.pow_succ]; omega
      have hp2_n3 : 2 ^ (8 * m + 46) % 3 ≠ 0 := pow2_mod3_nonzero_w5 _
      have hsub := sub_mod_of_le_s4_w19 3 (2 ^ (8 * m + 46)) (3 ^ (4 * m + 32)) (by decide)
        (Nat.le_of_lt (by rwa [hW, hK] at hlt_WK))
      rw [hsub, hp3_m3, Nat.sub_zero]
      have hm3_lt : 2 ^ (8 * m + 46) % 3 < 3 := Nat.mod_lt _ (by decide); omega
    by_cases h1 : Nat.gcd 3 D = 1
    · exact h1
    · exfalso; rcases hg1 with ⟨q, hq⟩
      have hg3 : Nat.gcd 3 D = 3 := by
        rcases (by omega : Nat.gcd 3 D = 2 ∨ Nat.gcd 3 D = 3) with h2 | h3
        · rw [h2] at hq; omega
        · exact h3
      rw [hg3] at hg2; rcases hg2 with ⟨q', hq'⟩; rw [hq'] at hD_n3; simp at hD_n3
  have hhen387 : henselOddInvModPow2 8 (3 ^ 31 * 3) * 3 = 387 := by decide
  have h22_ub : 22 * multiPivotCarryUB ((31, 8) :: List.replicate (m - 3) (4, 2)) (4, 2) [(9, 2 * m + 10)] < 387 * D := by
    have hid := all_m_multispike_pivot_exact_geom_w19 m 31 8 4 2 9 (2 * m + 10) hm (by decide)
    have h17 : 3 ^ 4 - 2 ^ (4 + 2) = 17 := by decide
    rw [h17] at hid
    let UB := multiPivotCarryUB ((31, 8) :: List.replicate (m - 3) (4, 2)) (4, 2) [(9, 2 * m + 10)]
    let Z := 2 ^ (8 * m + 33)
    have ht1_lt : 17 * 3 ^ ((m - 2) * 4 + 9) * (2 ^ 8 - 1) < Z := by
      dsimp [Z]
      rw [hm_eq, show (k + 3 - 2) * 4 + 9 = 13 + 4 * k by omega, show 8 * (k + 3) + 33 = 57 + 8 * k by omega,
          Nat.pow_add 3 13 (4 * k), Nat.pow_add 2 57 (8 * k), ← pow_pow_eq_mul_w5 3 4 k, ← pow_pow_eq_mul_w5 2 8 k]
      have hb1 : 17 * 3 ^ 13 * (2 ^ 8 - 1) < 2 ^ 57 := by decide
      have hk_le : (3 ^ 4) ^ k ≤ (2 ^ 8) ^ k := by
        induction k with | zero => simp | succ k' ih => rw [Nat.pow_succ (3 ^ 4), Nat.pow_succ (2 ^ 8)]; exact Nat.mul_le_mul ih (by decide)
      have hp_pos : (2 ^ 8) ^ k > 0 := nat_pow_pos_of_pos _ (by decide) k
      calc 17 * (3 ^ 13 * (3 ^ 4) ^ k) * (2 ^ 8 - 1) = (17 * 3 ^ 13 * (2 ^ 8 - 1)) * (3 ^ 4) ^ k := by ac_rfl
        _ ≤ (17 * 3 ^ 13 * (2 ^ 8 - 1)) * (2 ^ 8) ^ k := Nat.mul_le_mul_left _ hk_le
        _ < 2 ^ 57 * (2 ^ 8) ^ k := Nat.mul_lt_mul_of_pos_right hb1 hp_pos
    have ht2_lt : 2 ^ (8 + 4) * (3 ^ ((m - 3) * 4) - 2 ^ ((m - 3) * (4 + 2))) * 3 ^ (4 + 9) * (2 ^ 2 - 1) < 3 * Z := by
      dsimp [Z]
      have hsub_le : 3 ^ ((m - 3) * 4) - 2 ^ ((m - 3) * (4 + 2)) ≤ 3 ^ ((m - 3) * 4) := Nat.sub_le _ _
      have hle_a : 2 ^ (8 + 4) * (3 ^ ((m - 3) * 4) - 2 ^ ((m - 3) * (4 + 2))) * 3 ^ (4 + 9) * (2 ^ 2 - 1) ≤
          (2 ^ 12 * 3 ^ 13 * 3) * 3 ^ ((m - 3) * 4) := by
        calc 2 ^ (8 + 4) * (3 ^ ((m - 3) * 4) - 2 ^ ((m - 3) * (4 + 2))) * 3 ^ (4 + 9) * (2 ^ 2 - 1)
            ≤ 2 ^ (8 + 4) * 3 ^ ((m - 3) * 4) * 3 ^ (4 + 9) * (2 ^ 2 - 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsub_le))
          _ = (2 ^ 12 * 3 ^ 13 * 3) * 3 ^ ((m - 3) * 4) := by
              rw [show 8 + 4 = 12 from rfl, show 4 + 9 = 13 from rfl, show 2 ^ 2 - 1 = 3 from rfl]; ac_rfl
      have hlt_b : (2 ^ 12 * 3 ^ 13 * 3) * 3 ^ ((m - 3) * 4) < 3 * 2 ^ (8 * m + 33) := by
        rw [hm_eq, show k + 3 - 3 = k by omega, show k * 4 = 4 * k by omega, show 8 * (k + 3) + 33 = 57 + 8 * k by omega,
            Nat.pow_add 2 57 (8 * k), ← pow_pow_eq_mul_w5 3 4 k, ← pow_pow_eq_mul_w5 2 8 k]
        have hb2 : 2 ^ 12 * 3 ^ 13 * 3 < 3 * 2 ^ 57 := by decide
        have hk_le : (3 ^ 4) ^ k ≤ (2 ^ 8) ^ k := by
          induction k with | zero => simp | succ k' ih => rw [Nat.pow_succ (3 ^ 4), Nat.pow_succ (2 ^ 8)]; exact Nat.mul_le_mul ih (by decide)
        have hp_pos : (2 ^ 8) ^ k > 0 := nat_pow_pos_of_pos _ (by decide) k
        calc (2 ^ 12 * 3 ^ 13 * 3) * (3 ^ 4) ^ k ≤ (2 ^ 12 * 3 ^ 13 * 3) * (2 ^ 8) ^ k := Nat.mul_le_mul_left _ hk_le
          _ < (3 * 2 ^ 57) * (2 ^ 8) ^ k := Nat.mul_lt_mul_of_pos_right hb2 hp_pos
          _ = 3 * (2 ^ 57 * (2 ^ 8) ^ k) := by ac_rfl
      exact Nat.lt_of_le_of_lt hle_a hlt_b
    have ht3_le : 17 * 2 ^ (8 + 4 + (m - 3) * (4 + 2)) * 3 ^ 9 * (2 ^ (2 + (2 * m + 10)) - 1) ≤ 334611 * Z := by
      dsimp [Z]
      have hp_sub : 2 ^ (2 + (2 * m + 10)) - 1 ≤ 2 ^ (2 * m + 12) := by rw [show 2 + (2 * m + 10) = 2 * m + 12 by omega]; exact Nat.sub_le _ _
      have hexp : (8 + 4 + (m - 3) * (4 + 2)) + (2 * m + 12) = 8 * m + 6 := by omega
      have hp_mono : 2 ^ (8 * m + 6) ≤ 2 ^ (8 * m + 33) := nat_pow_mono_exp_pos 2 _ _ (by decide) (by omega)
      calc 17 * 2 ^ (8 + 4 + (m - 3) * (4 + 2)) * 3 ^ 9 * (2 ^ (2 + (2 * m + 10)) - 1)
          ≤ 17 * 2 ^ (8 + 4 + (m - 3) * (4 + 2)) * 3 ^ 9 * 2 ^ (2 * m + 12) := Nat.mul_le_mul_left _ hp_sub
        _ = (17 * 3 ^ 9) * (2 ^ (8 + 4 + (m - 3) * (4 + 2)) * 2 ^ (2 * m + 12)) := by ac_rfl
        _ = 334611 * 2 ^ (8 * m + 6) := by rw [show 17 * 3 ^ 9 = 334611 by decide, ← Nat.pow_add, hexp]
        _ ≤ 334611 * 2 ^ (8 * m + 33) := Nat.mul_le_mul_left 334611 hp_mono
    have h17_ub_lt : 17 * UB < 334615 * Z := by
      have hsum3 : (17 * 3 ^ ((m - 2) * 4 + 9) * (2 ^ 8 - 1) +
          2 ^ (8 + 4) * (3 ^ ((m - 3) * 4) - 2 ^ ((m - 3) * (4 + 2))) * 3 ^ (4 + 9) * (2 ^ 2 - 1)) +
          17 * 2 ^ (8 + 4 + (m - 3) * (4 + 2)) * 3 ^ 9 * (2 ^ (2 + (2 * m + 10)) - 1) <
          (Z + 3 * Z) + 334611 * Z :=
        Nat.add_lt_add_of_lt_of_le (Nat.add_lt_add ht1_lt ht2_lt) ht3_le
      change 17 * UB = _ at hid
      rw [← hid] at hsum3
      omega
    have h8192_Z : 8192 * Z < 7 * D := by
      dsimp [Z]
      have h2K_split : 2 ^ (8 * m + 46) = 8192 * 2 ^ (8 * m + 33) := by
        rw [show 8 * m + 46 = 13 + (8 * m + 33) by omega, Nat.pow_add 2 13, show (2 : Nat) ^ 13 = 8192 from rfl]
      rwa [h2K_split] at h2K_lt_7D
    change 22 * UB < 387 * D
    omega
  have hub_raw : multiPivotCarryUB ((31, 8) :: List.replicate (m - 3) (4, 2)) (4, 2) [(9, 2 * m + 10)] <
      (henselOddInvModPow2 8 (3 ^ 31 * 3) * 3) * D := by
    rw [hhen387]
    have h := h22_ub
    change 22 * _ < 387 * D at h
    omega
  rcases all_m_multispike_hensel_elim_w19 m 31 8 4 2 9 (2 * m + 10) 2 3
    hm (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)
    (by decide) (by decide) (by decide) ⟨m + 5, by omega⟩ (by decide) (by decide)
    hlt_WK hcop3_D hub_raw with ⟨hno_qs, hno_dp2⟩
  exact ⟨hW, hK, hlt_WK, hcop3_D, hhen387, h22_ub, hno_qs, hno_dp2⟩

set_option exponentiation.threshold 2048 in
/--
  Theorem W19.1c (`leftAnchoredDP2_no_1_to_30_cycles_and_heterogeneous_m_block_exclusions`,
  `zero custom axioms`):
  1. **Unconditional `1..30`-Cycle Freedom Across ALL `DP2` Words (`N_cut = 389`):**
     For EVERY `1 ≤ r ≤ 30` and EVERY `u : List MixedSRSSym` (including arbitrary `.R`-carrying
     words), `¬ dp2StepIter r u u`, and EVERY positive `m`-block `.R`-carrying `DP2` cycle has
     total odd-step weight `blockWeightSum (b0 :: rest) ≥ 31`; meanwhile in `M1 = Q_(2)^+`,
     `x_0 = 68629840493971 / 1738366812781` (`M1_DP2_29CYCLE_68629840493971_OVER_1738366812781`)
     is an exact 1-block `29`-odd-step (`A = 46`) cycle rejected on `Z^+` by
     `68629840493971 % 1738366812781 = 833534795512 ≠ 0`!
  2. **Symbolic Multi-Spike Heterogeneous-Weight All-`m` (`∀ m ≥ 3`) `.R`-Carrying `DP2`
     Cycle Exclusions (`henselOddInvModPow2`):**
     General `(m, w_sp, a_sp, w, a, w_tl, a_tl, d_a, d_mult)` `.R`-carrying `DP2` cycle exclusion
     across ALL `m ≥ 3`, instantiated unconditionally across **ALL `m ≥ 3`** to rule out the
     heterogeneous multi-spike family `[(4, 2)^(m - 2), (9, 2 * m + 10), (31, 8)]` (`387 * D`,
     `22 * UB < 387 * D`) (`Branch P4.3`, `W19_H1`, `W19_H2`).
-/
theorem leftAnchoredDP2_no_1_to_30_cycles_and_heterogeneous_m_block_exclusions :
    ((∀ (r : Nat) (u : List MixedSRSSym), 1 ≤ r -> r ≤ 30 -> ¬ dp2StepIter r u u) ∧
     (let shifts29 := List.replicate 28 1 ++ [18]
      dp2ShiftSum shifts29 = 46 ∧
      2 ^ 46 - 3 ^ 29 = 1738366812781 ∧
      dp2IterCarry shifts29 = 68629840493971 ∧
      68629840493971 % 1738366812781 = 833534795512 ∧
      833534795512 ≠ 0)) ∧
    (∀ (b0 : Nat × Nat) (rest : List (Nat × Nat)) (u0 : List MixedSRSSym),
      (∀ b ∈ b0 :: rest, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      dp2AnnotatedChain u0 (dp2BlocksToShifts (b0 :: rest)) u0 ->
      blockWeightSum (b0 :: rest) ≥ 31) ∧
    (∀ (m w_sp a_sp w a w_tl a_tl d_a d_mult : Nat) (u0 : List MixedSRSSym),
      let blocks := List.replicate (m - 2) (w, a) ++ [(w_tl, a_tl), (w_sp, a_sp)]
      let D := 2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks
      m ≥ 3 -> w_sp ≥ 1 -> a_sp ≥ 4 -> w ≥ 1 -> a ≥ 1 -> w_tl ≥ 1 -> a_tl ≥ 1 ->
      d_a ≥ 1 -> d_a ∣ a_sp -> d_a ∣ a -> d_a ∣ a_tl ->
      d_mult ∣ (2 ^ d_a - 1) -> d_mult % 2 = 1 ->
      3 ^ blockWeightSum blocks < 2 ^ blockStepSum blocks ->
      Nat.Coprime d_mult D ->
      multiPivotCarryUB ((w_sp, a_sp) :: List.replicate (m - 3) (w, a)) (w, a) [(w_tl, a_tl)] <
        (henselOddInvModPow2 a_sp (3 ^ w_sp * d_mult) * d_mult) * D ->
      ¬ dp2AnnotatedChain u0 (dp2BlocksToShifts blocks) u0) ∧
    (∀ (m : Nat) (u0 : List MixedSRSSym), m ≥ 3 ->
      ¬ dp2AnnotatedChain u0
          (dp2BlocksToShifts (List.replicate (m - 2) (4, 2) ++ [(9, 2 * m + 10), (31, 8)])) u0) := by
  have hno_1_25 := leftAnchoredDP2_no_1_to_25_cycles_and_infinite_m_block_exclusions.1.1
  have hno_1_30 : ∀ (r : Nat) (u : List MixedSRSSym), 1 ≤ r -> r ≤ 30 -> ¬ dp2StepIter r u u := by
    intro r u hr1 hr30 hiter
    by_cases hr25 : r ≤ 25
    · exact hno_1_25 r u hr1 hr25 hiter
    · rcases (leftAnchoredDP2_iterated_affine_carry_and_cycle_laws.1 r u u hiter).2 with
        ⟨shifts, hlen, _, hann, _, _⟩
      rcases leftAnchoredDP2_iterated_affine_carry_and_cycle_laws.2.1.1 shifts u (by omega) hann with
        ⟨hlt, _, _, _⟩
      rw [hlen] at hlt
      rcases dp2AnnotatedChain_syr_and_ge389_bound_w19 shifts u u hann with ⟨_, hsmall | hge389⟩
      · rcases hsmall with ⟨n, hn3, hn387, hno, i, hi_le, hi_eq, hur_eq⟩
        rw [hlen] at hi_le hur_eq
        have hcyc_n : syrIterW19 r n = n := by
          rw [show r = (r - i) + i by omega, syrIterW19_add (r - i) i n, ← hur_eq, hi_eq]
        let k := (n - 3) / 2
        have hk_lt : k < 193 := by dsimp [k]; omega
        have hn_eq : n = 2 * k + 3 := by dsimp [k]; omega
        rw [hn_eq] at hcyc_n
        exact no_small_odd_syr_cycles_26_to_30_w19 ⟨r, by omega⟩ ⟨k, hk_lt⟩ (by dsimp; omega) hcyc_n
      · rw [hlen] at hge389
        have hNu_pos : dp2GlobalOddVal u > 0 := by unfold dp2GlobalOddVal; omega
        have h389_le : 389 ^ r * 2 ^ dp2ShiftSum shifts ≤ 1168 ^ r :=
          nat_mul_le_cancel_right_w5 (dp2GlobalOddVal u) _ _ hNu_pos hge389
        let A := dp2ShiftSum shifts
        change 3 ^ r < 2 ^ A at hlt
        change 389 ^ r * 2 ^ A ≤ 1168 ^ r at h389_le
        rcases (by omega : r = 26 ∨ r = 27 ∨ r = 28 ∨ r = 29 ∨ r = 30) with
          rfl | rfl | rfl | rfl | rfl
        · by_cases hA : A ≤ 41
          · exact absurd (Nat.lt_of_lt_of_le hlt (nat_pow_mono_exp_pos 2 A 41 (by decide) hA)) (by decide)
          · have hp := Nat.mul_le_mul_left (389 ^ 26) (nat_pow_mono_exp_pos 2 42 A (by decide) (by omega))
            exact absurd (Nat.le_trans hp h389_le) (by decide)
        · by_cases hA : A ≤ 42
          · exact absurd (Nat.lt_of_lt_of_le hlt (nat_pow_mono_exp_pos 2 A 42 (by decide) hA)) (by decide)
          · have hp := Nat.mul_le_mul_left (389 ^ 27) (nat_pow_mono_exp_pos 2 43 A (by decide) (by omega))
            exact absurd (Nat.le_trans hp h389_le) (by decide)
        · by_cases hA : A ≤ 44
          · exact absurd (Nat.lt_of_lt_of_le hlt (nat_pow_mono_exp_pos 2 A 44 (by decide) hA)) (by decide)
          · have hp := Nat.mul_le_mul_left (389 ^ 28) (nat_pow_mono_exp_pos 2 45 A (by decide) (by omega))
            exact absurd (Nat.le_trans hp h389_le) (by decide)
        · by_cases hA : A ≤ 45
          · exact absurd (Nat.lt_of_lt_of_le hlt (nat_pow_mono_exp_pos 2 A 45 (by decide) hA)) (by decide)
          · have hp := Nat.mul_le_mul_left (389 ^ 29) (nat_pow_mono_exp_pos 2 46 A (by decide) (by omega))
            exact absurd (Nat.le_trans hp h389_le) (by decide)
        · by_cases hA : A ≤ 47
          · exact absurd (Nat.lt_of_lt_of_le hlt (nat_pow_mono_exp_pos 2 A 47 (by decide) hA)) (by decide)
          · have hp := Nat.mul_le_mul_left (389 ^ 30) (nat_pow_mono_exp_pos 2 48 A (by decide) (by omega))
            exact absurd (Nat.le_trans hp h389_le) (by decide)
  have hann_to_iter : ∀ (sh : List Nat) (x y : List MixedSRSSym), dp2AnnotatedChain x sh y -> dp2StepIter sh.length x y := by
    intro sh; induction sh with
    | nil => intro x y h0; exact h0
    | cons s stl ih => intro x y ⟨_, z, hst, _, htl⟩; exact ⟨z, hst, ih z y htl⟩
  have hfloor31 : ∀ (b0 : Nat × Nat) (rest : List (Nat × Nat)) (u0 : List MixedSRSSym),
      (∀ b ∈ b0 :: rest, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      dp2AnnotatedChain u0 (dp2BlocksToShifts (b0 :: rest)) u0 ->
      blockWeightSum (b0 :: rest) ≥ 31 := by
    intro b0 rest u0 hpos hann
    by_cases hle30 : blockWeightSum (b0 :: rest) ≤ 30
    · exfalso
      have hlen := (leftAnchoredDP2_no_1_to_20_cycles_and_all_m_block_locks.2.1 b0 rest hpos).1
      have hit := hann_to_iter (dp2BlocksToShifts (b0 :: rest)) u0 u0 hann
      rw [hlen] at hit
      have hge1 : blockWeightSum (b0 :: rest) ≥ 1 := by have := (hpos b0 (List.Mem.head _)).1; simp [blockWeightSum]; omega
      exact hno_1_30 (blockWeightSum (b0 :: rest)) u0 hge1 hle30 hit
    · omega
  refine ⟨⟨hno_1_30, by decide⟩, hfloor31, ?_, fun m u0 hm => (all_m_het_4_9_31_hensel387_elim_w19 m hm).2.2.2.2.2.2.2 u0⟩
  intro m w_sp a_sp w a w_tl a_tl d_a d_mult u0; dsimp only
  intro hm hw_sp ha_sp hw ha hw_tl ha_tl hda hd_sp hd_a hd_tl hd_m hd_odd hlt hcop hub
  exact (all_m_multispike_hensel_elim_w19 m w_sp a_sp w a w_tl a_tl d_a d_mult
    hm hw_sp ha_sp hw ha hw_tl ha_tl hda hd_sp hd_a hd_tl hd_m hd_odd hlt hcop hub).2 u0


-- ----------------------------------------------------------------------------
-- Section 4B: Symbolic All-`m ≥ 3` Multi-Spike Heterogeneous `(m - 1)`-Pivot
--             Closed-Form Identity & `henselOddInvModPow2` Brox Squeeze +
--             `m = 8` Balanced (`> 105×`) & Convergent `(41, 65)` (`609 * D`, `> 5×`)
--             Eliminations (`Branch P3.4`, `W19_H2`)
-- ----------------------------------------------------------------------------

private def blocksBal8W19 : List (Nat × Nat) :=
  [(17, 2), (17, 2), (17, 2), (17, 2), (17, 2), (17, 2), (17, 2), (17, 66)]

private def blocksHet8W19 : List (Nat × Nat) :=
  [(5, 2), (5, 2), (8, 8), (5, 2), (5, 2), (4, 4), (4, 2), (5, 2)]

set_option exponentiation.threshold 2048 in
private theorem bal8_rot6_escape_cert_w19 :
    ∀ j : Nat, j < 8 ->
      match rotBlocks j blocksBal8W19 with
      | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: rest =>
        multiPivotCarryUB [b0, b1, b2, b3, b4] b5 rest >
          3 * (2 ^ blockStepSum blocksBal8W19 - 3 ^ blockWeightSum blocksBal8W19)
      | _ => False := by
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (dsimp [rotBlocks, blocksBal8W19, List.drop, List.take, List.append]; decide)

set_option exponentiation.threshold 2048 in
private theorem bal8_7pivot_105x_cert_w19 :
    105 * multiPivotCarryUB [(17, 2), (17, 2), (17, 2), (17, 2), (17, 2), (17, 2)] (17, 2) [(17, 66)] <
      3 * (2 ^ blockStepSum blocksBal8W19 - 3 ^ blockWeightSum blocksBal8W19) ∧
    multiPivotCarryUB [(17, 2), (17, 2), (17, 2), (17, 2), (17, 2), (17, 2)] (17, 2) [(17, 66)] ≥ 1 := by decide

set_option exponentiation.threshold 2048 in
private theorem het8_rot7_escape_cert_w19 :
    ∀ j : Nat, j < 8 ->
      match rotBlocks j blocksHet8W19 with
      | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: rest =>
        multiPivotCarryUB [b0, b1, b2, b3, b4, b5] b6 rest >
          3 * (2 ^ blockStepSum blocksHet8W19 - 3 ^ blockWeightSum blocksHet8W19)
      | _ => False := by
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (dsimp [rotBlocks, blocksHet8W19, List.drop, List.take, List.append]; decide)

set_option exponentiation.threshold 2048 in
private theorem het8_hensel609_certs_w19 :
    blockWeightSum blocksHet8W19 = 41 ∧
    blockStepSum blocksHet8W19 = 65 ∧
    Nat.Coprime 3 (2 ^ blockStepSum blocksHet8W19 - 3 ^ blockWeightSum blocksHet8W19) ∧
    henselOddInvModPow2 8 (3 ^ 8 * 3) * 3 = 609 ∧
    5 * multiPivotCarryUB [(8, 8), (5, 2), (5, 2), (4, 4), (4, 2), (5, 2)] (5, 2) [(5, 2)] <
      609 * (2 ^ blockStepSum blocksHet8W19 - 3 ^ blockWeightSum blocksHet8W19) ∧
    multiPivotCarryUB [(8, 8), (5, 2), (5, 2), (4, 4), (4, 2), (5, 2)] (5, 2) [(5, 2)] ≥ 1 := by decide

/--
  Theorem W19.2c (`m_block_all_m_multispike_hensel_brox_and_8block_elimination`,
  `zero custom axioms`):
  1. **Universal Symbolic All-`m ≥ 3` Multi-Spike Heterogeneous-Weight `(m - 1)`-Pivot
     Closed-Form Geometric Identity:**
     For ALL `m ≥ 3` and `2 ^ (w + a) ≤ 3 ^ w`,
     `(3 ^ w - 2 ^ (w + a)) * multiPivotCarryUB ((w_sp, a_sp) :: replicate (m - 3) (w, a)) (w, a) [(w_tl, a_tl)]`
     equals the exact 3-term closed form in `(w_sp, a_sp)`, `(w, a)`, and `(w_tl, a_tl)`!
  2. **General Symbolic All-`m ≥ 3` Multi-Spike + `henselOddInvModPow2` Brox & `DP2` Elimination
     + Unconditional `[(4, 2)^(m - 2), (9, 2 * m + 10), (31, 8)]` Elimination (`22 * UB < 387 * D`):**
     Eliminates `[(4, 2)^(m - 2), (9, 2 * m + 10), (31, 8)]` across **100% of ALL `m ≥ 3`** via
     `s = 8` Hensel boost `henselOddInvModPow2 8 (3^31 * 3) * 3 = 387`!
  3. **Concrete `m = 8` Balanced (`> 105×` 7-Pivot vs All-8 6-Pivot Escape) & Convergent
     `(W = 41, K = 65)` Multi-Spike Heterogeneous (`609 * D`, `> 5×` vs All-8 Non-Hensel Escape)
     Eliminations** (`Branch P3.4`, witnesses `M1_BALANCED_8BLOCK_SIX_PIVOT_ESCAPE` &
     `M1_HET_MULTISPIKE_8BLOCK_NONHENSEL_ESCAPE`, `W19_H2`).
-/
theorem m_block_all_m_multispike_hensel_brox_and_8block_elimination :
    ((∀ (m w_sp a_sp w a w_tl a_tl : Nat), m ≥ 3 -> 2 ^ (w + a) ≤ 3 ^ w ->
        (3 ^ w - 2 ^ (w + a)) *
            multiPivotCarryUB ((w_sp, a_sp) :: List.replicate (m - 3) (w, a)) (w, a) [(w_tl, a_tl)] =
          (3 ^ w - 2 ^ (w + a)) * 3 ^ ((m - 2) * w + w_tl) * (2 ^ a_sp - 1) +
            2 ^ (a_sp + w) * (3 ^ ((m - 3) * w) - 2 ^ ((m - 3) * (w + a))) * 3 ^ (w + w_tl) * (2 ^ a - 1) +
            (3 ^ w - 2 ^ (w + a)) * 2 ^ (a_sp + w + (m - 3) * (w + a)) * 3 ^ w_tl * (2 ^ (a + a_tl) - 1)) ∧
     (∀ (m w_sp a_sp w a w_tl a_tl d_a d_mult : Nat),
        let blocks := List.replicate (m - 2) (w, a) ++ [(w_tl, a_tl), (w_sp, a_sp)]
        let D := 2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks
        m ≥ 3 -> w_sp ≥ 1 -> a_sp ≥ 4 -> w ≥ 1 -> a ≥ 1 -> w_tl ≥ 1 -> a_tl ≥ 1 ->
        d_a ≥ 1 -> d_a ∣ a_sp -> d_a ∣ a -> d_a ∣ a_tl ->
        d_mult ∣ (2 ^ d_a - 1) -> d_mult % 2 = 1 ->
        3 ^ blockWeightSum blocks < 2 ^ blockStepSum blocks ->
        Nat.Coprime d_mult D ->
        multiPivotCarryUB ((w_sp, a_sp) :: List.replicate (m - 3) (w, a)) (w, a) [(w_tl, a_tl)] <
          (henselOddInvModPow2 a_sp (3 ^ w_sp * d_mult) * d_mult) * D ->
        (¬ ∃ qs : List Nat,
            qs.length = blocks.length ∧
            ∀ j : Nat, j < blocks.length -> D * natAt qs j = broxSpiralCarry (rotBlocks j blocks)) ∧
        (∀ u0 : List MixedSRSSym, ¬ dp2AnnotatedChain u0 (dp2BlocksToShifts blocks) u0)) ∧
     (∀ m : Nat, m ≥ 3 ->
        let blocks := List.replicate (m - 2) (4, 2) ++ [(9, 2 * m + 10), (31, 8)]
        let D := 2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks
        3 ^ blockWeightSum blocks < 2 ^ blockStepSum blocks ∧
        henselOddInvModPow2 8 (3 ^ 31 * 3) * 3 = 387 ∧
        22 * multiPivotCarryUB ((31, 8) :: List.replicate (m - 3) (4, 2)) (4, 2) [(9, 2 * m + 10)] < 387 * D ∧
        (¬ ∃ qs : List Nat,
            qs.length = blocks.length ∧
            ∀ j : Nat, j < blocks.length -> D * natAt qs j = broxSpiralCarry (rotBlocks j blocks)) ∧
        (∀ u0 : List MixedSRSSym, ¬ dp2AnnotatedChain u0 (dp2BlocksToShifts blocks) u0))) ∧
    (let blocks_bal8 : List (Nat × Nat) := [(17, 2), (17, 2), (17, 2), (17, 2), (17, 2), (17, 2), (17, 2), (17, 66)]
     let D_bal8 := 2 ^ blockStepSum blocks_bal8 - 3 ^ blockWeightSum blocks_bal8
     let blocks_het8 : List (Nat × Nat) := [(5, 2), (5, 2), (8, 8), (5, 2), (5, 2), (4, 4), (4, 2), (5, 2)]
     let D_het8 := 2 ^ blockStepSum blocks_het8 - 3 ^ blockWeightSum blocks_het8
     (∀ j : Nat, j < 8 ->
       match rotBlocks j blocks_bal8 with
       | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: rest => multiPivotCarryUB [b0, b1, b2, b3, b4] b5 rest > 3 * D_bal8
       | _ => False) ∧
     105 * multiPivotCarryUB [(17, 2), (17, 2), (17, 2), (17, 2), (17, 2), (17, 2)] (17, 2) [(17, 66)] < 3 * D_bal8 ∧
     ¬ (∃ qs : List Nat,
       qs.length = 8 ∧
       ∀ j : Nat, j < 8 -> D_bal8 * natAt qs j = broxSpiralCarry (rotBlocks j blocks_bal8)) ∧
     ¬ (∃ u0 : List MixedSRSSym, dp2AnnotatedChain u0 (dp2BlocksToShifts blocks_bal8) u0) ∧
     blockWeightSum blocks_het8 = 41 ∧
     blockStepSum blocks_het8 = 65 ∧
     Nat.Coprime 3 D_het8 ∧
     (∀ j : Nat, j < 8 ->
       match rotBlocks j blocks_het8 with
       | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: rest => multiPivotCarryUB [b0, b1, b2, b3, b4, b5] b6 rest > 3 * D_het8
       | _ => False) ∧
     henselOddInvModPow2 8 (3 ^ 8 * 3) * 3 = 609 ∧
     5 * multiPivotCarryUB [(8, 8), (5, 2), (5, 2), (4, 4), (4, 2), (5, 2)] (5, 2) [(5, 2)] < 609 * D_het8 ∧
     ¬ (∃ qs : List Nat,
       qs.length = 8 ∧
       ∀ j : Nat, j < 8 -> D_het8 * natAt qs j = broxSpiralCarry (rotBlocks j blocks_het8)) ∧
     ¬ (∃ u0 : List MixedSRSSym, dp2AnnotatedChain u0 (dp2BlocksToShifts blocks_het8) u0)) := by
  have hw17_brox := m_block_all_rotation_cyclic_brox_and_multiprime_elimination
  refine ⟨⟨all_m_multispike_pivot_exact_geom_w19,
           fun m w_sp a_sp w a w_tl a_tl d_a d_mult hm hw_sp ha_sp hw ha hw_tl ha_tl hda hd_sp hd_a hd_tl hd_m hd_odd hlt hcop hub =>
             all_m_multispike_hensel_elim_w19 m w_sp a_sp w a w_tl a_tl d_a d_mult hm hw_sp ha_sp hw ha hw_tl ha_tl hda hd_sp hd_a hd_tl hd_m hd_odd hlt hcop hub,
           fun m hm => by
             rcases all_m_het_4_9_31_hensel387_elim_w19 m hm with ⟨_, _, hlt, _, h387, h22, hnq, hnd⟩
             exact ⟨hlt, h387, h22, hnq, hnd⟩⟩, ?_⟩
  dsimp only
  rcases bal8_7pivot_105x_cert_w19 with ⟨h105_bal8, _⟩
  rcases het8_hensel609_certs_w19 with ⟨hw41, hk65, hcop3_het8, hinv609, h5_het8, _⟩
  have hlt_bal8 : 3 ^ blockWeightSum blocksBal8W19 < 2 ^ blockStepSum blocksBal8W19 := by
    generalize 2 ^ blockStepSum blocksBal8W19 = P2, 3 ^ blockWeightSum blocksBal8W19 = P3 at h105_bal8 ⊢; omega
  have hlt_het8 : 3 ^ blockWeightSum blocksHet8W19 < 2 ^ blockStepSum blocksHet8W19 := by
    generalize 2 ^ blockStepSum blocksHet8W19 = P2, 3 ^ blockWeightSum blocksHet8W19 = P3 at h5_het8 ⊢; omega
  have hno_qs_bal8 : ¬ (∃ qs : List Nat, qs.length = 8 ∧
      ∀ j : Nat, j < 8 -> (2 ^ blockStepSum blocksBal8W19 - 3 ^ blockWeightSum blocksBal8W19) * natAt qs j =
        broxSpiralCarry (rotBlocks j blocksBal8W19)) := by
    rintro ⟨qs, hlen8, hspec8⟩
    rcases hw17_brox.1.2 (17, 2) [(17, 2), (17, 2), (17, 2), (17, 2), (17, 2), (17, 2), (17, 66)] qs 2 3
      (by decide) hlt_bal8 hlen8 hspec8 with ⟨hcop3, hcasc3⟩
    have h3_dvd : 3 ∣ natListGcd qs := hcasc3 (by decide) (by decide) (by decide) hcop3
    have h3D_le := hw17_brox.2.1 blocksBal8W19 qs 0
      [(17, 2), (17, 2), (17, 2), (17, 2), (17, 2), (17, 2)] (17, 2) [(17, 66)] 3
      (by decide) hlt_bal8 hlen8 hspec8 (by decide) rfl h3_dvd
    omega
  have hno_dp2_bal8 : ¬ (∃ u0 : List MixedSRSSym, dp2AnnotatedChain u0 (dp2BlocksToShifts blocksBal8W19) u0) := by
    rintro ⟨u0, hann⟩
    rcases (leftAnchoredDP2_no_1_to_20_cycles_and_all_m_block_locks.2.2
      (17, 2) [(17, 2), (17, 2), (17, 2), (17, 2), (17, 2), (17, 2), (17, 66)] u0 (by decide) hann).2.2 with
      ⟨ws, qs, _, hqs_len, _, hrot_q, _, _, _, _⟩
    exact hno_qs_bal8 ⟨qs, hqs_len, fun j hj => by
      have hrj := hrot_q j hj
      cases hd_u : ws.drop j with | nil => rw [hd_u] at hrj; exact False.elim hrj | cons _ _ => rw [hd_u] at hrj; exact hrj.2.2.2.2⟩
  have hno_qs_het8 : ¬ (∃ qs : List Nat, qs.length = 8 ∧
      ∀ j : Nat, j < 8 -> (2 ^ blockStepSum blocksHet8W19 - 3 ^ blockWeightSum blocksHet8W19) * natAt qs j =
        broxSpiralCarry (rotBlocks j blocksHet8W19)) := by
    rintro ⟨qs, hlen8, hspec8⟩
    have h3_dvd : 3 ∣ natListGcd qs :=
      (hw17_brox.1.2 (5, 2) [(5, 2), (8, 8), (5, 2), (5, 2), (4, 4), (4, 2), (5, 2)] qs 2 3
        (by decide) hlt_het8 hlen8 hspec8).2 (by decide) (by decide) (by decide) hcop3_het8
    have h609_le := hw17_brox.2.2.1 blocksHet8W19 qs 2
      (8, 8) [(5, 2), (5, 2), (4, 4), (4, 2), (5, 2)] (5, 2) [(5, 2)] 8 3
      (by decide) (by decide) hlt_het8 hlen8 hspec8 (by decide) rfl
      (by decide) (by decide) (by decide) h3_dvd
    rw [hinv609] at h609_le
    omega
  have hno_dp2_het8 : ¬ (∃ u0 : List MixedSRSSym, dp2AnnotatedChain u0 (dp2BlocksToShifts blocksHet8W19) u0) := by
    rintro ⟨u0, hann⟩
    rcases (leftAnchoredDP2_no_1_to_20_cycles_and_all_m_block_locks.2.2
      (5, 2) [(5, 2), (8, 8), (5, 2), (5, 2), (4, 4), (4, 2), (5, 2)] u0 (by decide) hann).2.2 with
      ⟨ws, qs, _, hqs_len, _, hrot_q, _, _, _, _⟩
    exact hno_qs_het8 ⟨qs, hqs_len, fun j hj => by
      have hrj := hrot_q j hj
      cases hd_u : ws.drop j with | nil => rw [hd_u] at hrj; exact False.elim hrj | cons _ _ => rw [hd_u] at hrj; exact hrj.2.2.2.2⟩
  exact ⟨bal8_rot6_escape_cert_w19, h105_bal8, hno_qs_bal8, hno_dp2_bal8,
         hw41, hk65, hcop3_het8, het8_rot7_escape_cert_w19, hinv609, h5_het8, hno_qs_het8, hno_dp2_het8⟩

end CollatzFormal
